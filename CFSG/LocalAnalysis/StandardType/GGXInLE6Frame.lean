module

public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
public import CFSG.LocalAnalysis.StandardType.GGXInLE6Sylow

public section

namespace CFSG.StandardType.GGXInLE6Frame

theorem mem_image_of_commute
    {H : Type} [Group H] [Finite H] (N E : Subgroup H) [N.Normal] (hN : IsPGroup 2 N)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsc : ∀ g : H, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E)
    {g : H ⧸ N} (hg3 : g ^ 3 = 1)
    (hcomm : ∀ e ∈ E.map (QuotientGroup.mk' N), g * e = e * g) :
    g ∈ E.map (QuotientGroup.mk' N) := by
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective g
  have ht : t ^ 3 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hg3
  have hc : ∀ e ∈ E, e * t * e⁻¹ * t⁻¹ ∈ N := by
    intro e he
    have h := hcomm (QuotientGroup.mk' N e) ⟨e, he, rfl⟩
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact h.symm
  obtain ⟨e, he, heN⟩ := GGXInLE6Sylow.mem_E_of_commute_mod_N N E hN hE3 hEc hsc ht hc
  refine ⟨e, he, ?_⟩
  show (e : H ⧸ N) = (t : H ⧸ N)
  rw [QuotientGroup.eq]
  exact heN

theorem nsub_le_normalizer
    {Q : Type} [Group Q] {E0 T Nsub : Subgroup Q} (hT : T ≤ E0)
    (h : ∀ n ∈ Nsub, ∀ e ∈ E0, n * e * n⁻¹ * e⁻¹ ∈ T) :
    Nsub ≤ Subgroup.normalizer (E0 : Set Q) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff'']
  intro e
  constructor
  · intro he
    have h1 : n⁻¹ * e * n * e⁻¹ ∈ T := by
      simpa using h n⁻¹ (Nsub.inv_mem hn) e he
    have h2 : n⁻¹ * e * n = (n⁻¹ * e * n * e⁻¹) * e := by group
    rw [h2]
    exact E0.mul_mem (hT h1) he
  · intro he
    have h1 : n * (n⁻¹ * e * n) * n⁻¹ * (n⁻¹ * e * n)⁻¹ ∈ T :=
      h n hn (n⁻¹ * e * n) he
    have h2 : n * (n⁻¹ * e * n) * n⁻¹ * (n⁻¹ * e * n)⁻¹ =
        e * (n⁻¹ * e * n)⁻¹ := by group
    have h3 : e * (n⁻¹ * e * n)⁻¹ ∈ T := h2 ▸ h1
    have h4 : (e * (n⁻¹ * e * n)⁻¹) * (n⁻¹ * e * n) ∈ E0 :=
      E0.mul_mem (hT h3) he
    have h5 : e = (e * (n⁻¹ * e * n)⁻¹) * (n⁻¹ * e * n) := by group
    rw [h5]
    exact h4

theorem quotFrame_of_transfer
    {L1 Q : Type} [Group L1] [Finite L1] [Group Q] [Finite Q]
    (ι : L1 →* Q) (hι : Function.Injective ι) {E0 : Subgroup Q}
    (hsc0 : ∀ g : Q, (∀ e ∈ E0, g * e = e * g) → g ^ 3 = 1 → g ∈ E0)
    {A : Subgroup (MulAut L1)}
    (hind : ∀ e ∈ E0, ∃ a ∈ A, ∀ l, ι (a l) = e * ι l * e⁻¹)
    {T N : Subgroup L1} (hn : (T.subgroupOf N).Normal) (hTN : T ≤ N)
    (hTexp : ∀ t ∈ T, t ^ 3 = 1)
    (hfix : ∀ a ∈ A, ∀ t ∈ T, a t = t)
    (hN : ∀ n ∈ N, ∀ a ∈ A, n * (a n)⁻¹ ∈ T)
    (hcox : haveI := hn; Nonempty (CoxeterSystem CoxeterMatrix.E₆ (N ⧸ T.subgroupOf N)))
    (hidx : ¬ 3 ∣ N.index) (hperf : commutator L1 = ⊤)
    {z : L1} (hzT : z ∈ T) (hzc : z ∈ Subgroup.center L1) (hzo : orderOf z = 3) :
    GGXInL.lup8f_QuotFrame Q E0 ι.range (T.map ι) (N.map ι) (ι z) := by
  classical
  have hTE : T.map ι ≤ E0 := by
    rintro _ ⟨t, ht, rfl⟩
    refine hsc0 (ι t) ?_ ?_
    · intro e he
      obtain ⟨a, ha, hae⟩ := hind e he
      have h1 := hae t
      rw [hfix a ha t ht] at h1
      calc ι t * e = e * ι t * e⁻¹ * e := by rw [← h1]
        _ = e * ι t := by group
    · rw [← map_pow, hTexp t ht, map_one]
  have hcomm : ∀ n ∈ N.map ι, ∀ e ∈ E0, n * e * n⁻¹ * e⁻¹ ∈ T.map ι := by
    rintro _ ⟨n, hn, rfl⟩ e he
    obtain ⟨a, ha, hae⟩ := hind e he
    have h1 := Subgroup.mem_map_of_mem ι (hN n hn a ha)
    rw [map_mul, map_inv, hae n] at h1
    have h2 : ι n * (e * ι n * e⁻¹)⁻¹ = ι n * e * (ι n)⁻¹ * e⁻¹ := by group
    rwa [h2] at h1
  have hnorm : N.map ι ≤ Subgroup.normalizer (E0 : Set Q) := nsub_le_normalizer hTE hcomm
  have hTN' : T.map ι ≤ N.map ι := Subgroup.map_mono hTN
  have hTnorm : ((T.map ι).subgroupOf (N.map ι)).Normal := by
    refine ⟨fun t ht g => ?_⟩
    obtain ⟨n₁, hn₁, hgn⟩ := Subgroup.mem_map.mp g.2
    have ht' : (t : Q) ∈ T.map ι := Subgroup.mem_subgroupOf.mp ht
    obtain ⟨t₁, ht₁, htt⟩ := Subgroup.mem_map.mp ht'
    have hcj := hn.conj_mem ⟨t₁, hTN ht₁⟩ (Subgroup.mem_subgroupOf.mpr ht₁) ⟨n₁, hn₁⟩
    have hcj' : n₁ * t₁ * n₁⁻¹ ∈ T := Subgroup.mem_subgroupOf.mp hcj
    rw [Subgroup.mem_subgroupOf]
    show (g : Q) * (t : Q) * (g : Q)⁻¹ ∈ T.map ι
    rw [← hgn, ← htt, ← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem ι hcj'
  haveI hTn : ((T.map ι).subgroupOf (N.map ι)).Normal := hTnorm
  have hcox' : ∃ (ι' : Type) (M : CoxeterMatrix ι'),
      Nonempty (CoxeterSystem M (↥(N.map ι) ⧸ (T.map ι).subgroupOf (N.map ι))) := by
    haveI := hn
    obtain ⟨cs⟩ := hcox
    let e : ↥N ≃* ↥(N.map ι) := Subgroup.equivMapOfInjective N ι hι
    have he : (T.subgroupOf N).map e.toMonoidHom = (T.map ι).subgroupOf (N.map ι) := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        have hu' : (u : L1) ∈ T := Subgroup.mem_subgroupOf.mp hu
        refine Subgroup.mem_subgroupOf.mpr ?_
        show ι (u : L1) ∈ T.map ι
        exact Subgroup.mem_map_of_mem ι hu'
      · intro hy
        rw [Subgroup.mem_subgroupOf] at hy
        obtain ⟨t₁, ht₁, htt⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨t₁, hTN ht₁⟩, Subgroup.mem_subgroupOf.mpr ht₁, Subtype.ext htt⟩
    exact ⟨Fin 6, CoxeterMatrix.E₆,
      ⟨cs.map (QuotientGroup.congr (T.subgroupOf N) ((T.map ι).subgroupOf (N.map ι)) e he)⟩⟩
  have hidx' : ¬ 3 ∣ (N.map ι).relIndex ι.range := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective N ⊤ hι,
      Subgroup.relIndex_top_right]
    exact hidx
  have hperf' : commutator ↥ι.range = ⊤ := by
    have hs : Function.Surjective ι.rangeRestrict := ι.rangeRestrict_surjective
    have h : (commutator L1).map ι.rangeRestrict = commutator ↥ι.range := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hs]
    rw [← h, hperf, Subgroup.map_top_of_surjective _ hs]
  refine
    { T_le_E0 := hTE
      T_odd := ?_
      z_mem_L0 := ⟨z, rfl⟩
      z_center := ?_
      z_mem_T := Subgroup.mem_map_of_mem ι hzT
      z_order := ?_
      L0_perfect := hperf'
      T_le_Nsub := hTN'
      Nsub_le_L0 := Subgroup.map_le_range ι N
      Nsub_le_norm := hnorm
      T_normal := hTnorm
      coxeter := hcox'
      idx := hidx' }
  · rintro _ ⟨t, ht, rfl⟩
    have hd : orderOf (ι t) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hTexp t ht, map_one])
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      exact ⟨1, rfl⟩
  · rintro _ ⟨l, rfl⟩
    have hz' := Subgroup.mem_center_iff.mp hzc l
    rw [← map_mul, ← map_mul, hz']
  · rw [orderOf_injective ι hι z]
    exact hzo

end CFSG.StandardType.GGXInLE6Frame

end
