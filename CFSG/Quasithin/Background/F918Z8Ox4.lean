module

public import CFSG.Quasithin.Background.F918Z8Ox2
public import CFSG.Quasithin.Background.F918Z8Ox3
public import CFSG.Quasithin.Background.F918Z8Op5
public import CFSG.Quasithin.Background.F918L1
public import CFSG.Quasithin.Background.F918L2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem opx_lift (h38 : Vol2Native.A38ForSQTKCat) {W : Type}
    [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hstd : D3Std M Mp T L V) {t : MulAut W} (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) :
    ∃ (S : Type) (_ : Group S) (φ : S →* ↥M), Function.Surjective φ ∧
      Vol2Native.SQTKHypCat S ∧ ∃ Lh : Subgroup S, Lh ∈ cComp (⊤ : Subgroup S) ∧
        IsSimpleGroup ↥Lh ∧ (∀ x ∈ Lh, ∀ y ∈ Lh, φ x = φ y → x = y) ∧
          Lh.map φ = L.subgroupOf M := by
  have hD := hstd.hyp
  have hTM : T ≤ M := hD.sylow.1
  have hLM : L ≤ M := le_of_mem_cComp hD.comp
  have hO2 : CFSG.pCore 2 ↥M = ⊥ := by
    have h := D31.pCoreOf_eq_bot hD
    unfold pCoreOf at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h
  have hLc : L.subgroupOf M ∈ cComp (⊤ : Subgroup ↥M) := subgroupOf_mem_cComp hD.comp
  obtain ⟨Shat, _, φ, hφ, hSQ, Lhat, hLhat, hmap⟩ := exists_sqtk_cover hD.qsqtk hO2 hLc
  have hnn : ¬ Lhat.Normal := by
    intro hN
    have hLN : (L.subgroupOf M).Normal := hmap ▸ hN.map φ hφ
    have key : ∀ s ∈ M, ∀ x ∈ L, s * x * s⁻¹ ∈ L := fun s hs x hx => by
      have := hLN.conj_mem ⟨x, hLM hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨s, hs⟩
      exact Subgroup.mem_subgroupOf.mp this
    apply htL
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => key t (hTM htT) x hx
    · intro h
      have := key t⁻¹ (M.inv_mem (hTM htT)) _ h
      simpa [mul_assoc] using this
  rcases (h38 Shat hSQ Lhat hLhat).1 with hN | ⟨hAT, -⟩
  · exact absurd hN hnn
  · have hsimple : IsSimpleGroup ↥Lhat := Vol2Native.L122A.isSimpleGroup_of_a38Types hAT
    have hnt : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hD.quasi
    let ψ : ↥Lhat →* ↥M := φ.comp Lhat.subtype
    have hrange : ψ.range = L.subgroupOf M := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact hmap
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases hsimple.eq_bot_or_eq_top_of_normal ψ.ker with h | h
      · exact h
      · exfalso
        have h1 : ψ.range = ⊥ := by
          rw [eq_bot_iff]
          rintro _ ⟨x, rfl⟩
          exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
        rw [hrange] at h1
        obtain ⟨x, hx1⟩ := exists_ne (1 : ↥L)
        have hx : (⟨(x : MulAut W), hLM x.2⟩ : ↥M) ∈ L.subgroupOf M :=
          Subgroup.mem_subgroupOf.mpr x.2
        rw [h1, Subgroup.mem_bot] at hx
        have hx' := congrArg Subtype.val hx
        exact hx1 (Subtype.ext (by simpa using hx'))
    refine ⟨Shat, inferInstance, φ, hφ, hSQ, Lhat, hLhat, hsimple, ?_, hmap⟩
    intro x hx y hy hxy
    exact congrArg Subtype.val (hinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)

theorem opx_normalizes_conj {W : Type} [CommGroup W] [Finite W]
    {M Mp L : Subgroup (MulAut W)} {t g : MulAut W} (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hcomm : ⁅L, conjAutSub t L⁆ = ⊥)
    (hinf : L ⊓ conjAutSub t L = ⊥) (hMp : Mp = L ⊔ conjAutSub t L)
    (hMpn : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))) (htM : t ∈ M) (hgM : g ∈ M)
    (hgc : ∀ x ∈ L, g * x = x * g) : ∀ x ∈ conjAutSub t L, g * x * g⁻¹ ∈ conjAutSub t L := by
  intro x hx
  have hgtM : g * t ∈ M := M.mul_mem hgM htM
  have hmem : g * x * g⁻¹ ∈ conjAutSub (g * t) L := by
    rw [mem_conjAutSub_iff]
    have h1 : t⁻¹ * x * t ∈ L := mem_conjAutSub_iff.mp hx
    have e : (g * t)⁻¹ * (g * x * g⁻¹) * (g * t) = t⁻¹ * x * t := by group
    rw [e]
    exact h1
  rcases d321a_perm hLs hnab hcomm hMp hMpn hgtM with h | h
  · rw [h] at hmem
    have hxL : x ∈ L := by
      have hc := hgc _ hmem
      have h1 : g⁻¹ * (g * x * g⁻¹) * g = g * x * g⁻¹ := by
        calc g⁻¹ * (g * x * g⁻¹) * g = g⁻¹ * ((g * x * g⁻¹) * g) := by group
          _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [hc]
          _ = g * x * g⁻¹ := by group
      have h2 : x = g * x * g⁻¹ := by
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g * x * g⁻¹ := h1
      rw [h2]
      exact hmem
    have hx1 : x ∈ L ⊓ conjAutSub t L := ⟨hxL, hx⟩
    rw [hinf, Subgroup.mem_bot] at hx1
    rw [hx1]
    simp
  · rw [h] at hmem
    exact hmem

theorem opx_subgroupOf_conj {W : Type} [CommGroup W] {M L : Subgroup (MulAut W)} {t : MulAut W}
    (htM : t ∈ M) :
    (conjAutSub t L).subgroupOf M =
      (L.subgroupOf M).map (MulAut.conj (⟨t, htM⟩ : ↥M)).toMonoidHom := by
  ext ⟨x, hx⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, mem_conjAutSub_iff]
  constructor
  · intro h
    refine ⟨⟨t⁻¹ * x * t, M.mul_mem (M.mul_mem (M.inv_mem htM) hx) htM⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr h
    · apply Subtype.ext
      show t * (t⁻¹ * x * t) * t⁻¹ = x
      group
  · rintro ⟨⟨y, hyM⟩, hy, hyx⟩
    have hy' : y ∈ L := Subgroup.mem_subgroupOf.mp hy
    have h1 : t * y * t⁻¹ = x := congrArg Subtype.val hyx
    have e : t⁻¹ * x * t = y := by
      rw [← h1]
      group
    rw [e]
    exact hy'

theorem d321OpExc_of_inputs (hL38 : D3L38)
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) : D321OpExc := by
  intro W _ _ M Mp T L V t hstd htT htL hMp g hgM hgc p hp hp2 hpL hk hex
  obtain ⟨hA38, hcomm, hinf, -⟩ := hL38 W M Mp T L V hstd t htT htL hMp
  have hD := hstd.hyp
  have hLs : IsSimpleGroup ↥L := Vol2Native.L122A.isSimpleGroup_of_a38Types hA38
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hD.quasi.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hLM : L ≤ M := le_of_mem_cComp hD.comp
  have htM : t ∈ M := hD.sylow.1 htT
  have hL'M : conjAutSub t L ≤ M := by
    intro x hx
    have h1 : t⁻¹ * x * t ∈ L := mem_conjAutSub_iff.mp hx
    have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem htM (hLM h1)) (M.inv_mem htM)
  have hgn := opx_normalizes_conj hLs hnab hcomm hinf hMp hD.Mp_normal htM hgM hgc
  obtain ⟨S, _, φ, hφ, hSQ, Lh, hLh, hs, hinj, hmap⟩ := opx_lift h38 hstd htT htL
  have hSfin : Finite S := hSQ.finite
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2 := hSQ.rank_top hp hp2
  have hne : L.subgroupOf M ≠ (conjAutSub t L).subgroupOf M := by
    intro h
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥L)
    have h1 : (⟨(x : MulAut W), hLM x.2⟩ : ↥M) ∈ L.subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr x.2
    rw [h] at h1
    have h2 : (x : MulAut W) ∈ L ⊓ conjAutSub t L := ⟨x.2, Subgroup.mem_subgroupOf.mp h1⟩
    rw [hinf, Subgroup.mem_bot] at h2
    exact hx1 (Subtype.ext h2)
  have hAut : Nat.card (MulAut ↥((conjAutSub t L).subgroupOf M)) ≤
      2 * Nat.card ↥((conjAutSub t L).subgroupOf M) :=
    opx_card_aut_le (excPair_congr
      ((d321b_conjEquiv t L).trans (Subgroup.subgroupOfEquivOfLe hL'M).symm) hex)
  have hpL' : p ∣ Nat.card ↥(L.subgroupOf M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv]
    exact hpL
  have hgp : ∃ k : ℕ, (⟨g, hgM⟩ : ↥M) ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hk
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hgL : ∀ x ∈ L.subgroupOf M, (⟨g, hgM⟩ : ↥M) * x * (⟨g, hgM⟩ : ↥M)⁻¹ = x := by
    intro x hx
    have hx' : (x : MulAut W) ∈ L := Subgroup.mem_subgroupOf.mp hx
    apply Subtype.ext
    show g * (x : MulAut W) * g⁻¹ = x
    rw [hgc _ hx']
    group
  have hgL' : ∀ x ∈ (conjAutSub t L).subgroupOf M,
      (⟨g, hgM⟩ : ↥M) * x * (⟨g, hgM⟩ : ↥M)⁻¹ ∈ (conjAutSub t L).subgroupOf M := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hgn _ (Subgroup.mem_subgroupOf.mp hx))
  have key := opx_cover φ hφ hp hp2 hrank hLh hs hinj hmap (opx_subgroupOf_conj htM) hne hAut
    hpL' hgp hgL hgL'
  exact Subgroup.mem_subgroupOf.mp key

end CFSG.Quasithin
