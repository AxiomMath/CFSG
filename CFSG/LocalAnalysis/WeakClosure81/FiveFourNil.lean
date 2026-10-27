module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

open scoped Pointwise

theorem isNilpotent_of_forall_supplement {K : Type} [Group K] [Finite K] {N T : Subgroup K}
    [N.Normal] (hN : Odd (Nat.card N)) (hT : IsPGroup 2 T)
    (hsupp : ∀ L : Subgroup K, T ≤ L → L ⊔ N = ⊤ → L = ⊤) : Group.IsNilpotent N := by
  classical
  refine (Group.isNilpotent_of_finite_tfae (G := ↥N)).out 4 1 |>.mp ?_
  intro p hp P
  haveI := hp
  letI : MulAction K (Sylow p ↥N) :=
    MulAction.compHom (Sylow p ↥N) (MulAut.conjNormal : K →* MulAut ↥N)
  have hodd : Odd (Nat.card (Sylow p ↥N)) := by
    rw [Sylow.card_eq_index_normalizer P]
    by_contra hcon
    rw [Nat.not_odd_iff_even] at hcon
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr
      (hcon.two_dvd.trans (Subgroup.index_dvd_card (Subgroup.normalizer (P : Set ↥N)))))
  have h2 : ¬ 2 ∣ Nat.card (Sylow p ↥N) := hodd.not_two_dvd_nat
  obtain ⟨R, hR⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p ↥N) h2
  have hRfix : ∀ t : ↥T, t • R = R := fun t => (MulAction.mem_fixedPoints.mp hR) t
  have hRnorm' : ((R : Subgroup ↥N).map N.subtype).Normal := by
    have hTL : T ≤ Subgroup.normalizer (R.map N.subtype) := by
      intro t ht
      have hsmul : (MulAut.conjNormal t : MulAut ↥N) • (R : Subgroup ↥N) = R := by
        have h1 : (⟨t, ht⟩ : ↥T) • R = R := hRfix ⟨t, ht⟩
        rw [Subgroup.smul_def] at h1
        have h2' : (MulAut.conjNormal t : MulAut ↥N) • R = R := h1
        have h3 := congrArg (fun S : Sylow p ↥N => (S : Subgroup ↥N)) h2'
        simpa only [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] using h3
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨n, hn, rfl⟩
        have hmem : (MulAut.conjNormal t : MulAut ↥N) n ∈ R := by
          have h1 := Subgroup.smul_mem_pointwise_smul n (MulAut.conjNormal t : MulAut ↥N) R hn
          rwa [hsmul] at h1
        exact ⟨(MulAut.conjNormal t : MulAut ↥N) n, hmem, rfl⟩
      · rintro ⟨n, hn, hx⟩
        have hsmul' : ((MulAut.conjNormal t : MulAut ↥N))⁻¹ • (R : Subgroup ↥N) = R := by
          have h2' := congrArg
            (fun S : Subgroup ↥N => ((MulAut.conjNormal t : MulAut ↥N))⁻¹ • S) hsmul
          rw [← mul_smul, inv_mul_cancel, one_smul] at h2'
          exact h2'.symm
        have hmem : ((MulAut.conjNormal t : MulAut ↥N))⁻¹ n ∈ R := by
          have h1 := Subgroup.smul_mem_pointwise_smul n
            ((MulAut.conjNormal t : MulAut ↥N))⁻¹ R hn
          rwa [hsmul'] at h1
        refine ⟨((MulAut.conjNormal t : MulAut ↥N))⁻¹ n, hmem, ?_⟩
        have hx' : x = t⁻¹ * N.subtype n * t := by
          rw [hx]
          group
        rw [hx']
        exact MulAut.conjNormal_inv_apply t n
    exact (Subgroup.normalizer_eq_top_iff).mp (hsupp _ hTL (Sylow.normalizer_sup_eq_top R))
  have hRnorm : (R : Subgroup ↥N).Normal := hRnorm'.of_map_subtype
  have hPR : P = R := by
    haveI : (R : Subgroup ↥N).Normal := hRnorm
    have hRP : (R : Subgroup ↥N) ≤ P := by
      have hp' : IsPGroup p ((R : Subgroup ↥N) ⊔ P : Subgroup ↥N) :=
        R.isPGroup'.to_sup_of_normal_left P.isPGroup'
      exact le_sup_left.trans (P.3 hp' le_sup_right).le
    have hcard : Nat.card P ≤ Nat.card R := by
      rw [P.card_eq_multiplicity, R.card_eq_multiplicity]
    exact Sylow.ext (Subgroup.eq_of_le_of_card_ge hRP hcard).symm
  rw [hPR]
  exact hRnorm

theorem isNilpotent_quotient_of_supplement {G : Type} [Group G] [Finite G]
    {H Y P T : Subgroup G} [(P.subgroupOf Y).Normal] (hYH : Y ≤ H)
    (hY : (Y.subgroupOf H).Normal) (hPY : P ≤ Y) (hP : (P.subgroupOf H).Normal)
    (hPS : IsSylowIn 2 P Y) (hT : IsPGroup 2 T) (hTH : T ≤ H)
    (hsupp : ∀ L : Subgroup G, L ≤ H → T ≤ L → Y ⊔ L = H → L = H) :
    Group.IsNilpotent (↥Y ⧸ P.subgroupOf Y) := by
  classical
  let P' : Subgroup ↥H := P.subgroupOf H
  let Y' : Subgroup ↥H := Y.subgroupOf H
  haveI hP' : P'.Normal := hP
  haveI hY' : Y'.Normal := hY
  have hP'Y' : P' ≤ Y' := fun x hx => hPY hx
  let q : ↥H →* (↥H ⧸ P') := QuotientGroup.mk' P'
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective P'
  have hqker : q.ker = P' := QuotientGroup.ker_mk' P'
  let N : Subgroup (↥H ⧸ P') := Y'.map q
  let T' : Subgroup (↥H ⧸ P') := (T.subgroupOf H).map q
  haveI hN : N.Normal := hY.map q hqsurj
  let f : ↥Y →* ↥N :=
    { toFun := fun y => ⟨q ⟨y.1, hYH y.2⟩, ⟨⟨y.1, hYH y.2⟩, y.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        exact map_one q
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul q ⟨a.1, hYH a.2⟩ ⟨b.1, hYH b.2⟩ }
  have hf : Function.Surjective f := by
    rintro ⟨n, hn⟩
    change n ∈ Y'.map q at hn
    obtain ⟨y', hy', rfl⟩ := hn
    refine ⟨⟨y'.1, hy'⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hker : f.ker = P.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hy
      have h1 : q ⟨y.1, hYH y.2⟩ = 1 := Subtype.ext_iff.mp hy
      have h1' : (⟨y.1, hYH y.2⟩ : ↥H) ∈ P' :=
        (QuotientGroup.eq_one_iff (⟨y.1, hYH y.2⟩ : ↥H)).mp h1
      exact Subgroup.mem_subgroupOf.mp h1'
    · intro hy
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (⟨y.1, hYH y.2⟩ : ↥H)).mpr
        (Subgroup.mem_subgroupOf.mpr hy)
  let e : (↥Y ⧸ P.subgroupOf Y) ≃* ↥N :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hNodd : Odd (Nat.card ↥N) := by
    have hcard : Nat.card ↥N = P.relIndex Y := by
      rw [← Nat.card_congr e.toEquiv]
      rfl
    rw [hcard, ← Nat.not_even_iff_odd]
    exact fun he => hPS.not_dvd_relIndex (even_iff_two_dvd.mp he)
  have hT' : IsPGroup 2 T' := by
    have h1 : IsPGroup 2 (T.subgroupOf H) := hT.comap_subtype
    simpa [T'] using h1.map q
  have hsuppK : ∀ Lq : Subgroup (↥H ⧸ P'), T' ≤ Lq → Lq ⊔ N = ⊤ → Lq = ⊤ := by
    intro Lq hT'L hLN
    have hLle : (Lq.comap q).map H.subtype ≤ H := Subgroup.map_subtype_le _
    have hTL : T ≤ (Lq.comap q).map H.subtype := by
      intro t ht
      exact ⟨⟨t, hTH ht⟩, hT'L ⟨⟨t, hTH ht⟩, ht, rfl⟩, rfl⟩
    have hYL : Y ⊔ (Lq.comap q).map H.subtype = H := by
      have hNcomap : N.comap q = Y' := by
        dsimp only [N]
        rw [Subgroup.comap_map_eq q Y', hqker]
        exact sup_eq_left.mpr hP'Y'
      have h1 : (Lq ⊔ N).comap q = ⊤ := by rw [hLN, Subgroup.comap_top]
      rw [← Subgroup.comap_sup_eq q Lq N hqsurj, hNcomap] at h1
      have h2' := congrArg (Subgroup.map H.subtype) h1
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hYH, Subgroup.map_top,
        Subgroup.range_subtype, sup_comm] at h2'
      exact h2'
    have hLH : (Lq.comap q).map H.subtype = H := hsupp _ hLle hTL hYL
    have hLtop : Lq.comap q = ⊤ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_top, Subgroup.range_subtype]
      exact hLH
    calc Lq = (Lq.comap q).map q := (Subgroup.map_comap_eq_self_of_surjective hqsurj Lq).symm
      _ = ⊤ := by rw [hLtop, Subgroup.map_top_of_surjective q hqsurj]
  have hnil : Group.IsNilpotent ↥N := isNilpotent_of_forall_supplement hNodd hT' hsuppK
  haveI : Group.IsNilpotent ↥N := hnil
  exact Group.nilpotent_of_mulEquiv e.symm

end CFSG.LocalAnalysis.WeakClosure81
