module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne (pElementSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_two_outer_of_isA5xA5 {Q : Type} [Group Q] [Finite Q] (hQ : IsA5xA5 Q) :
    IsPGroup 2 (CFSG.ComponentClassification.OuterAutomorphisms.Outer Q) := by
  obtain ⟨e⟩ := hQ
  let H := alternatingGroup (Fin 5) × alternatingGroup (Fin 5)
  have hcenter : Subgroup.center H = ⊥ :=
    center_eq_bot_of_isA5xA5 ⟨MulEquiv.refl H⟩
  have hcardA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hcardH : Nat.card H = 3600 := by
    rw [Nat.card_prod, hcardA5]
  have hcard : Nat.card (Outer H) = 8 := by
    have hinner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner H) =
        Nat.card H :=
      CFSG.ComponentClassification.InnerActionOrder.centerless_card H hcenter
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.ComponentClassification.OuterAutomorphisms.inner H)
    rw [hinner, CFSG.EvenSporadicStandard.TwoHS.card_mulAut_A5A5, hcardH] at hq
    change Nat.card (MulAut H ⧸
      CFSG.ComponentClassification.OuterAutomorphisms.inner H) = 8
    omega
  have hH : IsPGroup 2 (Outer H) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [hcard]
    norm_num
  exact hH.of_equiv (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm

theorem pElementSubgroup_eq_self_of_isA5xA5 {Q : Type} [Group Q] [Finite Q]
    {A : Subgroup Q} (hA : IsA5xA5 ↥A) :
    CFSG.RankThree.PartOne.pElementSubgroup 5 A = A := by
  obtain ⟨e⟩ := hA
  have hcardA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hA5top : CFSG.RankThree.PartOne.pElementSubgroup 5
      (⊤ : Subgroup (alternatingGroup (Fin 5))) = ⊤ := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := alternatingGroup (Fin 5)) 5 (by rw [hcardA5]; norm_num)
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hz
      omega
    have hsimple : IsSimpleGroup (⊤ : Subgroup (alternatingGroup (Fin 5))) :=
      (Subgroup.topEquiv (G := alternatingGroup (Fin 5))).isSimpleGroup_congr.mpr
        alternatingGroup.isSimpleGroup_five
    exact CFSG.RankThree.PartOne.KFU.pElementSubgroup_eq_of_simple hsimple
      (Subgroup.mem_top z) hz hz1
  have hProdTop : CFSG.RankThree.PartOne.pElementSubgroup 5
      (⊤ : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) = ⊤ := by
    refine le_antisymm le_top ?_
    intro p hp
    have hp1 : p.1 ∈ CFSG.RankThree.PartOne.pElementSubgroup 5
        (⊤ : Subgroup (alternatingGroup (Fin 5))) := by
      rw [hA5top]
      exact Subgroup.mem_top p.1
    have hp2 : p.2 ∈ CFSG.RankThree.PartOne.pElementSubgroup 5
        (⊤ : Subgroup (alternatingGroup (Fin 5))) := by
      rw [hA5top]
      exact Subgroup.mem_top p.2
    have hleft : (CFSG.RankThree.PartOne.pElementSubgroup 5
        (⊤ : Subgroup (alternatingGroup (Fin 5)))).map
        (MonoidHom.inl (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))) ≤
        CFSG.RankThree.PartOne.pElementSubgroup 5
          (⊤ : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) := by
      rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map Nat.prime_five]
      exact s13_Thirteen2_pElementSubgroup_mono le_top
    have hright : (CFSG.RankThree.PartOne.pElementSubgroup 5
        (⊤ : Subgroup (alternatingGroup (Fin 5)))).map
        (MonoidHom.inr (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))) ≤
        CFSG.RankThree.PartOne.pElementSubgroup 5
          (⊤ : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) := by
      rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map Nat.prime_five]
      exact s13_Thirteen2_pElementSubgroup_mono le_top
    have h1 : (p.1, 1) ∈ CFSG.RankThree.PartOne.pElementSubgroup 5
        (⊤ : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) :=
      hleft ⟨p.1, hp1, rfl⟩
    have h2 : (1, p.2) ∈ CFSG.RankThree.PartOne.pElementSubgroup 5
        (⊤ : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) :=
      hright ⟨p.2, hp2, rfl⟩
    have hmul := (CFSG.RankThree.PartOne.pElementSubgroup 5
      (⊤ : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))).mul_mem h1 h2
    simpa using hmul
  have htopA : CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup ↥A) = ⊤ := by
    have hmap : (CFSG.RankThree.PartOne.pElementSubgroup 5
        (⊤ : Subgroup ↥A)).map e.toMonoidHom = ⊤ := by
      rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map Nat.prime_five
        e.toMonoidHom ⊤, Subgroup.map_top_of_surjective _ e.surjective, hProdTop]
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hmap, Subgroup.map_top_of_surjective _ e.surjective]
  calc CFSG.RankThree.PartOne.pElementSubgroup 5 A
      = (CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup ↥A)).map A.subtype := by
        rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map Nat.prime_five
          A.subtype ⊤]
        congr 1
        rw [Subgroup.map_top, Subgroup.range_subtype]
    _ = (⊤ : Subgroup ↥A).map A.subtype := by rw [htopA]
    _ = A := by rw [Subgroup.map_top, Subgroup.range_subtype]

theorem exists_mul_centralizer_of_pow_five {Q : Type} [Group Q] [Finite Q]
    {A : Subgroup Q} [A.Normal] (hA : IsA5xA5 ↥A) {g : Q} {k : ℕ}
    (hg : g ^ 5 ^ k = 1) :
    ∃ a ∈ A, ∃ c ∈ Subgroup.centralizer (A : Set Q),
      g = a * c ∧ a ^ 5 ^ k = 1 ∧ c ^ 5 ^ k = 1 := by
  have hOut2 : IsPGroup 2 (Outer ↥A) := isPGroup_two_outer_of_isA5xA5 hA
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOut5 : ¬ 5 ∣ Nat.card (Outer ↥A) := by
    obtain ⟨m, hm⟩ := hOut2.exists_card_eq
    rw [hm]
    intro hd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd) (by norm_num)
  have hf : (MulAut.conjNormal (H := A) g : MulAut ↥A) ^ 5 ^ k = 1 := by
    rw [← map_pow, hg, map_one]
  let f : MulAut ↥A := MulAut.conjNormal (H := A) g
  have hmem : f ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥A := by
    have h1 : orderOf (QuotientGroup.mk'
        (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥A) f) ∣ 5 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, show f ^ 5 ^ k = 1 from hf, map_one])
    have h2 : orderOf (QuotientGroup.mk'
        (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥A) f) ∣
        Nat.card (Outer ↥A) := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (5 ^ k) (Nat.card (Outer ↥A)) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hOut5)
    have h3 : orderOf (QuotientGroup.mk'
        (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥A) f) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rwa [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  obtain ⟨a, ha⟩ := hmem
  have ha' : MulAut.conj a = MulAut.conjNormal (H := A) g := by simpa [f] using ha
  have hinj : Function.Injective (MulAut.conj : ↥A →* MulAut ↥A) := by
    rw [← MonoidHom.ker_eq_bot_iff,
      CFSG.ComponentClassification.InnerActionOrder.conjugation_kernel]
    exact center_eq_bot_of_isA5xA5 hA
  have ha_pow : a ^ 5 ^ k = 1 := by
    apply hinj
    rw [map_pow, ha', hf, map_one]
  have haQ : (a : Q) ^ 5 ^ k = 1 := by
    have := congrArg (fun x : ↥A => (x : Q)) ha_pow
    simpa using this
  let c : Q := (a : Q)⁻¹ * g
  have hc : c ∈ Subgroup.centralizer (A : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun φ : MulAut ↥A => ((φ ⟨y, hy⟩ : ↥A) : Q)) ha'
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h
    calc y * c = (a : Q)⁻¹ * ((a : Q) * y * (a : Q)⁻¹) * g := by
          simp only [c]
          group
      _ = (a : Q)⁻¹ * (g * y * g⁻¹) * g := by rw [h]
      _ = c * y := by
          simp only [c]
          group
  have hg_eq : g = (a : Q) * c := by simp [c]
  have hcomm : Commute (a : Q) c :=
    Subgroup.mem_centralizer_iff.mp hc (a : Q) a.2
  have hc_pow : c ^ 5 ^ k = 1 := by
    have h := hcomm.mul_pow (5 ^ k)
    rw [← hg_eq, hg, haQ, one_mul] at h
    exact h.symm
  exact ⟨(a : Q), a.2, c, hc, hg_eq, haQ, hc_pow⟩

theorem pElementSubgroup_top_eq_sup_of_isA5xA5 {Q : Type} [Group Q] [Finite Q]
    {A : Subgroup Q} [A.Normal] (hA : IsA5xA5 ↥A) :
    CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup Q) =
      A ⊔ CFSG.RankThree.PartOne.pElementSubgroup 5
        (Subgroup.centralizer (A : Set Q)) := by
  refine le_antisymm ?_ ?_
  ·
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨-, k, hk⟩
    have hg : x ^ 5 ^ k = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one x
    obtain ⟨a, ha, c, hc, hx, -, hc_pow⟩ := exists_mul_centralizer_of_pow_five hA hg
    have hcP : c ∈ CFSG.RankThree.PartOne.pElementSubgroup 5
        (Subgroup.centralizer (A : Set Q)) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp
        (orderOf_dvd_of_pow_eq_one hc_pow)
      exact Subgroup.subset_closure ⟨hc, j, hj⟩
    rw [hx]
    exact Subgroup.mul_mem_sup ha hcP
  ·
    refine sup_le ?_ ?_
    · have hAeq : CFSG.RankThree.PartOne.pElementSubgroup 5 A = A :=
        pElementSubgroup_eq_self_of_isA5xA5 hA
      rw [← hAeq]
      exact s13_Thirteen2_pElementSubgroup_mono le_top
    · exact s13_Thirteen2_pElementSubgroup_mono le_top

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
