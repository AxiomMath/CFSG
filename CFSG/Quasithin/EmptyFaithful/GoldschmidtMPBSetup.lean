module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7NoBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBlockCentrality
public import CFSG.Quasithin.Background.G11BridgeSQTK
public import CFSG.Quasithin.Background.C2Basic

public section

namespace CFSG.Quasithin.C58NS.MPB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {t : G} (hA : t ∈ Subgroup.normalizer (A : Set G))
    (hB : t ∈ Subgroup.normalizer (B : Set G)) :
    t ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite G] in
theorem le_normalizer_sup {H T R : Subgroup G} (hTH : T ≤ H)
    (hTR : T ≤ Subgroup.normalizer (R : Set G)) :
    T ≤ Subgroup.normalizer ((oTwoUpper H ⊔ R : Subgroup G) : Set G) := fun _ ht =>
  mem_normalizer_sup (le_normalizer_oTwoUpper H (hTH ht)) (hTR ht)

theorem isSubnormal_sup_oTwoUpper {H R : Subgroup G} (hRH : R ≤ H) :
    IsSubnormal (oTwoUpper H ⊔ R) H := by
  have hXH : oTwoUpper H ⊔ R ≤ H := sup_le (oTwoUpper_le H) hRH
  have hN : ((oTwoUpper H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).2
      (le_normalizer_oTwoUpper H)
  have hq : IsPGroup 2 (↥H ⧸ (oTwoUpper H).subgroupOf H) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H y.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.QuasithinUnique.Setup.Campbell.isSubnormal_of_pGroup_quotient
    (p := 2) ((oTwoUpper H).subgroupOf H) hq
    (X := (oTwoUpper H ⊔ R).subgroupOf H)
    (fun _ hx => (le_sup_left : oTwoUpper H ≤ oTwoUpper H ⊔ R) hx)
  exact (isSubnormal_iff_subgroupOf hXH).2 h

theorem le_of_proper_over {H T N Z : Subgroup G} (hmin : MinParabolic H T N) (hZH : Z ≤ H)
    (hTZ : T ≤ Z) (hZne : Z ≠ H) : Z ≤ N := by
  have hlt : Z < H := lt_of_le_of_ne hZH hZne
  obtain ⟨M, hM, hmax⟩ := Set.Finite.exists_maximalFor (fun x : Subgroup G => x)
    {Y : Subgroup G | Z ≤ Y ∧ Y < H} (Set.toFinite _) ⟨Z, le_rfl, hlt⟩
  have hMmax : IsMaxSubgroupIn H M := by
    refine ⟨hM.2, fun K hMK hKH => ?_⟩
    by_contra hne
    exact absurd (hmax ⟨hM.1.trans hMK.le, lt_of_le_of_ne hKH hne⟩ hMK.le) (not_le_of_gt hMK)
  have hMem : M ∈ maxOver H T := ⟨hMmax, hTZ.trans hM.1⟩
  have hU : maxOver H T = {N} := hmin.uniqueMax
  rw [hU] at hMem
  exact hM.1.trans (le_of_eq (Set.mem_singleton_iff.1 hMem))

omit [Finite G] in
theorem cgsIn_le_of_noCharNormal [Finite G] {H T N R X : Subgroup G} (hmin : MinParabolic H T N)
    (hTR : T ≤ Subgroup.normalizer (R : Set G))
    (hNC : Setup.Campbell.NoCharNormal R H) (hXH : X ≤ H) : cgsIn X R ≤ N := by
  unfold cgsIn
  refine iSup_le fun C => iSup_le fun hCR => iSup_le fun hC1 => iSup_le fun hCc => ?_
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := fun t ht =>
    Setup.Campbell.mem_normalizer_of_characteristic hCc hCR (hTR ht)
  have hne : H ⊓ Subgroup.normalizer (C : Set G) ≠ H := fun h =>
    hNC C hCR hC1 hCc (h ▸ inf_le_right)
  exact (inf_le_inf_right _ hXH).trans
    (le_of_proper_over hmin inf_le_left (le_inf hmin.isSylow.1 hTC) hne)

omit [Finite G] in
theorem mem_uFamHat {X R P M : Subgroup G} (hPX : P ≤ X) (hRP : R ≤ P)
    (hP : MinParabolic P R M) : P ∈ uFamHat X R := by
  refine ⟨⟨hPX, lt_of_le_of_ne hRP fun h => hP.not_normal ?_, ?_⟩, hP.not_normal⟩
  · rw [← h]
    exact Subgroup.le_normalizer
  · have hU : maxOver P R = {M} := hP.uniqueMax
    rw [hU, Set.ncard_singleton]

theorem isSQTKCat_of_isSQTKTC {H X : Subgroup G} (hXH : X ≤ H) (hH : IsSQTKTC H) :
    IsSQTKCat ↥X :=
  L246A7.isSQTKCat_of_le hXH ⟨G11.isStronglyQuasithin_of_tc hH.2, hH.1⟩

end CFSG.Quasithin.C58NS.MPB
