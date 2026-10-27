module

public import CFSG.RankThree.PartTwo.Sec15.LiebeckY4ProdHJKRec
public import CFSG.RankThree.PartTwo.Sec15.LiebeckY4ProdDefs
import CFSG.RankThree.PartTwo.Sec15.LiebeckY4ProdCoreA
import CFSG.RankThree.PartTwo.Sec15.LiebeckY4ProdSmall
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiag
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Ronan148JStruct
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec6.Item65Tools

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckY4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag

section Factors

variable {Γ : Type} [Group Γ] {U V E : Subgroup Γ}

theorem ProdSetting.symm (h : ProdSetting U V E) : ProdSetting V U E where
  comm v hv u hu := (h.comm u hu v hv).symm
  elem := h.elem
  card := h.card
  norm := by rw [sup_comm]; exact h.norm
  perfect := by rw [sup_comm]; exact h.perfect
  rank := h.rank
  gen := by rw [sup_comm]; exact h.gen

theorem mem_left_of_centralizes_five (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (eV : ↥V ≃* alternatingGroup (Fin 5)) {x : Γ} (hx : x ∈ U ⊔ V)
    (hxV : ∀ v ∈ V, x * v = v * x) : x ∈ U := by
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_eq_of_mem_sup hc hx
  have hvc : ∀ w ∈ V, w * v = v * w := by
    intro w hw
    apply mul_left_cancel (a := u)
    calc u * (w * v) = u * w * v := (mul_assoc _ _ _).symm
      _ = w * u * v := by rw [hc u hu w hw]
      _ = w * (u * v) := mul_assoc _ _ _
      _ = (u * v) * w := (hxV w hw).symm
      _ = u * (v * w) := mul_assoc _ _ _
  rw [eq_one_of_center_eq_bot (center_eq_bot_five eV) hv hvc, mul_one]
  exact hu

end Factors

theorem eq_bot_of_normalized_of_facHJ {Γ : Type} [Group Γ]
    {U P : Subgroup Γ} (hU : FacHJ ↥U) (hUP : U ≤ Subgroup.normalizer (P : Set Γ))
    (hP3 : ¬ 3 ∣ Nat.card P) : P ⊓ U = ⊥ := by
  obtain ⟨eU⟩ := hU
  have : IsSimpleGroup ↥U := by
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    exact eU.isSimpleGroup
  have hUc : Nat.card U = 604800 :=
    (Nat.card_congr eU.toEquiv).trans KFacts.KS14.card_nativeJ2
  have hn : ((P ⊓ U).subgroupOf U).Normal := by
    refine ⟨fun x hx w => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hUP w.2) x).mp hx.1,
      U.mul_mem (U.mul_mem w.2 hx.2) (U.inv_mem w.2)⟩
  haveI := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((P ⊓ U).subgroupOf U) with h | h
  · rwa [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_assoc, inf_idem] at h
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at h
    have h2 : Nat.card U ∣ Nat.card P := Subgroup.card_dvd_of_le (h.trans inf_le_left)
    rw [hUc] at h2
    exact hP3 ((show 3 ∣ 604800 by norm_num).trans h2)

section Preimage

variable {G : Type} [Group G] {A M : Subgroup G} [(ker148 A M).Normal]

theorem exists_img148_eq (hAM : A ≤ Subgroup.normalizer (M : Set G))
    {V : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)} (hVM : V ≤ img148 A M M)
    (hVN : img148 A M A ≤ Subgroup.normalizer (V : Set (↥(M ⊔ A) ⧸ ker148 A M))) :
    ∃ W : Subgroup G, W ≤ M ∧ A ≤ Subgroup.normalizer (W : Set G) ∧ img148 A M W = V := by
  set φ : ↥M →* ↥(M ⊔ A) ⧸ ker148 A M :=
    (QuotientGroup.mk' (ker148 A M)).comp (Subgroup.inclusion (le_sup_left : M ≤ M ⊔ A)) with hφ
  have hmem : ∀ g : G, g ∈ (V.comap φ).map M.subtype ↔
      ∃ hg : g ∈ M, QuotientGroup.mk' (ker148 A M) (⟨g, Subgroup.mem_sup_left hg⟩ : ↥(M ⊔ A)) ∈
        V := by
    intro g
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hg, h⟩
      exact ⟨⟨g, hg⟩, h, rfl⟩
  refine ⟨(V.comap φ).map M.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have key : ∀ a ∈ A, ∀ g ∈ (V.comap φ).map M.subtype,
        a * g * a⁻¹ ∈ (V.comap φ).map M.subtype := by
      intro a ha g hg
      obtain ⟨hgM, hgV⟩ := (hmem g).mp hg
      have hgM' : a * g * a⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hAM ha) g).mp hgM
      refine (hmem _).mpr ⟨hgM', ?_⟩
      have e : (⟨a * g * a⁻¹, Subgroup.mem_sup_left hgM'⟩ : ↥(M ⊔ A)) =
          ⟨a, Subgroup.mem_sup_right ha⟩ * ⟨g, Subgroup.mem_sup_left hgM⟩ *
            ⟨a, Subgroup.mem_sup_right ha⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      have hα : QuotientGroup.mk' (ker148 A M) (⟨a, Subgroup.mem_sup_right ha⟩ : ↥(M ⊔ A)) ∈
          img148 A M A := alpha148_mem_img148 ha
      exact (Subgroup.mem_normalizer_iff.mp (hVN hα) _).mp hgV
    intro a ha
    refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => key a ha g hg, fun hg => ?_⟩
    have := key a⁻¹ (A.inv_mem ha) _ hg
    simpa [mul_assoc] using this
  · ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ((hmem (m : G)).mp hm).2
    · intro hx
      obtain ⟨g, hg, hgM, rfl⟩ := mem_img148_iff.mp (hVM hx)
      exact mem_img148_iff.mpr ⟨g, hg, (hmem g).mpr ⟨hgM, hx⟩, rfl⟩

end Preimage

section Hyperplane


theorem exists_hyperplane_img148_ne_bot {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {c : G} {L : Subgroup G} (h : Sec15R G A c L) {M : Subgroup G} [(ker148 A M).Normal]
    {J : Subgroup G} {V : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)}
    (hset : ProdSetting (img148 A M J) V (img148 A M A))
    (hsup : img148 A M (deltaZero A (lB A) M) = img148 A M J ⊔ V)
    (hH : ProdTypeHJ (img148 A M J) V) :
    ∃ B' : Subgroup G, IsHyperplane A B' ∧
      img148 A M (deltaZero A (lB A) (M ⊓ Subgroup.centralizer (B' : Set G))) ≠ ⊥ ∧
      img148 A M (deltaZero A (lB A) (M ⊓ Subgroup.centralizer (B' : Set G))) ≤
        img148 A M J := by
  have hA := h.toSec14Std.isE27
  obtain ⟨hinf, ⟨eU⟩, ⟨eV⟩⟩ := hH
  have htA : ProdTypeA V (img148 A M J) :=
    Or.inr ⟨by rwa [inf_comm], Or.inr (Or.inr (Or.inr ⟨⟨eV⟩, ⟨eU⟩⟩))⟩
  obtain ⟨BE, hBE, ha, hb, -⟩ := prodCoreA_holds fixA5_holds fixA6Cover_holds centJ2E9_holds _ V
    (img148 A M J) (img148 A M A) hset.symm htA
  obtain ⟨B, hB, rfl⟩ := exists_hyperplane_of_img hA hBE
  have hRU : ∀ B' : Subgroup G, IsHyperplane A B' → B' ≠ B →
      img148 A M (deltaZero A (lB A) (M ⊓ Subgroup.centralizer (B' : Set G))) ≤
        img148 A M J := by
    intro B' hB' hne
    refine img148_deltaZero_centralizer_le fun Q hQ hBQ => ?_
    have hne' : img148 A M B' ≠ img148 A M B := fun heq =>
      hne (le_antisymm (le_of_img148_le hA hB'.1 hB.1 heq.le)
        (le_of_img148_le hA hB.1 hB'.1 heq.ge))
    refine hb (img148 A M B') (isHyperplane_img148 hA hB') hne' Q ?_ hBQ
    rw [sup_comm V (img148 A M J), ← hsup]
    exact hQ
  have hRV : img148 A M (deltaZero A (lB A) (M ⊓ Subgroup.centralizer (B : Set G))) ≤ V := by
    refine img148_deltaZero_centralizer_le fun Q hQ hBQ => ha Q ?_ hBQ
    rw [sup_comm V (img148 A M J), ← hsup]
    exact hQ
  by_contra hno
  push Not at hno
  have hDV : img148 A M (deltaZero A (lB A) M) ≤ V := by
    refine Ronan148J.img148_deltaZero_le_of_hyperplanes hA fun B' hB' R hR hRB' => ?_
    have hle : img148 A M R ≤ img148 A M (deltaZero A (lB A)
        (M ⊓ Subgroup.centralizer (B' : Set G))) := img148_mono (le_deltaZero hR hRB')
    by_cases hBB : B' = B
    · subst hBB
      exact hle.trans hRV
    · have hbot : img148 A M (deltaZero A (lB A)
          (M ⊓ Subgroup.centralizer (B' : Set G))) = ⊥ := by
        by_contra hne
        exact hno B' hB' hne (hRU B' hB' hBB)
      exact (hle.trans hbot.le).trans bot_le
  have hUV : img148 A M J ≤ V := le_sup_left.trans (hsup ▸ hDV)
  have hU1 : img148 A M J = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact le_inf le_rfl hUV
  have : Nontrivial ↥(img148 A M J) := by
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    exact eU.toEquiv.nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this hU1

end Hyperplane

section Main


theorem not_isSolvable_delta_of_prodTypeHJ (hCore : Step148Core) (hPoint : Step148Point)
    (hKT : Step148KType) (hLift : Step148Lift) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (hall : AllPointsHJ A) {M : Subgroup G} [(ker148 A M).Normal]
    (hM : M ∈ scriptY A) {J : Subgroup G} (hJM : J ∈ thetaComponentsIn M)
    {V : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)} (hset : ProdSetting (img148 A M J) V (img148 A M A))
    (hsup : img148 A M (deltaZero A (lB A) M) = img148 A M J ⊔ V)
    (hH : ProdTypeHJ (img148 A M J) V) :
    ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 (delta A (lB A) J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨B', -, hRne, hRU⟩ := exists_hyperplane_img148_ne_bot h hset hsup hH
  obtain ⟨-, ⟨eU⟩, ⟨eV⟩⟩ := hH
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := hM.2
  have hJle : J ≤ M := le_of_mem_thetaComponentsIn hJM
  have hVN : img148 A M A ≤ Subgroup.normalizer (V : Set (↥(M ⊔ A) ⧸ ker148 A M)) := fun e he =>
    (mem_normalizer_of_five_j2 (fun v hv u hu => (hset.comm u hu v hv).symm) eV eU
      (by rw [sup_comm V (img148 A M J)]; exact hset.norm he)).1
  have hVM : V ≤ img148 A M M := by
    have h1 : img148 A M J ⊔ V ≤ img148 A M M := hsup ▸ img148_mono (deltaZero_le M)
    exact le_sup_right.trans h1
  obtain ⟨W, -, hAW, hWV⟩ := exists_img148_eq hAM hVM hVN
  set Y1 := Ronan148M.centPre148 A M W with hY1def
  have hY1 : Y1 ∈ scriptY A := Ronan148M.centPre148_mem_scriptY hM hAW
  have hY1M : Y1 ≤ M := Ronan148M.centPre148_le
  have hJY1 : J ≤ Y1 := by
    intro g hg
    refine Ronan148M.mem_centPre148_iff.mpr
      ⟨hJle hg, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx' : x ∈ V := hWV ▸ hx
    have hgU : QuotientGroup.mk' (ker148 A M) (⟨g, Subgroup.mem_sup_left (hJle hg)⟩ : ↥(M ⊔ A)) ∈
        img148 A M J := mem_img148_iff.mpr ⟨g, _, hg, rfl⟩
    exact (hset.comm _ hgU x hx').symm
  have hY1s : ¬ Group.IsSolvable ↥Y1 :=
    Proof15Res8Solv.not_isSolvable_of_le hJY1 (isPerfect_of_mem_thetaComponentsIn hJM)
      (Y4Core.ne_bot_of_mem_thetaComponentsIn hJM)
  have hD : ¬ deltaZero A (lB A) Y1 ≤ pPrimeCoreOf 3 Y1 := by
    intro hle
    have h1 : deltaZero A (lB A) (M ⊓ Subgroup.centralizer (B' : Set G)) ≤
        deltaZero A (lB A) Y1 := by
      refine sSup_le fun R hR => ?_
      have hRc : img148 A M R ≤
          Subgroup.centralizer (img148 A M W : Set (↥(M ⊔ A) ⧸ ker148 A M)) := by
        rw [hWV]
        intro x hx
        have hxU : x ∈ img148 A M J := hRU (img148_mono (le_deltaZero hR.1 hR.2) hx)
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (hset.comm x hxU v hv).symm
      exact Ronan148J.le_deltaZero_centPre148 hR.1 (hR.2.trans inf_le_left) hRc
    have h2 : img148 A M (deltaZero A (lB A) (M ⊓ Subgroup.centralizer (B' : Set G))) ≤
        img148 A M (pPrimeCoreOf 3 Y1) := img148_mono (h1.trans hle)
    have hN3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 Y1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y1)
    have h3 := eq_bot_of_normalized_of_facHJ (U := img148 A M J) ⟨eU⟩
      ((img148_mono hJY1).trans (img148_le_normalizer (le_normalizer_pPrimeCoreOf 3 Y1)))
      (Item148PtRes.not_three_dvd_card_img148 hN3)
    exact hRne (le_bot_iff.mp ((le_inf h2 hRU).trans h3.le))
  obtain ⟨J', hJ', K, hKJ', hKΔ, hKnc, hKns⟩ :=
    exists_kRecord hCore hPoint hKT hLift h45 h48 h hall hY1 hY1s hD
  have hKY1 : K ≤ Y1 := hKJ'.trans (le_of_mem_thetaComponentsIn hJ')
  have himgK : img148 A M K ≤ img148 A M J := by
    have h1 := (img148_mono (hKΔ.le.trans (deltaZero_mono hKY1))).trans
      (Ronan148M.img148_deltaZero_centPre148_le (A := A) (Y := M) (J := W) (LB := lB A))
    rw [hWV, hsup] at h1
    intro x hx
    obtain ⟨hxD, hxC⟩ := h1 hx
    exact mem_left_of_centralizes_five hset.comm eV hxD fun v hv =>
      (Subgroup.mem_centralizer_iff.mp hxC v hv).symm
  have hKJ : ∀ k ∈ K, ∃ j ∈ J, j⁻¹ * k ∈ pPrimeCoreOf 3 Y1 := by
    intro k hk
    have hkM : k ∈ M ⊔ A := Subgroup.mem_sup_left (hY1M (hKY1 hk))
    obtain ⟨j, hjm, hjJ, hjk⟩ :=
      mem_img148_iff.mp (himgK (mem_img148_iff.mpr ⟨k, hkM, hk, rfl⟩))
    exact ⟨j, hjJ, Ronan148M.pPrimeCoreOf_le_pPrimeCoreOf_centPre148 (mk'_ker148_eq_iff.mp hjk)⟩
  have hJY1' : J ∈ thetaComponentsIn Y1 :=
    Sec6.mem_thetaComponentsIn_of hJY1 (isPerfect_of_mem_thetaComponentsIn hJM)
      (Sec18.isSubnormal_subgroupOf_of_le (mem_thetaComponentsIn_iff.mp hJM).2.2.1 hY1M)
      (isQuasisimple_theta_of_mem_thetaComponentsIn hJM)
  exact not_isSolvable_oPrimeResidual_delta_of
    (le_of_map_le_of_nonabelian hJY1' hJ' hKJ' (map_le_of_forall_exists_mem hJY1 hKJ) hKnc)
    hKΔ hKns

end Main

end CFSG.RankThree.PartTwo.Sec15.LiebeckY4
