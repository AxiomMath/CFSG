module

public import CFSG.Quasithin.Vol2.Ch7Lem734
public import CFSG.Quasithin.Vol2.Ch7Faith
public import CFSG.Quasithin.Vol2.Ch7Lem761End
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.Background.S1549DL3M
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Vol2.Ch7E61

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem hyp318_of_normal (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : Hyp318 T (fsuM T L) (fsuL0 T L) (fsuV T I) := by
  have hU := lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 h39
    hyp.fsu.sylow hyp.fsu.maximal
  obtain ⟨h1, h2, h3⟩ := h3228 G T L I hyp.fsu
  have hperf : ⁅L, L⁆ = L := hyp.fsu.maximal.1.2.1.2.1
  exact { inM := ⟨hU.1.1, le_sup_right.trans hU.1.2⟩
          nonempty := ⟨H, hH⟩
          perfect := by
            rw [fsuL0_eq_of_le_normalizer hTL]
            exact eq_oTwoUpper_of_perfect hperf
          le_M := Subgroup.le_normalizer
          normal := le_rfl
          unique := ⟨⟨hU.1.1, sup_le Subgroup.le_normalizer (le_sup_right.trans hU.1.2)⟩,
            fun M' hM' => hU.2 M' ⟨hM'.1, (sup_le_sup_right (le_fsuL0 T L) T).trans hM'.2⟩⟩
          reduced := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr ⟨h1, h2⟩
          centralizer := h3 }

theorem omegaOneCenter_le_center (hC58 : TheoremC58) (h317 : AS317Sylow) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : quasithinOmegaOneCenter T ≤ centerOf H := by
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hJ := thompsonJ_le_centralizer_fsuV h37 h38 h39 hyp hV hN
  rcases theorem318_three hC58 h317 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
      (hyp318_of_normal h37 h38 h39 h3228 hyp hTL hH) with ⟨hJ', -⟩ | ⟨-, hZ, -⟩
  · exact absurd (le_inf (iSup₂_le fun _ hA => hA.1) hJ) hJ'
  · exact hZ H hH

theorem inf_fsuM_eq_of_normal (hC58 : TheoremC58) (h317 : AS317Sylow) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5)
    (hyp : Hyp7_0_2 G T L I) (hTL : T ≤ Subgroup.normalizer (L : Set G)) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) :
    H ⊓ fsuM T L = H ⊓ Subgroup.normalizer (fsuV T I : Set G) := by
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  exact inf_eq_inf_normalizer_of_center (isTISetUnder_of_le_normalizer h325 hyp.fsu hTL) hNM
    (fsuV_inf_omegaOneCenter_ne_bot hyp.fsu hV hN)
    (omegaOneCenter_le_center hC58 h317 h37 h38 h39 h3228 hyp hTL hH)

theorem pCoreOf_L_le_centralizer (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  have hQ : pCoreOf 2 (fsuL0 T L ⊔ T) = T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    (h3228 G T L I hyp.fsu).2.2
  have h1 : pCoreOf 2 L ≤ pCoreOf 2 (fsuL0 T L ⊔ T) := by
    rw [fsuL0_eq_of_le_normalizer hTL]
    exact S1549D.pCoreOf_le_pCoreOf_of_normalizes le_sup_left
      (sup_le Subgroup.le_normalizer hTL)
  exact (h1.trans hQ.le).trans inf_le_right

theorem not_le_centralizer_fsuV (hyp : Hyp7_0_2 G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ¬ L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  intro hLC
  apply hyp.fsu.irrPlus.2.1
  rw [← hyp.fsu.irrPlus.2.2.2.1]
  change ⁅I, fsuL0 T L⁆ = ⊥
  rw [fsuL0_eq_of_le_normalizer hTL, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro i hi
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp (hLC hl) i (le_fsuV I T hi)).symm

theorem inf_centralizer_le_of_faithful (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {H : Subgroup G}
    (hloc1 : H ⊓ fsuM T L = H ⊓ Subgroup.normalizer (fsuV T I : Set G))
    (h2c : ∃ P : Subgroup G, QuasithinUnique.IsSylowTwoOf P (oTwoUpper H ⊓ fsuM T L) ∧
      oTwoUpper H ⊓ fsuM T L ≤ Subgroup.normalizer (P : Set G))
    (hfaith : ∀ B : Subgroup G, B ≤ H ⊓ fsuM T L → Odd (Nat.card B) →
      (∃ k : ℕ, B.relIndex (H ⊓ fsuM T L) = 2 ^ k) → ∀ b ∈ B,
        (∀ m ∈ conjClosure L T, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 (conjClosure L T)) → b = 1) :
    H ⊓ fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (H ⊓ fsuM T L) := by
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hXV : H ⊓ fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [hloc1]
    exact inf_le_right
  have hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (le_fsuL0 T L).trans (le_sup_left.trans hN)
  have hNeq : H ⊓ fsuM T L ⊓ oTwoUpper H = oTwoUpper H ⊓ fsuM T L := by
    rw [inf_comm (H ⊓ fsuM T L), ← inf_assoc, inf_eq_left.mpr (oTwoUpper_le H)]
  have hN2 : E1.IsTwoClosed (H ⊓ fsuM T L ⊓ oTwoUpper H) := by
    obtain ⟨P, hP, hPn⟩ := h2c
    rw [hNeq]
    exact ⟨P, hP, (Subgroup.normal_subgroupOf_iff_le_normalizer hP.1).mpr hPn⟩
  have hB : ∀ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) →
      ∀ b ∈ B, (∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G)) →
        b = 1 := by
    intro B hB b hb hbl
    refine hfaith B hB.1 hB.2.1 hB.2.2 b hb ?_
    have hbM : b ∈ fsuM T L := (hB.1 hb).2
    have hbL : b ∈ Subgroup.normalizer (L : Set G) := by
      have := hbM
      change b ∈ Subgroup.normalizer (fsuL0 T L : Set G) at this
      rwa [hL0] at this
    change ∀ m ∈ fsuL0 T L, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 (fsuL0 T L)
    rw [hL0]
    exact commutatorElement_mem_pCoreOf_of_centralizer hyp.fsu.quasisimple
      hyp.fsu.maximal.1.2.1.2.1 hLN (pCoreOf_L_le_centralizer h3228 hyp hTL)
      (not_le_centralizer_fsuV hyp hTL) hbL hbl
  have hp := Vol2.Ch10.SecD.isPGroup_inf_centralizer (X := H ⊓ fsuM T L)
    (N := H ⊓ fsuM T L ⊓ oTwoUpper H) (L0 := L) inf_le_left hXV hLN hN2
    (fun x hx ho => ⟨hx, mem_oTwoUpper_of_odd hx.1 ho⟩)
    (Vol2.Ch10.SecD.exists_relIndex_oTwoUpper_eq_two_pow inf_le_left) hB
  exact QuasithinUnique.le_pCoreOf_of_normalizes inf_le_left
    (Vol2.Ch10.SecD.le_normalizer_inf_centralizer hXV) hp

end CFSG.Quasithin.H13
