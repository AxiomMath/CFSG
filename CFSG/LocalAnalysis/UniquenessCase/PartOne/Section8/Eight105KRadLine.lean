module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadEigen
import CFSG.RankThree.PartOne.K133.PerfectUnip4
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LinearGroups (stdHermForm)
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f ε : ℕ}
  {b : StatedSU (2 * 2 + ε) (2 ^ f) K} {ω : K}

private noncomputable def kOfAct :
    ↥(F08.KOf8103 ⊤ (zpowers b)) →* Module.End K (Fin (2 * 2 + ε) → K) :=
  (Units.coeHom (Module.End K (Fin (2 * 2 + ε) → K))).comp
    (((Matrix.GeneralLinearGroup.toLin (n := Fin (2 * 2 + ε)) (R := K)).toMonoidHom).comp
      ((StatedSU (2 * 2 + ε) (2 ^ f) K).subtype.comp
        (F08.KOf8103 ⊤ (zpowers b)).subtype))

omit [Finite K] [CharP K 2] in
private theorem kOfAct_apply (k : ↥(F08.KOf8103 ⊤ (zpowers b)))
    (v : Fin (2 * 2 + ε) → K) :
    kOfAct (b := b) k v =
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v := by
  simp [kOfAct, Matrix.GeneralLinearGroup.coe_toLin]

omit [CharP K 2] in
private theorem kOfAct_perfect :
    Group.IsPerfect ↥(F08.KOf8103 ⊤ (zpowers b)) := by
  let X : Subgroup (StatedSU (2 * 2 + ε) (2 ^ f) K) :=
    ⊤ ⊓ centralizer ((zpowers b : Subgroup (StatedSU (2 * 2 + ε) (2 ^ f) K)) :
      Set (StatedSU (2 * 2 + ε) (2 ^ f) K))
  let P : Subgroup ↥X := ⨅ n : ℕ, derivedSeries ↥X n
  have hP : Group.IsPerfect ↥P := CFSG.perfect_residual_characterization.2.2.1
  change Group.IsPerfect ↥(P.map X.subtype)
  exact @Group.IsPerfect.map _ _ _ _ _ X.subtype hP

omit [Finite K] [CharP K 2] in
private theorem kOfAct_fix_of_finrank_le_one
    (hperf : Group.IsPerfect ↥(F08.KOf8103 ⊤ (zpowers b)))
    {L : Submodule K (Fin (2 * 2 + ε) → K)} (hL : Module.finrank K L ≤ 1)
    (hLstab : ∀ k : ↥(F08.KOf8103 ⊤ (zpowers b)), ∀ v ∈ L,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v ∈ L) :
    ∀ k : ↥(F08.KOf8103 ⊤ (zpowers b)), ∀ v ∈ L,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v = v := by
  let ρ : ↥(F08.KOf8103 ⊤ (zpowers b)) →*
      Module.End K (Fin (2 * 2 + ε) → K) := kOfAct (b := b)
  have hρ : ∀ (k : ↥(F08.KOf8103 ⊤ (zpowers b))) (v : Fin (2 * 2 + ε) → K),
      ρ k v =
        ((k : GL (Fin (2 * 2 + ε)) K) :
          Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v := by
    intro k v
    exact kOfAct_apply (b := b) k v
  have hLstabρ : ∀ k, ∀ v ∈ L, ρ k v ∈ L := by
    intro k v hv
    rw [hρ]
    exact hLstab k v hv
  have hdim : Module.finrank K L ≤
      Module.finrank K (⊥ : Submodule K (Fin (2 * 2 + ε) → K)) + 1 := by
    simpa only [finrank_bot, zero_add] using hL
  have h := CFSG.RankThree.PartOne.K133.perfect_trivial_on_section
    ρ hperf (W' := (⊥ : Submodule K (Fin (2 * 2 + ε) → K)))
    (W := L) bot_le hdim hLstabρ (fun k w hw => by
      rw [Submodule.mem_bot] at hw ⊢
      rw [hw]
      simp)
  intro k v hv
  have h' := h k v hv
  rw [Submodule.mem_bot, sub_eq_zero] at h'
  rw [← hρ]
  exact h'

omit [CharP K 2] in
private theorem kOfAct_fix_W_of_fix_line
    (hS : RadSetup ε b ω) (hperf : Group.IsPerfect ↥(F08.KOf8103 ⊤ (zpowers b)))
    {L : Submodule K (Fin (2 * 2 + ε) → K)} (hLW : L ≤ eigSU b ω)
    (hL : Module.finrank K L = 1)
    (hfixL : ∀ k : ↥(F08.KOf8103 ⊤ (zpowers b)), ∀ v ∈ L,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v = v) :
    ∀ k : ↥(F08.KOf8103 ⊤ (zpowers b)), ∀ w ∈ eigSU b ω,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w = w := by
  let ρ : ↥(F08.KOf8103 ⊤ (zpowers b)) →*
      Module.End K (Fin (2 * 2 + ε) → K) := kOfAct (b := b)
  have hρ : ∀ (k : ↥(F08.KOf8103 ⊤ (zpowers b))) (v : Fin (2 * 2 + ε) → K),
      ρ k v =
        ((k : GL (Fin (2 * 2 + ε)) K) :
          Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v := by
    intro k v
    exact kOfAct_apply (b := b) k v
  have hWstab : ∀ k, ∀ w ∈ eigSU b ω, ρ k w ∈ eigSU b ω := by
    intro k w hw
    have hk := kOf_le_stabSU_eigSU b ω k.2
    have h := (mem_stabSU.mp hk) w hw
    rw [hρ]
    exact h
  have hLstabρ : ∀ k, ∀ v ∈ L, ρ k v ∈ L := by
    intro k v hv
    rw [hρ, hfixL k v hv]
    exact hv
  have hfixLρ : ∀ k, ∀ v ∈ L, ρ k v = v := by
    intro k v hv
    rw [hρ, hfixL k v hv]
  have hdim : Module.finrank K (eigSU b ω) ≤ Module.finrank K L + 1 := by
    rw [hS.finrank_eig, hL]
  have hmodL : ∀ k, ∀ w ∈ eigSU b ω, ρ k w - w ∈ L :=
    CFSG.RankThree.PartOne.K133.perfect_trivial_on_section
      ρ hperf hLW hdim hWstab hLstabρ
  have hcomm : ∀ a b' : ↥(F08.KOf8103 ⊤ (zpowers b)), ∀ w ∈ eigSU b ω,
      ρ a (ρ b' w) = ρ b' (ρ a w) := by
    intro a b' w hw
    have ha := hmodL a w hw
    have hb := hmodL b' w hw
    have h1 : ρ a (ρ b' w) = ρ a w + (ρ b' w - w) := by
      calc
        ρ a (ρ b' w) = ρ a (w + (ρ b' w - w)) := by rw [add_sub_cancel]
        _ = ρ a w + ρ a (ρ b' w - w) := by rw [map_add]
        _ = ρ a w + (ρ b' w - w) := by rw [hfixLρ a _ hb]
    have h2 : ρ b' (ρ a w) = ρ b' w + (ρ a w - w) := by
      calc
        ρ b' (ρ a w) = ρ b' (w + (ρ a w - w)) := by rw [add_sub_cancel]
        _ = ρ b' w + ρ b' (ρ a w - w) := by rw [map_add]
        _ = ρ b' w + (ρ a w - w) := by rw [hfixLρ b' _ ha]
    rw [h1, h2]
    abel
  have h := CFSG.RankThree.PartOne.K133.perfect_trivial_of_commute_on
    ρ hperf (eigSU b ω) hWstab hcomm
  intro k w hw
  rw [← hρ]
  exact h k w hw

private theorem kOfAct_fix_W'_of_fix_W
    (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    (hfixW : ∀ k : ↥(F08.KOf8103 ⊤ (zpowers b)), ∀ w ∈ eigSU b ω,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w = w) :
    ∀ k : ↥(F08.KOf8103 ⊤ (zpowers b)), ∀ w' ∈ eigSU b ω⁻¹,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w' = w' := by
  intro k w' hw'
  have hW'stab : ∀ k : ↥(F08.KOf8103 ⊤ (zpowers b)), ∀ w' ∈ eigSU b ω⁻¹,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w' ∈ eigSU b ω⁻¹ := by
    intro k w' hw'
    have hk := kOf_le_stabSU_eigSU b ω⁻¹ k.2
    have h := (mem_stabSU.mp hk) w' hw'
    simpa using h
  have hz : ((k : GL (Fin (2 * 2 + ε)) K) :
      Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w' - w' ∈ eigSU b ω⁻¹ :=
    Submodule.sub_mem _ (hW'stab k w' hw') hw'
  have horth : ∀ w ∈ eigSU b ω,
      stdHermForm h (2 * 2 + ε) w
        (((k : GL (Fin (2 * 2 + ε)) K) :
          Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w' - w') = 0 := by
    intro w hw
    have hiso := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff_isometry h).mp
      (k : StatedSU (2 * 2 + ε) (2 ^ f) K).2
    have h1 := hiso.2
      ((((k⁻¹ : ↥(F08.KOf8103 ⊤ (zpowers b))) : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w) w'
    rw [hfixW k⁻¹ w hw, hfixW k w hw] at h1
    rw [map_sub, h1, sub_self]
  have hzero := hS.eq_zero_of_orth h hz horth
  rw [sub_eq_zero] at hzero
  exact hzero

omit [Finite K] in
private theorem kOfAct_eq_bot_of_fixes
    (hS : RadSetup ε b ω)
    (hfixW : ∀ k : ↥(F08.KOf8103 ⊤ (zpowers b)), ∀ w ∈ eigSU b ω,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w = w)
    (hfixW' : ∀ k : ↥(F08.KOf8103 ⊤ (zpowers b)), ∀ w' ∈ eigSU b ω⁻¹,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w' = w')
    (hfixV1 : ∀ k : ↥(F08.KOf8103 ⊤ (zpowers b)), ∀ v ∈ eigSU b 1,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v = v) :
    F08.KOf8103 ⊤ (zpowers b) = ⊥ := by
  let K0 := F08.KOf8103 ⊤ (zpowers b)
  have hfixAll : ∀ k : ↥K0, ∀ x : Fin (2 * 2 + ε) → K,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ x = x := by
    intro k x
    have hU : ∀ u ∈ (⊤ : Submodule K (Fin (2 * 2 + ε) → K)),
        ((b : GL (Fin (2 * 2 + ε)) K) :
          Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ u ∈
            (⊤ : Submodule K (Fin (2 * 2 + ε) → K)) := by
      intro u _
      exact Submodule.mem_top
    obtain ⟨v1, hv1, w, hw, w', hw', rfl⟩ :=
      hS.decomp (U := ⊤) hU x (by simp : x ∈ (⊤ : Submodule K (Fin (2 * 2 + ε) → K)))
    simp only [inf_top_eq] at hv1 hw hw'
    simp only [Matrix.mulVec_add, hfixV1 k v1 hv1, hfixW k w hw, hfixW' k w' hw']
  have hbot : K0 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    let k' : ↥K0 := ⟨k, hk⟩
    have hmat : ((k' : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) = 1 := by
      apply Matrix.ext_of_mulVec_single
      intro j
      rw [Matrix.one_mulVec]
      exact hfixAll k' (Pi.single j 1)
    have hGL : ((k' : StatedSU (2 * 2 + ε) (2 ^ f) K) :
        GL (Fin (2 * 2 + ε)) K) = 1 := Units.ext hmat
    exact Subtype.ext hGL
  change K0 = ⊥
  exact hbot

theorem RadSetup.kOf_moves_line (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    (hK₀ : F08.KOf8103 ⊤ (zpowers b) ≠ ⊥) {L : Submodule K (Fin (2 * 2 + ε) → K)}
    (hLW : L ≤ eigSU b ω) (hL : Module.finrank K L = 1) :
    ∃ k ∈ F08.KOf8103 ⊤ (zpowers b), ∃ v ∈ L,
      ((k : GL (Fin (2 * 2 + ε)) K) : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v ∉ L := by
  by_contra hcon
  let K0 := F08.KOf8103 ⊤ (zpowers b)
  have hperf : Group.IsPerfect ↥K0 := kOfAct_perfect (b := b)
  have hstab : ∀ k : ↥K0, ∀ v ∈ L,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v ∈ L := by
    intro k v hv
    by_contra hmem
    exact hcon ⟨(k : StatedSU (2 * 2 + ε) (2 ^ f) K), k.2, v, hv, hmem⟩
  have hfixL : ∀ k : ↥K0, ∀ v ∈ L,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v = v :=
    kOfAct_fix_of_finrank_le_one (b := b) hperf (by rw [hL]) hstab
  have hfixW : ∀ k : ↥K0, ∀ w ∈ eigSU b ω,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w = w :=
    kOfAct_fix_W_of_fix_line (b := b) hS hperf hLW hL hfixL
  have hfixW' : ∀ k : ↥K0, ∀ w' ∈ eigSU b ω⁻¹,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w' = w' :=
    kOfAct_fix_W'_of_fix_W (b := b) hS h hfixW
  have hV1stab : ∀ k : ↥K0, ∀ v ∈ eigSU b 1,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v ∈ eigSU b 1 := by
    intro k v hv
    have hk := kOf_le_stabSU_eigSU b 1 k.2
    have h := (mem_stabSU.mp hk) v hv
    simpa using h
  have hfixV1 : ∀ k : ↥K0, ∀ v ∈ eigSU b 1,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v = v :=
    kOfAct_fix_of_finrank_le_one (b := b) hperf hS.finrank_eig_one_le hV1stab
  exact hK₀ (kOfAct_eq_bot_of_fixes (b := b) hS hfixW hfixW' hfixV1)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
