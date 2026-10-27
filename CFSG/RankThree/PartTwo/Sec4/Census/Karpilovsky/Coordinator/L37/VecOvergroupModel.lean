module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.VecOvergroup
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelToJ
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.PerfectSupCenter
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.VecBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple CFSG.Sporadic.ON
open CFSG.Sporadic.ON.Native (nPts)
open scoped Pointwise commutatorElement

section General

variable {G X : Type*} [Group G] [MulAction G X]

theorem conj_mem_stabilizer_of_mem_pair {w w' : X} {h g : G}
    (hh : h ∈ MulAction.stabilizer G ({w, w'} : Set X)) (hg : g ∈ MulAction.stabilizer G w)
    (hg' : g ∈ MulAction.stabilizer G ({w, w'} : Set X)) :
    h * g * h⁻¹ ∈ MulAction.stabilizer G w := by
  have hgw : g • w = w := hg
  have hgw' : g • w' = w' := by
    rcases smul_pair_cases (MulAction.mem_stabilizer_iff.1 hg') with ⟨_, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · have hww : w = w' := hgw.symm.trans h1
      rw [← hww]
      exact hgw
  have hhi : (h⁻¹ • w = w) ∨ (h⁻¹ • w = w') := by
    rcases smul_pair_cases (MulAction.mem_stabilizer_iff.1 (Subgroup.inv_mem _ hh)) with
      ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul]
  rcases hhi with h1 | h1
  · rw [h1, hgw]
    exact (inv_smul_eq_iff.1 h1).symm
  · rw [h1, hgw']
    exact (inv_smul_eq_iff.1 h1).symm

theorem commutatorElement_mul_central {a b c d : G}
    (hc : ∀ g : G, g * c = c * g) (hd : ∀ g : G, g * d = d * g) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hcY : ∀ Y : G, c * Y * c⁻¹ = Y := fun Y => by rw [← hc Y, mul_inv_cancel_right]
  have hdY : ∀ Y : G, d * Y * d⁻¹ = Y := fun Y => by rw [← hd Y, mul_inv_cancel_right]
  calc ⁅a * c, b * d⁆ = a * (c * (b * d) * c⁻¹) * a⁻¹ * (b * d)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * (b * d) * a⁻¹ * (b * d)⁻¹ := by rw [hcY]
    _ = a * b * (d * a⁻¹ * d⁻¹) * b⁻¹ := by group
    _ = ⁅a, b⁆ := by rw [hdY, commutatorElement_def]

end General


theorem le_normalizer_or_eq_top_of_vec {T Y : Subgroup GM} [Group.IsPerfect T] {w : Fin nPts}
    (hTw : ∀ t ∈ T, phiJ t • w = w) (hcard : Nat.card (T.map phiJ) = 1876896)
    (hTY : T ≤ Y) : Y ≤ Subgroup.normalizer (T : Set GM) ∨ Y = ⊤ := by
  have hker : phiJ.ker ≤ Subgroup.center GM := (ker_phiJ_eq_center).le
  have hTeq : T.map phiJ = MulAction.stabilizer J w := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨t, ht, rfl⟩
      exact hTw t ht
    · rw [card_stabilizer_vec, hcard]
  have hYle : MulAction.stabilizer J w ≤ Y.map phiJ := hTeq ▸ Subgroup.map_mono hTY
  have key : ∀ y : GM, (∀ g ∈ MulAction.stabilizer J w,
      phiJ y * g * (phiJ y)⁻¹ ∈ MulAction.stabilizer J w) →
      y ∈ Subgroup.normalizer (T : Set GM) := by
    intro y hy
    set Tc := T.map (MulAut.conj y).toMonoidHom with hTc
    have hle : Tc ≤ T ⊔ phiJ.ker := by
      rintro _ ⟨t, ht, rfl⟩
      have hmem : phiJ (y * t * y⁻¹) ∈ T.map phiJ := by
        rw [hTeq, map_mul, map_mul, map_inv]
        exact hy _ (hTw t ht)
      obtain ⟨t', ht', heq⟩ := hmem
      have hk : t'⁻¹ * (y * t * y⁻¹) ∈ phiJ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
      have : (MulAut.conj y).toMonoidHom t = t' * (t'⁻¹ * (y * t * y⁻¹)) := by
        simp [MulAut.conj_apply]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht') (Subgroup.mem_sup_right hk)
    have hperf : Group.IsPerfect Tc := Group.IsPerfect.map (MulAut.conj y).toMonoidHom
    have h1 : Tc ≤ T := Proving.le_of_isPerfect_of_le_sup_center inferInstance hker hperf hle
    have h2 : Tc = T := Subgroup.eq_of_le_of_card_ge h1
      (by rw [hTc, Subgroup.card_map_of_injective (MulAut.conj y).injective])
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      rw [← h2]
      exact ⟨t, ht, rfl⟩
    · intro ht
      rw [← h2] at ht
      obtain ⟨t', ht', heq⟩ := ht
      have : t' = t := by
        simpa [MulAut.conj_apply] using heq
      rw [← this]
      exact ht'
  obtain ⟨w', h | h | h⟩ :=
    stabilizer_le_cases_of_base (fun _ hK => stabilizer_root_le_cases hK) w hYle
  · left
    intro y hy
    apply key y
    intro g hg
    have hyw : phiJ y ∈ MulAction.stabilizer J w := by rw [← h]; exact ⟨y, hy, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyw hg) (Subgroup.inv_mem _ hyw)
  · left
    intro y hy
    apply key y
    intro g hg
    have hyw : phiJ y ∈ MulAction.stabilizer J ({w, w'} : Set (Fin nPts)) := by
      rw [← h]; exact ⟨y, hy, rfl⟩
    have hg' : g ∈ MulAction.stabilizer J ({w, w'} : Set (Fin nPts)) := by
      rw [← h]; exact hYle hg
    exact conj_mem_stabilizer_of_mem_pair hyw hg hg'
  · right
    have hdec : ∀ x : GM, ∃ y ∈ Y, ∃ n : ℤ, x = y * zG ^ n := by
      intro x
      have : phiJ x ∈ Y.map phiJ := by rw [h]; trivial
      obtain ⟨y, hy, hyx⟩ := this
      have hk : y⁻¹ * x ∈ phiJ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      rw [ker_phiJ, Subgroup.mem_zpowers_iff] at hk
      obtain ⟨n, hn⟩ := hk
      exact ⟨y, hy, n, by rw [hn]; group⟩
    have hzcen : zG ∈ Subgroup.center GM := by
      rw [← ker_phiJ_eq_center, ker_phiJ]
      exact Subgroup.mem_zpowers zG
    have hzc : ∀ n : ℤ, ∀ g : GM, g * zG ^ n = zG ^ n * g := fun n g =>
      Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ hzcen n) g
    have hzY : zG ∈ Y := by
      obtain ⟨y₁, hy₁, n₁, h₁⟩ := hdec (xG 0)
      obtain ⟨y₂, hy₂, n₂, h₂⟩ := hdec (xG 3)
      rw [← comm_x0_x3, h₁, h₂, commutatorElement_mul_central (hzc n₁) (hzc n₂),
        commutatorElement_def]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy₁ hy₂) (Y.inv_mem hy₁)) (Y.inv_mem hy₂)
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, n, rfl⟩ := hdec x
    exact Y.mul_mem hy (Y.zpow_mem hzY n)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
