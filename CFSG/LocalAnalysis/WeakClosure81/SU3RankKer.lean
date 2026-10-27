module

public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

theorem mem_statedScalars_of_map_eq_one {n : ℕ} {F₀ : Type} [Field F₀] [Finite F₀]
    (hn : 2 ≤ n) (hcard : Nat.card F₀ = (2 ^ n) ^ 2) {X : Type} [Group X]
    (σ : ↥(StatedSU 3 (2 ^ n) F₀) →* X) (hσ : σ ≠ 1) {x : ↥(StatedSU 3 (2 ^ n) F₀)}
    (hx : σ x = 1) : (x : GL (Fin 3) F₀) ∈ StatedScalars (Fin 3) F₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2n : 2 ^ n ≠ 2 := by
    intro h
    have h4 : 4 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn
    omega
  have hnq : (3, 2 ^ n) ≠ (3, 2) := fun h => h2n (congrArg Prod.snd h)
  haveI : Group.IsPerfect ↥(StatedSU 3 (2 ^ n) F₀) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcard le_rfl hnq
  let Z : Subgroup ↥(StatedSU 3 (2 ^ n) F₀) :=
    (StatedScalars (Fin 3) F₀).subgroupOf (StatedSU 3 (2 ^ n) F₀)
  haveI hZnormal : Z.Normal :=
    Subgroup.Normal.subgroupOf (StatedScalars.normal (Fin 3) F₀) (StatedSU 3 (2 ^ n) F₀)
  let N : Subgroup ↥(StatedSU 3 (2 ^ n) F₀) := σ.ker
  haveI hNnormal : N.Normal := MonoidHom.normal_ker σ
  let q : ↥(StatedSU 3 (2 ^ n) F₀) →* (↥(StatedSU 3 (2 ^ n) F₀) ⧸ Z) :=
    QuotientGroup.mk' Z
  haveI : IsSimpleGroup (↥(StatedSU 3 (2 ^ n) F₀) ⧸ Z) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F₀ 2 n hcard 3 le_rfl hnq
  let M : Subgroup (↥(StatedSU 3 (2 ^ n) F₀) ⧸ Z) := N.map q
  have hqker : q.ker = Z := QuotientGroup.ker_mk' Z
  have hZcenter : Z ≤ Subgroup.center ↥(StatedSU 3 (2 ^ n) F₀) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hz' : (z : GL (Fin 3) F₀) ∈ Subgroup.center (GL (Fin 3) F₀) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact Subgroup.mem_subgroupOf.mp hz
    simpa using Subgroup.mem_center_iff.mp hz' (g : GL (Fin 3) F₀)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hMbot | hMtop
  · have hNZ : N ≤ Z := by
      have h : N.map q = ⊥ := hMbot
      have h' : N ≤ q.ker := (Subgroup.map_eq_bot_iff (H := N) (f := q)).mp h
      rwa [hqker] at h'
    have hxN : x ∈ N := MonoidHom.mem_ker.mpr hx
    exact Subgroup.mem_subgroupOf.mp (hNZ hxN)
  · exfalso
    have hNZ : N ⊔ Z = ⊤ := by
      have h : N.map q = ⊤ := hMtop
      rw [← hqker, ← Subgroup.comap_map_eq (f := q) N, h, Subgroup.comap_top]
    have hcomm : ⁅(⊤ : Subgroup ↥(StatedSU 3 (2 ^ n) F₀)), ⊤⁆ ≤ N := by
      have htop : ⁅(⊤ : Subgroup ↥(StatedSU 3 (2 ^ n) F₀)), ⊤⁆ =
          ⁅N ⊔ Z, (⊤ : Subgroup ↥(StatedSU 3 (2 ^ n) F₀))⁆ := by
        rw [hNZ]
      rw [htop, Subgroup.commutator_sup_right]
      apply sup_le
      · exact Subgroup.commutator_le_left N ⊤
      · have hbot : ⁅Z, (⊤ : Subgroup ↥(StatedSU 3 (2 ^ n) F₀))⁆ = ⊥ := by
          rw [Subgroup.commutator_comm]
          exact (Subgroup.commutator_top_left_eq_bot_iff_le_center (H := Z)).mpr hZcenter
        exact hbot.le.trans bot_le
    have hcommtop : ⁅(⊤ : Subgroup ↥(StatedSU 3 (2 ^ n) F₀)),
        (⊤ : Subgroup ↥(StatedSU 3 (2 ^ n) F₀))⁆ = ⊤ := by
      simpa only [commutator_def] using
        (Group.IsPerfect.commutator_eq_top (G := ↥(StatedSU 3 (2 ^ n) F₀)))
    have hNtop : N = ⊤ := le_antisymm le_top (hcommtop ▸ hcomm)
    exact hσ (MonoidHom.ext fun g => by
      have hg : g ∈ N := hNtop.symm ▸ Subgroup.mem_top g
      exact MonoidHom.mem_ker.mp hg)

end CFSG.LocalAnalysis.WeakClosure81

end
