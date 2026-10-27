module

public import CFSG.RankThree.GF2n.Stroth80.Sec311Conj
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec7Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec710_lemma61 (h56 : Stroth56NatStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hnom : ¬ OmegaMinusNat hc t 2) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZL : Z0 ≤ LB M Q B)
    (hH : ∀ g ∈ M, conjSubgroup g Z0 ≤ LB M Q B → conjSubgroup g Z0 = Z0) {g r : G}
    (hg : g ∈ M) (hr : r ∈ Rt M (LB M Q B) t)
    (hle : conjSubgroup r B ⊔ Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t)) :
    conjSubgroup g Z0 = Z0 := by
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hgi : g⁻¹ ∈ M := M.inv_mem hg
  have hZg : conjSubgroup g⁻¹ Z = Z := hc.conj_Z_eq hgi
  have hgg : ∀ T : Subgroup G, conjSubgroup g⁻¹ (conjSubgroup g T) = T := fun T => by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hcs : ∀ (a : G) (S T : Subgroup G),
      conjSubgroup a (S ⊔ T) = conjSubgroup a S ⊔ conjSubgroup a T :=
    fun a S T => Subgroup.map_sup _ _ _
  have hm : g⁻¹ * r ∈ M := M.mul_mem hgi hrM
  have h1 : conjSubgroup (g⁻¹ * r) B ⊔ Z ≤ Vt M (LB M Q B) B Z t := by
    have h' : conjSubgroup g⁻¹ (conjSubgroup r B ⊔ Z) ≤
        conjSubgroup g⁻¹ (conjSubgroup g (Vt M (LB M Q B) B Z t)) := Subgroup.map_mono hle
    rw [hcs, hZg, hgg, ← conjSubgroup_mul] at h'
    exact h'
  obtain ⟨r₀, hr₀, hr₀eq⟩ := h56 G M Q Z B hc n t hs hnom (g⁻¹ * r) hm h1
  have hr₀M : r₀ ∈ M := hc.Rt_le_M t hr₀
  have h3 : conjSubgroup r B ⊔ Z = conjSubgroup (g * r₀) B ⊔ Z := by
    have h' := congrArg (conjSubgroup g) hr₀eq
    rw [hcs, hcs, hc.conj_Z_eq hg, ← conjSubgroup_mul, ← conjSubgroup_mul] at h'
    simpa [mul_assoc] using h'
  have h4 : conjSubgroup r (LB M Q B) = conjSubgroup (g * r₀) (LB M Q B) :=
    hc.conj_LB_eq_of_conj_BZ hrM (M.mul_mem hg hr₀M) h3
  have hnormQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hr₀Z : conjSubgroup r₀ Z0 = Z0 :=
    conjSubgroup_eq_self_iff.mpr (hZ0.mem_normalizer hnormQ hr₀)
  have hrZ : conjSubgroup r Z0 = Z0 :=
    conjSubgroup_eq_self_iff.mpr (hZ0.mem_normalizer hnormQ hr)
  have h5 : conjSubgroup g Z0 ≤ conjSubgroup r (LB M Q B) := by
    rw [h4, conjSubgroup_mul]
    calc conjSubgroup g Z0 = conjSubgroup g (conjSubgroup r₀ Z0) := by rw [hr₀Z]
      _ ≤ conjSubgroup g (conjSubgroup r₀ (LB M Q B)) := Subgroup.map_mono (Subgroup.map_mono hZL)
  have h6 : conjSubgroup (r⁻¹ * g) Z0 ≤ LB M Q B := by
    rw [conjSubgroup_mul]
    calc conjSubgroup r⁻¹ (conjSubgroup g Z0)
        ≤ conjSubgroup r⁻¹ (conjSubgroup r (LB M Q B)) := Subgroup.map_mono h5
      _ = LB M Q B := by rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have h7 := hH (r⁻¹ * g) (M.mul_mem (M.inv_mem hrM) hg) h6
  calc conjSubgroup g Z0 = conjSubgroup r (conjSubgroup (r⁻¹ * g) Z0) := by
        rw [← conjSubgroup_mul, mul_inv_cancel_left]
    _ = conjSubgroup r Z0 := by rw [h7]
    _ = Z0 := hrZ

end CFSG.RankThree.GF2n.Stroth80
