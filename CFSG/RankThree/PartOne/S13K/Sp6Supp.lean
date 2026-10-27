module

public import CFSG.RankThree.PartOne.S13K.Sp6Conj

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne.KFQ

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def FixCoord (g : AutV K) (j : Fin 3) : Prop := ∀ a : Qext K, g (sg j a) = sg j a

theorem apply_sg_eq_zero_of_fix {g : AutV K} (hg : g ∈ M10 K) {j k : Fin 3} (hjk : j ≠ k)
    (hk : FixCoord g k) (a : Qext K) : g (sg j a) k = 0 := by
  apply eq_zero_of_forall_qForm
  intro b
  have h1 := formQ_map hg (sg j a) (sg k b)
  rw [hk b, formQ_sg_right, formQ_sg_right] at h1
  rw [h1]
  simp [Pi.single_eq_of_ne hjk.symm]

theorem apply_eq_self_of_supp {h : AutV K} {w : QV K (Fin 3)} (hw : ∀ k, w k ≠ 0 → FixCoord h k) :
    h w = w := by
  have hv := sg_add_sg_add_sg w
  have hk : ∀ k : Fin 3, h (sg k (w k)) = sg k (w k) := by
    intro k
    by_cases h0 : w k = 0
    · rw [h0]
      simp
    · exact hw k h0 (w k)
  calc h w = h (sg 0 (w 0) + sg 1 (w 1) + sg 2 (w 2)) := by rw [hv]
    _ = sg 0 (w 0) + sg 1 (w 1) + sg 2 (w 2) := by simp only [map_add, hk]
    _ = w := hv

theorem comm_aux {g h : AutV K} (hg : g ∈ M10 K) {Jg Jh : Set (Fin 3)}
    (hdisj : ∀ j, j ∈ Jg → j ∉ Jh) (hgJ : ∀ j, j ∉ Jg → FixCoord g j)
    (hhJ : ∀ j, j ∉ Jh → FixCoord h j) {j : Fin 3} (hj : j ∈ Jg) (a : Qext K) :
    g (h (sg j a)) = h (g (sg j a)) := by
  have hh1 : h (sg j a) = sg j a := hhJ j (hdisj j hj) a
  rw [hh1]
  symm
  refine apply_eq_self_of_supp fun k hk => hhJ k (hdisj k ?_)
  by_contra hkJ
  exact hk (apply_sg_eq_zero_of_fix hg (by rintro rfl; exact hkJ hj) (hgJ k hkJ) a)

theorem comm_of_disjoint_supp {g h : AutV K} (hg : g ∈ M10 K) (hh : h ∈ M10 K) {Jg Jh : Set (Fin 3)}
    (hdisj : ∀ j, j ∈ Jg → j ∉ Jh) (hgJ : ∀ j, j ∉ Jg → FixCoord g j)
    (hhJ : ∀ j, j ∉ Jh → FixCoord h j) : g * h = h * g := by
  have key : ∀ j a, g (h (sg j a)) = h (g (sg j a)) := by
    intro j a
    by_cases hjg : j ∈ Jg
    · exact comm_aux hg hdisj hgJ hhJ hjg a
    · by_cases hjh : j ∈ Jh
      · exact (comm_aux hh (fun k hk hkg => hdisj k hkg hk) hhJ hgJ hjh a).symm
      · rw [hhJ j hjh a, hgJ j hjg a, hhJ j hjh a]
  exact autV_ext_sg (fun a => key 0 a) (fun a => key 1 a) (fun a => key 2 a)

theorem commute_of_disjoint_supp {g h : ↥(M10 K)} {Jg Jh : Set (Fin 3)}
    (hdisj : ∀ j, j ∈ Jg → j ∉ Jh) (hgJ : ∀ j, j ∉ Jg → FixCoord g.1 j)
    (hhJ : ∀ j, j ∉ Jh → FixCoord h.1 j) : g * h = h * g :=
  Subtype.ext (comm_of_disjoint_supp g.2 h.2 hdisj hgJ hhJ)

theorem sgnPerm_sg (σ : Equiv.Perm (Fin 3)) (τ : Fin 3 → Bool) (j : Fin 3) (a : Qext K) :
    sgnPerm σ τ (sg j a) = sg (σ j) (if τ j then frobQ K a else a) := by
  funext i
  rw [sgnPerm_apply]
  by_cases h : i = σ j
  · subst h
    simp
  · have hi : σ.symm i ≠ j := fun hij => h (by rw [← hij]; simp)
    simp [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne h]

theorem fixCoord_conj {g : ↥(M10 K)} {σ : Equiv.Perm (Fin 3)} {τ : Fin 3 → Bool} {j : Fin 3}
    (hg : FixCoord g.1 j) : FixCoord ((sg10 σ τ * g * (sg10 σ τ)⁻¹ : ↥(M10 K)).1) (σ j) := by
  intro a
  set m : ↥(M10 K) := sg10 σ τ with hm
  have hmj : ∀ b : Qext K, m.1 (sg j b) = sg (σ j) (if τ j then frobQ K b else b) := fun b =>
    sgnPerm_sg σ τ j b
  set b : Qext K := if τ j then frobQ K a else a with hb
  have hmb : m.1 (sg j b) = sg (σ j) a := by
    rw [hmj]
    congr 1
    by_cases h : τ j
    · simp [hb, h, frobQ_frobQ]
    · simp [hb, h]
  change m.1 (g.1 ((m⁻¹ : ↥(M10 K)).1 (sg (σ j) a))) = sg (σ j) a
  have hinv : (m⁻¹ : ↥(M10 K)).1 (sg (σ j) a) = sg j b := by
    change m.1.symm (sg (σ j) a) = sg j b
    rw [LinearEquiv.symm_apply_eq, hmb]
  rw [hinv, hg b, hmb]

end CFSG.RankThree.PartOne.S13K
