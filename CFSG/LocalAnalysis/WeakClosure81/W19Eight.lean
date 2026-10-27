module

public import CFSG.LocalAnalysis.WeakClosure81.W19EightEx
public import CFSG.LocalAnalysis.WeakClosure81.W19EightAux
public import CFSG.LocalAnalysis.WeakClosure81.W19EightTrans
public import CFSG.LocalAnalysis.WeakClosure81.W19EightTwo
public import CFSG.LocalAnalysis.WeakClosure81.W19EightOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem mem_gammaSet_one_of_index (c : MinCex193 D V₀ V p X) {g : G} {B : Subgroup G}
    (hBA : B ≤ conjSubgroup V g) (hidx : (B.subgroupOf (conjSubgroup V g)).index = 2) :
    B ∈ E3.gammaSet V 1 (conjSubgroup V g) := by
  refine (c.mem_gammaSet_one_iff).2 ⟨hBA, ?_⟩
  have hA2 : IsPGroup 2 (conjSubgroup V g) := E3.isPGroup_conjSubgroup c.isPGroup_V g
  have h1 := E3.relIndex_eq_two_pow hA2 B
  have h2 : B.relIndex (conjSubgroup V g) = 2 := hidx
  rw [h2] at h1
  exact Nat.pow_right_injective (le_refl 2) (h1.symm.trans (pow_one 2).symm)

theorem exists_card_commEB (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h4 : ∀ (g : G) (K : Subgroup G), Conf196 D V X g K →
      Nat.card ↥(X ⊓ J193 D X (conjSubgroup V g) K) = p)
    {E F : Subgroup G} {g : G} (h : Hyp197 D V X E F g) :
    ∃ B ∈ E3.gammaSet V 1 (conjSubgroup V g), 2 < Nat.card ↥(commEB E F B) := by
  by_contra hcon
  have hle : ∀ B ∈ E3.gammaSet V 1 (conjSubgroup V g), Nat.card ↥(commEB E F B) ≤ 2 :=
    fun B hB => not_lt.1 fun h' => hcon ⟨B, hB, h'⟩
  have hAel : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup c.setting.isElemAbelian g
  have hA2 : IsPGroup 2 (conjSubgroup V g) := E3.isPGroup_conjSubgroup c.isPGroup_V g
  have hs1 : ∀ B ∈ E3.gammaSet V 1 (conjSubgroup V g),
      ⁅conjSubgroup V g, eB E F B⁆ ≤ conjSubgroup V₀ g := fun B hB =>
    c.comm_le_V₀_of_card_le_two h162 h.isElemAbelian h.A_le_normalizer_E hB (hle B hB)
  have hs2 : ∀ B ∈ E3.gammaSet V 1 (conjSubgroup V g), eB E F B ≠ E := fun B hB hBE =>
    c.false_of_eB_eq h162 h4 h hB hBE (hs1 B hB)
  have hidx : 4 ≤ ((conjSubgroup V g ⊓ centralizerQuot (X ⊔ D.T) E F).subgroupOf
      (conjSubgroup V g)).index := by
    by_contra hlt
    obtain ⟨m, hm⟩ : ∃ m, (conjSubgroup V g ⊓ centralizerQuot (X ⊔ D.T) E F).relIndex
        (conjSubgroup V g) = 2 ^ m := ⟨_, E3.relIndex_eq_two_pow hA2 _⟩
    have hm2 : m < 2 := by
      by_contra hm2
      have h5 : 4 ≤ 2 ^ m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hm2)
      have h6 : 4 ≤ (conjSubgroup V g ⊓ centralizerQuot (X ⊔ D.T) E F).relIndex
          (conjSubgroup V g) := by rw [hm]; exact h5
      exact hlt h6
    have hle2 : ((conjSubgroup V g ⊓ centralizerQuot (X ⊔ D.T) E F).subgroupOf
        (conjSubgroup V g)).index ≤ 2 := by
      have h7 : (conjSubgroup V g ⊓ centralizerQuot (X ⊔ D.T) E F).relIndex
          (conjSubgroup V g) ≤ 2 := by
        rw [hm]
        interval_cases m <;> norm_num
      exact h7
    obtain ⟨B, hB, hBE⟩ := h.exists_gamma_eB_eq c hle2
    exact hs2 B hB hBE
  obtain ⟨M⟩ := exists_modData c.hyp.isSolvable h.E_le h.isElemAbelian h.F_lt_E h.normalizer_E
    h.normalizer_F h.irreducible
  have hXH : X ≤ X ⊔ D.T := le_sup_left
  have hXn : X ⊔ D.T ≤ normalizer ((X ⊔ pCoreOf 2 (X ⊔ D.T) : Subgroup G) : Set G) :=
    c.le_normalizer_sup_pCoreOf
  have horbit : ∀ (a₁ : ↥(X ⊔ D.T)) (w : M.W), (a₁ : G) ∈ conjSubgroup V g → M.ρ a₁ w ≠ w →
      (∀ b : ↥(X ⊔ D.T), (b : G) ∈ conjSubgroup V g → M.ρ b w = w ∨ M.ρ b w = M.ρ a₁ w) →
      ∃ e ∈ E, M.ι e = w ∧ ⁅(a₁ : G), e⁆ ∈ conjSubgroup V₀ g ∧ ⁅(a₁ : G), e⁆ ≠ 1 ∧
        ⁅(a₁ : G), e⁆ ∈ E := by
    intro a₁ w ha₁A hmv horb
    obtain ⟨B, hBA, hBidx, hBw⟩ := M.exists_hyperplane_of_two_orbit h.A_le_H hAel ha₁A hmv horb
    have hB : B ∈ E3.gammaSet V 1 (conjSubgroup V g) := c.mem_gammaSet_one_of_index hBA hBidx
    obtain ⟨e, he, hιe⟩ := M.ι_surj w
    have heB : e ∈ eB E F B := mem_eB_of he fun b hb => by
      have hbH : b ∈ X ⊔ D.T := h.A_le_H (hBA hb)
      have hfix : M.ρ ⟨b, hbH⟩ (M.ι e) = M.ι e := by
        rw [hιe]
        exact hBw ⟨b, hbH⟩ hb
      have hmem := (M.ρ_ι_eq_iff h.normalizer_E ⟨b, hbH⟩ he).1 hfix
      rw [← commutatorElement_inv]
      exact F.inv_mem hmem
    have hc1V : ⁅(a₁ : G), e⁆ ∈ conjSubgroup V₀ g :=
      hs1 B hB (Subgroup.commutator_mem_commutator ha₁A heB)
    refine ⟨e, he, hιe, hc1V, ?_, commutator_mem_of_le_normalizer h.normalizer_E a₁.2 he⟩
    intro hc1
    apply hmv
    have h1 := M.ρ_sub_ι h.normalizer_E a₁ he
    rw [hc1, (M.ι_eq_zero 1 E.one_mem).2 F.one_mem, hιe] at h1
    exact sub_eq_zero.1 h1
  obtain ⟨a₁, w, ha₁A, hmv, horb⟩ := M.exists_two_orbit_of_comm_ne h.A_le_H hXH hAel
    c.odd_card_X hXn hidx (h.not_comm_le_centralizerQuot c)
  obtain ⟨e, he, hιe, hc1V, hc1ne, hc1E⟩ := horbit a₁ w ha₁A hmv horb
  have hne : E ⊓ conjSubgroup V₀ g ≠ ⊥ := by
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨⁅(a₁ : G), e⁆, hc1E, hc1V⟩, fun h1 => ?_⟩
    exact hc1ne (congrArg Subtype.val h1)
  have hq := h.quadratic c hne
  have hquadM := M.quadratic_module (A := conjSubgroup V g) h.normalizer_E hq.2.2
  obtain ⟨a₁', y, w', ha₁'A, hyX, hρy, hmv', horb', hfix'⟩ := M.exists_two_orbit_conf
    h.F_lt_E h.le_T le_sup_right hXH rfl c.hyp.isSylowIn_T.isPGroup hAel c.odd_card_X hXn hidx
    hquadM
  obtain ⟨e', he', hιe', hc'V, hc'ne, hc'E⟩ := horbit a₁' w' ha₁'A hmv' horb'
  have hyfix : M.ρ y (M.ι ⁅(a₁' : G), e'⁆) = M.ι ⁅(a₁' : G), e'⁆ := by
    have h1 := hfix'
    rw [← hιe', M.ρ_sub_ι h.normalizer_E a₁' he'] at h1
    exact h1
  have hyF : ⁅(y : G), ⁅(a₁' : G), e'⁆⁆ ∈ F := (M.ρ_ι_eq_iff h.normalizer_E y hc'E).1 hyfix
  have hycomm : (y : G) * ⁅(a₁' : G), e'⁆ = ⁅(a₁' : G), e'⁆ * (y : G) :=
    h.mul_comm_of_comm_mem c hyX hc'E hyF
  have hyC : (y : G) ∈ Subgroup.centralizer ({⁅(a₁' : G), e'⁆} : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hycomm.symm
  have hyM : (y : G) ∈ conjSubgroup D.M g :=
    centralizer_le_conj_M c.setting c.ne_bot g hc'V hc'ne hyC
  have hy1 : (y : G) = 1 := by
    have h1 : (y : G) ∈ X ⊓ conjSubgroup D.M g := ⟨hyX, hyM⟩
    rw [h.X_inf_conj_M c h162, Subgroup.mem_bot] at h1
    exact h1
  exact hρy (by rw [show y = 1 from Subtype.ext hy1]; exact map_one _)

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
