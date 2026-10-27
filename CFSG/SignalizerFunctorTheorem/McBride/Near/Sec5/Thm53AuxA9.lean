module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA8

public section

open CFSG.Open
open scoped Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53A

section Def

variable {G : Type u} [Group G]

@[expose] def WB (W B : Subgroup G) : Subgroup G :=
  ⨆ b ∈ B, ⨆ (_ : b ≠ 1), perfRes (cenIn (kOf W) {b})

theorem perfRes_cenIn_le_WB {W B : Subgroup G} {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    perfRes (cenIn (kOf W) {b}) ≤ WB W B :=
  le_iSup₂_of_le b hb (le_iSup_of_le hb1 le_rfl)

theorem WB_le_kOf [Finite G] (W B : Subgroup G) : WB W B ≤ kOf W :=
  iSup₂_le fun _ _ => iSup_le fun _ => (perfRes_le _).trans inf_le_left

theorem WB_le_perfRes [Finite G] {W B L : Subgroup G} (h : WB W B ≤ L) : WB W B ≤ perfRes L :=
  iSup₂_le fun _ hb => iSup_le fun hb1 =>
    le_perfRes_of_isPerfect (isPerfect_perfRes _) ((perfRes_cenIn_le_WB hb hb1).trans h)

end Def

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem admits_perfRes_cenIn_kOf (hθ : NearFunctor p A θ) {W : Subgroup G}
    (hW : W ∈ mtil p A θ) {b : G} (hb : b ∈ A) :
    Admits (dsub A θ ⊔ A) (perfRes (cenIn (kOf W) {b})) :=
  admits_perfRes (Admits.inf
    (Thm41Aux.admits_kOf (sup_le (admits_dsub_of_le hW.2) hW.1.1))
    (admits_centralizer_singleton (dsub_sup_le_centralizer hθ hb)))

theorem perfRes_cenIn_kOf_eq
    (hθ : NearFunctor p A θ) {W : Subgroup G} (hW : W ∈ mtil p A θ)
    (hperf : perfRes W ≤ kOf W) {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) (hk : kOf (θ b) ≤ W) :
    perfRes (cenIn (kOf W) {b}) = perfRes (kOf (θ b)) := by
  obtain ⟨hAW, -, hWθ, hnearW⟩ := mem_assoc_iff.mp hW.1
  have hc : θ b ≤ Subgroup.centralizer {b} := hθ.isFunctor.le_centralizer b hb hb1
  have hle : kOf (θ b) ≤ cenIn W {b} := le_inf hk ((kOf_le _).trans hc)
  have heq : kOf (cenIn W {b}) = kOf (θ b) := kOf_eq_of_kOf_le (hWθ b hb hb1) hle
  have h1 : cenIn (kOf W) {b} ≤ kOf (θ b) := by
    have := cenIn_kOf_le_kOf_cenIn hθ.prime hθ.elemAbelian hAW hnearW.1 hb hb1
    rwa [heq] at this
  refine le_antisymm (perfRes_mono h1) ?_
  refine le_perfRes_of_isPerfect (isPerfect_perfRes _) (le_inf ?_ ?_)
  · exact (perfRes_mono hk).trans hperf
  · exact (perfRes_le _).trans ((kOf_le _).trans hc)

theorem perfRes_cenIn_kOf_eq_bot {W : Subgroup G} (hW : W ∈ mtil p A θ) {b : G} (hb : b ∈ A)
    (hb1 : b ≠ 1) (hs : Group.IsSolvable ↥(θ b ⊓ W)) : perfRes (cenIn (kOf W) {b}) = ⊥ := by
  refine (perfRes_eq_bot_iff _).mpr ?_
  have hle : cenIn (kOf W) {b} ≤ θ b ⊓ W := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hW.1.2.2.1 b hb hb1 ⟨(kOf_le W) hx.1, hx.2⟩, (kOf_le W) hx.1⟩
  have := hs
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem apply_le_normalizer_perfRes_cenIn
    (h : Counterexample p A θ) {W : Subgroup G}
    (hW : Setting p A θ W) (hI : ∀ Y ∈ dset p A θ, thetaMG p A θ Y ∈ assoc p A θ)
    (hin : CompInput p W) {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) :
    θ b ≤ Subgroup.normalizer (perfRes (cenIn (kOf W) {b}) : Set G) := by
  have hθ := h.hyp.nearFunctor
  by_cases hs : Group.IsSolvable ↥(θ b ⊓ W)
  · rw [perfRes_cenIn_kOf_eq_bot hW.mem_mtil hb hb1 hs]
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_bot, mul_inv_eq_one, mul_eq_left]
  · rw [perfRes_cenIn_kOf_eq hθ hW.mem_mtil (perfRes_le_kOf h hW hI hin) hb hb1
      (kOf_apply_le h hW hI hb hb1 hs)]
    exact admits_perfRes (Thm52Aux.le_normalizer_kOf (θ b))

theorem WB_mem_mhat (hθ : NearFunctor p A θ) {W : Subgroup G} (hW : W ∈ mtil p A θ)
    {B : Subgroup G} (hBA : B ≤ A) : WB W B ∈ mhat p A θ :=
  mem_mhat_of_le_mtil hθ.prime hW ((WB_le_kOf W B).trans (kOf_le W))
    (Admits.iSup fun _ => Admits.iSup fun hb => Admits.iSup fun _ =>
      admits_perfRes_cenIn_kOf hθ hW (hBA hb))

theorem WB_sup_sol (hθ : NearFunctor p A θ) {W : Subgroup G} (hW : W ∈ mtil p A θ)
    (hin : CompInput p W) {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) :
    WB W B ⊔ sol W = kOf W := by
  have hBel : IsElemAbelian p B :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hθ.elemAbelian hB.1
  refine le_antisymm (sup_le (WB_le_kOf W B) (sol_le_kOf W)) ?_
  exact kOf_le_iSup_perfRes_cenIn_sup_sol hθ.prime hW.1.2.2.2.1 hin hBel (hB.1.trans hW.1.1) hB.2

theorem WB_mul_sol (hθ : NearFunctor p A θ) {W : Subgroup G} (hW : W ∈ mtil p A θ)
    (hin : CompInput p W) {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) :
    (WB W B : Set G) * (sol W : Set G) = (kOf W : Set G) := by
  have hle : WB W B ≤ Subgroup.normalizer (sol W : Set G) :=
    ((WB_le_kOf W B).trans (kOf_le W)).trans (Thm41Aux.le_normalizer_sol W)
  rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle, WB_sup_sol hθ hW hin hB]

theorem thetaOf_le_normalizer_WB
    (h : Counterexample p A θ) {W : Subgroup G}
    (hW : Setting p A θ W) (hI : ∀ Y ∈ dset p A θ, thetaMG p A θ Y ∈ assoc p A θ)
    (hin : CompInput p W) {B : Subgroup G} (hBA : B ≤ A) :
    thetaOf θ B ≤ Subgroup.normalizer (WB W B : Set G) :=
  Thm52Aux.le_normalizer_iSup _ fun _ => Thm52Aux.le_normalizer_iSup _ fun hb =>
    Thm52Aux.le_normalizer_iSup _ fun hb1 =>
      (thetaOf_le_apply hb hb1).trans (apply_le_normalizer_perfRes_cenIn h hW hI hin (hBA hb) hb1)

end Thm53A

end CFSG.SignalizerFunctorTheorem.McBride.Near
