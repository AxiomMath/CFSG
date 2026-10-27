module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC22K331ClLift
import CFSG.LocalAnalysis.UniquenessCase.UC22S206d
import CFSG.LocalAnalysis.UniquenessCase.UC22S206e
import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22S206c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.Open (StatedProj StatedScalars)

theorem k331c_ker_le_center {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (H : Subgroup (GL ι F)) :
    (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H)).ker ≤ Subgroup.center ↥H := by
  intro x hx
  rw [QuotientGroup.ker_mk'] at hx
  have hx' : (x : GL ι F) ∈ Subgroup.center (GL ι F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.mp hx' (y : GL ι F))

theorem k331c_six_le_card {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) {H : Subgroup (GL ι F)} {L : Type} [Group L] [Finite L]
    (e : L ≃* StatedProj H) {K : Subgroup L} (hK : IsAlt (Bar2 K) 8) : 6 ≤ Fintype.card ι := by
  haveI : Finite (GL ι F) :=
    Finite.of_injective (fun g : GL ι F => (g : Matrix ι ι F)) Units.val_injective
  let φ : ↥H →* L := e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H))
  have hφ : Function.Surjective φ :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ Subgroup.center ↥H := by
    refine le_trans (fun x hx => ?_) (k331c_ker_le_center H)
    rw [MonoidHom.mem_ker] at hx ⊢
    exact e.symm.injective (hx.trans (map_one e.symm).symm)
  obtain ⟨Γ, _, _, ρ, χ, hρ, hχ, hχ2⟩ := k331c_lift φ hφ hker hK
  let ρ' : Γ →* GL ι F := H.subtype.comp ρ
  have hρ' : Function.Injective ρ' := Subtype.val_injective.comp hρ
  have hker' : ρ'.ker ≤ χ.ker := by
    rw [(MonoidHom.ker_eq_bot_iff ρ').mpr hρ']
    exact bot_le
  obtain ⟨x, y, -, -, hx, hy, -, E, -, hE, hE8, hyE, hfix⟩ :=
    uc22s206d_alt8 χ hχ hχ2 ρ' hker'
  let P : GL ι F →* Module.End F (ι → F) :=
    (Units.coeHom (Module.End F (ι → F))).comp Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hPE : ∀ a ∈ E, P a = 1 → a = 1 := by
    intro a _ ha
    have h1 : Matrix.GeneralLinearGroup.toLin a = 1 := Units.ext ha
    exact Matrix.GeneralLinearGroup.toLin.injective (h1.trans (map_one _).symm)
  have hg7 : (ρ' y) ^ 7 = 1 := by
    rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  have h6 := uc22s206e_six (F := F) (V := ι → F) h2 P hE hE8 hPE hg7 hyE hfix
  exact h6.trans
    ((Submodule.finrank_le _).trans (Module.finrank_fintype_fun_eq_card (R := F) (η := ι)).le)

theorem k331At_of_proj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι ≤ 5) {H : Subgroup (GL ι F)} {L : Type} [Group L]
    [Finite L] (e : L ≃* StatedProj H) : K331At L := by
  intro T _ K hK _
  exact absurd (k331c_six_le_card h2 e hK) (by omega)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
