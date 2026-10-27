module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfCover
public import CFSG.Quasithin.Background.B4ModelsApi
public import CFSG.Quasithin.Background.F918D0
import CFSG.Quasithin.Background.B4L3Coord
import CFSG.Quasithin.Background.G64NatSec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

section Natural

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def s16ntNatRep [Algebra (ZMod 2) K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) : Representation (ZMod 2) ↥Γ (ι → K) where
  toFun γ := (Matrix.mulVecLin ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)).restrictScalars
    (ZMod 2)
  map_one' := by
    ext x i
    simp
  map_mul' γ δ := by
    ext x i
    simp

theorem s16nt_card_natMod [Finite K] (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    Nat.card (FFModel.nat Γ).Mod = Nat.card K ^ Fintype.card ι := by
  rw [← Nat.card_congr (MulEquiv.ofBijective (G64.natQuot Γ)
      ⟨G64.natQuot_injective, G64.natQuot_surjective⟩).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

theorem s16nt_cover_of_h1 [Finite K] [Algebra (ZMod 2) K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) {c : ℕ}
    (h : Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1
      (Representation.dual (s16ntNatRep Γ))) ≤ c) :
    S16BoundCover (FFModel.nat Γ) c := by
  intro W _ _ hW2 H Z hZ hcomm hreal
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ
  have hcomm' : XMod.commOf ↥H (⊤ : Subgroup W) = ⊤ := by
    rw [commOf_eq_commSub, ← commV_eq_commSub]; exact hcomm
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥Γ) hW2 H ⊤ Z le_top
    (fun z hz x hx => mem_fixV.1 (hZ hz) x hx) (fun x hx v hv => Subgroup.mem_top _) hcomm'
    π hπ.1 (s16ntNatRep Γ) β hβs hβk (fun γ v hv => hβe γ v hv)
  exact hcard.trans (Nat.pow_le_pow_right (by norm_num) h)

end Natural

theorem s16nt_cover_of_h1_model {D : FFModel} (hD : D.IsActionModel) [Finite D.Gam] {Q : Type}
    [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q] (e : D.Mod ≃* Multiplicative Q)
    (ρ : Representation (ZMod 2) D.Gam Q)
    (hρ : ∀ (γ : D.Gam) (q : D.Mod),
      e (hD.modAct γ q) = Multiplicative.ofAdd (ρ γ (Multiplicative.toAdd (e q)))) {c : ℕ}
    (h : Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 (Representation.dual ρ)) ≤ c) :
    S16BoundCover D c := by
  intro W _ _ hW2 H Z hZ hcomm hreal
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  let β' : ↥(⊤ : Subgroup W) →* Multiplicative Q := e.toMonoidHom.comp β
  have hβ's : Function.Surjective β' := e.surjective.comp hβs
  have hβ'k : ∀ u : ↥(⊤ : Subgroup W), β' u = 1 ↔ (u : W) ∈ Z := by
    intro u
    change e (β u) = 1 ↔ (u : W) ∈ Z
    rw [e.map_eq_one_iff, hβk]
  have hβ'e : ∀ (γ : D.Gam) (v : ↥(⊤ : Subgroup W))
      (hv : ((π γ : ↥H) : MulAut W) (v : W) ∈ (⊤ : Subgroup W)),
      β' ⟨((π γ : ↥H) : MulAut W) (v : W), hv⟩ =
        Multiplicative.ofAdd (ρ γ (Multiplicative.toAdd (β' v))) := by
    intro γ v hv
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β v)
    have hm' : D.act γ (m : D.Amb) ∈ D.sec := hD.sec_inv γ m m.2
    have h1 := hβe γ v m hv hm' hm.symm
    calc β' ⟨_, hv⟩
        = e (β ⟨_, hv⟩) := rfl
      _ = e (QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm'⟩) := by rw [h1]
      _ = e (hD.modAct γ (QuotientGroup.mk m)) := by
            show e (QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm'⟩) =
              e (hD.modEnd γ (QuotientGroup.mk m))
            rw [hD.modEnd_mk]
            rfl
      _ = e (hD.modAct γ (β v)) := by rw [hm]
      _ = Multiplicative.ofAdd (ρ γ (Multiplicative.toAdd (e (β v)))) := hρ γ (β v)
      _ = Multiplicative.ofAdd (ρ γ (Multiplicative.toAdd (β' v))) := rfl
  have hcomm' : XMod.commOf ↥H (⊤ : Subgroup W) = ⊤ := by
    rw [commOf_eq_commSub, ← commV_eq_commSub]; exact hcomm
  have hcard := card_le_pow_finrank_H1_dual (Γ := D.Gam) hW2 H ⊤ Z le_top
    (fun z hz x hx => mem_fixV.1 (hZ hz) x hx) (fun x hx v hv => Subgroup.mem_top _) hcomm'
    π hπs ρ β' hβ's hβ'k hβ'e
  exact hcard.trans (Nat.pow_le_pow_right (by norm_num) h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
