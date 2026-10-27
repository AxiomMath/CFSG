module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1.QuotMap
import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

private theorem commSub_le_of_sup_eq_top {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    {Z P : Subgroup W} (hZ : Z ≤ fixV K) (hP : StableUnder K P) (hsup : P ⊔ Z = ⊤) :
    commSub (⊤ : Subgroup W) K ≤ P := by
  rw [commSub, Subgroup.closure_le]
  rintro q ⟨x, hx, w, -, rfl⟩
  have hw : w ∈ P ⊔ Z := by rw [hsup]; exact Subgroup.mem_top w
  obtain ⟨p, hp, s, hs, rfl⟩ := Subgroup.mem_sup.mp hw
  have hxp : x p ∈ P := hP x hx p hp
  have hxs : x s = s := (mem_fixV.mp (hZ hs)) x hx
  have heq : x (p * s) * (p * s)⁻¹ = x p * p⁻¹ := by
    rw [map_mul, hxs]
    group
  rw [heq]
  exact P.mul_mem hxp (P.inv_mem hp)

private theorem exists_coordEquiv {W : Type} [CommGroup W] {Z P : Subgroup W} {Kf : Type}
    [Field Kf] (hinf : P ⊓ Z = ⊥) (hsup : P ⊔ Z = ⊤)
    {β : ↥(⊤ : Subgroup (W ⧸ Z)) →* Multiplicative (Fin 3 → Kf)}
    (hβinj : Function.Injective β) (hβsurj : Function.Surjective β) :
    ∃ e : ↥P ≃* Multiplicative (Fin 3 → Kf),
      ∀ (w : W) (hw : w ∈ P), e ⟨w, hw⟩ =
        (β ⟨QuotientGroup.mk w, Subgroup.mem_top _⟩ : Multiplicative (Fin 3 → Kf)) := by
  let f' : ↥P →* ↥(⊤ : Subgroup (W ⧸ Z)) :=
    ((QuotientGroup.mk' Z).comp (Subgroup.subtype P)).codRestrict ⊤ fun _ => Subgroup.mem_top _
  have hf_inj : Function.Injective f' := by
    intro a b hab
    have h1 : (a : W) * (b : W)⁻¹ ∈ Z :=
      (mk_eq_mk_iff (a : W) (b : W)).mp (congrArg Subtype.val hab)
    have h2 : (a : W) * (b : W)⁻¹ ∈ P := P.mul_mem a.2 (P.inv_mem b.2)
    have h3 : (a : W) * (b : W)⁻¹ = 1 := by
      have h4 : (a : W) * (b : W)⁻¹ ∈ P ⊓ Z := ⟨h2, h1⟩
      rw [hinf] at h4
      simpa using h4
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  have hf_surj : Function.Surjective f' := by
    intro u
    obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective Z (u : W ⧸ Z)
    have hu : u = ⟨QuotientGroup.mk w, Subgroup.mem_top _⟩ := Subtype.ext hw.symm
    have hwtop : w ∈ P ⊔ Z := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨p, hp, s, hs, rfl⟩ := Subgroup.mem_sup.mp hwtop
    refine ⟨⟨p, hp⟩, ?_⟩
    rw [hu]
    refine Subtype.ext ?_
    change QuotientGroup.mk p = QuotientGroup.mk (p * s)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff s).mpr hs, mul_one]
  refine ⟨MulEquiv.ofBijective (β.comp f') ⟨hβinj.comp hf_inj, hβsurj.comp hf_surj⟩, ?_⟩
  intro w hw
  rfl

private theorem cNatModSU3Sub_of_realizes {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    {Z P : Subgroup W} {n : ℕ} (hZK : StableUnder K Z) (hZ : Z ≤ fixV K) (hP : StableUnder K P)
    (hinf : P ⊓ Z = ⊥) (hsup : P ⊔ Z = ⊤) {Kf : Type} [hF : Field Kf] [hFin : Finite Kf]
    (hKcard : Nat.card Kf = (2 ^ n) ^ 2) {π : ↥(StatedSU 3 (2 ^ n) Kf) →* ↥(autQuot K Z)}
    (hπ : (FFModel.nat (StatedSU 3 (2 ^ n) Kf)).RealizesVia (autQuot K Z) ⊤ ⊥ π) :
    CNatModSU3Sub W P K n := by
  classical
  obtain ⟨β, hβsurj, hβker, hβeq⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.nat (StatedSU 3 (2 ^ n) Kf)) rfl rfl hπ
  have hβinj : Function.Injective β := (injective_iff_map_eq_one β).mpr fun u hu =>
    Subtype.ext (by simpa [Subgroup.mem_bot] using (hβker u).1 hu)
  obtain ⟨eP, heP⟩ := exists_coordEquiv (β := β) hinf hsup hβinj hβsurj
  refine ⟨⟨Kf, hKcard, eP, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx w hw
    exact hP x hx w hw
  · intro x hx
    obtain ⟨γx, hγx⟩ := hπ.1 (toAutQuot hZK ⟨x, hx⟩)
    let γx' : ↥(StatedSU 3 (2 ^ n) Kf) := γx
    have hγx' : π γx' = toAutQuot hZK ⟨x, hx⟩ := hγx
    refine ⟨(γx' : Matrix.GeneralLinearGroup (Fin 3) Kf), γx'.2, ?_⟩
    intro w hw hxw
    have hxw' : ((π γx' : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) (QuotientGroup.mk w) =
        QuotientGroup.mk ((x : MulAut W) w) := by
      rw [hγx', toAutQuot_apply_mk]
    have hkey : (β ⟨((π γx' : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) (QuotientGroup.mk w),
          Subgroup.mem_top _⟩ : Multiplicative (Fin 3 → Kf)) =
        Multiplicative.ofAdd (((γx' : Matrix.GeneralLinearGroup (Fin 3) Kf) :
          Matrix (Fin 3) (Fin 3) Kf).mulVec (Multiplicative.toAdd
            (β ⟨QuotientGroup.mk w, Subgroup.mem_top _⟩ : Multiplicative (Fin 3 → Kf)))) :=
      hβeq γx' ⟨QuotientGroup.mk w, Subgroup.mem_top _⟩ (Subgroup.mem_top _)
    rw [heP (x w) hxw, heP w hw, ← hxw']
    exact hkey
  · intro A hA
    let γA : ↥(StatedSU 3 (2 ^ n) Kf) := ⟨A, hA⟩
    obtain ⟨x, hx⟩ := toAutQuot_surjective hZK (π γA)
    refine ⟨x, x.2, ?_⟩
    intro w hw hxw
    have hxw' : ((π γA : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) (QuotientGroup.mk w) =
        QuotientGroup.mk ((x : MulAut W) w) := by
      rw [← hx, toAutQuot_apply_mk]
    have hkey : (β ⟨((π γA : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) (QuotientGroup.mk w),
          Subgroup.mem_top _⟩ : Multiplicative (Fin 3 → Kf)) =
        Multiplicative.ofAdd (((γA : Matrix.GeneralLinearGroup (Fin 3) Kf) :
          Matrix (Fin 3) (Fin 3) Kf).mulVec (Multiplicative.toAdd
            (β ⟨QuotientGroup.mk w, Subgroup.mem_top _⟩ : Multiplicative (Fin 3 → Kf)))) :=
      hβeq γA ⟨QuotientGroup.mk w, Subgroup.mem_top _⟩ (Subgroup.mem_top _)
    rw [heP ((x : MulAut W) w) hxw, heP w hw, ← hxw']
    exact hkey
  · intro x hx hfix
    apply MulEquiv.ext
    intro u
    have hutop : u ∈ P ⊔ Z := by rw [hsup]; exact Subgroup.mem_top u
    obtain ⟨p, hp, s, hs, rfl⟩ := Subgroup.mem_sup.mp hutop
    have hxp : (x : MulAut W) p = p := hfix p hp
    have hxs : (x : MulAut W) s = s := (mem_fixV.mp (hZ hs)) x hx
    rw [map_mul, hxp, hxs]
    rfl

theorem commSub_eq_and_cNatModSU3Sub_of_compl {W : Type} [CommGroup W]
    {K : Subgroup (MulAut W)} {Z : Subgroup W} {n : ℕ} (hZK : StableUnder K Z)
    (hZ : Z ≤ fixV K) (hNat : NatSUn (autQuot K Z) ⊤ ⊥ 3 n) {P : Subgroup W}
    (hP : StableUnder K P) (hinf : P ⊓ Z = ⊥) (hsup : P ⊔ Z = ⊤)
    (hPK : P ≤ commSub (⊤ : Subgroup W) K) :
    P = commSub (⊤ : Subgroup W) K ∧ CNatModSU3Sub W P K n := by
  obtain ⟨Kf, hKfield, hKfin, hKcard, π, hπ⟩ := hNat
  exact ⟨le_antisymm hPK (commSub_le_of_sup_eq_top hZ hP hsup),
    cNatModSU3Sub_of_realizes (hF := hKfield) (hFin := hKfin) hZK hZ hP hinf hsup hKcard hπ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1
