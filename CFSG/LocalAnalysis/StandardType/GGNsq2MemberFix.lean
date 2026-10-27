module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import CFSG.LocalAnalysis.StandardType.GGNsq2QuotNorm
public import CFSG.LocalAnalysis.StandardType.GGNsq2MemberQuotPos
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotCover
import CFSG.LocalAnalysis.StandardType.GGNsq2Main

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.CoprimeKernel CFSG.Blueprint
  CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q] {X Bs B : Subgroup G}
  {f : ↥(Subgroup.normalizer (X : Set G)) →* Q}

private lemma fL_normalizerMonoidHom_ukr
    (hD : Datum 3 (Subgroup.normalizer (X : Set G)) f X Bs (twoCentral X))
    (h₀ : ↥Bs) (l : ↥X) :
    hD.fL ((X.normalizerMonoidHom ⟨(h₀ : G), hD.BsN h₀.2⟩) l) =
      ((img _ f X).normalizerMonoidHom
        ⟨f ⟨(h₀ : G), hD.BsN h₀.2⟩, hD.f_mem_normalizer_img hD.BsN h₀.2⟩) (hD.fL l) := by
  let σL : MulAut ↥X := X.normalizerMonoidHom ⟨(h₀ : G), hD.BsN h₀.2⟩
  refine Subtype.ext ?_
  have e : (⟨((σL l : ↥X) : G), hD.LN (σL l).2⟩ :
        ↥(Subgroup.normalizer (X : Set G))) =
      ⟨(h₀ : G), hD.BsN h₀.2⟩ * ⟨(l : G), hD.LN l.2⟩ * ⟨(h₀ : G), hD.BsN h₀.2⟩⁻¹ := rfl
  change f ⟨((σL l : ↥X) : G), hD.LN (σL l).2⟩ =
    f ⟨(h₀ : G), hD.BsN h₀.2⟩ * f ⟨(l : G), hD.LN l.2⟩ *
      (f ⟨(h₀ : G), hD.BsN h₀.2⟩)⁻¹
  rw [e, map_mul, map_mul, map_inv]

private lemma twoCentral_eq_one_hU_ukr (hU : GGU62OuterDiagInput) [Finite Q]
    (hD : Datum 3 (Subgroup.normalizer (X : Set G)) f X Bs (twoCentral X))
    (hperf : Group.IsPerfect ↥X) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {ψ : Su K 2 1 6 →* Q}
    (h : GGNSLocalHyp 3 (img _ f B) (img _ f Bs) K 1 6 ψ) (hrange : ψ.range = img _ f X)
    {h₀ : ↥Bs} {g : GL (Fin 6) K}
    (hg : GGInducesUnitary (p := 2) (f := 1) ψ (hD.tau h₀ : Q) g)
    (hdet : Matrix.GeneralLinearGroup.det g ≠ 1) {z : G} (hz : z ∈ twoCentral X)
    (hcomm : (h₀ : G) * z = z * (h₀ : G)) : z = 1 := by
  let ψc : Su K 2 1 6 →* ↥(img _ f X) :=
    ψ.codRestrict (img _ f X) fun s => by
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hψcsurj : Function.Surjective ψc := by
    intro y
    have hy : (y : Q) ∈ ψ.range := hrange.symm ▸ y.2
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hy
    exact ⟨s, Subtype.ext hs⟩
  let σL : MulAut ↥X := X.normalizerMonoidHom ⟨(h₀ : G), hD.BsN h₀.2⟩
  let τL : MulAut ↥(img _ f X) := (img _ f X).normalizerMonoidHom
    ⟨f ⟨(h₀ : G), hD.BsN h₀.2⟩, hD.f_mem_normalizer_img hD.BsN h₀.2⟩
  have hzL : z ∈ X := twoCentral_le X hz
  have hzker : (⟨z, hzL⟩ : ↥X) ∈ hD.fL.ker := (hD.fL_eq_one_iff _).2 hz
  have hres := hU K hK ↥X ↥(img _ f X) hD.fL ψc σL τL g hperf hD.fL_surjective
    (fun u hu l' => Subgroup.mem_center_iff.1
      (hD.mem_center_of_mem ((hD.fL_eq_one_iff u).1 hu)) l')
    (fun u hu => by
      obtain ⟨k, hk⟩ := hD.Z2 _ ((hD.fL_eq_one_iff u).1 hu)
      exact ⟨k, Subtype.ext (by simpa using hk)⟩)
    hψcsurj
    (fun s hs => h.ker (by
      rw [MonoidHom.mem_ker] at hs ⊢
      exact congrArg Subtype.val hs))
    (fun l => fL_normalizerMonoidHom_ukr hD h₀ l)
    hg.1 hdet
    (fun s => by
      obtain ⟨y', hy', hby⟩ := hg.2 s
      exact ⟨y', hy', Subtype.ext hby⟩)
    ⟨z, hzL⟩ hzker (Subtype.ext (by
      show (h₀ : G) * z * (h₀ : G)⁻¹ = z
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm))
  exact congrArg Subtype.val hres

theorem Datum.twoCentral_eq_one_of_det_ne_one (hU : GGU62OuterDiagInput) [Finite Q]
    (hD : Datum 3 (Subgroup.normalizer (X : Set G)) f X Bs (twoCentral X))
    (hperf : Group.IsPerfect ↥X) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {ψ : Su K 2 1 6 →* Q}
    (h : GGNSLocalHyp 3 (img _ f B) (img _ f Bs) K 1 6 ψ) (hrange : ψ.range = img _ f X)
    {δ : ↥(img _ f Bs) →* Kˣ}
    (hδ : ∀ (b : ↥(img _ f Bs)) (g : GL (Fin 6) K),
      GGInducesUnitary (p := 2) (f := 1) ψ (b : Q) g →
        Matrix.GeneralLinearGroup.det g = δ b)
    {h₀ : ↥Bs} (hδ₀ : δ (hD.tau h₀) ≠ 1) {z : G} (hz : z ∈ twoCentral X)
    (hcomm : (h₀ : G) * z = z * (h₀ : G)) : z = 1 := by
  obtain ⟨g, hg⟩ := h.acts ((hD.tau h₀ : ↥(img _ f Bs)) : Q) (hD.tau h₀).2
  exact twoCentral_eq_one_hU_ukr hU hD hperf hK h hrange hg
    (by rw [hδ (hD.tau h₀) g hg]; exact hδ₀) hz hcomm

end NsQuot

end CFSG.StandardType

end
