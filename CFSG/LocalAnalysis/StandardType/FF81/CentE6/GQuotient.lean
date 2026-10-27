module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.RadSetting

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG.RankThree.GF2n.Smith81

private abbrev Hc {G : Type} [Group G] (t : G) : Subgroup G :=
  Subgroup.centralizer ({t} : Set G)

private abbrev Nc {G : Type} [Group G] (t : G) (Q : Subgroup G) : Subgroup ↥(Hc t) :=
  Q.subgroupOf (Hc t)

section Helpers

private theorem conj_mem_Q {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (h : ↥(Hc t)) (q : ↥Q) :
    (h : G) * (q : G) * (h : G)⁻¹ ∈ Q := by
  have hq : (⟨(q : G), R.le_cen_Q q.2⟩ : ↥(Hc t)) ∈ Nc t Q :=
    Subgroup.mem_subgroupOf.mpr q.2
  exact Subgroup.mem_subgroupOf.mp (hN.conj_mem ⟨(q : G), R.le_cen_Q q.2⟩ hq h)

private noncomputable def conjAutQ {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (h : ↥(Hc t)) : ↥Q ≃* ↥Q where
  toFun q := ⟨(h : G) * (q : G) * (h : G)⁻¹, conj_mem_Q R h q⟩
  invFun q := ⟨(h : G)⁻¹ * (q : G) * (h : G), by simpa using conj_mem_Q R h⁻¹ q⟩
  left_inv q := by
    apply Subtype.ext
    group
  right_inv q := by
    apply Subtype.ext
    group
  map_mul' q r := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

private theorem conjAutQ_mem_ker {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (h : ↥(Hc t)) {q : ↥Q} (hq : q ∈ π.ker) :
    conjAutQ R h q ∈ π.ker := by
  rw [MonoidHom.mem_ker] at hq ⊢
  have hz : (q : G) ∈ Subgroup.zpowers t := (R.ker_iff q).mp hq
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hcomm : (h : G) * t = t * (h : G) :=
    (Subgroup.mem_centralizer_iff.mp h.2 t (by simp)).symm
  have hconj : (h : G) * (q : G) * (h : G)⁻¹ = (q : G) := by
    calc
      (h : G) * (q : G) * (h : G)⁻¹ = (MulAut.conj (h : G)) (q : G) := rfl
      _ = (MulAut.conj (h : G)) (t ^ n) := by rw [← hn]
      _ = ((MulAut.conj (h : G)) t) ^ n := map_zpow _ _ _
      _ = t ^ n := by
        rw [MulAut.conj_apply, hcomm, mul_assoc, mul_inv_cancel, mul_one]
      _ = (q : G) := hn
  have hEq : conjAutQ R h q = q := Subtype.ext hconj
  rw [hEq, hq]

private theorem conjAutQ_ker_le {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (h : ↥(Hc t)) :
    π.ker ≤ (π.ker).comap (conjAutQ R h) := by
  intro q hq
  exact conjAutQ_mem_ker R h hq

@[simp] private theorem conjAutQ_coe {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (h : ↥(Hc t)) (q : ↥Q) :
    ((conjAutQ R h q : ↥Q) : G) = (h : G) * (q : G) * (h : G)⁻¹ := rfl

@[simp] private theorem conjAutQ_one {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (q : ↥Q) :
    conjAutQ R (1 : ↥(Hc t)) q = q := by
  apply Subtype.ext
  simp

@[simp] private theorem conjAutQ_comp {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (h h' : ↥(Hc t)) (q : ↥Q) :
    conjAutQ R h (conjAutQ R h' q) = conjAutQ R (h * h') q := by
  apply Subtype.ext
  simp only [conjAutQ_coe, Subgroup.coe_mul]
  group

private noncomputable abbrev conjQuot {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (h : ↥(Hc t)) :
    (↥Q ⧸ π.ker) ≃* (↥Q ⧸ π.ker) where
  toFun := QuotientGroup.map π.ker π.ker (conjAutQ R h) (conjAutQ_ker_le R h)
  invFun := QuotientGroup.map π.ker π.ker (conjAutQ R h⁻¹) (conjAutQ_ker_le R h⁻¹)
  left_inv x := by
    refine QuotientGroup.induction_on x (fun q => ?_)
    simp only [QuotientGroup.map_mk]
    change QuotientGroup.mk (conjAutQ R h⁻¹ (conjAutQ R h q)) = QuotientGroup.mk q
    rw [conjAutQ_comp]
    simp
  right_inv x := by
    refine QuotientGroup.induction_on x (fun q => ?_)
    simp only [QuotientGroup.map_mk]
    change QuotientGroup.mk (conjAutQ R h (conjAutQ R h⁻¹ q)) = QuotientGroup.mk q
    rw [conjAutQ_comp]
    simp
  map_mul' x y := map_mul _ x y

@[simp] private theorem conjQuot_apply {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (h : ↥(Hc t)) (x : ↥Q ⧸ π.ker) :
    conjQuot R h x = QuotientGroup.map π.ker π.ker (conjAutQ R h) (conjAutQ_ker_le R h) x :=
  rfl

private noncomputable def conjQuotHom {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] : ↥(Hc t) →* MulAut (↥Q ⧸ π.ker) where
  toFun h := conjQuot R h
  map_one' := by
    ext x
    refine QuotientGroup.induction_on x (fun q => ?_)
    rw [conjQuot_apply]
    simp only [MulAut.one_apply, QuotientGroup.map_mk]
    change QuotientGroup.mk (conjAutQ R (1 : ↥(Hc t)) q) = QuotientGroup.mk q
    rw [conjAutQ_one]
  map_mul' h h' := by
    ext x
    refine QuotientGroup.induction_on x (fun q => ?_)
    rw [conjQuot_apply, MulAut.mul_apply, conjQuot_apply, conjQuot_apply]
    simp only [QuotientGroup.map_mk]
    change QuotientGroup.mk (conjAutQ R (h * h') q) =
      QuotientGroup.mk (conjAutQ R h (conjAutQ R h' q))
    rw [conjAutQ_comp]

private noncomputable def cubeEquiv {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b) :
    Additive (↥Q ⧸ π.ker) ≃+ A5Cube.Cube (ZMod 2) :=
  (QuotientGroup.quotientKerEquivOfSurjective (φ := π) R.surj).toAdditive

private noncomputable def actCubeAdd {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (h : ↥(Hc t)) :
    A5Cube.Cube (ZMod 2) ≃+ A5Cube.Cube (ZMod 2) :=
  ((cubeEquiv R).symm.trans (conjQuotHom R h).toAdditive).trans (cubeEquiv R)

private noncomputable def rhoH {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] :
    ↥(Hc t) →* Module.End (ZMod 2) (A5Cube.Cube (ZMod 2)) where
  toFun h := (actCubeAdd R h).toAddMonoidHom.toZModLinearMap 2
  map_one' := by
    ext v
    simp [actCubeAdd]
  map_mul' h h' := by
    ext v
    simp [actCubeAdd]

private theorem pi_conjAutQ_of_mem_Q {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (q0 q : ↥Q) :
    π (conjAutQ R (⟨(q0 : G), R.le_cen_Q q0.2⟩ : ↥(Hc t)) q) = π q := by
  have hdecomp : conjAutQ R (⟨(q0 : G), R.le_cen_Q q0.2⟩ : ↥(Hc t)) q =
      (⟨(q0 : G), q0.2⟩ : ↥Q) * q * (⟨(q0 : G), q0.2⟩ : ↥Q)⁻¹ := by
    apply Subtype.ext
    simp [conjAutQ]
  rw [hdecomp, map_mul, map_mul, map_inv]
  rw [mul_comm (π (⟨(q0 : G), q0.2⟩ : ↥Q)) (π q), mul_assoc,
    mul_inv_cancel, mul_one]

private theorem conjQuot_eq_one_of_mem_Q {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (q0 : ↥Q) :
    conjQuotHom R (⟨(q0 : G), R.le_cen_Q q0.2⟩ : ↥(Hc t)) = 1 := by
  ext x
  refine QuotientGroup.induction_on x (fun q => ?_)
  rw [show conjQuotHom R (⟨(q0 : G), R.le_cen_Q q0.2⟩ : ↥(Hc t)) =
    conjQuot R (⟨(q0 : G), R.le_cen_Q q0.2⟩ : ↥(Hc t)) from rfl]
  rw [conjQuot_apply]
  simp only [MulAut.one_apply, QuotientGroup.map_mk]
  change QuotientGroup.mk (conjAutQ R (⟨(q0 : G), R.le_cen_Q q0.2⟩ : ↥(Hc t)) q) =
    QuotientGroup.mk q
  apply QuotientGroup.eq.mpr
  rw [MonoidHom.mem_ker, map_mul, map_inv, pi_conjAutQ_of_mem_Q]
  simp

private theorem rhoH_eq_one_of_mem_Q {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (q0 : ↥Q) :
    rhoH R (⟨(q0 : G), R.le_cen_Q q0.2⟩ : ↥(Hc t)) = 1 := by
  ext v
  simp [rhoH, actCubeAdd, conjQuot_eq_one_of_mem_Q R q0]

private theorem N_le_rhoH_ker {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] : Nc t Q ≤ (rhoH R).ker := by
  intro h hh
  rw [MonoidHom.mem_ker]
  have hQ : (h : G) ∈ Q := Subgroup.mem_subgroupOf.mp hh
  have hEq : h = (⟨(h : G), R.le_cen_Q hQ⟩ : ↥(Hc t)) := Subtype.ext rfl
  rw [hEq]
  exact rhoH_eq_one_of_mem_Q R ⟨(h : G), hQ⟩

private noncomputable def rhoX {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] :
    (↥(Hc t) ⧸ Nc t Q) →* Module.End (ZMod 2) (A5Cube.Cube (ZMod 2)) :=
  QuotientGroup.lift (Nc t Q) (rhoH R) (N_le_rhoH_ker R)

@[simp] private theorem rhoH_apply {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (h : ↥(Hc t))
    (v : A5Cube.Cube (ZMod 2)) :
    rhoH R h v = (actCubeAdd R h) v := rfl

@[simp] private theorem actCubeAdd_apply {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (h : ↥(Hc t))
    (v : A5Cube.Cube (ZMod 2)) :
    actCubeAdd R h v = cubeEquiv R (Additive.ofMul ((conjQuotHom R h)
      (Additive.toMul ((cubeEquiv R).symm v)))) := rfl

@[simp] private theorem conjQuotHom_apply {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (h : ↥(Hc t)) (x : ↥Q ⧸ π.ker) :
    conjQuotHom R h x = conjQuot R h x := rfl

private theorem cubeEquiv_mk {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b) (q : ↥Q) :
    cubeEquiv R (Additive.ofMul (QuotientGroup.mk q : ↥Q ⧸ π.ker)) =
      Multiplicative.toAdd (π q) := rfl

private theorem cubeEquiv_mk' {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b) (q : ↥Q) :
    cubeEquiv R (Additive.ofMul (QuotientGroup.mk' π.ker q)) =
      Multiplicative.toAdd (π q) := rfl

private theorem rhoH_on_L {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (l : ↥L) :
    rhoH R (⟨(l : G), R.le_cen_L l.2⟩ : ↥(Hc t)) = cubeAct (eL l) := by
  apply LinearMap.ext
  intro v
  obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective (π.ker) ((cubeEquiv R).symm v)
  have hv : cubeEquiv R (Additive.ofMul ((QuotientGroup.mk' π.ker) q)) = v := by
    calc
      cubeEquiv R (Additive.ofMul ((QuotientGroup.mk' π.ker) q)) =
          cubeEquiv R (Additive.ofMul ((cubeEquiv R).symm v)) := by rw [hq]
      _ = cubeEquiv R ((cubeEquiv R).symm v) := rfl
      _ = v := (cubeEquiv R).apply_symm_apply v
  rw [← hv, rhoH_apply, actCubeAdd_apply]
  simp only [AddEquiv.symm_apply_apply, toMul_ofMul, conjQuotHom_apply,
    conjQuot_apply, QuotientGroup.map_mk']
  simp only [cubeEquiv_mk, cubeEquiv_mk']
  have hconj : conjAutQ R (⟨(l : G), R.le_cen_L l.2⟩ : ↥(Hc t)) q =
      (⟨(l : G) * (q : G) * (l : G)⁻¹, conj_mem_Q R ⟨(l : G), R.le_cen_L l.2⟩ q⟩ : ↥Q) :=
    Subtype.ext rfl
  have hpi : Multiplicative.toAdd (π (conjAutQ R (⟨(l : G), R.le_cen_L l.2⟩ : ↥(Hc t)) q)) =
      Multiplicative.toAdd (π (⟨(l : G) * (q : G) * (l : G)⁻¹,
        conj_mem_Q R ⟨(l : G), R.le_cen_L l.2⟩ q⟩ : ↥Q)) :=
    congrArg (fun x => Multiplicative.toAdd (π x)) hconj
  change Multiplicative.toAdd (π (conjAutQ R (⟨(l : G), R.le_cen_L l.2⟩ : ↥(Hc t)) q)) =
    (cubeAct (eL l)) (Multiplicative.toAdd (π q))
  rw [hpi]
  exact R.equivariant l q (conj_mem_Q R ⟨(l : G), R.le_cen_L l.2⟩ q)


private noncomputable def Lbar {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (_R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] : Subgroup (↥(Hc t) ⧸ Nc t Q) :=
  (L.subgroupOf (Hc t)).map (QuotientGroup.mk' (Nc t Q))

private noncomputable def phiL {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] : ↥L →* (↥(Hc t) ⧸ Nc t Q) :=
  (QuotientGroup.mk' (Nc t Q)).comp (Subgroup.inclusion R.le_cen_L)

private theorem phiL_mem_Lbar {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (l : ↥L) : phiL R l ∈ Lbar R := by
  rw [Lbar, Subgroup.mem_map]
  refine ⟨⟨(l : G), R.le_cen_L l.2⟩, ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr l.2

private noncomputable def phiLBar {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] : ↥L →* ↥(Lbar R) where
  toFun l := ⟨phiL R l, phiL_mem_Lbar R l⟩
  map_one' := Subtype.ext (map_one (phiL R))
  map_mul' l l' := Subtype.ext (map_mul (phiL R) l l')

private theorem phiL_injective {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] : Function.Injective (phiL R) := by
  intro l1 l2 h
  have h' : (QuotientGroup.mk' (Nc t Q) (Subgroup.inclusion R.le_cen_L l1)) =
      (QuotientGroup.mk' (Nc t Q) (Subgroup.inclusion R.le_cen_L l2)) := h
  have hmemN : (Subgroup.inclusion R.le_cen_L l1)⁻¹ *
      (Subgroup.inclusion R.le_cen_L l2) ∈ Nc t Q := QuotientGroup.eq.mp h'
  have hQ : (l1 : G)⁻¹ * (l2 : G) ∈ Q := by
    simpa using Subgroup.mem_subgroupOf.mp hmemN
  have hL : (l1 : G)⁻¹ * (l2 : G) ∈ L := L.mul_mem (L.inv_mem l1.2) l2.2
  have hbot : (l1 : G)⁻¹ * (l2 : G) ∈ (⊥ : Subgroup G) := by
    rw [← R.inf_eq_bot]
    exact ⟨hL, hQ⟩
  have hone : (l1 : G)⁻¹ * (l2 : G) = 1 := Subgroup.mem_bot.mp hbot
  apply Subtype.ext
  have h12 : (l2 : G) = (l1 : G) := by
    have := congrArg (fun x => (l1 : G) * x) hone
    simpa using this
  exact h12.symm

private theorem phiLBar_surjective {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] : Function.Surjective (phiLBar R) := by
  intro x
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
  have hyL : (y : G) ∈ L := Subgroup.mem_subgroupOf.mp hy
  refine ⟨⟨(y : G), hyL⟩, ?_⟩
  apply Subtype.ext
  rw [← hyx]
  rfl

private theorem phiLBar_injective {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] : Function.Injective (phiLBar R) := by
  intro l1 l2 h
  exact phiL_injective R (congrArg Subtype.val h)

private noncomputable def phiLBarEquiv {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] : ↥L ≃* ↥(Lbar R) :=
  MulEquiv.ofBijective (phiLBar R) ⟨phiLBar_injective R, phiLBar_surjective R⟩

private noncomputable def eLbar {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] : ↥(Lbar R) ≃* SL(6, ZMod 2) :=
  (phiLBarEquiv R).symm.trans eL

@[simp] private theorem eLbar_phiLBar {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (l : ↥L) : eLbar R (phiLBar R l) = eL l := by
  rw [eLbar, MulEquiv.trans_apply]
  change eL ((phiLBarEquiv R).symm ((phiLBarEquiv R) l)) = eL l
  rw [MulEquiv.symm_apply_apply]

private theorem Lbar_mem_iff {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (x : ↥(Hc t) ⧸ Nc t Q) :
    x ∈ Lbar R ↔ ∃ l : ↥L, (QuotientGroup.mk (⟨(l : G), R.le_cen_L l.2⟩ :
      ↥(Hc t))) = x := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyL : (y : G) ∈ L := Subgroup.mem_subgroupOf.mp hy
    refine ⟨⟨(y : G), hyL⟩, ?_⟩
    rw [← hyx]
    congr 1
  · rintro ⟨l, hl⟩
    rw [← hl]
    exact phiL_mem_Lbar R l

private theorem rhoX_mk {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Nc t Q).Normal] (h : ↥(Hc t)) :
    rhoX R (QuotientGroup.mk h) = rhoH R h := rfl

end Helpers

theorem exists_cubeSetting_quotient {G : Type} [Group G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadGeom t Q L eL π b)
    [hN : (Q.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal] :
    ∃ S : CubeSetting (↥(Subgroup.centralizer ({t} : Set G)) ⧸
        Q.subgroupOf (Subgroup.centralizer ({t} : Set G))),
      (∀ x, x ∈ S.L ↔ ∃ l : ↥L, (QuotientGroup.mk (⟨(l : G), R.le_cen_L l.2⟩ :
        ↥(Subgroup.centralizer ({t} : Set G))) :
          ↥(Subgroup.centralizer ({t} : Set G)) ⧸
            Q.subgroupOf (Subgroup.centralizer ({t} : Set G))) = x) ∧
      (∀ (l : ↥L) (hl : (QuotientGroup.mk (⟨(l : G), R.le_cen_L l.2⟩ :
        ↥(Subgroup.centralizer ({t} : Set G))) :
          ↥(Subgroup.centralizer ({t} : Set G)) ⧸
            Q.subgroupOf (Subgroup.centralizer ({t} : Set G))) ∈ S.L),
        S.eL ⟨_, hl⟩ = eL l) := by
  let S : CubeSetting (↥(Hc t) ⧸ Nc t Q) :=
    { L := Lbar R
      eL := eLbar R
      ρ := rhoX R
      hρ := by
        intro l
        obtain ⟨l0, hl0⟩ := phiLBar_surjective R l
        rw [← hl0]
        change rhoX R (QuotientGroup.mk (Subgroup.inclusion R.le_cen_L l0)) =
          cubeAct (eLbar R (phiLBar R l0))
        rw [rhoX_mk, eLbar_phiLBar]
        exact rhoH_on_L R l0 }
  exact ⟨S, Lbar_mem_iff R, fun l hl => by
    have hEq : (⟨QuotientGroup.mk (⟨(l : G), R.le_cen_L l.2⟩ : ↥(Hc t)), hl⟩ :
        ↥(Lbar R)) = phiLBar R l := Subtype.ext rfl
    rw [hEq, eLbar_phiLBar]⟩


end CFSG.StandardType.FF81.CentE6
