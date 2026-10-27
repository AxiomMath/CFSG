module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Inner
import CFSG.LocalAnalysis.WeakClosure81.W183K3InnerFourAux1
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Core

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y R T L N : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V}

private theorem w183k3_finite_lgl : Finite (LGL 2 V) :=
  Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
    (fun e f h => LinearEquiv.ext (congrFun h))

private theorem w183k3_isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : CFSG.Open.IsQuasisimple B) : CFSG.Open.IsQuasisimple A := by
  have : Group.IsPerfect B := ⟨h.1⟩
  have : IsSimpleGroup (B ⧸ Subgroup.center B) := h.2
  have hperfect : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨hperfect.commutator_eq_top,
    (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
      (Subgroup.map_center_eq e)).isSimpleGroup⟩

private theorem w183k3_sq_eq_one (v : Multiplicative V) : v ^ 2 = 1 := by
  have h : (v ^ 2).toAdd = 0 := by
    rw [toAdd_pow, two_nsmul, ZModModule.add_self]
  calc v ^ 2 = Multiplicative.ofAdd (v ^ 2).toAdd := (ofAdd_toAdd _).symm
    _ = Multiplicative.ofAdd 0 := by rw [h]
    _ = 1 := rfl

theorem w183k3_four_mul_cent (h65f : Asch6_5Four) (c : QuasiCore R L N)
    (hshape : IsL3 (↥L ⧸ Subgroup.center ↥L) 2) {A : Subgroup (LGL 2 V)} (hAR : A ≤ R)
    (hcard : Nat.card ↥A = 4) (hel : IsElemAbelian 2 A)
    (hq : CFSG.Quasithin.G11.commSpace A (CFSG.SignalizerFunctorTheorem.Quadratic.commSub A) = ⊥) :
    ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, (a * l⁻¹) * x = x * (a * l⁻¹) := by
  classical
  haveI : Finite (LGL 2 V) := w183k3_finite_lgl
  haveI : Finite ↥R := Finite.of_injective (fun r : ↥R => (r : LGL 2 V)) Subtype.val_injective
  let Y₀ : Type := ↥L ⧸ Subgroup.center ↥L
  have hsub : IsSubnormal (L.subgroupOf R) ⊤ := by
    refine IsSubnormal.step le_top ?_ (IsSubnormal.refl ⊤)
    rw [Subgroup.normal_subgroupOf_iff le_top]
    intro a b ha _
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using c.normal (b : LGL 2 V) b.2 (a : LGL 2 V) ha
  have hcomp : IsComponentOf (L.subgroupOf R) ⊤ :=
    ⟨le_top, hsub,
      w183k3_isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe c.le) c.quasi⟩
  have hcov : CFSG.LocalAnalysis.UniquenessCase.UC22.CoverOf ↥(L.subgroupOf R) Y₀ := by
    refine ⟨w183k3_isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe c.le) c.quasi, ?_⟩
    exact ⟨QuotientGroup.congr (Subgroup.center ↥(L.subgroupOf R)) (Subgroup.center ↥L)
      (Subgroup.subgroupOfEquivOfLe c.le)
      (Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe c.le))⟩
  have hAcard : Nat.card ↥(A.subgroupOf R) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAR).toEquiv, hcard]
  have hel' : IsElemAbelian 2 (A.subgroupOf R) := hel.subgroupOf R
  have hquad : IsQuadraticOn (actOnMul R) (A.subgroupOf R) :=
    isQuadraticOn_actOnMul (R := R) hq
  have hALc : A.subgroupOf R ⊓
      Subgroup.centralizer ((L.subgroupOf R : Subgroup ↥R) : Set ↥R) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyA, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyA' : (y : LGL 2 V) ∈ A := Subgroup.mem_subgroupOf.mp hyA
    have hycent : ∀ l ∈ L, (y : LGL 2 V) * l = l * (y : LGL 2 V) := by
      intro l hl
      have hmem := (Subgroup.mem_centralizer_iff.mp hyC) (⟨l, c.le hl⟩ : ↥R)
        (Subgroup.mem_subgroupOf.mpr hl)
      exact (congrArg Subtype.val hmem).symm
    have hyN : (y : LGL 2 V) ∈ N := c.cent (y : LGL 2 V) y.2 hycent
    have hmem : (y : LGL 2 V) ∈ A ⊓ N := ⟨hyA', hyN⟩
    rw [isPGroup_inf_odd_eq_bot hel.isPGroup c.odd] at hmem
    exact Subtype.ext (by simpa using hmem)
  have hL_normal : (L.subgroupOf R).Normal := by
    rw [Subgroup.normal_subgroupOf_iff c.le]
    intro h k hh hk
    exact c.normal k hk h hh
  have hAnorm : A.subgroupOf R ≤ Subgroup.normalizer (L.subgroupOf R : Set ↥R) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hL_normal]
    exact le_top
  have hquasi_le_N : quasiCentre L ≤ N := by
    intro z hz
    obtain ⟨hzL, hzc⟩ := mem_quasiCentre.mp hz
    exact c.cent z (c.le hzL) hzc
  have hodd_center_L : Odd (Nat.card ↥(Subgroup.center ↥L)) := by
    have h1 : Odd (Nat.card ↥(quasiCentre L)) :=
      c.odd.of_dvd_nat (Subgroup.card_dvd_of_le hquasi_le_N)
    have h2 : Nat.card ↥(quasiCentre L) = Nat.card ↥(Subgroup.center ↥L) := by
      rw [quasiCentre, Subgroup.card_subtype]
    rwa [h2] at h1
  have hodd_sub : Odd (Nat.card ↥(Subgroup.center ↥(L.subgroupOf R))) := by
    have hmap : (Subgroup.center ↥(L.subgroupOf R)).map
        (Subgroup.subgroupOfEquivOfLe c.le).toMonoidHom = Subgroup.center ↥L :=
      Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe c.le)
    have h2 : Nat.card ↥(Subgroup.center ↥(L.subgroupOf R)) =
        Nat.card ↥(Subgroup.center ↥L) := by
      rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subgroupOfEquivOfLe c.le).injective]
    rw [h2]
    exact hodd_center_L
  have hinner := h65f ↥R (Multiplicative V) w183k3_sq_eq_one (actOnMul R)
    (actOnMul_injective (R := R)) (L.subgroupOf R) (A.subgroupOf R) hcomp hodd_sub hAnorm
    hAcard hel' hquad hALc Y₀ (inferInstance : Group Y₀) (Or.inl hshape) hcov
  intro a ha
  obtain ⟨l, hl, hal⟩ := hinner ⟨a, hAR ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
  refine ⟨(l : LGL 2 V), Subgroup.mem_subgroupOf.mp hl, ?_⟩
  intro x hx
  have hxmem : (⟨x, c.le hx⟩ : ↥R) ∈ L.subgroupOf R := Subgroup.mem_subgroupOf.mpr hx
  have h := (Subgroup.mem_centralizer_iff.mp hal) _ hxmem
  simpa using (congrArg (fun z : ↥R => (z : LGL 2 V)) h).symm

theorem w183k3_inner_of_quadratic (h65f : Asch6_5Four) (c : QuasiCore R L N)
    (hshape : IsL3 (↥L ⧸ Subgroup.center ↥L) 2) {D : Subgroup (LGL 2 V)} (hDR : D ≤ R)
    (hDe : IsElemAbelian 2 D)
    (hDq : CFSG.Quasithin.G11.commSpace D (CFSG.SignalizerFunctorTheorem.Quadratic.commSub D) = ⊥)
    (hD : 3 ≤ mRank D) :
    imgOf (psiQuot R L c.normal) D ≤ innAutOf (↥L ⧸ Subgroup.center ↥L) := by
  classical
  intro x hx
  rw [imgOf, Subgroup.mem_map] at hx
  obtain ⟨d, hd, rfl⟩ := hx
  rw [Subgroup.mem_subgroupOf] at hd
  let dL : LGL 2 V := (d : LGL 2 V)
  by_cases hd1 : dL = 1
  · have hd_eq : d = 1 := Subtype.ext hd1
    rw [hd_eq, map_one]
    exact Subgroup.one_mem _
  · obtain ⟨f, hfD, hfz⟩ : ∃ f ∈ D, f ∉ Subgroup.zpowers dL := by
      have hcardD : 8 ≤ Nat.card D := by
        have hne : Nat.card D ≠ 0 :=
          Nat.card_ne_zero.mpr ⟨⟨1, D.one_mem⟩, inferInstance⟩
        have hlog : 3 ≤ Nat.log 2 (Nat.card D) := by simpa [mRank] using hD
        have hpow : 2 ^ 3 ≤ Nat.card D := Nat.pow_le_of_le_log hne hlog
        simpa using hpow
      have hzple : Subgroup.zpowers dL ≤ D := Subgroup.zpowers_le.mpr hd
      have hcardzp : Nat.card (Subgroup.zpowers dL) = 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (hDe.2 dL hd) hd1
      have hne : Subgroup.zpowers dL ≠ D := by
        intro heq
        rw [heq] at hcardzp
        omega
      exact (SetLike.lt_iff_le_and_exists.mp (lt_of_le_of_ne hzple hne)).2
    let A : Subgroup (LGL 2 V) := Subgroup.closure ({dL, f} : Set (LGL 2 V))
    have hdA : dL ∈ A := Subgroup.subset_closure (by simp)
    have hA_le_D : A ≤ D := (Subgroup.closure_le D).mpr (by
      rintro y (rfl | rfl)
      · exact hd
      · exact hfD)
    have hA_R : A ≤ R := hA_le_D.trans hDR
    have hf1 : f ≠ 1 := fun h =>
      hfz (h ▸ Subgroup.mem_zpowers_iff.mpr ⟨0, zpow_zero dL⟩)
    have hdf : dL ≠ f := fun h =>
      hfz (h ▸ Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one dL⟩)
    have hA_card : Nat.card A = 4 :=
      w183k3_card_closure_pair (d := dL) (f := f)
        (by simpa [pow_two] using hDe.2 dL hd)
        (by simpa [pow_two] using hDe.2 f hfD)
        (hDe.comm hd hfD) hd1 hf1 hdf
    have hA_e : IsElemAbelian 2 A := CFSG.Open.IsElemAbelian.mono hDe hA_le_D
    have hA_q : CFSG.Quasithin.G11.commSpace A
        (CFSG.SignalizerFunctorTheorem.Quadratic.commSub A) = ⊥ := by
      rw [eq_bot_iff]
      calc CFSG.Quasithin.G11.commSpace A
            (CFSG.SignalizerFunctorTheorem.Quadratic.commSub A)
          ≤ CFSG.Quasithin.G11.commSpace D
              (CFSG.SignalizerFunctorTheorem.Quadratic.commSub D) :=
            CFSG.Quasithin.G11.commSpace_mono hA_le_D
              (CFSG.SignalizerFunctorTheorem.Quadratic.commSub_mono A D hA_le_D)
        _ = ⊥ := hDq
    obtain ⟨l, hl, hlc⟩ := w183k3_four_mul_cent h65f c hshape hA_R hA_card hA_e hA_q dL hdA
    have hr_mem : d * (⟨l, c.le hl⟩ : ↥R)⁻¹ ∈ (psiQuot R L c.normal).ker := by
      rw [QuasiCore.mem_ker_psiQuot_iff_centralizes c]
      intro y hy
      have hcoe : (((d * (⟨l, c.le hl⟩ : ↥R)⁻¹ : ↥R)) : LGL 2 V) = dL * l⁻¹ := by
        simp [dL]
      rw [hcoe]
      exact hlc y hy
    have hd_eq : d = (d * (⟨l, c.le hl⟩ : ↥R)⁻¹) * (⟨l, c.le hl⟩ : ↥R) := by
      group
    rw [hd_eq, map_mul, MonoidHom.mem_ker.mp hr_mem, one_mul]
    rw [← QuasiCore.imgOf_psiQuot_L c]
    exact apply_mem_imgOf (psiQuot R L c.normal) hl (c.le hl)

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
