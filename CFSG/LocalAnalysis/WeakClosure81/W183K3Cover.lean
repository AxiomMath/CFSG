module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Leaves
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Inner

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {R L N : Subgroup (LGL 2 V)}

private theorem w183K3Cover_finite_lgl : Finite (LGL 2 V) :=
  Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
    (fun e f h => LinearEquiv.ext (congrFun h))

private theorem w183K3Cover_isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : CFSG.Open.IsQuasisimple B) : CFSG.Open.IsQuasisimple A := by
  have : Group.IsPerfect B := ⟨h.1⟩
  have : IsSimpleGroup (B ⧸ Subgroup.center B) := h.2
  have hperfect : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨hperfect.commutator_eq_top,
    (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
      (Subgroup.map_center_eq e)).isSimpleGroup⟩

private theorem w183K3Cover_sq_eq_one (v : Multiplicative V) : v ^ 2 = 1 := by
  have h : (v ^ 2).toAdd = 0 := by
    rw [toAdd_pow, two_nsmul, ZModModule.add_self]
  calc v ^ 2 = Multiplicative.ofAdd (v ^ 2).toAdd := (ofAdd_toAdd _).symm
    _ = Multiplicative.ofAdd 0 := by rw [h]
    _ = 1 := rfl

theorem br3_cover_core (h65o : Asch6_5Odd) (c : QuasiCore R L N)
    (hshape : ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ (LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 p 1 ∨
      LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 p 1))
    {A : Subgroup (LGL 2 V)} (hAR : A ≤ R) (hcard : Nat.card ↥A = 4) (hel : IsElemAbelian 2 A)
    (hq : CFSG.Quasithin.G11.commSpace A (CFSG.SignalizerFunctorTheorem.Quadratic.commSub A) = ⊥) :
    False := by
  classical
  haveI : Finite (LGL 2 V) := w183K3Cover_finite_lgl
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
      w183K3Cover_isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe c.le) c.quasi⟩
  have hcov : CFSG.LocalAnalysis.UniquenessCase.UC22.CoverOf ↥(L.subgroupOf R) Y₀ := by
    refine ⟨w183K3Cover_isQuasisimple_of_mulEquiv
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
  rcases hshape with ⟨p, hp, hp5, hmodel⟩
  have hp2 : p ≠ 2 := by omega
  have h3p : 3 < p ^ 1 := by
    rw [pow_one]
    omega
  have hY : (Odd 1 ∧ LieModel Y₀ .PSL 3 p 1) ∨ LieModel Y₀ .PSU 3 p 1 := by
    rcases hmodel with h | h
    · exact Or.inl ⟨odd_one, h⟩
    · exact Or.inr h
  exact h65o ↥R (Multiplicative V) w183K3Cover_sq_eq_one (actOnMul R)
    (actOnMul_injective (R := R)) (L.subgroupOf R) (A.subgroupOf R) hcomp hodd_sub hAnorm
    hAcard hel' hquad hALc p 1 Y₀ (inferInstance : Group Y₀) hp hp2 h3p hY hcov

theorem br3CoverOne_holds : Br3CoverOne := by
  intro rows V _ _ _ Y T L Γ VA i h hc hshape hmem
  obtain ⟨A₀, hA₀, h4⟩ := hmem
  have hA₀Y : A₀ ≤ Y := h.le_G A₀ hA₀
  have hel : IsElemAbelian 2 A₀ := h.isElemAb A₀ hA₀
  have hq : CFSG.Quasithin.G11.commSpace A₀
      (CFSG.SignalizerFunctorTheorem.Quadratic.commSub A₀) = ⊥ := h.quadratic A₀ hA₀
  obtain ⟨B, _, hBcard⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card
    (p := 2) (n := 2) Nat.prime_two hel.isPGroup (H := ⊤) (by simpa using h4)
  let A : Subgroup (LGL 2 V) := B.map A₀.subtype
  have hAA₀ : A ≤ A₀ := Subgroup.map_subtype_le B
  have hAY : A ≤ Y := hAA₀.trans hA₀Y
  have hAcard : Nat.card ↥A = 4 := by
    rw [show A = B.map A₀.subtype from rfl, Subgroup.card_subtype, hBcard]
    norm_num
  have helA : IsElemAbelian 2 A := hel.mono hAA₀
  have hqA : CFSG.Quasithin.G11.commSpace A
      (CFSG.SignalizerFunctorTheorem.Quadratic.commSub A) = ⊥ :=
    le_bot_iff.mp ((CFSG.Quasithin.G11.commSpace_mono hAA₀
      (CFSG.SignalizerFunctorTheorem.Quadratic.commSub_mono A A₀ hAA₀)).trans (le_of_eq hq))
  exact br3_cover_core rows.h65o hc hshape hAY hAcard helA hqA

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
