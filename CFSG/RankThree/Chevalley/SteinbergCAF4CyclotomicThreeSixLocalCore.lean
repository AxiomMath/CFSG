module

public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicThreeSixActors
public import CFSG.RankThree.Chevalley.SteinbergCEF4PlaneAssembly
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicLocalCore

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl
  CFSG.LieType.AlgebraicGroups SteinbergBN EvenF4QPlus RootSpace CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical CFSG.LieType.Steinberg.Adjoint
open Subgroup
open scoped Pointwise commutatorElement

theorem F4_three_six_exists_nonregular_of_plane {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {ε : ℤ} {w : WeylGroup Tag.F4}
    (hεw : (ε = 1 ∧ w = f4Coxeter ^ 4 ∧ p ∣ Nat.card K ^ 2 + Nat.card K + 1) ∨
      (ε = -1 ∧ w = f4PhiSix ∧ p ∣ Nat.card K ^ 2 - Nat.card K + 1))
    (E₀ : Subgroup (adjointGroup .F4 K)) (hcard : Nat.card E₀ = p ^ 2)
    (hexp : ∀ x ∈ E₀, x ^ p = 1) :
    ∃ b ∈ E₀, b ≠ 1 ∧ (⁅centralizer ({b} : Set (adjointGroup .F4 K)),
      centralizer ({b} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) ≠ ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hF⟩ := exists_ringHom_pow_card K (AlgebraicClosure K)
  obtain ⟨g, hg, hgn, hc⟩ := exists_lang_torus_coordinates_three_six K (AlgebraicClosure K) F
    hF hεw hp hp3 E₀ (IsPGroup.of_card hcard)
  have hPT : ∀ y ∈ E₀, g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (y : ModGL Tag.F4 K) * g ∈
        torusGroup Tag.F4 (AlgebraicClosure K) ⊓ conjEntrywiseImage K g⁻¹ := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := hc y hy
    rw [hxy, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    exact hx
  let χ : E₀ →* (AlgebraicClosure K)ˣ :=
    { toFun := fun y => Units.mk0 (torusRootChar (g⁻¹ * baseChangeGL
          (algebraMap K (AlgebraicClosure K)) (((y : adjointGroup .F4 K)) : ModGL Tag.F4 K) * g)
            (Pi.single 0 1))
        (torusRootChar_ne_zero (torusGroup_le_diagonalGroup (hPT y y.2).1) _)
      map_one' := by
        apply Units.ext
        simp only [Subgroup.coe_one, map_one, mul_one, inv_mul_cancel, Units.val_mk0,
          Units.val_one]
        exact torusRootChar_one _
      map_mul' := fun a b => by
        apply Units.ext
        simp only [Subgroup.coe_mul, map_mul, Units.val_mk0, Units.val_mul]
        rw [show g⁻¹ * (baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((a : adjointGroup .F4 K) : ModGL Tag.F4 K) *
              baseChangeGL (algebraMap K (AlgebraicClosure K))
                ((b : adjointGroup .F4 K) : ModGL Tag.F4 K)) * g =
            (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((a : adjointGroup .F4 K) : ModGL Tag.F4 K) * g) *
            (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((b : adjointGroup .F4 K) : ModGL Tag.F4 K) * g) by group]
        exact torusRootChar_mul (torusGroup_le_diagonalGroup (hPT a a.2).1)
          (torusGroup_le_diagonalGroup (hPT b b.2).1) _ }
  obtain ⟨a, ha1, hχa⟩ := exists_ne_one_map_eq_one_of_card_sq hp
    (fun a => Subtype.ext (by simpa using hexp a a.2)) hcard χ
  have hχ1 : torusRootChar (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((a : adjointGroup .F4 K) : ModGL Tag.F4 K) * g) (Pi.single 0 1) = 1 := by
    have h1 := congrArg Units.val hχa
    simpa [χ] using h1
  have ha1' : (a : adjointGroup .F4 K) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hap : orderOf (a : adjointGroup .F4 K) = p := orderOf_eq_prime (hexp _ a.2) ha1'
  have hxap : orderOf (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((a : adjointGroup .F4 K) : ModGL Tag.F4 K) * g) = p := by
    have hinj : Function.Injective ((MulAut.conj g⁻¹).toMonoidHom.comp
        ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
          (adjointGroup Tag.F4 K).subtype)) :=
      (MulAut.conj g⁻¹).injective.comp ((baseChangeGL_injective (τ := Tag.F4)
        (algebraMap K (AlgebraicClosure K))).comp Subtype.val_injective)
    have h1 := orderOf_injective _ hinj (a : adjointGroup .F4 K)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      Subgroup.coe_subtype] at h1
    rw [h1, hap]
  obtain ⟨hne, -⟩ := F4_three_six_nonregular_actor K (AlgebraicClosure K) F hℓ hℓ2 hf hK hF hεw hp
    hp3 ⊤ le_top hg hgn (hPT a a.2) hxap ⟨Pi.single 0 1, isRoot_single Tag.F4 0, hχ1⟩
    (x₁ := (a : adjointGroup .F4 K)) (by group)
  exact ⟨a, a.2, ha1', hne⟩

theorem odd_F4_cyclotomic_three_six_all_actors_local_core_product_odd {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1 ∨ p ∣ Nat.card K ^ 2 - Nat.card K + 1)
    (B : Subgroup (MulAut (adjointGroup .F4 K)))
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) (t : B)
    (htE : t ∈ E) (ht1 : t ≠ 1) :
    ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)), E⁆ ⊔ thetaT p E :
        Subgroup B) : Set B) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)), E⁆ : Subgroup B) :
        Set B) * (thetaT p E : Set B) ∧
    Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)), E⁆ ⊔
      thetaT p E : Subgroup B)) ∧
    ((t : MulAut (adjointGroup .F4 K)) ∉
        (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range →
      inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)) = ⊥ ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)), E⁆ ⊔ thetaT p E = ⊥) ∧
    ∀ x : adjointGroup .F4 K, (t : MulAut (adjointGroup .F4 K)) = MulAut.conj x →
      (⁅centralizer ({x} : Set (adjointGroup .F4 K)),
        centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) ≠ ⊥ →
      Odd (Nat.card (inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)))) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Finite (Module.End K (RootModule .F4 K)) := Module.finite_of_finite K
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  obtain ⟨F, hF⟩ := exists_ringHom_pow_card K (AlgebraicClosure K)
  obtain ⟨ε, w, hεw⟩ : ∃ (ε : ℤ) (w : WeylGroup Tag.F4),
      (ε = 1 ∧ w = f4Coxeter ^ 4 ∧ p ∣ Nat.card K ^ 2 + Nat.card K + 1) ∨
        (ε = -1 ∧ w = f4PhiSix ∧ p ∣ Nat.card K ^ 2 - Nat.card K + 1) := by
    rcases hpd with h | h
    exacts [⟨1, _, Or.inl ⟨rfl, rfl, h⟩⟩, ⟨-1, _, Or.inr ⟨rfl, rfl, h⟩⟩]
  have hP : ∀ x : adjointGroup .F4 K, orderOf x = p →
      (⁅centralizer ({x} : Set (adjointGroup .F4 K)),
        centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) ≠ ⊥ →
      Odd (Nat.card (inSubgroup (aschbacherSolvableCore p)
        (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)))) := by
    intro x hxp hPx
    obtain ⟨g, hg, hgn, x', hx', hx'p, hxx'⟩ :=
      exists_lang_coordinate_three_six K (AlgebraicClosure K) F hF hεw hp hp3 hxp
    by_cases hreg : {α | IsRoot Tag.F4 α ∧ torusRootChar x' α = 1} = ∅
    · exact absurd (F4_three_six_regular_actor K (AlgebraicClosure K) F hF hεw hp hp3 hg hgn hx'
        hx'p hreg hxx').2 hPx
    · exact (F4_three_six_nonregular_actor K (AlgebraicClosure K) F hℓ hℓ2 hf hK hF hεw hp hp3 B
        hB hg hgn hx' hx'p (Set.nonempty_iff_ne_empty.2 hreg) hxx').2
  have hreg : ∀ x : adjointGroup .F4 K, orderOf x = p →
      ¬ (⁅centralizer ({x} : Set (adjointGroup .F4 K)),
        centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) ≠ ⊥ →
      Odd (Nat.card (centralizer ({x} : Set (adjointGroup .F4 K)))) := by
    intro x hxp hPx
    obtain ⟨g, hg, hgn, x', hx', hx'p, hxx'⟩ :=
      exists_lang_coordinate_three_six K (AlgebraicClosure K) F hF hεw hp hp3 hxp
    by_cases hreg : {α | IsRoot Tag.F4 α ∧ torusRootChar x' α = 1} = ∅
    · exact (F4_three_six_regular_actor K (AlgebraicClosure K) F hF hεw hp hp3 hg hgn hx' hx'p
        hreg hxx').1
    · exact absurd (F4_three_six_nonregular_actor K (AlgebraicClosure K) F hℓ hℓ2 hf hK hF hεw hp
        hp3 B hB hg hgn hx' hx'p (Set.nonempty_iff_ne_empty.2 hreg) hxx').1 hPx
  obtain ⟨hset, hodd, hnon⟩ := PlaneAssembly.plane_local_core_product_odd hinj
    (fun a b => by
      rw [← commutatorElement_def]
      exact F4_commutator_mem_range_conj K a b) hp hp2 hB
    (fun α hα hαp => by
      rw [inSubgroup, F4_localCore_eq_bot_of_noninner K hp hp3 B hB α hα hαp, Subgroup.map_bot])
    (fun x => (⁅centralizer ({x} : Set (adjointGroup .F4 K)),
      centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) ≠ ⊥)
    hP hreg
    (fun E₀ hcard hexp => F4_three_six_exists_nonregular_of_plane hℓ hℓ2 hf K hK hp hp3 hεw E₀
      hcard hexp)
    E hE hEcard htE ht1
  refine ⟨hset, hodd, hnon, fun x htx hRne => ?_⟩
  have htb : t = ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ := Subtype.ext htx
  have hxp : orderOf x = p := by
    rw [← orderOf_injective _ hinj x, ← Subgroup.orderOf_mk (MulAut.conj x) (hB ⟨x, rfl⟩), ← htb]
    exact orderOf_eq_prime (by
      have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E) ⟨t, htE⟩
      simpa using congrArg Subtype.val h) ht1
  rw [htb]
  exact hP x hxp hRne

end CFSG.RankThree.Chevalley
