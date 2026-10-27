module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Setup
import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofSL2
import CFSG.GroupTheory.PrimeOrderSubgroups
import CFSG.CGT.PushingUpLit.CGT6K1.InnerEven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (DerInf8)

namespace R891D4Setup

variable {X : Type} [Group X] [Finite X] {n : ℕ} {S B : Subgroup X}

private lemma r891_three_ne_zero_of_card_two_pow {F : Type} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) : (3 : F) ≠ 0 := by
  have : CharP F 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  rw [show (3 : F) = 1 + (2 : F) by ring, CharTwo.two_eq_zero, add_zero]
  exact one_ne_zero

private lemma r891_conj_zpow_three_of_mulEquiv {H F : Type} [Group H] [Finite H] [Field F]
    [Finite F] (h3 : (3 : F) ≠ 0) (e : H ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    {u v : H} (hu : u ^ 3 = 1) (hu1 : u ≠ 1) (hv : v ^ 3 = 1) (hv1 : v ≠ 1) :
    ∃ k : H, k * u * k⁻¹ = v := by
  have heu3 : e u ^ 3 = 1 := by rw [← map_pow, hu, map_one]
  have heu1 : e u ≠ 1 := fun h => hu1 (e.injective (h.trans (map_one e).symm))
  have hev3 : e v ^ 3 = 1 := by rw [← map_pow, hv, map_one]
  have hev1 : e v ≠ 1 := fun h => hv1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨A, hA⟩ :=
    CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof.exists_conj_of_pow_three
      h3 heu3 heu1 hev3 hev1
  refine ⟨e.symm A, ?_⟩
  apply e.injective
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hA

private lemma r891_conj_of_order_three_in_subgroup {H : Subgroup X} {F : Type} [Field F]
    [Finite F] (h3 : (3 : F) ≠ 0) (e : ↥H ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    {x y : X} (hx : x ∈ H) (hy : y ∈ H) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) : ∃ k ∈ H, k * x * k⁻¹ = y := by
  let xH : ↥H := ⟨x, hx⟩
  let yH : ↥H := ⟨y, hy⟩
  have hxH3 : xH ^ 3 = 1 := by ext; simpa [xH] using hx3
  have hxH1 : xH ≠ 1 := fun h => hx1 (by simpa [xH] using congrArg Subtype.val h)
  have hyH3 : yH ^ 3 = 1 := by ext; simpa [yH] using hy3
  have hyH1 : yH ≠ 1 := fun h => hy1 (by simpa [yH] using congrArg Subtype.val h)
  obtain ⟨kH, hk⟩ := r891_conj_zpow_three_of_mulEquiv h3 e hxH3 hxH1 hyH3 hyH1
  refine ⟨kH, kH.2, ?_⟩
  have h := congrArg (fun z : ↥H => (z : X)) hk
  simpa [xH, yH] using h

private lemma r891_conj_generator_into_B (h : R891D4Setup n S B) {P : Subgroup X} {s : X}
    (hs : s ∈ S) (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) (hZ : ZOf P = zpowers s)
    {A : Subgroup X} (hA : ∀ g : X, A.map (MulAut.conj g).toMonoidHom ≠ ZOf P) {a : X}
    (haord : orderOf a = 3) (hAa : A = zpowers a) :
    ∃ (g t : X), t ∈ B ∧ t ^ 3 = 1 ∧ t ≠ 1 ∧ a = g⁻¹ * t * g := by
  have ha3 : a ^ 3 = 1 := by rw [← haord]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at haord
    omega
  obtain ⟨g, hg | hg⟩ := h.conj a ha3 ha1
  · obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := h.sl2S
    let := hKfield
    let := hKfin
    have hKcard' : Nat.card K = 2 ^ (3 * n) := by
      rw [hKcard, ← pow_mul, mul_comm]
    have h3K : (3 : K) ≠ 0 := r891_three_ne_zero_of_card_two_pow hKcard'
    have hga3 : (g * a * g⁻¹) ^ 3 = 1 := by
      rw [show g * a * g⁻¹ = (MulAut.conj g) a by simp [MulAut.conj_apply]]
      rw [← map_pow, ha3, map_one]
    have hga1 : g * a * g⁻¹ ≠ 1 := by
      intro h1
      have h2 : (MulAut.conj g) a = 1 := by simpa [MulAut.conj_apply] using h1
      exact ha1 ((MulAut.conj g).injective (by simpa using h2))
    obtain ⟨k, _, hk⟩ :=
      r891_conj_of_order_three_in_subgroup h3K e hg hs hga3 hga1 hs3 hs1
    exfalso
    apply hA (k * g)
    have hconj : k * (g * a * g⁻¹) * k⁻¹ = s := hk
    rw [hAa, MonoidHom.map_zpowers, hZ]
    exact congrArg Subgroup.zpowers (by simpa [MulAut.conj_apply] using hconj)
  · refine ⟨g, g * a * g⁻¹, hg, ?_, ?_, ?_⟩
    · rw [show g * a * g⁻¹ = (MulAut.conj g) a by simp [MulAut.conj_apply]]
      rw [← map_pow, ha3, map_one]
    · intro h1
      have h2 : (MulAut.conj g) a = 1 := by simpa [MulAut.conj_apply] using h1
      exact ha1 ((MulAut.conj g).injective (by simpa using h2))
    · group

theorem class_clauses (h : R891D4Setup n S B) {P : Subgroup X} {s : X} (hs : s ∈ S)
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) (hZ : ZOf P = zpowers s) {A : Subgroup X}
    (hA3 : Nat.card A = 3) (hA : ∀ g : X, A.map (MulAut.conj g).toMonoidHom ≠ ZOf P) :
    LieModel ↥(DerInf8 ((⊤ : Subgroup X) ⊓ centralizer (A : Set X))) .PSL 2 2 (3 * n) ∧
      R891CentShape ↥(centralizer (A : Set X)) n := by
  obtain ⟨a, _, haord, hAa⟩ :=
    CFSG.GroupTheory.exists_generator_of_card_prime Nat.prime_three hA3
  have hn : 1 ≤ n := h.one_le
  obtain ⟨g, t, ht, ht3, ht1, ha_reg⟩ :=
    r891_conj_generator_into_B h hs hs3 hs1 hZ hA haord hAa
  have htS : t ∈ centralizer (S : Set X) := h.cent ▸ ht
  have hScent : S ≤ centralizer ({t} : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp htS x hx
  have hcentA : centralizer (A : Set X) =
      (centralizer ({t} : Set X)).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hAa, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, ha_reg]
    simpa using
      (CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton (G := X) g⁻¹ t).symm
  have hder : DerInf8 ((⊤ : Subgroup X) ⊓ centralizer (A : Set X)) =
      DerInf8 (centralizer (A : Set X)) := by rw [top_inf_eq]
  let e1 : ↥(centralizer (A : Set X)) ≃* ↥(centralizer ({t} : Set X)) :=
    (MulEquiv.subgroupCongr hcentA).trans
      (Subgroup.equivMapOfInjective (centralizer ({t} : Set X))
        (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm
  obtain ⟨e2⟩ := nonempty_derInf8_mulEquiv e1
  rw [h.derInf8_centralizer_eq ht ht3 ht1] at e2
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨eS⟩⟩ := h.sl2S
  let := hKfield
  let := hKfin
  let : Fintype K := Fintype.ofFinite K
  have hKFcard : Fintype.card K = 2 ^ (3 * n) := by
    rw [← Nat.card_eq_fintype_card, hKcard, ← pow_mul, mul_comm]
  let e3 : ↥(DerInf8 (centralizer (A : Set X))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K := e2.trans eS
  have hLie : LieModel ↥(DerInf8 (centralizer (A : Set X))) .PSL 2 2 (3 * n) :=
    CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two
      (by omega) hKFcard e3
  have hSmap_le : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (A : Set X) := by
    intro x hx
    obtain ⟨y, hyS, rfl⟩ := Subgroup.mem_map.mp hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hAa, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff, ha_reg]
    have hy : y * t = t * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hScent hyS)
    calc (g⁻¹ * y * g) * (g⁻¹ * t * g)
        = g⁻¹ * (y * t) * g := by group
      _ = g⁻¹ * (t * y) * g := by rw [hy]
      _ = (g⁻¹ * t * g) * (g⁻¹ * y * g) := by group
  let C : Subgroup X := centralizer (A : Set X)
  let U : Subgroup C := (S.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf C
  refine ⟨?_, ?_⟩
  · rw [hder]
    exact hLie
  · refine ⟨U, ?_, ?_⟩
    · have hUeq : U = (S.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf C := rfl
      rw [hUeq]
      let eU : ↥((S.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf C) ≃*
          Matrix.SpecialLinearGroup (Fin 2) K :=
        (Subgroup.subgroupOfEquivOfLe hSmap_le).trans
          ((Subgroup.equivMapOfInjective S (MulAut.conj g⁻¹).toMonoidHom
            (MulAut.conj g⁻¹).injective).symm.trans eS)
      exact CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two
        (by omega) hKFcard eU
    · intro c1 c2
      have hc1 : (c1 : X) ∈ (centralizer ({t} : Set X)).map
          (MulAut.conj g⁻¹).toMonoidHom := by
        rw [← hcentA]
        exact c1.2
      have hc2 : (c2 : X) ∈ (centralizer ({t} : Set X)).map
          (MulAut.conj g⁻¹).toMonoidHom := by
        rw [← hcentA]
        exact c2.2
      obtain ⟨d1, hd1, hd1eq⟩ := Subgroup.mem_map.mp hc1
      obtain ⟨d2, hd2, hd2eq⟩ := Subgroup.mem_map.mp hc2
      have hcommS : d1 * d2 * d1⁻¹ * d2⁻¹ ∈ S :=
        h.bcomm t ht ht3 ht1 d1 hd1 d2 hd2
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_map.2 ⟨d1 * d2 * d1⁻¹ * d2⁻¹, hcommS, ?_⟩
      have hd1' : g⁻¹ * d1 * g = (c1 : X) := by
        simpa [MulAut.conj_apply] using hd1eq
      have hd2' : g⁻¹ * d2 * g = (c2 : X) := by
        simpa [MulAut.conj_apply] using hd2eq
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hd1', ← hd2']
      group

end R891D4Setup

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
