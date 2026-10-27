module

public import CFSG.RankThree.PartOne.S10.PlaneSemidirect
import CFSG.RankThree.GroupTheory.SteinbergBKSpecialTwoExtraspecialQuotients
import CFSG.RankThree.GroupTheory.SteinbergBKSmallSylowTwoCommutatorOdd
import CFSG.LocalAnalysis.ComponentInitial.GroupComponents

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.GroupTheory.SteinbergBK
open scoped commutatorElement

namespace PlaneFactorCases

variable {B S : Type} [Group B] [Group S] [MulDistribMulAction B S]

@[expose, reducible] def invAction (X : Subgroup S) (hX : IsActionInvariant B X) :
    MulDistribMulAction B X :=
  MulDistribMulAction.compHom X
    (PlaneSemidirect.restrictHom (MulDistribMulAction.toMulAut B S) X hX)

theorem invAction_smul_coe (X : Subgroup S) (hX : IsActionInvariant B X) (b : B) (x : X) :
    (((invAction X hX).smul b x : X) : S) = b • (x : S) := rfl

structure SpecialData (X Z : Subgroup S) (n : ℕ) : Prop where
  le : Z ≤ X
  ne_bot : Z ≠ ⊥
  elementary : IsElementaryAbelian 2 Z
  fixed : ActionCentralizes B Z
  commutator_eq : ⁅X, X⁆ = Z
  sq_mem : ∀ x ∈ X, x ^ 2 ∈ Z
  central : ∀ z ∈ Z, ∀ y ∈ X, z * y = y * z
  center_le : ∀ x ∈ X, (∀ y ∈ X, x * y = y * x) → x ∈ Z
  card_center : Nat.card (Subgroup.center X) = Nat.card Z
  two_le : 2 ≤ n
  card_eq : Nat.card X = Nat.card Z * 2 ^ (2 * n)
  quotient : ∀ (Z₀ : Subgroup X) [Z₀.Normal], Z₀ ≤ Subgroup.center X →
    Nat.card (Subgroup.center X) = 2 * Nat.card Z₀ →
    IsExtraspecialPGroup 2 (X ⧸ Z₀) ∧ Nat.card (X ⧸ Z₀) = 2 ^ (1 + 2 * n)
  four_group : ∃ E : Subgroup S, E ≤ X ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4

theorem exists_smul_eq_of_sup_eq_top {X : Subgroup S} (hXinv : IsActionInvariant B X)
    {Bi Bj : Subgroup B} (hBi : ∀ c : B, c ∈ Bi ↔ ∀ s ∈ X, c • s = s) (hsup : Bi ⊔ Bj = ⊤)
    (hcommB : ∀ x y : B, x * y = y * x) :
    ∀ b : B, ∃ b₂ ∈ Bj, ∀ s ∈ X, b • s = b₂ • s := by
  intro b
  have hb : b ∈ (↑(Bi ⊔ Bj) : Set B) := by rw [hsup]; exact Subgroup.mem_top b
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Bi Bj (fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun g => by
      simp [hcommB x g])] at hb
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hb
  refine ⟨b₂, hb₂, fun s hs => ?_⟩
  rw [mul_smul]
  exact (hBi b₁).mp hb₁ _ (hXinv b₂ s hs)

theorem special_factor_package [Finite S] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hS : IsPGroup 2 S) {X : Subgroup S} (hX : MinimalPlaneFactor B X)
    (hnel : ¬ IsElementaryAbelian 2 X) {Bi Bj : Subgroup B} (hBjc : Nat.card Bj = p)
    (hBi : ∀ c : B, c ∈ Bi ↔ ∀ s ∈ X, c • s = s) (hsup : Bi ⊔ Bj = ⊤)
    (hcommB : ∀ x y : B, x * y = y * x) :
    ∃ n : ℕ, SpecialData (B := B) X (inSubgroup Subgroup.center X) n := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hXinv, hXc, hXmin, hnt, hirr, hel | hsp⟩ := hX
  · exact absurd hel hnel
  obtain ⟨hcommXX, hfrcen, hfrne, hfrel, hfrfix⟩ := hsp
  set Z := inSubgroup Subgroup.center X with hZ
  have hZmem : ∀ x : X, x ∈ Subgroup.center X ↔ (x : S) ∈ Z := fun x =>
    ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, hyx⟩ => by
      have : y = x := Subtype.ext hyx
      exact this ▸ hy⟩
  have hdec := exists_smul_eq_of_sup_eq_top hXinv hBi hsup hcommB
  let := invAction X hXinv
  let actBj : MulDistribMulAction Bj X :=
    MulDistribMulAction.compHom X ((MulDistribMulAction.toMulAut B X).comp Bj.subtype)
  have hsmulBj : ∀ (a : Bj) (x : X), ((a • x : X) : S) = (a : B) • (x : S) := fun _ _ => rfl
  have hP2 : IsPGroup 2 X := hS.to_subgroup X
  have hfrne' : inSubgroup frattini X ≠ ⊥ := hfrne
  have hmapinj := Subgroup.map_injective (f := X.subtype) X.subtype_injective
  have hcommP : commutator X = Subgroup.center X := by
    apply hmapinj
    show (commutator X).map X.subtype = (Subgroup.center X).map X.subtype
    rw [Subgroup.map_subtype_commutator, hcommXX]
    exact hfrcen
  have hfrP : frattini X = Subgroup.center X := by
    apply hmapinj
    exact hfrcen
  have hnab : ∃ x y : X, x * y ≠ y * x := by
    by_contra h
    push Not at h
    apply hfrne
    rw [← hcommXX, eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩))
  have hZel : ∀ z ∈ Subgroup.center X, z ^ 2 = 1 := by
    intro z hz
    have hzf : (z : S) ∈ inSubgroup frattini X := by rw [hfrcen]; exact (hZmem z).mp hz
    have := hfrel
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : S) hzf)
  have hAZ : ∀ a : Bj, ∀ z ∈ Subgroup.center X, a • z = z := by
    intro a z hz
    have hzf : (z : S) ∈ inSubgroup frattini X := by rw [hfrcen]; exact (hZmem z).mp hz
    exact Subtype.ext (hfrfix a z hzf)
  have hnontriv : ∃ a : Bj, ∃ x : X, x⁻¹ * (a • x) ∉ Subgroup.center X := by
    obtain ⟨b, s, hs, hns⟩ := hnt
    obtain ⟨b₂, hb₂, hbs⟩ := hdec b
    refine ⟨⟨b₂, hb₂⟩, ⟨s, hs⟩, fun hmem => hns ?_⟩
    have h1 : s⁻¹ * (b₂ • s) ∈ inSubgroup frattini X := by
      rw [hfrcen]
      exact (hZmem _).mp hmem
    rw [hbs s hs]
    have h2 := (inSubgroup frattini X).inv_mem h1
    simpa [mul_inv_rev] using h2
  have hirrP : ∀ W : Subgroup X, Subgroup.center X ≤ W → (∀ a : Bj, ∀ w ∈ W, a • w ∈ W) →
      W = Subgroup.center X ∨ W = ⊤ := by
    intro W hW hWinv
    have hY : ∀ b : B, ∀ y ∈ W.map X.subtype, b • y ∈ W.map X.subtype := by
      rintro b _ ⟨w, hw, rfl⟩
      obtain ⟨b₂, hb₂, hbs⟩ := hdec b
      rw [show X.subtype w = (w : S) from rfl, hbs w w.2]
      exact ⟨(⟨b₂, hb₂⟩ : Bj) • w, hWinv _ w hw, rfl⟩
    have hfrY : inSubgroup frattini X ≤ W.map X.subtype := by
      rw [hfrcen]
      exact Subgroup.map_mono hW
    rcases hirr (W.map X.subtype) hfrY (Subgroup.map_subtype_le W) hY with h | h
    · left
      apply hmapinj
      exact h.trans hfrcen
    · right
      apply hmapinj
      rw [h, Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨n, hn2, hidx, hquot, E, hE, hEcard⟩ :=
    special_two_irreducible_odd_action_extraspecial_central_quotients
      hp hp3 (P := X) (A := Bj) hP2 hnab hcommP hfrP hZel (isCyclic_of_prime_card hBjc) hBjc hAZ
      hnontriv hirrP
  have hXpg : Fact (IsPGroup 2 X) := ⟨hP2⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨n, ?_⟩
  have hcardZ : Nat.card Z = Nat.card (Subgroup.center X) :=
    Subgroup.card_map_of_injective X.subtype_injective
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_, ?_, hcommXX.trans hfrcen, ?_, ?_, ?_, hcardZ.symm, hn2,
    ?_, hquot, ?_⟩
  · show Z ≠ ⊥
    rw [← hfrcen]
    exact hfrne
  · show IsElementaryAbelian 2 Z
    rw [← hfrcen]
    exact hfrel
  · show ActionCentralizes B Z
    rw [← hfrcen]
    exact hfrfix
  · intro x hx
    have h1 : (⟨x, hx⟩ : X) ^ 2 ∈ frattini X :=
      pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x, hx⟩ : X)
    rw [hfrP] at h1
    exact (hZmem _).mp h1
  · rintro _ ⟨z, hz, rfl⟩ y hy
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨y, hy⟩ : X))).symm
  · intro x hx h
    exact (hZmem (⟨x, hx⟩ : X)).mp (Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (h y y.2).symm)
  · have h1 := Subgroup.card_mul_index (Subgroup.center X)
    rw [hidx] at h1
    rw [← h1]
    rw [hcardZ]
  · refine ⟨E.map X.subtype, Subgroup.map_subtype_le E, ?_, ?_⟩
    · have := isElemAbelian_iff_isElementaryAbelian.mp hE
      exact IsElementaryAbelian.map_subtype (H := E)
    · rw [Subgroup.card_map_of_injective X.subtype_injective, hEcard]

theorem elementary_factor_data [Finite B] [Finite S] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {X : Subgroup S} (hX : MinimalPlaneFactor B X) (hel : IsElementaryAbelian 2 X)
    {Bi Bj : Subgroup B} (hBjc : Nat.card Bj = p) (hBi : ∀ c : B, c ∈ Bi ↔ ∀ s ∈ X, c • s = s)
    (hsup : Bi ⊔ Bj = ⊤) (hcommB : ∀ x y : B, x * y = y * x) :
    5 ≤ Nat.card X ∧ ∀ J : Subgroup S, J ≤ X → ActionCentralizes B J → J = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hXinv, hXc, hXmin, hnt, hirr, -⟩ := hX
  have hdec := exists_smul_eq_of_sup_eq_top hXinv hBi hsup hcommB
  have hfrbot : inSubgroup frattini X = ⊥ := by
    have := hel
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact (IsPGroup 2 X) := ⟨IsElementaryAbelian.isPGroup 2 X⟩
    have h : frattini X = ⊥ := frattini_eq_bot_of_isElementaryAbelian (p := 2)
    simp only [inSubgroup, h, Subgroup.map_bot]
  have hmove : ∃ a : Bj, ∃ x ∈ X, (a : B) • x ≠ x := by
    obtain ⟨b, s, hs, hns⟩ := hnt
    obtain ⟨b₂, hb₂, hbs⟩ := hdec b
    refine ⟨⟨b₂, hb₂⟩, s, hs, fun h => hns ?_⟩
    rw [hbs s hs, h, inv_mul_cancel]
    exact one_mem _
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have hpS : Nat.card X ≤ p := by omega
    let act : MulDistribMulAction Bj S :=
      MulDistribMulAction.compHom S ((MulDistribMulAction.toMulAut B S).comp Bj.subtype)
    have hBjp : IsPGroup p Bj := IsPGroup.of_card (n := 1) (by rw [hBjc, pow_one])
    have hfix := smul_eq_self_of_card_le_prime hp hBjp X
      (fun a x hx => hXinv a x hx) hpS
    obtain ⟨a, x, hx, hax⟩ := hmove
    exact hax (hfix a x hx)
  · intro J hJX hJfix
    rcases hirr J (hfrbot ▸ bot_le) hJX (fun b y hy => by rw [hJfix b y hy]; exact hy) with h | h
    · rw [h, hfrbot]
    · exfalso
      obtain ⟨a, x, hx, hax⟩ := hmove
      exact hax (hJfix a x (h ▸ hx))

end PlaneFactorCases

end CFSG.RankThree.PartOne
