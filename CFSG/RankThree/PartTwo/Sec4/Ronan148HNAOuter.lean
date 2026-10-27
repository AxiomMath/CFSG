module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LNA

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut isInnerAut_congr)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)

@[expose] def OuterCubeE27 (S : Type) [Group S] : Prop :=
  ∀ τ : MulAut S, τ ^ 3 = 1 → ¬ IsInnerAut τ →
    ∃ E : Subgroup S, Late.IsE27 E ∧ ∀ x ∈ E, τ x = x

theorem OuterCubeE27.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : OuterCubeE27 Y) : OuterCubeE27 X := by
  intro τ hτ hout
  obtain ⟨E, hE, hfix⟩ := h (MulAut.congr e τ) (by rw [← map_pow, hτ, map_one])
    (fun h' => hout ((isInnerAut_congr e τ).mp h'))
  refine ⟨E.map e.symm.toMonoidHom, ⟨isElemAbelian_map _ hE.1, by
    rw [Subgroup.card_map_of_injective e.symm.injective, hE.2]⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h1 : e (τ (e.symm y)) = y := hfix y hy
  change τ (e.symm y) = e.symm y
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  exact h1

section Core

variable {G : Type} [Group G] [Finite G]

theorem conj_injective_of_center_eq_bot {L : Subgroup G} (hZ : Subgroup.center L = ⊥) :
    Function.Injective (MulAut.conj : L →* MulAut L) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : x ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h : x * g * x⁻¹ = g := congrArg (fun τ : MulAut L => τ g) hx
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  rw [hZ, Subgroup.mem_bot] at hx'
  exact hx'

theorem false_of_e27_centralized (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3)
    {E : Subgroup G} (hE : Late.IsE27 E) {a : G} (ha3 : a ^ 3 = 1) (haE : a ∉ E)
    (hc : ∀ x ∈ E, a * x = x * a) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha1 : a ≠ 1 := fun h => haE (h ▸ E.one_mem)
  have hW : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers a) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers ha3
  have hWc : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hc' : ∀ x ∈ E, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute x a from (hc x hx).symm) k).eq
  have hinf : E ⊓ Subgroup.zpowers a = ⊥ := by
    have hd : Nat.card (E ⊓ Subgroup.zpowers a : Subgroup G) ∣ 3 :=
      hWc ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : E ⊓ Subgroup.zpowers a = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hWc])
      have hmem : a ∈ E ⊓ Subgroup.zpowers a := by
        rw [heq]
        exact Subgroup.mem_zpowers a
      exact haE (Subgroup.mem_inf.mp hmem).1
  have hB := CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hE.1 hW hc'
  have hBc := Ronan148R.card_sup_of_commute_of_inf hc' hinf
  rw [hE.2, hWc] at hBc
  have hle := card_le_of_pRank_le hrk hB
  rw [hBc] at hle
  norm_num at hle

theorem le_of_outerCubeE27 {S : Type} [Group S] {L A : Subgroup G} (φ : L ≃* S)
    (hZ : Subgroup.center L = ⊥) (hout : OuterCubeE27 S)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hC : ∀ w ∈ Subgroup.centralizer (L : Set G), w ^ 3 = 1 → w = 1) : A ≤ L := by
  intro a ha
  have ha3 : a ^ 3 = 1 := hA.2 a ha
  obtain ⟨τ, hτdef⟩ : ∃ τ : MulAut L,
      τ = L.normalizerMonoidHom (⟨a, hAN ha⟩ : Subgroup.normalizer (L : Set G)) := ⟨_, rfl⟩
  have hτ : ∀ l : L, ((τ l : L) : G) = a * l * a⁻¹ := fun l => by subst hτdef; rfl
  have hτ3 : τ ^ 3 = 1 := by
    have ha3' : (⟨a, hAN ha⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [hτdef, ← map_pow, ha3', map_one]
  by_cases hin : IsInnerAut τ
  · obtain ⟨y, hy⟩ := hin
    have hy3 : y ^ 3 = 1 := by
      refine (map_eq_one_iff _ (conj_injective_of_center_eq_bot hZ)).mp ?_
      rw [map_pow, hy, hτ3]
    have hrep : ∀ l ∈ L, a * l * a⁻¹ = (y : G) * l * (y : G)⁻¹ := by
      intro l hl
      have h1 : ((MulAut.conj y ⟨l, hl⟩ : L) : G) = ((τ ⟨l, hl⟩ : L) : G) := by rw [hy]
      rw [hτ] at h1
      exact h1.symm
    have hwC : (y : G)⁻¹ * a ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := hrep l hl
      calc l * ((y : G)⁻¹ * a) = (y : G)⁻¹ * ((y : G) * l * (y : G)⁻¹) * a := by group
        _ = (y : G)⁻¹ * (a * l * a⁻¹) * a := by rw [h1]
        _ = (y : G)⁻¹ * a * l := by group
    have hcomm : a * (y : G) = (y : G) * a := by
      have h1 := hrep y y.2
      calc a * (y : G) = a * y * a⁻¹ * a := by group
        _ = y * y * (y : G)⁻¹ * a := by rw [h1]
        _ = y * a := by group
    have hy3' : (y : G) ^ 3 = 1 := by
      have h := congrArg Subtype.val hy3
      simpa using h
    have hw3 : ((y : G)⁻¹ * a) ^ 3 = 1 := by
      have hc : Commute (y : G)⁻¹ a := Commute.inv_left (show Commute (y : G) a from hcomm.symm)
      rw [hc.mul_pow, inv_pow, hy3', ha3, inv_one, one_mul]
    have hw1 := hC _ hwC hw3
    have : a = y := by
      calc a = y * ((y : G)⁻¹ * a) := by group
        _ = y := by rw [hw1, mul_one]
    rw [this]
    exact y.2
  · exfalso
    obtain ⟨E, hE, hfix⟩ := hout (MulAut.congr φ τ) (by rw [← map_pow, hτ3, map_one])
      (fun h' => hin ((isInnerAut_congr φ τ).mp h'))
    set E' : Subgroup G := (E.map φ.symm.toMonoidHom).map L.subtype with hE'def
    have hE'L : E' ≤ L := Subgroup.map_subtype_le _
    have hE' : Late.IsE27 E' := ⟨isElemAbelian_map _ (isElemAbelian_map _ hE.1), by
      rw [hE'def, Subgroup.card_map_of_injective L.subtype_injective,
        Subgroup.card_map_of_injective φ.symm.injective, hE.2]⟩
    have hfix' : ∀ x ∈ E', a * x = x * a := by
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have h1 : φ (τ (φ.symm z)) = z := hfix z hz
      have h2 : τ (φ.symm z) = φ.symm z := by
        apply φ.injective
        rw [MulEquiv.apply_symm_apply]
        exact h1
      have h3 : a * (φ.symm z : G) * a⁻¹ = (φ.symm z : G) := by
        rw [← hτ, h2]
      change a * (φ.symm z : G) = (φ.symm z : G) * a
      calc a * (φ.symm z : G) = a * (φ.symm z : G) * a⁻¹ * a := by group
        _ = (φ.symm z : G) * a := by rw [h3]
    have haE' : a ∉ E' := by
      intro haE
      apply hin
      refine ⟨⟨a, hE'L haE⟩, ?_⟩
      ext l
      change a * (l : G) * a⁻¹ = ((τ l : L) : G)
      rw [hτ]
    exact false_of_e27_centralized hrk hE' ha3 haE' hfix'

end Core

section Row

theorem row425_of_e27Move_outer {S : Type} [Group S] (h3 : NoThreeCover S)
    (hout : OuterCubeE27 S) (hE : ∃ E : Subgroup S, Late.IsE27 E)
    (hmove : Ronan148L.E27Move S) : Row425 S := by
  intro G _ _ _ A hA hrk hθ L hL ⟨eL⟩ c hLc K _ K' hK' _ hAZ hN
  exfalso
  have hcmem : c ∈ A ⊓ (K' ⊓ Subgroup.centralizer (K' : Set G)) :=
    hAZ ▸ Subgroup.mem_zpowers c
  have hcA : c ∈ A := hcmem.1
  have hK'L : K' ≤ L := (hK' ▸ Subgroup.map_subtype_le K).trans inf_le_left
  have hcL : c ∈ L := hK'L hcmem.2.1
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hLc fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
  have hZ : Subgroup.center L = ⊥ := Ronan148L.center_eq_bot_of_noThreeCover h3 hθ hL eL
  let φ : L ≃* S := (RonanK429.quotCenterEquivOfEqBot hZ).trans eL
  have hAc : ∀ a ∈ A, a * c = c * a := fun a ha =>
    congrArg Subtype.val (hA.1.1.is_comm.comm (⟨a, ha⟩ : A) ⟨c, hcA⟩)
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rcases CFSG.LocalCores.distinct_components_commute
        (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj a) hL) hL with h | h
    · exact h
    · exfalso
      have hcLa : c ∈ L.map (MulAut.conj a).toMonoidHom := by
        refine ⟨c, hcL, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hAc a ha, mul_inv_cancel_right]
      have hcC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hcLa
      exact hLc fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcC x hx)
  have hLE : ∃ E : Subgroup G, E ≤ L ∧ Late.IsE27 E := by
    obtain ⟨E, hE⟩ := hE
    refine ⟨(E.map φ.symm.toMonoidHom).map L.subtype, Subgroup.map_subtype_le _,
      isElemAbelian_map _ (isElemAbelian_map _ hE.1), ?_⟩
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective φ.symm.injective, hE.2]
  obtain ⟨E, hEL, hEe⟩ := hLE
  have hLC : ∀ x ∈ L, x ∈ Subgroup.centralizer (L : Set G) → x = 1 := by
    intro x hxL hxC
    have hmem : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hAL : A ≤ L := le_of_outerCubeE27 φ hZ hout hrk.le hAN hA.1
    fun w hw hw3 => Ronan148L.eq_one_of_mem_centralizer_of_rank hrk.le hLC hEL hEe hw hw3
  exact Ronan148L.not_normalizer_le_of_e27Move φ hmove hAL hA hcA hc1 hN

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148H
