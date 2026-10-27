module

public import CFSG.Quasithin.Vol2.GoldschmidtA128Act
public import CFSG.Quasithin.Vol2.GoldschmidtA128LinMain
public import CFSG.RankThree.OddKernel.FrattiniLinear
public import CFSG.Open.FusionDefs
public import CFSG.RankThree.OddKernel.CriticalFixedSpaces

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Vol2.A128

open Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.RankThree.OddKernel CFSG.Open

variable {p : ℕ} [hp : Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
  {P : Subgroup Y} [P.Normal]

@[expose] noncomputable def linAction (D : Subgroup P) [D.Characteristic] {n : ℕ}
    (e : (D ⧸ frattini D) ≃* Multiplicative (Fin n → ZMod p)) (E : Subgroup Y) :
    E →* Module.End (ZMod p) (Fin n → ZMod p) where
  toFun g := coordLin e (action D (g : Y))
  map_one' := by rw [Subgroup.coe_one, map_one, coordLin_one]; rfl
  map_mul' a b := by rw [Subgroup.coe_mul, map_mul, coordLin_mul]; rfl

theorem two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h')

theorem rank_bound_of_setting (hp2 : p ≠ 2) (hP : IsPGroup p P) (hP1 : P ≠ ⊥)
    (hno : ∀ t : Y, t * t = 1 → t ≠ 1 → ∃ x ∈ P, t * x ≠ x * t)
    (hloc : ∀ t : Y, orderOf t = 2 → CFSG.Open.pRank p (centralizer {t} : Subgroup Y) ≤ 2)
    (E : Subgroup Y) (hEsq : ∀ x ∈ E, x * x = 1) (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    Nat.card E ≤ 8 ∧ (Nat.card E = 8 → ∃ a ∈ E, a ≠ 1 ∧
      ∀ y : Y, a * y * a⁻¹ * y⁻¹ ∈ fusionOddCore Y) := by
  have : Nontrivial P := (nontrivial_iff_ne_bot P).2 hP1
  obtain ⟨D, hDc, hD1, hDexp, hDZ, -, hker⟩ := supercritical_witness hp2 hP
  have hDp : IsPGroup p D := hP.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
  have hWp : IsPGroup p (D ⧸ frattini D) := fun x => ⟨1, by rw [pow_one, hWpow]⟩
  obtain ⟨n, hn⟩ := hWp.exists_card_eq
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hn
  have hEsq' : ∀ g : E, g * g = 1 := fun g => Subtype.ext (hEsq g g.2)
  have hEcomm' : ∀ a b : E, a * b = b * a := fun a b => Subtype.ext (hEcomm a a.2 b b.2)
  have hinj : Function.Injective (linAction D e E) := by
    intro a b hab
    have h1 : action D (a : Y) = action D (b : Y) :=
      coordLin_injective e (by simpa [linAction] using hab)
    have h2 : action D ((a : Y)⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : ((a : Y)⁻¹ * b) * ((a : Y)⁻¹ * b) = 1 :=
      hEsq ((a : Y)⁻¹ * b) (E.mul_mem (E.inv_mem a.2) b.2)
    have h4 := involution_eq_one_of_action_eq_one hp2 D hker hno h3 h2
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  have hfix : ∀ g : E, g ≠ 1 →
      Module.finrank (ZMod p) (LinearMap.ker (linAction D e E g -
        (1 : Module.End (ZMod p) (Fin n → ZMod p)))) ≤ 2 := by
    intro g hg
    have hg2 : orderOf (g : Y) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]; exact hEsq g g.2
      · intro h; exact hg (Subtype.ext h)
    have hrank : CFSG.Open.pRank p (D.map P.subtype ⊓ centralizer {(g : Y)} : Subgroup Y) ≤ 2 :=
      (pRank_mono hp.out.one_lt inf_le_right).trans (hloc g hg2)
    have hcard := card_fixed_frattini_quotient_le hp2 hP D hDexp hg2 hrank
    have hpow : p ^ Module.finrank (ZMod p) (fixSpace (coordLin e (action D (g : Y)))) ≤ p ^ 2 := by
      rw [← card_fixed_eq_pow]
      exact hcard
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hpow
  have hbound := elemAbelian_two_bound (two_ne_zero_of_ne_two hp2) hEsq' hEcomm'
    (linAction D e E) hinj hfix
  refine ⟨hbound.1, fun h8 => ?_⟩
  obtain ⟨g, hg⟩ := hbound.2 h8
  have hinv : ∀ w, action D (g : Y) w = w⁻¹ := by
    refine (coordLin_eq_neg_iff e (action D (g : Y))).1 fun v => ?_
    have := LinearMap.congr_fun hg v
    simpa [linAction] using this
  have hg1 : g ≠ 1 := by
    rintro rfl
    have h1 : (1 : Module.End (ZMod p) (Fin n → ZMod p)) = -1 := by
      rw [← hg, map_one]
    rcases subsingleton_or_nontrivial (Fin n → ZMod p) with hs | hnt
    · have hsub : Subsingleton E := ⟨fun a b => hinj (Subsingleton.elim _ _)⟩
      have h1 : Nat.card E = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, inferInstance⟩
      omega
    · obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → ZMod p)
      have h3 := LinearMap.congr_fun h1 v
      simp only [Module.End.one_apply, LinearMap.neg_apply] at h3
      have h4 : (2 : ZMod p) • v = 0 := by
        rw [two_smul]
        nth_rewrite 1 [h3]
        exact neg_add_cancel v
      exact hv ((smul_eq_zero.1 h4).resolve_left (two_ne_zero_of_ne_two hp2))
  have hker_le : (action D).ker ≤ fusionOddCore Y :=
    le_sSup ⟨(action D).normal_ker, odd_card_ker_action hp2 D hker hno⟩
  refine ⟨g, g.2, fun h => hg1 (Subtype.ext h), fun y => hker_le ?_⟩
  rw [MonoidHom.mem_ker]
  have hcent : action D (g : Y) * action D y = action D y * action D (g : Y) := by
    ext w
    simp only [MulAut.mul_apply]
    rw [hinv, hinv, map_inv]
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  calc action D (g : Y) * action D y * (action D (g : Y))⁻¹ * (action D y)⁻¹ =
      action D y * action D (g : Y) * (action D (g : Y))⁻¹ * (action D y)⁻¹ := by rw [hcent]
    _ = 1 := by group

end CFSG.Quasithin.Vol2.A128
