module

public import CFSG.Quasithin.Vol2.Ch3Sec3KGSylow
public import CFSG.Quasithin.Vol2.KGFactHeSylow
public import CFSG.Quasithin.H13.KGFact68Base
public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.LieType.SteinbergBRBinaryLinearSylow
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.Quasithin.H13.KGAutSyl

open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.SteinbergBR.OddSylow CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem mem_inner_of_pow_eq_one_of_isPGroup {G : Type*} [Group G]
    (hout : IsPGroup 2 (Outer G)) {α : MulAut G} {m : ℕ} (hm : Odd m) (hα : α ^ m = 1) :
    α ∈ inner G := by
  have h1 : (QuotientGroup.mk' (inner G) α) ^ m = 1 := by rw [← map_pow, hα, map_one]
  obtain ⟨k, hk⟩ := hout (QuotientGroup.mk' (inner G) α)
  have h2 := orderOf_dvd_of_pow_eq_one hk
  have h3 := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have h4 : orderOf (QuotientGroup.mk' (inner G) α) = 1 :=
    (Nat.Coprime.coprime_dvd_left h2 hcop).eq_one_of_dvd h3
  have h5 := orderOf_eq_one_iff.mp h4
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h5

theorem normalizer_inf_le_of_isPGroup_outer {G : Type*} [Group G] [Finite G]
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hsn : ∀ P : Subgroup G, IsSylowTwoOf P ⊤ → Subgroup.normalizer (P : Set G) ≤ P)
    (hout : IsPGroup 2 (Outer G)) {A S : Subgroup (MulAut G)}
    (hA : (MulAut.conj : G →* MulAut G).range ≤ A) (hS : IsSylowTwoOf S A) :
    Subgroup.normalizer (S : Set (MulAut G)) ⊓ A ≤ S := by
  have : Finite (MulAut G) :=
    Finite.of_injective (fun e : MulAut G => (e : G → G)) fun _ _ h => MulEquiv.ext (congrFun h)
  intro x hx
  obtain ⟨hxN, hxA⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hb : ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m + (m : ℤ) * Nat.gcdB (2 ^ a) m = 1 := by
    have := Nat.gcd_eq_gcd_ab (2 ^ a) m
    rw [hcop.gcd_eq_one] at this
    exact_mod_cast this.symm
  have hxn : x ^ (2 ^ a * m) = 1 := hn ▸ pow_orderOf_eq_one x
  set y := (x ^ (2 ^ a)) ^ Nat.gcdA (2 ^ a) m with hy
  set z := (x ^ m) ^ Nat.gcdB (2 ^ a) m with hz
  have hxyz : x = y * z := by
    rw [hy, hz, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, hb, zpow_one]
  have hz2 : z ^ 2 ^ a = 1 := by
    rw [hz, KGHe.zpow_pow_comm', ← pow_mul, mul_comm, hxn, one_zpow]
  have hym : y ^ m = 1 := by
    rw [hy, KGHe.zpow_pow_comm', ← pow_mul, hxn, one_zpow]
  have hzS : z ∈ S := KGHe.mem_of_mem_normalizer_of_pow hS (A.zpow_mem (A.pow_mem hxA _) _)
    (Subgroup.zpow_mem _ (Subgroup.pow_mem _ hxN _) _) hz2
  have hyN : y ∈ Subgroup.normalizer (S : Set (MulAut G)) :=
    Subgroup.zpow_mem _ (Subgroup.pow_mem _ hxN _) _
  have hyI : y ∈ inner G := mem_inner_of_pow_eq_one_of_isPGroup hout hm hym
  have hSI : IsSylowTwoOf (S ⊓ inner G) (inner G) :=
    A4.isSylowTwoOf_inf_normal hS hA (fun g _ => Subgroup.mem_normalizer_iff.mpr fun h =>
      ⟨fun hh => (inner_normal G).conj_mem h hh g, fun hh => by
        have := (inner_normal G).conj_mem _ hh g⁻¹
        simpa [mul_assoc] using this⟩)
  have hyNI : y ∈ Subgroup.normalizer ((S ⊓ inner G : Subgroup (MulAut G)) : Set (MulAut G)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp hyN h]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (inner_normal G).conj_mem h h2 y⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := (inner_normal G).conj_mem _ h2 y⁻¹
      simpa [mul_assoc] using this
  have hyS : y ∈ S :=
    (Subgroup.mem_inf.mp (KGHe.mem_of_mem_normalizer_inner hinj hsn hSI hyI hyNI)).1
  rw [hxyz]
  exact S.mul_mem hyS hzS

theorem selfNormalizing_of_exists {G : Type*} [Group G] [Finite G]
    (hex : ∃ P₀ : Sylow 2 G, Subgroup.normalizer (P₀ : Set G) = P₀) (P : Subgroup G)
    (hP : IsSylowTwoOf P ⊤) : Subgroup.normalizer (P : Set G) ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := hex
  have hidx : ¬ 2 ∣ P.index := by
    have h := hP.2.2
    rwa [show (P.subgroupOf ⊤).index = P.relIndex ⊤ from rfl, Subgroup.relIndex_top_right] at h
  have h1 := normalizer_eq_of_one P₀ hP₀ (hP.2.1.toSylow hidx)
  rw [IsPGroup.toSylow_coe] at h1
  exact h1.le

theorem autSylowSelfNorm_of {Q : Type} [Group Q] [Finite Q] (hZ : Subgroup.center Q = ⊥)
    (hex : ∃ P₀ : Sylow 2 Q, Subgroup.normalizer (P₀ : Set Q) = P₀)
    (hout : IsPGroup 2 (Outer Q)) : AutSylowSelfNorm Q := fun _ _ hA hS =>
  normalizer_inf_le_of_isPGroup_outer (KG68.conj_injective_of_center hZ)
    (selfNormalizing_of_exists hex) hout hA hS

theorem isPGroup_outer_of_dvd_two {G : Type*} [Group G] (h : Nat.card (Outer G) ∣ 2) :
    IsPGroup 2 (Outer G) := by
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · exact IsPGroup.of_card (n := 0) (by rw [h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [h2, pow_one])

theorem autSylowSelfNorm_psl_two {n : ℕ} (hn : 3 ≤ n) {Q : Type} [Group Q] [Finite Q]
    (h : IsPSL n 2 1 Q) : AutSylowSelfNorm Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center Q = ⊥ := CFSG.Quasithin.F420.center_eq_bot_of_statedPSL h
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  let e : Q ≃* projectiveSL n K := e₀.trans (Id2519.projectiveSLEquivStatedProj n K).symm
  obtain ⟨⟨P₀, hP₀⟩, -⟩ := CFSG.LieType.SteinbergBR.BinaryLinear.binary_linear_key hn hK2
  refine autSylowSelfNorm_of hZ (exists_selfNormalizing_of_equiv e P₀ hP₀)
    (isPGroup_outer_of_dvd_two ?_)
  rw [card_outer_congr e]
  have h1 := CFSG.RankThree.Automorphisms.higher_linear_outer_order_divides_field_scalar_bound
    (K := K) (ℓ := 2) (f := 1) Nat.prime_two le_rfl hn (by rw [hK2, pow_one])
  norm_num at h1
  exact h1

theorem factAutSylowL42_holds : FactAutSylowL42 := fun _ _ _ h =>
  autSylowSelfNorm_psl_two (by norm_num) h

theorem factAutSylowL52_holds : FactAutSylowL52 := fun _ _ _ h =>
  autSylowSelfNorm_psl_two (by norm_num) h

theorem center_eq_bot_of_equiv_alt {Q : Type} [Group Q] {n : ℕ} (hn : 4 ≤ n)
    (e : Q ≃* alternatingGroup (Fin n)) : Subgroup.center Q = ⊥ := by
  have h4 : 4 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn
  have hZn : Subgroup.center (alternatingGroup (Fin n)) = ⊥ := alternatingGroup.center_eq_bot h4
  rw [eq_bot_iff]
  intro x hx
  have h1 : e x ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  rw [hZn, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [h1, map_one])

theorem autSylowSelfNorm_of_equiv_alt6 {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* alternatingGroup (Fin 6)) : AutSylowSelfNorm Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.SteinbergBR.SmallAlt.exists_selfNormalizing_six
  have : Finite (MulAut (alternatingGroup (Fin 6))) :=
    Finite.of_injective (fun f : MulAut (alternatingGroup (Fin 6)) => (f : _ → _))
      DFunLike.coe_injective
  obtain ⟨m, hm⟩ := CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six.exists_card_eq
  exact autSylowSelfNorm_of (center_eq_bot_of_equiv_alt (by norm_num) e)
    (exists_selfNormalizing_of_equiv e P₀ hP₀)
    (IsPGroup.of_card (n := m) (by rw [card_outer_congr e, hm]))

theorem factAutSylowA7_holds : FactAutSylowA7 := by
  intro Q _ _ hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hQ
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.SteinbergBR.SmallAlt.exists_selfNormalizing_seven
  refine autSylowSelfNorm_of (center_eq_bot_of_equiv_alt (by norm_num) e)
    (exists_selfNormalizing_of_equiv e P₀ hP₀) (isPGroup_outer_of_dvd_two ?_)
  rw [card_outer_congr e]
  exact CFSG.Quasithin.SteinbergCB.index_inner_dvd_two (n := 7) (Or.inr (by norm_num))

end CFSG.Quasithin.H13.KGAutSyl
