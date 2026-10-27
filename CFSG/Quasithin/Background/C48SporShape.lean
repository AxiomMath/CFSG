module

public import CFSG.Quasithin.Background.GoldschmidtS146RCases
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Quasithin.Background.C31Basic
public import CFSG.Quasithin.Background.C48SporCenter
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem card_modO2_dvd_of_isExt {K M₀ : Subgroup G} (hM0K : M₀ ≤ K)
    (hZ : IsPGroup 2 ↥(centerOf K)) {PV PY : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ {A : Type} [Group A] [Finite A], PV A → IsPGroup 2 A)
    (h : IsExt ↥(imageModCenter K M₀) PV PY) :
    ∃ (Y : Type) (_ : Group Y), PY Y ∧ Nat.card (ModO2 M₀) ∣ Nat.card Y := by
  obtain ⟨V, hV, hpv, hpy⟩ := h
  refine ⟨_, _, hpy, ?_⟩
  let φ : ↥M₀ →* ↥(imageModCenter K M₀) :=
    ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (Subgroup.inclusion hM0K)).codRestrict _
      (fun m => Subgroup.mem_map_of_mem _
        (show Subgroup.inclusion hM0K m ∈ M₀.subgroupOf K from m.2))
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨⟨k, hk⟩, hkM, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨k, hkM⟩, rfl⟩
  have hkerφ : IsPGroup 2 ↥φ.ker := by
    rintro ⟨m, hm⟩
    have hm1 : φ m = 1 := hm
    have hm' : (⟨m, hM0K m.2⟩ : ↥K) ∈ Subgroup.center ↥K := by
      have h2 : (QuotientGroup.mk' (Subgroup.center ↥K)) ⟨m, hM0K m.2⟩ = 1 :=
        congrArg Subtype.val hm1
      exact (QuotientGroup.eq_one_iff _).mp h2
    have hmZ : (m : G) ∈ centerOf K := by
      refine ⟨hM0K m.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      have := Subgroup.mem_center_iff.mp hm' ⟨g, hg⟩
      exact congrArg Subtype.val this
    obtain ⟨k, hk⟩ := hZ ⟨_, hmZ⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  set ψ : ↥M₀ →* ↥(imageModCenter K M₀) ⧸ V := (QuotientGroup.mk' V).comp φ with hψ
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective V).comp hφ
  have hVp : IsPGroup 2 ↥V := hPV hpv
  have hkerψ : IsPGroup 2 ↥ψ.ker := by
    rintro ⟨m, hm⟩
    have hmV : φ m ∈ V := by
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hm
      exact hm
    obtain ⟨a, ha⟩ := hVp ⟨_, hmV⟩
    have hφa : φ (m ^ 2 ^ a) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val ha
    obtain ⟨b, hb⟩ := hkerφ ⟨_, hφa⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hle : ψ.ker ≤ CFSG.pCore 2 ↥M₀ := le_sSup ⟨MonoidHom.normal_ker _, hkerψ⟩
  have h1 : Nat.card (ModO2 M₀) ∣ Nat.card (↥M₀ ⧸ ψ.ker) := Subgroup.index_dvd_of_le hle
  rwa [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv] at h1

omit [Finite G] in
theorem isPGroup_of_isE2 {n : ℕ} {A : Type} [Group A] (h : IsE2 n A) : IsPGroup 2 A := by
  obtain ⟨e⟩ := h
  intro x
  refine ⟨1, e.injective ?_⟩
  rw [map_pow, map_one, pow_one]
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  exact (show (2 : ZMod 2) = 0 from rfl) ▸ zero_mul _

theorem card_of_isPSL_two_two_two {Y : Type} [Group Y] (h : IsPSL 2 2 2 Y) : Nat.card Y = 60 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four h

theorem card_of_isAlt_six {Y : Type} [Group Y] (h : IsAlt 6 Y) : Nat.card Y = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  rfl

theorem card_of_isPSU_three_three {Y : Type} [Group Y] (h : IsPSU 3 3 1 Y) : Nat.card Y = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

omit [Finite G] in
theorem isPGroup_of_isZ4Cubed {A : Type} [Group A] (h : IsZ4Cubed A) : IsPGroup 2 A := by
  obtain ⟨e⟩ := h
  intro x
  refine ⟨2, e.injective ?_⟩
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  exact (show ((2 ^ 2 : ℕ) : ZMod 4) = 0 from rfl) ▸ zero_mul _

omit [Finite G] in
theorem isPGroup_of_isSpecial2Group {a b : ℕ} {A : Type} [Group A] [Finite A]
    (h : IsSpecial2Group a b A) : IsPGroup 2 A := by
  obtain ⟨hc, -, ⟨e⟩⟩ := h
  have hq : (Subgroup.center A).index = 2 ^ b := by
    rw [Subgroup.index, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp [ZMod.card]
  have hcard : Nat.card A = 2 ^ (a + b) := by
    rw [← Subgroup.card_mul_index (Subgroup.center A), hc, hq, pow_add]
  exact IsPGroup.of_card hcard

theorem card_modO2_dvd_of_c31Case379 {H R M L V K : Subgroup G} (h31 : C31Basic H R M L V K)
    (hc : C31Case3 H R M L V K ∨ C31Case7 H R M L V K ∨ C31Case9 H R M L V K) :
    Nat.card (ModO2 (conjClosure L M)) ∣ 60 ∨ Nat.card (ModO2 (conjClosure L M)) ∣ 360 ∨
      Nat.card (ModO2 (conjClosure L M)) ∣ 168 ∨ Nat.card (ModO2 (conjClosure L M)) ∣ 6048 := by
  have hM0K := h31.1
  have hZ := h31.2.2
  rcases hc with ⟨-, h1 | h1 | h1⟩ | ⟨-, h1 | h1⟩ | ⟨-, h1 | h1⟩
  · obtain ⟨Y, _, hY, hd⟩ := card_modO2_dvd_of_isExt hM0K hZ (fun h => isPGroup_of_isE2 h) h1
    rw [card_of_isPSL_two_two_two hY] at hd
    exact Or.inl hd
  · obtain ⟨Y, _, hY, hd⟩ := card_modO2_dvd_of_isExt hM0K hZ (fun h => isPGroup_of_isE2 h) h1
    rw [card_of_isAlt_six hY] at hd
    exact Or.inr (Or.inl hd)
  · obtain ⟨Y, _, hY, hd⟩ := card_modO2_dvd_of_isExt hM0K hZ (fun h => isPGroup_of_isE2 h) h1
    rw [GoldS146R.card_of_isPSL_three_two hY] at hd
    exact Or.inr (Or.inr (Or.inl hd))
  · obtain ⟨Y, _, hY, hd⟩ := card_modO2_dvd_of_isExt hM0K hZ (fun h => isPGroup_of_isZ4Cubed h) h1
    rw [GoldS146R.card_of_isPSL_three_two hY] at hd
    exact Or.inr (Or.inr (Or.inl hd))
  · obtain ⟨Y, _, hY, hd⟩ := card_modO2_dvd_of_isExt hM0K hZ (fun h => isPGroup_of_isE2 h) h1
    rw [card_of_isAlt_six hY] at hd
    exact Or.inr (Or.inl hd)
  · obtain ⟨Y, _, hY, hd⟩ := card_modO2_dvd_of_isExt hM0K hZ
      (fun h => isPGroup_of_isSpecial2Group h) h1
    rw [GoldS146R.card_of_isPSL_three_two hY] at hd
    exact Or.inr (Or.inr (Or.inl hd))
  · obtain ⟨Y, _, hY, hd⟩ := card_modO2_dvd_of_isExt hM0K hZ (fun h => isPGroup_of_isE2 h) h1
    rw [card_of_isPSU_three_three hY] at hd
    exact Or.inr (Or.inr (Or.inr hd))

omit [Finite G] in
theorem card_modO2_of_isExcA7Block {L₀ : Subgroup G} (hb : IsExcA7Block L₀) :
    Nat.card (ModO2 L₀) = 2520 := by
  obtain ⟨-, ⟨α, hα, hαk⟩, -⟩ := hb
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv, Nat.card_eq_fintype_card,
    card_alternatingGroup]
  rfl

omit [Finite G] in
theorem card_modO2_of_isHatA6Block [Finite G] {L₀ : Subgroup G} (hb : IsHatA6Block L₀) :
    Nat.card (ModO2 L₀) = 1080 := by
  obtain ⟨-, ⟨-, hc, ⟨e⟩⟩, -, -⟩ := hb
  rw [← Subgroup.card_mul_index (Subgroup.center (ModO2 L₀)), hc, Subgroup.index,
    Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  rfl

theorem dvd_card_of_isSporadic_m24 {X : Type} [Group X] (h : IsSporadic .M24 X) :
    23 ∣ Nat.card X := by
  obtain ⟨e⟩ := h
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have hne : (⟨m24c, m24c_mem⟩ : ↥CFSG.Blueprint.NativeSporadic.M24) ≠ 1 := by
    intro h1
    have := congrArg (fun g : ↥CFSG.Blueprint.NativeSporadic.M24 => (g : Equiv.Perm (Fin 24)) 1) h1
    simp only [OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq] at this
    exact absurd (m24c_fix 1 this) (by decide)
  have hpow : (⟨m24c, m24c_mem⟩ : ↥CFSG.Blueprint.NativeSporadic.M24) ^ 23 = 1 :=
    Subtype.ext (by simpa using m24c_pow)
  have hord := orderOf_eq_prime hpow hne
  rw [Nat.card_congr e.toEquiv, ← hord]
  exact orderOf_dvd_natCard _

theorem card_of_isPSL_four_two {X : Type} [Group X] (h : IsPSL 4 2 1 X) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

theorem card_of_isPSL_five_two {X : Type} [Group X] (h : IsPSL 5 2 1 X) :
    Nat.card X = 9999360 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two h

end CFSG.Quasithin.C48Spor
