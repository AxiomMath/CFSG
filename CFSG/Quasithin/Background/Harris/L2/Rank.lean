module

public import CFSG.Quasithin.Background.Harris.L2.Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesOuterAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.Harris.Interfaces

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem card_le_of_isPGroup_sl2 {F : Type*} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) (X : Subgroup SL(2, F)) (hX : IsPGroup 2 X) :
    Nat.card X ≤ 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hXP⟩ := hX.exists_le_sylow
  obtain ⟨P₀, hP₀⟩ := upperRootGroup_isSylow (F := F) (p := 2)
  have hPP₀ : Nat.card P = Nat.card P₀ := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hP₀card : Nat.card P₀ = 2 ^ n := by
    rw [show Nat.card P₀ = Nat.card (upperRootGroup F) by rw [← hP₀],
      natCard_upperRootGroup, hF]
  calc Nat.card X ≤ Nat.card P := Subgroup.card_le_of_le hXP
    _ = 2 ^ n := by rw [hPP₀, hP₀card]

@[expose] noncomputable def glvUnits : GLV V ≃* (Module.End (ZMod 2) V)ˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm

theorem repOf_toHomUnits_eq {F : Type*} [Field F] (L : Subgroup (GLV V)) (φ : ↥L ≃* SL(2, F))
    (g : SL(2, F)) : (repOf L φ).toHomUnits g = glvUnits ((φ.symm g : ↥L) : GLV V) := by
  ext v
  rfl

theorem range_repOf_toHomUnits {F : Type*} [Field F] (L : Subgroup (GLV V))
    (φ : ↥L ≃* SL(2, F)) : (repOf L φ).toHomUnits.range = L.map glvUnits.toMonoidHom := by
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(φ.symm g : ↥L), (φ.symm g).2, (repOf_toHomUnits_eq L φ g).symm⟩
  · rintro ⟨l, hl, rfl⟩
    refine ⟨φ ⟨l, hl⟩, ?_⟩
    rw [repOf_toHomUnits_eq, MulEquiv.symm_apply_apply]
    rfl

theorem m_le_of_sl2 [Finite V] {Γ A L : Subgroup (GLV V)} {m : ℕ} (hs : OneCompSetting Γ A L m)
    {n : ℕ} (hn : 2 ≤ n) (φ : ↥L ≃* SL(2, GaloisField 2 n)) : m ≤ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : n ≠ 0 := by omega
  let _inst : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hFnat : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  have hFcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, hFnat]
  set ρ := repOf L φ with hρ
  have hirr : ρ.IsIrreducible := repOf_isIrreducible φ hs.L_irr
  have hinj : Function.Injective ρ.toHomUnits := repOf_toHomUnits_injective L φ
  let A' : Subgroup (Module.End (ZMod 2) V)ˣ := A.map glvUnits.toMonoidHom
  have hAcard : Nat.card A' = 2 ^ m := by
    rw [← hs.A_card]
    exact Nat.card_congr ((A.equivMapOfInjective _ glvUnits.injective).symm.toEquiv)
  have hAea : CFSG.IsElementaryAbelian 2 A' := by
    obtain ⟨hcomm, hsq⟩ := hs.A_elem
    refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨a, ha, hax⟩ := x.2
      obtain ⟨b, hb, hby⟩ := y.2
      apply Subtype.ext
      show (x : (Module.End (ZMod 2) V)ˣ) * y = y * x
      rw [← hax, ← hby, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
      obtain ⟨a, ha, hax⟩ := x.2
      apply Subtype.ext
      show (x : (Module.End (ZMod 2) V)ˣ) ^ 2 = 1
      rw [← hax, ← map_pow, hsq a ha, map_one]
  have hAN : A' ≤ Subgroup.normalizer (ρ.toHomUnits.range : Set (Module.End (ZMod 2) V)ˣ) := by
    rw [range_repOf_toHomUnits]
    rintro _ ⟨a, ha, rfl⟩
    have haΓ : a ∈ Γ := hs.A_le ha
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨a * l * a⁻¹, hs.L_normal a haΓ l hl, ?_⟩
      simp [map_mul, map_inv]
    · rintro ⟨l, hl, hlu⟩
      refine ⟨a⁻¹ * l * a, ?_, ?_⟩
      · have := hs.L_normal a⁻¹ (Γ.inv_mem haΓ) l hl
        simpa using this
      · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv] at hlu ⊢
        rw [hlu]
        group
  by_cases hAL : A' ≤ ρ.toHomUnits.range
  ·
    have hle : A ≤ L := by
      intro a ha
      have h1 : glvUnits a ∈ ρ.toHomUnits.range := hAL ⟨a, ha, rfl⟩
      rw [range_repOf_toHomUnits] at h1
      obtain ⟨l, hl, hla⟩ := h1
      rw [glvUnits.injective hla] at hl
      exact hl
    let X : Subgroup SL(2, GaloisField 2 n) := (A.subgroupOf L).map φ.toMonoidHom
    have hXcard : Nat.card X = 2 ^ m := by
      rw [← hs.A_card]
      have h1 : Nat.card X = Nat.card (A.subgroupOf L) :=
        Nat.card_congr ((A.subgroupOf L).equivMapOfInjective _ φ.injective).symm.toEquiv
      rw [h1]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hXp : IsPGroup 2 X := IsPGroup.of_card (n := m) hXcard
    have := card_le_of_isPGroup_sl2 hFcard X hXp
    rw [hXcard] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  ·
    obtain ⟨s, hs1, hns, hcardA, -⟩ :=
      outer_data (by omega) hFnat ρ hirr hinj A' hAN hAL
    rw [hAcard] at hcardA
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hcardA
    omega

end CFSG.Quasithin.G11.Harris.L2
