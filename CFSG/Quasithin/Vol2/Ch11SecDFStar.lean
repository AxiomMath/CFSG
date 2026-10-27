module

public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11SecABasicV

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem pCore_two_quotient_eq_bot (H : Type*) [Group H] [Finite H] :
    CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 H with hN
  set M := (CFSG.pCore 2 (H ⧸ N)).comap (QuotientGroup.mk' N) with hM
  have hMp : IsPGroup 2 M :=
    (CFSG.pCore_isPGroup (p := 2) (G := H ⧸ N)).comap_of_ker_isPGroup _
      (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup (p := 2) (G := H))
  have hMn : M.Normal := (CFSG.pCore_normal (p := 2) (G := H ⧸ N)).comap _
  have hMN : M ≤ N := (CFSG.LieType.BorelTits.le_pCore 2 hMn hMp).trans_eq (SecA.open_pCore_eq 2 H)
  rw [eq_bot_iff]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H x =>
    have hx : x ∈ M := hq
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact hMN hx

theorem normal_map_of_characteristic {H : Type*} [Group H] {N : Subgroup H} (hN : N.Normal)
    {C : Subgroup ↥N} (hC : C.Characteristic) : (C.map N.subtype).Normal := by
  constructor
  rintro _ ⟨c, hc, rfl⟩ h
  let φ : ↥N ≃* ↥N :=
    { toFun := fun a => ⟨h * a * h⁻¹, hN.conj_mem a a.2 h⟩
      invFun := fun a => ⟨h⁻¹ * a * h, by simpa using hN.conj_mem a a.2 h⁻¹⟩
      left_inv := fun a => Subtype.ext (by simp [mul_assoc])
      right_inv := fun a => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hφ : C.map φ.toMonoidHom = C := Subgroup.characteristic_iff_map_eq.mp hC φ
  have hφc : φ c ∈ C := by
    rw [← hφ]
    exact ⟨c, hc, rfl⟩
  exact ⟨φ c, hφc, rfl⟩

theorem odd_card_of_isNilpotent_of_normal {H : Type*} [Group H] [Finite H]
    (hO2 : CFSG.pCore 2 H = ⊥) {N : Subgroup H} (hN : N.Normal) (hnil : Group.IsNilpotent ↥N) :
    Odd (Nat.card N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥N))
  have q := (Group.isNilpotent_of_finite_tfae (G := ↥N)).out 1 4
  have hPn : (P : Subgroup ↥N).Normal := q.mp hnil 2 inferInstance P
  have hPc : (P : Subgroup ↥N).Characteristic := Sylow.characteristic_of_normal P hPn
  have hmapn := normal_map_of_characteristic hN hPc
  have hmap2 : IsPGroup 2 ((P : Subgroup ↥N).map N.subtype) := P.isPGroup'.map _
  have hle : (P : Subgroup ↥N).map N.subtype ≤ CFSG.pCore 2 H :=
    (CFSG.LieType.BorelTits.le_pCore 2 hmapn hmap2).trans_eq (SecA.open_pCore_eq 2 H)
  rw [hO2, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at hle
  exact P.ne_bot_of_dvd_card h2 hle

theorem mulAut_eq_one_of_fixes_generalizedFitting {H : Type*} [Group H] [Finite H]
    (hO2 : CFSG.pCore 2 H = ⊥) (φ : MulAut H) {k : ℕ} (hk : φ ^ 2 ^ k = 1)
    (hfix : ∀ x ∈ CFSG.generalizedFitting H, φ x = x) : φ = 1 := by
  set F := CFSG.generalizedFitting H with hFdef
  have hFn : F.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := H)).2
  set Z := F ⊓ Subgroup.centralizer (F : Set H) with hZdef
  have hZn : Z.Normal := by
    have := hFn
    have : (Subgroup.centralizer (F : Set H)).Normal := Subgroup.normal_centralizer
    exact Subgroup.normal_inf_normal _ _
  have hZab : Group.IsNilpotent ↥Z := by
    have : IsMulCommutative ↥Z := ⟨⟨fun a b => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1)⟩⟩
    infer_instance
  have hZodd := odd_card_of_isNilpotent_of_normal hO2 hZn hZab
  apply CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_fixed_displacement Z φ
    (2 ^ k) hk (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hZodd))
    (fun z hz => hfix z hz.1)
  intro x
  have hC : x⁻¹ * φ x ∈ Subgroup.centralizer (F : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hconj : x * f * x⁻¹ ∈ F := hFn.conj_mem f hf x
    have heq := hfix (x * f * x⁻¹) hconj
    rw [map_mul, map_mul, map_inv, hfix f hf] at heq
    have hcomm := congrArg (fun y : H => x⁻¹ * y * φ x) heq
    calc f * (x⁻¹ * φ x) = x⁻¹ * (x * f * x⁻¹) * φ x := by group
      _ = x⁻¹ * (φ x * f * (φ x)⁻¹) * φ x := hcomm.symm
      _ = (x⁻¹ * φ x) * f := by group
  exact ⟨CFSG.centralizer_generalizedFitting_le H hC, hC⟩

end CFSG.Quasithin.Vol2.Ch11.SecD
