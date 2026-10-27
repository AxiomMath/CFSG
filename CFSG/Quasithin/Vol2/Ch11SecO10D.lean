module

public import CFSG.Quasithin.Vol2.Ch11SecO10B
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Quasithin CFSG.LieType.Universal.Spin Matrix
open CFSG.QuasithinUnique (IsSylowTwoOf)

section Upper

variable (F : Type*) [Field F]

@[expose] noncomputable def upperSub : Subgroup (SpecialLinearGroup (Fin 2) F) where
  carrier := Set.range upperSL2
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, upperSL2_add a b⟩
  one_mem' := ⟨0, upperSL2_zero⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨-a, ?_⟩
    rw [eq_inv_iff_mul_eq_one, ← upperSL2_add, neg_add_cancel, upperSL2_zero]

variable {F}

theorem upperSL2_injective : Function.Injective (upperSL2 (K := F)) := by
  intro a b h
  have := congrArg (fun N : SpecialLinearGroup (Fin 2) F => (N : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa using this

theorem card_upperSub [Finite F] : Nat.card (upperSub F) = Nat.card F := by
  change Nat.card (Set.range upperSL2) = _
  exact Nat.card_range_of_injective upperSL2_injective

theorem isPGroup_upperSub [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    IsPGroup 2 (upperSub F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (card_upperSub.trans hF)

theorem not_two_dvd_index_upperSub [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) :
    ¬ 2 ∣ (upperSub F).index := by
  have h1 := (upperSub F).card_mul_index
  rw [card_upperSub, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF] at h1
  have hpos : 0 < 2 ^ n := by positivity
  have hidx : (upperSub F).index = (2 ^ n) ^ 2 - 1 := Nat.eq_of_mul_eq_mul_left hpos h1
  rw [hidx]
  have hpos2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ hpos
  obtain ⟨c, hc⟩ : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
  omega

end Upper

theorem isSylowTwoOf_of_le_of_le {Y : Type*} [Group Y] {P C A : Subgroup Y}
    (hP : IsSylowTwoOf P A) (hPC : P ≤ C) (hCA : C ≤ A) : IsSylowTwoOf P C := by
  refine ⟨hPC, hP.2.1, fun hdvd => hP.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex P C A hPC hCA
  have h2 : 2 ∣ P.relIndex A := by rw [← h1]; exact Dvd.dvd.mul_right hdvd _
  exact h2

theorem exists_conj_le_of_two {Y : Type*} [Group Y] [Finite Y] {P S : Subgroup Y}
    (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) (hS : IsPGroup 2 S) :
    ∃ g : Y, ∀ s ∈ S, g * s * g⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P' : Sylow 2 Y := hP.toSylow hidx
  obtain ⟨Q, hQ⟩ := hS.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q P'
  refine ⟨g, fun s hs => ?_⟩
  have hs' : s ∈ (Q : Subgroup Y) := hQ hs
  have h1 : g * s * g⁻¹ ∈ ((g • Q : Sylow 2 Y) : Subgroup Y) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hs'
  rw [hg] at h1
  exact h1

theorem false_of_sl2 {Y : Type*} [Group Y] [Finite Y] {F : Type*} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) {H P B Z₀ : Subgroup Y}
    (hP : IsSylowTwoOf P H) (hBH : B ≤ H) (hPB : P ≤ Subgroup.normalizer (B : Set Y))
    (θ : ↥B ≃* SpecialLinearGroup (Fin 2) F) (hC : P ⊓ Subgroup.centralizer (B : Set Y) = ⊥)
    (hZP : Z₀ ≤ P) (hZc : ∀ z ∈ Z₀, ∀ p ∈ P, z * p = p * z) (hZq : 2 ^ n ≤ Nat.card Z₀)
    (hPq : 2 ^ n < Nat.card P) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPB' : IsSylowTwoOf P (B ⊔ P) :=
    isSylowTwoOf_of_le_of_le hP le_sup_right (sup_le hBH hP.1)
  have hD : IsSylowTwoOf (P ⊓ B) B :=
    A4.isSylowTwoOf_inf_normal hPB' le_sup_left (sup_le Subgroup.le_normalizer hPB)
  set S : Subgroup ↥B := (P ⊓ B).subgroupOf B with hSdef
  set S' : Subgroup (SpecialLinearGroup (Fin 2) F) := S.map θ.toMonoidHom with hS'def
  have eS : ↥S ≃* ↥(P ⊓ B) := Subgroup.subgroupOfEquivOfLe inf_le_right
  have eS' : ↥S ≃* ↥S' := S.equivMapOfInjective θ.toMonoidHom θ.injective
  have hS2 : IsPGroup 2 S := hD.2.1.of_equiv eS.symm
  have hS'2 : IsPGroup 2 S' := hS2.of_equiv eS'
  have hS'idx : ¬ 2 ∣ S'.index := by
    rw [hS'def, Subgroup.index_map_of_bijective θ.bijective]
    exact hD.2.2
  have hmemS : ∀ x ∈ S', ((θ.symm x : ↥B) : Y) ∈ P ⊓ B := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact Subgroup.mem_subgroupOf.mp hb
  obtain ⟨g, hg⟩ := exists_conj_le_of_two hS'2 hS'idx (isPGroup_upperSub hF)
  obtain ⟨g', hg'⟩ := exists_conj_le_of_two (isPGroup_upperSub hF)
    (not_two_dvd_index_upperSub hn hF) hS'2
  have hcardD : Nat.card ↥(P ⊓ B) ≤ 2 ^ n := by
    have h1 : S'.map (MulAut.conj g').toMonoidHom ≤ upperSub F := by
      rintro _ ⟨x, hx, rfl⟩
      exact hg' x hx
    calc Nat.card ↥(P ⊓ B) = Nat.card ↥S' := (Nat.card_congr eS.toEquiv).symm.trans
          (Nat.card_congr eS'.toEquiv)
      _ = Nat.card ↥(S'.map (MulAut.conj g').toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj g').injective).symm
      _ ≤ Nat.card ↥(upperSub F) := Subgroup.card_le_of_le h1
      _ = 2 ^ n := card_upperSub.trans hF
  have key : ∀ a ∈ P, (∀ d ∈ P ⊓ B, a * d = d * a) → a ∈ P ⊓ B := by
    intro a ha hcomm
    have haB : ∀ b ∈ B, a * b * a⁻¹ ∈ B := fun b hb =>
      (Subgroup.mem_normalizer_iff.mp (hPB ha) b).mp hb
    have haB' : ∀ b ∈ B, a⁻¹ * b * a⁻¹⁻¹ ∈ B := fun b hb =>
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hPB ha)) b).mp hb
    let αa : ↥B ≃* ↥B :=
      { toFun := fun b => ⟨a * b * a⁻¹, haB b b.2⟩
        invFun := fun b => ⟨a⁻¹ * b * a⁻¹⁻¹, haB' b b.2⟩
        left_inv := fun b => Subtype.ext (by simp [mul_assoc])
        right_inv := fun b => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun b c => Subtype.ext (by simp [mul_assoc]) }
    have hαa : ∀ b : ↥B, ((αa b : ↥B) : Y) = a * b * a⁻¹ := fun _ => rfl
    let β : MulAut (SpecialLinearGroup (Fin 2) F) :=
      ((((MulAut.conj g).trans θ.symm).trans αa).trans θ).trans (MulAut.conj g⁻¹)
    have hβ : ∀ y, β y = g⁻¹ * θ (αa (θ.symm (g * y * g⁻¹))) * g := fun y => by
      simp [β, MulAut.conj_apply]
    have hfix : ∀ c : F, β (upperSL2 c) = upperSL2 c := by
      intro c
      have hx := hg _ ⟨c, rfl⟩
      have hd := hmemS _ hx
      have h1 : αa (θ.symm (g * upperSL2 c * g⁻¹)) = θ.symm (g * upperSL2 c * g⁻¹) := by
        apply Subtype.ext
        rw [hαa, hcomm _ hd, mul_assoc, mul_inv_cancel, mul_one]
      rw [hβ, h1, MulEquiv.apply_symm_apply]
      group
    obtain ⟨s, hs⟩ := exists_conj_of_fix_upper β hfix
    set x₀ := g * upperSL2 s * g⁻¹ with hx₀
    have hx₀S : x₀ ∈ S' := hg _ ⟨s, rfl⟩
    set e : ↥B := θ.symm x₀ with he
    have heD : (e : Y) ∈ P ⊓ B := hmemS x₀ hx₀S
    have hconj : ∀ b : ↥B, a * b * a⁻¹ = e * b * e⁻¹ := by
      intro b
      have h1 := hs (g⁻¹ * θ b * g)
      rw [hβ, show g * (g⁻¹ * θ b * g) * g⁻¹ = θ b by group, MulEquiv.symm_apply_apply] at h1
      have h2 : θ (αa b) = θ (e * b * e⁻¹) := by
        rw [map_mul, map_mul, map_inv, he, MulEquiv.apply_symm_apply, hx₀]
        calc θ (αa b) = g * (g⁻¹ * θ (αa b) * g) * g⁻¹ := by group
          _ = _ := by rw [h1]; group
      have h3 := congrArg (fun z : ↥B => (z : Y)) (θ.injective h2)
      simpa [hαa] using h3
    have hcent : (e : Y)⁻¹ * a ∈ P ⊓ Subgroup.centralizer (B : Set Y) := by
      refine ⟨P.mul_mem (P.inv_mem heD.1) ha, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
      have h1 := hconj ⟨b, hb⟩
      simp only [InvMemClass.coe_inv] at h1
      calc b * ((e : Y)⁻¹ * a) = (e : Y)⁻¹ * ((e : Y) * b * (e : Y)⁻¹) * a := by group
        _ = (e : Y)⁻¹ * (a * b * a⁻¹) * a := by rw [h1]
        _ = (e : Y)⁻¹ * a * b := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcent
    rw [← hcent]
    exact heD
  have hZD : Z₀ ≤ P ⊓ B := fun z hz =>
    key z (hZP hz) fun d hd => hZc z hz d hd.1
  have hZeq : Z₀ = P ⊓ B := Subgroup.eq_of_le_of_card_ge hZD (hcardD.trans hZq)
  have hPD : P ≤ P ⊓ B := fun p hp =>
    key p hp fun d hd => by rw [← hZeq] at hd; exact (hZc d hd p hp).symm
  have := Subgroup.card_le_of_le hPD
  omega

end CFSG.Quasithin.Vol2.Ch11.O10
