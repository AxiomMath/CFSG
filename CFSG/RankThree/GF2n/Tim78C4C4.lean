module

public import CFSG.RankThree.GF2n.Tim78P210Basic

public section

namespace CFSG.RankThree.GF2n.Tim78

variable {G : Type*} [Group G] [Finite G]

theorem mulEquiv_C4_C4 {B : Subgroup G} (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hexp : ∀ x ∈ B, x ^ 4 = 1) (h4 : Nat.card ↥(PartTwo.omegaOneSub B) = 4)
    (hrel : (PartTwo.omegaOneSub B).relIndex B = 4) :
    Nonempty (↥B ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  classical
  have hB16 : Nat.card B = 16 := by
    have h1 := Subgroup.relIndex_mul_card (PartTwo.omegaOneSub B) B
    rw [inf_of_le_left (PartTwo.omegaOneSub_le B), hrel, h4] at h1
    omega
  have hsq : ∀ x ∈ B, x * x ∈ PartTwo.omegaOneSub B := fun x hx =>
    (mem_omegaOneSub_iff hBc).mpr ⟨B.mul_mem hx hx, by
      calc x * x * (x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := hexp x hx⟩
  let sqh : ↥B →* ↥(PartTwo.omegaOneSub B) :=
    { toFun := fun x => ⟨(x : G) * x, hsq x x.2⟩
      map_one' := Subtype.ext (by
        show ((1 : ↥B) : G) * ((1 : ↥B) : G) = 1
        simp)
      map_mul' := fun a b => Subtype.ext (by
        show ((a * b : ↥B) : G) * ((a * b : ↥B) : G) = ((a : G) * a) * ((b : G) * b)
        rw [Subgroup.coe_mul]
        have hab := hBc _ a.2 _ b.2
        calc (a : G) * b * ((a : G) * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hab]
          _ = (a : G) * a * ((b : G) * b) := by group) }
  have hker : sqh.ker = (PartTwo.omegaOneSub B).subgroupOf B := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_omegaOneSub_iff hBc]
    constructor
    · intro h
      exact ⟨x.2, congrArg Subtype.val h⟩
    · intro h
      exact Subtype.ext h.2
  have hrange : sqh.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [← Subgroup.index_ker, hker, ← Subgroup.relIndex, hrel, h4]
  have hne : PartTwo.omegaOneSub B ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at h4
    omega
  obtain ⟨⟨z₁, hz₁⟩, hz₁1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz₁1 : z₁ ≠ 1 := fun h => hz₁1' (Subtype.ext h)
  obtain ⟨z₂, hz₂, hz₂1, hz₂z₁⟩ : ∃ z₂ ∈ PartTwo.omegaOneSub B, z₂ ≠ 1 ∧ z₂ ≠ z₁ := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hinj : Function.Injective
        (fun z : ↥(PartTwo.omegaOneSub B) => decide ((z : G) = 1)) := by
      intro z z' h
      by_cases hz : (z : G) = 1
      · have hz' : (z' : G) = 1 := by simpa [hz] using h
        exact Subtype.ext (hz.trans hz'.symm)
      · have hz' : (z' : G) ≠ 1 := by simpa [hz] using h
        exact Subtype.ext ((hcon _ z.2 hz).trans (hcon _ z'.2 hz').symm)
    have := Nat.card_le_card_of_injective _ hinj
    rw [h4, Nat.card_eq_fintype_card, Fintype.card_bool] at this
    omega
  have hsq1 : ∀ z ∈ PartTwo.omegaOneSub B, z * z = 1 := fun z hz =>
    ((mem_omegaOneSub_iff hBc).mp hz).2
  have hz₁₂ : z₁ * z₂ ≠ 1 := fun h => hz₂z₁ (by
    calc z₂ = z₁ * (z₁ * z₂) := by rw [← mul_assoc, hsq1 z₁ hz₁, one_mul]
      _ = z₁ := by rw [h, mul_one])
  obtain ⟨u₁, hu₁⟩ : (⟨z₁, hz₁⟩ : ↥(PartTwo.omegaOneSub B)) ∈ sqh.range := by
    rw [hrange]
    trivial
  obtain ⟨u₂, hu₂⟩ : (⟨z₂, hz₂⟩ : ↥(PartTwo.omegaOneSub B)) ∈ sqh.range := by
    rw [hrange]
    trivial
  have hu₁' : (u₁ : G) * u₁ = z₁ := congrArg Subtype.val hu₁
  have hu₂' : (u₂ : G) * u₂ = z₂ := congrArg Subtype.val hu₂
  have hpow : ∀ x : ↥B, ∀ n : ℕ, x ^ (n % 4) = x ^ n := by
    intro x n
    have h1 : x ^ 4 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hexp x x.2)
    conv_rhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, h1, one_pow, mul_one]
  have hBcomm : ∀ x y : ↥B, x * y = y * x := fun x y => Subtype.ext (hBc _ x.2 _ y.2)
  let φ₀ : ZMod 4 × ZMod 4 → ↥B := fun p => u₁ ^ p.1.val * u₂ ^ p.2.val
  have hφ₀ : ∀ p q, φ₀ (p + q) = φ₀ p * φ₀ q := by
    intro p q
    show u₁ ^ (p + q).1.val * u₂ ^ (p + q).2.val = u₁ ^ p.1.val * u₂ ^ p.2.val *
      (u₁ ^ q.1.val * u₂ ^ q.2.val)
    rw [Prod.fst_add, Prod.snd_add, ZMod.val_add, ZMod.val_add, hpow, hpow, pow_add, pow_add]
    calc u₁ ^ p.1.val * u₁ ^ q.1.val * (u₂ ^ p.2.val * u₂ ^ q.2.val) =
        u₁ ^ p.1.val * (u₁ ^ q.1.val * u₂ ^ p.2.val) * u₂ ^ q.2.val := by group
      _ = u₁ ^ p.1.val * (u₂ ^ p.2.val * u₁ ^ q.1.val) * u₂ ^ q.2.val := by
          rw [hBcomm (u₁ ^ q.1.val) (u₂ ^ p.2.val)]
      _ = u₁ ^ p.1.val * u₂ ^ p.2.val * (u₁ ^ q.1.val * u₂ ^ q.2.val) := by group
  let φ : Multiplicative (ZMod 4 × ZMod 4) →* ↥B :=
    { toFun := fun p => φ₀ (Multiplicative.toAdd p)
      map_one' := by
        show u₁ ^ (0 : ZMod 4).val * u₂ ^ (0 : ZMod 4).val = 1
        rw [ZMod.val_zero, pow_zero, pow_zero, one_mul]
      map_mul' := fun p q => hφ₀ _ _ }
  have h20 : φ₀ (2, 0) = ⟨z₁, PartTwo.omegaOneSub_le B hz₁⟩ := by
    apply Subtype.ext
    show ((u₁ ^ (2 : ZMod 4).val * u₂ ^ (0 : ZMod 4).val : ↥B) : G) = z₁
    rw [show (2 : ZMod 4).val = 2 from rfl, ZMod.val_zero, pow_zero, mul_one, Subgroup.coe_pow,
      sq, hu₁']
  have h02 : φ₀ (0, 2) = ⟨z₂, PartTwo.omegaOneSub_le B hz₂⟩ := by
    apply Subtype.ext
    show ((u₁ ^ (0 : ZMod 4).val * u₂ ^ (2 : ZMod 4).val : ↥B) : G) = z₂
    rw [show (2 : ZMod 4).val = 2 from rfl, ZMod.val_zero, pow_zero, one_mul, Subgroup.coe_pow,
      sq, hu₂']
  have h22 : ((φ₀ (2, 2) : ↥B) : G) = z₁ * z₂ := by
    have : ((2, 2) : ZMod 4 × ZMod 4) = (2, 0) + (0, 2) := by decide
    rw [this, hφ₀, h20, h02]
    rfl
  have key : ∀ p : ZMod 4 × ZMod 4, p ≠ 0 → p = (2, 0) ∨ p = (0, 2) ∨ p = (2, 2) ∨
      p + p = (2, 0) ∨ p + p = (0, 2) ∨ p + p = (2, 2) := by decide
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hp' : φ₀ (Multiplicative.toAdd p) = 1 := hp
    have hpp : φ₀ (Multiplicative.toAdd p + Multiplicative.toAdd p) = 1 := by
      rw [hφ₀, hp', one_mul]
    by_contra hp1
    have hp0 : Multiplicative.toAdd p ≠ 0 := fun h => hp1 (by
      rw [← ofAdd_toAdd p, h]
      rfl)
    have hz : ∀ q ∈ ({(2, 0), (0, 2), (2, 2)} : Set (ZMod 4 × ZMod 4)), φ₀ q ≠ 1 := by
      rintro q (rfl | rfl | rfl)
      · rw [h20]
        exact fun h => hz₁1 (congrArg Subtype.val h)
      · rw [h02]
        exact fun h => hz₂1 (congrArg Subtype.val h)
      · exact fun h => hz₁₂ (by rw [← h22, h]; rfl)
    rcases key _ hp0 with h | h | h | h | h | h
    · exact hz (2, 0) (by simp) (by rw [← h]; exact hp')
    · exact hz (0, 2) (by simp) (by rw [← h]; exact hp')
    · exact hz (2, 2) (by simp) (by rw [← h]; exact hp')
    · exact hz (2, 0) (by simp) (by rw [← h]; exact hpp)
    · exact hz (0, 2) (by simp) (by rw [← h]; exact hpp)
    · exact hz (2, 2) (by simp) (by rw [← h]; exact hpp)
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le (by
    rw [hB16, Nat.card_eq_fintype_card]
    rfl)
  exact ⟨((MulEquiv.ofBijective φ hbij).symm).trans (MulEquiv.prodMultiplicative _ _)⟩

end CFSG.RankThree.GF2n.Tim78
