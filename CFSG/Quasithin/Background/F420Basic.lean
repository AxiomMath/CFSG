module

public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.F420

open CFSG.Open

section Sylow

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem exists_sylow_eq {S : Subgroup X} (hS : quasithinIsSylowTwo S) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = S :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ⟨hS.1.toSylow hS.2, rfl⟩

theorem exists_conj_mem_of_isPGroup {T S : Subgroup X} (hT : IsPGroup 2 T)
    (hS : quasithinIsSylowTwo S) : ∃ g : X, ∀ t ∈ T, g * t * g⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ⟩ := hT.exists_le_sylow
  obtain ⟨P, rfl⟩ := exists_sylow_eq hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  refine ⟨g, fun t ht => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have : (MulAut.conj g)⁻¹ • (g * t * g⁻¹) = t := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]
    group
  rw [this]
  exact hTQ ht

end Sylow

section Closure

variable {G : Type*} [Group G]

theorem isPGroup_closure_pair {r s : G} {n k : ℕ} (hr : r ^ (2 ^ n) = 1) (hs : s ^ 2 = 1)
    (hsr : s * r * s⁻¹ = r ^ k) : IsPGroup 2 (Subgroup.closure {r, s}) := by
  have hs' : s⁻¹ = s := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hs]
  have hconj : ∀ i : ℕ, s * r ^ i * s⁻¹ = r ^ (k * i) := by
    intro i
    rw [pow_mul, ← hsr, conj_pow]
  have hcomm : ∀ i : ℕ, s * r ^ i = r ^ (k * i) * s := by
    intro i
    rw [← hconj i, inv_mul_cancel_right]
  have hrinv : ∀ i : ℕ, (r ^ i)⁻¹ = r ^ ((2 ^ n - 1) * i) := by
    intro i
    have h2 : i + (2 ^ n - 1) * i = 2 ^ n * i := by
      calc i + (2 ^ n - 1) * i = (2 ^ n - 1 + 1) * i := by ring
        _ = 2 ^ n * i := by rw [Nat.sub_add_cancel Nat.one_le_two_pow]
    rw [inv_eq_iff_mul_eq_one, ← pow_add, h2, pow_mul, hr, one_pow]
  let H : Subgroup G :=
    { carrier := {x | ∃ i : ℕ, x = r ^ i ∨ x = r ^ i * s}
      mul_mem' := by
        rintro x y ⟨i, rfl | rfl⟩ ⟨j, rfl | rfl⟩
        · exact ⟨i + j, Or.inl (pow_add r i j).symm⟩
        · exact ⟨i + j, Or.inr (by rw [pow_add, mul_assoc])⟩
        · refine ⟨i + k * j, Or.inr ?_⟩
          rw [pow_add, mul_assoc, hcomm j, mul_assoc]
        · refine ⟨i + k * j, Or.inl ?_⟩
          rw [pow_add, mul_assoc, ← mul_assoc s, hcomm j, mul_assoc, ← sq, hs, mul_one]
      one_mem' := ⟨0, Or.inl (pow_zero r).symm⟩
      inv_mem' := by
        rintro x ⟨i, rfl | rfl⟩
        · exact ⟨_, Or.inl (hrinv i)⟩
        · refine ⟨k * ((2 ^ n - 1) * i), Or.inr ?_⟩
          rw [mul_inv_rev, hs', hrinv i, hcomm] }
  have hle : Subgroup.closure {r, s} ≤ H := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨1, Or.inl (pow_one x).symm⟩
    · exact ⟨0, Or.inr (by rw [pow_zero, one_mul])⟩
  refine IsPGroup.to_le (fun ⟨x, hx⟩ => ?_) hle
  obtain ⟨i, rfl | rfl⟩ := hx
  · refine ⟨n, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← pow_mul, mul_comm, pow_mul, hr, one_pow]
  · refine ⟨n + 1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    have hsq : (r ^ i * s) ^ 2 = r ^ (i + k * i) := by
      rw [sq, mul_assoc, ← mul_assoc s, hcomm i, mul_assoc, ← sq, hs, mul_one, ← pow_add]
    rw [pow_succ, mul_comm, pow_mul, hsq, ← pow_mul, mul_comm, pow_mul, hr, one_pow]

end Closure

section Witness

variable {X Y : Type*} [Group X] [Group Y]

@[expose] def SmallCentralizerWitness (X : Type*) [Group X] : Prop :=
  ∃ (T : Subgroup X) (z : X), IsPGroup 2 T ∧ ∀ x : X, (∀ t ∈ T, x * t = t * x) → x = 1 ∨ x = z

theorem centralizer_le_two [Finite X] (h : SmallCentralizerWitness X) {S : Subgroup X}
    (hS : quasithinIsSylowTwo S) (x y : X) (hx : ∀ s ∈ S, x * s = s * x)
    (hy : ∀ s ∈ S, y * s = s * y) : x = 1 ∨ y = 1 ∨ x = y := by
  obtain ⟨T, z, hT, hz⟩ := h
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup hT hS
  have key : ∀ w : X, (∀ s ∈ S, w * s = s * w) → w = 1 ∨ w = g * z * g⁻¹ := by
    intro w hw
    have hw' : ∀ t ∈ T, (g⁻¹ * w * g) * t = t * (g⁻¹ * w * g) := by
      intro t ht
      have h1 := hw _ (hg t ht)
      calc (g⁻¹ * w * g) * t = g⁻¹ * (w * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * w) * g := by rw [h1]
        _ = t * (g⁻¹ * w * g) := by group
    rcases hz _ hw' with h1 | h1
    · left
      calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · right
      calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
        _ = g * z * g⁻¹ := by rw [h1]
  rcases key x hx with h1 | h1
  · exact Or.inl h1
  rcases key y hy with h2 | h2
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (h1.trans h2.symm))

@[expose] def NoFourCentralizing (X : Type*) [Group X] : Prop :=
  ∀ S : Subgroup X, quasithinIsSylowTwo S → ∀ α β : MulAut X, (∀ s ∈ S, α s = s) →
    (∀ s ∈ S, β s = s) → α * β = β * α → α * α = 1 → β * β = 1 → α = 1 ∨ β = 1 ∨ α = β

theorem noFourCentralizing_of_inner [Finite X]
    (hinner : ∀ S : Subgroup X, quasithinIsSylowTwo S → ∀ α : MulAut X, (∀ s ∈ S, α s = s) →
      ∃ x : X, ∀ y : X, α y = x⁻¹ * y * x)
    (hW : SmallCentralizerWitness X) : NoFourCentralizing X := by
  intro S hS α β hα hβ _ _ _
  obtain ⟨a, ha⟩ := hinner S hS α hα
  obtain ⟨b, hb⟩ := hinner S hS β hβ
  have hcent : ∀ (φ : MulAut X) (c : X), (∀ y, φ y = c⁻¹ * y * c) → (∀ s ∈ S, φ s = s) →
      ∀ s ∈ S, c * s = s * c := by
    intro φ c hc hφ s hs
    have h1 := (hc s).symm.trans (hφ s hs)
    calc c * s = c * (c⁻¹ * s * c) := by rw [h1]
      _ = s * c := by group
  have hext : ∀ (φ : MulAut X) (c : X), (∀ y, φ y = c⁻¹ * y * c) → c = 1 → φ = 1 := by
    intro φ c hc h1
    ext y
    rw [hc, h1]
    simp
  rcases centralizer_le_two hW hS a b (hcent α a ha hα) (hcent β b hb hβ) with h | h | h
  · exact Or.inl (hext α a ha h)
  · exact Or.inr (Or.inl (hext β b hb h))
  · refine Or.inr (Or.inr ?_)
    ext y
    rw [ha, hb, h]

theorem quasithinIsSylowTwo_map (e : X ≃* Y) {S : Subgroup X} (hS : quasithinIsSylowTwo S) :
    quasithinIsSylowTwo (S.map e.toMonoidHom) := by
  refine ⟨hS.1.map _, ?_⟩
  rw [Subgroup.index_map_eq _ e.surjective (by
    rw [MonoidHom.ker_eq_bot_iff _ |>.mpr e.injective]
    exact bot_le)]
  exact hS.2

theorem NoFourCentralizing.of_mulEquiv (e : X ≃* Y) (h : NoFourCentralizing Y) :
    NoFourCentralizing X := by
  intro S hS α β hα hβ hab ha hb
  let c : MulAut X ≃* MulAut Y := MulAut.congr e
  have hfix : ∀ φ : MulAut X, (∀ s ∈ S, φ s = s) → ∀ s ∈ S.map e.toMonoidHom, c φ s = s := by
    rintro φ hφ _ ⟨s, hs, rfl⟩
    change e (φ (e.symm (e s))) = e s
    rw [MulEquiv.symm_apply_apply, hφ s hs]
  have key := h _ (quasithinIsSylowTwo_map e hS) (c α) (c β) (hfix α hα) (hfix β hβ)
    (by rw [← map_mul, hab, map_mul]) (by rw [← map_mul, ha, map_one])
    (by rw [← map_mul, hb, map_one])
  rcases key with h1 | h1 | h1
  · exact Or.inl (c.injective (h1.trans (map_one c).symm))
  · exact Or.inr (Or.inl (c.injective (h1.trans (map_one c).symm)))
  · exact Or.inr (Or.inr (c.injective h1))

end Witness

end CFSG.Quasithin.F420
