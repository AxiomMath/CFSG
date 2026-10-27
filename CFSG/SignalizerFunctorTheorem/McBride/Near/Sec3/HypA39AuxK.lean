module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxRed2

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped Pointwise commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type u} [Group Γ] {p : ℕ} {H A D D₁ D₂ E L R : Subgroup Γ}

namespace Red

theorem exists_prime [Finite Γ] (c : Red p H A D D₁ D₂ E L R) :
    ∃ r : ℕ, r.Prime ∧ ∀ x ∈ L, x ^ r = 1 := by
  obtain ⟨⟨x, hxL⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp c.hL0
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hord1 : orderOf x ≠ 1 := fun h => hx1' (orderOf_eq_one_iff.mp h)
  have hord0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  set r := (orderOf x).minFac with hr
  have hrp : r.Prime := Nat.minFac_prime hord1
  have hrd : r ∣ orderOf x := Nat.minFac_dvd _
  refine ⟨r, hrp, ?_⟩
  let T : Subgroup Γ :=
    { carrier := {y | y ∈ L ∧ y ^ r = 1}
      one_mem' := ⟨one_mem _, one_pow r⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        have hc : Commute a b := c.L_comm a ha.1 b hb.1
        rw [hc.mul_pow, ha.2, hb.2, mul_one]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hTL : T ≤ L := fun y hy => hy.1
  have hTadm : Admits (H ⊔ A) T := by
    refine admits_of_forall_conj fun g hg y hy => ⟨c.hLG.conj_mem hg hy.1, ?_⟩
    rw [conj_pow, hy.2, mul_one, mul_inv_cancel]
  have hTne : T ≠ ⊥ := by
    intro hT
    have hmem : x ^ (orderOf x / r) ∈ T := by
      refine ⟨pow_mem hxL _, ?_⟩
      rw [← pow_mul, Nat.div_mul_cancel hrd, pow_orderOf_eq_one]
    rw [hT, Subgroup.mem_bot] at hmem
    have h1 : orderOf (x ^ (orderOf x / r)) = r := orderOf_pow_orderOf_div hord0 hrd
    rw [hmem, orderOf_one] at h1
    exact hrp.one_lt.ne h1
  rcases c.hLmin T hTL hTadm with h | h
  · exact absurd h hTne
  · intro y hy
    have : y ∈ T := h ▸ hy
    exact this.2

theorem K_elem [Finite Γ] (c : Red p H A D D₁ D₂ E L R) {r : ℕ} (hr : ∀ x ∈ L, x ^ r = 1)
    {K : Subgroup Γ} (hK : Admits (H ⊔ A) K) (hLK : L ≤ K) (hKR : K ≤ R) (hne : K ⊔ D₁ ≠ R) :
    (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) ∧ ∀ x ∈ K, x ^ r = 1 := by
  obtain ⟨B, hBR', hBadm, hBD, hRB⟩ := c.hasB_sup hK hLK hKR hne
  have hD₂B : D₂ ≤ B := by
    rw [← hBD]
    exact inf_le_left
  have hBR : B ≤ R := hBR'.trans (sup_le hKR c.D₁_le_R)
  have hBcen : ∀ b ∈ B, ∀ l ∈ L, b * l = l * b := fun b hb l hl => c.R_cen b (hBR hb) l hl
  have hBL : B ≤ Subgroup.normalizer (L : Set Γ) := admits_of_centralizes hBcen
  have hKBL : K ≤ B ⊔ L := by
    calc K ≤ K ⊔ D₁ := le_sup_left
      _ = B ⊔ D₁ := hRB
      _ = B ⊔ L := by rw [c.hD₁, ← sup_assoc, sup_eq_left.mpr hD₂B]
  have hdec : ∀ x ∈ K, ∃ b ∈ B, ∃ l ∈ L, x = b * l := fun x hx =>
    (mem_sup_iff_mul_of_le_normalizer hBL).mp (hKBL hx)
  let S : Set Γ := {z | ∃ x ∈ K, ∃ y ∈ K, z = ⁅x, y⁆} ∪ {z | ∃ x ∈ K, z = x ^ r}
  have hSBK : ∀ z ∈ S, z ∈ B ⊓ K := by
    rintro z (⟨x, hx, y, hy, rfl⟩ | ⟨x, hx, rfl⟩)
    · obtain ⟨b₁, hb₁, l₁, hl₁, rfl⟩ := hdec x hx
      obtain ⟨b₂, hb₂, l₂, hl₂, rfl⟩ := hdec y hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h₁ : l₁ * (b₂ * l₂) * l₁⁻¹ = b₂ * l₂ := by
          have : l₁ * (b₂ * l₂) = (b₂ * l₂) * l₁ := by
            rw [← mul_assoc, (hBcen b₂ hb₂ l₁ hl₁).symm, mul_assoc, mul_assoc,
              c.L_comm l₁ hl₁ l₂ hl₂]
          rw [this, mul_assoc, mul_inv_cancel, mul_one]
        have h₂ : l₂ * b₁⁻¹ * l₂⁻¹ = b₁⁻¹ := by
          have : l₂ * b₁⁻¹ = b₁⁻¹ * l₂ := by
            have := hBcen b₁⁻¹ (inv_mem hb₁) l₂ hl₂
            exact this.symm
          rw [this, mul_assoc, mul_inv_cancel, mul_one]
        have : ⁅b₁ * l₁, b₂ * l₂⁆ = ⁅b₁, b₂⁆ := by
          calc ⁅b₁ * l₁, b₂ * l₂⁆ = b₁ * (l₁ * (b₂ * l₂) * l₁⁻¹) * b₁⁻¹ * l₂⁻¹ * b₂⁻¹ := by
                simp only [commutatorElement_def]
                group
            _ = b₁ * (b₂ * l₂) * b₁⁻¹ * l₂⁻¹ * b₂⁻¹ := by rw [h₁]
            _ = b₁ * b₂ * (l₂ * b₁⁻¹ * l₂⁻¹) * b₂⁻¹ := by group
            _ = b₁ * b₂ * b₁⁻¹ * b₂⁻¹ := by rw [h₂]
        rw [this]
        simp only [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hb₁ hb₂) (inv_mem hb₁)) (inv_mem hb₂)
      · simp only [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    · obtain ⟨b, hb, l, hl, rfl⟩ := hdec x hx
      have hc : Commute b l := hBcen b hb l hl
      rw [hc.mul_pow, hr l hl, mul_one]
      refine Subgroup.mem_inf.mpr ⟨pow_mem hb r, ?_⟩
      have hbK : b ∈ K := by
        have := mul_mem hx (inv_mem (hLK hl))
        simpa using this
      exact pow_mem hbK r
  have hTBK : Subgroup.closure S ≤ B ⊓ K := (Subgroup.closure_le _).mpr hSBK
  have hTadm : Admits (H ⊔ A) (Subgroup.closure S) := by
    refine admits_closure fun g hg z hz => ?_
    rcases hz with ⟨x, hx, y, hy, rfl⟩ | ⟨x, hx, rfl⟩
    · refine Or.inl ⟨g * x * g⁻¹, hK.conj_mem hg hx, g * y * g⁻¹, hK.conj_mem hg hy, ?_⟩
      simp only [commutatorElement_def]
      group
    · exact Or.inr ⟨g * x * g⁻¹, hK.conj_mem hg hx, (conj_pow).symm⟩
  have hT0 : Subgroup.closure S = ⊥ := by
    refine c.eq_bot_of_normal (hTBK.trans (inf_le_right.trans (hKR.trans c.R_le_H))) hTadm ?_
    intro x hx
    obtain ⟨hx1, hxD⟩ := Subgroup.mem_inf.mp hx
    have hxB := (Subgroup.mem_inf.mp (hTBK hx1)).1
    rw [← hBD]
    exact Subgroup.mem_inf.mpr ⟨hxB, hxD⟩
  have hmem : ∀ z ∈ S, z = 1 := fun z hz => by
    have : z ∈ Subgroup.closure S := Subgroup.subset_closure hz
    rw [hT0, Subgroup.mem_bot] at this
    exact this
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · exact commutatorElement_eq_one_iff_mul_comm.mp (hmem _ (Or.inl ⟨x, hx, y, hy, rfl⟩))
  · exact hmem _ (Or.inr ⟨x, hx, rfl⟩)

end Red

end CFSG.SignalizerFunctorTheorem.McBride.Near
