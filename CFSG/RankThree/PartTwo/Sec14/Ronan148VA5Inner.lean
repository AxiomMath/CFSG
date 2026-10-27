module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Alt
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JNA6

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

theorem inner_a5_mem_zpowers {Q : Type} [Group Q] {e x : Q} (he3 : e ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers e) : x = 1 ∨ x = e ∨ x = e⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h3 : e ^ (3 : ℤ) = 1 := by simpa using he3
  have hk : e ^ k = e ^ (k % 3) := by
    have hk3 : k = k % 3 + 3 * (k / 3) := by omega
    conv_lhs => rw [hk3]
    rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [hk]
  rcases hr with h | h | h
  · left
    rw [h]
    simp
  · right
    left
    rw [h]
    simp
  · right
    right
    rw [h]
    have h21 : e ^ (2 : ℤ) * e = 1 := by
      rw [← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num, h3]
    exact eq_inv_of_mul_eq_one_left h21

theorem inner_a5_center_eq_bot {H : Type} [Group H] (φ : H ≃* alternatingGroup (Fin 5)) :
    Subgroup.center H = ⊥ := by
  have hmap := Subgroup.map_center_eq φ
  rw [CFSG.RankThree.PartTwo.Sec14.Ronan148J.center_alternatingGroup_five_eq_bot] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hmap

def inner_a5_cyc012 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

def inner_a5_cyc031 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 0 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem inner_a5_cyc012_pow_three : inner_a5_cyc012 ^ 3 = 1 := by decide

theorem inner_a5_cyc031_pow_three : inner_a5_cyc031 ^ 3 = 1 := by decide

theorem inner_a5_cyc012_ne_one : inner_a5_cyc012 ≠ 1 := by decide

theorem inner_a5_cyc031_ne_one : inner_a5_cyc031 ≠ 1 := by decide

theorem inner_a5_cyc031_ne_cyc012 : inner_a5_cyc031 ≠ inner_a5_cyc012 := by decide

theorem inner_a5_cyc031_ne_cyc012_inv : inner_a5_cyc031 ≠ inner_a5_cyc012⁻¹ := by decide

theorem mem_of_inner_a5 {Q : Type} [Group Q] [Finite Q] {Aq Jq Zq : Subgroup Q} {e : Q}
    (hAab : ∀ x ∈ Aq, ∀ y ∈ Aq, x * y = y * x) (hA3 : ∀ a ∈ Aq, a ^ 3 = 1)
    (hF3 : ∀ w : Q, w ∈ Subgroup.centralizer (Aq : Set Q) → w ^ 3 = 1 → w ∈ Aq)
    (hC : Aq ⊓ Subgroup.centralizer (Jq : Set Q) = Subgroup.zpowers e)
    (hCD : Aq ⊓ Subgroup.centralizer (Jq : Set Q) ⊔ Aq ⊓ Jq = Aq)
    (hZJ : Zq ≤ Subgroup.centralizer (Jq : Set Q))
    (hAN : Aq ≤ Subgroup.normalizer (Zq : Set Q))
    (φ : ↥Zq ≃* alternatingGroup (Fin 5)) : e ∈ Zq := by
  have heA : e ∈ Aq := by
    have h : e ∈ Aq ⊓ Subgroup.centralizer (Jq : Set Q) := by
      rw [hC]
      exact Subgroup.mem_zpowers e
    exact h.1
  have he3 : e ^ 3 = 1 := hA3 e heA
  have hAeq : Subgroup.zpowers e ⊔ Aq ⊓ Jq = Aq := by
    rw [← hC]
    exact hCD
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : MulAut ↥Zq, ρ = Zq.normalizerMonoidHom ⟨e, hAN heA⟩ := ⟨_, rfl⟩
  have hρapp : ∀ z : ↥Zq, ((ρ z : ↥Zq) : Q) = e * z * e⁻¹ := fun z => by
    rw [hρdef]
    rfl
  have hρ3 : ρ ^ 3 = 1 := by
    rw [hρdef, ← map_pow]
    have h3 : (⟨e, hAN heA⟩ : ↥(Subgroup.normalizer (Zq : Set Q))) ^ 3 = 1 :=
      Subtype.ext (by simpa using he3)
    rw [h3, map_one]
  have hinn : CFSG.RankThree.PartTwo.KFacts.IsInnerAut ρ :=
    CFSG.HardMathSupport.Dickson.Sec6.I1431.isInnerAut_of_alt (β' := Fin 5) (by simp) φ hρ3
  obtain ⟨z₀, hz₀⟩ := MonoidHom.mem_range.mp hinn
  have hconj : ∀ z : ↥Zq, e * (z : Q) * e⁻¹ = (z₀ : Q) * z * (z₀ : Q)⁻¹ := by
    intro z
    rw [← hρapp, ← hz₀]
    rfl
  have hez₀ : e * (z₀ : Q) = (z₀ : Q) * e := by
    have h := hconj z₀
    have hz : (z₀ : Q) * (z₀ : Q) * (z₀ : Q)⁻¹ = z₀ := by group
    rw [hz] at h
    calc e * (z₀ : Q) = e * (z₀ : Q) * e⁻¹ * e := by group
      _ = (z₀ : Q) * e := by rw [h]
  have hz₀C : (z₀ : Q) ∈ Subgroup.centralizer (Aq : Set Q) := by
    have hAle : Aq ≤ Subgroup.centralizer ({(z₀ : Q)} : Set Q) := by
      rw [← hAeq]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (fun x hx => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hez₀
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (hZJ z₀.2) x hx.2)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hAle ha)
  have hz₀3' : z₀ ^ 3 = 1 := by
    have hcen : z₀ ^ 3 ∈ Subgroup.center ↥Zq := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : MulAut.conj (z₀ ^ 3) = 1 := by rw [map_pow, hz₀, hρ3]
      have h2 := congrArg (fun τ : MulAut ↥Zq => τ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * z₀ ^ 3 = z₀ ^ 3 * g * (z₀ ^ 3)⁻¹ * z₀ ^ 3 := by rw [h2]
        _ = z₀ ^ 3 * g := by group
    rw [inner_a5_center_eq_bot φ, Subgroup.mem_bot] at hcen
    exact hcen
  have hz₀3 : (z₀ : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hz₀3'
  have hz₀A : (z₀ : Q) ∈ Aq := hF3 _ hz₀C hz₀3
  have hz₀e : (z₀ : Q) ∈ Subgroup.zpowers e := by
    have h : (z₀ : Q) ∈ Aq ⊓ Subgroup.centralizer (Jq : Set Q) := ⟨hz₀A, hZJ z₀.2⟩
    rw [hC] at h
    exact h
  have hz₀1 : (z₀ : Q) ≠ 1 := by
    intro h1
    have hEZ : ∀ z ∈ Zq, e * z = z * e := by
      intro z hz
      have h : e * z * e⁻¹ = z := by
        have := hconj ⟨z, hz⟩
        simpa [h1] using this
      calc e * z = e * z * e⁻¹ * e := by group
        _ = z * e := by rw [h]
    have hAZ : Aq ≤ Subgroup.centralizer (Zq : Set Q) := by
      rw [← hAeq]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (hEZ z hz).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (Subgroup.mem_centralizer_iff.mp (hZJ hz) x hx.2).symm
    have hZ3 : ∀ w : ↥Zq, (w : Q) ^ 3 = 1 → (w : Q) ∈ Subgroup.zpowers e := by
      intro w hw3
      have hwC : (w : Q) ∈ Subgroup.centralizer (Aq : Set Q) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact (Subgroup.mem_centralizer_iff.mp (hAZ ha) (w : Q) w.2).symm
      have h : (w : Q) ∈ Aq ⊓ Subgroup.centralizer (Jq : Set Q) :=
        ⟨hF3 _ hwC hw3, hZJ w.2⟩
      rw [hC] at h
      exact h
    have hsmall : ∀ w : ↥Zq, w ≠ 1 → w ^ 3 = 1 → (w : Q) = e ∨ (w : Q) = e⁻¹ := by
      intro w hw1 hw3
      have hw3' : (w : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hw3
      rcases inner_a5_mem_zpowers he3 (hZ3 w hw3') with h | h | h
      · exact absurd (Subtype.ext h) hw1
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨a, ha⟩ : ∃ a : ↥Zq, φ a = inner_a5_cyc012 := ⟨φ.symm _, φ.apply_symm_apply _⟩
    obtain ⟨b, hb⟩ : ∃ b : ↥Zq, φ b = inner_a5_cyc031 := ⟨φ.symm _, φ.apply_symm_apply _⟩
    have ha3 : a ^ 3 = 1 :=
      φ.injective (by rw [map_pow, ha, inner_a5_cyc012_pow_three, map_one])
    have hb3 : b ^ 3 = 1 :=
      φ.injective (by rw [map_pow, hb, inner_a5_cyc031_pow_three, map_one])
    have ha1 : a ≠ 1 := fun h => inner_a5_cyc012_ne_one (by rw [← ha, h, map_one])
    have hb1 : b ≠ 1 := fun h => inner_a5_cyc031_ne_one (by rw [← hb, h, map_one])
    have hba : b = a ∨ b = a⁻¹ := by
      rcases hsmall a ha1 ha3 with h | h <;> rcases hsmall b hb1 hb3 with h' | h'
      · exact Or.inl (Subtype.ext (h'.trans h.symm))
      · exact Or.inr (Subtype.ext (by rw [Subgroup.coe_inv, h, h']))
      · exact Or.inr (Subtype.ext (by rw [Subgroup.coe_inv, h, h', inv_inv]))
      · exact Or.inl (Subtype.ext (h'.trans h.symm))
    have hcyc : inner_a5_cyc031 = inner_a5_cyc012 ∨ inner_a5_cyc031 = inner_a5_cyc012⁻¹ := by
      rcases hba with h | h
      · left
        rw [← hb, ← ha, h]
      · right
        rw [← hb, ← ha, h, map_inv]
    rcases hcyc with h | h
    · exact inner_a5_cyc031_ne_cyc012 h
    · exact inner_a5_cyc031_ne_cyc012_inv h
  have hZe : (z₀ : Q) ∈ Zq := z₀.2
  rcases inner_a5_mem_zpowers he3 hz₀e with h | h | h
  · exact absurd h hz₀1
  · rw [← h]
    exact hZe
  · have he : e = (z₀ : Q)⁻¹ := by rw [h, inv_inv]
    rw [he]
    exact Zq.inv_mem hZe

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
