module

public import CFSG.Walter.ReeOrder.JT.AuxElemRep
public import CFSG.Walter.ReeOrder.JT.AuxPClosed

public section

namespace CFSG.Walter.JT

variable {A : Type*} [Group A] [Finite A] {p : ℕ} [hp : Fact p.Prime] [IsElementaryAbelian p A]

theorem sylow_le_pCore_of_le_mulAut' (hA : Nat.card A ≤ p ^ 3) (hp5 : 5 ≤ p)
    {X : Subgroup (MulAut A)} (hX : Group.IsSolvable X)
    (h23 : ∀ R : Subgroup X, (IsPGroup 2 R ∨ IsPGroup 3 R) → (R ⊔ CFSG.pCore p X).Normal →
      ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (P : Sylow p X) : (P : Subgroup X) ≤ CFSG.pCore p X := by
  refine sylow_le_pCore_of_centralize_normal hX ?_ P
  intro x hx q hq hqp R hR hRn hxR
  have : Fact q.Prime := ⟨hq⟩
  have hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    by_cases hq2 : q = 2
    · subst hq2; exact h23 R (Or.inl hR) hRn
    by_cases hq3 : q = 3
    · subst hq3; exact h23 R (Or.inr hR) hRn
    have hq5 : 3 < q := by
      have := hq.two_le
      rcases Nat.lt_or_ge q 4 with h | h
      · interval_cases q <;> simp_all
      · omega
    intro a ha b hb
    exact Subtype.ext (mul_comm_of_isPGroup hA hq5 hqp (hR.map X.subtype) _ ⟨a, ha, rfl⟩ _
      ⟨b, hb, rfl⟩)
  set R' : Subgroup (MulAut A) := R.map X.subtype
  have hR'c : ∀ a ∈ R', ∀ b ∈ R', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hRc a ha b hb)
  have hR'p : ¬ p ∣ Nat.card R' := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    intro hdvd
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    rw [hk] at hdvd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp (hp.out.dvd_of_dvd_pow hdvd)).symm
  have hxR' : (Subgroup.zpowers x).map X.subtype ≤ Subgroup.normalizer (R' : Set (MulAut A)) := by
    rintro _ ⟨g, hg, rfl⟩
    have hgN : g ∈ Subgroup.normalizer (R : Set X) := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact Subgroup.zpow_mem _ hxR k
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨g * r * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgN r).mp hr, by simp⟩
    · rintro ⟨r, hr, hrz⟩
      have hzX : z ∈ X := by
        have : z = (g : MulAut A)⁻¹ * (r : MulAut A) * g := by
          rw [Subgroup.coe_subtype] at hrz
          rw [hrz]
          group
        rw [this]
        exact X.mul_mem (X.mul_mem (X.inv_mem g.2) r.2) g.2
      refine ⟨⟨z, hzX⟩, (Subgroup.mem_normalizer_iff.mp hgN ⟨z, hzX⟩).mpr ?_, rfl⟩
      have : g * ⟨z, hzX⟩ * g⁻¹ = r := by
        apply Subtype.ext
        rw [Subgroup.coe_subtype] at hrz
        rw [hrz]
        simp
      rw [this]
      exact hr
  have key := commute_of_isPGroup hA hR'c hR'p hp.out (by omega) (hx.map X.subtype) hxR'
  intro y hy
  have := key (x : MulAut A) ⟨x, Subgroup.mem_zpowers x, rfl⟩ (y : MulAut A) ⟨y, hy, rfl⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  calc (x : MulAut A) * y = ((x : MulAut A) * y * (x : MulAut A)⁻¹) * x := by group
    _ = y * x := by rw [this]

theorem sylow_le_pCore_of_le_mulAut (hA : Nat.card A ≤ p ^ 3) (hp5 : 5 ≤ p)
    {X : Subgroup (MulAut A)} (hX : Group.IsSolvable X)
    (h23 : ∀ R : Subgroup X, (IsPGroup 2 R ∨ IsPGroup 3 R) → ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (P : Sylow p X) : (P : Subgroup X) ≤ CFSG.pCore p X :=
  sylow_le_pCore_of_le_mulAut' hA hp5 hX (fun R hR _ => h23 R hR) P

end CFSG.Walter.JT
