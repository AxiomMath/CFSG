module

public import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem tim77_2_3 {A : Subgroup G} (hA : Assembly.IsElemAbelian 2 A) (hTI : IsTI A) {g : G}
    (hg : conjSubgroup g A ≤ Subgroup.normalizer (A : Set G)) :
    Assembly.IsElemAbelian 2 (A ⊔ conjSubgroup g A) := by
  set B := conjSubgroup g A with hBdef
  have hBTI : IsTI B := isTI_conjSubgroup hTI g
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    by_cases hAB : B = A
    · intro a ha b hb
      rw [hAB] at hb
      exact congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hABbot : A ⊓ B = ⊥ := by
      by_contra hne
      exact hAB (conjSubgroup_eq_of_isTI hTI hne)
    have hAN : ∀ a ∈ A, a ∈ Subgroup.normalizer (B : Set G) := by
      intro a ha
      by_contra haN
      have hBa : B ⊓ conjSubgroup a B = ⊥ :=
        inf_conjSubgroup_eq_bot_of_isTI hBTI fun h => haN (conjSubgroup_eq_self_iff.mp h)
      have hcon : ∀ b ∈ B, b * a⁻¹ * b⁻¹ * a ∈ A := by
        intro b hb
        have h1 : b * a⁻¹ * b⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp (hg hb) a⁻¹).mp (A.inv_mem ha)
        exact A.mul_mem h1 ha
      let φ : B → A := fun b => ⟨(b : G) * a⁻¹ * (b : G)⁻¹ * a, hcon b b.2⟩
      have hφ : Function.Injective φ := by
        intro b b' hbb
        have h1 : (b : G) * a⁻¹ * (b : G)⁻¹ * a = (b' : G) * a⁻¹ * (b' : G)⁻¹ * a :=
          congrArg Subtype.val hbb
        set c : G := (b' : G)⁻¹ * b with hc
        have hcB : c ∈ B := B.mul_mem (B.inv_mem b'.2) b.2
        have hca : c * a = a * c := by
          have h2 : (b : G) * a⁻¹ * (b : G)⁻¹ = (b' : G) * a⁻¹ * (b' : G)⁻¹ :=
            mul_right_cancel h1
          have h3 : c * a⁻¹ * c⁻¹ = a⁻¹ := by
            rw [hc]
            calc (b' : G)⁻¹ * b * a⁻¹ * ((b' : G)⁻¹ * b)⁻¹
                = (b' : G)⁻¹ * ((b : G) * a⁻¹ * (b : G)⁻¹) * b' := by group
              _ = (b' : G)⁻¹ * ((b' : G) * a⁻¹ * (b' : G)⁻¹) * b' := by rw [h2]
              _ = a⁻¹ := by group
          have h4 : c * a⁻¹ = a⁻¹ * c := by
            calc c * a⁻¹ = c * a⁻¹ * c⁻¹ * c := by group
              _ = a⁻¹ * c := by rw [h3]
          calc c * a = a * (a⁻¹ * c) * a := by group
            _ = a * (c * a⁻¹) * a := by rw [h4]
            _ = a * c := by group
        have hcBa : c ∈ conjSubgroup a B := by
          rw [mem_conjSubgroup]
          have : a⁻¹ * c * a = c := by
            calc a⁻¹ * c * a = a⁻¹ * (c * a) := by group
              _ = a⁻¹ * (a * c) := by rw [hca]
              _ = c := by group
          rw [this]
          exact hcB
        have hc1 : c = 1 := by
          have : c ∈ B ⊓ conjSubgroup a B := ⟨hcB, hcBa⟩
          rw [hBa] at this
          exact Subgroup.mem_bot.mp this
        apply Subtype.ext
        have : (b' : G)⁻¹ * b = 1 := hc1
        calc (b : G) = b' * ((b' : G)⁻¹ * b) := by group
          _ = b' := by rw [this, mul_one]
      have eBA : B ≃ A := (A.equivMapOfInjective _ (MulAut.conj g).injective).symm.toEquiv
      obtain ⟨b, hb⟩ := hφ.surjective_of_finite eBA ⟨a, ha⟩
      have h1 : (b : G) * a⁻¹ * (b : G)⁻¹ * a = a := congrArg Subtype.val hb
      have ha1 : a = 1 := by
        have : (b : G) * a⁻¹ * (b : G)⁻¹ = 1 := by
          calc (b : G) * a⁻¹ * (b : G)⁻¹ = (b : G) * a⁻¹ * (b : G)⁻¹ * a * a⁻¹ := by group
            _ = 1 := by rw [h1, mul_inv_cancel]
        have h5 : a⁻¹ = 1 := by
          calc a⁻¹ = (b : G)⁻¹ * ((b : G) * a⁻¹ * (b : G)⁻¹) * b := by group
            _ = 1 := by rw [this]; group
        simpa using h5
      exact haN (ha1 ▸ Subgroup.one_mem _)
    intro a ha b hb
    have hc : a⁻¹ * b⁻¹ * a * b ∈ A ⊓ B := by
      constructor
      · have : b⁻¹ * a * b ∈ A := by
          have := (Subgroup.mem_normalizer_iff.mp (hg (B.inv_mem hb)) a).mp ha
          simpa using this
        have h2 := A.mul_mem (A.inv_mem ha) this
        simpa [mul_assoc] using h2
      · have : a⁻¹ * b⁻¹ * a ∈ B := by
          have := (Subgroup.mem_normalizer_iff.mp (hAN a⁻¹ (A.inv_mem ha)) b⁻¹).mp
            (B.inv_mem hb)
          simpa using this
        exact B.mul_mem this hb
    rw [hABbot, Subgroup.mem_bot] at hc
    calc a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = b * a := by rw [hc, mul_one]
  have hBab : Assembly.IsElemAbelian 2 B := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      apply Subtype.ext
      have h := congrArg Subtype.val (hA.1.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩)
      simp only [Subgroup.coe_mul] at h
      simp only [Subgroup.coe_mul, MulEquiv.coe_toMonoidHom, ← map_mul, h]
    · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      simp only [MulEquiv.coe_toMonoidHom, ← map_pow, hA.2 x' hx', map_one]
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (hBab.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  have hmem : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
    intro x hx
    have hN : B ≤ Subgroup.normalizer (A : Set G) := hg
    have hx' : x ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hN]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, b, hb, hx⟩ := hmem x x.2
    obtain ⟨a', ha', b', hb', hy⟩ := hmem y y.2
    change (x : G) * y = y * x
    rw [hx, hy]
    calc a * b * (a' * b') = (a * a') * (b * b') := by
          rw [mul_assoc, ← mul_assoc b, ← hcomm a' ha' b hb]; group
      _ = (a' * a) * (b' * b) := by rw [hAc a ha a' ha', hBc b hb b' hb']
      _ = a' * b' * (a * b) := by
          rw [mul_assoc, ← mul_assoc a, hcomm a ha b' hb']; group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
    rw [Commute.mul_pow (hcomm a ha b hb), hA.2 a ha, hBab.2 b hb, one_mul]

end CFSG.RankThree.GF2n.Tim77
