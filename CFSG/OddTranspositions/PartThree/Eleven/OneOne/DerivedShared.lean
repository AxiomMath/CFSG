module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.Milestones.ASVolI.I2Covers

public section

namespace CFSG.OddTranspositions.PartThree

namespace DerivedShared

open scoped commutatorElement

lemma mem_sup_of_commute {H : Type*} [Group H] {L₁ L₂ : Subgroup H}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) {x : H} :
    x ∈ L₁ ⊔ L₂ ↔ ∃ a ∈ L₁, ∃ b ∈ L₂, a * b = x := by
  let T : Subgroup H :=
    { carrier := {x : H | ∃ a ∈ L₁, ∃ b ∈ L₂, a * b = x}
      one_mem' := ⟨1, L₁.one_mem, 1, L₂.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, L₁.mul_mem ha₁ ha₂, b₁ * b₂, L₂.mul_mem hb₁ hb₂, ?_⟩
        have h := (hcomm a₂ ha₂ b₁ hb₁).eq
        calc (a₁ * a₂) * (b₁ * b₂) = a₁ * (a₂ * (b₁ * b₂)) := by rw [mul_assoc]
          _ = a₁ * ((a₂ * b₁) * b₂) := by rw [mul_assoc]
          _ = a₁ * ((b₁ * a₂) * b₂) := by rw [h]
          _ = a₁ * (b₁ * (a₂ * b₂)) := by rw [mul_assoc]
          _ = (a₁ * b₁) * (a₂ * b₂) := by rw [mul_assoc]
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, L₁.inv_mem ha, b⁻¹, L₂.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact ((hcomm a ha b hb).inv_inv).eq }
  have hT : L₁ ⊔ L₂ = T := by
    apply le_antisymm
    · rw [Subgroup.sup_eq_closure_mul]
      refine (Subgroup.closure_le T).mpr ?_
      rintro x ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact Subgroup.mul_mem_sup ha hb
  rw [hT]
  exact Iff.rfl

lemma map_conj_comap {H X : Type*} [Group H] [Group X] (π : H →* X)
    {A B : Subgroup X} {r : H} (h : A.map (MulAut.conj (π r)).toMonoidHom = B) :
    (A.comap π).map (MulAut.conj r).toMonoidHom = B.comap π := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := hx
    change π (r * y * r⁻¹) ∈ B
    rw [map_mul, map_mul, map_inv, ← h]
    exact Subgroup.mem_map_of_mem _ hy
  · intro hx
    change π x ∈ B at hx
    rw [← h] at hx
    obtain ⟨a, ha, hax⟩ := hx
    refine ⟨r⁻¹ * x * r, ?_, ?_⟩
    · change π (r⁻¹ * x * r) ∈ A
      rw [map_mul, map_mul, map_inv, ← hax]
      rw [show (MulAut.conj (π r)).toMonoidHom a = π r * a * (π r)⁻¹ by
        simp [MulAut.conj_apply]]
      rw [show (π r)⁻¹ * (π r * a * (π r)⁻¹) * π r = a by group]
      exact ha
    · change r * (r⁻¹ * x * r) * r⁻¹ = x
      group

lemma comm_of_perfect {H : Type*} [Group H] (K : Subgroup H)
    (hKcen : K ≤ Subgroup.center H) (Lam : Subgroup H) {b : H}
    (hperf : commutator ↥Lam ⊔ K.subgroupOf Lam = ⊤)
    (hmem : ∀ a ∈ Lam, ⁅a, b⁆ ∈ K) :
    ∀ a ∈ Lam, Commute a b := by
  let φ : Lam →* K :=
    { toFun := fun a => ⟨⁅(a : H), b⁆, hmem a a.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a₁ a₂ => by
        apply Subtype.ext
        change ⁅((a₁ : H) * (a₂ : H)), b⁆ = ⁅(a₁ : H), b⁆ * ⁅(a₂ : H), b⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hc₂ : ⁅(a₂ : H), b⁆ ∈ Subgroup.center H := hKcen (hmem a₂ a₂.2)
        have hconj : (a₁ : H) * ⁅(a₂ : H), b⁆ * (a₁ : H)⁻¹ = ⁅(a₂ : H), b⁆ := by
          have h := Subgroup.mem_center_iff.mp hc₂ (a₁ : H)
          rw [h, mul_assoc, mul_inv_cancel, mul_one]
        rw [hconj]
        exact Subgroup.mem_center_iff.mp (hKcen (hmem a₁ a₁.2)) ⁅(a₂ : H), b⁆ }
  have hφ_apply : ∀ a : Lam, (φ a : H) = ⁅(a : H), b⁆ := fun a => rfl
  have hab : ∀ u v : K, Commute u v := by
    intro u v
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hKcen u.2) (v : H)).symm
  have hker_top : φ.ker = ⊤ := by
    apply top_unique
    rw [← hperf]
    apply sup_le
    · rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact (hab (φ x) (φ y)).commutator_eq
    · intro k hk
      rw [MonoidHom.mem_ker]
      have hc : Commute b (k : H) := Subgroup.mem_center_iff.mp (hKcen hk) b
      apply Subtype.ext
      rw [hφ_apply k]
      simpa using hc.symm.commutator_eq
  intro a ha
  have h1 : φ ⟨a, ha⟩ = 1 := by
    have : (⟨a, ha⟩ : Lam) ∈ φ.ker := by rw [hker_top]; exact Subgroup.mem_top _
    simpa [MonoidHom.mem_ker] using this
  have h2 : ⁅a, b⁆ = 1 := by
    have := congrArg (fun z : K => (z : H)) h1
    rw [hφ_apply ⟨a, ha⟩] at this
    simpa using this
  exact commutatorElement_eq_one_iff_commute.mp h2

lemma map_eq_self {H : Type*} [Group H] (f : H →* H) (S : Subgroup H)
    (hfix : ∀ x ∈ S, f x = x) : S.map f = S := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    rw [hfix y hy]
    exact hy
  · intro x hx
    exact ⟨x, hx, hfix x hx⟩

theorem isSL2_of_center_eq_bot {J : Type} [Group J] [Finite J]
    (hq : CFSG.IsQuasisimple J) (hcenter : Subgroup.center J ≠ ⊥)
    (hcard : Nat.card (Subgroup.center J) ≤ 2)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 5)) :
    Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  have h2 : IsPGroup 2 (Subgroup.center J) := by
    have hne1 : Nat.card (Subgroup.center J) ≠ 1 :=
      fun h1 => hcenter (Subgroup.eq_bot_of_card_eq _ h1)
    have heq : Nat.card (Subgroup.center J) = 2 := by
      have hpos : 0 < Nat.card (Subgroup.center J) := Nat.card_pos
      omega
    exact IsPGroup.of_card (p := 2) (n := 1) (by rw [pow_one]; exact heq)
  exact (CFSG.ASVolI.burnsideI2a_I_2_2_one hq hcenter h2).1 ⟨e⟩

end DerivedShared

end CFSG.OddTranspositions.PartThree
