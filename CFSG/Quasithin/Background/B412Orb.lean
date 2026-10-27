module

public import CFSG.Quasithin.Background.B4Misc
public import CFSG.Quasithin.Background.B412Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.B412

open Matrix CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem orbit_eq_of_mul_mem (hV : ∀ v : V, v ^ 2 = 1) (G : Subgroup (MulAut V)) (v : V)
    (hgen : Subgroup.closure (orbitOf G v) = ⊤)
    (hprod : ∀ a ∈ orbitOf G v, ∀ b ∈ orbitOf G v, a ≠ b → a * b ∈ orbitOf G v) :
    ∀ x : V, x ≠ 1 → x ∈ orbitOf G v := by
  have hinv : ∀ a : V, a⁻¹ = a := fun a => by
    have := hV a
    rw [pow_two] at this
    exact inv_eq_of_mul_eq_one_right this
  let W : Subgroup V :=
    { carrier := {x | x = 1 ∨ x ∈ orbitOf G v}
      one_mem' := Or.inl rfl
      mul_mem' := fun {a b} ha hb => by
        rcases ha with rfl | ha
        · rw [one_mul]; exact hb
        · rcases hb with rfl | hb
          · rw [mul_one]; exact Or.inr ha
          · by_cases hab : a = b
            · subst hab
              left
              have := hV a
              rwa [pow_two] at this
            · exact Or.inr (hprod a ha b hb hab)
      inv_mem' := fun {a} ha => by
        show a⁻¹ = 1 ∨ a⁻¹ ∈ orbitOf G v
        rw [hinv]
        exact ha }
  have hW : W = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro x hx
    exact Or.inr hx
  intro x hx1
  have : x ∈ W := by rw [hW]; trivial
  rcases this with h | h
  · exact absurd h hx1
  · exact h

theorem smul_mem_orbitOf {G : Subgroup (MulAut V)} {v a : V} {g : MulAut V} (hg : g ∈ G)
    (ha : a ∈ orbitOf G v) : g a ∈ orbitOf G v := by
  obtain ⟨g', hg', rfl⟩ := ha
  exact ⟨g * g', G.mul_mem hg hg', rfl⟩

theorem orbit_eq_orbitOf (G : Subgroup (MulAut V)) (v : V) :
    MulAction.orbit ↥G v = orbitOf G v := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem ne_one_of_card {G : Subgroup (MulAut V)} {v : V} (hΩ : Nat.card (orbitOf G v) = 15) :
    v ≠ 1 := by
  rintro rfl
  have h : orbitOf G (1 : V) = {1} := by
    ext x
    constructor
    · rintro ⟨g, -, rfl⟩
      exact map_one g
    · rintro rfl
      exact ⟨1, G.one_mem, rfl⟩
  rw [h, Nat.card_unique] at hΩ
  omega

theorem one_not_mem_orbitOf {G : Subgroup (MulAut V)} {v : V} (hv : v ≠ 1) :
    (1 : V) ∉ orbitOf G v := by
  rintro ⟨g, -, hg⟩
  apply hv
  have : g v = g 1 := by rw [hg, map_one]
  exact g.injective this

theorem mul_mem_of_fix [Finite V] {G : Subgroup (MulAut V)} {v : V}
    (ρ : ↥G →* SpecialLinearGroup (Fin 4) (ZMod 2)) (hρ : Function.Surjective ρ)
    {p : Fin 4 → ZMod 2} (hp : p ≠ 0)
    (hfix : ∀ g : ↥G, (g : MulAut V) v = v →
      (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ p = p)
    (hΩ : Nat.card (orbitOf G v) = 15)
    {x₀ y₀ : V} (hx₀ : x₀ ∈ orbitOf G v) (hy₀ : y₀ ∈ orbitOf G v) (hxy : x₀ ≠ y₀)
    (hxy₀ : x₀ * y₀ ∈ orbitOf G v) :
    ∀ a ∈ orbitOf G v, ∀ b ∈ orbitOf G v, a ≠ b → a * b ∈ orbitOf G v := by
  classical
  have hτ : ∀ g₁ g₂ : ↥G, (g₁ : MulAut V) v = (g₂ : MulAut V) v →
      (ρ g₁ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ p =
        (ρ g₂ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ p := by
    intro g₁ g₂ h
    have h1 : ((g₁⁻¹ * g₂ : ↥G) : MulAut V) v = v := by
      show (g₁ : MulAut V)⁻¹ ((g₂ : MulAut V) v) = v
      rw [← h, MulAut.inv_apply_self]
    have e : ρ g₂ = ρ g₁ * ρ (g₁⁻¹ * g₂) := by rw [← map_mul, mul_inv_cancel_left]
    rw [e, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hfix _ h1]
  have hne : ∀ g : ↥G, (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ p ≠ 0 :=
    fun g => mulVec_ne_zero _ hp
  let gOf : ↥(orbitOf G v) → ↥G := fun a => ⟨Classical.choose a.2, (Classical.choose_spec a.2).1⟩
  have hgOf : ∀ a : ↥(orbitOf G v), ((gOf a : ↥G) : MulAut V) v = a :=
    fun a => (Classical.choose_spec a.2).2
  let Φ : ↥(orbitOf G v) → {x : Fin 4 → ZMod 2 // x ≠ 0} :=
    fun a => ⟨(ρ (gOf a) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ p, hne _⟩
  have hΦ : Function.Surjective Φ := by
    rintro ⟨q, hq⟩
    obtain ⟨s, hs⟩ := exists_mulVec_eq hp hq
    obtain ⟨g, rfl⟩ := hρ s
    refine ⟨⟨(g : MulAut V) v, ⟨g, g.2, rfl⟩⟩, Subtype.ext ?_⟩
    show (ρ (gOf _) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ p = q
    rw [hτ _ g (hgOf _), hs]
  have hcard : Nat.card {x : Fin 4 → ZMod 2 // x ≠ 0} = 15 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rfl
  have hΦi : Function.Injective Φ :=
    ((Nat.bijective_iff_surjective_and_card Φ).mpr ⟨hΦ, hΩ.trans hcard.symm⟩).1
  have hinj : ∀ g₁ g₂ : ↥G, (ρ g₁ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ p =
      (ρ g₂ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ p → (g₁ : MulAut V) v = (g₂ : MulAut V) v := by
    intro g₁ g₂ h
    let a₁ : ↥(orbitOf G v) := ⟨(g₁ : MulAut V) v, ⟨g₁, g₁.2, rfl⟩⟩
    let a₂ : ↥(orbitOf G v) := ⟨(g₂ : MulAut V) v, ⟨g₂, g₂.2, rfl⟩⟩
    have h₁ : Φ a₁ = Φ a₂ := Subtype.ext (by
      show (ρ (gOf a₁) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ p =
        (ρ (gOf a₂) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ p
      rw [hτ (gOf a₁) g₁ (hgOf a₁), hτ (gOf a₂) g₂ (hgOf a₂), h])
    exact congrArg Subtype.val (hΦi h₁)
  intro a ha b hb hab
  obtain ⟨g₁, hg₁, rfl⟩ := ha
  obtain ⟨g₂, hg₂, rfl⟩ := hb
  obtain ⟨k₁, hk₁, rfl⟩ := hx₀
  obtain ⟨k₂, hk₂, rfl⟩ := hy₀
  obtain ⟨s, hs₁, hs₂⟩ := exists_mulVec_pair (hne ⟨k₁, hk₁⟩) (hne ⟨k₂, hk₂⟩)
    (fun h => hxy (hinj ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ h)) (hne ⟨g₁, hg₁⟩) (hne ⟨g₂, hg₂⟩)
    (fun h => hab (hinj ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ h))
  obtain ⟨g, rfl⟩ := hρ s
  have e₁ : (g : MulAut V) (k₁ v) = g₁ v := by
    have := hinj (g * ⟨k₁, hk₁⟩) ⟨g₁, hg₁⟩ (by
      rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hs₁])
    exact this
  have e₂ : (g : MulAut V) (k₂ v) = g₂ v := by
    have := hinj (g * ⟨k₂, hk₂⟩) ⟨g₂, hg₂⟩ (by
      rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hs₂])
    exact this
  rw [← e₁, ← e₂, ← map_mul]
  exact smul_mem_orbitOf g.2 hxy₀

theorem dvd_fifteen {i : ℕ} (h : i ∣ 15) : i = 1 ∨ i = 3 ∨ i = 5 ∨ i = 15 := by
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases i <;> simp_all

theorem mul_mem_of_simple [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    {v : V} (hG : IsSimpleGroup ↥G) (hS : IsSimpleGroup ↥(MulAction.stabilizer ↥G v))
    (hΩ : Nat.card (orbitOf G v) = 15) (h7 : 7 ∣ Nat.card (MulAction.stabilizer ↥G v))
    (hG3 : ¬ Nat.card G ∣ 6) (hG5 : ¬ Nat.card G ∣ 120)
    {x₀ y₀ : V} (hx₀ : x₀ ∈ orbitOf G v) (hy₀ : y₀ ∈ orbitOf G v) (hxy : x₀ ≠ y₀)
    (hxy₀ : x₀ * y₀ ∈ orbitOf G v) :
    ∀ a ∈ orbitOf G v, ∀ b ∈ orbitOf G v, a ≠ b → a * b ∈ orbitOf G v := by
  classical
  set S := MulAction.stabilizer ↥G v with hSdef
  have hv1 : v ≠ 1 := ne_one_of_card hΩ
  have h1Ω : (1 : V) ∉ orbitOf G v := one_not_mem_orbitOf hv1
  have hvΩ : v ∈ orbitOf G v := ⟨1, G.one_mem, rfl⟩
  have hidx : S.index = 15 := by
    rw [MulAction.index_stabilizer, orbit_eq_orbitOf, ← Nat.card_coe_set_eq, hΩ]
  have hN : Subgroup.normalizer (S : Set ↥G) = S := by
    have hle : S ≤ Subgroup.normalizer (S : Set ↥G) := Subgroup.le_normalizer
    have hdvd : (Subgroup.normalizer (S : Set ↥G)).index ∣ 15 :=
      hidx ▸ Subgroup.index_dvd_of_le hle
    by_cases htop : Subgroup.normalizer (S : Set ↥G) = ⊤
    · exfalso
      have hn : S.Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h | h
      · rw [h, Subgroup.card_bot] at h7
        omega
      · rw [h, Subgroup.index_top] at hidx
        omega
    · have hcore : (Subgroup.normalizer (S : Set ↥G)).normalCore = ⊥ := by
        have := Subgroup.normalCore_normal (Subgroup.normalizer (S : Set ↥G))
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.normalizer (S : Set ↥G)).normalCore with h | h
        · exact h
        · exact absurd (eq_top_iff.mpr (h ▸ Subgroup.normalCore_le _)) htop
      have hfact := Subgroup.index_normalCore_dvd_factorial_index
        (H := Subgroup.normalizer (S : Set ↥G))
      rw [hcore, Subgroup.index_bot] at hfact
      have hi15 : (Subgroup.normalizer (S : Set ↥G)).index = 15 := by
        rcases dvd_fifteen hdvd with h | h | h | h
        · exact absurd (Subgroup.index_eq_one.mp h) htop
        · rw [h] at hfact
          exact absurd hfact hG3
        · rw [h] at hfact
          exact absurd hfact hG5
        · exact h
      have h1 := Subgroup.relIndex_mul_index hle
      rw [hi15, hidx] at h1
      have h2 : S.relIndex (Subgroup.normalizer (S : Set ↥G)) = 1 := by omega
      exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hle
  have hfixpt : ∀ g : ↥G, (∀ h : ↥S, h • (g • v) = g • v) → g • v = v := by
    intro g hfix
    have hSa : S ≤ MulAction.stabilizer ↥G (g • v) := fun h hh => hfix ⟨h, hh⟩
    have hcard : Nat.card (MulAction.stabilizer ↥G (g • v)) = Nat.card S := by
      rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
      exact Subgroup.card_map_of_injective (MulAut.conj g).injective
    have heq : S = MulAction.stabilizer ↥G (g • v) := Subgroup.eq_of_le_of_card_ge hSa hcard.le
    have hgN : g ∈ Subgroup.normalizer (S : Set ↥G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rw [heq, MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul,
          MulAction.mem_stabilizer_iff.mp hh]
      · intro hh
        rw [heq, MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul] at hh
        exact MulAction.mem_stabilizer_iff.mpr (smul_left_cancel g hh)
    rw [hN] at hgN
    exact hgN
  have horbit7 : ∀ a ∈ orbitOf G v, a ≠ v → 7 ≤ (MulAction.orbit ↥S a).ncard := by
    intro a ha hav
    by_contra hlt
    push Not at hlt
    have hKidx := MulAction.index_stabilizer ↥S a
    have := Subgroup.normalCore_normal (MulAction.stabilizer ↥S a)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (MulAction.stabilizer ↥S a).normalCore with h | h
    · have hfact := Subgroup.index_normalCore_dvd_factorial_index
        (H := MulAction.stabilizer ↥S a)
      rw [h, Subgroup.index_bot, hKidx] at hfact
      have h7' := (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 7)).mp (h7.trans hfact)
      omega
    · obtain ⟨g₀, hg₀, rfl⟩ := ha
      apply hav
      exact hfixpt ⟨g₀, hg₀⟩ fun h' =>
        Subgroup.normalCore_le _ (h ▸ Subgroup.mem_top h')
  have hhv : ∀ h : ↥S, ((h : ↥G) : MulAut V) v = v := fun h => h.2
  have hmul : ∀ (h : ↥S) (a : V), v * ((h : ↥G) : MulAut V) a = ((h : ↥G) : MulAut V) (v * a) :=
    fun h a => by rw [map_mul, hhv]
  set Ω₁ : Set V := {a | a ∈ orbitOf G v ∧ a ≠ v ∧ v * a ∈ orbitOf G v} with hΩ₁
  set Ω₂ : Set V := {a | a ∈ orbitOf G v ∧ a ≠ v ∧ v * a ∉ orbitOf G v} with hΩ₂
  have hinv₁ : ∀ a ∈ Ω₁, MulAction.orbit ↥S a ⊆ Ω₁ := by
    rintro a ⟨ha, hav, hva⟩ _ ⟨h, rfl⟩
    show ((h : ↥G) : MulAut V) a ∈ _
    refine ⟨smul_mem_orbitOf (h : ↥G).2 ha, fun he => hav ?_, ?_⟩
    · exact ((h : ↥G) : MulAut V).injective (he.trans (hhv h).symm)
    · rw [hmul]
      exact smul_mem_orbitOf (h : ↥G).2 hva
  have hinv₂ : ∀ a ∈ Ω₂, MulAction.orbit ↥S a ⊆ Ω₂ := by
    rintro a ⟨ha, hav, hva⟩ _ ⟨h, rfl⟩
    show ((h : ↥G) : MulAut V) a ∈ _
    refine ⟨smul_mem_orbitOf (h : ↥G).2 ha, fun he => hav ?_, ?_⟩
    · exact ((h : ↥G) : MulAut V).injective (he.trans (hhv h).symm)
    · rw [hmul]
      intro hm
      apply hva
      have := smul_mem_orbitOf (G.inv_mem (h : ↥G).2) hm
      rwa [MulAut.inv_apply_self] at this
  have hvv : v * v = 1 := by
    have := hV v
    rwa [pow_two] at this
  have heven : Even (Nat.card Ω₁) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let f : Function.End Ω₁ := fun a => ⟨v * a, a.2.2.2, fun he => by
      apply h1Ω
      have : (a : V) = 1 := by
        calc (a : V) = v⁻¹ * (v * a) := by group
          _ = 1 := by rw [he, inv_mul_cancel]
      rw [← this]
      exact a.2.1, by
        rw [← mul_assoc, hvv, one_mul]
        exact a.2.1⟩
    have hf : f ^ 2 = 1 := by
      funext a
      apply Subtype.ext
      show v * (v * (a : V)) = a
      rw [← mul_assoc, hvv, one_mul]
    have h := card_fix_modEq_end 2 f hf
    have h0 : Nat.card {x // f x = x} = 0 := by
      rw [Nat.card_eq_zero]
      left
      constructor
      rintro ⟨a, ha⟩
      apply hv1
      have : v * (a : V) = a := congrArg Subtype.val ha
      calc v = v * a * (a : V)⁻¹ := by group
        _ = 1 := by rw [this, mul_inv_cancel]
    rw [h0] at h
    exact Nat.even_iff.mpr h
  have hne₁ : Ω₁.Nonempty := by
    obtain ⟨k, hk, rfl⟩ := hx₀
    refine ⟨k⁻¹ y₀, smul_mem_orbitOf (G.inv_mem hk) hy₀, fun he => hxy ?_, ?_⟩
    · rw [← he, MulAut.apply_inv_self]
    · have e : v * k⁻¹ y₀ = k⁻¹ (k v * y₀) := by rw [map_mul, MulAut.inv_apply_self]
      rw [e]
      exact smul_mem_orbitOf (G.inv_mem hk) hxy₀
  have hfin : (orbitOf G v).Finite := Set.toFinite _
  have hall : ∀ a ∈ orbitOf G v, a ≠ v → v * a ∈ orbitOf G v := by
    by_contra hc
    push Not at hc
    obtain ⟨a₂, ha₂, ha₂v, ha₂n⟩ := hc
    obtain ⟨a₁, ha₁⟩ := hne₁
    have hfin₁ : Ω₁.Finite := hfin.subset fun a ha => ha.1
    have hfin₂ : Ω₂.Finite := hfin.subset fun a ha => ha.1
    have hdisj : Disjoint Ω₁ Ω₂ :=
      Set.disjoint_left.mpr fun a h₁ h₂ => h₂.2.2 h₁.2.2
    have hunion : Ω₁ ∪ Ω₂ = orbitOf G v \ {v} := by
      ext a
      simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, hΩ₁, hΩ₂,
        Set.mem_ofPred_eq]
      tauto
    have hsum : Ω₁.ncard + Ω₂.ncard = 14 := by
      rw [← Set.ncard_union_eq hdisj hfin₁ hfin₂, hunion,
        Set.ncard_sdiff_singleton_of_mem hvΩ, ← Nat.card_coe_set_eq, hΩ]
    have h₁ : 7 ≤ Ω₁.ncard :=
      (horbit7 a₁ ha₁.1 ha₁.2.1).trans (Set.ncard_le_ncard (hinv₁ a₁ ha₁) hfin₁)
    have h₂ : 7 ≤ Ω₂.ncard :=
      (horbit7 a₂ ha₂ ha₂v).trans (Set.ncard_le_ncard (hinv₂ a₂ ⟨ha₂, ha₂v, ha₂n⟩) hfin₂)
    rw [Nat.card_coe_set_eq] at heven
    obtain ⟨m, hm⟩ := heven
    omega
  intro a ha b hb hab
  obtain ⟨g₀, hg₀, rfl⟩ := ha
  have hb' : g₀⁻¹ b ∈ orbitOf G v := smul_mem_orbitOf (G.inv_mem hg₀) hb
  have hbv : g₀⁻¹ b ≠ v := fun he => hab (by rw [← he, MulAut.apply_inv_self])
  have e : g₀ v * b = g₀ (v * g₀⁻¹ b) := by rw [map_mul, MulAut.apply_inv_self]
  rw [e]
  exact smul_mem_orbitOf hg₀ (hall _ hb' hbv)

end CFSG.Quasithin.B412

end
