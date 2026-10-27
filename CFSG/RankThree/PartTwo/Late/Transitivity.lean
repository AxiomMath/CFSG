module

public import CFSG.RankThree.PartTwo.Late.Uniqueness
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG

variable {G : Type*} [Group G]

@[expose] def IsConjIn (W S T : Subgroup G) : Prop :=
  ∃ w ∈ W, T = S.map (MulAut.conj w).toMonoidHom

@[expose] def maxIn (𝒬 : Set (Subgroup G)) (Y : Subgroup G) : Set (Subgroup G) :=
  {S | Maximal (fun R => R ∈ 𝒬 ∧ R ≤ Y) S}

@[expose] def IsLocallyTransitive (W : Subgroup G) (𝒬 : Set (Subgroup G)) (Y : Subgroup G) :
    Prop :=
  ∀ S ∈ maxIn 𝒬 Y, ∀ T ∈ maxIn 𝒬 Y, IsConjIn (W ⊓ Y) S T

theorem map_conj_one (S : Subgroup G) : S.map (MulAut.conj (1 : G)).toMonoidHom = S := by
  ext x
  simp

theorem map_conj_map_conj (S : Subgroup G) (v w : G) :
    (S.map (MulAut.conj w).toMonoidHom).map (MulAut.conj v).toMonoidHom =
      S.map (MulAut.conj (v * w)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem isConjIn_refl (W S : Subgroup G) : IsConjIn W S S :=
  ⟨1, one_mem W, (map_conj_one S).symm⟩

theorem IsConjIn.symm {W S T : Subgroup G} (h : IsConjIn W S T) : IsConjIn W T S := by
  obtain ⟨w, hw, rfl⟩ := h
  refine ⟨w⁻¹, inv_mem hw, ?_⟩
  rw [map_conj_map_conj, inv_mul_cancel, map_conj_one]

theorem IsConjIn.trans {W S T U : Subgroup G} (h₁ : IsConjIn W S T) (h₂ : IsConjIn W T U) :
    IsConjIn W S U := by
  obtain ⟨w, hw, rfl⟩ := h₁
  obtain ⟨v, hv, rfl⟩ := h₂
  exact ⟨v * w, mul_mem hv hw, map_conj_map_conj S v w⟩

theorem IsConjIn.mono {W W' S T : Subgroup G} (h : IsConjIn W S T) (hW : W ≤ W') :
    IsConjIn W' S T := by
  obtain ⟨w, hw, rfl⟩ := h
  exact ⟨w, hW hw, rfl⟩

theorem maximal_map_conj {W : Subgroup G} {𝒬 : Set (Subgroup G)}
    (hW : ∀ S ∈ 𝒬, ∀ w ∈ W, S.map (MulAut.conj w).toMonoidHom ∈ 𝒬) {S : Subgroup G}
    (hS : Maximal (· ∈ 𝒬) S) {w : G} (hw : w ∈ W) :
    Maximal (· ∈ 𝒬) (S.map (MulAut.conj w).toMonoidHom) := by
  refine ⟨hW S hS.prop w hw, fun R hR hle => ?_⟩
  have hR' := hW R hR w⁻¹ (inv_mem hw)
  have hSR : S ≤ R.map (MulAut.conj w⁻¹).toMonoidHom := by
    have := Subgroup.map_mono (f := (MulAut.conj w⁻¹).toMonoidHom) hle
    rwa [map_conj_map_conj, inv_mul_cancel, map_conj_one] at this
  have hRS := hS.2 hR' hSR
  have := Subgroup.map_mono (f := (MulAut.conj w).toMonoidHom) hRS
  rwa [map_conj_map_conj, mul_inv_cancel, map_conj_one] at this

theorem le_normalizer_inf {A X Y : Subgroup G} (hX : A ≤ Subgroup.normalizer (X : Set G))
    (hY : A ≤ Subgroup.normalizer (Y : Set G)) :
    A ≤ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hX ha) h,
    Subgroup.mem_normalizer_iff.mp (hY ha) h]

variable [Finite G]

theorem isConjIn_of_local {W : Subgroup G} {𝒬 : Set (Subgroup G)}
    (hW : ∀ S ∈ 𝒬, ∀ w ∈ W, S.map (MulAut.conj w).toMonoidHom ∈ 𝒬) {n : ℕ}
    (hmax : ∀ S' T' : Subgroup G, Maximal (· ∈ 𝒬) S' → Maximal (· ∈ 𝒬) T' →
      n < Nat.card (S' ⊓ T' : Subgroup G) → IsConjIn W S' T')
    {S T Y R₁ R₂ : Subgroup G} (hS : Maximal (· ∈ 𝒬) S) (hT : Maximal (· ∈ 𝒬) T)
    (hY : IsLocallyTransitive W 𝒬 Y)
    (hR₁ : R₁ ∈ 𝒬) (hR₁S : R₁ ≤ S) (hR₁Y : R₁ ≤ Y) (hn₁ : n < Nat.card R₁)
    (hR₂ : R₂ ∈ 𝒬) (hR₂T : R₂ ≤ T) (hR₂Y : R₂ ≤ Y) (hn₂ : n < Nat.card R₂) :
    IsConjIn W S T := by
  obtain ⟨S₁, hRS₁, hS₁⟩ :=
    Finite.exists_le_maximal (p := fun R => R ∈ 𝒬 ∧ R ≤ Y) (a := R₁) ⟨hR₁, hR₁Y⟩
  obtain ⟨T₁, hRT₁, hT₁⟩ :=
    Finite.exists_le_maximal (p := fun R => R ∈ 𝒬 ∧ R ≤ Y) (a := R₂) ⟨hR₂, hR₂Y⟩
  obtain ⟨w, hw, hT₁eq⟩ := hY S₁ hS₁ T₁ hT₁
  obtain ⟨S', hS₁S', hS'⟩ := Finite.exists_le_maximal (p := (· ∈ 𝒬)) hS₁.prop.1
  have hwW : w ∈ W := (Subgroup.mem_inf.mp hw).1
  have h₁ : IsConjIn W S S' :=
    hmax S S' hS hS' (lt_of_lt_of_le hn₁ (Subgroup.card_le_of_le (le_inf hR₁S (hRS₁.trans hS₁S'))))
  have hR₂S' : R₂ ≤ S'.map (MulAut.conj w).toMonoidHom := by
    calc R₂ ≤ T₁ := hRT₁
      _ = S₁.map (MulAut.conj w).toMonoidHom := hT₁eq
      _ ≤ S'.map (MulAut.conj w).toMonoidHom := Subgroup.map_mono hS₁S'
  have h₂ : IsConjIn W (S'.map (MulAut.conj w).toMonoidHom) T :=
    hmax _ T (maximal_map_conj hW hS' hwW) hT
      (lt_of_lt_of_le hn₂ (Subgroup.card_le_of_le (le_inf hR₂S' hR₂T)))
  exact (h₁.trans ⟨w, hwW, rfl⟩).trans h₂

section Standard

variable {p : ℕ} [Fact p.Prime] {A W : Subgroup G} {𝒬 : Set (Subgroup G)}

theorem exists_max_pair {S T : Subgroup G} (hS : Maximal (· ∈ 𝒬) S) (hT : Maximal (· ∈ 𝒬) T)
    (hST : ¬ IsConjIn W S T) :
    ∃ S₀ T₀ : Subgroup G, Maximal (· ∈ 𝒬) S₀ ∧ Maximal (· ∈ 𝒬) T₀ ∧ ¬ IsConjIn W S₀ T₀ ∧
      Nat.card (S ⊓ T : Subgroup G) ≤ Nat.card (S₀ ⊓ T₀ : Subgroup G) ∧
      ∀ S' T' : Subgroup G, Maximal (· ∈ 𝒬) S' → Maximal (· ∈ 𝒬) T' →
        Nat.card (S₀ ⊓ T₀ : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) → IsConjIn W S' T' := by
  let P : Set (Subgroup G × Subgroup G) :=
    {x | Maximal (· ∈ 𝒬) x.1 ∧ Maximal (· ∈ 𝒬) x.2 ∧ ¬ IsConjIn W x.1 x.2}
  obtain ⟨x, hxP, hx⟩ := Set.exists_max_image P (fun x => Nat.card (x.1 ⊓ x.2 : Subgroup G))
    (Set.toFinite P) ⟨(S, T), hS, hT, hST⟩
  refine ⟨x.1, x.2, hxP.1, hxP.2.1, hxP.2.2, hx (S, T) ⟨hS, hT, hST⟩, fun S' T' hS' hT' hlt => ?_⟩
  by_contra hne
  exact absurd (hx (S', T') ⟨hS', hT', hne⟩) (not_le.mpr hlt)

theorem inf_eq_bot_of_not_isConjIn (hp : ∀ S ∈ 𝒬, IsPGroup p S)
    (hA : ∀ S ∈ 𝒬, A ≤ Subgroup.normalizer (S : Set G))
    (hsub : ∀ S ∈ 𝒬, ∀ R : Subgroup G, R ≤ S → A ≤ Subgroup.normalizer (R : Set G) → R ∈ 𝒬)
    (hW : ∀ S ∈ 𝒬, ∀ w ∈ W, S.map (MulAut.conj w).toMonoidHom ∈ 𝒬)
    (hN : ∀ D ∈ 𝒬, D ≠ ⊥ → IsLocallyTransitive W 𝒬 (Subgroup.normalizer (D : Set G)))
    {S T : Subgroup G} (hS : Maximal (· ∈ 𝒬) S) (hT : Maximal (· ∈ 𝒬) T)
    (hST : ¬ IsConjIn W S T) : S ⊓ T = ⊥ := by
  obtain ⟨S₀, T₀, hS₀, hT₀, hST₀, hle, hmax⟩ := exists_max_pair hS hT hST
  suffices hD : S₀ ⊓ T₀ = ⊥ by
    rw [hD, Subgroup.card_bot] at hle
    exact Subgroup.eq_bot_of_card_le _ hle
  by_contra hD
  set D := S₀ ⊓ T₀
  have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_inf (hA S₀ hS₀.prop) (hA T₀ hT₀.prop)
  have hD𝒬 : D ∈ 𝒬 := hsub S₀ hS₀.prop D inf_le_left hAD
  have hAND : A ≤ Subgroup.normalizer ((Subgroup.normalizer (D : Set G) : Subgroup G) : Set G) :=
    hAD.trans Subgroup.le_normalizer
  have grow : ∀ X : Subgroup G, Maximal (· ∈ 𝒬) X → D ≤ X → D ≠ X →
      Nat.card D < Nat.card (X ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) ∧
        X ⊓ Subgroup.normalizer (D : Set G) ∈ 𝒬 := by
    intro X hX hDX hne
    obtain ⟨x, hxX, hxD, hxN⟩ := exists_mem_normalizer_not_mem_of_lt (hp X hX.prop)
      (lt_of_le_of_ne hDX hne)
    refine ⟨Subgroup.card_lt_of_lt (lt_of_le_of_ne (le_inf hDX Subgroup.le_normalizer) ?_),
      hsub X hX.prop _ inf_le_left (le_normalizer_inf (hA X hX.prop) hAND)⟩
    intro heq
    exact hxD (heq ▸ (⟨hxX, hxN⟩ : x ∈ X ⊓ Subgroup.normalizer (D : Set G)))
  have hDS : D ≠ S₀ := fun h => hST₀ (by
    rw [hS₀.eq_of_le hT₀.prop (h ▸ inf_le_right)]
    exact isConjIn_refl W T₀)
  have hDT : D ≠ T₀ := fun h => hST₀ (by
    rw [← hT₀.eq_of_le hS₀.prop (h ▸ inf_le_left)]
    exact isConjIn_refl W T₀)
  obtain ⟨h₁, hR₁⟩ := grow S₀ hS₀ inf_le_left hDS
  obtain ⟨h₂, hR₂⟩ := grow T₀ hT₀ inf_le_right hDT
  exact hST₀ (isConjIn_of_local hW hmax hS₀ hT₀ (hN D hD𝒬 hD) hR₁ inf_le_left inf_le_right h₁
    hR₂ inf_le_left inf_le_right h₂)

theorem isConjIn_of_maximal (hp : ∀ S ∈ 𝒬, IsPGroup p S)
    (hA : ∀ S ∈ 𝒬, A ≤ Subgroup.normalizer (S : Set G))
    (hsub : ∀ S ∈ 𝒬, ∀ R : Subgroup G, R ≤ S → A ≤ Subgroup.normalizer (R : Set G) → R ∈ 𝒬)
    (hW : ∀ S ∈ 𝒬, ∀ w ∈ W, S.map (MulAut.conj w).toMonoidHom ∈ 𝒬)
    (hN : ∀ D ∈ 𝒬, D ≠ ⊥ → IsLocallyTransitive W 𝒬 (Subgroup.normalizer (D : Set G)))
    (hAab : IsMulCommutative A)
    (hC : ∀ a ∈ A, a ≠ 1 → IsLocallyTransitive W 𝒬 (Subgroup.centralizer {a}))
    (hmeet : ∀ S T : Subgroup G, Maximal (· ∈ 𝒬) S → Maximal (· ∈ 𝒬) T → ¬ IsConjIn W S T →
      S ⊓ T = ⊥ →
      ∃ a ∈ A, a ≠ 1 ∧ S ⊓ Subgroup.centralizer {a} ≠ ⊥ ∧ T ⊓ Subgroup.centralizer {a} ≠ ⊥)
    {S T : Subgroup G} (hS : Maximal (· ∈ 𝒬) S) (hT : Maximal (· ∈ 𝒬) T) : IsConjIn W S T := by
  by_contra hST
  obtain ⟨S₀, T₀, hS₀, hT₀, hST₀, -, hmax⟩ := exists_max_pair hS hT hST
  have hD := inf_eq_bot_of_not_isConjIn hp hA hsub hW hN hS₀ hT₀ hST₀
  obtain ⟨a, haA, ha1, hSa, hTa⟩ := hmeet S₀ T₀ hS₀ hT₀ hST₀ hD
  have hAC : A ≤ Subgroup.normalizer ((Subgroup.centralizer {a} : Subgroup G) : Set G) := by
    refine le_trans (fun b hb => ?_) Subgroup.le_normalizer
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hAab.is_comm.comm ⟨b, hb⟩ ⟨a, haA⟩)
  have hcard : ∀ X : Subgroup G, Maximal (· ∈ 𝒬) X → X ⊓ Subgroup.centralizer {a} ≠ ⊥ →
      Nat.card (S₀ ⊓ T₀ : Subgroup G) < Nat.card (X ⊓ Subgroup.centralizer {a} : Subgroup G) ∧
        X ⊓ Subgroup.centralizer {a} ∈ 𝒬 := by
    intro X hX hne
    refine ⟨?_, hsub X hX.prop _ inf_le_left (le_normalizer_inf (hA X hX.prop) hAC)⟩
    rw [hD, Subgroup.card_bot]
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  obtain ⟨h₁, hR₁⟩ := hcard S₀ hS₀ hSa
  obtain ⟨h₂, hR₂⟩ := hcard T₀ hT₀ hTa
  exact hST₀ (isConjIn_of_local hW hmax hS₀ hT₀ (hC a haA ha1) hR₁ inf_le_left inf_le_right h₁
    hR₂ inf_le_left inf_le_right h₂)

end Standard

theorem exists_ne_one_inf_centralizer_ne_bot {A S T : Subgroup G} (hA : IsE27 A)
    (hS : S ≠ ⊥) (hT : T ≠ ⊥) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hcS : Nat.Coprime 3 (Nat.card S))
    (hcT : Nat.Coprime 3 (Nat.card T)) :
    ∃ a ∈ A, a ≠ 1 ∧ S ⊓ Subgroup.centralizer {a} ≠ ⊥ ∧ T ⊓ Subgroup.centralizer {a} ≠ ⊥ := by
  have hlarge : 3 ^ (2 + 1) ≤ Nat.card A := by rw [hA.2]; norm_num
  have hB : ∀ X : Subgroup G, X ≠ ⊥ → A ≤ Subgroup.normalizer (X : Set G) →
      Nat.Coprime 3 (Nat.card X) →
      ∃ B : Subgroup G, B ≤ A ∧ Nat.card B = 9 ∧ X ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
    intro X hX hAX hcX
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 2
      Nat.prime_three A X hA.1 hlarge hAX hcX
    by_contra! hall
    apply hX
    rw [← hgen]
    refine le_bot_iff.mp (iSup₂_le fun B hB => ?_)
    exact (hall B hB.1 hB.2).le
  obtain ⟨B₁, hB₁A, hB₁, hSB⟩ := hB S hS hAS hcS
  obtain ⟨B₂, hB₂A, hB₂, hTB⟩ := hB T hT hAT hcT
  have hmeet : B₁ ⊓ B₂ ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective (fun x : B₁ × B₂ => (⟨(x.1 : G) * x.2, mul_mem
        (hB₁A x.1.2) (hB₂A x.2.2)⟩ : A)) := by
      rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
      have h' : (x₁ : G) * x₂ = y₁ * y₂ := congrArg Subtype.val h
      have hmem : (y₁ : G)⁻¹ * x₁ ∈ B₁ ⊓ B₂ := by
        refine Subgroup.mem_inf.mpr ⟨B₁.mul_mem (B₁.inv_mem y₁.2) x₁.2, ?_⟩
        have : (y₁ : G)⁻¹ * x₁ = y₂ * (x₂ : G)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_assoc, mul_inv_cancel, mul_one]
        rw [this]
        exact B₂.mul_mem y₂.2 (B₂.inv_mem x₂.2)
      rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have h₁ : x₁ = y₁ := Subtype.ext hmem.symm
      subst h₁
      have h₂ : (x₂ : G) = y₂ := mul_left_cancel h'
      rw [Subtype.ext h₂]
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hB₁, hB₂, hA.2] at hle
    omega
  obtain ⟨⟨a, haB⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hmeet
  obtain ⟨haB₁, haB₂⟩ := Subgroup.mem_inf.mp haB
  refine ⟨a, hB₁A haB₁, fun h => ha1 (Subtype.ext h), ?_, ?_⟩
  · intro hbot
    apply hSB
    rw [eq_bot_iff, ← hbot]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB₁))
  · intro hbot
    apply hTB
    rw [eq_bot_iff, ← hbot]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB₂))

end CFSG.RankThree.PartTwo.Late
