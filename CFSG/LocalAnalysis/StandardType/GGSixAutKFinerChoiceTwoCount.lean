module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoCase

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.StandardType

namespace ChoiceTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] {n : ℕ} {L : Type} [Field L]
  [Algebra K L] {ζ : L} {E : Subgroup (StatedSp n K)} (F : SpFrame K n ζ E)
  {ψ : StatedSp n K →* G} {Bs : Subgroup G}

namespace SpFrame

@[expose] def expSub (hζ : ζ ^ 3 = 1) (ψ : StatedSp n K →* G) (X : Subgroup G) :
    AddSubgroup (Fin F.s → ZMod 3) where
  carrier := {f | ψ (F.tor f) ∈ X}
  add_mem' {f f'} hf hf' := by
    change ψ (F.tor (f + f')) ∈ X
    rw [F.tor_add hζ, map_mul]
    exact X.mul_mem hf hf'
  zero_mem' := by
    change ψ (F.tor 0) ∈ X
    rw [F.tor_zero, map_one]
    exact X.one_mem
  neg_mem' {f} hf := by
    change ψ (F.tor (-f)) ∈ X
    have h1 : F.tor (-f) = (F.tor f)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← F.tor_add hζ, neg_add_cancel, F.tor_zero]
    rw [h1, map_inv]
    exact X.inv_mem hf

omit [Finite G] in
theorem mem_expSub (hζ : ζ ^ 3 = 1) {X : Subgroup G} {f : Fin F.s → ZMod 3} :
    f ∈ F.expSub hζ ψ X ↔ ψ (F.tor f) ∈ X := Iff.rfl

omit [Finite G] in
theorem smul_mem_expSub (hζ : ζ ^ 3 = 1) {X : Subgroup G} {f : Fin F.s → ZMod 3}
    (hf : f ∈ F.expSub hζ ψ X) (c : ZMod 3) : c • f ∈ F.expSub hζ ψ X := by
  have := AddSubgroup.nsmul_mem _ hf c.val
  rwa [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val] at this

theorem eq_sum_single_of_supp {s : ℕ} {U : Finset (Fin s)} {f : Fin s → ZMod 3}
    (hf : ∀ i, i ∉ U → f i = 0) : f = ∑ i ∈ U, (f i).val • Pi.single i (1 : ZMod 3) := by
  funext l
  rw [Finset.sum_apply]
  by_cases hl : l ∈ U
  · rw [Finset.sum_eq_single_of_mem l hl (fun i _ hil => by
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hil), smul_zero])]
    rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  · rw [hf l hl, Finset.sum_eq_zero fun i hi => by
      rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => hl (by rw [h]; exact hi)), smul_zero]]

theorem pow_card_le_of_single (hζo : IsPrimitiveRoot ζ 3) (hψ : Function.Injective ψ)
    (hBs : ∀ g, g ∈ Bs ↔ ∃ f, ψ (F.tor f) = g) (X : Subgroup G) (U : Finset (Fin F.s))
    (hU : ∀ i ∈ U, ψ (F.tor (Pi.single i 1)) ∈ Subgroup.centralizer (X : Set G)) :
    3 ^ U.card ≤ Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
  classical
  have hζ := hζo.pow_eq_one
  have hsupp : ∀ f : Fin F.s → ZMod 3, (∀ i, i ∉ U → f i = 0) →
      ψ (F.tor f) ∈ Subgroup.centralizer (X : Set G) := by
    intro f hf
    rw [← F.mem_expSub hζ, eq_sum_single_of_supp hf]
    exact AddSubgroup.sum_mem _ fun i hi => AddSubgroup.nsmul_mem _ (hU i hi) _
  set ext : (U → ZMod 3) → Fin F.s → ZMod 3 :=
    fun e i => if h : i ∈ U then e ⟨i, h⟩ else 0 with hext
  have hextU : ∀ e i, i ∉ U → ext e i = 0 := fun e i hi => by simp [hext, hi]
  let φ : (U → ZMod 3) → (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := fun e =>
    ⟨ψ (F.tor (ext e)), (hBs _).mpr ⟨_, rfl⟩, hsupp _ (hextU e)⟩
  have hφ : Function.Injective φ := by
    intro e e' h
    have h1 : ext e = ext e' :=
      F.tor_injective hζo (hψ (congrArg Subtype.val h))
    funext i
    have := congrFun h1 i
    simpa [hext] using this
  have h1 := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_coe] at h1

omit [Finite G] in
theorem exists_basis (hζo : IsPrimitiveRoot ζ 3) (hψ : Function.Injective ψ)
    (hBs : ∀ g, g ∈ Bs ↔ ∃ f, ψ (F.tor f) = g) {D : Subgroup G} (hDB : D ≤ Bs)
    (hD9 : Nat.card D = 9) :
    ∃ t₁ t₂ : Fin F.s → ZMod 3, (∀ a, a ≠ 0 → comb2 t₁ t₂ a ≠ 0) ∧
      ∀ g, g ∈ D ↔ ∃ a, ψ (F.tor (comb2 t₁ t₂ a)) = g := by
  classical
  have hζ := hζo.pow_eq_one
  set KD := F.expSub hζ ψ D with hKD
  have hcard : Nat.card KD = 9 := by
    rw [← hD9]
    refine Nat.card_congr (Equiv.ofBijective (fun f => (⟨ψ (F.tor f), f.2⟩ : D)) ⟨?_, ?_⟩)
    · intro f f' h
      exact Subtype.ext (F.tor_injective hζo (hψ (congrArg Subtype.val h)))
    · intro d
      obtain ⟨f, hf⟩ := (hBs d).mp (hDB d.2)
      exact ⟨⟨f, show ψ (F.tor f) ∈ D by rw [hf]; exact d.2⟩, Subtype.ext hf⟩
  have hmult : ∀ t : Fin F.s → ZMod 3,
      Nat.card {f // ∃ c : ZMod 3, f = c • t} ≤ 3 := fun t => by
    have := Nat.card_le_card_of_surjective (fun c : ZMod 3 => (⟨c • t, c, rfl⟩ :
      {f // ∃ c : ZMod 3, f = c • t})) (fun ⟨f, c, hc⟩ => ⟨c, Subtype.ext hc.symm⟩)
    rwa [Nat.card_zmod] at this
  obtain ⟨t₁, ht₁K, ht₁⟩ : ∃ t ∈ KD, t ≠ 0 := by
    by_contra h
    push Not at h
    have : Nat.card KD ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun f f' => Subtype.ext ((h f f.2).trans (h f' f'.2).symm)⟩
    omega
  obtain ⟨t₂, ht₂K, ht₂⟩ : ∃ t ∈ KD, ∀ c : ZMod 3, t ≠ c • t₁ := by
    by_contra h
    push Not at h
    have : Nat.card KD ≤ Nat.card {f // ∃ c : ZMod 3, f = c • t₁} :=
      Nat.card_le_card_of_injective (fun f => (⟨f.1, h f.1 f.2⟩ : {f // ∃ c : ZMod 3, f = c • t₁}))
        fun f f' hff => Subtype.ext (Subtype.mk.inj hff)
    have := hmult t₁
    omega
  have hind : ∀ a, a ≠ 0 → comb2 t₁ t₂ a ≠ 0 := by
    intro a ha h0
    rw [comb2] at h0
    by_cases ha2 : a.2 = 0
    · have ha1 : a.1 ≠ 0 := fun h1 => ha (Prod.ext h1 ha2)
      rw [ha2, zero_smul, add_zero] at h0
      apply ht₁
      have := congrArg (fun f => a.1⁻¹ • f) h0
      simpa [smul_smul, inv_mul_cancel₀ ha1] using this
    · apply ht₂ (-(a.2⁻¹ * a.1))
      have h1 : a.2 • t₂ = -(a.1 • t₁) := eq_neg_of_add_eq_zero_right h0
      have := congrArg (fun f => a.2⁻¹ • f) h1
      simp only [smul_smul, inv_mul_cancel₀ ha2, one_smul, smul_neg] at this
      rw [this, neg_smul]
  refine ⟨t₁, t₂, hind, fun g => ⟨fun hg => ?_, fun ⟨a, ha⟩ => ?_⟩⟩
  ·
    obtain ⟨f, hf⟩ := (hBs g).mp (hDB hg)
    have hfK : f ∈ KD := show ψ (F.tor f) ∈ D by rw [hf]; exact hg
    have hinj : Function.Injective fun a : ZMod 3 × ZMod 3 =>
        (⟨comb2 t₁ t₂ a, KD.add_mem (F.smul_mem_expSub hζ ht₁K a.1)
          (F.smul_mem_expSub hζ ht₂K a.2)⟩ : KD) := by
      intro a a' h
      have h1 : comb2 t₁ t₂ a = comb2 t₁ t₂ a' := congrArg Subtype.val h
      by_contra hne
      apply hind (a - a') (sub_ne_zero.mpr hne)
      simp only [comb2] at h1 ⊢
      rw [Prod.fst_sub, Prod.snd_sub, sub_smul, sub_smul]
      rw [← sub_eq_zero] at h1
      rw [← h1]
      abel
    have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card]; rfl)
    obtain ⟨a, ha⟩ := hbij.2 ⟨f, hfK⟩
    exact ⟨a, by rw [← hf]; exact congrArg (fun y => ψ (F.tor y)) (congrArg Subtype.val ha)⟩
  · rw [← ha]
    exact KD.add_mem (F.smul_mem_expSub hζ ht₁K a.1) (F.smul_mem_expSub hζ ht₂K a.2)

end SpFrame

end ChoiceTwo

end CFSG.StandardType
