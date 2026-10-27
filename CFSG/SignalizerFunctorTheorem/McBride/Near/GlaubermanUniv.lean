module

public import CFSG.SignalizerFunctorTheorem.SolvableTheorem
public import CFSG.SignalizerFunctorTheorem.McBride.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

universe u

theorem isSolvableSignalizerFunctor_of_isFunctor {G : Type*} [Group G] {p : ℕ} {A : Subgroup G}
    {θ : G → Subgroup G} (hθ : IsFunctor p A θ)
    (hs : ∀ a ∈ A, a ≠ 1 → Group.IsSolvable (θ a)) : IsSolvableSignalizerFunctor p A θ where
  le_centralizer := hθ.le_centralizer
  coprime := hθ.coprime
  invariant a ha ha1 _ hx :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hθ.normalized a ha ha1 hx)
  balance := hθ.balance
  solvable := hs

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem card_comap_mulEquiv (e : H ≃* G) (K : Subgroup G) :
    Nat.card (K.comap (e : H →* G)) = Nat.card K := by
  rw [Subgroup.comap_equiv_eq_map_symm]
  exact Subgroup.card_map_of_injective e.symm.injective

theorem isSolvable_comap_mulEquiv (e : H ≃* G) (K : Subgroup G) (hK : Group.IsSolvable K) :
    Group.IsSolvable (K.comap (e : H →* G)) := by
  have hinj : Function.Injective ((e : H →* G).subgroupComap K) := by
    intro x y hxy
    exact Subtype.ext (e.injective (congrArg Subtype.val hxy))
  exact Group.isSolvable_of_isSolvable_injective hinj

theorem isSolvable_of_isSolvable_comap_mulEquiv (e : H ≃* G) (K : Subgroup G)
    (hK : Group.IsSolvable (K.comap (e : H →* G))) : Group.IsSolvable K := by
  have hsurj : Function.Surjective ((e : H →* G).subgroupComap K) := fun w =>
    ⟨⟨e.symm w, by simp⟩, Subtype.ext (by
      change e (e.symm w) = w
      simp)⟩
  have := hK
  exact Group.isSolvable_of_surjective hsurj

theorem iSup_comap_equiv (e : H ≃* G) (A : Subgroup G) (θ : G → Subgroup G) :
    (⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), θ a).comap (e : H →* G) =
      ⨆ (x : H) (_ : x ∈ A.comap (e : H →* G)) (_ : x ≠ 1),
        (θ (e x)).comap (e : H →* G) := by
  apply le_antisymm
  · rw [Subgroup.comap_equiv_eq_map_symm, Subgroup.map_le_iff_le_comap]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    intro y hy
    refine Subgroup.mem_iSup_of_mem (e.symm a) (Subgroup.mem_iSup_of_mem ?_
      (Subgroup.mem_iSup_of_mem ?_ ?_))
    · simpa using ha
    · simpa using ha1
    · simpa using hy
  · refine iSup_le fun x => iSup_le fun hx => iSup_le fun hx1 => ?_
    refine Subgroup.comap_mono (le_iSup_of_le (e x) (le_iSup_of_le hx (le_iSup_of_le ?_ le_rfl)))
    simpa using hx1

theorem isSolvableSignalizerFunctor_comap (e : H ≃* G) {p : ℕ} {A : Subgroup G}
    {θ : G → Subgroup G} (hθ : IsSolvableSignalizerFunctor p A θ) :
    IsSolvableSignalizerFunctor p (A.comap (e : H →* G))
      (fun x => (θ (e x)).comap (e : H →* G)) where
  le_centralizer a ha ha1 y hy := by
    have hne : e a ≠ 1 := by simpa using ha1
    have hy' : e y ∈ θ (e a) := hy
    have := hθ.le_centralizer (e a) ha hne hy'
    rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
    exact e.injective (by simpa using this)
  coprime a ha ha1 := by
    have hne : e a ≠ 1 := by simpa using ha1
    rw [card_comap_mulEquiv]
    exact hθ.coprime (e a) ha hne
  invariant a ha ha1 x hx := by
    have hne : e a ≠ 1 := by simpa using ha1
    have hnorm : e x ∈ Subgroup.normalizer ((θ (e a) : Subgroup G) : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hθ.invariant (e a) ha hne (e x) hx)
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simpa using Subgroup.mem_normalizer_iff.mp hnorm (e h)
  balance a ha ha1 b hb hb1 y hy := by
    have hne : e a ≠ 1 := by simpa using ha1
    have hne' : e b ≠ 1 := by simpa using hb1
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    have hy1' : e y ∈ θ (e a) := hy1
    have hy2' : e y ∈ Subgroup.centralizer {e b} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hy2 ⊢
      simpa using congrArg e hy2
    exact hθ.balance (e a) ha hne (e b) hb hne' (Subgroup.mem_inf.mpr ⟨hy1', hy2'⟩)
  solvable a ha ha1 := by
    have hne : e a ≠ 1 := by simpa using ha1
    exact isSolvable_comap_mulEquiv e _ (hθ.solvable (e a) ha hne)

end Transport

theorem glauberman_solvable_signalizer_functor_univ {G : Type u} [Group G] [Finite G] (p : ℕ)
    (hp : p.Prime) (A : Subgroup G) (hA : IsMulCommutative A) (hexp : ∀ a ∈ A, a ^ p = 1)
    (hrank : p ^ 3 ∣ Nat.card A) (θ : G → Subgroup G)
    (hθ : IsSolvableSignalizerFunctor p A θ) :
    let W : Subgroup G := ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), θ a
    Nat.Coprime p (Nat.card W) ∧ Group.IsSolvable W ∧
      ∀ a ∈ A, a ≠ 1 → θ a = W ⊓ Subgroup.centralizer {a} := by
  intro W
  let e : Shrink.{0} G ≃* G := Shrink.mulEquiv
  have : Finite (Shrink.{0} G) := Finite.of_equiv G e.toEquiv.symm
  have hAc : IsMulCommutative (A.comap (e : Shrink.{0} G →* G)) :=
    Subgroup.comap_injective_isMulCommutative A e.injective
  have hcard : Nat.card (A.comap (e : Shrink.{0} G →* G)) = Nat.card A := card_comap_mulEquiv e A
  have key := CFSG.SignalizerFunctorTheorem.glauberman_solvable_signalizer_functor
    (Shrink.{0} G) p hp (A.comap (e : Shrink.{0} G →* G)) hAc
    (fun a ha => e.injective (by simpa using hexp (e a) ha)) (hcard ▸ hrank)
    (fun x => (θ (e x)).comap (e : Shrink.{0} G →* G)) (isSolvableSignalizerFunctor_comap e hθ)
  obtain ⟨hcop, hsol, hcen⟩ := key
  have hW : (⨆ (x : Shrink.{0} G) (_ : x ∈ A.comap (e : Shrink.{0} G →* G)) (_ : x ≠ 1),
      (θ (e x)).comap (e : Shrink.{0} G →* G)) = W.comap (e : Shrink.{0} G →* G) :=
    (iSup_comap_equiv e A θ).symm
  rw [hW] at hcop hsol hcen
  refine ⟨?_, ?_, ?_⟩
  · rwa [card_comap_mulEquiv] at hcop
  · exact isSolvable_of_isSolvable_comap_mulEquiv e W hsol
  · intro a ha ha1
    have hne : e.symm a ≠ 1 := by simpa using ha1
    have hmem : e.symm a ∈ A.comap (e : Shrink.{0} G →* G) := by simpa using ha
    have h1 := hcen (e.symm a) hmem hne
    ext y
    have h2 := SetLike.ext_iff.mp h1 (e.symm y)
    simp only [Subgroup.mem_comap, MonoidHom.coe_ofClass, MulEquiv.apply_symm_apply,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at h2 ⊢
    rw [h2]
    constructor
    · rintro ⟨hyW, hc⟩
      refine ⟨hyW, ?_⟩
      simpa using congrArg e hc
    · rintro ⟨hyW, hc⟩
      refine ⟨hyW, ?_⟩
      exact e.injective (by simpa using hc)

theorem pow_dvd_card_of_isElemAbelian {G : Type*} [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    {A : Subgroup G} (hA : IsElemAbelian p A) (hk : p ^ k ≤ Nat.card A) :
    p ^ k ∣ Nat.card A := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ :=
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A hA).exists_card_eq
  rw [hr] at hk ⊢
  exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).mp hk)

theorem exists_greatest_signalizer_of_isFunctor {G : Type u} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {A : Subgroup G} (hA : IsElemAbelian p A) (hrank : p ^ 3 ≤ Nat.card A)
    {θ : G → Subgroup G} (hθ : IsFunctor p A θ)
    (hs : ∀ a ∈ A, a ≠ 1 → Group.IsSolvable (θ a)) :
    ∃ W : Subgroup G, Group.IsSolvable W ∧ A ≤ Subgroup.normalizer (W : Set G) ∧
      Nat.Coprime p (Nat.card W) ∧
      (∀ a ∈ A, a ≠ 1 → W ⊓ Subgroup.centralizer {a} = θ a) ∧
      ∀ X : Subgroup G, A ≤ Subgroup.normalizer (X : Set G) → Nat.Coprime p (Nat.card X) →
        (∀ a ∈ A, a ≠ 1 → X ⊓ Subgroup.centralizer {a} ≤ θ a) → X ≤ W := by
  obtain ⟨hcop, hsol, hcen⟩ := glauberman_solvable_signalizer_functor_univ p hp A hA.1 hA.2
    (pow_dvd_card_of_isElemAbelian hp hA hrank) θ (isSolvableSignalizerFunctor_of_isFunctor hθ hs)
  refine ⟨_, hsol, ?_, hcop, fun a ha ha1 => (hcen a ha ha1).symm, ?_⟩
  · intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simp only [Subgroup.map_iSup]
    refine iSup_congr fun a => iSup_congr fun ha => iSup_congr fun ha1 => ?_
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hθ.normalized a ha ha1 hx)
  · intro X hAX hcopX hXθ
    have hrank2 : p ^ 2 ≤ Nat.card A := (Nat.pow_le_pow_right hp.pos (by norm_num)).trans hrank
    rw [← iSup_centralizer_nonidentity hp hA hrank2 hAX hcopX]
    exact iSup_mono fun a => iSup_mono fun ha => iSup_mono fun ha1 => hXθ a ha ha1

end CFSG.SignalizerFunctorTheorem.McBride.Near
