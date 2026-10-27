module

public import CFSG.Quasithin.Recognition.CertTwoLocal
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsMod
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAutMain
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13.Sec53F.Yam

open scoped Pointwise
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.Sec53F
  CFSG.Quasithin.H13.Sec53F.BA

theorem map_symm_map {C : Type} [Group C] (φ : C ≃* C) (M : Subgroup C) :
    (M.map φ.toMonoidHom).map φ.symm.toMonoidHom = M := by
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    simpa using hm
  · intro hg
    exact ⟨φ g, ⟨g, hg, rfl⟩, by simp⟩

structure YamStd (C : Type) [Group C] (U P₀ P₁ : Subgroup C) : Prop where
  sylow : IsSylowTwoOf U ⊤
  no_normal : ∀ R : Subgroup C, R.Normal → IsPGroup 2 ↥R → R = ⊥
  ne : P₀ ≠ P₁
  le₀ : Subgroup.normalizer (U : Set C) ≤ P₀
  le₁ : Subgroup.normalizer (U : Set C) ≤ P₁
  coatom₀ : IsCoatom P₀
  coatom₁ : IsCoatom P₁
  above : ∀ A : Subgroup C, Subgroup.normalizer (U : Set C) ≤ A → A ≠ ⊤ → A ≤ P₀ ∨ A ≤ P₁
  twoLoc₀ : IsTwoLocal P₀
  twoLoc₁ : IsTwoLocal P₁

namespace YamStd

variable {C : Type} [Group C] {U P₀ P₁ : Subgroup C} (S : YamStd C U P₀ P₁)

include S

theorem ne_top_of_isTwoLocal {M : Subgroup C} (hM : IsTwoLocal M) : M ≠ ⊤ := by
  obtain ⟨R, hR1, hR2, rfl⟩ := hM
  intro htop
  exact hR1 (S.no_normal R (Subgroup.normalizer_eq_top_iff.mp htop) hR2)

theorem isMaximalTwoLocal₀ : IsMaximalTwoLocal P₀ := by
  refine ⟨S.twoLoc₀, fun M' hM' hle => ?_⟩
  rcases S.coatom₀.le_iff.mp hle with h | h
  · exact absurd h (S.ne_top_of_isTwoLocal hM')
  · exact h

theorem isMaximalTwoLocal₁ : IsMaximalTwoLocal P₁ := by
  refine ⟨S.twoLoc₁, fun M' hM' hle => ?_⟩
  rcases S.coatom₁.le_iff.mp hle with h | h
  · exact absurd h (S.ne_top_of_isTwoLocal hM')
  · exact h

theorem eq_or_eq {M : Subgroup C} (hM : IsMaximalTwoLocal M)
    (hN : Subgroup.normalizer (U : Set C) ≤ M) : M = P₀ ∨ M = P₁ := by
  rcases S.above M hN (S.ne_top_of_isTwoLocal hM.1) with h | h
  · exact Or.inl (hM.2 P₀ S.twoLoc₀ h).symm
  · exact Or.inr (hM.2 P₁ S.twoLoc₁ h).symm

theorem isYAmalgamPair : IsYAmalgamPair U P₀ P₁ := by
  refine ⟨S.sylow, S.ne, fun M => ⟨fun ⟨hM, hN⟩ => S.eq_or_eq hM hN, ?_⟩⟩
  rintro (rfl | rfl)
  · exact ⟨S.isMaximalTwoLocal₀, S.le₀⟩
  · exact ⟨S.isMaximalTwoLocal₁, S.le₁⟩

theorem pair [Finite C] {Y : Type} [Group Y] (e : Y ≃* C) {TY M₁ M₂ : Subgroup Y}
    (h : IsYAmalgamPair TY M₁ M₂) :
    ∃ c : C, TY.map e.toMonoidHom = U.map (MulAut.conj c).toMonoidHom ∧
      ((M₁.map e.toMonoidHom = P₀.map (MulAut.conj c).toMonoidHom ∧
          M₂.map e.toMonoidHom = P₁.map (MulAut.conj c).toMonoidHom) ∨
        (M₁.map e.toMonoidHom = P₁.map (MulAut.conj c).toMonoidHom ∧
          M₂.map e.toMonoidHom = P₀.map (MulAut.conj c).toMonoidHom)) := by
  have h' := IsYAmalgamPair.map e h
  obtain ⟨c, -, hc⟩ := S.sylow.exists_conj h'.1
  let φ : C ≃* C := (MulAut.conj c).symm
  have h'' := IsYAmalgamPair.map φ h'
  have hU : (TY.map e.toMonoidHom).map φ.toMonoidHom = U := by
    rw [hc]
    exact map_symm_map (MulAut.conj c) U
  rw [hU] at h''
  obtain ⟨hM1, hN1⟩ := (h''.2.2 ((M₁.map e.toMonoidHom).map φ.toMonoidHom)).2 (Or.inl rfl)
  obtain ⟨hM2, hN2⟩ := (h''.2.2 ((M₂.map e.toMonoidHom).map φ.toMonoidHom)).2 (Or.inr rfl)
  have hne : (M₁.map e.toMonoidHom).map φ.toMonoidHom ≠
      (M₂.map e.toMonoidHom).map φ.toMonoidHom := h''.2.1
  have key : ∀ M X : Subgroup C, M.map φ.toMonoidHom = X →
      M = X.map (MulAut.conj c).toMonoidHom := by
    intro M X hX
    rw [← hX]
    exact (map_symm_map φ M).symm
  refine ⟨c, hc, ?_⟩
  rcases S.eq_or_eq hM1 hN1 with a | a <;> rcases S.eq_or_eq hM2 hN2 with b | b
  · exact absurd (a.trans b.symm) hne
  · exact Or.inl ⟨key _ _ a, key _ _ b⟩
  · exact Or.inr ⟨key _ _ a, key _ _ b⟩
  · exact absurd (a.trans b.symm) hne

end YamStd

section Facts

variable {P P' : Type} [Group P] [Group P']

@[expose] def LieFactsOf (T N₁ N₂ : Subgroup P) : Prop :=
  TransFacts N₁ N₂ ∧ N₁ ⊓ N₂ ≤ Subgroup.normalizer (T : Set P) ∧ T ≤ perfectCore N₁ ∧
    T ≤ perfectCore N₂

theorem LieFactsOf.swap {T N₁ N₂ : Subgroup P} (h : LieFactsOf T N₁ N₂) : LieFactsOf T N₂ N₁ := by
  obtain ⟨⟨hs, h1, h2⟩, hn, hT1, hT2⟩ := h
  exact ⟨⟨by rwa [inf_comm], h2, h1⟩, by rwa [inf_comm], hT2, hT1⟩

theorem centerOf_map_equiv (e : P ≃* P') (X : Subgroup P) :
    centerOf (X.map e.toMonoidHom) = (centerOf X).map e.toMonoidHom := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, Subgroup.mem_centralizer_iff.mpr fun x' hx' => e.injective ?_⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc (e x') ⟨x', hx', rfl⟩
    rw [map_mul, map_mul]
    exact this
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨x', hx', rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc x' hx'
    change e x' * e x = e x * e x'
    rw [← map_mul, ← map_mul, this]

theorem transFacts_map {N₁ N₂ : Subgroup P} (h : TransFacts N₁ N₂) (e : P ≃* P') :
    TransFacts (N₁.map e.toMonoidHom) (N₂.map e.toMonoidHom) := by
  have hc : ∀ N : Subgroup P, centerOf (perfectCore (N.map e.toMonoidHom)) =
      (centerOf (perfectCore N)).map e.toMonoidHom := fun N => by
    rw [perfectCore_map_inj e.toMonoidHom e.injective N, centerOf_map_equiv]
  have key : ∀ N : Subgroup P, (∀ a ∈ centerOf (perfectCore N), ∀ a' ∈ centerOf (perfectCore N),
      a ≠ 1 → a' ≠ 1 → ∃ m ∈ N, m * a * m⁻¹ = a') →
      ∀ a ∈ centerOf (perfectCore (N.map e.toMonoidHom)),
        ∀ a' ∈ centerOf (perfectCore (N.map e.toMonoidHom)), a ≠ 1 → a' ≠ 1 →
          ∃ m ∈ N.map e.toMonoidHom, m * a * m⁻¹ = a' := by
    intro N hN a ha a' ha' h1 h1'
    rw [hc N] at ha ha'
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨x', hx', rfl⟩ := ha'
    obtain ⟨m, hm, hmx⟩ := hN x hx x' hx' (fun h0 => h1 (by rw [h0, map_one]))
      (fun h0 => h1' (by rw [h0, map_one]))
    exact ⟨e m, ⟨m, hm, rfl⟩, by
      have h3 := congrArg e hmx
      simpa [map_mul, map_inv] using h3⟩
  refine ⟨?_, key N₁ h.trans₁, key N₂ h.trans₂⟩
  rw [← Subgroup.map_inf N₁ N₂ e.toMonoidHom e.injective]
  have := h.solv
  exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective (N₁ ⊓ N₂)
    e.toMonoidHom e.injective).toMonoidHom)
    (Subgroup.equivMapOfInjective (N₁ ⊓ N₂) e.toMonoidHom e.injective).surjective

theorem LieFactsOf.map {T N₁ N₂ : Subgroup P} (h : LieFactsOf T N₁ N₂) (e : P ≃* P') :
    LieFactsOf (T.map e.toMonoidHom) (N₁.map e.toMonoidHom) (N₂.map e.toMonoidHom) := by
  obtain ⟨hT, hn, h1, h2⟩ := h
  refine ⟨transFacts_map hT e, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_inf N₁ N₂ e.toMonoidHom e.injective,
      ← Subgroup.map_equiv_normalizer_eq T e]
    exact Subgroup.map_mono hn
  · rw [perfectCore_map_inj e.toMonoidHom e.injective N₁]
    exact Subgroup.map_mono h1
  · rw [perfectCore_map_inj e.toMonoidHom e.injective N₂]
    exact Subgroup.map_mono h2

theorem lieFactsOf_of_yamStd {C : Type} [Group C] [Finite C] {U P₀ P₁ : Subgroup C}
    (S : YamStd C U P₀ P₁) (F : LieFactsOf U P₀ P₁) {Y : Type} [Group Y] (e : Y ≃* C)
    {TY M₁ M₂ : Subgroup Y} (h : IsYAmalgamPair TY M₁ M₂) : LieFactsOf TY M₁ M₂ := by
  obtain ⟨c, hT, hM⟩ := S.pair e h
  have hF := F.map (MulAut.conj c)
  have back : ∀ (N : Subgroup Y) (X : Subgroup C), N.map e.toMonoidHom = X →
      N = X.map e.symm.toMonoidHom := by
    intro N X hX
    rw [← hX]
    ext y
    simp
  have hF' : LieFactsOf (TY.map e.toMonoidHom) (M₁.map e.toMonoidHom) (M₂.map e.toMonoidHom) := by
    rcases hM with ⟨a, b⟩ | ⟨a, b⟩
    · rw [hT, a, b]
      exact hF
    · rw [hT, a, b]
      exact hF.swap
  have := hF'.map e.symm
  rwa [← back TY _ rfl, ← back M₁ _ rfl, ← back M₂ _ rfl] at this

end Facts

end CFSG.Quasithin.H13.Sec53F.Yam
