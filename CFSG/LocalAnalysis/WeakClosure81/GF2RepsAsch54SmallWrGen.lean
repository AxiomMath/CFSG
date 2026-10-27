module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512WrAbs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch80Wr

open Subgroup

variable {Y : Type*} [Group Y]

theorem eq_top_of_le_of_normalizer_le [Finite Y] {E : Subgroup Y} [E.Normal] (S : Sylow 2 Y)
    {M : Subgroup Y} (hEM : E ≤ M)
    (hNM : normalizer (((S : Subgroup Y) ⊓ E : Subgroup Y) : Set Y) ≤ M) : M = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq E S
  have hPmap : (P : Subgroup E).map E.subtype = (S : Subgroup Y) ⊓ E := by
    rw [hP, subgroupOf_map_subtype]
  have hfr := Sylow.normalizer_sup_eq_top P
  rw [hPmap] at hfr
  exact top_le_iff.mp (hfr ▸ sup_le hNM hEM)

theorem exists_abelian_of_model [Finite Y] {E : Subgroup Y} [E.Normal] (S : Sylow 2 Y)
    {K : Type*} [Group K] (e : ↥E ≃* K) (hK : WrModel K) :
    ¬ IsPGroup 2 ↥E ∧ ∃ A : Subgroup Y, A ≤ (S : Subgroup Y) ⊓ E ∧ IsMulCommutative ↥A ∧
      A.relIndex ((S : Subgroup Y) ⊓ E) = 2 ∧ A ≠ ⊥ ∧
      (S : Subgroup Y) ⊓ E ⊓ centralizer (((S : Subgroup Y) ⊓ E : Subgroup Y) : Set Y) ≠ ⊥ ∧
      normalizer (((S : Subgroup Y) ⊓ E : Subgroup Y) : Set Y) ≤ normalizer (A : Set Y) ∧
      E ≤ normalizer (((S : Subgroup Y) ⊓ E ⊓
        centralizer (((S : Subgroup Y) ⊓ E : Subgroup Y) : Set Y) : Subgroup Y) : Set Y) ⊔
        normalizer (A : Set Y) := by
  obtain ⟨P₀, A₀, hA₀P, hA₀, hA₀i, hZ, hgen, hP₀top⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Finite.of_equiv _ e.toEquiv
  set Z₀ := (P₀ : Subgroup K) ⊓ centralizer ((P₀ : Subgroup K) : Set K) with hZ₀
  have hE2 : ¬ IsPGroup 2 ↥E := by
    intro h
    have hK2 : IsPGroup 2 (⊤ : Subgroup K) := (h.of_equiv e).of_equiv Subgroup.topEquiv.symm
    exact hP₀top (P₀.is_maximal' hK2 le_top).symm
  obtain ⟨P, hP⟩ := CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq E S
  obtain ⟨g, hg₀⟩ := exists_map_conj_eq P₀ (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hg : (P₀ : Subgroup K).map (MulAut.conj g).toMonoidHom =
      (P : Subgroup E).map e.toMonoidHom := hg₀
  set φ : K →* Y := E.subtype.comp (e.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom) with hφ
  have hφinj : Function.Injective φ :=
    E.subtype_injective.comp (e.symm.injective.comp (MulAut.conj g).injective)
  have hPe : ((P : Subgroup E).map e.toMonoidHom).map e.symm.toMonoidHom = (P : Subgroup E) := by
    rw [map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ from
      MonoidHom.ext fun x => e.symm_apply_apply x, map_id]
  have hφP : (P₀ : Subgroup K).map φ = (S : Subgroup Y) ⊓ E := by
    have h1 : (P₀ : Subgroup K).map φ = (((P₀ : Subgroup K).map
        (MulAut.conj g).toMonoidHom).map e.symm.toMonoidHom).map E.subtype := by
      rw [hφ, map_map, map_map]
      rfl
    rw [h1, hg, hPe, hP, subgroupOf_map_subtype]
  have hcardZ : Nat.card ↥(Z₀.map φ) = Nat.card Z₀ := card_map_of_injective hφinj
  have hcardP : Nat.card ↥((P₀ : Subgroup K).map φ) = Nat.card P₀ := card_map_of_injective hφinj
  set T₀ := (S : Subgroup Y) ⊓ E
  have hZT : Z₀.map φ = T₀ ⊓ centralizer (T₀ : Set Y) := by
    rw [hZ₀, map_inf_centralizer_of_injective hφinj, hφP]
  have hP₀bot : (P₀ : Subgroup K) ≠ ⊥ := by
    intro h
    rw [h, relIndex_bot_right] at hA₀i
    exact absurd hA₀i (by norm_num)
  have hZ₀bot : Z₀ ≠ ⊥ := by
    have : Nontrivial ↥(P₀ : Subgroup K) := (nontrivial_iff_ne_bot _).mpr hP₀bot
    have := P₀.isPGroup'.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : center ↥(P₀ : Subgroup K))
    intro hbot
    have hzZ : ((z : ↥P₀) : K) ∈ Z₀ := by
      refine mem_inf.mpr ⟨(z : ↥P₀).2, mem_centralizer_iff.mpr fun y hy => ?_⟩
      have := mem_center_iff.mp z.2 ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [hbot, mem_bot] at hzZ
    exact hz1 (Subtype.ext (Subtype.ext hzZ))
  have hA₀bot : A₀ ≠ ⊥ := by
    intro h
    rw [h, relIndex_bot_left] at hA₀i
    have : 0 < Nat.card Z₀ := Nat.card_pos
    omega
  have hC₂ : A₀.map φ ≤ T₀ := hφP ▸ map_mono hA₀P
  have hA : IsMulCommutative ↥(A₀.map φ) := by
    have := hA₀
    exact inferInstance
  have hAi : (A₀.map φ).relIndex T₀ = 2 := by
    rw [← hφP, relIndex_map_map_of_injective _ _ hφinj, hA₀i]
  refine ⟨hE2, A₀.map φ, hC₂, hA, hAi, (map_eq_bot_iff_of_injective _ hφinj).not.mpr hA₀bot,
    ?_, ?_, ?_⟩
  · rw [← hZT]
    exact (map_eq_bot_iff_of_injective _ hφinj).not.mpr hZ₀bot
  ·
    intro y hy
    rw [mem_normalizer_iff_map_conj_eq] at hy ⊢
    have : Finite ↥T₀ := inferInstance
    refine eq_of_isCommutative_of_relIndex_two (P := T₀) ?_ hC₂ ?_ hA ?_ hAi ?_
    · exact hy ▸ map_mono hC₂
    · have := hA
      exact inferInstance
    · rw [← hy, relIndex_map_map_of_injective _ _ (MulAut.conj y).injective, hAi]
    · rw [← hZT, hcardZ, ← hφP, hcardP]
      exact hZ
  ·
    rw [← hZT]
    intro x hx
    have hxφ : x ∈ (⊤ : Subgroup K).map φ :=
      ⟨(MulAut.conj g).symm (e ⟨x, hx⟩), mem_top _, by simp [hφ, mul_assoc]⟩
    rw [← hgen, Subgroup.map_sup] at hxφ
    exact sup_le_sup (le_normalizer_map φ) (le_normalizer_map φ) hxφ

end CFSG.LocalAnalysis.WeakClosure81.Asch80Wr

end
