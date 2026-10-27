module

public import CFSG.Quasithin.MS93.S37Q1
public import CFSG.Quasithin.MS93.S37Res

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Sp

variable {F : Type} [Field F]

theorem exists_mem_P₁_map_pt₀ {p : Submodule F (V4 F)} (hp : IsPoint p) (hpl : p ≤ ln₀ F) :
    ∃ g ∈ P₁ F, (pt₀ F).map (Matrix.mulVecLin (mat g)) = p := by
  obtain ⟨v, hv0, rfl⟩ := exists_eq_span_of_isPoint hp
  have hvl : v ∈ ln₀ F := hpl (Submodule.mem_span_singleton_self v)
  obtain ⟨h2, h3⟩ := mem_ln₀.1 hvl
  obtain ⟨A, hA0, hA1⟩ : ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      (A : Matrix (Fin 2) (Fin 2) F) 0 0 = v (.inl 0) ∧
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 = v (.inl 1) := by
    by_cases ha : v (.inl 0) = 0
    · have hb : v (.inl 1) ≠ 0 := fun hb => hv0 (ext4 ha hb h2 h3)
      exact ⟨⟨!![0, -(v (.inl 1))⁻¹; v (.inl 1), 0], by simp [Matrix.det_fin_two, hb]⟩,
        by simp [ha], by simp⟩
    · exact ⟨⟨!![v (.inl 0), 0; v (.inl 1), (v (.inl 0))⁻¹], by simp [Matrix.det_fin_two, ha]⟩,
        by simp, by simp⟩
  refine ⟨levHom₁ A, lev₁_le_P₁ ⟨A, rfl⟩, ?_⟩
  rw [pt₀_eq_span, Submodule.map_span, Set.image_singleton]
  congr 1
  rw [Set.singleton_eq_singleton_iff, Matrix.mulVecLin_apply, mat_levHom₁,
    Matrix.fromBlocks_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [e₁, hA0, hA1, h2, h3]

end Sp

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem tImage_mul {S : Subgroup G} (θ₁ θ₂ : MulAut ↥S) (K : Subgroup G) :
    tImage (θ₁ * θ₂) K = tImage θ₁ (tImage θ₂ K) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hyS, hy, rfl⟩ := mem_tImage.1 hx
    exact mem_tImage.2 ⟨_, (θ₂ ⟨y, hyS⟩).2, mem_tImage.2 ⟨y, hyS, hy, rfl⟩, rfl⟩
  · intro hx
    obtain ⟨y, hyS, hy, rfl⟩ := mem_tImage.1 hx
    obtain ⟨z, hzS, hz, hze⟩ := mem_tImage.1 hy
    refine mem_tImage.2 ⟨z, hzS, hz, ?_⟩
    have e : θ₂ ⟨z, hzS⟩ = ⟨y, hyS⟩ := Subtype.ext hze
    show ((θ₁ (θ₂ ⟨z, hzS⟩) : ↥S) : G) = _
    rw [e]

omit [Finite G] in
theorem tImage_normalizer_mul {S : Subgroup G} (n : ↥(Subgroup.normalizer (S : Set G)))
    (θ : MulAut ↥S) (K : Subgroup G) :
    tImage (S.normalizerMonoidHom n * θ) K =
      (tImage θ K).map (MulAut.conj (n : G)).toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hyS, hy, rfl⟩ := mem_tImage.1 hx
    exact ⟨_, mem_tImage.2 ⟨y, hyS, hy, rfl⟩, rfl⟩
  · rintro ⟨_, hz, rfl⟩
    obtain ⟨y, hyS, hy, rfl⟩ := mem_tImage.1 hz
    exact mem_tImage.2 ⟨y, hyS, hy, rfl⟩

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem rho_conjG (g : Sp4 F) (x : ↥(L ⊔ pCoreOf 2 M)) :
    (C.conjG g).rho x = g⁻¹ * C.rho x * g := by
  obtain ⟨l, hl, q, hq, e⟩ := C.exists_mul_of_mem_sup x.2
  have hx : x = ⟨l * q, e ▸ x.2⟩ := Subtype.ext e.symm
  rw [hx, C.rho_mul hl hq, (C.conjG g).rho_mul hl hq]
  show g⁻¹ * C.α ⟨l, hl⟩ * g⁻¹⁻¹ = _
  rw [inv_inv]

theorem rhoIm_conjG (g : Sp4 F) (X : Subgroup G) :
    (C.conjG g).rhoIm X = (C.rhoIm X).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext y
  rw [(C.conjG g).mem_rhoIm, mem_map_conj, C.mem_rhoIm, inv_inv]
  constructor
  · rintro ⟨x, hxK, hxX, rfl⟩
    refine ⟨x, hxK, hxX, ?_⟩
    rw [C.rho_conjG g ⟨x, hxK⟩]
    group
  · rintro ⟨x, hxK, hxX, hρ⟩
    refine ⟨x, hxK, hxX, ?_⟩
    rw [C.rho_conjG g ⟨x, hxK⟩, hρ]
    group

theorem rhoIm_map_conj {X : Subgroup G} (hX : X ≤ L ⊔ pCoreOf 2 M) {l : G}
    (hl : l ∈ L ⊔ pCoreOf 2 M) :
    C.rhoIm (X.map (MulAut.conj l).toMonoidHom) =
      (C.rhoIm X).map (MulAut.conj (C.rho ⟨l, hl⟩)).toMonoidHom := by
  ext y
  rw [C.mem_rhoIm, mem_map_conj, C.mem_rhoIm]
  constructor
  · rintro ⟨x, hxK, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z, hX hz, hz, ?_⟩
    have e : (⟨(MulAut.conj l).toMonoidHom z, hxK⟩ : ↥(L ⊔ pCoreOf 2 M)) =
        ⟨l, hl⟩ * ⟨z, hX hz⟩ * (⟨l, hl⟩ : ↥(L ⊔ pCoreOf 2 M))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    group
  · rintro ⟨z, hzK, hz, hρ⟩
    refine ⟨l * z * l⁻¹, (L ⊔ pCoreOf 2 M).mul_mem ((L ⊔ pCoreOf 2 M).mul_mem hl hzK)
      ((L ⊔ pCoreOf 2 M).inv_mem hl), ⟨z, hz, rfl⟩, ?_⟩
    rw [C.rho_conj_eq hl hzK, hρ]
    group

theorem false_of_caseI_Q₁ (hT : C.T0bar = Q₁ F) (hq : 8 ≤ Nat.card F)
    (θ : MulAut ↥(T1 M T L)) (hcrit : ¬ Uq M T L ≤ Qt M θ) {p : Submodule F (V4 F)}
    (hp : IsPoint p) (hE : C.rhoIm (Ut M T L θ) = xPoint p) : False := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hUQ : ∀ φ : MulAut ↥(T1 M T L), C.rhoIm (Ut M T L φ) ≤ Q₁ F := fun φ g hg => by
    rw [← hT]
    obtain ⟨x, hxK, hx, rfl⟩ := (C.mem_rhoIm).1 hg
    exact ⟨⟨x, tImage_le φ _ hx⟩, rfl⟩
  have hpl : p ≤ ln₀ F := (xPoint_le_qLine_iff hp isLine_ln₀).1 (hE ▸ hUQ θ)
  have hcrit' := C.crit_inv C.pCore_le_T1 T1_le_T θ hcrit
  obtain ⟨p', hp', hE'⟩ : ∃ p' : Submodule F (V4 F), IsPoint p' ∧
      C.rhoIm (Ut M T L θ⁻¹) = xPoint p' := by
    rcases C.partner_cases θ⁻¹ hcrit' with h | ⟨hl, -⟩
    · exact h
    · exfalso
      have heq := (C.relIndex_inv_eq C.pCore_le_T1 T1_le_T θ hcrit (tImage_le θ _)
        (tImage_le θ⁻¹ _) (C.partner_relIndex_eq θ hcrit).le).2
      have h3 : Module.finrank F (perp p) = 3 := by
        have h := finrank_perp p
        have h1 : Module.finrank F p = 1 := hp
        omega
      have c1 : Nat.card ↥(fixSp (C.rhoIm (Ut M T L θ⁻¹))) = Nat.card F ^ 2 := by
        rw [Module.natCard_eq_pow_finrank (K := F), hl.1]
      have c2 : Nat.card ↥(perp p) = Nat.card F ^ 3 := by
        rw [Module.natCard_eq_pow_finrank (K := F), h3]
      rw [c1, hE, fixSp_xPoint hp, c2] at heq
      have hq4 := C.q_ge_four
      have hlt : Nat.card F ^ 2 < Nat.card F ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
  have hpl' : p' ≤ ln₀ F := (xPoint_le_qLine_iff hp' isLine_ln₀).1 (hE' ▸ hUQ θ⁻¹)
  obtain ⟨g₁, hg₁, hg₁p⟩ := exists_mem_P₁_map_pt₀ hp hpl
  obtain ⟨g₂, hg₂, hg₂p⟩ := exists_mem_P₁_map_pt₀ hp' hpl'
  set k := g₂ * g₁⁻¹ with hkdef
  have hk : k ∈ P₁ F := (P₁ F).mul_mem hg₂ ((P₁ F).inv_mem hg₁)
  have hkp : p.map (Matrix.mulVecLin (mat k)) = p' := by
    rw [hkdef, map_mat_mul, ← hg₁p, map_map_mat_inv', hg₂p]
  have hconj : ∀ {g : G} (hg : g ∈ L ⊔ pCoreOf 2 M), C.rho ⟨g, hg⟩ ∈ P₁ F →
      ∀ t ∈ T1 M T L, g * t * g⁻¹ ∈ T1 M T L := by
    intro g hg hgP t ht
    have htK := T1_le_sup ht
    have hK : g * t * g⁻¹ ∈ L ⊔ pCoreOf 2 M :=
      (L ⊔ pCoreOf 2 M).mul_mem ((L ⊔ pCoreOf 2 M).mul_mem hg htK) ((L ⊔ pCoreOf 2 M).inv_mem hg)
    refine C.mem_T1_of_rho_mem (x := ⟨_, hK⟩) ?_
    have htQ : C.rho ⟨t, htK⟩ ∈ Q₁ F := by
      rw [← hT]
      exact ⟨⟨t, ht⟩, rfl⟩
    rw [C.rho_conj_eq hg htK, hT]
    exact (Subgroup.mem_normalizer_iff.1 (P₁_le_normalizer_Q₁ hgP) _).1 htQ
  set l := C.lift k with hldef
  have hlK : l ∈ L ⊔ pCoreOf 2 M := Subgroup.mem_sup_left (C.lift_mem k)
  have hlρ : C.rho ⟨l, hlK⟩ = k := C.rho_lift k
  have hlN : l ∈ Subgroup.normalizer ((T1 M T L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨hconj hlK (hlρ ▸ hk) t, fun h => ?_⟩
    have hl' : l⁻¹ ∈ L ⊔ pCoreOf 2 M := (L ⊔ pCoreOf 2 M).inv_mem hlK
    have hlρ' : C.rho ⟨l⁻¹, hl'⟩ ∈ P₁ F := by
      have e : (⟨l⁻¹, hl'⟩ : ↥(L ⊔ pCoreOf 2 M)) = (⟨l, hlK⟩ : ↥(L ⊔ pCoreOf 2 M))⁻¹ := rfl
      rw [e, map_inv, hlρ]
      exact (P₁ F).inv_mem hk
    have := hconj hl' hlρ' _ h
    simpa [mul_assoc] using this
  set θ₁ := (T1 M T L).normalizerMonoidHom ⟨l, hlN⟩ * θ with hθ₁
  have hE₁ : C.rhoIm (Ut M T L θ₁) = xPoint p' := by
    have e : Ut M T L θ₁ = (Ut M T L θ).map (MulAut.conj l).toMonoidHom :=
      tImage_normalizer_mul ⟨l, hlN⟩ θ (Uq M T L)
    rw [e, C.rhoIm_map_conj ((tImage_le θ _).trans T1_le_sup) hlK, hE, hlρ, xPoint_map_conj, hkp]
  have hE₁' : C.rhoIm (Ut M T L θ₁⁻¹) = xPoint p' := by
    have hle : Ut M T L θ₁⁻¹ ≤ Ut M T L θ⁻¹ := by
      have e : Ut M T L θ₁⁻¹ = tImage θ⁻¹
          (tImage ((T1 M T L).normalizerMonoidHom ⟨l, hlN⟩)⁻¹ (Uq M T L)) := by
        rw [hθ₁, mul_inv_rev]
        exact tImage_mul _ _ _
      intro x hx
      rw [e] at hx
      obtain ⟨y, hyT, hy, rfl⟩ := mem_tImage.1 hx
      obtain ⟨u, huT, hu, hue⟩ := mem_tImage.1 hy
      refine mem_tImage.2 ⟨y, hyT, ?_, rfl⟩
      rw [← hue]
      show l⁻¹ * u * l⁻¹⁻¹ ∈ Uq M T L
      exact (Subgroup.mem_normalizer_iff.1 (C.hMU (C.sup_le_M ((L ⊔ pCoreOf 2 M).inv_mem hlK)))
        u).1 hu
    have heq : Ut M T L θ₁⁻¹ = Ut M T L θ⁻¹ :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [card_tImage θ⁻¹ C.Uq_le_T1, card_tImage θ₁⁻¹ C.Uq_le_T1])
    rw [heq, hE']
  set C' := C.conjG g₂ with hC'
  have hT' : C'.T0bar = Q₁ F := by
    rw [hC', C.T0bar_conjG, hT]
    exact qLine_map_conj_inv g₂ (mem_stab_iff.1 hg₂)
  have hX : (xPoint p').map (MulAut.conj g₂⁻¹).toMonoidHom = X₂ F := by
    rw [xPoint_map_conj, ← hg₂p, map_map_mat_inv']
  have hE₂ : C'.rhoIm (Ut M T L θ₁) = X₂ F := by
    rw [hC', C.rhoIm_conjG, hE₁, hX]
  have hE₂' : C'.rhoIm (Ut M T L θ₁⁻¹) = X₂ F := by
    rw [hC', C.rhoIm_conjG, hE₁', hX]
  obtain ⟨hθg, hθg'⟩ := C'.isGood_of_Q₁ hT' θ₁ hE₂ hE₂'
  have hQUD := C'.exists_of_sup_eq (C'.pCore_eq_of_rhoIm θ₁ hE₂ hθg.rhoIm_Qt).1
  exact C'.false_of_isGood_Q₁ hQUD hT' hq θ₁ hθg hθg'

end Cfg

end CFSG.Quasithin.MS93.S37
