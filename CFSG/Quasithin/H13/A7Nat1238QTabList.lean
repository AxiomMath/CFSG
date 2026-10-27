module

public import CFSG.Quasithin.H13.A7Nat1233
public import CFSG.Quasithin.H13.A7Nat1238NQBase
public import CFSG.Quasithin.H13.A7Nat1238QTabCmp

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin Subgroup

theorem List1222.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : List1222 X) :
    List1222 Y := by
  rcases h with h | ⟨n, hn5, hn8, φ, hφ, hker⟩
  · left
    rw [← Nat.card_congr e.toEquiv]
    exact h
  · right
    refine ⟨n, hn5, hn8, φ.comp e.symm.toMonoidHom, hφ.comp e.symm.surjective, fun y hy => ?_⟩
    have h1 : e.symm y ∈ center X := hker hy
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro g
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact h1 (e.symm g)

theorem exists_surj_alt_center_of_surj {G : Type} [Group G] [Finite G] {K : Subgroup G} {n : ℕ}
    (hn5 : 5 ≤ n) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    {φ : ↥K →* alternatingGroup (Fin n)} (hφ : Function.Surjective φ) :
    ∃ ψ : (↥K ⧸ CFSG.pCore 2 ↥K) →* alternatingGroup (Fin n), Function.Surjective ψ ∧
      ψ.ker ≤ center (↥K ⧸ CFSG.pCore 2 ↥K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAs : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn5)
  have hcA : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 :=
    card_alternating_fin n (by omega)
  have h3 : 3 ∣ n.factorial / 2 := by
    have h6 : 6 ∣ n.factorial := Nat.factorial_dvd_factorial (by omega : 3 ≤ n)
    obtain ⟨k, hk⟩ := h6
    rw [hk, show 6 * k = 2 * (3 * k) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    exact dvd_mul_right 3 k
  have hF1 : CFSG.pCore 2 ↥K ≤ φ.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    have hN : ((CFSG.pCore 2 ↥K).map φ).Normal := CFSG.pCore_normal.map φ hφ
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hAs _ hN with h1 | h1
    · exact h1
    · exfalso
      have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥K).map φ) := CFSG.pCore_isPGroup.map φ
      rw [h1] at h2
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
      rw [Subgroup.card_top, hcA] at hk
      rw [hk] at h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  set ψ := QuotientGroup.lift _ φ hF1 with hψ
  have hψs : Function.Surjective ψ := QuotientGroup.lift_surjective_of_surjective _ _ hφ hF1
  refine ⟨ψ, hψs, ?_⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq ψ.normal_ker with h1 | h1
  · exfalso
    have h2 : ∀ a : alternatingGroup (Fin n), a = 1 := fun a => by
      obtain ⟨q, rfl⟩ := hψs a
      exact (MonoidHom.mem_ker).1 (h1 ▸ mem_top q)
    have h4 : Nat.card (alternatingGroup (Fin n)) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h2 a).trans (h2 b).symm⟩, inferInstance⟩
    rw [hcA] at h4
    rw [h4] at h3
    norm_num at h3
  · exact h1

theorem bijective_toGL_zmod_two (n : ℕ) :
    Function.Bijective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* GL (Fin n) (ZMod 2)) := by
  refine ⟨fun a b hab => ?_, fun g => ?_⟩
  · apply Subtype.ext
    have := congrArg (fun g : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) =>
      (g : Matrix (Fin n) (Fin n) (ZMod 2))) hab
    simpa using this
  · have hdet : (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact units_zmod_two_eq_one _
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩

noncomputable def specialLinearFourTwoEquivAlt :
    Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) ≃* alternatingGroup (Fin 8) :=
  (MulEquiv.ofBijective _ (bijective_toGL_zmod_two 4)).trans
    CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm

theorem list1222_of_modules {G : Type} [Group G] [Finite G] {K V : Subgroup G}
    [IsMulCommutative ↥V] (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hmod : Modules12_2_2 K V) : List1222 (↥K ⧸ CFSG.pCore 2 ↥K) := by
  rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨n, hn5, hn8, ⟨φ, hφ, -⟩, -⟩ | ⟨-, φ, hφ, -⟩ | ⟨hL, -⟩ | ⟨-, -, ⟨e⟩, -⟩
  · rcases hn with rfl | rfl | rfl
    · left; left
      rw [Nat.card_congr e.toEquiv, nat_card_SL_three_zmod_two]
    · right
      refine ⟨8, by norm_num, le_rfl, (e.trans specialLinearFourTwoEquivAlt).toMonoidHom,
        (e.trans specialLinearFourTwoEquivAlt).surjective, ?_⟩
      intro x hx
      have : x = 1 := (e.trans specialLinearFourTwoEquivAlt).injective (by
        rw [map_one]; exact hx)
      rw [this]
      exact one_mem _
    · left; right; right
      rw [Nat.card_congr e.toEquiv, nat_card_SL_zmod_two]
      decide
  · left; left
    rw [Nat.card_congr e.toEquiv, nat_card_SL_three_zmod_two]
  · left; right; right
    rw [Nat.card_congr e.toEquiv, nat_card_SL_zmod_two]
    decide
  · obtain ⟨ψ, hψ, hψk⟩ := exists_surj_alt_center_of_surj hn5 hq hφ
    exact Or.inr ⟨n, hn5, hn8, ψ, hψ, hψk⟩
  · obtain ⟨ψ, hψ, hψk⟩ := exists_surj_alt_center_of_surj (by norm_num) hq hφ
    exact Or.inr ⟨7, by norm_num, by norm_num, ψ, hψ, hψk⟩
  · left; right; left
    rcases hL with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · obtain ⟨-, F, hF, hFfin, hFc, ⟨e⟩⟩ := hM
      rw [Nat.card_congr e.toEquiv,
        Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F) Nat.prime_three le_rfl hFc
          (by norm_num)]
      decide
    all_goals exact absurd h0 (by norm_num)
  · right
    refine ⟨6, by norm_num, by norm_num, e.toMonoidHom.comp (QuotientGroup.mk' _),
      e.surjective.comp (QuotientGroup.mk'_surjective _), fun x hx => ?_⟩
    have h1 : QuotientGroup.mk' (center _) x = 1 := e.injective (by
      rw [map_one]
      exact hx)
    exact (QuotientGroup.eq_one_iff x).1 h1

theorem isAlt_quot_solvableRadical_of_surj {X Y : Type} [Group X] [Group Y] [Finite X]
    [Finite Y] (hX : Nonempty (X ⧸ CFSG.pCore 2 X ≃* alternatingGroup (Fin 5)))
    {π : X →* Y} (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker) :
    IsAlt 5 (Y ⧸ CFSG.solvableRadical Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hX
  set α : X →* alternatingGroup (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' _) with hα
  have hαs : Function.Surjective α := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hαk : α.ker = CFSG.pCore 2 X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) x = 1 := e.injective (by rw [map_one]; exact h)
      exact (QuotientGroup.eq_one_iff x).1 h1
    · intro h
      show e (QuotientGroup.mk' (CFSG.pCore 2 X) x) = 1
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 h, map_one]
  set β : X →* Y ⧸ CFSG.solvableRadical Y := (QuotientGroup.mk' _).comp π with hβ
  have hβs : Function.Surjective β := (QuotientGroup.mk'_surjective _).comp hπ
  have hkS : Group.IsSolvable ↥π.ker := by
    have := hk.isNilpotent
    infer_instance
  have hRad : Group.IsSolvable ↥(CFSG.solvableRadical Y) :=
    CFSG.ABGLocalTools.solvableRadical_isSolvable (H := Y)
  have hAs : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin])
  have hAns : ¬ Group.IsSolvable (alternatingGroup (Fin 5)) := by
    have : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by rw [Nat.card_fin])⟩
    have : Nontrivial (alternatingGroup (Fin 5)) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [card_alternating_fin 5 (by norm_num)]; decide)
    exact Group.IsPerfect.not_isSolvable _
  have hker : β.ker = α.ker := by
    apply le_antisymm
    ·
      have hle : β.ker ≤ CFSG.solvableRadical X :=
        le_solvableRadical_of_map_le π hRad hkS β.normal_ker (by
          rintro _ ⟨x, hx, rfl⟩
          exact (QuotientGroup.eq_one_iff _).1 hx)
      have hRX : Group.IsSolvable ↥(CFSG.solvableRadical X) :=
        CFSG.ABGLocalTools.solvableRadical_isSolvable (H := X)
      have hN : ((CFSG.solvableRadical X).map α).Normal :=
        (inferInstance : (CFSG.solvableRadical X).Normal).map α hαs
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hAs _ hN with h | h
      · exact hle.trans ((Subgroup.map_eq_bot_iff _).1 h)
      · exfalso
        apply hAns
        have hs : Group.IsSolvable ↥((CFSG.solvableRadical X).map α) :=
          Group.isSolvable_of_surjective (f := α.subgroupMap _) (α.subgroupMap_surjective _)
        rw [h] at hs
        exact Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup (alternatingGroup (Fin 5))) ≃* _).toMonoidHom)
          Subgroup.topEquiv.surjective
    · rw [hαk]
      intro x hx
      rw [MonoidHom.mem_ker]
      show QuotientGroup.mk' _ (π x) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have hN : ((CFSG.pCore 2 X).map π).Normal := CFSG.pCore_normal.map π hπ
      have hS : Group.IsSolvable ↥((CFSG.pCore 2 X).map π) := by
        have := (CFSG.pCore_isPGroup.map π : IsPGroup 2 ↥((CFSG.pCore 2 X).map π)).isNilpotent
        infer_instance
      have hle : (CFSG.pCore 2 X).map π ≤ CFSG.solvableRadical Y :=
        le_sSup (show (CFSG.pCore 2 X).map π ∈
          {N : Subgroup Y | N.Normal ∧ Group.IsSolvable ↥N} from ⟨hN, hS⟩)
      exact hle ⟨x, hx, rfl⟩
  exact Nonempty.intro ((QuotientGroup.quotientKerEquivOfSurjective β hβs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)))

end CFSG.Quasithin.H13.A7
