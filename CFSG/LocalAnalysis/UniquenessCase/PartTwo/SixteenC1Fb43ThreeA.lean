module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbSyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Std
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c1_exists_conj_of_isSylowIn {p : ℕ} [Fact p.Prime] {S S' H : Subgroup G}
    (hS : IsSylowIn p S H) (hS' : IsSylowIn p S' H) :
    ∃ h ∈ H, ∀ x : G, x ∈ S' ↔ h⁻¹ * x * h ∈ S := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) hS.toSylow hS'.toSylow
  have hg' : MulAut.conj g • (hS.toSylow : Subgroup H) = (hS'.toSylow : Subgroup H) := by
    rw [← Sylow.coe_subgroup_smul (g := g), hg]
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · intro hx
    have hxH : x ∈ H := hS'.le hx
    have : (⟨x, hxH⟩ : H) ∈ (hS'.toSylow : Subgroup H) := hx
    rw [← hg', Subgroup.mem_smul_pointwise_iff_exists] at this
    obtain ⟨s, hs, hsx⟩ := this
    have : (g : G)⁻¹ * x * g = (s : G) := by
      have h2 : ((MulAut.conj g • s : H) : G) = x := congrArg Subtype.val hsx
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
      rw [← h2]; group
    rw [this]
    exact hs
  · intro hx
    have hxH : (g : G)⁻¹ * x * g ∈ H := hS.le hx
    have hxH' : x ∈ H := by
      have := H.mul_mem (H.mul_mem g.2 hxH) (H.inv_mem g.2)
      simpa [mul_assoc] using this
    have : (⟨x, hxH'⟩ : H) ∈ (hS'.toSylow : Subgroup H) := by
      rw [← hg', Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨⟨(g : G)⁻¹ * x * g, hxH⟩, hx, ?_⟩
      apply Subtype.ext
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact this

private theorem s16c1_isSylowIn_map_conj {p : ℕ} [Fact p.Prime] {P H : Subgroup G}
    (hP : IsSylowIn p P H) {g : G} (hg : g ∈ normalizer (H : Set G)) :
    IsSylowIn p (P.map (MulAut.conj g).toMonoidHom) H := by
  refine isSylowIn_of_card_eq ?_ ?_
  · rw [← Subgroup.mem_normalizer_iff_map_conj_eq.1 hg]
    exact Subgroup.map_mono hP.le
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hP.card_eq

theorem s16c1_normalizer_lift {M T V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : M ≤ stabTil V₀ V) (hT : IsSylowIn 2 T M)
    {S₁ : Subgroup (MulAut (Vtil V₀ V hV))} (hS₁ : S₁ ≤ barSub V₀ V hV T)
    {n : MulAut (Vtil V₀ V hV)} (hn : n ∈ barSub V₀ V hV M)
    (hnS : n ∈ normalizer (S₁ : Set (MulAut (Vtil V₀ V hV)))) :
    ∃ (m : G) (hm : m ∈ stabTil V₀ V), m ∈ M ∧
      m ∈ normalizer ((T ⊓ preBarSub M V₀ V hV S₁ : Subgroup G) : Set G) ∧
        actTil V₀ V hV ⟨m, hm⟩ = n := by
  classical
  let P₁ : Subgroup G := preBarSub M V₀ V hV S₁
  let T₁ : Subgroup G := T ⊓ P₁
  have hT₁_syl : IsSylowIn 2 T₁ P₁ := s16c1_sylow_preBarSub hM hT hS₁
  obtain ⟨g₀, hg₀M, hg₀n⟩ := (mem_barSub V₀ V hV M n).1 hn
  have hm₀P₁ : (g₀ : G) ∈ normalizer (P₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨hyM, hyS, hyS₁⟩ := (mem_preBarSub M V₀ V hV S₁).1 hy
      refine (mem_preBarSub M V₀ V hV S₁).2 ⟨?_, ?_⟩
      · exact M.mul_mem (M.mul_mem hg₀M hyM) (M.inv_mem hg₀M)
      · have hyS' : (g₀ : G) * y * (g₀ : G)⁻¹ ∈ stabTil V₀ V :=
          (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem g₀.2 hyS)
            ((stabTil V₀ V).inv_mem g₀.2)
        refine ⟨hyS', ?_⟩
        have hconj : actTil V₀ V hV ⟨(g₀ : G) * y * (g₀ : G)⁻¹, hyS'⟩
            = n * actTil V₀ V hV ⟨y, hyS⟩ * n⁻¹ := by
          have heq : (⟨(g₀ : G) * y * (g₀ : G)⁻¹, hyS'⟩ : ↥(stabTil V₀ V))
              = g₀ * ⟨y, hyS⟩ * g₀⁻¹ := Subtype.ext rfl
          simp only [heq, map_mul, map_inv, hg₀n]
        rw [hconj]
        exact (Subgroup.mem_normalizer_iff.1 hnS _).1 hyS₁
    · intro hy
      obtain ⟨hyM', hyS', hyS₁⟩ := (mem_preBarSub M V₀ V hV S₁).1 hy
      refine (mem_preBarSub M V₀ V hV S₁).2 ⟨?_, ?_⟩
      · have hy_eq : y = (g₀ : G)⁻¹ * ((g₀ : G) * y * (g₀ : G)⁻¹) * (g₀ : G) := by
          group
        rw [hy_eq]
        exact M.mul_mem (M.mul_mem (M.inv_mem hg₀M) hyM') hg₀M
      · have hyS : y ∈ stabTil V₀ V := by
          have hy_eq : y = (g₀ : G)⁻¹ * ((g₀ : G) * y * (g₀ : G)⁻¹) * (g₀ : G) := by
            group
          rw [hy_eq]
          exact (stabTil V₀ V).mul_mem
            ((stabTil V₀ V).mul_mem ((stabTil V₀ V).inv_mem g₀.2) hyS') g₀.2
        refine ⟨hyS, ?_⟩
        have hconj : actTil V₀ V hV ⟨y, hyS⟩
            = n⁻¹ * actTil V₀ V hV ⟨(g₀ : G) * y * (g₀ : G)⁻¹, hyS'⟩ * n := by
          have heq : (⟨y, hyS⟩ : ↥(stabTil V₀ V))
              = g₀⁻¹ * ⟨(g₀ : G) * y * (g₀ : G)⁻¹, hyS'⟩ * g₀ := by
            refine Subtype.ext ?_
            show y = (g₀ : G)⁻¹ * ((g₀ : G) * y * (g₀ : G)⁻¹) * (g₀ : G)
            group
          simp only [heq, map_mul, map_inv, hg₀n]
        rw [hconj]
        exact (Subgroup.mem_normalizer_iff.1 (inv_mem hnS) _).1 hyS₁
  have hT₂_syl : IsSylowIn 2 (T₁.map (MulAut.conj (g₀ : G)).toMonoidHom) P₁ :=
    s16c1_isSylowIn_map_conj hT₁_syl hm₀P₁
  obtain ⟨c, hcP₁, hc⟩ := s16c1_exists_conj_of_isSylowIn hT₁_syl hT₂_syl
  have hc_inv_mem : c⁻¹ ∈ P₁ := P₁.inv_mem hcP₁
  obtain ⟨_, hc_inv_s, hc_inv_img⟩ := (mem_preBarSub M V₀ V hV S₁).1 hc_inv_mem
  obtain ⟨t', ht'T, ht'eq⟩ := (mem_barSub V₀ V hV T _).1 (hS₁ hc_inv_img)
  have htP₁ : (t' : G) ∈ P₁ := by
    refine (mem_preBarSub M V₀ V hV S₁).2 ⟨hT.le ht'T, t'.2, ?_⟩
    rw [show (⟨(t' : G), t'.2⟩ : ↥(stabTil V₀ V)) = t' from Subtype.ext rfl, ht'eq]
    exact hc_inv_img
  have htT₁ : (t' : G) ∈ T₁ := ⟨ht'T, htP₁⟩
  let k : G := c⁻¹ * (g₀ : G)
  have hmemT₂ : ∀ x : G, x ∈ T₁.map (MulAut.conj (g₀ : G)).toMonoidHom ↔
      ∃ y ∈ T₁, (g₀ : G) * y * (g₀ : G)⁻¹ = x := by
    intro x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨y, hy, ?_⟩
      have h2 : MulAut.conj (g₀ : G) y = x := hyx
      rwa [MulAut.conj_apply] at h2
    · rintro ⟨y, hy, hyx⟩
      refine ⟨y, hy, ?_⟩
      have h2 : MulAut.conj (g₀ : G) y = x := by rwa [MulAut.conj_apply]
      exact h2
  have hkN : k ∈ normalizer (T₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyT₂ : (g₀ : G) * y * (g₀ : G)⁻¹ ∈
          T₁.map (MulAut.conj (g₀ : G)).toMonoidHom := (hmemT₂ _).2 ⟨y, hy, rfl⟩
      have h1 : c⁻¹ * ((g₀ : G) * y * (g₀ : G)⁻¹) * c ∈ T₁ :=
        (hc ((g₀ : G) * y * (g₀ : G)⁻¹)).1 hyT₂
      have hk : k * y * k⁻¹ = c⁻¹ * ((g₀ : G) * y * (g₀ : G)⁻¹) * c := by
        simp only [k]; group
      rw [hk]; exact h1
    · intro hy
      have h1 : c⁻¹ * ((g₀ : G) * y * (g₀ : G)⁻¹) * c ∈ T₁ := by
        have hk : c⁻¹ * ((g₀ : G) * y * (g₀ : G)⁻¹) * c = k * y * k⁻¹ := by
          simp only [k]; group
        rw [hk]; exact hy
      have hyT₂ : (g₀ : G) * y * (g₀ : G)⁻¹ ∈
          T₁.map (MulAut.conj (g₀ : G)).toMonoidHom :=
        (hc ((g₀ : G) * y * (g₀ : G)⁻¹)).2 h1
      obtain ⟨y', hy', hy''⟩ := (hmemT₂ _).1 hyT₂
      have hyy' : y' = y := mul_left_cancel (mul_right_cancel hy'')
      simpa [hyy'] using hy'
  have ht_inv_N : (t' : G)⁻¹ ∈ normalizer (T₁ : Set G) :=
    (normalizer (T₁ : Set G)).inv_mem (Subgroup.le_normalizer (H := T₁) htT₁)
  have hmN : (t' : G)⁻¹ * k ∈ normalizer (T₁ : Set G) :=
    (normalizer (T₁ : Set G)).mul_mem ht_inv_N hkN
  have htM : (t' : G) ∈ M := hT.le ht'T
  have hcM : c ∈ M := ((mem_preBarSub M V₀ V hV S₁).1 hcP₁).1
  have hkM : k ∈ M := M.mul_mem (M.inv_mem hcM) hg₀M
  have hmM : (t' : G)⁻¹ * k ∈ M := M.mul_mem (M.inv_mem htM) hkM
  have htS : (t' : G) ∈ stabTil V₀ V := hM htM
  have hkS : k ∈ stabTil V₀ V := (stabTil V₀ V).mul_mem hc_inv_s g₀.2
  have hmS : (t' : G)⁻¹ * k ∈ stabTil V₀ V :=
    (stabTil V₀ V).mul_mem ((stabTil V₀ V).inv_mem htS) hkS
  refine ⟨(t' : G)⁻¹ * k, hmS, hmM, hmN, ?_⟩
  have heq : (⟨(t' : G)⁻¹ * k, hmS⟩ : ↥(stabTil V₀ V))
      = (t')⁻¹ * ⟨c⁻¹, hc_inv_s⟩ * g₀ :=
    Subtype.ext (by simp only [k, Subgroup.coe_mul, Subgroup.coe_inv]; group)
  rw [heq]
  simp only [map_mul, map_inv]
  rw [ht'eq, hg₀n]
  group

theorem s16c1_frattini_lift {M T V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : M ≤ stabTil V₀ V) (hT : IsSylowIn 2 T M)
    {Q E : Subgroup (MulAut (Vtil V₀ V hV))} (hQ : Q ≤ barSub V₀ V hV T)
    (hE : IsPGroup 3 E) (hEM : E ≤ barSub V₀ V hV M)
    (hEQ : E ≤ normalizer (Q : Set (MulAut (Vtil V₀ V hV)))) (hEc : ¬ IsCyclic E) :
    ∃ X : Subgroup G, X ≤ M ∧ IsPGroup 3 X ∧ ¬ IsCyclic X ∧
      X ≤ normalizer ((T ⊓ preBarSub M V₀ V hV Q : Subgroup G) : Set G) := by
  classical
  let Y₀ : Subgroup G := T ⊓ preBarSub M V₀ V hV Q
  let N₁ : Subgroup G := M ⊓ normalizer (Y₀ : Set G)
  have hN₁s : N₁ ≤ stabTil V₀ V := inf_le_left.trans hM
  let f : ↥N₁ →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hN₁s)
  have hEf : E ≤ f.range := by
    intro φ hφ
    obtain ⟨m, hm, hmM, hmN, hmφ⟩ := s16c1_normalizer_lift hM hT hQ (hEM hφ) (hEQ hφ)
    exact ⟨⟨m, hmM, hmN⟩, hmφ⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P, hP3, hPE⟩ := exists_pGroup_map_eq f E hE hEf
  refine ⟨P.map N₁.subtype, (Subgroup.map_subtype_le P).trans inf_le_left, hP3.map N₁.subtype,
    ?_, fun x hx => ?_⟩
  · intro hcyc
    haveI : IsCyclic ↥(P.map N₁.subtype) := hcyc
    haveI : IsCyclic ↥P :=
      isCyclic_of_surjective (Subgroup.equivMapOfInjective P N₁.subtype N₁.subtype_injective).symm
        (Subgroup.equivMapOfInjective P N₁.subtype N₁.subtype_injective).symm.surjective
    haveI : IsCyclic ↥(P.map f) :=
      isCyclic_of_surjective (f.subgroupMap P) (f.subgroupMap_surjective P)
    rw [hPE] at this
    exact hEc this
  · obtain ⟨y, -, rfl⟩ := hx
    exact y.2.2

theorem s16c1_gammaSet_conj_mem {T V T₁ A : Subgroup G} {m : G} (hT₁ : T₁ ≤ T)
    (hm : m ∈ normalizer (T₁ : Set G)) (hAT₁ : A ≤ T₁) (hA : A ∈ E3.gammaSet V 0 T) :
    A.map (MulAut.conj m).toMonoidHom ∈ E3.gammaSet V 0 T := by
  obtain ⟨hAT, g, hAg, hm0⟩ := hA
  have hmap : A.map (MulAut.conj m).toMonoidHom = conjSubgroup A m⁻¹ := by
    simp only [conjSubgroup, inv_inv]
  refine ⟨?_, g * m⁻¹, ?_, ?_⟩
  · rw [hmap]
    have h1 : conjSubgroup A m⁻¹ ≤ conjSubgroup T₁ m⁻¹ := E3.conjSubgroup_mono_left m⁻¹ hAT₁
    rw [conjSubgroup_eq_iff_mem_normalizer.2 (inv_mem hm)] at h1
    exact h1.trans hT₁
  · rw [hmap, ← conjSubgroup_conjSubgroup]
    exact E3.conjSubgroup_mono_left m⁻¹ hAg
  · rw [hmap, ← conjSubgroup_conjSubgroup]
    rw [E3.mQuot_conjSubgroup, hm0]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
