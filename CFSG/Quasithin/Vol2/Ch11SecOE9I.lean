module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.Quasithin.Background.A1bGroups

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin

variable {G : Type} [Group G] {K : Type} [Field K] {L : Subgroup G}

abbrev emb (ψ : antiSp K ≃* ↥L) : antiSp K →* G := L.subtype.comp ψ.toMonoidHom

theorem emb_injective (ψ : antiSp K ≃* ↥L) : Function.Injective (emb ψ) :=
  L.subtype_injective.comp ψ.injective

theorem range_emb (ψ : antiSp K ≃* ↥L) : (emb ψ).range = L := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.surjective, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem emb_mem (ψ : antiSp K ≃* ↥L) (g : antiSp K) : emb ψ g ∈ L := (ψ g).2

theorem exists_emb_eq (ψ : antiSp K ≃* ↥L) {x : G} (hx : x ∈ L) : ∃ g, emb ψ g = x := by
  rw [← MonoidHom.mem_range, range_emb]
  exact hx

variable [L.Normal]

@[expose] noncomputable def autHom (ψ : antiSp K ≃* ↥L) : G →* MulAut (antiSp K) :=
  (MulAut.congr ψ.symm).toMonoidHom.comp MulAut.conjNormal

theorem emb_autHom (ψ : antiSp K ≃* ↥L) (x : G) (g : antiSp K) :
    emb ψ (autHom ψ x g) = x * emb ψ g * x⁻¹ := by
  show ((ψ (ψ.symm (MulAut.conjNormal x (ψ g))) : ↥L) : G) = x * (ψ g : G) * x⁻¹
  rw [MulEquiv.apply_symm_apply, MulAut.conjNormal_apply]

theorem conjSub_map_emb (ψ : antiSp K ≃* ↥L) (x : G) (M : Subgroup (antiSp K)) :
    A1b.conjSub x (M.map (emb ψ)) = (M.map (autHom ψ x).toMonoidHom).map (emb ψ) := by
  rw [A1b.conjSub, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact (emb_autHom ψ x g).symm

theorem mem_normalizer_map_emb_iff (ψ : antiSp K ≃* ↥L) (x : G) (M : Subgroup (antiSp K)) :
    x ∈ Subgroup.normalizer ((M.map (emb ψ) : Subgroup G) : Set G) ↔
      M.map (autHom ψ x).toMonoidHom = M := by
  rw [← A1b.conjSub_eq_iff_mem_normalizer, conjSub_map_emb]
  exact (Subgroup.map_injective (emb_injective ψ)).eq_iff

theorem autHom_emb (ψ : antiSp K ≃* ↥L) (y : antiSp K) : autHom ψ (emb ψ y) = MulAut.conj y := by
  refine MulEquiv.ext fun g => ?_
  apply emb_injective ψ
  rw [emb_autHom, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem eq_emb_of_autHom_eq (ψ : antiSp K ≃* ↥L) (hC : Subgroup.centralizer (L : Set G) = ⊥)
    {x : G} {y : antiSp K} (h : autHom ψ x = MulAut.conj y) : x = emb ψ y := by
  set z := x * (emb ψ y)⁻¹ with hz
  have h1 : autHom ψ z = 1 := by
    rw [hz, map_mul, map_inv, h, autHom_emb, mul_inv_cancel]
  have h2 : z ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨g, rfl⟩ := exists_emb_eq ψ hl
    have h3 := emb_autHom ψ z g
    rw [h1, MulAut.one_apply] at h3
    calc emb ψ g * z = z * emb ψ g * z⁻¹ * z := by rw [← h3]
      _ = z * emb ψ g := by group
  rw [hC, Subgroup.mem_bot, hz] at h2
  exact mul_inv_eq_one.mp h2

variable [CharP K 2]

theorem mul_inv_mem [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (ψ : antiSp K ≃* ↥L) (hC : Subgroup.centralizer (L : Set G) = ⊥) {x y : G}
    (hx : x * x = 1) (hy : y * y = 1) (hxL : x ∉ L) (hyL : y ∉ L) : x * y⁻¹ ∈ L := by
  have key : ∀ z : G, z * z = 1 → z ∉ L →
      ∃ g, autHom ψ z = MulAut.conj g * minorAut K ^ n := by
    intro z hz hzL
    refine outer_involution_form hn hK _ (by rw [← map_mul, hz, map_one]) fun hin => ?_
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hin
    exact hzL ((eq_emb_of_autHom_eq ψ hC hg.symm) ▸ emb_mem ψ g)
  obtain ⟨g, hg⟩ := key x hx hxL
  obtain ⟨h, hh⟩ := key y hy hyL
  have : autHom ψ (x * y⁻¹) = MulAut.conj (g * h⁻¹) := by
    rw [map_mul, map_inv, hg, hh, map_mul, map_inv]
    group
  rw [eq_emb_of_autHom_eq ψ hC this]
  exact emb_mem ψ _

theorem card_le_two_mul_inf [Finite G] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (ψ : antiSp K ≃* ↥L) (hC : Subgroup.centralizer (L : Set G) = ⊥)
    {A : Subgroup G} (hA : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ L) := by
  classical
  by_cases hAL : A ≤ L
  · rw [inf_eq_left.mpr hAL]
    omega
  obtain ⟨a, haA, haL⟩ := IsConcreteLE.not_le_iff_exists.mp hAL
  let f : ↥A → Bool × ↥(A ⊓ L) := fun b =>
    if hb : (b : G) ∈ L then (false, ⟨b, b.2, hb⟩)
    else (true, ⟨b * a⁻¹, A.mul_mem b.2 (A.inv_mem haA),
      mul_inv_mem hn hK ψ hC (hA b b.2) (hA a haA) hb haL⟩)
  have hf : Function.Injective f := by
    intro b c hbc
    by_cases hb : (b : G) ∈ L <;> by_cases hc : (c : G) ∈ L <;> simp [f, hb, hc] at hbc
    · exact Subtype.ext (Subtype.mk.inj hbc)
    · exact Subtype.ext (mul_right_cancel (Subtype.mk.inj hbc))
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h

theorem exists_equiv_antiUnipotent [Finite G] [Finite K] (e : antiSp K ≃* ↥L) {T : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) :
    ∃ ψ : antiSp K ≃* ↥L, (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn : L.Normal := inferInstance
  have hU₀ := CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_map_top e
    (card_and_isSylowTwoOf_antiUnipotent (K := K)).2
  have hTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal (⟨hT.1, hT.2.1, hT.2.2⟩ : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
      le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ := by
    refine ⟨le_top, hTL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTL.1).symm, ?_⟩
    show ¬ 2 ∣ ((T ⊓ L).subgroupOf L).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hTL.2.2
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₀).exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 hU)
  refine ⟨e.trans (MulAut.conj k), ?_⟩
  have h1 : (antiUnipotent K).map (e.trans (MulAut.conj k)).toMonoidHom =
      ((antiUnipotent K).map e.toMonoidHom).map (MulAut.conj k).toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [h1]
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  exact (hk x).symm

omit [L.Normal] in
theorem inf_eq_map_emb (ψ : antiSp K ≃* ↥L) {T : Subgroup G}
    (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) :
    T ⊓ L = (antiUnipotent K).map (emb ψ) := by
  show T ⊓ L = (antiUnipotent K).map (L.subtype.comp ψ.toMonoidHom)
  rw [← Subgroup.map_map, hψ, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]

theorem map_autHom_antiUnipotent (ψ : antiSp K ≃* ↥L) {T : Subgroup G}
    (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) {t : G}
    (ht : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) :
    (antiUnipotent K).map (autHom ψ t).toMonoidHom = antiUnipotent K := by
  rw [inf_eq_map_emb ψ hψ, mem_normalizer_map_emb_iff] at ht
  exact ht

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4
