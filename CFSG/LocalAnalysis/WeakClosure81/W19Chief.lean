module

public import CFSG.LocalAnalysis.WeakClosure81.W19Eight

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.SignalizerFunctorTheorem.Quadratic
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Card196Four (D : Data G) (V : Subgroup G) (p : ℕ) (X : Subgroup G) : Prop :=
  ∀ (g : G) (K : Subgroup G), Conf196 D V X g K →
    Nat.card ↥(X ⊓ J193 D X (conjSubgroup V g) K) = p

@[expose] def IsF198 (D : Data G) (V X F : Subgroup G) : Prop :=
  F ≤ V ∧ X ⊔ D.T ≤ normalizer (F : Set G) ∧ ⁅F, X⁆ = ⊥ ∧
    ∀ F' : Subgroup G, F ≤ F' → F' ≤ V → X ⊔ D.T ≤ normalizer (F' : Set G) →
      ⁅F', X⁆ = ⊥ → F' = F

theorem exists_isF198 (D : Data G) (V X : Subgroup G) : ∃ F : Subgroup G, IsF198 D V X F := by
  classical
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  let S : Set (Subgroup G) :=
    {F | F ≤ V ∧ X ⊔ D.T ≤ normalizer (F : Set G) ∧ ⁅F, X⁆ = ⊥}
  have hne : S.Nonempty := by
    refine ⟨⊥, bot_le, fun x _ => ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      simp
    · simp
  obtain ⟨F, hF, hmax⟩ := (Set.toFinite S).exists_maximalFor (fun F : Subgroup G => F) S hne
  exact ⟨F, hF.1, hF.2.1, hF.2.2, fun F' hFF' hF'V hF'n hF'X =>
    le_antisymm (hmax ⟨hF'V, hF'n, hF'X⟩ hFF') hFF'⟩

theorem exists_chief198 {H V F : Subgroup G} (hVn : H ≤ normalizer (V : Set G)) (hFV : F < V) :
    ∃ E : Subgroup G, F < E ∧ E ≤ V ∧ H ≤ normalizer (E : Set G) ∧
      ∀ U : Subgroup G, F ≤ U → U ≤ E → H ≤ normalizer (U : Set G) → U = F ∨ U = E := by
  classical
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  let S : Set (Subgroup G) := {E | F < E ∧ E ≤ V ∧ H ≤ normalizer (E : Set G)}
  have hne : S.Nonempty := ⟨V, hFV, le_rfl, hVn⟩
  obtain ⟨E, hE, hmin⟩ := (Set.toFinite S).exists_minimalFor (fun E : Subgroup G => E) S hne
  refine ⟨E, hE.1, hE.2.1, hE.2.2, fun U hFU hUE hUn => ?_⟩
  by_cases hUF : U = F
  · exact Or.inl hUF
  · right
    have hlt : F < U := lt_of_le_of_ne hFU (Ne.symm hUF)
    exact le_antisymm hUE (hmin ⟨hlt, hUE.trans hE.2.1, hUn⟩ hUE)

theorem mul_comm_of_comm_commutator {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {x e : G}
    (hxp : x ^ p = 1) (hxf : x * ⁅x, e⁆ = ⁅x, e⁆ * x) (hf2 : ⁅x, e⁆ ^ 2 = 1) :
    x * e = e * x := by
  set f : G := ⁅x, e⁆ with hf
  have hpow : ∀ k : ℕ, x ^ k * e * (x ^ k)⁻¹ = f ^ k * e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : x ^ (k + 1) * e * (x ^ (k + 1))⁻¹ = x * (x ^ k * e * (x ^ k)⁻¹) * x⁻¹ := by
        group
      have hk : x * f ^ k = f ^ k * x := (Commute.pow_right (show Commute x f from hxf) k).eq
      have h3 : x * e * x⁻¹ = f * e := by rw [hf, commutatorElement_def]; group
      rw [h1, ih]
      calc x * (f ^ k * e) * x⁻¹ = (x * f ^ k) * e * x⁻¹ := by group
        _ = (f ^ k * x) * e * x⁻¹ := by rw [hk]
        _ = f ^ k * (x * e * x⁻¹) := by group
        _ = f ^ (k + 1) * e := by rw [h3, pow_succ]; group
  have hfp : f ^ p = 1 := by
    have h1 := hpow p
    rw [hxp, one_mul, inv_one, mul_one] at h1
    exact (mul_eq_right.1 h1.symm)
  have hf1 : f ∈ (⊥ : Subgroup G) :=
    E1.mem_of_pow_mem_two_p hp hodd (k := 1) (j := 1)
      (by rw [pow_one, hfp]; exact Subgroup.one_mem _)
      (by rw [pow_one, hf2]; exact Subgroup.one_mem _)
  rw [Subgroup.mem_bot, hf, commutatorElement_eq_one_iff_mul_comm] at hf1
  exact hf1

structure Hyp198 (D : Data G) (X E F : Subgroup G) : Prop where
  E_le : E ≤ X ⊔ D.T
  isElemAbelian : IsElemAbelian 2 E
  F_le : F ≤ E
  normalizer_E : X ⊔ D.T ≤ normalizer (E : Set G)
  normalizer_F : X ⊔ D.T ≤ normalizer (F : Set G)
  irreducible : ∀ U : Subgroup G, F ≤ U → U ≤ E → X ⊔ D.T ≤ normalizer (U : Set G) →
    U = F ∨ U = E
  comm_F : ⁅F, twoResidual (X ⊔ D.T)⁆ = ⊥

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem twoResidual_le_iSup_conj (c : MinCex193 D V₀ V p X) :
    twoResidual (X ⊔ D.T) ≤ ⨆ h ∈ X ⊔ D.T, conjSubgroup X h := by
  set N : Subgroup G := ⨆ h ∈ X ⊔ D.T, conjSubgroup X h with hNdef
  have hXN : X ≤ N := by
    have key : conjSubgroup X 1 ≤ N :=
      le_iSup₂ (f := fun (h : G) (_ : h ∈ X ⊔ D.T) => conjSubgroup X h) (1 : G)
        (X ⊔ D.T).one_mem
    rwa [conjSubgroup_one] at key
  have hNH : N ≤ X ⊔ D.T := by
    refine iSup₂_le fun h hh x hx => ?_
    have hx' : h * x * h⁻¹ ∈ X := mem_conjSubgroup_iff.1 hx
    have e : x = h⁻¹ * (h * x * h⁻¹) * h := by group
    rw [e]
    exact (X ⊔ D.T).mul_mem ((X ⊔ D.T).mul_mem ((X ⊔ D.T).inv_mem hh)
      (Subgroup.mem_sup_left hx')) hh
  have hconj : ∀ k ∈ X ⊔ D.T, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
    intro k hk
    have hle : N ≤ N.comap (MulAut.conj k).toMonoidHom := by
      refine iSup₂_le fun h hh x hx => ?_
      rw [Subgroup.mem_comap]
      have hx' : h * x * h⁻¹ ∈ X := mem_conjSubgroup_iff.1 hx
      have hmem : k * x * k⁻¹ ∈ conjSubgroup X (h * k⁻¹) := by
        rw [mem_conjSubgroup_iff]
        have e : h * k⁻¹ * (k * x * k⁻¹) * (h * k⁻¹)⁻¹ = h * x * h⁻¹ := by group
        rw [e]
        exact hx'
      have key : conjSubgroup X (h * k⁻¹) ≤ N :=
        le_iSup₂ (f := fun (h : G) (_ : h ∈ X ⊔ D.T) => conjSubgroup X h) (h * k⁻¹)
          ((X ⊔ D.T).mul_mem hh ((X ⊔ D.T).inv_mem hk))
      exact key hmem
    intro n hn
    exact hle hn
  have hN : X ⊔ D.T ≤ normalizer (N : Set G) := fun k hk =>
    Subgroup.mem_normalizer_iff.2 fun n =>
      ⟨fun hn => hconj k hk n hn, fun hn => by
        have h1 := hconj k⁻¹ ((X ⊔ D.T).inv_mem hk) _ hn
        have e : k⁻¹ * (k * n * k⁻¹) * k⁻¹⁻¹ = n := by group
        rwa [e] at h1⟩
  refine twoResidual_le_of_isTwoQuotient hNH hN fun y hy => ?_
  have hTN : D.T ≤ normalizer (N : Set G) := le_sup_right.trans hN
  have hHeq : X ⊔ D.T = D.T ⊔ N :=
    le_antisymm (sup_le (hXN.trans le_sup_right) le_sup_left) (sup_le le_sup_right hNH)
  rw [hHeq] at hy
  exact exists_pow_mem_of_mem_sup_pGroup c.hyp.isSylowIn_T.isPGroup hTN hy

theorem comm_twoResidual_eq_bot (c : MinCex193 D V₀ V p X) {F : Subgroup G}
    (hFn : X ⊔ D.T ≤ normalizer (F : Set G)) (hFX : ⁅F, X⁆ = ⊥) :
    ⁅F, twoResidual (X ⊔ D.T)⁆ = ⊥ := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hFX' : ⁅X, F⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hFX
  refine c.twoResidual_le_iSup_conj.trans (iSup₂_le fun h hh x hx => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hx' : h * x * h⁻¹ ∈ X := mem_conjSubgroup_iff.1 hx
  have hf' : h * f * h⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.1 (hFn hh) f).1 hf
  have hmem := Subgroup.commutator_mem_commutator hx' hf'
  rw [hFX', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  calc f * x = h⁻¹ * ((h * f * h⁻¹) * (h * x * h⁻¹)) * h := by group
    _ = h⁻¹ * ((h * x * h⁻¹) * (h * f * h⁻¹)) * h := by rw [hmem]
    _ = x * f := by group

theorem exists_hyp198 (c : MinCex193 D V₀ V p X) (hVX : ⁅V, X⁆ ≠ ⊥) :
    ∃ E F : Subgroup G, Hyp198 D X E F ∧ F < E ∧ E ≤ V ∧ ¬ ⁅X, E⁆ ≤ F := by
  obtain ⟨F, hFV, hFn, hFX, hmax⟩ := exists_isF198 D V X
  have hFlt : F < V := lt_of_le_of_ne hFV fun h => hVX (h ▸ hFX)
  have hVn : X ⊔ D.T ≤ normalizer (V : Set G) := c.hyp.le_M.trans c.setting.pair.le_normalizer
  obtain ⟨E, hFE, hEV, hEn, hirr⟩ := exists_chief198 hVn hFlt
  have hEH : E ≤ X ⊔ D.T := hEV.trans c.V_le_H
  have hEel : IsElemAbelian 2 E := IsElemAbelian.mono c.setting.isElemAbelian hEV
  have hFel : IsElemAbelian 2 F := IsElemAbelian.mono c.setting.isElemAbelian hFV
  have hXE : ¬ ⁅X, E⁆ ≤ F := by
    intro hXE
    have hcomm : ⁅E, X⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hf : ⁅x, e⁆ ∈ F := hXE (Subgroup.commutator_mem_commutator hx he)
      have hxf : x * ⁅x, e⁆ = ⁅x, e⁆ * x := by
        have h1 : ⁅⁅x, e⁆, x⁆ ∈ ⁅F, X⁆ := Subgroup.commutator_mem_commutator hf hx
        rw [hFX, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1.symm
      exact mul_comm_of_comm_commutator c.hyp.prime c.hyp.odd (c.hyp.exponent x hx) hxf
        (hFel.2 _ hf)
    exact hFE.ne (hmax E hFE.le hEV hEn hcomm).symm
  exact ⟨E, F, ⟨hEH, hEel, hFE.le, hEn, hFn, hirr, c.comm_twoResidual_eq_bot hFn hFX⟩, hFE, hEV,
    hXE⟩

end MinCex193

namespace Hyp198

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X E F : Subgroup G}

theorem toHyp197 (h : Hyp198 D X E F) {g : G} (hA : conjSubgroup V g ≤ D.T)
    (hne : ¬ ⁅twoResidual (X ⊔ D.T), conjSubgroup V g⁆ ≤ centralizerQuot (X ⊔ D.T) E F) :
    Hyp197 D V X E F g :=
  ⟨h.E_le, h.isElemAbelian, h.F_le, h.normalizer_E, h.normalizer_F, h.irreducible, h.comm_F, hA,
    hne⟩

theorem hyp197 (c : MinCex193 D V₀ V p X) (h : Hyp198 D X E F) (hFE : F < E) {g : G}
    (hA : conjSubgroup V g ≤ D.T) (hAE : ¬ ⁅conjSubgroup V g, E⁆ ≤ F) :
    Hyp197 D V X E F g := by
  have hAH : conjSubgroup V g ≤ X ⊔ D.T := hA.trans le_sup_right
  obtain ⟨M⟩ := exists_modData c.hyp.isSolvable h.E_le h.isElemAbelian hFE h.normalizer_E
    h.normalizer_F h.irreducible
  have hXn : X ⊔ D.T ≤ normalizer ((X ⊔ pCoreOf 2 (X ⊔ D.T) : Subgroup G) : Set G) :=
    c.le_normalizer_sup_pCoreOf
  have hn := M.range_le_normalizer_img (le_sup_left : X ≤ X ⊔ D.T) hXn
  have hbot := M.img_inf_centralizer_eq_bot hFE (le_sup_right : D.T ≤ X ⊔ D.T)
    (le_sup_left : X ≤ X ⊔ D.T) rfl c.hyp.isSylowIn_T.isPGroup hn
  have hXA : ¬ ⁅X, conjSubgroup V g⁆ ≤ centralizerQuot (X ⊔ D.T) E F := by
    intro hXA
    apply hAE
    have hAC : conjSubgroup V g ≤ centralizerQuot (X ⊔ D.T) E F := by
      intro a ha
      have haH : a ∈ X ⊔ D.T := hAH ha
      have hmemT : M.ρ ⟨a, haH⟩ ∈ M.img D.T := M.mem_img.2 ⟨⟨a, haH⟩, hA ha, rfl⟩
      have hmemC : M.ρ ⟨a, haH⟩ ∈
          centralizer ((M.img X : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        obtain ⟨x, hxX, rfl⟩ := M.mem_img.1 hs
        have h1 : M.ρ ⁅x, (⟨a, haH⟩ : ↥(X ⊔ D.T))⁆ = 1 :=
          (M.ρ_eq_one _).2 (hXA (Subgroup.commutator_mem_commutator hxX ha))
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
      have h1 : M.ρ ⟨a, haH⟩ ∈ M.img D.T ⊓
          centralizer ((M.img X : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := ⟨hmemT, hmemC⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact (M.ρ_eq_one ⟨a, haH⟩).1 h1
    rw [Subgroup.commutator_le]
    intro a ha e he
    exact (hAC ha).2.2 e he
  have hne : ¬ ⁅twoResidual (X ⊔ D.T), conjSubgroup V g⁆ ≤ centralizerQuot (X ⊔ D.T) E F :=
    fun hle => hXA (le_trans (Subgroup.commutator_mono c.X_le_twoResidual le_rfl) hle)
  exact h.toHyp197 hA hne

theorem nine (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G) (h4 : Card196Four D V p X)
    (h : Hyp198 D X E F) (hFE : F < E) {g : G} (hA : conjSubgroup V g ≤ D.T)
    (hAE : ¬ ⁅conjSubgroup V g, E⁆ ≤ F) :
    ⁅conjSubgroup V g, V⁆ ≤ conjSubgroup V g ⊓ V ∧
      ∃ B ∈ E3.gammaSet V 1 (conjSubgroup V g), 2 < Nat.card ↥(commEB E F B) := by
  have h197 : Hyp197 D V X E F g := Hyp198.hyp197 c h hFE hA hAE
  refine ⟨?_, c.exists_card_commEB h162 h4 h197⟩
  obtain ⟨K, hK⟩ := c.exists_conf196 hA (h197.not_comm_le_pCoreOf c)
  exact (hK.V_le_conj_M c h162).2

end Hyp198

end CFSG.LocalAnalysis.WeakClosure81

end
