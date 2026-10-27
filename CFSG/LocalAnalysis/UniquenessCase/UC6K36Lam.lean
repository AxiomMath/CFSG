module

import CFSG.LocalAnalysis.UniquenessCase.UC6K36Rank
import CFSG.LocalAnalysis.UniquenessCase.UC6K36Comp
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Cent
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def comps36 (M : Subgroup G) : Set (Subgroup G) :=
  {K | CFSG.IsComponent K ∧ ⁅K, pCoreOf 2 M⁆ ≠ ⊥}

@[expose] noncomputable def lam36 (M : Subgroup G) : Subgroup G := sSup (comps36 M)

theorem map_conj_mem_comps36 {M K : Subgroup G} (hK : K ∈ comps36 M) {m : G} (hm : m ∈ M) :
    K.map (MulAut.conj m).toMonoidHom ∈ comps36 M := by
  refine ⟨CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj m) hK.1, ?_⟩
  have hQ : (pCoreOf 2 M).map (MulAut.conj m).toMonoidHom = pCoreOf 2 M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm)
  intro hbot
  apply hK.2
  have h1 : ⁅K.map (MulAut.conj m).toMonoidHom, (pCoreOf 2 M).map (MulAut.conj m).toMonoidHom⁆ =
      (⁅K, pCoreOf 2 M⁆).map (MulAut.conj m).toMonoidHom := (Subgroup.map_commutator _ _ _).symm
  rw [hQ, hbot] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj m).injective).1 h1.symm

theorem le_normalizer_lam36 (M : Subgroup G) : M ≤ normalizer (lam36 M : Set G) := by
  have key : ∀ m ∈ M, (lam36 M).map (MulAut.conj m).toMonoidHom ≤ lam36 M := by
    intro m hm
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (map_conj_mem_comps36 hK hm)
  intro m hm
  refine Subgroup.mem_normalizer_iff_map_conj_eq.2 (le_antisymm (key m hm) ?_)
  have h2 := key m⁻¹ (M.inv_mem hm)
  intro x hx
  have hx' : (MulAut.conj m⁻¹).toMonoidHom x ∈ (lam36 M).map (MulAut.conj m⁻¹).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  have := h2 hx'
  refine ⟨_, this, ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
  group

theorem mem_normalizer_sSup {S : Set (Subgroup G)} {x : G}
    (hx : ∀ K ∈ S, x ∈ normalizer (K : Set G)) : x ∈ normalizer ((sSup S : Subgroup G) : Set G) := by
  have key : ∀ y : G, (∀ K ∈ S, y ∈ normalizer (K : Set G)) →
      (sSup S).map (MulAut.conj y).toMonoidHom ≤ sSup S := by
    intro y hy
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have e1 : K.map (MulAut.conj y).toMonoidHom = K := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hy K hK)
    rw [e1]
    exact le_sSup hK
  refine Subgroup.mem_normalizer_iff_map_conj_eq.2 (le_antisymm (key x hx) ?_)
  have h2 := key x⁻¹ (fun K hK => (normalizer (K : Set G)).inv_mem (hx K hK))
  intro z hz
  have hz' : (MulAut.conj x⁻¹).toMonoidHom z ∈ (sSup S).map (MulAut.conj x⁻¹).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hz
  refine ⟨_, h2 hz', ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
  group

namespace Hyp36

variable {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem exists_noncentral_sylow_inf_of_dvd {K : Subgroup G} (hK : CFSG.IsComponent K)
    (hpK : p ∣ Nat.card K) (P : Sylow p G) :
    ∃ x ∈ (P : Subgroup G) ⊓ K, ∃ y ∈ K, x * y ≠ y * x := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨R, hR⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hK.2
  have hRc : (R : Subgroup K) ≤ Subgroup.center K := by
    intro r hr
    rw [Subgroup.mem_center_iff]
    intro g
    have hr' : (r : G) ∈ (P : Subgroup G) ⊓ K := by
      rw [← hR]
      exact ⟨r, hr, rfl⟩
    exact Subtype.ext (hcon r hr' g g.2).symm
  have hbot := eq_bot_of_sylow_le_center_of_isPerfect hK.1.1 R hRc
  have hdvd := R.dvd_card_of_dvd_card hpK
  rw [hbot, Subgroup.card_bot] at hdvd
  exact h.prime.one_lt.ne' (Nat.dvd_one.1 hdvd)

theorem le_of_component_of_not_normalizes {K : Subgroup G} (hK : CFSG.IsComponent K)
    (hpK : p ∣ Nat.card K) (hEN : ¬ E ≤ normalizer (K : Set G)) : K ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, hEP⟩ := IsPGroup.exists_le_sylow h.isPGroup
  have hPM : (P : Subgroup G) ≤ M := h.le_of_isPGroup P.isPGroup' hEP
  have hS := h.exists_noncentral_sylow_inf_of_dvd hK hpK P
  obtain ⟨e, he, heN⟩ := Set.not_subset.1 hEN
  have he1 : e ≠ 1 := by
    rintro rfl
    exact heN (Subgroup.one_mem _)
  have hep : e ^ p = 1 := h.elem.2 e he
  have hord : orderOf e = p := orderOf_eq_prime hep he1
  have hcomm : ∀ i : ℕ, 0 < i → i < p → ∀ x ∈ K, ∀ y ∈ K,
      e ^ i * x * (e ^ i)⁻¹ * y = y * (e ^ i * x * (e ^ i)⁻¹) := by
    intro i hi0 hip x hx y hy
    set Ki : Subgroup G := K.map (MulAut.conj (e ^ i)).toMonoidHom with hKi
    have hcKi : CFSG.IsComponent Ki :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (e ^ i)) hK
    have hne' : K ≠ Ki := by
      intro heq
      have hi : e ^ i ∈ normalizer (K : Set G) := mem_normalizer_of_map_conj_eq heq.symm
      have hcop : Nat.Coprime i (orderOf e) := by
        rw [hord]
        exact ((Nat.Prime.coprime_iff_not_dvd h.prime).2 (Nat.not_dvd_of_pos_of_lt hi0 hip)).symm
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      apply heN
      rw [← hm]
      exact (normalizer (K : Set G)).pow_mem hi m
    have hKc : K ≤ centralizer (Ki : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.1
      ((CFSG.LocalCores.distinct_components_commute hK hcKi).resolve_left hne')
    have hw : e ^ i * x * (e ^ i)⁻¹ ∈ Ki := ⟨x, hx, MulAut.conj_apply (e ^ i) x⟩
    exact Subgroup.mem_centralizer_iff.1 (hKc hy) _ hw
  have hzy : ∀ z ∈ K, ∀ y ∈ (P : Subgroup G) ⊓ K, z * y * z⁻¹ ∈ M := by
    intro z hz y hy
    obtain ⟨d, hde, hd⟩ := exists_mem_centralizer_conj_eq h.prime.pos hep hcomm hz
    have hdM : d ∈ M :=
      h.centralizer_le_of_ne_one he he1 (Subgroup.mem_centralizer_singleton_iff.2 hde)
    rw [← hd y (Subgroup.mem_inf.1 hy).2]
    exact M.mul_mem (M.mul_mem hdM (hPM (Subgroup.mem_inf.1 hy).1)) (M.inv_mem hdM)
  have hcommM : ⁅K, (P : Subgroup G) ⊓ K⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro z hz y hy
    rw [commutatorElement_def]
    exact M.mul_mem (hzy z hz y hy) (M.inv_mem (hPM (Subgroup.mem_inf.1 hy).1))
  have hS' : ¬ ∀ x ∈ (P : Subgroup G) ⊓ K, ∀ y ∈ K, x * y = y * x := by
    intro hall
    obtain ⟨x, hx, y, hy, hxy⟩ := hS
    exact hxy (hall x hx y hy)
  have := commutator_eq_self_of_not_central hK.1 (inf_le_right : (P : Subgroup G) ⊓ K ≤ K) hS'
  rw [← this]
  exact hcommM

end Hyp36

@[expose] def Rank2Good (K : Subgroup G) : Prop :=
  (∃ A : Subgroup G, A ≤ K ∧ IsElemAbelian 3 A ∧ Nat.card A = 9) ∧ Nat.card (Subgroup.center ↥K) ≤ 3

theorem Rank2Good.conj {K : Subgroup G} (hK : Rank2Good K) (g : G) :
    Rank2Good (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨⟨A, hAK, hAel, hAcard⟩, hZ⟩ := hK
  refine ⟨⟨A.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono hAK, hAel.map _, ?_⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hAcard]
  · have e : ↥K ≃* ↥(K.map (MulAut.conj g).toMonoidHom) :=
      K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
    exact hZ

theorem pRank_le_twoLocalPrimeRank {q : ℕ} (hq : q.Prime) {H : Subgroup G} (hH : IsTwoLocal H) :
    CFSG.Open.pRank q H ≤ twoLocalPrimeRank q G := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨H, hH, rfl⟩
  rintro _ ⟨K, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt K

theorem map_conj_map_conj (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

namespace Hyp36

variable {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem normalizes_of_rank (hp3 : p = 3) (he : twoLocalPrimeRank 3 G ≤ 3) {K : Subgroup G}
    (hK : CFSG.IsComponent K) (hpK : p ∣ Nat.card K) (hg : Rank2Good K) :
    E ≤ normalizer (K : Set G) := by
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hEN
  have hKM : K ≤ M := h.le_of_component_of_not_normalizes hK hpK hEN
  obtain ⟨e, heE, heN⟩ := Set.not_subset.1 hEN
  have heM : e ∈ M := h.E_le heE
  have he3 : e ^ 3 = 1 := h.elem.2 e heE
  set K1 : Subgroup G := K.map (MulAut.conj e).toMonoidHom with hK1
  set K2 : Subgroup G := K.map (MulAut.conj (e * e)).toMonoidHom with hK2
  have hcK1 : CFSG.IsComponent K1 := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj e) hK
  have hcK2 : CFSG.IsComponent K2 := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (e * e)) hK
  have hMmap : ∀ m ∈ M, ∀ X : Subgroup G, X ≤ M → X.map (MulAut.conj m).toMonoidHom ≤ M := by
    intro m hm X hX
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hX hx)) (M.inv_mem hm)
  have hK1M : K1 ≤ M := hMmap e heM K hKM
  have hK2M : K2 ≤ M := hMmap (e * e) (M.mul_mem heM heM) K hKM
  have hne01 : K ≠ K1 := fun heq => heN (mem_normalizer_of_map_conj_eq heq.symm)
  have hne02 : K ≠ K2 := by
    intro heq
    have h2 : e * e ∈ normalizer (K : Set G) := mem_normalizer_of_map_conj_eq heq.symm
    apply heN
    have : e = (e * e) * (e * e) := by
      have h3 : e * e * e = 1 := by rw [← pow_three']; exact he3
      calc e = (e * e * e) * e := by rw [h3, one_mul]
        _ = (e * e) * (e * e) := mul_assoc (e * e) e e
    rw [this]
    exact (normalizer (K : Set G)).mul_mem h2 h2
  have hne12 : K1 ≠ K2 := by
    intro heq
    apply hne01
    have h3 := congrArg (fun X : Subgroup G => X.map (MulAut.conj e⁻¹).toMonoidHom) heq
    simp only [hK1, hK2, map_conj_map_conj] at h3
    have e1 : e⁻¹ * e = 1 := inv_mul_cancel e
    rw [e1] at h3
    have e2 : e⁻¹ * (e * e) = e := by group
    rw [e2] at h3
    have e3' : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
      ext x
      simp [MulAut.conj_apply]
    rw [e3'] at h3
    exact h3
  have hcomm : ∀ {X Y : Subgroup G}, CFSG.IsComponent X → CFSG.IsComponent Y → X ≠ Y →
      ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
    intro X Y hX hY hXY x hx y hy
    have hc : ⁅X, Y⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hX hY).resolve_left hXY
    have hXc : X ≤ centralizer (Y : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
    exact (Subgroup.mem_centralizer_iff.1 (hXc hx) y hy).symm
  have g1 : Rank2Good K1 := hg.conj e
  have g2 : Rank2Good K2 := hg.conj (e * e)
  obtain ⟨⟨A0, hA0K, hA0e, hA0c⟩, hZ0⟩ := hg
  obtain ⟨⟨A1, hA1K, hA1e, hA1c⟩, hZ1⟩ := g1
  obtain ⟨⟨A2, hA2K, hA2e, hA2c⟩, hZ2⟩ := g2
  obtain ⟨hB, hBcard⟩ := exists_elemAbelian_of_three_commuting (p := 3)
    (hcomm hK hcK1 hne01) (hcomm hK hcK2 hne02) (hcomm hcK1 hcK2 hne12) hA0K hA1K hA2K hA0e hA1e hA2e
    hA0c hA1c hA2c hZ0 hZ2
  have hBM : A0 ⊔ A1 ⊔ A2 ≤ M := sup_le (sup_le (hA0K.trans hKM) (hA1K.trans hK1M)) (hA2K.trans hK2M)
  have h4 := four_le_pRank_of_elemAbelian hBM hB hBcard
  have hloc : IsTwoLocal M := h.maxTwoLocal.1
  have := (pRank_le_twoLocalPrimeRank (G := G) Nat.prime_three hloc).trans he
  omega

end Hyp36

theorem mem_normalizer_map_sSup (f : G →* G) {S : Set (Subgroup G)} {x : G}
    (hx : ∀ K ∈ S, x ∈ normalizer ((K.map f : Subgroup G) : Set G)) :
    x ∈ normalizer (((sSup S).map f : Subgroup G) : Set G) := by
  have key : ∀ y : G, (∀ K ∈ S, y ∈ normalizer ((K.map f : Subgroup G) : Set G)) →
      ((sSup S).map f).map (MulAut.conj y).toMonoidHom ≤ (sSup S).map f := by
    intro y hy
    rw [Subgroup.map_map, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← Subgroup.map_map]
    have e1 : (K.map f).map (MulAut.conj y).toMonoidHom = K.map f :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hy K hK)
    rw [e1]
    exact Subgroup.map_mono (le_sSup hK)
  refine Subgroup.mem_normalizer_iff_map_conj_eq.2 (le_antisymm (key x hx) ?_)
  have h2 := key x⁻¹ (fun K hK => (normalizer ((K.map f : Subgroup G) : Set G)).inv_mem (hx K hK))
  intro z hz
  have hz' : (MulAut.conj x⁻¹).toMonoidHom z ∈ ((sSup S).map f).map (MulAut.conj x⁻¹).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hz
  refine ⟨_, h2 hz', ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
  group

namespace Hyp36

variable {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem normalizer_lam36_eq_top (hE : ∀ (g : G) (K : Subgroup G), K ∈ comps36 M →
    E ≤ normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    normalizer (lam36 M : Set G) = ⊤ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  set W : Subgroup G := normalizer (lam36 M : Set G) with hW
  have hconj : ∀ (g : G), ∀ e ∈ E, g * e * g⁻¹ ∈ W := by
    intro g e he
    have hnorm : e ∈ normalizer (((lam36 M).map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) :=
      mem_normalizer_map_sSup (MulAut.conj g⁻¹).toMonoidHom (fun K hK => hE g⁻¹ K hK he)
    have e1 : ((lam36 M).map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj e).toMonoidHom =
        (lam36 M).map (MulAut.conj g⁻¹).toMonoidHom := Subgroup.mem_normalizer_iff_map_conj_eq.1 hnorm
    have e2 : ((((lam36 M).map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj e).toMonoidHom).map
        (MulAut.conj g).toMonoidHom) = (lam36 M).map (MulAut.conj (g * e * g⁻¹)).toMonoidHom := by
      rw [map_conj_map_conj, map_conj_map_conj]
    have e3 : (((lam36 M).map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom) =
        lam36 M := by
      rw [map_conj_map_conj, mul_inv_cancel]
      ext x
      simp [MulAut.conj_apply]
    have goal : (lam36 M).map (MulAut.conj (g * e * g⁻¹)).toMonoidHom = lam36 M := by
      rw [← e2, e1, e3]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 goal
  have hN1 : normalClosure (E : Set G) ≤ W := by
    refine (Subgroup.closure_le W).2 fun x hx => ?_
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    exact hconj c a ha
  set N₁ : Subgroup G := normalClosure (E : Set G) with hN₁
  have hEN₁ : E ≤ N₁ := Subgroup.le_normalClosure
  obtain ⟨R, hER⟩ := (h.isPGroup.comap_subtype (K := N₁)).exists_le_sylow
  set R' : Subgroup G := (R : Subgroup N₁).map N₁.subtype with hR'
  have hER' : E ≤ R' := by
    intro x hx
    exact ⟨⟨x, hEN₁ hx⟩, hER (show (⟨x, hEN₁ hx⟩ : N₁) ∈ E.subgroupOf N₁ from hx), rfl⟩
  have hR'p : IsPGroup p R' := R.isPGroup'.map _
  have hR'M : R' ≤ M := h.le_of_isPGroup hR'p hER'
  have hNM : normalizer (R' : Set G) ≤ M := h.normalizer_le_of_le hER' hR'M
  have hfr := Sylow.normalizer_sup_eq_top R
  refine top_le_iff.1 ?_
  rw [← hfr]
  exact sup_le (hNM.trans (le_normalizer_lam36 M)) hN1

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
