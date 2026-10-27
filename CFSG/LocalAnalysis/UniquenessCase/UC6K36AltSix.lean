module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddDefChar
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltFix
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup Equiv Equiv.Perm

namespace Alt36

theorem conj_injective {n : ℕ} (hn : 4 ≤ n) :
    Function.Injective (MulAut.conj : alternatingGroup (Fin n) →* MulAut (alternatingGroup (Fin n))) := by
  intro k k' hkk'
  refine Subtype.ext (CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn ?_)
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
  have h := congrArg (fun α : MulAut (alternatingGroup (Fin n)) =>
    ((α x : alternatingGroup (Fin n)) : Perm (Fin n))) hkk'
  simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h

theorem exists_conj_eq_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (α : MulAut (alternatingGroup (Fin 6)))
    (hα : α ^ p = 1) : ∃ s : alternatingGroup (Fin 6), MulAut.conj s = α := by
  set a : CFSG.ComponentClassification.OuterAutomorphisms.Outer (alternatingGroup (Fin 6)) :=
    QuotientGroup.mk α
  have h1 : a ^ p = 1 := by rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have h2 : orderOf a ∣ 4 :=
    (orderOf_dvd_natCard a).trans (CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four 6 (by norm_num))
  have h4 : orderOf a = 1 := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact h
    · rw [h] at h2
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (hp.dvd_of_dvd_pow (h2.trans (by norm_num : 4 ∣ 2 ^ 2)))) hp2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
  obtain ⟨s, hs⟩ := h4
  exact ⟨s, hs⟩

theorem mul_conj_mul_inv {K : Type*} [Group K] (r : MulAut K) (s : K) :
    r * MulAut.conj s * r⁻¹ = MulAut.conj (r s) := by
  refine MulEquiv.ext fun x => ?_
  change r (s * r.symm x * s⁻¹) = r s * x * (r s)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem eq_three_of_sq_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 2 ∣ 360) : p = 3 := by
  have h1 : p ^ 2 ≤ 360 := Nat.le_of_dvd (by norm_num) h
  have h2 : p ≤ 18 := by nlinarith
  interval_cases p
  all_goals first
    | rfl
    | exact absurd rfl hp2
    | (exfalso; revert hp; norm_num; done)
    | (exfalso; revert h; norm_num; done)

theorem card_map_of_faithful {G H : Type*} [Group G] [Group H] (f : G →* H) {E : Subgroup G}
    (hf : ∀ e ∈ E, f e = 1 → e = 1) : Nat.card (E.map f) = Nat.card E := by
  have hinj : Function.Injective (f.comp E.subtype) := by
    intro a b hab
    have h1 : f ((a : G) * (b : G)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.2 hab
    exact Subtype.ext (mul_inv_eq_one.1 (hf _ (E.mul_mem a.2 (E.inv_mem b.2)) h1))
  have hrange : E.map f = (f.comp E.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

end Alt36

namespace Hyp36

open Alt36 Odd

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

theorem false_of_alt_six (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) (φ : ↥L ⧸ center ↥L ≃* alternatingGroup (Fin 6)) : False := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLc : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  have hLM : ¬ L ≤ M := fun hLM => h.false_of_component_le hL hne hLM
  set Ψ : G →* MulAut (alternatingGroup (Fin 6)) := psi L φ with hΨ
  have hcj := conj_injective (n := 6) (by norm_num)
  have hfaith : ∀ e ∈ E, Ψ e = 1 → e = 1 := by
    intro e he hΨe
    by_contra he1
    refine hLM (h.le_of_not_faithful L hLc he he1 fun y hy => ?_)
    rw [← psi_mk_eq_iff L φ e y hy]
    change Ψ e _ = _
    rw [hΨe]
    rfl
  have hinner : ∀ e ∈ E, ∃ s, MulAut.conj s = Ψ e := fun e he =>
    exists_conj_eq_six h.prime h.odd (Ψ e) (by rw [← map_pow, h.elem.2 e he, map_one])
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    haveI := h.elem.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
  obtain ⟨e₀, he₀, he₀1, q₀, hq₀, hq₀e, y₀, hy₀, hy₀'⟩ := h.exists_centralizer_act_nontrivially hLc hne
  set ε := Ψ e₀ with hεdef
  obtain ⟨s₀, hs₀⟩ := hinner e₀ he₀
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  set Rb : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
    (pCoreOf 2 M).map Ψ ⊓ Subgroup.centralizer ({ε} : Set (MulAut (alternatingGroup (Fin 6)))) with hRb
  have hRb2 : IsPGroup 2 Rb := (hQ2.map Ψ).to_le inf_le_left
  have hRbcomm : ∀ r ∈ Rb, r * ε = ε * r := fun r hr =>
    (Subgroup.mem_centralizer_iff.1 hr.2 ε rfl).symm
  have hΨq : Ψ q₀ ≠ 1 := by
    intro h1
    apply hy₀'
    rw [← psi_mk_eq_iff L φ q₀ y₀ hy₀]
    change Ψ q₀ _ = _
    rw [h1]
    rfl
  have hqc : ε * Ψ q₀ = Ψ q₀ * ε := by
    calc ε * Ψ q₀ = Ψ (e₀ * q₀) := (map_mul Ψ e₀ q₀).symm
      _ = Ψ (q₀ * e₀) := by rw [hq₀e]
      _ = Ψ q₀ * ε := map_mul Ψ q₀ e₀
  have hΨqmem : Ψ q₀ ∈ Rb := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem Ψ hq₀, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hqc
  have hRbE : ∀ e ∈ E, ∀ r ∈ Rb, Ψ e * r * (Ψ e)⁻¹ ∈ Rb := by
    intro e he r hr
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hr.1
      rw [← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map.2 ⟨e * q * e⁻¹, (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (h.E_le he)) q).1 hq, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have hc : Commute ε (Ψ e) := by
        change Ψ e₀ * Ψ e = Ψ e * Ψ e₀
        rw [← map_mul, ← map_mul, hcommE e₀ he₀ e he]
      have hr' : Commute ε r := (hRbcomm r hr).symm
      exact (hc.mul_right hr').mul_right hc.inv_right
  have hRbnorm : ∀ k : alternatingGroup (Fin 6), ε k = k → ∀ r ∈ Rb,
      MulAut.conj k * r * (MulAut.conj k)⁻¹ ∈ Rb := by
    intro k hk r hr
    obtain ⟨-, m, hm, hconj⟩ := h.exists_mem_of_fixed L φ he₀ he₀1 hk
    have hc : Commute ε (MulAut.conj k) := commute_conj_of_fix hk
    have hr' : Commute ε r := (hRbcomm r hr).symm
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.1 hr.1
      rw [hconj, ← map_inv, ← map_mul, ← map_mul]
      refine Subgroup.mem_map.2 ⟨m * q' * m⁻¹, ?_, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm.1) q').1 hq'
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (hc.mul_right hr').mul_right hc.inv_right
  have hD : ∀ k : alternatingGroup (Fin 6), MulAut.conj k ∈ Rb → k = 1 := by
    have hs₀p : s₀ ^ p = 1 := hcj (by rw [map_pow, hs₀, ← map_pow, h.elem.2 e₀ he₀, map_one, map_one])
    have hσp : (s₀ : Perm (Fin 6)) ^ p = 1 := by
      rw [← Subgroup.coe_pow, hs₀p]
      rfl
    set RD : Subgroup (Perm (Fin 6)) := (Rb.comap MulAut.conj).map (alternatingGroup (Fin 6)).subtype
    have hRD2 : IsPGroup 2 RD := (hRb2.comap_of_injective _ hcj).map _
    have hcomm₀ : ∀ k : alternatingGroup (Fin 6), MulAut.conj k ∈ Rb → k * s₀ = s₀ * k := by
      intro k hk
      apply hcj
      rw [map_mul, map_mul, hs₀]
      exact hRbcomm _ hk
    have hRDσ : ∀ r ∈ RD, r * (s₀ : Perm (Fin 6)) = (s₀ : Perm (Fin 6)) * r := by
      rintro _ ⟨k, hk, rfl⟩
      exact congrArg Subtype.val (hcomm₀ k hk)
    have hRDn : ∀ g ∈ alternatingGroup (Fin 6), g * (s₀ : Perm (Fin 6)) = (s₀ : Perm (Fin 6)) * g →
        ∀ r ∈ RD, g * r * g⁻¹ ∈ RD := by
      intro g hg hgσ r hr
      obtain ⟨k, hk, rfl⟩ := hr
      have hg' : (⟨g, hg⟩ : alternatingGroup (Fin 6)) * s₀ = s₀ * ⟨g, hg⟩ := Subtype.ext hgσ
      have hfix : ε ⟨g, hg⟩ = ⟨g, hg⟩ := by
        rw [hεdef, ← hs₀, MulAut.conj_apply, ← hg', mul_inv_cancel_right]
      have h1 := hRbnorm ⟨g, hg⟩ hfix _ hk
      rw [← map_inv, ← map_mul, ← map_mul] at h1
      exact ⟨_, h1, rfl⟩
    intro k hk
    by_contra hk1
    have hRD1 : RD ≠ ⊥ := by
      intro hbot
      have hmem : (k : Perm (Fin 6)) ∈ RD := ⟨k, hk, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hk1 (Subtype.ext hmem)
    have hfix2 := card_compl_support_of_normalized h.prime h.odd hσp hRD2 hRDσ hRDn hRD1
    have hmod := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := (s₀ : Perm (Fin 6)))
      (by rw [pow_one]; exact hσp)
    rw [Fintype.card_fin] at hmod
    have hp2 : p ∣ 2 ^ 2 := by
      rcases hfix2 with h2 | h4
      · rw [h2] at hmod
        have h3 : p ∣ 6 - 2 := (Nat.modEq_iff_dvd' (by norm_num)).1 hmod
        norm_num at h3
        exact h3
      · rw [h4] at hmod
        have h3 : p ∣ 6 - 4 := (Nat.modEq_iff_dvd' (by norm_num)).1 hmod
        norm_num at h3
        exact h3.trans (by norm_num)
    exact h.odd ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 (h.prime.dvd_of_dvd_pow hp2))
  have hcent : ∀ r ∈ Rb, ∀ e ∈ E, r * Ψ e = Ψ e * r := by
    intro r hr e he
    obtain ⟨s, hs⟩ := hinner e he
    have hc1 : r * Ψ e * r⁻¹ * (Ψ e)⁻¹ ∈ Rb := by
      have := Rb.mul_mem hr (hRbE e he r⁻¹ (Rb.inv_mem hr))
      simpa only [mul_assoc] using this
    have hc2 : r * Ψ e * r⁻¹ * (Ψ e)⁻¹ = MulAut.conj (r s * s⁻¹) := by
      rw [← hs, mul_conj_mul_inv, map_mul, map_inv]
    rw [hc2] at hc1
    have h3 : r s = s := mul_inv_eq_one.1 (hD _ hc1)
    calc r * Ψ e = r * Ψ e * r⁻¹ * (Ψ e)⁻¹ * Ψ e * r := by group
      _ = Ψ e * r := by rw [hc2, h3, mul_inv_cancel, map_one, one_mul]
  set Et : Subgroup (alternatingGroup (Fin 6)) := (E.map Ψ).comap MulAut.conj with hEt
  have hEtmap : Et.map MulAut.conj = E.map Ψ := by
    refine Subgroup.map_comap_eq_self ?_
    rintro _ ⟨e, he, rfl⟩
    exact hinner e he
  have hcardE : Nat.card (E.map Ψ) = p ^ 2 := by
    rw [card_map_of_faithful Ψ hfaith, h.card]
  have hcardEt : Nat.card Et = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hcj, hEtmap, hcardE]
  have hp3 : p = 3 := by
    have h1 := Subgroup.card_subgroup_dvd_card Et
    rw [hcardEt, card_alt_six] at h1
    exact eq_three_of_sq_dvd h.prime h.odd h1
  subst hp3
  have hEt3 : IsPGroup 3 Et := IsPGroup.of_card hcardEt
  obtain ⟨P, hEtP⟩ := hEt3.exists_le_sylow
  have hPEt : (P : Subgroup (alternatingGroup (Fin 6))) = Et := by
    refine (Subgroup.eq_of_le_of_card_ge hEtP ?_).symm
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have hdvd := Subgroup.card_subgroup_dvd_card (P : Subgroup (alternatingGroup (Fin 6)))
    rw [hk, card_alt_six] at hdvd
    have hk2 : k ≤ 2 := by
      by_contra hk2
      have h27 : 3 ^ 3 ∣ 360 := (pow_dvd_pow 3 (by omega : 3 ≤ k)).trans hdvd
      norm_num at h27
    rw [hk, hcardEt]
    exact Nat.pow_le_pow_right (by norm_num) hk2
  have hfixEt : ∀ r ∈ Rb, ∀ s ∈ Et, r s = s := by
    intro r hr s hs
    obtain ⟨e, he, hes⟩ := Subgroup.mem_map.1 (show MulAut.conj s ∈ E.map Ψ from hs)
    have h1 := hcent r hr e he
    rw [hes] at h1
    apply hcj
    rw [← mul_conj_mul_inv, h1, mul_inv_cancel_right]
  letI : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have h9 : Fintype.card (GaloisField 3 2) = 9 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨χ⟩ := CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
    (GaloisField 3 2) h9
  set U : Sylow 3 (CFSG.AGLEmbedding.PSL2GF 3 2) :=
    P.mapSurjective (f := χ.symm.toMonoidHom) χ.symm.surjective
  have hrb : ∀ r ∈ Rb, r = 1 := by
    intro r hr
    set α : MulAut (CFSG.AGLEmbedding.PSL2GF 3 2) := MulAut.congr χ.symm r with hαdef
    have hα : ∀ u ∈ (U : Subgroup (CFSG.AGLEmbedding.PSL2GF 3 2)), α u = u := by
      intro u hu
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hu
      have hsEt : s ∈ Et := hPEt ▸ hs
      change χ.symm (r (χ (χ.symm s))) = χ.symm s
      rw [MulEquiv.apply_symm_apply, hfixEt r hr s hsEt]
    obtain ⟨u, -, hu⟩ := CFSG.AGLEmbedding.kFactL2UnipotentCentralizer 3 2 (by norm_num) (by norm_num) U α hα
    have hr' : r = MulAut.conj (χ u) := by
      apply (MulAut.congr χ.symm).injective
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.symm_apply_apply]
      exact hu
    have h1 := hD (χ u) (hr' ▸ hr)
    rw [hr', h1, map_one]
  exact hΨq (hrb _ hΨqmem)

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
