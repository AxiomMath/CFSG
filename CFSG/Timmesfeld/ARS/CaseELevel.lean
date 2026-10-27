module

public import CFSG.Timmesfeld.ARS.CaseERootSys
public import CFSG.Timmesfeld.ARS.CaseENatural
public import CFSG.Timmesfeld.ARS.Sec13Star

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {G : Type*} [Group G] {R : Set (Subgroup G)} {K : Type*} [Group K] {A A₀ : Subgroup G}
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {Ψ : K →* G}

theorem roots_eq_of_divisible (hF : CompFrame R A A₀ D n H Ψ) :
    D.roots = CFSG.LieType.RootSystem.roots D.isFiniteType ∅ := by
  rw [UniversalRootDatum.roots, hF.hdiv]

theorem special_map_rootGroup (hR : IsRootClass R) (hF : CompFrame R A A₀ D n H Ψ)
    (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {adj : Fin D.rank → Fin D.rank → Prop}
    (hX : IsConfig R adj (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ))
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {γ δ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) (hγδ : γ + δ ∈ D.roots) :
    Special R ((D.rootGroup γ).map Ψ) ((D.rootGroup δ).map Ψ) := by
  rw [roots_eq_of_divisible hF] at hγ hδ hγδ
  obtain ⟨w, a, b, hab, rfl, rfl⟩ := exists_weylAction_pair D.isFiniteType hpd hγ hδ hγδ
  have hsing : ∀ c, (Pi.single c 1 : Fin D.rank → ℤ) ∈ D.roots := fun c =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem c
  rw [← actsAs_nrep hF.hct w _ (hsing a), ← actsAs_nrep hF.hct w _ (hsing b), ← map_conjSub_eq,
    ← map_conjSub_eq]
  refine Sec3.special_conjSub hR ?_ _
  rcases hadj a b hab with h1 | h1
  · exact (hX.edge a b h1).1
  · exact (hX.edge b a h1).1.symm


section Level

variable (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  (hF : CompFrame R A A₀ D n H Ψ) (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef)

theorem weylAction_simple_eq_sub (k : Fin D.rank) {β : Fin D.rank → ℤ}
    (hk : coroot D.cartan k β = 1) :
    weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple k) β =
      β - Pi.single k 1 := by
  rw [weylAction_simple, reflection_apply_coroot, hk, one_smul]

theorem map_rootGroup_eq_conjSub (hF : CompFrame R A A₀ D n H Ψ) (k : Fin D.rank)
    {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) :
    (D.rootGroup β).map Ψ = conjSub ((D.rootGroup (weylAction D.isFiniteType
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple k) β)).map Ψ) (Ψ (n k)) := by
  rw [map_conjSub_eq, actsAs_n hF.hct k _ (weylAction_mem_roots _ _ hβ), ← weylAction_mul_apply,
    CoxeterSystem.simple_mul_simple_self, map_one, Module.End.one_apply]

include hF in
theorem conjSub_n_eq_of_commuting (k : Fin D.rank) {E : Subgroup G}
    (hP : Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ))
    (hQ : Commuting E ((D.rootGroup (-Pi.single k 1)).map Ψ)) : conjSub E (Ψ (n k)) = E := by
  have hm : Ψ (n k) ∈ (D.rootGroup (Pi.single k 1)).map Ψ ⊔
      (D.rootGroup (-Pi.single k 1)).map Ψ := by
    rw [← Subgroup.map_sup]
    exact Subgroup.mem_map_of_mem Ψ (hF.hct.n_mem k)
  exact conjSub_of_forall_commute fun e he => ((hP.sup_right hQ) e he _ hm).symm

variable {E : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
  (hEU : Commuting E ((negUnipotent D).map Ψ))

include h hA hAne hmax hA₀ hF hpd hE hEU in
theorem level_zero_or_one {S : Finset (Fin D.rank)}
    (hS : ∀ k, k ∈ S ↔ ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ))
    {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) (hβ0 : ∀ i, 0 ≤ β i) :
    (∑ k ∈ S, β k = 0 → Commuting E ((D.rootGroup β).map Ψ)) ∧
      (∑ k ∈ S, β k = 1 → E ∈ lambdaSet R ((D.rootGroup (-β)).map Ψ)) := by
  have hR := h.root
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  have hroots := roots_eq_of_divisible hF
  have hsymm := cartan_symm_of_posDef hpd
  induction hN : (ht β).toNat using Nat.strong_induction_on generalizing β with
  | _ N ih =>
    by_cases hsimple : ∃ k, β = Pi.single k 1
    · obtain ⟨k, rfl⟩ := hsimple
      have hsum : ∑ m ∈ S, (Pi.single k 1 : Fin D.rank → ℤ) m = if k ∈ S then 1 else 0 :=
        Finset.sum_pi_single' k 1 S
      refine ⟨fun h0 => ?_, fun h1 => ?_⟩
      · have hk : k ∉ S := fun hk => by
          simp [hsum, hk] at h0
        by_contra hc
        exact hk ((hS k).2 hc)
      · have hk : k ∈ S := by
          by_contra hk
          simp [hsum, hk] at h1
        exact mem_lambdaSet_of_commuting_negUnipotent h hA hAne hmax hA₀ hF hE hEU k
          ((hS k).1 hk)
    push Not at hsimple
    have hβr : β ∈ CFSG.LieType.RootSystem.roots D.isFiniteType ∅ := hroots ▸ hβ
    have hq := cartanForm_eq_two D.isFiniteType hsymm hβr
    have hc1 : ∀ m, coroot D.cartan m β ≤ 1 := fun m =>
      coroot_le_one D.isFiniteType hpd hβr (hsimple m)
    have hex : ∑ k ∈ S, β k ≤ 1 → ∃ k, k ∉ S ∧ 0 < β k ∧ coroot D.cartan k β = 1 := by
      intro hlev
      by_contra hcon
      push Not at hcon
      have h1 : ∑ m ∈ S, β m * coroot D.cartan m β ≤ ∑ m ∈ S, β m :=
        Finset.sum_le_sum fun m _ => by nlinarith [hβ0 m, hc1 m]
      have h2 : ∑ m ∈ Sᶜ, β m * coroot D.cartan m β ≤ 0 := by
        refine Finset.sum_nonpos fun m hm => ?_
        rcases (hβ0 m).lt_or_eq with hpos | hzero
        · have := hcon m (Finset.mem_compl.1 hm) hpos
          have hle : coroot D.cartan m β ≤ 0 := by have := hc1 m; omega
          nlinarith
        · rw [← hzero, zero_mul]
      have h3 := Finset.sum_add_sum_compl S (fun m => β m * coroot D.cartan m β)
      rw [cartanForm] at hq
      omega
    have hstep : ∀ k, k ∉ S → 0 < β k → coroot D.cartan k β = 1 →
        (∑ k ∈ S, β k = 0 → Commuting E ((D.rootGroup β).map Ψ)) ∧
          (∑ k ∈ S, β k = 1 → E ∈ lambdaSet R ((D.rootGroup (-β)).map Ψ)) := by
      intro k hkS hβk hck
      set s := (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple k
      have hs := weylAction_simple_eq_sub k hck
      set β' := β - Pi.single k 1 with hβ'
      have hβ'r : β' ∈ D.roots := by
        rw [← hs]
        exact weylAction_mem_roots _ _ hβ
      have hβ'0 : ∀ i, 0 ≤ β' i := fun i => by
        by_cases hik : i = k
        · subst hik
          simp [hβ']
          omega
        · simp [hβ', Pi.single_eq_of_ne hik, hβ0 i]
      have hht : ht β' = ht β - 1 := by
        rw [hβ', sub_eq_add_neg, ht_add, ht_neg, ht_single]
        ring
      have hlt : (ht β').toNat < N := by
        have hpos : 0 < ht β := lt_of_lt_of_le hβk
          (Finset.single_le_sum (fun i _ => hβ0 i) (Finset.mem_univ k))
        have h1 : (ht β').toNat < (ht β).toNat := by
          rw [hht]
          exact (Int.toNat_lt_toNat hpos).2 (by linarith)
        rw [← hN]
        exact h1
      have hlev : ∑ m ∈ S, β' m = ∑ m ∈ S, β m := Finset.sum_congr rfl fun m hm => by
        have hmk : m ≠ k := fun e => hkS (e ▸ hm)
        simp [hβ', Pi.single_eq_of_ne hmk]
      obtain ⟨ih0, ih1⟩ := ih _ hlt hβ'r hβ'0 rfl
      have hk : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.single_mem k
      have hEn : conjSub E (Ψ (n k)) = E := by
        refine conjSub_n_eq_of_commuting hF k ?_ ?_
        · by_contra hc
          exact hkS ((hS k).2 hc)
        · exact hEU.mono le_rfl (map_rootGroup_le_map_negUnipotent (Φ.neg_mem _ hk)
            (by rw [ht_neg, ht_single]; omega))
      have hMβ : (D.rootGroup β).map Ψ = conjSub ((D.rootGroup β').map Ψ) (Ψ (n k)) := by
        rw [map_rootGroup_eq_conjSub hF k hβ, hs]
      have hMβ' : (D.rootGroup (-β)).map Ψ = conjSub ((D.rootGroup (-β')).map Ψ) (Ψ (n k)) := by
        rw [map_rootGroup_eq_conjSub hF k (Φ.neg_mem _ hβ), map_neg, hs]
      refine ⟨fun h0 => ?_, fun h1 => ?_⟩
      · have h2 := (ih0 (hlev.trans h0)).conjSub (Ψ (n k))
        rwa [hEn, ← hMβ] at h2
      · have h2 := ih1 (hlev.trans h1)
        have h3 : conjSub E (Ψ (n k)) ∈ conjSet (lambdaSet R ((D.rootGroup (-β')).map Ψ))
            (Ψ (n k)) := conjSub_mem_conjSet h2 _
        rwa [conjSet_lambdaSet hR, hEn, ← hMβ'] at h3
    refine ⟨fun h0 => ?_, fun h1 => ?_⟩
    · obtain ⟨k, hkS, hβk, hck⟩ := hex (by omega)
      exact (hstep k hkS hβk hck).1 h0
    · obtain ⟨k, hkS, hβk, hck⟩ := hex (by omega)
      exact (hstep k hkS hβk hck).2 h1


include h hA hAne hmax hA₀ hF hpd hE hEU in
theorem level_le_one {adj : Fin D.rank → Fin D.rank → Prop}
    (hX : IsConfig R adj (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ))
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {S : Finset (Fin D.rank)}
    (hS : ∀ k, k ∈ S ↔ ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ))
    {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) (hβ0 : ∀ i, 0 ≤ β i) : ∑ k ∈ S, β k ≤ 1 := by
  have hR := h.root
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  have hroots := roots_eq_of_divisible hF
  have hsymm := cartan_symm_of_posDef hpd
  induction hN : (ht β).toNat using Nat.strong_induction_on generalizing β with
  | _ N ih =>
    by_contra hlev
    push Not at hlev
    have hβr : β ∈ CFSG.LieType.RootSystem.roots D.isFiniteType ∅ := hroots ▸ hβ
    have hq := cartanForm_eq_two D.isFiniteType hsymm hβr
    obtain ⟨k, hβk, hck⟩ : ∃ k, 0 < β k ∧ 0 < coroot D.cartan k β := by
      by_contra hcon
      push Not at hcon
      have h1 : cartanForm D.cartan β ≤ 0 := Finset.sum_nonpos fun m _ => by
        rcases (hβ0 m).lt_or_eq with hpos | hzero
        · nlinarith [hcon m hpos]
        · rw [← hzero, zero_mul]
      omega
    have hne : β ≠ Pi.single k 1 := by
      rintro rfl
      have h1 : ∑ m ∈ S, (Pi.single k 1 : Fin D.rank → ℤ) m ≤ 1 := by
        rw [Finset.sum_pi_single']
        split_ifs <;> norm_num
      omega
    have hck1 : coroot D.cartan k β = 1 :=
      le_antisymm (coroot_le_one D.isFiniteType hpd hβr hne) hck
    have hs := weylAction_simple_eq_sub k hck1
    set β' := β - Pi.single k 1 with hβ'
    have hβ'r : β' ∈ D.roots := by
      rw [← hs]
      exact weylAction_mem_roots _ _ hβ
    have hβ'0 : ∀ i, 0 ≤ β' i := fun i => by
      by_cases hik : i = k
      · subst hik
        simp [hβ']
        omega
      · simp [hβ', Pi.single_eq_of_ne hik, hβ0 i]
    have hlt : (ht β').toNat < N := by
      have hpos : 0 < ht β := lt_of_lt_of_le hβk
        (Finset.single_le_sum (fun i _ => hβ0 i) (Finset.mem_univ k))
      have hht : ht β' = ht β - 1 := by
        rw [hβ', sub_eq_add_neg, ht_add, ht_neg, ht_single]
        ring
      have h1 : (ht β').toNat < (ht β).toNat := by
        rw [hht]
        exact (Int.toNat_lt_toNat hpos).2 (by linarith)
      rw [← hN]
      exact h1
    have ih' := ih _ hlt hβ'r hβ'0 rfl
    have hsub : ∑ m ∈ S, β' m = ∑ m ∈ S, β m - ∑ m ∈ S, (Pi.single k 1 : Fin D.rank → ℤ) m := by
      rw [hβ']
      simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [Finset.sum_pi_single'] at hsub
    have hkS : k ∈ S := by
      by_contra hkS
      simp only [hkS, ↓reduceIte, sub_zero] at hsub
      omega
    simp only [hkS, ↓reduceIte] at hsub
    have h1 : ∑ m ∈ S, β' m = 1 := by omega
    have hk : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.single_mem k
    have hE1 := (level_zero_or_one h hA hAne hmax hA₀ hF hpd hE hEU hS hβ'r hβ'0).2 h1
    have hEk := mem_lambdaSet_of_commuting_negUnipotent h hA hAne hmax hA₀ hF hE hEU k
      ((hS k).1 hkS)
    have hl1 := hF.mem _ (Φ.neg_mem _ hβ'r)
    have hl2 := hF.mem _ (Φ.neg_mem _ hk)
    have hc := commuting_of_mem_deltaSet h hA hA₀ hE ⟨hl1, mem_lambdaSet_comm hl1.1.1 hE1⟩
      ⟨hl2, mem_lambdaSet_comm hl2.1.1 hEk⟩
    have hsum : -β' + -Pi.single k 1 = -β := by
      rw [hβ']
      abel
    have hsp := special_map_rootGroup hR hF hpd hX hadj (Φ.neg_mem _ hβ'r) (Φ.neg_mem _ hk)
      (by rw [hsum]; exact Φ.neg_mem _ hβ)
    exact hsp.not_commuting hR hc


include h hA hAne hmax hA₀ hF hpd hE hEU in
theorem mem_lambdaSet_of_mem_weylN {adj : Fin D.rank → Fin D.rank → Prop}
    (hX : IsConfig R adj (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ))
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {x : K} (hx : x ∈ weylN n H)
    (j : Fin D.rank)
    (h2 : ¬ Commuting (conjSub E (Ψ x)) ((D.rootGroup (Pi.single j 1)).map Ψ)) :
    conjSub E (Ψ x) ∈ lambdaSet R ((D.rootGroup (-Pi.single j 1)).map Ψ) := by
  classical
  have hR := h.root
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  obtain ⟨w, hw⟩ := exists_actsAs hF.hct hx
  have hj : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.single_mem j
  set β := weylAction D.isFiniteType w⁻¹ (Pi.single j 1) with hβdef
  have hβr : β ∈ D.roots := weylAction_mem_roots _ _ hj
  have hconj : ∀ γ ∈ D.roots, conjSub ((D.rootGroup γ).map Ψ) (Ψ x) =
      (D.rootGroup (weylAction D.isFiniteType w γ)).map Ψ := fun γ hγ => by
    rw [map_conjSub_eq, hw γ hγ]
  have hwβ : weylAction D.isFiniteType w β = Pi.single j 1 := by
    rw [hβdef, weylAction_apply_inv_apply]
  have hP : conjSub ((D.rootGroup β).map Ψ) (Ψ x) = (D.rootGroup (Pi.single j 1)).map Ψ := by
    rw [hconj β hβr, hwβ]
  have hQ : conjSub ((D.rootGroup (-β)).map Ψ) (Ψ x) = (D.rootGroup (-Pi.single j 1)).map Ψ := by
    rw [hconj _ (Φ.neg_mem _ hβr), map_neg, hwβ]
  have hEβ : ¬ Commuting E ((D.rootGroup β).map Ψ) := fun hc => h2 (by
    have := hc.conjSub (Ψ x)
    rwa [hP] at this)
  have hβ0 : ∀ i, 0 ≤ β i := by
    rcases nonneg_or_nonpos D.isFiniteType D.divisible hβr with h0 | h0
    · exact h0
    · exfalso
      refine hEβ (hEU.mono le_rfl (map_rootGroup_le_map_negUnipotent hβr ?_))
      exact ht_neg_of_nonpos hβr h0
  set S := Finset.univ.filter fun k => ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ)
  have hS : ∀ k, k ∈ S ↔ ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ) := fun k => by
    simp [S]
  have hle := level_le_one h hA hAne hmax hA₀ hF hpd hE hEU hX hadj hS hβr hβ0
  have hlv := level_zero_or_one h hA hAne hmax hA₀ hF hpd hE hEU hS hβr hβ0
  have hnn : 0 ≤ ∑ k ∈ S, β k := Finset.sum_nonneg fun k _ => hβ0 k
  rcases (show ∑ k ∈ S, β k = 0 ∨ ∑ k ∈ S, β k = 1 by omega) with h0 | h1
  · exact absurd (hlv.1 h0) hEβ
  · have h3 := hlv.2 h1
    have h4 : conjSub E (Ψ x) ∈ conjSet (lambdaSet R ((D.rootGroup (-β)).map Ψ)) (Ψ x) :=
      conjSub_mem_conjSet h3 _
    rwa [conjSet_lambdaSet hR, hQ] at h4

include h hA hAne hmax hA₀ hF hpd hE hEU in
theorem exists_not_commuting_single (hsurj : ∀ v ∈ levi R A A₀, ∃ g, Ψ g = v) :
    ∃ k, ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ) := by
  classical
  by_contra hcon
  push Not at hcon
  have hR := h.root
  set S : Finset (Fin D.rank) := ∅
  have hS : ∀ k, k ∈ S ↔ ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ) := fun k => by
    simp [S, hcon k]
  have hall : ∀ γ ∈ D.roots, Commuting E ((D.rootGroup γ).map Ψ) := by
    intro γ hγ
    rcases nonneg_or_nonpos D.isFiniteType D.divisible hγ with h0 | h0
    · exact (level_zero_or_one h hA hAne hmax hA₀ hF hpd hE hEU hS hγ h0).1 (by simp [S])
    · exact hEU.mono le_rfl (map_rootGroup_le_map_negUnipotent hγ (ht_neg_of_nonpos hγ h0))
  have hV : levi R A A₀ ≤ Subgroup.centralizer (E : Set G) := by
    intro v hv
    obtain ⟨g, rfl⟩ := hsurj v hv
    have hg : g ∈ ⨆ γ ∈ D.roots, D.rootGroup γ := by
      rw [hF.hct.iSup_eq_top]
      exact Subgroup.mem_top g
    have hle : (⨆ γ ∈ D.roots, D.rootGroup γ).map Ψ ≤ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun γ => ?_
      rw [Subgroup.map_iSup]
      exact iSup_le fun hγ => commuting_iff_le_centralizer.1 (hall γ hγ)
    exact hle (Subgroup.mem_map_of_mem Ψ hg)
  obtain ⟨X, hX, hEX⟩ := exists_mem_leviSet_not_commuting h hA hAne hA₀ hE
  exact hEX (commuting_iff_le_centralizer.2 ((le_gen hX).trans hV))


include h hA hAne hmax hA₀ hF hpd hE hEU in
theorem exists_eq_of_highest_of_exists {adj : Fin D.rank → Fin D.rank → Prop}
    (hX : IsConfig R adj (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ))
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {θ : Fin D.rank → ℤ}
    (hθ : θ ∈ D.roots) (hθ1 : ∀ i, 1 ≤ θ i)
    (hJ : ∃ k, ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ)) :
    ∃ j, θ j = 1 ∧ ∀ k, ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ) ↔ k = j := by
  classical
  set S := Finset.univ.filter fun k => ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ)
  have hS : ∀ k, k ∈ S ↔ ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ) := fun k => by
    simp [S]
  have hle := level_le_one h hA hAne hmax hA₀ hF hpd hE hEU hX hadj hS hθ
    (fun i => le_trans zero_le_one (hθ1 i))
  obtain ⟨j, hj⟩ := hJ
  have hjS : j ∈ S := (hS j).2 hj
  have hcard : (S.card : ℤ) ≤ ∑ k ∈ S, θ k := by
    calc (S.card : ℤ) = ∑ k ∈ S, (1 : ℤ) := by simp
      _ ≤ ∑ k ∈ S, θ k := Finset.sum_le_sum fun k _ => hθ1 k
  have hS1 : S.card = 1 := by
    have : 1 ≤ S.card := Finset.card_pos.2 ⟨j, hjS⟩
    omega
  obtain ⟨j', hj'⟩ := Finset.card_eq_one.1 hS1
  have hjj : j = j' := by
    rw [hj'] at hjS
    simpa using hjS
  refine ⟨j, ?_, fun k => ?_⟩
  · have e : ∑ k ∈ S, θ k = θ j := by rw [hj', hjj, Finset.sum_singleton]
    have := hθ1 j
    omega
  · rw [← hS k, hj', hjj, Finset.mem_singleton]


include h hA hAne hmax hA₀ hF hpd hE hEU in
theorem exists_eq_of_highest {adj : Fin D.rank → Fin D.rank → Prop}
    (hX : IsConfig R adj (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ))
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {θ : Fin D.rank → ℤ}
    (hθ : θ ∈ D.roots) (hθ1 : ∀ i, 1 ≤ θ i) (hsurj : ∀ v ∈ levi R A A₀, ∃ g, Ψ g = v) :
    ∃ j, θ j = 1 ∧ ∀ k, ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ) ↔ k = j :=
  exists_eq_of_highest_of_exists h hA hAne hmax hA₀ hF hpd hE hEU hX hadj hθ hθ1
    (exists_not_commuting_single h hA hAne hmax hA₀ hF hpd hE hEU hsurj)

end Level

end CFSG.Timmesfeld.ARS
