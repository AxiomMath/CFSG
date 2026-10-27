module

public import CFSG.Timmesfeld.ARS.BasicBridge
public import CFSG.LieType.TitsSimplicity.Core
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.RankOne
public import Certificates.Certificate43
public import Mathlib

public section

namespace CFSG.Timmesfeld.ARS

open scoped Pointwise

variable {G : Type*} [Group G]

private theorem conjSub_conjSub_inv_self (H : Subgroup G) (g : G) :
    conjSub (conjSub H g) g⁻¹ = H := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

section Abstract

variable {ι κ : Type*} {U T : Subgroup G} {P Q : ι → Subgroup G} {x : κ → G} {ℓ : κ → ℕ}

theorem exists_mem_conjSub_eq_of_descent (hQ : ∀ j, Q j ≤ U)
    (hD : ∀ k, x k ∈ T ∨ ∃ j k', ∃ m ∈ P j ⊔ Q j, x k = x k' * m ∧ ℓ k' < ℓ k ∧
      conjSub (P j) (x k) ≤ U)
    {E : Subgroup G} (hE : Commuting E U) (k : κ) (hEk : Commuting (conjSub E (x k)) U) :
    ∃ t ∈ T, conjSub E t = conjSub E (x k) := by
  induction hk : ℓ k using Nat.strong_induction_on generalizing k with
  | _ N ih =>
    rcases hD k with hkT | ⟨j, k', m, hm, hxk, hlt, hPU⟩
    · exact ⟨x k, hkT, rfl⟩
    · have hEP : Commuting E (P j) := by
        have h1 := (hEk.mono le_rfl hPU).conjSub (x k)⁻¹
        rwa [conjSub_conjSub_inv_self, conjSub_conjSub_inv_self] at h1
      have hEm : conjSub E m = E := conjSub_of_forall_commute fun e he =>
        ((hEP.sup_right (hE.mono le_rfl (hQ j))) e he m hm).symm
      have hk' : conjSub E (x k) = conjSub E (x k') := by
        rw [hxk, conjSub_mul, hEm]
      obtain ⟨t, ht, hte⟩ := ih (ℓ k') (hk ▸ hlt) k' (hk' ▸ hEk) rfl
      exact ⟨t, ht, hte.trans hk'.symm⟩

theorem exists_mem_conjSub_eq_of_bruhat (hTU : T ≤ Subgroup.normalizer (U : Set G))
    (hxT : ∀ k, ∀ t ∈ T, x k * t * (x k)⁻¹ ∈ T) (hQ : ∀ j, Q j ≤ U)
    (hD : ∀ k, x k ∈ T ∨ ∃ j k', ∃ m ∈ P j ⊔ Q j, x k = x k' * m ∧ ℓ k' < ℓ k ∧
      conjSub (P j) (x k) ≤ U)
    {E : Subgroup G} (hE : Commuting E U) {b b' : G} (hb : b ∈ T ⊔ U) (hb' : b' ∈ T ⊔ U)
    (k : κ) (hEv : Commuting (conjSub E (b * x k * b')) U) :
    ∃ t ∈ T, conjSub E t = conjSub E (b * x k * b') := by
  have hTU' : ((T ⊔ U : Subgroup G) : Set G) = (T : Set G) * (U : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right T U hTU
  have hEu : ∀ u ∈ U, conjSub E u = E := fun u hu =>
    conjSub_of_forall_commute fun e he => (hE e he u hu).symm
  have hb₀ : b ∈ (T : Set G) * (U : Set G) := hTU' ▸ hb
  have hb₀' : b' ∈ (T : Set G) * (U : Set G) := hTU' ▸ hb'
  obtain ⟨t₁, ht₁, u₁, hu₁, rfl⟩ := Set.mem_mul.1 hb₀
  obtain ⟨t₂, ht₂, u₂, hu₂, rfl⟩ := Set.mem_mul.1 hb₀'
  have ht₃ : x k * t₂ * (x k)⁻¹ ∈ T := hxT k t₂ ht₂
  have h₄ : t₁ * u₁ * (x k * t₂ * (x k)⁻¹) ∈ (T : Set G) * (U : Set G) := by
    rw [← hTU']
    exact mul_mem (mul_mem (Subgroup.mem_sup_left ht₁) (Subgroup.mem_sup_right hu₁))
      (Subgroup.mem_sup_left ht₃)
  obtain ⟨t₄, ht₄, u₄, hu₄, he₄⟩ := Set.mem_mul.1 h₄
  have heq : t₁ * u₁ * x k * (t₂ * u₂) = t₄ * u₄ * x k * u₂ := by
    rw [he₄]
    group
  have hconj : conjSub E (t₁ * u₁ * x k * (t₂ * u₂)) =
      conjSub (conjSub (conjSub E (x k)) u₄) t₄ := by
    rw [heq, conjSub_mul, hEu u₂ hu₂, conjSub_mul, conjSub_mul]
  have hFU : Commuting (conjSub (conjSub E (x k)) u₄) U := by
    have hU : conjSub U t₄⁻¹ = U := (RankOne.map_conj_eq_self_iff).2 (hTU (inv_mem ht₄))
    have h1 := (hconj ▸ hEv).conjSub t₄⁻¹
    rwa [conjSub_conjSub_inv_self, hU] at h1
  have hFeq : conjSub (conjSub E (x k)) u₄ = conjSub E (x k) := by
    have h2 : conjSub (conjSub (conjSub E (x k)) u₄) u₄⁻¹ = conjSub (conjSub E (x k)) u₄ :=
      conjSub_of_forall_commute fun y hy => (hFU y hy u₄⁻¹ (inv_mem hu₄)).symm
    rw [conjSub_conjSub_inv_self] at h2
    exact h2.symm
  obtain ⟨t, ht, hte⟩ := exists_mem_conjSub_eq_of_descent hQ hD hE k (hFeq ▸ hFU)
  refine ⟨t₄ * t, mul_mem ht₄ ht, ?_⟩
  rw [hconj, hFeq, conjSub_mul, hte]

theorem exists_mem_conjSub_eq_of_bruhat' {V : Subgroup G}
    (hB : ∀ v ∈ V, ∃ b ∈ T ⊔ U, ∃ k, ∃ b' ∈ T ⊔ U, v = b * x k * b')
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) (hxT : ∀ k, ∀ t ∈ T, x k * t * (x k)⁻¹ ∈ T)
    (hQ : ∀ j, Q j ≤ U)
    (hD : ∀ k, x k ∈ T ∨ ∃ j k', ∃ m ∈ P j ⊔ Q j, x k = x k' * m ∧ ℓ k' < ℓ k ∧
      conjSub (P j) (x k) ≤ U)
    {E : Subgroup G} (hE : Commuting E U) {v : G} (hv : v ∈ V)
    (hEv : Commuting (conjSub E v) U) : ∃ t ∈ T, conjSub E t = conjSub E v := by
  obtain ⟨b, hb, k, b', hb', rfl⟩ := hB v hv
  exact exists_mem_conjSub_eq_of_bruhat hTU hxT hQ hD hE hb hb' k hEv

end Abstract

section Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)

include hct in
theorem exists_eq_mul_mul_negBorel (hext : SteinbergExtras D n H) (g : K) :
    ∃ b ∈ (⨆ i, H i) ⊔ negUnipotent D, ∃ x ∈ weylN n H,
      ∃ b' ∈ (⨆ i, H i) ⊔ negUnipotent D, g = b * x * b' := by
  obtain ⟨w₀, hw₀⟩ := exists_forall_isRightDescent (D := D)
  have hn₀ := nrep_mem_weylN hct w₀
  have hconj : ∀ b ∈ borel D H,
      nrep hct w₀ * b * (nrep hct w₀)⁻¹ ∈ (⨆ i, H i) ⊔ negUnipotent D := by
    intro b hb
    rw [← SetLike.mem_coe, coe_borel hct] at hb
    obtain ⟨t, htT, u, hu, rfl⟩ := Set.mem_mul.1 hb
    rw [show nrep hct w₀ * (t * u) * (nrep hct w₀)⁻¹ =
      nrep hct w₀ * t * (nrep hct w₀)⁻¹ * (nrep hct w₀ * u * (nrep hct w₀)⁻¹) by group]
    exact mul_mem (Subgroup.mem_sup_left (conj_mem_iSup_of_mem_weylN hct hn₀ htT))
      (Subgroup.mem_sup_right (nrep_conj_mem_negUnipotent_of_forall_isRightDescent hct hw₀ hu))
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell hct hext ((nrep hct w₀)⁻¹ * g * nrep hct w₀)
  obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := hw
  refine ⟨_, hconj b₁ hb₁, nrep hct w₀ * nrep hct w * (nrep hct w₀)⁻¹,
    mul_mem (mul_mem hn₀ (nrep_mem_weylN hct w)) (inv_mem hn₀), _, hconj b₂ hb₂, ?_⟩
  calc g = nrep hct w₀ * ((nrep hct w₀)⁻¹ * g * nrep hct w₀) * (nrep hct w₀)⁻¹ := by group
    _ = _ := by rw [he]; group

include hct in
theorem exists_descent_of_mem_weylN (hext : SteinbergExtras D n H) (x : weylN n H) :
    (x : K) ∈ ⨆ i, H i ∨ ∃ j, ∃ x' : weylN n H,
      ∃ m ∈ D.rootGroup (Pi.single j 1) ⊔ D.rootGroup (-Pi.single j 1), (x : K) = x' * m ∧
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.length (weylNHom hct hext x') <
        (coxeterMatrix D.isFiniteType).toCoxeterSystem.length (weylNHom hct hext x) ∧
      (D.rootGroup (Pi.single j 1)).map (MulAut.conj (x : K)).toMonoidHom ≤ negUnipotent D := by
  by_cases hw : weylNHom hct hext x = 1
  · left
    exact mem_iSup_of_actsAs_one hct hext x.2 (hw ▸ actsAs_weylNHom hct hext x)
  · right
    obtain ⟨j, hj⟩ :=
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_rightDescent_of_ne_one hw
    have hnj : n j ∈ weylN n H := n_mem_weylN j
    have hroot := (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
    refine ⟨j, x * ⟨n j, hnj⟩⁻¹, n j, hct.n_mem j, by simp, ?_, ?_⟩
    · rw [map_mul, map_inv, weylNHom_n hct hext j, CoxeterSystem.inv_simple]
      exact hj
    · rw [actsAs_weylNHom hct hext x _ hroot]
      exact rootGroup_le_negUnipotent (weylAction_mem_roots _ _ hroot)
        (ht_weylAction_single_neg hj)

theorem map_conjSub_eq {G : Type*} [Group G] (Ψ : K →* G) (X : Subgroup K) (y : K) :
    conjSub (X.map Ψ) (Ψ y) = (X.map (MulAut.conj y).toMonoidHom).map Ψ := by
  rw [conjSub, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext z
  simp

include hct in
theorem exists_mem_map_conjSub_eq (hext : SteinbergExtras D n H) {G : Type*} [Group G]
    (Ψ : K →* G) {E : Subgroup G} (hE : Commuting E ((negUnipotent D).map Ψ)) (g : K)
    (hEg : Commuting (conjSub E (Ψ g)) ((negUnipotent D).map Ψ)) :
    ∃ t ∈ (⨆ i, H i).map Ψ, conjSub E t = conjSub E (Ψ g) := by
  obtain ⟨b, hb, x, hx, b', hb', rfl⟩ := exists_eq_mul_mul_negBorel hct hext g
  simp only [map_mul] at hEg ⊢
  have hmapsup : ∀ {y : K}, y ∈ (⨆ i, H i) ⊔ negUnipotent D →
      Ψ y ∈ (⨆ i, H i).map Ψ ⊔ (negUnipotent D).map Ψ := fun hy => by
    rw [← Subgroup.map_sup]
    exact Subgroup.mem_map_of_mem Ψ hy
  have hTU : (⨆ i, H i) ≤ Subgroup.normalizer ((negUnipotent D : Subgroup K) : Set K) :=
    le_normalizer_iSup₂ fun t htT γ hγ y hy =>
      (le_iSup₂ (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ ht γ < 0}) => D.rootGroup γ) γ hγ)
        ((Subgroup.mem_normalizer_iff.1 (iSup_le_normalizer_rootGroup hct hγ.1 htT) y).1 hy)
  refine exists_mem_conjSub_eq_of_bruhat (P := fun j => (D.rootGroup (Pi.single j 1)).map Ψ)
    (Q := fun j => (D.rootGroup (-Pi.single j 1)).map Ψ) (x := fun y : weylN n H => Ψ y)
    (ℓ := fun y => (coxeterMatrix D.isFiniteType).toCoxeterSystem.length (weylNHom hct hext y))
    ((Subgroup.map_mono hTU).trans (Subgroup.le_normalizer_map Ψ)) ?_ ?_ ?_ hE (hmapsup hb)
    (hmapsup hb') ⟨x, hx⟩ hEg
  · rintro y _ ⟨s, hs, rfl⟩
    exact ⟨_, conj_mem_iSup_of_mem_weylN hct y.2 hs, by simp⟩
  · intro j
    have hneg : -Pi.single j 1 ∈ D.roots := (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem
      _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j)
    exact Subgroup.map_mono (rootGroup_le_negUnipotent hneg
      (ht_neg_of_nonpos hneg (neg_nonpos.2 (Pi.single_nonneg.2 zero_le_one))))
  · intro y
    rcases exists_descent_of_mem_weylN hct hext y with hy | ⟨j, y', m, hm, hyy, hlt, hle⟩
    · exact Or.inl (Subgroup.mem_map_of_mem Ψ hy)
    · refine Or.inr ⟨j, y', Ψ m, ?_, by simp only [hyy, map_mul], hlt, ?_⟩
      · rw [← Subgroup.map_sup]
        exact Subgroup.mem_map_of_mem Ψ hm
      · rw [map_conjSub_eq]
        exact Subgroup.map_mono hle

end Steinberg

end CFSG.Timmesfeld.ARS
