module

public import CFSG.Timmesfeld.ARS.CaseEDist
public import CFSG.Timmesfeld.ARS.CaseEWeight

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

section Roots

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem linIndepPair_of_pos (hdiv : D.divisible = ∅) {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (hδ : δ ∈ D.roots) (hγp : 0 < ht γ) (hδp : 0 < ht δ) (hne : γ ≠ δ) : LinIndepPair γ δ := by
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  have hγi := isIndiv_of_divisible_eq_empty hdiv hγ
  have hδi := isIndiv_of_divisible_eq_empty hdiv hδ
  by_contra h
  rcases Φ.proportional γ hγ δ hδ h with h1 | h1 | h1 | h1 | h1 | h1
  · exact hne h1
  · rw [h1, ht_neg] at hγp
    omega
  · exact hγi δ hδ h1
  · rw [h1, ht_neg, ht_nsmul] at hγp
    omega
  · exact hδi γ hγ h1
  · rw [h1, ht_neg, ht_nsmul] at hδp
    omega

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)

include hct in
theorem borel_le_normalizer_rootGroup_of_max (hext : SteinbergExtras D n H)
    (hdiv : D.divisible = ∅) {θ : Fin D.rank → ℤ} (hθ : θ ∈ D.roots)
    (hmax : ∀ γ ∈ D.roots, ht γ ≤ ht θ) :
    borel D H ≤ Subgroup.normalizer (D.rootGroup θ : Set K) := by
  refine sup_le (iSup_le_normalizer_rootGroup hct hθ) (iSup₂_le fun β hβ => ?_)
  obtain ⟨hβr, hβp⟩ := hβ
  by_cases hβθ : β = θ
  · subst hβθ
    exact Subgroup.le_normalizer
  have hθp : 0 < ht θ := lt_of_lt_of_le hβp (hmax β hβr)
  have hind := linIndepPair_of_pos hdiv hθ hβr hθp hβp (Ne.symm hβθ)
  have hcone : ⨆ ε ∈ openCone D.roots θ β, D.rootGroup ε = ⊥ := by
    refine iSup₂_eq_bot.2 fun ε hε => ?_
    exfalso
    obtain ⟨hεr, a, b, ha, hb, rfl⟩ := hε
    have h1 := hmax _ hεr
    rw [ht_add, ht_nsmul, ht_nsmul] at h1
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have h2 : (a : ℤ) * ht θ + b * ht β > ht θ := by nlinarith
    linarith
  intro y hy
  rw [← conjSub_eq_self_iff]
  refine conjSub_of_forall_commute fun x hx => ?_
  have h1 := hext.commutator_mem θ hθ β hβr hind x hx y hy
  rw [hcone, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

include hct in
theorem mem_cellUnion_of_mem_rankOne (hext : SteinbergExtras D n H) (j : Fin D.rank) {y : K}
    (hy : y ∈ D.rootGroup (Pi.single j 1) ⊔ D.rootGroup (-Pi.single j 1)) :
    y ∈ cellUnion hct {1, (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j} := by
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  set S : Set (coxeterMatrix D.isFiniteType).Group :=
    {1, (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j}
  have hS : ∀ k ∈ ({j} : Set (Fin D.rank)), ∀ w ∈ S,
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple k * w ∈ S := by
    rintro k rfl w (rfl | rfl)
    · exact Or.inr (mul_one _)
    · exact Or.inl (CoxeterSystem.simple_mul_simple_self _ _)
  have hnS : ∀ g ∈ cellUnion hct S, n j * g ∈ cellUnion hct S := fun g hg =>
    n_mul_mem_cellUnion_of_stable hct hext hS rfl hg
  have hninv : ∀ g ∈ cellUnion hct S, (n j)⁻¹ * g ∈ cellUnion hct S := fun g hg => by
    have ht : ((n j) ^ 2)⁻¹ ∈ borel D H := inv_mem (iSup_le_borel (sq_n_mem_iSup hct j))
    rw [show (n j)⁻¹ * g = ((n j) ^ 2)⁻¹ * (n j * g) by group]
    exact mul_mem_cellUnion hct ht (hnS g hg)
  have hα : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.single_mem j
  have hXα : ∀ x ∈ D.rootGroup (Pi.single j 1), ∀ g ∈ cellUnion hct S,
      x * g ∈ cellUnion hct S := fun x hx g hg =>
    mul_mem_cellUnion hct (rootGroup_le_borel hα (ht_single_pos j) hx) hg
  have hXβ : ∀ x ∈ D.rootGroup (-Pi.single j 1), ∀ g ∈ cellUnion hct S,
      x * g ∈ cellUnion hct S := fun x hx g hg => by
    have hx' : (n j)⁻¹ * x * n j ∈ D.rootGroup (Pi.single j 1) := by
      have h1 := (actsAs_n hct j).inv_conj_mem (Φ.neg_mem _ hα) hx
      rwa [CoxeterSystem.inv_simple, map_neg, weylAction_simple_single, neg_neg] at h1
    rw [show x * g = n j * ((n j)⁻¹ * x * n j * ((n j)⁻¹ * g)) by group]
    exact hnS _ (hXα _ hx' _ (hninv g hg))
  have key : ∀ z ∈ D.rootGroup (Pi.single j 1) ⊔ D.rootGroup (-Pi.single j 1),
      ∀ g ∈ cellUnion hct S, z * g ∈ cellUnion hct S := by
    intro z hz
    rw [Subgroup.sup_eq_closure] at hz
    induction hz using Subgroup.closure_induction'' with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hXα x hx
      · exact hXβ x hx
    | inv_mem x hx =>
      rcases hx with hx | hx
      · exact hXα _ (inv_mem hx)
      · exact hXβ _ (inv_mem hx)
    | one => exact fun g hg => by rwa [one_mul]
    | mul x z _ _ ihx ihz =>
      intro g hg
      rw [mul_assoc]
      exact ihx _ (ihz g hg)
  have h1 : (1 : K) ∈ cellUnion hct S :=
    (mem_cellUnion hct).2 ⟨1, Or.inl rfl, by rw [bruhatCell_one]; exact one_mem _⟩
  simpa using key y hy 1 h1

end Roots

section Collinear

variable {G : Type} [Group G] {R : Set (Subgroup G)} {K : Type*} [Group K] {A A₀ : Subgroup G}
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {Ψ : K →* G}

theorem Sec13.exists_conjSub_eq_of_mem_leviSet (hS : Sec13 R A A₀) {X Y : Subgroup G}
    (hX : X ∈ leviSet R A A₀) (hY : Y ∈ leviSet R A A₀) :
    ∃ v ∈ levi R A A₀, conjSub X v = Y := by
  obtain ⟨g, hg, hgY⟩ := Sec3.exists_conjSub_eq_of_reflTransGen hS.hyp.root
    (fun X hX => hX.1.1) (hS.conn X hX Y hY)
  have hle : (⨆ D ∈ {D | Relation.ReflTransGen (oppGraph (leviSet R A A₀)) X D}, D) ≤
      levi R A A₀ := by
    refine iSup₂_le fun D hD => ?_
    change Relation.ReflTransGen (oppGraph (leviSet R A A₀)) X D at hD
    cases hD with
    | refl => exact le_gen hX
    | tail _ hcd => exact le_gen hcd.2.1
  exact ⟨g, hle hg, hgY⟩

theorem exists_eq_mul_n_mul_of_mem_lambdaSet (hS : Sec13 R A A₀)
    (hF : LeviFrame R A A₀ D n H Ψ) (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    {C : Subgroup G} (hC : C ∈ lambdaStar R A A₀) (hCU : Commuting C ((posUnipotent D).map Ψ))
    (hCT : (⨆ i, H i).map Ψ ≤ Subgroup.normalizer (C : Set G)) {j : Fin D.rank}
    (hCQ : ∀ k, Commuting C ((D.rootGroup (-Pi.single k 1)).map Ψ) ↔ k ≠ j)
    (hCPl : C ∈ lambdaSet R ((D.rootGroup (Pi.single j 1)).map Ψ))
    (hpat : ∀ γ ∈ D.roots, ¬ Commuting C ((D.rootGroup γ).map Ψ) → γ j = -1)
    {g : K} (hg : conjSub C (Ψ g) ∈ lambdaSet R C) :
    ∃ a ∈ stabOf Ψ C, ∃ b ∈ stabOf Ψ C, g = a * n j * b := by
  have h := hS.hyp
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  set cs := (coxeterMatrix D.isFiniteType).toCoxeterSystem
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  have hct := hF.hct
  have hCR : C ∈ R := hC.1.1.1
  have hB : borel D H ≤ stabOf Ψ C := borel_le_stabOf hCT hCU
  have hPk : ∀ k, Commuting C ((D.rootGroup (Pi.single k 1)).map Ψ) := fun k =>
    hCU.mono le_rfl (Subgroup.map_mono (rootGroup_le_posUnipotent (Φ.single_mem k)
      (ht_single_pos k)))
  have hn : ∀ k ∈ ({k | k ≠ j} : Set (Fin D.rank)), n k ∈ stabOf Ψ C := fun k hk =>
    n_mem_stabOf hF.toCompFrame k (hPk k) ((hCQ k).2 hk)
  have hCg : conjSub C (Ψ g) ∈ lambdaStar R A A₀ :=
    conjSub_mem_lambdaStar_of_mem_levi hR hC (hF.range g)
  obtain ⟨X, hX, hCX⟩ := exists_commutator_eq_of_mem_lambdaStar h hS.mem hS.sec8.2 hS.opp hC hCg
    (mem_lambdaSet_comm hCR hg)
  obtain ⟨θ, hθ, hmax⟩ : ∃ θ ∈ D.roots, ∀ γ ∈ D.roots, ht γ ≤ ht θ :=
    Set.exists_max_image _ ht (finite_roots D.isFiniteType D.divisible) ⟨_, Φ.single_mem j⟩
  obtain ⟨v, hv, hvX⟩ := hS.exists_conjSub_eq_of_mem_leviSet (hF.mem θ hθ) hX
  obtain ⟨h₀, rfl⟩ := hF.surj v hv
  obtain ⟨y, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_bruhatCell hct hF.hext h₀
  have hNθ := borel_le_normalizer_rootGroup_of_max hct hF.hext hF.hdiv hθ hmax
  set γ := weylAction D.isFiniteType y θ with hγdef
  have hγ : γ ∈ D.roots := weylAction_mem_roots _ _ hθ
  have hX' : X = conjSub ((D.rootGroup γ).map Ψ) (Ψ b₁) := by
    rw [← hvX, map_mul, map_mul, conjSub_mul, conjSub_mul, map_conjSub_eq Ψ _ b₂,
      (RankOne.map_conj_eq_self_iff).2 (hNθ hb₂), map_conjSub_eq, actsAs_nrep hct y _ hθ]
  have hCb₁ : conjSub C (Ψ b₁) = C := mem_stabOf.1 (hB hb₁)
  have e1 : ⁅C, X⁆ = conjSub ⁅C, (D.rootGroup γ).map Ψ⁆ (Ψ b₁) := by
    rw [hX', conjSub_commutator, hCb₁]
  have hnc : ¬ Commuting C ((D.rootGroup γ).map Ψ) := by
    intro hc
    rw [commuting_iff_commutator_eq_bot.1 hc] at e1
    have hbot : conjSub C (Ψ g) = ⊥ := by
      rw [← hCX, e1]
      exact Subgroup.map_bot _
    obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hCg.1.1.1
    rw [hbot] at hx
    exact hx1 (Subgroup.mem_bot.1 hx)
  have hγj : γ j = -1 := hpat γ hγ hnc
  have hαj : (-Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.neg_mem _ (Φ.single_mem j)
  have hγ' : -γ ∈ roots D.isFiniteType ∅ := by
    rw [← roots_eq_of_divisible hF.toCompFrame]
    exact Φ.neg_mem _ hγ
  obtain ⟨u, hu, hue⟩ := exists_mem_parabolic_eq_of_level_one D.isFiniteType hpd j hγ'
    (by rw [Pi.neg_apply, hγj, neg_neg])
  have hγu : γ = weylAction D.isFiniteType u (-Pi.single j 1) := by rw [map_neg, hue, neg_neg]
  have hMγ : (D.rootGroup γ).map Ψ =
      conjSub ((D.rootGroup (-Pi.single j 1)).map Ψ) (Ψ (nrep hct u)) := by
    rw [map_conjSub_eq, actsAs_nrep hct u _ hαj, ← hγu]
  have hCu : conjSub C (Ψ (nrep hct u)) = C := mem_stabOf.1 (nrep_mem_stabOf hct hn hu)
  have e2 : ⁅C, (D.rootGroup γ).map Ψ⁆ =
      conjSub ⁅C, (D.rootGroup (-Pi.single j 1)).map Ψ⁆ (Ψ (nrep hct u)) := by
    rw [hMγ, conjSub_commutator, hCu]
  set P := (D.rootGroup (Pi.single j 1)).map Ψ with hPdef
  set Q := (D.rootGroup (-Pi.single j 1)).map Ψ with hQdef
  have hPl := hF.mem _ (Φ.single_mem j)
  have hQl := hF.mem _ hαj
  have hQj : ¬ Commuting C Q := fun hc => ((hCQ j).1 hc) rfl
  have hsCQ : Special R C Q := special_of_not_commuting_of_mem_leviSet h hS.mem hC hQl hQj
  have hCψ : C ∈ psiSet R Q := ⟨hCR, hsCQ.symm⟩
  have hPQo : Opposite P Q := hF.opp j
  have hDR : ⁅Q, C⁆ ∈ R := hsCQ.symm.1
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hCR
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDR
  obtain ⟨x, hx, hxd⟩ := Sec3.exists_conj_eq_of_mem_sup hR hiso hPl.1.1 hQl.1.1 hPQo hCPl hCψ
    (Subgroup.mem_sup_left he) he1 (Subgroup.mem_sup_right hd) hd1
  have hCx : conjSub C x = ⁅Q, C⁆ := Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hCR x) hDR
    (hxd ▸ conj_mem_conjSub x he) hd hd1
  rw [← Subgroup.map_sup] at hx
  obtain ⟨y', hy', rfl⟩ := hx
  have hy'B : y' ∈ bruhatCell hct (cs.simple j) := by
    obtain ⟨w, hw, hy'w⟩ := (mem_cellUnion hct).1 (mem_cellUnion_of_mem_rankOne hct hF.hext j hy')
    rcases hw with rfl | rfl
    · exfalso
      rw [bruhatCell_one] at hy'w
      rw [mem_stabOf.1 (hB hy'w)] at hCx
      refine hsCQ.ne_commutator hR ?_
      rw [Subgroup.commutator_comm]
      exact hCx
    · exact hy'w
  have e3 : conjSub C (Ψ g) = conjSub C (Ψ (b₁ * nrep hct u * y')) := by
    rw [← hCX, e1, e2, Subgroup.commutator_comm C Q, ← hCx, ← conjSub_mul, ← conjSub_mul,
      ← map_mul, ← map_mul]
  obtain ⟨b₃, hb₃, b₄, hb₄, hy'e⟩ := hy'B
  rw [nrep_simple] at hy'e
  have hz : (b₁ * nrep hct u * y')⁻¹ * g ∈ stabOf Ψ C := by
    rw [mem_stabOf, map_mul, conjSub_mul, e3, map_inv, ← conjSub_mul, inv_mul_cancel,
      conjSub_one]
  refine ⟨b₁ * nrep hct u * b₃, mul_mem (mul_mem (hB hb₁) (nrep_mem_stabOf hct hn hu)) (hB hb₃),
    b₄ * ((b₁ * nrep hct u * y')⁻¹ * g), mul_mem (hB hb₄) hz, ?_⟩
  rw [hy'e]
  group

end Collinear

end CFSG.Timmesfeld.ARS
