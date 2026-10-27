module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Steinberg.CentralExt.BorelIndex

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

section SylowCentral

variable {U : Type*} [Group U] (Δ : UniversalRootDatum U)

@[expose] def GGRootSylowCentralAt (γ : Fin Δ.rank → ℤ) : Prop :=
  ∃ S : Subgroup U, IsPGroup 2 S ∧ ¬ 2 ∣ S.index ∧ Δ.rootGroup γ ≤ S ∧
    S ≤ Subgroup.centralizer (Δ.rootGroup γ : Set U)

@[expose] def GGRootSylowCentral (t : StatedLieTag) : Prop :=
  ∀ γ, GGRootClass Δ t γ → GGRootSylowCentralAt Δ γ

variable {Δ}

theorem exists_sylow_of_sylowCentralAt {G : Type*} [Group G] (ψ : U →* G)
    {γ : Fin Δ.rank → ℤ} (hγ : GGRootSylowCentralAt Δ γ) {u : U} {r : G}
    (hr : r ∈ ggRootSub Δ ψ γ u) :
    ∃ T : Sylow 2 ψ.range, r ∈ (T : Subgroup ψ.range).map ψ.range.subtype ∧
      (T : Subgroup ψ.range).map ψ.range.subtype ≤ Subgroup.centralizer {r} := by
  obtain ⟨S, hS2, hSi, hXS, hSC⟩ := hγ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S₁ : Subgroup U := S.map (MulAut.conj u).toMonoidHom with hS₁
  have hS₁i : S₁.index = S.index := Subgroup.index_map_equiv S (MulAut.conj u)
  set T₀ : Subgroup ψ.range := S₁.map ψ.rangeRestrict with hT₀
  have hT₀2 : IsPGroup 2 T₀ := (hS2.map _).map _
  have hT₀i : ¬ 2 ∣ T₀.index := fun h => hSi
    (hS₁i ▸ h.trans (Subgroup.index_map_dvd S₁ ψ.rangeRestrict_surjective))
  have hmap : T₀.map ψ.range.subtype = S₁.map ψ := by
    rw [hT₀, Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
  refine ⟨hT₀2.toSylow hT₀i, ?_, ?_⟩
  · rw [IsPGroup.toSylow_coe, hmap]
    exact Subgroup.map_mono (Subgroup.map_mono hXS) hr
  · rw [IsPGroup.toSylow_coe, hmap]
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hr
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzs : z * s = s * z := (Subgroup.mem_centralizer_iff.mp (hSC hs)) z hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_mul]
    congr 1
    calc u * s * u⁻¹ * (u * z * u⁻¹) = u * (s * z) * u⁻¹ := by group
      _ = u * (z * s) * u⁻¹ := by rw [hzs]
      _ = u * z * u⁻¹ * (u * s * u⁻¹) := by group

theorem ggRootInvolution_central_of_sylowCentral {t : StatedLieTag} (h : GGRootSylowCentral Δ t)
    {G : Type*} [Group G] (ψ : U →* G) (G₀ : Subgroup G) (hG₀ : ψ.range = G₀) {r : G}
    (hr : GGRootInvolution Δ t ψ r) :
    ∃ T : Sylow 2 G₀, r ∈ (T : Subgroup G₀).map G₀.subtype ∧
      (T : Subgroup G₀).map G₀.subtype ≤ Subgroup.centralizer {r} := by
  subst hG₀
  obtain ⟨-, γ, hγ, u, hru⟩ := hr
  exact exists_sylow_of_sylowCentralAt ψ (h γ hγ) hru

end SylowCentral

section Structure

variable {U : Type*} [Group U] {D : UniversalRootDatum U} {n : Fin D.rank → U}
  {H : Fin D.rank → Subgroup U}

theorem ggRootSylowCentralAt_weylAction
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hU2 : IsPGroup 2 (posUnipotent D)) (hUi : ¬ 2 ∣ (posUnipotent D).index)
    {c : Fin D.rank → ℤ} (hc : c ∈ D.roots) (hcU : D.rootGroup c ≤ posUnipotent D)
    (hcC : posUnipotent D ≤ Subgroup.centralizer (D.rootGroup c : Set U))
    (w : (coxeterMatrix D.isFiniteType).Group) :
    GGRootSylowCentralAt D (weylAction D.isFiniteType w c) := by
  set x := nrep hct w
  have hx : (D.rootGroup c).map (MulAut.conj x).toMonoidHom =
      D.rootGroup (weylAction D.isFiniteType w c) := actsAs_nrep hct w c hc
  refine ⟨(posUnipotent D).map (MulAut.conj x).toMonoidHom, hU2.map _, ?_, ?_, ?_⟩
  · rwa [show (posUnipotent D).map (MulAut.conj x).toMonoidHom =
      (posUnipotent D).map ((MulAut.conj x : U ≃* U) : U →* U) from rfl,
      Subgroup.index_map_equiv]
  · rw [← hx]
    exact Subgroup.map_mono hcU
  · rw [← hx]
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    have hzs : z * s = s * z := (Subgroup.mem_centralizer_iff.mp (hcC hs)) z hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc x * z * x⁻¹ * (x * s * x⁻¹) = x * (z * s) * x⁻¹ := by group
      _ = x * (s * z) * x⁻¹ := by rw [hzs]
      _ = x * s * x⁻¹ * (x * z * x⁻¹) := by group

theorem isPGroup_posUnipotent_two (hext : SteinbergExtras D n H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ)) : IsPGroup 2 (posUnipotent D) :=
  isPGroup_iSup_pos hext hX

theorem not_two_dvd_index_posUnipotent [Finite U]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup U))) :
    ¬ 2 ∣ (posUnipotent D).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
    (CentralExt.BorelIndex.coprime_index_posUnipotent hct hext hBU hX hT)

theorem ggRootSylowCentral_of_orbit [Finite U]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup U))) {C : Set (Fin D.rank → ℤ)}
    (hC : ∀ c ∈ C, c ∈ D.roots ∧ 0 < ht c ∧
      posUnipotent D ≤ Subgroup.centralizer (D.rootGroup c : Set U))
    {t : StatedLieTag}
    (horb : ∀ γ, GGRootClass D t γ → ∃ w, ∃ c ∈ C, γ = weylAction D.isFiniteType w c) :
    GGRootSylowCentral D t := by
  intro γ hγ
  obtain ⟨w, c, hcC, rfl⟩ := horb γ hγ
  obtain ⟨hc, hcpos, hcent⟩ := hC c hcC
  exact ggRootSylowCentralAt_weylAction hct (isPGroup_posUnipotent_two hext hX)
    (not_two_dvd_index_posUnipotent hct hext hBU hX hT) hc (rootGroup_le_posUnipotent hc hcpos)
    hcent w

end Structure

section MaxHeight

variable {U : Type*} [Group U] {D : UniversalRootDatum U} {n : Fin D.rank → U}
  {H : Fin D.rank → Subgroup U}

omit [Group U] in
private theorem ht_neg_eq {ι : Type*} [Fintype ι] (v : ι → ℤ) : ht (-v) = -ht v := by
  rw [← htHom_apply, ← htHom_apply, map_neg]

omit [Group U] in
private theorem ht_nsmul_add_eq {ι : Type*} [Fintype ι] (a b : ℕ) (v w : ι → ℤ) :
    ht (a • v + b • w) = a * ht v + b * ht w := by
  rw [← htHom_apply, map_add, map_nsmul, map_nsmul, htHom_apply, htHom_apply, nsmul_eq_mul,
    nsmul_eq_mul]

omit [Group U] in
private theorem ht_two_nsmul_eq {ι : Type*} [Fintype ι] (v : ι → ℤ) : ht (2 • v) = 2 * ht v := by
  rw [← htHom_apply, map_nsmul, htHom_apply, nsmul_eq_mul]
  rfl

theorem posUnipotent_le_centralizer_of_maxHeight (hext : SteinbergExtras D n H)
    {γ₀ : Fin D.rank → ℤ} (hγ₀ : γ₀ ∈ D.roots) (hmax : ∀ δ ∈ D.roots, ht δ ≤ ht γ₀)
    (hab : ∀ x ∈ D.rootGroup γ₀, ∀ y ∈ D.rootGroup γ₀, x * y = y * x)
    (hhalf : ∀ δ ∈ D.roots, γ₀ = 2 • δ →
      ∀ x ∈ D.rootGroup γ₀, ∀ y ∈ D.rootGroup δ, x * y = y * x) :
    posUnipotent D ≤ Subgroup.centralizer (D.rootGroup γ₀ : Set U) := by
  have h0 : 0 ≤ ht γ₀ := by
    have := hmax _ ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem γ₀ hγ₀)
    rw [ht_neg_eq] at this
    omega
  refine iSup₂_le fun δ hδ => ?_
  obtain ⟨hδr, hδpos⟩ := hδ
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  by_cases hli : LinIndepPair γ₀ δ
  · have hc := hext.commutator_mem γ₀ hγ₀ δ hδr hli x hx y hy
    have hbot : (⨆ ε ∈ openCone D.roots γ₀ δ, D.rootGroup ε) = ⊥ := by
      refine iSup₂_eq_bot.2 fun ε hε => ?_
      exfalso
      obtain ⟨hεr, a, b, ha, hb, rfl⟩ := hε
      have hle := hmax _ hεr
      rw [ht_nsmul_add_eq] at hle
      have h1 : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have h2 : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · rcases (RootSystem.ofCartan D.isFiniteType D.divisible).proportional γ₀ hγ₀ δ hδr hli with
      e | e | e | e | e | e
    · subst e
      exact hab x hx y hy
    · rw [e, ht_neg_eq] at h0
      omega
    · exact hhalf δ hδr e x hx y hy
    · rw [e, ht_neg_eq, ht_two_nsmul_eq] at h0
      omega
    · have hle := hmax δ hδr
      rw [e, ht_two_nsmul_eq] at hle hδpos
      omega
    · rw [e, ht_neg_eq, ht_two_nsmul_eq] at hδpos
      omega

theorem posUnipotent_le_centralizer_of_nextHeight (hext : SteinbergExtras D n H)
    (hD : D.divisible = ∅) {γ₁ θ : Fin D.rank → ℤ} (hγ₁ : γ₁ ∈ D.roots) (hpos : 0 < ht γ₁)
    (hnext : ∀ ε ∈ D.roots, ht γ₁ < ht ε → ε = θ)
    (hab : ∀ x ∈ D.rootGroup γ₁, ∀ y ∈ D.rootGroup γ₁, x * y = y * x)
    (hspec : ∀ δ ∈ D.roots, 0 < ht δ → (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ θ = a • γ₁ + b • δ) →
      ∀ x ∈ D.rootGroup γ₁, ∀ y ∈ D.rootGroup δ, x * y = y * x) :
    posUnipotent D ≤ Subgroup.centralizer (D.rootGroup γ₁ : Set U) := by
  refine iSup₂_le fun δ hδ => ?_
  obtain ⟨hδr, hδpos⟩ := hδ
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  by_cases hθ : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ θ = a • γ₁ + b • δ
  · exact hspec δ hδr hδpos hθ x hx y hy
  by_cases hli : LinIndepPair γ₁ δ
  · have hc := hext.commutator_mem γ₁ hγ₁ δ hδr hli x hx y hy
    have hbot : (⨆ ε ∈ openCone D.roots γ₁ δ, D.rootGroup ε) = ⊥ := by
      refine iSup₂_eq_bot.2 fun ε hε => ?_
      exfalso
      obtain ⟨hεr, a, b, ha, hb, rfl⟩ := hε
      have hlt : ht γ₁ < ht (a • γ₁ + b • δ) := by
        rw [ht_nsmul_add_eq]
        have h1 : (1 : ℤ) ≤ a := by exact_mod_cast ha
        have h2 : (1 : ℤ) ≤ b := by exact_mod_cast hb
        nlinarith
      exact hθ ⟨a, b, ha, hb, (hnext _ hεr hlt).symm⟩
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · rcases eq_or_eq_neg_of_not_linIndepPair D.isFiniteType hD hγ₁ hδr hli with e | e
    · subst e
      exact hab x hx y hy
    · rw [e, ht_neg_eq] at hδpos
      omega

theorem ht_pos_of_maxHeight {γ₀ : Fin D.rank → ℤ} (hγ₀ : γ₀ ∈ D.roots)
    (hmax : ∀ δ ∈ D.roots, ht δ ≤ ht γ₀) : 0 < ht γ₀ := by
  have h0 : 0 ≤ ht γ₀ := by
    have := hmax _ ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem γ₀ hγ₀)
    rw [ht_neg_eq] at this
    omega
  rcases (RootSystem.ofCartan D.isFiniteType D.divisible).mem_pos_or_mem_neg hγ₀ with h | h
  · exact h.2
  · have : ht γ₀ < 0 := h.2
    omega

theorem not_eq_two_smul_of_divisible_eq_empty (hD : D.divisible = ∅)
    {γ₀ δ : Fin D.rank → ℤ} (hδ : δ ∈ D.roots) (hγ₀ : γ₀ ∈ D.roots) : γ₀ ≠ 2 • δ := by
  rintro rfl
  exact two_smul_notMem_roots D.isFiniteType hD hδ hγ₀

end MaxHeight

section Orbit

variable {U : Type*} [Group U] {D : UniversalRootDatum U}

@[expose] def GGSimpleConj (D : UniversalRootDatum U) (i j : Fin D.rank) : Prop :=
  ∃ w, weylAction D.isFiniteType w (Pi.single i 1) = Pi.single j 1

theorem GGSimpleConj.refl (i : Fin D.rank) : GGSimpleConj D i i :=
  ⟨1, by rw [map_one, Module.End.one_apply]⟩

theorem GGSimpleConj.symm {i j : Fin D.rank} (h : GGSimpleConj D i j) : GGSimpleConj D j i := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w⁻¹, by rw [← hw, weylAction_inv_apply_apply]⟩

theorem GGSimpleConj.trans {i j k : Fin D.rank} (h : GGSimpleConj D i j)
    (h' : GGSimpleConj D j k) : GGSimpleConj D i k := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  exact ⟨w' * w, by rw [weylAction_mul_apply, hw, hw']⟩

theorem ggSimpleConj_of_cartan_eq {i j : Fin D.rank} (hij : D.cartan i j = -1)
    (hji : D.cartan j i = -1) : GGSimpleConj D i j := by
  refine ⟨(coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i *
    (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j, ?_⟩
  have h1 : reflection D.cartan j (Pi.single i 1) = Pi.single i 1 + Pi.single j 1 := by
    rw [reflection_apply_coroot, coroot_single, hji]
    module
  have h2 : coroot D.cartan i (Pi.single i 1 + Pi.single j 1) = 1 := by
    rw [map_add, coroot_single, coroot_single, D.isFiniteType.apply_self i, hij]
    norm_num
  rw [weylAction_mul_apply, weylAction_simple, weylAction_simple, h1, reflection_apply_coroot, h2]
  module

theorem exists_weylAction_eq_of_simpleConj (hD : D.divisible = ∅)
    (hconj : ∀ i j, GGSimpleConj D i j) {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (hδ : δ ∈ D.roots) : ∃ w, γ = weylAction D.isFiniteType w δ := by
  rcases hγ with ⟨w₁, i, rfl⟩ | ⟨_, i, hi, -⟩
  swap
  · rw [hD] at hi
    exact hi.elim
  rcases hδ with ⟨w₂, j, rfl⟩ | ⟨_, j, hj, -⟩
  swap
  · rw [hD] at hj
    exact hj.elim
  obtain ⟨v, hv⟩ := hconj j i
  exact ⟨w₁ * v * w₂⁻¹, by rw [weylAction_mul_apply, weylAction_mul_apply,
    weylAction_inv_apply_apply, hv]⟩

theorem exists_maxHeight (hr : 0 < D.rank) :
    ∃ γ₀ ∈ D.roots, ∀ δ ∈ D.roots, ht δ ≤ ht γ₀ := by
  have hfin : D.roots.Finite := (RootSystem.ofCartan D.isFiniteType D.divisible).finite_roots
  have hne : D.roots.Nonempty :=
    ⟨_, (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem ⟨0, hr⟩⟩
  exact Set.exists_max_image D.roots ht hfin hne

theorem ggLongRoot_of_simpleConj (hD : D.divisible = ∅) (hconj : ∀ i j, GGSimpleConj D i j)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) : GGLongRoot D γ := by
  have hr : 0 < D.rank := by
    rcases hγ with ⟨w, i, -⟩ | ⟨_, i, -, -⟩ <;> exact Fin.pos i
  obtain ⟨γ₀, hγ₀, hmax⟩ := exists_maxHeight hr
  obtain ⟨w, hw⟩ := exists_weylAction_eq_of_simpleConj hD hconj hγ hγ₀
  exact ⟨w, γ₀, hγ₀, hmax, hw⟩

end Orbit

section Long

variable {U : Type*} [Group U] {D : UniversalRootDatum U} {n : Fin D.rank → U}
  {H : Fin D.rank → Subgroup U}

theorem GGRootClass.longRoot_of_twisted {t : StatedLieTag} (ht : GGTwistedTag t)
    {γ : Fin D.rank → ℤ} (hγ : GGRootClass D t γ) : GGLongRoot D γ :=
  hγ.2 ht

theorem GGRootClass.longRoot_of_simpleConj (hD : D.divisible = ∅)
    (hconj : ∀ i j, GGSimpleConj D i j) {t : StatedLieTag} {γ : Fin D.rank → ℤ}
    (hγ : GGRootClass D t γ) : GGLongRoot D γ :=
  ggLongRoot_of_simpleConj hD hconj hγ.1

theorem ggRootSylowCentral_of_longRoot [Finite U]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup U)))
    (hab : ∀ γ₀ ∈ D.roots, (∀ δ ∈ D.roots, ht δ ≤ ht γ₀) →
      ∀ x ∈ D.rootGroup γ₀, ∀ y ∈ D.rootGroup γ₀, x * y = y * x)
    (hhalf : ∀ γ₀ ∈ D.roots, (∀ δ ∈ D.roots, ht δ ≤ ht γ₀) → ∀ δ ∈ D.roots, γ₀ = 2 • δ →
      ∀ x ∈ D.rootGroup γ₀, ∀ y ∈ D.rootGroup δ, x * y = y * x)
    {t : StatedLieTag} (hlong : ∀ γ, GGRootClass D t γ → GGLongRoot D γ) :
    GGRootSylowCentral D t := by
  refine ggRootSylowCentral_of_orbit hct hext hBU hX hT
    (C := {c | c ∈ D.roots ∧ ∀ δ ∈ D.roots, ht δ ≤ ht c})
    (fun c hc => ⟨hc.1, ht_pos_of_maxHeight hc.1 hc.2,
      posUnipotent_le_centralizer_of_maxHeight hext hc.1 hc.2 (hab c hc.1 hc.2)
        (hhalf c hc.1 hc.2)⟩) fun γ hγ => ?_
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hlong γ hγ
  exact ⟨w, γ₀, ⟨hγ₀, hmax⟩, rfl⟩

theorem ggRootSylowCentral_of_longRoot_reduced [Finite U]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hD : D.divisible = ∅)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup U)))
    (hab : ∀ γ₀ ∈ D.roots, (∀ δ ∈ D.roots, ht δ ≤ ht γ₀) →
      ∀ x ∈ D.rootGroup γ₀, ∀ y ∈ D.rootGroup γ₀, x * y = y * x)
    {t : StatedLieTag} (hlong : ∀ γ, GGRootClass D t γ → GGLongRoot D γ) :
    GGRootSylowCentral D t :=
  ggRootSylowCentral_of_longRoot hct hext hBU hX hT hab
    (fun _ hγ₀ _ _ hδ e => absurd e (not_eq_two_smul_of_divisible_eq_empty hD hδ hγ₀)) hlong

end Long

section CharTwo

theorem isPGroup_two_range_of_charTwo {F G : Type*} [Ring F] [CharP F 2] [Group G]
    (f : Multiplicative F →* G) : IsPGroup 2 f.range := by
  rintro ⟨_, c, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  have hc : c ^ 2 = 1 := by
    rw [pow_two]
    exact Multiplicative.toAdd.injective
      (by rw [toAdd_mul, toAdd_one, CharTwo.add_self_eq_zero])
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, hc, map_one]

theorem range_mul_comm {A G : Type*} [CommGroup A] [Group G] (f : A →* G) :
    ∀ x ∈ f.range, ∀ y ∈ f.range, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, mul_comm, map_mul]

theorem coprime_two_card_of_sq_eq_one {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (h : ∀ g ∈ H, g ^ 2 = 1 → g = 1) : Nat.Coprime 2 (Nat.card H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have h1 : (g : G) = 1 := h g g.2 (by
    rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one, Subgroup.coe_one])
  have h2 : g = 1 := Subtype.ext h1
  rw [h2, orderOf_one] at hg
  exact absurd hg (by norm_num)

end CharTwo

end CFSG.StandardType
