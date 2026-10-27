module

public import CFSG.LocalAnalysis.StandardType.PhanEFixedTorus

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {w₀ : (coxeterMatrix D.isFiniteType).Group}
  {F : FrobData D n H w₀} {n₀ : K} (L : StdLevi F n₀)
  {G : Type} [Group G] {ρ : G →* K} (hρ : Function.Injective ρ) (hρr : ρ.range = stdFix F n₀)
  {Kf : Type} [Field Kf] [Finite Kf] {f : ℕ} [CharP Kf 2] (κ : Kf ≃+* L.Fld)
  (hκ : ∀ c, κ (unitaryInvolution Kf 2 f c) = L.θ (κ c))

@[expose] noncomputable def fixEquiv : G ≃* stdFix F n₀ :=
  (MonoidHom.ofInjective hρ).trans (MulEquiv.subgroupCongr hρr)

theorem coe_fixEquiv (g : G) : ((fixEquiv hρ hρr g : stdFix F n₀) : K) = ρ g :=
  rfl

include hκ in
theorem ε_suToSL_mem_stdFix (i : Fin D.rank) (A : Su Kf 2 f 2) :
    L.ε i (suToSL κ 2 A) ∈ stdFix F n₀ :=
  (L.ε_mem_stdFix_iff i _).2 (range_suToSL L.θ κ hκ 2 ▸ ⟨A, rfl⟩)

include hκ in
theorem ε₂_suToSL_mem_stdFix {i j : Fin D.rank} (hij : i < j)
    (h3 : coxeterMatrix D.isFiniteType i j = 3) (A : Su Kf 2 f 3) :
    L.ε₂ i j (suToSL κ 3 A) ∈ stdFix F n₀ :=
  (L.ε₂_mem_stdFix_iff hij h3 _).2 (range_suToSL L.θ κ hκ 3 ▸ ⟨A, rfl⟩)

@[expose] noncomputable def stdIota (i : Fin D.rank) : Su Kf 2 f 2 →* G :=
  (fixEquiv hρ hρr).symm.toMonoidHom.comp
    (((L.ε i).comp (suToSL κ 2)).codRestrict (stdFix F n₀) (ε_suToSL_mem_stdFix L κ hκ i))

open Classical in
@[expose] noncomputable def stdTheta (i j : Fin D.rank) : Su Kf 2 f 3 →* G :=
  if h : i < j ∧ coxeterMatrix D.isFiniteType i j = 3 then
    (fixEquiv hρ hρr).symm.toMonoidHom.comp
      (((L.ε₂ i j).comp (suToSL κ 3)).codRestrict (stdFix F n₀)
        (ε₂_suToSL_mem_stdFix L κ hκ h.1 h.2))
  else 1

theorem ρ_stdIota (i : Fin D.rank) (A : Su Kf 2 f 2) :
    ρ (stdIota L hρ hρr κ hκ i A) = L.ε i (suToSL κ 2 A) := by
  rw [stdIota, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.codRestrict_apply]
  rw [← coe_fixEquiv hρ hρr]
  exact congrArg Subtype.val (MulEquiv.apply_symm_apply (fixEquiv hρ hρr) _)

theorem ρ_stdTheta {i j : Fin D.rank} (hij : i < j) (h3 : coxeterMatrix D.isFiniteType i j = 3)
    (A : Su Kf 2 f 3) : ρ (stdTheta L hρ hρr κ hκ i j A) = L.ε₂ i j (suToSL κ 3 A) := by
  rw [stdTheta, dif_pos ⟨hij, h3⟩]
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.codRestrict_apply]
  rw [← coe_fixEquiv hρ hρr]
  exact congrArg Subtype.val (MulEquiv.apply_symm_apply (fixEquiv hρ hρr) _)

private theorem hmbFam_suToSL_embSUid_two (A : Su Kf 2 f 2) :
    suToSL (f := f) κ 3 (embSUid (unitaryInvolution Kf 2 f) 2 A) =
      WeakCT.blk L.Fld 0 (suToSL (f := f) κ 2 A) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_suToSL, coe_embSUid, WeakCT.blk, WeakCT.coe_blockSL_three_zero, embPair,
      Matrix.map_apply]

private theorem hmbFam_suToSL_embSUid_zero (A : Su Kf 2 f 2) :
    suToSL (f := f) κ 3 (embSUid (unitaryInvolution Kf 2 f) 0 A) =
      WeakCT.blk L.Fld 1 (suToSL (f := f) κ 2 A) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_suToSL, coe_embSUid, WeakCT.blk, WeakCT.coe_blockSL_three_one, embPair,
      Matrix.map_apply]

theorem stdTheta_left {i j : Fin D.rank} (hij : i < j) (h3 : coxeterMatrix D.isFiniteType i j = 3) :
    (stdTheta L hρ hρr κ hκ i j).comp (embSUid (unitaryInvolution Kf 2 f) 2) =
      stdIota L hρ hρr κ hκ i := by
  refine MonoidHom.ext fun A => hρ ?_
  rw [MonoidHom.comp_apply, ρ_stdTheta L hρ hρr κ hκ hij h3, ρ_stdIota L hρ hρr κ hκ,
    hmbFam_suToSL_embSUid_two L κ A]
  exact DFunLike.congr_fun (L.ε₂_left i j hij h3) (suToSL (f := f) κ 2 A)

theorem stdTheta_right {i j : Fin D.rank} (hij : i < j)
    (h3 : coxeterMatrix D.isFiniteType i j = 3) :
    (stdTheta L hρ hρr κ hκ i j).comp (embSUid (unitaryInvolution Kf 2 f) 0) =
      stdIota L hρ hρr κ hκ j := by
  refine MonoidHom.ext fun A => hρ ?_
  rw [MonoidHom.comp_apply, ρ_stdTheta L hρ hρr κ hκ hij h3, ρ_stdIota L hρ hρr κ hκ,
    hmbFam_suToSL_embSUid_zero L κ A]
  exact DFunLike.congr_fun (L.ε₂_right i j hij h3) (suToSL (f := f) κ 2 A)

private theorem hmbFam_root_apply_mul_apply_nonneg {ε : Fin D.rank → ℤ} (hε : ε ∈ D.roots)
    (i j : Fin D.rank) : 0 ≤ ε i * ε j := by
  rcases (RootSystem.ofCartan D.isFiniteType D.divisible).sign ε hε with h | h
  · exact mul_nonneg (h i) (h j)
  · nlinarith [h i, h j]

private theorem hmbFam_pair_apply_left {i j : Fin D.rank} (hij : i ≠ j) (z : ℤ × ℤ) :
    pair i j z i = z.1 := by
  simp [pair_apply, hij]

private theorem hmbFam_pair_apply_right {i j : Fin D.rank} (hij : i ≠ j) (z : ℤ × ℤ) :
    pair i j z j = z.2 := by
  simp [pair_apply, hij.symm]

private theorem hmbFam_pair_reflection_mem_roots {i j : Fin D.rank} {z : ℤ × ℤ}
    (hz : pair i j z ∈ D.roots) :
    pair i j (-z.1 - D.cartan i j * z.2, z.2) ∈ D.roots := by
  have := (RootSystem.ofCartan D.isFiniteType D.divisible).refl_mem i _ hz
  rwa [RootSystem.ofCartan_refl_apply,
    reflection_pair_left j (D.isFiniteType.apply_self i)] at this

private theorem hmbFam_nsmul_add_nsmul_eq_pair (i j : Fin D.rank) (σ τ : ℤ) (a b : ℕ) :
    a • (σ • (Pi.single i 1 : Fin D.rank → ℤ)) + b • (τ • (Pi.single j 1 : Fin D.rank → ℤ)) =
      pair i j ((a : ℤ) * σ, (b : ℤ) * τ) := by
  rw [pair_apply, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]

private theorem hmbFam_openCone_eq_empty_of_cartan_eq_zero {i j : Fin D.rank} (hij : i ≠ j)
    (hA : D.cartan i j = 0) {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    openCone D.roots (σ • Pi.single i 1) (τ • Pi.single j 1) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro ε ⟨hε, a, b, ha, hb, rfl⟩
  rw [hmbFam_nsmul_add_nsmul_eq_pair] at hε
  have h1 := hmbFam_root_apply_mul_apply_nonneg hε i j
  have h2 := hmbFam_root_apply_mul_apply_nonneg (hmbFam_pair_reflection_mem_roots hε) i j
  rw [hmbFam_pair_apply_left hij, hmbFam_pair_apply_right hij] at h1 h2
  simp only [hA, zero_mul, sub_zero] at h2
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> nlinarith

private theorem hmbFam_linIndepPair_single {i j : Fin D.rank} (hij : i ≠ j) {σ τ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    LinIndepPair (σ • (Pi.single i 1 : Fin D.rank → ℤ))
      (τ • (Pi.single j 1 : Fin D.rank → ℤ)) := by
  intro a b h
  have h1 := congrFun h i
  have h2 := congrFun h j
  simp [hij, hij.symm] at h1 h2
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> simp_all

private theorem hmbFam_commutes_rootGroup_of_cartan_eq_zero (hext : SteinbergExtras D n H)
    {i j : Fin D.rank} (hij : i ≠ j) (hA : D.cartan i j = 0) {σ τ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    ∀ x ∈ D.rootGroup (σ • Pi.single i 1), ∀ y ∈ D.rootGroup (τ • Pi.single j 1),
      x * y = y * x := by
  have hroot : ∀ (k : Fin D.rank) (s : ℤ), (s = 1 ∨ s = -1) →
      s • (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := by
    intro k s hs
    have h1 : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
      (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k
    rcases hs with rfl | rfl
    · simpa using h1
    · simpa using (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ h1
  intro x hx y hy
  have h := hext.commutator_mem _ (hroot i σ hσ) _ (hroot j τ hτ)
    (hmbFam_linIndepPair_single hij hσ hτ) x hx y hy
  rw [hmbFam_openCone_eq_empty_of_cartan_eq_zero hij hA hσ hτ] at h
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

private theorem hmbFam_commutes_sup_left {A A' B : Subgroup K}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (h' : ∀ x ∈ A', ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ A ⊔ A', ∀ y ∈ B, x * y = y * x := by
  have hA : A ≤ Subgroup.centralizer (B : Set K) := fun z hz => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (h z hz w hw).symm
  have hA' : A' ≤ Subgroup.centralizer (B : Set K) := fun z hz => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (h' z hz w hw).symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 ((sup_le hA hA') hx) y hy).symm

private theorem hmbFam_commutes_sup_right {A B B' : Subgroup K}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (h' : ∀ x ∈ A, ∀ y ∈ B', x * y = y * x) :
    ∀ x ∈ A, ∀ y ∈ B ⊔ B', x * y = y * x := by
  intro x hx
  have hB : B ≤ Subgroup.centralizer ({x} : Set K) := fun y hy => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact h x hx y hy
  have hB' : B' ≤ Subgroup.centralizer ({x} : Set K) := fun y hy => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact h' x hx y hy
  intro y hy
  exact Subgroup.mem_centralizer_iff.1 ((sup_le hB hB') hy) x (Set.mem_singleton x)

private theorem hmbFam_commutes_rankOne (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (hij : i ≠ j) (hA : D.cartan i j = 0) :
    ∀ x ∈ rankOne D.rootGroup i, ∀ y ∈ rankOne D.rootGroup j, x * y = y * x := by
  have hroot : ∀ σ τ : ℤ, (σ = 1 ∨ σ = -1) → (τ = 1 ∨ τ = -1) →
      ∀ x ∈ D.rootGroup (σ • Pi.single i 1), ∀ y ∈ D.rootGroup (τ • Pi.single j 1),
        x * y = y * x :=
    fun σ τ hσ hτ => hmbFam_commutes_rootGroup_of_cartan_eq_zero hext hij hA hσ hτ
  have h1 : ∀ σ : ℤ, (σ = 1 ∨ σ = -1) →
      ∀ x ∈ D.rootGroup (σ • Pi.single i 1), ∀ y ∈ rankOne D.rootGroup j, x * y = y * x :=
    fun σ hσ => hmbFam_commutes_sup_right (by simpa using hroot σ 1 hσ (Or.inl rfl))
      (by simpa using hroot σ (-1) hσ (Or.inr rfl))
  exact hmbFam_commutes_sup_left (by simpa using h1 1 (Or.inl rfl))
    (by simpa using h1 (-1) (Or.inr rfl))

private theorem hmbFam_mem_rankOne (i : Fin D.rank) (A : SL(2, L.Fld)) :
    L.ε i A ∈ rankOne D.rootGroup i := by
  have hcl : Subgroup.closure (Set.range (sl2Upper (k := L.Fld)) ∪ Set.range sl2Lower) ≤
      (rankOne D.rootGroup i).comap (L.ε i) := by
    rw [Subgroup.closure_le]
    rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact Subgroup.mem_sup_left (show L.ε i (sl2Upper c) ∈
        (D.rootGroup (Pi.single i 1) : Set K) by rw [← L.upper i]; exact ⟨c, rfl⟩)
    · exact Subgroup.mem_sup_right (show L.ε i (sl2Lower c) ∈
        (D.rootGroup (-Pi.single i 1) : Set K) by rw [← L.lower i]; exact ⟨c, rfl⟩)
  exact hcl (Sp.mem_closure_sl2 A)

theorem StdLevi.ε_commute (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (h2 : coxeterMatrix D.isFiniteType i j = 2) (A B : SL(2, L.Fld)) :
    Commute (L.ε i A) (L.ε j B) := by
  have hij : i ≠ j := by
    rintro rfl
    have h1 : coxeterMatrix D.isFiniteType i i = 1 := by
      unfold CFSG.LieType.RootSystem.coxeterMatrix
      rw [TauCeti.coxeterMatrixOfCartanMatrix_apply, D.isFiniteType.apply_self]
      norm_num [TauCeti.coxeterOrder_four]
    rw [h1] at h2
    omega
  have hsymm : ∀ i j : Fin D.rank, D.cartan i j = 0 → D.cartan j i = 0 :=
    fun i j h => (D.isFiniteType.apply_eq_zero_iff).1 h
  have hA : D.cartan i j = 0 :=
    (TauCeti.coxeterMatrixOfCartanMatrix_apply_eq_two_iff D.cartan D.isFiniteType.apply_self
      (fun _ _ h => D.isFiniteType.apply_mul_apply_mem_of_ne h) hsymm hij).1 h2
  exact (commute_iff_eq _ _).2
    (hmbFam_commutes_rankOne hext hij hA _ (hmbFam_mem_rankOne L i A) _
      (hmbFam_mem_rankOne L j B))

theorem stdIota_comm (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (h2 : coxeterMatrix D.isFiniteType i j = 2) (a b : Su Kf 2 f 2) :
    stdIota L hρ hρr κ hκ i a * stdIota L hρ hρr κ hκ j b =
      stdIota L hρ hρr κ hκ j b * stdIota L hρ hρr κ hκ i a := by
  refine hρ ?_
  rw [map_mul, map_mul, ρ_stdIota L hρ hρr κ hκ, ρ_stdIota L hρ hρr κ hκ]
  exact (L.ε_commute hext h2 (suToSL (f := f) κ 2 a) (suToSL (f := f) κ 2 b)).eq

@[expose] noncomputable def stdFamily (hext : SteinbergExtras D n H) :
    PhanFamilyE Kf 2 f (coxeterMatrix D.isFiniteType) G where
  ι := stdIota L hρ hρr κ hκ
  θ := stdTheta L hρ hρr κ hκ
  left _ _ hij h3 := stdTheta_left L hρ hρr κ hκ hij h3
  right _ _ hij h3 := stdTheta_right L hρ hρr κ hκ hij h3
  comm _ _ h2 a b := stdIota_comm L hρ hρr κ hκ hext h2 a b

theorem map_range_stdFamily_ι (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    ((stdFamily L hρ hρr κ hκ hext).ι i).range.map ρ = (slSU L.θ 2).map (L.ε i) := by
  have hcomp : ρ.comp (stdIota L hρ hρr κ hκ i) = (L.ε i).comp (suToSL (f := f) κ 2) :=
    MonoidHom.ext fun A => ρ_stdIota L hρ hρr κ hκ i A
  change Subgroup.map ρ ((stdIota L hρ hρr κ hκ i).range) = (slSU L.θ 2).map (L.ε i)
  rw [← MonoidHom.range_comp (g := ρ) (f := stdIota L hρ hρr κ hκ i), hcomp,
    MonoidHom.range_comp, range_suToSL L.θ κ hκ 2]

private theorem hmbFam_suToSL_torusTwo (u : normOne (unitaryInvolution Kf 2 f)) :
    suToSL (f := f) κ 2 (torusTwo (unitaryInvolution Kf 2 f) u) =
      WeakCT.torusHom L.Fld (Units.map κ.toMonoidHom (u : Kfˣ)) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_suToSL, coe_torusTwo, WeakCT.coe_torusHom, Matrix.map_apply]

include hκ in
private theorem hmbFam_theta_map_mul (u : normOne (unitaryInvolution Kf 2 f)) :
    L.θ (κ ((u : Kfˣ) : Kf)) * κ ((u : Kfˣ) : Kf) = 1 := by
  have hu : unitaryInvolution Kf 2 f ((u : Kfˣ) : Kf) * ((u : Kfˣ) : Kf) = 1 := u.2
  calc L.θ (κ ((u : Kfˣ) : Kf)) * κ ((u : Kfˣ) : Kf)
      = κ (unitaryInvolution Kf 2 f ((u : Kfˣ) : Kf)) * κ ((u : Kfˣ) : Kf) := by
        rw [← hκ]
    _ = κ (unitaryInvolution Kf 2 f ((u : Kfˣ) : Kf) * ((u : Kfˣ) : Kf)) := by
        rw [map_mul]
    _ = 1 := by rw [hu, map_one]

private theorem hmbFam_units_map_symm_apply (a : L.Fldˣ) :
    Units.map κ.toMonoidHom (Units.map κ.symm.toMonoidHom a) = a := by
  ext
  simp

private theorem hmbFam_kappa_units_map_symm (a : L.Fldˣ) :
    κ (κ.symm (a : L.Fld)) = (a : L.Fld) := by
  simp

theorem map_range_nodeTor_stdFamily (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    ((stdFamily L hρ hρr κ hκ hext).nodeTor i).range.map ρ = H i ⊓ stdFix F n₀ := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hy
    change ρ (stdIota L hρ hρr κ hκ i (torusTwo (unitaryInvolution Kf 2 f) u)) ∈
      H i ⊓ stdFix F n₀
    rw [ρ_stdIota L hρ hρr κ hκ, hmbFam_suToSL_torusTwo L κ u]
    exact Subgroup.mem_inf.2 ⟨L.ε_torusHom_mem i _,
      (ε_torusHom_mem_stdFix_iff (F := F) L i _).2
        (by simpa using hmbFam_theta_map_mul L κ hκ u)⟩
  · rintro x ⟨hxH, hxfix⟩
    have hxH' : x ∈ Set.range (fun s => L.ε i (WeakCT.torusHom L.Fld s)) := by
      rw [L.diag i]
      simpa using hxH
    obtain ⟨a, rfl⟩ := hxH'
    have hθa : L.θ (a : L.Fld) * (a : L.Fld) = 1 :=
      (ε_torusHom_mem_stdFix_iff (F := F) L i a).1 hxfix
    let u₀ : Kfˣ := Units.map κ.symm.toMonoidHom a
    have hu₀ : u₀ ∈ normOne (unitaryInvolution Kf 2 f) := by
      rw [mem_normOne]
      show unitaryInvolution Kf 2 f (κ.symm (a : L.Fld)) * κ.symm (a : L.Fld) = 1
      apply κ.injective
      rw [map_mul, map_one, hκ, hmbFam_kappa_units_map_symm L κ a, hθa]
    refine Subgroup.mem_map.2
      ⟨stdIota L hρ hρr κ hκ i (torusTwo (unitaryInvolution Kf 2 f) ⟨u₀, hu₀⟩),
        ⟨⟨u₀, hu₀⟩, rfl⟩, ?_⟩
    rw [ρ_stdIota L hρ hρr κ hκ, hmbFam_suToSL_torusTwo L κ ⟨u₀, hu₀⟩,
      hmbFam_units_map_symm_apply L κ a]

theorem map_torus_stdFamily (hext : SteinbergExtras D n H) :
    (stdFamily L hρ hρr κ hκ hext).torus.map ρ = ⨆ i, (H i ⊓ stdFix F n₀) := by
  change Subgroup.map ρ (⨆ i, ((stdFamily L hρ hρr κ hκ hext).nodeTor i).range) =
    ⨆ i, (H i ⊓ stdFix F n₀)
  rw [Subgroup.map_iSup]
  exact iSup_congr fun i => map_range_nodeTor_stdFamily L hρ hρr κ hκ hext i

end CFSG.ClassicalInvolution.Phan.PhanE
