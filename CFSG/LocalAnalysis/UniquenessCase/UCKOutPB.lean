module

public import CFSG.LocalAnalysis.UniquenessCase.UCKOutPA
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossTorus
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.OutP

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
  (diagGL permGL coe_diagGL coe_permGL det_diagGL det_permGL exists_elemAbelian_four_projDiag)

theorem exists_orderOf_eq_of_dvd {L : Type} [Field L] [Finite L] {d : ℕ}
    (hd : d ∣ Nat.card Lˣ) : ∃ ζ : Lˣ, orderOf ζ = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Lˣ)
  obtain ⟨k, hk⟩ := hd
  have hpos : 0 < Nat.card Lˣ := Nat.card_pos
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  refine ⟨g ^ k, ?_⟩
  rw [orderOf_pow_of_dvd hk0 (by rw [hg, hk]; exact dvd_mul_left k d), hg, hk,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]

theorem diagGL_commute {L : Type} [Field L] (u w : Fin 5 → Lˣ) :
    Commute (diagGL 5 u : GL (Fin 5) L) (diagGL 5 w) := by
  show diagGL 5 u * diagGL 5 w = diagGL 5 w * diagGL 5 u
  rw [← map_mul, ← map_mul, mul_comm]

theorem four_le_pRank_projFive {L : Type} [Field L] [Finite L] {ζ : Lˣ} (hζ : orderOf ζ = 25)
    (H : Subgroup (GL (Fin 5) L))
    (hH : ∀ u : Fin 5 → Lˣ, (∀ i, u i ∈ Subgroup.zpowers ζ) → ∏ i, u i = 1 → diagGL 5 u ∈ H) :
    4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (StatedProj H)) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hζ1 : ζ ^ 25 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hωo : orderOf (ζ ^ 5) = 5 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hζ]; norm_num), hζ]
  set Z : Subgroup Lˣ := Subgroup.zpowers (ζ ^ 5) with hZ
  have hZcard : Nat.card Z = 5 := by rw [hZ, Nat.card_zpowers, hωo]
  have hZpow : ∀ x : Z, x ^ 5 = 1 := fun x => by rw [← hZcard]; exact pow_card_eq_one'
  have hZζ : ∀ x : Z, (x : Lˣ) ∈ Subgroup.zpowers ζ := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
    rw [← hk, ← zpow_natCast, ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers ζ _
  set π : H →* StatedProj H := QuotientGroup.mk' ((StatedScalars (Fin 5) L).subgroupOf H)
    with hπ
  have hπ1 : ∀ g : H, π g = 1 → ∃ s : Lˣ, Matrix.GeneralLinearGroup.scalar (Fin 5) s = g := by
    intro g hg
    have h1 := (QuotientGroup.eq_one_iff g).1 hg
    exact Subgroup.mem_subgroupOf.1 h1
  set u₀ : Fin 5 → Lˣ := ![ζ, ζ, ζ, ζ, (ζ ^ 4)⁻¹] with hu₀
  have he₀ : diagGL 5 u₀ ∈ H := by
    refine hH u₀ (fun i => ?_) ?_
    · fin_cases i
      · exact Subgroup.mem_zpowers ζ
      · exact Subgroup.mem_zpowers ζ
      · exact Subgroup.mem_zpowers ζ
      · exact Subgroup.mem_zpowers ζ
      · exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers ζ 4)
    · rw [Fin.prod_univ_five]
      change ζ * ζ * ζ * ζ * (ζ ^ 4)⁻¹ = 1
      rw [show ζ * ζ * ζ * ζ = ζ ^ 4 by rw [pow_succ, pow_succ, pow_succ, pow_one], mul_inv_cancel]
  set e₀ : H := ⟨diagGL 5 u₀, he₀⟩ with he₀def
  set x₀ : StatedProj H := π e₀ with hx₀
  have hu₀5 : u₀ ^ 5 = fun _ => ζ ^ 5 := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · show ((ζ ^ 4)⁻¹) ^ 5 = ζ ^ 5
      rw [inv_pow, ← pow_mul, inv_eq_iff_mul_eq_one, ← pow_add]
      exact hζ1
  have hx₀5 : x₀ ^ 5 = 1 := by
    rw [hx₀, ← map_pow]
    apply (QuotientGroup.eq_one_iff _).2
    rw [Subgroup.mem_subgroupOf]
    refine ⟨ζ ^ 5, ?_⟩
    change Matrix.GeneralLinearGroup.scalar (Fin 5) (ζ ^ 5) = (diagGL 5 u₀) ^ 5
    rw [← map_pow, hu₀5, scalar_eq_diagGL]
  have hx₀1 : x₀ ≠ 1 := by
    intro h1
    obtain ⟨s, hs⟩ := hπ1 e₀ h1
    have a := eq_of_diagGL_eq_scalar hs.symm 0
    have b := eq_of_diagGL_eq_scalar hs.symm 4
    have : ζ ^ 5 = 1 := by
      have hab : ζ = (ζ ^ 4)⁻¹ := a.trans b.symm
      rw [eq_inv_iff_mul_eq_one, ← pow_succ'] at hab
      exact hab
    have h25 : 25 ∣ 5 := by rw [← hζ]; exact orderOf_dvd_of_pow_eq_one this
    norm_num at h25
  have hx₀o : orderOf x₀ = 5 := orderOf_eq_prime hx₀5 hx₀1
  let v : (Fin 3 → Z) →* (Fin 5 → Lˣ) :=
    MonoidHom.mk' (fun c => ![(c 0 : Lˣ), c 1, c 2, 1, ((c 0 : Lˣ) * c 1 * c 2)⁻¹])
      (fun c c' => by
        funext i
        fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc, mul_inv])
  have hv_mem : ∀ c, diagGL 5 (v c) ∈ H := by
    intro c
    refine hH _ (fun i => ?_) ?_
    · fin_cases i
      · exact hZζ (c 0)
      · exact hZζ (c 1)
      · exact hZζ (c 2)
      · exact Subgroup.one_mem _
      · exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hZζ _) (hZζ _))
          (hZζ _))
    · rw [Fin.prod_univ_five]
      change (c 0 : Lˣ) * c 1 * c 2 * 1 * ((c 0 : Lˣ) * c 1 * c 2)⁻¹ = 1
      rw [mul_one, mul_inv_cancel]
  let ψ : (Fin 3 → Z) →* H := ((diagGL 5).comp v).codRestrict H hv_mem
  let θ₁ : (Fin 3 → Z) →* StatedProj H := π.comp ψ
  have hcomm : ∀ (y : Subgroup.zpowers x₀) (c : Fin 3 → Z),
      Commute ((Subgroup.zpowers x₀).subtype y) (θ₁ c) := by
    intro y c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 y.2
    change Commute (y : StatedProj H) (π (ψ c))
    rw [← hk, hx₀, ← map_zpow]
    refine Commute.map ?_ π
    show e₀ ^ k * ψ c = ψ c * e₀ ^ k
    apply Subtype.ext
    change (diagGL 5 u₀) ^ k * diagGL 5 (v c) = diagGL 5 (v c) * (diagGL 5 u₀) ^ k
    rw [← map_zpow]
    exact diagGL_commute _ _
  let Φ : Subgroup.zpowers x₀ × (Fin 3 → Z) →* StatedProj H :=
    MonoidHom.noncommCoprod (Subgroup.zpowers x₀).subtype θ₁ hcomm
  have hΦ : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨y, c⟩ hyc
    rw [MonoidHom.mem_ker, MonoidHom.noncommCoprod_apply] at hyc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 y.2
    have h1 : π (e₀ ^ k * ψ c) = 1 := by
      rw [map_mul, map_zpow, ← hx₀]
      change x₀ ^ k * θ₁ c = 1
      rw [hk]
      exact hyc
    obtain ⟨s, hs⟩ := hπ1 _ h1
    have hs' : diagGL 5 (u₀ ^ k * v c) = Matrix.GeneralLinearGroup.scalar (Fin 5) s := by
      rw [hs, map_mul, map_zpow]
      rfl
    have ent := eq_of_diagGL_eq_scalar hs'
    have e0 := ent 0
    have e1 := ent 1
    have e2 := ent 2
    have e3 := ent 3
    have e4 := ent 4
    change ζ ^ k * (c 0 : Lˣ) = s at e0
    change ζ ^ k * (c 1 : Lˣ) = s at e1
    change ζ ^ k * (c 2 : Lˣ) = s at e2
    change ζ ^ k * 1 = s at e3
    change ((ζ ^ 4)⁻¹) ^ k * ((c 0 : Lˣ) * c 1 * c 2)⁻¹ = s at e4
    rw [mul_one] at e3
    have hc0 : (c 0 : Lˣ) = 1 := mul_left_cancel (e0.trans (e3.symm.trans (mul_one _).symm))
    have hc1 : (c 1 : Lˣ) = 1 := mul_left_cancel (e1.trans (e3.symm.trans (mul_one _).symm))
    have hc2 : (c 2 : Lˣ) = 1 := mul_left_cancel (e2.trans (e3.symm.trans (mul_one _).symm))
    rw [hc0, hc1, hc2, mul_one, mul_one, inv_one, mul_one, ← e3, inv_zpow', ← zpow_natCast,
      ← zpow_mul, zpow_eq_zpow_iff_modEq, hζ] at e4
    have h5k : (5 : ℤ) ∣ k := by
      unfold Int.ModEq at e4
      push_cast at e4
      omega
    obtain ⟨m, rfl⟩ := h5k
    have hy : y = 1 := by
      apply Subtype.ext
      rw [← hk, zpow_mul, zpow_ofNat, hx₀5, one_zpow]
      rfl
    have hc : c = 1 := by
      funext i
      apply Subtype.ext
      fin_cases i
      · exact hc0
      · exact hc1
      · exact hc2
    rw [Subgroup.mem_bot, hy, hc]
    rfl
  have hcard : Nat.card (Subgroup.zpowers x₀ × (Fin 3 → Z)) = 5 ^ 4 := by
    rw [Nat.card_prod, Nat.card_zpowers, hx₀o, Nat.card_fun, hZcard, Nat.card_fin]
    norm_num
  have hcommA : ∀ a b : Subgroup.zpowers x₀ × (Fin 3 → Z), a * b = b * a := by
    rintro ⟨y, c⟩ ⟨y', c'⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 y.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 y'.2
    refine Prod.ext (Subtype.ext ?_) (funext fun i => Subtype.ext (mul_comm _ _))
    change (y : StatedProj H) * y' = y' * y
    rw [← hk, ← hl]
    exact (Commute.zpow_zpow_self x₀ k l).eq
  have hpowA : ∀ a : Subgroup.zpowers x₀ × (Fin 3 → Z), a ^ 5 = 1 := by
    rintro ⟨y, c⟩
    refine Prod.ext ?_ (funext fun i => hZpow (c i))
    change y ^ 5 = 1
    have hy5 : Nat.card (Subgroup.zpowers x₀) = 5 := by rw [Nat.card_zpowers, hx₀o]
    have := pow_card_eq_one' (G := Subgroup.zpowers x₀) (x := y)
    rwa [hy5] at this
  exact CFSG.SectionRank.le_pRank_of_injective (by norm_num) hcommA hpowA hcard Φ hΦ le_top

theorem prod_pow_fin_five {G : Type} [CommGroup G] {κ : G} (hκ : κ ^ 5 = 1) :
    ∏ i : Fin 5, κ ^ (i : ℕ) = 1 := by
  rw [Fin.prod_univ_five]
  change κ ^ 0 * κ ^ 1 * κ ^ 2 * κ ^ 3 * κ ^ 4 = 1
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
  change κ ^ (5 * 2) = 1
  rw [pow_mul, hκ, one_pow]

theorem det_powDiag {F : Type} [Field F] {κ : Fˣ} (hκ : κ ^ 5 = 1) :
    ((powDiag κ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det = 1 := by
  rw [powDiag, det_diagGL, ← Units.coe_prod, prod_pow_fin_five hκ, Units.val_one]

theorem det_diagGL_zeta {F : Type} [Field F] (ζ : Fˣ) :
    ((diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1] : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det = 1 := by
  rw [det_diagGL]
  simp [Fin.prod_univ_five]

theorem det_permGL_finRotate {F : Type} [Field F] :
    ((permGL 5 (finRotate 5) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det = 1 := by
  rw [det_permGL, sign_finRotate]
  simp

theorem exists_toGL_eq {F : Type} [Field F] {g : GL (Fin 5) F}
    (h : (g : Matrix (Fin 5) (Fin 5) F).det = 1) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 5) F, Matrix.SpecialLinearGroup.toGL s = g :=
  ⟨⟨g, h⟩, Units.ext rfl⟩

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem kOutP_psl {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSL n ℓ f) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f - 1) (hrank : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 3) {T : Subgroup K}
    (hT : IsPGroup p T) (hTi : ¬ p ∣ T.index) (α : MulAut K) (hα : orderOf α = p)
    (hαT : ∀ t ∈ T, α t = t) : α ∈ (MulAut.conj : K →* MulAut K).range := by
  classical
  obtain ⟨⟨hℓ, hf, hn2, -, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  haveI : Fact p.Prime := ⟨hp⟩
  have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have hFu : Nat.card Fˣ = ℓ ^ f - 1 := by rw [Nat.card_units, hFcard]
  have hrank' : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n F))) ≤ 3 := by
    rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rw [hFu]; exact hpq)
  by_cases h6 : 6 ≤ n
  · exfalso
    have hH : ∀ u : Fin n → Fˣ, (∀ i, u i ∈ Subgroup.zpowers ζ) →
        (∀ i : Fin n, 5 ≤ i.val → u i = 1) → ∏ i, u i = 1 → diagGL n u ∈ StatedSL n F := by
      intro u _ _ hprod
      rw [CFSG.Open.StatedAPI.mem_statedSL_iff, det_diagGL, ← Units.coe_prod, hprod,
        Units.val_one]
    obtain ⟨E, hE, hEcard⟩ :=
      exists_elemAbelian_four_projDiag hp (by omega) (Or.inl h6) hζ (StatedSL n F) hH
    have := CFSG.SectionRank.le_pRank hp.one_lt le_top hE hEcard
    omega
  obtain rfl : n = 5 := by omega
  obtain rfl : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hpn
  by_cases h25 : 25 ∣ ℓ ^ f - 1
  · exfalso
    obtain ⟨ζ', hζ'⟩ := exists_orderOf_eq_of_dvd (L := F) (d := 25) (by rw [hFu]; exact h25)
    have := four_le_pRank_projFive hζ' (StatedSL 5 F) (fun u _ hprod => by
      rw [CFSG.Open.StatedAPI.mem_statedSL_iff, det_diagGL, ← Units.coe_prod, hprod,
        Units.val_one])
    omega
  have hf5 : ¬ 5 ∣ f := fun h =>
    h25 (by simpa using sq_dvd_pow_sub_one Nat.prime_five hℓ.one_lt.le h hpq)
  haveI : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = ℓ ^ f := by rw [← Nat.card_eq_fintype_card]; exact hFcard
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP F ℓ := charP_of_card_eq_prime_pow hFcard'
  let θ : K ≃* projectiveSL 5 F :=
    e.trans (CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.statedProjSLEquiv 5 F)
  set β := MulAut.congr θ α with hβdef
  have hβo : orderOf β = 5 := by
    rw [hβdef]
    exact (orderOf_injective (MulAut.congr θ).toMonoidHom (MulAut.congr θ).injective α).trans hα
  have hβp : β ^ 5 = 1 := by
    have := pow_orderOf_eq_one β
    rwa [hβo] at this
  have hβE : β ∈ semilinearAutGroup 5 F :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.mem_semilinearAutGroup_of_pow
      (by norm_num) (by decide) hβp
  have hβD : β ∈ linearAutGroup 5 F := by
    by_contra hD
    exact hf5 (CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      hℓ hf (by norm_num) hFcard Nat.prime_five β hβE hD hβo).1
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 hβD
  have hT' : IsPGroup 5 (T.map (θ : K →* projectiveSL 5 F)) := hT.map _
  have hTi' : ¬ 5 ∣ (T.map (θ : K →* projectiveSL 5 F)).index := by
    rwa [Subgroup.index_map_equiv]
  have hβT : ∀ t ∈ T.map (θ : K →* projectiveSL 5 F), β t = t := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hβdef, MulAut.congr_apply]
    change θ (α (θ.symm (θ t))) = θ t
    rw [MulEquiv.symm_apply_apply, hαT t ht]
  have hcore : β ∈ (MulAut.conj : projectiveSL 5 F →* MulAut (projectiveSL 5 F)).range := by
    refine mem_range_conj_of_fixes Matrix.SpecialLinearGroup.toGL
      Matrix.SpecialLinearGroup.toGL_injective (proj 5 F) (proj_surjective 5 F) ?_ hζ ?_
      (exists_toGL_eq (det_diagGL_zeta ζ)) (exists_toGL_eq det_permGL_finRotate) A
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 5 F A) ?_ β ?_ hT'
      hTi' hβT
    · intro s hs
      obtain ⟨c, -, hc⟩ := proj_eq_one_iff.1 hs
      refine ⟨c, Units.ext ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hc, Matrix.GeneralLinearGroup.coe_scalar]
    · exact fun κ hκ => exists_toGL_eq (det_powDiag hκ)
    · intro s
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_slConjugation, Units.val_mul,
        Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    · intro s
      rw [← hA]
      exact conjAut_proj A s
  exact (CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ α).1 hcore

section Unitary

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

theorem diagGL_mem_gramSU_one {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F)
    {n : ℕ} {u : Fin n → Fˣ} (hu : ∀ i, u i ^ (ℓ ^ f + 1) = 1) (hprod : ∏ i, u i = 1) :
    diagGL n u ∈ gramSU h (1 : Matrix (Fin n) (Fin n) F) := by
  refine ⟨?_, ?_⟩
  · rw [coe_diagGL, Matrix.mul_one, Matrix.diagonal_map (map_zero h.bar),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have := congrArg Units.val (hu i)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [h.bar_apply, ← pow_succ]
    exact this
  · rw [det_diagGL, ← Units.coe_prod, hprod, Units.val_one]

theorem permGL_mem_gramSU_one {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F)
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : Equiv.Perm.sign σ = 1) :
    permGL n σ ∈ gramSU h (1 : Matrix (Fin n) (Fin n) F) := by
  have hmap : ((permGL n σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map h.bar =
      ((permGL n σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [coe_permGL]
    ext i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply]
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [hmap, Matrix.mul_one, coe_permGL, Matrix.transpose_permMatrix, inv_inv,
      ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  · rw [det_permGL, hσ]
    simp

theorem dvd_card_units_of_dvd_add_one {F : Type} [Field F] {q d : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : 1 ≤ q) (hd : d ∣ q + 1) : d ∣ Nat.card Fˣ := by
  rw [Nat.card_units, hF]
  refine hd.trans ⟨q - 1, ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  apply Nat.sub_eq_of_eq_add
  simp only [Nat.add_sub_cancel]
  ring

theorem kOutP_psu {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSU n ℓ f) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f + 1) (hrank : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 3) {T : Subgroup K}
    (hT : IsPGroup p T) (hTi : ¬ p ∣ T.index) (α : MulAut K) (hα : orderOf α = p)
    (hαT : ∀ t ∈ T, α t = t) : α ∈ (MulAut.conj : K →* MulAut K).range := by
  classical
  obtain ⟨⟨hℓ, hf, hn3, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  haveI : Fact p.Prime := ⟨hp⟩
  have h : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hrank' : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU n (ℓ ^ f) F))) ≤ 3 := by
    rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  have hdiag : ∀ u : Fin n → Fˣ, (∀ i, orderOf (u i) ∣ ℓ ^ f + 1) → ∏ i, u i = 1 →
      diagGL n u ∈ StatedSU n (ℓ ^ f) F := by
    intro u hu hprod
    show diagGL n u ∈ unitarySU ℓ f F n
    rw [unitarySU_eq_gramSU h n]
    exact diagGL_mem_gramSU_one h (fun i => orderOf_dvd_iff_pow_eq_one.1 (hu i)) hprod
  obtain ⟨ζ, hζ⟩ :=
    exists_prime_orderOf_dvd_card' (G := Fˣ) p (dvd_card_units_of_dvd_add_one hFcard hq1 hpq)
  have hzq : ∀ x ∈ Subgroup.zpowers ζ, orderOf x ∣ ℓ ^ f + 1 := fun x hx =>
    (orderOf_dvd_of_mem_zpowers hx).trans (hζ ▸ hpq)
  by_cases h6 : 6 ≤ n
  · exfalso
    obtain ⟨E, hE, hEcard⟩ := exists_elemAbelian_four_projDiag hp (by omega) (Or.inl h6) hζ
      (StatedSU n (ℓ ^ f) F) (fun u hu _ hprod => hdiag u (fun i => hzq _ (hu i)) hprod)
    have := CFSG.SectionRank.le_pRank hp.one_lt le_top hE hEcard
    omega
  obtain rfl : n = 5 := by omega
  obtain rfl : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hpn
  by_cases h25 : 25 ∣ ℓ ^ f + 1
  · exfalso
    obtain ⟨ζ', hζ'⟩ :=
      exists_orderOf_eq_of_dvd (L := F) (d := 25) (dvd_card_units_of_dvd_add_one hFcard hq1 h25)
    have := four_le_pRank_projFive hζ' (StatedSU 5 (ℓ ^ f) F) (fun u hu hprod =>
      hdiag u (fun i => (orderOf_dvd_of_mem_zpowers (hu i)).trans (hζ' ▸ h25)) hprod)
    omega
  have hf5 : ¬ 5 ∣ f := fun h5f =>
    h25 (by simpa using sq_dvd_pow_add_one Nat.prime_five (by norm_num) h5f hpq)
  have hne' : ¬(5 = 3 ∧ ℓ ^ f = 2) := fun h => by omega
  have hC1 : IsPrimeFormGram (1 : GL (Fin 5) F) := isPrimeFormGram_one
  obtain ⟨θ⟩ : Nonempty (K ≃* primeFormP h ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) :=
    ⟨(e.trans (unitaryPSUEquiv h (by norm_num)).symm).trans
      (Classical.choice
        (unitary_prime_form_full_semilinear_realization h hC1 (by norm_num) hne').1).symm⟩
  set β := MulAut.congr θ α with hβdef
  have hβo : orderOf β = 5 := by
    rw [hβdef]
    exact (orderOf_injective (MulAut.congr θ).toMonoidHom (MulAut.congr θ).injective α).trans hα
  have hβp : β ^ 5 = 1 := by
    have := pow_orderOf_eq_one β
    rwa [hβo] at this
  set σ := primeFormFieldFactor h hC1 (by norm_num) hne' β with hσdef
  have hσ1 : σ = 1 := by
    by_contra hσ1
    have hσp : σ ^ 5 = 1 := by rw [hσdef, ← map_pow, hβp, map_one]
    have hσo : orderOf σ = 5 := orderOf_eq_prime hσp hσ1
    exact hf5 (CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h
      (by norm_num) hne' Nat.prime_five (by norm_num) β hβo σ hσdef.symm hσo).1
  have hD : β ∈ primeFormD h ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
    rw [← ker_primeFormFieldFactor h hC1 (by norm_num) hne']
    exact hσ1
  obtain ⟨A, hA⟩ := hD
  have hT' : IsPGroup 5
      (T.map (θ : K →* primeFormP h ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))) :=
    hT.map _
  have hTi' : ¬ 5 ∣
      (T.map (θ : K →* primeFormP h ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))).index := by
    rwa [Subgroup.index_map_equiv]
  have hβT : ∀ t ∈ T.map (θ : K →* primeFormP h ((1 : GL (Fin 5) F) :
      Matrix (Fin 5) (Fin 5) F)), β t = t := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hβdef, MulAut.congr_apply]
    change θ (α (θ.symm (θ t))) = θ t
    rw [MulEquiv.symm_apply_apply, hαT t ht]
  have hzq5 : ∀ x : Fˣ, x ^ 5 = 1 → x ^ (ℓ ^ f + 1) = 1 := fun x hx =>
    orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one hx).trans hpq)
  have hcore : β ∈ (MulAut.conj :
      primeFormP h ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) →* MulAut _).range := by
    refine mem_range_conj_of_fixes
      (gramSU h ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)).subtype
      (gramSU h ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)).subtype_injective
      (QuotientGroup.mk' (normOneScalars h
        (gramSU h ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) 5))
      (QuotientGroup.mk'_surjective _) ?_ hζ ?_ ?_ ?_ (A : GL (Fin 5) F)
      (fun s => ⟨A * s * (A : GL (Fin 5) F)⁻¹, conj_mem_gramSU h _ A.2 s.2⟩) (fun s => rfl) β ?_
      hT' hTi' hβT
    · intro s hs
      obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq_one_iff s).1 hs
      exact ⟨c, hc⟩
    · intro κ hκ
      refine ⟨⟨powDiag κ, diagGL_mem_gramSU_one h (fun i => ?_) (prod_pow_fin_five hκ)⟩, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hzq5 κ hκ, one_pow]
    · refine ⟨⟨diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1], diagGL_mem_gramSU_one h (fun i => ?_) ?_⟩, rfl⟩
      · have hζ5 : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
        fin_cases i
        · exact hzq5 ζ hζ5
        · exact hzq5 ζ⁻¹ (by rw [inv_pow, hζ5, inv_one])
        · exact one_pow _
        · exact one_pow _
        · exact one_pow _
      · rw [Fin.prod_univ_five]
        change ζ * ζ⁻¹ * 1 * 1 * 1 = 1
        rw [mul_inv_cancel, one_mul, one_mul, one_mul]
    · exact ⟨⟨permGL 5 (finRotate 5), permGL_mem_gramSU_one h _ (by rw [sign_finRotate]; decide)⟩,
        rfl⟩
    · intro s
      rw [← hA]
      exact primeFormConjHom_mk h _ A s
  exact (CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ α).1 hcore

end Unitary

end CFSG.LocalAnalysis.UniquenessCase.UCK.OutP
