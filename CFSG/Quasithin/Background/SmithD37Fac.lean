module

public import CFSG.Quasithin.Background.D2Transport
public import CFSG.Quasithin.Background.SmithD37Row
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.SmithD37

open scoped Matrix

section Step

variable {F : Type} [Field F] {d : ℕ}

structure FacStep (Y' Y : Submodule F (Fin d → F)) where
  y : Fin d → F
  y_mem : y ∈ Y
  φ : (Fin d → F) →ₗ[F] F
  φ_y : φ y = 1
  φ_eq_zero : ∀ z ∈ Y', φ z = 0
  sub_mem : ∀ z ∈ Y, z - φ z • y ∈ Y'

theorem exists_facStep {Y' Y : Submodule F (Fin d → F)} (h : Y' ≤ Y)
    (hr : Module.finrank F Y' + 1 = Module.finrank F Y) : Nonempty (FacStep Y' Y) := by
  have hne : Y' ≠ Y := by
    rintro rfl
    omega
  obtain ⟨y, hyY, hyY'⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne h hne)
  obtain ⟨f, hfy, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyY' inferInstance
  have hf0 : ∀ z ∈ Y', f z = 0 := by
    intro z hz
    have : f z ∈ Y'.map f := Submodule.mem_map_of_mem hz
    rw [hf] at this
    exact (Submodule.mem_bot F).mp this
  have hsup : Y' ⊔ Submodule.span F {y} = Y := by
    refine Submodule.eq_of_le_of_finrank_le
      (sup_le h ((Submodule.span_singleton_le_iff_mem _ _).mpr hyY)) ?_
    have hlt : Y' < Y' ⊔ Submodule.span F {y} :=
      lt_of_le_of_ne le_sup_left fun he =>
        hyY' (he ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self y))
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  refine ⟨⟨y, hyY, (f y)⁻¹ • f, ?_, ?_, ?_⟩⟩
  · simp [inv_mul_cancel₀ hfy]
  · intro z hz
    simp [hf0 z hz]
  · intro z hz
    rw [← hsup] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have : ((f y)⁻¹ • f) (a + c • y) = c := by
      simp only [LinearMap.smul_apply, map_add, map_smul, hf0 a ha, smul_eq_mul, mul_zero,
        zero_add]
      field_simp
    rw [this, add_sub_cancel_right]
    exact ha

theorem exists_linearMap_eq_one {y : Fin d → F} (hy : y ≠ 0) :
    ∃ φ : (Fin d → F) →ₗ[F] F, φ y = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
  exact ⟨(y i)⁻¹ • LinearMap.proj i, by simp [inv_mul_cancel₀ hi]⟩

@[expose] noncomputable def facStepLine {y : Fin d → F} (hy : y ≠ 0) :
    FacStep (⊥ : Submodule F (Fin d → F)) (Submodule.span F {y}) where
  y := y
  y_mem := Submodule.mem_span_singleton_self y
  φ := (exists_linearMap_eq_one hy).choose
  φ_y := (exists_linearMap_eq_one hy).choose_spec
  φ_eq_zero z hz := by
    rw [(Submodule.mem_bot F).mp hz, map_zero]
  sub_mem z hz := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_smul, (exists_linearMap_eq_one hy).choose_spec, smul_eq_mul, mul_one, sub_self]
    exact Submodule.zero_mem _

@[simp]
theorem facStepLine_y {y : Fin d → F} (hy : y ≠ 0) : (facStepLine hy).y = y :=
  rfl

end Step

section Transport

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem fixV_map_congr (ψ : V ≃* W) (X : Subgroup (MulAut V)) :
    fixV (X.map (MulAut.congr ψ).toMonoidHom) = (fixV X).map ψ.toMonoidHom :=
  fixV_map_congr_equiv ψ X

theorem card_map_congr (ψ : V ≃* W) (X : Subgroup (MulAut V)) :
    Nat.card (X.map (MulAut.congr ψ).toMonoidHom) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.congr ψ).injective

theorem commSub_map_congr (ψ : V ≃* W) (X : Subgroup (MulAut V)) (S : Subgroup V) :
    commSub (S.map ψ.toMonoidHom) (X.map (MulAut.congr ψ).toMonoidHom) =
      (commSub S X).map ψ.toMonoidHom :=
  CFSG.Quasithin.commSub_map_mulAutCongr ψ S X

theorem commSeries_map_congr (ψ : V ≃* W) (X : Subgroup (MulAut V)) (k : ℕ) :
    commSeries (X.map (MulAut.congr ψ).toMonoidHom) k = (commSeries X k).map ψ.toMonoidHom :=
  CFSG.Quasithin.commSeries_map_mulAutCongr ψ X k

end Transport

section Fac

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)} {F : Type} [Field F] {d : ℕ}
  (Mm : MatModel L₁ L₂ F d) {Y' Y : Submodule F (Fin d → F)}

private theorem mat_add_row (A B : Matrix (Fin d) (Fin d) F) (i : Fin d) :
    (A + B) i = A i + B i :=
  rfl

private theorem mat_neg_row (A : Matrix (Fin d) (Fin d) F) (i : Fin d) : (-A) i = -A i :=
  rfl

private theorem mat_zero_row (i : Fin d) : (0 : Matrix (Fin d) (Fin d) F) i = 0 :=
  rfl

private theorem vecMulVec_row (x y : Fin d → F) (i : Fin d) :
    Matrix.vecMulVec x y i = x i • y := by
  ext j
  simp [Matrix.vecMulVec_apply]

theorem rank1_zero_left (y : Fin d → F) : rank1 Mm 0 y = (1 : U) := by
  rw [rank1, Matrix.zero_vecMulVec, ofAdd_zero, map_one]

theorem le_stabSub_rowSub_bot (P : Subgroup (MulAut U)) : P ≤ stabSub (rowSub Mm ⊥) := by
  intro a _ u
  rw [rowSub_bot, Subgroup.mem_bot, Subgroup.mem_bot, a.map_eq_one_iff]

@[expose] noncomputable def facProj (D : FacStep Y' Y) : U →* natMod F d where
  toFun u := Multiplicative.ofAdd fun i => D.φ (Multiplicative.toAdd (Mm.β u) i)
  map_one' := by
    simp only [map_one, toAdd_one]
    exact congrArg Multiplicative.ofAdd (funext fun i => by rw [mat_zero_row, map_zero]; rfl)
  map_mul' u v := by
    simp only [map_mul, toAdd_mul]
    exact congrArg Multiplicative.ofAdd (funext fun i => by rw [mat_add_row, map_add]; rfl)

theorem facProj_apply (D : FacStep Y' Y) (u : U) :
    facProj Mm D u = Multiplicative.ofAdd fun i => D.φ (Multiplicative.toAdd (Mm.β u) i) :=
  rfl

theorem facProj_rank1 (D : FacStep Y' Y) (x : Fin d → F) :
    facProj Mm D (rank1 Mm x D.y) = Multiplicative.ofAdd x := by
  rw [facProj_apply, β_rank1, toAdd_ofAdd]
  congr 1
  funext i
  rw [vecMulVec_row, map_smul, D.φ_y, smul_eq_mul, mul_one]

theorem facProj_eq_one (D : FacStep Y' Y) {u : U} (hu : u ∈ rowSub Mm Y') :
    facProj Mm D u = 1 := by
  rw [facProj_apply]
  have : (fun i => D.φ (Multiplicative.toAdd (Mm.β u) i)) = 0 :=
    funext fun i => D.φ_eq_zero _ (hu i)
  rw [this]
  rfl

theorem mul_inv_rank1_mem (D : FacStep Y' Y) {u : U} (hu : u ∈ rowSub Mm Y) :
    u * (rank1 Mm (Multiplicative.toAdd (facProj Mm D u)) D.y)⁻¹ ∈ rowSub Mm Y' := by
  intro i
  rw [map_mul, map_inv, β_rank1, toAdd_mul, toAdd_inv, toAdd_ofAdd, mat_add_row, mat_neg_row,
    vecMulVec_row, facProj_apply, toAdd_ofAdd, ← sub_eq_add_neg]
  exact D.sub_mem _ (hu i)

theorem mem_rowSub_of_facProj_eq_one (D : FacStep Y' Y) {u : U} (hu : u ∈ rowSub Mm Y)
    (h : facProj Mm D u = 1) : u ∈ rowSub Mm Y' := by
  have := mul_inv_rank1_mem Mm D hu
  rwa [h, toAdd_one, rank1_zero_left, inv_one, mul_one] at this

@[expose] noncomputable def rank1Hom (y : Fin d → F) : natMod F d →* U where
  toFun x := rank1 Mm (Multiplicative.toAdd x) y
  map_one' := by rw [toAdd_one, rank1_zero_left]
  map_mul' x x' := by
    rw [toAdd_mul, rank1, rank1, rank1, Matrix.add_vecMulVec, ofAdd_add, map_mul]

theorem facProj_apply_eq (D : FacStep Y' Y) {a : MulAut U} (ha : a ∈ stabSub (rowSub Mm Y'))
    {u v : U} (h : u * v⁻¹ ∈ rowSub Mm Y') : facProj Mm D (a u) = facProj Mm D (a v) := by
  have h1 : a u = a (u * v⁻¹) * a v := by rw [← map_mul, inv_mul_cancel_right]
  rw [h1, map_mul, facProj_eq_one Mm D ((ha _).2 h), one_mul]

theorem facProj_rank1_facProj (D : FacStep Y' Y) {a : MulAut U}
    (ha : a ∈ stabSub (rowSub Mm Y')) {u : U} (hu : u ∈ rowSub Mm Y) :
    facProj Mm D (a (rank1 Mm (Multiplicative.toAdd (facProj Mm D u)) D.y)) =
      facProj Mm D (a u) := by
  refine facProj_apply_eq Mm D ha ?_
  have := (rowSub Mm Y').inv_mem (mul_inv_rank1_mem Mm D hu)
  rwa [mul_inv_rev, inv_inv] at this

@[expose] noncomputable def facFun (D : FacStep Y' Y) (a : MulAut U) :
    natMod F d →* natMod F d :=
  (facProj Mm D).comp (a.toMonoidHom.comp (rank1Hom Mm D.y))

theorem facFun_apply (D : FacStep Y' Y) (a : MulAut U) (x : natMod F d) :
    facFun Mm D a x = facProj Mm D (a (rank1 Mm (Multiplicative.toAdd x) D.y)) :=
  rfl

theorem facFun_one (D : FacStep Y' Y) : facFun Mm D 1 = MonoidHom.id _ := by
  refine MonoidHom.ext fun x => ?_
  rw [facFun_apply, MulAut.one_apply, facProj_rank1, ofAdd_toAdd, MonoidHom.id_apply]

theorem facFun_mul (D : FacStep Y' Y) {a b : MulAut U} (ha : a ∈ stabSub (rowSub Mm Y'))
    (hb : b ∈ stabSub (rowSub Mm Y)) :
    facFun Mm D (a * b) = (facFun Mm D a).comp (facFun Mm D b) := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.comp_apply, facFun_apply, facFun_apply, facFun_apply,
    facProj_rank1_facProj Mm D ha ((hb _).2 (rank1_mem_rowSub Mm _ D.y_mem)), MulAut.mul_apply]

@[expose] noncomputable def facAct (D : FacStep Y' Y) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm Y)) (hP' : P ≤ stabSub (rowSub Mm Y')) :
    ↥P →* MulAut (natMod F d) where
  toFun a := MonoidHom.toMulEquiv (facFun Mm D a) (facFun Mm D (a : MulAut U)⁻¹)
    (by rw [← facFun_mul Mm D (hP' (P.inv_mem a.2)) (hP a.2), inv_mul_cancel, facFun_one])
    (by rw [← facFun_mul Mm D (hP' a.2) (hP (P.inv_mem a.2)), mul_inv_cancel, facFun_one])
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    exact congrArg (fun f : natMod F d →* natMod F d => f x) (facFun_one Mm D)
  map_mul' a b := by
    refine MulEquiv.ext fun x => ?_
    exact congrArg (fun f : natMod F d →* natMod F d => f x) (facFun_mul Mm D (hP' a.2) (hP b.2))

theorem facAct_eq_facProj (D : FacStep Y' Y) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm Y)) (hP' : P ≤ stabSub (rowSub Mm Y')) (a : ↥P)
    (x : natMod F d) :
    facAct Mm D hP hP' a x =
      facProj Mm D ((a : MulAut U) (rank1 Mm (Multiplicative.toAdd x) D.y)) :=
  rfl

theorem card_le_mul_of_map_le {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (f : G →* G') {H H' : Subgroup G} {K : Subgroup G'} (hK : H.map f ≤ K)
    (hH : f.ker ⊓ H ≤ H') : Nat.card H ≤ Nat.card H' * Nat.card K := by
  rw [← Subgroup.relIndex_mul_card f.ker H, Subgroup.relIndex_ker, mul_comm]
  exact Nat.mul_le_mul (Subgroup.card_le_of_le hH) (Subgroup.card_le_of_le hK)

theorem card_fixV_le_facAct [Finite U] [Finite F] (D : FacStep Y' Y) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm Y)) (hP' : P ≤ stabSub (rowSub Mm Y')) :
    Nat.card ↥(rowSub Mm Y ⊓ fixV P) ≤
      Nat.card ↥(rowSub Mm Y' ⊓ fixV P) * Nat.card ↥(fixV (facAct Mm D hP hP').range) := by
  refine card_le_mul_of_map_le (facProj Mm D) ?_ ?_
  · rintro _ ⟨u, ⟨huY, huP⟩, rfl⟩
    refine mem_fixV.mpr ?_
    rintro _ ⟨a, rfl⟩
    rw [facAct_eq_facProj, facProj_rank1_facProj Mm D (hP' a.2) huY, huP a a.2]
  · rintro u ⟨hu1, huY, huP⟩
    exact ⟨mem_rowSub_of_facProj_eq_one Mm D huY (MonoidHom.mem_ker.mp hu1), huP⟩

theorem rank1_mulVec (l : ↥L₁) (x y : Fin d → F) :
    rank1 Mm (((Mm.R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ x)
      y = (l : MulAut U) (rank1 Mm x y) := by
  apply Mm.β.injective
  rw [Mm.act₁, β_rank1, β_rank1, toAdd_ofAdd, Matrix.mul_vecMulVec]

theorem facProj_act (D : FacStep Y' Y) (l : ↥L₁) (u : U) :
    facProj Mm D ((l : MulAut U) u) = natAut Mm l (facProj Mm D u) := by
  rw [natAut_apply, facProj_apply, facProj_apply, Mm.act₁, toAdd_ofAdd, toAdd_ofAdd]
  congr 1
  funext i
  set R := ((Mm.R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)
  set B := Multiplicative.toAdd (Mm.β u)
  have : (R * B) i = ∑ j, R i j • B j := by
    ext k
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [this, map_sum]
  simp [Matrix.mulVec, dotProduct, map_smul]

theorem facAct_conj (D : FacStep Y' Y) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm Y)) (hP' : P ≤ stabSub (rowSub Mm Y')) (a : ↥P) (l : ↥L₁)
    (h : (a : MulAut U) * l * (a : MulAut U)⁻¹ ∈ L₁) :
    facAct Mm D hP hP' a * natAut Mm l * (facAct Mm D hP hP' a)⁻¹ = natAut Mm ⟨_, h⟩ := by
  rw [mul_inv_eq_iff_eq_mul]
  refine MulEquiv.ext fun x => ?_
  set w := rank1 Mm (Multiplicative.toAdd x) D.y
  have key : ((a : MulAut U) * l * (a : MulAut U)⁻¹) ((a : MulAut U) w) =
      (a : MulAut U) ((l : MulAut U) w) := by
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
  rw [MulAut.mul_apply, MulAut.mul_apply, facAct_eq_facProj, facAct_eq_facProj,
    natAut_apply Mm l x, toAdd_ofAdd, rank1_mulVec, ← key]
  exact facProj_act Mm D ⟨_, h⟩ _

theorem conj_mem_natSub_of_mem_range (D : FacStep Y' Y) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm Y)) (hP' : P ≤ stabSub (rowSub Mm Y'))
    (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁) :
    ∀ b ∈ (facAct Mm D hP hP').range, ∀ g ∈ natSub Mm, b * g * b⁻¹ ∈ natSub Mm := by
  rintro _ ⟨a, rfl⟩ _ ⟨l, rfl⟩
  exact ⟨⟨_, hPN _ a.2 _ l.2⟩, (facAct_conj Mm D hP hP' a l _).symm⟩

theorem range_facAct_le_normalizer (D : FacStep Y' Y) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm Y)) (hP' : P ≤ stabSub (rowSub Mm Y'))
    (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁) :
    (facAct Mm D hP hP').range ≤
      Subgroup.normalizer (natSub Mm : Set (MulAut (natMod F d))) := by
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_natSub_of_mem_range Mm D hP hP' hPN _ ⟨a, rfl⟩ g, ?_⟩
  rintro ⟨l, hl⟩
  have h := hPN _ (P.inv_mem a.2) _ l.2
  refine ⟨⟨_, h⟩, (facAct_conj Mm D hP hP' a⁻¹ l h).symm.trans ?_⟩
  rw [map_inv, hl]
  group

private theorem fac_glAut_injective :
    Function.Injective (glAut : Matrix.GeneralLinearGroup (Fin d) F →* MulAut (natMod F d)) := by
  intro g h hgh
  refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun v => ?_))
  have := congrArg
    (fun f : MulAut (natMod F d) => Multiplicative.toAdd (f (Multiplicative.ofAdd v))) hgh
  simpa [glAut_apply, Matrix.toLin'_apply] using this

private theorem fac_natAut_injective : Function.Injective (natAut Mm) :=
  fac_glAut_injective.comp Mm.inj₁

theorem facAct_eq_one_of_commute [CharP F 2] (D : FacStep Y' Y) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm Y)) (hP' : P ≤ stabSub (rowSub Mm Y')) (h2 : IsPGroup 2 ↥P)
    (a : ↥P) (hc : ∀ l ∈ L₁, (a : MulAut U) * l = l * a) : facAct Mm D hP hP' a = 1 := by
  set f := facAct Mm D hP hP' a with hf
  have hcomm : ∀ (l : ↥L₁) (x : natMod F d), f (natAut Mm l x) = natAut Mm l (f x) := by
    intro l x
    have h : (a : MulAut U) * l * (a : MulAut U)⁻¹ ∈ L₁ := by
      rw [hc l l.2, mul_inv_cancel_right]
      exact l.2
    have hl : (⟨_, h⟩ : ↥L₁) = l := by
      refine Subtype.ext ?_
      change (a : MulAut U) * l * (a : MulAut U)⁻¹ = l
      rw [hc l l.2, mul_inv_cancel_right]
    have := facAct_conj Mm D hP hP' a l h
    rw [hl, mul_inv_eq_iff_eq_mul] at this
    exact congrArg (fun g : MulAut (natMod F d) => g x) this
  let ψ : (Fin d → F) →+ (Fin d → F) :=
    { toFun := fun v => Multiplicative.toAdd (f (Multiplicative.ofAdd v))
      map_zero' := by simp
      map_add' := fun v w => by simp [ofAdd_add, map_mul] }
  obtain ⟨c, hc'⟩ := Mm.end₁ ψ fun l v => by
    have := congrArg Multiplicative.toAdd (hcomm l (Multiplicative.ofAdd v))
    rw [natAut_apply, natAut_apply, toAdd_ofAdd, toAdd_ofAdd] at this
    exact this
  have hψ : ∀ v, f (Multiplicative.ofAdd v) = Multiplicative.ofAdd (c • v) := fun v => by
    rw [← hc' v]
    rfl
  have hpow : ∀ (m : ℕ) (v : Fin d → F),
      (f ^ m) (Multiplicative.ofAdd v) = Multiplicative.ofAdd (c ^ m • v) := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih => intro v; rw [pow_succ, MulAut.mul_apply, hψ, ih, pow_succ, mul_smul]
  obtain ⟨n, hn⟩ := h2 a
  have h1 : f ^ 2 ^ n = 1 := by rw [hf, ← map_pow, hn, map_one]
  refine MulEquiv.ext fun x => ?_
  have hx : Multiplicative.toAdd x = c ^ 2 ^ n • Multiplicative.toAdd x := by
    have := congrArg Multiplicative.toAdd (hpow (2 ^ n) (Multiplicative.toAdd x))
    rwa [h1, MulAut.one_apply, ofAdd_toAdd, toAdd_ofAdd] at this
  rw [MulAut.one_apply, ← ofAdd_toAdd x, hψ, Multiplicative.ofAdd.apply_eq_iff_eq]
  have h3 : (c - 1) ^ 2 ^ n • Multiplicative.toAdd x = 0 := by
    rw [sub_pow_char_pow, one_pow, sub_smul, one_smul, ← hx, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · rw [sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero n two_ne_zero)).mp h4), one_smul]
  · rw [h4, smul_zero]

theorem facAct_eq_one_iff [CharP F 2] (D : FacStep Y' Y) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm Y)) (hP' : P ≤ stabSub (rowSub Mm Y'))
    (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁) (h2 : IsPGroup 2 ↥P) (a : ↥P) :
    facAct Mm D hP hP' a = 1 ↔ ∀ l ∈ L₁, (a : MulAut U) * l = l * a := by
  refine ⟨fun h1 l hl => ?_, facAct_eq_one_of_commute Mm D hP hP' h2 a⟩
  have h := hPN _ a.2 l hl
  have := facAct_conj Mm D hP hP' a ⟨l, hl⟩ h
  rw [h1, one_mul, inv_one, mul_one] at this
  have he := congrArg Subtype.val (fac_natAut_injective Mm this)
  simp only at he
  calc (a : MulAut U) * l = (a : MulAut U) * l * (a : MulAut U)⁻¹ * a := by group
    _ = l * a := by rw [← he]

theorem card_range_facAct_mul [CharP F 2] (D : FacStep Y' Y) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm Y)) (hP' : P ≤ stabSub (rowSub Mm Y'))
    (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁) (h2 : IsPGroup 2 ↥P) :
    Nat.card (facAct Mm D hP hP').range * Nat.card ↥(P ⊓ Subgroup.centralizer L₁) =
      Nat.card P := by
  have hker : (facAct Mm D hP hP').ker = (P ⊓ Subgroup.centralizer L₁).subgroupOf P := by
    ext a
    rw [MonoidHom.mem_ker, facAct_eq_one_iff Mm D hP hP' hPN h2, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact ⟨fun h => ⟨a.2, fun l hl => (h l hl).symm⟩, fun h l hl => (h.2 l hl).symm⟩
  have h1 := Subgroup.card_mul_index (facAct Mm D hP hP').ker
  rw [Subgroup.index_ker, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  rw [mul_comm]
  exact h1

theorem isPGroup_range_facAct (D : FacStep Y' Y) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm Y)) (hP' : P ≤ stabSub (rowSub Mm Y')) (h2 : IsPGroup 2 ↥P) :
    IsPGroup 2 ↥(facAct Mm D hP hP').range :=
  h2.of_surjective _ (facAct Mm D hP hP').rangeRestrict_surjective

theorem isElemAbelian2_range_facAct (D : FacStep Y' Y) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm Y)) (hP' : P ≤ stabSub (rowSub Mm Y'))
    (hE : IsElemAbelian2 P) : IsElemAbelian2 (facAct Mm D hP hP').range := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hE.1 _ a.2 _ b.2))
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (hE.2 _ a.2)
    rw [this, map_one]

@[expose] noncomputable def lineEquiv {y : Fin d → F} (hy : y ≠ 0) :
    natMod F d ≃* ↥(rowSub Mm (Submodule.span F {y})) where
  toFun x := ⟨rank1 Mm (Multiplicative.toAdd x) y,
    rank1_mem_rowSub Mm _ (Submodule.mem_span_singleton_self y)⟩
  invFun u := facProj Mm (facStepLine hy) u
  left_inv x := (facProj_rank1 Mm (facStepLine hy) _).trans (ofAdd_toAdd x)
  right_inv u := by
    have h := mul_inv_rank1_mem Mm (facStepLine hy) u.2
    rw [rowSub_bot, Subgroup.mem_bot, mul_inv_eq_one] at h
    exact Subtype.ext h.symm
  map_mul' x x' := Subtype.ext (map_mul (rank1Hom Mm y) x x')

theorem facAct_line {y : Fin d → F} (hy : y ≠ 0) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm (Submodule.span F {y})))
    (hP' : P ≤ stabSub (rowSub Mm ⊥)) (a : ↥P) :
    facAct Mm (facStepLine hy) hP hP' a =
      MulAut.congr (lineEquiv Mm hy).symm (resHom _ ⟨a, hP a.2⟩) :=
  MulEquiv.ext fun _ => rfl

theorem range_facAct_line {y : Fin d → F} (hy : y ≠ 0) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm (Submodule.span F {y})))
    (hP' : P ≤ stabSub (rowSub Mm ⊥)) :
    (facAct Mm (facStepLine hy) hP hP').range =
      (autSub P (rowSub Mm (Submodule.span F {y}))).map
        (MulAut.congr (lineEquiv Mm hy).symm).toMonoidHom := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨resHom _ ⟨a, hP a.2⟩, mem_autSub.mpr ⟨⟨a, hP a.2⟩, a.2, rfl⟩,
      (facAct_line Mm hy hP hP' a).symm⟩
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨b, hb, rfl⟩ := mem_autSub.mp hφ
    exact ⟨⟨b, hb⟩, facAct_line Mm hy hP hP' ⟨b, hb⟩⟩

theorem card_fixV_range_facAct_line {y : Fin d → F} (hy : y ≠ 0) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm (Submodule.span F {y})))
    (hP' : P ≤ stabSub (rowSub Mm ⊥)) :
    Nat.card ↥(fixV (facAct Mm (facStepLine hy) hP hP').range) =
      Nat.card ↥(fixV (autSub P (rowSub Mm (Submodule.span F {y})))) := by
  rw [range_facAct_line, fixV_map_congr,
    Subgroup.card_map_of_injective (lineEquiv Mm hy).symm.injective]

theorem card_range_facAct_line {y : Fin d → F} (hy : y ≠ 0) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm (Submodule.span F {y})))
    (hP' : P ≤ stabSub (rowSub Mm ⊥)) :
    Nat.card (facAct Mm (facStepLine hy) hP hP').range =
      Nat.card (autSub P (rowSub Mm (Submodule.span F {y}))) := by
  rw [range_facAct_line, card_map_congr]

theorem commSeries_range_facAct_line {y : Fin d → F} (hy : y ≠ 0) {P : Subgroup (MulAut U)}
    (hP : P ≤ stabSub (rowSub Mm (Submodule.span F {y})))
    (hP' : P ≤ stabSub (rowSub Mm ⊥)) {k : ℕ}
    (hk : commSeries (autSub P (rowSub Mm (Submodule.span F {y}))) k = ⊥) :
    commSeries (facAct Mm (facStepLine hy) hP hP').range k = ⊥ := by
  rw [range_facAct_line, commSeries_map_congr, hk, Subgroup.map_bot]

end Fac

end CFSG.Quasithin.SmithD37
