module

public import CFSG.Quasithin.Background.HTransport
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin

namespace H

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

abbrev StdMod (ι K : Type) := Multiplicative (ι → K)

abbrev toAddMap (g : MulAut (StdMod ι K)) (v : ι → K) : ι → K :=
  Multiplicative.toAdd (g (Multiplicative.ofAdd v))

omit [Fintype ι] [DecidableEq ι] in
theorem toAddMap_add (g : MulAut (StdMod ι K)) (v w : ι → K) :
    toAddMap g (v + w) = toAddMap g v + toAddMap g w := by
  unfold toAddMap
  rw [ofAdd_add, map_mul, toAdd_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem toAddMap_mul (g h : MulAut (StdMod ι K)) (v : ι → K) :
    toAddMap (g * h) v = toAddMap g (toAddMap h v) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem toAddMap_one (v : ι → K) : toAddMap (1 : MulAut (StdMod ι K)) v = v := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem toAddMap_inv_apply (g : MulAut (StdMod ι K)) (v : ι → K) :
    toAddMap g (toAddMap g⁻¹ v) = v := by
  unfold toAddMap
  rw [ofAdd_toAdd, ← MulAut.mul_apply, mul_inv_cancel]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem toAddMap_apply_inv (g : MulAut (StdMod ι K)) (v : ι → K) :
    toAddMap g⁻¹ (toAddMap g v) = v := by
  unfold toAddMap
  rw [ofAdd_toAdd, ← MulAut.mul_apply, inv_mul_cancel]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem toAddMap_injective {g h : MulAut (StdMod ι K)} (hgh : ∀ v, toAddMap g v = toAddMap h v) :
    g = h :=
  MulEquiv.ext fun x => congrArg Multiplicative.ofAdd (hgh (Multiplicative.toAdd x))

@[expose] def matAut (g : GL ι K) : MulAut (StdMod ι K) where
  toFun x := Multiplicative.ofAdd ((g : Matrix ι ι K) *ᵥ Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd x)
  left_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, ofAdd_toAdd]
  right_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' x y := by
    simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

theorem toAddMap_matAut (g : GL ι K) (v : ι → K) :
    toAddMap (matAut g) v = (g : Matrix ι ι K) *ᵥ v := rfl

@[expose] def matHom : GL ι K →* MulAut (StdMod ι K) where
  toFun := matAut
  map_one' := toAddMap_injective fun v => by
    rw [toAddMap_matAut, Units.val_one, Matrix.one_mulVec, toAddMap_one]
  map_mul' g h := toAddMap_injective fun v => by
    rw [toAddMap_mul, toAddMap_matAut, toAddMap_matAut, toAddMap_matAut, Units.val_mul,
      Matrix.mulVec_mulVec]

theorem matHom_apply (g : GL ι K) : matHom g = matAut g := rfl

@[expose] def natAut (Γ : Subgroup (GL ι K)) : ↥Γ →* MulAut (StdMod ι K) :=
  matHom.comp Γ.subtype

theorem natAut_apply (Γ : Subgroup (GL ι K)) (γ : ↥Γ) (x : StdMod ι K) :
    natAut Γ γ x = natAct Γ γ x := rfl

theorem toAddMap_natAut (Γ : Subgroup (GL ι K)) (γ : ↥Γ) (v : ι → K) :
    toAddMap (natAut Γ γ) v = ((γ : GL ι K) : Matrix ι ι K) *ᵥ v := rfl

abbrev natImage (Γ : Subgroup (GL ι K)) : Subgroup (MulAut (StdMod ι K)) := (natAut Γ).range

abbrev natNorm (Γ : Subgroup (GL ι K)) : Subgroup (MulAut (StdMod ι K)) :=
  Subgroup.normalizer (natImage Γ : Set (MulAut (StdMod ι K)))

theorem natImage_eq_map (Γ : Subgroup (GL ι K)) : natImage Γ = Γ.map matHom := by
  rw [natImage, natAut, MonoidHom.range_comp, Subgroup.range_subtype]

section Realize

variable {V : Type*} [CommGroup V]

theorem exists_mulEquiv_of_realizesVia (Γ : Subgroup (GL ι K)) {H : Subgroup (MulAut V)}
    {π : ↥Γ →* ↥H} (h : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π) :
    ∃ e : V ≃* StdMod ι K, ∀ (γ : ↥Γ) (v : V),
      e (((π γ : ↥H) : MulAut V) v) = natAct Γ γ (e v) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let q : ↥(⊤ : Subgroup (StdMod ι K)) ⧸
      (⊥ : Subgroup (StdMod ι K)).subgroupOf (⊤ : Subgroup (StdMod ι K)) ≃* StdMod ι K :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  let e : V ≃* StdMod ι K :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.ofBijective β ⟨hβi, hβs⟩).trans q)
  refine ⟨e, fun γ v => ?_⟩
  have hq : ∀ m : StdMod ι K, q (QuotientGroup.mk ⟨m, trivial⟩) = m := fun m => rfl
  have hqs : ∀ x, x = (QuotientGroup.mk ⟨q x, trivial⟩ : ↥(⊤ : Subgroup (StdMod ι K)) ⧸
      (⊥ : Subgroup (StdMod ι K)).subgroupOf (⊤ : Subgroup (StdMod ι K))) := fun x => by
    induction x using QuotientGroup.induction_on with
    | H m => rfl
  have h1 : β ⟨v, trivial⟩ = QuotientGroup.mk ⟨e v, trivial⟩ := hqs _
  have h2 := hβe γ ⟨v, trivial⟩ ⟨e v, trivial⟩ trivial trivial h1
  have h3 := congrArg q h2
  exact h3

theorem map_congrHom_eq_natImage (Γ : Subgroup (GL ι K)) {H : Subgroup (MulAut V)}
    {π : ↥Γ →* ↥H} (hπ : Function.Surjective π) (e : V ≃* StdMod ι K)
    (he : ∀ (γ : ↥Γ) (v : V), e (((π γ : ↥H) : MulAut V) v) = natAct Γ γ (e v)) :
    H.map (congrHom e) = natImage Γ := by
  have hγ : ∀ γ : ↥Γ, congrHom e ((π γ : ↥H) : MulAut V) = natAut Γ γ := fun γ => by
    ext x
    rw [congrHom_apply, he, MulEquiv.apply_symm_apply]
    rfl
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨γ, hγx⟩ := hπ ⟨x, hx⟩
    refine ⟨γ, ?_⟩
    rw [← hγ, hγx]
  · rintro ⟨γ, rfl⟩
    exact ⟨_, (π γ).2, hγ γ⟩

theorem exists_transport_natural {Γ : Subgroup (GL ι K)} {L X : Subgroup (MulAut V)}
    (hL : (FFModel.nat Γ).Realizes L ⊤ ⊥) (hLX : L ≤ X)
    (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    ∃ e : V ≃* StdMod ι K, natImage Γ ≤ X.map (congrHom e) ∧
      X.map (congrHom e) ≤ natNorm Γ := by
  obtain ⟨π, hπ⟩ := hL
  obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia Γ hπ
  have hLe := map_congrHom_eq_natImage Γ hπ.1 e he
  refine ⟨e, hLe ▸ Subgroup.map_mono hLX, ?_⟩
  have h1 : (Subgroup.normalizer (L : Set (MulAut V))).map (congrHom e) =
      Subgroup.normalizer ((L.map (congrHom e) : Subgroup (MulAut (StdMod ι K))) :
        Set (MulAut (StdMod ι K))) :=
    Subgroup.map_equiv_normalizer_eq L (MulAut.congr e)
  rw [natNorm, ← hLe, ← h1]
  exact Subgroup.map_mono hXN

end Realize

@[expose] def HasScalarCommutant (Γ : Subgroup (GL ι K)) : Prop :=
  ∀ f : (ι → K) →+ (ι → K),
    (∀ γ ∈ Γ, ∀ v, f ((γ : Matrix ι ι K) *ᵥ v) = (γ : Matrix ι ι K) *ᵥ f v) →
      ∃ c : K, ∀ v, f v = c • v

@[expose] def IsSemilinear (g : MulAut (StdMod ι K)) (σ : K ≃+* K) : Prop :=
  ∀ (c : K) (v : ι → K), toAddMap g (c • v) = σ c • toAddMap g v

omit [Fintype ι] [DecidableEq ι] in
theorem toAddMap_zero (g : MulAut (StdMod ι K)) : toAddMap g 0 = 0 := by
  unfold toAddMap
  rw [ofAdd_zero, map_one, toAdd_one]

omit [Fintype ι] [DecidableEq ι] in
theorem toAddMap_eq_zero_iff (g : MulAut (StdMod ι K)) {v : ι → K} :
    toAddMap g v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have := congrArg (toAddMap g⁻¹) h
    rwa [toAddMap_apply_inv, toAddMap_zero] at this
  · rintro rfl
    exact toAddMap_zero g

omit [Fintype ι] in
theorem IsSemilinear.unique [Nonempty ι] {g : MulAut (StdMod ι K)} {σ τ : K ≃+* K}
    (hσ : IsSemilinear g σ) (hτ : IsSemilinear g τ) : σ = τ := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  ext c
  have h1 := hσ c (toAddMap g⁻¹ (Pi.single i 1))
  have h2 := hτ c (toAddMap g⁻¹ (Pi.single i 1))
  rw [toAddMap_inv_apply] at h1 h2
  have h3 := congrFun (h1.symm.trans h2) i
  simpa using h3

omit [Fintype ι] [DecidableEq ι] in
theorem IsSemilinear.mul {g h : MulAut (StdMod ι K)} {σ τ : K ≃+* K} (hg : IsSemilinear g σ)
    (hh : IsSemilinear h τ) : IsSemilinear (g * h) (τ.trans σ) := by
  intro c v
  rw [toAddMap_mul, toAddMap_mul, hh, hg]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem isSemilinear_one : IsSemilinear (1 : MulAut (StdMod ι K)) (RingEquiv.refl K) :=
  fun _ _ => rfl

theorem isSemilinear_matAut (g : GL ι K) : IsSemilinear (matAut g) (RingEquiv.refl K) := by
  intro c v
  rw [toAddMap_matAut, toAddMap_matAut, Matrix.mulVec_smul]
  rfl

theorem exists_semilinear [Finite K] [Nonempty ι] {Γ : Subgroup (GL ι K)}
    (hΓ : HasScalarCommutant Γ) {g : MulAut (StdMod ι K)}
    (hg : g ∈ natNorm Γ) : ∃ σ : K ≃+* K, IsSemilinear g σ := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hconj : ∀ γ : ↥Γ, ∃ γ' : ↥Γ, g⁻¹ * natAut Γ γ * g = natAut Γ γ' := by
    intro γ
    have hmem : natAut Γ γ ∈ natImage Γ := ⟨γ, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) (natAut Γ γ)).mp hmem
    rw [inv_inv] at h2
    obtain ⟨γ', hγ'⟩ := h2
    exact ⟨γ', hγ'.symm⟩
  have hcomm : ∀ c : K, ∃ c' : K, ∀ v, toAddMap g (c • toAddMap g⁻¹ v) = c' • v := by
    intro c
    let f : (ι → K) →+ (ι → K) := AddMonoidHom.mk' (fun v => toAddMap g (c • toAddMap g⁻¹ v))
      (fun v w => by rw [toAddMap_add, smul_add, toAddMap_add])
    refine hΓ f fun γ hγ v => ?_
    obtain ⟨γ', hγ'⟩ := hconj ⟨γ, hγ⟩
    have hγg : g * natAut Γ γ' = natAut Γ ⟨γ, hγ⟩ * g := by
      rw [← hγ']
      group
    have h1 : toAddMap g⁻¹ ((γ : Matrix ι ι K) *ᵥ v) =
        ((γ' : GL ι K) : Matrix ι ι K) *ᵥ toAddMap g⁻¹ v := by
      have := congrArg (fun y => toAddMap y (toAddMap g⁻¹ v)) hγ'
      simp only [toAddMap_mul, toAddMap_natAut, toAddMap_inv_apply] at this
      exact this
    have h2 : ∀ w, toAddMap g (((γ' : GL ι K) : Matrix ι ι K) *ᵥ w) =
        (γ : Matrix ι ι K) *ᵥ toAddMap g w := by
      intro w
      have := congrArg (fun y => toAddMap y w) hγg
      simpa only [toAddMap_mul, toAddMap_natAut] using this
    change toAddMap g (c • toAddMap g⁻¹ ((γ : Matrix ι ι K) *ᵥ v)) =
      (γ : Matrix ι ι K) *ᵥ toAddMap g (c • toAddMap g⁻¹ v)
    rw [h1, ← Matrix.mulVec_smul, h2]
  choose σf hσf using hcomm
  have hsl : ∀ (c : K) (w : ι → K), toAddMap g (c • w) = σf c • toAddMap g w := by
    intro c w
    have := hσf c (toAddMap g w)
    rwa [toAddMap_apply_inv] at this
  have huniq : ∀ a b : K, (∀ w, a • toAddMap g w = b • toAddMap g w) → a = b := by
    intro a b h
    have h1 := h (toAddMap g⁻¹ (Pi.single i 1))
    rw [toAddMap_inv_apply] at h1
    simpa using congrFun h1 i
  let σr : K →+* K :=
    { toFun := σf
      map_one' := huniq _ _ fun w => by rw [← hsl, one_smul, one_smul]
      map_mul' := fun a b => huniq _ _ fun w => by rw [← hsl, mul_smul, hsl, hsl, mul_smul]
      map_zero' := huniq _ _ fun w => by rw [← hsl, zero_smul, zero_smul, toAddMap_zero]
      map_add' := fun a b => huniq _ _ fun w => by
        rw [← hsl, add_smul, toAddMap_add, hsl, hsl, add_smul] }
  have hinj : Function.Injective σr := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 := hsl a (Pi.single i 1)
    change toAddMap g (a • Pi.single i 1) = σf a • _ at h1
    have h2 : σf a = 0 := ha
    rw [h2, zero_smul, toAddMap_eq_zero_iff] at h1
    simpa using congrFun h1 i
  exact ⟨RingEquiv.ofBijective σr ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, hsl⟩

omit [Fintype ι] [DecidableEq ι] in
theorem card_fixV_zpowers (g : MulAut (StdMod ι K)) :
    Nat.card ↥(fixV (Subgroup.zpowers g)) = Nat.card {v : ι → K // toAddMap g v = v} := by
  refine Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, ?_⟩
      invFun := fun v => ⟨Multiplicative.ofAdd v.1, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun v => rfl }
  · have := mem_fixV_zpowers_iff.mp x.2
    unfold toAddMap
    rw [ofAdd_toAdd, this]
  · exact mem_fixV_zpowers_iff.mpr (congrArg Multiplicative.ofAdd v.2)

omit [DecidableEq ι] [Field K] in
theorem card_stdMod [Finite K] : Nat.card (StdMod ι K) = Nat.card K ^ Fintype.card ι := by
  change Nat.card (ι → K) = _
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

omit [DecidableEq ι] in
theorem rkIdx_fixV_of_card [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (g : MulAut (StdMod ι K))
    {j : ℕ} (hj : j ≤ n * Fintype.card ι)
    (hcard : Nat.card ↥(fixV (Subgroup.zpowers g)) = 2 ^ j) :
    rkIdx (fixV (Subgroup.zpowers g)) = n * Fintype.card ι - j := by
  have h1 := (fixV (Subgroup.zpowers g)).card_mul_index
  rw [hcard, card_stdMod, hK, ← pow_mul] at h1
  have h2 : n * Fintype.card ι = j + (n * Fintype.card ι - j) := (Nat.add_sub_cancel' hj).symm
  rw [h2, pow_add] at h1
  have h3 := Nat.eq_of_mul_eq_mul_left (by positivity) h1
  unfold rkIdx
  rw [h3, padicValNat.prime_pow]

omit [DecidableEq ι] in
theorem le_rkIdx_fixV_of_linear [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {g : MulAut (StdMod ι K)} (hg : IsSemilinear g (RingEquiv.refl K)) (hg1 : g ≠ 1) :
    n ≤ rkIdx (fixV (Subgroup.zpowers g)) := by
  let W : Submodule K (ι → K) :=
    { carrier := {v | toAddMap g v = v}
      add_mem' := fun {v w} hv hw => by
        change toAddMap g (v + w) = v + w
        rw [toAddMap_add, hv, hw]
      zero_mem' := toAddMap_zero g
      smul_mem' := fun c v hv => by
        change toAddMap g (c • v) = c • v
        rw [hg c v, hv]
        rfl }
  have hW : W ≠ ⊤ := by
    intro h
    apply hg1
    refine toAddMap_injective fun v => ?_
    have : v ∈ W := by rw [h]; trivial
    exact this
  have hlt : Module.finrank K W < Fintype.card ι := by
    have := Submodule.finrank_lt hW
    rwa [Module.finrank_fintype_fun_eq_card] at this
  have hcard : Nat.card ↥(fixV (Subgroup.zpowers g)) = 2 ^ (n * Module.finrank K W) := by
    rw [card_fixV_zpowers]
    have : Nat.card {v : ι → K // toAddMap g v = v} = Nat.card W := rfl
    rw [this, Module.natCard_eq_pow_finrank (K := K) (V := W), hK, ← pow_mul]
  have hle : n * Module.finrank K W ≤ n * Fintype.card ι := Nat.mul_le_mul_left n hlt.le
  rw [rkIdx_fixV_of_card hK g hle hcard]
  have : n * Module.finrank K W + n ≤ n * Fintype.card ι := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left n hlt
  omega

omit [DecidableEq ι] in
omit [Fintype ι] [DecidableEq ι] in
theorem IsSemilinear.pow {g : MulAut (StdMod ι K)} {σ : K ≃+* K} (hg : IsSemilinear g σ)
    (k : ℕ) : IsSemilinear (g ^ k) (σ ^ k) := by
  induction k with
  | zero => exact isSemilinear_one
  | succ k ih =>
    rw [pow_succ', pow_succ']
    exact hg.mul ih

omit [DecidableEq ι] in
theorem rkIdx_fixV_eq_of_linear [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    {g : MulAut (StdMod ι K)} (W : Submodule K (ι → K))
    (hW : ∀ v, v ∈ W ↔ toAddMap g v = v) :
    rkIdx (fixV (Subgroup.zpowers g)) = m * (Fintype.card ι - Module.finrank K W) := by
  have hle : Module.finrank K W ≤ Fintype.card ι := by
    have := Submodule.finrank_le W
    rwa [Module.finrank_fintype_fun_eq_card] at this
  have hcard : Nat.card ↥(fixV (Subgroup.zpowers g)) = 2 ^ (m * Module.finrank K W) := by
    rw [card_fixV_zpowers]
    have : Nat.card {v : ι → K // toAddMap g v = v} = Nat.card W :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => (hW v).symm)
    rw [this, Module.natCard_eq_pow_finrank (K := K) (V := W), hK, ← pow_mul]
  rw [rkIdx_fixV_of_card hK g (Nat.mul_le_mul_left m hle) hcard, Nat.mul_sub]

omit [DecidableEq ι] in
theorem card_fixV_of_semilinear [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {g : MulAut (StdMod ι K)} {σ : K ≃+* K} (hg : IsSemilinear g σ) {h : ℕ}
    (hσ : orderOf σ = h) (hgh : g ^ h = 1) :
    h ∣ n ∧ Nat.card ↥(fixV (Subgroup.zpowers g)) = 2 ^ (n * Fintype.card ι / h) := by
  let a : (ι → K) ≃+ (ι → K) :=
    { toFun := toAddMap g
      invFun := toAddMap g⁻¹
      left_inv := toAddMap_apply_inv g
      right_inv := toAddMap_inv_apply g
      map_add' := toAddMap_add g }
  have hiter : ∀ (k : ℕ) (v : ι → K), (⇑a)^[k] v = toAddMap (g ^ k) v := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [Function.iterate_succ_apply', ih, pow_succ']
      rfl
  have hah : ∀ v, (⇑a)^[h] v = v := fun v => by rw [hiter, hgh]; rfl
  obtain ⟨hdvd, k₀, -, -, b, -, C, hC, -, -, hCcard⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis Nat.prime_two hn hK σ hσ
      (Module.finrank_fintype_fun_eq_card K) a hg hah
  refine ⟨hdvd, ?_⟩
  rw [card_fixV_zpowers, ← hCcard]
  refine Nat.card_congr
    { toFun := fun v => ⟨v.1, by rw [← SetLike.mem_coe, hC]; exact v.2⟩
      invFun := fun v => ⟨v.1, by have := v.2; rw [← SetLike.mem_coe, hC] at this; exact this⟩
      left_inv := fun v => rfl
      right_inv := fun v => rfl }

omit [DecidableEq ι] in
theorem exists_basis_fixed_of_semilinear [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {g : MulAut (StdMod ι K)} {σ : K ≃+* K} (hg : IsSemilinear g σ)
    {h : ℕ} (hσ : orderOf σ = h) (hgh : g ^ h = 1) :
    ∃ b : Module.Basis (Fin (Fintype.card ι)) K (ι → K), ∀ i, toAddMap g (b i) = b i := by
  let a : (ι → K) ≃+ (ι → K) :=
    { toFun := toAddMap g
      invFun := toAddMap g⁻¹
      left_inv := toAddMap_apply_inv g
      right_inv := toAddMap_inv_apply g
      map_add' := toAddMap_add g }
  have hiter : ∀ (k : ℕ) (v : ι → K), (⇑a)^[k] v = toAddMap (g ^ k) v := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [Function.iterate_succ_apply', ih, pow_succ']
      rfl
  have hah : ∀ v, (⇑a)^[h] v = v := fun v => by rw [hiter, hgh]; rfl
  obtain ⟨-, -, -, -, b, hb, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis Nat.prime_two hn hK σ hσ
      (Module.finrank_fintype_fun_eq_card K) a hg hah
  exact ⟨b, hb⟩

omit [Fintype ι] [DecidableEq ι] in
theorem eq_one_of_linear_of_fix_basis {g : MulAut (StdMod ι K)}
    (hg : IsSemilinear g (RingEquiv.refl K)) {m : ℕ}
    (b : Module.Basis (Fin m) K (ι → K)) (hb : ∀ i, toAddMap g (b i) = b i) : g = 1 := by
  let f : (ι → K) →ₗ[K] (ι → K) :=
    { toFun := toAddMap g
      map_add' := toAddMap_add g
      map_smul' := fun c v => hg c v }
  have hf : f = LinearMap.id := b.ext fun i => hb i
  refine toAddMap_injective fun v => ?_
  have := congrArg (fun F : (ι → K) →ₗ[K] (ι → K) => F v) hf
  exact this

theorem rkIdx_fixV_of_semilinear_two [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    [Nonempty ι] {g : MulAut (StdMod ι K)} {σ : K ≃+* K} (hg : IsSemilinear g σ)
    (hσ : σ ≠ RingEquiv.refl K) (hg2 : g ^ 2 = 1) :
    2 ∣ n ∧ 2 * rkIdx (fixV (Subgroup.zpowers g)) = n * Fintype.card ι := by
  have hσ2 : σ ^ 2 = 1 := by
    have h1 : IsSemilinear (g ^ 2) (σ.trans σ) := by
      rw [pow_two]
      exact hg.mul hg
    rw [hg2] at h1
    have := h1.unique isSemilinear_one
    ext c
    exact congrArg (fun τ : K ≃+* K => τ c) this
  have hord : orderOf σ = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hσ2) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hσ
    · exact h
  obtain ⟨hdvd, hcard⟩ := card_fixV_of_semilinear hn hK hg hord hg2
  refine ⟨hdvd, ?_⟩
  obtain ⟨m, rfl⟩ := hdvd
  have hj : 2 * m * Fintype.card ι / 2 = m * Fintype.card ι := by
    rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hj] at hcard
  have hle : m * Fintype.card ι ≤ 2 * m * Fintype.card ι := by
    rw [mul_assoc]
    omega
  rw [rkIdx_fixV_of_card hK g hle hcard]
  rw [mul_assoc]
  omega

omit [Fintype ι] [DecidableEq ι] in
theorem IsSemilinear.inv {g : MulAut (StdMod ι K)} {σ : K ≃+* K} (hg : IsSemilinear g σ) :
    IsSemilinear g⁻¹ σ.symm := by
  intro c v
  have h := hg (σ.symm c) (toAddMap g⁻¹ v)
  rw [RingEquiv.apply_symm_apply, toAddMap_inv_apply] at h
  rw [← h, toAddMap_apply_inv]

@[expose] def linSub : Subgroup (MulAut (StdMod ι K)) where
  carrier := {g | IsSemilinear g (RingEquiv.refl K)}
  one_mem' := isSemilinear_one
  mul_mem' := fun {g h} hg hh => by
    have := (show IsSemilinear g (RingEquiv.refl K) from hg).mul hh
    exact this
  inv_mem' := fun {g} hg => by
    have := (show IsSemilinear g (RingEquiv.refl K) from hg).inv
    exact this

omit [Fintype ι] [DecidableEq ι] in
theorem mem_linSub {g : MulAut (StdMod ι K)} :
    g ∈ linSub (ι := ι) (K := K) ↔ IsSemilinear g (RingEquiv.refl K) := Iff.rfl

theorem natImage_le_linSub (Γ : Subgroup (GL ι K)) : natImage Γ ≤ linSub := by
  rintro _ ⟨γ, rfl⟩
  exact isSemilinear_matAut _

theorem matHom_injective : Function.Injective (matHom : GL ι K →* MulAut (StdMod ι K)) := by
  intro A B h
  apply Units.ext
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  have := congrArg (fun g => toAddMap g v) h
  simpa [matHom_apply, toAddMap_matAut] using this

theorem exists_matAut_of_mem_linSub {g : MulAut (StdMod ι K)} (hg : g ∈ linSub) :
    ∃ A : GL ι K, g = matAut A := by
  have hg' : IsSemilinear g⁻¹ (RingEquiv.refl K) := by
    have := (show IsSemilinear g (RingEquiv.refl K) from hg).inv
    exact this
  let f : (ι → K) →ₗ[K] (ι → K) :=
    { toFun := toAddMap g
      map_add' := toAddMap_add g
      map_smul' := fun c v => hg c v }
  let f' : (ι → K) →ₗ[K] (ι → K) :=
    { toFun := toAddMap g⁻¹
      map_add' := toAddMap_add g⁻¹
      map_smul' := fun c v => hg' c v }
  have hff' : LinearMap.toMatrix' f * LinearMap.toMatrix' f' = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : f ∘ₗ f' = LinearMap.id := LinearMap.ext fun v => toAddMap_inv_apply g v
    rw [this, LinearMap.toMatrix'_id]
  have hf'f : LinearMap.toMatrix' f' * LinearMap.toMatrix' f = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : f' ∘ₗ f = LinearMap.id := LinearMap.ext fun v => toAddMap_apply_inv g v
    rw [this, LinearMap.toMatrix'_id]
  refine ⟨⟨LinearMap.toMatrix' f, LinearMap.toMatrix' f', hff', hf'f⟩, ?_⟩
  refine toAddMap_injective fun v => ?_
  rw [toAddMap_matAut]
  change f v = _
  rw [← LinearMap.toMatrix'_mulVec]

theorem isCyclic_ringAut [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    IsCyclic (K ≃+* K) := by
  obtain ⟨σ, -, -, hσ, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hK
  exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, hσ⟩

theorem card_le_two_of_isCyclic {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] (B : Subgroup Q)
    (hB : ∀ b ∈ B, b ^ 2 = 1) : Nat.card B ≤ 2 := by
  obtain ⟨b, hb⟩ := (Subgroup.isCyclic B).exists_generator
  rw [← orderOf_eq_card_of_forall_mem_zpowers hb]
  have : (b : ↥B) ^ 2 = 1 := Subtype.ext (by simpa using hB b.1 b.2)
  have h := orderOf_le_of_pow_eq_one (by norm_num) this
  exact h

section FieldPart

variable [Finite K] [Nonempty ι] {Γ : Subgroup (GL ι K)}

@[expose] noncomputable def fieldAut (hΓ : HasScalarCommutant Γ)
    (g : ↥(natNorm Γ)) : K ≃+* K :=
  Classical.choose (exists_semilinear hΓ g.2)

theorem isSemilinear_fieldAut (hΓ : HasScalarCommutant Γ) (g : ↥(natNorm Γ)) :
    IsSemilinear (g : MulAut (StdMod ι K)) (fieldAut hΓ g) :=
  Classical.choose_spec (exists_semilinear hΓ g.2)

@[expose] noncomputable def fieldHom (hΓ : HasScalarCommutant Γ) :
    ↥(natNorm Γ) →* (K ≃+* K) where
  toFun := fieldAut hΓ
  map_one' := (isSemilinear_fieldAut hΓ 1).unique isSemilinear_one
  map_mul' g h :=
    (isSemilinear_fieldAut hΓ (g * h)).unique
      ((isSemilinear_fieldAut hΓ g).mul (isSemilinear_fieldAut hΓ h))

theorem fieldHom_eq_iff (hΓ : HasScalarCommutant Γ) (g : ↥(natNorm Γ))
    (σ : K ≃+* K) : fieldHom hΓ g = σ ↔ IsSemilinear (g : MulAut (StdMod ι K)) σ :=
  ⟨fun h => h ▸ isSemilinear_fieldAut hΓ g, fun h => (isSemilinear_fieldAut hΓ g).unique h⟩

theorem fieldHom_eq_one_iff (hΓ : HasScalarCommutant Γ) (g : ↥(natNorm Γ)) :
    fieldHom hΓ g = 1 ↔ (g : MulAut (StdMod ι K)) ∈ linSub :=
  fieldHom_eq_iff hΓ g 1

theorem card_le_two_mul_card_inf_linSub (hΓ : HasScalarCommutant Γ) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {E : Subgroup (MulAut (StdMod ι K))} (hEN : E ≤ natNorm Γ)
    (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ linSub) := by
  have : IsCyclic (K ≃+* K) := isCyclic_ringAut hn hK
  have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  have : Finite (MulAut (StdMod ι K)) := MulEquiv.finite_left
  let φ : ↥E →* (K ≃+* K) := (fieldHom hΓ).comp (Subgroup.inclusion hEN)
  have hrange : Nat.card φ.range ≤ 2 := by
    refine card_le_two_of_isCyclic _ ?_
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (by simpa using hE x.1 x.2)
    rw [this, map_one]
  have hker : Nat.card φ.ker = Nat.card ↥(E ⊓ linSub) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, (fieldHom_eq_one_iff hΓ _).mp x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, (fieldHom_eq_one_iff hΓ ⟨y.1, hEN y.2.1⟩).mpr y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hcard : Nat.card E = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
  rw [hcard, hker, mul_comm 2]
  exact Nat.mul_le_mul_left _ hrange

theorem pRank_two_le_linSub (hΓ : HasScalarCommutant Γ) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {X : Subgroup (MulAut (StdMod ι K))}
    (hX : X ≤ natNorm Γ) :
    CFSG.Open.pRank 2 X ≤ CFSG.Open.pRank 2 (X ⊓ linSub) + 1 := by
  have : Finite (MulAut (StdMod ι K)) := MulEquiv.finite_left
  obtain ⟨E, hEX, hE, hEc⟩ := exists_isElemAbelian_card_pRank X
  have hE₀ : IsElemAbelian 2 (E ⊓ linSub) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x hx.1⟩
    have := @mul_comm' (↥E) _ hE.1 ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩
    simpa using congrArg Subtype.val this
  obtain ⟨k, hk⟩ := exists_card_eq_two_pow_of_isElemAbelian hE₀
  have hk' : k ≤ CFSG.Open.pRank 2 (X ⊓ linSub) :=
    le_pRank Nat.prime_two (inf_le_inf_right _ hEX) hE₀ hk
  have h1 : 2 ^ CFSG.Open.pRank 2 X ≤ 2 ^ (k + 1) := by
    rw [← hEc, pow_succ, ← hk, mul_comm]
    exact card_le_two_mul_card_inf_linSub hΓ hn hK (hEX.trans hX) hE.2
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  omega

end FieldPart

end H

end CFSG.Quasithin
