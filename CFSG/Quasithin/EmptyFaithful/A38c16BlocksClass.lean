module

public import CFSG.Quasithin.EmptyFaithful.A38c16BlocksIndep

public section

namespace CFSG.Quasithin.A38c16.Blocks

open scoped MatrixGroups

section Setting

variable {W : Type} [CommGroup W]

@[expose] def conjOn (K : Subgroup (MulAut W)) (g : MulAut W) (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hg' : ∀ k ∈ K, g⁻¹ * k * g ∈ K) : ↥K ≃* ↥K where
  toFun k := ⟨g * k * g⁻¹, hg k k.2⟩
  invFun k := ⟨g⁻¹ * k * g, hg' k k.2⟩
  left_inv k := by apply Subtype.ext; simp [mul_assoc]
  right_inv k := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

variable {Γ K Kp : Subgroup (MulAut W)}

@[expose] def conjK (hΓ : Case3Setting Γ K Kp) (γ : ↥Γ) : ↥K ≃* ↥K :=
  conjOn K (γ : MulAut W) (hΓ.K_norm γ γ.2) (fun k hk => by
    simpa using hΓ.K_norm ((γ : MulAut W)⁻¹) (Γ.inv_mem γ.2) k hk)

@[expose] def conjKp (hΓ : Case3Setting Γ K Kp) (γ : ↥Γ) : ↥Kp ≃* ↥Kp :=
  conjOn Kp (γ : MulAut W) (hΓ.Kp_norm γ γ.2) (fun k hk => by
    simpa using hΓ.Kp_norm ((γ : MulAut W)⁻¹) (Γ.inv_mem γ.2) k hk)

theorem coe_conjK (hΓ : Case3Setting Γ K Kp) (γ : ↥Γ) (k : ↥K) :
    ((conjK hΓ γ k : ↥K) : MulAut W) = (γ : MulAut W) * k * (γ : MulAut W)⁻¹ := rfl

theorem coe_conjKp (hΓ : Case3Setting Γ K Kp) (γ : ↥Γ) (k : ↥Kp) :
    ((conjKp hΓ γ k : ↥Kp) : MulAut W) = (γ : MulAut W) * k * (γ : MulAut W)⁻¹ := rfl

theorem conjK_mul (hΓ : Case3Setting Γ K Kp) (γ γ' : ↥Γ) :
    conjK hΓ (γ * γ') = (conjK hΓ γ').trans (conjK hΓ γ) := by
  refine MulEquiv.ext fun k => Subtype.ext ?_
  show ((γ * γ' : ↥Γ) : MulAut W) * k * ((γ * γ' : ↥Γ) : MulAut W)⁻¹ =
    (γ : MulAut W) * ((γ' : MulAut W) * k * (γ' : MulAut W)⁻¹) * (γ : MulAut W)⁻¹
  simp [mul_assoc]

theorem conjKp_mul (hΓ : Case3Setting Γ K Kp) (γ γ' : ↥Γ) :
    conjKp hΓ (γ * γ') = (conjKp hΓ γ').trans (conjKp hΓ γ) := by
  refine MulEquiv.ext fun k => Subtype.ext ?_
  show ((γ * γ' : ↥Γ) : MulAut W) * k * ((γ * γ' : ↥Γ) : MulAut W)⁻¹ =
    (γ : MulAut W) * ((γ' : MulAut W) * k * (γ' : MulAut W)⁻¹) * (γ : MulAut W)⁻¹
  simp [mul_assoc]

@[expose] def liftAut {G : Type*} [Group G] (θ : G ≃* SL(3, ZMod 2)) (e : G ≃* G) :
    SL(3, ZMod 2) ≃* SL(3, ZMod 2) :=
  (θ.symm.trans e).trans θ

theorem liftAut_apply {G : Type*} [Group G] (θ : G ≃* SL(3, ZMod 2)) (e : G ≃* G)
    (x : SL(3, ZMod 2)) : liftAut θ e x = θ (e (θ.symm x)) := rfl

theorem liftAut_theta {G : Type*} [Group G] (θ : G ≃* SL(3, ZMod 2)) (e : G ≃* G) (g : G) :
    liftAut θ e (θ g) = θ (e g) := by
  rw [liftAut_apply, MulEquiv.symm_apply_apply]

theorem liftAut_trans {G : Type*} [Group G] (θ : G ≃* SL(3, ZMod 2)) (e e' : G ≃* G) :
    liftAut θ (e.trans e') = (liftAut θ e).trans (liftAut θ e') := by
  refine MulEquiv.ext fun x => ?_
  simp [liftAut_apply]

@[expose] noncomputable def classMap (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) (γ : ↥Γ) : ZMod 2 × ZMod 2 :=
  (outerClass (liftAut θ (conjK hΓ γ)), outerClass (liftAut θp (conjKp hΓ γ)))

theorem classMap_mul (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) (γ γ' : ↥Γ) :
    classMap hΓ θ θp (γ * γ') = classMap hΓ θ θp γ + classMap hΓ θ θp γ' := by
  unfold classMap
  rw [conjK_mul, conjKp_mul, liftAut_trans, liftAut_trans, hAut.trans, hAut.trans]
  refine Prod.ext ?_ ?_
  · exact add_comm _ _
  · exact add_comm _ _

theorem classMap_one (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) : classMap hΓ θ θp (1 : ↥Γ) = 0 := by
  have h := classMap_mul hAut hΓ θ θp 1 1
  rw [mul_one] at h
  simpa using h

theorem classMap_inv (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) (γ : ↥Γ) :
    classMap hΓ θ θp γ⁻¹ = classMap hΓ θ θp γ := by
  have h := classMap_mul hAut hΓ θ θp γ⁻¹ γ
  rw [inv_mul_cancel, classMap_one hAut hΓ θ θp] at h
  have key : ∀ a b : ZMod 2 × ZMod 2, 0 = a + b → a = b := by decide
  exact key _ _ h

theorem classMap_add_self (a : ZMod 2 × ZMod 2) : a + a = 0 := by
  revert a; decide

theorem exists_inner_of_outerClass_zero {G : Type*} [Group G] (hAut : SL3OutFacts)
    (θ : G ≃* SL(3, ZMod 2)) (e : G ≃* G) (h : outerClass (liftAut θ e) = 0) :
    ∃ g₀ : G, ∀ k : G, e k = g₀ * k * g₀⁻¹ := by
  obtain ⟨g, hg⟩ := hAut.inner _ h
  refine ⟨θ.symm g, fun k => ?_⟩
  apply θ.injective
  have := hg (θ k)
  rw [liftAut_theta] at this
  rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem exists_mul_of_classMap_eq_zero (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp)
    (θ : ↥K ≃* SL(3, ZMod 2)) (θp : ↥Kp ≃* SL(3, ZMod 2)) {γ : ↥Γ}
    (h : classMap hΓ θ θp γ = 0) :
    ∃ k : ↥K, ∃ y : ↥Kp, (γ : MulAut W) = (k : MulAut W) * (y : MulAut W) := by
  have h1 : outerClass (liftAut θ (conjK hΓ γ)) = 0 := by
    have := congrArg Prod.fst h
    simpa [classMap] using this
  have h2 : outerClass (liftAut θp (conjKp hΓ γ)) = 0 := by
    have := congrArg Prod.snd h
    simpa [classMap] using this
  obtain ⟨k₀, hk₀⟩ := exists_inner_of_outerClass_zero hAut θ _ h1
  obtain ⟨y₀, hy₀⟩ := exists_inner_of_outerClass_zero hAut θp _ h2
  have hk : ∀ k : ↥K, (γ : MulAut W) * k * (γ : MulAut W)⁻¹ =
      (k₀ : MulAut W) * k * (k₀ : MulAut W)⁻¹ := fun k => congrArg Subtype.val (hk₀ k)
  have hy : ∀ y : ↥Kp, (γ : MulAut W) * y * (γ : MulAut W)⁻¹ =
      (y₀ : MulAut W) * y * (y₀ : MulAut W)⁻¹ := fun y => congrArg Subtype.val (hy₀ y)
  refine ⟨k₀, y₀, ?_⟩
  set c : MulAut W := ((k₀ : MulAut W) * y₀)⁻¹ * γ with hc
  have hcΓ : c ∈ Γ := Γ.mul_mem (Γ.inv_mem (Γ.mul_mem (hΓ.K_le k₀.2) (hΓ.Kp_le y₀.2))) γ.2
  have hcinv : c⁻¹ = (γ : MulAut W)⁻¹ * ((k₀ : MulAut W) * y₀) := by
    simp [hc, mul_assoc]
  have hcK : ∀ k ∈ K, c * k = k * c := by
    intro k hkK
    have h3 : c * k * c⁻¹ = k := by
      calc c * k * c⁻¹ = ((k₀ : MulAut W) * y₀)⁻¹ * ((γ : MulAut W) * k * (γ : MulAut W)⁻¹) *
            ((k₀ : MulAut W) * y₀) := by rw [hcinv]; simp only [hc]; group
        _ = ((k₀ : MulAut W) * y₀)⁻¹ * ((k₀ : MulAut W) * k * (k₀ : MulAut W)⁻¹) *
            ((k₀ : MulAut W) * y₀) := by rw [hk ⟨k, hkK⟩]
        _ = (y₀ : MulAut W)⁻¹ * k * y₀ := by group
        _ = k := by
            rw [mul_assoc, hΓ.comm k hkK y₀ y₀.2]
            group
    exact mul_inv_eq_iff_eq_mul.mp h3
  have hcKp : ∀ y ∈ Kp, c * y = y * c := by
    intro y hyK
    have hcomm' : ∀ z ∈ Kp, (k₀ : MulAut W)⁻¹ * z * k₀ = z := by
      intro z hz
      rw [mul_assoc, ← hΓ.comm k₀ k₀.2 z hz]
      group
    have hmem : (y₀ : MulAut W) * y * (y₀ : MulAut W)⁻¹ ∈ Kp :=
      Kp.mul_mem (Kp.mul_mem y₀.2 hyK) (Kp.inv_mem y₀.2)
    have h3 : c * y * c⁻¹ = y := by
      calc c * y * c⁻¹ = ((k₀ : MulAut W) * y₀)⁻¹ * ((γ : MulAut W) * y * (γ : MulAut W)⁻¹) *
            ((k₀ : MulAut W) * y₀) := by rw [hcinv]; simp only [hc]; group
        _ = ((k₀ : MulAut W) * y₀)⁻¹ * ((y₀ : MulAut W) * y * (y₀ : MulAut W)⁻¹) *
            ((k₀ : MulAut W) * y₀) := by rw [hy ⟨y, hyK⟩]
        _ = (y₀ : MulAut W)⁻¹ * ((k₀ : MulAut W)⁻¹ * ((y₀ : MulAut W) * y * (y₀ : MulAut W)⁻¹) *
            k₀) * y₀ := by group
        _ = (y₀ : MulAut W)⁻¹ * ((y₀ : MulAut W) * y * (y₀ : MulAut W)⁻¹) * y₀ := by
            rw [hcomm' _ hmem]
        _ = y := by group
    exact mul_inv_eq_iff_eq_mul.mp h3
  have h4 : c = 1 := hΓ.cent c hcΓ hcK hcKp
  have h5 : ((k₀ : MulAut W) * y₀)⁻¹ * γ = 1 := h4
  exact (inv_mul_eq_one.mp h5).symm

end Setting

section Blocks

variable {W : Type} [CommGroup W]

@[expose] def blk (S : Subgroup W) (γ : MulAut W) : Subgroup W := S.comap (γ⁻¹ : MulAut W).toMonoidHom

theorem mem_blk {S : Subgroup W} {γ : MulAut W} {w : W} : w ∈ blk S γ ↔ γ⁻¹ w ∈ S := Iff.rfl

structure Norm2 (K Kp : Subgroup (MulAut W)) (σ : MulAut W) : Prop where
  K_fwd : ∀ k ∈ K, σ * k * σ⁻¹ ∈ K
  K_bwd : ∀ k ∈ K, σ⁻¹ * k * σ ∈ K
  Kp_fwd : ∀ k ∈ Kp, σ * k * σ⁻¹ ∈ Kp
  Kp_bwd : ∀ k ∈ Kp, σ⁻¹ * k * σ ∈ Kp

theorem norm2_of_mem {Γ K Kp : Subgroup (MulAut W)} (hΓ : Case3Setting Γ K Kp) (γ : ↥Γ) :
    Norm2 K Kp (γ : MulAut W) where
  K_fwd := hΓ.K_norm γ γ.2
  K_bwd := fun k hk => by simpa using hΓ.K_norm ((γ : MulAut W)⁻¹) (Γ.inv_mem γ.2) k hk
  Kp_fwd := hΓ.Kp_norm γ γ.2
  Kp_bwd := fun k hk => by simpa using hΓ.Kp_norm ((γ : MulAut W)⁻¹) (Γ.inv_mem γ.2) k hk

theorem inv2_blk {K Kp : Subgroup (MulAut W)} {S : Subgroup W} {γ : MulAut W}
    (hγ : Norm2 K Kp γ) (hS : Inv2 K Kp S) : Inv2 K Kp (blk S γ) := by
  constructor
  · intro k hk w hw
    have : γ⁻¹ (k w) = (γ⁻¹ * k * γ) (γ⁻¹ w) := by simp [MulAut.mul_apply]
    show γ⁻¹ (k w) ∈ S
    rw [this]
    exact hS.1 _ (hγ.K_bwd k hk) _ hw
  · intro k hk w hw
    have : γ⁻¹ (k w) = (γ⁻¹ * k * γ) (γ⁻¹ w) := by simp [MulAut.mul_apply]
    show γ⁻¹ (k w) ∈ S
    rw [this]
    exact hS.2 _ (hγ.Kp_bwd k hk) _ hw

theorem blk_min {K Kp : Subgroup (MulAut W)} {S : Subgroup W} {γ : MulAut W}
    (hγ : Norm2 K Kp γ)
    (hmin : ∀ N : Subgroup W, N ≤ S → IsKSub K N → IsKSub Kp N → N = ⊥ ∨ N = S) :
    ∀ N : Subgroup W, N ≤ blk S γ → IsKSub K N → IsKSub Kp N → N = ⊥ ∨ N = blk S γ := by
  intro N hN hNK hNKp
  let N' : Subgroup W := N.comap γ.toMonoidHom
  have hN'S : N' ≤ S := fun v hv => by
    have := hN hv
    simpa [mem_blk] using this
  have hv : ∀ k : MulAut W, ∀ v : W, γ (k v) = (γ * k * γ⁻¹) (γ v) := by
    intro k v; simp [MulAut.mul_apply]
  have hN'K : IsKSub K N' := fun k hk v hv' => by
    show γ (k v) ∈ N
    rw [hv]
    exact hNK _ (hγ.K_fwd k hk) _ hv'
  have hN'Kp : IsKSub Kp N' := fun k hk v hv' => by
    show γ (k v) ∈ N
    rw [hv]
    exact hNKp _ (hγ.Kp_fwd k hk) _ hv'
  rcases hmin N' hN'S hN'K hN'Kp with h | h
  · left
    rw [eq_bot_iff]
    intro n hn
    have : γ⁻¹ n ∈ N' := by
      show γ (γ⁻¹ n) ∈ N
      simpa using hn
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    have h1 : γ⁻¹ n = γ⁻¹ 1 := by rw [this, map_one]
    exact (γ⁻¹ : MulAut W).injective h1
  · right
    apply le_antisymm hN
    intro w hw
    have : γ⁻¹ w ∈ N' := by rw [h]; exact hw
    have h2 : γ (γ⁻¹ w) ∈ N := this
    simpa using h2

theorem blk_ne_bot {S : Subgroup W} (γ : MulAut W) (hS : S ≠ ⊥) : blk S γ ≠ ⊥ := by
  intro h
  apply hS
  rw [eq_bot_iff]
  intro v hv
  have : γ v ∈ blk S γ := by
    show γ⁻¹ (γ v) ∈ S
    simpa using hv
  rw [h, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact γ.injective (this.trans (map_one γ).symm)

variable {Γ K Kp : Subgroup (MulAut W)}

theorem blk_count (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp) (θ : ↥K ≃* SL(3, ZMod 2))
    (θp : ↥Kp ≃* SL(3, ZMod 2)) {S : Subgroup W} {t : ZMod 2 × ZMod 2}
    (hcount : ∀ F : Subgroup (↥K × ↥Kp), blkFixCard K Kp S F =
      Nat.card (fixSetT t (F.map (MulEquiv.prodCongr θ θp).toMonoidHom)))
    (γ : ↥Γ) (F : Subgroup (↥K × ↥Kp)) :
    blkFixCard K Kp (blk S γ) F =
      Nat.card (fixSetT (t + classMap hΓ θ θp γ)
        (F.map (MulEquiv.prodCongr θ θp).toMonoidHom)) := by
  set c : ↥K × ↥Kp →* ↥K × ↥Kp :=
    (MulEquiv.prodCongr (conjK hΓ γ⁻¹) (conjKp hΓ γ⁻¹)).toMonoidHom with hc
  have hψc : ∀ (g : ↥K × ↥Kp) (w : W),
      (((c g).1 : MulAut W) * ((c g).2 : MulAut W)) ((γ : MulAut W)⁻¹ w) =
        (γ : MulAut W)⁻¹ (((g.1 : MulAut W) * (g.2 : MulAut W)) w) := by
    intro g w
    have e1 : ((c g).1 : MulAut W) = (γ : MulAut W)⁻¹ * g.1 * (γ : MulAut W) := by
      show ((conjK hΓ γ⁻¹ g.1 : ↥K) : MulAut W) = _
      rw [coe_conjK]; simp
    have e2 : ((c g).2 : MulAut W) = (γ : MulAut W)⁻¹ * g.2 * (γ : MulAut W) := by
      show ((conjKp hΓ γ⁻¹ g.2 : ↥Kp) : MulAut W) = _
      rw [coe_conjKp]; simp
    rw [e1, e2]
    simp [MulAut.mul_apply]
  have h1 : blkFixCard K Kp (blk S γ) F = blkFixCard K Kp S (F.map c) := by
    unfold blkFixCard
    refine Nat.card_congr (Equiv.subtypeEquiv ((γ : MulAut W)⁻¹).toEquiv (fun w => ?_))
    constructor
    · rintro ⟨hw, hfix⟩
      refine ⟨hw, ?_⟩
      rintro _ ⟨g, hg, rfl⟩
      show (((c g).1 : MulAut W) * ((c g).2 : MulAut W)) ((γ : MulAut W)⁻¹ w) = (γ : MulAut W)⁻¹ w
      rw [hψc, hfix g hg]
    · rintro ⟨hw, hfix⟩
      refine ⟨hw, fun g hg => ?_⟩
      have := hfix (c g) ⟨g, hg, rfl⟩
      have h2 : (((c g).1 : MulAut W) * ((c g).2 : MulAut W)) ((γ : MulAut W)⁻¹ w) =
          (γ : MulAut W)⁻¹ w := this
      rw [hψc] at h2
      exact ((γ : MulAut W)⁻¹).injective h2
  rw [h1, hcount (F.map c), Subgroup.map_map]
  have h2 : (MulEquiv.prodCongr θ θp).toMonoidHom.comp c =
      (MulEquiv.prodCongr (liftAut θ (conjK hΓ γ⁻¹)) (liftAut θp (conjKp hΓ γ⁻¹))).toMonoidHom.comp
        (MulEquiv.prodCongr θ θp).toMonoidHom := by
    refine MonoidHom.ext fun g => Prod.ext ?_ ?_
    · show θ (conjK hΓ γ⁻¹ g.1) = liftAut θ (conjK hΓ γ⁻¹) (θ g.1)
      exact (liftAut_theta _ _ _).symm
    · show θp (conjKp hΓ γ⁻¹ g.2) = liftAut θp (conjKp hΓ γ⁻¹) (θp g.2)
      exact (liftAut_theta _ _ _).symm
  rw [h2, ← Subgroup.map_map, hAut.card_fix, ← classMap_inv hAut hΓ θ θp γ]
  rfl

theorem blk_eq_of_classMap_eq (hAut : SL3OutFacts) (hΓ : Case3Setting Γ K Kp)
    (θ : ↥K ≃* SL(3, ZMod 2)) (θp : ↥Kp ≃* SL(3, ZMod 2)) {S : Subgroup W}
    (hSK : IsKSub K S) (hSKp : IsKSub Kp S) {γ γ' : ↥Γ}
    (h : classMap hΓ θ θp γ = classMap hΓ θ θp γ') : blk S γ = blk S γ' := by
  have h0 : classMap hΓ θ θp (γ⁻¹ * γ') = 0 := by
    rw [classMap_mul hAut hΓ θ θp, classMap_inv hAut hΓ θ θp, h]
    exact classMap_add_self _
  obtain ⟨k, y, hky⟩ := exists_mul_of_classMap_eq_zero hAut hΓ θ θp h0
  have hsub : ∀ v ∈ S, ((γ⁻¹ * γ' : ↥Γ) : MulAut W) v ∈ S ∧
      ((γ⁻¹ * γ' : ↥Γ) : MulAut W)⁻¹ v ∈ S := by
    intro v hv
    rw [hky]
    refine ⟨?_, ?_⟩
    · rw [MulAut.mul_apply]
      exact hSK _ k.2 _ (hSKp _ y.2 _ hv)
    · rw [mul_inv_rev, MulAut.mul_apply]
      exact hSKp _ (Kp.inv_mem y.2) _ (hSK _ (K.inv_mem k.2) _ hv)
  ext w
  show (γ : MulAut W)⁻¹ w ∈ S ↔ (γ' : MulAut W)⁻¹ w ∈ S
  constructor
  · intro hw
    have h1 := (hsub _ hw).2
    have e : ((γ⁻¹ * γ' : ↥Γ) : MulAut W)⁻¹ ((γ : MulAut W)⁻¹ w) = (γ' : MulAut W)⁻¹ w := by
      simp [mul_inv_rev, MulAut.mul_apply]
    rwa [e] at h1
  · intro hw
    have h1 := (hsub _ hw).1
    have e : ((γ⁻¹ * γ' : ↥Γ) : MulAut W) ((γ' : MulAut W)⁻¹ w) = (γ : MulAut W)⁻¹ w := by
      simp [MulAut.mul_apply]
    rwa [e] at h1

end Blocks

end CFSG.Quasithin.A38c16.Blocks
