module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS3L30
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS3Nat

public section

namespace CFSG.Quasithin.F53.Stellmacher

open CFSG.Quasithin.F53Mod Equiv

theorem exists_hom_ne_one {V : Type} [CommGroup V] (hsq : ∀ x : V, x * x = 1) {u : V}
    (hu : u ≠ 1) : ∃ f : V →* Multiplicative (ZMod 2), f u ≠ 1 := by
  have h2 : ∀ x : Additive V, (2 : ℕ) • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Additive.ofMul.surjective x
    rw [← ofMul_pow, pow_two, hsq y]
    rfl
  let : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) (Additive V), φ (Additive.ofMul u) ≠ 0 := by
    by_contra h
    push Not at h
    exact hu ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) (Additive.ofMul u)).mp h)
  refine ⟨{ toFun := fun x => Multiplicative.ofAdd (φ (Additive.ofMul x))
            map_one' := by simp
            map_mul' := fun x y => by simp [ofMul_mul] }, ?_⟩
  intro h
  apply hφ
  exact h

@[expose] def powHom {W : Type} [CommGroup W] (a : W) (ha : a * a = 1) :
    Multiplicative (ZMod 2) →* W where
  toFun x := a ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [← pow_eq_pow_mod _ (by rw [pow_two]; exact ha), pow_add]

@[expose] def retrTerm (M : Model 3) (f : M.W →* Multiplicative (ZMod 2)) (u : M.W)
    (g : Perm (Fin 3)) : M.W →* M.W :=
  (powHom (M.act g u) (by rw [← map_mul, M.sq, map_one])).comp
    (f.comp (M.act g⁻¹).toMonoidHom)

theorem retrTerm_apply (M : Model 3) (f : M.W →* Multiplicative (ZMod 2)) (u : M.W)
    (g : Perm (Fin 3)) (w : M.W) :
    retrTerm M f u g w = (M.act g u) ^ (Multiplicative.toAdd (f (M.act g⁻¹ w))).val := rfl

theorem retrTerm_equivariant (M : Model 3) (f : M.W →* Multiplicative (ZMod 2)) (u : M.W)
    (σ g : Perm (Fin 3)) (w : M.W) :
    retrTerm M f u (σ * g) (M.act σ w) = M.act σ (retrTerm M f u g w) := by
  rw [retrTerm_apply, retrTerm_apply, map_pow, mul_inv_rev, act_mul_apply, act_mul_apply,
    act_inv_act]

theorem retr_equivariant (M : Model 3) (f : M.W →* Multiplicative (ZMod 2)) (u : M.W)
    (σ : Perm (Fin 3)) (w : M.W) :
    (∏ g, retrTerm M f u g) (M.act σ w) = M.act σ ((∏ g, retrTerm M f u g) w) := by
  rw [MonoidHom.finsetProd_apply, MonoidHom.finsetProd_apply]
  change _ = (M.act σ).toMonoidHom _
  rw [map_prod]
  exact (Fintype.prod_equiv (Equiv.mulLeft σ) _ _ (fun g => (retrTerm_equivariant M f u σ g w).symm)).symm

theorem univ_perm_three : (Finset.univ : Finset (Perm (Fin 3))) =
    {1, s3d, s3d * s3d, s3t, s3t * s3d, s3t * s3d * s3d} := by decide +kernel

theorem s3d_inv : s3d⁻¹ = s3d * s3d := by decide +kernel

theorem s3t_inv : s3t⁻¹ = s3t := by decide +kernel

theorem s3td_inv : (s3t * s3d)⁻¹ = s3d * s3d * s3t := by decide +kernel

theorem s3tdd_inv : (s3t * s3d * s3d)⁻¹ = s3d * s3t := by decide +kernel

theorem s3dd_inv : (s3d * s3d)⁻¹ = s3d := by decide +kernel

theorem retr_apply_u (M : Model 3) (f : M.W →* Multiplicative (ZMod 2)) {u : M.W}
    (hf : f u = Multiplicative.ofAdd 1) (hut : M.act s3t u = u)
    (hrel : M.act s3d (M.act s3d u) = u * M.act s3d u) :
    (∏ g, retrTerm M f u g) u = u := by
  have hsq := M.sq
  set v := M.act s3d u with hv
  have hdv : M.act s3d v = u * v := hrel
  have hduv : M.act s3d (u * v) = u := by
    rw [map_mul, hdv, mul_left_comm, hsq, mul_one]
  have htv : M.act s3t v = u * v := by
    rw [hv, s3_act_t_d, hut, hrel]
  have htuv : M.act s3t (u * v) = v := by
    rw [map_mul, hut, htv, ← mul_assoc, hsq, one_mul]
  have hfuv : f (u * v) = Multiplicative.ofAdd 1 * f v := by rw [map_mul, hf]
  have ad' : M.act s3d⁻¹ u = u * v := by rw [s3d_inv, act_mul_apply, hrel]
  have add : M.act (s3d * s3d) u = u * v := by rw [act_mul_apply, hrel]
  have add' : M.act (s3d * s3d)⁻¹ u = v := by rw [s3dd_inv]
  have at' : M.act s3t⁻¹ u = u := by rw [s3t_inv, hut]
  have atd : M.act (s3t * s3d) u = u * v := by rw [act_mul_apply, htv]
  have atd' : M.act (s3t * s3d)⁻¹ u = u * v := by
    rw [s3td_inv, act_mul_apply, act_mul_apply, hut, hrel]
  have atdd : M.act (s3t * s3d * s3d) u = v := by
    rw [act_mul_apply, act_mul_apply, hrel, htuv]
  have atdd' : M.act (s3t * s3d * s3d)⁻¹ u = v := by
    rw [s3tdd_inv, act_mul_apply, hut]
  have hfv : f v = Multiplicative.ofAdd 0 ∨ f v = Multiplicative.ofAdd 1 := by
    have : ∀ z : Multiplicative (ZMod 2), z = Multiplicative.ofAdd 0 ∨ z = Multiplicative.ofAdd 1 := by
      decide
    exact this _
  rw [MonoidHom.finsetProd_apply, univ_perm_three,
    Finset.prod_insert (by decide +kernel), Finset.prod_insert (by decide +kernel),
    Finset.prod_insert (by decide +kernel), Finset.prod_insert (by decide +kernel),
    Finset.prod_insert (by decide +kernel), Finset.prod_singleton]
  simp only [retrTerm_apply, map_one, inv_one, ad', add, add', at', atd, atd', atdd, atdd', hut,
    MulAut.one_apply, hf, hfuv, ← hv]
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  rcases hfv with h | h
  · simp only [h, toAdd_mul, toAdd_ofAdd, add_zero, ZMod.val_zero, ZMod.val_one, pow_zero, pow_one,
      mul_one, one_mul]
    calc _ = u * ((u * u) * (v * v)) := by ac_rfl
      _ = u := by rw [hsq u, hsq v, one_mul, mul_one]
  · simp only [h, toAdd_mul, toAdd_ofAdd, h11, ZMod.val_zero, ZMod.val_one, pow_zero, pow_one,
      one_mul]
    calc _ = u * ((u * u) * (v * v)) := by ac_rfl
      _ = u := by rw [hsq u, hsq v, one_mul, mul_one]

theorem exists_retraction (M : Model 3) {S : Subgroup M.W} (hS : IsInvSub M ⊤ S) {u : M.W}
    (huS : u ∈ S) (hu1 : u ≠ 1) (hut : M.act s3t u = u)
    (hrel : M.act s3d (M.act s3d u) = u * M.act s3d u) :
    ∃ π : M.W →* M.W, (∀ σ w, π (M.act σ w) = M.act σ (π w)) ∧ π u = u ∧ ∀ w, π w ∈ S := by
  obtain ⟨f, hf⟩ := exists_hom_ne_one M.sq hu1
  have hf1 : f u = Multiplicative.ofAdd 1 := by
    have : ∀ z : Multiplicative (ZMod 2), z ≠ 1 → z = Multiplicative.ofAdd 1 := by decide
    exact this _ hf
  refine ⟨∏ g, retrTerm M f u g, retr_equivariant M f u, retr_apply_u M f hf1 hut hrel, fun w => ?_⟩
  rw [MonoidHom.finsetProd_apply]
  refine Subgroup.prod_mem _ fun g _ => ?_
  rw [retrTerm_apply]
  exact Subgroup.pow_mem _ (hS g (Subgroup.mem_top g) u huS) _

theorem exists_compl_of_retraction (M : Model 3) {U : Subgroup M.W} (π : M.W →* M.W)
    (hπ : ∀ σ w, π (M.act σ w) = M.act σ (π w)) (hπU : ∀ w ∈ U, π w = w)
    (hπS : ∀ w, π w ∈ U) : ∃ U' : Subgroup M.W, IsInvSub M ⊤ U' ∧ IsCompl U U' := by
  refine ⟨π.ker, ?_, ?_, ?_⟩
  · intro σ _ w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    rw [hπ, hw, map_one]
  · rw [Subgroup.disjoint_def]
    intro x hxU hxK
    rw [← hπU x hxU]
    exact MonoidHom.mem_ker.mp hxK
  · rw [codisjoint_iff, eq_top_iff]
    intro w _
    rw [Subgroup.mem_sup]
    refine ⟨π w, hπS w, (π w)⁻¹ * w, ?_, by simp⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπU _ (hπS w), inv_mul_cancel]

theorem frame_map {M N : Model 3} (e : M.Iso N) {u : M.W} (h : S3Frame M u) :
    S3Frame N (e.toMulEquiv u) where
  fix_t := by rw [← e.map_act, h.fix_t]
  ne_one := fun h1 => h.ne_one (e.toMulEquiv.injective (by rw [h1, map_one]))
  d_ne := fun h1 => h.d_ne (e.toMulEquiv.injective (by rw [e.map_act, h1]))
  rel := by rw [← e.map_act, ← e.map_act, h.rel, map_mul, e.map_act]
  span := fun w => by
    obtain ⟨x, rfl⟩ := e.toMulEquiv.surjective w
    rcases h.span x with rfl | rfl | rfl | rfl
    · left; exact map_one _
    · right; left; rfl
    · right; right; left; exact e.map_act s3d u
    · right; right; right; rw [map_mul, e.map_act]

theorem exists_frame_of_card_four (M : Model 3) (hcard : Nat.card M.W = 4)
    (hfaith : ∀ σ : Perm (Fin 3), (∀ w : M.W, M.act σ w = w) → σ = 1) :
    ∃ u : M.W, S3Frame M u := by
  have hA : fixW M (alternatingGroup (Fin 3)) ≠ ⊤ := by
    intro h
    exact s3d_ne_one (hfaith s3d ((fixW_A3_eq_top_iff M).mp h))
  have hidx : (fixW M S3Syl).index ≤ 2 := by
    obtain ⟨w, hw⟩ : ∃ w : M.W, w ≠ 1 := by
      by_contra h
      push Not at h
      have : Subsingleton M.W := ⟨fun a b => by rw [h a, h b]⟩
      have := Nat.card_of_subsingleton (1 : M.W)
      omega
    obtain ⟨v, hv1, hvt⟩ := exists_fixed_t M hw
    have hv : v ∈ fixW M S3Syl := by rw [S3Syl_eq]; exact (mem_fixW_zpowers M).mpr hvt
    have h2 : 1 < Nat.card (fixW M S3Syl) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr
        ((Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨v, hv⟩, fun h => hv1 (congrArg Subtype.val h)⟩)
    have h3 := Subgroup.card_mul_index (fixW M S3Syl)
    have h4 : 0 < (fixW M S3Syl).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    by_contra h5
    push Not at h5
    have : 2 * 3 ≤ Nat.card (fixW M S3Syl) * (fixW M S3Syl).index := Nat.mul_le_mul h2 h5
    omega
  obtain ⟨hU, hcompl, ⟨e⟩, hfix⟩ := s3_lemma30 M hA hidx
  have hR : commW M (alternatingGroup (Fin 3)) ⊤ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h4 := Nat.card_congr e.toMulEquiv.toEquiv
    rw [nat3_card] at h4
    rw [hcard]
    exact h4
  have hC : fixW M ⊤ = ⊥ := by
    rw [← hfix]
    rw [hR] at hcompl
    exact top_disjoint.mp hcompl.disjoint
  obtain ⟨e'⟩ := s3_lemma30_natural M hA hidx hC
  obtain ⟨u₂, hu₂⟩ := exists_frame_nat3
  exact ⟨e'.symm.toMulEquiv u₂, frame_map e'.symm hu₂⟩

theorem model3_exists_compl (M : Model 3) {U : Subgroup M.W} (hU : IsInvSub M ⊤ U)
    (hcard : Nat.card U = 4)
    (hfaith : ∀ σ : Perm (Fin 3), (∀ w ∈ U, M.act σ w = w) → σ = 1) :
    ∃ U' : Subgroup M.W, IsInvSub M ⊤ U' ∧ IsCompl U U' := by
  obtain ⟨u₀, h⟩ : ∃ u₀ : U, S3Frame (M.restrict U hU) u₀ :=
    exists_frame_of_card_four (M.restrict U hU) hcard
      (fun σ hσ => hfaith σ fun w hw => congrArg Subtype.val (hσ ⟨w, hw⟩))
  set u : M.W := (u₀ : M.W) with hu
  have hut : M.act s3t u = u := congrArg Subtype.val h.fix_t
  have hrel : M.act s3d (M.act s3d u) = u * M.act s3d u := congrArg Subtype.val h.rel
  have hu1 : u ≠ 1 := fun h1 => h.ne_one (Subtype.ext h1)
  have hspan : ∀ w ∈ U, w = 1 ∨ w = u ∨ w = M.act s3d u ∨ w = u * M.act s3d u := by
    intro w hw
    rcases h.span ⟨w, hw⟩ with h1 | h1 | h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (Or.inl (congrArg Subtype.val h1))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h1)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h1)))
  obtain ⟨π, hπ, hπu, hπS⟩ := exists_retraction M hU u₀.2 hu1 hut hrel
  have hπd : π (M.act s3d u) = M.act s3d u := by rw [hπ, hπu]
  refine exists_compl_of_retraction M π hπ (fun w hw => ?_) hπS
  rcases hspan w hw with rfl | rfl | rfl | rfl
  · exact map_one _
  · exact hπu
  · exact hπd
  · rw [map_mul, hπu, hπd]

section Group

variable {G : Type} [Group G]

@[expose] def conjActK (X K : Subgroup G) (hN : X ≤ Subgroup.normalizer (K : Set G)) :
    ↥X →* MulAut ↥K where
  toFun x :=
    { toFun := fun z =>
        ⟨(x : G) * z * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hN x.2) z).mp z.2⟩
      invFun := fun z => ⟨(x : G)⁻¹ * z * (x : G), by
        have := (Subgroup.mem_normalizer_iff.mp (hN (X.inv_mem x.2)) z).mp z.2
        simpa using this⟩
      left_inv := fun z => Subtype.ext (by simp [mul_assoc])
      right_inv := fun z => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun z => Subtype.ext (by simp)
  map_mul' := fun a b => MulEquiv.ext fun z => Subtype.ext (by simp [mul_assoc])

theorem isElemAbelian_comm' {K : Subgroup G} (hK : CFSG.Open.IsElemAbelian 2 K) {x y : G}
    (hx : x ∈ K) (hy : y ∈ K) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hK hx hy

@[expose] noncomputable def kModel [Finite G] (X K : Subgroup G) (hN : X ≤ Subgroup.normalizer (K : Set G))
    (hK : CFSG.Open.IsElemAbelian 2 K) (ψ : ↥X →* Perm (Fin 3)) (hψ : Function.Surjective ψ)
    (hker : ∀ x : ↥X, ψ x = 1 → ∀ z ∈ K, (x : G) * z * (x : G)⁻¹ = z) : Model 3 where
  W := ↥K
  grp := { (inferInstance : Group ↥K) with
    mul_comm := fun a b => Subtype.ext (isElemAbelian_comm' hK a.2 b.2) }
  fin := inferInstance
  act := MonoidHom.liftOfRightInverse ψ (Function.surjInv hψ) (Function.rightInverse_surjInv hψ)
    ⟨conjActK X K hN, fun x hx => MulEquiv.ext fun z => Subtype.ext (hker x hx z z.2)⟩
  sq := fun w => Subtype.ext (by
    have := hK.2 w w.2
    simpa [pow_two] using this)

theorem coe_kModel_act [Finite G] (X K : Subgroup G) (hN : X ≤ Subgroup.normalizer (K : Set G))
    (hK : CFSG.Open.IsElemAbelian 2 K) (ψ : ↥X →* Perm (Fin 3)) (hψ : Function.Surjective ψ)
    (hker : ∀ x : ↥X, ψ x = 1 → ∀ z ∈ K, (x : G) * z * (x : G)⁻¹ = z) (x : ↥X) (w : ↥K) :
    ((show ↥K from (kModel X K hN hK ψ hψ hker).act (ψ x) w : ↥K) : G) =
      (x : G) * (w : G) * (x : G)⁻¹ := by
  show ((MonoidHom.liftOfRightInverse ψ (Function.surjInv hψ) (Function.rightInverse_surjInv hψ)
    ⟨conjActK X K hN, _⟩) (ψ x) w : G) = _
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

theorem exists_normal_complement_nat3 [Finite G]
    (X Q K Z : Subgroup G) (ψ : ↥X →* Equiv.Perm (Fin 3)) (hψ : Function.Surjective ψ)
    (hker : ∀ x : ↥X, ψ x = 1 ↔ (x : G) ∈ Q)
    (hK : CFSG.Open.IsElemAbelian 2 K) (hXK : X ≤ Subgroup.normalizer (K : Set G))
    (hQK : Q ≤ Subgroup.centralizer (K : Set G)) (hZK : Z ≤ K)
    (hXZ : X ≤ Subgroup.normalizer (Z : Set G)) (hZcard : Nat.card Z = 4)
    (hZfaith : ∀ x ∈ X, (∀ z ∈ Z, x * z * x⁻¹ = z) → x ∈ Q) :
    ∃ K' : Subgroup G, K' ≤ K ∧ X ≤ Subgroup.normalizer (K' : Set G) ∧ Z ⊓ K' = ⊥ ∧
      Z ⊔ K' = K := by
  have hker' : ∀ x : ↥X, ψ x = 1 → ∀ z ∈ K, (x : G) * z * (x : G)⁻¹ = z := by
    intro x hx z hz
    have h := Subgroup.mem_centralizer_iff.mp (hQK ((hker x).mp hx)) z hz
    rw [mul_inv_eq_iff_eq_mul]
    exact h.symm
  let M := kModel X K hXK hK ψ hψ hker'
  let U : Subgroup ↥K := Z.subgroupOf K
  have hact : ∀ (x : ↥X) (w : ↥K), (Subtype.val (M.act (ψ x) w : ↥K) : G) =
      (x : G) * (w : G) * (x : G)⁻¹ :=
    fun x w => coe_kModel_act X K hXK hK ψ hψ hker' x w
  have hU : IsInvSub M ⊤ U := by
    intro σ _ w hw
    obtain ⟨x, rfl⟩ := hψ σ
    show (Subtype.val (M.act (ψ x) w : ↥K) : G) ∈ Z
    exact (congrArg (· ∈ Z) (hact x w)).mpr ((Subgroup.mem_normalizer_iff.mp (hXZ x.2) _).mp hw)
  have hcard : Nat.card U = 4 := by
    rw [← hZcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv
  have hfaith : ∀ σ : Perm (Fin 3), (∀ w ∈ U, M.act σ w = w) → σ = 1 := by
    intro σ hσ
    obtain ⟨x, rfl⟩ := hψ σ
    rw [hker]
    refine hZfaith x x.2 fun z hz => ?_
    have := congrArg Subtype.val (hσ ⟨z, hZK hz⟩ hz)
    rw [hact] at this
    exact this
  obtain ⟨U', hU'inv, hcompl⟩ : ∃ U' : Subgroup ↥K, IsInvSub M ⊤ U' ∧ IsCompl U U' :=
    model3_exists_compl M hU hcard hfaith
  have hZmap : U.map K.subtype = Z := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hZK
  have hinj : Function.Injective K.subtype := Subtype.val_injective
  refine ⟨U'.map K.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨w, -, rfl⟩
    exact w.2
  · intro x hx
    have key : ∀ y ∈ X, ∀ k ∈ U'.map K.subtype, y * k * y⁻¹ ∈ U'.map K.subtype := by
      rintro y hy _ ⟨w, hw, rfl⟩
      refine ⟨M.act (ψ ⟨y, hy⟩) w, hU'inv _ (Subgroup.mem_top _) w hw, ?_⟩
      exact hact ⟨y, hy⟩ w
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key x hx h hh, fun hh => ?_⟩
    have := key x⁻¹ (X.inv_mem hx) _ hh
    simpa [mul_assoc] using this
  · rw [← hZmap, ← Subgroup.map_inf_eq _ _ _ hinj, hcompl.inf_eq_bot, Subgroup.map_bot]
  · rw [← hZmap, ← Subgroup.map_sup, hcompl.sup_eq_top, Subgroup.map_top, Subgroup.range_subtype]

end Group

end CFSG.Quasithin.F53.Stellmacher
