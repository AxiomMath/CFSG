module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
public import CFSG.Quasithin.Vol2.GoldschmidtKGHatA6F4

public section

namespace CFSG.Quasithin.H13

open CFSG.Fischer CFSG.Quasithin.Vol2.KGHat

section F4Model

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem neg_eq_self_zmod2 (w : W) : -w = w := by
  have h : (-1 : ZMod 2) = 1 := by decide
  calc -w = (-1 : ZMod 2) • w := (neg_one_smul _ w).symm
    _ = w := by rw [h, one_smul]

theorem add_self_zmod2 (w : W) : w + w = 0 := by
  rw [← two_smul (ZMod 2) w]
  have h : (2 : ZMod 2) = 0 := by decide
  rw [h, zero_smul]

theorem sq_eq_add_one [Finite W] (hW : Nat.card W = 2 ^ 6) {Γ : Type} [Group Γ]
    (hΓ : Group.IsPerfect Γ) (ρ : Γ →* (W →ₗ[ZMod 2] W)) (z₀ : Γ)
    (hcomm : ∀ γ w, ρ γ (ρ z₀ w) = ρ z₀ (ρ γ w))
    (h3 : ∀ w, ρ z₀ (ρ z₀ (ρ z₀ w)) = w) (hne : ∃ w, ρ z₀ w ≠ w) :
    ∀ w, ρ z₀ (ρ z₀ w) = ρ z₀ w + w := by
  set z : W →ₗ[ZMod 2] W := ρ z₀ with hzdef
  let p : W →ₗ[ZMod 2] W := z ∘ₗ z + z + LinearMap.id
  let W₀ : Submodule (ZMod 2) W := LinearMap.ker p
  have hmemW₀ : ∀ w, w ∈ W₀ ↔ z (z w) + z w + w = 0 := fun w => Iff.rfl
  have hinv : ∀ γ : Γ, ∀ w ∈ W₀, ρ γ w ∈ W₀ := by
    intro γ w hw
    rw [hmemW₀] at hw ⊢
    have h := congrArg (ρ γ) hw
    rw [map_add, map_add, map_zero, hcomm γ (z w), hcomm γ w] at h
    exact h
  have hz' : ∀ w ∈ W₀, z (z w) = z w + w := by
    intro w hw
    rw [hmemW₀] at hw
    have h : z (z w) = -(z w + w) := eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact hw)
    rw [h, neg_eq_self_zmod2]
  obtain ⟨w₁, hw₁⟩ := hne
  have hu : z w₁ + w₁ ∈ W₀ := by
    rw [hmemW₀]
    have e1 : z (z w₁ + w₁) = z (z w₁) + z w₁ := map_add z _ _
    have e2 : z (z (z w₁ + w₁)) = w₁ + z (z w₁) := by rw [e1, map_add, h3]
    rw [e2, e1]
    have e3 : (w₁ + z (z w₁)) + (z (z w₁) + z w₁) + (z w₁ + w₁) =
        (w₁ + w₁) + (z (z w₁) + z (z w₁)) + (z w₁ + z w₁) := by abel
    rw [e3]
    simp [add_self_zmod2]
  have hu0 : z w₁ + w₁ ≠ 0 := fun h => by
    have h' : z w₁ = -w₁ := eq_neg_of_add_eq_zero_left h
    exact hw₁ (by rw [h', neg_eq_self_zmod2])
  let z' : W₀ →ₗ[ZMod 2] W₀ := z.restrict (fun w hw => hinv z₀ w hw)
  have hzz' : ∀ x : W₀, z' (z' x) = z' x + x := fun x => Subtype.ext (hz' x x.2)
  let α' : Γ →* (W₀ →ₗ[ZMod 2] W₀) :=
    { toFun := fun γ => (ρ γ).restrict (fun w hw => hinv γ w hw)
      map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
      map_mul' := fun γ δ => LinearMap.ext fun x => Subtype.ext (by simp) }
  have hα' : ∀ γ x, α' γ (z' x) = z' (α' γ x) := fun γ x => Subtype.ext (hcomm γ x)
  have hdvd := three_dvd_finrank z' hzz' hΓ α' hα' z₀ (fun x => rfl)
  have hcard : Nat.card W₀ = 4 ^ Module.finrank F4 (F4Space z' hzz') := natCard_F4Space z' hzz'
  have hd1 : 1 ≤ Module.finrank F4 (F4Space z' hzz') := by
    by_contra hlt
    have h0 : Module.finrank F4 (F4Space z' hzz') = 0 := by omega
    rw [h0, pow_zero] at hcard
    have hsub : Subsingleton W₀ := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact hu0 (congrArg Subtype.val (Subsingleton.elim (⟨z w₁ + w₁, hu⟩ : W₀) 0))
  have hd3 : 3 ≤ Module.finrank F4 (F4Space z' hzz') := Nat.le_of_dvd (by omega) hdvd
  have hcard64 : 64 ≤ Nat.card W₀ := by
    rw [hcard]
    calc (64 : ℕ) = 4 ^ 3 := by norm_num
      _ ≤ 4 ^ Module.finrank F4 (F4Space z' hzz') := Nat.pow_le_pow_right (by norm_num) hd3
  have hle : Nat.card W₀ ≤ Nat.card W := Nat.card_le_card_of_injective _ Subtype.val_injective
  have htop : W₀.toAddSubgroup = ⊤ :=
    (AddSubgroup.card_eq_iff_eq_top W₀.toAddSubgroup).mp (by
      have : Nat.card W₀.toAddSubgroup = Nat.card W₀ := rfl
      omega)
  intro w
  exact hz' w (by
    have : w ∈ W₀.toAddSubgroup := by rw [htop]; exact AddSubgroup.mem_top w
    exact this)

theorem exists_f4_model [Finite W] (hW : Nat.card W = 2 ^ 6) {Γ : Type} [Group Γ]
    (hΓ : Group.IsPerfect Γ) (ρ : Γ →* (W →ₗ[ZMod 2] W)) (hρ : Function.Injective ρ)
    (hZ : Nat.card (Subgroup.center Γ) = 3) :
    ∃ (Φ : W ≃+ (Fin 3 → F4)) (μ : Γ →* Matrix.GeneralLinearGroup (Fin 3) F4),
      Function.Injective μ ∧
      (∀ γ, ((μ γ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1) ∧
      (∀ γ w, Φ (ρ γ w) =
        ((μ γ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).mulVec
          (Φ w)) ∧
      (∀ g ∈ Subgroup.center Γ, ∃ c : F4,
        ((μ g : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = c • 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic (Subgroup.center Γ) := isCyclic_of_prime_card hZ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Subgroup.center Γ)
  set z₀ : Γ := (g : Γ) with hz₀def
  have hz₀c : z₀ ∈ Subgroup.center Γ := g.2
  have hord : orderOf z₀ = 3 := by
    rw [hz₀def, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hZ]
  have hz₀3 : z₀ ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one z₀
  have hz₀ne : z₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hord; omega
  have hcomm : ∀ γ w, ρ γ (ρ z₀ w) = ρ z₀ (ρ γ w) := fun γ w => by
    have h := Subgroup.mem_center_iff.mp hz₀c γ
    have h2 : ρ γ * ρ z₀ = ρ z₀ * ρ γ := by rw [← map_mul, ← map_mul, h]
    exact LinearMap.congr_fun h2 w
  have h3 : ∀ w, ρ z₀ (ρ z₀ (ρ z₀ w)) = w := fun w => by
    have h : z₀ * (z₀ * z₀) = 1 := by rw [← pow_three]; exact hz₀3
    have h2 : ρ z₀ * (ρ z₀ * ρ z₀) = 1 := by rw [← map_mul, ← map_mul, h, map_one]
    exact LinearMap.congr_fun h2 w
  have hne : ∃ w, ρ z₀ w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hz₀ne (hρ (by rw [map_one]; exact LinearMap.ext hcon))
  have hzl := sq_eq_add_one hW hΓ ρ z₀ hcomm h3 hne
  let z : W →ₗ[ZMod 2] W := ρ z₀
  let X := F4Space z hzl
  have hcardX : Nat.card X = 4 ^ Module.finrank F4 X := natCard_F4Space z hzl
  have hd : Module.finrank F4 X = 3 := by
    have h1 : Nat.card X = 2 ^ 6 := by rw [← hW]; exact Nat.card_congr (Equiv.refl _)
    have h2 : (4 : ℕ) ^ Module.finrank F4 X = 4 ^ 3 := by rw [← hcardX, h1]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) h2
  have : Module.Finite F4 X := Module.Finite.of_finite
  let b : Module.Basis (Fin 3) F4 X := Module.finBasisOfFinrankEq F4 X hd
  let f : Γ →* (X →ₗ[F4] X) := f4Action z hzl ρ hcomm
  let μ₀ : Γ →* Matrix (Fin 3) (Fin 3) F4 :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom.comp f
  have hμ₀ : ∀ γ, μ₀ γ = LinearMap.toMatrix b b (f γ) := fun γ => rfl
  let μ : Γ →* Matrix.GeneralLinearGroup (Fin 3) F4 := μ₀.toHomUnits
  have hμ : ∀ γ, ((μ γ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      μ₀ γ := fun γ => rfl
  let eW : W ≃+ X :=
    { toFun := fun w => F4Space.mk z hzl w
      invFun := fun x => F4Space.val z hzl x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let Φ : W ≃+ (Fin 3 → F4) := eW.trans b.equivFun.toAddEquiv
  have hequiv : ∀ γ w, Φ (ρ γ w) = (μ₀ γ).mulVec (Φ w) := by
    intro γ w
    show b.equivFun (F4Space.mk z hzl (ρ γ w)) =
      (LinearMap.toMatrix b b (f γ)).mulVec (b.equivFun (F4Space.mk z hzl w))
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
    rfl
  have hμz₀ : μ₀ z₀ = F4.ω • (1 : Matrix (Fin 3) (Fin 3) F4) := by
    rw [hμ₀, f4Action_eq_omega_smul z hzl ρ hcomm z₀ (fun x => rfl)]
    rw [map_smul, LinearMap.toMatrix_id]
  refine ⟨Φ, μ, ?_, ?_, ?_, ?_⟩
  · intro γ δ h
    have h1 : μ₀ γ = μ₀ δ := by
      have := congrArg (fun u : Matrix.GeneralLinearGroup (Fin 3) F4 =>
        (u : Matrix (Fin 3) (Fin 3) F4)) h
      simpa [hμ] using this
    have h2 : f γ = f δ := (LinearMap.toMatrixAlgEquiv b).injective h1
    apply hρ
    refine LinearMap.ext fun w => ?_
    exact congrArg (fun F : X →ₗ[F4] X => F4Space.val z hzl (F (F4Space.mk z hzl w))) h2
  · intro γ
    rw [hμ, hμ₀, LinearMap.det_toMatrix]
    exact det_f4Action_eq_one z hzl hΓ ρ hcomm γ
  · intro γ w
    rw [hμ]
    exact hequiv γ w
  · intro c hcc
    have hfin : IsOfFinOrder z₀ := orderOf_pos_iff.mp (by rw [hord]; norm_num)
    have hmem : c ∈ Submonoid.powers z₀ := by
      rw [hfin.mem_powers_iff_mem_zpowers]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨c, hcc⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp hmem
    refine ⟨F4.ω ^ n, ?_⟩
    rw [hμ, ← hn, map_pow, hμz₀, smul_pow, one_pow]

end F4Model

section Additive

variable {V : Type} [CommGroup V]

@[reducible, expose] def zmod2ModuleOfExp (hV2 : ∀ v : V, v ^ 2 = 1) :
    Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule (fun x => by
    have h : (2 : ℕ) • x = Additive.ofMul (Additive.toMul x ^ 2) := rfl
    rw [h, hV2]
    rfl)

variable [Module (ZMod 2) (Additive V)]

@[expose] def autLin (f : MulAut V) : Additive V →ₗ[ZMod 2] Additive V :=
  (MulEquiv.toAdditive f).toAddMonoidHom.toZModLinearMap 2

theorem autLin_apply (f : MulAut V) (v : V) :
    autLin f (Additive.ofMul v) = Additive.ofMul (f v) := rfl

@[expose] def linAutHom : MulAut V →* (Additive V →ₗ[ZMod 2] Additive V) where
  toFun := autLin
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

theorem linAutHom_injective : Function.Injective (linAutHom (V := V)) := fun _ _ h =>
  MulEquiv.ext fun v => Additive.ofMul.injective (LinearMap.congr_fun h (Additive.ofMul v))

end Additive

theorem realizes_nat_range {V : Type} [CommGroup V] (H : Subgroup (MulAut V)) {K : Type} [Field K]
    (Φ : V ≃* Multiplicative (Fin 3 → K)) (μ : ↥H →* Matrix.GeneralLinearGroup (Fin 3) K)
    (hμ : Function.Injective μ)
    (hequiv : ∀ (h : ↥H) (v : V), Φ ((h : MulAut V) v) =
      Multiplicative.ofAdd (((μ h : Matrix.GeneralLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).mulVec (Multiplicative.toAdd (Φ v)))) :
    (FFModel.nat μ.range).Realizes H ⊤ ⊥ := by
  let e : ↥H ≃* ↥μ.range := MonoidHom.ofInjective hμ
  have he : ∀ h : ↥H, ((e h : ↥μ.range) : Matrix.GeneralLinearGroup (Fin 3) K) = μ h :=
    fun h => rfl
  dsimp only [FFModel.Realizes, FFModel.RealizesVia, FFModel.nat]
  refine ⟨e.symm.toMonoidHom, e.symm.surjective, bot_le, bot_le, fun _ _ _ => Subgroup.mem_top _,
    ?_, fun _ _ _ => Subgroup.mem_top _, ?_, ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ m hm
    have hm1 : m = 1 := Subgroup.mem_bot.mp hm
    rw [Subgroup.mem_bot, hm1]
    simp [natAct]
  · refine ⟨(QuotientGroup.mk' _).comp
      ((Φ.toMonoidHom.comp (⊤ : Subgroup V).subtype).codRestrict _
        (fun _ => Subgroup.mem_top _)), ?_, ?_, ?_⟩
    · intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨⟨Φ.symm (m : Multiplicative (Fin 3 → K)), Subgroup.mem_top _⟩, ?_⟩
      show QuotientGroup.mk _ = QuotientGroup.mk m
      exact congrArg QuotientGroup.mk (Subtype.ext (Φ.apply_symm_apply _))
    · intro u
      show QuotientGroup.mk _ = (1 : _ ⧸ _) ↔ _
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subgroup.mem_bot]
      exact map_eq_one_iff Φ Φ.injective
    · intro γ u m hu hm hβ
      have hβ' := QuotientGroup.eq.mp hβ
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hβ'
      have hm' : (m : Multiplicative (Fin 3 → K)) = Φ (u : V) := by
        have : (Φ (u : V))⁻¹ * (m : Multiplicative (Fin 3 → K)) = 1 := hβ'
        exact (inv_mul_eq_one.mp this).symm
      show QuotientGroup.mk _ = QuotientGroup.mk _
      refine congrArg QuotientGroup.mk (Subtype.ext ?_)
      show Φ (((e.symm γ : ↥H) : MulAut V) (u : V)) =
        natAct μ.range γ (m : Multiplicative (Fin 3 → K))
      rw [hm', hequiv (e.symm γ) (u : V)]
      have hγ : γ = e (e.symm γ) := (e.apply_symm_apply γ).symm
      show _ = Multiplicative.ofAdd ((((γ : ↥μ.range) : Matrix.GeneralLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).mulVec _)
      rw [hγ, he]
      simp

theorem alt6_noncomm : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra h
  push Not at h
  let : CommGroup (alternatingGroup (Fin 6)) :=
    { (inferInstance : Group (alternatingGroup (Fin 6))) with mul_comm := h }
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  have hp := IsSimpleGroup.prime_card (α := alternatingGroup (Fin 6))
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 6)), Fintype.card_perm,
    Fintype.card_fin] at h2
  have h6 : (6 : ℕ).factorial = 720 := by decide
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by omega
  rw [h360] at hp
  exact absurd hp (by norm_num)

theorem isHat_alt6 {X : Type} [Group X] (hp : Group.IsPerfect X)
    (hZ : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) :
    IsHat X (alternatingGroup (Fin 6)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  refine ⟨⟨hp, e.isSimpleGroup, ?_⟩, hZ, ⟨e⟩⟩
  obtain ⟨x, y, hxy⟩ := alt6_noncomm
  refine ⟨e.symm x, e.symm y, fun h => hxy ?_⟩
  have h' := congrArg e h
  simpa using h'

theorem isHat_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {S : Type} [Group S]
    (h : IsHat X S) : IsHat Y S := by
  obtain ⟨hq, hZ, ⟨f⟩⟩ := h
  have hc : (Subgroup.center X).map (e : X →* Y) = Subgroup.center Y :=
    Subgroup.map_center_eq e
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_,
    ⟨(QuotientGroup.congr _ _ e hc).symm.trans f⟩⟩
  rw [← hZ, ← hc]
  exact Subgroup.card_map_of_injective e.injective

theorem hatA6SixModel : HatA6SixModel := by
  intro V _ _ hV2 hV H hperf hZ he
  let : Module (ZMod 2) (Additive V) := zmod2ModuleOfExp hV2
  have : Finite (Additive V) := Finite.of_equiv V Additive.ofMul
  have hW : Nat.card (Additive V) = 2 ^ 6 := by
    rw [← hV]
    exact Nat.card_congr Additive.toMul
  let ρ : ↥H →* (Additive V →ₗ[ZMod 2] Additive V) := linAutHom.comp H.subtype
  have hρ : Function.Injective ρ := fun a b h => Subtype.ext (linAutHom_injective h)
  obtain ⟨Φ, μ, hμ, hdet, hequiv, hcent⟩ := exists_f4_model hW hperf ρ hρ hZ
  let Φ' : V ≃* Multiplicative (Fin 3 → F4) :=
    { toFun := fun v => Multiplicative.ofAdd (Φ (Additive.ofMul v))
      invFun := fun x => Additive.toMul (Φ.symm (Multiplicative.toAdd x))
      left_inv := fun v => by simp
      right_inv := fun x => by simp
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (Φ (Additive.ofMul (a * b))) =
          Multiplicative.ofAdd (Φ (Additive.ofMul a)) * Multiplicative.ofAdd (Φ (Additive.ofMul b))
        rw [ofMul_mul, map_add]
        rfl }
  have hequiv' : ∀ (h : ↥H) (v : V), Φ' ((h : MulAut V) v) =
      Multiplicative.ofAdd (((μ h : Matrix.GeneralLinearGroup (Fin 3) F4) :
        Matrix (Fin 3) (Fin 3) F4).mulVec (Multiplicative.toAdd (Φ' v))) :=
    fun h v => congrArg Multiplicative.ofAdd (hequiv h (Additive.ofMul v))
  let e : ↥H ≃* ↥μ.range := MonoidHom.ofInjective hμ
  have hc : (Subgroup.center ↥H).map (e : ↥H →* ↥μ.range) = Subgroup.center ↥μ.range :=
    Subgroup.map_center_eq e
  refine ⟨F4, inferInstance, inferInstance, μ.range, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, F4.card]
  · rintro _ ⟨γ, rfl⟩
    exact hdet γ
  · exact isHat_of_mulEquiv e (isHat_alt6 hperf hZ he.some)
  · intro g hg
    rw [← hc] at hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    exact hcent γ hγ
  · exact realizes_nat_range H Φ' μ hμ hequiv'

end CFSG.Quasithin.H13
