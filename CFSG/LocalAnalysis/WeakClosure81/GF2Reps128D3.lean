module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2PTenR
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.GLTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.ActionOnSub

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
open scoped Matrix MatrixGroups TensorProduct

theorem w4t_tensor_dvd_of_card_dvd {n f : ℕ} (hn : 1 ≤ n)
    (h : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 2 ^ f * ((2 ^ f) ^ 2 - 1)) : n ∣ f := by
  have h1 : (2 ^ n) ^ 2 - 1 ∣ 2 ^ f * ((2 ^ f) ^ 2 - 1) := (Dvd.intro_left _ rfl).trans h
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    refine Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) ?_ odd_one
    rw [← pow_mul, Nat.even_pow]
    exact ⟨even_two, by omega⟩
  have hcop : Nat.Coprime ((2 ^ n) ^ 2 - 1) (2 ^ f) :=
    Nat.Coprime.pow_right f (Nat.coprime_two_right.mpr hodd)
  have h2 : (2 ^ n) ^ 2 - 1 ∣ (2 ^ f) ^ 2 - 1 := hcop.dvd_of_dvd_mul_left h1
  rw [← pow_mul, ← pow_mul] at h2
  have h3 := Nat.pow_sub_one_gcd_pow_sub_one 2 (n * 2) (f * 2)
  rw [Nat.gcd_eq_left h2] at h3
  have h4 : 2 ^ (n * 2) = 2 ^ Nat.gcd (n * 2) (f * 2) := by
    have := Nat.one_le_two_pow (n := n * 2)
    have := Nat.one_le_two_pow (n := Nat.gcd (n * 2) (f * 2))
    omega
  have h5 : n * 2 = Nat.gcd (n * 2) (f * 2) := Nat.pow_right_injective le_rfl h4
  have h6 : n * 2 ∣ f * 2 := by
    rw [h5]
    exact Nat.gcd_dvd_right _ _
  exact Nat.dvd_of_mul_dvd_mul_right two_pos h6

theorem w4t_tensor_exists_sl {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (b : Module.Basis (Fin 2) F V) {G : Type} [Group G] [Group.IsPerfect G]
    (ρ : G →* (V ≃ₗ[F] V)) (hρ : Function.Injective ρ) :
    ∃ R : G →* SL(2, F), Function.Injective R ∧
      ∀ g, ((R g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        LinearMap.toMatrix b b (ρ g : V →ₗ[F] V) := by
  let f : G →* GL (Fin 2) F := (basisGL b).comp ρ
  have hf : ∀ g, ((f g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      LinearMap.toMatrix b b (ρ g : V →ₗ[F] V) := fun g => coe_basisGL b (ρ g)
  let R : G →* SL(2, F) :=
    { toFun := fun g => ⟨(f g : Matrix (Fin 2) (Fin 2) F), det_eq_one_of_perfect f g⟩
      map_one' := Subtype.ext (show ((f 1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 by
        rw [map_one, Units.val_one])
      map_mul' := fun a c => Subtype.ext
        (show ((f (a * c) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          (f a : Matrix (Fin 2) (Fin 2) F) * (f c : Matrix (Fin 2) (Fin 2) F) by
        rw [map_mul, Units.val_mul]) }
  refine ⟨R, fun g g' h => hρ (basisGL_injective b (Units.ext ?_)), fun g => hf g⟩
  exact congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h

section Core

variable {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]

theorem w4t_tensor_core [Nontrivial Y] {K₁ K₂ : Subgroup (GLV Y)}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hirr : Offender.IsIrrAct (K₁ ⊔ K₂))
    {n : ℕ} (hn : 2 ≤ n) (e₁ : ↥K₁ ≃* SL(2, GaloisField 2 n)) {τ : GLV Y} (hτ : τ * τ = 1)
    (hτ1 : τ ≠ 1) (hτ₁ : ∀ x ∈ K₁, τ * x * τ ∈ K₂) (hτ₂ : ∀ y ∈ K₂, τ * y * τ ∈ K₁)
    (hDfix : ∀ k ∈ K₁, ∀ u ∈ LinearMap.range ((τ : Module.End (ZMod 2) Y) - 1),
      (k * (τ * k * τ)) u = u) :
    2 * n ≤ Module.finrank (ZMod 2) (LinearMap.range ((τ : Module.End (ZMod 2) Y) - 1)) ∨
      (Module.finrank (ZMod 2) (LinearMap.range ((τ : Module.End (ZMod 2) Y) - 1)) = n ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
          ∃ (φ₁ : ↥K₁ ≃* SL(2, F)) (φ₂ : ↥K₂ ≃* SL(2, F)) (A : Y ≃+ Matrix (Fin 2) (Fin 2) F),
            (∀ (g : ↥K₁) (v : Y),
              A ((g : GLV Y) v) = ((φ₁ g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * A v) ∧
            ∀ (g : ↥K₂) (v : Y),
              A ((g : GLV Y) v) = A v * ((φ₂ g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ) := by
  classical
  set R := LinearMap.range ((τ : Module.End (ZMod 2) Y) - 1) with hRdef
  have hGF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [hGF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : IsSimpleGroup SL(2, GaloisField 2 n) := P22y.isSimpleGroup_sl2 h4
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card (GaloisField 2 n) h4
  have : IsSimpleGroup ↥K₁ := e₁.isSimpleGroup
  have hper₁ : Group.IsPerfect ↥K₁ :=
    Group.IsPerfect.ofSurjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
  have hττ : ∀ x : GLV Y, τ * (τ * x * τ) * τ = x := fun x => by
    calc τ * (τ * x * τ) * τ = τ * τ * x * (τ * τ) := by group
      _ = x := by rw [hτ, one_mul, mul_one]
  have hconj : ∀ x x' : GLV Y, τ * (x * x') * τ = τ * x * τ * (τ * x' * τ) := fun x x' => by
    calc τ * (x * x') * τ = τ * x * 1 * x' * τ := by group
      _ = τ * x * τ * (τ * x' * τ) := by rw [← hτ]; group
  let e₂ : ↥K₂ ≃* ↥K₁ :=
    { toFun := fun y => ⟨τ * y * τ, hτ₂ y y.2⟩
      invFun := fun x => ⟨τ * x * τ, hτ₁ x x.2⟩
      left_inv := fun y => Subtype.ext (hττ y)
      right_inv := fun x => Subtype.ext (hττ x)
      map_mul' := fun y y' => Subtype.ext (hconj y y') }
  have : IsSimpleGroup ↥K₂ := e₂.isSimpleGroup
  have hper₂ : Group.IsPerfect ↥K₂ :=
    Group.IsPerfect.ofSurjective (f := e₂.symm.toMonoidHom) e₂.symm.surjective
  have hZ : ∀ {K : Subgroup (GLV Y)} [IsSimpleGroup ↥K], Group.IsPerfect ↥K →
      ∀ z : ↥K, (∀ x : ↥K, z * x = x * z) → z = 1 := by
    intro K _ hK z hz
    have := hK
    have hc : z ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.mpr fun g => (hz g).symm
    rwa [TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (Group.IsPerfect.not_isMulCommutative ↥K), Subgroup.mem_bot] at hc
  have hR0 : R ≠ ⊥ := by
    intro hR
    refine hτ1 (LinearEquiv.ext fun w => ?_)
    have h : ((τ : Module.End (ZMod 2) Y) - 1) w ∈ R := LinearMap.mem_range_self _ w
    rw [hR, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    exact h
  have hmatch₁ : ∀ v ∈ R, ∀ k ∈ K₁, ∃ y ∈ K₂, k v = y v := by
    intro v hv k hk
    refine ⟨τ * k⁻¹ * τ, hτ₁ _ (inv_mem hk), ?_⟩
    have h := hDfix k⁻¹ (inv_mem hk) v hv
    have h' : (k * (k⁻¹ * (τ * k⁻¹ * τ))) v = k v := by
      rw [LinearEquiv.mul_apply]
      exact congrArg k h
    rw [mul_inv_cancel_left] at h'
    exact h'.symm
  have hmatch₂ : ∀ v ∈ R, ∀ y ∈ K₂, y v = (τ * y * τ)⁻¹ v := by
    intro v hv y hy
    have h : ((τ * y * τ) * (τ * (τ * y * τ) * τ)) v = v := hDfix _ (hτ₂ y hy) v hv
    rw [hττ] at h
    calc y v = ((τ * y * τ)⁻¹ * ((τ * y * τ) * y)) v := by rw [inv_mul_cancel_left]
      _ = (τ * y * τ)⁻¹ v := by rw [LinearEquiv.mul_apply, h]
  obtain ⟨F, _, _, _, _, hcom, V₀, V₁, _, _, _, _, _, _, ρ₀, ρ₁, e, hnt₀, hnt₁, he₀, he₁⟩ :=
    K147L2Pair.exists_tensor_field hcomm hirr
  have : Finite V₀ := Module.finite_of_finite F
  have : Finite V₁ := Module.finite_of_finite F
  have : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  have hF2 : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F), Nat.card_zmod]
  have hR2 : Nat.card ↥R = 2 ^ Module.finrank (ZMod 2) ↥R := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥R), Nat.card_zmod]
  have hF1 : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨c, hcR, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR0
  have hex : ∀ u : ↥R, ∃ a : F, (u : Y) = a • c := fun u =>
    K147L2Pair.exists_smul_eq_of_match hcomm hirr hcom hc0 (hmatch₁ c hcR) fun y hy =>
      ⟨_, inv_mem (hτ₂ y hy), hmatch₂ c hcR y hy, hmatch₂ u u.2 y hy⟩
  choose α hα using hex
  have hRF : Nat.card ↥R ≤ Nat.card F := Nat.card_le_card_of_injective α fun u u' h =>
    Subtype.ext ((hα u).trans (h ▸ (hα u').symm))
  have hinj₀ : Function.Injective ρ₀ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    refine LinearEquiv.ext fun v => e.injective ?_
    have := he₀ g v
    rw [hg] at this
    simpa using this
  have hinj₁ : Function.Injective ρ₁ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    refine LinearEquiv.ext fun v => e.injective ?_
    have := he₁ g v
    rw [hg] at this
    simpa using this
  have hnsc₀ : ∀ a : ↥K₁, a ≠ 1 → ∀ s : F,
      ((ρ₀ a : V₀ ≃ₗ[F] V₀) : V₀ →ₗ[F] V₀) ≠ s • LinearMap.id := by
    intro a ha s hs
    have h1 : ∀ x, ρ₀ a x = s • x := fun x => LinearMap.congr_fun hs x
    refine ha (hZ hper₁ a fun g => hinj₀ (LinearEquiv.ext fun v => ?_))
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, h1, map_smul]
  have hnsc₁ : ∀ b : ↥K₂, b ≠ 1 → ∀ s : F,
      ((ρ₁ b : V₁ ≃ₗ[F] V₁) : V₁ →ₗ[F] V₁) ≠ s • LinearMap.id := by
    intro b hb s hs
    have h1 : ∀ x, ρ₁ b x = s • x := fun x => LinearMap.congr_fun hs x
    refine hb (hZ hper₂ b fun g => hinj₁ (LinearEquiv.ext fun v => ?_))
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, h1, map_smul]
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥K₁)
  let b : ↥K₂ := ⟨τ * (a : GLV Y)⁻¹ * τ, hτ₁ _ (inv_mem a.2)⟩
  have hd₁le := K147L2Pair.pow_finrank_le_card_sq e _ _ (hnsc₀ a ha) τ a fun w => by
    show e ((a : GLV Y) ((b : GLV Y) w)) = _
    rw [he₀ a, he₁ b, TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]
  obtain ⟨b', hb'⟩ := exists_ne (1 : ↥K₂)
  let a' : ↥K₁ := ⟨τ * (b' : GLV Y)⁻¹ * τ, hτ₂ _ (inv_mem b'.2)⟩
  have hd₀le := K147L2Pair.pow_finrank_le_card_sq
    (e.trans (TensorProduct.comm F V₀ V₁).toAddEquiv) _ _ (hnsc₁ b' hb') τ b' fun w => by
    show TensorProduct.comm F V₀ V₁ (e ((b' : GLV Y) ((a' : GLV Y) w))) =
      TensorProduct.map _ _ (TensorProduct.comm F V₀ V₁ (e w))
    rw [he₁ b', he₀ a', TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id,
      TensorProduct.map_comm]
  have hR2F : Nat.card ↥R ^ 2 ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hRF 2
  have hd₀ : Module.finrank F V₀ = 2 := by
    have h0 : 0 < Module.finrank F V₀ := Module.finrank_pos
    have h1 : Module.finrank F V₀ ≠ 1 := fun h1 =>
      ha (hinj₀ ((forall_eq_one_of_finrank_eq_one hper₁ ρ₀ h1 a).trans (map_one ρ₀).symm))
    have h2 := (Nat.pow_le_pow_iff_right hF1).mp (hd₀le.trans hR2F)
    omega
  have hd₁ : Module.finrank F V₁ = 2 := by
    have h0 : 0 < Module.finrank F V₁ := Module.finrank_pos
    have h1 : Module.finrank F V₁ ≠ 1 := fun h1 =>
      hb' (hinj₁ ((forall_eq_one_of_finrank_eq_one hper₂ ρ₁ h1 b').trans (map_one ρ₁).symm))
    have h2 := (Nat.pow_le_pow_iff_right hF1).mp (hd₁le.trans hR2F)
    omega
  have hFR : Nat.card F = Nat.card ↥R := by
    rw [hd₁] at hd₁le
    exact le_antisymm ((Nat.pow_le_pow_iff_left two_ne_zero).mp hd₁le) hRF
  have hε : Module.finrank (ZMod 2) F = Module.finrank (ZMod 2) ↥R :=
    Nat.pow_right_injective le_rfl (hF2.symm.trans (hFR.trans hR2))
  let b₀ : Module.Basis (Fin 2) F V₀ := Module.finBasisOfFinrankEq F V₀ hd₀
  let b₁ : Module.Basis (Fin 2) F V₁ := Module.finBasisOfFinrankEq F V₁ hd₁
  have := hper₁
  have := hper₂
  obtain ⟨R₀, hR₀i, hR₀⟩ := w4t_tensor_exists_sl b₀ ρ₀ hinj₀
  obtain ⟨R₁, hR₁i, hR₁⟩ := w4t_tensor_exists_sl b₁ ρ₁ hinj₁
  have hcK₁ : Nat.card ↥K₁ = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e₁.toEquiv, CFSG.GH74.GLS.IVK.Proofs2.Sl2Inv.card_SL2, hGF]
  have hdvd := Subgroup.card_dvd_of_injective R₀ hR₀i
  rw [hcK₁, CFSG.GH74.GLS.IVK.Proofs2.Sl2Inv.card_SL2, hF2] at hdvd
  obtain ⟨k, hk⟩ := w4t_tensor_dvd_of_card_dvd (by omega) hdvd
  have hlow : 2 ^ n ≤ Nat.card F := by
    have h := two_pow_le_natCard_of_ne_one hn hper₁ e₁ ρ₀
      ⟨a, fun h => ha (hinj₀ (h.trans (map_one ρ₀).symm))⟩
    rw [Module.natCard_eq_pow_finrank (K := F) (V := V₀), hd₀, mul_comm, pow_mul] at h
    exact (Nat.pow_le_pow_iff_left two_ne_zero).mp h
  have hnf : n ≤ Module.finrank (ZMod 2) F := by
    rw [hF2] at hlow
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hlow
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  ·
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 1 with hk0 | hk0
      · have : k = 0 := by omega
        rw [this, mul_zero] at hk
        omega
      · omega
    rw [hk1, mul_one] at hk
    refine Or.inr ⟨by rw [← hε, hk], F, inferInstance, inferInstance, by rw [hF2, hk], ?_⟩
    have hcSL : Nat.card SL(2, F) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [CFSG.GH74.GLS.IVK.Proofs2.Sl2Inv.card_SL2, hF2, hk]
    have hcK₂ : Nat.card ↥K₂ = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e₂.toEquiv, hcK₁]
    have hb₀ : Function.Bijective R₀ := hR₀i.bijective_of_nat_card_le (by rw [hcSL, hcK₁])
    have hb₁ : Function.Bijective R₁ := hR₁i.bijective_of_nat_card_le (by rw [hcSL, hcK₂])
    refine ⟨MulEquiv.ofBijective R₀ hb₀, MulEquiv.ofBijective R₁ hb₁,
      e.trans (tensorMatrixEquiv b₀ b₁).toAddEquiv, fun g v => ?_, fun g v => ?_⟩
    · show tensorMatrixEquiv b₀ b₁ (e ((g : GLV Y) v)) = _
      rw [he₀, tensorMatrixEquiv_map_left, MulEquiv.ofBijective_apply, hR₀]
      rfl
    · show tensorMatrixEquiv b₀ b₁ (e ((g : GLV Y) v)) = _
      rw [he₁, tensorMatrixEquiv_map_right, MulEquiv.ofBijective_apply, hR₁]
      rfl
  ·
    refine Or.inl ?_
    rw [← hε, hk]
    calc 2 * n = n * 2 := by ring
      _ ≤ n * k := Nat.mul_le_mul_left n hk2

end Core

section Transport

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {t : MulAut W}

omit [Finite W] in
theorem w4t_tensor_mem_fixV_zpowers {w : W} :
    w ∈ fixV (Subgroup.zpowers t) ↔ t w = w := by
  refine ⟨fun h => h t (Subgroup.mem_zpowers t), fun h x hx => ?_⟩
  have hle : Subgroup.zpowers t ≤ MulAction.stabilizer (MulAut W) w :=
    Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr h)
  exact MulAction.mem_stabilizer_iff.mp (hle hx)

theorem w4t_tensor_rkIdx_eq [ExpTwo W] (s : MulAut W) :
    rkIdx (fixV (Subgroup.zpowers s)) = Module.finrank (ZMod 2)
      (LinearMap.range ((toGL s : Module.End (ZMod 2) (Additive W)) - 1)) := by
  classical
  set f : Module.End (ZMod 2) (Additive W) := (toGL s : Module.End (ZMod 2) (Additive W)) - 1
    with hf
  have : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  have hmem : ∀ w : W, w ∈ fixV (Subgroup.zpowers s) ↔ Additive.ofMul w ∈ LinearMap.ker f := by
    intro w
    rw [w4t_tensor_mem_fixV_zpowers, LinearMap.mem_ker, hf, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero, LinearEquiv.coe_coe, toGL_apply]
    exact ⟨fun h => congrArg Additive.ofMul h, fun h => Additive.ofMul.injective h⟩
  have hcardker : Nat.card (fixV (Subgroup.zpowers s)) = Nat.card (LinearMap.ker f) :=
    Nat.card_congr
      { toFun := fun w => ⟨Additive.ofMul (w : W), (hmem w).mp w.2⟩
        invFun := fun a => ⟨Additive.toMul (a : Additive W), (hmem _).mpr a.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hW2 : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    rw [Nat.card_congr (Additive.ofMul : W ≃ Additive W),
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hK2 : Nat.card (LinearMap.ker f) = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker f) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hidx := (fixV (Subgroup.zpowers s)).card_mul_index
  rw [hcardker, hK2, hW2, ← LinearMap.finrank_range_add_finrank_ker f, pow_add] at hidx
  have hi : (fixV (Subgroup.zpowers s)).index = 2 ^ Module.finrank (ZMod 2) (LinearMap.range f) :=
    Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (hidx.trans (mul_comm _ _))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rkIdx
  rw [hi, padicValNat.prime_pow]

theorem tensor_or_two_mul_le (hW : ∀ w : W, w ^ 2 = 1) (ht2 : orderOf t = 2)
    (hmove : L.map (MulAut.conj t).toMonoidHom ≠ L)
    (hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hirr : IsIrrOn (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊤ ⊥)
    (hdiag : ∀ x ∈ L, ∀ w ∈ commV (Subgroup.zpowers t), (x * (t * x * t⁻¹)) w = w)
    {n : ℕ} (hn : 2 ≤ n) (e₁ : ↥L ≃* SL(2, GaloisField 2 n)) :
    2 * n ≤ rkIdx (fixV (Subgroup.zpowers t)) ∨
      (rkIdx (fixV (Subgroup.zpowers t)) = n ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          IsMatTensor2 L (L.map (MulAut.conj t).toMonoidHom) K) := by
  classical
  have : ExpTwo W := ⟨fun w => by rw [← sq]; exact hW w⟩
  set L' := L.map (MulAut.conj t).toMonoidHom with hL'
  have ht : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have : Nontrivial W := by
    obtain ⟨w, -, hw⟩ := SetLike.exists_of_lt hirr.1
    exact ⟨⟨w, 1, fun h => hw (h ▸ Subgroup.one_mem _)⟩⟩
  have hinjGL : Function.Injective (toGL : MulAut W →* GLV (Additive W)) := toGL_injective
  set K₁ : Subgroup (GLV (Additive W)) := L.map toGL with hK₁
  set K₂ : Subgroup (GLV (Additive W)) := L'.map toGL with hK₂
  have hLL' : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := fun a ha b hb =>
    commutatorElement_eq_one_iff_mul_comm.mp
      (Subgroup.mem_bot.mp (hcomm ▸ Subgroup.commutator_mem_commutator ha hb))
  have hcomm' : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hLL' a ha b hb]
  have hirr' : Offender.IsIrrAct (K₁ ⊔ K₂) := by
    intro U hU
    let J : Subgroup W :=
      { carrier := {w | Additive.ofMul w ∈ U}
        mul_mem' := fun ha hb => U.add_mem ha hb
        one_mem' := U.zero_mem
        inv_mem' := fun ha => U.neg_mem ha }
    have hJ : StableUnder (L ⊔ L') J := by
      intro x hx w hw
      have hx' : toGL x ∈ K₁ ⊔ K₂ := by
        rw [hK₁, hK₂, ← Subgroup.map_sup]
        exact Subgroup.mem_map_of_mem _ hx
      exact hU _ hx' _ hw
    rcases hirr.2.2.2 J hJ bot_le le_top with h | h
    · refine Or.inl (eq_bot_iff.mpr fun u hu => ?_)
      have hu' : Additive.toMul u ∈ J := hu
      rw [h, Subgroup.mem_bot] at hu'
      exact (Submodule.mem_bot _).mpr (congrArg Additive.ofMul hu')
    · refine Or.inr (eq_top_iff.mpr fun u _ => ?_)
      have hu' : Additive.toMul u ∈ J := h ▸ Subgroup.mem_top _
      exact hu'
  have hτ : toGL t * toGL t = 1 := by rw [← map_mul, ht, map_one]
  have hτ1 : toGL t ≠ 1 := by
    intro h1
    have ht1 : t = 1 := hinjGL (h1.trans (map_one _).symm)
    apply hmove
    ext x
    simp [hL', ht1]
  have hτ₁ : ∀ x ∈ K₁, toGL t * x * toGL t ∈ K₂ := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨t * a * t⁻¹, ⟨a, ha, rfl⟩, ?_⟩
    rw [htinv, map_mul, map_mul]
  have hτ₂ : ∀ y ∈ K₂, toGL t * y * toGL t ∈ K₁ := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨a, ha, ?_⟩
    have e : t * (t * a * t⁻¹) * t = a := by
      rw [htinv]
      calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
        _ = a := by rw [ht, one_mul, mul_one]
    rw [← map_mul, ← map_mul]
    exact congrArg toGL e.symm
  have hDfix : ∀ k ∈ K₁,
      ∀ u ∈ LinearMap.range ((toGL t : Module.End (ZMod 2) (Additive W)) - 1),
        (k * (toGL t * k * toGL t)) u = u := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨a, rfl⟩
    have hmem : t (Additive.toMul a) * (Additive.toMul a)⁻¹ ∈ commV (Subgroup.zpowers t) :=
      Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, Additive.toMul a, rfl⟩
    have h := hdiag x hx _ hmem
    have e : toGL x * (toGL t * toGL x * toGL t) = toGL (x * (t * x * t⁻¹)) := by
      rw [htinv, map_mul, map_mul, map_mul]
    have e2 : ((toGL t : Module.End (ZMod 2) (Additive W)) - 1) a =
        Additive.ofMul (t (Additive.toMul a) * (Additive.toMul a)⁻¹) := by
      rw [LinearMap.sub_apply, Module.End.one_apply, ofMul_mul, ofMul_inv, ← sub_eq_add_neg]
      rfl
    rw [e, e2, toGL_apply, h]
  rcases w4t_tensor_core hcomm' hirr' hn ((L.equivMapOfInjective toGL hinjGL).symm.trans e₁) hτ
      hτ1 hτ₁ hτ₂ hDfix with h | ⟨hR, F, _, _, hF, φ₁, φ₂, A, hA₁, hA₂⟩
  · exact Or.inl (by rwa [w4t_tensor_rkIdx_eq])
  · refine Or.inr ⟨by rwa [w4t_tensor_rkIdx_eq], F, inferInstance, inferInstance, hF, ?_⟩
    let ψ : W ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F) :=
      { toFun := fun w => Multiplicative.ofAdd (A (Additive.ofMul w))
        invFun := fun X => Additive.toMul (A.symm (Multiplicative.toAdd X))
        left_inv := fun w => by simp
        right_inv := fun X => by simp
        map_mul' := fun w w' => by
          show Multiplicative.ofAdd (A (Additive.ofMul (w * w'))) =
            Multiplicative.ofAdd (A (Additive.ofMul w)) *
              Multiplicative.ofAdd (A (Additive.ofMul w'))
          rw [ofMul_mul, map_add, ofAdd_add] }
    refine ⟨(L.equivMapOfInjective toGL hinjGL).trans φ₁,
      (L'.equivMapOfInjective toGL hinjGL).trans φ₂, ψ, fun x w => ?_, fun y w => ?_⟩
    · exact hA₁ (L.equivMapOfInjective toGL hinjGL x) (Additive.ofMul w)
    · exact hA₂ (L'.equivMapOfInjective toGL hinjGL y) (Additive.ofMul w)

end Transport

end CFSG.LocalAnalysis.WeakClosure81
