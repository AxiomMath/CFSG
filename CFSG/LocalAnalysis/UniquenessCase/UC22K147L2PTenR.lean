module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2PSet
public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2PTen
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.TensorAssemble
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.TensorRank
public import CFSG.GH74.GLS.IVK.Proofs2.Sl2Inv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair

open CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
open scoped TensorProduct MatrixGroups

theorem not_dvd_card_sl2_two_mul {q : ℕ} (hq : 8 ≤ q) :
    ¬ q * (q ^ 2 - 1) ∣ (2 * q) * ((2 * q) ^ 2 - 1) := by
  intro h
  have hQ : 64 ≤ q ^ 2 := by nlinarith
  have e1 : (2 * q) * ((2 * q) ^ 2 - 1) = q * (2 * (4 * q ^ 2 - 1)) := by
    rw [mul_pow]
    ring
  rw [e1] at h
  have h2 := Nat.dvd_of_mul_dvd_mul_left (by omega) h
  generalize q ^ 2 = Q at hQ h2
  have e2 : 2 * (4 * Q - 1) = 8 * (Q - 1) + 6 := by omega
  rw [e2] at h2
  have h3 := (Nat.dvd_add_right (dvd_mul_left (Q - 1) 8)).mp h2
  have := Nat.le_of_dvd (by norm_num) h3
  omega

section Ten

variable {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]

theorem pow_finrank_le_card_sq {F : Type} [Field F] [Finite F] {W₀ W₁ : Type} [AddCommGroup W₀]
    [Module F W₀] [AddCommGroup W₁] [Module F W₁] [Module.Finite F W₀] [Module.Finite F W₁]
    (e : Y ≃+ W₀ ⊗[F] W₁) (A : W₀ →ₗ[F] W₀) (B : W₁ →ₗ[F] W₁)
    (hA : ∀ a : F, A ≠ a • LinearMap.id) (τ x : GLV Y)
    (hy : ∀ w, e (x ((τ * x⁻¹ * τ) w)) = TensorProduct.map A B (e w)) :
    Nat.card F ^ Module.finrank F W₁ ≤
      Nat.card ↥(LinearMap.range ((τ : Module.End (ZMod 2) Y) - 1)) ^ 2 := by
  classical
  haveI : Finite (W₀ ⊗[F] W₁) := Module.finite_of_finite F
  have hrank := CFSG.AGLEmbeddingD2.McLaughlin.finrank_le_finrank_range_tensor_sub_one_of_not_scalar
    A B hA
  have hpre : ∀ s : ↥(LinearMap.range (TensorProduct.map A B - LinearMap.id :
      W₀ ⊗[F] W₁ →ₗ[F] W₀ ⊗[F] W₁)), ∃ p : ↥(LinearMap.range
        ((τ : Module.End (ZMod 2) Y) - 1)) × ↥(LinearMap.range ((τ : Module.End (ZMod 2) Y) - 1)),
      e (x (τ (x⁻¹ (p.1 : Y))) + x (p.2 : Y)) = s := by
    rintro ⟨_, z, rfl⟩
    refine ⟨(⟨τ (e.symm z) - e.symm z, e.symm z, rfl⟩,
      ⟨τ (x⁻¹ (e.symm z)) - x⁻¹ (e.symm z), x⁻¹ (e.symm z), rfl⟩), ?_⟩
    have hxx : x (x⁻¹ (e.symm z)) = e.symm z := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    have h1 : x (τ (x⁻¹ (τ (e.symm z) - e.symm z))) + x (τ (x⁻¹ (e.symm z)) - x⁻¹ (e.symm z)) =
        x ((τ * x⁻¹ * τ) (e.symm z)) - e.symm z := by
      simp only [map_sub, LinearEquiv.mul_apply, hxx]
      abel
    show e (x (τ (x⁻¹ (τ (e.symm z) - e.symm z))) + x (τ (x⁻¹ (e.symm z)) - x⁻¹ (e.symm z))) =
      (TensorProduct.map A B - LinearMap.id : W₀ ⊗[F] W₁ →ₗ[F] W₀ ⊗[F] W₁) z
    rw [h1, map_sub, hy, AddEquiv.apply_symm_apply, LinearMap.sub_apply, LinearMap.id_apply]
  choose ι hι using hpre
  have hinj : Function.Injective ι := fun s s' h =>
    Subtype.ext ((hι s).symm.trans (by rw [h, hι s']))
  have h1 := Nat.card_le_card_of_injective ι hinj
  rw [Nat.card_prod, ← sq, Module.natCard_eq_pow_finrank (K := F)] at h1
  exact (Nat.pow_le_pow_right Nat.card_pos hrank).trans h1

theorem ten_core [Nontrivial Y] {K₁ K₂ : Subgroup (GLV Y)}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hirr : Offender.IsIrrAct (K₁ ⊔ K₂))
    {F₀ : Type} [Field F₀] [Fintype F₀] [CharP F₀ 2] (e₁ : ↥K₁ ≃* SL(2, F₀)) {n : ℕ}
    (hn : 3 ≤ n) (hF₀ : Fintype.card F₀ = 2 ^ n) {τ : GLV Y} (hτ : τ * τ = 1)
    (hτ₁ : ∀ x ∈ K₁, τ * x * τ ∈ K₂) (hτ₂ : ∀ y ∈ K₂, τ * y * τ ∈ K₁)
    (hδ : Module.finrank (ZMod 2) (LinearMap.range ((τ : Module.End (ZMod 2) Y) - 1)) ≤ n + 1) :
    n ≤ Module.finrank (ZMod 2) (LinearMap.range ((τ : Module.End (ZMod 2) Y) - 1)) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Algebra (ZMod 2) F),
        Nat.card F = 2 ^ n ∧ IsTensorModel 2 F (K₁ ⊔ K₂) := by
  classical
  set R := LinearMap.range ((τ : Module.End (ZMod 2) Y) - 1) with hRdef
  have hF₀n : Nat.card F₀ = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF₀]
  have h4 : 4 ≤ Nat.card F₀ := by
    rw [hF₀n]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : IsSimpleGroup SL(2, F₀) := P22y.isSimpleGroup_sl2 h4
  haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F₀ h4
  haveI : IsSimpleGroup ↥K₁ := e₁.isSimpleGroup
  have hper₁ : Group.IsPerfect ↥K₁ :=
    Group.IsPerfect.ofSurjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card F₀ = Fintype.card (GaloisField 2 n) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF₀n, GaloisField.card 2 n (by omega)]
  let eG : ↥K₁ ≃* SL(2, GaloisField 2 n) :=
    e₁.trans (slRingEquiv (FiniteField.ringEquivOfCardEq hcard))
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
  haveI : IsSimpleGroup ↥K₂ := e₂.isSimpleGroup
  have hper₂ : Group.IsPerfect ↥K₂ :=
    Group.IsPerfect.ofSurjective (f := e₂.symm.toMonoidHom) e₂.symm.surjective
  have hZ : ∀ {K : Subgroup (GLV Y)} [IsSimpleGroup ↥K], Group.IsPerfect ↥K →
      ∀ z : ↥K, (∀ x : ↥K, z * x = x * z) → z = 1 := by
    intro K _ hK z hz
    haveI := hK
    have hc : z ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.mpr fun g => (hz g).symm
    rwa [TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (Group.IsPerfect.not_isMulCommutative ↥K), Subgroup.mem_bot] at hc
  have hR0 : R ≠ ⊥ := by
    intro hR
    have hτ1 : τ = 1 := LinearEquiv.ext fun w => by
      have h : ((τ : Module.End (ZMod 2) Y) - 1) w ∈ R := LinearMap.mem_range_self _ w
      rw [hR, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
      exact h
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥K₁)
    refine hg (hZ hper₁ g fun x => Subtype.ext ?_)
    have hx : (x : GLV Y) ∈ K₂ := by simpa [hτ1] using hτ₁ x x.2
    exact hcomm g g.2 x hx
  have hinf : K₁ ⊓ K₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val
      (hZ hper₁ ⟨x, hx.1⟩ fun g => Subtype.ext (hcomm g g.2 x hx.2).symm)
  let δ : ↥K₁ →* GLV Y :=
    { toFun := fun k => (k : GLV Y) * (τ * k * τ)
      map_one' := by
        show (1 : GLV Y) * (τ * 1 * τ) = 1
        rw [one_mul, mul_one, hτ]
      map_mul' := fun a b => by
        show (a : GLV Y) * b * (τ * (a * b) * τ) = a * (τ * a * τ) * (b * (τ * b * τ))
        have h := hcomm b b.2 _ (hτ₁ a a.2)
        rw [hconj]
        calc (a : GLV Y) * b * (τ * a * τ * (τ * b * τ)) =
            a * (b * (τ * a * τ)) * (τ * b * τ) := by group
          _ = a * ((τ * a * τ) * b) * (τ * b * τ) := by rw [h]
          _ = a * (τ * a * τ) * (b * (τ * b * τ)) := by group }
  have hδτ : ∀ k : ↥K₁, τ * δ k = δ k * τ := fun k => by
    have h := hcomm k k.2 _ (hτ₁ k k.2)
    show τ * ((k : GLV Y) * (τ * k * τ)) = (k : GLV Y) * (τ * k * τ) * τ
    calc τ * ((k : GLV Y) * (τ * k * τ)) = τ * ((τ * k * τ) * k) := by rw [h]
      _ = τ * τ * k * τ * k := by group
      _ = k * τ * k * (τ * τ) := by rw [hτ, one_mul, mul_one]
      _ = (k : GLV Y) * (τ * k * τ) * τ := by group
  have hRinv : ∀ k : ↥K₁, ∀ u ∈ R, δ k u ∈ R := by
    rintro k _ ⟨w, rfl⟩
    refine ⟨δ k w, ?_⟩
    have h := LinearEquiv.congr_fun (hδτ k) w
    simp only [LinearEquiv.mul_apply] at h
    show τ (δ k w) - δ k w = δ k (τ w - w)
    rw [map_sub, ← h]
  let ρD : Representation (ZMod 2) ↥K₁ Y :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp δ
  have hDfix : ∀ k : ↥K₁, ∀ u ∈ R, δ k u = u := by
    by_contra hc
    push Not at hc
    obtain ⟨k, u, hu, hne⟩ := hc
    have := two_mul_le_finrank_of_moves ρD (K := ⊤) ((Subgroup.topEquiv).trans e₁) (by omega)
      hF₀n (Y := R) (fun a _ u hu => hRinv a u hu) ⟨k, Subgroup.mem_top k, u, hu, hne⟩
    omega
  have hmatch₁ : ∀ v ∈ R, ∀ k ∈ K₁, ∃ y ∈ K₂, k v = y v := by
    intro v hv k hk
    refine ⟨τ * k⁻¹ * τ, hτ₁ _ (inv_mem hk), ?_⟩
    have h := hDfix ⟨k⁻¹, inv_mem hk⟩ v hv
    have h' : (k * (k⁻¹ * (τ * k⁻¹ * τ))) v = k v := by
      rw [LinearEquiv.mul_apply]
      exact congrArg k h
    rw [mul_inv_cancel_left] at h'
    exact h'.symm
  have hmatch₂ : ∀ v ∈ R, ∀ y ∈ K₂, y v = (τ * y * τ)⁻¹ v := by
    intro v hv y hy
    have h : ((τ * y * τ) * (τ * (τ * y * τ) * τ)) v = v := hDfix ⟨τ * y * τ, hτ₂ y hy⟩ v hv
    rw [hττ] at h
    calc y v = ((τ * y * τ)⁻¹ * ((τ * y * τ) * y)) v := by rw [inv_mul_cancel_left]
      _ = (τ * y * τ)⁻¹ v := by rw [LinearEquiv.mul_apply, h]
  obtain ⟨F, _, _, _, _, hcom, V₀, V₁, _, _, _, _, _, _, ρ₀, ρ₁, e, hnt₀, hnt₁, he₀, he₁⟩ :=
    exists_tensor_field hcomm hirr
  haveI : Finite V₀ := Module.finite_of_finite F
  haveI : Finite V₁ := Module.finite_of_finite F
  haveI : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  have hF2 : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F), Nat.card_zmod]
  have hR2 : Nat.card ↥R = 2 ^ Module.finrank (ZMod 2) ↥R := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥R), Nat.card_zmod]
  have hF1 : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨c, hcR, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR0
  have hex : ∀ u : ↥R, ∃ a : F, (u : Y) = a • c := fun u =>
    exists_smul_eq_of_match hcomm hirr hcom hc0 (hmatch₁ c hcR) fun y hy =>
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
  have hd₁le := pow_finrank_le_card_sq e _ _ (hnsc₀ a ha) τ a fun w => by
    show e ((a : GLV Y) ((b : GLV Y) w)) = _
    rw [he₀ a, he₁ b, TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]
  obtain ⟨b', hb'⟩ := exists_ne (1 : ↥K₂)
  let a' : ↥K₁ := ⟨τ * (b' : GLV Y)⁻¹ * τ, hτ₂ _ (inv_mem b'.2)⟩
  have hd₀le := pow_finrank_le_card_sq (e.trans (TensorProduct.comm F V₀ V₁).toAddEquiv) _ _
    (hnsc₁ b' hb') τ b' fun w => by
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
  have hlow : 2 ^ n ≤ Nat.card F := by
    have h := two_pow_le_natCard_of_ne_one (by omega) hper₁ eG ρ₀
      ⟨a, fun h => ha (hinj₀ (h.trans (map_one ρ₀).symm))⟩
    rw [Module.natCard_eq_pow_finrank (K := F) (V := V₀), hd₀, mul_comm, pow_mul] at h
    exact (Nat.pow_le_pow_iff_left two_ne_zero).mp h
  have hε : Module.finrank (ZMod 2) F = Module.finrank (ZMod 2) ↥R :=
    Nat.pow_right_injective le_rfl (hF2.symm.trans (hFR.trans hR2))
  have hnε : n ≤ Module.finrank (ZMod 2) F := by
    rw [hF2] at hlow
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hlow
  have hεn : Module.finrank (ZMod 2) F = n := by
    by_contra hne
    have hε1 : Module.finrank (ZMod 2) F = n + 1 := by omega
    let b₀ : Module.Basis (Fin 2) F V₀ := Module.finBasisOfFinrankEq F V₀ hd₀
    haveI := hper₁
    let R₀ : ↥K₁ →* StatedSL 2 F := ((basisGL b₀).comp ρ₀).codRestrict (StatedSL 2 F)
      (fun g => Subgroup.subset_closure (det_eq_one_of_perfect ((basisGL b₀).comp ρ₀) g))
    have hR₀ : Function.Injective R₀ := fun g g' h =>
      hinj₀ (basisGL_injective b₀ (congrArg Subtype.val h))
    have hdvd := Subgroup.card_dvd_of_injective R₀ hR₀
    rw [Nat.card_congr e₁.toEquiv, ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
      CFSG.GH74.GLS.IVK.Proofs2.Sl2Inv.card_SL2, CFSG.GH74.GLS.IVK.Proofs2.Sl2Inv.card_SL2, hF₀n,
      hF2, hε1, pow_succ (2 : ℕ) n, mul_comm (2 ^ n) 2] at hdvd
    exact not_dvd_card_sl2_two_mul (q := 2 ^ n)
      (by calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn) hdvd
  have hFn : Nat.card F = 2 ^ n := by rw [hF2, hεn]
  refine ⟨by rw [← hε, hεn], F, inferInstance, inferInstance, inferInstance, hFn, ?_⟩
  have hSL : Nat.card SL(2, F) = Nat.card SL(2, F₀) := by
    rw [CFSG.GH74.GLS.IVK.Proofs2.Sl2Inv.card_SL2, CFSG.GH74.GLS.IVK.Proofs2.Sl2Inv.card_SL2, hFn,
      hF₀n]
  have hcL : Nat.card ↥K₁ = Nat.card ↥(StatedSL 2 F) := by
    rw [Nat.card_congr e₁.toEquiv, ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
      hSL]
  have hcL₂ : Nat.card ↥K₂ = Nat.card ↥(StatedSL 2 F) := by
    rw [Nat.card_congr e₂.toEquiv, hcL]
  exact isTensorModel_of_tensorData hcomm hinf ρ₀ ρ₁ e he₀ he₁ hd₀ hd₁ hper₁ hper₂ hcL hcL₂
    hinj₀ hinj₁

end Ten

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair
