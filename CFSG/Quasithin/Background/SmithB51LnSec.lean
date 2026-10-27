module

public import CFSG.Quasithin.Background.SmithB51LnReal
public import CFSG.Quasithin.Background.SmithB51SL3Common

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix Module
open scoped Matrix

theorem exists_equiv_zmod_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (n : ℕ) :
    Nonempty (↥(StatedSL n (ZMod 2)) ≃* ↥(StatedSL n K)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card (ZMod 2) = Fintype.card K := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK]
  set φ : ZMod 2 ≃+* K := FiniteField.ringEquivOfCardEq hcard
  have hmem : ∀ γ : ↥(StatedSL n (ZMod 2)),
      Units.map (φ.toRingHom.mapMatrix :
        Matrix (Fin n) (Fin n) (ZMod 2) →+* Matrix (Fin n) (Fin n) K)
          (γ : GL (Fin n) (ZMod 2)) ∈ StatedSL n K := by
    intro γ
    apply Subgroup.subset_closure
    show (((γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).map φ).det = 1
    have h1 : ((γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
      have hu : ∀ u : (ZMod 2)ˣ, (u : ZMod 2) = 1 := by decide
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact hu _
    have h2 := RingHom.map_det φ.toRingHom
      ((γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
    rw [h1, map_one] at h2
    exact h2.symm
  let ι : ↥(StatedSL n (ZMod 2)) →* ↥(StatedSL n K) :=
    ((Units.map (φ.toRingHom.mapMatrix : Matrix (Fin n) (Fin n) (ZMod 2) →+*
      Matrix (Fin n) (Fin n) K)).comp (StatedSL n (ZMod 2)).subtype).codRestrict _ hmem
  have hinj : Function.Injective ι := by
    intro g h hgh
    apply mat_injective
    ext i j
    have := congrArg
      (fun x : ↥(StatedSL n K) => ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) hgh
    exact φ.injective this
  have hsurj : Function.Surjective ι := by
    intro γ'
    refine ⟨ofGL (Units.map (φ.symm.toRingHom.mapMatrix : Matrix (Fin n) (Fin n) K →+*
      Matrix (Fin n) (Fin n) (ZMod 2)) (γ' : GL (Fin n) K)), Subtype.ext (Units.ext ?_)⟩
    ext i j
    show φ (φ.symm _) = _
    rw [RingEquiv.apply_symm_apply]
  exact ⟨MulEquiv.ofBijective ι ⟨hinj, hsurj⟩⟩

theorem center_eq_bot_of_equiv {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {n : ℕ} (e : X ≃* ↥(StatedSL n K)) : Subgroup.center X = ⊥ := by
  obtain ⟨ι⟩ := exists_equiv_zmod_two hK n
  set f := e.trans ι.symm
  rw [eq_bot_iff]
  intro z hz
  have h1 : f z = 1 := by
    apply eq_one_of_forall_commute
    intro g
    obtain ⟨x, rfl⟩ := f.surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz x).symm]
  rw [Subgroup.mem_bot]
  exact f.injective (h1.trans (map_one f).symm)

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)} {W U : Subgroup V}

theorem faithful_sec (h : B51Hyp G L) (c : SecCtx G L A W U) (hZ : Subgroup.center ↥L = ⊥) :
    (L ⊔ A) ⊓ centSec W U = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 := (secKernel_le h c).1 hx
  have h2 := (secKernel_le h c).2 hx
  have hz : (⟨x, h1⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h2 l l.2)
  rw [hZ, Subgroup.mem_bot] at hz
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hz

theorem faithful_secL (h : B51Hyp G L) (c : SecCtx G L A W U) (hZ : Subgroup.center ↥L = ⊥) :
    L ⊓ centSec W U = ⊥ := by
  rw [eq_bot_iff, ← faithful_sec h c hZ]
  exact inf_le_inf_right _ le_sup_left

theorem sec_IH (hA21 : AsA21SQTKSection) (hIH : B51Part1Below (Nat.card V))
    (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (c : SecCtx G L A W U)
    (hcard : Nat.card (Sec W U) < Nat.card V) (hr : rAV (autSec A W U) ≤ 1) :
    ∃ B, B ≤ autSec A W U ∧ IsFFStarOffender (autSec (L ⊔ A) W U) B ∧
      Nat.card (autSec A W U) * Nat.card (fixV (autSec A W U)) ≤ Nat.card B * Nat.card (fixV B) ∧
      B51Part1 (autSec L W U ⊔ B) (autSec L W U) := by
  obtain ⟨B, hBA, hB, hBc⟩ :=
    exists_offender_max (CFSG.Quasithin.sq_eq_one_sec hV W U) (isA2_secA h c) hr
  exact ⟨B, hBA, hB, hBc,
    hIH (Sec W U) hcard (CFSG.Quasithin.sq_eq_one_sec hV W U) _ _ (b51Hyp_secY h c hA21 hB)⟩

@[expose] noncomputable def rkSub (A : Subgroup (MulAut V)) (X : Subgroup V) : ℕ :=
  rk X - rk ↥(X ⊓ fixV A)

theorem rkSub_top (A : Subgroup (MulAut V)) : rkSub A ⊤ = rkIdx (fixV A) := by
  have := rk_add_rkIdx (fixV A)
  rw [rkSub, top_inf_eq, rk_top]
  omega

theorem rkSub_ge_sec (hV : ∀ v : V, v ^ 2 = 1) {W U : Subgroup V} (hUW : U ≤ W)
    (hAW : A ≤ stabSub W) : rkIdx (fixV (autSec A W U)) + rkSub A U ≤ rkSub A W :=
  rk_mu_section hV hUW hAW

theorem rkSub_mono {X X' : Subgroup V} (hXX' : X ≤ X') : rkSub A X ≤ rkSub A X' := by
  have h1 := rk_sup_add_rk_inf X (X' ⊓ fixV A)
  have h2 : X ⊓ (X' ⊓ fixV A) = X ⊓ fixV A := by
    rw [← inf_assoc, inf_eq_left.2 hXX']
  have h3 : X ⊔ (X' ⊓ fixV A) ≤ X' := sup_le hXX' inf_le_left
  have h4 := rk_mono h3
  rw [h2] at h1
  unfold rkSub
  have h5 : rk ↥(X ⊓ fixV A) ≤ rk X := rk_mono inf_le_left
  have h6 : rk ↥(X' ⊓ fixV A) ≤ rk X' := rk_mono inf_le_left
  omega

theorem rkSub_sup {X I : Subgroup V} (hX : ∀ a ∈ A, ∀ x ∈ X, a x ∈ X)
    (hI : ∀ a ∈ A, ∀ x ∈ I, a x ∈ I) (hXI : X ⊓ I = ⊥) :
    rkSub A (X ⊔ I) = rkSub A X + rkSub A I := by
  have hfix : (X ⊔ I) ⊓ fixV A = (X ⊓ fixV A) ⊔ (I ⊓ fixV A) := by
    refine le_antisymm (fun v hv => ?_) (sup_le (inf_le_inf_right _ le_sup_left)
      (inf_le_inf_right _ le_sup_right))
    obtain ⟨hvXI, hvF⟩ := hv
    obtain ⟨x, hx, i, hi, rfl⟩ := Subgroup.mem_sup.1 hvXI
    have key : ∀ a ∈ A, a x = x ∧ a i = i := by
      intro a ha
      have h1 : a (x * i) = x * i := hvF a ha
      rw [map_mul] at h1
      have h2 : a x * x⁻¹ = i * (a i)⁻¹ := by
        rw [mul_inv_eq_iff_eq_mul, mul_comm i, mul_assoc, mul_comm i x, ← h1, mul_comm (a x),
          ← mul_assoc, inv_mul_cancel, one_mul]
      have h3 : a x * x⁻¹ ∈ X ⊓ I := ⟨X.mul_mem (hX a ha x hx) (X.inv_mem hx), by
        rw [h2]; exact I.mul_mem hi (I.inv_mem (hI a ha i hi))⟩
      rw [hXI, Subgroup.mem_bot, mul_inv_eq_one] at h3
      refine ⟨h3, ?_⟩
      rw [h3, mul_inv_cancel, eq_comm, mul_inv_eq_one] at h2
      exact h2.symm
    exact Subgroup.mul_mem_sup ⟨hx, fun a ha => (key a ha).1⟩ ⟨hi, fun a ha => (key a ha).2⟩
  have h1 := rk_sup_add_rk_inf X I
  rw [hXI, rk_bot, add_zero] at h1
  have h2 := rk_sup_add_rk_inf (X ⊓ fixV A) (I ⊓ fixV A)
  have h3 : (X ⊓ fixV A) ⊓ (I ⊓ fixV A) = ⊥ := by
    rw [eq_bot_iff, ← hXI]
    exact inf_le_inf inf_le_left inf_le_left
  rw [h3, rk_bot, add_zero] at h2
  have h4 : rk ↥(X ⊓ fixV A) ≤ rk X := rk_mono inf_le_left
  have h5 : rk ↥(I ⊓ fixV A) ≤ rk I := rk_mono inf_le_left
  have h6 : rkSub A (X ⊔ I) = rk ↥(X ⊔ I) - rk ↥((X ⊔ I) ⊓ fixV A) := rfl
  rw [h6, hfix, h1, h2, rkSub, rkSub]
  omega

theorem rkIdx_fixV_autSec_bot {X : Subgroup V} (hAX : A ≤ stabSub X) :
    rkIdx (fixV (autSec A X ⊥)) = rkSub A X := by
  have hAbot : A ≤ stabSub (⊥ : Subgroup V) := fun a _ u => by
    simp only [Subgroup.mem_bot]
    constructor
    · intro h
      exact a.injective (h.trans (map_one a).symm)
    · intro h
      rw [h, map_one]
  have hcardS : Nat.card (Sec X ⊥) = Nat.card X := by
    have := card_sec_mul (bot_le : (⊥ : Subgroup V) ≤ X)
    rwa [Subgroup.card_bot, mul_one] at this
  have hfixc : Nat.card (fixV (autSec A X ⊥)) = Nat.card ↥(X ⊓ fixV A) := by
    let f : ↥(X ⊓ fixV A) → ↥(fixV (autSec A X ⊥)) := fun x =>
      ⟨QuotientGroup.mk ⟨x, x.2.1⟩, (mk_mem_fixV_autSec_iff hAX hAbot _).2 fun a ha => by
        rw [x.2.2 a ha, mul_inv_cancel]; exact Subgroup.one_mem _⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        have := congrArg Subtype.val hxy
        simp only [f, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at this
        apply Subtype.ext
        have h2 : ((x : V))⁻¹ * (y : V) = 1 := this
        rw [inv_mul_eq_one] at h2
        exact h2
      · intro s
        obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (s : Sec X ⊥)
        have hs := s.2
        rw [← hw, mk_mem_fixV_autSec_iff hAX hAbot] at hs
        refine ⟨⟨w, w.2, fun a ha => ?_⟩, Subtype.ext ?_⟩
        · have := hs a ha
          rw [Subgroup.mem_bot, mul_inv_eq_one] at this
          exact this
        · exact hw
    exact (Nat.card_eq_of_bijective f hf).symm
  have h1 := rk_add_rkIdx (fixV (autSec A X ⊥))
  have h2 : rk (fixV (autSec A X ⊥)) = rk ↥(X ⊓ fixV A) := by
    unfold rk; rw [hfixc]
  have h3 : rk (Sec X ⊥) = rk X := by
    unfold rk; rw [hcardS]
  unfold rkSub
  omega

section RealBounds

variable {n : ℕ} {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
  {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)} {Y : Subgroup V}

theorem eq_one_of_forall_M (hM : M = mat ∨ M = dmat) {γ : ↥(StatedSL n (ZMod 2))}
    (h : ∀ x, M γ *ᵥ x = x) : γ = 1 := by
  rcases hM with rfl | rfl
  · exact eq_of_mulVec_eq fun x => by rw [h, mat_one, one_mulVec]
  · have h3 : dmat γ = 1 := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro y
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h, one_mulVec]
    have h4 : mat γ⁻¹ = 1 := by
      have := congrArg Matrix.transpose h3
      rwa [dmat, transpose_transpose, transpose_one] at this
    have h5 : γ⁻¹ = 1 := eq_of_mulVec_eq fun x => by rw [h4, mat_one]
    exact inv_eq_one.1 h5

omit [Finite V] in
theorem card_pre (hπ : Function.Bijective π) {B : Subgroup (MulAut V)} (hBL : B ≤ L) :
    Nat.card (pre π B) = Nat.card B := by
  have h1 : (pre π B).map π = B.subgroupOf L :=
    Subgroup.map_comap_eq_self_of_surjective hπ.2 _
  rw [← Subgroup.card_map_of_injective hπ.1, h1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv

omit [Finite V] in
theorem isPGroup_pre (hπ : Function.Bijective π) {B : Subgroup (MulAut V)}
    (hB2 : IsPGroup 2 ↥B) : IsPGroup 2 ↥(pre π B) := by
  intro x
  obtain ⟨k, hk⟩ := hB2 ⟨((π x : ↥L) : MulAut V), x.2⟩
  refine ⟨k, Subtype.ext (hπ.1 ?_)⟩
  apply Subtype.ext
  have := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
  rw [map_pow, map_one]
  simpa using this

theorem rk_le_mul_pre (hπ : Function.Bijective π) {B : Subgroup (MulAut V)} (hBL : B ≤ L)
    (hB2 : IsPGroup 2 ↥B) :
    rk B ≤ (n - finrank (ZMod 2) (fixN (pre π B))) * finrank (ZMod 2) (commN (pre π B)) := by
  have h1 := card_le_two_pow_mul (pre π B)
  rw [card_pre hπ hBL, card_eq_two_pow_of_isPGroup hB2] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

omit [Finite V] in
theorem finrank_fixM_lt (hπ : Function.Bijective π) (hM : M = mat ∨ M = dmat)
    {B : Subgroup (MulAut V)} (hBL : B ≤ L) (hBne : B ≠ ⊥) :
    finrank (ZMod 2) (fixM M (pre π B)) < n := by
  obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBne
  obtain ⟨γ, hγ⟩ := hπ.2 ⟨b, hBL hb⟩
  have hγB : γ ∈ pre π B := by rw [mem_pre, hγ]; exact hb
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    rw [map_one] at hγ
    exact hb1 (Subtype.ext (congrArg Subtype.val hγ).symm)
  have hne : fixM M (pre π B) ≠ ⊤ := by
    intro htop
    apply hγ1
    apply eq_one_of_forall_M hM
    intro x
    have : x ∈ fixM M (pre π B) := by rw [htop]; trivial
    exact this γ hγB
  have := Submodule.finrank_lt hne
  rwa [Module.finrank_fin_fun (ZMod 2)] at this

theorem RealM.rk_le (h : RealM L W Y π M) (hM : M = mat ∨ M = dmat) {B : Subgroup (MulAut V)}
    (hBL : B ≤ L) (hB2 : IsPGroup 2 ↥B) (hBne : B ≠ ⊥) (hn : 1 ≤ n) :
    rk B ≤ (n - 1) * rkIdx (fixV (autSec B W Y)) ∧ 1 ≤ rkIdx (fixV (autSec B W Y)) := by
  have hπ : Function.Bijective π := ⟨h.injective hM, h.1⟩
  have hidx := h.rkIdx_fixV_autSec hBL
  have hlt := finrank_fixM_lt hπ hM hBL hBne
  have hB2' := isPGroup_pre hπ hB2
  have hmul := rk_le_mul_pre hπ hBL hB2
  have hD := finrank_fixD_add (pre π B)
  refine ⟨?_, by omega⟩
  rw [hidx]
  rcases hM with rfl | rfl
  ·
    have hfD : 1 ≤ finrank (ZMod 2) (fixD (pre π B)) := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      exact fixD_ne_bot_of_isPGroup hB2' hn (Submodule.finrank_eq_zero.1 h0)
    rw [fixM_mat] at hlt ⊢
    calc rk B ≤ (n - finrank (ZMod 2) (fixN (pre π B))) * finrank (ZMod 2) (commN (pre π B)) :=
          hmul
      _ ≤ (n - finrank (ZMod 2) (fixN (pre π B))) * (n - 1) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = (n - 1) * (n - finrank (ZMod 2) (fixN (pre π B))) := Nat.mul_comm _ _
  · have hfN : 1 ≤ finrank (ZMod 2) (fixN (pre π B)) := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      exact fixN_ne_bot_of_isPGroup hB2' hn (Submodule.finrank_eq_zero.1 h0)
    rw [fixM_dmat] at hlt ⊢
    have he : n - finrank (ZMod 2) (fixD (pre π B)) = finrank (ZMod 2) (commN (pre π B)) := by
      omega
    rw [he]
    calc rk B ≤ (n - finrank (ZMod 2) (fixN (pre π B))) * finrank (ZMod 2) (commN (pre π B)) :=
          hmul
      _ ≤ (n - 1) * finrank (ZMod 2) (commN (pre π B)) := Nat.mul_le_mul_right _ (by omega)

end RealBounds

end CFSG.Quasithin.B5.Ln
