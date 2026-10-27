module

public import CFSG.Quasithin.Background.SmithD37ClsDefs
public import CFSG.Quasithin.Background.SmithB45SzNat
public import CFSG.Quasithin.Background.SmithB45ExcJ1
public import CFSG.Quasithin.Background.SmithB45ExcL2Cover
public import CFSG.Quasithin.Background.SmithB45SL3L32
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddClassical
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.SmithD37

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor

namespace ClsSz

section Bridge

variable {Q : Type} [CommGroup Q] {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

@[expose] def toEnd (θ : Q ≃* Multiplicative M) (φ : Q →* Q) : Module.End (ZMod 2) M :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun w => Multiplicative.toAdd (θ (φ (θ.symm (Multiplicative.ofAdd w))))
      map_zero' := by simp
      map_add' := fun x y => by simp [ofAdd_add] }

@[expose] def ofEnd (θ : Q ≃* Multiplicative M) (f : Module.End (ZMod 2) M) : Q →* Q where
  toFun v := θ.symm (Multiplicative.ofAdd (f (Multiplicative.toAdd (θ v))))
  map_one' := by simp
  map_mul' x y := by simp [toAdd_mul]

theorem toEnd_apply (θ : Q ≃* Multiplicative M) (φ : Q →* Q) (w : M) :
    toEnd θ φ w = Multiplicative.toAdd (θ (φ (θ.symm (Multiplicative.ofAdd w)))) := rfl

theorem ofEnd_apply (θ : Q ≃* Multiplicative M) (f : Module.End (ZMod 2) M) (v : Q) :
    ofEnd θ f v = θ.symm (Multiplicative.ofAdd (f (Multiplicative.toAdd (θ v)))) := rfl

@[expose] def endEquiv (θ : Q ≃* Multiplicative M) : (Q →* Q) ≃ Module.End (ZMod 2) M where
  toFun := toEnd θ
  invFun := ofEnd θ
  left_inv φ := by
    ext v
    simp [toEnd_apply, ofEnd_apply]
  right_inv f := by
    ext w
    simp [toEnd_apply, ofEnd_apply]

theorem comm_iff (θ : Q ≃* Multiplicative M) (φ : Q →* Q) (l : MulAut Q) :
    (∀ v, φ (l v) = l (φ v)) ↔ ∀ w, toEnd θ φ (binPsi θ l w) = binPsi θ l (toEnd θ φ w) := by
  constructor
  · intro h w
    simp [toEnd_apply, binPsi_apply, h]
  · intro h v
    have h1 := h (Multiplicative.toAdd (θ v))
    simp only [toEnd_apply, binPsi_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply] at h1
    exact θ.injective (Multiplicative.toAdd.injective h1)

theorem endCard_eq {Γ : Type} [Group Γ] (θ : Q ≃* Multiplicative M) {L : Subgroup (MulAut Q)}
    (π : Γ →* ↥L) (hπ : Function.Surjective π) :
    endCard L = Nat.card (EndRing (B45Sz.repOfG
      ((binPsi θ).toMonoidHom.comp (L.subtype.comp π)))) := by
  rw [natCard_endRing]
  refine Nat.card_congr ((endEquiv θ).subtypeEquiv fun φ => ?_)
  constructor
  · intro h g w
    exact (comm_iff θ φ _).mp (h _ (π g).2) w
  · intro h l hl
    obtain ⟨g, hg⟩ := hπ ⟨l, hl⟩
    refine (comm_iff θ φ l).mpr fun w => ?_
    have h1 := h g w
    simp only [B45Sz.repOfG_apply, MonoidHom.coe_comp, Function.comp_apply, hg,
      Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, LinearEquiv.coe_coe] at h1
    exact h1

end Bridge

section Basic

theorem center_eq_bot {X : Type} [Group X] (hq : CFSG.IsQuasisimple X) (hs : IsSimpleGroup X) :
    Subgroup.center X = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    apply hab
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    have hx : x ∈ Subgroup.center X := h ▸ Subgroup.mem_top x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hx y]

@[expose] noncomputable def quotCenterEquiv {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) :
    X ⧸ Subgroup.center X ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

variable {Q : Type} [CommGroup Q] [Finite Q]

theorem card_sq_mul_le_of_two_le (hW : ∀ w : Q, w ^ 2 = 1) {X A : Subgroup (MulAut Q)}
    (hA : IsA2 X A) (hr : (2 : ℚ) ≤ rAV A) :
    Nat.card A ^ 2 * Nat.card (fixV A) ≤ Nat.card Q := by
  have hmul := hA.rAV_mul
  have hpos : (0 : ℚ) < (rk A : ℚ) := by exact_mod_cast hA.rk_pos
  have h1 : 2 * rk A ≤ rkIdx (fixV A) := by
    have := mul_le_mul_of_nonneg_right hr hpos.le
    rw [hmul] at this
    exact_mod_cast this
  have hadd := rk_add_rkIdx (fixV A)
  have cW : Nat.card Q = 2 ^ rk Q := card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW)
  have cF : Nat.card (fixV A) = 2 ^ rk (fixV A) := card_eq_two_pow hW (fixV A)
  have cA : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hA.isElemAbelian2.isPGroup
  rw [cW, cF, cA, ← pow_mul, ← pow_add, Nat.pow_le_pow_iff_right (by norm_num)]
  omega

theorem le_normalizer {G L E : Subgroup (MulAut Q)} (h : Cls2F G L E) :
    E ≤ Subgroup.normalizer (L : Set (MulAut Q)) :=
  h.a2.1.trans (B45Sz.b4Hyp_data h.hyp).2.2.2.2

end Basic

section Suzuki

open CFSG.Blueprint

variable {Q : Type} [CommGroup Q] [Finite Q]

theorem sz_endCard_card (hW : ∀ v : Q, v * v = 1)
    {L : Subgroup (MulAut Q)} (hirr : ∀ U : Subgroup Q, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {a : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : ↥L ≃* suzukiGroup a K) {t : MulAut Q} (htL : t ∈ L) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hidx : (fixV (Subgroup.zpowers t)).index ≤ 2 ^ (2 * (2 * a + 1))) :
    endCard L = 2 ^ (2 * a + 1) ∧ Nat.card Q = 2 ^ (4 * (2 * a + 1)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := X7b.charP_two_of_card_pow hK
  obtain ⟨M, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hW
  let π : ↥(suzukiGroup a K) →* (M ≃ₗ[ZMod 2] M) :=
    (binPsi θ).toMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom)
  have hπ : ∀ g, π g = binPsi θ ((e.symm g : ↥L) : MulAut Q) := fun g => rfl
  have hirrM : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, B45Sz.repOfG π g u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirr U fun x hx u hu => ?_
    obtain ⟨l, hl, rfl⟩ := hx
    have h1 := hU (e ⟨l, hl⟩) u hu
    rwa [B45Sz.repOfG_apply, hπ, MulEquiv.symm_apply_apply] at h1
  have hntQ : Nontrivial Q := by
    by_contra hQ
    rw [not_nontrivial_iff_subsingleton] at hQ
    exact ht1 (MulEquiv.ext fun x => Subsingleton.elim _ _)
  have hntM : Nontrivial M := by
    obtain ⟨w, hw⟩ := exists_ne (1 : Q)
    refine ⟨⟨Multiplicative.toAdd (θ w), 0, fun h => hw ?_⟩⟩
    have h1 : θ w = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  have : Fact (B45Sz.repOfG π).IsIrreducible :=
    ⟨(X7.isIrreducible_iff (B45Sz.repOfG π)).mpr ⟨hntM, hirrM⟩⟩
  set t₀ : ↥(suzukiGroup a K) := e ⟨t, htL⟩ with ht₀
  have ht₀2 : t₀ * t₀ = 1 := by
    rw [ht₀, ← map_mul]
    have : (⟨t, htL⟩ : ↥L) * ⟨t, htL⟩ = 1 := Subtype.ext ht2
    rw [this, map_one]
  have ht₀1 : t₀ ≠ 1 := by
    intro h
    apply ht1
    have := congrArg (fun g => ((e.symm g : ↥L) : MulAut Q)) h
    simpa [ht₀] using this
  have hπt : π t₀ = binPsi θ t := by rw [hπ, ht₀, MulEquiv.symm_apply_apply]
  have hnt : ∃ g, B45Sz.repOfG π g ≠ 1 := by
    refine ⟨t₀, fun h => ht1 ?_⟩
    have h1 : π t₀ = 1 :=
      LinearEquiv.toLinearMap_injective (by rw [← B45Sz.repOfG_apply, h]; rfl)
    rw [hπt] at h1
    exact (binPsi θ).injective (h1.trans (map_one (binPsi θ)).symm)
  have hsmall : Module.finrank (ZMod 2) (LinearMap.range (B45Sz.repOfG π t₀ - 1)) ≤
      2 * (2 * a + 1) := by
    rw [B45Sz.index_fixV_zpowers_eq θ t] at hidx
    rw [B45Sz.repOfG_apply, hπt]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hidx
  have hdim := B45Sz.sz_finrank_eq_four_of_small hK π hnt ht₀2 ht₀1 hsmall
  obtain ⟨c, ι, θ', hact⟩ := B45Sz.sz_coords_of_four hK π hnt hdim
  obtain ⟨-, hirr'⟩ := (X7.isIrreducible_iff (B45Sz.repOfG π)).mp Fact.out
  have hsurj := B45Sz.surjective_of_coords π (fun U hU => hirr' U hU) ι 0 _ θ' hact
  have hD : Nat.card (EndRing (B45Sz.repOfG π)) = 2 ^ (2 * a + 1) := by
    rw [← hK]
    exact (Nat.card_congr (RingEquiv.ofBijective ι ⟨ι.injective, hsurj⟩).toEquiv).symm
  refine ⟨?_, ?_⟩
  · rw [endCard_eq θ e.symm.toMonoidHom e.symm.surjective]
    exact hD
  · rw [natCard_eq θ, natCard_eq_pow_finrank (ρ := B45Sz.repOfG π), hD, hdim, ← pow_mul,
      mul_comm]

theorem card_le_of_sz [Nontrivial Q]
    (hW : ∀ v : Q, v * v = 1) {L E : Subgroup (MulAut Q)} (hperf : Group.IsPerfect ↥L)
    (hirr : ∀ U : Subgroup Q, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : ↥L ⧸ Subgroup.center ↥L ≃* suzukiGroup a K) (e : ↥L ≃* suzukiGroup a K)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut Q))) (hEel : IsElemAbelian2 E) :
    E ≤ L ∧ Nat.card E ≤ 2 ^ (2 * a + 1) := by
  obtain ⟨-, -, hP, -, -⟩ :=
    Family.suzuki_irreducible_normalizer_excludes a ha hK Q hW L hperf hirr α
  have hEL : E ≤ L := hP E hEel.isPGroup hEN
  refine ⟨hEL, ?_⟩
  have h1 := Family.suzuki_exponent_two_card_le hK ((E.subgroupOf L).map e.toMonoidHom) (by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (by
      have := hEel.2 _ (Subgroup.mem_subgroupOf.mp hx)
      simpa [sq] using this)
    rw [this, map_one])
  rw [Subgroup.card_map_of_injective e.injective] at h1
  have h2 : Nat.card (E.subgroupOf L) = Nat.card E := by
    rw [← Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hEL]
  omega

end Suzuki

section Eight

variable {Q : Type} [CommGroup Q] {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem exists_mul_ne {X : Type} [Group X] (hq : CFSG.IsQuasisimple X) :
    ∃ x y : X, x * y ≠ y * x := by
  obtain ⟨a, b, hab⟩ := hq.2.2
  induction a using QuotientGroup.induction_on with | H x => ?_
  induction b using QuotientGroup.induction_on with | H y => ?_
  exact ⟨x, y, fun hxy => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy])⟩

theorem endCard_eq_two (θ : Q ≃* Multiplicative M) {L : Subgroup (MulAut Q)}
    (hirr : ∀ U : Subgroup Q, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnc : ∃ x y : ↥L, x * y ≠ y * x) (h8 : Nat.card M = 8) : endCard L = 2 := by
  classical
  let π : ↥L →* (M ≃ₗ[ZMod 2] M) := (binPsi θ).toMonoidHom.comp (L.subtype.comp (MonoidHom.id _))
  have hπ : ∀ l, π l = binPsi θ (l : MulAut Q) := fun _ => rfl
  have hntM : Nontrivial M := by
    rw [← Finite.one_lt_card_iff_nontrivial, h8]
    norm_num
  have hirrM : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, B45Sz.repOfG π g u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirr U fun x hx u hu => ?_
    obtain ⟨l, hl, rfl⟩ := hx
    exact hU ⟨l, hl⟩ u hu
  have : Fact (B45Sz.repOfG π).IsIrreducible :=
    ⟨(X7.isIrreducible_iff (B45Sz.repOfG π)).mpr ⟨hntM, hirrM⟩⟩
  rw [endCard_eq θ (MonoidHom.id _) Function.surjective_id]
  let D := EndRing (B45Sz.repOfG π)
  have hfin : Finite D := finite_endRing _
  let k := Module.finrank D M
  have hcard : 8 = Nat.card D ^ k := h8 ▸ natCard_eq_pow_finrank (ρ := B45Sz.repOfG π)
  have hD2 : 2 ≤ Nat.card D := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  change Nat.card D = 2
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hcard
      norm_num at hcard
    · exact h0
  by_contra hne
  have hD3 : 3 ≤ Nat.card D := by omega
  have hk1' : k = 1 := by
    by_contra hk2
    have h9 : 3 ^ 2 ≤ Nat.card D ^ k :=
      (Nat.pow_le_pow_left hD3 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  apply Subtype.ext
  apply (binPsi θ).injective
  have : Module.Free D M := Module.Free.of_divisionRing D M
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hk1' (repD _ x)
  obtain ⟨d, hd, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hk1' (repD _ y)
  refine LinearEquiv.ext fun w => ?_
  have hx : ∀ v, binPsi θ (x : MulAut Q) v = c • v := fun v => by
    change repD (B45Sz.repOfG π) x v = c • v
    rw [hc]
    rfl
  have hy : ∀ v, binPsi θ (y : MulAut Q) v = d • v := fun v => by
    change repD (B45Sz.repOfG π) y v = d • v
    rw [hd]
    rfl
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, hx, hy, hx, hy, smul_smul, smul_smul, mul_comm]

end Eight

section L32

open B45L32 B42L2 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.Family
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

variable {Q : Type} [CommGroup Q] [Finite Q] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W]

theorem false_of_finrank_eight {G L E : Subgroup (MulAut Q)} (h : Cls2F G L E)
    (θ : Q ≃* Multiplicative W) (eL : ↥L ≃* GL32) (hZ : Subgroup.center ↥L = ⊥)
    (h8 : Module.finrank (ZMod 2) W = 8) : False := by
  classical
  have hHyp := h.hyp
  have hoff := h.off
  have hA := h.a2
  obtain ⟨-, -, hirr, hLG, -⟩ := B45Sz.b4Hyp_data hHyp
  have : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  have : Nontrivial W := by
    rw [← Module.finrank_pos_iff (R := ZMod 2), h8]
    norm_num
  set Φ := unitsPsi θ with hΦ
  have hcardW : Nat.card Q = 2 ^ 8 := by
    rw [natCard_eq θ, H13.NQTerm.card_eq_two_pow_finrank (M := W), h8]
  have hfixeq : Nat.card ↥(LocalAnalysis.CommutingFactor.fixedSub (E.map Φ.toMonoidHom)) =
      Nat.card ↥(fixV E) := natCard_fixedSub_map θ E
  have hcardA : Nat.card (E.map Φ.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective Φ.injective
  obtain ⟨hAc, hA2⟩ := comm_map_unitsPsi θ hA.2.2
  have hfaith : ∀ d ∈ G.map Φ.toMonoidHom,
      (∀ v ∈ (⊤ : Submodule (ZMod 2) W), (d : Module.End (ZMod 2) W) v = v) → d = 1 := by
    rintro _ ⟨φ, -, rfl⟩ h
    rw [eq_one_of_unitsPsi θ fun w => h w Submodule.mem_top]
    exact map_one _
  let eY : ↥(L.map Φ.toMonoidHom) ≃* GL32 :=
    (L.equivMapOfInjective Φ.toMonoidHom Φ.injective).symm.trans eL
  by_cases hGL : G = L
  ·
    subst hGL
    have hIirr : ∀ U ≤ (⊤ : Submodule (ZMod 2) W), (∀ d ∈ G.map Φ.toMonoidHom, ∀ v ∈ U,
        (d : Module.End (ZMod 2) W) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro U _ hU
      refine irr_map θ hirr U ?_
      rintro _ ⟨l, hl, rfl⟩ u hu
      have h1 := hU (Φ l) ⟨l, hl, rfl⟩ u hu
      rw [hΦ, unitsPsi_apply] at h1
      exact h1
    have hcases := H13.NQTerm.gl3_cases (I := ⊤) (fun _ _ _ _ => Submodule.mem_top)
      top_ne_bot hIirr hfaith le_rfl le_rfl eY
      (Subgroup.map_mono hA.1) (map_unitsPsi_ne_bot θ hA.2.1) hAc hA2 (a := rk ↥E)
      (by rw [hcardA, B1.card_elemAbelian hA.2.2])
    rw [top_inf_eq, finrank_top, h8] at hcases
    have hfixW : Nat.card ↥(LocalAnalysis.CommutingFactor.fixedSub (E.map Φ.toMonoidHom)) =
        2 ^ Module.finrank (ZMod 2)
          ↥(LocalAnalysis.CommutingFactor.fixedSub (E.map Φ.toMonoidHom)) :=
      H13.NQTerm.card_eq_two_pow_finrank
    rw [B1.card_elemAbelian hA.2.2, ← hfixeq, hfixW, hcardW, ← pow_mul, ← pow_add] at hoff
    have hle := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hoff
    rcases hcases with ⟨h3, -⟩ | ⟨-, h | h⟩
    · omega
    · obtain ⟨h1, h2⟩ := h
      omega
    · obtain ⟨h1, h2⟩ := h
      omega
  ·
    obtain ⟨hLG', hLn, hself, -⟩ := FFC.b4hyp_data hHyp
    obtain ⟨g, hgG, hgL⟩ : ∃ g ∈ G, g ∉ L := by
      by_contra hcon
      push Not at hcon
      exact hGL (le_antisymm hcon hLG')
    have hYn : ∀ d ∈ G.map Φ.toMonoidHom, ∀ y ∈ L.map Φ.toMonoidHom,
        d * y * d⁻¹ ∈ L.map Φ.toMonoidHom := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨l, hl, rfl⟩
      exact ⟨x * l * x⁻¹, hLn x hx l hl, by simp⟩
    have hCY : ∀ d ∈ G.map Φ.toMonoidHom,
        (∀ y ∈ L.map Φ.toMonoidHom, d * y = y * d) → d = 1 := by
      rintro _ ⟨x, hx, rfl⟩ h
      have hc : ∀ l ∈ L, x * l = l * x := fun l hl =>
        Φ.injective (by rw [map_mul, map_mul]; exact h _ ⟨l, hl, rfl⟩)
      have hxL := hself x hx hc
      have hcen : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (hc y y.2).symm
      rw [hZ, Subgroup.mem_bot] at hcen
      have : x = 1 := congrArg Subtype.val hcen
      rw [this]
      exact map_one _
    have hd₀Y : Φ g ∉ L.map Φ.toMonoidHom := by
      rintro ⟨l, hl, hlg⟩
      exact hgL (Φ.injective hlg ▸ hl)
    have hirrD : ∀ U : Submodule (ZMod 2) W, (∀ d ∈ G.map Φ.toMonoidHom, ∀ v ∈ U,
        (d : Module.End (ZMod 2) W) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro U hU
      refine irr_map θ hirr U ?_
      rintro _ ⟨l, hl, rfl⟩ u hu
      have h1 := hU (Φ l) ⟨l, hLG' hl, rfl⟩ u hu
      rw [hΦ, unitsPsi_apply] at h1
      exact h1
    have hlt := card_sq_mul_lt_of_not_le hirrD h8 (Subgroup.map_mono hLG') hYn eY hCY
      (Subgroup.map_mono hA.1) (map_unitsPsi_ne_bot θ hA.2.1) hAc hA2 ⟨g, hgG, rfl⟩ hd₀Y
    rw [hcardA, hfixeq, ← natCard_eq θ] at hlt
    omega

theorem l32_endCard_card {G L E : Subgroup (MulAut Q)} (h : Cls2F G L E) (eL : ↥L ≃* GL32)
    (hZ : Subgroup.center ↥L = ⊥) : endCard L = 2 ∧ Nat.card Q = 2 ^ 3 := by
  classical
  have hW : ∀ v : Q, v * v = 1 := fun v => by rw [← pow_two]; exact h.exp v
  obtain ⟨M, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hW
  obtain ⟨hnt, -, hirr, -, -⟩ := B45Sz.b4Hyp_data h.hyp
  have hntM : Nontrivial M := by
    obtain ⟨w, hw⟩ := exists_ne (1 : Q)
    refine ⟨⟨Multiplicative.toAdd (θ w), 0, fun h => hw ?_⟩⟩
    have h1 : θ w = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  rcases finrank_eq_three_or_eight θ hirr eL with h3 | h8
  · have hcard : Nat.card M = 8 := by
      rw [H13.NQTerm.card_eq_two_pow_finrank (M := M), h3]
      norm_num
    obtain ⟨x, y, hxy⟩ := exists_mul_ne h.hyp.2.2.1
    refine ⟨endCard_eq_two θ hirr ⟨x, y, hxy⟩ hcard, ?_⟩
    rw [natCard_eq θ, hcard]
    norm_num
  · exact (false_of_finrank_eight h θ eL hZ h8).elim

end L32

end ClsSz

open ClsSz

theorem cls2F_sz
    {Q : Type} [CommGroup Q] [Finite Q] {G L E : Subgroup (MulAut Q)}
    (h : Cls2F G L E) {f : ℕ} (hf : IsSz f ↥L) :
    endCard L = 2 ^ f ∧ Nat.card Q = 2 ^ (4 * f) ∧ Nat.card E ≤ 2 ^ f ∧
      Nat.card E ^ 2 * Nat.card (fixV E) ≤ Nat.card Q := by
  have hf' := hf
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hf'
  obtain ⟨hnt, hperf, hirr, hLG, hGN⟩ := B45Sz.b4Hyp_data h.hyp
  have hW : ∀ v : Q, v * v = 1 := fun v => by rw [← pow_two]; exact h.exp v
  have hZ : Subgroup.center ↥L = ⊥ :=
    center_eq_bot h.hyp.2.2.1 (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 _ hf).2
  let α : ↥L ⧸ Subgroup.center ↥L ≃* CFSG.Blueprint.suzukiGroup a K :=
    (quotCenterEquiv hZ).trans e
  obtain ⟨t, htL, ht2, ht1, hidx⟩ := B45Sz.exists_small_involution h.exp h.hyp ha hK α h.a2 h.off
  obtain ⟨hend, hcard⟩ := sz_endCard_card hW hirr hK e htL ht2 ht1 hidx
  have hnat := szNaturalOfSmallDisplacement_holds a ha K hK Q hW L hperf hirr ⟨α⟩
    ⟨t, htL, ht2, ht1, hidx⟩
  obtain ⟨-, hqh⟩ := B45Sz.qOf_qhatOf_eq_two hLG hGN hnat
  have hr : (2 : ℚ) ≤ rAV E := le_kq_iff.mp (le_of_eq hqh.symm) E h.a2 h.cubic
  exact ⟨hend, hcard, (card_le_of_sz hW hperf hirr ha hK α e (h.a2.1.trans hGN)
    h.a2.isElemAbelian2).2, card_sq_mul_le_of_two_le h.exp h.a2 hr⟩

theorem cls2F_j1 {Q : Type} [CommGroup Q] [Finite Q]
    {G L E : Subgroup (MulAut Q)} (h : Cls2F G L E) (hJ : IsSporadic .J1 ↥L) : False := by
  obtain ⟨e⟩ := hJ
  have hW : ∀ v : Q, v * v = 1 := fun v => by rw [← pow_two]; exact h.exp v
  have hs : IsSimpleGroup ↥L := by
    have := CFSG.Walter.J1Props.J1_simple
    exact (e.trans CFSG.Walter.walterJ1EquivNative.symm).isSimpleGroup
  have hZ := center_eq_bot h.hyp.2.2.1 hs
  obtain ⟨hnt, -, hirr, -, -⟩ := B45Sz.b4Hyp_data h.hyp
  have hlt := B45Exc.sporadicExclusion2F_J1 Q hW L E h.hyp.2.2.1 ⟨hnt, hirr⟩
    ⟨(quotCenterEquiv hZ).trans e⟩ (le_normalizer h) h.a2.2.1 h.a2.2.2
  exact absurd h.off (not_le.mpr hlt)

theorem cls2F_psl2_prime
    {Q : Type} [CommGroup Q] [Finite Q] {G L E : Subgroup (MulAut Q)}
    (h : Cls2F G L E) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hL : IsPSL 2 p 1 ↥L) :
    p = 7 ∧ endCard L = 2 ∧ Nat.card Q = 2 ^ 3 := by
  obtain ⟨hnt, hperf, hirr, -, -⟩ := B45Sz.b4Hyp_data h.hyp
  have hW : ∀ v : Q, v * v = 1 := fun v => by rw [← pow_two]; exact h.exp v
  have hZ : Subgroup.center ↥L = ⊥ :=
    center_eq_bot h.hyp.2.2.1 (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hL).2
  by_cases hp11 : 11 ≤ p
  · exfalso
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨α⟩ := Family.equiv_projectiveSL_of_model hL
    have hlt := B45Exc.primeLinearTwoExclusion2F hp11 hW hperf hirr
      ((quotCenterEquiv hZ).trans α) E (le_normalizer h) h.a2.2.1 h.a2.2.2
    exact absurd h.off (not_le.mpr hlt)
  · have h7 : p = 7 := by
      have hp10 : p ≤ 10 := by omega
      interval_cases p
      · rfl
      all_goals norm_num at hp
    subst h7
    obtain ⟨eS⟩ := Family.equiv_SL3_two_of_model_seven hL
    exact ⟨rfl, l32_endCard_card h (eS.trans B42L2.slEquivGL32) hZ⟩

end CFSG.Quasithin.SmithD37
