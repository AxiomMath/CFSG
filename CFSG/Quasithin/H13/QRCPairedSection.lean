module

public import CFSG.Quasithin.H13.QRCPairedQuotient

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups
  CFSG.GorensteinWalter CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Statement

variable {A : Type*} [Group A] {k : Type} [Field k]

@[expose] def ActsAsFieldP {X Y : Subgroup A} (θ : X ≃* projectiveSL 2 k)
    (θ' : Y ≃* projectiveSL 2 k) (a : A) (σ : RingAut k) : Prop :=
  X.map (MulAut.conj a).toMonoidHom = Y ∧ ∀ (x : X) (y : Y) (g : SL(2, k)),
    (y : A) = a * x * a⁻¹ → θ x = proj 2 k g →
      θ' y = proj 2 k (Matrix.SpecialLinearGroup.map σ.toRingHom g)

@[expose] def IsFieldPermP {K₁ K₂ : Subgroup A} (θ₁ : K₁ ≃* projectiveSL 2 k)
    (θ₂ : K₂ ≃* projectiveSL 2 k) (a : A) : Prop :=
  ∃ σ₁ σ₂ : RingAut k, (ActsAsFieldP θ₁ θ₁ a σ₁ ∧ ActsAsFieldP θ₂ θ₂ a σ₂) ∨
    (ActsAsFieldP θ₁ θ₂ a σ₁ ∧ ActsAsFieldP θ₂ θ₁ a σ₂)

variable [CharP k 2]

theorem ActsAsField.toP {X Y : Subgroup A} {θ : X ≃* SL(2, k)} {θ' : Y ≃* SL(2, k)} {a : A}
    {σ : RingAut k} (h : ActsAsField θ θ' a σ) :
    ActsAsFieldP (θ.trans projSLEquiv) (θ'.trans projSLEquiv) a σ := by
  refine ⟨h.1, fun x y g hy hx => ?_⟩
  simp only [MulEquiv.trans_apply] at hx ⊢
  rw [← projSLEquiv_apply] at hx
  rw [h.2 x y hy, projSLEquiv.injective hx, projSLEquiv_apply]

theorem IsFieldPerm.toP {K₁ K₂ : Subgroup A} {θ₁ : K₁ ≃* SL(2, k)} {θ₂ : K₂ ≃* SL(2, k)}
    {a : A} (h : IsFieldPerm θ₁ θ₂ a) :
    IsFieldPermP (θ₁.trans projSLEquiv) (θ₂.trans projSLEquiv) a := by
  obtain ⟨σ₁, σ₂, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := h
  · exact ⟨σ₁, σ₂, Or.inl ⟨h₁.toP, h₂.toP⟩⟩
  · exact ⟨σ₁, σ₂, Or.inr ⟨h₁.toP, h₂.toP⟩⟩

theorem map_projSLEquiv_symm_projUnitriangular :
    (projUnitriangular 2 k).map (projSLEquiv (k := k)).symm.toMonoidHom =
      sl2UpperUnipotentSubgroup k := by
  rw [← unitriangular_two_eq_sl2UpperUnipotent, projUnitriangular, map_map]
  convert map_id (unitriangular 2 k)
  ext g
  simp [← projSLEquiv_apply]

theorem map_projSLEquiv_symm_projUpperTriangular :
    (projUpperTriangular 2 k).map (projSLEquiv (k := k)).symm.toMonoidHom = sl2Borel k := by
  rw [← upperTriangular_two_eq_sl2Borel, projUpperTriangular, map_map]
  convert map_id (upperTriangular 2 k)
  ext g
  simp [← projSLEquiv_apply]

theorem stdSub_projSL {X : Subgroup A} (θ : X ≃* SL(2, k)) (Z : Subgroup (projectiveSL 2 k))
    (Z' : Subgroup SL(2, k)) (hZ : Z.map (projSLEquiv (k := k)).symm.toMonoidHom = Z') :
    (Z.map (θ.trans projSLEquiv).symm.toMonoidHom).map X.subtype = stdSub θ Z' := by
  rw [stdSub, ← hZ, map_map, map_map, map_map]
  rfl

end Statement

section Main

variable {H : Type} [Group H] [Finite H]

theorem qrc_paired_even_linear_sections_produce_original_pair_with_full_second_projection_core
    (hns : ¬ Group.IsSolvable H) (hchar : IsCharacteristicP 2 H) (T : Sylow 2 H)
    (hTn : ¬ (T : Subgroup H).Normal) {M : Subgroup H} (hTM : (T : Subgroup H) ≤ M)
    (hMH : M < ⊤) (hmax : ∀ Y : Subgroup H, (T : Subgroup H) ≤ Y → Y < ⊤ → Y ≤ M)
    {V : Subgroup H} [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H)) (hVM : V ≤ inSubgroup (pCore 2) M)
    (hVQ : 4 ≤ (V ⊓ pCore 2 H).relIndex V) {n : ℕ} {k : Type} [Field k]
    (hk : Nat.card k = 2 ^ n) (hn : 2 ≤ n) {K₁ K₂ : Subgroup (H ⧸ kerIn M ⊤)}
    (hK : (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)) = K₁ ⊔ K₂)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥)
    (hK₁ : Nonempty (K₁ ≃* projectiveSL 2 k)) (hK₂ : Nonempty (K₂ ≃* projectiveSL 2 k)) :
    let D := kerIn M ⊤
    let π := QuotientGroup.mk' D
    let Q := pCore 2 H
    let S := (T : Subgroup H).map π
    let B := M.map π
    let E := V.map π
    let E₁ := (E ⊔ K₂) ⊓ K₁
    let E₂ := (E ⊔ K₁) ⊓ K₂
    (∃ ι : H ⧸ D →* MulAut ↥(K₁ ⊔ K₂), Function.Injective ι ∧
      ∀ a x, (ι a x : H ⧸ D) = a * x * a⁻¹) ∧
    ∃ (R : Subgroup (H ⧸ D)) (θ₁ : K₁ ≃* projectiveSL 2 k) (θ₂ : K₂ ≃* projectiveSL 2 k),
      let U₁ := ((projUnitriangular 2 k).map θ₁.symm.toMonoidHom).map K₁.subtype
      let U₂ := ((projUnitriangular 2 k).map θ₂.symm.toMonoidHom).map K₂.subtype
      let B₁ := ((projUpperTriangular 2 k).map θ₁.symm.toMonoidHom).map K₁.subtype
      let B₂ := ((projUpperTriangular 2 k).map θ₂.symm.toMonoidHom).map K₂.subtype
      IsPGroup 2 R ∧ (K₁ ⊔ K₂) ⊓ R = ⊥ ∧ (K₁ ⊔ K₂) ⊔ R = ⊤ ∧
      (∀ r ∈ R, IsFieldPermP θ₁ θ₂ r) ∧ (∃ r ∈ R, K₁.map (MulAut.conj r).toMonoidHom = K₂) ∧
      S = U₁ ⊔ U₂ ⊔ R ∧ B = B₁ ⊔ B₂ ⊔ R ∧ E ≤ U₁ ⊔ U₂ ∧
      ∃ r : ℕ, 1 ≤ r ∧ Nat.card E₁ = 2 ^ r ∧ Nat.card E₂ = 2 ^ r ∧
      ∃ (L₁ : Subgroup (H ⧸ D)) (g : H),
        let I := V ⊔ conjugate V g
        let H₀ := (L₁ ⊔ E₂).comap π
        let RI := I ⊓ Q
        let J := I ⊓ E₂.comap π
        L₁ ≤ K₁ ∧ π g ∈ L₁ ∧ L₁ = E₁ ⊔ conjugate E₁ (π g) ∧ g ∈ I ∧
        I ≤ oddResidualPreimage H ∧ V < I ∧ I.map π = L₁ ⊔ E₂ ∧
        L₁ ⊔ E₂ = E ⊔ conjugate E (π g) ∧ IsSylowOf 2 (U₁ ⊓ L₁) L₁ ∧
        (2 ≤ r → ∃ m : ℕ, 2 ≤ m ∧ r ≤ m ∧ m ∣ n ∧ ∃ (k' : Type) (_ : Field k'),
          Nat.card k' = 2 ^ m ∧ ∃ e : L₁ ≃* projectiveSL 2 k',
            ((B₁ ⊓ L₁).subgroupOf L₁).map e.toMonoidHom = projUpperTriangular 2 k' ∧
            ((U₁ ⊓ L₁).subgroupOf L₁).map e.toMonoidHom = projUnitriangular 2 k') ∧
        (r = 1 → Nat.card E = 4 ∧ E = E₁ ⊔ E₂ ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
          Nonempty (L₁ ≃* DihedralGroup p) ∧ B₁ ⊓ L₁ = E₁ ∧ U₁ ⊓ L₁ = E₁) ∧
        H₀ = D ⊔ I ∧ (I.subgroupOf (Q ⊔ I)).Normal ∧ Q ⊔ I ≤ H₀ ∧
        ((Q ⊔ I).subgroupOf H₀).Normal ∧ Q ≤ normalizer (I : Set H) ∧ ⁅D, I⁆ ≤ Q ∧
        IsSylowOf 2 ((T : Subgroup H) ⊓ I) I ∧ I ⊓ D = RI ∧
        (∃ θ : I →* ↥L₁ × ↥E₂, Function.Surjective θ ∧ θ.ker = RI.subgroupOf I ∧
          ∀ i : I, π (i : H) = ((θ i).1 : H ⧸ D) * (θ i).2) ∧
        J = kerIn (M ⊓ I) I ∧ J = inSubgroup (pCore 2) I ∧
        (∃ κ : J →* E₂, Function.Surjective κ ∧ κ.ker = RI.subgroupOf J ∧
          ∀ j : J, π (j : H) = κ j) ∧ E₂ ≠ ⊥ ∧
        inSubgroup (pCore 2) (Q ⊔ I) = Q ⊔ J ∧ IsCharacteristicP 2 I ∧
        inSubgroup (pCore 2) (M ⊓ I) = (T : Subgroup H) ⊓ I ∧
        I ⊓ normalizer (V : Set H) ≤ M ⊓ I ∧
        ∃ ψ : I →* L₁, Function.Surjective ψ ∧ ψ.ker = J.subgroupOf I ∧
          (∀ i : I, ∃ a ∈ E₂, π (i : H) = (ψ i : H ⧸ D) * a) ∧
          ((M ⊓ I).subgroupOf I).map ψ = (B₁ ⊓ L₁).subgroupOf L₁ ∧
          (((T : Subgroup H) ⊓ I).subgroupOf I).map ψ = (U₁ ⊓ L₁).subgroupOf L₁ ∧
          (V.subgroupOf I).map ψ = E₁.subgroupOf L₁ ∧ E₁ ≤ U₁ ⊓ L₁ ∧
          (∀ v ∈ E₁, ∀ u ∈ U₁ ⊓ L₁, v * u = u * v) ∧ (V ⊓ J).relIndex V = 2 ^ r := by
  intro D π Q S B E E₁ E₂
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := LinearModel.charP_two_of_card hk
  obtain ⟨-, -, hDK₀, hKn, hCK, hKS, ⟨hSB, hBtop, hBmax⟩, -, hEcard, hEO⟩ :=
    bender_section_setup hns T hTn hTM hMH hmax hVT hVM
  rw [hK] at hKn hCK hKS
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hπker : π.ker = D := QuotientGroup.ker_mk' D
  have := hKn
  obtain ⟨φ₁⟩ := hK₁
  obtain ⟨φ₂⟩ := hK₂
  set θ₁ : K₁ ≃* SL(2, k) := φ₁.trans projSLEquiv.symm with hθ₁
  set θ₂ : K₂ ≃* SL(2, k) := φ₂.trans projSLEquiv.symm with hθ₂
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hn
  have : IsSimpleGroup K₁ := isSimpleGroup_of_sl2 hk4 θ₁
  have hZ₁ : ∀ z ∈ K₁, (∀ y ∈ K₁, z * y = y * z) → z = 1 := fun z hz h =>
    eq_one_of_central θ₁ hz h
  have hcard : Nat.card K₁ = Nat.card K₂ :=
    (Nat.card_congr θ₁.toEquiv).trans (Nat.card_congr θ₂.toEquiv).symm
  have hTsyl : IsSylowTwoOf (T : Subgroup H) ⊤ := ⟨le_top, T.isPGroup', by
    show ¬ 2 ∣ (T : Subgroup H).relIndex ⊤
    rw [relIndex_top_right]
    exact T.not_dvd_index⟩
  obtain ⟨-, -, -, ⟨-, hmin⟩, -, -⟩ :=
    Setup.qt_A7_unique_Sylow_overgroup_core_and_simple_section hTsyl hTn hTM hMH hmax
  have hsw : ∃ a : H ⧸ D, K₁.map (MulAut.conj a).toMonoidHom = K₂ := by
    by_contra hno
    push Not at hno
    have hK₁n : K₁.Normal := ⟨fun x hx a => by
      rcases conj_factor_eq_or hc hKn hZ₁ hcard a with h | h
      · rw [← h]
        exact ⟨x, hx, rfl⟩
      · exact absurd h (hno a)⟩
    have hNn : (K₁.comap π).Normal := hK₁n.comap π
    have hDN : D ≤ K₁.comap π := fun x hx => by
      show π x ∈ K₁
      rw [show π x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
      exact K₁.one_mem
    have hNK₀ : K₁.comap π ≤ oddResidualPreimage H := by
      intro x hx
      have h1 : π x ∈ (oddResidualPreimage H).map π := hK ▸ mem_sup_left hx
      obtain ⟨y, hy, hyx⟩ := h1
      have h2 : y⁻¹ * x ∈ D := by
        rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      have h3 := (oddResidualPreimage H).mul_mem hy (hDK₀ h2)
      rwa [mul_inv_cancel_left] at h3
    rcases hmin _ hNn hDN hNK₀ with h | h
    · apply ne_bot_of_sl2 θ₁
      rw [← map_comap_eq_self_of_surjective hπs K₁, h]
      exact (Subgroup.map_eq_bot_iff _).2 hπker.ge
    · apply ne_bot_of_sl2 θ₂
      have h1 : K₁ = K₁ ⊔ K₂ := by
        rw [← hK, ← h, map_comap_eq_self_of_surjective hπs]
      rw [← hd, inf_eq_right.2 (h1 ▸ le_sup_right : K₂ ≤ K₁)]
  set S' : Sylow 2 (H ⧸ D) := T.mapSurjective hπs with hS'
  have hS'S : (S' : Subgroup (H ⧸ D)) = S := Sylow.coe_mapSurjective hπs T
  have hSE : S ≤ normalizer (E : Set (H ⧸ D)) := (map_mono hTV).trans (le_normalizer_map π)
  have hE4 : 4 ≤ Nat.card E := hEcard ▸ hVQ
  have : IsElementaryAbelian 2 E := IsElementaryAbelian.map π
  obtain ⟨θ₁', θ₂', R, hR2, hKR, hKRt, hRperm, hRsw, hS, hB, hEU, hSK₁, hBK₁, hE₁U, hE₂U, r, hr1,
    hr, hr', x₁, L₁, hx₁K, hL₁, hx₁L, hL₁K, hLeq, hsyl, hcore, hO2, hO2P, hlin, hdih⟩ :=
    paired_quotient hk hn hc hd hKn hCK S' (hS'S ▸ hKS) θ₁ θ₂ hsw (hS'S ▸ hSB) hBtop
      (hS'S ▸ hBmax) hEO (hS'S ▸ hSE) hE4
  rw [hS'S] at hS hSK₁ hsyl hO2P hlin hdih
  set Ū := sl2UpperUnipotentSubgroup k with hŪ
  have hE₁L : E₁ ≤ L₁ := hL₁ ▸ le_sup_left
  have hE₂K : E₂ ≤ K₂ := inf_le_right
  have hFA : ∀ f ∈ L₁, ∀ a ∈ E₂, f * a = a * f := fun f hf a ha => hc f (hL₁K hf) a (hE₂K ha)
  have hFAb : L₁ ⊓ E₂ = ⊥ := eq_bot_iff.2 ((inf_le_inf hL₁K hE₂K).trans hd.le)
  have : IsElementaryAbelian 2 E₂ := isElementaryAbelian_of_le hE₂U
    (fun u hu v hv => stdSub_upperUnipotent_comm θ₂' hu hv)
    (fun u hu => stdSub_upperUnipotent_sq θ₂' hu)
  have hE₂S : E₂ ≤ S :=
    hE₂U.trans ((le_sup_right : stdSub θ₂' Ū ≤ _).trans (hS ▸ le_sup_left))
  have hE₂B : E₂ ≤ B := hE₂S.trans hSB
  have hsupinf : ∀ X : Subgroup (H ⧸ D), E₂ ≤ X → X ⊓ (L₁ ⊔ E₂) = (X ⊓ L₁) ⊔ E₂ := by
    intro X hX
    refine le_antisymm (fun y hy => ?_) (sup_le (inf_le_inf_left _ le_sup_left)
      (le_inf hX le_sup_right))
    obtain ⟨hyX, hyL⟩ := mem_inf.1 hy
    obtain ⟨l, hl, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_commute hFA hyL
    have hlX : l ∈ X := by
      have := X.mul_mem hyX (X.inv_mem (hX ha))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem_sup ⟨hlX, hl⟩ ha
  have hEL : (E ⊔ E₂) ⊓ L₁ = E₁ := by
    apply le_antisymm
    · exact inf_le_inf (sup_le_sup_left hE₂K _) hL₁K
    · refine le_inf (fun e₁ he₁ => ?_) hE₁L
      have hEK : E ≤ K₁ ⊔ K₂ := hEU.trans (sup_le_sup (stdSub_le _ _) (stdSub_le _ _))
      obtain ⟨e₂, he₂, he⟩ := exists_mul_mem_of_mem_proj hc hEK he₁
      have := mul_mem_sup (S := E) (T := E₂) he (E₂.inv_mem he₂)
      rwa [mul_inv_cancel_right] at this
  have hVQ' : ¬ V ≤ pCore 2 H := by
    intro h
    rw [inf_eq_left.2 h, relIndex_self] at hVQ
    omega
  have hF : (∃ ℓ a : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ 1 ≤ a ∧ Nonempty (L₁ ≃* DihedralGroup (ℓ ^ a)) ∧
        Nat.card ↥((V.map π ⊔ E₂) ⊓ L₁) = 2) ∨
      (∃ (f : ℕ) (k : Type) (_ : Field k), 2 ≤ f ∧ Nat.card k = 2 ^ f ∧
        Nonempty (L₁ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k)) ∨
      ∃ (b : ℕ) (k : Type) (_ : Field k), 1 ≤ b ∧ Nat.card k = 2 ^ (2 * b + 1) ∧
        Nonempty (L₁ ≃* CFSG.Blueprint.suzukiGroup b k) := by
    rcases Nat.lt_or_ge r 2 with h | h
    · obtain ⟨-, -, hD, -, -⟩ := hdih (by omega)
      refine Or.inl ⟨3, 1, Nat.prime_three, by norm_num, le_rfl, by rw [pow_one]; exact hD, ?_⟩
      rw [hEL, hr, show r = 1 by omega, pow_one]
    · obtain ⟨f, hf, -, -, e, -, -⟩ := hlin h
      exact Or.inr (Or.inl ⟨f, GaloisField 2 f, inferInstance, hf,
        GaloisField.card 2 f (by omega), ⟨e⟩⟩)
  have h9 := qrc_original_pair_lift_retains_central_second_factor hchar T hTn hTM hMH hmax hVT
    hTV hVM hVQ' hFA hFAb (mem_sup_left hx₁L) hLeq.symm hF hsyl inf_le_right hcore hO2 hO2P
    (hsupinf S hE₂S) (hsupinf B hE₂B)
  obtain ⟨g, hgI, hVI, hgx, h9⟩ := h9
  dsimp only at h9
  obtain ⟨hIF, hH₀, hIn, hQIH₀, hQIn, hQN, hcomm, hTIsyl, hID, hθ, hJcore, hJO, hκ, hQIO,
    hcharI, hO2MI, hNV, ψ, hψs, hψker, hψπ, hψM, hψT, hψV⟩ := h9
  have hU₁e : ((projUnitriangular 2 k).map (θ₁'.trans projSLEquiv).symm.toMonoidHom).map
      K₁.subtype = stdSub θ₁' Ū :=
    stdSub_projSL θ₁' _ _ map_projSLEquiv_symm_projUnitriangular
  have hU₂e : ((projUnitriangular 2 k).map (θ₂'.trans projSLEquiv).symm.toMonoidHom).map
      K₂.subtype = stdSub θ₂' Ū :=
    stdSub_projSL θ₂' _ _ map_projSLEquiv_symm_projUnitriangular
  have hB₁e : ((projUpperTriangular 2 k).map (θ₁'.trans projSLEquiv).symm.toMonoidHom).map
      K₁.subtype = stdSub θ₁' (sl2Borel k) :=
    stdSub_projSL θ₁' _ _ map_projSLEquiv_symm_projUpperTriangular
  have hB₂e : ((projUpperTriangular 2 k).map (θ₂'.trans projSLEquiv).symm.toMonoidHom).map
      K₂.subtype = stdSub θ₂' (sl2Borel k) :=
    stdSub_projSL θ₂' _ _ map_projSLEquiv_symm_projUpperTriangular
  have hSL₁ : S ⊓ L₁ = stdSub θ₁' Ū ⊓ L₁ := by
    rw [← hSK₁, inf_assoc, inf_eq_right.2 hL₁K]
  have hBL₁ : B ⊓ L₁ = stdSub θ₁' (sl2Borel k) ⊓ L₁ := by
    rw [← hBK₁, inf_assoc, inf_eq_right.2 hL₁K]
  have hι : Function.Injective (MulAut.conjNormal : H ⧸ D →* MulAut ↥(K₁ ⊔ K₂)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    rw [mem_bot]
    refine hCK a fun x hx => ?_
    have h1 := congrArg (fun φ : MulAut ↥(K₁ ⊔ K₂) => ((φ ⟨x, hx⟩ : ↥(K₁ ⊔ K₂)) : H ⧸ D)) ha
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h1]
  have hIK₀ : V ⊔ conjugate V g ≤ oddResidualPreimage H := by
    intro i hi
    have h1 : π i ∈ L₁ ⊔ E₂ := hIF ▸ mem_map_of_mem _ hi
    have h2 : π i ∈ (oddResidualPreimage H).map π := hK ▸ (sup_le_sup hL₁K hE₂K) h1
    obtain ⟨y, hy, hyi⟩ := h2
    have h3 : y⁻¹ * i ∈ D := by
      rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hyi, inv_mul_cancel]
    have h4 := (oddResidualPreimage H).mul_mem hy (hDK₀ h3)
    rwa [mul_inv_cancel_left] at h4
  have hE₂ne : E₂ ≠ ⊥ := by
    intro h
    have h1 : Nat.card E₂ = 2 ^ r := hr'
    rw [h, card_bot] at h1
    have : 1 < 2 ^ r := Nat.one_lt_two_pow (by omega)
    omega
  have hrel : (V ⊓ ((V ⊔ conjugate V g) ⊓ E₂.comap π)).relIndex V = 2 ^ r := by
    have h1 := relIndex_ker (V.subgroupOf (V ⊔ conjugate V g)) ψ
    rw [hψker, relIndex_subgroupOf (le_sup_left : V ≤ V ⊔ conjugate V g), hψV] at h1
    rw [inf_comm, inf_relIndex_right]
    refine h1.trans ?_
    change Nat.card ↥(((E ⊔ E₂) ⊓ L₁).subgroupOf L₁) = 2 ^ r
    rw [hEL, Nat.card_congr (subgroupOfEquivOfLe hE₁L).toEquiv, hr]
  refine ⟨⟨MulAut.conjNormal, hι, fun a x => MulAut.conjNormal_apply a x⟩, R,
    θ₁'.trans projSLEquiv, θ₂'.trans projSLEquiv, ?_⟩
  intro U₁ U₂ B₁ B₂
  have hU₁' : U₁ = stdSub θ₁' Ū := hU₁e
  have hU₂' : U₂ = stdSub θ₂' Ū := hU₂e
  have hB₁' : B₁ = stdSub θ₁' (sl2Borel k) := hB₁e
  have hB₂' : B₂ = stdSub θ₂' (sl2Borel k) := hB₂e
  rw [hU₁', hU₂', hB₁', hB₂']
  refine ⟨hR2, hKR, hKRt, fun r hr => (hRperm r hr).toP, hRsw, hS, hB, hEU, r, hr1, hr, hr', L₁,
    g, ?_⟩
  intro I H₀ RI J
  have hrel' : (V ⊓ J).relIndex V = 2 ^ r := hrel
  refine ⟨hL₁K, by rw [hgx]; exact hx₁L, by rw [hgx]; exact hL₁, hgI, hIK₀, hVI, hIF,
    by rw [hgx]; exact hLeq.symm, by rw [← hSL₁]; exact hsyl, ?_, ?_, hH₀, hIn, hQIH₀, hQIn, hQN,
    hcomm, hTIsyl, hID, hθ, hJcore, hJO, hκ, hE₂ne, hQIO, hcharI, hO2MI, hNV, ψ, hψs, hψker, hψπ,
    by rw [hψM, hBL₁], by rw [hψT, hSL₁], ?_, le_inf hE₁U hE₁L,
    fun v hv u hu => stdSub_upperUnipotent_comm θ₁' (hE₁U hv) hu.1, hrel'⟩
  · intro h2
    obtain ⟨f, hf, hrf, hfn, e, heB, heU⟩ := hlin h2
    have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    refine ⟨f, hf, hrf, hfn, GaloisField 2 f, inferInstance, hcardF,
      e.trans (p2PSLEquiv _).symm, ?_, ?_⟩
    · rw [← hBL₁, map_mulEquiv_trans, heB]
      exact map_symm_eq_of_map_eq _ map_p2Equiv_projUpperTriangular
    · rw [← hSL₁, map_mulEquiv_trans, heU]
      exact map_symm_eq_of_map_eq _ map_p2Equiv_projUnitriangular
  · intro h1
    obtain ⟨hEc, hE12, hD, hBL, hSL⟩ := hdih h1
    exact ⟨hEc, hE12, 3, Nat.prime_three, by norm_num, hD, by rw [← hBL₁]; exact hBL,
      by rw [← hSL₁]; exact hSL⟩
  · rw [hψV]
    change (((E ⊔ E₂) ⊓ L₁).subgroupOf L₁) = E₁.subgroupOf L₁
    rw [hEL]

end Main

end CFSG.Quasithin.H13.QRC
