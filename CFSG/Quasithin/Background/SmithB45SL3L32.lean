module

public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.D2Tools

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace B45L32

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Family
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace Matrix

theorem card_sym_comm_le : ∀ s00 s01 s02 s11 s12 s22 : ZMod 2,
    !![s00, s01, s02; s01, s11, s12; s02, s12, s22] *
      !![s00, s01, s02; s01, s11, s12; s02, s12, s22] = 1 →
    !![s00, s01, s02; s01, s11, s12; s02, s12, s22] ≠ 1 →
    (Finset.univ.filter fun p : Tup8 => (tzp p)ᵀ = tzp p ∧
      !![s00, s01, s02; s01, s11, s12; s02, s12, s22] * tzp p =
        tzp p * !![s00, s01, s02; s01, s11, s12; s02, s12, s22]).card ≤ 8 := by
  decide +kernel

theorem natCard_fixedSub_repQ_le_of_tGen {A : Subgroup H32} (ht : tGen ∈ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a ^ 2 = 1)
    (hA4 : Nat.card A = 4) : Nat.card (fixedSub repQ A) ≤ 8 := by
  classical
  set B : Subgroup GL32 := A.comap sIncl with hB
  have hBmem : ∀ n, n ∈ B ↔ sIncl n ∈ A := fun n => Iff.rfl
  have hc2 : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
  have hinr : ∀ ε : Multiplicative (ZMod 2), (SemidirectProduct.inr ε : H32) ∈ A := by
    intro ε
    rcases hc2 ε with rfl | rfl
    · rw [map_one]
      exact A.one_mem
    · exact ht
  have hleft : ∀ a ∈ A, a.left ∈ B := fun a ha => by
    have h1 : sIncl a.left = a * (SemidirectProduct.inr a.right)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact SemidirectProduct.inl_left_mul_inr_right a
    rw [hBmem, h1]
    exact A.mul_mem ha (A.inv_mem (hinr _))
  let e : A ≃ B × Multiplicative (ZMod 2) :=
    { toFun := fun a => (⟨a.1.left, hleft a.1 a.2⟩, a.1.right)
      invFun := fun p => ⟨sIncl p.1.1 * SemidirectProduct.inr p.2, A.mul_mem p.1.2 (hinr _)⟩
      left_inv := fun a => Subtype.ext (SemidirectProduct.inl_left_mul_inr_right a.1)
      right_inv := fun p => by
        apply Prod.ext
        · apply Subtype.ext
          simp [sIncl, SemidirectProduct.mul_left]
        · simp [sIncl, SemidirectProduct.mul_right] }
  have hcardA : Nat.card A = Nat.card B * 2 := by
    rw [Nat.card_congr e, Nat.card_prod]
    congr 1
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hB2 : Nat.card B = 2 := by omega
  have : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨b, hbB⟩, hb1⟩ := exists_ne (1 : B)
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hτ : tauHom b = b := by
    have h1 := hcomm tGen ht (sIncl b) hbB
    rw [tGen_mul_sIncl] at h1
    exact sIncl_injective (mul_right_cancel h1)
  have hbb : b * b = 1 := by
    apply sIncl_injective
    rw [map_mul, map_one, ← pow_two]
    exact hsq _ hbB
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hsym : (b : Mat3)ᵀ = (b : Mat3) := by
    have := congrArg (fun x : GL32 => (x : Mat3)) hτ
    simp only [tauHom_val, hbinv] at this
    exact this
  have hle : Nat.card (fixedSub repQ A) ≤
      Nat.card {X : Mat3 | X ∈ traceZero ∧ (Xᵀ = X ∧ (b : Mat3) * X = X * (b : Mat3))} := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨((x : traceZero) : Mat3), (x : traceZero).2, ?_, ?_⟩) ?_
    · have h1 : repQ tGen x.1 = x.1 := x.2 tGen ht
      rw [repQ_tGen] at h1
      exact congrArg Subtype.val h1
    · have h1 : repQ (sIncl b) x.1 = x.1 := x.2 _ hbB
      rw [repQ_sIncl] at h1
      have h2 := congrArg Subtype.val h1
      rw [repA_apply, hbinv] at h2
      calc (b : Mat3) * ((x : traceZero) : Mat3)
          = (b : Mat3) * ((x : traceZero) : Mat3) * (b : Mat3) * (b : Mat3) := by
            rw [Matrix.mul_assoc _ (b : Mat3) (b : Mat3), ← Units.val_mul, hbb, Units.val_one,
              Matrix.mul_one]
        _ = ((x : traceZero) : Mat3) * (b : Mat3) := by rw [h2]
    · intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext (Subtype.ext hxy)
  rw [natCard_traceZero_setOf] at hle
  refine hle.trans ?_
  have hb00 := congrFun (congrFun hsym 0) 1
  have hb02 := congrFun (congrFun hsym 0) 2
  have hb12 := congrFun (congrFun hsym 1) 2
  simp only [Matrix.transpose_apply] at hb00 hb02 hb12
  have hbeta : (b : Mat3) = !![(b : Mat3) 0 0, (b : Mat3) 0 1, (b : Mat3) 0 2;
      (b : Mat3) 0 1, (b : Mat3) 1 1, (b : Mat3) 1 2;
      (b : Mat3) 0 2, (b : Mat3) 1 2, (b : Mat3) 2 2] := by
    conv_lhs => rw [Matrix.eta_fin_three (b : Mat3)]
    rw [hb00, hb02, hb12]
  have hbsq : (b : Mat3) * (b : Mat3) = 1 := by
    rw [← Units.val_mul, hbb, Units.val_one]
  have hbne : (b : Mat3) ≠ 1 := fun h => hb1' (Units.ext h)
  rw [hbeta] at hbsq hbne ⊢
  exact card_sym_comm_le _ _ _ _ _ _ hbsq hbne

theorem natCard_fixedSub_repQ_le_of_not_le {A : Subgroup H32}
    (hA : ¬ A ≤ (sIncl : GL32 →* H32).range) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hsq : ∀ a ∈ A, a ^ 2 = 1) (hA4 : Nat.card A = 4) : Nat.card (fixedSub repQ A) ≤ 8 := by
  obtain ⟨a, haA, haS⟩ := Set.not_subset.1 hA
  have ha2 : a * a = 1 := by
    have := hsq a haA
    rwa [pow_two] at this
  obtain ⟨m, hm⟩ := exists_conj_tGen haS ha2
  have ht : tGen ∈ A.map (MulAut.conj (sIncl m)).toMonoidHom := ⟨a, haA, by
    rw [← hm]
    rfl⟩
  have hcomm' : ∀ x ∈ A.map (MulAut.conj (sIncl m)).toMonoidHom,
      ∀ y ∈ A.map (MulAut.conj (sIncl m)).toMonoidHom, x * y = y * x := by
    rintro _ ⟨a₁, ha₁, rfl⟩ _ ⟨a₂, ha₂, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a₁ ha₁ a₂ ha₂]
  have hsq' : ∀ x ∈ A.map (MulAut.conj (sIncl m)).toMonoidHom, x ^ 2 = 1 := by
    rintro _ ⟨a₁, ha₁, rfl⟩
    rw [← map_pow, hsq a₁ ha₁, map_one]
  have hcard : Nat.card (A.map (MulAut.conj (sIncl m)).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj (sIncl m)).injective
  rw [← natCard_fixedSub_conj repQ A (sIncl m)]
  exact natCard_fixedSub_repQ_le_of_tGen ht hcomm' hsq' (hcard.trans hA4)

theorem card_sq_mul_fixedSub_repQ_lt {A : Subgroup H32} (hA0 : A ≠ ⊥)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A ^ 2 * Nat.card (fixedSub repQ A) < 256 := by
  by_cases hS : A ≤ (sIncl : GL32 →* H32).range
  · rcases fixed_data_le_S hS hA0 hcomm hsq with ⟨h1, -, h3⟩ | ⟨h1, -, h3⟩ <;>
      rw [h1, h3] <;> norm_num
  · rcases fixed_data_not_S hS hcomm hsq with ⟨h1, -, h3⟩ | ⟨h1, -, -⟩
    · rw [h1, h3]
      norm_num
    · have h8 := natCard_fixedSub_repQ_le_of_not_le hS hcomm hsq h1
      rw [h1]
      omega

theorem card_sq_mul_lt_of_not_le {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    [FiniteDimensional (ZMod 2) S] {D Y A : Subgroup (Module.End (ZMod 2) S)ˣ}
    (hirr : ∀ U : Submodule (ZMod 2) S,
      (∀ d ∈ D, ∀ v ∈ U, (d : Module.End (ZMod 2) S) v ∈ U) → U = ⊥ ∨ U = ⊤)
    (h8 : Module.finrank (ZMod 2) S = 8)
    (hYD : Y ≤ D) (hYn : ∀ d ∈ D, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) (eY : Y ≃* GL32)
    (hCY : ∀ d ∈ D, (∀ y ∈ Y, d * y = y * d) → d = 1) (hAD : A ≤ D) (hA1 : A ≠ ⊥)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    {d₀ : (Module.End (ZMod 2) S)ˣ} (hd₀ : d₀ ∈ D) (hd₀Y : d₀ ∉ Y) :
    Nat.card A ^ 2 * Nat.card ↥(LocalAnalysis.CommutingFactor.fixedSub A) < Nat.card S := by
  classical
  set C := LocalAnalysis.CommutingFactor.fixedSub A
  have : Finite S := Module.finite_of_finite (ZMod 2)
  have : Finite ↥C := Module.finite_of_finite (ZMod 2)
  have hS256 : Nat.card S = 256 := by
    rw [H13.NQTerm.card_eq_two_pow_finrank (M := S), h8]
    norm_num
  have : (Y.subgroupOf D).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
      (hYn g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  have hCY' : ∀ d : D, (∀ y ∈ Y.subgroupOf D, d * y = y * d) → d = 1 := by
    intro d hd
    refine Subtype.ext (hCY d d.2 fun y hy => ?_)
    exact congrArg Subtype.val (hd ⟨y, hYD hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
  obtain ⟨Ψ, -⟩ := H13.NQTerm.exists_H32_mulEquiv
    ((Subgroup.subgroupOfEquivOfLe hYD).trans eY) hCY'
    (d₀ := ⟨d₀, hd₀⟩) fun h => hd₀Y (Subgroup.mem_subgroupOf.mp h)
  let ρH : H32 →* (S ≃ₗ[ZMod 2] S) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) S).toMonoidHom.comp
      (D.subtype.comp Ψ.toMonoidHom)
  have hρH : ∀ (h : H32) (v : S),
      ρH h v = (((Ψ h : D) : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) v :=
    fun _ _ => rfl
  have hnt : Nontrivial S := by
    rw [← Module.finrank_pos_iff (R := ZMod 2), h8]
    norm_num
  have hirrH : IsIrrRep ρH := by
    refine isIrrRep_of hnt fun N hN => hirr N fun d hd v hv => ?_
    obtain ⟨h, hh⟩ := Ψ.surjective ⟨d, hd⟩
    have h1 := hN h v hv
    rw [hρH, hh] at h1
    exact h1
  obtain ⟨A', hA'mem⟩ : ∃ A' : Subgroup H32, ∀ h, h ∈ A' ↔ (Ψ h).1 ∈ A :=
    ⟨(A.subgroupOf D).comap Ψ.toMonoidHom, fun _ => Iff.rfl⟩
  have hmemA' : ∀ b (hb : b ∈ A), Ψ.symm ⟨b, hAD hb⟩ ∈ A' := by
    intro b hb
    rw [hA'mem, MulEquiv.apply_symm_apply]
    exact hb
  have hA'0 : A' ≠ ⊥ := by
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
    intro hbot
    have h1 := hmemA' b hb
    rw [hbot, Subgroup.mem_bot] at h1
    apply hb1
    have h2 : (⟨b, hAD hb⟩ : D) = 1 := by
      rw [← Ψ.apply_symm_apply ⟨b, hAD hb⟩, h1, map_one]
    have h3 : b = 1 := congrArg Subtype.val h2
    exact Subtype.ext h3
  have hcomm' : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    apply Ψ.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact hAc _ ((hA'mem x).mp hx) _ ((hA'mem y).mp hy)
  have hsq' : ∀ x ∈ A', x ^ 2 = 1 := by
    intro x hx
    apply Ψ.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hA2 _ ((hA'mem x).mp hx)
  have hcardA' : Nat.card A' = Nat.card A :=
    Nat.card_congr
      { toFun := fun h => ⟨(Ψ h).1, (hA'mem h).mp h.2⟩
        invFun := fun b => ⟨Ψ.symm ⟨b.1, hAD b.2⟩, hmemA' b.1 b.2⟩
        left_inv := fun h => Subtype.ext (Ψ.symm_apply_apply h.1)
        right_inv := fun b => Subtype.ext (by
          change (Ψ (Ψ.symm ⟨b.1, hAD b.2⟩)).1 = b.1
          rw [MulEquiv.apply_symm_apply]) }
  have hfixA' : Nat.card (fixedSub ρH A') = Nat.card ↥C :=
    Nat.card_congr
      { toFun := fun y => ⟨y.1, LocalAnalysis.CommutingFactor.mem_fixedSub.mpr fun b hb => by
            have h1 := mem_fixedSub.mp y.2 _ (hmemA' b hb)
            rw [hρH, MulEquiv.apply_symm_apply] at h1
            exact h1⟩
        invFun := fun v => ⟨v.1, mem_fixedSub.mpr fun h hh => by
          rw [hρH]
          exact LocalAnalysis.CommutingFactor.mem_fixedSub.mp v.2 _ ((hA'mem h).mp hh)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rcases irreducible_GL3_ext_classification ρH hirrH with h | h | h
  · exfalso
    have := card_eq_of_modIso_H h
    rw [Nat.card_zmod, hS256] at this
    omega
  · exfalso
    have := card_eq_of_modIso_H h
    rw [natCard_P6, hS256] at this
    omega
  · have hQ := natCard_fixedSub_of_modIso h A'
    have hlt := card_sq_mul_fixedSub_repQ_lt hA'0 hcomm' hsq'
    rw [← hQ, hfixA', hcardA'] at hlt
    rw [hS256]
    exact hlt

end B45L32

section Main

open B45L32 B42L2 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.Family CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

variable {V : Type} [CommGroup V] [Finite V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W]

omit [Finite V] in
theorem B45L32.finrank_eq_three_or_eight (θ : V ≃* Multiplicative W) [Nontrivial W]
    {L : Subgroup (MulAut V)}
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (eL : ↥L ≃* GL32) :
    Module.finrank (ZMod 2) W = 3 ∨ Module.finrank (ZMod 2) W = 8 := by
  classical
  have : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  let ρ : GL32 →* (W ≃ₗ[ZMod 2] W) :=
    (binPsi θ).toMonoidHom.comp (L.subtype.comp eL.symm.toMonoidHom)
  have hρ : ∀ g w, ρ g w = binPsi θ (eL.symm g : MulAut V) w := fun _ _ => rfl
  have hirrρ : IsIrrRep ρ := by
    refine isIrrRep_of inferInstance fun N hN => irr_map θ hirr N ?_
    rintro _ ⟨l, hl, rfl⟩ u hu
    have h1 := hN (eL ⟨l, hl⟩) u hu
    rw [hρ, MulEquiv.symm_apply_apply] at h1
    exact h1
  have hW : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := H13.NQTerm.card_eq_two_pow_finrank
  rcases irreducible_binary_GL3_classification ρ hirrρ with h | h | h | h
  · exfalso
    obtain ⟨f, hf⟩ := h
    have := H13.NQTerm.nontrivial_GL32
    obtain ⟨g, hg⟩ : ∃ g : GL32, g ≠ 1 := exists_ne 1
    apply hg
    apply eL.symm.injective
    rw [map_one]
    apply Subtype.ext
    apply eq_one_of_unitsPsi θ
    intro w
    rw [unitsPsi_apply]
    obtain ⟨c, rfl⟩ := f.surjective w
    have h1 : f (repTriv g c) = ρ g (f c) := hf g c
    have h2 : repTriv g c = c := rfl
    rw [h2, hρ] at h1
    exact h1.symm
  · left
    have := card_eq_of_modIso h
    rw [natCard_Vec3, hW] at this
    exact (Nat.pow_right_injective le_rfl (this.symm.trans (by norm_num : (8 : ℕ) = 2 ^ 3)))
  · left
    have := card_eq_of_modIso h
    rw [natCard_Vec3, hW] at this
    exact (Nat.pow_right_injective le_rfl (this.symm.trans (by norm_num : (8 : ℕ) = 2 ^ 3)))
  · right
    have := card_eq_of_modIso h
    rw [natCard_traceZero, hW] at this
    exact (Nat.pow_right_injective le_rfl (this.symm.trans (by norm_num : (256 : ℕ) = 2 ^ 8)))

theorem asB45L32_holds : AsB45L32 := by
  classical
  intro V _ _ hV G L hHyp hP hq2
  obtain ⟨hZ, hmodel⟩ := hP
  obtain ⟨eL⟩ := exists_gl32_of_model hZ hmodel
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hV'
  have hirr := Bridge.TypeList.irr_of_isIrrSec hHyp.2.2.2
  have hntW : Nontrivial W := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hHyp.2.2.2.1
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  have hLG : L ≤ G := hHyp.2.1 ▸ quasithinGenFitting_le G
  rcases finrank_eq_three_or_eight θ hirr eL with h3 | h8
  ·
    obtain ⟨π', -, f, hf⟩ := exists_natural_l32 θ hirr eL h3
    have hV8 : Nat.card V = 2 ^ 3 := by
      rw [natCard_eq θ, H13.NQTerm.card_eq_two_pow_finrank (M := W), h3]
    obtain ⟨B₀, hB₀L, hB₀ne, hB₀el, hB₀rk, hB₀fix⟩ := exists_axis π' f hf
    have hr : rAV B₀ = 1 / 2 := by
      rw [rAV_eq_of_card hV8 hB₀rk hB₀fix]
      norm_num
    have hcard : Nat.card B₀ = 4 := by
      rw [B1.card_elemAbelian hB₀el, hB₀rk]
      norm_num
    have hcub : commSeries B₀ 3 = ⊥ := commSeries_three_eq_bot_of_card_four hV hB₀el hcard
    have hle : qhatOf G ≤ ((1 / 2 : ℚ) : WithTop ℚ) :=
      kq_le_iff.mpr ⟨B₀, ⟨hB₀L.trans hLG, hB₀ne, hB₀el⟩, hcub, hr.le⟩
    exact hle.trans (WithTop.coe_le_coe.mpr (by norm_num))
  ·
    exfalso
    obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp hq2
    have hoff := (rAV_le_two_iff hV hA).mp hAr
    have : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
    set Φ := unitsPsi θ with hΦ
    have hcardW : Nat.card V = 2 ^ 8 := by
      rw [natCard_eq θ, H13.NQTerm.card_eq_two_pow_finrank (M := W), h8]
    have hfixeq : Nat.card ↥(LocalAnalysis.CommutingFactor.fixedSub (A.map Φ.toMonoidHom)) =
        Nat.card ↥(fixV A) := natCard_fixedSub_map θ A
    have hcardA : Nat.card (A.map Φ.toMonoidHom) = Nat.card A :=
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
        (Subgroup.map_mono hA.1) (map_unitsPsi_ne_bot θ hA.2.1) hAc hA2 (a := rk ↥A)
        (by rw [hcardA, B1.card_elemAbelian hA.2.2])
      rw [top_inf_eq, finrank_top, h8] at hcases
      have hfixW : Nat.card ↥(LocalAnalysis.CommutingFactor.fixedSub (A.map Φ.toMonoidHom)) =
          2 ^ Module.finrank (ZMod 2)
            ↥(LocalAnalysis.CommutingFactor.fixedSub (A.map Φ.toMonoidHom)) :=
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

end Main

end CFSG.Quasithin
