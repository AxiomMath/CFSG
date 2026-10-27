module

public import CFSG.Quasithin.Background.E6TwentyThreePA
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentL5
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentEven
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

section UG

open Id2519.Tab.L5 Matrix Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_UG_ge {N : M5} (hN0 : N ≠ 0) (hNN : N * N = 0) : 16 ≤ Nat.card ↥(UG N) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin 5 → ZMod 2) := Matrix.mulVecLin N with hf
  set K := LinearMap.ker f with hK
  have hrange : LinearMap.range f ≤ K := by
    rintro _ ⟨v, rfl⟩
    rw [hK, LinearMap.mem_ker, hf, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  have hrange0 : LinearMap.range f ≠ ⊥ := by
    intro h0
    apply hN0
    have hf0 : f = 0 := LinearMap.range_eq_bot.mp h0
    have : Matrix.toLin' N = 0 := hf0
    simpa using this
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun (ZMod 2)] at hrn
  have hr1 : 1 ≤ finrank (ZMod 2) (LinearMap.range f) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hrange0
  have hrk : finrank (ZMod 2) (LinearMap.range f) ≤ finrank (ZMod 2) K :=
    Submodule.finrank_mono hrange
  set k := finrank (ZMod 2) K with hk
  have hq := Submodule.finrank_quotient_add_finrank K
  rw [Module.finrank_fin_fun (ZMod 2)] at hq
  have hmem : ∀ g : ((Fin 5 → ZMod 2) ⧸ K) →ₗ[ZMod 2] K,
      InUG N (1 + LinearMap.toMatrix' (K.subtype ∘ₗ g ∘ₗ K.mkQ)) ∧
        (1 + LinearMap.toMatrix' (K.subtype ∘ₗ g ∘ₗ K.mkQ)).det = 1 := by
    intro g
    set M := LinearMap.toMatrix' (K.subtype ∘ₗ g ∘ₗ K.mkQ) with hM
    have hMv : ∀ v, M *ᵥ v = (g (K.mkQ v) : Fin 5 → ZMod 2) := fun v => by
      rw [hM, LinearMap.toMatrix'_mulVec]
      rfl
    have hNM : N * M = 0 := by
      apply M5_ext_mulVec
      intro v
      rw [← Matrix.mulVec_mulVec, hMv, Matrix.zero_mulVec]
      exact LinearMap.mem_ker.mp (g (K.mkQ v)).2
    have hMK : ∀ x : Fin 5 → ZMod 2, N *ᵥ x = 0 → M *ᵥ x = 0 := by
      intro x hx
      rw [hMv]
      have hxK : x ∈ K := by
        rw [hK, LinearMap.mem_ker, hf, Matrix.mulVecLin_apply]
        exact hx
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero K).mpr hxK, map_zero]
      rfl
    have hMM : M * M = 0 := by
      apply M5_ext_mulVec
      intro v
      rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
      refine hMK _ ?_
      rw [hMv]
      exact LinearMap.mem_ker.mp (g (K.mkQ v)).2
    refine ⟨⟨by rw [add_sub_cancel_left]; exact hNM, fun x hx => by
      rw [add_sub_cancel_left]; exact hMK x hx⟩, ?_⟩
    have hsq : (1 + M) * (1 + M) = 1 := by
      have h1 : (1 + M) * (1 + M) = 1 + (M + M) + M * M := by noncomm_ring
      rw [h1, hMM, M5_add_self]
      simp
    have hdet := congrArg Matrix.det hsq
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact zmod2_sq_eq_one hdet
  let ι : (((Fin 5 → ZMod 2) ⧸ K) →ₗ[ZMod 2] K) → ↥(UG N) := fun g =>
    ⟨⟨1 + LinearMap.toMatrix' (K.subtype ∘ₗ g ∘ₗ K.mkQ), (hmem g).2⟩, (hmem g).1⟩
  have hι : Function.Injective ι := by
    intro g g' hgg'
    have h1 : LinearMap.toMatrix' (K.subtype ∘ₗ g ∘ₗ K.mkQ) =
        LinearMap.toMatrix' (K.subtype ∘ₗ g' ∘ₗ K.mkQ) := by
      have := congrArg (fun u : ↥(UG N) => ((u : S) : M5)) hgg'
      simpa [ι] using this
    have h2 := LinearMap.toMatrix'.injective h1
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := K.mkQ_surjective q
    have h3 := congrArg (fun F : (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin 5 → ZMod 2) => F v) h2
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h3
    exact Subtype.ext h3
  have hfin : Finite (((Fin 5 → ZMod 2) ⧸ K) →ₗ[ZMod 2] K) := Module.finite_of_finite (ZMod 2)
  have hcard : Nat.card (((Fin 5 → ZMod 2) ⧸ K) →ₗ[ZMod 2] K) = 2 ^ ((5 - k) * k) := by
    have : Fintype (((Fin 5 → ZMod 2) ⧸ K) →ₗ[ZMod 2] K) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card,
      Module.finrank_linearMap]
    congr 2
    omega
  have hle := Nat.card_le_card_of_injective ι hι
  rw [hcard] at hle
  have hk1 : 1 ≤ k := le_trans hr1 hrk
  have hk4 : k ≤ 4 := by omega
  have h16 : 16 ≤ 2 ^ ((5 - k) * k) := by
    interval_cases k <;> norm_num
  omega

end UG

theorem sq_eq_one_of_sylow {H : Type*} [Group H] [Finite H] (P : Sylow 2 H)
    (hP : ∀ t ∈ (P : Subgroup H), t ^ 2 = 1) {g : H} (hg : IsPGroup 2 (Subgroup.zpowers g)) :
    g ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H P Q
  have hgQ : g ∈ (Q : Subgroup H) := hQ (Subgroup.mem_zpowers g)
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hgQ
  have h1 := hP _ hgQ
  have h2 : (MulAut.conj c)⁻¹ • g = c⁻¹ * g * c := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
  rw [h2] at h1
  have h3 : g ^ 2 = c * (c⁻¹ * g * c) ^ 2 * c⁻¹ := by
    rw [pow_two, pow_two]
    group
  rw [h3, h1]
  group

namespace InspHyp

variable {G : Type} [Group G] [Finite G] {Y E X : Subgroup G} {a z : G}

theorem false_of_patL5 (h : InspHyp Y E X a z) (hL5 : Id2519.PatL5 Y X)
    (h8 : (E ⊓ Subgroup.centralizer (Y : Set G)).relIndex E = 8) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hmodel⟩ := hL5
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := hmodel
  have hcard2 : Nat.card F = 2 := by simpa using hcard
  let φ : ↥Y ≃* Id2519.Tab.L5.S :=
    e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 5 F hcard2)
  have hc : Subgroup.center ↥Y = ⊥ := by
    rw [← Subgroup.map_bot φ.symm.toMonoidHom, ← Id2519.Tab.L5.center_S]
    exact (Subgroup.map_center_eq φ.symm).symm
  have hperf : Group.IsPerfect ↥Y := h.quasi.1
  have hsimple : IsSimpleGroup ↥Y := by
    have := h.quasi.2.1
    exact MulEquiv.isSimpleGroup
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm
  have hker : φ.toMonoidHom.ker = Subgroup.center ↥Y := by
    rw [hc, MonoidHom.ker_eq_bot_iff]
    exact φ.injective
  have hcardE := card_map_quotAction φ.toMonoidHom φ.surjective hker hperf h.norm
  rw [h8] at hcardE
  set ψ := quotAction φ.toMonoidHom φ.surjective hker with hψ
  set Ebar := (E.subgroupOf (Subgroup.normalizer (Y : Set G))).map ψ with hEbar
  set Inn := CFSG.ComponentClassification.OuterAutomorphisms.inner Id2519.Tab.L5.S with hInn
  have hidx : Inn.index ≤ 2 := Id2519.Tab.L5.card_outer_S
  have hA : 4 ≤ Nat.card ↥(Inn ⊓ Ebar) := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal Inn Ebar
    have hmul := Subgroup.relIndex_mul_card (H := Inn) (K := Ebar)
    rw [hcardE] at hmul
    have h0 : Inn.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle : Inn.relIndex Ebar ≤ 2 :=
      (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd).trans hidx
    have hpos : 0 < Inn.relIndex Ebar :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at hmul; exact absurd hmul (by norm_num)
    interval_cases hr : Inn.relIndex Ebar <;> omega
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ Inn ⊓ Ebar, w ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : Inn ⊓ Ebar = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hall
    rw [hbot, Subgroup.card_bot] at hA
    omega
  obtain ⟨x, hxE, hxw⟩ := hw.2
  obtain ⟨s, hs⟩ := hw.1
  have hxE' : (x : G) ∈ E := hxE
  have hs2 : s * s = 1 := by
    have hww : w * w = 1 := by
      rw [← hxw, ← map_mul]
      have : x * x = 1 := Subtype.ext (h.mul_self_eq_one hxE')
      rw [this, map_one]
    have hz : s * s ∈ Subgroup.center Id2519.Tab.L5.S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun α : MulAut Id2519.Tab.L5.S => α g) hww
      simp only [← hs, MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h1
      have h2 : s * s * g * (s * s)⁻¹ = g := by
        rw [show s * s * g * (s * s)⁻¹ = s * (s * g * s⁻¹) * s⁻¹ by group]
        exact h1
      calc g * (s * s) = s * s * g * (s * s)⁻¹ * (s * s) := by rw [h2]
        _ = s * s * g := by group
    rw [Id2519.Tab.L5.center_S, Subgroup.mem_bot] at hz
    exact hz
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply hw1
    rw [← hs, map_one]
  have hcent : ∀ y : ↥Y, (y : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ↔
      φ y ∈ Subgroup.centralizer ({s} : Set Id2519.Tab.L5.S) := by
    intro y
    rw [mem_centralizer_iff_quotAction φ.toMonoidHom φ.surjective hker hc x y,
      Subgroup.mem_centralizer_singleton_iff]
    change ψ x (φ y) = φ y ↔ _
    rw [hxw, ← hs, MulAut.conj_apply]
    constructor
    · intro h1
      calc φ y * s = s * φ y * s⁻¹ * s := by rw [h1]
        _ = s * φ y := by group
    · intro h1
      rw [← h1]
      group
  have hmapC : ((Y ⊓ Subgroup.centralizer ({(x : G)} : Set G)).subgroupOf Y).map
      φ.toMonoidHom = Subgroup.centralizer ({s} : Set Id2519.Tab.L5.S) := by
    ext w'
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hcent y).1 (Subgroup.mem_subgroupOf.mp hy).2
    · intro hw'
      refine ⟨φ.symm w', Subgroup.mem_subgroupOf.mpr ⟨(φ.symm w').2, (hcent _).2 ?_⟩, ?_⟩
      · simpa using hw'
      · simp
  have hsI : Id2519.IdentSetting Y X a :=
    ⟨h.quasi, h.norm h.mem, h.mul_self_eq_one h.mem, h.commutator_eq, h.comp,
      Or.inr (Or.inr h.a6)⟩
  have h720 : Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G)) ∣ 720 := by
    obtain ⟨a', ε, hε, hα⟩ := Id2519.Tab.L5.aut_form (MulAut.congr φ hsI.conjAut)
    interval_cases ε
    · exfalso
      simp only [pow_zero, mul_one] at hα
      have hx : ∀ y : ↥Y, hsI.conjAut y = φ.symm a' * y * (φ.symm a')⁻¹ := by
        intro y
        apply φ.injective
        have h1 := congrArg (fun f : MulAut Id2519.Tab.L5.S => f (φ y)) hα
        simp only [MulAut.conj_apply] at h1
        have h2 : (MulAut.congr φ hsI.conjAut) (φ y) = φ (hsI.conjAut y) := by
          show φ (hsI.conjAut (φ.symm (φ y))) = _
          rw [MulEquiv.symm_apply_apply]
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← h2, h1]
      exact hsI.false_of_inner hsimple φ
        (fun y hy B => Id2519.Tab.L5.involution_centralizer_component_free hy B) (φ.symm a') hx
    · simp only [pow_one] at hα
      exact hsI.card_cent_dvd_of_outer φ a' hα
  obtain ⟨T, hT, hET⟩ := h.exists_sylow_a
  have hT16 : Nat.card ↥T ≤ 16 := by
    have hTd : Nat.card ↥T ∣ 720 := (Subgroup.card_dvd_of_le hT.le).trans h720
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hT.isPGroup
    rw [hm] at hTd ⊢
    have hm4 : m ≤ 4 := by
      by_contra hm5
      push Not at hm5
      have : 2 ^ 5 ∣ 720 := (Nat.pow_dvd_pow 2 hm5).trans hTd
      omega
    calc 2 ^ m ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hm4
      _ = 16 := by norm_num
  have hxY : ¬ Y ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
    intro hle
    apply hw1
    rw [← hxw]
    exact (quotAction_eq_one_iff _ _ hker hperf x).mpr (Subgroup.mem_centralizer_iff.mpr
      fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hle hy))
  have hTx : T ≤ Y ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
    intro t ht
    refine ⟨(hT.le ht).1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hET hxE') t ht)
  have hfle := h.factorization_le hxE' hxY
  have hTsyl : IsSylowIn 2 T (Y ⊓ Subgroup.centralizer ({(x : G)} : Set G)) := by
    refine isSylowIn_of_card_eq hTx ?_
    rw [hT.card_eq]
    congr 1
    refine le_antisymm ?_ hfle
    have hd : 2 ^ (Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G))).factorization 2 ∣
        Nat.card ↥(Y ⊓ Subgroup.centralizer ({(x : G)} : Set G)) := by
      rw [← hT.card_eq]
      exact Subgroup.card_dvd_of_le hTx
    exact (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hd
  set Ts := (T.subgroupOf Y).map φ.toMonoidHom with hTs
  have hTY : T ≤ Y := hT.le.trans inf_le_left
  have hcardTs : Nat.card ↥Ts = Nat.card ↥T := by
    rw [hTs, Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv]
  have hcardC : Nat.card ↥(Subgroup.centralizer ({s} : Set Id2519.Tab.L5.S)) =
      Nat.card ↥(Y ⊓ Subgroup.centralizer ({(x : G)} : Set G)) := by
    rw [← hmapC, Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hTsC : Ts ≤ Subgroup.centralizer ({s} : Set Id2519.Tab.L5.S) := by
    rw [← hmapC, hTs]
    exact Subgroup.map_mono fun t ht => Subgroup.mem_subgroupOf.mpr
      (hTx (Subgroup.mem_subgroupOf.mp ht))
  have hTsSyl : IsSylowIn 2 Ts (Subgroup.centralizer ({s} : Set Id2519.Tab.L5.S)) := by
    refine isSylowIn_of_card_eq hTsC ?_
    rw [hcardTs, hcardC, hTsyl.card_eq]
  have hs2' : ((s : Id2519.Tab.L5.S) : Id2519.Tab.L5.M5) * s = 1 := by
    have := congrArg (fun g : Id2519.Tab.L5.S => (g : Id2519.Tab.L5.M5)) hs2
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using this
  set U := Id2519.Tab.L5.UG ((s : Id2519.Tab.L5.M5) - 1) with hU
  have hUC : U ≤ Subgroup.centralizer ({s} : Set Id2519.Tab.L5.S) := fun u hu => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Id2519.Tab.L5.UG_comm_y hu hs2').symm
  have hUn : (U.subgroupOf (Subgroup.centralizer ({s} : Set Id2519.Tab.L5.S))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hUC]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have hgs : g * s = s * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hgN : (g : Id2519.Tab.L5.M5) * ((s : Id2519.Tab.L5.M5) - 1) =
        ((s : Id2519.Tab.L5.M5) - 1) * g := by
      have := congrArg (fun g : Id2519.Tab.L5.S => (g : Id2519.Tab.L5.M5)) hgs
      simp only [Matrix.SpecialLinearGroup.coe_mul] at this
      rw [Matrix.mul_sub, Matrix.sub_mul, this, Matrix.mul_one, Matrix.one_mul]
    intro u
    constructor
    · exact Id2519.Tab.L5.UG_conj_mem hgN
    · intro hu'
      have hgN' : ((g⁻¹ : Id2519.Tab.L5.S) : Id2519.Tab.L5.M5) * ((s : Id2519.Tab.L5.M5) - 1) =
          ((s : Id2519.Tab.L5.M5) - 1) * ((g⁻¹ : Id2519.Tab.L5.S) : Id2519.Tab.L5.M5) := by
        have hgs' : g⁻¹ * s = s * g⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgs, mul_inv_cancel_right]
        have := congrArg (fun g : Id2519.Tab.L5.S => (g : Id2519.Tab.L5.M5)) hgs'
        simp only [Matrix.SpecialLinearGroup.coe_mul] at this
        rw [Matrix.mul_sub, Matrix.sub_mul, this, Matrix.mul_one, Matrix.one_mul]
      have := Id2519.Tab.L5.UG_conj_mem hgN' hu'
      simpa [mul_assoc] using this
  have hU2 : IsPGroup 2 U := fun u => ⟨1, by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, pow_two]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact (Id2519.Tab.L5.mem_UG.mp u.2).mul_self⟩
  have hUTs : U ≤ Ts := hTsSyl.le_of_normal hUC hUn hU2
  have hU16 : 16 ≤ Nat.card ↥U :=
    card_UG_ge (Id2519.Tab.L5.N_ne_zero hs1) (Id2519.Tab.L5.N_sq hs2')
  have hUeq : U = Ts := by
    refine Subgroup.eq_of_le_of_card_ge hUTs ?_
    rw [hcardTs]
    omega
  have hTsq : ∀ t ∈ T, t ^ 2 = 1 := by
    intro t ht
    have htU : φ ⟨t, hTY ht⟩ ∈ U := by
      rw [hUeq]
      exact ⟨⟨t, hTY ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    have h1 : φ ⟨t, hTY ht⟩ * φ ⟨t, hTY ht⟩ = 1 :=
      Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul]
        exact (Id2519.Tab.L5.mem_UG.mp htU).mul_self)
    rw [← map_mul, ← map_one φ] at h1
    have h2 := congrArg Subtype.val (φ.injective h1)
    rw [pow_two]
    exact h2
  obtain ⟨eX⟩ := h.a6
  obtain ⟨y0, hy04, hy02⟩ := Id2519.exists_two_elt_alt6
  set yX : ↥X := eX.symm y0 with hyX
  set H := Y ⊓ Subgroup.centralizer ({a} : Set G) with hH
  set yH : ↥H := ⟨yX, h.comp.1 yX.2⟩ with hyH
  have hy4 : yH ^ 4 = 1 := by
    apply Subtype.ext
    have : (yX : G) ^ 4 = 1 := by
      have := congrArg (fun g : ↥X => (g : G)) (show yX ^ 4 = 1 by
        rw [hyX, ← map_pow, hy04, map_one])
      simpa using this
    simpa [hyH] using this
  have hyp : IsPGroup 2 (Subgroup.zpowers yH) := by
    refine IsPGroup.of_card_dvd_pow (n := 2) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by simpa using hy4)
  have hsq := sq_eq_one_of_sylow hT.toSylow (fun t ht => by
    rw [IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at ht
    exact Subtype.ext (by simpa using hTsq _ ht)) hyp
  apply hy02
  have h1 : (yX : G) ^ 2 = 1 := by
    have := congrArg Subtype.val hsq
    simpa [hyH] using this
  have h2 : yX ^ 2 = 1 := Subtype.ext (by simpa using h1)
  have h3 := congrArg eX h2
  rwa [hyX, map_pow, MulEquiv.apply_symm_apply, map_one] at h3

end InspHyp

end CFSG.Quasithin.E6
