module

public import CFSG.CGT.Timmesfeld75.WeaklyClosed
public import CFSG.RankThree.GF2n.Stroth80.Sec35

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem mem_Q_of_pi_conj_eq {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (H : StrothHyp M Q Z) {m : G} (hm : m ∈ M)
    (h : ∀ x ∈ Q, M₀.π (m * x * m⁻¹) = M₀.π x) : m ∈ Q := by
  refine H.centralizer_Qt m hm fun y hy => ?_
  have hmy : m * y * m⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 hm) y).mp hy
  exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hy hmy).mpr (h y hy)

theorem eq_of_pi_conj_eq {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {g : G}
    {S₁ S₂ : M₀.E → M₀.E} (h1 : ∀ x ∈ Q, M₀.π (g * x * g⁻¹) = S₁ (M₀.π x))
    (h2 : ∀ x ∈ Q, M₀.π (g * x * g⁻¹) = S₂ (M₀.π x)) : S₁ = S₂ := by
  funext e
  obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
  rw [← h1 x hx, ← h2 x hx]

theorem exists_actionHom_H0 {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (H : StrothHyp M Q Z) (h : GlobalModelData M Q Z γ M₀) :
    ∃ φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E),
      (∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) ∧
      (∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) ∧ ∀ (m : H0 M Z) e, M₀.Qf (φ m e) = M₀.Qf e := by
  have hex : ∀ m : ↥(H0 M Z), ∃ T : M₀.E ≃ₗ[K] M₀.E,
      (∀ x ∈ Q, M₀.π ((m : G) * x * (m : G)⁻¹) = T (M₀.π x)) ∧ ∀ e, M₀.Qf (T e) = M₀.Qf e := by
    intro m
    have hm : (m : G) ∈ M ⊓ Subgroup.centralizer (Z : Set G) := m.2
    obtain ⟨T, hT1, hT2, -⟩ := h.linear_of_centralizes hm.1 (fun z hz => by
      have := Subgroup.mem_centralizer_iff.mp hm.2 z hz
      rw [← this]; group)
    exact ⟨T, hT1, hT2⟩
  choose T hT1 hT2 using hex
  have hQ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q → (m : G) * x * (m : G)⁻¹ ∈ Q := fun m x hx =>
    (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 (m.2 : (m : G) ∈ M ⊓ _).1) x).mp hx
  refine ⟨{ toFun := T
            map_one' := ?_
            map_mul' := ?_ }, hT1, ?_, hT2⟩
  · refine LinearEquiv.ext fun e => ?_
    have := congrFun (eq_of_pi_conj_eq (M₀ := M₀) (g := ((1 : ↥(H0 M Z)) : G)) (S₁ := T 1)
      (S₂ := id) (hT1 1) (fun x _ => by simp)) e
    simpa using this
  · intro a b
    refine LinearEquiv.ext fun e => ?_
    have := congrFun (eq_of_pi_conj_eq (M₀ := M₀) (g := ((a * b : ↥(H0 M Z)) : G))
      (S₁ := T (a * b)) (S₂ := fun e => T a (T b e)) (hT1 (a * b)) (fun x hx => by
        rw [← hT1 b x hx, ← hT1 a _ (hQ b x hx)]
        simp [mul_assoc])) e
    simpa using this
  · intro m
    show T m = 1 ↔ _
    have hmM : (m : G) ∈ M := (m.2 : (m : G) ∈ M ⊓ _).1
    constructor
    · intro h1
      refine mem_Q_of_pi_conj_eq (M₀ := M₀) H hmM fun x hx => ?_
      rw [hT1 m x hx, h1]
      rfl
    · intro hmQ
      refine LinearEquiv.ext fun e => ?_
      have := congrFun (eq_of_pi_conj_eq (M₀ := M₀) (g := (m : G)) (S₁ := T m) (S₂ := id)
        (hT1 m) (fun x hx => Tim79.QuadModel.pi_conj_self (M₀ := M₀) hmQ hx)) e
      simpa using this

theorem exists_actionHom_M {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (H : StrothHyp M Q Z) (h : GlobalModelData M Q Z γ M₀) :
    ∃ φ : ↥M →* Equiv.Perm M₀.E,
      (∀ (m : M) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) ∧
      (∀ m : M, φ m = 1 ↔ (m : G) ∈ Q) ∧ (∀ (m : M) (e f : M₀.E), φ m (e + f) = φ m e + φ m f) ∧
      ∀ m : M, ∃ σ : K ≃+* K, ∀ (c : K) e, φ m (c • e) = σ c • φ m e := by
  have hex : ∀ m : ↥M, ∃ (T : M₀.E ≃+ M₀.E) (σ : K ≃+* K),
      (∀ x ∈ Q, M₀.π ((m : G) * x * (m : G)⁻¹) = T (M₀.π x)) ∧
        ∀ (c : K) e, T (c • e) = σ c • T e := by
    intro m
    obtain ⟨σ, a, T, hT1, hTπ, -, -⟩ := h.act m m.2
    exact ⟨T, σ, hTπ, hT1⟩
  choose T σ hT1 hT2 using hex
  have hQ : ∀ (m : ↥M) (x : G), x ∈ Q → (m : G) * x * (m : G)⁻¹ ∈ Q := fun m x hx =>
    (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 m.2) x).mp hx
  refine ⟨{ toFun := fun m => (T m).toEquiv
            map_one' := ?_
            map_mul' := ?_ }, hT1, ?_, fun m e f => (T m).map_add e f, fun m => ⟨σ m, hT2 m⟩⟩
  · refine Equiv.ext fun e => ?_
    have := congrFun (eq_of_pi_conj_eq (M₀ := M₀) (g := ((1 : ↥M) : G)) (S₁ := T 1)
      (S₂ := id) (hT1 1) (fun x _ => by simp)) e
    simpa using this
  · intro a b
    refine Equiv.ext fun e => ?_
    have := congrFun (eq_of_pi_conj_eq (M₀ := M₀) (g := ((a * b : ↥M) : G))
      (S₁ := T (a * b)) (S₂ := fun e => T a (T b e)) (hT1 (a * b)) (fun x hx => by
        rw [← hT1 b x hx, ← hT1 a _ (hQ b x hx)]
        simp [mul_assoc])) e
    simpa using this
  · intro m
    show (T m).toEquiv = 1 ↔ _
    constructor
    · intro h1
      refine mem_Q_of_pi_conj_eq (M₀ := M₀) H m.2 fun x hx => ?_
      rw [hT1 m x hx]
      exact congrArg (fun f : Equiv.Perm M₀.E => f (M₀.π x)) h1
    · intro hmQ
      refine Equiv.ext fun e => ?_
      have := congrFun (eq_of_pi_conj_eq (M₀ := M₀) (g := (m : G)) (S₁ := T m) (S₂ := id)
        (hT1 m) (fun x hx => Tim79.QuadModel.pi_conj_self (M₀ := M₀) hmQ hx)) e
      simpa using this

end CFSG.RankThree.GF2n.Stroth80

namespace CFSG.RankThree.GF2n.Stroth80

theorem ker_inf_range_eq_bot_of_pow_eq_one {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] {T : V →ₗ[K] V} {m : ℕ} (hm : Odd m) (hT : T ^ m = 1) :
    LinearMap.ker (T - 1) ⊓ LinearMap.range (T - 1) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, y, rfl⟩
  have hfix : T ((T - 1) y) = (T - 1) y := by
    have h0 : (T - 1) ((T - 1) y) = 0 := LinearMap.mem_ker.mp hx1
    simp only [LinearMap.sub_apply, Module.End.one_apply] at h0 ⊢
    exact sub_eq_zero.mp h0
  have hpow : ∀ i : ℕ, (T ^ i) ((T - 1) y) = (T - 1) y := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, Module.End.mul_apply, hfix, ih]
  have h1 : (∑ i ∈ Finset.range m, T ^ i) ((T - 1) y) = 0 := by
    have := geom_sum_mul T m
    rw [hT, sub_self] at this
    rw [← Module.End.mul_apply, this]
    rfl
  rw [LinearMap.sum_apply] at h1
  simp only [hpow, Finset.sum_const, Finset.card_range] at h1
  have hmK : (m : K) = 1 := by
    obtain ⟨k, rfl⟩ := hm
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    push_cast
    rw [h2]
    simp
  rw [← Nat.cast_smul_eq_nsmul K, hmK, one_smul] at h1
  simp [h1]

theorem ker_sup_range_eq_top_of_pow_eq_one {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {T : V →ₗ[K] V} {m : ℕ} (hm : Odd m) (hT : T ^ m = 1) :
    LinearMap.ker (T - 1) ⊔ LinearMap.range (T - 1) = ⊤ := by
  have hinf := ker_inf_range_eq_bot_of_pow_eq_one hm hT
  apply Submodule.eq_top_of_finrank_eq
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (T - 1))
    (LinearMap.range (T - 1))
  rw [hinf, finrank_bot, add_zero] at h1
  rw [h1]
  have := LinearMap.finrank_range_add_finrank_ker (T - 1)
  omega

theorem exists_fixed_vector_of_isPGroup {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Finite V] (Λ : Subgroup (V ≃ₗ[K] V)) (hΛ : IsPGroup 2 Λ)
    (S : Submodule K V) (hS : ∀ T ∈ Λ, ∀ v ∈ S, T v ∈ S) (hS0 : S ≠ ⊥) :
    ∃ v ∈ S, v ≠ 0 ∧ ∀ T ∈ Λ, T v = v := by
  letI : MulAction Λ S :=
    { smul := fun T v => ⟨T.1 v.1, hS T.1 T.2 v.1 v.2⟩
      one_smul := fun v => Subtype.ext rfl
      mul_smul := fun a b v => Subtype.ext rfl }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hΛ.card_modEq_card_fixedPoints S
  have hSeven : 2 ∣ Nat.card S := by
    haveI : Module.Finite K S := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := K) (V := S)]
    have hK : 2 ∣ Nat.card K := by
      haveI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).mp (FiniteField.cast_card_eq_zero K)
    have hpos : Module.finrank K S ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      exact hS0
    exact dvd_pow hK hpos
  have hF : 2 ∣ Nat.card (MulAction.fixedPoints Λ S) :=
    (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).mpr hSeven))
  by_contra hcon
  push Not at hcon
  have hsub : Subsingleton (MulAction.fixedPoints Λ S) := by
    have h0 : ∀ a : MulAction.fixedPoints Λ S, (a : S) = 0 := by
      intro a
      by_contra h
      have hne : (a : S).1 ≠ 0 := fun h' => h (Subtype.ext h')
      obtain ⟨T, hT, hTv⟩ := hcon (a : S).1 (a : S).2 hne
      apply hTv
      have := MulAction.mem_fixedPoints.mp a.2 ⟨T, hT⟩
      exact congrArg Subtype.val this
    exact ⟨fun a b => Subtype.ext ((h0 a).trans (h0 b).symm)⟩
  have hle : Nat.card (MulAction.fixedPoints Λ S) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr hsub
  haveI : Nonempty (MulAction.fixedPoints Λ S) :=
    ⟨⟨0, MulAction.mem_fixedPoints.mpr fun g => Subtype.ext (map_zero g.1)⟩⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints Λ S) := Nat.card_pos
  have := Nat.le_of_dvd hpos hF
  omega

end CFSG.RankThree.GF2n.Stroth80

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Lgen_normalizes (M L : Subgroup G) : M ≤ Subgroup.normalizer (Lgen M L : Set G) := by
  intro m hm
  refine conjSubgroup_eq_self_iff.mp (conjSubgroup_eq_of_le ?_)
  unfold Lgen
  show Subgroup.map _ _ ≤ _
  rw [Subgroup.map_iSup]
  refine iSup_le fun m' => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hm' => ?_
  have h1 : conjSubgroup m (conjSubgroup m' L) = conjSubgroup (m * m') L :=
    (conjSubgroup_mul m m' L).symm
  exact h1.le.trans (le_iSup₂_of_le (m * m') (M.mul_mem hm hm') le_rfl)

theorem le_Lgen_self (M L : Subgroup G) : L ≤ Lgen M L := by
  unfold Lgen
  have : conjSubgroup 1 L ≤ ⨆ (m : G) (_ : m ∈ M), conjSubgroup m L :=
    le_iSup₂_of_le 1 M.one_mem le_rfl
  rwa [conjSubgroup_one] at this

theorem Ctx.not_commutative_genB (hc : Ctx M Q Z B) :
    ¬ ∀ x ∈ (⨆ (m : G) (_ : m ∈ M), conjSubgroup m B), ∀ y ∈ (⨆ (m : G) (_ : m ∈ M),
      conjSubgroup m B), x * y = y * x := by
  intro hcomm
  set S : Subgroup G := Lgen M B with hSdef
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hSQ : S ≤ Q := by
    refine iSup₂_le fun m hm => ?_
    exact (Subgroup.map_mono hc.le : conjSubgroup m B ≤ conjSubgroup m Q).trans
      (hc.conj_Q_eq hm).le
  have hSnorm : ∀ m ∈ M, conjSubgroup m S = S := fun m hm =>
    conjSubgroup_eq_self_iff.mpr (Lgen_normalizes M B hm)
  have hSnZ : S ≤ Subgroup.normalizer (Z : Set G) := fun s hs =>
    hc.hyp.Z_normal.2 (hQM (hSQ hs))
  haveI : IsMulCommutative ↥Z := hc.hyp.maxAb.prop.2.2
  have hcommSZ : IsMulCommutative ↥(S ⊔ Z) := by
    refine IsMulCommutative.of_setLike_mul_comm fun x hx y hy => ?_
    obtain ⟨s, hs, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hSnZ hx
    obtain ⟨s', hs', z', hz', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hSnZ hy
    have h1 : s * s' = s' * s := hcomm s hs s' hs'
    have h2 : z * s' = s' * z := hc.hyp.toHyp79.V_central hz (hSQ hs')
    have h3 : s * z' = z' * s := (hc.hyp.toHyp79.V_central hz' (hSQ hs)).symm
    have h4 : z * z' = z' * z := setLike_mul_comm hz hz'
    calc s * z * (s' * z') = s * (z * s') * z' := by group
      _ = s * (s' * z) * z' := by rw [h2]
      _ = (s * s') * (z * z') := by group
      _ = (s' * s) * (z' * z) := by rw [h1, h4]
      _ = s' * (s * z') * z := by group
      _ = s' * (z' * s) * z := by rw [h3]
      _ = s' * z' * (s * z) := by group
  have hP : (S ⊔ Z) ≤ M ∧ M ≤ Subgroup.normalizer ((S ⊔ Z : Subgroup G) : Set G) ∧
      IsMulCommutative ↥(S ⊔ Z) :=
    ⟨sup_le (hSQ.trans hQM) (hZQ.trans hQM), fun m hm => conjSubgroup_eq_self_iff.mp
      (by rw [conjSubgroup_sup', hSnorm m hm, hc.conj_Z_eq hm]), hcommSZ⟩
  have hmax : S ⊔ Z ≤ Z := hc.hyp.maxAb.2 hP le_sup_right
  have hBZ : B ≤ Z := (le_Lgen_self M B).trans (le_sup_left.trans hmax)
  obtain ⟨g, hg⟩ := hc.conj
  exact hc.ne (Subgroup.eq_of_le_of_card_ge hBZ (by rw [hg, card_conjSubgroup]))

end CFSG.RankThree.GF2n.Stroth80
