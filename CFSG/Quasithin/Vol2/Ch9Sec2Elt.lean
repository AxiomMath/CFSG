module

public import CFSG.Quasithin.Vol2.Ch9Sec1Adapt
public import CFSG.Quasithin.Vol2.Ch9Lem922
public import CFSG.Quasithin.Background.HOm4UT

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin.H CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits Matrix
open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem rho_smul_e11 {K : Type} [Field K]
    {p : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
    (hp : p ∈ (uni K).prod (uni K)) (c : K) :
    Om4.rho p (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
      Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]) := by
  obtain ⟨a, ha⟩ := mem_uni_iff.mp hp.1
  obtain ⟨b, hb⟩ := mem_uni_iff.mp hp.2
  apply Multiplicative.toAdd.injective
  rw [toAdd_rho, toAdd_ofAdd, ha, hb]
  ext i j
  rw [mul_mul_transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem exists_rho_smul_e11 {K : Type} [Field K] {c a : K} (hc : c ≠ 0) (ha : a ≠ 0) :
    (∃ γ, Om4.rho γ (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
      Multiplicative.ofAdd !![a, 0; 0, 0]) ∧
    (∃ γ, Om4.rho γ (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
      Multiplicative.ofAdd !![0, a; 0, 0]) ∧
    (∃ γ, Om4.rho γ (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
      Multiplicative.ofAdd !![0, 0; a, 0]) ∧
    (∃ γ, Om4.rho γ (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
      Multiplicative.ofAdd !![0, 0; 0, a]) := by
  let g₁ : SpecialLinearGroup (Fin 2) K :=
    ⟨!![a / c, 0; 0, c / a], by simp [Matrix.det_fin_two_of]; field_simp⟩
  let g₂ : SpecialLinearGroup (Fin 2) K :=
    ⟨!![0, -(c / a); a / c, 0], by simp [Matrix.det_fin_two_of]; field_simp⟩
  let h₂ : SpecialLinearGroup (Fin 2) K := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩
  have key : ∀ (g h : SpecialLinearGroup (Fin 2) K) (Y : Matrix (Fin 2) (Fin 2) K),
      (∀ i j, ((g : Matrix (Fin 2) (Fin 2) K) * (c • !![(1 : K), 0; 0, 0]) *
        (h : Matrix (Fin 2) (Fin 2) K)ᵀ) i j = Y i j) →
      Om4.rho (g, h) (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
        Multiplicative.ofAdd Y := by
    intro g h Y hY
    apply Multiplicative.toAdd.injective
    rw [toAdd_rho, toAdd_ofAdd, toAdd_ofAdd]
    ext i j
    exact hY i j
  refine ⟨⟨(g₁, 1), key _ _ _ fun i j => ?_⟩, ⟨(g₁, h₂), key _ _ _ fun i j => ?_⟩,
    ⟨(g₂, 1), key _ _ _ fun i j => ?_⟩, ⟨(g₂, h₂), key _ _ _ fun i j => ?_⟩⟩
  all_goals
    rw [mul_mul_transpose_apply]
    fin_cases i <;> fin_cases j <;> (simp [g₁, g₂, h₂]; try field_simp)

omit [Finite G] in
theorem aut_pow_eq_one {K : Type} [Field K] (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (τ : K ≃+* K) : τ ^ n = 1 := by
  obtain ⟨σ, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  rw [← hcard]
  exact pow_card_eq_one'

noncomputable abbrev bar {K : Type} [Field K] (e : ↥(fsuV T I) ≃* Om4.VM K) :
    ↥(Subgroup.normalizer (fsuV T I : Set G)) →* MulAut (Om4.VM K) :=
  (MulAut.congr e).toMonoidHom.comp (conjAct (fsuV T I))

omit [Finite G] in
theorem bar_apply {K : Type} [Field K] (e : ↥(fsuV T I) ≃* Om4.VM K)
    (x : ↥(Subgroup.normalizer (fsuV T I : Set G))) (v : ↥(fsuV T I)) :
    bar e x (e v) = e ⟨(x : G) * v * (x : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp x.2 v).mp v.2⟩ := by
  show e ((conjAct (fsuV T I) x) (e.symm (e v))) = _
  rw [MulEquiv.symm_apply_apply]
  exact congrArg e (Subtype.ext (coe_conjAct_apply _ _ _))

omit [Finite G] in
theorem mem_centralizer_of_bar {K : Type} [Field K] (e : ↥(fsuV T I) ≃* Om4.VM K)
    (x : ↥(Subgroup.normalizer (fsuV T I : Set G))) (hx : bar e x = 1) :
    (x : G) ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h := congrArg (fun φ : MulAut (Om4.VM K) => φ (e ⟨v, hv⟩)) hx
  simp only [bar_apply, MulAut.one_apply] at h
  have h2 : (x : G) * v * (x : G)⁻¹ = v := congrArg Subtype.val (e.injective h)
  calc v * (x : G) = ((x : G) * v * (x : G)⁻¹) * x := by rw [h2]
    _ = x * v := by group

namespace Setup

variable (S : Setup T L I n)

structure IsCoord {K : Type} [Field K] [Fintype K] [CharP K 2] (e : ↥(fsuV T I) ≃* Om4.VM K)
    (ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) :
    Prop where
  card : Fintype.card K = 2 ^ n
  surj : Function.Surjective ψ
  act : ∀ k : ↥(fsuL0 T L), MulAut.congr e
    (conjAct (fsuV T I) (Subgroup.inclusion S.L0_le_normalizer_V k)) = Om4.rho (ψ k)
  sylow : ((T ⊓ fsuL0 T L).subgroupOf (fsuL0 T L)).map ψ = (uni K).prod (uni K)

theorem exists_isCoord : ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2)
    (e : ↥(fsuV T I) ≃* Om4.VM K)
    (ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K),
    S.IsCoord e ψ := by
  obtain ⟨K, _, _, _, hK, e, ψ, hs, ha, hT⟩ := S.exists_coord_adapted
  exact ⟨K, inferInstance, inferInstance, inferInstance, e, ψ, ⟨hK, hs, ha, hT⟩⟩

namespace IsCoord

variable {S} {K : Type} [Field K] [Fintype K] [CharP K 2] {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem four_le : 4 ≤ Nat.card K := by
  rw [Nat.card_eq_fintype_card, hc.card]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) S.two_le

theorem natCard : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hc.card]

theorem bar_L0 (k : ↥(fsuL0 T L)) :
    bar e (Subgroup.inclusion S.L0_le_normalizer_V k) = Om4.rho (ψ k) := hc.act k

theorem map_autOn : (autOn (fsuL0 T L) (fsuV T I)).map (MulAut.congr e).toMonoidHom =
    (Om4.rho (K := K)).range := by
  ext φ
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyL : (y : G) ∈ fsuL0 T L := hy
    refine ⟨ψ ⟨y, hyL⟩, ?_⟩
    rw [← hc.act]
    rfl
  · rintro ⟨γ, rfl⟩
    obtain ⟨k, rfl⟩ := hc.surj γ
    rw [← hc.act]
    exact ⟨_, ⟨Subgroup.inclusion S.L0_le_normalizer_V k, k.2, rfl⟩, rfl⟩

theorem exists_form {x : G} (hx : x ∈ fsuM T L) :
    ∃ (A B : GL (Fin 2) K) (τ : K ≃+* K),
      bar e ⟨x, S.hMN hx⟩ = Om4.lr A B * Om4.frM τ ∨
        bar e ⟨x, S.hMN hx⟩ = Om4.lr A B * Om4.frM τ * Om4.trM :=
  S.exists_form hc.card hc.map_autOn
    (S.autOn_M_le_normalizer ⟨⟨x, S.hMN hx⟩, hx, rfl⟩)

theorem isNS_of_odd {x : G} (hx : x ∈ fsuM T L) (hodd : Odd (orderOf x)) :
    ∃ (A B : GL (Fin 2) K) (τ : K ≃+* K), bar e ⟨x, S.hMN hx⟩ = Om4.lr A B * Om4.frM τ := by
  obtain ⟨A, B, τ, h | h⟩ := hc.exists_form hx
  · exact ⟨A, B, τ, h⟩
  · exfalso
    have hd : orderOf (bar e ⟨x, S.hMN hx⟩) ∣ orderOf x := by
      have := orderOf_map_dvd (bar e) (⟨x, S.hMN hx⟩ : ↥(Subgroup.normalizer (fsuV T I : Set G)))
      rwa [Subgroup.orderOf_mk] at this
    rw [h] at hd
    exact Om4.not_odd_orderOf_swap A B τ (Odd.of_dvd_nat hodd hd)

theorem toAdd_e_eq {v : G}
    (hv : v ∈ fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)) :
    Multiplicative.toAdd (e ⟨v, hv.1⟩) =
      Multiplicative.toAdd (e ⟨v, hv.1⟩) 0 0 • !![(1 : K), 0; 0, 0] := by
  have hfix : ∀ p ∈ (uni K).prod (uni K), Om4.rho p (e ⟨v, hv.1⟩) = e ⟨v, hv.1⟩ := by
    intro p hp
    rw [← hc.sylow] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    rw [← hc.bar_L0, bar_apply]
    congr 1
    refine Subtype.ext ?_
    show (t : G) * v * (t : G)⁻¹ = v
    rw [Subgroup.mem_centralizer_iff.mp hv.2 _ (Subgroup.mem_subgroupOf.mp ht),
      mul_inv_cancel_right]
  rw [fixV_rho_uni_prod hfix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem symm_mem (c : K) :
    ((e.symm (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) : ↥(fsuV T I)) : G) ∈
      fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) := by
  set w := e.symm (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) with hw
  refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
  have htL : t ∈ fsuL0 T L := ht.2
  have h1 := rho_smul_e11 (p := ψ ⟨t, htL⟩) (by
    rw [← hc.sylow]
    exact ⟨⟨t, htL⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩) c
  rw [← hc.bar_L0] at h1
  have h2 : e w = Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]) := by
    rw [hw, MulEquiv.apply_symm_apply]
  rw [← h2, bar_apply] at h1
  have h3 : t * w * t⁻¹ = w := congrArg Subtype.val (e.injective h1)
  calc t * (w : G) = (t * w * t⁻¹) * t := by group
    _ = w * t := by rw [h3]

theorem exists_z (h1 : zQ T I = fsuV T I) :
    ∃ (z : G) (hz : z ∈ fsuV T I), z ∈ quasithinOmegaOneCenter T ∧ ∃ c : K, c ≠ 0 ∧
      e ⟨z, hz⟩ = Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]) := by
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp
    (fsuV_inf_omegaOneCenter_ne_bot S.hyp.fsu S.hV S.hN))
  have hz' : (z : G) ∈ fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) :=
    S.omegaOneCenter_T_le h1 hz.2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  refine ⟨z, hz.1, hz.2, Multiplicative.toAdd (e ⟨z, hz.1⟩) 0 0, fun h0 => hz1' ?_, ?_⟩
  · have h2 := hc.toAdd_e_eq hz'
    rw [h0, zero_smul] at h2
    have h3 : e ⟨z, hz.1⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h2]
      rfl
    have := congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h3)
    exact this
  · apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    exact hc.toAdd_e_eq hz'

theorem isUT_of_mem_centralizer (h1 : zQ T I = fsuV T I) {x : G} (hx : x ∈ fsuM T L)
    (hodd : Odd (orderOf x))
    (hxZ : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ∃ (A B : GL (Fin 2) K) (τ : K ≃+* K), Om4.IsUT A ∧ Om4.IsUT B ∧
      bar e ⟨x, S.hMN hx⟩ = Om4.lr A B * Om4.frM τ := by
  obtain ⟨A, B, τ, h⟩ := hc.isNS_of_odd hx hodd
  obtain ⟨z, hzV, hzZ, c, hc0, hze⟩ := hc.exists_z h1
  have hfix : bar e ⟨x, S.hMN hx⟩ (e ⟨z, hzV⟩) = e ⟨z, hzV⟩ := by
    rw [bar_apply]
    congr 1
    refine Subtype.ext ?_
    show x * z * x⁻¹ = z
    rw [← Subgroup.mem_centralizer_iff.mp hxZ z hzZ, mul_inv_cancel_right]
  rw [h, hze] at hfix
  have h2 := congrArg Multiplicative.toAdd hfix
  rw [Om4.toAdd_apply_smul_e11, toAdd_ofAdd] at h2
  have hτc : τ c ≠ 0 := by rwa [Ne, map_eq_zero_iff τ τ.injective]
  have h3 : (A : Matrix (Fin 2) (Fin 2) K) * !![(1 : K), 0; 0, 0] *
      (B : Matrix (Fin 2) (Fin 2) K)ᵀ = (c / τ c) • !![(1 : K), 0; 0, 0] := by
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hτc, one_smul]
  obtain ⟨hA, hB⟩ := Om4.isUT_of_mul_e11 h3
  exact ⟨A, B, τ, hA, hB, h⟩

theorem pow_mem_centralizer (h1 : zQ T I = fsuV T I) {x : G} (hx : x ∈ fsuM T L)
    (hodd : Odd (orderOf x))
    (hxZ : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    x ^ (n * (2 ^ n - 1)) ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  obtain ⟨A, B, τ, hA, hB, h⟩ := hc.isUT_of_mem_centralizer h1 hx hodd hxZ
  have hτ : τ ^ n = 1 := aut_pow_eq_one (by have := S.two_le; omega) hc.natCard τ
  have hpow := Om4.pow_eq_one_of_isUT hA hB hτ
  rw [hc.card, ← h] at hpow
  set y : ↥(Subgroup.normalizer (fsuV T I : Set G)) := ⟨x, S.hMN hx⟩ with hy
  have hyodd : Odd (orderOf (bar e y)) := by
    have := orderOf_map_dvd (bar e) y
    rw [hy, Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hodd this
  have hdvd : orderOf (bar e y) ∣ n * (2 ^ n - 1) := by
    have h2 := orderOf_dvd_of_pow_eq_one hpow
    exact (Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.coprime_two_right.mpr hyodd) h2)
  have h3 : bar e (y ^ (n * (2 ^ n - 1))) = 1 := by
    rw [map_pow]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have := mem_centralizer_of_bar e _ h3
  simpa [hy] using this

end IsCoord

include S in
theorem comm_mem_pCoreOf (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) {x : G} (hx : x ∈ fsuM T L)
    (hxV : x ∈ Subgroup.centralizer (fsuV T I : Set G)) :
    ∀ l ∈ fsuL0 T L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 (fsuL0 T L) := by
  intro l hl
  refine S.inf_centralizer_L0_le h37c h38c ⟨?_, ?_⟩
  · have h1 : x * l * x⁻¹ ∈ fsuL0 T L := (Subgroup.mem_normalizer_iff.mp hx l).mp hl
    exact (fsuL0 T L).mul_mem h1 ((fsuL0 T L).inv_mem hl)
  · refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hlN := S.L0_le_normalizer_V hl
    have hv' : l⁻¹ * v * l ∈ fsuV T I := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlN) v).mp hv
      simpa using this
    have hc1 := Subgroup.mem_centralizer_iff.mp hxV v hv
    have hc2 := Subgroup.mem_centralizer_iff.mp hxV _ hv'
    have hc2' : (l⁻¹ * v * l) * x⁻¹ = x⁻¹ * (l⁻¹ * v * l) := by
      calc (l⁻¹ * v * l) * x⁻¹ = x⁻¹ * (x * (l⁻¹ * v * l)) * x⁻¹ := by group
        _ = x⁻¹ * ((l⁻¹ * v * l) * x) * x⁻¹ := by rw [← hc2]
        _ = x⁻¹ * (l⁻¹ * v * l) := by group
    calc v * (x * l * x⁻¹ * l⁻¹) = (v * x) * l * x⁻¹ * l⁻¹ := by group
      _ = (x * v) * l * x⁻¹ * l⁻¹ := by rw [hc1]
      _ = x * l * ((l⁻¹ * v * l) * x⁻¹) * l⁻¹ := by group
      _ = x * l * (x⁻¹ * (l⁻¹ * v * l)) * l⁻¹ := by rw [hc2']
      _ = x * l * x⁻¹ * l⁻¹ * v := by group

namespace IsCoord

variable {S} {K : Type} [Field K] [Fintype K] [CharP K 2] {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem le_centralizer_T (hn : Odd n) :
    fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) ≤
      Subgroup.centralizer (T : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have htM : t ∈ fsuM T L := T_le_fsuM ht
  set y : ↥(Subgroup.normalizer (fsuV T I : Set G)) := ⟨t, S.hMN htM⟩ with hy
  have hV1 : ∀ w ∈ fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G),
      t * w * t⁻¹ ∈ fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) := by
    rintro w ⟨hwV, hwC⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (S.hMN htM) w).mp hwV,
      Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hs' : t⁻¹ * s * t ∈ T ⊓ fsuL0 T L := by
      refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hs.1) ht, ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (T_le_normalizer_L0 ht))
        s).mp hs.2
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.mp hwC _ hs'
    calc s * (t * w * t⁻¹) = t * ((t⁻¹ * s * t) * w) * t⁻¹ := by group
      _ = t * (w * (t⁻¹ * s * t)) * t⁻¹ := by rw [h2]
      _ = t * w * t⁻¹ * s := by group
  have hform : ∃ (μ : K) (τ : K ≃+* K), μ ≠ 0 ∧ ∀ c : K,
      bar e y (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
        Multiplicative.ofAdd ((μ * τ c) • !![(1 : K), 0; 0, 0]) := by
    obtain ⟨A, B, τ, h | h⟩ := hc.exists_form htM
    all_goals
      have hE : ∀ c : K, bar e y (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
          (Om4.lr A B * Om4.frM τ) (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) := by
        intro c
        rw [hy, h]
        try rw [MulAut.mul_apply, Om4.trM_smul_e11]
      have hw := hc.symm_mem (e := e) 1
      have h2 := hc.toAdd_e_eq (hV1 _ hw)
      have h3 : e ⟨t * (e.symm (Multiplicative.ofAdd ((1 : K) • !![(1 : K), 0; 0, 0])) : G) *
          t⁻¹, (hV1 _ hw).1⟩ = bar e y (Multiplicative.ofAdd ((1 : K) • !![(1 : K), 0; 0, 0])) := by
        rw [← bar_apply e y, MulEquiv.apply_symm_apply]
      rw [h3, hE, Om4.toAdd_apply_smul_e11, map_one, one_smul] at h2
      obtain ⟨hA, hB⟩ := Om4.isUT_of_mul_e11 h2
      obtain ⟨hA0, -⟩ := hA.apply_ne_zero
      obtain ⟨hB0, -⟩ := hB.apply_ne_zero
      exact ⟨_, τ, mul_ne_zero hA0 hB0, fun c => by rw [hE, Om4.apply_smul_e11 hA hB]⟩
  obtain ⟨μ, τ, hμ, hact⟩ := hform
  let P : ℕ → K := fun j => Nat.rec 1 (fun _ p => μ * τ p) j
  have hiter : ∀ j : ℕ, ∀ c : K, (bar e y ^ j) (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
      Multiplicative.ofAdd ((P j * (τ ^ j) c) • !![(1 : K), 0; 0, 0]) := by
    intro j
    induction j with
    | zero => intro c; simp [P]
    | succ j ih =>
      intro c
      rw [pow_succ', MulAut.mul_apply, ih, hact, pow_succ', RingAut.mul_apply, map_mul]
      congr 2
      simp only [P]
      ring
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.hyp.fsu.sylow.1) ⟨t, ht⟩
  have hk' : orderOf t = 2 ^ k := by rw [← hk, Subgroup.orderOf_mk]
  have hy1 : bar e y ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : y ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hk', pow_orderOf_eq_one]
      rfl
    rw [this, map_one]
  have hP : ∀ c : K, P (2 ^ k) * (τ ^ 2 ^ k) c = c := by
    intro c
    have := hiter (2 ^ k) c
    rw [hy1, MulAut.one_apply] at this
    have h2 := congrArg
      (fun X : Om4.VM K => (Multiplicative.toAdd X : Matrix (Fin 2) (Fin 2) K) 0 0)
      this
    simpa using h2.symm
  have hP1 : P (2 ^ k) = 1 := by simpa using hP 1
  have hτk : τ ^ 2 ^ k = 1 := RingEquiv.ext fun c => by
    have := hP c
    rw [hP1, one_mul] at this
    exact this
  have hτn : τ ^ n = 1 := aut_pow_eq_one (by have := S.two_le; omega) hc.natCard τ
  have hτ1 : τ = 1 := by
    have h2 : orderOf τ ∣ Nat.gcd (2 ^ k) n :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hτk) (orderOf_dvd_of_pow_eq_one hτn)
    have h3 : Nat.gcd (2 ^ k) n = 1 :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hn)
    rw [h3, Nat.dvd_one, orderOf_eq_one_iff] at h2
    exact h2
  have hPj : ∀ j, P j = μ ^ j := by
    intro j
    induction j with
    | zero => simp [P]
    | succ j ih => simp only [P] at ih ⊢; rw [ih, hτ1, RingAut.one_apply, pow_succ, mul_comm]
  have hμ1 : μ = 1 := by
    have h2 : μ ^ 2 ^ k = 1 := by rw [← hPj]; exact hP1
    have h3 : μ ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one μ hμ
    have h4 : orderOf μ ∣ Nat.gcd (2 ^ k) (Fintype.card K - 1) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    have h5 : Nat.gcd (2 ^ k) (Fintype.card K - 1) = 1 := by
      rw [hc.card]
      refine Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ?_)
      exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by
        have := S.two_le; omega⟩) odd_one
    rw [h5, Nat.dvd_one, orderOf_eq_one_iff] at h4
    exact h4
  have hv2 := hc.toAdd_e_eq hv
  set c := (Multiplicative.toAdd (e ⟨v, hv.1⟩) : Matrix (Fin 2) (Fin 2) K) 0 0 with hcdef
  have hev : e ⟨v, hv.1⟩ = Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    exact hv2
  have hfix : bar e y (e ⟨v, hv.1⟩) = e ⟨v, hv.1⟩ := by
    rw [hev, hact, hμ1, hτ1, one_mul, RingAut.one_apply]
  rw [bar_apply] at hfix
  have h5 : t * v * t⁻¹ = v := congrArg Subtype.val (e.injective hfix)
  calc t * v = (t * v * t⁻¹) * t := by group
    _ = v * t := by rw [h5]


theorem fsuV_eq_conjClosure (h1 : zQ T I = fsuV T I) :
    fsuV T I = conjClosure (fsuV T I ⊓ Subgroup.centralizer (T : Set G)) (fsuL0 T L) := by
  refine le_antisymm ?_ (conjClosure_le fun l hl v hv =>
    (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V hl) v).mp hv.1)
  obtain ⟨z, hzV, hzZ, c, hc0, hze⟩ := hc.exists_z h1
  have hzVC : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [← S.omegaOneCenter_T_eq h1]
    exact hzZ
  set W := conjClosure (fsuV T I ⊓ Subgroup.centralizer (T : Set G)) (fsuL0 T L) with hW
  have hpart : ∀ γ, ((e.symm (Om4.rho γ (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]))) :
      ↥(fsuV T I)) : G) ∈ W := by
    intro γ
    obtain ⟨k, rfl⟩ := hc.surj γ
    rw [← hze, ← hc.bar_L0, bar_apply, MulEquiv.symm_apply_apply]
    exact mem_conjClosure k.2 hzVC
  have hone : ((e.symm (Multiplicative.ofAdd (0 : Matrix (Fin 2) (Fin 2) K)) : ↥(fsuV T I)) :
      G) ∈ W := by
    rw [show Multiplicative.ofAdd (0 : Matrix (Fin 2) (Fin 2) K) = 1 from rfl, map_one]
    exact W.one_mem
  have hsingle : ∀ a : K,
      ((e.symm (Multiplicative.ofAdd !![a, 0; 0, 0]) : ↥(fsuV T I)) : G) ∈ W ∧
      ((e.symm (Multiplicative.ofAdd !![0, a; 0, 0]) : ↥(fsuV T I)) : G) ∈ W ∧
      ((e.symm (Multiplicative.ofAdd !![0, 0; a, 0]) : ↥(fsuV T I)) : G) ∈ W ∧
      ((e.symm (Multiplicative.ofAdd !![0, 0; 0, a]) : ↥(fsuV T I)) : G) ∈ W := by
    intro a
    by_cases ha : a = 0
    · subst ha
      have h0 : !![(0 : K), 0; 0, 0] = 0 := by ext i j; fin_cases i <;> fin_cases j <;> rfl
      rw [h0]
      exact ⟨hone, hone, hone, hone⟩
    · obtain ⟨⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩, ⟨γ₃, h₃⟩, ⟨γ₄, h₄⟩⟩ := exists_rho_smul_e11 hc0 ha
      exact ⟨h₁ ▸ hpart γ₁, h₂ ▸ hpart γ₂, h₃ ▸ hpart γ₃, h₄ ▸ hpart γ₄⟩
  intro w hw
  set X : Matrix (Fin 2) (Fin 2) K := Multiplicative.toAdd (e ⟨w, hw⟩) with hXdef
  have hX : Multiplicative.ofAdd X = Multiplicative.ofAdd !![X 0 0, 0; 0, 0] *
      Multiplicative.ofAdd !![0, X 0 1; 0, 0] * Multiplicative.ofAdd !![0, 0; X 1 0, 0] *
      Multiplicative.ofAdd !![0, 0; 0, X 1 1] := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hw' : w = ((e.symm (Multiplicative.ofAdd X)) : G) := by
    rw [hXdef, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  rw [hw', hX, map_mul, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul]
  obtain ⟨h00, -, -, -⟩ := hsingle (X 0 0)
  obtain ⟨-, h01, -, -⟩ := hsingle (X 0 1)
  obtain ⟨-, -, h10, -⟩ := hsingle (X 1 0)
  obtain ⟨-, -, -, h11⟩ := hsingle (X 1 1)
  exact W.mul_mem (W.mul_mem (W.mul_mem h00 h01) h10) h11

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
