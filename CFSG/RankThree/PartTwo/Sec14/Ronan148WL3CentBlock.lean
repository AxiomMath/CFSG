module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentTorus
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentNT
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
import CFSG.RankThree.PartTwo.Sec4.RonanK432L3HardMat
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] def IsBlockAct (π : Bool) (p f : ℕ) (K : Type) [Field K] (ε : Kˣ)
    (β : MulAut (projImage (slPi π 3 (p ^ f) K))) : Prop :=
  (∃ y : GL (Fin 3) K, y * diagE ε = diagE ε * y ∧ ∀ m : projImage (slPi π 3 (p ^ f) K),
    (β m : ProjGenLinGroup (Fin 3) K) = pmk y * (m : ProjGenLinGroup (Fin 3) K) * (pmk y)⁻¹) ∨
  (∃ (σ : K ≃+* K) (g : GL (Fin 3) K), g * diagE ε = diagE ε * g ∧
    ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      (β (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) = pmk (g * frobGL σ s * g⁻¹))

theorem frobGL_diagE (σ : K ≃+* K) {ε : Kˣ} (hσε : σ (ε : K) = ε) :
    frobGL σ (diagE ε) = diagE ε := by
  rw [diagE, frobGL_diagUnits, map_one]
  congr 1
  exact Units.ext hσε

theorem commute_diagE_of_frob (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {ε : Kˣ}
    (hε3 : (ε : K) ^ 3 = 1) {σ : K ≃+* K} (hσε : σ (ε : K) = ε) {g s₀ : GL (Fin 3) K} {c : Kˣ}
    (hs₀ : pmk s₀ = pmk (diagE ε))
    (h : g * frobGL σ s₀ * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * s₀) :
    g * diagE ε = diagE ε * g := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hs₀
  have hs : s₀ = diagE ε * GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by
    rw [← hu, map_inv, mul_inv_cancel_right]
  rw [hs, map_mul, frobGL_scalar, frobGL_diagE σ hσε] at h
  have hsc : ∀ (w : Kˣ) (y : GL (Fin 3) K),
      y * GeneralLinearGroup.scalar (Fin 3) w = GeneralLinearGroup.scalar (Fin 3) w * y :=
    fun w y => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar w y).eq
  set S := GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) u⁻¹) with hSdef
  have e1 : g * (diagE ε * S) * g⁻¹ = g * diagE ε * g⁻¹ * S := by
    calc g * (diagE ε * S) * g⁻¹ = g * diagE ε * (S * g⁻¹) := by group
      _ = g * diagE ε * (g⁻¹ * S) := by rw [hsc _ g⁻¹]
      _ = g * diagE ε * g⁻¹ * S := by group
  have e2 : GeneralLinearGroup.scalar (Fin 3) c * (diagE ε * GeneralLinearGroup.scalar (Fin 3) u⁻¹)
      = GeneralLinearGroup.scalar (Fin 3) (c * u⁻¹) * diagE ε := by
    rw [hsc u⁻¹ (diagE ε), map_mul]
    group
  refine commute_of_conj_diagE (hK.three_ne_zero hq) hε3
    (c := c * u⁻¹ * (Units.map (σ : K →* K) u⁻¹)⁻¹) ?_
  calc g * diagE ε * g⁻¹ = (g * diagE ε * g⁻¹ * S) * S⁻¹ := by group
    _ = GeneralLinearGroup.scalar (Fin 3) (c * u⁻¹) * diagE ε * S⁻¹ := by rw [← e1, h, e2]
    _ = GeneralLinearGroup.scalar (Fin 3) (c * u⁻¹) *
        (diagE ε * GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) u⁻¹)⁻¹) := by
          rw [hSdef, ← map_inv]
          group
    _ = GeneralLinearGroup.scalar (Fin 3) (c * u⁻¹) *
        (GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) u⁻¹)⁻¹ * diagE ε) := by
          rw [hsc]
    _ = GeneralLinearGroup.scalar (Fin 3) (c * u⁻¹ * (Units.map (σ : K →* K) u⁻¹)⁻¹) *
        diagE ε := by
          rw [map_mul (GeneralLinearGroup.scalar (Fin 3)) (c * u⁻¹)]
          group

variable {ι : Type*} {α : ι → MulAut (projImage (slPi π 3 (p ^ f) K))}
  {e₀ : projImage (slPi π 3 (p ^ f) K)}

theorem exists_lift (e₀ : projImage (slPi π 3 (p ^ f) K)) :
    ∃ s₀ ∈ slPi π 3 (p ^ f) K, (e₀ : ProjGenLinGroup (Fin 3) K) = pmk s₀ := by
  obtain ⟨s₀, hs₀, h⟩ := e₀.2
  exact ⟨s₀, hs₀, h.symm⟩

theorem CentConfig.isBlockAct_of_diagE (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hc : CentConfig π p f K α e₀) {ε : Kˣ} (hε3 : (ε : K) ^ 3 = 1)
    (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagE ε)) (x : ι) :
    IsBlockAct π p f K ε (α x) := by
  rcases hc.dich x with ⟨y, -, hyx⟩ | ⟨f₀, hf, σ, hσ, g, -, hgx⟩
  · obtain ⟨c, hc'⟩ := exists_conj_eq_scalar_mul hyx (hc.fix x) he₀
    exact Or.inl ⟨y, commute_of_conj_diagE (hK.three_ne_zero hq) hε3 hc', hyx⟩
  · obtain ⟨s₀, hs₀, hs₀e⟩ := exists_lift e₀
    obtain ⟨c, hc'⟩ := exists_frob_conj_eq_scalar_mul hgx (hc.fix x) hs₀ hs₀e
    exact Or.inr ⟨σ, g, commute_diagE_of_frob hK hq hε3 (fieldAut_apply_eq hq hf hσ hε3)
      (hs₀e.symm.trans he₀) hc', hgx⟩

@[expose] def blockPair (n : ℕ) : rootsOfUnity n K →* rootsOfUnity n K × rootsOfUnity n K where
  toFun v := (v⁻¹ ^ 2, v)
  map_one' := by simp
  map_mul' v w := by
    ext
    · simp only [Prod.fst_mul]
      rw [mul_inv, mul_pow]
    · rfl

@[expose] noncomputable def blockTorusSub (hK : PiField π p f K) {n : ℕ}
    (hn : n ∣ qSubPi π (p ^ f)) : Subgroup (projImage (slPi π 3 (p ^ f) K)) :=
  ((torusHomM hK hn).comp (blockPair n)).range

theorem coe_blockPair_fst (n : ℕ) (v : rootsOfUnity n K) :
    (((blockPair n v).1 : rootsOfUnity n K) : Kˣ) = (v : Kˣ)⁻¹ ^ 2 := by
  change (((v⁻¹ ^ 2 : rootsOfUnity n K)) : Kˣ) = _
  rw [Subgroup.coe_pow, Subgroup.coe_inv]

theorem diagUnits_block_eq (v : Kˣ) :
    (diagUnits (v⁻¹ ^ 2) v (v⁻¹ ^ 2 * v)⁻¹ : GL (Fin 3) K) = diagUnits (v⁻¹ ^ 2) v v := by
  rw [show (v⁻¹ ^ 2 * v)⁻¹ = v by group]

theorem coe_blockTorus (hK : PiField π p f K) {n : ℕ} (hn : n ∣ qSubPi π (p ^ f))
    (v : rootsOfUnity n K) :
    (((torusHomM hK hn).comp (blockPair n)) v : ProjGenLinGroup (Fin 3) K) =
      pmk (diagUnits ((v : Kˣ)⁻¹ ^ 2) v v) := by
  rw [MonoidHom.comp_apply, coe_torusHomM, coe_blockPair_fst]
  exact congrArg pmk (diagUnits_block_eq (v : Kˣ))

theorem not_three_dvd_card_blockTorusSub (hK : PiField π p f K) {n : ℕ}
    (hn : n ∣ qSubPi π (p ^ f)) (hn1 : 1 < n) (hn3 : ¬ 3 ∣ n) :
    ¬ 3 ∣ Nat.card (blockTorusSub hK hn) := by
  have := hK.finite
  have : NeZero n := ⟨by omega⟩
  have hcard : Nat.card (rootsOfUnity n K) = n :=
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd (dvd_trans hn (qSubPi_dvd hK))
  intro h3
  apply hn3
  have h := Subgroup.card_range_dvd ((torusHomM hK hn).comp (blockPair n))
  rw [hcard] at h
  exact dvd_trans h3 h

theorem IsBlockAct.mapsTo_blockTorusSub (hK : PiField π p f K) {n : ℕ}
    (hn : n ∣ qSubPi π (p ^ f)) {ε : Kˣ} (hε : ε ≠ 1)
    {β : MulAut (projImage (slPi π 3 (p ^ f) K))} (hβ : IsBlockAct π p f K ε β) :
    ∀ w ∈ blockTorusSub hK hn, β w ∈ blockTorusSub hK hn := by
  rintro _ ⟨v, rfl⟩
  rcases hβ with ⟨y, hy, hβ⟩ | ⟨σ, g, hg, hβ⟩
  · refine ⟨v, Subtype.ext ?_⟩
    rw [hβ, coe_blockTorus, ← map_inv, ← map_mul, ← map_mul,
      commute_diagUnits_of_commute_diagE hε hy, mul_inv_cancel_right]
  · have hs := torusHom_mem_slPi hK (rootsOfUnity_le_of_dvd hn (blockPair n v).1.2)
      (rootsOfUnity_le_of_dvd hn (blockPair n v).2.2)
    have he : ((torusHomM hK hn).comp (blockPair n)) v =
        projOf _ ⟨torusHom (((blockPair n v).1 : Kˣ), ((blockPair n v).2 : Kˣ)), hs⟩ := rfl
    refine ⟨⟨Units.map (σ : K →* K) v, units_map_mem_rootsOfUnity σ v.2⟩, Subtype.ext ?_⟩
    have hT : torusHom (((blockPair n v).1 : Kˣ), ((blockPair n v).2 : Kˣ)) =
        (diagUnits ((v : Kˣ)⁻¹ ^ 2) v v : GL (Fin 3) K) := by
      rw [show torusHom (((blockPair n v).1 : Kˣ), ((blockPair n v).2 : Kˣ)) =
        diagUnits ((blockPair n v).1 : Kˣ) ((blockPair n v).2 : Kˣ)
          (((blockPair n v).1 : Kˣ) * ((blockPair n v).2 : Kˣ))⁻¹ from rfl, coe_blockPair_fst]
      exact diagUnits_block_eq (v : Kˣ)
    have hσv : Units.map (σ : K →* K) ((v : Kˣ)⁻¹ ^ 2) =
        (Units.map (σ : K →* K) (v : Kˣ))⁻¹ ^ 2 := by rw [map_pow, map_inv]
    rw [coe_blockTorus, he, hβ _ hs]
    simp only [hT]
    rw [frobGL_diagUnits, hσv, commute_diagUnits_of_commute_diagE hε hg, mul_inv_cancel_right]

theorem CentConfig.false_of_field_typeTwo (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h8 : ¬ (π = false ∧ p ^ f = 8)) (hc : CentConfig π p f K α e₀) {ε : Kˣ}
    (hε3 : (ε : K) ^ 3 = 1) (hε1 : ε ≠ 1)
    (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagE ε)) (x : ι)
    (hx : IsFieldAct π p f K (α x)) : False := by
  obtain ⟨f₀, hf, σ, hσ, g, -, hgx⟩ := hx
  have hp := hK.prime
  have hf₀ : 1 ≤ f₀ := by have := hK.one_le; omega
  have hq₀3 : p ^ f = (p ^ f₀) ^ 3 := by rw [← pow_mul, mul_comm, ← hf]
  have hq₀ : ModThree π (p ^ f₀) := modThree_of_cube (hq₀3 ▸ hq)
  have hq₀2 : 2 ≤ p ^ f₀ := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
  obtain ⟨n, hn1, hndvd, hn3, hns1, hns2⟩ : ∃ n, 1 < n ∧ n ∣ qSubPi π (p ^ f) ∧ ¬ 3 ∣ n ∧
      ¬ n ∣ piCard π (p ^ f₀) - 1 ∧ ¬ n ∣ piCard π (p ^ f₀) ^ 2 - 1 := by
    cases π
    · change p ^ f₀ % 3 = 2 at hq₀
      have h2 : 2 < p ^ f₀ := by
        rcases Nat.lt_or_ge 2 (p ^ f₀) with h | h
        · exact h
        · exfalso
          apply h8
          refine ⟨rfl, ?_⟩
          rw [hq₀3, show p ^ f₀ = 2 by omega]
          norm_num
      obtain ⟨n, hn1, hnd, hn3, h1, h2⟩ := exists_field_divisor_minus hq₀ h2
      refine ⟨n, hn1, ?_, hn3, h1, ?_⟩
      · change n ∣ p ^ f + 1
        rwa [hq₀3]
      · change ¬ n ∣ ((p ^ f₀) ^ 2) ^ 2 - 1
        rwa [← pow_mul]
    · change p ^ f₀ % 3 = 1 at hq₀
      obtain ⟨n, hn1, hnd, hn3, h1, h2⟩ := exists_field_divisor_plus hq₀ hq₀2
      refine ⟨n, hn1, ?_, hn3, h1, h2⟩
      change n ∣ p ^ f - 1
      rwa [hq₀3]
  obtain ⟨ρ, hρ, hρo⟩ := exists_orderOf_eq hK (by omega) hndvd
  obtain ⟨s₀, hs₀, hs₀e⟩ := exists_lift e₀
  obtain ⟨c, hc'⟩ := exists_frob_conj_eq_scalar_mul hgx (hc.fix x) hs₀ hs₀e
  have hg := commute_diagE_of_frob hK hq hε3 (fieldAut_apply_eq hq hf hσ hε3)
    (hs₀e.symm.trans he₀) hc'
  have hfixW := hc.hV _ (not_three_dvd_card_blockTorusSub hK hndvd hn1 hn3) fun y =>
    (hc.isBlockAct_of_diagE hK hq hε3 he₀ y).mapsTo_blockTorusSub hK hndvd hε1
  set v : rootsOfUnity n K := ⟨ρ, hρ⟩
  have hs := torusHom_mem_slPi hK (rootsOfUnity_le_of_dvd hndvd (blockPair n v).1.2)
    (rootsOfUnity_le_of_dvd hndvd (blockPair n v).2.2)
  have he : ((torusHomM hK hndvd).comp (blockPair n)) v =
      projOf _ ⟨torusHom (((blockPair n v).1 : Kˣ), ((blockPair n v).2 : Kˣ)), hs⟩ := rfl
  have hfix := congrArg Subtype.val (hfixW x _ ⟨v, rfl⟩)
  have hT : torusHom (((blockPair n v).1 : Kˣ), ((blockPair n v).2 : Kˣ)) =
      (diagUnits (ρ⁻¹ ^ 2) ρ ρ : GL (Fin 3) K) := by
    rw [show torusHom (((blockPair n v).1 : Kˣ), ((blockPair n v).2 : Kˣ)) =
      diagUnits ((blockPair n v).1 : Kˣ) ((blockPair n v).2 : Kˣ)
        (((blockPair n v).1 : Kˣ) * ((blockPair n v).2 : Kˣ))⁻¹ from rfl, coe_blockPair_fst]
    exact diagUnits_block_eq ρ
  rw [coe_blockTorus, he, hgx] at hfix
  simp only [hT] at hfix
  rw [frobGL_diagUnits, commute_diagUnits_of_commute_diagE hε1 hg, mul_inv_cancel_right] at hfix
  have hv : ((v : rootsOfUnity n K) : Kˣ) = ρ := rfl
  rw [hv] at hfix
  obtain ⟨u, h1, h2, -⟩ := (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mp hfix
  set σρ := Units.map (σ : K →* K) ρ with hσρ
  have hσinv : Units.map (σ : K →* K) (ρ⁻¹ ^ 2) = σρ⁻¹ ^ 2 := by rw [map_pow, map_inv]
  rw [hσinv] at h1
  have hu : u = ρ * σρ⁻¹ := by rw [← h2, mul_comm σρ u, mul_inv_cancel_right]
  rw [hu] at h1
  have hμ3 : (ρ * σρ⁻¹) ^ 3 = 1 := by
    have e1 : σρ⁻¹ ^ 2 * (ρ * σρ⁻¹) = ρ * σρ⁻¹ ^ 3 := by
      rw [mul_left_comm, ← pow_succ]
    rw [e1] at h1
    calc (ρ * σρ⁻¹) ^ 3 = ρ ^ 2 * (ρ * σρ⁻¹ ^ 3) := by rw [mul_pow, ← mul_assoc, ← pow_succ]
      _ = ρ ^ 2 * ρ⁻¹ ^ 2 := by rw [h1]
      _ = 1 := by rw [inv_pow, mul_inv_cancel]
  have hμn : (ρ * σρ⁻¹) ∈ rootsOfUnity n K :=
    mul_mem hρ (inv_mem (units_map_mem_rootsOfUnity σ hρ))
  have hμ1 : ρ * σρ⁻¹ = 1 := by
    have h3 : orderOf (ρ * σρ⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hμ3
    have hn' : orderOf (ρ * σρ⁻¹) ∣ n :=
      orderOf_dvd_of_pow_eq_one ((mem_rootsOfUnity _ _).mp hμn)
    have h31 : orderOf (ρ * σρ⁻¹) ∣ Nat.gcd 3 n := Nat.dvd_gcd h3 hn'
    have hcop : Nat.gcd 3 n = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn3
    rw [hcop] at h31
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h31)
  have hσρ' : σ (ρ : K) = ρ := by
    have : σρ = ρ := (mul_inv_eq_one.mp hμ1).symm
    exact congrArg Units.val this
  have hpos : 1 ≤ piCard π (p ^ f₀) := by
    cases π
    · exact Nat.one_le_pow _ _ (by omega)
    · change 1 ≤ p ^ f₀
      omega
  rcases hσ with hσ | hσ
  · rw [hσ] at hσρ'
    exact hns1 (hρo ▸ orderOf_dvd_of_pow_eq_self hpos hσρ')
  · rw [hσ] at hσρ'
    exact hns2 (hρo ▸ orderOf_dvd_of_pow_eq_self (Nat.one_le_pow _ _ (by omega)) hσρ')

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
