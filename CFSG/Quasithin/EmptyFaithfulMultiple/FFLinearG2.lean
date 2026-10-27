module

public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearNat
public import CFSG.Quasithin.Background.P3G2Iso
public import CFSG.Quasithin.Background.B4ModelsIso

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.FFL

open Matrix CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Assembly.LowTwoRank
open CFSG.Open (quasithinG2 quasithinZorn)

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def cayleyEquivG2 (K : Type) [Field K] [CharP K 2] :
    ↥(cayleyGroup K) ≃* ↥(quasithinG2 K) :=
  MulEquiv.subgroupCongr G11.P3G2.quasithinG2_eq_cayleyGroup.symm

@[expose] noncomputable def g2A₁ (K : Type) [Field K] : SL3 K :=
  SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 2) (by decide) 1

@[expose] noncomputable def g2A₃ (K : Type) [Field K] : SL3 K :=
  SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 2) (by decide) 1 *
    SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1) (by decide) 1

@[expose] noncomputable def g2u (K : Type) [Field K] [CharP K 2] : ↥(quasithinG2 K) :=
  cayleyEquivG2 K (g2Y ![0, 1, 0] * g2A (g2A₁ K))

@[expose] noncomputable def g2γ (K : Type) [Field K] [CharP K 2] : ↥(quasithinG2 K) :=
  cayleyEquivG2 K (g2A (g2A₃ K))

abbrev g2E (g : ↥(quasithinG2 K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K := g

theorem g2u_zmk (r a b c d e f s : K) :
    g2E (g2u K) (zmk r a b c d e f s) =
      zmk (r + (b + c)) (a + (e + f)) (b + c) (c + d) d (e + (r + s + (b + c))) (e + f)
        (s + (b + c)) := by
  change ybFun ![0, 1, 0] (gAFun ((g2A₁ K : SL3 K) : Matrix (Fin 3) (Fin 3) K)
    (zmk r a b c d e f s)) = _
  have hneg : ∀ x : K, -x = x := CharTwo.neg_eq
  rw [gAFun_zmk, ybFun_zmk]
  apply zmk_congr <;>
    simp [g2A₁, Matrix.SpecialLinearGroup.transvection, Matrix.transvection,
      Matrix.adjugate_fin_three, sub_eq_add_neg, hneg]

theorem g2u_pow_four_zmk (r a b c d e f s : K) :
    g2E (g2u K) (g2E (g2u K) (g2E (g2u K) (g2E (g2u K) (zmk r a b c d e f s)))) =
      zmk r (a + c) b c d e (f + d) s := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [g2u_zmk]
  apply zmk_congr
  · linear_combination (2 * b + 5 * c + 5 * d) * h2
  · linear_combination (5 * r + 10 * b + 13 * c + 4 * d + 5 * e + 2 * f + 5 * s) * h2
  · linear_combination (2 * c + 3 * d) * h2
  · linear_combination (2 * d) * h2
  · ring
  · linear_combination (2 * r + 8 * b + 15 * c + 10 * d + 2 * s) * h2
  · linear_combination (3 * r + 7 * b + 10 * c + 3 * d + 2 * e + 3 * s) * h2
  · linear_combination (2 * b + 5 * c + 5 * d) * h2

theorem g2u_pow_eight : g2u K ^ 8 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have key : ∀ x, g2E (g2u K) (g2E (g2u K) (g2E (g2u K) (g2E (g2u K) (g2E (g2u K)
      (g2E (g2u K) (g2E (g2u K) (g2E (g2u K) x))))))) = x := by
    intro x
    rw [zorn_eta x, g2u_pow_four_zmk, g2u_pow_four_zmk]
    apply zmk_congr <;> first | rfl | linear_combination x.2.1 2 * h2 |
      linear_combination x.2.2.1 0 * h2
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have h8 : ((g2u K ^ 8 : ↥(quasithinG2 K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K) x =
      (⇑(g2E (g2u K)))^[8] x := by
    rw [Subgroup.coe_pow, LinearEquiv.coe_pow]
  rw [h8]
  show _ = x
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
    Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
    Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_zero_apply]
  exact key x

theorem isPGroup_zpowers_g2u : IsPGroup 2 ↥(Subgroup.zpowers (g2u K)) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨3, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
    show ((2 ^ 3 : ℕ) : ℤ) = ((8 : ℕ) : ℤ) from rfl, zpow_natCast, g2u_pow_eight,
    _root_.one_zpow]

omit [CharP K 2] in
theorem g2A₃_coe : ((g2A₃ K : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
    slMat (slGamma (K := K) (a := (1 : Fin 3)) (b := 2) (by decide)) := rfl

theorem g2γ_zmk (r a s : K) : g2E (g2γ K) (zmk r a 0 0 0 0 0 s) = zmk r a 0 0 0 0 0 s := by
  change gAFun ((g2A₃ K : SL3 K) : Matrix (Fin 3) (Fin 3) K) (zmk r a 0 0 0 0 0 s) = _
  have h : ((g2A₃ K : SL3 K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![a, 0, 0] = ![a, 0, 0] := by
    rw [g2A₃_coe]
    exact slGamma_mulVec_of _ rfl rfl
  have h0 : (adjugate ((g2A₃ K : SL3 K) : Matrix (Fin 3) (Fin 3) K))ᵀ *ᵥ ![(0 : K), 0, 0] =
      ![0, 0, 0] := by
    have hz : (![(0 : K), 0, 0] : Fin 3 → K) = 0 := by
      funext i
      fin_cases i <;> rfl
    rw [hz, mulVec_zero]
  unfold gAFun zmk
  exact Prod.ext rfl (Prod.ext h (Prod.ext h0 rfl))

omit [CharP K 2] in
theorem g2A₃_eq : specialLinearGroupEquivStatedSL 3 K (g2A₃ K) =
    slGamma (K := K) (a := (1 : Fin 3)) (b := 2) (by decide) := by
  rw [g2A₃, map_mul]
  rfl

theorem g2γ_pow_three : g2γ K ^ 3 = 1 := by
  have h : g2A₃ K ^ 3 = 1 := by
    apply (specialLinearGroupEquivStatedSL 3 K).injective
    rw [map_pow, g2A₃_eq, map_one]
    exact slGamma_pow_three _
  rw [g2γ, ← map_pow, ← map_pow, h, map_one, map_one]

theorem fixesFixed_g2 :
    FixesFixed (FFModel.zornQ (quasithinG2 K)) (Subgroup.zpowers (g2u K)) (g2γ K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  intro m hm0 hm
  obtain ⟨x, rfl⟩ : ∃ x : quasithinZorn K, Multiplicative.ofAdd x = m := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ := hm _ (Subgroup.mem_zpowers (g2u K))
  have htr : x.1 + x.2.2.2 = 0 := hm0
  have ht2 : g2E (g2u K) x = x + (t, 0, 0, t) := by
    have h0 : g2E (g2u K) x + -x = (t, 0, 0, t) := ht
    rw [← h0]
    abel
  rw [zorn_eta x, g2u_zmk] at ht2
  have ha := congrArg (fun y : quasithinZorn K => y.2.1 0) ht2
  have hb := congrArg (fun y : quasithinZorn K => y.2.1 1) ht2
  have hc := congrArg (fun y : quasithinZorn K => y.2.1 2) ht2
  have he := congrArg (fun y : quasithinZorn K => y.2.2.1 1) ht2
  have hf := congrArg (fun y : quasithinZorn K => y.2.2.1 2) ht2
  simp only [zmk, Prod.snd_add, Prod.fst_add, Pi.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply,
    add_zero] at ha hb hc he hf
  have hx2 : x.2.1 2 = 0 := by linear_combination hb
  have hy0 : x.2.2.1 0 = 0 := by linear_combination hc
  have hy1 : x.2.2.1 1 = 0 := by linear_combination hf
  have hy2 : x.2.2.1 2 = 0 := by linear_combination ha - hy1
  have hx1 : x.2.1 1 = 0 := by linear_combination he - htr - hx2
  refine ⟨0, ?_⟩
  change g2E (g2γ K) x + -x = (0, 0, 0, 0)
  have hx : x = zmk x.1 (x.2.1 0) 0 0 0 0 0 x.2.2.2 := by
    conv_lhs => rw [zorn_eta x]
    rw [hx1, hx2, hy0, hy1, hy2]
  rw [hx, g2γ_zmk, add_neg_cancel]
  rfl

theorem g2γ_moves : ∃ m ∈ (FFModel.zornQ (quasithinG2 K)).sec,
    (FFModel.zornQ (quasithinG2 K)).act (g2γ K) m * m⁻¹ ∉ (FFModel.zornQ (quasithinG2 K)).ker := by
  refine ⟨Multiplicative.ofAdd (zmk (0 : K) 0 1 0 0 0 0 0), show (0 : K) + 0 = 0 from add_zero 0,
    ?_⟩
  rintro ⟨t, ht⟩
  have h1 : gAFun ((g2A₃ K : SL3 K) : Matrix (Fin 3) (Fin 3) K) (zmk 0 0 1 0 0 0 0 0) +
      -zmk 0 0 1 0 0 0 0 0 = (t, 0, 0, t) := ht
  have h2 := congrArg (fun y : quasithinZorn K => y.2.1 2) h1
  have hA : ((g2A₃ K : SL3 K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0] = ![0, 0, 1] := by
    rw [g2A₃_coe]
    funext k
    fin_cases k
    · exact slGamma_mulVec_other _ _ (by decide) (by decide)
    · exact slGamma_mulVec_fst _ _
    · exact (slGamma_mulVec_snd _ _).trans (by simp)
  simp [gAFun, zmk, hA] at h2

theorem zornQ_faithful {Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)}
    (hΓ : Γ ≤ quasithinG2 K) : (FFModel.zornQ Γ).Faithful := by
  intro (γ : ↥Γ) hγ
  have hmem : (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈ cayleyGroup K := by
    rw [← G11.P3G2.quasithinG2_eq_cayleyGroup]
    exact hΓ γ.2
  set g : ↥(cayleyGroup K) := ⟨(γ : quasithinZorn K ≃ₗ[K] quasithinZorn K), hmem⟩ with hg
  have hmove : ∀ w : quasithinZorn K, w.1 + w.2.2.2 = 0 →
      ∃ c : K, cgE g w = w + c • cayleyOne K := by
    intro w hw
    obtain ⟨c, hc⟩ := hγ (Multiplicative.ofAdd w) hw
    refine ⟨c, ?_⟩
    have hc' : cgE g w + -w = (c, 0, 0, c) := hc
    have hc1 : c • cayleyOne K = ((c, 0, 0, c) : quasithinZorn K) := by simp [cayleyOne]
    rw [hc1, ← hc']
    abel
  have hfix : ∀ w : quasithinZorn K, w.1 = 0 → w.2.2.2 = 0 → cayleyNorm w = 0 →
      (∀ c : K, cayleyNorm (w + c • cayleyOne K) = c * c) → cgE g w = w := by
    intro w h1 h2 hN0 hN
    obtain ⟨c, hc⟩ := hmove w (by rw [h1, h2, add_zero])
    have hn := cg_norm g w
    rw [hc, hN, hN0] at hn
    have hc0 : c = 0 := mul_self_eq_zero.mp hn
    rw [hc, hc0, zero_smul, add_zero]
  have hb : ∀ (u₀ u₁ u₂ v₀ v₁ v₂ : K), u₀ * v₀ + u₁ * v₁ + u₂ * v₂ = 0 →
      cgE g (zmk 0 u₀ u₁ u₂ v₀ v₁ v₂ 0) = zmk 0 u₀ u₁ u₂ v₀ v₁ v₂ 0 := by
    intro u₀ u₁ u₂ v₀ v₁ v₂ huv
    refine hfix _ rfl rfl (by rw [cayleyNorm_zmk, huv]; ring) fun c => ?_
    rw [cayleyOne_eq, zmk_smul, zmk_add, cayleyNorm_zmk]
    linear_combination huv
  have hU0 := hb 1 0 0 0 0 0 (by ring)
  have hU1 := hb 0 1 0 0 0 0 (by ring)
  have hU2 := hb 0 0 1 0 0 0 (by ring)
  have hV0 := hb 0 0 0 1 0 0 (by ring)
  have hV1 := hb 0 0 0 0 1 0 (by ring)
  have hV2 := hb 0 0 0 0 0 1 (by ring)
  have hE : cgE g (zmk 1 0 0 0 0 0 0 0) = zmk 1 0 0 0 0 0 0 0 := by
    have hprod : cayleyMul (zmk (0 : K) 1 0 0 0 0 0 0) (zmk 0 0 0 0 1 0 0 0) =
        zmk 1 0 0 0 0 0 0 0 := by
      rw [cayleyMul_zmk]
      apply zmk_congr <;> ring
    rw [← hprod, cg_mul, hU0, hV0]
  have hE' : cgE g (zmk 0 0 0 0 0 0 0 1) = zmk 0 0 0 0 0 0 0 1 := by
    have hsplit : zmk (0 : K) 0 0 0 0 0 0 1 = cayleyOne K - zmk 1 0 0 0 0 0 0 0 := by
      rw [cayleyOne_eq, eq_sub_iff_add_eq, zmk_add]
      apply zmk_congr <;> ring
    rw [hsplit, map_sub, cg_one, hE]
  have hid : (cgE g : quasithinZorn K →ₗ[K] quasithinZorn K) = LinearMap.id :=
    zorn_linearMap_ext hE hU0 hU1 hU2 hV0 hV1 hV2 hE'
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun hid x

theorem card_commutator_quasithinG2
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card ↥⁅quasithinG2 F, quasithinG2 F⁆ = 6048 := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF', pow_one])
  let ε : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two hF').symm
  have hc : ⁅quasithinG2 F, quasithinG2 F⁆ = ⁅cayleyGroup F, cayleyGroup F⁆ := by
    rw [G11.P3G2.quasithinG2_eq_cayleyGroup]
  let f2 : ↥⁅quasithinG2 F, quasithinG2 F⁆ ≃* ↥⁅cayleyGroup F, cayleyGroup F⁆ :=
    MulEquiv.subgroupCongr hc
  let f3 : ↥⁅cayleyGroup F, cayleyGroup F⁆ ≃* ↥subG2 :=
    ((zornConj ε).subgroupMap _).trans
      (MulEquiv.subgroupCongr ((map_cayley_commutator ε).trans g2Two_commutator_eq))
  rw [Nat.card_congr (f2.trans f3).toEquiv, Nat.card_congr G11.P3G2.subG2EquivSU.toEquiv,
    LinearGroups.UnitaryThreeOverNine.card_statedSU G2U.card_F9]

end CFSG.Quasithin.EmptyFaithfulMultiple.FFL
