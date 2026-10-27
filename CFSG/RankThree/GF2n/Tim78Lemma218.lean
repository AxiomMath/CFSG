module

public import CFSG.RankThree.GF2n.Tim78RankOne218
import CFSG.Timmesfeld.ARS.NaturalModule
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.RankThree.GF2n.Tim78Frattini
import CFSG.RankThree.GF2n.Tim78NaturalModule

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def InducesNaturalSL2 (n : ℕ) (H W : Subgroup G) : Prop :=
  ∃ (φ : H →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (ψ : W ≃* Multiplicative (Fin 2 → GaloisField 2 n)),
    Function.Surjective φ ∧ φ.ker = (Subgroup.centralizer (W : Set G)).subgroupOf H ∧
    ∀ (z : H) (w w' : W), (w' : G) = (z : G) * w * (z : G)⁻¹ →
      Multiplicative.toAdd (ψ w') =
        (φ z : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ Multiplicative.toAdd (ψ w)

theorem upperUnipotent_inf_lowerUnipotent (K : Type*) [Field K] :
    upperUnipotent K ⊓ lowerUnipotent K = ⊥ := by
  rw [eq_bot_iff]
  rintro m ⟨hu, hl⟩
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff K).mp hu
  obtain ⟨s, hs⟩ := (mem_lowerUnipotent_iff K).mp hl
  have h01 := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 2) K =>
    (m : Matrix (Fin 2) (Fin 2) K) 0 1) hs
  simp only [ARS.NaturalModule.coe_upperElt, ARS.NaturalModule.coe_lowerElt] at h01
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h01
  rw [Subgroup.mem_bot, h01, upperElt_zero]

theorem two_pow_eq_factorization {n : ℕ} (hn : n ≠ 0) :
    2 ^ n =
      2 ^ (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))).factorization 2 := by
  have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow hn
  have h2 : 1 < (2 ^ n) ^ 2 := by nlinarith
  have hodd : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := by
    have h4 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 hn) two_ne_zero
    omega
  rw [card_SL_two_galoisField hn, Nat.factorization_mul (by positivity) (by omega),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]

noncomputable def sylowUpper {n : ℕ} (hn : n ≠ 0) :
    Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard (upperUnipotent (GaloisField 2 n)) (by
    rw [card_upperUnipotent, GaloisField.card 2 n hn]
    exact two_pow_eq_factorization hn)

theorem coe_sylowUpper {n : ℕ} (hn : n ≠ 0) :
    ((sylowUpper hn : Sylow 2 _) : Subgroup _) = upperUnipotent (GaloisField 2 n) := by
  simp [sylowUpper]

noncomputable def sylowLower {n : ℕ} (hn : n ≠ 0) :
    Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard (lowerUnipotent (GaloisField 2 n)) (by
    rw [card_lowerUnipotent, GaloisField.card 2 n hn]
    exact two_pow_eq_factorization hn)

theorem coe_sylowLower {n : ℕ} (hn : n ≠ 0) :
    ((sylowLower hn : Sylow 2 _) : Subgroup _) = lowerUnipotent (GaloisField 2 n) := by
  simp [sylowLower]

variable [Finite G]

namespace Hyp218

variable {M V Q P W : Subgroup G} {g : G} (h : Hyp218 M V Q P W g)
include h

theorem le_conjSubgroup_Q {x : G} (hxW : x ∈ Subgroup.normalizer (W : Set G))
    (hxV : conjSubgroup x V = conjSubgroup g V) {y : G} (hy : IsOpp V P g y) :
    V ≤ conjSubgroup g Q := by
  have hx' : conjSubgroup x (conjSubgroup g V) ≠ conjSubgroup g V := by
    intro heq
    apply h.ne
    have e : conjSubgroup x (conjSubgroup g V) = conjSubgroup x V := by rw [heq, hxV]
    exact Subgroup.map_injective (MulAut.conj x).injective e
  have hcls : conjSubgroup x (conjSubgroup g V) ∈ classIn V W :=
    conj_mem_classIn hxW ⟨⟨g, rfl⟩, h.V1_le_W⟩
  obtain ⟨u, hu, hueq⟩ := h.exists_Pg_conj_eq hxW hxV hy hcls hx'
    ⟨⟨1, (conjSubgroup_one V).symm⟩, h.V_le_W⟩ (Ne.symm h.ne)
  have hnV : conjSubgroup (u * x) V = conjSubgroup g V := by
    rw [conjSubgroup_mul, hxV, conjSubgroup_eq_self_iff]
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    rw [h.Pg_comm hu ha, mul_inv_cancel_right]
    exact ha
  have hnV1 : conjSubgroup (u * x) (conjSubgroup g V) = V := by rw [conjSubgroup_mul, hueq]
  have hm : g⁻¹ * (u * x) ∈ M := by
    rw [← h.normalizer_eq, ← conjSubgroup_eq_self_iff, conjSubgroup_mul, hnV, ← conjSubgroup_mul,
      inv_mul_cancel, conjSubgroup_one]
  have hQ : conjSubgroup (u * x) Q = conjSubgroup g Q := by
    have e : conjSubgroup (u * x) Q = conjSubgroup g (conjSubgroup (g⁻¹ * (u * x)) Q) := by
      rw [← conjSubgroup_mul, mul_inv_cancel_left]
    rw [e, conjSubgroup_eq_self_iff.mpr (h.M_le_normalizer_Q hm)]
  rw [← hnV1, ← hQ]
  exact Subgroup.map_mono h.le

theorem exists_natural {x : G} (hxW : x ∈ Subgroup.normalizer (W : Set G))
    (hxV : conjSubgroup x V = conjSubgroup g V) {y : G} (hy : IsOpp V P g y)
    (hq : 4 ≤ Nat.card V) {H : Subgroup G} (hH : H = P ⊔ conjSubgroup g P) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card V = 2 ^ n ∧
      ∃ (φ : H →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
        (ψ : W ≃* Multiplicative (Fin 2 → GaloisField 2 n)),
        Function.Surjective φ ∧ φ.ker = (Subgroup.centralizer (W : Set G)).subgroupOf H ∧
        (∀ (z : H) (w w' : W), (w' : G) = (z : G) * w * (z : G)⁻¹ →
          Multiplicative.toAdd (ψ w') =
            (φ z : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ Multiplicative.toAdd (ψ w)) ∧
        (P.subgroupOf H).map φ = upperUnipotent (GaloisField 2 n) ∧
        ((conjSubgroup g P).subgroupOf H).map φ = lowerUnipotent (GaloisField 2 n) ∧
        IsPGroup 2 (H ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) ∧
        ∀ w : W, (w : G) ∈ V ↔ Multiplicative.toAdd (ψ w) 1 = 0 := by
  classical
  obtain ⟨n, hn2, hVn, φ, hφs, hφker, hφP, hφPg, hL2⟩ := h.exists_rankOne hxW hxV hy hq hH
  set K := GaloisField 2 n with hK
  have hPH : P ≤ H := hH ▸ le_sup_left
  have hHW : H ≤ Subgroup.normalizer (W : Set G) :=
    hH ▸ sup_le h.P_le_normalizer_W (h.Pg_le_normalizer_W hxW hxV)
  let ρ : H →* MulAut W := W.normalizerMonoidHom.comp (Subgroup.inclusion hHW)
  have hρ : ∀ (z : H) (w : W), ((ρ z w : W) : G) = (z : G) * w * (z : G)⁻¹ := fun _ _ => rfl
  have hker : φ.ker ≤ ρ.ker := by
    intro z hz
    rw [hφker, Subgroup.mem_subgroupOf] at hz
    rw [MonoidHom.mem_ker]
    ext w
    rw [hρ, MulAut.one_apply, (Subgroup.mem_centralizer_iff.mp hz w w.2).symm,
      mul_inv_cancel_right]
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφs
  let ρ' : Matrix.SpecialLinearGroup (Fin 2) K →* MulAut W :=
    (QuotientGroup.lift φ.ker ρ hker).comp e.symm.toMonoidHom
  have hρ' : ∀ z : H, ρ' (φ z) = ρ z := by
    intro z
    have h1 : e.symm (φ z) = (z : H ⧸ φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift φ.ker ρ hker (e.symm (φ z)) = ρ z
    rw [h1]
    rfl
  have : IsMulCommutative W := h.W_elemAb.1
  let _ : CommGroup W := IsMulCommutative.instCommGroup
  let _ : DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) (Additive W) :=
    { smul := fun m v => Additive.ofMul (ρ' m (Additive.toMul v))
      one_smul := fun v => by
        show Additive.ofMul (ρ' 1 (Additive.toMul v)) = v
        rw [map_one, MulAut.one_apply, ofMul_toMul]
      mul_smul := fun m m' v => by
        show Additive.ofMul (ρ' (m * m') (Additive.toMul v)) =
          Additive.ofMul (ρ' m (Additive.toMul (Additive.ofMul (ρ' m' (Additive.toMul v)))))
        rw [map_mul, MulAut.mul_apply, toMul_ofMul]
      smul_zero := fun m => by
        show Additive.ofMul (ρ' m (Additive.toMul 0)) = 0
        rw [toMul_zero, map_one, ofMul_one]
      smul_add := fun m v v' => by
        show Additive.ofMul (ρ' m (Additive.toMul (v + v'))) =
          Additive.ofMul (ρ' m (Additive.toMul v)) + Additive.ofMul (ρ' m (Additive.toMul v'))
        rw [toMul_add, map_mul, ofMul_mul] }
  let ι : Additive W → G := fun v => ((Additive.toMul v : W) : G)
  have hι_inj : Function.Injective ι := fun a b hab =>
    Additive.toMul.injective (Subtype.ext hab)
  have hι_zero : ι 0 = 1 := rfl
  have hι_sub : ∀ a b : Additive W, ι (a - b) = ι a * (ι b)⁻¹ := by
    intro a b
    show ((Additive.toMul a / Additive.toMul b : W) : G) = _
    rw [Subgroup.coe_div, div_eq_mul_inv]
  have hsmul : ∀ (z : H) (v : Additive W), ι (φ z • v) = (z : G) * ι v * (z : G)⁻¹ := by
    intro z v
    show ((ρ' (φ z) (Additive.toMul v) : W) : G) = _
    rw [hρ']
    rfl
  have hmemW : ∀ v : Additive W, ι v ∈ W := fun v => (Additive.toMul v).2
  obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (h.conj_ne_bot y)
  have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  have hbP : b ∈ P := hy.le hb
  have hbW : b ∉ Subgroup.centralizer (W : Set G) := fun hbW => hb1' (hy.cent b hb fun a ha =>
    (Subgroup.mem_centralizer_iff.mp hbW a (h.V1_le_W ha)).symm)
  have hfixV : ∀ w ∈ W, (b * w = w * b) → w ∈ V := fun w hw hbw =>
    h.mem_of_commute hy hbP hbW hw hbw
  have hfix : ∀ v : Additive W, (∀ m : Matrix.SpecialLinearGroup (Fin 2) K, m • v = v) →
      v = 0 := by
    intro v hv
    have hfixz : ∀ z : H, (z : G) * ι v = ι v * z := by
      intro z
      have := congrArg ι (hv (φ z))
      rw [hsmul] at this
      calc (z : G) * ι v = ((z : G) * ι v * (z : G)⁻¹) * z := by group
        _ = ι v * z := by rw [this]
    have hvV : ι v ∈ V := hfixV _ (hmemW v) (hfixz ⟨b, hPH hbP⟩)
    have hu : x * b * x⁻¹ ∈ conjSubgroup g P := by
      rw [← h.conjSubgroup_P_eq hxV, mem_conjSubgroup, show x⁻¹ * (x * b * x⁻¹) * x = b by group]
      exact hbP
    have hcomm := hfixz ⟨x * b * x⁻¹, hH ▸ le_sup_right (a := P) hu⟩
    have hx'W : x⁻¹ * ι v * x ∈ W := by
      have := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hxW) (hmemW v)
      rwa [inv_inv] at this
    have h1 : x⁻¹ * ι v * x ∈ V := hfixV _ hx'W (by
      calc b * (x⁻¹ * ι v * x) = x⁻¹ * ((x * b * x⁻¹) * ι v) * x := by group
        _ = x⁻¹ * (ι v * (x * b * x⁻¹)) * x := by rw [hcomm]
        _ = x⁻¹ * ι v * x * b := by group)
    have hvV1 : ι v ∈ conjSubgroup g V := by
      rw [← hxV, mem_conjSubgroup]
      exact h1
    have : ι v ∈ V ⊓ conjSubgroup g V := ⟨hvV, hvV1⟩
    rw [h.inf_V1, Subgroup.mem_bot] at this
    exact hι_inj (this.trans hι_zero.symm)
  have hupper : ∀ a ∈ upperUnipotent K, ∃ p : H, (p : G) ∈ P ∧ φ p = a := by
    intro a ha
    rw [← hφP] at ha
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp ha
    exact ⟨p, Subgroup.mem_subgroupOf.mp hp, rfl⟩
  have hquad : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : Additive W,
      a' • (a • v - v) = a • v - v := by
    intro a ha a' ha' v
    obtain ⟨p, hp, rfl⟩ := hupper a ha
    obtain ⟨p', hp', rfl⟩ := hupper a' ha'
    apply hι_inj
    rw [hsmul, hι_sub, hsmul]
    have hc : (p : G) * ι v * (p : G)⁻¹ * (ι v)⁻¹ ∈ V := by
      have := h.commutator_mem hp (h.W_le_P (hmemW v))
      rwa [commutatorElement_def] at this
    rw [h.central hp' hc, mul_inv_cancel_right]
  obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.V_ne_bot
  have hv₀1' : v₀ ≠ 1 := fun h1 => hv₀1 (Subtype.ext h1)
  let w₀ : Additive W := Additive.ofMul ⟨v₀, h.V_le_W hv₀⟩
  have hw : ∀ a ∈ upperUnipotent K, a • w₀ = w₀ := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := hupper a ha
    apply hι_inj
    rw [hsmul]
    show (p : G) * v₀ * (p : G)⁻¹ = v₀
    rw [h.central hp hv₀, mul_inv_cancel_right]
  have hw0 : w₀ ≠ 0 := fun h0 => hv₀1' (congrArg ι h0)
  obtain ⟨θ, hθinj, -, -, hθ⟩ := ARS.exists_natural_of_quadratic hfix hquad hw hw0
  have hθbij : Function.Bijective θ := by
    refine hθinj.bijective_of_nat_card_le ?_
    have h1 : Nat.card (Additive W) = Nat.card W := rfl
    rw [h1, h.card_W, Nat.card_fun, Nat.card_fin, GaloisField.card 2 n (by omega), ← hVn]
    exact (sq _).symm.le
  let θe : (Fin 2 → K) ≃+ Additive W := AddEquiv.ofBijective θ hθbij
  let ψ : W ≃* Multiplicative (Fin 2 → K) :=
    { toFun := fun w => Multiplicative.ofAdd (θe.symm (Additive.ofMul w))
      invFun := fun u => Additive.toMul (θe (Multiplicative.toAdd u))
      left_inv := fun w => by simp
      right_inv := fun u => by simp
      map_mul' := fun w w' => by
        show Multiplicative.ofAdd (θe.symm (Additive.ofMul (w * w'))) =
          Multiplicative.ofAdd (θe.symm (Additive.ofMul w)) *
            Multiplicative.ofAdd (θe.symm (Additive.ofMul w'))
        rw [ofMul_mul, map_add, ofAdd_add] }
  have hψ : ∀ w : W, θ (Multiplicative.toAdd (ψ w)) = Additive.ofMul w := fun w =>
    θe.apply_symm_apply _
  have hcompat : ∀ (z : H) (w w' : W), (w' : G) = (z : G) * w * (z : G)⁻¹ →
      Multiplicative.toAdd (ψ w') =
        (φ z : Matrix (Fin 2) (Fin 2) K) *ᵥ Multiplicative.toAdd (ψ w) := by
    intro z w w' hww'
    apply hθinj
    rw [hθ, hψ, hψ]
    apply hι_inj
    rw [hsmul]
    exact hww'
  refine ⟨n, hn2, hVn, φ, ψ, hφs, hφker, hcompat, hφP, hφPg, hL2, fun w => ?_⟩
  constructor
  · intro hwV
    refine (ARS.NaturalModule.forall_upperElt_mulVec_eq_iff _).mp fun t => ?_
    obtain ⟨p, hp, hpt⟩ := hupper _ ((mem_upperUnipotent_iff K).mpr ⟨t, rfl⟩)
    rw [← hpt, ← hcompat p w w (by rw [h.central hp hwV, mul_inv_cancel_right])]
  · intro hw1
    have hfixed := (ARS.NaturalModule.forall_upperElt_mulVec_eq_iff _).mpr hw1
    have hbu : φ ⟨b, hPH hbP⟩ ∈ upperUnipotent K := by
      rw [← hφP]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbP)
    obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff K).mp hbu
    have hbw : b * w * b⁻¹ ∈ W := conj_mem_of_mem_normalizer (h.P_le_normalizer_W hbP) w.2
    have h1 := hcompat ⟨b, hPH hbP⟩ w ⟨_, hbw⟩ rfl
    rw [ht, hfixed t] at h1
    have h2 : (⟨_, hbw⟩ : W) = w := ψ.injective (Multiplicative.toAdd.injective h1)
    have h3 : b * w * b⁻¹ = w := congrArg Subtype.val h2
    exact hfixV _ w.2 (by
      calc b * (w : G) = b * w * b⁻¹ * b := by group
        _ = w * b := by rw [h3])

end Hyp218

noncomputable def diagHom (K : Type*) [Field K] : Kˣ →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun := ARS.NaturalModule.diagElt
  map_one' := ARS.NaturalModule.diagElt_one
  map_mul' a b := (ARS.NaturalModule.diagElt_mul_diagElt a b).symm

theorem diagHom_injective (K : Type*) [Field K] : Function.Injective (diagHom K) := by
  intro a b hab
  have h00 := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 2) K =>
    (m : Matrix (Fin 2) (Fin 2) K) 0 0) hab
  simp only [diagHom, MonoidHom.coe_mk, OneHom.coe_mk, ARS.NaturalModule.coe_diagElt,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one] at h00
  exact Units.ext h00

namespace Hyp218

variable {M V Q P W : Subgroup G} {g : G} (h : Hyp218 M V Q P W g)
include h

theorem conclusions (hq : 4 ≤ Nat.card V) {H : Subgroup G} (hH : H = P ⊔ conjSubgroup g P) :
    V ≤ conjSubgroup g Q ∧
    (∀ w ∈ W, w ≠ 1 → ∃! U, U ∈ classIn V W ∧ w ∈ U) ∧
    (∃ n : ℕ, Nat.card V = 2 ^ n ∧ InducesNaturalSL2 n H W) ∧
    P = Q ∧ inSubgroup frattini Q = V ∧ Q ⊓ Subgroup.centralizer (Q : Set G) = V ∧
    ⁅Q, Q⁆ = V ∧ H ⊓ Subgroup.centralizer (W : Set G) = inSubgroup (pCore 2) H ∧
    ∃ k ∈ M ⊓ H, orderOf k = Nat.card V - 1 ∧
      ∀ i : ℕ, 0 < i → i < Nat.card V - 1 → ∀ v ∈ V, k ^ i * v = v * k ^ i → v = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := h.exists_isOpp
  obtain ⟨x, hxW, hxV⟩ := h.exists_conj_eq_V1 hy
  obtain ⟨n, hn2, hVn, φ, ψ, hφs, hφker, hcompat, hφP, hφPg, hL2, hVψ⟩ :=
    h.exists_natural hxW hxV hy hq hH
  set K := GaloisField 2 n with hK
  have hn0 : n ≠ 0 := by omega
  have hPH : P ≤ H := hH ▸ le_sup_left
  have hHW : H ≤ Subgroup.normalizer (W : Set G) :=
    hH ▸ sup_le h.P_le_normalizer_W (h.Pg_le_normalizer_W hxW hxV)
  have hψV : ∀ v : W, (v : G) ∈ V →
      Multiplicative.toAdd (ψ v) = ![Multiplicative.toAdd (ψ v) 0, 0] := by
    intro v hv
    funext i
    fin_cases i
    · rfl
    · exact (hVψ v).mp hv
  have hψ0 : ∀ v : W, Multiplicative.toAdd (ψ v) = 0 → (v : G) = 1 := by
    intro v hv
    have : ψ v = 1 := Multiplicative.toAdd.injective (by rw [hv]; rfl)
    rw [map_eq_one_iff _ ψ.injective] at this
    rw [this]
    rfl
  have htorus : ∀ c : Kˣ, ∃ z : H, φ z = ARS.NaturalModule.diagElt c ∧ (z : G) ∈ M ∧
      ∀ v : W, (v : G) ∈ V → ∀ w : W, (w : G) = z * v * (z : G)⁻¹ →
        Multiplicative.toAdd (ψ w) 0 = (c : K) * Multiplicative.toAdd (ψ v) 0 := by
    intro c
    obtain ⟨z, hz⟩ := hφs (ARS.NaturalModule.diagElt c)
    have hcoord : ∀ v : W, (v : G) ∈ V → ∀ w : W, (w : G) = z * v * (z : G)⁻¹ →
        Multiplicative.toAdd (ψ w) = ![(c : K) * Multiplicative.toAdd (ψ v) 0, 0] := by
      intro v hv w hw
      rw [hcompat z v w hw, hz, ARS.NaturalModule.diagElt_mulVec, (hVψ v).mp hv, mul_zero]
    refine ⟨z, hz, ?_, fun v hv w hw => by rw [hcoord v hv w hw]; rfl⟩
    rw [← h.normalizer_eq]
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    have hw : (z : G) * v * (z : G)⁻¹ ∈ W := conj_mem_of_mem_normalizer (hHW z.2) (h.V_le_W hv)
    have := hcoord ⟨v, h.V_le_W hv⟩ hv ⟨_, hw⟩ rfl
    exact (hVψ ⟨_, hw⟩).mpr (by rw [this]; rfl)
  have heqV : ∀ U : Subgroup G, U ≤ V → M ≤ Subgroup.normalizer (U : Set G) → U ≠ ⊥ → U = V := by
    intro U hUV hMU hU
    refine le_antisymm hUV fun v hv => ?_
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU
    have hu1' : u ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
    set u' : W := ⟨u, h.V_le_W (hUV hu)⟩
    set v' : W := ⟨v, h.V_le_W hv⟩
    set s₀ := Multiplicative.toAdd (ψ u') 0 with hs₀
    set s := Multiplicative.toAdd (ψ v') 0 with hs
    have hs₀0 : s₀ ≠ 0 := by
      intro h0
      apply hu1'
      refine hψ0 u' ?_
      rw [hψV u' (hUV hu), ← hs₀, h0]
      funext i
      fin_cases i <;> rfl
    by_cases hs0 : s = 0
    · have : (v : G) = 1 := by
        refine hψ0 v' ?_
        rw [hψV v' hv, ← hs, hs0]
        funext i
        fin_cases i <;> rfl
      rw [this]
      exact U.one_mem
    set c : Kˣ := Units.mk0 (s / s₀) (div_ne_zero hs0 hs₀0)
    obtain ⟨z, -, hzM, hzc⟩ := htorus c
    have hw : (z : G) * u * (z : G)⁻¹ ∈ W :=
      conj_mem_of_mem_normalizer (hHW z.2) (h.V_le_W (hUV hu))
    have hzu : (z : G) * u * (z : G)⁻¹ ∈ U := conj_mem_of_mem_normalizer (hMU hzM) hu
    have hzuV : (z : G) * u * (z : G)⁻¹ ∈ V := hUV hzu
    have h1 := hzc u' (hUV hu) ⟨_, hw⟩ rfl
    have heq : (⟨_, hw⟩ : W) = v' := by
      apply ψ.injective
      apply Multiplicative.toAdd.injective
      rw [hψV ⟨_, hw⟩ hzuV, hψV v' hv, h1]
      congr 2
      rw [← hs₀, ← hs]
      simp only [c, Units.val_mk0]
      exact div_mul_cancel₀ s hs₀0
    have : (z : G) * u * (z : G)⁻¹ = v := congrArg Subtype.val heq
    rw [← this]
    exact hzu
  have hVQ : V ≤ Subgroup.centralizer (Q : Set G) := by
    have hU : V ⊓ Subgroup.centralizer (Q : Set G) ≠ ⊥ := by
      obtain ⟨d, hdV, hd1, hdc⟩ := exists_mem_not_mem_commutator_mem (p := 2) (P := Q)
        (B := ⊥) (N := V) h.isPGroup_Q (bot_lt_iff_ne_bot.mpr h.V_ne_bot) h.V_le_Q
        (by rw [Subgroup.normalizer_eq_top]; exact le_top)
        (h.Q_le_M.trans h.M_le_normalizer)
      intro hbot
      apply hd1
      have : d ∈ V ⊓ Subgroup.centralizer (Q : Set G) := ⟨hdV, mem_centralizer_of_forall
        fun q hq => by
          have := hdc q hq
          rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this⟩
      rw [hbot] at this
      exact this
    have := heqV _ inf_le_left (fun m hm => mem_normalizer_inf (h.M_le_normalizer hm)
      (mem_normalizer_centralizer (h.M_le_normalizer_Q hm))) hU
    rw [← this]
    exact inf_le_right
  have hPQ : P = Q := by
    refine le_antisymm h.P_le_Q fun q hq => ?_
    rw [h.hP]
    exact ⟨hq, mem_centralizer_of_forall fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (hVQ hv) q hq)⟩
  have hQnc : ¬ ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro hc
    have hQc : IsMulCommutative Q :=
      ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
    have hQV : Q ≤ V := h.maxAb.le_of_ge ⟨h.Q_le_M, h.M_le_normalizer_Q, hQc⟩ h.V_le_Q
    exact h.ne (Subgroup.eq_of_le_of_card_ge (h.le.trans hQV) (by rw [card_conjSubgroup]))
  have hPQ' : P = inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (V : Set G) := h.hP'
  have hΦ : inSubgroup frattini Q = V := by
    refine heqV _ (hPQ ▸ h.frattini_P_le) (fun m hm =>
      mem_normalizer_inSubgroup_frattini (h.M_le_normalizer_Q hm)) fun hbot => hQnc ?_
    intro a ha b hb
    have := commutatorElement_mem_inSubgroup_frattini h.isPGroup_Q ha hb
    rwa [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  have hQ' : ⁅Q, Q⁆ = V := by
    refine heqV _ ((Subgroup.commutator_le).mpr fun a ha b hb =>
      h.commutator_mem (hPQ ▸ ha) (hPQ ▸ hb)) (fun m hm => ?_) fun hbot => hQnc ?_
    · rw [← conjSubgroup_eq_self_iff]
      have hQm : conjSubgroup m Q = Q := conjSubgroup_eq_self_iff.mpr (h.M_le_normalizer_Q hm)
      calc conjSubgroup m ⁅Q, Q⁆ = ⁅conjSubgroup m Q, conjSubgroup m Q⁆ :=
            Subgroup.map_commutator _ _ _
        _ = ⁅Q, Q⁆ := by rw [hQm]
    · intro a ha b hb
      have := Subgroup.commutator_mem_commutator ha hb
      rwa [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  have hLO : H ⊓ Subgroup.centralizer (W : Set G) = inSubgroup (pCore 2) H := by
    obtain ⟨hO2, hOH, hHO⟩ := inSubgroup_pCore_two H
    refine le_antisymm (le_inSubgroup_pCore inf_le_left (fun z hz =>
      mem_normalizer_inf (Subgroup.le_normalizer hz) (mem_normalizer_centralizer (hHW hz)))
      hL2) fun z hz => ?_
    have hn : ((inSubgroup (pCore 2) H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mpr hHO
    have hNn : (((inSubgroup (pCore 2) H).subgroupOf H).map φ).Normal := hn.map _ hφs
    have hN2 : IsPGroup 2 (((inSubgroup (pCore 2) H).subgroupOf H).map φ) :=
      (hO2.of_equiv (Subgroup.subgroupOfEquivOfLe hOH).symm).map _
    have hleU := hN2.le_sylow_of_normal (sylowUpper hn0)
    have hleL := hN2.le_sylow_of_normal (sylowLower hn0)
    rw [coe_sylowUpper] at hleU
    rw [coe_sylowLower] at hleL
    have hmem : φ ⟨z, hOH hz⟩ ∈ upperUnipotent K ⊓ lowerUnipotent K := by
      have : φ ⟨z, hOH hz⟩ ∈ ((inSubgroup (pCore 2) H).subgroupOf H).map φ :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hz)
      exact ⟨hleU this, hleL this⟩
    rw [upperUnipotent_inf_lowerUnipotent, Subgroup.mem_bot, ← MonoidHom.mem_ker, hφker,
      Subgroup.mem_subgroupOf] at hmem
    exact ⟨hOH hz, hmem⟩
  have hcartan : ∃ k ∈ M ⊓ H, orderOf k = Nat.card V - 1 ∧
      ∀ i : ℕ, 0 < i → i < Nat.card V - 1 → ∀ v ∈ V, k ^ i * v = v * k ^ i → v = 1 := by
    have hKcard : Nat.card Kˣ = Nat.card V - 1 := by
      rw [Nat.card_units, GaloisField.card 2 n hn0, hVn]
    obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
    rw [hKcard] at hc
    obtain ⟨z, hz, hzM, -⟩ := htorus c
    have hdiag : orderOf (φ z) = Nat.card V - 1 := by
      rw [hz, show ARS.NaturalModule.diagElt c = diagHom K c from rfl,
        orderOf_injective _ (diagHom_injective K), hc]
    have hdvd : Nat.card V - 1 ∣ orderOf z := hdiag ▸ orderOf_map_dvd φ z
    have hzq : z ^ (Nat.card V - 1) ∈ (Subgroup.centralizer (W : Set G)).subgroupOf H := by
      rw [← hφker, MonoidHom.mem_ker, map_pow, ← hdiag, pow_orderOf_eq_one]
    obtain ⟨j, hj⟩ := hL2 ⟨((z ^ (Nat.card V - 1) : H) : G),
      ⟨(z ^ (Nat.card V - 1)).2, Subgroup.mem_subgroupOf.mp hzq⟩⟩
    have hj' : z ^ ((Nat.card V - 1) * 2 ^ j) = 1 := by
      rw [pow_mul]
      apply Subtype.ext
      have := congrArg Subtype.val hj
      simpa using this
    have hdvd2 : orderOf z ∣ (Nat.card V - 1) * 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
    obtain ⟨d, hd⟩ := hdvd
    have hq1 : 0 < Nat.card V - 1 := by omega
    have hd2 : d ∣ 2 ^ j := by
      rw [hd] at hdvd2
      exact (Nat.mul_dvd_mul_iff_left hq1).mp hdvd2
    obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    set k : H := z ^ 2 ^ a with hkdef
    have hk : orderOf k = Nat.card V - 1 := by
      rw [hkdef, orderOf_pow' z (by positivity), hd, Nat.gcd_mul_left_left,
        Nat.mul_div_cancel _ (by positivity)]
    have hcop : Nat.Coprime (2 ^ a) (Nat.card V - 1) := by
      refine Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ?_)
      rw [hVn]
      exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, hn0⟩) odd_one
    refine ⟨(k : G), ⟨?_, k.2⟩, by rw [Subgroup.orderOf_coe]; exact hk,
      fun i hi0 hiq v hv hkv => ?_⟩
    · rw [hkdef, Subgroup.coe_pow]
      exact M.pow_mem hzM _
    ·
      set v' : W := ⟨v, h.V_le_W hv⟩
      have hw : ((k ^ i : H) : G) * v * ((k ^ i : H) : G)⁻¹ = v := by
        rw [Subgroup.coe_pow, hkv, mul_inv_cancel_right]
      have h1 := hcompat (k ^ i) v' v' hw.symm
      rw [map_pow, hkdef, map_pow, hz, ← pow_mul, show ARS.NaturalModule.diagElt c =
        diagHom K c from rfl, ← map_pow, show diagHom K (c ^ (2 ^ a * i)) =
        ARS.NaturalModule.diagElt (c ^ (2 ^ a * i)) from rfl, ARS.NaturalModule.diagElt_mulVec,
        (hVψ v').mp hv] at h1
      have h2 := congrFun h1 0
      simp only [Matrix.cons_val_zero] at h2
      have hne : ((c ^ (2 ^ a * i) : Kˣ) : K) ≠ 1 := by
        intro h1'
        have hu : c ^ (2 ^ a * i) = 1 := Units.ext h1'
        have := orderOf_dvd_of_pow_eq_one hu
        rw [hc] at this
        have := (hcop.symm.dvd_of_dvd_mul_left this)
        exact absurd (Nat.le_of_dvd hi0 this) (by omega)
      have hs : Multiplicative.toAdd (ψ v') 0 = 0 := by
        have h3 : (((c ^ (2 ^ a * i) : Kˣ) : K) - 1) * Multiplicative.toAdd (ψ v') 0 = 0 := by
          rw [sub_mul, one_mul, ← h2, sub_self]
        rcases mul_eq_zero.mp h3 with h4 | h4
        · exact absurd (sub_eq_zero.mp h4) hne
        · exact h4
      refine hψ0 v' ?_
      rw [hψV v' hv, hs]
      funext i
      fin_cases i <;> rfl
  have hhP : P = inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (V : Set G) := hPQ'
  refine ⟨h.le_conjSubgroup_Q hxW hxV hy, fun w hw hw1 => h.partition hy hw hw1,
    ⟨n, hVn, φ, ψ, hφs, hφker, hcompat⟩, hPQ, hΦ, ?_, hQ', hLO, hcartan⟩
  rw [← hPQ]
  exact h.V_eq_center.symm

end Hyp218

theorem tim78_2_18 {M V Q P W H : Subgroup G} {g : G} (hM : IsMaximalTwoLocal M)
    (hF : generalizedFitting M = pCore 2 M)
    (hVmax : Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
      IsMulCommutative U) V)
    (hV2 : ∀ x ∈ V, x ^ 2 = 1) (hTI : IsTI V) (hQ : Q = inSubgroup (pCore 2) M)
    (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q) (hq : 4 ≤ Nat.card V)
    (hP : P = Q ⊓ Subgroup.centralizer (V : Set G)) (hW : W = V ⊔ conjSubgroup g V)
    (hH : H = P ⊔ conjSubgroup g P) :
    V ≤ conjSubgroup g Q ∧
    ((∀ w ∈ W, w ≠ 1 → ∃! U, U ∈ classIn V W ∧ w ∈ U) ∧
      ∃ n : ℕ, Nat.card V = 2 ^ n ∧ InducesNaturalSL2 n H W) ∧
    (P = Q ∧ inSubgroup frattini Q = V ∧ Q ⊓ Subgroup.centralizer (Q : Set G) = V ∧
      ⁅Q, Q⁆ = V ∧ H ⊓ Subgroup.centralizer (W : Set G) = inSubgroup (pCore 2) H) := by
  have h : Hyp218 M V Q P W g := ⟨hM, hF, hVmax, hV2, hTI, hgV, hgQ, hQ, hP, hW⟩
  obtain ⟨ha, hb₁, hb₂, hc₁, hc₂, hc₃, hc₄, hc₅, -⟩ := h.conclusions hq hH
  exact ⟨ha, ⟨hb₁, hb₂⟩, hc₁, hc₂, hc₃, hc₄, hc₅⟩

theorem tim78_2_18_cartan {M V Q P : Subgroup G} {g : G} (hM : IsMaximalTwoLocal M)
    (hF : generalizedFitting M = pCore 2 M)
    (hVmax : Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
      IsMulCommutative U) V)
    (hV2 : ∀ x ∈ V, x ^ 2 = 1) (hTI : IsTI V) (hQ : Q = inSubgroup (pCore 2) M)
    (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q) (hq : 4 ≤ Nat.card V)
    (hP : P = Q ⊓ Subgroup.centralizer (V : Set G)) :
    ∃ k ∈ M ⊓ (P ⊔ conjSubgroup g P), orderOf k = Nat.card V - 1 ∧
      ∀ i : ℕ, 0 < i → i < Nat.card V - 1 → ∀ v ∈ V, k ^ i * v = v * k ^ i → v = 1 := by
  have h : Hyp218 M V Q P (V ⊔ conjSubgroup g V) g := ⟨hM, hF, hVmax, hV2, hTI, hgV, hgQ, hQ,
    hP, rfl⟩
  exact (h.conclusions hq rfl).2.2.2.2.2.2.2.2

theorem cartan_element_of_isMaximalAbelian {M B : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hF : generalizedFitting M = pCore 2 M)
    (hBmax : Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
      IsMulCommutative U) B)
    (hB2 : ∀ x ∈ B, x ^ 2 = 1) (hTI : IsTI B) (hq : 4 ≤ Nat.card B) {g : G}
    (hgQ : conjSubgroup g B ≤ inSubgroup (pCore 2) M) (hgB : conjSubgroup g B ≠ B) :
    Subgroup.normalizer (B : Set G) = M ∧
      ∃ k ∈ M, orderOf k = Nat.card B - 1 ∧ ∀ b ∈ B, k * b * k⁻¹ = b → b = 1 := by
  have h : Hyp218 M B (inSubgroup (pCore 2) M)
      (inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (B : Set G)) (B ⊔ conjSubgroup g B) g :=
    ⟨hM, hF, hBmax, hB2, hTI, hgB, hgQ, rfl, rfl, rfl⟩
  obtain ⟨k, hk, hko, hkreg⟩ := (h.conclusions hq rfl).2.2.2.2.2.2.2.2
  refine ⟨h.normalizer_eq, k, hk.1, hko, fun b hb hkb => hkreg 1 one_pos (by omega) b hb ?_⟩
  rw [pow_one]
  calc k * b = k * b * k⁻¹ * k := by group
    _ = b * k := by rw [hkb]

end CFSG.RankThree.GF2n.Tim78
