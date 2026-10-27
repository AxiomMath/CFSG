module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalSL
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderUO

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial

namespace NoOffPSLRest

section Expo

variable {F : Type} [Field F] {p : ℕ}

@[expose] noncomputable def expo (p : ℕ) (ζ z : Fˣ) : ZMod p :=
  open Classical in
  if h : ∃ a : ℕ, ζ ^ a = z then ((Classical.choose h : ℕ) : ZMod p) else 0

theorem expo_pow {ζ : Fˣ} (hord : orderOf ζ = p) (a : ℕ) : expo p ζ (ζ ^ a) = (a : ZMod p) := by
  have h : ∃ a' : ℕ, ζ ^ a' = ζ ^ a := ⟨a, rfl⟩
  rw [expo, dite_eq_left h]
  have hc := Classical.choose_spec h
  rw [pow_eq_pow_iff_modEq, hord] at hc
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc

theorem pow_val_expo [NeZero p] {ζ : Fˣ} (hord : orderOf ζ = p) {z : Fˣ}
    (hz : ∃ a : ℕ, ζ ^ a = z) : ζ ^ (expo p ζ z).val = z := by
  obtain ⟨a, rfl⟩ := hz
  rw [expo_pow hord, ZMod.val_natCast, pow_eq_pow_iff_modEq, hord]
  exact Nat.mod_modEq a p

theorem expo_mul {ζ : Fˣ} (hord : orderOf ζ = p) {z w : Fˣ} (hz : ∃ a : ℕ, ζ ^ a = z)
    (hw : ∃ a : ℕ, ζ ^ a = w) : expo p ζ (z * w) = expo p ζ z + expo p ζ w := by
  obtain ⟨a, rfl⟩ := hz
  obtain ⟨b, rfl⟩ := hw
  rw [← pow_add, expo_pow hord, expo_pow hord, expo_pow hord, Nat.cast_add]

theorem pow_val_add [NeZero p] {ζ : Fˣ} (hord : orderOf ζ = p) (x y : ZMod p) :
    ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
  rw [← pow_add, pow_eq_pow_iff_modEq, hord, ZMod.val_add]
  exact Nat.mod_modEq _ p

theorem exists_pow_eq [Fact p.Prime] {ζ : Fˣ} (hord : orderOf ζ = p) {z : Fˣ} (hz : z ^ p = 1) :
    ∃ a : ℕ, ζ ^ a = z := by
  have hprim : IsPrimitiveRoot (ζ : F) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hord)
  obtain ⟨a, -, ha⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (z : F))
    (by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one])
  exact ⟨a, Units.ext (by rw [Units.val_pow_eq_pow_val, ha])⟩

end Expo

section Proj

variable {G : Type} [Group G] {F : Type} [Field F] {m p : ℕ}

@[expose] noncomputable def projRep (p : ℕ) (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (b : G) : Fin (m + 1) → Fˣ :=
  open Classical in
  if h : ∃ d : Fin (m + 1) → Fˣ, (∀ i, d i ^ p = 1) ∧
      (b, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ then Classical.choose h else 1

theorem projRep_spec {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G} {b : G}
    (hb : b ∈ LinModel.rootTorus p ψ) :
    (∀ i, projRep p ψ b i ^ p = 1) ∧
      (b, InnerDiagA.diagGL (projRep p ψ b)) ∈ LinFusion.ggInducedPairs ψ := by
  have h : ∃ d : Fin (m + 1) → Fˣ, (∀ i, d i ^ p = 1) ∧
      (b, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ := hb
  rw [projRep, dite_eq_left h]
  exact Classical.choose_spec h

@[expose] noncomputable def projCoord (p : ℕ) (ζ : Fˣ)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G) (b : G) : Fin (m + 1) → ZMod p :=
  fun i => expo p ζ (projRep p ψ b i)

theorem exists_scalar_of_rep [CharP F 2] {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {b : G}
    {d d' : Fin (m + 1) → Fˣ} (hd : ∀ i, d i ^ p = 1) (hbd : (b, InnerDiagA.diagGL d) ∈
      LinFusion.ggInducedPairs ψ) (hd' : ∀ i, d' i ^ p = 1)
    (hbd' : (b, InnerDiagA.diagGL d') ∈ LinFusion.ggInducedPairs ψ) :
    ∃ c : Fˣ, c ^ p = 1 ∧ ∀ i, d' i = c * d i := by
  obtain ⟨c, hc⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker hbd hbd'
  have hent := NoOffenderClassical.SL.entry_of_diagGL_eq hc
  refine ⟨c, ?_, hent⟩
  have h1 := hd' 0
  rwa [hent 0, mul_pow, hd 0, mul_one] at h1

theorem projCoord_eq_add [CharP F 2] (hp : p.Prime)
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {ζ : Fˣ}
    (hord : orderOf ζ = p) {b : G} {d : Fin (m + 1) → Fˣ} (hd : ∀ i, d i ^ p = 1)
    (hbd : (b, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ) :
    ∃ c : ZMod p, ∀ i, projCoord p ζ ψ b i = expo p ζ (d i) + c := by
  have : Fact p.Prime := ⟨hp⟩
  have hb : b ∈ LinModel.rootTorus p ψ := ⟨d, hd, hbd⟩
  obtain ⟨hd₀, hbd₀⟩ := projRep_spec hb
  obtain ⟨c, hcp, hc⟩ := exists_scalar_of_rep hker hd hbd hd₀ hbd₀
  refine ⟨expo p ζ c, fun i => ?_⟩
  change expo p ζ (projRep p ψ b i) = _
  rw [hc i, expo_mul hord (exists_pow_eq hord hcp) (exists_pow_eq hord (hd i)), add_comm]

end Proj

section Props

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {F : Type} [Field F] [CharP F 2] {m p : ℕ}
  {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G} {ζ : Fˣ}

omit [CharP F 2] in
theorem projCoord_inj (hp : p.Prime) (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    (hord : orderOf ζ = p) {b b' : G} (hb : b ∈ LinModel.rootTorus p ψ)
    (hb' : b' ∈ LinModel.rootTorus p ψ)
    (h : ∃ c : ZMod p, ∀ i, projCoord p ζ ψ b i = projCoord p ζ ψ b' i + c) : b = b' := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨c, hc⟩ := h
  obtain ⟨hd, hbd⟩ := projRep_spec hb
  obtain ⟨hd', hbd'⟩ := projRep_spec hb'
  have hdi : projRep p ψ b = fun i => ζ ^ c.val * projRep p ψ b' i := by
    funext i
    have h1 := congrArg (fun z : ZMod p => ζ ^ z.val) (hc i)
    change ζ ^ (expo p ζ (projRep p ψ b i)).val = ζ ^ (expo p ζ (projRep p ψ b' i) + c).val at h1
    rw [pow_val_expo hord (exists_pow_eq hord (hd i)), pow_val_add hord,
      pow_val_expo hord (exists_pow_eq hord (hd' i)), mul_comm] at h1
    exact h1
  have h2 : (b', InnerDiagA.diagGL (projRep p ψ b)) ∈ LinFusion.ggInducedPairs ψ := by
    have h3 := LinModel.scalar_mul_mem_ggInducedPairs hbd' (ζ ^ c.val)
    rw [LinModel.scalar_mul_diagGL] at h3
    rw [hdi]
    exact h3
  have h4 := (LinFusion.ggInducedPairs ψ).mul_mem hbd ((LinFusion.ggInducedPairs ψ).inv_mem h2)
  rw [Prod.inv_mk, Prod.mk_mul_mk, mul_inv_cancel] at h4
  have h5 := LinFusion.mem_centralizer_of_mem_ggInducedPairs_one h4
  rw [hC, Subgroup.mem_bot, mul_inv_eq_one] at h5
  exact h5

theorem projCoord_surj (hp : p.Prime)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (hord : orderOf ζ = p) (v : Fin (m + 1) → ZMod p) (hv : ∑ i, v i = 0) :
    ∃ b ∈ LinModel.rootTorus p ψ, ∃ c : ZMod p, ∀ i, projCoord p ζ ψ b i = v i + c := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζp : ζ ^ p = 1 := by rw [← hord, pow_orderOf_eq_one]
  set d : Fin (m + 1) → Fˣ := fun i => ζ ^ (v i).val with hd
  have hdp : ∀ i, d i ^ p = 1 := fun i => by
    rw [hd, ← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  have hdvd : p ∣ ∑ i, (v i).val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    simpa only [ZMod.natCast_zmod_val] using hv
  have hdprod : ∏ i, d i = 1 := by
    rw [hd, Finset.prod_pow_eq_pow_sum]
    obtain ⟨t, ht⟩ := hdvd
    rw [ht, pow_mul, hζp, one_pow]
  have hmem := LinModel.exists_mem_of_prod_eq_one ψ d hdprod
  refine ⟨ψ (LinModel.diagSL d hdprod), ⟨d, hdp, hmem⟩, ?_⟩
  obtain ⟨c, hc⟩ := projCoord_eq_add hp hker hord hdp hmem
  refine ⟨c, fun i => ?_⟩
  rw [hc i, hd]
  simp only
  rw [expo_pow hord, ZMod.natCast_zmod_val]

theorem exists_projRep_of_semilinear [Finite F] (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) (hord : orderOf ζ = p) {Bs : Subgroup G}
    (hle : Bs ≤ LinModel.rootTorus p ψ) (hge : LinModel.rootTorus p ψ ≤ Bs) {y : G}
    (hyM : y ∈ Subgroup.normalizer (ψ.range : Set G))
    (hyB : y ∈ Subgroup.normalizer (Bs : Set G)) (hyp : y ^ p = 1) :
    ∃ (π : Equiv.Perm (Fin (m + 1))) (s : ZMod p), s ≠ 0 ∧ ∀ b ∈ Bs, ∃ c : ZMod p, ∀ i,
      projCoord p ζ ψ (y * b * y⁻¹) i = s * projCoord p ζ ψ b (π i) + c := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hconj : ∀ b ∈ Bs, y * b * y⁻¹ ∈ Bs := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp hyB b).mp hb
  obtain ⟨A, σ, hAσ⟩ := NoOffenderClassical.SL.exists_semilinear hm hp hp2 hker hC hyM hyp
  set σu : Fˣ →* Fˣ := Units.map (σ : F →* F) with hσu
  have hσu1 : ∀ x : Fˣ, σu x = 1 ↔ x = 1 := fun x => by
    constructor
    · intro h
      apply Units.ext
      have h1 := congrArg Units.val h
      rw [hσu, Units.coe_map, Units.val_one] at h1
      rw [Units.val_one]
      exact σ.injective (h1.trans (map_one σ).symm)
    · rintro rfl
      exact map_one σu
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hζp : ζ ^ p = 1 := by rw [← hord, pow_orderOf_eq_one]
  have hσζp : σu ζ ^ p = 1 := by rw [← map_pow, hζp, map_one]
  obtain ⟨s₀, hs₀⟩ := exists_pow_eq hord hσζp
  have hs0 : (s₀ : ZMod p) ≠ 0 := by
    intro h0
    obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff s₀ p).mp h0
    have h1 : σu ζ = 1 := by rw [← hs₀, ht, pow_mul, hζp, one_pow]
    exact hζ1 ((hσu1 ζ).mp h1)
  have hexpoσ : ∀ z : Fˣ, z ^ p = 1 → expo p ζ (σu z) = (s₀ : ZMod p) * expo p ζ z := by
    intro z hz
    obtain ⟨a, rfl⟩ := exists_pow_eq hord hz
    rw [map_pow, ← hs₀, ← pow_mul, expo_pow hord, expo_pow hord, Nat.cast_mul]
  set R := projRep p ψ with hR
  have hRb : ∀ b ∈ Bs, (∀ i, R b i ^ p = 1) ∧
      (b, InnerDiagA.diagGL (R b)) ∈ LinFusion.ggInducedPairs ψ := fun b hb =>
    projRep_spec (hle hb)
  have hmat : ∀ b ∈ Bs, ∃ c : Fˣ, A * InnerDiagA.diagGL (fun k => σu (R b k)) =
      InnerDiagA.diagGL (fun k => c * R (y * b * y⁻¹) k) * A := by
    intro b hb
    have h1 := NoOffenderClassical.SL.conj_mem_ggInducedPairs hAσ (hRb b hb).2
    obtain ⟨c, hc⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker h1
      (hRb _ (hconj b hb)).2
    refine ⟨c⁻¹, ?_⟩
    rw [← LinModel.scalar_mul_diagGL, hc, NoOffenderClassical.SL.map_diagGL, ← hσu]
    have hz : GeneralLinearGroup.scalar (Fin (m + 1)) c⁻¹ *
        GeneralLinearGroup.scalar (Fin (m + 1)) c = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    calc A * InnerDiagA.diagGL (fun k => σu (R b k)) =
        (GeneralLinearGroup.scalar (Fin (m + 1)) c⁻¹ * GeneralLinearGroup.scalar (Fin (m + 1)) c) *
          (A * InnerDiagA.diagGL (fun k => σu (R b k)) * A⁻¹) * A := by rw [hz]; group
      _ = _ := by group
  set δ : ↥Bs → Fin (m + 1) → F := fun b k => ((σu (R b k) : Fˣ) : F) with hδ
  have hsep : ∀ l l', l ≠ l' → ∃ b, δ b l ≠ δ b l' := by
    intro l l' hll'
    set t := NoOffenderClassical.twoPoint ζ l l' with ht
    have htp : ∀ k, t k ^ p = 1 := NoOffenderClassical.twoPoint_pow hζp l l'
    have htprod : ∏ k, t k = 1 := NoOffenderClassical.twoPoint_prod ζ hll'
    have hmem := LinModel.exists_mem_of_prod_eq_one ψ t htprod
    have hb : ψ (LinModel.diagSL t htprod) ∈ Bs := hge ⟨t, htp, hmem⟩
    refine ⟨⟨_, hb⟩, fun heq => ?_⟩
    obtain ⟨c, -, hc⟩ := exists_scalar_of_rep hker htp hmem (hRb _ hb).1 (hRb _ hb).2
    have h1 : σu (R (ψ (LinModel.diagSL t htprod)) l) =
        σu (R (ψ (LinModel.diagSL t htprod)) l') := Units.ext heq
    rw [hc l, hc l', map_mul, map_mul] at h1
    have h2 := mul_left_cancel h1
    have h3 : t l = t l' := by
      have h4 := (hσu1 (t l * (t l')⁻¹)).mp (by rw [map_mul, map_inv, h2, mul_inv_cancel])
      exact mul_inv_eq_one.mp h4
    simp only [ht, NoOffenderClassical.twoPoint, ite_true, Ne.symm hll', ite_false] at h3
    have h5 : ζ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [h3]
      exact mul_inv_cancel ζ
    have hg := pow_gcd_eq_one.mpr ⟨hζp, h5⟩
    rw [(Nat.coprime_primes hp Nat.prime_two).mpr hp2, pow_one] at hg
    exact hζ1 hg
  obtain ⟨ρ, hρ⟩ := NoOffenderClassical.exists_perm_of_separating A hsep fun b => by
    obtain ⟨c, hc⟩ := hmat b b.2
    refine ⟨fun k => ((c * R (y * b * y⁻¹) k : Fˣ) : F), ?_⟩
    have h1 := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL] at h1
    exact h1
  have hcoord : ∀ b ∈ Bs, ∃ c : Fˣ, ∀ k, c * R (y * b * y⁻¹) k = σu (R b (ρ k)) := by
    intro b hb
    obtain ⟨c, hc⟩ := hmat b hb
    refine ⟨c, fun k => ?_⟩
    have h1 := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL] at h1
    have h2 := hρ fun k => ((σu (R b k) : Fˣ) : F)
    rw [h1] at h2
    have h3 := congrArg (· * ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
      h2
    simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one] at h3
    have h4 := congrFun (congrFun h3 k) k
    rw [diagonal_apply_eq, diagonal_apply_eq] at h4
    exact Units.ext h4
  refine ⟨ρ, (s₀ : ZMod p), hs0, fun b hb => ?_⟩
  obtain ⟨c, hc⟩ := hcoord b hb
  have hcp : c ^ p = 1 := by
    have h2 : (c * R (y * b * y⁻¹) 0) ^ p = 1 := by
      rw [hc 0, ← map_pow, (hRb b hb).1, map_one]
    rwa [mul_pow, (hRb _ (hconj b hb)).1 0, mul_one] at h2
  refine ⟨-expo p ζ c, fun i => ?_⟩
  change expo p ζ (R (y * b * y⁻¹) i) = (s₀ : ZMod p) * expo p ζ (R b (ρ i)) + -expo p ζ c
  have h1 : expo p ζ (c * R (y * b * y⁻¹) i) = expo p ζ c + expo p ζ (R (y * b * y⁻¹) i) :=
    expo_mul hord (exists_pow_eq hord hcp) (exists_pow_eq hord ((hRb _ (hconj b hb)).1 i))
  rw [hc i, hexpoσ _ ((hRb b hb).1 (ρ i))] at h1
  rw [h1, add_comm (expo p ζ c)]
  exact (add_neg_cancel_right _ _).symm

end Props

end NoOffPSLRest

section Family

open NoOffPSLRest

theorem NoOffPSLRest.pslSplit_projFrame (G : Type) [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (n f : ℕ) (ψ : (ggU .PSL n f).K →* G)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSL n f).D .PSL n f ψ)
    (hC : Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥) (hpq : p ∣ 2 ^ f - 1) :
    ∃ (m : ℕ) (κ : G → (Fin m → ZMod p)), 4 ≤ m ∧
      (∀ b ∈ Bs, ∀ b' ∈ Bs, (∃ c : ZMod p, ∀ i, κ b i = κ b' i + c) → b = b') ∧
      (∀ v : Fin m → ZMod p, ∑ i, v i = 0 → ∃ b ∈ Bs, ∃ c : ZMod p, ∀ i, κ b i = v i + c) ∧
      ∀ g ∈ ggM p B x L D J, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 →
        ∃ (π : Equiv.Perm (Fin m)) (s : ZMod p), s ≠ 0 ∧
          ∀ b ∈ Bs, ∃ c : ZMod p, ∀ i, κ (g⁻¹ * b * g) i = s * κ b (π i) + c := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hctx.2.2.2.1.1.2.2.1; omega⟩
  have hm : 2 ≤ m := hctx.2.2.2.1.2
  have hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :=
    hctx.2.2.2.2.1.2
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hpp := hctx.prime
  have hp2 := hctx.ne_two
  have : NeZero p := ⟨hpp.ne_zero⟩
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]
    exact hC
  obtain ⟨A₀, hA₀⟩ := ggBstarToralPSLInput_holds G p B Bs x L D J m f ψ hctx hC hpq
  set ψ' := ψ.comp (InnerDiagA.conjSL A₀⁻¹) with hψ'
  have hker' := LinTorus.ker_comp_conjSL_le hker A₀⁻¹
  have hrange' : ψ'.range = ψ.range := LinTorus.range_comp_conjSL ψ A₀⁻¹
  have hC' : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by
    rw [hrange']
    exact hCψ
  have hBsD : ∀ b ∈ Bs, ∃ d : Fin (m + 1) → (GaloisField 2 f)ˣ,
      (b, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ' := by
    intro b hb
    obtain ⟨Ab, hAb⟩ := RootPlaneA.exists_gl_of_psiInnerDiag hm hker (hctx.2.2.2.2.2.2.1.2 b hb)
    obtain ⟨d, hd⟩ := LinTorus.exists_eq_diagGL fun i j hij => hA₀ b hb Ab hAb hij
    have h1 : (b⁻¹, Ab) ∈ LinFusion.ggInducedPairs ψ := fun u => by
      change b⁻¹ * ψ u * b⁻¹⁻¹ = _
      rw [inv_inv]
      exact hAb u
    have h2 := (LinFusion.ggInducedPairs ψ).inv_mem h1
    rw [Prod.inv_mk, inv_inv] at h2
    have h3 := LinModel.mem_ggInducedPairs_comp_conjSL_inv h2 A₀
    refine ⟨d⁻¹, ?_⟩
    rw [LinFusion.diagGL_inv, ← hd]
    convert h3 using 2
    group
  have hle : Bs ≤ LinModel.rootTorus p ψ' :=
    LinModel.le_rootTorus hker' hBsD hctx.bstar.2.1.2
  have hge : LinModel.rootTorus p ψ' ≤ Bs := LinModel.rootTorus_le hC' hBsD hctx.bstar.2.2.2
  have hpK : p ∣ Nat.card (GaloisField 2 f)ˣ := by
    rw [Nat.card_units, GaloisField.card 2 f (by omega)]
    exact hpq
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 f)ˣ) (hp := ⟨hpp⟩) p hpK
  set κ := projCoord p ζ ψ' with hκ
  have hinj : ∀ b ∈ Bs, ∀ b' ∈ Bs, (∃ c : ZMod p, ∀ i, κ b i = κ b' i + c) → b = b' :=
    fun b hb b' hb' h => projCoord_inj hpp hC' hζ (hle hb) (hle hb') h
  refine ⟨m + 1, κ, ?_, hinj, fun v hv => ?_, fun g hgM hgB hgp => ?_⟩
  ·
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
    have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1
    have hr4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
    have hcard : p ^ 4 ≤ Nat.card Bs :=
      calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hpp.pos hr4
        _ = Nat.card B := hBcard.symm
        _ ≤ Nat.card Bs := hBBs
    have hinj' : Function.Injective fun b : Bs => κ b := fun b b' h =>
      Subtype.ext (hinj b b.2 b' b'.2 ⟨0, fun i => by simpa using congrFun h i⟩)
    have h2 := Nat.card_le_card_of_injective _ hinj'
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h2
    exact (Nat.pow_le_pow_iff_right hpp.one_lt).mp (hcard.trans h2)
  · obtain ⟨b, hb, c, hc⟩ := projCoord_surj hpp hker' hζ v hv
    exact ⟨b, hge hb, c, hc⟩
  · have hyM : g⁻¹ ∈ Subgroup.normalizer (ψ'.range : Set G) := by
      rw [hrange', hctx.range_eq]
      exact Subgroup.inv_mem _ hgM
    have hyp : g⁻¹ ^ p = 1 := by rw [inv_pow, hgp, inv_one]
    obtain ⟨π, s, hs, hπ⟩ := exists_projRep_of_semilinear hm hpp hp2 hker' hC' hζ hle hge hyM
      (Subgroup.inv_mem _ hgB) hyp
    refine ⟨π, s, hs, fun b hb => ?_⟩
    obtain ⟨c, hc⟩ := hπ b hb
    refine ⟨c, fun i => ?_⟩
    have h := hc i
    rw [inv_inv] at h
    exact h

theorem ggSixBstarProjFrameOn_PSLSplit : GGSixBstarProjFrameOn GGPSLSplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq⟩ := hP
  exact NoOffPSLRest.pslSplit_projFrame G p B Bs x L D J n f ψ hctx hC hpq

theorem ggSixBstarNoOffenderOn_PSLSplitProj : GGSixBstarNoOffenderOn GGPSLSplit :=
  ggNoOffender_of_projFrameOn ggSixBstarProjFrameOn_PSLSplit

theorem ggSixBstarNoOffenderOn_PSLSplitDvd : GGSixBstarNoOffenderOn GGPSLSplitDvd :=
  fun G _ _ p B Bs x L D J t n f ψ hP hctx hC =>
    ggSixBstarNoOffenderOn_PSLSplitProj G p B Bs x L D J t n f ψ ⟨hP.1, hP.2.1⟩ hctx hC

end Family

end CFSG.StandardType
