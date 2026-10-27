module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourSix
public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.StandardType.SpFour

open Module Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCSpIsotypic
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.TwoThree CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedSp)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem mem_spPull_of_sq (hK : Nat.card K = 2) {x b : StatedSp m K} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (blocks : SpPrimaryBlocks 2 1 3 x (proj m K x)) (hbx : b * x = x * b)
    (hb2 : b * b = 1) (hfix : ∀ u ∈ LinearMap.ker (spEnd x - 1), spEnd b u = u) :
    b ∈ spPull x (SpFin.h3 K) := by
  classical
  have hcb : spLin m K b ∈ gl_centralizer (spLin m K x) :=
    mem_gl_centralizer.mpr (spEnd_comm_iff.mp hbx)
  set c : gl_centralizer (spLin m K x) := ⟨spLin m K b, hcb⟩ with hc
  have hc2 : c * c = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, ← map_mul, hb2, map_one]
    rfl)
  haveI : Fact (Irreducible (SpFin.h3 K)) := ⟨SpFin.h3_irreducible hK⟩
  haveI : Module.Finite K (AdjoinRoot (SpFin.h3 K)) :=
    (AdjoinRoot.powerBasis SpFin.h3_monic.ne_zero).finite
  haveI : Finite (AdjoinRoot (SpFin.h3 K)) := Module.finite_of_finite K
  set d := blockDetHom (spLin m K x) (SpFin.h3 K) c with hd
  have hd2 : d * d = 1 := by rw [hd, ← map_mul, hc2, map_one]
  have hd3 : d ^ 3 = 1 := by
    have h1 : d ^ Nat.card (AdjoinRoot (SpFin.h3 K))ˣ = 1 := pow_card_eq_one'
    rwa [Nat.card_units, SpFin.card_adjoinRoot_h3 hK] at h1
  have hd1 : d = 1 := by
    calc d = d ^ 3 * (d * d)⁻¹ := by group
      _ = 1 := by rw [hd3, hd2]; simp
  have hx3v : x ^ 3 = 1 := hx3
  show spLin m K b ∈ specialBlock (spForm m K) (spLin m K x) (SpFin.h3 K)
  rw [mem_specialBlock]
  refine ⟨?_, hcb, hd1⟩
  rw [orbitFactor_spForm, SpFin.h3_reciprocal, Set.pair_eq_singleton]
  refine ⟨mem_unitaryCentralizer.mpr ⟨spLin_mem _, mem_gl_centralizer.mp hcb⟩, ?_⟩
  intro k hk hkn v hv
  by_cases hk1 : k = Polynomial.X - 1
  · subst hk1
    exact hfix v (blocks.fixed_eq ▸ hv)
  · have hbot := SpFin.primaryComponent_eq_bot_of_ne hK hx3 hx1 blocks hk hk1
      (fun h => hkn (h ▸ Set.mem_singleton _))
    rw [hbot, Submodule.mem_bot] at hv
    rw [hv, map_zero]

section Unip

theorem spTransvection_comm_of_orth {a b : Fin m ⊕ Fin m → K} (hba : spForm m K b a = 0) :
    spTransvection a (1 : K) * spTransvection b 1 = spTransvection b 1 * spTransvection a 1 := by
  have h := CFSG.RankThree.PartOne.CTP.spTransvection_conj (spTransvection a (1 : K)) b 1
  rw [spEnd_spTransvection, hba, mul_zero, zero_smul, add_zero] at h
  exact mul_inv_eq_iff_eq_mul.mp h

@[expose] noncomputable def uElem (x : StatedSp m K) (v : Fin m ⊕ Fin m → K) : StatedSp m K :=
  spTransvection v 1 * spTransvection (spEnd x v) 1 * spTransvection (spEnd x (spEnd x v)) 1

variable {T : Submodule K (Fin m ⊕ Fin m → K)}

theorem uElem_mem_gammaT (hT : ∀ u ∈ T, ∀ v ∈ T, spForm m K u v = 0) {x : StatedSp m K}
    (hTx : ∀ t ∈ T, spEnd x t ∈ T) {v : Fin m ⊕ Fin m → K} (hv : v ∈ T) :
    uElem x v ∈ gammaT T :=
  mul_mem (mul_mem (spTransvection_mem_gammaT hT hv 1)
    (spTransvection_mem_gammaT hT (hTx v hv) 1))
    (spTransvection_mem_gammaT hT (hTx _ (hTx v hv)) 1)

theorem uElem_comm (hT : ∀ u ∈ T, ∀ v ∈ T, spForm m K u v = 0) {x : StatedSp m K}
    (hx3 : x ^ 3 = 1) (hTx : ∀ t ∈ T, spEnd x t ∈ T) {v : Fin m ⊕ Fin m → K} (hv : v ∈ T) :
    uElem x v * x = x * uElem x v := by
  have hx3' : spEnd x ^ 3 = 1 := spEnd_pow hx3
  have h0 : spEnd x (spEnd x (spEnd x v)) = v := by
    have := congrArg (fun f : Module.End K (Fin m ⊕ Fin m → K) => f v) hx3'
    simpa [pow_succ, Module.End.mul_apply] using this
  have hv1 : spEnd x v ∈ T := hTx v hv
  have hv2 : spEnd x (spEnd x v) ∈ T := hTx _ hv1
  have c01 : spTransvection v (1 : K) * spTransvection (spEnd x v) 1 =
      spTransvection (spEnd x v) 1 * spTransvection v 1 :=
    spTransvection_comm_of_orth (hT _ hv1 _ hv)
  have c02 : spTransvection v (1 : K) * spTransvection (spEnd x (spEnd x v)) 1 =
      spTransvection (spEnd x (spEnd x v)) 1 * spTransvection v 1 :=
    spTransvection_comm_of_orth (hT _ hv2 _ hv)
  have e1 : x * uElem x v * x⁻¹ = (x * spTransvection v 1 * x⁻¹) *
      (x * spTransvection (spEnd x v) 1 * x⁻¹) *
      (x * spTransvection (spEnd x (spEnd x v)) 1 * x⁻¹) := by
    unfold uElem
    group
  have hconj : x * uElem x v * x⁻¹ = uElem x v := by
    rw [e1, CFSG.RankThree.PartOne.CTP.spTransvection_conj,
      CFSG.RankThree.PartOne.CTP.spTransvection_conj,
      CFSG.RankThree.PartOne.CTP.spTransvection_conj, h0]
    unfold uElem
    calc spTransvection (spEnd x v) (1 : K) * spTransvection (spEnd x (spEnd x v)) 1 *
          spTransvection v 1
        = spTransvection (spEnd x v) 1 * (spTransvection (spEnd x (spEnd x v)) 1 *
          spTransvection v 1) := mul_assoc _ _ _
      _ = spTransvection (spEnd x v) 1 * (spTransvection v 1 *
          spTransvection (spEnd x (spEnd x v)) 1) := by rw [c02]
      _ = (spTransvection (spEnd x v) 1 * spTransvection v 1) *
          spTransvection (spEnd x (spEnd x v)) 1 := (mul_assoc _ _ _).symm
      _ = (spTransvection v 1 * spTransvection (spEnd x v) 1) *
          spTransvection (spEnd x (spEnd x v)) 1 := by rw [c01]
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

theorem spEnd_three_transvections {a b c : Fin m ⊕ Fin m → K} (hab : spForm m K a b = 0)
    (hac : spForm m K a c = 0) (hbc : spForm m K b c = 0) (w : Fin m ⊕ Fin m → K) :
    spEnd (spTransvection a (1 : K) * spTransvection b 1 * spTransvection c 1) w =
      w + spForm m K w a • a + spForm m K w b • b + spForm m K w c • c := by
  have hba : spForm m K b a = 0 := (spForm_comm' b a).trans hab
  have hca : spForm m K c a = 0 := (spForm_comm' c a).trans hac
  have hcb : spForm m K c b = 0 := (spForm_comm' c b).trans hbc
  simp only [spEnd_mul, Module.End.mul_apply, spEnd_spTransvection, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, one_mul, hba, hca, hcb, mul_zero,
    zero_smul, add_zero]

theorem uElem_ne_one (hK : Nat.card K = 2) (hT : ∀ u ∈ T, ∀ v ∈ T, spForm m K u v = 0)
    {x : StatedSp m K} (hx3 : x ^ 3 = 1) (hfp : ∀ u, spEnd x u = u → u = 0)
    (hTx : ∀ t ∈ T, spEnd x t ∈ T) {v : Fin m ⊕ Fin m → K} (hv : v ∈ T) (hv0 : v ≠ 0) :
    uElem x v ≠ 1 := by
  intro h1
  have hv1 : spEnd x v ∈ T := hTx v hv
  have hv2 : spEnd x (spEnd x v) ∈ T := hTx _ hv1
  have hb0 : spEnd x v ≠ 0 := fun h => hv0 (spEnd_injective' x (h.trans (map_zero _).symm))
  have hx3' : spEnd x ^ 3 = 1 := spEnd_pow hx3
  have hsum : v + spEnd x v + spEnd x (spEnd x v) = 0 := by
    have h2 := sum_apply_eq_zero hx3' (U := ⊤) (fun _ _ => trivial) (fun u _ hu => hfp u hu)
      (w := v) trivial
    simpa [LinearMap.add_apply, sq, Module.End.mul_apply] using h2
  have h2 : (v + spEnd x v) + (v + spEnd x v) = 0 := SpFin.add_self_eq_zero_mod K _
  have hc : spEnd x (spEnd x v) = v + spEnd x v := by
    have h3 : spEnd x (spEnd x v) = -(v + spEnd x v) := eq_neg_of_add_eq_zero_right hsum
    rw [h3]
    exact neg_eq_of_add_eq_zero_right h2
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, spForm m K w₀ (spEnd x v) ≠ 0 := by
    by_contra h
    push Not at h
    exact hb0 ((spForm_nondegenerate (r := m) (K := K)).2 _ h)
  have hev := spEnd_three_transvections (a := v) (b := spEnd x v) (c := spEnd x (spEnd x v))
    (hT _ hv _ hv1) (hT _ hv _ hv2) (hT _ hv1 _ hv2) w₀
  change spEnd (uElem x v) w₀ = _ at hev
  rw [h1, spEnd_one, Module.End.one_apply] at hev
  set α := spForm m K w₀ v with hα
  set β := spForm m K w₀ (spEnd x v) with hβ
  have hγ : spForm m K w₀ (spEnd x (spEnd x v)) = α + β := by
    rw [hc, map_add]
  rw [hγ, hc] at hev
  have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hrel : β • v + α • spEnd x v = 0 := by
    have h4 : α • v + β • spEnd x v + (α + β) • (v + spEnd x v) = 0 := by
      have := hev
      simpa [add_assoc] using this
    have key : β • v + α • spEnd x v = (α • v + β • spEnd x v + (α + β) • (v + spEnd x v)) -
        (2 : K) • (α • v + β • spEnd x v) := by module
    rw [key, h4, h2K, zero_smul, sub_zero]
  have hβ1 : β = 1 :=
    (eq_zero_or_eq_one_of_card hK β).resolve_left hw₀
  rw [hβ1, one_smul] at hrel
  rcases eq_zero_or_eq_one_of_card hK α with hα0 | hα1
  · rw [hα0, zero_smul, add_zero] at hrel
    exact hv0 hrel
  · rw [hα1, one_smul] at hrel
    have h5 : spEnd x v = v := by
      have h6 : spEnd x v = -v := eq_neg_of_add_eq_zero_right hrel
      rw [h6]
      exact neg_eq_of_add_eq_zero_right (SpFin.add_self_eq_zero_mod K v)
    exact hv0 (hfp v h5)

end Unip

section Zero

theorem conclAt_of_zero (hK : Nat.card K = 2) {Ã : Subgroup (StatedSp 4 K)}
    (hÃ : IsElemAbelian 3 Ã) (hcard : 3 ^ 3 ≤ Nat.card Ã)
    {T : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hT0 : T ≠ ⊥)
    (hTiso : ∀ u ∈ T, ∀ v ∈ T, spForm 4 K u v = 0) (hTÃ : ∀ a ∈ Ã, ∀ t ∈ T, spEnd a t ∈ T)
    {x : StatedSp 4 K} (hx : x ∈ Ã) (hx1 : x ≠ 1)
    (blocks : SpPrimaryBlocks 2 1 3 x (proj 4 K x)) (hd : spFixedDim x = 0)
    (hEN : EndNodeAt Ã x) : ConclAt Ã x := by
  classical
  haveI := SpFin.finite_statedSp_group (K := K) (m := 4)
  have hx3 : x ^ 3 = 1 := hÃ.2 x hx
  have hx3' : spLin 4 K x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hbx : ∀ b ∈ Ã, b * x = x * b := fun b hb => TableB.IsElemAbelian.comm hÃ hb hx
  have hfix : finrank K (LinearMap.ker (spEnd x - 1)) = spFixedDim x := by
    rw [← blocks.fixed_eq]
    rfl
  have hker : ∀ u, spEnd x u = u → u = 0 := by
    intro u hu
    have h0 : LinearMap.ker (spEnd x - 1) = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hu' : u ∈ LinearMap.ker (spEnd x - 1) := mem_ker_sub_one_iff.mpr hu
    rw [h0, Submodule.mem_bot] at hu'
    exact hu'
  have hfixV : ∀ (b : StatedSp 4 K), ∀ u ∈ LinearMap.ker (spEnd x - 1), spEnd b u = u := by
    intro b u hu
    rw [hker u (mem_ker_sub_one_iff.mp hu), map_zero]
  have hsum : finrank K (LinearMap.ker (spEnd x - 1)) +
      finrank K (LinearMap.range (spEnd x - 1)) = 2 * 4 := by
    have h := Submodule.finrank_add_eq_of_isCompl (SpFin.isCompl_fix_rng hx3')
    rw [SpFin.finrank_spSpace 4] at h
    exact h
  have hh3 := SpFin.h3_mem_primaryFactors hK hx3 hx1
  have hmult : 4 ≤ primaryMultiplicity (spEnd x) (SpFin.h3 K) := by
    haveI : Fact (Irreducible (SpFin.h3 K)) := ⟨SpFin.h3_irreducible hK⟩
    have h1 := finrank_primaryComponent (spEnd x) (SpFin.h3 K)
    rw [SpFin.h3_natDegree] at h1
    have h1' : finrank K (primaryComponent (spEnd x) (SpFin.h3 K)) =
        finrank K (LinearMap.range (spEnd x - 1)) := by
      rw [SpFin.primaryComponent_h3 hK hx3]
    have h2 : primaryMultiplicity (spEnd x) (SpFin.h3 K) =
        finrank (AdjoinRoot (SpFin.h3 K)) (primaryComponent (spEnd x) (SpFin.h3 K)) := rfl
    omega
  have hPq := SpFin.spPull_isQuasisimple_of_four_le (h := ⟨SpFin.h3 K, hh3⟩) blocks
    SpFin.h3_ne_X_sub_one SpFin.h3_reciprocal hmult
  have hlay : layerC x = spPull x (SpFin.h3 K) :=
    SpFin.layer_eq_of_isComponentOf (SpFin.isComponentOf_of_normalized
      (spPull_le_centralizer x _) (spPull_normalized x _) hPq) hEN.1
  have hcent : ∀ s ∈ Ã, (∀ j ∈ spPull x (SpFin.h3 K), s * j = j * s) ↔
      s ∈ Subgroup.zpowers x := by
    intro s hs
    have h := hEN.2 s hs
    rw [hlay] at h
    exact h
  have h9 : 9 ≤ Nat.card (Ã ⊓ spPull x (SpFin.h3 K) : Subgroup (StatedSp 4 K)) := by
    have h := SpFin.card_le_three_mul_inf_pull hK hÃ hx hx1 blocks fun b _ => hfixV b
    norm_num at hcard
    omega
  obtain ⟨t, htmem, htn⟩ : ∃ t ∈ (Ã ⊓ spPull x (SpFin.h3 K) : Subgroup (StatedSp 4 K)),
      t ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle : (Ã ⊓ spPull x (SpFin.h3 K) : Subgroup (StatedSp 4 K)) ≤ Subgroup.zpowers x :=
      fun t ht => hcon t ht
    have h10 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1] at h10
    omega
  obtain ⟨htÃ, htP⟩ := Subgroup.mem_inf.mp htmem
  have ht3 : t ^ 3 = 1 := hÃ.2 t htÃ
  have hj : ∃ j ∈ spPull x (SpFin.h3 K), t * j ≠ j * t := by
    by_contra hcon
    push Not at hcon
    exact htn ((hcent t htÃ).mp hcon)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
  have hug : uElem x v ∈ gammaT T := uElem_mem_gammaT hTiso (hTÃ x hx) hv
  have huc : uElem x v * x = x * uElem x v := uElem_comm hTiso hx3 (hTÃ x hx) hv
  have huP : uElem x v ∈ spPull x (SpFin.h3 K) :=
    mem_spPull_of_sq hK hx3 hx1 blocks huc (gammaT_sq T hug) (hfixV _)
  set U : Subgroup (StatedSp 4 K) := gammaT T ⊓ spPull x (SpFin.h3 K) with hU
  have hU1 : U ≠ ⊥ := by
    intro h
    have hmem : uElem x v ∈ U := ⟨hug, huP⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact uElem_ne_one hK hTiso hx3 hker (hTÃ x hx) hv hv0 hmem
  have hU2 : IsPGroup 2 U := (isPGroup_gammaT T).to_le inf_le_left
  have hUA : ∀ s ∈ Ã, ∀ u ∈ U, s * u * s⁻¹ ∈ U := by
    intro s hs u hu
    exact ⟨conj_mem_gammaT (hTÃ s hs) (hTÃ s⁻¹ (Ã.inv_mem hs)) hu.1,
      spPull_normalized x _ s (Subgroup.mem_centralizer_singleton_iff.mpr (hbx s hs)) u hu.2⟩
  obtain ⟨j, hjP, hjt⟩ := hj
  refine ⟨U, hU1, hU2, ?_, hUA, t, ?_, ht3, fun s hs => TableB.IsElemAbelian.comm hÃ hs htÃ,
    mem_normalizer_of_conj_mem hUA htÃ, j, ?_, hjt⟩
  · rw [hlay]
    exact inf_le_right
  · rw [hlay]
    exact htP
  · rw [hlay]
    exact hjP

end Zero

end CFSG.StandardType.SpFour
