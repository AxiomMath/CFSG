module

public import CFSG.LocalAnalysis.StandardType.GGTPNI1BCSupp
public import CFSG.RankThree.PartOne.S11d.PSpComponent
public import CFSG.RankThree.PartOne.S11d.LayerDecomp

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  Polynomial
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

open CFSG.RankThree.PartOne (charP_two_of_card_eq_pow)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlockEquivOne)

theorem tpbcB_card_statedSp_succ (K : Type) [Field K] [Finite K] (r : ℕ) :
    Nat.card (StatedSp (r + 1) K) =
      Nat.card (StatedSp r K) * (Nat.card K ^ (2 * r + 1) * (Nat.card K ^ (2 * (r + 1)) - 1)) := by
  rw [card_statedSp, card_statedSp, Finset.prod_Icc_succ_top (by omega)]
  have h : (r + 1) ^ 2 = r ^ 2 + (2 * r + 1) := by ring
  rw [h, pow_add]
  ring

theorem tpbcB_card_statedSp_pos (K : Type) [Field K] [Finite K] (r : ℕ) :
    0 < Nat.card (StatedSp r K) := by
  rw [card_statedSp]
  refine Nat.mul_pos (pow_pos Nat.card_pos _) (Finset.prod_pos fun j hj => ?_)
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have : 1 < Nat.card K ^ (2 * j) := Nat.one_lt_pow (by omega) hq
  omega

theorem tpbcB_card_statedSp_strictMono (K : Type) [Field K] [Finite K] :
    StrictMono (fun r => Nat.card (StatedSp r K)) := by
  refine strictMono_nat_of_lt_succ fun r => ?_
  rw [tpbcB_card_statedSp_succ]
  have hpos := tpbcB_card_statedSp_pos K r
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have h1 : 2 ≤ Nat.card K ^ (2 * r + 1) := by
    calc 2 ≤ Nat.card K := hq2
      _ ≤ Nat.card K ^ (2 * r + 1) := Nat.le_self_pow (by omega) _
  have h2 : 3 ≤ Nat.card K ^ (2 * (r + 1)) - 1 := by
    have h4 : 4 ≤ Nat.card K ^ (2 * (r + 1)) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hq2 2
        _ ≤ Nat.card K ^ (2 * (r + 1)) :=
          Nat.pow_le_pow_right (Nat.card_pos) (by omega)
    omega
  have h3 : 1 < Nat.card K ^ (2 * r + 1) * (Nat.card K ^ (2 * (r + 1)) - 1) := by
    calc 1 < 2 * 3 := by norm_num
      _ ≤ _ := Nat.mul_le_mul h1 h2
  calc Nat.card (StatedSp r K) = Nat.card (StatedSp r K) * 1 := (mul_one _).symm
    _ < _ := Nat.mul_lt_mul_of_pos_left h3 hpos

theorem tpbcB_card_of_hasLabel_C {X : Type} [Group X] {m n : ℕ}
    {K : Type} [Field K] [Finite K] (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ n)
    (hlab : GGHasLabel ⟨.C, m, n⟩ X) :
    Nat.card X = Nat.card (StatedSp m K) := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨K', hF, hfin, hK', ⟨e⟩⟩ := (tpbc_hasLabel_C_iff m n X).mp hlab
  haveI : CharP K' 2 := charP_two_of_card_eq_pow hK'
  have hbij : Function.Bijective (proj m K') :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo (r := m)
  have h1 : Nat.card X = Nat.card (StatedProj (StatedSp m K')) := Nat.card_congr e.toEquiv
  have h2 : Nat.card (StatedSp m K') = Nat.card (StatedProj (StatedSp m K')) :=
    Nat.card_congr (MulEquiv.ofBijective (proj m K') hbij).toEquiv
  rw [h1, ← h2, card_statedSp, card_statedSp, hK', hK]

theorem tpbcB_spSupported_fixed_eq_bot_of_dim_zero {r ℓ f p : ℕ} {K : Type} [Field K]
    {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (H : SpPrimaryBlocks ℓ f p x a)
    (h0 : CFSG.RankThree.PartOne.spFixedDim x = 0) :
    spSupported x {X - 1} = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  have hbot : primaryComponent (spEnd x) (X - 1) = ⊥ := by
    have : Module.finrank K (primaryComponent (spEnd x) (X - 1)) = 0 := h0
    exact Submodule.finrank_eq_zero.mp this
  have hsq := H.isInternal.submodule_iSup_eq_top
  have hall : ∀ v : Fin r ⊕ Fin r → K, spEnd w v = v := by
    intro v
    have hv : v ∈ ⨆ k : primaryFactors (spEnd x), primaryComponent (spEnd x) (k : K[X]) := by
      rw [hsq]; trivial
    refine Submodule.iSup_induction (fun k : primaryFactors (spEnd x) =>
      primaryComponent (spEnd x) (k : K[X])) (motive := fun v => spEnd w v = v) hv ?_ ?_ ?_
    · intro k v hv
      by_cases hk : (k : K[X]) = X - 1
      · rw [hk, hbot] at hv
        rw [(Submodule.mem_bot K).mp hv, map_zero]
      · exact (mem_spSupported.mp hw).2 k k.2 (by simpa using hk) v hv
    · exact map_zero _
    · intro a b ha hb
      rw [map_add, ha, hb]
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun v => ?_)
  rw [map_one]
  exact hall v

theorem tpbcB_spFixedDim_pos {r ℓ f p : ℕ} {K : Type} [Field K]
    {x : StatedSp r K} {a : StatedProj (StatedSp r K)} {J : Subgroup (StatedSp r K)}
    (H : SpPrimaryBlocks ℓ f p x a)
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer {x}))
    (hJfix : J ≤ spSupported x {X - 1}) :
    0 < CFSG.RankThree.PartOne.spFixedDim x := by
  by_contra h
  have h0 : CFSG.RankThree.PartOne.spFixedDim x = 0 := by omega
  have hSbot := tpbcB_spSupported_fixed_eq_bot_of_dim_zero H h0
  have hJbot : J ≤ ⊥ := hJfix.trans (le_of_eq hSbot)
  have hJeq : J = ⊥ := le_bot_iff.mp hJbot
  haveI : Nontrivial J := CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2
  rw [hJeq] at this
  exact (not_subsingleton_iff_nontrivial.mpr this) inferInstance

theorem tpbcB_ker_sub_one_ne_top {r : ℕ} {K : Type} [Field K] {x : StatedSp r K}
    (hx1 : x ≠ 1) : LinearMap.ker (spEnd x - 1) ≠ ⊤ := by
  intro h
  apply hx1
  have h0 : spEnd x - 1 = 0 := LinearMap.ker_eq_top.mp h
  have h1 : spEnd x = 1 := sub_eq_zero.mp h0
  have h2 : spLin r K x = 1 := Units.ext h1
  exact spLin_injective (by rw [h2, map_one])

theorem tpbcB_J_eq_fixed {p m n : ℕ} (hp : p.Prime) (hm : 3 ≤ m) (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hchar : CharP K 2) (hK : Nat.card K = 2 ^ n)
    {x : StatedSp (m + 1) K} {J : Subgroup (StatedSp (m + 1) K)}
    (H : SpPrimaryBlocks 2 n p x (proj (m + 1) K x))
    (hxord : orderOf x = p)
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer {x}))
    (hJfix : J ≤ spSupported x {X - 1})
    (hlab : GGHasLabel ⟨.C, m, n⟩ (↥J ⧸ Subgroup.center ↥J)) :
    J = spSupported x {X - 1} := by
  have hpos := tpbcB_spFixedDim_pos H hJ hJfix
  have hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) :=
    CFSG.RankThree.PartOne.X_sub_one_mem_primaryFactors x hpos
  obtain ⟨φ, -⟩ := H.fixedFactor hmem
  have hB : ((spForm (m + 1) K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin (m + 1) ⊕ Fin (m + 1) → K)
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp
      hB H.fixed_nondegenerate
  have hcard_quot : Nat.card (↥J ⧸ Subgroup.center ↥J) = Nat.card (StatedSp m K) :=
    tpbcB_card_of_hasLabel_C (by omega) hK hlab
  have hcard_quot_le : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card J :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hcard_J_le : Nat.card J ≤ Nat.card (spSupported x {X - 1}) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hJfix) (Subgroup.inclusion_injective hJfix)
  have hcard_S : Nat.card (spSupported x {X - 1}) = Nat.card (StatedSp s K) :=
    Nat.card_congr (φ.trans e).toEquiv
  have hchain : Nat.card (StatedSp m K) ≤ Nat.card (StatedSp s K) := by
    rw [← hcard_quot, ← hcard_S]
    exact hcard_quot_le.trans hcard_J_le
  have hms : m ≤ s := by
    by_contra h
    push_neg at h
    have := (tpbcB_card_statedSp_strictMono K).lt_iff_lt.mpr h
    omega
  have hsm : s ≤ m := by
    have hx1 : x ≠ 1 := by
      intro hx; rw [hx, orderOf_one] at hxord; exact hp.one_lt.ne' hxord.symm
    have hVdim : Module.finrank K (Fin (m + 1) ⊕ Fin (m + 1) → K) = 2 * (m + 1) := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp [two_mul]
    have hker : LinearMap.ker (spEnd x - 1) ≠ ⊤ := tpbcB_ker_sub_one_ne_top hx1
    have hlt : Module.finrank K (primaryComponent (spEnd x) (X - 1)) < 2 * (m + 1) := by
      rw [H.fixed_eq, ← hVdim]
      exact Submodule.finrank_lt hker
    omega
  have hsm_eq : s = m := le_antisymm hsm hms
  have hcard_J_eq : Nat.card J = Nat.card (StatedSp m K) := by
    apply le_antisymm
    · calc Nat.card J ≤ Nat.card (spSupported x {X - 1}) := hcard_J_le
        _ = Nat.card (StatedSp s K) := hcard_S
        _ = Nat.card (StatedSp m K) := by rw [hsm_eq]
    · calc Nat.card (StatedSp m K) = Nat.card (↥J ⧸ Subgroup.center ↥J) := hcard_quot.symm
        _ ≤ Nat.card J := hcard_quot_le
  refine Subgroup.eq_of_le_of_card_ge hJfix ?_
  rw [hcard_S, hsm_eq, hcard_J_eq]

theorem tpbcB_spFixedDim_eq {p m n : ℕ} (hp : p.Prime) (hm : 3 ≤ m) (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hchar : CharP K 2) (hK : Nat.card K = 2 ^ n)
    {x : StatedSp (m + 1) K} {J : Subgroup (StatedSp (m + 1) K)}
    (H : SpPrimaryBlocks 2 n p x (proj (m + 1) K x))
    (hxord : orderOf x = p)
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer {x}))
    (hJfix : J ≤ spSupported x {X - 1})
    (hlab : GGHasLabel ⟨.C, m, n⟩ (↥J ⧸ Subgroup.center ↥J)) :
    CFSG.RankThree.PartOne.spFixedDim x = 2 * m := by
  have hpos := tpbcB_spFixedDim_pos H hJ hJfix
  have hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) :=
    CFSG.RankThree.PartOne.X_sub_one_mem_primaryFactors x hpos
  obtain ⟨φ, -⟩ := H.fixedFactor hmem
  have hB : ((spForm (m + 1) K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin (m + 1) ⊕ Fin (m + 1) → K)
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp
      hB H.fixed_nondegenerate
  have hJeq : J = spSupported x {X - 1} := tpbcB_J_eq_fixed hp hm hn hchar hK H hxord hJ hJfix hlab
  have hcard_quot : Nat.card (↥J ⧸ Subgroup.center ↥J) = Nat.card (StatedSp m K) :=
    tpbcB_card_of_hasLabel_C (by omega) hK hlab
  have hcard_S : Nat.card (spSupported x {X - 1}) = Nat.card (StatedSp s K) :=
    Nat.card_congr (φ.trans e).toEquiv
  have hsm : s ≤ m := by
    have hx1 : x ≠ 1 := by
      intro hx; rw [hx, orderOf_one] at hxord; exact hp.one_lt.ne' hxord.symm
    have hVdim : Module.finrank K (Fin (m + 1) ⊕ Fin (m + 1) → K) = 2 * (m + 1) := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp [two_mul]
    have hker : LinearMap.ker (spEnd x - 1) ≠ ⊤ := tpbcB_ker_sub_one_ne_top hx1
    have hlt : Module.finrank K (primaryComponent (spEnd x) (X - 1)) < 2 * (m + 1) := by
      rw [H.fixed_eq, ← hVdim]
      exact Submodule.finrank_lt hker
    omega
  have hcard_J : Nat.card J = Nat.card (StatedSp m K) := by
    have hle : Nat.card J ≤ Nat.card (StatedSp m K) := by
      calc Nat.card J = Nat.card (spSupported x {X - 1}) := by rw [hJeq]
        _ = Nat.card (StatedSp s K) := hcard_S
        _ ≤ Nat.card (StatedSp m K) := (tpbcB_card_statedSp_strictMono K).monotone hsm
    have hge : Nat.card (StatedSp m K) ≤ Nat.card J := by
      calc Nat.card (StatedSp m K) = Nat.card (↥J ⧸ Subgroup.center ↥J) := hcard_quot.symm
        _ ≤ Nat.card J :=
          Nat.card_le_card_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    exact le_antisymm hle hge
  have hs_eq : s = m := (tpbcB_card_statedSp_strictMono K).injective (by
    rw [← hcard_S, ← hcard_J, hJeq])
  unfold CFSG.RankThree.PartOne.spFixedDim
  rw [hs, hs_eq]

theorem tpbcB_fix_action {p m n : ℕ} (hp : p.Prime)
    {K : Type} [Field K] [Finite K] (hchar : CharP K 2)
    {x : StatedSp (m + 1) K} {J E : Subgroup (StatedSp (m + 1) K)}
    (H : SpPrimaryBlocks 2 n p x (proj (m + 1) K x))
    (hJ_eq : J = spSupported x {X - 1})
    (hcomm : ∀ e ∈ E, ∀ j ∈ J, e * j = j * e)
    (hpos : 0 < CFSG.RankThree.PartOne.spFixedDim x)
    {e : StatedSp (m + 1) K} (he : e ∈ E) :
    ∀ u ∈ primaryComponent (spEnd x) (X - 1), spEnd e u = u := by
  have hcent : e ∈ Subgroup.centralizer
      (CFSG.RankThree.PartOne.spFixedFactor x : Set (StatedSp (m + 1) K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : s ∈ J := by rw [hJ_eq]; exact hs
    exact (hcomm e he s hs').symm
  obtain ⟨l, hl⟩ := CFSG.RankThree.PartOne.scalar_on_fix_of_centralizes hcent
  have hl' : ∀ u ∈ primaryComponent (spEnd x) (X - 1), spEnd e u = l • u :=
    fun u hu => hl u (H.fixed_eq ▸ hu)
  have hl1 : l = 1 := by
    have hnd := H.fixed_nondegenerate
    have hV0ne : primaryComponent (spEnd x) (X - 1) ≠ ⊥ := by
      intro hbot
      have : CFSG.RankThree.PartOne.spFixedDim x = 0 := by
        unfold CFSG.RankThree.PartOne.spFixedDim
        rw [hbot]; simp
      omega
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0ne
    obtain ⟨v, hv, huv⟩ : ∃ v ∈ primaryComponent (spEnd x) (X - 1),
        spForm (m + 1) K u v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h0 := hnd.1 ⟨u, hu⟩ (fun w => hcon w.1 w.2)
      exact hu0 (congrArg Subtype.val h0)
    have hiso : spForm (m + 1) K (spEnd e u) (spEnd e v) = spForm (m + 1) K u v :=
      mem_sesqUnitaryGroup.mp (spLin_mem e) u v
    rw [hl' u hu, hl' v hv] at hiso
    have h1 : spForm (m + 1) K (l • u) (l • v) = (l * l) * spForm (m + 1) K u v := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have hiso' : (l * l) * spForm (m + 1) K u v = spForm (m + 1) K u v := by
      rw [← h1]; exact hiso
    have hll : l * l = 1 := by
      have h2 : (l * l) * spForm (m + 1) K u v = 1 * spForm (m + 1) K u v := by
        rw [hiso']; ring
      exact mul_right_cancel₀ huv h2
    rcases mul_self_eq_one_iff.mp hll with h1 | h1
    · exact h1
    · rw [h1, CharTwo.neg_eq]
  intro u hu
  rw [hl' u hu, hl1, one_smul]

theorem tpbcB_card_le_of_fixed_action {p m n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] (hchar : CharP K 2)
    {x : StatedSp (m + 1) K} {E : Subgroup (StatedSp (m + 1) K)}
    (H : SpPrimaryBlocks 2 n p x (proj (m + 1) K x))
    (hdim : CFSG.RankThree.PartOne.spFixedDim x = 2 * m)
    (hE : IsElemAbelian p E)
    (hfix : ∀ e ∈ E, ∀ u ∈ primaryComponent (spEnd x) (X - 1), spEnd e u = u) :
    Nat.card E ≤ p := by
  classical
  have hBnd : (spForm (m + 1) K).Nondegenerate := spForm_nondegenerate
  have hBalt : (spForm (m + 1) K).IsAlt := spForm_isAlt
  have hrefl : (spForm (m + 1) K).IsRefl := hBalt.isRefl
  have hV0nd : ((spForm (m + 1) K).restrict
      (primaryComponent (spEnd x) (X - 1))).Nondegenerate := H.fixed_nondegenerate
  set W : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    (spForm (m + 1) K).orthogonal (primaryComponent (spEnd x) (X - 1)) with hWdef
  have hcompl : IsCompl (primaryComponent (spEnd x) (X - 1)) W :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hV0nd
  have hWnd : ((spForm (m + 1) K).restrict W).Nondegenerate := by
    rw [hWdef, LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hrefl]
    rw [LinearMap.BilinForm.orthogonal_orthogonal hBnd hrefl]
    exact hcompl.symm
  have hWdim : Module.finrank K W = 2 := by
    have hV0d : Module.finrank K (primaryComponent (spEnd x) (X - 1)) = 2 * m := hdim
    rw [hWdef, LinearMap.BilinForm.finrank_orthogonal hBnd, hV0d]
    have hVdim : Module.finrank K (Fin (m + 1) ⊕ Fin (m + 1) → K) = 2 * (m + 1) := by
      rw [Module.finrank_fintype_fun_eq_card]; simp [two_mul]
    omega
  have hWmem : ∀ a ∈ E, ∀ w ∈ W, spEnd a w ∈ W := by
    intro a ha w hw
    rw [hWdef, LinearMap.BilinForm.mem_orthogonal_iff] at hw ⊢
    intro u hu
    refine hrefl (spEnd a w) u ?_
    have hiso := mem_sesqUnitaryGroup.mp (spLin_mem a) w u
    change spForm (m + 1) K (spEnd a w) (spEnd a u) = spForm (m + 1) K w u at hiso
    rw [hfix a ha u hu] at hiso
    rw [hiso]
    exact hrefl u w (hw u hu)
  have hres : ∀ a ∈ E, W.map
      ((spLin (m + 1) K (a : StatedSp (m + 1) K)).toLinearEquiv : _ →ₗ[K] _) = W := by
    intro a ha
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hWmem a ha w hw
    · intro w hw
      refine ⟨(spLin (m + 1) K (a : StatedSp (m + 1) K)).toLinearEquiv.symm w, ?_, ?_⟩
      · change spEnd a⁻¹ w ∈ W
        exact hWmem a⁻¹ (E.inv_mem ha) w hw
      · exact (spLin (m + 1) K (a : StatedSp (m + 1) K)).toLinearEquiv.apply_symm_apply w
  have hψmem : ∀ a : E, LinearMap.GeneralLinearGroup.ofLinearEquiv
      (LinearEquiv.ofSubmodules ((spLin (m + 1) K (a : StatedSp (m + 1) K)).toLinearEquiv) W W
        (hres a a.2)) ∈ sesqUnitaryGroup ((spForm (m + 1) K).restrict W) := by
    intro a
    rw [mem_sesqUnitaryGroup]
    intro u v
    change spForm (m + 1) K (spEnd (a : StatedSp (m + 1) K) (u : _))
      (spEnd (a : StatedSp (m + 1) K) (v : _)) = spForm (m + 1) K (u : _) (v : _)
    exact mem_sesqUnitaryGroup.mp (spLin_mem (a : StatedSp (m + 1) K)) (u : _) (v : _)
  let ψ : E →* sesqUnitaryGroup ((spForm (m + 1) K).restrict W) :=
    { toFun := fun a => ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv
        (LinearEquiv.ofSubmodules ((spLin (m + 1) K (a : StatedSp (m + 1) K)).toLinearEquiv) W W
          (hres a a.2)), hψmem a⟩
      map_one' := by
        ext w
        simp [LinearEquiv.ofSubmodules_apply]
      map_mul' := by
        intro a b
        ext w
        simp only [LinearEquiv.ofSubmodules_apply, LinearMap.GeneralLinearGroup.coe_ofLinearEquiv,
          Subgroup.coe_mul]
        rw [map_mul, LinearMap.GeneralLinearGroup.toLinearEquiv_mul]
        rfl }
  have hψ_inj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    apply Subtype.ext
    apply spLin_injective
    apply Units.ext
    apply LinearMap.ext
    intro v
    have hv : v ∈ primaryComponent (spEnd x) (X - 1) ⊔ W := by
      rw [hcompl.sup_eq_top]
      trivial
    obtain ⟨u, hu, w, hw, huv⟩ := Submodule.mem_sup.mp hv
    rw [← huv, map_add, hfix a a.2 u hu]
    congr 1
    have hw_id : ((ψ a : sesqUnitaryGroup ((spForm (m + 1) K).restrict W)) :
        LinearMap.GeneralLinearGroup K ↥W) = 1 := by
      simpa using congrArg Subtype.val ha
    have h2 : (((ψ a : sesqUnitaryGroup ((spForm (m + 1) K).restrict W)) :
        LinearMap.GeneralLinearGroup K ↥W) : ↥W →ₗ[K] ↥W) ⟨w, hw⟩ = ⟨w, hw⟩ := by
      rw [hw_id]; rfl
    simpa [ψ, LinearMap.GeneralLinearGroup.coe_ofLinearEquiv,
      LinearMap.GeneralLinearGroup.coe_toLinearEquiv, LinearEquiv.ofSubmodules_apply,
      spEnd] using congrArg Subtype.val h2
  have hWalt : ((spForm (m + 1) K).restrict W).IsAlt := by
    intro x
    change spForm (m + 1) K (x : Fin (m + 1) ⊕ Fin (m + 1) → K)
      (x : Fin (m + 1) ⊕ Fin (m + 1) → K) = 0
    exact hBalt (x : Fin (m + 1) ⊕ Fin (m + 1) → K)
  have hψel : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp u.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp v.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← ha, ← hb, ← map_mul, ← map_mul, hE.1.is_comm.comm a b]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have ha : a ^ p = 1 := Subtype.ext (by simpa using hE.2 a.1 a.2)
      rw [ha]
      exact map_one ψ
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hWalt hWnd
  have hs1 : s = 1 := by
    have : 2 * s = 2 := by rw [← hs, hWdim]
    omega
  subst s
  let e' : sesqUnitaryGroup ((spForm (m + 1) K).restrict W) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K := e.trans (longBlockEquivOne K).symm
  have hE' : IsElemAbelian p (ψ.range.map e'.toMonoidHom) := hψel.map e'.toMonoidHom
  have hcard : Nat.card (ψ.range.map e'.toMonoidHom) ≤ p :=
    tpbc_card_le_of_isElemAbelian_sl2 hp hp2 hE'
  have hcard_eq : Nat.card (ψ.range.map e'.toMonoidHom) = Nat.card E := by
    rw [Subgroup.card_map_of_injective e'.injective,
      MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψ_inj]
    exact Nat.card_congr (Subgroup.topEquiv (G := ↥E)).toEquiv
  rw [← hcard_eq]
  exact hcard

theorem tpbcc_le_zpowers_of_fixed {p m n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hchar : CharP K 2) (hK : Nat.card K = 2 ^ n)
    {x : StatedSp (m + 1) K} {J E : Subgroup (StatedSp (m + 1) K)}
    (H : SpPrimaryBlocks 2 n p x (proj (m + 1) K x)) (hprojinj : Function.Injective (proj (m + 1) K))
    (hxp : x ^ p = 1) (hxord : orderOf x = p) (hxE : x ∈ E) (hE : IsElemAbelian p E)
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer {x}))
    (hJfix : J ≤ spSupported x {X - 1})
    (hlab : GGHasLabel ⟨.C, m, n⟩ (↥J ⧸ Subgroup.center ↥J))
    (hcomm : ∀ e ∈ E, ∀ j ∈ J, e * j = j * e) : E ≤ Subgroup.zpowers x := by
  have hJeq : J = spSupported x {X - 1} :=
    tpbcB_J_eq_fixed hp hm hn hchar hK H hxord hJ hJfix hlab
  have hdim : CFSG.RankThree.PartOne.spFixedDim x = 2 * m :=
    tpbcB_spFixedDim_eq hp hm hn hchar hK H hxord hJ hJfix hlab
  have hpos : 0 < CFSG.RankThree.PartOne.spFixedDim x := by rw [hdim]; omega
  have hfix : ∀ e ∈ E, ∀ u ∈ primaryComponent (spEnd x) (X - 1), spEnd e u = u :=
    fun e he => tpbcB_fix_action hp hchar H hJeq hcomm hpos he
  have hxne : x ≠ 1 := by
    intro hx
    have : p = 1 := by rw [← hxord, hx, orderOf_one]
    exact hp.ne_one this
  have hcard : Nat.card E ≤ p :=
    tpbcB_card_le_of_fixed_action hp hp2 hchar H hdim hE hfix
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : Subgroup.zpowers x ≤ E := Subgroup.zpowers_le.mpr hxE
  have h2 : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hxne]
  exact (Subgroup.eq_of_le_of_card_ge h1 (h2 ▸ hcard)).ge

end CFSG.StandardType

end
