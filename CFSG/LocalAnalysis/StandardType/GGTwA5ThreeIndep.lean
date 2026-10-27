module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTBXDatumOfTor
public import CFSG.LocalAnalysis.StandardType.GGTBTorCartan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem twi1_natCast_mul_div_eq {m a b : ℕ} (h3m : 3 ∣ m)
    (h : (a : ZMod 3) = (b : ZMod 3)) :
    (a : ZMod m) * ((m / 3 : ℕ) : ZMod m) =
      (b : ZMod m) * ((m / 3 : ℕ) : ZMod m) := by
  have h3 : (3 : ℤ) ∣ (a : ℤ) - (b : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) - (b : ℤ)) 3).mp (by
      push_cast
      rw [h, sub_self])
  obtain ⟨c, hc⟩ := h3
  have h3m' : (3 : ZMod m) * ((m / 3 : ℕ) : ZMod m) = 0 := by
    have h : ((3 : ℕ) : ZMod m) * ((m / 3 : ℕ) : ZMod m) = 0 := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' h3m, ZMod.natCast_self]
    simpa using h
  have hzero : ((a : ZMod m) - (b : ZMod m)) * ((m / 3 : ℕ) : ZMod m) = 0 := by
    rw [show (a : ZMod m) - (b : ZMod m) = (((a : ℤ) - (b : ℤ) : ℤ) : ZMod m) by
      push_cast; ring, hc]
    push_cast
    rw [show (3 : ZMod m) * (c : ZMod m) * ((m / 3 : ℕ) : ZMod m)
        = (c : ZMod m) * ((3 : ZMod m) * ((m / 3 : ℕ) : ZMod m)) by ring, h3m', mul_zero]
  rw [sub_mul, sub_eq_zero] at hzero
  exact hzero

private theorem twi1_three_mul_eq_zero {m : ℕ} (hm : Odd m) (h3m : 3 ∣ m) {x : ZMod m}
    (hx : (3 : ZMod m) * x = 0) :
    ∃ t : ℕ, t < 3 ∧ x = (t : ZMod m) * ((m / 3 : ℕ) : ZMod m) := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  haveI : NeZero m := ⟨hm0⟩
  have hmpos : 0 < m / 3 :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h3m) (by norm_num)
  have hdiv : m ∣ 3 * x.val := by
    have h1 : ((3 * x.val : ℕ) : ZMod m) = 0 := by
      rw [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
      exact hx
    exact (ZMod.natCast_eq_zero_iff (3 * x.val) m).mp h1
  obtain ⟨k, hk⟩ := hdiv
  have hmul : m = 3 * (m / 3) := (Nat.mul_div_cancel' h3m).symm
  have hmk : m * k = 3 * ((m / 3) * k) := by
    conv_lhs => rw [hmul]
    rw [mul_assoc]
  have hxval : x.val = (m / 3) * k := Nat.mul_left_cancel (by norm_num) (hk.trans hmk)
  refine ⟨k, ?_, ?_⟩
  · have hxlt : x.val < m := ZMod.val_lt x
    have h1 : (m / 3) * k < (m / 3) * 3 := by
      calc (m / 3) * k = x.val := hxval.symm
        _ < m := hxlt
        _ = 3 * (m / 3) := hmul
        _ = (m / 3) * 3 := by rw [mul_comm]
    exact (Nat.mul_lt_mul_left hmpos).mp h1
  · rw [← ZMod.natCast_zmod_val x, hxval]
    push_cast
    ring

private theorem twi1_two_mul_eq_zero {m : ℕ} (hm : Odd m) {y : ZMod m}
    (hy : (2 : ZMod m) * y = 0) : y = 0 := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  haveI : NeZero m := ⟨hm0⟩
  have hdiv : m ∣ 2 * y.val := by
    have h1 : ((2 * y.val : ℕ) : ZMod m) = 0 := by
      rw [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
      exact hy
    exact (ZMod.natCast_eq_zero_iff (2 * y.val) m).mp h1
  have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
  have hdvd : m ∣ y.val := by
    refine hcop.symm.dvd_of_dvd_mul_right ?_
    rwa [mul_comm] at hdiv
  rw [← ZMod.natCast_zmod_val y]
  exact (ZMod.natCast_eq_zero_iff y.val m).mpr hdvd

private noncomputable def twi1_corProd {m N : ℕ} {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) :
    (Fin N → Multiplicative (ZMod m)) →* L' :=
  MonoidHom.noncommPiCoprod cor (fun i j _ _x _y => hcomm i j _ _)

private theorem twi1_corProd_apply {m N : ℕ} {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ))
    (f : Fin N → Multiplicative (ZMod m)) :
    twi1_corProd cor hcomm f = (List.ofFn fun k => cor k (f k)).prod := by
  change Finset.univ.noncommProd (fun i => cor i (f i)) (fun i _ j _ _ => hcomm i j _ _) = _
  unfold Finset.noncommProd
  exact ggTor_multiset_noncommProd (α := L') _ _ (Fin.univ_val_map _) _

private theorem twi1_corProd_mulSingle {m N : ℕ} {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) (k : Fin N)
    (y : Multiplicative (ZMod m)) :
    twi1_corProd cor hcomm (Pi.mulSingle k y) = cor k y :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

private theorem twi1_corProd_mem_iSup {m N : ℕ} {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ))
    (f : Fin N → Multiplicative (ZMod m)) :
    twi1_corProd cor hcomm f ∈ ⨆ k, (cor k).range := by
  rw [twi1_corProd_apply]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  exact Subgroup.mem_iSup_of_mem k (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

private theorem twi1_iSup_le_range {m N : ℕ} {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) :
    (⨆ k, (cor k).range) ≤ (twi1_corProd cor hcomm).range := by
  refine iSup_le fun k => ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨Pi.mulSingle k y, twi1_corProd_mulSingle cor hcomm k y⟩

private theorem twi1_ker {m : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {C : Matrix (Fin 5) (Fin 5) ℤ} {M : CoxeterMatrix (Fin 5)}
    (w : GGTorusTorWit m 5 L' A) (hw : w.Holds C M)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ))
    (ξ : Fin 5 → Multiplicative (ZMod m))
    (hξ : MulAut.conj (twi1_corProd w.cor hcomm ξ) = 1) :
    ∀ j, ∑ k, (C j k : ZMod m) * Multiplicative.toAdd (ξ k) = 0 := by
  obtain ⟨-, -, hcorT, hαmul, -, -, -, hpair, -⟩ := hw
  intro j
  have hmem : ∀ g, MulAut.conj (twi1_corProd w.cor hcomm g) ∈ w.T := by
    intro g
    have h1 : ⨆ k, (w.cor k).range ≤ w.T.comap (MulAut.conj : L' →* MulAut L') :=
      iSup_le fun k => by
        rintro _ ⟨ζ, rfl⟩
        exact hcorT k ζ
    exact h1 (twi1_corProd_mem_iSup w.cor hcomm g)
  let β : (Fin 5 → Multiplicative (ZMod m)) →* Multiplicative (ZMod m) :=
    (ggTorAlphaHom w.T (w.α j) (hαmul j)).comp
      (((MulAut.conj : L' →* MulAut L').comp (twi1_corProd w.cor hcomm)).codRestrict w.T hmem)
  have hβ : ∀ g, β g = w.α j (MulAut.conj (twi1_corProd w.cor hcomm g)) := fun g => rfl
  have hβs : ∀ k y, β (Pi.mulSingle k y) = y ^ C j k := by
    intro k y
    rw [hβ, twi1_corProd_mulSingle, hpair]
  have h1 : β ξ = 1 := by rw [hβ, hξ]; exact ggTor_alpha_one w.T (w.α j) (hαmul j)
  rw [← Finset.univ_prod_mulSingle ξ, map_prod] at h1
  simp only [hβs] at h1
  have h1list : (List.ofFn fun k => ξ k ^ C j k).prod = 1 := by
    rw [List.prod_ofFn]; exact h1
  have hsum : (List.ofFn fun k => (C j k) • Multiplicative.toAdd (ξ k)).sum = 0 := by
    apply Multiplicative.ofAdd.injective
    rw [ofAdd_list_prod]
    have hfun : (Multiplicative.ofAdd ∘ fun k => (C j k) • Multiplicative.toAdd (ξ k))
        = (fun k => ξ k ^ C j k) := by
      funext k
      rw [Function.comp_apply, ofAdd_zsmul]
      exact congrArg (· ^ (C j k)) (Equiv.apply_symm_apply Multiplicative.ofAdd (ξ k))
    have hlist : (List.map Multiplicative.ofAdd
          (List.ofFn fun k => (C j k) • Multiplicative.toAdd (ξ k)))
        = (List.ofFn fun k => ξ k ^ C j k) := by
      rw [List.map_ofFn]
      exact congrArg List.ofFn hfun
    rw [hlist, h1list]
    rfl
  rw [List.sum_ofFn] at hsum
  simpa only [zsmul_eq_mul, Int.cast_natCast] using hsum

private theorem twi1_ggTor_ker {m : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {C : Matrix (Fin 5) (Fin 5) ℤ} {M : CoxeterMatrix (Fin 5)}
    (hm0 : m ≠ 0) (h3m : 3 ∣ m)
    (w : GGTorusTorWit m 5 L' A) (hw : w.Holds C M)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ))
    (f : Fin 5 → Multiplicative (ZMod 3))
    (hf : MulAut.conj (ggTorE h3m w.cor hcomm f) = 1) :
    ∀ j, ∑ k, (C j k : ZMod 3) * Multiplicative.toAdd (f k) = 0 := by
  obtain ⟨-, -, hcorT, hαmul, -, -, -, hpair, -⟩ := hw
  intro j
  have hmem : ∀ g, MulAut.conj (ggTorE h3m w.cor hcomm g) ∈ w.T := by
    intro g
    have h1 : ⨆ k, (w.cor k).range ≤ w.T.comap (MulAut.conj : L' →* MulAut L') :=
      iSup_le fun k => by
        rintro _ ⟨ζ, rfl⟩
        exact hcorT k ζ
    exact h1 (ggTorE_mem h3m w.cor hcomm g)
  let β : (Fin 5 → Multiplicative (ZMod 3)) →* Multiplicative (ZMod m) :=
    (ggTorAlphaHom w.T (w.α j) (hαmul j)).comp
      (((MulAut.conj : L' →* MulAut L').comp (ggTorE h3m w.cor hcomm)).codRestrict w.T hmem)
  have hβ : ∀ g, β g = w.α j (MulAut.conj (ggTorE h3m w.cor hcomm g)) := fun g => rfl
  have hβs : ∀ k y, β (Pi.mulSingle k y) =
      ggZetaP 3 m ^ ((Multiplicative.toAdd y).val * C j k) := by
    intro k y
    rw [hβ, ggTorE_mulSingle, hpair, ggTorPsi_apply, ← zpow_natCast, ← zpow_mul]
  have h1 : β f = 1 := by
    rw [hβ, hf]
    exact ggTor_alpha_one w.T (w.α j) (hαmul j)
  rw [← Finset.univ_prod_mulSingle f, map_prod] at h1
  simp only [hβs] at h1
  rw [ggTor_zpow_sum, ← orderOf_dvd_iff_zpow_eq_one, ggZetaP_orderOf Nat.prime_three hm0 h3m,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  push_cast at h1
  simpa [ZMod.natCast_zmod_val, mul_comm] using h1

private def twi1_c0vec : Fin 5 → ZMod 3 := ![1, 2, 0, 1, 2]

private theorem twi1_c0vec_eq (k : Fin 5) : twi1_c0vec k = (k : ZMod 3) + 1 := by
  fin_cases k <;> decide

private def twi1_c0fun : Fin 5 → Multiplicative (ZMod 3) :=
  fun k => Multiplicative.ofAdd (twi1_c0vec k)

private def twi1_c0funM (m : ℕ) : Fin 5 → Multiplicative (ZMod m) :=
  fun k => ggZetaP 3 m ^ (twi1_c0vec k).val

private theorem twi1_ggTorE_eq_corProd {m : ℕ} {L' : Type} [Group L']
    {A : Subgroup (MulAut L')}
    (h3m : 3 ∣ m) (w : GGTorusTorWit m 5 L' A)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)) :
    ggTorE h3m w.cor hcomm twi1_c0fun = twi1_corProd w.cor hcomm (twi1_c0funM m) := by
  rw [ggTorE_apply, twi1_corProd_apply]
  refine congrArg (fun l : List L' => l.prod) (congrArg List.ofFn (funext fun k => ?_))
  simp only [twi1_c0fun, twi1_c0funM, ggTorPsi_apply, Multiplicative.toAdd,
    Equiv.symm_apply_apply]

theorem ggTorusTorWit_coroot_indep_twA5 {m : ℕ} (hm : Odd m) (h3m : 3 ∣ m)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')} (w : GGTorusTorWit m 5 L' A)
    (hw : w.Holds (CartanMatrix.A 5) (CoxeterMatrix.A 5)) {z : L'}
    (hz : z ∈ Subgroup.center L') (hzo : orderOf z = 3) :
    ∀ c : Fin 5 → ZMod 3,
      (List.ofFn fun k => w.cor k (ggZetaP 3 m ^ (c k).val)).prod = 1 → c = 0 := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hw' := hw
  obtain ⟨-, hAT, hcorT, hαmul, -, hcomm, hfix, hpair, -, -, hsep, -, -, hoddZ,
    ⟨-, hTfix, htor⟩, -, -⟩ := hw
  intro c hc
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hzm : z ^ m = 1 := by
    obtain ⟨n, hn⟩ := h3m
    rw [hn, pow_mul, hz3, one_pow]
  have hzTsc : z ∈ w.Tsc := hoddZ z hz (by rw [hzo]; norm_num)
  have hziSup : z ∈ ⨆ k, (w.cor k).range := htor z hzTsc hzm
  obtain ⟨ξ, hξ⟩ := MonoidHom.mem_range.mp (twi1_iSup_le_range w.cor hcomm hziSup)
  have hξ1 : MulAut.conj (twi1_corProd w.cor hcomm ξ) = 1 := by
    rw [hξ]
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hz g).symm]
    group
  have hsys := twi1_ker w hw' hcomm ξ hξ1
  set x : Fin 5 → ZMod m := fun k => Multiplicative.toAdd (ξ k) with hx
  have hsys' : ∀ j, ∑ k, (CartanMatrix.A 5 j k : ZMod m) * x k = 0 := fun j => hsys j
  have hcoord := cartanA_ker_coord (p := m) (N := 5) x hsys'
  have hxk : ∀ k : Fin 5, x k = ((k : ZMod m) + 1) * x 0 := by
    intro k
    have := hcoord k.val k.isLt
    simpa using this
  have h6x0 : 6 * x 0 = 0 := by
    have h4 := hsys' 4
    simp [CartanMatrix.A, Fin.sum_univ_succ] at h4
    rw [hxk 3, hxk 4] at h4
    norm_num at h4
    linear_combination h4
  have h3x0 : (3 : ZMod m) * x 0 = 0 := by
    have h2y : (2 : ZMod m) * ((3 : ZMod m) * x 0) = 0 := by
      rw [show (2 : ZMod m) * ((3 : ZMod m) * x 0) = 6 * x 0 by ring]
      exact h6x0
    exact twi1_two_mul_eq_zero hm h2y
  obtain ⟨t, ht3, hxt⟩ := twi1_three_mul_eq_zero hm h3m h3x0
  set P0 : L' := ggTorE h3m w.cor hcomm twi1_c0fun with hP0
  have hP0_eq : P0 = twi1_corProd w.cor hcomm (twi1_c0funM m) := by
    rw [hP0]
    exact twi1_ggTorE_eq_corProd h3m w hcomm
  have hξeq : ξ = twi1_c0funM m ^ t := by
    funext k
    have hxk' : x k = (((k + 1) * t : ℕ) : ZMod m) * ((m / 3 : ℕ) : ZMod m) := by
      rw [hxk k, hxt]
      push_cast
      ring
    have hcmp : (((k + 1) * t : ℕ) : ZMod 3) = (((twi1_c0vec k).val * t : ℕ) : ZMod 3) := by
      push_cast
      rw [twi1_c0vec_eq, ZMod.natCast_zmod_val]
    have hmain : (((k + 1) * t : ℕ) : ZMod m) * ((m / 3 : ℕ) : ZMod m) =
        (((twi1_c0vec k).val * t : ℕ) : ZMod m) * ((m / 3 : ℕ) : ZMod m) :=
      twi1_natCast_mul_div_eq h3m hcmp
    have hξk : ξ k = Multiplicative.ofAdd (x k) := by
      rw [hx]
      exact (ofAdd_toAdd (ξ k)).symm
    show ξ k = (twi1_c0funM m ^ t) k
    rw [Pi.pow_apply, hξk, hxk']
    have hzpow : (twi1_c0funM m k) ^ t =
        Multiplicative.ofAdd ((((twi1_c0vec k).val * t : ℕ) : ZMod m) *
          ((m / 3 : ℕ) : ZMod m)) := by
      show (ggZetaP 3 m ^ (twi1_c0vec k).val) ^ t = _
      rw [← pow_mul]
      show (Multiplicative.ofAdd ((m / 3 : ℕ) : ZMod m)) ^ ((twi1_c0vec k).val * t) = _
      rw [← ofAdd_nsmul, nsmul_eq_mul]
    rw [hzpow, hmain]
  have hzt : z = P0 ^ t := by
    rw [← hξ, hξeq, map_pow, ← hP0_eq]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hzo
    norm_num at hzo
  have hP01 : P0 ≠ 1 := by
    intro h
    apply hz1
    rw [hzt, h, one_pow]
  have hP03 : P0 ^ 3 = 1 := by
    rw [hP0_eq, ← map_pow]
    have h3 : twi1_c0funM m ^ 3 = 1 := by
      funext k
      rw [Pi.pow_apply, Pi.one_apply]
      show (ggZetaP 3 m ^ (twi1_c0vec k).val) ^ 3 = 1
      rw [← pow_mul, mul_comm, pow_mul, ggZetaP_pow_self h3m, one_pow]
    rw [h3, map_one]
  have hP0o : orderOf P0 = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hP03 hP01
  have hcf : ggTorE h3m w.cor hcomm (fun k => Multiplicative.ofAdd (c k)) = 1 := by
    rw [ggTorE_apply]
    simpa only [ggTorPsi_apply, Multiplicative.toAdd, Equiv.symm_apply_apply] using hc
  have hcf' : MulAut.conj (ggTorE h3m w.cor hcomm
      (fun k => Multiplicative.ofAdd (c k))) = 1 := by
    rw [hcf, map_one]
  have hcK := twi1_ggTor_ker hm0 h3m w hw' hcomm (fun k => Multiplicative.ofAdd (c k)) hcf'
  have hcK' : ∀ j, ∑ k, (CartanMatrix.A 5 j k : ZMod 3) * c k = 0 := by
    intro j
    have := hcK j
    simpa only [Multiplicative.toAdd, Equiv.symm_apply_apply] using this
  have hcc := cartanA_ker_coord (p := 3) (N := 5) c hcK'
  have hc_eq : c = (c 0) • twi1_c0vec := by
    funext k
    have hk := hcc k.val k.isLt
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [twi1_c0vec_eq k, mul_comm]
    simpa using hk
  have hcd : (fun k => Multiplicative.ofAdd (c k)) = twi1_c0fun ^ (c 0).val := by
    funext k
    rw [Pi.pow_apply]
    have hk : c k = c 0 * twi1_c0vec k := by
      have := congrFun hc_eq k
      simpa only [Pi.smul_apply, smul_eq_mul] using this
    rw [hk]
    rw [show c 0 * twi1_c0vec k = (c 0).val • twi1_c0vec k by
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val]]
    rw [ofAdd_nsmul]
    simp only [twi1_c0fun]
  have hrel : P0 ^ (c 0).val = 1 := by
    have h := hcf
    rw [hcd, map_pow, ← hP0] at h
    exact h
  have hc0 : c 0 = 0 := by
    have hdvd : orderOf P0 ∣ (c 0).val := orderOf_dvd_iff_pow_eq_one.mpr hrel
    rw [hP0o] at hdvd
    have hlt : (c 0).val < 3 := by simpa using ZMod.val_lt (c 0)
    have hv : (c 0).val = 0 := by
      obtain ⟨q, hq⟩ := hdvd
      omega
    exact ZMod.val_injective (n := 3) (by simp [hv])
  have hc_zero : c = 0 := by
    rw [hc_eq, hc0]
    simp
  exact hc_zero

end CFSG.StandardType

end
