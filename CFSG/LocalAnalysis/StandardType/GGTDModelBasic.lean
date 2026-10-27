module

public import CFSG.LocalAnalysis.StandardType.GGTDModelDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Basic

variable {K : Type} [Field K] {N m : ℕ} {L' : Type} [Group L']

private def l48g1_pad (K : Type) [Field K] (N : ℕ) :
    (Fin (N + 1) → Kˣ) →* (Fin (N + 2) → Kˣ) where
  toFun f := Fin.cons 1 f
  map_one' := by funext i; cases i using Fin.cases <;> simp
  map_mul' f g := by funext i; cases i using Fin.cases <;> simp [Pi.mul_apply]

private lemma l48g1_range_comp_of_surjective {G N P : Type*} [Group G] [Group N] [Group P]
    (g : N →* P) (f : G →* N) (hf : Function.Surjective f) :
    (g.comp f).range = g.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hf]
  exact (MonoidHom.range_eq_map g).symm

private lemma l48g1_castSucc_ne_succ (k : Fin N) : k.castSucc ≠ k.succ := by
  intro h
  have := congrArg Fin.val h
  simp [Fin.val_castSucc, Fin.val_succ] at this

private lemma l48g1_pv_apply {K : Type} [Field K] (N : ℕ) (k : Fin N) (z : Kˣ)
    (i : Fin (N + 1)) :
    ggTDpvFun N k z i =
      (if i = k.castSucc then z else 1) * (if i = k.succ then z⁻¹ else 1) := by
  simp only [ggTDpvFun, Pi.mul_apply, Pi.mulSingle_apply]

private lemma l48g1_pad_pv {K : Type} [Field K] (N : ℕ) (k : Fin N) (z : Kˣ) :
    l48g1_pad K N (ggTDpvFun N k z) = ggTDpvFun (N + 1) k.succ z := by
  show Fin.cons 1 (ggTDpvFun N k z) = ggTDpvFun (N + 1) k.succ z
  funext i
  cases i using Fin.cases with
  | zero =>
      rw [Fin.cons_zero, l48g1_pv_apply, Fin.castSucc_succ]
      rw [if_neg (fun h => Fin.succ_ne_zero k.castSucc h.symm),
          if_neg (fun h => Fin.succ_ne_zero k.succ h.symm)]
      simp
  | succ i =>
      simp only [Fin.cons_succ, l48g1_pv_apply, Fin.castSucc_succ, Fin.succ_inj]

private lemma l48g1_telescope (μ : Subgroup Kˣ) :
    ∀ N : ℕ, ∀ s : ggTDTg μ N, ∃ f : Fin N → μ,
      (s : Fin (N + 1) → Kˣ) = ∏ k, ggTDpvFun N k (f k : Kˣ) := by
  intro N
  induction N with
  | zero =>
      intro s
      refine ⟨Fin.elim0, ?_⟩
      funext i
      fin_cases i
      have h := s.2.2
      simpa using h
  | succ N ih =>
      intro s
      let s0 : μ := ⟨(s : Fin (N + 2) → Kˣ) 0, s.2.1 0⟩
      let v0 : ggTDTg μ (N + 1) := ggTDpv μ (N + 1) 0 s0
      let w : Fin (N + 2) → Kˣ :=
        (v0 : Fin (N + 2) → Kˣ)⁻¹ * (s : Fin (N + 2) → Kˣ)
      have hv0 : (v0 : Fin (N + 2) → Kˣ) 0 = (s0 : Kˣ) := by
        show ggTDpvFun (N + 1) 0 (s0 : Kˣ) 0 = (s0 : Kˣ)
        rw [l48g1_pv_apply]
        simp
      have hw0 : w 0 = 1 := by
        show ((v0 : Fin (N + 2) → Kˣ) 0)⁻¹ * (s : Fin (N + 2) → Kˣ) 0 = 1
        rw [hv0]
        exact inv_mul_cancel (s0 : Kˣ)
      let t : ggTDTg μ N := ⟨Fin.tail w, by
        refine ⟨?_, ?_⟩
        · intro i
          change ((v0 : Fin (N + 2) → Kˣ) i.succ)⁻¹ * (s : Fin (N + 2) → Kˣ) i.succ ∈ μ
          exact μ.mul_mem (μ.inv_mem (v0.2.1 i.succ)) (s.2.1 i.succ)
        · have hprod : (∏ i : Fin (N + 2), w i) = 1 := by
            show (∏ i : Fin (N + 2),
              ((v0 : Fin (N + 2) → Kˣ) i)⁻¹ * (s : Fin (N + 2) → Kˣ) i) = 1
            rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, v0.2.2, s.2.2]
            simp
          show (∏ i : Fin (N + 1), w i.succ) = 1
          rw [Fin.prod_univ_succ, hw0, one_mul] at hprod
          exact hprod⟩
      obtain ⟨f, hf⟩ := ih t
      refine ⟨Fin.cases s0 f, ?_⟩
      have hsw : (s : Fin (N + 2) → Kˣ) =
          (v0 : Fin (N + 2) → Kˣ) * w := by
        show (s : Fin (N + 2) → Kˣ) =
          (v0 : Fin (N + 2) → Kˣ) *
            ((v0 : Fin (N + 2) → Kˣ)⁻¹ * (s : Fin (N + 2) → Kˣ))
        group
      rw [hsw]
      have hwt : w = l48g1_pad K N (t : Fin (N + 1) → Kˣ) := by
        show w = Fin.cons 1 (t : Fin (N + 1) → Kˣ)
        funext i
        cases i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact hw0
        | succ i => rw [Fin.cons_succ]; rfl
      rw [hwt, hf]
      rw [map_prod]
      simp_rw [l48g1_pad_pv]
      rw [Fin.prod_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ]
      rfl

theorem ggTDroot_of_act (M : GGTDModel K N m L') {a : MulAut L'} {t : Fin (N + 1) → Kˣ}
    (h : M.Act a t) (k : Fin N) :
    ggTDroot M k a = M.ι ⟨t k.castSucc / t k.succ, M.act_ratio_mem h _ _⟩ := by
  rw [ggTDroot, dif_pos ⟨t, h⟩]
  obtain ⟨c, hc⟩ := M.act_ratio (Classical.choose_spec ⟨t, h⟩) h
  congr 1
  apply Subtype.ext
  show (Classical.choose ⟨t, h⟩) k.castSucc / (Classical.choose ⟨t, h⟩) k.succ =
    t k.castSucc / t k.succ
  rw [hc k.castSucc, hc k.succ, div_eq_div_iff_mul_eq_mul]
  ac_rfl

theorem ggTDcor_apply (M : GGTDModel K N m L') (k : Fin N) (ζ : Multiplicative (ZMod m)) :
    ggTDcor M k ζ = M.φ (M.dgm (ggTDpv M.μ N k (M.ι.symm ζ))) := rfl

theorem ggTDTg_gen (μ : Subgroup Kˣ) (N : ℕ) : (⨆ k : Fin N, (ggTDpv μ N k).range) = ⊤ := by
  apply le_antisymm le_top
  intro s _
  obtain ⟨f, hf⟩ := l48g1_telescope μ N s
  have hsub : s = ∏ k, ggTDpv μ N k (f k) := by
    apply Subtype.ext
    simpa [Subgroup.val_finset_prod, ggTDpv] using hf
  rw [hsub]
  refine Subgroup.prod_mem _ (fun k _ => ?_)
  exact Subgroup.mem_iSup_of_mem k ⟨f k, rfl⟩

theorem ggTDTsc_le (M : GGTDModel K N m L') :
    (M.φ.comp M.dgm).range ≤ ⨆ k, (ggTDcor M k).range := by
  rw [MonoidHom.range_eq_map, ← ggTDTg_gen M.μ N, Subgroup.map_iSup]
  apply iSup_le; intro k
  rw [MonoidHom.map_range]
  have h1 : ((M.φ.comp M.dgm).comp (ggTDpv M.μ N k)).range = (ggTDcor M k).range := by
    rw [show ggTDcor M k =
      (M.φ.comp (M.dgm.comp (ggTDpv M.μ N k))).comp M.ι.symm.toMonoidHom from rfl]
    rw [l48g1_range_comp_of_surjective (M.φ.comp (M.dgm.comp (ggTDpv M.μ N k)))
      M.ι.symm.toMonoidHom M.ι.symm.surjective]
    rfl
  rw [h1]
  exact le_iSup (fun k => (ggTDcor M k).range) k

theorem ggTDzeta (M : GGTDModel K N m L') {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ∣ m)
    (hm : 0 < m) : ∃ ζ : Kˣ, ζ ∈ M.μ ∧ ζ ^ p = 1 ∧ ζ ≠ 1 ∧ ζ ≠ ζ⁻¹ := by
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
  have hple : p ≤ m := Nat.le_of_dvd hm hpm
  have hdivpos : 0 < m / p := Nat.div_pos hple hp.pos
  have hdiv : m / (m / p) = p := by
    nth_rewrite 1 [← Nat.div_mul_cancel hpm]
    exact Nat.mul_div_right p hdivpos
  let x : Multiplicative (ZMod m) := ggZetaP p m
  have horder : orderOf x = p := by
    change addOrderOf ((m / p : ℕ) : ZMod m) = p
    rw [ZMod.addOrderOf_coe (m / p) hm0, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpm)]
    exact hdiv
  have hxpow : x ^ p = 1 := by rw [← horder]; exact pow_orderOf_eq_one x
  have hxne : x ≠ 1 := by
    intro h
    exact hp.ne_one (by rw [← horder]; exact orderOf_eq_one_iff.mpr h)
  have hxinv : x ≠ x⁻¹ := by
    intro h
    have hx2 : x ^ 2 = 1 := by
      calc x ^ 2 = x * x := pow_two x
        _ = 1 := by nth_rewrite 1 [h]; exact inv_mul_cancel x
    have hp_dvd_2 : p ∣ 2 := by
      rw [← horder]
      exact orderOf_dvd_iff_pow_eq_one.mpr hx2
    have hple2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd_2
    have hp2le : 2 ≤ p := hp.two_le
    omega
  let z : M.μ := M.ι.symm x
  refine ⟨((z : M.μ) : Kˣ), z.2, ?_, ?_, ?_⟩
  · have hzpow : z ^ p = 1 := by
      have := congrArg M.ι.symm hxpow
      simpa using this
    show ((z : M.μ) : Kˣ) ^ p = 1
    rw [← Subgroup.coe_pow, hzpow, Subgroup.coe_one]
  · intro h
    apply hxne
    have hz1 : z = 1 := Subtype.coe_injective (by simpa using h)
    have h2 : M.ι z = 1 := by rw [hz1, map_one]
    simpa [z] using h2
  · intro h
    have hzinv : z = z⁻¹ := Subtype.coe_injective h
    have hxinv' : x = x⁻¹ := by
      have h2 := congrArg M.ι hzinv
      simp only [map_inv] at h2
      rwa [show M.ι z = x from M.ι.apply_symm_apply x] at h2
    exact hxinv hxinv'

theorem ggTDholdsOne (M : GGTDModel K N m L') {A : Subgroup (MulAut L')}
    (hN : ∀ σ, MulAut.conj (M.φ (M.Pm σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hAT : ∀ a ∈ A, ∃ t, M.Act a t) (hN2 : 2 ≤ N) :
    GGTDHoldsOne (ggTDwit M A hN) (CartanMatrix.A N) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    change ∃ t, M.Act x t at hx
    change ∃ t, M.Act y t at hy
    obtain ⟨t, ht⟩ := hx
    obtain ⟨u, hu⟩ := hy
    refine M.act_unique (M.act_mul ht hu) ?_
    have h : u * t = t * u := funext fun i => mul_comm _ _
    rw [← h]
    exact M.act_mul hu ht
  · intro a ha
    change ∃ t, M.Act a t
    exact hAT a ha
  · intro k ζ
    change MulAut.conj (ggTDcor M k ζ) ∈ ggTDT M
    rw [ggTDcor_apply M k ζ]
    change ∃ t, M.Act (MulAut.conj (M.φ (M.dgm (ggTDpv M.μ N k (M.ι.symm ζ))))) t
    exact ⟨_, M.act_dgm _⟩
  · intro j x hx y hy
    change ∃ t, M.Act x t at hx
    change ∃ t, M.Act y t at hy
    obtain ⟨t, ht⟩ := hx
    obtain ⟨u, hu⟩ := hy
    change ggTDroot M j (x * y) = ggTDroot M j x * ggTDroot M j y
    rw [ggTDroot_of_act M (M.act_mul ht hu) j, ggTDroot_of_act M ht j,
      ggTDroot_of_act M hu j, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Pi.mul_apply]
    exact mul_div_mul_comm _ _ _ _
  · intro k
    change Function.Injective (ggTDcor M k)
    intro ζ ξ h
    rw [ggTDcor_apply M k ζ, ggTDcor_apply M k ξ] at h
    let z : M.μ := M.ι.symm ζ
    let z' : M.μ := M.ι.symm ξ
    let G : M.μ →* L' := M.φ.comp (M.dgm.comp (ggTDpv M.μ N k))
    have hG : G z = G z' := by
      change M.φ (M.dgm (ggTDpv M.μ N k (M.ι.symm ζ))) =
        M.φ (M.dgm (ggTDpv M.μ N k (M.ι.symm ξ)))
      exact h
    have hw : M.φ (M.dgm (ggTDpv M.μ N k (z / z'))) = 1 := by
      change G (z / z') = 1
      rw [map_div, hG, div_eq_mul_inv, mul_inv_cancel]
    obtain ⟨c, hc⟩ := M.ker_dgm (ggTDpv M.μ N k (z / z')) hw
    obtain ⟨i, hi1, hi2⟩ : ∃ i : Fin (N + 1), i ≠ k.castSucc ∧ i ≠ k.succ := by
      rcases Nat.eq_zero_or_pos k.val with hk | hk
      · refine ⟨⟨2, by omega⟩, ?_, ?_⟩ <;>
          (simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega)
      · refine ⟨⟨0, by omega⟩, ?_, ?_⟩ <;>
          (simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega)
    have hci : ((ggTDpv M.μ N k (z / z') : Fin (N + 1) → Kˣ) i) = 1 := by
      show ggTDpvFun N k ((z / z' : M.μ) : Kˣ) i = 1
      rw [l48g1_pv_apply, if_neg hi1, if_neg hi2]
      simp
    have hc1 : c = 1 := by rw [← hc i, hci]
    have hz : ((ggTDpv M.μ N k (z / z') : Fin (N + 1) → Kˣ) k.castSucc) = (z / z' : Kˣ) := by
      show ggTDpvFun N k ((z / z' : M.μ) : Kˣ) k.castSucc = (z / z' : Kˣ)
      rw [l48g1_pv_apply, if_pos rfl, if_neg (l48g1_castSucc_ne_succ k)]
      simp
    have hzz : z / z' = 1 := by
      have : ((z / z' : M.μ) : Kˣ) = 1 := by
        rw [Subgroup.coe_div, ← hz, hc k.castSucc, hc1]
      exact Subtype.coe_injective (by simpa using this)
    have hz' : z = z' := div_eq_one.mp hzz
    rw [← M.ι.apply_symm_apply ζ, ← M.ι.apply_symm_apply ξ]
    exact congrArg M.ι hz'
  · intro j k ζ ξ
    change Commute (ggTDcor M j ζ) (ggTDcor M k ξ)
    rw [ggTDcor_apply M j ζ, ggTDcor_apply M k ξ]
    change (M.φ (M.dgm (ggTDpv M.μ N j (M.ι.symm ζ)))) *
        (M.φ (M.dgm (ggTDpv M.μ N k (M.ι.symm ξ)))) =
      (M.φ (M.dgm (ggTDpv M.μ N k (M.ι.symm ξ)))) *
        (M.φ (M.dgm (ggTDpv M.μ N j (M.ι.symm ζ))))
    simp only [← map_mul]
    rw [mul_comm]
  · intro τ hτ k ζ
    change ∃ t, M.Act τ t at hτ
    obtain ⟨t, ht⟩ := hτ
    change τ (ggTDcor M k ζ) = ggTDcor M k ζ
    rw [ggTDcor_apply M k ζ]
    exact M.act_fix ht (ggTDpv M.μ N k (M.ι.symm ζ))
  · intro i j ζ
    change ggTDroot M i (MulAut.conj (ggTDcor M j ζ)) = ζ ^ (CartanMatrix.A N) i j
    let z : M.μ := M.ι.symm ζ
    have hs : MulAut.conj (ggTDcor M j ζ) =
        MulAut.conj (M.φ (M.dgm (ggTDpv M.μ N j z))) := by
      rw [ggTDcor_apply M j ζ]
    rw [hs, ggTDroot_of_act M (M.act_dgm (ggTDpv M.μ N j z)) i]
    have hz : M.ι z = ζ := M.ι.apply_symm_apply ζ
    rw [← hz, ← map_zpow, M.ι.injective.eq_iff]
    apply Subtype.ext
    show ((ggTDpv M.μ N j z : ggTDTg M.μ N) : Fin (N + 1) → Kˣ) i.castSucc /
        ((ggTDpv M.μ N j z : ggTDTg M.μ N) : Fin (N + 1) → Kˣ) i.succ =
      ((z ^ (CartanMatrix.A N) i j : M.μ) : Kˣ)
    have hL : ((ggTDpv M.μ N j z : ggTDTg M.μ N) : Fin (N + 1) → Kˣ) i.castSucc /
        ((ggTDpv M.μ N j z : ggTDTg M.μ N) : Fin (N + 1) → Kˣ) i.succ =
        (if i = j then ((z : M.μ) : Kˣ) * ((z : M.μ) : Kˣ)
          else if i.val + 1 = j.val ∨ j.val + 1 = i.val then
            ((z : M.μ) : Kˣ)⁻¹ else 1) := by
      change ggTDpvFun N j ((z : M.μ) : Kˣ) i.castSucc /
        ggTDpvFun N j ((z : M.μ) : Kˣ) i.succ = _
      rw [l48g1_pv_apply N j ((z : M.μ) : Kˣ) i.castSucc,
        l48g1_pv_apply N j ((z : M.μ) : Kˣ) i.succ]
      simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> simp_all <;> (first | omega | group | rw [pow_two])
    rw [hL]
    have hA : (CartanMatrix.A N) i j =
        (if i = j then (2 : ℤ) else
          if i.val + 1 = j.val ∨ j.val + 1 = i.val then (-1 : ℤ) else 0) := by
      simp only [CartanMatrix.A, Matrix.of_apply]
    rw [hA]
    split_ifs <;> simp [pow_two]

end Basic

end CFSG.StandardType
