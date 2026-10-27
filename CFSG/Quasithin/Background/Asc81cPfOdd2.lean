module

public import CFSG.Quasithin.Background.Asc81cPfOdd1

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W]

section Arith

theorem eq_one_of_pow_add_one_eq_two_pow {p m n : ℕ} (hp : Odd p) (hp1 : 1 < p) (hm : 0 < m)
    (hn : 2 ≤ n) (h : p ^ m + 1 = 2 ^ n) : m = 1 := by
  have h4 : 2 ^ n % 4 = 0 := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    rw [pow_add]
    norm_num [Nat.mul_mod_left]
  have hmodd : Odd m := by
    by_contra hme
    rw [Nat.not_odd_iff_even] at hme
    obtain ⟨j, rfl⟩ := hme
    obtain ⟨t, ht⟩ := hp.pow (n := j)
    have h1 : p ^ (j + j) = 4 * (t * t + t) + 1 := by
      rw [← two_mul, pow_mul', ht]
      ring
    omega
  let S : ℤ := ∑ i ∈ Finset.range m, (-(p : ℤ)) ^ i
  have hS : S * ((p : ℤ) + 1) = (p : ℤ) ^ m + 1 := by
    have h1 := geom_sum_mul (-(p : ℤ)) m
    rw [hmodd.neg_pow] at h1
    linear_combination -h1
  have hSodd : S % 2 = 1 := by
    have h1 : S % 2 = (∑ i ∈ Finset.range m, (-(p : ℤ)) ^ i % 2) % 2 :=
      Finset.sum_int_mod _ _ _
    have h2 : ∀ i ∈ Finset.range m, (-(p : ℤ)) ^ i % 2 = 1 := fun i _ =>
      Int.odd_iff.1 ((Int.odd_coe_nat p |>.2 hp).neg.pow)
    rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact Int.odd_iff.1 (Int.odd_coe_nat m |>.2 hmodd)
  have hSpos : 0 < S := by
    have h1 : (0 : ℤ) < (p : ℤ) ^ m + 1 := by positivity
    rw [← hS] at h1
    exact pos_of_mul_pos_left h1 (by positivity)
  obtain ⟨s, hs⟩ : ∃ s : ℕ, S = s := ⟨S.toNat, (Int.toNat_of_nonneg hSpos.le).symm⟩
  rw [hs] at hS hSodd
  have hsdvd : s ∣ 2 ^ n := by
    rw [← h]
    exact ⟨p + 1, by exact_mod_cast hS.symm⟩
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hsdvd
  have he0 : e = 0 := by
    by_contra he0
    have h1 : (2 : ℤ) ∣ (s : ℤ) := by
      rw [he]
      exact_mod_cast dvd_pow_self 2 he0
    omega
  rw [he0, pow_zero] at he
  rw [he, Nat.cast_one, one_mul] at hS
  have h1 : p ^ m = p ^ 1 := by
    rw [pow_one]
    exact_mod_cast (by linarith : ((p : ℤ) ^ m) = p)
  exact Nat.pow_right_injective hp1 h1

end Arith

section Free

variable [Finite W]

theorem card_dvd_of_free {R : Subgroup (MulAut W)} (S : Finset W)
    (hS : ∀ r ∈ R, ∀ v ∈ S, r v ∈ S) (hfree : ∀ r ∈ R, ∀ v ∈ S, r v = v → r = 1) :
    Nat.card R ∣ S.card := by
  classical
  have := finite_mulAut (W := W)
  have : Fintype (MulAut W) := Fintype.ofFinite _
  let Rf : Finset (MulAut W) := (R : Set (MulAut W)).toFinset
  let o : W → Finset W := fun v => Rf.image fun r => r v
  have hRf : ∀ r, r ∈ Rf ↔ r ∈ R := fun r => by simp [Rf]
  have hcardR : Rf.card = Nat.card R := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    rfl
  have hcardo : ∀ v ∈ S, (o v).card = Nat.card R := by
    intro v hv
    rw [Finset.card_image_of_injOn, hcardR]
    intro r hr r' hr' hrr
    have h1 : (r'⁻¹ * r) v = v := by
      rw [MulAut.mul_apply, show r v = r' v from hrr, MulAut.inv_apply_self]
    have h2 := hfree _ (R.mul_mem (R.inv_mem ((hRf r').1 hr')) ((hRf r).1 hr)) v hv h1
    rw [inv_mul_eq_one] at h2
    exact h2.symm
  have hmem : ∀ v w, w ∈ o v → o w = o v := by
    intro v w hw
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hw
    ext u
    simp only [o, Finset.mem_image]
    constructor
    · rintro ⟨r', hr', rfl⟩
      exact ⟨r' * r, (hRf _).2 (R.mul_mem ((hRf r').1 hr') ((hRf r).1 hr)), rfl⟩
    · rintro ⟨r', hr', rfl⟩
      refine ⟨r' * r⁻¹, (hRf _).2 (R.mul_mem ((hRf r').1 hr') (R.inv_mem ((hRf r).1 hr))), ?_⟩
      rw [MulAut.mul_apply, MulAut.inv_apply_self]
  have hself : ∀ v, v ∈ o v := fun v =>
    Finset.mem_image.2 ⟨1, (hRf 1).2 R.one_mem, rfl⟩
  have hfib := Finset.card_eq_sum_card_fiberwise (f := o) (t := S.image o)
    (fun v hv => Finset.mem_image_of_mem o hv)
  rw [hfib]
  refine Finset.dvd_sum fun b hb => ?_
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb
  have h1 : S.filter (fun w => o w = o v) = o v := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨-, hw⟩
      rw [← hw]
      exact hself w
    · intro hw
      refine ⟨?_, hmem v w hw⟩
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hw
      exact hS r ((hRf r).1 hr) v hv
  rw [h1, hcardo v hv]

end Free

section Spread

variable [Finite W] {G : Subgroup (MulAut W)} {Ω : Set (Subgroup (MulAut W))}
  {X₀ Y₀ : Subgroup (MulAut W)}

theorem TransSetting.card_oddU_eq (hT : TransSetting G Ω) (hX₀ : X₀ ∈ Ω)
    {Z : Subgroup (MulAut W)} (hZ : Z ∈ Ω) : Nat.card (oddU G Z) = Nat.card (oddU G X₀) := by
  obtain ⟨g, hg, rfl⟩ := hT.trans X₀ hX₀ Z hZ
  refine le_antisymm ?_ ?_
  · refine Nat.card_le_card_of_injective (fun u => (⟨g⁻¹ u.1, ?_⟩ : oddU G X₀)) ?_
    · have h1 := oddU_map_conj (G.inv_mem hg) u.2
      rwa [map_conj_map_conj, inv_mul_cancel, map_conj_one] at h1
    · intro a b hab
      exact Subtype.ext (g⁻¹.injective (congrArg Subtype.val hab :))
  · refine Nat.card_le_card_of_injective (fun u => (⟨g u.1, oddU_map_conj hg u.2⟩ :
      oddU G (X₀.map (MulAut.conj g).toMonoidHom))) ?_
    intro a b hab
    exact Subtype.ext (g.injective (congrArg Subtype.val hab :))

theorem TransSetting.card_union_oddU (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) (hodd : Odd (Nat.card G)) :
    ∃ T : Finset W, (∀ v ∈ T, v ∈ commSub (⊤ : Subgroup W) G ∧ v ≠ 1) ∧
      (∀ v ∈ T, ∃ Z ∈ Ω, v ∈ oddU G Z) ∧
      T.card = Ω.ncard * (Nat.card (oddU G X₀) - 1) := by
  classical
  have hfin := finite_subgroups (W := W)
  have : Fintype W := Fintype.ofFinite W
  have hΩfin : Ω.Finite := Set.toFinite Ω
  let S : Subgroup (MulAut W) → Finset W := fun Z => ((oddU G Z : Set W) \ {1}).toFinset
  have hSd : (hΩfin.toFinset : Set (Subgroup (MulAut W))).PairwiseDisjoint S := by
    intro Z hZ Z' hZ' hZZ'
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    simp only [S, Set.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe,
      Set.mem_singleton_iff] at hw hw'
    have h1 : w ∈ oddU G Z ⊓ oddU G Z' := ⟨hw.1, hw'.1⟩
    rw [hT.oddU_inf_eq_bot hW hX₀ hY₀ hnc hodd (hΩfin.mem_toFinset.1 hZ)
      (hΩfin.mem_toFinset.1 hZ') hZZ'] at h1
    exact hw.2 h1
  refine ⟨hΩfin.toFinset.biUnion S, ?_, ?_, ?_⟩
  · intro v hv
    simp only [Finset.mem_biUnion, S, Set.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe,
      Set.mem_singleton_iff] at hv
    obtain ⟨Z, -, hv1, hv2⟩ := hv
    exact ⟨hv1.2, hv2⟩
  · intro v hv
    simp only [Finset.mem_biUnion, S, Set.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe,
      Set.mem_singleton_iff] at hv
    obtain ⟨Z, hZ, hv1, -⟩ := hv
    exact ⟨Z, hΩfin.mem_toFinset.1 hZ, hv1⟩
  · rw [Finset.card_biUnion hSd]
    have hS : ∀ Z ∈ hΩfin.toFinset, (S Z).card = Nat.card (oddU G X₀) - 1 := by
      intro Z hZ
      simp only [S]
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, card_diff_one,
        hT.card_oddU_eq hX₀ (hΩfin.mem_toFinset.1 hZ)]
    rw [Finset.sum_congr rfl hS, Finset.sum_const, smul_eq_mul,
      ← Set.ncard_eq_toFinset_card Ω hΩfin]

theorem TransSetting.card_oddU_eq_two (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) (hodd : Odd (Nat.card G))
    (hk : 7 ≤ Nat.card X₀) :
    Nat.card (oddU G X₀) = 2 ∧ Ω.ncard + 1 = Nat.card (commSub (⊤ : Subgroup W) G) := by
  classical
  have hfin := finite_subgroups (W := W)
  have hXh := (hT.hyp X₀ hX₀).1
  have hXY : X₀ ≠ Y₀ := fun h => hnc (h ▸ commutes_self_of_isCyclic hXh.2.2.1)
  have horb : ∀ K ∈ Ω, K ≠ X₀ → ∀ x ∈ X₀, K.map (MulAut.conj x).toMonoidHom ≠ X₀ := by
    intro K hK hKX x hx h
    apply hKX
    have h1 : X₀.map (MulAut.conj x).toMonoidHom = X₀ :=
      map_conj_eq_of_commutes fun z hz => mul_comm_of_isCyclic hXh.2.2.1 hx hz
    rw [← h1] at h
    exact map_conj_injective x h
  obtain ⟨K₂, hK₂, hK₂X, hK₂o⟩ : ∃ K ∈ Ω, K ≠ X₀ ∧
      ∀ x ∈ X₀, K ≠ Y₀.map (MulAut.conj x).toMonoidHom := by
    by_contra hall
    push Not at hall
    obtain ⟨g, hg, hgY⟩ := hT.trans Y₀ hY₀ X₀ hX₀
    have hK' : X₀.map (MulAut.conj g).toMonoidHom ∈ Ω := hT.inv g hg X₀ hX₀
    have hK'X : X₀.map (MulAut.conj g).toMonoidHom ≠ X₀ := by
      intro h
      apply hXY.symm
      apply map_conj_injective g
      show Y₀.map (MulAut.conj g).toMonoidHom = X₀.map (MulAut.conj g).toMonoidHom
      rw [← hgY, h]
    obtain ⟨y, hy, hyK⟩ := hall _ hK' hK'X
    have hyX : X₀.map (MulAut.conj y⁻¹).toMonoidHom = X₀ :=
      map_conj_eq_of_commutes fun z hz => mul_comm_of_isCyclic hXh.2.2.1 (X₀.inv_mem hy) hz
    refine no_swap hodd (G.mul_mem (G.inv_mem (hXh.1 hy)) hg) hXY.symm ?_ ?_
    · rw [← map_conj_map_conj, ← hgY, hyX]
    · rw [← map_conj_map_conj, hyK, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  have hinj : ∀ K ∈ Ω, K ≠ X₀ → Set.InjOn (fun x => K.map (MulAut.conj x).toMonoidHom)
      (X₀ : Set (MulAut W)) := by
    intro K hK hKX x hx x' hx' h
    have h1 : K.map (MulAut.conj (x'⁻¹ * x)).toMonoidHom = K := by
      rw [← map_conj_map_conj]
      show (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x'⁻¹).toMonoidHom = K
      rw [show K.map (MulAut.conj x).toMonoidHom = K.map (MulAut.conj x').toMonoidHom from h,
        map_conj_map_conj, inv_mul_cancel, map_conj_one]
    have h2 := hT.semiregular hW hX₀ hY₀ hnc hodd hX₀ hK hKX (X₀.mul_mem (X₀.inv_mem hx') hx) h1
    rw [inv_mul_eq_one] at h2
    exact h2.symm
  let O₁ := (fun x => Y₀.map (MulAut.conj x).toMonoidHom) '' (X₀ : Set (MulAut W))
  let O₂ := (fun x => K₂.map (MulAut.conj x).toMonoidHom) '' (X₀ : Set (MulAut W))
  have hO₁ : O₁ ⊆ Ω \ {X₀} := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hT.inv x (hXh.1 hx) Y₀ hY₀, horb Y₀ hY₀ (Ne.symm hXY) x hx⟩
  have hO₂ : O₂ ⊆ Ω \ {X₀} := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hT.inv x (hXh.1 hx) K₂ hK₂, horb K₂ hK₂ hK₂X x hx⟩
  have hdisj : Disjoint O₁ O₂ := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', h⟩
    have h' : K₂.map (MulAut.conj x').toMonoidHom = Y₀.map (MulAut.conj x).toMonoidHom := h
    have hc : x'⁻¹ * x = x * x'⁻¹ := mul_comm_of_isCyclic hXh.2.2.1 (X₀.inv_mem hx') hx
    apply hK₂o (x * x'⁻¹) (X₀.mul_mem hx (X₀.inv_mem hx'))
    calc K₂ = (K₂.map (MulAut.conj x').toMonoidHom).map (MulAut.conj x'⁻¹).toMonoidHom := by
          rw [map_conj_map_conj, inv_mul_cancel, map_conj_one]
      _ = (Y₀.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x'⁻¹).toMonoidHom := by rw [h']
      _ = Y₀.map (MulAut.conj (x'⁻¹ * x)).toMonoidHom := map_conj_map_conj _ _ _
      _ = _ := by rw [hc]
  have hΩ : 2 * Nat.card X₀ + 1 ≤ Ω.ncard := by
    have h1 := Set.ncard_le_ncard (Set.union_subset hO₁ hO₂) (Set.toFinite _)
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      (hinj Y₀ hY₀ (Ne.symm hXY)).ncard_image,
      (hinj K₂ hK₂ hK₂X).ncard_image, ← Nat.card_coe_set_eq,
      Set.ncard_sdiff_singleton_of_mem hX₀] at h1
    have h2 : 0 < Ω.ncard := Set.ncard_pos (Set.toFinite Ω) |>.2 ⟨X₀, hX₀⟩
    have h3 : Nat.card (X₀ : Set (MulAut W)) = Nat.card X₀ := rfl
    omega
  obtain ⟨T, hT1, -, hT3⟩ := hT.card_union_oddU hW hX₀ hY₀ hnc hodd
  have hTle : T.card + 1 ≤ Nat.card (commSub (⊤ : Subgroup W) G) := by
    have : Fintype W := Fintype.ofFinite W
    have hsub : T ⊆ ((commSub (⊤ : Subgroup W) G : Set W) \ {1}).toFinset := by
      intro v hv
      simp only [Set.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
      exact hT1 v hv
    have h1 := Finset.card_le_card hsub
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, card_diff_one] at h1
    have h2 : 0 < Nat.card (commSub (⊤ : Subgroup W) G) := Nat.card_pos
    omega
  have hV₀ := card_commSub_G_eq hW hodd hXh.1 hXh.2.2.2.1
  have hq := card_commSub hXh
  have hD2 : 2 ≤ Nat.card (oddU G X₀) := by
    have h1 := hT.oddU_ne_bot hW hX₀ hY₀ hnc hodd hX₀
    have h2 := (Subgroup.one_lt_card_iff_ne_bot _).2 h1
    omega
  set D := Nat.card (oddU G X₀)
  set h := Nat.card X₀
  rw [hV₀, hq, hT3] at hTle
  have hD : D = 2 := by
    by_contra hD
    have hD3 : 3 ≤ D := by omega
    have h1 : (2 * h + 1) * (D - 1) ≤ Ω.ncard * (D - 1) := Nat.mul_le_mul_right _ hΩ
    have h2 : (2 * h + 1) * (D - 1) + 1 ≤ D * (h + 1) := le_trans (by omega) hTle
    obtain ⟨E, hE⟩ : ∃ E, D = E + 1 := ⟨D - 1, by omega⟩
    rw [hE, Nat.add_sub_cancel] at h2
    have h3 : h * E ≤ h * 1 := by nlinarith
    have h4 := Nat.le_of_mul_le_mul_left h3 (by omega)
    omega
  refine ⟨hD, ?_⟩
  rw [hD] at hTle
  rw [hV₀, hq, hD]
  omega

theorem TransSetting.exists_oddU (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) (hodd : Odd (Nat.card G))
    (hk : 7 ≤ Nat.card X₀) {v : W} (hv : v ∈ commSub (⊤ : Subgroup W) G) (hv1 : v ≠ 1) :
    ∃ Z ∈ Ω, v ∈ oddU G Z := by
  classical
  have : Fintype W := Fintype.ofFinite W
  obtain ⟨hD, hΩ⟩ := hT.card_oddU_eq_two hW hX₀ hY₀ hnc hodd hk
  obtain ⟨T, hT1, hT2, hT3⟩ := hT.card_union_oddU hW hX₀ hY₀ hnc hodd
  have hsub : T ⊆ ((commSub (⊤ : Subgroup W) G : Set W) \ {1}).toFinset := by
    intro w hw
    simp only [Set.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
    exact hT1 w hw
  have hcard : ((commSub (⊤ : Subgroup W) G : Set W) \ {1}).toFinset.card ≤ T.card := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, card_diff_one, hT3, hD]
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hvT : v ∈ T := by
    rw [heq]
    simp only [Set.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
    exact ⟨hv, hv1⟩
  exact hT2 v hvT

end Spread

end Pf

end Asc81c

end CFSG.Quasithin
