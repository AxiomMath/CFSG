module

public import CFSG.RankThree.PartOne.KF.D4Torus
public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {p f : ℕ} {K : Type} [Field K] {σ : K →+* K}

structure D4Param (p f : ℕ) (K : Type) [Field K] (σ : K →+* K) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  one_le : 1 ≤ f
  card : Nat.card K = (2 ^ f) ^ 3
  frob : ∀ c, σ c = c ^ 2 ^ f
  dvd : p ∣ 2 ^ f - 1

namespace D4Param

variable (h : D4Param p f K σ)

include h in
theorem finite : Finite K := Nat.finite_of_card_ne_zero (by rw [h.card]; positivity)

include h in
theorem ringChar_eq_two : ringChar K = 2 := by
  have := h.finite
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have := CharP.addOrderOf_one K
  have h0 : ringChar K = addOrderOf (1 : K) := ringChar.eq K (addOrderOf (1 : K))
  have h1 : ringChar K ∣ Nat.card K := h0 ▸ addOrderOf_dvd_natCard (1 : K)
  rw [h.card, ← pow_mul] at h1
  have h2 := Nat.Prime.dvd_of_dvd_pow (Fact.out : (ringChar K).Prime) h1
  exact (Nat.prime_dvd_prime_iff_eq (Fact.out : (ringChar K).Prime) Nat.prime_two).1 h2

include h in
theorem sigma_cube (c : K) : σ (σ (σ c)) = c := by
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  rw [h.frob, h.frob, h.frob, ← pow_mul, ← pow_mul,
    show 2 ^ f * (2 ^ f * 2 ^ f) = Fintype.card K by
      rw [← Nat.card_eq_fintype_card, h.card]; ring]
  exact FiniteField.pow_card c

include h in
theorem sigma_fix (x : Kˣ) (hx : x ^ p = 1) : σ (x : K) = x := by
  obtain ⟨m, hm⟩ := h.dvd
  have h1 : x ^ (2 ^ f - 1) = 1 := by rw [hm, pow_mul, hx, one_pow]
  have h2 : x ^ 2 ^ f = x := by
    have : 2 ^ f = (2 ^ f - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_two_pow)).symm
    rw [this, pow_succ, h1, one_mul]
  rw [h.frob, ← Units.val_pow_eq_pow_val, h2]

end D4Param

theorem d4Tuple_mul (x y x' y' : Kˣ) :
    d4Tuple (x * x') (y * y') = d4Tuple x y * d4Tuple x' y' := by
  funext j
  by_cases h : j = d4i2 <;> simp [d4Tuple, h]

theorem d4Tuple_one' : d4Tuple (1 : Kˣ) 1 = 1 := by
  funext j
  by_cases h : j = d4i2 <;> simp [d4Tuple, h]

variable (p K) in
@[expose] noncomputable def tp3Hom : (Fin 2 → rootsOfUnity p K) →* ModGL TwistTag.D4.tag K where
  toFun b := rootDiagUnit TwistTag.D4.tag
    (d4Tuple ((b 1 : rootsOfUnity p K) : Kˣ) ((b 0 : rootsOfUnity p K) : Kˣ))
  map_one' := by
    show rootDiagUnit TwistTag.D4.tag (d4Tuple 1 1) = 1
    rw [d4Tuple_one', rootDiagUnit_one]
  map_mul' b b' := by
    show rootDiagUnit TwistTag.D4.tag (d4Tuple ((b 1 * b' 1 : rootsOfUnity p K) : Kˣ)
      ((b 0 * b' 0 : rootsOfUnity p K) : Kˣ)) = _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, d4Tuple_mul, rootDiagUnit_mul]

theorem tp3Hom_apply (b : Fin 2 → rootsOfUnity p K) :
    tp3Hom p K b = rootDiagUnit TwistTag.D4.tag
      (d4Tuple ((b 1 : rootsOfUnity p K) : Kˣ) ((b 0 : rootsOfUnity p K) : Kˣ)) := rfl

theorem tp3Hom_injective :
    Function.Injective (tp3Hom p K) := by
  intro b b' hb
  have hb' := rootDiagUnit_injective hb
  have h2 := congrFun hb' d4i2
  have h0 := congrFun hb' d4i0
  rw [d4Tuple_two, d4Tuple_two] at h2
  rw [d4Tuple_zero, d4Tuple_zero] at h0
  funext i
  fin_cases i
  · exact Subtype.ext h2
  · exact Subtype.ext h0

theorem tp3Hom_mem_torusGroup
    [Finite K] (hchar : ringChar K = 2) (b : Fin 2 → rootsOfUnity p K) :
    tp3Hom p K b ∈ torusGroup TwistTag.D4.tag K :=
  (even_power_two_Cartan_root_diagonals_inner TwistTag.D4.tag (Or.inr (Or.inr (Or.inl rfl))) K
    hchar).1 _

theorem mem_adjointGroup_of_mem_torusGroup
    {τ : Tag} {t : ModGL τ K} (ht : t ∈ torusGroup τ K) :
    t ∈ adjointGroup τ K := by
  have hle : torusGroup τ K ≤ adjointGroup τ K := by
    rw [torusGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, u⟩, rfl⟩
    exact torusElt_mem_adjointGroup i u
  exact hle ht

theorem d4Tuple_perm (x y : Kˣ) (j : Fin TwistTag.D4.tag.rank) :
    d4Tuple x y (TwistTag.D4.perm j) = d4Tuple x y j := by
  obtain ⟨h0, h1, h3, h2⟩ := perm_D4_values
  rcases fin_D4_cases j with rfl | rfl | rfl | rfl
  · rw [h0, d4Tuple_zero, d4Tuple_one]
  · rw [h1, d4Tuple_one, d4Tuple_three]
  · rw [h2]
  · rw [h3, d4Tuple_three, d4Tuple_zero]

theorem d4Tuple_perm_symm (x y : Kˣ) (i : Fin TwistTag.D4.tag.rank) :
    d4Tuple x y (TwistTag.D4.perm.symm i) = d4Tuple x y i := by
  have h := d4Tuple_perm x y (TwistTag.D4.perm.symm i)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

namespace D4Param

variable (h : D4Param p f K σ)

include h in
theorem twistHom_tp3Hom
    (b : Fin 2 → rootsOfUnity p K) :
    twistHom TwistTag.D4 K σ (tp3Hom p K b) = tp3Hom p K b := by
  rw [tp3Hom_apply, twistHom_rootDiagUnit_eq]
  congr 1
  funext i
  have hx : Units.map σ.toMonoidHom ((b 1 : rootsOfUnity p K) : Kˣ) = (b 1 : rootsOfUnity p K) :=
    Units.ext (h.sigma_fix _ ((mem_rootsOfUnity p _).mp (b 1).2))
  have hy : Units.map σ.toMonoidHom ((b 0 : rootsOfUnity p K) : Kˣ) = (b 0 : rootsOfUnity p K) :=
    Units.ext (h.sigma_fix _ ((mem_rootsOfUnity p _).mp (b 0).2))
  rw [d4Tuple_perm_symm]
  rcases fin_D4_cases i with rfl | rfl | rfl | rfl
  · rw [d4Tuple_zero]
    exact hx
  · rw [d4Tuple_one]
    exact hx
  · rw [d4Tuple_two]
    exact hy
  · rw [d4Tuple_three]
    exact hx

include h in
theorem twistedFixedGroup_eq :
    twistedFixedGroup TwistTag.D4 K σ = graphFixedRootGroup TwistTag.D4 K σ := by
  have := h.finite
  let σE : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσE : σE.toRingHom = σ := RingHom.ext fun _ => rfl
  have h1 := (even_triality_fixed_group_eq_root_group K h.ringChar_eq_two σE
    (fun c => h.sigma_cube c)).1
  rwa [hσE] at h1

include h in
theorem tp3Hom_mem_graphFixedRootGroup
    (b : Fin 2 → rootsOfUnity p K) :
    tp3Hom p K b ∈ graphFixedRootGroup TwistTag.D4 K σ := by
  have := h.finite
  rw [← h.twistedFixedGroup_eq]
  exact (mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ).2
    ⟨mem_adjointGroup_of_mem_torusGroup (tp3Hom_mem_torusGroup h.ringChar_eq_two b),
      h.twistHom_tp3Hom b⟩

end D4Param

@[expose] noncomputable def tp3M
    (h : D4Param p f K σ) :
    (Fin 2 → rootsOfUnity p K) →* ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
  (tp3Hom p K).codRestrict _ h.tp3Hom_mem_graphFixedRootGroup

@[expose] noncomputable def Tp3
    (h : D4Param p f K σ) :
    Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
  (tp3M h).range

section Tp3

variable (h : D4Param p f K σ)

theorem coe_tp3M
    (b : Fin 2 → rootsOfUnity p K) :
    ((tp3M h b : ↥(graphFixedRootGroup TwistTag.D4 K σ)) : ModGL TwistTag.D4.tag K) =
      tp3Hom p K b := rfl

theorem tp3M_injective
    : Function.Injective (tp3M h) := fun _ _ hh =>
  tp3Hom_injective (congrArg Subtype.val hh)

theorem tp3M_mem_Tp3
    (b : Fin 2 → rootsOfUnity p K) : tp3M h b ∈ Tp3 h := ⟨b, rfl⟩

theorem Tp3_comm
    (s t : ↥(graphFixedRootGroup TwistTag.D4 K σ)) (hs : s ∈ Tp3 h)
    (ht : t ∈ Tp3 h) : s * t = t * s := by
  obtain ⟨b, rfl⟩ := hs
  obtain ⟨b', rfl⟩ := ht
  rw [← map_mul, ← map_mul, mul_comm]

theorem Tp3_exp
    (t : ↥(graphFixedRootGroup TwistTag.D4 K σ)) (ht : t ∈ Tp3 h) : t ^ p = 1 := by
  obtain ⟨b, rfl⟩ := ht
  rw [← map_pow]
  have : b ^ p = 1 := funext fun i => Subtype.ext (by
    simpa using (mem_rootsOfUnity p _).mp (b i).2)
  rw [this, map_one]

end Tp3

theorem mem_Tp3_of_mem_graphFixedRootTorus
    (h : D4Param p f K σ)
    {t : ↥(graphFixedRootGroup TwistTag.D4 K σ)}
    (ht : (t : ModGL TwistTag.D4.tag K) ∈ graphFixedRootTorus TwistTag.D4 K σ)
    (htp : t ^ p = 1) : t ∈ Tp3 h := by
  have := h.finite
  obtain ⟨hT, hΓ⟩ := Subgroup.mem_inf.1 (Subgroup.mem_inf.1 ht).1
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hfix : twistHom TwistTag.D4 K σ (rootDiagUnit TwistTag.D4.tag l) =
      rootDiagUnit TwistTag.D4.tag l := by
    rw [← hl]
    exact ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ).1 hΓ).2
  have hcompat := compat_of_twistHom_rootDiagUnit hfix
  have hlp : l ^ p = 1 := by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := K)
    have h1 : rootDiagUnit TwistTag.D4.tag (l ^ p) = rootDiagUnit TwistTag.D4.tag l ^ p :=
      map_pow (rootDiagUnitHom TwistTag.D4.tag K) l p
    rw [h1, ← hl, rootDiagUnit_one]
    exact congrArg Subtype.val htp
  have hlpi : ∀ i, l i ^ p = 1 := fun i => by simpa using congrFun hlp i
  have hmem : ∀ i, l i ∈ rootsOfUnity p K := fun i => (mem_rootsOfUnity p _).mpr (hlpi i)
  have hσl : ∀ i, Units.map σ.toMonoidHom (l i) = l i := fun i =>
    Units.ext (h.sigma_fix (l i) (hlpi i))
  obtain ⟨e01, e13, e30, -⟩ := perm_D4_values
  have hl1 : l d4i1 = l d4i0 := by
    have := hcompat d4i0
    rwa [e01, hσl] at this
  have hl3 : l d4i3 = l d4i0 := by
    have := hcompat d4i1
    rwa [e13, hσl, hl1] at this
  refine ⟨![⟨l d4i2, hmem _⟩, ⟨l d4i0, hmem _⟩], Subtype.ext ?_⟩
  rw [coe_tp3M, hl, tp3Hom_apply]
  congr 1
  funext i
  rcases fin_D4_cases i with rfl | rfl | rfl | rfl
  · exact d4Tuple_zero _ _
  · rw [d4Tuple_one]
    exact hl1.symm
  · exact d4Tuple_two _ _
  · rw [d4Tuple_three]
    exact hl3.symm

theorem not_dvd_triality_index {p q idx : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hq : 2 ≤ q)
    (hdvd : p ∣ q - 1)
    (hmul : (q ^ 3 - 1) * (q - 1) * idx =
      q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)) : ¬ p ∣ idx := by
  intro hpi
  have hq1 : 1 ≤ q := by omega
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
  have hz : (((q : ℤ) ^ 3 - 1) * ((q : ℤ) - 1)) * (idx : ℤ) =
      (q : ℤ) ^ 12 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 6 - 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hmul
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] at this
    rw [Nat.cast_sub h3, Nat.cast_sub hq1, Nat.cast_sub h1, Nat.cast_sub h6] at this
    simpa using this
  have hne : ((q : ℤ) ^ 3 - 1) * ((q : ℤ) - 1) ≠ 0 := by
    have hq2' : (2 : ℤ) ≤ q := by exact_mod_cast hq
    have a1 : (q : ℤ) - 1 > 0 := by linarith
    have a2 : (q : ℤ) ^ 3 - 1 > 0 := by nlinarith [sq_nonneg ((q : ℤ)), sq_nonneg ((q : ℤ) - 1)]
    exact (mul_pos a2 a1).ne'
  have hidx : (idx : ℤ) = (q : ℤ) ^ 12 * ((q : ℤ) + 1) * ((q : ℤ) ^ 3 + 1) *
      ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) := by
    have h0 : (((q : ℤ) ^ 3 - 1) * ((q : ℤ) - 1)) * ((idx : ℤ) - (q : ℤ) ^ 12 * ((q : ℤ) + 1) *
        ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1)) = 0 := by
      linear_combination hz
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hne
    · linarith
  have hqp : ((q : ℕ) : ZMod p) = 1 := by
    have h0 : ((q - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    rw [Nat.cast_sub hq1] at h0
    simpa [sub_eq_zero] using h0
  have hz' : ((idx : ℕ) : ZMod p) = 12 := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) hidx
    simp only [Int.cast_natCast, Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_one] at this
    rw [this, hqp]
    norm_num
  have h0 : ((idx : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpi
  rw [h0] at hz'
  have h12 : p ∣ 12 := by
    have : (((12 : ℕ)) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hz'.symm
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) h12
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem not_dvd_index_graphFixedRootTorus
    (h : D4Param p f K σ) :
    ¬ p ∣ ((graphFixedRootTorus TwistTag.D4 K σ).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ)).index := by
  have := h.finite
  have hq2 : 2 ≤ 2 ^ f := by
    have : 2 ^ 1 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
    simpa using this
  obtain ⟨hC, hH, -⟩ := triality_both_orientations_exact_finite_order 2 f Nat.prime_two h.one_le K
    h.card 1 (Or.inl rfl) σ (fun c => by rw [pow_one]; exact h.frob c)
  have hle : graphFixedRootTorus TwistTag.D4 K σ ≤ graphFixedRootGroup TwistTag.D4 K σ :=
    inf_le_right
  have hcardH : Nat.card ((graphFixedRootTorus TwistTag.D4 K σ).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ)) = Nat.card (graphFixedRootTorus TwistTag.D4 K σ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hmul := Subgroup.card_mul_index ((graphFixedRootTorus TwistTag.D4 K σ).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ))
  rw [hcardH, hH, hC] at hmul
  exact not_dvd_triality_index h.prime h.five_le hq2 h.dvd hmul

theorem exists_conj_into_Tp3
    (h : D4Param p f K σ) (X : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ))
    (hX : ∀ x ∈ X, x ^ p = 1) : ∃ g : ↥(graphFixedRootGroup TwistTag.D4 K σ),
      ∀ x ∈ X, g * x * g⁻¹ ∈ Tp3 h := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hP : IsPGroup p X := fun x => ⟨1, Subtype.ext (by simpa using hX x.1 x.2)⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.Chevalley.exists_conj_map_le_of_not_dvd_index
    (not_dvd_index_graphFixedRootTorus h) hP
  refine ⟨g, fun x hx => ?_⟩
  have h1 : g * x * g⁻¹ ∈ (graphFixedRootTorus TwistTag.D4 K σ).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ) := hg ⟨x, hx, rfl⟩
  refine mem_Tp3_of_mem_graphFixedRootTorus h (Subgroup.mem_subgroupOf.mp h1) ?_
  have : (g * x * g⁻¹) ^ p = g * x ^ p * g⁻¹ := conj_pow
  rw [this, hX x hx, mul_one, mul_inv_cancel]

end CFSG.RankThree.PartOne.KFU
