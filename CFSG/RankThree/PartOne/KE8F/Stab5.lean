module

public import CFSG.RankThree.PartOne.KE8F.Stab5Fix
public import CFSG.RankThree.PartOne.KE8F.BaseCase
public import Certificates.Certificate14974

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice RootSpace
open CFSG.RankThree.E6 (charVal charVal_single charVal_mulVec charVal_smul charVal_smul_col
  eq_of_charVal_single weylMatrix)
open CFSG.RankThree.PartOne.KE (rootKernel dualWeylStabilizer mem_dualWeylStabilizer
  fixedCharTuples rootChar_eq_rootChar_iff rootChar_pow_mulVec_of_mem_fixedCharTuples)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

set_option linter.unusedSectionVars false

theorem e8Five_torsion_count : E8FiveTorsionCount :=
  Certificates.certificate14974

section Hyperplane


theorem exists_dotProduct_ker {p : ℕ} [Fact p.Prime] (Z' : AddSubgroup (Fin 4 → ZMod p))
    (hcard : p ^ 3 ≤ Nat.card Z') :
    ∃ f : Fin 4 → ZMod p, f ≠ 0 ∧ ∀ c, dotProduct f c = 0 → c ∈ Z' := by
  classical
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  by_cases htop : Z' = ⊤
  · refine ⟨Pi.single 0 1, ?_, fun c _ => by rw [htop]; trivial⟩
    intro h
    have := congrFun h 0
    simp at this
  ·
    have hV : Nat.card (Fin 4 → ZMod p) = p ^ 4 := by simp [Nat.card_eq_fintype_card]
    have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Z'
    rw [hV] at hmul
    have hQdvd : Nat.card ((Fin 4 → ZMod p) ⧸ Z') ∣ p ^ 4 := Dvd.intro _ hmul.symm
    obtain ⟨k, hk, hkQ⟩ := (Nat.dvd_prime_pow hp).1 hQdvd
    have hQ1 : Nat.card ((Fin 4 → ZMod p) ⧸ Z') ≠ 1 := by
      intro h1
      apply htop
      have : Subsingleton ((Fin 4 → ZMod p) ⧸ Z') := (Nat.card_eq_one_iff_unique.1 h1).1
      exact (AddSubgroup.index_eq_one.1 (by rw [AddSubgroup.index]; exact h1))
    have hk1 : k = 1 := by
      have hk0 : k ≠ 0 := fun h0 => hQ1 (by rw [hkQ, h0, pow_zero])
      by_contra hne
      have hk2 : 2 ≤ k := by omega
      have : p ^ 2 ≤ Nat.card ((Fin 4 → ZMod p) ⧸ Z') := by
        rw [hkQ]; exact Nat.pow_le_pow_right hp.pos hk2
      have h3 : p ^ 2 * p ^ 3 ≤ Nat.card ((Fin 4 → ZMod p) ⧸ Z') * Nat.card Z' :=
        Nat.mul_le_mul this hcard
      have h5 : p ^ 5 = p ^ 2 * p ^ 3 := by ring
      have : p ^ 4 < p ^ 5 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
    have hQp : Nat.card ((Fin 4 → ZMod p) ⧸ Z') = p := by rw [hkQ, hk1, pow_one]
    have hZp : Nat.card (ZMod p) = p := by simp [Nat.card_eq_fintype_card]
    let e : ((Fin 4 → ZMod p) ⧸ Z') ≃+ ZMod p := addEquivOfPrimeCardEq hQp hZp
    let φ : (Fin 4 → ZMod p) →+ ZMod p := e.toAddMonoidHom.comp (QuotientAddGroup.mk' Z')
    have hφker : ∀ c, φ c = 0 ↔ c ∈ Z' := fun c => by
      change e (QuotientAddGroup.mk c) = 0 ↔ _
      rw [map_eq_zero_iff _ e.injective, QuotientAddGroup.eq_zero_iff]
    have hφsingle : ∀ (i : Fin 4) (a : ZMod p), φ (Pi.single i a) = a * φ (Pi.single i 1) := by
      intro i a
      have : (Pi.single i a : Fin 4 → ZMod p) = (a.val : ℕ) • (Pi.single i 1 : Fin 4 → ZMod p) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [nsmul_eq_mul]
        · simp [Pi.single_eq_of_ne hj]
      rw [this, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    have hφdot : ∀ c, φ c = dotProduct (fun i => φ (Pi.single i 1)) c := by
      intro c
      conv_lhs => rw [← Finset.univ_sum_single c]
      rw [map_sum]
      calc ∑ i, φ (Pi.single i (c i)) = ∑ i, (c i * φ (Pi.single i 1)) :=
            Finset.sum_congr rfl fun i _ => hφsingle i (c i)
        _ = dotProduct (fun i => φ (Pi.single i 1)) c :=
            Finset.sum_congr rfl fun i _ => mul_comm _ _
    refine ⟨fun i => φ (Pi.single i 1), ?_, fun c hc => ?_⟩
    · intro h
      apply htop
      refine (AddSubgroup.eq_top_iff' Z').2 fun c => ?_
      rw [← hφker, hφdot, h, zero_dotProduct]
    · rw [← hφker, hφdot]
      exact hc

end Hyperplane


section Eigen

@[expose] def e8Vt5 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  ((toMat Tag.E8.rank e8P4VList).map (Int.cast : ℤ → ZMod 5))ᵀ

@[expose] def e8FiveT2 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![2, 1, 1, 4, 0, 0, 0, 0; 0, 1, 4, 1, 0, 0, 0, 0; 2, 2, 1, 1, 0, 0, 0, 0; 2, 3, 0, 3, 0, 0, 0, 0; 1, 4, 2, 2, 1, 0, 0, 0; 1, 2, 1, 4, 0, 1, 0, 0; 1, 4, 0, 3, 0, 0, 1, 0; 3, 0, 1, 2, 0, 0, 0, 1]

@[expose] def e8FiveR2 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![1, 0, 0, 0, 4, 0, 2, 1; 0, 1, 0, 0, 3, 4, 0, 1; 0, 0, 1, 0, 4, 1, 0, 1; 0, 0, 0, 1, 0, 3, 4, 2; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]

theorem e8FiveT2_mul : e8FiveT2 * (e8Vt5 - (2 : ZMod 5) • 1) = e8FiveR2 := by
  decide +kernel

theorem read_eig2 {z : Fin 8 → ZMod 5} (h0 : e8FiveR2 *ᵥ z = 0) :
    z = e8FiveEig2 ![z 4, z 5, z 6, z 7] := by
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have e3 := congrFun h0 3
  simp [e8FiveR2, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] at e0 e1 e2 e3
  funext j
  fin_cases j
  · simp [e8FiveEig2]; linear_combination e0
  · simp [e8FiveEig2]; linear_combination e1
  · simp [e8FiveEig2]; linear_combination e2
  · simp [e8FiveEig2]; linear_combination e3
  · simp [e8FiveEig2]
  · simp [e8FiveEig2]
  · simp [e8FiveEig2]
  · simp [e8FiveEig2]

@[expose] def e8FiveT3 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![0, 1, 3, 1, 0, 0, 0, 0; 3, 2, 2, 4, 0, 0, 0, 0; 2, 3, 3, 0, 0, 0, 0, 0; 2, 2, 4, 4, 0, 0, 0, 0; 1, 3, 2, 2, 1, 0, 0, 0; 2, 3, 2, 4, 0, 1, 0, 0; 4, 4, 3, 2, 0, 0, 1, 0; 4, 0, 1, 3, 0, 0, 0, 1]

@[expose] def e8FiveR3 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![1, 0, 0, 0, 4, 0, 1, 2; 0, 1, 0, 0, 4, 1, 2, 1; 0, 0, 1, 0, 3, 1, 4, 4; 0, 0, 0, 1, 0, 2, 4, 3; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]

theorem e8FiveT3_mul : e8FiveT3 * (e8Vt5 - (3 : ZMod 5) • 1) = e8FiveR3 := by
  decide +kernel

theorem read_eig3 {z : Fin 8 → ZMod 5} (h0 : e8FiveR3 *ᵥ z = 0) :
    z = e8FiveEig3 ![z 4, z 5, z 6, z 7] := by
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have e3 := congrFun h0 3
  simp [e8FiveR3, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] at e0 e1 e2 e3
  funext j
  fin_cases j
  · simp [e8FiveEig3]; linear_combination e0
  · simp [e8FiveEig3]; linear_combination e1
  · simp [e8FiveEig3]; linear_combination e2
  · simp [e8FiveEig3]; linear_combination e3
  · simp [e8FiveEig3]
  · simp [e8FiveEig3]
  · simp [e8FiveEig3]
  · simp [e8FiveEig3]


theorem eig_param2 {z : Fin 8 → ZMod 5} (h : e8Vt5 *ᵥ z = (2 : ZMod 5) • z) :
    z = e8FiveEig2 ![z 4, z 5, z 6, z 7] :=
  read_eig2 (echelon_aux5 e8FiveT2_mul h)

theorem eig_param3 {z : Fin 8 → ZMod 5} (h : e8Vt5 *ᵥ z = (3 : ZMod 5) • z) :
    z = e8FiveEig3 ![z 4, z 5, z 6, z 7] :=
  read_eig3 (echelon_aux5 e8FiveT3_mul h)

theorem e8FiveEig2_add (c c' : Fin 4 → ZMod 5) :
    e8FiveEig2 (c + c') = e8FiveEig2 c + e8FiveEig2 c' := by
  have h : ∀ j : Fin 8, e8FiveEig2 (c + c') j = e8FiveEig2 c j + e8FiveEig2 c' j := by
    intro j
    fin_cases j <;> simp [e8FiveEig2] <;> ring
  exact funext h

theorem e8FiveEig3_add (c c' : Fin 4 → ZMod 5) :
    e8FiveEig3 (c + c') = e8FiveEig3 c + e8FiveEig3 c' := by
  have h : ∀ j : Fin 8, e8FiveEig3 (c + c') j = e8FiveEig3 c j + e8FiveEig3 c' j := by
    intro j
    fin_cases j <;> simp [e8FiveEig3] <;> ring
  exact funext h

theorem e8FiveEig2_pi (c : Fin 4 → ZMod 5) :
    (![e8FiveEig2 c 4, e8FiveEig2 c 5, e8FiveEig2 c 6, e8FiveEig2 c 7] : Fin 4 → ZMod 5) = c := by
  funext j
  fin_cases j <;> simp [e8FiveEig2]

theorem e8FiveEig3_pi (c : Fin 4 → ZMod 5) :
    (![e8FiveEig3 c 4, e8FiveEig3 c 5, e8FiveEig3 c 6, e8FiveEig3 c 7] : Fin 4 → ZMod 5) = c := by
  funext j
  fin_cases j <;> simp [e8FiveEig3]

end Eigen

section Main

theorem exists_many_m40 (B : (Fin 4 → ZMod 5) → (Fin Tag.E8.rank → ZMod 5))
    (hBadd : ∀ c c', B (c + c') = B c + B c')
    (π : (Fin Tag.E8.rank → ZMod 5) → (Fin 4 → ZMod 5)) (hπB : ∀ c, π (B c) = c)
    (Zs : AddSubgroup (Fin Tag.E8.rank → ZMod 5)) (hZ : ∀ z ∈ Zs, z = B (π z))
    (hcard : 125 ≤ Nat.card Zs)
    (hT : ∀ f : Fin 4 → ZMod 5, f ≠ 0 →
      25 ≤ ((e8FiveT40 B).filter fun c => dotProduct f c = 0).card)
    {g : WeylGroup Tag.E8} (hfix : ∀ z ∈ Zs, g ∈ dualWeylStabilizer z) :
    25 ≤ (m40 g).ncard := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hB0 : B 0 = 0 := by
    have := hBadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  let Bh : (Fin 4 → ZMod 5) →+ (Fin Tag.E8.rank → ZMod 5) := AddMonoidHom.mk' B hBadd
  let Z' : AddSubgroup (Fin 4 → ZMod 5) := Zs.comap Bh
  have hZ'mem : ∀ c, c ∈ Z' ↔ B c ∈ Zs := fun c => Iff.rfl
  have hZ'card : Nat.card Z' = Nat.card Zs := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun c : Z' => (⟨B c.1, (hZ'mem c.1).1 c.2⟩ : Zs)) ⟨?_, ?_⟩)
    · intro c c' h
      have h1 : B c.1 = B c'.1 := congrArg Subtype.val h
      exact Subtype.ext (by simpa [hπB] using congrArg π h1)
    · rintro ⟨z, hz⟩
      refine ⟨⟨π z, ?_⟩, Subtype.ext ?_⟩
      · rw [hZ'mem, ← hZ z hz]
        exact hz
      · exact (hZ z hz).symm
  obtain ⟨f, hf0, hf⟩ := exists_dotProduct_ker (p := 5) Z' (by rw [hZ'card]; omega)
  set T' := (e8FiveT40 B).filter fun c => dotProduct f c = 0 with hT'
  have hsub : (T'.image B : Set (Fin Tag.E8.rank → ZMod 5)) ⊆ m40 g := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
    rw [hT', Finset.mem_filter, e8FiveT40, Finset.mem_filter] at hc
    obtain ⟨⟨-, hc0, hc40⟩, hfc⟩ := hc
    refine ⟨hfix _ ((hZ'mem c).1 (hf c hfc)), ?_, hc40⟩
    intro h0
    apply hc0
    rw [← hπB c, h0]
    have : π 0 = 0 := by rw [← hB0, hπB]
    exact this
  have hinj : Function.Injective B := fun c c' h => by
    simpa [hπB] using congrArg π h
  calc 25 ≤ T'.card := hT f hf0
    _ = (T'.image B).card := (Finset.card_image_of_injective _ hinj).symm
    _ = ((T'.image B : Finset _) : Set (Fin Tag.E8.rank → ZMod 5)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (m40 g).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem not_dvd_card_iInf_five
    {lam : ZMod 5} (hlam : lam = 2 ∨ lam = 3) (Zs : AddSubgroup (Fin Tag.E8.rank → ZMod 5))
    (hZ : ∀ z ∈ Zs, e8Vt5 *ᵥ z = lam • z) (hcard : 125 ≤ Nat.card Zs) :
    ¬ 5 ∣ Nat.card (⨅ z ∈ Zs, dualWeylStabilizer z : Subgroup (WeylGroup Tag.E8)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro h5
  set U : Subgroup (WeylGroup Tag.E8) := ⨅ z ∈ Zs, dualWeylStabilizer z with hU
  have : Fintype U := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hgW : orderOf (g : WeylGroup Tag.E8) = 5 := by rw [Subgroup.orderOf_coe]; exact hg
  have hfix : ∀ z ∈ Zs, (g : WeylGroup Tag.E8) ∈ dualWeylStabilizer z := fun z hz => by
    have h1 : (g : WeylGroup Tag.E8) ∈ (⨅ z ∈ Zs, dualWeylStabilizer z : Subgroup (WeylGroup Tag.E8)) :=
      g.2
    rw [Subgroup.mem_iInf] at h1
    exact (Subgroup.mem_iInf.1 (h1 z)) hz
  have hZsub : (Zs : Set (Fin Tag.E8.rank → ZMod 5)) ⊆ fixSet (g : WeylGroup Tag.E8) := hfix
  have hcardn : (Zs : Set (Fin Tag.E8.rank → ZMod 5)).ncard = Nat.card Zs :=
    (Nat.card_coe_set_eq _).symm
  rcases fixset_bound hgW with h | h
  · have := Set.ncard_le_ncard hZsub (Set.toFinite _)
    omega
  · have hT := e8Five_torsion_count
    have h25 : 25 ≤ (m40 (g : WeylGroup Tag.E8)).ncard := by
      rcases hlam with rfl | rfl
      · exact exists_many_m40 e8FiveEig2 e8FiveEig2_add (fun z => ![z 4, z 5, z 6, z 7])
          e8FiveEig2_pi Zs (fun z hz => eig_param2 (hZ z hz)) hcard (fun f hf => (hT f hf).1) hfix
      · exact exists_many_m40 e8FiveEig3 e8FiveEig3_add (fun z => ![z 4, z 5, z 6, z 7])
          e8FiveEig3_pi Zs (fun z hz => eig_param3 (hZ z hz)) hcard (fun f hf => (hT f hf).2) hfix
    omega

end Main

section Tuples

theorem eigen_of_fixedChar {L : Type} [Field L] {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {ζ : Lˣ} (hζ : orderOf ζ = 5) {a : Fin Tag.E8.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e8P4V Fr) {e : Fin Tag.E8.rank → ℕ} (he : ∀ i, a i = ζ ^ e i)
    {z : Fin Tag.E8.rank → ZMod 5} (hz : ∀ i, z i = (e i : ZMod 5)) :
    e8Vt5 *ᵥ z = (q : ZMod 5) • z := by
  have hzfun : z = fun i => (e i : ZMod 5) := funext hz
  refine eq_of_charVal_single (τ := Tag.E8) fun j => ?_
  have hL : charVal (e8Vt5 *ᵥ z) (Pi.single j 1) = charVal z (e8P4V *ᵥ Pi.single j 1) := by
    rw [e8P4V_eq]
    exact charVal_mulVec z (toMat Tag.E8.rank e8P4VList) (Pi.single j 1)
  have h2 : rootChar a (e8P4V *ᵥ Pi.single j 1) =
      rootChar a ((q : ℕ) • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) := by
    have := rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha 1 (Pi.single j 1)
    rw [pow_one, pow_one] at this
    rw [this, rootChar_nsmul]
  have h3 := (rootChar_eq_rootChar_iff hζ e a he _ _).1 h2
  rw [← hzfun] at h3
  calc charVal (e8Vt5 *ᵥ z) (Pi.single j 1) = charVal z (e8P4V *ᵥ Pi.single j 1) := hL
    _ = charVal z ((q : ℕ) • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) := h3
    _ = charVal z ((q : ℤ) • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) := by rw [natCast_zsmul]
    _ = ((q : ℤ) : ZMod 5) * charVal z (Pi.single j 1) := charVal_smul z _ _
    _ = charVal ((q : ZMod 5) • z) (Pi.single j 1) := by
        rw [charVal_smul_col, Int.cast_natCast]

end Tuples

section StabGenFive

theorem sq_add_one_eq_zero_five : ∀ x : ZMod 5, x * x + 1 = 0 → x = 2 ∨ x = 3 := by decide

theorem stabGen_five
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {Fr : L →+* L}
    {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (hq5 : 5 ∣ q * q + 1) (hℓ : ¬ ℓ ∣ 5) :
    StabGen L Fr 5 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro Y hY hcard
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf (L := L) (by norm_num : (5 : ℕ).Prime) hℓ
  have hζ5 : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hYfin : Finite Y := Nat.finite_of_card_ne_zero (by
    have : 0 < 5 ^ 3 := by norm_num
    omega)
  have hYfin' : Finite (Y : Set (Fin Tag.E8.rank → Lˣ)) := hYfin
  refine famStabilizer_subset_closure_of (by norm_num) hζ (Y : Set (Fin Tag.E8.rank → Lˣ))
    (fun a ha i => (hY ha).2 i) ?_
  intro z hz
  have hpow_eq : ∀ m n : ℕ, ζ ^ m = ζ ^ n ↔ m % 5 = n % 5 := fun m n => by
    rw [pow_eq_pow_iff_modEq, hζ]
    rfl
  have hinj_pow : ∀ x y : ZMod 5, ζ ^ x.val = ζ ^ y.val → x = y := fun x y h => by
    have h1 := (hpow_eq _ _).1 h
    rw [Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.mod_eq_of_lt (ZMod.val_lt y)] at h1
    exact ZMod.val_injective 5 h1
  have hadd_pow : ∀ x y : ZMod 5, ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := fun x y => by
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hζ5).symm
  have hz1 : ∀ a b c : (Y : Set (Fin Tag.E8.rank → Lˣ)), c.1 = a.1 * b.1 → z c = z a + z b := by
    intro a b c habc
    funext i
    apply hinj_pow
    have h1 : ζ ^ (z c i).val = c.1 i := (hz c i).symm
    rw [h1, habc, Pi.mul_apply, hz a i, hz b i, Pi.add_apply, hadd_pow]
  have hone : ((1 : Fin Tag.E8.rank → Lˣ) ∈ (Y : Set (Fin Tag.E8.rank → Lˣ))) := one_mem Y
  have hz0 : z ⟨1, hone⟩ = 0 := by
    have := hz1 ⟨1, hone⟩ ⟨1, hone⟩ ⟨1, hone⟩ (by simp)
    exact left_eq_add.1 this
  let Zs : AddSubgroup (Fin Tag.E8.rank → ZMod 5) :=
    { carrier := Set.range z
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨⟨a.1 * b.1, mul_mem a.2 b.2⟩, hz1 a b _ rfl⟩
      zero_mem' := ⟨⟨1, hone⟩, hz0⟩
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        refine ⟨⟨a.1⁻¹, inv_mem a.2⟩, ?_⟩
        have h1 := hz1 ⟨a.1⁻¹, inv_mem a.2⟩ a ⟨1, hone⟩ (by simp)
        rw [hz0] at h1
        exact (eq_neg_of_add_eq_zero_left h1.symm) }
  have hzinj : Function.Injective z := fun a b h => by
    apply Subtype.ext
    funext i
    rw [hz a i, hz b i, h]
  have hcardZ : Nat.card Zs = Nat.card Y := by
    show Nat.card (Set.range z) = _
    rw [Nat.card_range_of_injective hzinj]
    rfl
  have hq : (q : ZMod 5) = 2 ∨ (q : ZMod 5) = 3 := by
    have h0 := (ZMod.natCast_eq_zero_iff (q * q + 1) 5).2 hq5
    push_cast at h0
    exact sq_add_one_eq_zero_five _ h0
  have hE : ∀ w ∈ Zs, e8Vt5 *ᵥ w = (q : ZMod 5) • w := by
    rintro _ ⟨a, rfl⟩
    exact eigen_of_fixedChar hFr hζ (hY a.2).1 (e := fun i => (z a i).val) (hz a)
      (fun i => (ZMod.natCast_zmod_val (z a i)).symm)
  have hiInf : (⨅ a : (Y : Set (Fin Tag.E8.rank → Lˣ)), dualWeylStabilizer (z a) :
      Subgroup (WeylGroup Tag.E8)) = ⨅ w ∈ Zs, dualWeylStabilizer w :=
    le_antisymm (le_iInf₂ fun w hw => by
        obtain ⟨a, rfl⟩ := hw
        exact iInf_le _ a)
      (le_iInf fun a => iInf₂_le (z a) ⟨a, rfl⟩)
  rw [hiInf]
  exact not_dvd_card_iInf_five hq Zs hE (by rw [hcardZ]; exact hcard)

end StabGenFive

end CFSG.RankThree.PartOne.KE8F
