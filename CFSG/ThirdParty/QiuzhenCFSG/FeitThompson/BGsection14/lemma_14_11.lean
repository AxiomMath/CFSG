module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection14.corollary_14_9

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-! # Lemma 14 11 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_mem_omegaOneSubgroup_of_mem_pow_eq_one
    {H : Subgroup G} {p : Nat.Primes} {x : G}
    (hxH : x ∈ H) (hxp : x ^ p.val = 1) :
    x ∈ section12OmegaOneSubgroup p H := by
  let xH : H := ⟨x, hxH⟩
  have hxΩ : xH ∈ omega₁ (G := H) (p := p.val) := by
    rw [omega₁, omega]
    exact Subgroup.subset_closure (by simpa [xH] using hxp)
  exact Subgroup.mem_map.mpr ⟨xH, hxΩ, rfl⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_primeOrder_le_omegaOneSubgroup_of_le
    {H X : Subgroup G} {p : Nat.Primes}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p H) :
    X ≤ section12OmegaOneSubgroup p H := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXH, hXcard⟩
  intro x hxX
  have hxpowX : (⟨x, hxX⟩ : X) ^ Nat.card X = 1 := pow_card_eq_one'
  have hxpow : x ^ p.val = 1 := by
    simpa [hXcard] using congrArg Subtype.val hxpowX
  exact
    section14_mem_omegaOneSubgroup_of_mem_pow_eq_one
      (G := G) (H := H) (p := p) (x := x) (hXH hxX) hxpow

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_isMulCommutative_sup_of_le_centralizer
    {A Y : Subgroup G}
    (hAcomm : IsMulCommutative A) (hYcomm : IsMulCommutative Y)
    (hYleCentA : Y ≤ Subgroup.centralizer (A : Set G)) :
    IsMulCommutative (A ⊔ Y : Subgroup G) := by
  classical
  let D : Subgroup G := A ⊔ Y
  let AD : Subgroup D := A.subgroupOf D
  let YD : Subgroup D := Y.subgroupOf D
  have hA_norm_Y : A ≤ Subgroup.normalizer (Y : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hcomm : a * y = y * a :=
        Subgroup.mem_centralizer_iff.mp (hYleCentA hy) a ha
      have hconj : a * y * a⁻¹ = y := by
        calc
          a * y * a⁻¹ = y * a * a⁻¹ := by rw [hcomm]
          _ = y := by simp [mul_assoc]
      simpa [hconj] using hy
    · intro hy
      let y' : G := a * y * a⁻¹
      have hy'Y : y' ∈ Y := by simpa [y'] using hy
      have hcomm' : a * y' = y' * a :=
        Subgroup.mem_centralizer_iff.mp (hYleCentA hy'Y) a ha
      have hconj : a⁻¹ * y' * a = y' := by
        have h := congrArg (fun t : G => a⁻¹ * t) hcomm'
        simpa [mul_assoc] using h.symm
      have hy_eq : y = y' := by
        calc
          y = a⁻¹ * y' * a := by simp [y', mul_assoc]
          _ = y' := hconj
      simpa [hy_eq] using hy'Y
  haveI : YD.Normal := by
    simpa [D, YD] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := A) (N := Y) hA_norm_Y)
  have hAD_YD_top : AD ⊔ YD = ⊤ := by
    calc
      AD ⊔ YD = D.subgroupOf D := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := A) (A' := Y) (B := D)
          (by simp [D])
          (by simp [D])
      _ = ⊤ := by simp
  refine ⟨⟨fun x y => ?_⟩⟩
  have hxTop : x ∈ AD ⊔ YD := by simp [hAD_YD_top]
  have hyTop : y ∈ AD ⊔ YD := by simp [hAD_YD_top]
  rcases (Subgroup.mem_sup_of_normal_right (s := AD) (t := YD) (x := x)).1 hxTop with
    ⟨aD, haD, bD, hbD, hxab⟩
  rcases (Subgroup.mem_sup_of_normal_right (s := AD) (t := YD) (x := y)).1 hyTop with
    ⟨cD, hcD, dD, hdD, hycd⟩
  let a : G := aD
  let b : G := bD
  let c : G := cD
  let d : G := dD
  have haA : a ∈ A := by simpa [a, AD, Subgroup.mem_subgroupOf] using haD
  have hbY : b ∈ Y := by simpa [b, YD, Subgroup.mem_subgroupOf] using hbD
  have hcA : c ∈ A := by simpa [c, AD, Subgroup.mem_subgroupOf] using hcD
  have hdY : d ∈ Y := by simpa [d, YD, Subgroup.mem_subgroupOf] using hdD
  have hx_eq : (x : G) = a * b := by
    have hval := congrArg (fun z : D => (z : G)) hxab
    simpa [a, b] using hval.symm
  have hy_eq : (y : G) = c * d := by
    have hval := congrArg (fun z : D => (z : G)) hycd
    simpa [c, d] using hval.symm
  have hac : a * c = c * a :=
    setLike_mul_comm (s := A) haA hcA
  have hbd : b * d = d * b :=
    setLike_mul_comm (s := Y) hbY hdY
  have hbc : b * c = c * b :=
    (Subgroup.mem_centralizer_iff.mp (hYleCentA hbY) c hcA).symm
  have had : a * d = d * a :=
    Subgroup.mem_centralizer_iff.mp (hYleCentA hdY) a haA
  apply Subtype.ext
  change (x : G) * (y : G) = (y : G) * (x : G)
  rw [hx_eq, hy_eq]
  calc
    (a * b) * (c * d) = a * (b * c) * d := by simp [mul_assoc]
    _ = a * (c * b) * d := by rw [hbc]
    _ = (a * c) * (b * d) := by simp [mul_assoc]
    _ = (c * a) * (d * b) := by rw [hac, hbd]
    _ = c * (a * d) * b := by simp [mul_assoc]
    _ = c * (d * a) * b := by rw [had]
    _ = (c * d) * (a * b) := by simp [mul_assoc]

omit [IsMinCE G] in
private theorem CFSG.section14_commutator_centralizerIn_eq_bot_of_coprime
    {K P : Subgroup G}
    (hPnormK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card K))
    (hKcomm : IsMulCommutative K) :
    subgroupCentralizerIn ⁅K, P⁆ P = ⊥ := by
  classical
  have hcomm_le_left : ⁅K, P⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro k hk p hp
    have hkconj : p * k⁻¹ * p⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hPnormK hp) (k⁻¹)).1 (K.inv_mem hk)
    simpa [commutatorElement_def, mul_assoc] using K.mul_mem hk hkconj
  haveI : Subgroup.Normalizes P K := ⟨hPnormK⟩
  let Cfix : Subgroup K := fixedPointSubgroup (↥P) (↥K)
  let Ccomm : Subgroup K := commutatorAction (A := ↥P) (G := ↥K)
  have hfixed_eq :
      Cfix = (subgroupCentralizerIn K P).subgroupOf K := by
    simpa [Cfix] using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn K P hPnormK
  have hcomm_map : Ccomm.map K.subtype = ⁅K, P⁆ := by
    simpa [Ccomm] using
      commutatorAction_subgroup_conj_map_eq_commutator K P hPnormK
  have hsolvK : Group.IsSolvable K := by
    let : IsMulCommutative K := hKcomm
    let : CommGroup K := IsMulCommutative.instCommGroup
    infer_instance
  have hcompl : IsCompl Cfix Ccomm := by
    simpa [Cfix, Ccomm] using
      (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := K) (A := P) hsolvK hcop hKcomm)
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases hx with ⟨hxK0, hxCentP⟩
  have hxK : x ∈ K := hcomm_le_left hxK0
  let xK : K := ⟨x, hxK⟩
  have hxFix : xK ∈ Cfix := by
    rw [hfixed_eq]
    change (x : G) ∈ subgroupCentralizerIn K P
    exact ⟨hxK, hxCentP⟩
  have hxComm : xK ∈ Ccomm := by
    have hxMap : x ∈ Ccomm.map K.subtype := by
      simpa [hcomm_map] using hxK0
    rcases Subgroup.mem_map.mp hxMap with ⟨y, hyC, hyx⟩
    have hy_eq : y = xK := Subtype.ext hyx
    simpa [hy_eq] using hyC
  have hxbot : xK ∈ (⊥ : Subgroup K) := by
    have hinf_bot : Cfix ⊓ Ccomm = ⊥ := hcompl.disjoint.eq_bot
    have hxinf : xK ∈ Cfix ⊓ Ccomm := ⟨hxFix, hxComm⟩
    simpa [hinf_bot] using hxinf
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_subgroupCentralizerIn_normal_of_normal
    {E A : Subgroup G} (hAnorm : section10NormalIn A E) :
    section10NormalIn (subgroupCentralizerIn E A) E := by
  classical
  have hAE : A ≤ E := hAnorm.1
  haveI : (A.subgroupOf E).Normal := hAnorm.2
  have hC_le_E : subgroupCentralizerIn E A ≤ E := inf_le_left
  refine ⟨hC_le_E, ?_⟩
  have hCsub_eq :
      (subgroupCentralizerIn E A).subgroupOf E =
        Subgroup.centralizer ((A.subgroupOf E : Subgroup E) : Set E) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      apply Subtype.ext
      have hxC : (x : G) ∈ Subgroup.centralizer (A : Set G) := hx.2
      have haA : (a : G) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using ha
      exact Subgroup.mem_centralizer_iff.mp hxC (a : G) haA
    · intro hx
      refine ⟨x.property, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr (fun a ha => by
        let aE : E := ⟨a, hAE ha⟩
        have haSub : aE ∈ A.subgroupOf E := by
          simpa [aE, Subgroup.mem_subgroupOf] using ha
        have hcomm := Subgroup.mem_centralizer_iff.mp hx aE haSub
        exact congrArg Subtype.val hcomm)
  rw [hCsub_eq]
  exact Subgroup.normal_centralizer

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_quotient_prime_of_primeOrder_not_le_centralizer
    {E A Q : Subgroup G} {q : Nat.Primes}
    (hAnorm : section10NormalIn A E)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q E)
    (hQ_not_le_C : ¬ Q ≤ subgroupCentralizerIn E A) :
    q ∈ section12QuotientPrimeSet (subgroupCentralizerIn E A) E := by
  classical
  let C : Subgroup G := subgroupCentralizerIn E A
  have hCnorm : section10NormalIn C E :=
    section14_subgroupCentralizerIn_normal_of_normal
      (G := G) (E := E) (A := A) hAnorm
  have hQ_inf_C_bot : Q ⊓ C = ⊥ := by
    let R : Subgroup Q := (Q ⊓ C).subgroupOf Q
    haveI : Fact (Nat.card Q).Prime := by
      rw [hQ.2]
      exact ⟨q.2⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (G := Q) R with hRbot | hRtop
    · apply le_bot_iff.mp
      intro x hx
      have hxR : (⟨x, hx.1⟩ : Q) ∈ R := by
        simpa [R, Subgroup.mem_subgroupOf] using hx.2
      have hxbot : (⟨x, hx.1⟩ : Q) ∈ (⊥ : Subgroup Q) := by
        simpa [hRbot] using hxR
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)
    · have hQ_le_C : Q ≤ C := by
        intro x hxQ
        have hxR : (⟨x, hxQ⟩ : Q) ∈ R := by
          simp [R, hRtop]
        simpa [R, Subgroup.mem_subgroupOf] using hxR
      exact False.elim (hQ_not_le_C hQ_le_C)
  have hQ_norm_C : Q ≤ Subgroup.normalizer (C : Set G) :=
    hQ.1.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hCnorm.1).1 hCnorm.2)
  let D : Subgroup G := Q ⊔ C
  have hcompCQ : (C.subgroupOf D).IsComplement' (Q.subgroupOf D) := by
    simpa [C, D, sup_comm, inf_comm] using
      section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
        (G := G) (H := C) (R := Q) hQ_norm_C
        (by simpa [inf_comm] using hQ_inf_C_bot)
  have hq_rel_D : q.val ∣ C.relIndex D := by
    have hQsub_card : Nat.card (Q.subgroupOf D) = q.val := by
      calc
        Nat.card (Q.subgroupOf D) = Nat.card Q := by
          simpa [D] using section12_card_subgroupOf_eq (H := Q) (K := D) le_sup_left
        _ = q.val := hQ.2
    have hq_idx : q.val ∣ (C.subgroupOf D).index := by
      have hq_card : q.val ∣ Nat.card (Q.subgroupOf D) := by
        simp [hQsub_card]
      simpa [hcompCQ.symm.index_eq_card] using hq_card
    simpa [Subgroup.relIndex] using hq_idx
  have hD_le_E : D ≤ E := by
    exact sup_le hQ.1 inf_le_left
  have hCsub_le_Dsub : C.subgroupOf E ≤ D.subgroupOf E := by
    intro x hx
    simpa [C, D, Subgroup.mem_subgroupOf] using (le_sup_right : C ≤ Q ⊔ C) hx
  have hrel_eq :
      (C.subgroupOf E).relIndex (D.subgroupOf E) = C.relIndex D := by
    simpa [C, D] using
      (Subgroup.relIndex_subgroupOf
        (H := C) (K := D) (L := E) (hKL := hD_le_E))
  have hq_idx_E : q.val ∣ (C.subgroupOf E).index :=
    (hrel_eq.symm ▸ hq_rel_D).trans
      (Subgroup.relIndex_dvd_index_of_le hCsub_le_Dsub)
  exact ⟨inf_le_left, hq_idx_E⟩

private theorem CFSG.section14_lemma_14_11_not_tau2
    {M E E₁₂ E₁ E₂ E₃ Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section14MFamilyF G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q E)
    (hQnotF : ¬ Q ≤ section8FittingSubgroup E) :
    q ∉ section12Tau2Primes M := by
  intro hqτ2
  obtain ⟨A, hA⟩ :=
    section12_exists_rankTwo_in_E_of_tau2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE hqτ2
  have hQA : Q ∈ section10PrimeOrderSubgroupsIn q A := by
    have hEq :=
      (corollary_12_6_a
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := q)
        hM.1 hE hqτ2 hA).2
    simpa [hEq] using hQ
  have hAnorm : section10NormalIn A E :=
    (corollary_12_6_a
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := q)
      hM.1 hE hqτ2 hA).1
  have hAnil : Group.IsNilpotent A := by
    have hElem := (section12_rankTwo_elementary hA).2
    letI : IsElementaryAbelian q.val A := hElem
    letI : IsMulCommutative A := hElem.toIsMulCommutative
    letI : CommGroup A := IsMulCommutative.instCommGroup
    infer_instance
  have hA_le_F : A ≤ section8FittingSubgroup E := by
    simpa [section8FittingSubgroup] using
      section12_le_fittingSubgroupOf_of_normalIn_nilpotent
        (G := G) (H := E) (N := A) hAnorm.1 hAnorm.2 hAnil
  exact hQnotF (hQA.1.trans hA_le_F)

private theorem CFSG.section14_lemma_14_11_not_tau3
    {M E E₁₂ E₁ E₂ E₃ Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section14MFamilyF G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q E)
    (hQnotF : ¬ Q ≤ section8FittingSubgroup E) :
    q ∉ section12Tau3Primes M := by
  intro hqτ3
  have hE3norm : section10NormalIn E₃ E :=
    (lemma_12_1_b
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE).2
  haveI : (E₃.subgroupOf E).Normal := hE3norm.2
  have hQsubE_p : IsPGroup q.val (Q.subgroupOf E) := by
    refine IsPGroup.of_card (p := q.val) (G := Q.subgroupOf E) (n := 1) ?_
    have hcard : Nat.card (Q.subgroupOf E) = Nat.card Q :=
      section12_card_subgroupOf_eq hQ.1
    simp [hcard, hQ.2, pow_one]
  have hQsub_le_E3sub : Q.subgroupOf E ≤ E₃.subgroupOf E :=
    section12_pSubgroup_le_normal_hall_of_prime_mem
      (R := E) (π := section12Tau3Primes M) (H := E₃.subgroupOf E)
      (A := Q.subgroupOf E) hE.2.2.2.2.2 hqτ3 hQsubE_p
  have hQ_le_E3 : Q ≤ E₃ := by
    intro x hxQ
    let xE : E := ⟨x, hQ.1 hxQ⟩
    have hxSub : xE ∈ Q.subgroupOf E := by
      simpa [xE, Subgroup.mem_subgroupOf] using hxQ
    have hxE3sub : xE ∈ E₃.subgroupOf E := hQsub_le_E3sub hxSub
    simpa [xE, Subgroup.mem_subgroupOf] using hxE3sub
  have hE3cyc : IsCyclic E₃ :=
    (lemma_12_1_d
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE).2
  have hE3nil : Group.IsNilpotent E₃ := by
    letI : IsCyclic E₃ := hE3cyc
    letI : IsMulCommutative E₃ := IsCyclic.isMulCommutative
    letI : CommGroup E₃ := IsMulCommutative.instCommGroup
    infer_instance
  have hE3_le_F : E₃ ≤ section8FittingSubgroup E := by
    simpa [section8FittingSubgroup] using
      section12_le_fittingSubgroupOf_of_normalIn_nilpotent
        (G := G) (H := E) (N := E₃) hE3norm.1 hE3norm.2 hE3nil
  exact hQnotF (hQ_le_E3.trans hE3_le_F)

private theorem CFSG.section14_lemma_14_11_tau1
    {M E E₁₂ E₁ E₂ E₃ Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section14MFamilyF G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hq : q ∈ subgroupPrimeSet E)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q E)
    (hQnotF : ¬ Q ≤ section8FittingSubgroup E) :
    q ∈ section12Tau1Primes M := by
  have hqτ :=
    section12_prime_mem_tau_union_of_mem_E (G := G) hM.1 hE.1 hq
  rcases hqτ with hqτ12 | hqτ3
  · rcases hqτ12 with hqτ1 | hqτ2
    · exact hqτ1
    · exact False.elim
        (section14_lemma_14_11_not_tau2
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q)
          hM hE hQ hQnotF hqτ2)
  · exact False.elim
      (section14_lemma_14_11_not_tau3
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q)
        hM hE hQ hQnotF hqτ3)

private theorem CFSG.section14_lemma_14_11_sylow_cyclic
    {M E E₁₂ E₁ E₂ E₃ Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section14MFamilyF G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hq : q ∈ subgroupPrimeSet E)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q E)
    (hQnotF : ¬ Q ≤ section8FittingSubgroup E)
    (S : Sylow q.val E) :
    IsCyclic (S : Subgroup E) := by
  have hqτ1 :=
    section14_lemma_14_11_tau1
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q)
      hM hE hq hQ hQnotF
  have hqE : q.val ∣ Nat.card E := by
    simpa [subgroupPrimeSet] using hq
  have hqG : q.val ∣ Nat.card G :=
    hqE.trans (Subgroup.card_subgroup_dvd_card E)
  have hqodd : q.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hqG
  have hqrank : primeRank q.val E ≤ 1 := by
    rcases hqτ1 with ⟨_hqσ, _hqder, hqrank⟩
    have hEM : E ≤ M := hE.1.2.1
    let e : E.subgroupOf M ≃* E :=
      Subgroup.subgroupOfEquivOfLe (H := E) (K := M) hEM
    have hqrank_sub : primeRank q.val (E.subgroupOf M) ≤ 1 := by
      simpa [hqrank] using
        section8_primeRank_le_of_subgroup (S := E.subgroupOf M) q.val
    exact
      (section14_primeRank_le_of_equiv
        (R := E.subgroupOf M) (S := E) q.val e).trans hqrank_sub
  exact section12_sylow_cyclic_of_primeRank_le_one hqodd hqrank S

private theorem CFSG.section14_lemma_14_11_msigma_centralizer_bot
    {M E E₁₂ E₁ E₂ E₃ Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section14MFamilyF G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hq : q ∈ subgroupPrimeSet E)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q E)
    (hQnotF : ¬ Q ≤ section8FittingSubgroup E) :
    subgroupCentralizerIn (section10Msigma M) Q = ⊥ := by
  have hqτ1 :=
    section14_lemma_14_11_tau1
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q)
      hM hE hq hQ hQnotF
  by_contra hCQne
  have hQM : Q ≤ M := hQ.1.trans hE.1.2.1
  have hQ_M : Q ∈ section10PrimeOrderSubgroupsIn q M := ⟨hQM, hQ.2⟩
  have hqκ : q ∈ section14KappaPrimes M :=
    ⟨Or.inl hqτ1, ⟨Q, hQ_M, hCQne⟩⟩
  simp [hM.2] at hqκ

private theorem CFSG.section14_lemma_14_11_fitting_qprime
    {M E E₁₂ E₁ E₂ E₃ Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section14MFamilyF G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hq : q ∈ subgroupPrimeSet E)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q E)
    (hQnotF : ¬ Q ≤ section8FittingSubgroup E) :
    q ∉ subgroupPrimeSet (section8FittingSubgroup E) := by
  haveI : Fact q.val.Prime := ⟨q.2⟩
  intro hqF
  let F : Subgroup G := section8FittingSubgroup E
  let Fsub : Subgroup E := F.subgroupOf E
  have hFsub_eq : Fsub = fittingSubgroup E := by
    simpa [F, Fsub] using section8FittingSubgroup_subgroupOf_eq E
  have hqFsub : q ∈ subgroupPrimeSet Fsub := by
    rw [section8_subgroupPrimeSet_subgroupOf_eq (section8FittingSubgroup_le E)]
    exact hqF
  have hFsub_char : Fsub.Characteristic := by
    rw [hFsub_eq]
    infer_instance
  have hFsub_nil : Group.IsNilpotent Fsub := by
    rw [hFsub_eq]
    infer_instance
  let P : Sylow q.val Fsub := default
  let Pmap : Subgroup E := (P : Subgroup Fsub).map Fsub.subtype
  have hP_ne : (P : Subgroup Fsub) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := Fsub) (p := q.val) P (by
      simpa [subgroupPrimeSet] using hqFsub)
  have hPmap_ne : Pmap ≠ ⊥ := by
    intro hPmap_bot
    have hmap_bot : (P : Subgroup Fsub).map Fsub.subtype = (⊥ : Subgroup Fsub).map Fsub.subtype := by
      simpa [Pmap] using hPmap_bot
    exact hP_ne (Subgroup.map_injective Fsub.subtype_injective hmap_bot)
  have hP_normal : (P : Subgroup Fsub).Normal :=
    Group.IsNilpotent.sylow_normal hFsub_nil q.val P
  have hP_char : (P : Subgroup Fsub).Characteristic :=
    Sylow.characteristic_of_normal P hP_normal
  have hPmap_char : Pmap.Characteristic := by
    letI : Fsub.Characteristic := hFsub_char
    letI : (P : Subgroup Fsub).Characteristic := hP_char
    simpa [Pmap] using
      characteristic_map_subtype_of_characteristic (G := E) Fsub (P : Subgroup Fsub)
  have hPmap_p : IsPGroup q.val Pmap := by
    simpa [Pmap] using IsPGroup.map (p := q.val) (H := (P : Subgroup Fsub)) P.isPGroup' Fsub.subtype
  obtain ⟨S, hPmap_le_S⟩ := IsPGroup.exists_le_sylow (G := E) (p := q.val) hPmap_p
  have hS_cyc : IsCyclic (S : Subgroup E) :=
    section14_lemma_14_11_sylow_cyclic
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q)
      hM hE hq hQ hQnotF S
  have hPmap_cyc : IsCyclic Pmap := by
    letI : IsCyclic (S : Subgroup E) := hS_cyc
    have hsub_cyc : IsCyclic (Pmap.subgroupOf (S : Subgroup E)) := by
      infer_instance
    exact
      (Subgroup.subgroupOfEquivOfLe
        (H := Pmap) (K := (S : Subgroup E)) hPmap_le_S).isCyclic.1 hsub_cyc
  let Ωlocal : Subgroup Pmap := omega₁ (G := Pmap) (p := q.val)
  let ΩE : Subgroup E := section12OmegaOneSubgroup q Pmap
  have hΩlocal_char : Ωlocal.Characteristic := by
    simpa [Ωlocal] using omega₁_characteristic (G := Pmap) (p := q.val)
  have hΩE_char : ΩE.Characteristic := by
    letI : Pmap.Characteristic := hPmap_char
    letI : Ωlocal.Characteristic := hΩlocal_char
    simpa [ΩE, Ωlocal, section12OmegaOneSubgroup] using
      characteristic_map_subtype_of_characteristic (G := E) Pmap Ωlocal
  have hΩE_normal : ΩE.Normal := by
    letI : ΩE.Characteristic := hΩE_char
    infer_instance
  have hΩE_le_Pmap : ΩE ≤ Pmap := by
    simpa [ΩE, Ωlocal, section12OmegaOneSubgroup] using Subgroup.map_subtype_le Ωlocal
  have hPmap_le_Fsub : Pmap ≤ Fsub := by
    simpa [Pmap] using Subgroup.map_subtype_le (P : Subgroup Fsub)
  have hΩE_le_Fsub : ΩE ≤ Fsub := hΩE_le_Pmap.trans hPmap_le_Fsub
  have hΩE_card : Nat.card ΩE = q.val := by
    simpa [ΩE] using
      section14_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
        (G := E) (H := Pmap) (p := q) hPmap_p hPmap_cyc hPmap_ne
  have hΩE_p : IsPGroup q.val ΩE := by
    refine IsPGroup.of_card (p := q.val) (G := ΩE) (n := 1) ?_
    simp [hΩE_card]
  let Qsub : Subgroup E := Q.subgroupOf E
  have hQsub_card : Nat.card Qsub = q.val := by
    calc
      Nat.card Qsub = Nat.card Q := by
        simpa [Qsub] using section12_card_subgroupOf_eq hQ.1
      _ = q.val := hQ.2
  have hQsub_p : IsPGroup q.val Qsub := by
    refine IsPGroup.of_card (p := q.val) (G := Qsub) (n := 1) ?_
    simp [hQsub_card]
  have hsup_p : IsPGroup q.val (ΩE ⊔ Qsub : Subgroup E) := by
    letI : ΩE.Normal := hΩE_normal
    have hsup_p' : IsPGroup q.val (Qsub ⊔ ΩE : Subgroup E) := by
      exact IsPGroup.to_sup_of_normal_right
        (p := q.val) (H := Qsub) (K := ΩE) hQsub_p hΩE_p
    rw [sup_comm]
    exact hsup_p'
  obtain ⟨S0, hsup_le_S0⟩ := IsPGroup.exists_le_sylow (G := E) (p := q.val) hsup_p
  have hΩE_le_S0 : ΩE ≤ (S0 : Subgroup E) := le_trans le_sup_left hsup_le_S0
  have hQsub_le_S0 : Qsub ≤ (S0 : Subgroup E) := le_trans le_sup_right hsup_le_S0
  have hS0_cyc : IsCyclic (S0 : Subgroup E) :=
    section14_lemma_14_11_sylow_cyclic
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q)
      hM hE hq hQ hQnotF S0
  let ΩS0 : Subgroup E := section12OmegaOneSubgroup q (S0 : Subgroup E)
  have hS0_ne : (S0 : Subgroup E) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := E) (p := q.val) S0 (by
      simpa [subgroupPrimeSet] using hq)
  have hΩS0_card : Nat.card ΩS0 = q.val := by
    simpa [ΩS0] using
      section14_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
        (G := E) (H := (S0 : Subgroup E)) (p := q) S0.isPGroup' hS0_cyc hS0_ne
  have hΩE_prime_S0 : ΩE ∈ section10PrimeOrderSubgroupsIn q (S0 : Subgroup E) := by
    exact ⟨hΩE_le_S0, hΩE_card⟩
  have hQsub_prime_S0 : Qsub ∈ section10PrimeOrderSubgroupsIn q (S0 : Subgroup E) := by
    exact ⟨hQsub_le_S0, hQsub_card⟩
  have hΩE_le_ΩS0 : ΩE ≤ ΩS0 :=
    section14_primeOrder_le_omegaOneSubgroup_of_le
      (G := E) (H := (S0 : Subgroup E)) (X := ΩE) (p := q) hΩE_prime_S0
  have hQsub_le_ΩS0 : Qsub ≤ ΩS0 :=
    section14_primeOrder_le_omegaOneSubgroup_of_le
      (G := E) (H := (S0 : Subgroup E)) (X := Qsub) (p := q) hQsub_prime_S0
  have hΩE_eq_ΩS0 : ΩE = ΩS0 := by
    refine Subgroup.eq_of_le_of_card_ge hΩE_le_ΩS0 ?_
    exact le_of_eq (hΩS0_card.trans hΩE_card.symm)
  have hQsub_eq_ΩS0 : Qsub = ΩS0 := by
    refine Subgroup.eq_of_le_of_card_ge hQsub_le_ΩS0 ?_
    exact le_of_eq (hΩS0_card.trans hQsub_card.symm)
  have hQsub_eq_ΩE : Qsub = ΩE := hQsub_eq_ΩS0.trans hΩE_eq_ΩS0.symm
  have hQ_le_F : Q ≤ F := by
    intro x hxQ
    let xE : E := ⟨x, hQ.1 hxQ⟩
    have hxQsub : xE ∈ Qsub := by
      simpa [Qsub, xE, Subgroup.mem_subgroupOf] using hxQ
    have hxΩE : xE ∈ ΩE := by
      simpa [hQsub_eq_ΩE] using hxQsub
    have hxFsub : xE ∈ Fsub := hΩE_le_Fsub hxΩE
    simpa [Fsub, F, xE, Subgroup.mem_subgroupOf] using hxFsub
  exact hQnotF hQ_le_F

private theorem CFSG.section14_lemma_14_11_exists_rankTwo_nontrivial_commutator
    {M E E₁₂ E₁ E₂ E₃ Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section14MFamilyF G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hq : q ∈ subgroupPrimeSet E)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q E)
    (hQnotF : ¬ Q ≤ section8FittingSubgroup E) :
    ∃ p : Nat.Primes, ∃ A : Subgroup G,
      p ∈ section12Tau2Primes M ∧
        A ∈ section12RankTwoElementaryAbelianIn p E ∧
          ⁅A, Q⁆ ≠ ⊥ ∧
            q ∈ section12QuotientPrimeSet (subgroupCentralizerIn E A) E := by
  classical
  haveI : Fact q.val.Prime := ⟨q.2⟩
  let K : Subgroup G := ⁅E, Q⁆
  let K₀ : Subgroup G := ⁅K, Q⁆
  have hQM : Q ≤ M := hQ.1.trans hE.1.2.1
  have hqτ1 :=
    section14_lemma_14_11_tau1
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q)
      hM hE hq hQ hQnotF
  have hCQbot :=
    section14_lemma_14_11_msigma_centralizer_bot
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q)
      hM hE hq hQ hQnotF
  have hq_not_sigma : q ∉ section10SigmaPrimes M := hqτ1.1
  have hK_le_E : K ≤ E := by
    change ⁅E, Q⁆ ≤ E
    rw [Subgroup.commutator_le]
    intro e he q' hq'
    have hqNormE : q' ∈ Subgroup.normalizer (E : Set G) :=
      Subgroup.le_normalizer (hQ.1 hq')
    have hconj : q' * e⁻¹ * q'⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp hqNormE (e⁻¹)).1 (E.inv_mem he)
    simpa [commutatorElement_def, mul_assoc] using E.mul_mem he hconj
  have hK_norm_E : section10NormalIn K E := by
    have hK_norm_sup : ((⁅E, Q⁆).subgroupOf (E ⊔ Q)).Normal := by
      exact commutator_normal_in_sup E Q
    have hsup_norm :
        E ⊔ Q ≤ Subgroup.normalizer ((⁅E, Q⁆ : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := ⁅E, Q⁆) (K := E ⊔ Q) (commutator_le_sup E Q)).1 hK_norm_sup
    have hE_norm :
        E ≤ Subgroup.normalizer ((⁅E, Q⁆ : Subgroup G) : Set G) :=
      le_trans le_sup_left hsup_norm
    refine ⟨hK_le_E, ?_⟩
    simpa [K] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := ⁅E, Q⁆) (K := E) (by simpa [K] using hK_le_E)).2 hE_norm
  have hK_le_der : K ≤ ambientDerivedSubgroup E := by
    have hcomm_le : ⁅E, Q⁆ ≤ ⁅E, E⁆ := Subgroup.commutator_mono le_rfl hQ.1
    simpa [K, section12_ambientDerivedSubgroup_eq_commutator] using hcomm_le
  have hDer_comm : IsMulCommutative (ambientDerivedSubgroup E) :=
    (corollary_12_10_b
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE).2
  have hK_comm : IsMulCommutative K :=
    section14_isMulCommutative_of_le hDer_comm hK_le_der
  have hK_nil : Group.IsNilpotent K := by
    letI : IsMulCommutative K := hK_comm
    letI : CommGroup K := IsMulCommutative.instCommGroup
    infer_instance
  have hK_le_F : K ≤ section8FittingSubgroup E := by
    simpa [section8FittingSubgroup] using
      section12_le_fittingSubgroupOf_of_normalIn_nilpotent
        (G := G) (H := E) (N := K) hK_norm_E.1 hK_norm_E.2 hK_nil
  have hqF :
      q ∉ subgroupPrimeSet (section8FittingSubgroup E) :=
    section14_lemma_14_11_fitting_qprime
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q)
      hM hE hq hQ hQnotF
  have hK_qprime : IsPiSubgroup (G := G) (section10PPrimeSet q) K := by
    intro r hrK
    have hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup E) :=
      hrK.trans (Subgroup.card_dvd_of_le hK_le_F)
    rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hrq
    subst hrq
    exact hqF hrF
  have hE_norm_K : E ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK_norm_E.1).1 hK_norm_E.2
  have hQ_norm_K : Q ≤ Subgroup.normalizer (K : Set G) := hQ.1.trans hE_norm_K
  have hQ_normIn_K : Q ≤ subgroupNormalizerIn M (K : Set G) := by
    exact le_inf hQ_norm_K hQM
  have hK_sigma_compl :
      IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ K :=
    section12_subgroup_of_complement_is_sigma_compl
      (G := G) (M := M) (E := E) (K := K) hM.1 hE.1 hK_le_E
  have h10_11d :=
    proposition_10_11_d
      (G := G) (M := M) (K := K) (P := Q) (p := q)
      hM.1 (hK_le_E.trans hE.1.2.1) hK_sigma_compl hq_not_sigma
      hQ_normIn_K hQ.2 hCQbot hK_comm hK_qprime
  rcases h10_11d with ⟨_hK₀cent, hK₀_norm_M, hK₀_cyc⟩
  have hK₀_le_K : K₀ ≤ K := by
    change ⁅K, Q⁆ ≤ K
    rw [Subgroup.commutator_le]
    intro k hk q' hq'
    have hqNormK : q' ∈ Subgroup.normalizer (K : Set G) := hQ_norm_K hq'
    have hconj : q' * k⁻¹ * q'⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hqNormK (k⁻¹)).1 (K.inv_mem hk)
    simpa [commutatorElement_def, mul_assoc] using K.mul_mem hk hconj
  have hK₀_le_E : K₀ ≤ E := hK₀_le_K.trans hK_le_E
  have hq_coprime_K : Nat.Coprime (Nat.card Q) (Nat.card K) := by
    rw [hQ.2]
    refine Nat.coprime_of_dvd ?_
    intro r hrPrime hrqdiv hrKdiv
    have hr_eq_q : r = q.val := ((q.2.dvd_iff_eq hrPrime.ne_one).1 hrqdiv).symm
    let r' : Nat.Primes := ⟨r, hrPrime⟩
    have hrK : r' ∈ subgroupPrimeSet K := by
      simpa [subgroupPrimeSet] using hrKdiv
    have hrK' : r' ∈ section10PPrimeSet q := hK_qprime r' hrK
    rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff] at hrK'
    exact hrK' (Subtype.ext hr_eq_q)
  have hCK₀bot : subgroupCentralizerIn K₀ Q = ⊥ := by
    simpa [K₀] using
      section14_commutator_centralizerIn_eq_bot_of_coprime
        (G := G) (K := K) (P := Q) hQ_norm_K hq_coprime_K hK_comm
  have hK₀_ne_bot : K₀ ≠ ⊥ := by
    intro hK₀bot
    have hK_le_cent_Q : K ≤ Subgroup.centralizer (Q : Set G) := by
      simpa [K₀, hK₀bot] using
        (Subgroup.commutator_eq_bot_iff_le_centralizer : ⁅K, Q⁆ = ⊥ ↔
          K ≤ Subgroup.centralizer (Q : Set G)).mp hK₀bot
    have hQ_comm : IsMulCommutative Q := by
      letI : IsCyclic Q := isCyclic_of_prime_card hQ.2
      infer_instance
    have hKQ_comm : IsMulCommutative (Q ⊔ K : Subgroup G) :=
      section14_isMulCommutative_sup_of_le_centralizer
        (G := G) (A := Q) (Y := K) hQ_comm hK_comm hK_le_cent_Q
    have hQK_le_E : Q ⊔ K ≤ E := sup_le hQ.1 hK_le_E
    have hK_sub_norm_QK : (K.subgroupOf (Q ⊔ K)).Normal := by
      simpa [sup_comm] using
        (Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := Q) (N := K) hQ_norm_K)
    have hconj_QK {e y : G} (he : e ∈ E) (hy : y ∈ Q ⊔ K) :
        e * y * e⁻¹ ∈ Q ⊔ K := by
      let D : Subgroup G := Q ⊔ K
      let Kd : Subgroup D := K.subgroupOf D
      let Qd : Subgroup D := Q.subgroupOf D
      haveI : Kd.Normal := by
        simpa [D, Kd, sup_comm] using hK_sub_norm_QK
      have htop : Kd ⊔ Qd = ⊤ := by
        calc
          Kd ⊔ Qd = (K ⊔ Q).subgroupOf D := by
            symm
            simpa [D, Kd, Qd, sup_comm] using
              (Subgroup.subgroupOf_sup
                (A := K) (A' := Q) (B := D) le_sup_right le_sup_left)
          _ = ⊤ := by
            exact Subgroup.subgroupOf_eq_top.mpr (by simp [D, sup_comm])
      have hyD : (⟨y, hy⟩ : D) ∈ Kd ⊔ Qd := by
        simp [htop]
      rcases (Subgroup.mem_sup_of_normal_left (x := (⟨y, hy⟩ : D)) (s := Kd) (t := Qd)).1 hyD with
        ⟨kD, hkD, qD, hqD, hy_eq⟩
      have hkK : (kD : G) ∈ K := by
        simpa [Kd, Subgroup.mem_subgroupOf] using hkD
      have hqQ : (qD : G) ∈ Q := by
        simpa [Qd, Subgroup.mem_subgroupOf] using hqD
      have hk_conj : e * (kD : G) * e⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hE_norm_K he) (kD : G)).1 hkK
      have hq_conj : e * (qD : G) * e⁻¹ ∈ Q ⊔ K := by
        have hcommK : ⁅e, (qD : G)⁆ ∈ K := by
          change ⁅e, (qD : G)⁆ ∈ ⁅E, Q⁆
          exact Subgroup.commutator_mem_commutator he hqQ
        have hq_eq :
            e * (qD : G) * e⁻¹ = ⁅e, (qD : G)⁆ * (qD : G) := by
          rw [commutatorElement_def]
          simp [mul_assoc]
        rw [hq_eq]
        exact (Q ⊔ K).mul_mem (Subgroup.mem_sup_right hcommK) (Subgroup.mem_sup_left hqQ)
      have hy_eq' : y = (kD : G) * (qD : G) := by
        have hval := congrArg (fun z : D => (z : G)) hy_eq
        simpa using hval.symm
      have hy_conj_eq :
          e * y * e⁻¹ = (e * (kD : G) * e⁻¹) * (e * (qD : G) * e⁻¹) := by
        rw [hy_eq']
        simp [mul_assoc]
      rw [hy_conj_eq]
      exact (Q ⊔ K).mul_mem (Subgroup.mem_sup_right hk_conj) hq_conj
    have hQK_norm_E : section10NormalIn (Q ⊔ K) E := by
      refine ⟨hQK_le_E, ?_⟩
      have hE_norm_QK : E ≤ Subgroup.normalizer ((Q ⊔ K : Subgroup G) : Set G) := by
        intro e he
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · exact hconj_QK he
        · intro hy
          have hy' := hconj_QK (E.inv_mem he) hy
          simpa [mul_assoc] using hy'
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQK_le_E).2 hE_norm_QK
    have hQK_nil : Group.IsNilpotent (Q ⊔ K : Subgroup G) := by
      letI : IsMulCommutative (Q ⊔ K : Subgroup G) := hKQ_comm
      letI : CommGroup (Q ⊔ K : Subgroup G) := IsMulCommutative.instCommGroup
      infer_instance
    have hQK_le_F : Q ⊔ K ≤ section8FittingSubgroup E := by
      simpa [section8FittingSubgroup] using
        section12_le_fittingSubgroupOf_of_normalIn_nilpotent
          (G := G) (H := E) (N := Q ⊔ K)
          hQK_norm_E.1 hQK_norm_E.2 hQK_nil
    exact hQnotF (le_sup_left.trans hQK_le_F)
  obtain ⟨x₀, hx₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK₀_ne_bot
  obtain ⟨p, z, _hzpow, hzK₀, hzne, hX⟩ :=
    section14_exists_primeOrder_zpowers_in
      (G := G) (B := K₀) x₀.2 (by simpa using hx₀ne)
  have hX_le_K₀ : Subgroup.zpowers z ≤ K₀ := by
    exact hX.1
  have hX_card : Nat.card (Subgroup.zpowers z) = p.val := by
    exact hX.2
  have hX_E : Subgroup.zpowers z ∈ section10PrimeOrderSubgroupsIn p E := by
    exact ⟨hX_le_K₀.trans hK₀_le_E, hX_card⟩
  have hpE : p ∈ subgroupPrimeSet E := by
    have hp_dvd_X : p.val ∣ Nat.card (Subgroup.zpowers z) := by
      simp [hX_card]
    simpa [subgroupPrimeSet] using
      hp_dvd_X.trans (Subgroup.card_dvd_of_le (hX_le_K₀.trans hK₀_le_E))
  have hp_not_sigma : p ∉ section10SigmaPrimes M :=
    section12_not_sigma_of_mem_complement (G := G) (M := M) (E := E) hM.1 hE.1 hpE
  have hM8 : M ∈ section8MaximalSubgroups G := by
    simpa [section8MaximalSubgroups, section9MaximalSubgroups] using hM.1
  have hK₀_le_M : K₀ ≤ M := hK₀_norm_M.1
  have hNK₀_eq_M :
      Subgroup.normalizer (K₀ : Set G) = M :=
    section8_normalizer_eq_of_nontrivial_normal_in_maximal
      hM8 hK₀_le_M hK₀_ne_bot hK₀_norm_M.2
  have hNX_le_M :
      Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ M := by
    let Xsub : Subgroup K₀ := (Subgroup.zpowers z).subgroupOf K₀
    letI : IsCyclic K₀ := hK₀_cyc
    haveI : Xsub.Characteristic :=
      section12_subgroup_characteristic_of_cyclic (H := K₀) Xsub
    have hNK₀_le_NX :
        Subgroup.normalizer (K₀ : Set G) ≤
          Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
      have hnorm :=
        section8_normalizer_map_subtype_le_of_characteristic
          (G := G) (H := K₀) (K := Xsub)
      have hmap_eq : (Xsub.map K₀.subtype : Subgroup G) = Subgroup.zpowers z := by
        calc
          (Xsub.map K₀.subtype : Subgroup G) = Subgroup.zpowers z ⊓ K₀ := by
            simp [Xsub]
          _ = Subgroup.zpowers z := inf_eq_left.mpr hX_le_K₀
      simpa [hmap_eq] using hnorm
    have hM_le_NX : M ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
      rw [← hNK₀_eq_M]
      exact hNK₀_le_NX
    have hNX_eq_M :
        Subgroup.normalizer (Subgroup.zpowers z : Set G) = M :=
      section8_normalizer_eq_of_nontrivial_normal_in_maximal
        hM8 (hX_le_K₀.trans hK₀_le_M) (section12_primeOrder_ne_bot hX)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (hX_le_K₀.trans hK₀_le_M)).2 hM_le_NX)
    rw [hNX_eq_M]
  rcases lemma_10_5
      (G := G) (M := M) (X := Subgroup.zpowers z) (p := p)
      hM.1 hp_not_sigma hX_card hNX_le_M with
    ⟨hprank, _hp_not_ideal, _hAglobal⟩
  have hpτ2 : p ∈ section12Tau2Primes M := by
    simpa [section12Tau2Primes] using ⟨hp_not_sigma, hprank⟩
  obtain ⟨A, hA⟩ :=
    section12_exists_rankTwo_in_E_of_tau2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE hpτ2
  have hX_A : Subgroup.zpowers z ∈ section10PrimeOrderSubgroupsIn p A := by
    have hEq :=
      (corollary_12_6_a
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM.1 hE hpτ2 hA).2
    exact hEq ▸ hX_E
  have hX_le_A : Subgroup.zpowers z ≤ A := by
    exact hX_A.1
  have hAQ_ne : ⁅A, Q⁆ ≠ ⊥ := by
    intro hAQbot
    have hA_le_cent_Q : A ≤ Subgroup.centralizer (Q : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer : ⁅A, Q⁆ = ⊥ ↔
        A ≤ Subgroup.centralizer (Q : Set G)).mp hAQbot
    have hX_le_CK₀ : Subgroup.zpowers z ≤ subgroupCentralizerIn K₀ Q := by
      intro x hx
      exact ⟨hX_le_K₀ hx, hA_le_cent_Q (hX_le_A hx)⟩
    have hXbot : Subgroup.zpowers z = ⊥ := by
      apply le_bot_iff.mp
      rw [← hCK₀bot]
      exact hX_le_CK₀
    exact (section12_primeOrder_ne_bot hX) hXbot
  have hAnorm : section10NormalIn A E :=
    (corollary_12_6_a
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM.1 hE hpτ2 hA).1
  let C : Subgroup G := subgroupCentralizerIn E A
  have hCnorm : section10NormalIn C E :=
    section14_subgroupCentralizerIn_normal_of_normal
      (G := G) (E := E) (A := A) hAnorm
  have hQ_not_le_C : ¬ Q ≤ C := by
    intro hQC
    have hA_le_cent_Q : A ≤ Subgroup.centralizer (Q : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro q' hq'
      exact ((hQC hq').2 a ha).symm
    exact hAQ_ne
      ((Subgroup.commutator_eq_bot_iff_le_centralizer : ⁅A, Q⁆ = ⊥ ↔
        A ≤ Subgroup.centralizer (Q : Set G)).2 hA_le_cent_Q)
  have hQ_inf_C_bot : Q ⊓ C = ⊥ := by
    let R : Subgroup Q := (Q ⊓ C).subgroupOf Q
    haveI : Fact (Nat.card Q).Prime := by
      rw [hQ.2]
      exact ⟨q.2⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (G := Q) R with hRbot | hRtop
    · apply le_bot_iff.mp
      intro x hx
      have hxR : (⟨x, hx.1⟩ : Q) ∈ R := by
        simpa [R, Subgroup.mem_subgroupOf] using hx.2
      have hxbot : (⟨x, hx.1⟩ : Q) ∈ (⊥ : Subgroup Q) := by
        simpa [hRbot] using hxR
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)
    · have hQ_le_C : Q ≤ C := by
        intro x hxQ
        have hxR : (⟨x, hxQ⟩ : Q) ∈ R := by
          simp [R, hRtop]
        simpa [R, Subgroup.mem_subgroupOf] using hxR
      exact False.elim (hQ_not_le_C hQ_le_C)
  have hQ_norm_C : Q ≤ Subgroup.normalizer (C : Set G) :=
    hQ.1.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hCnorm.1).1 hCnorm.2)
  let D : Subgroup G := Q ⊔ C
  have hcompCQ : (C.subgroupOf D).IsComplement' (Q.subgroupOf D) := by
    simpa [D, sup_comm, inf_comm] using
      section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
        (G := G) (H := C) (R := Q) hQ_norm_C (by simpa [inf_comm] using hQ_inf_C_bot)
  have hq_rel_D : q.val ∣ C.relIndex D := by
    have hQsub_card : Nat.card (Q.subgroupOf D) = q.val := by
      calc
        Nat.card (Q.subgroupOf D) = Nat.card Q := by
          simpa [D] using section12_card_subgroupOf_eq (H := Q) (K := D) le_sup_left
        _ = q.val := hQ.2
    have hq_idx : q.val ∣ (C.subgroupOf D).index := by
      have hq_card : q.val ∣ Nat.card (Q.subgroupOf D) := by
        simp [hQsub_card]
      simpa [hcompCQ.symm.index_eq_card] using hq_card
    simpa [Subgroup.relIndex] using hq_idx
  have hD_le_E : D ≤ E := by
    exact sup_le hQ.1 inf_le_left
  have hCsub_le_Dsub : C.subgroupOf E ≤ D.subgroupOf E := by
    intro x hx
    simpa [D, Subgroup.mem_subgroupOf] using (le_sup_right : C ≤ Q ⊔ C) hx
  have hrel_eq :
      (C.subgroupOf E).relIndex (D.subgroupOf E) = C.relIndex D := by
    simpa using
      (Subgroup.relIndex_subgroupOf
        (H := C) (K := D) (L := E) (hKL := hD_le_E))
  have hq_idx_E : q.val ∣ (C.subgroupOf E).index :=
    (hrel_eq.symm ▸ hq_rel_D).trans
      (Subgroup.relIndex_dvd_index_of_le hCsub_le_Dsub)
  refine ⟨p, A, hpτ2, hA, hAQ_ne, ?_⟩
  exact ⟨inf_le_left, hq_idx_E⟩

/-- Lemma 14.11: maximal subgroups of type `𝓕` with a prime-order subgroup
outside the Fitting subgroup give the stated `τ₂` or `κ` alternative. -/
public theorem CFSG.lemma_14_11
    {M E Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section14MFamilyF G)
    (hE : section12ComplementToMsigma M E)
    (hq : q ∈ subgroupPrimeSet E)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q E)
    (hQnotF : ¬ Q ≤ section8FittingSubgroup E) :
    ∃ Mstar : Subgroup G,
      Mstar ∈ section9MaximalSubgroups G ∧
        ((q ∈ section12Tau2Primes Mstar ∧
            section9MaximalSubgroupsContaining (Subgroup.centralizer (Q : Set G)) =
              {Mstar}) ∨
          (q ∈ section14KappaPrimes Mstar ∧
            Mstar ∈ section14MFamilyP1 G)) ∧
        section14Theorem12_7Corollary12_9Situation M E Q Mstar q := by
  classical
  obtain ⟨E₁₂, E₁, E₂, E₃, hEdata⟩ :=
    section14_exists_EData_of_complement
      (G := G) (M := M) (E := E) hM.1 hE
  have hqτ1 :=
    section14_lemma_14_11_tau1
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q)
      hM hEdata hq hQ hQnotF
  have hCQbot :=
    section14_lemma_14_11_msigma_centralizer_bot
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q)
      hM hEdata hq hQ hQnotF
  obtain ⟨p, A, hpτ2, hA, hAQ_ne, hqQuot⟩ :=
    section14_lemma_14_11_exists_rankTwo_nontrivial_commutator
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q)
      hM hEdata hq hQ hQnotF
  have h12_9a :=
    corollary_12_9_a
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (A := A) (Q := Q) (p := p) (q := q)
      hM.1 hEdata hpτ2 hA hqτ1 hQ hCQbot hAQ_ne
  have h12_9b :=
    corollary_12_9_b
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (A := A) (Q := Q) (p := p) (q := q)
      hM.1 hEdata hpτ2 hA hqτ1 hQ hCQbot hAQ_ne
  have h12_9c :=
    corollary_12_9_c
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (A := A) (Q := Q) (p := p) (q := q)
      hM.1 hEdata hpτ2 hA hqτ1 hQ hCQbot hAQ_ne
  rcases h12_9a with ⟨hA₀prime, hA₀eq, hA₀normM⟩
  rcases h12_9c with ⟨hA₁prime, hCA₁_not_le_M⟩
  have hA₀_not_conj :
      ¬ section14ConjugateSubgroups ⁅A, Q⁆ (subgroupCentralizerIn A Q) := by
    intro hconj
    rcases hconj with ⟨g, hg⟩
    have hg' : (⁅A, Q⁆).conjBy g⁻¹ = subgroupCentralizerIn A Q := by
      simpa [section11_conjBy_inv] using congrArg (fun H => H.conjBy g⁻¹) hg
    exact h12_9b g⁻¹ hg'
  have hA_ne_top : A ≠ ⊤ := by
    intro htop
    haveI : Fact p.val.Prime := ⟨p.2⟩
    have hElem := (section12_rankTwo_elementary hA).2
    haveI : IsElementaryAbelian p.val A := hElem
    have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
    have htop_p : IsPGroup p.val (⊤ : Subgroup G) :=
      hAp.of_equiv (MulEquiv.subgroupCongr htop)
    have hGp : IsPGroup p.val G :=
      htop_p.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    haveI : Group.IsNilpotent G :=
      IsPGroup.isNilpotent (p := p.val) (G := G) (h := hGp)
    exact IsMinCE.not_solvable (G := G) (inferInstance : Group.IsSolvable G)
  have hNA_ne_top : Subgroup.normalizer (A : Set G) ≠ ⊤ := by
    intro hNtop
    have hAnormG : A.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    letI : IsSimpleGroup G := IsMinCE.simple
    rcases hAnormG.eq_bot_or_eq_top with hAbot | hAtop
    · exact section12_rankTwo_ne_bot hA hAbot
    · exact hA_ne_top hAtop
  obtain ⟨Mstar, hMstarCont⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) (H := Subgroup.normalizer (A : Set G)) hNA_ne_top
  have hMstar_max : Mstar ∈ section9MaximalSubgroups G := hMstarCont.1
  have hAnormE :
      section10NormalIn A E :=
    (corollary_12_6_a
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM.1 hEdata hpτ2 hA).1
  have hE_le_normA : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAnormE.1).1 hAnormE.2
  have hE_le_Mstar : E ≤ Mstar := hE_le_normA.trans hMstarCont.2
  have hQ_Mstar : Q ∈ section10PrimeOrderSubgroupsIn q Mstar := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hQ.1.trans hE_le_Mstar, hQ.2⟩
  have hqτstar :
      q ∈ section12Tau1Primes Mstar ∪ section12Tau2Primes Mstar :=
    lemma_12_11_b
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (A := A) (Mstar := Mstar) (p := p)
      hM.1 hEdata hpτ2 hA hMstarCont hqQuot
  have hpσβstar :
      p ∈ section10SigmaPrimes Mstar ∧ p ∉ section10BetaPrimes Mstar :=
    (lemma_12_11_a
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (A := A) (Mstar := Mstar) (p := p)
      hM.1 hEdata hpτ2 hA hMstarCont) hpτ2
  have hA_Mstar : A ∈ section12RankTwoElementaryAbelianIn p Mstar :=
    section12_rankTwo_mono hA hE_le_Mstar
  have hA_le_msigma_star : A ≤ section10Msigma Mstar :=
    section12_rankTwo_le_msigma_of_sigma
      (G := G) (M := Mstar) (A := A) (p := p)
      hMstar_max hpσβstar.1 hA_Mstar
  rcases hqτstar with hqτ1star | hqτ2star
  · have hCstar_ne_bot : subgroupCentralizerIn (section10Msigma Mstar) Q ≠ ⊥ := by
      have hA₁_le_C : subgroupCentralizerIn A Q ≤ subgroupCentralizerIn (section10Msigma Mstar) Q := by
        intro x hx
        exact ⟨hA_le_msigma_star hx.1, hx.2⟩
      intro hbot
      exact section12_primeOrder_ne_bot hA₁prime
        (le_bot_iff.mp (hA₁_le_C.trans (by simp [hbot])))
    have hqκ : q ∈ section14KappaPrimes Mstar := by
      exact ⟨Or.inl hqτ1star, ⟨Q, hQ_Mstar, hCstar_ne_bot⟩⟩
    have hMstarP : Mstar ∈ section14MFamilyP G := ⟨hMstar_max, ⟨q, hqκ⟩⟩
    have hMstar_not_P2 : Mstar ∉ section14MFamilyP2 G := by
      intro hP2
      have hsolvMstar : Group.IsSolvable Mstar :=
        section14_solvable_of_le_maximal (G := G) hMstar_max le_rfl
      obtain ⟨Kstar, hKstar⟩ :=
        section14_exists_hallSubgroupIn
          (G := G) (H := Mstar) hsolvMstar (section14KappaPrimes Mstar)
      have hσ_eq_β :=
        (proposition_14_2_g
          (G := G) (M := Mstar) (K := Kstar) hP2 hKstar).1
      exact hpσβstar.2 (hσ_eq_β ▸ hpσβstar.1)
    have hMstarP1 : Mstar ∈ section14MFamilyP1 G := by
      refine ⟨hMstarP, ?_⟩
      by_contra hneq
      exact hMstar_not_P2 ⟨hMstarP, hneq⟩
    refine ⟨Mstar, hMstar_max, Or.inr ⟨hqκ, hMstarP1⟩, ?_⟩
    refine ⟨p, A, ⁅A, Q⁆, subgroupCentralizerIn A Q, hpτ2, hA, hqτ1, hQ, hCQbot,
      hqQuot, rfl, hA₀eq, hA₀prime, hA₀normM, hA₀_not_conj, rfl,
      hA₁prime, hCA₁_not_le_M, hMstarCont⟩
  · have hQ_ne_bot : Q ≠ ⊥ := section12_primeOrder_ne_bot hQ
    obtain ⟨xQ, hxQne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ_ne_bot
    obtain ⟨_qz, z, _hz_zpowQ, hzQ, hzne, hzprimeQ⟩ :=
      section14_exists_primeOrder_zpowers_in
        (G := G) (B := Q) xQ.2 (by simpa using hxQne)
    have hzQ_le : Subgroup.zpowers z ≤ Q := by
      exact
        (show Subgroup.zpowers z ≤ Q ∧ Nat.card (Subgroup.zpowers z) = _ from by
          simpa [section10PrimeOrderSubgroupsIn] using hzprimeQ).1
    have hQ_card_prime : Nat.Prime (Nat.card Q) := by
      rw [hQ.2]
      exact q.2
    have hzpow_eq_Q : Subgroup.zpowers z = Q := by
      exact section14_subgroup_eq_of_le_prime_card
        hzQ_le hQ_card_prime (section12_primeOrder_ne_bot hzprimeQ)
    have hZprime : Nat.card (Subgroup.zpowers z) = q.val := by
      simpa [hzpow_eq_Q] using hQ.2
    have hA₁_le_cent_z :
        subgroupCentralizerIn A Q ≤ elementCentralizerIn (section10Msigma Mstar) z := by
      intro x hx
      refine ⟨hA_le_msigma_star hx.1, ?_⟩
      change x ∈ Subgroup.centralizer ({z} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy_eq : y = z := by simpa using hy
      simpa [hy_eq] using hx.2 z hzQ
    have hcentz_ne_bot : elementCentralizerIn (section10Msigma Mstar) z ≠ ⊥ := by
      intro hbot
      exact section12_primeOrder_ne_bot hA₁prime
        (le_bot_iff.mp (hA₁_le_cent_z.trans (by simp [hbot])))
    have hz_tau2 :
        subgroupPrimeSet (Subgroup.zpowers z) ⊆ section12Tau2Primes Mstar := by
      intro r hr
      have hrQ : r ∈ subgroupPrimeSet Q := by
        simpa [hzpow_eq_Q] using hr
      have hrdiv : r.val ∣ Nat.card Q := by
        simpa [subgroupPrimeSet] using hrQ
      have hr_eq_q : r = q := by
        apply Subtype.ext
        exact (Nat.prime_dvd_prime_iff_eq r.2 q.2).1 (by simpa [hQ.2] using hrdiv)
      simpa [hr_eq_q] using hqτ2star
    have huniq_z :
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({z} : Set G)) = {Mstar} := by
      have hbot_pi : IsPiSubgroup (G := G) (section10SigmaPrimes Mstar)ᶜ (⊥ : Subgroup G) := by
        intro r hr
        simp [r.2.ne_one] at hr
      obtain ⟨Estar, hEstar_comp, _hbotEstar⟩ :=
        section14_exists_sigma_complement_containing
          (G := G) (M := Mstar) (K := ⊥) hMstar_max bot_le hbot_pi
      obtain ⟨E₁₂star, E₁star, E₂star, E₃star, hEstar⟩ :=
        section14_exists_EData_of_complement
          (G := G) (M := Mstar) (E := Estar) hMstar_max hEstar_comp
      exact corollary_12_10_e
        (G := G) (M := Mstar) (E := Estar) (E₁₂ := E₁₂star)
        (E₁ := E₁star) (E₂ := E₂star) (E₃ := E₃star) (x := z)
        hMstar_max hEstar (hQ_Mstar.1 (by simpa [hzpow_eq_Q] using Subgroup.mem_zpowers z))
        hzne hz_tau2 hcentz_ne_bot
    have hcent_singleton_eq :
        Subgroup.centralizer ({z} : Set G) =
          Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_centralizer_iff] at hx ⊢
        intro y hy
        rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
        have hzcomm : Commute z x := hx z (by simp)
        exact (hzcomm.zpow_left n).eq
      · intro hx
        rw [Subgroup.mem_centralizer_iff] at hx ⊢
        intro y hy
        have hzpow : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
        have hy_eq : y = z := by simpa using hy
        simpa [hy_eq] using hx z hzpow
    have huniq_zpow :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (Subgroup.zpowers z : Set G)) =
          {Mstar} := by
      simpa [hcent_singleton_eq] using huniq_z
    have huniq_Q :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (Q : Set G)) = {Mstar} := by
      simpa [hzpow_eq_Q] using huniq_zpow
    refine ⟨Mstar, hMstar_max, Or.inl ⟨hqτ2star, huniq_Q⟩, ?_⟩
    refine ⟨p, A, ⁅A, Q⁆, subgroupCentralizerIn A Q, hpτ2, hA, hqτ1, hQ, hCQbot,
      hqQuot, rfl, hA₀eq, hA₀prime, hA₀normM, hA₀_not_conj, rfl,
      hA₁prime, hCA₁_not_le_M, hMstarCont⟩

end Section14
