module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.RankThree.PartTwo.Sec3.Item38Tools
import CFSG.RankThree.PartTwo.Sec3.TwoGroupPrimeFiveAction
import CFSG.RankThree.PartOne.S10.FaithfulPlaneTwoActionOnPrimeGroup
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary
import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankWithout
import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientBM
import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientKernelElimination
import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingSelectedBase
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec3

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Faithful

omit [Finite G] in
theorem commutator_ne_bot_of_faithful {E S X : Subgroup G}
    (hEf : E ⊓ Subgroup.centralizer (S : Set G) = ⊥) (hXE : X ≤ E) {x : G} (hxX : x ∈ X)
    (hx1 : x ≠ 1) : ⁅S, X⁆ ≠ ⊥ := by
  intro h
  have hSX := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hx : x ∈ E ⊓ Subgroup.centralizer (S : Set G) :=
    ⟨hXE hxX, Subgroup.mem_centralizer_iff.mpr fun s hs =>
      (Subgroup.mem_centralizer_iff.mp (hSX hs) x hxX).symm⟩
  rw [hEf, Subgroup.mem_bot] at hx
  exact hx1 hx

end Faithful

section Large

theorem two_lt_localRank_of_ne_five {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p)
    (hq3 : 3 < q) (hp5 : p ≠ 5) {E S Q : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian p E)
    (hE1 : E ≠ ⊥) (hS : IsPGroup 2 S) (hQ : IsPGroup q Q)
    (hES : E ≤ Subgroup.normalizer (S : Set G))
    (hEf : E ⊓ Subgroup.centralizer (S : Set G) = ⊥)
    (hESQ : E ⊔ S ≤ Subgroup.normalizer (Q : Set G))
    (hESf : (E ⊔ S) ⊓ Subgroup.centralizer (Q : Set G) = ⊥) : 2 < localRank q G := by
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : q ≠ 2 := by omega
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨e, heE⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have hep : orderOf e = p := orderOf_eq_prime (hE.2 e heE) he1'
  set X := Subgroup.zpowers e with hXdef
  have hXp : Nat.card X = p := by rw [hXdef, Nat.card_zpowers, hep]
  have hXE : X ≤ E := Subgroup.zpowers_le.mpr heE
  have hXS : X ≤ Subgroup.normalizer (S : Set G) := hXE.trans hES
  have hX : IsPGroup p X := IsPGroup.of_card (n := 1) (by rw [hXp, pow_one])
  have hcopS : Nat.Coprime p (Nat.card S) := by
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  set U := ⁅S, X⁆ with hUdef
  have hUS : U ≤ S := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing S X hXS
  have hUX : ⁅U, X⁆ = U :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent p hp X S hX hXS hcopS
  have hU1 : U ≠ ⊥ :=
    commutator_ne_bot_of_faithful hEf hXE (Subgroup.mem_zpowers e) he1'
  have hU2 : IsPGroup 2 U := hS.to_le hUS
  have hUf : U ⊓ Subgroup.centralizer (Q : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ (hUS.trans le_sup_right)).trans hESf.le)
  have h5 := rank3II_3_6 hq hq2 hp hp3 hQ hU2 hXp hUX hU1
    (hUS.trans (le_sup_right.trans hESQ)) (hXE.trans (le_sup_left.trans hESQ)) hUf
    fun u hu hu1 => by
      rw [assembly_pRank_eq hq]
      exact (Lifting36.pRank_centralizer_le_localRank hq Q hU2 hu hu1).trans hcon
  exact hp5 h5

end Large

section Elem

omit [Finite G] in
theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

omit [Finite G] in
theorem isElementaryAbelian_of_le_isElemAbelian {p : ℕ} {E B : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian p E) (hBE : B ≤ E) : CFSG.IsElementaryAbelian p ↥B :=
  { toIsMulCommutative := ⟨⟨fun x y => by
      have h : (x : G) * y = y * x := congrArg Subtype.val
        (hE.1.is_comm.comm ⟨(x : G), hBE x.2⟩ ⟨(y : G), hBE y.2⟩)
      exact Subtype.ext h⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa using hE.2 x (hBE x.2)) }

omit [Finite G] in
theorem exists_le_card_eq_sq {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian p E) (hE2 : p ^ 2 ≤ Nat.card E) :
    ∃ B ≤ E, Nat.card B = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨B', -, hB'⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card hp
    (isPGroup_of_isElemAbelian hE) (H := ⊤) (by rwa [Subgroup.card_top])
  exact ⟨B'.map E.subtype, Subgroup.map_subtype_le _,
    by rw [Subgroup.card_map_of_injective E.subtype_injective, hB']⟩

end Elem

section FiveOther

theorem two_lt_localRank_of_five_of_ne {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hq5 : q ≠ 5)
    {E S Q : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 5 E) (hE25 : 25 ≤ Nat.card E)
    (hS : IsPGroup 2 S) (hQ : IsPGroup q Q) (hES : E ≤ Subgroup.normalizer (S : Set G))
    (hEf : E ⊓ Subgroup.centralizer (S : Set G) = ⊥)
    (hESQ : E ⊔ S ≤ Subgroup.normalizer (Q : Set G))
    (hESf : (E ⊔ S) ⊓ Subgroup.centralizer (Q : Set G) = ⊥) : 2 < localRank q G := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq2 : q ≠ 2 := by omega
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hBE, hB25⟩ := exists_le_card_eq_sq (by norm_num) hE (by norm_num; omega)
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := hBE.trans hES
  have hSQ : S ≤ Subgroup.normalizer (Q : Set G) := le_sup_right.trans hESQ
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) := le_sup_left.trans hESQ
  have hSf : S ⊓ Subgroup.centralizer (Q : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ le_sup_right).trans hESf.le)
  have hE1 : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE25
    omega
  have hS1 : S ≠ ⊥ := by
    intro h
    apply hE1
    rw [eq_bot_iff, ← hEf]
    refine fun x hx => ⟨hx, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hs' : s ∈ (⊥ : Subgroup G) := h ▸ hs
    rw [Subgroup.mem_bot] at hs'
    rw [hs', one_mul, mul_one]
  obtain ⟨D, hDQ, hND, hDexp, hDcomm, hSD⟩ := exists_critical_subgroup hq2 hQ hS hSQ hSf hS1
  have hDq : IsPGroup q D := hQ.to_le hDQ
  have hDcl : ⁅⁅D, D⁆, D⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx d hd
    have hxc : x ∈ Subgroup.centralizer (D : Set G) := by
      rw [← SetLike.mem_coe] at hx
      refine (Subgroup.closure_le _).mpr ?_ (Subgroup.commutator_def D D ▸ hx)
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact Subgroup.mem_centralizer_iff.mpr fun c hc => (hDcomm a ha b hb c hc).symm
    rw [Subgroup.mem_bot, commutatorElement_def,
      (Subgroup.mem_centralizer_iff.mp hxc d hd).symm, mul_inv_cancel_right, mul_inv_cancel]
  have hBD : B ≤ Subgroup.normalizer (D : Set G) := (hBE.trans hEQ).trans hND
  have hSD' : S ≤ Subgroup.normalizer (D : Set G) := hSQ.trans hND
  have hB5 : IsPGroup 5 B := (isPGroup_of_isElemAbelian hE).to_le hBE
  have hcopS : Nat.Coprime 5 (Nat.card S) := by
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hB1 : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB25
    norm_num at hB25
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  have h0 : ⁅S, B⁆ ∈ {U : Subgroup G | U ≤ S ∧ B ≤ Subgroup.normalizer (U : Set G) ∧
      ⁅U, B⁆ = U ∧ ¬ U ≤ Subgroup.centralizer (D : Set G)} := by
    refine ⟨CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing S B hBS,
      CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized B S hBS,
      CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 5 (by norm_num) B S
        hB5 hBS hcopS, fun hle => ?_⟩
    have hbot : ⁅S, B⁆ ≤ S ⊓ Subgroup.centralizer (D : Set G) :=
      le_inf (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing S B hBS) hle
    rw [hSD, le_bot_iff] at hbot
    exact commutator_ne_bot_of_faithful hEf hBE hbB (fun h => hb1 (Subtype.ext h)) hbot
  obtain ⟨R, ⟨hRS, hBR, hRB, hRD⟩, hRmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min _ ⟨_, h0⟩
  have hR2 : IsPGroup 2 R := hS.to_le hRS
  have hset : MinTwoActionSetting 5 q B D R :=
    { prime_p := by norm_num
      prime_q := hq
      three_lt_p := by norm_num
      q_ne_two := hq2
      p_ne_q := fun h => hq5 h.symm
      A_elem := isElementaryAbelian_of_le_isElemAbelian hE hBE
      A_card := by rw [hB25]
      D_inv := sup_le (hRS.trans hSD') hBD
      D_pgroup := hDq
      D_exp := hDexp
      D_class := hDcl
      R_two := hR2
      R_inv := hBR
      R_comm := hRB
      R_ne := fun h => hRD (h ▸ bot_le)
      R_act := fun h => hRD (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
      R_min := fun U hUR hBU hUB => by
        by_contra hUD
        exact hRmin U ⟨hUR.le.trans hRS, hBU, hUB, hUD⟩ hUR }
  have hrank2 : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2 :=
    fun r hr hr1 => (Lifting36.pRank_centralizer_le_localRank hq D hR2 hr hr1).trans hcon
  obtain ⟨-, ⟨eR⟩, -, hQD⟩ := minimalTwoActionWithoutRankThreeFixedGroup_of
    minimalTwoActionSmallFaithfulQuotient elementaryFaithfulQuotientKernelElimination G 5 q B D R
    hset hrank2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hBR5, -⟩ :=
    minimalTwoActionSmallFaithfulQuotient G 5 q B D R hset fun r hr hr1 =>
      (hrank2 r hr hr1).trans (by norm_num)
  have hRext : IsExtraspecialPGroup 2 ↥R := Lifting36.isExtraspecialPGroup_of_mulEquiv eR.symm
    (CFSG.RankThree.GroupTheory.SteinbergBY.quaternion_dihedral_extraspecial_involution_generation
      |>.2.1)
  have hRcard : Nat.card R = 2 ^ (1 + 2 * 2) := by
    rw [Nat.card_congr eR.toEquiv, CFSG.RankThree.GroupTheory.card_QD32]
    norm_num
  have hRf : R ⊓ Subgroup.centralizer (D : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hRS).trans hSD.le)
  have hBRne : B ⊓ Subgroup.centralizer (R : Set G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBR5
    omega
  obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBRne
  have hb₀1' : b₀ ≠ 1 := fun h => hb₀1 (Subtype.ext h)
  have hLD : S ⊔ B ≤ Subgroup.normalizer (D : Set G) := sup_le hSD' hBD
  have hb₀S : b₀ ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hk : s * b₀ * s⁻¹ * b₀⁻¹ ∈ S := by
      have : b₀ * s⁻¹ * b₀⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hBS hb₀.1) s⁻¹).mp (inv_mem hs)
      have e : s * b₀ * s⁻¹ * b₀⁻¹ = s * (b₀ * s⁻¹ * b₀⁻¹) := by group
      rw [e]
      exact mul_mem hs this
    have hko : ¬ q ∣ orderOf (s * b₀ * s⁻¹ * b₀⁻¹) := by
      intro hdvd
      obtain ⟨k, hk2⟩ := (IsPGroup.iff_orderOf.mp hS) ⟨_, hk⟩
      rw [Subgroup.orderOf_mk] at hk2
      rw [hk2] at hdvd
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))
    have hkD := commutator_mem_centralizer_of_scalar hq hq2 hLD hDq (hRS.trans le_sup_left) hR2
      hRf hRext hRcard (Lifting36.relIndex_frattini_of_isQDShape hq hQD)
      (Subgroup.mem_sup_right hb₀.1) hb₀.2 (Subgroup.mem_sup_left hs) hko
    have hk1 : s * b₀ * s⁻¹ * b₀⁻¹ ∈ S ⊓ Subgroup.centralizer (D : Set G) := ⟨hk, hkD⟩
    rw [hSD, Subgroup.mem_bot] at hk1
    calc s * b₀ = s * b₀ * s⁻¹ * b₀⁻¹ * (b₀ * s) := by group
      _ = b₀ * s := by rw [hk1, one_mul]
  have hb₀E : b₀ ∈ E ⊓ Subgroup.centralizer (S : Set G) := ⟨hBE hb₀.1, hb₀S⟩
  rw [hEf, Subgroup.mem_bot] at hb₀E
  exact hb₀1' hb₀E

end FiveOther

section FiveFive

omit [Finite G] in
theorem eq_of_prime_dvd_card_of_isPGroup {r p : ℕ} (hr : r.Prime) (hp : p.Prime) {H : Type*}
    [Group H] [Finite H] (hH : IsPGroup p H) (hd : r ∣ Nat.card H) : r = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  rw [hn] at hd
  exact (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hd)

theorem three_lt_localRank_of_five_five {E S Q : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian 5 E) (hE25 : 25 ≤ Nat.card E) (hS : IsPGroup 2 S)
    (hQ : IsPGroup 5 Q) (hES : E ≤ Subgroup.normalizer (S : Set G))
    (hEf : E ⊓ Subgroup.centralizer (S : Set G) = ⊥)
    (hESQ : E ⊔ S ≤ Subgroup.normalizer (Q : Set G))
    (hESf : (E ⊔ S) ⊓ Subgroup.centralizer (Q : Set G) = ⊥) : 3 < localRank 5 G := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, hBE, hB25⟩ := exists_le_card_eq_sq (by norm_num) hE (by norm_num; omega)
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := hBE.trans hES
  have hSQ : S ≤ Subgroup.normalizer (Q : Set G) := le_sup_right.trans hESQ
  have hB5 : IsPGroup 5 B := (isPGroup_of_isElemAbelian hE).to_le hBE
  have hSB : Disjoint S B := IsPGroup.disjoint_of_ne 2 5 (by norm_num) S B hS hB5
  have hSQd : Disjoint S Q := IsPGroup.disjoint_of_ne 2 5 (by norm_num) S Q hS hQ
  let _ : MulDistribMulAction ↥B ↥S := Subgroup.conjMulDistribMulActionOfLeNormalizer B S hBS
  have hsmul : ∀ (b : ↥B) (s : ↥S), ((b • s : ↥S) : G) = (b : G) * s * (b : G)⁻¹ :=
    fun _ _ => rfl
  have hfaith : ∀ c : ↥B, (∀ s : ↥S, c • s = s) → c = 1 := by
    intro c hc
    have hcS : (c : G) ∈ E ⊓ Subgroup.centralizer (S : Set G) := by
      refine ⟨hBE c.2, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      have h1 : (c : G) * s * (c : G)⁻¹ = s := by
        rw [← hsmul c ⟨s, hs⟩, hc ⟨s, hs⟩]
      calc s * c = (c : G) * s * (c : G)⁻¹ * c := by rw [h1]
        _ = c * s := by group
    rw [hEf, Subgroup.mem_bot] at hcS
    exact Subtype.ext hcS
  let φ : ↥S ⋊[MulDistribMulAction.toMulAut ↥B ↥S] ↥B →* G :=
    SemidirectProduct.lift S.subtype B.subtype fun b => MonoidHom.ext fun s => rfl
  have hφ : ∀ x, φ x = (x.left : G) * x.right := fun _ => rfl
  have hφmem : ∀ x, φ x ∈ E ⊔ S := fun x =>
    mul_mem (Subgroup.mem_sup_right x.left.2) (Subgroup.mem_sup_left (hBE x.right.2))
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hφ] at hx
    have hl : (x.left : G) = (x.right : G)⁻¹ := eq_inv_of_mul_eq_one_left hx
    have hlB : (x.left : G) ∈ B := hl ▸ inv_mem x.right.2
    have h1 : (x.left : G) = 1 := Subgroup.disjoint_def.mp hSB x.left.2 hlB
    have h2 : (x.right : G) = 1 := by
      rw [h1, one_mul] at hx
      exact hx
    exact SemidirectProduct.ext (Subtype.ext h1) (Subtype.ext h2)
  have hφN : ∀ x, φ x ∈ Subgroup.normalizer (Q : Set G) := fun x => hESQ (hφmem x)
  let β : (↥S ⋊[MulDistribMulAction.toMulAut ↥B ↥S] ↥B) →* MulAut ↥Q :=
    Q.normalizerMonoidHom.comp (φ.codRestrict _ hφN)
  have hβ : ∀ x (y : ↥Q), ((β x y : ↥Q) : G) = φ x * y * (φ x)⁻¹ := fun x y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨φ x, hφN x⟩ y
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : φ x ∈ Subgroup.centralizer (Q : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have h1 : ((β x ⟨y, hy⟩ : ↥Q) : G) = y := by rw [hx]; rfl
      rw [hβ] at h1
      calc y * φ x = φ x * y * (φ x)⁻¹ * φ x := by rw [h1]
        _ = φ x * y := by group
    have hmem : φ x ∈ (E ⊔ S) ⊓ Subgroup.centralizer (Q : Set G) := ⟨hφmem x, hxC⟩
    rw [hESf, Subgroup.mem_bot] at hmem
    exact hφinj (hmem.trans (map_one φ).symm)
  have h39 := faithful_plane_two_action_on_defining_prime_group_rank_obstruction 5 (by norm_num)
    (by norm_num) ↥B ↥S (isElementaryAbelian_of_le_isElemAbelian hE hBE) (by rw [hB25]) hS
    hfaith ↥Q hQ β hβinj
  let ι : ↥Q ⋊[β] (↥S ⋊[MulDistribMulAction.toMulAut ↥B ↥S] ↥B) →* G :=
    SemidirectProduct.lift Q.subtype φ fun k => MonoidHom.ext fun y => hβ k y
  have hι : ∀ x, ι x = (x.left : G) * φ x.right := fun _ => rfl
  have hQφ : ∀ k, φ k ∈ Q → k = 1 := by
    intro k hk
    set s : ↥S := k.left
    set b : ↥B := k.right
    have hkx : φ k = (s : G) * b := hφ k
    have hcomm : ∀ t : ↥S, φ k * t = t * φ k := by
      intro t
      have hkN : φ k ∈ Subgroup.normalizer (S : Set G) := by
        rw [hkx]
        exact mul_mem (Subgroup.le_normalizer s.2) (hBS b.2)
      have h1 : φ k * t * (φ k)⁻¹ * (t : G)⁻¹ ∈ S :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp hkN t).mp t.2) (inv_mem t.2)
      have h2 : φ k * t * (φ k)⁻¹ * (t : G)⁻¹ ∈ Q := by
        have : (t : G) * (φ k)⁻¹ * (t : G)⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp (hSQ t.2) (φ k)⁻¹).mp (inv_mem hk)
        have e : φ k * t * (φ k)⁻¹ * (t : G)⁻¹ = φ k * ((t : G) * (φ k)⁻¹ * (t : G)⁻¹) := by group
        rw [e]
        exact mul_mem hk this
      have h3 : φ k * t * (φ k)⁻¹ * (t : G)⁻¹ = 1 := Subgroup.disjoint_def.mp hSQd h1 h2
      calc φ k * t = φ k * t * (φ k)⁻¹ * (t : G)⁻¹ * (t * φ k) := by group
        _ = t * φ k := by rw [h3, one_mul]
    have hinner : ∀ t : ↥S, b • t = s⁻¹ * t * s := by
      intro t
      apply Subtype.ext
      rw [hsmul]
      have h1 := hcomm t
      rw [hkx] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (b : G) * t * (b : G)⁻¹ = (s : G)⁻¹ * ((s : G) * b * t) * (b : G)⁻¹ := by group
        _ = (s : G)⁻¹ * (t * ((s : G) * b)) * (b : G)⁻¹ := by rw [h1]
        _ = (s : G)⁻¹ * t * s := by group
    have hb1 : b = 1 := PlaneAux.eq_one_of_smul_eq_inner (by norm_num) (by norm_num) hB5 hS hfaith
      hinner
    have hs1 : (s : G) = 1 := by
      have hsQ : (s : G) ∈ Q := by
        have := hk
        rw [hkx, hb1, Subgroup.coe_one, mul_one] at this
        exact this
      exact Subgroup.disjoint_def.mp hSQd s.2 hsQ
    exact SemidirectProduct.ext (Subtype.ext hs1) hb1
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hι] at hx
    have hy : (x.left : G) = (φ x.right)⁻¹ := eq_inv_of_mul_eq_one_left hx
    have hk : x.right⁻¹ = 1 := hQφ x.right⁻¹ (by rw [map_inv, ← hy]; exact x.left.2)
    have hk1 : x.right = 1 := inv_eq_one.mp hk
    have hy1 : (x.left : G) = 1 := by rw [hy, hk1, map_one, inv_one]
    exact SemidirectProduct.ext (Subtype.ext hy1) hk1
  have hcard : ∀ r : ℕ, r.Prime →
      r ∣ Nat.card (↥Q ⋊[β] (↥S ⋊[MulDistribMulAction.toMulAut ↥B ↥S] ↥B)) → r = 2 ∨ r = 5 := by
    intro r hr hd
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
      Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod] at hd
    rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
    · exact Or.inr (eq_of_prime_dvd_card_of_isPGroup hr (by norm_num) hQ h)
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact Or.inl (eq_of_prime_dvd_card_of_isPGroup hr Nat.prime_two hS h)
      · exact Or.inr (eq_of_prime_dvd_card_of_isPGroup hr (by norm_num) hB5 h)
  have hloc : 3 < localRank 5 (↥Q ⋊[β] (↥S ⋊[MulDistribMulAction.toMulAut ↥B ↥S] ↥B)) := by
    by_contra h
    push Not at h
    exact absurd (PlaneAux.evenRank_le_of_localRank_le_of_card (by norm_num) hcard h)
      (not_le.mpr h39)
  exact hloc.trans_le (PlaneAux.localRank_le_of_injective (by norm_num) ι hιinj)

end FiveFive

theorem rank3II_3_8 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p) (hq3 : 3 < q)
    {E S Q : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian p E) (hE1 : E ≠ ⊥)
    (hS : IsPGroup 2 S) (hQ : IsPGroup q Q) (hES : E ≤ Subgroup.normalizer (S : Set G))
    (hEf : E ⊓ Subgroup.centralizer (S : Set G) = ⊥)
    (hESQ : E ⊔ S ≤ Subgroup.normalizer (Q : Set G))
    (hESf : (E ⊔ S) ⊓ Subgroup.centralizer (Q : Set G) = ⊥)
    (hp5 : p = 5 → 25 ≤ Nat.card E) :
    2 < localRank q G := by
  by_cases hp5' : p = 5
  · subst hp5'
    by_cases hq5 : q = 5
    · subst hq5
      exact lt_trans (by norm_num)
        (three_lt_localRank_of_five_five hE (hp5 rfl) hS hQ hES hEf hESQ hESf)
    · exact two_lt_localRank_of_five_of_ne hq hq3 hq5 hE (hp5 rfl) hS hQ hES hEf hESQ hESf
  · exact two_lt_localRank_of_ne_five hp hq hp3 hq3 hp5' hE hE1 hS hQ hES hEf hESQ hESf

end CFSG.RankThree.PartTwo.Sec3
