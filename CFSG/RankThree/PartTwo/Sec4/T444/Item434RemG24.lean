module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemG24Mat
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherKit
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2LeviA2
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2TorusConj
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Centralizers
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalG2Four
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeU3
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Fischer
open CFSG.ComponentClassification.RankTwoExceptional CFSG.LocalAnalysis.ComponentInitial

namespace Item434RemG24

abbrev SL3F : Type := SpecialLinearGroup (Fin 3) F4

theorem mem_normalizer_of_conj {X : Type*} [Group X] [Finite X] (S : Subgroup X) {x : X}
    (h : ∀ s ∈ S, x * s * x⁻¹ ∈ S) : x ∈ Subgroup.normalizer (S : Set X) := by
  let f : ↥S → ↥S := fun s => ⟨x * (s : X) * x⁻¹, h s s.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h : x * (a : X) * x⁻¹ = x * (b : X) * x⁻¹ := congrArg Subtype.val hab
    simpa using h
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  obtain ⟨s, hs⟩ := hsurj ⟨x * y * x⁻¹, hy⟩
  have hs' : x * (s : X) * x⁻¹ = x * y * x⁻¹ := congrArg Subtype.val hs
  have : (s : X) = y := by simpa using hs'
  rw [← this]
  exact s.2

theorem card_subtype_list {L : List Mat3} (hnd : L.Nodup) :
    Nat.card {m : Mat3 // m ∈ L} = L.length := by
  rw [← Nat.card_congr (List.Nodup.getEquiv L hnd), Nat.card_fin]

theorem card_of_list {H : Subgroup SL3F} {L : List Mat3}
    (hH : ∀ x : SL3F, x ∈ H ↔ (x : Mat3) ∈ L) (hdet : ∀ m ∈ L, m.det = 1) (hnd : L.Nodup) :
    Nat.card H = L.length := by
  have e : H ≃ {m : Mat3 // m ∈ L} :=
    { toFun := fun x => ⟨((x : SL3F) : Mat3), (hH x).1 x.2⟩
      invFun := fun m => ⟨⟨m.1, hdet m.1 m.2⟩, (hH _).2 m.2⟩
      left_inv := fun x => rfl
      right_inv := fun m => rfl }
  rw [Nat.card_congr e, card_subtype_list hnd]

theorem card_le_of_forall_mem {H : Subgroup SL3F} {L : List Mat3}
    (hH : ∀ x ∈ H, (x : Mat3) ∈ L) (hnd : L.Nodup) : Nat.card H ≤ L.length := by
  rw [← card_subtype_list hnd]
  refine Nat.card_le_card_of_injective (fun x => ⟨((x : SL3F) : Mat3), hH x x.2⟩) ?_
  intro x y hxy
  have h := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext h)

theorem det_of_mem_sZero {m : Mat3} (hm : m ∈ sZeroList) : m.det = 1 := by
  have h := List.all_eq_true.mp sZero_checks.2.2 m hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem cube_of_mem_sZero {m : Mat3} (hm : m ∈ sZeroList) : m * m * m = 1 := by
  have h := List.all_eq_true.mp sZero_checks.2.2 m hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem mem_sZero_of_mem_eList {i : Fin 4} {m : Mat3} (hm : m ∈ eList i) : m ∈ sZeroList := by
  have h := List.all_eq_true.mp (eList_checks i).1 m hm
  simpa using h

theorem mul_mem_sZero {a b : Mat3} (ha : a ∈ sZeroList) (hb : b ∈ sZeroList) :
    a * b ∈ sZeroList := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp sZero_checks.1 _ ha) _ hb
  simpa using h

theorem mul_mem_eList {i : Fin 4} {a b : Mat3} (ha : a ∈ eList i) (hb : b ∈ eList i) :
    a * b ∈ eList i := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp (eList_checks i).2.2.1 _ ha) _ hb
  simpa using h

theorem inv_eq_sq {x : SL3F} (h3 : (x : Mat3) * (x : Mat3) * (x : Mat3) = 1) :
    x⁻¹ = x * x := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  change (x : Mat3) * ((x : Mat3) * (x : Mat3)) = 1
  rw [← Matrix.mul_assoc]
  exact h3

@[expose] def sZeroGrp : Subgroup SL3F where
  carrier := {x | (x : Mat3) ∈ sZeroList}
  mul_mem' {_ _} hx hy := mul_mem_sZero hx hy
  one_mem' := sZero_checks.2.1
  inv_mem' {x} hx := by
    change ((x⁻¹ : SL3F) : Mat3) ∈ sZeroList
    rw [inv_eq_sq (cube_of_mem_sZero hx)]
    exact mul_mem_sZero hx hx

@[expose] def eGrp (i : Fin 4) : Subgroup SL3F where
  carrier := {x | (x : Mat3) ∈ eList i}
  mul_mem' {_ _} hx hy := mul_mem_eList hx hy
  one_mem' := by
    have h := List.all_eq_true.mp (eList_checks i).2.1 1 (by decide)
    simpa using h
  inv_mem' {x} hx := by
    change ((x⁻¹ : SL3F) : Mat3) ∈ eList i
    rw [inv_eq_sq (cube_of_mem_sZero (mem_sZero_of_mem_eList hx))]
    exact mul_mem_eList hx hx

theorem card_sZeroGrp : Nat.card sZeroGrp = 27 := by
  rw [card_of_list (fun _ => Iff.rfl) (fun _ hm => det_of_mem_sZero hm) sZero_card.2.1,
    sZero_card.1]

theorem card_eGrp (i : Fin 4) : Nat.card (eGrp i) = 9 := by
  rw [card_of_list (fun _ => Iff.rfl)
    (fun _ hm => det_of_mem_sZero (mem_sZero_of_mem_eList hm)) (eList_checks i).2.2.2.2.2,
    (eList_checks i).2.2.2.2.1]

theorem exists_not_comm : ∃ x ∈ sZeroGrp, ∃ y ∈ sZeroGrp, x * y ≠ y * x := by
  obtain ⟨h1, h2, h3⟩ := sZero_noncomm
  refine ⟨⟨_, det_of_mem_sZero h1⟩, h1, ⟨_, det_of_mem_sZero h2⟩, h2, fun h => h3 ?_⟩
  exact congrArg (fun x : SL3F => (x : Mat3)) h

theorem exists_eq_eGrp {P : Subgroup SL3F} (hPS : P ≤ sZeroGrp)
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (h9 : Nat.card P = 9) : ∃ i, P = eGrp i := by
  obtain ⟨x, hxP, hxZ⟩ : ∃ x ∈ P, ((x : SL3F) : Mat3) ∉ zList := by
    by_contra hall
    push Not at hall
    have := card_le_of_forall_mem hall sZero_card.2.2.2.1
    rw [h9, sZero_card.2.2.1] at this
    omega
  have hc := List.all_eq_true.mp centralizer_check ((x : SL3F) : Mat3) (hPS hxP)
  simp only [hxZ, decide_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc
  refine ⟨eIdx ((x : SL3F) : Mat3), Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) ?_⟩
  · rcases hc.2 _ (hPS hy) with h | h
    · exact absurd (congrArg (fun z : SL3F => (z : Mat3)) (hPc x hxP y hy)) h
    · exact h
  · rw [h9, card_eGrp]

set_option maxRecDepth 10000 in
theorem det_one_add_smul : ∀ i : Fin 4, ∀ t : F4, (1 + t • nMat i).det = 1 := by
  decide +kernel

theorem one_add_smul_mul (i : Fin 4) (s t : F4) :
    (1 + s • nMat i) * (1 + t • nMat i) = 1 + (s + t) • nMat i := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, (normalizes_check i).1,
    smul_zero, add_zero, add_smul, add_assoc]
  abel

@[expose] def rHom (i : Fin 4) : Multiplicative F4 →* SL3F where
  toFun t := (⟨1 + t.toAdd • nMat i, det_one_add_smul i _⟩ : SL3F)
  map_one' := Subtype.ext (by
    change 1 + (0 : F4) • nMat i = 1
    rw [zero_smul, add_zero])
  map_mul' s t := Subtype.ext (by
    change 1 + (s.toAdd + t.toAdd) • nMat i = (1 + s.toAdd • nMat i) * (1 + t.toAdd • nMat i)
    rw [one_add_smul_mul])

@[expose] def rGrp (i : Fin 4) : Subgroup SL3F := (rHom i).range

theorem isPGroup_rGrp (i : Fin 4) : IsPGroup 2 (rGrp i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : IsPGroup 2 (⊤ : Subgroup (Multiplicative F4)) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, F4.card]
    norm_num
  rw [rGrp, MonoidHom.range_eq_map]
  exact h4.map _

theorem rGrp_ne_bot (i : Fin 4) : rGrp i ≠ ⊥ := by
  intro h
  have hmem : rHom i (Multiplicative.ofAdd 1) ∈ rGrp i := ⟨_, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  have h' := congrArg (fun x : SL3F => (x : Mat3)) hmem
  change 1 + (1 : F4) • nMat i = 1 at h'
  rw [one_smul, add_eq_left] at h'
  exact (normalizes_check i).2.1 h'

theorem eGrp_le_normalizer (i : Fin 4) :
    eGrp i ≤ Subgroup.normalizer (rGrp i : Set SL3F) := by
  intro e he
  refine mem_normalizer_of_conj _ ?_
  rintro _ ⟨t, rfl⟩
  have hc := List.all_eq_true.mp (normalizes_check i).2.2 _ he
  simp only [List.any_eq_true, decide_eq_true_eq] at hc
  obtain ⟨c, -, hcN⟩ := hc
  refine ⟨Multiplicative.ofAdd (c * t.toAdd), Subtype.ext ?_⟩
  rw [inv_eq_sq (cube_of_mem_sZero (mem_sZero_of_mem_eList he))]
  change 1 + (c * t.toAdd) • nMat i =
    (e : Mat3) * (1 + t.toAdd • nMat i) * ((e : Mat3) * (e : Mat3))
  have he3 := cube_of_mem_sZero (mem_sZero_of_mem_eList he)
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.mul_assoc, he3, hcN, smul_smul, mul_comm]

theorem map_injective {K : Type} [Field K] {σ : F4 →+* K} (hσ : Function.Injective σ) :
    Function.Injective (SpecialLinearGroup.map σ : SL3F →* SpecialLinearGroup (Fin 3) K) := by
  intro x y hxy
  ext i j
  have h := congrArg (fun z : SpecialLinearGroup (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K) i j)
    hxy
  exact hσ h

section G2


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem injective_of_range (hK : Nat.card K = 4)
    {φ : SpecialLinearGroup (Fin (2 + 1)) K →* ModGL .G2 K} (hrange : φ.range = g2LongA2 K) :
    Function.Injective φ := by
  have hT : Nat.card (g2TorusR K) = 3 := by rw [card_g2TorusR, hK]
  have hTle : g2TorusR K ≤ g2LongA2 K := by
    rw [← center_g2LongA2 hK]
    exact Subgroup.map_subtype_le _
  have hmem : ∀ g, φ g ∈ g2LongA2 K := fun g => hrange ▸ ⟨g, rfl⟩
  set ψ := φ.codRestrict (g2LongA2 K) hmem with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have hq := CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl
  have hψ1 : ∃ k, ψ k ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : g2LongA2 K = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨g, hg⟩ := hψs ⟨y, hy⟩
      have h1 := congrArg Subtype.val (hall g)
      rw [hg] at h1
      exact Subgroup.mem_bot.mpr h1
    have hle : Nat.card (g2TorusR K) ≤ Nat.card (⊥ : Subgroup (ModGL .G2 K)) :=
      Subgroup.card_le_of_le (hTle.trans hbot.le)
    rw [Subgroup.card_bot] at hle
    omega
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hψ1
  have hψinj : ψ.ker = ⊥ := by
    by_contra hne
    obtain ⟨⟨x, hxk⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
    have hxZ : (x : SpecialLinearGroup (Fin (2 + 1)) K) ∈ LinearFlag.scalars (2 + 1) K := by
      rw [LinearFlag.scalars_eq_center]
      exact hker hxk
    obtain ⟨c₀, -, hc₀⟩ := LinearFlag.mem_scalars.mp hxZ
    have hc₀1 : c₀ ≠ 1 := by
      intro h1
      apply hx1
      apply Subtype.ext
      rw [hc₀, h1, Units.val_one, map_one]
      rfl
    have hU : Nat.card Kˣ = 3 := by
      have h := Nat.card_units (α := K)
      rw [hK] at h
      exact h
    have hc₀3 : orderOf c₀ = 3 := by
      have h3 : c₀ ^ 3 = 1 := by rw [← hU]; exact pow_card_eq_one'
      exact orderOf_eq_prime h3 hc₀1
    have hz : Subgroup.zpowers c₀ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hc₀3, hU])
    have hcen : Subgroup.center (SpecialLinearGroup (Fin (2 + 1)) K) ≤ ψ.ker := by
      intro y hy
      rw [← LinearFlag.scalars_eq_center] at hy
      obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.mp hy
      have hcz : c ∈ Subgroup.zpowers c₀ := hz ▸ Subgroup.mem_top c
      obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers).mpr hcz
      simp only at hn
      have hyx : y = (x : SpecialLinearGroup (Fin (2 + 1)) K) ^ n := by
        have h1 : ((x ^ n : SpecialLinearGroup (Fin (2 + 1)) K) :
            Matrix (Fin (2 + 1)) (Fin (2 + 1)) K) =
            (x : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K) ^ n := Matrix.SpecialLinearGroup.coe_pow x n
        rw [hc₀, ← map_pow, ← Units.val_pow_eq_pow_val, hn, ← hc] at h1
        exact Subtype.ext h1.symm
      rw [hyx]
      exact ψ.ker.pow_mem hxk n
    have hkereq : ψ.ker = Subgroup.center _ := le_antisymm hker hcen
    have θ : SpecialLinearGroup (Fin (2 + 1)) K ⧸ Subgroup.center _ ≃* ↥(g2LongA2 K) :=
      (QuotientGroup.quotientMulEquivOfEq hkereq.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
    have hZ := Item434CharThree.center_eq_bot_of_quasisimple_quotient hq θ
    have hT1 : g2TorusR K = ⊥ := by rw [← center_g2LongA2 hK, hZ, Subgroup.map_bot]
    rw [hT1, Subgroup.card_bot] at hT
    omega
  have hinj := (MonoidHom.ker_eq_bot_iff ψ).1 hψinj
  intro x y hxy
  exact hinj (Subtype.ext hxy)

abbrev G2K (K : Type) [Field K] : Type := ↥(adjointGroup .G2 K)

@[expose] noncomputable def phiX (σ : F4 ≃+* K)
    {φ : SpecialLinearGroup (Fin (2 + 1)) K →* ModGL .G2 K} (hrange : φ.range = g2LongA2 K) :
    SL3F →* G2K K :=
  (φ.comp (SpecialLinearGroup.map σ.toRingHom)).codRestrict (adjointGroup .G2 K) fun _ =>
    g2LongA2_le_adjointGroup (hrange ▸ ⟨_, rfl⟩)

theorem phiX_injective (hK : Nat.card K = 4) (σ : F4 ≃+* K)
    {φ : SpecialLinearGroup (Fin (2 + 1)) K →* ModGL .G2 K} (hrange : φ.range = g2LongA2 K) :
    Function.Injective (phiX σ hrange) := by
  intro x y hxy
  have h := congrArg Subtype.val hxy
  exact map_injective σ.injective (injective_of_range hK hrange h)

omit [CharP K 2] in
theorem factorization_card_g2K (hK : Nat.card K = 4) :
    (Nat.card (G2K K)).factorization 3 = 3 := by
  have h : CFSG.Open.ordG2 4 = 3 ^ 3 * 9318400 := by norm_num [CFSG.Open.ordG2]
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK, h]
  exact Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)

theorem card_map_sZeroGrp (hK : Nat.card K = 4) (σ : F4 ≃+* K)
    {φ : SpecialLinearGroup (Fin (2 + 1)) K →* ModGL .G2 K} (hrange : φ.range = g2LongA2 K) :
    Nat.card (sZeroGrp.map (phiX σ hrange)) = 3 ^ (Nat.card (G2K K)).factorization 3 := by
  rw [Subgroup.card_map_of_injective (phiX_injective hK σ hrange), card_sZeroGrp,
    factorization_card_g2K hK]
  norm_num

theorem false_of_e27 (hK : Nat.card K = 4) (σ : F4 ≃+* K)
    {φ : SpecialLinearGroup (Fin (2 + 1)) K →* ModGL .G2 K} (hrange : φ.range = g2LongA2 K)
    {P : Subgroup (G2K K)} (hPe : CFSG.Assembly.IsElemAbelian 3 P) (h27 : Nat.card P = 27) :
    False := by
  set Φ := phiX σ hrange
  have hS := card_map_sZeroGrp hK σ hrange
  obtain ⟨g, hg⟩ := Item434SmallTwoOther.exists_map_conj_of_sylow hS
    (by rw [h27, hS, factorization_card_g2K hK]; norm_num)
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_not_comm
  apply hxy
  apply phiX_injective hK σ hrange
  rw [map_mul, map_mul]
  apply (MulAut.conj g).injective
  rw [map_mul, map_mul]
  have hxP : MulAut.conj g (Φ x) ∈ P := by
    rw [hg]
    exact ⟨Φ x, ⟨x, hx, rfl⟩, rfl⟩
  have hyP : MulAut.conj g (Φ y) ∈ P := by
    rw [hg]
    exact ⟨Φ y, ⟨y, hy, rfl⟩, rfl⟩
  have hc := congrArg Subtype.val (hPe.1.is_comm.comm ⟨_, hxP⟩ ⟨_, hyP⟩)
  simp only [Subgroup.coe_mul] at hc
  exact hc

theorem exists_two_group_of_e9 (hK : Nat.card K = 4) (σ : F4 ≃+* K)
    {φ : SpecialLinearGroup (Fin (2 + 1)) K →* ModGL .G2 K} (hrange : φ.range = g2LongA2 K)
    {P : Subgroup (G2K K)} (hPe : CFSG.Assembly.IsElemAbelian 3 P) (h9 : Nat.card P = 9) :
    ∃ R : Subgroup (G2K K), IsPGroup 2 R ∧ R ≠ ⊥ ∧
      P ≤ Subgroup.normalizer (R : Set (G2K K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Φ := phiX σ hrange with hΦ
  have hinj := phiX_injective hK σ hrange
  have hS := card_map_sZeroGrp hK σ hrange
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hS hPp
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'le : P' ≤ sZeroGrp.map Φ := Item434AltPerm.map_conj_inv_le hg
  have hP'g : P'.map (MulAut.conj g).toMonoidHom = P := by
    rw [hP', Item434AltPerm.map_conj_map_conj_inv]
  set P₀ := P'.comap Φ ⊓ sZeroGrp with hP₀
  have hP₀map : P₀.map Φ = P' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro y hy
      obtain ⟨x, hxS, rfl⟩ := hP'le hy
      exact ⟨x, ⟨hy, hxS⟩, rfl⟩
  have hP₀card : Nat.card P₀ = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hP₀map, hP',
      Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective, h9]
  have hP'e : CFSG.Assembly.IsElemAbelian 3 P' :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hPe
  have hP₀c : ∀ x ∈ P₀, ∀ y ∈ P₀, x * y = y * x := by
    intro x hx y hy
    apply hinj
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hP'e.1.is_comm.comm ⟨Φ x, hx.1⟩ ⟨Φ y, hy.1⟩)
  obtain ⟨i, hi⟩ := exists_eq_eGrp (P := P₀) inf_le_right hP₀c hP₀card
  refine ⟨((rGrp i).map Φ).map (MulAut.conj g).toMonoidHom, ((isPGroup_rGrp i).map Φ).map _,
    ?_, ?_⟩
  · intro h
    apply rGrp_ne_bot i
    rw [Subgroup.map_eq_bot_iff_of_injective (f := (MulAut.conj g).toMonoidHom) _
        (MulAut.conj g).injective, Subgroup.map_eq_bot_iff_of_injective _ hinj] at h
    exact h
  · rw [← hP'g, ← hP₀map, hi]
    exact (Subgroup.map_mono (Subgroup.map_mono (eGrp_le_normalizer i))).trans
      ((Subgroup.map_mono (Subgroup.le_normalizer_map Φ)).trans (Subgroup.le_normalizer_map _))

theorem closure_hyperCent_eq_top (hK : Nat.card K = 4) (σ : F4 ≃+* K)
    {φ : SpecialLinearGroup (Fin (2 + 1)) K →* ModGL .G2 K} (hrange : φ.range = g2LongA2 K)
    [IsSimpleGroup ↥(adjointGroup .G2 K)] {P : Subgroup (G2K K)}
    (hPe : CFSG.Assembly.IsElemAbelian 3 P) (h9 : Nat.card P = 9) :
    Subgroup.closure (Item434SmallTwoOther.hyperCent P) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR2, hR1, hPR⟩ := exists_two_group_of_e9 hK σ hrange hPe h9
  set ι := (adjointGroup .G2 K).subtype with hι
  set A := P.map ι with hA
  have : CFSG.IsElementaryAbelian 3 A := by
    have hAe : CFSG.Assembly.IsElemAbelian 3 A :=
      CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hPe
    refine { toIsMulCommutative := hAe.1, exponent_dvd_p := ?_ }
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hAe.2 _ a.2)
  have hA9 : 3 ^ 2 ≤ Nat.card A := by
    rw [hA, Subgroup.card_map_of_injective (adjointGroup .G2 K).subtype_injective, h9]
    norm_num
  have hgen := CFSG.LieType.Chevalley.ordinary_root_invariant_prime_subgroup_centralizer_generation
    .G2 K 2 3 (by norm_num) A (Subgroup.map_subtype_le _) hA9 (R.map ι)
    (Subgroup.map_subtype_le _) (hR2.map _) (fun h => hR1 (by
      rwa [Subgroup.map_eq_bot_iff_of_injective _ (adjointGroup .G2 K).subtype_injective] at h))
    ((Subgroup.map_mono hPR).trans (Subgroup.le_normalizer_map ι))
  have hle : (⨆ a ∈ A, ⨆ (_ : a ≠ 1), adjointGroup .G2 K ⊓
      Subgroup.centralizer ({a} : Set (ModGL .G2 K))) ≤
      (Subgroup.closure (Item434SmallTwoOther.hyperCent P)).map ι := by
    refine iSup₂_le fun a ha => iSup_le fun ha1 => ?_
    rintro x ⟨hxG, hxC⟩
    obtain ⟨p, hp, rfl⟩ := ha
    have hp1 : p ≠ 1 := fun h => ha1 (by rw [h, map_one])
    have hpx : p * ⟨x, hxG⟩ = ⟨x, hxG⟩ * p :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm
    exact ⟨⟨x, hxG⟩, Subgroup.subset_closure
      (Item434SmallTwoOther.mem_hyperCent_of_commute h9 hp (hPe.2 p hp) hp1 hpx), rfl⟩
  rw [eq_top_iff]
  intro y _
  have hy : (y : ModGL .G2 K) ∈ (⨆ a ∈ A, ⨆ (_ : a ≠ 1), adjointGroup .G2 K ⊓
      Subgroup.centralizer ({a} : Set (ModGL .G2 K))) := by
    rw [hgen]
    exact y.2
  obtain ⟨z, hz, hzy⟩ := hle hy
  rwa [Subtype.ext hzy] at hz

end G2

section Main


variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_g24 (h : Ctx434Core G A M Q)
    (hL : IsSmallTwoOtherG24 (layer G ⧸ Subgroup.center (layer G))) : False := by
  obtain ⟨q, hq2, hq3, hv, ⟨e⟩⟩ := hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField 2 2
  have hK : Nat.card K = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hKq : Nat.card K = q.card := by
    rw [hK, TauCeti.PrimePower.card_def, hq2, hq3]
    norm_num
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq2 K hKq
  have hcen : Subgroup.center (G2K K) = ⊥ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let eA : AdjointQuotient .G2 K ≃* G2K K :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  set θ : layer G ⧸ Subgroup.center (layer G) ≃* G2K K := (e.trans b.symm).trans eA
  have hZ : Subgroup.center (layer G) = ⊥ := by
    have hperf : Group.IsPerfect (layer G) := h.isQuasisimple.1
    refine CFSG.ComponentClassification.RankTwoExceptional.g2FourOddCenter (layer G)
      hperf.commutator_eq_top ⟨⟨Nat.prime_two, by norm_num, rfl, by norm_num⟩,
        ⟨K, inferInstance, inferInstance, hK.trans (by norm_num), ⟨e.trans b.symm⟩⟩⟩ ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := h.isQuasisimple.2.1
  have : IsSimpleGroup ↥(adjointGroup .G2 K) := θ.symm.isSimpleGroup
  have hinner : ∀ φ : MulAut (G2K K), φ ^ 3 = 1 →
      φ ∈ (MulAut.conj : G2K K →* MulAut (G2K K)).range := by
    intro φ hφ
    have hsq := CFSG.EvenSmallLie.GTwoFour.mul_self_mem_inner hK φ
    have h4 : φ = (φ * φ) * (φ * φ) := by
      calc φ = φ ^ 3 * φ := by rw [hφ, one_mul]
        _ = (φ * φ) * (φ * φ) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [h4]
    exact Subgroup.mul_mem _ hsq hsq
  obtain ⟨φ, hφ⟩ := exists_sl3_hom (K := K)
  have hrange := range_sl3_hom hφ
  set σ : F4 ≃+* K := F4.equivGaloisField
  refine Item434SmallTwoOther.false_of_gen_of_inner h hZ θ hinner hcen fun P hPe hPc => ?_
  rcases h.card_layerStar with h9 | ⟨h27, -⟩
  · rw [h9] at hPc
    exact closure_hyperCent_eq_top hK σ hrange hPe hPc
  · rw [h27] at hPc
    exact (false_of_e27 hK σ hrange hPe hPc).elim

end Main

end Item434RemG24

section Families


theorem item434SmallTwoOtherAtG24 :
    Item434SmallTwoOtherAtG24 := by
  intro _ _ _ _ _ G _ _ _ _ _ A M Q hc hL
  exact (Item434RemG24.false_of_g24 hc hL).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
