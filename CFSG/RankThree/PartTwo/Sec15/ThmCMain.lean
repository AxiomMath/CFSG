module

public import CFSG.RankThree.PartTwo.Sec15.ThmCConsumers
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
public import CFSG.RankThree.PartTwo.Sec15.Gagen1511Point
public import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.Sec15.ThmCLemma7
public import CFSG.RankThree.PartTwo.Sec15.ThmCLemma9
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmC

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem thmc_mem_center_of_comm {E : Type} [Group E] [Group.IsPerfect E] {x : E}
    (hx : ∀ y : E, ⁅x, y⁆ ∈ Subgroup.center E) : x ∈ Subgroup.center E := by
  have hmul : ∀ u v : E, ⁅x, u * v⁆ = ⁅x, u⁆ * ⁅x, v⁆ := by
    intro u v
    have hcv : u * ⁅x, v⁆ * u⁻¹ = ⁅x, v⁆ := by
      rw [Subgroup.mem_center_iff.mp (hx v) u, mul_inv_cancel_right]
    calc ⁅x, u * v⁆ = ⁅x, u⁆ * (u * ⁅x, v⁆ * u⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = ⁅x, u⁆ * ⁅x, v⁆ := by rw [hcv]
  have hinv : ∀ w : E, ⁅x, w⁻¹⁆ = ⁅x, w⁆⁻¹ := by
    intro w
    have h1 := hmul w w⁻¹
    rw [mul_inv_cancel, commutatorElement_one_right] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have key : ∀ y z : E, Commute x ⁅y, z⁆ := by
    intro y z
    rw [← commutatorElement_eq_one_iff_commute, commutatorElement_def y z,
      hmul (y * z * y⁻¹) z⁻¹, hmul (y * z) y⁻¹, hmul y z, hinv y, hinv z]
    have hc : ⁅x, z⁆ * ⁅x, y⁆ = ⁅x, y⁆ * ⁅x, z⁆ := Subgroup.mem_center_iff.mp (hx y) _
    rw [← hc]
    group
  have hTop : (⊤ : Subgroup E) ≤ Subgroup.centralizer ({x} : Set E) := by
    rw [← Group.IsPerfect.commutator_eq_top (G := E)]
    refine Subgroup.commutator_le.mpr fun y _ z _ => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr (key y z).symm
  exact Subgroup.mem_center_iff.mpr fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (hTop (Subgroup.mem_top g))

private theorem thmc_quot_center_equiv {X : Type} [Group X] [Group.IsPerfect X] {V N : Subgroup X}
    [V.Normal] [N.Normal] (hVN : V ≤ N)
    (hZ : Subgroup.map (QuotientGroup.mk' V) N ≤ Subgroup.center (X ⧸ V)) :
    Nonempty ((X ⧸ V) ⧸ Subgroup.center (X ⧸ V) ≃* (X ⧸ N) ⧸ Subgroup.center (X ⧸ N)) := by
  let Φ : X ⧸ V →* X ⧸ N := QuotientGroup.map V N (MonoidHom.id X) (fun x hx => hVN hx)
  have hΦs : Function.Surjective Φ := by
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨(y : X ⧸ V), rfl⟩
  have hΦk : ∀ x : X ⧸ V, Φ x = 1 → x ∈ Subgroup.center (X ⧸ V) := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hyN : y ∈ N := (QuotientGroup.eq_one_iff y).mp hx
    exact hZ (Subgroup.mem_map_of_mem _ hyN)
  have hΦc : ∀ x : X ⧸ V, x ∈ Subgroup.center (X ⧸ V) → Φ x ∈ Subgroup.center (X ⧸ N) := by
    intro x hx
    refine Subgroup.mem_center_iff.mpr fun w => ?_
    obtain ⟨v, rfl⟩ := hΦs w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx v]
  have hcentral : ∀ x : X ⧸ V, Φ x ∈ Subgroup.center (X ⧸ N) → x ∈ Subgroup.center (X ⧸ V) := by
    intro x hx
    refine thmc_mem_center_of_comm fun y => hΦk _ ?_
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.mp hx (Φ y)).symm
  let ψ : X ⧸ V →* (X ⧸ N) ⧸ Subgroup.center (X ⧸ N) :=
    (QuotientGroup.mk' (Subgroup.center (X ⧸ N))).comp Φ
  have hψs : Function.Surjective ψ := by
    intro w
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨u, rfl⟩ := hΦs v
    exact ⟨u, rfl⟩
  have hψk : ψ.ker = Subgroup.center (X ⧸ V) := by
    ext x
    rw [MonoidHom.mem_ker]
    exact ⟨fun hx => hcentral x ((QuotientGroup.eq_one_iff (Φ x)).mp hx),
      fun hx => (QuotientGroup.eq_one_iff (Φ x)).mpr (hΦc x hx)⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hψk).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩

private theorem thmc_twoMult_of_mulEquiv {S S' : Type} [Group S] [Group S'] (h : TwoMultLeTwo S)
    (e : S' ≃* S) : TwoMultLeTwo S' := by
  intro E _ _ hE hφ Z hZ hp
  obtain ⟨φ⟩ := hφ
  exact h E hE ⟨φ.trans e⟩ Z hZ hp

private theorem thmc_twoMult_of_quot {X : Type} [Group X] [Group.IsPerfect X] {V N : Subgroup X}
    [V.Normal] [N.Normal] (hVN : V ≤ N)
    (hZ : Subgroup.map (QuotientGroup.mk' V) N ≤ Subgroup.center (X ⧸ V))
    {S : Type} [Group S] (hS : TwoMultLeTwo S)
    (e : (X ⧸ N) ⧸ Subgroup.center (X ⧸ N) ≃* S) :
    TwoMultLeTwo ((X ⧸ V) ⧸ Subgroup.center (X ⧸ V)) := by
  obtain ⟨φ⟩ := thmc_quot_center_equiv hVN hZ
  exact thmc_twoMult_of_mulEquiv hS (φ.trans e)

private theorem thmc_center_eq_bot {Q : Type} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (hs : IsSimpleGroup Q) : Subgroup.center Q = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨-, hsq, -⟩ := hq
    have hnt : Nontrivial (Q ⧸ Subgroup.center Q) := hsq.toNontrivial
    have hsub : Subsingleton (Q ⧸ Subgroup.center Q) := by
      rw [h]; exact QuotientGroup.subsingleton_quotient_top
    exact (not_nontrivial_iff_subsingleton.mpr hsub) hnt

private theorem thmc_quot_center_nonempty {Q S : Type} [Group Q] [Group S]
    (hq : CFSG.IsQuasisimple Q) [IsSimpleGroup S] (e : Q ≃* S) :
    Nonempty (Q ⧸ Subgroup.center Q ≃* S) := by
  have hc := thmc_center_eq_bot hq e.isSimpleGroup
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot.trans e)⟩

private theorem thmc_quot_center_self {Q : Type} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (hs : IsSimpleGroup Q) : Nonempty (Q ⧸ Subgroup.center Q ≃* Q) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (thmc_center_eq_bot hq hs)).trans QuotientGroup.quotientBot⟩

private theorem thmc_isSimple_of_isoLThreePi {Q : Type} [Group Q] {m : ℕ} (hm : 3 ≤ m)
    (hiso : Sec4.IsoLThreePi Q 2 m) : IsSimpleGroup Q := by
  have h8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · haveI : IsSimpleGroup (CFSG.PGLModel.projSL 3 (GaloisField 2 m)) :=
      CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField 2 m) (by norm_num)
        (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact φ.isSimpleGroup
  · haveI : IsSimpleGroup (CFSG.PGLModel.projSU 3 2 m) :=
      CFSG.PGLModel.isSimpleGroup_projSU_of_admissible
        (show CFSG.Open.StatedLieAdmissible .PSU 3 2 m from by
          show Nat.Prime 2 ∧ 1 ≤ m ∧ 3 ≤ 3 ∧ (3, 2 ^ m) ≠ (3, 2)
          exact ⟨Nat.prime_two, by omega, le_refl 3, fun h => by
            have := congrArg Prod.snd h
            simp only at this
            omega⟩)
    exact φ.isSimpleGroup

private theorem thmc_comm_zpowers_le {A Y : Subgroup G} {LB : Subgroup G → Subgroup G} {c' : G}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hcA : c' ∈ A)
    (hYA : A ≤ Subgroup.normalizer (Y : Set G))
    (hdec : Y = pPrimeCoreOf 3 Y ⊔
      deltaZero A LB (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G))) :
    ⁅Y, Subgroup.zpowers c'⁆ ≤ pPrimeCoreOf 3 Y := by
  set O := pPrimeCoreOf 3 Y with hO
  have hzN : Subgroup.zpowers c' ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.zpowers_le.mpr (normalizer_le_normalizer_pPrimeCoreOf 3 Y (hYA hcA))
  have hYS : Y ≤ Sec14.commutatorInSubgroup (Subgroup.zpowers c') O := by
    refine hdec.le.trans (sup_le (fun o ho => ?_) (fun d hd => ?_))
    · refine Sec14.mem_commutatorInSubgroup.mpr ⟨Subgroup.le_normalizer ho, fun q hq => ?_⟩
      rw [commutatorElement_def]
      exact O.mul_mem ((Subgroup.mem_normalizer_iff.mp (hzN hq) o).mp ho) (O.inv_mem ho)
    · have hdY : d ∈ Y := (deltaZero_le _).trans inf_le_left hd
      have hdd : Commute d c' :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (Proof1511Point.deltaZero_le_centralizer hA LB hcA inf_le_right hd)
      refine Sec14.mem_commutatorInSubgroup.mpr
        ⟨le_normalizer_pPrimeCoreOf 3 Y hdY, fun q hq => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
      have h1 : ⁅c' ^ k, d⁆ = 1 :=
        commutatorElement_eq_one_iff_commute.mpr (hdd.symm.zpow_left k)
      rw [h1]
      exact O.one_mem
  rw [Subgroup.commutator_le]
  intro y hy z hz
  have h := (Sec14.mem_commutatorInSubgroup.mp (hYS hy)).2 z hz
  rw [← commutatorElement_inv]
  exact O.inv_mem h

private theorem thmc_core
    (hK : KFactM2) (h148 : Sec14.Item148R) (h142 : Sec14.Concl142S14)
    (h146 : Sec14.Item146S14) (h1444 : Sec14.Item1444S14) (hbot : Sec14.Item145BotS14)
    (L7p : ∀ {A Y : Subgroup G}, Y ∈ Sec15.scriptY0 A (lB A) → Group.IsPerfect ↥Y)
    (L7z : ∀ {A Y : Subgroup G}, Y ∈ Sec15.scriptY0 A (lB A) → ∀ {a : G}, a ∈ A →
      ⁅Y, Subgroup.zpowers a⁆ ≤ pPrimeCoreOf 3 Y →
        ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers a⁆ ≤ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆)
    (L7c : ∀ {A Y : Subgroup G}, Y ∈ Sec15.scriptY0 A (lB A) →
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) (CFSG.pPrimeCore 3 ↥Y) =
          CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧
        CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧
        Odd (Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))))
    (L9 : ∀ {A Y : Subgroup G}, Y ∈ Sec15.scriptY0 A (lB A) →
      TwoMultLeTwo ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) →
      ∀ {e : G}, e ∈ Subgroup.normalizer (Y : Set G) → IsPGroup 3 ↥(Subgroup.zpowers e) →
        ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers e⁆ ≤ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆)
    (A : Subgroup G) (c : G) (L : Subgroup G) (hR : Sec15R G A c L)
    (Y : Subgroup G) (hY0 : Y ∈ Sec15.scriptY0 A (lB A)) :
    CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) := by
  have hS : Sec14Std G A c L := hR.toSec14Std
  have hA : IsE27 A := hS.isE27
  have hAab : IsMulCommutative A := hR.isElemAbelian.1
  have hY4 : Y ∈ Sec15.scriptY4 A (lB A) := hY0.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY4.1.2
  have hbot' : ∃ B, IsHyperplane A B ∧ lB A B = ⊥ := hbot G A c L hS
  have hYΔ : Y = deltaZero A (lB A) Y := Sec14.rank3II_15_1_lB hA hbot' hY4
  have hN : ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ ∈ scriptQ A (lB A) :=
    Sec17.Proof17Q0.commutator_pCoreOf_mem_scriptQ hA (h1444 G A c L hS)
      (h146 G A c L hS) hbot' hY4
  have h146' : Sec14.Item146 A (lB A) := h146 G A c L hS
  have h142' : Sec14.Concl142 A (lB A) := h142 G A c L hS
  have hAA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hQq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :=
    Sec15.Proof1515.isQuasisimple_quot_pPrimeCore hY4
  obtain ⟨hmap, hZle, -⟩ := L7c hY0
  have hZ : Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) (CFSG.pPrimeCore 3 ↥Y) ≤
      Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := hmap.le.trans hZle
  have hVN : CFSG.pCore 2 ↥Y ≤ CFSG.pPrimeCore 3 ↥Y := Sec15.pCore_two_le_pPrimeCore_three
  haveI := L7p hY0
  rcases Sec15.Proof1515.cases148_of_mem_scriptY4 (h148 G A c L hR) hAab hY4 hYΔ with
    ⟨c', hc', hdec, -, -, -⟩ | ⟨c', L', hc', -, -, hS3⟩ |
      ⟨⟨φ10⟩, ⟨c', L', hc', -, -⟩, -⟩ |
      ⟨c', L', n, m, hc', -, hn, -, hiso, -⟩
  ·
    have hcA : c' ∈ A := (zpowers_mem_omegaA_iff.mp hc').1
    have hYa := thmc_comm_zpowers_le hAA hcA hAY hdec
    exact lemma8_of_comm hA h146' h142' hAY hc' hN (L7z hY0 hcA hYa)
  ·
    have hcA : c' ∈ A := (zpowers_mem_omegaA_iff.mp hc').1
    have hcard : Nat.card (Subgroup.zpowers c') = 3 := (zpowers_mem_omegaA_iff.mp hc').2.1
    have hP3 : IsPGroup 3 ↥(Subgroup.zpowers c') := IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
    rcases hS3 with hT | hN7 | hE7
    · obtain ⟨-, ⟨eT⟩⟩ := hT
      have hM := thmc_twoMult_of_quot hVN hZ hK.1 eT
      exact lemma8_of_comm hA h146' h142' hAY hc' hN (L9 hY0 hM (hAY hcA) hP3)
    · obtain ⟨φ7⟩ := hN7
      haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      obtain ⟨eA⟩ := thmc_quot_center_nonempty hQq φ7
      have hM := thmc_twoMult_of_quot hVN hZ hK.2.1 eA
      exact lemma8_of_comm hA h146' h142' hAY hc' hN (L9 hY0 hM (hAY hcA) hP3)
    · obtain ⟨hf7K, hNL⟩ := hE7
      obtain ⟨φL⟩ := hNL
      haveI : IsSimpleGroup (CFSG.PGLModel.projSL 3 (GaloisField 7 1)) :=
        CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField 7 1) (by norm_num)
          (Or.inl (by norm_num)) (Or.inl (by norm_num))
      obtain ⟨hf7K', hL7K⟩ := hK.2.2.1
      obtain ⟨eL⟩ := thmc_quot_center_nonempty hQq φL
      have hM := thmc_twoMult_of_quot hVN hZ hL7K eL
      exact lemma8_of_comm hA h146' h142' hAY hc' hN (L9 hY0 hM (hAY hcA) hP3)
  ·
    have hcA : c' ∈ A := (zpowers_mem_omegaA_iff.mp hc').1
    have hcard : Nat.card (Subgroup.zpowers c') = 3 := (zpowers_mem_omegaA_iff.mp hc').2.1
    have hP3 : IsPGroup 3 ↥(Subgroup.zpowers c') :=
      IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin 10)) := alternatingGroup.isSimpleGroup (by simp)
    obtain ⟨eA⟩ := thmc_quot_center_nonempty hQq φ10
    have hM := thmc_twoMult_of_quot hVN hZ hK.2.2.2.1 eA
    exact lemma8_of_comm hA h146' h142' hAY hc' hN (L9 hY0 hM (hAY hcA) hP3)
  ·
    have hcA : c' ∈ A := (zpowers_mem_omegaA_iff.mp hc').1
    have hcard : Nat.card (Subgroup.zpowers c') = 3 := (zpowers_mem_omegaA_iff.mp hc').2.1
    have hP3 : IsPGroup 3 ↥(Subgroup.zpowers c') :=
      IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
    have hm3 : 3 ≤ 3 * n := by omega
    have hsQ := thmc_isSimple_of_isoLThreePi hm3 hiso
    obtain ⟨eQ⟩ := thmc_quot_center_self hQq hsQ
    have hM := thmc_twoMult_of_quot hVN hZ (hK.2.2.2.2 (3 * n) hm3 _ hiso) eQ
    exact lemma8_of_comm hA h146' h142' hAY hc' hN (L9 hY0 hM (hAY hcA) hP3)

theorem pCoreOf_mem_scriptQ_of_scriptY0
    (hK : KFactM2) (h148 : Sec14.Item148R) (h142 : Sec14.Concl142S14)
    (h146 : Sec14.Item146S14) (h1444 : Sec14.Item1444S14) (hbot : Sec14.Item145BotS14) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) := by
  intro G _ _ A c L hR Y hY0
  exact thmc_core (G := G) hK h148 h142 h146 h1444 hbot
    (fun {A Y} hY => lemma7_perfect hY)
    (fun {A Y} hY {a} ha hYa => (lemma7_centralizes hY ha hYa).2.2)
    (fun {A Y} hY => by
      obtain ⟨h1, h2, h3⟩ := lemma7_center hY
      exact ⟨h2, h3, h1⟩)
    (fun {A Y} hY hM {e} he he3 => lemma9_of hY (lemma7_perfect hY) (lemma7_center hY).1 hM he he3)
    A c L hR Y hY0

theorem step171CommQ_of_route
    (hK : KFactM2) (h148 : Sec14.Item148R) (h142 : Sec14.Concl142S14)
    (h146 : Sec14.Item146S14) (h1444 : Sec14.Item1444S14) (hbot : Sec14.Item145BotS14) :
    Sec17.Step171CommQ :=
  step171CommQ_of_thmC (pCoreOf_mem_scriptQ_of_scriptY0 hK h148 h142 h146 h1444 hbot)

end CFSG.RankThree.PartTwo.Sec15.ThmC
