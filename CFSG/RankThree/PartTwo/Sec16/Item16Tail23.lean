module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] noncomputable def Step1623NoTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → IsSimpleGroup ↥L → ∀ n : ℕ, IsZ3LThreeTwo A c L n → 2 ^ n % 3 = 2 →
      Nonempty (↥L ≃* projSU 3 2 n) →
      ∀ T ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2),
        T = ⊥

@[expose] noncomputable def Step1623End : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → IsSimpleGroup ↥L → ∀ n : ℕ, IsZ3LThreeTwo A c L n →
      Nonempty (↥L ≃* projSU 3 2 n) → omegaA A = {Subgroup.zpowers c} →
    (∀ a ∈ A, a ≠ 1 → CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) = ⊥) →
    (∀ T ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2),
      T = ⊥) →
    ∀ R : Subgroup G, Minimal (fun Q => Q ∈ scriptQPi A (lB A) ⊤ (piOf 2) ∧ Q ≠ ⊥) R →
      IsKleinFour R → R = ⁅R, Subgroup.zpowers c⁆ →
      Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = 9 →
      (∀ b ∈ A ⊓ Subgroup.centralizer (R : Set G), b ≠ 1 →
        R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) →
        False

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec16.Proof1623

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThreeEvenClassification.Helpers (coprime_commutator_centralizer_factorization)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem theta_eq_bot_of_isSimpleGroup {L : Subgroup G} [IsSimpleGroup ↥L]
    (hq : IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    aschbacherSolvableCore 3 ↥L = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 ↥L) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨-, -, x, y, hxy⟩ := hq
    have hsub : Subsingleton (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [h1]
      exact QuotientGroup.subsingleton_quotient_top
    apply hxy
    have : Subsingleton ((↥L ⧸ aschbacherSolvableCore 3 ↥L) ⧸
        Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
      QuotientGroup.mk_surjective.subsingleton
    exact Subsingleton.elim _ _

omit [Finite G] in
theorem isKleinFour_closure_pair {r s : G} (hr : r * r = 1) (hs : s * s = 1)
    (hr1 : r ≠ 1) (hs1 : s ≠ 1) (hrs : r ≠ s) (hc : Commute r s) :
    IsKleinFour (Subgroup.closure ({r, s} : Set G)) := by
  have hK : Subgroup.closure ({r, s} : Set G) =
      CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions r s hr hs hc := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      change g ∈ ({r * s, r, s, 1} : Set G)
      rcases hg with rfl | rfl <;> simp
    · intro g hg
      have hg' : g ∈ ({r * s, r, s, 1} : Set G) := hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
      rcases hg' with rfl | rfl | rfl | rfl
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.one_mem _
  rw [hK]
  exact CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions r s hr hs hr1 hs1
    hrs hc

theorem step1623E4_of :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Ctx169 G A c L →
      (∀ T ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2),
        T = ⊥) →
      ∀ R : Subgroup G, Minimal (fun Q => Q ∈ scriptQPi A (lB A) ⊤ (piOf 2) ∧ Q ≠ ⊥) R →
        IsKleinFour R ∧ Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = 9 := by
  intro G _ _ A c L h hno R hRmin
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hRQ2, hR1⟩, hmin⟩ := hRmin
  have hRQ : R ∈ scriptQ A (lB A) := hRQ2.1.1
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hRQ2.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hRQ.1.2.2
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [h.card_eq]; norm_num)
  have hdich : ∀ W ≤ R, A ≤ Subgroup.normalizer (W : Set G) → W ≠ ⊥ → W = R := by
    intro W hWR hAW hW1
    have hWQ : W ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
      ⟨⟨mem_scriptQ_of_le hRQ hWR hAW, le_top⟩,
        (isPiSubgroup_piOf_iff Nat.prime_two W).mpr (hR2.to_le hWR)⟩
    exact le_antisymm hWR (hmin ⟨hWQ, hW1⟩ hWR)
  have hRC : R ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ := by
    refine hno _ ⟨fun x hx => ?_, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (hR2.to_le inf_le_left), le_normalizer_inf hAR
        (h.A_le_centralizer.trans Subgroup.le_normalizer)⟩
    exact Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer hx.2
  have hcR : c ∈ Subgroup.normalizer (R : Set G) := hAR h.mem_A
  have hZ : (Subgroup.center ↥R).map R.subtype = R := by
    refine hdich _ (Subgroup.map_subtype_le _)
      (hAR.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)) ?_
    have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
    have hc := hR2.center_nontrivial
    intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective] at hbot
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hc hbot
  have hRab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    have hxZ : x ∈ (Subgroup.center ↥R).map R.subtype := by rw [hZ]; exact hx
    obtain ⟨x', hx'Z, rfl⟩ := hxZ
    have := Subgroup.mem_center_iff.mp hx'Z ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
  have hk0 : k ≠ 0 := by
    intro h0
    apply hR1
    rw [← Subgroup.card_eq_one, hk, h0, pow_zero]
  obtain ⟨⟨r, hrR⟩, hr2⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hr2' : r ^ 2 = 1 := by
    have := pow_orderOf_eq_one (⟨r, hrR⟩ : ↥R)
    rw [hr2] at this
    simpa using congrArg Subtype.val this
  have hr1 : r ≠ 1 := by
    intro h1
    have : orderOf (⟨r, hrR⟩ : ↥R) = 1 := by
      rw [orderOf_eq_one_iff]
      exact Subtype.ext h1
    omega
  set s := c * r * c⁻¹ with hs
  have hsR : s ∈ R := (Subgroup.mem_normalizer_iff.mp hcR r).mp hrR
  set t := c * s * c⁻¹ with ht
  have htR : t ∈ R := (Subgroup.mem_normalizer_iff.mp hcR s).mp hsR
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hc3' : c * c * c = 1 := by rw [← pow_three', hc3]
  have hctr : c * t * c⁻¹ = r := by
    rw [ht, hs]
    calc c * (c * (c * r * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * r * (c * c * c)⁻¹ := by group
      _ = r := by rw [hc3']; group
  have hrst : r * s * t = 1 := by
    have hmem : r * s * t ∈ R ⊓ Subgroup.centralizer ({c} : Set G) := by
      refine ⟨mul_mem (mul_mem hrR hsR) htR, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : c * (r * s * t) * c⁻¹ = s * t * r := by
        calc c * (r * s * t) * c⁻¹ = (c * r * c⁻¹) * (c * s * c⁻¹) * (c * t * c⁻¹) := by group
          _ = s * t * r := by rw [← hs, ← ht, hctr]
      have h2 : s * t * r = r * s * t := by
        rw [mul_assoc r, ← hRab (s * t) (mul_mem hsR htR) r hrR]
      calc r * s * t * c = c * (c⁻¹ * (r * s * t) * c) := by group
        _ = c * (r * s * t) := by
          congr 1
          have h3 : c⁻¹ * (c * (r * s * t) * c⁻¹) * c = r * s * t := by group
          rw [h1, h2] at h3
          exact h3
    rw [hRC] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hrr : r * r = 1 := by rw [← pow_two, hr2']
  have hs2 : s * s = 1 := by
    rw [hs]
    calc c * r * c⁻¹ * (c * r * c⁻¹) = c * (r * r) * c⁻¹ := by group
      _ = 1 := by rw [hrr]; group
  have htrs : t = r * s := by
    calc t = (r * s)⁻¹ * (r * s * t) := by group
      _ = s⁻¹ * r⁻¹ := by rw [hrst, mul_one, mul_inv_rev]
      _ = s * r := by rw [inv_eq_of_mul_eq_one_right hs2, inv_eq_of_mul_eq_one_right hrr]
      _ = r * s := (hRab r hrR s hsR).symm
  have hs1 : s ≠ 1 := by
    intro h1
    apply hr1
    calc r = c⁻¹ * s * c := by rw [hs]; group
      _ = 1 := by rw [h1]; group
  have hrs : r ≠ s := by
    intro h1
    have hmem : r ∈ R ⊓ Subgroup.centralizer ({c} : Set G) := by
      refine ⟨hrR, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc r * c = c * (c⁻¹ * r * c) := by group
        _ = c * r := by
          congr 1
          calc c⁻¹ * r * c = c⁻¹ * s * c := by rw [← h1]
            _ = r := by rw [hs]; group
    rw [hRC] at hmem
    exact hr1 (Subgroup.mem_bot.mp hmem)
  set W := Subgroup.closure ({r, s} : Set G) with hW
  have hWR : W ≤ R := by
    rw [hW, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hrR
    · exact hsR
  have hW4 : IsKleinFour W :=
    isKleinFour_closure_pair hrr hs2 hr1 hs1 hrs (hRab r hrR s hsR)
  have hcW : c ∈ Subgroup.normalizer (W : Set G) := by
    have hle : W.map (MulAut.conj c).toMonoidHom ≤ W := by
      rw [hW, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      rcases hg with rfl | rfl
      · exact Subgroup.subset_closure (by simp [hs])
      · change c * s * c⁻¹ ∈ _
        rw [← ht, htrs]
        exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    exact Subgroup.mem_normalizer_fintype fun w hw => hle ⟨w, hw, rfl⟩
  set B := A ⊓ Subgroup.centralizer (R : Set G) with hB
  have hBA : B ≤ A := inf_le_left
  have hcB : c ∉ B := by
    intro hcB
    apply hR1
    refine le_bot_iff.mp ?_
    rw [← hRC]
    exact le_inf le_rfl fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hcB.2 x hx)
  have hEB : ∀ E ≤ A, 9 ≤ Nat.card E → E ⊓ B ≠ ⊥ := by
    intro E hEA hE9 hEB
    have hEel : CFSG.Assembly.IsElemAbelian 3 E := isElemAbelian_of_le h.isElemAbelian hEA
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
      Nat.prime_three E R ⟨hEel.1, hEel.2⟩ (by norm_num; exact hE9) (hEA.trans hAR)
      (by rw [hk]; exact Nat.Coprime.pow_right k (by norm_num))
    apply hR1
    rw [← hgen]
    refine le_bot_iff.mp (iSup_le fun D => iSup_le fun hD => ?_)
    obtain ⟨hDE, hD3⟩ := hD
    have hD3' : Nat.card D = 3 := by simpa using hD3
    by_contra hne
    have hAD : A ≤ Subgroup.normalizer
        ((Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
      (show A ≤ Subgroup.centralizer (D : Set G) from fun y hy =>
        Subgroup.mem_centralizer_iff.mpr fun d hd => h.commute (hEA (hDE hd)) hy).trans
        Subgroup.le_normalizer
    have hRD := hdich _ inf_le_left (le_normalizer_inf hAR hAD) (fun hb => hne (le_of_eq hb))
    have hDB : D ≤ E ⊓ B := by
      refine le_inf hDE fun d hd => ⟨hEA (hDE hd), Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro x hx
      have hxD : x ∈ R ⊓ Subgroup.centralizer (D : Set G) := by rw [hRD]; exact hx
      exact (Subgroup.mem_centralizer_iff.mp hxD.2 d hd).symm
    rw [hEB, le_bot_iff] at hDB
    rw [hDB, Subgroup.card_bot] at hD3'
    norm_num at hD3'
  have hcz : Nat.card (Subgroup.zpowers c) = 3 := h.card_zpowers
  have hzB : Subgroup.zpowers c ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxc, hxB⟩
    by_contra hx1
    have hzx := zpowers_eq_of_mem_of_ne_one hcz hxc hx1
    apply hcB
    have hcx : c ∈ Subgroup.zpowers x := hzx ▸ Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr hxB) hcx
  have hAcB : A ≤ Subgroup.zpowers c ⊔ B := by
    intro a haA
    by_contra ha
    have hac : a ∉ Subgroup.zpowers c := fun h' => ha (Subgroup.mem_sup_left h')
    have ha1 : a ≠ 1 := fun h' => hac (h' ▸ one_mem _)
    have haz : Nat.card (Subgroup.zpowers a) = 3 := by
      have hdvd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one (h.isElemAbelian.2 a haA)
      rw [Nat.card_zpowers]
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) ha1
      · exact h3
    set E := Subgroup.zpowers c ⊔ Subgroup.zpowers a with hE
    have hEA : E ≤ A := sup_le (Subgroup.zpowers_le.mpr h.mem_A) (Subgroup.zpowers_le.mpr haA)
    have hE9 : 9 ≤ Nat.card E := nine_le_card_of_lt hEA h.card_eq hcz
      (lt_of_le_of_ne le_sup_left fun heq => hac (by
        rw [heq]
        exact (le_sup_right : Subgroup.zpowers a ≤ E) (Subgroup.mem_zpowers a)))
    obtain ⟨⟨d, hdEB⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hEB E hEA hE9)
    have hd1' : d ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
    obtain ⟨hdE, hdB⟩ := Subgroup.mem_inf.mp hdEB
    have hza : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun y hy => by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_left (h.commute haA h.mem_A) j))).trans
      (Subgroup.centralizer_le_normalizer _)
    have hdE' : d ∈ ((Subgroup.zpowers c : Set G) * (Subgroup.zpowers a : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hza]
      exact hdE
    obtain ⟨y, hy, z, hz, hyz0⟩ := hdE'
    have hyz : y * z = d := hyz0
    have hzcB : z ∈ Subgroup.zpowers c ⊔ B := by
      have : z = y⁻¹ * d := by rw [← hyz]; group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left (inv_mem hy)) (Subgroup.mem_sup_right hdB)
    by_cases hz1 : z = 1
    · apply hd1'
      have hdy : d = y := by rw [← hyz, hz1, mul_one]
      have hdmem : d ∈ Subgroup.zpowers c ⊓ B := ⟨hdy ▸ hy, hdB⟩
      rw [hzB] at hdmem
      exact Subgroup.mem_bot.mp hdmem
    · have hzz := zpowers_eq_of_mem_of_ne_one haz hz hz1
      apply ha
      have haz' : a ∈ Subgroup.zpowers z := hzz ▸ Subgroup.mem_zpowers a
      exact (Subgroup.zpowers_le.mpr hzcB) haz'
  have hcBN : Subgroup.zpowers c ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      h.commute (hBA hy) h.mem_A)).trans (Subgroup.centralizer_le_normalizer _)
  have hsupcard : Nat.card (Subgroup.zpowers c ⊔ B : Subgroup G) ≤ 3 * Nat.card B := by
    calc Nat.card (Subgroup.zpowers c ⊔ B : Subgroup G)
        = Nat.card (((Subgroup.zpowers c ⊔ B : Subgroup G) : Set G)) := rfl
      _ = Nat.card ((Subgroup.zpowers c : Set G) * (B : Set G)) := by
          rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcBN]
      _ ≤ Nat.card (Subgroup.zpowers c : Set G) * Nat.card (B : Set G) := Set.natCard_mul_le
      _ = 3 * Nat.card B := by
          change Nat.card (Subgroup.zpowers c) * Nat.card B = 3 * Nat.card B
          rw [hcz]
  have hB9 : Nat.card B = 9 := by
    have h1 : 27 ≤ 3 * Nat.card B := by
      rw [← h.card_eq]
      exact (Subgroup.card_le_of_le hAcB).trans hsupcard
    have hdvd : Nat.card B ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h.card_eq]
      exact Subgroup.card_dvd_of_le hBA
    obtain ⟨j, hj, hjB⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hj3 : j ≠ 3 := by
      intro hj3
      apply hcB
      have hBeq : B = A := Subgroup.eq_of_le_of_card_ge hBA (by rw [hjB, hj3, h.card_eq]; norm_num)
      rw [hBeq]
      exact h.mem_A
    have hj2 : j ≤ 2 := by omega
    interval_cases j
    · rw [hjB] at h1
      norm_num at h1
    · rw [hjB] at h1
      norm_num at h1
    · rw [hjB]
      norm_num
  have hBW : B ≤ Subgroup.normalizer (W : Set G) :=
    (inf_le_right.trans (Subgroup.centralizer_le hWR)).trans (Subgroup.centralizer_le_normalizer _)
  have hAW : A ≤ Subgroup.normalizer (W : Set G) :=
    hAcB.trans (sup_le (Subgroup.zpowers_le.mpr hcW) hBW)
  have hW1 : W ≠ ⊥ := by
    intro hbot
    have hrW : r ∈ W := Subgroup.subset_closure (by simp)
    rw [hbot] at hrW
    exact hr1 (Subgroup.mem_bot.mp hrW)
  have hWeq := hdich W hWR hAW hW1
  refine ⟨?_, hB9⟩
  rw [← hWeq]
  exact hW4

end CFSG.RankThree.PartTwo.Sec16.Proof1623

