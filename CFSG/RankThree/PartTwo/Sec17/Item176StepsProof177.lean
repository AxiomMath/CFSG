module

public import CFSG.RankThree.PartTwo.Sec17.Item177Proof
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofTools
import CFSG.RankThree.PartTwo.Sec17.Item171ProofKFact
import CFSG.RankThree.PartTwo.Sec17.Item17TailEnd
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Step177MeetQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅V, Y₀⁆ ≠ ⊥ → V ⊓ Y₀ ∈ scriptQ A (lB A)

@[expose] noncomputable def Step177MainM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1514 A (lB A) c L → Item176 A (lB A) c L →
    omegaA A = {Subgroup.zpowers c} →
    ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅Y₀, V⁆ = ⊥ → ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ →
      (∀ b ∈ A ⊓ L, b ≠ 1 →
        ⁅V, Subgroup.zpowers c⁆ ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) = ⊥) →
      normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c ≤
        Subgroup.normalizer (Y₀ : Set G)

namespace Proof176Steps

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_of_forall_three_element {Y C : Subgroup G} (hY : Y = oPrimeResidualOf 3 Y)
    (h : ∀ y ∈ Y, ∀ k : ℕ, y ^ 3 ^ k = 1 → y ∈ C) : Y ≤ C := by
  rw [hY, oPrimeResidualOf, oPrimeResidual, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨y, ⟨k, hk⟩, rfl⟩
  exact h y y.2 k (by simpa using congrArg Subtype.val hk)

theorem commutator_inf_ne_bot
    {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) {V : Subgroup G}
    (hVM : V ≤ Subgroup.normalizer (Y₀ : Set G))
    (hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hVab : CFSG.Assembly.IsElemAbelian 2 V) (hVY : ⁅V, Y₀⁆ ≠ ⊥) : ⁅V ⊓ Y₀, A⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hWA
  set W := V ⊓ Y₀ with hWdef
  obtain ⟨⟨-, hAY⟩, hYres, -, hq⟩ := h.mem_y0Star.prop.1
  have hYM : Y₀ ≤ Subgroup.normalizer (Y₀ : Set G) := Subgroup.le_normalizer
  have hYV : Y₀ ≤ Subgroup.normalizer (V : Set G) := hYM.trans hMV
  have hYW : Y₀ ≤ Subgroup.normalizer (W : Set G) := le_normalizer_inf hYV hYM
  have hWC : W ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hWA
  set K : Subgroup ↥Y₀ := (Subgroup.centralizer (W : Set G)).subgroupOf Y₀ with hKdef
  have hKn : K.Normal := by
    refine ⟨fun k hk y => ?_⟩
    rw [hKdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hk ⊢
    intro w hw
    have hw' : (y : G)⁻¹ * w * (y : G) ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (hYW (inv_mem y.2)) w).mp hw
      simpa [mul_assoc] using this
    have h1 := hk _ hw'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc w * ((y : G) * (k : G) * (y : G)⁻¹)
        = (y : G) * (((y : G)⁻¹ * w * (y : G)) * (k : G)) * (y : G)⁻¹ := by group
      _ = (y : G) * ((k : G) * ((y : G)⁻¹ * w * (y : G))) * (y : G)⁻¹ := by rw [h1]
      _ = (y : G) * (k : G) * (y : G)⁻¹ * w := by group
  set O := CFSG.pCore 2 ↥Y₀ with hO
  set π₀ := QuotientGroup.mk' O with hπ₀
  have hKbar : (K.map π₀).Normal := hKn.map π₀ (QuotientGroup.mk'_surjective O)
  rcases Proof171.normal_le_center_or_eq_top hq hKbar with hcen | htop
  ·
    have hcomm : ∀ a ∈ A, ∀ y ∈ Y₀, a * y * a⁻¹ * y⁻¹ ∈ O.map Y₀.subtype := by
      intro a ha y hy
      set σ : MulAut ↥Y₀ := Y₀.normalizerMonoidHom ⟨a, hAY ha⟩ with hσ
      set α : MulAut (↥Y₀ ⧸ O) := QuotientGroup.congr O O σ (CFSG.pCore_map_iso 2 σ) with hα
      have hσapp : ∀ z : ↥Y₀, ((σ z : ↥Y₀) : G) = a * (z : G) * a⁻¹ := fun z => rfl
      have hαapp : ∀ z : ↥Y₀, α (π₀ z) = π₀ (σ z) := fun z => rfl
      have hα1 : α = 1 := by
        refine mulAut_eq_one_of_central hq.1 α fun q => ?_
        obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective O q
        rw [hαapp, ← map_inv, ← map_mul]
        refine hcen (Subgroup.mem_map_of_mem π₀ ?_)
        rw [hKdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
        intro w hw
        have haw : a * w = w * a := (Subgroup.mem_centralizer_iff.mp (hWC hw) a ha)
        have hzw : (z : G)⁻¹ * w * (z : G) ∈ W := by
          have := (Subgroup.mem_normalizer_iff.mp (hYW (inv_mem z.2)) w).mp hw
          simpa [mul_assoc] using this
        have haw' : a * ((z : G)⁻¹ * w * (z : G)) = ((z : G)⁻¹ * w * (z : G)) * a :=
          (Subgroup.mem_centralizer_iff.mp (hWC hzw) a ha)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσapp]
        calc w * ((z : G)⁻¹ * (a * (z : G) * a⁻¹))
            = (z : G)⁻¹ * (((z : G) * w * (z : G)⁻¹) * a) * (z : G) * a⁻¹ := by group
          _ = (z : G)⁻¹ * (a * ((z : G) * w * (z : G)⁻¹)) * (z : G) * a⁻¹ := by
              have hzw' : (z : G) * w * (z : G)⁻¹ ∈ W :=
                (Subgroup.mem_normalizer_iff.mp (hYW z.2) w).mp hw
              rw [(Subgroup.mem_centralizer_iff.mp (hWC hzw') a ha).symm]
          _ = (z : G)⁻¹ * (a * (z : G) * a⁻¹) * (a * w * a⁻¹) := by group
          _ = (z : G)⁻¹ * (a * (z : G) * a⁻¹) * w := by
              rw [haw]
              group
      have h1 : π₀ (σ ⟨y, hy⟩) = π₀ ⟨y, hy⟩ := by
        rw [← hαapp, hα1]
        rfl
      rw [hπ₀, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      have h2 : σ ⟨y, hy⟩ * (⟨y, hy⟩ : ↥Y₀)⁻¹ ∈ O := by
        have h3 := (CFSG.pCore_normal (p := 2) (G := ↥Y₀)).conj_mem _ (inv_mem h1)
          (⟨y, hy⟩ : ↥Y₀)
        have : σ ⟨y, hy⟩ * (⟨y, hy⟩ : ↥Y₀)⁻¹ =
            (⟨y, hy⟩ : ↥Y₀) * ((σ ⟨y, hy⟩)⁻¹ * ⟨y, hy⟩)⁻¹ * (⟨y, hy⟩ : ↥Y₀)⁻¹ := by group
        rw [this]
        exact h3
      refine ⟨_, h2, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hσapp]
    have hAsec : ∀ a ∈ A, a ∈ sectionCentralizer A L
        ((aschbacherSolvableCore 3 ↥L).map L.subtype) := by
      intro a ha
      refine ⟨ha, fun x hx => ?_⟩
      have he := hcomm a ha x (h.le_y0 hx)
      have heL : a * x * a⁻¹ * x⁻¹ ∈ L :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp (h.toSec13Data.le_normalizer ha) x).mp hx)
          (inv_mem hx)
      set T := (O.map Y₀.subtype).subgroupOf L with hT
      have hTn : T.Normal := by
        refine ⟨fun t ht l => ?_⟩
        rw [hT, Subgroup.mem_subgroupOf] at ht ⊢
        have hlY : (l : G) ∈ Y₀ := h.le_y0 l.2
        obtain ⟨o, ho, hot⟩ := ht
        refine ⟨⟨l, hlY⟩ * o * ⟨l, hlY⟩⁻¹,
          (CFSG.pCore_normal (p := 2) (G := ↥Y₀)).conj_mem o ho _, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hot ⊢
        rw [hot]
      have hT2 : IsPGroup 2 T :=
        ((CFSG.pCore_isPGroup (p := 2) (G := ↥Y₀)).map Y₀.subtype).comap_subtype
      have hTθ : T ≤ aschbacherSolvableCore 3 ↥L :=
        (le_sSup (⟨hTn, hT2⟩ : T ∈ {N : Subgroup ↥L | N.Normal ∧ IsPGroup 2 N}) :
          T ≤ CFSG.pCore 2 ↥L).trans
          ((solvable_prime_complement_core_characterization (H := ↥L)
            Nat.prime_three).2.2.2.2.2.2 2 Nat.prime_two (by norm_num))
      exact ⟨⟨_, heL⟩, hTθ (Subgroup.mem_subgroupOf.mpr he), rfl⟩
    have hAc : A ≤ Subgroup.zpowers c := fun a ha => by
      have := hAsec a ha
      rw [h.toSec13Data.sectionCentralizer_eq] at this
      exact this
    have h27 := Subgroup.card_le_of_le hAc
    rw [h.isE27.2, Nat.card_zpowers, h.toSec13Data.orderOf_eq] at h27
    omega
  ·
    have h3K : ∀ y ∈ Y₀, ∀ k : ℕ, y ^ 3 ^ k = 1 → y ∈ Subgroup.centralizer (W : Set G) := by
      intro y hy k hyk
      set y' : ↥Y₀ := ⟨y, hy⟩ with hy'
      obtain ⟨z, hzK, hz⟩ : ∃ z ∈ K, π₀ z = π₀ y' := by
        have : π₀ y' ∈ K.map π₀ := htop ▸ Subgroup.mem_top _
        exact this
      have ho : z⁻¹ * y' ∈ O := by
        rw [hπ₀, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hz
        exact hz
      obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y₀) ⟨_, ho⟩
      have hm' : (z⁻¹ * y') ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      set πK := QuotientGroup.mk' K with hπK
      have hz1 : πK z = 1 := by
        rw [hπK, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hzK
      have h1 : πK y' = πK (z⁻¹ * y') := by
        rw [map_mul, map_inv, hz1, inv_one, one_mul]
      have h2 : πK y' ^ 2 ^ m = 1 := by rw [h1, ← map_pow, hm', map_one]
      have h3 : πK y' ^ 3 ^ k = 1 := by
        rw [← map_pow, show y' ^ 3 ^ k = 1 from Subtype.ext (by simpa using hyk), map_one]
      have h4 : πK y' = 1 := by
        have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
        rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow m k (by norm_num)), Nat.dvd_one,
          orderOf_eq_one_iff] at this
      have h5 : y' ∈ K := (QuotientGroup.eq_one_iff y').mp h4
      exact Subgroup.mem_subgroupOf.mp h5
    have hYC : Y₀ ≤ Subgroup.centralizer (W : Set G) := le_of_forall_three_element hYres h3K
    have hVYW : ⁅V, Y₀⁆ ≤ W :=
      le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hYV)
        (by rw [Subgroup.commutator_comm]; exact
          Subgroup.le_normalizer_iff_commutator_le_left.mp hVM)
    have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hVab
    have hV3 : ¬ 3 ∣ Nat.card V := by
      obtain ⟨n, hn⟩ := hV2.exists_card_eq
      rw [hn]
      intro h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    have h3V : ∀ y ∈ Y₀, ∀ k : ℕ, y ^ 3 ^ k = 1 → y ∈ Subgroup.centralizer (V : Set G) := by
      intro y hy k hyk
      have hP : IsPGroup 3 (Subgroup.zpowers y) := by
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hyk)
        exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
      have hPV : Subgroup.zpowers y ≤ Subgroup.normalizer (V : Set G) :=
        Subgroup.zpowers_le.mpr (hYV hy)
      have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
        Nat.prime_three (Subgroup.zpowers y) V hP hV3 hPV
      have hle : ⁅V, Subgroup.zpowers y⁆ ≤ W :=
        (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hy)).trans hVYW
      have hbot : ⁅⁅V, Subgroup.zpowers y⁆, Subgroup.zpowers y⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
        have hyx : x * y = y * x := Subgroup.mem_centralizer_iff.mp (hYC hy) x (hle hx)
        exact ((show Commute y x from hyx.symm).zpow_left j).eq
      rw [hidem] at hbot
      have hVC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_iff.mp (hVC hv) y (Subgroup.mem_zpowers y)).symm
    have hYCV : Y₀ ≤ Subgroup.centralizer (V : Set G) := le_of_forall_three_element hYres h3V
    apply hVY
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp hYCV

end Proof176Steps

open Proof176Steps in
theorem step177Meet_of (hQ : Step177MeetQ) : Step177Meet := by
  intro G _ _ A c L Y₀ h V hV hVY
  obtain ⟨hVM, hMV, hVab⟩ := hV.prop
  exact ⟨hQ G A c L Y₀ h V hV hVY, commutator_inf_ne_bot h hVM hMV hVab hVY⟩

end CFSG.RankThree.PartTwo.Sec17
