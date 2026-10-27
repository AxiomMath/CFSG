module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProofDefs
import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofL

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

@[expose] def KSL3OddE9Aut : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e →
    Sec4.IsoLThreePi T p e →
    ∀ E : Subgroup (MulAut T), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      ∃ S : Subgroup T, S ≠ ⊥ ∧ IsPGroup 2 S ∧ ∀ σ ∈ E, S.map (σ : T →* T) = S

namespace KS163QLProof

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def autHom {A L : Subgroup G} (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    A →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
  (Sec4.thetaQuotMulAut L).comp (L.normalizerMonoidHom.comp (Subgroup.inclusion hAL))

theorem autHom_mk {A L : Subgroup G} (hAL : A ≤ Subgroup.normalizer (L : Set G)) (a : A)
    (l : L) : autHom hAL a (l : L ⧸ aschbacherSolvableCore 3 L) =
      ((⟨(a : G) * l * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hAL a.2) l).mp l.2⟩ : L) :
        L ⧸ aschbacherSolvableCore 3 L) := by
  simp only [autHom, MonoidHom.comp_apply]
  rw [Sec4.thetaQuotMulAut_mk]
  congr 1

theorem autHom_eq_one_iff {A L : Subgroup G} (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (a : A) : autHom hAL a = 1 ↔
      (a : G) ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
  have key : ∀ l (hl : l ∈ L),
      (((⟨(a : G) * l * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hAL a.2) l).mp hl⟩ : L) :
          L ⧸ aschbacherSolvableCore 3 L) = ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ↔
        (a : G) * l * (a : G)⁻¹ * l⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype) := by
    intro l hl
    rw [← mul_inv_eq_one, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨t, ht, hte⟩
      have : t = (⟨(a : G) * l * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hAL a.2) l).mp hl⟩ *
          (⟨l, hl⟩ : L)⁻¹ : L) := Subtype.ext hte
      rw [← this]
      exact ht
  constructor
  · intro h1
    refine ⟨a.2, fun l hl => ?_⟩
    have h2 := congrArg (fun τ : MulAut (L ⧸ aschbacherSolvableCore 3 L) =>
      τ ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)) h1
    simp only [MulAut.one_apply] at h2
    rw [autHom_mk] at h2
    exact (key l hl).mp h2
  · rintro ⟨-, h⟩
    ext x
    induction x using QuotientGroup.induction_on with
    | H l =>
      rw [MulAut.one_apply, autHom_mk]
      exact (key l l.2).mpr (h l l.2)

theorem card_autImage {A L : Subgroup G} {c : G} (h : Sec13Data G A c L) :
    CFSG.Assembly.IsElemAbelian 3 (autHom h.mem_lA.2.1).range ∧
      Nat.card (autHom h.mem_lA.2.1).range = 9 := by
  set ρ := autHom h.mem_lA.2.1 with hρ
  have hA := h.isElemAbelian
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    change (x : MulAut (L ⧸ aschbacherSolvableCore 3 L)) * (y : MulAut _) =
      (y : MulAut _) * (x : MulAut _)
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact isMulCommutative_iff.mp hA.1 a b
  · obtain ⟨a, rfl⟩ := hy
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (by simpa using hA.2 a a.2)
    rw [this, map_one]
  ·
    have hker : ∀ a : A, a ∈ ρ.ker ↔ (a : G) ∈ Subgroup.zpowers c := by
      intro a
      rw [MonoidHom.mem_ker, hρ, autHom_eq_one_iff, h.mem_lA.2.2.1]
      rfl
    have hc3 : Nat.card (Subgroup.zpowers c) = 3 := (zpowers_mem_omegaA_iff.mp
      h.zpowers_mem_omegaA).2.1
    have hle : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr h.mem_A
    have hkcard' : Nat.card ρ.ker = Nat.card (Subgroup.zpowers c) :=
      Nat.card_congr ⟨fun x => ⟨(x : A), (hker x).mp x.2⟩,
        fun y => ⟨⟨y, hle y.2⟩, (hker _).mpr y.2⟩, fun x => rfl, fun y => rfl⟩
    have hkcard : Nat.card ρ.ker = 3 := hkcard'.trans hc3
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [h.card_eq, hkcard, Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv] at h1
    omega

end KS163QLProof

open KS163QLProof in
theorem ks163QLInvL3_of (hK : KSL3OddE9Aut) : KS163QLInvL3 := by
  intro G _ _ A c L h hn2 hL3 _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  obtain ⟨p, e, _, he, hiso⟩ := hL3
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hn2 ⟨e, he, hiso⟩
  set θ := aschbacherSolvableCore 3 L with hθ
  set ρ := autHom hD.mem_lA.2.1 with hρ
  obtain ⟨hEab, hE9⟩ := card_autImage hD
  obtain ⟨S, hS1, hS2, hSE⟩ := hK _ p e hp2 he hiso ρ.range hEab hE9
  set π := QuotientGroup.mk' θ with hπ
  set K₀ := S.comap π with hK₀
  set K := K₀.map L.subtype with hKdef
  have hKL : K ≤ L := Subgroup.map_subtype_le K₀
  have hKcard : Nat.card K = Nat.card S * Nat.card θ := by
    rw [hKdef, Subgroup.card_map_of_injective L.subtype_injective, hK₀,
      Steps165.card_comap_of_surjective' π (QuotientGroup.mk'_surjective θ) S, hπ,
      QuotientGroup.ker_mk']
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hS3 : ¬ 3 ∣ Nat.card S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
    rw [hk]
    intro h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  have hS2' : 2 ∣ Nat.card S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
    have h1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hS1
    rw [hk] at h1 ⊢
    rcases k with _ | k
    · simp at h1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    have hfwd : ∀ (b : A), ∀ x ∈ K, (b : G) * x * (b : G)⁻¹ ∈ K := by
      intro b x hx
      obtain ⟨l, hl, rfl⟩ := hx
      have hlS : π l ∈ S := hl
      have hm : (ρ b) (π l) ∈ S := by
        rw [← hSE (ρ b) ⟨b, rfl⟩]
        exact ⟨_, hlS, rfl⟩
      rw [hρ, hπ, QuotientGroup.mk'_apply, autHom_mk] at hm
      exact ⟨_, hm, rfl⟩
    intro x
    constructor
    · exact hfwd ⟨a, ha⟩ x
    · intro hx
      have := hfwd ⟨a⁻¹, inv_mem ha⟩ _ hx
      simpa [mul_assoc] using this
  refine ⟨K, hKL, hAK, ?_, ?_⟩
  · rw [hKcard]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact hS3 h
    · exact hθ3 h
  · rw [hKcard]
    exact hS2'.mul_right _

end CFSG.RankThree.PartTwo.Sec16
