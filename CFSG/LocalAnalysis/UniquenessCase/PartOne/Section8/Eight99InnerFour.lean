module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveStepD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem r899_outer_comm_Sz {X : Type} [Group X] {n : ℕ}
    (h : IsSz X n) : ∀ a b : Outer X, a * b = b * a := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := (CFSG.Blueprint.LieModel.suzukiModel h).2
  have : IsCyclic (Outer (CFSG.Blueprint.suzukiGroup a K)) :=
    (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).1
  have : IsCyclic (Outer X) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).isCyclic.2 inferInstance
  intro x y
  exact IsMulCommutative.is_comm.comm x y

theorem r899_inner_of_hom {H X : Type} [Group H] [Finite H] [Group X] [Finite X]
    (ρ : H →* MulAut X) {p : ℕ} (hp : p.Prime) (hcomm : ∀ a b : Outer X, a * b = b * a)
    (hOp : uc22p22g_OpEq p H) {h : H} {b : ℕ} (hh : h ^ (p ^ b) = 1) :
    ρ h ∈ (MulAut.conj : X →* MulAut X).range := by
  classical
  have : Finite (Outer X) := uc22p22g_finite_outer X
  let ψ : H →* Outer X :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)).comp ρ
  let Q : Subgroup (Outer X) := ψ.range
  have : Finite Q := Finite.of_injective _ Subtype.val_injective
  obtain ⟨a, m, hm, hcard⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := Q)).ne' p hp.ne_one
  let r : H →* Q := ψ.rangeRestrict
  have hrcomm : ∀ x y : H, Commute (r x) (r y) := fun x y =>
    Subtype.ext (hcomm (ψ x) (ψ y))
  let f : H →* Q :=
    { toFun := fun x => (r x) ^ m
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul, (hrcomm x y).mul_pow] }
  have hf : IsPGroup p ↥f.range := by
    intro z
    obtain ⟨x, hx⟩ := z.2
    refine ⟨a, ?_⟩
    have hz : (z : Q) = (r x) ^ m := hx.symm
    have h0 : (z : Q) ^ (p ^ a) = 1 := by
      rw [hz, ← pow_mul, show m * p ^ a = Nat.card Q by rw [hcard, mul_comm]]
      exact pow_card_eq_one'
    exact Subtype.ext (by simpa using h0)
  have hf1 := hOp Q f hf
  have h1 : (r h) ^ m = 1 := by
    have : f h ∈ f.range := ⟨h, rfl⟩
    rw [hf1] at this
    exact Subgroup.mem_bot.1 this
  have h2 : (r h) ^ (p ^ b) = 1 := by rw [← map_pow, hh, map_one]
  have hcop : Nat.Coprime (p ^ b) m :=
    Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have h3 : r h = 1 := by
    have h4 : orderOf (r h) ∣ Nat.gcd (p ^ b) m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
    rw [hcop.gcd_eq_one] at h4
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  have h5 : ψ h = 1 := congrArg Subtype.val h3
  exact (QuotientGroup.eq_one_iff
    (N := CFSG.ComponentClassification.OuterAutomorphisms.inner X) (x := ρ h)).1 h5

theorem r899_inner_of_le_normalizer {M K : Subgroup G} (hMK : M ≤ normalizer (K : Set G))
    {p : ℕ} (hp : p.Prime) (hOp : F10.OpRes p M = M)
    (hcomm : ∀ a b : Outer (Bar2 K), a * b = b * a) {a : G} (ha : a ∈ M) (hap : a ^ p = 1) :
    UC6S846.rhoL K ⟨a, hMK ha⟩ ∈ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
  have hOp' : uc22p22g_OpEq p ↥M :=
    PartTwo.S17.uc22p22g_opEq_of_surjective (MonoidHom.id _) Function.surjective_id hp hOp
  have hh : (⟨a, ha⟩ : ↥M) ^ (p ^ 1) = 1 := by
    rw [pow_one]
    exact Subtype.ext hap
  have h1 := r899_inner_of_hom ((UC6S846.rhoL K).comp (Subgroup.inclusion hMK)) hp hcomm hOp' hh
  have h2 : ((UC6S846.rhoL K).comp (Subgroup.inclusion hMK)) ⟨a, ha⟩ =
      UC6S846.rhoL K ⟨a, hMK ha⟩ := by
    rw [MonoidHom.comp_apply]
    congr 1
  rwa [h2] at h1

theorem r899_exists_centralizesBar_of_inner {K : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hZ : center (Bar2 K) = ⊥)
    (hle : ∀ Q : Subgroup (Bar2 K), IsElemAbelian p Q → Nat.card Q ≤ p)
    {B : Subgroup G} (hB : IsElemAbelian p B) (hBN : B ≤ normalizer (K : Set G))
    (hinn : ∀ b (hb : b ∈ B),
      UC6S846.rhoL K ⟨b, hBN hb⟩ ∈ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range) :
    ∃ C : Subgroup G, C ≤ B ∧ (∀ c ∈ C, CentralizesBar c K) ∧ Nat.card B ≤ p * Nat.card C := by
  let φ : ↥B →* MulAut (Bar2 K) := (UC6S846.rhoL K).comp (Subgroup.inclusion hBN)
  have hinj : Function.Injective (MulAut.conj : Bar2 K →* MulAut (Bar2 K)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ
  have hpow : ∀ b : ↥B, φ b ^ p = 1 := by
    intro b
    rw [← map_pow]
    have : b ^ p = 1 := Subtype.ext (by simpa using hB.2 _ b.2)
    rw [this, map_one]
  have hinn' : φ.range ≤ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
    rintro _ ⟨b, rfl⟩
    exact hinn b b.2
  set Q : Subgroup (Bar2 K) := φ.range.comap MulAut.conj with hQ
  have hQcard : Nat.card Q = Nat.card φ.range := by
    rw [← Subgroup.map_comap_eq_self hinn', Subgroup.card_map_of_injective hinj]
  have hQel : IsElemAbelian p Q := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · obtain ⟨a, ha⟩ : MulAut.conj (x : Bar2 K) ∈ φ.range := x.2
      obtain ⟨b, hb⟩ : MulAut.conj (y : Bar2 K) ∈ φ.range := y.2
      have hab : a * b = b * a := by
        have : IsMulCommutative ↥B := hB.1
        exact mul_comm' a b
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, ← ha, ← hb, ← map_mul, hab,
        map_mul]
    · obtain ⟨a, ha⟩ : MulAut.conj x ∈ φ.range := hx
      rw [map_pow, ← ha, hpow, map_one]
  have hQle : Nat.card Q ≤ p := hle Q hQel
  refine ⟨φ.ker.map B.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨hBN b.2, fun l hl => ?_⟩
    have h1 : UC6S846.rhoL K (Subgroup.inclusion hBN b) = 1 := hb
    have h2 : UC6S846.rhoL K (Subgroup.inclusion hBN b) (QuotientGroup.mk ⟨l, hl⟩) =
        QuotientGroup.mk ⟨l, hl⟩ := by
      rw [h1, MulAut.one_apply]
    exact (UC6S846.rhoL_fix_iff K _ ⟨l, hl⟩).1 h2
  · rw [Subgroup.card_map_of_injective B.subtype_injective, ← Subgroup.card_ker_mul_card_range φ,
      mul_comm p]
    exact Nat.mul_le_mul_left _ (hQcard ▸ hQle)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
