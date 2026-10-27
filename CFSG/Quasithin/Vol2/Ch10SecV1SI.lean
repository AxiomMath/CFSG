module

public import CFSG.Quasithin.Vol2.Ch10SecV1SG

public noncomputable section

namespace CFSG.Quasithin.Vol2.Ch10.V1C.A319

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank
open scoped Matrix

theorem three_le_pRank_of_gens {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x z c : G} (hx : x ^ p = 1) (hz : z ^ p = 1) (hc : c ^ p = 1) (hxz : Commute x z)
    (hxc : Commute x c) (hzc : Commute z c) (hx1 : x ≠ 1) (hz1 : ∀ n : ℕ, x ^ n ≠ z)
    (hc1 : ∀ m n : ℕ, x ^ m * z ^ n ≠ c) : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  set B₀ : Subgroup G := ⊥
  have h₀ : ∀ b : B₀, B₀.subtype b = 1 := fun b => Subgroup.mem_bot.1 b.2
  have hc₀ : ∀ a b : B₀, a * b = b * a := fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])
  have hp₀ : ∀ a : B₀, a ^ p = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, Subgroup.mem_bot.1 a.2, one_pow])
  have hcard₀ : Nat.card B₀ = p ^ 0 := by rw [pow_zero]; exact Subgroup.card_bot
  obtain ⟨F₁, hF₁, hc₁, hp₁, hcard₁, hr₁⟩ := exists_extend hc₀ hp₀ hcard₀ B₀.subtype
    Subtype.val_injective (y := x) hx (by
      rintro ⟨b, hb⟩
      exact hx1 (hb ▸ h₀ b))
    (fun b => by rw [h₀ b]; exact Commute.one_left x)
  have hr₁' : ∀ a, ∃ n : ℕ, F₁ a = x ^ n := fun a => by
    obtain ⟨b, n, hb⟩ := hr₁ a
    exact ⟨n, by rw [hb, h₀ b, one_mul]⟩
  obtain ⟨F₂, hF₂, hc₂, hp₂, hcard₂, hr₂⟩ := exists_extend hc₁ hp₁ hcard₁ F₁ hF₁ (y := z)
    hz (by
      rintro ⟨a, ha⟩
      obtain ⟨n, hn⟩ := hr₁' a
      exact hz1 n (hn ▸ ha))
    (fun a => by
      obtain ⟨n, hn⟩ := hr₁' a
      rw [hn]
      exact hxz.pow_left n)
  have hr₂' : ∀ a, ∃ m n : ℕ, F₂ a = x ^ m * z ^ n := fun a => by
    obtain ⟨b, n, hb⟩ := hr₂ a
    obtain ⟨m, hm⟩ := hr₁' b
    exact ⟨m, n, by rw [hb, hm]⟩
  obtain ⟨F₃, hF₃, hc₃, hp₃, hcard₃, -⟩ := exists_extend hc₂ hp₂ hcard₂ F₂ hF₂ (y := c)
    hc (by
      rintro ⟨a, ha⟩
      obtain ⟨m, n, hmn⟩ := hr₂' a
      exact hc1 m n (hmn ▸ ha))
    (fun a => by
      obtain ⟨m, n, hmn⟩ := hr₂' a
      rw [hmn]
      exact (hxc.pow_left m).mul_left (hzc.pow_left n))
  exact le_pRank_of_injective hp.out.one_lt hc₃ hp₃ hcard₃ F₃ hF₃ le_top

variable {H : Type} [Group H] {L : Subgroup H} {K : Type} [Field K]
  (φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K))

theorem det_mat (l : ↥L) : (mat φ l).det = 1 := by
  have h := (specialLinearGroupEquivStatedSL 3 K).apply_symm_apply (φ (QuotientGroup.mk l))
  rw [mat, ← h, specialLinearGroupEquivStatedSL_coe]
  exact ((specialLinearGroupEquivStatedSL 3 K).symm (φ (QuotientGroup.mk l))).2

theorem mat_pow (l : ↥L) (n : ℕ) : mat φ (l ^ n) = mat φ l ^ n := by
  induction n with
  | zero => simp [mat]
  | succ n ih => rw [pow_succ, mat_mul, ih, pow_succ]

theorem mat_one : mat φ (1 : ↥L) = 1 := by
  simp [mat]

@[expose] def O2 (L : Subgroup H) : Subgroup H := (CFSG.pCore 2 ↥L).map L.subtype

theorem O2_le : O2 L ≤ L := by
  rintro _ ⟨l, -, rfl⟩
  exact l.2

theorem O2_normal (hL : L.Normal) : (O2 L).Normal :=
  ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 ↥L)
      (mem_normalizer_of_normal hL g)) n).mp hn⟩

theorem mat_eq_one_iff (l : ↥L) : mat φ l = 1 ↔ (l : H) ∈ O2 L := by
  constructor
  · intro h
    exact ⟨l, mem_pCore_of_mat φ h, rfl⟩
  · rintro ⟨l', hl', hl⟩
    have e : l' = l := Subtype.ext hl
    subst e
    have h1 : (QuotientGroup.mk l' : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 :=
      (QuotientGroup.eq_one_iff l').mpr hl'
    simp [mat, h1]

end CFSG.Quasithin.Vol2.Ch10.V1C.A319
