module

public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424Model
import CFSG.RankThree.PartTwo.Sec15.ONanKS1424CoreLift
import CFSG.RankThree.PartTwo.Sec15.ONanKS1424CoreEven

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial Matrix

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem lmodel_ker {X : Type} [Group X] (hK : PiField π p f K) (M : LModel π p f K X) :
    (∀ g : ↥(slPi π 3 (p ^ f) K), M.μ g = 1 → g ^ 3 = 1) ∧
      ∀ g : ↥(slPi π 3 (p ^ f) K), M.μ g = 1 → ∀ x : ↥(slPi π 3 (p ^ f) K), x * g = g * x := by
  constructor
  · intro g hg
    obtain ⟨c, hc⟩ := (M.ker_iff g).mp hg
    have hdet := det_eq_one hK g
    have hc3 : c ^ 3 = 1 := by
      rw [← hc, det_scalar_three] at hdet
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
    apply Subtype.ext
    show (g : GL (Fin 3) K) ^ 3 = 1
    rw [← hc, ← map_pow, hc3, map_one]
  · intro g hg x
    obtain ⟨c, hc⟩ := (M.ker_iff g).mp hg
    apply Subtype.ext
    show (x : GL (Fin 3) K) * g = g * x
    rw [← hc]
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (x : GL (Fin 3) K)).eq

theorem core_even (hK : PiField π 2 f K) {X : Type} [Group X] [Finite X] (M : LModel π 2 f K X)
    {R : Subgroup X} (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R) {H : Subgroup X}
    (hH : H ≤ Subgroup.normalizer (R : Set X)) {T : Type} [Group T] [IsSimpleGroup T] {t₄ : T}
    (ht4 : orderOf t₄ = 4) (φ : ↥H →* T) (hφ : Function.Surjective φ) : False := by
  have := hK.finite
  have := hK.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := slPi π 3 (2 ^ f) K with hL
  obtain ⟨hker, hcen⟩ := lmodel_ker hK M
  obtain ⟨S, hS2, hSR, hSinj, hSn⟩ := exists_lift M.μ M.surjective hker hcen R hR2
  have hSne : S ≠ ⊥ := by
    intro h
    apply hR1
    rw [← hSR, h, Subgroup.map_bot]
  set S₀ : Subgroup (GL (Fin 3) K) := S.map L.subtype with hS₀
  have hS₀2 : IsPGroup 2 S₀ := hS2.map L.subtype
  have hS₀ne : S₀ ≠ ⊥ := by
    intro h
    apply hSne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have : (x : GL (Fin 3) K) ∈ S₀ := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subtype.ext this
  set Hc : Subgroup ↥L := H.comap M.μ with hHc
  set Hh : Subgroup (GL (Fin 3) K) := Hc.map L.subtype with hHh
  have hHhn : Hh ≤ Subgroup.normalizer (S₀ : Set (GL (Fin 3) K)) := by
    rintro _ ⟨h, hh, rfl⟩
    have hn := hSn h (hH hh)
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨s, hs, rfl⟩ := hx
    exact ⟨h * s * h⁻¹, (Subgroup.mem_normalizer_iff.mp hn s).mp hs, rfl⟩
  obtain ⟨N, hNH, hN2, hNn, hN2el⟩ := exists_unipotent_normal hS₀ne hS₀2 hHhn
  let μH : ↥Hc →* ↥H := (M.μ.comp Hc.subtype).codRestrict H fun g => g.2
  let φ' : ↥Hc →* T := φ.comp μH
  have hφ' : Function.Surjective φ' := fun t => by
    obtain ⟨h, rfl⟩ := hφ t
    obtain ⟨g, hg⟩ := M.surjective (h : X)
    exact ⟨⟨g, by rw [hHc, Subgroup.mem_comap, hg]; exact h.2⟩, by
      show φ ⟨M.μ g, _⟩ = φ h
      congr 1
      exact Subtype.ext hg⟩
  let Nc : Subgroup ↥Hc := N.comap (L.subtype.comp Hc.subtype)
  have hNcn : Nc.Normal := ⟨fun x hx y => by
    have hy : ((y : ↥L) : GL (Fin 3) K) ∈ Hh := ⟨y, y.2, rfl⟩
    exact hNn _ hy _ hx⟩
  have hT₀n : (Nc.map φ').Normal := hNcn.map φ' hφ'
  have hT₀ : Nc.map φ' = ⊥ := by
    rcases hT₀n.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx, hxt⟩ := (show t₄ ∈ Nc.map φ' by rw [h]; exact Subgroup.mem_top _)
      have hx2 : x ^ 2 = 1 := Subtype.ext (Subtype.ext (by simpa using hN2 _ hx))
      have : t₄ ^ 2 = 1 := by rw [← hxt, ← map_pow, hx2, map_one]
      have := orderOf_dvd_of_pow_eq_one this
      rw [ht4] at this
      omega
  obtain ⟨h₁, rfl⟩ := hφ t₄
  obtain ⟨g₁, hg₁⟩ := M.surjective (h₁ : X)
  have hg₁c : g₁ ∈ Hc := by rw [hHc, Subgroup.mem_comap, hg₁]; exact h₁.2
  obtain ⟨a, m, hm, ho⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g₁).ne'
  set g₂ : ↥Hc := ⟨g₁ ^ m, Hc.pow_mem hg₁c m⟩ with hg₂
  have hg₂a : (g₂ : ↥L) ^ (2 ^ a) = 1 := by
    show (g₁ ^ m) ^ (2 ^ a) = 1
    rw [← pow_mul, mul_comm, ← ho]
    exact pow_orderOf_eq_one g₁
  have hg₂N : g₂ ^ 2 ∈ Nc := by
    have h1 : (((g₂ : ↥L)) : GL (Fin 3) K) ∈ Hh := ⟨g₂, g₂.2, rfl⟩
    have h2 : (((g₂ : ↥L)) : GL (Fin 3) K) ^ (2 ^ a) = 1 := by
      have := congrArg Subtype.val hg₂a
      simpa using this
    exact hN2el _ h1 a h2
  have hφg₂ : φ' (g₂ ^ 2) = 1 := by
    have : φ' (g₂ ^ 2) ∈ Nc.map φ' := ⟨_, hg₂N, rfl⟩
    rw [hT₀, Subgroup.mem_bot] at this
    exact this
  have hφg : φ' g₂ = φ h₁ ^ m := by
    show φ ⟨M.μ (g₁ ^ m), _⟩ = _
    rw [← map_pow]
    congr 1
    apply Subtype.ext
    show M.μ (g₁ ^ m) = ((h₁ ^ m : ↥H) : X)
    rw [map_pow, hg₁]
    rfl
  have hord : orderOf (φ h₁ ^ m) = 4 := by
    have hcop : Nat.Coprime 4 m := by
      have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
      simpa using this
    rw [orderOf_pow' (φ h₁) hm.pos.ne', ht4, Nat.Coprime.gcd_eq_one hcop, Nat.div_one]
  have hsq : (φ h₁ ^ m) ^ 2 = 1 := by
    rw [← hφg, ← map_pow]
    exact hφg₂
  have := orderOf_dvd_of_pow_eq_one hsq
  rw [hord] at this
  omega

end CFSG.RankThree.PartTwo.Sec15.KS1424
