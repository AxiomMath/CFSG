module

public import CFSG.RankThree.PartTwo.Sec19.Step1917StepsZ2
import CFSG.RankThree.PartTwo.Sec19.Step1919O2

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.ABGLocalTools (IsSylowOf)

namespace Step1917Steps

@[expose] def ThreeCentralZ2 (X : Type) [Group X] : Prop :=
  ∀ x : X, x ≠ 1 →
    (∃ S : Sylow 3 X, x ∈ (S : Subgroup X) ∧ ∀ s ∈ (S : Subgroup X), s * x = x * s) →
    ∃ P : Subgroup X, IsPGroup 3 P ∧ ∃ hx : x ∈ P,
      (⟨x, hx⟩ : P) ∈ Subgroup.upperCentralSeries P 2 ∧ (⟨x, hx⟩ : P) ∉ Subgroup.center P

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem mem_center_map_iff (f : X →* Y) {P : Subgroup X} {P' : Subgroup Y}
    (hPP' : P.map f = P') (hf : Set.InjOn f P) {x : X} (hx : x ∈ P) (hfx : f x ∈ P') :
    (⟨f x, hfx⟩ : P') ∈ Subgroup.center P' ↔ (⟨x, hx⟩ : P) ∈ Subgroup.center P := by
  subst hPP'
  rw [mem_center_iff_of_mem, mem_center_iff_of_mem]
  constructor
  · intro h p hp
    refine hf (P.mul_mem hp hx) (P.mul_mem hx hp) ?_
    rw [map_mul, map_mul]
    exact h (f p) (Subgroup.mem_map_of_mem f hp)
  · rintro h _ ⟨p, hp, rfl⟩
    rw [← map_mul, ← map_mul, h p hp]

theorem mem_upperCentralSeries_two_map_iff (f : X →* Y) {P : Subgroup X} {P' : Subgroup Y}
    (hPP' : P.map f = P') (hf : Set.InjOn f P) {x : X} (hx : x ∈ P) (hfx : f x ∈ P') :
    (⟨f x, hfx⟩ : P') ∈ Subgroup.upperCentralSeries P' 2 ↔
      (⟨x, hx⟩ : P) ∈ Subgroup.upperCentralSeries P 2 := by
  subst hPP'
  rw [mem_upperCentralSeries_two_iff_of_mem, mem_upperCentralSeries_two_iff_of_mem]
  constructor
  · intro h p hp q hq
    have hc : x * p * x⁻¹ * p⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem hx hp) (P.inv_mem hx)) (P.inv_mem hp)
    refine hf (P.mul_mem hq hc) (P.mul_mem hc hq) ?_
    have := h (f p) (Subgroup.mem_map_of_mem f hp) (f q) (Subgroup.mem_map_of_mem f hq)
    simpa [map_mul, map_inv] using this
  · rintro h _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    have := congrArg f (h p hp q hq)
    simpa [map_mul, map_inv] using this

theorem threeCentralZ2_of_mulEquiv [Finite X] (φ : X ≃* Y) (h : ThreeCentralZ2 Y) :
    ThreeCentralZ2 X := by
  intro x hx1 ⟨S, hxS, hxc⟩
  have hφs : Function.Surjective φ.toMonoidHom := φ.surjective
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  obtain ⟨P', hP'3, hxP', h2, hZ⟩ := h (φ x)
    (fun h1 => hx1 (φ.injective (h1.trans φ.map_one.symm)))
    ⟨S.mapSurjective hφs, ⟨x, hxS, rfl⟩, by
      rintro _ ⟨s, hs, rfl⟩
      change φ s * φ x = φ x * φ s
      rw [← map_mul, ← map_mul, hxc s hs]⟩
  set P := P'.map φ.symm.toMonoidHom with hP
  have hPP' : P.map φ.toMonoidHom = P' := by
    rw [hP, Subgroup.map_map]
    convert Subgroup.map_id P'
    ext y
    simp
  have hxP : x ∈ P := ⟨φ x, hxP', by simp⟩
  refine ⟨P, hP'3.map φ.symm.toMonoidHom, hxP, ?_, ?_⟩
  · exact (mem_upperCentralSeries_two_map_iff φ.toMonoidHom hPP' hinj.injOn hxP hxP').mp h2
  · exact fun h' => hZ ((mem_center_map_iff φ.toMonoidHom hPP' hinj.injOn hxP hxP').mpr h')

end Transport

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_of_threeCentralZ2 {L T : Subgroup G} {z : G} (hTL : IsSylowOf 3 (T ⊓ L) L)
    (hzT : z ∈ T) (hzL : z ∈ L) (hz1 : z ≠ 1) (hzc : ∀ t ∈ T, t * z = z * t)
    (hX : ThreeCentralZ2 (L ⧸ CFSG.pCore 2 L)) :
    ∃ P : Subgroup G, P ≤ L ∧ IsPGroup 3 P ∧ ∃ hzP : z ∈ P,
      (⟨z, hzP⟩ : P) ∈ Subgroup.upperCentralSeries P 2 ∧ (⟨z, hzP⟩ : P) ∉ Subgroup.center P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 L with hN
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set z' : L := ⟨z, hzL⟩ with hz'
  obtain ⟨S₀, hS₀⟩ := hTL
  have hmemS₀ : ∀ s : L, s ∈ (S₀ : Subgroup L) ↔ (s : G) ∈ T ⊓ L := by
    intro s
    rw [← hS₀]
    constructor
    · intro hs
      exact ⟨s, hs, rfl⟩
    · rintro ⟨y, hy, hys⟩
      rwa [← Subtype.ext hys]
  have hz'S₀ : z' ∈ (S₀ : Subgroup L) := (hmemS₀ z').mpr ⟨hzT, hzL⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, z ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := S₀.isPGroup' ⟨z', hz'S₀⟩
    exact ⟨k, by simpa [hz'] using congrArg (fun w : (S₀ : Subgroup L) => ((w : L) : G)) hk⟩
  have hx1 : π z' ≠ 1 := by
    intro h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := L)) ⟨z', h⟩
    exact hz1 (eq_one_of_pow_two_pow_of_pow_three_pow
      (by simpa [hz'] using congrArg (fun w : N => ((w : L) : G)) hj) hk)
  obtain ⟨Pb, hPb3, hxPb, h2, hZ⟩ := hX (π z') hx1 ⟨S₀.mapSurjective hπs, ⟨z', hz'S₀, rfl⟩, by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc s ((hmemS₀ s).mp hs).1)⟩
  set P₁ := Pb.comap π with hP₁
  have hz'P₁ : z' ∈ P₁ := hxPb
  have hzpow : IsPGroup 3 (Subgroup.zpowers (⟨z', hz'P₁⟩ : P₁)) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨k, Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_zpow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    simp [hz', hk]
  obtain ⟨R₀, hR₀⟩ := hzpow.exists_le_sylow
  set R : Subgroup L := (R₀ : Subgroup P₁).map P₁.subtype with hR
  have hz'R : z' ∈ R := ⟨⟨z', hz'P₁⟩, hR₀ (Subgroup.mem_zpowers _), rfl⟩
  have hR3 : IsPGroup 3 R := R₀.isPGroup'.map _
  have hinj : Set.InjOn π R := by
    intro a ha b hb hab
    have hN' : a⁻¹ * b ∈ N := QuotientGroup.eq.mp hab
    have hR' : a⁻¹ * b ∈ R := R.mul_mem (R.inv_mem ha) hb
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := L)) ⟨_, hN'⟩
    obtain ⟨i, hi⟩ := hR3 ⟨_, hR'⟩
    have h1 : a⁻¹ * b = 1 := eq_one_of_pow_two_pow_of_pow_three_pow
      (by simpa using congrArg (fun w : N => (w : L)) hj)
      (by simpa using congrArg (fun w : R => (w : L)) hi)
    exact (inv_mul_eq_one.mp h1)
  have hRPb : R.map π = Pb := by
    set π₁ : P₁ →* Pb := (π.comp P₁.subtype).codRestrict Pb (fun y => y.2) with hπ₁
    have hπ₁s : Function.Surjective π₁ := by
      rintro ⟨y, hy⟩
      obtain ⟨l, rfl⟩ := hπs y
      exact ⟨⟨l, hy⟩, rfl⟩
    have htop : ((R₀.mapSurjective hπ₁s : Sylow 3 Pb) : Subgroup Pb) = ⊤ :=
      ((R₀.mapSurjective hπ₁s).3 (hPb3.to_subgroup ⊤) le_top).symm
    rw [Sylow.coe_mapSurjective] at htop
    have hcomp : π.comp P₁.subtype = Pb.subtype.comp π₁ := rfl
    rw [hR, Subgroup.map_map, hcomp, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have h2R : (⟨z', hz'R⟩ : R) ∈ Subgroup.upperCentralSeries R 2 :=
    (mem_upperCentralSeries_two_map_iff π hRPb hinj hz'R hxPb).mp h2
  have hZR : (⟨z', hz'R⟩ : R) ∉ Subgroup.center R := fun h =>
    hZ ((mem_center_map_iff π hRPb hinj hz'R hxPb).mpr h)
  have hinjL : Set.InjOn L.subtype R := L.subtype_injective.injOn
  have hzP : z ∈ R.map L.subtype := ⟨z', hz'R, rfl⟩
  exact ⟨R.map L.subtype, Subgroup.map_subtype_le _, hR3.map _, hzP,
    (mem_upperCentralSeries_two_map_iff L.subtype rfl hinjL hz'R hzP).mpr h2R,
    fun h => hZR ((mem_center_map_iff L.subtype rfl hinjL hz'R hzP).mp h)⟩

end Lift

end Step1917Steps

open Step1917Steps

@[expose] def Step1917Z2KM12 : Prop :=
  ThreeCentralZ2 CFSG.Blueprint.NativeSporadic.M12

@[expose] def Step1917Z2KLie9 : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    (p ^ e % 9 = 1 → ThreeCentralZ2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p e))) ∧
    (p ^ e % 9 = 8 → ThreeCentralZ2 (CFSG.Assembly.RankThreeEven.projSU 3 p e))

@[expose] def Step1917Z2KLie3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q T : Subgroup G) (z : G) (p e : ℕ) [Fact p.Prime],
    1 ≤ e → Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) p e → p ^ e % 9 ≠ 1 → p ^ e % 9 ≠ 8 →
    Group.IsPerfect L →
    IsPGroup 3 Q → Q ≤ Subgroup.normalizer (L : Set G) → (∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) →
    CFSG.Open.pRank 3 (Q ⊔ L) ≤ 3 →
    IsSylowOf 3 T (Q ⊔ L) → Q ≤ T → z ∈ L → z ∈ T → z ≠ 1 → (∀ t ∈ T, t * z = z * t) →
    ∃ P : Subgroup G, P ≤ Q ⊔ L ∧ IsPGroup 3 P ∧ ∃ hzP : z ∈ P,
      (⟨z, hzP⟩ : P) ∈ Subgroup.upperCentralSeries P 2 ∧ (⟨z, hzP⟩ : P) ∉ Subgroup.center P

theorem step1917Z2KFact_of (hM12 : Step1917Z2KM12) (hLie9 : Step1917Z2KLie9)
    (hLie3 : Step1917Z2KLie3) : Step1917Z2KFact := by
  intro G _ _ L Q T z hLp htype hQ3 hQN hQnab hrank hTY hQT hzL hzT hz1 hzc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYN : Q ⊔ L ≤ Subgroup.normalizer (L : Set G) := sup_le hQN Subgroup.le_normalizer
  have hTL : IsSylowOf 3 (T ⊓ L) L := hTY.inf_of_le_normalizer le_sup_right hYN
  have hlift : ThreeCentralZ2 (L ⧸ CFSG.pCore 2 L) → ∃ P : Subgroup G, P ≤ Q ⊔ L ∧
      IsPGroup 3 P ∧ ∃ hzP : z ∈ P, (⟨z, hzP⟩ : P) ∈ Subgroup.upperCentralSeries P 2 ∧
        (⟨z, hzP⟩ : P) ∉ Subgroup.center P := fun hX => by
    obtain ⟨P, hPL, hP3, hzP, h2, hZ⟩ := exists_of_threeCentralZ2 hTL hzT hzL hz1 hzc hX
    exact ⟨P, hPL.trans le_sup_right, hP3, hzP, h2, hZ⟩
  rcases htype with ⟨p, e, hp, he, hiso⟩ | ⟨⟨ψ⟩⟩
  · by_cases h9 : p ^ e % 9 = 1 ∨ p ^ e % 9 = 8
    · apply hlift
      rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
      · rcases h9 with h9 | h9
        · exact threeCentralZ2_of_mulEquiv φ ((hLie9 p e he).1 h9)
        · omega
      · rcases h9 with h9 | h9
        · omega
        · exact threeCentralZ2_of_mulEquiv φ ((hLie9 p e he).2 h9)
    · push Not at h9
      exact hLie3 G L Q T z p e he hiso h9.1 h9.2 hLp hQ3 hQN hQnab hrank hTY hQT hzL hzT hz1 hzc
  · exact hlift (threeCentralZ2_of_mulEquiv ψ hM12)

end CFSG.RankThree.PartTwo.Sec19
