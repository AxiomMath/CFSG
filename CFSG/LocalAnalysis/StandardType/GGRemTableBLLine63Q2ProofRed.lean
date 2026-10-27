module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofLift
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCover
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Two
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Cover
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.StandardType

section TwoCenter

variable {G : Type} [Group G] [Finite G] (L : Subgroup G)

@[expose] def twoCenter : Subgroup G where
  carrier := {z | z ∈ L ∧ (∀ l ∈ L, z * l = l * z) ∧ z ^ (2 ^ Nat.card G) = 1}
  one_mem' := ⟨L.one_mem, fun l _ => by rw [one_mul, mul_one], one_pow _⟩
  mul_mem' := by
    rintro x y ⟨hxL, hxc, hx⟩ ⟨hyL, hyc, hy⟩
    refine ⟨L.mul_mem hxL hyL, fun l hl => ?_, ?_⟩
    · rw [mul_assoc, hyc l hl, ← mul_assoc, hxc l hl, mul_assoc]
    · rw [(show Commute x y from (hyc x hxL).symm).mul_pow, hx, hy, one_mul]
  inv_mem' := by
    rintro x ⟨hxL, hxc, hx⟩
    refine ⟨L.inv_mem hxL, fun l hl => ?_, by rw [inv_pow, hx, inv_one]⟩
    have h := hxc l hl
    calc x⁻¹ * l = x⁻¹ * (l * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * l) * x⁻¹ := by rw [h]
      _ = l * x⁻¹ := by group

theorem isPGroup_twoCenter : IsPGroup 2 (twoCenter L) :=
  fun z => ⟨Nat.card G, Subtype.ext z.2.2.2⟩

instance twoCenter_normal :
    ((twoCenter L).subgroupOf (Subgroup.normalizer (L : Set G))).Normal where
  conj_mem := by
    rintro z hz ⟨n, hn⟩
    obtain ⟨hzL, hzc, hz2⟩ := Subgroup.mem_subgroupOf.mp hz
    rw [Subgroup.mem_subgroupOf]
    have hnL : ∀ l, l ∈ L ↔ n * l * n⁻¹ ∈ L := Subgroup.mem_normalizer_iff.mp hn
    have hnL' : ∀ l, l ∈ L ↔ n⁻¹ * l * n⁻¹⁻¹ ∈ L :=
      Subgroup.mem_normalizer_iff.mp (inv_mem hn)
    refine ⟨(hnL _).mp hzL, fun l hl => ?_, ?_⟩
    · have hl' : n⁻¹ * l * n ∈ L := by
        have := (hnL' l).mp hl
        rwa [inv_inv] at this
      have h := hzc _ hl'
      calc n * (z : G) * n⁻¹ * l = n * ((z : G) * (n⁻¹ * l * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * l * n) * (z : G)) * n⁻¹ := by rw [h]
        _ = l * (n * (z : G) * n⁻¹) := by group
    · show (n * (z : G) * n⁻¹) ^ (2 ^ Nat.card G) = 1
      rw [conj_pow, hz2]
      group

abbrev RedGrp : Type :=
  ↥(Subgroup.normalizer (L : Set G)) ⧸
    (twoCenter L).subgroupOf (Subgroup.normalizer (L : Set G))

@[expose] def redMk : ↥(Subgroup.normalizer (L : Set G)) →* RedGrp L := QuotientGroup.mk' _

theorem redMk_eq_one_iff (n : ↥(Subgroup.normalizer (L : Set G))) :
    redMk L n = 1 ↔ (n : G) ∈ twoCenter L :=
  (QuotientGroup.eq_one_iff n).trans Subgroup.mem_subgroupOf

theorem isPGroup_ker_redMk : IsPGroup 2 (redMk L).ker := fun y =>
  ⟨Nat.card G, Subtype.ext (Subtype.ext
    (by simpa using ((redMk_eq_one_iff L y.1).mp y.2).2.2))⟩

@[expose] def redMkL : ↥L →* RedGrp L :=
  (redMk L).comp (Subgroup.inclusion Subgroup.le_normalizer)

theorem redMkL_eq_one_iff (l : ↥L) : redMkL L l = 1 ↔ (l : G) ∈ twoCenter L :=
  redMk_eq_one_iff L _

instance redL_normal : (redMkL L).range.Normal where
  conj_mem := by
    rintro _ ⟨l, rfl⟩ q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨n * (l : G) * n⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 l).mp l.2⟩, ?_⟩
    show redMk L ⟨n * (l : G) * n⁻¹, _⟩ = (n : RedGrp L) * redMk L ⟨(l : G), _⟩ * (n : RedGrp L)⁻¹
    rfl

end TwoCenter

section Cover

open CFSG.StandardType.LineU
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_redCover (hcov : Line63.UnitaryCoverOddAt 1 6 K) (hL : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K 6)) :
    ∃ φ : ↥(unitarySU 2 1 K 6) →* RedGrp L,
      (∀ s, φ s ∈ (redMkL L).range) ∧ (∀ l : ↥L, ∃ s, φ s = redMkL L l) ∧
      ∀ (s : ↥(unitarySU 2 1 K 6)) (l : ↥L), φ s = redMkL L l →
        ggQuotHom θ l = LargeEvenProjMk (unitarySU 2 1 K 6) s := by
  classical
  set ψ : ↥L →* LargeEvenProj (unitarySU 2 1 K 6) := ggQuotHom θ with hψ
  set σ : ↥L →* ↥(redMkL L).range := (redMkL L).rangeRestrict with hσ
  have hσs : Function.Surjective σ := (redMkL L).rangeRestrict_surjective
  have hkerψ : ψ.ker = Subgroup.center ↥L := ker_ggQuotHom θ
  have hσ1 : ∀ l : ↥L, σ l = 1 ↔ redMkL L l = 1 := fun l =>
    ⟨fun h => by simpa [hσ] using congrArg Subtype.val h,
      fun h => Subtype.ext (by simpa [hσ] using h)⟩
  have hkσψ : σ.ker ≤ ψ.ker := by
    intro l hl
    have h2 := (redMkL_eq_one_iff L l).mp ((hσ1 l).mp (MonoidHom.mem_ker.mp hl))
    rw [hkerψ, Subgroup.mem_center_iff]
    intro l'
    exact Subtype.ext (h2.2.1 l' l'.2).symm
  let ψ₁ : ↥(redMkL L).range →* LargeEvenProj (unitarySU 2 1 K 6) :=
    (MonoidHom.liftOfSurjective σ hσs) ⟨ψ, hkσψ⟩
  have hψ₁ : ∀ l, ψ₁ (σ l) = ψ l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply σ _ (Function.rightInverse_surjInv hσs) ⟨ψ, hkσψ⟩ l
  have hψ₁s : Function.Surjective ψ₁ := by
    intro r
    obtain ⟨l, hl⟩ := ggQuotHom_surjective θ r
    exact ⟨σ l, by rw [hψ₁]; exact hl⟩
  have hψ₁ker : ψ₁.ker ≤ Subgroup.center ↥(redMkL L).range := by
    intro y hy
    obtain ⟨l, rfl⟩ := hσs y
    have hl : l ∈ ψ.ker := by rw [MonoidHom.mem_ker, ← hψ₁]; exact hy
    rw [hkerψ] at hl
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l', rfl⟩ := hσs g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hl l']
  have hperf₁ : commutator ↥(redMkL L).range = ⊤ := by
    have : (commutator ↥L).map σ = commutator ↥(redMkL L).range := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hσs]
    rw [← this, hL, Subgroup.map_top_of_surjective _ hσs]
  have hodd : Odd (Nat.card ψ₁.ker) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hne)
    obtain ⟨l, hl⟩ := hσs y.1
    have hy2 : (y : ↥(redMkL L).range) ^ 2 = 1 := by
      have := congrArg Subtype.val (pow_orderOf_eq_one y)
      rw [hy] at this
      simpa using this
    have hl' : l ∈ ψ.ker := by rw [MonoidHom.mem_ker, ← hψ₁, hl]; exact y.2
    rw [hkerψ] at hl'
    have hlc : ∀ l'' ∈ L, (l : G) * l'' = l'' * (l : G) := fun l'' hl'' =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hl' ⟨l'', hl''⟩)).symm
    have hl2 : redMkL L (l ^ 2) = 1 := by
      rw [← hσ1, map_pow, hl, hy2]
    have hl2' := ((redMkL_eq_one_iff L (l ^ 2)).mp hl2).2.2
    have hl2'' : (l : G) ^ (2 ^ (Nat.card G + 1)) = 1 := by
      rw [pow_succ', pow_mul]
      simpa using hl2'
    have hlpow : (l : G) ^ (2 ^ Nat.card G) = 1 := pow_two_pow_card (l : G) hl2''
    have hl1 : σ l = 1 := (hσ1 l).mpr ((redMkL_eq_one_iff L l).mpr ⟨l.2, hlc, hlpow⟩)
    have hy1 : y = 1 := Subtype.ext (by rw [← hl, hl1]; rfl)
    rw [hy1, orderOf_one] at hy
    norm_num at hy
  obtain ⟨φ₀, hφ₀⟩ := hcov.2 ↥(redMkL L).range ψ₁ hψ₁s hψ₁ker hperf₁ hodd
  have hφs : Function.Surjective φ₀ := by
    have hcomm : ⁅(⊤ : Subgroup ↥(redMkL L).range), (⊤ : Subgroup ↥(redMkL L).range)⁆ ≤
        φ₀.range := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨s, hs⟩ : ∃ s : ↥(unitarySU 2 1 K 6),
          ψ₁ x = LargeEvenProjMk (unitarySU 2 1 K 6) s := by
        obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ₁ x)
        exact ⟨s0, hs0.symm⟩
      obtain ⟨s', hs'⟩ : ∃ s : ↥(unitarySU 2 1 K 6),
          ψ₁ y = LargeEvenProjMk (unitarySU 2 1 K 6) s := by
        obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ₁ y)
        exact ⟨s0, hs0.symm⟩
      have hz : x * (φ₀ s)⁻¹ ∈ Subgroup.center ↥(redMkL L).range := by
        apply hψ₁ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφ₀, ← hs, mul_inv_cancel]
      have hz' : y * (φ₀ s')⁻¹ ∈ Subgroup.center ↥(redMkL L).range := by
        apply hψ₁ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφ₀, ← hs', mul_inv_cancel]
      have hx : x = (x * (φ₀ s)⁻¹) * φ₀ s := by group
      have hy : y = (y * (φ₀ s')⁻¹) * φ₀ s' := by group
      rw [hx, hy, comm_mul_central hz hz']
      exact ⟨⁅s, s'⁆, by rw [map_commutatorElement]⟩
    rw [show (⁅(⊤ : Subgroup ↥(redMkL L).range), (⊤ : Subgroup ↥(redMkL L).range)⁆ :
      Subgroup ↥(redMkL L).range) = ⊤ from hperf₁] at hcomm
    intro l
    obtain ⟨s, hs⟩ := hcomm (Subgroup.mem_top l)
    exact ⟨s, hs⟩
  refine ⟨(redMkL L).range.subtype.comp φ₀, fun s => (φ₀ s).2, fun l => ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hφs (σ l)
    exact ⟨s, congrArg Subtype.val hs⟩
  · intro s l h
    have h1 : φ₀ s = σ l := Subtype.ext h
    rw [← hφ₀ s, h1, hψ₁]

end Cover

end CFSG.StandardType.Line63.H5

end
