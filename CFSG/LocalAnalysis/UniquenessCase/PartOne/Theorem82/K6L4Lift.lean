module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Defs
public import CFSG.LieType.SeitzGeneration.ExcHigh.Generic
public import CFSG.RankThree.PartOne.KF.CentralQuot
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Open

namespace TwoQuot

variable {H Y : Type} [Group H] [Group Y] [Finite H] [Finite Y] {π : H →* Y}

theorem not_dvd_card_ker (hπ : TwoQuot π) {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    ¬ p ∣ Nat.card π.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hπ.two
  intro hd
  rw [hk] at hd
  exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))

private theorem not_dvd_card_inf_ker (hπ : TwoQuot π) (C : Subgroup H) {p : ℕ} (hp : p.Prime)
    (h2 : p ≠ 2) : ¬ p ∣ Nat.card ↥(C ⊓ π.ker) :=
  fun hd => not_dvd_card_ker hπ hp h2 (hd.trans (Subgroup.card_dvd_of_le inf_le_right))

private theorem isCentralPQuot_three (hπ : TwoQuot π) :
    CFSG.RankThree.PartOne.KFU.IsCentralPQuot 3 π :=
  ⟨hπ.surj, hπ.central,
    (Nat.prime_three.coprime_iff_not_dvd).mpr (not_dvd_card_ker hπ Nat.prime_three (by norm_num))⟩

private theorem card_eq_card_map_mul_card_inf_ker (C : Subgroup H) :
    Nat.card C = Nat.card (C.map π) * Nat.card ↥(C ⊓ π.ker) := by
  set g : C →* Y := π.comp C.subtype with hg
  have hrange : g.range = C.map π := by rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : g.ker = (C ⊓ π.ker).subgroupOf C := by
    ext x
    simp [hg, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have h := Subgroup.card_ker_mul_card_range g
  rw [hker, hrange] at h
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, mul_comm] at h
  exact h.symm

theorem comp_conj (hπ : TwoQuot π) (g : H) :
    TwoQuot (π.comp (MulAut.conj g).toMonoidHom) ∧
      (π.comp (MulAut.conj g).toMonoidHom).ker = π.ker := by
  have hker : (π.comp (MulAut.conj g).toMonoidHom).ker = π.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro hx
      have hmem := (MonoidHom.normal_ker π).conj_mem ((MulAut.conj g) x) hx g⁻¹
      have h := MonoidHom.mem_ker.mp hmem
      rw [MulAut.conj_apply] at h
      simp only [map_mul, map_inv, inv_inv] at h
      rwa [show (π g)⁻¹ * (π g * π x * (π g)⁻¹) * π g = π x by group] at h
    · intro hx
      exact (MonoidHom.normal_ker π).conj_mem x hx g
  refine ⟨⟨hπ.surj.comp (MulAut.conj g).surjective, ?_, ?_⟩, hker⟩
  · rw [hker]; exact hπ.central
  · rw [hker]; exact hπ.two

theorem exists_lift_E27 (hπ : TwoQuot π) {A : Subgroup Y} (hA : IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) :
    ∃ Ã : Subgroup H, IsElemAbelian 3 Ã ∧ Nat.card Ã = 27 ∧ Ã.map π = A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Ã, hmap, hdis, hE⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.exists_lift_elemAbelian_of_coprime_ker π hπ.surj
      (not_dvd_card_ker hπ Nat.prime_three (by norm_num)) hA
  have hcard : Nat.card Ã = Nat.card A := by
    rw [← hmap]
    exact (CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker π hdis).symm
  exact ⟨Ã, hE, by rw [hcard, h27], hmap⟩

theorem centralizer_map (hπ : TwoQuot π) {S : Subgroup H} (hS : ∀ s ∈ S, s ^ 3 = 1) :
    Subgroup.centralizer ((S.map π : Subgroup Y) : Set Y) =
      (Subgroup.centralizer (S : Set H)).map π := by
  have hq := isCentralPQuot_three hπ
  apply le_antisymm
  · intro y hy
    obtain ⟨h, rfl⟩ := hπ.surj y
    change π h ∈ Subgroup.centralizer ((S.map π : Subgroup Y) : Set Y) at hy
    rw [Subgroup.mem_centralizer_iff] at hy
    rw [Subgroup.mem_map]
    refine ⟨h, ?_, rfl⟩
    change h ∈ Subgroup.centralizer (S : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact hq.commute_of_map_commute (hS s hs) (hy (π s) (Subgroup.mem_map_of_mem π hs))
  · rintro y ⟨h, hh, rfl⟩
    change h ∈ Subgroup.centralizer (S : Set H) at hh
    rw [Subgroup.mem_centralizer_iff] at hh
    change π h ∈ Subgroup.centralizer ((S.map π : Subgroup Y) : Set Y)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
    rw [← map_mul, ← map_mul]
    exact congrArg π (hh s₀ hs₀)

theorem centralizer_map_singleton (hπ : TwoQuot π) {d : H} (hd : d ^ 3 = 1) :
    Subgroup.centralizer ({π d} : Set Y) = (Subgroup.centralizer ({d} : Set H)).map π := by
  have h3 : ∀ s ∈ Subgroup.zpowers d, s ^ 3 = 1 := by
    intro s hs
    have h1 : orderOf s ∣ orderOf d := orderOf_dvd_of_mem_zpowers hs
    have h2 : orderOf d ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hd
    exact orderOf_dvd_iff_pow_eq_one.mp (h1.trans h2)
  have h := centralizer_map hπ (S := Subgroup.zpowers d) h3
  rw [MonoidHom.map_zpowers] at h
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h

theorem normalizer_lift (hπ : TwoQuot π) {S : Subgroup H} (hS : ∀ s ∈ S, s ^ 3 = 1) {n : Y}
    (hn : n ∈ Subgroup.normalizer ((S.map π : Subgroup Y) : Set Y)) :
    ∃ h : H, π h = n ∧ h ∈ Subgroup.normalizer (S : Set H) := by
  have hq := isCentralPQuot_three hπ
  obtain ⟨h, hh⟩ := hπ.surj n
  refine ⟨h, hh, ?_⟩
  have hconj : ∀ s ∈ S, h * s * h⁻¹ ∈ S := by
    intro s hs
    have hπs : π (h * s * h⁻¹) ∈ S.map π := by
      have h1 : n * π s * n⁻¹ ∈ S.map π :=
        (Subgroup.mem_normalizer_iff.mp hn (π s)).mp (Subgroup.mem_map_of_mem π hs)
      simpa [hh, map_mul, map_inv] using h1
    obtain ⟨s', hs', hs'eq⟩ := Subgroup.mem_map.mp hπs
    set z : H := (h * s * h⁻¹) * s'⁻¹ with hz
    have hzker : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hs'eq, mul_inv_cancel]
    have hz3 : z ^ 3 = 1 := by
      have hzc : Commute z s' := (Subgroup.mem_center_iff.mp (hπ.central hzker) s').symm
      have h1 : (h * s * h⁻¹) ^ 3 = z ^ 3 * s' ^ 3 := by
        have hzs : h * s * h⁻¹ = z * s' := by rw [hz]; group
        rw [hzs, hzc.mul_pow]
      have h2 : (h * s * h⁻¹) ^ 3 = 1 := by
        have hconj : h * s * h⁻¹ = (MulAut.conj h) s := by rw [MulAut.conj_apply]
        rw [hconj, ← map_pow (MulAut.conj h) s 3, hS s hs, map_one]
      rw [h2, hS s' hs', mul_one] at h1
      exact h1.symm
    have hz1 : z = 1 := hq.eq_one_of_pow_eq_one hzker hz3
    have hs'eq2 : h * s * h⁻¹ = s' := by
      have : (h * s * h⁻¹) * s'⁻¹ = 1 := by rw [← hz]; exact hz1
      exact mul_inv_eq_one.mp this
    rw [hs'eq2]
    exact hs'
  have hle : S.map (MulAut.conj h).toMonoidHom ≤ S := by
    rintro _ ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply] using hconj s hs
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]

theorem factorization_card_map (hπ : TwoQuot π) (C : Subgroup H) {p : ℕ} (hp : p.Prime)
    (h2 : p ≠ 2) :
    (Nat.card (C.map π)).factorization p = (Nat.card C).factorization p := by
  have hzero : (Nat.card ↥(C ⊓ π.ker)).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_card_inf_ker hπ C hp h2)
  have h1 : Nat.card (C.map π) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  have h2' : Nat.card ↥(C ⊓ π.ker) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  rw [card_eq_card_map_mul_card_inf_ker (π := π) C, Nat.factorization_mul h1 h2']
  simp only [Finsupp.add_apply, hzero, add_zero]

theorem pRank_map (hπ : TwoQuot π) (C : Subgroup H) {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    pRank p (C.map π) = pRank p C := by
  haveI : Fact p.Prime := ⟨hp⟩
  set g : C →* Y := π.comp C.subtype with hg
  have hrange : g.range = C.map π := by rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : g.ker = (C ⊓ π.ker).subgroupOf C := by
    ext x
    simp [hg, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hN : ¬ p ∣ Nat.card g.ker := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact not_dvd_card_inf_ker hπ C hp h2
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (C.map π),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup C, ← hrange,
    ← CFSG.SectionRank.pRank_quotient_eq (G := C) (p := p) g.ker hN]
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
    (QuotientGroup.quotientKerEquivRange g)).symm

end TwoQuot

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
