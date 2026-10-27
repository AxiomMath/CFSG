module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Group.Pi.Units
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

open Matrix
open scoped Pointwise

variable {K : Type} [Field K]

@[expose] noncomputable def diagHom : (Fin 3 → Kˣ) →* GL (Fin 3) K :=
  (Units.map (Matrix.diagonalRingHom (Fin 3) K).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem coe_diagHom (d : Fin 3 → Kˣ) :
    ((diagHom d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal (fun i => (d i : K)) := by
  simp [diagHom, MulEquiv.piUnits]

theorem diagHom_injective : Function.Injective (diagHom (K := K)) := by
  intro d e h
  funext i
  apply Units.ext
  have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) i i) h
  simpa [coe_diagHom] using this


theorem card_GL_three_eq [Finite K] {a u : ℕ} (hu : Odd u) (ha : 2 ≤ a)
    (hQ : Nat.card K = 2 ^ a * u + 1) :
    ∃ c : ℕ, Odd c ∧ Nat.card (GL (Fin 3) K) = 2 ^ (3 * a + 1) * c := by
  have := Fintype.ofFinite K
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  rw [Matrix.card_GL_field, Fin.prod_univ_three, ← Nat.card_eq_fintype_card, hQ]
  set c₀ := 2 ^ (b + 2) * u with hc₀
  have hc₀e : Even c₀ := by
    rw [hc₀]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right u
  have e1 : (c₀ + 1) ^ 3 - (c₀ + 1) ^ ((0 : Fin 3) : ℕ) = c₀ * (c₀ ^ 2 + 3 * c₀ + 3) := by
    apply Nat.sub_eq_of_eq_add
    simp
    ring
  have e2 : (c₀ + 1) ^ 3 - (c₀ + 1) ^ ((1 : Fin 3) : ℕ) = (c₀ + 1) * c₀ * (c₀ + 2) := by
    apply Nat.sub_eq_of_eq_add
    simp
    ring
  have e3 : (c₀ + 1) ^ 3 - (c₀ + 1) ^ ((2 : Fin 3) : ℕ) = (c₀ + 1) ^ 2 * c₀ := by
    apply Nat.sub_eq_of_eq_add
    simp
    ring
  have hc2 : c₀ + 2 = 2 * (2 ^ (b + 1) * u + 1) := by
    rw [hc₀]
    ring
  refine ⟨u ^ 3 * (c₀ ^ 2 + 3 * c₀ + 3) * (c₀ + 1) ^ 3 * (2 ^ (b + 1) * u + 1), ?_, ?_⟩
  · have h1 : Odd (c₀ ^ 2 + 3 * c₀ + 3) := by
      have : Even (c₀ ^ 2 + 3 * c₀) := by
        have h2 : Even (c₀ ^ 2) := Nat.even_pow.mpr ⟨hc₀e, by norm_num⟩
        exact Even.add h2 (Even.mul_left hc₀e 3)
      exact Even.add_odd this (by decide)
    have h2 : Odd (c₀ + 1) := Even.add_one hc₀e
    have h3 : Odd (2 ^ (b + 1) * u + 1) :=
      Even.add_one (Even.mul_right (Nat.even_pow.mpr ⟨even_two, by omega⟩) u)
    exact Odd.mul (Odd.mul (Odd.mul (Odd.pow hu) h1) (Odd.pow h2)) h3
  · rw [e1, e2, e3, hc2, hc₀]
    ring


@[expose] noncomputable def diagRoots (m : ℕ) : (Fin 3 → rootsOfUnity m K) →* GL (Fin 3) K :=
  diagHom.comp ((rootsOfUnity m K).subtype.compLeft (Fin 3))

theorem diagRoots_injective (m : ℕ) : Function.Injective (diagRoots (K := K) m) := by
  intro d e h
  have h1 := diagHom_injective h
  funext i
  apply Subtype.ext
  exact congrFun h1 i

theorem diagRoots_comm (m : ℕ) (d e : Fin 3 → rootsOfUnity m K) :
    diagRoots m d * diagRoots m e = diagRoots m e * diagRoots m d := by
  rw [← map_mul, ← map_mul]
  congr 1
  funext i
  exact mul_comm _ _

theorem diagRoots_sq_eq_one {m : ℕ} {d : Fin 3 → rootsOfUnity m K} (h : diagRoots m d ^ 2 = 1) :
    ∀ i, ((d i : Kˣ)) ^ 2 = 1 := by
  rw [← map_pow] at h
  have := diagRoots_injective m (h.trans (map_one _).symm)
  intro i
  have h2 := congrFun this i
  have h3 := congrArg Subtype.val h2
  simpa [pow_two] using h3


theorem exists_abelian_index_two [Finite K] {a u : ℕ} (hu : Odd u) (ha : 2 ≤ a)
    (hQ : Nat.card K = 2 ^ a * u + 1) {G : Type*} [Group G] [Finite G]
    (ι : G →* GL (Fin 3) K) (hι : Function.Injective ι) (hG : IsPGroup 2 G) :
    ∃ C : Subgroup G, (∀ x ∈ C, ∀ y ∈ C, x * y = y * x) ∧ C.index ≤ 2 ∧
      Nat.card {x : G // x ∈ C ∧ x ^ 2 = 1} ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : 2 ^ a ∣ Nat.card K - 1 := by rw [hQ]; simp
  have hd2 : 2 ∣ Nat.card K - 1 := by
    rw [hQ]
    simp only [Nat.add_sub_cancel]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have hμ : Nat.card (rootsOfUnity (2 ^ a) K) = 2 ^ a :=
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd hd
  have hμ2 : Nat.card (rootsOfUnity 2 K) = 2 := CFSG.LinearGroups.card_rootsOfUnity_of_dvd hd2
  set D : Subgroup (GL (Fin 3) K) := (diagRoots (K := K) (2 ^ a)).range with hD
  have hDcard : Nat.card D = 2 ^ (3 * a) := by
    rw [hD, ← Nat.card_congr (MonoidHom.ofInjective (diagRoots_injective (2 ^ a))).toEquiv,
      Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hμ, ← pow_mul, mul_comm]
  have hDp : IsPGroup 2 D := IsPGroup.of_card hDcard
  obtain ⟨P, hDP⟩ := hDp.exists_le_sylow
  have hrange : IsPGroup 2 ι.range := hG.of_surjective ι.rangeRestrict
    (MonoidHom.rangeRestrict_surjective ι)
  obtain ⟨Q, hQr⟩ := hrange.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 3) K) Q P
  set ι' : G →* GL (Fin 3) K := (MulAut.conj g).toMonoidHom.comp ι with hι'
  have hι'inj : Function.Injective ι' := (MulAut.conj g).injective.comp hι
  have hι'P : ι'.range ≤ P := by
    rintro _ ⟨x, rfl⟩
    have h1 : ι x ∈ (Q : Subgroup (GL (Fin 3) K)) := hQr ⟨x, rfl⟩
    have h2 : (MulAut.conj g) (ι x) ∈
        ((g • Q : Sylow 2 (GL (Fin 3) K)) : Subgroup (GL (Fin 3) K)) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨ι x, h1, rfl⟩
    rw [hg] at h2
    exact h2
  refine ⟨D.comap ι', ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨dx, hdx⟩ := hx
    obtain ⟨dy, hdy⟩ := hy
    apply hι'inj
    rw [map_mul, map_mul, ← hdx, ← hdy]
    exact diagRoots_comm _ _ _
  ·
    obtain ⟨c, hcodd, hcard⟩ := card_GL_three_eq hu ha hQ
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp P.2
    have hPdvd : Nat.card P ∣ Nat.card (GL (Fin 3) K) := Subgroup.card_subgroup_dvd_card _
    rw [hj, hcard] at hPdvd
    have hcop : Nat.Coprime (2 ^ j) c :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hcodd)
    have hj' : j ≤ 3 * a + 1 :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hPdvd)
    have hcardD : Nat.card (D.subgroupOf (P : Subgroup (GL (Fin 3) K))) = 2 ^ (3 * a) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv, hDcard]
    have h1 := Subgroup.card_mul_index (D.subgroupOf (P : Subgroup (GL (Fin 3) K)))
    rw [hcardD, hj] at h1
    have h2 : (D.subgroupOf (P : Subgroup (GL (Fin 3) K))).index ≤ 2 := by
      have h3 : 2 ^ (3 * a) * (D.subgroupOf (P : Subgroup (GL (Fin 3) K))).index ≤
          2 ^ (3 * a) * 2 := by
        rw [h1, ← pow_succ]
        exact Nat.pow_le_pow_right (by norm_num) hj'
      exact Nat.le_of_mul_le_mul_left h3 (by positivity)
    rw [Subgroup.index_comap]
    calc D.relIndex ι'.range ≤ D.relIndex (P : Subgroup (GL (Fin 3) K)) :=
          Subgroup.relIndex_le_of_le_right hι'P Subgroup.index_ne_zero_of_finite
      _ ≤ 2 := h2
  ·
    have hμ2' : Nat.card (Fin 3 → rootsOfUnity 2 K) = 8 := by
      rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hμ2]
      norm_num
    have hR₂ : Nat.card (diagRoots (K := K) 2).range ≤ 8 := by
      rw [← hμ2']
      exact Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    have hmem : ∀ x : G, x ∈ D.comap ι' → x ^ 2 = 1 → ι' x ∈ (diagRoots (K := K) 2).range := by
      intro x hxC hx2
      obtain ⟨d, hd⟩ := hxC
      have h1 : diagRoots (2 ^ a) d ^ 2 = 1 := by
        rw [hd, ← map_pow, hx2, map_one]
      have h2 := diagRoots_sq_eq_one h1
      refine ⟨fun i => ⟨(d i : Kˣ), (mem_rootsOfUnity _ _).mpr (h2 i)⟩, ?_⟩
      rw [← hd]
      rfl
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : {x : G // x ∈ D.comap ι' ∧ x ^ 2 = 1} =>
        (⟨ι' x.1, hmem x.1 x.2.1 x.2.2⟩ : (diagRoots (K := K) 2).range)) ?_) hR₂
    intro x y hxy
    exact Subtype.ext (hι'inj (congrArg Subtype.val hxy))


theorem card_elem_quotient_le [Finite K] {a u : ℕ} (hu : Odd u) (ha : 2 ≤ a)
    (hQ : Nat.card K = 2 ^ a * u + 1) {G : Type*} [Group G] [Finite G]
    (ι : G →* GL (Fin 3) K) (hι : Function.Injective ι) (hG : IsPGroup 2 G)
    {E : Type*} [Group E] [Finite E] (hE : ∀ x : E, x ^ 2 = 1) (ψ : G →* E)
    (hψ : Function.Surjective ψ) : Nat.card E ≤ 16 := by
  obtain ⟨C, hCab, hCidx, hCinv⟩ := exists_abelian_index_two hu ha hQ ι hι hG
  let χ : ↥C →* E := ψ.comp C.subtype
  let sq : ↥C →* ↥C :=
    { toFun := fun x => x ^ 2
      map_one' := by simp
      map_mul' := fun x y => by
        have hc : Commute x y := Subtype.ext (hCab x x.2 y y.2)
        exact hc.mul_pow 2 }
  have hle : sq.range ≤ χ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    show ψ ((x : G) ^ 2) = 1
    rw [map_pow, hE]
  have hker : Nat.card sq.ker ≤ 8 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : sq.ker => (⟨(x : ↥C).1, (x : ↥C).2, ?_⟩ : {x : G // x ∈ C ∧ x ^ 2 = 1})) ?_) hCinv
    · have h := x.2
      rw [MonoidHom.mem_ker] at h
      exact congrArg (fun y : ↥C => (y : G)) h
    · intro x y hxy
      have h : (x : ↥C).1 = (y : ↥C).1 :=
        congrArg (fun z : {x : G // x ∈ C ∧ x ^ 2 = 1} => z.1) hxy
      exact Subtype.ext (Subtype.ext h)
  have h1 : Nat.card sq.ker * Nat.card sq.range = Nat.card C := by
    have := Subgroup.card_mul_index sq.ker
    rwa [Subgroup.index_ker] at this
  have h2 : sq.range.index * Nat.card sq.range = Nat.card C := by
    have := Subgroup.card_mul_index sq.range
    rwa [mul_comm] at this
  have h3 : sq.range.index = Nat.card sq.ker := by
    have hpos : 0 < Nat.card sq.range := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)
  have h4 : Nat.card χ.range ≤ 8 := by
    rw [← Subgroup.index_ker]
    exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hle)) (h3 ▸ hker)
  have h5 : χ.range.index ≤ 2 := by
    have : χ.range = C.map ψ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this]
    exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_map_dvd C hψ)) hCidx
  have h6 := Subgroup.card_mul_index χ.range
  calc Nat.card E = Nat.card χ.range * χ.range.index := h6.symm
    _ ≤ 8 * 2 := Nat.mul_le_mul h4 h5
    _ = 16 := by norm_num


theorem glMap_injective {K K' : Type} [Field K] [Field K'] (f : K →+* K') :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin 3) f) := by
  intro g h hgh
  apply Units.ext
  ext i j
  have := congrArg (fun x : GL (Fin 3) K' => (x : Matrix (Fin 3) (Fin 3) K') i j) hgh
  exact f.injective (by simpa [Matrix.GeneralLinearGroup.map] using this)


theorem card_elem_quotient_le_of_odd [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp : p ≠ 2)
    {G : Type*} [Group G] [Finite G] (ι : G →* GL (Fin 3) K) (hι : Function.Injective ι)
    (hG : IsPGroup 2 G) {E : Type*} [Group E] [Finite E] (hE : ∀ x : E, x ^ 2 = 1) (ψ : G →* E)
    (hψ : Function.Surjective ψ) : Nat.card E ≤ 16 := by
  have := Fintype.ofFinite K
  obtain ⟨m, hm⟩ := (FiniteField.card K p)
  have hQodd : Nat.card K % 2 = 1 := by
    rw [Nat.card_eq_fintype_card, hm.2]
    exact Nat.odd_iff.mp (Odd.pow ((Nat.Prime.odd_of_ne_two Fact.out hp)))
  set K' := FiniteField.Extension K p 2 with hK'
  have hcard : Nat.card K' = Nat.card K ^ 2 := FiniteField.natCard_extension K p 2
  obtain ⟨t, ht⟩ : ∃ t, Nat.card K = 2 * t + 1 := ⟨Nat.card K / 2, by omega⟩
  have h4 : 4 ∣ Nat.card K' - 1 := by
    rw [hcard, ht]
    have : (2 * t + 1) ^ 2 - 1 = 4 * (t * (t + 1)) := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [this]
    exact dvd_mul_right _ _
  have hne : Nat.card K' - 1 ≠ 0 := by
    have : 1 < Nat.card K' := Finite.one_lt_card
    omega
  obtain ⟨a, u, hu, hau⟩ := Nat.exists_eq_two_pow_mul_odd hne
  have ha : 2 ≤ a := by
    by_contra hlt
    have ha1 : a ≤ 1 := by omega
    have h2 : 2 ^ a ∣ 2 := by
      calc 2 ^ a ∣ 2 ^ 1 := Nat.pow_dvd_pow 2 ha1
        _ = 2 := by norm_num
    have h5 : 4 ∣ 2 ^ a * u := hau ▸ h4
    have h6 : 2 ^ a * u % 4 = 2 ^ a * u % 4 := rfl
    rcases Nat.lt_or_ge a 1 with h | h
    · have : a = 0 := by omega
      subst this
      simp at h5
      have hodd : u % 2 = 1 := Nat.odd_iff.mp hu
      omega
    · have : a = 1 := by omega
      subst this
      have hodd : u % 2 = 1 := Nat.odd_iff.mp hu
      simp at h5
      omega
  have hQ : Nat.card K' = 2 ^ a * u + 1 := by
    have : 1 < Nat.card K' := Finite.one_lt_card
    omega
  exact card_elem_quotient_le hu ha hQ
    ((Matrix.GeneralLinearGroup.map (n := Fin 3) (algebraMap K K')).comp ι)
    ((glMap_injective _).comp hι) hG hE ψ hψ


end CFSG.RankThree.PartTwo.Sec15.KS1424
