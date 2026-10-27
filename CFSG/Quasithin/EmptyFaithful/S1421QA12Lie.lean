module

public import CFSG.Quasithin.EmptyFaithful.S1421QA12Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bD
public import CFSG.Quasithin.EmptyFaithful.S1421QEx
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace QA12

theorem le_perfectCore_of_isTwoParabolicsOver_psl_psp {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 2 ≤ n) (hX : IsPSL 3 2 n X ∨ IsPSp4 2 n X) {U P P' : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hPar : IsTwoParabolicsOver U P P') :
    U ≤ perfectCore P ∧ U ≤ perfectCore P' := by
  obtain ⟨F, hF, hFin, P₀, -, hres, -, hperf, -⟩ :=
    F146Field.Case2b.parabolics_of_type hn hX hU
  obtain ⟨-, -, hmax, -, -, -⟩ := hres
  have hP1 : P ⋖ (⊤ : Subgroup X) := (hPar.2.2.2.2 P hPar.2.1).mpr (Or.inl rfl)
  have hP2 : P' ⋖ (⊤ : Subgroup X) := (hPar.2.2.2.2 P' hPar.2.2.1).mpr (Or.inr rfl)
  obtain ⟨j, hj⟩ := (hmax P hPar.2.1).mp hP1
  obtain ⟨j', hj'⟩ := (hmax P' hPar.2.2.1).mp hP2
  exact ⟨hj ▸ hperf j, hj' ▸ hperf j'⟩

theorem center_facts_of_isSL3 {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n) (hX : IsSL3 (2 ^ n) X) :
    (∀ z ∈ Subgroup.center X, z ^ 3 = 1) ∧ IsPSL 3 2 n (X ⧸ Subgroup.center X) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have hcenter : (Subgroup.center X).map (e : X →* ↥(StatedSL 3 F)) =
      (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F) := by
    rw [Subgroup.map_center_eq e]
    have h1 := Subgroup.map_center_eq (specialLinearGroupEquivStatedSL 3 F)
    rw [map_center_eq_statedScalars] at h1
    exact h1.symm
  refine ⟨fun z hz => ?_, ⟨Nat.prime_two, by omega, by norm_num, by simp, by simp⟩, F, hF, hFin,
    hcard, ⟨QuotientGroup.congr _ _ e hcenter⟩⟩
  have hzs : e z ∈ (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F) := by
    rw [← hcenter]
    exact Subgroup.mem_map_of_mem _ hz
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hzs)
  have hc3 : (c : F) ^ 3 = 1 := QEx.cube_eq_one_of_scalar_mem hc
  have hc3' : c ^ 3 = 1 := Units.ext (by simpa using hc3)
  apply e.injective
  apply Subtype.ext
  rw [map_pow, map_one]
  show ((e z : GL (Fin 3) F)) ^ 3 = 1
  rw [← hc, ← map_pow, hc3', map_one]

theorem le_of_map_le_of_center {X : Type} [Group X] {Z D U : Subgroup X} [Z.Normal]
    (hZ : Z ≤ Subgroup.center X) (hZodd : ∀ z ∈ Z, Odd (orderOf z)) (hU : IsPGroup 2 U)
    (h : U.map (QuotientGroup.mk' Z) ≤ D.map (QuotientGroup.mk' Z)) : U ≤ D := by
  intro u hu
  obtain ⟨d, hd, hdu⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_map_of_mem _ hu))
  have hz : d⁻¹ * u ∈ Z := QuotientGroup.eq.mp hdu
  set z := d⁻¹ * u with hzdef
  have hu' : u = d * z := by rw [hzdef]; group
  obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
  have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcomm : Commute d z := Subgroup.mem_center_iff.mp (hZ hz) d
  have h1 : (d ^ 2 ^ k) * (z ^ 2 ^ k) = 1 := by
    rw [← hcomm.mul_pow, ← hu']
    exact hk'
  have h2 : z ^ 2 ^ k ∈ D := by
    have : z ^ 2 ^ k = (d ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact D.inv_mem (D.pow_mem hd _)
  have hcop : Nat.Coprime (2 ^ k) (orderOf z) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (hZodd z hz))
  have h3 : z ∈ D := (Subgroup.zpowers_le.mpr h2) (A4.mem_zpowers_pow_of_coprime hcop)
  rw [hu']
  exact D.mul_mem hd h3

theorem le_perfectCore_of_isTwoParabolicsOver_sl3 {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 2 ≤ n) (hX : IsSL3 (2 ^ n) X) {U P P' : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (hPar : IsTwoParabolicsOver U P P') : U ≤ perfectCore P ∧ U ≤ perfectCore P' := by
  obtain ⟨hZ3, hpsl⟩ := center_facts_of_isSL3 hn hX
  have hZodd : ∀ z ∈ Subgroup.center X, Odd (orderOf z) := fun z hz =>
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one (hZ3 z hz))
  have hZN : Subgroup.center X ≤ Subgroup.normalizer (U : Set X) := fun z hz => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc := Subgroup.mem_center_iff.mp hz
    rw [show z * h * z⁻¹ = h by rw [← hc h]; group]
  have hZP : Subgroup.center X ≤ P := fun z hz => (hPar.2.2.2.1 (hZN hz)).1
  have hZP' : Subgroup.center X ≤ P' := fun z hz => (hPar.2.2.2.1 (hZN hz)).2
  have hsurj : Function.Surjective (QuotientGroup.mk' (Subgroup.center X)) :=
    QuotientGroup.mk'_surjective _
  have hUb : IsSylowTwoOf (U.map (QuotientGroup.mk' (Subgroup.center X))) ⊤ := by
    rw [K1.isSylowTwoOf_top_iff] at hU ⊢
    exact ⟨hU.1.map _, fun h2 => hU.2 (h2.trans (Subgroup.index_map_dvd _ hsurj))⟩
  have key : ∀ {Q : Subgroup X}, U ≤ Q → Q ⋖ (⊤ : Subgroup X) → Subgroup.center X ≤ Q →
      U ≤ perfectCore Q := by
    intro Q hUQ hQ hZQ
    have hker : (QuotientGroup.mk' (Subgroup.center X)).ker ≤ Q := by
      rw [QuotientGroup.ker_mk']
      exact hZQ
    have hQb := CFSG.QuasithinUnique.Setup.X7a.covBy_map_of_ker_le hsurj hker hQ
    rw [Subgroup.map_top_of_surjective _ hsurj] at hQb
    obtain ⟨F, hF, hFin, P₀, -, hres, -, hperf, -⟩ :=
      F146Field.Case2b.parabolics_of_type hn (Or.inl hpsl) hUb
    obtain ⟨-, -, hmax, -, -, -⟩ := hres
    obtain ⟨j, hj⟩ := (hmax _ (Subgroup.map_mono hUQ)).mp hQb
    have h1 := hperf j
    rw [← hj, ← map_perfectCore] at h1
    exact le_of_map_le_of_center (le_refl _) hZodd (hU.2.1) h1
  exact ⟨key hPar.2.1 ((hPar.2.2.2.2 P hPar.2.1).mpr (Or.inl rfl)) hZP,
    key hPar.2.2.1 ((hPar.2.2.2.2 P' hPar.2.2.1).mpr (Or.inr rfl)) hZP'⟩

theorem lieSylowLePerfectCore : LieSylowLePerfectCore := by
  intro X _ _ n hn hX U P P' hU hPar
  rcases hX with h | h | h
  · exact le_perfectCore_of_isTwoParabolicsOver_psl_psp hn (Or.inl h) hU hPar
  · exact le_perfectCore_of_isTwoParabolicsOver_sl3 hn h hU hPar
  · exact le_perfectCore_of_isTwoParabolicsOver_psl_psp hn (Or.inr h) hU hPar

end QA12

end CFSG.Quasithin
