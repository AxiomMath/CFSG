module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic
import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
import CFSG.RankThree.PartOne.S12.ModelTransport

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.Assembly.LowTwoRank Matrix
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

section Perfect

variable {M : Type*} [Group M]

theorem conj_commutator_eq {g x y : M} (hx : g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center M)
    (hy : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.center M) :
    g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  set a := g * x * g⁻¹ * x⁻¹ with ha
  set b := g * y * g⁻¹ * y⁻¹ with hb
  have ha' : ∀ z : M, z * a = a * z := fun z => Subgroup.mem_center_iff.mp hx z
  have hb' : ∀ z : M, z * b = b * z := fun z => Subgroup.mem_center_iff.mp hy z
  have hgx : g * x * g⁻¹ = a * x := by rw [ha]; group
  have hgy : g * y * g⁻¹ = b * y := by rw [hb]; group
  calc g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
    _ = (a * x) * (b * y) * (a * x)⁻¹ * (b * y)⁻¹ := by rw [hgx, hgy]
    _ = a * (x * (b * y) * x⁻¹) * a⁻¹ * (b * y)⁻¹ := by group
    _ = x * (b * y) * x⁻¹ * (b * y)⁻¹ := by
        rw [← ha' (x * (b * y) * x⁻¹)]
        group
    _ = (x * b) * y * x⁻¹ * y⁻¹ * b⁻¹ := by group
    _ = b * (x * y * x⁻¹ * y⁻¹) * b⁻¹ := by rw [hb' x]; group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [← hb' (x * y * x⁻¹ * y⁻¹)]; group

theorem le_centralizer_of_isPerfect {S : Subgroup M} [Group.IsPerfect S] {g : M}
    (h : ∀ x ∈ S, g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center M) :
    S ≤ Subgroup.centralizer ({g} : Set M) := by
  have hS : ⁅S, S⁆ = S := Subgroup.commutator_eq_self
  rw [← hS, Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
  have := conj_commutator_eq (h x hx) (h y hy)
  symm
  calc g * (x * y * x⁻¹ * y⁻¹) = g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ * g := by group
    _ = x * y * x⁻¹ * y⁻¹ * g := by rw [this]

end Perfect

section SL

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem isQuasisimple_slPi (hK : PiField π p f K) (hq2 : 2 < p ^ f) :
    IsQuasisimple (slPi π 3 (p ^ f) K) := by
  cases π
  · have := hK.finite
    have : Fact p.Prime := ⟨hK.prime⟩
    have hcard : Nat.card K = (p ^ f) ^ 2 := hK.card
    have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := by
      intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
    exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU
      (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcard le_rfl hnq)
      (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hcard 3 le_rfl
        hnq)).1
  · exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
      (Sec4.slPiTrueEquiv (p ^ f) K).symm
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl)

theorem isPerfect_slPi (hK : PiField π p f K) (hq2 : 2 < p ^ f) :
    Group.IsPerfect (slPi π 3 (p ^ f) K) :=
  (isQuasisimple_slPi hK hq2).1

theorem mem_statedScalars_of_mem_center (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {z : slPi π 3 (p ^ f) K} (hz : z ∈ Subgroup.center (slPi π 3 (p ^ f) K)) :
    (z : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  refine Sec4.mem_statedScalars_of_commute hπ hq' hτ hτ1 fun x hx => ?_
  have := Subgroup.mem_center_iff.mp hz ⟨x, hx⟩
  exact (congrArg Subtype.val this).symm

theorem mem_statedScalars_of_commute_mk (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) {g : GL (Fin 3) K}
    (h : ∀ s ∈ slPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk s = ProjGenLinGroup.mk s * ProjGenLinGroup.mk g) :
    g ∈ StatedScalars (Fin 3) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have : Group.IsPerfect (slPi π 3 (p ^ f) K) := isPerfect_slPi hK hq2
  have hC := le_centralizer_of_isPerfect (S := slPi π 3 (p ^ f) K) (g := g) fun x hx => by
    rw [← ProjGenLinGroup.mk_eq_one, map_mul, map_mul, map_mul, map_inv, map_inv, h x hx]
    group
  refine Sec4.mem_statedScalars_of_commute hπ hq' hτ hτ1 fun x hx => ?_
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hC hx)).symm

end SL

section Proj

variable {K : Type} [Field K]

theorem center_projImage_eq_bot {ι : Type} [Fintype ι] [DecidableEq ι] {H : Subgroup (GL ι K)}
    [Group.IsPerfect H]
    (hZ : ∀ z ∈ Subgroup.center H, (z : GL ι K) ∈ Subgroup.center (GL ι K)) :
    Subgroup.center (projImage H) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨_, ⟨h, hh, rfl⟩⟩ hcen
  have hcomm : ∀ k ∈ H, h⁻¹ * k⁻¹ * h * k ∈ Subgroup.center (GL ι K) := by
    intro k hk
    have h1 := Subgroup.mem_center_iff.mp hcen ⟨ProjGenLinGroup.mk k, Subgroup.mem_map_of_mem _ hk⟩
    have h2 : ProjGenLinGroup.mk k * ProjGenLinGroup.mk h =
        ProjGenLinGroup.mk h * ProjGenLinGroup.mk k := congrArg Subtype.val h1
    rw [← ProjGenLinGroup.mk_eq_one, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_assoc ((ProjGenLinGroup.mk h)⁻¹ * (ProjGenLinGroup.mk k)⁻¹), ← h2]
    group
  have hc : QuotientGroup.mk' (Subgroup.center H) (⟨h, hh⟩ : H) ∈
      Subgroup.center (H ⧸ Subgroup.center H) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ y
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := Subgroup.mem_center_iff.mp (hcomm k k.2) z
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev]
    simpa [mul_assoc] using hz
  rw [Group.IsPerfect.center_quotient_center_eq_bot, Subgroup.mem_bot,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
  apply Subtype.ext
  exact ProjGenLinGroup.mk_eq_one.mpr (hZ _ hc)

variable {p f : ℕ} {π : Bool}

theorem isPerfect_projImage_slPi (hK : PiField π p f K) (hq2 : 2 < p ^ f) :
    Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) := by
  have : Group.IsPerfect (slPi π 3 (p ^ f) K) := isPerfect_slPi hK hq2
  exact Group.IsPerfect.map _

theorem center_projImage_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) : Subgroup.center (projImage (slPi π 3 (p ^ f) K)) = ⊥ := by
  have : Group.IsPerfect (slPi π 3 (p ^ f) K) := isPerfect_slPi hK hq2
  refine center_projImage_eq_bot fun z hz => ?_
  have := mem_statedScalars_of_mem_center hK hq hz
  rwa [GeneralLinearGroup.center_eq_range_scalar]

theorem center_projImage_glPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) : Subgroup.center (projImage (glPi π 3 (p ^ f) K)) = ⊥ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rw [eq_bot_iff]
  rintro ⟨_, ⟨g, hg, rfl⟩⟩ hcen
  have hs : g ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_commute_mk hK hq hq2 fun s hs => ?_
    have h1 := Subgroup.mem_center_iff.mp hcen
      ⟨ProjGenLinGroup.mk s, Subgroup.mem_map_of_mem _ (Sec4.slPi_le_glPi hπ hs)⟩
    exact (congrArg Subtype.val h1).symm
  apply Subtype.ext
  refine ProjGenLinGroup.mk_eq_one.mpr ?_
  rwa [GeneralLinearGroup.center_eq_range_scalar]

end Proj

section Two

variable {K : Type} [Field K] {p f : ℕ}

theorem eq_two_one_of_pow_eq_two (hp : p.Prime) (h2 : p ^ f = 2) : p = 2 ∧ f = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h2
  have hp2 : p = 2 := by
    have hdvd : p ∣ 2 := ⟨p ^ (f - 1), by rw [← pow_succ', Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr hf), h2]⟩
    rcases Nat.prime_two.eq_one_or_self_of_dvd p hdvd with h | h
    · exact absurd h hp.one_lt.ne'
    · exact h
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective le_rfl (show 2 ^ f = 2 ^ 1 by rw [h2, pow_one])⟩

theorem isSolvable_slPi_two (hK : PiField false p f K) (h2 : p ^ f = 2) :
    Group.IsSolvable (slPi false 3 (p ^ f) K) := by
  obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hK.prime h2
  have hU : UnitaryFieldData 2 1 K := hK.unitary
  have := hK.finite
  have hcard : Nat.card (slPi false 3 (2 ^ 1) K) = 216 :=
    CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
  have := Fintype.ofFinite (slPi false 3 (2 ^ 1) K)
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
    Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)

theorem isSolvable_glPi_two (hK : PiField false p f K) (h2 : p ^ f = 2) :
    Group.IsSolvable (glPi false 3 (p ^ f) K) := by
  have hπ : false = false → UnitaryFieldData p f K := fun _ => hK.unitary
  have := isSolvable_slPi_two hK h2
  let ι : slPi false 3 (p ^ f) K →* glPi false 3 (p ^ f) K :=
    Subgroup.inclusion (Sec4.slPi_le_glPi hπ)
  let δ : glPi false 3 (p ^ f) K →* Kˣ :=
    (GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).comp (glPi false 3 (p ^ f) K).subtype
  refine Group.isSolvable_of_ker_le_range ι δ fun x hx => ?_
  have hdet : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have := congrArg Units.val hx
    simpa [δ] using this
  exact ⟨⟨x, (Sec4.mem_slPi_iff hπ).mpr ⟨x.2, hdet⟩⟩, rfl⟩

theorem isSolvable_projImage {ι : Type} [Fintype ι] [DecidableEq ι] {H : Subgroup (GL ι K)}
    [Group.IsSolvable H] : Group.IsSolvable (projImage H) :=
  Group.isSolvable_of_surjective ((ProjGenLinGroup.mk : GL ι K →* _).subgroupMap_surjective H)

theorem isSolvable_projImage_glPi_two (hK : PiField false p f K) (h2 : p ^ f = 2) :
    Group.IsSolvable (projImage (glPi false 3 (p ^ f) K)) := by
  have := isSolvable_glPi_two hK h2
  exact isSolvable_projImage

theorem isSolvable_projImage_slPi_two (hK : PiField false p f K) (h2 : p ^ f = 2) :
    Group.IsSolvable (projImage (slPi false 3 (p ^ f) K)) := by
  have := isSolvable_slPi_two hK h2
  exact isSolvable_projImage

end Two

section Models

theorem piField_galoisField (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) :
    PiField true p e (GaloisField p e) :=
  ⟨Fact.out, he, by
    rw [GaloisField.card p e (by omega)]
    rfl⟩

theorem piField_galoisField_two (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) :
    PiField false p e (GaloisField p (2 * e)) :=
  ⟨Fact.out, he, by
    rw [GaloisField.card p (2 * e) (by omega)]
    show p ^ (2 * e) = (p ^ e) ^ 2
    rw [← pow_mul, mul_comm]⟩

theorem projSL_eq (p e : ℕ) [Fact p.Prime] :
    projSL 3 (GaloisField p e) = projImage (slPi true 3 (p ^ e) (GaloisField p e)) :=
  (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 3 _).symm

theorem projSU_eq (p e : ℕ) [Fact p.Prime] :
    projSU 3 p e = projImage (slPi false 3 (p ^ e) (GaloisField p (2 * e))) :=
  (CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 3 p e).symm

theorem isPerfect_center_projSL (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (hq : p ^ e % 3 = 1) :
    Group.IsPerfect (projSL 3 (GaloisField p e)) ∧
      Subgroup.center (projSL 3 (GaloisField p e)) = ⊥ := by
  have hK := piField_galoisField p e he
  have hq2 : 2 < p ^ e := by
    have : p ^ e ≠ 1 := fun h => by
      have := Nat.pow_eq_one.mp h
      rcases this with h' | h'
      · exact (Fact.out : p.Prime).one_lt.ne' h'
      · omega
    omega
  rw [projSL_eq]
  exact ⟨isPerfect_projImage_slPi hK hq2, center_projImage_slPi hK hq hq2⟩

theorem isPerfect_center_projSU (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (hq : p ^ e % 3 = 2)
    (hq2 : 2 < p ^ e) :
    Group.IsPerfect (projSU 3 p e) ∧ Subgroup.center (projSU 3 p e) = ⊥ := by
  have hK := piField_galoisField_two p e he
  rw [projSU_eq]
  exact ⟨isPerfect_projImage_slPi hK hq2, center_projImage_slPi hK hq hq2⟩

theorem isSolvable_projSU_two :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    Group.IsSolvable (projSU 3 2 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [projSU_eq]
  exact isSolvable_projImage_slPi_two (piField_galoisField_two 2 1 le_rfl) (by norm_num)

theorem isPerfect_center_alt7 :
    Group.IsPerfect (alternatingGroup (Fin 7)) ∧
      Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
  ⟨Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp)),
    alternatingGroup.center_eq_bot (by simp)⟩

end Models

end CFSG.RankThree.PartTwo.Sec13
