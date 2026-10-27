module

public import CFSG.LocalAnalysis.StandardType.GGTriD4TwoRow.Reduction
public import CFSG.LocalAnalysis.StandardType.GGTriD4TwoRow.Bridge
public import CFSG.LocalAnalysis.StandardType.GGTriD4TwoRow.Sylow
public import CFSG.LocalAnalysis.StandardType.GGTriD4TwoRow.FieldComp
public import CFSG.LocalAnalysis.StandardType.GGIrred937CompLemmas
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputsModel
public import CFSG.Mathlib.GroupTheory.SylowConj

public section

namespace CFSG.StandardType.TriD4TwoRow

open Subgroup CFSG.Open CFSG.RankThree.PartTwo.Sec4.Item434D42

section Transport

variable {G R : Type} [Group G] [Group R] {P : Subgroup G} [P.Normal]

noncomputable def conjCongr (ε : R ≃* P) : G →* MulAut R :=
  (MulAut.congr ε.symm).toMonoidHom.comp MulAut.conjNormal

theorem conjCongr_apply (ε : R ≃* P) (y : G) (r : R) :
    conjCongr ε y r = ε.symm (MulAut.conjNormal y (ε r)) := by
  simp [conjCongr, MulAut.congr_apply]

theorem coe_ε_conjCongr_apply (ε : R ≃* P) (y : G) (r : R) :
    ((ε (conjCongr ε y r) : P) : G) = y * ε r * y⁻¹ := by
  rw [conjCongr_apply, MulEquiv.apply_symm_apply, MulAut.conjNormal_apply]

theorem conjCongr_of_mem (ε : R ≃* P) {p : G} (hp : p ∈ P) :
    conjCongr ε p = MulAut.conj (ε.symm ⟨p, hp⟩) := by
  ext r
  apply ε.injective
  apply Subtype.ext
  rw [coe_ε_conjCongr_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.apply_symm_apply]
  rfl

theorem exists_fixed_involution_of_conjCongr (ε : R ≃* P)
    (hbij : Function.Bijective (conjCongr ε))
    (h2 : ∀ y : G, y ∉ P → y ^ 3 = 1 → ∃ t ∈ P, t ≠ 1 ∧ t ^ 2 = 1 ∧ y * t = t * y)
    {φ : MulAut R} (hφ : φ ∉ Set.range (MulAut.conj : R →* MulAut R)) (hφ3 : φ ^ 3 = 1) :
    ∃ t : R, t ≠ 1 ∧ t ^ 2 = 1 ∧ φ t = t := by
  obtain ⟨y, rfl⟩ := hbij.2 φ
  have hyP : y ∉ P := fun hy => hφ ⟨ε.symm ⟨y, hy⟩, (conjCongr_of_mem ε hy).symm⟩
  have hy3 : y ^ 3 = 1 := hbij.1 (by rw [map_pow, hφ3, map_one])
  obtain ⟨t, htP, ht1, ht2, hyt⟩ := h2 y hyP hy3
  refine ⟨ε.symm ⟨t, htP⟩, fun h => ht1 ?_, ?_, ?_⟩
  · have := congrArg (fun x => ((ε x : P) : G)) h
    simpa using this
  · apply ε.injective
    apply Subtype.ext
    simp [ht2]
  · apply ε.injective
    apply Subtype.ext
    rw [coe_ε_conjCongr_apply, MulEquiv.apply_symm_apply, hyt, mul_inv_cancel_right]

theorem exists_conj_moving_of_conjCongr [Finite R] (ε : R ≃* P)
    (hbij : Function.Bijective (conjCongr ε))
    (h3 : ∀ B : Subgroup G, IsElemAbelian 3 B → 27 ≤ Nat.card B → ∀ u ∈ B, u ∈ P → u ≠ 1 →
      IsSolvable ↥(centralizer {u} ⊓ P) ∨
        ∃ n ∈ P, n ∈ normalizer (B : Set G) ∧ n * u * n⁻¹ ∉ zpowers u)
    {A : Subgroup (MulAut R)} (hA : IsElemAbelian 3 A) (h27 : 27 ≤ Nat.card A) {a₀ : MulAut R}
    (ha₀ : a₀ ∈ A) (ha₀1 : a₀ ≠ 1) (hI : a₀ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcyc : CFSG.StandardType.GGFixCompCyclic 3 a₀) :
    ∃ n : R, MulAut.conj n ∈ normalizer (A : Set (MulAut R)) ∧
      MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ zpowers a₀ := by
  set ρ : G ≃* MulAut R := MulEquiv.ofBijective (conjCongr ε) hbij with hρ
  have hρa : ∀ y, ρ y = conjCongr ε y := fun _ => rfl
  set B : Subgroup G := A.map ρ.symm.toMonoidHom with hB
  have hmemB : ∀ y, y ∈ B ↔ ρ y ∈ A := by
    intro y
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hy
      exact ⟨ρ y, hy, by simp⟩
  have hBab : IsElemAbelian 3 B := hA.map _
  have hB27 : 27 ≤ Nat.card B := by
    rw [hB, Subgroup.card_map_of_injective ρ.symm.injective]
    exact h27
  obtain ⟨r₀, rfl⟩ := hI
  set u : G := (ε r₀ : G) with hu
  have huP : u ∈ P := (ε r₀).2
  have hρu : ρ u = MulAut.conj r₀ := by
    rw [hρa, conjCongr_of_mem ε huP]
    congr 1
    apply ε.injective
    simp [hu]
  have huB : u ∈ B := (hmemB u).2 (hρu ▸ ha₀)
  have hu1 : u ≠ 1 := fun h => ha₀1 (by rw [← hρu, h, map_one])
  rcases h3 B hBab hB27 u huB huP hu1 with hs | ⟨n, hnP, hnN, hnu⟩
  · exfalso
    refine CFSG.StandardType.Irred937.not_ggFixCompCyclic_of_solvable _ ?_ hcyc
    let f : ↥(CFSG.StandardType.ggFix (MulAut.conj r₀)) →* ↥(centralizer {u} ⊓ P) :=
      { toFun := fun r => ⟨(ε r : G), by
          refine Subgroup.mem_inf.mpr ⟨?_, (ε r).2⟩
          rw [mem_centralizer_singleton_iff]
          have hr : r₀ * r * r₀⁻¹ = r := r.2
          have := congrArg (fun x => ((ε x : P) : G)) hr
          simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at this
          rw [hu]
          calc (ε r : G) * (ε r₀ : G) = (ε r₀ : G) * (ε r : G) * (ε r₀ : G)⁻¹ * (ε r₀ : G) := by
                rw [this]
            _ = (ε r₀ : G) * (ε r : G) := by group⟩
        map_one' := by simp
        map_mul' := fun a b => by simp }
    have hf : Function.Injective f := by
      intro a b hab
      have := congrArg (fun x => ((x : ↥(centralizer {u} ⊓ P)) : G)) hab
      simp only [f, MonoidHom.coe_mk, OneHom.coe_mk] at this
      exact Subtype.ext (ε.injective (Subtype.ext this))
    have : Group.IsSolvable ↥(centralizer {u} ⊓ P) := hs
    exact solvable_of_solvable_injective hf
  · refine ⟨ε.symm ⟨n, hnP⟩, ?_, ?_⟩
    · have hρn : ρ n = MulAut.conj (ε.symm ⟨n, hnP⟩) := conjCongr_of_mem ε hnP
      rw [mem_normalizer_iff]
      intro x
      obtain ⟨y, rfl⟩ := ρ.surjective x
      rw [← hρn, ← map_inv, ← map_mul, ← map_mul, ← hmemB, ← hmemB]
      exact mem_normalizer_iff.mp hnN y
    · rw [← conjCongr_of_mem ε hnP, ← hρa, ← hρu, ← map_inv, ← map_mul, ← map_mul]
      intro hmem
      apply hnu
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
      refine mem_zpowers_iff.mpr ⟨k, ρ.injective ?_⟩
      rw [map_zpow, hk]

end Transport

theorem d4G_exists_involution_commute :
    haveI := d4P_normal_d4G
    ∀ y : d4G, y ∉ d4P.subgroupOf d4G → y ^ 3 = 1 →
      ∃ t ∈ d4P.subgroupOf d4G, t ≠ 1 ∧ t ^ 2 = 1 ∧ y * t = t * y := by
  intro y hyP hy3
  have hyP' : (y : Equiv.Perm (Fin 2457)) ∉ d4P := fun h => hyP (Subgroup.mem_subgroupOf.mpr h)
  have hy3' : (y : Equiv.Perm (Fin 2457)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hy3, Subgroup.coe_one]
  obtain ⟨t, htP, ht1, ht2, hyt⟩ := d4S0_facts.2.2.2.2.2 _ y.2 hyP' hy3'
  refine ⟨⟨t, d4P_le_d4G htP⟩, Subgroup.mem_subgroupOf.mpr htP, fun h => ht1 ?_, ?_, ?_⟩
  · exact congrArg Subtype.val h
  · exact Subtype.ext (by simp [ht2])
  · exact Subtype.ext (by simp [hyt])

theorem d4G_exists_normalizer_moving_or_solvable
    (hrk : ∀ E : Subgroup (Equiv.Perm (Fin 2457)), E ≤ d4P → IsElemAbelian 3 E → Nat.card E ≤ 9) :
    ∀ B : Subgroup d4G, IsElemAbelian 3 B → 27 ≤ Nat.card B → ∀ u ∈ B,
      u ∈ d4P.subgroupOf d4G → u ≠ 1 →
      IsSolvable ↥(centralizer {u} ⊓ d4P.subgroupOf d4G) ∨
        ∃ n ∈ d4P.subgroupOf d4G, n ∈ normalizer (B : Set d4G) ∧ n * u * n⁻¹ ∉ zpowers u := by
  intro B hB h27 u huB huP hu1
  set B₁ : Subgroup (Equiv.Perm (Fin 2457)) := B.map d4G.subtype with hB₁
  have hB₁G : B₁ ≤ d4G := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hB₁c : Nat.card B₁ = Nat.card B := Subgroup.card_map_of_injective d4G.subtype_injective
  rcases exists_normalizer_moving_or_solvable hrk hB₁G (hB.map _) (hB₁c ▸ h27) ⟨u, huB, rfl⟩
    (Subgroup.mem_subgroupOf.mp huP) (fun h => hu1 (Subtype.ext h)) with hs | ⟨n, hnP, hnN, hnu⟩
  · left
    let f : ↥(centralizer {u} ⊓ d4P.subgroupOf d4G) →*
        ↥(centralizer {(u : Equiv.Perm (Fin 2457))} ⊓ d4P) :=
      { toFun := fun x => ⟨((x : d4G) : Equiv.Perm (Fin 2457)), by
          obtain ⟨hxc, hxP⟩ := Subgroup.mem_inf.mp x.2
          refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_subgroupOf.mp hxP⟩
          rw [mem_centralizer_singleton_iff] at hxc ⊢
          exact congrArg Subtype.val hxc⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro a b hab
      have := congrArg (fun x : ↥(centralizer {(u : Equiv.Perm (Fin 2457))} ⊓ d4P) =>
        (x : Equiv.Perm (Fin 2457))) hab
      exact Subtype.ext (Subtype.ext this)
    have : Group.IsSolvable ↥(centralizer {(u : Equiv.Perm (Fin 2457))} ⊓ d4P) := hs
    exact solvable_of_solvable_injective hf
  · right
    have hmem : ∀ b : d4G, b ∈ B ↔ (b : Equiv.Perm (Fin 2457)) ∈ B₁ := fun b =>
      ⟨fun hb => ⟨b, hb, rfl⟩, fun ⟨c, hc, he⟩ => (Subtype.ext he : c = b) ▸ hc⟩
    refine ⟨⟨n, d4P_le_d4G hnP⟩, Subgroup.mem_subgroupOf.mpr hnP, ?_, ?_⟩
    · rw [mem_normalizer_iff]
      intro b
      rw [hmem, hmem]
      exact mem_normalizer_iff.mp hnN b
    · intro h
      apply hnu
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
      exact mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem ggTriD4TwoModelFacts_holds :
    GGTriD4TwoModelFacts := by
  intro K _ _ hK hs hna
  obtain ⟨e⟩ := nonempty_triD4Two_equiv_d4P hK
  have hZR := center_eq_bot_of_simple hs hna
  have hZP : Subgroup.center d4P = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : e.symm x ∈ Subgroup.center (GGTriD4R 1 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (Subgroup.mem_center_iff.mp hx (e y))
    rw [hZR, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    simpa using congrArg e hx'
  have := d4P_normal_d4G
  let ε : GGTriD4R 1 K ≃* d4P.subgroupOf d4G :=
    e.trans (Subgroup.subgroupOfEquivOfLe d4P_le_d4G).symm
  have hbij : Function.Bijective (conjCongr ε) :=
    (MulAut.congr ε.symm).bijective.comp (d4G_conjNormal_bijective hZP)
  have hI : GGTriD4ID 1 K = Set.range (MulAut.conj : GGTriD4R 1 K →* MulAut (GGTriD4R 1 K)) :=
    ggTriD4InnDiagInput_holds 1 le_rfl K hK hs
  have hrkR := ggTriD4_card_le_of_isElemAbelian 1 le_rfl K hK hs
  have hrk : ∀ E : Subgroup (Equiv.Perm (Fin 2457)), E ≤ d4P → IsElemAbelian 3 E →
      Nat.card E ≤ 9 := by
    intro E hEP hE
    have h := hrkR ((E.subgroupOf d4P).map e.symm.toMonoidHom) ((hE.subgroupOf d4P).map _)
    rw [Subgroup.card_map_of_injective e.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv] at h
    simpa using h
  have : Finite (GGTriD4R 1 K) := Finite.of_equiv _ e.symm.toEquiv
  refine ⟨?_, fun φ _ hφI hφ3 => ?_, fun A hA _ h27 _ a₀ ha₀ ha₀1 haI hcyc => ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : 2 ∣ Nat.card (GGTriD4R 1 K) := by
      rw [Nat.card_congr e.toEquiv, card_d4P]
      norm_num
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
    refine ⟨t, fun h => ?_, by rw [← ht]; exact pow_orderOf_eq_one t⟩
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · rw [hI] at hφI
    exact exists_fixed_involution_of_conjCongr ε hbij d4G_exists_involution_commute hφI hφ3
  · rw [hI] at haI
    exact exists_conj_moving_of_conjCongr ε hbij
      (d4G_exists_normalizer_moving_or_solvable hrk) hA h27 ha₀ ha₀1 haI hcyc

theorem ggNbrKGFieldTriD4Two_holds :
    GGNbrKGFieldTriD4Two :=
  ggNbrKGFieldTriD4Two_of_model ggTriD4TwoModelFacts_holds

end CFSG.StandardType.TriD4TwoRow
