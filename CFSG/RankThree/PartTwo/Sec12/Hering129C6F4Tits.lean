module

public import CFSG.RankThree.PartTwo.Sec12.Hering129C6F4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425F4
import CFSG.RankThree.PartOne.S11d.FixedFactsRee
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam6

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.RankThree.PartTwo.Sec4.Ronan148H
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open CFSG.LieType.Ree (ReeTag)

namespace Hering129C

@[expose] def E9MoveOdd (S : Type) [Group S] : Prop :=
  ∀ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 → ∀ s ∈ E, s ≠ 1 →
    ∃ n ∈ Subgroup.normalizer (E : Set S),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S) ∧ n ^ 3 = 1

theorem E9MoveOdd.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : E9MoveOdd Y) :
    E9MoveOdd X := by
  intro E hE hE9 s hs hs1
  have hEm : CFSG.Assembly.IsElemAbelian 3 (E.map e.toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hE _
  obtain ⟨n, hn, hns, hn3⟩ := h (E.map e.toMonoidHom) hEm
    (by rw [Subgroup.card_map_of_injective e.injective, hE9]) (e s) ⟨s, hs, rfl⟩
    (by rw [Ne, map_eq_one_iff _ e.injective]; exact hs1)
  have hN := Subgroup.map_equiv_normalizer_eq E e
  rw [← hN] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  refine ⟨m, hm, fun hm' => hns ?_, ?_⟩
  · have hZ : (Subgroup.zpowers s).map e.toMonoidHom = Subgroup.zpowers (e s) :=
      MonoidHom.map_zpowers _ s
    rw [← hZ, ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨m, hm', rfl⟩
  · apply e.injective
    simpa using hn3

section Ree


open CFSG.RankThree.PartOne.KFU (torusSU torusVec diagU diagUHom diagU_injective permGL
  mem_torusSU_iff)

variable (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem e9MoveOdd_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    E9MoveOdd (ReeTag.F4.reeGamma K a) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro B hB hB9 c hcB hc1
  have hc3 : c ^ 3 = 1 := hB.2 c hcB
  have hBc : ∀ x ∈ B, ∀ z ∈ B, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  obtain ⟨y, hyB, hyc⟩ : ∃ y ∈ B, y ∉ Subgroup.zpowers c := by
    by_contra h
    push Not at h
    have hle : B ≤ Subgroup.zpowers c := fun x hx => h x hx
    have h1 := Subgroup.card_le_of_le hle
    rw [hB9, Nat.card_zpowers] at h1
    have h2 : orderOf c ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hc3
    omega
  have hy3 : y ^ 3 = 1 := hB.2 y hyB
  have hy1 : y ≠ 1 := fun h => hyc (h ▸ Subgroup.one_mem _)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  obtain ⟨eU⟩ := Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK y hyo
  set Fq := GaloisField 2 (2 * (2 * a + 1)) with hFq
  have hU : UnitaryFieldData 2 (2 * a + 1) Fq :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  haveI := hU.finite
  have hpq := three_dvd_two_pow_odd_add_one a
  set C := Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)) with hCdef
  have hBC : B ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hBc x hx y hyB)
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set B₁ : Subgroup C := B.subgroupOf C with hB₁
  obtain ⟨ψ, hψ⟩ := CFSG.RankThree.PartOne.KFU.exists_diag_iso_le_of_iso hU Nat.prime_three hpq
    eU.symm B₁ (fun x hx => Subtype.ext (hB.2 _ hx))
    (fun x hx z hz => Subtype.ext (hBc _ hx _ hz))
  set T : Subgroup (unitarySU 2 (2 * a + 1) Fq 3) :=
    (torusSU 3 3 Fq).subgroupOf (unitarySU 2 (2 * a + 1) Fq 3) with hT
  have hTle : B₁.comap ψ.toMonoidHom ≤ T := fun g hg => hψ g hg
  have hTcard : Nat.card T ≤ 9 := by
    rw [hT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (CFSG.RankThree.PartOne.KFU.torusSU_le_unitarySU hU hpq)).toEquiv]
    exact CFSG.RankThree.PartOne.KFU.card_torusSU_le (by norm_num) 2
  have hB₁c : Nat.card (B₁.comap ψ.toMonoidHom) = 9 := by
    have hmap : (B₁.comap ψ.toMonoidHom).map ψ.toMonoidHom = B₁ :=
      Subgroup.map_comap_eq_self_of_surjective ψ.surjective _
    rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hmap, hB₁,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv, hB9]
  have hTeq : B₁.comap ψ.toMonoidHom = T := Subgroup.eq_of_le_of_card_ge hTle (by omega)
  have hmemT : ∀ g : unitarySU 2 (2 * a + 1) Fq 3,
      ψ g ∈ B₁ ↔ (g : GL (Fin 3) Fq) ∈ torusSU 3 3 Fq := by
    intro g
    have := SetLike.ext_iff.mp hTeq g
    exact this
  set c₁ : C := ⟨c, hBC hcB⟩ with hc₁
  set y₁ : C := ⟨y, hyC⟩ with hy₁
  have hc₁B : c₁ ∈ B₁ := hcB
  have hy₁B : y₁ ∈ B₁ := hyB
  have hgc : ((ψ.symm c₁ : unitarySU 2 (2 * a + 1) Fq 3) : GL (Fin 3) Fq) ∈ torusSU 3 3 Fq :=
    (hmemT _).mp (by rw [MulEquiv.apply_symm_apply]; exact hc₁B)
  have hgy : ((ψ.symm y₁ : unitarySU 2 (2 * a + 1) Fq 3) : GL (Fin 3) Fq) ∈ torusSU 3 3 Fq :=
    (hmemT _).mp (by rw [MulEquiv.apply_symm_apply]; exact hy₁B)
  obtain ⟨d, hd3, hdp, hdc⟩ := mem_torusSU_iff.mp hgc
  obtain ⟨e, he3, hep, hey⟩ := mem_torusSU_iff.mp hgy
  let P : Equiv.Perm (Fin 3) → unitarySU 2 (2 * a + 1) Fq 3 := fun σ =>
    ⟨permGL σ, CFSG.RankThree.PartOne.KFU.permGL_mem_unitarySU hU σ⟩
  have hPcoe : ∀ σ, ((P σ : unitarySU 2 (2 * a + 1) Fq 3) : GL (Fin 3) Fq) = permGL σ :=
    fun _ => rfl
  have hecomm : ∀ σ : Equiv.Perm (Fin 3), e ∘ σ.symm = e := by
    intro σ
    have hcy : ψ (P σ) * y₁ = y₁ * ψ (P σ) := by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (ψ (P σ)).2
    have h1 : P σ * ψ.symm y₁ = ψ.symm y₁ * P σ := by
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hcy]
    have h2 : permGL σ * diagU e * (permGL σ)⁻¹ = diagU e := by
      rw [hey]
      have := congrArg (fun x : unitarySU 2 (2 * a + 1) Fq 3 => (x : GL (Fin 3) Fq)) h1
      simp only [Subgroup.coe_mul, hPcoe] at this
      rw [this, mul_inv_cancel_right]
    rw [CFSG.RankThree.PartOne.KFU.permGL_conj_diagU] at h2
    exact diagU_injective h2
  have heconst : ∀ i, e i = e 0 := by
    intro i
    fin_cases i
    · rfl
    · have := congrFun (hecomm (Equiv.swap 0 1)) 0
      simpa using this
    · have := congrFun (hecomm (Equiv.swap 0 2)) 0
      simpa using this
  have hdnc : ¬ ∀ i j, d i = d j := by
    intro hdconst
    have he1 : e 0 ≠ 1 := by
      intro h1
      apply hy1
      have : e = 1 := funext fun i => by rw [heconst i, h1]; rfl
      have hgy1 : ψ.symm y₁ = 1 := by
        apply Subtype.ext
        rw [← hey, this, CFSG.RankThree.PartOne.KFU.diagU_one]
        rfl
      have : y₁ = 1 := by
        rw [← MulEquiv.apply_symm_apply ψ y₁, hgy1, map_one]
      exact congrArg Subtype.val this
    have hprim : IsPrimitiveRoot (e 0) 3 :=
      (IsPrimitiveRoot.iff_orderOf).mpr (orderOf_eq_prime (he3 0) he1)
    have hprim' : IsPrimitiveRoot ((e 0 : Fqˣ) : Fq) 3 := IsPrimitiveRoot.coe_units_iff.mpr hprim
    have hd0 : ((d 0 : Fqˣ) : Fq) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hd3 0, Units.val_one]
    obtain ⟨k, -, hk'⟩ := hprim'.eq_pow_of_pow_eq_one hd0
    have hk : e 0 ^ k = d 0 := Units.ext (by rw [Units.val_pow_eq_pow_val, hk'])
    have hde : d = e ^ k := funext fun i => by
      rw [Pi.pow_apply, heconst i, hdconst i 0, hk]
    have hcy : c₁ = y₁ ^ k := by
      apply ψ.symm.injective
      apply Subtype.ext
      rw [map_pow, SubgroupClass.coe_pow, ← hdc, ← hey, hde,
        CFSG.RankThree.PartOne.KFU.diagU_pow]
    apply hyc
    have hcy' : c = y ^ k := congrArg Subtype.val hcy
    have hle : Subgroup.zpowers c ≤ Subgroup.zpowers y := by
      rw [Subgroup.zpowers_le, hcy']
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) k
    have hcard : Nat.card (Subgroup.zpowers y) ≤ Nat.card (Subgroup.zpowers c) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hyo,
        orderOf_eq_prime hc3 hc1]
    rw [Subgroup.eq_of_le_of_card_ge hle hcard]
    exact Subgroup.mem_zpowers y
  set ρ : Equiv.Perm (Fin 3) := finRotate 3 with hρ
  have hPconj : ∀ x : GL (Fin 3) Fq, x ∈ torusSU 3 3 Fq ↔
      permGL ρ * x * (permGL ρ)⁻¹ ∈ torusSU 3 3 Fq := by
    intro x
    constructor
    · exact (CFSG.RankThree.PartOne.KFU.normPerm_permGL (p := 3) ρ).1 x
    · intro hx
      have h := (CFSG.RankThree.PartOne.KFU.normPerm_permGL (p := 3) ρ⁻¹).1 _ hx
      have heq : (permGL ρ)⁻¹ * (permGL ρ * x * (permGL ρ)⁻¹) * ((permGL ρ)⁻¹)⁻¹ = x := by
        group
      rwa [map_inv, heq] at h
  set n : ReeTag.F4.reeGamma K a := ((ψ (P ρ) : C) : ReeTag.F4.reeGamma K a) with hn
  have hnC : n ∈ C := (ψ (P ρ)).2
  have hn3 : n ^ 3 = 1 := by
    have hρ3 : ρ ^ 3 = 1 := by decide
    have h1 : (P ρ) ^ 3 = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, hPcoe, ← map_pow, hρ3, map_one]
      rfl
    have h2 : (ψ (P ρ)) ^ 3 = 1 := by rw [← map_pow, h1, map_one]
    simpa [hn] using congrArg Subtype.val h2
  refine ⟨n, ?_, ?_, hn3⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ z : C, (z : ReeTag.F4.reeGamma K a) ∈ B ↔
        n * z * n⁻¹ ∈ B := by
      intro z
      have hz : ((ψ (P ρ) * z * (ψ (P ρ))⁻¹ : C) : ReeTag.F4.reeGamma K a) = n * z * n⁻¹ := rfl
      rw [← hz]
      change z ∈ B₁ ↔ ψ (P ρ) * z * (ψ (P ρ))⁻¹ ∈ B₁
      rw [← MulEquiv.apply_symm_apply ψ z, ← map_inv, ← map_mul, ← map_mul, hmemT, hmemT]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hPcoe]
      exact hPconj _
    constructor
    · intro hx
      exact (key ⟨x, hBC hx⟩).mp hx
    · intro hx
      have hxC : x ∈ C := by
        have h1 : n * x * n⁻¹ ∈ C := hBC hx
        have h2 : x = n⁻¹ * (n * x * n⁻¹) * n := by group
        rw [h2]
        exact mul_mem (mul_mem (inv_mem hnC) h1) hnC
      exact (key ⟨x, hxC⟩).mpr hx
  · intro hnZ
    have hs : n * c * n⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp hnZ c).mp (Subgroup.mem_zpowers c)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hk₁ : c₁ ^ k = ψ (P ρ) * c₁ * (ψ (P ρ))⁻¹ := Subtype.ext (by
      rw [SubgroupClass.coe_zpow]
      exact hk)
    have hk₂ : (ψ.symm c₁) ^ k = P ρ * ψ.symm c₁ * (P ρ)⁻¹ := by
      apply ψ.injective
      rw [map_zpow, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hk₁]
    have hk₃ : (diagU d) ^ k = permGL ρ * diagU d * (permGL ρ)⁻¹ := by
      rw [hdc]
      have := congrArg (fun x : unitarySU 2 (2 * a + 1) Fq 3 => (x : GL (Fin 3) Fq)) hk₂
      simpa [hPcoe] using this
    rw [CFSG.RankThree.PartOne.KFU.permGL_conj_diagU] at hk₃
    have hdk : d ∘ ρ.symm = d ^ k := by
      apply diagU_injective
      rw [← hk₃]
      exact (map_zpow diagUHom d k).symm
    exact rot_not_mem_zpowers hd3 hdnc k hdk

end Ree

section Derived

variable {H : Type} [Group H]

theorem e9Move_of_odd_derived {N : Subgroup H} (hN : ∀ y : H, y ^ 3 = 1 → y ∈ N)
    (h : E9MoveOdd H) : E9Move ↥N := by
  intro E hE hE9 s hs hs1
  set E' : Subgroup H := E.map N.subtype with hE'
  have hE'el : CFSG.Assembly.IsElemAbelian 3 E' := CFSG.Open.IsElemAbelian.map hE _
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective N.subtype_injective, hE9]
  obtain ⟨n, hn, hns, hn3⟩ := h E' hE'el hE'9 (s : H) ⟨s, hs, rfl⟩
    (fun h1 => hs1 (Subtype.ext h1))
  have hnN : n ∈ N := hN n hn3
  have hmemE : ∀ x : ↥N, (x : H) ∈ E' ↔ x ∈ E := fun x =>
    Subgroup.mem_map_iff_mem N.subtype_injective
  refine ⟨⟨n, hnN⟩, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := (Subgroup.mem_normalizer_iff.mp hn) (x : H)
    rw [← hmemE, ← hmemE (⟨n, hnN⟩ * x * ⟨n, hnN⟩⁻¹)]
    exact h1
  · intro hm
    apply hns
    rw [Subgroup.mem_normalizer_iff]
    intro h0
    have hz : Subgroup.zpowers (s : H) = (Subgroup.zpowers s).map N.subtype :=
      (MonoidHom.map_zpowers N.subtype s).symm
    have hzN : Subgroup.zpowers (s : H) ≤ N := Subgroup.zpowers_le.mpr s.2
    by_cases h0N : h0 ∈ N
    · have h2 := (Subgroup.mem_normalizer_iff.mp hm) ⟨h0, h0N⟩
      have hmz : ∀ x : ↥N, (x : H) ∈ Subgroup.zpowers (s : H) ↔ x ∈ Subgroup.zpowers s :=
        fun x => by rw [hz]; exact Subgroup.mem_map_iff_mem N.subtype_injective
      have h3 := hmz ⟨h0, h0N⟩
      have h4 := hmz (⟨n, hnN⟩ * ⟨h0, h0N⟩ * ⟨n, hnN⟩⁻¹)
      rw [h3]
      exact h2.trans h4.symm
    · have h5 : n * h0 * n⁻¹ ∉ N := fun hh => by
        apply h0N
        have := N.mul_mem (N.mul_mem (N.inv_mem hnN) hh) hnN
        simpa [mul_assoc] using this
      exact ⟨fun hh => absurd (hzN hh) h0N, fun hh => absurd (hzN hh) h5⟩

end Derived

section Tits


open CFSG.LieType.Ree.ReeTag (reeFixedEquivReeGamma)
open CFSG.LieType.Ree (reeFixed)

theorem e9MoveOdd_reeFixed_zmod_two : E9MoveOdd ↥(reeFixed ReeTag.F4 (ZMod 2) 0) :=
  (e9MoveOdd_reeGamma 0 (ZMod 2) (by rw [Nat.card_zmod]; norm_num)).of_mulEquiv
    (reeFixedEquivReeGamma (ZMod 2) 0)

theorem pow_three_mem_commutator_reeFixed_zmod_two {y : ↥(reeFixed ReeTag.F4 (ZMod 2) 0)}
    (hy : y ^ 3 = 1) : y ∈ _root_.commutator ↥(reeFixed ReeTag.F4 (ZMod 2) 0) := by
  have hT := CFSG.LieType.Simplicity.titsData (ZMod 2) (Nat.card_zmod 2)
  have hsup := hT.commutator_sup_zpowers_eq_top (Nat.card_zmod 2)
  have hg2 := hT.g₁_sq_mem
  haveI : (_root_.commutator ↥(reeFixed ReeTag.F4 (ZMod 2) 0)).Normal :=
    Subgroup.commutator_normal ⊤ ⊤
  exact CFSG.RankThree.PartOne.FieldFix.mem_of_odd_pow_of_sup_zpowers hsup hg2 (m := 3)
    (by decide) hy

theorem e9Move_commutator_reeFixed_zmod_two :
    E9Move ↥(_root_.commutator ↥(reeFixed ReeTag.F4 (ZMod 2) 0)) :=
  e9Move_of_odd_derived (fun _ hy => pow_three_mem_commutator_reeFixed_zmod_two hy)
    e9MoveOdd_reeFixed_zmod_two

theorem kFCensus46SixF4_tits :
    KFCensusOn (fun Q _ => ∃ f : ℕ, Blueprint.ReeTitsModel Q .Tits 2 f) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨f', hf'⟩ := hQ
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv Q 2 f' hf'
  exact census_false_of_e9Move hD
    (e.trans (CFSG.Sporadic.Schreier.Tits.titsDerivedIso (K := ZMod 2)).symm)
    e9Move_commutator_reeFixed_zmod_two

theorem kFCensus46SixF4_holds : KFCensus46SixF4 := by
  intro Q Lb _ _ _ c a I X f hQ hD
  obtain ⟨f', hf' | hf'⟩ := hQ
  · exact kFCensus46SixF4_twisted Q Lb c a I X f ⟨f', hf'⟩ hD
  · exact kFCensus46SixF4_tits Q Lb c a I X f ⟨f', hf'⟩ hD

end Tits

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
