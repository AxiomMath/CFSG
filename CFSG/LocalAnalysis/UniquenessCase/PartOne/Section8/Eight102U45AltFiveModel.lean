module

import CFSG.LocalAnalysis.UniquenessCase.UC6K332Bridge
import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix CFSG.RankThree
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec21.U4Lines
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor d8Comb_four d8Vec_mem_SU permGL_mem_SU
  exists_conj_into_d8Tor_su)

private def Q {G : Type} [Group G] (Y ℓ : Subgroup G) : Subgroup G :=
  Y ⊓ Subgroup.centralizer (ℓ : Set G) ⊓
    Subgroup.centralizer
      (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ : Set G)) : Set G)

private theorem mapL_inf {G G' : Type} [Group G] [Group G']
    {Y : Subgroup G} {Y' : Subgroup G'} (e : Y ≃* Y')
    {Z₁ Z₂ : Subgroup G} (h₁ : Z₁ ≤ Y) (h₂ : Z₂ ≤ Y) :
    mapL e (Z₁ ⊓ Z₂) = mapL e Z₁ ⊓ mapL e Z₂ := by
  rw [mapL, mapL, mapL, Subgroup.subgroupOf, Subgroup.subgroupOf, Subgroup.subgroupOf,
    Subgroup.comap_inf, Subgroup.map_inf _ _ _ (embedOf_injective e)]

private theorem mapL_Q {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    {Y : Subgroup G} {Y' : Subgroup G'} (e : Y ≃* Y') {ℓ : Subgroup G} (hℓ : ℓ ≤ Y) :
    mapL e (Q Y ℓ) = Q Y' (mapL e ℓ) := by
  have hC : Y ⊓ Subgroup.centralizer (ℓ : Set G) ≤ Y := inf_le_left
  have hJ : inSubgroup perfectResidual
      (Y ⊓ Subgroup.centralizer (ℓ : Set G)) ≤ Y :=
    (Subgroup.map_subtype_le _).trans inf_le_left
  have hQ : Q Y ℓ = (Y ⊓ Subgroup.centralizer (ℓ : Set G)) ⊓
      (Y ⊓ Subgroup.centralizer
        (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ : Set G)) : Set G)) := by
    rw [Q, ← inf_assoc,
      inf_eq_left.mpr (inf_le_left : Y ⊓ Subgroup.centralizer (ℓ : Set G) ≤ Y)]
  rw [hQ, mapL_inf e hC inf_le_left, mapL_inf_centralizer e hℓ,
    mapL_inf_centralizer e hJ, mapL_perfectResidual_inf e hℓ, Q, ← inf_assoc,
    inf_eq_left.mpr (inf_le_left : Y' ⊓ Subgroup.centralizer (mapL e ℓ : Set G') ≤ Y')]

private theorem isCyclic_Q_mapL_iff {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    {Y : Subgroup G} {Y' : Subgroup G'} (e : Y ≃* Y') {ℓ : Subgroup G} (hℓ : ℓ ≤ Y) :
    IsCyclic ↥(Q Y ℓ) ↔ IsCyclic ↥(Q Y' (mapL e ℓ)) := by
  have hZ : Q Y ℓ ≤ Y := inf_le_left.trans inf_le_left
  constructor
  · intro h
    haveI : IsCyclic ↥(Q Y ℓ) := h
    rw [← mapL_Q e hℓ]
    exact isCyclic_of_injective (mapLEquiv e hZ).symm.toMonoidHom
      (mapLEquiv e hZ).symm.injective
  · intro h
    rw [← mapL_Q e hℓ] at h
    haveI : IsCyclic ↥(mapL e (Q Y ℓ)) := h
    exact isCyclic_of_injective (mapLEquiv e hZ).toMonoidHom
      (mapLEquiv e hZ).injective

private theorem torusD_mem_SU {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}
    (hbe : Even b) (v : D8Mod 3 F) :
    (torusD v : GL (Fin 4) F) ∈ SU (unitaryInvolution F 2 b) 4 := by
  rw [torusD_apply]
  exact d8Vec_mem_SU (Or.inl rfl) d8Comb_four (unitaryInvolution F 2 b)
    (fun u => unitaryInvolution_rootsOfUnity hbe u) v

private theorem center_longSL_eq_bot {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}
    (hb2 : 2 ≤ b) (hF : Nat.card F = (2 ^ b) ^ 2) :
    Subgroup.center (longSL (unitaryInvolution F 2 b)) = ⊥ := by
  obtain ⟨eL⟩ := nonempty_longSL_mulEquiv (F := F) (b := b) (by omega) hF
  haveI : IsSimpleGroup (projSL 2 (GaloisField 2 b)) :=
    CFSG.RankThree.PartTwo.Sec21.isSimpleGroup_projSL_two hb2
  haveI : IsSimpleGroup (longSL (unitaryInvolution F 2 b)) := eL.isSimpleGroup
  exact CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.center_eq_bot_of_simple
    (inferInstance : IsSimpleGroup _)
    (CFSG.RankThree.PartTwo.Sec21.exists_not_commute_of_mulEquiv_projSL eL)

private theorem not_nonempty_derInf8_mulEquiv_projSL_two {X : Type} [Group X] [Finite X]
    {n : ℕ} (hn : 1 ≤ n) {J : Subgroup X} (hL : IsL2 (Bar2 J) n) :
    ¬ Nonempty (J ≃* projSL 2 (GaloisField 2 (2 * n))) := by
  rintro ⟨eJ⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2n : 2 ≤ 2 * n := by omega
  haveI : IsSimpleGroup (projSL 2 (GaloisField 2 (2 * n))) :=
    CFSG.RankThree.PartTwo.Sec21.isSimpleGroup_projSL_two h2n
  haveI : IsSimpleGroup J := eJ.isSimpleGroup
  have hna : ∃ a b : J, a * b ≠ b * a :=
    CFSG.RankThree.PartTwo.Sec21.exists_not_commute_of_mulEquiv_projSL eJ
  have hO : CFSG.pCore 2 ↥J = ⊥ :=
    CFSG.CGT.PushingUp.pCore_eq_bot_of_isSimpleGroup hna
  obtain ⟨eBar⟩ : Nonempty (Bar2 J ≃* projSL 2 (GaloisField 2 n)) :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.nonempty_projSL_of_lieModel hL
  let eJbar : Bar2 J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have e : projSL 2 (GaloisField 2 (2 * n)) ≃* projSL 2 (GaloisField 2 n) :=
    eJ.symm.trans (eJbar.symm.trans eBar)
  have hEq : 2 * n = n :=
    CFSG.RankThree.PartTwo.Sec21.eq_of_mulEquiv_projSL_two (by omega) hn e
  omega

private theorem isCyclic_Q_longSL {F : Type} [Field F] [Finite F]
    (σ : F ≃+* F) {a : F} {t : GL (Fin 4) F}
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![a, 1, 1, a⁻¹])
    (ha1 : a ≠ 1) (hainv : a ≠ a⁻¹) (hinv1 : (1 : F) ≠ a⁻¹)
    (hS : inSubgroup perfectResidual
      (SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F))) = longSL σ)
    (hcenter : Subgroup.center (longSL σ) = ⊥) :
    IsCyclic ↥(Q (SU σ 4) (Subgroup.zpowers t)) := by
  set C : Subgroup (GL (Fin 4) F) := SU σ 4 ⊓
    Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F)) with hC
  have hQle : Q (SU σ 4) (Subgroup.zpowers t) ≤ C := by
    rw [Q]
    exact inf_le_left
  let χ : C →* F :=
    { toFun := fun x => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0
      map_one' := by simp
      map_mul' := fun x y => by
        obtain ⟨h01, h02, h03, -⟩ := pattern_long_of_mem ht ha1 hainv hinv1 x.2.2
        simp [Matrix.mul_apply, Fin.sum_univ_four, h01, h02, h03] }
  let ψ : ↥(Q (SU σ 4) (Subgroup.zpowers t)) →* Fˣ :=
    χ.toHomUnits.comp (Subgroup.inclusion hQle)
  have hker : ∀ z : ↥(Q (SU σ 4) (Subgroup.zpowers t)), ψ z = 1 → z = 1 := by
    intro z hz
    have hz00 : (((z : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) 0 0 = 1 := by
      have h := congrArg (fun u : Fˣ => (u : F)) hz
      simpa [ψ, χ, MonoidHom.coe_toHomUnits, Subgroup.inclusion] using h
    have hzpat := pattern_long_of_mem ht ha1 hainv hinv1
      (x := (z : GL (Fin 4) F)) z.2.1.2
    have hzLong : (z : GL (Fin 4) F) ∈ longSL σ :=
      mem_longSL_of σ z.2.1.1 hzpat hz00
    have hzCen : (z : GL (Fin 4) F) ∈
        Subgroup.centralizer (longSL σ : Set (GL (Fin 4) F)) := by
      have h := z.2.2
      rwa [hS] at h
    have hcent : (⟨(z : GL (Fin 4) F), hzLong⟩ : longSL σ) ∈
        Subgroup.center (longSL σ) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hzCen (w : GL (Fin 4) F) w.2
    rw [hcenter, Subgroup.mem_bot] at hcent
    exact Subtype.ext (by simpa using congrArg Subtype.val hcent)
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : ψ (x * y⁻¹) = 1 := by
      rw [map_mul, hxy]
      simp
    have h2 : x * y⁻¹ = 1 := hker _ h1
    calc x = x * y⁻¹ * y := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = 1 * y := by rw [h2]
      _ = y := one_mul y
  exact isCyclic_of_injective ψ hinj

private structure TorusLineSetup (F : Type) [Field F] [Finite F] [CharP F 2] (b : ℕ) where
  ω : rootsOfUnity 3 F
  a : F
  hω : ω ≠ 1
  ha : a = ((ω : Fˣ) : F)
  ha1 : a ≠ 1
  hainv : a ≠ a⁻¹
  hinv1 : (1 : F) ≠ a⁻¹
  ht1 : ((torusD ((ω, 1) : D8Mod 3 F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = diagonal ![a, 1, 1, a⁻¹]
  ht3 : ((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = diagonal ![a, a, a⁻¹, a⁻¹]
  hw1 : weyl₁ ∈ SU (unitaryInvolution F 2 b) 4
  hw2 : weyl₂ ∈ SU (unitaryInvolution F 2 b) 4
  hσσ : ∀ c, unitaryInvolution F 2 b (unitaryInvolution F 2 b c) = c

private theorem exists_torusLineSetup {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}
    (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2) :
    Nonempty (TorusLineSetup F b) := by
  have hμ := card_rootsOfUnity_three hbe hF
  have : Nontrivial (rootsOfUnity 3 F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hμ]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : rootsOfUnity 3 F)
  set a : F := ((ω : Fˣ) : F) with ha
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha3; norm_num at ha3
  have hainv : a ≠ a⁻¹ := by
    intro h
    apply ha1
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ ha0
    calc a = a ^ 3 * a⁻¹ * a⁻¹ := by field_simp
      _ = 1 := by rw [ha3, one_mul, ← h, h2]
  have hinv1 : (1 : F) ≠ a⁻¹ := fun h => ha1 (by rw [← inv_inv a, ← h, inv_one])
  have hw1 : weyl₁ ∈ SU (unitaryInvolution F 2 b) 4 :=
    permGL_mem_SU (unitaryInvolution F 2 b) _ (by decide)
  have hw2 : weyl₂ ∈ SU (unitaryInvolution F 2 b) 4 :=
    permGL_mem_SU (unitaryInvolution F 2 b) _ (by decide)
  have ht1 : ((torusD ((ω, 1) : D8Mod 3 F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = diagonal ![a, 1, 1, a⁻¹] := by
    rw [coe_torusD]
    simp [ha]
  have ht3 : ((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = diagonal ![a, a, a⁻¹, a⁻¹] := by
    rw [coe_torusD]
    simp [ha]
  exact ⟨TorusLineSetup.mk ω a hω ha ha1 hainv hinv1 ht1 ht3 hw1 hw2
    (unitaryInvolution_involutive hF)⟩

private theorem torusLine_facts {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}
    (hb : 0 < b) (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2) (D : TorusLineSetup F b) :
    IsCyclic ↥(Q (SU (unitaryInvolution F 2 b) 4)
        (Subgroup.zpowers (torusD ((D.ω, 1) : D8Mod 3 F)))) ∧
      IsCyclic ↥(Q (SU (unitaryInvolution F 2 b) 4)
        (Subgroup.zpowers (torusD ((1, D.ω) : D8Mod 3 F)))) ∧
      Nonempty (inSubgroup perfectResidual (SU (unitaryInvolution F 2 b) 4 ⊓
          Subgroup.centralizer (Subgroup.zpowers
            (torusD ((D.ω, D.ω) : D8Mod 3 F)) : Set (GL (Fin 4) F))) ≃*
        projSL 2 (GaloisField 2 (2 * b))) ∧
      Nonempty (inSubgroup perfectResidual (SU (unitaryInvolution F 2 b) 4 ⊓
          Subgroup.centralizer (Subgroup.zpowers
            (torusD ((D.ω, D.ω⁻¹) : D8Mod 3 F)) : Set (GL (Fin 4) F))) ≃*
        projSL 2 (GaloisField 2 (2 * b))) := by
  let σ : F ≃+* F := unitaryInvolution F 2 b
  have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := hbe; omega
  obtain ⟨eL⟩ := nonempty_longSL_mulEquiv (F := F) (b := b) hb hF
  obtain ⟨eS⟩ := nonempty_shortSL_mulEquiv_galois σ hb hF
  have hperfL : ⁅longSL σ, longSL σ⁆ = longSL σ := Subgroup.isPerfect_iff.mp
    (CFSG.RankThree.PartTwo.Sec21.isPerfect_of_mulEquiv_projSL hb2 eL)
  have hperfS : ⁅shortSL σ, shortSL σ⁆ = shortSL σ := Subgroup.isPerfect_iff.mp
    (CFSG.RankThree.PartTwo.Sec21.isPerfect_of_mulEquiv_projSL (by omega) eS)
  have hS1 := perfectResidual_long σ D.ht1 D.ha1 D.hainv D.hinv1 hperfL
  have hS3 := perfectResidual_short σ D.hσσ D.ht3 D.hainv hperfS
  have hL2 : Subgroup.zpowers (torusD ((1, D.ω) : D8Mod 3 F)) =
      (Subgroup.zpowers (torusD ((D.ω, 1) : D8Mod 3 F))).map
        (MulAut.conj weyl₁).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact (conj_weyl₁ ((D.ω, 1) : D8Mod 3 F)).symm
  have hL4 : Subgroup.zpowers (torusD ((D.ω, D.ω⁻¹) : D8Mod 3 F)) =
      (Subgroup.zpowers (torusD ((D.ω, D.ω) : D8Mod 3 F))).map
        (MulAut.conj weyl₂).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact (conj_weyl₂ ((D.ω, D.ω) : D8Mod 3 F)).symm
  have hℓ1 : Subgroup.zpowers (torusD ((D.ω, 1) : D8Mod 3 F)) ≤ SU σ 4 :=
    Subgroup.zpowers_le.mpr (torusD_mem_SU (b := b) hbe (D.ω, 1))
  have hQ1 : IsCyclic ↥(Q (SU σ 4)
      (Subgroup.zpowers (torusD ((D.ω, 1) : D8Mod 3 F)))) :=
    isCyclic_Q_longSL σ D.ht1 D.ha1 D.hainv D.hinv1 hS1 (center_longSL_eq_bot hb2 hF)
  have hmap2 : mapL (MulAut.conj (⟨weyl₁, D.hw1⟩ : ↥(SU σ 4)))
      (Subgroup.zpowers (torusD ((D.ω, 1) : D8Mod 3 F))) =
      Subgroup.zpowers (torusD ((1, D.ω) : D8Mod 3 F)) := by
    rw [mapL_conj (⟨weyl₁, D.hw1⟩ : ↥(SU σ 4)) hℓ1]
    exact hL2.symm
  have hQ2 : IsCyclic ↥(Q (SU σ 4)
      (Subgroup.zpowers (torusD ((1, D.ω) : D8Mod 3 F)))) := by
    rw [← hmap2]
    exact (isCyclic_Q_mapL_iff (MulAut.conj (⟨weyl₁, D.hw1⟩ : ↥(SU σ 4))) hℓ1).1 hQ1
  have hshort3 : inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((D.ω, D.ω) : D8Mod 3 F)) : Set (GL (Fin 4) F))) ≃*
      projSL 2 (GaloisField 2 (2 * b)) := by
    rw [hS3]
    exact eS
  have hshort4 : inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((D.ω, D.ω⁻¹) : D8Mod 3 F)) : Set (GL (Fin 4) F))) ≃*
      projSL 2 (GaloisField 2 (2 * b)) := by
    rw [hL4, perfectResidual_conj D.hw2, hS3]
    exact ((shortSL σ).equivMapOfInjective _ (MulAut.conj weyl₂).injective).symm.trans eS
  exact ⟨hQ1, hQ2, ⟨hshort3⟩, ⟨hshort4⟩⟩

private theorem isCyclic_Q_SU_of_conj_into_torus {F : Type} [Field F] [Finite F] [CharP F 2]
    {b : ℕ} (hb : 0 < b) (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2)
    {ℓ : Subgroup (GL (Fin 4) F)}
    (hℓ : ℓ ≤ SU (unitaryInvolution F 2 b) 4) (h3 : Nat.card ℓ = 3)
    {g : ↥(SU (unitaryInvolution F 2 b) 4)}
    (hT : mapL (MulAut.conj g) ℓ ≤ d8Tor 3 F 4)
    {X : Type} [Group X] {J_X : Subgroup X}
    (hneg : ¬ Nonempty (J_X ≃* projSL 2 (GaloisField 2 (2 * b))))
    (hJX : J_X ≃* inSubgroup perfectResidual
      (SU (unitaryInvolution F 2 b) 4 ⊓
        Subgroup.centralizer (ℓ : Set (GL (Fin 4) F)))) :
    IsCyclic ↥(Q (SU (unitaryInvolution F 2 b) 4) ℓ) := by
  obtain ⟨D⟩ := exists_torusLineSetup (b := b) hbe hF
  obtain ⟨hQ1, hQ2, ⟨hshort3⟩, ⟨hshort4⟩⟩ := torusLine_facts hb hbe hF D
  have hμ := card_rootsOfUnity_three hbe hF
  have h3map : Nat.card (mapL (MulAut.conj g) ℓ) = 3 := by
    rw [card_mapL (MulAut.conj g) hℓ, h3]
  have hQmap : IsCyclic ↥(Q (SU (unitaryInvolution F 2 b) 4)
      (mapL (MulAut.conj g) ℓ)) := by
    rcases line_cases hμ D.hω hT h3map with h1 | h2 | h3' | h4
    · rw [h1]
      exact hQ1
    · rw [h2]
      exact hQ2
    · exfalso
      apply hneg
      exact ⟨hJX.trans ((perfectResidualEquiv (MulAut.conj g) hℓ).trans
        (h3'.symm ▸ hshort3))⟩
    · exfalso
      apply hneg
      exact ⟨hJX.trans ((perfectResidualEquiv (MulAut.conj g) hℓ).trans
        (h4.symm ▸ hshort4))⟩
  exact (isCyclic_Q_mapL_iff (MulAut.conj g) hℓ).2 hQmap

theorem isCyclic_centralizer_inf_centralizer_derInf8_of_isL2 {X : Type} [Group X] [Finite X]
    {n : ℕ} (hX : IsU4 X n) (hn : Even n) {A : Subgroup X} (hA : Nat.card A = 3)
    (hL : IsL2 (Bar2 (F08.DerInf8 (⊤ ⊓ centralizer (A : Set X)))) n) :
    IsCyclic ↥(centralizer (A : Set X) ⊓
      centralizer (F08.DerInf8 (⊤ ⊓ centralizer (A : Set X)) : Set X)) := by
  have hn1 : 1 ≤ n := (hX.admissible).2.1
  have hn0 : 2 ≤ n := by obtain ⟨k, hk⟩ := hn; omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 (2 * n)
  let σ : F ≃+* F := unitaryInvolution F 2 n
  have hF : Nat.card F = (2 ^ n) ^ 2 := card_galoisField_two_mul n (by omega)
  obtain ⟨e₀⟩ := CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.nonempty_projSU_of_lieModel hX
  obtain ⟨e₁⟩ := nonempty_projSU_mulEquiv_SU n (by omega)
  let e : (⊤ : Subgroup X) ≃* SU σ 4 := Subgroup.topEquiv.trans (e₀.trans e₁)
  let ℓ : Subgroup (GL (Fin 4) F) := mapL e A
  have hℓSU : ℓ ≤ SU σ 4 := mapL_le e A
  have h3ℓ : Nat.card ℓ = 3 := by
    change Nat.card (mapL e A) = 3
    rw [card_mapL e le_top, hA]
  have hneg : ¬ Nonempty (F08.DerInf8 (⊤ ⊓ centralizer (A : Set X)) ≃*
      projSL 2 (GaloisField 2 (2 * n))) :=
    not_nonempty_derInf8_mulEquiv_projSL_two hn1 hL
  have hJX : F08.DerInf8 (⊤ ⊓ centralizer (A : Set X)) ≃*
      inSubgroup perfectResidual
        (SU σ 4 ⊓ Subgroup.centralizer (ℓ : Set (GL (Fin 4) F))) :=
    perfectResidualEquiv e le_top
  have hX3 : ∀ x ∈ ℓ.subgroupOf (SU σ 4), x ^ 3 = 1 := by
    intro x hx
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := pow_card_eq_one' (G := ℓ) (x := ⟨(x : GL (Fin 4) F), hx⟩)
    rw [h3ℓ] at h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_su (n := 4) (Or.inl rfl) d8Comb_four hF
    Nat.prime_three (by norm_num)
    (CFSG.RankThree.PartTwo.Sec21.three_dvd_two_pow_sub_one hn)
    (ℓ.subgroupOf (SU σ 4)) hX3
  have hT : mapL (MulAut.conj g) ℓ ≤ d8Tor 3 F 4 := by
    rw [mapL_conj g hℓSU]
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨x, hℓSU hx⟩ hx
  have hQ : IsCyclic ↥(Q (SU σ 4) ℓ) :=
    isCyclic_Q_SU_of_conj_into_torus (b := n) (by omega) hn hF hℓSU h3ℓ hT hneg hJX
  have hQtop : IsCyclic ↥(Q (⊤ : Subgroup X) A) :=
    (isCyclic_Q_mapL_iff e le_top).2 hQ
  have htarget : Q (⊤ : Subgroup X) A =
      centralizer (A : Set X) ⊓ centralizer
        (F08.DerInf8 (⊤ ⊓ centralizer (A : Set X)) : Set X) := by
    rw [Q, top_inf_eq]
    rfl
  rwa [htarget] at hQtop

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
