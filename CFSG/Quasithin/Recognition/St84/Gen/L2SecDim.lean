module

public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LMod

import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.Quasithin.Background.Harris.OrdinaryProofs.FrobDim
import CFSG.Quasithin.Background.Harris.L2.Numerics
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDescent
public import CFSG.Timmesfeld.RankOne.SL2
import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyAlt

public section

namespace CFSG.Quasithin.St84

open CFSG.GH74.QTGen4.DSGen4
open CFSG.Quasithin.H13.NFa2
open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem div_gcd_le_card_of_image_add_mod {m d : ℕ} {J : Finset ℕ} (hm : 1 ≤ m) (hJ : J.Nonempty)
    (hJm : ∀ i ∈ J, i < m) (hd : J.image (fun i => (i + d) % m) = J) :
    m / Nat.gcd m d ≤ J.card := by
  have h := CFSG.Quasithin.G11.Harris.L2.le_card_mul_gcd (n := m) (d := d) (by omega) hJ hJm hd
  exact Nat.div_le_of_le_mul (by rwa [Nat.mul_comm] at h)

theorem two_mul_le_mul_two_pow_of_image_add_mod {m d : ℕ} {J : Finset ℕ} (hm : 1 ≤ m)
    (hd1 : 1 ≤ d) (hJ : J.Nonempty) (hJm : ∀ i ∈ J, i < m)
    (hd : J.image (fun i => (i + d) % m) = J) :
    2 * m ≤ d * 2 ^ J.card := by
  have hdiv := div_gcd_le_card_of_image_add_mod hm hJ hJm hd
  set g := Nat.gcd m d with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left d (by omega)
  have hmul : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m d)
  have ht1 : 1 ≤ m / g := by
    rcases Nat.eq_zero_or_pos (m / g) with h | h
    · rw [h, Nat.mul_zero] at hmul
      omega
    · exact h
  have hgd : g ≤ d := Nat.le_of_dvd hd1 (Nat.gcd_dvd_right m d)
  have h2t : 2 * (m / g) ≤ 2 ^ (m / g) :=
    CFSG.Quasithin.Background.Harris.OrdinaryProofs.two_mul_le_two_pow ht1
  have hpow : 2 ^ (m / g) ≤ 2 ^ J.card := Nat.pow_le_pow_right (by norm_num) hdiv
  have h2m : 2 * m = 2 * (g * (m / g)) := by rw [hmul]
  calc 2 * m = 2 * (g * (m / g)) := h2m
    _ = g * (2 * (m / g)) := by ring
    _ ≤ g * 2 ^ (m / g) := Nat.mul_le_mul_left g h2t
    _ ≤ d * 2 ^ J.card := Nat.mul_le_mul hgd hpow

theorem eq_three_of_mul_two_pow_eq {m d : ℕ} {J : Finset ℕ} (hm : 2 ≤ m) (hd1 : 1 ≤ d)
    (hJ : J.Nonempty) (hJm : ∀ i ∈ J, i < m) (hd : J.image (fun i => (i + d) % m) = J)
    (h : d * 2 ^ J.card = 2 * m + 2) : m = 3 := by
  have hdim : d * 2 ^ J.card ≤ 2 * m + 2 := by omega
  rcases CFSG.Quasithin.G11.Harris.L2.l2_numerics hm hd1 hJ hJm hd hdim with
    ⟨h1, hdm⟩ | ⟨h2, hm2d⟩ | ⟨-, hm3, -⟩
  · rw [h1] at h
    omega
  · rw [h2] at h
    omega
  · exact hm3

theorem pCore_le_secRep_ker {V Z L : Subgroup G} {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (s : SecRep L Z V W) (hsecHyp : SecHyp L Z V)
    (hChief : IsChiefPair L Z V) : CFSG.pCore 2 ↥L ≤ s.ρ.ker := by
  intro p hp
  rw [MonoidHom.mem_ker]
  have hPgrp : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hPle : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hPn : ∀ x ∈ L, ∀ q ∈ CFSG.Open.pCoreOf 2 L,
      x * q * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    intro x hx q hq
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hx) q).mp hq
  exact SecRep.ρ_eq_one_of_normal_pgroup hChief hsecHyp s hPle hPgrp hPn p
    ((CFSG.mem_openPCoreOf_iff p).mpr hp)

theorem exists_irreducible_SL2_rep {V Z L : Subgroup G} {m : ℕ}
    (hquot : IsL2Quot m (oTwoQuot ↥L)) (hsecHyp : SecHyp L Z V)
    (hChief : IsChiefPair L Z V) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (s : SecRep L Z V W) (hkerP : CFSG.pCore 2 ↥L ≤ s.ρ.ker) (l₀' : ↥L) (v₀' : ↥V)
    (hfix : s.ρ l₀' (s.cl v₀') ≠ s.cl v₀') :
    ∃ ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)) W,
      ρ.IsIrreducible ∧ (∃ g, ρ g ≠ 1) ∧
        ∃ ψ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m),
          Function.Surjective ψ ∧ ∀ l, ρ (ψ l) = (s.ρ l).toLinearMap := by
  classical
  let q : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  obtain ⟨e⟩ := hquot
  let eSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m) :=
    CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 m)
  let bar : oTwoQuot ↥L →* (W ≃ₗ[ZMod 2] W) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) s.ρ hkerP
  let Φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m) →* (W ≃ₗ[ZMod 2] W) :=
    bar.comp (e.symm.toMonoidHom.comp eSL.symm.toMonoidHom)
  let ρSL : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)) W :=
    { toFun := fun g => (Φ g).toLinearMap
      map_one' := by rw [map_one]; rfl
      map_mul' := fun g h => by rw [map_mul]; rfl }
  have hΦ_mk : ∀ l : ↥L, Φ (eSL (e (q l))) = s.ρ l := by
    intro l
    simp [Φ, bar, q, QuotientGroup.lift_mk']
  have hρSL_mk : ∀ l : ↥L, ρSL (eSL (e (q l))) = (s.ρ l).toLinearMap := by
    intro l
    rw [show ρSL (eSL (e (q l))) = (Φ (eSL (e (q l)))).toLinearMap from rfl, hΦ_mk l]
  haveI : Nontrivial W := ⟨s.ρ l₀' (s.cl v₀'), s.cl v₀', hfix⟩
  have hirrSL : ρSL.IsIrreducible := by
    haveI : Nontrivial (Subrepresentation ρSL) := by
      refine ⟨⊥, ⊤, ?_⟩
      intro h
      exact bot_ne_top (α := Submodule (ZMod 2) W)
        (congrArg Subrepresentation.toSubmodule h)
    refine { eq_bot_or_eq_top := fun U => ?_ }
    have hS : ∀ l : ↥L, ∀ w ∈ U.toSubmodule, s.ρ l w ∈ U.toSubmodule := by
      intro l w hw
      have h1 := U.apply_mem_toSubmodule (eSL (e (q l))) hw
      rwa [hρSL_mk l] at h1
    rcases SecRep.irreducible hChief hsecHyp s U.toSubmodule hS with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  have hneρ : ρSL (eSL (e (q l₀'))) ≠ 1 := by
    intro h
    have hbar : s.ρ l₀' = 1 := by
      refine LinearEquiv.ext fun w => ?_
      have h1 : (s.ρ l₀').toLinearMap w = w := by
        rw [← hρSL_mk l₀']
        exact LinearMap.congr_fun h w
      simpa using h1
    apply hfix
    rw [hbar]
    rfl
  refine ⟨ρSL, hirrSL, ⟨eSL (e (q l₀')), hneρ⟩,
    eSL.toMonoidHom.comp (e.toMonoidHom.comp q), ?_, hρSL_mk⟩
  exact eSL.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))

private theorem exists_relIndex_eq_of_secRep {V Z L : Subgroup G} {m : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (hm : 1 ≤ m) (hVZ : Z ≤ V)
    (hnormalZV : V ≤ Subgroup.normalizer (Z : Set G)) (s : SecRep L Z V W)
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)) W)
    [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1) :
    ∃ (d : ℕ) (J : Finset ℕ), 1 ≤ d ∧ J.Nonempty ∧ (∀ i ∈ J, i < m) ∧
      J.image (fun i => (i + d) % m) = J ∧ Z.relIndex V = 2 ^ (d * 2 ^ J.card) := by
  classical
  let _ : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hk : Fintype.card (GaloisField 2 m) = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 m (by omega)]
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    binary_SL2_irreducible_Frobenius_descent hm hk ρ hnt
  let b : Module.Basis (Fin (Module.finrank (EndRing ρ) W)) (EndRing ρ) W :=
    Module.finBasis (EndRing ρ) W
  obtain ⟨_, _, _, _, _, _, J, hJne, hJm, _, hshift, hdim⟩ := hdesc b
  refine ⟨d, J, hd1, hJne, hJm, hshift, ?_⟩
  have hWcard : Nat.card W = 2 ^ (d * 2 ^ J.card) := by
    rw [Module.natCard_eq_pow_finrank (K := EndRing ρ) (V := W), hDcard, hdim, pow_mul]
  have hker : s.cls.ker = Z.subgroupOf V := by
    ext n
    rw [MonoidHom.mem_ker, s.ker n, Subgroup.mem_subgroupOf]
  haveI hNZV : (Z.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVZ).mpr hnormalZV
  have hquotW : Nat.card (↥V ⧸ Z.subgroupOf V) = Nat.card W := by
    have eW : (↥V ⧸ Z.subgroupOf V) ≃* Multiplicative W :=
      (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective s.cls s.surj)
    exact (Nat.card_congr eW.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
  show (Z.subgroupOf V).index = 2 ^ (d * 2 ^ J.card)
  rw [Subgroup.index_eq_card, hquotW, hWcard]

theorem exists_relIndex_eq_of_irreducible {V Z L : Subgroup G} {m : ℕ} (hm : 1 ≤ m)
    (hquot : IsL2Quot m (oTwoQuot ↥L)) (hVZ : Z ≤ V) (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hirr : ∀ W : Subgroup G, Z ≤ W → W ≤ V → L ≤ Subgroup.normalizer (W : Set G) →
      W = Z ∨ W = V)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z) :
    ∃ (d : ℕ) (J : Finset ℕ), 1 ≤ d ∧ J.Nonempty ∧ (∀ i ∈ J, i < m) ∧
      J.image (fun i => (i + d) % m) = J ∧ Z.relIndex V = 2 ^ (d * 2 ^ J.card) := by
  classical
  have hZV : Z < V := by
    refine lt_of_le_of_ne hVZ ?_
    intro heq
    obtain ⟨l, hl, v, hv, hne⟩ := hnt
    apply hne
    rw [heq]
    have hconj : l * v * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp (hL hl)).1 v).mp hv
    exact V.mul_mem hconj (V.inv_mem hv)
  obtain ⟨l₀, hl₀, v₀, hv₀, hne₀⟩ := hnt
  let l₀' : ↥L := ⟨l₀, hl₀⟩
  let v₀' : ↥V := ⟨v₀, hv₀⟩
  have hnormalZV : V ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_mono le_rfl hVZ).trans hsec.2.1)
  have hsecHyp : SecHyp L Z V :=
    { le := hVZ
      norm₀ := hL.trans inf_le_right
      norm₁ := hL.trans inf_le_left
      normal := hnormalZV
      comm := fun a ha b hb => hsec.2.1 (Subgroup.commutator_mem_commutator ha hb)
      sq := fun a ha => by simpa [pow_two] using hsec.2.2 a ha }
  have hChief : IsChiefPair L Z V :=
    { lt := hZV
      norm₀ := hL.trans inf_le_right
      norm₁ := hL.trans inf_le_left
      normal := hnormalZV
      min := fun N hZN hNV hLN => hirr N hZN hNV hLN }
  obtain ⟨W, hWadd, hWmod, hWfin, ⟨s⟩⟩ := exists_secRep hsecHyp
  letI : AddCommGroup W := hWadd
  letI : Module (ZMod 2) W := hWmod
  letI : Finite W := hWfin
  have hfix : s.ρ l₀' (s.cl v₀') ≠ s.cl v₀' := by
    intro h
    exact hne₀ ((SecRep.fix_iff hsecHyp s l₀' v₀').mp h)
  have hkerP : CFSG.pCore 2 ↥L ≤ s.ρ.ker := pCore_le_secRep_ker s hsecHyp hChief
  obtain ⟨ρSL, hirrSL, hntSL, -⟩ :=
    exists_irreducible_SL2_rep hquot hsecHyp hChief s hkerP l₀' v₀' hfix
  letI : Fact ρSL.IsIrreducible := ⟨hirrSL⟩
  exact exists_relIndex_eq_of_secRep hm hVZ hnormalZV s ρSL hntSL

theorem two_pow_le_relIndex_of_irreducible {V Z L : Subgroup G} {m : ℕ} (hm : 1 ≤ m)
    (hquot : IsL2Quot m (oTwoQuot ↥L)) (hVZ : Z ≤ V) (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hirr : ∀ W : Subgroup G, Z ≤ W → W ≤ V → L ≤ Subgroup.normalizer (W : Set G) →
      W = Z ∨ W = V)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z) :
    2 ^ (2 * m) ≤ Z.relIndex V := by
  obtain ⟨d, J, hd1, hJne, hJm, hshift, hrel⟩ :=
    exists_relIndex_eq_of_irreducible hm hquot hVZ hsec hL hirr hnt
  have h2 : 2 * m ≤ d * 2 ^ J.card :=
    two_mul_le_mul_two_pow_of_image_add_mod hm hd1 hJne hJm hshift
  rw [hrel]
  exact Nat.pow_le_pow_right (by norm_num) h2

theorem eq_three_of_irreducible_of_relIndex {V Z L : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (hquot : IsL2Quot m (oTwoQuot ↥L)) (hVZ : Z ≤ V) (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hirr : ∀ W : Subgroup G, Z ≤ W → W ≤ V → L ≤ Subgroup.normalizer (W : Set G) →
      W = Z ∨ W = V)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z)
    (hcard : Z.relIndex V = 2 ^ (2 * m + 2)) : m = 3 := by
  obtain ⟨d, J, hd1, hJne, hJm, hshift, hrel⟩ :=
    exists_relIndex_eq_of_irreducible (by omega) hquot hVZ hsec hL hirr hnt
  have hpow : 2 ^ (d * 2 ^ J.card) = 2 ^ (2 * m + 2) := by
    rw [← hrel, hcard]
  have h : d * 2 ^ J.card = 2 * m + 2 := Nat.pow_right_injective le_rfl hpow
  exact eq_three_of_mul_two_pow_eq hm hd1 hJne hJm hshift h

end CFSG.Quasithin.St84
