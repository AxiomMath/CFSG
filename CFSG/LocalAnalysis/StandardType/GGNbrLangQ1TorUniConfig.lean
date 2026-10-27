module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniTor
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces


private lemma l02qu7_E_isElemAbelian
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    {L : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hAb : IsElemAbelian p Bs) {R : Type} [Group R] [Finite R]
    (θ : L ⧸ Subgroup.center L ≃* R) :
    IsElemAbelian p ((ggGamma L hN).range.map (ggInducedAut θ)) := by
  let hcomp : Bs →* MulAut R := (ggInducedAut θ).comp (ggGamma L hN)
  have hrange : hcomp.range = (ggGamma L hN).range.map (ggInducedAut θ) := by
    ext a
    simp only [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨ggGamma L hN b, ⟨b, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, rfl⟩
  rw [← hrange]
  refine isElemAbelian_range (fun a b => hAb.1.is_comm.comm a b)
    (fun b => Subtype.ext (by simpa using hAb.2 b b.2)) hcomp

private lemma l02qu7_E_subset_I
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    {L : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : L ⧸ Subgroup.center L ≃* R)
    (hact : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∀ a ∈ (ggGamma L hN).range.map (ggInducedAut θ), a ∈ I := by
  intro a ha
  let hcomp : Bs →* MulAut R := (ggInducedAut θ).comp (ggGamma L hN)
  have hrange : hcomp.range = (ggGamma L hN).range.map (ggInducedAut θ) := by
    ext a
    simp only [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨ggGamma L hN b, ⟨b, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, rfl⟩
  rw [← hrange] at ha
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp ha
  obtain ⟨φ, hφI, hφ⟩ := hact c⁻¹ (inv_mem c.2)
  have heq : hcomp c = φ := by
    simp only [hcomp, MonoidHom.comp_apply]
    ext x
    obtain ⟨y, rfl⟩ := θ.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    have hrel : ((ggGamma L hN c l : L) : G) = (c⁻¹)⁻¹ * (l : G) * c⁻¹ := by
      rw [ggGamma_coe]
      simp [Subgroup.coe_inv]
    have h1 := hφ l (ggGamma L hN c l) hrel
    rw [ggInducedAut_apply]
    exact h1.symm
  rw [hc] at heq
  rwa [heq]

private lemma l02qu7_rank_bound
    {G : Type} [Group G] [Finite G] {p d : ℕ} {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBle : B ≤ Bs) (hp : p.Prime) (hS : LargeEvenSStar p B x L) (hL : commutator L = ⊤)
    {R : Type} [Group R] [Finite R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hlift : GGTorusLift p (ggUnitaryTorusRank p d) R) :
    p ^ (ggUnitaryTorusRank p d) ≤
      Nat.card ((ggGamma L hN).range.map (ggInducedAut θ)) := by
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBle.trans hN
  have hle : (ggBeta L θ hBN).range ≤ (ggGamma L hN).range.map (ggInducedAut θ) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggGamma L hBN b, ⟨Subgroup.inclusion hBle b, rfl⟩, rfl⟩
  exact (pow_le_card_range_ggBeta hp hS hL θ hBN hlift).trans
    (Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))

private lemma l02qu7_p3_bound
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBle : B ≤ Bs) (hS : LargeEvenSStar p B x L) (hL : commutator L = ⊤)
    (hβ : p ∈ LargeEvenBeta 4 G) {R : Type} [Group R] [Finite R]
    (θ : L ⧸ Subgroup.center L ≃* R) :
    p ^ 3 ≤ Nat.card ((ggGamma L hN).range.map (ggInducedAut θ)) := by
  have hp : p.Prime := hβ.1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBle.trans hN
  have hle : (ggBeta L θ hBN).range ≤ (ggGamma L hN).range.map (ggInducedAut θ) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggGamma L hBN b, ⟨Subgroup.inclusion hBle b, rfl⟩, rfl⟩
  have h4 : p ^ 4 ≤ Nat.card B := pow_four_le_card_of_bmax hp hS.1 hβ.2.2.2
  have hc : Nat.card (ggBeta L θ hBN).range * p = Nat.card B :=
    card_range_ggBeta_mul L θ hp hS hL hBN
  have h3 : p ^ 3 ≤ Nat.card (ggBeta L θ hBN).range := by
    rw [← hc, pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 hp.pos
  exact h3.trans
    (Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))

theorem q1TorUni_config :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
      GGConfig p B Bs x L D J →
      GGMarkingAll (K := ↥L) (fun lab R _ I _ θ =>
        UnitaryTorsion p lab → ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
          (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
          ToralUni R ((ggGamma L hN).range.map (ggInducedAut θ))) := by
  intro G _ _ p B Bs x L D J hcfg
  unfold GGMarkingAll
  intro P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  refine ⟨hperf, lab, hlab, ?_⟩
  by_cases htag : lab.tag = .twA
  · unfold LargeEvenRawDatumLegacy at hraw ⊢
    rw [htag] at hraw ⊢
    obtain ⟨K, fieldInst, finiteInst, hK, hQ⟩ := hraw
    refine ⟨K, fieldInst, finiteInst, hK, ?_⟩
    obtain ⟨hs, hna, θ, hPθ⟩ := hQ
    refine ⟨hs, hna, θ, hPθ, ?_⟩
    intro hS hN hact
    unfold LargeEvenInLambda2 at hlab
    rw [htag] at hlab
    obtain ⟨-, -, -, -, -, hβ, hSstar, -⟩ := hcfg.1
    have hp : p.Prime := hβ.1
    have hBle : B ≤ Bs := hcfg.2.1.1
    have hAb : IsElemAbelian p Bs := hcfg.2.1.2.1
    have hd : 3 ≤ lab.rank + 1 := by have := hlab.2.1; omega
    have hpq : p ∣ 2 ^ lab.n + 1 := hS.2.1.trans (Nat.gcd_dvd_right _ _)
    have hm : 1 ≤ lab.n := hlab.1
    have hdq : ¬((lab.rank + 1) = 3 ∧ 2 ^ lab.n = 2) := by
      rintro ⟨h1, h2⟩
      have hr2 : lab.rank = 2 := by omega
      have hn2 : 2 ≤ lab.n := hlab.2.2 hr2
      have h4 : 4 ≤ 2 ^ lab.n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    have hdq' : (lab.rank + 1, 2 ^ lab.n) ≠ (3, 2) := by
      rintro h
      exact hdq ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    have hd63 : ¬((lab.rank + 1) = 6 ∧ p = 3) := by
      rintro ⟨h1, h2⟩
      exact hS.2.2 ⟨by omega, h2⟩
    have hlift : GGTorusLift p (ggUnitaryTorusRank p (lab.rank + 1))
        (LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n))) :=
      ggTorusLift_unitary (d := lab.rank + 1) (n := lab.n) (K := K) hK hm hd hdq' hp hpq
    have hE : IsElemAbelian p ((ggGamma L hN).range.map (ggInducedAut θ)) :=
      l02qu7_E_isElemAbelian hN hAb θ
    have hEI : ∀ a ∈ (ggGamma L hN).range.map (ggInducedAut θ),
        a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
          (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n)) :=
      l02qu7_E_subset_I (p := p) hN θ hact
    have hpd : p ∣ lab.rank + 1 := hS.2.1.trans (Nat.gcd_dvd_left _ _)
    have hr : p ^ ((lab.rank + 1) - 3) ≤
        Nat.card ((ggGamma L hN).range.map (ggInducedAut θ)) := by
      have h := l02qu7_rank_bound hN hBle hp hSstar hperf θ hlift
      simpa [ggUnitaryTorusRank, hpd] using h
    have h3 : p ^ 3 ≤ Nat.card ((ggGamma L hN).range.map (ggInducedAut θ)) :=
      l02qu7_p3_bound hN hBle hSstar hperf hβ θ
    exact toralUni_of_rank (d := lab.rank + 1) (m := lab.n) (p := p)
      hd hm hdq hK hp hpq hd63 hE hEI hr h3
  · refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw
    obtain ⟨hs, hna, θ, hPθ⟩ := hh
    refine ⟨hs, hna, θ, hPθ, ?_⟩
    intro hS hN hact
    exact absurd hS.1 htag

end CFSG.StandardType
