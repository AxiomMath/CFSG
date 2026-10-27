module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent
public import CFSG.LieType.HighestRoot.CentG2Main
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcInner
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcRed
import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofBlocks

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.HighestRoot
  CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
open scoped MatrixGroups

namespace Item211Res5Proof

section G2


variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def g2RhoA : SL(2, K) →* adjointGroup .G2 K :=
  (simpleRootSL2 .G2 K g2ia).codRestrict (adjointGroup .G2 K)
    (fun A => simpleRootSL2_mem_adjointGroup g2ia A)

variable (K) in
@[expose] noncomputable def g2RhoV : SL(2, K) →* adjointGroup .G2 K :=
  (rhoV K).codRestrict (adjointGroup .G2 K) (fun A => by
    rw [rhoV_apply]
    exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ K _)
      (simpleRootSL2_mem_adjointGroup _ _)) (inv_mem (canonicalRep_mem_adjointGroup _ K _)))

theorem coe_g2RhoA (A : SL(2, K)) : (g2RhoA K A : ModGL .G2 K) = simpleRootSL2 .G2 K g2ia A :=
  rfl

theorem coe_g2RhoV (A : SL(2, K)) : (g2RhoV K A : ModGL .G2 K) = rhoV K A :=
  rfl

theorem g2RhoA_injective : Function.Injective (g2RhoA K) := fun _ _ h =>
  simpleRootSL2_injective_g2 g2ia (congrArg Subtype.val h)

theorem g2RhoV_injective : Function.Injective (g2RhoV K) := fun _ _ h =>
  rhoV_injective (congrArg Subtype.val h)

theorem mem_range_g2RhoA_iff {x : adjointGroup .G2 K} : x ∈ (g2RhoA K).range ↔ x ∈ g2LongSL2 K := by
  rw [mem_g2LongSL2_iff]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A, rfl⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, Subtype.ext hA⟩

theorem mem_range_g2RhoV_iff {x : adjointGroup .G2 K} :
    x ∈ (g2RhoV K).range ↔ x ∈ g2ShortSL2 K := by
  rw [mem_g2ShortSL2_iff]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A, rfl⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, Subtype.ext hA⟩

theorem g2RhoA_neg_one : g2RhoA K (-1) = g2z := by
  apply Subtype.ext
  rw [coe_g2RhoA, neg_one_eq_HSL_neg_one, show g2ia = g2l from rfl, simpleRootSL2_HSL,
    torusElt_neg_one_eq]
  rfl

theorem g2RhoV_neg_one : g2RhoV K (-1) = g2z := by
  apply Subtype.ext
  rw [coe_g2RhoV, neg_one_eq_HSL_neg_one, rhoV_HSL]
  change rootDiagUnit .G2 (Pi.mulSingle g2ir (-1)) = rootDiagUnit .G2 (signTuple .G2 K g2l)
  congr 1
  funext j
  rcases fin_G2_cases j with rfl | rfl
  · rw [Pi.mulSingle_eq_of_ne (by decide)]
    change (1 : Kˣ) = (-1 : Kˣ) ^ Tag.G2.cartan g2l g2l
    rw [show Tag.G2.cartan g2l g2l = 2 by decide]
    exact (show Even (2 : ℤ) by decide).neg_one_zpow.symm
  · rw [Pi.mulSingle_eq_same]
    change (-1 : Kˣ) = (-1 : Kˣ) ^ Tag.G2.cartan g2l g2ir
    rw [show Tag.G2.cartan g2l g2ir = -1 by decide]
    exact (show Odd (-1 : ℤ) by decide).neg_one_zpow.symm

theorem g2RhoA_comm (a b : SL(2, K)) : g2RhoA K a * g2RhoV K b = g2RhoV K b * g2RhoA K a :=
  (g2Short_commute_g2Long (mem_range_g2RhoV_iff.mp ⟨b, rfl⟩)
    (mem_range_g2RhoA_iff.mp ⟨a, rfl⟩)).symm

theorem coe_mem_toralCentralizer {x : adjointGroup .G2 K} (hx : x * g2z = g2z * x) :
    (x : ModGL .G2 K) ∈ toralCentralizer .G2 K (signTuple .G2 K g2l) :=
  (g2_mem_toralCentralizer_iff rfl x).mpr (Subgroup.mem_centralizer_singleton_iff.mpr hx)

theorem conj_coe_mem_pair (hK : ringChar K ≠ 2) {γ : Fin (Tag.rank .G2) → ℤ}
    (hγ : γ = g2e0 ∨ γ = g2δ) {h y : adjointGroup .G2 K} (hh : h * g2z = g2z * h)
    (hy : (y : ModGL .G2 K) ∈ rootSubgroup .G2 K γ ⊔ rootSubgroup .G2 K (-γ)) :
    ((h * y * h⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈
      rootSubgroup .G2 K γ ⊔ rootSubgroup .G2 K (-γ) := by
  have hN := g2_toralCentralizer_le_normalizer hK hγ (coe_mem_toralCentralizer hh)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact (Subgroup.mem_normalizer_iff.mp hN _).mp hy

theorem sq_mem_pairs_of_mem_torus {t : ModGL .G2 K} (ht : t ∈ torusGroup .G2 K) :
    t ^ 2 ∈ (rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)) ⊔
      (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)) := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have e : rootDiagUnit .G2 l ^ 2 = simpleRootSL2 .G2 K g2ia (HSL (l g2ia)) *
      rhoV K (HSL (l g2ia * l g2ir ^ 2)) := by
    rw [rhoA_HSL, rhoV_HSL, ← rootDiagUnit_mul, sq, ← rootDiagUnit_mul]
    congr 1
    funext j
    rcases fin_G2_cases j with rfl | rfl
    · have c0 : Tag.G2.cartan g2ia g2ia = 2 := by decide
      simp only [Pi.mul_apply, c0, Pi.mulSingle_eq_of_ne (show g2ia ≠ g2ir by decide), mul_one]
      rw [zpow_two]
    · have c1 : Tag.G2.cartan g2ia g2ir = -1 := by decide
      simp only [Pi.mul_apply, c1, Pi.mulSingle_eq_same, zpow_neg_one]
      rw [inv_mul_cancel_left, sq]
  rw [e]
  refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
  · rw [← range_simpleRootSL2_g2]
    exact ⟨_, rfl⟩
  · rw [← range_rhoV]
    exact ⟨_, rfl⟩

theorem g2_decomp (hK : ringChar K ≠ 2) {x : adjointGroup .G2 K} (hxz : x * g2z = g2z * x)
    (hx3 : x ^ 3 = 1) : ∃ a b : SL(2, K), x = g2RhoA K a * g2RhoV K b := by
  have ha : ∀ i, signTuple .G2 K g2l i = 1 ∨ signTuple .G2 K g2l i = -1 := by
    intro i
    rcases Int.even_or_odd (Tag.cartan .G2 g2l i) with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  set R := rootSpan .G2 K (rootCharKernel (signTuple .G2 K g2l)) with hR
  have hRe := g2_rootSpan_kernel (K := K) hK
  have hx2 := sq_mem_toralRootGroup hK ha (coe_mem_toralCentralizer hxz)
  have hT : torusGroup .G2 K ≤ Subgroup.normalizer (R : Set (ModGL .G2 K)) :=
    torusGroup_le_normalizer_rootSpan fun _ hα => hα.1
  have hx2' : (x : ModGL .G2 K) ^ 2 ∈
      ((torusGroup .G2 K ⊔ R : Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := hx2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hT] at hx2'
  obtain ⟨t, ht, u, hu, htu⟩ := hx2'
  have htu' : t * u = (x : ModGL .G2 K) ^ 2 := htu
  have hx3' : (x : ModGL .G2 K) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hx3, Subgroup.coe_one]
  have hx4 : (x : ModGL .G2 K) = (t * u) ^ 2 := by
    rw [htu', ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hx3', one_mul, pow_one]
  have ht2 : t ^ 2 ∈ R := by
    rw [hR, hRe]
    exact sq_mem_pairs_of_mem_torus ht
  have hconj : t⁻¹ * u * t ∈ R := by
    have h := (Subgroup.mem_normalizer_iff.mp (hT (inv_mem ht)) u).mp hu
    simpa using h
  have hmem : (x : ModGL .G2 K) ∈ R := by
    rw [hx4, show (t * u) ^ 2 = t ^ 2 * (t⁻¹ * u * t) * u by rw [sq, sq]; group]
    exact mul_mem (mul_mem ht2 hconj) hu
  rw [hR, hRe] at hmem
  have hN : rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0) ≤
      Subgroup.normalizer ((rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ) :
        Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := fun m hm =>
    mem_normalizer_sup_of_commute (fun y hy => g2_commute hK hm (Subgroup.mem_sup_left hy))
      (fun y hy => g2_commute hK hm (Subgroup.mem_sup_right hy))
  have hmem' : (x : ModGL .G2 K) ∈ (((rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)) ⊔
      (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)) : Subgroup (ModGL .G2 K)) :
        Set (ModGL .G2 K)) := hmem
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hmem'
  obtain ⟨m, hm, s, hs, hms⟩ := hmem'
  rw [← range_simpleRootSL2_g2] at hm
  rw [← range_rhoV] at hs
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hs
  have hms' : m * s = (x : ModGL .G2 K) := hms
  refine ⟨a, b, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, coe_g2RhoA, coe_g2RhoV]
  change _ = simpleRootSL2 .G2 K g2l a * rhoV K b
  rw [ha, hb, hms']

theorem blockPair_g2 (hK : ringChar K ≠ 2) : BlockPair (g2RhoA K) (g2RhoV K) g2z where
  inj₁ := g2RhoA_injective
  inj₂ := g2RhoV_injective
  comm := g2RhoA_comm
  neg₁ := g2RhoA_neg_one
  neg₂ := g2RhoV_neg_one
  norm₁ h hh c := by
    have hy : (g2RhoA K c : ModGL .G2 K) ∈ rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0) :=
      mem_range_g2RhoA_iff.mp ⟨c, rfl⟩
    exact mem_range_g2RhoA_iff.mpr (conj_coe_mem_pair hK (Or.inl rfl) hh hy)
  norm₂ h hh c := by
    have hy : (g2RhoV K c : ModGL .G2 K) ∈ rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ) :=
      mem_range_g2RhoV_iff.mp ⟨c, rfl⟩
    exact mem_range_g2RhoV_iff.mpr (conj_coe_mem_pair hK (Or.inr rfl) hh hy)
  decomp x hx hx3 := g2_decomp hK hx hx3

theorem ringChar_eq_of_card_prime [Finite K] {p : ℕ} (hp : p.Prime) (hKp : Nat.card K = p) :
    ringChar K = p := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime (by rw [Fintype.card_eq_nat_card, hKp])
  exact ringChar.eq K p

theorem exists_eq_conj_of_card_prime [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hKp : Nat.card K = p) (α : MulAut (adjointGroup .G2 K)) :
    ∃ g : adjointGroup .G2 K, α = MulAut.conj g := by
  have hK3 : ringChar K ≠ 3 := by rw [ringChar_eq_of_card_prime hp hKp]; omega
  have hK4 : 4 ≤ Nat.card K := by omega
  obtain ⟨hnf, -⟩ := CFSG.RankThree.PartTwo.KFacts.g2_automorphism_normal_form hK3 hK4 (K := K)
  obtain ⟨g, σ, rfl⟩ := hnf α
  refine ⟨g, ?_⟩
  rw [Item211Lie2Proof.ringEquiv_eq_one_of_card_prime hp hKp σ, map_one, mul_one]

section ThreeA

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LieType.Steinberg.RankTwo


theorem isQuasisimple_centralizer_short_split [Finite K] (h31 : 3 ∣ Nat.card K - 1)
    {z : adjointGroup .G2 K} (hzS : z ∈ g2ShortSL2 K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    CFSG.IsQuasisimple (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) := by
  obtain ⟨A, hA⟩ := mem_range_g2RhoV_iff.mpr hzS
  have hA3 : A ^ 3 = 1 := g2RhoV_injective (by rw [map_pow, hA, hz3, map_one])
  obtain ⟨P, t, hPt⟩ := exists_conj_HSL_of_three h31 A ⟨1, by simpa using hA3⟩
  have ht3 : orderOf t = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply HSLHom_injective (K := K)
      rw [map_pow, HSLHom_apply, ← hPt, conj_pow, hA3, mul_one, mul_inv_cancel, map_one]
    · rintro rfl
      apply hz1
      have h1 : A = 1 := by
        have : P * A * P⁻¹ = 1 := by rw [hPt]; exact (map_one (HSLHom K))
        simpa using this
      rw [← hA, h1, map_one]
  set m := g2RhoV K P with hm
  have hmz : ((m * z * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) =
      rootDiagUnit .G2 (Pi.mulSingle g2ir t) := by
    rw [hm, ← hA, ← map_inv, ← map_mul, ← map_mul, coe_g2RhoV, hPt, rhoV_HSL]
  obtain ⟨φ, hφinj, hφ⟩ := exists_a2Hom_injective (K := K)
  have hKer := rootCharKernel_threeA (K := K) ht3
  have heq : Subgroup.centralizer ({m * z * m⁻¹} : Set (adjointGroup .G2 K)) = φ.range := by
    apply le_antisymm
    · intro x hx
      have hx' := (mem_centralizer_iff_toral hmz).mp hx
      obtain ⟨w, hw, hwx⟩ := Sec4.Res417Seven.toralCentralizer_threeA_le_range_a2 φ hφ ht3 hx'
      have : w = x := Subtype.ext hwx
      rwa [← this]
    · refine range_le_of_a2y φ hφ _ fun γ hγ c => ?_
      rw [mem_centralizer_iff_toral hmz, mem_toralCentralizer]
      refine ⟨(a2y γ c).2, ?_⟩
      rw [coe_a2y hγ]
      have hmem : g2CommRoot (a2pos (γ 0, γ 1)) ∈ rootCharKernel (Pi.mulSingle g2ir t) := by
        rw [hKer]
        exact a2_long_roots hγ
      rw [rootDiagUnit_conj_pinnedX _ hmem.1, hmem.2, Units.val_one, one_mul]
  have hq : CFSG.IsQuasisimple φ.range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hφinj)
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num))
  have hq' : CFSG.IsQuasisimple
      (Subgroup.centralizer ({m * z * m⁻¹} : Set (adjointGroup .G2 K))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr heq).symm hq
  have hmap : (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))).map
      (MulAut.conj m).toMonoidHom =
      Subgroup.centralizer ({m * z * m⁻¹} : Set (adjointGroup .G2 K)) := by
    rw [Item211Lie2Proof.map_centralizer_singleton_mulEquiv, MulAut.conj_apply]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))).equivMapOfInjective
      (MulAut.conj m).toMonoidHom (MulAut.conj m).injective).trans
        (MulEquiv.subgroupCongr hmap)).symm hq'

theorem isQuasisimple_centralizer_short [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hKp : Nat.card K = p) {z : adjointGroup .G2 K} (hzS : z ∈ g2ShortSL2 K) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) :
    CFSG.IsQuasisimple (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) := by
  have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h0 : p % 3 ≠ 0 := by
      intro h
      have h3p : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
      rcases (Nat.dvd_prime hp).mp h3p with h1 | h1 <;> omega
    omega
  rcases h3 with h | h
  · exact isQuasisimple_centralizer_short_split (by rw [hKp]; omega) hzS hz3 hz1
  · exact Sec11.KS11Lie7Proof.isQuasisimple_centralizer_threeA (by rw [hKp]; omega)
      (by rw [hKp]; omega) hzS hz3 hz1

end ThreeA

end G2

end Item211Res5Proof

end CFSG.RankThree.PartTwo.Sec21
