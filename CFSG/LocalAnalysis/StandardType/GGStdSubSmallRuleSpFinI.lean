module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFinNum
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlane
public import CFSG.RankThree.PartOne.S11d.PSpGood
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S11d.PSLDescent
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType.SpFin

open Module CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpFull CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.TwoThree CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedSp)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem finite_statedSp_group : Finite (StatedSp m K) :=
  Finite.of_injective
    (fun x : StatedSp m K =>
      ((x : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))

theorem isoSetup_map {Ã : Subgroup (StatedSp m K)} (hÃ : IsElemAbelian 3 Ã) :
    IsoSetup (spForm m K) (Ã.map (spLin m K)) where
  comm := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hÃ ha hb]
  exp := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hÃ.2 a ha, map_one]
  inv := by
    rintro _ ⟨a, ha, rfl⟩ v w
    exact mem_sesqUnitaryGroup.mp (spLin_mem a) v w

theorem fixedFactor_fix_range {x d : StatedSp m K}
    (blocks : SpPrimaryBlocks 2 1 3 x (proj m K x)) (hd : d ∈ spFixedFactor x) :
    ∀ w ∈ LinearMap.range (spEnd x - 1), spEnd d w = w := by
  classical
  rintro _ ⟨u, rfl⟩
  have hd' : d ∈ spSupported x {Polynomial.X - 1} := hd
  have hu : u ∈ ⨆ k : primaryFactors (spEnd x), primaryComponent (spEnd x) (k : Polynomial K) := by
    rw [blocks.isInternal.submodule_iSup_eq_top]
    trivial
  refine Submodule.iSup_induction
    (fun k : primaryFactors (spEnd x) => primaryComponent (spEnd x) (k : Polynomial K))
    (motive := fun u => spEnd d ((spEnd x - 1) u) = (spEnd x - 1) u) hu ?_ ?_ ?_
  · rintro ⟨k, hk⟩ u hu
    by_cases hk1 : k = Polynomial.X - 1
    · subst hk1
      have : u ∈ LinearMap.ker (spEnd x - 1) := blocks.fixed_eq ▸ hu
      rw [LinearMap.mem_ker.mp this, map_zero]
    · have hmem : (spEnd x - 1) u ∈ primaryComponent (spEnd x) k := by
        have := apply_mem_primaryComponent (Commute.refl (spEnd x)) hu
        simp only [LinearMap.sub_apply, Module.End.one_apply]
        exact Submodule.sub_mem _ this hu
      exact (mem_spSupported.mp hd').2 k hk (fun h => hk1 (Set.mem_singleton_iff.mp h)) _ hmem
  · simp
  · intro a b ha hb
    simp only [map_add, ha, hb]

theorem commute_of_fix_fixedFactor {x b d : StatedSp m K} (hx3 : x ^ 3 = 1)
    (blocks : SpPrimaryBlocks 2 1 3 x (proj m K x)) (hbx : b * x = x * b)
    (hb : ∀ u ∈ LinearMap.ker (spEnd x - 1), spEnd b u = u) (hd : d ∈ spFixedFactor x) :
    b * d = d * b := by
  have hd' : d ∈ spSupported x {Polynomial.X - 1} := hd
  have hdx : d * x = x * d := (mem_spSupported.mp hd').1
  have hxd : spEnd x * spEnd d = spEnd d * spEnd x := (spEnd_comm_iff.mp hdx).symm
  have hxb : spEnd x * spEnd b = spEnd b * spEnd x := (spEnd_comm_iff.mp hbx).symm
  have hx3' : spEnd x ^ 3 = 1 := spEnd_pow hx3
  apply spEnd_injective
  rw [spEnd_mul, spEnd_mul]
  apply LinearMap.ext
  intro v
  obtain ⟨v₁, hv₁, w, hw, rfl⟩ := CFSG.RankThree.PartOne.OddIso.exists_fix_add_range (p := 3)
    ⟨1, by norm_num⟩ hx3' v
  obtain ⟨u, rfl⟩ := hw
  have hdv₁ : spEnd d v₁ ∈ LinearMap.ker (spEnd x - 1) := by
    rw [LinearMap.mem_ker, sub_one_apply_comm hxd, LinearMap.mem_ker.mp hv₁, map_zero]
  have hbw : spEnd b ((spEnd x - 1) u) ∈ LinearMap.range (spEnd x - 1) :=
    ⟨spEnd b u, by rw [sub_one_apply_comm hxb]⟩
  have hdw : spEnd d ((spEnd x - 1) u) = (spEnd x - 1) u :=
    fixedFactor_fix_range blocks hd _ (LinearMap.mem_range_self _ u)
  have hdbw : spEnd d (spEnd b ((spEnd x - 1) u)) = spEnd b ((spEnd x - 1) u) :=
    fixedFactor_fix_range blocks hd _ hbw
  simp only [Module.End.mul_apply, map_add]
  rw [hdw, hb _ hdv₁, hb _ hv₁, hdbw]

omit [Finite K] [CharP K 2] in
theorem finrank_spSpace (m : ℕ) : finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, ← two_mul]

theorem isQuasisimple_fixedFactor_of_six_le (hK : Nat.card K = 2) {x : StatedSp m K}
    (blocks : SpPrimaryBlocks 2 1 3 x (proj m K x)) (hd : 6 ≤ spFixedDim x) :
    CFSG.IsQuasisimple (spFixedFactor x) := by
  have hmem := X_sub_one_mem_primaryFactors x (by omega)
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hB : ((spForm m K).restrict (primaryComponent (spEnd x) (Polynomial.X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin m ⊕ Fin m → K)
  obtain ⟨s, hs, ⟨e⟩⟩ := KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB
    blocks.fixed_nondegenerate
  have hs3 : 3 ≤ s := by
    have : spFixedDim x = finrank K (primaryComponent (spEnd x) (Polynomial.X - 1)) := rfl
    omega
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (φ.trans e).symm
    (CFSG.LieType.Universal.Symplectic.isQuasisimple s K (by omega)
      (Or.inr (Or.inr ⟨hK, hs3⟩)))

theorem coreI (hK : Nat.card K = 2) (hm : 5 ≤ m) {Ã : Subgroup (StatedSp m K)}
    (hÃ : IsElemAbelian 3 Ã) (hcard : 3 ^ (m - 1) ≤ Nat.card Ã)
    {T : Submodule K (Fin m ⊕ Fin m → K)} (hT0 : T ≠ ⊥)
    (hTiso : ∀ u ∈ T, ∀ v ∈ T, spForm m K u v = 0)
    (hTÃ : ∀ a ∈ Ã, ∀ t ∈ T, spEnd a t ∈ T) {x : StatedSp m K} (hx : x ∈ Ã) (hx1 : x ≠ 1)
    (blocks : SpPrimaryBlocks 2 1 3 x (proj m K x)) (hd : 4 ≤ spFixedDim x) :
    ∃ Q : Subgroup (StatedSp m K), CFSG.IsQuasisimple Q ∧
      Q ≤ Subgroup.centralizer ({x} : Set (StatedSp m K)) ∧
      (∀ c ∈ Subgroup.centralizer ({x} : Set (StatedSp m K)), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) ∧
      ((∃ b ∈ Ã, b ∉ Subgroup.zpowers x ∧ ∀ q ∈ Q, b * q = q * b) ∨
        3 ^ 3 ≤ Nat.card (Ã ⊓ Q : Subgroup (StatedSp m K))) := by
  classical
  haveI := finite_statedSp_group (K := K) (m := m)
  haveI := finite_units_end (K := K) (V := Fin m ⊕ Fin m → K)
  have hx3 : x ^ 3 = 1 := hÃ.2 x hx
  set Xg : Subgroup (Module.End K (Fin m ⊕ Fin m → K))ˣ := Ã.map (spLin m K) with hXg
  have hXiso := isoSetup_map hÃ
  have hx₀ : spLin m K x ∈ Xg := ⟨x, hx, rfl⟩
  have hx₁ : spLin m K x ≠ 1 := fun h => hx1 (spLin_injective (h.trans (map_one _).symm))
  have hcardX : 3 ^ (m - 1) ≤ Nat.card Xg := by
    rw [hXg, ← Nat.card_congr (Ã.equivMapOfInjective (spLin m K) spLin_injective).toEquiv]
    exact hcard
  have hTX : ∀ g ∈ Xg, ∀ t ∈ T, (g : Module.End K (Fin m ⊕ Fin m → K)) t ∈ T := by
    rintro _ ⟨a, ha, rfl⟩ t ht
    exact hTÃ a ha t ht
  have hlem := lemI hK spForm_nondegenerate spForm_isAlt.isRefl hXiso hx₀ hx₁ (n := m)
    (by omega) (finrank_spSpace m) hcardX hT0 hTiso hTX
  have hx3' : (spLin m K x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hsum : finrank K (LinearMap.ker (spEnd x - 1)) + finrank K (LinearMap.range (spEnd x - 1)) =
      2 * m := by
    have h := Submodule.finrank_add_eq_of_isCompl (isCompl_fix_rng hx3')
    rw [finrank_spSpace m] at h
    exact h
  have hfix : finrank K (LinearMap.ker (spEnd x - 1)) = spFixedDim x := by
    rw [← blocks.fixed_eq]
    rfl
  have hbx : ∀ b ∈ Ã, b * x = x * b := fun b hb => TableB.IsElemAbelian.comm hÃ hb hx
  have hnz : ∀ b ∈ Ã, spLin m K b ∉ Subgroup.zpowers (spLin m K x) → b ∉ Subgroup.zpowers x := by
    intro b _ hn hbz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbz
    exact hn (Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow, hk]⟩)
  by_cases hd6 : 6 ≤ spFixedDim x
  · refine ⟨spFixedFactor x, isQuasisimple_fixedFactor_of_six_le hK blocks hd6,
      spFixedFactor_le_centralizer x, fun c hc q hq => spFixedFactor_conj hc hq, ?_⟩
    rcases hlem with ⟨g, hgX, hgn, hgf⟩ | ⟨hdm, hX2⟩
    · obtain ⟨b, hb, rfl⟩ := hgX
      exact Or.inl ⟨b, hb, hnz b hb hgn, fun q hq =>
        commute_of_fix_fixedFactor hx3 blocks (hbx b hb) (fun u hu => hgf u hu) hq⟩
    · right
      have hle : (Xg ⊓ fixG (LinearMap.range (spEnd x - 1)) :
          Subgroup (Module.End K (Fin m ⊕ Fin m → K))ˣ) ≤
          (Ã ⊓ spFixedFactor x : Subgroup (StatedSp m K)).map (spLin m K) := by
        rintro g ⟨hgX, hgf⟩
        obtain ⟨b, hb, rfl⟩ := hgX
        exact ⟨b, ⟨hb, mem_spFixedFactor_of_fix (hbx b hb) (fun w hw => hgf w hw)⟩, rfl⟩
      calc 3 ^ 3 ≤ 3 ^ (m - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ Nat.card (Xg ⊓ fixG (LinearMap.range (spEnd x - 1)) :
            Subgroup (Module.End K (Fin m ⊕ Fin m → K))ˣ) := hX2
        _ ≤ Nat.card ((Ã ⊓ spFixedFactor x : Subgroup (StatedSp m K)).map (spLin m K)) :=
          Subgroup.card_le_of_le hle
        _ = Nat.card (Ã ⊓ spFixedFactor x : Subgroup (StatedSp m K)) :=
          (Nat.card_congr ((Ã ⊓ spFixedFactor x : Subgroup (StatedSp m K)).equivMapOfInjective
            (spLin m K) spLin_injective).toEquiv).symm
  · obtain ⟨s, hs, -⟩ := blocks.rank
    have hd4 : spFixedDim x = 4 := by
      have : spFixedDim x = 2 * s := hs
      omega
    have hnorm : ∀ c ∈ Subgroup.centralizer ({x} : Set (StatedSp m K)),
        ∀ q ∈ ⁅spFixedFactor x, spFixedFactor x⁆,
          c * q * c⁻¹ ∈ ⁅spFixedFactor x, spFixedFactor x⁆ := by
      intro c hc q hq
      have hle : ⁅spFixedFactor x, spFixedFactor x⁆.map (MulAut.conj c).toMonoidHom ≤
          ⁅spFixedFactor x, spFixedFactor x⁆ := by
        rw [Subgroup.map_commutator]
        have hDc : (spFixedFactor x).map (MulAut.conj c).toMonoidHom ≤ spFixedFactor x := by
          rintro _ ⟨y, hy, rfl⟩
          exact spFixedFactor_conj hc hy
        exact Subgroup.commutator_mono hDc hDc
      exact hle ⟨q, hq, rfl⟩
    refine ⟨⁅spFixedFactor x, spFixedFactor x⁆, (spFixed_four_two hK blocks hd4).1,
      (Subgroup.commutator_le_self _).trans (spFixedFactor_le_centralizer x),
      hnorm, ?_⟩
    rcases hlem with ⟨g, hgX, hgn, hgf⟩ | ⟨hdm, hX2⟩
    · obtain ⟨b, hb, rfl⟩ := hgX
      exact Or.inl ⟨b, hb, hnz b hb hgn, fun q hq =>
        commute_of_fix_fixedFactor hx3 blocks (hbx b hb) (fun u hu => hgf u hu)
          (Subgroup.commutator_le_self _ hq)⟩
    · exfalso
      have hdm' : finrank K (LinearMap.range (spEnd x - 1)) ≤ 4 := hdm
      omega

end CFSG.StandardType.SpFin
