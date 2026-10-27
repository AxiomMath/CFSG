module

public import CFSG.RankThree.PartOne.TCX.Tri.E36Frame
public import CFSG.RankThree.PartOne.TCX.Tri.AnTw
public import CFSG.RankThree.PartOne.TCX.Tri.Skeleton
public import CFSG.RankThree.PartOne.TCX.Tri.Frame
public import CFSG.RankThree.PartOne.TCX.Tri.E2A1
public import CFSG.RankThree.PartOne.KLCE.A2Sector
public import CFSG.RankThree.PartOne.KGD.D4T36Family
public import CFSG.RankThree.PartOne.KGD.D4QPerX
public import CFSG.RankThree.PartOne.KGD.D4T36Core
public import CFSG.RankThree.PartOne.TCX.Tri.LayerField
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KE.A1Fixed
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E6TwFourKernel
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PartOne.TCX.E.AnFamily
public import CFSG.RankThree.PartOne.TCX.Tri.E2Kernel
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.TCX.E
  CFSG.RankThree.Lattice
open CFSG.RankThree.PartOne.TCX.F4 (LayerClaimsF4)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.TCX
open scoped MatrixGroups Matrix

section Nseq

variable {L : Type} [Field L] [CharP L 2]

theorem nseq_triF0 (f₀ : ℕ) (n : ModGL TwistTag.D4.tag L)
    (hn : Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n = n) (k : ℕ) :
    Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) (nseq n (triF0 L f₀) k) =
        nseq n (triF0 L f₀) k ∧
      nseq n (triF0 L f₀) k * triP L ^ k = (n * triP L) ^ k := by
  have hP : Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) (triP L) = triP L :=
    units_map_entrywiseHom_diagramMap (t := TwistTag.D4) _
  induction k with
  | zero => simp [nseq_zero]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hstep : nseq n (triF0 L f₀) (k + 1) =
        n * (triP L * nseq n (triF0 L f₀) k * (triP L)⁻¹) := by
      rw [nseq_succ, triF0_apply, ih1]
    refine ⟨?_, ?_⟩
    · rw [hstep, map_mul, map_mul, map_mul, map_inv, hn, hP, ih1]
    · rw [hstep, pow_succ' (n * triP L) k, ← ih2, pow_succ' (triP L) k]
      group

end Nseq

section Embedding


theorem d4A2_set_eq (i : Fin 4) (v : WeylGroup TwistTag.D4.tag)
    (hvS : (fun x => v • x) '' d4StdA2 = d4Sigma i) :
    {r : Fin TwistTag.D4.tag.rank → ℤ | ∃ a b : Fin 3, a ≠ b ∧ r = v • d4Chain a b} =
      d4Sigma i := by
  obtain ⟨c01, c12, c10, c21⟩ := d4Chain_values
  have c02 : d4Chain 0 2 = Pi.single 0 1 + Pi.single 2 1 := by
    rw [← d4Chain_add 0 1 2, c01, c12]
  have c20 : d4Chain 2 0 = -(Pi.single 0 1 + Pi.single 2 1) := by
    rw [d4Chain_swap 0 2, c02]
  rw [← hvS]
  ext r
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨d4Chain a b, ?_, rfl⟩
    rcases d4Chain_cases a b hab with h | h | h | h | h | h <;> rw [h] <;> simp [d4StdA2]
  · rintro ⟨y, hy, rfl⟩
    simp only [d4StdA2, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, 1, by decide, by simp only [c01]⟩
    · exact ⟨1, 2, by decide, by simp only [c12]⟩
    · exact ⟨0, 2, by decide, by simp only [c02]⟩
    · exact ⟨1, 0, by decide, by simp only [c10]⟩
    · exact ⟨2, 1, by decide, by simp only [c21]⟩
    · exact ⟨2, 0, by decide, by simp only [c20]⟩

@[expose] noncomputable def d4A2Embedding (i : Fin 4) (v : WeylGroup TwistTag.D4.tag)
    (hvS : (fun x => v • x) '' d4StdA2 = d4Sigma i) :
    AnEmbedding TwistTag.D4.tag (0 + 3) (d4Sigma i) where
  ρ L _ := (MulAut.conj (canonicalRep (coxeterSystem TwistTag.D4.tag) L v)).toMonoidHom.comp
    (d4rhoStd L)
  r a b := v • d4Chain a b
  mem x := by
    rw [← d4A2_set_eq i v hvS]
    exact Iff.rfl
  isRoot a b hab := ((d4Std_frame' (ZMod 2)).transport v).isRoot a b hab
  neg a b := (((d4Std_frame' (ZMod 2)).transport v).neg a b).symm
  inj L _ := ((d4Std_frame' L).transport v).injective
  range L _ := by
    rw [((d4Std_frame' L).transport v).range, d4A2_set_eq i v hvS]
  gen L _ a b hab := ((d4Std_frame' L).transport v).transv a b hab
  tor L _ b := ⟨fun a => rootChar b (v • d4Chain a 0), fun A =>
    ((d4Std_frame' L).transport v).torus b A⟩
  diag L _ A hA := ((d4Std_frame' L).transport v).diag A hA

end Embedding

section Relations

variable {L : Type} [Field L]
  [CharP L 2]

theorem tri_a2_conj {ε : ℤ} {w : WeylGroup TwistTag.D4.tag}
    (hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x) (i : Fin 4)
    (v : WeylGroup TwistTag.D4.tag)
    (hv0 : v • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4U i)
    (hv2 : v • (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4T36A *ᵥ d4U i)
    (a b : Fin 3) (hab : a ≠ b) (c : L) :
    (canonicalRep (coxeterSystem TwistTag.D4.tag) L w * triP L) *
        pinnedX TwistTag.D4.tag L (v • d4Chain a b) c *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) L w * triP L)⁻¹ =
      pinnedX TwistTag.D4.tag L (ε • (v • d4Chain (finRotate 3 a) (finRotate 3 b))) c := by
  have h2 : (2 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 2
  have hα : IsRoot TwistTag.D4.tag (v • d4Chain a b) :=
    ((d4Std_frame' L).transport v).isRoot a b hab
  have hρα : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm (v • d4Chain a b)) :=
    hα.permLattice TwistTag.D4.cartan_perm
  have e1 : (canonicalRep (coxeterSystem TwistTag.D4.tag) L w * triP L) *
      pinnedX TwistTag.D4.tag L (v • d4Chain a b) c *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L w * triP L)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.D4.tag) L w *
        (triP L * pinnedX TwistTag.D4.tag L (v • d4Chain a b) c * (triP L)⁻¹) *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹ := by group
  rw [e1, triP_conj_pinnedX hα c, canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hρα c, hw,
    KGD.permLattice_symm_permLattice]
  have hrot := d4T36_perm i v hv0 hv2 a b hab
  have hMu : d4T36M ε *ᵥ (v • d4Chain a b) = ε • (d4T36A *ᵥ (v • d4Chain a b)) := by
    rw [d4T36M, Matrix.smul_mulVec]
  rw [hMu, hrot]

end Relations

section Layer

variable {C : Type} [Group C]
  [Finite C] {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {p f₀ : ℕ}
  {ι : C →* ModGL TwistTag.D4.tag L} {α₀ : MulAut C}

theorem tri_a2_layer (h : IsShintani p ι (triF0 L f₀) (triPhi L p f₀) α₀) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀)
    (hodd : ∀ t ∈ torusGroup TwistTag.D4.tag L, ∃ m : ℕ, Odd m ∧ t ^ m = 1)
    {K : Type} [Field K] [Finite K] [Algebra K L] [IsAlgClosure K L] (σ : K ≃+* K)
    (hKc : Nat.card K = (2 ^ (p * f₀)) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ (p * f₀))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {w : WeylGroup TwistTag.D4.tag}
    (hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x)
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀C : g₀ ∈ adjointGroup TwistTag.D4.tag L)
    (hg₀ : triF0 L f₀ g₀ = g₀ * canonicalRep (coxeterSystem TwistTag.D4.tag) L w)
    (i : Fin 4) {x : C} (hx : orderOf x = p) {c : C} (hcα : α₀ c = c)
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = g₀⁻¹ * ι (c * x * c⁻¹) * g₀)
    (hbT : rootDiagUnit TwistTag.D4.tag b ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) L w) (triF0 L f₀))
    (hker : rootCharKernel b = trialitySigma i) :
    SingleLayerData p α₀ (Subgroup.centralizer ({x} : Set C)) := by
  classical
  have hp3 : 3 < p := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hpf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have hkcard : Nat.card (fixSubfield σ) = 2 ^ (p * f₀) :=
    card_fixSubfield_cube Nat.prime_two hpf hKc σ hσ
  obtain ⟨_, hst1, hac1⟩ := exists_tower_algebra (K₀ := fixSubfield σ) (K := K) (L := L)
  have hkcard' : Nat.card (fixSubfield σ) = 2 ^ (p * (1 * f₀)) := by rw [hkcard, one_mul]
  obtain ⟨σQ, hσQord, hσQ⟩ := exists_layer_aut hp hf₀ 1 le_rfl L hkcard'
  rw [one_mul] at hσQ
  have : CharP (fixSubfield σ) 2 := ⟨fun x => by
    rw [← (algebraMap (fixSubfield σ) L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  obtain ⟨K₀, _, _, _, hK₀⟩ := exists_subfield_of_frobenius hp hf₀ hkcard hσQord
  obtain ⟨_, hst2, hac2⟩ := exists_tower_algebra (K₀ := K₀) (K := fixSubfield σ) (L := L)
  set n : ModGL TwistTag.D4.tag L := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hndef
  have hn_rat : Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n = n :=
    canonicalRep_frobenius_fixed f₀ w
  have hP_rat : Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) (triP L) = triP L :=
    units_map_entrywiseHom_diagramMap (t := TwistTag.D4) _
  set m : ModGL TwistTag.D4.tag L := n * triP L with hmdef
  have hm_rat : Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) m = m := by
    rw [hmdef, map_mul, hn_rat, hP_rat]
  obtain ⟨v, hv0, hv2, hvS⟩ := exists_smul_d4StdA2 i
  set E := d4A2Embedding i v hvS with hE
  set π : Equiv.Perm (Fin (0 + 3)) := finRotate 3 with hπ
  have hcs : ε = 1 → ∀ a b : Fin (0 + 3), a ≠ b → ∃ β : Lˣ, ∀ c : L,
      m * pinnedX TwistTag.D4.tag L (E.r a b) c * m⁻¹ =
        pinnedX TwistTag.D4.tag L (E.r (π a) (π b)) ((β : L) * c) := by
    intro hε1 a b hab
    refine ⟨1, fun c => ?_⟩
    have := tri_a2_conj (L := L) hw i v hv0 hv2 a b hab c
    rw [hε1, one_smul] at this
    rw [Units.val_one, one_mul]
    exact this
  have hcu : ε = -1 → ∀ a b : Fin (0 + 3), a ≠ b → ∃ β : Lˣ, ∀ c : L,
      m * pinnedX TwistTag.D4.tag L (E.r a b) c * m⁻¹ =
        pinnedX TwistTag.D4.tag L (E.r (π b) (π a)) ((β : L) * c) := by
    intro hε1 a b hab
    refine ⟨1, fun c => ?_⟩
    have := tri_a2_conj (L := L) hw i v hv0 hv2 a b hab c
    rw [hε1, neg_smul, one_smul, ← smul_neg, ← d4Chain_swap] at this
    rw [Units.val_one, one_mul]
    exact this
  have hSroot : ∀ α ∈ d4Sigma i, IsRoot TwistTag.D4.tag α := fun α hα =>
    isRoot_of_mem_d4Sigma hα
  have hSneg : ∀ α ∈ d4Sigma i, -α ∈ d4Sigma i := by
    intro α hα
    obtain ⟨a, b, hab, rfl⟩ := (E.mem α).1 hα
    exact (E.mem _).2 ⟨b, a, hab.symm, E.neg a b⟩
  obtain ⟨P, hfam, hPeq⟩ := an_family' E ε hε π (K := fixSubfield σ) (L := L) hf₀ hp hp5 hkcard
    m hcs hcu
  obtain ⟨hN1, hN2⟩ := nseq_triF0 f₀ n hn_rat p
  have hfam' : IsSigmaFamilyΦ (nseq n (triF0 L f₀) p) (triPhi L p f₀) (d4Sigma i)
      (fun _ : Unit => P) := by
    refine isSigmaFamilyΦ_twPhi (nseq n (triF0 L f₀) p) (triP L ^ p)
      (iterateFrobenius L 2 (f₀ * p)) (d4Sigma i) (fun _ : Unit => P) ?_
    rw [hN2]
    exact hfam
  have hjoin : rootSpan TwistTag.D4.tag L (d4Sigma i) ⊓
      twistedFixedPoints (nseq n (triF0 L f₀) p) (triPhi L p f₀) ≤ (fun _ : Unit => P) () := by
    change rootSpan TwistTag.D4.tag L (d4Sigma i) ⊓ twistedFixedPoints (nseq n (triF0 L f₀) p)
      (twPhi (triP L ^ p) (iterateFrobenius L 2 (f₀ * p))) ≤ P
    rw [twistedFixedPoints_twPhi, hN2, ← E.range L, ← hPeq]
  obtain ⟨D, hD, ρ', τ', hρ'inj, hρ'range, hρ'compat, hclaims⟩ := an_model' E ε hε π
    (K₀ := K₀) (K := fixSubfield σ) (L := L) hf₀ hK₀ hp hp5 hkcard σQ hσQord hσQ m hm_rat hcs hcu
  have hrr : ρ'.range = (fun _ : Unit => P) () := by rw [hρ'range, hPeq]
  have hcompat : ∀ d, n * triF0 L f₀ (ρ' d) * n⁻¹ = ρ' (τ' d) := fun d => by
    rw [← hρ'compat d, triF0_apply, hmdef]
    group
  have hmodel : ∃ (D : Type) (_ : Group D) (ρ' : D →* ModGL TwistTag.D4.tag L) (τ' : D →* D),
      Function.Injective ρ' ∧ ρ'.range = (fun _ : Unit => P) () ∧
      (∀ d, n * triF0 L f₀ (ρ' d) * n⁻¹ = ρ' (τ' d)) ∧
      ∀ {G : Type} [Group G] (α : MulAut G) (φ : D →* G), Function.Injective φ →
        (∀ d, α (φ d) = φ (τ' d)) → ∀ Q : Subgroup G, φ.range = Q → LayerClaimsF4 p α Q := by
    refine ⟨D, hD, ρ', τ', hρ'inj, hrr, hcompat, ?_⟩
    intro G _ α φ hφ hαφ Q hQ
    have hker : ∀ d, φ d = 1 → d ∈ Subgroup.center D := fun d hd => by
      have : d = 1 := hφ (hd.trans (map_one φ).symm)
      rw [this]
      exact one_mem _
    exact (hclaims 1 hp.not_dvd_one α φ hker (fun d => by
      rw [Function.iterate_one]
      exact hαφ d) Q hQ).2
  have hbS : rootCharKernel b ⊆ d4Sigma i := by
    rw [hker]
    exact le_rfl
  have hbc : rootDiagUnit TwistTag.D4.tag b ∈ Subgroup.centralizer
      (rootSpan TwistTag.D4.tag L (d4Sigma i) : Set (ModGL TwistTag.D4.tag L)) := by
    refine (rootDiagUnit_mem_centralizer_rootSpan_iff b hSroot).2 fun β hβ => ?_
    have hβ' : β ∈ rootCharKernel b := by
      rw [hker]
      exact hβ
    exact hβ'.2
  exact tri_layer_of_frame h hp hp3 hodd hg₀C hg₀ hSroot hSneg (fun _ : Unit => P) hfam' hjoin
    hx hcα hb hbT hbS hbc hmodel

end Layer

end CFSG.RankThree.PartOne.TCX.Tri
