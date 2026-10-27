module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockPSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMOmegaFixed
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoOneLinear

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedOmega)


private lemma omegaBlockGroup_moved_eq_unitaryRCK {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (heprim : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε ≠ ε) :
    ∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2),
      Nat.card E = Q ^ 2 ∧
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃*
        ↥(ClassicalBlocks.GUFull m Q E)) := by
  obtain ⟨d, m, E, hEfield, hEfin, -, hEcard, -, -, ⟨iso⟩⟩ :=
    ClassicalBlocks.blockGroup_iso_Omega_unitary Φ hΦ h8 b hb hodd hε heprim h1
  exact
    letI : Field E := hEfield
    letI : Fintype E := hEfin
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by
      obtain ⟨f, -, hKcard⟩ := FiniteField.card K 2
      have hEtwo : Fintype.card E = 2 ^ (2 * ((f : ℕ) * d)) := by
        rw [hEcard, hKcard, ← pow_mul, ← pow_mul]
        congr 1
        ring
      have hcharE : CharP E 2 := charP_of_card_eq_prime_pow (p := 2)
        (f := 2 * ((f : ℕ) * d)) hEtwo
      refine ⟨m, Fintype.card K ^ d, E, hEfield, Fintype.finite hEfin, hcharE, ?_, ⟨iso⟩⟩
      rw [Nat.card_eq_fintype_card]
      exact hEcard

private lemma omegaBlockGroup_pair_eq_generalLinearRCK {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    {e e' : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e')
    (hne : e ≠ e') (hεe : ε = e + e') :
    ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2),
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* GL (Fin m) E) := by
  obtain ⟨d, m, E, hEfield, hEfin, -, hEcard, -, -, ⟨iso⟩⟩ :=
    ClassicalBlocks.blockGroup_iso_Omega_linear Φ hΦ h8 b hb hodd hε he he' hne hεe
  exact
    letI : Field E := hEfield
    letI : Fintype E := hEfin
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by
      obtain ⟨f, -, hKcard⟩ := FiniteField.card K 2
      have hEtwo : Fintype.card E = 2 ^ ((f : ℕ) * d) := by
        rw [hEcard, hKcard, ← pow_mul]
      have hcharE : CharP E 2 := charP_of_card_eq_prime_pow (p := 2)
        (f := (f : ℕ) * d) hEtwo
      exact ⟨m, E, hEfield, Fintype.finite hEfin, hcharE, ⟨iso⟩⟩

private lemma omegaBlockModel_fixed {ι : Type} [Fintype ι] [DecidableEq ι] {f : ℕ}
    (hf : 1 ≤ f) (Φ : QuadraticForm (GaloisField 2 f) (ι → GaloisField 2 f))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    {b : GL ι (GaloisField 2 f)} (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({b} : Set (GL ι (GaloisField 2 f))))) ε)
    {J' : Subgroup ↥(StatedOmega ⇑Φ)}
    (hCo : CFSG.Open.IsComponentOf
      (J'.subgroupOf (glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)) ⊤)
    (h1 : (b : Matrix ι ι (GaloisField 2 f)) * ε = ε) :
    ∃ (t : StatedLieTag) (m g : ℕ)
      (κ : (ggU t m g).K →* ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)),
      RCKClassicalTag t ∧ 1 ≤ g ∧
        RCKModelConverse (J'.subgroupOf (glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε))
          t m g κ := by
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  let H : Subgroup ↥(StatedOmega ⇑Φ) := glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε
  let C : Subgroup ↥H := J'.subgroupOf H
  change ∃ (t : StatedLieTag) (m g : ℕ) (κ : (ggU t m g).K →* ↥H),
    RCKClassicalTag t ∧ 1 ≤ g ∧ RCKModelConverse C t m g κ
  have hCoC : CFSG.Open.IsComponentOf C ⊤ := hCo
  obtain ⟨ι₁, hFintype₁, hDecEq₁, Q₁, -, ⟨Φ₁, hΦ₁eq, hΦ₁nd⟩, hdisj⟩ :=
    ClassicalBlocks.blockGroup_iso_Omega_one Φ hΦ h8 b hb hodd hε h1
  letI : Fintype ι₁ := hFintype₁
  letI : DecidableEq ι₁ := hDecEq₁
  rcases hdisj with ⟨⟨iso⟩, hnotsmall⟩ | ⟨-, -, hsol, -⟩
  · have hsmall : ¬ (Nat.card (GaloisField 2 f) = 2 ∧ Fintype.card ι₁ = 4 ∧
        ∃ S : Submodule (GaloisField 2 f) (ι₁ → GaloisField 2 f),
          Module.finrank (GaloisField 2 f) S = 2 ∧ ∀ x ∈ S, Φ₁ x = 0) := by
      simpa only [Nat.card_eq_fintype_card, hΦ₁eq] using hnotsmall
    have hiso : Nonempty (↥H ≃* ↥(StatedOmega ⇑Φ₁)) := ⟨hΦ₁eq.symm ▸ iso⟩
    exact rckBlockModel_omegaFixed hCoC hf Φ₁ hΦ₁nd hsmall hiso.some
  · exfalso
    have hCq : CFSG.Open.IsQuasisimple C := hCoC.2.2
    haveI : Nontrivial (C ⧸ Subgroup.center C) := hCq.2.toNontrivial
    haveI : Nontrivial C := (QuotientGroup.mk_surjective (s := Subgroup.center C)).nontrivial
    haveI : Group.IsPerfect C := ⟨hCq.1⟩
    letI : Group.IsSolvable ↥H := hsol
    exact (Group.IsPerfect.not_isSolvable C) inferInstance

private lemma omegaBlockModel_moved {ι : Type} [Fintype ι] [DecidableEq ι] {f : ℕ}
    (Φ : QuadraticForm (GaloisField 2 f) (ι → GaloisField 2 f))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    {b : GL ι (GaloisField 2 f)} (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({b} : Set (GL ι (GaloisField 2 f))))) ε)
    {J' : Subgroup ↥(StatedOmega ⇑Φ)}
    (hCo : CFSG.Open.IsComponentOf
      (J'.subgroupOf (glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)) ⊤)
    (heprim : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f)
      (Units.val '' ({b} : Set (GL ι (GaloisField 2 f))))) ε)
    (h1 : (b : Matrix ι ι (GaloisField 2 f)) * ε ≠ ε) :
    (∃ (t : StatedLieTag) (m g : ℕ)
      (κ : (ggU t m g).K →* ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)),
      RCKClassicalTag t ∧ 1 ≤ g ∧
        RCKModelConverse (J'.subgroupOf (glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε))
          t m g κ) ∨
    (∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), m ≤ 3 ∧
      Nat.card E = Q ^ 2 ∧
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃*
        ↥(ClassicalBlocks.GUFull m Q E))) := by
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  let H : Subgroup ↥(StatedOmega ⇑Φ) := glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε
  let C : Subgroup ↥H := J'.subgroupOf H
  change (∃ (t : StatedLieTag) (m g : ℕ) (κ : (ggU t m g).K →* ↥H),
      RCKClassicalTag t ∧ 1 ≤ g ∧ RCKModelConverse C t m g κ) ∨
    (∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), m ≤ 3 ∧
      Nat.card E = Q ^ 2 ∧ Nonempty (↥H ≃* ↥(ClassicalBlocks.GUFull m Q E)))
  have hCoC : CFSG.Open.IsComponentOf C ⊤ := hCo
  rcases omegaBlockGroup_moved_eq_unitaryRCK Φ hΦ h8 b hb hodd hε heprim h1 with
    ⟨m, Q, E, hEfield, hEfin, hCh, hEcard, ⟨iso⟩⟩
  letI : Field E := hEfield
  letI : Finite E := hEfin
  letI : CharP E 2 := hCh
  rcases rckBlockModel_unitaryCase (m := m) (Q := Q) (E := E) hCoC hEcard (Φ := iso) with
    h | h
  · exact Or.inl h
  · obtain ⟨m', Q', E', hF', hFin', hCh', hm3, hEcard', Φ', -⟩ := h
    exact Or.inr ⟨m', Q', E', hF', hFin', hCh', hm3, hEcard', ⟨Φ'⟩⟩

private lemma omegaBlockModel_pair {ι : Type} [Fintype ι] [DecidableEq ι] {f : ℕ}
    (Φ : QuadraticForm (GaloisField 2 f) (ι → GaloisField 2 f))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    {b : GL ι (GaloisField 2 f)} (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({b} : Set (GL ι (GaloisField 2 f))))) ε)
    {J' : Subgroup ↥(StatedOmega ⇑Φ)}
    (hCo : CFSG.Open.IsComponentOf
      (J'.subgroupOf (glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)) ⊤)
    {e e' : Matrix ι ι (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f)
      (Units.val '' ({b} : Set (GL ι (GaloisField 2 f))))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f)
      (Units.val '' ({b} : Set (GL ι (GaloisField 2 f))))) e')
    (hne : e ≠ e') (hεe : ε = e + e') :
    ∃ (t : StatedLieTag) (m g : ℕ)
      (κ : (ggU t m g).K →* ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)),
      RCKClassicalTag t ∧ 1 ≤ g ∧
        RCKModelConverse (J'.subgroupOf (glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε))
          t m g κ := by
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  let H : Subgroup ↥(StatedOmega ⇑Φ) := glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε
  let C : Subgroup ↥H := J'.subgroupOf H
  change ∃ (t : StatedLieTag) (m g : ℕ) (κ : (ggU t m g).K →* ↥H),
    RCKClassicalTag t ∧ 1 ≤ g ∧ RCKModelConverse C t m g κ
  have hCoC : CFSG.Open.IsComponentOf C ⊤ := hCo
  rcases omegaBlockGroup_pair_eq_generalLinearRCK Φ hΦ h8 b hb hodd hε he he' hne hεe with
    ⟨m, E, hEfield, hEfin, hCh, ⟨iso⟩⟩
  letI : Field E := hEfield
  letI : Finite E := hEfin
  letI : CharP E 2 := hCh
  exact rckBlockModel_linearCase (m := m) (E := E) hCoC (Φ := iso)

private lemma omegaBlockModel_of_isPrimAdjIdemIn {ι : Type} [Fintype ι] [DecidableEq ι] {f : ℕ}
    (hf : 1 ≤ f) (Φ : QuadraticForm (GaloisField 2 f) (ι → GaloisField 2 f))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    {b : GL ι (GaloisField 2 f)} (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({b} : Set (GL ι (GaloisField 2 f))))) ε)
    {J' : Subgroup ↥(StatedOmega ⇑Φ)}
    (hJ' : IsComponentOf J' ⁅glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε,
      glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε⁆) :
    (∃ (t : StatedLieTag) (m g : ℕ) (κ : (ggU t m g).K →*
        ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)),
      RCKClassicalTag t ∧ 1 ≤ g ∧
        RCKModelConverse (J'.subgroupOf (glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε))
          t m g κ) ∨
    (∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), m ≤ 3 ∧
      Nat.card E = Q ^ 2 ∧
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃*
        ↥(ClassicalBlocks.GUFull m Q E))) := by
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  let H : Subgroup ↥(StatedOmega ⇑Φ) := glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε
  let C : Subgroup ↥H := J'.subgroupOf H
  have hC : IsComponentOf C ⊤ := rckIsComponentOf_top_of_commutator hJ'
  have hCo : CFSG.Open.IsComponentOf C ⊤ := (CFSG.Assembly.isComponentOf_iff_open).1 hC
  let G : Matrix ι ι (GaloisField 2 f) :=
    LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Φ)
  have hG : IsUnit G.det := CFSG.StandardType.TableC.polarGram_isUnit_det Φ hΦ
  have hGt : Matrix.transpose G = G := CFSG.StandardType.TableC.polarGram_transpose Φ
  have hS : ∀ s ∈ ({b} : Set (GL ι (GaloisField 2 f))),
      ∀ s' ∈ ({b} : Set (GL ι (GaloisField 2 f))), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hSU : ∀ s ∈ ({b} : Set (GL ι (GaloisField 2 f))),
      Matrix.transpose (s : Matrix ι ι (GaloisField 2 f)) * G *
        (s : Matrix ι ι (GaloisField 2 f)) = G := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    have hg : ∀ v : ι → GaloisField 2 f,
        Φ (Matrix.mulVec (s : Matrix ι ι (GaloisField 2 f)) v) = Φ v :=
      fun v => CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.isometry_of_mem_statedOmega
        (f := ⇑Φ) hb v
    have h := CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.gram_invariant (Q := Φ) hg
    simpa [G, Matrix.map_id,
      CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.polarGram_eq_toMatrix₂'] using h
  have hSUmap : ∀ s ∈ ({b} : Set (GL ι (GaloisField 2 f))),
      Matrix.transpose ((s : Matrix ι ι (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) * G *
        (s : Matrix ι ι (GaloisField 2 f)) = G := by
    simpa [Matrix.map_id] using hSU
  obtain ⟨e, he, heε, -⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn
    (RingHom.id (GaloisField 2 f)) (fun _ => rfl) (G := G) hG
    (by simpa [Matrix.map_id] using hGt) hS hSUmap hε
  rcases CFSG.StandardType.TableC.isPrimIdemIn_cases hG hGt hS hSU hε he heε with
    heq | ⟨-, e', he', hne', hεe⟩
  · have heprim : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({b} : Set (GL ι (GaloisField 2 f))))) ε := heq ▸ he
    by_cases h1 : (b : Matrix ι ι (GaloisField 2 f)) * ε = ε
    · exact Or.inl (omegaBlockModel_fixed hf Φ hΦ h8 hb hodd hε hCo h1)
    · exact omegaBlockModel_moved Φ hΦ h8 hb hodd hε hCo heprim h1
  · exact Or.inl (omegaBlockModel_pair Φ hΦ h8 hb hodd hε hCo he he' hne' hεe)

theorem rckBlockModel_Omega {ι : Type} [Fintype ι] [DecidableEq ι] {f : ℕ} (hf : 1 ≤ f)
    (Φ : QuadraticForm (GaloisField 2 f) (ι → GaloisField 2 f))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    {b : GL ι (GaloisField 2 f)} (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({b} : Set (GL ι (GaloisField 2 f))))) ε)
    {J' : Subgroup ↥(StatedOmega ⇑Φ)}
    (hJ' : IsComponentOf J' ⁅glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε,
      glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε⁆) :
    (∃ (t : StatedLieTag) (m g : ℕ) (κ : (ggU t m g).K →*
        ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)),
      RCKClassicalTag t ∧ 1 ≤ g ∧
        RCKModelConverse (J'.subgroupOf (glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε))
          t m g κ) ∨
    (∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), m ≤ 3 ∧
      Nat.card E = Q ^ 2 ∧
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃*
        ↥(ClassicalBlocks.GUFull m Q E))) := by
  classical
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  exact omegaBlockModel_of_isPrimAdjIdemIn hf Φ hΦ h8 hb hodd hε hJ'

end CFSG.StandardType.RCKRP
