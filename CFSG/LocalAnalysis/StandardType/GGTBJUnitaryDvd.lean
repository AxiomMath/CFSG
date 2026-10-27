module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryTorusCard
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitary
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitaryDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySix
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeAPermutationDatumLE3
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeAParabolicLE3
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUBlock
public import CFSG.LocalAnalysis.StandardType.GGTBJLinearSplitA
public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag

theorem ggTBJUnitary_sideDatum_of_block
    {G : Type} [Group G] [Finite G] {p r f : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hr : 3 ≤ r)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : ↥(unitarySU 2 f F (r + 1)) →* X} (hM : UnitTB.Model ψ)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F, LineU.ActsDiagU ψ a t)
    (S : Finset (Fin (r + 1))) (hS2 : 2 ≤ S.card) (hSr : S.card ≤ r)
    (hc3 : r + 1 - S.card ≤ 3)
    (hJ : J = (TableBUE.blockSU (K := F) (n := f) S).map (X.subtype.comp ψ)) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, c = r + 1 - S.card := ⟨_, rfl⟩
  have hScard : S.card = r + 1 - c := by omega
  have hc1 : 1 ≤ c := by omega
  have hres := ggResSideDatumLE3_of_diagonal_unitary_block hF hf hp2 hpq hr hc1
    (by omega : c ≤ 3) (by omega) hBs hSC hN hM hdiag S hScard hJ
  by_cases hc1' : c = 1
  · exact Or.inl (hres.1 hc1')
  · exact Or.inr (hres.2 (by omega))

private theorem ggTBJUnitDvd_core
    {G : Type} [Group G] [Finite G] {p r f : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hr : 4 ≤ r)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : ↥(unitarySU 2 f F (r + 1)) →* X} (hM : UnitTB.Model ψ)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F, LineU.ActsDiagU ψ a t)
    (hBsCard : p ^ r ≤ Nat.card Bs)
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3)
    (hfix : ∀ b : Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (S : Finset (Fin (r + 1))) (hS2 : 2 ≤ S.card)
    (hJ : J = (TableBUE.blockSU (K := F) (n := f) S).map (X.subtype.comp ψ)) (hJX : J ≠ X) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  have hSle : S.card ≤ r + 1 := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hSr : S.card ≤ r := by
    by_contra hSgt
    have hSuniv : S = Finset.univ :=
      Finset.eq_univ_of_card S (by simpa only [Fintype.card_fin] using (by omega : S.card = r + 1))
    apply hJX
    rw [hJ, hSuniv, SUTorus.blockSU_univ, ← MonoidHom.range_eq_map, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ hM.surj, Subgroup.map_top, Subgroup.range_subtype]
  have hc3 : r + 1 - S.card ≤ 3 := by
    obtain ⟨c, hc⟩ : ∃ c, c = r + 1 - S.card := ⟨_, rfl⟩
    have hScard : S.card = r + 1 - c := by omega
    have hcr : c ≤ r := by omega
    have hrc : 1 ≤ r - c := by omega
    obtain ⟨V, hVadd, hVmod, ι, φ', h', α', hlin', hrefl', hpair', ⟨e, he⟩, hclos', hJgen'⟩ :=
      exists_adapted_weyl_datum_of_diagonal_unitary_block_corank hF hf hp2 hpq (by omega) hcr hrc
        hBs hSC hN hM hdiag S hScard hJ
    let : AddCommGroup V := hVadd
    let : Module (ZMod p) V := hVmod
    have := ggCorank_le_three_of_datum hcr ι φ' h' α' hlin' hJgen' hBsCard hCJ hfix
    omega
  exact ggTBJUnitary_sideDatum_of_block hF hf hp2 hpq (by omega) hBs hSC hN hM hdiag S hS2 hSr
    hc3 hJ

private theorem eq_three_of_dvd_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ 5 + 1) :
    p = 3 := by
  have h6 : p ∣ 2 * 3 := by simpa using hd
  rcases (Nat.Prime.dvd_mul hp).mp h6 with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h

private theorem exists_diagonal_cover_unitaryDvd_L
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : ¬ (r = 5 ∧ f = 1)) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* L),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r + 1) → F, LineU.ActsDiagU φ a t := by
  by_cases h5 : r = 5
  · subst h5
    have hf : f ≠ 1 := fun hf1 => hr5 ⟨rfl, hf1⟩
    have hp3 : p = 3 := eq_three_of_dvd_six Fact.out hH.1.1.2.2.2.2.2.1.2.1 hpd
    subst hp3
    exact exists_diagonal_cover_of_unitary_six_L hRig hH hf hpq hLab hΛ
  · exact exists_diagonal_cover_of_large_unitary_side hRig hH (Or.inl rfl) hr h5 hpq hpd hLab hΛ

private theorem exists_diagonal_cover_unitaryDvd_K
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : ¬ (r = 5 ∧ f = 1)) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* K),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin (r + 1) → F, LineU.ActsDiagU φ a t := by
  by_cases h5 : r = 5
  · subst h5
    have hf : f ≠ 1 := fun hf1 => hr5 ⟨rfl, hf1⟩
    have hp3 : p = 3 := eq_three_of_dvd_six Fact.out hH.1.1.2.2.2.2.2.1.2.1 hpd
    subst hp3
    have hpJ : 3 ∣ Nat.card J := hSP G 3 B x L D J hH.1.1 hH.1.2.2
    exact exists_diagonal_cover_of_unitary_six_side hRig hLB hH (Or.inr rfl) hf hpq hLab hΛ hpJ
  · exact exists_diagonal_cover_of_large_unitary_side hRig hH (Or.inr ⟨y, hH.2.2.2.2.1⟩) hr h5 hpq
      hpd hLab hΛ

theorem ggResHyp_J_ne_L {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : J ≠ L := by
  have hp : p.Prime := Fact.out
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := hH.1.1.2.2.2.2.2.2.1.2.2.1
  intro hJL
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hH.1.2.2.1.2.2.2.2.2.2
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  rw [hJL, inf_centralizer_eq_zpowers_of_sstar hp hH.1.1.2.2.2.2.2.2.1] at hD
  rw [hD, Nat.card_zpowers, orderOf_eq_prime (hH.1.2.1.2.1.2 x hxBs) hx1] at hDcard
  have : 1 < p := hp.one_lt
  nlinarith

theorem ggResHyp_J_ne_K {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : J ≠ K := by
  have hp : p.Prime := Fact.out
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hnb.1.2.1
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  intro hJK'
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hH.1.2.2.1.2.2.2.2.2.2
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  rw [hJK'] at hD
  have hle : D ≤ Subgroup.zpowers y := by
    rw [hD]
    exact inf_centralizer_le_zpowers_of_sHat hnb.1
  have h1 : Nat.card D ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hle
  rw [hDcard, Nat.card_zpowers, orderOf_eq_prime (hBs.2 y hyBs) hy1] at h1
  have : 1 < p := hp.one_lt
  nlinarith

theorem ggTBJLeft_unitary_of_cover
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hf : 1 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {φ : ↥(unitarySU 2 f F (r + 1)) →* L} (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r + 1) → F, LineU.ActsDiagU φ a t) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hcardA : p ^ (r + 1 - 2) ≤ Nat.card ↥(ggGamma L hN).range :=
    card_ggGamma_range_ge_of_unitary_model hp hF hf hpq (by omega) hN hSC hM hdiag
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := hH.1.1.2.2.2.2.2.2.1.2.2.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hH.1.tableB_facts.2.2.2.1 hl) x rfl).symm
  have hBsCard : p ^ r ≤ Nat.card Bs := by
    have h1 := card_range_ggGamma_mul_prime_le hp hBs hN hxBs hx1 hxC
    calc p ^ r = p ^ (r + 1 - 2) * p := by rw [← pow_succ]; congr 1; omega
      _ ≤ Nat.card ↥(ggGamma L hN).range * p := Nat.mul_le_mul_right _ hcardA
      _ ≤ Nat.card Bs := h1
  have hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hH.1.2.2.1.2.2.2.2.2.1
  have hDB : D ≤ Bs := hH.1.2.2.1.1.trans hH.1.2.1.1
  obtain ⟨S, hJblock, hS2⟩ := exists_block_of_diagonal_unitary_component (by omega : 2 ≤ r)
    hf hpq hBs hN hF hM hdiag (SetLike.coe_subset_coe.mpr hDB) hJ
  have hfix : ∀ b : Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) :=
    fun b hb => hH.unitary_J_fix_mem_centralizer_of_L hM hdiag b hb
  exact ggTBJUnitDvd_core hF hf hp2 hpq hr hBs hSC hN hM hdiag hBsCard
    hH.1.card_bstar_inf_centralizer_J_le hfix S hS2 hJblock (ggResHyp_J_ne_L hH)

theorem ggTBJLeft_unitaryDvd_of_label
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : ¬ (r = 5 ∧ f = 1)) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  classical
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_unitaryDvd_L hRig hH hr hr5 hpq hpd hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  exact ggTBJLeft_unitary_of_cover hH hr hΛ.1 hpq hF hN hM hdiag

theorem ggTBJLeft_unitaryCoprime_of_label
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : ¬ (r = 5 ∧ f = 1)) (hpq : p ∣ 2 ^ f + 1) (hpd : ¬ p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  classical
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_of_large_unitary_L_coprime hRig hH hr (not_and_or.mp hr5) hpq hpd hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  exact ggTBJLeft_unitary_of_cover hH hr hΛ.1 hpq hF hN hM hdiag

theorem ggTBJNbr_unitary_of_cover
    (hI3 : GGNbrSubcomponentInput) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hf : 1 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    {φ : ↥(unitarySU 2 f F (r + 1)) →* K} (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin (r + 1) → F, LineU.ActsDiagU φ a t) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hcardA : p ^ (r + 1 - 2) ≤ Nat.card ↥(ggGamma K hN).range :=
    card_ggGamma_range_ge_of_unitary_model hp hF hf hpq (by omega) hN hSC hM hdiag
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hyB
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hyC : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hnb.1.2.2.2.1 hk) y rfl).symm
  have hBsCard : p ^ r ≤ Nat.card Bs := by
    have h1 := card_range_ggGamma_mul_prime_le hp hBs hN hyBs hy1 hyC
    calc p ^ r = p ^ (r + 1 - 2) * p := by rw [← pow_succ]; congr 1; omega
      _ ≤ Nat.card ↥(ggGamma K hN).range * p := Nat.mul_le_mul_right _ hcardA
      _ ≤ Nat.card Bs := h1
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hnb
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  have hxD : x ∈ D := hH.1.2.2.1.2.2.2.1
  have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hxD)
  obtain ⟨S, hJblock, hS2⟩ := exists_block_of_diagonal_unitary_component (by omega : 2 ≤ r)
    hf hpq hBs hN hF hM hdiag (Set.singleton_subset_iff.mpr hx) hcomp
  have hfix : ∀ b : Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) :=
    fun b hb => hH.unitary_J_fix_mem_centralizer_of_K hLB hSP hM hdiag b hb
  exact ggTBJUnitDvd_core hF hf hp2 hpq hr hBs hSC hN hM hdiag hBsCard
    hH.1.card_bstar_inf_centralizer_J_le hfix S hS2 hJblock (ggResHyp_J_ne_K hH)

theorem ggTBJNbr_unitaryDvd_of_label
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : ¬ (r = 5 ∧ f = 1)) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  classical
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_unitaryDvd_K hRig hLB hSP hH hr hr5 hpq hpd hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  exact ggTBJNbr_unitary_of_cover hI3 hLB hSP hH hr hΛ.1 hpq hF hN hM hdiag

theorem ggTBJNbr_unitaryCoprime_of_label
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : ¬ (r = 5 ∧ f = 1)) (hpq : p ∣ 2 ^ f + 1) (hpd : ¬ p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  classical
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_of_large_unitary_side_coprime hRig hH (Or.inr ⟨y, hH.2.2.2.2.1⟩) hr
      (not_and_or.mp hr5) hpq hpd hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  exact ggTBJNbr_unitary_of_cover hI3 hLB hSP hH hr hΛ.1 hpq hF hN hM hdiag

theorem ggTBJLeftOn_unitaryDvd
    (hRig : GGLabelRigidInput) :
    GGTBJLeftOn ggTBJUnitaryDvdLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hL _hX
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨htag, hr, hr5, hpq, hpd⟩ := hP.1
  have hlab : lab = ⟨.twA, lab.rank, lab.n⟩ := by
    rcases lab with ⟨t, r, n⟩
    simp only at htag
    subst htag
    rfl
  have hΛ' : LargeEvenInLambda2 (⟨.twA, lab.rank, lab.n⟩ : LargeEvenLabel) := by
    rw [← hlab]
    exact hΛ
  have hhas' : GGHasLabel (⟨.twA, lab.rank, lab.n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L) := by
    rw [← hlab]
    exact hhas
  rcases ggTBJLeft_unitaryDvd_of_label hRig hH hr hr5 hpq hpd hhas' hΛ' with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJNbrOn_unitaryDvd
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) :
    GGTBJNbrOn ggTBJUnitaryDvdLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hK _hX
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hK
  obtain ⟨htag, hr, hr5, hpq, hpd⟩ := hP.1
  have hlab : lab = ⟨.twA, lab.rank, lab.n⟩ := by
    rcases lab with ⟨t, r, n⟩
    simp only at htag
    subst htag
    rfl
  have hΛ' : LargeEvenInLambda2 (⟨.twA, lab.rank, lab.n⟩ : LargeEvenLabel) := by
    rw [← hlab]
    exact hΛ
  have hhas' : GGHasLabel (⟨.twA, lab.rank, lab.n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) := by
    rw [← hlab]
    exact hhas
  rcases ggTBJNbr_unitaryDvd_of_label hRig hI3 hLB hSP hH hr hr5 hpq hpd hhas' hΛ' with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJOrderRestSplitA_of_restUnitDvd
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (h : GGTBJOrderRestSplitAUnitDvdInput) : GGTBJOrderRestSplitAInput :=
  GGTBJOrdinaryOutside.of_proved (ggTBJLeftOn_unitaryDvd hRig)
    (ggTBJNbrOn_unitaryDvd hRig hI3 hLB hSP) h

end CFSG.StandardType

end
