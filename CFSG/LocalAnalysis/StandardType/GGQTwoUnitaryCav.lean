module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdField
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUTwo
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavQuotient
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavImage
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModelCoprime
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdCent
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13UnitaryDvdNorm
public import CFSG.LocalAnalysis.StandardType.GGTDModelUPerm
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitaryAutomizer
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavImageOrder
public import CFSG.LocalAnalysis.StandardType.GGQTwoUnitaryRealization
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavHeartImage

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.StandardType CFSG.StandardType.LineU CFSG.StandardType.TableBUE
open CFSG.StandardType.UnitTB CFSG.StandardType.UnitAct CFSG.StandardType.InndiagSU
open CFSG.StandardType.QTwoCav

public section

namespace CFSG.StandardType.QTwoUnitaryCav


variable {G : Type} [Group G] [Finite G] {p : ℕ}
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem diag_mem_gamma (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] {n d : ℕ}
    {φ : ↥(unitarySU 2 n K d) →* L}
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, ActsDiagU φ a t)
    {Dmat : ↥(unitarySU 2 n K d)} {u : Fin d → K}
    (hD : ((Dmat : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u)
    (hu : ∀ i, u i ^ p = 1) :
    MulAut.conj (φ Dmat) ∈ (ggGamma L hN).range :=
  UnitTB.conj_mem_of_selfCent (gamma_hyps hS hN).2 hdiag hD hu

theorem perm_mem_normalizer_gamma (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] {n d : ℕ}
    {φ : ↥(unitarySU 2 n K d) →* L} (hM : UnitTB.Model φ)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hd : 3 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, ActsDiagU φ a t)
    (σ : Equiv.Perm (Fin d)) :
    MulAut.conj (φ (LineU.permSU hM.field σ)) ∈
      Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut L)) :=
  unitDvd_conj_perm_mem_normalizer hM hp hpq hd
    (fun a ha => (gamma_hyps hS hN).1.2 a ha) (gamma_hyps hS hN).2 hdiag σ

end CFSG.StandardType.QTwoUnitaryCav

namespace CFSG.StandardType.QTwoUnitaryCav

variable {G : Type} [Group G] [Finite G]

theorem card_fixingSubgroup_compl_four {d : ℕ} (S : Finset (Fin d)) (hS4 : 4 ≤ S.card) :
    4 ∣ Nat.card ↥(fixingSubgroup (Equiv.Perm (Fin d)) ((S : Set (Fin d))ᶜ)) := by
  classical
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS4
  let pT : Fin d → Prop := fun i => i ∈ (T : Set (Fin d))
  let e : Equiv.Perm {i // pT i} →* Equiv.Perm (Fin d) := Equiv.Perm.ofSubtype (p := pT)
  have he_inj : Function.Injective e := Equiv.Perm.ofSubtype_injective (p := pT)
  have hPTle : e.range ≤ fixingSubgroup (Equiv.Perm (Fin d)) ((S : Set (Fin d))ᶜ) := by
    intro y hy
    obtain ⟨f, rfl⟩ := hy
    rw [mem_fixingSubgroup_iff]
    intro i hi
    exact Equiv.Perm.ofSubtype_apply_of_not_mem f (fun hiT => hi (hTS hiT))
  have hcardPT : Nat.card ↥e.range = Nat.card (Equiv.Perm {i // pT i}) := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective he_inj, Subgroup.card_top]
  have hcardDom : Nat.card {i // pT i} = 4 := by
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hTcard]
  have h4PT : 4 ∣ Nat.card ↥e.range := by
    rw [hcardPT, Nat.card_perm, hcardDom]
    norm_num
  exact dvd_trans h4PT (Subgroup.card_dvd_of_le hPTle)

theorem block_image_automizer_four {K : Type} [Field K] [Finite K] {n d p : ℕ}
    {X : Subgroup G} {ψ : ↥(unitarySU 2 n K d) →* X} (hM : UnitTB.Model ψ)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d)
    {A : Subgroup (MulAut X)} (hA : IsElemAbelian p A)
    (hsc : GGTorusSelfCent p A) (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU ψ a t)
    (S : Finset (Fin d)) (hS4 : 4 ≤ S.card) :
    4 ∣ Nat.card ↥(ggAutomizer
      (((TableBUE.blockSU (K := K) (n := n) S).map ψ).map
        (MulAut.conj : X →* MulAut X)) A) := by
  classical
  obtain ⟨ρ, hρinj, -, hρeq⟩ :=
    exists_permAut_unitary hM hK hp hp2 hpq hd hA hsc hdiag
  set H : Subgroup (Equiv.Perm (Fin d)) :=
    fixingSubgroup (Equiv.Perm (Fin d)) ((S : Set (Fin d))ᶜ) with hH
  have h4H : 4 ∣ Nat.card ↥H := card_fixingSubgroup_compl_four S hS4
  have hcardmap : Nat.card ↥(H.map ρ) = Nat.card ↥H :=
    Subgroup.card_map_of_injective hρinj
  have h4map : 4 ∣ Nat.card ↥(H.map ρ) := by rwa [hcardmap]
  have hle : H.map ρ ≤ ggAutomizer
      (((TableBUE.blockSU (K := K) (n := n) S).map ψ).map
        (MulAut.conj : X →* MulAut X)) A := by
    rintro _ ⟨σ, hσH, rfl⟩
    have hfix : ∀ i ∉ S, σ i = i := (mem_fixingSubgroup_iff _).mp hσH
    have hperm : LineU.permSU hM.field σ ∈ TableBUE.blockSU (K := K) (n := n) S :=
      UnitAct.permSU_mem_blockSU_of_fixes_compl (S := S) hfix
    have hψmem : ψ (LineU.permSU hM.field σ) ∈
        (TableBUE.blockSU (K := K) (n := n) S).map ψ := ⟨_, hperm, rfl⟩
    have hconjmem : MulAut.conj (ψ (LineU.permSU hM.field σ)) ∈
        ((TableBUE.blockSU (K := K) (n := n) S).map ψ).map
          (MulAut.conj : X →* MulAut X) := ⟨_, hψmem, rfl⟩
    have hNA : MulAut.conj (ψ (LineU.permSU hM.field σ)) ∈
        Subgroup.normalizer (A : Set (MulAut X)) :=
      unitDvd_conj_perm_mem_normalizer hM hp hpq (by omega) hA.2 hsc hdiag σ
    rw [hρeq σ hNA]
    exact ggConjAut_mem_ggAutomizer hconjmem hNA
  exact dvd_trans h4map (Subgroup.card_dvd_of_le hle)

end CFSG.StandardType.QTwoUnitaryCav

namespace CFSG.StandardType.QTwoUnitaryCav

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem actual_block_image_automizer_four (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] {n d : ℕ}
    {ψ : ↥(unitarySU 2 n K d) →* L} (hM : UnitTB.Model ψ)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, ActsDiagU ψ a t)
    (S : Finset (Fin d)) (hS4 : 4 ≤ S.card) :
    4 ∣ Nat.card ↥(ggAutomizer
      (((TableBUE.blockSU (K := K) (n := n) S).map ψ).map
        (MulAut.conj : L →* MulAut L)) ((ggGamma L hN).range)) :=
  block_image_automizer_four hM hK hp hp2 hpq hd
    (gamma_hyps hS hN).1 (gamma_hyps hS hN).2 hdiag S hS4

theorem exists_diagModel_coprime_actual (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] {n d : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d)
    (hcov : LineU.UnitaryCoverAt n d K)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 n K d))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ ψ : ↥(unitarySU 2 n K d) →* L, UnitTB.Model ψ ∧
      ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, ActsDiagU ψ a t := by
  classical
  have hperf : commutator L = ⊤ := hS.2.1.1
  have hA : IsElemAbelian p (ggGamma L hN).range := (gamma_hyps hS hN).1
  have hAI : ∀ a ∈ (ggGamma L hN).range,
      ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L, x (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨φ, hφI, hind⟩ := h3 b⁻¹ (Subgroup.inv_mem _ b.2)
    have hφeq : φ = ggLAut L θ ⟨b, hN b.2⟩ := by
      have h := eq_ggLAut_of_induces L θ (hN (Subgroup.inv_mem _ b.2)) hind
      simpa using h
    have hβI : ggBeta L θ hN b ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
      rw [ggBeta_eq, ← hφeq]
      exact hφI
    exact ⟨ggBeta L θ hN b, hβI, fun l => ggBeta_ggQuotHom L hN θ b l⟩
  obtain ⟨ψ, hψs, hψker, hdiag⟩ :=
    LineU.exists_diagModel_coprime (ψ := ggQuotHom θ) hK hn hd hp hpq hpd hcov
      (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf hA hAI
  exact ⟨ψ, ⟨TableBU.unitaryFieldData_of_card hK hn, hψs, hψker⟩, hdiag⟩

end CFSG.StandardType.QTwoUnitaryCav

namespace CFSG.StandardType.QTwoUnitaryCav

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem heart_le_gamma (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] {n d : ℕ}
    {ψ : ↥(unitarySU 2 n K d) →* L}
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, ActsDiagU ψ a t) :
    Subgroup.closure (UnitTB.heartSetU ψ p) ≤ (ggGamma L hN).range := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨D, u, hD, hu, rfl⟩
  exact UnitTB.conj_mem_of_selfCent (gamma_hyps hS hN).2 hdiag hD hu

theorem exists_induced_mem_of_h3 (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] {n d : ℕ}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 n K d))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∀ a ∈ (ggGamma L hN).range,
      ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L, x (ggQuotHom θ l) = ggQuotHom θ (a l) := by
  rintro _ ⟨b, rfl⟩
  obtain ⟨φ, hφI, hind⟩ := h3 b⁻¹ (Subgroup.inv_mem _ b.2)
  have hφeq : φ = ggLAut L θ ⟨b, hN b.2⟩ := by
    have h := eq_ggLAut_of_induces L θ (hN (Subgroup.inv_mem _ b.2)) hind
    simpa using h
  refine ⟨ggBeta L θ hN b, ?_, fun l => ggBeta_ggQuotHom L hN θ b l⟩
  rw [ggBeta_eq, ← hφeq]
  exact hφI

theorem exists_diagModel_dvd_actual (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] {n d : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d)
    (hcov : LineU.UnitaryCoverAt n d K)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 n K d))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hcard : p ^ (d / p + 2) ≤ Nat.card (ggGamma L hN).range) :
    ∃ ψ : ↥(unitarySU 2 n K d) →* L, UnitTB.Model ψ ∧
      ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, ActsDiagU ψ a t := by
  classical
  have hperf : commutator L = ⊤ := hS.2.1.1
  have hA : IsElemAbelian p (ggGamma L hN).range := (gamma_hyps hS hN).1
  have hAI := exists_induced_mem_of_h3 (K := K) (n := n) (d := d) hN θ h3
  obtain ⟨ψ, hψs, hψker, hdiag⟩ :=
    LineU.exists_diagModel (ψ := ggQuotHom θ) hK hn hd hp hpq hpd hcov
      (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf hA hAI hcard
  exact ⟨ψ, ⟨TableBU.unitaryFieldData_of_card hK hn, hψs, hψker⟩, hdiag⟩

end CFSG.StandardType.QTwoUnitaryCav

namespace CFSG.StandardType.QTwoUnitaryCav

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem actual_cav_local_of_model (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] {n d : ℕ}
    {ψ : ↥(unitarySU 2 n K d) →* L} (hM : UnitTB.Model ψ)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, ActsDiagU ψ a t)
    (S : Finset (Fin d)) (hS4 : 4 ≤ S.card) :
    Subgroup.closure (UnitTB.heartSetU ψ p) ≤ (ggGamma L hN).range ∧
      (∀ σ : Equiv.Perm (Fin d),
        MulAut.conj (ψ (LineU.permSU hM.field σ)) ∈
          Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut L))) ∧
      4 ∣ Nat.card ↥(ggAutomizer
        (((TableBUE.blockSU (K := K) (n := n) S).map ψ).map
          (MulAut.conj : L →* MulAut L)) ((ggGamma L hN).range)) :=
  ⟨heart_le_gamma hS hN hdiag,
    fun σ => perm_mem_normalizer_gamma hS hN hM hp hpq (by omega) hdiag σ,
    actual_block_image_automizer_four hS hN hM hK hp hp2 hpq hd hdiag S hS4⟩

theorem four_dvd_component_image_of_block_eq (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] {n d : ℕ}
    {ψ : ↥(unitarySU 2 n K d) →* L} (hM : UnitTB.Model ψ)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, ActsDiagU ψ a t)
    {S : Finset (Fin d)} (hS4 : 4 ≤ S.card)
    (hJ : (J.subgroupOf L).map (MulAut.conj : L →* MulAut L) =
      ((TableBUE.blockSU (K := K) (n := n) S).map ψ).map
        (MulAut.conj : L →* MulAut L)) :
    4 ∣ Nat.card ↥(ggAutomizer ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L))
      ((ggGamma L hN).range)) := by
  rw [hJ]
  exact actual_block_image_automizer_four hS hN hM hK hp hp2 hpq hd hdiag S hS4

end CFSG.StandardType.QTwoUnitaryCav

namespace CFSG.StandardType.QTwoUnitaryCav

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem unitary_full_cav_local
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {d : ℕ} (hd : 5 ≤ d) (hpd : ¬ p ∣ d)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K d))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K d))
        (LargeEvenGUSet (Fin d) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (S : Finset (Fin d)) (hS4 : 4 ≤ S.card) :
    ∃ (ψ : ↥(unitarySU 2 1 K d) →* L) (hM : UnitTB.Model ψ),
      (∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, ActsDiagU ψ a t) ∧
      Subgroup.closure (UnitTB.heartSetU ψ p) ≤ (ggGamma L hN).range ∧
      (∀ σ : Equiv.Perm (Fin d),
        MulAut.conj (ψ (LineU.permSU hM.field σ)) ∈
          Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut L))) ∧
      4 ∣ Nat.card ↥(ggAutomizer
        (((TableBUE.blockSU (K := K) (n := 1) S).map ψ).map
          (MulAut.conj : L →* MulAut L)) ((ggGamma L hN).range)) := by
  classical
  have hp : p.Prime := hp3 ▸ Nat.prime_three
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  have hpq : p ∣ 2 ^ 1 + 1 := by rw [hp3]; norm_num
  have hd6 : (d, 1) ≠ (6, 1) := by
    rintro ⟨rfl, -⟩
    exact hpd (by rw [hp3]; norm_num)
  have hcov : UnitaryCoverAt 1 d K := unitaryCoverAt hK hd hd6
  obtain ⟨ψ, hM, hdiag⟩ :=
    exists_diagModel_coprime_actual hS hN hK (by norm_num) (by omega) hp hpq hpd hcov θ h3
  obtain ⟨hheart, hperm, hfour⟩ :=
    actual_cav_local_of_model (n := 1) hS hN hM hK hp hp2 hpq (by omega) hdiag S hS4
  exact ⟨ψ, hM, hdiag, hheart, hperm, hfour⟩

theorem unitary_heart_cav_local
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {d : ℕ} (hd : 9 ≤ d) (hpd : p ∣ d)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K d))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K d))
        (LargeEvenGUSet (Fin d) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ (d - 2))
    (S : Finset (Fin d)) (hS4 : 4 ≤ S.card) :
    ∃ (ψ : ↥(unitarySU 2 1 K d) →* L) (hM : UnitTB.Model ψ),
      (∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, ActsDiagU ψ a t) ∧
      Subgroup.closure (UnitTB.heartSetU ψ p) ≤ (ggGamma L hN).range ∧
      (∀ σ : Equiv.Perm (Fin d),
        MulAut.conj (ψ (LineU.permSU hM.field σ)) ∈
          Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut L))) ∧
      4 ∣ Nat.card ↥(ggAutomizer
        (((TableBUE.blockSU (K := K) (n := 1) S).map ψ).map
          (MulAut.conj : L →* MulAut L)) ((ggGamma L hN).range)) := by
  classical
  have hp : p.Prime := hp3 ▸ Nat.prime_three
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  have hpq : p ∣ 2 ^ 1 + 1 := by rw [hp3]; norm_num
  have hd6 : (d, 1) ≠ (6, 1) := by
    rintro ⟨rfl, -⟩
    omega
  have hcov : UnitaryCoverAt 1 d K := unitaryCoverAt hK (by omega) hd6
  have hcard : p ^ (d / p + 2) ≤ Nat.card (ggGamma L hN).range := by
    rw [gamma_card hN, hidx, hp3]
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  obtain ⟨ψ, hM, hdiag⟩ :=
    exists_diagModel_dvd_actual hS hN hK (by norm_num) (by omega) hp hpq hpd hcov θ h3 hcard
  obtain ⟨hheart, hperm, hfour⟩ :=
    actual_cav_local_of_model (n := 1) hS hN hM hK hp hp2 hpq (by omega) hdiag S hS4
  exact ⟨ψ, hM, hdiag, hheart, hperm, hfour⟩

end CFSG.StandardType.QTwoUnitaryCav

end

public section

namespace CFSG.StandardType.QTwoUnitaryCav

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem four_dvd_original_automizer_of_block (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] {n d : ℕ}
    {ψ : ↥(unitarySU 2 n K d) →* L} (hM : UnitTB.Model ψ)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, ActsDiagU ψ a t)
    {S : Finset (Fin d)} (hS4 : 4 ≤ S.card)
    (hJ : (J.subgroupOf L).map (MulAut.conj : L →* MulAut L) =
      ((TableBUE.blockSU (K := K) (n := n) S).map ψ).map
        (MulAut.conj : L →* MulAut L)) :
    4 ∣ Nat.card ↥(ggAutomizer J Bs) :=
  dvd_trans (four_dvd_component_image_of_block_eq hS hN hM hK hp hp2 hpq hd hdiag hS4 hJ)
    (QTwoCav.card_automizer_inner_image_dvd_of_setting hN hS hp hp2)

end CFSG.StandardType.QTwoUnitaryCav

end

public section

namespace CFSG.StandardType.QTwoUnitaryCav

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.StandardType CFSG.StandardType.TableBUE CFSG.StandardType.InndiagSU
open CFSG.SectionRank.OddCover
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.StandardType CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

variable {K : Type} [Field K] [Finite K] {d : ℕ}
  {h : UnitaryFieldData 2 1 K} {Q : GL (Fin d) K}
  {hQ : Q ∈ primeFormUnitary h (idGram K d)}

theorem isSemilin_conj_frameMk (P : ↥(unitarySU 2 1 K d)) :
    IsSemilin (frameMk h Q hQ) (MulAut.conj (frameMk h Q hQ P)) (P : GL (Fin d) K) 1 := by
  intro v w hvw
  rw [MulAut.conj_apply]
  calc frameMk h Q hQ P * frameMk h Q hQ v * (frameMk h Q hQ P)⁻¹
      = frameMk h Q hQ (P * v * P⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = frameMk h Q hQ w := by
      congr 1
      exact Subtype.ext hvw.symm

theorem prod_weight_eq_one_of_inner (hK : Nat.card K = (2 ^ 1) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ 1) ≠ (3, 2)) (hp : Nat.Prime 3) (hpq : 3 ∣ 2 ^ 1 + 1)
    (u : ↥(unitarySU 2 1 K d))
    {σ : Fin d → Kˣ} (hσn : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1)
    (hfr : FrameAct h Q hQ (MulAut.conj (frameMk h Q hQ u)) σ) (h3d : 3 ∣ d) :
    ∏ k, (σ k : K) = 1 := by
  classical
  have hconj : IsSemilin (frameMk h Q hQ)
      (MulAut.conj (frameMk h Q hQ u)) u 1 := by
    intro v w hvw
    rw [MulAut.conj_apply]
    calc frameMk h Q hQ u * frameMk h Q hQ v * (frameMk h Q hQ u)⁻¹
        = frameMk h Q hQ (u * v * u⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = frameMk h Q hQ w := by
        congr 1
        exact Subtype.ext hvw.symm
  have hconj_inv : IsSemilin (frameMk h Q hQ) (MulAut.conj (frameMk h Q hQ u))⁻¹ u⁻¹ 1 := by
    intro v w hvw
    have h1 : frameMk h Q hQ v = MulAut.conj (frameMk h Q hQ u) (frameMk h Q hQ w) := by
      rw [hconj w v]
      · have hw : (w : GL (Fin d) K) =
            (u : GL (Fin d) K)⁻¹ * (v : GL (Fin d) K) * (u : GL (Fin d) K) := by
          simpa only [inv_inv, map_one, MulAut.one_apply] using hvw
        rw [hw]
        simp only [map_one, MulAut.one_apply]
        group
    rw [h1]
    exact MulAut.inv_apply_self _ (MulAut.conj (frameMk h Q hQ u)) (frameMk h Q hQ w)
  have hu : (u : GL (Fin d) K) ∈ primeFormUnitary h (idGram K d) :=
    unitarySU_le_primeFormUnitary h
      (show (u : GL (Fin d) K) ∈ unitarySU 2 1 K d from u.2)
  have hNmem : diagHom d σ * u⁻¹ ∈ primeFormUnitary h (idGram K d) :=
    Subgroup.mul_mem _ (diagHom_mem_primeFormUnitary h hσn) (Subgroup.inv_mem _ hu)
  have h1 : IsSemilin (frameMk h Q hQ) 1 (diagHom d σ * u⁻¹) 1 := by
    have hm := IsSemilin.mul h (φ := 1) (ψ := 1) (B := diagHom d σ) (C := u⁻¹)
      hfr hconj_inv (Subgroup.inv_mem _ hu)
    simpa [mul_inv_cancel, mul_assoc] using hm
  obtain ⟨c, hcN⟩ := mem_scalars_of_isSemilin_one h hK hd hdq hp hpq Q hQ hNmem h1
  have hdu : ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 :=
    ((mem_unitarySU_iff h).mp u.2).1
  have hduinv : (((u⁻¹ : ↥(unitarySU 2 1 K d)) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K).det = 1 :=
    ((mem_unitarySU_iff h).mp
      (show (u⁻¹ : GL (Fin d) K) ∈ unitarySU 2 1 K d from Subgroup.inv_mem _ u.2)).1
  have hdetN : ((diagHom d σ * u⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K).det = ∏ k, (σ k : K) := by
    rw [Units.val_mul, Matrix.det_mul, det_diagHom, hduinv, mul_one]
  have hdetc : ((Matrix.GeneralLinearGroup.scalar (Fin d) c :
      GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = (c : K) ^ d := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  haveI : NeZero d := ⟨by omega⟩
  have hc3 : (c : K) ^ 3 = 1 := by
    have hcU : Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ primeFormUnitary h (idGram K d) := by
      rw [hcN]
      exact hNmem
    have h1 := (SUTorus.scalar_mem_primeFormUnitary_iff h c).mp hcU
    rw [h.bar_apply] at h1
    have h2 : (c : K) ^ 2 * c = 1 := by simpa using h1
    calc (c : K) ^ 3 = (c : K) ^ 2 * c := by ring
      _ = 1 := h2
  have hcd : (c : K) ^ d = 1 := by
    obtain ⟨k, rfl⟩ := h3d
    rw [pow_mul, hc3, one_pow]
  calc ∏ k, (σ k : K) = ((diagHom d σ * u⁻¹ : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K).det := hdetN.symm
    _ = ((Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K).det := by rw [hcN]
    _ = (c : K) ^ d := hdetc
    _ = 1 := hcd



end CFSG.StandardType.QTwoUnitaryCav

public section

namespace CFSG.StandardType.QTwoUnitaryCav

open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.StandardType CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

variable {K : Type} [Field K] [Finite K] {d : ℕ}
  {h : UnitaryFieldData 2 1 K} {Q : GL (Fin d) K}
  {hQ : Q ∈ primeFormUnitary h (idGram K d)}
  {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))}
  {σ : Fin d → Kˣ}

@[expose] noncomputable def qTwoFramePerm :
    Equiv.Perm (Fin d) →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))) where
  toFun π := MulAut.conj (frameMk h Q hQ (LineU.permSU h π))
  map_one' := by
    rw [UnitAct.permSU_one, map_one, map_one]
  map_mul' π τ := by
    rw [UnitAct.permSU_mul, map_mul, map_mul]

theorem frameAct_qTwoFramePerm
    (hσn : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1)
    (he : FrameAct h Q hQ e σ) (π : Equiv.Perm (Fin d)) :
    FrameAct h Q hQ
      (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) π * e *
        (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) π)⁻¹)
      (σ ∘ ⇑π.symm) := by
  classical
  have hmatGL : (LineU.permSU h π : GL (Fin d) K) * (diagHom d σ : GL (Fin d) K) *
      ((LineU.permSU h π : GL (Fin d) K))⁻¹ =
        (diagHom d (σ ∘ ⇑π.symm) : GL (Fin d) K) := by
    apply Units.ext
    simp only [Units.val_mul, coe_diagHom, coe_permGL_matrix, coe_permGL_inv_matrix]
    exact permMatrix_conj_diag π (fun i => (σ i : K))
  have hP : (LineU.permSU h π : GL (Fin d) K) ∈
      primeFormUnitary h (idGram K d) :=
    TableBUE.unitarySU_le_primeFormUnitary h (LineU.permSU h π).2
  have hconj := isSemilin_conj_frameMk (h := h) (Q := Q) (hQ := hQ) (LineU.permSU h π)
  have hinv := CFSG.StandardType.TableBUD.IsSemilin.inv hconj
  have h1 := hconj.mul h he (TableBUD.diagHom_mem_primeFormUnitary h hσn)
  have h2 := h1.mul h hinv (Subgroup.inv_mem _ hP)
  rw [show (1 : K ≃+* K) * 1 * 1⁻¹ = 1 from by group] at h2
  simp only [map_one, MulAut.one_apply, inv_one, one_mul, mul_one] at h2
  rw [hmatGL] at h2
  exact h2


variable {G : Type} [Group G] [Finite G] {p : ℕ}
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem heart_inner_frame_prod_one [Fact p.Prime]
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo p lab) (htag : lab.tag = .twA)
    (h3d : 3 ∣ lab.rank + 1) (hd6 : 6 ≤ lab.rank + 1)
    (hdq : (lab.rank + 1, 2 ^ 1) ≠ (3, 2))
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ (lab.rank - 1))
    (M : GGQ2LDatum p Bs L x) (hM : M.HeartShape)
    (hxC : x ∈ Subgroup.centralizer (L : Set G)) :
    ∃ (K : Type) (hfield : Field K), letI := hfield;
      ∃ (hfin : Finite K), letI := hfin;
      ∃ (h : UnitaryFieldData 2 1 K),
      ∃ (hK : Nat.card K = (2 ^ 1) ^ 2),
      ∃ (θ : L ⧸ Subgroup.center L ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ 1)))
        (hN : Bs ≤ Subgroup.normalizer (L : Set G))
        (Q : GL (Fin (lab.rank + 1)) K)
        (hQ : Q ∈ primeFormUnitary h (idGram K (lab.rank + 1))),
        (∀ e ∈ (ggBeta L θ hN).range, ∃ σ : Fin (lab.rank + 1) → Kˣ,
          σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
          (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
          (∏ k, ((σ k : Kˣ) : K)) = 1 ∧
          TableBUD.FrameAct h Q hQ e σ) ∧
        Nat.card ↥(TableBUD.frameWeights h Q hQ (by omega) 3
          (ggBeta L θ hN).range) = 3 ^ ((lab.rank + 1) - 2) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  have hpq : p ∣ 2 ^ 1 + 1 := by rw [hp3]; norm_num
  obtain ⟨K, hfield, hfin, h, hK, θ, hN, Q, hQ, hfr, hcardW⟩ :=
    QTwoUnitary.exists_frame_of_marking_twA_heart hS hp3 hq2 htag h3d hmark hidx
  letI := hfield
  letI := hfin
  have hinner := GGQ2LDatum.beta_image_inner_of_heartShape M hp2 hN hM hxC θ
  refine ⟨K, hfield, hfin, h, hK, θ, hN, Q, hQ, ?_, hcardW⟩
  intro e he
  obtain ⟨σ, hσ0, hσ3, hσn, hfrσ⟩ := hfr e he
  obtain ⟨r, hr⟩ := hinner he
  obtain ⟨u, rfl⟩ := frameMk_surjective h Q hQ r
  have hfr' : TableBUD.FrameAct h Q hQ (MulAut.conj (frameMk h Q hQ u)) σ := by
    rw [← hr] at hfrσ
    exact hfrσ
  have hprod : ∏ k, ((σ k : Kˣ) : K) = 1 :=
    prod_weight_eq_one_of_inner (K := K) (d := lab.rank + 1) hK (by omega) hdq
      (hp3 ▸ hp) (hp3 ▸ hpq) u hσn hfr' (by simpa using h3d)
  exact ⟨σ, hσ0, hσ3, hσn, hprod, hfrσ⟩

end CFSG.StandardType.QTwoUnitaryCav

public section

namespace CFSG.StandardType.QTwoUnitaryCav

open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open Finset

@[expose] def unitProductHom {K : Type} [Field K] (d : ℕ) : (Fin d → Kˣ) →* Kˣ where
  toFun σ := ∏ k, σ k
  map_one' := by simp
  map_mul' σ τ := by
    change (∏ k, (σ k * τ k)) = (∏ k, σ k) * (∏ k, τ k)
    rw [Finset.prod_mul_distrib]

@[expose] def normalizedWeightSubgroup {K : Type} [Field K] {d : ℕ} (hd : 1 ≤ d) :
    Subgroup (Fin d → Kˣ) where
  carrier := {σ | σ ⟨0, hd⟩ = 1}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    change (a * b) ⟨0, hd⟩ = 1
    rw [Pi.mul_apply, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    change (a⁻¹) ⟨0, hd⟩ = 1
    rw [Pi.inv_apply, ha, inv_one]

@[expose] def heartWeightSubgroup {K : Type} [Field K] {d : ℕ} (hd : 1 ≤ d) :
    Subgroup (Fin d → Kˣ) :=
  normalizedWeightSubgroup (K := K) hd ⊓ (unitProductHom (K := K) d).ker

theorem mem_heartWeightSubgroup {K : Type} [Field K] {d : ℕ} {hd : 1 ≤ d}
    {σ : Fin d → Kˣ} : σ ∈ heartWeightSubgroup (K := K) hd ↔
      σ ⟨0, hd⟩ = 1 ∧ (∏ k, σ k) = 1 := Iff.rfl

theorem card_heartWeightSubgroup {K : Type} [Field K] [Finite K] {d : ℕ}
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hd : 2 ≤ d) :
    Nat.card ↥(heartWeightSubgroup (K := K) (by omega : 1 ≤ d)) = 3 ^ (d - 2) := by
  classical
  set T := normalizedWeightSubgroup (K := K) (by omega : 1 ≤ d) with hT
  set f : T →* Kˣ := (unitProductHom (K := K) d).comp T.subtype with hf
  have hker : f.ker = (T ⊓ (unitProductHom (K := K) d).ker).subgroupOf T := by
    ext σ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      exact ⟨σ.2, h⟩
    · rintro ⟨-, h⟩
      exact h
  have hsurj : Function.Surjective f := by
    intro c
    classical
    let j : Fin d := ⟨1, by omega⟩
    let σ : Fin d → Kˣ := Function.update 1 j c
    have hσ0 : σ ⟨0, by omega⟩ = 1 := by
      simp [σ, Function.update, j]
    refine ⟨⟨σ, hσ0⟩, ?_⟩
    change (∏ k, σ k) = c
    rw [Finset.prod_eq_single j]
    · simp [σ, Function.update]
    · intro b _ hb
      simp [σ, Function.update, hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hrange] at hcard
  have hTcard : Nat.card ↥T = 3 ^ (d - 1) := by
    rw [hT]
    exact QTwoUnitary.card_normalized_weights (K := K) hK (by omega)
  have hKunits : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hK]; norm_num
  rw [Subgroup.card_top, hKunits, hTcard] at hcard
  have h3 : 3 ^ (d - 1) = 3 ^ (d - 2) * 3 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h3] at hcard
  have hcardker : Nat.card ↥f.ker = 3 ^ (d - 2) :=
    Nat.eq_of_mul_eq_mul_right (by norm_num) hcard
  have hheart : Nat.card ↥(heartWeightSubgroup (K := K) (by omega : 1 ≤ d)) =
      Nat.card ↥f.ker := by
    rw [heartWeightSubgroup, ← hT, hker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  rw [hheart, hcardker]


variable {K : Type} [Field K] [Finite K] {d : ℕ}
  {h : UnitaryFieldData 2 1 K} {Q : GL (Fin d) K}
  {hQ : Q ∈ primeFormUnitary h (idGram K d)}

theorem frameWeights_eq_heartWeight
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))))}
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hd3 : 3 ≤ d)
    (hdq : (d, 2 ^ 1) ≠ (3, 2)) (hp : Nat.Prime 3) (hpq : 3 ∣ 2 ^ 1 + 1)
    (hinner : ∀ e ∈ E, ∃ u : ↥(unitarySU 2 1 K d),
      e = MulAut.conj (frameMk h Q hQ u))
    (hfr : ∀ e ∈ E, ∃ σ : Fin d → Kˣ,
      σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
      (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
      TableBUD.FrameAct h Q hQ e σ)
    (h3d : 3 ∣ d)
    (hcardW : Nat.card ↥(TableBUD.frameWeights h Q hQ (by omega) 3 E) = 3 ^ (d - 2)) :
    TableBUD.frameWeights h Q hQ (by omega) 3 E = heartWeightSubgroup (by omega : 1 ≤ d) := by
  classical
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro σ hσ
    rw [TableBUD.frameWeights, Subgroup.mem_mk] at hσ
    obtain ⟨hσ0, hσp, hσn, e, he, hfrσ⟩ := hσ
    obtain ⟨u, rfl⟩ := hinner e he
    have hprod : ∏ k, ((σ k : Kˣ) : K) = 1 :=
      prod_weight_eq_one_of_inner hK hd3 hdq hp hpq u hσn hfrσ h3d
    refine Subgroup.mem_inf.mpr ⟨hσ0, ?_⟩
    rw [MonoidHom.mem_ker]
    rw [show (unitProductHom (K := K) d) σ = ∏ k, σ k from rfl]
    apply Units.ext
    rw [Units.coe_prod, hprod, Units.val_one]
  · rw [hcardW, card_heartWeightSubgroup hK (by omega)]

theorem heartWeightSubgroup_perm
    {hd : 1 ≤ d} (hK : Nat.card K = (2 ^ 1) ^ 2) (h3d : 3 ∣ d)
    {σ : Fin d → Kˣ} (hσ : σ ∈ heartWeightSubgroup (K := K) hd)
    (π : Equiv.Perm (Fin d)) :
    (fun k => (σ (π⁻¹ ⟨0, hd⟩))⁻¹ * σ (π⁻¹ k)) ∈
      heartWeightSubgroup (K := K) hd := by
  rw [heartWeightSubgroup, Subgroup.mem_inf] at hσ ⊢
  obtain ⟨hσ0, hσprod⟩ := hσ
  constructor
  · change (fun k => (σ (π⁻¹ ⟨0, hd⟩))⁻¹ * σ (π⁻¹ k)) ⟨0, hd⟩ = 1
    simp
  · rw [MonoidHom.mem_ker] at hσprod ⊢
    rw [show (unitProductHom (K := K) d) σ = ∏ k, σ k from rfl] at hσprod
    change (∏ k, (σ (π⁻¹ ⟨0, hd⟩))⁻¹ * σ (π⁻¹ k)) = 1
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hreindex : ∏ k, σ (π⁻¹ k) = ∏ k, σ k :=
      Equiv.prod_comp π⁻¹ σ
    rw [hreindex, hσprod, mul_one]
    have hσ3 : (σ (π⁻¹ ⟨0, hd⟩)) ^ 3 = 1 := by
      have h : (σ (π⁻¹ ⟨0, hd⟩) : Kˣ) ^ Nat.card Kˣ = 1 :=
        pow_card_eq_one' (x := σ (π⁻¹ ⟨0, hd⟩))
      rwa [show Nat.card Kˣ = 3 by rw [Nat.card_units, hK]; norm_num] at h
    have hc3 : ((σ (π⁻¹ ⟨0, hd⟩))⁻¹) ^ 3 = 1 := by
      rw [inv_pow, hσ3, inv_one]
    obtain ⟨m, rfl⟩ := h3d
    rw [pow_mul, hc3, one_pow]

variable {G : Type} [Group G] [Finite G] {p : ℕ}
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem heart_inner_frame_weights_eq_of_le_sup_zpowers [Fact p.Prime]
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo p lab) (htag : lab.tag = .twA)
    (h3d : 3 ∣ lab.rank + 1) (hd6 : 6 ≤ lab.rank + 1)
    (hdq : (lab.rank + 1, 2 ^ 1) ≠ (3, 2))
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ (lab.rank - 1))
    (hBs : Bs ≤ L ⊔ Subgroup.zpowers x)
    (hxC : x ∈ Subgroup.centralizer (L : Set G)) :
    ∃ (K : Type) (hfield : Field K), letI := hfield;
      ∃ (hfin : Finite K), letI := hfin;
      ∃ (h : UnitaryFieldData 2 1 K),
      ∃ (hK : Nat.card K = (2 ^ 1) ^ 2),
      ∃ (θ : L ⧸ Subgroup.center L ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ 1)))
        (hN : Bs ≤ Subgroup.normalizer (L : Set G))
        (Q : GL (Fin (lab.rank + 1)) K)
        (hQ : Q ∈ primeFormUnitary h (idGram K (lab.rank + 1))),
        (∀ e ∈ (ggBeta L θ hN).range,
          ∃ σ : Fin (lab.rank + 1) → Kˣ,
            σ ∈ heartWeightSubgroup (K := K) (by omega) ∧
            TableBUD.FrameAct h Q hQ e σ) ∧
        (∀ σ : Fin (lab.rank + 1) → Kˣ,
          σ ∈ heartWeightSubgroup (K := K) (by omega) →
            ∃ e ∈ (ggBeta L θ hN).range, TableBUD.FrameAct h Q hQ e σ) ∧
        TableBUD.frameWeights h Q hQ (by omega) 3 (ggBeta L θ hN).range =
          heartWeightSubgroup (K := K) (by omega) := by
  classical
  obtain ⟨K, hfield, hfin, h, hK, θ, hN, Q, hQ, hfr, hcardW⟩ :=
    QTwoUnitary.exists_frame_of_marking_twA_heart hS hp3 hq2 htag h3d hmark hidx
  letI := hfield
  letI := hfin
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  have hpq : p ∣ 2 ^ 1 + 1 := by rw [hp3]; norm_num
  have hinnerRange := beta_image_inner_of_le_sup_zpowers hN hBs hxC θ
  have hinner : ∀ e ∈ (ggBeta L θ hN).range,
      ∃ u : ↥(unitarySU 2 1 K (lab.rank + 1)),
        e = MulAut.conj (frameMk h Q hQ u) := by
    intro e he
    obtain ⟨r, hr⟩ := hinnerRange he
    obtain ⟨u, rfl⟩ := frameMk_surjective h Q hQ r
    exact ⟨u, hr.symm⟩
  have hfr0 : ∀ e ∈ (ggBeta L θ hN).range,
      ∃ σ : Fin (lab.rank + 1) → Kˣ,
        σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
        TableBUD.FrameAct h Q hQ e σ := by
    intro e he
    obtain ⟨σ, hσ0, hσ3, hσn, hfrσ⟩ := hfr e he
    exact ⟨σ, hσ0, hσ3, hσn, hfrσ⟩
  have heq : TableBUD.frameWeights h Q hQ (by omega) 3 (ggBeta L θ hN).range =
      heartWeightSubgroup (K := K) (by omega) :=
    frameWeights_eq_heartWeight hK (by omega) hdq (hp3 ▸ hp) (hp3 ▸ hpq)
      hinner hfr0 (by simpa using h3d) hcardW
  refine ⟨K, hfield, hfin, h, hK, θ, hN, Q, hQ, ?_, ?_, heq⟩
  · intro e he
    obtain ⟨σ, hσ0, hσ3, hσn, hfrσ⟩ := hfr e he
    obtain ⟨u, heu⟩ := hinner e he
    have hfrσ' : TableBUD.FrameAct h Q hQ (MulAut.conj (frameMk h Q hQ u)) σ := by
      rw [← heu]
      exact hfrσ
    have hprodK : ∏ k, ((σ k : Kˣ) : K) = 1 :=
      prod_weight_eq_one_of_inner hK (by omega) hdq (hp3 ▸ hp) (hp3 ▸ hpq)
        u hσn hfrσ' (by simpa using h3d)
    refine ⟨σ, ?_, hfrσ⟩
    refine Subgroup.mem_inf.mpr ⟨hσ0, ?_⟩
    rw [MonoidHom.mem_ker]
    rw [show (unitProductHom (K := K) (lab.rank + 1)) σ = ∏ k, σ k from rfl]
    apply Units.ext
    rw [Units.coe_prod, hprodK, Units.val_one]
  · intro σ hσ
    have hσW : σ ∈ TableBUD.frameWeights h Q hQ (by omega) 3 (ggBeta L θ hN).range := by
      rw [heq]; exact hσ
    rw [TableBUD.frameWeights, Subgroup.mem_mk] at hσW
    obtain ⟨-, -, -, e, he, hfrσ⟩ := hσW
    exact ⟨e, he, hfrσ⟩

variable {K : Type} [Field K] [Finite K] {d : ℕ}
  {h : UnitaryFieldData 2 1 K} {Q : GL (Fin d) K}
  {hQ : Q ∈ primeFormUnitary h (idGram K d)}

theorem qTwoFramePerm_mem_normalizer
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))))}
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hd3 : 3 ≤ d)
    (hdq : (d, 2 ^ 1) ≠ (3, 2)) (hp : Nat.Prime 3) (hpq : 3 ∣ 2 ^ 1 + 1)
    (hinner : ∀ e ∈ E, ∃ u : ↥(unitarySU 2 1 K d),
      e = MulAut.conj (frameMk h Q hQ u))
    (hfr : ∀ e ∈ E, ∃ σ : Fin d → Kˣ,
      σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
      (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
      TableBUD.FrameAct h Q hQ e σ)
    (h3d : 3 ∣ d)
    (hcardW : Nat.card ↥(TableBUD.frameWeights h Q hQ (by omega) 3 E) = 3 ^ (d - 2))
    (π : Equiv.Perm (Fin d)) :
    qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) π ∈
      Subgroup.normalizer (E : Set (MulAut
        (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))))) := by
  classical
  have heq : TableBUD.frameWeights h Q hQ (by omega) 3 E =
      heartWeightSubgroup (K := K) (by omega : 1 ≤ d) :=
    frameWeights_eq_heartWeight hK hd3 hdq hp hpq hinner hfr h3d hcardW
  have hmem : ∀ (τ : Equiv.Perm (Fin d)) (e : MulAut
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))), e ∈ E →
      qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ * e *
        (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ)⁻¹ ∈ E := by
    intro τ e he
    obtain ⟨σ, hσ0, hσ3, hσn, hfrσ⟩ := hfr e he
    obtain ⟨u, heu⟩ := hinner e he
    let e0 : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))) :=
      MulAut.conj (frameMk h Q hQ u)
    have hfrσ0 : TableBUD.FrameAct h Q hQ e0 σ := by
      dsimp only [e0]
      rw [← heu]
      exact hfrσ
    have hprod : ∏ k, ((σ k : Kˣ) : K) = 1 :=
      prod_weight_eq_one_of_inner hK hd3 hdq hp hpq u hσn hfrσ0 h3d
    have hσmem : σ ∈ heartWeightSubgroup (K := K) (by omega) := by
      refine Subgroup.mem_inf.mpr ⟨hσ0, ?_⟩
      rw [MonoidHom.mem_ker]
      rw [show (unitProductHom (K := K) d) σ = ∏ k, σ k from rfl]
      apply Units.ext
      rw [Units.coe_prod, hprod, Units.val_one]
    have hτmem : (fun k => (σ (τ.symm ⟨0, by omega⟩))⁻¹ * σ (τ.symm k)) ∈
        heartWeightSubgroup (K := K) (by omega) := by
      simpa [Equiv.symm_apply_eq] using
        heartWeightSubgroup_perm (K := K) hK h3d (hd := by omega) hσmem τ
    have hτW : (fun k => (σ (τ.symm ⟨0, by omega⟩))⁻¹ * σ (τ.symm k)) ∈
        TableBUD.frameWeights h Q hQ (by omega) 3 E := by
      rw [heq]
      exact hτmem
    rw [TableBUD.frameWeights, Subgroup.mem_mk] at hτW
    obtain ⟨-, -, hτn, e', he', hfr'⟩ := hτW
    have hact : TableBUD.FrameAct h Q hQ
        (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ * e0 *
          (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ)⁻¹) (σ ∘ ⇑τ.symm) :=
      frameAct_qTwoFramePerm hσn hfrσ0 τ
    have hact' : TableBUD.FrameAct h Q hQ
        (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ * e0 *
          (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ)⁻¹)
        (fun k => (σ (τ.symm ⟨0, by omega⟩))⁻¹ * σ (τ.symm k)) := by
      simpa [Function.comp] using
        hact.smul ((σ (τ.symm ⟨0, by omega⟩))⁻¹)
    have huniq := TableBUD.FrameAct.unique hτn hact' hfr'
    have hgoal : qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ * e0 *
        (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ)⁻¹ ∈ E := by
      rw [huniq]
      exact he'
    simpa only [heu, e0] using hgoal
  rw [Subgroup.mem_normalizer_iff]
  intro e
  constructor
  · intro he
    exact hmem π e he
  · intro he
    have hπinv : qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) π⁻¹ =
        (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) π)⁻¹ :=
      map_inv (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ)) π
    have h := hmem (π⁻¹)
      (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) π * e *
        (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) π)⁻¹) he
    simpa [hπinv, mul_assoc] using h


variable {G : Type} [Group G] [Finite G] {p : ℕ}
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem heart_framePerm_mem_normalizer_of_le_sup_zpowers [Fact p.Prime]
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo p lab) (htag : lab.tag = .twA)
    (h3d : 3 ∣ lab.rank + 1) (hd6 : 6 ≤ lab.rank + 1)
    (hdq : (lab.rank + 1, 2 ^ 1) ≠ (3, 2))
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ (lab.rank - 1))
    (hBs : Bs ≤ L ⊔ Subgroup.zpowers x)
    (hxC : x ∈ Subgroup.centralizer (L : Set G))
    (π : Equiv.Perm (Fin (lab.rank + 1))) :
    ∃ (K : Type) (hfield : Field K), letI := hfield;
      ∃ (hfin : Finite K), letI := hfin;
      ∃ (h : UnitaryFieldData 2 1 K),
      ∃ (hK : Nat.card K = (2 ^ 1) ^ 2),
      ∃ (θ : L ⧸ Subgroup.center L ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ 1)))
        (hN : Bs ≤ Subgroup.normalizer (L : Set G))
        (Q : GL (Fin (lab.rank + 1)) K)
        (hQ : Q ∈ primeFormUnitary h (idGram K (lab.rank + 1))),
        qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) π ∈
          Subgroup.normalizer ((ggBeta L θ hN).range :
            Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ 1))))) := by
  classical
  obtain ⟨K, hfield, hfin, h, hK, θ, hN, Q, hQ, hfr, hcardW⟩ :=
    QTwoUnitary.exists_frame_of_marking_twA_heart hS hp3 hq2 htag h3d hmark hidx
  letI := hfield
  letI := hfin
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  have hpq : p ∣ 2 ^ 1 + 1 := by rw [hp3]; norm_num
  have hinnerRange := beta_image_inner_of_le_sup_zpowers hN hBs hxC θ
  have hinner : ∀ e ∈ (ggBeta L θ hN).range,
      ∃ u : ↥(unitarySU 2 1 K (lab.rank + 1)),
        e = MulAut.conj (frameMk h Q hQ u) := by
    intro e he
    obtain ⟨r, hr⟩ := hinnerRange he
    obtain ⟨u, rfl⟩ := frameMk_surjective h Q hQ r
    exact ⟨u, hr.symm⟩
  have hfr0 : ∀ e ∈ (ggBeta L θ hN).range,
      ∃ σ : Fin (lab.rank + 1) → Kˣ,
        σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
        TableBUD.FrameAct h Q hQ e σ := by
    intro e he
    obtain ⟨σ, hσ0, hσ3, hσn, hfrσ⟩ := hfr e he
    exact ⟨σ, hσ0, hσ3, hσn, hfrσ⟩
  refine ⟨K, hfield, hfin, h, hK, θ, hN, Q, hQ, ?_⟩
  exact qTwoFramePerm_mem_normalizer (E := (ggBeta L θ hN).range)
    hK (by omega) hdq (hp3 ▸ hp) (hp3 ▸ hpq) hinner hfr0
    (by simpa using h3d) hcardW π


open CFSG.SectionRank.OddCover (diagHom)

theorem exists_quotient_J_block_of_le_sup_zpowers [Fact p.Prime]
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo p lab) (htag : lab.tag = .twA)
    (h3d : 3 ∣ lab.rank + 1) (hd6 : 6 ≤ lab.rank + 1)
    (hdq : (lab.rank + 1, 2 ^ 1) ≠ (3, 2))
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ (lab.rank - 1))
    (hsup : Bs ≤ L ⊔ Subgroup.zpowers x)
    (hxC : x ∈ Subgroup.centralizer (L : Set G)) :
    ∃ (K : Type) (hfield : Field K), letI := hfield;
      ∃ (hfin : Finite K), letI := hfin;
      ∃ (h : UnitaryFieldData 2 1 K),
      ∃ (hK : Nat.card K = (2 ^ 1) ^ 2),
      ∃ (θ : L ⧸ Subgroup.center L ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ 1)))
        (hN : Bs ≤ Subgroup.normalizer (L : Set G))
        (Q : GL (Fin (lab.rank + 1)) K)
        (hQ : Q ∈ primeFormUnitary h (idGram K (lab.rank + 1)))
        (I : Finset (Fin (lab.rank + 1))),
        4 ≤ I.card ∧
        (J.subgroupOf L).map (ggQuotHom θ) =
          (TableBUE.blockSU (K := K) (n := 1) I).map (frameMk h Q hQ) ∧
        (∀ e ∈ (ggBeta L θ hN).range, ∃ σ : Fin (lab.rank + 1) → Kˣ,
          σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
          (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
          TableBUD.FrameAct h Q hQ e σ) ∧
        (∀ e ∈ (ggBeta L θ hN).range,
          ∃ u : ↥(unitarySU 2 1 K (lab.rank + 1)),
            e = MulAut.conj (frameMk h Q hQ u)) ∧
        (∀ e ∈ (ggBeta L θ hN).range, ∃ σ : Fin (lab.rank + 1) → Kˣ,
          σ ∈ heartWeightSubgroup (K := K) (by omega) ∧
          TableBUD.FrameAct h Q hQ e σ) ∧
        Nat.card ↥(TableBUD.frameWeights h Q hQ (by omega) 3
          (ggBeta L θ hN).range) = 3 ^ ((lab.rank + 1) - 2) ∧
        TableBUD.frameWeights h Q hQ (by omega) 3 (ggBeta L θ hN).range =
          heartWeightSubgroup (K := K) (by omega) := by
  classical
  have hp : p.Prime := by rw [hp3]; exact Nat.prime_three
  have hpq : p ∣ 2 ^ 1 + 1 := by rw [hp3]; norm_num
  obtain ⟨K, hfield, hfin, h, hK, θ, hN, Q, hQ, hfr, hcardW⟩ :=
    QTwoUnitary.exists_frame_of_marking_twA_heart hS hp3 hq2 htag h3d hmark hidx
  letI := hfield
  letI := hfin
  have hDL : D ≤ Subgroup.normalizer (L : Set G) := QTwoCav.d_le_normalizer hS hN
  have hstd : LargeEvenStdSub p B x L D J := hS.1.1.2.2
  have hpre : LargeEvenStdSubPre p B x L D J := hstd.1
  obtain ⟨-, -, -, -, -, hJcomp, -⟩ := hpre
  have hJq : IsComponentOf ((J.subgroupOf L).map (ggQuotHom θ))
      (⨅ d : D, ggFix (ggBeta L θ hDL d)) :=
    QTwoCav.isComponentOf_quotient_image (hDL := hDL) (θ := θ) hJcomp
  obtain ⟨d, hd1, hdgen, hdiInf⟩ :=
    QTwoCav.exists_beta_d_generator (θ := θ) hp hS hN
  have hJq' : IsComponentOf ((J.subgroupOf L).map (ggQuotHom θ))
      (ggFix (ggBeta L θ hDL d)) := by
    rwa [hdiInf] at hJq
  have hDB : D ≤ B := hstd.1.1
  have hBBs : B ≤ Bs := hS.1.1.2.1.1
  have hDleBs : D ≤ Bs := hDB.trans hBBs
  have hβDmem : ggBeta L θ hDL d ∈ (ggBeta L θ hN).range :=
    range_ggBeta_le θ hDleBs hDL hN (MonoidHom.mem_range.mpr ⟨d, rfl⟩)
  have hfrD := hfr (ggBeta L θ hDL d) hβDmem
  obtain ⟨σ, hσ0, hσ3, hσn, hfrσ⟩ := hfrD
  have hβinner : (ggBeta L θ hN).range ≤
      (MulAut.conj : LargeEvenProj
        (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ 1)) →*
          MulAut (LargeEvenProj
            (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ 1)))).range :=
    beta_image_inner_of_le_sup_zpowers (R := LargeEvenProj
      (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ 1))) hN hsup hxC θ
  obtain ⟨y, hy⟩ := hβinner hβDmem
  have hfrσ' : TableBUD.FrameAct h Q hQ (MulAut.conj y) σ := by
    rw [hy]
    exact hfrσ
  have hmemSu : (y, diagHom (lab.rank + 1) σ) ∈
      SUTorus.suPairs (frameMk h Q hQ) := by
    refine ⟨?_, ?_⟩
    · exact SUTorus.mem_normalizer_of_mem_primeFormUnitary h
        (TableBUD.diagHom_mem_primeFormUnitary h hσn)
    · intro u v hv
      have h := hfrσ' u v hv
      simpa [MulAut.conj_apply] using h
  have hKqcomp : IsComponentOf ((J.subgroupOf L).map (ggQuotHom θ))
      ((frameMk h Q hQ).range ⊓
        Subgroup.centralizer ({y} : Set (LargeEvenProj
          (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ 1))))) := by
    have hfix : ggFix (ggBeta L θ hDL d) =
        Subgroup.centralizer ({y} : Set (LargeEvenProj
          (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ 1)))) := by
      have hfix0 : ggFix (ggBeta L θ hDL d) = ggFix (MulAut.conj y) :=
        congrArg ggFix hy.symm
      rw [hfix0]
      ext x
      rw [mem_ggFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        have h' : y * x = x * y := by
          calc y * x = (y * x * y⁻¹) * y := by group
            _ = x * y := by rw [h]
        exact h'.symm
      · intro h
        calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [← h]
          _ = x := by group
    have hrange : (frameMk h Q hQ).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (frameMk_surjective h Q hQ)
    simpa [hfix, hrange] using hJq'
  have hker : (frameMk h Q hQ).ker ≤
      Subgroup.center ↥(unitarySU 2 1 K (lab.rank + 1)) :=
    TableBUI.ker_frameMk_le_center h Q hQ
  obtain ⟨I, hI4, -, hblock⟩ :=
    CFSG.StandardType.SUTorus.exists_blockSU_of_isComponentOf_two (m := lab.rank) h hker hmemSu hKqcomp
  have hinner : ∀ e ∈ (ggBeta L θ hN).range,
      ∃ u : ↥(unitarySU 2 1 K (lab.rank + 1)),
        e = MulAut.conj (frameMk h Q hQ u) := by
    intro e he
    have hβinnerL := beta_image_inner_of_le_sup_zpowers hN hsup hxC θ
    obtain ⟨r, hr⟩ := hβinnerL he
    obtain ⟨u, rfl⟩ := frameMk_surjective h Q hQ r
    exact ⟨u, hr.symm⟩
  have hfr0 : ∀ e ∈ (ggBeta L θ hN).range,
      ∃ σ : Fin (lab.rank + 1) → Kˣ,
        σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
        TableBUD.FrameAct h Q hQ e σ := by
    intro e he
    obtain ⟨σ, hσ0, hσ3, hσn, hfrσ⟩ := hfr e he
    exact ⟨σ, hσ0, hσ3, hσn, hfrσ⟩
  have heq : TableBUD.frameWeights h Q hQ (by omega) 3 (ggBeta L θ hN).range =
      heartWeightSubgroup (K := K) (by omega) :=
    frameWeights_eq_heartWeight hK (by omega) hdq (hp3 ▸ hp) (hp3 ▸ hpq)
      hinner hfr0 (by simpa using h3d) hcardW
  have hprodEq : ∀ e ∈ (ggBeta L θ hN).range, ∃ σ : Fin (lab.rank + 1) → Kˣ,
      σ ∈ heartWeightSubgroup (K := K) (by omega) ∧
      TableBUD.FrameAct h Q hQ e σ := by
    intro e he
    obtain ⟨σ, hσ0, hσ3, hσn, hfrσ⟩ := hfr e he
    obtain ⟨u, heu⟩ := hinner e he
    have hfrσ' : TableBUD.FrameAct h Q hQ (MulAut.conj (frameMk h Q hQ u)) σ := by
      rw [← heu]
      exact hfrσ
    have hprodK : ∏ k, ((σ k : Kˣ) : K) = 1 :=
      prod_weight_eq_one_of_inner hK (by omega) hdq (hp3 ▸ hp) (hp3 ▸ hpq)
        u hσn hfrσ' (by simpa using h3d)
    refine ⟨σ, ?_, hfrσ⟩
    refine Subgroup.mem_inf.mpr ⟨hσ0, ?_⟩
    rw [MonoidHom.mem_ker]
    rw [show (unitProductHom (K := K) (lab.rank + 1)) σ = ∏ k, σ k from rfl]
    apply Units.ext
    rw [Units.coe_prod, hprodK, Units.val_one]
  exact ⟨K, hfield, hfin, h, hK, θ, hN, Q, hQ, I, hI4, hblock,
    hfr, hinner, hprodEq, hcardW, heq⟩

end CFSG.StandardType.QTwoUnitaryCav

end