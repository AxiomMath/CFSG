module

public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_9_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Corollary 12.10(a) infrastructure

This file contains the reusable support lemmas for Corollary 12.10(a).
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section12_isMulCommutative_of_nilpotent_of_sylow
    {K : Type*} [Group K] [Finite K]
    (hnil : Group.IsNilpotent K)
    (hSyl : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p K),
      IsMulCommutative (P : Subgroup K)) :
    IsMulCommutative K := by
  classical
  let e : (∀ p : (Nat.card K).primeFactors, ∀ P : Sylow p.val K, P) ≃* K :=
    Sylow.directProductOfNormal (G := K) (fun {p} [hp : Fact p.Prime] (P : Sylow p K) =>
      Group.IsNilpotent.sylow_normal hnil p P)
  refine ⟨⟨fun x y => ?_⟩⟩
  let x' := e.symm x
  let y' := e.symm y
  have hxy' : x' * y' = y' * x' := by
    funext p P
    haveI : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    have hcomm : IsMulCommutative (P : Subgroup K) := hSyl p.val P
    exact Subtype.ext <|
      setLike_mul_comm (s := (P : Subgroup K))
        (x' p P).property (y' p P).property
  have hxy := congrArg e hxy'
  simpa [x', y'] using hxy

omit [IsMinCE G] in
public theorem CFSG.section12_primeRank_at_least_two_of_rankTwo
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    2 ≤ primeRank p.val M := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hAM : A ≤ M := section12_rankTwo_le hA
  rcases section12_rankTwo_elementary hA with ⟨hcard, hElem⟩
  haveI : IsElementaryAbelian p.val A := hElem
  have hAcomm : IsMulCommutative A := inferInstance
  let A' : Subgroup M := A.subgroupOf M
  have hA'p : IsPGroup p.val A' :=
    (IsElementaryAbelian.isPGroup p.val A).of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) hAM).symm
  have hA'comm : IsMulCommutative A' := by
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := M)
  have hgenA : 2 ≤ generatorRank A :=
    section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
      (p := p.val) hcard
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) hAM)
  have hgenA' : 2 ≤ generatorRank A' := by
    simpa [hgen_eq] using hgenA
  exact hgenA'.trans
    (section12_generatorRank_le_primeRank_of_subgroup (R := M) (q := p.val)
      (A := A') hA'p hA'comm)

omit [IsMinCE G] in
public theorem CFSG.section12_primeRank_le_one_of_cyclic_sylow
    {p : ℕ} {R : Type*} [Group R] [Finite R] [Fact p.Prime]
    (S : Sylow p R) (hS_cyc : IsCyclic (S : Subgroup R)) :
    primeRank p R ≤ 1 := by
  rw [primeRank]
  refine csSup_le ?_ ?_
  · letI : IsCyclic (S : Subgroup R) := hS_cyc
    refine ⟨0, ?_⟩
    exact ⟨(S : Subgroup R), S.isPGroup', inferInstance, by simp⟩
  · intro n hn
    rcases hn with ⟨A, hAp, _hAcomm, hnA⟩
    obtain ⟨T, hA_le_T⟩ := IsPGroup.exists_le_sylow (G := R) (p := p) hAp
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R S T
    have hT_cyc : IsCyclic (T : Subgroup R) := by
      let e :
          (S : Subgroup R) ≃* ((g • S : Sylow p R) : Subgroup R) :=
        Subgroup.equivMapOfInjective
          (f := (MulAut.conj g).toMonoidHom) (S : Subgroup R)
          (EquivLike.injective (MulAut.conj g))
      have hconj_cyc : IsCyclic (((g • S : Sylow p R) : Subgroup R)) :=
        e.isCyclic.mp hS_cyc
      rw [← hg]
      exact hconj_cyc
    have hA_cyc : IsCyclic A := Subgroup.isCyclic_of_le hA_le_T
    exact hnA.trans (generatorRank_le_one_of_isCyclic (G := A) hA_cyc)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12HallSubgroupIn_map_subtype
    {π : Set Nat.Primes} {H : Subgroup G} {K : Subgroup H}
    (hK : IsHallSubgroup π K) :
    section12HallSubgroupIn π (K.map H.subtype) H := by
  have hKH : K.map H.subtype ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  refine ⟨hKH, ?_⟩
  have hsub_eq : (K.map H.subtype).subgroupOf H = K := by
    ext x
    constructor
    · intro hx
      change ((x : H) : G) ∈ K.map H.subtype at hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
      have hy_eq : y = x := Subtype.ext hyx
      simpa [hy_eq] using hy
    · intro hx
      change ((x : H) : G) ∈ K.map H.subtype
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  simpa [hsub_eq] using hK

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_isPiSubgroup_subgroupOf
    {π : Set Nat.Primes} {H K : Subgroup G}
    (hKπ : IsPiSubgroup (G := G) π K) (hKH : K ≤ H) :
    IsPiSubgroup (G := H) π (K.subgroupOf H) := by
  intro p hp
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  exact hKπ p (by rwa [hcard] at hp)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_complementToMsigma_of_local_complement
    {M : Subgroup G} {E : Subgroup M}
    (hcomp : (section10MsigmaSubgroup M).IsComplement' E) :
    section12ComplementToMsigma M (E.map M.subtype) := by
  classical
  have hσmap :
      (section10MsigmaSubgroup M).map M.subtype = section10Msigma M := by
    simp [section10Msigma]
  have htop_map : (⊤ : Subgroup M).map M.subtype = M := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hσmap] at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  · calc
      M = (⊤ : Subgroup M).map M.subtype := htop_map.symm
      _ = (section10MsigmaSubgroup M ⊔ E).map M.subtype := by
        rw [hcomp.sup_eq_top]
      _ = section10Msigma M ⊔ E.map M.subtype := by
        rw [Subgroup.map_sup, hσmap]
  · rw [Subgroup.disjoint_def]
    intro x hxσ hxE
    rw [← hσmap] at hxσ
    rcases Subgroup.mem_map.mp hxσ with ⟨y, hyσ, hyx⟩
    rcases Subgroup.mem_map.mp hxE with ⟨z, hzE, hzx⟩
    have hyz : y = z := Subtype.ext (hyx.trans hzx.symm)
    have hyE : y ∈ E := by
      simpa [hyz] using hzE
    have hybot : y ∈ (⊥ : Subgroup M) := by
      have hinf : section10MsigmaSubgroup M ⊓ E = ⊥ :=
        hcomp.disjoint.eq_bot
      have hyinf : y ∈ section10MsigmaSubgroup M ⊓ E := ⟨hyσ, hyE⟩
      simpa [hinf] using hyinf
    have hyone : y = 1 := by
      simpa using hybot
    calc
      x = (y : M) := hyx.symm
      _ = 1 := by simpa using congrArg (fun t : M => (t : G)) hyone

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_extend_complementIn_from_complementToMsigma
    {M E K L : Subgroup G}
    (hME : section12ComplementToMsigma M E)
    (hKL : section12ComplementIn E K L) :
    section12ComplementIn M K (section10Msigma M ⊔ L) := by
  refine ⟨hKL.1.trans hME.2.1, sup_le hME.1 (hKL.2.1.trans hME.2.1), ?_, ?_⟩
  · calc
      M = section10Msigma M ⊔ E := hME.2.2.1
      _ = section10Msigma M ⊔ (K ⊔ L) := by rw [hKL.2.2.1]
      _ = K ⊔ (section10Msigma M ⊔ L) := by
        simp [sup_comm, sup_left_comm]
  · rw [Subgroup.disjoint_def]
    intro x hxK hxsup
    have hxE : x ∈ E := hKL.1 hxK
    have hLnorm : L ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
      (hKL.2.1.trans hME.2.1).trans section12_le_normalizer_msigma
    change x ∈ ((section10Msigma M ⊔ L : Subgroup G) : Set G) at hxsup
    rw [Subgroup.coe_mul_of_right_le_normalizer_left
      (N := section10Msigma M) (H := L) hLnorm, Set.mem_mul] at hxsup
    rcases hxsup with ⟨s, hsσ, l, hlL, hsl⟩
    have hlE : l ∈ E := hKL.2.1 hlL
    have hsE : s ∈ E := by
      have hs_eq : s = x * l⁻¹ := by
        calc
          s = s * (l * l⁻¹) := by simp
          _ = (s * l) * l⁻¹ := by simp [mul_assoc]
          _ = x * l⁻¹ := by rw [hsl]
      rw [hs_eq]
      exact E.mul_mem hxE (E.inv_mem hlE)
    have hsone : s = 1 := (Subgroup.disjoint_def.mp hME.2.2.2) hsσ hsE
    have hx_eq_l : x = l := by simpa [hsone] using hsl.symm
    have hxL : x ∈ L := hx_eq_l ▸ hlL
    exact (Subgroup.disjoint_def.mp hKL.2.2.2) hxK hxL

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_subgroupCentralizerIn_commute
    (A S : Subgroup G) :
    S ≤ Subgroup.centralizer (subgroupCentralizerIn A S : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  exact (Subgroup.mem_centralizer_iff.mp hc.2 s hs).symm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_E_le_normalizer_CA_msigma
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hAnorm : section10NormalIn A E) :
    E ≤ Subgroup.normalizer
      (subgroupCentralizerIn A (section10Msigma M) : Set G) := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  have hE_norm_A : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAnorm.1).mp hAnorm.2
  have hE_norm_σ : E ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hE.1.2.1.trans section12_le_normalizer_msigma
  intro e he
  have he_norm_A : e ∈ Subgroup.normalizer (A : Set G) := hE_norm_A he
  have he_norm_σ : e ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    hE_norm_σ he
  have he_inv_norm_A : e⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normalizer (A : Set G)).inv_mem he_norm_A
  have he_inv_norm_σ : e⁻¹ ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    (Subgroup.normalizer (section10Msigma M : Set G)).inv_mem he_norm_σ
  have hconj_mem :
      ∀ {x : G}, x ∈ C → e * x * e⁻¹ ∈ C := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp he_norm_A x).1 hx.1
    · change e * x * e⁻¹ ∈ Subgroup.centralizer (section10Msigma M : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyσ
      have hy_conj : e⁻¹ * y * e ∈ section10Msigma M := by
        simpa using (Subgroup.mem_normalizer_iff.mp he_inv_norm_σ y).1 hyσ
      have hcomm :
          (e⁻¹ * y * e) * x = x * (e⁻¹ * y * e) :=
        Subgroup.mem_centralizer_iff.mp hx.2 (e⁻¹ * y * e) hy_conj
      calc
        y * (e * x * e⁻¹) = e * ((e⁻¹ * y * e) * x) * e⁻¹ := by group
        _ = e * (x * (e⁻¹ * y * e)) * e⁻¹ := by rw [hcomm]
        _ = (e * x * e⁻¹) * y := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hconj_mem hx
  · intro hx
    have hx' : e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹ ∈ C := by
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp he_inv_norm_A (e * x * e⁻¹)).1 hx.1
      · change e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹ ∈
          Subgroup.centralizer (section10Msigma M : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hyσ
        have hy_conj : e * y * e⁻¹ ∈ section10Msigma M :=
          (Subgroup.mem_normalizer_iff.mp he_norm_σ y).1 hyσ
        have hcomm :
            (e * y * e⁻¹) * (e * x * e⁻¹) =
              (e * x * e⁻¹) * (e * y * e⁻¹) :=
          Subgroup.mem_centralizer_iff.mp hx.2 (e * y * e⁻¹) hy_conj
        calc
          y * (e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹) =
              e⁻¹ * ((e * y * e⁻¹) * (e * x * e⁻¹)) * e := by group
          _ = e⁻¹ * ((e * x * e⁻¹) * (e * y * e⁻¹)) * e := by rw [hcomm]
          _ = (e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹) * y := by group
    simpa [C, mul_assoc] using hx'

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_CA_msigma_normalIn_E
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hAnorm : section10NormalIn A E) :
    section10NormalIn (subgroupCentralizerIn A (section10Msigma M)) E := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  have hCE : C ≤ E := inf_le_left.trans hAnorm.1
  refine ⟨hCE, ?_⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hCE).2
    (by simpa [C] using section12_E_le_normalizer_CA_msigma (G := G) hE hAnorm)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_complementIn_of_normal_isComplement'
    {H K L : Subgroup G}
    (hKL : section12ComplementIn H K L) (hKnorm : section10NormalIn K H) :
    (L.subgroupOf H).IsComplement' (K.subgroupOf H) := by
  rcases hKL with ⟨hKH, hLH, hHsup, hdisj⟩
  have hsup_local : L.subgroupOf H ⊔ K.subgroupOf H = ⊤ := by
    calc
      L.subgroupOf H ⊔ K.subgroupOf H = (L ⊔ K).subgroupOf H := by
        symm
        exact Subgroup.subgroupOf_sup (A := L) (A' := K) (B := H) hLH hKH
      _ = ⊤ := by
        rw [sup_comm, hHsup]
        simp
  haveI : (K.subgroupOf H).Normal := hKnorm.2
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxL hxK
    apply Subtype.ext
    exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxK,
      by simpa [Subgroup.mem_subgroupOf] using hxL⟩
  · simpa [hsup_local] using
      (Subgroup.mul_normal (L.subgroupOf H) (K.subgroupOf H)).symm

public theorem CFSG.section12_exists_EData_containing_sigma_compl_piSubgroup
    {M A : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hAM : A ≤ M)
    (hAπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ A) :
    ∃ E E₁₂ E₁ E₂ E₃ : Subgroup G,
      section12EData M E E₁₂ E₁ E₂ E₃ ∧ A ≤ E := by
  classical
  let A_M : Subgroup M := A.subgroupOf M
  have hAπ_M : IsPiSubgroup (G := M) (section10SigmaPrimes M)ᶜ A_M :=
    section12_isPiSubgroup_subgroupOf hAπ hAM
  letI : MulDistribMulAction Unit M := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hAinv_M : IsInvariant Unit M A_M := by
    refine ⟨?_⟩
    intro _ x
    simp
  have hsolvM : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  have hcopM : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
  obtain ⟨Eloc, hElocHall, _hElocInv, hA_Eloc⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := Unit) hsolvM hcopM (section10SigmaPrimes M)ᶜ
      A_M hAπ_M hAinv_M
  have hσHall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
    (theorem_10_2_b (G := G) hM).2
  let E : Subgroup G := Eloc.map M.subtype
  have hEcomp : section12ComplementToMsigma M E :=
    section12_complementToMsigma_of_local_complement
      (M := M) (E := Eloc) (section11_isComplement_of_isHall_compl hσHall hElocHall)
  have hA_E : A ≤ E := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hAM hx⟩, hA_Eloc (by simpa [A_M, Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hEproper : E ≠ ⊤ := by
    intro hEtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hEtop] using hEcomp.2.1
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hsolvE : IsSolvable E :=
    IsMinCE.proper_subgroups_solvable E (lt_top_iff_ne_top.2 hEproper)
  letI : MulDistribMulAction Unit E := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hcopE : Nat.Coprime (Nat.card Unit) (Nat.card E) := by simp
  obtain ⟨E₁₂loc, hE₁₂Hall, _hE₁₂Inv⟩ :=
    exists_isHallSubgroup_isInvariant
      (G := E) (A := Unit) hsolvE hcopE
      (section12Tau1Primes M ∪ section12Tau2Primes M)
  let E₁₂ : Subgroup G := E₁₂loc.map E.subtype
  have hE₁₂HallIn :
      section12HallSubgroupIn
        (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E :=
    section12HallSubgroupIn_map_subtype (G := G) (H := E) (K := E₁₂loc) hE₁₂Hall
  have hE₁₂proper : E₁₂ ≠ ⊤ := by
    intro htop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [htop] using hE₁₂HallIn.1.trans hEcomp.2.1
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hsolvE₁₂ : IsSolvable E₁₂ :=
    IsMinCE.proper_subgroups_solvable E₁₂ (lt_top_iff_ne_top.2 hE₁₂proper)
  letI : MulDistribMulAction Unit E₁₂ := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hcopE₁₂ : Nat.Coprime (Nat.card Unit) (Nat.card E₁₂) := by simp
  obtain ⟨E₁loc, hE₁Hall, _hE₁Inv⟩ :=
    exists_isHallSubgroup_isInvariant
      (G := E₁₂) (A := Unit) hsolvE₁₂ hcopE₁₂
      (section12Tau1Primes M)
  let E₁ : Subgroup G := E₁loc.map E₁₂.subtype
  have hE₁HallIn : section12HallSubgroupIn (section12Tau1Primes M) E₁ E₁₂ :=
    section12HallSubgroupIn_map_subtype (G := G) (H := E₁₂) (K := E₁loc) hE₁Hall
  obtain ⟨E₂loc, hE₂Hall, _hE₂Inv⟩ :=
    exists_isHallSubgroup_isInvariant
      (G := E₁₂) (A := Unit) hsolvE₁₂ hcopE₁₂
      (section12Tau2Primes M)
  let E₂ : Subgroup G := E₂loc.map E₁₂.subtype
  have hE₂HallIn : section12HallSubgroupIn (section12Tau2Primes M) E₂ E₁₂ :=
    section12HallSubgroupIn_map_subtype (G := G) (H := E₁₂) (K := E₂loc) hE₂Hall
  obtain ⟨E₃loc, hE₃Hall, _hE₃Inv⟩ :=
    exists_isHallSubgroup_isInvariant
      (G := E) (A := Unit) hsolvE hcopE
      (section12Tau3Primes M)
  let E₃ : Subgroup G := E₃loc.map E.subtype
  have hE₃HallIn : section12HallSubgroupIn (section12Tau3Primes M) E₃ E :=
    section12HallSubgroupIn_map_subtype (G := G) (H := E) (K := E₃loc) hE₃Hall
  exact ⟨E, E₁₂, E₁, E₂, E₃,
    ⟨hEcomp, hE₁₂HallIn, hE₁HallIn, hE₂HallIn, hE₃HallIn⟩, hA_E⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_mem_omegaOneSubgroup_of_mem_pow_eq_one
    {H : Subgroup G} {p : Nat.Primes} {x : G}
    (hxH : x ∈ H) (hxp : x ^ p.val = 1) :
    x ∈ section12OmegaOneSubgroup p H := by
  let xH : H := ⟨x, hxH⟩
  have hxΩ : xH ∈ omega₁ (G := H) (p := p.val) := by
    rw [omega₁, omega]
    exact Subgroup.subset_closure (by simpa [xH] using hxp)
  exact Subgroup.mem_map.mpr ⟨xH, hxΩ, rfl⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_primeOrder_le_omegaOneSubgroup_of_le
    {H X : Subgroup G} {p : Nat.Primes}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p H) :
    X ≤ section12OmegaOneSubgroup p H := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXH, hXcard⟩
  intro x hxX
  have hxpowX : (⟨x, hxX⟩ : X) ^ Nat.card X = 1 := pow_card_eq_one'
  have hxpow : x ^ p.val = 1 := by
    simpa [hXcard] using congrArg Subtype.val hxpowX
  exact section12_mem_omegaOneSubgroup_of_mem_pow_eq_one (p := p) (hXH hxX) hxpow

omit [IsMinCE G] in
public theorem CFSG.section12_natCard_omegaOne_cyclic_pGroup_eq_prime
    {H : Type*} [Group H] [Finite H] {p : Nat.Primes}
    [Fact (IsPGroup p.val H)] (hcyc : IsCyclic H) [Nontrivial H] :
    Nat.card (omega₁ (G := H) (p := p.val)) = p.val := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  letI : IsCyclic H := hcyc
  letI : CommGroup H := hcyc.commGroup
  have hOmega_eq_ker : omega₁ (G := H) (p := p.val) =
      (powMonoidHom p.val : H →* H).ker := by
    apply le_antisymm
    · rw [omega₁, omega]
      refine (Subgroup.closure_le (K := (powMonoidHom p.val : H →* H).ker)).2 ?_
      intro x hx
      change x ^ (p.val ^ 1) = 1 at hx
      simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
    · intro x hx
      change x ∈ Subgroup.closure {y : H | y ^ (p.val ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
  obtain ⟨n, hn_pos, hcardH⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p.val) (G := H) (hG := Fact.out)).mp
      inferInstance
  calc
    Nat.card (omega₁ (G := H) (p := p.val))
        = Nat.card ((powMonoidHom p.val : H →* H).ker) := by rw [hOmega_eq_ker]
    _ = (Nat.card H).gcd p.val := IsCyclic.card_powMonoidHom_ker (G := H) p.val
    _ = p.val := by
      rw [hcardH]
      exact Nat.gcd_eq_right_iff_dvd.mpr
        (dvd_pow_self p.val (Nat.pos_iff_ne_zero.mp hn_pos))

omit [IsMinCE G] in
public theorem CFSG.section12_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
    {H : Subgroup G} {p : Nat.Primes}
    (hHp : IsPGroup p.val H) (hHcyc : IsCyclic H) (hHne : H ≠ ⊥) :
    Nat.card (section12OmegaOneSubgroup p H) = p.val := by
  classical
  haveI : Fact (IsPGroup p.val H) := ⟨hHp⟩
  haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hHne
  have hcard :
      Nat.card (section12OmegaOneSubgroup p H) =
        Nat.card (omega₁ (G := H) (p := p.val)) := by
    simpa [section12OmegaOneSubgroup] using
      (Subgroup.card_map_of_injective
        (K := omega₁ (G := H) (p := p.val)) (f := H.subtype) H.subtype_injective)
  exact hcard.trans
    (section12_natCard_omegaOne_cyclic_pGroup_eq_prime (H := H) (p := p) hHcyc)

omit [IsMinCE G] in
public theorem CFSG.section12_isCyclic_of_omegaOneSubgroup_card_eq_prime
    {H : Subgroup G} {p : Nat.Primes}
    (hHp : IsPGroup p.val H) (hpodd : p.val ≠ 2)
    (hOmegaH : Nat.card (section12OmegaOneSubgroup p H) = p.val) :
    IsCyclic H := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  haveI : Fact (IsPGroup p.val H) := ⟨hHp⟩
  by_contra hHcyc
  obtain ⟨A, _hAnorm, hAcard, _hAelem⟩ :=
    lemma_4_5_a (R := H) (p := p.val) hpodd hHcyc
  let Amap : Subgroup G := A.map H.subtype
  have hA_le_omega : A ≤ omega₁ (G := H) (p := p.val) := elementaryAbelian_le_omega₁
  have hAmap_le_omegaH : Amap ≤ section12OmegaOneSubgroup p H := by
    simpa [Amap, section12OmegaOneSubgroup] using
      Subgroup.map_mono (f := H.subtype) hA_le_omega
  have hAmap_card : Nat.card Amap = Nat.card A := by
    exact
      (Nat.card_congr
        (Subgroup.equivMapOfInjective
          (f := H.subtype) A H.subtype_injective).toEquiv).symm
  have hcard_le : Nat.card Amap ≤ Nat.card (section12OmegaOneSubgroup p H) :=
    Subgroup.card_le_of_le hAmap_le_omegaH
  have hp_sq_le_p : p.val ^ 2 ≤ p.val := by
    simpa [hAmap_card, hAcard, hOmegaH] using hcard_le
  have hp_lt_sq : p.val < p.val ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_left p.2.one_lt p.2.pos
  exact (not_le_of_gt hp_lt_sq) hp_sq_le_p

omit [IsMinCE G] in
public theorem CFSG.section12_omegaOneSubgroup_le_of_nontrivial_subgroup_of_cyclic_pSubgroup
    {H K : Subgroup G} {p : Nat.Primes}
    (hHp : IsPGroup p.val H) (hHcyc : IsCyclic H) (hHne : H ≠ ⊥)
    (hKH : K ≤ H) (hKne : K ≠ ⊥) :
    section12OmegaOneSubgroup p H ≤ K := by
  have hKsubp : IsPGroup p.val (K.subgroupOf H) := hHp.to_subgroup (K.subgroupOf H)
  have hKp : IsPGroup p.val K :=
    hKsubp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := K) (K := H) hKH)
  letI : IsCyclic H := hHcyc
  have hKsubcyc : IsCyclic (K.subgroupOf H) := by infer_instance
  have hKcyc : IsCyclic K :=
    (Subgroup.subgroupOfEquivOfLe (H := K) (K := H) hKH).isCyclic.mp hKsubcyc
  have hOmegaH_card :
      Nat.card (section12OmegaOneSubgroup p H) = p.val :=
    section12_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
      (G := G) (H := H) (p := p) hHp hHcyc hHne
  have hOmegaK_card :
      Nat.card (section12OmegaOneSubgroup p K) = p.val :=
    section12_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
      (G := G) (H := K) (p := p) hKp hKcyc hKne
  have hOmegaK_primeH :
      section12OmegaOneSubgroup p K ∈ section10PrimeOrderSubgroupsIn p H := by
    exact ⟨(show section12OmegaOneSubgroup p K ≤ K from by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.property).trans hKH, hOmegaK_card⟩
  have hOmegaH_primeH :
      section12OmegaOneSubgroup p H ∈ section10PrimeOrderSubgroupsIn p H :=
    ⟨show section12OmegaOneSubgroup p H ≤ H from by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.property,
      hOmegaH_card⟩
  have hOmegaK_le_OmegaH :
      section12OmegaOneSubgroup p K ≤ section12OmegaOneSubgroup p H :=
    section12_primeOrder_le_omegaOneSubgroup_of_le
      (G := G) (H := H) (X := section12OmegaOneSubgroup p K) hOmegaK_primeH
  have hOmegaK_eq_OmegaH :
      section12OmegaOneSubgroup p K = section12OmegaOneSubgroup p H := by
    exact
      Subgroup.eq_of_le_of_card_ge hOmegaK_le_OmegaH (by
        rw [hOmegaK_card, hOmegaH_card])
  intro x hx
  rw [← hOmegaK_eq_OmegaH] at hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact y.property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_omegaOneSubgroup_mono
    {H K : Subgroup G} {p : Nat.Primes} (hHK : H ≤ K) :
    section12OmegaOneSubgroup p H ≤ section12OmegaOneSubgroup p K := by
  have hmap :
      Subgroup.map (Subgroup.inclusion hHK) (omega₁ (G := H) (p := p.val)) ≤
        omega₁ (G := K) (p := p.val) := by
    rw [omega₁, omega, MonoidHom.map_closure]
    refine (Subgroup.closure_le (K := omega₁ (G := K) (p := p.val))).2 ?_
    rintro _ ⟨z, hz, rfl⟩
    exact Subgroup.subset_closure
      (by simpa [MonoidHom.coe_coe, pow_one] using congrArg (Subgroup.inclusion hHK) hz)
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  have hyK : Subgroup.inclusion hHK y ∈ omega₁ (G := K) (p := p.val) :=
    hmap (Subgroup.mem_map_of_mem (Subgroup.inclusion hHK) hy)
  exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hHK y, hyK, rfl⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_omegaOne_map_hom_le
    {R T : Type*} [Group R] [Group T] {p : ℕ} (f : R →* T) :
    (omega₁ (G := R) (p := p)).map f ≤ omega₁ (G := T) (p := p) := by
  rw [omega₁, omega, MonoidHom.map_closure]
  refine (Subgroup.closure_le (K := omega₁ (G := T) (p := p))).2 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.subset_closure (by
    simpa [pow_one, map_pow] using congrArg f hx)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_omegaOne_le_map_subtype_of_forall_pow_eq_one_mem
    {R : Type*} [Group R] {p : ℕ} (H : Subgroup R)
    (hmem : ∀ x : R, x ^ p = 1 → x ∈ H) :
    omega₁ (G := R) (p := p) ≤ (omega₁ (G := H) (p := p)).map H.subtype := by
  rw [omega₁, omega]
  refine (Subgroup.closure_le (K := (omega₁ (G := H) (p := p)).map H.subtype)).2 ?_
  intro x hx
  have hxH : x ∈ H := hmem x (by simpa [pow_one] using hx)
  have hxOmegaH : ⟨x, hxH⟩ ∈ omega₁ (G := H) (p := p) := by
    change ⟨x, hxH⟩ ∈ Subgroup.closure {y : H | y ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    simpa [pow_one] using hx
  exact Subgroup.mem_map_of_mem H.subtype hxOmegaH

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_omegaOneSubgroup_le_of_forall_pow_eq_one_mem
    {H K : Subgroup G} {p : Nat.Primes} (hKH : K ≤ H)
    (hmem : ∀ x : H, x ^ p.val = 1 → ((x : H) : G) ∈ K) :
    section12OmegaOneSubgroup p H ≤ section12OmegaOneSubgroup p K := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  let KH : Subgroup H := K.subgroupOf H
  have hle :
      omega₁ (G := H) (p := p.val) ≤
        (omega₁ (G := KH) (p := p.val)).map KH.subtype :=
    section12_omegaOne_le_map_subtype_of_forall_pow_eq_one_mem
      (R := H) (p := p.val) KH (by
        intro z hz
        exact hmem z hz)
  have hy_map : y ∈ (omega₁ (G := KH) (p := p.val)).map KH.subtype := hle hy
  rcases Subgroup.mem_map.mp hy_map with ⟨z, hz, hz_eq⟩
  let eKH : KH →* K := (Subgroup.subgroupOfEquivOfLe (H := K) (K := H) hKH).toMonoidHom
  have hzK : eKH z ∈ omega₁ (G := K) (p := p.val) :=
    section12_omegaOne_map_hom_le eKH (Subgroup.mem_map_of_mem eKH hz)
  exact Subgroup.mem_map.mpr ⟨eKH z, hzK, by
    change ((eKH z : K) : G) = ((y : H) : G)
    simpa [eKH, KH] using congrArg H.subtype hz_eq⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_pow_eq_one_mem_of_cyclic_quotient_nontrivial_image
    {R : Type*} [Group R] [Finite R] {p : Nat.Primes}
    {K L : Subgroup R} [K.Normal]
    (hquot_p : IsPGroup p.val (R ⧸ K))
    (hquot_cyc : IsCyclic (R ⧸ K))
    (hKL : K ≤ L) (hK_ne_L : K ≠ L) :
    ∀ x : R, x ^ p.val = 1 → x ∈ L := by
  classical
  let q : R →* R ⧸ K := QuotientGroup.mk' K
  let Lbar : Subgroup (R ⧸ K) := L.map q
  have hLbar_ne_bot : Lbar ≠ ⊥ := by
    intro hLbar_bot
    apply hK_ne_L
    apply le_antisymm hKL
    intro x hxL
    have hxbar : q x ∈ Lbar := Subgroup.mem_map_of_mem q hxL
    have hxone : q x = 1 := by
      have hxbot : q x ∈ (⊥ : Subgroup (R ⧸ K)) := by
        simpa [Lbar, hLbar_bot] using hxbar
      simpa using hxbot
    exact (QuotientGroup.eq_one_iff (N := K) (x := x)).1 hxone
  have htop_ne_bot : (⊤ : Subgroup (R ⧸ K)) ≠ ⊥ := by
    intro htop_bot
    exact hLbar_ne_bot (le_bot_iff.mp (by simpa [htop_bot] using (show Lbar ≤ ⊤ from le_top)))
  have htop_p : IsPGroup p.val (⊤ : Subgroup (R ⧸ K)) :=
    hquot_p.to_subgroup (⊤ : Subgroup (R ⧸ K))
  have htop_cyc : IsCyclic (⊤ : Subgroup (R ⧸ K)) := by
    letI : IsCyclic (R ⧸ K) := hquot_cyc
    infer_instance
  have homega_le_Lbar :
      section12OmegaOneSubgroup (G := R ⧸ K) p (⊤ : Subgroup (R ⧸ K)) ≤ Lbar :=
    section12_omegaOneSubgroup_le_of_nontrivial_subgroup_of_cyclic_pSubgroup
      (G := R ⧸ K) (H := ⊤) (K := Lbar) (p := p)
      htop_p htop_cyc htop_ne_bot le_top hLbar_ne_bot
  intro x hxpow
  have hxbar_pow : (q x) ^ p.val = 1 := by
    simpa [q, map_pow] using congrArg q hxpow
  have hxbar_omega :
      q x ∈ section12OmegaOneSubgroup (G := R ⧸ K) p (⊤ : Subgroup (R ⧸ K)) :=
    section12_mem_omegaOneSubgroup_of_mem_pow_eq_one
      (G := R ⧸ K) (H := ⊤) (p := p) (x := q x) (by simp) hxbar_pow
  have hxbar_Lbar : q x ∈ Lbar := homega_le_Lbar hxbar_omega
  rcases Subgroup.mem_map.mp hxbar_Lbar with ⟨l, hlL, hlx⟩
  have hlx_one : q (l⁻¹ * x) = 1 := by
    calc
      q (l⁻¹ * x) = (q l)⁻¹ * q x := by simp [q]
      _ = 1 := by rw [hlx]; simp
  have hlxK : l⁻¹ * x ∈ K :=
    (QuotientGroup.eq_one_iff (N := K) (x := l⁻¹ * x)).1 hlx_one
  have hx_eq : x = l * (l⁻¹ * x) := by group
  rw [hx_eq]
  exact L.mul_mem hlL (hKL hlxK)

public theorem CFSG.section12_isMulCommutative_of_mulEquiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : IsMulCommutative B) :
    IsMulCommutative A := by
  classical
  refine ⟨⟨fun x y => ?_⟩⟩
  letI : IsMulCommutative B := hB
  letI : CommGroup B := IsMulCommutative.instCommGroup
  apply e.injective
  calc
    e (x * y) = e x * e y := e.map_mul x y
    _ = e y * e x := mul_comm (e x) (e y)
    _ = e (y * x) := (e.map_mul y x).symm

public theorem CFSG.section12_sylow_abelian_of_sigma_compl_nilpotent_subgroup
    {M K : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ section9MaximalSubgroups G)
    (hKle : K ≤ M) (hKπ : IsPiSubgroup (section10SigmaPrimes M)ᶜ K)
    (P : Sylow p K) :
    IsMulCommutative (P : Subgroup K) := by
  classical
  let p' : Nat.Primes := ⟨p, Fact.out⟩
  by_contra hPnonab
  let Pamb : Subgroup G := (P : Subgroup K).map K.subtype
  have hPamb_p : IsPGroup p'.val Pamb := by
    simpa [p', Pamb] using IsPGroup.map (P.isPGroup') K.subtype
  have hPamb_le_K : Pamb ≤ K := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hPamb_le_M : Pamb ≤ M := hPamb_le_K.trans hKle
  have hPnoncyc : ¬ IsCyclic Pamb := by
    intro hPamb_cyc
    let e : (P : Subgroup K) ≃* Pamb :=
      Subgroup.equivMapOfInjective (f := K.subtype) (P : Subgroup K) K.subtype_injective
    have hPcyc : IsCyclic (P : Subgroup K) := e.isCyclic.2 hPamb_cyc
    letI : IsCyclic (P : Subgroup K) := hPcyc
    exact hPnonab inferInstance
  have hP_ne_bot : (P : Subgroup K) ≠ ⊥ := by
    intro hPbot
    haveI : Subsingleton (P : Subgroup K) := by
      rw [hPbot]
      infer_instance
    exact hPnonab inferInstance
  haveI : Nontrivial (P : Subgroup K) :=
    (Subgroup.nontrivial_iff_ne_bot (H := (P : Subgroup K))).2 hP_ne_bot
  have hp_dvd_P : p'.val ∣ Nat.card (P : Subgroup K) :=
    section12_prime_dvd_card_of_nontrivial_pSubgroup
      (G := K) (p := p') (B := (P : Subgroup K)) P.isPGroup' inferInstance
  have hp_dvd_K : p'.val ∣ Nat.card K :=
    hp_dvd_P.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup K))
  have hp_not_sigma : p' ∉ section10SigmaPrimes M := by
    have hp_compl : p' ∈ (section10SigmaPrimes M)ᶜ := hKπ p' hp_dvd_K
    simpa using hp_compl
  obtain ⟨A, hA_Pamb⟩ :=
    section12_exists_rankTwo_in_noncyclic_pSubgroup
      (G := G) (P := Pamb) (p := p') hPamb_p hPnoncyc
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p' M :=
    section12_rankTwo_mono hA_Pamb hPamb_le_M
  have hpM : p' ∈ subgroupPrimeSet M := section12_rankTwo_prime_mem hA_M
  have hrank_ge_two : 2 ≤ primeRank p'.val M :=
    section12_primeRank_at_least_two_of_rankTwo hA_M
  have hrank_le_two : primeRank p'.val M ≤ 2 := by
    by_contra hnot
    have hgt : 2 < primeRank p'.val M := by omega
    exact hp_not_sigma (section12_sigmaPrimes_mem_of_alphaPrimes_mem hM ⟨hpM, hgt⟩)
  have hprank : primeRank p'.val M = 2 := le_antisymm hrank_le_two hrank_ge_two
  have hpτ2 : p' ∈ section12Tau2Primes M := by
    simpa [section12Tau2Primes] using ⟨hp_not_sigma, hprank⟩
  have hM_sylow_ab : section12HasAbelianSylowSubgroups p' M :=
    (theorem_12_5_b (G := G) (M := M) (A := A) (p := p') hM hpτ2 hA_M).1
  let PsubM : Subgroup M := Pamb.subgroupOf M
  have hPsubM_p : IsPGroup p'.val PsubM :=
    hPamb_p.of_equiv (Subgroup.subgroupOfEquivOfLe (H := Pamb) (K := M) hPamb_le_M).symm
  obtain ⟨T, hPsubM_le_T⟩ := IsPGroup.exists_le_sylow (G := M) (p := p'.val) hPsubM_p
  let Tamb : Subgroup G := section10AmbientSylowSubgroup M T
  have hPamb_le_Tamb : Pamb ≤ Tamb := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hPamb_le_M hx⟩,
        hPsubM_le_T (by simpa [PsubM, Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hTamb_comm : IsMulCommutative Tamb := by
    letI : IsMulCommutative (T : Subgroup M) := hM_sylow_ab T
    change IsMulCommutative ((T : Subgroup M).map M.subtype)
    exact Subgroup.map_isMulCommutative (f := M.subtype) (H := (T : Subgroup M))
  have hPamb_comm : IsMulCommutative Pamb := by
    refine ⟨⟨fun x y => ?_⟩⟩
    exact Subtype.ext <|
      setLike_mul_comm (s := Tamb)
        (hPamb_le_Tamb x.property) (hPamb_le_Tamb y.property)
  let e : (P : Subgroup K) ≃* Pamb :=
    Subgroup.equivMapOfInjective (f := K.subtype) (P : Subgroup K) K.subtype_injective
  exact hPnonab (section12_isMulCommutative_of_mulEquiv e hPamb_comm)

end Section12

/-!
# Corollary 12.10(a)
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 12.10(a). -/
public theorem CFSG.corollary_12_10_a
    {M K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKle : K ≤ M) (hKπ : IsPiSubgroup (section10SigmaPrimes M)ᶜ K)
    (hKnil : Group.IsNilpotent K) :
    IsMulCommutative K := by
  exact section12_isMulCommutative_of_nilpotent_of_sylow hKnil
    (fun p _hp P =>
      section12_sylow_abelian_of_sigma_compl_nilpotent_subgroup
        (G := G) (M := M) (K := K) (p := p) hM hKle hKπ P)

end Section12
