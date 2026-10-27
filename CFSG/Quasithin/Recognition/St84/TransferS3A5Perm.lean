module

public import CFSG.Quasithin.Recognition.St84.TransferS3A5Setup
public import CFSG.Quasithin.Recognition.St84.TransferS3A5Count
public import CFSG.GroupTheory.CosetActionPerm
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

private lemma map_subtype_le_pCoreOf_of_isPGroup {P : Subgroup H} (M : Subgroup ↥P)
    (hM : M.Normal) (hp : IsPGroup 2 (M.map P.subtype)) : M.map P.subtype ≤ pCoreOf 2 P :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le M)
    (@CFSG.ABGLocalTools.le_normalizer_map_subtype _ _ P M hM) hp

private lemma pCoreOf_P2_eq_QA {L1 L2 S : Subgroup H} (hB : S3A5VertexId L1 L2 S) :
    pCoreOf 2 (f112P2 L1 L2 S) = pCoreOf 2 (f112saP2' L1 L2 S) := by
  have h := hB.oTwo_right
  unfold dsQ at h
  rw [bigB_comm] at h
  exact h.symm.trans hB.QA_eq

private lemma pCoreOf_P1_eq_QS {L1 L2 S : Subgroup H} (hB : S3A5VertexId L1 L2 S) :
    pCoreOf 2 (f112P1 L1 L2 S) = pCoreOf 2 L1 := by
  have h := hB.oTwo_left
  unfold dsQ at h
  exact h.symm

private theorem f112sa_le_pCoreOf_P2'_of_three_dvd
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    {N : Subgroup H} (hNB : N ≤ bigB L1 L2 S) (hNPA : N ≤ f112P2 L1 L2 S)
    (hPN : f112P2 L1 L2 S ≤ Subgroup.normalizer (N : Set H))
    (h3 : 3 ∣ Nat.card ↥N) : N ≤ pCoreOf 2 (f112saP2' L1 L2 S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hxH3 : orderOf (x : H) = 3 := (Subgroup.orderOf_coe x).trans hx3
  have hxB : (x : H) ∈ bigB L1 L2 S := hNB x.2
  have hxPA : (x : H) ∈ f112P2 L1 L2 S := hNPA x.2
  have hxodd : Odd (orderOf (x : H)) := by rw [hxH3]; norm_num
  have hxoTwo : (x : H) ∈ oTwoRes L2 :=
    f112sa_mem_oTwoRes_of_odd hF h1 hxPA hxodd
  have hxX2 : (x : H) ∈ f112saX2 L1 L2 S := ⟨hxoTwo, hxB⟩
  have hxEA : (x : H) ∈ f112saP2' L1 L2 S :=
    f112saK_le_P2' L1 L2 S (Subgroup.mem_sup_right hxX2)
  have hAE : N ⊓ f112saP2' L1 L2 S ≤ oTwoPrime (f112saP2' L1 L2 S) := by
    rw [f112sa_oTwoPrime_P2'_eq hF h1 h2]
    exact inf_le_right
  have hAnorm : f112saP2' L1 L2 S ≤
      Subgroup.normalizer ((N ⊓ f112saP2' L1 L2 S : Subgroup H) : Set H) := by
    have h := (le_inf (Subgroup.le_normalizer : f112saP2' L1 L2 S ≤
        Subgroup.normalizer (f112saP2' L1 L2 S : Set H))
      ((f112sa_P2'_le_P2 hF.toW).trans hPN)).trans (Subgroup.inf_normalizer_le_normalizer_inf
        (H := f112saP2' L1 L2 S) (K := N))
    simpa [inf_comm] using h
  have hx3' : ∃ a ∈ N ⊓ f112saP2' L1 L2 S, orderOf a = 3 :=
    ⟨(x : H), ⟨x.2, hxEA⟩, hxH3⟩
  have hq : IsL2Quot 2 (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))) :=
    f112sa_isL2Quot_oTwoPrime_P2' hF h1 h2
  have hsup := oTwoPrime_eq_sup_pCoreOf_of_isL2Quot
    (A := N ⊓ f112saP2' L1 L2 S) (E := f112saP2' L1 L2 S) hAE hAnorm hx3' hq
  rw [f112sa_oTwoPrime_P2'_eq hF h1 h2] at hsup
  have hEAK : f112saP2' L1 L2 S ≤ f112saK L1 L2 S := by
    rw [hsup]
    refine sup_le ?_ ((f112sa_QA_le_T hF).trans inf_le_right)
    have hNK : N ⊓ f112saP2' L1 L2 S ≤ f112saP2' L1 L2 S ⊓ bigB L1 L2 S :=
      le_inf inf_le_right (inf_le_left.trans hNB)
    rwa [f112sa_P2'_inf_bigB hF.toW] at hNK
  have hle := Subgroup.card_le_of_le hEAK
  rw [f112sa_card_P2' hF h1 h2, f112sa_card_K hF h1 h2] at hle
  have hpos : 0 < Nat.card ↥(S ⊓ f112saK L1 L2 S) := Nat.card_pos
  omega

private theorem f112sa_normalCore_bigB_P2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hB : S3A5VertexId L1 L2 S) :
    ((bigB L1 L2 S).subgroupOf (f112P2 L1 L2 S)).normalCore =
      (pCoreOf 2 (f112saP2' L1 L2 S)).subgroupOf (f112P2 L1 L2 S) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQAEA : pCoreOf 2 (f112saP2' L1 L2 S) ≤ f112saP2' L1 L2 S :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hEAPA : f112saP2' L1 L2 S ≤ f112P2 L1 L2 S := f112sa_P2'_le_P2 hF.toW
  have hQAPA : pCoreOf 2 (f112saP2' L1 L2 S) ≤ f112P2 L1 L2 S := hQAEA.trans hEAPA
  have hPAN : f112P2 L1 L2 S ≤
      Subgroup.normalizer (pCoreOf 2 (f112saP2' L1 L2 S) : Set H) :=
    f112sa_P2_le_normalizer_QA hF
  haveI : ((pCoreOf 2 (f112saP2' L1 L2 S)).subgroupOf (f112P2 L1 L2 S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQAPA).mpr hPAN
  have hQAB : pCoreOf 2 (f112saP2' L1 L2 S) ≤ bigB L1 L2 S :=
    (f112sa_QA_le_T hF).trans (inf_le_right.trans (f112sa_K_le_bigB L1 L2 S))
  refine le_antisymm ?_ ?_
  · set C := ((bigB L1 L2 S).subgroupOf (f112P2 L1 L2 S)).normalCore with hC
    set N := C.map (f112P2 L1 L2 S).subtype with hN
    have hCB : C ≤ (bigB L1 L2 S).subgroupOf (f112P2 L1 L2 S) := Subgroup.normalCore_le _
    have hNB : N ≤ bigB L1 L2 S := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_subgroupOf.mp (hCB hc)
    have hNPA : N ≤ f112P2 L1 L2 S := Subgroup.map_subtype_le C
    have hPN : f112P2 L1 L2 S ≤ Subgroup.normalizer (N : Set H) :=
      @CFSG.ABGLocalTools.le_normalizer_map_subtype _ _ _ C (Subgroup.normalCore_normal _)
    have hNQA : N ≤ pCoreOf 2 (f112saP2' L1 L2 S) := by
      by_cases h3 : 3 ∣ Nat.card ↥N
      · exact f112sa_le_pCoreOf_P2'_of_three_dvd hF h1 h2 hNB hNPA hPN h3
      · have hdvdB : Nat.card ↥N ∣ Nat.card ↥(bigB L1 L2 S) := Subgroup.card_dvd_of_le hNB
        rw [f112sa_card_bigB hF h1 h2] at hdvdB
        obtain ⟨a, ha⟩ := hF.1.h1.pgroup.exists_card_eq
        rw [ha] at hdvdB
        have hcop : Nat.Coprime (Nat.card ↥N) 3 :=
          ((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm
        have hdvd2 : Nat.card ↥N ∣ 2 ^ a := hcop.dvd_of_dvd_mul_left hdvdB
        have hp : IsPGroup 2 ↥N := IsPGroup.of_card_dvd_pow (p := 2) hdvd2
        have hle := map_subtype_le_pCoreOf_of_isPGroup C (Subgroup.normalCore_normal _) hp
        rwa [pCoreOf_P2_eq_QA hB] at hle
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hNQA (Subgroup.mem_map_of_mem _ hx))
  · refine (Subgroup.normal_le_normalCore (N := (pCoreOf 2 (f112saP2' L1 L2 S)).subgroupOf
      (f112P2 L1 L2 S))).mpr ?_
    intro x hx
    exact hQAB (Subgroup.mem_subgroupOf.mp hx)

private lemma exists_perm5_hom {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hB : S3A5VertexId L1 L2 S) :
    ∃ ρ : ↥(f112P2 L1 L2 S) →* Equiv.Perm (Fin 5),
      ρ.ker = (pCoreOf 2 (f112saP2' L1 L2 S)).subgroupOf (f112P2 L1 L2 S) ∧
      Nat.card ↥ρ.range = 60 * (S ⊓ f112saK L1 L2 S).relIndex S := by
  have hidx : (bigB L1 L2 S).relIndex (f112P2 L1 L2 S) = 5 := by
    rw [← f112_inf_eq_bigB hF.toW]
    simpa using f112sa_relIndex_right hF h1 le_rfl h2
  obtain ⟨ρ, -, hker, -⟩ :=
    CFSG.GroupTheory.exists_hom_perm_ker_eq_normalCore (bigB L1 L2 S) (f112P2 L1 L2 S) hidx
  have hker' : ρ.ker = (pCoreOf 2 (f112saP2' L1 L2 S)).subgroupOf (f112P2 L1 L2 S) :=
    hker.trans (f112sa_normalCore_bigB_P2 hF h1 h2 hB)
  refine ⟨ρ, hker', ?_⟩
  have hcard := Subgroup.card_ker_mul_card_range ρ
  rw [hker'] at hcard
  have hkerCard : Nat.card ↥((pCoreOf 2 (f112saP2' L1 L2 S)).subgroupOf
      (f112P2 L1 L2 S)) = Nat.card ↥(pCoreOf 2 (f112saP2' L1 L2 S)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (f112saP2' L1 L2 S)).trans
        (f112sa_P2'_le_P2 hF.toW))).toEquiv
  rw [hkerCard, f112sa_card_P2_eq hF h1 h2] at hcard
  have hSrel : Nat.card ↥S =
      (S ⊓ f112saK L1 L2 S).relIndex S * Nat.card ↥(S ⊓ f112saK L1 L2 S) := by
    have h := Subgroup.relIndex_mul_card (S ⊓ f112saK L1 L2 S) S
    rw [inf_eq_left.mpr inf_le_left] at h
    exact h.symm
  have hTcard : Nat.card ↥(S ⊓ f112saK L1 L2 S) =
      4 * Nat.card ↥(pCoreOf 2 (f112saP2' L1 L2 S)) := f112sa_card_T_eq_QA hF h1 h2
  have hQpos : 0 < Nat.card ↥(pCoreOf 2 (f112saP2' L1 L2 S)) := Nat.card_pos
  have hmain : Nat.card ↥(pCoreOf 2 (f112saP2' L1 L2 S)) * Nat.card ↥ρ.range =
      Nat.card ↥(pCoreOf 2 (f112saP2' L1 L2 S)) *
        (60 * (S ⊓ f112saK L1 L2 S).relIndex S) := by
    rw [hcard, hSrel, hTcard]
    ring
  exact Nat.eq_of_mul_eq_mul_left hQpos hmain

private theorem f112sa_relIndex_T_dvd_two {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hB : S3A5VertexId L1 L2 S) :
    (S ⊓ f112saK L1 L2 S).relIndex S ∣ 2 := by
  obtain ⟨ρ, -, hcard⟩ := exists_perm5_hom hF h1 h2 hB
  have hdvd : Nat.card ↥ρ.range ∣ 120 := by
    have h := Subgroup.card_subgroup_dvd_card ρ.range
    rw [Nat.card_perm, Nat.card_fin] at h
    have h120 : Nat.factorial 5 = 120 := by norm_num
    rwa [h120] at h
  rw [hcard] at hdvd
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd

theorem f112sa_relIndex_T_eq_two {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hB : S3A5VertexId L1 L2 S)
    (hS : ¬ S ≤ L2) : (S ⊓ L2).relIndex S = 2 := by
  rw [hB.T_eq]
  have hdvd := f112sa_relIndex_T_dvd_two hF h1 h2 hB
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exfalso
    apply hS
    have hle : S ≤ S ⊓ f112saK L1 L2 S := Subgroup.relIndex_eq_one.mp h
    rw [← hB.T_eq] at hle
    exact hle.trans inf_le_right
  · exact h

theorem f112sa_perm5 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hB : S3A5VertexId L1 L2 S)
    (hS : ¬ S ≤ L2) :
    Nonempty (oTwoQuot ↥(L2 ⊔ bigB L2 L1 S) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨ρ, hker, hcard⟩ := exists_perm5_hom hF h1 h2 hB
  have hrel : (S ⊓ f112saK L1 L2 S).relIndex S = 2 := by
    rw [← hB.T_eq]
    exact f112sa_relIndex_T_eq_two hF h1 h2 hB hS
  have hcard120 : Nat.card ↥ρ.range = Nat.card (Equiv.Perm (Fin 5)) := by
    rw [hcard, hrel, Nat.card_perm, Nat.card_fin]
    norm_num
  have htop : ρ.range = ⊤ := Subgroup.eq_top_of_card_eq (H := ρ.range) hcard120
  have hsurj : Function.Surjective ρ := by
    rw [← MonoidHom.range_eq_top]
    exact htop
  have hPA : L2 ⊔ bigB L2 L1 S = f112P2 L1 L2 S := by
    rw [f112P2, bigB_comm]
  rw [hPA]
  exact ⟨QuotientGroup.liftEquiv (CFSG.pCore 2 ↥(f112P2 L1 L2 S)) hsurj
    (by rw [hker, ← pCoreOf_P2_eq_QA hB, CFSG.openPCoreOf_subgroupOf])⟩

private theorem f112sa_relIndex_L1_sup_S {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    (L1 ⊔ S).relIndex (f112P1 L1 L2 S) = 3 := by
  have hprod := CFSG.Quasithin.EmptyFaithfulMultiple.L1547.card_sup_mul_card_inf
    (H := S) (K := L1) hF.1.h1.normalizes
  rw [sup_comm] at hprod
  rw [CFSG.Quasithin.F6.GoldPair.card_eq_six_mul_pCoreOf h1, f112sa_card_S_inf_L1 hF h1] at hprod
  have hcardSL : Nat.card ↥(L1 ⊔ S) = 3 * Nat.card ↥S := by
    have hq : 0 < 2 * Nat.card ↥(pCoreOf 2 L1) := Nat.mul_pos (by norm_num) Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    calc Nat.card ↥(L1 ⊔ S) * (2 * Nat.card ↥(pCoreOf 2 L1))
        = Nat.card ↥S * (6 * Nat.card ↥(pCoreOf 2 L1)) := hprod
      _ = (3 * Nat.card ↥S) * (2 * Nat.card ↥(pCoreOf 2 L1)) := by ring
  have hle : L1 ⊔ S ≤ f112P1 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hrel := Subgroup.relIndex_mul_card (L1 ⊔ S) (f112P1 L1 L2 S)
  rw [inf_eq_left.mpr hle, f112sa_card_P1_eq hF h1 h2, hcardSL] at hrel
  have h3 : (L1 ⊔ S).relIndex (f112P1 L1 L2 S) * (3 * Nat.card ↥S) =
      3 * (3 * Nat.card ↥S) := by
    rw [hrel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by norm_num) Nat.card_pos) h3

private theorem f112sa_bigB_inf_L1_sup_S_le {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    bigB L1 L2 S ⊓ (L1 ⊔ S) ≤ S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  rintro x ⟨hxB, hxLS⟩
  obtain ⟨l, hlL, s, hsS, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hF.1.h1.normalizes).mp hxLS
  have hlB : l ∈ bigB L1 L2 S := by
    have h : l = (l * s) * s⁻¹ := by group
    rw [h]
    exact (bigB L1 L2 S).mul_mem hxB
      ((bigB L1 L2 S).inv_mem ((le_sup_right : S ≤ bigB L1 L2 S) hsS))
  have hl : l ∈ S ⊓ L1 := by
    rw [← f112sa_borelOf_left_eq hF h1, ← F1.inf_bigB_eq_borelOf hR]
    exact ⟨hlL, hlB⟩
  exact S.mul_mem hl.1 hsS

private lemma f112sa_ker_prod_eq {L1 L2 S : Subgroup H}
    {ρ₁ ρ₂ : ↥(f112P1 L1 L2 S) →* Equiv.Perm (Fin 3)}
    (hd : ∀ x : ↥(f112P1 L1 L2 S), ρ₁ x = 1 → ρ₂ x = 1 → (x : H) ∈ pCoreOf 2 L1)
    (he : ∀ x : ↥(f112P1 L1 L2 S), (x : H) ∈ pCoreOf 2 L1 → ρ₁ x = 1 ∧ ρ₂ x = 1) :
    (ρ₁.prod ρ₂).ker = (pCoreOf 2 L1).subgroupOf (f112P1 L1 L2 S) := by
  rw [MonoidHom.ker_prod]
  refine le_antisymm ?_ ?_
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hd x (MonoidHom.mem_ker.mp hx.1)
      (MonoidHom.mem_ker.mp hx.2))
  · intro x hx
    exact ⟨MonoidHom.mem_ker.mpr (he x (Subgroup.mem_subgroupOf.mp hx)).1,
      MonoidHom.mem_ker.mpr (he x (Subgroup.mem_subgroupOf.mp hx)).2⟩

private theorem f112sa_surjective_prod {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hB : S3A5VertexId L1 L2 S)
    (hS : ¬ S ≤ L2)
    {ρ₁ ρ₂ : ↥(f112P1 L1 L2 S) →* Equiv.Perm (Fin 3)}
    (hker : (ρ₁.prod ρ₂).ker = (pCoreOf 2 L1).subgroupOf (f112P1 L1 L2 S)) :
    Function.Surjective (ρ₁.prod ρ₂) := by
  have hQ1S : pCoreOf 2 L1 ≤ S ⊓ L1 := F7.isSylowTwoOf_pCoreOf_le hF.1.h1.sylow
  have hQ1B : pCoreOf 2 L1 ≤ bigB L1 L2 S := by
    refine hQ1S.trans ?_
    rw [← f112sa_borelOf_left_eq hF h1]
    exact le_sup_left.trans le_sup_left
  have hQ1le : pCoreOf 2 L1 ≤ f112P1 L1 L2 S := hQ1B.trans le_sup_right
  have hrel : (S ⊓ L2).relIndex S = 2 := f112sa_relIndex_T_eq_two hF h1 h2 hB hS
  have hcardS : Nat.card ↥S = 2 * Nat.card ↥(S ⊓ L2) := by
    have h := Subgroup.relIndex_mul_card (S ⊓ L2) S
    rw [hrel, inf_eq_left.mpr inf_le_left] at h
    exact h.symm
  have hcardT : Nat.card ↥(S ⊓ L2) = 2 * Nat.card ↥(pCoreOf 2 L1) := by
    rw [hB.T_eq, f112sa_card_T_eq_QS hF h1 h2, ← hB.QS_eq]
  have hcardP1 : Nat.card ↥(f112P1 L1 L2 S) = 36 * Nat.card ↥(pCoreOf 2 L1) := by
    rw [f112sa_card_P1_eq hF h1 h2, hcardS, hcardT]
    ring
  have hkerCard : Nat.card ↥((ρ₁.prod ρ₂).ker) = Nat.card ↥(pCoreOf 2 L1) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ1le).toEquiv
  have hcard := Subgroup.card_ker_mul_card_range (ρ₁.prod ρ₂)
  rw [hkerCard, hcardP1] at hcard
  have hQpos : 0 < Nat.card ↥(pCoreOf 2 L1) := Nat.card_pos
  have hrange : Nat.card ↥(ρ₁.prod ρ₂).range = 36 := by
    refine Nat.eq_of_mul_eq_mul_left hQpos ?_
    rw [hcard]
    ring
  have htop : (ρ₁.prod ρ₂).range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq (H := (ρ₁.prod ρ₂).range) ?_
    rw [hrange, Nat.card_prod, Nat.card_perm, Nat.card_fin]
    norm_num
  rw [← MonoidHom.range_eq_top]
  exact htop

theorem f112sa_exists_rhoPair {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hB : S3A5VertexId L1 L2 S) :
    ∃ (ρ₁ ρ₂ : ↥(f112P1 L1 L2 S) →* Equiv.Perm (Fin 3)) (i₁ i₂ : Fin 3),
      (∀ x : ↥(f112P1 L1 L2 S), (x : H) ∈ bigB L1 L2 S → ρ₁ x i₁ = i₁) ∧
      (∀ x : ↥(f112P1 L1 L2 S), (x : H) ∈ L1 ⊔ S → ρ₂ x i₂ = i₂) ∧
      (∀ x : ↥(f112P1 L1 L2 S), (x : H) ∈ L1 → ρ₂ x = 1) ∧
      (∀ x : ↥(f112P1 L1 L2 S), ρ₁ x = 1 → ρ₂ x = 1 → (x : H) ∈ pCoreOf 2 L1) ∧
      (∀ x : ↥(f112P1 L1 L2 S), (x : H) ∈ pCoreOf 2 L1 → ρ₁ x = 1 ∧ ρ₂ x = 1) ∧
      (ρ₁.prod ρ₂).ker = (pCoreOf 2 L1).subgroupOf (f112P1 L1 L2 S) ∧
      (¬ S ≤ L2 → Function.Surjective (ρ₁.prod ρ₂)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx1 : (bigB L1 L2 S).relIndex (f112P1 L1 L2 S) = 3 := by
    rw [← f112_inf_eq_bigB hF.toW]
    exact f112sa_relIndex_left hF h1 le_rfl h2
  obtain ⟨ρ₁, i₁, hker1, hfix1⟩ :=
    CFSG.GroupTheory.exists_hom_perm_ker_eq_normalCore (bigB L1 L2 S) (f112P1 L1 L2 S) hidx1
  obtain ⟨ρ₂, i₂, hker2, hfix2⟩ :=
    CFSG.GroupTheory.exists_hom_perm_ker_eq_normalCore (L1 ⊔ S) (f112P1 L1 L2 S)
      (f112sa_relIndex_L1_sup_S hF h1 h2)
  have hP1N : f112P1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set H) :=
    sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left
      (Hyp111R.of_hyp111 rankOneListedFacts hF.1)).1
  haveI : (L1.subgroupOf (f112P1 L1 L2 S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : L1 ≤ f112P1 L1 L2 S)).mpr hP1N
  have hL1ker : L1.subgroupOf (f112P1 L1 L2 S) ≤ ρ₂.ker := by
    rw [hker2]
    exact (Subgroup.normal_le_normalCore (N := L1.subgroupOf (f112P1 L1 L2 S))).mpr
      (Subgroup.subgroupOf_mono (f112P1 L1 L2 S) le_sup_left)
  have hc : ∀ x : ↥(f112P1 L1 L2 S), (x : H) ∈ L1 → ρ₂ x = 1 := by
    intro x hx
    exact MonoidHom.mem_ker.mp (hL1ker (Subgroup.mem_subgroupOf.mpr hx))
  have hd : ∀ x : ↥(f112P1 L1 L2 S), ρ₁ x = 1 → ρ₂ x = 1 → (x : H) ∈ pCoreOf 2 L1 := by
    intro x hx1 hx2
    have hxM : x ∈ ρ₁.ker ⊓ ρ₂.ker :=
      ⟨MonoidHom.mem_ker.mpr hx1, MonoidHom.mem_ker.mpr hx2⟩
    have hxN : (x : H) ∈ (ρ₁.ker ⊓ ρ₂.ker).map (f112P1 L1 L2 S).subtype :=
      Subgroup.mem_map_of_mem _ hxM
    have hNB : (ρ₁.ker ⊓ ρ₂.ker).map (f112P1 L1 L2 S).subtype ≤ bigB L1 L2 S := by
      intro y hy
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
      rw [hker1] at hm
      exact Subgroup.mem_subgroupOf.mp (Subgroup.normalCore_le _ hm.1)
    have hNLS : (ρ₁.ker ⊓ ρ₂.ker).map (f112P1 L1 L2 S).subtype ≤ L1 ⊔ S := by
      intro y hy
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
      rw [hker2] at hm
      exact Subgroup.mem_subgroupOf.mp (Subgroup.normalCore_le _ hm.2)
    have hNS : (ρ₁.ker ⊓ ρ₂.ker).map (f112P1 L1 L2 S).subtype ≤ S :=
      (le_inf hNB hNLS).trans (f112sa_bigB_inf_L1_sup_S_le hF h1)
    have hpN : IsPGroup 2 ↥((ρ₁.ker ⊓ ρ₂.ker).map (f112P1 L1 L2 S).subtype) :=
      hF.1.h1.pgroup.to_le hNS
    have hle := map_subtype_le_pCoreOf_of_isPGroup (ρ₁.ker ⊓ ρ₂.ker)
      (Subgroup.normal_inf_normal ρ₁.ker ρ₂.ker) hpN
    rw [pCoreOf_P1_eq_QS hB] at hle
    exact hle hxN
  have hQ1S : pCoreOf 2 L1 ≤ S ⊓ L1 := F7.isSylowTwoOf_pCoreOf_le hF.1.h1.sylow
  have hQ1B : pCoreOf 2 L1 ≤ bigB L1 L2 S := by
    refine hQ1S.trans ?_
    rw [← f112sa_borelOf_left_eq hF h1]
    exact le_sup_left.trans le_sup_left
  have hQ1le : pCoreOf 2 L1 ≤ f112P1 L1 L2 S := hQ1B.trans le_sup_right
  have hP1NQ : f112P1 L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set H) :=
    hP1N.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L1)
  haveI : ((pCoreOf 2 L1).subgroupOf (f112P1 L1 L2 S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ1le).mpr hP1NQ
  have he1 : (pCoreOf 2 L1).subgroupOf (f112P1 L1 L2 S) ≤ ρ₁.ker := by
    rw [hker1]
    exact (Subgroup.normal_le_normalCore (N := (pCoreOf 2 L1).subgroupOf
      (f112P1 L1 L2 S))).mpr
      (Subgroup.subgroupOf_mono (f112P1 L1 L2 S) hQ1B)
  have hQ1LS : pCoreOf 2 L1 ≤ L1 ⊔ S :=
    (hQ1S.trans inf_le_right).trans le_sup_left
  have he2 : (pCoreOf 2 L1).subgroupOf (f112P1 L1 L2 S) ≤ ρ₂.ker := by
    rw [hker2]
    exact (Subgroup.normal_le_normalCore (N := (pCoreOf 2 L1).subgroupOf
      (f112P1 L1 L2 S))).mpr
      (Subgroup.subgroupOf_mono (f112P1 L1 L2 S) hQ1LS)
  have he : ∀ x : ↥(f112P1 L1 L2 S), (x : H) ∈ pCoreOf 2 L1 → ρ₁ x = 1 ∧ ρ₂ x = 1 := by
    intro x hx
    exact ⟨MonoidHom.mem_ker.mp (he1 (Subgroup.mem_subgroupOf.mpr hx)),
      MonoidHom.mem_ker.mp (he2 (Subgroup.mem_subgroupOf.mpr hx))⟩
  have hker := f112sa_ker_prod_eq hd he
  exact ⟨ρ₁, ρ₂, i₁, i₂, hfix1, hfix2, hc, hd, he, hker,
    fun hS => f112sa_surjective_prod hF h1 h2 hB hS hker⟩

theorem f112sa_s3s3 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hB : S3A5VertexId L1 L2 S)
    (hS : ¬ S ≤ L2) :
    Nonempty (oTwoQuot ↥(L1 ⊔ bigB L1 L2 S) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨ρ₁, ρ₂, i₁, i₂, -, -, -, -, -, hker, hf⟩ := f112sa_exists_rhoPair hF h1 h2 hB
  exact ⟨QuotientGroup.liftEquiv (CFSG.pCore 2 ↥(f112P1 L1 L2 S)) (hf hS)
    (by rw [hker, ← pCoreOf_P1_eq_QS hB, CFSG.openPCoreOf_subgroupOf])⟩

end CFSG.Quasithin.F112R.St84
