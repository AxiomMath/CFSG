module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers
public import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2
public import CFSG.RankThree.CentralExtension.ScalarNormalizerKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover
open CFSG.Quasithin.F112R CFSG.Quasithin.A312J2
open CFSG.Sporadic.Schreier (centralizerIn)

section Model


theorem nonempty_centralizerIn_P_equiv :
    Nonempty (↥(centralizerIn P permTwoA) ≃* ↥(j2CtxA.Y 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCP : centralizerIn P permTwoA ≤ P := inf_le_left
  have hZ : Nat.card ((centralizerIn P permTwoA).subgroupOf P) = 1920 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv]
    exact Kernel.centralizerIn_P_permTwoA.2.1
  have hidx : ((centralizerIn P permTwoA).subgroupOf P).index = 315 := by
    have h := ((centralizerIn P permTwoA).subgroupOf P).card_mul_index
    rw [hZ, card_P] at h
    omega
  obtain ⟨T, hT⟩ := CFSG.RankThree.CentralExtension.exists_sylow_le_of_index_coprime (p := 2)
    ((centralizerIn P permTwoA).subgroupOf P) (by rw [hidx]; norm_num)
  have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf (T : Subgroup ↥P) ⊤ :=
    CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.2 ⟨T.isPGroup', T.not_dvd_index⟩
  obtain ⟨e⟩ := @nonempty_equiv_of_overgroup ↥P ↥CFSG.Sporadic.J2.J inferInstance inferInstance
    inferInstance inferInstance jEquivP.symm _ hT₀ j2CtxA.S j2A_sylow _ hT (j2CtxA.Y 3)
    (fun W hW hc => eq_j2Y3_of_card hW (hc.trans hZ))
  exact ⟨(Subgroup.subgroupOfEquivOfLe hCP).symm.trans e⟩

theorem nonempty_centralizerIn_R_equiv :
    Nonempty (↥(centralizerIn R permTwoA) ≃* ↥(AJ2L.rCtx.Y 2)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCR : centralizerIn R permTwoA ≤ R := inf_le_left
  have hZ : Nat.card ((centralizerIn R permTwoA).subgroupOf R) = 3840 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCR).toEquiv]
    exact Kernel.centralizerIn_R_permTwoA.2.1
  have hidx : ((centralizerIn R permTwoA).subgroupOf R).index = 315 := by
    have h := ((centralizerIn R permTwoA).subgroupOf R).card_mul_index
    rw [hZ, card_R] at h
    omega
  obtain ⟨T, hT⟩ := CFSG.RankThree.CentralExtension.exists_sylow_le_of_index_coprime (p := 2)
    ((centralizerIn R permTwoA).subgroupOf R) (by rw [hidx]; norm_num)
  have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf (T : Subgroup ↥R) ⊤ :=
    CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.2 ⟨T.isPGroup', T.not_dvd_index⟩
  obtain ⟨e⟩ := nonempty_equiv_of_overgroup (MulEquiv.refl ↥R) hT₀ AJ2L.rCtx_sylow hT
    (M := AJ2L.rCtx.Y 2) fun W hW hc => by
      have hc' : Nat.card W = 3840 := hc.trans hZ
      rcases AJ2L.overgroup hW with h | ⟨j, hj, hWj, hcj⟩
      · rw [h, Subgroup.card_top, card_R] at hc'
        norm_num at hc'
      · rw [hc'] at hcj
        have hj2 : j = 2 := by
          interval_cases j <;> simp_all
        subst hj2
        exact hWj
  exact ⟨(Subgroup.subgroupOfEquivOfLe hCR).symm.trans e⟩

theorem oTwoQuot_centralizerIn_P :
    Nonempty (CFSG.Quasithin.oTwoQuot ↥(centralizerIn P permTwoA) ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := nonempty_centralizerIn_P_equiv
  obtain ⟨e2⟩ := quot_Y3_alt5
  have e1 : CFSG.Quasithin.oTwoQuot ↥(centralizerIn P permTwoA) ≃*
      CFSG.Quasithin.oTwoQuot ↥(j2CtxA.Y 3) := oTwoQuotCongr e
  exact ⟨e1.trans e2⟩

theorem oTwoQuot_centralizerIn_R :
    Nonempty (CFSG.Quasithin.oTwoQuot ↥(centralizerIn R permTwoA) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨e⟩ := nonempty_centralizerIn_R_equiv
  obtain ⟨e2⟩ := perm5_Y2
  exact ⟨(oTwoQuotCongr e).trans e2⟩

theorem centralizerIn_R_le_normalizer :
    centralizerIn R permTwoA ≤
      Subgroup.normalizer (centralizerIn P permTwoA : Set (Equiv.Perm (Fin 315))) := by
  intro r hr
  have hrP := R_le_normalizer hr.1
  have hrc : Commute r permTwoA := Subgroup.mem_centralizer_singleton_iff.1 hr.2
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxP, hxz⟩
    have hxc : Commute x permTwoA := Subgroup.mem_centralizer_singleton_iff.1 hxz
    exact ⟨(Subgroup.mem_normalizer_iff.1 hrP x).1 hxP,
      Subgroup.mem_centralizer_singleton_iff.2 ((hrc.mul_left hxc).mul_left hrc.inv_left)⟩
  · rintro ⟨hxP, hxz⟩
    have hyc : Commute (r * x * r⁻¹) permTwoA := Subgroup.mem_centralizer_singleton_iff.1 hxz
    have h := (hrc.inv_left.mul_left hyc).mul_left hrc
    rw [show r⁻¹ * (r * x * r⁻¹) * r = x by group] at h
    exact ⟨(Subgroup.mem_normalizer_iff.1 hrP x).2 hxP, Subgroup.mem_centralizer_singleton_iff.2 h⟩

theorem pCoreOf_centralizerIn_permTwoA :
    CFSG.Open.pCoreOf 2 (centralizerIn P permTwoA) =
        CFSG.Open.pCoreOf 2 (centralizerIn R permTwoA) ∧
      CFSG.Quasithin.IsQ8D8 ↥(CFSG.Open.pCoreOf 2 (centralizerIn R permTwoA)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eP⟩ := nonempty_centralizerIn_P_equiv
  obtain ⟨eR⟩ := nonempty_centralizerIn_R_equiv
  have hPR : centralizerIn P permTwoA ≤ centralizerIn R permTwoA :=
    inf_le_inf_right _ P_le_R
  have hle : CFSG.Open.pCoreOf 2 (centralizerIn P permTwoA) ≤
      CFSG.Open.pCoreOf 2 (centralizerIn R permTwoA) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hPR)
      (centralizerIn_R_le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  refine ⟨Subgroup.eq_of_le_of_card_ge hle ?_, isQ8D8_pCoreOf_of_mulEquiv eR isQ8D8_pCoreOf_Y2⟩
  rw [card_pCoreOf_of_mulEquiv eP 2, J2L.card_pCoreOf_Y3, card_pCoreOf_of_mulEquiv eR 2,
    AJ2L.card_pCoreOf_Y2]

end Model

theorem eq_bot_of_le_isQ8D8_of_fpf {G : Type*} [Group G] {Q P' : Subgroup G}
    (hQ : CFSG.Quasithin.IsQ8D8 ↥Q) (hPQ : P' ≤ Q) {x : G}
    (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hxP : ∀ p ∈ P', x * p * x⁻¹ ∈ P')
    (hfpf : ∀ p ∈ P', x * p = p * x → p = 1) : P' = ⊥ := by
  classical
  have hfin : Finite ↥Q := Nat.finite_of_card_ne_zero (by rw [hQ.1]; norm_num)
  obtain ⟨z, hzc, hz1, hzz, hcen, hsq⟩ := CFSG.Quasithin.H13.isQ8D8_central_facts hQ
  obtain ⟨xs, hx2, -, hxx, -⟩ := hQ.exists_fiveLines hzc hz1
  have hzcomm : ∀ g : ↥Q, z * g = g * z := fun g => (Subgroup.mem_center_iff.1 hzc g).symm
  let φ : ↥Q →* ↥Q :=
    { toFun := fun q => ⟨x * q * x⁻¹, hxQ q q.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hφ : ∀ q : ↥Q, ((φ q : ↥Q) : G) = x * q * x⁻¹ := fun _ => rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h := congrArg Subtype.val hab
    rw [hφ, hφ, mul_left_inj, mul_right_inj] at h
    exact Subtype.ext h
  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.1 hφinj
  have hφz : φ z = z := by
    have hc : φ z ∈ Subgroup.center ↥Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := hφsurj g
      rw [← map_mul, ← map_mul, hzcomm g']
    rcases hcen _ hc with h | h
    · exact absurd (hφinj (h.trans (map_one φ).symm)) hz1
    · exact h
  have hxz : x * (z : G) = (z : G) * x := by
    have h : x * (z : G) * x⁻¹ = z := by rw [← hφ, hφz]
    calc x * (z : G) = x * (z : G) * x⁻¹ * x := by group
      _ = (z : G) * x := by rw [h]
  have hzP : (z : G) ∉ P' := fun h => hz1 (Subtype.ext (hfpf _ h hxz))
  have hsq1 : ∀ p ∈ P', p * p = 1 := by
    intro p hp
    rcases hsq ⟨p, hPQ hp⟩ with h | h
    · exact congrArg Subtype.val h
    · exfalso
      apply hzP
      have h' : p * p = (z : G) := congrArg Subtype.val h
      rw [← h']
      exact P'.mul_mem hp hp
  have hzsq : ∀ g : ↥Q, z * g * (z * g) = g * g := by
    intro g
    calc
      z * g * (z * g) = z * z * (g * g) := by
        rw [mul_assoc z g, ← mul_assoc g z, ← hzcomm g]
        group
      _ = g * g := by rw [hzz, one_mul]
  have key : ∀ p ∈ P', ∀ q ∈ P', p ≠ 1 → q ≠ 1 → p = q := by
    intro p hp q hq hp1 hq1
    by_contra hpq
    have hp'1 : (⟨p, hPQ hp⟩ : ↥Q) ≠ 1 := fun h => hp1 (congrArg Subtype.val h)
    have hq'1 : (⟨q, hPQ hq⟩ : ↥Q) ≠ 1 := fun h => hq1 (congrArg Subtype.val h)
    have hp'z : (⟨p, hPQ hp⟩ : ↥Q) ≠ z := fun h => hzP (by rw [← h]; exact hp)
    have hq'z : (⟨q, hPQ hq⟩ : ↥Q) ≠ z := fun h => hzP (by rw [← h]; exact hq)
    have hpq2 : (⟨p, hPQ hp⟩ : ↥Q) * ⟨q, hPQ hq⟩ * (⟨p, hPQ hp⟩ * ⟨q, hPQ hq⟩) = 1 :=
      Subtype.ext (hsq1 (p * q) (P'.mul_mem hp hq))
    obtain ⟨i, hi⟩ := hQ.eq_line_of_involution hzc hz1 hx2 hxx
      (Subtype.ext (hsq1 p hp)) hp'1 hp'z
    obtain ⟨j, hj⟩ := hQ.eq_line_of_involution hzc hz1 hx2 hxx
      (Subtype.ext (hsq1 q hq)) hq'1 hq'z
    have hne : (⟨p, hPQ hp⟩ : ↥Q) ≠ ⟨q, hPQ hq⟩ := fun h => hpq (congrArg Subtype.val h)
    by_cases hij : i = j
    · subst hij
      have hzpq : (⟨p, hPQ hp⟩ : ↥Q) * ⟨q, hPQ hq⟩ = z := by
        rcases hi with h1 | h1 <;> rcases hj with h2 | h2
        · exact absurd (h1.trans h2.symm) hne
        · rw [h1, h2, ← mul_assoc, ← hzcomm, mul_assoc, hx2, mul_one]
        · rw [h1, h2, mul_assoc, hx2, mul_one]
        · exact absurd (h1.trans h2.symm) hne
      apply hzP
      have h' : p * q = (z : G) := congrArg Subtype.val hzpq
      rw [← h']
      exact P'.mul_mem hp hq
    · have hl : (xs i * xs j) * (xs i * xs j) = z := by rw [← pow_two]; exact hxx i j hij
      have hsame : (⟨p, hPQ hp⟩ : ↥Q) * ⟨q, hPQ hq⟩ * (⟨p, hPQ hp⟩ * ⟨q, hPQ hq⟩) =
          (xs i * xs j) * (xs i * xs j) := by
        rcases hi with h1 | h1 <;> rcases hj with h2 | h2 <;> rw [h1, h2]
        · rw [show xs i * (z * xs j) = z * (xs i * xs j) by
            rw [← mul_assoc, ← hzcomm, mul_assoc], hzsq]
        · rw [show z * xs i * xs j = z * (xs i * xs j) by rw [mul_assoc], hzsq]
        · rw [show z * xs i * (z * xs j) = xs i * xs j by
            rw [mul_assoc, ← mul_assoc (xs i), ← hzcomm, ← mul_assoc, ← mul_assoc, hzz, one_mul]]
      exact hz1 (hl.symm.trans (hsame.symm.trans hpq2))
  rw [eq_bot_iff]
  intro p hp
  rw [Subgroup.mem_bot]
  by_contra hp1
  have hxp1 : x * p * x⁻¹ ≠ 1 := fun h => hp1 (by
    calc p = x⁻¹ * (x * p * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group)
  have he := key _ (hxP p hp) p hp hxp1 hp1
  exact hp1 (hfpf p hp (by
    calc x * p = x * p * x⁻¹ * x := by group
      _ = p * x := by rw [he]))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact
