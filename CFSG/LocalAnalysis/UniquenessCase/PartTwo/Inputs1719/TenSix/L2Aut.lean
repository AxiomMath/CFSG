module

public import CFSG.GH74.GLS.IVK.L2.KI2Aux
public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL2OddGroup
public import CFSG.Quasithin.Vol2.Ch4Sec4F4411D
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix

open CFSG.GH74.GLS.IVK CFSG.Open Subgroup
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

private theorem exists_ne_one_mem_inf_innAut [Finite K] (hF : L2Field F) (e : K ≃* L2 F)
    {A : Subgroup (MulAut K)} (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8) :
    ∃ b ∈ A ⊓ innAut K, b ≠ 1 := by
  classical
  set V : Subgroup (MulAut K) := A ⊓ innDiagSub e with hV
  have hVcard : Nat.card ↥V = 4 :=
    CFSG.GH74.GLS.IVK.card_inf_innDiag_eq_four e hF A hA.isElementaryAbelian h8
  have hidx : (innAut K).relIndex (innDiagSub e) = 2 :=
    CFSG.GH74.GLS.IVK.innAut_relIndex_two e hF
  have hVle : V ≤ innDiagSub e := inf_le_right
  have hrel : (V ⊓ innAut K).relIndex V ≤ 2 := by
    have h1 := Subgroup.relIndex_inf_le (H := innAut K) (K := V) (L := V)
    have h2 : (innAut K).relIndex V ≤ 2 := by
      have h := Subgroup.relIndex_le_of_le_right hVle (by rw [hidx]; norm_num)
      rwa [hidx] at h
    have h3 : V.relIndex V = 1 := Subgroup.relIndex_self V
    calc (V ⊓ innAut K).relIndex V ≤ (innAut K).relIndex V * V.relIndex V := by
          simpa [inf_comm] using h1
      _ ≤ 2 * 1 := Nat.mul_le_mul h2 h3.le
      _ = 2 := by norm_num
  have hne : V ⊓ innAut K ≠ ⊥ := by
    intro hbot
    have h4 : (V ⊓ innAut K).relIndex V = 4 := by
      rw [hbot, Subgroup.relIndex_bot_left, hVcard]
    omega
  have hVe : V ⊓ innAut K = A ⊓ innAut K := by
    rw [hV, inf_assoc, inf_eq_right.mpr (CFSG.GH74.GLS.IVK.innAut_le_innDiagSub e)]
  rw [hVe] at hne
  by_contra hcon
  push Not at hcon
  exact hne (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx))

theorem card_le_eight_of_isElemAbelian
    (hF : L2Field F) (e : K ≃* L2 F)
    {A : Subgroup (MulAut K)} (hA : IsElemAbelian 2 A) : Nat.card A ≤ 8 := by
  let Ψ : MulAut K ≃* CFSG.GorensteinWalter.PGammaL2 F :=
    CFSG.ComponentClassification.AutL2Facts.autEquiv (e.trans (L2.equivPSL F))
  rw [← Subgroup.card_map_of_injective (f := Ψ.toMonoidHom) Ψ.injective]
  apply CFSG.ComponentClassification.AutL2Facts.pGammaL2_card_le_eight_of_sq
    (isOddPrimePower_of_L2Field hF)
  rintro _ ⟨x, hx, rfl⟩
  change Ψ x * Ψ x = 1
  rw [← map_mul, ← pow_two, hA.2 x hx, map_one]

private theorem eq_bot_pCoreOf_inf_of_pgl2 [Finite K] {H N : Subgroup (MulAut K)}
    {F₀ : Type} [Field F₀] [Finite F₀] (eN : ↥N ≃* CFSG.GorensteinWalter.PGL2 F₀)
    (hodd : Odd (Nat.card F₀)) (h3 : 3 < Nat.card F₀) (hNH : N ≤ H) :
    pCoreOf 2 H ⊓ N = ⊥ := by
  set P : Subgroup (MulAut K) := pCoreOf 2 H ⊓ N with hPdef
  have hPN : P ≤ N := inf_le_right
  have hPsm : (P.subgroupOf N).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hPN).2 ?_
    intro p n hp hn
    refine ⟨?_, ?_⟩
    · exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf (hNH hn) hp.1
    · exact N.mul_mem (N.mul_mem hn hp.2) (N.inv_mem hn)
  have hPp : IsPGroup 2 ↥(P.subgroupOf N) :=
    ((CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 H).to_le inf_le_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe hPN).symm
  have hbot : P.subgroupOf N = ⊥ := by
    have := hPsm
    exact CFSG.Quasithin.H13.Ch4.E443.F4411.eq_bot_of_mulEquiv_pgl2
      (CFSG.GH74.GLS.IVK.isOddPrimePower_of_odd_card hodd) h3 eN hPp
  exact (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hPN

private theorem le_centralizer_of_le_pCoreOf {A : Subgroup (MulAut K)} {a : MulAut K}
    (hA : IsElemAbelian 2 A) (haA : a ∈ A) {H : Subgroup (MulAut K)}
    (hAO : A ≤ pCoreOf 2 H)
    (hNH : innAut K ⊓ centralizer ({a} : Set (MulAut K)) ≤ H)
    (hPbot : pCoreOf 2 H ⊓ (innAut K ⊓ centralizer ({a} : Set (MulAut K))) = ⊥) :
    A ≤ centralizer
      (↑(innAut K ⊓ centralizer ({a} : Set (MulAut K))) : Set (MulAut K)) := by
  have hAC : A ≤ centralizer ({a} : Set (MulAut K)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hA.comm hx haA
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hxO : x ∈ pCoreOf 2 H := hAO hx
  have hnH : n ∈ H := hNH hn
  have hmemP : n * x * n⁻¹ * x⁻¹ ∈
      pCoreOf 2 H ⊓ (innAut K ⊓ centralizer ({a} : Set (MulAut K))) := by
    refine ⟨?_, ?_, ?_⟩
    · exact (pCoreOf 2 H).mul_mem
        (CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hnH hxO)
        ((pCoreOf 2 H).inv_mem hxO)
    · have h1 : x * n⁻¹ * x⁻¹ ∈ innAut K :=
        Subgroup.Normal.conj_mem (innAut_normal (K := K)) n⁻¹ ((innAut K).inv_mem hn.1) x
      have h2 : n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) := by group
      rw [h2]
      exact (innAut K).mul_mem hn.1 h1
    · exact (centralizer ({a} : Set (MulAut K))).mul_mem
        ((centralizer ({a} : Set (MulAut K))).mul_mem
          ((centralizer ({a} : Set (MulAut K))).mul_mem hn.2 (hAC hx))
          ((centralizer ({a} : Set (MulAut K))).inv_mem hn.2))
        ((centralizer ({a} : Set (MulAut K))).inv_mem (hAC hx))
  have hmem_bot : n * x * n⁻¹ * x⁻¹ = 1 := by
    have hPN : n * x * n⁻¹ * x⁻¹ ∈ innAut K ⊓ centralizer ({a} : Set (MulAut K)) :=
      hmemP.2
    have h1 : (⟨n * x * n⁻¹ * x⁻¹, hPN⟩ : ↥(innAut K ⊓
        centralizer ({a} : Set (MulAut K)))) ∈ (pCoreOf 2 H ⊓ (innAut K ⊓
          centralizer ({a} : Set (MulAut K)))).subgroupOf (innAut K ⊓
            centralizer ({a} : Set (MulAut K))) := hmemP
    rw [hPbot, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have hcomm : n * x = x * n := by
    have h1 : ⁅n, x⁆ = 1 := by
      rw [commutatorElement_def]
      exact hmem_bot
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  exact hcomm

theorem exists_not_le_pCoreOf_of_card_eight (hF : L2Field F) (h9 : 9 < Nat.card F)
    (e : K ≃* L2 F) {A : Subgroup (MulAut K)} (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8) :
    ∃ a ∈ A, a ≠ 1 ∧ ∀ H : Subgroup (MulAut K), A ≤ H →
      H ≤ centralizer ({a} : Set (MulAut K)) →
      innAut K ⊓ centralizer ({a} : Set (MulAut K)) ≤ H → ¬ A ≤ pCoreOf 2 H := by
  classical
  have : Finite K := Finite.of_injective (e : K → L2 F) e.injective
  obtain ⟨a, haA, haD, ha2⟩ :=
    CFSG.GH74.GLS.IVK.exists_involution_outside e hF A hA.isElementaryAbelian h8
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha2
    omega
  refine ⟨a, haA, ha1, ?_⟩
  intro H hAH hHC hNH hAO
  obtain ⟨F₀, hF₀field, hF₀fin, hF₀sq, ⟨ψ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec20.L2OddGroup.isPGL2_fixedSubgroup_of_not_mem_innDiagSub e ha2 haD
  have hF₀odd : Odd (Nat.card F₀) := by
    have h1 : Odd (Nat.card F₀ ^ 2) := by rw [hF₀sq]; exact hF.1
    rw [pow_two] at h1
    exact (Nat.odd_mul.mp h1).1
  have hF₀3 : 3 < Nat.card F₀ := by
    by_contra hle
    push Not at hle
    have h2 : Nat.card F₀ ^ 2 ≤ 9 := by nlinarith
    rw [hF₀sq] at h2
    omega
  have hNmap : (CFSG.GH74.GLS.fixedSubgroup K a).map (MulAut.conj : K →* MulAut K) =
      innAut K ⊓ centralizer ({a} : Set (MulAut K)) :=
    CFSG.GH74.GLS.IVK.map_conj_fixedSubgroup_eq
      (CFSG.GH74.GLS.IVK.conj_injective_of_L2 e) a
  let eN := ((Subgroup.equivMapOfInjective (CFSG.GH74.GLS.fixedSubgroup K a)
        (MulAut.conj : K →* MulAut K) (CFSG.GH74.GLS.IVK.conj_injective_of_L2 e)).trans
      (MulEquiv.subgroupCongr hNmap)).symm.trans ψ
  have hPbot : pCoreOf 2 H ⊓ (innAut K ⊓ centralizer ({a} : Set (MulAut K))) = ⊥ :=
    eq_bot_pCoreOf_inf_of_pgl2 eN hF₀odd hF₀3 hNH
  have hcentral := le_centralizer_of_le_pCoreOf hA haA hAO hNH hPbot
  obtain ⟨b, hb, hb1⟩ := exists_ne_one_mem_inf_innAut hF e hA h8
  have hbC : b ∈ centralizer ({a} : Set (MulAut K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hA.comm hb.1 haA
  have hbN : b ∈ innAut K ⊓ centralizer ({a} : Set (MulAut K)) := ⟨hb.2, hbC⟩
  have hbcenter : (⟨b, hbN⟩ : ↥(innAut K ⊓ centralizer ({a} : Set (MulAut K)))) ∈
      Subgroup.center ↥(innAut K ⊓ centralizer ({a} : Set (MulAut K))) := by
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (hcentral hb.1 (m : MulAut K) m.2)
  have hcenter_bot : Subgroup.center ↥(innAut K ⊓
      centralizer ({a} : Set (MulAut K))) = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv eN
      (CFSG.GorensteinWalter.pgl2_center_eq_bot F₀)
  rw [hcenter_bot, Subgroup.mem_bot] at hbcenter
  exact hb1 (congrArg Subtype.val hbcenter)

theorem card_le_eight_of_isElemAbelian_eight (hF : Nat.card F = 8) (e : K ≃* L2 F)
    {A : Subgroup (MulAut K)} (hA : IsElemAbelian 2 A) : Nat.card A ≤ 8 := by
  have : Finite K := Finite.of_injective (e : K → L2 F) e.injective
  have hAdm : StatedLieAdmissible .PSL 2 2 3 := by
    rw [StatedLieAdmissible]; norm_num
  have hLM : CFSG.Blueprint.LieModel K .PSL 2 2 3 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
      ⟨hAdm, F, inferInstance, inferInstance, hF, ⟨e⟩⟩⟩
  have hcard : Nat.card (MulAut K) = 1512 :=
    CFSG.LocalAnalysis.GLTheoremA.small_card_psl28 hLM
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hA.isPGroup
  have hdvd : 2 ^ k ∣ 1512 := by
    rw [← hk, ← hcard]
    exact Subgroup.card_subgroup_dvd_card A
  have h189 : (1512 : ℕ) = 189 * 2 ^ 3 := by norm_num
  rw [h189] at hdvd
  have hcop : Nat.Coprime (2 ^ k) 189 := Nat.Coprime.pow_left _ (by norm_num)
  have h23 : 2 ^ k ∣ 2 ^ 3 := Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd
  have hk3 : k ≤ 3 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (Nat.le_of_dvd (by norm_num) h23)
  calc Nat.card A = 2 ^ k := hk
    _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 8 := by norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix
