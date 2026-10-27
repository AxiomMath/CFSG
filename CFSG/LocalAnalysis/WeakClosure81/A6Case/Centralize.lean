module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenCommI
import CFSG.LocalAnalysis.WeakClosure81.SevenSevenCMin
import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction
import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.Plane9
import CFSG.RankThree.PartTwo.Sec17.Item174StarL2

public section

namespace CFSG.LocalAnalysis.WeakClosure81.A6Case

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement
open CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

private theorem commute_commutator_of_conj_eq_inv {d y f : G} (hd2 : d * d = 1)
    (hinv : d * y * d⁻¹ = y⁻¹) (hfy : Commute f y) : Commute ⁅f, d⁆ y := by
  have hdy : d⁻¹ * y * d = y⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hd2]
    have hdy' : d * y = y⁻¹ * d := by
      have h := congrArg (fun z => z * d) hinv
      simpa [mul_assoc] using h
    calc d * y * d = (y⁻¹ * d) * d := by rw [hdy']
      _ = y⁻¹ := by rw [mul_assoc, hd2, mul_one]
  have hdyinv : d * y⁻¹ * d⁻¹ = y := by
    have h := congrArg (fun z => z⁻¹) hinv
    simpa [mul_assoc] using h
  have hfinv : f⁻¹ * y⁻¹ * f = y⁻¹ := by
    calc f⁻¹ * y⁻¹ * f = y⁻¹ * f⁻¹ * f := by rw [(hfy.inv_inv).eq]
      _ = y⁻¹ * (f⁻¹ * f) := by group
      _ = y⁻¹ := by rw [inv_mul_cancel, mul_one]
  have h1 : ⁅f, d⁆ * y * ⁅f, d⁆⁻¹ = y := by
    calc (f * d * f⁻¹ * d⁻¹) * y * (f * d * f⁻¹ * d⁻¹)⁻¹
        = f * d * f⁻¹ * (d⁻¹ * y * d) * f * d⁻¹ * f⁻¹ := by group
      _ = f * d * f⁻¹ * y⁻¹ * f * d⁻¹ * f⁻¹ := by rw [hdy]
      _ = f * d * (f⁻¹ * y⁻¹ * f) * d⁻¹ * f⁻¹ := by group
      _ = f * d * y⁻¹ * d⁻¹ * f⁻¹ := by rw [hfinv]
      _ = f * (d * y⁻¹ * d⁻¹) * f⁻¹ := by group
      _ = f * y * f⁻¹ := by rw [hdyinv]
      _ = y := by rw [hfy.eq]; group
  show ⁅f, d⁆ * y = y * ⁅f, d⁆
  calc ⁅f, d⁆ * y = ⁅f, d⁆ * y * ⁅f, d⁆⁻¹ * ⁅f, d⁆ := by group
    _ = y * ⁅f, d⁆ := congrArg (fun z => z * ⁅f, d⁆) h1

private theorem eq_one_of_commutator_of_isTI {U : Subgroup G} (h : Hyp711 V H E)
    (hU : U ∈ omegaSet V H E) {d y : G} (hdU : d ∈ U) (hy : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hinv : d * y * d⁻¹ = y⁻¹) {f : G} (hfdU : ⁅f, d⁆ ∈ U)
    (hcomm : Commute ⁅f, d⁆ y) : ⁅f, d⁆ = 1 := by
  by_contra hne
  have hUab : IsElemAbelian 2 U := isElemAbelian_of_mem_omegaSet h.elemAbelian hU
  have hU2 : IsPGroup 2 U := isPGroup_two_of_isElemAbelian hUab
  obtain ⟨g, hUg, -, -⟩ := mem_omegaSet.mp hU
  have hTI : U ⊓ CFSG.Quasithin.conjSubgroup U y⁻¹ = ⊥ ∨
      U = CFSG.Quasithin.conjSubgroup U y⁻¹ := by
    rw [hUg]
    have h := inf_conjSubgroup_eq_bot_or_eq h.ti g (g * y⁻¹)
    rwa [← CFSG.Quasithin.conjSubgroup_conjSubgroup] at h
  have hcy : y * ⁅f, d⁆ * y⁻¹ = ⁅f, d⁆ := by
    calc y * ⁅f, d⁆ * y⁻¹ = (⁅f, d⁆ * y) * y⁻¹ := by rw [hcomm.eq]
      _ = ⁅f, d⁆ := by group
  have hmem_conj : ⁅f, d⁆ ∈ CFSG.Quasithin.conjSubgroup U y⁻¹ := by
    rw [show CFSG.Quasithin.conjSubgroup U y⁻¹ =
      U.map (MulAut.conj y).toMonoidHom by rw [CFSG.Quasithin.conjSubgroup, inv_inv]]
    exact Subgroup.mem_map.mpr ⟨⁅f, d⁆, hfdU, by
      show (MulAut.conj y) ⁅f, d⁆ = ⁅f, d⁆
      rw [MulAut.conj_apply, hcy]⟩
  have hmemInf : ⁅f, d⁆ ∈ U ⊓ CFSG.Quasithin.conjSubgroup U y⁻¹ :=
    Subgroup.mem_inf.mpr ⟨hfdU, hmem_conj⟩
  rcases hTI with hbot | heq
  · have hb : ⁅f, d⁆ ∈ (⊥ : Subgroup G) := by rwa [hbot] at hmemInf
    exact hne (Subgroup.mem_bot.mp hb)
  · have hyN : y ∈ Subgroup.normalizer (U : Set G) := by
      refine (Subgroup.mem_normalizer_iff_map_conj_eq (H := U) (g := y)).mpr ?_
      have h : CFSG.Quasithin.conjSubgroup U y⁻¹ = U.map (MulAut.conj y).toMonoidHom := by
        rw [CFSG.Quasithin.conjSubgroup, inv_inv]
      exact h ▸ heq.symm
    exact CFSG.RankThree.PartTwo.Sec17.Proof174Host.not_inv_of_mem hU2
      (orderOf_eq_prime hy hy1) hyN hdU hinv

theorem commute_of_mem_centralizer_of_inverts {U : Subgroup G} (h : Hyp711 V H E)
    (hU : U ∈ omegaSet V H E) {d y : G} (hdU : d ∈ U) (hy : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hinv : d * y * d⁻¹ = y⁻¹) {f : G} (hf : f ∈ iSub V H E) (hfy : Commute f y) :
    Commute f d := by
  classical
  have hUab : IsElemAbelian 2 U := isElemAbelian_of_mem_omegaSet h.elemAbelian hU
  have hd2 : d * d = 1 := elemAbelian_mul_self hUab hdU
  have hfd_mem : ⁅f, d⁆ ∈ U ⊓ iSub V H E := by
    have hU' : U ∈ omegaSet U H E := by rw [omegaSet_eq_of_mem hU]; exact hU
    have hOm : ∀ W ∈ omegaSet U H E, W ≤ H := by
      rw [omegaSet_eq_of_mem hU]; exact h.omega_le
    have h := commutator_mem_inf_iSub (V := U) (H := H) (E := E)
      (isElemAbelian_of_mem_omegaSet h.elemAbelian hU) (isTI_of_mem_omegaSet hU h.ti)
      h.abelian h.le h.normal hOm hU' (by rwa [iSub_eq_of_mem hU]) hdU
    rwa [iSub_eq_of_mem hU] at h
  have hcomm : Commute ⁅f, d⁆ y := commute_commutator_of_conj_eq_inv hd2 hinv hfy
  exact commutatorElement_eq_one_iff_commute.mp
    (eq_one_of_commutator_of_isTI h hU hdU hy hy1 hinv hfd_mem.1 hcomm)

theorem centralizer_iSub_fixed_le_centralizer {U P : Subgroup G} (h : Hyp711 V H E)
    (hU : U ∈ omegaSet V H E) {d : G} (hd : d ∈ U) (hPK : P ≤ kSub V H E)
    (hPab : ∀ a ∈ P, ∀ b ∈ P, Commute a b) (hP3 : ∀ a ∈ P, a ^ 3 = 1)
    (hdP : ∀ a ∈ P, d * a * d⁻¹ = a⁻¹) {y : G} (hyP : y ∈ P) (hy1 : y ≠ 1) :
    P ≤ Subgroup.centralizer
      ((iSub V H E ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  obtain ⟨hfI, hfC⟩ := Subgroup.mem_inf.mp hf
  have hfy : Commute f y := ((Subgroup.mem_centralizer_iff.mp hfC) y (by simp)).symm
  have hfd : Commute f d :=
    commute_of_mem_centralizer_of_inverts h hU hd (hP3 y hyP) hy1 (hdP y hyP) hfI hfy
  have hIleH : iSub V H E ≤ H :=
    h.iSub_le.trans (h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H))
  have hKN : kSub V H E ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    (kSub_le_of_forall_le h.omega_le).trans
      (le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal h.le h.normal))
  have hzN : z ∈ Subgroup.normalizer (iSub V H E : Set G) := hKN (hPK hz)
  have hzfI : z * f * z⁻¹ ∈ iSub V H E :=
    (Subgroup.mem_normalizer_iff.mp hzN f).mp hfI
  have hzy : Commute z y := hPab z hz y hyP
  have hzfC : Commute (z * f * z⁻¹) y := by
    have h := hfy.conj z
    have hzy_eq : z * y * z⁻¹ = y := by rw [hzy.eq]; group
    rwa [hzy_eq] at h
  have hzfd : Commute (z * f * z⁻¹) d :=
    commute_of_mem_centralizer_of_inverts h hU hd (hP3 y hyP) hy1 (hdP y hyP) hzfI hzfC
  have h1 : Commute f (z⁻¹ * d * z) := by
    have h := (Commute.conj_iff z).mp (by
      show Commute (z * f * z⁻¹) (z * (z⁻¹ * d * z) * z⁻¹)
      simpa [mul_assoc] using hzfd)
    simpa [mul_assoc] using h
  have hz2 : z ^ 2 = z⁻¹ := by
    have h : z ^ 2 * z = 1 := by simpa [pow_succ] using hP3 z hz
    exact eq_inv_of_mul_eq_one_left h
  have hzinv : z⁻¹ * z⁻¹ = z := by rw [← mul_inv_rev, ← pow_two, hz2, inv_inv]
  have hdz : d * z = z⁻¹ * d := by
    have := congrArg (fun t => t * d) (hdP z hz)
    simpa [mul_assoc] using this
  have hzeq : z⁻¹ * d * z = z * d := by
    calc z⁻¹ * d * z = z⁻¹ * (d * z) := by group
      _ = z⁻¹ * (z⁻¹ * d) := by rw [hdz]
      _ = (z⁻¹ * z⁻¹) * d := by group
      _ = z * d := by rw [hzinv]
  have h2 : Commute f (z * d) := hzeq ▸ h1
  have h3 : Commute f z := by
    have h := h2.mul_right hfd.inv_right
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h
  exact h3

private theorem fixedSubgroup_eq_top_of_isElemAbelian {U P : Subgroup G}
    (h : Hyp711 V H E) (hU : U ∈ omegaSet V H E) {d : G} (hd : d ∈ U)
    (hPK : P ≤ kSub V H E) [CFSG.IsElementaryAbelian 3 ↥P]
    (hdP : ∀ a ∈ P, d * a * d⁻¹ = a⁻¹)
    (α : ↥P →* MulAut ↥(iSub V H E))
    (hα : ∀ (z : ↥P) (a : ↥(iSub V H E)),
      ((α z) a : G) = (z : G) * (a : G) * (z : G)⁻¹)
    (hgen_eq : (⨆ a : ↥P, ⨆ (_ : a ≠ 1),
      CFSG.SolvableSignalizer.fixedSubgroup α a) = ⊤) :
    ∀ z : ↥P, CFSG.SolvableSignalizer.fixedSubgroup α z = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hPab : ∀ a ∈ P, ∀ b ∈ P, Commute a b := fun a ha b hb =>
    Subgroup.mul_comm_of_mem_isMulCommutative P ha hb
  have hP3 : ∀ a ∈ P, a ^ 3 = 1 := by
    intro a ha
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p 3 ↥P) (⟨a, ha⟩ : ↥P)
    exact congrArg Subtype.val h
  intro z
  rw [eq_top_iff, ← hgen_eq]
  refine iSup_le fun y => iSup_le fun hy1 => ?_
  have hy1' : (y : G) ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
  have hle := centralizer_iSub_fixed_le_centralizer h hU hd hPK hPab hP3 hdP y.2 hy1'
  intro a ha
  rw [CFSG.SolvableSignalizer.mem_fixedSubgroup] at ha ⊢
  have hya : (y : G) * (a : G) * (y : G)⁻¹ = (a : G) := by
    have h := congrArg (fun t : ↥(iSub V H E) => (t : G)) ha
    simpa [hα] using h
  have hcomm_y : Commute (a : G) y := by
    rw [Commute]
    calc (a : G) * (y : G) = ((y : G) * (a : G) * (y : G)⁻¹) * (y : G) := by rw [hya]
      _ = (y : G) * (a : G) := by group
  have hmemC : (a : G) ∈ iSub V H E ⊓ Subgroup.centralizer ({(y : G)} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨a.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hcomm_y.symm.eq
  have hcomm_z : (a : G) * (z : G) = (z : G) * (a : G) :=
    (Subgroup.mem_centralizer_iff.mp (hle z.2)) (a : G) hmemC
  apply Subtype.ext
  have hza : (z : G) * (a : G) * (z : G)⁻¹ = (a : G) := by
    calc (z : G) * (a : G) * (z : G)⁻¹ = ((a : G) * (z : G)) * (z : G)⁻¹ := by
          rw [← hcomm_z]
      _ = (a : G) := by group
  simpa [hα] using hza

private theorem le_centralizer_iSub_of_fixedSubgroup_eq_top {P : Subgroup G}
    (α : ↥P →* MulAut ↥(iSub V H E))
    (hα : ∀ (z : ↥P) (a : ↥(iSub V H E)),
      ((α z) a : G) = (z : G) * (a : G) * (z : G)⁻¹)
    (hfix : ∀ z : ↥P, CFSG.SolvableSignalizer.fixedSubgroup α z = ⊤) :
    P ≤ Subgroup.centralizer (iSub V H E : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have htop := hfix ⟨z, hz⟩
  have hmem : (⟨a, ha⟩ : ↥(iSub V H E)) ∈
      CFSG.SolvableSignalizer.fixedSubgroup α ⟨z, hz⟩ := by
    rw [htop]; exact Subgroup.mem_top _
  rw [CFSG.SolvableSignalizer.mem_fixedSubgroup] at hmem
  have h : (z : G) * a * (z : G)⁻¹ = a := by
    have := congrArg (fun t : ↥(iSub V H E) => (t : G)) hmem
    simpa [hα] using this
  calc a * (z : G) = ((z : G) * a * (z : G)⁻¹) * (z : G) := by rw [h]
    _ = (z : G) * a := by group

private theorem false_of_le_pCore_of_isElemAbelian {P : Subgroup G}
    [CFSG.IsElementaryAbelian 3 ↥P] (hPcard : 3 ^ 2 ≤ Nat.card ↥P)
    (hPJ : P ≤ pCoreOf 2 (kSub V H E)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hP3 : ∀ a ∈ P, a ^ 3 = 1 := by
    intro a ha
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p 3 ↥P) (⟨a, ha⟩ : ↥P)
    exact congrArg Subtype.val h
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥P = 1 := by rw [hbot]; simp
    rw [h1] at hPcard
    norm_num at hPcard
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hzG1 : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hJ2 : IsPGroup 2 (pCoreOf 2 (kSub V H E)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kSub V H E)
  have hodd : Odd (orderOf (z : G)) := by
    have hdvd : orderOf (z : G) ∣ 3 := orderOf_dvd_of_pow_eq_one (hP3 z z.2)
    exact Odd.of_dvd_nat ⟨1, by norm_num⟩ hdvd
  exact hzG1 (eq_one_of_mem_isPGroup_of_odd hJ2 (hPJ z.2) hodd)

theorem false_of_elementaryAbelian_inverted (h : Hyp711 V H E) {U P : Subgroup G}
    (hU : U ∈ omegaSet V H E) {d : G} (hd : d ∈ U) (hPK : P ≤ kSub V H E)
    [CFSG.IsElementaryAbelian 3 ↥P] (hPcard : 3 ^ 2 ≤ Nat.card ↥P)
    (hdP : ∀ a ∈ P, d * a * d⁻¹ = a⁻¹) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hIleH : iSub V H E ≤ H :=
    h.iSub_le.trans (h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H))
  have hPN : P ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    hPK.trans ((kSub_le_of_forall_le h.omega_le).trans
      (le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal h.le h.normal)))
  letI : CommGroup ↥P := IsMulCommutative.instCommGroup
  let α : ↥P →* MulAut ↥(iSub V H E) :=
    (Subgroup.normalizerMonoidHom (iSub V H E)).comp
      (P.subtype.codRestrict (Subgroup.normalizer (iSub V H E : Set G)) (fun z => hPN z.2))
  have hα : ∀ (z : ↥P) (a : ↥(iSub V H E)),
      ((α z) a : G) = (z : G) * (a : G) * (z : G)⁻¹ := by
    intro z a
    simp [α, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hI2 : IsPGroup 2 (iSub V H E) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le (h.iSub_le.trans h.pcore_le)
  have hnot3 : ¬ 3 ∣ Nat.card ↥(iSub V H E) := by
    rw [CFSG.Quasithin.card_eq_two_pow_of_isPGroup hI2]
    intro hdvd
    have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at h2
  have hgen_eq : (⨆ a : ↥P, ⨆ (_ : a ≠ 1),
      CFSG.SolvableSignalizer.fixedSubgroup α a) = ⊤ :=
    CFSG.SolvableSignalizer.iSup_fixedSubgroup_eq_top 3 Nat.prime_three α hPcard hnot3
  have hfix := fixedSubgroup_eq_top_of_isElemAbelian h hU hd hPK hdP α hα hgen_eq
  have hPcent := le_centralizer_iSub_of_fixedSubgroup_eq_top α hα hfix
  have hPJ : P ≤ pCoreOf 2 (kSub V H E) :=
    fun z hz => centralizer_iSub_le_pCoreOf h ⟨hPK hz, hPcent hz⟩
  exact false_of_le_pCore_of_isElemAbelian hPcard hPJ

theorem false_of_inverted_pair (h : Hyp711 V H E) {U : Subgroup G} (hU : U ∈ omegaSet V H E)
    {d : G} (hd : d ∈ U) {ρ c : G} (hρK : ρ ∈ kSub V H E) (hcK : c ∈ kSub V H E)
    (hρ : ρ ^ 3 = 1) (hc : c ^ 3 = 1) (hρc : Commute ρ c) (hdρ : d * ρ * d⁻¹ = ρ⁻¹)
    (hdc : d * c * d⁻¹ = c⁻¹) (hcρ : c ∉ Subgroup.zpowers ρ)
    (hρ1 : ρ ≠ 1) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set P : Subgroup G := Subgroup.closure ({ρ, c} : Set G) with hPdef
  have hPK : P ≤ kSub V H E := by
    rw [hPdef]
    exact (Subgroup.closure_le (kSub V H E)).mpr (by
      intro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]; exact hρK
      · rw [hz]; exact hcK)
  haveI hP_elem : CFSG.IsElementaryAbelian 3 ↥P := by
    rw [hPdef]
    exact isElementaryAbelian_closure_pair hρ hc hρc.eq
  have hPcard : Nat.card ↥P = 9 := by
    rw [hPdef]
    have h := card_closure_pair hρ hρ1 hc hρc.eq hcρ
    norm_num at h ⊢
    exact h
  have hPab : ∀ a ∈ P, ∀ b ∈ P, Commute a b := by
    intro a ha b hb
    exact congrArg Subtype.val ((hP_elem.toIsMulCommutative.is_comm).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hdP : ∀ a ∈ P, d * a * d⁻¹ = a⁻¹ := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with ha | ha
        · rw [ha]; exact hdρ
        · rw [ha]; exact hdc
    | one => simp
    | mul a b ha hb iha ihb =>
        calc d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
          _ = a⁻¹ * b⁻¹ := by rw [iha, ihb]
          _ = (a * b)⁻¹ := by
              rw [mul_inv_rev]
              exact (hPab a ha b hb).inv_inv.eq
    | inv a ha iha =>
        have h : d * a⁻¹ * d⁻¹ = (d * a * d⁻¹)⁻¹ := by group
        rw [h, iha, inv_inv]
  exact false_of_elementaryAbelian_inverted h hU hd hPK (by rw [hPcard]; norm_num) hdP

end CFSG.LocalAnalysis.WeakClosure81.A6Case
