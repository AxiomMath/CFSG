module

public import CFSG.RankThree.PartOne.K1327.Transport
public import CFSG.RankThree.PartOne.K1327.Dichotomy
public import CFSG.RankThree.PartOne.K1327.Generic
public import CFSG.RankThree.PartOne.K1327.StepA
public import CFSG.RankThree.PartOne.K1327.Special

public section

namespace CFSG.RankThree.PartOne.K1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem line_commute (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hT : ¬ Outcome152Five p E A (lieGenerated p E))
    (hEA : E = A) (hpf : p ∣ 2 ^ f + 1) {z : MulAut E} (hz : Inverter p E z) (Bd : Bridge p E)
    (fr : Row8Frame p A L E f K) (hZ : Subgroup.center L = ⊥) {r : ℕ} (hr : r.Prime)
    (hrq : r ∣ Nat.card K - 1) {zs : MulAut E} (hcore : fr.Core c r zs)
    (hR0 : fr.lft (Rr K r) ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G))
    (hR0' : fr.lft (Rr K r) ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G))
    (hRE : ∀ x ∈ fr.lft (Rr K r), ∀ e ∈ E, x * e = e * x) {b : G} (hb : b ∈ autFixedInG E zs)
    (hb1 : b ≠ 1) {u : G} (huV : u ∈ Vof p (Jof p (fr.lft (Rr K r)))) (hub : u * b = b * u) :
    Commute u c := by
  set R := fr.lft (Rr K r) with hRdef
  set J := Jof p R with hJdef
  have hp := h.prime
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hbE : b ∈ E := Subgroup.map_subtype_le _ hb
  obtain ⟨g₀, hg₀X, hg₀⟩ := hcore.conj
  obtain ⟨y, hy, hyg⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hg₀X)
  have hty : zs = conjAut E y hy * fr.r₁ * (conjAut E y hy)⁻¹ := by
    rw [hyg]
    exact hg₀.symm
  obtain ⟨I, hI, hKI, halt⟩ := exists_member hS hRe h hF13 hT hEA hpf hcore.mem hcore.kfAt
    fr.mem₁L hy hty hb hb1
  rcases halt with hi | hiii
  ·
    have hKb := eq_of_alt_one hS hTwo hFull h hEA hpf hcore.mem hcore.kfAt hb hb1 hI hKI hi
    have hLift := KFAt.toLiftAt hcore.kfAt
    have hR1 : R ≠ ⊥ := by
      intro h0
      have hcardR : Nat.card R = r := by
        rw [hRdef, fr.lft_card hZ]
        exact rootsOfUnity_card hr hrq
      rw [h0, Subgroup.card_bot] at hcardR
      exact hr.one_lt.ne hcardR
    have hcK : c ∈ kZero p E zs := by
      have : c ∈ autMovedInG E zs := by
        rw [hcore.mov]
        exact Subgroup.mem_zpowers c
      exact hcore.kfAt.2.2.2.1 this
    have hEM : ∀ e ∈ E, e ∈ Subgroup.centralizer (R : Set G) := fun e he => by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact hRE x hx e he
    have hcJ : c ∈ J := mem_Jof_of_pow hp (hEM c hcE) (Sec12Three.pow_eq_one_of_mem_E h hcE)
    have hJM : J ≤ Subgroup.centralizer (R : Set G) := by
      rw [hJdef, Jof_def]
      unfold pElementSubgroup
      rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
    have huR : ∀ x ∈ R, u * x = x * u := fun x hx =>
      (Subgroup.mem_centralizer_iff.1 (hJM (Vof_le p J huV)) x hx).symm
    exact commute_of_member hp hcore.kfAt.2.1 hLift.1 hLift.2.1 hKb hcore.R_le hR1 hcK
      (fun x hx => (hRE x hx c hcE).symm) (Sec12Three.pow_eq_one_of_mem_E h hcE)
      (Vof_conj p J c hcJ) (Vof_solvable_coprime hp J).2 huV hub huR
  ·
    have hbz : zs ⟨b, hbE⟩ = ⟨b, hbE⟩ := by
      obtain ⟨e, he, hbe⟩ := Subgroup.mem_map.1 hb
      have : (⟨b, hbE⟩ : ↥E) = e := Subtype.ext hbe.symm
      rw [this]
      exact he
    obtain ⟨k, hk, hkK, hkz⟩ := hcore.kfAt.2.2.2.2
    have hzsI : zs ∈ torusImage E I := Sec12Three.mem_torusImage_iff.2 ⟨k, hKI hkK, hk, hkz⟩
    have hIb : I ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.1 hI).1
    obtain ⟨d'', hd'', hbd⟩ := exists_third h hF13 hcard hz Bd fr.mem₀ fr.mem₁ hcore.mem fr.ord₀₁
      fr.mem₀L fr.mem₁L hcore.comm hcore.notL ⟨g₀, hg₀X, hg₀⟩ hbE hbz hIb hiii hzsI
    exact commute_of_third hp h hF hF13 hcard hEA Bd fr hZ hr hrq hcore hR0 hR0' hRE hd'' hbd hb1
      huV hub


omit [Finite G] in
theorem le_normalizer_Vof (p : ℕ) (J : Subgroup G) : J ≤ Subgroup.normalizer (Vof p J : Set G) := by
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    exact Vof_conj p J j hj v hv
  · intro hv
    have := Vof_conj p J j⁻¹ (J.inv_mem hj) _ hv
    simpa [mul_assoc] using this

theorem theta_Jof_eq_bot (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hT : ¬ Outcome152Five p E A (lieGenerated p E))
    (hEA : E = A) (hf2 : 2 ≤ f) (hpf : p ∣ 2 ^ f + 1) {z : MulAut E} (hz : Inverter p E z)
    (Bd : Bridge p E) (fr : Row8Frame p A L E f K) (hZ : Subgroup.center L = ⊥) {r : ℕ}
    (hr : r.Prime) (hrq : r ∣ Nat.card K - 1) {zs : MulAut E} (hcore : fr.Core c r zs)
    (hR0 : fr.lft (Rr K r) ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G))
    (hR0' : fr.lft (Rr K r) ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G))
    (hRE : ∀ x ∈ fr.lft (Rr K r), ∀ e ∈ E, x * e = e * x)
    (hmodel : StatedClassicalModel (↥(Jof p (fr.lft (Rr K r))) ⧸
      aschbacherSolvableCore p ↥(Jof p (fr.lft (Rr K r)))) .PSU 4 2 f) :
    aschbacherSolvableCore p ↥(Jof p (fr.lft (Rr K r))) = ⊥ := by
  set R := fr.lft (Rr K r) with hRdef
  set J := Jof p R with hJdef
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hEM : ∀ e ∈ E, e ∈ Subgroup.centralizer (R : Set G) := fun e he => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hRE x hx e he
  have hEJ : ∀ e ∈ E, e ∈ J := fun e he =>
    mem_Jof_of_pow hp (hEM e he) (Sec12Three.pow_eq_one_of_mem_E h he)
  have hcJ : c ∈ J := hEJ c hcE
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  have hdat := RefFacts.ElemData.of_isElementaryAbelian hp hp2 hE
  have hBcard : Nat.card (autFixedInG E zs) = p ^ 2 := by
    have h1 := RefFacts.card_eq_inf_fixed_mul hdat hcore.mem.1 (B := ⊤) le_top
    rw [Subgroup.card_top, top_inf_eq, hcard] at h1
    have h2 : Nat.card ↥(autFixed E zs) = p ^ 2 := by
      have : Nat.card ↥(autFixed E zs) * p = p ^ 2 * p := by rw [← h1]; ring
      exact Nat.eq_of_mul_eq_mul_right hp.pos this
    show Nat.card ↥((autFixed E zs).map E.subtype) = p ^ 2
    rw [Subgroup.card_map_of_injective E.subtype_injective, h2]
  have hBE : autFixedInG E zs ≤ E := Subgroup.map_subtype_le _
  have hB : IsElemAbelian p (autFixedInG E zs) :=
    ⟨(isElementaryAbelian_of_le' hE hBE).toIsMulCommutative, fun x hx =>
      Sec12Three.pow_eq_one_of_mem_E h (hBE hx)⟩
  have hBV : autFixedInG E zs ≤ Subgroup.normalizer (Vof p J : Set G) := fun b hb =>
    le_normalizer_Vof p J (hEJ b (hBE hb))
  have hVsc := Vof_solvable_coprime hp J
  have hcomm : ∀ b ∈ autFixedInG E zs, b ≠ 1 →
      ∀ u ∈ Vof p J ⊓ Subgroup.centralizer ({b} : Set G), Commute u c := by
    intro b hb hb1 u hu
    exact line_commute hS hRe hTwo hFull h hF hF13 hT hEA hpf hz Bd fr hZ hr hrq hcore hR0 hR0'
      hRE hb hb1 hu.1 (Subgroup.mem_centralizer_singleton_iff.1 hu.2)
  have hVc := commute_of_commute_centralizers hp hB hBcard hBV hVsc.2 hcomm
  have hgen : Subgroup.closure {x : ↥J | ∃ k : ℕ, orderOf x = p ^ k} = ⊤ := by
    have h1 : Subgroup.closure (((↑) : ↥J → G) ⁻¹'
        {x : G | x ∈ Subgroup.centralizer (R : Set G) ∧ ∃ k : ℕ, orderOf x = p ^ k}) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    refine eq_top_iff.2 (h1.symm.le.trans (Subgroup.closure_mono ?_))
    intro x hx
    obtain ⟨-, k, hk⟩ := hx
    exact ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk⟩
  have hcp : orderOf (⟨c, hcJ⟩ : ↥J) = p := by
    rw [Subgroup.orderOf_mk]
    exact Sec12Three.orderOf_c h
  have hcent : ∀ v ∈ aschbacherSolvableCore p ↥J, v * ⟨c, hcJ⟩ = ⟨c, hcJ⟩ * v := by
    intro v hv
    have hvV : (v : G) ∈ Vof p J := ⟨v, hv, rfl⟩
    exact Subtype.ext (hVc _ hvV).eq
  exact theta_eq_bot_of_commute hGA hp hf2 hgen hmodel hcp hcent

theorem statedModel_Jof (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hT : ¬ Outcome152Five p E A (lieGenerated p E))
    (hEA : E = A) (hf2 : 2 ≤ f) (hpf : p ∣ 2 ^ f + 1) {z : MulAut E} (hz : Inverter p E z)
    (Bd : Bridge p E) (fr : Row8Frame p A L E f K) (hZ : Subgroup.center L = ⊥) {r : ℕ}
    (hr : r.Prime) (hrq : r ∣ Nat.card K - 1) {zs : MulAut E} (hcore : fr.Core c r zs)
    (hR0 : fr.lft (Rr K r) ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G))
    (hR0' : fr.lft (Rr K r) ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G))
    (hRE : ∀ x ∈ fr.lft (Rr K r), ∀ e ∈ E, x * e = e * x)
    (hmodel : StatedClassicalModel (↥(Jof p (fr.lft (Rr K r))) ⧸
      aschbacherSolvableCore p ↥(Jof p (fr.lft (Rr K r)))) .PSU 4 2 f) :
    StatedClassicalModel ↥(Jof p (fr.lft (Rr K r))) .PSU 4 2 f := by
  have hθ := theta_Jof_eq_bot hGA hS hRe hTwo hFull h hF hF13 hT hEA hf2 hpf hz Bd fr hZ hr hrq hcore
    hR0 hR0' hRE hmodel
  exact Equivariance.statedClassicalModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot) hmodel

end CFSG.RankThree.PartOne.K1327
