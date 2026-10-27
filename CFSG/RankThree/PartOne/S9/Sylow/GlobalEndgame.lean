module

public import CFSG.RankThree.PartOne.S9.Sylow.GlobalOddCore
import CFSG.RankThree.PGroups.SolvableFittingSelfCentralizing
import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalLemmas
public import CFSG.RankThree.PartOne.S9.Sylow.ResidualLocal

public section

namespace CFSG.RankThree.PartOne.Sec9B

open CFSG Subgroup CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem coprime_orderOf_of_isPGroup {p s : ℕ} (hp : p.Prime) (hs : s.Prime) (hps : p ≠ s)
    {P : Subgroup G} (hP : IsPGroup p ↥P) {x : G} (hx : x ∈ P) : Nat.Coprime (orderOf x) s := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have h1 : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h2 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  exact Nat.Coprime.coprime_dvd_left h2
    (Nat.Coprime.pow_left k ((Nat.coprime_primes hp hs).mpr hps))

structure Endgame [Finite G] (p : ℕ) (A B R E : Subgroup G) (b c : G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  A_pgroup : IsPGroup p ↥A
  B_le : B ≤ A
  A_le_C : A ≤ Subgroup.centralizer ({b} : Set G)
  b_mem : b ∈ B
  c_mem : c ∈ B
  R_two : IsPGroup 2 ↥R
  R_le_L : R ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G))
  E_le_L : E ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G))
  A_normalizes_R : A ≤ Subgroup.normalizer (R : Set G)
  A_normalizes_E : A ≤ Subgroup.normalizer (E : Set G)
  R_normalizes_E : R ≤ Subgroup.normalizer (E : Set G)
  comm_ER : ⁅E, R⁆ = E
  comm_RA : ⁅R, A⁆ = R
  minimal : ∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U → U = ⊥
  global : ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({b} : Set G)), A⁆ = ⊥
  odd_core : ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p → ∀ X : Subgroup G,
    X ≤ inSubgroup (pCore s) (Subgroup.normalizer (Subgroup.zpowers b : Set G)) →
    R ⊔ A ≤ Subgroup.normalizer (X : Set G) → (∀ x ∈ X, x ^ s = 1) → ⁅⁅X, X⁆, X⁆ = ⊥ →
    ⁅R, X⁆ ≠ ⊥ → ⁅B, X⁆ = ⊥
  E_not_odd : ¬ E ≤ inSubgroup (pPrimeCore 2) (Subgroup.centralizer ({b} : Set G))
  E_odd_c : E ≤ inSubgroup (pPrimeCore 2) (Subgroup.centralizer ({c} : Set G))

@[expose] noncomputable def endK (p : ℕ) (b : G) (E : Subgroup G) : Subgroup G :=
  conjClosure (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G))) E

theorem centralizer_le_normalizer_theta (p : ℕ) (b : G) :
    Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.normalizer (inSubgroup (aschbacherSolvableCore p)
        (Subgroup.centralizer ({b} : Set G)) : Set G) :=
  Subgroup.le_normalizer.trans
    (SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p _)

theorem theta_le_centralizer (p : ℕ) (b : G) :
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G)) ≤
      Subgroup.centralizer ({b} : Set G) := Subgroup.map_subtype_le _

theorem theta_le_normalizer_endK (p : ℕ) (b : G) (E : Subgroup G) :
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G)) ≤
      Subgroup.normalizer (endK p b E : Set G) :=
  le_normalizer_conjClosure _ _

theorem le_endK (p : ℕ) (b : G) (E : Subgroup G) : E ≤ endK p b E := le_conjClosure _ _

theorem E_le_normalizer_endO (s : ℕ) (p : ℕ) (b : G) (E : Subgroup G) :
    E ≤ Subgroup.normalizer (inSubgroup (pCore s) (endK p b E) : Set G) := fun _ hx =>
  SteinbergBY.le_normalizer_inSubgroup_pCore s _ (le_endK p b E hx)

namespace Endgame

variable [Finite G] {p : ℕ} {A B R E : Subgroup G} {b c : G} (h : Endgame p A B R E b c)

include h

theorem K_le_L : endK p b E ≤ inSubgroup (aschbacherSolvableCore p)
    (Subgroup.centralizer ({b} : Set G)) := conjClosure_le_of_le h.E_le_L

theorem A_normalizes_L : A ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore p)
    (Subgroup.centralizer ({b} : Set G)) : Set G) := fun _ hx =>
  centralizer_le_normalizer_theta p b (h.A_le_C hx)

theorem A_normalizes_K : A ≤ Subgroup.normalizer (endK p b E : Set G) := fun _ hx =>
  mem_normalizer_conjClosure_of_normalizes (h.A_normalizes_L hx) (h.A_normalizes_E hx)

theorem B_normalizes_K : B ≤ Subgroup.normalizer (endK p b E : Set G) := fun _ hx =>
  h.A_normalizes_K (h.B_le hx)

theorem R_normalizes_K : R ≤ Subgroup.normalizer (endK p b E : Set G) := fun _ hx =>
  theta_le_normalizer_endK p b E (h.R_le_L hx)

theorem K_solvable : Group.IsSolvable ↥(endK p b E) :=
  isSolvable_of_le_theta h.prime h.K_le_L

theorem K_not_dvd : ¬ p ∣ Nat.card ↥(endK p b E) :=
  not_dvd_card_of_le_theta h.prime h.K_le_L

theorem K_even : 2 ∣ Nat.card ↥(endK p b E) := by
  by_contra hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card ↥(endK p b E)) := Nat.prime_two.coprime_iff_not_dvd.mpr hodd
  have h1 := le_inSubgroup_pPrimeCore hcop h.K_le_L (theta_le_normalizer_endK p b E)
  have h2 := inSubgroup_pPrimeCore_mono (r := 2) (theta_le_centralizer p b)
    (centralizer_le_normalizer_theta p b)
  exact h.E_not_odd ((le_endK p b E).trans (h1.trans h2))

theorem R_normalizes_O (s : ℕ) :
    R ≤ Subgroup.normalizer (inSubgroup (pCore s) (endK p b E) : Set G) := fun _ hx =>
  SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore s _ (h.R_normalizes_K hx)

theorem A_normalizes_O (s : ℕ) :
    A ≤ Subgroup.normalizer (inSubgroup (pCore s) (endK p b E) : Set G) := fun _ hx =>
  SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore s _ (h.A_normalizes_K hx)

theorem B_normalizes_O (s : ℕ) :
    B ≤ Subgroup.normalizer (inSubgroup (pCore s) (endK p b E) : Set G) := fun _ hx =>
  h.A_normalizes_O s (h.B_le hx)

theorem active_le_centralizer {s : ℕ} (hs : s.Prime)
    (hact : ⁅E, inSubgroup (pCore s) (endK p b E)⁆ ≠ ⊥) :
    inSubgroup (pCore s) (endK p b E) ≤ Subgroup.centralizer (B : Set G) := by
  set M := inSubgroup (pCore s) (endK p b E) with hM
  have hMs : IsPGroup s ↥M := SteinbergBY.isPGroup_inSubgroup_pCore s _
  have hRM : R ≤ Subgroup.normalizer (M : Set G) := h.R_normalizes_O s
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := h.A_normalizes_O s
  have hBM : B ≤ Subgroup.normalizer (M : Set G) := h.B_normalizes_O s
  have hEM : E ≤ Subgroup.normalizer (M : Set G) := E_le_normalizer_endO s p b E
  have hLK := theta_le_normalizer_endK p b E
  have ha : ¬ R ≤ Subgroup.centralizer (M : Set G) := by
    intro hRC
    apply hact
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    calc E = ⁅E, R⁆ := h.comm_ER.symm
      _ ≤ Subgroup.centralizer (M : Set G) := commutator_le_centralizer_of_centralizes hEM hRC
  have hb : ¬ A ≤ Subgroup.centralizer (M : Set G) := by
    intro hAC
    apply ha
    calc R = ⁅R, A⁆ := h.comm_RA.symm
      _ ≤ Subgroup.centralizer (M : Set G) := commutator_le_centralizer_of_centralizes hRM hAC
  have hs2 : s ≠ 2 := by
    rintro rfl
    apply hb
    have hMC : M ≤ inSubgroup (pCore 2) (Subgroup.centralizer ({b} : Set G)) :=
      (SteinbergBY.inSubgroup_pCore_mono h.K_le_L hLK).trans
        (SteinbergBY.inSubgroup_pCore_mono (theta_le_centralizer p b)
          (centralizer_le_normalizer_theta p b))
    have hglob : A ≤ Subgroup.centralizer
        (inSubgroup (pCore 2) (Subgroup.centralizer ({b} : Set G)) : Set G) := by
      have := h.global
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at this
      exact this
    exact hglob.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hMC))
  have hMne : M ≠ ⊥ := fun h0 => hact (by rw [h0, Subgroup.commutator_bot_right])
  have : Fact s.Prime := ⟨hs⟩
  have hsp : s ≠ p := by
    rintro rfl
    apply h.K_not_dvd
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hMs
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hMne (Subgroup.eq_bot_of_card_eq M (by simpa using hn))
    exact (dvd_pow_self s hn0).trans
      (hn ▸ Subgroup.card_dvd_of_le (SteinbergBY.inSubgroup_pCore_le s _))
  obtain ⟨X, hXM, hX1, hXnorm, hXexp, hXcomm, hXdet⟩ := exists_critical hs hs2 hMs hMne
  have hXO : X ≤ inSubgroup (pCore s) (Subgroup.normalizer (Subgroup.zpowers b : Set G)) :=
    hXM.trans ((SteinbergBY.inSubgroup_pCore_mono h.K_le_L hLK).trans
      ((SteinbergBY.inSubgroup_pCore_mono (theta_le_centralizer p b)
        (centralizer_le_normalizer_theta p b)).trans
        (SteinbergBY.inSubgroup_pCore_mono (Sec9A.centralizer_le_normalizer_zpowers b)
          (normalizer_zpowers_le_normalizer_centralizer b))))
  have hRAX : R ⊔ A ≤ Subgroup.normalizer (X : Set G) :=
    sup_le (fun r hr => hXnorm r (hRM hr)) (fun a ha => hXnorm a (hAM ha))
  have hXX : ⁅⁅X, X⁆, X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (Subgroup.commutator_mono le_rfl hXM).trans (hXcomm.trans inf_le_right)
  have hRX : ⁅R, X⁆ ≠ ⊥ := by
    intro hRX0
    apply ha
    intro r hr
    have hrC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRX0 hr
    have hfix : ∀ x ∈ X, r * x * r⁻¹ = x := fun x hx => by
      have h' := Subgroup.mem_centralizer_iff.mp hrC x hx
      calc r * x * r⁻¹ = x * r * r⁻¹ := by rw [← h']
        _ = x := by group
    refine Subgroup.mem_centralizer_iff.mpr fun m hm => ?_
    have := hXdet r (hRM hr) hfix
      (coprime_orderOf_of_isPGroup Nat.prime_two hs (Ne.symm hs2) h.R_two hr) m hm
    calc m * r = (r * m * r⁻¹) * r := by rw [this]
      _ = r * m := by group
  have hBX := h.odd_core s hs hs2 hsp X hXO hRAX hXexp hXX hRX
  intro m hm
  refine Subgroup.mem_centralizer_iff.mpr fun b' hb' => ?_
  have hfix : ∀ x ∈ X, b' * x * b'⁻¹ = x := fun x hx => by
    have hbC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBX hb'
    have h' := Subgroup.mem_centralizer_iff.mp hbC x hx
    calc b' * x * b'⁻¹ = x * b' * b'⁻¹ := by rw [← h']
      _ = x := by group
  have := hXdet b' (hBM hb') hfix
    (coprime_orderOf_of_isPGroup h.prime hs (Ne.symm hsp) (h.A_pgroup.to_le h.B_le) hb') m hm
  calc b' * m = (b' * m * b'⁻¹) * b' := by group
    _ = m * b' := by rw [this]

end Endgame

@[expose] noncomputable def endN (p : ℕ) (b : G) (E : Subgroup G) : Subgroup G :=
  ⨆ s : {s : ℕ // s.Prime ∧ ⁅E, inSubgroup (pCore s) (endK p b E)⁆ ≠ ⊥},
    inSubgroup (pCore s.1) (endK p b E)

@[expose] noncomputable def endP (p : ℕ) (b : G) (E : Subgroup G) : Subgroup G :=
  ⨆ s : {s : ℕ // s.Prime ∧ ⁅E, inSubgroup (pCore s) (endK p b E)⁆ = ⊥},
    inSubgroup (pCore s.1) (endK p b E)

theorem endN_le_endK (p : ℕ) (b : G) (E : Subgroup G) : endN p b E ≤ endK p b E :=
  iSup_le fun s => SteinbergBY.inSubgroup_pCore_le s.1 _

theorem endP_le_endK (p : ℕ) (b : G) (E : Subgroup G) : endP p b E ≤ endK p b E :=
  iSup_le fun s => SteinbergBY.inSubgroup_pCore_le s.1 _

theorem endK_le_normalizer_endN (p : ℕ) (b : G) (E : Subgroup G) :
    endK p b E ≤ Subgroup.normalizer (endN p b E : Set G) := fun _ hg =>
  mem_normalizer_iSup fun s => SteinbergBY.le_normalizer_inSubgroup_pCore s.1 _ hg

theorem endP_le_centralizer (p : ℕ) (b : G) (E : Subgroup G) :
    endP p b E ≤ Subgroup.centralizer (endK p b E : Set G) := by
  refine iSup_le fun s => ?_
  have hE : E ≤ Subgroup.centralizer (inSubgroup (pCore s.1) (endK p b E) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp s.2.2
  have hK : endK p b E ≤ Subgroup.centralizer (inSubgroup (pCore s.1) (endK p b E) : Set G) :=
    conjClosure_le hE fun g hg => mem_normalizer_centralizer_of_mem_normalizer
      (SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore s.1 _
        (theta_le_normalizer_endK p b E hg))
  intro x hx
  exact Subgroup.mem_centralizer_iff.mpr fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (hK hk) x hx).symm

theorem fitting_le_endN_sup_endP (p : ℕ) (b : G) (E : Subgroup G) [Finite G] :
    inSubgroup fittingSubgroup (endK p b E) ≤ endN p b E ⊔ endP p b E := by
  rw [inSubgroup, LocalCores.fittingSubgroup_eq_iSup_pCore, Subgroup.map_iSup]
  refine iSup_le fun s => ?_
  have hsp : (s : ℕ).Prime := Nat.prime_of_mem_primeFactors s.2
  by_cases hact : ⁅E, inSubgroup (pCore (s : ℕ)) (endK p b E)⁆ = ⊥
  · exact le_sup_of_le_right (le_iSup (fun t : {t : ℕ // t.Prime ∧
      ⁅E, inSubgroup (pCore t) (endK p b E)⁆ = ⊥} => inSubgroup (pCore t.1) (endK p b E))
      ⟨s, hsp, hact⟩)
  · exact le_sup_of_le_left (le_iSup (fun t : {t : ℕ // t.Prime ∧
      ⁅E, inSubgroup (pCore t) (endK p b E)⁆ ≠ ⊥} => inSubgroup (pCore t.1) (endK p b E))
      ⟨s, hsp, hact⟩)

theorem inf_centralizer_fitting_le {K : Subgroup G} [Finite G] (hK : Group.IsSolvable ↥K) :
    K ⊓ Subgroup.centralizer (inSubgroup fittingSubgroup K : Set G) ≤
      inSubgroup fittingSubgroup K := by
  intro k ⟨hkK, hkC⟩
  have : (⟨k, hkK⟩ : ↥K) ∈ Subgroup.centralizer (fittingSubgroup ↥K : Set ↥K) := by
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => Subtype.ext ?_
    exact Subgroup.mem_centralizer_iff.mp hkC y.1 (Subgroup.mem_map_of_mem K.subtype hy)
  exact ⟨⟨k, hkK⟩, CFSG.RankThree.PGroups.solvable_fitting_self_centralizing ↥K this, rfl⟩

namespace Endgame

variable [Finite G] {p : ℕ} {A B R E : Subgroup G} {b c : G} (h : Endgame p A B R E b c)

include h

theorem endN_le_centralizer : endN p b E ≤ Subgroup.centralizer (B : Set G) :=
  iSup_le fun s => h.active_le_centralizer s.2.1 s.2.2

theorem B_le_normalizer_endP : B ≤ Subgroup.normalizer (endP p b E : Set G) := fun _ hx =>
  mem_normalizer_iSup fun s => h.B_normalizes_O s.1 hx

theorem centralizer_endN_le : ∀ k ∈ endK p b E, (∀ x ∈ endN p b E, x * k = k * x) →
    k ∈ endN p b E ⊔ endP p b E := by
  intro k hk hkN
  have : Group.IsSolvable ↥(endK p b E) := h.K_solvable
  have hN : endN p b E ≤ Subgroup.centralizer ({k} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hkN x hx)
  have hP : endP p b E ≤ Subgroup.centralizer ({k} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (endP_le_centralizer p b E hx) k hk).symm
  have hF := (fitting_le_endN_sup_endP p b E).trans (sup_le hN hP)
  have hkF : k ∈ Subgroup.centralizer (inSubgroup fittingSubgroup (endK p b E) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hF hy)
  exact fitting_le_endN_sup_endP p b E (inf_centralizer_fitting_le h.K_solvable ⟨hk, hkF⟩)

theorem contradiction : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨h.prime⟩
  set K := endK p b E with hK
  have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥B) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp (h.A_pgroup.to_le h.B_le)
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr h.K_not_dvd).symm
  have hfac := central_complement_of_fixed (K := K) (B := B) (N := endN p b E)
    (P := endP p b E) h.K_solvable hcop h.B_normalizes_K (endN_le_endK p b E)
    (endP_le_endK p b E) (endK_le_normalizer_endN p b E)
    (fun x hx k hk => (Subgroup.mem_centralizer_iff.mp (endP_le_centralizer p b E hx) k hk).symm)
    h.B_le_normalizer_endP
    (fun b' hb' x hx => by
      have := Subgroup.mem_centralizer_iff.mp (h.endN_le_centralizer hx) b' hb'
      calc b' * x * b'⁻¹ = x * b' * b'⁻¹ := by rw [this]
        _ = x := by group)
    h.centralizer_endN_le
  set Oc := inSubgroup (pPrimeCore 2) (Subgroup.centralizer ({c} : Set G)) with hOc
  have hKM0 : ∀ k ∈ K, ∀ m ∈ K ⊓ Oc, k * m * k⁻¹ ∈ K ⊓ Oc := by
    intro k hk m hm
    obtain ⟨z, hzK, hzc, c', hc'K, hc'B, rfl⟩ := hfac k hk
    have hc'C : c' ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hc'B c h.c_mem).symm
    have hc'N : c' ∈ Subgroup.normalizer (Oc : Set G) :=
      normalizer_le_normalizer_inSubgroup_pPrimeCore 2 _ (Subgroup.le_normalizer hc'C)
    have hw : c' * m * c'⁻¹ ∈ K ⊓ Oc :=
      ⟨K.mul_mem (K.mul_mem hc'K hm.1) (K.inv_mem hc'K),
        (Subgroup.mem_normalizer_iff.mp hc'N m).mp hm.2⟩
    have hzw : z * (c' * m * c'⁻¹) = (c' * m * c'⁻¹) * z := hzc _ hw.1
    have : z * c' * m * (z * c')⁻¹ = c' * m * c'⁻¹ := by
      calc z * c' * m * (z * c')⁻¹ = z * (c' * m * c'⁻¹) * z⁻¹ := by group
        _ = (c' * m * c'⁻¹) * z * z⁻¹ := by rw [hzw]
        _ = c' * m * c'⁻¹ := by group
    rw [this]
    exact hw
  have hKM0n : K ≤ Subgroup.normalizer ((K ⊓ Oc : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_of_forall_conj_mem (hKM0 k hk) (fun m hm => by
      simpa using hKM0 k⁻¹ (K.inv_mem hk) m hm)
  have hM0cop : Nat.Coprime 2 (Nat.card ↥(K ⊓ Oc)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (coprime_card_inSubgroup_pPrimeCore (r := 2) _)
  have hM0 : K ⊓ Oc ≤ inSubgroup (pPrimeCore 2) K :=
    le_inSubgroup_pPrimeCore hM0cop inf_le_left hKM0n
  have hEOK : E ≤ inSubgroup (pPrimeCore 2) K := fun e he =>
    hM0 ⟨le_endK p b E he, h.E_odd_c he⟩
  have hKOK : K ≤ inSubgroup (pPrimeCore 2) K :=
    conjClosure_le hEOK fun g hg =>
      normalizer_le_normalizer_inSubgroup_pPrimeCore 2 K (theta_le_normalizer_endK p b E hg)
  have hcop2 : Nat.Coprime 2 (Nat.card ↥K) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hKOK)
      (coprime_card_inSubgroup_pPrimeCore (r := 2) K)
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop2 h.K_even

end Endgame

end CFSG.RankThree.PartOne.Sec9B
