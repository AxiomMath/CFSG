module

public import CFSG.RankThree.PartOne.K133.ResData
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.RankThree.PartOne.K133X

open CFSG CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.OutStructure
open Subgroup

theorem exists_inner_ne_one_of_plane {X : Type*} [Group X] {p : ℕ} (hp : p.Prime)
    (hO : OutPChain p X) {Ē C : Subgroup (MulAut X)} (hE : IsElementaryAbelian p Ē) (hCĒ : C ≤ Ē)
    (hcard : Nat.card C = p ^ 2) : ∃ c ∈ C, c ≠ 1 ∧ c ∈ Inn X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpow : ∀ x ∈ C, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian (A := Ē) x (hCĒ hx)
  have hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.is_comm.comm ⟨x, hCĒ hx⟩ ⟨y, hCĒ hy⟩)
  have hCne : C ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  obtain ⟨a, haC, ha1⟩ : ∃ a ∈ C, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hCne (Subgroup.eq_bot_iff_forall _ |>.2 hcon)
  have haord : orderOf a = p := orderOf_eq_prime (hpow a haC) ha1
  have : Finite (Subgroup.zpowers a) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, haord]; exact hp.ne_zero)
  obtain ⟨b, hbC, hba⟩ : ∃ b ∈ C, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle : C ≤ Subgroup.zpowers a := fun x hx => hcon x hx
    have h1 : Nat.card C ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, haord, hcard] at h1
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hb1 : b ≠ 1 := fun h => hba (h ▸ one_mem _)
  have hbord : orderOf b = p := orderOf_eq_prime (hpow b hbC) hb1
  have : Finite (Subgroup.zpowers b) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hbord]; exact hp.ne_zero)
  have ha' : a ^ (p ^ 1) ∈ Inn X := by rw [pow_one, hpow a haC]; exact (Inn X).one_mem
  have hb' : b ^ (p ^ 1) ∈ Inn X := by rw [pow_one, hpow b hbC]; exact (Inn X).one_mem
  rcases OutPChain.comparable hO (hcomm a haC b hbC) ha' hb' with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine ⟨a * b ^ m, C.mul_mem haC (C.zpow_mem hbC m), ?_, hm⟩
    intro h1
    have hab : a ∈ Subgroup.zpowers b := by
      have : a = (b ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) m)
    have hle : Subgroup.zpowers a ≤ Subgroup.zpowers b := (Subgroup.zpowers_le).2 hab
    have hc : Nat.card (Subgroup.zpowers b) ≤ Nat.card (Subgroup.zpowers a) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, haord, hbord]
    have heq : Subgroup.zpowers a = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle hc
    exact hba (heq ▸ Subgroup.mem_zpowers b)
  · refine ⟨b * a ^ m, C.mul_mem hbC (C.zpow_mem haC m), ?_, hm⟩
    intro h1
    exact hba (by
      have : b = (a ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) m))

def restrictCentralizer {X : Type*} [Group X] {u : X} (φ : MulAut X) (hφ : φ u = u) :
    ↥(Subgroup.centralizer ({u} : Set X)) ≃* ↥(Subgroup.centralizer ({u} : Set X)) where
  toFun m := ⟨φ (m : X), by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = u := hy
    have h := (Subgroup.mem_centralizer_iff.1 m.2) u (Set.mem_singleton u)
    rw [hy']
    calc u * φ (m : X) = φ u * φ (m : X) := by rw [hφ]
      _ = φ (u * (m : X)) := (map_mul φ u (m : X)).symm
      _ = φ ((m : X) * u) := by rw [h]
      _ = φ (m : X) * φ u := map_mul φ (m : X) u
      _ = φ (m : X) * u := by rw [hφ]⟩
  invFun m := ⟨φ.symm (m : X), by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = u := hy
    have h := (Subgroup.mem_centralizer_iff.1 m.2) u (Set.mem_singleton u)
    have hφ' : φ.symm u = u := φ.injective (by rw [φ.apply_symm_apply, hφ])
    rw [hy']
    calc u * φ.symm (m : X) = φ.symm u * φ.symm (m : X) := by rw [hφ']
      _ = φ.symm (u * (m : X)) := (map_mul φ.symm u (m : X)).symm
      _ = φ.symm ((m : X) * u) := by rw [h]
      _ = φ.symm (m : X) * φ.symm u := map_mul φ.symm (m : X) u
      _ = φ.symm (m : X) * u := by rw [hφ']⟩
  left_inv m := Subtype.ext (φ.symm_apply_apply (m : X))
  right_inv m := Subtype.ext (φ.apply_symm_apply (m : X))
  map_mul' m n := Subtype.ext (map_mul φ (m : X) (n : X))

def centralizerCore (p : ℕ) {X : Type*} [Group X] (u : X) : Subgroup X :=
  (pCore p ↥(Subgroup.centralizer ({u} : Set X))).map (Subgroup.centralizer ({u} : Set X)).subtype

theorem centralizerCore_stable (p : ℕ) {X : Type*} [Group X] {u : X} (φ : MulAut X) (hφ : φ u = u) :
    ∀ s ∈ centralizerCore p u, φ s ∈ centralizerCore p u := by
  rintro _ ⟨m, hm, rfl⟩
  have key := pCore_map_iso p (restrictCentralizer φ hφ)
  have hmem : (restrictCentralizer φ hφ) m ∈
      (pCore p ↥(Subgroup.centralizer ({u} : Set X))).map (restrictCentralizer φ hφ).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hm
  rw [key] at hmem
  exact ⟨_, hmem, rfl⟩

theorem isPGroup_centralizerCore (p : ℕ) {X : Type*} [Group X] (u : X) :
    IsPGroup p (centralizerCore p u) :=
  IsPGroup.map (pCore_isPGroup (p := p) (G := ↥(Subgroup.centralizer ({u} : Set X)))) _

theorem exists_mem_centralizerCore_not_commute {X : Type*} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u a : X} (hchar : IsCharacteristicP 2 ↥(Subgroup.centralizer ({u} : Set X)))
    (ha : a ∈ Subgroup.centralizer ({u} : Set X)) (hord : orderOf a = p) :
    ∃ s ∈ centralizerCore 2 u, a * s ≠ s * a := by
  by_contra hcon
  push Not at hcon
  have hmem : (⟨a, ha⟩ : ↥(Subgroup.centralizer ({u} : Set X))) ∈
      Subgroup.centralizer (pCore 2 ↥(Subgroup.centralizer ({u} : Set X)) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subtype.ext (hcon t ⟨t, ht, rfl⟩).symm
  have hin := hchar hmem
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := ↥(Subgroup.centralizer ({u} : Set X)))) ⟨_, hin⟩
  have hk' : a ^ (2 ^ k) = 1 := by
    have := congrArg (fun z => ((z : ↥(pCore 2 ↥(Subgroup.centralizer ({u} : Set X)))) :
      ↥(Subgroup.centralizer ({u} : Set X))).1) hk
    simpa using this
  have hdvd : p ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hk'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))

@[expose] def CharTwoCent (X : Type*) [Group X] : Prop :=
  ∀ u : X, orderOf u = 2 → IsCharacteristicP 2 ↥(Subgroup.centralizer ({u} : Set X))

theorem goodResV_of_charTwoCent {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : Subgroup.center X = ⊥) (hO : OutPChain p X) (hC : CharTwoCent X) :
    GoodResV p X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro Ē hE hEc hR
  obtain ⟨C, hCĒ, hCc, Kb, -, -, -, ⟨V, hVK, hVel, hVc⟩, hfix⟩ := hR
  obtain ⟨c, hcC, hc1, hcInn⟩ := exists_inner_ne_one_of_plane hp hO hE hCĒ hCc
  obtain ⟨a, rfl⟩ := hcInn
  have hcinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := DFunLike.congr_fun hg z
      rw [MulAut.conj_apply, MulAut.one_apply] at h1
      calc z * g = g * z * g⁻¹ * g * 1 := by rw [h1]; group
        _ = g * z := by group
    rw [hZ, Subgroup.mem_bot] at hgc
    exact hgc
  have hcp : (MulAut.conj a) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (A := Ē) _ (hCĒ hcC)
  have hap : a ^ p = 1 := by
    apply hcinj
    rw [map_pow, map_one]
    exact hcp
  have ha1 : a ≠ 1 := fun h => hc1 (by rw [h, map_one])
  have haord : orderOf a = p := orderOf_eq_prime hap ha1
  have hVne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hVc
    omega
  obtain ⟨u, huV, hu1⟩ : ∃ u ∈ V, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hVne (Subgroup.eq_bot_iff_forall _ |>.2 hcon)
  have hu2 : orderOf u = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime _ hu1
    exact elemPow_eq_one_of_isElementaryAbelian (A := V) u huV
  have hfixu : ∀ φ ∈ C, φ u = u := fun φ hφ => hfix φ hφ u (hVK huV)
  have hau : a ∈ Subgroup.centralizer ({u} : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = u := hy
    have h1 := hfixu _ hcC
    rw [MulAut.conj_apply] at h1
    rw [hy']
    calc u * a = a * u * a⁻¹ * a := by rw [h1]
      _ = a * u := by group
  obtain ⟨s, hs, hmove⟩ := exists_mem_centralizerCore_not_commute hp hp2 (hC u hu2) hau haord
  refine Or.inr ⟨C, hCĒ, hCc, centralizerCore 2 u, isPGroup_centralizerCore 2 u,
    fun φ hφ t ht => centralizerCore_stable 2 φ (hfixu φ hφ) t ht, MulAut.conj a, hcC, s, hs, ?_⟩
  rw [MulAut.conj_apply]
  intro h
  apply hmove
  calc a * s = a * s * a⁻¹ * a := by group
    _ = s * a := by rw [h]

end CFSG.RankThree.PartOne.K133X
