module

public import CFSG.Sporadic.Th.Recog.MFactsB.Letters
public import CFSG.Sporadic.Th.Recog.AltNine

public section

namespace CFSG.Sporadic.Th.Recog.MFactsB

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Recognition.PresentedWords
open Equiv Equiv.Perm

section Basic


@[expose] noncomputable def CQt : Subgroup ↥Max3.M :=
  Max3.Q.subgroupOf Max3.M ⊓ Subgroup.centralizer ({tLetter} : Set ↥Max3.M)

@[expose] noncomputable def pre (a : Fin 18) : ↥Max3.M :=
  ω₁ ^ (a.val / 6) * ω₂ ^ (a.val / 2 % 3) * dM ^ (a.val % 2)

@[expose] noncomputable def D₀ : Subgroup ↥Max3.M :=
  CQt ⊔ Subgroup.zpowers ω₁ ⊔ Subgroup.zpowers ω₂ ⊔ Subgroup.zpowers dM

private def pD : Perm (Fin 9) := swap 0 4 * swap 1 7 * swap 2 8 * swap 3 5

private def pE : Perm (Fin 9) := swap 0 2 * swap 1 8 * swap 3 6 * swap 4 7

private def pU : Perm (Fin 9) := swap 0 8 * swap 1 2

private def pT : Perm (Fin 9) := swap 0 7 * swap 0 8 * (swap 1 2 * swap 1 4)

private def pW1 : Perm (Fin 9) := pD * pE

private def pW2 : Perm (Fin 9) := pU * pW1 * pU⁻¹

private def permPre (a : Fin 18) : Perm (Fin 9) :=
  pW1 ^ (a.val / 6) * pW2 ^ (a.val / 2 % 3) * pD ^ (a.val % 2)

private def permOf (p : Fin 3 × Fin 18) : Perm (Fin 9) :=
  pT ^ p.1.val * permPre p.2

private def tab (p : Fin 3 × Fin 18) : Fin 9 × Fin 9 × Fin 9 :=
  (permOf p 0, permOf p 1, permOf p 3)

private theorem coe_kap_pre (a : Fin 18) :
    (Max3.InvRep.kap (pre a) : Perm (Fin 9)) = permPre a := by
  rw [pre, permPre, map_mul, map_mul, map_pow, map_pow, map_pow,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
    Subgroup.coe_pow, coe_kap_ω₁, coe_kap_ω₂, coe_kap_dM]
  rfl

private theorem coe_kap_t_pow_pre (k : Fin 3) (a : Fin 18) :
    (Max3.InvRep.kap (tLetter ^ k.val * pre a) : Perm (Fin 9)) = permOf (k, a) := by
  rw [permOf, map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, coe_kap_tLetter,
    coe_kap_pre]
  rfl

private theorem tab_injective : Function.Injective tab := by
  decide +kernel

private theorem pre_comm_tLetter (a : Fin 18) : pre a * tLetter = tLetter * pre a := by
  have h1 : Commute (ω₁ ^ (a.val / 6)) tLetter :=
    @Commute.pow_left ↥Max3.M (inferInstance : Monoid ↥Max3.M) ω₁ tLetter
      ω₁_comm_tLetter _
  have h2 : Commute (ω₂ ^ (a.val / 2 % 3)) tLetter :=
    @Commute.pow_left ↥Max3.M (inferInstance : Monoid ↥Max3.M) ω₂ tLetter
      ω₂_comm_tLetter _
  have h3 : Commute (dM ^ (a.val % 2)) tLetter :=
    @Commute.pow_left ↥Max3.M (inferInstance : Monoid ↥Max3.M) dM tLetter
      dM_comm_tLetter _
  have h12 : Commute (ω₁ ^ (a.val / 6) * ω₂ ^ (a.val / 2 % 3)) tLetter :=
    Commute.mul_left (a := ω₁ ^ (a.val / 6)) (b := ω₂ ^ (a.val / 2 % 3))
      (c := tLetter) h1 h2
  have h : Commute ((ω₁ ^ (a.val / 6) * ω₂ ^ (a.val / 2 % 3)) *
      dM ^ (a.val % 2)) tLetter :=
    Commute.mul_left (a := ω₁ ^ (a.val / 6) * ω₂ ^ (a.val / 2 % 3))
      (b := dM ^ (a.val % 2)) (c := tLetter) h12 h3
  simpa only [pre] using h.eq

private theorem t_pow_pre_comm (k : Fin 3) (a : Fin 18) :
    (tLetter ^ k.val * pre a) * tLetter = tLetter * (tLetter ^ k.val * pre a) := by
  have ht : Commute (tLetter ^ k.val) tLetter :=
    @Commute.pow_left ↥Max3.M (inferInstance : Monoid ↥Max3.M) tLetter tLetter
      (Commute.refl (a := tLetter)) k.val
  have hp : Commute (pre a) tLetter := pre_comm_tLetter a
  have h : Commute (tLetter ^ k.val * pre a) tLetter :=
    Commute.mul_left (a := tLetter ^ k.val) (b := pre a) (c := tLetter) ht hp
  exact h.eq

private noncomputable abbrev C : Subgroup (alternatingGroup (Fin 9)) :=
  Subgroup.centralizer ({Max3.InvRep.kap tLetter} : Set (alternatingGroup (Fin 9)))

private noncomputable def f (p : Fin 3 × Fin 18) : ↥C :=
  ⟨Max3.InvRep.kap (tLetter ^ p.1.val * pre p.2), by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg Max3.InvRep.kap (t_pow_pre_comm p.1 p.2)
    simpa only [map_mul] using h⟩

private theorem f_injective : Function.Injective f := by
  intro p q hpq
  apply tab_injective
  have hv : (Max3.InvRep.kap (tLetter ^ p.1.val * pre p.2) : Perm (Fin 9)) =
      (Max3.InvRep.kap (tLetter ^ q.1.val * pre q.2) : Perm (Fin 9)) :=
    congrArg (fun z : ↥C => ((z : alternatingGroup (Fin 9)) : Perm (Fin 9))) hpq
  rw [coe_kap_t_pow_pre p.1 p.2, coe_kap_t_pow_pre q.1 q.2] at hv
  have htab : tab p = tab q := by
    simp only [tab]
    rw [hv]
  exact htab

theorem exists_kap_eq {σ : alternatingGroup (Fin 9)}
    (hσ : σ * Max3.InvRep.kap tLetter = Max3.InvRep.kap tLetter * σ) :
    ∃ (k : Fin 3) (a : Fin 18), Max3.InvRep.kap (tLetter ^ k.val * pre a) = σ := by
  have hcardC : Nat.card ↥C = 54 :=
    card_centralizer_of_cycleType_three_three cycleType_kap_tLetter
  have hcardDom : Nat.card (Fin 3 × Fin 18) = 54 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr
      ⟨f_injective, by rw [hcardDom, hcardC]⟩
  let σ' : ↥C := ⟨σ, Subgroup.mem_centralizer_singleton_iff.mpr hσ⟩
  obtain ⟨p, hp⟩ := hbij.surjective σ'
  refine ⟨p.1, p.2, ?_⟩
  have h := congrArg (fun z : ↥C => (z : alternatingGroup (Fin 9))) hp
  change ((f p : ↥C) : alternatingGroup (Fin 9)) = σ at h
  simpa [f] using h


theorem exists_rT_mul {m : ↥Max3.M} (hm : m * tLetter = tLetter * m) :
    ∃ (k : Fin 3) (a : Fin 18) (q : ↥Max3.M), q ∈ CQt ∧
      m = tLetter ^ k.val * pre a * q := by
  have hσ : Max3.InvRep.kap m * Max3.InvRep.kap tLetter =
      Max3.InvRep.kap tLetter * Max3.InvRep.kap m := by
    rw [← map_mul, ← map_mul, hm]
  obtain ⟨k, a, hka⟩ := exists_kap_eq hσ
  let q : ↥Max3.M := (tLetter ^ k.val * pre a)⁻¹ * m
  have hκq : Max3.InvRep.kap q = 1 := by
    dsimp only [q]
    rw [map_mul, map_inv, hka]
    group
  have hqQ : (q : J) ∈ Max3.Q := Max3.InvRep.kap_eq_one_iff.mp hκq
  have hqcomm : q * tLetter = tLetter * q := by
    dsimp only [q]
    have h1 : Commute ((tLetter ^ k.val * pre a)⁻¹) tLetter :=
      Commute.inv_left (a := tLetter ^ k.val * pre a) (b := tLetter)
        (t_pow_pre_comm k a)
    exact (Commute.mul_left (a := (tLetter ^ k.val * pre a)⁻¹) (b := m)
      (c := tLetter) h1 hm).eq
  refine ⟨k, a, q, ?_, ?_⟩
  · rw [CQt, Subgroup.mem_inf]
    exact ⟨Subgroup.mem_subgroupOf.mpr hqQ,
      Subgroup.mem_centralizer_singleton_iff.mpr hqcomm⟩
  · dsimp only [q]
    group

theorem D₀_le_centralizer :
    D₀ ≤ Subgroup.centralizer ({tLetter} : Set ↥Max3.M) := by
  rw [D₀]
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · intro q hq
    exact hq.2
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr ω₁_comm_tLetter
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr ω₂_comm_tLetter
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr dM_comm_tLetter

private def tau : Perm (Fin 9) := swap 0 1 * swap 2 8 * swap 4 7

private noncomputable def Dtau : Subgroup ↥Max3.M :=
  (Subgroup.centralizer ({tau} : Set (Perm (Fin 9)))).comap
    ((alternatingGroup (Fin 9)).subtype.comp Max3.InvRep.kap)

private theorem CQt_le_Dtau : CQt ≤ Dtau := by
  intro q hq
  rw [Dtau, Subgroup.mem_comap]
  have hqQ : (q : J) ∈ Max3.Q := Subgroup.mem_subgroupOf.mp hq.1
  have hκ : Max3.InvRep.kap q = 1 := Max3.InvRep.kap_eq_one_iff.mpr hqQ
  rw [MonoidHom.comp_apply, hκ, map_one]
  exact Subgroup.mem_centralizer_singleton_iff.mpr (by group)

private theorem zpowers_le_Dtau {x : ↥Max3.M} {σ : Perm (Fin 9)}
    (hx : (Max3.InvRep.kap x : Perm (Fin 9)) = σ) (hσ : σ * tau = tau * σ) :
    Subgroup.zpowers x ≤ Dtau := by
  rw [Subgroup.zpowers_le, Dtau, Subgroup.mem_comap, MonoidHom.comp_apply,
    Subgroup.mem_centralizer_singleton_iff]
  change ((Max3.InvRep.kap x : alternatingGroup (Fin 9)) : Perm (Fin 9)) * tau =
    tau * ((Max3.InvRep.kap x : alternatingGroup (Fin 9)) : Perm (Fin 9))
  rw [hx]
  exact hσ

private theorem CQt_sup_gens_le_Dtau :
    CQt ⊔ Subgroup.zpowers ω₁ ⊔ Subgroup.zpowers ω₂ ⊔ Subgroup.zpowers dM ≤ Dtau := by
  refine sup_le (sup_le (sup_le CQt_le_Dtau ?_) ?_) ?_
  · exact zpowers_le_Dtau coe_kap_ω₁ (by decide +kernel)
  · exact zpowers_le_Dtau coe_kap_ω₂ (by decide +kernel)
  · exact zpowers_le_Dtau coe_kap_dM (by decide +kernel)

private theorem D₀_le_Dtau : D₀ ≤ Dtau := by
  rw [D₀]
  exact CQt_sup_gens_le_Dtau

theorem tLetter_not_mem_D₀ : tLetter ∉ D₀ := by
  intro h
  have hτ : tLetter ∈ Dtau := D₀_le_Dtau h
  rw [Dtau, Subgroup.mem_comap, MonoidHom.comp_apply,
    Subgroup.mem_centralizer_singleton_iff] at hτ
  change ((Max3.InvRep.kap tLetter : alternatingGroup (Fin 9)) : Perm (Fin 9)) * tau =
    tau * ((Max3.InvRep.kap tLetter : alternatingGroup (Fin 9)) : Perm (Fin 9)) at hτ
  rw [coe_kap_tLetter] at hτ
  have hne : ((swap 0 7 * swap 0 8 * (swap 1 2 * swap 1 4)) : Perm (Fin 9)) * tau ≠
      tau * (swap 0 7 * swap 0 8 * (swap 1 2 * swap 1 4)) := by
    decide +kernel
  exact hne hτ

theorem D₀_inf_zpowers : D₀ ⊓ Subgroup.zpowers tLetter = ⊥ := by
  set I : Subgroup ↥Max3.M := D₀ ⊓ Subgroup.zpowers tLetter with hI
  have hcardT : Nat.card ↥(Subgroup.zpowers tLetter) = 3 := by
    rw [Nat.card_zpowers, orderOf_tLetter]
  have hIle : I ≤ Subgroup.zpowers tLetter := inf_le_right
  have hdvd : Nat.card ↥I ∣ 3 := by
    rw [← hcardT]
    exact Subgroup.card_dvd_of_le hIle
  have hIcard : Nat.card ↥I = 1 ∨ Nat.card ↥I = 3 :=
    (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd
  rcases hIcard with h1 | h3
  · rw [Subgroup.card_eq_one] at h1
    simpa using h1
  · exfalso
    have hIeq : I = Subgroup.zpowers tLetter := by
      refine Subgroup.eq_of_le_of_card_ge hIle ?_
      rw [h3, hcardT]
    have ht : tLetter ∈ I := by
      rw [hIeq]
      exact Subgroup.mem_zpowers tLetter
    exact tLetter_not_mem_D₀ (Subgroup.mem_inf.mp ht).1

private theorem CQt_le_D₀ : CQt ≤ D₀ := by
  intro q hq
  rw [D₀]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left hq))

private theorem ω₁_pow_mem_D₀ (n : ℕ) : ω₁ ^ n ∈ D₀ := by
  rw [D₀]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers ω₁) n)))

private theorem ω₂_pow_mem_D₀ (n : ℕ) : ω₂ ^ n ∈ D₀ := by
  rw [D₀]
  exact Subgroup.mem_sup_left
    (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers ω₂) n))

private theorem dM_pow_mem_D₀ (n : ℕ) : dM ^ n ∈ D₀ := by
  rw [D₀]
  exact Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers dM) n)

private theorem pre_mem_D₀ (a : Fin 18) : pre a ∈ D₀ := by
  rw [pre]
  exact mul_mem (mul_mem (ω₁_pow_mem_D₀ _) (ω₂_pow_mem_D₀ _))
    (dM_pow_mem_D₀ _)

theorem D₀_sup_zpowers :
    D₀ ⊔ Subgroup.zpowers tLetter = Subgroup.centralizer ({tLetter} : Set ↥Max3.M) := by
  refine le_antisymm ?_ ?_
  · refine sup_le D₀_le_centralizer ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by group)
  · intro m hm
    have hmc : m * tLetter = tLetter * m :=
      (Subgroup.mem_centralizer_iff.mp hm tLetter (Set.mem_singleton tLetter)).symm
    obtain ⟨k, a, q, hq, rfl⟩ := exists_rT_mul hmc
    exact mul_mem (mul_mem
      (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers tLetter) k.val))
      (Subgroup.mem_sup_left (pre_mem_D₀ a)))
      (Subgroup.mem_sup_left (CQt_le_D₀ hq))

theorem exists_complement_t : ∃ D₀ : Subgroup ↥Max3.M, D₀ ⊓ Subgroup.zpowers tLetter = ⊥ ∧
    D₀ ⊔ Subgroup.zpowers tLetter = Subgroup.centralizer {tLetter} :=
  ⟨D₀, D₀_inf_zpowers, D₀_sup_zpowers⟩


end Basic

end CFSG.Sporadic.Th.Recog.MFactsB
