module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829B
public import CFSG.Quasithin.Vol2.Ch3E213MKer
public import CFSG.Quasithin.Vol2.Ch8Sec2Steps

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section L828SLem12

variable {G : Type} [Group G] [Finite G] {T L I H : Subgroup G} {h : G} {k : ℕ}

theorem s828_pCore_eq_sup (hE214 : ASInputs.AS_E_2_14)
    (hC : Concl822 T L I H h k) (hk2 : k ≤ 2) :
    pCoreOf 2 (ch82I (fsuV T I) h) = ch82A (fsuV T I) h ⊔ ch82B (fsuV T I) h := by
  obtain ⟨-, hhI, hIC, hZ1, -, -, -, hker, -, hcases, -, -, -, -, -, -, -, -, h28, hchar, hTI⟩ :=
    hC
  have hP := e214P_eq_kerIn_82 hE214 hhI hIC hZ1 h28 hchar hTI hk2 hcases
  rw [hker] at hP
  exact hP.symm

theorem s828_pair (hV : IsElemAbelian 2 (fsuV T I)) (hVT : fsuV T I ≤ T)
    (hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G)) (hC : Concl822 T L I H h k) :
    E2.Pair (ch82I (fsuV T I) h) (T ⊓ ch82I (fsuV T I) h) (fsuM T L ⊓ ch82I (fsuV T I) h)
      (fsuV T I) h := by
  obtain ⟨-, hhI, hIC, -, -, hSyl, hMI, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  have hcl := hIC.2.2.2.1
  rw [inf_inf_eq_82 (M := fsuM T L) hIC.1] at hcl
  exact pair_82 hV hVT hTV hSyl hMI hhI hcl

theorem s828_pCore_eq_pairForm {M : Subgroup G}
    (hP : E2.Pair (ch82I (fsuV T I) h) (T ⊓ ch82I (fsuV T I) h) (M ⊓ ch82I (fsuV T I) h)
      (fsuV T I) h)
    (hPeq : pCoreOf 2 (ch82I (fsuV T I) h) = ch82A (fsuV T I) h ⊔ ch82B (fsuV T I) h) :
    pCoreOf 2 (ch82I (fsuV T I) h) =
      (kerIn (M ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ⊓ fsuV T I) ⊔
        B6.conjSub h (kerIn (M ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ⊓ fsuV T I) := by
  rw [hP.conjSub_kerIn_inf_eq, hP.kerIn_inf_eq]
  exact hPeq.trans (sup_comm _ _)

theorem s828_comm_mod_Z {M : Subgroup G}
    (hP : E2.Pair (ch82I (fsuV T I) h) (T ⊓ ch82I (fsuV T I) h) (M ⊓ ch82I (fsuV T I) h)
      (fsuV T I) h)
    (hPeq : pCoreOf 2 (ch82I (fsuV T I) h) = ch82A (fsuV T I) h ⊔ ch82B (fsuV T I) h)
    {x y : G} (hx : x ∈ pCoreOf 2 (ch82I (fsuV T I) h))
    (hy : y ∈ pCoreOf 2 (ch82I (fsuV T I) h)) :
    (∃ z ∈ ch82ZI (fsuV T I) h, x * y = y * x * z) ∧ x ^ 2 ∈ ch82ZI (fsuV T I) h := by
  have hE := s828_pCore_eq_pairForm hP hPeq
  rw [hE] at hx hy
  obtain ⟨z, hz, hxy⟩ := hP.exists_comm_P hx hy
  obtain ⟨-, hsq⟩ := hP.commutator_sq_mem_Z hx hy
  exact ⟨⟨z, hz, hxy⟩, hsq⟩

theorem s828_commutator_V_le_B {M : Subgroup G}
    (hP : E2.Pair (ch82I (fsuV T I) h) (T ⊓ ch82I (fsuV T I) h) (M ⊓ ch82I (fsuV T I) h)
      (fsuV T I) h)
    (hker : kerIn (M ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) = pCoreOf 2 (ch82I (fsuV T I) h)) :
    ⁅fsuV T I, pCoreOf 2 (ch82I (fsuV T I) h)⁆ ≤ ch82B (fsuV T I) h := by
  rw [Subgroup.commutator_le]
  intro v hv q hq
  have := hP.commutator_mem_B hv hq
  rw [hker, inf_comm] at this
  exact this

theorem s828_mem_B_of_centralizes {M : Subgroup G}
    (hP : E2.Pair (ch82I (fsuV T I) h) (T ⊓ ch82I (fsuV T I) h) (M ⊓ ch82I (fsuV T I) h)
      (fsuV T I) h)
    (hPeq : pCoreOf 2 (ch82I (fsuV T I) h) = ch82A (fsuV T I) h ⊔ ch82B (fsuV T I) h)
    (hker : kerIn (M ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) = pCoreOf 2 (ch82I (fsuV T I) h))
    {x : G} (hx : x ∈ pCoreOf 2 (ch82I (fsuV T I) h))
    (hxv : ∀ v ∈ fsuV T I, v * x * v⁻¹ * x⁻¹ ∈ ch82ZI (fsuV T I) h) :
    x ∈ ch82B (fsuV T I) h := by
  have hE := s828_pCore_eq_pairForm hP hPeq
  rw [hE] at hx
  have := hP.mem_B_of_commutator_mem_Z hx hxv
  rw [hker, inf_comm] at this
  exact this

theorem s828_centralizer_tilde_le_P {M : Subgroup G}
    (hP : E2.Pair (ch82I (fsuV T I) h) (T ⊓ ch82I (fsuV T I) h) (M ⊓ ch82I (fsuV T I) h)
      (fsuV T I) h)
    (hPeq : pCoreOf 2 (ch82I (fsuV T I) h) = ch82A (fsuV T I) h ⊔ ch82B (fsuV T I) h)
    (hZc : ch82ZI (fsuV T I) h ≤ Subgroup.centralizer (ch82I (fsuV T I) h : Set G))
    (hchar : QuasithinUnique.CharTwo (ch82I (fsuV T I) h))
    {d : G} (hd : d ∈ ch82I (fsuV T I) h)
    (hdP : ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h), d * p * d⁻¹ * p⁻¹ ∈ ch82ZI (fsuV T I) h) :
    d ∈ pCoreOf 2 (ch82I (fsuV T I) h) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ih := ch82I (fsuV T I) h with hIh
  set Ph := pCoreOf 2 Ih with hPh
  set Zh := ch82ZI (fsuV T I) h with hZh
  have hE : Ph = (kerIn (M ⊓ Ih) Ih ⊓ fsuV T I) ⊔
      B6.conjSub h (kerIn (M ⊓ Ih) Ih ⊓ fsuV T I) := s828_pCore_eq_pairForm hP hPeq
  have hcen' : ∀ z ∈ Zh, ∀ x ∈ Ih, x * z * x⁻¹ = z := fun z hz x hx => by
    have := (Subgroup.mem_centralizer_iff.mp (hZc hz)) x hx
    rw [this]
    group
  let C : Subgroup G :=
    { carrier := {c | c ∈ Ih ∧ ∀ p ∈ Ph, c * p * c⁻¹ * p⁻¹ ∈ Zh}
      one_mem' := ⟨Ih.one_mem, fun p _ => by simp [Zh.one_mem]⟩
      mul_mem' := by
        rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
        refine ⟨Ih.mul_mem ha hb, fun p hp => ?_⟩
        have e : a * b * p * (a * b)⁻¹ * p⁻¹ =
            (a * (b * p * b⁻¹ * p⁻¹) * a⁻¹) * (a * p * a⁻¹ * p⁻¹) := by group
        rw [e, hcen' _ (hbp p hp) a ha]
        exact Zh.mul_mem (hbp p hp) (hap p hp)
      inv_mem' := by
        rintro a ⟨ha, hap⟩
        refine ⟨Ih.inv_mem ha, fun p hp => ?_⟩
        have hz := hap p hp
        have e2 : a⁻¹ * p * a⁻¹⁻¹ * p⁻¹ = a⁻¹ * (a * p * a⁻¹ * p⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e2, hcen' _ (Zh.inv_mem hz) a⁻¹ (Ih.inv_mem ha)]
        exact Zh.inv_mem hz }
  have hCmem : ∀ c : G, c ∈ C ↔ c ∈ Ih ∧ ∀ p ∈ Ph, c * p * c⁻¹ * p⁻¹ ∈ Zh := fun c => Iff.rfl
  have hNPh : Ih ≤ Subgroup.normalizer (Ph : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Ih
  have hconj : ∀ i ∈ Ih, ∀ c ∈ C, i * c * i⁻¹ ∈ C := by
    intro i hi c hc
    rw [hCmem] at hc ⊢
    refine ⟨Ih.mul_mem (Ih.mul_mem hi hc.1) (Ih.inv_mem hi), fun p hp => ?_⟩
    have hp' : i⁻¹ * p * i ∈ Ph := by
      have := (Subgroup.mem_normalizer_iff.mp (hNPh (Ih.inv_mem hi)) p).mp hp
      simpa using this
    have e : i * c * i⁻¹ * p * (i * c * i⁻¹)⁻¹ * p⁻¹ =
        i * (c * (i⁻¹ * p * i) * c⁻¹ * (i⁻¹ * p * i)⁻¹) * i⁻¹ := by group
    rw [e, hcen' _ (hc.2 _ hp') i hi]
    exact hc.2 _ hp'
  have hCN : Ih ≤ Subgroup.normalizer (C : Set G) := by
    intro i hi
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact hconj i hi c hc
    · intro hc
      have := hconj i⁻¹ (Ih.inv_mem hi) _ hc
      convert this using 1
      group
  have hCI : C ≤ Ih := fun c hc => hc.1
  have hC2 : IsPGroup 2 ↥C := by
    intro x
    have hxc : (x : G) ∈ C := x.2
    obtain ⟨n, hn⟩ := CFSG.Quasithin.Ch3E213M.isTwo_of_centralizes hP hchar hxc.1 (fun p hp => by
      have hp' : p ∈ Ph := by rw [hE]; exact hp
      exact hxc.2 p hp')
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hdC : d ∈ C := ⟨hd, hdP⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCI hCN hC2 hdC

end L828SLem12

end CFSG.Quasithin.H13
