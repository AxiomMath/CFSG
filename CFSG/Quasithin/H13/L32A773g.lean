module

public import CFSG.Quasithin.H13.L32A773f

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem comm_mem_sL_of_mem_Q {q l : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hl : l ∈ L) :
    l * q * l⁻¹ * q⁻¹ ∈ sL T L V := by
  have h := (C.l71 G T L V C.hyp).2.2 (Subgroup.commutator_mem_commutator hq hl)
  have := inv_mem h
  rwa [commutatorElement_def, show (q * l * q⁻¹ * l⁻¹)⁻¹ = l * q * l⁻¹ * q⁻¹ by group] at this

theorem sL_le_Q : sL T L V ≤ pCoreOf 2 (L ⊔ T) := C.sL_le_P.trans C.pCoreOf_le_pCoreOf_sup

theorem sq_mem_v_of_mem_Q {p : G} (hpQ : p ∈ pCoreOf 2 (L ⊔ T)) (hpS : p ^ 2 ∈ sL T L V) :
    p ^ 2 ∈ V := by
  refine C.mem_v_of_comm_mem hpS fun l hl => ?_
  obtain ⟨s, hs⟩ : ∃ s, s = l * p * l⁻¹ * p⁻¹ := ⟨_, rfl⟩
  have hsS : s ∈ sL T L V := by rw [hs]; exact C.comm_mem_sL_of_mem_Q hpQ hl
  have hps : p * s * p⁻¹ * s⁻¹ ∈ V := C.comm_mem_v_Q_sL hpQ hsS
  have hs2 : s ^ 2 ∈ V := C.sq_mem C.u0_eq hsS
  have hc : (p * s * p⁻¹ * s⁻¹) * s = s * (p * s * p⁻¹ * s⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (C.v_le_centerOf hps)).2 s hsS).symm
  have e : l * p ^ 2 * l⁻¹ * (p ^ 2)⁻¹ = (p * s * p⁻¹ * s⁻¹) * s ^ 2 := by
    have h1 : l * p * l⁻¹ = s * p := by rw [hs]; group
    calc l * p ^ 2 * l⁻¹ * (p ^ 2)⁻¹ = (l * p * l⁻¹) * (l * p * l⁻¹) * (p ^ 2)⁻¹ := by
          simp only [pow_two]; group
      _ = s * p * (s * p) * (p ^ 2)⁻¹ := by rw [h1]
      _ = s * ((p * s * p⁻¹ * s⁻¹) * s) := by simp only [pow_two]; group
      _ = s * (s * (p * s * p⁻¹ * s⁻¹)) := by rw [hc]
      _ = (p * s * p⁻¹ * s⁻¹) * s ^ 2 := by
          rw [show s * (s * (p * s * p⁻¹ * s⁻¹)) = s ^ 2 * (p * s * p⁻¹ * s⁻¹) by
            simp only [pow_two]; group]
          exact Subgroup.mem_centralizer_iff.mp
            (Subgroup.mem_inf.mp (C.v_le_centerOf hps)).2 _ (pow_mem hsS 2)
  rw [e]
  exact mul_mem hps hs2

theorem mem_sL_of_mem_Q {q : G} (hqQ : q ∈ pCoreOf 2 (L ⊔ T)) (hq2 : q ^ 2 ∈ sL T L V) :
    q ∈ sL T L V := by
  obtain ⟨θ, -, hθs, hθ1, -, -, -, -, -, χ, hχk, hχt, hχs, hχe⟩ :=
    C.exists_st C.u0_eq C.vh65 C.l71
  have hLV := C.L_le_normalizer_V
  have hLS : L ≤ Subgroup.normalizer (sL T L V : Set G) := le_normalizer_conjClosure _ _
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T := by
    rw [← C.hF.cT]
    exact inf_le_left
  have hqN : q ∈ Subgroup.normalizer (sL T L V : Set G) := C.T_le_normalizer_sL (hQT hqQ)
  have hqV : q ∈ Subgroup.centralizer (V : Set G) := C.mem_centralizer_of_mem_Q hqQ
  have hqv2 := C.sq_mem_v_of_mem_Q hqQ hq2
  have hqS : ∀ s ∈ sL T L V, q * s * q⁻¹ ∈ sL T L V := fun s hs =>
    (Subgroup.mem_normalizer_iff.mp hqN s).mp hs
  have hqS' : ∀ s ∈ sL T L V, q⁻¹ * s * q ∈ sL T L V := fun s hs => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hqN) s).mp hs
    simpa using this
  have hvq : ∀ v ∈ V, q * v * q⁻¹ = v := fun v hv => by
    rw [(Subgroup.mem_centralizer_iff.mp hqV v hv).symm, mul_inv_cancel_right]
  let X : Subgroup G :=
    { carrier := {x | x ∈ sL T L V ∨ q⁻¹ * x ∈ sL T L V}
      one_mem' := Or.inl (one_mem _)
      mul_mem' := fun {a b} ha hb => by
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (mul_mem ha hb)
        · right
          rw [show q⁻¹ * (a * b) = (q⁻¹ * a * q) * (q⁻¹ * b) by group]
          exact mul_mem (hqS' a ha) hb
        · right
          rw [show q⁻¹ * (a * b) = (q⁻¹ * a) * b by group]
          exact mul_mem ha hb
        · left
          rw [show a * b = q ^ 2 * (q⁻¹ * (q⁻¹ * a) * q) * (q⁻¹ * b) by
            simp only [pow_two]; group]
          exact mul_mem (mul_mem hq2 (hqS' _ ha)) hb
      inv_mem' := fun {a} ha => by
        rcases ha with ha | ha
        · exact Or.inl (inv_mem ha)
        · right
          rw [show q⁻¹ * a⁻¹ = (q⁻¹ * (q⁻¹ * a)⁻¹ * q) * (q ^ 2)⁻¹ by
            simp only [pow_two]; group]
          exact mul_mem (hqS' _ (inv_mem ha)) (inv_mem hq2) }
  have hmemX : ∀ {x : G}, x ∈ X ↔ x ∈ sL T L V ∨ q⁻¹ * x ∈ sL T L V := Iff.rfl
  have hSX : sL T L V ≤ X := fun s hs => hmemX.mpr (Or.inl hs)
  have hqX : q ∈ X := hmemX.mpr (Or.inr (by rw [inv_mul_cancel]; exact one_mem _))
  have hXQ : X ≤ pCoreOf 2 (L ⊔ T) := fun x hx => by
    rcases hmemX.mp hx with h | h
    · exact C.sL_le_Q h
    · rw [show x = q * (q⁻¹ * x) by group]
      exact mul_mem hqQ (C.sL_le_Q h)
  have hdec : ∀ x ∈ X, ∃ s ∈ sL T L V, s = x ∨ q * s = x := fun x hx => by
    rcases hmemX.mp hx with h | h
    · exact ⟨x, h, Or.inl rfl⟩
    · exact ⟨q⁻¹ * x, h, Or.inr (by group)⟩
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ V := by
    intro a ha b hb
    obtain ⟨s, hs, rfl | rfl⟩ := hdec a ha <;> obtain ⟨t, ht, rfl | rfl⟩ := hdec b hb
    · exact C.comm_mem C.u0_eq hs ht
    · rw [show s * (q * t) * s⁻¹ * (q * t)⁻¹ =
        (s * q * s⁻¹ * q⁻¹) * (q * (s * t * s⁻¹ * t⁻¹) * q⁻¹) by group,
        hvq _ (C.comm_mem C.u0_eq hs ht)]
      refine mul_mem ?_ (C.comm_mem C.u0_eq hs ht)
      have := inv_mem (C.comm_mem_v_Q_sL hqQ hs)
      rwa [show (q * s * q⁻¹ * s⁻¹)⁻¹ = s * q * s⁻¹ * q⁻¹ by group] at this
    · rw [show q * s * t * (q * s)⁻¹ * t⁻¹ =
        (q * (s * t * s⁻¹ * t⁻¹) * q⁻¹) * (q * t * q⁻¹ * t⁻¹) by group,
        hvq _ (C.comm_mem C.u0_eq hs ht)]
      exact mul_mem (C.comm_mem C.u0_eq hs ht) (C.comm_mem_v_Q_sL hqQ ht)
    · have h1 : s * q * s⁻¹ * q⁻¹ ∈ V := by
        have := inv_mem (C.comm_mem_v_Q_sL hqQ hs)
        rwa [show (q * s * q⁻¹ * s⁻¹)⁻¹ = s * q * s⁻¹ * q⁻¹ by group] at this
      rw [show q * s * (q * t) * (q * s)⁻¹ * (q * t)⁻¹ =
        q * ((s * q * s⁻¹ * q⁻¹) * (q * (s * t * s⁻¹ * t⁻¹) * q⁻¹)) * q⁻¹ *
          (q * (q * t * q⁻¹ * t⁻¹) * q⁻¹) by group,
        hvq _ (C.comm_mem C.u0_eq hs ht), hvq _ (C.comm_mem_v_Q_sL hqQ ht),
        hvq _ (mul_mem h1 (C.comm_mem C.u0_eq hs ht))]
      exact mul_mem (mul_mem h1 (C.comm_mem C.u0_eq hs ht)) (C.comm_mem_v_Q_sL hqQ ht)
  have hsq : ∀ a ∈ X, a ^ 2 ∈ V := by
    intro a ha
    obtain ⟨s, hs, rfl | rfl⟩ := hdec a ha
    · exact C.sq_mem C.u0_eq hs
    · have h1 : q⁻¹ * s * q * s⁻¹ ∈ V := by
        have := C.comm_mem_v_Q_sL (inv_mem hqQ) hs
        simpa using this
      rw [show (q * s) ^ 2 = q ^ 2 * ((q⁻¹ * s * q * s⁻¹) * s ^ 2) by
        simp only [pow_two]; group]
      exact mul_mem hqv2 (mul_mem h1 (C.sq_mem C.u0_eq hs))
  have hθS : ∀ l : ↥L, θ l = 1 → (l : G) ∈ sL T L V := fun l hl => by
    rw [← C.pCoreOf_eq_sL, C.pCoreOf_eq]
    exact Subgroup.mem_inf.mpr ⟨l.2, (hθ1 l).mp hl⟩
  have D : SecMod L X V θ :=
    { le := v_le_sL.trans hSX
      normX := le_normalizer_of_conj_mem' fun l hl x hx => by
        obtain ⟨s, hs, rfl | rfl⟩ := hdec x hx
        · exact hSX ((Subgroup.mem_normalizer_iff.mp (hLS hl) s).mp hs)
        · refine hmemX.mpr (Or.inr ?_)
          rw [show q⁻¹ * (l * (q * s) * l⁻¹) =
            (q⁻¹ * (l * q * l⁻¹ * q⁻¹) * q) * (l * s * l⁻¹) by group]
          exact mul_mem (hqS' _ (C.comm_mem_sL_of_mem_Q hqQ hl))
            ((Subgroup.mem_normalizer_iff.mp (hLS hl) s).mp hs)
      normY := hLV
      comm := hcomm
      sq := hsq
      surj := hθs
      ker := fun l hl x hx => hcomm _ (hSX (hθS l hl)) x hx
      faithful := fun l hl => (hθ1 l).mpr
        (C.mem_centralizer_of_comm_mem C.u0_eq l.2 fun s hs => hl s (hSX hs)) }
  obtain ⟨N, -, hNX, hNL, hNS, hgen⟩ := D.exists_compl C.vh63 v_le_sL hSX hLS hχk hχt hχs hχe
  obtain ⟨n, hn, s, hs, rfl⟩ := hgen q hqX
  have hnQ := hXQ (hNX hn)
  have hnV : n ∈ V := C.mem_v_of_mem_Q hnQ fun l hl => by
    rw [← hNS]
    exact Subgroup.mem_inf.mpr ⟨mul_mem ((Subgroup.mem_normalizer_iff.mp (hNL hl) n).mp hn)
      (inv_mem hn), C.comm_mem_sL_of_mem_Q hnQ hl⟩
  exact mul_mem (v_le_sL hnV) hs

theorem pCoreOf_sup_eq_sL : pCoreOf 2 (L ⊔ T) = sL T L V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (fun p hp => ?_) C.sL_le_Q
  by_contra hpS
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)) ⟨p, hp⟩
  have hk' : p ^ 2 ^ k ∈ sL T L V := by
    have : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact one_mem _
  have hex : ∃ m, p ^ 2 ^ m ∈ sL T L V := ⟨k, hk'⟩
  set m := Nat.find hex with hm
  have hmS : p ^ 2 ^ m ∈ sL T L V := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hmS
    exact hpS hmS
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hq2 : (p ^ 2 ^ m') ^ 2 ∈ sL T L V := by
    rw [← pow_mul, ← pow_succ]
    rw [hm'] at hmS
    exact hmS
  exact Nat.find_min hex (show m' < m by omega) (C.mem_sL_of_mem_Q (pow_mem hp _) hq2)

theorem T_le_L : T ≤ L := by
  intro t ht
  obtain ⟨l, hl, q, hq, rfl⟩ := C.exists_mul_of_mem_T ht
  rw [C.pCoreOf_sup_eq_sL] at hq
  exact mul_mem hl (C.sL_le_L C.u0_eq hq)

end Ctx73

end CFSG.Quasithin.H13.L32A
