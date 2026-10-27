module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cSub2A
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section Coh4

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.centralizer_U_le_QB :
    B ⊓ Subgroup.centralizer (conjClosure V B : Set D) ≤ pCoreOf 2 B := by
  have hCB : B ⊓ Subgroup.centralizer (conjClosure V B : Set D) ≤ B := inf_le_left
  have hBC : B ≤ Subgroup.normalizer
      ((B ⊓ Subgroup.centralizer (conjClosure V B : Set D) : Subgroup D) : Set D) := by
    refine le_normalizer_of_conj_mem fun b hb c hc =>
      ⟨B.mul_mem (B.mul_mem hb hc.1) (B.inv_mem hb), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have hu' : b⁻¹ * u * b ∈ conjClosure V B := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B (B.inv_mem hb)) u).mp
        hu
      simpa using this
    have hc' := Subgroup.mem_centralizer_iff.mp hc.2 _ hu'
    calc u * (b * c * b⁻¹) = b * ((b⁻¹ * u * b) * c) * b⁻¹ := by group
      _ = b * (c * (b⁻¹ * u * b)) * b⁻¹ := by rw [hc']
      _ = (b * c * b⁻¹) * u := by group
  have hCK : B ⊓ Subgroup.centralizer (conjClosure V B : Set D) ≤
      centralizerMod (Subgroup.zpowers z) B V := by
    intro c hc
    have hzc : z * c = c * z := Subgroup.mem_centralizer_iff.mp hc.2 z g.z_mem_U
    refine ⟨hc.1, ?_, fun v hv => ?_⟩
    · refine (Subgroup.centralizer_le_normalizer _) ?_
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact ((show Commute z c from hzc).zpow_left k).eq
    · have hvc : c * v = v * c :=
        (Subgroup.mem_centralizer_iff.mp hc.2 v (le_conjClosure V B hv)).symm
      have e : c * v * c⁻¹ * v⁻¹ = 1 := by rw [hvc]; group
      rw [e]
      exact Subgroup.one_mem _
  exact (le_coreIn hCB hBC hCK).trans (ker_le_pCoreOf g.hyp.gold g.hyp.natural)

omit [Finite D] in
theorem Gen3.orderOf_x : orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (by rw [pow_three']; exact g.x_cube) ?_
  intro h1
  exact g.x_not (h1 ▸ (A ⊓ B).one_mem)

end Coh4

section Coh5

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂) {T' : Subgroup D}
  (c : AutCoh A B T')

include g c

theorem AutCoh.subAm (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 128) :
    ∃ A' B' : Subgroup D, SubAm A B A' B' := by
  obtain ⟨y, hyA, hy3⟩ := g.hyp.gold.vertex_left.exists_order_three
  obtain ⟨hUA, hUB⟩ := c.U_le g hU hyA hy3
  have hVNA := c.V_le_NA g hyA hy3
  have hinf := c.card_inf g hT
  have hinf' : Nat.card ↥((T' ⊓ pCoreOf 2 B) ⊓ (T' ⊓ pCoreOf 2 A)) = 16 := by
    rw [inf_comm]; exact hinf
  have dA : SubData A (A ⊓ B) (T' ⊓ pCoreOf 2 A) (T' ⊓ pCoreOf 2 B) y :=
    { vertex := g.hyp.gold.vertex_left
      N_le := inf_le_right
      N_norm := c.norm₁
      card_Q := by rw [g.card_QA' hT, c.card_NA g hT]
      W_le := inf_le_left.trans c.le
      W_inf_Q := fun w hw => ⟨hw.1.1, hw.2⟩
      card_W := by rw [hinf', c.card_NB g hT]
      w_mem := hyA
      w_order := hy3
      centralizer_le := by
        rintro w ⟨hwA, hwC⟩
        have : w ∈ A ⊓ Subgroup.centralizer (V : Set D) :=
          ⟨hwA, Subgroup.centralizer_le (fun v hv => hVNA hv) hwC⟩
        rw [g.hyp.natural.centralizer_eq] at this
        exact this }
  have dB : SubData B (A ⊓ B) (T' ⊓ pCoreOf 2 B) (T' ⊓ pCoreOf 2 A) x :=
    { vertex := g.hyp.gold.vertex_right
      N_le := inf_le_right
      N_norm := c.norm₂
      card_Q := by rw [g.card_QB' hT, c.card_NB g hT]
      W_le := inf_le_left.trans c.le
      W_inf_Q := fun w hw => ⟨hw.1.1, hw.2⟩
      card_W := by rw [hinf, c.card_NA g hT]
      w_mem := g.x_mem
      w_order := g.orderOf_x
      centralizer_le := fun w hw =>
        g.centralizer_U_le_QB ⟨hw.1, Subgroup.centralizer_le (fun u hu => hUB hu) hw.2⟩ }
  refine ⟨((T' ⊓ pCoreOf 2 A) ⊔ Subgroup.zpowers y) ⊔ (T' ⊓ pCoreOf 2 B),
    ((T' ⊓ pCoreOf 2 B) ⊔ Subgroup.zpowers x) ⊔ (T' ⊓ pCoreOf 2 A), ?_⟩
  have hA'T := dA.H'_inf_T
  have hB'T := dB.H'_inf_T
  have hmeet : (((T' ⊓ pCoreOf 2 A) ⊔ Subgroup.zpowers y) ⊔ (T' ⊓ pCoreOf 2 B)) ⊓
      (((T' ⊓ pCoreOf 2 B) ⊔ Subgroup.zpowers x) ⊔ (T' ⊓ pCoreOf 2 A)) =
      (T' ⊓ pCoreOf 2 A) ⊔ (T' ⊓ pCoreOf 2 B) := by
    apply le_antisymm
    · rintro w ⟨hwA', hwB'⟩
      rw [← hA'T]
      exact ⟨hwA', dA.H'_le_H hwA', dB.H'_le_H hwB'⟩
    · refine le_inf dA.T'_le_H' ?_
      rw [sup_comm]
      exact dB.T'_le_H'
  refine ⟨dA.H'_le_H, dB.H'_le_H, dA.relIndex_H', dB.relIndex_H', ?_, ?_⟩
  · rw [hmeet]; exact dA.vertex_H'
  · rw [hmeet, sup_comm (T' ⊓ pCoreOf 2 A) (T' ⊓ pCoreOf 2 B)]
    exact dB.vertex_H'

end Coh5

section Final

variable {A B : Subgroup D} {z : D} {V : Subgroup D} [Finite D]

theorem isGoldCaseAutM12Cat_of_coh
    (h : GoldHyp3 A B z V)
    (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 128) {T' : Subgroup D}
    (c : AutCoh A B T') : IsGoldCaseAutM12Cat B A := by
  obtain ⟨x, a, a₁, a₂, g⟩ := GoldHyp3.exists_gen3 h
  obtain ⟨A', B', s⟩ := c.subAm g hU hT
  exact isGoldCaseAutM12Cat_of_subAm h hU hT s

end Final

end GoldAmL3c

end F6

end CFSG.Quasithin
