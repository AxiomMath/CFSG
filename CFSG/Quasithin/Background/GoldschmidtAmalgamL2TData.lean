module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TQY
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Hyp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

open scoped Pointwise

namespace F6

namespace GoldAmL2T

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section Data

variable [Finite D] {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem centralizer_U_le_QB :
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
    have hzc : z * c = c * z := Subgroup.mem_centralizer_iff.mp hc.2 z g.hyp.z_mem_U
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
  exact (le_coreIn hCB hBC hCK).trans (GoldAmL3.ker_le_pCoreOf g.hyp.gold g.hyp.natural)

theorem card_yGrp (hT : Nat.card ↥(A ⊓ B) = 64) : Nat.card ↥(yGrp A B V) = 16 := by
  obtain ⟨y, hyA, hyT⟩ := g.hyp.exists_y
  exact (yGrp_eq_sup g hT hyA hyT).2

omit [Finite D] in
theorem orderOf_x : orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (by rw [pow_three']; exact g.x_cube) ?_
  intro h1
  exact g.x_not (h1 ▸ (A ⊓ B).one_mem)

theorem subDataA (hT : Nat.card ↥(A ⊓ B) = 64) {y : D} (hyA : y ∈ A) (hy3 : orderOf y = 3) :
    SubData A (A ⊓ B) (yGrp A B V) (conjClosure V B) y where
  vertex := g.hyp.gold.vertex_left
  N_le := yGrp_le_QA g
  N_norm := A_le_normalizer_yGrp
  card_Q := by rw [card_QA_of_card_T g hT, card_yGrp g hT]
  W_le := g.hyp.U_le_T
  W_inf_Q := fun u hu => by
    rw [← (card_yGrp_inf_U g hT).2] at hu
    exact hu.1
  card_W := by
    rw [inf_comm, (card_yGrp_inf_U g hT).1, g.card_U]
  w_mem := hyA
  w_order := hy3
  centralizer_le := centralizer_yGrp_le g

theorem subDataB (hT : Nat.card ↥(A ⊓ B) = 64) :
    SubData B (A ⊓ B) (conjClosure V B) (yGrp A B V) x where
  vertex := g.hyp.gold.vertex_right
  N_le := g.hyp.U_le
  N_norm := le_normalizer_conjClosure V B
  card_Q := by rw [card_QB_of_card_T g hT, g.card_U]
  W_le := (yGrp_le_QA g).trans g.hyp.QA_le_T
  W_inf_Q := yGrp_inf_QB_le_U g hT
  card_W := by
    rw [(card_yGrp_inf_U g hT).1, card_yGrp g hT]
  w_mem := g.x_mem
  w_order := orderOf_x g
  centralizer_le := centralizer_U_le_QB g

end Data

end GoldAmL2T

end F6

end CFSG.Quasithin
