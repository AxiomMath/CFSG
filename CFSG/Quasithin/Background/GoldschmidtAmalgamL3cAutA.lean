module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cAutSub
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TSubC
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cAutSq
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cAutY

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section AutA

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.not_mem_QA_of_psi {q₀ : ↥(pCoreOf 2 B)} (h₀ : psi g q₀ = (zel z, zel z)) :
    (q₀ : D) ∉ pCoreOf 2 A := by
  intro hQ
  have hqa := g.comm_a_of_fst_z (q := q₀) (by rw [h₀])
  have hc : a * (q₀ : D) = (q₀ : D) * a := g.V_comm_QA g.a_mem hQ
  have : a * (q₀ : D) * a⁻¹ * (q₀ : D)⁻¹ = 1 := by rw [hc]; group
  rw [this] at hqa
  exact g.hyp.natural.z_ne hqa.symm

end AutA

section AutA2

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂) {A' B' : Subgroup D}
  (s : SubAm A B A' B')

include g s

theorem SubAm.hKU (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 128) {y : D}
    (hyA' : y ∈ A') (hy3 : orderOf y = 3) :
    ∀ q ∈ pCoreOf 2 A, q ∈ conjSub y (conjClosure V B) →
      (∀ u ∈ conjClosure V B, u * q = q * u) → q ∈ V := by
  intro q hqQ hqy hqc
  have hUA' : conjClosure V B ≤ A' := (s.U_le_T' g hyA' hy3).trans inf_le_left
  have hqA' : q ∈ A' := by
    have hq1 : y⁻¹ * q * y ∈ conjClosure V B := mem_conjSub.mp hqy
    have e : q = y * (y⁻¹ * q * y) * y⁻¹ := by group
    rw [e]
    exact A'.mul_mem (A'.mul_mem hyA' (hUA' hq1)) (A'.inv_mem hyA')
  have hqK := g.hyp.mem_coreIn_of_comm hqQ hqc
  rw [← g.hyp.pCoreOf_inf_centralizer_eq_coreIn] at hqK
  have hqB : q ∈ B := pCoreOf_le 2 B hqK.1
  have hqT' : q ∈ A' ⊓ B' := by rw [← s.inf_B_eq g]; exact ⟨hqA', hqB⟩
  have hqN : q ∈ pCoreOf 2 B' := by
    rw [pCoreOf_eq_inf_of_relIndex_two s.le₂ s.idx₂]; exact ⟨hqT'.2, hqK.1⟩
  have hd := s.nData g hU hT
  have hqU : q ∈ conjClosure V B := (hd.inf_centralizer_eq g hU).le ⟨hqN, hqK.2⟩
  have hyA : y ∈ A := s.le₁ hyA'
  exact g.hyp.inf_conjSub_conjClosure_le hU hyA hy3 ⟨hqU, hqy⟩

theorem SubAm.exists_A'' (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 128) :
    ∃ A'' : Subgroup D, A'' ≤ A' ∧ A''.relIndex A' = 2 ∧ Vertex A'' (A'' ⊓ B') ∧
      Nonempty (↥(pCoreOf 2 A'') ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
      (∃ q ∈ pCoreOf 2 A', ∃ q' ∈ pCoreOf 2 A', q * q' ≠ q' * q) := by
  obtain ⟨y, hyA, hy3⟩ := g.hyp.gold.vertex_left.exists_order_three
  have hy3' : y * y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3, pow_three'] at this
  have hyA' : y ∈ A' := mem_of_cube_of_relIndex_two s.idx₁ hyA hy3'
  obtain ⟨Y, hYQ, hVY, hYc, hYn, hYe, hYle, hnc⟩ :=
    g.exists_Y' hU hyA hy3 (s.hKU g hU hT hyA' hy3)
  have hd := s.nData g hU hT
  obtain ⟨q₀, hq₀N, h₀, hinv⟩ := hd.exists_q₀_invol g hU
  have hUA' : conjClosure V B ≤ A' := (s.U_le_T' g hyA' hy3).trans inf_le_left
  have ha₁A' : a₁ ∈ A' := hUA' g.a₁_mem_U
  have hQ' : pCoreOf 2 A' = A' ⊓ pCoreOf 2 A := pCoreOf_eq_inf_of_relIndex_two s.le₁ s.idx₁
  have hYA' : Y ≤ A' := hYle A' ha₁A' hyA'
  have hYN : Y ≤ pCoreOf 2 A' := by rw [hQ']; exact le_inf hYA' hYQ
  have hq₀B' : (q₀ : D) ∈ B' := pCoreOf_le 2 B' hq₀N
  have hq₀A : (q₀ : D) ∈ A := (g.hyp.gold.pCoreOf_right_le q₀.2).1
  have hq₀T' : (q₀ : D) ∈ A' ⊓ B' := by rw [← s.inf_A_eq g]; exact ⟨hq₀B', hq₀A⟩
  have hq₀1 : (q₀ : D) ≠ 1 := fun h => g.not_mem_QA_of_psi h₀ (h ▸ (pCoreOf 2 A).one_mem)
  have hWcases : ∀ w ∈ Subgroup.zpowers (q₀ : D), w = 1 ∨ w = q₀ := fun w hw => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact zpow_eq_one_or_self (by rw [pow_two]; exact hinv) k
  have hWQ : Subgroup.zpowers (q₀ : D) ⊓ pCoreOf 2 A' = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw, hwQ⟩
    rcases hWcases w hw with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd (by rw [hQ'] at hwQ; exact hwQ.2) (g.not_mem_QA_of_psi h₀)
  have hWY : Subgroup.zpowers (q₀ : D) ⊓ Y = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf_left _ hYN) hWQ.le)
  have dd : SubData A' (A' ⊓ B') Y (Subgroup.zpowers (q₀ : D)) y :=
    { vertex := s.v₁
      N_le := hYN
      N_norm := fun h hh => hYn (s.le₁ hh)
      card_Q := by rw [s.card_pCoreOf_A' g hT, hYc]
      W_le := Subgroup.zpowers_le.mpr hq₀T'
      W_inf_Q := hWQ.le.trans bot_le
      card_W := by
        rw [hWY, Subgroup.card_bot, Nat.card_zpowers]
        have : orderOf (q₀ : D) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hinv) hq₀1
        rw [this]
      w_mem := hyA'
      w_order := hy3
      centralizer_le := by
        rintro w ⟨hwA', hwC⟩
        rw [hQ']
        refine ⟨hwA', ?_⟩
        have : w ∈ A ⊓ Subgroup.centralizer (V : Set D) :=
          ⟨s.le₁ hwA', Subgroup.centralizer_le (fun v hv => hVY hv) hwC⟩
        rw [g.hyp.natural.centralizer_eq] at this
        exact this }
  refine ⟨(Y ⊔ Subgroup.zpowers y) ⊔ Subgroup.zpowers (q₀ : D), dd.H'_le_H, dd.relIndex_H',
    ?_, ?_, ?_⟩
  · have h : ((Y ⊔ Subgroup.zpowers y) ⊔ Subgroup.zpowers (q₀ : D)) ⊓ B' =
        Y ⊔ Subgroup.zpowers (q₀ : D) := by
      rw [← dd.H'_inf_T]
      ext w
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, dd.H'_le_H h1, h2⟩
      · rintro ⟨h1, -, h3⟩
        exact ⟨h1, h3⟩
    rw [h]
    exact dd.vertex_H'
  · obtain ⟨e'⟩ := hYe
    exact ⟨(MulEquiv.subgroupCongr dd.pCoreOf_H').trans e'⟩
  · have he₁A' : y * a₁ * y⁻¹ ∈ A' := A'.mul_mem (A'.mul_mem hyA' ha₁A') (A'.inv_mem hyA')
    have ha₁Q : a₁ ∈ pCoreOf 2 A := g.hyp.conjClosure_le_pCoreOf_left g.a₁_mem_U
    have he₁Q : y * a₁ * y⁻¹ ∈ pCoreOf 2 A := conj_mem_pCoreOf_left (s.le₁ hyA') ha₁Q
    refine ⟨a₁, ?_, y * a₁ * y⁻¹, ?_, hnc⟩
    · rw [hQ']; exact ⟨ha₁A', ha₁Q⟩
    · rw [hQ']; exact ⟨he₁A', he₁Q⟩

end AutA2

end GoldAmL3c

end F6

end CFSG.Quasithin
