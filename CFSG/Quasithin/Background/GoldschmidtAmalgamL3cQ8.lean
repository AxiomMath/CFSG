module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cSq
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cHfpf
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cQuat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section Q8

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.a_mem_QB : a ∈ pCoreOf 2 B := g.U_le_QB g.a_mem_U

theorem Gen3.psi_a (hU : Nat.card (conjClosure V B) = 8) : psi g ⟨a, g.a_mem_QB⟩ = 1 :=
  MonoidHom.mem_ker.mp ((g.mem_ker_psi hU _).mpr
    ⟨g.a_mem_QB, Subgroup.mem_centralizer_iff.mpr fun _ hw => g.U_comm hw g.a_mem_U⟩)

theorem Gen3.exists_q₀_invol (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 64) :
    ∃ q : ↥(pCoreOf 2 B), psi g q = (zel z, zel z) ∧ (q : D) * q = 1 := by
  obtain ⟨q₀, h₀⟩ := g.exists_q₀ hU hT
  have hs := g.sq_q₀_mem hU hT h₀
  rcases zpowers_cases g.hyp hs with e | e
  · exact ⟨q₀, h₀, e⟩
  · refine ⟨q₀ * ⟨a, g.a_mem_QB⟩, ?_, ?_⟩
    · rw [map_mul, g.psi_a hU, mul_one, h₀]
    · have hq₀B : (q₀ : D) ∈ B := pCoreOf_le 2 B q₀.2
      have hqa := g.comm_a_of_fst_z (q := q₀) (by rw [h₀])
      have e1 : a * (q₀ : D) = z * q₀ * a := by
        calc a * (q₀ : D) = (a * q₀ * a⁻¹ * (q₀ : D)⁻¹) * q₀ * a := by group
          _ = z * q₀ * a := by rw [hqa]
      have hzq : (q₀ : D) * z = z * (q₀ : D) := g.z_comm hq₀B
      show (q₀ : D) * a * ((q₀ : D) * a) = 1
      calc (q₀ : D) * a * ((q₀ : D) * a) = q₀ * (a * q₀) * a := by group
        _ = q₀ * (z * q₀ * a) * a := by rw [e1]
        _ = (q₀ * z) * q₀ * (a * a) := by group
        _ = (z * q₀) * q₀ * (a * a) := by rw [hzq]
        _ = z * ((q₀ : D) * q₀) * (a * a) := by group
        _ = 1 := by rw [e, g.a_sq, g.z_mul_z]; group

theorem Gen3.exists_p (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 64)
    {q₀ : ↥(pCoreOf 2 B)} (h₀ : psi g q₀ = (zel z, zel z)) (hinv : (q₀ : D) * q₀ = 1) :
    ∃ p : D, p ∈ pCoreOf 2 B ∧ p * p = 1 ∧ a * p = p * a ∧ a₂ * p * a₂⁻¹ * p⁻¹ = z ∧
      (q₀ : D) * p = p * q₀ ∧ (p = (g.xc q₀ : D) ∨ p = (g.xc q₀ : D) * a) := by
  have hzz := g.zel_mul_zel
  have rot := g.psi_xc hU
  have h₁ : psi g (g.xc q₀) = (1, zel z) := by rw [rot, h₀]; simp [hzz]
  have hq₁inv : (g.xc q₀ : D) * (g.xc q₀ : D) = 1 := by
    show x * q₀ * x⁻¹ * (x * q₀ * x⁻¹) = 1
    calc x * (q₀ : D) * x⁻¹ * (x * q₀ * x⁻¹) = x * ((q₀ : D) * q₀) * x⁻¹ := by group
      _ = 1 := by rw [hinv]; group
  have haq₁ : a * (g.xc q₀ : D) = (g.xc q₀ : D) * a := g.comm_a_of_fst_one (by rw [h₁])
  have ha₂q₁ : a₂ * (g.xc q₀ : D) * a₂⁻¹ * (g.xc q₀ : D)⁻¹ = z := by
    have h := g.comm_a₂ hU (g.xc q₀)
    have e : (a * (g.xc q₀ : D) * a⁻¹ * (g.xc q₀ : D)⁻¹) *
        (a₁ * (g.xc q₀ : D) * a₁⁻¹ * (g.xc q₀ : D)⁻¹) = z := by
      change ((psi g (g.xc q₀)).1 : D) * ((psi g (g.xc q₀)).2 : D) = z
      rw [h₁]
      simp [zel]
    rw [h, e]
  have hqa := g.comm_a_of_fst_z (q := q₀) (by rw [h₀])
  have hq₀B : (q₀ : D) ∈ B := pCoreOf_le 2 B q₀.2
  have hq₁B : (g.xc q₀ : D) ∈ B := pCoreOf_le 2 B (g.xc q₀).2
  have hcomm01 := g.comm_q₀_q₁_mem hU hT h₀
  rcases zpowers_cases g.hyp hcomm01 with hd | hd
  · refine ⟨(g.xc q₀ : D), (g.xc q₀).2, hq₁inv, haq₁, ha₂q₁, ?_, Or.inl rfl⟩
    calc (q₀ : D) * (g.xc q₀ : D) = ((q₀ : D) * (g.xc q₀ : D) * (q₀ : D)⁻¹ * (g.xc q₀ : D)⁻¹) *
        ((g.xc q₀ : D) * q₀) := by group
      _ = (g.xc q₀ : D) * q₀ := by rw [hd, one_mul]
  · have haQ := g.a_mem_QB
    have ha₂i : a₂⁻¹ = a₂ := inv_eq_of_mul_eq_one_right g.a₂_sq
    have hzq₁ : (g.xc q₀ : D) * z = z * (g.xc q₀ : D) := g.z_comm hq₁B
    have hq₀a' : (q₀ : D) * a * (q₀ : D)⁻¹ * a⁻¹ = z := by
      calc (q₀ : D) * a * (q₀ : D)⁻¹ * a⁻¹ = (a * q₀ * a⁻¹ * (q₀ : D)⁻¹)⁻¹ := by group
        _ = z := by rw [hqa, g.z_inv]
    have hq₀a : (q₀ : D) * a = z * a * q₀ := by
      calc (q₀ : D) * a = ((q₀ : D) * a * (q₀ : D)⁻¹ * a⁻¹) * a * q₀ := by group
        _ = z * a * q₀ := by rw [hq₀a']
    have e : (q₀ : D) * (g.xc q₀ : D) = z * (g.xc q₀ : D) * q₀ := by
      calc (q₀ : D) * (g.xc q₀ : D) = ((q₀ : D) * (g.xc q₀ : D) * (q₀ : D)⁻¹ *
          (g.xc q₀ : D)⁻¹) * (g.xc q₀ : D) * q₀ := by group
        _ = z * (g.xc q₀ : D) * q₀ := by rw [hd]
    have haa₂ : a * a₂⁻¹ = a₂⁻¹ * a :=
      (show Commute a a₂ from g.U_comm g.a_mem_U g.a₂_mem_U).inv_right.eq
    refine ⟨(g.xc q₀ : D) * a, (pCoreOf 2 B).mul_mem (g.xc q₀).2 haQ, ?_, ?_, ?_, ?_, Or.inr rfl⟩
    · calc (g.xc q₀ : D) * a * ((g.xc q₀ : D) * a) = (g.xc q₀ : D) * (a * (g.xc q₀ : D)) * a := by
            group
        _ = (g.xc q₀ : D) * ((g.xc q₀ : D) * a) * a := by rw [haq₁]
        _ = ((g.xc q₀ : D) * (g.xc q₀ : D)) * (a * a) := by group
        _ = 1 := by rw [hq₁inv, g.a_sq]; group
    · calc a * ((g.xc q₀ : D) * a) = (a * (g.xc q₀ : D)) * a := by group
        _ = ((g.xc q₀ : D) * a) * a := by rw [haq₁]
    · calc a₂ * ((g.xc q₀ : D) * a) * a₂⁻¹ * ((g.xc q₀ : D) * a)⁻¹
          = a₂ * (g.xc q₀ : D) * (a * a₂⁻¹) * a⁻¹ * (g.xc q₀ : D)⁻¹ := by group
        _ = a₂ * (g.xc q₀ : D) * (a₂⁻¹ * a) * a⁻¹ * (g.xc q₀ : D)⁻¹ := by rw [haa₂]
        _ = a₂ * (g.xc q₀ : D) * a₂⁻¹ * (g.xc q₀ : D)⁻¹ := by group
        _ = z := ha₂q₁
    · calc (q₀ : D) * ((g.xc q₀ : D) * a) = ((q₀ : D) * (g.xc q₀ : D)) * a := by group
        _ = (z * (g.xc q₀ : D) * q₀) * a := by rw [e]
        _ = z * (g.xc q₀ : D) * ((q₀ : D) * a) := by group
        _ = z * (g.xc q₀ : D) * (z * a * q₀) := by rw [hq₀a]
        _ = z * ((g.xc q₀ : D) * z) * a * q₀ := by group
        _ = z * (z * (g.xc q₀ : D)) * a * q₀ := by rw [hzq₁]
        _ = (z * z) * (g.xc q₀ : D) * a * q₀ := by group
        _ = ((g.xc q₀ : D) * a) * q₀ := by rw [g.z_mul_z, one_mul]

theorem Gen3.isCentralProduct₂_QB (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 64) :
    IsCentralProduct₂ ↥(pCoreOf 2 B) (QuaternionGroup 2) (QuaternionGroup 2) := by
  obtain ⟨q₀, h₀, hinv⟩ := g.exists_q₀_invol hU hT
  obtain ⟨p, hpQ, hpp, hap, ha₂p, hq₀p, hpcases⟩ := g.exists_p hU hT h₀ hinv
  have hz1 : z ≠ 1 := g.hyp.natural.z_ne
  have haQ := g.a_mem_QB
  have ha₂Q : a₂ ∈ pCoreOf 2 B := g.U_le_QB g.a₂_mem_U
  have ha₁Q : a₁ ∈ pCoreOf 2 B := g.U_le_QB g.a₁_mem_U
  have hqa := g.comm_a_of_fst_z (q := q₀) (by rw [h₀])
  have hq₀B : (q₀ : D) ∈ B := pCoreOf_le 2 B q₀.2
  have hzs : z * a = a * z := (g.z_comm g.a_mem_B).symm
  have hzs' : z * a₂ = a₂ * z := (g.z_comm g.a₂_mem_B).symm
  have hts : (q₀ : D) * a * (q₀ : D)⁻¹ = z * a := by
    have hqa' : (q₀ : D) * a * (q₀ : D)⁻¹ * a⁻¹ = z := by
      calc (q₀ : D) * a * (q₀ : D)⁻¹ * a⁻¹ = (a * q₀ * a⁻¹ * (q₀ : D)⁻¹)⁻¹ := by group
        _ = z := by rw [hqa, g.z_inv]
    calc (q₀ : D) * a * (q₀ : D)⁻¹ = ((q₀ : D) * a * (q₀ : D)⁻¹ * a⁻¹) * a := by group
      _ = z * a := by rw [hqa']
  have hts' : p * a₂ * p⁻¹ = z * a₂ := by
    have e : p * a₂ * p⁻¹ * a₂⁻¹ = z := by
      calc p * a₂ * p⁻¹ * a₂⁻¹ = (a₂ * p * a₂⁻¹ * p⁻¹)⁻¹ := by group
        _ = z := by rw [ha₂p, g.z_inv]
    calc p * a₂ * p⁻¹ = (p * a₂ * p⁻¹ * a₂⁻¹) * a₂ := by group
      _ = z * a₂ := by rw [e]
  have c3 : (q₀ : D) * a₂ = a₂ * q₀ := by
    have h := g.comm_a₂ hU q₀
    have e : (a * (q₀ : D) * a⁻¹ * (q₀ : D)⁻¹) * (a₁ * (q₀ : D) * a₁⁻¹ * (q₀ : D)⁻¹) = 1 := by
      change ((psi g q₀).1 : D) * ((psi g q₀).2 : D) = 1
      rw [h₀]
      simp [zel, g.z_mul_z]
    rw [e] at h
    calc (q₀ : D) * a₂ = (a₂ * (q₀ : D) * a₂⁻¹ * (q₀ : D)⁻¹)⁻¹ * (a₂ * q₀) := by group
      _ = a₂ * q₀ := by rw [h]; simp
  refine isCentralProduct₂_of_dihedral_pair (pCoreOf 2 B) (s := a) (t := (q₀ : D)) (s' := a₂)
    (t' := p) (z₀ := z) haQ q₀.2 ha₂Q hpQ hz1 g.z_mul_z hzs hzs' g.a_sq hinv g.a₂_sq hpp hts hts'
    (g.U_comm g.a_mem_U g.a₂_mem_U) hap c3 hq₀p ?_ (g.card_QB hT)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact haQ
    · exact q₀.2
    · exact ha₂Q
    · exact hpQ
  · intro q hq
    set C := Subgroup.closure ({a, (q₀ : D), a₂, p} : Set D) with hC
    have haC : a ∈ C := Subgroup.subset_closure (by simp)
    have hq₀C : (q₀ : D) ∈ C := Subgroup.subset_closure (by simp)
    have ha₂C : a₂ ∈ C := Subgroup.subset_closure (by simp)
    have hpC : p ∈ C := Subgroup.subset_closure (by simp)
    have hzC : z ∈ C := by
      have e : z = a * (q₀ : D) * a⁻¹ * (q₀ : D)⁻¹ := hqa.symm
      rw [e]
      exact C.mul_mem (C.mul_mem (C.mul_mem haC hq₀C) (C.inv_mem haC)) (C.inv_mem hq₀C)
    have ha₁C : a₁ ∈ C := by
      rcases g.a₂_eq_or hU with e | e
      · have : a₁ = a⁻¹ * a₂ := by rw [e]; group
        rw [this]; exact C.mul_mem (C.inv_mem haC) ha₂C
      · have : a₁ = (z * a)⁻¹ * a₂ := by rw [e]; group
        rw [this]; exact C.mul_mem (C.inv_mem (C.mul_mem hzC haC)) ha₂C
    have hVC : ∀ v ∈ V, v ∈ C := by
      intro v hv
      rcases g.mem_V_iff.mp hv with rfl | rfl | rfl | rfl
      · exact C.one_mem
      · exact hzC
      · exact haC
      · exact C.mul_mem hzC haC
    have hUC : ∀ u ∈ conjClosure V B, u ∈ C := by
      intro u hu
      rcases g.mem_U_cases hU hu with huV | ⟨v, hv, rfl⟩
      · exact hVC u huV
      · exact C.mul_mem (hVC v hv) ha₁C
    have hxcC : (g.xc q₀ : D) ∈ C := by
      rcases hpcases with e | e
      · rw [← e]; exact hpC
      · have : (g.xc q₀ : D) = p * a⁻¹ := by rw [e]; group
        rw [this]; exact C.mul_mem hpC (C.inv_mem haC)
    have hcl := g.mem_closure_QB hU hT h₀ hq
    have hle : Subgroup.closure ((conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)}) ≤ C := by
      rw [Subgroup.closure_le]
      rintro w (hw | hw | hw)
      · exact hUC w hw
      · rw [hw]; exact hq₀C
      · rw [Set.mem_singleton_iff.mp hw]; exact hxcC
    exact hle hcl

theorem Gen3.exists_noncomm_QA (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 64) :
    ∃ q ∈ pCoreOf 2 A, ∃ q' ∈ pCoreOf 2 A, q * q' ≠ q' * q := by
  obtain ⟨q₀, h₀⟩ := g.exists_q₀ hU hT
  have rot := g.psi_xc hU
  have hzz := g.zel_mul_zel
  have h₁ : psi g (g.xc q₀) = (1, zel z) := by rw [rot, h₀]; simp [hzz]
  have hq₁B : (g.xc q₀ : D) ∈ B := pCoreOf_le 2 B (g.xc q₀).2
  have hap : a * (g.xc q₀ : D) = (g.xc q₀ : D) * a := g.comm_a_of_fst_one (by rw [h₁])
  have hq₁Q : (g.xc q₀ : D) ∈ pCoreOf 2 A := by
    rw [← inf_inf_centralizer_eq_pCoreOf g.hyp.natural]
    exact ⟨g.hyp.gold.pCoreOf_right_le (g.xc q₀).2,
      Subgroup.mem_centralizer_iff.mpr fun v hv => g.comm_V_of hq₁B hap hv⟩
  refine ⟨a₁, g.hyp.conjClosure_le_pCoreOf_left g.a₁_mem_U, g.xc q₀, hq₁Q, fun hc => ?_⟩
  have h2 := g.comm_a₁_of_snd_z (q := g.xc q₀) (by rw [h₁])
  have : a₁ * (g.xc q₀ : D) * a₁⁻¹ * (g.xc q₀ : D)⁻¹ = 1 := by rw [hc]; group
  rw [this] at h2
  exact g.hyp.natural.z_ne h2.symm

end Q8

end GoldAmL3c

end F6

end CFSG.Quasithin
