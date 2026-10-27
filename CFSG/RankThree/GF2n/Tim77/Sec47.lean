module

public import CFSG.RankThree.GF2n.Tim77.Sec47Basic
public import CFSG.RankThree.GF2n.Tim77.Sec47Aut
public import CFSG.RankThree.GF2n.Tim77.Sec47Mod
public import CFSG.RankThree.GF2n.Tim77.Sec46
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.CGT.Timmesfeld75.BenderInputs6
public import CFSG.RankThree.GF2n.Tim77.Sec47Gen

namespace CFSG.RankThree.GF2n.Tim77

public section
open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G}

theorem sec47_conj_A0_eq (h : Sec3Ctx A Abar S₀ B) {b : G} (hb : b ∈ B) :
    conjSubgroup b (Section3.A0 A Abar) = Section3.A0 A Abar := by
  apply conjSubgroup_eq_of_mem_centralizer
  exact Subgroup.mem_centralizer_iff.mpr fun g hg =>
    (sec46_comm_A h hb (h.setup.L_le hg)).symm

theorem sec47_inter_Q (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {z x : G} (hz : z ∈ Sec45Z A Abar B) (hxA : x ∈ conjSubgroup z A)
    (hxQ : x ∈ Sec45Q A Abar B) : x ∈ conjSubgroup z (Section3.A0 A Abar) := by
  obtain ⟨x₀, hx₀, hx₀1⟩ := sec32a_exists_mem_ne_one h.setup.Lb_ne_bot
  have hB1 : (1 : G) ∈ B := B.one_mem
  have hTIz : IsTI (conjSubgroup z Abar) := by
    obtain ⟨g, hg⟩ := h.exists_abar_eq
    rw [hg]
    exact isTI_conjSubgroup (isTI_conjSubgroup h.hyp.ti g) z
  have hy : z * x₀ * z⁻¹ ∈ conjSubgroup z Abar := by
    rw [mem_conjSubgroup, show z⁻¹ * (z * x₀ * z⁻¹) * z = x₀ by group]
    exact h.setup.Lb_le hx₀
  have hyQ : z * x₀ * z⁻¹ ∈ Sec45Q A Abar B := by
    have hN := sec46_Z_le_normalizer_Q h hS hz
    exact (Subgroup.mem_normalizer_iff.mp hN x₀).mp
      (sec46_Abar0_le_Q A Abar B hB1 hx₀)
  have hy1 : z * x₀ * z⁻¹ ≠ 1 := fun e => hx₀1 (by
    have := congrArg (fun t => z⁻¹ * t * z) e
    simpa [mul_assoc] using this)
  have hcomm : x * (z * x₀ * z⁻¹) = (z * x₀ * z⁻¹) * x :=
    sec46_hNc h hS x hxQ _ hyQ
  have hN : x ∈ normalizer (conjSubgroup z Abar : Set G) :=
    mem_normalizer_of_commute_of_isTI hTIz hy hy1 hcomm
  rw [h.a0_eq, sec41g_conj_inf_normalizer]
  exact Subgroup.mem_inf.mpr ⟨hxA, hN⟩

theorem sec47_comm_of_quot (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {y w e f : G} (hy : y ∈ Sec45Z A Abar B) (hw : w ∈ Sec45Z A Abar B)
    (he : e ∈ conjSubgroup y A) (heA : e ∉ conjSubgroup y (Section3.A0 A Abar))
    (hf : f ∈ conjSubgroup w A) (hfA : f ∉ conjSubgroup w (Section3.A0 A Abar))
    (hc : e * f * (f * e)⁻¹ ∈ Sec45Q A Abar B) :
    ∀ x ∈ conjSubgroup y A, ∀ v ∈ conjSubgroup w A, x * v = v * x := by
  by_cases hnc : ∀ x ∈ conjSubgroup y A, ∀ v ∈ conjSubgroup w A, x * v = v * x
  · exact hnc
  exfalso
  have hAN := sec46_hAN h hS
  have hNc := sec46_hNc h hS
  have S := sec41g_prop24 h hAN hNc hy hw hnc
  have hEy : IsElemAbelian 2 (conjSubgroup y A) := isElemAbelian_conj h.hyp.elemAbelian y
  have hEw : IsElemAbelian 2 (conjSubgroup w A) := isElemAbelian_conj h.hyp.elemAbelian w
  have he2 : e * e = 1 := by rw [← sq]; exact hEy.2 e he
  have hf2 : f * f = 1 := by rw [← sq]; exact hEw.2 f hf
  have hinv_e : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have hinv_f : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
  have hodd : Odd (orderOf (e * f)) := S.odd_orderOf_mul he heA hf hfA
  have hcQ : e * f * (e * f) ∈ Sec45Q A Abar B := by
    have := hc
    rwa [mul_inv_rev, hinv_e, hinv_f] at this
  obtain ⟨j, hj⟩ := hodd
  have hpow : (e * f) ^ (2 * j + 2) = e * f := by
    rw [show 2 * j + 2 = orderOf (e * f) + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  have hmemQ : e * f ∈ Sec45Q A Abar B := by
    rw [← hpow, show 2 * j + 2 = 2 * (j + 1) by ring, pow_mul, sq]
    exact Subgroup.pow_mem _ hcQ (j + 1)
  have hsq : (e * f) ^ 2 = 1 := (sec46_Q_elemAbelian h hS).2 _ hmemQ
  have hdvd : orderOf (e * f) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hle : orderOf (e * f) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hj0 : j = 0 := by omega
  have hef : e * f = 1 := by
    have h1 : orderOf (e * f) = 1 := by omega
    exact orderOf_eq_one_iff.mp h1
  have hfe : f = e := by
    have := eq_inv_of_mul_eq_one_right hef
    rw [this, hinv_e]
  have heH : e ∈ conjSubgroup w A := hfe ▸ hf
  have hcomm_of : ∀ x ∈ conjSubgroup w A, e * x = x * e := fun x hx => by
    have := hEw.1.is_comm.comm ⟨e, heH⟩ ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hewA : e ∈ normalizer (conjSubgroup w A : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · have e1 : e * x * e⁻¹ = x := by rw [hcomm_of x hx]; group
      rw [e1]
      exact hx
    · have key : e⁻¹ * (e * x * e⁻¹) * e = x := by group
      rw [← key]
      exact (conjSubgroup w A).mul_mem ((conjSubgroup w A).mul_mem
        ((conjSubgroup w A).inv_mem heH) hx) heH
  have := sec41g_key h hAN hNc hy hw hnc
  apply heA
  rw [← this]
  exact Subgroup.mem_inf.mpr ⟨he, hewA⟩

theorem sec47_le_comap {N T : Subgroup G} {g : G} (hT : ∀ t ∈ T, g * t * g⁻¹ ∈ N) :
    T ≤ N.comap (MulAut.conj g).toMonoidHom := fun t ht => by
  rw [Subgroup.mem_comap]
  exact hT t ht

theorem sec47_mem_normalizer_of_invol {N : Subgroup G} {g : G} (hg : g * g = 1)
    (hN : ∀ x ∈ N, g * x * g⁻¹ ∈ N) : g ∈ normalizer (N : Set G) := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hN x hx, fun hx => ?_⟩
  have h2 := hN _ hx
  have e : g * (g * x * g⁻¹) * g⁻¹ = x := by
    rw [hinv]
    calc g * (g * x * g) * g = (g * g) * x * (g * g) := by simp only [mul_assoc]
      _ = x := by rw [hg, one_mul, mul_one]
  rwa [e] at h2

@[expose] def sec47P (A Abar B : Subgroup G) : Subgroup G :=
  ⨆ (y : G) (_ : y ∈ Sec45Z A Abar B ∧ conjSubgroup y A ≤ centralizer (A : Set G)),
    conjSubgroup y (Section3.A0 A Abar)

theorem sec47P_le_Q (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) :
    sec47P A Abar B ≤ Sec45Q A Abar B :=
  iSup_le fun y => iSup_le fun hy => sec46_hAN h hS y hy.1

theorem sec47P_comm (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {e y w x : G} (hy : y ∈ Sec45Z A Abar B) (hyC : conjSubgroup y A ≤ centralizer (A : Set G))
    (he : e ∈ conjSubgroup y A) (hw : w ∈ Sec45Z A Abar B)
    (hwC : conjSubgroup w A ≤ centralizer (A : Set G)) (hx : x ∈ conjSubgroup w A) :
    e * x = x * e :=
  sec41g_comm_pair h (sec46_hAN h hS) (sec46_hNc h hS) hy hw he hx hyC hwC

theorem sec47P_centralized_by (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {e y : G} (hy : y ∈ Sec45Z A Abar B) (hyC : conjSubgroup y A ≤ centralizer (A : Set G))
    (he : e ∈ conjSubgroup y A) (x : G) (hx : x ∈ sec47P A Abar B) : e * x = x * e := by
  have hP : sec47P A Abar B ≤ Subgroup.centralizer ({e} : Set G) := by
    refine iSup_le fun w => iSup_le fun hw => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    rw [hf]
    exact sec47P_comm h hS hy hyC he hw.1 hw.2 (conjSubgroup_mono h.setup.L_le hx)
  exact Subgroup.mem_centralizer_iff.mp (hP hx) e (Set.mem_singleton e)

theorem sec47_conj_eq_of_comm {g t : G} (h : g * t = t * g) : g * t * g⁻¹ = t := by
  rw [h]
  group

theorem sec47P_comm_A (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {α x : G} (hα : α ∈ A) (hx : x ∈ sec47P A Abar B) : α * x = x * α := by
  have hP : sec47P A Abar B ≤ Subgroup.centralizer (A : Set G) := by
    refine iSup_le fun w => iSup_le fun hw => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp (hw.2 (conjSubgroup_mono h.setup.L_le hx)) a ha
  exact Subgroup.mem_centralizer_iff.mp (hP hx) α hα

theorem sec47_fam (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {α : G} (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar) {e : G}
    (he : e ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar)) (heα : e * α = α * e) :
    ∃ y ∈ Sec45Z A Abar B, e ∈ conjSubgroup y A ∧ e ∉ conjSubgroup y (Section3.A0 A Abar) ∧
      conjSubgroup y A ≤ centralizer (A : Set G) := by
  obtain ⟨y, hy, a, ha, haA₀, rfl⟩ := sec41g_mem_D.mp he
  refine ⟨y, hy, sec41g_mem_conj ha, sec41g_not_mem_conj haA₀, ?_⟩
  have hα1 : α ∈ conjSubgroup (1 : G) A := by rw [conjSubgroup_one]; exact hα
  have hαA01 : α ∉ conjSubgroup (1 : G) (Section3.A0 A Abar) := by
    rw [conjSubgroup_one]; exact hαA₀
  have hc : y * a * y⁻¹ * α * (α * (y * a * y⁻¹))⁻¹ ∈ Sec45Q A Abar B := by
    have e1 : y * a * y⁻¹ * α = α * (y * a * y⁻¹) := heα
    rw [e1, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hcomm := sec47_comm_of_quot h hS hy (Subgroup.one_mem _) (sec41g_mem_conj ha)
    (sec41g_not_mem_conj haA₀) hα1 hαA01 hc
  simp only [conjSubgroup_one] at hcomm
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (hcomm x hx v hv).symm

@[expose] def sec47N1 (A Abar B : Subgroup G) (h₀ : G) : Subgroup G :=
  (Section3.A0 A Abar ⊔ sec47P A Abar B) ⊔ conjSubgroup h₀ (Section3.A0 A Abar)

theorem sec47_conj_le_P {y : G} (hy : y ∈ Sec45Z A Abar B)
    (hyC : conjSubgroup y A ≤ centralizer (A : Set G)) :
    conjSubgroup y (Section3.A0 A Abar) ≤ sec47P A Abar B :=
  le_iSup_of_le y (le_iSup_of_le ⟨hy, hyC⟩ le_rfl)

theorem sec47_comm_conj (h : Sec3Ctx A Abar S₀ B) {h₀ x v : G}
    (hx : x ∈ conjSubgroup h₀ A) (hv : v ∈ conjSubgroup h₀ A) : x * v = v * x :=
  IsElemAbelian.comm (isElemAbelian_conj h.hyp.elemAbelian h₀) hx hv

theorem sec47_N1_le_Q (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {h₀ : G}
    (hh₀ : h₀ ∈ Sec45Z A Abar B) : sec47N1 A Abar B h₀ ≤ Sec45Q A Abar B :=
  sup_le (sup_le (sec46_A0_le_Q A Abar B) (sec47P_le_Q h hS)) (sec46_hAN h hS h₀ hh₀)

theorem sec47_normalizes_fam (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {h₀ : G}
    (hh₀ : h₀ ∈ Sec45Z A Abar B) {y e : G} (hy : y ∈ Sec45Z A Abar B)
    (hyC : conjSubgroup y A ≤ centralizer (A : Set G))
    (he : e ∈ conjSubgroup y A) (heA : e ∉ conjSubgroup y (Section3.A0 A Abar))
    (hee : e * e = 1) :
    e ∈ normalizer ((sec47N1 A Abar B h₀ : Subgroup G) : Set G) := by
  have hPN : sec47P A Abar B ≤ sec47N1 A Abar B h₀ := le_sup_right.trans le_sup_left
  have hA0N : Section3.A0 A Abar ≤ sec47N1 A Abar B h₀ := le_sup_left.trans le_sup_left
  have hhN : conjSubgroup h₀ (Section3.A0 A Abar) ≤ sec47N1 A Abar B h₀ := le_sup_right
  have hcA0 : ∀ t ∈ Section3.A0 A Abar, e * t * e⁻¹ = t := fun t ht =>
    sec47_conj_eq_of_comm
      (Subgroup.mem_centralizer_iff.mp (hyC he) t (h.setup.L_le ht)).symm
  have hcP : ∀ t ∈ sec47P A Abar B, e * t * e⁻¹ = t := fun t ht =>
    sec47_conj_eq_of_comm (sec47P_centralized_by h hS hy hyC he t ht)
  have hcH : ∀ t ∈ conjSubgroup h₀ (Section3.A0 A Abar),
      e * t * e⁻¹ ∈ sec47N1 A Abar B h₀ := by
    intro t ht
    by_cases hc : ∀ x ∈ conjSubgroup y A, ∀ v ∈ conjSubgroup h₀ A, x * v = v * x
    · have ht' : t ∈ conjSubgroup h₀ A := conjSubgroup_mono h.setup.L_le ht
      rw [sec47_conj_eq_of_comm (hc e he t ht')]
      exact hhN ht
    · have S := sec41g_prop24 h (sec46_hAN h hS) (sec46_hNc h hS) hy hh₀ hc
      have hM := S.sup_le_normalizer_M
      have hyA : conjSubgroup y A ≤ conjSubgroup y A ⊔ conjSubgroup h₀ A := le_sup_left
      have hen : e ∈ normalizer ((conjSubgroup y (Section3.A0 A Abar) ⊔
          conjSubgroup h₀ (Section3.A0 A Abar) : Subgroup G) : Set G) :=
        hM (hyA he)
      have hMN : conjSubgroup y (Section3.A0 A Abar) ⊔
          conjSubgroup h₀ (Section3.A0 A Abar) ≤ sec47N1 A Abar B h₀ :=
        sup_le ((sec47_conj_le_P hy hyC).trans hPN) hhN
      have hA₀le : conjSubgroup h₀ (Section3.A0 A Abar) ≤
          conjSubgroup y (Section3.A0 A Abar) ⊔ conjSubgroup h₀ (Section3.A0 A Abar) := le_sup_right
      exact hMN ((Subgroup.mem_normalizer_iff.mp hen t).mp (hA₀le ht))
  apply sec47_mem_normalizer_of_invol hee
  have hsup : sec47N1 A Abar B h₀ ≤ (sec47N1 A Abar B h₀).comap (MulAut.conj e).toMonoidHom :=
    sup_le (sup_le (sec47_le_comap fun t ht => by rw [hcA0 t ht]; exact hA0N ht)
      (sec47_le_comap fun t ht => by rw [hcP t ht]; exact hPN ht))
      (sec47_le_comap hcH)
  exact fun x hx => hsup hx

theorem sec47_normalizes_alpha (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {h₀ α : G}
    (hh₀ : h₀ ∈ Sec45Z A Abar B) (hα : α ∈ A) (hαα : α * α = 1) :
    α ∈ normalizer ((sec47N1 A Abar B h₀ : Subgroup G) : Set G) := by
  have hPN : sec47P A Abar B ≤ sec47N1 A Abar B h₀ := le_sup_right.trans le_sup_left
  have hA0N : Section3.A0 A Abar ≤ sec47N1 A Abar B h₀ := le_sup_left.trans le_sup_left
  have hhN : conjSubgroup h₀ (Section3.A0 A Abar) ≤ sec47N1 A Abar B h₀ := le_sup_right
  have hcA0 : ∀ t ∈ Section3.A0 A Abar, α * t * α⁻¹ = t := fun t ht =>
    sec47_conj_eq_of_comm (h.setup.comm_A hα (h.setup.L_le ht))
  have hcP : ∀ t ∈ sec47P A Abar B, α * t * α⁻¹ = t := fun t ht =>
    sec47_conj_eq_of_comm (sec47P_comm_A h hS hα ht)
  have hcH : ∀ t ∈ conjSubgroup h₀ (Section3.A0 A Abar),
      α * t * α⁻¹ ∈ sec47N1 A Abar B h₀ := by
    intro t ht
    by_cases hc : ∀ x ∈ A, ∀ v ∈ conjSubgroup h₀ A, x * v = v * x
    · have ht' : t ∈ conjSubgroup h₀ A := conjSubgroup_mono h.setup.L_le ht
      rw [sec47_conj_eq_of_comm (hc α hα t ht')]
      exact hhN ht
    · have S := sec41g_prop24 h (sec46_hAN h hS) (sec46_hNc h hS) (Subgroup.one_mem _) hh₀
        (by simpa only [conjSubgroup_one] using hc)
      have hM := S.sup_le_normalizer_M
      simp only [conjSubgroup_one] at hM
      have hAle : A ≤ A ⊔ conjSubgroup h₀ A := le_sup_left
      have hen : α ∈ normalizer ((Section3.A0 A Abar ⊔
          conjSubgroup h₀ (Section3.A0 A Abar) : Subgroup G) : Set G) :=
        hM (hAle hα)
      have hMN : Section3.A0 A Abar ⊔ conjSubgroup h₀ (Section3.A0 A Abar) ≤
          sec47N1 A Abar B h₀ := sup_le hA0N hhN
      have hA₀le : conjSubgroup h₀ (Section3.A0 A Abar) ≤
          Section3.A0 A Abar ⊔ conjSubgroup h₀ (Section3.A0 A Abar) := le_sup_right
      exact hMN ((Subgroup.mem_normalizer_iff.mp hen t).mp (hA₀le ht))
  apply sec47_mem_normalizer_of_invol hαα
  have hsup : sec47N1 A Abar B h₀ ≤ (sec47N1 A Abar B h₀).comap (MulAut.conj α).toMonoidHom :=
    sup_le (sup_le (sec47_le_comap fun t ht => by rw [hcA0 t ht]; exact hA0N ht)
      (sec47_le_comap fun t ht => by rw [hcP t ht]; exact hPN ht))
      (sec47_le_comap hcH)
  exact fun x hx => hsup hx

theorem sec47_normalizes_gamma (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {h₀ γ : G}
    (hh₀ : h₀ ∈ Sec45Z A Abar B) (hγ : γ ∈ conjSubgroup h₀ A) (hγγ : γ * γ = 1) :
    γ ∈ normalizer ((sec47N1 A Abar B h₀ : Subgroup G) : Set G) := by
  have hPN : sec47P A Abar B ≤ sec47N1 A Abar B h₀ := le_sup_right.trans le_sup_left
  have hA0N : Section3.A0 A Abar ≤ sec47N1 A Abar B h₀ := le_sup_left.trans le_sup_left
  have hhN : conjSubgroup h₀ (Section3.A0 A Abar) ≤ sec47N1 A Abar B h₀ := le_sup_right
  have hPc : sec47P A Abar B ≤ (sec47N1 A Abar B h₀).comap (MulAut.conj γ).toMonoidHom := by
    refine iSup_le fun w => iSup_le fun hw => ?_
    refine sec47_le_comap fun x hx => ?_
    by_cases hc2 : ∀ u ∈ conjSubgroup w A, ∀ v ∈ conjSubgroup h₀ A, u * v = v * u
    · rw [sec47_conj_eq_of_comm (hc2 x (conjSubgroup_mono h.setup.L_le hx) γ hγ).symm]
      exact hPN (sec47_conj_le_P hw.1 hw.2 hx)
    · have S := sec41g_prop24 h (sec46_hAN h hS) (sec46_hNc h hS) hw.1 hh₀ hc2
      have hM := S.sup_le_normalizer_M
      have hwA : conjSubgroup w A ≤ conjSubgroup w A ⊔ conjSubgroup h₀ A := le_sup_left
      have hγA : conjSubgroup h₀ A ≤ conjSubgroup w A ⊔ conjSubgroup h₀ A := le_sup_right
      have hγN : γ ∈ normalizer ((conjSubgroup w (Section3.A0 A Abar) ⊔
          conjSubgroup h₀ (Section3.A0 A Abar) : Subgroup G) : Set G) := hM (hγA hγ)
      have hMN : conjSubgroup w (Section3.A0 A Abar) ⊔
          conjSubgroup h₀ (Section3.A0 A Abar) ≤ sec47N1 A Abar B h₀ :=
        sup_le ((sec47_conj_le_P hw.1 hw.2).trans hPN) hhN
      have hwx : conjSubgroup w (Section3.A0 A Abar) ≤ conjSubgroup w (Section3.A0 A Abar) ⊔
          conjSubgroup h₀ (Section3.A0 A Abar) := le_sup_left
      exact hMN ((Subgroup.mem_normalizer_iff.mp hγN x).mp (hwx hx))
  have hA0c : Section3.A0 A Abar ≤ (sec47N1 A Abar B h₀).comap (MulAut.conj γ).toMonoidHom := by
    refine sec47_le_comap fun t ht => ?_
    by_cases hcA : ∀ x ∈ A, ∀ v ∈ conjSubgroup h₀ A, x * v = v * x
    · rw [sec47_conj_eq_of_comm (hcA t (h.setup.L_le ht) γ hγ).symm]
      exact hA0N ht
    · have S := sec41g_prop24 h (sec46_hAN h hS) (sec46_hNc h hS) (Subgroup.one_mem _) hh₀
        (by simpa only [conjSubgroup_one] using hcA)
      have hM := S.sup_le_normalizer_M
      simp only [conjSubgroup_one] at hM
      have hγA : conjSubgroup h₀ A ≤ A ⊔ conjSubgroup h₀ A := le_sup_right
      have hγN : γ ∈ normalizer ((Section3.A0 A Abar ⊔
          conjSubgroup h₀ (Section3.A0 A Abar) : Subgroup G) : Set G) := hM (hγA hγ)
      have hMN : Section3.A0 A Abar ⊔ conjSubgroup h₀ (Section3.A0 A Abar) ≤
          sec47N1 A Abar B h₀ := sup_le hA0N hhN
      have hA₀le : Section3.A0 A Abar ≤
          Section3.A0 A Abar ⊔ conjSubgroup h₀ (Section3.A0 A Abar) := le_sup_left
      exact hMN ((Subgroup.mem_normalizer_iff.mp hγN t).mp (hA₀le ht))
  have hhc : conjSubgroup h₀ (Section3.A0 A Abar) ≤
      (sec47N1 A Abar B h₀).comap (MulAut.conj γ).toMonoidHom := by
    refine sec47_le_comap fun t ht => ?_
    have ht' : t ∈ conjSubgroup h₀ A := conjSubgroup_mono h.setup.L_le ht
    rw [sec47_conj_eq_of_comm (sec47_comm_conj h hγ ht')]
    exact hhN ht
  apply sec47_mem_normalizer_of_invol hγγ
  have hsup : sec47N1 A Abar B h₀ ≤
      (sec47N1 A Abar B h₀).comap (MulAut.conj γ).toMonoidHom :=
    sup_le (sup_le hA0c hPc) hhc
  exact fun x hx => hsup hx

theorem sec47_Q_le_of_conj (h : Sec3Ctx A Abar S₀ B) {N : Subgroup G}
    (hN : ∀ z ∈ Sec45Z A Abar B, conjSubgroup z (Section3.A0 A Abar) ≤ N)
    (hA₀ : Section3.A0 A Abar ≤ N) : Sec45Q A Abar B ≤ N := by
  obtain ⟨k, hk, -, hk0⟩ := sa_exists_k h
  have hkZ : k ∈ Sec45Z A Abar B := sec46_k_mem_Z hk B.one_mem
  unfold Sec45Q
  refine sup_le hA₀ (iSup₂_le fun b hb => ?_)
  have hbk : b * k * b⁻¹ ∈ Sec45Z A Abar B := sec46_conj_mem_Z h hb hkZ
  have e : conjSubgroup b (Section3.Abar0 A Abar) =
      conjSubgroup (b * k * b⁻¹) (Section3.A0 A Abar) := by
    rw [hk0]
    calc conjSubgroup b (conjSubgroup k (Section3.A0 A Abar))
        = conjSubgroup (b * k) (Section3.A0 A Abar) := (conjSubgroup_mul b k _).symm
      _ = conjSubgroup ((b * k * b⁻¹) * b) (Section3.A0 A Abar) := by
          rw [show b * k * b⁻¹ * b = b * k by group]
      _ = conjSubgroup (b * k * b⁻¹) (conjSubgroup b (Section3.A0 A Abar)) :=
          conjSubgroup_mul _ _ _
      _ = conjSubgroup (b * k * b⁻¹) (Section3.A0 A Abar) := by
          rw [sec47_conj_A0_eq h hb]
  rw [e]
  exact hN _ hbk

theorem sec47_A0_le_N1 (h₀ : G) :
    Section3.A0 A Abar ≤ sec47N1 A Abar B h₀ := le_sup_left.trans le_sup_left

theorem sec47_Q_le_N1 (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {h₀ : G}
    (hN : Sec45Z A Abar B ≤ normalizer ((sec47N1 A Abar B h₀ : Subgroup G) : Set G)) :
    Sec45Q A Abar B ≤ sec47N1 A Abar B h₀ :=
  sec47_Q_le_of_conj h (fun z hz t ht => by
      have hx : z⁻¹ * t * z ∈ sec47N1 A Abar B h₀ :=
        sec47_A0_le_N1 h₀ (mem_conjSubgroup.mp ht)
      have e : z * (z⁻¹ * t * z) * z⁻¹ = t := by group
      have := (Subgroup.mem_normalizer_iff.mp (hN hz) (z⁻¹ * t * z)).mp hx
      rwa [e] at this) (sec47_A0_le_N1 h₀)
end

public section
open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G}

theorem sec47_E_conj
    (h : Sec3Ctx A Abar S₀ B) {α : G} (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar)
    {d : G} (hd : d ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar)) :
    ∃ g ∈ Sec45Z A Abar B, d = g * α * g⁻¹ := by
  obtain ⟨d₀, hd₀, hcl⟩ := sec46_single h
  have hα' : α ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) :=
    sec41g_mem_D.mpr ⟨1, Subgroup.one_mem _, α, hα, hαA₀, by simp⟩
  obtain ⟨g₀, hg₀, hgα⟩ := hcl α hα'
  obtain ⟨g₁, hg₁, hgd⟩ := hcl d hd
  refine ⟨g₁ * g₀⁻¹, Subgroup.mul_mem _ hg₁ (Subgroup.inv_mem _ hg₀), ?_⟩
  rw [hgd, hgα]
  group

abbrev sec47Kz (A Abar B : Subgroup G) [((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal] :
    Type :=
  ↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)

abbrev sec47Lz (A Abar B : Subgroup G) [((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal] :
    Type :=
  sec47Kz A Abar B ⧸ Subgroup.center (sec47Kz A Abar B)

theorem sec47_alpha_ne_one
    [hN : ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal]
    [Nontrivial (sec47Lz A Abar B)]
    (h : Sec3Ctx A Abar S₀ B) (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {α : G} (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar) :
    (QuotientGroup.mk' (Subgroup.center (sec47Kz A Abar B))
      (QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))
        (⟨α, sec46_A_le_Z A Abar B hα⟩ : ↥(Sec45Z A Abar B)))) ≠ 1 := by
  intro h1
  set φ : ↥(Sec45Z A Abar B) →* sec47Lz A Abar B :=
    (QuotientGroup.mk' (Subgroup.center (sec47Kz A Abar B))).comp
      (QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))) with hφ
  have hαφ : φ ⟨α, sec46_A_le_Z A Abar B hα⟩ = 1 := h1
  have hφ1 : ∀ z : ↥(Sec45Z A Abar B), (z : G) ∈ sec41g_D (Sec45Z A Abar B) A
      (Section3.A0 A Abar) → φ z = 1 := by
    intro z hz
    obtain ⟨g, hg, hzg⟩ := sec47_E_conj h hα hαA₀ hz
    have e : z = ⟨g, hg⟩ * ⟨α, sec46_A_le_Z A Abar B hα⟩ * (⟨g, hg⟩)⁻¹ :=
      Subtype.ext (by simp [hzg])
    rw [e, map_mul, map_mul, map_inv, hαφ, mul_one, mul_inv_cancel]
  have hall : ∀ z : ↥(Sec45Z A Abar B), φ z = 1 := by
    intro z
    have hz := sec46_gen h hS z
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hφ1 x hx
      · show (QuotientGroup.mk' (Subgroup.center (sec47Kz A Abar B)))
          (QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) x) = 1
        have h2 : QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) x =
            (1 : sec47Kz A Abar B) := (QuotientGroup.eq_one_iff x).mpr hx
        rw [h2, map_one]
    | one => exact map_one φ
    | mul x y _ _ hx hy => rw [map_mul, hx, hy, mul_one]
    | inv x _ hx => rw [map_inv, hx, inv_one]
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (sec47Lz A Abar B)
  have hsurj : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  exact hxy (by rw [hall x', hall y'])

def sec47phi (A Abar B : Subgroup G)
    [((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal] :
    ↥(Sec45Z A Abar B) →* sec47Lz A Abar B :=
  (QuotientGroup.mk' (Subgroup.center (sec47Kz A Abar B))).comp
    (QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)))

theorem sec47_family_lift
    [((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal]
    [Nontrivial (sec47Lz A Abar B)]
    (h : Sec3Ctx A Abar S₀ B) (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {α : G} (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar)
    (hconj : ∀ x y : sec47Lz A Abar B, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hαL : orderOf (sec47phi A Abar B ⟨α, sec46_A_le_Z A Abar B hα⟩) = 2)
    (x : sec47Lz A Abar B) (hx : orderOf x = 2)
    (hxc : Commute x (sec47phi A Abar B ⟨α, sec46_A_le_Z A Abar B hα⟩)) :
    ∃ e : G, e ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) ∧ e * α = α * e ∧
      ∃ hez : e ∈ Sec45Z A Abar B, sec47phi A Abar B ⟨e, hez⟩ = x := by
  set αZ : ↥(Sec45Z A Abar B) := ⟨α, sec46_A_le_Z A Abar B hα⟩ with hαZ
  obtain ⟨c, hc⟩ := (isConj_iff.mp (hconj _ _ hαL hx))
  obtain ⟨z₁, hz₁⟩ := (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))) c
  set e : G := (z₁ : G) * α * (z₁ : G)⁻¹ with he
  have hE : e ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) :=
    sec41g_mem_D.mpr ⟨z₁, z₁.2, α, hα, hαA₀, rfl⟩
  have heZ : e ∈ Sec45Z A Abar B := sec46_D_le_Z hE
  set eZ : ↥(Sec45Z A Abar B) := ⟨e, heZ⟩ with heZdef
  have hz₁' : sec47phi A Abar B z₁ = c := hz₁
  have hαD : α ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) :=
    sec41g_mem_D.mpr ⟨1, Subgroup.one_mem _, α, hα, hαA₀, by simp⟩
  have hφe : sec47phi A Abar B eZ = x := by
    have e1 : eZ = z₁ * αZ * z₁⁻¹ := Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv, hz₁', hc]
  have hsec := sec46_sec42Data h hS (sec46_single h) (sec46_O2 h hS)
  have hcomm_K : Commute (QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) eZ)
      (QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) αZ) := by
    apply qp_commute_lift_Z hsec
    · exact ⟨eZ, hE, rfl⟩
    · exact ⟨αZ, hαD, rfl⟩
    · show Commute (sec47phi A Abar B eZ) (sec47phi A Abar B αZ)
      rw [hφe]
      exact hxc
  have hK := hcomm_K.eq
  have hQN := QuotientGroup.eq.mp hK
  have hQ' : (e * α)⁻¹ * (α * e) ∈ Sec45Q A Abar B := Subgroup.mem_subgroupOf.mp hQN
  have hee : e * e = 1 := sec46_D_sq h hE
  have hαα : α * α = 1 := sec46_D_sq h hαD
  have hinvE : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hinvα : α⁻¹ = α := inv_eq_of_mul_eq_one_right hαα
  have e1 : e * α * (α * e)⁻¹ = ((e * α)⁻¹ * (α * e))⁻¹ := by
    simp only [mul_inv_rev, hinvE, hinvα, mul_assoc]
  have hc' : e * α * (α * e)⁻¹ ∈ Sec45Q A Abar B := by
    rw [e1]
    exact (Sec45Q A Abar B).inv_mem hQ'
  have hcomm := sec47_comm_of_quot h hS (y := z₁) (w := 1) z₁.2 (Subgroup.one_mem _)
    (sec41g_mem_conj hα) (sec41g_not_mem_conj hαA₀)
    (by rw [conjSubgroup_one]; exact hα) (by rw [conjSubgroup_one]; exact hαA₀) hc'
  refine ⟨e, hE, ?_, heZ, hφe⟩
  have := hcomm e (sec41g_mem_conj hα) α (by rw [conjSubgroup_one]; exact hα)
  exact this

theorem sec47_gen_Z
    [((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal]
    (h : Sec3Ctx A Abar S₀ B) (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {α : G} (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar)
    (hsimp : IsSimpleGroup (sec47Lz A Abar B)) (hperf : Group.IsPerfect (sec47Lz A Abar B))
    (hconj : ∀ x y : sec47Lz A Abar B, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hLgen : ∀ a g : sec47Lz A Abar B, orderOf a = 2 → orderOf g = 2 → ¬ Commute a g →
      Subgroup.closure ({x : sec47Lz A Abar B | x * x = 1 ∧ Commute x a} ∪ {g}) = ⊤) :
    ∃ γ : G, γ ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) ∧ ¬ Commute γ α ∧
      Sec45Z A Abar B ≤ Subgroup.closure ({e : G | e ∈ sec41g_D (Sec45Z A Abar B) A
        (Section3.A0 A Abar) ∧ e * α = α * e} ∪ {α, γ}) ⊔ Sec45Q A Abar B := by
  classical
  haveI := hsimp
  have hαD : α ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) :=
    sec41g_mem_D.mpr ⟨1, Subgroup.one_mem _, α, hα, hαA₀, by simp⟩
  have hαα : α * α = 1 := sec46_D_sq h hαD
  set αZ : ↥(Sec45Z A Abar B) := ⟨α, sec46_A_le_Z A Abar B hα⟩ with hαZ
  have hᾱ1 : sec47phi A Abar B αZ ≠ 1 := sec47_alpha_ne_one h hS hα hαA₀
  have hᾱ2 : sec47phi A Abar B αZ * sec47phi A Abar B αZ = 1 := by
    rw [← map_mul]
    have : αZ * αZ = 1 := Subtype.ext hαα
    rw [this, map_one]
  have hᾱord : orderOf (sec47phi A Abar B αZ) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hᾱ2) hᾱ1
  obtain ⟨t, ht2, htn⟩ := sec47_exists_noncomm_invol hsimp hperf hᾱord
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj _ _ hᾱord ht2)
  obtain ⟨z₀, hz₀⟩ := (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))) c
  have hz₀' : sec47phi A Abar B z₀ = c := hz₀
  set γ : G := (z₀ : G) * α * (z₀ : G)⁻¹ with hγdef
  have hγE : γ ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) :=
    sec41g_mem_D.mpr ⟨z₀, z₀.2, α, hα, hαA₀, rfl⟩
  have hγZ : γ ∈ Sec45Z A Abar B := sec46_D_le_Z hγE
  set γZ : ↥(Sec45Z A Abar B) := ⟨γ, hγZ⟩ with hγZdef
  have hφγ : sec47phi A Abar B γZ = t := by
    have e1 : γZ = z₀ * αZ * z₀⁻¹ := Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv, hz₀', hc]
  have hγn : ¬ Commute γ α := by
    intro hcomm
    apply htn
    have hc2 : sec47phi A Abar B αZ * t = t * sec47phi A Abar B αZ := by
      rw [← hφγ, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm.symm
    exact hc2
  set T : Set G := {e : G | e ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) ∧
    e * α = α * e} ∪ {α, γ} with hT
  set Tz : Set ↥(Sec45Z A Abar B) := {z | (z : G) ∈ T} with hTz
  have hTsub : ∀ e ∈ T, e ∈ Sec45Z A Abar B := by
    rintro e (⟨he, -⟩ | he)
    · exact sec46_D_le_Z he
    · rcases he with rfl | rfl
      · exact sec46_A_le_Z A Abar B hα
      · exact hγZ
  have htn' : ¬ Commute (sec47phi A Abar B αZ) (sec47phi A Abar B γZ) := by
    rw [hφγ]
    exact htn
  have hLtop : Subgroup.closure (sec47phi A Abar B '' Tz) = ⊤ := by
    rw [eq_top_iff]
    have hS1 := hLgen (sec47phi A Abar B αZ) (sec47phi A Abar B γZ) hᾱord
      (by rw [hφγ]; exact ht2) htn'
    rw [← hS1]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro x (⟨hx2, hxc⟩ | hxg)
    · by_cases hx1 : x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      · have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
        obtain ⟨e, he, hec, hez, hφe⟩ :=
          sec47_family_lift h hS hα hαA₀ hconj hᾱord x hxo hxc
        apply Subgroup.subset_closure
        exact ⟨⟨e, hez⟩, Or.inl ⟨he, hec⟩, hφe⟩
    · rw [Set.mem_singleton_iff] at hxg
      rw [hxg]
      apply Subgroup.subset_closure
      exact ⟨γZ, Or.inr (Set.mem_insert_of_mem _ rfl), rfl⟩
  set W : Subgroup ↥(Sec45Z A Abar B) := Subgroup.closure Tz with hW
  have hWL : ∀ z : ↥(Sec45Z A Abar B), sec47phi A Abar B z ∈ W.map (sec47phi A Abar B) := by
    intro z
    have hmap : W.map (sec47phi A Abar B) = Subgroup.closure (sec47phi A Abar B '' Tz) :=
      MonoidHom.map_closure _ _
    rw [hmap, hLtop]
    exact Subgroup.mem_top _
  set N : Subgroup ↥(Sec45Z A Abar B) := (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B) with hN
  set πK : ↥(Sec45Z A Abar B) →* sec47Kz A Abar B := QuotientGroup.mk' N with hπK
  set WK : Subgroup (sec47Kz A Abar B) := W.map πK with hWK
  have hWK_comm : ∀ k : sec47Kz A Abar B,
      ∃ w ∈ WK, w⁻¹ * k ∈ Subgroup.center (sec47Kz A Abar B) := by
    intro k
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective N k
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp (hWL z)
    refine ⟨πK w, Subgroup.mem_map_of_mem _ hw, ?_⟩
    have h1 : QuotientGroup.mk' (Subgroup.center (sec47Kz A Abar B)) ((πK w)⁻¹ * πK z) = 1 := by
      rw [map_mul, map_inv]
      have hwe' : QuotientGroup.mk' (Subgroup.center (sec47Kz A Abar B)) (πK w) =
          QuotientGroup.mk' (Subgroup.center (sec47Kz A Abar B)) (πK z) := hwe
      rw [hwe', inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hcomm := sec47_comm_le_of_sup_center WK hWK_comm
  set EK : Set (sec47Kz A Abar B) := πK '' {t : ↥(Sec45Z A Abar B) |
    (t : G) ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar)} with hEK
  have hEKgen : Subgroup.closure EK = ⊤ := by
    have hcl : (⊤ : Subgroup ↥(Sec45Z A Abar B)) ≤
        Subgroup.closure ({t : ↥(Sec45Z A Abar B) | (t : G) ∈ sec41g_D (Sec45Z A Abar B) A
          (Section3.A0 A Abar)} ∪ ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B) :
            Set ↥(Sec45Z A Abar B))) := fun y _ => sec46_gen h hS y
    have h1 := Subgroup.map_mono (f := πK) hcl
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective πK
      (QuotientGroup.mk'_surjective N)] at h1
    refine eq_top_iff.mpr (h1.trans ((Subgroup.closure_le _).mpr ?_))
    rintro _ ⟨t, (ht | hn), rfl⟩
    · exact Subgroup.subset_closure ⟨t, ht, rfl⟩
    · have h2 : πK t = 1 := (QuotientGroup.eq_one_iff t).mpr hn
      rw [h2]
      exact Subgroup.one_mem _
  have haW : πK αZ ∈ WK := Subgroup.mem_map_of_mem _ (Subgroup.subset_closure
    (show αZ ∈ Tz from Or.inr (Set.mem_insert _ _)))
  have hEKsub : ∀ e ∈ EK,
      ∃ c ∈ ⁅(⊤ : Subgroup (sec47Kz A Abar B)), (⊤ : Subgroup (sec47Kz A Abar B))⁆,
      e = πK αZ * c := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨g, hg, htg⟩ := sec47_E_conj h hα hαA₀ ht
    have e1 : t = (⟨g, hg⟩ : ↥(Sec45Z A Abar B)) * αZ * (⟨g, hg⟩ : ↥(Sec45Z A Abar B))⁻¹ :=
      Subtype.ext htg
    refine ⟨⁅(πK αZ)⁻¹, πK ⟨g, hg⟩⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _), ?_⟩
    rw [e1, map_mul, map_mul, map_inv]
    simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
    group
  have hWtop : WK = ⊤ :=
    sec47_eq_top_of_gen WK EK (πK αZ) hEKgen haW hEKsub hcomm
  refine ⟨γ, hγE, hγn, ?_⟩
  intro z hz
  have hzK : πK ⟨z, hz⟩ ∈ WK := by
    rw [hWtop]
    exact Subgroup.mem_top _
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hzK
  have hwQ : w⁻¹ * ⟨z, hz⟩ ∈ N := (QuotientGroup.eq).mp hwz
  have himg : (Sec45Z A Abar B).subtype '' Tz = T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hTsub x hx⟩, hx, rfl⟩
  have hwT : (w : G) ∈ Subgroup.closure T := by
    have hm := Subgroup.mem_map_of_mem (Sec45Z A Abar B).subtype hw
    rw [hW, MonoidHom.map_closure, himg] at hm
    exact hm
  have hz_eq : z = (w : G) * ((w⁻¹ * ⟨z, hz⟩ : ↥(Sec45Z A Abar B)) : G) := by
    simp
  rw [hz_eq]
  exact Subgroup.mul_mem_sup hwT (Subgroup.mem_subgroupOf.mp hwQ)
end

public section
open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G}

theorem sec47_twist_contra
    (h : Sec3Ctx A Abar S₀ B) (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {α : G} (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar)
    (hM : ⁅(⁅Sec45Z A Abar B, Sec45Z A Abar B⁆ ⊔ Sec45Q A Abar B),
        (⁅Sec45Z A Abar B, Sec45Z A Abar B⁆ ⊔ Sec45Q A Abar B)⁆ ⊔ Sec45Q A Abar B =
      ⁅Sec45Z A Abar B, Sec45Z A Abar B⁆ ⊔ Sec45Q A Abar B)
    (hZ' : ∀ u ∈ ⁅Sec45Z A Abar B, Sec45Z A Abar B⁆, ∀ q ∈ Sec45Q A Abar B,
      ⁅q, u⁆ ∈ Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G)) :
    False := by
  have hB1 : (1 : G) ∈ B := B.one_mem
  have hZQ : Sec45Q A Abar B ≤ Sec45Z A Abar B := sec46_Q_le_Z h
  have hQab : ∀ x ∈ Sec45Q A Abar B, ∀ y ∈ Sec45Q A Abar B, x * y = y * x :=
    fun x hx y hy => sec46_hNc h hS x hx y hy
  have htw := sec47_twist hQab hZQ (inf_le_left : Sec45Q A Abar B ⊓ _ ≤ Sec45Q A Abar B)
    (fun c hc z hz => by
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 z hz
      exact this.symm) hZ' hM
  have hAbne : Section3.Abar0 A Abar ≠ Abar := h.setup.Lb_ne
  obtain ⟨β, hβĀ, hβĀ₀⟩ : ∃ β ∈ Abar, β ∉ Section3.Abar0 A Abar := by
    by_contra hcon
    push_neg at hcon
    have h0 : Section3.Abar0 A Abar ≤ Abar := by
      rw [Sec3Ctx.abar0_eq h]
      exact inf_le_left
    exact hAbne (le_antisymm h0 (fun x hx => hcon x hx))
  have hββ : β * β = 1 := h.setup.sq_Ab hβĀ
  have hβ1 : β ≠ 1 := fun e => hβĀ₀ (e ▸ Subgroup.one_mem _)
  have hodd : Odd (orderOf (α * β)) := h.setup.odd_orderOf_mul hα hαA₀ hβĀ hβĀ₀
  have hαα : α * α = 1 := h.setup.sq_A hα
  obtain ⟨g, hgmem, hgβ⟩ := sec47_conj_of_odd hαα hββ hodd
  have hgZ : g ∈ Sec45Z A Abar B := by
    have hsub : Subgroup.closure ({α, β} : Set G) ≤ Sec45Z A Abar B := by
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      rcases hx with rfl | rfl
      · exact sec46_A_le_Z A Abar B hα
      · exact sec46_Abar_le_Z A Abar B hB1 hβĀ
    exact hsub hgmem
  have hαZ : α ∈ Sec45Z A Abar B := sec46_A_le_Z A Abar B hα
  have hmZ : ⁅g, α⁆ ∈ ⁅Sec45Z A Abar B, Sec45Z A Abar B⁆ :=
    Subgroup.commutator_mem_commutator hgZ hαZ
  have hmM : ⁅g, α⁆ ∈ ⁅Sec45Z A Abar B, Sec45Z A Abar B⁆ ⊔ Sec45Q A Abar B :=
    Subgroup.mem_sup_left hmZ
  have hβeq : ⁅g, α⁆ * α = β := by
    rw [← hgβ]
    simp only [commutatorElement_def]
    group
  obtain ⟨a₀, ha₀, ha₀1⟩ := sec32a_exists_mem_ne_one h.a0_ne_bot
  have ha₀Q : a₀ ∈ Sec45Q A Abar B := sec46_A0_le_Q A Abar B ha₀
  have hβa₀ : β * a₀ = a₀ * β := by
    have h1 : ⁅g, α⁆ * a₀ = a₀ * ⁅g, α⁆ := (htw _ hmM a₀ ha₀Q)
    have h2 : α * a₀ = a₀ * α := h.setup.comm_A hα (h.setup.L_le ha₀)
    calc β * a₀ = (⁅g, α⁆ * α) * a₀ := by rw [hβeq]
      _ = ⁅g, α⁆ * (α * a₀) := by rw [mul_assoc]
      _ = ⁅g, α⁆ * (a₀ * α) := by rw [h2]
      _ = (⁅g, α⁆ * a₀) * α := by rw [mul_assoc]
      _ = (a₀ * ⁅g, α⁆) * α := by rw [h1]
      _ = a₀ * (⁅g, α⁆ * α) := by rw [mul_assoc]
      _ = a₀ * β := by rw [hβeq]
  have hαa₀ : α * a₀ = a₀ * α := h.setup.comm_A hα (h.setup.L_le ha₀)
  have hαX : α ∈ A ⊔ Abar := Subgroup.mem_sup_left hα
  have hβX : β ∈ A ⊔ Abar := Subgroup.mem_sup_right hβĀ
  have hab : ∀ P : Sylow 2 ↥(A ⊔ Abar), ¬ ((⟨α, hαX⟩ : ↥(A ⊔ Abar)) ∈ P ∧
      (⟨β, hβX⟩ : ↥(A ⊔ Abar)) ∈ P) := by
    rintro P ⟨hαP, hβP⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP2 : IsPGroup 2 (P : Subgroup ↥(A ⊔ Abar)) := P.isPGroup'
    have hmul : (⟨α, hαX⟩ * ⟨β, hβX⟩ : ↥(A ⊔ Abar)) ∈ (P : Subgroup ↥(A ⊔ Abar)) :=
      Subgroup.mul_mem _ hαP hβP
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP2) ⟨_, hmul⟩
    have hinj : Function.Injective
        (((A ⊔ Abar).subtype).comp (P : Subgroup ↥(A ⊔ Abar)).subtype) :=
      fun x y hxy => Subtype.ext (Subtype.ext (by simpa using hxy))
    have e1 : orderOf (α * β) = orderOf (⟨_, hmul⟩ : ↥(P : Subgroup ↥(A ⊔ Abar))) := by
      have e0 := orderOf_injective _ hinj (⟨⟨α, hαX⟩ * ⟨β, hβX⟩, hmul⟩ :
        ↥(P : Subgroup ↥(A ⊔ Abar)))
      rw [← e0]
      rfl
    have e2 : orderOf (α * β) = 2 ^ k := by
      rw [e1, hk]
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
      have : Odd (2 ^ k) := by rw [← e2]; exact hodd
      exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h2)
    have hαβ1 : α * β = 1 := orderOf_eq_one_iff.mp (by rw [e2, hk0, pow_zero])
    have hβα : β = α := by
      have := eq_inv_of_mul_eq_one_right hαβ1
      rw [this, inv_eq_of_mul_eq_one_right hαα]
    have hαbot : α ∈ A ⊓ Abar := Subgroup.mem_inf.mpr ⟨hα, hβα ▸ hβĀ⟩
    rw [h.setup.inf_eq_bot, Subgroup.mem_bot] at hαbot
    exact hαA₀ (hαbot ▸ Subgroup.one_mem _)
  have hres := h.setup.tim77_2_4_three CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput hαX hβX hαα hββ hab
    (by rw [Sec3Ctx.m_eq h]; exact Subgroup.mem_sup_left ha₀)
    hαa₀ hβa₀
  exact ha₀1 hres

theorem sec47_Q_normalizes_N1 (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {h₀ : G}
    (hh₀ : h₀ ∈ Sec45Z A Abar B) :
    Sec45Q A Abar B ≤ normalizer ((sec47N1 A Abar B h₀ : Subgroup G) : Set G) := by
  intro q hq
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have hxQ := sec47_N1_le_Q h hS hh₀ hx
    rw [sec47_conj_eq_of_comm (sec46_hNc h hS q hq x hxQ)]
    exact hx
  · have hyQ := sec47_N1_le_Q h hS hh₀ hx
    have hcomm := sec46_hNc h hS (q⁻¹) ((Sec45Q A Abar B).inv_mem hq) _ hyQ
    have e : x = q⁻¹ * (q * x * q⁻¹) * q := by group
    rw [e, show q⁻¹ * (q * x * q⁻¹) * q = (q * x * q⁻¹) by
      calc q⁻¹ * (q * x * q⁻¹) * q = (q⁻¹ * (q * x * q⁻¹)) * q := rfl
        _ = ((q * x * q⁻¹) * q⁻¹) * q := by rw [hcomm]
        _ = q * x * q⁻¹ := by group]
    exact hx

theorem sec47_Q_le_N1_of_gen (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {α γ h₀ : G}
    (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar) (hαα : α * α = 1)
    (hh₀ : h₀ ∈ Sec45Z A Abar B) (hγ : γ ∈ conjSubgroup h₀ A) (hγγ : γ * γ = 1)
    (hgen : Sec45Z A Abar B ≤ Subgroup.closure ({e : G | e ∈ sec41g_D (Sec45Z A Abar B) A
      (Section3.A0 A Abar) ∧ e * α = α * e} ∪ {α, γ}) ⊔ Sec45Q A Abar B) :
    Sec45Q A Abar B ≤ sec47N1 A Abar B h₀ := by
  have hZN : Sec45Z A Abar B ≤ normalizer ((sec47N1 A Abar B h₀ : Subgroup G) : Set G) := by
    refine hgen.trans (sup_le ?_ (sec47_Q_normalizes_N1 h hS hh₀))
    refine (Subgroup.closure_le _).mpr ?_
    rintro g (⟨he, heα⟩ | hg)
    · obtain ⟨y, hy, hye, heA, hC⟩ := sec47_fam h hS hα hαA₀ he heα
      exact sec47_normalizes_fam h hS hh₀ hy hC hye heA (sec46_D_sq h he)
    · rcases hg with rfl | rfl
      · exact sec47_normalizes_alpha h hS hh₀ hα hαα
      · exact sec47_normalizes_gamma h hS hh₀ hγ hγγ
  exact sec47_Q_le_N1 h hS hZN

theorem sec47_mem_sup_of_comm {X Y Q : Subgroup G} (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hX : X ≤ Q) (hY : Y ≤ Q) {x : G} (hx : x ∈ X ⊔ Y) :
    ∃ a ∈ X, ∃ b ∈ Y, a * b = x := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ X, ∃ b ∈ Y, a * b = x}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, X.mul_mem ha₁ ha₂, b₁ * b₂, Y.mul_mem hb₁ hb₂, ?_⟩
        have hc : b₁ * a₂ = a₂ * b₁ := hQ _ (hY hb₁) _ (hX ha₂)
        calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
          _ = a₁ * (b₁ * a₂) * b₂ := by rw [← hc]
          _ = a₁ * b₁ * (a₂ * b₂) := by group
      one_mem' := ⟨1, X.one_mem, 1, Y.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, X.inv_mem ha, b⁻¹, Y.inv_mem hb, ?_⟩
        have hc : b * a = a * b := hQ _ (hY hb) _ (hX ha)
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [hc] }
  have hle : X ⊔ Y ≤ S := sup_le (fun a ha => ⟨a, ha, 1, Y.one_mem, by simp⟩)
    (fun b hb => ⟨1, X.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem sec47_conj_A0_normalizes (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {z h₀ : G}
    (hz : z ∈ Sec45Z A Abar B) (hh₀ : h₀ ∈ Sec45Z A Abar B) :
    conjSubgroup z (Section3.A0 A Abar) ≤ normalizer (conjSubgroup h₀ A : Set G) := by
  intro t ht
  by_cases hc : ∀ x ∈ conjSubgroup z A, ∀ v ∈ conjSubgroup h₀ A, x * v = v * x
  · have htA : t ∈ conjSubgroup z A := conjSubgroup_mono h.setup.L_le ht
    refine Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn => ?_, fun hn => ?_⟩
    · have hcomm := hc t htA n hn
      rw [show t * n * t⁻¹ = n by rw [hcomm]; group]
      exact hn
    · have hcomm := hc t htA (t * n * t⁻¹) hn
      have e2 : t⁻¹ * (t * n * t⁻¹) * t = t * n * t⁻¹ := by
        calc t⁻¹ * (t * n * t⁻¹) * t = t⁻¹ * ((t * n * t⁻¹) * t) := by group
          _ = t⁻¹ * (t * (t * n * t⁻¹)) := by rw [← hcomm]
          _ = t * n * t⁻¹ := by group
      have e : n = t⁻¹ * (t * n * t⁻¹) * t := by group
      rw [e, e2]
      exact hn
  · have hk := sec41g_key h (sec46_hAN h hS) (sec46_hNc h hS) hz hh₀ hc
    have : t ∈ conjSubgroup z A ⊓ normalizer (conjSubgroup h₀ A : Set G) := by
      rw [hk]
      exact ht
    exact (Subgroup.mem_inf.mp this).2

theorem sec47_Q_le_normalizer_conj (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {h₀ : G}
    (hh₀ : h₀ ∈ Sec45Z A Abar B) :
    Sec45Q A Abar B ≤ normalizer (conjSubgroup h₀ A : Set G) := by
  refine sec47_Q_le_of_conj h (fun z hz => sec47_conj_A0_normalizes h hS hz hh₀) ?_
  have := sec47_conj_A0_normalizes h hS (Subgroup.one_mem _) hh₀
  rwa [conjSubgroup_one] at this

theorem sec47_phi_mul {Q : Subgroup G} (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) {γ : G}
    (hγ : ∀ q ∈ Q, γ * q * γ⁻¹ ∈ Q) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) :
    (a * b) * γ * (a * b)⁻¹ * γ⁻¹ = (a * γ * a⁻¹ * γ⁻¹) * (b * γ * b⁻¹ * γ⁻¹) := by
  set β : G := b * γ * b⁻¹ * γ⁻¹ with hβdef
  have hβQ : β ∈ Q := by
    have : β = b * (γ * b⁻¹ * γ⁻¹) := by rw [hβdef]; group
    rw [this]
    exact Q.mul_mem hb (by
      have := hγ b⁻¹ (Q.inv_mem hb)
      simpa [mul_assoc] using this)
  have hαβ : a * β * a⁻¹ = β := hQ a ha β hβQ ▸ (by group)
  calc (a * b) * γ * (a * b)⁻¹ * γ⁻¹ = a * (b * γ * b⁻¹ * γ⁻¹) * γ * a⁻¹ * γ⁻¹ := by group
    _ = a * β * γ * a⁻¹ * γ⁻¹ := by rw [hβdef]
    _ = (a * β * a⁻¹) * (a * γ * a⁻¹ * γ⁻¹) := by group
    _ = β * (a * γ * a⁻¹ * γ⁻¹) := by rw [hαβ]
    _ = (a * γ * a⁻¹ * γ⁻¹) * β := by
      have hαγ : a * γ * a⁻¹ * γ⁻¹ ∈ Q := by
        have := hγ a⁻¹ (Q.inv_mem ha)
        have h2 : a * γ * a⁻¹ * γ⁻¹ = a * (γ * a⁻¹ * γ⁻¹) := by group
        rw [h2]
        exact Q.mul_mem ha (by simpa [mul_assoc] using this)
      exact (hQ _ hβQ _ hαγ)
    _ = (a * γ * a⁻¹ * γ⁻¹) * (b * γ * b⁻¹ * γ⁻¹) := by rw [hβdef]

theorem sec47P_le_centralizer_S (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {α : G}
    (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar) :
    sec47P A Abar B ≤ Subgroup.centralizer ({α} ∪ {e : G | e ∈ sec41g_D (Sec45Z A Abar B) A
        (Section3.A0 A Abar) ∧ e * α = α * e} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  rintro s (hs | ⟨hsE, hsα⟩)
  · rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact sec47P_comm_A h hS hα hx
  · obtain ⟨z, hz, hsA, -, hC⟩ := sec47_fam h hS hα hαA₀ hsE hsα
    exact sec47P_centralized_by h hS hz hC hsA x hx

theorem sec47_A0P_le_R (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {α : G}
    (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar) :
    Section3.A0 A Abar ⊔ sec47P A Abar B ≤
      Subgroup.centralizer ({α} ∪ {e : G | e ∈ sec41g_D (Sec45Z A Abar B) A
        (Section3.A0 A Abar) ∧ e * α = α * e} : Set G) := by
  refine sup_le ?_ (sec47P_le_centralizer_S h hS hα hαA₀)
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  rintro s (hs | ⟨hsE, hsα⟩)
  · rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact h.setup.comm_A hα (h.setup.L_le ha)
  · obtain ⟨y, hy, hys, -, hC⟩ := sec47_fam h hS hα hαA₀ hsE hsα
    exact (Subgroup.mem_centralizer_iff.mp (hC hys) a (h.setup.L_le ha)).symm

theorem sec47_Cz_eq (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {α γ : G}
    (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar) (hγ : γ ∈ Sec45Z A Abar B)
    (hgen : Sec45Z A Abar B ≤ Subgroup.closure ({e : G | e ∈ sec41g_D (Sec45Z A Abar B) A
      (Section3.A0 A Abar) ∧ e * α = α * e} ∪ {α, γ}) ⊔ Sec45Q A Abar B) :
    Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G) =
      (Sec45Q A Abar B ⊓ Subgroup.centralizer ({α} ∪ {e : G | e ∈ sec41g_D (Sec45Z A Abar B) A
        (Section3.A0 A Abar) ∧ e * α = α * e} : Set G)) ⊓
      (Sec45Q A Abar B ⊓ Subgroup.centralizer ({γ} : Set G)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxQ, hxZ⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxQ, ?_⟩, Subgroup.mem_inf.mpr ⟨hxQ, ?_⟩⟩
    · rw [Subgroup.mem_centralizer_iff]
      rintro s (hs | ⟨he, -⟩)
      · rw [Set.mem_singleton_iff] at hs
        rw [hs]
        exact Subgroup.mem_centralizer_iff.mp hxZ α (sec46_A_le_Z A Abar B hα)
      · exact Subgroup.mem_centralizer_iff.mp hxZ s (sec46_D_le_Z he)
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact Subgroup.mem_centralizer_iff.mp hxZ γ hγ
  · intro hx
    obtain ⟨hxR, hxH⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxQ, hxS⟩ := Subgroup.mem_inf.mp hxR
    obtain ⟨-, hxγ⟩ := Subgroup.mem_inf.mp hxH
    refine Subgroup.mem_inf.mpr ⟨hxQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hgenK : Subgroup.closure ({e : G | e ∈ sec41g_D (Sec45Z A Abar B) A
        (Section3.A0 A Abar) ∧ e * α = α * e} ∪ {α, γ}) ≤ Subgroup.centralizer ({x} : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro t (ht | ht)
      · have h1 := Subgroup.mem_centralizer_iff.mp hxS t (Or.inr ht)
        refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact h1.symm
      · rcases ht with rfl | rfl
        · have h1 := Subgroup.mem_centralizer_iff.mp hxS t (Or.inl rfl)
          refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact h1.symm
        · have h1 := Subgroup.mem_centralizer_iff.mp hxγ t rfl
          refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact h1.symm
    have hQK : Sec45Q A Abar B ≤ Subgroup.centralizer ({x} : Set G) := by
      intro q hq
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact sec46_hNc h hS x hxQ q hq
    have hzK := (sup_le hgenK hQK) (hgen hz)
    exact (Subgroup.mem_centralizer_iff.mp hzK x (Set.mem_singleton x)).symm

theorem sec47_R_index_le (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {α : G}
    (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar) {h₀ : G} (hh₀ : h₀ ∈ Sec45Z A Abar B)
    (hQN1 : Sec45Q A Abar B ≤ (Section3.A0 A Abar ⊔ sec47P A Abar B) ⊔
      conjSubgroup h₀ (Section3.A0 A Abar)) :
    (((Sec45Q A Abar B ⊓ Subgroup.centralizer ({α} ∪ {e : G | e ∈ sec41g_D
        (Sec45Z A Abar B) A (Section3.A0 A Abar) ∧ e * α = α * e} : Set G)).subgroupOf
        (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))).index ≤
      Nat.card (Section3.A0 A Abar) := by
  have hQab : ∀ x ∈ Sec45Q A Abar B, ∀ y ∈ Sec45Q A Abar B, x * y = y * x :=
    fun x hx y hy => sec46_hNc h hS x hx y hy
  set N : Subgroup ↥(Sec45Z A Abar B) := (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B) with hN
  set R : Subgroup G := Sec45Q A Abar B ⊓ Subgroup.centralizer ({α} ∪ {e : G | e ∈ sec41g_D
      (Sec45Z A Abar B) A (Section3.A0 A Abar) ∧ e * α = α * e} : Set G) with hR
  set X : Subgroup G := Section3.A0 A Abar ⊔ sec47P A Abar B with hX
  have hXQ : X ≤ Sec45Q A Abar B :=
    sup_le (sec46_A0_le_Q A Abar B) (sec47P_le_Q h hS)
  have hXR : X ≤ R := le_inf hXQ (sec47_A0P_le_R h hS hα hαA₀)
  set Y : Subgroup G := conjSubgroup h₀ (Section3.A0 A Abar) with hY
  have hYQ : Y ≤ Sec45Q A Abar B := sec46_hAN h hS h₀ hh₀
  set U : Subgroup ↥N := (X.subgroupOf (Sec45Z A Abar B)).subgroupOf N with hU
  set T : Subgroup ↥N := (Y.subgroupOf (Sec45Z A Abar B)).subgroupOf N with hT
  set RN : Subgroup ↥N := (R.subgroupOf (Sec45Z A Abar B)).subgroupOf N with hRN
  have hUR : U ≤ RN := by
    intro n hn
    rw [hU, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn
    rw [hRN, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hXR hn
  have hcomm : ∀ x y : ↥N, x * y = y * x := fun x y =>
    Subtype.ext (Subtype.ext (hQab _ (Subgroup.mem_subgroupOf.mp x.2) _
      (Subgroup.mem_subgroupOf.mp y.2)))
  have hUT : U ⊔ T = ⊤ := by
    refine eq_top_iff.mpr fun n _ => ?_
    have hnQ : (n : G) ∈ Sec45Q A Abar B := Subgroup.mem_subgroupOf.mp n.2
    have hnXY : (n : G) ∈ X ⊔ Y := hQN1 hnQ
    obtain ⟨a, ha, b, hb, hab⟩ := sec47_mem_sup_of_comm hQab hXQ hYQ hnXY
    have haZ : a ∈ Sec45Z A Abar B := sec46_Q_le_Z h (hXQ ha)
    have hbZ : b ∈ Sec45Z A Abar B := sec46_Q_le_Z h (hYQ hb)
    have hn_eq : n = (⟨⟨a, haZ⟩, Subgroup.mem_subgroupOf.mpr (hXQ ha)⟩ : ↥N) *
        ⟨⟨b, hbZ⟩, Subgroup.mem_subgroupOf.mpr (hYQ hb)⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hab.symm
    rw [hn_eq]
    refine Subgroup.mul_mem_sup ?_ ?_
    · rw [hU, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact ha
    · rw [hT, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hb
  have hU1 : U.index ≤ Nat.card T := sec47_index_le_card U T hcomm hUT
  have hUR' : RN.index ≤ U.index := Subgroup.index_antitone hUR
  have hTY : Nat.card T ≤ Nat.card Y := by
    refine Nat.card_le_card_of_injective
      (fun t : T => (⟨((t : ↥N) : G), Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp
        t.2)⟩ : ↥Y)) ?_
    intro t₁ t₂ ht
    have h1 := congrArg Subtype.val ht
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  have hYA : Nat.card Y = Nat.card (Section3.A0 A Abar) := card_conjSubgroup h₀ _
  calc RN.index ≤ U.index := hUR'
    _ ≤ Nat.card T := hU1
    _ ≤ Nat.card Y := hTY
    _ = Nat.card (Section3.A0 A Abar) := hYA

theorem sec47_H_index_le (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {γ h₀ : G}
    (hh₀ : h₀ ∈ Sec45Z A Abar B) (hγZ : γ ∈ Sec45Z A Abar B)
    (hγ : γ ∈ conjSubgroup h₀ A) :
    (((Sec45Q A Abar B ⊓ Subgroup.centralizer ({γ} : Set G)).subgroupOf
        (Sec45Z A Abar B)).subgroupOf
      ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))).index ≤ Nat.card (Section3.A0 A Abar) := by
  have hQab : ∀ x ∈ Sec45Q A Abar B, ∀ y ∈ Sec45Q A Abar B, x * y = y * x :=
    fun x hx y hy => sec46_hNc h hS x hx y hy
  have hγQ : ∀ q ∈ Sec45Q A Abar B, γ * q * γ⁻¹ ∈ Sec45Q A Abar B := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp (sec46_Z_le_normalizer_Q h hS hγZ) q).mp hq
  have hQN : ∀ n : ↥((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)),
      ((n : ↥(Sec45Z A Abar B)) : G) ∈ Sec45Q A Abar B :=
    fun n => Subgroup.mem_subgroupOf.mp n.2
  let φ : ↥((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) →* G :=
    MonoidHom.mk' (fun n => ((n : ↥(Sec45Z A Abar B)) : G) * γ *
      ((n : ↥(Sec45Z A Abar B)) : G)⁻¹ * γ⁻¹) (by
        intro a b
        have hm : (((a * b : ↥((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))) :
            ↥(Sec45Z A Abar B)) : G) = ((a : ↥(Sec45Z A Abar B)) : G) *
            ((b : ↥(Sec45Z A Abar B)) : G) := by
          simp only [Subgroup.coe_mul]
        simp only [hm]
        exact sec47_phi_mul hQab hγQ (hQN a) (hQN b))
  have hφ : ∀ n, φ n = ((n : ↥(Sec45Z A Abar B)) : G) * γ *
      ((n : ↥(Sec45Z A Abar B)) : G)⁻¹ * γ⁻¹ := fun n => rfl
  have hmemH : ∀ n : ↥((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)),
      n ∈ ((Sec45Q A Abar B ⊓ Subgroup.centralizer ({γ} : Set G)).subgroupOf
        (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) ↔
      γ * ((n : ↥(Sec45Z A Abar B)) : G) = ((n : ↥(Sec45Z A Abar B)) : G) * γ := by
    intro n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, hc⟩
      exact hc γ (Set.mem_singleton γ)
    · intro hc
      refine ⟨hQN n, fun t ht => ?_⟩
      rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact hc
  have hφker : ∀ n : ↥((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)),
      φ n = 1 ↔ γ * ((n : ↥(Sec45Z A Abar B)) : G) = ((n : ↥(Sec45Z A Abar B)) : G) * γ := by
    intro n
    rw [hφ]
    show ⁅((n : ↥(Sec45Z A Abar B)) : G), γ⁆ = 1 ↔ _
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ⟨fun h1 => h1.symm, fun h1 => h1.symm⟩
  have hker : ((Sec45Q A Abar B ⊓ Subgroup.centralizer ({γ} : Set G)).subgroupOf
      (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) = φ.ker := by
    ext n
    rw [MonoidHom.mem_ker, hφker, hmemH]
  have hrange : φ.range ≤ conjSubgroup h₀ (Section3.A0 A Abar) := by
    rintro _ ⟨n, rfl⟩
    have hx := sec47_Q_le_normalizer_conj h hS hh₀ (hQN n)
    have hφn : φ n = (((n : ↥(Sec45Z A Abar B)) : G) * γ * ((n : ↥(Sec45Z A Abar B)) : G)⁻¹) *
        γ⁻¹ := by rw [hφ]
    have hA : φ n ∈ conjSubgroup h₀ A := by
      rw [hφn]
      refine (conjSubgroup h₀ A).mul_mem ?_ ((conjSubgroup h₀ A).inv_mem hγ)
      exact (Subgroup.mem_normalizer_iff.mp hx γ).mp hγ
    have hQ : φ n ∈ Sec45Q A Abar B := by
      rw [hφ]
      have e1 : ((n : ↥(Sec45Z A Abar B)) : G) * γ * ((n : ↥(Sec45Z A Abar B)) : G)⁻¹ * γ⁻¹ =
          ((n : ↥(Sec45Z A Abar B)) : G) * (γ * ((n : ↥(Sec45Z A Abar B)) : G)⁻¹ * γ⁻¹) := by
        simp only [mul_assoc]
      rw [e1]
      exact (Sec45Q A Abar B).mul_mem (hQN n) (hγQ _ ((Sec45Q A Abar B).inv_mem (hQN n)))
    exact sec47_inter_Q h hS hh₀ hA hQ
  rw [hker, Subgroup.index_ker]
  calc Nat.card φ.range ≤ Nat.card (conjSubgroup h₀ (Section3.A0 A Abar) : Subgroup G) :=
        Subgroup.card_le_of_le hrange
    _ = Nat.card (Section3.A0 A Abar) := card_conjSubgroup h₀ _

theorem sec47_index_inf_le {Γ : Type} [Group Γ] [Finite Γ] (R K : Subgroup Γ) (a : ℕ)
    (hR : R.index ≤ a) (hK : K.index ≤ a) : Nat.card (Γ ⧸ (R ⊓ K)) ≤ a ^ 2 := by
  change (R ⊓ K).index ≤ a ^ 2
  calc (R ⊓ K).index ≤ R.index * K.index := Subgroup.index_inf_le
    _ ≤ a * a := Nat.mul_le_mul hR hK
    _ = a ^ 2 := (pow_two a).symm

theorem sec47_index_V (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {α γ h₀ : G}
    (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar) (hh₀ : h₀ ∈ Sec45Z A Abar B)
    (hγZ : γ ∈ Sec45Z A Abar B) (hγ : γ ∈ conjSubgroup h₀ A)
    (hgen : Sec45Z A Abar B ≤ Subgroup.closure ({e : G | e ∈ sec41g_D (Sec45Z A Abar B) A
      (Section3.A0 A Abar) ∧ e * α = α * e} ∪ {α, γ}) ⊔ Sec45Q A Abar B)
    (hQN1 : Sec45Q A Abar B ≤ (Section3.A0 A Abar ⊔ sec47P A Abar B) ⊔
      conjSubgroup h₀ (Section3.A0 A Abar)) :
    Nat.card (↥((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) ⧸
      (((Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G)).subgroupOf
        (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)))) ≤
      Nat.card (Section3.A0 A Abar) ^ 2 := by
  rw [sec47_Cz_eq h hS hα hαA₀ hγZ hgen]
  have hD : (((Sec45Q A Abar B ⊓ Subgroup.centralizer ({α} ∪ {e : G | e ∈ sec41g_D
      (Sec45Z A Abar B) A (Section3.A0 A Abar) ∧ e * α = α * e} : Set G)) ⊓
      (Sec45Q A Abar B ⊓ Subgroup.centralizer ({γ} : Set G))).subgroupOf
      (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) =
      (((Sec45Q A Abar B ⊓ Subgroup.centralizer ({α} ∪ {e : G | e ∈ sec41g_D
        (Sec45Z A Abar B) A (Section3.A0 A Abar) ∧ e * α = α * e} : Set G)).subgroupOf
        (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))) ⊓
      (((Sec45Q A Abar B ⊓ Subgroup.centralizer ({γ} : Set G)).subgroupOf
        (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))) := by
    ext n
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [hD]
  exact sec47_index_inf_le _ _ _ (sec47_R_index_le h hS hα hαA₀ hh₀ hQN1)
    (sec47_H_index_le h hS hh₀ hγZ hγ)

theorem sec47_commutator_le_of_central {K : Type} [Group K] (W : Subgroup K)
    (h : ∀ k : K, ∃ w ∈ W, w⁻¹ * k ∈ Subgroup.center K) :
    ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ ⁅W, W⁆ := by
  refine Subgroup.commutator_le.mpr fun k1 _ k2 _ => ?_
  obtain ⟨w1, hw1, hc1⟩ := h k1
  obtain ⟨w2, hw2, hc2⟩ := h k2
  set c1 := w1⁻¹ * k1 with hc1def
  set c2 := w2⁻¹ * k2 with hc2def
  have hk1 : k1 = w1 * c1 := by rw [hc1def]; group
  have hk2 : k2 = w2 * c2 := by rw [hc2def]; group
  rw [hk1, hk2, sec47_commutatorElement_mul_mul_central hc1 hc2]
  exact Subgroup.commutator_mem_commutator hw1 hw2

theorem sec47_M_perf [hN : ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal]
    (h : Sec3Ctx A Abar S₀ B) (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    (hperf : Group.IsPerfect (sec47Lz A Abar B)) :
    ⁅(⁅Sec45Z A Abar B, Sec45Z A Abar B⁆ ⊔ Sec45Q A Abar B),
      (⁅Sec45Z A Abar B, Sec45Z A Abar B⁆ ⊔ Sec45Q A Abar B)⁆ ⊔ Sec45Q A Abar B =
    ⁅Sec45Z A Abar B, Sec45Z A Abar B⁆ ⊔ Sec45Q A Abar B := by
  set Z := Sec45Z A Abar B with hZ
  set Q := Sec45Q A Abar B with hQ
  set N : Subgroup ↥Z := Q.subgroupOf Z with hN'
  set M : Subgroup G := ⁅Z, Z⁆ ⊔ Q with hM
  have hQZ : Q ≤ Z := sec46_Q_le_Z h
  have hZZ : ⁅Z, Z⁆ ≤ Z := Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ =>
    Z.mul_mem (Z.mul_mem (Z.mul_mem hg₁ hg₂) (Z.inv_mem hg₁)) (Z.inv_mem hg₂)
  have hMZ : M ≤ Z := sup_le hZZ hQZ
  have hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun x hx y hy => sec46_hNc h hS x hx y hy
  have hMM : ⁅M, M⁆ ⊔ Q ≤ M := sup_le (Subgroup.commutator_le.mpr fun x hx y hy =>
    M.mul_mem (M.mul_mem (M.mul_mem hx hy) (M.inv_mem hx)) (M.inv_mem hy)) le_sup_right
  apply le_antisymm hMM
  let π : ↥Z →* sec47Kz A Abar B := QuotientGroup.mk' N
  let πL : sec47Kz A Abar B →* sec47Lz A Abar B := QuotientGroup.mk' (Subgroup.center _)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hπL : Function.Surjective πL := QuotientGroup.mk'_surjective _
  have hπN : ∀ n ∈ N, π n = 1 := fun n hn => (QuotientGroup.eq_one_iff n).mpr hn
  have htop : (⊤ : Subgroup ↥Z).map Z.subtype = Z := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hCZ : (⁅(⊤ : Subgroup ↥Z), (⊤ : Subgroup ↥Z)⁆).map Z.subtype = ⁅Z, Z⁆ := by
    rw [Subgroup.map_commutator, htop]
  have hNmap : N.map Z.subtype = Q := by
    rw [hN', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQZ]
  have hMap : (⁅(⊤ : Subgroup ↥Z), (⊤ : Subgroup ↥Z)⁆ ⊔ N).map Z.subtype = M := by
    rw [Subgroup.map_sup, hCZ, hNmap]
  have hA : (⁅(⊤ : Subgroup ↥Z), (⊤ : Subgroup ↥Z)⁆).map π =
      ⁅(⊤ : Subgroup (sec47Kz A Abar B)), (⊤ : Subgroup (sec47Kz A Abar B))⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ]
  set Mz : Subgroup ↥Z := M.subgroupOf Z with hMz
  have hCZM : ⁅(⊤ : Subgroup ↥Z), (⊤ : Subgroup ↥Z)⁆ ≤ Mz := by
    intro x hx
    rw [hMz, Subgroup.mem_subgroupOf]
    have hxm : (x : G) ∈ (⁅(⊤ : Subgroup ↥Z), (⊤ : Subgroup ↥Z)⁆).map Z.subtype :=
      Subgroup.mem_map_of_mem _ hx
    rw [hCZ] at hxm
    exact (le_sup_left : ⁅Z, Z⁆ ≤ M) hxm
  have hMzle : Mz ≤ ⁅(⊤ : Subgroup ↥Z), (⊤ : Subgroup ↥Z)⁆ ⊔ N := by
    intro x hx
    rw [hMz, Subgroup.mem_subgroupOf] at hx
    have hx' : Z.subtype x ∈ (⁅(⊤ : Subgroup ↥Z), (⊤ : Subgroup ↥Z)⁆ ⊔ N).map Z.subtype := by
      rw [hMap]
      exact hx
    exact (Subgroup.mem_map_iff_mem Z.subtype_injective).mp hx'
  have hNbot : N.map π = ⊥ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hπN x hx, Subgroup.mem_bot]
    · intro hy
      rw [Subgroup.mem_bot] at hy
      exact ⟨1, Subgroup.one_mem _, by rw [map_one, hy]⟩
  have hB : Mz.map π = ⁅(⊤ : Subgroup (sec47Kz A Abar B)), (⊤ : Subgroup (sec47Kz A Abar B))⁆ := by
    apply le_antisymm
    · calc Mz.map π ≤ (⁅(⊤ : Subgroup ↥Z), (⊤ : Subgroup ↥Z)⁆ ⊔ N).map π :=
            Subgroup.map_mono hMzle
        _ = (⁅(⊤ : Subgroup ↥Z), (⊤ : Subgroup ↥Z)⁆).map π ⊔ N.map π := Subgroup.map_sup _ _ _
        _ = ⁅(⊤ : Subgroup (sec47Kz A Abar B)), (⊤ : Subgroup (sec47Kz A Abar B))⁆ := by
            rw [hA, hNbot]
            exact sup_bot_eq _
    · rw [← hA]
      exact Subgroup.map_mono hCZM
  have hWc : ∀ k : sec47Kz A Abar B, ∃ w ∈ Mz.map π,
      w⁻¹ * k ∈ Subgroup.center (sec47Kz A Abar B) := by
    intro k
    have htopL : (⁅(⊤ : Subgroup (sec47Kz A Abar B)), (⊤ : Subgroup (sec47Kz A Abar B))⁆).map
        πL = ⊤ := by
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective πL hπL]
      exact hperf.commutator_eq_top
    obtain ⟨c, hc, hcπ⟩ := Subgroup.mem_map.mp (htopL ▸ Subgroup.mem_top (πL k))
    refine ⟨c, hB ▸ hc, ?_⟩
    have h1 : πL (c⁻¹ * k) = 1 := by rw [map_mul, map_inv, hcπ, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hWW : Mz.map π ≤ ⁅Mz.map π, Mz.map π⁆ := by
    have h2 := sec47_commutator_le_of_central (Mz.map π) hWc
    rw [hB] at h2 ⊢
    exact h2
  have hcomm_map : ⁅Mz.map π, Mz.map π⁆ = (⁅Mz, Mz⁆).map π := (Subgroup.map_commutator _ _ _).symm
  have hMzG : Mz.map Z.subtype = M := by
    rw [hMz, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMZ]
  intro m hm
  let mz : ↥Z := ⟨m, hMZ hm⟩
  have hmz : mz ∈ Mz := by
    rw [hMz, Subgroup.mem_subgroupOf]
    exact hm
  have hπm : π mz ∈ ⁅Mz.map π, Mz.map π⁆ := hWW (Subgroup.mem_map_of_mem _ hmz)
  rw [hcomm_map] at hπm
  obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp hπm
  have hxN : x⁻¹ * mz ∈ N := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    show π (x⁻¹ * mz) = 1
    rw [map_mul, map_inv, hxπ, inv_mul_cancel]
  have hxG : (x : G) ∈ ⁅M, M⁆ := by
    have h3 : Z.subtype x ∈ (⁅Mz, Mz⁆).map Z.subtype := Subgroup.mem_map_of_mem _ hx
    rw [Subgroup.map_commutator, hMzG] at h3
    exact h3
  have hQm : (x : G)⁻¹ * m ∈ Q := by
    have h4 := Subgroup.mem_subgroupOf.mp hxN
    simpa using h4
  have hm_eq : m = (x : G) * ((x : G)⁻¹ * m) := by group
  rw [hm_eq]
  exact Subgroup.mul_mem_sup hxG hQm

theorem sec47_comm_of_act (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    [hN : ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal]
    [hC : ((((Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G)).subgroupOf
          (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)))).Normal]
    (ρ : (↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) →*
      MulAut (↥((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) ⧸
        (((Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G)).subgroupOf
          (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)))))
    (hρ : ∀ (x : ↥(Sec45Z A Abar B)) (n : ↥((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))),
      ρ (QuotientGroup.mk x) (QuotientGroup.mk n) = QuotientGroup.mk
        ⟨x * n * x⁻¹, Subgroup.Normal.conj_mem inferInstance (n : ↥(Sec45Z A Abar B)) n.2 x⟩)
    (hnt : ∀ y ∈ commutator (↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf
      (Sec45Z A Abar B)), ρ y = 1) :
    ∀ u ∈ ⁅Sec45Z A Abar B, Sec45Z A Abar B⁆, ∀ q ∈ Sec45Q A Abar B,
      ⁅q, u⁆ ∈ Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G) := by
  intro u hu q hq
  have hqZ : q ∈ Sec45Z A Abar B := sec46_Q_le_Z h hq
  have htop : (⊤ : Subgroup ↥(Sec45Z A Abar B)).map (Sec45Z A Abar B).subtype =
      Sec45Z A Abar B := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hCZ : (⁅(⊤ : Subgroup ↥(Sec45Z A Abar B)), (⊤ : Subgroup ↥(Sec45Z A Abar B))⁆).map
      (Sec45Z A Abar B).subtype = ⁅Sec45Z A Abar B, Sec45Z A Abar B⁆ := by
    rw [Subgroup.map_commutator, htop]
  have hu' : u ∈ (⁅(⊤ : Subgroup ↥(Sec45Z A Abar B)), (⊤ : Subgroup ↥(Sec45Z A Abar B))⁆).map
      (Sec45Z A Abar B).subtype := by
    rw [hCZ]
    exact hu
  obtain ⟨x, hx, hxu⟩ := Subgroup.mem_map.mp hu'
  have hcomm : (QuotientGroup.mk x : ↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf
      (Sec45Z A Abar B)) ∈ commutator (↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf
      (Sec45Z A Abar B)) := by
    have e1 : (commutator (↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf
        (Sec45Z A Abar B))) =
        (⁅(⊤ : Subgroup ↥(Sec45Z A Abar B)), (⊤ : Subgroup ↥(Sec45Z A Abar B))⁆).map
        (QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))) := by
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective _)]
      rfl
    rw [e1]
    exact Subgroup.mem_map_of_mem _ hx
  have hact := hnt _ hcomm
  set n : ↥((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) :=
    ⟨⟨q, hqZ⟩, Subgroup.mem_subgroupOf.mpr hq⟩ with hn
  have h1 : ρ (QuotientGroup.mk x) (QuotientGroup.mk n) = QuotientGroup.mk n := by
    rw [hact]
    rfl
  rw [hρ x n] at h1
  have h2 := QuotientGroup.eq.mp h1
  have h3 := Subgroup.mem_subgroupOf.mp h2
  have h4 := Subgroup.mem_subgroupOf.mp h3
  have hc : ((((x : ↥(Sec45Z A Abar B)) : G) * q * ((x : ↥(Sec45Z A Abar B)) : G)⁻¹)⁻¹ * q) ∈
      Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G) := by
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, hn] using h4
  have hqc : q * ((((x : ↥(Sec45Z A Abar B)) : G) * q * ((x : ↥(Sec45Z A Abar B)) : G)⁻¹)⁻¹ * q) *
      q⁻¹ = ⁅q, ((x : ↥(Sec45Z A Abar B)) : G)⁆ := by
    simp only [commutatorElement_def]
    group
  have hcq : q * ((((x : ↥(Sec45Z A Abar B)) : G) * q * ((x : ↥(Sec45Z A Abar B)) : G)⁻¹)⁻¹ * q) =
      ((((x : ↥(Sec45Z A Abar B)) : G) * q * ((x : ↥(Sec45Z A Abar B)) : G)⁻¹)⁻¹ * q) * q :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 q hqZ
  rw [← hxu]
  show ⁅q, ((x : ↥(Sec45Z A Abar B)) : G)⁆ ∈ _
  rw [← hqc, hcq, mul_assoc, mul_inv_cancel, mul_one]
  exact hc

theorem sec47_card_two_pow {V : Type} [Group V] [Finite V]
    (hV : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup V)) : ∃ d : ℕ, Nat.card V = 2 ^ d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 V := IsPGroup.iff_orderOf.mpr fun g => by
    have hg : g ^ 2 = 1 := hV.2 g (Subgroup.mem_top g)
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hg) with h1 | h1
    · exact ⟨0, by rw [h1]; simp⟩
    · exact ⟨1, by rw [h1]; simp⟩
  exact IsPGroup.iff_card.mp hp

theorem sec47_hnt_of_act
    (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    [hN : ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal]
    [hC : ((((Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G)).subgroupOf
          (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)))).Normal]
    {α : G} (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar)
    (hperf : Group.IsPerfect (sec47Lz A Abar B))
    (ρ : (↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) →*
      MulAut (↥((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) ⧸
        (((Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G)).subgroupOf
          (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)))))
    (hρ : ∀ (x : ↥(Sec45Z A Abar B)) (n : ↥((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))),
      ρ (QuotientGroup.mk x) (QuotientGroup.mk n) = QuotientGroup.mk
        ⟨x * n * x⁻¹, Subgroup.Normal.conj_mem inferInstance (n : ↥(Sec45Z A Abar B)) n.2 x⟩) :
    ∃ y ∈ commutator (↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)),
      ρ y ≠ 1 := by
  by_contra hcon
  push_neg at hcon
  exact sec47_twist_contra h hS hα hαA₀ (sec47_M_perf h hS hperf)
    (sec47_comm_of_act h hS ρ hρ hcon)

theorem sec47_conj_Q_le (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {b : G} (hb : b ∈ B) :
    Sec45Q A Abar B ≤ (Sec45Q A Abar B).comap (MulAut.conj b).toMonoidHom := by
  have hB1 : (1 : G) ∈ B := B.one_mem
  refine sup_le (fun t ht => ?_) (iSup₂_le fun b' hb' => fun t ht => ?_)
  · rw [Subgroup.mem_comap]
    show b * t * b⁻¹ ∈ Sec45Q A Abar B
    rw [sec46_conj_fix h hb (h.setup.L_le ht)]
    exact sec46_A0_le_Q A Abar B ht
  · rw [Subgroup.mem_comap]
    show b * t * b⁻¹ ∈ Sec45Q A Abar B
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ Section3.Abar0 A Abar, t = b' * y * b'⁻¹ :=
      ⟨b'⁻¹ * t * b', mem_conjSubgroup.mp ht, by group⟩
    have := sec46_conj_mem_Q (A := A) (Abar := Abar) (B := B) (B.mul_mem hb hb') hy
    rwa [show b * (b' * y * b'⁻¹) * b⁻¹ = (b * b') * y * (b * b')⁻¹ by group]

def sec47CZ (h : Sec3Ctx A Abar S₀ B) (b : ↥B) :
    ↥(Sec45Z A Abar B) ≃* ↥(Sec45Z A Abar B) where
  toFun z := ⟨(b : G) * z * (b : G)⁻¹, sec46_conj_mem_Z h b.2 z.2⟩
  invFun z := ⟨(b : G)⁻¹ * z * (b : G), by
    have := sec46_conj_mem_Z h (B.inv_mem b.2) z.2
    simpa using this⟩
  left_inv z := Subtype.ext (by
    show (b : G)⁻¹ * ((b : G) * z * (b : G)⁻¹) * (b : G) = z
    group)
  right_inv z := Subtype.ext (by
    show (b : G) * ((b : G)⁻¹ * z * (b : G)) * (b : G)⁻¹ = z
    group)
  map_mul' z w := Subtype.ext (by
    show (b : G) * ((z : G) * (w : G)) * (b : G)⁻¹ =
      ((b : G) * z * (b : G)⁻¹) * ((b : G) * w * (b : G)⁻¹)
    group)

def sec47Phi (h : Sec3Ctx A Abar S₀ B) : ↥B →* MulAut ↥(Sec45Z A Abar B) :=
  MonoidHom.mk' (fun b => sec47CZ h b) (fun a b => MulEquiv.ext fun z => Subtype.ext (by
    show ((a : G) * (b : G)) * (z : G) * ((a : G) * (b : G))⁻¹ =
      (a : G) * ((b : G) * (z : G) * (b : G)⁻¹) * (a : G)⁻¹
    group))

theorem sec47_E_conj_B (h : Sec3Ctx A Abar S₀ B) {b e : G} (hb : b ∈ B)
    (he : e ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar)) :
    b * e * b⁻¹ ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) := by
  obtain ⟨y, hy, a, ha, haA₀, rfl⟩ := sec41g_mem_D.mp he
  refine sec41g_mem_D.mpr ⟨b * y * b⁻¹, sec46_conj_mem_Z h hb hy, a, ha, haA₀, ?_⟩
  have hba : b * a * b⁻¹ = a := sec46_conj_fix h hb ha
  calc b * (y * a * y⁻¹) * b⁻¹ = (b * y * b⁻¹) * (b * a * b⁻¹) * (b * y * b⁻¹)⁻¹ := by group
    _ = (b * y * b⁻¹) * a * (b * y * b⁻¹)⁻¹ := by rw [hba]

theorem sec47_aut_center {K : Type} [Group K] (e : MulAut K) (k : K)
    (hk : k ∈ Subgroup.center K) : e k ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g', rfl⟩ := e.surjective g
  have hk' : ∀ y : K, y * k = k * y := fun y => Subgroup.mem_center_iff.mp hk y
  have := congrArg e (hk' g')
  simp only [map_mul] at this
  exact this

theorem sec47_top_elemAbelian {G : Type} [Group G] {H : Subgroup G}
    (hH : CFSG.Open.IsElemAbelian 2 H) : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup ↥H) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (hH.1.is_comm.comm x.1 y.1)⟩⟩, ?_⟩
  intro x _
  apply Subtype.ext
  simpa using hH.2 x.1 x.2

theorem sec47_C2 (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {x : G} (hxA : x ∈ Section3.Abar0 A Abar) (hxB : x ∉ normalizer (B : Set G))
    {b : G} (hb : b ∈ B)
    (hyp : ∀ w ∈ Sec45Z A Abar B, (b * w * b⁻¹)⁻¹ * w ∈ Sec45Q A Abar B) : b = 1 := by
  by_contra hb1
  have hQab : ∀ x ∈ Sec45Q A Abar B, ∀ y ∈ Sec45Q A Abar B, x * y = y * x :=
    fun x hx y hy => sec46_hNc h hS x hx y hy
  have hkey : ∀ z ∈ Sec45Z A Abar B, ∀ a ∈ Section3.A0 A Abar,
      b * (z * a * z⁻¹) * b⁻¹ = z * a * z⁻¹ := by
    intro z hz a ha
    have hqQ : (b * z * b⁻¹)⁻¹ * z ∈ Sec45Q A Abar B := hyp z hz
    set q := (b * z * b⁻¹)⁻¹ * z with hq
    have hbz : b * z * b⁻¹ = z * q⁻¹ := by
      rw [hq]
      group
    have hba : b * a * b⁻¹ = a := sec46_conj_fix h hb (h.setup.L_le ha)
    have haQ : a ∈ Sec45Q A Abar B := sec46_A0_le_Q A Abar B ha
    have hqa : q⁻¹ * a * q = a := by
      have hc := hQab q hqQ a haQ
      calc q⁻¹ * a * q = q⁻¹ * (a * q) := by group
        _ = q⁻¹ * (q * a) := by rw [← hc]
        _ = a := by group
    calc b * (z * a * z⁻¹) * b⁻¹ = (b * z * b⁻¹) * (b * a * b⁻¹) * (b * z * b⁻¹)⁻¹ := by group
      _ = (z * q⁻¹) * a * (z * q⁻¹)⁻¹ := by rw [hbz, hba]
      _ = z * (q⁻¹ * a * q) * z⁻¹ := by group
      _ = z * a * z⁻¹ := by rw [hqa]
  have hcent : ∀ z ∈ Sec45Z A Abar B, conjSubgroup z (Section3.A0 A Abar) ≤
      Subgroup.centralizer ({b} : Set G) := by
    intro z hz t ht
    obtain ⟨a, ha, rfl⟩ : ∃ a ∈ Section3.A0 A Abar, t = z * a * z⁻¹ :=
      ⟨z⁻¹ * t * z, mem_conjSubgroup.mp ht, by group⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    have := hkey z hz a ha
    calc b * (z * a * z⁻¹) = (b * (z * a * z⁻¹) * b⁻¹) * b := by group
      _ = (z * a * z⁻¹) * b := by rw [this]
  have hQc : Sec45Q A Abar B ≤ Subgroup.centralizer ({b} : Set G) :=
    sec47_Q_le_of_conj h hcent (by simpa [conjSubgroup_one] using hcent 1 (Subgroup.one_mem _))
  have hx' : x ∈ Sec45Q A Abar B := sec46_Abar0_le_Q A Abar B B.one_mem hxA
  have hbx : b * x = x * b := by
    have := Subgroup.mem_centralizer_iff.mp (hQc hx') b (Set.mem_singleton b)
    exact this
  exact hxB (mem_normalizer_of_commute_of_isTI (sec46_B_ti h) hb hb1 hbx.symm)

theorem sec47_sigma_inj
    [hN : ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal]
    (h : Sec3Ctx A Abar S₀ B) (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {x : G} (hxA : x ∈ Section3.Abar0 A Abar) (hxB : x ∉ normalizer (B : Set G)) :
    ∃ σ : ↥B →* MulAut (sec47Lz A Abar B), Function.Injective σ := by
  have hY1 : ∀ b : ↥B, ∀ y ∈ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B),
      sec47Phi h b y ∈ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B) := by
    intro b y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact Subgroup.mem_comap.mp (sec47_conj_Q_le h hS b.2 hy)
  obtain ⟨σ₁, hσ₁⟩ := sec47_quot_hom ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))
    (sec47Phi h) hY1
  have hY2 : ∀ b : ↥B, ∀ k ∈ Subgroup.center (sec47Kz A Abar B),
      σ₁ b k ∈ Subgroup.center (sec47Kz A Abar B) :=
    fun b k hk => sec47_aut_center (σ₁ b) k hk
  obtain ⟨σ₂, hσ₂⟩ := sec47_quot_hom (Subgroup.center (sec47Kz A Abar B)) σ₁ hY2
  refine ⟨σ₂, ?_⟩
  rw [injective_iff_map_eq_one]
  rintro ⟨b, hb⟩ hb1
  have hσ₁e : ∀ w : ↥(Sec45Z A Abar B), σ₁ ⟨b, hb⟩ (QuotientGroup.mk w) =
      QuotientGroup.mk (⟨b * (w : G) * b⁻¹, sec46_conj_mem_Z h hb w.2⟩ :
        ↥(Sec45Z A Abar B)) :=
    fun w => hσ₁ ⟨b, hb⟩ w
  have hsec := sec46_sec42Data h hS (sec46_single h) (sec46_O2 h hS)
  have hfixD : ∀ e : ↥(Sec45Z A Abar B), (e : G) ∈ sec41g_D (Sec45Z A Abar B) A
      (Section3.A0 A Abar) → σ₁ ⟨b, hb⟩ (QuotientGroup.mk e) = QuotientGroup.mk e := by
    intro e he
    have hdD : (QuotientGroup.mk e : sec47Kz A Abar B) ∈
        QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) ''
          {t : ↥(Sec45Z A Abar B) | (t : G) ∈ sec41g_D (Sec45Z A Abar B) A
            (Section3.A0 A Abar)} :=
      ⟨e, he, rfl⟩
    have hmemD : σ₁ ⟨b, hb⟩ (QuotientGroup.mk e) ∈
        QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) ''
          {t : ↥(Sec45Z A Abar B) | (t : G) ∈ sec41g_D (Sec45Z A Abar B) A
            (Section3.A0 A Abar)} :=
      ⟨⟨b * (e : G) * b⁻¹, sec46_conj_mem_Z h hb e.2⟩, sec47_E_conj_B h hb he,
        (hσ₁e e).symm⟩
    have hk : ∀ k : sec47Kz A Abar B,
        k⁻¹ * σ₁ ⟨b, hb⟩ k ∈ Subgroup.center (sec47Kz A Abar B) := by
      intro k
      have hk1 : QuotientGroup.mk (σ₁ ⟨b, hb⟩ k) = (QuotientGroup.mk k : sec47Lz A Abar B) := by
        rw [← hσ₂ ⟨b, hb⟩ k, hb1, MulAut.one_apply]
      exact QuotientGroup.eq.mp hk1.symm
    have hz := hk (QuotientGroup.mk e)
    by_contra hne
    apply qp_inj hsec hdD hz (fun h1 => hne (inv_mul_eq_one.mp h1).symm)
    rw [mul_inv_cancel_left]
    exact hmemD
  have hfixD' : ∀ d ∈ QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) ''
      {t : ↥(Sec45Z A Abar B) | (t : G) ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar)},
      σ₁ ⟨b, hb⟩ d = d := by
    rintro _ ⟨e, he, rfl⟩
    exact hfixD e he
  have hone : σ₁ ⟨b, hb⟩ = 1 := qp_aut_eq_of_fix hsec (σ₁ ⟨b, hb⟩) hfixD'
  have hyp : ∀ w ∈ Sec45Z A Abar B, (b * w * b⁻¹)⁻¹ * w ∈ Sec45Q A Abar B := by
    intro w hw
    have h1 : σ₁ ⟨b, hb⟩ (QuotientGroup.mk ⟨w, hw⟩) = QuotientGroup.mk ⟨w, hw⟩ := by
      rw [hone, MulAut.one_apply]
    rw [hσ₁e ⟨w, hw⟩] at h1
    have h2 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1)
    simpa using h2
  exact Subtype.ext (sec47_C2 h hS hxA hxB hb hyp)
end

public section
open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G}

theorem sec47_comap_elemAbelian {X Y : Type} [Group X] [Group Y] {Z : Subgroup Y} {f : X →* Y}
    (hf : Function.Injective f) (hZ : IsElemAbelian 2 Z) : IsElemAbelian 2 (Z.comap f) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · simp only [Subgroup.coe_mul, map_mul]
    exact IsElemAbelian.comm hZ (Subgroup.mem_comap.mp x.2) (Subgroup.mem_comap.mp y.2)
  · rw [map_pow, map_one]
    exact hZ.2 _ (Subgroup.mem_comap.mp hx)

theorem sec47_subgroupOf_elemAbelian {Q Z : Subgroup G} (hQ : IsElemAbelian 2 Q) :
    IsElemAbelian 2 (Q.subgroupOf Z) :=
  sec47_comap_elemAbelian (f := Z.subtype) Subtype.val_injective hQ

theorem sec47_C_normal {Q Z : Subgroup G} :
    ((Q ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf Z).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hc : (g : G) * (n : G) = (n : G) * (g : G) :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2 g g.2
  have hgn : ((g * n * g⁻¹ : ↥Z) : G) = (n : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc, mul_inv_cancel_right]
  rw [hgn]
  exact hn

theorem sec47_C_le_center {Q Z : Subgroup G} :
    (Q ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf Z ≤ Subgroup.center ↥Z := by
  intro n hn
  rw [Subgroup.mem_subgroupOf] at hn
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2 g g.2

theorem sec47_C_le_N {Q Z : Subgroup G} :
    (Q ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf Z ≤ Q.subgroupOf Z := by
  intro n hn
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact (Subgroup.mem_inf.mp hn).1

theorem sec47_arith_psl2 {v t m d : ℕ} (hv : v = 2 ^ d) (hvle : v ≤ t ^ 2)
    (hB : 2 * t ≤ 2 ^ m) (hd : 2 * m ≤ d) (ht : 0 < t) : False := by
  have h1 : 2 ^ (2 * m) ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have h2 : (2 * t) ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left hB 2
  have h3 : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by rw [← pow_mul, mul_comm]
  have h4 : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
  have h5 : 0 < t ^ 2 := by positivity
  nlinarith

theorem sec47_arith_sz {v t k d : ℕ} (hv : v = 2 ^ d) (hvle : v ≤ t ^ 2)
    (hB : 2 * t ≤ 2 ^ (2 * k + 1)) (hd : 4 * (2 * k + 1) ≤ d) : False := by
  have h1 : 2 ^ (4 * (2 * k + 1)) ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have h2 : (2 * t) ^ 2 ≤ (2 ^ (2 * k + 1)) ^ 2 := Nat.pow_le_pow_left hB 2
  have h3 : (2 ^ (2 * k + 1)) ^ 2 = 2 ^ (4 * k + 2) := by
    rw [← pow_mul]
    congr 1
    ring
  have h4 : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
  have h5 : 2 ^ (8 * k + 6) = 4 * 2 ^ (4 * (2 * k + 1)) := by
    rw [show 8 * k + 6 = 4 * (2 * k + 1) + 2 by ring, pow_add]
    norm_num
    ring
  have h6 : 2 ^ (8 * k + 6) ≤ 2 ^ (4 * k + 2) := by
    rw [h5]
    nlinarith
  have h7 : 8 * k + 6 ≤ 4 * k + 2 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h6
  omega

theorem sec47_sz_facts {L : Type} [Group L] [Finite L] {k : ℕ} (hk : 1 ≤ k)
    (e : L ≃* CFSG.Open.Sz k) : IsSimpleGroup L ∧ Group.IsPerfect L := by
  haveI : IsSimpleGroup (CFSG.Open.Sz k) :=
    CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup (n := k) hk
  haveI hpS := CFSG.SectionRank.suzukiMatrixGroup_isPerfect k (by omega)
  haveI : Group.IsPerfect (CFSG.Open.Sz k) :=
    Group.IsPerfect.ofSurjective
      (f := (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv k).symm.toMonoidHom)
      (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv k).symm.surjective
  haveI hs : IsSimpleGroup L := e.isSimpleGroup
  haveI hp : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  exact ⟨hs, hp⟩

theorem sec47_index_card_le
    [hN : ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal]
    (h : Sec3Ctx A Abar S₀ B) (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {α : G} (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar)
    (hsimp : IsSimpleGroup (sec47Lz A Abar B)) (hperf : Group.IsPerfect (sec47Lz A Abar B))
    (hconj : ∀ x y : sec47Lz A Abar B, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hLgen : ∀ a g : sec47Lz A Abar B, orderOf a = 2 → orderOf g = 2 → ¬ Commute a g →
      Subgroup.closure ({x : sec47Lz A Abar B | x * x = 1 ∧ Commute x a} ∪ {g}) = ⊤) :
    Nat.card (↥((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) ⧸
      (((Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G)).subgroupOf
        (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)))) ≤
      Nat.card (Section3.A0 A Abar) ^ 2 := by
  have hαD : α ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) :=
    sec41g_mem_D.mpr ⟨1, Subgroup.one_mem _, α, hα, hαA₀, by simp⟩
  have hαα : α * α = 1 := sec46_D_sq h hαD
  obtain ⟨γ, hγE, -, hgen⟩ := sec47_gen_Z h hS hα hαA₀ hsimp hperf hconj hLgen
  obtain ⟨g, hgZ, hγg⟩ := sec47_E_conj h hα hαA₀ hγE
  have hγ : γ ∈ conjSubgroup g A := by
    rw [mem_conjSubgroup]
    have e1 : g⁻¹ * γ * g = α := by rw [hγg]; group
    rw [e1]
    exact hα
  have hγγ : γ * γ = 1 := sec46_D_sq h hγE
  have hQN1 := sec47_Q_le_N1_of_gen h hS hα hαA₀ hαα hgZ hγ hγγ hgen
  exact sec47_index_V h hS hα hαA₀ hgZ (sec46_D_le_Z hγE) hγ hgen hQN1

theorem sec47_V_action
    [hN : ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal]
    [hC : ((Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G)).subgroupOf
      (Sec45Z A Abar B)).Normal]
    (h : Sec3Ctx A Abar S₀ B) (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {α : G} (hα : α ∈ A) (hαA₀ : α ∉ Section3.A0 A Abar)
    (hperf : Group.IsPerfect (sec47Lz A Abar B)) :
    ∃ ρ : (↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) →*
      MulAut (↥((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) ⧸
        (((Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G)).subgroupOf
          (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)))),
      CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup (↥((Sec45Q A Abar B).subgroupOf
        (Sec45Z A Abar B)) ⧸
        (((Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G)).subgroupOf
          (Sec45Z A Abar B)).subgroupOf ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))))) ∧
      ∃ y ∈ commutator (↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)),
        ρ y ≠ 1 := by
  have hNel := sec47_subgroupOf_elemAbelian (Z := Sec45Z A Abar B)
    (sec46_Q_elemAbelian h hS)
  obtain ⟨ρ, hρ, hV⟩ := sec47_quot_action ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))
    ((Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G)).subgroupOf
      (Sec45Z A Abar B)) hNel sec47_C_le_N sec47_C_le_center
  exact ⟨ρ, hV, sec47_hnt_of_act h hS hα hαA₀ hperf ρ hρ⟩

theorem sec47_core
    (h : Sec3Ctx A Abar S₀ B)
    (hq : Section3.q A Abar = 2) :
    Section3.Abar0 A Abar ≤ normalizer (B : Set G) := by
  have h46 := sec46w_of
  have hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b := by
    intro b hb hb1
    obtain ⟨x, hxA, hx1, hxo⟩ := sec44w_holds G A Abar S₀ B h hq b hb hb1
    exact ⟨b, hb, hb1, Or.inl ⟨⟨x, hxA, hx1, hxo⟩, rfl⟩⟩
  obtain ⟨hQab, hQZ, hZN, hmain⟩ := h46 G A Abar S₀ B h hq
  haveI hNorm : ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQZ).mpr hZN
  obtain ⟨hrad, hmod⟩ := hmain
  haveI hCn : ((Sec45Q A Abar B ⊓ Subgroup.centralizer (Sec45Z A Abar B : Set G)).subgroupOf
      (Sec45Z A Abar B)).Normal := sec47_C_normal
  have hA0A : Section3.A0 A Abar ≤ A := by
    rw [h.a0_eq]
    exact inf_le_left
  have ht : 0 < Nat.card (Section3.A0 A Abar) := Nat.card_pos
  obtain ⟨α, hα, hαA₀⟩ : ∃ α ∈ A, α ∉ Section3.A0 A Abar := by
    by_contra hcon
    push_neg at hcon
    have h1 : (Section3.A0 A Abar).relIndex A = 1 := Subgroup.relIndex_eq_one.mpr hcon
    have h2 := sec46_relIndex_A h hq
    omega
  by_contra hcon
  obtain ⟨x, hxA, hxB⟩ : ∃ x ∈ Section3.Abar0 A Abar, x ∉ normalizer (B : Set G) := by
    by_contra hc
    push_neg at hc
    exact hcon hc
  obtain ⟨σ₂, hinj⟩ := sec47_sigma_inj h hS hxA hxB
  obtain ⟨g, hgB⟩ := h.nota.conj
  have hBel : IsElemAbelian 2 B := by
    rw [hgB]
    exact isElemAbelian_conj h.hyp.elemAbelian g
  have hBcard : Nat.card B = Nat.card A := by
    rw [hgB]
    exact card_conjSubgroup g A
  have hA_rel : Nat.card A = 2 * Nat.card (Section3.A0 A Abar) := by
    have e1 := Subgroup.relIndex_mul_card (H := Section3.A0 A Abar) (K := A)
    rw [inf_eq_left.mpr hA0A, sec46_relIndex_A h hq] at e1
    omega
  obtain ⟨hσel, hσcard⟩ := sec47_card_le_hom σ₂ hinj (sec47_top_elemAbelian hBel)
  rcases hmod with ⟨m, hm⟩ | ⟨a, ha⟩
  ·
    have hf2 : 2 ≤ m := sec47_f_two_le hrad hm
    obtain ⟨e⟩ := id hm
    obtain ⟨hs, hp, -⟩ := sec47_psl2_facts hf2 e
    haveI := hs
    have hconj : ∀ x y : sec47Lz A Abar B, orderOf x = 2 → orderOf y = 2 → IsConj x y :=
      fun x y hx hy => isConj_of_orderOf_eq_two_of_mulEquiv_psl2 hf2 e hx hy
    have hLgen : ∀ a g' : sec47Lz A Abar B, orderOf a = 2 → orderOf g' = 2 → ¬ Commute a g' →
        Subgroup.closure ({x : sec47Lz A Abar B | x * x = 1 ∧ Commute x a} ∪ {g'}) = ⊤ :=
      fun a g' ha' hg' hag => sec47_gen_psl2 hf2 hm ha' hg' hag
    have hVle := sec47_index_card_le h hS hα hαA₀ hs hp hconj hLgen
    obtain ⟨ρ, hV, hnt⟩ := sec47_V_action h hS hα hαA₀ hp
    obtain ⟨d, hd⟩ := sec47_card_two_pow hV
    have hdm : 2 * m ≤ d := sec47_module_bound hV ρ hrad hf2 hm hnt hd
    have hBle : Nat.card σ₂.range ≤ 2 ^ m := sec47_card_le_psl2 (by omega) hm hσel
    rw [hσcard, hBcard, hA_rel] at hBle
    exact sec47_arith_psl2 hd hVle hBle hdm ht
  ·
    have ha1 : 1 ≤ a := sec47_sz_one_le hrad ha
    obtain ⟨e⟩ := id ha
    obtain ⟨hs, hp⟩ := sec47_sz_facts ha1 e
    haveI := hs
    have hconj : ∀ x y : sec47Lz A Abar B, orderOf x = 2 → orderOf y = 2 → IsConj x y :=
      fun x y hx hy => isConj_of_orderOf_eq_two_of_mulEquiv_sz ha1 e hx hy
    have hLgen : ∀ a' g' : sec47Lz A Abar B, orderOf a' = 2 → orderOf g' = 2 → ¬ Commute a' g' →
        Subgroup.closure ({x : sec47Lz A Abar B | x * x = 1 ∧ Commute x a'} ∪ {g'}) = ⊤ :=
      fun a' g' ha' hg' hag => sec47_gen_sz ha1 ha ha' hg' hag
    have hVle := sec47_index_card_le h hS hα hαA₀ hs hp hconj hLgen
    obtain ⟨ρ, hV, hnt⟩ := sec47_V_action h hS hα hαA₀ hp
    obtain ⟨d, hd⟩ := sec47_card_two_pow hV
    have hdm : 4 * (2 * a + 1) ≤ d := sec47_module_bound_sz hV ρ hrad ha hnt hd
    have hBle : Nat.card σ₂.range ≤ 2 ^ (2 * a + 1) := sec47_card_le_sz ha1 ha hσel
    rw [hσcard, hBcard, hA_rel] at hBle
    exact sec47_arith_sz hd hVle hBle hdm

theorem sec47_of
    : Tim77Sec47Statement := by
  intro G _ _ A Abar S₀ B h hq B' hB'conj hB'S
  by_cases hBA : B' = A
  · rw [hBA, h.abar0_eq]
    exact inf_le_right
  · obtain ⟨g, hg⟩ := hB'conj
    have hgN : conjSubgroup g A ≤ normalizer (A : Set G) := by
      rw [← hg]
      exact hB'S.trans h.s0_le_normalizer
    have hX := tim77_2_3 h.hyp.elemAbelian h.hyp.ti hgN
    have hC : B' ≤ Subgroup.centralizer (A : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hb' : b ∈ conjSubgroup g A := by
        rw [← hg]
        exact hb
      exact IsElemAbelian.comm hX (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb')
    have hnota : Section3.Notation A Abar S₀ B' :=
      { choice := h.nota.choice, sylow := h.nota.sylow, contains := h.nota.contains,
        conj := ⟨g, hg⟩, ne := hBA, le := le_inf hB'S hC }
    exact sec47_core ⟨h.hyp, h.not_root, h.not_wc, hnota⟩ hq
end

end CFSG.RankThree.GF2n.Tim77
