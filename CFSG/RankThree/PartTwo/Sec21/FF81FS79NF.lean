module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Tr
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Fr6
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Fus2

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem zpow_three_cases {G : Type*} [Group G] {w : G} (h3 : w ^ 3 = 1) (k : ℤ) :
    w ^ k = 1 ∨ w ^ k = w ∨ w ^ k = w⁻¹ := by
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have e : w ^ k = w ^ (k % 3) := by
    have h1 : w ^ (3 : ℤ) = 1 := by exact_mod_cast h3
    calc w ^ k = w ^ (k % 3 + 3 * (k / 3)) := by rw [Int.emod_add_mul_ediv]
      _ = w ^ (k % 3) * (w ^ (3 : ℤ)) ^ (k / 3) := by rw [zpow_add, zpow_mul]
      _ = w ^ (k % 3) := by rw [h1, one_zpow, mul_one]
  rcases hk with h0 | h0 | h0 <;> rw [e, h0]
  · left; exact zpow_zero w
  · right; left; exact zpow_one w
  · right; right
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3])

def R34Stmt (b b₁ b₂ : H) : Prop :=
  setMul (Opp 3 (Nor (Subgroup.zpowers (b₁ * b₂))))
    (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers (b₁ * b₂))) =
      Nor (Subgroup.zpowers (b₁ * b₂))

theorem FS79Hyp.nf_I' (h : FS79Hyp b t b₁ b₂ J) {u v w₀ : H} (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hw₀ : w₀ ∈ Subgroup.closure ({b₁, b₂} : Set H)) (hw₀1 : w₀ ≠ 1)
    (hu : ∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H), y * u = u * y) (hbv : b * v = v * b)
    (hw₀v : w₀ * v = v * w₀) : ¬ HC u v := by
  rintro ⟨g, hgu⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB₁3 : IsPGroup 3 (Subgroup.closure ({b₁, b₂} : Set H)) := by
    have hE := h.isElemAb_B
    haveI := hE.1
    exact (IsElementaryAbelian.isPGroup 3 _).to_le (FS79Hyp.B₁_le_B b b₁ b₂)
  have hXu : Subgroup.closure ({b₁, b₂} : Set H) ≤ Cen u := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hu y hy)
  have hEv : E0 b w₀ ≤ Cen v := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hbv
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hw₀v
  obtain ⟨g', -, hg'⟩ := h.conj_into_sylow hv2 hv1 hgu hB₁3 hXu (h.E0_pgroup hw₀) hEv
    (h.E0_card hw₀ hw₀1)
  have hconjB₁ : ∀ z ∈ Subgroup.closure ({b₁, b₂} : Set H),
      g' * z * g'⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H) := by
    intro z hz
    obtain ⟨j, hj, hjB, hjz⟩ := h.fusion_B₁ hz (h.E0_le_B hw₀ (hg' z hz))
    rw [hjz]
    exact hjB z hz
  set X' : Subgroup H := (Subgroup.closure ({b₁, b₂} : Set H)).map (MulAut.conj g').toMonoidHom
    with hX'
  have hX'card : Nat.card X' = 9 := by
    rw [hX', Subgroup.card_map_of_injective (MulAut.conj g').injective]
    simpa using h.E9.2
  have hX'E : X' ≤ E0 b w₀ := by
    rintro _ ⟨z, hz, rfl⟩
    have e : (MulAut.conj g').toMonoidHom z = g' * z * g'⁻¹ := by simp [MulAut.conj_apply]
    rw [e]
    exact hg' z hz
  have hX'eq : X' = E0 b w₀ :=
    Subgroup.eq_of_le_of_card_ge hX'E (by rw [hX'card, h.E0_card hw₀ hw₀1])
  have hbE : b ∈ E0 b w₀ := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  rw [← hX'eq] at hbE
  obtain ⟨z, hz, hzb⟩ := hbE
  have e : (MulAut.conj g').toMonoidHom z = g' * z * g'⁻¹ := by simp [MulAut.conj_apply]
  rw [e] at hzb
  have hbB₁ : b ∈ Subgroup.closure ({b₁, b₂} : Set H) := by
    rw [← hzb]
    exact hconjB₁ z hz
  exact h.b_not_mem_J (h.B₁_le_J hbB₁)

theorem FS79Hyp.nf_I (h : FS79Hyp b t b₁ b₂ J) {u v w w₀ : H} (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hw : w ∈ Subgroup.closure ({b₁, b₂} : Set H))
    (hw₀ : w₀ ∈ Subgroup.closure ({b₁, b₂} : Set H)) (hw₀1 : w₀ ≠ 1) (hwu : w * u = u * w)
    (hbv : b * v = v * b) (hw₀v : w₀ * v = v * w₀)
    (hdis : ∀ j ∈ J, (∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H),
      j * y * j⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H)) →
        j * w * j⁻¹ ∉ Subgroup.zpowers w₀) : ¬ HC u v := by
  rintro ⟨g, hgu⟩
  have hw3 : w ^ 3 = 1 := h.B_pow_three (FS79Hyp.B₁_le_B b b₁ b₂ hw)
  have hX3 : IsPGroup 3 (Subgroup.zpowers w) := isPGroup_zpowers_of_pow_three hw3
  have hXu : Subgroup.zpowers w ≤ Cen u := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hwu
  have hEv : E0 b w₀ ≤ Cen v := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hbv
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hw₀v
  obtain ⟨g', -, hg'⟩ := h.conj_into_sylow hv2 hv1 hgu hX3 hXu (h.E0_pgroup hw₀) hEv
    (h.E0_card hw₀ hw₀1)
  have hw' : g' * w * g'⁻¹ ∈ E0 b w₀ := hg' w (Subgroup.mem_zpowers w)
  obtain ⟨j, hj, hjB, hjw⟩ := h.fusion_B₁ hw (h.E0_le_B hw₀ hw')
  apply hdis j hj hjB
  rw [← hjw]
  exact h.E0_inf_B₁ hw₀ hw' (hjw ▸ hjB w hw)


theorem FS79Hyp.t_mem_Y (b t : H) : t ∈ Subgroup.closure ({b, t} : Set H) :=
  Subgroup.subset_closure (by simp)

theorem mem_Nor_zpowers_of_conj {x₀ g : H} (hg : g * x₀ * g⁻¹ ∈ Subgroup.zpowers x₀) :
    g ∈ Nor (Subgroup.zpowers x₀) := by
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have e : g * x₀ ^ k * g⁻¹ = (g * x₀ * g⁻¹) ^ k := by
    have := map_zpow (MulAut.conj g) x₀ k
    simpa [MulAut.conj_apply] using this
  rw [e]
  exact Subgroup.zpow_mem _ hg k

theorem mem_Nor_zpowers_of_comm {x₀ g : H} (hg : g * x₀ = x₀ * g) :
    g ∈ Nor (Subgroup.zpowers x₀) :=
  fs79_cen_le_nor_zpowers x₀ (Subgroup.mem_centralizer_singleton_iff.mpr hg)

theorem FS79Hyp.nf_IIa (h : FS79Hyp b t b₁ b₂ J) {x₀ ρ : H} {Q : Subgroup H} (hctl : Ctl b x₀ Q)
    (hx₀ : x₀ ∈ Subgroup.closure ({b₁, b₂} : Set H)) (hx₀1 : x₀ ≠ 1)
    (horb : ∀ j ∈ J, (∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H),
        j * y * j⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H)) →
        j * x₀ * j⁻¹ ∈ Subgroup.zpowers x₀ → j * x₀ * j⁻¹ = x₀ ∨ j * x₀ * j⁻¹ = x₀⁻¹)
    (hρJ : ρ ∈ J) (hρ2 : ρ * ρ = 1) (hρ1 : ρ ≠ 1) (hx₀ρ : x₀ * ρ = ρ * x₀) :
    ¬ HC (t * ρ) ρ := by
  rintro ⟨g, hgu⟩
  have hx₀J : x₀ ∈ J := h.B₁_le_J hx₀
  have hx₀t : x₀ * t = t * x₀ := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t hx₀J)
  have hρt : ρ * t = t * ρ := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t hρJ)
  have hbρ : ρ * b = b * ρ := h.b_comm_of_mem_J hρJ
  have hx₀3 : x₀ ^ 3 = 1 := h.B_pow_three (FS79Hyp.B₁_le_B b b₁ b₂ hx₀)
  have hX3 : IsPGroup 3 (Subgroup.zpowers x₀) := isPGroup_zpowers_of_pow_three hx₀3
  have hXu : Subgroup.zpowers x₀ ≤ Cen (t * ρ) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc x₀ * (t * ρ) = (x₀ * t) * ρ := by group
      _ = (t * x₀) * ρ := by rw [hx₀t]
      _ = t * (x₀ * ρ) := by group
      _ = t * (ρ * x₀) := by rw [hx₀ρ]
      _ = (t * ρ) * x₀ := by group
  have hEv : E0 b x₀ ≤ Cen ρ := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hbρ.symm
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hx₀ρ
  obtain ⟨g', hg'u, hg'⟩ := h.conj_into_sylow hρ2 hρ1 hgu hX3 hXu (h.E0_pgroup hx₀) hEv
    (h.E0_card hx₀ hx₀1)
  have hx' : g' * x₀ * g'⁻¹ ∈ E0 b x₀ := hg' x₀ (Subgroup.mem_zpowers x₀)
  obtain ⟨j, hj, hjB, hjx⟩ := h.fusion_B₁ hx₀ (h.E0_le_B hx₀ hx')
  have hmem : g' * x₀ * g'⁻¹ ∈ Subgroup.zpowers x₀ :=
    h.E0_inf_B₁ hx₀ hx' (hjx ▸ hjB x₀ hx₀)
  have hnor : g' ∈ Nor (Subgroup.zpowers x₀) := mem_Nor_zpowers_of_conj hmem
  have hux : t * ρ ∈ Nor (Subgroup.zpowers x₀) := by
    refine mem_Nor_zpowers_of_comm ?_
    calc t * ρ * x₀ = t * (ρ * x₀) := by group
      _ = t * (x₀ * ρ) := by rw [hx₀ρ]
      _ = (t * x₀) * ρ := by group
      _ = (x₀ * t) * ρ := by rw [hx₀t]
      _ = x₀ * (t * ρ) := by group
  obtain ⟨y, hy, j', hj', hy1, -⟩ := hctl.conj_YJ h hx₀ hx₀1 (FS79Hyp.t_mem_Y b t)
    (Subgroup.one_mem _) hρJ hρJ hux hnor (by simpa using hg'u)
  apply h.t_ne_one
  calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
    _ = 1 := by rw [← hy1]; group

theorem FS79Hyp.nf_III (h : FS79Hyp b t b₁ b₂ J) {x₀ ρ : H} {Q : Subgroup H} (hctl : Ctl b x₀ Q)
    (hx₀ : x₀ ∈ Subgroup.closure ({b₁, b₂} : Set H)) (hx₀1 : x₀ ≠ 1)
    (hρJ : ρ ∈ J) (hρ2 : ρ * ρ = 1) (hρ1 : ρ ≠ 1) (hx₀ρ : x₀ * ρ = ρ * x₀) :
    ¬ HC t (t * ρ) := by
  rintro ⟨x, hxt⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx₀J : x₀ ∈ J := h.B₁_le_J hx₀
  have hx₀t : x₀ * t = t * x₀ := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t hx₀J)
  have hρt : ρ * t = t * ρ := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t hρJ)
  have ht2 := h.t_sq
  set v : H := t * ρ with hv
  have hv2 : v * v = 1 := by
    calc t * ρ * (t * ρ) = t * (ρ * t) * ρ := by group
      _ = t * (t * ρ) * ρ := by rw [hρt]
      _ = (t * t) * (ρ * ρ) := by group
      _ = 1 := by rw [ht2, hρ2, one_mul]
  have hv1 : v ≠ 1 := by
    intro h1
    apply h.t_not_mem_J
    have : t = ρ⁻¹ := by
      calc t = (t * ρ) * ρ⁻¹ := by group
        _ = ρ⁻¹ := by rw [← hv, h1, one_mul]
    rw [this]
    exact J.inv_mem hρJ
  set E : Subgroup H := (Subgroup.closure ({b₁, b₂} : Set H)).map (MulAut.conj x).toMonoidHom
    with hE
  have hB₁3 : IsPGroup 3 (Subgroup.closure ({b₁, b₂} : Set H)) := by
    have hE' := h.isElemAb_B
    haveI := hE'.1
    exact (IsElementaryAbelian.isPGroup 3 _).to_le (FS79Hyp.B₁_le_B b b₁ b₂)
  have hE3 : IsPGroup 3 E := hB₁3.map _
  have hEcard : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj x).injective]
    simpa using h.E9.2
  have hEv : E ≤ Cen v := by
    rintro _ ⟨z, hz, rfl⟩
    have hzt : z * t = t * z :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t (h.B₁_le_J hz))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : (MulAut.conj x).toMonoidHom z = x * z * x⁻¹ := by simp [MulAut.conj_apply]
    rw [e, ← hxt]
    calc x * z * x⁻¹ * (x * t * x⁻¹) = x * (z * t) * x⁻¹ := by group
      _ = x * (t * z) * x⁻¹ := by rw [hzt]
      _ = x * t * x⁻¹ * (x * z * x⁻¹) := by group
  have hSyl := h.isSylowOf_cen hv2 hv1 hE3 hEv hEcard
  have hx₀3 : x₀ ^ 3 = 1 := h.B_pow_three (FS79Hyp.B₁_le_B b b₁ b₂ hx₀)
  have hX3 : IsPGroup 3 (Subgroup.zpowers x₀) := isPGroup_zpowers_of_pow_three hx₀3
  have hXv : Subgroup.zpowers x₀ ≤ Cen v := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc x₀ * (t * ρ) = (x₀ * t) * ρ := by group
      _ = (t * x₀) * ρ := by rw [hx₀t]
      _ = t * (x₀ * ρ) := by group
      _ = t * (ρ * x₀) := by rw [hx₀ρ]
      _ = (t * ρ) * x₀ := by group
  obtain ⟨c, hc, hcx⟩ := L14.exists_conj_le_sylowOf hSyl hXv hX3
  have hcx₀ : c * x₀ * c⁻¹ ∈ E := hcx x₀ (Subgroup.mem_zpowers x₀)
  obtain ⟨z, hz, hzx⟩ := hcx₀
  have e : (MulAut.conj x).toMonoidHom z = x * z * x⁻¹ := by simp [MulAut.conj_apply]
  rw [e] at hzx
  have hgz : (c⁻¹ * x) * z * (c⁻¹ * x)⁻¹ = x₀ := by
    calc (c⁻¹ * x) * z * (c⁻¹ * x)⁻¹ = c⁻¹ * (x * z * x⁻¹) * c := by group
      _ = c⁻¹ * (c * x₀ * c⁻¹) * c := by rw [hzx]
      _ = x₀ := by group
  obtain ⟨j, hj, hjB, hjz⟩ := h.fusion_B₁ hz (by
    rw [hgz]
    exact FS79Hyp.B₁_le_B b b₁ b₂ hx₀)
  rw [hgz] at hjz
  have hjt : j * t = t * j := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t hj)
  have hg''x : (c⁻¹ * x * j⁻¹) * x₀ * (c⁻¹ * x * j⁻¹)⁻¹ = x₀ := by
    calc (c⁻¹ * x * j⁻¹) * x₀ * (c⁻¹ * x * j⁻¹)⁻¹
        = (c⁻¹ * x) * (j⁻¹ * x₀ * j) * (c⁻¹ * x)⁻¹ := by group
      _ = (c⁻¹ * x) * z * (c⁻¹ * x)⁻¹ := by
        congr 2
        rw [hjz]
        group
      _ = x₀ := hgz
  have hcv : c * v = v * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hg''t : (c⁻¹ * x * j⁻¹) * t * (c⁻¹ * x * j⁻¹)⁻¹ = v := by
    have h1 : j⁻¹ * t * j = t := by
      calc j⁻¹ * t * j = j⁻¹ * (t * j) := by group
        _ = j⁻¹ * (j * t) := by rw [hjt]
        _ = t := by group
    calc (c⁻¹ * x * j⁻¹) * t * (c⁻¹ * x * j⁻¹)⁻¹
        = (c⁻¹ * x) * (j⁻¹ * t * j) * (c⁻¹ * x)⁻¹ := by group
      _ = c⁻¹ * (x * t * x⁻¹) * c := by rw [h1]; group
      _ = c⁻¹ * v * c := by rw [hxt]
      _ = v := by
        calc c⁻¹ * v * c = c⁻¹ * (v * c) := by group
          _ = c⁻¹ * (c * v) := by rw [hcv]
          _ = v := by group
  have hnor : (c⁻¹ * x * j⁻¹) ∈ Nor (Subgroup.zpowers x₀) :=
    mem_Nor_zpowers_of_comm (by
      have := hg''x
      calc (c⁻¹ * x * j⁻¹) * x₀ = ((c⁻¹ * x * j⁻¹) * x₀ * (c⁻¹ * x * j⁻¹)⁻¹) * (c⁻¹ * x * j⁻¹) := by
            group
        _ = x₀ * (c⁻¹ * x * j⁻¹) := by rw [hg''x])
  have hux : t * 1 ∈ Nor (Subgroup.zpowers x₀) := by
    refine mem_Nor_zpowers_of_comm ?_
    simpa using hx₀t.symm
  obtain ⟨y, hy, j', hj', -, hρj⟩ := hctl.conj_YJ h hx₀ hx₀1 (FS79Hyp.t_mem_Y b t)
    (FS79Hyp.t_mem_Y b t) (Subgroup.one_mem _) hρJ hux hnor (by simpa using hg''t)
  apply hρ1
  calc ρ = j' * 1 * j'⁻¹ := hρj
    _ = 1 := by group


namespace J6

theorem c₁_pow_three : c₁ ^ 3 = 1 := by decide +kernel

theorem c₂_pow_three : c₂ ^ 3 = 1 := by decide +kernel

theorem d_pow_three : (c₁ * c₂) ^ 3 = 1 := by decide +kernel

theorem c₁_ne_one : c₁ ≠ 1 := by decide +kernel

theorem c₂_ne_one : c₂ ≠ 1 := by decide +kernel

theorem d_ne_one : c₁ * c₂ ≠ 1 := by decide +kernel

theorem c₁_comm_a2 : c₁ * a2 = a2 * c₁ := a2_cen_c1.symm

theorem d_comm_sg3 : (c₁ * c₂) * sg3 = sg3 * (c₁ * c₂) := sg3_cen_d.symm

end J6

namespace Std

variable (S : Std b t b₁ b₂ J)

include S

theorem b₁_mem_B₁ : b₁ ∈ Subgroup.closure ({b₁, b₂} : Set H) := Subgroup.subset_closure (by simp)

theorem b₂_mem_B₁ : b₂ ∈ Subgroup.closure ({b₁, b₂} : Set H) := Subgroup.subset_closure (by simp)

theorem ι_d : S.ι (J6.c₁ * J6.c₂) = b₁ * b₂ := by rw [map_mul, S.ι_c₁, S.ι_c₂]

theorem d_mem_B₁ : b₁ * b₂ ∈ Subgroup.closure ({b₁, b₂} : Set H) :=
  Subgroup.mul_mem _ S.b₁_mem_B₁ S.b₂_mem_B₁

theorem b₁_ne_one : b₁ ≠ 1 := fun h1 =>
  J6.c₁_ne_one (S.ι_injective (S.ι_c₁.trans (h1.trans (map_one S.ι).symm)))

theorem b₂_ne_one : b₂ ≠ 1 := fun h1 =>
  J6.c₂_ne_one (S.ι_injective (S.ι_c₂.trans (h1.trans (map_one S.ι).symm)))

theorem d_ne_one : b₁ * b₂ ≠ 1 := fun h1 =>
  J6.d_ne_one (S.ι_injective (S.ι_d.trans (h1.trans (map_one S.ι).symm)))

theorem mem_zpowers_ι {σ x : J6.S6} (h3 : σ ^ 3 = 1) (hx : S.ι x ∈ Subgroup.zpowers (S.ι σ)) :
    x = 1 ∨ x = σ ∨ x = σ⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← map_zpow] at hk
  have := S.ι_injective hk
  rw [← this]
  exact zpow_three_cases h3 k

theorem conj_b₁ {j : H} (hj : j ∈ J) :
    j * b₁ * j⁻¹ = S.ι (S.φ ⟨j, hj⟩ * J6.c₁ * (S.φ ⟨j, hj⟩)⁻¹) := by
  have := S.conj_ι hj J6.c₁
  rwa [S.ι_c₁] at this

theorem conj_d {j : H} (hj : j ∈ J) :
    j * (b₁ * b₂) * j⁻¹ = S.ι (S.φ ⟨j, hj⟩ * (J6.c₁ * J6.c₂) * (S.φ ⟨j, hj⟩)⁻¹) := by
  have := S.conj_ι hj (J6.c₁ * J6.c₂)
  rwa [S.ι_d] at this

theorem zpowers_b₁_eq : Subgroup.zpowers b₁ = Subgroup.zpowers (S.ι J6.c₁) := by rw [S.ι_c₁]

theorem zpowers_d_eq : Subgroup.zpowers (b₁ * b₂) = Subgroup.zpowers (S.ι (J6.c₁ * J6.c₂)) := by
  rw [S.ι_d]

theorem hdis_A : ∀ j ∈ J, (∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H),
    j * y * j⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H)) →
      j * (b₁ * b₂) * j⁻¹ ∉ Subgroup.zpowers b₁ := by
  intro j hj hjB hmem
  have hσ := S.norm6 hj hjB
  rw [S.conj_d hj, S.zpowers_b₁_eq] at hmem
  have h1 := S.mem_zpowers_ι J6.c₁_pow_three hmem
  have h2 := (J6.norm_orbits _ hσ).2.2
  have : S.φ ⟨j, hj⟩ * (J6.c₁ * J6.c₂) * (S.φ ⟨j, hj⟩)⁻¹ ∈
      ({1, J6.c₁, J6.c₁⁻¹} : Finset J6.S6) := by
    rcases h1 with h1 | h1 | h1 <;> simp [h1]
  exact J6.orbitC_not_cyc_c1 _ h2 this

theorem hdis_B : ∀ j ∈ J, (∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H),
    j * y * j⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H)) →
      j * b₁ * j⁻¹ ∉ Subgroup.zpowers (b₁ * b₂) := by
  intro j hj hjB hmem
  have hσ := S.norm6 hj hjB
  rw [S.conj_b₁ hj, S.zpowers_d_eq] at hmem
  have h1 := S.mem_zpowers_ι J6.d_pow_three hmem
  have h2 := (J6.norm_orbits _ hσ).1
  have : S.φ ⟨j, hj⟩ * J6.c₁ * (S.φ ⟨j, hj⟩)⁻¹ ∈
      ({1, J6.c₁ * J6.c₂, (J6.c₁ * J6.c₂)⁻¹} : Finset J6.S6) := by
    rcases h1 with h1 | h1 | h1 <;> simp [h1]
  exact J6.orbitB_not_cyc_d _ h2 this

theorem horb_b₁ : ∀ j ∈ J, (∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H),
    j * y * j⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H)) →
      j * b₁ * j⁻¹ ∈ Subgroup.zpowers b₁ → j * b₁ * j⁻¹ = b₁ ∨ j * b₁ * j⁻¹ = b₁⁻¹ := by
  intro j hj hjB hmem
  have hσ := S.norm6 hj hjB
  rw [S.conj_b₁ hj, S.zpowers_b₁_eq] at hmem
  rw [S.conj_b₁ hj]
  have h1 := S.mem_zpowers_ι J6.c₁_pow_three hmem
  have h2 := (J6.norm_orbits _ hσ).1
  have h3 := J6.orbitB_cyc_c1 _ h2 (by rcases h1 with h1 | h1 | h1 <;> simp [h1])
  rcases h3 with h3 | h3
  · left
    rw [h3, S.ι_c₁]
  · right
    rw [h3, map_inv, S.ι_c₁]

theorem horb_d : ∀ j ∈ J, (∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H),
    j * y * j⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H)) →
      j * (b₁ * b₂) * j⁻¹ ∈ Subgroup.zpowers (b₁ * b₂) →
        j * (b₁ * b₂) * j⁻¹ = b₁ * b₂ ∨ j * (b₁ * b₂) * j⁻¹ = (b₁ * b₂)⁻¹ := by
  intro j hj hjB hmem
  have hσ := S.norm6 hj hjB
  rw [S.conj_d hj, S.zpowers_d_eq] at hmem
  rw [S.conj_d hj]
  have h1 := S.mem_zpowers_ι J6.d_pow_three hmem
  have h2 := (J6.norm_orbits _ hσ).2.2
  have h3 := J6.orbitC_cyc_d _ h2 (by rcases h1 with h1 | h1 | h1 <;> simp [h1])
  rcases h3 with h3 | h3
  · left
    rw [h3, S.ι_d]
  · right
    rw [h3, map_inv, S.ι_d]

theorem d_comm_ι_sg3 : (b₁ * b₂) * S.ι J6.sg3 = S.ι J6.sg3 * (b₁ * b₂) := by
  calc (b₁ * b₂) * S.ι J6.sg3 = S.ι (J6.c₁ * J6.c₂) * S.ι J6.sg3 := by rw [S.ι_d]
    _ = S.ι ((J6.c₁ * J6.c₂) * J6.sg3) := (map_mul _ _ _).symm
    _ = S.ι (J6.sg3 * (J6.c₁ * J6.c₂)) := by rw [J6.d_comm_sg3]
    _ = S.ι J6.sg3 * S.ι (J6.c₁ * J6.c₂) := map_mul _ _ _
    _ = S.ι J6.sg3 * (b₁ * b₂) := by rw [S.ι_d]

theorem b₁_comm_ι_a2 : b₁ * S.ι J6.a2 = S.ι J6.a2 * b₁ := by
  calc b₁ * S.ι J6.a2 = S.ι J6.c₁ * S.ι J6.a2 := by rw [S.ι_c₁]
    _ = S.ι (J6.c₁ * J6.a2) := (map_mul _ _ _).symm
    _ = S.ι (J6.a2 * J6.c₁) := by rw [J6.c₁_comm_a2]
    _ = S.ι J6.a2 * S.ι J6.c₁ := map_mul _ _ _
    _ = S.ι J6.a2 * b₁ := by rw [S.ι_c₁]

theorem ι_a2_sq : S.ι J6.a2 * S.ι J6.a2 = 1 := by rw [← map_mul, J6.a2_sq, map_one]

theorem ι_sg3_sq : S.ι J6.sg3 * S.ι J6.sg3 = 1 := by rw [← map_mul, J6.sg3_sq, map_one]

theorem ι_a2_ne_one : S.ι J6.a2 ≠ 1 := fun h1 =>
  J6.a2_ne_one (S.ι_injective (h1.trans (map_one S.ι).symm))

theorem ι_sg3_ne_one : S.ι J6.sg3 ≠ 1 := fun h1 =>
  J6.sg3_ne_one (S.ι_injective (h1.trans (map_one S.ι).symm))

theorem J_comm_t {x : H} (hx : x ∈ J) : x * t = t * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (S.hyp.J_le_cen_t hx)

theorem nf_t_a2 : ¬ HC t (S.ι J6.a2) :=
  S.hyp.nf_I' S.ι_a2_sq S.ι_a2_ne_one S.b₁_mem_B₁ S.b₁_ne_one
    (fun y hy => S.J_comm_t (S.hyp.B₁_le_J hy)) (S.ι_comm_b J6.a2).symm S.b₁_comm_ι_a2

theorem nf_t_sg3 : ¬ HC t (S.ι J6.sg3) :=
  S.hyp.nf_I' S.ι_sg3_sq S.ι_sg3_ne_one S.d_mem_B₁ S.d_ne_one
    (fun y hy => S.J_comm_t (S.hyp.B₁_le_J hy)) (S.ι_comm_b J6.sg3).symm S.d_comm_ι_sg3

theorem nf_a2_sg3 : ¬ HC (S.ι J6.a2) (S.ι J6.sg3) :=
  S.hyp.nf_I S.ι_sg3_sq S.ι_sg3_ne_one S.b₁_mem_B₁ S.d_mem_B₁ S.d_ne_one S.b₁_comm_ι_a2
    (S.ι_comm_b J6.sg3).symm S.d_comm_ι_sg3 S.hdis_B

theorem nf_tia2_sg3 : ¬ HC (t * S.ι J6.a2) (S.ι J6.sg3) := by
  refine S.hyp.nf_I S.ι_sg3_sq S.ι_sg3_ne_one S.b₁_mem_B₁ S.d_mem_B₁ S.d_ne_one ?_
    (S.ι_comm_b J6.sg3).symm S.d_comm_ι_sg3 S.hdis_B
  have hb₁t : b₁ * t = t * b₁ := S.J_comm_t (S.hyp.b₁_mem)
  calc b₁ * (t * S.ι J6.a2) = (b₁ * t) * S.ι J6.a2 := by group
    _ = (t * b₁) * S.ι J6.a2 := by rw [hb₁t]
    _ = t * (b₁ * S.ι J6.a2) := by group
    _ = t * (S.ι J6.a2 * b₁) := by rw [S.b₁_comm_ι_a2]
    _ = (t * S.ι J6.a2) * b₁ := by group

theorem nf_tisg3_a2 : ¬ HC (t * S.ι J6.sg3) (S.ι J6.a2) := by
  refine S.hyp.nf_I S.ι_a2_sq S.ι_a2_ne_one S.d_mem_B₁ S.b₁_mem_B₁ S.b₁_ne_one ?_
    (S.ι_comm_b J6.a2).symm S.b₁_comm_ι_a2 S.hdis_A
  have hdt : (b₁ * b₂) * t = t * (b₁ * b₂) :=
    S.J_comm_t (J.mul_mem S.hyp.b₁_mem S.hyp.b₂_mem)
  calc (b₁ * b₂) * (t * S.ι J6.sg3) = ((b₁ * b₂) * t) * S.ι J6.sg3 := by group
    _ = (t * (b₁ * b₂)) * S.ι J6.sg3 := by rw [hdt]
    _ = t * ((b₁ * b₂) * S.ι J6.sg3) := by group
    _ = t * (S.ι J6.sg3 * (b₁ * b₂)) := by rw [S.d_comm_ι_sg3]
    _ = (t * S.ι J6.sg3) * (b₁ * b₂) := by group

theorem nf_a2_tia2 : ¬ HC (t * S.ι J6.a2) (S.ι J6.a2) :=
  S.hyp.nf_IIa (Ctl.of_N_bi (S.hyp.N_bi b₁ (Set.mem_insert _ _))) S.b₁_mem_B₁ S.b₁_ne_one
    S.horb_b₁ (S.ι_mem _) S.ι_a2_sq S.ι_a2_ne_one S.b₁_comm_ι_a2

theorem nf_sg3_tisg3 (h34 : R34Stmt b b₁ b₂) : ¬ HC (t * S.ι J6.sg3) (S.ι J6.sg3) :=
  S.hyp.nf_IIa (Ctl.of_N_bi h34) S.d_mem_B₁ S.d_ne_one S.horb_d (S.ι_mem _) S.ι_sg3_sq
    S.ι_sg3_ne_one S.d_comm_ι_sg3

theorem nf_t_tia2 : ¬ HC t (t * S.ι J6.a2) :=
  S.hyp.nf_III (Ctl.of_N_bi (S.hyp.N_bi b₁ (Set.mem_insert _ _))) S.b₁_mem_B₁ S.b₁_ne_one
    (S.ι_mem _) S.ι_a2_sq S.ι_a2_ne_one S.b₁_comm_ι_a2

theorem nf_t_tisg3 (h34 : R34Stmt b b₁ b₂) : ¬ HC t (t * S.ι J6.sg3) :=
  S.hyp.nf_III (Ctl.of_N_bi h34) S.d_mem_B₁ S.d_ne_one (S.ι_mem _) S.ι_sg3_sq
    S.ι_sg3_ne_one S.d_comm_ι_sg3

end Std

end CFSG.RankThree.PartTwo.Sec21.FF81
