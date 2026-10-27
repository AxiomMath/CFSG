module

public import CFSG.RankThree.PartOne.SEITZ12.CaseB4
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open Subgroup

variable {G : Type*} [Group G]

theorem phi4B_hom_one {P N : Type*} [Group P] [Group N] [Group.IsPerfect P]
    [Group.IsNilpotent N] (f : P →* N) (x : P) : f x = 1 := by
  by_contra hx
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Nontrivial f.range := ⟨⟨⟨f x, x, rfl⟩, 1, fun h' => hx (congrArg Subtype.val h')⟩⟩
  exact Group.IsPerfect.not_isNilpotent f.range inferInstance

namespace phi4B_Ctx

variable {D X₂ S₂ Z₂ : Subgroup G} {t : G} {q : ℕ} {cls : G → Prop}

theorem S₁_isPGroup (h : phi4B_Ctx D X₂ S₂ Z₂ t q cls) : IsPGroup 2 (conjSub S₂ t) := by
  apply phi4B_isPGroup_of_pow (k := 2)
  intro x hx
  have h1 := h.core.suz₁.sq_Z _ (h.core.suz₁.sq_mem x hx)
  have e : x ^ (2 ^ 2) = (x * x) * (x * x) := phi4B_pow_four x
  rw [e]
  exact h1

theorem diag_mul (h : phi4B_Ctx D X₂ S₂ Z₂ t q cls) {s s' : G} (hs : s ∈ conjSub X₂ t)
    (hs' : s' ∈ conjSub X₂ t) :
    (s * s') * (t * (s * s') * t) = (s * (t * s * t)) * (s' * (t * s' * t)) := by
  have hc := h.core
  have hcomm' : s' * (t * s * t) = (t * s * t) * s' :=
    (hc.comm _ (phi4B_tau_mem' hc.t_sq hs) s' hs').symm
  calc s * s' * (t * (s * s') * t) = s * s' * ((t * s * t) * (t * s' * t)) := by
        rw [phi4B_tau_mul hc.t_sq]
    _ = s * (s' * (t * s * t)) * (t * s' * t) := by simp only [mul_assoc]
    _ = s * ((t * s * t) * s') * (t * s' * t) := by rw [hcomm']
    _ = s * (t * s * t) * (s' * (t * s' * t)) := by simp only [mul_assoc]

theorem diag_comm (h : phi4B_Ctx D X₂ S₂ Z₂ t q cls) {s : G} (hs : s ∈ conjSub X₂ t) :
    (s * (t * s * t)) * t = t * (s * (t * s * t)) := by
  have hc := h.core
  have e1 : t * (s * (t * s * t)) * t = s * (t * s * t) := by
    calc t * (s * (t * s * t)) * t = (t * s * t) * (t * (t * s * t) * t) := by
          rw [← phi4B_tau_mul hc.t_sq]
      _ = (t * s * t) * s := by rw [phi4B_tau_tau hc.t_sq]
      _ = s * (t * s * t) := hc.comm _ (phi4B_tau_mem' hc.t_sq hs) s hs
  calc s * (t * s * t) * t = t * (s * (t * s * t)) * t * t := by rw [e1]
    _ = t * (s * (t * s * t)) := by rw [mul_assoc, hc.t_sq, mul_one]

theorem B5 [Finite D] (h : phi4B_Ctx D X₂ S₂ Z₂ t q cls) : False := by
  have hc := h.core
  obtain ⟨d, hdD, x, hxZ, hx1, hdt⟩ := h.B4
  have key : ∀ s : ↥(conjSub X₂ t), ∃ a r : G, a ∈ conjSub S₂ t ∧ r ∈ X₂ ∧
      d * (s.1 * (t * s.1 * t)) * d⁻¹ = a * r := by
    intro s
    have hsD : s.1 ∈ D := h.X₁D s.2
    have hτ : t * s.1 * t ∈ X₂ := phi4B_tau_mem' hc.t_sq s.2
    have hδD : s.1 * (t * s.1 * t) ∈ D := mul_mem hsD (h.X₂D hτ)
    have hwD : d * (s.1 * (t * s.1 * t)) * d⁻¹ ∈ D := mul_mem (mul_mem hdD hδD) (inv_mem hdD)
    have hwx : d * (s.1 * (t * s.1 * t)) * d⁻¹ * x = x * (d * (s.1 * (t * s.1 * t)) * d⁻¹) := by
      rw [← hdt]
      have e1 : d * (s.1 * (t * s.1 * t)) * d⁻¹ * (d * t * d⁻¹) =
          d * ((s.1 * (t * s.1 * t)) * t) * d⁻¹ := by group
      have e2 : d * t * d⁻¹ * (d * (s.1 * (t * s.1 * t)) * d⁻¹) =
          d * (t * (s.1 * (t * s.1 * t))) * d⁻¹ := by group
      rw [e1, e2, h.diag_comm s.2]
    have hmem := h.B x hxZ hx1 _ hwD hwx
    obtain ⟨a, ha, r, hr, e⟩ := (phi4B_mem_sup_iff (fun _ ha _ hb => hc.comm_SX ha hb)).1 hmem
    exact ⟨a, r, ha, hr, e⟩
  choose a r ha hr har using key
  have hmul : ∀ s s' : ↥(conjSub X₂ t), a (s * s') = a s * a s' := by
    intro s s'
    have hδ := h.diag_mul s.2 s'.2
    have e1 : a (s * s') * r (s * s') = (a s * a s') * (r s * r s') := by
      rw [← har (s * s')]
      have e2 : d * ((s * s' : ↥(conjSub X₂ t)).1 * (t * (s * s' : ↥(conjSub X₂ t)).1 * t)) *
          d⁻¹ = (d * (s.1 * (t * s.1 * t)) * d⁻¹) * (d * (s'.1 * (t * s'.1 * t)) * d⁻¹) := by
        have : d * ((s * s' : ↥(conjSub X₂ t)).1 * (t * (s * s' : ↥(conjSub X₂ t)).1 * t)) *
            d⁻¹ = d * ((s.1 * (t * s.1 * t)) * (s'.1 * (t * s'.1 * t))) * d⁻¹ := by
          rw [← hδ]
          rfl
        rw [this]
        group
      rw [e2, har s, har s']
      have hcm : r s * a s' = a s' * r s := (hc.comm_SX (ha s') (hr s)).symm
      calc a s * r s * (a s' * r s') = a s * (r s * a s') * r s' := by simp only [mul_assoc]
        _ = a s * (a s' * r s) * r s' := by rw [hcm]
        _ = a s * a s' * (r s * r s') := by simp only [mul_assoc]
    exact (hc.mul_inj (hc.S₁_le (ha (s * s'))) (hc.S₁_le (mul_mem (ha s) (ha s')))
      (hr (s * s')) (mul_mem (hr s) (hr s')) e1).1
  have hperf₁ : ⁅conjSub X₂ t, conjSub X₂ t⁆ = conjSub X₂ t := by
    unfold conjSub
    rw [← Subgroup.map_commutator, h.perf]
  have : Group.IsPerfect ↥(conjSub X₂ t) := Subgroup.isPerfect_iff.2 hperf₁
  have : Finite ↥(conjSub S₂ t) :=
    Nat.finite_of_card_ne_zero (by rw [hc.suz₁.card_S]; have := hc.q_ge; positivity)
  have : Group.IsNilpotent ↥(conjSub S₂ t) := h.S₁_isPGroup.isNilpotent
  let f : ↥(conjSub X₂ t) →* ↥(conjSub S₂ t) :=
    MonoidHom.mk' (fun s => ⟨a s, ha s⟩) (fun s s' => Subtype.ext (hmul s s'))
  have hatriv : ∀ s : ↥(conjSub X₂ t), a s = 1 := fun s =>
    congrArg Subtype.val (phi4B_hom_one f s)
  obtain ⟨z, hz, hz1⟩ := hc.Z₁_ne
  have hzX : z ∈ conjSub X₂ t := hc.S₁_le (hc.Z₁_le hz)
  have hτz : t * z * t ∈ Z₂ := phi4B_tau_mem' hc.t_sq hz
  have hτz1 : t * z * t ≠ 1 := hc.tau_ne_one hz1
  have hρ := har ⟨z, hzX⟩
  rw [hatriv ⟨z, hzX⟩, one_mul] at hρ
  have hρX : r ⟨z, hzX⟩ ∈ X₂ := hr _
  have hδΩ : z * (t * z * t) ∈ phi4B_Om Z₂ t := mul_mem (mem_sup_left hz) (mem_sup_right hτz)
  have hδ2 : (z * (t * z * t)) * (z * (t * z * t)) = 1 := hc.Om_sq hδΩ
  have hδ1 : z * (t * z * t) ≠ 1 := fun e =>
    hz1 (hc.eq_one_of_mul hzX (hc.S₂_le (hc.suz.Z_le hτz)) e).1
  have hρ2 : r ⟨z, hzX⟩ * r ⟨z, hzX⟩ = 1 := by
    have : r ⟨z, hzX⟩ * r ⟨z, hzX⟩ =
        d * ((z * (t * z * t)) * (z * (t * z * t))) * d⁻¹ := by
      rw [← hρ]
      group
    rw [this, hδ2]
    group
  have hρ1 : r ⟨z, hzX⟩ ≠ 1 := by
    intro e
    apply hδ1
    have : z * (t * z * t) = d⁻¹ * (d * (z * (t * z * t)) * d⁻¹) * d := by group
    rw [this]
    simp only [hρ]
    rw [e]
    group
  have hcl : cls (r ⟨z, hzX⟩) := h.cls₄ _ hρX hρ2 hρ1
  have hcl' := h.cls_conj d⁻¹ (inv_mem hdD) _ hcl
  have e : d⁻¹ * r ⟨z, hzX⟩ * d⁻¹⁻¹ = z * (t * z * t) := by
    rw [← hρ]
    group
  rw [e] at hcl'
  exact h.cls₃ z hz (t * z * t) hτz hz1 hτz1 hcl'

end phi4B_Ctx

theorem phi4_caseB_false {G : Type*} [Group G]
    (D X₂ S₂ Z₂ : Subgroup G) [Finite D] (t : G) (q : ℕ) (cls : G → Prop) (hq : 8 ≤ q)
    (ht2 : t * t = 1) (htD : t ∈ D) (hX₂D : X₂ ≤ D) (hX₁D : conjSub X₂ t ≤ D)
    (hcomm : ∀ x ∈ X₂, ∀ y ∈ conjSub X₂ t, x * y = y * x) (hinf : X₂ ⊓ conjSub X₂ t = ⊥)
    (hperf : ⁅X₂, X₂⁆ = X₂) (hS₂X : S₂ ≤ X₂)
    (hS₂syl : ∀ P : Subgroup G, P ≤ X₂ → IsPGroup 2 P → S₂ ≤ P → P = S₂)
    (hS₂ : SuzukiTwo q S₂ Z₂)
    (hcls : ∀ g ∈ D, ∀ x, cls x → cls (g * x * g⁻¹)) (hclst : cls t)
    (hcls₂ : ∀ z ∈ Z₂, z ≠ 1 → cls z)
    (hcls₃ : ∀ z₁ ∈ conjSub Z₂ t, ∀ z₂ ∈ Z₂, z₁ ≠ 1 → z₂ ≠ 1 → ¬ cls (z₁ * z₂))
    (hcls₄ : ∀ x ∈ X₂, x * x = 1 → x ≠ 1 → cls x)
    (hB : ∀ z ∈ conjSub Z₂ t, z ≠ 1 → ∀ x ∈ D, x * z = z * x → x ∈ conjSub S₂ t ⊔ X₂)
    (hN : ∀ n ∈ D, (∃ k : ℕ, orderOf n = 2 ^ k) →
      (∀ z ∈ conjSub Z₂ t, n * z * n⁻¹ ∈ conjSub Z₂ t) →
      ∀ z ∈ conjSub Z₂ t, n * z = z * n)
    (hsq : ∃ y ∈ D, y * y = t) : False :=
  phi4B_Ctx.B5
    { core := { q_ge := hq, t_sq := ht2, comm := hcomm, inf := hinf, S₂_le := hS₂X, suz := hS₂ }
      tD := htD
      X₂D := hX₂D
      X₁D := hX₁D
      perf := hperf
      S₂syl := hS₂syl
      cls_conj := hcls
      cls_t := hclst
      cls₂ := hcls₂
      cls₃ := hcls₃
      cls₄ := hcls₄
      B := hB
      N := hN
      sq := hsq }

end CFSG.RankThree.PartOne.SEITZ12
