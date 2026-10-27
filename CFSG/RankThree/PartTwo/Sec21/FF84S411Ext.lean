module

public import CFSG.RankThree.PartTwo.Sec21.FF84S411Comm
public import CFSG.LargeExtraspecial.S9FiveB

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {e : ↥S ≃* Multiplicative F6}
  {ψ : ↥(Nor S) →* OmG} {s t : ↥S} {b : G}

@[expose] noncomputable def liftG (ψ : ↥(Nor S) →* OmG) (t : G) (g : OmG) : G := by
  classical exact
    if h : ∃ y : G, ∃ hy : y ∈ Nor S, y ∈ Rstar S t ∧ ψ ⟨y, hy⟩ = g then Classical.choose h else 1

section
variable (C : Ctx411 S e ψ s t b)
include C

theorem Ctx411.liftG_spec {g : OmG} (hg : g ∈ Eτ) :
    ∃ hy : liftG ψ (t : G) g ∈ Rstar S (t : G), ψ ⟨liftG ψ (t : G) g, C.Rs_le_nor_S hy⟩ = g := by
  have hex : ∃ y : G, ∃ hy : y ∈ Nor S, y ∈ Rstar S (t : G) ∧ ψ ⟨y, hy⟩ = g := by
    rw [← C.psi_Rs_eq] at hg
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hg
    exact ⟨n.1, n.2, hn, rfl⟩
  have hL : liftG ψ (t : G) g = Classical.choose hex := by
    unfold liftG
    exact dif_pos hex
  obtain ⟨hy', hR, hψ⟩ := Classical.choose_spec hex
  have hR' : liftG ψ (t : G) g ∈ Rstar S (t : G) := by rw [hL]; exact hR
  refine ⟨hR', ?_⟩
  have : ∀ (z : G) (hz : z ∈ Nor S), z = Classical.choose hex → ψ ⟨z, hz⟩ = g := by
    rintro z hz rfl
    exact hψ
  exact this _ _ hL

theorem Ctx411.Fc_zero {y₁ y₂ : G} (h₁ : y₁ ∈ Rstar S (t : G)) (h₂ : y₂ ∈ Rstar S (t : G)) :
    Fc e y₁ y₂ = 0 := by
  let F : OmG → OmG → F6 := fun g₁ g₂ => Fc e (liftG ψ (t : G) g₁) (liftG ψ (t : G) g₂)
  have hW : ∀ g₁ ∈ Eτ, ∀ g₂ ∈ Eτ,
      polarMinus (F g₁ g₂) sig0 = 0 ∧ polarMinus (F g₁ g₂) tau0 = 0 := by
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨k₁, -⟩ := C.liftG_spec hg₁
    obtain ⟨k₂, -⟩ := C.liftG_spec hg₂
    exact prW_mem _ (C.vec_perp (C.comm_mem_S k₁ k₂) (C.comm_mem_T k₁ k₂))
  have hA1 : ∀ g₁ ∈ Eτ, ∀ g₁' ∈ Eτ, ∀ g₂ ∈ Eτ, F (g₁ * g₁') g₂ = F g₁ g₂ + F g₁' g₂ := by
    intro g₁ hg₁ g₁' hg₁' g₂ hg₂
    have hg12 : g₁ * g₁' ∈ Eτ := mul_mem hg₁ hg₁'
    obtain ⟨k, hk⟩ := C.liftG_spec hg12
    obtain ⟨k₁, hk₁⟩ := C.liftG_spec hg₁
    obtain ⟨k₁', hk₁'⟩ := C.liftG_spec hg₁'
    obtain ⟨k₂, -⟩ := C.liftG_spec hg₂
    have hk11 : liftG ψ (t : G) g₁ * liftG ψ (t : G) g₁' ∈ Rstar S (t : G) := mul_mem k₁ k₁'
    have hψ : ψ ⟨liftG ψ (t : G) (g₁ * g₁'), C.Rs_le_nor_S k⟩ =
        ψ ⟨liftG ψ (t : G) g₁ * liftG ψ (t : G) g₁', C.Rs_le_nor_S hk11⟩ := by
      have : (⟨liftG ψ (t : G) g₁ * liftG ψ (t : G) g₁', C.Rs_le_nor_S hk11⟩ : ↥(Nor S)) =
          ⟨liftG ψ (t : G) g₁, C.Rs_le_nor_S k₁⟩ * ⟨liftG ψ (t : G) g₁', C.Rs_le_nor_S k₁'⟩ := rfl
      rw [this, map_mul, hk, hk₁, hk₁']
    show Fc e (liftG ψ (t : G) (g₁ * g₁')) _ = Fc e _ _ + Fc e _ _
    rw [C.Fc_congr_left k hk11 k₂ hψ, C.Fc_mul_left k₁ k₂ k₁']
  have hA2 : ∀ g₁ ∈ Eτ, ∀ g₂ ∈ Eτ, ∀ g₂' ∈ Eτ, F g₁ (g₂ * g₂') = F g₁ g₂ + F g₁ g₂' := by
    intro g₁ hg₁ g₂ hg₂ g₂' hg₂'
    have hg22 : g₂ * g₂' ∈ Eτ := mul_mem hg₂ hg₂'
    obtain ⟨k, hk⟩ := C.liftG_spec hg22
    obtain ⟨k₂, hk₂⟩ := C.liftG_spec hg₂
    obtain ⟨k₂', hk₂'⟩ := C.liftG_spec hg₂'
    obtain ⟨k₁, -⟩ := C.liftG_spec hg₁
    have hk22 : liftG ψ (t : G) g₂ * liftG ψ (t : G) g₂' ∈ Rstar S (t : G) := mul_mem k₂ k₂'
    have hψ : ψ ⟨liftG ψ (t : G) (g₂ * g₂'), C.Rs_le_nor_S k⟩ =
        ψ ⟨liftG ψ (t : G) g₂ * liftG ψ (t : G) g₂', C.Rs_le_nor_S hk22⟩ := by
      have : (⟨liftG ψ (t : G) g₂ * liftG ψ (t : G) g₂', C.Rs_le_nor_S hk22⟩ : ↥(Nor S)) =
          ⟨liftG ψ (t : G) g₂, C.Rs_le_nor_S k₂⟩ * ⟨liftG ψ (t : G) g₂', C.Rs_le_nor_S k₂'⟩ := rfl
      rw [this, map_mul, hk, hk₂, hk₂']
    show Fc e _ (liftG ψ (t : G) (g₂ * g₂')) = Fc e _ _ + Fc e _ _
    rw [C.Fc_congr_right k hk22 k₁ hψ, C.Fc_mul_right k₁ k₂ k₂']
  have hA3 : ∀ g ∈ Eτ, F g g = 0 := fun g _ => C.Fc_self _
  have hA4 : ∀ h ∈ P2, ∀ g₁ ∈ Eτ, ∀ g₂ ∈ Eτ, F (h * g₁ * h⁻¹) (h * g₂ * h⁻¹) = h • F g₁ g₂ := by
    intro h hh g₁ hg₁ g₂ hg₂
    obtain ⟨⟨m, hm⟩, hmφ⟩ := phiM_surj C.H C.hes C.het ⟨h, hh⟩
    have hmN : m ∈ Nor S := M_le_nor C.H C.hes C.het hm
    have hmψ : ψ ⟨m, hmN⟩ = h := by
      have := congrArg Subtype.val hmφ
      exact this
    have hmt : m ∈ Cen (t : G) := by
      rw [cenS_pair, Subgroup.mem_centralizer_iff] at hm
      exact Subgroup.mem_centralizer_singleton_iff.2 (hm _ (by simp)).symm
    have hc1 : h * g₁ * h⁻¹ ∈ Eτ := eich_conj_P2 hg₁ hh
    have hc2 : h * g₂ * h⁻¹ ∈ Eτ := eich_conj_P2 hg₂ hh
    obtain ⟨z₁, hz₁⟩ := C.liftG_spec hc1
    obtain ⟨z₂, hz₂⟩ := C.liftG_spec hc2
    obtain ⟨k₁, hk₁⟩ := C.liftG_spec hg₁
    obtain ⟨k₂, hk₂⟩ := C.liftG_spec hg₂
    have hq₁ : m * liftG ψ (t : G) g₁ * m⁻¹ ∈ Rstar S (t : G) := C.Rs_conj hmN hmt k₁
    have hq₂ : m * liftG ψ (t : G) g₂ * m⁻¹ ∈ Rstar S (t : G) := C.Rs_conj hmN hmt k₂
    have hψ1 : ψ ⟨liftG ψ (t : G) (h * g₁ * h⁻¹), C.Rs_le_nor_S z₁⟩ =
        ψ ⟨m * liftG ψ (t : G) g₁ * m⁻¹, C.Rs_le_nor_S hq₁⟩ := by
      have : (⟨m * liftG ψ (t : G) g₁ * m⁻¹, C.Rs_le_nor_S hq₁⟩ : ↥(Nor S)) =
          ⟨m, hmN⟩ * ⟨liftG ψ (t : G) g₁, C.Rs_le_nor_S k₁⟩ * ⟨m, hmN⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hmψ, hk₁, hz₁]
    have hψ2 : ψ ⟨liftG ψ (t : G) (h * g₂ * h⁻¹), C.Rs_le_nor_S z₂⟩ =
        ψ ⟨m * liftG ψ (t : G) g₂ * m⁻¹, C.Rs_le_nor_S hq₂⟩ := by
      have : (⟨m * liftG ψ (t : G) g₂ * m⁻¹, C.Rs_le_nor_S hq₂⟩ : ↥(Nor S)) =
          ⟨m, hmN⟩ * ⟨liftG ψ (t : G) g₂, C.Rs_le_nor_S k₂⟩ * ⟨m, hmN⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hmψ, hk₂, hz₂]
    show Fc e (liftG ψ (t : G) (h * g₁ * h⁻¹)) (liftG ψ (t : G) (h * g₂ * h⁻¹)) =
      h • Fc e (liftG ψ (t : G) g₁) (liftG ψ (t : G) g₂)
    rw [C.Fc_congr_left z₁ hq₁ z₂ hψ1, C.Fc_congr_right z₂ hq₂ hq₁ hψ2, ← hmψ]
    exact C.Fc_conj k₁ k₂ hmN hmt (by rw [hmψ]; exact hh)
  have key := C.hNoAlt F hW hA1 hA2 hA3 hA4 (ψ ⟨y₁, C.Rs_le_nor_S h₁⟩) (C.psi_mem_E h₁)
    (ψ ⟨y₂, C.Rs_le_nor_S h₂⟩) (C.psi_mem_E h₂)
  obtain ⟨l₁, hl₁⟩ := C.liftG_spec (C.psi_mem_E h₁)
  obtain ⟨l₂, hl₂⟩ := C.liftG_spec (C.psi_mem_E h₂)
  have e1 := C.Fc_congr_left l₁ h₁ l₂ hl₁
  have e2 := C.Fc_congr_right l₂ h₂ h₁ hl₂
  have : Fc e y₁ y₂ = F (ψ ⟨y₁, C.Rs_le_nor_S h₁⟩) (ψ ⟨y₂, C.Rs_le_nor_S h₂⟩) :=
    e2.symm.trans e1.symm
  rw [this]
  exact key

theorem Ctx411.comm_vec_mem {y₁ y₂ : G} (h₁ : y₁ ∈ Rstar S (t : G))
    (h₂ : y₂ ∈ Rstar S (t : G)) : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ = 1 ∨ y₁ * y₂ * y₁⁻¹ * y₂⁻¹ = (t : G) := by
  have h0 := C.Fc_zero h₁ h₂
  unfold Fc at h0
  exact eq_one_or_of_vec (e := e) C.het (C.comm_mem_S h₁ h₂) (prW_eq_zero _ h0)

theorem Ctx411.center_le {z : G} (hz : z ∈ Rstar S (t : G))
    (hc : ∀ y ∈ Rstar S (t : G), z * y = y * z) : z = 1 ∨ z = (t : G) := by
  have hzS : z ∈ S := by
    have : z ∈ CenS (S ⊓ Op 2 (Cen (t : G))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (hc r (C.R_le_Rstar hr)).symm
    rwa [C.CR] at this
  have hzT : z ∈ Op 2 (Cen (t : G)) := (Subgroup.mem_inf.1 hz).1
  have hv : polarMinus (vecOf e z) tau0 = 0 := C.vec_perp hzS hzT
  have hf : ∀ g ∈ Eτ, g • vecOf e z = vecOf e z := by
    intro g hg
    obtain ⟨k, hk⟩ := C.liftG_spec hg
    have hcomm : (liftG ψ (t : G) g) * z = z * (liftG ψ (t : G) g) := (hc _ k).symm
    have := (C.H.comm_iff ⟨liftG ψ (t : G) g, C.Rs_le_nor_S k⟩ ⟨z, hzS⟩).1 hcomm
    rw [hk] at this
    rw [vecOf_of_mem hzS]
    exact this
  exact eq_one_or_of_vec (e := e) C.het hzS (eich_fixed C.hE hv hf)

theorem Ctx411.t_mem_Rstar : (t : G) ∈ Rstar S (t : G) :=
  C.R_le_Rstar (Subgroup.mem_inf.2 ⟨t.2, t_mem_T e C.ht1⟩)

theorem Ctx411.tt : (t : G) * t = 1 := congrArg Subtype.val (sq_S e t)

theorem Ctx411.sq_mem {x : G} (hx : x ∈ Rstar S (t : G)) : x * x = 1 ∨ x * x = (t : G) := by
  have hxt : ∀ y ∈ Rstar S (t : G), y * (t : G) = (t : G) * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.1 (S3.Op_le 2 _ (Subgroup.mem_inf.1 hy).1)
  refine C.center_le (mul_mem hx hx) ?_
  intro y hy
  rcases C.comm_vec_mem hx hy with h | h
  · have : x * y = y * x := by
      have h2 : x * y * x⁻¹ = y := by
        have := congrArg (fun w => w * y) h
        simpa [mul_assoc] using this
      calc x * y = (x * y * x⁻¹) * x := by group
        _ = y * x := by rw [h2]
    calc x * x * y = x * (x * y) := by group
      _ = x * (y * x) := by rw [this]
      _ = (x * y) * x := by group
      _ = y * x * x := by rw [this]
      _ = y * (x * x) := by group
  · have h2 : x * y = (t : G) * (y * x) := by
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = (t : G) * (y * x) := by rw [h]
    have ht := C.tt
    calc x * x * y = x * (x * y) := by group
      _ = x * ((t : G) * (y * x)) := by rw [h2]
      _ = ((t : G) * x) * (y * x) := by
        rw [← hxt x hx]
        group
      _ = (t : G) * (x * y) * x := by group
      _ = (t : G) * ((t : G) * (y * x)) * x := by rw [h2]
      _ = ((t : G) * t) * (y * x) * x := by group
      _ = y * (x * x) := by rw [ht]; group

theorem Ctx411.Rstar_extraspecial : IsExtraspecialPlus 4 (Rstar S (t : G)) := by
  let tR : ↥(Rstar S (t : G)) := ⟨(t : G), C.t_mem_Rstar⟩
  have hord : orderOf tR = 2 := by
    rw [← Subgroup.orderOf_coe tR]
    have := orderOf_t (t := t) e C.ht1
    exact this
  have hZ : Nat.card ↥(Subgroup.zpowers tR) = 2 := by rw [Nat.card_zpowers, hord]
  have hZc : Subgroup.zpowers tR ≤ Subgroup.center ↥(Rstar S (t : G)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (S3.Op_le 2 _ (Subgroup.mem_inf.1 y.2).1)
  have hcomm : ∀ x y : ↥(Rstar S (t : G)), ⁅x, y⁆ ∈ Subgroup.zpowers tR := by
    intro x y
    rcases C.comm_vec_mem x.2 y.2 with h | h
    · have : ⁅x, y⁆ = 1 := Subtype.ext h
      rw [this]
      exact Subgroup.one_mem _
    · have : ⁅x, y⁆ = tR := Subtype.ext h
      rw [this]
      exact Subgroup.mem_zpowers _
  have hmemZ : ∀ x : ↥(Rstar S (t : G)), ((x : G) = 1 ∨ (x : G) = (t : G)) →
      x ∈ Subgroup.zpowers tR := by
    intro x hx
    rcases hx with h | h
    · have : x = 1 := Subtype.ext h
      rw [this]
      exact Subgroup.one_mem _
    · have : x = tR := Subtype.ext h
      rw [this]
      exact Subgroup.mem_zpowers _
  have hsq : ∀ x : ↥(Rstar S (t : G)), x ^ 2 ∈ Subgroup.zpowers tR := by
    intro x
    apply hmemZ
    rw [pow_two]
    exact C.sq_mem x.2
  have hcent : ∀ x : ↥(Rstar S (t : G)), (∀ y, x * y = y * x) → x ∈ Subgroup.zpowers tR := by
    intro x hx
    apply hmemZ
    exact C.center_le x.2 (fun y hy => congrArg Subtype.val (hx ⟨y, hy⟩))
  have hnab : ∃ x : ↥(Rstar S (t : G)), x ∉ Subgroup.zpowers tR := by
    by_contra hcon
    push Not at hcon
    have h1 : (⊤ : Subgroup ↥(Rstar S (t : G))) ≤ Subgroup.zpowers tR := fun x _ => hcon x
    have h2 := Subgroup.card_le_of_le h1
    rw [Subgroup.card_top, C.card_Rs, hZ] at h2
    omega
  have hP : IsPGroup 2 ↥(Rstar S (t : G)) := (S3.Op_isPGroup 2 _).to_le inf_le_left
  refine ⟨CFSG.LargeExtraspecial.S9.isExtraspecialPGroup_of_center hP hZ hZc hcomm hsq hcent hnab,
    ?_, S ⊓ Op 2 (Cen (t : G)), C.R_le_Rs, isEA_of_le C.hSE inf_le_left, ?_⟩
  · rw [C.card_Rs]
    norm_num
  · rw [C.card_R]
    norm_num

end

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
