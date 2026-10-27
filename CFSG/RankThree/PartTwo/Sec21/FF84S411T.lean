module

public import CFSG.RankThree.PartTwo.Sec21.FF84S411Ext

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {e : ↥S ≃* Multiplicative F6}
  {ψ : ↥(Nor S) →* OmG} {s t : ↥S} {b : G}

theorem eichVec_all : ∀ w : F6, polarMinus w tau0 = 0 →
    (∀ x : F6, eichVec x w = 0 ∨ eichVec x w = tau0) → w = 0 ∨ w = tau0 := by
  decide +kernel

section
variable (C : Ctx411 S e ψ s t b)
include C

theorem Ctx411.E_eq_one_of_move {g : OmG} (hg : g ∈ Eτ)
    (h : ∀ v : F6, g • v - v = 0 ∨ g • v - v = tau0) : g = 1 := by
  obtain ⟨w, hw, hx⟩ := Eτ_apply C.hE hg
  have h2 : ∀ x : F6, eichVec x w = 0 ∨ eichVec x w = tau0 := fun x => by
    rw [← hx x]
    exact h x
  have h3 := eichVec_all w hw h2
  have h4 : ∀ x : F6, g • x = x := by
    intro x
    have : g • x - x = 0 := by
      rw [hx x]
      rcases h3 with rfl | rfl
      · exact eichVec_zero x
      · exact eichVec_tau0 x
    exact sub_eq_zero.1 this
  exact (C.hPar qMinus_tau0 tau0_ne_zero).2.2.1 g (fun x _ => h4 x)

theorem Ctx411.vec_of_one_or_t {c : G} (h : c = 1 ∨ c = (t : G)) :
    vecOf e c = 0 ∨ vecOf e c = tau0 := by
  rcases h with rfl | rfl
  · left
    exact vecOf_one
  · right
    rw [vecOf_of_mem t.2]
    exact C.het

theorem Ctx411.S_le_cen_t : S ≤ Cen (t : G) := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.2 (S_comm' e hx t.2)

theorem Ctx411.S_le_nor_T : S ≤ Nor (Op 2 (Cen (t : G))) := fun x hx =>
  le_nor_op2 (Cen (t : G)) (C.S_le_cen_t hx)

theorem Ctx411.S_le_nor_Rs : S ≤ Nor (Rstar S (t : G)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => C.Rs_conj (Subgroup.le_normalizer hx) (C.S_le_cen_t hx) hy
  · intro hy
    have := C.Rs_conj (Subgroup.le_normalizer (inv_mem hx)) (C.S_le_cen_t (inv_mem hx)) hy
    simpa [mul_assoc] using this

theorem Ctx411.isPGroup_S : IsPGroup 2 S := fun x =>
  ⟨1, by rw [pow_one, pow_two]; exact sq_S e x⟩

theorem Ctx411.isPGroup_P : IsPGroup 2 (Op 2 (Cen (t : G)) ⊔ S : Subgroup G) :=
  IsPGroup.to_sup_of_normal_left' (S3.Op_isPGroup 2 _) C.isPGroup_S C.S_le_nor_T

theorem Ctx411.P_le_cen_t : (Op 2 (Cen (t : G)) ⊔ S : Subgroup G) ≤ Cen (t : G) :=
  sup_le (S3.Op_le 2 _) C.S_le_cen_t

theorem Ctx411.mem_Q {x : G} (hx : x ∈ Rstar S (t : G) ⊔ S) :
    ∃ a ∈ Rstar S (t : G), ∃ σ ∈ S, a * σ = x := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left (Rstar S (t : G)) S C.S_le_nor_Rs
  have : x ∈ (↑(Rstar S (t : G) ⊔ S) : Set G) := hx
  rw [h] at this
  exact Set.mem_mul.1 this

theorem Ctx411.mem_P {x : G} (hx : x ∈ (Op 2 (Cen (t : G)) ⊔ S : Subgroup G)) :
    ∃ a ∈ Op 2 (Cen (t : G)), ∃ σ ∈ S, a * σ = x := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left (Op 2 (Cen (t : G))) S C.S_le_nor_T
  have : x ∈ (↑(Op 2 (Cen (t : G)) ⊔ S : Subgroup G) : Set G) := hx
  rw [h] at this
  exact Set.mem_mul.1 this

theorem Ctx411.mem_R_iff_Zt {z : G} :
    z ∈ S ⊓ Op 2 (Cen (t : G)) ↔ z ∈ Rstar S (t : G) ⊔ S ∧
      ∀ q ∈ Rstar S (t : G) ⊔ S, z * q * z⁻¹ * q⁻¹ = 1 ∨ z * q * z⁻¹ * q⁻¹ = (t : G) := by
  constructor
  · intro hz
    refine ⟨Subgroup.mem_sup_left (C.R_le_Rstar hz), ?_⟩
    intro q hq
    obtain ⟨a, ha, σ, hσ, rfl⟩ := C.mem_Q hq
    have hzS := (Subgroup.mem_inf.1 hz).1
    have hzT := (Subgroup.mem_inf.1 hz).2
    have hc : z * σ = σ * z := S_comm' e hzS hσ
    have h1 : σ * z⁻¹ = z⁻¹ * σ := (Commute.inv_right hc.symm).eq
    have h2 : z * (a * σ) * z⁻¹ * (a * σ)⁻¹ = z * a * z⁻¹ * a⁻¹ := by
      calc z * (a * σ) * z⁻¹ * (a * σ)⁻¹ = z * a * (σ * z⁻¹) * σ⁻¹ * a⁻¹ := by group
        _ = z * a * (z⁻¹ * σ) * σ⁻¹ * a⁻¹ := by rw [h1]
        _ = z * a * z⁻¹ * a⁻¹ := by group
    rw [h2]
    exact eq_one_or_of_vec (e := e) C.het (C.comm_mem_S (C.R_le_Rstar hz) ha)
      (C.comm_R_vec ha hzS hzT)
  · rintro ⟨hzQ, hz⟩
    obtain ⟨r, hr, σ₀, hσ₀, rfl⟩ := C.mem_Q hzQ
    have hrN := C.Rs_le_nor_S hr
    have hr1 : ψ ⟨r, hrN⟩ = 1 := by
      refine C.E_eq_one_of_move (C.psi_mem_E hr) (fun v => ?_)
      obtain ⟨q, hq⟩ : ∃ q : ↥S, Multiplicative.toAdd (e q) = v :=
        ⟨e.symm (Multiplicative.ofAdd v), by simp⟩
      have hqQ : (q : G) ∈ Rstar S (t : G) ⊔ S := Subgroup.mem_sup_right q.2
      have hc := hz _ hqQ
      have hσq : σ₀ * (q : G) = (q : G) * σ₀ := S_comm' e hσ₀ q.2
      have hx : r * σ₀ * (q : G) * (r * σ₀)⁻¹ * (q : G)⁻¹ = r * (q : G) * r⁻¹ * (q : G)⁻¹ := by
        have h1 : σ₀ * (q : G) * σ₀⁻¹ = q := by
          rw [hσq]
          group
        calc r * σ₀ * (q : G) * (r * σ₀)⁻¹ * (q : G)⁻¹
            = r * (σ₀ * (q : G) * σ₀⁻¹) * r⁻¹ * (q : G)⁻¹ := by group
          _ = r * (q : G) * r⁻¹ * (q : G)⁻¹ := by rw [h1]
      rw [hx] at hc
      have hv := C.vec_of_one_or_t hc
      have hrq : r * (q : G) * r⁻¹ ∈ S := C.conj_mem_S hr q.2
      rw [vecOf_mul hrq (inv_mem q.2), C.vec_conj_Rs hr q.2, vecOf_inv q.2,
        vecOf_of_mem q.2, hq] at hv
      have h3 : ψ ⟨r, hrN⟩ • v + v = ψ ⟨r, hrN⟩ • v - v := by
        rw [sub_eq_add_neg, F6_neg]
      rw [← h3]
      exact hv
    have hrS : r ∈ S := (C.H.psi_eq_one_iff _).1 hr1
    have hzS : r * σ₀ ∈ S := S.mul_mem hrS hσ₀
    refine Subgroup.mem_inf.2 ⟨hzS, ?_⟩
    have hperp : polarMinus (vecOf e (r * σ₀)) tau0 = 0 := by
      by_contra hne
      have h1 := zmod_two_eq_one_of_ne_zero _ hne
      obtain ⟨g, hg, hg1, hg2⟩ := eich_not_move C.hE h1
      obtain ⟨k, hk⟩ := C.liftG_spec hg
      have hkQ : liftG ψ (t : G) g ∈ Rstar S (t : G) ⊔ S := Subgroup.mem_sup_left k
      have hc := hz _ hkQ
      have hmem : (liftG ψ (t : G) g) * (r * σ₀)⁻¹ * (liftG ψ (t : G) g)⁻¹ ∈ S :=
        C.conj_mem_S k (inv_mem hzS)
      have hid : r * σ₀ * liftG ψ (t : G) g * (r * σ₀)⁻¹ * (liftG ψ (t : G) g)⁻¹ =
          (r * σ₀) * (liftG ψ (t : G) g * (r * σ₀)⁻¹ * (liftG ψ (t : G) g)⁻¹) := by group
      rw [hid] at hc
      have hv := C.vec_of_one_or_t hc
      rw [vecOf_mul hzS hmem, C.vec_conj_Rs k (inv_mem hzS), vecOf_inv hzS, hk] at hv
      have h3 : vecOf e (r * σ₀) + g • vecOf e (r * σ₀) = g • vecOf e (r * σ₀) - vecOf e (r * σ₀) := by
        rw [sub_eq_add_neg, F6_neg, add_comm]
      rw [h3] at hv
      rcases hv with hv | hv
      · exact hg1 hv
      · exact hg2 hv
    have := (C.R_perp ⟨r * σ₀, hzS⟩).2 (by rw [← vecOf_of_mem hzS]; exact hperp)
    exact this

theorem Ctx411.nor_R_of_nor_Q {x : G} (hxQ : x ∈ Nor (Rstar S (t : G) ⊔ S))
    (hxt : x ∈ Cen (t : G)) : x ∈ Nor (S ⊓ Op 2 (Cen (t : G))) := by
  have key : ∀ y : G, y ∈ Nor (Rstar S (t : G) ⊔ S) → y ∈ Cen (t : G) →
      ∀ z, z ∈ S ⊓ Op 2 (Cen (t : G)) → y * z * y⁻¹ ∈ S ⊓ Op 2 (Cen (t : G)) := by
    intro y hy hyt z hz
    have hzQ := ((C.mem_R_iff_Zt).1 hz).1
    have hz2 := ((C.mem_R_iff_Zt).1 hz).2
    rw [C.mem_R_iff_Zt]
    refine ⟨(Subgroup.mem_normalizer_iff.1 hy z).1 hzQ, ?_⟩
    intro q hq
    have hq' : y⁻¹ * q * y ∈ Rstar S (t : G) ⊔ S := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) q).1 hq
      simpa using this
    have hc := hz2 _ hq'
    have hid : y * z * y⁻¹ * q * (y * z * y⁻¹)⁻¹ * q⁻¹ =
        y * (z * (y⁻¹ * q * y) * z⁻¹ * (y⁻¹ * q * y)⁻¹) * y⁻¹ := by group
    have hyt' : y * (t : G) = (t : G) * y := Subgroup.mem_centralizer_singleton_iff.1 hyt
    rw [hid]
    rcases hc with hc | hc
    · left
      rw [hc]
      group
    · right
      rw [hc]
      calc y * (t : G) * y⁻¹ = (t : G) * y * y⁻¹ := by rw [hyt']
        _ = (t : G) := by group
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact fun hz => key x hxQ hxt z hz
  · intro hz
    have := key x⁻¹ (inv_mem hxQ) (inv_mem hxt) _ hz
    simpa [mul_assoc] using this

theorem Ctx411.T_le_Rstar : Op 2 (Cen (t : G)) ≤ Rstar S (t : G) := by
  have hQP : Rstar S (t : G) ⊔ S ≤ (Op 2 (Cen (t : G)) ⊔ S : Subgroup G) :=
    sup_le_sup_right inf_le_left S
  have hPQ : (Op 2 (Cen (t : G)) ⊔ S : Subgroup G) ≤ Rstar S (t : G) ⊔ S := by
    by_contra hne
    obtain ⟨x, hx, hxn⟩ := exists_mem_nor_not_mem C.isPGroup_P hQP hne
    obtain ⟨hxP, hxN⟩ := Subgroup.mem_inf.1 hx
    have hxt : x ∈ Cen (t : G) := C.P_le_cen_t hxP
    have hxR := C.nor_R_of_nor_Q hxN hxt
    obtain ⟨a, ha, σ, hσ, rfl⟩ := C.mem_P hxP
    have hσR : σ ∈ Nor (S ⊓ Op 2 (Cen (t : G))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have : σ * z * σ⁻¹ = z := by
            rw [S_comm' e hσ (Subgroup.mem_inf.1 hz).1]
            group
          rw [this]
          exact (Subgroup.mem_inf.1 hz).1
        · exact S3.Op_conj_mem 2 (Subgroup.le_normalizer (C.S_le_cen_t hσ))
            (Subgroup.mem_inf.1 hz).2
      · intro hz
        have h1 : σ * z * σ⁻¹ ∈ S := (Subgroup.mem_inf.1 hz).1
        have h2 : σ * z * σ⁻¹ = z := by
          have hzS : z ∈ S := by
            have := S.mul_mem (S.mul_mem (inv_mem hσ) h1) hσ
            simpa [mul_assoc] using this
          rw [S_comm' e hσ hzS]
          group
        rw [h2] at hz
        exact hz
    have haR : a ∈ Nor (S ⊓ Op 2 (Cen (t : G))) := by
      have := mul_mem hxR (inv_mem hσR)
      simpa [mul_assoc] using this
    have haRs : a ∈ Rstar S (t : G) := Subgroup.mem_inf.2 ⟨ha, haR⟩
    exact hxn (Subgroup.mul_mem _ (Subgroup.mem_sup_left haRs) (Subgroup.mem_sup_right hσ))
  intro x hx
  have hxP : x ∈ (Op 2 (Cen (t : G)) ⊔ S : Subgroup G) := Subgroup.mem_sup_left hx
  obtain ⟨r, hr, σ, hσ, hrσ⟩ := C.mem_Q (hPQ hxP)
  have hσT : σ ∈ Op 2 (Cen (t : G)) := by
    have h1 : σ = r⁻¹ * x := by rw [← hrσ]; group
    rw [h1]
    exact mul_mem (inv_mem (Subgroup.mem_inf.1 hr).1) hx
  have hσR : σ ∈ Rstar S (t : G) := C.R_le_Rstar (Subgroup.mem_inf.2 ⟨hσ, hσT⟩)
  rw [← hrσ]
  exact mul_mem hr hσR

theorem Ctx411.T_eq : Op 2 (Cen (t : G)) = Rstar S (t : G) :=
  le_antisymm C.T_le_Rstar inf_le_left

end

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
