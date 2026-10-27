module

public import CFSG.Quasithin.EmptyFaithful.S143HB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise

namespace S143

section Util

variable {G : Type} [Group G]

theorem mem_zpowers_of_mul_self_eq_one {b z : G} (hb : b * b = 1) (hz : z ∈ Subgroup.zpowers b) :
    z = 1 ∨ z = b := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have ht2 : b ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hb
  rw [zpow_eq_zpow_emod k ht2]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left; rw [hk, zpow_zero]
  · right; rw [hk, zpow_one]

end Util

section Complement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2

theorem Counter.exists_complement_rOf_sup_uOfL22 {t : G} (htT : t ∈ T)
    (htRQ : t ∉ rOf T M ⊔ qOf T) :
    ∃ C₀ : Subgroup G, C₀ ≤ rOf T M ⊔ uOfL22 T M ∧ c.Ac hrW hrV hr2 ⊓ C₀ = ⊥ ∧
      c.Ac hrW hrV hr2 ⊔ C₀ = rOf T M ⊔ uOfL22 T M := by
  have h := c.h1281
  obtain ⟨u, huU, huW, hu2⟩ := c.exists_involution_not_mem_wOfU
  have hr'W := c.conj_mem_wOfU hrW htT
  have hr'V := c.conj_not_mem_VZ hrV htT
  have hr'2 : (t⁻¹ * r * t) * (t⁻¹ * r * t) = 1 := Counter.conj_sq hr2
  set r' : G := t⁻¹ * r * t with hr'def
  have hAt : c.Ac hr'W hr'V hr'2 = conjSubgroup (c.Ac hrW hrV hr2) t :=
    c.Ac_conj_eq hrW hrV hr2 htT
  have hVA : VZ T M ≤ c.Ac hrW hrV hr2 := c.VZ_le_Ac hrW hrV hr2
  have hVAt : VZ T M ≤ c.Ac hr'W hr'V hr'2 := c.VZ_le_Ac hr'W hr'V hr'2
  have hinf : c.Ac hrW hrV hr2 ⊓ c.Ac hr'W hr'V hr'2 = VZ T M := by
    rw [hAt]; exact c.Ac_inf_conj hrW hrV hr2 htT htRQ
  have hsup : c.Ac hrW hrV hr2 ⊔ c.Ac hr'W hr'V hr'2 = rOf T M := by
    rw [hAt]; exact c.Ac_sup_conj hrW hrV hr2 htT htRQ
  set At := c.Ac hr'W hr'V hr'2 with hAtdef
  set A := c.Ac hrW hrV hr2 with hAdef
  have hAtR : At ≤ rOf T M := c.Ac_le_rOf hr'W hr'V hr'2
  have hAR : A ≤ rOf T M := c.Ac_le_rOf hrW hrV hr2
  set b : G := g * r' * g⁻¹ with hbdef
  have hbAt : b ∈ At := c.r1_mem_Ac hr'W hr'V hr'2
  have hr2At : g * g * r' * (g * g)⁻¹ ∈ At := c.r2_mem_Ac hr'W hr'V hr'2
  have hr'At : r' ∈ At := c.r_mem_Ac hr'W hr'V hr'2
  have UD := c.udata hr'W hr'V hr'2 huU huW
  have hf : (u * b * u⁻¹)⁻¹ * (g * g * r' * (g * g)⁻¹) ∈ VZ T M := by
    have := c.quotSetting.normal
    have h2 := (c.kdata hr'W hr'V hr'2).conj_r1 UD
    rwa [E_eq_VZ c] at h2
  set f : G := (u * b * u⁻¹)⁻¹ * (g * g * r' * (g * g)⁻¹) with hfdef
  set b' : G := u * b * u⁻¹ with hb'def
  have hb'f : b' = (g * g * r' * (g * g)⁻¹) * f⁻¹ := by rw [hfdef]; group
  have hb'At : b' ∈ At := by
    rw [hb'f]; exact At.mul_mem hr2At (At.inv_mem (hVAt hf))
  have hbb : b * b = 1 := c.sq_Ac hr'W hr'V hr'2 hbAt
  have hb'b' : b' * b' = 1 := c.sq_Ac hr'W hr'V hr'2 hb'At
  have hcommAt : ∀ x ∈ At, ∀ y ∈ At, x * y = y * x := fun x hx y hy =>
    mul_comm_of_sq_eq_one (fun z hz => c.sq_Ac hr'W hr'V hr'2 hz) hx hy
  have hbb' : b * b' = b' * b := hcommAt b hbAt b' hb'At
  have huu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hub'u : u * b' * u⁻¹ = b := by
    rw [hb'def, huu]
    calc u * (u * b * u) * u = (u * u) * b * (u * u) := by group
      _ = b := by rw [hu2]; group
  have hnorm : r' * b * (g * g * r' * (g * g)⁻¹) ∈ VZ T M := c.norm_mem_VZ hr'W hr'V hr'2
  have hgN : ∀ v ∈ VZ T M, g * v * g⁻¹ ∈ VZ T M := by
    intro v hv
    have hgN' : g ∈ Subgroup.normalizer (VZ T M : Set G) := by
      rw [h.normalizer_VZ]; exact h.le c.goodElt.mem
    exact (Subgroup.mem_normalizer_iff.mp hgN' v).mp hv
  have hgN' : ∀ v ∈ VZ T M, g⁻¹ * v * g ∈ VZ T M := by
    intro v hv
    have hgN'' : g⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) := by
      rw [h.normalizer_VZ]; exact h.le ((yOfL22 T M).inv_mem c.goodElt.mem)
    have := (Subgroup.mem_normalizer_iff.mp hgN'' v).mp hv
    simpa using this
  have hbV : b ∉ VZ T M := by
    intro hmem
    apply hr'V
    have := hgN' _ hmem
    have e : g⁻¹ * (g * r' * g⁻¹) * g = r' := by group
    rwa [e] at this
  have hr2V : g * g * r' * (g * g)⁻¹ ∉ VZ T M := by
    intro hmem
    apply hr'V
    have h1 := hgN' _ hmem
    have h2 := hgN' _ h1
    have e : g⁻¹ * (g⁻¹ * (g * g * r' * (g * g)⁻¹) * g) * g = r' := by group
    rwa [e] at h2
  set B : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers b' with hBdef
  have hBcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers b', x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcb : Commute b b' := hbb'
    exact (Commute.zpow_zpow hcb i j).eq
  have hBAt : B ≤ At := sup_le ((Subgroup.zpowers_le).2 hbAt) ((Subgroup.zpowers_le).2 hb'At)
  have hBel : ∀ x ∈ B, x = 1 ∨ x = b ∨ x = b' ∨ x = b * b' := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute hBcomm hx
    rcases mem_zpowers_of_mul_self_eq_one hbb hy with rfl | rfl <;>
      rcases mem_zpowers_of_mul_self_eq_one hb'b' hz with rfl | rfl <;> simp
  have hr2eq : g * g * r' * (g * g)⁻¹ = b' * f := by rw [hb'f]; group
  have hn' : r' * b * (g * g * r' * (g * g)⁻¹) = r' * ((b * b') * f) := by
    rw [hr2eq]; group
  have hr'Vmem : ∀ w ∈ VZ T M, r' * w ∈ VZ T M → r' ∈ VZ T M := fun w hw h1 => by
    have := (VZ T M).mul_mem h1 ((VZ T M).inv_mem hw)
    simpa using this
  have hBV : B ⊓ VZ T M = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxB, hxV⟩ := hx
    rcases hBel x hxB with h1 | h1 | h1 | h1
    · rw [h1]; exact (Subgroup.mem_bot).mpr rfl
    · rw [h1] at hxV; exact absurd hxV hbV
    · exfalso
      rw [h1] at hxV
      apply hr2V
      rw [hr2eq]; exact (VZ T M).mul_mem hxV hf
    · exfalso
      rw [h1] at hxV
      apply hr'V
      have hw : (b * b') * f ∈ VZ T M := (VZ T M).mul_mem hxV hf
      refine hr'Vmem _ hw ?_
      rw [← hn']; exact hnorm
  have hAtBV : At ≤ B ⊔ VZ T M := by
    intro x hx
    obtain ⟨e, he, hcases⟩ := c.mem_Ac_cases hr'W hr'V hr'2 hx
    have heBV : e ∈ B ⊔ VZ T M := Subgroup.mem_sup_right he
    have hbB : b ∈ B ⊔ VZ T M :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
    have hb'B : b' ∈ B ⊔ VZ T M :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b'))
    have hfV : f ∈ B ⊔ VZ T M := Subgroup.mem_sup_right hf
    have hr2BV : g * g * r' * (g * g)⁻¹ ∈ B ⊔ VZ T M := by
      rw [hr2eq]; exact (B ⊔ VZ T M).mul_mem hb'B hfV
    have hr'BV : r' ∈ B ⊔ VZ T M := by
      have hn := hnorm
      rw [hn'] at hn
      have e' : r' = (r' * ((b * b') * f)) * ((b * b') * f)⁻¹ := by group
      rw [e']
      exact (B ⊔ VZ T M).mul_mem (Subgroup.mem_sup_right hn)
        ((B ⊔ VZ T M).inv_mem ((B ⊔ VZ T M).mul_mem ((B ⊔ VZ T M).mul_mem hbB hb'B) hfV))
    rcases hcases with rfl | rfl | rfl | rfl
    · exact heBV
    · exact (B ⊔ VZ T M).mul_mem hr'BV heBV
    · exact (B ⊔ VZ T M).mul_mem hbB heBV
    · exact (B ⊔ VZ T M).mul_mem hr2BV heBV
  have hconjB : ∀ x ∈ B, u * x * u⁻¹ ∈ B := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute hBcomm hx
    have e : u * (y * z) * u⁻¹ = (u * y * u⁻¹) * (u * z * u⁻¹) := by group
    rw [e]
    refine B.mul_mem ?_ ?_
    · rcases mem_zpowers_of_mul_self_eq_one hbb hy with rfl | rfl
      · have : u * (1 : G) * u⁻¹ = 1 := by group
        rw [this]; exact B.one_mem
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b')
    · rcases mem_zpowers_of_mul_self_eq_one hb'b' hz with rfl | rfl
      · have : u * (1 : G) * u⁻¹ = 1 := by group
        rw [this]; exact B.one_mem
      · rw [hub'u]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hconjB' : ∀ x ∈ B, u⁻¹ * x * u ∈ B := by
    intro x hx
    have h1 := hconjB x hx
    rw [huu] at h1 ⊢
    exact h1
  have huNB : u ∈ Subgroup.normalizer (B : Set G) := mem_normalizer_of_conj_mem hconjB hconjB'
  have hzuN : Subgroup.zpowers u ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.zpowers_le).2 huNB
  set C₀ : Subgroup G := B ⊔ Subgroup.zpowers u with hC₀def
  have hRU_R : rOf T M ⊓ uOfL22 T M = Hyp1281Two.wOfU T M := by
    apply le_antisymm
    · intro x hx
      have : x ∈ rOf T M ⊓ qOf T := ⟨hx.1, uOfL22_le_qOf c hx.2⟩
      rwa [rOf_inf_qOf c] at this
    · exact le_inf (fun w hw => c.mem_rOf_of_mem_wOfU hw) (Hyp1281Two.wOfU_le_uOfL22 T M)
  have hRUle : rOf T M ⊔ uOfL22 T M ≥ rOf T M := le_sup_left
  have huRU : u ∈ rOf T M ⊔ uOfL22 T M := Subgroup.mem_sup_right huU
  have hC₀le : C₀ ≤ rOf T M ⊔ uOfL22 T M :=
    sup_le ((hBAt.trans hAtR).trans le_sup_left) ((Subgroup.zpowers_le).2 huRU)
  refine ⟨C₀, hC₀le, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxC⟩ := hx
    have hxC' : x ∈ (B : Set G) * (Subgroup.zpowers u : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left B (Subgroup.zpowers u) hzuN]
      exact hxC
    obtain ⟨β, hβ, w, hw, hxβ⟩ := Set.mem_mul.mp hxC'
    rcases mem_zpowers_of_mul_self_eq_one hu2 hw with hw1 | hw1
    ·
      rw [hw1, mul_one] at hxβ
      subst hxβ
      have : β ∈ B ⊓ VZ T M := by
        refine ⟨hβ, ?_⟩
        rw [← hinf]
        exact ⟨hxA, hBAt hβ⟩
      rw [hBV] at this
      exact this
    ·
      exfalso
      rw [hw1] at hxβ
      apply huW
      have huR : u ∈ rOf T M := by
        have : u = β⁻¹ * x := by rw [← hxβ]; group
        rw [this]
        exact (rOf T M).mul_mem ((rOf T M).inv_mem (hAtR (hBAt hβ))) (hAR hxA)
      have : u ∈ rOf T M ⊓ uOfL22 T M := ⟨huR, huU⟩
      rwa [hRU_R] at this
  ·
    apply le_antisymm
    · exact sup_le (hAR.trans le_sup_left) hC₀le
    · have hRle : rOf T M ≤ A ⊔ C₀ := by
        rw [← hsup]
        refine sup_le le_sup_left ?_
        refine hAtBV.trans (sup_le ?_ (hVA.trans le_sup_left))
        exact (le_sup_left : B ≤ C₀).trans le_sup_right
      have huAC : u ∈ A ⊔ C₀ :=
        Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
      refine sup_le hRle ?_
      intro x hxU
      have hWU : (Hyp1281Two.wOfU T M).relIndex (uOfL22 T M) = 2 := by
        have h1 := Subgroup.relIndex_mul_card (Hyp1281Two.wOfU T M) (uOfL22 T M)
        have hW : Nat.card (Hyp1281Two.wOfU T M) = 16 := card_wOf c
        rw [inf_eq_left.mpr (Hyp1281Two.wOfU_le_uOfL22 T M), hW, c.c15.q8sq.1] at h1
        omega
      rcases coset_of_relIndex_two hWU hxU huU huW with hxW | hxW
      · exact hRle (c.mem_rOf_of_mem_wOfU hxW)
      · have : x = (x * u⁻¹) * u := by group
        rw [this]
        exact (A ⊔ C₀).mul_mem (hRle (c.mem_rOf_of_mem_wOfU hxW)) huAC

end Complement

end S143

end CFSG.Quasithin
