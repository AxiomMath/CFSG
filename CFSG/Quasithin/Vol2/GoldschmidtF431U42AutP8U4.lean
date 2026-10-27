module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8A6U
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8U0

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Dich

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G} {ρ : G}

theorem rho_dichotomy (h : F55Ctx c R) (hr : RhoCtx c R ρ) (qd : QData c) :
    (∀ q ∈ oddCl (cenOf (c.iso.toG fhB)), ρ * q = q * ρ) ∨
      (∀ q ∈ oddCl (cenOf (c.iso.toG fhB)), (z * ρ) * q = q * (z * ρ)) := by
  have := qd.normal
  set F := c.iso.toG fhB with hF
  have hρX : ρ ∈ cenOf F := h.hR.1 hr.mem.1
  have hzX : z ∈ cenOf F := TfG_le_cen c (z_mem_TfG c)
  have hF2 : F * F = 1 := F_sq c.iso
  have hz2 : z * z = 1 := by simpa [pow_two] using c.z2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  let ρX : ↥(cenOf F) := ⟨ρ, hρX⟩
  let zX : ↥(cenOf F) := ⟨z, hzX⟩
  let φ : ↥(cenOf F) →* MulAut ↥qd.Q := MulAut.conjNormal
  have hαρ : ∀ q : ↥qd.Q, (((φ ρX q : ↥qd.Q) : ↥(cenOf F)) : G) =
      ρ * (((q : ↥qd.Q) : ↥(cenOf F)) : G) * ρ⁻¹ := fun q => rfl
  have hαz : ∀ q : ↥qd.Q, (((φ zX q : ↥qd.Q) : ↥(cenOf F)) : G) =
      z * (((q : ↥qd.Q) : ↥(cenOf F)) : G) * z⁻¹ := fun q => rfl
  have hqF : ∀ q : ↥qd.Q, (((q : ↥qd.Q) : ↥(cenOf F)) : G) * F = F * (((q : ↥qd.Q) :
      ↥(cenOf F)) : G) := fun q => Subgroup.mem_centralizer_singleton_iff.1 q.1.2
  let ι : ↥qd.Q →* G := (cenOf F).subtype.comp qd.Q.subtype
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  let LB : Subgroup ↥qd.Q := (B1G c).comap ι
  have hB1 : B1G c ≤ ι.range := by
    intro g hg
    obtain ⟨q, hq⟩ := (qd.mem_oddCl_iff g).1 (B1G_le_oddCl c hg)
    exact ⟨q, hq⟩
  have hLB : Nat.card ↥LB = 12 := by
    have h1 : LB.map ι = B1G c := Subgroup.map_comap_eq_self hB1
    rw [← Subgroup.card_map_of_injective hι (K := LB), h1]
    exact card_B1G c
  have hρL : ∀ l ∈ LB, φ ρX l = l := by
    intro l hl
    have hlB : ι l ∈ B1G c := hl
    have h1 : ι l * ρ = ρ * ι l := Subgroup.mem_centralizer_iff.1 hr.mem.2 (ι l) hlB
    apply Subtype.ext
    apply Subtype.ext
    rw [hαρ]
    show ρ * ι l * ρ⁻¹ = ι l
    calc ρ * ι l * ρ⁻¹ = (ι l * ρ) * ρ⁻¹ := by rw [h1]
      _ = ι l := by group
  have hzL : ∀ l ∈ LB, φ zX l = l := by
    intro l hl
    have hlB : ι l ∈ B1G c := hl
    have hlz : ι l ∈ cenOf z := by rw [c.cenOf_z]; exact (B1G_le_E1G c hlB).1
    have h1 : ι l * z = z * ι l := Subgroup.mem_centralizer_singleton_iff.1 hlz
    apply Subtype.ext
    apply Subtype.ext
    rw [hαz]
    show z * ι l * z⁻¹ = ι l
    calc z * ι l * z⁻¹ = (ι l * z) * z⁻¹ := by rw [h1]
      _ = ι l := by group
  have hρ2 : ∀ k, φ ρX (φ ρX k) = k := by
    intro k
    apply Subtype.ext
    apply Subtype.ext
    rw [hαρ, hαρ]
    have hk := hqF k
    calc ρ * (ρ * (((k : ↥qd.Q) : ↥(cenOf F)) : G) * ρ⁻¹) * ρ⁻¹
        = (ρ * ρ) * (((k : ↥qd.Q) : ↥(cenOf F)) : G) * (ρ * ρ)⁻¹ := by group
      _ = F * (((k : ↥qd.Q) : ↥(cenOf F)) : G) * F⁻¹ := by rw [hr.sq]
      _ = (((k : ↥qd.Q) : ↥(cenOf F)) : G) := by
        have hFi : F⁻¹ = F := inv_eq_of_mul_eq_one_right hF2
        rw [hFi, ← hk]
        calc ((k : ↥qd.Q) : ↥(cenOf F)) * F * F
            = (((k : ↥qd.Q) : ↥(cenOf F)) : G) * (F * F) := by group
          _ = _ := by rw [hF2, mul_one]
  have hz2' : ∀ k, φ zX (φ zX k) = k := by
    intro k
    apply Subtype.ext
    apply Subtype.ext
    rw [hαz, hαz, hzinv]
    calc z * (z * (((k : ↥qd.Q) : ↥(cenOf F)) : G) * z) * z
        = (z * z) * (((k : ↥qd.Q) : ↥(cenOf F)) : G) * (z * z) := by group
      _ = _ := by rw [hz2]; group
  have hz1 : ∃ k, φ zX k ≠ k := by
    by_contra hcon0
    have hcon : ∀ k, φ zX k = k := fun k => by_contra fun hne => hcon0 ⟨k, hne⟩
    have hQz : oddCl (cenOf F) ≤ cenOf z := by
      intro q hq
      obtain ⟨q', rfl⟩ := (qd.mem_oddCl_iff q).1 hq
      have := congrArg (fun w : ↥qd.Q => (((w : ↥qd.Q) : ↥(cenOf F)) : G)) (hcon q')
      rw [cenOf, Subgroup.mem_centralizer_singleton_iff]
      have h1 : z * (((q' : ↥qd.Q) : ↥(cenOf F)) : G) * z⁻¹ = (((q' : ↥qd.Q) : ↥(cenOf F)) : G) :=
        this
      calc (((q' : ↥qd.Q) : ↥(cenOf F)) : G) * z
          = (z * (((q' : ↥qd.Q) : ↥(cenOf F)) : G) * z⁻¹) * z := by rw [h1]
        _ = z * (((q' : ↥qd.Q) : ↥(cenOf F)) : G) := by group
    have h3 := Subgroup.card_dvd_of_le hQz
    rw [qd.card_oddCl, c.cenOf_z, c.iso.card_M₁] at h3
    omega
  by_cases hρ1 : ∃ k, φ ρX k ≠ k
  · right
    have hEq : φ ρX = φ zX :=
      aut_swap_unique qd.equiv LB hLB (φ ρX) (φ zX) hρ2 hz2' hρ1 hz1 hρL hzL
    intro q hq
    obtain ⟨q', rfl⟩ := (qd.mem_oddCl_iff q).1 hq
    have h1 := congrArg (fun w : ↥qd.Q => (((w : ↥qd.Q) : ↥(cenOf F)) : G))
      (DFunLike.congr_fun hEq q')
    simp only [hαρ, hαz] at h1
    set Q' : G := (((q' : ↥qd.Q) : ↥(cenOf F)) : G) with hQ'
    have h2 : ρ * Q' = z * Q' * z⁻¹ * ρ := by
      calc ρ * Q' = (ρ * Q' * ρ⁻¹) * ρ := by group
        _ = z * Q' * z⁻¹ * ρ := by rw [h1]
    calc z * ρ * Q' = z * (ρ * Q') := by group
      _ = z * (z * Q' * z⁻¹ * ρ) := by rw [h2]
      _ = (z * z) * Q' * z⁻¹ * ρ := by group
      _ = Q' * (z * ρ) := by rw [hz2, one_mul, hzinv]; group
  · left
    have hρ1' : ∀ k, φ ρX k = k := fun k => by_contra fun hne => hρ1 ⟨k, hne⟩
    intro q hq
    obtain ⟨q', rfl⟩ := (qd.mem_oddCl_iff q).1 hq
    have h1 := congrArg (fun w : ↥qd.Q => (((w : ↥qd.Q) : ↥(cenOf F)) : G)) (hρ1' q')
    simp only [hαρ] at h1
    set Q' : G := (((q' : ↥qd.Q) : ↥(cenOf F)) : G) with hQ'
    calc ρ * Q' = (ρ * Q' * ρ⁻¹) * ρ := by group
      _ = Q' * ρ := by rw [h1]

end Dich

end CFSG.Quasithin.H13.F431.U42Aut
