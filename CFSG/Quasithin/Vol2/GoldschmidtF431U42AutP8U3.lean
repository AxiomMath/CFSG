module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8U2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8U0

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section NoOuter

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G} {ρ : G}

theorem isConj_F_of_cen_Q (qd : QData c)
    (hall : ∀ u : G, u * u = 1 → u ≠ 1 → IsConj u z ∨ IsConj u (c.iso.toG fhB)) {x : G}
    (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hcen : ∀ q ∈ oddCl (cenOf (c.iso.toG fhB)), x * q = q * x) :
    IsConj x (c.iso.toG fhB) := by
  rcases hall x hx2 hx1 with hxz | hxF
  · exfalso
    obtain ⟨g, hg⟩ := isConj_iff.1 hxz
    have h1 : cenOf z = B6.conjSub g (cenOf x) := by
      rw [conjSub_cenOf, hg]
    have h2 : Nat.card ↥(cenOf z) = Nat.card ↥(cenOf x) := by rw [h1, conjSub_card]
    have h3 : Nat.card ↥(oddCl (cenOf (c.iso.toG fhB))) ∣ Nat.card ↥(cenOf x) :=
      Subgroup.card_dvd_of_le (fun q hq => Subgroup.mem_centralizer_singleton_iff.2
        (hcen q hq).symm)
    rw [qd.card_oddCl, ← h2, c.cenOf_z, c.iso.card_M₁] at h3
    omega
  · exact hxF

theorem no_outer_central (h : F55Ctx c R) (hr : RhoCtx c R ρ) (hρE : ρ ∉ Eg c)
    (hE : Nat.card ↥(Eg c) = 1440)
    (hall : ∀ u : G, u * u = 1 → u ≠ 1 → IsConj u z ∨ IsConj u (c.iso.toG fhB))
    (qd : QData c)
    (hcen : ∀ q ∈ oddCl (cenOf (c.iso.toG fhB)), (z * ρ) * q = q * (z * ρ)) : False := by
  set F := c.iso.toG fhB with hF
  set r := z * ρ with hr_def
  have hF2 : F * F = 1 := F_sq c.iso
  have hFinv : F⁻¹ = F := inv_eq_of_mul_eq_one_right hF2
  have hFq : ∀ q ∈ oddCl (cenOf F), F * q = q * F := fun q hq =>
    (Subgroup.mem_centralizer_singleton_iff.1 (oddCl_le _ hq)).symm
  have hrC : r ∈ C1G c R := (C1G c R).mul_mem (z_mem_C1G c h) hr.mem
  have hrX : r ∈ cenOf F := h.hR.1 hrC.1
  have hrF : r * F = F * r := Subgroup.mem_centralizer_singleton_iff.1 hrX
  have hrE : r ∉ Eg c := fun hm => hρE (by
    have := (Eg c).mul_mem ((Eg c).inv_mem (z_mem_Eg c)) hm
    rwa [hr_def, ← mul_assoc, inv_mul_cancel, one_mul] at this)
  have hr2 : r * r = 1 := r_sq c h hr
  have hrne : r ≠ 1 := fun h1 => hrE (h1 ▸ (Eg c).one_mem)
  have hrFC : r * F ∈ C1G c R := (C1G c R).mul_mem hrC (F_mem_C1G c h)
  have hrFE : r * F ∉ Eg c := fun hm => hrE (by
    have := (Eg c).mul_mem hm ((Eg c).inv_mem (F_mem_Eg c))
    rwa [hFinv, mul_assoc, hF2, mul_one] at this)
  have hrF2 : (r * F) * (r * F) = 1 := by
    calc (r * F) * (r * F) = r * (F * r) * F := by group
      _ = r * (r * F) * F := by rw [hrF]
      _ = (r * r) * (F * F) := by group
      _ = 1 := by rw [hr2, hF2, one_mul]
  have hrFne : r * F ≠ 1 := fun h1 => hrFE (h1 ▸ (Eg c).one_mem)
  have hcenF : ∀ q ∈ oddCl (cenOf F), (r * F) * q = q * (r * F) := by
    intro q hq
    calc (r * F) * q = r * (F * q) := by group
      _ = r * (q * F) := by rw [hFq q hq]
      _ = (r * q) * F := by group
      _ = (q * r) * F := by rw [hcen q hq]
      _ = q * (r * F) := by group
  have hrΦ : IsConj r F := isConj_F_of_cen_Q c qd hall hr2 hrne hcen
  have hrFΦ : IsConj (r * F) F := isConj_F_of_cen_Q c qd hall hrF2 hrFne hcenF
  have hnΦ : ∀ x : G, IsConj x F → IsConj x z → False := fun x h1 h2 => h.hnc (h1.symm.trans h2)
  set d := dG c with hd
  have hdU : d ∈ UG c := dG_mem_UG c
  have hd2 : d * d = 1 := dG_sq c
  have hrd : r * d = d * r := C1G_comm_UG c h hrC hdU
  have hrd2 : (r * d) * (r * d) = 1 := by
    calc (r * d) * (r * d) = r * (d * r) * d := by group
      _ = r * (r * d) * d := by rw [← hrd]
      _ = (r * r) * (d * d) := by group
      _ = 1 := by rw [hr2, hd2, one_mul]
  have hrdne : r * d ≠ 1 := by
    intro h1
    apply hrE
    have : r = d⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact (Eg c).inv_mem (UG_le_Eg c hdU)
  have hzd : z * d = d * z := C1G_comm_UG c h (z_mem_C1G c h) hdU
  have hconjrFd : IsConj (r * F * d) (r * d) := by
    refine isConj_iff.2 ⟨z, ?_⟩
    have hz2 : z * z = 1 := by simpa [pow_two] using c.z2
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    rw [hzinv]
    have h1 := z_conj_r c h hr
    calc z * (r * F * d) * z = (z * r * z) * F * d := by
          calc z * (r * F * d) * z = z * r * F * (d * z) := by group
            _ = z * r * F * (z * d) := by rw [← hzd]
            _ = (z * r * z) * F * d := by
                have hFz : z * F = F * z := zF_comm c
                calc z * r * F * (z * d) = z * r * (F * z) * d := by group
                  _ = z * r * (z * F) * d := by rw [hFz]
                  _ = (z * r * z) * F * d := by group
      _ = r * d := by
          have : z * r * z = r * F := by
            have := h1
            rwa [hzinv] at this
          rw [this]
          calc r * F * F * d = r * (F * F) * d := by group
            _ = r * d := by rw [hF2, mul_one]
  have hconjS : ∀ s ∈ UG c, s * s = 1 → s ≠ 1 →
      IsConj (r * s) (r * d) ∧ IsConj (r * F * s) (r * d) := by
    intro s hsU hs2 hs1
    obtain ⟨q, hq, hqs⟩ := U_fusion c hsU hs2 hs1
    have hqr : q * r = r * q := (hcen q hq).symm
    have hqF : q * F = F * q := (hFq q hq).symm
    have h1 : IsConj (r * s) (r * d) := isConj_iff.2 ⟨q, by
      calc q * (r * s) * q⁻¹ = (q * r) * s * q⁻¹ := by group
        _ = (r * q) * s * q⁻¹ := by rw [hqr]
        _ = r * (q * s * q⁻¹) := by group
        _ = r * d := by rw [hqs]⟩
    have h2 : IsConj (r * F * s) (r * F * d) := isConj_iff.2 ⟨q, by
      calc q * (r * F * s) * q⁻¹ = (q * r) * F * s * q⁻¹ := by group
        _ = (r * q) * F * s * q⁻¹ := by rw [hqr]
        _ = r * (q * F) * s * q⁻¹ := by group
        _ = r * (F * q) * s * q⁻¹ := by rw [hqF]
        _ = r * F * (q * s * q⁻¹) := by group
        _ = r * F * d := by rw [hqs]⟩
    exact ⟨h1, h2.trans hconjrFd⟩
  have hall' : ∀ x : G, x ∈ R → x ∉ Eg c → x * x = 1 → x ≠ 1 →
      x = r ∨ x = r * F ∨ ∃ s ∈ UG c, s * s = 1 ∧ s ≠ 1 ∧ (x = r * s ∨ x = r * F * s) := by
    intro x hxR hxE hx2 hx1
    obtain ⟨c₁, hc₁, u, hu, hxcu⟩ := (decomp_R c h).2 x hxR
    have hcu : c₁ * u = u * c₁ := C1G_comm_UG c h hc₁ hu
    have huE : u ∈ Eg c := UG_le_Eg c hu
    have hc₁E : c₁ ∉ Eg c := fun hm => hxE (by
      rw [hxcu]
      exact (Eg c).mul_mem hm huE)
    have hxx : (c₁ * c₁) * (u * u) = 1 := by
      calc (c₁ * c₁) * (u * u) = c₁ * (c₁ * u) * u := by group
        _ = c₁ * (u * c₁) * u := by rw [hcu]
        _ = (c₁ * u) * (c₁ * u) := by group
        _ = 1 := by rw [← hxcu]; exact hx2
    have hcc : c₁ * c₁ = 1 := by
      have h1 : c₁ * c₁ = (u * u)⁻¹ := eq_inv_of_mul_eq_one_left hxx
      have h2 : c₁ * c₁ ∈ C1G c R := (C1G c R).mul_mem hc₁ hc₁
      have h3 : (u * u)⁻¹ ∈ UG c := (UG c).inv_mem ((UG c).mul_mem hu hu)
      rw [h1] at h2 ⊢
      rw [C1G_inf_UG c h3 h2]
    have huu : u * u = 1 := by
      rw [hcc, one_mul] at hxx
      exact hxx
    rcases C1G_outer_inv c h hr hρE hc₁ hc₁E hcc with hc | hc
    · by_cases hu1 : u = 1
      · left
        rw [hxcu, hc, hu1, mul_one]
      · right; right
        exact ⟨u, hu, huu, hu1, Or.inl (by rw [hxcu, hc])⟩
    · by_cases hu1 : u = 1
      · right; left
        rw [hxcu, hc, hu1, mul_one]
      · right; right
        exact ⟨u, hu, huu, hu1, Or.inr (by rw [hxcu, hc])⟩
  obtain ⟨hZ, hP⟩ := outer_counts c h hE
  rcases hall (r * d) hrd2 hrdne with hz | hf
  ·
    have hsub : {x : G | x ∈ R ∧ x ∉ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x F} ⊆ {r, r * F} := by
      rintro x ⟨hxR, hxE, hx2, hx1, hxf⟩
      rcases hall' x hxR hxE hx2 hx1 with hx | hx | ⟨s, hsU, hs2, hs1, hxs⟩
      · exact Or.inl hx
      · exact Or.inr hx
      · exfalso
        have hxz : IsConj x z := by
          rcases hxs with rfl | rfl
          · exact (hconjS s hsU hs2 hs1).1.trans hz
          · exact (hconjS s hsU hs2 hs1).2.trans hz
        exact hnΦ x hxf hxz
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({r, r * F} : Set G).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      simp
    have hP' : 6 ≤ Set.ncard {x : G | x ∈ R ∧ x ∉ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x F} := hP
    omega
  ·
    have hsub : {x : G | x ∈ R ∧ x ∉ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x z} ⊆ (∅ : Set G) := by
      rintro x ⟨hxR, hxE, hx2, hx1, hxz⟩
      rcases hall' x hxR hxE hx2 hx1 with hx | hx | ⟨s, hsU, hs2, hs1, hxs⟩
      · exact absurd hxz (fun hc => hnΦ x (hx ▸ hrΦ) hc)
      · exact absurd hxz (fun hc => hnΦ x (hx ▸ hrFΦ) hc)
      · exfalso
        have hxf : IsConj x F := by
          rcases hxs with rfl | rfl
          · exact (hconjS s hsU hs2 hs1).1.trans hf
          · exact (hconjS s hsU hs2 hs1).2.trans hf
        exact hnΦ x hxf hxz
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_empty] at h1
    omega

end NoOuter

end CFSG.Quasithin.H13.F431.U42Aut
