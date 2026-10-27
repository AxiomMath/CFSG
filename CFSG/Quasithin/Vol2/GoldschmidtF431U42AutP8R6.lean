module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R5

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Dec

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

theorem F_mem_R (h : F55Ctx c R) : c.iso.toG fhB ∈ R :=
  mem_of_central_of_isSylowTwoOf h.hR (Subgroup.mem_centralizer_singleton_iff.2 rfl)
    (fun _ hb => Subgroup.mem_centralizer_singleton_iff.1 hb) (F_sq c.iso)

theorem z_mem_TfG : z ∈ TfG c := by
  have hxz : c.iso.toG xB = z := c.iso.toG_xB c.z2 c.z1 c.zc
  have hzT : z ∈ c.iso.imgG That := by
    have : c.iso.toG xB ∈ c.iso.imgG That := c.iso.mem_imgG.2 ⟨xB, xA_mem_That, rfl⟩
    rwa [hxz] at this
  have hzF : z * c.iso.toG fhB = c.iso.toG fhB * z := (c.comm_z (c.iso.toG_mem fhB)).symm
  exact ⟨hzT, Subgroup.mem_centralizer_singleton_iff.2 hzF⟩

theorem z_mem_R (h : F55Ctx c R) : z ∈ R := h.hTR (z_mem_TfG c)

theorem UG_le_TfG : UG c ≤ TfG c := by
  intro g hg
  obtain ⟨b, hb, rfl⟩ := c.iso.mem_imgG.1 hg
  refine ⟨c.iso.mem_imgG.2 ⟨b, Uh_le_That hb, rfl⟩, ?_⟩
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  have h1 : b * fhB = fhB * b := Subtype.ext (Uh_comm_f hb)
  rw [← AutIso.toG_mul, ← AutIso.toG_mul, h1]

theorem UG_le_R (h : F55Ctx c R) : UG c ≤ R := (UG_le_TfG c).trans h.hTR

theorem card_UG : Nat.card ↥(UG c) = 8 := by
  rw [UG, c.iso.card_imgG Uh_le_Bh, card_Uh]

theorem F_mem_C1G (h : F55Ctx c R) : c.iso.toG fhB ∈ C1G c R := by
  refine ⟨F_mem_R c h, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.1 (B1G_le_E1G c hg).2

theorem z_mem_C1G (h : F55Ctx c R) : z ∈ C1G c R := by
  refine ⟨z_mem_R c h, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  have : g ∈ cenOf z := by rw [c.cenOf_z]; exact (B1G_le_E1G c hg).1
  exact Subgroup.mem_centralizer_singleton_iff.1 this

theorem conj_C1G (h : F55Ctx c R) {n : G} (hn : n ∈ R) {g : G} (hg : g ∈ C1G c R) :
    n * g * n⁻¹ ∈ C1G c R := by
  refine ⟨R.mul_mem (R.mul_mem hn hg.1) (R.inv_mem hn), Subgroup.mem_centralizer_iff.2 ?_⟩
  intro b hb
  have hb' : n⁻¹ * b * n⁻¹⁻¹ ∈ B1G c := conj_B1G c h (R.inv_mem hn) hb
  have hgb : g * (n⁻¹ * b * n⁻¹⁻¹) = (n⁻¹ * b * n⁻¹⁻¹) * g :=
    (Subgroup.mem_centralizer_iff.1 hg.2 _ hb').symm
  simp only [inv_inv] at hgb
  calc b * (n * g * n⁻¹) = n * ((n⁻¹ * b * n) * g) * n⁻¹ := by group
    _ = n * (g * (n⁻¹ * b * n)) * n⁻¹ := by rw [hgb]
    _ = n * g * n⁻¹ * b := by group

theorem C1G_inf_UG {u : G} (hu : u ∈ UG c) (hu1 : u ∈ C1G c R) : u = 1 := by
  obtain ⟨b, hb, rfl⟩ := c.iso.mem_imgG.1 hu
  have h1 : c.iso.toG b * b1G c = b1G c * c.iso.toG b :=
    (Subgroup.mem_centralizer_iff.1 hu1.2 _ (b1G_mem_B1G c)).symm
  have hbP : c.iso.toG b = c.iso.toG1 (Subgroup.inclusion Bh_le_P1h b) :=
    (c.iso.toG1_inclusion b).symm
  rw [hbP] at h1
  have h2 : Subgroup.inclusion Bh_le_P1h b * b1P = b1P * Subgroup.inclusion Bh_le_P1h b :=
    c.iso.toG1_injective (by rw [map_mul, map_mul]; exact h1)
  have h3 : (b : Ah) * b1A = b1A * (b : Ah) := congrArg (fun x : ↥P1h => (x : Ah)) h2
  have h4 : (b : Ah) = 1 := Uh_comm_b1 hb h3
  have h5 : b = 1 := Subtype.ext h4
  rw [h5, AutIso.toG_one]

theorem decomp_R (h : F55Ctx c R) :
    Nat.card ↥(C1G c R) = 8 ∧ ∀ r ∈ R, ∃ x ∈ C1G c R, ∃ u ∈ UG c, r = x * u := by
  have hUR := UG_le_R c h
  let f : ↥(C1G c R) × ↥(UG c) → ↥R := fun p =>
    ⟨(p.1 : G) * (p.2 : G), R.mul_mem p.1.2.1 (hUR p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨x, hx⟩, ⟨u, hu⟩⟩ ⟨⟨x', hx'⟩, ⟨u', hu'⟩⟩ he
    have he' : x * u = x' * u' := congrArg Subtype.val he
    have hxx : x'⁻¹ * x = u' * u⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * u) * u⁻¹ := by group
        _ = x'⁻¹ * (x' * u') * u⁻¹ := by rw [he']
        _ = u' * u⁻¹ := by group
    have h1 : x'⁻¹ * x ∈ C1G c R := (C1G c R).mul_mem ((C1G c R).inv_mem hx') hx
    have h2 : x'⁻¹ * x ∈ UG c := by rw [hxx]; exact (UG c).mul_mem hu' ((UG c).inv_mem hu)
    have h3 : x'⁻¹ * x = 1 := C1G_inf_UG c h2 h1
    have hxe : x = x' := by
      calc x = x' * (x'⁻¹ * x) := by group
        _ = x' := by rw [h3]; group
    have hue : u = u' := by
      have : u' * u⁻¹ = 1 := by rw [← hxx]; exact h3
      calc u = (u' * u⁻¹)⁻¹ * u' := by group
        _ = u' := by rw [this]; group
    subst hxe
    subst hue
    rfl
  have hcardP : Nat.card (↥(C1G c R) × ↥(UG c)) = Nat.card ↥(C1G c R) * 8 := by
    rw [Nat.card_prod, card_UG]
  have hle : Nat.card ↥(C1G c R) * 8 ≤ 64 := by
    have := Nat.card_le_card_of_injective f hinj
    rw [hcardP, h.hR64] at this
    norm_num at this
    exact this
  have h8 := card_C1G c h
  have hC : Nat.card ↥(C1G c R) = 8 := by omega
  refine ⟨hC, ?_⟩
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcardP, hC, h.hR64]
    norm_num
  intro r hr
  obtain ⟨⟨x, u⟩, hxu⟩ := hbij.2 ⟨r, hr⟩
  have : (x : G) * (u : G) = r := congrArg Subtype.val hxu
  exact ⟨x, x.2, u, u.2, this.symm⟩

theorem C1G_comm_UG (h : F55Ctx c R) {x u : G} (hx : x ∈ C1G c R) (hu : u ∈ UG c) :
    x * u = u * x := by
  have h1 : x * u * x⁻¹ * u⁻¹ ∈ C1G c R := by
    have := (C1G c R).mul_mem hx (conj_C1G c h (UG_le_R c h hu) ((C1G c R).inv_mem hx))
    simpa [mul_assoc] using this
  have h2 : x * u * x⁻¹ * u⁻¹ ∈ UG c := by
    have := (UG c).mul_mem (conj_UG c h hx.1 hu) ((UG c).inv_mem hu)
    simpa [mul_assoc] using this
  have h3 := C1G_inf_UG c h2 h1
  calc x * u = (x * u * x⁻¹ * u⁻¹) * u * x := by group
    _ = u * x := by rw [h3]; group

end Dec

end CFSG.Quasithin.H13.F431.U42Aut
