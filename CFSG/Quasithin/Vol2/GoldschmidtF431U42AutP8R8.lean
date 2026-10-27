module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R7
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R6

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section View2

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

theorem exists_view2 (h : F55Ctx c R) :
    ∃ m : G, m * dG c * m⁻¹ = c.iso.toG fhB ∧ B6.conjSub m (M₁ ⊓ cenOf (dG c)) = R := by
  obtain ⟨hh, hhd⟩ := isConj_iff.1 (dG_conj_F c h)
  set F := c.iso.toG fhB with hF
  set Td := M₁ ⊓ cenOf (dG c) with hTd
  have hK : B6.conjSub hh Td ≤ cenOf F := by
    intro x hx
    rw [B6.mem_conjSub] at hx
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h1 : hh⁻¹ * x * hh * dG c = dG c * (hh⁻¹ * x * hh) :=
      Subgroup.mem_centralizer_singleton_iff.1 hx.2
    rw [← hhd]
    calc x * (hh * dG c * hh⁻¹) = hh * (hh⁻¹ * x * hh * dG c) * hh⁻¹ := by group
      _ = hh * (dG c * (hh⁻¹ * x * hh)) * hh⁻¹ := by rw [h1]
      _ = (hh * dG c * hh⁻¹) * x := by group
  have hK64 : Nat.card ↥(B6.conjSub hh Td) = 64 := by rw [conjSub_card, hTd, card_Td]
  have hKp : IsPGroup 2 ↥(B6.conjSub hh Td) :=
    IsPGroup.of_card (n := 6) (by rw [hK64]; norm_num)
  obtain ⟨S, hS, hKS⟩ := B6.exists_isSylowTwoOf_ge hKp hK
  obtain ⟨g, hg, hRS⟩ := B6.isSylowTwoOf_exists_conj h.hR hS
  have hSR : Nat.card ↥S = 64 := by rw [hRS, conjSub_card, h.hR64]; norm_num
  have hKeq : B6.conjSub hh Td = S :=
    Subgroup.eq_of_le_of_card_ge hKS (by rw [hSR, hK64])
  have hgF : g * F = F * g := Subgroup.mem_centralizer_singleton_iff.1 hg
  refine ⟨g⁻¹ * hh, ?_, ?_⟩
  · calc g⁻¹ * hh * dG c * (g⁻¹ * hh)⁻¹ = g⁻¹ * (hh * dG c * hh⁻¹) * g := by group
      _ = g⁻¹ * F * g := by rw [hhd]
      _ = F := by
        calc g⁻¹ * F * g = g⁻¹ * (F * g) := by group
          _ = g⁻¹ * (g * F) := by rw [hgF]
          _ = F := by group
  · rw [B6.conjSub_mul, hKeq, hRS, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]

theorem exists_u (h : F55Ctx c R) :
    ∃ u : G, u ∈ R ∧ IsConj u z ∧ (∀ r ∈ R, r * u = u * r) ∧
      ∀ x ∈ cenOf (c.iso.toG fhB), x * u = u * x → x ∈ R := by
  obtain ⟨m, hmd, hmR⟩ := exists_view2 c h
  set F := c.iso.toG fhB with hF
  have hzM : z ∈ M₁ := by rw [← c.cenOf_z]; exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hdz : dG c * z = z * dG c := by
    have : dG c ∈ cenOf z := by rw [c.cenOf_z]; exact dG_mem_M1 c
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  have hzTd : z ∈ M₁ ⊓ cenOf (dG c) :=
    ⟨hzM, Subgroup.mem_centralizer_singleton_iff.2 hdz.symm⟩
  have hmem : ∀ x : G, x ∈ R ↔ m⁻¹ * x * m ∈ M₁ ⊓ cenOf (dG c) := fun x => by
    rw [← hmR, B6.mem_conjSub]
  refine ⟨m * z * m⁻¹, (hmem _).2 (by simpa [mul_assoc] using hzTd),
    (isConj_iff.2 ⟨m, rfl⟩).symm, ?_, ?_⟩
  · intro r hr
    have h1 : m⁻¹ * r * m ∈ M₁ := ((hmem r).1 hr).1
    have h2 : (m⁻¹ * r * m) * z = z * (m⁻¹ * r * m) := by
      have : m⁻¹ * r * m ∈ cenOf z := by rw [c.cenOf_z]; exact h1
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    calc r * (m * z * m⁻¹) = m * ((m⁻¹ * r * m) * z) * m⁻¹ := by group
      _ = m * (z * (m⁻¹ * r * m)) * m⁻¹ := by rw [h2]
      _ = (m * z * m⁻¹) * r := by group
  · intro x hx hxu
    rw [hmem]
    have hxF : x * F = F * x := Subgroup.mem_centralizer_singleton_iff.1 hx
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · rw [← c.cenOf_z]
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc m⁻¹ * x * m * z = m⁻¹ * (x * (m * z * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * z * m⁻¹) * x) * m := by rw [hxu]
        _ = z * (m⁻¹ * x * m) := by group
    · rw [← hmd] at hxF
      calc m⁻¹ * x * m * dG c = m⁻¹ * (x * (m * dG c * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * dG c * m⁻¹) * x) * m := by rw [hxF]
        _ = dG c * (m⁻¹ * x * m) := by group

theorem F_not_mem_UG : c.iso.toG fhB ∉ UG c := by
  intro hF
  obtain ⟨b, hb, hbF⟩ := c.iso.mem_imgG.1 hF
  have h1 : b = fhB := c.iso.toG_injective hbF
  rw [h1] at hb
  exact fhatA_not_mem_Uh hb

theorem dG_mem_R (h : F55Ctx c R) : dG c ∈ R := UG_le_R c h (dG_mem_UG c)

theorem cen_d_le_R (h : F55Ctx c R) :
    ∀ x ∈ cenOf (c.iso.toG fhB), x * dG c = dG c * x → x ∈ R := by
  obtain ⟨u, huR, hu, huc, hcu⟩ := exists_u c h
  set F := c.iso.toG fhB with hF
  obtain ⟨e⟩ := h.hD
  have hFc : ∀ r ∈ R, r * F = F * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.1 (h.hR.1 hr)
  have hdc : ∀ r ∈ R, r * dG c = dG c * r := fun r hr => by
    have := dG_central c h hr
    calc r * dG c = (r * dG c * r⁻¹) * r := by group
      _ = dG c * r := by rw [this]
  have hFR : F ∈ R := F_mem_R c h
  have hdR : dG c ∈ R := dG_mem_R c h
  have hcen : ∀ {y : G} (hy : y ∈ R), (∀ r ∈ R, r * y = y * r) →
      ∀ q : DihedralGroup 4 × DihedralGroup 4, e ⟨y, hy⟩ * q = q * e ⟨y, hy⟩ := by
    intro y hy hyc q
    obtain ⟨r, rfl⟩ := e.surjective q
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hyc r.1 r.2).symm)
  have hne : ∀ {y : G} (hy : y ∈ R), y ≠ 1 → e ⟨y, hy⟩ ≠ 1 := by
    intro y hy hy1 h1
    apply hy1
    have := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hne2 : ∀ {y y' : G} (hy : y ∈ R) (hy' : y' ∈ R), y ≠ y' → e ⟨y, hy⟩ ≠ e ⟨y', hy'⟩ := by
    intro y y' hy hy' hyy h1
    exact hyy (congrArg Subtype.val (e.injective h1))
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply c.z1
    exact (isConj_one_right.1 hu)
  have huF : u ≠ F := by
    rintro rfl
    exact h.hnc hu
  have hdF : dG c ≠ F := by
    intro hd
    apply F_not_mem_UG c
    rw [← hF, ← hd]
    exact dG_mem_UG c
  have hud : u ≠ dG c := by
    rintro rfl
    exact h.hnc ((dG_conj_F c h).symm.trans hu)
  have hF1 : F ≠ 1 := F_ne_one c.iso
  have hd1 : dG c ≠ 1 := dG_ne_one c
  have key := Delta_central_triple (e ⟨F, hFR⟩) (hcen hFR hFc) (hne hFR hF1) (e ⟨dG c, hdR⟩)
    (hcen hdR hdc) (hne hdR hd1) (hne2 hFR hdR hdF.symm) (e ⟨u, huR⟩) (hcen huR huc)
    (hne huR hu1) (hne2 huR hFR huF) (hne2 huR hdR hud)
  have hu_eq : u = F * dG c := by
    have := e.injective (key.trans (map_mul e ⟨F, hFR⟩ ⟨dG c, hdR⟩).symm)
    exact congrArg Subtype.val this
  intro x hx hxd
  apply hcu x hx
  have hxF : x * F = F * x := Subgroup.mem_centralizer_singleton_iff.1 hx
  rw [hu_eq]
  calc x * (F * dG c) = (x * F) * dG c := by group
    _ = F * (x * dG c) := by rw [hxF]; group
    _ = F * (dG c * x) := by rw [hxd]
    _ = (F * dG c) * x := by group

end View2

end CFSG.Quasithin.H13.F431.U42Aut
