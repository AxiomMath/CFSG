module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Ctx
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Sub

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

@[expose] def oddCl {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  Subgroup.closure {y : G | y ∈ H ∧ Odd (orderOf y)}

section Odd

variable {G : Type*} [Group G]

theorem oddCl_le (H : Subgroup G) : oddCl H ≤ H := by
  rw [oddCl, Subgroup.closure_le]
  exact fun y hy => hy.1

theorem oddCl_conj {H : Subgroup G} {n : G} (h1 : ∀ x ∈ H, n * x * n⁻¹ ∈ H) {y : G}
    (hy : y ∈ oddCl H) : n * y * n⁻¹ ∈ oddCl H := by
  unfold oddCl at hy ⊢
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨h1 x hx.1, ?_⟩
    have : orderOf (n * x * n⁻¹) = orderOf x :=
      orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective x
    rw [this]; exact hx.2
  | one => simp
  | mul x y _ _ hx hy =>
    have : n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
    rw [this]; exact mul_mem hx hy
  | inv x _ hx =>
    have : n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem hx

theorem mem_oddCl_of_pow_three {H : Subgroup G} {x : G} (hx : x ∈ H) (h3 : x ^ 3 = 1) :
    x ∈ oddCl H :=
  Subgroup.subset_closure ⟨hx, Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)⟩

end Odd

theorem exists_elt_Alt1 {l : PL} (hl : l ∈ Alt1L) : ∃ a : Ah, a ∈ Alt1h ∧ RepL l (a : P45) := by
  obtain ⟨w, hw, hwl⟩ := List.mem_map.1 (Dl1_eq ▸ Alt1_check.2.2.2.2 l hl)
  exact ⟨aW w, ⟨l, hl, hwl ▸ repL_aW w⟩, hwl ▸ repL_aW w⟩

theorem pow_three_of_repL {m : PL} {α : Ah} (hm : RepL m (α : P45))
    (h3 : comp m (comp m m) = idL) : α ^ 3 = 1 := by
  have h : RepL idL ((α : P45) * ((α : P45) * (α : P45))) := by
    rw [← h3]
    exact repL_mul hm (repL_mul hm hm)
  have h' : (α : P45) * ((α : P45) * (α : P45)) = 1 := eq_of_repL h (repL_one 45)
  apply Subtype.ext
  simpa [pow_succ, mul_assoc] using h'

theorem Alt1_prod :
    ∀ p ∈ Alt1h, ∃ α ∈ Alt1h, ∃ β ∈ Alt1h, α ^ 3 = 1 ∧ β ^ 3 = 1 ∧ p = α * β := by
  intro p ⟨l, hl, hrep⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Alt1_gen l hl
  have hT3 : ∀ m ∈ T3L, m ∈ Alt1L ∧ comp m (comp m m) = idL := by
    intro m hm
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hm
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h2
    exact ⟨h1, h2.2⟩
  obtain ⟨α, hα, hαr⟩ := exists_elt_Alt1 (hT3 a ha).1
  have hαp : α ^ 3 = 1 := pow_three_of_repL hαr (hT3 a ha).2
  rcases List.mem_cons.1 hb with rfl | hb'
  · refine ⟨α, hα, 1, Alt1h.one_mem, hαp, one_pow 3, ?_⟩
    have h1 : RepL l ((α : P45) * 1) := by
      rw [← hab]
      exact repL_mul hαr (repL_one 45)
    rw [mul_one] at h1 ⊢
    exact Subtype.ext (eq_of_repL hrep h1)
  · obtain ⟨β, hβ, hβr⟩ := exists_elt_Alt1 (hT3 b hb').1
    refine ⟨α, hα, β, hβ, hαp, pow_three_of_repL hβr (hT3 b hb').2, ?_⟩
    have h1 : RepL l ((α : P45) * (β : P45)) := by
      rw [← hab]
      exact repL_mul hαr hβr
    exact Subtype.ext (eq_of_repL hrep h1)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section E1

variable (c : AutCtx G M₁ M₂ z)

@[expose] def E1G : Subgroup G := M₁ ⊓ cenOf (c.iso.toG fhB)

@[expose] def B1G : Subgroup G := (Alt1h.subgroupOf P1h).map c.iso.toG1

theorem mem_B1G_iff {g : G} :
    g ∈ B1G c ↔ ∃ p : ↥P1h, (p : Ah) ∈ Alt1h ∧ c.iso.toG1 p = g := by
  unfold B1G
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem toG1_fP1 : c.iso.toG1 fP1 = c.iso.toG fhB := AutIso.toG1_inclusion c.iso fhB

theorem toG1_mem (p : ↥P1h) : c.iso.toG1 p ∈ M₁ := (c.iso.phi1 p).2

theorem exists_toG1 {g : G} (hg : g ∈ M₁) : ∃ p : ↥P1h, c.iso.toG1 p = g :=
  ⟨c.iso.phi1.symm ⟨g, hg⟩, by simp [AutIso.toG1]⟩

theorem toG1_comm_iff (p : ↥P1h) :
    c.iso.toG1 p * c.iso.toG fhB = c.iso.toG fhB * c.iso.toG1 p ↔
      (p : Ah) ∈ Subgroup.centralizer ({fhatA} : Set Ah) := by
  rw [← toG1_fP1 c, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h2 := congrArg (fun x : ↥P1h => (x : Ah)) (c.iso.toG1_injective h)
    simpa only [Subgroup.coe_mul, coe_fP1] using h2
  · intro h
    exact congrArg c.iso.toG1 (Subtype.ext (by simpa only [Subgroup.coe_mul, coe_fP1] using h))

theorem mem_E1G_iff {g : G} :
    g ∈ E1G c ↔ ∃ p : ↥P1h, (p : Ah) ∈ Subgroup.centralizer ({fhatA} : Set Ah) ∧
      c.iso.toG1 p = g := by
  constructor
  · rintro ⟨hM, hF⟩
    obtain ⟨p, rfl⟩ := exists_toG1 c hM
    exact ⟨p, (toG1_comm_iff c p).1 (Subgroup.mem_centralizer_singleton_iff.1 hF), rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨toG1_mem c p, Subgroup.mem_centralizer_singleton_iff.2 ((toG1_comm_iff c p).2 hp)⟩

theorem B1G_le_E1G : B1G c ≤ E1G c := by
  rintro g hg
  obtain ⟨p, hp, rfl⟩ := (mem_B1G_iff c).1 hg
  exact (mem_E1G_iff c).2 ⟨p, (Alt1h_le_C1 hp).2, rfl⟩

theorem card_E1G : Nat.card ↥(E1G c) = 96 := by
  have e : E1G c = ((P1h ⊓ Subgroup.centralizer ({fhatA} : Set Ah)).subgroupOf P1h).map
      c.iso.toG1 := by
    ext g
    rw [mem_E1G_iff, Subgroup.mem_map]
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, ⟨p.2, hp⟩, rfl⟩
    · rintro ⟨p, ⟨-, hp⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  rw [e, Subgroup.card_map_of_injective c.iso.toG1_injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  exact card_C1

theorem E1G_le_cen : E1G c ≤ cenOf (c.iso.toG fhB) := inf_le_right

theorem odd_mem_B1G {g : G} (hg : g ∈ E1G c) (hodd : Odd (orderOf g)) : g ∈ B1G c := by
  obtain ⟨p, hp, rfl⟩ := (mem_E1G_iff c).1 hg
  refine (mem_B1G_iff c).2 ⟨p, mem_Alt1h_of_odd ⟨p.2, hp⟩ ?_, rfl⟩
  have h1 : orderOf (c.iso.toG1 p) = orderOf p :=
    orderOf_injective c.iso.toG1 c.iso.toG1_injective p
  rw [h1, ← Subgroup.orderOf_coe] at hodd
  exact hodd

theorem B1G_eq_oddCl : B1G c = oddCl (E1G c) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨p, hp, rfl⟩ := (mem_B1G_iff c).1 hg
    obtain ⟨α, hα, β, hβ, hα3, hβ3, hpab⟩ := Alt1_prod _ hp
    have hmem : ∀ γ : Ah, γ ∈ Alt1h → γ ^ 3 = 1 → ∀ q : ↥P1h, (q : Ah) = γ →
        c.iso.toG1 q ∈ oddCl (E1G c) := by
      intro γ hγ hγ3 q hq
      refine mem_oddCl_of_pow_three (B1G_le_E1G c ((mem_B1G_iff c).2 ⟨q, hq ▸ hγ, rfl⟩)) ?_
      rw [← map_pow]
      have : q ^ 3 = 1 := Subtype.ext (by simpa [hq] using hγ3)
      rw [this, map_one]
    have hp' : p = ⟨α, Alt1h_le_C1.trans inf_le_left hα⟩ * ⟨β, Alt1h_le_C1.trans inf_le_left hβ⟩ :=
      Subtype.ext hpab
    rw [hp', map_mul]
    exact mul_mem (hmem α hα hα3 _ rfl) (hmem β hβ hβ3 _ rfl)
  · rw [oddCl, Subgroup.closure_le]
    exact fun y hy => odd_mem_B1G c hy.1 hy.2

theorem conj_E1G {R : Subgroup G} (h : F55Ctx c R) {n : G} (hn : n ∈ R) {g : G}
    (hg : g ∈ E1G c) : n * g * n⁻¹ ∈ E1G c := by
  set F := c.iso.toG fhB with hF
  have hnF : n * F = F * n := Subgroup.mem_centralizer_singleton_iff.1 (h.hR.1 hn)
  have hnF' : n * F * n⁻¹ = F := by rw [hnF]; group
  have hgF : g * F = F * g := Subgroup.mem_centralizer_singleton_iff.1 hg.2
  have hgz : g * z = z * g := by
    have : g ∈ cenOf z := by rw [c.cenOf_z]; exact hg.1
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  have hz : ∀ {m : G}, m ∈ R → m * z * m⁻¹ = z ∨ m * z * m⁻¹ = F * z :=
    fun hm => conj_z_R c h.h5 h.h6 h.ht0 h.hR h.hTR h.hR64 hm
  have hzn : ∃ w, (w = z ∨ w = F * z) ∧ n⁻¹ * z * n = w := by
    rcases hz (R.inv_mem hn) with h1 | h1
    · exact ⟨z, Or.inl rfl, by simpa using h1⟩
    · exact ⟨F * z, Or.inr rfl, by simpa using h1⟩
  obtain ⟨w, hw, hwn⟩ := hzn
  have hgw : g * w = w * g := by
    rcases hw with rfl | rfl
    · exact hgz
    · calc g * (F * z) = (g * F) * z := by group
        _ = (F * g) * z := by rw [hgF]
        _ = F * (g * z) := by group
        _ = F * (z * g) := by rw [hgz]
        _ = (F * z) * g := by group
  have hnwn : n * w * n⁻¹ = z := by rw [← hwn]; group
  have hnF'' : n⁻¹ * F * n = F := by
    calc n⁻¹ * F * n = n⁻¹ * (F * n) := by group
      _ = n⁻¹ * (n * F) := by rw [hnF]
      _ = F := by group
  refine ⟨?_, ?_⟩
  · rw [← c.cenOf_z]
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc n * g * n⁻¹ * z = n * (g * (n⁻¹ * z * n)) * n⁻¹ := by group
      _ = n * (g * w) * n⁻¹ := by rw [hwn]
      _ = n * (w * g) * n⁻¹ := by rw [hgw]
      _ = (n * w * n⁻¹) * (n * g * n⁻¹) := by group
      _ = z * (n * g * n⁻¹) := by rw [hnwn]
  · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc n * g * n⁻¹ * F = n * (g * (n⁻¹ * F * n)) * n⁻¹ := by group
      _ = n * (g * F) * n⁻¹ := by rw [hnF'']
      _ = n * (F * g) * n⁻¹ := by rw [hgF]
      _ = (n * F * n⁻¹) * (n * g * n⁻¹) := by group
      _ = F * (n * g * n⁻¹) := by rw [hnF']

end E1

end CFSG.Quasithin.H13.F431.U42Aut
