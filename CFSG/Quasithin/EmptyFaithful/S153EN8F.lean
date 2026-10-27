module

public import CFSG.Quasithin.EmptyFaithful.S153EN8E
public import CFSG.Quasithin.EmptyFaithful.S153EN8B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153EN8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t} {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

section Decomp

variable (h113 : StageLemma14113) (c : Chain15359 cx N₁ N₂ g s y t₁) (B : BarModel cx)
  {d : G} (hdM : d ∈ M)

theorem exists_ne_one_commV₁ : ∃ u ∈ commV B.L₁, u ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have h0 : commV B.L₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
  have h4 := B.hS.card_U₁
  rw [h0, Subgroup.card_bot] at h4
  omega

include c B hdM in
theorem barM_not_mem_N (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hbd : barM cx hdM ∈ B.L₂)
    {N : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))}
    (hiso : Nonempty (↥N ≃* Equiv.Perm (Fin 3))) (hNtop : commV N = ⊤) (hN : barM cx hdM ∈ N) :
    False := by
  obtain ⟨e⟩ := hiso
  have hfix := S153E55.fixV_eq_bot_of_perm IntMod.sq_eq_one e hNtop hN (barM_cube hdM hd3)
    (barM_ne_one c hdM hd3 hd1)
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_commV₁ B
  have hu' : u ∈ fixV (Subgroup.zpowers (barM cx hdM)) :=
    mem_fixV_zpowers_iff.2 (B.hS.L₂_fix₁ hbd hu)
  rw [hfix] at hu'
  exact hu1 (Subgroup.mem_bot.1 hu')

theorem decomp_aux (c54 : Chain15354 cx N₁ N₂ g s) {Na Nb : Subgroup (MulAut ↥(VZ T M))}
    (hdM : d ∈ M) (hdI : d ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc)
    {α β : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)} (hα : α ∈ Na) (hβ : β ∈ Nb)
    (hαI : α ∈ autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc))
    (hβI : β ∈ autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc))
    (hαβ : α * β = barM cx hdM) (hα1 : α ≠ 1) :
    ∃ na nb : G, d = na * nb ∧ na ∈ Ni153 T Mc M V₁ Na ∧ nb ∈ Ni153 T Mc M V₁ Nb ∧
      na ∉ Pgp153 T M V₁ Mc g := by
  have hV := cx.c.hyp.elemAbelian
  have hI := c54.h54.one
  obtain ⟨m₁, hm₁I, hm₁⟩ := (mem_autI hV).1 hαI
  obtain ⟨m₂, hm₂I, hm₂⟩ := (mem_autI hV).1 hβI
  have hm₁Ni : (m₁ : G) ∈ Ni153 T Mc M V₁ Na :=
    S153E.mem_preAut153.2 ⟨hm₁I, m₁.2, by
      have : conjAct (VZ T M) ⟨(m₁ : G), m₁.2⟩ = α := hm₁
      rw [this]
      exact hα⟩
  have hm₂Ni : (m₂ : G) ∈ Ni153 T Mc M V₁ Nb :=
    S153E.mem_preAut153.2 ⟨hm₂I, m₂.2, by
      have : conjAct (VZ T M) ⟨(m₂ : G), m₂.2⟩ = β := hm₂
      rw [this]
      exact hβ⟩
  have hdN : d ∈ Subgroup.normalizer (VZ T M : Set G) := cx.c.hyp.le_normalizer hdM
  have hk : convI hV (⟨d, hdN⟩ * (m₁ * m₂)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, hm₁, hm₂, hαβ]
    show barM cx hdM * (barM cx hdM)⁻¹ = 1
    exact mul_inv_cancel _
  have hkC : d * ((m₁ : G) * (m₂ : G))⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) :=
    (convI_eq_one_iff hV _).1 hk
  have hkI : d * ((m₁ : G) * (m₂ : G))⁻¹ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc :=
    (Y153 Mc M ⊔ UH153 T M V₁ Mc).mul_mem hdI ((Y153 Mc M ⊔ UH153 T M V₁ Mc).inv_mem
      ((Y153 Mc M ⊔ UH153 T M V₁ Mc).mul_mem hm₁I hm₂I))
  have heP : d * ((m₁ : G) * (m₂ : G))⁻¹ ∈ Pgp153 T M V₁ Mc g :=
    S153E55.centralizer_le_P hI cx ⟨hkI, hkC⟩
  refine ⟨d * ((m₁ : G) * (m₂ : G))⁻¹ * (m₁ : G), (m₂ : G), by group,
    (Ni153 T Mc M V₁ Na).mul_mem (P_le_Ni c54 Na heP) hm₁Ni, hm₂Ni, ?_⟩
  intro hP
  have hm₁P : (m₁ : G) ∈ Pgp153 T M V₁ Mc g := by
    have := (Pgp153 T M V₁ Mc g).mul_mem ((Pgp153 T M V₁ Mc g).inv_mem heP) hP
    simpa [mul_assoc] using this
  have hm₁C := P_le_centralizer c54 hm₁P
  exact hα1 (hm₁ ▸ (convI_eq_one_iff hV m₁).2 hm₁C)

include c B hdM in
theorem exists_decomp (hdY : d ∈ Y153 Mc M) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hbd : barM cx hdM ∈ B.L₂) :
    ∃ n₁ n₂ n₂' n₁' : G, d = n₁ * n₂ ∧ n₁ ∈ Ni153 T Mc M V₁ N₁ ∧ n₂ ∈ Ni153 T Mc M V₁ N₂ ∧
      n₁ ∉ Pgp153 T M V₁ Mc g ∧ d = n₂' * n₁' ∧ n₂' ∈ Ni153 T Mc M V₁ N₂ ∧
      n₁' ∈ Ni153 T Mc M V₁ N₁ ∧ n₂' ∉ Pgp153 T M V₁ Mc g := by
  have hV := cx.c.hyp.elemAbelian
  have hdI : d ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.mem_sup_left hdY
  have hΩ := S153E55.autI_YU_eq cx c.h53one
  have haΩ : barM cx hdM ∈ N₁ ⊔ N₂ := by
    rw [← hΩ]
    exact convI_mem_autI hV hdI (S153E55.YU_le_normalizer_V cx hdI)
  obtain ⟨a, ha, b, hb, hab⟩ := S1417.exists_mul_of_mem_sup_of_commute c.h53one.comm haΩ
  have haI : a ∈ autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
    rw [hΩ]
    exact Subgroup.mem_sup_left ha
  have hbI : b ∈ autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
    rw [hΩ]
    exact Subgroup.mem_sup_right hb
  have hcomm : a * b = b * a := c.h53one.comm a ha b hb
  have hN₁I : N₁ ≤ autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
    rw [hΩ]
    exact le_sup_left
  have hN₂I : N₂ ≤ autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
    rw [hΩ]
    exact le_sup_right
  have htop₁ : commV (V := IntMod (VZ T M) hV) N₁ = ⊤ := S153E55.commV_eq_top cx hN₁I c.h53one.comm₁
  have htop₂ : commV (V := IntMod (VZ T M) hV) N₂ = ⊤ := S153E55.commV_eq_top cx hN₂I c.h53one.comm₂
  have ha1 : a ≠ 1 := by
    intro h
    refine barM_not_mem_N c B hdM hd3 hd1 hbd c.h53one.iso₂ htop₂ ?_
    rw [← hab, h, one_mul]
    exact hb
  have hb1 : b ≠ 1 := by
    intro h
    refine barM_not_mem_N c B hdM hd3 hd1 hbd c.h53one.iso₁ htop₁ ?_
    rw [← hab, h, mul_one]
    exact ha
  obtain ⟨n₁, n₂, hd12, hn₁, hn₂, hn₁P⟩ :=
    decomp_aux c.toChain15354 hdM hdI ha hb haI hbI hab ha1
  obtain ⟨n₂', n₁', hd21, hn₂', hn₁', hn₂'P⟩ :=
    decomp_aux c.toChain15354 hdM hdI hb ha hbI haI (hcomm.symm.trans hab) hb1
  exact ⟨n₁, n₂, n₂', n₁', hd12, hn₁, hn₂, hn₁P, hd21, hn₂', hn₁', hn₂'P⟩

include h113 c B hdM in
theorem centralizer_Q_le_V₁ (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hbd : barM cx hdM ∈ B.L₂) {x : G}
    (hxQ : x ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G)) (hxd : x * d = d * x) : x ∈ V₁ := by
  have hdY := mem_Y h113 c hdM hd3
  obtain ⟨n₁, n₂, n₂', n₁', hd12, hn₁, hn₂, hn₁P, hd21, hn₂', hn₁', hn₂'P⟩ :=
    exists_decomp c B hdM hdY hd3 hd1 hbd
  have hpd := S153E55.pdecomp cx c.toChain15354
  have hxP : x ∈ Pgp153 T M V₁ Mc g := Q_le_P h113 c.toChain15358 hxQ
  obtain rfl : s = 1 := c.h58.two_s
  have hdx : d * x * d⁻¹ = x := by
    calc d * x * d⁻¹ = (x * d) * d⁻¹ := by rw [hxd]
      _ = x := by group
  have hxV : x ∈ VZ T M :=
    fixed_mem_V hpd c.h54.four_nat₁ c.h54.four_nat₂ hd12 hn₁ hn₂ hn₁P hd21 hn₂' hn₁' hn₂'P
      (k := 1) (by simpa using hd3) hxP hdx
  have hV := cx.c.hyp.elemAbelian
  set xt : IntMod (VZ T M) hV := IntMod.mk hV ⟨x, hxV⟩ with hxt
  have hfix : barM cx hdM xt = xt := by
    refine IntMod.val_injective ?_
    rw [barM_apply_val]
    exact hdx
  have hmem : xt ∈ commV B.L₁ :=
    (fix_iff_mem_commV₁ B.hS hbd (odd_orderOf_of_cube (barM_cube hdM hd3))
      (barM_ne_one c hdM hd3 hd1) xt).1 hfix
  rw [← B.hV₁, mem_map_inclMod_iff]
  exact ⟨xt, hmem, rfl⟩

end Decomp

end S153EN8

end CFSG.Quasithin
