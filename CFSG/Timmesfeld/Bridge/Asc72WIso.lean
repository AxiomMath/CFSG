module

public import CFSG.Timmesfeld.Bridge.Asc72WInner
public import CFSG.Timmesfeld.Bridge.Asc72WAct

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open Equiv CFSG.BenderSuzuki SemidirectProduct

namespace WreathData

variable {G : Type} [Group G] {D : Set G} {M : Subgroup G} (W : WreathData G D M)

section Transport

variable {L : Type*} [Group L] {i₀ : Fin W.r} {t : Fin W.r → G}
  (htπ : ∀ l, W.π (t l) = Equiv.swap i₀ l)

@[expose] def conjIso (l : Fin W.r) : W.S l ≃* W.S i₀ :=
  ((MulAut.conj (t l)).subgroupMap (W.S l)).trans (MulEquiv.subgroupCongr
    ((show (W.S l).map (MulAut.conj (t l) : G →* G) = (W.S l).map (MulAut.conj (t l)).toMonoidHom
      from rfl).trans ((W.conj (t l) l).trans (by rw [htπ l, Equiv.swap_apply_right]))))

theorem coe_conjIso (l : Fin W.r) (x : W.S l) : (W.conjIso htπ l x : G) = t l * x * (t l)⁻¹ :=
  rfl

theorem coe_conjIso_symm (l : Fin W.r) (z : W.S i₀) :
    ((W.conjIso htπ l).symm z : G) = (t l)⁻¹ * z * t l := by
  have h := congrArg Subtype.val ((W.conjIso htπ l).apply_symm_apply z)
  rw [coe_conjIso] at h
  rw [← h]
  group

variable (ψ₀ : W.S i₀ ≃* L)

@[expose] def transport (l : Fin W.r) : W.S l ≃* L := (W.conjIso htπ l).trans ψ₀

theorem coe_transport_symm (l : Fin W.r) (y : L) :
    ((W.transport htπ ψ₀ l).symm y : G) = (t l)⁻¹ * (ψ₀.symm y : G) * t l := by
  rw [transport, MulEquiv.symm_trans_apply, coe_conjIso_symm]

@[expose] def baseEquiv : (Fin W.r → L) ≃* M :=
  (MulEquiv.piCongrRight fun l => (W.transport htπ ψ₀ l).symm).trans W.e

theorem coe_baseEquiv_mulSingle (l : Fin W.r) (y : L) :
    ((W.baseEquiv htπ ψ₀ (Pi.mulSingle l y) : M) : G) = (t l)⁻¹ * (ψ₀.symm y : G) * t l := by
  have h : MulEquiv.piCongrRight (fun l => (W.transport htπ ψ₀ l).symm) (Pi.mulSingle l y) =
      Pi.mulSingle l ((W.transport htπ ψ₀ l).symm y) := by
    funext k
    rw [MulEquiv.piCongrRight_apply]
    exact Pi.apply_mulSingle (fun k => (W.transport htπ ψ₀ k).symm) (fun k => map_one _) l y k
  rw [baseEquiv, MulEquiv.trans_apply, h, W.e_mulSingle, coe_transport_symm]

variable [M.Normal]

@[expose] def baseAct : G →* MulAut (Fin W.r → L) :=
  (MulAut.congr (W.baseEquiv htπ ψ₀).symm).toMonoidHom.comp MulAut.conjNormal

theorem baseAct_apply_eq_iff (g : G) (x y : Fin W.r → L) :
    W.baseAct htπ ψ₀ g x = y ↔
      ((W.baseEquiv htπ ψ₀ y : M) : G) = g * (W.baseEquiv htπ ψ₀ x : G) * g⁻¹ := by
  rw [baseAct, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_eq,
    ← Subtype.coe_inj, MulAut.conjNormal_apply, eq_comm]

theorem baseAct_injective (hC : Subgroup.centralizer (M : Set G) = ⊥) :
    Function.Injective (W.baseAct htπ ψ₀) := by
  refine (injective_iff_map_eq_one _).mpr fun g hg => ?_
  have hmem : g ∈ Subgroup.centralizer (M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    obtain ⟨x, hx⟩ := (W.baseEquiv htπ ψ₀).surjective ⟨m, hm⟩
    have h := (W.baseAct_apply_eq_iff htπ ψ₀ g x x).mp (by rw [hg]; rfl)
    rw [hx] at h
    calc m * g = (g * m * g⁻¹) * g := by rw [← h]
      _ = g * m := by group
  rw [hC] at hmem
  exact hmem

variable [Finite G] in
theorem baseAct_eq_act (hS : Setup G D) (ht0 : t i₀ = 1) (htD : ∀ l, l ≠ i₀ → t l ∈ D)
    {u : G} (hu : u ∈ D) {i j : Fin W.r} (hij : i ≠ j) (huπ : W.π u = Equiv.swap i j)
    (hcomm : ∀ k, k ≠ i → k ≠ j → ∀ x ∈ W.S k, Commute u x) :
    ∃ h : Fin W.r → L, W.baseAct htπ ψ₀ u = WreathAct.act L W.r ⟨h, Equiv.swap i j⟩ ∧
      (∀ k, k ≠ i → k ≠ j → h k = 1) ∧ h j = (h i)⁻¹ := by
  classical
  obtain ⟨m₀, hm₀, hinner⟩ := W.innerOn_conj_swap hS ht0 htD htπ hu hij huπ hcomm
  set m : L := ψ₀ ⟨m₀, hm₀⟩ with hmdef
  have hψm : (ψ₀.symm m : G) = m₀ := by rw [hmdef, MulEquiv.symm_apply_apply]
  have hui : u⁻¹ = u := hS.oddT.inv_eq hu
  set h : Fin W.r → L := Pi.mulSingle j m * Pi.mulSingle i m⁻¹ with hhdef
  have hhj : h j = m := by
    rw [hhdef, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hij), mul_one]
  have hhi : h i = m⁻¹ := by
    rw [hhdef, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij, one_mul]
  have hhk : ∀ k, k ≠ i → k ≠ j → h k = 1 := fun k hki hkj => by
    rw [hhdef, Pi.mul_apply, Pi.mulSingle_eq_of_ne hkj, Pi.mulSingle_eq_of_ne hki, one_mul]
  refine ⟨h, ?_, hhk, by rw [hhj, hhi, inv_inv]⟩
  apply MulEquiv.toMonoidHom_injective
  refine MonoidHom.pi_ext fun k y => ?_
  simp only [MulEquiv.coe_toMonoidHom]
  rw [WreathAct.act_mulSingle, W.baseAct_apply_eq_iff, coe_baseEquiv_mulSingle,
    coe_baseEquiv_mulSingle]
  show (t (Equiv.swap i j k))⁻¹ * (ψ₀.symm (h (Equiv.swap i j k) * y *
    (h (Equiv.swap i j k))⁻¹) : G) * t (Equiv.swap i j k) =
    u * ((t k)⁻¹ * (ψ₀.symm y : G) * t k) * u⁻¹
  set Y : G := (ψ₀.symm y : G) with hYdef
  have hY : Y ∈ W.S i₀ := (ψ₀.symm y).2
  by_cases hki : k = i
  · subst hki
    rw [Equiv.swap_apply_left, hhj, map_mul, map_mul, map_inv]
    push_cast
    rw [hψm, ← hYdef, ← hinner Y hY]
    group
  by_cases hkj : k = j
  · subst hkj
    rw [Equiv.swap_apply_right, hhi, map_mul, map_mul, map_inv, inv_inv]
    push_cast
    rw [hψm, ← hYdef]
    have hX : m₀⁻¹ * Y * m₀ ∈ W.S i₀ :=
      (W.S i₀).mul_mem ((W.S i₀).mul_mem ((W.S i₀).inv_mem hm₀) hY) hm₀
    have h1 := hinner _ hX
    have h2 : m₀ * (m₀⁻¹ * Y * m₀) * m₀⁻¹ = Y := by group
    rw [h2] at h1
    have h3 : m₀⁻¹ * Y * m₀ = (t k * u * (t i)⁻¹)⁻¹ * Y * (t k * u * (t i)⁻¹) := by
      calc m₀⁻¹ * Y * m₀ = (t k * u * (t i)⁻¹)⁻¹ * (t k * u * (t i)⁻¹ * (m₀⁻¹ * Y * m₀) *
            (t k * u * (t i)⁻¹)⁻¹) * (t k * u * (t i)⁻¹) := by group
        _ = (t k * u * (t i)⁻¹)⁻¹ * Y * (t k * u * (t i)⁻¹) := by rw [h1]
    rw [h3]
    calc (t i)⁻¹ * ((t k * u * (t i)⁻¹)⁻¹ * Y * (t k * u * (t i)⁻¹)) * t i
        = u⁻¹ * ((t k)⁻¹ * Y * t k) * u := by group
      _ = u * ((t k)⁻¹ * Y * t k) * u⁻¹ := by rw [hui]
  · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, hhk k hki hkj, one_mul, inv_one, mul_one]
    have hmem : (t k)⁻¹ * Y * t k ∈ W.S k := by
      rw [← coe_transport_symm W htπ ψ₀ k y]
      exact ((W.transport htπ ψ₀ k).symm y).2
    rw [← hYdef, (hcomm k hki hkj _ hmem).eq, mul_inv_cancel_right]

end Transport

variable [Finite G] in
theorem exists_mulEquiv_l2Wreath (hS : Setup G D) [M.Normal]
    (hC : Subgroup.centralizer (M : Set G) = ⊥) :
    ∃ f : ℕ, 2 ≤ f ∧ ∃ Φ : G ≃* L2Wreath f W.r, ∀ u ∈ D, ∃ i j : Fin W.r, i ≠ j ∧
      (Φ u).right = Equiv.swap i j ∧ (∀ k, k ≠ i → k ≠ j → (Φ u).left k = 1) ∧
      (Φ u).left j = ((Φ u).left i)⁻¹ := by
  classical
  set i₀ : Fin W.r := ⟨0, by have := W.two_le; omega⟩ with hi₀
  obtain ⟨f, hf, ⟨ψ₀⟩⟩ := wreathData_factor_psl2 hS W i₀
  have hex : ∀ l : Fin W.r, ∃ t : G, (l ≠ i₀ → t ∈ D) ∧ W.π t = Equiv.swap i₀ l ∧
      (l = i₀ → t = 1) := by
    intro l
    by_cases hl : l = i₀
    · refine ⟨1, fun h => absurd hl h, ?_, fun _ => rfl⟩
      rw [hl, map_one, Equiv.swap_self]
      rfl
    · obtain ⟨u, hu, huπ⟩ := W.exists_mem_swap hS (Ne.symm hl)
      exact ⟨u, fun _ => hu, huπ, fun h => absurd h hl⟩
  choose t htD htπ ht1 using hex
  have ht0 : t i₀ = 1 := ht1 i₀ rfl
  have hB : IsBenderGroup (PSL2Model f) := .isPSL2 f hf (MulEquiv.refl _)
  have := IsBenderGroup.isSimpleGroup hB
  have hLZ : ∀ z : PSL2Model f, (∀ y, z * y = y * z) → z = 1 := by
    intro z hz
    have hc : Subgroup.center (PSL2Model f) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PSL2Model f)) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hB
        exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
    have hzc : z ∈ Subgroup.center (PSL2Model f) :=
      Subgroup.mem_center_iff.mpr fun y => (hz y).symm
    rw [hc] at hzc
    exact hzc
  have hιG := W.baseAct_injective htπ ψ₀ hC
  have hιW := WreathAct.act_injective (L := PSL2Model f) (n := W.r) hLZ
  have hle : (W.baseAct htπ ψ₀).range ≤ (WreathAct.act (PSL2Model f) W.r).range := by
    rw [MonoidHom.range_eq_map, ← hS.gen, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨i, j, hij, huπ, hcomm⟩ := W.swap u hu
    obtain ⟨h, hh, -, -⟩ := W.baseAct_eq_act htπ ψ₀ hS ht0 (fun l hl => htD l hl) hu hij huπ
      hcomm
    exact ⟨_, hh.symm⟩
  have hcardM : Nat.card M = Nat.card (PSL2Model f) ^ W.r := by
    rw [← Nat.card_congr (W.baseEquiv htπ ψ₀).toEquiv, Nat.card_fun, Nat.card_fin]
  have hcardG : Nat.card (L2Wreath f W.r) ≤ Nat.card G := by
    rw [WreathAct.card_wreath, Subgroup.card_eq_card_quotient_mul_card_subgroup W.π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange W.π).toEquiv,
      MonoidHom.range_eq_top.mpr (W.π_surjective hS), Subgroup.card_top, Nat.card_perm,
      Nat.card_fin, mul_comm]
    refine Nat.mul_le_mul_left _ ?_
    rw [← hcardM]
    exact Subgroup.card_le_of_le fun m hm => W.π_eq_one_of_mem hm
  have : Finite (L2Wreath f W.r) := WreathAct.finite_wreath
  have : Finite (WreathAct.act (PSL2Model f) W.r).range :=
    Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have heq : (W.baseAct htπ ψ₀).range = (WreathAct.act (PSL2Model f) W.r).range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hιW).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hιG).toEquiv]
    exact hcardG
  let Φ : G ≃* L2Wreath f W.r := (MonoidHom.ofInjective hιG).trans
    ((MulEquiv.subgroupCongr heq).trans (MonoidHom.ofInjective hιW).symm)
  have hΦ : ∀ g, WreathAct.act (PSL2Model f) W.r (Φ g) = W.baseAct htπ ψ₀ g := by
    intro g
    rw [← MonoidHom.ofInjective_apply hιW]
    simp only [Φ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    exact MonoidHom.ofInjective_apply hιG
  refine ⟨f, hf, Φ, fun u hu => ?_⟩
  obtain ⟨i, j, hij, huπ, hcomm⟩ := W.swap u hu
  obtain ⟨h, hh, h1, h2⟩ := W.baseAct_eq_act htπ ψ₀ hS ht0 (fun l hl => htD l hl) hu hij huπ
    hcomm
  have hΦu : Φ u = ⟨h, Equiv.swap i j⟩ := hιW (by rw [hΦ, hh])
  exact ⟨i, j, hij, by rw [hΦu], by rw [hΦu]; exact h1, by rw [hΦu]; exact h2⟩

end WreathData

end CFSG.Timmesfeld.Bridge.Asc72
