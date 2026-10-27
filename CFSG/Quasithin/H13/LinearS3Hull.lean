module

public import CFSG.Quasithin.SteinbergBSNoncentralHyperplane
public import CFSG.Quasithin.SteinbergCBWeakClosureCommute
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Quasithin.H13.LinearS3

open Subgroup CFSG.Quasithin.SteinbergBS
open scoped Pointwise

variable {G : Type*} [Group G]

theorem perm_three_normal_eq_top {N : Subgroup (Equiv.Perm (Fin 3))} (hN : N.Normal)
    {σ : Equiv.Perm (Fin 3)} (hσN : σ ∈ N) (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) : N = ⊤ := by
  have key : ∀ τ : Equiv.Perm (Fin 3), τ ≠ 1 → τ * τ = 1 →
      τ = Equiv.swap 0 1 ∨ τ = Equiv.swap 0 2 ∨ τ = Equiv.swap 1 2 := by decide
  have hsw : ∃ a b : Fin 3, a ≠ b ∧ σ = Equiv.swap a b := by
    rcases key σ hσ1 hσ2 with h | h | h
    · exact ⟨0, 1, by decide, h⟩
    · exact ⟨0, 2, by decide, h⟩
    · exact ⟨1, 2, by decide, h⟩
  obtain ⟨a, b, hab, rfl⟩ := hsw
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro τ ⟨c, d, hcd, rfl⟩
  obtain ⟨x, hx⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hab hcd)
  rw [← hx]
  exact hN.conj_mem _ hσN x

theorem conjugate_eq_smul (V : Subgroup G) (g : G) : conjugate V g = MulAut.conj g⁻¹ • V := by
  ext x
  rw [mem_conjugate_iff, SteinbergCB.mem_conj_inv_smul_iff]

theorem card_conjugate (V : Subgroup G) (g : G) : Nat.card (conjugate V g) = Nat.card V :=
  card_map_of_injective (MulAut.conj g⁻¹).injective

theorem sq_eq_one_of_mem_conjugate {V : Subgroup G} [IsElementaryAbelian 2 V] {g x : G}
    (hx : x ∈ conjugate V g) : x ^ 2 = 1 := by
  have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (mem_conjugate_iff.1 hx)
  rw [conj_pow] at h1
  have h2 : x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
  rw [h2, h1]
  group

theorem conjugate_le_of_mem {X H : Subgroup G} (hXH : X ≤ H) {k : G} (hk : k ∈ H) :
    conjugate X k ≤ H := by
  intro x hx
  have h1 := hXH (mem_conjugate_iff.1 hx)
  have h2 : x = k⁻¹ * (k * x * k⁻¹) * k := by group
  rw [h2]
  exact H.mul_mem (H.mul_mem (H.inv_mem hk) h1) hk

theorem conjugate_mono {X Y : Subgroup G} (hXY : X ≤ Y) (g : G) : conjugate X g ≤ conjugate Y g :=
  fun _ hx => mem_conjugate_iff.2 (hXY (mem_conjugate_iff.1 hx))

theorem conj_mem_iSup_conjugate {X H : Subgroup G} {k : G} (hk : k ∈ H) {x : G}
    (hx : x ∈ ⨆ h ∈ H, conjugate X h) : k * x * k⁻¹ ∈ ⨆ h ∈ H, conjugate X h := by
  have hle : (⨆ h ∈ H, conjugate X h) ≤
      (⨆ h ∈ H, conjugate X h).comap (MulAut.conj k).toMonoidHom := by
    refine iSup₂_le fun h hh y hy => ?_
    rw [mem_comap]
    have hmem : (MulAut.conj k).toMonoidHom y ∈ conjugate X (h * k⁻¹) := by
      rw [mem_conjugate_iff]
      have h1 := mem_conjugate_iff.1 hy
      rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        show h * k⁻¹ * (k * y * k⁻¹) * (h * k⁻¹)⁻¹ = h * y * h⁻¹ by group]
    exact le_iSup₂ (f := fun h (_ : h ∈ H) => conjugate X h) (h * k⁻¹)
      (H.mul_mem hh (H.inv_mem hk)) hmem
  have h1 := hle hx
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1

theorem le_normalizer_of_conj_mem {X H : Subgroup G}
    (h : ∀ k ∈ H, ∀ x ∈ X, k * x * k⁻¹ ∈ X) : H ≤ normalizer (X : Set G) := by
  intro k hk
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h k hk x, fun hx => ?_⟩
  have h1 := h k⁻¹ (H.inv_mem hk) _ hx
  rwa [show k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x by group] at h1

theorem not_isCyclic_of_four_le {B : Subgroup G} (hB : ∀ x ∈ B, x ^ 2 = 1)
    (h4 : 4 ≤ Nat.card B) : ¬ IsCyclic B := fun hc => by
  have := card_le_two_of_isCyclic hc hB
  omega

theorem centralizer_le_normalizer_conjugate {V : Subgroup G}
    (hcent : ∀ B : Subgroup G, B ≤ V → ¬ IsCyclic B →
      centralizer (B : Set G) ≤ normalizer (V : Set G)) (g : G) {B : Subgroup G}
    (hB : B ≤ conjugate V g) (hBc : ¬ IsCyclic B) :
    centralizer (B : Set G) ≤ normalizer (conjugate V g : Set G) := by
  have hB'V : conjugate B g⁻¹ ≤ V := by
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    have h1 := mem_conjugate_iff.1 (hB hx)
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
  have hB'c : ¬ IsCyclic (conjugate B g⁻¹) := by
    intro hc
    apply hBc
    have : IsCyclic ↥(B.map (MulAut.conj g⁻¹⁻¹).toMonoidHom) := hc
    exact isCyclic_of_surjective
      (B.equivMapOfInjective (MulAut.conj g⁻¹⁻¹).toMonoidHom (MulAut.conj g⁻¹⁻¹).injective).symm
      (MulEquiv.surjective _)
  intro c hc
  have hgc : g * c * g⁻¹ ∈ centralizer (conjugate B g⁻¹ : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, mem_conjugate_iff, inv_inv] at hy
    have h1 := (mem_centralizer_iff.1 hc) _ hy
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * y := by group
  have hN := hcent _ hB'V hB'c hgc
  rw [mem_normalizer_iff] at hN ⊢
  intro x
  rw [mem_conjugate_iff, mem_conjugate_iff, hN (g * x * g⁻¹),
    show g * c * g⁻¹ * (g * x * g⁻¹) * (g * c * g⁻¹)⁻¹ = g * (c * x * c⁻¹) * g⁻¹ by group]

theorem mem_inSubgroup_pCore_iff {H : Subgroup G} {x : ↥H} :
    (x : G) ∈ CFSG.inSubgroup (CFSG.pCore 2) H ↔ x ∈ CFSG.pCore 2 ↥H :=
  Subgroup.mem_map_iff_mem H.subtype_injective

theorem inSubgroup_pCore_le (H : Subgroup G) : CFSG.inSubgroup (CFSG.pCore 2) H ≤ H :=
  map_subtype_le _

theorem le_normalizer_inSubgroup_pCore (H : Subgroup G) :
    H ≤ normalizer (CFSG.inSubgroup (CFSG.pCore 2) H : Set G) := by
  refine le_normalizer_of_conj_mem fun k hk x hx => ?_
  have hxH : x ∈ H := inSubgroup_pCore_le H hx
  have hx' : (⟨x, hxH⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := mem_inSubgroup_pCore_iff.1 hx
  have h1 := (CFSG.pCore_normal (p := 2) (G := ↥H)).conj_mem _ hx' ⟨k, hk⟩
  exact mem_inSubgroup_pCore_iff.2 h1

theorem le_inSubgroup_pCore {H N : Subgroup G} (hNH : N ≤ H)
    (hHN : H ≤ normalizer (N : Set G)) (hN : IsPGroup 2 N) :
    N ≤ CFSG.inSubgroup (CFSG.pCore 2) H := by
  have hnorm : (N.subgroupOf H).Normal := by
    refine ⟨fun x hx k => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.1 (hHN k.2) x).1 hx
  have hp : IsPGroup 2 (N.subgroupOf H) := hN.of_equiv (subgroupOfEquivOfLe hNH).symm
  have hle : N.subgroupOf H ≤ CFSG.pCore 2 ↥H := le_sSup ⟨hnorm, hp⟩
  intro x hx
  exact mem_inSubgroup_pCore_iff.2
    (hle (show (⟨x, hNH hx⟩ : ↥H) ∈ N.subgroupOf H from mem_subgroupOf.2 hx))

theorem inSubgroup_pCore_le_sylow (T : Sylow 2 G) {H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) : CFSG.inSubgroup (CFSG.pCore 2) H ≤ T := by
  have h1 : CFSG.pCore 2 ↥H ≤ (T.subtype hTH : Subgroup ↥H) :=
    IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup (T.subtype hTH)
  intro x hx
  have hxH : x ∈ H := inSubgroup_pCore_le H hx
  have h2 := h1 ((mem_inSubgroup_pCore_iff (x := ⟨x, hxH⟩)).1 hx)
  rwa [Sylow.coe_subtype, mem_subgroupOf] at h2

theorem linear_S3_abelian_hull_obstruction [Finite G] (T : Sylow 2 G) {V : Subgroup G}
    [IsElementaryAbelian 2 V] {n : ℕ} (hVn : Nat.card V = 2 ^ n) (hn : 4 ≤ n)
    (hVT : V ≤ T) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (htrans : ∀ Z₁ : Subgroup G, Z₁ ≤ V → Nat.card Z₁ = 2 → ∀ Z₂ : Subgroup G, Z₂ ≤ V →
      Nat.card Z₂ = 2 → ∃ a ∈ normalizer (V : Set G), conjugate Z₁ a = Z₂)
    (hcent : ∀ B : Subgroup G, B ≤ V → ¬ IsCyclic B →
      centralizer (B : Set G) ≤ normalizer (V : Set G))
    (hhull : ∀ Z : Subgroup G, Z ≤ V → Nat.card Z = 2 →
      ∀ x ∈ ⨆ h ∈ normalizer (Z : Set G), conjugate V h,
        ∀ y ∈ ⨆ h ∈ normalizer (Z : Set G), conjugate V h, x * y = y * x)
    (hwc : ∀ g : G, conjugate V g ≤ T → ⁅V, conjugate V g⁆ = ⊥)
    {Z W H : Subgroup G} (_hZW : Z ≤ W) (hWV : W ≤ V) (hZ : Nat.card Z = 2)
    (_hW : Nat.card W = 4) (hTH : (T : Subgroup G) ≤ H) (hHZ : H ≤ normalizer (Z : Set G))
    (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hHW₀ : ¬ H ≤ normalizer
      ((⨆ (g : G) (_ : conjugate V g ≤ T), conjugate V g : Subgroup G) : Set G))
    (hS₃ : Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)))
    (hUab : ∀ x ∈ ⨆ h ∈ H, conjugate W h, ∀ y ∈ ⨆ h ∈ H, conjugate W h, x * y = y * x)
    (hUV : (⨆ h ∈ H, conjugate W h) ≤ centralizer (V : Set G))
    (hUQ : ⁅⨆ h ∈ H, conjugate W h, CFSG.inSubgroup (CFSG.pCore 2) H⁆ ≤ Z)
    (hWU : W < ⨆ h ∈ H, conjugate W h) : False := by
  classical
  set Q := CFSG.inSubgroup (CFSG.pCore 2) H with hQ
  set U := ⨆ h ∈ H, conjugate W h with hU
  have hQH : Q ≤ H := inSubgroup_pCore_le H
  have hQT : Q ≤ T := inSubgroup_pCore_le_sylow T hTH
  have hQn : H ≤ normalizer (Q : Set G) := le_normalizer_inSubgroup_pCore H
  have hQmax : ∀ N : Subgroup G, N ≤ H → H ≤ normalizer (N : Set G) → IsPGroup 2 N → N ≤ Q :=
    fun N hNH hHN hN => le_inSubgroup_pCore hNH hHN hN
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : V) ⟨y, hy⟩)
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  obtain ⟨e⟩ := hS₃
  let π : ↥H →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : ∀ x : ↥H, π x = 1 ↔ (x : G) ∈ Q := by
    intro x
    rw [hQ, mem_inSubgroup_pCore_iff]
    simp only [π, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hUH : U ≤ H := iSup₂_le fun k hk => conjugate_le_of_mem (hWV.trans (hVT.trans hTH)) hk
  have hHU : ∀ k ∈ H, ∀ x ∈ U, k * x * k⁻¹ ∈ U := fun k hk x hx =>
    conj_mem_iSup_conjugate hk hx
  have hU2 : ∀ x ∈ U, x ^ 2 = 1 := by
    let S : Subgroup G :=
      { carrier := {x | x ∈ U ∧ x ^ 2 = 1}
        mul_mem' := fun {x y} hx hy => ⟨U.mul_mem hx.1 hy.1, by
          rw [pow_two, show x * y * (x * y) = x * (y * x) * y by group, hUab y hy.1 x hx.1,
            show x * (x * y) * y = x ^ 2 * y ^ 2 by simp only [pow_two, mul_assoc], hx.2, hy.2,
            one_mul]⟩
        one_mem' := ⟨U.one_mem, one_pow 2⟩
        inv_mem' := fun {x} hx => ⟨U.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
    have hUS : U ≤ S := iSup₂_le fun k hk x hx =>
      ⟨le_iSup₂ (f := fun h (_ : h ∈ H) => conjugate W h) k hk hx,
        sq_eq_one_of_mem_conjugate (conjugate_mono hWV k hx)⟩
    exact fun x hx => (hUS hx).2
  have hUQle : U ≤ Q := by
    refine hQmax U hUH (le_normalizer_of_conj_mem hHU) fun x => ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hU2 x x.2
  have hZc : ∀ k ∈ H, ∀ z ∈ Z, k * z = z * k := by
    intro k hk z hz
    by_cases hz1 : z = 1
    · rw [hz1, mul_one, one_mul]
    have h1 : k * z * k⁻¹ ∈ Z := (mem_normalizer_iff.1 (hHZ hk) z).1 hz
    have h2 : k * z * k⁻¹ ≠ 1 := fun h => hz1 (by
      rw [show z = k⁻¹ * (k * z * k⁻¹) * k by group, h]
      group)
    have h3 := eq_of_card_le_two hZ.le h1 hz h2 hz1
    calc k * z = k * z * k⁻¹ * k := by group
      _ = z * k := by rw [h3]
  obtain ⟨g, hgT, hgQ⟩ : ∃ g : G, conjugate V g ≤ T ∧ ¬ conjugate V g ≤ Q := by
    by_contra hcon
    push Not at hcon
    apply hHW₀
    refine le_normalizer_of_conj_mem fun k hk x hx => ?_
    have hle : (⨆ (g : G) (_ : conjugate V g ≤ T), conjugate V g) ≤
        (⨆ (g : G) (_ : conjugate V g ≤ T), conjugate V g).comap
          (MulAut.conj k).toMonoidHom := by
      refine iSup₂_le fun g hg y hy => ?_
      rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hgk : conjugate V (g * k⁻¹) ≤ T := by
        intro z hz
        have hz' : k⁻¹ * z * k ∈ conjugate V g := by
          rw [mem_conjugate_iff]
          have h1 := mem_conjugate_iff.1 hz
          rwa [show g * (k⁻¹ * z * k) * g⁻¹ = g * k⁻¹ * z * (g * k⁻¹)⁻¹ by group]
        have h2 : k * (k⁻¹ * z * k) * k⁻¹ ∈ Q := (mem_normalizer_iff.1 (hQn hk) _).1
          (hcon g hg hz')
        rw [show k * (k⁻¹ * z * k) * k⁻¹ = z by group] at h2
        exact hQT h2
      have hmem : k * y * k⁻¹ ∈ conjugate V (g * k⁻¹) := by
        rw [mem_conjugate_iff]
        have h1 := mem_conjugate_iff.1 hy
        rwa [show g * k⁻¹ * (k * y * k⁻¹) * (g * k⁻¹)⁻¹ = g * y * g⁻¹ by group]
      exact le_iSup₂ (f := fun g (_ : conjugate V g ≤ T) => conjugate V g) (g * k⁻¹) hgk hmem
    have h1 := hle hx
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  have hA₀H : conjugate V g ≤ H := hgT.trans hTH
  obtain ⟨h, hhH, hAW⟩ : ∃ h ∈ H, ¬ conjugate V (g * h) ≤ normalizer (W : Set G) := by
    by_contra hcon
    push Not at hcon
    let R : Subgroup G := ⨆ k ∈ H, conjugate (conjugate V g) k
    have hRW : R ≤ normalizer (W : Set G) := iSup₂_le fun k hk => by
      rw [← conjugate_mul]
      exact hcon k hk
    have hRH : R ≤ H := iSup₂_le fun k hk => conjugate_le_of_mem hA₀H hk
    have hRn : (R.subgroupOf H).Normal := by
      refine ⟨fun r hr k => ?_⟩
      rw [mem_subgroupOf] at hr ⊢
      exact conj_mem_iSup_conjugate k.2 hr
    obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.1 hgQ
    have haR : a ∈ R := le_iSup₂ (f := fun k (_ : k ∈ H) => conjugate (conjugate V g) k) 1
      H.one_mem (by rwa [conjugate_one])
    have ha2 : (⟨a, hRH haR⟩ : ↥H) * ⟨a, hRH haR⟩ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, ← pow_two, sq_eq_one_of_mem_conjugate haA, Subgroup.coe_one]
    have htop := perm_three_normal_eq_top (hRn.map π hπs) (σ := π ⟨a, hRH haR⟩)
      ⟨⟨a, hRH haR⟩, mem_subgroupOf.2 haR, rfl⟩ (fun h1 => haQ ((hπker _).1 h1))
      (by rw [← map_mul, ha2, map_one])
    have hHW : ∀ k ∈ H, k ∈ normalizer (W : Set G) := by
      intro k hk
      have hk' : π ⟨k, hk⟩ ∈ (R.subgroupOf H).map π := by
        rw [htop]
        exact mem_top _
      obtain ⟨r, hr, hrk⟩ := hk'
      have hq : ((r⁻¹ * ⟨k, hk⟩ : ↥H) : G) ∈ Q :=
        (hπker _).1 (by rw [map_mul, map_inv, hrk, inv_mul_cancel])
      have hkr : k = (r : G) * ((r⁻¹ * ⟨k, hk⟩ : ↥H) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      rw [hkr]
      exact mul_mem (hRW (mem_subgroupOf.1 hr)) (hTW (hQT hq))
    exact (not_le_of_gt hWU) (iSup₂_le fun k hk => (conjugate_of_mem_normalizer (hHW k hk)).le)
  set A := conjugate V (g * h) with hAdef
  have hAH : A ≤ H := by
    rw [hAdef, conjugate_mul]
    exact conjugate_le_of_mem hA₀H hhH
  have hAQ : ¬ A ≤ Q := by
    intro hle
    apply hgQ
    intro x hx
    have h1 : h⁻¹ * x * h ∈ A := by
      rw [hAdef, mem_conjugate_iff]
      have h2 := mem_conjugate_iff.1 hx
      rwa [show g * h * (h⁻¹ * x * h) * (g * h)⁻¹ = g * x * g⁻¹ by group]
    have h3 := (mem_normalizer_iff.1 (hQn hhH) _).1 (hle h1)
    rwa [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at h3
  have hA2 : ∀ x ∈ A, x ^ 2 = 1 := fun x hx => sq_eq_one_of_mem_conjugate hx
  have hAcard : Nat.card A = 2 ^ n := by rw [card_conjugate, hVn]
  have hDi : Q.relIndex A = 2 := by
    let f : ↥A →* Equiv.Perm (Fin 3) := π.comp (Subgroup.inclusion hAH)
    have hker : f.ker = Q.subgroupOf A := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      exact hπker (Subgroup.inclusion hAH x)
    have hrel : Q.relIndex A = Nat.card f.range := by
      rw [relIndex, ← hker, index_ker]
    have hAp : IsPGroup 2 ↥A := fun x => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact hA2 x x.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hAp.of_surjective f.rangeRestrict
      f.rangeRestrict_surjective)
    have hdvd : 2 ^ k ∣ 6 := by
      rw [← hk]
      have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
      rw [← h6]
      exact card_subgroup_dvd_card _
    have hk2 : k < 2 := by
      by_contra hk2
      have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := h4.trans hdvd
      norm_num at this
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hAQ
      intro x hx
      have h1 : f ⟨x, hx⟩ ∈ f.range := ⟨⟨x, hx⟩, rfl⟩
      have hbot : f.range = ⊥ := by
        rw [← card_eq_one]
        simpa using hk
      rw [hbot, mem_bot] at h1
      exact (hπker (Subgroup.inclusion hAH ⟨x, hx⟩)).1 h1
    rw [hrel, hk]
    interval_cases k
    · exact absurd rfl hk0
    · rfl
  have hDcard : Nat.card ↥(Q ⊓ A) = 2 ^ (n - 1) := by
    have h1 := relIndex_mul_card Q A
    rw [hDi, hAcard] at h1
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hUA : U ≤ normalizer (A : Set G) := by
    intro u hu
    let f : ↥(Q ⊓ A) →* G :=
      { toFun := fun b => u * (b : G) * u⁻¹ * (b : G)⁻¹
        map_one' := by simp
        map_mul' := fun b₁ b₂ => by
          have hz : u * (b₂ : G) * u⁻¹ * (b₂ : G)⁻¹ ∈ Z := hUQ (by
            rw [← commutatorElement_def]
            exact commutator_mem_commutator hu b₂.2.1)
          have hc := hZc _ (hQH b₁.2.1) _ hz
          simp only [Subgroup.coe_mul, mul_inv_rev]
          calc u * ((b₁ : G) * b₂) * u⁻¹ * ((b₂ : G)⁻¹ * (b₁ : G)⁻¹)
              = u * b₁ * u⁻¹ * ((u * b₂ * u⁻¹ * (b₂ : G)⁻¹) * (b₁ : G)⁻¹) := by group
            _ = u * b₁ * u⁻¹ * ((b₁ : G)⁻¹ * (u * b₂ * u⁻¹ * (b₂ : G)⁻¹)) := by
              congr 1
              have hc' : (b₁ : G)⁻¹ * (u * b₂ * u⁻¹ * (b₂ : G)⁻¹) =
                  (u * b₂ * u⁻¹ * (b₂ : G)⁻¹) * (b₁ : G)⁻¹ := by
                calc (b₁ : G)⁻¹ * (u * b₂ * u⁻¹ * (b₂ : G)⁻¹)
                    = (b₁ : G)⁻¹ * ((u * b₂ * u⁻¹ * (b₂ : G)⁻¹) * b₁) * (b₁ : G)⁻¹ := by
                      group
                  _ = (b₁ : G)⁻¹ * (b₁ * (u * b₂ * u⁻¹ * (b₂ : G)⁻¹)) * (b₁ : G)⁻¹ := by
                      rw [← hc]
                  _ = (u * b₂ * u⁻¹ * (b₂ : G)⁻¹) * (b₁ : G)⁻¹ := by group
              rw [hc']
            _ = u * b₁ * u⁻¹ * (b₁ : G)⁻¹ * (u * b₂ * u⁻¹ * (b₂ : G)⁻¹) := by group }
    have hfZ : f.range ≤ Z := by
      rintro _ ⟨b, rfl⟩
      exact hUQ (by
        change u * (b : G) * u⁻¹ * (b : G)⁻¹ ∈ _
        rw [← commutatorElement_def]
        exact commutator_mem_commutator hu b.2.1)
    have hker : f.ker = (centralizer ({u} : Set G)).subgroupOf (Q ⊓ A) := by
      ext b
      rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_singleton_iff]
      change u * (b : G) * u⁻¹ * (b : G)⁻¹ = 1 ↔ _
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    have hci : (centralizer ({u} : Set G)).relIndex (Q ⊓ A) ≤ 2 := by
      rw [relIndex, ← hker, index_ker, ← hZ]
      exact card_le_of_le hfZ
    have hCcard : 4 ≤ Nat.card ↥(centralizer ({u} : Set G) ⊓ (Q ⊓ A)) := by
      have h1 := relIndex_mul_card (centralizer ({u} : Set G)) (Q ⊓ A)
      rw [hDcard] at h1
      have h2 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
        rw [← pow_succ']
        congr 1
        omega
      have h3 : 4 ≤ 2 ^ (n - 2) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h5 := Nat.mul_le_mul_right (Nat.card ↥(centralizer ({u} : Set G) ⊓ (Q ⊓ A))) hci
      omega
    have hCA : centralizer ({u} : Set G) ⊓ (Q ⊓ A) ≤ A := inf_le_right.trans inf_le_right
    have hCc : ¬ IsCyclic ↥(centralizer ({u} : Set G) ⊓ (Q ⊓ A)) :=
      not_isCyclic_of_four_le (fun x hx => hA2 x (hCA hx)) hCcard
    have hu' : u ∈ centralizer ((centralizer ({u} : Set G) ⊓ (Q ⊓ A) : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro c hc
      exact mem_centralizer_singleton_iff.1 hc.1
    exact centralizer_le_normalizer_conjugate hcent (g * h) hCA hCc hu'
  have hcomm : ∀ x : G, MulAut.conj x⁻¹ • V ≤ T → ⁅V, MulAut.conj x⁻¹ • V⁆ = ⊥ := by
    intro x hx
    rw [← conjugate_eq_smul] at hx ⊢
    exact hwc x hx
  have hVsmul : ∃ a : G, V = MulAut.conj a⁻¹ • V := ⟨1, by rw [inv_one, map_one, one_smul]⟩
  have hAsmul : ∃ a : G, A = MulAut.conj a⁻¹ • V := ⟨g * h, conjugate_eq_smul V (g * h)⟩
  have hAWc : ⁅A, V⁆ = ⊥ → False := by
    intro hAV
    apply hAW
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ ?_
    have h1 := (commutator_eq_bot_iff_le_centralizer.1 hAV) ha
    exact centralizer_le (SetLike.coe_subset_coe.2 hWV) h1
  have hAV : ¬ A ≤ normalizer (V : Set G) := by
    intro hle
    have h1 := SteinbergCB.linear_weak_closure_normalizing_conjugates_centralize T hVT hTV hcomm
      V A hVsmul hAsmul hle
    rw [commutator_comm] at h1
    exact hAWc h1
  have hDA : Q ⊓ A ≤ A := inf_le_right
  have hDV : Q ⊓ A ≤ normalizer (V : Set G) := inf_le_left.trans (hQT.trans hTV)
  have hDV1 : ⁅Q ⊓ A, V⁆ ≠ ⊥ := by
    intro hDV1
    have hDc : ¬ IsCyclic ↥(Q ⊓ A) := by
      refine not_isCyclic_of_four_le (fun x hx => hA2 x hx.2) ?_
      rw [hDcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hVD : V ≤ centralizer ((Q ⊓ A : Subgroup G) : Set G) := by
      rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
      exact hDV1
    have hVA : V ≤ normalizer (A : Set G) :=
      hVD.trans (centralizer_le_normalizer_conjugate hcent (g * h) hDA hDc)
    have h1 := SteinbergCB.linear_weak_closure_normalizing_conjugates_centralize T hVT hTV hcomm
      A V hAsmul hVsmul hVA
    exact hAWc h1
  have hNVA : V ⊓ normalizer (A : Set G) ≤ normalizer ((Q ⊓ A : Subgroup G) : Set G) := by
    intro v hv
    have hvV : v ∈ V := (mem_inf.1 hv).1
    have hvA : v ∈ normalizer (A : Set G) := (mem_inf.1 hv).2
    have hvQ := hQn (hTH (hVT hvV))
    rw [mem_normalizer_iff] at hvQ hvA ⊢
    intro x
    rw [mem_inf, mem_inf, hvQ x, hvA x]
  have hDrel : (Q ⊓ A).relIndex A = 2 := by rw [inf_relIndex_right, hDi]
  have hCDV := linear_noncentral_hyperplane_faithfulness hVn hn htrans hcent hhull
    ⟨g * h, rfl⟩ hAV hDA hDrel hDV hDV1 hNVA
  apply hAW
  intro a ha
  refine Subgroup.centralizer_le_normalizer _ (centralizer_le (SetLike.coe_subset_coe.2 hWU.le) ?_)
  rw [mem_centralizer_iff]
  intro u hu
  have hc : u * a * u⁻¹ * a⁻¹ ∈ (Q ⊓ A) ⊓ centralizer (V : Set G) := by
    refine ⟨⟨hUQle ?_, ?_⟩, hUV ?_⟩
    · rw [show u * a * u⁻¹ * a⁻¹ = u * (a * u⁻¹ * a⁻¹) by group]
      exact U.mul_mem hu (hHU a (hAH ha) _ (U.inv_mem hu))
    · exact A.mul_mem ((mem_normalizer_iff.1 (hUA hu) a).1 ha) (A.inv_mem ha)
    · rw [show u * a * u⁻¹ * a⁻¹ = u * (a * u⁻¹ * a⁻¹) by group]
      exact U.mul_mem hu (hHU a (hAH ha) _ (U.inv_mem hu))
  rw [hCDV, mem_bot] at hc
  calc u * a = u * a * u⁻¹ * a⁻¹ * (a * u) := by group
    _ = a * u := by rw [hc, one_mul]

end CFSG.Quasithin.H13.LinearS3
