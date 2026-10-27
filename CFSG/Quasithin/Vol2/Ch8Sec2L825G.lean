module

public import CFSG.Quasithin.Background.E2Pair
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch8Sec2Defs
public import CFSG.Quasithin.Vol2.Ch8Sec2L825E
public import CFSG.Quasithin.Vol2.E2StatementsAS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.ASInputs

section L825G

variable {G : Type} [Group G]

theorem fixV_sup_82 {W : Type*} [CommGroup W] (X Y : Subgroup (MulAut W)) :
    fixV (X ⊔ Y) = fixV X ⊓ fixV Y :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq X Y

theorem autI_zpowers_82 {V : Subgroup G} (hV : IsElemAbelian 2 V) {x : G}
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) :
    autI hV (Subgroup.zpowers x) = Subgroup.zpowers (convI hV ⟨x, hxN⟩) := by
  ext φ
  rw [mem_autI]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hgx : g = ⟨x, hxN⟩ ^ n := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn.symm)
    rw [hgx, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ n
  · intro hφ
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hφ
    refine ⟨⟨x, hxN⟩ ^ n, ?_, map_zpow _ _ _⟩
    rw [Subgroup.coe_zpow]
    exact Subgroup.zpow_mem_zpowers x n

variable [Finite G]

theorem mem_centralizer_of_conj_82 {T N V : Subgroup G} {h : G}
    (hP : E2.Pair (ch82I V h) T N V h) (hNV : N ≤ Subgroup.normalizer (V : Set G))
    (h3 : ∀ X : Subgroup G, X ≤ N → Nat.card ↥X = 3 →
      ∀ p ∈ e214P V (ch82I V h) h,
        (∀ y ∈ X, y * p * y⁻¹ * p⁻¹ ∈ V ⊓ B6.conjSub h V) → p ∈ V ⊓ B6.conjSub h V)
    {x : G} (hxN : x ∈ N) (hx3 : orderOf x = 3) {a : G} (ha : a ∈ ch82A V h)
    (hc : a⁻¹ * (x * a * x⁻¹) ∈ Subgroup.centralizer (V : Set G)) :
    a ∈ Subgroup.centralizer (V : Set G) := by
  set B := kerIn N (ch82I V h) ⊓ V with hBdef
  set P := B ⊔ B6.conjSub h B with hPdef
  have hxI : x ∈ ch82I V h := hP.le_X hxN
  have hAeq : B6.conjSub h B = ch82A V h := hP.conjSub_kerIn_inf_eq
  have haP : a ∈ P := Subgroup.mem_sup_right (hAeq ▸ ha)
  have hxaP : x * a * x⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hP.le_normalizer_P hxI) a).mp haP
  have hcP : a⁻¹ * (x * a * x⁻¹) ∈ P := P.mul_mem (P.inv_mem haP) hxaP
  have hcB : a⁻¹ * (x * a * x⁻¹) ∈ B := by
    refine hP.mem_B_of_commutator_mem_Z hcP fun v hv => ?_
    have h1 : v * (a⁻¹ * (x * a * x⁻¹)) = (a⁻¹ * (x * a * x⁻¹)) * v :=
      Subgroup.mem_centralizer_iff.mp hc v hv
    rw [h1, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hBp : IsPGroup 2 ↥B :=
    (B2F.isPGroup_of_isElemAbelian hP.elem).to_le inf_le_right
  have hxB : x ∈ Subgroup.normalizer (B : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer_kerIn N (ch82I V h) hxI, hNV hxN⟩
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  obtain ⟨b, hb, hfix⟩ := exists_fixed_mul_82 hBp hx3' hxB hcB
  have habP : a * b ∈ P := P.mul_mem haP (Subgroup.mem_sup_left hb)
  have hPeq : P = e214P V (ch82I V h) h := by
    rw [hPdef, hAeq, hBdef, hP.kerIn_inf_eq, sup_comm]
    rfl
  have hcomm : Commute x (a * b) := by
    show x * (a * b) = (a * b) * x
    calc x * (a * b) = (x * (a * b) * x⁻¹) * x := by group
      _ = (a * b) * x := by rw [hfix]
  have hZ := h3 (Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hxN)
    (by rw [Nat.card_zpowers, hx3]) (a * b) (hPeq ▸ habP) fun y hy => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h1 : x ^ n * (a * b) = (a * b) * x ^ n := (hcomm.zpow_left n).eq
      rw [h1, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
  have haV : a ∈ V := by
    have h1 : a = (a * b) * b⁻¹ := by group
    rw [h1]
    exact V.mul_mem hZ.1 (V.inv_mem hb.2)
  exact Subgroup.mem_centralizer_iff.mpr fun v hv => hP.comm hv haV

theorem fix_autI_eq_one_82 {T N V : Subgroup G} {h : G} (hV : IsElemAbelian 2 V)
    (hP : E2.Pair (ch82I V h) T N V h) (hNV : N ≤ Subgroup.normalizer (V : Set G))
    (h3 : ∀ X : Subgroup G, X ≤ N → Nat.card ↥X = 3 →
      ∀ p ∈ e214P V (ch82I V h) h,
        (∀ y ∈ X, y * p * y⁻¹ * p⁻¹ ∈ V ⊓ B6.conjSub h V) → p ∈ V ⊓ B6.conjSub h V)
    {x : G} (hxN : x ∈ N) (hx3 : orderOf x = 3) :
    ∀ φ ∈ autI hV (ch82A V h), convI hV ⟨x, hNV hxN⟩ * φ * (convI hV ⟨x, hNV hxN⟩)⁻¹ = φ →
      φ = 1 := by
  intro φ hφ hfix
  obtain ⟨g, hgA, rfl⟩ := (mem_autI hV).mp hφ
  set y : Subgroup.normalizer (V : Set G) := ⟨x, hNV hxN⟩ with hy
  have h1 : convI hV (g⁻¹ * (y * g * y⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hfix, inv_mul_cancel]
  have h2 := (convI_eq_one_iff hV _).mp h1
  have h3' : (g : G)⁻¹ * (x * g * x⁻¹) ∈ Subgroup.centralizer (V : Set G) := h2
  have h4 := mem_centralizer_of_conj_82 hP hNV h3 hxN hx3 hgA h3'
  exact (convI_eq_one_iff hV g).mpr h4

theorem commutator_autI_eq_82 {T N V : Subgroup G} {h : G} (hV : IsElemAbelian 2 V)
    (hP : E2.Pair (ch82I V h) T N V h) (hNV : N ≤ Subgroup.normalizer (V : Set G))
    (h3 : ∀ X : Subgroup G, X ≤ N → Nat.card ↥X = 3 →
      ∀ p ∈ e214P V (ch82I V h) h,
        (∀ y ∈ X, y * p * y⁻¹ * p⁻¹ ∈ V ⊓ B6.conjSub h V) → p ∈ V ⊓ B6.conjSub h V)
    {x : G} (hxN : x ∈ N) (hx3 : orderOf x = 3)
    (hxA : convI hV ⟨x, hNV hxN⟩ ∈
      Subgroup.normalizer (autI hV (ch82A V h) : Set (MulAut (IntMod V hV)))) :
    ⁅autI hV (ch82A V h), Subgroup.zpowers (convI hV ⟨x, hNV hxN⟩)⁆ = autI hV (ch82A V h) := by
  have : Finite (MulAut (IntMod V hV)) := MulEquiv.finite_left
  exact commutator_zpowers_eq_82 hxA (fix_autI_eq_one_82 hV hP hNV h3 hxN hx3)

end L825G

end CFSG.Quasithin.H13
