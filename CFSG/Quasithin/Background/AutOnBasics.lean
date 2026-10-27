module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

namespace AutOn

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem coe_conjAct_apply (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (v : V) :
    ((conjAct V g v : V) : G) = g * v * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v

theorem mem_autOn_iff {X V : Subgroup G} {φ : MulAut V} :
    φ ∈ autOn X V ↔ ∃ n : Subgroup.normalizer (V : Set G), (n : G) ∈ X ∧ conjAct V n = φ := by
  unfold autOn
  rw [Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf]

theorem mem_autOn_iff_exists {X V : Subgroup G} {a : MulAut V} :
    a ∈ autOn X V ↔ ∃ (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)), x ∈ X ∧
      conjAct V ⟨x, hx⟩ = a := by
  rw [mem_autOn_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.1, n.2, hn, rfl⟩
  · rintro ⟨x, hx, hxX, rfl⟩
    exact ⟨⟨x, hx⟩, hxX, rfl⟩

theorem conjAct_mem_autOn {X V : Subgroup G} (n : Subgroup.normalizer (V : Set G))
    (hn : (n : G) ∈ X) : conjAct V n ∈ autOn X V :=
  mem_autOn_iff.2 ⟨n, hn, rfl⟩

theorem conjAct_mem_autOn_of_mem {X V : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hxX : x ∈ X) : conjAct V ⟨x, hx⟩ ∈ autOn X V :=
  conjAct_mem_autOn ⟨x, hx⟩ hxX

theorem autOn_mono {X Y V : Subgroup G} (h : X ≤ Y) : autOn X V ≤ autOn Y V := by
  intro φ hφ
  obtain ⟨n, hn, rfl⟩ := mem_autOn_iff.1 hφ
  exact conjAct_mem_autOn n (h hn)

theorem isPGroup_autOn {p : ℕ} {A U : Subgroup G} (hA : IsPGroup p A) :
    IsPGroup p (autOn A U) := by
  have h1 : IsPGroup p (A.subgroupOf (Subgroup.normalizer (U : Set G))) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hA ⟨(x : G), hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  exact h1.map _

theorem card_autOn_dvd [Finite G] (L U : Subgroup G) : Nat.card (autOn L U) ∣ Nat.card L := by
  refine (Subgroup.card_map_dvd _ _).trans ?_
  rw [← Subgroup.card_map_of_injective (Subgroup.normalizer (U : Set G)).subtype_injective,
    Subgroup.subgroupOf_map_subtype]
  exact Subgroup.card_dvd_of_le inf_le_left

theorem autOn_eq_bot_of_le_centralizer {X V : Subgroup G}
    (h : X ≤ Subgroup.centralizer (V : Set G)) : autOn X V = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨n, hn, rfl⟩ := mem_autOn_iff.1 ha
  rw [Subgroup.mem_bot]
  ext v
  have hc := Subgroup.mem_centralizer_iff.1 (h hn) (v : G) v.2
  show ((conjAct V n v : V) : G) = (v : G)
  rw [coe_conjAct_apply, ← hc, mul_inv_cancel_right]

theorem conjAct_mem_normalizer_autOn {Y V : Subgroup G} (g : Subgroup.normalizer (V : Set G))
    (hg : (g : G) ∈ Subgroup.normalizer (Y : Set G)) :
    conjAct V g ∈ Subgroup.normalizer (autOn Y V : Set (MulAut V)) := by
  have hmem : g ∈ Subgroup.normalizer
      ((Y.subgroupOf (Subgroup.normalizer (V : Set G)) : Subgroup _) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.mp hg (x : G)
  exact Subgroup.le_normalizer_map (conjAct V) ⟨g, hmem, rfl⟩

theorem autOn_le_normalizer_autOn {X Y V : Subgroup G}
    (h : X ≤ Subgroup.normalizer (Y : Set G)) :
    autOn X V ≤ Subgroup.normalizer (autOn Y V : Set (MulAut V)) := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
  exact conjAct_mem_normalizer_autOn g (h (Subgroup.mem_subgroupOf.mp hg))

theorem autOn_sup_eq {X Y V : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) : autOn (X ⊔ Y) V = autOn X V ⊔ autOn Y V := by
  unfold autOn
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem conjAct_eq_one_iff {V : Subgroup G} (n : Subgroup.normalizer (V : Set G)) :
    conjAct V n = 1 ↔ (n : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) h
    simp only [coe_conjAct_apply, MulAut.one_apply] at this
    calc v * (n : G) = ((n : G) * v * (n : G)⁻¹) * n := by rw [this]
      _ = n * v := by group
  · intro h
    ext v
    have hc := h (v : G) v.2
    show ((conjAct V n v : V) : G) = (v : G)
    rw [coe_conjAct_apply, ← hc, mul_inv_cancel_right]

theorem autOn_ne_bot_of_not_le_centralizer {A V : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V : Set G)) (h : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    autOn A V ≠ ⊥ := by
  intro hbot
  apply h
  intro a ha
  have hmem := conjAct_mem_autOn_of_mem (hA ha) ha
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (conjAct_eq_one_iff ⟨a, hA ha⟩).1 hmem

theorem mem_of_conjAct_mem_autOn {K X V : Subgroup G} (hKN : K ≤ Subgroup.normalizer (V : Set G))
    (hXK : X ≤ K) (hCX : K ⊓ Subgroup.centralizer (V : Set G) ≤ X) {x : G} (hx : x ∈ K)
    (h : conjAct V ⟨x, hKN hx⟩ ∈ autOn X V) : x ∈ X := by
  obtain ⟨y, hyX, hye⟩ := mem_autOn_iff.1 h
  have h2 : conjAct V (y⁻¹ * ⟨x, hKN hx⟩) = 1 := by
    rw [map_mul, map_inv, hye, inv_mul_cancel]
  have h3 : (y : G)⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
    simpa using (conjAct_eq_one_iff _).1 h2
  have h4 : (y : G)⁻¹ * x ∈ X := hCX ⟨K.mul_mem (K.inv_mem (hXK hyX)) hx, h3⟩
  have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [e]
  exact X.mul_mem hyX h4

theorem autOn_map_conj {V X : Subgroup G} {u : G} (hu : u ∈ Subgroup.normalizer (V : Set G)) :
    autOn (X.map (MulAut.conj u).toMonoidHom) V =
      (autOn X V).map (MulAut.conj (conjAct V ⟨u, hu⟩)).toMonoidHom := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := mem_autOn_iff.mp hφ
    obtain ⟨x, hx, hxg⟩ := hg
    set n : Subgroup.normalizer (V : Set G) := ⟨u, hu⟩⁻¹ * g * ⟨u, hu⟩ with hn
    have hnx : (n : G) = x := by
      rw [hn]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hxg]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    refine ⟨conjAct V n, mem_autOn_iff.mpr ⟨n, hnx ▸ hx, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hn, map_mul, map_mul, map_inv]
    group
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_autOn_iff.mp hψ
    refine mem_autOn_iff.mpr ⟨⟨u, hu⟩ * g * ⟨u, hu⟩⁻¹, ?_, ?_⟩
    · exact ⟨g, hg, by simp [MulAut.conj_apply]⟩
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv]

open scoped IsMulCommutative in
theorem fixV_autOn_eq {L V : Subgroup G} [IsMulCommutative V]
    (hL : L ≤ Subgroup.normalizer (V : Set G)) :
    fixV (autOn L V) = (Subgroup.centralizer (L : Set G)).subgroupOf V := by
  ext v
  rw [mem_fixV, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h l hl
    have := congrArg Subtype.val (h _ (conjAct_mem_autOn_of_mem (hL hl) hl))
    rw [coe_conjAct_apply] at this
    calc l * (v : G) = l * v * l⁻¹ * l := by group
      _ = v * l := by rw [this]
  · intro h a ha
    obtain ⟨n, hn, rfl⟩ := mem_autOn_iff.1 ha
    apply Subtype.ext
    rw [coe_conjAct_apply, h n hn]
    group

open scoped IsMulCommutative in
theorem map_commV_autOn_eq {X V : Subgroup G} [IsMulCommutative V]
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) : (commV (autOn X V)).map V.subtype = ⁅V, X⁆ := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, commV, Subgroup.closure_le]
    rintro _ ⟨σ, hσ, v, rfl⟩
    obtain ⟨g, hgX, rfl⟩ := mem_autOn_iff.1 hσ
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show ((conjAct V g v * v⁻¹ : V) : G) ∈ ⁅V, X⁆
    rw [Subgroup.coe_mul, coe_conjAct_apply, Subgroup.coe_inv]
    have e : (g : G) * v * (g : G)⁻¹ * (v : G)⁻¹ = ⁅(v : G), (g : G)⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (⁅V, X⁆).inv_mem (Subgroup.commutator_mem_commutator v.2 hgX)
  · rw [Subgroup.commutator_le]
    intro w hw k hk
    have hmem : conjAct V ⟨k, hXV hk⟩ ⟨w, hw⟩ * (⟨w, hw⟩ : V)⁻¹ ∈ commV (autOn X V) :=
      Subgroup.subset_closure ⟨_, conjAct_mem_autOn ⟨k, hXV hk⟩ hk, ⟨w, hw⟩, rfl⟩
    refine ⟨(conjAct V ⟨k, hXV hk⟩ ⟨w, hw⟩ * (⟨w, hw⟩ : V)⁻¹)⁻¹,
      (commV (autOn X V)).inv_mem hmem, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, coe_conjAct_apply]
    rw [commutatorElement_def]
    group

open scoped IsMulCommutative in
theorem commV_autOn_eq {V X : Subgroup G} [IsMulCommutative V]
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) :
    commV (autOn X V) = (⁅V, X⁆).subgroupOf V := by
  rw [← map_commV_autOn_eq hXV]
  exact (Subgroup.comap_map_eq_self_of_injective V.subtype_injective _).symm

open scoped IsMulCommutative in
theorem commV_autOn_eq_top {L U : Subgroup G} [IsMulCommutative U]
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hcomm : ⁅U, L⁆ = U) : commV (autOn L U) = ⊤ := by
  rw [commV_autOn_eq hLU, hcomm, Subgroup.subgroupOf_self]

end AutOn

end CFSG.Quasithin
