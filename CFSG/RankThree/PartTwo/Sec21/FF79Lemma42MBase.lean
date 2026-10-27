module

import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

theorem m42_mem_cen {x g : G} (h : x * g = g * x) : g ∈ Cen x :=
  Subgroup.mem_centralizer_singleton_iff.mpr h.symm

theorem m42_cen_comm {x g : G} (hg : g ∈ Cen x) : x * g = g * x :=
  (Subgroup.mem_centralizer_singleton_iff.mp hg).symm

theorem m42_mem_cenS {S : Subgroup G} {g : G} (h : ∀ s ∈ S, s * g = g * s) : g ∈ CenS S :=
  Subgroup.mem_centralizer_iff.mpr h

theorem m42_cenS_comm {S : Subgroup G} {g : G} (hg : g ∈ CenS S) {s : G} (hs : s ∈ S) :
    s * g = g * s :=
  Subgroup.mem_centralizer_iff.mp hg s hs

theorem m42_cenS_zpowers (x : G) : CenS (Subgroup.zpowers x) = Cen x := by
  ext g
  constructor
  · intro hg
    exact m42_mem_cen (m42_cenS_comm hg (Subgroup.mem_zpowers x))
  · intro hg
    refine m42_mem_cenS fun s hs => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact ((show Commute x g from m42_cen_comm hg).zpow_left i).eq

theorem m42_cenS_closure_pair (x y : G) :
    CenS (Subgroup.closure ({x, y} : Set G)) = Cen x ⊓ Cen y := by
  ext g
  constructor
  · intro hg
    exact ⟨m42_mem_cen (m42_cenS_comm hg (Subgroup.subset_closure (by simp))),
      m42_mem_cen (m42_cenS_comm hg (Subgroup.subset_closure (by simp)))⟩
  · rintro ⟨h1, h2⟩
    refine m42_mem_cenS fun s hs => ?_
    have : Subgroup.closure ({x, y} : Set G) ≤ Cen g := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact m42_mem_cen (m42_cen_comm h1).symm
      · exact m42_mem_cen (m42_cen_comm h2).symm
    exact (m42_cen_comm (this hs)).symm

theorem m42_Opp_le (p : ℕ) (H : Subgroup G) : Opp p H ≤ H := Subgroup.map_subtype_le _

theorem m42_Opp_conj_mem {p : ℕ} {H : Subgroup G} {g z : G} (hg : g ∈ H) (hz : z ∈ Opp p H) :
    g * z * g⁻¹ ∈ Opp p H := by
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * z' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  exact (CFSG.pPrimeCore_normal (p := p) (G := H)).conj_mem z' hz' ⟨g, hg⟩

variable [Finite G]

theorem m42_Opp_coprime (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    Nat.Coprime p (Nat.card (Opp p H)) := by
  have h := CFSG.pPrimeCore_coprime_card (p := p) (G := ↥H)
  rwa [← Subgroup.card_map_of_injective H.subtype_injective] at h

theorem m42_Opp_orderOf (p : ℕ) [Fact p.Prime] {H : Subgroup G} {x : G} (hx : x ∈ Opp p H) :
    Nat.Coprime p (orderOf x) :=
  (m42_Opp_coprime p H).coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hx)

theorem m42_le_Opp {p : ℕ} {H N : Subgroup G} (hNH : N ≤ H)
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hc : Nat.Coprime p (Nat.card N)) :
    N ≤ Opp p H := by
  let N' : Subgroup ↥H := N.subgroupOf H
  haveI : N'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hN g.1 g.2 n hn⟩
  have hcard : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  have hle : N' ≤ CFSG.pPrimeCore p ↥H := le_sSup ⟨inferInstance, hcard ▸ hc⟩
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hNH hx⟩, hle hx, rfl⟩

theorem m42_Opp_normalizes (p : ℕ) (H : Subgroup G) : H ≤ Nor (Opp p H) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => m42_Opp_conj_mem hg hz, fun hz => ?_⟩
  have := m42_Opp_conj_mem (H.inv_mem hg) hz
  have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
  rwa [e] at this

theorem m42_Lay_le (H : Subgroup G) : Lay H ≤ H := Subgroup.map_subtype_le _

theorem m42_Lay_conj_mem {H : Subgroup G} {g z : G} (hg : g ∈ H) (hz : z ∈ Lay H) :
    g * z * g⁻¹ ∈ Lay H := by
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * z' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  haveI : (CFSG.layer ↥H).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI : (CFSG.layer ↥H).Normal := inferInstance
  exact this.conj_mem z' hz' ⟨g, hg⟩

theorem m42_Lay_map (φ : G ≃* G) (M : Subgroup G) :
    (Lay M).map φ.toMonoidHom = Lay (M.map φ.toMonoidHom) := by
  let e : ↥M ≃* ↥(M.map φ.toMonoidHom) := M.equivMapOfInjective φ.toMonoidHom φ.injective
  have h1 := CFSG.WholeGroup.layer_map_mulEquiv e
  have hcomp : (M.map φ.toMonoidHom).subtype.comp e.toMonoidHom =
      φ.toMonoidHom.comp M.subtype := by
    ext x; rfl
  calc (Lay M).map φ.toMonoidHom
      = (CFSG.layer ↥M).map (φ.toMonoidHom.comp M.subtype) := by
        change ((CFSG.layer ↥M).map M.subtype).map φ.toMonoidHom = _
        rw [Subgroup.map_map]
    _ = (CFSG.layer ↥M).map ((M.map φ.toMonoidHom).subtype.comp e.toMonoidHom) := by
        rw [hcomp]
    _ = ((CFSG.layer ↥M).map e.toMonoidHom).map (M.map φ.toMonoidHom).subtype := by
        rw [Subgroup.map_map]
    _ = Lay (M.map φ.toMonoidHom) := by rw [h1]; rfl

theorem m42_Lay_conj_mem_of_normalizes {M : Subgroup G} {g z : G}
    (hg : ∀ m, m ∈ M ↔ g * m * g⁻¹ ∈ M) (hz : z ∈ Lay M) : g * z * g⁻¹ ∈ Lay M := by
  have hM : M.map (MulAut.conj g).toMonoidHom = M := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact (hg m).mp hm
    · intro hy
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      refine ⟨g⁻¹ * y * g, (hg _).mpr (by rw [e]; exact hy), by simpa using e⟩
  have := m42_Lay_map (MulAut.conj g) M
  rw [hM] at this
  rw [← this]
  exact ⟨z, hz, by simp⟩

theorem m42_simple_inf {S N : Subgroup G} [IsSimpleGroup S]
    (hS : ∀ s ∈ S, ∀ n ∈ N ⊓ S, s * n * s⁻¹ ∈ N ⊓ S) : N ⊓ S = ⊥ ∨ S ≤ N := by
  let T : Subgroup ↥S := (N ⊓ S).subgroupOf S
  haveI : T.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hS g.1 g.2 n hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with h | h
  · left
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxS : x ∈ S := hx.2
    have : (⟨x, hxS⟩ : ↥S) ∈ T := hx
    rw [h, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  · right
    intro x hx
    have : (⟨x, hx⟩ : ↥S) ∈ T := by rw [h]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1

theorem m42_comm_of_normal {S N Y : Subgroup G} [IsSimpleGroup S] (hSY : S ≤ Y) (hNY : N ≤ Y)
    (hSn : ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hNn : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N)
    (hSN : ¬ S ≤ N) : ∀ s ∈ S, ∀ n ∈ N, s * n = n * s := by
  have hbot : N ⊓ S = ⊥ := by
    refine (m42_simple_inf (S := S) (N := N) fun s hs n hn => ?_).resolve_right hSN
    exact ⟨hNn s (hSY hs) n hn.1, hSn s (hSY hs) n hn.2⟩
  intro s hs n hn
  have h1 : s * n * s⁻¹ * n⁻¹ ∈ N :=
    N.mul_mem (hNn s (hSY hs) n hn) (N.inv_mem hn)
  have h2 : s * n * s⁻¹ * n⁻¹ ∈ S := by
    have : s * (n * s⁻¹ * n⁻¹) = s * n * s⁻¹ * n⁻¹ := by group
    rw [← this]
    exact S.mul_mem hs (by
      have := hSn n (hNY hn) s⁻¹ (S.inv_mem hs)
      simpa [mul_assoc] using this)
  have : s * n * s⁻¹ * n⁻¹ ∈ N ⊓ S := ⟨h1, h2⟩
  rw [hbot, Subgroup.mem_bot] at this
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
  exact this


theorem m42_Opp_map (p : ℕ) (φ : G ≃* G) (M : Subgroup G) :
    (Opp p M).map φ.toMonoidHom = Opp p (M.map φ.toMonoidHom) := by
  let e : ↥M ≃* ↥(M.map φ.toMonoidHom) := M.equivMapOfInjective φ.toMonoidHom φ.injective
  have h1 := CFSG.pPrimeCore_map_iso p e
  have hcomp : (M.map φ.toMonoidHom).subtype.comp e.toMonoidHom =
      φ.toMonoidHom.comp M.subtype := by
    ext x; rfl
  calc (Opp p M).map φ.toMonoidHom
      = (CFSG.pPrimeCore p ↥M).map (φ.toMonoidHom.comp M.subtype) := by
        change ((CFSG.pPrimeCore p ↥M).map M.subtype).map φ.toMonoidHom = _
        rw [Subgroup.map_map]
    _ = (CFSG.pPrimeCore p ↥M).map ((M.map φ.toMonoidHom).subtype.comp e.toMonoidHom) := by
        rw [hcomp]
    _ = ((CFSG.pPrimeCore p ↥M).map e.toMonoidHom).map (M.map φ.toMonoidHom).subtype := by
        rw [Subgroup.map_map]
    _ = Opp p (M.map φ.toMonoidHom) := by rw [h1]; rfl

theorem m42_Opp_conj_mem_of_normalizes {p : ℕ} {M : Subgroup G} {g z : G}
    (hg : ∀ m, m ∈ M ↔ g * m * g⁻¹ ∈ M) (hz : z ∈ Opp p M) : g * z * g⁻¹ ∈ Opp p M := by
  have hM : M.map (MulAut.conj g).toMonoidHom = M := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact (hg m).mp hm
    · intro hy
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      refine ⟨g⁻¹ * y * g, (hg _).mpr (by rw [e]; exact hy), by simpa using e⟩
  have := m42_Opp_map p (MulAut.conj g) M
  rw [hM] at this
  rw [← this]
  exact ⟨z, hz, by simp⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
