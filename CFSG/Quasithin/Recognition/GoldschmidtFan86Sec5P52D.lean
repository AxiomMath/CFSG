module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P52S
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PConj

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem relIndex_inter_le {δ ε : V} (hεδ : Γ.Adj ε δ) (x : G) :
    (nbrStab Γ G ε ⊓ (nbrStab Γ G δ ⊓ Subgroup.centralizer ({x} : Set G))).relIndex
        (nbrStab Γ G ε) ≤
      (Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G δ) *
        (nbrStab Γ G δ).relIndex (MulAction.stabilizer G ε ⊓ MulAction.stabilizer G δ) := by
  set Ke := nbrStab Γ G ε with hKe
  set Kd := nbrStab Γ G δ with hKd
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hfinE : Finite Ke := F.finite_nbrStab ε
  have hfinD : Finite Kd := F.finite_nbrStab δ
  have hUle : Ke ⊓ (Kd ⊓ C) ≤ Ke ⊓ Kd := inf_le_inf_left _ inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hUle (inf_le_left : Ke ⊓ Kd ≤ Ke)
  rw [← hmul]
  have h1 : (Ke ⊓ (Kd ⊓ C)).relIndex (Ke ⊓ Kd) = C.relIndex (Ke ⊓ Kd) := by
    have : Ke ⊓ (Kd ⊓ C) = C ⊓ (Ke ⊓ Kd) := by
      ext g
      simp only [Subgroup.mem_inf]
      tauto
    rw [this, Subgroup.inf_relIndex_right]
  have h2 : C.relIndex (Ke ⊓ Kd) ≤ C.relIndex Kd :=
    Subgroup.relIndex_le_of_le_right inf_le_right (relIndex_ne_zero_of_finite _ _)
  have h3 : (Ke ⊓ Kd).relIndex Ke ≤
      Kd.relIndex (MulAction.stabilizer G ε ⊓ MulAction.stabilizer G δ) := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    have := F.finite_stabilizer_inf ε δ
    exact Subgroup.relIndex_le_of_le_right (F.nbrStab_le_edge ε hεδ)
      (relIndex_ne_zero_of_finite _ _)
  rw [h1]
  exact Nat.mul_le_mul h2 h3

theorem fan52_eps {δ ε : V} (hεδ : Γ.Adj ε δ) {x : G} (hx : x ∈ MulAction.stabilizer G δ)
    (hxo : orderOf x = Fan86.valence Γ δ) :
    Nat.card (nbrStab Γ G ε) ≤
      ((Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G δ) *
        (nbrStab Γ G δ).relIndex (MulAction.stabilizer G ε ⊓ MulAction.stabilizer G δ)) ^
          Fan86.valence Γ ε := by
  obtain ⟨y, hy, hyo⟩ := F.exists_orderOf_eq_valence ε
  have hp := F.valence_isPrime ε
  set Ke := nbrStab Γ G ε with hKe
  set U : Subgroup G :=
    Ke ⊓ (nbrStab Γ G δ ⊓ Subgroup.centralizer ({x} : Set G)) with hU
  have hfinE : Finite Ke := F.finite_nbrStab ε
  have hUb := F.relIndex_inter_le hεδ x
  have hfinP : Finite (Subgroup.zpowers y) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hyo]; exact hp.ne_zero)
  have : Fintype (Subgroup.zpowers y) := Fintype.ofFinite _
  let Uj : Subgroup.zpowers y → Subgroup G := fun g => U.comap (MulAut.conj (g : G)⁻¹).toMonoidHom
  have memUj : ∀ g h, h ∈ Uj g ↔ (g : G)⁻¹ * h * g ∈ U := fun g h => by
    simp [Uj]
  set X : Subgroup G := ⨅ g : Subgroup.zpowers y, Uj g with hX
  have memX : ∀ h, h ∈ X ↔ ∀ g ∈ Subgroup.zpowers y, g⁻¹ * h * g ∈ U := by
    intro h
    rw [hX, Subgroup.mem_iInf]
    constructor
    · intro hh g hg
      exact (memUj ⟨g, hg⟩ h).1 (hh ⟨g, hg⟩)
    · intro hh g
      exact (memUj g h).2 (hh g g.2)
  have hXU : ∀ h ∈ X, h ∈ U := by
    intro h hh
    simpa using (memX h).1 hh 1 (one_mem _)
  have hUj : ∀ g, (Uj g).relIndex Ke = U.relIndex Ke := by
    intro g
    have hg : ((g : G)⁻¹) • ε = ε := by
      rw [inv_smul_eq_iff]
      exact (MulAction.mem_stabilizer_iff.1 (by
        have := Subgroup.zpowers_le.2 hy g.2
        exact this)).symm
    show (U.comap (MulAut.conj (g : G)⁻¹).toMonoidHom).relIndex Ke = U.relIndex Ke
    rw [Subgroup.relIndex_comap, F.map_conj_nbrStab hg]
  have hXidx : X.relIndex Ke ≤ U.relIndex Ke ^ Fan86.valence Γ ε := by
    refine (Subgroup.relIndex_iInf_le Uj).trans ?_
    simp only [hUj, Finset.prod_const, Finset.card_univ]
    rw [Fintype.card_eq_nat_card, Nat.card_zpowers, hyo]
  have hxX : ∀ h ∈ X, x * h = h * x := by
    intro h hh
    have := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (hXU h hh)).2).2
    rw [Subgroup.mem_centralizer_iff] at this
    exact this x rfl
  have hxN : x ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : x * h * x⁻¹ = h := by rw [hxX h hh]; group
      rw [this]
      exact hh
    · intro hh
      have hc := hxX _ hh
      have h1 : x * (x * h * x⁻¹) = x * h := by
        calc x * (x * h * x⁻¹) = x * h * x⁻¹ * x := hc
          _ = x * h := by group
      have h2 : x * h * x⁻¹ = h := mul_left_cancel h1
      rw [← h2]
      exact hh
  have hyN : y ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [memX] at hh ⊢
      intro g hg
      have := hh (y⁻¹ * g) (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y)) hg)
      have e : g⁻¹ * (y * h * y⁻¹) * g = (y⁻¹ * g)⁻¹ * h * (y⁻¹ * g) := by group
      rw [e]
      exact this
    · intro hh
      rw [memX] at hh ⊢
      intro g hg
      have := hh (y * g) (Subgroup.mul_mem _ (Subgroup.mem_zpowers y) hg)
      have e : (y * g)⁻¹ * (y * h * y⁻¹) * (y * g) = g⁻¹ * h * g := by group
      rw [e] at this
      exact this
  have hLδ : LocTr Γ (Subgroup.normalizer (X : Set G)) δ := by
    intro p q hp hq
    obtain ⟨i, hi⟩ := F.exists_pow_smul_eq hx hxo hp hq
    exact ⟨x ^ i, (Subgroup.normalizer (X : Set G)).pow_mem hxN i,
      MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer G δ).pow_mem hx i), hi⟩
  have hLε : LocTr Γ (Subgroup.normalizer (X : Set G)) ε := by
    intro p q hp hq
    obtain ⟨i, hi⟩ := F.exists_pow_smul_eq hy hyo hp hq
    exact ⟨y ^ i, (Subgroup.normalizer (X : Set G)).pow_mem hyN i,
      MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer G ε).pow_mem hy i), hi⟩
  have hET := F.edgeTransitive_of_locTr (F.locTr_all hεδ hLε hLδ)
  have hXbot : X = ⊥ := by
    refine F.eq_bot_of_edgeTransitive hεδ (fun h hh => ?_) hET
    have hhK : h ∈ Ke := (Subgroup.mem_inf.1 (hXU h hh)).1
    exact ⟨MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer ε hhK),
      mem_nbrStab.1 hhK δ hεδ⟩
  rw [hXbot, Subgroup.relIndex_bot_left] at hXidx
  exact hXidx.trans (Nat.pow_le_pow_left hUb _)

end FanTree

end CFSG.Quasithin.Fan86
