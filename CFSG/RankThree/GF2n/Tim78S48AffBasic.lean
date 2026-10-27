module

public import CFSG.RankThree.GF2n.Tim78S48PairBasic

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def affC (B P : Subgroup G) (g : G) (hPB : P ≤ Subgroup.normalizer (B : Set G)) :
    Subgroup G where
  carrier := {c | c ∈ P ∧ ∀ y ∈ conjSubgroup g B, ⁅c, y⁆ ∈ B}
  one_mem' := ⟨P.one_mem, fun y _ => by simpa using B.one_mem⟩
  mul_mem' := by
    rintro a b ⟨haP, ha⟩ ⟨hbP, hb⟩
    refine ⟨P.mul_mem haP hbP, fun y hy => ?_⟩
    have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPB haP) _).mp (hb y hy)) (ha y hy)
  inv_mem' := by
    rintro a ⟨haP, ha⟩
    refine ⟨P.inv_mem haP, fun y hy => ?_⟩
    have e : ⁅a⁻¹, y⁆ = a⁻¹ * (⁅a, y⁆)⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hPB (P.inv_mem haP)) _).mp (B.inv_mem (ha y hy))

namespace Aff

theorem mem_conj_iff {g x : G} {S : Subgroup G} :
    x ∈ conjSubgroup g S ↔ ∃ s ∈ S, x = g * s * g⁻¹ := by
  constructor
  · intro h
    exact ⟨g⁻¹ * x * g, mem_conjSubgroup.mp h, by group⟩
  · rintro ⟨s, hs, rfl⟩
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hs

theorem conj_le_of_mem {X S : Subgroup G} {h : G} (hh : h ∈ X) (hS : S ≤ X) :
    conjSubgroup h S ≤ X := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := mem_conj_iff.mp hx
  exact X.mul_mem (X.mul_mem hh (hS hs)) (X.inv_mem hh)

theorem comm_mul_self_eq (p y : G) : ⁅p, y⁆ * y = p * y * p⁻¹ := by
  simp only [commutatorElement_def]; group

theorem conj_sup (r : G) (A A' : Subgroup G) :
    conjSubgroup r (A ⊔ A') = conjSubgroup r A ⊔ conjSubgroup r A' := Subgroup.map_sup _ _ _

theorem mem_normalizer_of_conj_le [Finite G] {c : G} {S : Subgroup G}
    (h : conjSubgroup c S ≤ S) : c ∈ Subgroup.normalizer (S : Set G) :=
  Subgroup.mem_normalizer_fintype fun n hn => h (mem_conj_iff.mpr ⟨n, hn, rfl⟩)

theorem conj_le_of_mem_normalizer {L A : Subgroup G} {r : G}
    (hr : r ∈ Subgroup.normalizer (L : Set G)) (hA : A ≤ L) : conjSubgroup r A ≤ L := by
  have := Subgroup.map_mono (f := (MulAut.conj r).toMonoidHom) hA
  rwa [show Subgroup.map (MulAut.conj r).toMonoidHom L = conjSubgroup r L from rfl,
    conjSubgroup_eq_self_iff.mpr hr] at this

end Aff

open Aff

namespace Phase1

variable {B T : Subgroup G} {g : G}

theorem part_W (h : Phase1 B T g) : ∀ w ∈ B ⊔ conjSubgroup g B, w ≠ 1 →
    ∃! U, U ∈ classIn B (B ⊔ conjSubgroup g B) ∧ w ∈ U := by
  obtain ⟨n, hn, hnat, hpart, -⟩ := h
  exact hpart

theorem trans_X (h : Phase1 B T g) : ∀ U ∈ classIn B (B ⊔ conjSubgroup g B),
    ∃ x ∈ T ⊔ conjSubgroup g T, U = conjSubgroup x B := by
  obtain ⟨n, hn, hnat, hpart, htrans, -⟩ := h
  exact htrans

theorem comm_X_K (h : Phase1 B T g) :
    ∀ x ∈ T ⊔ conjSubgroup g T, ∀ k ∈ kernel48 B T g, ⁅x, k⁆ ∈ B ⊔ conjSubgroup g B := by
  obtain ⟨n, hn, hnat, hpart, htrans, hKel, hKform, hWA, hA, hcomm, -⟩ := h
  exact hcomm

theorem relIndex_T (h : Phase1 B T g) :
    (T ⊓ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)).relIndex T =
      Nat.card B := by
  obtain ⟨n, hn, hnat, hpart, htrans, hKel, hKform, hWA, hA, hcomm, hrel, -⟩ := h
  exact hrel

end Phase1

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

omit [Finite G] in
theorem P_le_normalizer_B : P ≤ Subgroup.normalizer (B : Set G) :=
  H.P_le_M.trans H.M_le_normalizer_B

@[expose] def aC (g : G) : Subgroup G := affC B P g H.P_le_normalizer_B

omit [Finite G] in
theorem mem_aC {c : G} : c ∈ H.aC g ↔ c ∈ P ∧ ∀ y ∈ conjSubgroup g B, ⁅c, y⁆ ∈ B := Iff.rfl

omit [Finite G] in
theorem aC_le_P : H.aC g ≤ P := fun _ hc => hc.1

omit [Finite G] in
theorem aC_le_M : H.aC g ≤ M := H.aC_le_P.trans H.P_le_M

omit [Finite G] in
theorem aC_le_Q : H.aC g ≤ Q := H.aC_le_P.trans H.P_le_Q

theorem B_le_aC (h48 : Hyp48 M B T g) : B ≤ H.aC g := fun b hb =>
  ⟨H.B_le_P hb, fun y hy => by
    have := H.commute_of_conj_le_M h48.leM b hb y hy
    rw [commutatorElement_eq_one_iff_mul_comm.mpr this]
    exact B.one_mem⟩

theorem P_inf_Bg (hBgQ : conjSubgroup g B ⊓ Q = ⊥) : P ⊓ conjSubgroup g B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ conjSubgroup g B ⊓ Q := ⟨hx.2, H.P_le_Q hx.1⟩
  rwa [hBgQ] at this

theorem P_inf_W (h48 : Hyp48 M B T g) (hBgQ : conjSubgroup g B ⊓ Q = ⊥) :
    P ⊓ (B ⊔ conjSubgroup g B) = B := by
  refine le_antisymm (fun x hx => ?_) (le_inf H.B_le_P le_sup_left)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun x hx y hy => (H.commute_of_conj_le_M h48.leM y hy x hx).symm) hx.2
  have hbP : b ∈ P := by
    have := P.mul_mem (P.inv_mem (H.B_le_P ha)) hx.1
    rwa [inv_mul_cancel_left] at this
  have : b ∈ P ⊓ conjSubgroup g B := ⟨hbP, hb⟩
  rw [H.P_inf_Bg hBgQ, Subgroup.mem_bot] at this
  rw [this, mul_one]
  exact ha

theorem mem_aC_of_comm_mem (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hBgQ : conjSubgroup g B ⊓ Q = ⊥)
    (hpart : ∀ w ∈ B ⊔ conjSubgroup g B, w ≠ 1 →
      ∃! U, U ∈ classIn B (B ⊔ conjSubgroup g B) ∧ w ∈ U)
    {p y : G} (hp : p ∈ P) (hy : y ∈ conjSubgroup g B) (hy1 : y ≠ 1) (h : ⁅p, y⁆ ∈ B) :
    p ∈ H.aC g := by
  have hzW : ⁅p, y⁆ * y ∈ B ⊔ conjSubgroup g B :=
    (B ⊔ conjSubgroup g B).mul_mem (Subgroup.mem_sup_left h) (Subgroup.mem_sup_right hy)
  have hz1 : ⁅p, y⁆ * y ≠ 1 := by
    intro h1
    apply hy1
    have hyB : y ∈ B := by
      have : y = (⁅p, y⁆)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact B.inv_mem h
    have : y ∈ B ⊓ conjSubgroup g B := ⟨hyB, hy⟩
    rw [H.B_inf_Bg hP] at this
    exact Subgroup.mem_bot.mp this
  obtain ⟨U, ⟨⟨⟨r, rfl⟩, hUle⟩, hzU⟩, -⟩ := hpart _ hzW hz1
  have hpy : p * y * p⁻¹ ∈ conjSubgroup (p * g) B := by
    rw [conjSubgroup_mul]
    exact mem_conj_iff.mpr ⟨y, hy, rfl⟩
  have hU : conjSubgroup r B = conjSubgroup (p * g) B := by
    refine H.conj_B_eq_of_inf_ne_bot fun hbot => ?_
    have : ⁅p, y⁆ * y ∈ conjSubgroup r B ⊓ conjSubgroup (p * g) B :=
      ⟨hzU, by rw [comm_mul_self_eq]; exact hpy⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hz1 this
  refine ⟨hp, fun y' hy' => ?_⟩
  have h1 : p * y' * p⁻¹ ∈ B ⊔ conjSubgroup g B := by
    apply hUle
    rw [hU, conjSubgroup_mul]
    exact mem_conj_iff.mpr ⟨y', hy', rfl⟩
  have h2 : ⁅p, y'⁆ ∈ B ⊔ conjSubgroup g B := by
    have : ⁅p, y'⁆ = (p * y' * p⁻¹) * y'⁻¹ := by simp only [commutatorElement_def]
    rw [this]
    exact (B ⊔ conjSubgroup g B).mul_mem h1
      ((B ⊔ conjSubgroup g B).inv_mem (Subgroup.mem_sup_right hy'))
  have h3 : ⁅p, y'⁆ ∈ P := by
    have hy'N : y' ∈ Subgroup.normalizer (P : Set G) := H.M_le_normalizer_P (h48.leM hy')
    have : ⁅p, y'⁆ = p * (y' * p⁻¹ * y'⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact P.mul_mem hp ((Subgroup.mem_normalizer_iff.mp hy'N p⁻¹).mp (P.inv_mem hp))
  have : ⁅p, y'⁆ ∈ P ⊓ (B ⊔ conjSubgroup g B) := ⟨h3, h2⟩
  rwa [H.P_inf_W h48 hBgQ] at this

theorem aC_le_normalizer_W (h48 : Hyp48 M B T g) :
    H.aC g ≤ Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
  intro c hc
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  obtain ⟨b, hb, y, hy, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun x hx y hy => (H.commute_of_conj_le_M h48.leM y hy x hx).symm) hw
  have hbc : c * b * c⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp (H.P_le_normalizer_B hc.1) b).mp hb
  have e : c * (b * y) * c⁻¹ = (c * b * c⁻¹) * (⁅c, y⁆ * y) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (B ⊔ conjSubgroup g B).mul_mem (Subgroup.mem_sup_left hbc)
    ((B ⊔ conjSubgroup g B).mul_mem (Subgroup.mem_sup_left (hc.2 y hy))
      (Subgroup.mem_sup_right hy))

theorem aC_le_normalizer_X (h48 : Hyp48 M B T g)
    (htrans : ∀ U ∈ classIn B (B ⊔ conjSubgroup g B),
      ∃ h ∈ T ⊔ conjSubgroup g T, U = conjSubgroup h B) :
    H.aC g ≤ Subgroup.normalizer ((T ⊔ conjSubgroup g T : Subgroup G) : Set G) := by
  intro c hc
  have hcN := H.aC_le_normalizer_W h48 hc
  have hT : conjSubgroup c T = T :=
    conjSubgroup_eq_self_iff.mpr (H.M_le_normalizer_T (H.aC_le_M hc))
  have hU : conjSubgroup (c * g) B ∈ classIn B (B ⊔ conjSubgroup g B) := by
    refine ⟨⟨c * g, rfl⟩, ?_⟩
    rw [conjSubgroup_mul]
    have : conjSubgroup c (conjSubgroup g B) ≤ conjSubgroup c (B ⊔ conjSubgroup g B) :=
      Subgroup.map_mono le_sup_right
    rwa [conjSubgroup_eq_self_iff.mpr hcN] at this
  obtain ⟨h, hh, hhB⟩ := htrans _ hU
  have hTg : conjSubgroup (c * g) T = conjSubgroup h T := H.conj_T_eq_of_conj_B_eq hhB
  apply mem_normalizer_of_conj_le
  rw [conj_sup, hT, ← conjSubgroup_mul, hTg]
  exact sup_le le_sup_left (conj_le_of_mem hh le_sup_left)

end Hyp4

end CFSG.RankThree.GF2n.Tim78
