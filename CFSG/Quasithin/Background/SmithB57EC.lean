module

public import CFSG.Quasithin.Background.SmithB57EB
public import CFSG.Quasithin.Background.P4InspSpBasic

public section

namespace CFSG.Quasithin

namespace SmithB57E

open CFSG.Open CFSG.QuasithinUnique FFC
open scoped commutatorElement

section General

variable {Ω : Type*} [Group Ω]

theorem commutator_le_of_sq_mem {M L : Subgroup Ω} (hn : ∀ y ∈ M, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (h2 : ∀ y ∈ M, y ^ 2 ∈ L) : ⁅M, M⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have e : x * y * x⁻¹ * y⁻¹ = (x * y) ^ 2 * (y⁻¹ * (x ^ 2)⁻¹ * y⁻¹⁻¹) * (y ^ 2)⁻¹ := by
    rw [sq, sq, sq]
    group
  rw [commutatorElement_def, e]
  exact L.mul_mem (L.mul_mem (h2 _ (M.mul_mem hx hy))
    (hn _ (M.inv_mem hy) _ (L.inv_mem (h2 x hx)))) (L.inv_mem (h2 y hy))

theorem eq_map_alternating {n : ℕ} (hn : 5 ≤ n) {M L : Subgroup Ω} (hL : ⁅M, M⁆ = L)
    (π : Equiv.Perm (Fin n) ≃* ↥M) :
    L = (alternatingGroup (Fin n)).map (M.subtype.comp π.toMonoidHom) := by
  have hrange : (M.subtype.comp π.toMonoidHom).range = M := by
    ext x
    constructor
    · rintro ⟨σ, rfl⟩
      exact (π σ).2
    · intro hx
      exact ⟨π.symm ⟨x, hx⟩, by simp⟩
  rw [← hL, ← G11.P4InspSp.p4inspsp_commutator_range hn (M.subtype.comp π.toMonoidHom), hrange]

theorem mem_iff_alternating {n : ℕ} (hn : 5 ≤ n) {M L : Subgroup Ω} (hL : ⁅M, M⁆ = L)
    (π : Equiv.Perm (Fin n) ≃* ↥M) (σ : Equiv.Perm (Fin n)) :
    ((π σ : ↥M) : Ω) ∈ L ↔ σ ∈ alternatingGroup (Fin n) := by
  rw [eq_map_alternating hn hL π]
  have hinj : Function.Injective (M.subtype.comp π.toMonoidHom) :=
    M.subtype_injective.comp π.injective
  exact Subgroup.mem_map_iff_mem hinj

theorem card_eq_alternating {n : ℕ} (hn : 5 ≤ n) {M L : Subgroup Ω} (hL : ⁅M, M⁆ = L)
    (π : Equiv.Perm (Fin n) ≃* ↥M) :
    Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin n)) := by
  rw [eq_map_alternating hn hL π]
  exact Subgroup.card_map_of_injective (M.subtype_injective.comp π.injective)

noncomputable def equivAlternating {n : ℕ} (hn : 5 ≤ n) {M L : Subgroup Ω} (hL : ⁅M, M⁆ = L)
    (π : Equiv.Perm (Fin n) ≃* ↥M) : ↥L ≃* ↥(alternatingGroup (Fin n)) :=
  ((MulEquiv.subgroupCongr (eq_map_alternating hn hL π)).trans
    ((alternatingGroup (Fin n)).equivMapOfInjective _
      (M.subtype_injective.comp π.injective)).symm)

theorem nine_dvd_card {X : Type*} [Group X] [Finite X] (h : ThreeRank2 X) : 9 ∣ Nat.card X := by
  obtain ⟨x, y, hx1, hx3, hy3, hxy, hyx⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hordx : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hordy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hE0 : IsElemAbelian 3 (⊥ : Subgroup X) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2]
    · rw [Subgroup.mem_bot.1 ha, one_pow]
  obtain ⟨hE1, hc1⟩ := exists_elemAbelian_sup_zpowers (E := ⊥) hE0 hordx
    (fun e he => by rw [Subgroup.mem_bot.1 he]; exact Commute.one_left _)
    (fun h => hx1 (Subgroup.mem_bot.1 h))
  rw [bot_sup_eq] at hE1 hc1
  obtain ⟨-, hc2⟩ := exists_elemAbelian_sup_zpowers hE1 hordy
    (fun e he => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      exact Commute.zpow_left (show Commute x y from hxy) n) hyx
  rw [hc1, Subgroup.card_bot] at hc2
  have h9 := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers x ⊔ Subgroup.zpowers y)
  rw [hc2] at h9
  simpa using h9

end General

variable {V : Type} [CommGroup V] [Finite V]

namespace Hyp

variable {G L : Subgroup (MulAut V)} (S : Hyp G L)
include S

theorem commutator_sup (hP4 : AsB15Part4) {B : Subgroup (MulAut V)}
    (hB : IsFFStarOffender G B) : ⁅L ⊔ B, L ⊔ B⁆ = L := by
  have hBn : B ≤ Subgroup.normalizer (L : Set (MulAut V)) := fun b hb =>
    S.le_normalizer hP4 (hB.1 hb)
  refine le_antisymm (commutator_le_of_sq_mem (fun y hy => S.conj_mem hP4
    ((sup_le S.hLG hB.1) hy)) (B1Red.sq_mem_of_mem_sup hBn hB.2.2.1.2)) ?_
  calc L = ⁅L, L⁆ := (B5.commutator_L_perfect' S.hLq).symm
    _ ≤ ⁅L ⊔ B, L ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left

theorem sym_data (hP4 : AsB15Part4) {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B)
    {U Z : Subgroup V} {n : ℕ} (hn : 5 ≤ n) (h : SymmetricNatural (L ⊔ B) U Z n) :
    ∃ π : Equiv.Perm (Fin n) ≃* ↥(L ⊔ B),
      (FFModel.symDn n).RealizesVia (L ⊔ B) U Z π.toMonoidHom ∧
      ∀ σ, ((π σ : ↥(L ⊔ B)) : MulAut V) ∈ L ↔ σ ∈ alternatingGroup (Fin n) := by
  obtain ⟨π₀, hπ₀⟩ := h
  refine ⟨FFC.equivOfRealizes (FFC.symDn_faithful hn) hπ₀, hπ₀,
    mem_iff_alternating hn (S.commutator_sup hP4 hB) _⟩

theorem false_of_five (hP4 : AsB15Part4) {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B)
    (π : Equiv.Perm (Fin 5) ≃* ↥(L ⊔ B)) : False := by
  have h9 := nine_dvd_card S.h3
  rw [card_eq_alternating (le_refl 5) (S.commutator_sup hP4 hB) π, nat_card_alternatingGroup]
    at h9
  simp [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial] at h9

end Hyp

section Eight

abbrev t01 : Equiv.Perm (Fin 8) := Equiv.swap 0 1

abbrev c234 : Equiv.Perm (Fin 8) := Equiv.swap 2 3 * Equiv.swap 3 4

abbrev c567 : Equiv.Perm (Fin 8) := Equiv.swap 5 6 * Equiv.swap 6 7

theorem t01_not_mem : t01 ∉ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem c234_mem : c234 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem c567_mem : c567 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem t01_sq : t01 * t01 = 1 := by decide

theorem c234_cube : c234 ^ 3 = 1 := by decide

theorem c567_cube : c567 ^ 3 = 1 := by decide

theorem c234_ne_one : c234 ≠ 1 := by decide

theorem comm_c234_c567 : c234 * c567 = c567 * c234 := by decide

theorem comm_t01_c234 : t01 * c234 = c234 * t01 := by decide

theorem comm_t01_c567 : t01 * c567 = c567 * t01 := by decide

theorem c567_ne : c567 ≠ 1 ∧ c567 ≠ c234 ∧ c567 ≠ c234 ^ 2 := by decide

theorem c567_not_mem_zpowers : c567 ∉ Subgroup.zpowers c234 := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  have hord : orderOf c234 = 3 := orderOf_eq_prime c234_cube c234_ne_one
  rw [← zpow_mod_orderOf, hord] at hk
  have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk3 with h0 | h1 | h2
  · rw [h0, zpow_zero] at hk
    exact c567_ne.1 hk.symm
  · rw [h1, zpow_one] at hk
    exact c567_ne.2.1 hk.symm
  · rw [h2] at hk
    exact c567_ne.2.2 (by rw [← hk]; norm_cast)

end Eight

namespace Hyp

variable {G L : Subgroup (MulAut V)} (S : Hyp G L)
include S

theorem conj_X_eq {s a : MulAut V} (hsa : s * a⁻¹ ∈ L)
    {x : MulAut V} (hx : x ∈ pCoreOf 3 G) (ha : a ∈ G) :
    s * x * s⁻¹ = a * x * a⁻¹ := by
  have hax : a * x * a⁻¹ ∈ pCoreOf 3 G :=
    (Subgroup.mem_normalizer_iff.1 ((le_normalizer_pCore3 G) ha) x).1 hx
  have hc := S.commute_X _ hax _ hsa
  calc s * x * s⁻¹ = (s * a⁻¹) * (a * x * a⁻¹) * (s * a⁻¹)⁻¹ := by group
    _ = a * x * a⁻¹ := by rw [← hc]; group

theorem false_of_eight {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B)
    (hBX : ¬ B ≤ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V)))
    (π : Equiv.Perm (Fin 8) ≃* ↥(L ⊔ B))
    (hπ : ∀ σ, ((π σ : ↥(L ⊔ B)) : MulAut V) ∈ L ↔ σ ∈ alternatingGroup (Fin 8)) : False := by
  have hMG : L ⊔ B ≤ G := sup_le S.hLG hB.1
  set f : Equiv.Perm (Fin 8) → MulAut V := fun σ => ((π σ : ↥(L ⊔ B)) : MulAut V) with hf
  have hfmul : ∀ σ τ, f (σ * τ) = f σ * f τ := fun σ τ => by simp [hf]
  have hfone : f 1 = 1 := by simp [hf]
  have hfG : ∀ σ, f σ ∈ G := fun σ => hMG (π σ).2
  have hfinj : Function.Injective f := Subtype.val_injective.comp π.injective
  obtain ⟨a, haB, hax⟩ : ∃ a ∈ B, a ∉ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V)) := by
    by_contra h
    push Not at h
    exact hBX h
  obtain ⟨x₀, hx₀, hx₀a⟩ : ∃ x₀ ∈ pCoreOf 3 G, x₀ * a ≠ a * x₀ := by
    by_contra h
    push Not at h
    exact hax (Subgroup.mem_centralizer_iff.2 fun x hx => (h x hx))
  have haM : a ∈ L ⊔ B := (le_sup_right : B ≤ L ⊔ B) haB
  set σa : Equiv.Perm (Fin 8) := π.symm ⟨a, haM⟩ with hσa
  have hfa : f σa = a := by simp [hf, hσa]
  have haL : a ∉ L := fun h => hx₀a (S.commute_X x₀ hx₀ a h)
  have hσaodd : σa ∉ alternatingGroup (Fin 8) := fun h => haL (hfa ▸ (hπ σa).2 h)
  set s := f t01 with hs
  have hsa : s * a⁻¹ ∈ L := by
    have : s * a⁻¹ = f (t01 * σa⁻¹) := by
      rw [hfmul, ← hfa]
      congr 1
      have h1 : f σa * f σa⁻¹ = 1 := by rw [← hfmul, mul_inv_cancel, hfone]
      exact (eq_inv_of_mul_eq_one_right h1).symm
    rw [this]
    refine (hπ _).2 ?_
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
    have h1 : Equiv.Perm.sign t01 = -1 := by decide
    have h2 : Equiv.Perm.sign σa = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σa) with h | h
      · exact absurd ((Equiv.Perm.mem_alternatingGroup).2 h) hσaodd
      · exact h
    rw [h1, h2]
    rfl
  have hsG : s ∈ G := hfG t01
  have hs2 : s * s = 1 := by rw [hs, ← hfmul, t01_sq, hfone]
  have hs1 : s ≠ 1 := by
    intro h
    apply t01_not_mem
    have : f t01 ∈ L := by rw [← hs, h]; exact L.one_mem
    exact (hπ t01).1 this
  have hnc : ∃ x ∈ pCoreOf 3 G, s * x ≠ x * s := by
    refine ⟨x₀, hx₀, fun h => ?_⟩
    have h1 : s * x₀ * s⁻¹ = x₀ := by rw [h]; group
    rw [S.conj_X_eq hsa hx₀ (hB.1 haB)] at h1
    apply hx₀a
    calc x₀ * a = a * x₀ * a⁻¹ * a := by rw [h1]
      _ = a * x₀ := by group
  have hsD : ∀ d ∈ pCoreOf 3 G, s * d * s⁻¹ ∈ pCoreOf 3 G := fun d hd =>
    (Subgroup.mem_normalizer_iff.1 ((le_normalizer_pCore3 G) hsG) d).1 hd
  obtain ⟨c, hcX, hc3, hsc⟩ :=
    exists_inv_of_order_prime Nat.prime_three (pCore3_isPGroup G) hs2 hsD hnc
  have hxL : f c234 ∈ L := (hπ c234).2 c234_mem
  have hyL : f c567 ∈ L := (hπ c567).2 c567_mem
  refine false_of_commuting_threes S.hq (t := s) (c := c) (x := f c234) (y := f c567) hsG
    ((pCore3_le G) hcX) (hfG _) (hfG _) hs2 hs1 ?_ ?_ hsc ?_ ?_ ?_ ?_ ?_ ?_
    (S.commute_X c hcX _ hxL).symm ?_ (S.commute_X c hcX _ hyL).symm
  · rw [← hc3]
    exact pow_orderOf_eq_one c
  · intro h
    rw [h, orderOf_one] at hc3
    exact absurd hc3 (by norm_num)
  · intro h
    exact c234_ne_one (hfinj (h.trans hfone.symm))
  · have : f (c234 ^ 3) = f c234 ^ 3 := by simp [hf]
    rw [← this, c234_cube, hfone]
  · have : f (c567 ^ 3) = f c567 ^ 3 := by simp [hf]
    rw [← this, c567_cube, hfone]
  · rw [← hfmul, ← hfmul, comm_c234_c567]
  · intro hmem
    apply c567_not_mem_zpowers
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have : f (c234 ^ k) = f c234 ^ k := by simp [hf]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, hfinj (this.trans hk)⟩
  · rw [hs, ← hfmul, ← hfmul, comm_t01_c234]
  · rw [hs, ← hfmul, ← hfmul, comm_t01_c567]

end Hyp

end SmithB57E

end CFSG.Quasithin
