module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN3e

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

theorem card_perm_fin_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_perm_fin_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

namespace PsiData

variable (P : PsiData T L V 3) (h : Hyp6Sec2 G T M L V)

omit [Finite G] in
theorem ker_eq : P.ψ.ker = (CHU T L V).subgroupOf (HH T) := by
  ext x
  rw [MonoidHom.mem_ker, P.ker, Subgroup.mem_subgroupOf]

omit [Finite G] in
include P in
theorem card_HH : Nat.card ↥(HH T) = Nat.card ↥(CHU T L V) * 6 := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective P.surj
  have hle : CHU T L V ≤ HH T := centralizerMod_le_left _ _ _
  rw [P.ker_eq, card_perm_fin_three,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  exact h1.symm

include P h in
theorem subgroupOf_T_eq (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h629 : Stmt6_2_9)
    (h6210 : Stmt6_2_10) (h6212 : Stmt6_2_12) (a : ↥(HH T)) (haV : (a : G) ∈ V)
    (haC : (a : G) ∉ CHU T L V) :
    T.subgroupOf (HH T) = (Subgroup.zpowers (P.ψ a)).comap P.ψ := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  constructor
  · intro hx
    rcases P.psi_eq_of_mem_M h h629 a haV haC x (h.T_le hx) with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers _
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : P.ψ x * P.ψ a = P.ψ a * P.ψ x := by
      rw [← hk]
      exact ((Commute.refl (P.ψ a)).zpow_left k).eq
    have hxN : (x : G) ∈ Subgroup.normalizer (V : Set G) := ((P.swap_norm a haV haC).2 x).mpr hcomm
    have hxHM : (x : G) ∈ HH T ⊓ M := by
      rw [(h629 G T M L V h).1]
      exact ⟨x.2, hxN⟩
    rw [P.HH_inf_M_eq_T h hZ h629 h6210 h6212] at hxHM
    exact hxHM

include P h in
theorem card_T (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h629 : Stmt6_2_9)
    (h6210 : Stmt6_2_10) (h6212 : Stmt6_2_12) : Nat.card ↥T = 2 * Nat.card ↥(CHU T L V) := by
  obtain ⟨a, haV, haC⟩ := exists_a h hZ h6210
  have hτ : (P.ψ a).IsSwap := (P.swap_norm a haV haC).1
  have hidx : (T.subgroupOf (HH T)).index = 3 := by
    rw [P.subgroupOf_T_eq h hZ h629 h6210 h6212 a haV haC,
      Subgroup.index_comap_of_surjective _ P.surj]
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers (P.ψ a))
    rw [Nat.card_zpowers, hτ.orderOf, card_perm_fin_three] at h1
    omega
  have h2 := Subgroup.relIndex_mul_card (H := T) (K := HH T)
  rw [inf_eq_left.mpr (T_le_HH T), Subgroup.relIndex, hidx, P.card_HH] at h2
  omega

end PsiData

namespace KData

variable {g : G} {D : Subgroup G} (hk : KData T L V g D)

omit [Finite G] in
include hk in
theorem card_K : Nat.card ↥(V ⊔ conjSubgroup V g) = 192 := by
  obtain ⟨φ, hφs, hφk⟩ := hk.quot
  have h1 := Subgroup.card_ker_mul_card_of_surjective hφs
  rw [hφk, card_perm_fin_three,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hk.D_le_K).toEquiv, hk.extra.2.1] at h1
  omega

end KData

omit [Finite G] in
theorem exists_hom_perm5 (hNeq : Subgroup.normalizer (V : Set G) = L ⊔ T)
    (e : ↥(autOn (L ⊔ T) V) ≃* Equiv.Perm (Fin 5)) :
    ∃ φ : ↥(Subgroup.normalizer (V : Set G)) →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
      φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G)) := by
  set N : Subgroup G := Subgroup.normalizer (V : Set G) with hN
  have hautN : autOn N V = autOn (L ⊔ T) V := by rw [hNeq]
  let f : ↥N →* MulAut ↥V := A4.actionOn V N le_rfl
  have hmem : ∀ x : ↥N, f x ∈ autOn (L ⊔ T) V := fun x => by
    rw [← hautN]
    exact (A4.mem_autOn_iff le_rfl).mpr ⟨x, rfl⟩
  let g₁ : ↥N →* ↥(autOn (L ⊔ T) V) := f.codRestrict _ hmem
  refine ⟨e.toMonoidHom.comp g₁, ?_, ?_⟩
  · intro p
    obtain ⟨a, rfl⟩ := e.surjective p
    have ha : (a : MulAut ↥V) ∈ autOn N V := by
      rw [hautN]
      exact a.2
    obtain ⟨x, hx⟩ := (A4.mem_autOn_iff le_rfl).mp ha
    exact ⟨x, by
      have : g₁ x = a := Subtype.ext hx
      simp [this]⟩
  · ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    rw [show e.toMonoidHom (g₁ x) = e (g₁ x) from rfl, MulEquiv.map_eq_one_iff]
    have : g₁ x = 1 ↔ f x = 1 := by
      constructor
      · intro h1
        exact congrArg Subtype.val h1
      · intro h1
        exact Subtype.ext h1
    rw [this]
    exact A4.actionOn_eq_one_iff le_rfl x

omit [Finite G] in
theorem card_normalizer (hNeq : Subgroup.normalizer (V : Set G) = L ⊔ T)
    (e : ↥(autOn (L ⊔ T) V) ≃* Equiv.Perm (Fin 5)) :
    Nat.card ↥(Subgroup.normalizer (V : Set G)) =
      Nat.card ↥(Subgroup.centralizer (V : Set G)) * 120 := by
  obtain ⟨φ, hφs, hφk⟩ := exists_hom_perm5 hNeq e
  have h1 := Subgroup.card_ker_mul_card_of_surjective hφs
  rw [hφk, card_perm_fin_five,
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer _)).toEquiv] at h1
  exact h1.symm

end CFSG.Quasithin.H13.GM22
