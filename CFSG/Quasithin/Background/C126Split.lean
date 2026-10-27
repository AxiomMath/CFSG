module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Background.E2Three

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B2F E2

theorem two_pow_mul_ne_120 (n : ℕ) : 2 ^ n * (4 ^ n - 1) ≠ 120 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h64 : 64 ≤ 4 ^ n := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have : 63 ≤ 4 ^ n - 1 := by omega
    nlinarith

theorem strictMono_two_pow_mul : StrictMono fun n : ℕ => 2 ^ n * (4 ^ n - 1) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have ha : 0 < 2 ^ n := by positivity
  have hb : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨b, hb'⟩ : ∃ b, 4 ^ n = b + 1 := ⟨4 ^ n - 1, by omega⟩
  have e1 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  have e2 : 4 ^ (n + 1) = 4 * (b + 1) := by rw [pow_succ, hb']; ring
  have e3 : 4 * (b + 1) - 1 = 4 * b + 3 := by omega
  simp only [e1, e2, e3, hb', Nat.add_sub_cancel]
  nlinarith [Nat.zero_le (2 ^ n * b)]

section Module

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}

theorem card_of_isL2Natural {C : Subgroup W} {n : ℕ} (h : E2.IsL2Natural L C n) :
    Nat.card ↥L = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨-, F, _, _, hF, e, -⟩ := h
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hq]
  have h4 : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]

theorem card_of_isA5Module (h : E2.IsA5Module L) : Nat.card ↥L = 120 := by
  obtain ⟨θ, -⟩ := h
  rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

end Module

section Solvable

variable {X : Type*} [Group X]

theorem isSolvable_sup_of_le_normalizer' {N T : Subgroup X}
    (hTN : T ≤ Subgroup.normalizer (N : Set X)) (hN : Group.IsSolvable N)
    (hT : Group.IsSolvable T) : Group.IsSolvable (N ⊔ T : Subgroup X) := by
  set V := N ⊔ T
  have hNV : N ≤ V := le_sup_left
  have hTV : T ≤ V := le_sup_right
  have hVN : V ≤ Subgroup.normalizer (N : Set X) := sup_le Subgroup.le_normalizer hTN
  have : (N.subgroupOf V).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNV).mpr hVN
  set π := QuotientGroup.mk' (N.subgroupOf V)
  set f : T →* V ⧸ N.subgroupOf V := π.comp (Subgroup.inclusion hTV)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hv : (v : X) ∈ ((T ⊔ N : Subgroup X) : Set X) := by
      rw [sup_comm]
      exact v.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T N hTN] at hv
    obtain ⟨t, ht, n, hn, htn⟩ := hv
    refine ⟨⟨t, ht⟩, ?_⟩
    change π (Subgroup.inclusion hTV ⟨t, ht⟩) = π v
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h : ((Subgroup.inclusion hTV ⟨t, ht⟩)⁻¹ * v : V) = (t⁻¹ * v : X) := rfl
    rw [h, ← htn, inv_mul_cancel_left]
    exact hn
  have hNVsol : Group.IsSolvable (N.subgroupOf V) := by
    have := hN
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNV).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNV).injective
  have hQsol : Group.IsSolvable (V ⧸ N.subgroupOf V) := Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_subgroup_quotient (N.subgroupOf V)

theorem isSolvable_iSup_family (I : Finset (Subgroup X)) (hcard : I.card = 1 ∨ I.card = 2)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hsolv : ∀ L ∈ I, Group.IsSolvable ↥L) : Group.IsSolvable ↥(⨆ L ∈ I, L) := by
  classical
  rcases hcard with h | h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
    have hs : (⨆ L ∈ ({a} : Finset (Subgroup X)), L) = a := by simp
    rw [hs]
    exact hsolv a (Finset.mem_singleton_self a)
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 h
    have hx := hsolv x (by simp)
    have hy := hsolv y (by simp)
    have hsup : (⨆ L ∈ ({x, y} : Finset (Subgroup X)), L) = x ⊔ y := by
      simp [iSup_or, iSup_sup_eq]
    rw [hsup]
    refine isSolvable_sup_of_le_normalizer' (fun b hb => ?_) hx hy
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have hc := hcomm x (by simp) y (by simp) hxy
    have key : ∀ c ∈ x, ∀ d ∈ y, d * c * d⁻¹ = c := fun c hc' d hd => by
      have h1 := hc c hc' d hd
      calc d * c * d⁻¹ = (c * d) * d⁻¹ := by rw [h1]
        _ = c := by simp
    constructor
    · intro ha
      rw [key a ha b hb]
      exact ha
    · intro ha
      have h2 := key _ ha b⁻¹ (y.inv_mem hb)
      have e : b⁻¹ * (b * a * b⁻¹) * b⁻¹⁻¹ = a := by group
      rw [e] at h2
      exact h2.symm ▸ ha

end Solvable

section PerfectCore

variable {G : Type} [Group G] [Finite G]

theorem perfectCore_le_twoResidual' (H : Subgroup G) : perfectCore H ≤ twoResidual H := by
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf H
  have : Group.IsNilpotent ↥T := hT.2.1.isNilpotent
  refine perfectCore_le_of_sup_solvable (B := T) (twoResidual_le H)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidual_le H)).2
      (le_normalizer_twoResidual H)) ?_ inferInstance
  rw [sup_comm]
  exact (sup_twoResidual_eq hT).symm

theorem perfectCore_le_centralizer_of_solvable {A V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hsolv : Group.IsSolvable ↥(autI hV A)) :
    perfectCore A ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  have h1 : (perfectCore (A.subgroupOf (Subgroup.normalizer (V : Set G)))).map
      (Subgroup.normalizer (V : Set G)).subtype = perfectCore A := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hAN]
  rw [← h1] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h2 : (perfectCore (A.subgroupOf (Subgroup.normalizer (V : Set G)))).map (convI hV) = ⊥ := by
    rw [map_perfectCore]
    exact (isSolvable_iff_perfectCore_eq_bot _).1 hsolv
  have h3 : convI hV y = 1 := by
    have : convI hV y ∈ (perfectCore (A.subgroupOf (Subgroup.normalizer (V : Set G)))).map
        (convI hV) := Subgroup.mem_map_of_mem _ hy
    rw [h2, Subgroup.mem_bot] at this
    exact this
  exact (convI_eq_one_iff hV y).1 h3

theorem perfectCore_le_centralizer_of_J {H V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hKJ : twoResidual H ≤ thompsonJ H)
    (hsolv : Group.IsSolvable ↥(autI hV (thompsonJ H))) :
    perfectCore H ≤ Subgroup.centralizer (V : Set G) := by
  have hPH : perfectCore H ≤ thompsonJ H := (perfectCore_le_twoResidual' H).trans hKJ
  have hP : ⁅perfectCore H, perfectCore H⁆ = perfectCore H := perfectCore_perfect H
  exact (le_perfectCore_of_perfect hPH hP).trans
    (perfectCore_le_centralizer_of_solvable hV ((thompsonJ_le_self H).trans hHN) hsolv)

end PerfectCore

end CFSG.Quasithin.C126
