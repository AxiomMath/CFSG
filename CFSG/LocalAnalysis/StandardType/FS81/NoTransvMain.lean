module

public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvUnique
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreDefs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem fs81Nt_mem_commutator (hsimple : IsSimpleGroup G) {b₀ : G} {A : Subgroup G}
    (hb₀ : orderOf b₀ = 3) (hdisj : Disjoint (Subgroup.zpowers b₀) A) (hA : A ≠ ⊥) :
    b₀ ∈ commutator G := by
  rcases hsimple.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    have : IsMulCommutative G := (commutator_eq_bot_iff G).mp h
    have := Subgroup.normal_of_comm (Subgroup.zpowers b₀)
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.zpowers b₀) with h1 | h1
    · have hb : b₀ = 1 := (Subgroup.mem_bot).mp (h1 ▸ Subgroup.mem_zpowers b₀)
      rw [hb, orderOf_one] at hb₀
      omega
    · rw [h1] at hdisj
      exact hA (disjoint_top.mp hdisj.symm)
  · rw [h]
    exact Subgroup.mem_top b₀

theorem transvSetup_of
    {b₀ : G} {K E : Subgroup G} {r : Row} (hstd : StdAssumptions b₀ K E r)
    {B : Basis3 G (r.n + 1)} (hB : Adapted B b₀ K E) (hfus : Fus42 B b₀)
    (htr : TransvAll b₀ K E) : TransvSetup b₀ K E := by
  obtain ⟨-, ⟨hA, hEmax, -, -, -, -⟩, -, hdisj, hsup, -, -, hCK⟩ := hstd
  obtain ⟨hb₀, hKC, hKn, hKz, hKmark, hA2, -, -⟩ := hA
  have hOut := fs81_row_out_not_dvd_three hKmark hKz
  have hnorm : ¬ (Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by
    have := hfus.1
    rwa [hB.1] at this
  exact ⟨hb₀, hEmax.2.1, hsup, hdisj, htr.1, htr.2, fun y hy k hk =>
    fs81_three_elem_mem_E hb₀ hKC hKn hOut hA2 hsup hCK hEmax.2.1 hnorm hy hk⟩

theorem twoLocalPrimeRank_C_le {b₀ : G} {K : Subgroup G} {n : ℕ} (hb₀ : orderOf b₀ = 3)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hKz : Subgroup.center K = ⊥) (hOut : ¬ 3 ∣ Nat.card (Outer K))
    (hA2 : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hK3 : ∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' ≤ 3 ^ n) :
    twoLocalPrimeRank 3 ↥(Subgroup.centralizer ({b₀} : Set G)) ≤ n + 1 :=
  fs81Nt_twoLocalPrimeRank_le fun _ _ => fs81Nt_pRank_le fun F _ hF => by
    have := card_elemAb_le_of_C hb₀ hKC hKn hKz hOut hA2 hK3
      (F := F.map (Subgroup.centralizer ({b₀} : Set G)).subtype) (Subgroup.map_subtype_le _)
      (hF.map _)
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at this

@[expose] def NoTransvData {n : ℕ} (B : Basis3 G (n + 1)) (b₀ : G) (K E : Subgroup G) : Prop :=
  SignChanges B.b b₀ E ∧ DiagSigns B E ∧ CoordTrans B b₀ E ∧ KleinSigns B E ∧ DiagSigns3 B E ∧
    (∃ k₀ k₁ : Fin (n + 1), k₀ ≠ 0 ∧ k₁ ≠ 0 ∧ k₀ ≠ k₁ ∧ SignRealized B E (dsign k₀ k₁)) ∧
    NoOffenderA b₀ K E

@[expose] def NoTransvDataAt (r : Row) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E r → ∀ B : Basis3 G (r.n + 1), Adapted B b₀ K E → LocalData r B b₀ →
      Fus42 B b₀ → TransvAll b₀ K E → NoTransvData B b₀ K E

theorem noTransv_of
    (hR : RowElemAb3) (h6 : NoTransvDataAt Row.D6) (h7 : NoTransvDataAt Row.twD7)
    (hE7 : NoTransvDataAt Row.E7) : NoTransv := by
  intro G _ _ b₀ K E r hstd B hB hloc hfus htr
  have hdata : NoTransvData B b₀ K E := by
    cases r with
    | D6 => exact h6 G b₀ K E hstd B hB hloc hfus htr
    | twD7 => exact h7 G b₀ K E hstd B hB hloc hfus htr
    | E7 => exact hE7 G b₀ K E hstd B hB hloc hfus htr
  obtain ⟨hsc, hdiag, hct, hKl, hd3, ⟨k₀, k₁, hk₀, hk₁, hk, hds⟩, hoff⟩ := hdata
  have h := transvSetup_of hstd hB hfus htr
  obtain ⟨hsimple, ⟨hA, -, -, hEcard, -, -⟩, hrow, hdisj, -, hEKmax, hEKcard, -⟩ := hstd
  obtain ⟨hb₀, hKC, hKn, hKz, hKmark, hA2, hA3, -⟩ := hA
  have hOut := fs81_row_out_not_dvd_three hKmark hKz
  obtain ⟨P₁, hP⟩ := h.exists_transvP1'
  obtain ⟨μ, hμ⟩ := hP.exists_cube_eq_pow h B hB hsc hdiag hct
  have hn : 6 ≤ r.n := by cases r <;> decide
  have hK3 := (hR G K (E ⊓ K) r hrow hKz inf_le_right hEKmax.2.1 hEKcard).1
  have hrank : twoLocalPrimeRank 3 G ≤ r.n + 1 := by
    rw [← hA3]
    exact twoLocalPrimeRank_C_le hb₀ hKC hKn hKz hOut hA2 hK3
  have hne := hP.not_exp_three h B hB hsc hKl hd3 hk₀ hk₁ hk hds hn hrank
  have hA9 : 9 ≤ Nat.card ↥(E ⊓ K) := by
    rw [hEKcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ r.n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hEA : Nat.card E = 3 * Nat.card ↥(E ⊓ K) := by
    rw [hEcard, hEKcard, Row.m, pow_succ, mul_comm]
  have hAbot : E ⊓ K ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hA9
    omega
  exact hP.false_of_noOffender h B hB hsc hKl hd3 hμ hne hA9 hKC hKn hKz hOut hoff hEA
    (fs81Nt_mem_commutator hsimple hb₀ hdisj hAbot)

end CFSG.StandardType.FrameRoute.FS81

end
