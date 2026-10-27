module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem normalizer_zpowers_eq_centralizer {z : G} (hz : z ^ 2 = 1) :
    Subgroup.normalizer (Subgroup.zpowers z : Set G) = Subgroup.centralizer ({z} : Set G) := by
  refine le_antisymm (fun g hg => ?_) (centralizer_le_normalizer_zpowers z)
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hz1 : z = 1
  · rw [hz1, mul_one, one_mul]
  have h1 : g * z * g⁻¹ ∈ Subgroup.zpowers z :=
    (Subgroup.mem_normalizer_iff.mp hg z).mp (Subgroup.mem_zpowers z)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  have hz2 : ∀ k : ℤ, z ^ k = 1 ∨ z ^ k = z := by
    intro k
    have e : z ^ k = z ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
      rw [zpow_add, zpow_mul, zpow_two, ← pow_two, hz, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · left
      rw [e, h0, zpow_zero]
    · right
      rw [e, h0, zpow_one]
  rcases hz2 k with h | h
  · rw [h] at hk
    exfalso
    apply hz1
    have : g * z * g⁻¹ * g = g := by rw [← hk, one_mul]
    simpa using this
  · rw [h] at hk
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [← hk]

theorem cComp_of_le_of_normal {X N K : Subgroup G} (hXN : X ≤ N)
    (hX : N ≤ Subgroup.normalizer (X : Set G)) (hK : quasithinIsCComponent K N) (hKX : K ≤ X) :
    quasithinIsCComponent K X := by
  refine ⟨hK.1, hK.2.1, A3.subnormal_of_le_of_le hK.2.2.1 hKX hXN, ?_⟩
  intro J hJK hJ1 hJp hJX
  exact hK.2.2.2 J hJK hJ1 hJp (A3.subnormal_trans hJX (A3.subnormal_of_normal hXN
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hXN).mpr hX)))

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem mem_V₁_of_mem_centralizer (hF : Facts43) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) {z : G} (hzV : z ∈ fsuV T I)
    (hzT : z ∈ Subgroup.centralizer (T : Set G)) : z ∈ V₁ := by
  have hab := (SecA.isElemAbelian_fsuV h).1
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV h).2 w w.2)
  have hn : 2 ≤ n := h.one_lt
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨x.2, hx⟩
    rw [hcV] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hx'))
  have hflag := SecA.isFlagW_of_isVi h hV₁
  rw [hZ] at hflag
  have hfix : ∀ p ∈ autOn (T ⊓ L) (fsuV T I), p ⟨z, hzV⟩ = ⟨z, hzV⟩ := by
    intro p hp
    obtain ⟨t, ht, htV, rfl⟩ := SecA.mem_autOn_iff.mp hp
    apply Subtype.ext
    rw [SecA.conjV_apply_coe]
    have hc := Subgroup.mem_centralizer_iff.mp hzT t ht.1
    calc t * z * t⁻¹ = z * t * t⁻¹ := by rw [hc]
      _ = z := by group
  have hmem : (⟨z, hzV⟩ : ↥(fsuV T I)) ∈ V₁.subgroupOf (fsuV T I) := by
    rcases hk with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ |
        ⟨-, -, -, -, -, K, _, _, hK, π, hπ⟩
    · rw [hZ] at hπ
      exact hF.fixSL3 K n hn hK _ hsq _ π hπ _ (SecA.isSylowTwoOf_P h) _ hflag _ hfix
    · rw [hZ] at hπ
      exact hF.fixSp4 K n hn hK _ hsq _ π hπ _ (SecA.isSylowTwoOf_P h) _ hflag _ hfix
    · rw [hZ] at hπ
      exact hF.fixG2 K n hn hK _ hsq _ π hπ _ (SecA.isSylowTwoOf_P h) _ hflag _ hfix
  exact hmem

theorem kOf_le_centralizer_V₁ (hP : SecB.PointFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    KOf L V₁ V₁ ≤ Subgroup.centralizer (V₁ : Set G) := by
  have hL₁ := SecB.lOf_le_centralizer hP h1102 h hV₁
  refine conjClosure_le fun g hg x hx => ?_
  exact (Subgroup.mem_normalizer_iff.mp (SecA.mem_normalizer_centralizer hg) x).mp (hL₁ hx)

theorem kOf_le_centralizer_of (hP : SecB.PointFacts) (hF : Facts43) (h1102 : Stmt11_0_2)
    (h1142 : Stmt11_4_2) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) {z : G} (hz : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G))
    (hz1 : z ≠ 1) :
    KOf L V₁ V₁ ≤ Subgroup.centralizer ({z} : Set G) ∧
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (KOf L V₁ V₁ : Set G) := by
  have hz2 : z ^ 2 = 1 := (SecA.isElemAbelian_fsuV h).2 z hz.1
  have hzV₁ := mem_V₁_of_mem_centralizer hF h1102 h hcV hV₁ hz.1 hz.2
  have hL₁ := SecB.lOf_le_centralizer hP h1102 h hV₁
  have hL₁z : LOf L V₁ ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := fun l hl =>
    centralizer_le_normalizer_zpowers z (Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hL₁ hl) z hzV₁).symm))
  have heq := h1142 G T L I n V₁ h hV₁ z hz hz1
  rw [← heq, ← normalizer_zpowers_eq_centralizer hz2]
  exact ⟨SecD.kOf_le_normalizer hL₁z, SecD.normalizer_le_normalizer_kOf L V₁ _⟩

theorem out2Closed_kOf (hF : Facts43) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1)
    (h1112 : Stmt11_1_2) (h1141 : Stmt11_4_1) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hKC : KOf L V₁ V₁ ≤ Subgroup.centralizer (V₁ : Set G)) :
    Out2Closed (↥(KOf L V₁ V₁) ⧸ CFSG.pCore 2 ↥(KOf L V₁ V₁)) := by
  have hn := h.one_lt
  have hK := SecD.kOf_cComp h1110 h1112 h hV₁
  have hKC' : quasithinIsCComponent (KOf L V₁ V₁) (Subgroup.centralizer (V₁ : Set G)) :=
    cComp_of_le_of_normal (Subgroup.centralizer_le_normalizer (V₁ : Set G))
      (fun t ht => SecA.mem_normalizer_centralizer ht) hK hKC
  by_cases heq : LOf L V₁ = KOf L V₁ V₁
  · rw [← heq]
    obtain ⟨F, _, _, hF4, ⟨e⟩⟩ := (h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁
    exact hF.out2SL2 F n (by omega) hF4 _ ⟨e⟩
  have hlt : LOf L V₁ < KOf L V₁ V₁ := lt_of_le_of_ne (le_conjClosure _ _) heq
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  rcases (h1141 G T L I n V₁ X h hV₁ hX).2.1 _ hKC' hlt with h1 | ⟨⟨p, hp, hp11, hpsl⟩, -⟩
  · have hTN : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
    have hsyl : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
        (Subgroup.normalizer (V₁ : Set G)) := by
      rw [inf_eq_left.mpr hTN]
      exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTN
    obtain ⟨K', hLK', hK', hNK', hcase'⟩ := h1111 G T L I n 1 V₁ V₁ h hV₁
      (Or.inl ⟨rfl, SecA.IsVi.ne_bot h hV₁ le_rfl, le_rfl, hsyl⟩)
    have hKK' : KOf L V₁ V₁ = K' := cComp_eq_of_normal hK hK' hNK'
      (SecD.lOf_ne_bot h1110 h hV₁) (perfectCore_perfect _) (le_conjClosure _ _) hLK'
    have hlists : List11_1_1Two (↥(KOf L V₁ V₁) ⧸ CFSG.pCore 2 ↥(KOf L V₁ V₁)) n ∨
        (n = 2 ∧ List11_1_1Three (↥(KOf L V₁ V₁) ⧸ CFSG.pCore 2 ↥(KOf L V₁ V₁))) := by
      rw [hKK']
      rcases hcase' with h0 | hl | hl
      · exact absurd (h0.trans hKK'.symm) heq
      · exact Or.inl hl
      · exact Or.inr hl
    exact hF.out2Case1 G _ n hlists h1 hK.2.1
  · exact hF.out2L2p _ p hp hp11 hpsl

end CFSG.Quasithin.Vol2.Ch11.SecE
