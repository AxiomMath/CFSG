module

public import CFSG.Quasithin.EmptyFaithful.S153D51

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace S153F

open CFSG.Quasithin.S153D

section Generic

variable {G : Type} [Group G]

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have h : B6.conjSub g (A ⊔ B) = A ⊔ B := by
    rw [OrderIso.map_sup, B6.conjSub_eq_self hA, B6.conjSub_eq_self hB]
  exact h

theorem mem_normalizer_blockU {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer (blockU L : Set G) := by
  have hQ : g ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) := normalizer_le_normalizer_pCoreOf 2 L hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg hQ ⊢
  show Subgroup.map (MulAut.conj g).toMonoidHom ⁅pCoreOf 2 L, L⁆ = ⁅pCoreOf 2 L, L⁆
  rw [Subgroup.map_commutator]
  exact congrArg₂ (fun A B => ⁅A, B⁆) hQ hg

theorem blockU_le {L : Subgroup G} : blockU L ≤ L := by
  rw [blockU, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hg₁L : g₁ ∈ L := pCoreOf_le 2 L hg₁
  rw [commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem hg₁L hg₂) (inv_mem hg₁L)) (inv_mem hg₂)

theorem blockU_le_pCoreOf {L : Subgroup G} : blockU L ≤ pCoreOf 2 L := by
  rw [blockU, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hg₁' : g₁ ∈ pCoreOf 2 L := hg₁
  have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ pCoreOf 2 L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hg₂) _).mp (inv_mem hg₁')
  have h2 := mul_mem hg₁' h1
  have e : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact h2

theorem mem_normalizer_of_le_centralizer {P C : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (C : Set G)) (hP : P ≤ C) :
    g ∈ Subgroup.normalizer (P : Set G) :=
  Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hP hg)

theorem mem_normalizer_conjSub_of_conj {g t : G} {X : Subgroup G}
    (h : t⁻¹ * g * t ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer ((B6.conjSub t X : Subgroup G) : Set G) := by
  rw [normalizer_conjSub, B6.mem_conjSub]
  exact h

theorem isPGroup_conjSub {P : Subgroup G} (hP : IsPGroup 2 ↥P) (t : G) :
    IsPGroup 2 ↥(B6.conjSub t P) := by
  intro x
  have hx : t⁻¹ * (x : G) * t ∈ P := B6.mem_conjSub.mp x.2
  obtain ⟨k, hk⟩ := hP ⟨t⁻¹ * (x : G) * t, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  have h1 : (t⁻¹ * (x : G) * t) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : (t⁻¹ * (x : G) * t) ^ 2 ^ k = t⁻¹ * (x : G) ^ 2 ^ k * t := by
    simpa using conj_pow (a := t⁻¹) (b := (x : G)) (i := 2 ^ k)
  have h3 : t⁻¹ * (x : G) ^ 2 ^ k * t = 1 := h2 ▸ h1
  have h4 : (x : G) ^ 2 ^ k = t * (t⁻¹ * (x : G) ^ 2 ^ k * t) * t⁻¹ := by group
  rw [h4, h3]
  simp

end Generic

section Closing

variable {G : Type} [Group G] [Finite G]

theorem exists_closing_subgroup {L S T YL YC : Subgroup G} {t₁ : G}
    (hS : S ≤ Subgroup.normalizer (L : Set G)) (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (ht₁ : t₁ ∈ T) (ht₁S : t₁ ∉ S) (hT : ∀ x ∈ T, x ∈ S ∨ t₁⁻¹ * x ∈ S)
    (hYLL : YL ≤ L) (hYC : YC = B6.conjSub t₁ YL) (hYCC : YC ≤ Subgroup.centralizer (L : Set G))
    (hU0 : blockU L ≠ ⊥) (hUP : blockU L ≤ pCoreOf 2 YL) :
    ∃ W : Subgroup G, W ≠ ⊥ ∧ IsPGroup 2 ↥W ∧ L ≤ Subgroup.normalizer (W : Set G) ∧
      T ≤ Subgroup.normalizer (W : Set G) ∧ YL ⊔ YC ≤ Subgroup.normalizer (W : Set G) := by
  set U := blockU L with hUdef
  set U' := B6.conjSub t₁ U with hU'def
  have hUYL : U ≤ YL := hUP.trans (pCoreOf_le 2 YL)
  have hU'YC : U' ≤ YC := hYC ▸ (B6.conjSub t₁).monotone hUYL
  have hLU : L ≤ Subgroup.normalizer (U : Set G) := fun g hg =>
    mem_normalizer_blockU (Subgroup.le_normalizer hg)
  have hNU : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (U : Set G) := fun g hg =>
    mem_normalizer_blockU hg
  have hLU' : L ≤ Subgroup.normalizer (U' : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh =>
      ((Subgroup.mem_centralizer_iff.mp (hYCC (hU'YC hh))) g hg).symm)
  have hYLU' : YL ≤ Subgroup.normalizer (U' : Set G) := fun g hg => hLU' (hYLL hg)
  have hYCU : YC ≤ Subgroup.normalizer (U : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (blockU_le : U ≤ L) (hYCC hg))
  have hYCU' : YC ≤ Subgroup.normalizer (U' : Set G) := by
    intro g hg
    apply mem_normalizer_conjSub_of_conj
    have hg' : t₁⁻¹ * g * t₁ ∈ YL := B6.mem_conjSub.mp (hYC ▸ hg)
    exact hLU (hYLL hg')
  set P := pCoreOf 2 YL with hPdef
  have hP2 : IsPGroup 2 ↥P := pCoreOf_isPGroup 2 YL
  have hP'2 : IsPGroup 2 ↥(B6.conjSub t₁ P) := isPGroup_conjSub hP2 t₁
  have hPYL : P ≤ YL := pCoreOf_le 2 YL
  have hPN : YL ≤ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 YL
  have hP'YC : B6.conjSub t₁ P ≤ YC := hYC ▸ (B6.conjSub t₁).monotone hPYL
  have hPW : P ≤ pCoreOf 2 (YL ⊔ YC) := by
    refine le_pCoreOf_of_le_normalizer 2 (hPYL.trans le_sup_left) (sup_le hPN fun g hg => ?_) hP2
    exact mem_normalizer_of_le_centralizer (hYCC hg) (hPYL.trans hYLL)
  have hP'W : B6.conjSub t₁ P ≤ pCoreOf 2 (YL ⊔ YC) := by
    refine le_pCoreOf_of_le_normalizer 2 (hP'YC.trans le_sup_right) (sup_le (fun g hg => ?_) fun g hg => ?_) hP'2
    · exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh =>
        ((Subgroup.mem_centralizer_iff.mp (hYCC (hP'YC hh))) g (hYLL hg)).symm)
    · have h1 : YC ≤ Subgroup.normalizer ((B6.conjSub t₁ P : Subgroup G) : Set G) := by
        rw [normalizer_conjSub, hYC]
        exact (B6.conjSub t₁).monotone hPN
      exact h1 hg
  have hWle : U ⊔ U' ≤ pCoreOf 2 (YL ⊔ YC) :=
    sup_le (hUP.trans hPW) ((B6.conjSub t₁).monotone hUP |>.trans hP'W)
  have ht₁sq : t₁ * t₁ ∈ S := by
    rcases hT (t₁ * t₁) (mul_mem ht₁ ht₁) with h | h
    · exact h
    · exfalso
      apply ht₁S
      simpa using h
  have hSW : S ≤ Subgroup.normalizer ((U ⊔ U' : Subgroup G) : Set G) := by
    intro x hx
    refine mem_normalizer_sup (hNU (hS hx)) ?_
    apply mem_normalizer_conjSub_of_conj
    have h1 : t₁⁻¹ * x * t₁ ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hTS ht₁)) x).mp hx
      simpa using this
    exact hNU (hS h1)
  have ht₁W : t₁ ∈ Subgroup.normalizer ((U ⊔ U' : Subgroup G) : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have e0 : B6.conjSub t₁ U = U' := rfl
    have e1 : B6.conjSub t₁ U' = U := by
      rw [← e0, ← B6.conjSub_mul]
      exact B6.conjSub_eq_self (hNU (hS ht₁sq))
    have h : B6.conjSub t₁ (U ⊔ U') = U ⊔ U' := by
      rw [OrderIso.map_sup, e0, e1, sup_comm]
    exact h
  have hTW : T ≤ Subgroup.normalizer ((U ⊔ U' : Subgroup G) : Set G) := by
    intro x hx
    rcases hT x hx with hxS | hxS
    · exact hSW hxS
    · have h2 := mul_mem ht₁W (hSW hxS)
      have e : t₁ * (t₁⁻¹ * x) = x := by group
      rwa [e] at h2
  refine ⟨U ⊔ U', fun h => hU0 (le_bot_iff.mp (h ▸ le_sup_left)),
    (pCoreOf_isPGroup 2 (YL ⊔ YC)).to_le hWle, fun g hg => mem_normalizer_sup (hLU hg) (hLU' hg),
    hTW, sup_le (fun g hg => mem_normalizer_sup (hLU (hYLL hg)) (hYLU' hg)) fun g hg =>
      mem_normalizer_sup (hYCU hg) (hYCU' hg)⟩

omit [Finite G] in
theorem mem_or_mem_of_relIndex_eq_two {S T : Subgroup G} (hidx : S.relIndex T = 2) {t x : G}
    (ht : t ∈ T) (htS : t ∉ S) (hx : x ∈ T) : x ∈ S ∨ t⁻¹ * x ∈ S := by
  classical
  by_cases hxS : x ∈ S
  · exact Or.inl hxS
  right
  have hHi : (S.subgroupOf T).index = 2 := hidx
  have : (S.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hHi
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hHi
  have hX : (⟨x, hx⟩ : ↥T) ∉ S.subgroupOf T := fun h => hxS (Subgroup.mem_subgroupOf.mp h)
  have hY : (⟨t, ht⟩ : ↥T) ∉ S.subgroupOf T := fun h => htS (Subgroup.mem_subgroupOf.mp h)
  have key : ∀ b : ↥T, b ∉ S.subgroupOf T → b * a ∈ S.subgroupOf T := by
    intro b hb
    rcases ha b with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact h1
    · exact absurd h2 hb
  have hz : (⟨t, ht⟩ * a : ↥T)⁻¹ * (⟨x, hx⟩ * a) ∈ S.subgroupOf T :=
    mul_mem (inv_mem (key _ hY)) (key _ hX)
  have hn := (inferInstance : (S.subgroupOf T).Normal).conj_mem _ hz a
  have e : a * ((⟨t, ht⟩ * a : ↥T)⁻¹ * (⟨x, hx⟩ * a)) * a⁻¹ = (⟨t, ht⟩ : ↥T)⁻¹ * ⟨x, hx⟩ := by
    group
  rw [e] at hn
  exact Subgroup.mem_subgroupOf.mp hn

omit [Finite G] in
theorem blockU_ne_bot_of_isLin2Type {L : Subgroup G} {n : ℕ} (h : IsLin2Type L n) :
    blockU L ≠ ⊥ := by
  obtain ⟨F, hF, hFin, hcard, α, -, -, β, hβs, -, -⟩ := h
  intro hbot
  have hsub : ∀ u : ↥(blockU L), u = 1 := fun u => by
    apply Subtype.ext
    have : (u : G) ∈ (⊥ : Subgroup G) := hbot ▸ u.2
    simpa using this
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (fun _ : Fin 2 => (1 : F)))
  rw [hsub u, map_one] at hu
  have h1 : (fun _ : Fin 2 => (1 : F)) = 0 := by
    have := congrArg Multiplicative.toAdd hu
    simpa using this.symm
  exact one_ne_zero (congrFun h1 0)

end Closing

end S153F

end CFSG.Quasithin
