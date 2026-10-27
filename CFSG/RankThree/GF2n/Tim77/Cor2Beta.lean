module

public import CFSG.RankThree.GF2n.Tim77.Cor2BetaPack
public import CFSG.RankThree.GF2n.Tim77.Cor2BetaCentral
public import CFSG.RankThree.GF2n.Tim77.Cor2BetaStmts
public import CFSG.RankThree.GF2n.Tim77.Defs

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions CFSG.Open Subgroup
open CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups

theorem cor2Beta_shult_inner_of {G : Type} [Group G] [Finite G]
    (hC3 : Cor2BetaInnerOnComponentStatement)
    {S : Sylow 2 G} {t : G} (hs : ShultSetup S t) {E Y : Subgroup G}
    (hd : Cor2BetaDecomp (normalClosure ({t} : Set G)) E Y) {a : G} (ha2 : a * a = 1)
    (haH : a ∈ normalizer (normalClosure ({t} : Set G) : Set G))
    (hac : ∀ w ∈ CFSG.LargeExtraspecial.S11.wcl t, a * w = w * a)
    (hstar : ∀ g : G, a * (g * t * g⁻¹) = (g * t * g⁻¹) * a →
      g * t * g⁻¹ ∈ CFSG.LargeExtraspecial.S11.wcl t) :
    ∃ e ∈ E, ∀ x ∈ E, a * x * a⁻¹ = e * x * e⁻¹ :=
  cor2Beta_inner_on_layer_of_components hd.E_eq fun _ hK =>
    hC3 G hs hd ha2 haH hac hstar hK

theorem cor2Beta_of_rootType_of
    (hB7 : Cor2BetaShultDecompStatement) (hC3 : Cor2BetaInnerOnComponentStatement)
    {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hTI : IsTI A) (hroot : IsRootType 2 A) (hW : ⁅WAC A, WAC A⁆ = ⊥)
    (hSyl : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.normalizer (A : Set G)) :
    ∃ (r : ℕ) (X : Fin r → Subgroup ↥(Subgroup.normalClosure (A : Set G))),
      (∀ i, (X i).Normal) ∧ (∀ i j, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j, x * y = y * x) ∧
      ⨆ i, X i = ⊤ ∧
      ∀ i, IsCoveringOf Tim77Cor2BetaList ↥(X i) ∨ HasNormalTwoComplement ↥(X i) := by
  classical
  refine cor2Beta_shape_target ?_
  by_cases hA1 : A = ⊥
  · subst hA1
    have h0 : normalClosure (((⊥ : Subgroup G) : Subgroup G) : Set G) = ⊥ :=
      le_antisymm (normalClosure_le_normal (fun x hx => hx)) bot_le
    rw [h0]
    refine ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_,
      fun i => i.elim0⟩
    simp
  obtain ⟨S, hS⟩ := hSyl
  obtain ⟨t, htA, ht1, htS, htc⟩ := cor2Beta_exists_central_mem hA hA1 S hS
  have ht2 : t * t = 1 := by
    have := hA.2 t htA
    rwa [sq] at this
  have hs : ShultSetup S t := ⟨ht1, ht2, htS, htc, cor2Beta_isMulCommutative_wcl hroot hW htA ht1⟩
  obtain ⟨E, Y, hd⟩ := hB7 G hs
  have hHn : (normalClosure ({t} : Set G)).Normal := inferInstance
  have htH : t ∈ normalClosure ({t} : Set G) := subset_normalClosure (Set.mem_singleton t)
  have hHG : normalClosure ({t} : Set G) ≤ normalClosure (A : Set G) :=
    normalClosure_mono (Set.singleton_subset_iff.mpr htA)
  by_cases hab : IsMulCommutative ↥(normalClosure (A : Set G))
  · exact cor2Beta_shape_of_abelian hA hab
  by_cases hAH : A ≤ normalClosure ({t} : Set G)
  · have hGH : normalClosure (A : Set G) = normalClosure ({t} : Set G) ⊔ ⊥ := by
      rw [sup_bot_eq]
      exact le_antisymm (normalClosure_le_normal hAH) hHG
    exact cor2Beta_shape_of_decomp_mul hd (Q := ⊥)
      (fun q hq h _ => by rw [Subgroup.mem_bot.mp hq]; simp) hGH cor2Beta_hasNormalTwoComplement_bot
  · obtain ⟨a₀, ha₀A, ha₀H⟩ := Set.not_subset.mp hAH
    have ha₀t : a₀ ∉ Subgroup.zpowers t := fun h => ha₀H ((Subgroup.zpowers_le.mpr htH) h)
    have h4 := cor2Beta_four_le_card hA htA ht1 ha₀A ha₀t
    have hO : ∀ N : Subgroup G, N.Normal → N ≤ normalClosure ({t} : Set G) →
        Odd (Nat.card N) → ∀ n ∈ N, ∀ h ∈ normalClosure ({t} : Set G), n * h = h * n :=
      fun N hN _ hodd n hn h hh => cor2Beta_oddNormal_commute hA hTI h4 hodd n hn h (hHG hh)
    have hY := cor2Beta_decomp_Y_commute hs hd hO
    have hinner : ∀ a ∈ A, ∃ h ∈ normalClosure ({t} : Set G),
        ∃ c ∈ centralizer (normalClosure ({t} : Set G) : Set G), a = h * c := by
      intro a haA
      have ha2 : a * a = 1 := by
        have := hA.2 a haA
        rwa [sq] at this
      have haN : a ∈ normalizer (normalClosure ({t} : Set G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        exact ⟨fun hh => hHn.conj_mem h hh a, fun hh => by
          have := hHn.conj_mem _ hh a⁻¹
          simpa [mul_assoc] using this⟩
      have hac : ∀ w ∈ CFSG.LargeExtraspecial.S11.wcl t, a * w = w * a :=
        fun w hw => cor2Beta_wcl_commute hroot htA ht1 w hw a haA
      by_cases ha1 : a = 1
      · exact ⟨1, one_mem _, 1, one_mem _, by simp [ha1]⟩
      have hstar : ∀ g : G, a * (g * t * g⁻¹) = (g * t * g⁻¹) * a →
          g * t * g⁻¹ ∈ CFSG.LargeExtraspecial.S11.wcl t :=
        fun g h => cor2Beta_mem_wcl_of_commute hroot htA ht1 haA ha1 g h
      obtain ⟨e, heE, he⟩ := cor2Beta_shult_inner_of hC3 hs hd ha2 haN hac hstar
      refine ⟨e, hd.E_le heE, e⁻¹ * a, ?_, by group⟩
      have hcE : ∀ x ∈ E, x * (e⁻¹ * a) = (e⁻¹ * a) * x := by
        intro x hx
        have h1 := he x hx
        calc x * (e⁻¹ * a) = e⁻¹ * (e * x * e⁻¹) * a := by group
          _ = e⁻¹ * (a * x * a⁻¹) * a := by rw [h1]
          _ = (e⁻¹ * a) * x := by group
      have hcY : ∀ y ∈ Y, y * (e⁻¹ * a) = (e⁻¹ * a) * y := by
        intro y hy
        have hya : a * y = y * a :=
          cor2Beta_commute_of_centralizes hTI hroot htA ht1 hab (hY y hy) a haA
        have hey : e⁻¹ * y = y * e⁻¹ := by
          have := hd.comm e heE y hy
          calc e⁻¹ * y = e⁻¹ * (y * e) * e⁻¹ := by group
            _ = e⁻¹ * (e * y) * e⁻¹ := by rw [this]
            _ = y * e⁻¹ := by group
        calc y * (e⁻¹ * a) = (y * e⁻¹) * a := by group
          _ = (e⁻¹ * y) * a := by rw [hey]
          _ = e⁻¹ * (y * a) := by group
          _ = e⁻¹ * (a * y) := by rw [hya]
          _ = (e⁻¹ * a) * y := by group
      have hsub : E ⊔ Y ≤ Subgroup.centralizer ({e⁻¹ * a} : Set G) :=
        sup_le (fun x hx => by
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact hcE x hx)
          (fun y hy => by
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact hcY y hy)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h' := hsub (hd.sup_eq ▸ hh)
      rw [Subgroup.mem_centralizer_singleton_iff] at h'
      exact h'
    obtain ⟨Q, hGQ, hQc, hQab⟩ := cor2Beta_exists_complement hTI hroot htA ht1 hab hinner
    haveI := hQab
    exact cor2Beta_shape_of_decomp_mul hd hQc hGQ cor2Beta_hasNormalTwoComplement_of_comm

theorem tim77BetaBox_of_nodes (hB7 : Cor2BetaShultDecompStatement)
    (hC3 : Cor2BetaInnerOnComponentStatement) : Tim77BetaBox :=
  fun _ _ _ _ hA hTI hroot hW hSyl => cor2Beta_of_rootType_of hB7 hC3 hA hTI hroot hW hSyl

end CFSG.RankThree.GF2n.Tim77
