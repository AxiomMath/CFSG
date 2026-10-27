module

public import CFSG.Quasithin.Vol2.GoldschmidtE217B1L27
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Red
public import CFSG.GH74.E2.K0Simple
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M E217R3

namespace E217R4

theorem l27_ambient
    {X : Type} [Group X] {K S : Subgroup X} (hK : CFSG.GH74.E2.ShapeL27 ↥K)
    (hS : IsSylowTwoOf S K) :
    Nat.card K = 168 ∧ Nat.card S = 8 ∧ K ⊓ Subgroup.normalizer (S : Set X) = S ∧
      ∃ z ∈ S, z * z = 1 ∧ z ≠ 1 ∧ (∀ s ∈ S, z * s = s * z) ∧
        ∀ g ∈ K, g * z = z * g → g ∈ S := by
  obtain ⟨hSK, hS2, hSi⟩ := hS
  obtain ⟨hK168, hcard, hnorm, z, hz, hz2, hz1, hzc, hzN⟩ := l27_table hK (S.subgroupOf K)
    hS2.comap_subtype hSi
  refine ⟨hK168, ?_, ?_, (z : X), hz, ?_, fun h => hz1 (Subtype.ext h), fun s hs => ?_,
    fun g hg hc => ?_⟩
  · rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).symm.toEquiv
  · refine le_antisymm (fun g ⟨hgK, hgN⟩ => ?_) (le_inf hSK Subgroup.le_normalizer)
    have := hnorm ⟨g, hgK⟩ fun s hs => ?_
    · exact this
    · exact (Subgroup.mem_normalizer_iff.1 hgN _).1 hs
  · exact congrArg Subtype.val hz2
  · exact congrArg Subtype.val (hzc ⟨s, hSK hs⟩ hs)
  · exact hzN ⟨g, hg⟩ (Subtype.ext hc)

theorem exists_maxParabolic2 {X : Type} [Group X] [Finite X] {K S : Subgroup X}
    (hS : IsSylowTwoOf S K) (hne : K ⊓ Subgroup.normalizer (S : Set X) ≠ K) :
    ∃ P : Subgroup X, IsMaxParabolic2 K P ∧ K ⊓ Subgroup.normalizer (S : Set X) ≤ P := by
  set B := K ⊓ Subgroup.normalizer (S : Set X) with hB
  obtain ⟨P, ⟨⟨hPpar, hPK, hBP⟩, hPmax⟩⟩ := WellFounded.has_min
    (wellFounded_gt (α := Subgroup X))
    {Q : Subgroup X | IsParabolic2 K Q ∧ Q ≠ K ∧ B ≤ Q}
    ⟨B, ⟨inf_le_left, S, hS, le_rfl⟩, hne, le_rfl⟩
  refine ⟨P, ⟨hPpar, hPK, fun Q hQ hQK hPQ => ?_⟩, hBP⟩
  by_contra hne'
  exact hPmax Q ⟨hQ, hQK, hBP.trans hPQ⟩ (lt_of_le_of_ne hPQ (Ne.symm hne'))

theorem not_le_of_diag {X : Type} [Group X] [Finite X] {K T : Subgroup X}
    (hS : IsSylowTwoOf (T ⊓ K) K) (hne : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) ≠ K)
    (hdiag : ∀ P : Subgroup X, IsMaxParabolic2 K P →
      K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) ≤ P →
      ¬ T ≤ Subgroup.normalizer (P : Set X)) : ¬ T ≤ K := by
  intro hTK
  obtain ⟨P, hP, hBP⟩ := exists_maxParabolic2 hS hne
  refine hdiag P hP hBP ?_
  have hTS : T ⊓ K = T := inf_eq_left.2 hTK
  rw [hTS] at hBP
  exact (le_inf hTK Subgroup.le_normalizer).trans (hBP.trans Subgroup.le_normalizer)

theorem r3Pkg2bOne_L32
    (p7 : R3Pkg2c7) {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}
    (hS : Setting2 H T M V K) (hlt : (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8)
    (hC2 : Case2 H T M K) (hL32 : IsPSL 3 2 1 ↥(E2.star M H K))
    (hdiag : E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)))
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) : False := by
  have hmp := hS.toHyp2.hyp.minParabolic
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hLie3 : CFSG.Blueprint.LieModel ↥(E2.star M H K) .PSL 3 2 1 := by
    unfold CFSG.Blueprint.LieModel
    exact Or.inl ⟨by decide, hL32⟩
  have hshape : CFSG.GH74.E2.ShapeL27 ↥(E2.star M H K) := Or.inr hLie3
  have hpsl7 : IsPSL 2 7 1 ↥(E2.star M H K) := by
    rcases CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism _ hLie3 with
      ⟨-, h7⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h7
    all_goals exact absurd h0 (by norm_num)
  have hfacts := CFSG.GH74.E2.ShapeL27.facts hshape
  have hsimp : IsSimpleGroup ↥(E2.star M H K) := hfacts.1
  have hZ : Subgroup.center ↥(E2.star M H K) = ⊥ := by
    have := hfacts.1
    exact CFSG.GH74.E2.center_eq_bot_of_simple_of_not_prime hfacts.2.2
  have hX := asHyp_star' hmp hS.mem_cComp hS.eq_sup hC2 hsimp hZ
    (nonab_star' (M := M) hS.mem_cComp)
  have hTK : E2.star M H (T ⊓ K) = E2.star M H T ⊓ E2.star M H K :=
    E2P.star_inf_T hmp.isSylow hS.mem_cComp.2.2.1 hKH
  have hMK' : E2.star M H (M ⊓ K) = E2.star M H M ⊓ E2.star M H K := E2P.star_inf_M K
  have hStarTM : E2.star M H T ≤ E2.star M H M :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hmp.le)
  have hSsyl : IsSylowTwoOf (E2.star M H T ⊓ E2.star M H K) (E2.star M H K) :=
    B6.isSylowTwoOf_inf_normal hX.minPar.isSylow le_top
      (Subgroup.normalizer_eq_top_iff.2 hX.normal).ge
  obtain ⟨hK168, hc8, hNS, z, hzS, hz2, hz1, hzc, hzK⟩ := l27_ambient hshape hSsyl
  obtain ⟨S', hS'syl, hBS'⟩ := hB
  obtain ⟨-, hc8', hNS', -⟩ := l27_ambient hshape hS'syl
  have hB' : E2.star M H (M ⊓ K) = S' := by rw [hBS']; exact hNS'
  have hSB : E2.star M H T ⊓ E2.star M H K ≤ E2.star M H (M ⊓ K) := by
    rw [hMK']
    exact inf_le_inf_right _ hStarTM
  have hSS' : E2.star M H T ⊓ E2.star M H K = S' :=
    Subgroup.eq_of_le_of_card_ge (hB' ▸ hSB) (by rw [hc8, hc8'])
  have hMK : E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) := by
    rw [hB', ← hSS']
    have hzmem : z ∈ zStar H T M K := by
      rw [zStar, hTK]
      exact ⟨hzS, Subgroup.mem_centralizer_iff.2 fun s hs => (hzc s hs).symm⟩
    apply le_antisymm
    · intro x hx
      refine ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      have hy' : y ∈ Subgroup.centralizer ((E2.star M H T ⊓ E2.star M H K : Subgroup _) :
          Set (E2.StarQuot M H)) := by
        have := hy.2
        rwa [hTK] at this
      exact (Subgroup.mem_centralizer_iff.1 hy' x hx).symm
    · rintro x ⟨hxK, hxC⟩
      exact hzK x hxK ((Subgroup.mem_centralizer_iff.1 hxC z hzmem).symm)
  have hdiag' : ∀ P : Subgroup (E2.StarQuot M H), IsMaxParabolic2 (E2.star M H K) P →
      E2.star M H K ⊓ Subgroup.normalizer
        ((E2.star M H T ⊓ E2.star M H K : Subgroup (E2.StarQuot M H)) : Set (E2.StarQuot M H)) ≤ P →
      ¬ E2.star M H T ≤ Subgroup.normalizer (P : Set (E2.StarQuot M H)) :=
    fun P hP hle => hdiag P hP (by rw [hTK]; exact hle)
  have hne : E2.star M H K ⊓ Subgroup.normalizer
      ((E2.star M H T ⊓ E2.star M H K : Subgroup (E2.StarQuot M H)) : Set (E2.StarQuot M H)) ≠
      E2.star M H K := fun h => by
    rw [hNS] at h
    have h1 : Nat.card ↥(E2.star M H T ⊓ E2.star M H K : Subgroup (E2.StarQuot M H)) =
        Nat.card ↥(E2.star M H K) := by rw [h]
    omega
  have hnotle := not_le_of_diag hSsyl hne hdiag'
  have hbig : 8 < Nat.card (E2.star M H T) := by
    have h1 : Nat.card (E2.star M H T ⊓ E2.star M H K : Subgroup _) ≤ Nat.card (E2.star M H T) :=
      Subgroup.card_le_of_le inf_le_left
    by_contra hcon
    have h2 : Nat.card (E2.star M H T) = 8 := by omega
    have : E2.star M H T ⊓ E2.star M H K = E2.star M H T :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact hnotle (this ▸ inf_le_right)
  have haut : 8 < E2.autCard (E2.star M H T) (E2.star M H K) := by
    have : E2.autCard (E2.star M H T) (E2.star M H K) = Nat.card (E2.star M H T) := by
      unfold E2.autCard
      rw [Subgroup.normalizer_eq_top_iff.2 hX.normal, hX.cent]
      simp [Subgroup.relIndex_bot_left]
    rw [this]
    exact hbig
  exact p7 G H T M V K hS hlt hC2 hpsl7 hMK haut

end E217R4

end CFSG.Quasithin
