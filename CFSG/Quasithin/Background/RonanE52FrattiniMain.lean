module

public import CFSG.Quasithin.Background.RonanE52Frattini
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.RonanE52

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_sup_thompsonJi {P C : Subgroup G} (hP : IsSylowIn 2 P ⊤) {i : ℕ}
    (hi : i < CFSG.Open.pRank 2 P) (hJC : thompsonJi P i ≤ C) :
    C ≤ Subgroup.normalizer (thompsonJi P i : Set G) ⊔ thompsonJi C i := by
  have hP2 : IsSylowTwoOf P ⊤ := hP
  have hbr : ∀ (g : G) (X : Subgroup G), B6.conjSub g X = cjSub g X := fun g X =>
    Subgroup.ext fun x => B6.mem_conjSub.trans mem_cjSub.symm
  have hconj : ∀ (g : G) (X : Subgroup G),
      B6.conjSub g (thompsonJi X i) = thompsonJi (B6.conjSub g X) i := by
    intro g X
    rw [hbr, hbr]
    exact cjSub_thompsonJi g X i
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian P
  have hA₀c : IsElemAbelianCorank P 0 A₀ := isMaxElemAbelian_iff_corank_zero.mp hA₀
  have hA₀J : A₀ ≤ thompsonJi P i :=
    (le_iSup₂_of_le A₀ hA₀c le_rfl : A₀ ≤ thompsonJi P 0).trans
      (thompsonJi_mono (Nat.zero_le i) hi)
  have hrank : ∀ {X : Subgroup G}, thompsonJi P i ≤ X →
      CFSG.Open.pRank 2 X = CFSG.Open.pRank 2 P := by
    intro X hX
    refine le_antisymm ?_ ?_
    · exact (CFSG.SectionRank.pRank_mono one_lt_two (le_top : X ≤ ⊤)).trans
        (pRank_eq_top_of_isSylow hP).ge
    · refine CFSG.SectionRank.le_pRank one_lt_two (hA₀J.trans hX) hA₀c.2.1 ?_
      have h := hA₀c.2.2
      rw [pow_zero, mul_one] at h
      exact h
  have hJX : ∀ {X : Subgroup G}, thompsonJi P i ≤ X → thompsonJi P i ≤ thompsonJi X i := by
    intro X hX
    refine iSup₂_le fun A hA => ?_
    have hAJ : A ≤ thompsonJi P i := le_iSup₂_of_le A hA le_rfl
    have hAX : IsElemAbelianCorank X i A :=
      ⟨hAJ.trans hX, hA.2.1, by rw [hrank hX]; exact hA.2.2⟩
    exact le_iSup₂_of_le A hAX le_rfl
  have hJP : thompsonJi P i ≤ P := iSup_le fun _ => iSup_le fun hA => hA.1
  obtain ⟨S, hS, hJS⟩ := A4.exists_isSylowTwoOf_ge (hJX hJC) (hP2.2.1.to_le hJP)
  have hJS' : thompsonJi S i = thompsonJi P i := by
    obtain ⟨R, hR, hSR⟩ := A4.exists_isSylowTwoOf_ge (le_top : S ≤ ⊤) hS.2.1
    obtain ⟨g, -, hRg⟩ := B6.isSylowTwoOf_exists_conj hP2 hR
    have hpS : CFSG.Open.pRank 2 S = CFSG.Open.pRank 2 R :=
      (hrank hJS).trans (hrank (hJS.trans hSR)).symm
    have h2 : thompsonJi S i ≤ thompsonJi R i := thompsonJi_le_thompsonJi_of_pRank_eq hSR hpS i
    have h3 : Nat.card (thompsonJi R i) = Nat.card (thompsonJi P i) := by
      rw [hRg, ← hconj, B6.card_conjSub]
    exact (Subgroup.eq_of_le_of_card_ge (hJX hJS)
      ((Subgroup.card_le_of_le h2).trans h3.le)).symm
  intro c hc
  have hcC : cjSub c C = C := B2F.cjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hc)
  have hcJ : cjSub c (thompsonJi C i) = thompsonJi C i := by
    rw [cjSub_thompsonJi, hcC]
  have hcN : c ∈ Subgroup.normalizer (thompsonJi C i : Set G) :=
    B2F.mem_normalizer_iff_cjSub_eq.mpr hcJ
  have hS' : IsSylowTwoOf (B6.conjSub c S) (thompsonJi C i) := by
    have := B6.isSylowTwoOf_conjSub hS c
    rwa [B6.conjSub_eq_self hcN] at this
  obtain ⟨y, hy, hyS⟩ := B6.isSylowTwoOf_exists_conj hS hS'
  have key : B6.conjSub (y⁻¹ * c) (thompsonJi P i) = thompsonJi P i := by
    rw [← hJS', B6.conjSub_mul, hconj, hyS, ← hconj, ← B6.conjSub_mul, inv_mul_cancel,
      B6.conjSub_one]
  have hn : y⁻¹ * c ∈ Subgroup.normalizer (thompsonJi P i : Set G) :=
    B2F.mem_normalizer_iff_cjSub_eq.mpr ((hbr _ _).symm.trans key)
  have e : c = y * (y⁻¹ * c) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left hn)

end CFSG.Quasithin.RonanE52
