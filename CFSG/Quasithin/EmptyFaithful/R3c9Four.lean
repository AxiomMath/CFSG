module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L33

public section

namespace CFSG.Quasithin.R3c9

open CFSG.Open CFSG.QuasithinUnique

@[expose] def FourSelfCentTwo (X : Type) [Group X] : Prop :=
  ∀ V : Subgroup X, Nat.card V = 4 → (∀ v ∈ V, v ^ 2 = 1) → (∀ u ∈ V, ∀ v ∈ V, u * v = v * u) →
    ∀ c : X, (∀ v ∈ V, c * v = v * c) → (∃ k : ℕ, orderOf c = 2 ^ k) → c ∈ V

theorem FourSelfCentTwo.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : FourSelfCentTwo X) : FourSelfCentTwo Y := by
  intro V hV4 hV2 hVc c hc hco
  have h4 : Nat.card (V.map e.symm.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hV4
  have hsq : ∀ v ∈ V.map e.symm.toMonoidHom, v ^ 2 = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    show e.symm w ^ 2 = 1
    rw [← map_pow, hV2 w hw, map_one]
  have hcomm : ∀ u ∈ V.map e.symm.toMonoidHom, ∀ v ∈ V.map e.symm.toMonoidHom, u * v = v * u := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show e.symm a * e.symm b = e.symm b * e.symm a
    rw [← map_mul, ← map_mul, hVc a ha b hb]
  have hcent : ∀ v ∈ V.map e.symm.toMonoidHom, e.symm c * v = v * e.symm c := by
    rintro _ ⟨a, ha, rfl⟩
    show e.symm c * e.symm a = e.symm a * e.symm c
    rw [← map_mul, ← map_mul, hc a ha]
  have hord : ∃ k : ℕ, orderOf (e.symm c) = 2 ^ k := by
    obtain ⟨k, hk⟩ := hco
    exact ⟨k, by rw [MulEquiv.orderOf_eq]; exact hk⟩
  obtain ⟨w, hw, hwc⟩ := Subgroup.mem_map.mp (h _ h4 hsq hcomm _ hcent hord)
  have : w = c := e.symm.injective hwc
  rw [← this]
  exact hw

theorem fourSelfCentTwo_psl2
    {K : Type} [Field K] [Finite K] (hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K)) :
    FourSelfCentTwo (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  intro V hV4 hV2 hVc c hc _
  have hVK : IsKleinFour V := by
    refine ⟨hV4, ?_⟩
    have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV4]; norm_num)
    have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV4]; norm_num)
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    exact orderOf_eq_prime (Subtype.ext (by simpa [sq] using hV2 g g.2)) hg
  let toPGL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K →* CFSG.GorensteinWalter.PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hVP : IsKleinFour (V.map toPGL) :=
    CFSG.GorensteinWalter.isKleinFour_map_of_injective V hVK toPGL htoPGL
  have hcent := CFSG.GorensteinWalter.pgl2_kleinFour_centralizer_eq_self K hK _ hVP
  have hgC : toPGL c ∈ Subgroup.centralizer ((V.map toPGL : Subgroup (CFSG.GorensteinWalter.PGL2 K)) :
      Set (CFSG.GorensteinWalter.PGL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    simp only [← map_mul]
    exact congrArg toPGL (hc v hv).symm
  rw [hcent] at hgC
  obtain ⟨v, hv, hvg⟩ := hgC
  rw [← htoPGL hvg]
  exact hv

theorem fourSelfCentTwo_of_isPSL_two
    {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hodd : Odd p) (h : StatedClassicalModel X .PSL 2 p 1) :
    FourSelfCentTwo X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Finite K := inferInstance
  have hodd' : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp, hodd, le_rfl, hK⟩
  exact FourSelfCentTwo.of_mulEquiv
    ((e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).symm)
    (fourSelfCentTwo_psl2 hodd')


theorem fourSelfCentTwo_l33
    {X : Type} [Group X] (h : StatedClassicalModel X .PSL 3 3 1) : FourSelfCentTwo X := by
  obtain ⟨e₀⟩ := Unc25K1.psl33_equiv h
  let e : X ≃* Unc25K1.S3 := e₀.trans Unc25K1.psl33EquivS3
  refine FourSelfCentTwo.of_mulEquiv e.symm ?_
  intro F hF4 hF2 hFc c hc _
  have hF : IsFourSubgroup F :=
    ⟨⟨⟨⟨fun a b => Subtype.ext (hFc a a.2 b b.2)⟩⟩, fun x hx => hF2 x hx⟩, hF4⟩
  have hC := Unc25L33.sylowFourData_P0.centralizer_four hF
  rw [← hC]
  exact Subgroup.mem_centralizer_iff.mpr fun v hv => (hc v hv).symm

end CFSG.Quasithin.R3c9
