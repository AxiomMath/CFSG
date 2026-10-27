module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1BA
public import CFSG.Quasithin.Background.C126NatDProd
public import CFSG.Quasithin.Background.GoldschmidtC24EightAlt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl4_bf_sylow_join {X L L' T : Subgroup (MulAut W)}
    (F : s16h_SL4TwoFrame X L L' T) :
    IsSylowTwoOf (T ⊓ (L ⊔ L')) (L ⊔ L') := by
  have hTX : IsSylowTwoOf T X := ⟨F.t_le, F.t_two, F.t_syl⟩
  have hN : X ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmap : (L ⊔ L').map (MulAut.conj x).toMonoidHom = L ⊔ L' := by
      rw [Subgroup.map_sup]
      rcases F.perm x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, sup_comm]
    simpa only [MulEquiv.toMonoidHom_eq_coe] using hmap
  exact CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hTX (sup_le F.le_x F.le_x') hN

theorem s16h_sl4_bf_sylow_inf {X L L' T : Subgroup (MulAut W)}
    (F : s16h_SL4TwoFrame X L L' T) :
    IsSylowTwoOf (T ⊓ L) L ∧ IsSylowTwoOf (T ⊓ L') L' := by
  have hS := s16h_sl4_bf_sylow_join F
  constructor
  · have h := CFSG.Quasithin.C126.Nat.isSylowTwoOf_inf_left (L₁ := L) (L₂ := L') F.comm hS
    rwa [inf_assoc, show (L ⊔ L') ⊓ L = L by rw [inf_comm,
      inf_eq_left.mpr le_sup_left]] at h
  · have h := CFSG.Quasithin.C126.Nat.isSylowTwoOf_inf_right (L₁ := L) (L₂ := L') F.comm hS
    rwa [inf_assoc, show (L ⊔ L') ⊓ L' = L' by rw [inf_comm,
      inf_eq_left.mpr le_sup_right]] at h

theorem s16h_sl4_bf_inf_eq_bot {X L L' T : Subgroup (MulAut W)}
    (F : s16h_SL4TwoFrame X L L' T) (hL : IsAlt ↥L 5) (hLL' : L ≠ L') :
    L ⊓ L' = ⊥ := by
  obtain ⟨e⟩ := hL
  haveI : IsSimpleGroup ↥L := e.isSimpleGroup
  have hcardLL' : Nat.card ↥L' = Nat.card ↥L := by
    obtain ⟨t, -, htL⟩ := F.swap
    rw [← htL, Subgroup.card_map_of_injective (MulAut.conj t).injective]
  have hLnorm : L ≤ Subgroup.normalizer ((L ⊓ L') : Set (MulAut W)) := by
    refine (show L ≤ Subgroup.centralizer ((L ⊓ L') : Set (MulAut W)) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (F.comm a ha y hy.2).symm
  have hnorm : ((L ⊓ L').subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hLnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ L').subgroupOf L) with hbot | htop
  · rw [Subgroup.subgroupOf_eq_bot] at hbot
    rw [disjoint_iff] at hbot
    simpa [inf_of_le_left inf_le_left] using hbot
  · exfalso
    have hle : L ≤ L' := (Subgroup.subgroupOf_eq_top.1 htop).trans inf_le_right
    exact hLL' (Subgroup.eq_of_le_of_card_ge hle hcardLL'.le)

theorem s16h_sl4_bf_inf_sup_eq {X L L' T : Subgroup (MulAut W)}
    (F : s16h_SL4TwoFrame X L L' T) (hL : IsAlt ↥L 5) (hLL' : L ≠ L') :
    T ⊓ (L ⊔ L') = (T ⊓ L) ⊔ (T ⊓ L') := by
  have hdisj := s16h_sl4_bf_inf_eq_bot F hL hLL'
  have hS := s16h_sl4_bf_sylow_join F
  have h := CFSG.Quasithin.C126.Nat.eq_sup_inf_of_commuting (L₁ := L) (L₂ := L')
    F.comm hdisj hS
  have h1 : (T ⊓ (L ⊔ L')) ⊓ L = T ⊓ L := by
    rw [inf_assoc, show (L ⊔ L') ⊓ L = L by rw [inf_comm, inf_eq_left.mpr le_sup_left]]
  have h2 : (T ⊓ (L ⊔ L')) ⊓ L' = T ⊓ L' := by
    rw [inf_assoc, show (L ⊔ L') ⊓ L' = L' by rw [inf_comm, inf_eq_left.mpr le_sup_right]]
  rw [h1, h2] at h
  exact h

theorem s16h_sl4_bf_exists_order_three {X : Type} [Group X] [Finite X]
    {H S : Subgroup X} (e : ↥H ≃* alternatingGroup (Fin 5))
    (hS : IsSylowTwoOf S H) :
    ∃ b ∈ H, b ^ 3 = 1 ∧ b ≠ 1 ∧ b ∈ Subgroup.normalizer (S : Set X) := by
  have hP : IsPGroup 2 (S.subgroupOf H) :=
    CFSG.Quasithin.A4.isPGroup_subgroupOf_of_le hS.1 hS.2.1
  have hi : ¬ 2 ∣ (S.subgroupOf H).index := hS.2.2
  have hP' : IsPGroup 2 ((S.subgroupOf H).map e.toMonoidHom) := hP.map e.toMonoidHom
  have hi' : ¬ 2 ∣ ((S.subgroupOf H).map e.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective e.bijective]
    exact hi
  obtain ⟨y, hyN, hy3, hy1⟩ :=
    CFSG.Quasithin.C24Eight.A5Sylow.exists_normalizer_order_three
      ((S.subgroupOf H).map e.toMonoidHom) hP' hi'
  have hmapN : (Subgroup.normalizer ((S.subgroupOf H : Subgroup ↥H) : Set ↥H)).map
      e.toMonoidHom =
      Subgroup.normalizer (((S.subgroupOf H).map e.toMonoidHom :
        Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5))) :=
    Subgroup.map_normalizer_eq_of_bijective (S.subgroupOf H) e.bijective
  have hyN' : y ∈ (Subgroup.normalizer ((S.subgroupOf H : Subgroup ↥H) : Set ↥H)).map
      e.toMonoidHom := by
    rw [hmapN]
    exact hyN
  obtain ⟨z, hzN, hzy⟩ := hyN'
  have hz3 : z ^ 3 = 1 := by
    apply e.injective
    show e.toMonoidHom (z ^ 3) = e.toMonoidHom 1
    rw [map_pow, hzy, hy3, map_one]
  refine ⟨(z : X), z.2, ?_, ?_, ?_⟩
  · simpa using congrArg (fun w : ↥H => (w : X)) hz3
  · intro hb
    apply hy1
    have hz1 : z = 1 := Subtype.ext hb
    rw [← hzy, hz1, map_one]
  · have hzN' : z ∈ (Subgroup.normalizer (S : Set X)).subgroupOf H := by
      rw [Subgroup.subgroupOf_normalizer_eq hS.1]
      exact hzN
    exact hzN'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
