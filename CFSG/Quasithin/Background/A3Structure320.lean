
module

public import CFSG.Quasithin.Background.A3Structure320Core
public import CFSG.Quasithin.Background.A3StructureBasic

public section

namespace CFSG.Quasithin

namespace A320

open CFSG.Open CFSG.SectionRank
open scoped commutatorElement

theorem not_dvd_card_solvRad {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hcommon : A36Common ↥L) (hF : ¬ 3 ∣ Nat.card (CFSG.fittingSubgroup ↥L)) :
    ¬ 3 ∣ Nat.card (solvRad L) := by
  rw [card_solvRad_eq]
  obtain ⟨-, -, halt, -, -⟩ := hcommon
  rcases halt with ⟨-, hrel⟩ | ⟨-, hFR, hcard⟩
  · have h1 := Subgroup.relIndex_mul_card (CFSG.fittingSubgroup ↥L) (CFSG.solvableRadical ↥L)
    rw [hrel] at h1
    intro h3
    rw [← h1] at h3
    have h4 : 3 ∣ Nat.card ↥(CFSG.fittingSubgroup ↥L ⊓ CFSG.solvableRadical ↥L) :=
      (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)
    exact hF (h4.trans (Subgroup.card_dvd_of_le inf_le_left))
  · rw [← hFR]
    rcases hcard with h | h
    · rw [h]
      norm_num
    · rw [h] at hF ⊢
      exact absurd dvd_rfl hF

theorem not_dvd_card_fitting {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : A36Case3 ↥L ∨ A36Case4 ↥L) : ¬ 3 ∣ Nat.card (CFSG.fittingSubgroup ↥L) := by
  rcases h with ⟨p, hp, hp3, -, ⟨e⟩, -⟩ | ⟨-, -, -, hprimes⟩
  · have hcard : Nat.card ↥(CFSG.fittingSubgroup ↥L) = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hcard]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  · intro h3
    have := hprimes 3 Nat.prime_three h3
    omega

theorem radicalShape_of_a36 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : L ∈ cComp (⊤ : Subgroup G)) (hs : A36Strong L) : RadicalShape L := by
  obtain ⟨hconc, hcommon, -⟩ := hs
  rcases hconc with ⟨-, hsimple, -⟩ | ⟨⟨hqs, -⟩, hcard, -⟩ | h3 | h4
  ·
    left
    have hnormal : (CFSG.solvableRadical ↥L).Normal := inferInstance
    have := hsimple
    have hbot : solvRad L = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.solvableRadical ↥L) with h | h
      · rw [← A36A.subgroupOf_solvRad L] at h
        exact (Subgroup.subgroupOf_eq_bot.1 h).eq_bot_of_le (solvRad_le L)
      · rw [← A36A.subgroupOf_solvRad L, Subgroup.subgroupOf_eq_top] at h
        exact absurd ((solvRad_eq_self_iff L).1 (le_antisymm (solvRad_le L) h))
          (not_isSolvable_of_mem_cComp hL)
    rw [hbot]
    simp
  ·
    right
    obtain ⟨-, hsimple, -⟩ := hqs
    have hZsolv : Group.IsSolvable ↥(Subgroup.center ↥L) :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.1 b.2 a)
    have hS : Group.IsSolvable ↥((solvRad L).subgroupOf L) := by
      rw [A36A.subgroupOf_solvRad L]
      exact A3.solvableRadical_isSolvable
    have hsubZ : (solvRad L).subgroupOf L ≤ (Subgroup.center ↥L) := by
      have hn : ((solvRad L).subgroupOf L).Normal := inferInstance
      let q := QuotientGroup.mk' (Subgroup.center ↥L)
      have hqn : (((solvRad L).subgroupOf L).map q).Normal :=
        Subgroup.Normal.map hn q (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
      have := hsimple
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((solvRad L).subgroupOf L).map q) with
        h | h
      · intro s hs
        have h1 : q s ∈ ((solvRad L).subgroupOf L).map q := ⟨s, hs, rfl⟩
        rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
      · exfalso
        have hQ : Group.IsSolvable (↥L ⧸ (Subgroup.center ↥L)) := by
          refine Group.isSolvable_of_surjective
            (f := q.comp ((solvRad L).subgroupOf L).subtype) ?_
          intro x
          have hx : x ∈ ((solvRad L).subgroupOf L).map q := h ▸ Subgroup.mem_top x
          obtain ⟨s, hs, hsx⟩ := hx
          exact ⟨⟨s, hs⟩, hsx⟩
        have hL' : Group.IsSolvable ↥L :=
          Group.isSolvable_of_ker_le_range (Subgroup.center ↥L).subtype q
            (by rw [QuotientGroup.ker_mk', (Subgroup.center ↥L).range_subtype])
        exact not_isSolvable_of_mem_cComp hL hL'
    have hsolv_eq : solvRad L = (Subgroup.center ↥L).map L.subtype := by
      apply le_antisymm
      · intro x hx
        exact ⟨⟨x, solvRad_le L hx⟩, hsubZ (Subgroup.mem_subgroupOf.2 hx), rfl⟩
      · have hRR : ((Subgroup.center ↥L).map L.subtype).subgroupOf L = (Subgroup.center ↥L) :=
          Subgroup.comap_map_eq_self_of_injective L.subtype_injective (Subgroup.center ↥L)
        refine le_solvRad (by rintro _ ⟨z, -, rfl⟩; exact z.2) (by rw [hRR]; infer_instance) ?_
        exact Group.isSolvable_of_surjective
          (f := ((Subgroup.center ↥L).equivMapOfInjective L.subtype
            L.subtype_injective).toMonoidHom)
          ((Subgroup.center ↥L).equivMapOfInjective _ _).surjective
    refine ⟨?_, ?_⟩
    · rw [hsolv_eq]
      exact (Nat.card_congr ((Subgroup.center ↥L).equivMapOfInjective L.subtype
        L.subtype_injective).toEquiv).symm.trans hcard
    · rw [hsolv_eq, eq_bot_iff, Subgroup.commutator_le]
      rintro _ ⟨z, hz, rfl⟩ g hg
      have h1 := Subgroup.mem_center_iff.1 hz ⟨g, hg⟩
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (congrArg Subtype.val h1.symm)
  · exact Or.inl (not_dvd_card_solvRad hcommon (not_dvd_card_fitting (Or.inl h3)))
  · exact Or.inl (not_dvd_card_solvRad hcommon (not_dvd_card_fitting (Or.inr h4)))

theorem isSolvable_pCore_two (H : Type*) [Group H] [Finite H] :
    Group.IsSolvable ↥(CFSG.pCore 2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(CFSG.pCore 2 H) := IsPGroup.isNilpotent CFSG.pCore_isPGroup
  infer_instance

theorem map_solvRad_le {H Q : Type*} [Group H] [Finite H] [Group Q] (π : H →* Q)
    (L : Subgroup H) : (solvRad L).map π ≤ solvRad (L.map π) := by
  refine le_solvRad (Subgroup.map_mono (solvRad_le L)) ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (solvRad_le L))]
    rintro _ _ ⟨r, hr, rfl⟩ ⟨l, hl, rfl⟩
    refine ⟨l * r * l⁻¹, conj_mem_solvRad (Subgroup.le_normalizer hl) hr, ?_⟩
    simp
  · have : Group.IsSolvable ↥(solvRad L) := solvRad_isSolvable L
    exact Group.isSolvable_of_surjective (π.subgroupMap_surjective (solvRad L))

theorem map_centralizerModSolvRad_le {H Q : Type*} [Group H] [Finite H] [Group Q] (π : H →* Q)
    (hπ : Function.Surjective π) (L : Subgroup H) [L.Normal] :
    (centralizerModSolvRad L).map π ≤ centralizerModSolvRad (L.map π) := by
  rintro _ ⟨h, ⟨-, hh⟩, rfl⟩
  have : (L.map π).Normal := Subgroup.Normal.map ‹L.Normal› π hπ
  refine ⟨Subgroup.le_normalizer_of_normal (Subgroup.mem_top _), ?_⟩
  rintro _ ⟨l, hl, rfl⟩
  rw [← map_commutatorElement]
  exact map_solvRad_le π L ⟨_, hh l hl, rfl⟩

end A320

theorem a320_one_of_sqtkHyp {G : Type} [Group G] [Finite G] (hG : SQTKHyp G)
    (h36 : A36Statement G) {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G)) [L.Normal]
    (h3 : 1 ≤ CFSG.Open.pRank 3 L) :
    CFSG.Open.pRank 3 (centralizerModSolvRad L) ≤ 1 :=
  A320.pRank_centralizer_le hL (hG.pRank_le ⊤ Nat.prime_three (by norm_num))
    (A320.radicalShape_of_a36 hL (h36 L hL)) h3

theorem a320_two_of_sqtkHyp {G : Type} [Group G] [Finite G] (hG : SQTKHyp G)
    (h36 : A36Statement G) {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G)) [L.Normal]
    (h2 : CFSG.Open.pRank 3 L = 2) : ¬ HasS3Section (centralizerModSolvRad L) := by
  rintro ⟨K, ρ, hKC, hρ⟩
  exact A320.no_s3_of_centralizer hL (hG.pRank_le ⊤ Nat.prime_three (by norm_num))
    (A320.radicalShape_of_a36 hL (h36 L hL)) h2 K.subtype
    (fun x hx => by
      rw [(MonoidHom.ker_eq_bot_iff _).2 K.subtype_injective, Subgroup.mem_bot] at hx
      rw [hx, orderOf_one]
      norm_num)
    (fun k => hKC k.2) ρ hρ

namespace A320

theorem quotient_setup {H : Type} [Group H] [Finite H] (hH : SQTKGroup H)
    {L : Subgroup H} (hL : L ∈ cComp (⊤ : Subgroup H)) [L.Normal] :
    SQTKHyp (H ⧸ CFSG.pCore 2 H) ∧
      L.map (QuotientGroup.mk' (CFSG.pCore 2 H)) ∈ cComp (⊤ : Subgroup (H ⧸ CFSG.pCore 2 H)) ∧
      (L.map (QuotientGroup.mk' (CFSG.pCore 2 H))).Normal ∧
      IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 H)).ker := by
  refine ⟨SQTKHyp.of_sqtkGroup H hH, ?_, ?_, ?_⟩
  · exact (cComp_quotient_bijOn (CFSG.pCore 2 H) (isSolvable_pCore_two H)).mapsTo hL
  · exact Subgroup.Normal.map ‹L.Normal› _ (QuotientGroup.mk'_surjective _)
  · rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup

end A320

theorem a320_one {H : Type} [Group H] [Finite H] (hH : SQTKGroup H)
    (h36 : A36Statement (H ⧸ CFSG.pCore 2 H)) {L : Subgroup H}
    (hL : L ∈ cComp (⊤ : Subgroup H)) [L.Normal] (h3 : 1 ≤ CFSG.Open.pRank 3 L) :
    CFSG.Open.pRank 3 (centralizerModSolvRad L) ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hGH, hLbar, hLn, hker⟩ := A320.quotient_setup hH hL
  let π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H)
  have h3bar : 1 ≤ CFSG.Open.pRank 3 (L.map π) :=
    h3.trans (A320.pRank_le_pRank_map (by norm_num) π hker L)
  have h1 := a320_one_of_sqtkHyp hGH h36 hLbar h3bar
  calc CFSG.Open.pRank 3 (centralizerModSolvRad L)
      ≤ CFSG.Open.pRank 3 ((centralizerModSolvRad L).map π) :=
        A320.pRank_le_pRank_map (by norm_num) π hker _
    _ ≤ CFSG.Open.pRank 3 (centralizerModSolvRad (L.map π)) :=
        CFSG.SectionRank.pRank_mono (by norm_num)
          (A320.map_centralizerModSolvRad_le π (QuotientGroup.mk'_surjective _) L)
    _ ≤ 1 := h1

theorem a320_two {H : Type} [Group H] [Finite H] (hH : SQTKGroup H)
    (h36 : A36Statement (H ⧸ CFSG.pCore 2 H)) {L : Subgroup H}
    (hL : L ∈ cComp (⊤ : Subgroup H)) [L.Normal] (h2 : CFSG.Open.pRank 3 L = 2) :
    ¬ HasS3Section (centralizerModSolvRad L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hGH, hLbar, hLn, hker⟩ := A320.quotient_setup hH hL
  let π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H)
  have hL2bar : CFSG.Open.pRank 3 (L.map π) = 2 := by
    have h1 := A320.pRank_le_pRank_map (p := 3) (by norm_num) π hker L
    have h2' := hGH.pRank_le (L.map π) Nat.prime_three (by norm_num)
    omega
  rintro ⟨K, ρ, hKC, hρ⟩
  refine A320.no_s3_of_centralizer hLbar (hGH.pRank_le ⊤ Nat.prime_three (by norm_num))
    (A320.radicalShape_of_a36 hLbar (h36 _ hLbar)) hL2bar (π.comp K.subtype) ?_ ?_ ρ hρ
  · intro x hx h3d
    have hxN : (x : H) ∈ CFSG.pCore 2 H := (QuotientGroup.eq_one_iff _).1 hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 (CFSG.pCore_isPGroup (G := H) (p := 2))
      ⟨x, hxN⟩
    have hk' : orderOf x = 2 ^ k := by
      rw [← Subgroup.orderOf_coe x]
      exact (Subgroup.orderOf_coe (⟨x, hxN⟩ : ↥(CFSG.pCore 2 H))).trans hk
    rw [hk'] at h3d
    have := Nat.prime_three.dvd_of_dvd_pow h3d
    omega
  · intro k
    exact A320.map_centralizerModSolvRad_le π (QuotientGroup.mk'_surjective _) L
      ⟨k, hKC k.2, rfl⟩

end CFSG.Quasithin
