module

public import CFSG.Milestones.ASVolI.A3Aut.SmallBase
public import CFSG.Milestones.ASVolI.A3Aut.SmallD4Inner
public import CFSG.Milestones.ASVolI.A3Aut.SmallD4Core

public section

namespace CFSG.ASVolI

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

theorem burnsideAut_a315_3D4two :
    ∀ (G : Type) [Group G] (L T B : Subgroup G), CFSG.Quasithin.A315Hyp L T B →
      CFSG.Quasithin.Is3D4 2 1 ↥L → CFSG.Quasithin.A315Case6 L T B := by
  intro G _ L T B h hL
  haveI : Finite G := h.sqtk.finite
  haveI := burnsideA315x_normal h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBL : B ≤ L := fun b _ => burnsideAut_d42_mem h hL b
  have hc := burnsideA315x_config_of_le h hBL
  haveI := h.simple
  have hne₀ := burnsideAut_Config_sup_ne_top hc h.nonabelian
  obtain ⟨K, _, _, σ, φ, hK, hσ, hφ, -, -⟩ :=
    CFSG.QuasithinUnique.Setup.X6.even_rank_two_residual_triality hL hc.sylow
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hB₁C : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := graphFixedRootBorel_le _ _ _
  set ψ : ↥L →* ModGL TwistTag.D4.tag K :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp φ.toMonoidHom with hψdef
  have hψ : Function.Injective ψ :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective.comp φ.injective
  have hUψ : ((T ⊓ L).subgroupOf L).map ψ = graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    rw [hψdef, ← Subgroup.map_map, hφ]
    exact Subgroup.map_subgroupOf_eq_of_le hUC
  have hrange : (⊤ : Subgroup ↥L).map ψ = graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    ext x
    constructor
    · rintro ⟨l, -, rfl⟩
      exact (φ l).2
    · intro hx
      obtain ⟨l, hl⟩ := φ.surjective ⟨x, hx⟩
      refine ⟨l, trivial, ?_⟩
      show ((φ l : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : ModGL TwistTag.D4.tag K) = x
      rw [hl]
  set Bm := (B.subgroupOf L).map ψ with hBm
  have eB : ↥(B.subgroupOf L) ≃* ↥Bm := (B.subgroupOf L).equivMapOfInjective ψ hψ
  have hBC : Bm ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rintro _ ⟨x, -, rfl⟩
    exact (φ x).2
  have hodd : Odd (Nat.card ↥Bm) := by
    rw [← Nat.card_congr eB.toEquiv]
    exact hc.odd
  have hnot3 : ¬ IsPGroup 3 ↥Bm := fun hp => hc.not3 (hp.of_equiv eB.symm)
  have hcases : IsMulCommutative ↥Bm ∨ ∃ r : ℕ, r.Prime ∧ IsPGroup r ↥Bm := by
    rcases hc.cases with hab | ⟨r, hr, hBr⟩
    · left
      refine ⟨⟨fun a b => ?_⟩⟩
      apply eB.symm.injective
      rw [map_mul, map_mul]
      exact hab.is_comm.comm _ _
    · exact Or.inr ⟨r, hr, hBr.of_equiv eB⟩
  have hperm : (Bm : Set (ModGL TwistTag.D4.tag K)) *
        (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) =
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) *
        (Bm : Set (ModGL TwistTag.D4.tag K)) := by
    have := burnsideA315x_map_permute ψ hc.perm
    rwa [hUψ] at this
  have hU2 : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := by
    rw [← hUψ]
    exact hc.sylow.2.1.map ψ
  have hsup : (B.subgroupOf L ⊔ (T ⊓ L).subgroupOf L).map ψ =
      Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    rw [Subgroup.map_sup, hUψ]
  have hsolv : Group.IsSolvable ↥(Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := by
    have hnil : Group.IsNilpotent ↥(B.subgroupOf L) := by
      rcases hc.cases with hab | ⟨r, hr, hBr⟩
      · haveI := hab
        infer_instance
      · haveI : Fact r.Prime := ⟨hr⟩
        exact hBr.isNilpotent
    haveI := hc.sup_solvable hnil
    rw [← hsup]
    exact solvable_of_surjective (f := ((B.subgroupOf L ⊔ (T ⊓ L).subgroupOf L).equivMapOfInjective
      ψ hψ).toMonoidHom) (MulEquiv.surjective _)
  have hne : Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≠
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    intro heq
    apply hne₀
    apply Subgroup.map_injective hψ
    rw [hsup, heq, hrange]
  obtain ⟨hB₁7, Dm, hDB, hDB₁, hD7, hrest⟩ :=
    burnsideAut_d42_core hK σ hσ Bm hBC hodd hnot3 hcases hperm hU2 hsolv hne
  have hN : (Subgroup.normalizer (((T ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L)).map ψ =
      graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
    have hBnorm := (fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀).2.2.2.2.2.2.1
    rw [hψdef, ← Subgroup.map_map, Subgroup.map_equiv_normalizer_eq _ φ, hφ,
      CFSG.QuasithinUnique.Setup.X6.normalizer_subgroupOf_eq' hUC, hBnorm]
    exact Subgroup.map_subgroupOf_eq_of_le hB₁C
  have hNG : (Subgroup.normalizer (((T ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [CFSG.QuasithinUnique.Setup.X6.normalizer_subgroupOf_eq' (inf_le_right : T ⊓ L ≤ L)]
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_left
  have hpull : ∀ X : Subgroup (ModGL TwistTag.D4.tag K), X ≤ Bm → (X.comap ψ).map ψ = X :=
    fun X hX => Subgroup.map_comap_eq_self (hX.trans (Subgroup.map_le_range ψ _))
  have hcardpull : ∀ X : Subgroup (ModGL TwistTag.D4.tag K), X ≤ Bm →
      Nat.card ↥((X.comap ψ).map L.subtype) = Nat.card ↥X := by
    intro X hX
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    conv_rhs => rw [← hpull X hX]
    rw [Subgroup.card_map_of_injective hψ]
  have hBeq : B = (B.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hBL).symm
  set D₀ := Dm.comap ψ with hD₀
  have hD₀N : D₀ ≤ Subgroup.normalizer (((T ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro x hx
    have hx' : ψ x ∈ (Subgroup.normalizer (((T ⊓ L).subgroupOf L : Subgroup ↥L) :
        Set ↥L)).map ψ := by
      rw [hN]
      exact hDB₁ hx
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [← hψ hyx]
  have hDcard : Nat.card ↥(D₀.map L.subtype) = 7 := by rw [hcardpull Dm hDB, hD7]
  have hDle : D₀.map L.subtype ≤ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [← hNG]
    exact Subgroup.map_mono hD₀N
  refine ⟨hL, D₀.map L.subtype, ⟨hDle, by rw [hDcard]; decide, ?_⟩, hDcard, ?_⟩
  ·
    obtain ⟨k, hk⟩ := hU2.exists_card_eq
    refine ⟨k, ?_⟩
    have h1 := Subgroup.relIndex_mul_card (D₀.map L.subtype)
      (L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G))
    rw [inf_eq_left.2 hDle, hDcard] at h1
    have h2 : Nat.card ↥(L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) =
        7 * 2 ^ k := by
      rw [← hNG, Subgroup.card_map_of_injective L.subtype_injective, ← hk, ← hB₁7, ← hN,
        Subgroup.card_map_of_injective hψ]
    rw [h2, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  · have hBm₀ : (B.subgroupOf L) = Bm.comap ψ := (Subgroup.comap_map_eq_self_of_injective hψ _).symm
    rcases hrest with hBD | ⟨Am, hAB, hA3, hDA, hcomm, hBDA⟩
    · left
      rw [hBeq, hBm₀, hBD]
    · right
      set A₀ := Am.comap ψ with hA₀
      have hAcard : Nat.card ↥(A₀.map L.subtype) = 3 := by rw [hcardpull Am hAB, hA3]
      refine ⟨A₀.map L.subtype, hAcard, ?_, ?_, ?_⟩
      · have h1 : Nat.card ↥(D₀.map L.subtype ⊓ A₀.map L.subtype) ∣ 1 := by
          have h7 : Nat.card ↥(D₀.map L.subtype ⊓ A₀.map L.subtype) ∣ 7 :=
            hDcard ▸ Subgroup.card_dvd_of_le inf_le_left
          have h3 : Nat.card ↥(D₀.map L.subtype ⊓ A₀.map L.subtype) ∣ 3 :=
            hAcard ▸ Subgroup.card_dvd_of_le inf_le_right
          have := Nat.dvd_gcd h7 h3
          simpa using this
        exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h1)
      · rintro _ ⟨d, hd, rfl⟩ _ ⟨a, ha, rfl⟩
        have h1 : ψ (d * a) = ψ (a * d) := by
          rw [map_mul, map_mul]
          exact hcomm _ hd _ ha
        have h2 := hψ h1
        show ((d : G) * (a : G)) = (a : G) * (d : G)
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, h2]
      · have hsup' : (D₀ ⊔ A₀).map ψ = (B.subgroupOf L).map ψ := by
          rw [Subgroup.map_sup, hpull Dm hDB, hpull Am hAB, ← hBDA]
        have h0 : D₀ ⊔ A₀ = B.subgroupOf L := Subgroup.map_injective hψ hsup'
        rw [hBeq, ← h0, Subgroup.map_sup]

end CFSG.ASVolI
