module

public import CFSG.Quasithin.Background.Harris.R1.J2VertGens
public import CFSG.Quasithin.Background.Harris.R1.J2VertSplitCount
public import CFSG.Quasithin.Background.Harris.R1.J2VertSym
public import CFSG.Quasithin.Background.Harris.R1.J2VertEmbed
public import CFSG.Quasithin.Background.Harris.R1.J2VertR
public import CFSG.Quasithin.Background.Harris.R1.SignChoiceL24
public import CFSG.Quasithin.Background.Harris.R1.QbetaDAbelInst
public import CFSG.Quasithin.EmptyFaithful.SzSurvLocStmt
public import CFSG.Quasithin.Recognition.SzVBKerAux

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1
  CFSG.CosetTable CFSG.ComponentClassification.J2Cover CFSG.Quasithin.SzVB

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem sup_bigB_eq (hset : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    K1 ⊔ bigB K1 L2 S = K1 ⊔ S := by
  apply le_antisymm
  · refine sup_le le_sup_left (sup_le (sup_le ?_ ?_) le_sup_right)
    · exact (F1.borelOf_le K1 S).trans le_sup_left
    · exact (F112J2.borelOf_L2_le_S hset hR).trans le_sup_right
  · exact sup_le le_sup_left ((le_sup_right : S ≤ bigB K1 L2 S).trans le_sup_right)

omit [Finite G] in
theorem card_eq_of_S5 {X : Subgroup G} (e : OTwoQuot X ≃* Equiv.Perm (Fin 5))
    (h32 : Nat.card ↥(pCoreOf 2 X) = 32) : Nat.card X = 3840 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥X)
  have h2 : Nat.card ↥(CFSG.Open.pCore 2 ↥X) = 32 := by
    rw [← h32, pCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
  have h3 : Nat.card (↥X ⧸ CFSG.Open.pCore 2 ↥X) = 120 := by
    rw [show Nat.card (↥X ⧸ CFSG.Open.pCore 2 ↥X) = Nat.card (OTwoQuot X) from rfl,
      Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  rw [h1, h2, h3]

omit [Finite G] in
theorem card_sylow_eq {S X : Subgroup G} [Finite X] (hS : IsSylowTwoOf S X)
    (hX : Nat.card X = 3840) : Nat.card S = 256 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite S := Finite.of_injective _ (Subgroup.inclusion_injective hS.1)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS.2.1
  have h := Subgroup.relIndex_mul_card (H := S) (K := X)
  rw [inf_of_le_left hS.1, hk, hX] at h
  have hodd : ¬ 2 ∣ S.relIndex X := hS.2.2
  have hr : 0 < S.relIndex X := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at h
    norm_num at h
  have hle : 2 ^ k ≤ 3840 := by
    rw [← h]
    exact Nat.le_mul_of_pos_left _ hr
  have hk12 : k < 12 := by
    by_contra hc
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
    norm_num at this
    omega
  rw [hk]
  interval_cases k <;> norm_num at h ⊢ <;> omega

theorem survivor11Loc_of
    (hRO : RankOneListedFacts.{0}) (hset : R1SettingLegacyBare K1 L2 S Zs)
    (hZS : ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs)
    (hL24 : IsL2Quot 2 (OTwoQuot K1)) (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥)
    (hSK : ¬ S ≤ K1) : Survivor11Loc K1 L2 S := by
  classical
  have hR : Hyp111R K1 L2 S := F112J2.hyp111R_of_setting hRO hset
  have hcen := f112R1aCenter_of_rankOne hRO G K1 L2 S Zs hset hL24 hna
  have hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs := qbeta_of_ZS_inst hRO hset hZS hL24 hna
  have hN2 : pCoreOf 2 (K1 ⊔ S) = pCoreOf 2 K1 := n2Loc_holds hRO G K1 L2 S Zs hset hZS hL24 hna
  have hQ : pCoreOf 2 (K1 ⊔ S) = vBeta K1 L2 S Zs := hN2.trans hQK
  have hQ8 : IsQ8D8 ↥(vBeta K1 L2 S Zs) := F112J2.isQ8D8_vBeta_of_setting hRO hset hL24 hna hcen
  have hW32 : Nat.card ↥(vBeta K1 L2 S Zs) = 32 := hQ8.1
  obtain ⟨eS5⟩ : Nonempty (OTwoQuot (K1 ⊔ S) ≃* Equiv.Perm (Fin 5)) :=
    (r1aSplit_holds G K1 L2 S Zs hset hL24 hN2).resolve_left hSK
  have hX : Nat.card ↥(K1 ⊔ S) = 3840 := card_eq_of_S5 eS5 (by rw [hQ, hW32])
  have heq := sup_bigB_eq hset hR
  refine ⟨⟨eS5⟩, by rw [hQK]; exact hQ8, ?_⟩
  let C5 := F112J2.fiveCtxOfSetting hRO hset hL24 hna
  let C : FamCtx K1 L2 S Zs (Fin 5) := famCtxOfFive C5
  obtain ⟨z, x, a, b, hzZ, hz1, hxW, haK, hbK, hzz, hzx, hxx, hxij, hx0, ha2, hb3, hab5, hza, hzb,
    hax, hbx, hclQ, hclK, hLQ⟩ := exists_normalized_gens C (Fintype.card_fin 5) hL24 hcen hQ hQK
  have hrel : VertRel z x a b := ⟨hzz, hzx, hxx, hxij, hx0, ha2, hb3, hab5, hza, hzb, hax, hbx⟩
  set X : Subgroup G := K1 ⊔ S with hXdef
  have hWK : vBeta K1 L2 S Zs ≤ K1 := hQK ▸ pCoreOf_le 2 K1
  have hzX : z ∈ X := Subgroup.mem_sup_left (hWK (F112J2.Zs_le_vBeta K1 L2 S Zs hzZ))
  have hxX : ∀ i, x i ∈ X := fun i => Subgroup.mem_sup_left (hWK (hxW i))
  have haX : a ∈ X := Subgroup.mem_sup_left haK
  have hbX : b ∈ X := Subgroup.mem_sup_left hbK
  set g := hrel.toVertGens hzX hxX haX hbX with hg
  have hχ : Function.Injective g.chi := hrel.chi_injective hzX hxX haX hbX hz1
  have hmapQ := hrel.map_Q hzX hxX haX hbX
  have hmapL := hrel.map_L hzX hxX haX hbX
  have hgQ : g.Q = (pCoreOf 2 X).subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [hmapQ, Subgroup.subgroupOf_map_subtype, hclQ, inf_of_le_left (pCoreOf_le 2 X), hN2]
  have : g.Q.Normal := by
    rw [hgQ]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 X)).mpr
      (le_normalizer_pCoreOf 2 X)
  have hXc : X ≤ Subgroup.centralizer (Zs : Set G) := sup_le hset.K1_cent_Z (F112J2.S_le_centralizer_Z hset)
  have hchar : CharTwo X := by
    have h1 := hset.hyp.h1.charTwo
    rwa [sup_eq_left.mpr ((F112J2.borelOf_L2_le_S hset hR).trans le_sup_right)] at h1
  have hC : ∀ h : ↥X, (∀ q ∈ g.Q, h * q = q * h) → h = 1 ∨ h = g.z := by
    intro h hh
    have hcp : (h : G) ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
      refine ⟨h.2, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
      have hpX : p ∈ X := pCoreOf_le 2 X hp
      have := hh ⟨p, hpX⟩ (by rw [hgQ]; exact Subgroup.mem_subgroupOf.mpr hp)
      exact (congrArg Subtype.val this).symm
    have hW : (h : G) ∈ vBeta K1 L2 S Zs := hQ ▸ hchar hcp
    have hZ : (h : G) ∈ Zs := hcen _ hW fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hcp.2 u (by rw [hQ]; exact hu)).symm
    rcases mem_Zs_cases hset hzZ hz1 hZ with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)
  have hLQ' : g.L ⊓ g.Q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp
    rw [Subgroup.map_inf_eq _ _ _ X.subtype_injective, hmapL, hmapQ, hclQ]
    exact hLQ
  obtain ⟨s, hsS, hsK⟩ := IsConcreteLE.not_le_iff_exists.mp hSK
  have hsX : s ∈ X := Subgroup.mem_sup_right hsS
  have hs : (⟨s, hsX⟩ : ↥X) ∉ g.Q ⊔ g.L := by
    intro hmem
    apply hsK
    have h1 : s ∈ (g.Q ⊔ g.L).map X.subtype := ⟨⟨s, hsX⟩, hmem, rfl⟩
    rw [Subgroup.map_sup, hmapQ, hmapL, ← Subgroup.closure_union] at h1
    rw [← hclK]
    convert h1 using 2
    ext y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  obtain ⟨ε, t, e, -, he⟩ := VertGens.exists_mulEquiv hχ hC hLQ' hX hs
  have hinv : ∀ i, e.symm (g.gens t i) = PresentedGroup.of i := fun i => by
    rw [← he i, MulEquiv.symm_apply_apply]
  cases ε with
  | false =>
    exfalso
    set j : ↥X →* Equiv.Perm (Fin 64) := sHom.comp e.symm.toMonoidHom with hj
    have hjinj : Function.Injective j := sHom_injective.comp e.symm.injective
    have hjrange : j.range = sHom.range := by
      rw [hj, MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ e.symm.surjective,
        ← MonoidHom.range_eq_map]
    have hjgen : ∀ i, j (g.gens t i) = sGen i := fun i => by
      show sHom (e.symm (g.gens t i)) = sGen i
      rw [hinv, sHom_of]
    have hjz : j g.z = zs := hjgen 0
    have hgQ' : g.Q = Subgroup.closure {g.gens t 0, g.gens t 1, g.gens t 2, g.gens t 3,
        g.gens t 4} := by
      apply Subgroup.map_injective X.subtype_injective
      rw [hmapQ, MonoidHom.map_closure]
      congr 1
      simp only [Set.image_insert_eq, Set.image_singleton]
      rfl
    have hset5 : sGen '' {i : Fin 8 | i.val < 5} = {sGen 0, sGen 1, sGen 2, sGen 3, sGen 4} := by
      ext y
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        fin_cases i
        all_goals first
          | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr (Or.inl rfl))
          | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          | exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
          | exact absurd hi (by decide)
      · rintro (rfl | rfl | rfl | rfl | rfl)
        exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩,
          ⟨4, by decide, rfl⟩]
    have hQ' : g.Q.map j = Qs := by
      rw [hgQ', MonoidHom.map_closure, Qs, hset5]
      simp only [Set.image_insert_eq, Set.image_singleton, hjgen]
    obtain ⟨v, hvV, hv2, hv1, hvz, -, hSv, hcnt⟩ := exists_symm_root_counts hset hR hzZ hz1
    have hvX : v ∈ X := pCoreOf_le 2 X (hset.V_le hvV)
    have hvQ : (⟨v, hvX⟩ : ↥X) ∈ g.Q := by
      rw [hgQ]
      exact Subgroup.mem_subgroupOf.mpr (hset.V_le hvV)
    have hSyl : IsSylowTwoOf S X := F112J2.isSylowTwoOf_K1S hR
    have hS256 : Nat.card ↥(S.subgroupOf X) = 256 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSyl.1).toEquiv]
      exact card_sylow_eq hSyl hX
    have hzc : ∀ h : ↥X, h * g.z = g.z * h := fun h =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hXc h.2) z hzZ).symm
    obtain ⟨h28, h12⟩ := split_root_counts j hjinj hjrange (S.subgroupOf X) g.Q hS256 hQ' hzc
      hjz hvQ (Subtype.ext hv2) (fun h => hv1 (congrArg Subtype.val h))
      (fun h => hvz (congrArg Subtype.val h)) (fun s hs =>
        (hSv s (Subgroup.mem_subgroupOf.mp hs)).imp (fun h => Subtype.ext h)
          (fun h => Subtype.ext h))
    have htr : ∀ (w : G) (hw : w ∈ X),
        Nat.card {y : S.subgroupOf X // (y : ↥X) * ⟨v, hvX⟩ = ⟨v, hvX⟩ * y ∧
          (y : ↥X) * y = ⟨w, hw⟩} =
        Nat.card {y : S // (y : G) * v = v * y ∧ (y : G) * y = w} := fun w hw =>
      Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hSyl.1).toEquiv.subtypeEquiv fun _ =>
        ⟨fun h => ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩,
          fun h => ⟨Subtype.ext h.1, Subtype.ext h.2⟩⟩)
    have e1 := htr z hzX
    have e2 := htr v hvX
    have e3 : Nat.card {y : S // (y : G) * v = v * y ∧ (y : G) * y = z} = 28 := e1 ▸ h28
    have e4 : Nat.card {y : S // (y : G) * v = v * y ∧ (y : G) * y = v} = 12 := e2 ▸ h12
    omega
  | true =>
    set φ : ↥X →* Equiv.Perm (Fin 315) := rHom.comp e.symm.toMonoidHom with hφ
    have hφinj : Function.Injective φ := rHom_injective.comp e.symm.injective
    have hφR : φ.range ≤ R := by
      rw [hφ, MonoidHom.range_comp]
      exact (Subgroup.map_le_range _ _).trans range_rHom_le_R
    refine exists_autJ2_embedding (X := ↥(K1 ⊔ bigB K1 L2 S)) (by rw [heq]; exact hX)
      (φ.comp (MulEquiv.subgroupCongr heq).toMonoidHom)
      (hφinj.comp (MulEquiv.subgroupCongr heq).injective) ?_
    rw [MonoidHom.range_comp]
    exact (Subgroup.map_le_range _ _).trans hφR

theorem r1aLoc_nonab
    (hRO : RankOneListedFacts.{0}) (hset : R1SettingLegacyBare K1 L2 S Zs)
    (hZS : ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs)
    (hL24 : IsL2Quot 2 (OTwoQuot K1)) (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥) :
    Survivor10Loc K1 L2 S ∨ Survivor11Loc K1 L2 S := by
  by_cases hSK : S ≤ K1
  · left
    have hcen := f112R1aCenter_of_rankOne hRO G K1 L2 S Zs hset hL24 hna
    refine ⟨hL24, ?_, hSK⟩
    rw [qbeta_of_ZS_inst hRO hset hZS hL24 hna]
    exact F112J2.isQ8D8_vBeta_of_setting hRO hset hL24 hna hcen
  · exact Or.inr (survivor11Loc_of hRO hset hZS hL24 hna hSK)

theorem f112R1aLoc_of_abelian
    (hRO : RankOneListedFacts.{0}) (hab : F112R1aAbelianStatement) : F112R1aLocStatement := by
  intro G _ _ K1 L2 S Zs hset hZS hL24
  by_cases hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = ⊥
  · exact (hab G K1 L2 S Zs hset hL24 hna).elim
  · exact r1aLoc_nonab hRO hset (hZS hna) hL24 hna

end CFSG.Quasithin.Background.Harris.R1.J2Vert
