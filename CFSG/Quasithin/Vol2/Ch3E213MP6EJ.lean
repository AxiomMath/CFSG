module

public import CFSG.Quasithin.Vol2.Ch3E213MP6EA
public import CFSG.Quasithin.Vol2.Ch3E213MP6AC
public import CFSG.Quasithin.Vol2.Ch3E213MP6EI
public import CFSG.Quasithin.Vol2.Ch3E213MLift
public import CFSG.Quasithin.Vol2.Ch3E213MShare
public import CFSG.Quasithin.H13.QRCBenderAmbient
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp antiSpEquiv)

namespace P6E

theorem isSylowTwoOf_top_of_sylow' {W : Type} [Group W] [Finite W] (S : Sylow 2 W) :
    IsSylowTwoOf (S : Subgroup W) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, S.isPGroup', ?_⟩
  rw [show ((S : Subgroup W).subgroupOf ⊤).index = (S : Subgroup W).index from
    Subgroup.relIndex_top_right _]
  exact S.not_dvd_index

theorem inf_pCoreOf_le {G : Type} [Group G] [Finite G] {H X V : Subgroup G} (hXH : X ≤ H)
    (hVX : V ≤ X) : V ⊓ pCoreOf 2 H ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_trans (le_inf inf_le_right (inf_le_left.trans hVX))
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left))
  exact (le_inf (hXH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
    Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf

end P6E

theorem sp4One_model_hyps {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}
    (hS : Setting H T M V K) (h2 : Case2 H T M K)
    (hSp : E2.IsSp4Prime 1 ↥(E2.star M H K))
    (hD : E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)))
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) :
    (barIn M H K).Normal ∧
      IsSylowTwoOf (barIn M H T) ⊤ ∧
      (∀ a : ↥H ⧸ kerIn (M.subgroupOf H) ⊤,
        (∀ k ∈ barIn M H K, a * k = k * a) → a = 1) ∧
      IsAlt 6 ↥(barIn M H K) ∧
      barIn M H K ⊔ barIn M H T = ⊤ ∧
      (∀ P : Subgroup (↥H ⧸ kerIn (M.subgroupOf H) ⊤),
        IsMaxParabolic2 (barIn M H K) P →
        barIn M H K ⊓ Subgroup.normalizer
          ((barIn M H T ⊓ barIn M H K : Subgroup (↥H ⧸ kerIn (M.subgroupOf H) ⊤)) :
            Set (↥H ⧸ kerIn (M.subgroupOf H) ⊤)) ≤ P →
        ¬ barIn M H T ≤
          Subgroup.normalizer (P : Set (↥H ⧸ kerIn (M.subgroupOf H) ⊤))) ∧
      (∃ S₀ : Subgroup (↥H ⧸ kerIn (M.subgroupOf H) ⊤), IsSylowTwoOf S₀ (barIn M H K) ∧
        barIn M H M ⊓ barIn M H K = barIn M H K ⊓
          Subgroup.normalizer (S₀ : Set (↥H ⧸ kerIn (M.subgroupOf H) ⊤))) ∧
      barIn M H T ≤ barIn M H M ∧
      barIn M H V ≤ barIn M H T ∧
      barIn M H T ≤ Subgroup.normalizer (barIn M H V : Set (↥H ⧸ kerIn (M.subgroupOf H) ⊤)) ∧
      (∀ x ∈ barIn M H V, x * x = 1) ∧
      4 ≤ Nat.card (barIn M H V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAlt : IsAlt 6 ↥(E2.star M H K) := by
    have h : E2.IsSp4Prime 1 ↥(E2.star M H K) = IsAlt 6 ↥(E2.star M H K) := rfl
    exact cast h hSp
  have hmp := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hKnH : (K.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH, hS.eq_sup]
    exact sup_le Subgroup.le_normalizer h2.1
  obtain ⟨T', hT', -, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', -⟩ :=
    qrcHyp_of_hyp28 hS.hyp hS.charTwo
  have hVQ' : 4 ≤ (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) := by
    rw [relIndex_subgroupOf_inf_pCore hVH]
    exact hS.four_le
  obtain ⟨-, -, -, hKn, hCK, hKS, ⟨hSB, -, -⟩, -, hEcard, -⟩ :=
    H13.QRC.bender_section_setup hS.not_solvable T' hTn hTM' hMH' hmax' hVT' hVM'
  have hK₀ := map_oddResidualPreimage_eq_of_case2 hS h2
  have hKN : (barIn M H K).Normal := by simpa only [barIn] using hK₀ ▸ hKn
  have hCK' : ∀ a : ↥H ⧸ kerIn (M.subgroupOf H) ⊤,
      (∀ k ∈ barIn M H K, a * k = k * a) → a = 1 := by
    simpa only [barIn, hK₀] using hCK
  obtain ⟨φ⟩ := nonempty_mulEquiv_star hMH K
  obtain ⟨e₀⟩ := hAlt
  have hAlt' : IsAlt 6 ↥(barIn M H K) := ⟨φ.trans e₀⟩
  have hTKs := E2P.star_inf_T (M := M) hmp.isSylow
    (CFSG.Open.IsSubnormal.step hKH hKnH (CFSG.Open.IsSubnormal.refl H)) hKH
  have hMKs := E2P.star_inf_M (H := H) (M := M) K
  set e := starEquiv hMH with he
  have hKe : (barIn M H K).map e.toMonoidHom = E2.star M H K :=
    map_barIn_starEquiv hMH K
  have hTe : (barIn M H T).map e.toMonoidHom = E2.star M H T :=
    map_barIn_starEquiv hMH T
  have hMe : (barIn M H M).map e.toMonoidHom = E2.star M H M :=
    map_barIn_starEquiv hMH M
  have hT'bar : (T' : Subgroup H).map
      (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) = barIn M H T := by
    rw [hT']; rfl
  have hSsyl : IsSylowTwoOf (barIn M H T) ⊤ := by
    have h := P6E.isSylowTwoOf_top_of_sylow'
      (T'.mapSurjective (QuotientGroup.mk'_surjective (kerIn (M.subgroupOf H) ⊤)))
    rw [Sylow.coe_mapSurjective, hT'bar] at h
    exact h
  have hKS' : barIn M H K ⊔ barIn M H T = ⊤ := by
    simpa only [barIn, hK₀, hT'bar] using hKS
  have hSB' : barIn M H T ≤ barIn M H M := by
    simpa only [barIn, hT'bar] using hSB
  have hdiag : ∀ P : Subgroup (↥H ⧸ kerIn (M.subgroupOf H) ⊤),
      IsMaxParabolic2 (barIn M H K) P →
      barIn M H K ⊓ Subgroup.normalizer
        ((barIn M H T ⊓ barIn M H K : Subgroup (↥H ⧸ kerIn (M.subgroupOf H) ⊤)) :
          Set (↥H ⧸ kerIn (M.subgroupOf H) ⊤)) ≤ P →
      ¬ barIn M H T ≤
        Subgroup.normalizer (P : Set (↥H ⧸ kerIn (M.subgroupOf H) ⊤)) := by
    intro P hP hle hSP
    refine hD (P.map e.toMonoidHom) ?_ ?_ ?_
    · rw [← hKe]
      exact P5.isMaxParabolic2_map_equiv e hP
    · rw [← hKe, hTKs, ← hTe, ← hKe, ← Subgroup.map_inf _ _ _ e.injective,
        ← P5.map_inf_normalizer]
      exact Subgroup.map_mono hle
    · rw [← hTe]
      exact P5.map_le_normalizer e hSP
  have hBorel : ∃ S₀ : Subgroup (↥H ⧸ kerIn (M.subgroupOf H) ⊤),
      IsSylowTwoOf S₀ (barIn M H K) ∧
      barIn M H M ⊓ barIn M H K = barIn M H K ⊓
        Subgroup.normalizer (S₀ : Set (↥H ⧸ kerIn (M.subgroupOf H) ⊤)) := by
    obtain ⟨S₀, hS₀, hS₀eq⟩ := hB
    refine ⟨S₀.map e.symm.toMonoidHom, ?_, ?_⟩
    · have h := P5.isSylowTwoOf_map_equiv e.symm hS₀
      rwa [← hKe, P5.map_symm_map] at h
    · have h := congrArg (Subgroup.map e.symm.toMonoidHom) hS₀eq
      rw [hMKs, ← hMe, ← hKe, ← Subgroup.map_inf _ _ _ e.injective,
        P5.map_symm_map, P5.map_inf_normalizer, P5.map_symm_map] at h
      exact h
  have hEl : IsElementaryAbelian 2 (V.subgroupOf H) := hel
  have hEel : IsElementaryAbelian 2 (barIn M H V) :=
    IsElementaryAbelian.map (A := V.subgroupOf H)
      (f := (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤) :
        ↥H →* (↥H ⧸ kerIn (M.subgroupOf H) ⊤)))
  have hE2 : ∀ x ∈ barIn M H V, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hES : barIn M H V ≤ barIn M H T := by
    simpa only [barIn, hT'bar] using
      Subgroup.map_mono (f := QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) hVT'
  have hSE : barIn M H T ≤
      Subgroup.normalizer (barIn M H V : Set (↥H ⧸ kerIn (M.subgroupOf H) ⊤)) := by
    simpa only [barIn, hT'bar] using
      (Subgroup.map_mono (f := QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) hTV').trans
        (Subgroup.le_normalizer_map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)))
  have hE4 : 4 ≤ Nat.card (barIn M H V) := hEcard ▸ hVQ'
  exact ⟨hKN, hSsyl, hCK', hAlt', hKS', hdiag, hBorel, hSB', hES, hSE, hE2, hE4⟩

theorem member_sp4One
    {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}
    (hS : Setting H T M V K) (h2 : Case2 H T M K) (hSp : E2.IsSp4Prime 1 ↥(E2.star M H K))
    (hD : E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)))
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) :
    ∃ g : G, Sp4Member H T M V g (ZMod 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  obtain ⟨hKN, hSsyl, hCK, hAlt, hKS, hdiag, hBorel, hSB, hES, hSE, hE2, hE4⟩ :=
    sp4One_model_hyps hS h2 hSp hD hB
  set D := kerIn (M.subgroupOf H) (⊤ : Subgroup H) with hDdef
  set π := QuotientGroup.mk' D with hπdef
  set Kb := barIn M H K with hKbdef
  set Sb := barIn M H T with hSbdef
  set Bb := barIn M H M with hBbdef
  set Eb := barIn M H V with hEbdef
  have hKbN : Kb.Normal := hKN
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', -⟩ :=
    qrcHyp_of_hyp28 hS.hyp hS.charTwo
  obtain ⟨-, -, -, -, -, -, -, -, hEcard, -⟩ :=
    H13.QRC.bender_section_setup hS.not_solvable T' hTn hTM' hMH' hmax' hVT' hVM'
  have hEl : IsElementaryAbelian 2 (V.subgroupOf H) := hel
  have hVQ' : 4 ≤ (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) := by
    rw [relIndex_subgroupOf_inf_pCore hVH]
    exact hS.four_le
  have hVQ : ¬ V.subgroupOf H ≤ CFSG.pCore 2 H := fun h => by
    rw [inf_eq_left.2 h, Subgroup.relIndex_self] at hVQ'
    omega
  have hT'bar : (T' : Subgroup H).map π = Sb := by
    rw [hT', hSbdef]; rfl
  obtain ⟨⟨χ⟩, -, x, hxK, hFeq, hBF, hSFsyl, hE4le, hN⟩ :=
    P6E.model_sp4_one hSsyl hCK hAlt hKS hdiag hBorel hSB hES hSE hE2 hE4
  have hbot : IsElementaryAbelian 2 (⊥ : Subgroup (↥H ⧸ D)) :=
    { is_comm := ⟨fun _ _ => Subsingleton.elim _ _⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun _ => Subsingleton.elim _ _ }
  have hFA : ∀ f ∈ Kb ⊔ Eb, ∀ a ∈ (⊥ : Subgroup (↥H ⧸ D)), f * a = a * f := fun f _ a ha => by
    rw [Subgroup.mem_bot.1 ha, mul_one, one_mul]
  have hxL : x ∈ Kb ⊔ Eb ⊔ ⊥ := by
    rw [sup_bot_eq]
    exact (le_sup_left : Kb ≤ Kb ⊔ Eb) hxK
  have hL : Kb ⊔ Eb ⊔ ⊥ = Eb ⊔ CFSG.conjugate Eb x := by
    rw [sup_bot_eq]
    exact hFeq
  have hFnt : Kb ⊔ Eb ≠ ⊥ := by
    intro h
    have h1 : Eb ≤ ⊥ := by
      rw [← h]
      exact le_sup_right
    have h3 := hE4
    rw [le_bot_iff.1 h1, Subgroup.card_bot] at h3
    omega
  obtain ⟨σ⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
    (k := ZMod 2) (ZMod.card 2)
  have hexact : OddCoverExact ↥(Kb ⊔ Eb) :=
    oddCoverExact_of_mulEquiv_statedSp 2 (χ.trans σ.symm)
  have hSF : CFSG.ABGLocalTools.IsSylowOf 2 (Sb ⊓ (Kb ⊔ Eb)) (Kb ⊔ Eb) :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hSFsyl.1, hSFsyl.2.1, hSFsyl.2.2⟩
  have hPFcore : kerIn (Sb ⊓ (Kb ⊔ Eb)) (Kb ⊔ Eb) = ⊥ := by
    have hle : kerIn (Sb ⊓ (Kb ⊔ Eb)) (Kb ⊔ Eb) ≤ Kb ⊔ Eb := kerIn_le.trans inf_le_right
    exact hN _ hle (hSFsyl.2.1.to_le kerIn_le)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 (le_normalizer_kerIn _ _))
  have hFO : inSubgroup (CFSG.pCore 2) (Kb ⊔ Eb) = ⊥ := by
    refine hN _ (Subgroup.map_subtype_le _) (CFSG.pCore_isPGroup.map _) ?_
    rw [inSubgroup, show ((CFSG.pCore 2 ↥(Kb ⊔ Eb)).map (Kb ⊔ Eb).subtype).subgroupOf
      (Kb ⊔ Eb) = CFSG.pCore 2 ↥(Kb ⊔ Eb) from
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _]
    infer_instance
  have hPFO : inSubgroup (CFSG.pCore 2) (Sb ⊓ (Kb ⊔ Eb)) = Sb ⊓ (Kb ⊔ Eb) := by
    have htop : CFSG.pCore 2 ↥(Sb ⊓ (Kb ⊔ Eb)) = ⊤ :=
      top_le_iff.1 (le_sSup ⟨inferInstance, hSFsyl.2.1.to_subgroup ⊤⟩)
    rw [inSubgroup, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hSL : (T' : Subgroup H).map π ⊓ (Kb ⊔ Eb ⊔ ⊥) = Sb ⊓ (Kb ⊔ Eb) ⊔ ⊥ := by
    rw [hT'bar, sup_bot_eq, sup_bot_eq]
  have hBL : Bb ⊓ (Kb ⊔ Eb ⊔ ⊥) = Sb ⊓ (Kb ⊔ Eb) ⊔ ⊥ := by
    rw [sup_bot_eq, sup_bot_eq]
    exact hBF
  obtain ⟨g, hgI, hVI, -, -, -, -, -, -, -, -, hTIsyl, -, -, hJ1, hJ2, -, -, hcharI, hO2MI, hNV,
      ψ, hψs, hψker, -, -, -, -⟩ :=
    pair_lift_of_oddCoverExact hcharH T' hTn hTM' hMH' hmax' hVT' hTV' hVM' hVQ
      (F := Kb ⊔ Eb) (A := ⊥) hFA (inf_bot_eq _) hxL hL hFnt hexact
      (SF := Sb ⊓ (Kb ⊔ Eb)) (PF := Sb ⊓ (Kb ⊔ Eb)) hSF inf_le_right hPFcore hFO hPFO hSL hBL
  rw [hT'] at hTIsyl hO2MI
  have hVMI : V.subgroupOf H ≤ inSubgroup (CFSG.pCore 2)
      (M.subgroupOf H ⊓ (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g)) := by
    rw [hO2MI]
    exact le_inf (hT' ▸ hVT') le_sup_left
  obtain ⟨hIX, hpair, hker⟩ := pair_of_qrc_kerIn hTH hMH hS.hyp.le_T hS.hyp.normal_T
    hS.hyp.elem rfl hgI hTIsyl (fun x hx => (hNV ⟨hx.2, hx.1⟩).1) hVMI (hJ1.symm.trans hJ2)
  obtain ⟨hc2, hne⟩ := charTwo_ne_of_qrc hVH hcharI hVI
  rw [hIX] at hc2 hne
  have hψk' :
      ψ.ker = CFSG.pCore 2 ↥(V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) := by
    rw [hψker, hJ2, inSubgroup]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have hXH : Ch3n.pairI V (g : G)⁻¹ ≤ H := by
    rw [← hIX]
    exact Subgroup.map_subtype_le _
  have hle : V ⊓ pCoreOf 2 H ≤
      kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹) ⊓ V := by
    rw [hker]
    exact le_inf (P6E.inf_pCoreOf_le hXH hpair.V_le) inf_le_left
  have hVcard : (V ⊓ pCoreOf 2 H).relIndex V = Nat.card Eb := by
    rw [← relIndex_subgroupOf_inf_pCore hVH, ← hEcard]
    rfl
  have hpos : 0 < (V ⊓ pCoreOf 2 H).relIndex V := by
    rw [hVcard]
    exact Nat.card_pos
  set ρ : ↥(V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) ≃* ↥(Ch3n.pairI V (g : G)⁻¹) :=
    ((V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g).equivMapOfInjective H.subtype
      H.subtype_injective).trans (MulEquiv.subgroupCongr hIX) with hρ
  set τ : Equiv.Perm (Fin 6) ≃* antiSp (ZMod 2) := ((antiSpEquiv (ZMod 2)).trans σ).symm
    with hτ
  set ψX : ↥(Ch3n.pairI V (g : G)⁻¹) →* antiSp (ZMod 2) :=
    (τ.toMonoidHom.comp (χ.toMonoidHom.comp ψ)).comp ρ.symm.toMonoidHom with hψX
  have hψXs : Function.Surjective ψX :=
    (τ.surjective.comp (χ.surjective.comp hψs)).comp ρ.symm.surjective
  have hker1 : (τ.toMonoidHom.comp (χ.toMonoidHom.comp ψ)).ker =
      CFSG.pCore 2 ↥(V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) := by
    rw [← hψk']
    ext y
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  have hψXk : ψX.ker = (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹)
      (Ch3n.pairI V (g : G)⁻¹)).subgroupOf (Ch3n.pairI V (g : G)⁻¹) := by
    rw [hψX, ← MonoidHom.comap_ker, hker1, Subgroup.comap_equiv_eq_map_symm',
      MulEquiv.symm_symm, CFSG.pCore_map_iso, hker, pCoreOf]
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _).symm
  refine ⟨(g : G)⁻¹, H.inv_mem g.2, hpair, hc2, hne, hker, ⟨ψX, hψXs, hψXk⟩, ?_⟩
  rw [Nat.card_zmod]
  calc (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹) ⊓ V).relIndex V
      ≤ (V ⊓ pCoreOf 2 H).relIndex V :=
        Nat.le_of_dvd hpos (Subgroup.relIndex_dvd_of_le_left V hle)
    _ = Nat.card Eb := hVcard
    _ ≤ 2 ^ 2 := hE4le

theorem pkgSp4One :
    PkgSp4One := by
  intro G _ _ H T M V K hS h2 hSp hD hB
  obtain ⟨g, h⟩ := member_sp4One hS h2 hSp hD hB
  exact e213Concl_of_sp4Member h

end CFSG.Quasithin.Ch3E213M
