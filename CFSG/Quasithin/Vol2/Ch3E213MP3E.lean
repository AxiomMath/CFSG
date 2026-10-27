module

public import CFSG.Quasithin.Vol2.Ch3E213MP3D
public import CFSG.Quasithin.Vol2.Ch3E213MShare
public import CFSG.Quasithin.Vol2.Ch3E213MFam
public import CFSG.Quasithin.H13.QRCBenderAmbient
public import CFSG.Quasithin.Vol2.Ch3E213MP3C

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.GorensteinWalter (PSL2)

namespace P3

theorem map_equiv_centralizer_eq {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (K : Subgroup Y) : (Subgroup.centralizer (K : Set Y)).map e.toMonoidHom =
      Subgroup.centralizer ((K.map e.toMonoidHom : Subgroup Y') : Set Y') := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨k, hk, rfl⟩
    have := congrArg e (h k hk)
    simpa using this
  · intro h k hk
    apply e.injective
    simpa using h (e k) ⟨k, hk, rfl⟩

theorem autCard_map {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (X K : Subgroup Y) :
    E2.autCard (X.map e.toMonoidHom) (K.map e.toMonoidHom) = E2.autCard X K := by
  rw [E2.autCard, E2.autCard, ← Subgroup.map_equiv_normalizer_eq, ← map_equiv_centralizer_eq,
    ← Subgroup.map_inf _ _ e.toMonoidHom e.injective,
    ← Subgroup.map_inf _ _ e.toMonoidHom e.injective,
    Subgroup.relIndex_map_map_of_injective _ _ e.injective]

theorem card_quotient_pCore_eq {I L : Type*} [Group I] [Group L] {ψ : I →* L}
    (hψ : Function.Surjective ψ) (hker : ψ.ker = CFSG.pCore 2 I) :
    Nat.card (I ⧸ CFSG.pCore 2 I) = Nat.card L :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).toEquiv

theorem exists_orderOf_of_surjective {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {I : Subgroup H} {L : Type*} [Group L] {ψ : I →* L} (hψ : Function.Surjective ψ) {c : L}
    {n : ℕ} (hc : orderOf c = n) : ∃ x ∈ I.map H.subtype, orderOf x = n := by
  obtain ⟨y, rfl⟩ := hψ c
  have hdvd : n ∣ orderOf y := hc ▸ orderOf_map_dvd ψ y
  have hz : orderOf (y ^ (orderOf y / n)) = n := orderOf_pow_orderOf_div (orderOf_pos y).ne' hdvd
  refine ⟨((y ^ (orderOf y / n) : I) : H), ⟨_, (y ^ (orderOf y / n)).2, rfl⟩, ?_⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]

end P3

theorem P3.relIndex_map_subtype {G : Type} [Group G] {H : Subgroup G} (X W : Subgroup H) :
    (X.map H.subtype ⊓ W.map H.subtype).relIndex (W.map H.subtype) = X.relIndex W := by
  rw [← Subgroup.map_inf _ _ _ H.subtype_injective,
    Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective, Subgroup.inf_relIndex_right]

theorem exists_dihedral_member_of_oddPaired
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat)
    {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G} (hS : Setting H T M V K)
    (h1 : Case1 H T M K) {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7)
    (hPSL : IsPSL 2 p 1 ↥(E2.star M H K))
    (haut : 8 < E2.autCard (E2.star M H T) (E2.star M H K)) :
    ∃ g ∈ H, E2.Pair (Ch3n.pairI V g) (T ⊓ Ch3n.pairI V g) (M ⊓ Ch3n.pairI V g) V g ∧
      CharTwo (Ch3n.pairI V g) ∧ Ch3n.pairI V g ≠ V ∧
      kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) = pCoreOf 2 (Ch3n.pairI V g) ∧
      ∃ ℓ b : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ 1 ≤ b ∧
        (pCoreOf 2 (Ch3n.pairI V g)).relIndex (Ch3n.pairI V g) = 2 * ℓ ^ b ∧
        (∃ c ∈ Ch3n.pairI V g, orderOf c = ℓ ^ b) ∧
        (pCoreOf 2 (Ch3n.pairI V g) ⊓ V).relIndex V = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', -⟩ :=
    qrcHyp_of_hyp28 hS.hyp hS.charTwo
  have := hel
  obtain ⟨-, -, -, hKn, hCK, -, ⟨hSB, -, -⟩, -, hEcard, hEO⟩ :=
    H13.QRC.bender_section_setup hS.not_solvable T' hTn hTM' hMH' hmax' hVT' hVM'
  obtain ⟨t₀, ht₀T, -, hK, hc, hd⟩ := exists_paired_of_case1' h38 hS h1
  set D := kerIn (M.subgroupOf H) (⊤ : Subgroup H) with hD
  set π := QuotientGroup.mk' D with hπ
  set K₁ := barIn M H K with hK₁
  set S := (T' : Subgroup H).map π with hSdef
  set E := (V.subgroupOf H).map π with hEdef
  rw [hK] at hKn hCK
  obtain ⟨φ⟩ := nonempty_mulEquiv_star hMH K
  obtain ⟨-, F, _, _, hF, ⟨ψ₀⟩⟩ := hPSL
  have hF' : Nat.card F = p := by rw [hF, pow_one]
  set θ : K₁ ≃* PSL2 F := φ.trans (ψ₀.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm) with hθ
  have := P3.isSimpleGroup_of hp hp8 hF' θ
  have hS2 : IsPGroup 2 S := T'.isPGroup'.map π
  have hSsyl : IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, hS2, ?_⟩
    show ¬ 2 ∣ S.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have h := (T'.mapSurjective (QuotientGroup.mk'_surjective D)).not_dvd_index
    rwa [Sylow.coe_mapSurjective] at h
  have htS : π t₀ ∈ S := ⟨t₀, hT' ▸ ht₀T, rfl⟩
  have hES : E ≤ S := Subgroup.map_mono hVT'
  have hSE : S ≤ Subgroup.normalizer (E : Set _) :=
    (Subgroup.map_mono hTV').trans (Subgroup.le_normalizer_map π)
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have h := hS.hyp.elem.1.is_comm.comm (⟨(v : G), hv⟩ : V) ⟨(w : G), hw⟩
    exact Subtype.ext (congrArg (Subtype.val : V → G) h)
  have hE2 : ∀ e ∈ E, e * e = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← pow_two, CFSG.elemPow_eq_one_of_isElementaryAbelian v hv, map_one]
  have hVQ' : 4 ≤ (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) := by
    rw [relIndex_subgroupOf_inf_pCore hVH]
    exact hS.four_le
  have hE4 : 4 ≤ Nat.card E := hEcard ▸ hVQ'
  have haut' : 8 < E2.autCard S K₁ := by
    have hST : S = barIn M H T := by rw [hSdef, hT']; rfl
    rw [← P3.autCard_map (starEquiv hMH), hST, hK₁, map_barIn_starEquiv, map_barIn_starEquiv]
    exact haut
  obtain ⟨hEN, a, haE, haC, hEa⟩ :=
    P3.exists_eq_sup hp hp8 hF' θ hc hd hKn hCK hSsyl htS rfl hSE hEc hE2 hE4 haut'
  have hK2 : ¬ IsPGroup 2 K₁ := by
    intro h2
    have := h2.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center K₁)
    refine hz (Subtype.ext (Subtype.ext (P3.eq_one_of_central θ z.1.2 fun y hy => ?_)))
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)).symm
  obtain ⟨y, hyK, ℓ, b, hℓ, hℓ2, hb, hy, hay⟩ :=
    P3.exists_inverted hK2 (hE2 a haE) (hEN haE) haC
  have hdd := P3.dihedral_data hEc hE2 haE haC hEa hyK hℓ hℓ2 hb hy hay hES hS2 hEO
  dsimp only at hdd
  obtain ⟨hFA, hFAb, hxL, hL, ⟨eD⟩, hcard2, hsyl, hPF, hcore, hFO, hPFO, hSL, hBL⟩ := hdd
  have : CFSG.IsElementaryAbelian 2 ↥(E ⊓ Subgroup.centralizer (K₁ : Set (↥H ⧸ D))) :=
    P3.isElementaryAbelian_of (fun x hx z hz => hEc x hx.1 z hz.1) fun x hx => hE2 x hx.1
  have hVQ : ¬ V.subgroupOf H ≤ CFSG.pCore 2 H := by
    intro h
    rw [inf_eq_left.2 h, Subgroup.relIndex_self] at hVQ'
    omega
  have h9 := H13.QRC.qrc_original_pair_lift_retains_central_second_factor hcharH T' hTn hTM'
    hMH' hmax' hVT' hTV' hVM' hVQ hFA hFAb hxL hL
    (Or.inl ⟨ℓ, b, hℓ, hℓ2, hb, ⟨eD⟩, hcard2⟩) hsyl hPF hcore hFO hPFO hSL hBL
  obtain ⟨g, hgI, hVI, -, h9⟩ := h9
  dsimp only at h9
  obtain ⟨-, -, -, -, -, -, -, hTIsyl, -, -, hJcore, hJO, -, -, hcharI, hO2MI, hNV, ψ, hψs,
    hψker, -, -, -, hψV⟩ := h9
  rw [hT'] at hTIsyl hO2MI
  have hVMI : V.subgroupOf H ≤ inSubgroup (CFSG.pCore 2)
      (M.subgroupOf H ⊓ (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g)) := by
    rw [hO2MI]
    exact le_inf (hT' ▸ hVT') le_sup_left
  obtain ⟨hIX, hpair, hker⟩ := pair_of_qrc_kerIn hTH hMH hS.hyp.le_T hS.hyp.normal_T
    hS.hyp.elem rfl hgI hTIsyl (fun x hx => (hNV ⟨hx.2, hx.1⟩).1) hVMI (hJcore.symm.trans hJO)
  obtain ⟨hc2, hne⟩ := charTwo_ne_of_qrc hVH hcharI hVI
  rw [hIX] at hc2 hne
  have hψk : ψ.ker = CFSG.pCore 2 ↥(V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) := by
    rw [hψker, hJO, inSubgroup]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have hcardI : (pCoreOf 2 (Ch3n.pairI V (g : G)⁻¹)).relIndex (Ch3n.pairI V (g : G)⁻¹) =
      2 * ℓ ^ b := by
    rw [← hIX, relIndex_pCoreOf_map_subtype, P3.card_quotient_pCore_eq hψs hψk,
      Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  obtain ⟨c, hc, hcy⟩ := P3.exists_orderOf_of_surjective hψs
    (c := ⟨y, Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton y))⟩)
    (by rw [Subgroup.orderOf_mk, hy])
  have hJrel : (inSubgroup (CFSG.pCore 2)
      (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g)).relIndex (V.subgroupOf H) = 2 := by
    have h2 := Subgroup.relIndex_ker ((V.subgroupOf H).subgroupOf
      (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g)) ψ
    rw [hψker, hJO, Subgroup.relIndex_subgroupOf le_sup_left, hψV,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h2
    exact h2.trans hcard2
  have hVrel : (pCoreOf 2 (Ch3n.pairI V (g : G)⁻¹) ⊓ V).relIndex V = 2 := by
    have h2 := P3.relIndex_map_subtype (inSubgroup (CFSG.pCore 2)
      (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g)) (V.subgroupOf H)
    rw [map_subtype_inSubgroup_pCore, hIX, Subgroup.map_subgroupOf_eq_of_le hVH] at h2
    rw [h2, hJrel]
  exact ⟨(g : G)⁻¹, H.inv_mem g.2, hpair, hc2, hne, hker, ℓ, b, hℓ, hℓ2, hb, hcardI,
    ⟨c, hIX ▸ hc, hcy⟩, hVrel⟩

theorem pkgOddPaired
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) : PkgOddPaired := by
  intro G _ _ H T M V K hS h1 p hp hp8 hPSL _ haut
  obtain ⟨g, hg, hpair, hc2, hne, hker, ℓ, b, hℓ, hℓ2, hb, hcard, -, -⟩ :=
    exists_dihedral_member_of_oddPaired h38 hS h1 hp hp8 hPSL haut
  exact ⟨g, hg, hpair, hc2, hne, relIndex_le_of_dihedral hpair hc2 hℓ hℓ2 hb (hker ▸ hcard)⟩

end CFSG.Quasithin.Ch3E213M
