module

public import CFSG.Monster.Existence.Defs
public import CFSG.Monster.Existence.Co1Bridge
public import CFSG.Monster.Generated.FiniteSimple
public import CFSG.Monster.B.Cbar.FourGroupSpin

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG CFSG.Monster CFSG.Monster.Spin CFSG.Monster.Griess CFSG.Monster.Visible
  CFSG.Monster.Generated Subgroup

theorem center_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (center G).map e.toMonoidHom = center H := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro hx g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx]
  · intro hx g
    apply e.injective
    rw [map_mul, map_mul, hx]

theorem IsExtraspecialPGroup.of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : IsExtraspecialPGroup p G) : IsExtraspecialPGroup p H := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hc : (commutator G).map e.toMonoidHom = commutator H := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hf : (frattini G).map e.toMonoidHom = frattini H :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hc, hcomm, center_map_mulEquiv]
  · rw [← hf, hfrat, center_map_mulEquiv]
  · rw [← center_map_mulEquiv e, Subgroup.card_map_of_injective e.injective, hcard]

theorem natCard_rhoQvis : Nat.card rhoQvis = 2 ^ 25 := by
  rw [← natCard_Q, Nat.card_congr rhoIso.toEquiv, Nat.card_congr MulOpposite.opEquiv.symm]

noncomputable def rhoQvisEquivQ : rhoQvis ≃* Q :=
  (MulEquiv.inv' rhoQvis).trans rhoIso.symm

theorem isExtraspecialPGroup_rhoQvis : IsExtraspecialPGroup 2 rhoQvis :=
  IsExtraspecialPGroup.of_mulEquiv rhoQvisEquivQ.symm isExtraspecialPGroup_Q

theorem natCard_visQuot_eq :
    Nat.card (Gvis ⧸ rhoQvis) = 4157776806543360000 :=
  VisQuot.natCard_visQuot

theorem natCard_Gvis :
    Nat.card Gvis = twoBCentralizerOrder := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup rhoQvis, natCard_visQuot_eq,
    natCard_rhoQvis, twoBCentralizerOrder]
  norm_num

theorem pCore_Gvis :
    pCore 2 Gvis = rhoQvis := by
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, IsPGroup.of_card natCard_rhoQvis⟩)
  have hsimple : IsSimpleGroup (Gvis ⧸ rhoQvis) := VisQuot.isSimpleGroup_visQuot
  have hfin : Finite (Gvis ⧸ rhoQvis) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_visQuot_eq]; norm_num)
  set f := QuotientGroup.mk' rhoQvis
  have hn : ((pCore 2 Gvis).map f).Normal :=
    Subgroup.Normal.map pCore_normal f (QuotientGroup.mk'_surjective _)
  have hp : IsPGroup 2 ((pCore 2 Gvis).map f) := IsPGroup.map pCore_isPGroup f
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · rw [← QuotientGroup.ker_mk' rhoQvis, ← Subgroup.map_eq_bot_iff]
    exact hbot
  · exfalso
    rw [htop] at hp
    have hp' : IsPGroup 2 (Gvis ⧸ rhoQvis) :=
      hp.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn'⟩ := (IsPGroup.iff_card (p := 2)).1 hp'
    rw [natCard_visQuot_eq] at hn'
    have h3 : 3 ∣ 2 ^ n := by rw [← hn']; norm_num
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) (by norm_num)).1
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h3))
    omega

theorem centralizer_rhoQvis_le : Subgroup.centralizer (rhoQvis : Set Gvis) ≤ rhoQvis := by
  intro g hg
  rw [← ker_conjVis, MonoidHom.mem_ker]
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [conjVis_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    change g * (x : Gvis) * g⁻¹ = x
    rw [← Subgroup.mem_centralizer_iff.1 hg x x.2, mul_inv_cancel_right]

variable {G : Type} [Group G]

theorem self_mem_cent (z : G) : z ∈ cent z := Subgroup.mem_centralizer_singleton_iff.2 rfl

theorem isTwoBCentralizer_of_equiv
    (z : G) (e : cent z ≃* Gvis)
    (he : ((e ⟨z, self_mem_cent z⟩ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = xmat) :
    IsTwoBCentralizer z := by
  have hmap : (pCore 2 (cent z)).map e.toMonoidHom = rhoQvis := by
    rw [pCore_map_iso 2 e, pCore_Gvis]
  let eQ : pCore 2 (cent z) ≃* rhoQvis :=
    ((pCore 2 (cent z)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have mem_iff : ∀ y : cent z, y ∈ pCore 2 (cent z) ↔ e y ∈ rhoQvis := by
    intro y
    rw [← hmap, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  refine ⟨IsExtraspecialPGroup.of_mulEquiv eQ.symm isExtraspecialPGroup_rhoQvis, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr eQ.toEquiv, natCard_rhoQvis]
  · intro g hg
    have hz : (⟨z, self_mem_cent z⟩ : cent z) ∈ pCore 2 (cent z) := by
      rw [mem_iff]
      exact Subgroup.mem_subgroupOf.2 (he ▸ xmat_mem_Qmat)
    have hgz : g ∈ cent z := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hg z ⟨_, hz, rfl⟩).symm
    have hcent : e ⟨g, hgz⟩ ∈ Subgroup.centralizer (rhoQvis : Set Gvis) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      obtain ⟨q, hq, rfl⟩ : ∃ q : cent z, q ∈ pCore 2 (cent z) ∧ e q = r := by
        refine ⟨e.symm r, ?_, e.apply_symm_apply r⟩
        rw [mem_iff, e.apply_symm_apply]
        exact hr
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hg q ⟨q, hq, rfl⟩
    have hmem : (⟨g, hgz⟩ : cent z) ∈ pCore 2 (cent z) :=
      (mem_iff _).2 (centralizer_rhoQvis_le hcent)
    exact ⟨_, hmem, rfl⟩
  · exact ⟨(QuotientGroup.congr _ _ e hmap).trans Co1Bridge.visQuotEquivCo1⟩
  · rw [Nat.card_congr e.toEquiv, natCard_Gvis]
  · rw [Nat.card_congr e.toEquiv, natCard_Gvis, twoBCentralizerOrder]
    norm_num

@[expose] noncomputable def centConjEquiv (g z : G) : cent (g * z * g⁻¹) ≃* cent z where
  toFun x := ⟨g⁻¹ * x * g, by
    have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hx]
      _ = z * (g⁻¹ * x * g) := by group⟩
  invFun y := ⟨g * y * g⁻¹, by
    have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
      _ = g * (z * y) * g⁻¹ := by rw [hy]
      _ = g * z * g⁻¹ * (g * y * g⁻¹) := by group⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem isTwoBCentralizer_of_isConj
    (z : G) (e : cent z ≃* Gvis)
    (he : ((e ⟨z, self_mem_cent z⟩ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = xmat) (ζ : G)
    (hζ : IsConj z ζ) : IsTwoBCentralizer ζ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hζ
  refine isTwoBCentralizer_of_equiv _ ((centConjEquiv c z).trans e) ?_
  have : centConjEquiv c z ⟨c * z * c⁻¹, self_mem_cent _⟩ = ⟨z, self_mem_cent z⟩ :=
    Subtype.ext (by simp [centConjEquiv, mul_assoc])
  rw [MulEquiv.trans_apply, this, he]

theorem xmat_mem_AutO : xmat ∈ AutO := Hmat_le_AutO (Qmat_le_Hmat xmat_mem_Qmat)

@[expose] noncomputable def xGriess : MGriess := ⟨xmat, xmat_mem_AutO⟩

theorem map_cent_xGriess : (cent xGriess).map AutO.subtype = Gvis := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hh
    refine (mem_Hmat_iff_of_mem_AutO h.2).2 ?_
    exact (congrArg Subtype.val hc).symm
  · intro hg
    refine ⟨⟨g, Gvis_le_AutO hg⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext ((mem_Hmat_iff_of_mem_AutO (Gvis_le_AutO hg)).1 hg).symm

noncomputable def centGriessEquiv : cent xGriess ≃* Gvis :=
  ((cent xGriess).equivMapOfInjective AutO.subtype AutO.subtype_injective).trans
    (MulEquiv.subgroupCongr map_cent_xGriess)

theorem isTwoBCentralizer_MGriess
    (ζ : MGriess) (hζ : IsConj xGriess ζ) : IsTwoBCentralizer ζ :=
  isTwoBCentralizer_of_isConj xGriess centGriessEquiv rfl ζ hζ

@[expose] noncomputable def xGmat : Gmat := ⟨xmat, Hmat_le_Gmat (Qmat_le_Hmat xmat_mem_Qmat)⟩

theorem map_cent_xGmat : (cent xGmat).map Gmat.subtype = Gvis := by
  rw [← Hmat, ← Gmat_inf_centralizer_xmat]
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hh)
  · rintro ⟨hg, hc⟩
    refine ⟨⟨g, hg⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hc)

noncomputable def centGmatEquiv : cent xGmat ≃* Gvis :=
  ((cent xGmat).equivMapOfInjective Gmat.subtype Gmat.subtype_injective).trans
    (MulEquiv.subgroupCongr map_cent_xGmat)

theorem isTwoBCentralizer_Gmat
    (ζ : Gmat) (hζ : IsConj xGmat ζ) : IsTwoBCentralizer ζ :=
  isTwoBCentralizer_of_isConj xGmat centGmatEquiv rfl ζ hζ

theorem rhoQvisEquivQ_symm_zQ :
    ((rhoQvisEquivQ.symm zQ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = xmat := by
  have h : rhoQvisEquivQ.symm zQ = rhoN zQ := by
    apply rhoQvisEquivQ.injective
    rw [MulEquiv.apply_symm_apply]
    change zQ = rhoIso.symm (MulOpposite.op (rhoN zQ)⁻¹)
    have hinv : (rhoN zQ)⁻¹ = rhoN zQ := by
      rw [inv_eq_iff_mul_eq_one, ← rhoN_mul]
      have : zQ * zQ = 1 := by
        rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_zQ]
      rw [this, rhoN_one]
    rw [hinv, ← rhoIso_apply, MulEquiv.symm_apply_apply]
  rw [h, coe_coe_rhoN_zQ, xmat_eq_xB]

theorem center_rhoQvis : Subgroup.center rhoQvis = Subgroup.zpowers (rhoQvisEquivQ.symm zQ) :=
  Spin.center_eq_zpowers_of_mulEquiv rhoQvisEquivQ.symm center_Q

theorem Gmat_inf_centralizer_Qmat :
    Gmat ⊓ Subgroup.centralizer (Qmat : Set (SpaceB ≃ₗ[ℚ] SpaceB)) = Subgroup.zpowers xmat := by
  have hxQ : xmat ∈ Qmat := xmat_mem_Qmat
  have hxc : ∀ r ∈ Qmat, xmat * r = r * xmat := by
    intro r hr
    have hz : rhoQvisEquivQ.symm zQ ∈ Subgroup.center rhoQvis := by
      rw [center_rhoQvis]
      exact Subgroup.mem_zpowers _
    have := Subgroup.mem_center_iff.1 hz ⟨⟨r, Qmat_le_Hmat hr⟩, Subgroup.mem_subgroupOf.2 hr⟩
    have := congrArg (fun q : rhoQvis => ((q : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB)) this
    simp only [Subgroup.coe_mul, rhoQvisEquivQ_symm_zQ] at this
    exact this.symm
  apply le_antisymm
  · rintro g ⟨hgM, hgc⟩
    have hgx : g ∈ Hmat := by
      rw [← Gmat_inf_centralizer_xmat]
      exact ⟨hgM, Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hgc xmat hxQ).symm⟩
    have hcent : (⟨g, hgx⟩ : Gvis) ∈ Subgroup.centralizer (rhoQvis : Set Gvis) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hgc r (Subgroup.mem_subgroupOf.1 hr)
    have hmem := centralizer_rhoQvis_le hcent
    have hz : (⟨⟨g, hgx⟩, hmem⟩ : rhoQvis) ∈ Subgroup.center rhoQvis := by
      rw [Subgroup.mem_center_iff]
      intro r
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 hcent r r.2)
    rw [center_rhoQvis] at hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have := congrArg (fun q : rhoQvis => ((q : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB)) hk
    simpa [rhoQvisEquivQ_symm_zQ] using this
  · rw [Subgroup.zpowers_le]
    exact ⟨Hmat_le_Gmat (Qmat_le_Hmat hxQ),
      Subgroup.mem_centralizer_iff.2 fun r hr => (hxc r hr).symm⟩

theorem generated_group_Co1_local_recognition_hypotheses :
    Finite Gmat ∧ IsSimpleGroup Gmat ∧ (∃ g h : Gmat, g * h ≠ h * g) ∧
      Gmat ⊓ Subgroup.centralizer {xmat} = Hmat ∧
      pCore 2 Gvis = rhoQvis ∧ IsExtraspecialPGroup 2 rhoQvis ∧ Nat.card rhoQvis = 2 ^ 25 ∧
      Subgroup.center rhoQvis = Subgroup.zpowers (rhoQvisEquivQ.symm zQ) ∧
      ((rhoQvisEquivQ.symm zQ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = xmat ∧
      Nonempty (Gvis ⧸ rhoQvis ≃* Blueprint.NativeSporadic.Co1) ∧
      Gmat ⊓ Subgroup.centralizer (Qmat : Set (SpaceB ≃ₗ[ℚ] SpaceB)) = Subgroup.zpowers xmat ∧
      xmatTau ∈ Qmat ∧ xmatTau ∉ Subgroup.zpowers xmat := by
  obtain ⟨-, hfin, hcent, -, -, -, -, hx1, hxt1, -, hxxt, -, -, hconj, -, -⟩ :=
    generated_rational_group_finite_centralizer
  obtain ⟨-, hsimple, -⟩ := generated_rational_group_finite_simple
  refine ⟨hfin, hsimple, ?_, hcent, pCore_Gvis, isExtraspecialPGroup_rhoQvis, natCard_rhoQvis,
    center_rhoQvis, rhoQvisEquivQ_symm_zQ, ⟨Co1Bridge.visQuotEquivCo1⟩, Gmat_inf_centralizer_Qmat,
    ?_, ?_⟩
  · refine ⟨⟨tauB, tauB_mem_Gmat⟩, ⟨xmat, Hmat_le_Gmat (Qmat_le_Hmat xmat_mem_Qmat)⟩, ?_⟩
    intro h
    have h' : tauB * xmat * tauB⁻¹ = xmat := by
      have := congrArg Subtype.val h
      simp only [Subgroup.coe_mul] at this
      rw [this, mul_inv_cancel_right]
    exact hxxt (h'.symm.trans hconj)
  · obtain ⟨-, -, -, -, -, -, -, hV, -, -, -⟩ := B.triality_four_group_spin_identification
    exact hV (mem_Vmat.2 (Or.inr (Or.inr (Or.inl rfl))))
  · rw [CFSG.Monster.mem_zpowers_iff_of_orderOf_eq_two orderOf_xmat]
    rintro (h | h)
    · exact hxt1 h
    · exact hxxt h.symm

end CFSG.Monster.Existence
