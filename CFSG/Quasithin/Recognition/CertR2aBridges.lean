module

public import CFSG.Quasithin.Recognition.CertG2TwoOuter
public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Quasithin.Recognition.CertTwoLocalPair

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.QuasithinUnique

theorem map_commutator_top {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : (commutator G).map f = commutator H := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
    MonoidHom.range_eq_top.2 hf]

theorem commutator_mulEquiv {V Q : Type*} [Group V] [Group Q] (e : V ≃* Q) :
    Nonempty (↥(commutator V) ≃* ↥(commutator Q)) := by
  have h : (commutator V).map e.toMonoidHom = commutator Q :=
    map_commutator_top e.toMonoidHom e.surjective
  exact ⟨(Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr h)⟩

theorem center_eq_bot_of_simple_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ x y : G, x * y ≠ y * x) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨x, y, hxy⟩ := h
    have hx : x ∈ Subgroup.center G := by rw [h1]; trivial
    exact hxy ((Subgroup.mem_center_iff.1 hx y).symm)

theorem u33G_nonabelian
    : ∃ x y : U33G, x * y ≠ y * x := by
  obtain ⟨x, y, hxy⟩ := u33J_nonabelian
  refine ⟨u33ToJ.symm x, u33ToJ.symm y, fun h => hxy ?_⟩
  have := congrArg u33ToJ h
  simpa using this

theorem center_u33G
    : Subgroup.center U33G = ⊥ := by
  have := isSimpleGroup_u33Pres
  exact center_eq_bot_of_simple_nonabelian u33G_nonabelian

section G2

variable {k : Type} [Field k]

theorem g2_commutator_eq_range
    (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1) :
    commutator (G2Group k) = (g2HomC h2).range := by
  apply Subgroup.map_injective (Subgroup.subtype_injective (adjointGroup Tag.G2 k))
  rw [Subgroup.map_subtype_commutator, g2_derived_eq_range h2 hk2, ← MonoidHom.range_comp]
  rfl

theorem g2_quotient_injective
    (h2 : (2 : k) = 0) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center (G2Group k))).comp (g2HomC h2)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  have hcen : x ∈ Subgroup.center U33G := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply g2HomC_injective h2
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hx (g2HomC h2 y)
  rw [center_u33G] at hcen
  exact hcen

theorem g2_quotient_commutator_equiv
    (k : Type) [Field k] [Finite k] (hk : Nat.card k = 2) :
    Nonempty (↥(commutator (AdjointQuotient Tag.G2 k)) ≃* PSU3 3 1) := by
  have h2 := two_eq_zero_of_card_two hk
  have hk2 := eq_zero_or_eq_one_of_card_two hk
  obtain ⟨e⟩ := u33Pres_mulEquiv_PSU3
  set ψ := (QuotientGroup.mk' (Subgroup.center (G2Group k))).comp (g2HomC h2) with hψ
  have hrange : ψ.range = commutator (AdjointQuotient Tag.G2 k) := by
    rw [hψ, MonoidHom.range_comp, ← g2_commutator_eq_range h2 hk2]
    exact map_commutator_top _ (QuotientGroup.mk'_surjective _)
  exact ⟨((MonoidHom.ofInjective (g2_quotient_injective h2)).trans
    (MulEquiv.subgroupCongr hrange)).symm.trans e⟩

end G2

theorem isG22Prime_equiv
    (W : Type) [Group W] (h : F6.IsG22Prime W) :
    Nonempty (W ≃* PSU3 3 1) := by
  obtain ⟨V, _, ⟨K, _, _, hK, ⟨eV⟩⟩, ⟨eW⟩⟩ := h
  obtain ⟨c⟩ := commutator_mulEquiv eV
  obtain ⟨d⟩ := g2_quotient_commutator_equiv K hK
  exact ⟨eW.trans (c.trans d)⟩

theorem g22Prime_bridge
    (D : Type) [Group D] [Finite D] (H₁ H₂ : Subgroup D)
    (h : F6.IsYAmalgam F6.IsG22Prime H₁ H₂) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂)
      (fun Y _ => Nonempty (Y ≃* PSU3 3 1)) := by
  refine f6_bridge_of_pair (IsY := F6.IsG22Prime)
    (P := fun Y _ => Nonempty (Y ≃* PSU3 3 1)) (fun W _ _ hW => isG22Prime_equiv W hW)
    (fun W _ _ hW => ?_) D H₁ H₂ h
  obtain ⟨e⟩ := isG22Prime_equiv W hW
  obtain ⟨f⟩ := u33Pres_mulEquiv_PSU3
  have : Finite U33G := u33Pres_finite_card_le.1
  exact TwoLocalPairProp.of_mulEquiv (e.trans f.symm).symm u33Extra.twoLocalPairProp

section Aut

variable {k : Type} [Field k]

theorem normal_range_g2HomC
    (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1) :
    ((g2HomC h2).range).Normal :=
  Subgroup.normal_of_index_eq_two (g2IndexTwoData h2 hk2).index_range

noncomputable def g2Action
    (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1) :
    G2Group k →* MulAut U33G :=
  haveI := normal_range_g2HomC h2 hk2
  (MulAut.congr (MonoidHom.ofInjective (g2HomC_injective h2)).symm).toMonoidHom.comp
    MulAut.conjNormal

theorem g2HomC_action
    (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1) (c : G2Group k)
    (x : U33G) : g2HomC h2 (g2Action h2 hk2 c x) = c * g2HomC h2 x * c⁻¹ := by
  have := normal_range_g2HomC h2 hk2
  simp [g2Action, MulAut.congr_apply, MonoidHom.apply_ofInjective_symm,
    MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

theorem g2Action_injective
    (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1) :
    Function.Injective (g2Action h2 hk2) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro c hc
  rw [MonoidHom.mem_ker] at hc
  have hcomm : ∀ x : U33G, c * g2HomC h2 x = g2HomC h2 x * c := by
    intro x
    have h := g2HomC_action h2 hk2 c x
    rw [hc, MulAut.one_apply] at h
    calc c * g2HomC h2 x = (c * g2HomC h2 x * c⁻¹) * c := by group
      _ = g2HomC h2 x * c := by rw [← h]
  have D := g2IndexTwoData h2 hk2
  rcases D.cover c with ⟨r, hr⟩ | ⟨r, hr⟩
  ·
    have hcen : r ∈ Subgroup.center U33G := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply g2HomC_injective h2
      rw [map_mul, map_mul, hr]
      exact (hcomm y).symm
    rw [center_u33G] at hcen
    rw [Subgroup.mem_bot.1 hcen, map_one] at hr
    exact Subgroup.mem_bot.2 hr.symm
  ·
    exfalso
    apply u33Phi'_not_inner
    refine ⟨r⁻¹, fun x => ?_⟩
    apply g2HomC_injective h2
    have hρ : g2RhoC h2 * g2RhoC h2 = 1 := D.sq
    have hc : c = g2HomC h2 r * g2RhoC h2 := by
      calc c = c * (g2RhoC h2 * g2RhoC h2) := by rw [hρ, mul_one]
        _ = g2HomC h2 r * g2RhoC h2 := by rw [← mul_assoc, hr]
    have h1 := hcomm x
    rw [hc] at h1
    have h3 : g2RhoC h2 * g2HomC h2 x * (g2RhoC h2)⁻¹ = g2HomC h2 (u33Phi' x) := D.conj x
    calc g2HomC h2 (u33Phi' x) = g2RhoC h2 * g2HomC h2 x * (g2RhoC h2)⁻¹ := h3.symm
      _ = (g2HomC h2 r)⁻¹ * (g2HomC h2 r * g2RhoC h2 * g2HomC h2 x) * (g2RhoC h2)⁻¹ := by group
      _ = (g2HomC h2 r)⁻¹ * (g2HomC h2 x * (g2HomC h2 r * g2RhoC h2)) * (g2RhoC h2)⁻¹ := by
          rw [h1]
      _ = g2HomC h2 (r⁻¹ * x * r⁻¹⁻¹) := by
          simp only [map_mul, map_inv]
          group

theorem card_g2Group
    (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1) :
    Nat.card (G2Group k) = 12096 := by
  have D := g2IndexTwoData h2 hk2
  have h1 := Subgroup.card_mul_index (g2HomC h2).range
  rw [D.index_range] at h1
  have h3 : Nat.card (g2HomC h2).range = 6048 := by
    rw [← card_u33Pres]
    exact (Nat.card_congr (MonoidHom.ofInjective (g2HomC_injective h2)).toEquiv).symm
  omega

theorem g2Action_bijective
    [Finite k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1) :
    Function.Bijective (g2Action h2 hk2) := by
  have : Finite U33G := u33Pres_finite_card_le.1
  refine (g2Action_injective h2 hk2).bijective_of_nat_card_le ?_
  rw [card_g2Group h2 hk2]
  exact card_mulAut_u33Pres_le

theorem g2Group_mulEquiv_aut
    (k : Type) [Field k] [Finite k] (hk : Nat.card k = 2) :
    Nonempty (G2Group k ≃* MulAut (PSU3 3 1)) := by
  have h2 := two_eq_zero_of_card_two hk
  have hk2 := eq_zero_or_eq_one_of_card_two hk
  obtain ⟨e⟩ := u33Pres_mulEquiv_PSU3
  exact ⟨(MulEquiv.ofBijective (g2Action h2 hk2) (g2Action_bijective h2 hk2)).trans
    (MulAut.congr e)⟩

theorem center_g2Group
    (k : Type) [Field k] [Finite k] (hk : Nat.card k = 2) :
    Subgroup.center (G2Group k) = ⊥ := by
  have h2 := two_eq_zero_of_card_two hk
  have hk2 := eq_zero_or_eq_one_of_card_two hk
  rw [eq_bot_iff]
  intro z hz
  have hz' := Subgroup.mem_center_iff.1 hz
  have : g2Action h2 hk2 z = 1 := by
    ext x
    apply g2HomC_injective h2
    rw [g2HomC_action, MulAut.one_apply]
    have := hz' (g2HomC h2 x)
    calc z * g2HomC h2 x * z⁻¹ = g2HomC h2 x * z * z⁻¹ := by rw [this]
      _ = g2HomC h2 x := by group
  exact Subgroup.mem_bot.2 (g2Action_injective h2 hk2 (this.trans (map_one _).symm))

end Aut

theorem isG22_equiv_g2Group
    (W : Type) [Group W] (h : F6.IsG22 W) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧ Nonempty (W ≃* G2Group K) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK,
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq (center_g2Group K hK)).trans
      QuotientGroup.quotientBot)⟩⟩

theorem g22_bridge
    (D : Type) [Group D] [Finite D] (H₁ H₂ : Subgroup D)
    (h : F6.IsYAmalgam F6.IsG22 H₁ H₂) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂) (IsG2Over 1) := by
  refine f6_bridge_of_pair (IsY := F6.IsG22) (P := IsG2Over 1) (fun W _ _ hW => ?_)
    (fun W _ _ hW => ?_) D H₁ H₂ h
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := isG22_equiv_g2Group W hW
    obtain ⟨f⟩ := g2Group_mulEquiv_aut K hK
    exact Or.inl ⟨rfl, ⟨e.trans f⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := isG22_equiv_g2Group W hW
    exact TwoLocalPairProp.of_mulEquiv e.symm (g2_twoLocalPairProp K hK)

end CFSG.Quasithin
