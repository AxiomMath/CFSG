module

public import CFSG.Milestones.ASVolI.F45.TitsLoc
public import CFSG.Milestones.ASVolI.F45.Six
public import CFSG.Milestones.ASVolI.F4Sylow
public import CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType
  CFSG.Sporadic.Schreier.Tits CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ExceptionalRoots CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

theorem burnsideF45_card_eq_of_equiv {E X : Type*} [Group E] [Group X] {A : Subgroup E}
    {B : Subgroup X} (θ : ↥A ≃* ↥B) {K : Subgroup E} {L : Subgroup X} (hK : K ≤ A) (hL : L ≤ B)
    (h : ∀ x : ↥A, (x : E) ∈ K ↔ ((θ x : ↥B) : X) ∈ L) : Nat.card K = Nat.card L :=
  Nat.card_congr
    { toFun := fun k => ⟨θ ⟨k, hK k.2⟩, (h _).1 k.2⟩
      invFun := fun l =>
        ⟨θ.symm ⟨l, hL l.2⟩, (h _).2 (by rw [MulEquiv.apply_symm_apply]; exact l.2)⟩
      left_inv := fun k => by
        apply Subtype.ext
        simp
      right_inv := fun l => by
        apply Subtype.ext
        simp }

section Theta


theorem burnsideF45_tits_theta {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Tits 2 1 Gp M₁ M₂) :
    ∃ θ : ↥(M₁ ⊔ M₂) ≃* ↥(titsH ⊔ titsN),
      (∀ x : ↥(M₁ ⊔ M₂),
        (x : E) ∈ M₁ ↔ ((θ x : ↥(titsH ⊔ titsN)) : Equiv.Perm (Fin 1755)) ∈ titsH) ∧
      (∀ x : ↥(M₁ ⊔ M₂),
        (x : E) ∈ M₂ ↔ ((θ x : ↥(titsH ⊔ titsN)) : Equiv.Perm (Fin 1755)) ∈ titsN) := by
  have hyp4 := hyp.toHypF_4_4g
  have hGp : Gp = ⊤ := hyp.canonical (Or.inr rfl)
  obtain ⟨K, fK, finK, charK, hscope, marking, h1, h2⟩ := burnsideF4gF4Two_chart_tits hyp4
  letI := fK
  haveI := finK
  haveI : CharP K F4.prime := charK
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := hscope
  have hK : Nat.card K = 2 := by simpa using hK'
  obtain ⟨Φ, hΦ⟩ := burnsideF4gF4Two_key hK
  let e1 : ↥(reeGroup K 0) ≃* Gm K 0 := MulEquiv.subgroupCongr burnsideF4gF4Two_reeGroup_eq
  let Φ' : ↥(reeGroup K 0) ≃* ↥twoF4M := e1.trans Φ
  obtain ⟨Θ, hΘ⟩ := burnsideF4gF4Two_commutator_equiv (reeGroup K 0) Φ'
  have hZ : Subgroup.center ↥⁅reeGroup K 0, reeGroup K 0⁆ = ⊥ := by
    have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv Θ
    rw [titsD_center] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ Θ.injective).1 h
  obtain ⟨eC, heC⟩ := burnsideF4gF4Two_exists_derivedEquiv (reeGroup K 0)
    ⁅reeGroup K 0, reeGroup K 0⁆ rfl hZ
  let Ψ : ↥Gp ≃* ↥titsD := marking.symm.trans (eC.trans Θ)
  have hsup : M₁ ⊔ M₂ = Gp := hyp4.gen.trans hGp.symm
  let θ : ↥(M₁ ⊔ M₂) ≃* ↥(titsH ⊔ titsN) :=
    (MulEquiv.subgroupCongr hsup).trans (Ψ.trans (MulEquiv.subgroupCongr titsH_sup_N.symm))
  have hle : ⁅reeGroup K 0, reeGroup K 0⁆ ≤ reeGroup K 0 := Subgroup.commutator_le_self _
  have hM : ∀ (M : Subgroup E) (P : Subgroup (ModGL Tag.F4 K)),
      M.subgroupOf Gp = (derivedImage (reeGroup K 0) P).map marking.toMonoidHom →
      ∀ y : ↥Gp, (y : E) ∈ M ↔
        (((eC (marking.symm y) : ↥⁅reeGroup K 0, reeGroup K 0⁆) : ModGL Tag.F4 K) ∈ P) := by
    intro M P hMP y
    have hy : (y : E) ∈ M ↔ y ∈ M.subgroupOf Gp := Iff.rfl
    have h3 := burnsideF4gF4Two_map_derivedImage (reeGroup K 0) ⁅reeGroup K 0, reeGroup K 0⁆ P rfl
      eC heC
    have h4 : ∀ z : DerivedCentralQuotient (reeGroup K 0),
        z ∈ derivedImage (reeGroup K 0) P ↔
          ((eC z : ↥⁅reeGroup K 0, reeGroup K 0⁆) : ModGL Tag.F4 K) ∈ P := by
      intro z
      have h5 : eC z ∈ (derivedImage (reeGroup K 0) P).map eC.toMonoidHom ↔
          z ∈ derivedImage (reeGroup K 0) P := by
        rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
      rw [← h5, h3]
      exact Iff.rfl
    rw [hy, hMP, Subgroup.mem_map_equiv]
    exact h4 _
  have hM₁ : ∀ y : ↥Gp, (y : E) ∈ M₁ ↔
      (e1 ⟨(eC (marking.symm y) : ↥⁅reeGroup K 0, reeGroup K 0⁆),
        hle (eC (marking.symm y)).2⟩ : Gm K 0) ∈ (burnsideF4gF4Two_system hK).P₁ := fun y =>
    (hM M₁ _ h1 y).trans (burnsideF4gF4Two_mem_P₁_iff hK (e1 ⟨(eC (marking.symm y) :
      ↥⁅reeGroup K 0, reeGroup K 0⁆), hle (eC (marking.symm y)).2⟩)).symm
  have hM₂ : ∀ y : ↥Gp, (y : E) ∈ M₂ ↔
      (e1 ⟨(eC (marking.symm y) : ↥⁅reeGroup K 0, reeGroup K 0⁆),
        hle (eC (marking.symm y)).2⟩ : Gm K 0) ∈ (burnsideF4gF4Two_system hK).P₂ := fun y =>
    (hM M₂ _ h2 y).trans (burnsideF4gF4Two_mem_P₂_iff hK (e1 ⟨(eC (marking.symm y) :
      ↥⁅reeGroup K 0, reeGroup K 0⁆), hle (eC (marking.symm y)).2⟩)).symm
  have hz : ∀ (P : Subgroup (Gm K 0)) (z : Gm K 0), Φ z ∈ P.map Φ.toMonoidHom ↔ z ∈ P := by
    intro P z
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hΨ : ∀ y : ↥Gp, ((Ψ y : ↥titsD) : Equiv.Perm (Fin 1755)) =
      ((Φ (e1 ⟨(eC (marking.symm y) : ↥⁅reeGroup K 0, reeGroup K 0⁆),
        hle (eC (marking.symm y)).2⟩) : ↥twoF4M) : Equiv.Perm (Fin 1755)) := fun y =>
    hΘ (eC (marking.symm y))
  have hH : ∀ g : ↥titsD, (g : Equiv.Perm (Fin 1755)) ∈ twoF4H ↔
      (g : Equiv.Perm (Fin 1755)) ∈ titsH := fun g =>
    ⟨fun hg => mem_of_mem_extSub_of_mem_D titsH_le_titsD hg g.2, fun hg => Or.inl hg⟩
  have hN : ∀ g : ↥titsD, (g : Equiv.Perm (Fin 1755)) ∈ twoF4N ↔
      (g : Equiv.Perm (Fin 1755)) ∈ titsN := fun g =>
    ⟨fun hg => mem_of_mem_extSub_of_mem_D titsN_le_titsD hg g.2, fun hg => Or.inl hg⟩
  rcases hΦ with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
  · have k1 : ∀ z : Gm K 0, z ∈ (burnsideF4gF4Two_system hK).P₁ ↔
        ((Φ z : ↥twoF4M) : Equiv.Perm (Fin 1755)) ∈ twoF4H := by
      intro z
      rw [← hz _ z, hp1]
      exact Iff.rfl
    have k2 : ∀ z : Gm K 0, z ∈ (burnsideF4gF4Two_system hK).P₂ ↔
        ((Φ z : ↥twoF4M) : Equiv.Perm (Fin 1755)) ∈ twoF4N := by
      intro z
      rw [← hz _ z, hp2]
      exact Iff.rfl
    refine ⟨θ, fun x => (hM₁ (MulEquiv.subgroupCongr hsup x)).trans ((k1 _).trans ?_),
      fun x => (hM₂ (MulEquiv.subgroupCongr hsup x)).trans ((k2 _).trans ?_)⟩
    · rw [← hΨ]
      exact hH _
    · rw [← hΨ]
      exact hN _
  · exfalso
    have k1 : ∀ z : Gm K 0, z ∈ (burnsideF4gF4Two_system hK).P₁ ↔
        ((Φ z : ↥twoF4M) : Equiv.Perm (Fin 1755)) ∈ twoF4N := by
      intro z
      rw [← hz _ z, hp1]
      exact Iff.rfl
    have hA : ∀ x : ↥(M₁ ⊔ M₂),
        (x : E) ∈ M₁ ↔ ((θ x : ↥(titsH ⊔ titsN)) : Equiv.Perm (Fin 1755)) ∈ titsN := fun x =>
      (hM₁ (MulEquiv.subgroupCongr hsup x)).trans ((k1 _).trans (by rw [← hΨ]; exact hN _))
    have hc := burnsideF45_card_eq_of_equiv θ le_sup_left le_sup_right hA
    rw [titsQN_facts.2.2.2] at hc
    obtain ⟨hq1, -⟩ := burnsideF45_q_Tits hyp hGp
    rw [burnsideF45_qOne_eq] at hq1
    have hdvd := Subgroup.relIndex_dvd_card (M₁ ⊓ M₂) M₁
    rw [hc, show (M₁ ⊓ M₂).relIndex M₁ = 5 by omega] at hdvd
    norm_num at hdvd

end Theta

section Model

open CFSG.Quasithin.TitsGeo CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.H13.F431


theorem burnsideF45_titsData {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Tits p f Gp M₁ M₂) : burnsideF45_TitsData (incl M₁ M₂) := by
  obtain ⟨hp2, hf1, -⟩ := hyp.model
  subst hp2
  subst hf1
  have hGp : Gp = ⊤ := hyp.canonical (Or.inr rfl)
  haveI : Finite E := hyp.finite
  obtain ⟨θ, hθ1, hθ2⟩ := burnsideF45_tits_theta hyp
  obtain ⟨-, -, -, -, -, hPt, ⟨_, hAff⟩, hLn, hpoly⟩ :=
    tits_geometry Certificates.certificate4190
  have h00 : (0 : Fin 1755) ∈ titsLine (0 : Fin 2925) := octGraph_adj_inl_inr.1 hPt.adj
  have hsup : M₁ ⊔ M₂ = Gp := hyp.gen.trans hGp.symm
  let θ' : ↥titsD ≃* ↥Gp :=
    (MulEquiv.subgroupCongr titsH_sup_N.symm).trans (θ.symm.trans (MulEquiv.subgroupCongr hsup))
  have hst1 : ∀ y : ↥titsD, ((θ' y : ↥Gp) : E) ∈ M₁ ↔ (y : Equiv.Perm (Fin 1755)) ∈ titsH := by
    intro y
    have := hθ1 (θ.symm (MulEquiv.subgroupCongr titsH_sup_N.symm y))
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hst2 : ∀ y : ↥titsD, ((θ' y : ↥Gp) : E) ∈ M₂ ↔ (y : Equiv.Perm (Fin 1755)) ∈ titsN := by
    intro y
    have := hθ2 (θ.symm (MulEquiv.subgroupCongr titsH_sup_N.symm y))
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hH : ∀ y : ↥titsD, (y : Equiv.Perm (Fin 1755)) ∈ titsH ↔
      y • (Sum.inl 0 : Vtx) = Sum.inl 0 := by
    intro y
    rw [← (xdatumD h00).stab1 y, smul_xv_iff', TitsGeo.mem_range_φ1_iff, toPermD_phiD]
  have hN : ∀ y : ↥titsD, (y : Equiv.Perm (Fin 1755)) ∈ titsN ↔
      y • (Sum.inr 0 : Vtx) = Sum.inr 0 := by
    intro y
    rw [← (xdatumD h00).stab2 y, smul_lv_iff', TitsGeo.mem_range_φ2_iff, toPermD_phiD]
  have hm : 3 ≤ GLKind.Tits.m := burnsideF45_three_le_m _
  have D := burnsideF45_xdatum_of_model hyp Nat.prime_two hm θ' (ΓM := octGraph)
    (v₁ := (Sum.inl 0 : Vtx)) (v₂ := Sum.inr 0)
    (fun y => (hst1 y).trans (hH y)) (fun y => (hst2 y).trans (hN y))
    (fun y z => by rw [dsmul_inl, dsmul_inr]; exact Sum.inl_ne_inr)
    (fun y z => by rw [dsmul_inl, dsmul_inl]; exact fun h => h)
    (fun y z => by rw [dsmul_inr, dsmul_inr]; exact fun h => h) hPt.adj
  have f₁ : ∀ b, octGraph.Adj (Sum.inl 0) b →
      ∃ y : ↥titsD, y • (Sum.inl 0 : Vtx) = Sum.inl 0 ∧ y • (Sum.inr 0 : Vtx) = b :=
    fun b hb => (hPt.trans b hb).imp fun k hk => ⟨hk.1, hk.2.2⟩
  have f₂ : ∀ b, octGraph.Adj (Sum.inr 0) b →
      ∃ y : ↥titsD, y • (Sum.inr 0 : Vtx) = Sum.inr 0 ∧ y • (Sum.inl 0 : Vtx) = b :=
    fun b hb => hLn.flag hPt.adj.symm hb
  obtain ⟨e, he1, he2, heq, hadjE⟩ := D.exists_equiv (F45.cov_of_flags hpoly.connected f₁ f₂) f₁
  have hsurj : Function.Surjective (burnsideF45_Phi hyp θ') := by
    intro g
    have hg : g ∈ (burnsideF45_setting hyp Nat.prime_two hm).N := by
      show toE (incl M₁ M₂) g ∈ Gp
      rw [hGp]
      exact Subgroup.mem_top _
    rw [D.N_eq] at hg
    exact hg
  have EQ : EqData (burnsideF45_Phi hyp θ') e octGraph (incl M₁ M₂).graph := ⟨hsurj, heq, hadjE⟩
  have he1' : e (incl M₁ M₂).xv = Sum.inl 0 := he1
  have he2' : e (incl M₁ M₂).lv = Sum.inr 0 := he2
  have tPt : ∀ b : Vtx, PtLoc ↥titsD octGraph (Sum.inl 0) b (Sum.inr 0) →
      ∃ b', PtLoc (incl M₁ M₂).G0 (incl M₁ M₂).graph (incl M₁ M₂).xv b' (incl M₁ M₂).lv :=
    fun b h => ⟨e.symm b, PtLoc.transport EQ (by rw [he1', he2', Equiv.apply_symm_apply]; exact h)⟩
  have tAff : ∀ lab : ZMod 5 → Vtx, AffLab ↥titsD octGraph (Sum.inl 0) lab →
      ∃ lab', AffLab (incl M₁ M₂).G0 (incl M₁ M₂).graph (incl M₁ M₂).xv lab' :=
    fun lab h => ⟨_, AffLab.transport EQ (a := (incl M₁ M₂).xv) (by rw [he1']; exact h)⟩
  have tLn : ∀ b₇ b₁ b₂ : Vtx, LnLoc ↥titsD octGraph (Sum.inr 0) b₇ b₁ b₂ →
      ∃ b₇' b₁' b₂', LnLoc (incl M₁ M₂).G0 (incl M₁ M₂).graph (incl M₁ M₂).lv b₇' b₁' b₂' :=
    fun b₇ b₁ b₂ h => ⟨e.symm b₇, e.symm b₁, e.symm b₂,
      LnLoc.transport EQ (by rw [he2']; simpa using h)⟩
  let iso : (incl M₁ M₂).graph ≃g octGraph := ⟨e, fun {a b} => (hadjE a b).symm⟩
  have hpolyι : IsGenPolygon (incl M₁ M₂).graph 8 := IsGenPolygon.of_iso iso hpoly
  have cardx : Nat.card (stv (incl M₁ M₂) (incl M₁ M₂).xv) = 10240 := by
    rw [card_stv_xv (incl M₁ M₂) (incl_faithful M₁ M₂)]
    show Nat.card ↥M₁ = 10240
    rw [burnsideF45_card_eq_of_equiv θ le_sup_left le_sup_left hθ1]
    exact titsQH_facts.2.2.2
  have cardl : Nat.card (stv (incl M₁ M₂) (incl M₁ M₂).lv) = 6144 := by
    have h : stv (incl M₁ M₂) (incl M₁ M₂).lv = (f2 (c := incl M₁ M₂)).range := by
      ext g
      exact burnsideF45_mem_stv_lv_iff (incl M₁ M₂) g
    rw [h, ← Nat.card_congr (MonoidHom.ofInjective
      (f2_injective (incl M₁ M₂) (incl_faithful M₁ M₂))).toEquiv]
    show Nat.card ↥M₂ = 6144
    rw [burnsideF45_card_eq_of_equiv θ le_sup_right le_sup_right hθ2]
    exact titsQN_facts.2.2.2
  exact ⟨incl_faithful M₁ M₂, hpolyι, tPt _ hPt, tAff _ hAff, tLn _ _ _ hLn, cardx, cardl⟩

end Model

end CFSG.ASVolI
