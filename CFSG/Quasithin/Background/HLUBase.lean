module

public import CFSG.Quasithin.Background.HParabBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57M5D5

public section

namespace CFSG.Quasithin.H.LU

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.Parab CFSG.QuasithinUnique.B42A57 CFSG.QuasithinUnique.A5.Delta5
open scoped commutatorElement

variable {V W : Type*} [CommGroup V] [CommGroup W]

@[expose] def resEquiv (e : V ≃* W) {U : Subgroup V} {U' : Subgroup W}
    (hU : ∀ v, v ∈ U ↔ e v ∈ U') : ↥U ≃* ↥U' where
  toFun u := ⟨e (u : V), (hU u).1 u.2⟩
  invFun u := ⟨e.symm (u : W), (hU _).2 (by rw [e.apply_symm_apply]; exact u.2)⟩
  left_inv u := Subtype.ext (e.symm_apply_apply (u : V))
  right_inv u := Subtype.ext (e.apply_symm_apply (u : W))
  map_mul' a b := Subtype.ext (map_mul e (a : V) (b : V))

theorem mem_stabSub_congrHom (e : V ≃* W) {U : Subgroup V} {U' : Subgroup W}
    (hU : ∀ v, v ∈ U ↔ e v ∈ U') {g : MulAut V} : congrHom e g ∈ stabSub U' ↔ g ∈ stabSub U := by
  constructor
  · intro h v
    have h1 := h (e v)
    rw [congrHom_apply, e.symm_apply_apply] at h1
    rw [hU, hU v]
    exact h1
  · intro h w
    rw [congrHom_apply, ← hU, h, hU, e.apply_symm_apply]

theorem congrHom_symm_comp {S T : Type*} [CommGroup S] [CommGroup T] (f : S ≃* T) :
    (congrHom f.symm).comp (congrHom f) = MonoidHom.id (MulAut S) :=
  MonoidHom.ext fun x => MulEquiv.ext fun s => by
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, congrHom_apply, MulEquiv.symm_symm,
      MulEquiv.symm_apply_apply]

theorem autSub_map (e : V ≃* W) (P : Subgroup (MulAut V)) {U : Subgroup V} {U' : Subgroup W}
    (hU : ∀ v, v ∈ U ↔ e v ∈ U') :
    autSub (P.map (congrHom e)) U' = (autSub P U).map (congrHom (resEquiv e hU)) := by
  ext φ
  rw [mem_autSub, Subgroup.mem_map]
  constructor
  · rintro ⟨g', ⟨g, hg, hgg⟩, rfl⟩
    have hgs : g ∈ stabSub U := (mem_stabSub_congrHom e hU).1 (hgg ▸ g'.2)
    refine ⟨resHom U ⟨g, hgs⟩, mem_autSub.2 ⟨⟨g, hgs⟩, hg, rfl⟩, ?_⟩
    refine MulEquiv.ext fun u => Subtype.ext ?_
    show e (g (e.symm u)) = (g' : MulAut W) u
    rw [← hgg]
    rfl
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hψ
    refine ⟨⟨congrHom e g, (mem_stabSub_congrHom e hU).2 g.2⟩, ⟨g, hg, rfl⟩, ?_⟩
    exact MulEquiv.ext fun u => Subtype.ext rfl

theorem realizes_map (D : FFModel) {S T : Type*} [CommGroup S] [CommGroup T] (f : S ≃* T)
    {L : Subgroup (MulAut S)} (h : D.Realizes L ⊤ ⊥) : D.Realizes (L.map (congrHom f)) ⊤ ⊥ := by
  obtain ⟨π, hπ, -, hks, -, -, hsec, hker, β, hβs, hβk, hβe⟩ := h
  let ι : ↥L ≃* ↥(L.map (congrHom f)) := L.equivMapOfInjective (congrHom f) (congrHom_injective f)
  let r : ↥(⊤ : Subgroup T) →* ↥(⊤ : Subgroup S) :=
    { toFun := fun t => ⟨f.symm (t : T), trivial⟩
      map_one' := Subtype.ext (map_one f.symm)
      map_mul' := fun a b => Subtype.ext (map_mul f.symm (a : T) (b : T)) }
  refine ⟨ι.toMonoidHom.comp π, ι.surjective.comp hπ, le_top, hks, fun _ _ _ => trivial,
    fun _ z hz => ?_, hsec, hker, β.comp r, fun q => ?_, fun t => ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · obtain ⟨u, hu⟩ := hβs q
    refine ⟨⟨f u, trivial⟩, ?_⟩
    rw [MonoidHom.comp_apply, ← hu]
    exact congrArg β (Subtype.ext (f.symm_apply_apply u))
  · rw [MonoidHom.comp_apply, hβk, Subgroup.mem_bot, Subgroup.mem_bot]
    exact f.symm.map_eq_one_iff
  · intro γ t m hu hm hβ
    have h1 := hβe γ (r t) m trivial hm hβ
    rw [MonoidHom.comp_apply, ← h1]
    refine congrArg β (Subtype.ext ?_)
    show f.symm (f ((π γ : MulAut S) (f.symm t))) = (π γ : MulAut S) (f.symm t)
    exact f.symm_apply_apply _

theorem realizes_autSub_of_map (D : FFModel) (e : V ≃* W) (P : Subgroup (MulAut V))
    {U : Subgroup V} {U' : Subgroup W} (hU : ∀ v, v ∈ U ↔ e v ∈ U')
    (h : D.Realizes (autSub (P.map (congrHom e)) U') ⊤ ⊥) : D.Realizes (autSub P U) ⊤ ⊥ := by
  rw [autSub_map e P hU] at h
  have h2 := realizes_map D (resEquiv e hU).symm h
  rwa [Subgroup.map_map, congrHom_symm_comp, Subgroup.map_id] at h2

theorem autSub_eq_top_of_map (e : V ≃* W) (P : Subgroup (MulAut V)) {U : Subgroup V}
    {U' : Subgroup W} (hU : ∀ v, v ∈ U ↔ e v ∈ U') (h : autSub (P.map (congrHom e)) U' = ⊤) :
    autSub P U = ⊤ := by
  rw [autSub_map e P hU] at h
  have h2 := congrArg (Subgroup.map (congrHom (resEquiv e hU).symm)) h
  rwa [Subgroup.map_map, congrHom_symm_comp, Subgroup.map_id,
    Subgroup.map_top_of_surjective _ (MulAut.congr (resEquiv e hU).symm).surjective] at h2

@[expose] noncomputable def autSubEquiv (e : V ≃* W) (P : Subgroup (MulAut V)) {U : Subgroup V}
    {U' : Subgroup W} (hU : ∀ v, v ∈ U ↔ e v ∈ U') :
    ↥(autSub P U) ≃* ↥(autSub (P.map (congrHom e)) U') :=
  ((autSub P U).equivMapOfInjective _ (congrHom_injective (resEquiv e hU))).trans
    (MulEquiv.subgroupCongr (autSub_map e P hU).symm)

theorem isQuasisimple_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) : CFSG.IsQuasisimple S := by
  obtain ⟨a, b, hab⟩ := hnc
  have hZ : Subgroup.center S = ⊥ := by
    rcases (Subgroup.center S).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a) hab
  have hP : commutator S = ⊤ := by
    rcases (inferInstance : (commutator S).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      apply hab
      have hm : ⁅a, b⁆ ∈ commutator S := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
    · exact h
  let e : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨⟨hP⟩, e.isSimpleGroup, e.symm a, e.symm b, fun h => hab (e.symm.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem isQuasisimple_quot_pCore {G S : Type*} [Group G] [Group S] [Finite G] (f : G →* S)
    (hf : Function.Surjective f) [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (hker : IsPGroup 2 f.ker) : CFSG.IsQuasisimple (G ⧸ CFSG.pCore 2 G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite S := Finite.of_surjective f hf
  have hle : f.ker ≤ CFSG.pCore 2 G := le_sSup ⟨f.normal_ker, hker⟩
  have hge : CFSG.pCore 2 G ≤ f.ker := by
    have hN : ((CFSG.pCore 2 G).map f).Normal := CFSG.pCore_normal.map f hf
    rcases hN.eq_bot_or_eq_top with h | h
    · exact (Subgroup.map_eq_bot_iff _).1 h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have hp : IsPGroup 2 S := by
        have h1 : IsPGroup 2 ((CFSG.pCore 2 G).map f) := CFSG.pCore_isPGroup.map f
        rw [h] at h1
        exact h1.of_equiv Subgroup.topEquiv
      have : Nontrivial S := ⟨⟨a * b, b * a, hab⟩⟩
      have hZ : Subgroup.center S ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 hp.center_nontrivial
      rcases (Subgroup.center S).normal_of_characteristic.eq_bot_or_eq_top with h2 | h2
      · exact hZ h2
      · exact hab ((Subgroup.mem_center_iff.1 (h2 ▸ Subgroup.mem_top b)) a)
  have heq : CFSG.pCore 2 G = f.ker := le_antisymm hge hle
  let e : G ⧸ CFSG.pCore 2 G ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq heq).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have : IsSimpleGroup (G ⧸ CFSG.pCore 2 G) := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hnc
  exact isQuasisimple_of_simple ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by
    rw [map_mul, map_mul, h]))⟩

@[expose] def resP {P : Subgroup (MulAut V)} {U : Subgroup V} (hP : P ≤ stabSub U) :
    ↥P →* ↥(autSub P U) where
  toFun p := ⟨resHom U ⟨p, hP p.2⟩, mem_autSub.2 ⟨⟨p, hP p.2⟩, p.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (resHom U))
  map_mul' a b := Subtype.ext (map_mul (resHom U) ⟨a, hP a.2⟩ ⟨b, hP b.2⟩)

theorem resP_surjective {P : Subgroup (MulAut V)} {U : Subgroup V} (hP : P ≤ stabSub U) :
    Function.Surjective (resP hP) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
  exact ⟨⟨g, hg⟩, rfl⟩

theorem isQuasisimple_of_autSub [Finite V] {P : Subgroup (MulAut V)} {U : Subgroup V}
    (hP : P ≤ stabSub U) [IsSimpleGroup ↥(autSub P U)]
    (hnc : ∃ a b : ↥(autSub P U), a * b ≠ b * a) (hC : IsPGroup 2 ↥(P ⊓ centSub U)) :
    CFSG.IsQuasisimple (↥P ⧸ CFSG.pCore 2 ↥P) := by
  have : Finite (MulAut V) := ZTrans.finite_mulAut_z (V := V)
  refine isQuasisimple_quot_pCore (resP hP) (resP_surjective hP) hnc ?_
  let j : ↥(resP hP).ker →* ↥(P ⊓ centSub U) :=
    { toFun := fun k => ⟨((k : ↥P) : MulAut V), (k : ↥P).2, fun u hu => by
        have h1 := congrArg (fun φ : ↥(autSub P U) => (((φ : MulAut ↥U) ⟨u, hu⟩ : ↥U) : V)) k.2
        exact h1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine hC.of_injective j fun a b h => ?_
  have h1 : ((a : ↥P) : MulAut V) = ((b : ↥P) : MulAut V) :=
    congrArg (fun z : ↥(P ⊓ centSub U) => (z : MulAut V)) h
  exact Subtype.ext (Subtype.ext h1)

theorem a0b0_ne : a0' * b0' ≠ b0' * a0' := by
  intro h
  have h1 : a0 * b0 = b0 * a0 := congrArg Subtype.val h
  revert h1
  decide

theorem alt5_of_gens {S : Type} [CommGroup S] {L : Subgroup (MulAut S)} [Finite ↥L]
    (hL : Nat.card ↥L ≤ 60) {x y : MulAut S} (hx : x ∈ L) (hy : y ∈ L)
    (β : S ≃* ↥(G6.coreMod 5))
    (hβx : ∀ s, ((β (x s) : ↥(G6.coreMod 5)) : G6.PermMod 5) = G6.permAct 5 a0 (β s))
    (hβy : ∀ s, ((β (y s) : ↥(G6.coreMod 5)) : G6.PermMod 5) = G6.permAct 5 b0 (β s)) :
    AlternatingNatural L ⊤ ⊥ 5 ∧ Nonempty (↥(alternatingGroup (Fin 5)) ≃* ↥L) := by
  have hD := FFModel.altDn_isActionModel 5
  let β' : S ≃* ↥(FFModel.altDn 5).sec := β
  set π₀ : ↥(alternatingGroup (Fin 5)) →* MulAut S := conjHom hD β' with hπ₀
  have hπx : π₀ a0' = x := by
    apply MulEquiv.ext
    intro s
    apply β'.injective
    exact (CFSG.QuasithinUnique.B42A57.conjAct_apply hD β' a0' s).trans (Subtype.ext (hβx s).symm)
  have hπy : π₀ b0' = y := by
    apply MulEquiv.ext
    intro s
    apply β'.injective
    exact (CFSG.QuasithinUnique.B42A57.conjAct_apply hD β' b0' s).trans (Subtype.ext (hβy s).symm)
  have hinj : Function.Injective π₀ := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply altDn5_faithful
    intro m hm
    have h1 : CFSG.QuasithinUnique.B42A57.conjAct hD β' γ (β'.symm ⟨m, hm⟩) = β'.symm ⟨m, hm⟩ :=
      congrArg (fun f : MulAut S => f (β'.symm ⟨m, hm⟩)) hγ
    have h2 := CFSG.QuasithinUnique.B42A57.conjAct_apply hD β' γ (β'.symm ⟨m, hm⟩)
    rw [h1, β'.apply_symm_apply] at h2
    have h3 : (FFModel.altDn 5).act γ m = m := (congrArg Subtype.val h2).symm
    rw [h3, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hcl : Subgroup.closure ({x, y} : Set (MulAut S)) = π₀.range := by
    rw [MonoidHom.range_eq_map, ← closure_a5, MonoidHom.map_closure, Set.image_pair, hπx, hπy]
  have hcard : Nat.card ↥π₀.range = 60 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top, a5_card]
  have hle : Subgroup.closure ({x, y} : Set (MulAut S)) ≤ L := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hx
    · exact hy
  have hLeq : L = Subgroup.closure ({x, y} : Set (MulAut S)) :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hcl, hcard]; exact hL)).symm
  have : Finite (FFModel.altDn 5).Gam := (inferInstance : Finite (alternatingGroup (Fin 5)))
  refine ⟨realizesMod_of_two_generators hD altDn5_ker altDn5_faithful L ?_ β' x y a0' b0'
    hβx hβy hLeq, ?_⟩
  · show Nat.card ↥(alternatingGroup (Fin 5)) ≤ Nat.card ↥L
    rw [a5_card, hLeq, hcl, hcard]
  · have hr : π₀.range = L := hcl.symm.trans hLeq.symm
    exact ⟨(MulEquiv.ofBijective π₀.rangeRestrict
      ⟨fun a b h => hinj (congrArg Subtype.val h), π₀.rangeRestrict_surjective⟩).trans
      (MulEquiv.subgroupCongr hr)⟩

theorem card_coreMod_five : Nat.card ↥(G6.coreMod 5) = 16 := by
  rw [← Nat.card_congr PsiD.toEquiv]
  exact Nat.card_eq_fintype_card.trans (card_Wn 4)

theorem permAct_toW_eq {σ : Equiv.Perm (Fin 5)} {a b : ℕ}
    (h : ∀ i : Fin 5, CFSG.Monster.Code.bvec 5 b i = CFSG.Monster.Code.bvec 5 a (σ⁻¹ i)) :
    toW 5 b = G6.permAct 5 σ (toW 5 a) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply, toAdd_toW, toAdd_toW]
  exact h i

theorem simple_of_alt5 {G : Type*} [Group G] (ι : ↥(alternatingGroup (Fin 5)) ≃* G) :
    IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨ι.symm.isSimpleGroup, ι a0', ι b0', fun h => a0b0_ne (ι.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem alt5_of_map {V W : Type} [CommGroup V] [CommGroup W] [Finite V] (e : V ≃* W)
    (P : Subgroup (MulAut V)) {U : Subgroup V} {U' : Subgroup W} (hU : ∀ v, v ∈ U ↔ e v ∈ U')
    (hL : Nat.card ↥(autSub (P.map (congrHom e)) U') ≤ 60) {x y : MulAut ↥U'}
    (hx : x ∈ autSub (P.map (congrHom e)) U') (hy : y ∈ autSub (P.map (congrHom e)) U')
    (β : ↥U' ≃* ↥(G6.coreMod 5))
    (hβx : ∀ s, ((β (x s) : ↥(G6.coreMod 5)) : G6.PermMod 5) = G6.permAct 5 a0 (β s))
    (hβy : ∀ s, ((β (y s) : ↥(G6.coreMod 5)) : G6.PermMod 5) = G6.permAct 5 b0 (β s)) :
    AlternatingNatural (autSub P U) ⊤ ⊥ 5 ∧
      Nonempty (↥(alternatingGroup (Fin 5)) ≃* ↥(autSub P U)) := by
  have : Finite (MulAut V) := ZTrans.finite_mulAut_z (V := V)
  have : Finite (MulAut ↥U) := ZTrans.finite_mulAut_z (V := ↥U)
  set f := resEquiv e hU
  rw [autSub_map e P hU] at hx hy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  have hc : ∀ (z : MulAut ↥U) (s : ↥U), f (z s) = congrHom f z (f s) := fun z s => by
    rw [congrHom_apply, MulEquiv.symm_apply_apply]
  refine alt5_of_gens (hL.trans' (Nat.card_congr (autSubEquiv e P hU).toEquiv).le) hx₀ hy₀
    (f.trans β) (fun s => ?_) (fun s => ?_)
  · rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hc]
    exact hβx (f s)
  · rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hc]
    exact hβy (f s)

theorem lu_A5_of_std {V W : Type} [CommGroup V] [CommGroup W] [Finite V] [Finite W] (e : V ≃* W)
    {H X : Subgroup (MulAut V)} {P' : Subgroup (MulAut W)} {U' : Subgroup W}
    (hP : (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom e) = P')
    (hU : fixV (X.map (congrHom e)) = U') (hcard : Nat.card ↥P' = 960)
    (hL : Nat.card ↥(autSub P' U') ≤ 60) {x y : MulAut ↥U'} (hx : x ∈ autSub P' U')
    (hy : y ∈ autSub P' U') (β : ↥U' ≃* ↥(G6.coreMod 5))
    (hβx : ∀ s, ((β (x s) : ↥(G6.coreMod 5)) : G6.PermMod 5) = G6.permAct 5 a0 (β s))
    (hβy : ∀ s, ((β (y s) : ↥(G6.coreMod 5)) : G6.PermMod 5) = G6.permAct 5 b0 (β s)) :
    CFSG.IsQuasisimple (↥(perfectCore (H ⊓ stabSub (fixV X))) ⧸
        CFSG.pCore 2 ↥(perfectCore (H ⊓ stabSub (fixV X)))) ∧
      AlternatingNatural (V := ↥(fixV X)) (autSub (perfectCore (H ⊓ stabSub (fixV X))) (fixV X))
        ⊤ ⊥ 5 := by
  have : Finite (MulAut V) := ZTrans.finite_mulAut_z (V := V)
  set P := perfectCore (H ⊓ stabSub (fixV X))
  have hUe : ∀ v, v ∈ fixV X ↔ e v ∈ U' := fun v => by
    rw [← hU, fixV_map_congrHom]
    exact (Subgroup.mem_map_iff_mem e.injective).symm
  subst hP
  obtain ⟨hA, ⟨ι⟩⟩ := alt5_of_map e P hUe hL hx hy β hβx hβy
  obtain ⟨hS, hnc⟩ := simple_of_alt5 ι
  have hPU : P ≤ stabSub (fixV X) := (perfectCore_le _).trans inf_le_right
  refine ⟨?_, hA⟩
  have h60 : Nat.card ↥(autSub P (fixV X)) = 60 := (Nat.card_congr ι.toEquiv).symm.trans a5_card
  have h := card_autSub_mul hPU
  rw [h60, ← card_map_congrHom e P, hcard] at h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isQuasisimple_of_autSub hPU hnc (IsPGroup.of_card (n := 4) (by omega))

theorem maskOf_mul (n : ℕ) (a b : Wn n) : maskOf n (a * b) = maskOf n a ^^^ maskOf n b := by
  have ha := maskOf_spec a
  have hb := maskOf_spec b
  have hlt : maskOf n a ^^^ maskOf n b < 2 ^ n := Nat.xor_lt_two_pow ha.1 hb.1
  have h : a * b = toW n (maskOf n a ^^^ maskOf n b) := by rw [toW_xor, ha.2, hb.2]
  rw [h, maskOf_toW hlt]

theorem maskOf_one (n : ℕ) : maskOf n (1 : Wn n) = 0 := by
  rw [← toW_zero n, maskOf_toW (Nat.two_pow_pos n)]

@[expose] noncomputable def maskHom (n k : ℕ) (U : Subgroup (Wn n)) (bc : List ℕ) : ↥U →* Wn k where
  toFun u := toW k (actM bc (maskOf n (u : Wn n)))
  map_one' := by
    show toW k (actM bc (maskOf n 1)) = 1
    rw [maskOf_one, (actM_xor bc).map_zero, toW_zero]
  map_mul' a b := by
    show toW k (actM bc (maskOf n ((a : Wn n) * b))) = _
    rw [maskOf_mul, actM_xor, toW_xor]

theorem maskHom_apply {n k : ℕ} {U : Subgroup (Wn n)} {bc : List ℕ} (u : ↥U) {m : ℕ}
    (hm : m < 2 ^ n) (hu : (u : Wn n) = toW n m) : maskHom n k U bc u = toW k (actM bc m) := by
  show toW k (actM bc (maskOf n (u : Wn n))) = _
  rw [hu, maskOf_toW hm]

@[expose] noncomputable def maskEquiv (n k : ℕ) (l : List ℕ) (T : Subgroup (Wn k)) (bc : List ℕ)
    (hl : ∀ a ∈ l, a < 2 ^ n) (hT : ∀ m ∈ combos l, toW k (actM bc m) ∈ T)
    (h0 : ∀ m ∈ combos l, actM bc m < 2 ^ k ∧ (actM bc m = 0 → m = 0))
    (hcard : Nat.card ↥T ≤ Nat.card ↥(maskSub n l)) : ↥(maskSub n l) ≃* ↥T :=
  have hmem : ∀ u : ↥(maskSub n l), maskHom n k (maskSub n l) bc u ∈ T := by
    intro u
    obtain ⟨m, hm, hmu⟩ := u.2
    rw [maskHom_apply u (combos_lt hl m hm) hmu.symm]
    exact hT m hm
  have hinj : Function.Injective ((maskHom n k (maskSub n l) bc).codRestrict T hmem) := by
    rw [injective_iff_map_eq_one]
    intro u h
    obtain ⟨m, hm, hmu⟩ := u.2
    have h2 : maskHom n k (maskSub n l) bc u = 1 := congrArg Subtype.val h
    rw [maskHom_apply u (combos_lt hl m hm) hmu.symm, ← toW_zero k] at h2
    have h3 := (h0 m hm).2 (toW_inj (h0 m hm).1 (Nat.two_pow_pos k) h2)
    exact Subtype.ext (hmu.symm.trans (by rw [h3, toW_zero]; rfl))
  have : Finite ↥(maskSub n l) := Subtype.finite
  have : Finite ↥T := Subtype.finite
  MulEquiv.ofBijective _ ((Function.Injective.bijective_of_nat_card_le hinj hcard))

theorem maskEquiv_apply {n k : ℕ} {l : List ℕ} {T : Subgroup (Wn k)} {bc : List ℕ}
    {hl : ∀ a ∈ l, a < 2 ^ n} {hT : ∀ m ∈ combos l, toW k (actM bc m) ∈ T}
    {h0 : ∀ m ∈ combos l, actM bc m < 2 ^ k ∧ (actM bc m = 0 → m = 0)}
    {hcard : Nat.card ↥T ≤ Nat.card ↥(maskSub n l)} (u : ↥(maskSub n l)) {m : ℕ}
    (hm : m ∈ combos l) (hu : (u : Wn n) = toW n m) :
    ((maskEquiv n k l T bc hl hT h0 hcard u : ↥T) : Wn k) = toW k (actM bc m) :=
  maskHom_apply u (combos_lt hl m hm) hu

end CFSG.Quasithin.H.LU
