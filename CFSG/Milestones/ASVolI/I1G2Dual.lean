module

public import CFSG.Milestones.ASVolI.I2
public import CFSG.Milestones.ASVolI.B4G2
public import CFSG.Quasithin.Recognition.HSTypeConj
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Rk
public import CFSG.Quasithin.MS93.M15WeylQ

public section

namespace CFSG.ASVolI

open CFSG.Open

section Basic

variable {W : Type} [CommGroup W]

open CFSG.Quasithin in
theorem burnsideI17b_card_sup_mul_card_inf [Finite W] (U C : Subgroup W) :
    Nat.card ↥(U ⊔ C) * Nat.card ↥(U ⊓ C) = Nat.card ↥U * Nat.card ↥C := by
  have h1 : C.relIndex (U ⊔ C) = C.relIndex U := Subgroup.relIndex_sup_right U C
  have h3 := Subgroup.relIndex_mul_card (H := C) (K := U ⊔ C)
  have h4 := Subgroup.relIndex_mul_card (H := C) (K := U)
  rw [inf_eq_left.2 le_sup_right] at h3
  rw [inf_comm] at h4
  rw [h1] at h3
  rw [← h3, ← h4]
  ring

theorem burnsideI17b_card_le_of_offender [Finite W] {V C : Subgroup W} {a : ℕ}
    (hW : Nat.card W ≤ a * Nat.card ↥C) : Nat.card ↥V ≤ a * Nat.card ↥(V ⊓ C) := by
  have h1 := burnsideI17b_card_sup_mul_card_inf V C
  have h2 : Nat.card ↥(V ⊔ C) ≤ Nat.card W :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have hpos : 0 < Nat.card ↥C := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card ↥V * Nat.card ↥C = Nat.card ↥(V ⊔ C) * Nat.card ↥(V ⊓ C) := h1.symm
    _ ≤ Nat.card W * Nat.card ↥(V ⊓ C) := Nat.mul_le_mul_right _ h2
    _ ≤ (a * Nat.card ↥C) * Nat.card ↥(V ⊓ C) := Nat.mul_le_mul_right _ hW
    _ = a * Nat.card ↥(V ⊓ C) * Nat.card ↥C := by ring

theorem burnsideI17b_sup_eq_top [Finite W] {V C : Subgroup W} {a : ℕ}
    (hW : Nat.card W ≤ a * Nat.card ↥C) (hV : Nat.card ↥V = a * Nat.card ↥(V ⊓ C)) :
    V ⊔ C = ⊤ := by
  have h1 := burnsideI17b_card_sup_mul_card_inf V C
  have hpos : 0 < Nat.card ↥(V ⊓ C) := Nat.card_pos
  have h2 : Nat.card ↥(V ⊔ C) = a * Nat.card ↥C := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, hV]
    ring
  rw [← Subgroup.card_eq_iff_eq_top]
  have h3 : Nat.card ↥(V ⊔ C) ≤ Nat.card W := Nat.card_le_card_of_injective _ Subtype.val_injective
  omega

open CFSG.Quasithin in
theorem burnsideI17b_fixV_le_of_dual [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {V : Subgroup W}
    {A : Subgroup (MulAut W)} (h : dualAnn V ≤ commV (dualSub A)) : fixV A ≤ V := by
  rw [commV_dualSub hW] at h
  exact (dualAnn_le_dualAnn_iff hW).1 h

end Basic

section Restr

open CFSG.Quasithin

variable {W : Type} [CommGroup W] {M : Type} [CommGroup M]

theorem burnsideI17b_le_stabSub (V : Subgroup W) (G : Subgroup (MulAut W))
    (hG : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V) : G ≤ stabSub V := fun g hg =>
  mem_stabSub_of_invariant (hG g hg) (hG g⁻¹ (G.inv_mem hg))

noncomputable def burnsideI17b_rho (V : Subgroup W) (β : ↥V ≃* M) (G : Subgroup (MulAut W))
    (hG : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V) : ↥G →* MulAut M :=
  ((MulAut.congr β).toMonoidHom.comp (resHom V)).comp
    (Subgroup.inclusion (burnsideI17b_le_stabSub V G hG))

theorem burnsideI17b_rho_apply (V : Subgroup W) (β : ↥V ≃* M) (G : Subgroup (MulAut W))
    (hG : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V) (g : ↥G) (v : ↥V) :
    burnsideI17b_rho V β G hG g (β v) = β ⟨(g : MulAut W) v, hG g g.2 v v.2⟩ := by
  change MulAut.congr β (resHom V ⟨(g : MulAut W), burnsideI17b_le_stabSub V G hG g.2⟩) (β v) = _
  rw [CFSG.Quasithin.H13.congr_apply_eq β]
  rfl

omit [CommGroup W] [CommGroup M] in
theorem burnsideI17b_genFitting_range {Y M' : Type*} [Group Y] [Group M'] (f : Y →* M')
    (hf : Function.Injective f) :
    quasithinGenFitting f.range =
      (CFSG.ComponentClassification.GeneralizedFitting.subgroup Y).map f := by
  rw [CFSG.Quasithin.quasithinGenFitting_eq_map_subtype]
  have h := CFSG.Quasithin.HSType.generalizedFitting_map_equiv (MonoidHom.ofInjective hf)
  rw [← h, Subgroup.map_map]
  rfl

omit [CommGroup W] [CommGroup M] in
theorem burnsideI17b_genFitting_eq_subgroupOf {Ω : Type*} [Group Ω] (G : Subgroup Ω) :
    CFSG.ComponentClassification.GeneralizedFitting.subgroup ↥G =
      (quasithinGenFitting G).subgroupOf G := by
  rw [CFSG.Quasithin.quasithinGenFitting_eq_map_subtype]
  exact (Subgroup.comap_map_eq_self_of_injective G.subtype_injective _).symm

theorem burnsideI17b_faithful (hW : ∀ w : W, w ^ 2 = 1) {G L : Subgroup (MulAut W)} {V : Subgroup W}
    (hL : L = quasithinGenFitting G) (hVinv : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V)
    (hcomm : commV G ≤ V) (hLfaith : ∀ l ∈ L, (∀ v ∈ V, l v = v) → l = 1) :
    ∀ g ∈ G, (∀ v ∈ V, g v = v) → g = 1 := by
  let N : Subgroup (MulAut W) :=
    { carrier := {g | g ∈ G ∧ ∀ v ∈ V, g v = v}
      one_mem' := ⟨G.one_mem, fun v _ => rfl⟩
      mul_mem' := fun {a b} ha hb => ⟨G.mul_mem ha.1 hb.1, fun v hv => by
        change a (b v) = v
        rw [hb.2 v hv, ha.2 v hv]⟩
      inv_mem' := fun {a} ha => ⟨G.inv_mem ha.1, fun v hv => by
        change a⁻¹ v = v
        have := ha.2 v hv
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
        exact this.symm⟩ }
  have hNG : N ≤ G := fun g hg => hg.1
  have hcm : ∀ g ∈ N, ∀ w : W, g w * w⁻¹ ∈ V := fun g hg w =>
    hcomm (Subgroup.subset_closure ⟨g, hg.1, w, rfl⟩)
  have hcomm_N : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    ext w
    change a (b w) = b (a w)
    have h1 : a (b w) = (b w * w⁻¹) * a w := by
      have : b w = (b w * w⁻¹) * w := (inv_mul_cancel_right (b w) w).symm
      conv_lhs => rw [this, map_mul, ha.2 _ (hcm b hb w)]
    have h2 : b (a w) = (a w * w⁻¹) * b w := by
      have : a w = (a w * w⁻¹) * w := (inv_mul_cancel_right (a w) w).symm
      conv_lhs => rw [this, map_mul, hb.2 _ (hcm a ha w)]
    rw [h1, h2]
    calc b w * w⁻¹ * a w = (b w * w⁻¹) * (a w * w⁻¹) * w := by group
      _ = (a w * w⁻¹) * (b w * w⁻¹) * w := by rw [mul_comm (b w * w⁻¹)]
      _ = (a w * w⁻¹) * b w := by group
  have hnormal : (N.subgroupOf G).Normal := by
    refine ⟨fun n hn h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hnG : (n : MulAut W) ∈ G := n.2
    have hhG : (h : MulAut W) ∈ G := h.2
    show ((h : MulAut W) * (n : MulAut W) * (h : MulAut W)⁻¹) ∈ N
    refine ⟨G.mul_mem (G.mul_mem hhG hnG) (G.inv_mem hhG), fun v hv => ?_⟩
    have hv' : (h : MulAut W)⁻¹ v ∈ V := hVinv _ (G.inv_mem hhG) v hv
    have h1 := hn.2 _ hv'
    show (h : MulAut W) ((n : MulAut W) ((h : MulAut W)⁻¹ v)) = v
    rw [h1]
    simp
  haveI : IsMulCommutative ↥N := ⟨⟨fun a b => Subtype.ext (hcomm_N a a.2 b b.2)⟩⟩
  have hNnil : Group.IsNilpotent ↥N := inferInstance
  have hNL : N ≤ L := by
    rw [hL]
    exact le_trans (le_sSup (show N ∈ {N : Subgroup (MulAut W) | N ≤ G ∧
      (N.subgroupOf G).Normal ∧ Group.IsNilpotent ↥N} from ⟨hNG, hnormal, hNnil⟩)) le_sup_left
  intro g hg hgV
  exact hLfaith g (hNL ⟨hg, hgV⟩) hgV

noncomputable def burnsideI17b_img (V : Subgroup W) (β : ↥V ≃* M) (G : Subgroup (MulAut W))
    (hG : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V) (A : Subgroup (MulAut W)) : Subgroup (MulAut M) :=
  (A.subgroupOf G).map (burnsideI17b_rho V β G hG)

theorem burnsideI17b_mem_img (V : Subgroup W) (β : ↥V ≃* M) (G : Subgroup (MulAut W))
    (hG : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V) (A : Subgroup (MulAut W)) (x : MulAut M) :
    x ∈ burnsideI17b_img V β G hG A ↔ ∃ (a : ↥G), (a : MulAut W) ∈ A ∧
      burnsideI17b_rho V β G hG a = x := by
  simp [burnsideI17b_img, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem burnsideI17b_rho_injective (V : Subgroup W) (β : ↥V ≃* M) (G : Subgroup (MulAut W))
    (hG : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V)
    (hfaith : ∀ g ∈ G, (∀ v ∈ V, g v = v) → g = 1) :
    Function.Injective (burnsideI17b_rho V β G hG) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : ∀ v ∈ V, (g : MulAut W) v = v := by
    intro v hv
    have := burnsideI17b_rho_apply V β G hG g ⟨v, hv⟩
    rw [hg, MulAut.one_apply] at this
    exact congrArg Subtype.val (β.injective this).symm
  exact Subtype.ext (hfaith _ g.2 h1)

theorem burnsideI17b_mem_fixV_img (V : Subgroup W) (β : ↥V ≃* M) (G : Subgroup (MulAut W))
    (hG : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V) {A : Subgroup (MulAut W)} (hAG : A ≤ G) (v : ↥V) :
    β v ∈ fixV (burnsideI17b_img V β G hG A) ↔ (v : W) ∈ fixV A := by
  rw [mem_fixV, mem_fixV]
  constructor
  · intro h a ha
    have haG : a ∈ G := hAG ha
    have h1 := h (burnsideI17b_rho V β G hG ⟨a, haG⟩)
      ((burnsideI17b_mem_img V β G hG A _).2 ⟨⟨a, haG⟩, ha, rfl⟩)
    rw [burnsideI17b_rho_apply V β G hG ⟨a, haG⟩ v] at h1
    exact congrArg Subtype.val (β.injective h1)
  · intro h x hx
    obtain ⟨a, ha, rfl⟩ := (burnsideI17b_mem_img V β G hG A x).1 hx
    rw [burnsideI17b_rho_apply V β G hG a v]
    congr 1
    exact Subtype.ext (h _ ha)

theorem burnsideI17b_card_fixV_img (V : Subgroup W) (β : ↥V ≃* M) (G : Subgroup (MulAut W))
    (hG : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V) {A : Subgroup (MulAut W)} (hAG : A ≤ G) :
    Nat.card ↥(fixV (burnsideI17b_img V β G hG A)) = Nat.card ↥(V ⊓ fixV A) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨((β.symm x.1 : ↥V) : W), (β.symm x.1).2, ?_⟩
      invFun := fun y => ⟨β ⟨y.1, y.2.1⟩, ?_⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  · have := (burnsideI17b_mem_fixV_img V β G hG hAG (β.symm x.1)).1
    rw [MulEquiv.apply_symm_apply] at this
    exact this x.2
  · exact (burnsideI17b_mem_fixV_img V β G hG hAG ⟨y.1, y.2.1⟩).2 y.2.2

theorem burnsideI17b_card_img (V : Subgroup W) (β : ↥V ≃* M) (G : Subgroup (MulAut W))
    (hG : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V) (hfaith : ∀ g ∈ G, (∀ v ∈ V, g v = v) → g = 1)
    {A : Subgroup (MulAut W)} (hAG : A ≤ G) :
    Nat.card ↥(burnsideI17b_img V β G hG A) = Nat.card ↥A := by
  rw [burnsideI17b_img, Subgroup.card_map_of_injective (burnsideI17b_rho_injective V β G hG hfaith)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv

theorem burnsideI17b_img_normal (V : Subgroup W) (β : ↥V ≃* M) (G : Subgroup (MulAut W))
    (hG : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V) {L : Subgroup (MulAut W)} (hLG : L ≤ G)
    (hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (g : ↥G) (h : MulAut M) :
    h ∈ burnsideI17b_img V β G hG L ↔
      burnsideI17b_rho V β G hG g * h * (burnsideI17b_rho V β G hG g)⁻¹ ∈
        burnsideI17b_img V β G hG L := by
  constructor
  · intro hh
    obtain ⟨l, hl, rfl⟩ := (burnsideI17b_mem_img V β G hG L h).1 hh
    refine (burnsideI17b_mem_img V β G hG L _).2 ⟨g * l * g⁻¹, ?_, ?_⟩
    · exact hnorm g g.2 l hl
    · simp only [map_mul, map_inv]
  · intro hh
    obtain ⟨l, hl, hl'⟩ := (burnsideI17b_mem_img V β G hG L _).1 hh
    refine (burnsideI17b_mem_img V β G hG L h).2 ⟨g⁻¹ * l * g, ?_, ?_⟩
    · have := hnorm (g : MulAut W)⁻¹ (G.inv_mem g.2) l hl
      simpa using this
    · simp only [map_mul, map_inv, hl']
      group

end Restr

section Model

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem burnsideI17b_negc_apply (g : ↥(cayleyGroup K)) (v : Multiplicative (Ix3 → K)) :
    Multiplicative.toAdd ((burnsideB46_pi burnsideB46_neg_pi) g v) =
      g2Act g (Multiplicative.toAdd v) := by
  rw [burnsideB46_pi_apply, burnsideB46_neg_pi_apply]
  simp [burnsideB46_cg]

theorem burnsideI17b_neg_fixV (hc : ∃ c : K, c ≠ 0 ∧ c ≠ 1) :
    fixV (burnsideB46_neg_L (K := K)) = ⊥ := by
  ext v
  rw [Subgroup.mem_bot, ← burnsideB46_neg_theta_eq_one, ← MonoidHom.mem_ker,
    burnsideB46_neg_ker hc]

theorem burnsideI17b_hyp_big (hqs : burnsideB46_G2Qs) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {Gm : Subgroup (MulAut (Multiplicative (Ix3 → K)))}
    (hLG : burnsideB46_neg_L ≤ Gm) (hF : quasithinGenFitting Gm = burnsideB46_neg_L) :
    burnsideB46_Hyp (Multiplicative (Ix3 → K)) n K Gm burnsideB46_neg_L burnsideB46_neg_pi
      burnsideB46_neg_theta := by
  have H := burnsideB46_neg_Hyp hqs hn hK
  have hq := burnsideB46_neg_qs hqs hn hK
  exact { H with le := hLG, fstar := hF.trans (burnsideB46_neg_layer hq).symm }

end Model

section Aux

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin in
@[expose] def burnsideI17b_res {W : Type} [CommGroup W] (V : Subgroup W) :
    DualGrp W →* DualGrp ↥V where
  toFun f := f.comp V.subtype
  map_one' := rfl
  map_mul' _ _ := rfl

open CFSG.Quasithin in
theorem burnsideI17b_res_eq_one_iff {W : Type} [CommGroup W] (V : Subgroup W) (f : DualGrp W) :
    burnsideI17b_res V f = 1 ↔ f ∈ dualAnn V := by
  constructor
  · intro h u hu
    exact DFunLike.congr_fun h ⟨u, hu⟩
  · intro h
    exact DFunLike.ext _ _ fun v : ↥V => h v v.2

open CFSG.Quasithin in
@[expose] def burnsideI17b_dualEquiv {A B : Type} [CommGroup A] [CommGroup B] (e : A ≃* B) :
    DualGrp A ≃* DualGrp B where
  toFun g := g.comp e.symm.toMonoidHom
  invFun h := h.comp e.toMonoidHom
  left_inv g := DFunLike.ext _ _ fun a => by
    show g (e.symm (e a)) = g a
    rw [MulEquiv.symm_apply_apply]
  right_inv h := DFunLike.ext _ _ fun b => by
    show h (e (e.symm b)) = h b
    rw [MulEquiv.apply_symm_apply]
  map_mul' _ _ := rfl

open CFSG.Quasithin in
theorem burnsideI17b_res_surjective {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (V : Subgroup W) : Function.Surjective (burnsideI17b_res V) := by
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (hW (v : W))
  have h1 := dualAnn_card hW V
  have h2 := Subgroup.card_ker_mul_card_range (burnsideI17b_res V)
  have h3 : (burnsideI17b_res V).ker = dualAnn V := by
    ext f
    exact burnsideI17b_res_eq_one_iff V f
  have h4 := card_dualGrp hW
  have h5 := card_dualGrp hV2
  rw [h3] at h2
  have hpos : 0 < Nat.card ↥(dualAnn V) := Nat.card_pos
  have h6 : Nat.card (burnsideI17b_res V).range = Nat.card (DualGrp ↥V) := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [h2, h4, h5, ← h1]
  rw [← MonoidHom.range_eq_top]
  exact Subgroup.eq_top_of_card_eq _ h6

noncomputable local instance burnsideI17b_algZ2 (K : Type) [Field K] [CharP K 2] :
    Algebra (ZMod 2) K := ZMod.algebra K 2

open CFSG.Quasithin CFSG.Quasithin.JonesParshall in
@[expose] noncomputable def burnsideI17b_phi (K : Type) [Field K] [CharP K 2] :
    Multiplicative (Ix3 → K) →* DualGrp (Multiplicative (Ix3 → K)) where
  toFun u :=
    { toFun := fun x => Multiplicative.ofAdd
        (B513N.psiB K B5.G2D.bilQLin (Multiplicative.toAdd u) (Multiplicative.toAdd x))
      map_one' := by
        rw [toAdd_one, map_zero, ofAdd_zero]
      map_mul' := fun x y => by
        rw [toAdd_mul, map_add, ofAdd_add] }
  map_one' := by
    refine DFunLike.ext _ _ fun x => ?_
    show Multiplicative.ofAdd (B513N.psiB K B5.G2D.bilQLin (Multiplicative.toAdd 1)
      (Multiplicative.toAdd x)) = 1
    rw [toAdd_one, map_zero, LinearMap.zero_apply, ofAdd_zero]
  map_mul' u v := by
    refine DFunLike.ext _ _ fun x => ?_
    show Multiplicative.ofAdd (B513N.psiB K B5.G2D.bilQLin (Multiplicative.toAdd (u * v))
      (Multiplicative.toAdd x)) =
      Multiplicative.ofAdd (B513N.psiB K B5.G2D.bilQLin (Multiplicative.toAdd u)
        (Multiplicative.toAdd x)) *
      Multiplicative.ofAdd (B513N.psiB K B5.G2D.bilQLin (Multiplicative.toAdd v)
        (Multiplicative.toAdd x))
    rw [toAdd_mul, map_add, LinearMap.add_apply, ofAdd_add]

open CFSG.Quasithin CFSG.Quasithin.JonesParshall in
theorem burnsideI17b_phi_injective (K : Type) [Field K] [Finite K] [CharP K 2] :
    Function.Injective (burnsideI17b_phi K) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have hψ : B513N.psiB K B5.G2D.bilQLin (Multiplicative.toAdd u) = 0 := by
    refine LinearMap.ext fun x => ?_
    have h1 := DFunLike.congr_fun hu (Multiplicative.ofAdd x)
    have h2 : Multiplicative.ofAdd
        (B513N.psiB K B5.G2D.bilQLin (Multiplicative.toAdd u) x) = 1 := h1
    exact ofAdd_eq_one.mp h2
  have h3 : Multiplicative.toAdd u = 0 :=
    B513N.psiB_injective K B5.G2D.bilQLin (fun z hz => B5.G2D.eq_zero_of_bilQ hz)
      (hψ.trans (map_zero (B513N.psiB K B5.G2D.bilQLin)).symm)
  exact toAdd_eq_zero.mp h3

open CFSG.Quasithin CFSG.Quasithin.JonesParshall in
theorem burnsideI17b_sq_eq_one (K : Type) [Field K] [CharP K 2] (q : Multiplicative (Ix3 → K)) :
    q ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, two_nsmul, toAdd_one]
  funext i
  exact CharTwo.add_self_eq_zero (Multiplicative.toAdd q i)

open CFSG.Quasithin CFSG.Quasithin.JonesParshall in
theorem burnsideI17b_phi_bijective (K : Type) [Field K] [Finite K] [CharP K 2] :
    Function.Bijective (burnsideI17b_phi K) := by
  have hcard : Nat.card (DualGrp (Multiplicative (Ix3 → K))) = Nat.card (Multiplicative (Ix3 → K)) :=
    card_dualGrp (burnsideI17b_sq_eq_one K)
  exact (burnsideI17b_phi_injective K).bijective_of_nat_card_le hcard.le

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit in
theorem burnsideI17b_psiB_g2Act (K : Type) [Field K] [CharP K 2] (g : ↥(cayleyGroup K))
    (u x : Ix3 → K) :
    B513N.psiB K B5.G2D.bilQLin (g2Act g u) x = B513N.psiB K B5.G2D.bilQLin u (g2Act g⁻¹ x) := by
  rw [B513N.psiB_apply, B513N.psiB_apply]
  congr 1
  have h : g2Act g (g2Act g⁻¹ x) = x := by
    rw [← B5.G2D.g2Act_mul_apply, mul_inv_cancel, B5.G2D.g2Act_one_apply]
  show bilQ (g2Act g u) x = bilQ u (g2Act g⁻¹ x)
  rw [← bilQ_g2Act g u (g2Act g⁻¹ x), h]

end Aux

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 in
theorem burnsideI17b_dual_coord {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (Γ₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)) (hΓ : Γ₀ ≤ cayleyGroup K)
    (ρ : ↥Γ₀ →* MulAut W) (V : Subgroup W)
    (hρV : ∀ γ : ↥Γ₀, ∀ v ∈ V, ρ γ v ∈ V)
    (β : ↥V ≃* Multiplicative (Ix3 → K))
    (hβ : ∀ (γ : ↥Γ₀) (v : ↥V), β ⟨ρ γ (v : W), hρV γ v v.2⟩ =
      Multiplicative.ofAdd (g2Act (Subgroup.inclusion hΓ γ) (Multiplicative.toAdd (β v)))) :
    ∃ β' : DualGrp W →* Multiplicative (Ix3 → K), Function.Surjective β' ∧
      (∀ f, β' f = 1 ↔ f ∈ dualAnn V) ∧
      ∀ (γ : ↥Γ₀) (f : DualGrp W), β' ((dualAct W (ρ γ)) f) =
        Multiplicative.ofAdd (g2Act (Subgroup.inclusion hΓ γ) (Multiplicative.toAdd (β' f))) := by
  let Φ : Multiplicative (Ix3 → K) ≃* DualGrp (Multiplicative (Ix3 → K)) :=
    MulEquiv.ofBijective (burnsideI17b_phi K) (burnsideI17b_phi_bijective K)
  let η : DualGrp ↥V ≃* DualGrp (Multiplicative (Ix3 → K)) := burnsideI17b_dualEquiv β
  let ι : DualGrp W →* Multiplicative (Ix3 → K) :=
    Φ.symm.toMonoidHom.comp (η.toMonoidHom.comp (burnsideI17b_res V))
  have hι : ∀ f, Φ (ι f) = η (burnsideI17b_res V f) := fun f => Φ.apply_symm_apply _
  refine ⟨ι, ?_, ?_, ?_⟩
  · exact Φ.symm.surjective.comp (η.surjective.comp (burnsideI17b_res_surjective hW V))
  · intro f
    show Φ.symm (η (burnsideI17b_res V f)) = 1 ↔ f ∈ dualAnn V
    exact (Φ.symm.map_eq_one_iff).trans ((η.map_eq_one_iff).trans (burnsideI17b_res_eq_one_iff V f))
  · intro γ f
    apply Φ.injective
    rw [hι]
    refine DFunLike.ext _ _ fun x => ?_
    have hinv : Subgroup.inclusion hΓ γ⁻¹ = (Subgroup.inclusion hΓ γ)⁻¹ := map_inv _ γ
    have key := hβ γ⁻¹ (β.symm x)
    rw [MulEquiv.apply_symm_apply, hinv] at key
    have hy : ((ρ γ)⁻¹ ((β.symm x : ↥V) : W)) = ((β.symm (Multiplicative.ofAdd
        (g2Act (Subgroup.inclusion hΓ γ)⁻¹ (Multiplicative.toAdd x))) : ↥V) : W) := by
      rw [← map_inv ρ γ]
      exact congrArg Subtype.val ((β.eq_symm_apply).mpr key)
    have h3 : f ((β.symm (Multiplicative.ofAdd
        (g2Act (Subgroup.inclusion hΓ γ)⁻¹ (Multiplicative.toAdd x))) : ↥V) : W) =
        Multiplicative.ofAdd (B513N.psiB K B5.G2D.bilQLin (Multiplicative.toAdd (ι f))
          (g2Act (Subgroup.inclusion hΓ γ)⁻¹ (Multiplicative.toAdd x))) :=
      (DFunLike.congr_fun (hι f) (Multiplicative.ofAdd
        (g2Act (Subgroup.inclusion hΓ γ)⁻¹ (Multiplicative.toAdd x)))).symm
    show f (((ρ γ)⁻¹ : MulAut W) ((β.symm x : ↥V) : W)) = _
    rw [hy, h3]
    exact congrArg Multiplicative.ofAdd (burnsideI17b_psiB_g2Act K (Subgroup.inclusion hΓ γ)
      (Multiplicative.toAdd (ι f)) (Multiplicative.toAdd x)).symm

section DualStmts

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Quasithin in
theorem burnsideI17b_dual_exp2 {W : Type} [CommGroup W] (f : DualGrp W) : f ^ 2 = 1 := by
  refine DualGrp.ext fun w => ?_
  rw [sq]
  show f w * f w = 1
  generalize f w = a
  revert a
  decide

open CFSG.Quasithin in
theorem burnsideI17b_dual_commV_mono {V : Type} [CommGroup V] {A B : Subgroup (MulAut V)}
    (h : A ≤ B) : commV A ≤ commV B :=
  Subgroup.closure_mono fun _ ⟨a, ha, v, hv⟩ => ⟨a, h ha, v, hv⟩

open CFSG.Quasithin CFSG.Quasithin.Explicit in
@[expose] noncomputable def burnsideI17b_dualPi {K : Type} [Field K] [CharP K 2] {W : Type}
    [CommGroup W] (πW : ↥(cayleyGroup K) →* MulAut W) : ↥(quasithinG2 K) →* MulAut (DualGrp W) :=
  (dualAct W).comp (πW.comp burnsideB46_cg.toMonoidHom)

open CFSG.Quasithin CFSG.Quasithin.Explicit in
theorem burnsideI17b_dualPi_apply {K : Type} [Field K] [CharP K 2] {W : Type}
    [CommGroup W] (πW : ↥(cayleyGroup K) →* MulAut W) (γ : ↥(cayleyGroup K)) :
    burnsideI17b_dualPi πW (burnsideB46_cg.symm γ) = dualAct W (πW γ) := by
  unfold burnsideI17b_dualPi
  simp

open CFSG.Quasithin CFSG.Quasithin.Explicit in
theorem burnsideI17b_dualPi_range {K : Type} [Field K] [CharP K 2] {W : Type}
    [CommGroup W] (πW : ↥(cayleyGroup K) →* MulAut W) :
    (burnsideI17b_dualPi πW).range = dualSub πW.range := by
  ext a
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨πW (burnsideB46_cg γ), ⟨burnsideB46_cg γ, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨γ, rfl⟩, rfl⟩
    exact ⟨burnsideB46_cg.symm γ, burnsideI17b_dualPi_apply πW γ⟩

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.ASVolI.ChB in
theorem burnsideI17b_dual_Hyp (hqs : burnsideB46_G2Qs) {n : ℕ} (hn : 2 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (πW : ↥(cayleyGroup K) →* MulAut W) (hπinj : Function.Injective πW)
    (V : Subgroup W) (hfix : fixV πW.range = ⊥) (hcomm : commV πW.range = V)
    (β' : DualGrp W →* Multiplicative (Ix3 → K)) (hsurj : Function.Surjective β')
    (hker : ∀ f, β' f = 1 ↔ f ∈ dualAnn V)
    (hact : ∀ (γ : ↥(cayleyGroup K)) (f : DualGrp W), β' ((dualAct W (πW γ)) f) =
      Multiplicative.ofAdd (g2Act γ (Multiplicative.toAdd (β' f)))) :
    burnsideB46_Hyp (DualGrp W) n K (dualSub πW.range) (dualSub πW.range)
      (burnsideI17b_dualPi πW) (burnsideB46_neg_theta.comp β') := by
  have hinj : Function.Injective (burnsideI17b_dualPi πW) := by
    unfold burnsideI17b_dualPi
    exact (dualAct_injective hW).comp (hπinj.comp burnsideB46_cg.injective)
  have hrange := burnsideI17b_dualPi_range πW
  have hq : CFSG.Open.IsQuasisimple ↥(dualSub πW.range) := by
    let e : ↥(quasithinG2 K) ≃* ↥(dualSub πW.range) :=
      (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm (hqs K n hn hK)
  have hlayer : layerOf (dualSub πW.range) = dualSub πW.range :=
    le_antisymm (burnsideB46_layerOf_le _) (le_sSup ⟨le_rfl, IsSubnormal.refl _, hq⟩)
  have hcommL : commV (dualSub πW.range) = ⊤ := by
    rw [commV_dualSub hW, hfix, dualAnn_bot]
  have hfixL : fixV (dualSub πW.range) = dualAnn V := by
    rw [fixV_dualSub, hcomm]
  have hθ : Function.Surjective (burnsideB46_neg_theta (K := K)) := fun y =>
    ⟨Multiplicative.ofAdd (burnsideB46_ix (Multiplicative.toAdd y)),
      congrArg Multiplicative.ofAdd (burnsideB46_nat_ix _)⟩
  have hfst : quasithinGenFitting (dualSub πW.range) = layerOf (dualSub πW.range) :=
    (le_antisymm (CFSG.Quasithin.quasithinGenFitting_le _)
      (le_sup_of_le_right (le_sSup ⟨le_rfl, IsSubnormal.refl _, hq⟩))).trans hlayer.symm
  have hcl : commV (layerOf (dualSub πW.range)) = ⊤ := (congrArg commV hlayer).trans hcommL
  have hkerθ : (burnsideB46_neg_theta.comp β').ker = fixV (dualSub πW.range) := by
    rw [hfixL]
    ext f
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, burnsideB46_neg_theta_eq_one, hker]
  refine ⟨burnsideI17b_dual_exp2, by omega, hK, hinj, hrange, le_rfl, hfst, hcl, hθ.comp hsurj,
    hkerθ, ?_⟩
  intro γ v
  show burnsideB46_neg_theta (β' (dualAct W (πW (burnsideB46_cg γ)) v)) = _
  rw [hact]
  exact burnsideB46_neg_equiv γ (β' v)

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit in
theorem burnsideI17b_dual_eq_R {K : Type} [Field K] [CharP K 2] {x : quasithinZorn K}
    (hx : cayleyTr x = 0) (h : zP x = 0) : x = zmk x.1 0 0 0 0 0 0 x.1 := by
  have e := trace_zero_eq hx
  rw [h, zI_zero, zero_add, cayleyOne_eq, zmk_smul, mul_zero, mul_one] at e
  exact e

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit in
theorem burnsideI17b_dual_psi_comm {K : Type} [Field K] [CharP K 2] {X : Type} [CommGroup X]
    (ψ : ↥(zornO0 K) →* X) (ρ : ↥(cayleyGroup K) →* MulAut X)
    (hψ : ∀ (γ : ↥(cayleyGroup K)) (m m' : ↥(zornO0 K)),
      (m' : Multiplicative (quasithinZorn K)) =
        Multiplicative.ofAdd (cgE γ (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)))) →
        ψ m' = ρ γ (ψ m))
    (γ : ↥(cayleyGroup K)) (y : quasithinZorn K) (hy : cayleyTr y = 0) (t : ↥(zornO0 K))
    (ht : (t : Multiplicative (quasithinZorn K)) = Multiplicative.ofAdd (cgE γ y - y)) :
    ψ t = ρ γ (ψ ⟨Multiplicative.ofAdd y, hy⟩) * (ψ ⟨Multiplicative.ofAdd y, hy⟩)⁻¹ := by
  have h1 : t = (⟨Multiplicative.ofAdd (cgE γ y), (cg_tr γ y).trans hy⟩ : ↥(zornO0 K)) *
      (⟨Multiplicative.ofAdd y, hy⟩ : ↥(zornO0 K))⁻¹ := by
    apply Subtype.ext
    rw [ht]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ofAdd_sub, div_eq_mul_inv]
  rw [h1, map_mul, map_inv, hψ γ ⟨Multiplicative.ofAdd y, hy⟩
    ⟨Multiplicative.ofAdd (cgE γ y), (cg_tr γ y).trans hy⟩ rfl]

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.MS93 in
theorem burnsideI17b_dual_psi_R_mem {K : Type} [Field K] [CharP K 2] {X : Type} [CommGroup X]
    (ψ : ↥(zornO0 K) →* X) (ρ : ↥(cayleyGroup K) →* MulAut X)
    (hψ : ∀ (γ : ↥(cayleyGroup K)) (m m' : ↥(zornO0 K)),
      (m' : Multiplicative (quasithinZorn K)) =
        Multiplicative.ofAdd (cgE γ (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)))) →
        ψ m' = ρ γ (ψ m))
    (x : ↥(cayleyGroup K)) (c : K) (m : ↥(zornO0 K))
    (hm : (m : Multiplicative (quasithinZorn K)) = Multiplicative.ofAdd (zmk c 0 0 0 0 0 0 c)) :
    ψ m ∈ commV (((A1 K).map (MulAut.conj x).toMonoidHom).map ρ) := by
  obtain ⟨t₁, ht₁, t₂, ht₂, he⟩ := exists_sub_o0Comm_A1 c
  have e : zmk c 0 0 0 0 0 0 c = cgE x t₁ - cgE x t₂ := by
    rw [← map_sub, ← he, cgE_R]
  obtain ⟨γ₁, hγ₁, y₁, hy₁, hδ₁⟩ := (mem_o0Comm_conj_iff x).2 ⟨t₁, ht₁, rfl⟩
  obtain ⟨γ₂, hγ₂, y₂, hy₂, hδ₂⟩ := (mem_o0Comm_conj_iff x).2 ⟨t₂, ht₂, rfl⟩
  have htr : ∀ (γ : ↥(cayleyGroup K)) (y : quasithinZorn K), cayleyTr y = 0 →
      cayleyTr (cgE γ y - y) = 0 := fun γ y hy => by
    rw [cayleyTr_sub', cg_tr, hy, sub_zero]
  have key₁ := burnsideI17b_dual_psi_comm ψ ρ hψ γ₁ y₁ hy₁
    ⟨Multiplicative.ofAdd (cgE γ₁ y₁ - y₁), htr γ₁ y₁ hy₁⟩ rfl
  have key₂ := burnsideI17b_dual_psi_comm ψ ρ hψ γ₂ y₂ hy₂
    ⟨Multiplicative.ofAdd (cgE γ₂ y₂ - y₂), htr γ₂ y₂ hy₂⟩ rfl
  have hm' : m = (⟨Multiplicative.ofAdd (cgE γ₁ y₁ - y₁), htr γ₁ y₁ hy₁⟩ : ↥(zornO0 K)) *
      (⟨Multiplicative.ofAdd (cgE γ₂ y₂ - y₂), htr γ₂ y₂ hy₂⟩ : ↥(zornO0 K))⁻¹ := by
    apply Subtype.ext
    rw [hm]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e, hδ₁, hδ₂, ofAdd_sub, div_eq_mul_inv]
  rw [hm', map_mul, map_inv, key₁, key₂]
  exact Subgroup.mul_mem _
    (Subgroup.subset_closure ⟨ρ γ₁, Subgroup.mem_map.2 ⟨γ₁, hγ₁, rfl⟩, _, rfl⟩)
    (Subgroup.inv_mem _
      (Subgroup.subset_closure ⟨ρ γ₂, Subgroup.mem_map.2 ⟨γ₂, hγ₂, rfl⟩, _, rfl⟩))

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 in
theorem burnsideI17b_dual_ge2 (hqs : burnsideB46_G2Qs) {n : ℕ} (hn : 2 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (πW : ↥(cayleyGroup K) →* MulAut W) (hπinj : Function.Injective πW)
    (V : Subgroup W) (hVinv : ∀ γ : ↥(cayleyGroup K), ∀ v ∈ V, πW γ v ∈ V)
    (β : ↥V ≃* Multiplicative (Ix3 → K))
    (hβ : ∀ (γ : ↥(cayleyGroup K)) (v : ↥V), β ⟨πW γ (v : W), hVinv γ v v.2⟩ =
      Multiplicative.ofAdd (g2Act γ (Multiplicative.toAdd (β v))))
    (hfix : fixV πW.range = ⊥) (hcomm : commV πW.range = V) (x : ↥(cayleyGroup K)) :
    dualAnn V ≤ commV (dualSub (((A1 K).map (MulAut.conj x).toMonoidHom).map πW)) := by
  obtain ⟨β', hβ'surj, hβ'ker, hβ'act⟩ :=
    burnsideI17b_dual_coord hW (cayleyGroup K) le_rfl πW V hVinv β hβ
  have hact : ∀ (γ : ↥(cayleyGroup K)) (f : DualGrp W), β' ((dualAct W (πW γ)) f) =
      Multiplicative.ofAdd (g2Act γ (Multiplicative.toAdd (β' f))) := hβ'act
  have H := burnsideI17b_dual_Hyp hqs hn hK hW πW hπinj V hfix hcomm β' hβ'surj hβ'ker hact
  obtain ⟨ψ, hψs, -, hψe, hψθ⟩ := burnsideB46_weyl H hn
  intro c hc
  obtain ⟨m, rfl⟩ := hψs c
  have h1 : burnsideB46_nat (zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)))) = 0 := by
    rw [← hψθ m]
    show Multiplicative.toAdd (burnsideB46_neg_theta (β' (ψ m))) = 0
    rw [(hβ'ker _).2 hc, map_one]
    rfl
  have h2 : zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))) = 0 := by
    have := congrArg burnsideB46_ix h1
    rwa [burnsideB46_ix_nat, burnsideB46_ix_zero] at this
  have hm : (m : Multiplicative (quasithinZorn K)) = Multiplicative.ofAdd
      (zmk (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).1 0 0 0 0 0 0
        (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).1) :=
    (ofAdd_toAdd _).symm.trans (congrArg Multiplicative.ofAdd (burnsideI17b_dual_eq_R m.2 h2))
  have hψ' : ∀ (γ : ↥(cayleyGroup K)) (m m' : ↥(zornO0 K)),
      (m' : Multiplicative (quasithinZorn K)) =
        Multiplicative.ofAdd (cgE γ (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)))) →
        ψ m' = ((dualAct W).comp πW) γ (ψ m) := fun γ m m' h => by
    rw [hψe (burnsideB46_cg.symm γ) m m' h]
    exact congrArg (fun a : MulAut (DualGrp W) => a (ψ m)) (burnsideI17b_dualPi_apply πW γ)
  have key := burnsideI17b_dual_psi_R_mem ψ ((dualAct W).comp πW) hψ' x _ m hm
  have hle : ((A1 K).map (MulAut.conj x).toMonoidHom).map ((dualAct W).comp πW) ≤
      dualSub (((A1 K).map (MulAut.conj x).toMonoidHom).map πW) := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨πW s, ⟨s, hs, rfl⟩, rfl⟩
  exact burnsideI17b_dual_commV_mono hle key

theorem burnsideI17b_realizes_of_coord {K : Type} [Field K] [CharP K 2]
    {Γ₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)} (hΓ : Γ₀ ≤ cayleyGroup K)
    {M : Type} [CommGroup M] {H : Subgroup (MulAut M)} {U Z : Subgroup M} {π : ↥Γ₀ →* ↥H}
    (hπ : Function.Surjective π) (hZU : Z ≤ U)
    (hHU : ∀ h : ↥H, ∀ u ∈ U, (h : MulAut M) u ∈ U)
    (hHZ : ∀ h : ↥H, ∀ z ∈ Z, (h : MulAut M) z ∈ Z)
    (β : ↥U →* Multiplicative (Ix3 → K)) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : M) ∈ Z)
    (hβe : ∀ (γ : ↥Γ₀) (u : ↥U) (hu : ((π γ : ↥H) : MulAut M) (u : M) ∈ U),
      β ⟨((π γ : ↥H) : MulAut M) (u : M), hu⟩ = Multiplicative.ofAdd
        (g2Act (Subgroup.inclusion hΓ γ) (Multiplicative.toAdd (β u)))) :
    (FFModel.zornQ Γ₀).RealizesVia H U Z π := by
  have hΓ' : Γ₀ ≤ quasithinG2 K :=
    hΓ.trans (CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)).ge
  have hD := FFModel.zornQ_isActionModel Γ₀ hΓ'
  let e := zornSecEquiv (F := K) Γ₀
  refine ⟨hπ, hZU, hD.ker_le, hHU, hHZ, hD.sec_inv, hD.ker_inv, e.symm.toMonoidHom.comp β,
    e.symm.surjective.comp hβs, fun u => ?_, fun γ u m hu hm hum => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hβk]
  · have h1 : β u = e (QuotientGroup.mk m) := by
      have := congrArg e hum
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at this
      exact this
    have h2 := hβe γ u hu
    rw [h1] at h2
    show e.symm (β ⟨((π γ : ↥H) : MulAut M) (u : M), hu⟩) = _
    rw [MulEquiv.symm_apply_eq, h2]
    change _ = Multiplicative.ofAdd (zP (((show ↥Γ₀ from γ) : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (Multiplicative.toAdd (show Multiplicative (quasithinZorn K) from m.1))))
    have h3 : Multiplicative.toAdd (e (QuotientGroup.mk m)) =
        zP (Multiplicative.toAdd (show Multiplicative (quasithinZorn K) from m.1)) := rfl
    rw [h3]
    have h4 := g2_zP_apply (Subgroup.inclusion hΓ γ)
      (Multiplicative.toAdd (show Multiplicative (quasithinZorn K) from m.1)) m.2
    rw [g2Act_apply]
    exact congrArg Multiplicative.ofAdd h4.symm

theorem burnsideI17b_comm_le_cayley (K : Type) [Field K] [CharP K 2] :
    ⁅quasithinG2 K, quasithinG2 K⁆ ≤ cayleyGroup K :=
  (Subgroup.commutator_le_self _).trans
    (CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)).le

theorem burnsideI17b_dual_one
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (ρ : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* MulAut W) (V : Subgroup W)
    (hρV : ∀ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆, ∀ v ∈ V, ρ γ v ∈ V)
    (β : ↥V ≃* Multiplicative (Ix3 → K))
    (hβ : ∀ (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) (v : ↥V),
      β ⟨ρ γ (v : W), hρV γ v v.2⟩ = Multiplicative.ofAdd
        (g2Act (Subgroup.inclusion (burnsideI17b_comm_le_cayley K) γ) (Multiplicative.toAdd (β v))))
    (G : Subgroup (MulAut W)) (hLG : ρ.range ≤ G)
    (hGN : G ≤ Subgroup.normalizer (ρ.range : Set (MulAut W)))
    (hGC : G ⊓ Subgroup.centralizer (ρ.range : Set (MulAut W)) = ⊥)
    (hfix : fixV ρ.range = ⊥) (hcomm : commV ρ.range = V)
    {A : Subgroup (MulAut W)} (hA : IsA2 G A) (hAc : Nat.card ↥(commV A) ≤ Nat.card ↥A) :
    fixV A ≤ commV G := by
  have hΓ := burnsideI17b_comm_le_cayley K
  obtain ⟨β', hβ's, hβ'k, hβ'e⟩ := burnsideI17b_dual_coord hW _ hΓ ρ V hρV β hβ
  have hY : ∀ f : DualGrp W, f ^ 2 = 1 := fun f => burnsideI17b_dual_exp2 f
  have hfixL0 : fixV (dualSub ρ.range) = dualAnn V := by rw [fixV_dualSub, hcomm]
  have hcommL0 : commV (dualSub ρ.range) = ⊤ := by
    rw [commV_dualSub hW, hfix, dualAnn_bot]
  have hnat : G2NaturalDerived (dualSub ρ.range) ⊤ (fixV (dualSub ρ.range)) 1 := by
    refine ⟨K, inferInstance, inferInstance, by rw [hK, pow_one], ?_⟩
    let π' : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(dualSub ρ.range) :=
      ((dualAct W).comp ρ).codRestrict (dualSub ρ.range) (fun γ => ⟨ρ γ, ⟨γ, rfl⟩, rfl⟩)
    have hπ's : Function.Surjective π' := by
      rintro ⟨y, a, ⟨γ, rfl⟩, rfl⟩
      exact ⟨γ, rfl⟩
    refine ⟨π', burnsideI17b_realizes_of_coord hΓ hπ's le_top (fun _ _ _ => trivial)
      (fun h z hz => ?_) (β'.comp (⊤ : Subgroup (DualGrp W)).subtype) ?_ ?_ ?_⟩
    · have := mem_fixV.1 hz h h.2
      rw [this]
      exact hz
    · exact hβ's.comp (Subgroup.topEquiv.surjective)
    · intro u
      rw [MonoidHom.comp_apply, hβ'k, hfixL0]
      rfl
    · intro γ u hu
      exact hβ'e γ u.1
  obtain ⟨hAG, hA1, hAe⟩ := hA
  have hA2 : IsA2 (dualSub G) (dualSub A) := by
    refine ⟨Subgroup.map_mono hAG, ?_, ?_, ?_⟩
    · intro h
      apply hA1
      have : Nat.card ↥(dualSub A) = 1 := by rw [h]; exact Subgroup.card_bot
      rw [card_dualSub hW] at this
      exact Subgroup.eq_bot_of_card_eq A this
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact (map_mul (dualAct W) a b).symm.trans
        ((congrArg (dualAct W) (hAe.1 a ha b hb)).trans (map_mul (dualAct W) b a))
    · rintro _ ⟨a, ha, rfl⟩
      exact (map_pow (dualAct W) a 2).symm.trans
        ((congrArg (dualAct W) (hAe.2 a ha)).trans (map_one _))
  have hr : Nat.card (DualGrp W) ≤ Nat.card ↥(dualSub A) * Nat.card ↥(fixV (dualSub A)) := by
    have h1 := dualAnn_card hW (commV A)
    rw [card_dualGrp hW, card_dualSub hW, fixV_dualSub]
    calc Nat.card W = Nat.card ↥(dualAnn (commV A)) * Nat.card ↥(commV A) := h1.symm
      _ ≤ Nat.card ↥(dualAnn (commV A)) * Nat.card ↥A := Nat.mul_le_mul_left _ hAc
      _ = Nat.card ↥A * Nat.card ↥(dualAnn (commV A)) := by ring
  have hXN : dualSub G ≤ Subgroup.normalizer (dualSub ρ.range : Set (MulAut (DualGrp W))) :=
    (Subgroup.map_mono hGN).trans (Subgroup.le_normalizer_map (dualAct W))
  have hXC : dualSub G ⊓ Subgroup.centralizer (dualSub ρ.range : Set (MulAut (DualGrp W))) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨g, hg, rfl⟩, hxc⟩
    rw [Subgroup.mem_bot]
    have hmem : g ∈ G ⊓ Subgroup.centralizer (ρ.range : Set (MulAut W)) := by
      refine ⟨hg, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
      have h1 := Subgroup.mem_centralizer_iff.1 hxc (dualAct W l) ⟨l, hl, rfl⟩
      apply dualAct_injective hW
      rw [map_mul, map_mul]
      exact h1
    rw [hGC, Subgroup.mem_bot] at hmem
    rw [hmem, map_one]
  have key := CFSG.Quasithin.H13.fixV_le_commV_of_g2 CFSG.Quasithin.H13.b46OffenderCommEqFix hY
    (Subgroup.map_mono hLG) hXN hXC hcommL0 hnat ⟨Subgroup.map_mono hAG, hA2.2⟩ hr
  have key' : fixV (dualSub G) ≤ commV (dualSub A) := key
  rw [fixV_dualSub, commV_dualSub hW] at key'
  exact (dualAnn_le_dualAnn_iff hW).1 key'

end DualStmts

section One

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.H13
  CFSG.Quasithin.H13.VolI in
theorem burnsideI17b_modQ_commV :
    commV ((g2Derived (ZMod 2)).map (g2QAct (ZMod 2))) = ⊤ := by
  rw [eq_top_iff]
  intro q _
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  have h := zornO0_gen m
  have hm : (QuotientGroup.mk m : ModQ) ∈ (Subgroup.closure
      {x | ∃ γ y, x = zornSecAct γ y * y⁻¹}).map
      (QuotientGroup.mk' ((zornR (ZMod 2)).subgroupOf (zornO0 (ZMod 2)))) := ⟨m, h, rfl⟩
  rw [MonoidHom.map_closure] at hm
  refine (Subgroup.closure_le _).2 ?_ hm
  rintro _ ⟨_, ⟨γ, y, rfl⟩, rfl⟩
  refine Subgroup.subset_closure ⟨g2QAct (ZMod 2) ⟨γ.1, g2Derived_two_le γ.2⟩,
    ⟨⟨γ.1, g2Derived_two_le γ.2⟩, Subgroup.mem_subgroupOf.2 γ.2, rfl⟩, QuotientGroup.mk y, ?_⟩
  rw [map_mul, map_inv]
  rfl

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.H13 in
theorem burnsideI17b_natV_one {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {W : Type} [CommGroup W] [Finite W]
    {G L : Subgroup (MulAut W)} {V : Subgroup W} (hLG : L ≤ G)
    (hVinv : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V)
    (ρ : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* MulAut W) (hrange : ρ.range = L)
    (hρV : ∀ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆, ∀ v ∈ V, ρ γ v ∈ V)
    (β : ↥V ≃* Multiplicative (Ix3 → K))
    (hβ : ∀ (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) (v : ↥V),
      β ⟨ρ γ (v : W), hρV γ v v.2⟩ = Multiplicative.ofAdd
        (g2Act (Subgroup.inclusion (burnsideI17b_comm_le_cayley K) γ) (Multiplicative.toAdd (β v)))) :
    G2NaturalDerived (burnsideI17b_img V (MulEquiv.refl ↥V) G hVinv L) ⊤ ⊥ 1 := by
  have hΓ := burnsideI17b_comm_le_cayley K
  refine ⟨K, inferInstance, inferInstance, by rw [hK, pow_one], ?_⟩
  have hρG : ∀ γ, ρ γ ∈ G := fun γ => hLG (hrange ▸ ⟨γ, rfl⟩)
  let r := burnsideI17b_rho V (MulEquiv.refl ↥V) G hVinv
  let π₁ : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* MulAut ↥V :=
    r.comp (ρ.codRestrict G hρG)
  have hπ₁ : ∀ γ, π₁ γ ∈ burnsideI17b_img V (MulEquiv.refl ↥V) G hVinv L := fun γ =>
    (burnsideI17b_mem_img V (MulEquiv.refl ↥V) G hVinv L _).2
      ⟨⟨ρ γ, hρG γ⟩, hrange ▸ ⟨γ, rfl⟩, rfl⟩
  let π' : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(burnsideI17b_img V (MulEquiv.refl ↥V) G hVinv L) :=
    π₁.codRestrict _ hπ₁
  have hπ's : Function.Surjective π' := by
    rintro ⟨y, hy⟩
    obtain ⟨a, haL, rfl⟩ := (burnsideI17b_mem_img V (MulEquiv.refl ↥V) G hVinv L y).1 hy
    have : (a : MulAut W) ∈ ρ.range := by rw [hrange]; exact haL
    obtain ⟨γ, hγ⟩ := this
    refine ⟨γ, Subtype.ext ?_⟩
    show π₁ γ = _
    show r ⟨ρ γ, hρG γ⟩ = _
    congr 1
    exact Subtype.ext hγ
  refine ⟨π', burnsideI17b_realizes_of_coord hΓ hπ's bot_le (fun _ _ _ => trivial)
    (fun h z hz => ?_) (β.toMonoidHom.comp (⊤ : Subgroup ↥V).subtype) ?_ ?_ ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz]
    exact map_one _
  · exact β.surjective.comp Subgroup.topEquiv.surjective
  · intro u
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    simp
  · intro γ u hu
    have h1 : ((π' γ : ↥(burnsideI17b_img V (MulEquiv.refl ↥V) G hVinv L)) : MulAut ↥V)
        (u : ↥V) = ⟨ρ γ ((u : ↥V) : W), hρV γ (u : ↥V) (u : ↥V).2⟩ :=
      burnsideI17b_rho_apply V (MulEquiv.refl ↥V) G hVinv ⟨ρ γ, hρG γ⟩ u.1
    show β (((π' γ : ↥(burnsideI17b_img V (MulEquiv.refl ↥V) G hVinv L)) : MulAut ↥V) u.1) = _
    rw [h1]
    exact hβ γ u.1

end One

section One2

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.H13
  CFSG.Quasithin.Vol2.Ch11.G2Q8

theorem burnsideI17b_main_one
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {G L : Subgroup (MulAut W)} {V : Subgroup W}
    (hL : L = quasithinGenFitting G) (hVinv : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V)
    (ρ : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* MulAut W) (hrange : ρ.range = L)
    (hρV : ∀ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆, ∀ v ∈ V, ρ γ v ∈ V)
    (β : ↥V ≃* Multiplicative (Ix3 → K))
    (hβ : ∀ (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) (v : ↥V),
      β ⟨ρ γ (v : W), hρV γ v v.2⟩ = Multiplicative.ofAdd
        (g2Act (Subgroup.inclusion (burnsideI17b_comm_le_cayley K) γ) (Multiplicative.toAdd (β v))))
    (hcomm : commV G ≤ V) (hfix : fixV G = ⊥) (hFF : IsFFModule G) : V = ⊤ := by
  have hΓ := burnsideI17b_comm_le_cayley K
  have hLG : L ≤ G := hL ▸ quasithinGenFitting_le G
  have hρG : ∀ γ, ρ γ ∈ G := fun γ => hLG (hrange ▸ ⟨γ, rfl⟩)
  have hρfaith : ∀ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆, (∀ v ∈ V, ρ γ v = v) → γ = 1 := by
    intro γ h
    have h1 : Subgroup.inclusion hΓ γ = 1 := by
      apply cayley_eq_one
      intro w
      obtain ⟨v, hv⟩ := β.surjective (Multiplicative.ofAdd w)
      have h2 := hβ γ v
      have h3 : (⟨ρ γ (v : W), hρV γ v v.2⟩ : ↥V) = v := Subtype.ext (h v v.2)
      rw [h3, hv] at h2
      exact (Multiplicative.ofAdd.injective h2).symm
    refine Subtype.ext ?_
    have h4 := congrArg Subtype.val h1
    exact h4
  have hLfaith : ∀ l ∈ L, (∀ v ∈ V, l v = v) → l = 1 := by
    intro l hl h
    rw [← hrange] at hl
    obtain ⟨γ, rfl⟩ := hl
    rw [hρfaith γ h, map_one]
  have hfaith := burnsideI17b_faithful hW hL hVinv hcomm hLfaith
  let r := burnsideI17b_rho V (MulEquiv.refl ↥V) G hVinv
  have hrinj : Function.Injective r :=
    burnsideI17b_rho_injective V (MulEquiv.refl ↥V) G hVinv hfaith
  have hnatV := burnsideI17b_natV_one hK hLG hVinv ρ hrange hρV β hβ
  obtain ⟨E, hE⟩ := CFSG.Quasithin.B42U33.exists_equiv_of_g2NaturalDerived hnatV
  set Lm := burnsideI17b_img V (MulEquiv.refl ↥V) G hVinv L with hLm
  have hDm : (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) = Lm.map (MulAut.congr E).toMonoidHom :=
    hE.symm
  have hfixLm : fixV Lm = ⊥ := by
    have h1 := CFSG.Quasithin.H13.U3.GC137.fixV_derived_Q
    rw [hDm, fixV_map_congr E Lm] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective (fixV Lm) (f := E.toMonoidHom) E.injective).1 h1
  have hcommLm : commV Lm = ⊤ := by
    have h1 := burnsideI17b_modQ_commV
    rw [hDm, commV_map_congr E Lm] at h1
    rw [eq_top_iff]
    intro v _
    have h2 : E v ∈ (commV Lm).map E.toMonoidHom := by rw [h1]; trivial
    obtain ⟨u, hu, hue⟩ := h2
    have h3 : u = v := E.injective hue
    rw [← h3]
    exact hu
  have hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    have h1 := le_normalizer_quasithinGenFitting G hg
    rw [← hL] at h1
    exact (Subgroup.mem_normalizer_iff.1 h1 l).1 hl
  have hVfix : ∀ y ∈ V, (∀ l ∈ L, l y = y) → y = 1 := by
    intro y hy h
    have hmem : (⟨y, hy⟩ : ↥V) ∈ fixV Lm :=
      (burnsideI17b_mem_fixV_img V (MulEquiv.refl ↥V) G hVinv hLG ⟨y, hy⟩).2
        (mem_fixV.2 h)
    rw [hfixLm, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hfixL : fixV L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxG : x ∈ fixV G := by
      rw [mem_fixV]
      intro g hg
      have hy : g x * x⁻¹ ∈ V := hcomm (Subgroup.subset_closure ⟨g, hg, x, rfl⟩)
      have hy1 : g x * x⁻¹ = 1 := by
        refine hVfix _ hy (fun l hl => ?_)
        have h1 : (g⁻¹ * l * g⁻¹⁻¹ : MulAut W) ∈ L := hnorm g⁻¹ (G.inv_mem hg) l hl
        have h2 := mem_fixV.1 hx _ h1
        have h3 : l (g x) = g x := by
          have : g⁻¹ (l (g x)) = x := by simpa [MulAut.mul_apply] using h2
          rw [MulAut.inv_apply, MulEquiv.symm_apply_eq] at this
          rw [this]
        rw [map_mul, map_inv, h3, mem_fixV.1 hx l hl]
      exact mul_inv_eq_one.1 hy1
    rw [hfix, Subgroup.mem_bot] at hxG
    exact hxG
  have hcommL : commV L = V := by
    apply le_antisymm
    · exact (commV_mono hLG).trans hcomm
    · intro v hv
      have hmem : (⟨v, hv⟩ : ↥V) ∈ commV Lm := by rw [hcommLm]; trivial
      have hle : commV Lm ≤ (commV L).comap V.subtype := by
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨x, hx, u, rfl⟩
        obtain ⟨g, hgL, rfl⟩ := (burnsideI17b_mem_img V (MulEquiv.refl ↥V) G hVinv L x).1 hx
        have h1 : (burnsideI17b_rho V (MulEquiv.refl ↥V) G hVinv g u : ↥V) =
            ⟨(g : MulAut W) (u : W), hVinv g g.2 u u.2⟩ :=
          burnsideI17b_rho_apply V (MulEquiv.refl ↥V) G hVinv g u
        show ((burnsideI17b_rho V (MulEquiv.refl ↥V) G hVinv g u * u⁻¹ : ↥V) : W) ∈ commV L
        rw [h1]
        exact Subgroup.subset_closure ⟨(g : MulAut W), hgL, (u : W), rfl⟩
      exact hle hmem
  have hGC : G ⊓ Subgroup.centralizer (ρ.range : Set (MulAut W)) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzG, hzC⟩
    rw [Subgroup.mem_bot]
    have hy : ∀ h ∈ (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)),
        MulAut.congr E (burnsideI17b_rho V (MulEquiv.refl ↥V) G hVinv ⟨z, hzG⟩) * h =
          h * MulAut.congr E (burnsideI17b_rho V (MulEquiv.refl ↥V) G hVinv ⟨z, hzG⟩) := by
      intro h hh
      rw [hDm] at hh
      obtain ⟨h0, hh0, rfl⟩ := hh
      obtain ⟨g, hgL, rfl⟩ := (burnsideI17b_mem_img V (MulEquiv.refl ↥V) G hVinv L h0).1 hh0
      have hgr : (g : MulAut W) ∈ (ρ.range : Set (MulAut W)) := by
        rw [SetLike.mem_coe, hrange]; exact hgL
      have hcz : (g : MulAut W) * z = z * (g : MulAut W) := Subgroup.mem_centralizer_iff.1 hzC _ hgr
      have hzg : (⟨z, hzG⟩ : ↥G) * g = g * ⟨z, hzG⟩ := Subtype.ext hcz.symm
      show MulAut.congr E (burnsideI17b_rho V (MulEquiv.refl ↥V) G hVinv ⟨z, hzG⟩) *
          MulAut.congr E (burnsideI17b_rho V (MulEquiv.refl ↥V) G hVinv g) =
        MulAut.congr E (burnsideI17b_rho V (MulEquiv.refl ↥V) G hVinv g) *
          MulAut.congr E (burnsideI17b_rho V (MulEquiv.refl ↥V) G hVinv ⟨z, hzG⟩)
      simp only [← map_mul, hzg]
    have hy1 := schur_Q _ hy
    have h2 : burnsideI17b_rho V (MulEquiv.refl ↥V) G hVinv ⟨z, hzG⟩ = 1 :=
      (MulAut.congr E).injective (hy1.trans (map_one _).symm)
    exact congrArg Subtype.val (hrinj (h2.trans (map_one _).symm))
  have hGrange : ∀ g : ↥G, MulAut.congr E (burnsideI17b_rho V (MulEquiv.refl ↥V) G hVinv g) ∈
      (g2QAct (ZMod 2)).range := by
    intro g
    refine normalizer_two_Q _ (fun h => ?_)
    rw [hDm, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have := burnsideI17b_img_normal V (MulEquiv.refl ↥V) G hVinv hLG hnorm g
      ((MulAut.congr E).symm h)
    rw [this]
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact Iff.rfl
  obtain ⟨A, hAG, hA1, hAe, hAr⟩ := hFF
  set Am := burnsideI17b_img V (MulEquiv.refl ↥V) G hVinv A with hAm
  have hcardAm : Nat.card ↥Am = Nat.card ↥A :=
    burnsideI17b_card_img V (MulEquiv.refl ↥V) G hVinv hfaith hAG
  have hAm1 : Am ≠ ⊥ := by
    intro h
    apply hA1
    have : Nat.card ↥Am = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hcardAm] at this
    exact Subgroup.eq_bot_of_card_eq A this
  have hAme : IsElemAbelian2 Am := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := (burnsideI17b_mem_img V (MulEquiv.refl ↥V) G hVinv A x).1 hx
      obtain ⟨b, hb, rfl⟩ := (burnsideI17b_mem_img V (MulEquiv.refl ↥V) G hVinv A y).1 hy
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAe.1 _ ha _ hb)
    · obtain ⟨a, ha, rfl⟩ := (burnsideI17b_mem_img V (MulEquiv.refl ↥V) G hVinv A x).1 hx
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (hAe.2 _ ha)
      rw [this, map_one]
  set Amq := Am.map (MulAut.congr E).toMonoidHom with hAmq
  have hAmq1 : Amq ≠ ⊥ := fun h =>
    hAm1 ((Subgroup.map_eq_bot_iff_of_injective Am (f := (MulAut.congr E).toMonoidHom)
      (MulAut.congr E).injective).1 h)
  have hAmqe : IsElemAbelian2 Amq := isElemAbelian2_map_congr E hAme
  have hAmqle : Amq ≤ (g2QAct (ZMod 2)).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, haA, rfl⟩ := (burnsideI17b_mem_img V (MulEquiv.refl ↥V) G hVinv A x).1 hx
    exact hGrange a
  have hcardAmq : Nat.card ↥Amq = Nat.card ↥A :=
    (Subgroup.card_map_of_injective (MulAut.congr E).injective).trans hcardAm
  have hfixAmq : Nat.card ↥(fixV Amq) = Nat.card ↥(V ⊓ fixV A) := by
    rw [hAmq, fixV_map_congr E Am, Subgroup.card_map_of_injective E.injective]
    exact burnsideI17b_card_fixV_img V (MulEquiv.refl ↥V) G hVinv hAG
  have hVQ : Nat.card ↥V = Nat.card ModQ := Nat.card_congr E.toEquiv
  have hoff : Nat.card ModQ ≤ Nat.card ↥Amq * Nat.card ↥(fixV Amq) := by
    rw [← hVQ, hcardAmq, hfixAmq]
    exact burnsideI17b_card_le_of_offender hAr
  obtain ⟨h8a, h8f⟩ := CFSG.Quasithin.B42U33.offender_exact hAmqle hAmq1 hAmqe hoff
  have hcomm8 : commV Amq = fixV Amq := offenderClaim_two_Q Amq hAmqle hAmq1 hAmqe hoff
  have hA8 : Nat.card ↥A = 8 := hcardAmq ▸ h8a
  have hC8 : Nat.card ↥(V ⊓ fixV A) = 8 := hfixAmq ▸ h8f
  have hV64 : Nat.card ↥V = 64 := hVQ.trans card_ModQ
  have hVA : Nat.card ↥V = Nat.card ↥A * Nat.card ↥(V ⊓ fixV A) := by rw [hA8, hC8, hV64]
  have hsup : V ⊔ fixV A = ⊤ := burnsideI17b_sup_eq_top hAr hVA
  have hcommA : Nat.card ↥(commV A) ≤ Nat.card ↥A := by
    have hle : commV A ≤ (commV Am).map V.subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, w, rfl⟩
      have hw : w ∈ V ⊔ fixV A := by rw [hsup]; trivial
      obtain ⟨v, hv, c, hc, hwvc⟩ := Subgroup.mem_sup.1 hw
      have hac : a c = c := mem_fixV.1 hc a ha
      have h1 : a w * w⁻¹ = a v * v⁻¹ := by
        rw [← hwvc, map_mul, hac, mul_inv_rev]
        group
      rw [h1]
      refine ⟨⟨a v, hVinv a (hAG ha) v hv⟩ * (⟨v, hv⟩ : ↥V)⁻¹, ?_, ?_⟩
      · refine Subgroup.subset_closure ⟨burnsideI17b_rho V (MulEquiv.refl ↥V) G hVinv ⟨a, hAG ha⟩,
          (burnsideI17b_mem_img V (MulEquiv.refl ↥V) G hVinv A _).2 ⟨⟨a, hAG ha⟩, ha, rfl⟩,
          ⟨v, hv⟩, ?_⟩
        exact burnsideI17b_rho_apply V (MulEquiv.refl ↥V) G hVinv ⟨a, hAG ha⟩ ⟨v, hv⟩ ▸ rfl
      · rfl
    calc Nat.card ↥(commV A) ≤ Nat.card ↥((commV Am).map V.subtype) := Subgroup.card_le_of_le hle
      _ = Nat.card ↥(commV Am) := Subgroup.card_map_of_injective V.subtype_injective
      _ = Nat.card ↥(commV Amq) := by
        rw [hAmq, commV_map_congr E Am, Subgroup.card_map_of_injective E.injective]
      _ = Nat.card ↥(fixV Amq) := by rw [hcomm8]
      _ = Nat.card ↥A := by rw [h8f, hA8]
  have hfixLr : fixV ρ.range = ⊥ := by rw [hrange]; exact hfixL
  have hcommLr : commV ρ.range = V := by rw [hrange]; exact hcommL
  have hGN : G ≤ Subgroup.normalizer (ρ.range : Set (MulAut W)) := by
    rw [hrange, hL]
    exact le_normalizer_quasithinGenFitting G
  have hfA : fixV A ≤ commV G :=
    burnsideI17b_dual_one hK hW ρ V hρV β hβ G (hrange ▸ hLG) hGN hGC hfixLr hcommLr
      ⟨hAG, hA1, hAe⟩ hcommA
  have hfAV : fixV A ≤ V := hfA.trans hcomm
  rw [sup_eq_left.2 hfAV] at hsup
  exact hsup

end One2

section Main

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8

theorem burnsideI17b_main_ge2 (hqs : burnsideB46_G2Qs) {n : ℕ} (hn : 2 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {G L : Subgroup (MulAut W)} {V : Subgroup W}
    (hL : L = quasithinGenFitting G) (hVinv : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V)
    (πW : ↥(cayleyGroup K) →* MulAut W) (hrange : πW.range = L)
    (hπV : ∀ γ : ↥(cayleyGroup K), ∀ v ∈ V, πW γ v ∈ V)
    (β : ↥V ≃* Multiplicative (Ix3 → K))
    (hβ : ∀ (γ : ↥(cayleyGroup K)) (v : ↥V), β ⟨πW γ (v : W), hπV γ v v.2⟩ =
      Multiplicative.ofAdd (g2Act γ (Multiplicative.toAdd (β v))))
    (hcomm : commV G ≤ V) (hfix : fixV G = ⊥) (hFF : IsFFModule G) : V = ⊤ := by
  have hLG : L ≤ G := hL ▸ quasithinGenFitting_le G
  have hc : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := exists_ne_zero_ne_one_of_card hn hK
  have hπfaith : ∀ γ : ↥(cayleyGroup K), (∀ v ∈ V, πW γ v = v) → γ = 1 := by
    intro γ h
    apply cayley_eq_one
    intro w
    obtain ⟨v, hv⟩ := β.surjective (Multiplicative.ofAdd w)
    have h1 := hβ γ v
    have h2 : (⟨πW γ (v : W), hπV γ v v.2⟩ : ↥V) = v := Subtype.ext (h v v.2)
    rw [h2, hv] at h1
    exact (Multiplicative.ofAdd.injective h1).symm
  have hπinj : Function.Injective πW := by
    rw [injective_iff_map_eq_one]
    intro γ h
    exact hπfaith γ (fun v _ => by rw [h]; rfl)
  have hLfaith : ∀ l ∈ L, (∀ v ∈ V, l v = v) → l = 1 := by
    intro l hl h
    rw [← hrange] at hl
    obtain ⟨γ, rfl⟩ := hl
    rw [hπfaith γ h, map_one]
  have hfaith := burnsideI17b_faithful hW hL hVinv hcomm hLfaith
  set ρ := burnsideI17b_rho V β G hVinv with hρdef
  have hρinj : Function.Injective ρ := burnsideI17b_rho_injective V β G hVinv hfaith
  have hρπ : ∀ (γ : ↥(cayleyGroup K)) (hγ : πW γ ∈ G),
      ρ ⟨πW γ, hγ⟩ = burnsideB46_pi burnsideB46_neg_pi γ := by
    intro γ hγ
    refine MulEquiv.ext fun m => ?_
    obtain ⟨v, rfl⟩ := β.surjective m
    rw [hρdef, burnsideI17b_rho_apply V β G hVinv ⟨πW γ, hγ⟩ v]
    apply Multiplicative.toAdd.injective
    rw [burnsideI17b_negc_apply, hβ γ v]
    rfl
  have hLm : burnsideI17b_img V β G hVinv L = burnsideB46_neg_L := by
    ext x
    rw [burnsideI17b_mem_img]
    constructor
    · rintro ⟨a, haL, rfl⟩
      have haL' : (a : MulAut W) ∈ πW.range := by rw [hrange]; exact haL
      obtain ⟨γ, hγ⟩ := haL'
      have : a = ⟨πW γ, hγ ▸ a.2⟩ := Subtype.ext hγ.symm
      rw [this, hρπ γ _]
      exact ⟨burnsideB46_cg.symm γ, rfl⟩
    · rintro ⟨γ', rfl⟩
      have hmem : πW (burnsideB46_cg γ') ∈ L := by rw [← hrange]; exact ⟨_, rfl⟩
      refine ⟨⟨πW (burnsideB46_cg γ'), hLG hmem⟩, hmem, ?_⟩
      rw [hρπ]
      simp [burnsideB46_pi_apply]
  have hFm : quasithinGenFitting ρ.range = burnsideB46_neg_L := by
    rw [burnsideI17b_genFitting_range ρ hρinj, burnsideI17b_genFitting_eq_subgroupOf G, ← hL]
    exact hLm
  have hLGm : burnsideB46_neg_L ≤ ρ.range := by
    rw [← hLm]
    rintro _ ⟨a, _, rfl⟩
    exact ⟨a, rfl⟩
  have H := burnsideI17b_hyp_big hqs hn hK hLGm hFm
  have hfixneg : fixV (burnsideB46_neg_L (K := K)) = ⊥ := burnsideI17b_neg_fixV hc
  obtain ⟨A, hAG, hA1, hAe, hAr⟩ := hFF
  set Am := burnsideI17b_img V β G hVinv A with hAm
  have hAmG : Am ≤ ρ.range := by
    rintro _ ⟨a, _, rfl⟩
    exact ⟨a, rfl⟩
  have hcardAm : Nat.card ↥Am = Nat.card ↥A := burnsideI17b_card_img V β G hVinv hfaith hAG
  have hAm1 : Am ≠ ⊥ := by
    intro h
    apply hA1
    have : Nat.card ↥Am = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hcardAm] at this
    exact Subgroup.eq_bot_of_card_eq A this
  have hAme : IsElemAbelian2 Am := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := (burnsideI17b_mem_img V β G hVinv A x).1 hx
      obtain ⟨b, hb, rfl⟩ := (burnsideI17b_mem_img V β G hVinv A y).1 hy
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAe.1 _ ha _ hb)
    · obtain ⟨a, ha, rfl⟩ := (burnsideI17b_mem_img V β G hVinv A x).1 hx
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (hAe.2 _ ha)
      rw [this, map_one]
  have hVQ : Nat.card ↥V = Nat.card (Multiplicative (Ix3 → K)) := Nat.card_congr β.toEquiv
  have hAmff : Nat.card (Multiplicative (Ix3 → K)) ≤ Nat.card ↥Am * Nat.card ↥(fixV Am) := by
    rw [← hVQ, hcardAm, burnsideI17b_card_fixV_img V β G hVinv hAG]
    exact burnsideI17b_card_le_of_offender hAr
  haveI : Finite (Multiplicative (Ix3 → K)) := inferInstance
  obtain ⟨hAmL, hAm3, hAmfix⟩ := burnsideB46_of_offender hqs H hn hAmG hAme hAm1 hAmff
  obtain ⟨x, hx⟩ := burnsideB46_of_offender_conj hqs H hn hAmG hAme hAm1 hAmff
  have hcardQ := burnsideB46_of_card_V H
  rw [hfixneg, Subgroup.card_bot, one_mul] at hAmfix hcardQ
  have hVA : Nat.card ↥V = Nat.card ↥A * Nat.card ↥(V ⊓ fixV A) := by
    rw [hVQ, hcardQ, ← hcardAm, ← burnsideI17b_card_fixV_img V β G hVinv hAG, hAmfix, hAm3]
    ring
  have hsup : V ⊔ fixV A = ⊤ := burnsideI17b_sup_eq_top hAr hVA
  have hAeq : A = ((A1 K).map (MulAut.conj x).toMonoidHom).map πW := by
    have hπL : ∀ y, πW y ∈ G := fun y => hLG (hrange ▸ ⟨y, rfl⟩)
    ext a
    constructor
    · intro ha
      have h1 : ρ ⟨a, hAG ha⟩ ∈ Am := (burnsideI17b_mem_img V β G hVinv A _).2 ⟨⟨a, hAG ha⟩, ha, rfl⟩
      rw [hx] at h1
      obtain ⟨z, hz, hzρ⟩ := h1
      refine ⟨z, hz, ?_⟩
      have h2 : ρ ⟨πW z, hπL z⟩ = ρ ⟨a, hAG ha⟩ := by rw [hρπ z (hπL z)]; exact hzρ
      exact congrArg Subtype.val (hρinj h2)
    · rintro ⟨y, hy, rfl⟩
      have h1 : burnsideB46_pi burnsideB46_neg_pi y ∈ Am := by
        rw [hx]
        exact ⟨y, hy, rfl⟩
      obtain ⟨a', ha', h2⟩ := (burnsideI17b_mem_img V β G hVinv A _).1 h1
      rw [← hρπ y (hπL y)] at h2
      have h3 := congrArg Subtype.val (hρinj h2)
      rw [h3] at ha'
      exact ha'
  have hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    have h1 := le_normalizer_quasithinGenFitting G hg
    rw [← hL] at h1
    exact (Subgroup.mem_normalizer_iff.1 h1 l).1 hl
  have hVfix : ∀ y ∈ V, (∀ l ∈ L, l y = y) → y = 1 := by
    intro y hy h
    have hmem : β ⟨y, hy⟩ ∈ fixV (burnsideB46_neg_L (K := K)) := by
      rw [mem_fixV]
      rintro _ ⟨γ', rfl⟩
      have hπ : πW (burnsideB46_cg γ') ∈ L := by rw [← hrange]; exact ⟨_, rfl⟩
      have h1 := hβ (burnsideB46_cg γ') ⟨y, hy⟩
      have h2 : (⟨πW (burnsideB46_cg γ') y, hπV _ y hy⟩ : ↥V) = ⟨y, hy⟩ :=
        Subtype.ext (h _ hπ)
      rw [h2] at h1
      apply Multiplicative.toAdd.injective
      rw [burnsideB46_neg_pi_apply]
      have h3 := congrArg Multiplicative.toAdd h1
      rw [toAdd_ofAdd] at h3
      exact h3.symm
    rw [hfixneg, Subgroup.mem_bot] at hmem
    have := β.injective (hmem.trans (map_one β).symm)
    exact congrArg Subtype.val this
  have hfixL : fixV L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxG : x ∈ fixV G := by
      rw [mem_fixV]
      intro g hg
      have hy : g x * x⁻¹ ∈ V := hcomm (Subgroup.subset_closure ⟨g, hg, x, rfl⟩)
      have hy1 : g x * x⁻¹ = 1 := by
        refine hVfix _ hy (fun l hl => ?_)
        have h1 : (g⁻¹ * l * g⁻¹⁻¹ : MulAut W) ∈ L := hnorm g⁻¹ (G.inv_mem hg) l hl
        have h2 := mem_fixV.1 hx _ h1
        have h3 : l (g x) = g x := by
          have : g⁻¹ (l (g x)) = x := by simpa [MulAut.mul_apply] using h2
          rw [MulAut.inv_apply, MulEquiv.symm_apply_eq] at this
          rw [this]
        rw [map_mul, map_inv, h3, mem_fixV.1 hx l hl]
      exact mul_inv_eq_one.1 hy1
    rw [hfix, Subgroup.mem_bot] at hxG
    exact hxG
  have hcommL : commV L = V := by
    apply le_antisymm
    · exact (commV_mono hLG).trans hcomm
    · intro v hv
      have htop : commV (burnsideB46_neg_L (K := K)) = ⊤ := burnsideB46_neg_comm hc
      have hmem : β ⟨v, hv⟩ ∈ commV (burnsideB46_neg_L (K := K)) := by rw [htop]; trivial
      let S : Subgroup ↥V := (commV L).comap V.subtype
      have hle : commV (burnsideB46_neg_L (K := K)) ≤ S.map β.toMonoidHom := by
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨y, ⟨γ', rfl⟩, m, rfl⟩
        obtain ⟨u, rfl⟩ := β.surjective m
        have hπ : πW (burnsideB46_cg γ') ∈ L := by rw [← hrange]; exact ⟨_, rfl⟩
        have h1 := hβ (burnsideB46_cg γ') u
        refine ⟨⟨πW (burnsideB46_cg γ') (u : W), hπV _ u u.2⟩ * u⁻¹, ?_, ?_⟩
        · show ((⟨πW (burnsideB46_cg γ') (u : W), hπV _ u u.2⟩ * u⁻¹ : ↥V) : W) ∈ commV L
          exact Subgroup.subset_closure ⟨πW (burnsideB46_cg γ'), hπ, (u : W), rfl⟩
        · show β (⟨πW (burnsideB46_cg γ') (u : W), hπV _ u u.2⟩ * u⁻¹) = _
          rw [map_mul, map_inv, h1]
          congr 1
      obtain ⟨s, hs, hsβ⟩ := hle hmem
      have : s = ⟨v, hv⟩ := β.injective hsβ
      rw [this] at hs
      exact hs
  have hdual := burnsideI17b_dual_ge2 hqs hn hK hW πW hπinj V hπV β hβ
    (by rw [hrange]; exact hfixL) (by rw [hrange]; exact hcommL) x
  rw [← hAeq] at hdual
  have hfA : fixV A ≤ V := burnsideI17b_fixV_le_of_dual hW hdual
  rw [sup_eq_left.2 hfA] at hsup
  exact hsup

open CFSG.Quasithin.B513N in
theorem burnsideI17b_ge2 (hqs : burnsideB46_G2Qs) {n : ℕ} (hn : 2 ≤ n)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {G L : Subgroup (MulAut W)} {V : Subgroup W}
    (hL : L = quasithinGenFitting G) (hVinv : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V)
    (hNat : G2NaturalDerived L V ⊥ n) (hcomm : commV G ≤ V) (hfix : fixV G = ⊥)
    (hFF : IsFFModule G) : V = ⊤ := by
  obtain ⟨K, _, _, hK, hR⟩ := hNat
  haveI : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  haveI : CharP K 2 := charP_of_card_eq_prime_pow hF
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  have heq : ⁅quasithinG2 K, quasithinG2 K⁆ = quasithinG2 K :=
    (g2Derived_eq hc0 hc1).trans
      CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup.symm
  rw [heq] at hR
  obtain ⟨π₀, hπ₀⟩ := hR
  let π : ↥(quasithinG2 K) →* ↥L := π₀
  have hπ : (FFModel.zornQ (quasithinG2 K)).RealizesVia L V ⊥ π := hπ₀
  have hΓ : quasithinG2 K ≤ cayleyGroup K :=
    (CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)).le
  obtain ⟨β₀, hβs, hβk, hβe⟩ := g2_coord hΓ hπ
  have hUinv := hπ.2.2.2.1
  have hπs : Function.Surjective π := hπ.1
  let β : ↥V ≃* Multiplicative (Ix3 → K) := MulEquiv.ofBijective β₀
    ⟨(MonoidHom.ker_eq_bot_iff β₀).1 (by
      rw [eq_bot_iff]
      intro u hu
      have := (hβk u).1 hu
      rw [Subgroup.mem_bot] at this ⊢
      exact Subtype.ext this), hβs⟩
  let πW : ↥(cayleyGroup K) →* MulAut W :=
    L.subtype.comp (π.comp burnsideB46_cg.symm.toMonoidHom)
  have hπW : ∀ γ : ↥(cayleyGroup K), πW γ = ((π (burnsideB46_cg.symm γ) : ↥L) : MulAut W) :=
    fun _ => rfl
  have hrange : πW.range = L := by
    ext l
    constructor
    · rintro ⟨γ, rfl⟩
      rw [hπW]
      exact (π (burnsideB46_cg.symm γ)).2
    · intro hl
      obtain ⟨γ', hγ'⟩ := hπs ⟨l, hl⟩
      refine ⟨burnsideB46_cg γ', ?_⟩
      rw [hπW, MulEquiv.symm_apply_apply]
      exact congrArg Subtype.val hγ'
  have hπV : ∀ γ : ↥(cayleyGroup K), ∀ v ∈ V, πW γ v ∈ V := fun γ v hv => by
    rw [hπW]
    exact hUinv (π (burnsideB46_cg.symm γ)) v hv
  have hβ : ∀ (γ : ↥(cayleyGroup K)) (v : ↥V), β ⟨πW γ (v : W), hπV γ v v.2⟩ =
      Multiplicative.ofAdd (g2Act γ (Multiplicative.toAdd (β v))) := by
    intro γ v
    have h1 := hβe (burnsideB46_cg.symm γ) v (hπV γ v v.2)
    have hincl : Subgroup.inclusion hΓ (burnsideB46_cg.symm γ) = γ := Subtype.ext rfl
    rw [hincl] at h1
    exact h1
  exact burnsideI17b_main_ge2 hqs hn hK hW hL hVinv πW hrange hπV β hβ hcomm hfix hFF

open CFSG.Quasithin.B513N in
theorem burnsideI17b_one
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {G L : Subgroup (MulAut W)} {V : Subgroup W}
    (hL : L = quasithinGenFitting G) (hVinv : ∀ g ∈ G, ∀ v ∈ V, g v ∈ V)
    (hNat : G2NaturalDerived L V ⊥ 1) (hcomm : commV G ≤ V) (hfix : fixV G = ⊥)
    (hFF : IsFFModule G) : V = ⊤ := by
  obtain ⟨K, _, _, hK, hR⟩ := hNat
  have hK' : Nat.card K = 2 := by rw [hK, pow_one]
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by
    rw [Nat.card_eq_fintype_card] at hK'
    rw [hK', pow_one])
  obtain ⟨π₀, hπ₀⟩ := hR
  let π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥L := π₀
  have hπ : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia L V ⊥ π := hπ₀
  have hΓ := burnsideI17b_comm_le_cayley K
  obtain ⟨β₀, hβs, hβk, hβe⟩ := g2_coord hΓ hπ
  have hUinv := hπ.2.2.2.1
  have hπs : Function.Surjective π := hπ.1
  let β : ↥V ≃* Multiplicative (Ix3 → K) := MulEquiv.ofBijective β₀
    ⟨(MonoidHom.ker_eq_bot_iff β₀).1 (by
      rw [eq_bot_iff]
      intro u hu
      have := (hβk u).1 hu
      rw [Subgroup.mem_bot] at this ⊢
      exact Subtype.ext this), hβs⟩
  let ρ : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* MulAut W := L.subtype.comp π
  have hρπ : ∀ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆, ρ γ = ((π γ : ↥L) : MulAut W) := fun _ => rfl
  have hrange : ρ.range = L := by
    ext l
    constructor
    · rintro ⟨γ, rfl⟩
      rw [hρπ]
      exact (π γ).2
    · intro hl
      obtain ⟨γ, hγ⟩ := hπs ⟨l, hl⟩
      exact ⟨γ, by rw [hρπ, hγ]⟩
  have hρV : ∀ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆, ∀ v ∈ V, ρ γ v ∈ V := fun γ v hv => by
    rw [hρπ]
    exact hUinv (π γ) v hv
  have hβ : ∀ (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) (v : ↥V),
      β ⟨ρ γ (v : W), hρV γ v v.2⟩ = Multiplicative.ofAdd
        (g2Act (Subgroup.inclusion (burnsideI17b_comm_le_cayley K) γ)
          (Multiplicative.toAdd (β v))) := fun γ v => hβe γ v (hρV γ v v.2)
  exact burnsideI17b_main_one hK' hW hL hVinv ρ hrange hρV β hβ hcomm hfix hFF

end Main

section Final

theorem as_I_1_7b : I_1_7b := by
  intro W _ _ hW G L V n hL hVinv hNat hcomm hfix hFF
  have hn1 : 1 ≤ n := by
    obtain ⟨K, _, _, hK, -⟩ := hNat
    by_contra h0
    have : n = 0 := by omega
    rw [this, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact burnsideI17b_one hW hL hVinv hNat hcomm hfix hFF
  · exact burnsideI17b_ge2 burnsideB46_G2Qs_of_cert h hW hL hVinv hNat hcomm hfix hFF

end Final

end CFSG.ASVolI
