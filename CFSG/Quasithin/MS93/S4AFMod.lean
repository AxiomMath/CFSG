module

public import CFSG.Quasithin.MS93.S46FFExt
public import CFSG.Quasithin.MS93.S4A42Cob
public import CFSG.Quasithin.Background.D14Dual

public section

namespace CFSG.Quasithin.MS93.S4A.F

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S46
open scoped Matrix

section Res

variable {G : Type*} [Group G] {X : Type} [CommGroup X]

@[expose] def resRho (ρ : G →* MulAut X) (M : Subgroup X) (hM : ∀ g, ∀ m ∈ M, ρ g m ∈ M) :
    G →* MulAut ↥M where
  toFun g :=
    { toFun := fun m => ⟨ρ g m, hM g m m.2⟩
      invFun := fun m => ⟨ρ g⁻¹ m, hM g⁻¹ m m.2⟩
      left_inv := fun m => Subtype.ext (by simp)
      right_inv := fun m => Subtype.ext (by simp)
      map_mul' := fun m m' => Subtype.ext (by simp) }
  map_one' := MulEquiv.ext fun m => Subtype.ext (by simp)
  map_mul' g h := MulEquiv.ext fun m => Subtype.ext (by simp)

theorem coe_resRho_apply (ρ : G →* MulAut X) (M : Subgroup X) (hM : ∀ g, ∀ m ∈ M, ρ g m ∈ M)
    (g : G) (m : ↥M) : ((resRho ρ M hM g m : ↥M) : X) = ρ g m :=
  rfl

end Res

section Faithful

variable {F : Type} [Field F] [Finite F] {X : Type} [CommGroup X]

theorem inf_ker_eq_bot (ρ : SL3 F →* MulAut X) (hnt : ∃ g x, ρ g x ≠ x)
    {B : Subgroup (SL3 F)} (hB2 : ∀ b ∈ B, b ^ 2 = 1) : B ⊓ ρ.ker = ⊥ := by
  rw [eq_bot_iff]
  rintro b ⟨hb, hbk⟩
  have hc := ker_le_center ρ hnt hbk
  exact eq_one_of_pow_three (pow_three_eq_one_of_mem_center hc) (e := 1)
    (by simpa using hB2 b hb)

theorem card_map_eq (ρ : SL3 F →* MulAut X) (hnt : ∃ g x, ρ g x ≠ x)
    {B : Subgroup (SL3 F)} (hB2 : ∀ b ∈ B, b ^ 2 = 1) : Nat.card (B.map ρ) = Nat.card B := by
  have h := B1More.card_map_mul_card_inf_ker B ρ
  rwa [inf_ker_eq_bot ρ hnt hB2, Subgroup.card_bot, mul_one] at h

omit [Finite F] in
theorem isElemAbelian2_map (ρ : SL3 F →* MulAut X) {B : Subgroup (SL3 F)}
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) :
    IsElemAbelian2 (B.map ρ) := by
  constructor
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    rw [← map_mul, ← map_mul, hBc b hb b' hb']
  · rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB2 b hb, map_one]

theorem map_ne_bot (ρ : SL3 F →* MulAut X) (hnt : ∃ g x, ρ g x ≠ x) {B : Subgroup (SL3 F)}
    (hB : B ≠ ⊥) (hB2 : ∀ b ∈ B, b ^ 2 = 1) : B.map ρ ≠ ⊥ := by
  intro h
  apply hB
  have h1 : Nat.card B = 1 := by rw [← card_map_eq ρ hnt hB2, h, Subgroup.card_bot]
  exact Subgroup.eq_bot_of_card_eq B h1

theorem fix_of_fix (ρ : SL3 F →* MulAut X) {M : Subgroup X} (hM : ∀ g, ∀ m ∈ M, ρ g m ∈ M)
    {B : Subgroup (SL3 F)} (hB : B ≠ ⊥) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hBM : ∀ b ∈ B, ∀ m ∈ M, ρ b m = m) : ∀ g, ∀ m ∈ M, ρ g m = m := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g, m, hm, hgm⟩ := hcon
  have hnt : ∃ g, ∃ x : ↥M, resRho ρ M hM g x ≠ x :=
    ⟨g, ⟨m, hm⟩, fun h => hgm (congrArg Subtype.val h)⟩
  apply map_ne_bot (resRho ρ M hM) hnt hB hB2
  rw [eq_bot_iff]
  rintro _ ⟨b, hb, rfl⟩
  rw [Subgroup.mem_bot]
  exact MulEquiv.ext fun x => Subtype.ext (hBM b hb x x.2)

end Faithful

section DualNat

variable {X : Type} [CommGroup X] [Finite X]

theorem card_rootGroup02 {F' : Type} [Field F'] :
    Nat.card (rootGroup 0 2 : Subgroup (SL3 F')) = Nat.card F' :=
  Nat.card_range_of_injective (rootElt_injective (F := F') (by decide : (0 : Fin 3) ≠ 2))

theorem card_commN_rootGroup02_le {F' : Type} [Field F'] [Finite F'] :
    Nat.card (commN (rootGroup 0 2 : Subgroup (SL3 F'))) ≤ Nat.card F' := by
  rw [commN_rootGroup (by decide)]
  refine Nat.card_le_card_of_surjective
    (fun c : F' => (⟨Pi.single 0 c, fun k hk => by simp [Pi.single_eq_of_ne hk]⟩ :
      ↥(coordLine (0 : Fin 3) : Submodule F' (Fin 3 → F')))) ?_
  rintro ⟨y, hy⟩
  refine ⟨y 0, Subtype.ext ?_⟩
  funext k
  by_cases hk : k = 0
  · subst hk
    simp
  · simp [Pi.single_eq_of_ne hk, hy k hk]

omit [Finite X] in
theorem dualGrp_sq (f : DualGrp X) : f ^ 2 = 1 := by
  refine DualGrp.ext fun x => ?_
  have h : ∀ m : Multiplicative (ZMod 2), m ^ 2 = 1 := by decide
  exact h (f x)

omit [Finite X] in
theorem dualAnn_top : dualAnn (⊤ : Subgroup X) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  exact DualGrp.ext fun x => hf x (Subgroup.mem_top x)

abbrev ActOn (G : Type*) [Group G] (V : Type*) [CommGroup V] : Type _ := G →* MulAut V

@[expose] noncomputable def dualRho {G : Type*} [Group G] (ρ : G →* MulAut X) :
    ActOn G (DualGrp X) :=
  (dualAct X).comp ρ

omit [Finite X] in
theorem dualRho_apply {G : Type*} [Group G] (ρ : G →* MulAut X) (g : G) (f : DualGrp X)
    (x : X) : (dualRho ρ g f) x = f (ρ g⁻¹ x) := by
  change f ((ρ g)⁻¹ x) = f (ρ g⁻¹ x)
  rw [map_inv]

omit [Finite X] in
theorem range_dualRho {G : Type*} [Group G] (ρ : G →* MulAut X) :
    (dualRho ρ).range = dualSub ρ.range := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨ρ g, ⟨g, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩

omit [Finite X] in
theorem fixV_map_dualRho {G : Type*} [Group G] (ρ : G →* MulAut X) (A : Subgroup G) :
    fixV (A.map (dualRho ρ)) = dualAnn (commV (A.map ρ)) := by
  ext f
  rw [mem_dualAnn_commV]
  constructor
  · rintro h _ ⟨g, hg, rfl⟩ v
    have h1 := congrArg (fun φ : DualGrp X => φ v) (h (dualRho ρ g⁻¹) ⟨g⁻¹, A.inv_mem hg, rfl⟩)
    change f ((ρ g⁻¹)⁻¹ v) = f v at h1
    rwa [← map_inv, inv_inv] at h1
  · rintro h _ ⟨g, hg, rfl⟩
    refine DualGrp.ext fun v => ?_
    change f ((ρ g)⁻¹ v) = f v
    rw [← map_inv]
    exact h (ρ g⁻¹) ⟨g⁻¹, A.inv_mem hg, rfl⟩ v

omit [Finite X] in
theorem fixV_range_dualRho {G : Type*} [Group G] (ρ : G →* MulAut X) :
    fixV (dualRho ρ).range = dualAnn (commV ρ.range) := by
  ext f
  rw [mem_dualAnn_commV]
  constructor
  · rintro h _ ⟨g, rfl⟩ v
    have h1 := congrArg (fun φ : DualGrp X => φ v) (h (dualRho ρ g⁻¹) ⟨g⁻¹, rfl⟩)
    change f ((ρ g⁻¹)⁻¹ v) = f v at h1
    rwa [← map_inv, inv_inv] at h1
  · rintro h _ ⟨g, rfl⟩
    refine DualGrp.ext fun v => ?_
    change f ((ρ g)⁻¹ v) = f v
    rw [← map_inv]
    exact h (ρ g⁻¹) ⟨g⁻¹, rfl⟩ v

theorem commV_range_dualRho (hX2 : ∀ x : X, x ^ 2 = 1) {G : Type*} [Group G]
    (ρ : G →* MulAut X) : commV (dualRho ρ).range = dualAnn (fixV ρ.range) := by
  rw [← commV_dualSub hX2]
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
  · rintro _ ⟨_, ⟨g, rfl⟩, f, rfl⟩
    exact Subgroup.subset_closure ⟨dualAct X (ρ g), ⟨ρ g, ⟨g, rfl⟩, rfl⟩, f, rfl⟩
  · rintro _ ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, f, rfl⟩
    exact Subgroup.subset_closure ⟨dualRho ρ g, ⟨g, rfl⟩, f, rfl⟩

theorem commV_map_dualRho (hX2 : ∀ x : X, x ^ 2 = 1) {G : Type*} [Group G]
    (ρ : G →* MulAut X) (A : Subgroup G) :
    commV (A.map (dualRho ρ)) = dualAnn (fixV (A.map ρ)) := by
  rw [← commV_dualSub hX2]
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, f, rfl⟩
    exact Subgroup.subset_closure ⟨dualAct X (ρ g), ⟨ρ g, ⟨g, hg, rfl⟩, rfl⟩, f, rfl⟩
  · rintro _ ⟨_, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, f, rfl⟩
    exact Subgroup.subset_closure ⟨dualRho ρ g, ⟨g, hg, rfl⟩, f, rfl⟩

omit [Finite X] in
theorem dualRho_eq_one_iff (hX2 : ∀ x : X, x ^ 2 = 1) {G : Type*} [Group G]
    (ρ : G →* MulAut X) (g : G) : dualRho ρ g = 1 ↔ ρ g = 1 := by
  constructor
  · intro h
    apply dualAct_injective hX2
    rw [map_one]
    exact h
  · intro h
    change dualAct X (ρ g) = 1
    rw [h, map_one]

theorem isFFModule_of_natCoord_dual (hX2 : ∀ x : X, x ^ 2 = 1) {G : Type*} [Group G]
    (ρ : G →* MulAut X) {F' : Type} [Field F'] [Finite F'] [CharP F' 2]
    {σ : SL3 F' ≃* ↥(dualRho ρ).range} {θ : DualGrp X ≃* Multiplicative (Fin 3 → F')}
    (hθ : IsNatCoord σ θ) : IsFFModule ρ.range := by
  set E : Subgroup (SL3 F') := rootGroup 0 2 with hE
  set Bs := E.map (((dualRho ρ).range).subtype.comp σ.toMonoidHom) with hBs
  have hinj : Function.Injective (((dualRho ρ).range).subtype.comp σ.toMonoidHom) :=
    ((dualRho ρ).range).subtype_injective.comp σ.injective
  have hBsK : Bs ≤ (dualRho ρ).range := by
    rintro _ ⟨e, -, rfl⟩
    exact (σ e).2
  have hEB : ∀ g, g ∈ E ↔ (σ g).1 ∈ Bs := by
    intro g
    constructor
    · intro hg
      exact ⟨g, hg, rfl⟩
    · rintro ⟨e, he, hge⟩
      have : e = g := hinj hge
      rw [← this]
      exact he
  set E' : Subgroup G := Bs.comap (dualRho ρ) with hE'
  have hE'map : E'.map (dualRho ρ) = Bs := Subgroup.map_comap_eq_self hBsK
  set B : Subgroup (MulAut X) := E'.map ρ with hB
  have hker : (dualRho ρ).ker = ρ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact dualRho_eq_one_iff hX2 ρ g
  have hcard : Nat.card B = Nat.card Bs := by
    rw [hB, ← Subgroup.relIndex_ker E' ρ, ← hker, Subgroup.relIndex_ker E' (dualRho ρ), hE'map]
  have hcB : Nat.card B = Nat.card F' := by
    rw [hcard, hBs, Subgroup.card_map_of_injective hinj, hE, card_rootGroup02]
  have hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    rw [← rootElt_add, ← rootElt_add, add_comm]
  have hE2 : ∀ e ∈ E, e ^ 2 = 1 := by
    rintro _ ⟨c, rfl⟩
    rw [sq, ← rootElt_add, CharTwo.add_self_eq_zero, rootElt_zero]
  have hBsc : ∀ x ∈ Bs, ∀ y ∈ Bs, x * y = y * x := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    rw [← map_mul, ← map_mul, hEc e he e' he']
  have hBs2 : ∀ x ∈ Bs, x ^ 2 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hE2 e he, map_one]
  have hBe : IsElemAbelian2 B := by
    constructor
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      have h1 : dualRho ρ (g * g' * (g' * g)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, hBsc _ hg _ hg', mul_inv_cancel]
      rw [dualRho_eq_one_iff hX2, map_mul, map_inv, mul_inv_eq_one] at h1
      rwa [map_mul, map_mul] at h1
    · rintro _ ⟨g, hg, rfl⟩
      have h1 : dualRho ρ (g ^ 2) = 1 := by rw [map_pow]; exact hBs2 _ hg
      rwa [dualRho_eq_one_iff hX2, map_pow] at h1
  have hB1 : B ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card F' = 1 := by rw [← hcB, hbot, Subgroup.card_bot]
    have h2 : 1 < Nat.card F' := Finite.one_lt_card
    omega
  refine ⟨B, Subgroup.map_le_range ρ E', hB1, hBe, ?_⟩
  have h1 := dualAnn_card hX2 (fixV B)
  rw [hB, ← commV_map_dualRho hX2, hE'map] at h1
  have h2 : Nat.card ↥(commV Bs) = Nat.card ↥(commN E) :=
    card_eq_of_coord θ (S := (commN E : Set (Fin 3 → F'))) (mem_commV_iff_coord hθ hEB hBsK)
  rw [← h1, h2, hcB]
  exact Nat.mul_le_mul_right _ card_commN_rootGroup02_le

end DualNat

section DualOff

variable {F : Type} [Field F] [Finite F] {n : ℕ} {X : Type} [CommGroup X] [Finite X]

theorem natCoord_of_dualOff (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1) (ρ : SL3 F →* MulAut X)
    (hirr : ∀ W : Subgroup X, (∀ g : SL3 F, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ g x, ρ g x ≠ x) {B : Subgroup (SL3 F)} (hB : B ≠ ⊥)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hcard : Nat.card (commV (B.map ρ)) ≤ Nat.card B) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = Nat.card F ∧
      ∃ (σ : SL3 F' ≃* ↥ρ.range) (θ : X ≃* Multiplicative (Fin 3 → F')), IsNatCoord σ θ := by
  set ρs := dualRho ρ with hρs
  have hρs_apply : ∀ g f x, (ρs g f) x = f (ρ g⁻¹ x) := dualRho_apply ρ
  have hirrs : ∀ W : Subgroup (DualGrp X), (∀ g : SL3 F, ∀ w ∈ W, ρs g w ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hinv : ∀ g : SL3 F, ∀ x ∈ dualCoann W, ρ g x ∈ dualCoann W := by
      intro g x hx f hf
      have h1 := hx (ρs g⁻¹ f) (hW g⁻¹ f hf)
      rwa [hρs_apply, inv_inv] at h1
    rcases hirr _ hinv with h | h
    · right
      rw [← dualAnn_dualCoann hX2 W, h, dualAnn_bot]
    · left
      rw [← dualAnn_dualCoann hX2 W, h, dualAnn_top]
  have hnts : ∃ g f, ρs g f ≠ f := by
    obtain ⟨g, x, hx⟩ := hnt
    by_contra hcon
    push Not at hcon
    apply hx
    have h1 : ρs g⁻¹ = 1 := MulEquiv.ext fun f => hcon g⁻¹ f
    have h2 : ρ g⁻¹ = 1 := dualAct_injective hX2 (by rw [map_one]; exact h1)
    have h3 : ρ g = 1 := by rw [map_inv, inv_eq_one] at h2; exact h2
    rw [h3, MulAut.one_apply]
  have hffs : IsFFModule ρs.range := by
    have h1 := D14.isFFModule_dualSub_of_card hX2 (Subgroup.map_le_range ρ B)
      (map_ne_bot ρ hnt hB hB2) (isElemAbelian2_map ρ hB2 hBc)
      (by rw [card_map_eq ρ hnt hB2]; exact hcard)
    rwa [← range_dualRho] at h1
  obtain ⟨F', iF', fF', hFF', σs, θs, hθs⟩ :=
    exists_natCoord ρs h14 hSQ hsq hF dualGrp_sq hirrs hnts hffs
  have : CharP F' 2 := FFC.charP_two_of_card_pow (hFF'.trans hF)
  have hff : IsFFModule ρ.range := isFFModule_of_natCoord_dual hX2 ρ hθs
  exact exists_natCoord ρ h14 hSQ hsq hF hX2 hirr hnt hff

end DualOff

section Coord

variable {F' : Type} [Field F'] [Finite F']

theorem card_mul_card_le_of_ne_top {S : Submodule F' (Fin 3 → F')} (hS : S ≠ ⊤) :
    Nat.card F' * Nat.card S ≤ Nat.card F' ^ 3 := by
  have h1 : Nat.card S = Nat.card F' ^ Module.finrank F' S := Module.natCard_eq_pow_finrank
  have h2 : Module.finrank F' S < 3 := by
    have := Submodule.finrank_lt hS
    rwa [Module.finrank_fin_fun] at this
  rw [h1, ← pow_succ']
  exact Nat.pow_le_pow_right Nat.card_pos (by omega)

omit [Finite F'] in
theorem fixN_ne_top {E : Subgroup (SL3 F')} (hE : E ≠ ⊥) : fixN E ≠ ⊤ := by
  intro h
  apply hE
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  refine eq_one_of_mulVec_eq_self fun x => ?_
  have hx : x ∈ fixN E := by rw [h]; trivial
  exact hx g hg

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)} {σ : SL3 F' ≃* ↥K}
  {θ : V ≃* Multiplicative (Fin 3 → F')}

omit [Finite F'] in
theorem comap_ne_bot {B : Subgroup (MulAut V)} (hBK : B ≤ K) (hB : B ≠ ⊥) :
    (B.subgroupOf K).comap σ.toMonoidHom ≠ ⊥ := by
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
  intro hbot
  have hg : σ.symm ⟨b, hBK hb⟩ ∈ (B.subgroupOf K).comap σ.toMonoidHom := by
    show (σ (σ.symm ⟨b, hBK hb⟩) : MulAut V) ∈ B
    rw [MulEquiv.apply_symm_apply]
    exact hb
  rw [hbot, Subgroup.mem_bot, MulEquiv.symm_apply_eq, map_one] at hg
  have hb' : b = 1 := congrArg Subtype.val hg
  exact hb1 (Subtype.ext hb')

theorem card_mul_card_fixV_le (hθ : IsNatCoord σ θ) {B : Subgroup (MulAut V)} (hBK : B ≤ K)
    (hB : B ≠ ⊥) : Nat.card F' * Nat.card (fixV B) ≤ Nat.card V := by
  set E : Subgroup (SL3 F') := (B.subgroupOf K).comap σ.toMonoidHom with hEdef
  have hE : ∀ g, g ∈ E ↔ (σ g : MulAut V) ∈ B := fun g => Iff.rfl
  have h1 : Nat.card (fixV B) = Nat.card (fixN E) :=
    card_eq_of_coord θ (S := (fixN E : Set (Fin 3 → F'))) (mem_fixV_iff_coord hθ hE hBK)
  rw [h1, card_of_coord θ]
  exact card_mul_card_le_of_ne_top (fixN_ne_top (comap_ne_bot hBK hB))

theorem le_card_commV_of_coord (hθ : IsNatCoord σ θ) {B : Subgroup (MulAut V)} (hBK : B ≤ K)
    (hB : B ≠ ⊥) : Nat.card F' ≤ Nat.card (commV B) := by
  set E : Subgroup (SL3 F') := (B.subgroupOf K).comap σ.toMonoidHom with hEdef
  have hE : ∀ g, g ∈ E ↔ (σ g : MulAut V) ∈ B := fun g => Iff.rfl
  have h1 : Nat.card (commV B) = Nat.card (commN E) :=
    card_eq_of_coord θ (S := (commN E : Set (Fin 3 → F'))) (mem_commV_iff_coord hθ hE hBK)
  rw [h1]
  exact card_le_commN (comap_ne_bot hBK hB)

end Coord

section SecComm

variable {G : Type*} [Group G] {X : Type} [CommGroup X] [Finite X] (ρ : G →* MulAut X)

theorem card_commV_sec_mul_le {W U : Subgroup X} (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) (hUW : U ≤ W) (A : Subgroup G) :
    Nat.card (commV (A.map (secRho ρ hW hU))) * Nat.card ↥(G6.commOn (A.map ρ) W ⊓ U) ≤
      Nat.card (G6.commOn (A.map ρ) W) := by
  rw [map_secRho]
  have h1 := card_secPre hUW (commV (autSec (A.map ρ) W U))
  have h2 : secPre W U (commV (autSec (A.map ρ) W U)) ≤ G6.commOn (A.map ρ) W ⊔ U :=
    secPre_commV_le le_sup_right fun a ha w hw =>
      Subgroup.mem_sup_left (Subgroup.subset_closure ⟨a, ha, w, hw, rfl⟩)
  have h3 := card_sup_mul_card_inf (G6.commOn (A.map ρ) W) U
  have hU0 : 0 < Nat.card U := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hU0
  calc Nat.card (commV (autSec (A.map ρ) W U)) * Nat.card ↥(G6.commOn (A.map ρ) W ⊓ U) *
        Nat.card U
      = (Nat.card (commV (autSec (A.map ρ) W U)) * Nat.card U) *
          Nat.card ↥(G6.commOn (A.map ρ) W ⊓ U) := by ring
    _ ≤ Nat.card ↥(G6.commOn (A.map ρ) W ⊔ U) * Nat.card ↥(G6.commOn (A.map ρ) W ⊓ U) := by
        rw [h1]
        exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le h2)
    _ = Nat.card (G6.commOn (A.map ρ) W) * Nat.card U := h3

omit [Finite X] in
theorem commOn_le_commV (A : Subgroup (MulAut X)) (W : Subgroup X) :
    G6.commOn A W ≤ commV A :=
  Subgroup.closure_mono fun _ ⟨a, ha, w, _, hw⟩ => ⟨a, ha, w, hw⟩

theorem card_commV_sec_le {W U : Subgroup X} (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) (hUW : U ≤ W) (A : Subgroup G) :
    Nat.card (commV (A.map (secRho ρ hW hU))) ≤ Nat.card (commV (A.map ρ)) := by
  have h1 := card_commV_sec_mul_le ρ hW hU hUW A
  have h2 : 0 < Nat.card ↥(G6.commOn (A.map ρ) W ⊓ U) := Nat.card_pos
  have h3 := Subgroup.card_le_of_le (commOn_le_commV (A.map ρ) W)
  calc Nat.card (commV (A.map (secRho ρ hW hU)))
      ≤ Nat.card (commV (A.map (secRho ρ hW hU))) * Nat.card ↥(G6.commOn (A.map ρ) W ⊓ U) :=
        Nat.le_mul_of_pos_right _ h2
    _ ≤ Nat.card (G6.commOn (A.map ρ) W) := h1
    _ ≤ Nat.card (commV (A.map ρ)) := h3

end SecComm

section Lower

variable {F : Type} [Field F] [Finite F] {n : ℕ} {X : Type} [CommGroup X] [Finite X]

omit [Finite F] [Finite X] in
theorem commV_range_ne_bot (ρ : SL3 F →* MulAut X) (hnt : ∃ g x, ρ g x ≠ x) :
    commV ρ.range ≠ ⊥ := by
  obtain ⟨g₀, w₀, hw₀⟩ := hnt
  intro h
  have : ρ g₀ w₀ * w₀⁻¹ ∈ commV ρ.range :=
    Subgroup.subset_closure ⟨ρ g₀, mem_range_apply ρ g₀, w₀, rfl⟩
  rw [h, Subgroup.mem_bot, mul_inv_eq_one] at this
  exact hw₀ this

omit [Finite F] in
theorem exists_irr_sec (ρ : SL3 F →* MulAut X) {R : Subgroup X}
    (hRinv : ∀ g, ∀ u ∈ R, ρ g u ∈ R) (hRY : R ≤ commV ρ.range) (hRne : R ≠ commV ρ.range) :
    ∃ M₀ : Subgroup X, ∃ hM₀inv : (∀ g, ∀ u ∈ M₀, ρ g u ∈ M₀), R ≤ M₀ ∧ M₀ ≤ commV ρ.range ∧
      (∀ J' : Subgroup (Sec (commV ρ.range) M₀),
        (∀ g, ∀ s ∈ J', secRho ρ (fun g _ hx => commV_inv ρ g hx) hM₀inv g s ∈ J') →
        J' = ⊥ ∨ J' = ⊤) ∧
      ∃ g s, secRho ρ (fun g _ hx => commV_inv ρ g hx) hM₀inv g s ≠ s := by
  have : Group.IsPerfect (SL3 F) := isPerfect_SL3
  have hYinv : ∀ g, ∀ x ∈ commV ρ.range, ρ g x ∈ commV ρ.range := fun g x hx => commV_inv ρ g hx
  obtain ⟨M₀, hM₀inv, hRM₀, hM₀Y, hM₀ne, hM₀max⟩ := exists_maximal_inv ρ hRinv hRY hRne
  obtain ⟨g₁, x₁, hx₁, hg₁⟩ : ∃ g, ∃ x ∈ commV ρ.range, ρ g x * x⁻¹ ∉ M₀ := by
    by_contra h
    push Not at h
    exact hM₀ne (le_antisymm hM₀Y (commV_le_of_isPerfect ρ fun g x hx => h g x hx))
  exact ⟨M₀, hM₀inv, hRM₀, hM₀Y, sec_irr ρ hYinv hM₀inv hM₀Y hM₀max,
    sec_nt ρ hYinv hM₀inv hx₁ hg₁⟩

theorem le_card_commV (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1) (ρ : SL3 F →* MulAut X)
    (hnt : ∃ g x, ρ g x ≠ x) {B : Subgroup (SL3 F)} (hB : B ≠ ⊥)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hcard : Nat.card (commV (B.map ρ)) ≤ Nat.card B) :
    Nat.card F ≤ Nat.card (commV (B.map ρ)) := by
  have hYinv : ∀ g, ∀ x ∈ commV ρ.range, ρ g x ∈ commV ρ.range := fun g x hx => commV_inv ρ g hx
  obtain ⟨M₀, hM₀inv, -, hM₀Y, hirrS, hntS⟩ := exists_irr_sec ρ (R := ⊥)
    (fun g u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]) bot_le
    (commV_range_ne_bot ρ hnt).symm
  have hcomm := card_commV_sec_le ρ hYinv hM₀inv hM₀Y B
  obtain ⟨F', iF', fF', hFF', σ, θ, hθ⟩ := natCoord_of_dualOff h14 hSQ hsq hF (sec_sq hX2)
    (secRho ρ hYinv hM₀inv) hirrS hntS hB hB2 hBc (hcomm.trans hcard)
  have h1 := le_card_commV_of_coord hθ (Subgroup.map_le_range _ B)
    (map_ne_bot (secRho ρ hYinv hM₀inv) hntS hB hB2)
  rw [hFF'] at h1
  exact h1.trans hcomm

end Lower

section Cocycle

variable {F : Type} [Field F] [Finite F] {X : Type} [CommGroup X] [Finite X]

omit [Finite F] [Finite X] in
theorem exists_fix_of_cocycle {F' : Type} [Field F'] [Finite F'] [CharP F' 2]
    (ρ : SL3 F →* MulAut X) {Y M₀ : Subgroup X} (hY : ∀ g, ∀ u ∈ Y, ρ g u ∈ Y)
    (hM₀ : ∀ g, ∀ m ∈ M₀, ρ g m = m)
    (τ : SL3 F →* SL3 F') (hτ : Function.Surjective τ) (hτc : ∀ k, τ k = 1 → k ^ 3 = 1)
    (π : ↥Y →* Multiplicative (Fin 3 → F')) (hπs : Function.Surjective π)
    (hπk : ∀ u : ↥Y, π u = 1 → (u : X) ∈ M₀)
    (hπe : ∀ g (u : ↥Y), π (resRho ρ Y hY g u) =
      Multiplicative.ofAdd ((τ g : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (π u)))
    {Y₀ : Subgroup (SL3 F)} (hY₀2 : IsPGroup 2 Y₀) (hY₀τ : Y₀.map τ ≠ ⊥)
    {y : X} (hy : ∀ g, ρ g y * y⁻¹ ∈ Y) (hyY₀ : ∀ t ∈ Y₀, ρ t y = y) :
    ∃ u ∈ Y, y * u⁻¹ ∈ fixV ρ.range := by
  set c : SL3 F → ↥Y := fun g => ⟨ρ g y * y⁻¹, hy g⟩ with hc
  set f : SL3 F → (Fin 3 → F') := fun g => Multiplicative.toAdd (π (c g)) with hf
  have hcmul : ∀ g h, c (g * h) = resRho ρ Y hY g (c h) * c g := by
    intro g h
    apply Subtype.ext
    simp only [hc, Subgroup.coe_mul, coe_resRho_apply, map_mul, MulAut.mul_apply, map_inv]
    group
  have hcoc : ∀ a ∈ (⊤ : Subgroup (SL3 F)), ∀ b ∈ (⊤ : Subgroup (SL3 F)),
      f (a * b) = f a + ((τ a : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ f b := by
    intro a _ b _
    simp only [hf, hcmul, map_mul, hπe, toAdd_mul, toAdd_ofAdd]
    exact add_comm _ _
  have hfY : ∀ t ∈ Y₀, f t = 0 := by
    intro t ht
    have h1 : c t = 1 := Subtype.ext (by simp [hc, hyY₀ t ht])
    simp [hf, h1]
  have hP : ∀ k ∈ (⊤ : Subgroup (SL3 F)), τ k = 1 → ∃ b : ℕ, Odd b ∧ k ^ b ∈ (⊥ : Subgroup _) :=
    fun k _ hk => ⟨3, by decide, by rw [Subgroup.mem_bot]; exact hτc k hk⟩
  obtain ⟨n, hn⟩ := exists_coboundary_of_cocycle hcoc le_top hfY (fun g => ⟨_, trivial,
    (hτ g).choose_spec⟩) hP bot_le hY₀τ hY₀2
  obtain ⟨u₀, hu₀⟩ := hπs (Multiplicative.ofAdd n)
  refine ⟨u₀, u₀.2, ?_⟩
  set w : X := y * (u₀ : X)⁻¹ with hw
  clear_value w
  have hwM : ∀ g, ρ g w * w⁻¹ ∈ M₀ := by
    intro g
    have h1 : π (c g * (resRho ρ Y hY g u₀ * u₀⁻¹)⁻¹) = 1 := by
      rw [map_mul π, map_inv π, map_mul π, map_inv π, hπe, hu₀]
      apply Multiplicative.toAdd.injective
      have := hn g trivial
      simp only [hf] at this
      simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_one, this]
      abel
    have h2 := hπk _ h1
    have e : ((c g * (resRho ρ Y hY g u₀ * u₀⁻¹)⁻¹ : ↥Y) : X) = ρ g w * w⁻¹ := by
      simp only [hc, hw, Subgroup.coe_mul, Subgroup.coe_inv, coe_resRho_apply, map_mul, map_inv,
        mul_inv_rev, inv_inv]
      simp only [mul_comm, mul_left_comm, mul_assoc]
    rwa [e] at h2
  have : Group.IsPerfect (SL3 F) := isPerfect_SL3
  have hfix := fix_of_two_step ρ (L := ⊤) Group.IsPerfect.commutator_eq_top (U₁ := M₀)
    (U₂ := Subgroup.zpowers w) (fun l _ m hm => hM₀ l m hm) (by
      rintro l - _ ⟨k, rfl⟩
      have e : ρ l (w ^ k) * (w ^ k)⁻¹ = (ρ l w * w⁻¹) ^ k := by
        rw [map_zpow, mul_zpow, inv_zpow]
      rw [e]
      exact M₀.zpow_mem (hwM l) k)
  rintro _ ⟨g, rfl⟩
  exact hfix g trivial w (Subgroup.mem_zpowers w)

end Cocycle

section Split

variable {F : Type} [Field F] [Finite F] {n : ℕ} {X : Type} [CommGroup X] [Finite X]

omit [Finite F] in
theorem isPGroup_of_sq {B : Subgroup (SL3 F)} (hB2 : ∀ b ∈ B, b ^ 2 = 1) : IsPGroup 2 B :=
  fun b => ⟨1, Subtype.ext (by simpa using hB2 b b.2)⟩

theorem ffSplit (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1) (ρ : SL3 F →* MulAut X)
    {B : Subgroup (SL3 F)} (hB : B ≠ ⊥)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hqB : Nat.card F ≤ Nat.card B)
    (hidx : Nat.card X ≤ Nat.card F * Nat.card (fixV (B.map ρ))) :
    commV ρ.range ⊔ fixV ρ.range = ⊤ := by
  by_cases hnt : ∃ g x, ρ g x ≠ x
  swap
  · push Not at hnt
    rw [eq_top_iff]
    intro x _
    refine Subgroup.mem_sup_right ?_
    rintro _ ⟨g, rfl⟩
    exact hnt g x
  have : CharP F 2 := FFC.charP_two_of_card_pow hF
  set Y := commV ρ.range with hYdef
  have hYinv : ∀ g, ∀ x ∈ Y, ρ g x ∈ Y := fun g x hx => commV_inv ρ g hx
  obtain ⟨M₀, hM₀inv, -, hM₀Y, hirrS, hntS⟩ := exists_irr_sec ρ (R := ⊥)
    (fun g u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]) bot_le
    (commV_range_ne_bot ρ hnt).symm
  set ρS := secRho ρ hYinv hM₀inv with hρS
  set A : Subgroup (MulAut X) := B.map ρ with hA
  have hAK : A ≤ ρ.range := Subgroup.map_le_range ρ B
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB2 b hb, map_one]
  have hfaith := inf_centSec_eq_bot ρ hYinv hM₀inv hntS hAK hA2
  have hcardX : Nat.card X ≤ Nat.card A * Nat.card (fixV A) := by
    rw [hA, card_map_eq ρ hnt hB2]
    exact hidx.trans (Nat.mul_le_mul_right _ hqB)
  have hffS := sec_ff ρ hYinv hM₀inv hM₀Y hAK (map_ne_bot ρ hnt hB hB2)
    (isElemAbelian2_map ρ hB2 hBc) hcardX hfaith
  obtain ⟨F', iF', fF', hFF', σ, θ, hθ⟩ :=
    exists_natCoord ρS h14 hSQ hsq hF (sec_sq hX2) hirrS hntS hffS
  have : CharP F' 2 := FFC.charP_two_of_card_pow (hFF'.trans hF)
  have hb := card_mul_card_fixV_le hθ (Subgroup.map_le_range ρS B)
    (map_ne_bot ρS hntS hB hB2)
  rw [hFF', hρS, map_secRho] at hb
  have hAY : A ≤ stabSub Y := hAK.trans (range_le_stabSub ρ hYinv)
  have hd := card_inf_fixV_le_autSec hM₀Y hAY (U := M₀)
  have hcs := card_sec_mul hM₀Y
  have he := card_sup_mul_card_inf Y (fixV A)
  have hfu : Nat.card ↥(Y ⊔ fixV A) ≤ Nat.card X := Subgroup.card_le_card_group _
  have hmc : Nat.card ↥(M₀ ⊓ fixV A) ≤ Nat.card M₀ := Subgroup.card_le_of_le inf_le_left
  have hc0 : 0 < Nat.card (fixV A) := Nat.card_pos
  have hcs0 : 0 < Nat.card (fixV (autSec A Y M₀)) := Nat.card_pos
  have hq0 : 0 < Nat.card F := Nat.card_pos
  have hi0 : 0 < Nat.card ↥(Y ⊓ fixV A) := Nat.card_pos
  have h1 : Nat.card Y ≤ Nat.card F * Nat.card (fixV (autSec A Y M₀)) *
      Nat.card ↥(M₀ ⊓ fixV A) := by
    refine Nat.le_of_mul_le_mul_right ?_ hc0
    calc Nat.card Y * Nat.card (fixV A) = Nat.card ↥(Y ⊔ fixV A) * Nat.card ↥(Y ⊓ fixV A) :=
          he.symm
      _ ≤ (Nat.card F * Nat.card (fixV A)) *
            (Nat.card (fixV (autSec A Y M₀)) * Nat.card ↥(M₀ ⊓ fixV A)) :=
          Nat.mul_le_mul (hfu.trans hidx) hd
      _ = Nat.card F * Nat.card (fixV (autSec A Y M₀)) * Nat.card ↥(M₀ ⊓ fixV A) *
            Nat.card (fixV A) := by ring
  have h2 : Nat.card F * Nat.card (fixV (autSec A Y M₀)) * Nat.card M₀ ≤ Nat.card Y := by
    rw [← hcs]
    exact Nat.mul_le_mul_right _ hb
  have hpos : 0 < Nat.card F * Nat.card (fixV (autSec A Y M₀)) := Nat.mul_pos hq0 hcs0
  have hmm : Nat.card M₀ ≤ Nat.card ↥(M₀ ⊓ fixV A) :=
    Nat.le_of_mul_le_mul_left (h2.trans h1) hpos
  have hM₀A : M₀ ≤ fixV A := by
    have := Subgroup.eq_of_le_of_card_ge (inf_le_left : M₀ ⊓ fixV A ≤ M₀) hmm
    rw [← this]
    exact inf_le_right
  have hM₀fix : ∀ g, ∀ m ∈ M₀, ρ g m = m :=
    fix_of_fix ρ hM₀inv hB hB2 fun b hb m hm => hM₀A hm (ρ b) ⟨b, hb, rfl⟩
  have hYC : Y ⊔ fixV A = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    refine le_antisymm hfu ?_
    refine Nat.le_of_mul_le_mul_right ?_ hi0
    calc Nat.card X * Nat.card ↥(Y ⊓ fixV A)
        ≤ (Nat.card F * Nat.card (fixV A)) *
            (Nat.card (fixV (autSec A Y M₀)) * Nat.card ↥(M₀ ⊓ fixV A)) :=
          Nat.mul_le_mul hidx hd
      _ = Nat.card F * Nat.card (fixV (autSec A Y M₀)) * Nat.card ↥(M₀ ⊓ fixV A) *
            Nat.card (fixV A) := by ring
      _ ≤ Nat.card F * Nat.card (fixV (autSec A Y M₀)) * Nat.card M₀ * Nat.card (fixV A) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hmc)
      _ ≤ Nat.card Y * Nat.card (fixV A) := Nat.mul_le_mul_right _ h2
      _ = Nat.card ↥(Y ⊔ fixV A) * Nat.card ↥(Y ⊓ fixV A) := he.symm
  set τ : SL3 F →* SL3 F' := σ.symm.toMonoidHom.comp ρS.rangeRestrict with hτ
  have hτs : Function.Surjective τ :=
    σ.symm.surjective.comp ρS.rangeRestrict_surjective
  have hστ : ∀ g, (σ (τ g) : MulAut (Sec Y M₀)) = ρS g := by
    intro g
    simp [hτ]
  have hτc : ∀ k, τ k = 1 → k ^ 3 = 1 := by
    intro k hk
    have h1 : ρS k = 1 := by rw [← hστ k, hk, map_one]; rfl
    exact pow_three_eq_one_of_mem_center (ker_le_center ρS hntS (MonoidHom.mem_ker.mpr h1))
  have hBτ : B.map τ ≠ ⊥ := by
    intro hbot
    apply hB
    rw [← inf_eq_left.mpr (show B ≤ ρS.ker from fun b hb => by
      have h1 : τ b = 1 := by
        have : τ b ∈ B.map τ := ⟨b, hb, rfl⟩
        rwa [hbot, Subgroup.mem_bot] at this
      rw [MonoidHom.mem_ker, ← hστ b, h1, map_one]
      rfl)]
    exact inf_ker_eq_bot ρS hntS hB2
  set π : ↥Y →* Multiplicative (Fin 3 → F') :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (M₀.subgroupOf Y)) with hπ
  have hπs : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : ∀ u : ↥Y, π u = 1 → (u : X) ∈ M₀ := by
    intro u hu
    have h1 : (QuotientGroup.mk' (M₀.subgroupOf Y) u) = 1 := θ.injective (by rw [map_one]; exact hu)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  have hπe : ∀ g (u : ↥Y), π (resRho ρ Y hYinv g u) =
      Multiplicative.ofAdd ((τ g : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (π u)) := by
    intro g u
    have h1 : QuotientGroup.mk' (M₀.subgroupOf Y) (resRho ρ Y hYinv g u) =
        (σ (τ g) : MulAut (Sec Y M₀)) (QuotientGroup.mk' (M₀.subgroupOf Y) u) := by
      rw [hστ]
      rfl
    simp only [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [h1, hθ]
  have hfixY : ∀ y ∈ fixV A, y ∈ Y ⊔ fixV ρ.range := by
    intro y hy
    obtain ⟨u, huY, hu⟩ := exists_fix_of_cocycle ρ hYinv hM₀fix τ hτs hτc π hπs hπk hπe
      (isPGroup_of_sq hB2) hBτ (y := y) (fun g => Subgroup.subset_closure
        ⟨ρ g, mem_range_apply ρ g, y, rfl⟩) fun t ht => hy (ρ t) ⟨t, ht, rfl⟩
    have e : y = (y * u⁻¹) * u := by group
    rw [e, mul_comm]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left huY) (Subgroup.mem_sup_right hu)
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Y ⊔ fixV A := by rw [hYC]; trivial
  obtain ⟨y₁, hy₁, c₁, hc₁, rfl⟩ := Subgroup.mem_sup.mp hx
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy₁) (hfixY c₁ hc₁)

end Split

section Decomp

variable {F : Type} [Field F] [Finite F] {n : ℕ} {X : Type} [CommGroup X] [Finite X]

omit [Finite F] [Finite X] in
theorem zpowers_sq_eq_one {G : Type*} [Group G] {t : G} (ht2 : t ^ 2 = 1) :
    ∀ s ∈ Subgroup.zpowers t, s ^ 2 = 1 := by
  rintro _ ⟨k, rfl⟩
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]

theorem dualOff_decomp (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1) (ρ : SL3 F →* MulAut X)
    (hnt : ∃ g x, ρ g x ≠ x) {B : Subgroup (SL3 F)} (hB : B ≠ ⊥)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hqB : Nat.card F ≤ Nat.card B) (hcomm : Nat.card (commV (B.map ρ)) ≤ Nat.card F) :
    commV ρ.range ⊓ fixV ρ.range = ⊥ ∧ commV ρ.range ⊔ fixV ρ.range = ⊤ ∧
      ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = Nat.card F ∧
        ∃ (τ : SL3 F →* SL3 F') (θ : ↥(commV ρ.range) ≃* Multiplicative (Fin 3 → F')),
          Function.Surjective τ ∧ ∀ g (p : ↥(commV ρ.range)),
            θ (resRho ρ (commV ρ.range) (fun g _ hx => commV_inv ρ g hx) g p) =
              Multiplicative.ofAdd ((τ g : Matrix (Fin 3) (Fin 3) F') *ᵥ
                Multiplicative.toAdd (θ p)) := by
  have : Group.IsPerfect (SL3 F) := isPerfect_SL3
  have : CharP F 2 := FFC.charP_two_of_card_pow hF
  set P := commV ρ.range with hPdef
  set C := fixV ρ.range with hCdef
  have hPinv : ∀ g, ∀ x ∈ P, ρ g x ∈ P := fun g _ hx => commV_inv ρ g hx
  have hPC : P ⊓ C = ⊥ := by
    have hidx : Nat.card (DualGrp X) ≤ Nat.card F * Nat.card (fixV (B.map (dualRho ρ))) := by
      rw [fixV_map_dualRho, card_dualGrp hX2, ← dualAnn_card hX2 (commV (B.map ρ)), mul_comm]
      exact Nat.mul_le_mul_right _ hcomm
    have hsplit := ffSplit h14 hSQ hsq hF dualGrp_sq (dualRho ρ) hB hB2 hBc hqB hidx
    rw [commV_range_dualRho hX2, fixV_range_dualRho] at hsplit
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    obtain ⟨f, hf⟩ := exists_dualChar_ne_one hX2 hx1
    have hf' : f ∈ dualAnn C ⊔ dualAnn P := by rw [hsplit]; trivial
    obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := Subgroup.mem_sup.mp hf'
    apply hf
    change f₁ x * f₂ x = 1
    rw [hf₁ x hx.2, hf₂ x hx.1, mul_one]
  have hirrP : ∀ J : Subgroup X, (∀ g, ∀ u ∈ J, ρ g u ∈ J) → J ≤ P → J = ⊥ ∨ J = P := by
    intro J hJ hJP
    by_cases hJe : J = P
    · exact Or.inr hJe
    left
    obtain ⟨M₀, hM₀inv, hJM₀, hM₀P, -, hntS⟩ := exists_irr_sec ρ hJ hJP hJe
    have hcS := card_commV_sec_le ρ hPinv hM₀inv hM₀P B
    have hlow := le_card_commV h14 hSQ hsq hF (sec_sq hX2) (secRho ρ hPinv hM₀inv) hntS hB hB2
      hBc (hcS.trans (hcomm.trans hqB))
    have hmul := card_commV_sec_mul_le ρ hPinv hM₀inv hM₀P B
    have hle := Subgroup.card_le_of_le (commOn_le_commV (B.map ρ) P)
    have h1 : Nat.card ↥(G6.commOn (B.map ρ) P ⊓ M₀) ≤ 1 := by
      have hq0 : 0 < Nat.card F := Nat.card_pos
      refine Nat.le_of_mul_le_mul_left ?_ hq0
      calc Nat.card F * Nat.card ↥(G6.commOn (B.map ρ) P ⊓ M₀)
          ≤ Nat.card (commV (B.map (secRho ρ hPinv hM₀inv))) *
              Nat.card ↥(G6.commOn (B.map ρ) P ⊓ M₀) := Nat.mul_le_mul_right _ hlow
        _ ≤ Nat.card (G6.commOn (B.map ρ) P) := hmul
        _ ≤ Nat.card F * 1 := by rw [mul_one]; exact hle.trans hcomm
    have h2 : G6.commOn (B.map ρ) P ⊓ M₀ = ⊥ := Subgroup.eq_bot_of_card_le _ h1
    have hBM : ∀ b ∈ B, ∀ m ∈ M₀, ρ b m = m := by
      intro b hb m hm
      have h3 : ρ b m * m⁻¹ ∈ G6.commOn (B.map ρ) P ⊓ M₀ :=
        ⟨Subgroup.subset_closure ⟨ρ b, ⟨b, hb, rfl⟩, m, hM₀P hm, rfl⟩,
          M₀.mul_mem (hM₀inv b m hm) (M₀.inv_mem hm)⟩
      rw [h2, Subgroup.mem_bot, mul_inv_eq_one] at h3
      exact h3
    have hM₀fix := fix_of_fix ρ hM₀inv hB hB2 hBM
    have hM₀C : M₀ ≤ P ⊓ C := fun m hm => ⟨hM₀P hm, by rintro _ ⟨g, rfl⟩; exact hM₀fix g m hm⟩
    rw [hPC] at hM₀C
    exact eq_bot_iff.mpr (hJM₀.trans hM₀C)
  set ρP := resRho ρ P hPinv with hρP
  have hirrP' : ∀ W : Subgroup ↥P, (∀ g : SL3 F, ∀ w ∈ W, ρP g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hinv : ∀ g, ∀ u ∈ W.map P.subtype, ρ g u ∈ W.map P.subtype := by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨ρP g w, hW g w hw, rfl⟩
    rcases hirrP _ hinv (Subgroup.map_subtype_le W) with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).mp h
    · right
      rw [eq_top_iff]
      intro w _
      have hw : (w : X) ∈ W.map P.subtype := by rw [h]; exact w.2
      obtain ⟨w', hw', he⟩ := hw
      rwa [← Subtype.ext he]
  have hntP : ∃ g p, ρP g p ≠ p := by
    by_contra hcon
    push Not at hcon
    apply commV_range_ne_bot ρ hnt
    rw [eq_bot_iff]
    refine commV_le_of_isPerfect ρ fun g x hx => ?_
    have h1 := congrArg Subtype.val (hcon g ⟨x, hx⟩)
    rw [coe_resRho_apply] at h1
    rw [Subgroup.mem_bot, h1, mul_inv_cancel]
  have hcommP : Nat.card (commV (B.map ρP)) ≤ Nat.card (commV (B.map ρ)) := by
    have hle : (commV (B.map ρP)).map P.subtype ≤ commV (B.map ρ) := by
      rw [Subgroup.map_le_iff_le_comap, commV, Subgroup.closure_le]
      rintro _ ⟨_, ⟨b, hb, rfl⟩, p, rfl⟩
      exact Subgroup.subset_closure ⟨ρ b, ⟨b, hb, rfl⟩, p, rfl⟩
    rw [← Subgroup.card_map_of_injective P.subtype_injective]
    exact Subgroup.card_le_of_le hle
  have hP2 : ∀ p : ↥P, p ^ 2 = 1 := fun p => Subtype.ext (by
    rw [Subgroup.coe_pow, hX2, Subgroup.coe_one])
  obtain ⟨F', iF', fF', hFF', σ, θ, hθ⟩ := natCoord_of_dualOff h14 hSQ hsq hF hP2 ρP hirrP'
    hntP hB hB2 hBc (hcommP.trans (hcomm.trans hqB))
  have : CharP F' 2 := FFC.charP_two_of_card_pow (hFF'.trans hF)
  set τ : SL3 F →* SL3 F' := σ.symm.toMonoidHom.comp ρP.rangeRestrict with hτ
  have hτs : Function.Surjective τ := σ.symm.surjective.comp ρP.rangeRestrict_surjective
  have hστ : ∀ g, (σ (τ g) : MulAut ↥P) = ρP g := by
    intro g
    simp [hτ]
  have hτe : ∀ g (p : ↥P), θ (ρP g p) =
      Multiplicative.ofAdd ((τ g : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (θ p)) := by
    intro g p
    rw [← hστ g, hθ]
  have hτc : ∀ k, τ k = 1 → k ^ 3 = 1 := by
    intro k hk
    have h1 : ρP k = 1 := by rw [← hστ k, hk, map_one]; rfl
    exact pow_three_eq_one_of_mem_center (ker_le_center ρP hntP (MonoidHom.mem_ker.mpr h1))
  refine ⟨hPC, ?_, F', iF', fF', hFF', τ, θ, hτs, hτe⟩
  obtain ⟨⟨t, htB⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht2 : t ^ 2 = 1 := hB2 t htB
  have hτt : τ t ≠ 1 := by
    intro h
    apply ht1'
    have h3 := hτc t h
    calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, ht2, inv_one, one_mul]
  set δ : ↥P →* ↥P :=
    { toFun := fun p => ρP t p * p⁻¹
      map_one' := by simp
      map_mul' := fun p p' => by
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ } with hδ
  set ℓ : (Fin 3 → F') →ₗ[F'] (Fin 3 → F') :=
    Matrix.mulVecLin ((τ t : SL3 F') : Matrix (Fin 3) (Fin 3) F') - LinearMap.id with hℓ
  have hℓne : LinearMap.range ℓ ≠ ⊥ := by
    intro hbot
    apply hτt
    refine eq_one_of_mulVec_eq_self fun x => ?_
    have h1 : ℓ x ∈ LinearMap.range ℓ := LinearMap.mem_range_self ℓ x
    rw [hbot, Submodule.mem_bot, hℓ, LinearMap.sub_apply, Matrix.mulVecLin_apply,
      LinearMap.id_apply, sub_eq_zero] at h1
    exact h1
  have hTθ : ∀ v : ↥P, v ∈ δ.range ↔
      Multiplicative.toAdd (θ v) ∈ (LinearMap.range ℓ : Set (Fin 3 → F')) := by
    intro v
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨Multiplicative.toAdd (θ p), ?_⟩
      rw [hℓ, LinearMap.sub_apply, Matrix.mulVecLin_apply, LinearMap.id_apply]
      show _ = Multiplicative.toAdd (θ (ρP t p * p⁻¹))
      rw [map_mul, map_inv, hτe, toAdd_mul, toAdd_inv, toAdd_ofAdd, sub_eq_add_neg]
    · rintro ⟨x, hx⟩
      refine ⟨θ.symm (Multiplicative.ofAdd x), θ.injective ?_⟩
      show θ (ρP t (θ.symm (Multiplicative.ofAdd x)) * (θ.symm (Multiplicative.ofAdd x))⁻¹) = θ v
      rw [map_mul, map_inv, hτe, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, ← hx, hℓ, LinearMap.sub_apply,
        Matrix.mulVecLin_apply, LinearMap.id_apply, sub_eq_add_neg]
  have hTcard : Nat.card F ≤ Nat.card δ.range := by
    rw [card_eq_of_coord θ hTθ, ← hFF']
    exact card_le_of_ne_bot hℓne
  have hTle : δ.range.map P.subtype ≤ commV (B.map ρ) := by
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨ρ t, ⟨t, htB, rfl⟩, p, rfl⟩
  have hTeq : δ.range.map P.subtype = commV (B.map ρ) := by
    refine Subgroup.eq_of_le_of_card_ge hTle ?_
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact hcomm.trans hTcard
  have hzt2 := zpowers_sq_eq_one ht2
  have hztτ : (Subgroup.zpowers t).map τ ≠ ⊥ := by
    intro hbot
    apply hτt
    have : τ t ∈ (Subgroup.zpowers t).map τ := ⟨t, Subgroup.mem_zpowers t, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  rw [eq_top_iff]
  intro x _
  have hx : ρ t x * x⁻¹ ∈ δ.range.map P.subtype := by
    rw [hTeq]
    exact Subgroup.subset_closure ⟨ρ t, ⟨t, htB, rfl⟩, x, rfl⟩
  obtain ⟨_, ⟨p, rfl⟩, hpx⟩ := hx
  set w : X := x * (p : X)⁻¹ with hw
  have hpx' : ρ t p * (p : X)⁻¹ = ρ t x * x⁻¹ := hpx
  have hwt : ρ t w = w := by
    rw [hw, map_mul, map_inv]
    have e : ρ t x = (ρ t p * (p : X)⁻¹) * x := by rw [hpx', inv_mul_cancel_right]
    rw [e]
    simp only [mul_comm, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨u, huP, hu⟩ := exists_fix_of_cocycle ρ hPinv (M₀ := ⊥)
    (fun _ m hm => by rw [Subgroup.mem_bot.mp hm, map_one]) τ hτs hτc θ.toMonoidHom θ.surjective
    (fun u hu => by
      rw [Subgroup.mem_bot]
      have : u = 1 := θ.injective (by rw [map_one]; exact hu)
      rw [this, Subgroup.coe_one]) hτe (isPGroup_of_sq hzt2) hztτ (y := w)
    (fun g => Subgroup.subset_closure ⟨ρ g, mem_range_apply ρ g, w, rfl⟩) (by
      rintro _ ⟨k, rfl⟩
      rw [map_zpow]
      have hst : ρ t ∈ MulAction.stabilizer (MulAut X) w := hwt
      exact (Subgroup.zpowers_le.mpr hst) ⟨k, rfl⟩)
  have e : x = (w * u⁻¹) * (u * p) := by rw [hw]; group
  rw [e, mul_comm]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (P.mul_mem huP p.2)) (Subgroup.mem_sup_right hu)

end Decomp

section FFDecomp

variable {F : Type} [Field F] [Finite F] {n : ℕ} {X : Type} [CommGroup X] [Finite X]

@[expose] def IsNatDecomp (ρ : SL3 F →* MulAut X) : Prop :=
  commV ρ.range ⊓ fixV ρ.range = ⊥ ∧ commV ρ.range ⊔ fixV ρ.range = ⊤ ∧
    ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = Nat.card F ∧
      ∃ (τ : SL3 F →* SL3 F') (θ : ↥(commV ρ.range) ≃* Multiplicative (Fin 3 → F')),
        Function.Surjective τ ∧ ∀ g (p : ↥(commV ρ.range)),
          θ (resRho ρ (commV ρ.range) (fun g _ hx => commV_inv ρ g hx) g p) =
            Multiplicative.ofAdd ((τ g : Matrix (Fin 3) (Fin 3) F') *ᵥ
              Multiplicative.toAdd (θ p))

omit [Finite X] in
theorem irr_resRho {G : Type*} [Group G] (ρ : G →* MulAut X) {P : Subgroup X}
    (hPinv : ∀ g, ∀ x ∈ P, ρ g x ∈ P)
    (hirr : ∀ J : Subgroup X, (∀ g, ∀ u ∈ J, ρ g u ∈ J) → J ≤ P → J = ⊥ ∨ J = P) :
    ∀ W : Subgroup ↥P, (∀ g, ∀ w ∈ W, resRho ρ P hPinv g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hinv : ∀ g, ∀ u ∈ W.map P.subtype, ρ g u ∈ W.map P.subtype := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨resRho ρ P hPinv g w, hW g w hw, rfl⟩
  rcases hirr _ hinv (Subgroup.map_subtype_le W) with h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).mp h
  · right
    rw [eq_top_iff]
    intro w _
    have hw : (w : X) ∈ W.map P.subtype := by rw [h]; exact w.2
    obtain ⟨w', hw', he⟩ := hw
    rwa [← Subtype.ext he]

omit [Finite F] [Finite X] in
theorem resRho_nt (ρ : SL3 F →* MulAut X) (hnt : ∃ g x, ρ g x ≠ x) :
    ∃ g p, resRho ρ (commV ρ.range) (fun g _ hx => commV_inv ρ g hx) g p ≠ p := by
  have : Group.IsPerfect (SL3 F) := isPerfect_SL3
  by_contra hcon
  push Not at hcon
  apply commV_range_ne_bot ρ hnt
  rw [eq_bot_iff]
  refine commV_le_of_isPerfect ρ fun g x hx => ?_
  have h1 := congrArg Subtype.val (hcon g ⟨x, hx⟩)
  rw [coe_resRho_apply] at h1
  rw [Subgroup.mem_bot, h1, mul_inv_cancel]

theorem card_le_mul_inf_fixV (A : Subgroup (MulAut X)) (W : Subgroup X) {q : ℕ}
    (h : Nat.card X ≤ q * Nat.card (fixV A)) : Nat.card W ≤ q * Nat.card ↥(W ⊓ fixV A) := by
  have h1 := card_sup_mul_card_inf W (fixV A)
  have h2 : Nat.card ↥(W ⊔ fixV A) ≤ Nat.card X := Subgroup.card_le_card_group _
  have hc : 0 < Nat.card (fixV A) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hc
  calc Nat.card W * Nat.card (fixV A) = Nat.card ↥(W ⊔ fixV A) * Nat.card ↥(W ⊓ fixV A) :=
        h1.symm
    _ ≤ (q * Nat.card (fixV A)) * Nat.card ↥(W ⊓ fixV A) := Nat.mul_le_mul_right _ (h2.trans h)
    _ = q * Nat.card ↥(W ⊓ fixV A) * Nat.card (fixV A) := by ring

theorem card_mul_inf_fixV_mono {N K : Subgroup X} (hNK : N ≤ K) (C : Subgroup X) {q : ℕ}
    (h : q * Nat.card ↥(N ⊓ C) ≤ Nat.card N) : q * Nat.card ↥(K ⊓ C) ≤ Nat.card K := by
  have h1 := card_sup_mul_card_inf N (K ⊓ C)
  have h2 : Nat.card ↥(N ⊔ K ⊓ C) ≤ Nat.card K := Subgroup.card_le_of_le (sup_le hNK inf_le_left)
  have h3 : N ⊓ (K ⊓ C) = N ⊓ C := by rw [← inf_assoc, inf_eq_left.mpr hNK]
  rw [h3] at h1
  have hN : 0 < Nat.card N := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hN
  calc q * Nat.card ↥(K ⊓ C) * Nat.card N = q * (Nat.card N * Nat.card ↥(K ⊓ C)) := by ring
    _ = q * (Nat.card ↥(N ⊔ K ⊓ C) * Nat.card ↥(N ⊓ C)) := by rw [← h1]
    _ = Nat.card ↥(N ⊔ K ⊓ C) * (q * Nat.card ↥(N ⊓ C)) := by ring
    _ ≤ Nat.card K * Nat.card N := Nat.mul_le_mul h2 h

theorem card_mul_inf_fixV_le_of_sec {G : Type*} [Group G] (ρ : G →* MulAut X)
    {W U : Subgroup X} (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U)
    (hUW : U ≤ W) (A : Subgroup G) {q : ℕ}
    (h : q * Nat.card (fixV (A.map (secRho ρ hW hU))) ≤ Nat.card (Sec W U)) :
    q * Nat.card ↥(W ⊓ fixV (A.map ρ)) ≤ Nat.card W := by
  rw [map_secRho] at h
  have hAW : A.map ρ ≤ stabSub W := (Subgroup.map_le_range ρ A).trans (range_le_stabSub ρ hW)
  have h1 := card_inf_fixV_le_autSec hUW hAW (U := U)
  have h2 : Nat.card ↥(U ⊓ fixV (A.map ρ)) ≤ Nat.card U := Subgroup.card_le_of_le inf_le_left
  have h3 := card_sec_mul hUW
  calc q * Nat.card ↥(W ⊓ fixV (A.map ρ))
      ≤ q * (Nat.card (fixV (autSec (A.map ρ) W U)) * Nat.card U) :=
        Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left _ h2))
    _ = (q * Nat.card (fixV (autSec (A.map ρ) W U))) * Nat.card U := by ring
    _ ≤ Nat.card (Sec W U) * Nat.card U := Nat.mul_le_mul_right _ h
    _ = Nat.card W := h3

theorem le_index_fixV (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1) (ρ : SL3 F →* MulAut X)
    (hnt : ∃ g x, ρ g x ≠ x) {B : Subgroup (SL3 F)} (hB : B ≠ ⊥)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hcard : Nat.card X ≤ Nat.card B * Nat.card (fixV (B.map ρ))) :
    Nat.card F * Nat.card (fixV (B.map ρ)) ≤ Nat.card X := by
  have hYinv : ∀ g, ∀ x ∈ commV ρ.range, ρ g x ∈ commV ρ.range :=
    fun g _ hx => commV_inv ρ g hx
  obtain ⟨M₀, hM₀inv, -, hM₀Y, hirrS, hntS⟩ := exists_irr_sec ρ (R := ⊥)
    (fun g u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]) bot_le
    (commV_range_ne_bot ρ hnt).symm
  have hAK : B.map ρ ≤ ρ.range := Subgroup.map_le_range ρ B
  have hA2 : ∀ a ∈ B.map ρ, a ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB2 b hb, map_one]
  have hfaith := inf_centSec_eq_bot ρ hYinv hM₀inv hntS hAK hA2
  have hcardX : Nat.card X ≤ Nat.card (B.map ρ) * Nat.card (fixV (B.map ρ)) := by
    rw [card_map_eq ρ hnt hB2]
    exact hcard
  have hffS := sec_ff ρ hYinv hM₀inv hM₀Y hAK (map_ne_bot ρ hnt hB hB2)
    (isElemAbelian2_map ρ hB2 hBc) hcardX hfaith
  obtain ⟨F', iF', fF', hFF', σ, θ, hθ⟩ := exists_natCoord (secRho ρ hYinv hM₀inv) h14 hSQ hsq
    hF (sec_sq hX2) hirrS hntS hffS
  have hb := card_mul_card_fixV_le hθ (Subgroup.map_le_range _ B)
    (map_ne_bot (secRho ρ hYinv hM₀inv) hntS hB hB2)
  rw [hFF'] at hb
  have h1 := card_mul_inf_fixV_le_of_sec ρ hYinv hM₀inv hM₀Y B hb
  have h2 := card_mul_inf_fixV_mono (le_top : commV ρ.range ≤ ⊤) (fixV (B.map ρ)) h1
  rwa [top_inf_eq, Subgroup.card_top] at h2

theorem ffOff_decomp (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1) (ρ : SL3 F →* MulAut X)
    (hnt : ∃ g x, ρ g x ≠ x) {B : Subgroup (SL3 F)} (hB : B ≠ ⊥)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hqB : Nat.card F ≤ Nat.card B)
    (hidx : Nat.card X ≤ Nat.card F * Nat.card (fixV (B.map ρ))) : IsNatDecomp ρ := by
  have : Group.IsPerfect (SL3 F) := isPerfect_SL3
  have : CharP F 2 := FFC.charP_two_of_card_pow hF
  set P := commV ρ.range with hPdef
  set C := fixV ρ.range with hCdef
  have hPinv : ∀ g, ∀ x ∈ P, ρ g x ∈ P := fun g _ hx => commV_inv ρ g hx
  have hAK : B.map ρ ≤ ρ.range := Subgroup.map_le_range ρ B
  have hA2 : ∀ a ∈ B.map ρ, a ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB2 b hb, map_one]
  have hcardX : Nat.card X ≤ Nat.card (B.map ρ) * Nat.card (fixV (B.map ρ)) := by
    rw [card_map_eq ρ hnt hB2]
    exact hidx.trans (Nat.mul_le_mul_right _ hqB)
  have hPC' : P ⊔ C = ⊤ := ffSplit h14 hSQ hsq hF hX2 ρ hB hB2 hBc hqB hidx
  have hPC : P ⊓ C = ⊥ := by
    have hnts : ∃ g f, dualRho ρ g f ≠ f := by
      obtain ⟨g, x, hx⟩ := hnt
      by_contra hcon
      push Not at hcon
      apply hx
      have h1 : dualRho ρ g = 1 := MulEquiv.ext fun f => hcon g f
      rw [(dualRho_eq_one_iff hX2 ρ g).mp h1, MulAut.one_apply]
    have hcomms : Nat.card (commV (B.map (dualRho ρ))) ≤ Nat.card F := by
      rw [commV_map_dualRho hX2]
      have h1 := dualAnn_card hX2 (fixV (B.map ρ))
      have hc : 0 < Nat.card (fixV (B.map ρ)) := Nat.card_pos
      exact Nat.le_of_mul_le_mul_right (h1.le.trans hidx) hc
    obtain ⟨-, hsplit, -⟩ := dualOff_decomp h14 hSQ hsq hF dualGrp_sq (dualRho ρ) hnts hB hB2
      hBc hqB hcomms
    rw [commV_range_dualRho hX2, fixV_range_dualRho] at hsplit
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    obtain ⟨f, hf⟩ := exists_dualChar_ne_one hX2 hx1
    have hf' : f ∈ dualAnn C ⊔ dualAnn P := by rw [hsplit]; trivial
    obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := Subgroup.mem_sup.mp hf'
    apply hf
    change f₁ x * f₂ x = 1
    rw [hf₁ x hx.2, hf₂ x hx.1, mul_one]
  have hP := card_le_mul_inf_fixV (B.map ρ) P hidx
  have hirrP : ∀ J : Subgroup X, (∀ g, ∀ u ∈ J, ρ g u ∈ J) → J ≤ P → J = ⊥ ∨ J = P := by
    intro J hJ hJP
    by_cases hJe : J = P
    · exact Or.inr hJe
    left
    obtain ⟨M₀, hM₀inv, hJM₀, hM₀P, hirrS, hntS⟩ := exists_irr_sec ρ hJ hJP hJe
    have hfaith := inf_centSec_eq_bot ρ hPinv hM₀inv hntS hAK hA2
    have hffS := sec_ff ρ hPinv hM₀inv hM₀P hAK (map_ne_bot ρ hnt hB hB2)
      (isElemAbelian2_map ρ hB2 hBc) hcardX hfaith
    obtain ⟨F', iF', fF', hFF', σ, θ, hθ⟩ := exists_natCoord (secRho ρ hPinv hM₀inv) h14 hSQ
      hsq hF (sec_sq hX2) hirrS hntS hffS
    have hb := card_mul_card_fixV_le hθ (Subgroup.map_le_range _ B)
      (map_ne_bot (secRho ρ hPinv hM₀inv) hntS hB hB2)
    rw [hFF', map_secRho] at hb
    have hAP : B.map ρ ≤ stabSub P := hAK.trans (range_le_stabSub ρ hPinv)
    have hd := card_inf_fixV_le_autSec hM₀P hAP (U := M₀)
    have hcs := card_sec_mul hM₀P
    have hmm : Nat.card M₀ ≤ Nat.card ↥(M₀ ⊓ fixV (B.map ρ)) := by
      have hS0 : 0 < Nat.card (Sec P M₀) := Nat.card_pos
      refine Nat.le_of_mul_le_mul_left ?_ hS0
      calc Nat.card (Sec P M₀) * Nat.card M₀ = Nat.card P := hcs
        _ ≤ Nat.card F * Nat.card ↥(P ⊓ fixV (B.map ρ)) := hP
        _ ≤ Nat.card F * (Nat.card (fixV (autSec (B.map ρ) P M₀)) *
              Nat.card ↥(M₀ ⊓ fixV (B.map ρ))) := Nat.mul_le_mul_left _ hd
        _ = (Nat.card F * Nat.card (fixV (autSec (B.map ρ) P M₀))) *
              Nat.card ↥(M₀ ⊓ fixV (B.map ρ)) := by ring
        _ ≤ Nat.card (Sec P M₀) * Nat.card ↥(M₀ ⊓ fixV (B.map ρ)) :=
            Nat.mul_le_mul_right _ hb
    have hM₀A : M₀ ≤ fixV (B.map ρ) := by
      have := Subgroup.eq_of_le_of_card_ge (inf_le_left : M₀ ⊓ fixV (B.map ρ) ≤ M₀) hmm
      rw [← this]
      exact inf_le_right
    have hM₀fix := fix_of_fix ρ hM₀inv hB hB2 fun b hb m hm => hM₀A hm (ρ b) ⟨b, hb, rfl⟩
    have hM₀C : M₀ ≤ P ⊓ C := fun m hm => ⟨hM₀P hm, by rintro _ ⟨g, rfl⟩; exact hM₀fix g m hm⟩
    rw [hPC] at hM₀C
    exact eq_bot_iff.mpr (hJM₀.trans hM₀C)
  set ρP := resRho ρ P hPinv with hρP
  have hirrP' := irr_resRho ρ hPinv hirrP
  have hntP := resRho_nt ρ hnt
  have hP2 : ∀ p : ↥P, p ^ 2 = 1 := fun p => Subtype.ext (by
    rw [Subgroup.coe_pow, hX2, Subgroup.coe_one])
  have hfixP : (fixV (B.map ρP)).map P.subtype = P ⊓ fixV (B.map ρ) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.2, ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hp (ρP b) ⟨b, hb, rfl⟩)
    · rintro ⟨hxP, hx⟩
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      rintro _ ⟨b, hb, rfl⟩
      exact Subtype.ext (hx (ρ b) ⟨b, hb, rfl⟩)
  have hffP : IsFFModule ρP.range := by
    refine ⟨B.map ρP, Subgroup.map_le_range _ _, map_ne_bot ρP hntP hB hB2,
      isElemAbelian2_map ρP hB2 hBc, ?_⟩
    rw [card_map_eq ρP hntP hB2, ← Subgroup.card_map_of_injective P.subtype_injective, hfixP]
    exact hP.trans (Nat.mul_le_mul_right _ hqB)
  obtain ⟨F', iF', fF', hFF', σ, θ, hθ⟩ := exists_natCoord ρP h14 hSQ hsq hF hP2 hirrP' hntP hffP
  set τ : SL3 F →* SL3 F' := σ.symm.toMonoidHom.comp ρP.rangeRestrict with hτ
  have hτs : Function.Surjective τ := σ.symm.surjective.comp ρP.rangeRestrict_surjective
  have hστ : ∀ g, (σ (τ g) : MulAut ↥P) = ρP g := by
    intro g
    simp [hτ]
  have hτe : ∀ g (p : ↥P), θ (ρP g p) =
      Multiplicative.ofAdd ((τ g : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (θ p)) := by
    intro g p
    rw [← hστ g, hθ]
  exact ⟨hPC, hPC', F', iF', fF', hFF', τ, θ, hτs, hτe⟩

end FFDecomp

end CFSG.Quasithin.MS93.S4A.F
