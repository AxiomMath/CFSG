module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Infra_vtil_sq_eq_one (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (w : Vtil V₀ V hV) : w ^ 2 = 1 := by
  induction w using QuotientGroup.induction_on with
  | H x =>
    rw [← QuotientGroup.mk_pow, IntMod.sq_eq_one, QuotientGroup.mk_one]

theorem s15_Infra_v1Sub_le {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) : v1Sub D.M V₀ V hV L ≤ V := by
  by_cases h0 : V₀ = ⊥
  · rw [v1Sub_of_eq_bot D.M V₀ V hV L h0]
    refine iSup_le fun m => ?_
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hxW : (m : G) * x * (m : G)⁻¹ ∈ wSub V₀ V hV L := hx.1
    have hxV : (m : G) * x * (m : G)⁻¹ ∈ V := preTil_le V₀ V hV _ hxW
    have hm : (m : G) ∈ normalizer (V : Set G) := h.pairFacts.le_normalizer m.2
    exact (Subgroup.mem_normalizer_iff.1 hm x).2 hxV
  · rw [v1Sub_of_ne_bot D.M V₀ V hV L h0]
    exact h.pairFacts.le

theorem s15_Infra_le_v1Sub (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G) :
    V₀ ≤ v1Sub M V₀ V hV L := by
  by_cases h0 : V₀ = ⊥
  · rw [h0]
    exact bot_le
  · rw [v1Sub_of_ne_bot M V₀ V hV L h0]

theorem s15_Infra_le_normalizer_v1Sub {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) : D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) := by
  by_cases h0 : V₀ = ⊥
  · set X : Subgroup G := wSub V₀ V hV L ⊓ centralizer (L : Set G) with hX
    have hV₁ : v1Sub D.M V₀ V hV L = ⨆ m : ↥D.M, conjSubgroup X (m : G) :=
      v1Sub_of_eq_bot D.M V₀ V hV L h0
    have hmain : ∀ x ∈ D.M, conjSubgroup (v1Sub D.M V₀ V hV L) x ≤ v1Sub D.M V₀ V hV L := by
      intro x hx
      rw [hV₁]
      have hmap : conjSubgroup (⨆ m : ↥D.M, conjSubgroup X (m : G)) x =
          ⨆ m : ↥D.M, conjSubgroup (conjSubgroup X (m : G)) x := by
        simpa only [conjSubgroup] using
          (Subgroup.map_iSup (G := G) (N := G)
            (f := (MulAut.conj x⁻¹ : MulAut G).toMonoidHom)
            (s := fun m : ↥D.M => conjSubgroup X (m : G)))
      rw [hmap]
      refine iSup_le fun m => ?_
      rw [conjSubgroup_conjSubgroup]
      exact le_iSup (fun m' : ↥D.M => conjSubgroup X (m' : G)) ⟨(m : G) * x, D.M.mul_mem m.2 hx⟩
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    have h1 : conjSubgroup (v1Sub D.M V₀ V hV L) x ≤ v1Sub D.M V₀ V hV L := hmain x hx
    have h2 : conjSubgroup (v1Sub D.M V₀ V hV L) x⁻¹ ≤ v1Sub D.M V₀ V hV L :=
      hmain x⁻¹ (D.M.inv_mem hx)
    have h3 : conjSubgroup (conjSubgroup (v1Sub D.M V₀ V hV L) x⁻¹) x ≤
        conjSubgroup (v1Sub D.M V₀ V hV L) x := Subgroup.map_mono h2
    have h4 : v1Sub D.M V₀ V hV L ≤ conjSubgroup (v1Sub D.M V₀ V hV L) x := by
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h3
      exact h3
    have hEq : conjSubgroup (v1Sub D.M V₀ V hV L) x = v1Sub D.M V₀ V hV L :=
      le_antisymm h1 h4
    intro h
    rw [← mem_conjSubgroup_iff, hEq]
  · rw [v1Sub_of_ne_bot D.M V₀ V hV L h0]
    exact h.pairFacts.le_normalizer₀

theorem s15_Infra_mSub_eq_rk_imgTil_add (V₀ V U : Subgroup G) (hV : IsElemAbelian 2 V)
    (hU : U ≤ V) : mSub U = rk ↥(imgTil V₀ V hV U) + mSub (U ⊓ V₀) := by
  have hker : (mkTil V₀ V hV).ker = modNull V₀ V hV := QuotientGroup.ker_mk' _
  have hcardU : Nat.card ↥(intSub V hV U) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv
  have hcardI : Nat.card ↥(modNull V₀ V hV ⊓ intSub V hV U) = Nat.card ↥(U ⊓ V₀) := by
    have heq : modNull V₀ V hV ⊓ intSub V hV U = intSub V hV (U ⊓ V₀) := by
      ext x
      rw [Subgroup.mem_inf, mem_modNull, mem_intSub, mem_intSub, Subgroup.mem_inf]
      tauto
    rw [heq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans inf_le_left hU)).toEquiv
  have hmul : Nat.card ↥(imgTil V₀ V hV U) * Nat.card ↥(U ⊓ V₀) = Nat.card ↥U := by
    have hmain := Subgroup.relIndex_mul_card (H := (mkTil V₀ V hV).ker) (K := intSub V hV U)
    rw [Subgroup.relIndex_ker] at hmain
    rw [hker] at hmain
    rw [hcardI, hcardU] at hmain
    exact hmain
  unfold mSub rk
  rw [← hmul, padicValNat.mul (Nat.card_pos (α := ↥(imgTil V₀ V hV U))).ne'
    (Nat.card_pos (α := ↥(U ⊓ V₀))).ne']

theorem s15_Infra_imgTil_top (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    imgTil V₀ V hV V = ⊤ := by
  have h : intSub V hV V = (⊤ : Subgroup (IntMod V hV)) := by
    ext x
    rw [mem_intSub]
    exact ⟨fun _ => trivial, fun _ => x.val_mem⟩
  rw [imgTil, h, Subgroup.map_top_of_surjective (mkTil V₀ V hV) (mkTil_surjective V₀ V hV)]

theorem s15_Infra_imgTil_sup_left {V₀ V U : Subgroup G} (hV : IsElemAbelian 2 V) (hU : U ≤ V)
    (hV₀ : V₀ ≤ V) : imgTil V₀ V hV (U ⊔ V₀) = imgTil V₀ V hV U := by
  have hsup : intSub V hV (U ⊔ V₀) = intSub V hV U ⊔ modNull V₀ V hV := by
    unfold intSub modNull
    exact Subgroup.subgroupOf_sup hU hV₀
  refine le_antisymm ?_ ?_
  · intro q hq
    rw [mem_imgTil] at hq ⊢
    obtain ⟨x, hx, rfl⟩ := hq
    have hx' : x ∈ intSub V hV (U ⊔ V₀) := (mem_intSub V hV (U ⊔ V₀) x).2 hx
    rw [hsup] at hx'
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 hx'
    refine ⟨y, (mem_intSub V hV U y).1 hy, ?_⟩
    have hz1 : mkTil V₀ V hV z = 1 := by
      rw [← map_one (mkTil V₀ V hV), mkTil_eq_iff]
      simpa using (mem_modNull V₀ V hV z).1 hz
    rw [← hyz, map_mul, hz1, mul_one]
  · intro q hq
    rw [mem_imgTil] at hq ⊢
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨x, (le_sup_left : U ≤ U ⊔ V₀) hx, rfl⟩

theorem s15_Infra_barSub_conjSubgroup (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ stabTil V₀ V) (X : Subgroup G) :
    barSub V₀ V hV (conjSubgroup X m) =
      (barSub V₀ V hV X).map (MulAut.conj (actTil V₀ V hV ⟨m, hm⟩)⁻¹).toMonoidHom := by
  ext φ
  rw [mem_barSub, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [mem_conjSubgroup_iff] at hg
    have hgs : m * (g : G) * m⁻¹ ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem hm g.2) ((stabTil V₀ V).inv_mem hm)
    refine ⟨actTil V₀ V hV ⟨m * (g : G) * m⁻¹, hgs⟩,
      actTil_mem_barSub V₀ V hV hg hgs, ?_⟩
    change MulAut.conj (actTil V₀ V hV ⟨m, hm⟩)⁻¹
        (actTil V₀ V hV ⟨m * (g : G) * m⁻¹, hgs⟩) = actTil V₀ V hV g
    rw [MulAut.conj_apply,
      show (actTil V₀ V hV ⟨m, hm⟩)⁻¹ = actTil V₀ V hV ⟨m, hm⟩⁻¹
        from (map_inv _ _).symm, ← map_mul]
    rw [show (actTil V₀ V hV ⟨m, hm⟩⁻¹)⁻¹ = actTil V₀ V hV ⟨m, hm⟩
      from by simp, ← map_mul]
    have hg' : (⟨m, hm⟩⁻¹ * ⟨m * (g : G) * m⁻¹, hgs⟩ * ⟨m, hm⟩ : stabTil V₀ V) = g :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]; group)
    rw [hg']
  · rintro ⟨θ, hθ, hθφ⟩
    rw [mem_barSub] at hθ
    obtain ⟨g, hgX, rfl⟩ := hθ
    have hgs : m⁻¹ * (g : G) * m ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem ((stabTil V₀ V).inv_mem hm) g.2) hm
    refine ⟨⟨m⁻¹ * (g : G) * m, hgs⟩, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      show m * (m⁻¹ * (g : G) * m) * m⁻¹ ∈ X
      rw [show m * (m⁻¹ * (g : G) * m) * m⁻¹ = (g : G) by group]
      exact hgX
    · rw [← hθφ]
      change actTil V₀ V hV ⟨m⁻¹ * (g : G) * m, hgs⟩ =
        MulAut.conj (actTil V₀ V hV ⟨m, hm⟩)⁻¹ (actTil V₀ V hV g)
      rw [MulAut.conj_apply,
        show (actTil V₀ V hV ⟨m, hm⟩)⁻¹ = actTil V₀ V hV ⟨m, hm⟩⁻¹
          from (map_inv _ _).symm, ← map_mul]
      rw [show (actTil V₀ V hV ⟨m, hm⟩⁻¹)⁻¹ = actTil V₀ V hV ⟨m, hm⟩
        from by simp, ← map_mul]
      have hg' : (⟨m⁻¹ * (g : G) * m, hgs⟩ : stabTil V₀ V) =
          ⟨m, hm⟩⁻¹ * g * ⟨m, hm⟩ := rfl
      rw [hg']

theorem s15_Infra_commSub_top_map_conj {W : Type*} [CommGroup W]
    (X : Subgroup (MulAut W)) (α : MulAut W) :
    commSub ⊤ (X.map (MulAut.conj α).toMonoidHom) = (commSub ⊤ X).map α.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, -, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    refine ⟨x₀ (α⁻¹ w) * (α⁻¹ w)⁻¹, ⟨x₀, hx₀, α⁻¹ w, trivial, rfl⟩, ?_⟩
    change α (x₀ (α⁻¹ w) * (α⁻¹ w)⁻¹) = (MulAut.conj α x₀) w * w⁻¹
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.apply_inv_self, map_mul, map_inv]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x₀, hx₀, v, -, rfl⟩ := hs
    refine ⟨MulAut.conj α x₀, ⟨x₀, hx₀, rfl⟩, α v, trivial, ?_⟩
    change (MulAut.conj α x₀) (α v) * (α v)⁻¹ = α (x₀ v * v⁻¹)
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.inv_apply_self,
      map_mul, map_inv]

theorem s15_Infra_wTil_conjSubgroup (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ stabTil V₀ V) :
    wTil V₀ V hV (conjSubgroup L m) =
      (wTil V₀ V hV L).map ((actTil V₀ V hV ⟨m, hm⟩)⁻¹).toMonoidHom := by
  unfold wTil
  rw [s15_Infra_barSub_conjSubgroup V₀ V hV hm L]
  exact s15_Infra_commSub_top_map_conj (barSub V₀ V hV L) (actTil V₀ V hV ⟨m, hm⟩)⁻¹

theorem s15_Infra_preTil_map_actTil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ stabTil V₀ V) (S : Subgroup (Vtil V₀ V hV)) :
    preTil V₀ V hV (S.map ((actTil V₀ V hV ⟨m, hm⟩)⁻¹).toMonoidHom) =
      conjSubgroup (preTil V₀ V hV S) m := by
  ext g
  constructor
  · intro hg
    rw [mem_preTil] at hg
    obtain ⟨x, rfl, hxS⟩ := hg
    rw [Subgroup.mem_map] at hxS
    obtain ⟨s, hsS, hs⟩ := hxS
    rw [mem_conjSubgroup_iff]
    have hxV : m * x.val * m⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (stabTil_le_normalizer V₀ V hm) x.val).1 x.val_mem
    rw [mem_preTil_iff_of_mem V₀ V hV S hxV]
    have h1 : (IntMod.mk hV ⟨m * x.val * m⁻¹, hxV⟩ : IntMod V hV) =
        actStab V₀ V hV ⟨m, hm⟩ x := by
      apply IntMod.val_injective
      rw [actStab_apply_val]
      rfl
    rw [h1, ← actTil_mk, ← hs]
    change (actTil V₀ V hV ⟨m, hm⟩) ((actTil V₀ V hV ⟨m, hm⟩)⁻¹ s) ∈ S
    rw [MulAut.apply_inv_self]
    exact hsS
  · intro hg
    rw [mem_conjSubgroup_iff] at hg
    rw [mem_preTil] at hg ⊢
    obtain ⟨y, hy, hyS⟩ := hg
    have hgV : g ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (stabTil_le_normalizer V₀ V hm) g).2 (hy ▸ y.val_mem)
    refine ⟨actStab V₀ V hV ⟨m, hm⟩⁻¹ y, ?_, ?_⟩
    · rw [actStab_apply_val, hy]
      simp only [InvMemClass.coe_inv, Subtype.coe_mk]
      group
    · rw [Subgroup.mem_map]
      refine ⟨mkTil V₀ V hV y, hyS, ?_⟩
      rw [← map_inv]
      exact actTil_mk V₀ V hV ⟨m, hm⟩⁻¹ y

theorem s15_Infra_wSub_conjSubgroup (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ stabTil V₀ V) :
    wSub V₀ V hV (conjSubgroup L m) = conjSubgroup (wSub V₀ V hV L) m := by
  unfold wSub
  rw [s15_Infra_wTil_conjSubgroup V₀ V L hV hm]
  exact s15_Infra_preTil_map_actTil V₀ V hV hm (wTil V₀ V hV L)

theorem s15_Infra_imgTil_conjSubgroup (V₀ V U : Subgroup G) (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ stabTil V₀ V) :
    imgTil V₀ V hV (conjSubgroup U m) =
      (imgTil V₀ V hV U).map ((actTil V₀ V hV ⟨m, hm⟩)⁻¹).toMonoidHom := by
  ext q
  rw [mem_imgTil, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_conjSubgroup_iff] at hx
    refine ⟨mkTil V₀ V hV (actStab V₀ V hV ⟨m, hm⟩ x), ?_, ?_⟩
    · rw [mem_imgTil]
      exact ⟨actStab V₀ V hV ⟨m, hm⟩ x, hx, rfl⟩
    · rw [← actTil_mk]
      simp
  · rintro ⟨θ, hθ, rfl⟩
    rw [mem_imgTil] at hθ
    obtain ⟨x, hx, rfl⟩ := hθ
    refine ⟨actStab V₀ V hV ⟨m, hm⟩⁻¹ x, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff, actStab_apply_val]
      simp only [InvMemClass.coe_inv, Subtype.coe_mk]
      rw [show m * (m⁻¹ * x.val * (m⁻¹)⁻¹) * m⁻¹ = x.val by group]
      exact hx
    · rw [← map_inv]
      exact actTil_mk V₀ V hV ⟨m, hm⟩⁻¹ x

theorem s15_Infra_conjSubgroup_v1Sub {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) {m : G} (hm : m ∈ D.M) :
    conjSubgroup (v1Sub D.M V₀ V hV L) m = v1Sub D.M V₀ V hV L :=
  conjSubgroup_eq_iff_mem_normalizer.mpr (s15_Infra_le_normalizer_v1Sub h hV hm)

theorem s15_Infra_v1Sub_eq_iSup {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) (h0 : V₀ = ⊥) :
    v1Sub D.M V₀ V hV L = ⨆ m : D.M,
      wSub V₀ V hV (conjSubgroup L (m : G)) ⊓ centralizer (conjSubgroup L (m : G) : Set G) := by
  rw [v1Sub_of_eq_bot D.M V₀ V hV L h0]
  refine iSup_congr fun m => ?_
  rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
    ← s15_Infra_wSub_conjSubgroup V₀ V L hV
      (le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀ m.2)]

theorem s15_Infra_mem_nBar_iff {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) {m : G} (hm : m ∈ D.M) :
    m ∈ nBar D.M V₀ V hV L ↔
      barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  rw [nBar, mem_preBarSub]
  constructor
  · rintro ⟨-, hh, hnorm⟩
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV hh L]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 (inv_mem hnorm)
  · intro heq
    refine ⟨hm, hMs hm, ?_⟩
    have hmap : (barSub V₀ V hV L).map
        (MulAut.conj (actTil V₀ V hV ⟨m, hMs hm⟩)⁻¹).toMonoidHom = barSub V₀ V hV L := by
      rw [← s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hm) L]
      exact heq
    exact (inv_mem_iff).1 ((Subgroup.mem_normalizer_iff_map_conj_eq).2 hmap)

theorem s15_Infra_mul_inv_mem_nBar_iff {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) {m m' : G} (hm : m ∈ D.M) (hm' : m' ∈ D.M) :
    m' * m⁻¹ ∈ nBar D.M V₀ V hV L ↔
      barSub V₀ V hV (conjSubgroup L m') = barSub V₀ V hV (conjSubgroup L m) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hmem : m' * m⁻¹ ∈ D.M := D.M.mul_mem hm' (D.M.inv_mem hm)
  have hstab_inv : m⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem (hMs hm)
  have ha_inv : actTil V₀ V hV ⟨m⁻¹, hstab_inv⟩ = (actTil V₀ V hV ⟨m, hMs hm⟩)⁻¹ := by
    rw [show (⟨m⁻¹, hstab_inv⟩ : stabTil V₀ V) = (⟨m, hMs hm⟩ : stabTil V₀ V)⁻¹ from rfl,
      map_inv]
  have hconj : ∀ x : G,
      barSub V₀ V hV (conjSubgroup L (x * m⁻¹)) =
        (barSub V₀ V hV (conjSubgroup L x)).map
          (MulAut.conj (actTil V₀ V hV ⟨m, hMs hm⟩)).toMonoidHom := by
    intro x
    rw [← conjSubgroup_conjSubgroup L x m⁻¹,
      s15_Infra_barSub_conjSubgroup V₀ V hV hstab_inv (conjSubgroup L x)]
    congr 1
    rw [ha_inv, inv_inv]
  have hone : conjSubgroup L (m * m⁻¹) = L := by
    rw [mul_inv_cancel, conjSubgroup_one]
  rw [s15_Infra_mem_nBar_iff h hV hmem, hconj m']
  constructor
  · intro hh
    apply Subgroup.map_injective
      (f := (MulAut.conj (actTil V₀ V hV ⟨m, hMs hm⟩)).toMonoidHom)
      (MulEquiv.injective (MulAut.conj (actTil V₀ V hV ⟨m, hMs hm⟩)))
    rw [← hconj m, hone]
    exact hh
  · intro hh
    have hh' := congrArg (Subgroup.map
      (MulAut.conj (actTil V₀ V hV ⟨m, hMs hm⟩)).toMonoidHom) hh
    rw [← hconj m, hone] at hh'
    exact hh'

theorem s15_Infra_wSub_eq_of_barSub_eq_bot {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L = ⊥) :
    wSub V₀ V hV L = V₀ := by
  unfold wSub wTil
  rw [hL]
  have hcomm : commSub (⊤ : Subgroup (Vtil V₀ V hV))
      (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) = ⊥ := by
    rw [commSub_eq_bot_iff]
    intro v _ x hx
    rw [Subgroup.mem_bot.1 hx]
    rfl
  rw [hcomm, preTil_bot, inf_eq_right.mpr h.pairFacts.le]

theorem s15_Infra_v1Sub_eq_of_barSub_eq_bot {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L = ⊥) :
    v1Sub D.M V₀ V hV L = V₀ := by
  by_cases h0 : V₀ = ⊥
  · subst h0
    rw [v1Sub_of_eq_bot D.M ⊥ V hV L rfl]
    have hW : wSub ⊥ V hV L = ⊥ := s15_Infra_wSub_eq_of_barSub_eq_bot h hV hL
    rw [hW, bot_inf_eq]
    simp [E3.conjSubgroup_bot]
  · rw [v1Sub_of_ne_bot D.M V₀ V hV L h0]

theorem s15_Infra_nBar_eq_of_barSub_eq_bot {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L = ⊥) :
    nBar D.M V₀ V hV L = D.M := by
  have hbot : normalizer ((⊥ : Subgroup (MulAut (Vtil V₀ V hV))) :
      Set (MulAut (Vtil V₀ V hV))) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot
  rw [nBar, hL, hbot]
  ext g
  rw [mem_preBarSub]
  constructor
  · rintro ⟨hgM, -⟩
    exact hgM
  · intro hgM
    exact ⟨hgM, le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀ hgM, trivial⟩

theorem s15_Infra_iSup_barSub_le {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    (⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) ≤
      Mbar D.M V₀ V h.isElemAbelian := by
  refine iSup_le fun m => barSub_mono V₀ V h.isElemAbelian ?_
  calc conjSubgroup L (m : G) ≤ conjSubgroup D.M (m : G) := E3.conjSubgroup_mono_left _ h.le
    _ = D.M := conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer m.2)

theorem s15_Infra_iSup_barSub_normal {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) :
    ((⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))).subgroupOf
      (Mbar D.M V₀ V h.isElemAbelian)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (s15_Infra_iSup_barSub_le h)]
  intro φ hφ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  obtain ⟨g, hgM, rfl⟩ := (mem_barSub V₀ V h.isElemAbelian D.M φ).1 hφ
  rw [Subgroup.map_iSup]
  have hstep : ∀ m : D.M,
      (barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))).map
          (MulAut.conj (actTil V₀ V h.isElemAbelian g)).toMonoidHom =
        barSub V₀ V h.isElemAbelian (conjSubgroup L ((m : G) * (g : G)⁻¹)) := by
    intro m
    have hginv : (g : G)⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem g.2
    have h1 := s15_Infra_barSub_conjSubgroup V₀ V h.isElemAbelian (m := (g : G)⁻¹) hginv
      (conjSubgroup L (m : G))
    rw [conjSubgroup_conjSubgroup] at h1
    have h2 : actTil V₀ V h.isElemAbelian ⟨(g : G)⁻¹, hginv⟩ =
        (actTil V₀ V h.isElemAbelian g)⁻¹ := map_inv _ _
    rw [h2, inv_inv] at h1
    exact h1.symm
  simp only [MulEquiv.toMonoidHom_eq_coe] at hstep
  rw [iSup_congr hstep]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun m => le_iSup (fun m' : D.M =>
      barSub V₀ V h.isElemAbelian (conjSubgroup L (m' : G)))
      ⟨(m : G) * (g : G)⁻¹, D.M.mul_mem m.2 (D.M.inv_mem hgM)⟩
  · refine iSup_le fun m => ?_
    have hσ : barSub V₀ V h.isElemAbelian (conjSubgroup L
        (((m : G) * (g : G)) * (g : G)⁻¹)) =
        barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G)) := by
      congr 1
      congr 1
      group
    rw [← hσ]
    exact le_iSup (fun m' : D.M =>
      barSub V₀ V h.isElemAbelian (conjSubgroup L ((m' : G) * (g : G)⁻¹)))
      ⟨(m : G) * (g : G), D.M.mul_mem m.2 hgM⟩

@[expose] noncomputable def wStarConj (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) : Set (Subgroup (vStar M V₀ V hV L)) :=
  {X | ∃ m ∈ M, X = imgTil (v1Sub M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) m)}

theorem s15_Infra_map_wStar_mem_wStarConj {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V)
    {e : MulAut (vStar D.M V₀ V hV L)} (he : e ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :
    (wStar D.M V₀ V hV L).map e.toMonoidHom ∈ wStarConj D.M V₀ V hV L := by
  obtain ⟨g, hgM, rfl⟩ :=
    (mem_barSub (v1Sub D.M V₀ V hV L) V hV D.M e).1 he
  refine ⟨(g : G)⁻¹, D.M.inv_mem hgM, ?_⟩
  have hginv : (g : G)⁻¹ ∈ stabTil (v1Sub D.M V₀ V hV L) V :=
    (stabTil _ _).inv_mem g.2
  rw [wStar]
  rw [s15_Infra_imgTil_conjSubgroup (v1Sub D.M V₀ V hV L) V (wSub V₀ V hV L) hV hginv]
  rw [show actTil (v1Sub D.M V₀ V hV L) V hV ⟨(g : G)⁻¹, hginv⟩ =
      (actTil (v1Sub D.M V₀ V hV L) V hV g)⁻¹ from map_inv _ _, inv_inv]

theorem mSub_wSub_sup_v1Sub (D : Data G) {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) :
    mSub (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) =
      gamma15 D.M V₀ V hV L + mSub (v1Sub D.M V₀ V hV L) := by
  have hle : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h hV)
  rw [s15_Infra_mSub_eq_rk_imgTil_add (v1Sub D.M V₀ V hV L) V _ hV hle,
    inf_eq_right.mpr le_sup_right,
    s15_Infra_imgTil_sup_left (V₀ := v1Sub D.M V₀ V hV L) (U := wSub V₀ V hV L) hV
      (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h hV)]
  rfl

theorem mSub_wSub (D : Data G) {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) :
    mSub (wSub V₀ V hV L) = gamma15 D.M V₀ V hV L + delta15 D.M V₀ V hV L := by
  rw [s15_Infra_mSub_eq_rk_imgTil_add (v1Sub D.M V₀ V hV L) V (wSub V₀ V hV L) hV
    (preTil_le V₀ V hV _), inf_comm]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
