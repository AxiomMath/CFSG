module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteOrder
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylTorusAut
public import CFSG.LocalAnalysis.StandardType.GGIrred937Lattice
import CFSG.LocalAnalysis.StandardType.GGTorusMaxStructAux2

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem

private theorem tmStruct_transport {G H W V : Type} [Group G] [Group H] [Group W] [Group V]
    (e : G ≃* H) {E : Subgroup G} {T : Subgroup H} (hET : E.map e.toMonoidHom = T)
    (act : W →* MulAut V) (π : (Subgroup.normalizer (T : Set H)) →* W) (φ : T ≃* V)
    (hπs : Function.Surjective π)
    (hπk : π.ker = T.subgroupOf (Subgroup.normalizer (T : Set H)))
    (hπi : ∀ (g : Subgroup.normalizer (T : Set H)) (x : T),
      φ (T.normalizerMonoidHom g x) = act (π g) (φ x)) :
    ∃ (π' : (Subgroup.normalizer (E : Set G)) →* W) (φ' : E ≃* V),
      Function.Surjective π' ∧ π'.ker = E.subgroupOf (Subgroup.normalizer (E : Set G)) ∧
      ∀ (g : Subgroup.normalizer (E : Set G)) (x : E),
        φ' (E.normalizerMonoidHom g x) = act (π' g) (φ' x) := by
  have hmemT : ∀ y : G, e y ∈ T ↔ y ∈ E := by
    intro y
    rw [← hET]
    exact Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective
  have hmem : ∀ g : G, g ∈ Subgroup.normalizer (E : Set G) ↔
      e g ∈ Subgroup.normalizer (T : Set H) := by
    intro g
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h x
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [hmemT, show e g * e y * (e g)⁻¹ = e (g * y * g⁻¹) by simp, hmemT]
      exact h y
    · intro h y
      have h1 := h (e y)
      rw [hmemT, show e g * e y * (e g)⁻¹ = e (g * y * g⁻¹) by simp, hmemT] at h1
      exact h1
  let Φ : (Subgroup.normalizer (E : Set G)) →* (Subgroup.normalizer (T : Set H)) :=
    { toFun := fun g => ⟨e g, (hmem g).mp g.2⟩
      map_one' := Subtype.ext (map_one e)
      map_mul' := fun g g' => Subtype.ext (map_mul e (g : G) (g' : G)) }
  have hΦsurj : Function.Surjective Φ := by
    intro t
    refine ⟨⟨e.symm t, (hmem _).mpr (by simpa using t.2)⟩, ?_⟩
    exact Subtype.ext (by
      show e (e.symm (t : H)) = (t : H)
      exact e.apply_symm_apply _)
  let ψ : E →* T :=
    { toFun := fun x => ⟨e x, (hmemT x).mpr x.2⟩
      map_one' := Subtype.ext (map_one e)
      map_mul' := fun x y => Subtype.ext (map_mul e (x : G) (y : G)) }
  have hψbij : Function.Bijective ψ := by
    constructor
    · intro x y hxy
      exact Subtype.ext (e.injective (congrArg Subtype.val hxy))
    · intro t
      have ht : (t : H) ∈ E.map e.toMonoidHom := hET ▸ t.2
      obtain ⟨y, hy, hyt⟩ := ht
      exact ⟨⟨y, hy⟩, Subtype.ext hyt⟩
  refine ⟨π.comp Φ, (MulEquiv.ofBijective ψ hψbij).trans φ, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨t, ht⟩ := hπs w
    obtain ⟨g, hg⟩ := hΦsurj t
    exact ⟨g, by simp [hg, ht]⟩
  · ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : π (Φ g) = 1 ↔ ((Φ g : Subgroup.normalizer (T : Set H)) : H) ∈ T := by
      rw [← MonoidHom.mem_ker, hπk, Subgroup.mem_subgroupOf]
    simp only [MonoidHom.comp_apply]
    rw [h1]
    exact hmemT g
  · intro g x
    have hx : ψ (E.normalizerMonoidHom g x) = T.normalizerMonoidHom (Φ g) (ψ x) := by
      apply Subtype.ext
      change e ((g : G) * (x : G) * (g : G)⁻¹) = e (g : G) * e (x : G) * (e (g : G))⁻¹
      rw [map_mul, map_mul, map_inv]
    have h := hπi (Φ g) (ψ x)
    change φ (ψ (E.normalizerMonoidHom g x)) = act (π (Φ g)) (φ (ψ x))
    rw [hx]
    exact h

private theorem tmStruct_card_of {G W : Type} [Group G] [Group W] {E : Subgroup G}
    (π : (Subgroup.normalizer (E : Set G)) →* W) (hπs : Function.Surjective π)
    (hπk : π.ker = E.subgroupOf (Subgroup.normalizer (E : Set G))) :
    Nat.card (Subgroup.normalizer (E : Set G)) = Nat.card E * Nat.card W := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have h2 : Nat.card (Subgroup.normalizer (E : Set G) ⧸ π.ker) = Nat.card W :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv
  have h3 : Nat.card π.ker = Nat.card E := by
    rw [hπk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  rw [h1, h2, h3, mul_comm]

private theorem tmStruct_cent_of {G W V : Type} [Group G] [Group W] [Group V] {E : Subgroup G}
    (act : W →* MulAut V) (hact : Function.Injective act)
    (π : (Subgroup.normalizer (E : Set G)) →* W) (φ : E ≃* V)
    (hπk : π.ker = E.subgroupOf (Subgroup.normalizer (E : Set G)))
    (hπi : ∀ (g : Subgroup.normalizer (E : Set G)) (x : E),
      φ (E.normalizerMonoidHom g x) = act (π g) (φ x))
    (g : G) (hg : g ∈ Subgroup.normalizer (E : Set G)) (hc : ∀ e ∈ E, g * e = e * g) :
    g ∈ E := by
  have h1 : act (π ⟨g, hg⟩) = 1 := by
    refine MulEquiv.ext fun v => ?_
    obtain ⟨x, rfl⟩ := φ.surjective v
    rw [← hπi ⟨g, hg⟩ x, MulAut.one_apply]
    congr 1
    exact Subtype.ext (by
      show g * (x : G) * g⁻¹ = (x : G)
      rw [hc x x.2, mul_inv_cancel_right])
  have h2 : π ⟨g, hg⟩ = 1 := hact (h1.trans (map_one act).symm)
  have h3 : (⟨g, hg⟩ : Subgroup.normalizer (E : Set G)) ∈ π.ker := h2
  rw [hπk, Subgroup.mem_subgroupOf] at h3
  exact h3

private theorem tmStruct_irred_of {G : Type} [Group G] {τ : Tag} {E : Subgroup G}
    (π : (Subgroup.normalizer (E : Set G)) →* WeylGroup τ)
    (φ : E ≃* Multiplicative (Fin τ.rank → ZMod 3)) (hπs : Function.Surjective π)
    (hπi : ∀ (g : Subgroup.normalizer (E : Set G)) (x : E),
      φ (E.normalizerMonoidHom g x) = ExcWeylOuter.torusMulAut τ 3 (π g) (φ x))
    (hirr : ∀ U : AddSubgroup (Fin τ.rank → ZMod 3),
      (∀ (i : Fin τ.rank) (x : Fin τ.rank → ZMod 3), x ∈ U →
        TableBExc.torusAct τ 3 (simple τ i) x ∈ U) → U = ⊥ ∨ U = ⊤) :
    GGWeylIrred E := by
  haveI : NeZero 3 := ⟨by norm_num⟩
  let ι : Multiplicative (Fin τ.rank → ZMod 3) →* G := E.subtype.comp φ.symm.toMonoidHom
  have hinj : Function.Injective ι :=
    Subtype.val_injective.comp φ.symm.injective
  have hrange : ι.range = E := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact (φ.symm s).2
    · intro hx
      exact ⟨φ ⟨x, hx⟩, by simp [ι]⟩
  choose g hg using fun i : Fin τ.rank => hπs (simple τ i)
  have hm : ∀ (i : Fin τ.rank) (s : Fin τ.rank → ZMod 3),
      (g i : G) * ι (Multiplicative.ofAdd s) * (g i : G)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct τ 3 (simple τ i) s)) := by
    intro i s
    have h1 := hπi (g i) (φ.symm (Multiplicative.ofAdd s))
    rw [hg i, MulEquiv.apply_symm_apply, ExcWeylOuter.torusMulAut_apply] at h1
    have h2 := (φ.eq_symm_apply).mpr h1
    exact congrArg (fun y : E => (y : G)) h2
  have h := Irred937.ggWeylIrred_range_of_torusAct ι hinj (fun i => (g i : G)) hm hirr
  rwa [hrange] at h

theorem tmStruct_E7
    (G : Type) [Group G] [Finite G] (hEm : IsEm 7 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 7) :
    ∃ (π : (Subgroup.normalizer (E : Set G)) →* WeylGroup Tag.E7)
      (φ : E ≃* Multiplicative (Fin Tag.E7.rank → ZMod 3)),
      Function.Surjective π ∧ π.ker = E.subgroupOf (Subgroup.normalizer (E : Set G)) ∧
      ∀ (g : Subgroup.normalizer (E : Set G)) (e : E),
        φ (E.normalizerMonoidHom g e) = ExcWeylOuter.torusMulAut Tag.E7 3 (π g) (φ e) := by
  obtain ⟨hZ, ⟨t, r, n⟩, ⟨hmt, -, hn⟩, hlab⟩ := exists_label_of_marking hsimple hEm
  dsimp only at hmt hn
  subst hn
  have ht : t = .E7 := by rcases hmt with ⟨-, h⟩ | ⟨h, -⟩ <;> [exact h; omega]
  obtain ⟨e⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := ⟨t, r, 1⟩) hlab ht hZ
  let eG : G ≃* adjointGroup .E7 (GaloisField 2 1) := Subgroup.topEquiv.symm.trans e
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by omega)]; norm_num
  have hE' : IsElemAbelian 3 (E.map eG.toMonoidHom) := TableB.isElemAbelian_map hE eG.toMonoidHom
  have hcard' : Nat.card (E.map eG.toMonoidHom) = 3 ^ 7 := by
    rw [Subgroup.card_map_of_injective eG.injective, hcard]
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E7 hGF hE' hcard'.ge
  have hE1 : E.map (eG.trans (MulAut.conj c⁻¹)).toMonoidHom =
      (TableBExcTwoTB.tE (GaloisField 2 1) TableBExcTwo.frameE7).range := by
    have h : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id (adjointGroup .E7 (GaloisField 2 1)) := by
      ext y
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
      group
    have h1 : (eG.trans (MulAut.conj c⁻¹)).toMonoidHom =
        (MulAut.conj c⁻¹).toMonoidHom.comp eG.toMonoidHom := rfl
    rw [h1, ← Subgroup.map_map, hc, Subgroup.map_map, h, Subgroup.map_id]
  obtain ⟨π, φ, hπs, hπk, hπi⟩ := tmStruct_concrete (τ := .E7) (d := 6) (K := GaloisField 2 1)
    (Or.inl rfl) TableBExcTwo.frameE7 rfl TableBExcTwoFusion.frameE7_reflections
    TableBExc.Three.cartan_symm_E7
    (TableBExc.isUnit_det_cartan_of_eq Nat.prime_three CFSG.StandardType.det_cartan_E7
      (by norm_num)) hGF (TableBExcTwoTB.centralizer_tE_frameE7 hGF)
  exact tmStruct_transport (eG.trans (MulAut.conj c⁻¹)) hE1 (ExcWeylOuter.torusMulAut Tag.E7 3)
    π φ hπs hπk hπi

theorem tmStruct_E8
    (G : Type) [Group G] [Finite G] (hEm : IsEm 8 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 8) :
    ∃ (π : (Subgroup.normalizer (E : Set G)) →* WeylGroup Tag.E8)
      (φ : E ≃* Multiplicative (Fin Tag.E8.rank → ZMod 3)),
      Function.Surjective π ∧ π.ker = E.subgroupOf (Subgroup.normalizer (E : Set G)) ∧
      ∀ (g : Subgroup.normalizer (E : Set G)) (e : E),
        φ (E.normalizerMonoidHom g e) = ExcWeylOuter.torusMulAut Tag.E8 3 (π g) (φ e) := by
  obtain ⟨hZ, ⟨t, r, n⟩, ⟨hmt, -, hn⟩, hlab⟩ := exists_label_of_marking hsimple hEm
  dsimp only at hmt hn
  subst hn
  have ht : t = .E8 := by rcases hmt with ⟨h, -⟩ | ⟨-, h⟩ <;> [omega; exact h]
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.exists_mulEquiv_adjointGroup_of_isLabel_E8
    (lab := ⟨t, r, 1⟩) hlab ht hZ
  let eG : G ≃* adjointGroup .E8 (GaloisField 2 1) := Subgroup.topEquiv.symm.trans e
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by omega)]; norm_num
  have hE' : IsElemAbelian 3 (E.map eG.toMonoidHom) := TableB.isElemAbelian_map hE eG.toMonoidHom
  have hcard' : Nat.card (E.map eG.toMonoidHom) = 3 ^ 8 := by
    rw [Subgroup.card_map_of_injective eG.injective, hcard]
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E8 hGF hE' hcard'.ge
  have hE1 : E.map (eG.trans (MulAut.conj c⁻¹)).toMonoidHom =
      (TableBExcTwoTB.tE (GaloisField 2 1) TableBExcTwo.frameE8).range := by
    have h : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id (adjointGroup .E8 (GaloisField 2 1)) := by
      ext y
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
      group
    have h1 : (eG.trans (MulAut.conj c⁻¹)).toMonoidHom =
        (MulAut.conj c⁻¹).toMonoidHom.comp eG.toMonoidHom := rfl
    rw [h1, ← Subgroup.map_map, hc, Subgroup.map_map, h, Subgroup.map_id]
  obtain ⟨π, φ, hπs, hπk, hπi⟩ := tmStruct_concrete (τ := .E8) (d := 7) (K := GaloisField 2 1)
    (Or.inr rfl) TableBExcTwo.frameE8 rfl TableBExcTwoFusion.frameE8_reflections
    TableBExc.Three.cartan_symm_E8
    (TableBExc.isUnit_det_cartan_of_eq Nat.prime_three CFSG.StandardType.det_cartan_E8
      (by norm_num)) hGF (centralizer_tE_frameE8 hGF)
  exact tmStruct_transport (eG.trans (MulAut.conj c⁻¹)) hE1 (ExcWeylOuter.torusMulAut Tag.E8 3)
    π φ hπs hπk hπi

theorem tmStruct_card_E7
    (G : Type) [Group G] [Finite G] (hEm : IsEm 7 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 7) :
    Nat.card (Subgroup.normalizer (E : Set G)) = 3 ^ 7 * Nat.card (WeylGroup Tag.E7) := by
  obtain ⟨π, φ, hπs, hπk, -⟩ := tmStruct_E7 G hEm hsimple E hE hcard
  rw [tmStruct_card_of π hπs hπk, hcard]

theorem tmStruct_card_E8
    (G : Type) [Group G] [Finite G] (hEm : IsEm 8 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 8) :
    Nat.card (Subgroup.normalizer (E : Set G)) = 3 ^ 8 * Nat.card (WeylGroup Tag.E8) := by
  obtain ⟨π, φ, hπs, hπk, -⟩ := tmStruct_E8 G hEm hsimple E hE hcard
  rw [tmStruct_card_of π hπs hπk, hcard]

theorem tmStruct_cent_E7
    (G : Type) [Group G] [Finite G] (hEm : IsEm 7 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 7) :
    ∀ g ∈ Subgroup.normalizer (E : Set G), (∀ e ∈ E, g * e = e * g) → g ∈ E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π, φ, -, hπk, hπi⟩ := tmStruct_E7 G hEm hsimple E hE hcard
  intro g hg hc
  exact tmStruct_cent_of (ExcWeylOuter.torusMulAut Tag.E7 3)
    (ExcWeylOuter.torusMulAut_injective (by norm_num)) π φ hπk hπi g hg hc

theorem tmStruct_cent_E8
    (G : Type) [Group G] [Finite G] (hEm : IsEm 8 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 8) :
    ∀ g ∈ Subgroup.normalizer (E : Set G), (∀ e ∈ E, g * e = e * g) → g ∈ E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π, φ, -, hπk, hπi⟩ := tmStruct_E8 G hEm hsimple E hE hcard
  intro g hg hc
  exact tmStruct_cent_of (ExcWeylOuter.torusMulAut Tag.E8 3)
    (ExcWeylOuter.torusMulAut_injective (by norm_num)) π φ hπk hπi g hg hc

theorem tmStruct_irred_E7
    (G : Type) [Group G] [Finite G] (hEm : IsEm 7 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 7) :
    ∀ F : Subgroup G, F ≤ E →
      (∀ g ∈ Subgroup.normalizer (E : Set G), ∀ f ∈ F, g * f * g⁻¹ ∈ F) → F = ⊥ ∨ F = E := by
  obtain ⟨π, φ, hπs, -, hπi⟩ := tmStruct_E7 G hEm hsimple E hE hcard
  exact tmStruct_irred_of π φ hπs hπi (fun U hU => Irred937.latticeIrred_E7 (Or.inl rfl) U hU)

theorem tmStruct_irred_E8
    (G : Type) [Group G] [Finite G] (hEm : IsEm 8 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 8) :
    ∀ F : Subgroup G, F ≤ E →
      (∀ g ∈ Subgroup.normalizer (E : Set G), ∀ f ∈ F, g * f * g⁻¹ ∈ F) → F = ⊥ ∨ F = E := by
  obtain ⟨π, φ, hπs, -, hπi⟩ := tmStruct_E8 G hEm hsimple E hE hcard
  exact tmStruct_irred_of π φ hπs hπi (fun U hU => Irred937.latticeIrred_E8 (Or.inl rfl) U hU)

end CFSG.StandardType.FrameRoute

end
