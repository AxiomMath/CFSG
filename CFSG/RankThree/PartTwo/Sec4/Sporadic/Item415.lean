module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2UT
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Subgroup CFSG.Blueprint
  CFSG.RankThree.Asc83Table
open scoped commutatorElement Pointwise

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem inSubgroup_pCore_map (φ : G ≃* G') (H : Subgroup G) :
    (inSubgroup (CFSG.pCore 2) H).map φ.toMonoidHom =
      inSubgroup (CFSG.pCore 2) (H.map φ.toMonoidHom) := by
  rw [inSubgroup, inSubgroup,
    ← CFSG.pCore_map_iso 2 (H.equivMapOfInjective φ.toMonoidHom φ.injective), Subgroup.map_map,
    Subgroup.map_map]
  rfl

theorem map_centralizer_singleton (φ : G ≃* G') (a : G) :
    (centralizer ({a} : Set G)).map φ.toMonoidHom = centralizer ({φ a} : Set G') := by
  ext y
  simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply, hy]

theorem zpowers_map (φ : G ≃* G') (a : G) :
    zpowers (φ a) = (zpowers a).map φ.toMonoidHom :=
  (MonoidHom.map_zpowers φ.toMonoidHom a).symm

theorem normalizer_zpowers_map (φ : G ≃* G') (a : G) :
    normalizer ((zpowers (φ a) : Subgroup G') : Set G') =
      (normalizer ((zpowers a : Subgroup G) : Set G)).map φ.toMonoidHom := by
  rw [zpowers_map]
  exact (map_equiv_normalizer_eq _ φ).symm

noncomputable def quotNormalizerCongr (φ : G ≃* G') (H : Subgroup G) :
    normalizer (H : Set G) ⧸ H.subgroupOf (normalizer (H : Set G)) ≃*
      normalizer ((H.map φ.toMonoidHom : Subgroup G') : Set G') ⧸
        (H.map φ.toMonoidHom).subgroupOf
          (normalizer ((H.map φ.toMonoidHom : Subgroup G') : Set G')) :=
  QuotientGroup.congr _ _ (((normalizer (H : Set G)).equivMapOfInjective φ.toMonoidHom
    φ.injective).trans (MulEquiv.subgroupCongr (map_equiv_normalizer_eq H φ))) (by
      ext ⟨x, hx⟩
      simp only [mem_map, mem_subgroupOf]
      constructor
      · rintro ⟨⟨y, hyN⟩, hy, hyx⟩
        have : φ y = x := congrArg Subtype.val hyx
        exact ⟨y, hy, this⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, le_normalizer hy⟩, hy, rfl⟩)

@[expose] def PtA (a : G) : Prop :=
  Nonempty (normalizer ((zpowers a : Subgroup G) : Set G) ≃*
    Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) ∧
  inSubgroup (CFSG.pCore 2) (normalizer (inSubgroup (CFSG.pCore 2)
      (normalizer ((zpowers a : Subgroup G) : Set G)) : Set G)) =
    inSubgroup (CFSG.pCore 2) (normalizer ((zpowers a : Subgroup G) : Set G)) ∧
  (inSubgroup (CFSG.pCore 2) (normalizer ((zpowers a : Subgroup G) : Set G))).map
      (MulAut.conj : G →* MulAut G) ∈
    maxInvariantPiSubgroups
      (normalizer ((zpowers (MulAut.conj a) : Subgroup (MulAut G)) : Set (MulAut G)))
      ((normalizer ((zpowers a : Subgroup G) : Set G)).map (MulAut.conj : G →* MulAut G))
      (piOf 2)

theorem PtA.map (φ : G ≃* G') {a : G} (h : PtA a) : PtA (φ a) := by
  obtain ⟨⟨e⟩, h2, h3⟩ := h
  set N := normalizer ((zpowers a : Subgroup G) : Set G)
  have hN := normalizer_zpowers_map φ a
  refine ⟨⟨(MulEquiv.subgroupCongr hN).trans
    ((N.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans e)⟩, ?_, ?_⟩
  · rw [hN, ← inSubgroup_pCore_map, ← map_equiv_normalizer_eq, ← inSubgroup_pCore_map, h2]
  · set ψ := MulAut.congr φ
    have hmem := Set.mem_image_of_mem (fun X : Subgroup (MulAut G) => X.map ψ.toMonoidHom) h3
    rw [image_maxInvariantPiSubgroups] at hmem
    have eX : ((inSubgroup (CFSG.pCore 2) N).map (MulAut.conj : G →* MulAut G)).map
        ψ.toMonoidHom = (inSubgroup (CFSG.pCore 2) (normalizer
          ((zpowers (φ a) : Subgroup G') : Set G'))).map (MulAut.conj : G' →* MulAut G') := by
      rw [← map_map_conj, inSubgroup_pCore_map, ← hN]
    have eA : (N.map (MulAut.conj : G →* MulAut G)).map ψ.toMonoidHom =
        (normalizer ((zpowers (φ a) : Subgroup G') : Set G')).map
          (MulAut.conj : G' →* MulAut G') := by
      rw [← map_map_conj, ← hN]
    have eH : (normalizer ((zpowers (MulAut.conj a) : Subgroup (MulAut G)) :
        Set (MulAut G))).map ψ.toMonoidHom = normalizer ((zpowers (MulAut.conj (φ a)) :
          Subgroup (MulAut G')) : Set (MulAut G')) := by
      rw [map_equiv_normalizer_eq, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
        CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
    rw [eX, eA, eH] at hmem
    exact hmem

theorem PtA.of_zpowers_eq {a b : G} (h : zpowers a = zpowers b) (ha : PtA a) : PtA b := by
  have hc : zpowers (MulAut.conj a) = zpowers (MulAut.conj b) := by
    rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, h]
  unfold PtA at ha ⊢
  rw [h, hc] at ha
  exact ha

@[expose] def Pt4 (P A : Subgroup G) : Prop :=
  ∀ a ∈ A, a ∉ P ⊓ centralizer (P : Set G) →
    Nonempty (autIn ⊤ A ≃* Equiv.Perm (Fin 3)) ∧ PtA a

theorem Pt4.map (φ : G ≃* G') {P A : Subgroup G} (h : Pt4 P A) :
    Pt4 (P.map φ.toMonoidHom) (A.map φ.toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ hZ
  have hZ' : a ∉ P ⊓ centralizer (P : Set G) := fun h' => hZ (by
    rw [← map_inf_centralizer]
    exact mem_map_of_mem _ h')
  obtain ⟨⟨e⟩, hA⟩ := h a ha hZ'
  exact ⟨⟨(autInTopCongr φ A).symm.trans e⟩, hA.map φ⟩

@[expose] def Pt5 (P A : Subgroup G) : Prop :=
  ∃ S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2),
    maxInvariantPiSubgroups ⊤ A (piOf 2) = (conjugate S) '' (P : Set G) ∧
    (maxInvariantPiSubgroups ⊤ A (piOf 2)).ncard = 3 ∧
    (∃ T : Sylow 2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)),
      Nonempty (S ≃* (T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))))) ∧
    ∃ a b : G, closure {a, b} = A ∧
      ((S ⊓ centralizer ((P ⊓ centralizer (P : Set G) : Subgroup G) : Set G) : Subgroup G) :
          Set G) *
        (inSubgroup (CFSG.pCore 2) (centralizer {a}) : Set G) *
        (inSubgroup (CFSG.pCore 2) (centralizer {b}) : Set G) = S

theorem Pt5.map (φ : G ≃* G') {P A : Subgroup G} (h : Pt5 P A) :
    Pt5 (P.map φ.toMonoidHom) (A.map φ.toMonoidHom) := by
  obtain ⟨S, hS, hset, hcard, ⟨T, ⟨eT⟩⟩, a, b, hab, hprod⟩ := h
  have hI : maxInvariantPiSubgroups ⊤ (A.map φ.toMonoidHom) (piOf 2) =
      (fun X => X.map φ.toMonoidHom) '' maxInvariantPiSubgroups ⊤ A (piOf 2) := by
    rw [image_maxInvariantPiSubgroups, Subgroup.map_top_of_surjective _ φ.surjective]
  refine ⟨S.map φ.toMonoidHom, ?_, ?_, ?_,
    ⟨T, ⟨(S.equivMapOfInjective _ φ.injective).symm.trans eT⟩⟩, φ a, φ b, ?_, ?_⟩
  · rw [hI]
    exact Set.mem_image_of_mem _ hS
  · rw [hI, hset, Set.image_image, Subgroup.coe_map, Set.image_image]
    exact Set.image_congr fun g _ => conjugate_map φ S g
  · rw [hI, Set.ncard_image_of_injective _ (Subgroup.map_injective φ.injective), hcard]
  · rw [← hab, MonoidHom.map_closure, Set.image_pair, MulEquiv.coe_toMonoidHom]
  · have h1 : (S ⊓ centralizer ((P ⊓ centralizer (P : Set G) : Subgroup G) : Set G)).map
          φ.toMonoidHom = S.map φ.toMonoidHom ⊓ centralizer
            ((P.map φ.toMonoidHom ⊓ centralizer (P.map φ.toMonoidHom : Set G') :
              Subgroup G') : Set G') := by
      rw [Subgroup.map_inf _ _ _ φ.injective, map_equiv_centralizer_eq, map_inf_centralizer]
    have h2 : ∀ c : G, (inSubgroup (CFSG.pCore 2) (centralizer ({c} : Set G))).map
        φ.toMonoidHom = inSubgroup (CFSG.pCore 2) (centralizer ({φ c} : Set G')) := fun c => by
      rw [inSubgroup_pCore_map, map_centralizer_singleton]
    have := congrArg (fun s : Set G => (φ.toMonoidHom : G → G') '' s) hprod
    simp only [Set.image_mul, ← Subgroup.coe_map, h1, h2] at this
    exact this

@[expose] def Pt123 (P : Subgroup G) : Prop :=
  (IsHeisThree P ∧
    Nonempty (normalizer (P : Set G) ⧸ P.subgroupOf (normalizer (P : Set G)) ≃*
      Multiplicative (ZMod 8))) ∧
  (∀ B ∈ {B : Subgroup G | B ≤ P ∧ Nat.card B = 9},
    ∀ B' ∈ {B : Subgroup G | B ≤ P ∧ Nat.card B = 9},
      ∃ x ∈ normalizer (P : Set G), B' = conjugate B x) ∧
  ∀ Z : Subgroup G, Z = P ⊓ centralizer (P : Set G) →
    ((∀ g : G, conjugate Z g ≤ P → conjugate Z g = Z) ∧
      IsExtOf (centralizer (Z : Set G)) (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∧
      Nonempty (normalizer (Z : Set G) ⧸ Z.subgroupOf (normalizer (Z : Set G)) ≃*
        Matrix.ProjGenLinGroup (Fin 2) (GaloisField 3 2)))

theorem mem_nine_map (φ : G ≃* G') {P : Subgroup G} {C : Subgroup G'}
    (hC : C ∈ {B : Subgroup G' | B ≤ P.map φ.toMonoidHom ∧ Nat.card B = 9}) :
    C.map φ.symm.toMonoidHom ∈ {B : Subgroup G | B ≤ P ∧ Nat.card B = 9} := by
  obtain ⟨hCP, h9⟩ := hC
  refine ⟨?_, by rw [Subgroup.card_map_of_injective φ.symm.injective, h9]⟩
  have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hCP
  rwa [map_symm_map] at this

theorem Pt123.map (φ : G ≃* G') {P : Subgroup G} (h : Pt123 P) :
    Pt123 (P.map φ.toMonoidHom) := by
  obtain ⟨⟨hH, ⟨eQ⟩⟩, h2, h3⟩ := h
  obtain ⟨hw, hext, ⟨eZ⟩⟩ := h3 _ rfl
  set e := P.equivMapOfInjective φ.toMonoidHom φ.injective
  refine ⟨⟨⟨CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv e hH.1,
    by rw [← Nat.card_congr e.toEquiv]; exact hH.2.1,
    by rw [← Monoid.exponent_eq_of_mulEquiv e]; exact hH.2.2⟩,
    ⟨(quotNormalizerCongr φ P).symm.trans eQ⟩⟩, ?_, ?_⟩
  · intro B hB B' hB'
    obtain ⟨x, hx, hxB⟩ := h2 _ (mem_nine_map φ hB) _ (mem_nine_map φ hB')
    refine ⟨φ x, ?_, ?_⟩
    · rw [← map_equiv_normalizer_eq]
      exact mem_map_of_mem _ hx
    · have := congrArg (fun C : Subgroup G => C.map φ.toMonoidHom) hxB
      simp only [map_map_symm, conjugate_map] at this
      exact this
  · intro Z' hZ'
    rw [← map_inf_centralizer] at hZ'
    subst hZ'
    refine ⟨fun g hg => ?_, ?_,
      ⟨(quotNormalizerCongr φ (P ⊓ centralizer (P : Set G))).symm.trans eZ⟩⟩
    · have hg' : conjugate (P ⊓ centralizer (P : Set G)) (φ.symm g) ≤ P := by
        rw [← Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective,
          conjugate_map, φ.apply_symm_apply]
        exact hg
      have := congrArg (fun C : Subgroup G => C.map φ.toMonoidHom) (hw _ hg')
      simp only [conjugate_map, φ.apply_symm_apply] at this
      exact this
    · rw [← map_equiv_centralizer_eq]
      exact isExtOf_of_mulEquiv ((centralizer ((P ⊓ centralizer (P : Set G) : Subgroup G) :
        Set G)).equivMapOfInjective φ.toMonoidHom φ.injective).symm hext

end Transport

theorem forall_sylow_of_P3 (Q : ∀ (G : Type) [Group G], Subgroup G → Prop)
    (hQ : ∀ (G G' : Type) [Group G] [Group G'] (φ : G ≃* G') (P : Subgroup G),
      Q G P → Q G' (P.map φ.toMonoidHom))
    (h0 : Q GJ P3) (G : Type) [Group G] (h : Nonempty (G ≃* NativeSporadic.J2))
    (P : Sylow 3 G) : Q G P := by
  obtain ⟨e0⟩ := h
  set e : G ≃* GJ := e0.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card G = 604800 := (Nat.card_congr e.toEquiv).trans card_GJ
  have hP0 : Nat.card (P3.map e.symm.toMonoidHom) = 3 ^ (Nat.card G).factorization 3 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, card_P3, hcard,
      factorization_eq_of_eq Nat.prime_three (show 604800 = 3 ^ 3 * 22400 by norm_num)
        (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := exists_sylow_eq_map hP0 P
  rw [hg, Subgroup.map_map]
  exact hQ _ _ (e.symm.trans (MulAut.conj g)) _ h0

theorem pt123_P3 : Pt123 P3 := by
  refine ⟨⟨isHeisThree_P3, quotient_normalizer_P3⟩, delta_transitive, fun Z hZ => ?_⟩
  rw [inf_centralizer_P3, ← z_eq] at hZ
  subst hZ
  exact ⟨weaklyClosed, isExtOf_centralizer, quotient_normalizer_Z⟩

theorem ptA_x : PtA xJ := by
  refine ⟨normalizer_x_equiv, ?_, ?_⟩
  · rw [pCore_normalizer_x]
    exact pCore_normalizer_V
  · rw [pCore_normalizer_x]
    exact V_mem_maxInvariant

theorem ptA_a (k : Fin 3) : PtA (aJ k) := by
  have h := ptA_x.map (MulAut.conj (cJ k))
  rwa [MulAut.conj_apply, (c_spec k).2] at h

theorem orderOf_eq_three {g : GJ} (hg : g ∈ E0) (hg1 : g ≠ 1) : orderOf g = 3 :=
  orderOf_eq_prime (cube_of_mem_P3 (E0_le_P3 hg)) hg1

theorem aJ_ne_one (k : Fin 3) : aJ k ≠ 1 := by
  intro h
  have h' : xJ = 1 := by
    have := conj_c_a k
    rw [h, mul_one, inv_mul_cancel] at this
    exact this.symm
  exact xJ_ne_one h'

theorem zpowers_eq_a {a : GJ} (ha : a ∈ E0) (hz : a ∉ zpowers zJ) :
    ∃ k : Fin 3, zpowers a = zpowers (aJ k) := by
  have ha1 : a ≠ 1 := fun h => hz (h ▸ one_mem _)
  have hcard : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers, orderOf_eq_three ha ha1]
  rcases E0_elt_pow ha ha1 with ⟨n, hn⟩ | ⟨k, n, hn⟩
  · exfalso
    apply hz
    have hle : zpowers zJ ≤ zpowers a := by
      rw [zpowers_le, ← hn]
      exact pow_mem (mem_zpowers a) n
    have heq : zpowers zJ = zpowers a := Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by
      rw [hcard, card_zpowers_z]))
    rw [heq]
    exact mem_zpowers a
  · refine ⟨k, (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm⟩
    · rw [zpowers_le, ← hn]
      exact pow_mem (mem_zpowers a) n
    · exact le_of_eq (by
        rw [hcard, Nat.card_zpowers, orderOf_eq_three (aJ_mem_E0 k) (aJ_ne_one k)])

theorem pt4_E0 : Pt4 P3 E0 := by
  intro a ha hZ
  rw [inf_centralizer_P3, ← z_eq] at hZ
  obtain ⟨k, hk⟩ := zpowers_eq_a ha hZ
  exact ⟨autIn_E0, (ptA_a k).of_zpowers_eq hk.symm⟩

theorem pt5_E0 : Pt5 P3 E0 := sig5_E0

theorem conjugate_P3 {n : GJ} (hn : n ∈ normalizer ((P3 : Subgroup GJ) : Set GJ)) :
    P3.map (MulAut.conj n⁻¹).toMonoidHom = P3 := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨p, hp, rfl⟩
    have := (mem_normalizer_iff.mp (inv_mem hn) p).mp hp
    simpa using this
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]

theorem pt45_P3 {A : Subgroup GJ} (hA : A ∈ {B : Subgroup GJ | B ≤ P3 ∧ Nat.card B = 9}) :
    Pt4 P3 A ∧ Pt5 P3 A := by
  have hE : E0 ∈ {B : Subgroup GJ | B ≤ P3 ∧ Nat.card B = 9} :=
    ⟨E0_le_P3, (ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 0).card⟩
  obtain ⟨n, hn, hnA⟩ := delta_transitive E0 hE A hA
  have hP : P3.map (MulAut.conj n⁻¹).toMonoidHom = P3 := conjugate_P3 hn
  have hA' : E0.map (MulAut.conj n⁻¹).toMonoidHom = A := hnA.symm
  have h4 := pt4_E0.map (MulAut.conj n⁻¹)
  have h5 := pt5_E0.map (MulAut.conj n⁻¹)
  rw [hP, hA'] at h4 h5
  exact ⟨h4, h5⟩

theorem pt45_map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') {P : Subgroup G}
    (h : ∀ A ∈ {B : Subgroup G | B ≤ P ∧ Nat.card B = 9}, Pt4 P A ∧ Pt5 P A) :
    ∀ A ∈ {B : Subgroup G' | B ≤ P.map φ.toMonoidHom ∧ Nat.card B = 9},
      Pt4 (P.map φ.toMonoidHom) A ∧ Pt5 (P.map φ.toMonoidHom) A := by
  intro A hA
  obtain ⟨h4, h5⟩ := h _ (mem_nine_map φ hA)
  have e : (A.map φ.symm.toMonoidHom).map φ.toMonoidHom = A := map_map_symm φ A
  exact ⟨e ▸ h4.map φ, e ▸ h5.map φ⟩

end CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

theorem rank3II_4_15 : Item4_15 := by
  intro G _ _ h P Z hZ Δ hΔ
  subst hZ hΔ
  have h123 := forall_sylow_of_P3 (fun _ _ P => Pt123 P) (fun _ _ _ _ φ _ hP => hP.map φ)
    pt123_P3 G h P
  have h45 := forall_sylow_of_P3
    (fun G _ P => ∀ A ∈ {B : Subgroup G | B ≤ P ∧ Nat.card B = 9}, Pt4 P A ∧ Pt5 P A)
    (fun _ _ _ _ φ _ hP => pt45_map φ hP) (fun _ hA => pt45_P3 hA) G h P
  obtain ⟨h1, h2, h3⟩ := h123
  exact ⟨h1, h2, h3 _ rfl, fun A hA => (h45 A hA).1, fun A hA => (h45 A hA).2⟩

end CFSG.RankThree.PartTwo.Sec4.Sporadic
