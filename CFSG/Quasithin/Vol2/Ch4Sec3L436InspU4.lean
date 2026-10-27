module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspU4Model
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspNat
public import CFSG.Quasithin.Background.C48SporImg
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspL3
public import CFSG.Quasithin.H13.U4ParRecog

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.Ch4.U4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par

theorem img_perfectCore {G : Type} [Group G] [Finite G] {X P : Subgroup G}
    (N : Subgroup ↥X) [N.Normal] (hPX : P ≤ X) :
    C48Spor.img N (perfectCore P) = perfectCore (C48Spor.img N P) := by
  have hpc : (perfectCore P).subgroupOf X = perfectCore (P.subgroupOf X) := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le ((perfectCore_le P).trans hPX),
      map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPX]
  unfold C48Spor.img
  rw [hpc, map_perfectCore]

theorem imgHom_kernel_pGroup {G : Type} [Group G] {X Y : Subgroup G}
    (N : Subgroup ↥X) [N.Normal] (hYX : Y ≤ X) (hN : IsPGroup 2 ↥N) :
    IsPGroup 2 ↥(C48Spor.imgHom (N := N) hYX).ker := by
  let f := C48Spor.imgHom (N := N) hYX
  let η : ↥f.ker →* ↥N :=
    ((Subgroup.inclusion hYX).comp f.ker.subtype).codRestrict N
      (fun y => (C48Spor.mem_ker_imgHom hYX y.1).mp y.2)
  apply hN.of_injective η
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ↥N => ((z : ↥X) : G)) hab

noncomputable def modO2_equiv_of_mulEquiv {G H : Type} [Group G] [Group H]
    (A : Subgroup G) (B : Subgroup H) (e : ↥A ≃* ↥B) : ModO2 A ≃* ModO2 B :=
  QuotientGroup.congr _ _ e (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e)

private theorem mem_centerOf_of_mem_center {G : Type} [Group G] {K : Subgroup G}
    {x : ↥K} (hx : x ∈ Subgroup.center ↥K) : (x : G) ∈ centerOf K := by
  refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩)

theorem isPGroup_center {G : Type} [Group G] {K : Subgroup G}
    (hZ : IsPGroup 2 ↥(centerOf K)) : IsPGroup 2 ↥(Subgroup.center ↥K) := by
  let f : ↥(Subgroup.center ↥K) →* ↥(centerOf K) :=
    { toFun := fun x => ⟨((x : ↥K) : G), mem_centerOf_of_mem_center x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine hZ.of_injective f fun x y hxy => ?_
  have := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext this)

private theorem false_of_point_image {G : Type} [Group G] [Finite G]
    (K P V : Subgroup G) (m : ℕ) (hm : 2 ≤ m)
    (hZ : IsPGroup 2 ↥(centerOf K)) (hPK : P ≤ K)
    {F : Type} [Field F] (h : UnitaryFieldData 2 m F)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* hypSU h 2 0)
    (hP : (C48Spor.img (Subgroup.center ↥K) P).map e.toMonoidHom = parP h)
    (hnat : ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ m ∧
      IsNaturalSection (perfectCore P) V (V ⊓ centerOf K)
        (CFSG.pCore 2 ↥(perfectCore P)) (StatedSL 2 k))
    (hV : V ≤ CFSG.Open.pCoreOf 2 (perfectCore P) ⊓
      Subgroup.centralizer (CFSG.Open.pCoreOf 2 (perfectCore P) : Set G)) : False := by
  let N := Subgroup.center ↥K
  have hAK : perfectCore P ≤ K := (perfectCore_le P).trans hPK
  have hVK : V ≤ K := hV.trans (inf_le_left.trans
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hAK))
  have hk : IsPGroup 2 ↥(C48Spor.imgHom (N := N) hAK).ker :=
    imgHom_kernel_pGroup N hAK (isPGroup_center hZ)
  have hA : (C48Spor.img N (perfectCore P)).map e.toMonoidHom = perfectCore (parP h) := by
    rw [img_perfectCore N hPK, map_perfectCore, hP]
  have hO : (C48Spor.img N (CFSG.Open.pCoreOf 2 (perfectCore P))).map e.toMonoidHom =
      CFSG.Open.pCoreOf 2 (perfectCore (parP h)) := by
    rw [C48Spor.img_pCoreOf hAK hk, ← pCoreOf_map_of_inj e.injective, hA]
  have hW : (C48Spor.img N V).map e.toMonoidHom ≤
      centerOf (CFSG.Open.pCoreOf 2 (perfectCore (parP h))) := by
    have hVZ : V ≤ centerOf (CFSG.Open.pCoreOf 2 (perfectCore P)) := hV
    have hmap : C48Spor.img N V ≤
        centerOf (C48Spor.img N (CFSG.Open.pCoreOf 2 (perfectCore P))) :=
      (C48Spor.img_mono hVZ).trans C48Spor.img_centerOf_le
    have hmap' := Subgroup.map_mono (f := e.toMonoidHom) hmap
    rw [← centerOf_map_of_inj e.injective, hO] at hmap'
    exact hmap'
  obtain ⟨k, _, _, -, hnat⟩ := hnat
  apply G2A.false_of_natural_comm_inf hnat (le_refl (centerOf K))
  intro a ha v hv
  let aK : ↥K := ⟨a, hAK ha⟩
  let vK : ↥K := ⟨v, hVK hv⟩
  have ha' : e (aK : ↥K ⧸ N) ∈ perfectCore (parP h) := by
    rw [← hA]
    exact Subgroup.mem_map_of_mem _ (C48Spor.mem_img.mpr ⟨aK, ha, rfl⟩)
  have hv' : e (vK : ↥K ⧸ N) ∈
      centerOf (CFSG.Open.pCoreOf 2 (perfectCore (parP h))) :=
    hW (Subgroup.mem_map_of_mem _ (C48Spor.mem_img.mpr ⟨vK, hv, rfl⟩))
  have hc := Subgroup.mem_centralizer_iff.mp
    (point_core_centralizes_center_pCore h hm ha') _ hv'
  have hc' : (aK : ↥K ⧸ N) * (vK : ↥K ⧸ N) =
      (vK : ↥K ⧸ N) * (aK : ↥K ⧸ N) := by
    apply e.injective
    simpa only [map_mul] using hc.symm
  have hmk : ((aK * vK * aK⁻¹ * vK⁻¹ : ↥K) : ↥K ⧸ N) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hc']
    group
  have hmem : aK * vK * aK⁻¹ * vK⁻¹ ∈ N := by
    simpa only [QuotientGroup.eq_one_iff] using hmk
  exact mem_centerOf_of_mem_center hmem

theorem normalizer_map_of_ker_le {X Y : Type} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Surjective f) {S : Subgroup X} (hk : f.ker ≤ S) :
    (Subgroup.normalizer (S : Set X)).map f =
      Subgroup.normalizer (S.map f : Set Y) := by
  apply Subgroup.comap_injective hf
  rw [Subgroup.comap_map_eq_self (hk.trans Subgroup.le_normalizer),
    Subgroup.comap_normalizer_eq_of_surjective _ hf, Subgroup.comap_map_eq_self hk]

theorem exists_equiv_sylow {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e₀ : X ≃* Y) {U : Subgroup X} {S : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) (hS : IsSylowTwoOf S ⊤) :
    ∃ e : Y ≃* X, S.map e.toMonoidHom = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUi : ¬ 2 ∣ U.index := by
    have hi : (U.subgroupOf ⊤).index = U.index := Subgroup.relIndex_top_right U
    rw [← hi]
    exact hU.2.2
  have hSi : ¬ 2 ∣ S.index := by
    have hi : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
    rw [← hi]
    exact hS.2.2
  let U' : Sylow 2 Y := Sylow.mapSurjective (f := e₀.toMonoidHom) e₀.surjective (hU.2.1.toSylow hUi)
  let S' : Sylow 2 Y := hS.2.1.toSylow hSi
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y U' S'
  let e : X ≃* Y := e₀.trans (MulAut.conj y)
  have hUS : U.map e.toMonoidHom = S := by
    change U.map ((MulAut.conj y).toMonoidHom.comp e₀.toMonoidHom) = S
    rw [← Subgroup.map_map]
    change (MulAut.conj y) • (U.map e₀.toMonoidHom) = S
    change (MulAut.conj y) • (U' : Subgroup Y) = (S' : Subgroup Y)
    rw [← Sylow.coe_subgroup_smul, hy]
  refine ⟨e.symm, ?_⟩
  rw [← hUS, Subgroup.map_map]
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by
    ext x
    exact e.symm_apply_apply x
  rw [hcomp, Subgroup.map_id]

theorem maxParabolic_center_image {G : Type} [Group G] [Finite G]
    (K P : Subgroup G) (hP : IsMaxParabolic2 K P)
    (hZ : IsPGroup 2 ↥(centerOf K)) :
    ∃ S : Subgroup (↥K ⧸ Subgroup.center ↥K), IsSylowTwoOf S ⊤ ∧
      Subgroup.normalizer (S : Set (↥K ⧸ Subgroup.center ↥K)) ≤
        C48Spor.img (Subgroup.center ↥K) P ∧
      IsCoatom (C48Spor.img (Subgroup.center ↥K) P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P₀ := P.comap K.subtype
  have hP₀ : IsMaxParabolic2 (⊤ : Subgroup ↥K) P₀ :=
    L436.isMaxParabolic2_comap K.subtype K.subtype_injective K.range_subtype.symm hP
  obtain ⟨S, hS, hNS, hcov⟩ := Lie2Parabolic.exists_sylow_of_isMaxParabolic2 hP₀
  let q : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' _
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hSi : ¬ 2 ∣ S.index := by
    have hi : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
    rw [← hi]
    exact hS.2.2
  have hZS : Subgroup.center ↥K ≤ S :=
    (isPGroup_center hZ).le_sylow_of_normal (hS.2.1.toSylow hSi)
  have hkS : q.ker ≤ S := by simpa only [q, QuotientGroup.ker_mk'] using hZS
  have hkP : q.ker ≤ P₀ := hkS.trans (Subgroup.le_normalizer.trans hNS)
  have hImg : P₀.map q = C48Spor.img (Subgroup.center ↥K) P := rfl
  refine ⟨S.map q, L3M.isSylowTwoOf_map_top hS hq, ?_, ?_⟩
  · rw [← normalizer_map_of_ker_le q hq hkS, ← hImg]
    exact Subgroup.map_mono hNS
  · rw [← hImg]
    have hc : P₀.map q ⋖ ⊤ := by
      rw [← Subgroup.map_top_of_surjective q hq]
      exact CFSG.QuasithinUnique.Setup.X7a.covBy_map_of_ker_le hq hkP hcov
    refine ⟨hc.1.ne, ?_⟩
    intro Q hQ
    by_contra hQt
    exact hc.2 hQ (lt_top_iff_ne_top.mpr hQt)


theorem exists_unitary4_parabolic {G : Type} [Group G] [Finite G]
    (K P : Subgroup G) (m : ℕ)
    (hU : IsPSU 4 2 m (↥K ⧸ Subgroup.center ↥K))
    (hP : IsMaxParabolic2 K P) (hZ : IsPGroup 2 ↥(centerOf K)) :
    ∃ (F : Type) (_ : Field F) (h : UnitaryFieldData 2 m F),
      ∃ e : (↥K ⧸ Subgroup.center ↥K) ≃* hypSU h 2 0,
        (C48Spor.img (Subgroup.center ↥K) P).map e.toMonoidHom = parP h ∨
        (C48Spor.img (Subgroup.center ↥K) P).map e.toMonoidHom = parP2 h := by
  obtain ⟨F, _, h, ⟨e₀⟩⟩ := exists_hypSU_equiv_of_lieModel
    (Or.inl ⟨by decide, hU⟩)
  have := h.finite
  have := CFSG.ClassicalGroups.UnitaryFlag.finite_hypSU h (r := 2) (ε := 0)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hNS, hco⟩ := maxParabolic_center_image K P hP hZ
  obtain ⟨U, hU⟩ := (unitary_order_and_Sylow (r := 2) (ε := 0) h
    (by norm_num) (by norm_num)).2.1
  have hUs : IsSylowTwoOf (hypUnitriangular h 2 0) ⊤ := by
    rw [← hU]
    refine ⟨le_top, U.isPGroup', ?_⟩
    have hi : ((U : Subgroup (hypSU h 2 0)).subgroupOf ⊤).index =
        (U : Subgroup (hypSU h 2 0)).index := Subgroup.relIndex_top_right _
    rw [hi]
    exact U.not_dvd_index
  obtain ⟨e, he⟩ := exists_equiv_sylow e₀ hUs hS
  refine ⟨F, inferInstance, h, e, ?_⟩
  apply eq_parP_or_eq_parP2
  · have hc : ((C48Spor.img (Subgroup.center ↥K) P).map e.toMonoidHom) ⋖ ⊤ := by
      rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
      exact CFSG.QuasithinUnique.Setup.X7a.covBy_map_of_ker_le e.surjective
        (by
          intro x hx
          have hx' : e x = 1 := hx
          have hx1 : x = 1 := e.injective (hx'.trans e.map_one.symm)
          simpa only [hx1] using (C48Spor.img (Subgroup.center ↥K) P).one_mem) (by
          refine ⟨lt_top_iff_ne_top.mpr hco.1, ?_⟩
          intro A hPA hAt
          exact hAt.ne (hco.2 A hPA))
    refine ⟨hc.1.ne, ?_⟩
    intro A hA
    by_contra hAt
    exact hc.2 hA (lt_top_iff_ne_top.mpr hAt)
  · rw [← UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num),
      ← he, ← Subgroup.map_normalizer_eq_of_bijective S e.bijective]
    exact Subgroup.map_mono hNS


noncomputable def modO2_perfectCore_center_image {G H : Type} [Group G] [Finite G]
    [Group H] [Finite H] (K P : Subgroup G) (Q : Subgroup H)
    (hPK : P ≤ K) (hZ : IsPGroup 2 ↥(centerOf K))
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* H)
    (hP : (C48Spor.img (Subgroup.center ↥K) P).map e.toMonoidHom = Q) :
    ModO2 (perfectCore P) ≃* ModO2 (perfectCore Q) := by
  have hAK : perfectCore P ≤ K := (perfectCore_le P).trans hPK
  have hk : IsPGroup 2 ↥(C48Spor.imgHom (N := Subgroup.center ↥K) hAK).ker :=
    imgHom_kernel_pGroup _ hAK (isPGroup_center hZ)
  have hA : (C48Spor.img (Subgroup.center ↥K) (perfectCore P)).map e.toMonoidHom =
      perfectCore Q := by
    rw [img_perfectCore _ hPK, map_perfectCore, hP]
  exact (C48Spor.modO2Equiv hAK hk).trans
    (modO2_equiv_of_mulEquiv _ _
      (((C48Spor.img (Subgroup.center ↥K) (perfectCore P)).equivMapOfInjective
        e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hA)))

theorem false_of_isPSU4_natural {G : Type} [Group G] [Finite G]
    (K P V : Subgroup G) (m : ℕ) (hm : 2 ≤ m)
    (hZ : IsPGroup 2 ↥(centerOf K))
    (hU : IsPSU 4 2 m (↥K ⧸ Subgroup.center ↥K))
    (hP : IsMaxParabolic2 K P)
    (hpsl : IsPSL 2 2 m (ModO2 (perfectCore P)))
    (hnat : ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ m ∧
      IsNaturalSection (perfectCore P) V (V ⊓ centerOf K)
        (CFSG.pCore 2 ↥(perfectCore P)) (StatedSL 2 k))
    (hV : V ≤ CFSG.Open.pCoreOf 2 (perfectCore P) ⊓
      Subgroup.centralizer (CFSG.Open.pCoreOf 2 (perfectCore P) : Set G)) : False := by
  obtain ⟨F, _, h, e, hQ | hQ⟩ := exists_unitary4_parabolic K P m hU hP hZ
  · exact false_of_point_image K P V m hm hZ hP.1.1 h e hQ hnat hV
  · let δ := modO2_perfectCore_center_image K P (parP2 h) hP.1.1 hZ e hQ
    apply not_psl2_modO2_line h hm
    obtain ⟨ha, k, _, _, hk, ⟨e₁⟩⟩ := hpsl
    exact ⟨ha, k, inferInstance, inferInstance, hk, ⟨δ.symm.trans e₁⟩⟩


end CFSG.Quasithin.H13.Ch4.U4A
