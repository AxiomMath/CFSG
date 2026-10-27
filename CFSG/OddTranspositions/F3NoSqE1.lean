module

public import CFSG.OddTranspositions.ClassificationStatement
public import CFSG.OddTranspositions.UPQHyp
public import CFSG.OddTranspositions.SymNoSqE1
public import CFSG.LargeExtraspecial.S12InspFamER3b

public section

namespace CFSG.OddTranspositions

open CFSG.Blueprint.Fischer
open CFSG.Fischer.Classification
open CFSG.Fischer.Classification.F3
open CFSG.Fischer.Classification.Recognition
open CFSG.Fischer.Classification.Unitary
open CFSG.RankThree.GF2n.Tim79a
open CFSG.Open
open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem pCore_sup_map_subtype_le_of_normal_of_isPGroup_inf {G : Type*} [Group G]
    (L Z : Subgroup G)
    (hZnorm : (Z.subgroupOf (Z ⊔ L)).Normal)
    (hker2 : IsPGroup 2 (Z.subgroupOf L))
    (hpL : CFSG.pCore 2 L ≤ Z.subgroupOf L) :
    (CFSG.pCore 2 (Z ⊔ L : Subgroup G)).map (Z ⊔ L : Subgroup G).subtype ≤ Z := by
  classical
  let K : Subgroup G := Z ⊔ L
  have hZK : Z ≤ K := le_sup_left
  have hLK : L ≤ K := le_sup_right
  have hZnormK : (Z.subgroupOf K).Normal := by simpa [K] using hZnorm
  haveI : (Z.subgroupOf K).Normal := hZnormK
  let π : K →* K ⧸ Z.subgroupOf K := QuotientGroup.mk' _
  let ψ : L →* K ⧸ Z.subgroupOf K :=
    (QuotientGroup.mk' (Z.subgroupOf K)).comp (Subgroup.inclusion hLK)
  have hψ_ker : ψ.ker = Z.subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk (⟨(l : G), hLK l.2⟩ : K) : K ⧸ Z.subgroupOf K) = 1 ↔
      l ∈ Z.subgroupOf L
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have hψ_surj : Function.Surjective ψ := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have htop : (Z.subgroupOf K) ⊔ (L.subgroupOf K) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hZK hLK, Subgroup.subgroupOf_self]
    have hset : ((⊤ : Subgroup K) : Set K) =
        (Z.subgroupOf K : Set K) * (L.subgroupOf K : Set K) := by
      rw [← htop, Subgroup.normal_mul]
    have hk : k ∈ (Z.subgroupOf K : Set K) * (L.subgroupOf K : Set K) := by
      rw [← hset]
      trivial
    obtain ⟨z, hz, l, hl, hk_eq⟩ := hk
    refine ⟨⟨l, Subgroup.mem_subgroupOf.mp hl⟩, ?_⟩
    have hz1 : (QuotientGroup.mk z : K ⧸ Z.subgroupOf K) = 1 :=
      (QuotientGroup.eq_one_iff z).mpr hz
    have hkl : (QuotientGroup.mk k : K ⧸ Z.subgroupOf K) =
        QuotientGroup.mk z * QuotientGroup.mk l := by
      rw [← hk_eq]
      rfl
    rw [hkl, hz1, one_mul]
    rfl
  have hPnorm : ((CFSG.pCore 2 K).map π).Normal :=
    Subgroup.Normal.map CFSG.pCore_normal π (QuotientGroup.mk'_surjective _)
  have hP2 : IsPGroup 2 ((CFSG.pCore 2 K).map π) :=
    CFSG.pCore_isPGroup.map π
  have hpre2 : IsPGroup 2 (((CFSG.pCore 2 K).map π).comap ψ) :=
    hP2.comap_of_ker_isPGroup ψ (by rw [hψ_ker]; exact hker2)
  have hpre_norm : (((CFSG.pCore 2 K).map π).comap ψ).Normal := hPnorm.comap ψ
  have hpre_le : (((CFSG.pCore 2 K).map π).comap ψ) ≤ CFSG.pCore 2 L :=
    le_sSup ⟨hpre_norm, hpre2⟩
  have hcore_le : CFSG.pCore 2 K ≤ Z.subgroupOf K := by
    intro x hx
    have hxP : π x ∈ (CFSG.pCore 2 K).map π := Subgroup.mem_map_of_mem π hx
    obtain ⟨l, hl⟩ := hψ_surj (π x)
    have hlpre : l ∈ ((CFSG.pCore 2 K).map π).comap ψ := by
      rw [Subgroup.mem_comap, hl]
      exact hxP
    have hlcore : l ∈ CFSG.pCore 2 L := hpre_le hlpre
    have hmap : (CFSG.pCore 2 L).map ψ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hψ_ker]
      exact hpL
    have hzero : ψ l = 1 := by
      have hmem : ψ l ∈ (CFSG.pCore 2 L).map ψ := Subgroup.mem_map_of_mem ψ hlcore
      rw [hmap] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hπx : π x = 1 := by rw [← hl, hzero]
    exact (QuotientGroup.eq_one_iff x).mp hπx
  have hmap := Subgroup.map_mono (f := K.subtype) hcore_le
  rw [Subgroup.map_subgroupOf_eq_of_le hZK] at hmap
  exact hmap

theorem pCore_localGroup_R3_le {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hf : IsF3Form f) (hm5 : 5 ≤ m) (h36 : m = 5 → (D3 f).ncard = 36)
    {v : Fin m → ZMod 3} (hv : f v v = 1) :
    (CFSG.pCore 2 (LocalGroup (D3 f) (reflBar f v))).map
        (LocalGroup (D3 f) (reflBar f v)).subtype ≤ Subgroup.zpowers (reflBar f v) := by
  classical
  have hm4 : 4 ≤ m := by omega
  set L : Subgroup (R3 f) := LocalGroup (D3 f) (reflBar f v) with hL
  set Z : Subgroup (R3 f) := Subgroup.zpowers (reflBar f v) with hZ
  let Q := LocalQuotient (D3 f) (reflBar f v)
  obtain ⟨f', hf', ⟨e, he⟩, Φ, hΦimg⟩ :=
    CFSG.Fischer.Classification.exists_localQuotient_equiv hf hm4 hv
  have hiso' : CFSG.LargeExtraspecial.S12InspF3.HIso f' := by
    rcases Nat.lt_or_ge m 6 with hm6 | hm6
    · obtain rfl : m = 5 := by omega
      exact CFSG.LargeExtraspecial.S12InspF3.hIso_of_four hf'
        (CFSG.LargeExtraspecial.S12InspF3.ncard_D3_local_eq_fifteen hf hv (h36 rfl) hf' he)
    · intro a b ha hb hab
      exact F3.exists_isotropic_perp_two hf' (by omega) ha hb hab
  have hpcR3 : CFSG.pCore 2 (R3 f') = ⊥ :=
    CFSG.LargeExtraspecial.S12InspF3.normal_two_eq_bot hf' (by omega) hiso'
      (N := CFSG.pCore 2 (R3 f')) CFSG.pCore_normal CFSG.pCore_isPGroup
  have hpcQ : CFSG.pCore 2 Q = ⊥ := by
    have hmap : (CFSG.pCore 2 Q).map Φ.toMonoidHom = CFSG.pCore 2 (R3 f') :=
      CFSG.pCore_map_iso 2 Φ
    rw [hpcR3] at hmap
    have hle : CFSG.pCore 2 Q ≤ Φ.toMonoidHom.ker :=
      (Subgroup.map_eq_bot_iff _).mp hmap
    have hker : Φ.toMonoidHom.ker = ⊥ := by
      rw [MonoidHom.ker_eq_bot_iff]
      exact Φ.injective
    rw [hker] at hle
    exact le_bot_iff.mp hle
  have hpcL_center : CFSG.pCore 2 L ≤ Subgroup.center L := by
    let π : L →* Q := QuotientGroup.mk' (Subgroup.center L)
    have hmap : (CFSG.pCore 2 L).map π ≤ CFSG.pCore 2 Q :=
      le_sSup ⟨Subgroup.Normal.map CFSG.pCore_normal π (QuotientGroup.mk'_surjective _),
        CFSG.pCore_isPGroup.map π⟩
    rw [hpcQ] at hmap
    have hbot : (CFSG.pCore 2 L).map π = ⊥ := le_bot_iff.mp hmap
    have hle : CFSG.pCore 2 L ≤ π.ker := (Subgroup.map_eq_bot_iff _).mp hbot
    change CFSG.pCore 2 L ≤ (QuotientGroup.mk' (Subgroup.center L)).ker at hle
    rwa [QuotientGroup.ker_mk'] at hle
  have hP_R3 : Pair (R3 f) (D3 f) := pair_R3 hf hm4
  have hZ_R3 : Subgroup.center (R3 f) = ⊥ := center_R3_eq_bot hf hm4
  have hS_R3 : IsSimpleGroup (commutator (R3 f)) :=
    CFSG.LargeExtraspecial.r3SimpleInput m f hf hm4 (fun h4 => by omega)
  have hna_R3 : ∃ a b : commutator (R3 f), a * b ≠ b * a :=
    CFSG.Fischer.Classification.Recognition.R3.nonabelian_commutator_R3 hf hm5 hS_R3
  have hcenterL : (Subgroup.center L).map L.subtype ≤ Z :=
    Pair.center_localGroup_le hP_R3 hZ_R3 hS_R3 hna_R3 (tripleProperty_D3 hf hm5)
      (reflBar_mem_D3 hv)
  calc (CFSG.pCore 2 L).map L.subtype
      ≤ (Subgroup.center L).map L.subtype := Subgroup.map_mono hpcL_center
    _ ≤ Z := hcenterL

theorem noSqE1_R3 {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hf : IsF3Form f) (hm : 5 ≤ m) (h36 : m = 5 → (D3 f).ncard = 36) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 (D3 f) := by
  classical
  intro d hd
  obtain ⟨v, hv, rfl⟩ := mem_D3_iff.1 hd
  have hm4 : 4 ≤ m := by omega
  set L : Subgroup (R3 f) := LocalGroup (D3 f) (reflBar f v) with hL
  set Z : Subgroup (R3 f) := Subgroup.zpowers (reflBar f v) with hZ
  have hpcL_le : (CFSG.pCore 2 L).map L.subtype ≤ Z :=
    pCore_localGroup_R3_le hf hm h36 hv
  have hZnorm : (Z.subgroupOf (Z ⊔ L)).Normal := by
    apply Subgroup.normal_of_le_center
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro k
    have hzZ : (z : R3 f) ∈ Z := Subgroup.mem_subgroupOf.mp hz
    have hZle : Z ≤ Subgroup.centralizer ({(z : R3 f)} : Set (R3 f)) := by
      intro z' hz'
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hzZ
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz'
      rw [← hi, ← hj]
      exact (Commute.zpow_zpow_self (reflBar f v) i j).eq.symm
    have hLle : L ≤ Subgroup.centralizer ({(z : R3 f)} : Set (R3 f)) := by
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hzZ
      rw [← hi]
      exact (((show Commute (l : R3 f) (reflBar f v) from
        commute_of_mem_localGroup' (E := D3 f) (d := reflBar f v) hl).symm).zpow_left i).eq.symm
    have hKle : Z ⊔ L ≤ Subgroup.centralizer ({(z : R3 f)} : Set (R3 f)) := sup_le hZle hLle
    have hk : (k : R3 f) ∈ Subgroup.centralizer ({(z : R3 f)} : Set (R3 f)) := hKle k.2
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hk)
  have hZ2 : IsPGroup 2 Z := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [pow_one, hZ, Nat.card_zpowers, orderOf_reflBar hf hm4 hv]
  have hker2 : IsPGroup 2 (Z.subgroupOf L) := by
    let inc : Z.subgroupOf L →* Z :=
      { toFun := fun x => ⟨(x : L), (Subgroup.mem_subgroupOf.mp x.2)⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun x y => Subtype.ext rfl }
    exact hZ2.of_injective inc fun x y h => by
      have h' : ((x : L) : R3 f) = ((y : L) : R3 f) :=
        congrArg (fun z : Z => (z : R3 f)) h
      exact Subtype.ext (Subtype.ext h')
  have hpL : CFSG.pCore 2 L ≤ Z.subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hpcL_le (Subgroup.mem_map_of_mem L.subtype hx)
  have hpcK : (CFSG.pCore 2 (Z ⊔ L : Subgroup (R3 f))).map
        (Z ⊔ L : Subgroup (R3 f)).subtype ≤ Z :=
    pCore_sup_map_subtype_le_of_normal_of_isPGroup_inf L Z hZnorm hker2 hpL
  have hKcen : CFSG.RankThree.GF2n.Tim79a.cenGen (D3 f) (reflBar f v) = Z ⊔ L := by
    rw [CFSG.RankThree.GF2n.Tim79a.cenGen]
    have hset : (D3 f ∩ (Subgroup.centralizer ({reflBar f v} : Set (R3 f)) : Set (R3 f))) =
        insert (reflBar f v) (LocalClass (D3 f) (reflBar f v)) := by
      ext w
      rw [Set.mem_inter_iff]
      rw [show w ∈ (Subgroup.centralizer ({reflBar f v} : Set (R3 f)) : Set (R3 f)) ↔
          w * reflBar f v = reflBar f v * w from Subgroup.mem_centralizer_singleton_iff]
      exact (Set.ext_iff.mp (centralizerClass_eq (E := D3 f) (x := reflBar f v)
        (reflBar_mem_D3 hv))) w
    rw [hset]
    change Subgroup.closure (insert (reflBar f v) (LocalClass (D3 f) (reflBar f v))) = Z ⊔ L
    rw [hL, hZ, LocalGroup, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    rfl
  rw [hKcen, center_R3_eq_bot hf hm4, sup_bot_eq]
  exact hpcK

theorem noSqE1_R3_of_ge_six {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hf : IsF3Form f) (hm6 : 6 ≤ m) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 (D3 f) :=
  noSqE1_R3 hf (by omega) fun h5 => by omega

theorem noSqE1_R3_of_five_ncard36 {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}
    (hf : IsF3Form f) (h36 : (D3 f).ncard = 36) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 (D3 f) :=
  noSqE1_R3 (m := 5) hf le_rfl fun _ => h36

theorem nonabelianCommutator_of_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    (h : ∃ a b : commutator H, a * b ≠ b * a) :
    ∃ a b : commutator G, a * b ≠ b * a := by
  have hmap : (commutator G).map φ.toMonoidHom = commutator H := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ φ.surjective]
  let e : commutator G ≃* commutator H :=
    ((commutator G).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hmap)
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e.symm a, e.symm b, fun h' => hab ?_⟩
  have := congrArg e h'
  simpa [e] using this

theorem transvectionHyp_R3_of_five_ncard45 {G : Type} [Group G] {D : Set G}
    (hP : Pair G D) (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G))
    {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)} (hf : IsF3Form f)
    (h45 : (D3 f).ncard = 45) (φ : G ≃* R3 f) (hD : D3 f = φ '' D) :
    CFSG.Timmesfeld.Transvection.TransvectionHyp G
      {A | ∃ d ∈ D, A = Subgroup.zpowers d} := by
  have hS_R3 : IsSimpleGroup (commutator (R3 f)) := by
    haveI : IsSimpleGroup (commutator G) := hS
    exact CFSG.Fischer.Classification.Recognition.R3.isSimpleGroup_commutator_of_mulEquiv φ
  have hna_R3 : ∃ a b : commutator (R3 f), a * b ≠ b * a :=
    CFSG.Fischer.Classification.Recognition.R3.nonabelian_commutator_R3 hf (by norm_num) hS_R3
  have hnaG : ∃ a b : commutator G, a * b ≠ b * a :=
    nonabelianCommutator_of_mulEquiv φ hna_R3
  obtain ⟨ψ, hψ⟩ := CFSG.Fischer.Classification.exists_mulEquiv_U2_four_of_ncard hf h45
  let Φ : G ≃* Unitary.U2 4 := φ.trans ψ
  have hΦD : Φ '' D = Unitary.DU 4 := by
    rw [MulEquiv.coe_trans, Set.image_comp, ← hD, hψ]
  have hM : fischerCentralQuotientModel D (SUm 4) (TU 4) :=
    (CFSG.Fischer.Classification.fischerCentralQuotientModel_iff_U2 (m := 4)).2 ⟨Φ, hΦD⟩
  exact transvectionHyp_of_psu hP hZ hS hnaG (by norm_num) hM

theorem f3Row : F3Row := by
  intro G _ D hP hZ hS m hm f hsymm hnd hmodel
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨φ, hφ⟩ :=
    (CFSG.Fischer.Classification.fischerCentralQuotientModel_iff (f := f) D).1 hmodel
  have hD : D3 f = φ '' D := by
    ext q
    constructor
    · intro hq
      refine ⟨φ.symm q, ?_, φ.apply_symm_apply q⟩
      exact (hφ (φ.symm q)).2 (by simpa using hq)
    · rintro ⟨g, hg, rfl⟩
      exact (hφ g).1 hg
  rcases Nat.lt_or_ge m 6 with hm6 | hm6
  · obtain rfl : m = 5 := by omega
    rcases CFSG.Fischer.Classification.R3_five_cases hf with ⟨h45, _⟩ | ⟨h36, _⟩
    · exact Or.inr (transvectionHyp_R3_of_five_ncard45 hP hZ hS hf h45 φ hD)
    · exact Or.inl (noSqE1_of_map_mulEquiv φ hD (noSqE1_R3_of_five_ncard36 hf h36))
  · exact Or.inl (noSqE1_of_map_mulEquiv φ hD (noSqE1_R3_of_ge_six hf hm6))

end CFSG.OddTranspositions
