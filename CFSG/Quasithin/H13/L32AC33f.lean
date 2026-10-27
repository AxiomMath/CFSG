module

public import CFSG.Quasithin.H13.L32AC33e

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

@[expose] def szB12 (T H K : Subgroup G) (c : ↥H ⧸ CFSG.pCore 2 ↥H) :
    Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  szB1 T H K ⊔ (szB1 T H K).map (MulAut.conj c : _ →* (↥H ⧸ CFSG.pCore 2 ↥H))

omit [Finite G] in
theorem isSylowIn_modO2Image {T : Subgroup G} (hT : IsSylowTwoOf T H) :
    IsSylowIn 2 (modO2Image H T) ⊤ := by
  have hS2 : IsPGroup 2 ↥(T.subgroupOf H) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  refine ⟨le_top, hS2.map _, fun hd => hT.2.2 ?_⟩
  rw [Subgroup.relIndex_top_right] at hd
  exact hd.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _))

theorem isSolvable_preimage {X : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hX : Group.IsSolvable ↥X) :
    Group.IsSolvable ↥((X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : CFSG.pCore 2 ↥H ≤ X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := fun q hq => by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff q).mpr hq]
    exact X.one_mem
  have hsQ : Group.IsSolvable ↥(CFSG.pCore 2 ↥H) := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).isNilpotent
    infer_instance
  let g : ↥(X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) →* ↥X :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp
      (X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).subtype).codRestrict X fun x => x.2
  have hker : g.ker ≤ (Subgroup.inclusion hle).range := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (x : ↥H) = 1 := congrArg Subtype.val hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨x, h1⟩, rfl⟩
  have : Group.IsSolvable ↥(X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) :=
    Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) g hker
  exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective _ H.subtype
    H.subtype_injective).toMonoidHom) (MulEquiv.surjective _)

theorem mem_normalizer_l1_of_solvable (h29 : Thm14_7_29) (S : Setting147 G T L V H)
    {X : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hX : Group.IsSolvable ↥X)
    (hLT : modO2Image H (l1 T L V ⊔ T) ≤ X) {β : ↥H}
    (hβ : QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ X) :
    (β : G) ∈ Subgroup.normalizer (l1 T L V : Set G) := by
  have hLTH : l1 T L V ⊔ T ≤ H := sup_le (Setting147.l1H' S) (Setting147.TH' S)
  have hLTY : l1 T L V ⊔ T ≤ (X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype :=
    fun z hz => Subgroup.mem_map.mpr ⟨⟨z, hLTH hz⟩, hLT (mem_modO2Image'.mpr ⟨_, hz, rfl⟩), rfl⟩
  have hYM := h29 G T L V S.hyp _ hLTY ((Subgroup.map_subtype_le _).trans S.hz.2.1)
    (isSolvable_preimage hX)
  have hβY : (β : G) ∈ (X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype :=
    Subgroup.mem_map.mpr ⟨β, hβ, rfl⟩
  exact normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hYM hβY, Subgroup.le_normalizer (S.hz.2.1 β.2)⟩)

namespace CtxB

variable {K : Subgroup G} {t₀ : G} (C : CtxB T L V H K t₀)
include C

theorem ht₀H : t₀ ∈ H := C.hTH C.ht₀

theorem isSylowIn_szS1 : IsSylowIn 2 (szS1 T H K) (modO2Image H K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact F6.isSylowIn_inf_of_isSubnormal (modO2Image_mem_cComp C.hK).2.2.1
    (isSylowIn_modO2Image (isSylowTwoOf_of_quasithinIsSylowTwo C.S.hyp.fsu.sylow C.hTH))

theorem isSolvable_szB1 : Group.IsSolvable ↥(szB1 T H K) := by
  have hS := C.isSylowIn_szS1
  have hSB : szS1 T H K ≤ szB1 T H K := le_inf Subgroup.le_normalizer hS.le
  refine isSolvable_of_isPGroup_odd hSB inf_le_left hS.isPGroup ?_
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hSB (inf_le_right : szB1 T H K ≤ _)
  have hodd : Odd ((szS1 T H K).relIndex (modO2Image H K)) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hS.not_dvd_relIndex)
  exact (Nat.odd_mul.mp (hmul ▸ hodd)).1

theorem commute_szB1 (hA37 : A37ForSQTK) {a b : ↥H ⧸ CFSG.pCore 2 ↥H} (ha : a ∈ szB1 T H K)
    (hb : b ∈ (szB1 T H K).map
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        _ →* (↥H ⧸ CFSG.pCore 2 ↥H))) :
    a * b = b * a := by
  have hb' : b ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) := by
    have h1 := modO2Image_map_conj C.hKH ⟨t₀, C.ht₀H⟩
    rw [h1]
    exact Subgroup.map_mono inf_le_right hb
  exact commute_of_conj hA37 C.S C.hK C.ht₀H C.ht₀N ha.2 hb'

theorem isSolvable_szB12 (hA37 : A37ForSQTK) :
    Group.IsSolvable ↥(szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩)) := by
  have h1 := C.isSolvable_szB1
  have h2 : Group.IsSolvable ↥((szB1 T H K).map
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        _ →* (↥H ⧸ CFSG.pCore 2 ↥H))) :=
    Group.isSolvable_of_surjective (f := MonoidHom.subgroupMap _ (szB1 T H K))
      (MonoidHom.subgroupMap_surjective _ _)
  refine isSolvable_sup_of_le_normalizer' (fun b hb => ?_) h1 h2
  refine mem_normalizer_of_conj_mem_fin fun a ha => ?_
  rw [← C.commute_szB1 hA37 ha hb, mul_inv_cancel_right]
  exact ha

theorem mk_T_conj_mem_szB12 {g : ↥H} (hgT : (g : G) ∈ T) {b : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hb : b ∈ szB1 T H K) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) g * b * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) g)⁻¹ ∈
      szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) := by
  rcases C.two g g.2 with hgN | hgN
  · exact Subgroup.mem_sup_left
      ((Subgroup.mem_normalizer_iff.mp (C.mk_T_mem_normalizer_szB1 hgT hgN) b).mp hb)
  · have hrT : t₀⁻¹ * (g : G) ∈ T := mul_mem (inv_mem C.ht₀) hgT
    have hrH : t₀⁻¹ * (g : G) ∈ H := mul_mem (inv_mem C.ht₀H) g.2
    have hr := C.mk_T_mem_normalizer_szB1 (r := ⟨t₀⁻¹ * g, hrH⟩) hrT hgN
    have h1 := (Subgroup.mem_normalizer_iff.mp hr b).mp hb
    have e : QuotientGroup.mk' (CFSG.pCore 2 ↥H) g = QuotientGroup.mk' (CFSG.pCore 2 ↥H)
        ⟨t₀, C.ht₀H⟩ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀⁻¹ * g, hrH⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext (by simp)
    refine Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨_, h1, ?_⟩)
    rw [e]
    simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
    group

theorem mk_T_mem_normalizer_szB12 {t : ↥H} (htT : (t : G) ∈ T) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) t ∈ Subgroup.normalizer
      (szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have hle : szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) ≤
      (szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩)).comap
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) t) : _ →* (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine sup_le (fun b hb => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_comap]
      simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
      exact C.mk_T_conj_mem_szB12 htT hb
    · obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      rw [Subgroup.mem_comap]
      have htt : (t : G) * t₀ ∈ T := mul_mem htT C.ht₀
      have h1 := C.mk_T_conj_mem_szB12 (g := t * ⟨t₀, C.ht₀H⟩) htt hb'
      rw [map_mul] at h1
      simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
      have e : QuotientGroup.mk' (CFSG.pCore 2 ↥H) t *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩ * b' *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩)⁻¹) *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H) t)⁻¹ =
            QuotientGroup.mk' (CFSG.pCore 2 ↥H) t *
              QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩ * b' *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥H) t *
              QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩)⁻¹ := by group
      rw [e]
      exact h1
  refine mem_normalizer_of_conj_mem_fin fun a ha => ?_
  have := hle ha
  rw [Subgroup.mem_comap] at this
  simpa only [MonoidHom.coe_ofClass, MulAut.conj_apply] using this

theorem mk_l1_mem_normalizer_szB12 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈ Subgroup.normalizer
      (szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  refine mem_normalizer_sup'' (C.mk_l1_mem_normalizer_szB1 h1222 h1332 h1334 hy hy3)
    (mem_normalizer_map_conj ?_)
  have hTl1 := Setting147.T_le_N_l1 C.S h1332
  have hy' : t₀⁻¹ * y * t₀ ∈ l1 T L V := by
    have := (Subgroup.mem_normalizer_iff.mp (hTl1 (inv_mem C.ht₀)) y).mp hy
    simpa using this
  have hy'3 : (t₀⁻¹ * y * t₀) ^ 3 = 1 := by
    rw [show (t₀⁻¹ * y * t₀) ^ 3 = t₀⁻¹ * y ^ 3 * t₀ by rw [pow_three, pow_three]; group, hy3]
    group
  have h1 := C.mk_l1_mem_normalizer_szB1 h1222 h1332 h1334 hy' hy'3
  have e : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩)⁻¹ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀⁻¹ * y * t₀, Setting147.l1H' C.S hy'⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact h1

theorem mk_l1T_le_normalizer_szB12 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    modO2Image H (l1 T L V ⊔ T) ≤ Subgroup.normalizer
      (szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 C.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 C.S.hyp h1222 h1332 h1334 hV2
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hl1P : l1 T L V ≤ ((Subgroup.normalizer
      (szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H))).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map
          H.subtype := by
    rw [← hl1]
    refine l1_le_of_cube S14 fun y hyL hy3 => ?_
    have hy : y ∈ l1 T L V := by rw [← hl1]; exact hyL
    exact Subgroup.mem_map.mpr ⟨⟨y, Setting147.l1H' C.S hy⟩,
      C.mk_l1_mem_normalizer_szB12 h1222 h1332 h1334 hy hy3, rfl⟩
  have hTP : T ≤ ((Subgroup.normalizer
      (szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H))).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map
          H.subtype := fun t ht =>
    Subgroup.mem_map.mpr ⟨⟨t, C.hTH ht⟩, C.mk_T_mem_normalizer_szB12 ht, rfl⟩
  intro z hz
  obtain ⟨w, hw, rfl⟩ := mem_modO2Image'.mp hz
  obtain ⟨w', hw', hww⟩ := Subgroup.mem_map.mp (sup_le hl1P hTP hw)
  have : w' = w := Subtype.ext hww
  rw [← this]
  exact hw'

theorem isSolvable_szX (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    Group.IsSolvable ↥(szB12 T H K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) ⊔
      modO2Image H (l1 T L V ⊔ T)) := by
  have hLT : Group.IsSolvable ↥(l1 T L V ⊔ T) := by
    rw [sup_comm]
    exact isSolvable_of_isTwoThree (isTwoThree_card_sup (relIndex_l1 h1222 h1332 h1334 C.S.hyp)
      C.S.hyp.fsu.sylow.1 (Setting147.T_le_N_l1 C.S h1332))
  have hLTH : l1 T L V ⊔ T ≤ H := sup_le (Setting147.l1H' C.S) C.hTH
  have : Group.IsSolvable ↥((l1 T L V ⊔ T).subgroupOf H) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hLTH).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hLTb : Group.IsSolvable ↥(modO2Image H (l1 T L V ⊔ T)) :=
    Group.isSolvable_of_surjective
      (f := MonoidHom.subgroupMap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
        ((l1 T L V ⊔ T).subgroupOf H)) (MonoidHom.subgroupMap_surjective _ _)
  exact isSolvable_sup_of_le_normalizer' (C.mk_l1T_le_normalizer_szB12 h1222 h1332 h1334)
    (C.isSolvable_szB12 hA37) hLTb

theorem mem_normalizer_l1_of_szB1 (hA37 : A37ForSQTK) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {β : ↥H}
    (hβ : QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ szB1 T H K) :
    (β : G) ∈ Subgroup.normalizer (l1 T L V : Set G) :=
  mem_normalizer_l1_of_solvable h29 C.S (C.isSolvable_szX hA37 h1222 h1332 h1334) le_sup_right
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left hβ))

end CtxB

end CFSG.Quasithin.H13.L32A.C
