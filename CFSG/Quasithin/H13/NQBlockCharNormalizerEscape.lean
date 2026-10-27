module

public import CFSG.Quasithin.H13.NQBlockComplementaryLayer
public import CFSG.Quasithin.H13.NQTermCharNormalizerResidual
public import CFSG.Quasithin.H13.NQBlockNormalizedCore
public import CFSG.Quasithin.H13.NQRigidWitness
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
public import CFSG.LieType.SteinbergBRParabolicResidualImage

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup

section Transport

open CFSG.Quasithin.SteinbergCC

variable {G : Type*} [Group G]

theorem exists_frattini_subgroupOf_equiv {H X : Subgroup G} (hXH : X ≤ H)
    [(X.subgroupOf H).Normal] :
    ∃ Θ : ((X.subgroupOf H) ⧸ CFSG.pCore 2 (X.subgroupOf H)) ⧸
        frattini ((X.subgroupOf H) ⧸ CFSG.pCore 2 (X.subgroupOf H)) ≃*
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X),
      ∀ (h : H) (hn : (h : G) ∈ normalizer (X : Set G)) w,
        Θ (frattiniQuotConj (X.subgroupOf H) h w) = normalizerFrattiniConj X ⟨h, hn⟩ (Θ w) := by
  let e₁ : X.subgroupOf H ≃* X := subgroupOfEquivOfLe hXH
  let e₂ : X.subgroupOf H ⧸ CFSG.pCore 2 (X.subgroupOf H) ≃* X ⧸ CFSG.pCore 2 X :=
    QuotientGroup.congr (CFSG.pCore 2 (X.subgroupOf H)) (CFSG.pCore 2 X) e₁
      (CFSG.pCore_map_iso 2 e₁)
  let Θ := QuotientGroup.congr _ _ e₂ (map_frattini_mulEquiv e₂)
  refine ⟨Θ, fun h hn w => ?_⟩
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  rfl

theorem characteristic_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {C : Subgroup A} (hC : C.Characteristic) : (C.map e.toMonoidHom).Characteristic := by
  rw [characteristic_iff_map_eq]
  intro φ
  have h := characteristic_iff_map_eq.mp hC ((e.trans φ).trans e.symm)
  calc (C.map e.toMonoidHom).map φ.toMonoidHom
      = ((C.map ((e.trans φ).trans e.symm).toMonoidHom).map e.toMonoidHom) := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext x
        simp
    _ = C.map e.toMonoidHom := by rw [h]

theorem pCoreOf_map_subtype {H : Subgroup G} (K : Subgroup H) :
    (CFSG.Open.pCoreOf 2 K).map H.subtype = CFSG.Open.pCoreOf 2 (K.map H.subtype) := by
  unfold CFSG.Open.pCoreOf
  exact CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_pCore_of_injective 2 H.subtype
    H.subtype_injective K

theorem quasithinIsLocal_map_subtype [Finite G] {H : Subgroup G} {T A : Subgroup H}
    (h : CFSG.Open.quasithinIsLocal T A) :
    CFSG.Open.quasithinIsLocal (T.map H.subtype) (A.map H.subtype) := by
  obtain ⟨hT2, hAc, hidx, hO2⟩ := h
  have hAc' : A ∈ cComp (A ⊔ T) := hAc
  refine ⟨hT2.map _, ?_, ?_, ?_⟩
  · have := map_subtype_mem_cComp_of_mem hAc'
    rwa [Subgroup.map_sup] at this
  · rw [← Subgroup.map_sup]
    intro h2
    apply hidx
    have e : ((T.map H.subtype).subgroupOf ((A ⊔ T).map H.subtype)).index =
        (T.subgroupOf (A ⊔ T)).index := by
      change (T.map H.subtype).relIndex ((A ⊔ T).map H.subtype) = T.relIndex (A ⊔ T)
      exact Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective
    rwa [e] at h2
  · rw [← Subgroup.map_sup, ← pCoreOf_map_subtype]
    intro hb
    apply hO2
    exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hb

end Transport

section NC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem characteristic_normalizer_facts [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {T X C : Subgroup G} (hT : quasithinIsSylowTwo T) (hC1 : C ≠ ⊥)
    (hCR : C ≤ pCoreOf 2 (X ⊔ T)) (hCc : (C.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic) :
    T ≤ normalizer (C : Set G) ∧ normalizer (C : Set G) ≠ ⊤ ∧
      C ≤ pCoreOf 2 (normalizer (C : Set G)) ∧ IsSylowTwoOf T (normalizer (C : Set G)) ∧
      pCoreOf 2 (normalizer (C : Set G)) ≤ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRp : IsPGroup 2 (pCoreOf 2 (X ⊔ T)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hCp : IsPGroup 2 C := hRp.to_le hCR
  have hTR : T ≤ normalizer (pCoreOf 2 (X ⊔ T) : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) (X ⊔ T))
  have hCmap : (C.subgroupOf (pCoreOf 2 (X ⊔ T))).map (pCoreOf 2 (X ⊔ T)).subtype = C :=
    map_subgroupOf_eq_of_le hCR
  have hRC : normalizer (pCoreOf 2 (X ⊔ T) : Set G) ≤ normalizer (C : Set G) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (C.subgroupOf (pCoreOf 2 (X ⊔ T)))
    rwa [hCmap] at h
  have hTN : T ≤ normalizer (C : Set G) := hTR.trans hRC
  have hCN : C ≤ normalizer (C : Set G) := Subgroup.le_normalizer
  have hCO : C ≤ pCoreOf 2 (normalizer (C : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCN le_rfl hCp
  have hTs : IsSylowTwoOf T (normalizer (C : Set G)) :=
    ⟨hTN, hT.1, fun h2 => hT.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTN))⟩
  refine ⟨hTN, fun htop => ?_, hCO, hTs, ?_⟩
  ·
    have hCn : C.Normal := normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal C with h0 | h1
    · exact hC1 h0
    · have hG2 : IsPGroup 2 G := by
        have h := hCp
        rw [h1] at h
        exact IsPGroup.of_equiv h Subgroup.topEquiv
      obtain ⟨a, b, hab⟩ := hnab
      have hsolv : Group.IsSolvable G := by
        have := hG2.isNilpotent
        infer_instance
      exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolv a b)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : y ∈ CFSG.pCore 2 ↥(normalizer (C : Set G)) := by
      exact hy
    exact mem_subgroupOf.mp (pCore_two_le_subgroupOf hTs hy')

end NC

section Canonicity

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem coe_mem_normalizer_of_mem_normalizer_subgroupOf {K X : Subgroup G} (hXK : X ≤ K)
    (k : normalizer ((X.subgroupOf K : Subgroup K) : Set K)) :
    ((k : K) : G) ∈ normalizer (X : Set G) := by
  have h := Subgroup.mem_map_of_mem K.subtype k.2
  rw [map_subtype_normalizer_eq, map_subgroupOf_eq_of_le hXK] at h
  exact h.2

omit [Finite G] in
theorem exists_residual_subgroupOf_equiv {K X : Subgroup G} (hXK : X ≤ K) :
    ∃ Θ : ((X.subgroupOf K) ⧸ CFSG.pCore 2 (X.subgroupOf K)) ⧸
        frattini ((X.subgroupOf K) ⧸ CFSG.pCore 2 (X.subgroupOf K)) ≃*
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X),
      ∀ (k : normalizer ((X.subgroupOf K : Subgroup K) : Set K)) w,
        Θ (normalizerResidualAction (X.subgroupOf K) k w) =
          normalizerFrattiniConj X ⟨(k : K), coe_mem_normalizer_of_mem_normalizer_subgroupOf hXK k⟩
            (Θ w) := by
  let e₁ : X.subgroupOf K ≃* X := subgroupOfEquivOfLe hXK
  let e₂ : X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K) ≃* X ⧸ CFSG.pCore 2 X :=
    QuotientGroup.congr (CFSG.pCore 2 (X.subgroupOf K)) (CFSG.pCore 2 X) e₁
      (CFSG.pCore_map_iso 2 e₁)
  let Θ := QuotientGroup.congr _ _ e₂ (map_frattini_mulEquiv e₂)
  refine ⟨Θ, fun k w => ?_⟩
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  rfl

end Canonicity

section CharNormalizer

open CFSG.Quasithin.SteinbergCC

open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)

variable {G : Type} [Group G] [Finite G]

abbrev WPlane (X : Subgroup G) : Type :=
  (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)

omit [Finite G] in
theorem quasithinIsSylowTwo_subgroupOf {T H : Subgroup G} (hT : CFSG.Open.quasithinIsSylowTwo T)
    (hTH : T ≤ H) : CFSG.Open.quasithinIsSylowTwo (T.subgroupOf H) :=
  ⟨hT.1.of_equiv (subgroupOfEquivOfLe hTH).symm, fun h2 =>
    hT.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩

omit [Finite G] in
theorem pCore_sup_subgroupOf_map {H X T : Subgroup G} (hXH : X ≤ H) (hTH : T ≤ H) :
    ((CFSG.pCore 2 ↥(X.subgroupOf H ⊔ T.subgroupOf H)).map
        (X.subgroupOf H ⊔ T.subgroupOf H).subtype).map H.subtype =
      CFSG.Open.pCoreOf 2 (X ⊔ T) := by
  have h1 := pCoreOf_map_subtype (H := H) (X.subgroupOf H ⊔ T.subgroupOf H)
  unfold CFSG.Open.pCoreOf at h1
  rw [h1, Subgroup.map_sup, map_subgroupOf_eq_of_le hXH, map_subgroupOf_eq_of_le hTH]
  unfold CFSG.Open.pCoreOf
  try with_reducible rfl

theorem char_normalizer_residual_in_G {T H L : Subgroup G}
    (hT : CFSG.Open.quasithinIsSylowTwo T)
    (hTH : T ≤ H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) (hHLT : H = L ⊔ T)
    (hLC : L ∈ cComp L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXn : (X.subgroupOf H).Normal) (hX2 : NoPQuotient 2 X)
    (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hW : Nat.card (WPlane X) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    (hirr : ∀ V : Subgroup (WPlane X),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
        V = ⊥ ∨ V = ⊤)
    (C : Subgroup G) (hC1 : C ≠ ⊥) (hCR : C ≤ CFSG.Open.pCoreOf 2 (X ⊔ T))
    (hCc : (C.subgroupOf (CFSG.Open.pCoreOf 2 (X ⊔ T))).Characteristic) :
    let Y := (CFSG.perfectResidual ↥(L ⊓ normalizer (CFSG.Open.pCoreOf 2 (X ⊔ T) : Set G))).map
      (L ⊓ normalizer (CFSG.Open.pCoreOf 2 (X ⊔ T) : Set G)).subtype
    let A := (CFSG.perfectResidual ↥(L ⊓ normalizer (C : Set G))).map
      (L ⊓ normalizer (C : Set G)).subtype
    CFSG.Open.quasithinIsLocal T A ∧ ¬ CFSG.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A) ∧
      ⁅X, Y⁆ = X ∧ X ≤ Y ∧ Y ≤ A ∧
      ∀ l : normalizer (X : Set G), (l : G) ∈ L → ∃ y : normalizer (X : Set G), (y : G) ∈ Y ∧
        normalizerFrattiniConj X y = normalizerFrattiniConj X l := by
  intro Y A
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXH : X ≤ H := hXL.trans hLH
  have := hLn
  have := hXn
  have hT' := quasithinIsSylowTwo_subgroupOf hT hTH
  let T' : Sylow 2 H := hT'.1.toSylow hT'.2
  have hT'c : (T' : Subgroup H) = T.subgroupOf H := rfl
  have hL' : L.subgroupOf H ∈ cComp (L.subgroupOf H) := subgroupOf_mem_cComp_of_le hLH hLC
  have hLT' : L.subgroupOf H ⊔ (T' : Subgroup H) = ⊤ := by
    rw [hT'c, ← Subgroup.subgroupOf_sup hLH hTH, ← hHLT, Subgroup.subgroupOf_self]
  have hXL' : X.subgroupOf H ≤ L.subgroupOf H := fun x hx => hXL hx
  let e₁ : X.subgroupOf H ≃* X := subgroupOfEquivOfLe hXH
  have hX2' : ∀ (N : Subgroup (X.subgroupOf H)) [N.Normal],
      IsPGroup 2 ((X.subgroupOf H) ⧸ N) → N = ⊤ :=
    CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_surjective e₁.symm.toMonoidHom
      e₁.symm.surjective hX2
  let e₂ : X.subgroupOf H ⧸ CFSG.pCore 2 (X.subgroupOf H) ≃* X ⧸ CFSG.pCore 2 X :=
    QuotientGroup.congr _ _ e₁ (CFSG.pCore_map_iso 2 e₁)
  have hP' : IsPGroup p (X.subgroupOf H ⧸ CFSG.pCore 2 (X.subgroupOf H)) :=
    IsPGroup.of_equiv hXp e₂.symm
  obtain ⟨Θ, hΘ⟩ := exists_frattini_subgroupOf_equiv hXH
  have hW' : Nat.card ((X.subgroupOf H ⧸ CFSG.pCore 2 (X.subgroupOf H)) ⧸
      frattini (X.subgroupOf H ⧸ CFSG.pCore 2 (X.subgroupOf H))) = p ^ 2 :=
    (Nat.card_congr Θ.toEquiv).trans hW
  have hirr' : ∀ U : Subgroup ((X.subgroupOf H ⧸ CFSG.pCore 2 (X.subgroupOf H)) ⧸
      frattini (X.subgroupOf H ⧸ CFSG.pCore 2 (X.subgroupOf H))),
      (∀ l ∈ L.subgroupOf H, ∀ u ∈ U, frattiniQuotConj (X.subgroupOf H) l u ∈ U) →
        U = ⊥ ∨ U = ⊤ := by
    intro U hU
    rcases hirr (U.map Θ.toMonoidHom) (by
        rintro ⟨l, hln⟩ hlL _ ⟨u, hu, rfl⟩
        have hlH : l ∈ H := hLH hlL
        refine ⟨frattiniQuotConj (X.subgroupOf H) ⟨l, hlH⟩ u,
          hU ⟨l, hlH⟩ (mem_subgroupOf.mpr hlL) u hu, ?_⟩
        exact hΘ ⟨l, hlH⟩ hln u) with h0 | h1
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ Θ.injective).mp h0
    · right
      rw [eq_top_iff]
      intro u _
      have hu : Θ u ∈ U.map Θ.toMonoidHom := by rw [h1]; exact Subgroup.mem_top _
      obtain ⟨u', hu', he⟩ := hu
      rw [Θ.injective he] at hu'
      exact hu'
  have hnt' : ∃ l ∈ L.subgroupOf H, ∃ w,
      frattiniQuotConj (X.subgroupOf H) l w ≠ w := by
    obtain ⟨⟨l, hln⟩, hlL, hne⟩ := hLW
    have hlH : l ∈ H := hLH hlL
    obtain ⟨w, hw⟩ : ∃ w, normalizerFrattiniConj X ⟨l, hln⟩ w ≠ w := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      exact hne (MulEquiv.ext hall)
    refine ⟨⟨l, hlH⟩, mem_subgroupOf.mpr hlL, Θ.symm w, fun heq => hw ?_⟩
    have h1 := congrArg Θ heq
    rwa [hΘ ⟨l, hlH⟩ hln, MulEquiv.apply_symm_apply] at h1
  have key :=
    NQTerm.characteristic_normalizer_perfect_residuals_are_original_nonquasisimple_local_Ccomponents
      hL' T' hLT' hp hp5 hXL' hX2' hP' hW' hirr' hnt'
  have hCH : C ≤ H := hCR.trans ((Subgroup.map_subtype_le _).trans (sup_le hXH hTH))
  have hR'map := pCore_sup_subgroupOf_map hXH hTH
  have hC'R : C.subgroupOf H ≤ (CFSG.pCore 2 ↥(X.subgroupOf H ⊔ (T' : Subgroup H))).map
      (X.subgroupOf H ⊔ (T' : Subgroup H)).subtype := by
    intro c hc
    have h1 : (c : G) ∈ ((CFSG.pCore 2 ↥(X.subgroupOf H ⊔ T.subgroupOf H)).map
        (X.subgroupOf H ⊔ T.subgroupOf H).subtype).map H.subtype := hR'map ▸ hCR hc
    obtain ⟨r, hr, hrc⟩ := h1
    have hrc' : r = c := Subtype.ext hrc
    rw [← hrc']
    exact hr
  have hC'1 : C.subgroupOf H ≠ ⊥ := by
    intro hb
    apply hC1
    rw [← map_subgroupOf_eq_of_le hCH, hb, Subgroup.map_bot]
  have hC'c : ((C.subgroupOf H).subgroupOf ((CFSG.pCore 2 ↥(X.subgroupOf H ⊔
      (T' : Subgroup H))).map (X.subgroupOf H ⊔ (T' : Subgroup H)).subtype)).Characteristic := by
    set R' : Subgroup H := (CFSG.pCore 2 ↥(X.subgroupOf H ⊔ (T' : Subgroup H))).map
      (X.subgroupOf H ⊔ (T' : Subgroup H)).subtype with hR'def
    let ψR : R' ≃* CFSG.Open.pCoreOf 2 (X ⊔ T) :=
      (R'.equivMapOfInjective H.subtype H.subtype_injective).trans
        (MulEquiv.subgroupCongr hR'map)
    have hmap : (C.subgroupOf H).subgroupOf R' =
        (C.subgroupOf (CFSG.Open.pCoreOf 2 (X ⊔ T))).map ψR.symm.toMonoidHom := by
      ext x
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, mem_subgroupOf, mem_subgroupOf,
        mem_subgroupOf]
      rfl
    rw [hmap]
    exact characteristic_map_mulEquiv ψR.symm hCc
  obtain ⟨-, -, -, -, -, hXY', hXleY', hYA', -, -, -, -, -, hψ3, -, hAq', hAloc', -⟩ :=
    key (C.subgroupOf H) hC'R hC'c hC'1
  have hBmap : (L.subgroupOf H ⊓ normalizer ((C.subgroupOf H : Subgroup H) : Set H)).map
      H.subtype = L ⊓ normalizer (C : Set G) := by
    rw [Subgroup.map_inf _ _ _ H.subtype_injective, map_subgroupOf_eq_of_le hLH,
      map_subtype_normalizer_eq, map_subgroupOf_eq_of_le hCH, ← inf_assoc,
      inf_eq_left.mpr hLH]
  have hAmap : ((CFSG.perfectResidual ↥(L.subgroupOf H ⊓
      normalizer ((C.subgroupOf H : Subgroup H) : Set H))).map
        (L.subgroupOf H ⊓ normalizer ((C.subgroupOf H : Subgroup H) : Set H)).subtype).map
          H.subtype =
      (CFSG.perfectResidual ↥(L ⊓ normalizer (C : Set G))).map
        (L ⊓ normalizer (C : Set G)).subtype := by
    rw [CFSG.LieType.SteinbergBR.BlockPar.map_perfectResidual_subgroup]
    exact CFSG.LieType.SteinbergBR.BlockPar.perfectResidual_map_subtype_congr hBmap
  have hTmap : (T' : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le hTH
  have hRH : CFSG.Open.pCoreOf 2 (X ⊔ T) ≤ H :=
    (Subgroup.map_subtype_le _).trans (sup_le hXH hTH)
  have hRmap : ((CFSG.pCore 2 ↥(X.subgroupOf H ⊔ (T' : Subgroup H))).map
      (X.subgroupOf H ⊔ (T' : Subgroup H)).subtype) =
      (CFSG.Open.pCoreOf 2 (X ⊔ T)).subgroupOf H := by
    rw [← hR'map]
    exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hBYmap : (L.subgroupOf H ⊓ normalizer (((CFSG.pCore 2 ↥(X.subgroupOf H ⊔
      (T' : Subgroup H))).map (X.subgroupOf H ⊔ (T' : Subgroup H)).subtype : Subgroup H) :
        Set H)).map H.subtype =
      L ⊓ normalizer (CFSG.Open.pCoreOf 2 (X ⊔ T) : Set G) := by
    rw [hRmap, Subgroup.map_inf _ _ _ H.subtype_injective, map_subgroupOf_eq_of_le hLH,
      map_subtype_normalizer_eq, map_subgroupOf_eq_of_le hRH, ← inf_assoc,
      inf_eq_left.mpr hLH]
  have hYmap : ((CFSG.perfectResidual ↥(L.subgroupOf H ⊓ normalizer
      (((CFSG.pCore 2 ↥(X.subgroupOf H ⊔ (T' : Subgroup H))).map
        (X.subgroupOf H ⊔ (T' : Subgroup H)).subtype : Subgroup H) : Set H))).map
          (L.subgroupOf H ⊓ normalizer (((CFSG.pCore 2 ↥(X.subgroupOf H ⊔
            (T' : Subgroup H))).map (X.subgroupOf H ⊔ (T' : Subgroup H)).subtype :
              Subgroup H) : Set H)).subtype).map H.subtype = Y := by
    rw [CFSG.LieType.SteinbergBR.BlockPar.map_perfectResidual_subgroup]
    exact CFSG.LieType.SteinbergBR.BlockPar.perfectResidual_map_subtype_congr hBYmap
  have hXmap : (X.subgroupOf H).map H.subtype = X := map_subgroupOf_eq_of_le hXH
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := quasithinIsLocal_map_subtype hAloc'
    rwa [hTmap, hAmap] at h1
  rotate_left
  · have h1 := congrArg (Subgroup.map H.subtype) hXY'
    rwa [Subgroup.map_commutator, hXmap, hYmap] at h1
  · have h1 := Subgroup.map_mono (f := H.subtype) hXleY'
    rwa [hXmap, hYmap] at h1
  · have h1 := Subgroup.map_mono (f := H.subtype) hYA'
    rwa [hYmap, hAmap] at h1
  · rintro ⟨l, hln⟩ hlL
    have hlH : l ∈ H := hLH hlL
    have hmem : frattiniQuotConj (X.subgroupOf H) ⟨l, hlH⟩ ∈
        (L.subgroupOf H).map (frattiniQuotConj (X.subgroupOf H)) :=
      Subgroup.mem_map_of_mem _ (mem_subgroupOf.mpr hlL)
    rw [← hψ3] at hmem
    obtain ⟨y', hy', hyl⟩ := hmem
    have hyY : (y' : G) ∈ Y := by
      rw [← hYmap]
      exact Subgroup.mem_map_of_mem _ hy'
    have hyn : (y' : G) ∈ normalizer (X : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mp hXn y'.2
    refine ⟨⟨y', hyn⟩, hyY, MulEquiv.ext fun w => ?_⟩
    have h1 := hΘ y' hyn (Θ.symm w)
    have h2 := hΘ ⟨l, hlH⟩ hln (Θ.symm w)
    rw [MulEquiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, hyl]
  · intro hq
    apply hAq'
    set A' := (CFSG.perfectResidual ↥(L.subgroupOf H ⊓
      normalizer ((C.subgroupOf H : Subgroup H) : Set H))).map
        (L.subgroupOf H ⊓ normalizer ((C.subgroupOf H : Subgroup H) : Set H)).subtype
    let eA : A' ≃* (CFSG.perfectResidual ↥(L ⊓ normalizer (C : Set G))).map
        (L ⊓ normalizer (C : Set G)).subtype :=
      (A'.equivMapOfInjective H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hAmap)
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (QuotientGroup.congr _ _ eA (CFSG.pCore_map_iso 2 eA))).2 hq

end CharNormalizer

section NodeThree

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)

theorem le_pCore_of_normal_of_isQuasisimple {K : Type*} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K)) {p : ℕ} [Fact p.Prime] {X Y : Subgroup K}
    [hXn : X.Normal] (hP : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hXY : ⁅X, Y⁆ = X) :
    X ≤ CFSG.pCore 2 K := by
  classical
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 K)) :=
    QuotientGroup.mk'_surjective _
  have : (X.map (QuotientGroup.mk' (CFSG.pCore 2 K))).Normal := hXn.map _ hπ
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
      (X.map (QuotientGroup.mk' (CFSG.pCore 2 K))) with hZ | hT
  · have h2 : ⁅X.map (QuotientGroup.mk' (CFSG.pCore 2 K)),
        Y.map (QuotientGroup.mk' (CFSG.pCore 2 K))⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hZ.trans (Subgroup.center_le_centralizer _))
    rw [← Subgroup.map_commutator, hXY, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h2
    exact h2
  · exfalso
    have hXs : Group.IsSolvable X := isSolvable_of_isPGroup_quotient_pCore hP
    have hs : Group.IsSolvable (K ⧸ CFSG.pCore 2 K) := by
      have hsurj : Function.Surjective
          ((QuotientGroup.mk' (CFSG.pCore 2 K)).comp X.subtype) := by
        intro z
        have hz : z ∈ X.map (QuotientGroup.mk' (CFSG.pCore 2 K)) := hT ▸ Subgroup.mem_top z
        obtain ⟨x, hx, rfl⟩ := hz
        exact ⟨⟨x, hx⟩, rfl⟩
      exact Group.isSolvable_of_surjective hsurj
    obtain ⟨-, hsimp, a, b, hab⟩ := hq
    have := hsimp
    have : Group.IsSolvable ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a b)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_subgroupOf_of_mem {K X : Subgroup G} {k : K}
    (hk : (k : G) ∈ normalizer (X : Set G)) :
    k ∈ normalizer ((X.subgroupOf K : Subgroup K) : Set K) := by
  rw [mem_normalizer_iff] at hk ⊢
  intro x
  have h := hk x
  simpa [mem_subgroupOf] using h

omit [Finite G] in
theorem le_normalizer_of_characteristic_subgroupOf {N K X : Subgroup G} (hKN : K ≤ N)
    (hKn : (K.subgroupOf N).Normal) (hXK : X ≤ K) (hXc : (X.subgroupOf K).Characteristic) :
    N ≤ normalizer (X : Set G) := by
  have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (X.subgroupOf K)
  rw [map_subgroupOf_eq_of_le hXK] at h1
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mp hKn).trans h1

theorem escaping_characteristic_normalizer_core (h39 : SQTKCLayerPerfectResidual)
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G)
    {T H L : Subgroup G} (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) (hLH : L ≤ H)
    (hLn : (L.subgroupOf H).Normal) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Subgroup G}
    (hXL : X ≤ L) (hXn : (X.subgroupOf H).Normal) (hX2 : NoPQuotient 2 X)
    (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrank : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) (hW : Nat.card (WPlane X) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    (hirr : ∀ V : Subgroup (WPlane X),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
        V = ⊥ ∨ V = ⊤)
    {C Y A : Subgroup G} (hC1 : C ≠ ⊥) (hCR : C ≤ pCoreOf 2 (X ⊔ T))
    (hCc : (C.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic) (hY : Group.IsPerfect Y)
    (hA : A = (CFSG.perfectResidual ↥(L ⊓ normalizer (C : Set G))).map
      (L ⊓ normalizer (C : Set G)).subtype)
    (hAloc : quasithinIsLocal T A) (hXY : ⁅X, Y⁆ = X) (hXleY : X ≤ Y) (hYA : Y ≤ A)
    (hψ : ∀ l : normalizer (X : Set G), (l : G) ∈ L → ∃ y : normalizer (X : Set G),
      (y : G) ∈ Y ∧ normalizerFrattiniConj X y = normalizerFrattiniConj X l) :
    T ≤ normalizer (C : Set G) ∧ normalizer (C : Set G) ≠ ⊤ ∧
      C ≤ pCoreOf 2 (normalizer (C : Set G)) ∧ IsSylowTwoOf T (normalizer (C : Set G)) ∧
      A ≤ normalizer (C : Set G) ∧ quasithinIsLocal T A ∧ T ≤ normalizer (A : Set G) ∧
      ∃ KC : Subgroup G, (KC ∈ cComp (normalizer (C : Set G)) ∧ A ≤ KC) ∧
        (∀ K' : Subgroup G, K' ∈ cComp (normalizer (C : Set G)) ∧ A ≤ K' → K' = KC) ∧
        (KC.subgroupOf (normalizer (C : Set G))).Normal ∧
        ⁅X, Y⁆ = X ∧ X ≤ Y ∧ Y ≤ A ∧ A ≤ KC ∧
        pCoreOf 2 KC ≤ pCoreOf 2 (normalizer (C : Set G)) ∧
        pCoreOf 2 (normalizer (C : Set G)) ≤ T ∧ pCoreOf 2 KC ≤ normalizer (X : Set G) ∧
        (¬ CFSG.IsQuasisimple (↥KC ⧸ CFSG.pCore 2 ↥KC) →
          (X.subgroupOf KC).Characteristic ∧ normalizer (C : Set G) ≤ normalizer (X : Set G)) ∧
        (¬ normalizer (C : Set G) ≤ normalizer (X : Set G) →
          CFSG.IsQuasisimple (↥KC ⧸ CFSG.pCore 2 ↥KC) ∧ ¬ (X.subgroupOf KC).Normal ∧
            A < KC) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTN, hNtop, hCO, hTs, hO2T⟩ := characteristic_normalizer_facts hnab hT hC1 hCR hCc
  set NC := normalizer (C : Set G) with hNCdef
  have hXH : X ≤ H := hXL.trans hLH
  have hHX : H ≤ normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mp hXn
  have hHL : H ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mp hLn
  have hTX : T ≤ normalizer (X : Set G) := hTH.trans hHX
  have hAB : A ≤ L ⊓ NC := by
    rw [hA]
    exact Subgroup.map_subtype_le _
  have hAL : A ≤ L := hAB.trans inf_le_left
  have hANC : A ≤ NC := hAB.trans inf_le_right
  have hTA : T ≤ normalizer (A : Set G) := by
    have hTB : T ≤ normalizer ((L ⊓ NC : Subgroup G) : Set G) := by
      intro t ht
      rw [mem_normalizer_iff]
      intro n
      have h1 := mem_normalizer_iff.mp (hHL (hTH ht)) n
      have h2 := mem_normalizer_iff.mp (Subgroup.le_normalizer (hTN ht)) n
      simp only [mem_inf] at h1 h2 ⊢
      exact and_congr h1 h2
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.perfectResidual ↥(L ⊓ NC))
    rw [hA]
    exact hTB.trans h
  have hloc : LocalSQTK G := (qtkeCore_of_cat hnab hK).1
  have hO2 : pCoreOf 2 NC ≠ ⊥ := fun hb => hC1 (le_bot_iff.mp (hb ▸ hCO))
  have hAl : A ∈ lFamily T := hAloc.2.1
  obtain ⟨KC, ⟨hKC, hAK⟩, huniq⟩ := existsUnique_cComp_of_lFamily h39 hloc hO2 hTs hANC hAl
  have hKn : (KC.subgroupOf NC).Normal := Vol2Native.lemma_1_2_4_normal hloc
    Vol2Native.a37ForSQTKCat_proved Vol2.Ch10.SecA.a38ForSQTKCat_proved hO2 hTs hAl hAK hKC hTA
  have hKNC : KC ≤ NC := le_of_mem_cComp hKC
  have hOKO : pCoreOf 2 KC ≤ pCoreOf 2 NC :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKC)
  have hOKX : pCoreOf 2 KC ≤ normalizer (X : Set G) := hOKO.trans (hO2T.trans hTX)
  have hYK : Y ≤ KC := hYA.trans hAK
  have hXK : X ≤ KC := hXleY.trans hYK
  have hYX : Y ≤ normalizer (X : Set G) := (hYA.trans hAL).trans (hLH.trans hHX)
  have hYX' : Y.subgroupOf KC ≤ normalizer ((X.subgroupOf KC : Subgroup KC) : Set KC) :=
    fun y hy => mem_normalizer_subgroupOf_of_mem (hYX (mem_subgroupOf.mp hy))
  let e₁ : X.subgroupOf KC ≃* X := subgroupOfEquivOfLe hXK
  let e₂ : X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC) ≃* X ⧸ CFSG.pCore 2 X :=
    QuotientGroup.congr _ _ e₁ (CFSG.pCore_map_iso 2 e₁)
  have hP' : IsPGroup p (X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC)) :=
    IsPGroup.of_equiv hXp e₂.symm
  have hnq : ¬ CFSG.IsQuasisimple (↥KC ⧸ CFSG.pCore 2 ↥KC) →
      (X.subgroupOf KC).Characteristic ∧ NC ≤ normalizer (X : Set G) := by
    intro hq
    have hSQT : CFSG.IsStronglyQuasithin KC :=
      NQRigid.isStronglyQuasithin_of_le hKNC (hloc NC hO2).1
    have hLC : CFSG.IsCComponent (⊤ : Subgroup KC) := by
      have h1 := subgroupOf_mem_cComp (cComp_mem_of_le hKC le_rfl hKNC)
      rw [subgroupOf_self] at h1
      exact mem_cComp_top_iff_isCComponent.mp h1
    have := hY
    have hY' : Group.IsPerfect (Y.subgroupOf KC) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hYK).symm.toMonoidHom)
        (subgroupOfEquivOfLe hYK).symm.surjective
    have hX2' : NoPQuotient 2 (X.subgroupOf KC) :=
      CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_surjective e₁.symm.toMonoidHom
        e₁.symm.surjective hX2
    have hexp' : Monoid.exponent (X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC)) = p :=
      (Monoid.exponent_eq_of_mulEquiv e₂).trans hexp
    have hrank' : CFSG.pRank p (X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC)) = 2 :=
      (CFSG.QuasithinUnique.Setup.Campbell.pRank_eq_of_mulEquiv e₂ p).trans hrank
    obtain ⟨Θ, hΘ⟩ := exists_residual_subgroupOf_equiv hXK
    have hW' : Nat.card ((X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC)) ⧸
        frattini (X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC))) = p ^ 2 :=
      (Nat.card_congr Θ.toEquiv).trans hW
    have hnt : ∃ y : Y.subgroupOf KC, ∃ w,
        normalizerResidualAction (X.subgroupOf KC) (inclusion hYX' y) w ≠ w := by
      obtain ⟨l, hlL, hl1⟩ := hLW
      obtain ⟨y, hyY, hyl⟩ := hψ l hlL
      obtain ⟨w, hw⟩ : ∃ w, normalizerFrattiniConj X y w ≠ w := by
        by_contra hall
        simp only [not_exists, not_not] at hall
        apply hl1
        rw [← hyl]
        exact MulEquiv.ext hall
      refine ⟨⟨⟨y, hYK hyY⟩, hyY⟩, Θ.symm w, fun heq => hw ?_⟩
      have h1 := congrArg Θ heq
      rw [hΘ, MulEquiv.apply_symm_apply] at h1
      exact h1
    have hirr' : ∀ U : Subgroup ((X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC)) ⧸
        frattini (X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC))),
        (∀ y : Y.subgroupOf KC, ∀ u ∈ U,
          normalizerResidualAction (X.subgroupOf KC) (inclusion hYX' y) u ∈ U) →
          U = ⊥ ∨ U = ⊤ := by
      intro U hU
      rcases hirr (U.map Θ.toMonoidHom) (by
          rintro l hlL _ ⟨u, hu, rfl⟩
          obtain ⟨y, hyY, hyl⟩ := hψ l hlL
          refine ⟨_, hU ⟨⟨y, hYK hyY⟩, hyY⟩ u hu, ?_⟩
          have h1 := hΘ (inclusion hYX' ⟨⟨y, hYK hyY⟩, hyY⟩) u
          rw [← hyl]
          exact h1) with h0 | h1
      · left
        exact (Subgroup.map_eq_bot_iff_of_injective _ Θ.injective).mp h0
      · right
        rw [eq_top_iff]
        intro u _
        have hu : Θ u ∈ U.map Θ.toMonoidHom := by
          rw [h1]
          exact Subgroup.mem_top _
        obtain ⟨u', hu', he⟩ := hu
        rw [Θ.injective he] at hu'
        exact hu'
    have hNX' : CFSG.pCore 2 ↥KC ≤ normalizer ((X.subgroupOf KC : Subgroup KC) : Set KC) := by
      intro k hk
      apply mem_normalizer_subgroupOf_of_mem
      apply hOKX
      exact Subgroup.mem_map_of_mem KC.subtype hk
    obtain ⟨-, -, -, -, -, -, -, hXc, -⟩ :=
      normalized_two_core_forces_original_witness_canonicity_in_nonquasisimple_overgroup
        hSQT hLC hq hY' hp2 (fun x hx => hXleY hx) hYX' hX2' hP' hexp' hrank' hW' hnt hirr'
        hNX' _ _ _ rfl rfl rfl
    exact ⟨hXc, le_normalizer_of_characteristic_subgroupOf hKNC hKn hXK hXc⟩
  have hesc : ¬ NC ≤ normalizer (X : Set G) →
      CFSG.IsQuasisimple (↥KC ⧸ CFSG.pCore 2 ↥KC) ∧ ¬ (X.subgroupOf KC).Normal ∧ A < KC := by
    intro hNX
    have hq : CFSG.IsQuasisimple (↥KC ⧸ CFSG.pCore 2 ↥KC) := by
      by_contra hq
      exact hNX (hnq hq).2
    have hXnK : ¬ (X.subgroupOf KC).Normal := by
      intro hXn'
      have hXY' : ⁅X.subgroupOf KC, Y.subgroupOf KC⁆ = X.subgroupOf KC := by
        apply Subgroup.map_injective KC.subtype_injective
        rw [Subgroup.map_commutator, map_subgroupOf_eq_of_le hXK, map_subgroupOf_eq_of_le hYK,
          hXY]
      have h1 := le_pCore_of_normal_of_isQuasisimple hq hP' hXY'
      have hXO : X ≤ pCoreOf 2 KC := by
        intro x hx
        have hx' : (⟨x, hXK hx⟩ : KC) ∈ CFSG.pCore 2 ↥KC := h1 hx
        exact ⟨_, hx', rfl⟩
      have hX2g : IsPGroup 2 X := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 KC).to_le hXO
      have htop := hX2 ⊥ (hX2g.of_equiv (QuotientGroup.quotientBot).symm)
      have hX1 : Nat.card X = 1 := by
        rw [← Subgroup.card_top, ← htop, Subgroup.card_bot]
      have hW1 : Nat.card (WPlane X) ∣ 1 := by
        rw [← hX1]
        exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)
      rw [hW] at hW1
      have hp1 := (Fact.out : p.Prime).one_lt
      have h3 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp1
      have h4 := Nat.le_of_dvd one_pos hW1
      omega
    refine ⟨hq, hXnK, lt_of_le_of_ne hAK fun hAKe => hXnK ?_⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hXK, ← hAKe]
    exact hAL.trans (hLH.trans hHX)
  exact ⟨hTN, hNtop, hCO, hTs, hANC, hAloc, hTA, KC, ⟨hKC, hAK⟩, fun K' hK' => huniq K' hK',
    hKn, hXY, hXleY, hYA, hAK, hOKO, hO2T, hOKX, hnq, hesc⟩

theorem escaping_characteristic_normalizer_has_proper_original_local_of
    (h39 : SQTKCLayerPerfectResidual)
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G)
    {T H L : Subgroup G} (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) (hLH : L ≤ H)
    (hLn : (L.subgroupOf H).Normal) (hHLT : H = L ⊔ T) (hLC : L ∈ cComp L) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXn : (X.subgroupOf H).Normal) (hX2 : NoPQuotient 2 X)
    (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrank : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) (hW : Nat.card (WPlane X) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    (hirr : ∀ V : Subgroup (WPlane X),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
        V = ⊥ ∨ V = ⊤) :
    let R := pCoreOf 2 (X ⊔ T)
    let Y := (CFSG.perfectResidual ↥(L ⊓ normalizer (R : Set G))).map
      (L ⊓ normalizer (R : Set G)).subtype
    ∀ C : Subgroup G, C ≠ ⊥ → C ≤ R → (C.subgroupOf R).Characteristic →
      let A := (CFSG.perfectResidual ↥(L ⊓ normalizer (C : Set G))).map
        (L ⊓ normalizer (C : Set G)).subtype
      T ≤ normalizer (C : Set G) ∧ normalizer (C : Set G) ≠ ⊤ ∧
        C ≤ pCoreOf 2 (normalizer (C : Set G)) ∧ IsSylowTwoOf T (normalizer (C : Set G)) ∧
        A ≤ normalizer (C : Set G) ∧ quasithinIsLocal T A ∧ T ≤ normalizer (A : Set G) ∧
        ∃ KC : Subgroup G, (KC ∈ cComp (normalizer (C : Set G)) ∧ A ≤ KC) ∧
          (∀ K' : Subgroup G, K' ∈ cComp (normalizer (C : Set G)) ∧ A ≤ K' → K' = KC) ∧
          (KC.subgroupOf (normalizer (C : Set G))).Normal ∧
          ⁅X, Y⁆ = X ∧ X ≤ Y ∧ Y ≤ A ∧ A ≤ KC ∧
          pCoreOf 2 KC ≤ pCoreOf 2 (normalizer (C : Set G)) ∧
          pCoreOf 2 (normalizer (C : Set G)) ≤ T ∧ pCoreOf 2 KC ≤ normalizer (X : Set G) ∧
          (¬ CFSG.IsQuasisimple (↥KC ⧸ CFSG.pCore 2 ↥KC) →
            (X.subgroupOf KC).Characteristic ∧
              normalizer (C : Set G) ≤ normalizer (X : Set G)) ∧
          (¬ normalizer (C : Set G) ≤ normalizer (X : Set G) →
            CFSG.IsQuasisimple (↥KC ⧸ CFSG.pCore 2 ↥KC) ∧ ¬ (X.subgroupOf KC).Normal ∧
              A < KC) := by
  intro R Y C hC1 hCR hCc A
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hAloc, -, hXY, hXleY, hYA, hψ⟩ := char_normalizer_residual_in_G hT hTH hLH hLn hHLT
    hLC hp hp5 hXL hXn hX2 hXp hW hLW hirr C hC1 hCR hCc
  have hYp : Group.IsPerfect Y := by
    have := (CFSG.perfect_residual_characterization
      (G := ↥(L ⊓ normalizer (R : Set G)))).2.2.1
    exact Group.IsPerfect.map _
  exact escaping_characteristic_normalizer_core h39 hnab hK hT hTH hLH hLn (by omega) hXL hXn
    hX2 hXp hexp hrank hW hLW hirr hC1 hCR hCc hYp rfl hAloc hXY hXleY hYA hψ

end NodeThree

end CFSG.Quasithin.H13.NQBlock
