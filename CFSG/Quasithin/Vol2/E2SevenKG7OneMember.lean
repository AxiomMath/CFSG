module

public import CFSG.Quasithin.Vol2.E2SevenKG7OneS6
public import CFSG.Quasithin.Vol2.E2SevenKG7OneModel
public import CFSG.Quasithin.Vol2.E2SevenKG7Large

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open Ch3E213M.P6E

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem kg7One_map_subgroupOf {X Y : Subgroup G} (hYX : Y ≤ X) :
    (Y.subgroupOf X).map X.subtype = Y :=
  Subgroup.map_subgroupOf_eq_of_le hYX

omit [Finite G] in
theorem kg7One_mem_normalizer_iff {X U : Subgroup G} (hUX : U ≤ X) (y : ↥X) :
    y ∈ Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X) ↔
      (y : G) ∈ Subgroup.normalizer (U : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hUX, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem kg7One_mem_normalizer_map_iff {X : Subgroup G} (P : Subgroup ↥X) (y : ↥X) :
    (y : G) ∈ Subgroup.normalizer ((P.map X.subtype : Subgroup G) : Set G) ↔
      y ∈ Subgroup.normalizer (P : Set ↥X) := by
  have hP : (P.map X.subtype).subgroupOf X = P :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective P
  rw [← kg7One_mem_normalizer_iff (Subgroup.map_subtype_le P) y, hP]

omit [Finite G] in
theorem kg7One_sylow_map {X : Subgroup G} {S J : Subgroup ↥X} (h : IsSylowTwoOf S J) :
    IsSylowTwoOf (S.map X.subtype) (J.map X.subtype) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map _, ?_⟩
  show ¬ 2 ∣ (S.map X.subtype).relIndex (J.map X.subtype)
  rw [Subgroup.relIndex_map_map_of_injective _ _ X.subtype_injective]
  exact h.2.2

omit [Finite G] in
theorem kg7One_map_conj {X : Subgroup G} (Y : Subgroup ↥X) (x : ↥X) :
    (Y.map (MulAut.conj x⁻¹).toMonoidHom).map X.subtype =
      (Y.map X.subtype).map (MulAut.conj (x : G)⁻¹).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem exists_isInIHTVC_sp4_one {X T M K V : Subgroup G} (h : Hyp28 X T M V)
    (hker0 : kerIn M X = ⊥) (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set G))
    (hC : X ⊓ Subgroup.centralizer (K : Set G) = ⊥) (hKT : K ⊔ T = X)
    (hSp : IsSp4Prime 1 ↥K) (hD : IsDiagramNontrivial T K (T ⊓ K))
    (hMK : M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hnX : E1.nParam X = 1) (hV4 : 4 ≤ Nat.card V) :
    ∃ I : Subgroup G, ASInputs.IsInIHTVC X T M V I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := h.minParabolic
  have hTX : T ≤ X := hmp.isSylow.1
  have hMX : M ≤ X := hmp.maximal.1.le
  have hTM : T ≤ M := hmp.le
  have hVX : V ≤ X := h.le_H
  haveI hKn : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN
  have hTsyl : IsSylowTwoOf (T.subgroupOf X) ⊤ :=
    CFSG.Quasithin.Ch3E213M.P5.isSylowTwoOf_subgroupOf_top hmp.isSylow
  have hCx : ∀ a : ↥X, (∀ x ∈ K.subgroupOf X, a * x = x * a) → a = 1 := by
    intro a ha
    have h1 : (a : G) ∈ X ⊓ Subgroup.centralizer (K : Set G) := by
      refine ⟨a.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      have h2 := congrArg Subtype.val (ha ⟨k, hKX hk⟩ (Subgroup.mem_subgroupOf.mpr hk))
      exact h2.symm
    rw [hC, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hAlt : IsAlt 6 ↥(K.subgroupOf X) := by
    obtain ⟨e₀⟩ : IsAlt 6 ↥K := hSp
    exact ⟨(Subgroup.subgroupOfEquivOfLe hKX).trans e₀⟩
  have hKS : K.subgroupOf X ⊔ T.subgroupOf X = ⊤ :=
    CFSG.Quasithin.Ch3E213M.subgroupOf_sup_eq_top hKT.symm
  have hSB : T.subgroupOf X ≤ M.subgroupOf X := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hTM (Subgroup.mem_subgroupOf.mp hy))
  have hES : V.subgroupOf X ≤ T.subgroupOf X := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (h.le_T (Subgroup.mem_subgroupOf.mp hy))
  have hSE : T.subgroupOf X ≤ Subgroup.normalizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    intro y hy
    exact (kg7One_mem_normalizer_iff hVX y).mpr (h.normal_T (Subgroup.mem_subgroupOf.mp hy))
  have hE2 : ∀ x ∈ V.subgroupOf X, x * x = 1 := fun x hx => by
    apply Subtype.ext
    have h1 := h.elem.2 (x : G) (Subgroup.mem_subgroupOf.mp hx)
    simpa [sq] using h1
  have hE4 : 4 ≤ Nat.card (V.subgroupOf X) := by
    have : Nat.card (V.subgroupOf X) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv
    omega
  have hTKX : (T ⊓ K).subgroupOf X = T.subgroupOf X ⊓ K.subgroupOf X := by
    ext y
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hdiag : ∀ P : Subgroup ↥X, IsMaxParabolic2 (K.subgroupOf X) P →
      (K.subgroupOf X) ⊓ Subgroup.normalizer
          ((T.subgroupOf X ⊓ K.subgroupOf X : Subgroup ↥X) : Set ↥X) ≤ P →
        ¬ T.subgroupOf X ≤ Subgroup.normalizer (P : Set ↥X) := by
    intro P hP hle hTP
    have hmax := isMaxParabolic2_map_subtype hKX hP
    have hle' : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ P.map X.subtype := by
      rintro g ⟨hgK, hgN⟩
      have hgX : (⟨g, hKX hgK⟩ : ↥X) ∈ K.subgroupOf X := Subgroup.mem_subgroupOf.mpr hgK
      have hgN' : (⟨g, hKX hgK⟩ : ↥X) ∈
          Subgroup.normalizer ((T.subgroupOf X ⊓ K.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
        rw [← hTKX]
        exact (kg7One_mem_normalizer_iff (inf_le_left.trans hTX) _).mpr hgN
      exact ⟨_, hle ⟨hgX, hgN'⟩, rfl⟩
    have hT' : T ≤ Subgroup.normalizer (P.map X.subtype : Set G) := by
      intro t ht
      have htX : (⟨t, hTX ht⟩ : ↥X) ∈ T.subgroupOf X := Subgroup.mem_subgroupOf.mpr ht
      exact (kg7One_mem_normalizer_map_iff P ⟨t, hTX ht⟩).mpr (hTP htX)
    exact hD (P.map X.subtype) hmax hle' hT'
  have hNorm : ∀ y : ↥X, y ∈ Subgroup.normalizer
      ((T.subgroupOf X ⊓ K.subgroupOf X : Subgroup ↥X) : Set ↥X) ↔
        (y : G) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    intro y
    rw [← hTKX]
    exact kg7One_mem_normalizer_iff (inf_le_left.trans hTX) y
  have key : ∀ g : G, g ∈ M ⊓ K ↔ g ∈ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    fun g => by rw [hMK]
  have hBorel : ∃ S₀ : Subgroup ↥X, IsSylowTwoOf S₀ (K.subgroupOf X) ∧
      M.subgroupOf X ⊓ K.subgroupOf X =
        K.subgroupOf X ⊓ Subgroup.normalizer (S₀ : Set ↥X) := by
    refine ⟨T.subgroupOf X ⊓ K.subgroupOf X,
      A4.isSylowTwoOf_inf_normal hTsyl le_top
        (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge, ?_⟩
    ext y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hNorm y]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, ((key y).mp ⟨Subgroup.mem_subgroupOf.mp h1, Subgroup.mem_subgroupOf.mp h2⟩).2⟩
    · rintro ⟨h2, h3⟩
      have h4 := (key y).mpr ⟨Subgroup.mem_subgroupOf.mp h2, h3⟩
      exact ⟨Subgroup.mem_subgroupOf.mpr h4.1, h2⟩
  obtain ⟨⟨σ, hσS, hσE⟩, hJN, ⟨x, hxK, hJgen, hBJ, hSylJ, -, hNJ⟩⟩ :=
    Ch3E213M.P6E.model_sp4_one_ext hTsyl hCx hAlt hKS hdiag hBorel hSB hES hSE hE2 hE4
  set I : Subgroup G := (K.subgroupOf X ⊔ V.subgroupOf X).map X.subtype with hIdef
  have hIX : I ≤ X := Subgroup.map_subtype_le _
  have hkI : ∀ k : ↥(K.subgroupOf X ⊔ V.subgroupOf X), ((k : ↥X) : G) ∈ I :=
    fun k => Subgroup.mem_map_of_mem X.subtype k.2
  have hmapM : (M.subgroupOf X ⊓ (K.subgroupOf X ⊔ V.subgroupOf X)).map X.subtype = M ⊓ I := by
    rw [Subgroup.map_inf _ _ _ X.subtype_injective, kg7One_map_subgroupOf hMX]
  have hmapT : (T.subgroupOf X ⊓ (K.subgroupOf X ⊔ V.subgroupOf X)).map X.subtype = T ⊓ I := by
    rw [Subgroup.map_inf _ _ _ X.subtype_injective, kg7One_map_subgroupOf hTX]
  have hMI : M ⊓ I = T ⊓ I := by
    rw [← hmapM, ← hmapT, hBJ]
  have hSylI : IsSylowTwoOf (T ⊓ I) I := by
    have h := kg7One_sylow_map hSylJ
    rwa [hmapT] at h
  have hNM : kerIn (M ⊓ I) I ≤ M ⊓ I := fun n hn => by
    have h1 := hn 1 I.one_mem
    simpa using h1
  have hker : kerIn (M ⊓ I) I = ⊥ := by
    have hNT : kerIn (M ⊓ I) I ≤ T ⊓ I := hMI ▸ hNM
    have hNI : kerIn (M ⊓ I) I ≤ I := hNM.trans inf_le_right
    have hNX : kerIn (M ⊓ I) I ≤ X := hNI.trans hIX
    have hNP : IsPGroup 2 (kerIn (M ⊓ I) I) := hSylI.2.1.to_le hNT
    have hN' := hNJ ((kerIn (M ⊓ I) I).subgroupOf X) ?_ hNP.comap_subtype ?_
    · rw [← kg7One_map_subgroupOf hNX, hN', Subgroup.map_bot]
    · intro y hy
      obtain ⟨j, hj, hjy⟩ := Subgroup.mem_map.mp (hNI (Subgroup.mem_subgroupOf.mp hy))
      have hjy' : j = y := Subtype.ext hjy
      exact hjy' ▸ hj
    · refine ⟨fun n hn g => ?_⟩
      have hn1 : ((n : ↥X) : G) ∈ kerIn (M ⊓ I) I :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hn)
      have hnI : ((n : ↥X) : G) ∈ I := hkI n
      have hgI : ((g : ↥X) : G) ∈ I := hkI g
      have hc := (kerIn_subgroupOf_normal (M ⊓ I) I).conj_mem ⟨((n : ↥X) : G), hnI⟩
        (Subgroup.mem_subgroupOf.mpr hn1) ⟨((g : ↥X) : G), hgI⟩
      apply Subgroup.mem_subgroupOf.mpr
      apply Subgroup.mem_subgroupOf.mpr
      simpa using Subgroup.mem_subgroupOf.mp hc
  have hgI : ((x : ↥X) : G)⁻¹ ∈ I :=
    I.inv_mem (Subgroup.mem_map_of_mem X.subtype
      ((le_sup_left : K.subgroupOf X ≤ K.subgroupOf X ⊔ V.subgroupOf X) hxK))
  have hIgen : I = V ⊔ B6.conjSub ((x : ↥X) : G)⁻¹ V := by
    have h : I = (V.subgroupOf X ⊔ CFSG.conjugate (V.subgroupOf X) x).map X.subtype := by
      rw [← hJgen]
    rw [h, Subgroup.map_sup, kg7One_map_subgroupOf hVX]
    congr 1
    unfold CFSG.conjugate
    rw [kg7One_map_conj, kg7One_map_subgroupOf hVX]
    rfl
  let eIJ : ↥(K.subgroupOf X ⊔ V.subgroupOf X) ≃* ↥I :=
    (K.subgroupOf X ⊔ V.subgroupOf X).equivMapOfInjective X.subtype X.subtype_injective
  let Θ : StarQuot (M ⊓ I) I ≃* Equiv.Perm (Fin 6) :=
    (starQuotEquivOfBot hker).trans (eIJ.symm.trans σ)
  have hL : ∀ Y : Subgroup G, (Y.subgroupOf I).map eIJ.symm.toMonoidHom =
      (Y.subgroupOf X).subgroupOf (K.subgroupOf X ⊔ V.subgroupOf X) := by
    intro Y
    ext k
    constructor
    · rintro ⟨i, hi, hik⟩
      have hki : ((k : ↥X) : G) = ((i : ↥I) : G) := by
        rw [← hik]
        exact congrArg Subtype.val (eIJ.apply_symm_apply i)
      exact Subgroup.mem_subgroupOf.mpr (by
        show ((k : ↥X) : G) ∈ Y
        rw [hki]
        exact Subgroup.mem_subgroupOf.mp hi)
    · intro hk
      refine ⟨eIJ k, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mp hk
      · exact eIJ.symm_apply_apply k
  have hstar : ∀ Y : Subgroup G,
      (star (M ⊓ I) I Y).map Θ.toMonoidHom =
        ((Y.subgroupOf X).subgroupOf (K.subgroupOf X ⊔ V.subgroupOf X)).map σ.toMonoidHom := by
    intro Y
    have h1 : (star (M ⊓ I) I Y).map Θ.toMonoidHom =
        ((star (M ⊓ I) I Y).map (starQuotEquivOfBot hker).toMonoidHom).map
          (eIJ.symm.trans σ).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [h1, map_star_starQuotEquivOfBot hker Y, ← hL Y, Subgroup.map_map]
    rfl
  have hTJ : ((T ⊓ I).subgroupOf X).subgroupOf (K.subgroupOf X ⊔ V.subgroupOf X) =
      (T.subgroupOf X ⊓ (K.subgroupOf X ⊔ V.subgroupOf X)).subgroupOf
        (K.subgroupOf X ⊔ V.subgroupOf X) := by
    ext k
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hk
      exact ⟨hk.1, k.2⟩
    · intro hk
      exact ⟨hk.1, hkI k⟩
  have hΘT : (star (M ⊓ I) I (T ⊓ I)).map Θ.toMonoidHom = S06 := by
    rw [hstar, hTJ]
    exact hσS
  have hΘM : (star (M ⊓ I) I (M ⊓ I)).map Θ.toMonoidHom = S06 := by
    rw [congrArg (star (M ⊓ I) I) hMI]
    exact hΘT
  have hΘV : (star (M ⊓ I) I V).map Θ.toMonoidHom = Z6 := by
    rw [hstar]
    exact hσE
  have hBorelG : E2.IsBorelIn ⊤ (star (M ⊓ I) I (M ⊓ I)) := by
    refine isBorelIn_of_map_equiv Θ ?_
    rw [hΘM]
    refine ⟨S06, isSylowTwoOf_S06, ?_⟩
    rw [top_inf_eq]
    exact le_antisymm Subgroup.le_normalizer normalizer_S06_le
  have hcent : star (M ⊓ I) I V ≤
      Subgroup.centralizer ((star (M ⊓ I) I (T ⊓ I) : Subgroup (StarQuot (M ⊓ I) I)) :
        Set (StarQuot (M ⊓ I) I)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hy' : Θ y ∈ Z6 := by
      rw [← hΘV]
      exact Subgroup.mem_map_of_mem _ hy
    have hs' : Θ s ∈ S06 := by
      rw [← hΘT]
      exact Subgroup.mem_map_of_mem _ hs
    have hc : Θ s * Θ y = Θ y * Θ s :=
      Subgroup.mem_centralizer_iff.mp (Z6_le_centralizer_S06 hy') (Θ s) hs'
    apply Θ.injective
    rw [map_mul, map_mul]
    exact hc
  have hroot : ∀ P : Subgroup (StarQuot (M ⊓ I) I), IsMaxParabolic2 ⊤ P →
      star (M ⊓ I) I (M ⊓ I) ≤ P → ¬ star (M ⊓ I) I V ≤ ASInputs.rootGroupOf P := by
    intro P hP hBP hVP
    have hP' : IsMaxParabolic2 ⊤ (P.map Θ.toMonoidHom) := by
      have h := CFSG.Quasithin.Ch3E213M.P5.isMaxParabolic2_map_equiv Θ hP
      rwa [Subgroup.map_top_of_surjective Θ.toMonoidHom Θ.surjective] at h
    have hS6 : S06 ≤ P.map Θ.toMonoidHom := by
      rw [← hΘM]
      exact Subgroup.map_mono hBP
    have hZ : Z6 ≤ ASInputs.rootGroupOf (P.map Θ.toMonoidHom) := by
      rw [← hΘV, ← map_rootGroupOf_equiv Θ P]
      exact Subgroup.map_mono hVP
    exact not_le_rootGroupOf_Z6 hP' hS6 hZ
  have hO : ∃ n : ℕ, E2.IsSp4Prime n ↥(oTwoUpper (⊤ : Subgroup (StarQuot M X))) :=
    ⟨1, isSp4Prime_oTwoUpper_star hmp hker0 hKX hXN hC hKT hSp⟩
  have hPC : IsSylowTwoOf (pCoreOf 2 (kerIn (M ⊓ I) I)) (kerIn (M ⊓ I) I) := by
    rw [hker]
    have hb : pCoreOf 2 (⊥ : Subgroup G) = ⊥ :=
      le_bot_iff.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 ⊥)
    rw [hb]
    refine ⟨le_rfl, IsPGroup.of_bot, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    norm_num
  refine ⟨I, hIX, ⟨((x : ↥X) : G)⁻¹, hgI, hIgen⟩, hSylI, hPC, 1, ⟨1, ?_⟩,
    Or.inr (Or.inr ⟨hO, le_rfl, Or.inr ⟨rfl, ⟨Θ⟩⟩, hBorelG, hcent, hroot⟩)⟩
  rw [hnX]
  norm_num

end E2

end CFSG.Quasithin

end
