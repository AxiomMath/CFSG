module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323MS
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323Mod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement Pointwise

namespace C45

variable {G : Type} [Group G]

theorem isTwoLocal_map_conj {H : Subgroup G} (hH : IsTwoLocal H) (g : G) :
    IsTwoLocal (H.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨P, hP, hP2, rfl⟩ := hH
  refine ⟨P.map (MulAut.conj g).toMonoidHom, ?_, hP2.map _, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
    exact hP
  · exact Subgroup.map_equiv_normalizer_eq P (MulAut.conj g)

theorem map_conj_inv (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have e : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [e, Subgroup.map_id]

theorem isMaxTwoLocal_map_conj {M : Subgroup G} (hM : quasithinIsMaxTwoLocal M) (g : G) :
    quasithinIsMaxTwoLocal (M.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨isTwoLocal_map_conj hM.1 g, fun H hH hMH => ?_⟩
  have h1 : M ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← map_conj_inv M g]
    exact Subgroup.map_mono hMH
  have h2 := hM.2 _ (isTwoLocal_map_conj hH g⁻¹) h1
  rw [← h2, Subgroup.map_map]
  have e : ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [e, Subgroup.map_id]

theorem normalizer_le [Finite G] {M : Subgroup G} (hM : quasithinIsMaxTwoLocal M) :
    Subgroup.normalizer (M : Set G) ≤ M := by
  obtain ⟨⟨P, hP, hP2, hMP⟩, hmax⟩ := hM
  have hPM : P ≤ pCoreOf 2 M := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ hP2
    · rw [hMP]
      exact Subgroup.le_normalizer
    · rw [hMP]
  have hO : pCoreOf 2 M ≠ ⊥ := fun h => hP (le_bot_iff.mp (h ▸ hPM))
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 M : Set G)) :=
    ⟨_, hO, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M, rfl⟩
  have heq := hmax _ hloc (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  intro x hx
  rw [← heq]
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M hx

theorem mem_normalizer_zpowers {x y : G} (h : x * y = y * x) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  have hc : ∀ n : ℤ, x * y ^ n * x⁻¹ = y ^ n := fun n => by
    rw [(Commute.zpow_right h n).eq]
    group
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, (hc n).symm⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' : y ^ n = x * w * x⁻¹ := hn
    calc y ^ n = x⁻¹ * (x * y ^ n * x⁻¹) * x := by group
      _ = x⁻¹ * (x * w * x⁻¹) * x := by rw [hc n, hn']
      _ = w := by group

theorem card_sup_mul_card_inf [Finite G] {X N : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) =
      Nat.card X * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

variable [Finite G] {T M L D : Subgroup G}

theorem false_of_card
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    {ZL : Subgroup G} (hZLZ : ZL ≤ quasithinOmegaOneCenter T)
    (hZLL : ZL ≤ Subgroup.centralizer (L : Set G)) (h4 : 4 ≤ Nat.card ZL)
    (h2 : Nat.card ↥(quasithinOmegaOneCenter T) ≤ 2 * Nat.card ZL) : False := by
  set Z := quasithinOmegaOneCenter T with hZ
  obtain ⟨d, hdD, hdM⟩ : ∃ d ∈ D, d ∉ M := by
    by_contra hcon
    push Not at hcon
    exact h.not_D_le hcon
  have hZT : Z ≤ T := (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) :=
    (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_right
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hZC hb) a (hZT ha)
  have hdZ : d ∈ Subgroup.normalizer (Z : Set G) :=
    Hyp331.normalizer_le_normalizer_of_characteristic hZT
      (CFSG.QuasithinUnique.L246C127.characteristic_omegaOneCenter T) (h.DN hdD)
  set ZLd := ZL.map (MulAut.conj d).toMonoidHom with hZLd
  have hZLdZ : ZLd ≤ Z := by
    rintro _ ⟨w, hw, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hdZ w).mp (hZLZ hw)
  have hcardd : Nat.card ZLd = Nat.card ZL :=
    Subgroup.card_map_of_injective (MulAut.conj d).injective
  have hN : ZL ≤ Subgroup.normalizer (ZLd : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
      hZab b (hZLdZ hb) a (hZLZ ha))
  have hprod := card_sup_mul_card_inf hN
  have hsup : Nat.card (ZL ⊔ ZLd : Subgroup G) ≤ Nat.card Z :=
    Subgroup.card_le_of_le (sup_le hZLZ hZLdZ)
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ ZL ⊓ ZLd, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : ZL ⊓ ZLd = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [h1, Subgroup.card_bot, mul_one, hcardd] at hprod
    nlinarith
  obtain ⟨w, hw, hwz⟩ := hz.2
  have hz2 : z ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenter T (hZLZ hz.1)
  have hcomm : ∀ {a : G}, a ∈ ZL → ∀ x ∈ L ⊔ T, x * a = a * x := by
    intro a ha x hx
    have hle : L ⊔ T ≤ Subgroup.centralizer ({a} : Set G) := by
      refine sup_le (fun l hl => ?_) (fun t ht => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (hZLL ha) l hl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (hZC (hZLZ ha)) t ht)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx))
  have hNz : Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ M := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine h.toSetup331.normalizer_le h38 h39 (Subgroup.zpowers_ne_bot.mpr hz1) ?_
      fun x hx => mem_normalizer_zpowers (hcomm hz.1 x hx)
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one]
  have hLTM : L ⊔ T ≤ M.map (MulAut.conj d⁻¹).toMonoidHom := by
    intro x hx
    have hxw := hcomm hw x hx
    have h1 : d * x * d⁻¹ * z = z * (d * x * d⁻¹) := by
      rw [← hwz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc d * x * d⁻¹ * (d * w * d⁻¹) = d * (x * w) * d⁻¹ := by group
        _ = d * (w * x) * d⁻¹ := by rw [hxw]
        _ = d * w * d⁻¹ * (d * x * d⁻¹) := by group
    refine ⟨d * x * d⁻¹, hNz (mem_normalizer_zpowers h1), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hMd : M.map (MulAut.conj d⁻¹).toMonoidHom = M :=
    (h.toSetup331.isUniqueM h38 h39).2 _ ⟨isMaxTwoLocal_map_conj h.maxM d⁻¹, hLTM⟩
  have hdN : d⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMd
  exact hdM (by simpa using M.inv_mem (normalizer_le h.maxM hdN))

omit [Finite G] in
theorem isE2_card_sq {m : ℕ} {X : Type} [Group X] (h : IsE2 m X) :
    Nat.card X = 2 ^ m ∧ ∀ x : X, x * x = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨?_, fun x => ?_⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi]
  · apply e.injective
    rw [map_mul, map_one]
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
    generalize Multiplicative.toAdd (e x) i = a
    revert a
    decide

theorem relIndex_eq (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    T.relIndex L = T.relIndex (L ⊔ T) := by
  have h1 := card_sup_mul_card_inf (X := T) (N := L) hTL
  have h2 := Subgroup.relIndex_mul_card T L
  have h3 := Subgroup.relIndex_mul_card T (L ⊔ T)
  rw [inf_of_le_left (le_sup_right : T ≤ L ⊔ T)] at h3
  rw [sup_comm] at h1
  have hT : 0 < Nat.card T := Nat.card_pos
  have hTL' : 0 < Nat.card (T ⊓ L : Subgroup G) := Nat.card_pos
  have this : T.relIndex L * (Nat.card (T ⊓ L : Subgroup G) * Nat.card T) =
      T.relIndex (L ⊔ T) * (Nat.card (T ⊓ L : Subgroup G) * Nat.card T) := by
    calc T.relIndex L * (Nat.card (T ⊓ L : Subgroup G) * Nat.card T) =
          (T.relIndex L * Nat.card (T ⊓ L : Subgroup G)) * Nat.card T := by ring
      _ = Nat.card T * Nat.card L := by rw [h2]; ring
      _ = Nat.card (L ⊔ T : Subgroup G) * Nat.card (T ⊓ L : Subgroup G) := h1.symm
      _ = (T.relIndex (L ⊔ T) * Nat.card T) * Nat.card (T ⊓ L : Subgroup G) := by rw [h3]
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hTL' hT) this

theorem card_le_two (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : IsModO2Surj L α)
    {U : Subgroup G} (β : ↥U →* Multiplicative (Fin 1 → Fin 3 → F))
    (hβi : Function.Injective β)
    (hβe : ∀ (a : ↥L) (u v : ↥U), (v : G) = a * u * a⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (β u) i))
    {Y : Subgroup G} (hYU : Y ≤ U) (hYC : Y ≤ Subgroup.centralizer (T : Set G)) :
    Nat.card Y ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  let f : ↥L →* L3.Γ := (Mod3323.toL3 hF).comp (e.toMonoidHom.comp α)
  have hf : Function.Surjective f := by
    intro γ
    let γ' : Matrix.SpecialLinearGroup (Fin 3) F :=
      Matrix.SpecialLinearGroup.map (Mod3323.toZ2 hF).symm.toRingHom γ
    obtain ⟨l, hl⟩ := hα.1 (e.symm γ')
    refine ⟨l, ?_⟩
    have h1 : e (α l) = γ' := by rw [hl, MulEquiv.apply_symm_apply]
    show Mod3323.toL3 hF (e (α l)) = γ
    rw [h1]
    apply Subtype.ext
    ext i j
    rw [Mod3323.toL3_apply, Matrix.SpecialLinearGroup.map_apply_coe]
    simp
  set I := (T.subgroupOf L).map f with hI
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hI2 : IsPGroup 2 I := (hT2.comap_of_injective L.subtype L.subtype_injective).map _
  have hidx : ¬ 2 ∣ I.index := by
    intro h2
    have h1 := Subgroup.index_map_dvd (T.subgroupOf L) hf
    have h3 : (T.subgroupOf L).index = T.relIndex (L ⊔ T) := by
      rw [← relIndex_eq hTL]
      rfl
    rw [h3] at h1
    exact h.toSetup331.isSylowTwoOf.2.2 (h2.trans h1)
  obtain ⟨v₀, hv₀⟩ := Mod3323.exists_fix hI2 hidx
  let φ : ↥Y → L3.Vec := fun y =>
    Mod3323.toZ2 hF ∘ Multiplicative.toAdd (β ⟨y, hYU y.2⟩) 0
  have hφ : ∀ y : ↥Y, φ y = 0 ∨ φ y = v₀ := by
    intro y
    refine hv₀ _ ?_
    rintro _ ⟨s, hs, rfl⟩
    have hsy : (s : G) * y * (s : G)⁻¹ = y := by
      have := Subgroup.mem_centralizer_iff.mp (hYC y.2) s hs
      rw [this]
      group
    have h1 := hβe s ⟨y, hYU y.2⟩ ⟨y, hYU y.2⟩ hsy.symm 0
    have hm : ((e (α s) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((α s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      have := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 F (e (α s))
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    show L3.act (Mod3323.toL3 hF (e (α s)))
      (Mod3323.toZ2 hF ∘ Multiplicative.toAdd (β ⟨y, hYU y.2⟩) 0) = _
    rw [Mod3323.act_toL3, hm, ← h1]
  have hinj : Function.Injective φ := by
    intro y y' hyy
    have h1 : Multiplicative.toAdd (β ⟨y, hYU y.2⟩) 0 =
        Multiplicative.toAdd (β ⟨y', hYU y'.2⟩) 0 := by
      funext i
      exact (Mod3323.toZ2 hF).injective (congrFun hyy i)
    have h2 : β ⟨y, hYU y.2⟩ = β ⟨y', hYU y'.2⟩ := by
      apply Multiplicative.toAdd.injective
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      exact h1
    have h3 := congrArg Subtype.val (hβi h2)
    exact Subtype.ext h3
  let ψ : ↥Y → ↥({0, v₀} : Finset L3.Vec) := fun y =>
    ⟨φ y, by rcases hφ y with h0 | h0 <;> simp [h0]⟩
  have hψ : Function.Injective ψ := fun y y' hyy => hinj (congrArg Subtype.val hyy)
  calc Nat.card Y ≤ Nat.card ↥({0, v₀} : Finset L3.Vec) := Nat.card_le_card_of_injective ψ hψ
    _ = ({0, v₀} : Finset L3.Vec).card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 2 := Finset.card_le_two

omit [Finite G] in
theorem card_sl_eq {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))}
    (hα₂ : IsModO2Surj L α₂) {F : Type} [Field F]
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : IsModO2Surj L α) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 168 := by
  have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv,
      ← hα.2, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα.1).toEquiv]
  have h2 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
    rw [← hα₂.2, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α₂ hα₂.1).toEquiv,
      ← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3
        (ZMod 2)).toEquiv]
    exact card_L3Γ
  rw [h1, h2]

theorem not_isC134Case5
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : ¬ IsC134Case5 (L ⊔ T) T L := by
  rintro ⟨-, h5⟩
  exact MS3323.false_of_le_center h h38 h39 hTL (h5 T h.toSetup331.isSylowTwoOf le_rfl).1

theorem not_isC134Case4
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂) :
    ¬ IsC134Case4 (L ⊔ T) T L := by
  rintro ⟨⟨n, F, _, _, α, hFc, hα, hE2, hCZ, hZQ, -, hU, -⟩, -⟩
  set Q := c134Q (L ⊔ T) L with hQ
  set Z := quasithinOmegaOneCenter T with hZdef
  have hF := Mod3323.card_eq_two hFc (card_sl_eq hα₂ hα)
  have hn : n = 1 := by
    have h2n : 2 ^ n = 2 ^ 1 := by rw [← hFc, hF, pow_one]
    exact Nat.pow_right_injective (le_refl 2) h2n
  subst hn
  obtain ⟨hC4, hCsq⟩ := isE2_card_sq hE2
  have hsyl := h.toSetup331.isSylowTwoOf
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hOL : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hx)
  have hQO : Q ≤ pCoreOf 2 (L ⊔ T) := commutator_le_left_of_le_normalizer hOL
  have hQT : Q ≤ T := hQO.trans (pCoreOf_le_of_isSylowTwoOf hsyl)
  have hZT : Z ≤ T := (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) :=
    (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_right
  set ZL := Z ⊓ Subgroup.centralizer (L : Set G) with hZL
  have hCZL : c134CQ (L ⊔ T) L ≤ ZL := by
    intro c hc
    have hcT : c ∈ T := hQT hc.1
    have hcC : c ∈ Subgroup.centralizer (T : Set G) :=
      Subgroup.centralizer_le (le_sup_right : T ≤ L ⊔ T) (hCZ hc).2
    have hc2 : c ^ 2 = 1 := by
      rw [pow_two]
      exact congrArg Subtype.val (hCsq ⟨c, hc⟩)
    exact ⟨Subgroup.subset_closure ⟨⟨hcT, hcC⟩, hc2⟩, hc.2⟩
  have hZL4 : 4 ≤ Nat.card ZL := by
    have := Subgroup.card_le_of_le hCZL
    rw [hC4] at this
    simpa using this
  obtain ⟨hLU, -, β, -, hβk, hβe⟩ := hU
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hβe' : ∀ (a : ↥L) (u v : ↥⁅centerOf Q, L⁆), (v : G) = a * u * a⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (β u) i) := fun a u v huv i => by
    simpa [moduleAct] using hβe a u v huv i
  have hZU : Nat.card (Z ⊓ ⁅centerOf Q, L⁆ : Subgroup G) ≤ 2 :=
    card_le_two h hTL hF hα β hβi hβe' inf_le_right (inf_le_left.trans hZC)
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVO : vPlus L T ≤ pCoreOf 2 (L ⊔ T) := hred.1.trans inf_le_left
  have hVC : vPlus L T ≤ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    hred.1.trans inf_le_right
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hVLQ : ⁅vPlus L T, L⁆ ≤ centerOf Q := by
    refine le_inf (Subgroup.commutator_mono hVO le_rfl) ?_
    exact (commutator_le_left_of_le_normalizer hLV).trans
      (hVC.trans (Subgroup.centralizer_le hQO))
  have hUQ : ⁅centerOf Q, L⁆ ≤ T :=
    (commutator_le_left_of_le_normalizer (fun x hx => ChiefCount.mem_normalizer_inf
      (mem_normalizer_commutator (hOL hx) (Subgroup.le_normalizer hx))
      (B2F.normalizer_le_normalizer_centralizer _ (mem_normalizer_commutator (hOL hx)
        (Subgroup.le_normalizer hx))))).trans (inf_le_left.trans hQT)
  have hZLU : ZL ≤ Subgroup.normalizer ((⁅centerOf Q, L⁆ : Subgroup G) : Set G) := fun z hz =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      Subgroup.mem_centralizer_iff.mp (hZC hz.1) u (hUQ hu))
  obtain ⟨-, hdec⟩ := h.vPlus_decomp
  rw [Hyp331.mPlus_eq_of_le hTL] at hdec
  have hZV : Z ≤ ZL ⊔ ⁅centerOf Q, L⁆ := by
    intro z hz
    have hzV : z ∈ vPlus L T := le_conjClosure _ _ hz
    rw [hdec] at hzV
    have hle : ⁅vPlus L T, L⁆ ⊔ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≤
        ZL ⊔ ⁅centerOf Q, L⁆ :=
      sup_le (hVLQ.trans (hZQ.le.trans (sup_le (hCZL.trans le_sup_left) le_sup_right)))
        le_sup_left
    exact hle hzV
  have hZle : Z ≤ ZL ⊔ (Z ⊓ ⁅centerOf Q, L⁆) :=
    (le_inf le_rfl hZV).trans (ChiefCount.inf_sup_le inf_le_left hZLU)
  have hprod := card_sup_mul_card_inf (X := ZL) (N := Z ⊓ ⁅centerOf Q, L⁆) fun z hz =>
    ChiefCount.mem_normalizer_inf
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp (hZC hz.1) y (hZT hy))) (hZLU hz)
  have hpos : 0 < Nat.card (ZL ⊓ (Z ⊓ ⁅centerOf Q, L⁆) : Subgroup G) := Nat.card_pos
  have h2 : Nat.card Z ≤ 2 * Nat.card ZL := by
    have h1 := Subgroup.card_le_of_le hZle
    nlinarith
  exact false_of_card h h38 h39 inf_le_left inf_le_right hZL4 h2

end C45

end CFSG.Quasithin.H13
