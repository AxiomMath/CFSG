module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveProofSL
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClAltSix

public section

namespace CFSG.StandardType

namespace FieldFiveSp

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix LayerCores LayerFacts ClNonsplit
  CFSG.LocalAnalysis.ComponentInitial

section Helpers

theorem natCast_card_ne_zero_of_pow_five {K : Type*} [Field K] [CharP K 2] {H : Type*} [Group H]
    [Finite H] (h : ∀ g : H, g ^ 5 = 1) : (Nat.card H : K) ≠ 0 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (fun g => ⟨1, by simpa using h g⟩ : IsPGroup 5 H)
  have h4 : ((4 : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K 2 4).mpr (by norm_num)
  have h5 : ((5 : ℕ) : K) = 1 := by
    have e : ((5 : ℕ) : K) = ((4 : ℕ) : K) + 1 := by push_cast; ring
    rw [e, h4, zero_add]
  rw [hk, Nat.cast_pow, h5, one_pow]
  exact one_ne_zero

variable {G : Type*} [Group G] {n : ℕ} {F : Type} [Field F]

@[expose] def spOf (ψ : StatedSp n F →* G) (D : Subgroup G) : Subgroup (StatedSp n F) :=
  ((D.prod ⊤) ⊓ ggConjPairs ψ).map (MonoidHom.snd G (StatedSp n F))

theorem mem_spOf {ψ : StatedSp n F →* G} {D : Subgroup G} {s : StatedSp n F} :
    s ∈ spOf ψ D ↔ ∃ e ∈ D, (e, s) ∈ ggConjPairs ψ := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.1, (Subgroup.mem_prod.mp (Subgroup.mem_inf.mp hq).1).1, (Subgroup.mem_inf.mp hq).2⟩
  · rintro ⟨e, he, h⟩
    exact ⟨(e, s), Subgroup.mem_inf.mpr ⟨Subgroup.mem_prod.mpr ⟨he, Subgroup.mem_top s⟩, h⟩, rfl⟩

theorem range_inf_centralizer_eq_spOf {ψ : StatedSp n F →* G} (hinj : Function.Injective ψ)
    {D : Subgroup G} (hDs : ∀ e ∈ D, ∃ s, (e, s) ∈ ggConjPairs ψ) :
    ψ.range ⊓ Subgroup.centralizer (D : Set G) =
      (Subgroup.centralizer (spOf ψ D : Set (StatedSp n F))).map ψ := by
  apply le_antisymm
  · rintro _ ⟨⟨u, rfl⟩, hu⟩
    refine ⟨u, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_, rfl⟩
    obtain ⟨e, he, heg⟩ := mem_spOf.mp hg
    have hxu : e * ψ u = ψ u * e := (Subgroup.mem_centralizer_iff.mp hu e he)
    have h1 : g * u * g⁻¹ = u := hinj (by
      rw [heg u]
      calc e * ψ u * e⁻¹ = ψ u * e * e⁻¹ := by rw [hxu]
        _ = ψ u := by group)
    calc g * u = g * u * g⁻¹ * g := by group
      _ = u * g := by rw [h1]
  · rintro _ ⟨u, hu, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    obtain ⟨g, hg⟩ := hDs e he
    have hsu : g * u = u * g :=
      Subgroup.mem_centralizer_iff.mp hu g (mem_spOf.mpr ⟨e, he, hg⟩)
    have h1 : g * u * g⁻¹ = u := by rw [hsu]; group
    have h2 := hg u
    rw [h1] at h2
    calc e * ψ u = e * ψ u * e⁻¹ * e := by group
      _ = ψ u * e := by rw [← h2]

theorem comap_adjCent_map_sp [CharP F 2] (S : Subgroup (StatedSp n F)) :
    (adjCent (S.map (StatedSp n F).subtype)
        (isInvol_spAdj (n := n) (F := F))).comap (StatedSp n F).subtype =
      Subgroup.centralizer (S : Set (StatedSp n F)) := by
  ext u
  rw [Subgroup.mem_comap, adjCent, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hu, -⟩ g hg
    exact Subtype.ext (hu (g : GL (Fin n ⊕ Fin n) F) ⟨g, hg, rfl⟩)
  · intro hu
    refine ⟨fun g hg => ?_, mem_unitaryOf_spAdj_iff.mpr u.2⟩
    obtain ⟨g', hg', rfl⟩ := hg
    exact congrArg Subtype.val (hu g' hg')

end Helpers

section Fix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}
  {D : Fin r → Type} [∀ i, Field (D i)] [∀ i, Algebra K (D i)] {d : Fin r → ℕ}
  [∀ i, NeZero (d i)]

theorem fix_of_coord_eq_one {Φ : PiMat D d →ₐ[K] Matrix ι ι K} {τ : PiMat D d → PiMat D d}
    (hτ : IsInvol τ) {π : Fin r → Fin r} (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {Sf : ∀ b, Subgroup (GL (Fin (d b)) (D b))} {c : Fin r} {w : (PiMat D d)ˣ}
    (hwU : w ∈ unitaryOf hτ) (hwc : (w : PiMat D d) c = 1) :
    ∀ M ∈ (coreOf π hτ Sf c).map (Units.map Φ.toMonoidHom),
      M * Units.map Φ.toMonoidHom w = Units.map Φ.toMonoidHom w * M ∧
      (M : Matrix ι ι K) * ((Units.map Φ.toMonoidHom w : GL ι K) - 1 : Matrix ι ι K) =
        ((Units.map Φ.toMonoidHom w : GL ι K) : Matrix ι ι K) - 1 := by
  have hwπc : (w : PiMat D d) (π c) = 1 := apply_perm_eq_one hτ hπ hwU hwc
  rintro _ ⟨s, hs, rfl⟩
  have hso := (Subgroup.mem_inf.mp hs).2
  have hk : ∀ k, (s : PiMat D d) k * (w : PiMat D d) k = (w : PiMat D d) k * (s : PiMat D d) k ∧
      (s : PiMat D d) k * ((w : PiMat D d) k - 1) = (w : PiMat D d) k - 1 := by
    intro k
    by_cases hkc : k = c
    · subst hkc
      rw [hwc]
      simp
    by_cases hkπ : k = π c
    · subst hkπ
      rw [hwπc]
      simp
    rw [hso.2 k hkc hkπ]
    simp
  have h1 : (s : PiMat D d) * (w : PiMat D d) = (w : PiMat D d) * (s : PiMat D d) :=
    funext fun k => (hk k).1
  have h2 : (s : PiMat D d) * ((w : PiMat D d) - 1) = (w : PiMat D d) - 1 :=
    funext fun k => (hk k).2
  have hsΦ : ((Units.map Φ.toMonoidHom s : GL ι K) : Matrix ι ι K) = Φ (s : PiMat D d) := rfl
  have hwΦ : ((Units.map Φ.toMonoidHom w : GL ι K) : Matrix ι ι K) = Φ (w : PiMat D d) := rfl
  constructor
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, hsΦ, hwΦ, ← map_mul, h1, map_mul]
  · rw [hsΦ, hwΦ, ← map_one Φ, ← map_sub, ← map_mul, h2]

end Fix

section FixedCore

theorem exists_fixedCore_component_sp {G : Type} [Group G] [Finite G] {n : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) {ψ : StatedSp n F →* G}
    (hinj : Function.Injective ψ) {z : G} {t : StatedSp n F} (ht : (z, t) ∈ ggConjPairs ψ)
    (htp : t ^ 5 = 1) {S : Subgroup (GL (Fin n ⊕ Fin n) F)} (hSq : CFSG.IsQuasisimple S)
    (hSU : S ≤ unitaryOf (isInvol_spAdj (n := n) (F := F)))
    (hSB : ∀ M ∈ S, M * (t : GL (Fin n ⊕ Fin n) F) = t * M ∧
      (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
          (((t : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) - 1) =
        ((t : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) - 1) :
    ∃ K : Subgroup G, IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {z}) ∧
      (S.comap (StatedSp n F).subtype).map ψ ≤ K ∧ 5 ∣ Nat.card K ∧
      ∀ (w : G) (s : StatedSp n F), (w, s) ∈ ggConjPairs ψ → s ^ 5 = 1 → s * t = t * s →
        ¬ GGNbrClauseFiveMarking 5 w K ∧
          (w ∈ Subgroup.centralizer (K : Set G) → ∀ M ∈ S,
            M * (s : GL (Fin n ⊕ Fin n) F) = s * M ∧
            (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
                (((s : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) - 1) =
              ((s : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) - 1) := by
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hker : ψ.ker ≤ Subgroup.center (StatedSp n F) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hinj]
    exact bot_le
  have hBu : (t : GL (Fin n ⊕ Fin n) F) ∈ unitaryOf (isInvol_spAdj (n := n) (F := F)) :=
    mem_unitaryOf_spAdj_iff.mpr t.2
  have hBp : (t : GL (Fin n ⊕ Fin n) F) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, htp, Subgroup.coe_one]
  obtain ⟨r', D', d', _, _, _, _, _, Φ', τ', hτ', π', hπ', Sf', hΦ', hR', hτΦ', himg', hy',
    hSle', hSn', hder', hq'⟩ := exists_coreData isInvol_spAdj
      (natCast_card_zpowers_ne_zero hp hp2 hBp) (adj_stab_zpowers isInvol_spAdj hBu)
      (exists_symd_spAdj (fun g hg => Subgroup.zpowers_le.mpr t.2 hg)
        (natCast_card_zpowers_ne_zero hp hp2 hBp))
  have hΦu' : Function.Injective (Units.map Φ'.toMonoidHom) :=
    Units.map_injective (f := Φ'.toMonoidHom) hΦ'
  have hFy : IsCoreFamily (adjCent (Subgroup.zpowers (t : GL (Fin n ⊕ Fin n) F))
      (isInvol_spAdj (n := n) (F := F)))
      (fun c : {b : Fin r' // b ≤ π' b ∧ Sf' b ≠ ⊥} =>
        (coreOf π' hτ' Sf' c.1).map (Units.map Φ'.toMonoidHom)) := by
    have h := (isCoreFamily_coreOf hτ' hπ' hSle' hSn' hder' hq').map _ hΦu'
    rwa [himg'] at h
  have hle : ∀ C : GL (Fin n ⊕ Fin n) F,
      adjCent (Subgroup.zpowers C) (isInvol_spAdj (n := n) (F := F)) ≤
        (StatedSp n F).subtype.range := fun C g hg =>
    ⟨⟨g, mem_unitaryOf_spAdj_iff.mp (Subgroup.mem_inf.mp hg).2⟩, rfl⟩
  have hFy' := hFy.comap (StatedSp n F).subtype (Subgroup.subtype_injective _) (hle t)
  rw [comap_adjCent_sp t] at hFy'
  obtain ⟨j₀, hc1, hc2, hπj₀, hSf'ne, hSle⟩ := exists_le_coreOf_of_fix isInvol_spAdj hΦ' hR' hτ'
    hπ' himg' hder' hSq hSU hSB
  set c' : {b : Fin r' // b ≤ π' b ∧ Sf' b ≠ ⊥} := ⟨j₀, le_of_eq hπj₀.symm, hSf'ne⟩ with hc'
  set Y := (coreOf π' hτ' Sf' j₀).map (Units.map Φ'.toMonoidHom) with hYdef
  have hYle : Y ≤ (StatedSp n F).subtype.range := (hFy.1 c').trans (hle t)
  have hYcomp : IsComponentOf ((Y.comap (StatedSp n F).subtype).map ψ)
      ((Subgroup.centralizer (Subgroup.zpowers t : Set (StatedSp n F))).map ψ) :=
    LinNonsplit.isComponentOf_map_of_le ψ hker le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance) (hFy'.1 c') (hFy'.2.1 c') (hFy'.2.2.1 c')
  rw [← range_inf_centralizer_eq hinj ht] at hYcomp
  have hrange' : ∀ X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F,
      X * ((t : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        ((t : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * X →
        X ∈ Set.range Φ' := fun X hX => (hR' X).mpr fun g hg => commute_of_mem_zpowers hX hg
  have hsurj : Function.Surjective (algebraMap F (D' j₀)) :=
    algebraMap_surjective_of_corner Φ' hΦ' hrange' inferInstance hc1 hc2
  have hD2 : Nat.card (D' j₀) = 2 :=
    (card_eq_of_corner Φ' hΦ' hrange' inferInstance hc1 hc2).trans hF
  have hτK : ∀ (c : F) (z : PiMat D' d'), τ' (c • z) = c • τ' z := fun c z =>
    hΦ' (by simp only [map_smul, hτΦ', spAdj_smul])
  have halt : ∀ c : D' j₀, tauFix τ' j₀ (Matrix.scalar (Fin (d' j₀)) c) =
      Matrix.scalar (Fin (d' j₀)) c := tauFix_scalar_of_smul hπ' hπj₀ hτK hsurj
  have hT := isInvol_tauFix hτ' hπ' hπj₀
  have hfg : factorGroup π' hτ' hπ' j₀ = matUnitary hT := by
    unfold factorGroup
    split_ifs
    rfl
  have hyj : ∃ z, z + tauFix τ' j₀ z = 1 := by
    obtain ⟨Y0, hY0⟩ := hy'
    refine ⟨Y0 j₀, ?_⟩
    have h1 := congrFun hY0 j₀
    rwa [Pi.add_apply, apply_tau_eq_tauFix hτ' hπ' hπj₀, Pi.one_apply] at h1
  have hSfle : Sf' j₀ ≤ matUnitary hT := hfg ▸ hSle' j₀
  have hderj : ∃ k, LayerFacts.ggDer (matUnitary hT) k ≤ Sf' j₀ := hfg ▸ hder' j₀
  have hqj : CFSG.IsQuasisimple (Sf' j₀) := ((hq' j₀).resolve_left hSf'ne).1
  obtain ⟨H, hH⟩ := hT.exists_gram_id halt
  have hsym := transpose_gram_eq hT H hH
  obtain ⟨z0, hz0⟩ := hyj
  have hHy := gram_eq_add_transpose H hH hsym hz0
  have hB : (Matrix.toBilin' (H : Matrix (Fin (d' j₀)) (Fin (d' j₀)) (D' j₀))).IsAlt := by
    have h2 := isAlt_toBilin'_add_transpose ((H : Matrix (Fin (d' j₀)) (Fin (d' j₀)) (D' j₀)) * z0)
    rwa [← hHy] at h2
  have hn := nondegenerate_toBilin'_gram H
  have hmap := map_toLin_matUnitary H hH (hT := hT)
  let e6 : matUnitary hT ≃*
      sesqUnitaryGroup (Matrix.toBilin' (H : Matrix (Fin (d' j₀)) (Fin (d' j₀)) (D' j₀))) :=
    ((matUnitary hT).equivMapOfInjective _ Matrix.GeneralLinearGroup.toLin.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hfr : Module.finrank (D' j₀) (Fin (d' j₀) → D' j₀) = d' j₀ := Module.finrank_fin_fun _
  obtain ⟨s', hs', ⟨e7⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  rw [hfr] at hs'
  have hd0 : 0 < d' j₀ := Nat.pos_of_ne_zero (NeZero.ne (d' j₀))
  let e1 : ↥((Y.comap (StatedSp n F).subtype).map ψ) ≃* ↥(Y.comap (StatedSp n F).subtype) :=
    ((Y.comap (StatedSp n F).subtype).equivMapOfInjective ψ hinj).symm
  let e2 : ↥(Y.comap (StatedSp n F).subtype) ≃* ↥Y :=
    ((Y.comap (StatedSp n F).subtype).equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hYle))
  let e3 : ↥Y ≃* ↥(coreOf π' hτ' Sf' j₀) :=
    ((coreOf π' hτ' Sf' j₀).equivMapOfInjective _ hΦu').symm
  let e4 : ↥(coreOf π' hτ' Sf' j₀) ≃* ↥(Sf' j₀) :=
    MulEquiv.ofBijective _ (bijective_coreOf hτ' hπ' hSle' j₀)
  have hcore : (∀ g ∈ matUnitary hT, g ^ 5 = 1 → g ∈ Sf' j₀) ∧
      (∀ g ∈ Sf' j₀, (∀ h ∈ Sf' j₀, g * h = h * g) → g = 1) ∧
      ((Sf' j₀ = matUnitary hT ∧ 2 ≤ s' ∧ (s', 1) ≠ (2, 1)) ∨
        Nonempty (↥(Sf' j₀) ≃* alternatingGroup (Fin 6))) ∧ 5 ∣ Nat.card (Sf' j₀) := by
    by_cases h6 : 6 ≤ d' j₀
    · have hqU := CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hB
        hn (by omega) (Or.inr (Or.inr ⟨hD2, by omega⟩))
      have hU : CFSG.IsQuasisimple (matUnitary hT) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv e6.symm hqU
      have hSfU : Sf' j₀ = matUnitary hT :=
        le_antisymm hSfle (le_of_ggDer_le (LayerFacts.ggCommutator_eq_of_isQuasisimple hU) le_rfl
          hderj.choose_spec)
      refine ⟨fun g hg _ => hSfU ▸ hg, fun g hg hgc => ?_, Or.inl ⟨hSfU, by omega, fun h => ?_⟩,
        ?_⟩
      · let eU : ↥(Sf' j₀) ≃* StatedSp s' (D' j₀) :=
          (MulEquiv.subgroupCongr hSfU).trans (e6.trans e7)
        have hz : eU ⟨g, hg⟩ ∈ Subgroup.center (StatedSp s' (D' j₀)) := by
          rw [Subgroup.mem_center_iff]
          intro y
          obtain ⟨y', rfl⟩ := eU.surjective y
          rw [← map_mul, ← map_mul]
          exact congrArg eU (Subtype.ext (hgc y' y'.2).symm)
        rw [CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot, Subgroup.mem_bot] at hz
        have h1 : (⟨g, hg⟩ : ↥(Sf' j₀)) = 1 := eU.injective (by rw [hz, map_one])
        exact congrArg Subtype.val h1
      · have := congrArg Prod.fst h
        simp only at this
        omega
      ·
        rw [Nat.card_congr ((MulEquiv.subgroupCongr hSfU).trans (e6.trans e7)).toEquiv,
          CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hD2]
        have h15 := Finset.dvd_prod_of_mem (fun j => 2 ^ (2 * j) - 1)
          (Finset.mem_Icc.2 ⟨(by norm_num : 1 ≤ 2), (by omega : 2 ≤ s')⟩)
        norm_num at h15
        exact ((show 5 ∣ 15 by norm_num).trans h15).mul_left _
    rcases (show d' j₀ = 2 ∨ d' j₀ = 4 by omega) with hd2 | hd4
    ·
      exfalso
      have : Group.IsSolvable (GL (Fin (d' j₀)) (D' j₀)) := by
        rw [hd2]
        exact CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable 2
          (D' j₀) (Or.inr ⟨rfl, Or.inl hD2⟩)
      exact not_isQuasisimple_of_le (U := matUnitary hT) inferInstance hSfle hqj
    ·
      obtain ⟨E⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hD2 hB hn (by rw [hfr, hd4])
      obtain ⟨⟨E6⟩, -⟩ := CFSG.RankThree.PartOne.derived_alt_index_of_mulEquiv_sympFour (e6.trans E)
      obtain ⟨hqc, hodd⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour (e6.trans E)
      let eS : ↥(commutator ↥(matUnitary hT)) ≃* ↥⁅matUnitary hT, matUnitary hT⁆ :=
        ((commutator ↥(matUnitary hT)).equivMapOfInjective (matUnitary hT).subtype
          (matUnitary hT).subtype_injective).trans
            (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator (matUnitary hT)))
      have hqS : CFSG.IsQuasisimple ↥⁅matUnitary hT, matUnitary hT⁆ :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eS hqc
      have hSfeq : Sf' j₀ = ⁅matUnitary hT, matUnitary hT⁆ := by
        refine le_antisymm ?_ (le_of_ggDer_le (LayerFacts.ggCommutator_eq_of_isQuasisimple hqS)
          (Subgroup.commutator_le_self _) hderj.choose_spec)
        rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple hqj]
        exact Subgroup.commutator_mono hSfle hSfle
      let eA : ↥(Sf' j₀) ≃* alternatingGroup (Fin 6) :=
        (MulEquiv.subgroupCongr hSfeq).trans (eS.symm.trans E6)
      refine ⟨fun g hg hg5 => ?_, fun g hg hgc => ?_, Or.inr ⟨eA⟩, ?_⟩
      · have h1 := hodd hp hp2 (⟨g, hg⟩ : ↥(matUnitary hT)) (Subtype.ext (by simpa using hg5))
        rw [hSfeq, ← Subgroup.map_subtype_commutator]
        exact ⟨⟨g, hg⟩, h1, rfl⟩
      · have hz : eA ⟨g, hg⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
          rw [Subgroup.mem_center_iff]
          intro y
          obtain ⟨y', rfl⟩ := eA.surjective y
          rw [← map_mul, ← map_mul]
          exact congrArg eA (Subtype.ext (hgc y' y'.2).symm)
        rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hz
        have h1 : (⟨g, hg⟩ : ↥(Sf' j₀)) = 1 := eA.injective (by rw [hz, map_one])
        exact congrArg Subtype.val h1
      ·
        have h6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
          have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
          have hF6 : Nat.card (Fin 6) = 6 := by simp
          rw [Nat.card_perm, hF6, show Nat.factorial 6 = 720 by decide] at h
          omega
        rw [Nat.card_congr eA.toEquiv, h6]
        norm_num
  refine ⟨(Y.comap (StatedSp n F).subtype).map ψ, hYcomp,
    Subgroup.map_mono (Subgroup.comap_mono hSle),
    (Nat.card_congr (e1.trans (e2.trans (e3.trans e4))).toEquiv).symm ▸ hcore.2.2.2,
    fun w s hs hsp hst => ?_⟩
  have hAB : (s : GL (Fin n ⊕ Fin n) F) * t = t * s := by
    rw [← Subgroup.coe_mul, hst, Subgroup.coe_mul]
  have hsB : (s : GL (Fin n ⊕ Fin n) F) ∈ adjCent (Subgroup.zpowers (t : GL (Fin n ⊕ Fin n) F))
      (isInvol_spAdj (n := n) (F := F)) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun g hg => ?_,
      mem_unitaryOf_spAdj_iff.mpr s.2⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute (t : GL (Fin n ⊕ Fin n) F) s from hAB.symm) k).eq
  rw [← himg'] at hsB
  obtain ⟨a, haU, has⟩ := hsB
  have haj : coordHom D' d' j₀ a ∈ matUnitary hT := coordHom_mem_matUnitary hτ' hπ' hπj₀ haU
  have ha5 : coordHom D' d' j₀ a ^ 5 = 1 := by
    have h1 : a ^ 5 = 1 := hΦu' (by
      rw [map_pow, has, map_one, ← Subgroup.coe_pow, hsp, Subgroup.coe_one])
    rw [← map_pow, h1, map_one]
  have hajS : coordHom D' d' j₀ a ∈ Sf' j₀ := hcore.1 _ haj ha5
  have hinner : ∃ k ∈ (Y.comap (StatedSp n F).subtype).map ψ,
      ∀ l ∈ (Y.comap (StatedSp n F).subtype).map ψ, w⁻¹ * l * w = k⁻¹ * l * k := by
    obtain ⟨ã, hãorb, hãa⟩ := exists_mem_orbitGroup_fix hτ' hπ' hπj₀ haj
    have hãcore : ã ∈ coreOf π' hτ' Sf' j₀ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (by rw [hãa]; exact hajS), hãorb⟩
    have hãY : Units.map Φ'.toMonoidHom ã ∈ Y := ⟨ã, hãcore, rfl⟩
    obtain ⟨kk, hkk⟩ := hYle hãY
    refine ⟨ψ kk, ⟨kk, (show (StatedSp n F).subtype kk ∈ Y by rw [hkk]; exact hãY), rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨γ, hγcore, hγu⟩ := (Subgroup.mem_comap.mp hu : (StatedSp n F).subtype u ∈ Y)
    have hconj : s⁻¹ * u * s = kk⁻¹ * u * kk := by
      apply Subtype.ext
      have e := conj_eq_conj_of_mem_orbitGroup hτ' hπ' haU (Subgroup.mem_inf.mp hγcore).2 hãorb
        hãa
      have e' := congrArg (Units.map Φ'.toMonoidHom) e
      simp only [map_mul, map_inv] at e'
      rw [has, hγu, ← hkk] at e'
      simpa using e'
    have h1 := hs (s⁻¹ * u * s)
    rw [show s * (s⁻¹ * u * s) * s⁻¹ = u by group] at h1
    calc w⁻¹ * ψ u * w = w⁻¹ * (w * ψ (s⁻¹ * u * s) * w⁻¹) * w := by rw [← h1]
      _ = ψ (s⁻¹ * u * s) := by group
      _ = ψ (kk⁻¹ * u * kk) := by rw [hconj]
      _ = (ψ kk)⁻¹ * ψ u * ψ kk := by rw [map_mul, map_mul, map_inv]
  refine ⟨?_, fun hwK M hM => ?_⟩
  ·
    rcases hcore.2.2.1 with ⟨hSfU, h2, h3⟩ | hA6
    · let eK : ↥((Y.comap (StatedSp n F).subtype).map ψ) ≃* StatedSp s' (D' j₀) :=
        e1.trans (e2.trans (e3.trans (e4.trans ((MulEquiv.subgroupCongr hSfU).trans
          (e6.trans e7)))))
      exact not_ggNbrClauseFiveMarking_sp (f := 1) (by rw [hD2, pow_one]) eK h2 h3 hp hp2
        (by norm_num) (by norm_num) hinner
    · obtain ⟨eA⟩ := hA6
      exact ggNonsplitNbrAltSixInput_holds G _ ⟨e1.trans (e2.trans (e3.trans (e4.trans eA)))⟩ 5
        hp hp2 (by norm_num) w
  ·
    have hcomm : ∀ g ∈ Sf' j₀, coordHom D' d' j₀ a * g = g * coordHom D' d' j₀ a := by
      intro g hg
      obtain ⟨⟨γ, hγcore⟩, hγg⟩ := (bijective_coreOf hτ' hπ' hSle' j₀).2 ⟨g, hg⟩
      have hγg' : coordHom D' d' j₀ γ = g := congrArg Subtype.val hγg
      have hγY : Units.map Φ'.toMonoidHom γ ∈ Y := ⟨γ, hγcore, rfl⟩
      obtain ⟨u, hu⟩ := hYle hγY
      have hψu : ψ u ∈ (Y.comap (StatedSp n F).subtype).map ψ :=
        ⟨u, (show (StatedSp n F).subtype u ∈ Y by rw [hu]; exact hγY), rfl⟩
      have h1 : w * ψ u * w⁻¹ = ψ u := by
        rw [(Subgroup.mem_centralizer_iff.mp hwK _ hψu).symm, mul_inv_cancel_right]
      have h2 : s * u * s⁻¹ = u := hinj (by rw [hs u, h1])
      have h3 : (s : GL (Fin n ⊕ Fin n) F) * (u : GL (Fin n ⊕ Fin n) F) =
          (u : GL (Fin n ⊕ Fin n) F) * s := by
        have h4 : s * u = u * s := by
          calc s * u = s * u * s⁻¹ * s := by group
            _ = u * s := by rw [h2]
        rw [← Subgroup.coe_mul, h4, Subgroup.coe_mul]
      have h5 : Units.map Φ'.toMonoidHom (a * γ) = Units.map Φ'.toMonoidHom (γ * a) := by
        rw [map_mul, map_mul, has]
        have hu' : (u : GL (Fin n ⊕ Fin n) F) = Units.map Φ'.toMonoidHom γ := hu
        rw [← hu']
        exact h3
      have h6 := congrArg (coordHom D' d' j₀) (hΦu' h5)
      rw [map_mul, map_mul, hγg'] at h6
      exact h6
    have ha1 : coordHom D' d' j₀ a = 1 := hcore.2.1 _ hajS hcomm
    have haj1 : (a : PiMat D' d') j₀ = 1 := by
      have h := congrArg (fun g : GL (Fin (d' j₀)) (D' j₀) =>
        (g : Matrix (Fin (d' j₀)) (Fin (d' j₀)) (D' j₀))) ha1
      simpa [coe_coordHom] using h
    obtain ⟨γ, hγcore, rfl⟩ := hSle hM
    have hγo := (Subgroup.mem_inf.mp hγcore).2
    have hk : ∀ k, (γ : PiMat D' d') k * (a : PiMat D' d') k =
          (a : PiMat D' d') k * (γ : PiMat D' d') k ∧
        (γ : PiMat D' d') k * ((a : PiMat D' d') k - 1) = (a : PiMat D' d') k - 1 := by
      intro k
      by_cases hkj : k = j₀
      · subst hkj
        rw [haj1]
        simp
      have hkπ : k ≠ π' j₀ := by rw [hπj₀]; exact hkj
      rw [hγo.2 k hkj hkπ]
      simp
    have h1 : (γ : PiMat D' d') * (a : PiMat D' d') = (a : PiMat D' d') * (γ : PiMat D' d') :=
      funext fun k => (hk k).1
    have h2 : (γ : PiMat D' d') * ((a : PiMat D' d') - 1) = (a : PiMat D' d') - 1 :=
      funext fun k => (hk k).2
    have hγΦ : ((Units.map Φ'.toMonoidHom γ : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = Φ' (γ : PiMat D' d') := rfl
    have hsΦ : ((s : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        Φ' (a : PiMat D' d') := by rw [← has]; rfl
    constructor
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, hγΦ, hsΦ, ← map_mul, h1, map_mul]
    · rw [hγΦ, hsΦ, ← map_one Φ', ← map_sub, ← map_mul, h2]

end FixedCore

section Main

theorem fieldFive_sp {G : Type} [Group G] [Finite G] {n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 2) {ψ : StatedSp n F →* G} (hinj : Function.Injective ψ)
    {D : Subgroup G} (hDel : IsElemAbelian 5 D) (hDcard : Nat.card D = 5 ^ 2)
    (hDs : ∀ e ∈ D, ∃ s, (e, s) ∈ ggConjPairs ψ) {x : G} (hxD : x ∈ D) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x}))
    (hLmark : GGNbrClauseFiveMarking 5 x L)
    {J : Subgroup G} (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ y ∈ D, y ≠ 1 ∧ ∃ K : Subgroup G,
      IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {y}) ∧ J ≤ K ∧ 5 ∣ Nat.card K ∧
      x ∉ Subgroup.centralizer (K : Set G) ∧ ¬ GGNbrClauseFiveMarking 5 x K := by
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  have : Fact (5 : ℕ).Prime := ⟨hp⟩
  have hker : ψ.ker ≤ Subgroup.center (StatedSp n F) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hinj]
    exact bot_le
  have hZ1 : ∀ g : StatedSp n F, ((1 : G), g) ∈ ggConjPairs ψ → g = 1 := fun g hg => by
    have h := mem_center_of_mem_ggConjPairs_one hinj hg
    rwa [CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot, Subgroup.mem_bot] at h
  have hpow : ∀ e ∈ D, ∀ s : StatedSp n F, (e, s) ∈ ggConjPairs ψ → s ^ 5 = 1 := by
    intro e he s hs
    refine hZ1 _ ?_
    have h := (ggConjPairs ψ).pow_mem hs 5
    rwa [Prod.pow_mk, hDel.2 e he] at h
  have hcomm : ∀ e ∈ D, ∀ e' ∈ D, ∀ s s' : StatedSp n F, (e, s) ∈ ggConjPairs ψ →
      (e', s') ∈ ggConjPairs ψ → s * s' = s' * s := by
    intro e he e' he' s s' hs hs'
    have hee : e * e' = e' * e :=
      congrArg Subtype.val (hDel.1.is_comm.comm (⟨e, he⟩ : ↥D) ⟨e', he'⟩)
    have h := (ggConjPairs ψ).mul_mem ((ggConjPairs ψ).mul_mem hs hs')
      ((ggConjPairs ψ).inv_mem ((ggConjPairs ψ).mul_mem hs' hs))
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, hee, mul_inv_cancel] at h
    have h1 := hZ1 _ h
    calc s * s' = s * s' * (s' * s)⁻¹ * (s' * s) := by group
      _ = s' * s := by rw [h1, one_mul]
  set SD := spOf ψ D with hSD
  set AD := SD.map (StatedSp n F).subtype with hAD
  have hADsp : ∀ g ∈ AD, g ∈ StatedSp n F := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hADu : ∀ g ∈ AD, g ∈ unitaryOf (isInvol_spAdj (n := n) (F := F)) := fun g hg =>
    mem_unitaryOf_spAdj_iff.mpr (hADsp g hg)
  have hADcomm : ∀ g ∈ AD, ∀ h ∈ AD, g * h = h * g := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    obtain ⟨e, he, hes⟩ := mem_spOf.mp hs
    obtain ⟨e', he', hes'⟩ := mem_spOf.mp hs'
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, hcomm e he e' he' s s' hes hes', Subgroup.coe_mul]
  have hADcard : (Nat.card AD : F) ≠ 0 := natCast_card_ne_zero_of_pow_five fun g => by
    obtain ⟨_, ⟨s, hs, rfl⟩⟩ := g
    obtain ⟨e, he, hes⟩ := mem_spOf.mp hs
    apply Subtype.ext
    simp only [SubmonoidClass.mk_pow, Subgroup.coe_subtype, OneMemClass.coe_one]
    rw [← Subgroup.coe_pow, hpow e he s hes, Subgroup.coe_one]
  obtain ⟨r, E, e, _, _, _, _, _, Φ, τ, hτ, π, hπ, Sf, hΦ, hR, -, himg, -, hSle, hSn, hder,
    hq⟩ := exists_coreData isInvol_spAdj hADcard
      (fun X hX g hg => adj_mul_comm isInvol_spAdj (hADu g hg) (hX g hg))
      (exists_symd_spAdj hADsp hADcard)
  have hΦu : Function.Injective (Units.map Φ.toMonoidHom) :=
    Units.map_injective (f := Φ.toMonoidHom) hΦ
  have hFD : IsCoreFamily (adjCent AD (isInvol_spAdj (n := n) (F := F)))
      (fun c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥} =>
        (coreOf π hτ Sf c.1).map (Units.map Φ.toMonoidHom)) := by
    have h := (isCoreFamily_coreOf hτ hπ hSle hSn hder hq).map _ hΦu
    rwa [himg] at h
  have hle : adjCent AD (isInvol_spAdj (n := n) (F := F)) ≤ (StatedSp n F).subtype.range :=
    fun g hg => ⟨⟨g, mem_unitaryOf_spAdj_iff.mp (Subgroup.mem_inf.mp hg).2⟩, rfl⟩
  have hFD' := hFD.comap (StatedSp n F).subtype (Subgroup.subtype_injective _) hle
  rw [hAD, comap_adjCent_map_sp SD] at hFD'
  have hJG : IsComponentOf J ((Subgroup.centralizer (SD : Set (StatedSp n F))).map ψ) := by
    have h1 := CFSG.LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hL.2.1
      (Subgroup.centralizer (D : Set G))
    have h2 : ψ.range ⊓ Subgroup.centralizer {x} ⊓ Subgroup.centralizer (D : Set G) =
        ψ.range ⊓ Subgroup.centralizer (D : Set G) := by
      rw [inf_assoc, inf_eq_right.mpr
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxD))]
    rw [h2, range_inf_centralizer_eq_spOf hinj hDs] at h1
    exact isComponentOf_of_isSubnormal_of_isComponentOf hJ h1
  obtain ⟨⟨c, hcπ, hSc⟩, hJeq⟩ := LayerPDiv.exists_eq_map_of_isComponentOf ψ hker le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) (ggCommutator_self_le _) _ hFD'.1
    hFD'.2.1 hFD'.2.2.1 hFD'.2.2.2.1 hJG
  set S := (coreOf π hτ Sf c).map (Units.map Φ.toMonoidHom) with hSdef
  have hSq : CFSG.IsQuasisimple S := hFD.2.2.1 ⟨c, hcπ, hSc⟩
  have hSU : S ≤ unitaryOf (isInvol_spAdj (n := n) (F := F)) :=
    (hFD.1 ⟨c, hcπ, hSc⟩).trans inf_le_right
  have hJeq' : J = (S.comap (StatedSp n F).subtype).map ψ := hJeq
  obtain ⟨sx, hsx⟩ := hDs x hxD
  obtain ⟨y₀, hy₀D, hy₀x⟩ : ∃ y₀ ∈ D, y₀ ∉ Subgroup.zpowers x := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers x from fun d hd => hall d hd)
    rw [Nat.card_zpowers, hDcard] at h1
    have h2 : orderOf x ≤ 5 := orderOf_le_of_pow_eq_one (by norm_num) (hDel.2 x hxD)
    omega
  obtain ⟨sy, hsy⟩ := hDs y₀ hy₀D
  have hsx5 := hpow x hxD sx hsx
  have hsy5 := hpow y₀ hy₀D sy hsy
  have hcoord : ∀ s : StatedSp n F, s ∈ SD → ∃ a : (PiMat E e)ˣ, a ∈ unitaryOf hτ ∧
      Units.map Φ.toMonoidHom a = (s : GL (Fin n ⊕ Fin n) F) ∧
      ∀ z : PiMat E e, z * (a : PiMat E e) = (a : PiMat E e) * z := by
    intro s hs
    have hsA : (s : GL (Fin n ⊕ Fin n) F) ∈ AD := ⟨s, hs, rfl⟩
    have hsB : (s : GL (Fin n ⊕ Fin n) F) ∈ adjCent AD (isInvol_spAdj (n := n) (F := F)) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun g hg => hADcomm g hg _ hsA,
        mem_unitaryOf_spAdj_iff.mpr s.2⟩
    rw [← himg] at hsB
    obtain ⟨a, haU, has⟩ := hsB
    refine ⟨a, haU, has, fun z => hΦ ?_⟩
    have h1 := (hR (Φ z)).mp ⟨z, rfl⟩ _ hsA
    have has' : ((s : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        Φ (a : PiMat E e) := by rw [← has]; rfl
    rw [map_mul, map_mul, ← has']
    exact h1
  obtain ⟨a, haU, has, hac⟩ := hcoord sx (mem_spOf.mpr ⟨x, hxD, hsx⟩)
  obtain ⟨w₀, hw₀U, hw₀s, hw₀c⟩ := hcoord sy (mem_spOf.mpr ⟨y₀, hy₀D, hsy⟩)
  obtain ⟨α, hα⟩ := exists_scalar_of_central hac c
  obtain ⟨β, hβ⟩ := exists_scalar_of_central hw₀c c
  have hscal5 : ∀ (u : (PiMat E e)ˣ) (γ : E c),
      (u : PiMat E e) c = Matrix.scalar (Fin (e c)) γ → u ^ 5 = 1 → γ ^ 5 = 1 := by
    intro u γ hγ hu5
    have h1 := congrArg (fun v : (PiMat E e)ˣ => (v : PiMat E e) c) hu5
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, Units.val_one, Pi.one_apply] at h1
    rw [hγ, ← map_pow] at h1
    have i₀ : Fin (e c) := ⟨0, Nat.pos_of_ne_zero (NeZero.ne (e c))⟩
    have h2 := congrFun (congrFun h1 i₀) i₀
    simpa using h2
  have ha5 : a ^ 5 = 1 := hΦu (by
    rw [map_pow, has, map_one, ← Subgroup.coe_pow, hsx5, Subgroup.coe_one])
  have hw5 : w₀ ^ 5 = 1 := hΦu (by
    rw [map_pow, hw₀s, map_one, ← Subgroup.coe_pow, hsy5, Subgroup.coe_one])
  have hα5 := hscal5 a α hα ha5
  have hβ5 := hscal5 w₀ β hβ hw5
  have hα1 : α ≠ 1 := by
    intro hα1
    have hac1 : (a : PiMat E e) c = 1 := by rw [hα, hα1, map_one]
    have hfix := fix_of_coord_eq_one (Φ := Φ) hτ hπ (Sf := Sf) haU hac1
    rw [has] at hfix
    obtain ⟨Kx, hKx, hJKx, -, hKxw⟩ :=
      exists_fixedCore_component_sp hF hinj hsx hsx5 hSq hSU fun M hM => hfix M hM
    rw [← hJeq'] at hJKx
    have hLK : L = Kx := by
      rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hL hKx with h | h
      · exact h
      · exfalso
        apply CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hJ.2.2
        have hc : L ≤ Subgroup.centralizer (Kx : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
        exact ((hJ.1.trans inf_le_left).trans hc).trans (Subgroup.centralizer_le hJKx)
    exact (hKxw x sx hsx hsx5 rfl).1 (hLK ▸ hLmark)
  have hαo : orderOf α = 5 := orderOf_eq_prime hα5 hα1
  have hprim : IsPrimitiveRoot α 5 := hαo ▸ IsPrimitiveRoot.orderOf α
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one hβ5
  have hyt : (y₀ * (x ^ j)⁻¹, sy * (sx ^ j)⁻¹) ∈ ggConjPairs ψ := by
    have h := (ggConjPairs ψ).mul_mem hsy
      ((ggConjPairs ψ).inv_mem ((ggConjPairs ψ).pow_mem hsx j))
    rwa [Prod.pow_mk, Prod.inv_mk, Prod.mk_mul_mk] at h
  have hyD : y₀ * (x ^ j)⁻¹ ∈ D := D.mul_mem hy₀D (D.inv_mem (D.pow_mem hxD j))
  have hy1 : y₀ * (x ^ j)⁻¹ ≠ 1 := by
    intro h
    apply hy₀x
    rw [mul_inv_eq_one.mp h]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j
  have ht5 : (sy * (sx ^ j)⁻¹) ^ 5 = 1 := hpow _ hyD _ hyt
  have hwt : Units.map Φ.toMonoidHom (w₀ * (a ^ j)⁻¹) =
      ((sy * (sx ^ j)⁻¹ : StatedSp n F) : GL (Fin n ⊕ Fin n) F) := by
    rw [map_mul, map_inv, map_pow, has, hw₀s]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  have hwU : w₀ * (a ^ j)⁻¹ ∈ unitaryOf hτ :=
    (unitaryOf hτ).mul_mem hw₀U ((unitaryOf hτ).inv_mem ((unitaryOf hτ).pow_mem haU j))
  have hwc : ((w₀ * (a ^ j)⁻¹ : (PiMat E e)ˣ) : PiMat E e) c = 1 := by
    have h1 : ((a ^ j : (PiMat E e)ˣ) : PiMat E e) c = (w₀ : PiMat E e) c := by
      rw [Units.val_pow_eq_pow_val, Pi.pow_apply, hα, hβ, ← map_pow, hj]
    rw [Units.val_mul, Pi.mul_apply, ← h1, ← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Pi.one_apply]
  have hfix := fix_of_coord_eq_one (Φ := Φ) hτ hπ (Sf := Sf) hwU hwc
  rw [hwt] at hfix
  obtain ⟨K, hK, hJK, h5K, hKw⟩ :=
    exists_fixedCore_component_sp hF hinj hyt ht5 hSq hSU fun M hM => hfix M hM
  rw [← hJeq'] at hJK
  have hst : sx * (sy * (sx ^ j)⁻¹) = (sy * (sx ^ j)⁻¹) * sx :=
    hcomm x hxD _ hyD sx _ hsx hyt
  obtain ⟨hnm, hcentK⟩ := hKw x sx hsx hsx5 hst
  have hxK : x ∉ Subgroup.centralizer (K : Set G) := by
    intro hxK
    have hfx := hcentK hxK
    have hT1 : ∀ γ ∈ coreOf π hτ Sf c, γ = 1 := by
      intro γ hγ
      have h := (hfx _ ⟨γ, hγ, rfl⟩).2
      have hγΦ : ((Units.map Φ.toMonoidHom γ : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = Φ (γ : PiMat E e) := rfl
      have hsxΦ : ((sx : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
          Φ (a : PiMat E e) := by rw [← has]; rfl
      rw [hγΦ, hsxΦ, ← map_one Φ, ← map_sub, ← map_mul] at h
      have h2 := congrFun (hΦ h) c
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply] at h2
      rw [hα] at h2
      have hg1 : coordHom E e c γ = 1 :=
        LinNonsplit.eq_one_of_mul_scalar_sub_one hα1 (by rw [coe_coordHom]; exact h2)
      exact coordHom_injOn hτ hπ (Subgroup.mem_inf.mp hγ).2 (Subgroup.one_mem _)
        (by rw [hg1, map_one])
    obtain ⟨a₁, a₂, haa⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hSq
    have h1 : a₁ = 1 := by
      obtain ⟨γ, hγ, hγa⟩ := a₁.2
      apply Subtype.ext
      rw [← hγa, hT1 γ hγ, map_one]
      rfl
    exact haa (by rw [h1, one_mul, mul_one])
  exact ⟨_, hyD, hy1, K, hK, hJK, h5K, hxK, hnm⟩

end Main

end FieldFiveSp

section Tag

open CFSG.Assembly

theorem ggFieldFiveNbrTag_PSp : GGFieldFiveNbrTag .PSp := by
  intro G _ _ n ψ G₀ hpres D hDel hDcard _ hDdiag x hxD L hL hLmark J hJ
  obtain ⟨⟨-, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  rw [← hrange] at hL ⊢
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans
      (CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := GaloisField 2 1) n).le
  exact FieldFiveSp.fieldFive_sp hF hinj hDel hDcard
    (fun d hd => LayerPDiv.exists_mem_ggConjPairs_sp (F := GaloisField 2 1) hrk ψ hker
      (hDdiag d hd)) hxD hL hLmark hJ

theorem ggSixFieldFiveInput_of_genuine_PSL_PSp (hPSU : GGFieldFiveNbrTag .PSU)
    (hPlus : GGFieldFiveNbrTag .POmegaPlus) (hMinus : GGFieldFiveNbrTag .POmegaMinus)
    (hF4 : GGFieldFiveNbrTag .F4) (hE6 : GGFieldFiveNbrTag .E6) (hE7 : GGFieldFiveNbrTag .E7)
    (hE8 : GGFieldFiveNbrTag .E8) (hTwE6 : GGFieldFiveNbrTag .twistedE6) : GGSixFieldFiveInput :=
  ggSixFieldFiveInput_of_genuine ggFieldFiveNbrTag_PSL hPSU ggFieldFiveNbrTag_PSp hPlus hMinus hF4
    hE6 hE7 hE8 hTwE6

theorem ggSixFieldFiveInput_of_rest (hPSU : GGFieldFiveNbrTag .PSU)
    (hPlus : GGFieldFiveNbrTag .POmegaPlus) (hMinus : GGFieldFiveNbrTag .POmegaMinus)
    (hE8 : GGFieldFiveNbrTag .E8) (hF4 : GGFieldFiveRankTag .F4) (hE6 : GGFieldFiveRankTag .E6)
    (hE7 : GGFieldFiveRankTag .E7) (hTwE6 : GGFieldFiveRankTag .twistedE6) :
    GGSixFieldFiveInput := by
  refine ggSixFieldFiveInput_of_tags_or_rank fun t => ?_
  cases t with
  | PSL => exact Or.inl ggFieldFiveNbrTag_PSL
  | PSU => exact Or.inl hPSU
  | PSp => exact Or.inl ggFieldFiveNbrTag_PSp
  | POmegaPlus => exact Or.inl hPlus
  | POmegaMinus => exact Or.inl hMinus
  | F4 => exact Or.inr hF4
  | E6 => exact Or.inr hE6
  | E7 => exact Or.inr hE7
  | E8 => exact Or.inl hE8
  | twistedE6 => exact Or.inr hTwE6
  | _ => exact Or.inl (ggFieldFiveNbrTag_of_vacuous _ (by simp))

end Tag

end CFSG.StandardType
