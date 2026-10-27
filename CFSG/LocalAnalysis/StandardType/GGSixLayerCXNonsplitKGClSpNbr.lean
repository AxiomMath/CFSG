module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClCorner
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClSp
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClMark

public section

namespace CFSG.StandardType

namespace ClNonsplit

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix LayerCores LayerFacts
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def GGNonsplitNbrSpOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K' : Subgroup G) (f : ℕ) (F' : Type) [Field F']
    [Finite F'], Nat.card F' = 2 ^ f → 2 ≤ f → Nonempty (↥K' ≃* StatedSp 1 F') →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ 2 ^ f - 1 → ¬ p ∣ 2 ^ f + 1 → ∀ x : G,
      (∃ k ∈ K', ∀ l ∈ K', x⁻¹ * l * x = k⁻¹ * l * k) → ¬ GGNbrClauseFiveMarking p x K'

@[expose] def GGNonsplitNbrAltSixInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K' : Subgroup G),
    Nonempty (↥K' ≃* alternatingGroup (Fin 6)) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ x : G, ¬ GGNbrClauseFiveMarking p x K'


section Main

theorem not_ggNbrClauseFiveMarking_nbr_sp (hSp1 : GGNonsplitNbrSpOneInput)
    (hA6 : GGNonsplitNbrAltSixInput) {G : Type} [Group G] [Finite G] {n f : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f) {ψ : StatedSp n F →* G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n F)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1) {x y : G} (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hxy : x * y = y * x) {s t : StatedSp n F} (hs : (x, s) ∈ ggConjPairs ψ)
    (ht : (y, t) ∈ ggConjPairs ψ) {K K' : Subgroup G}
    (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {x})) (hpK : ¬ p ∣ Nat.card K)
    (hK' : IsComponentOf K' (ψ.range ⊓ Subgroup.centralizer {y})) (hKK' : K ≤ K') :
    ¬ GGNbrClauseFiveMarking p x K' := by
  classical
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := F) n).le
  have hZ1 : ∀ g : StatedSp n F, ((1 : G), g) ∈ ggConjPairs ψ → g = 1 := fun g hg => by
    have h := mem_center_of_mem_ggConjPairs_one hinj hg
    rwa [CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot, Subgroup.mem_bot] at h
  have hsp : s ^ p = 1 := hZ1 _ (by
    have h := (ggConjPairs ψ).pow_mem hs p
    rwa [Prod.pow_mk, hx] at h)
  have htp : t ^ p = 1 := hZ1 _ (by
    have h := (ggConjPairs ψ).pow_mem ht p
    rwa [Prod.pow_mk, hy] at h)
  have hst : s * t = t * s := by
    have h := (ggConjPairs ψ).mul_mem ((ggConjPairs ψ).mul_mem hs ht)
      ((ggConjPairs ψ).inv_mem ((ggConjPairs ψ).mul_mem ht hs))
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, hxy, mul_inv_cancel] at h
    have h1 := hZ1 _ h
    calc s * t = s * t * (t * s)⁻¹ * (t * s) := by group
      _ = t * s := by rw [h1, one_mul]
  have hAu : (s : GL (Fin n ⊕ Fin n) F) ∈ unitaryOf (isInvol_spAdj (n := n) (F := F)) :=
    mem_unitaryOf_spAdj_iff.mpr s.2
  have hBu : (t : GL (Fin n ⊕ Fin n) F) ∈ unitaryOf (isInvol_spAdj (n := n) (F := F)) :=
    mem_unitaryOf_spAdj_iff.mpr t.2
  have hAp : (s : GL (Fin n ⊕ Fin n) F) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hsp, Subgroup.coe_one]
  have hBp : (t : GL (Fin n ⊕ Fin n) F) ^ p = 1 := by
    rw [← Subgroup.coe_pow, htp, Subgroup.coe_one]
  have hAB : (s : GL (Fin n ⊕ Fin n) F) * t = t * s := by
    rw [← Subgroup.coe_mul, hst, Subgroup.coe_mul]
  have hsymd : ∀ {C : GL (Fin n ⊕ Fin n) F}, C ∈ StatedSp n F → C ^ p = 1 →
      ∃ Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F, (∀ g ∈ Subgroup.zpowers C,
        Y * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
          (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * Y) ∧ Y + spAdj n F Y = 1 :=
    fun hC hCp => exists_symd_spAdj (fun g hg => Subgroup.zpowers_le.mpr hC hg)
      (natCast_card_zpowers_ne_zero hp hp2 hCp)
  obtain ⟨r, D, d, _, _, _, _, _, Φ, τ, hτ, π, hπ, Sf, hΦ, -, -, himg, hy0, hSle, hSn, hder,
    hq⟩ := exists_coreData isInvol_spAdj (natCast_card_zpowers_ne_zero hp hp2 hAp)
      (adj_stab_zpowers isInvol_spAdj hAu) (hsymd s.2 hAp)
  obtain ⟨r', D', d', _, _, _, _, _, Φ', τ', hτ', π', hπ', Sf', hΦ', hR', hτΦ', himg', hy',
    hSle', hSn', hder', hq'⟩ := exists_coreData isInvol_spAdj
      (natCast_card_zpowers_ne_zero hp hp2 hBp) (adj_stab_zpowers isInvol_spAdj hBu)
      (hsymd t.2 hBp)
  have hΦu : Function.Injective (Units.map Φ.toMonoidHom) :=
    Units.map_injective (f := Φ.toMonoidHom) hΦ
  have hΦu' : Function.Injective (Units.map Φ'.toMonoidHom) :=
    Units.map_injective (f := Φ'.toMonoidHom) hΦ'
  have hFx : IsCoreFamily (adjCent (Subgroup.zpowers (s : GL (Fin n ⊕ Fin n) F))
      (isInvol_spAdj (n := n) (F := F)))
      (fun c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥} =>
        (coreOf π hτ Sf c.1).map (Units.map Φ.toMonoidHom)) := by
    have h := (isCoreFamily_coreOf hτ hπ hSle hSn hder hq).map _ hΦu
    rwa [himg] at h
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
  have hFx' := hFx.comap (StatedSp n F).subtype (Subgroup.subtype_injective _) (hle s)
  have hFy' := hFy.comap (StatedSp n F).subtype (Subgroup.subtype_injective _) (hle t)
  rw [comap_adjCent_sp s] at hFx'
  rw [comap_adjCent_sp t] at hFy'
  rw [range_inf_centralizer_eq hinj hs] at hK
  rw [range_inf_centralizer_eq hinj ht] at hK'
  obtain ⟨⟨b, hbπ, hSb⟩, hKeq⟩ := LayerPDiv.exists_eq_map_of_isComponentOf ψ hker le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) (ggCommutator_self_le _) _ hFx'.1 hFx'.2.1
    hFx'.2.2.1 hFx'.2.2.2.1 hK
  set Sc := (coreOf π hτ Sf b).map (Units.map Φ.toMonoidHom) with hScdef
  have hKeq' : K = (Sc.comap (StatedSp n F).subtype).map ψ := hKeq
  have hpS : ¬ p ∣ Nat.card (Sf b) := by
    intro h
    apply hpK
    rw [hKeq', Subgroup.card_map_of_injective hinj,
      ← Subgroup.card_map_of_injective (Subgroup.subtype_injective (StatedSp n F)),
      Subgroup.map_comap_eq_self ((hFx.1 ⟨b, hbπ, hSb⟩).trans (hle s)),
      Subgroup.card_map_of_injective hΦu,
      Nat.card_congr (Equiv.ofBijective _ (bijective_coreOf hτ hπ hSle b))]
    exact h
  have hMB := fix_of_not_dvd isInvol_spAdj hΦ hτ hπ himg hy0 hSle hder
    ((hq b).resolve_left hSb).1 hp hp2 hpS hBu hBp hAB
  obtain ⟨j₀, hc1, hc2, hπj₀, hSf'ne, hScle⟩ := exists_le_coreOf_of_fix isInvol_spAdj hΦ' hR' hτ'
    hπ' himg' hder' (hFx.2.2.1 ⟨b, hbπ, hSb⟩) ((hFx.1 ⟨b, hbπ, hSb⟩).trans inf_le_right) hMB
  set c' : {b : Fin r' // b ≤ π' b ∧ Sf' b ≠ ⊥} := ⟨j₀, le_of_eq hπj₀.symm, hSf'ne⟩ with hc'
  set Y := (coreOf π' hτ' Sf' j₀).map (Units.map Φ'.toMonoidHom) with hYdef
  have hYle : Y ≤ (StatedSp n F).subtype.range := (hFy.1 c').trans (hle t)
  have hYcomp : IsComponentOf ((Y.comap (StatedSp n F).subtype).map ψ)
      ((Subgroup.centralizer (Subgroup.zpowers t : Set (StatedSp n F))).map ψ) :=
    LinNonsplit.isComponentOf_map_of_le ψ hker le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance) (hFy'.1 c') (hFy'.2.1 c') (hFy'.2.2.1 c')
  have hKY : K ≤ (Y.comap (StatedSp n F).subtype).map ψ := by
    rw [hKeq']
    exact Subgroup.map_mono (Subgroup.comap_mono hScle)
  have hK'eq : K' = (Y.comap (StatedSp n F).subtype).map ψ := by
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hK' hYcomp with h | h
    · exact h
    · exfalso
      have h1 : K' ≤ Subgroup.centralizer
          (((Y.comap (StatedSp n F).subtype).map ψ : Subgroup G) : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      exact CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hK.2.2
        (hKK'.trans (h1.trans (Subgroup.centralizer_le hKY)))
  rw [hK'eq]
  have hrange' : ∀ X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F,
      X * ((t : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        ((t : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * X →
        X ∈ Set.range Φ' := fun X hX => (hR' X).mpr fun g hg => commute_of_mem_zpowers hX hg
  have hsurj : Function.Surjective (algebraMap F (D' j₀)) :=
    algebraMap_surjective_of_corner Φ' hΦ' hrange' inferInstance hc1 hc2
  have hcardD : Nat.card (D' j₀) = 2 ^ f :=
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
  have hsB : (s : GL (Fin n ⊕ Fin n) F) ∈ adjCent (Subgroup.zpowers (t : GL (Fin n ⊕ Fin n) F))
      (isInvol_spAdj (n := n) (F := F)) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun g hg => ?_, hAu⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute (t : GL (Fin n ⊕ Fin n) F) s from hAB.symm) k).eq
  rw [← himg'] at hsB
  obtain ⟨a, haU, has⟩ := hsB
  have haj : coordHom D' d' j₀ a ∈ matUnitary hT := coordHom_mem_matUnitary hτ' hπ' hπj₀ haU
  have hinner : coordHom D' d' j₀ a ∈ Sf' j₀ →
      ∃ k ∈ (Y.comap (StatedSp n F).subtype).map ψ,
        ∀ l ∈ (Y.comap (StatedSp n F).subtype).map ψ, x⁻¹ * l * x = k⁻¹ * l * k := by
    intro haS
    obtain ⟨ã, hãorb, hãa⟩ := exists_mem_orbitGroup_fix hτ' hπ' hπj₀ haj
    have hãcore : ã ∈ coreOf π' hτ' Sf' j₀ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (by rw [hãa]; exact haS), hãorb⟩
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
    calc x⁻¹ * ψ u * x = x⁻¹ * (x * ψ (s⁻¹ * u * s) * x⁻¹) * x := by rw [← h1]
      _ = ψ (s⁻¹ * u * s) := by group
      _ = ψ (kk⁻¹ * u * kk) := by rw [hconj]
      _ = (ψ kk)⁻¹ * ψ u * ψ kk := by rw [map_mul, map_mul, map_inv]
  have hgood : CFSG.IsQuasisimple (sesqUnitaryGroup
      (Matrix.toBilin' (H : Matrix (Fin (d' j₀)) (Fin (d' j₀)) (D' j₀)))) →
      (s' = 1 → 2 ≤ f) → (s' ≠ 1 → 2 ≤ s' ∧ (s', f) ≠ (2, 1)) →
      ¬ GGNbrClauseFiveMarking p x ((Y.comap (StatedSp n F).subtype).map ψ) := by
    intro hqU hs1 hs2
    have hU : CFSG.IsQuasisimple (matUnitary hT) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e6.symm hqU
    have hSfU : Sf' j₀ = matUnitary hT :=
      le_antisymm hSfle (le_of_ggDer_le (LayerFacts.ggCommutator_eq_of_isQuasisimple hU) le_rfl
        hderj.choose_spec)
    let eK : ↥((Y.comap (StatedSp n F).subtype).map ψ) ≃* StatedSp s' (D' j₀) :=
      e1.trans (e2.trans (e3.trans (e4.trans ((MulEquiv.subgroupCongr hSfU).trans
        (e6.trans e7)))))
    have hinn := hinner (hSfU ▸ haj)
    by_cases h1 : s' = 1
    · subst h1
      exact hSp1 G _ f (D' j₀) hcardD (hs1 rfl) ⟨eK⟩ p hp hp2 hq1 hq2 x hinn
    · obtain ⟨h2, h3⟩ := hs2 h1
      exact not_ggNbrClauseFiveMarking_sp hcardD eK h2 h3 hp hp2 hq1 hq2 hinn
  rcases card_eq_two_or_four_le (D := D' j₀) with hD2 | hD4
  · have hf1 : f = 1 := by
      rw [hcardD] at hD2
      exact Nat.pow_right_injective (le_refl 2) (show 2 ^ f = 2 ^ 1 by simpa using hD2)
    by_cases h6 : 6 ≤ d' j₀
    · refine hgood (CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hB
        hn (by omega) (Or.inr (Or.inr ⟨hD2, by omega⟩))) (fun h => by omega) (fun _ => ?_)
      refine ⟨by omega, fun h => ?_⟩
      have := congrArg Prod.fst h
      simp only at this
      omega
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
      obtain ⟨hqc, -⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour (e6.trans E)
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
      exact hA6 G _ ⟨e1.trans (e2.trans (e3.trans (e4.trans ((MulEquiv.subgroupCongr hSfeq).trans
        (eS.symm.trans E6)))))⟩ p hp hp2 hp3 x
  · have hf2 : 2 ≤ f := by
      rw [hcardD] at hD4
      by_contra h
      push Not at h
      interval_cases f <;> norm_num at hD4
    refine hgood (CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hB hn
      (by omega) (Or.inl hD4)) (fun _ => hf2) (fun h => ⟨by omega, fun h' => ?_⟩)
    have := congrArg Prod.snd h'
    simp only at this
    omega

end Main

end ClNonsplit

section Tag

theorem ggNonsplitNbrMarkingTag_PSp (hSp1 : ClNonsplit.GGNonsplitNbrSpOneInput)
    (hA6 : ClNonsplit.GGNonsplitNbrAltSixInput) : GGNonsplitNbrMarkingTag .PSp := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K K' hK hpK hK' hKK' _
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  rw [← hrange] at hK hK'
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by have := hadm.2.1; omega)
  obtain ⟨s, hs⟩ := LayerPDiv.exists_mem_ggConjPairs_sp (F := GaloisField 2 f) hrk ψ hker hxD
  obtain ⟨t, ht⟩ := LayerPDiv.exists_mem_ggConjPairs_sp (F := GaloisField 2 f) hrk ψ hker hyD
  exact ClNonsplit.not_ggNbrClauseFiveMarking_nbr_sp hSp1 hA6 hF hker hp hp2 hq1 hq2 hx hy hxy hs ht
    hK hpK hK' hKK'

theorem ggNonsplitTag_PSp (hSp1 : ClNonsplit.GGNonsplitNbrSpOneInput)
    (hA6 : ClNonsplit.GGNonsplitNbrAltSixInput) : GGNonsplitTag .PSp :=
  ⟨ggNonsplitCompLiftTag_PSp, ggNonsplitNbrMarkingTag_PSp hSp1 hA6⟩

end Tag

end CFSG.StandardType
