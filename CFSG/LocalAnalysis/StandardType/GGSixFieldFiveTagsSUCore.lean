module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsSUHerm

public section

namespace CFSG.StandardType

namespace FieldFiveSU

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix LayerCores LayerFacts ClNonsplit
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem exists_fixedCore_component_su {K : Type} [Field K] {n : ℕ} {G : Type} [Group G]
    [Finite G] (h : UnitaryFieldData 2 1 K) (hn : 4 ≤ n) {ψ : ↥(unitarySU 2 1 K n) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K n)) {z : G} {t : GL (Fin n) K}
    (ht : (z, t) ∈ SUTorus.suPairs ψ) (ht5 : t ^ 5 = 1) {S : Subgroup (GL (Fin n) K)}
    (hSq : CFSG.IsQuasisimple S) (hSU : S ≤ unitaryOf (isInvol_suAdj (n := n) h))
    (hSB : ∀ M ∈ S, M * t = t * M ∧
      (M : Matrix (Fin n) (Fin n) K) * ((t : Matrix (Fin n) (Fin n) K) - 1) =
        (t : Matrix (Fin n) (Fin n) K) - 1) :
    ∃ L' : Subgroup G, IsComponentOf L' (ψ.range ⊓ Subgroup.centralizer {z}) ∧
      (S.comap (unitarySU 2 1 K n).subtype).map ψ ≤ L' ∧ 5 ∣ Nat.card L' ∧
      ∀ (w : G) (s : GL (Fin n) K), (w, s) ∈ SUTorus.suPairs ψ → s ^ 5 = 1 → s * t = t * s →
        ¬ GGNbrClauseFiveMarking 5 w L' ∧
          (w ∈ Subgroup.centralizer (L' : Set G) → ∀ M ∈ S, M * s = s * M ∧
            (M : Matrix (Fin n) (Fin n) K) * ((s : Matrix (Fin n) (Fin n) K) - 1) =
              (s : Matrix (Fin n) (Fin n) K) - 1) := by
  classical
  have := h.finite
  have : CharP K 2 := h.charP
  have hp : (5 : ℕ).Prime := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hK4 : Nat.card K = 4 := by rw [h.card_eq_sq]; norm_num
  have hpK : ¬ 5 ∣ Nat.card K - 1 := by rw [hK4]; norm_num
  have hnq : (n, 2 ^ 1) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have htU := mem_unitaryOf_of_pow_eq_one h (by omega) hp hpK ht.1 ht5
  obtain ⟨c₀, hc₀⟩ := exists_add_bar_eq_one h
  have hsymd : ∃ Y : Matrix (Fin n) (Fin n) K,
      (∀ g ∈ Subgroup.zpowers t, Y * (g : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K) * Y) ∧ Y + suAdj h Y = 1 :=
    ⟨c₀ • 1, fun g _ => by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one],
      by rw [suAdj_smul_one, ← add_smul, hc₀, one_smul]⟩
  obtain ⟨r', D', d', _, _, _, _, _, Φ', τ', hτ', π', hπ', Sf', hΦ', hR', hτΦ', himg', -,
    hSle', hSn', hder', hq'⟩ := exists_coreData (isInvol_suAdj (n := n) h)
      (natCast_card_zpowers_ne_zero hp hp2 ht5) (adj_stab_zpowers (isInvol_suAdj (n := n) h) htU)
      hsymd
  have hΦu' : Function.Injective (Units.map Φ'.toMonoidHom) :=
    Units.map_injective (f := Φ'.toMonoidHom) hΦ'
  have hFy : IsCoreFamily (adjCent (Subgroup.zpowers t) (isInvol_suAdj (n := n) h))
      (fun c : {b : Fin r' // b ≤ π' b ∧ Sf' b ≠ ⊥} =>
        (coreOf π' hτ' Sf' c.1).map (Units.map Φ'.toMonoidHom)) := by
    have h1 := (isCoreFamily_coreOf hτ' hπ' hSle' hSn' hder' hq').map _ hΦu'
    rwa [himg'] at h1
  obtain ⟨hFy', -⟩ := isCoreFamily_su h hFy
  rw [← centralizer_inducedMatrices_zpowers h (by omega) hnq hker ht] at hFy'
  have hEA : ∀ e ∈ Subgroup.zpowers z, ∃ B', (e, B') ∈ SUTorus.suPairs ψ := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ⟨t ^ k, (SUTorus.suPairs ψ).zpow_mem ht k⟩
  have hcz : Subgroup.centralizer (Subgroup.zpowers z : Set G) = Subgroup.centralizer {z} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨j₀, hc1, hc2, hπj₀, hSf'ne, hSle⟩ := exists_le_coreOf_of_fix
    (isInvol_suAdj (n := n) h) hΦ' hR' hτ' hπ' himg' hder' hSq hSU hSB
  set c' : {b : Fin r' // b ≤ π' b ∧ Sf' b ≠ ⊥} := ⟨j₀, le_of_eq hπj₀.symm, hSf'ne⟩ with hc'
  set Y := (coreOf π' hτ' Sf' j₀).map (Units.map Φ'.toMonoidHom) with hYdef
  have hYle : Y ≤ (unitarySU 2 1 K n).subtype.range := by
    intro g hg
    have hgU := (Subgroup.mem_inf.mp (hFy.1 c' hg)).2
    have hgdet : g ∈ (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
      have hperf := LayerFacts.ggCommutator_eq_of_isQuasisimple (hFy.2.2.1 c')
      have hg' : g ∈ ⁅Y, Y⁆ := by rw [hperf]; exact hg
      exact ((Subgroup.commutator_mono le_top le_top).trans
        (Abelianization.commutator_subset_ker _)) hg'
    refine ⟨⟨g, (mem_unitarySU_iff_suAdj h).mpr ⟨hgU, ?_⟩⟩, rfl⟩
    rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply,
      Units.val_one] at hgdet
    exact hgdet
  have hYcomp : IsComponentOf ((Y.comap (unitarySU 2 1 K n).subtype).map ψ)
      (ψ.range ⊓ Subgroup.centralizer (Subgroup.zpowers z : Set G)) :=
    LinNonsplit.isComponentOf_map_of_le ψ hker (map_ggSUCent_le hEA)
      (normal_map_ggSUCent hker) (hFy'.1 c') (hFy'.2.1 c') (hFy'.2.2.1 c')
  rw [hcz] at hYcomp
  have hrange' : ∀ X0 : Matrix (Fin n) (Fin n) K,
      X0 * (t : Matrix (Fin n) (Fin n) K) = (t : Matrix (Fin n) (Fin n) K) * X0 →
        X0 ∈ Set.range Φ' := fun X0 hX0 => (hR' X0).mpr fun g hg => commute_of_mem_zpowers hX0 hg
  have hcardD : Nat.card (D' j₀) = 4 :=
    (card_eq_of_corner Φ' hΦ' hrange' inferInstance hc1 hc2).trans hK4
  have hτK : ∀ (c : K) (z : PiMat D' d'), τ' (c • z) = h.bar c • τ' z := fun c z =>
    hΦ' (by simp only [map_smul, hτΦ', suAdj_smul])
  have hT := isInvol_tauFix hτ' hπ' hπj₀
  have hkj : ∃ c : D' j₀, tauFix τ' j₀ (Matrix.scalar (Fin (d' j₀)) c) ≠
      Matrix.scalar (Fin (d' j₀)) c := by
    obtain ⟨c₁, hc₁⟩ := h.exists_bar_ne
    refine ⟨algebraMap K (D' j₀) c₁, ?_⟩
    rw [tauFix_scalar_algebraMap_of_semilinear hπ' hπj₀ hτK c₁]
    intro heq
    exact hc₁ ((algebraMap K (D' j₀)).injective (scalar_injective heq))
  have hfg : factorGroup π' hτ' hπ' j₀ = matUnitary hT := by
    unfold factorGroup
    split_ifs
    rfl
  have hSfle : Sf' j₀ ≤ matUnitary hT := hfg ▸ hSle' j₀
  have hderj : ∃ k, LayerFacts.ggDer (matUnitary hT) k ≤ Sf' j₀ := hfg ▸ hder' j₀
  have hqj : CFSG.IsQuasisimple (Sf' j₀) := ((hq' j₀).resolve_left hSf'ne).1
  have hpD : ¬ 5 ∣ Nat.card (D' j₀) - 1 := by rw [hcardD]; norm_num
  obtain ⟨hcen, h5S⟩ := herm_core_facts hT hkj hcardD hSfle hderj hqj
  set Y' := Y.comap (unitarySU 2 1 K n).subtype with hY'def
  let e2 : ↥Y' ≃* ↥Y :=
    (Y'.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hYle))
  let e3 : ↥Y ≃* ↥(coreOf π' hτ' Sf' j₀) :=
    ((coreOf π' hτ' Sf' j₀).equivMapOfInjective _ hΦu').symm
  let e4 : ↥(coreOf π' hτ' Sf' j₀) ≃* ↥(Sf' j₀) :=
    MulEquiv.ofBijective _ (bijective_coreOf hτ' hπ' hSle' j₀)
  let ε : ↥(Sf' j₀) ≃* ↥Y' := (e2.trans (e3.trans e4)).symm
  set φ : ↥(Sf' j₀) →* G := (ψ.comp Y'.subtype).comp ε.toMonoidHom with hφ
  have hφrange : φ.range = Y'.map ψ := by
    ext g
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨ε z, (ε z).2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨ε.symm ⟨u, hu⟩, ?_⟩
      rw [hφ]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        Subgroup.coe_subtype]
  have hφker : φ.ker ≤ Subgroup.center ↥(Sf' j₀) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 : ((ε z : ↥Y') : ↥(unitarySU 2 1 K n)) ∈ ψ.ker := hz
    have h2 := Subgroup.mem_center_iff.mp (hker h1) ((ε w : ↥Y') : ↥(unitarySU 2 1 K n))
    apply ε.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    exact h2
  have hqY' : CFSG.IsQuasisimple Y' := CFSG.LocalCores.isQuasisimple_of_mulEquiv ε hqj
  have hperfY' : ⁅Y', Y'⁆ = Y' := LayerFacts.ggCommutator_eq_of_isQuasisimple hqY'
  refine ⟨Y'.map ψ, hYcomp, Subgroup.map_mono (Subgroup.comap_mono hSle), ?_,
    fun w s hs hs5 hst => ?_⟩
  ·
    refine LayerPDiv.dvd_card_map_of_perfect ψ hker hperfY' hp ?_
    rw [← Nat.card_congr ε.toEquiv]
    exact h5S
  have hsU := mem_unitaryOf_of_pow_eq_one h (by omega) hp hpK hs.1 hs5
  have hsB : s ∈ adjCent (Subgroup.zpowers t) (isInvol_suAdj (n := n) h) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun g hg => ?_, hsU⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute t s from hst.symm) k).eq
  rw [← himg'] at hsB
  obtain ⟨a, haU, has⟩ := hsB
  have ha5 : a ^ 5 = 1 := hΦu' (by rw [map_pow, has, hs5, map_one])
  have haj : coordHom D' d' j₀ a ∈ matUnitary hT := coordHom_mem_matUnitary hτ' hπ' hπj₀ haU
  have haj5 : coordHom D' d' j₀ a ^ 5 = 1 := by rw [← map_pow, ha5, map_one]
  have haS : coordHom D' d' j₀ a ∈ Sf' j₀ :=
    mem_core_of_pow_eq_one_herm hT hkj hSfle hderj hqj hp hp2 hpD haj haj5
  refine ⟨?_, fun hwK M hM => ?_⟩
  ·
    have hinn : ∃ k ∈ Y'.map ψ, ∀ l ∈ Y'.map ψ, w⁻¹ * l * w = k⁻¹ * l * k := by
      obtain ⟨ã, hãorb, hãa⟩ := exists_mem_orbitGroup_fix hτ' hπ' hπj₀ haj
      have hãcore : ã ∈ coreOf π' hτ' Sf' j₀ :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (by rw [hãa]; exact haS), hãorb⟩
      have hãY : Units.map Φ'.toMonoidHom ã ∈ Y := ⟨ã, hãcore, rfl⟩
      obtain ⟨kk, hkk⟩ := hYle hãY
      refine ⟨ψ kk, ⟨kk, (show (unitarySU 2 1 K n).subtype kk ∈ Y by rw [hkk]; exact hãY), rfl⟩,
        ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨γ, hγcore, hγu⟩ := (Subgroup.mem_comap.mp hu : (unitarySU 2 1 K n).subtype u ∈ Y)
      have hconjGL : s⁻¹ * (u : GL (Fin n) K) * s =
          ((kk⁻¹ * u * kk : ↥(unitarySU 2 1 K n)) : GL (Fin n) K) := by
        have e := conj_eq_conj_of_mem_orbitGroup hτ' hπ' haU (Subgroup.mem_inf.mp hγcore).2 hãorb
          hãa
        have e' := congrArg (Units.map Φ'.toMonoidHom) e
        simp only [map_mul, map_inv] at e'
        rw [has, hγu, ← hkk] at e'
        simpa using e'
      have hpair := (SUTorus.suPairs ψ).inv_mem hs
      rw [Prod.inv_mk] at hpair
      have h1 := (SUTorus.mem_suPairs.mp hpair).2 u (kk⁻¹ * u * kk)
        (hconjGL.symm.trans (by rw [inv_inv]))
      rw [inv_inv] at h1
      rw [h1, map_mul, map_mul, map_inv]
    exact ggNonsplitNbrHermInput_holds G _ (D' j₀) (d' j₀) (tauFix τ' j₀) hT hkj (Sf' j₀) hSfle
      hderj hqj φ hφrange hφker 1 (by rw [hcardD]; norm_num) 5 hp hp2 (by norm_num) (by norm_num)
      w hinn
  ·
    have hconj : ∀ u : ↥Y', s * ((u : ↥(unitarySU 2 1 K n)) : GL (Fin n) K) * s⁻¹ =
        ((u : ↥(unitarySU 2 1 K n)) : GL (Fin n) K) := by
      have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq ψ hker
        (LayerFacts.ggIsPerfect_of_commutator_eq hperfY')
        (((unitarySU 2 1 K n).normalizerMonoidHom ⟨s, hs.1⟩).toMonoidHom.comp Y'.subtype)
        Y'.subtype (fun u => by
          have h1 := hs.2 (u : ↥(unitarySU 2 1 K n))
            ((unitarySU 2 1 K n).normalizerMonoidHom ⟨s, hs.1⟩ (u : ↥(unitarySU 2 1 K n))) rfl
          have h2 : w * ψ (u : ↥(unitarySU 2 1 K n)) * w⁻¹ = ψ (u : ↥(unitarySU 2 1 K n)) := by
            rw [(Subgroup.mem_centralizer_iff.mp hwK _ ⟨u, u.2, rfl⟩).symm,
              mul_inv_cancel_right]
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
          rw [← h1, h2])
      intro u
      exact congrArg Subtype.val (key u)
    have hcomm : ∀ g ∈ Sf' j₀, coordHom D' d' j₀ a * g = g * coordHom D' d' j₀ a := by
      intro g hg
      obtain ⟨⟨γ, hγcore⟩, hγg⟩ := (bijective_coreOf hτ' hπ' hSle' j₀).2 ⟨g, hg⟩
      have hγg' : coordHom D' d' j₀ γ = g := congrArg Subtype.val hγg
      have hγY : Units.map Φ'.toMonoidHom γ ∈ Y := ⟨γ, hγcore, rfl⟩
      obtain ⟨u, hu⟩ := hYle hγY
      have huY : u ∈ Y' := show (unitarySU 2 1 K n).subtype u ∈ Y by rw [hu]; exact hγY
      have h3 : s * (u : GL (Fin n) K) = (u : GL (Fin n) K) * s := by
        have h4 := hconj ⟨u, huY⟩
        calc s * (u : GL (Fin n) K) = s * (u : GL (Fin n) K) * s⁻¹ * s := by group
          _ = (u : GL (Fin n) K) * s := by rw [h4]
      have h5 : Units.map Φ'.toMonoidHom (a * γ) = Units.map Φ'.toMonoidHom (γ * a) := by
        rw [map_mul, map_mul, has]
        have hu' : (u : GL (Fin n) K) = Units.map Φ'.toMonoidHom γ := hu
        rw [← hu']
        exact h3
      have h6 := congrArg (coordHom D' d' j₀) (hΦu' h5)
      rw [map_mul, map_mul, hγg'] at h6
      exact h6
    have ha1 : coordHom D' d' j₀ a = 1 := hcen _ haj5 hcomm
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
    have hγΦ : ((Units.map Φ'.toMonoidHom γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Φ' (γ : PiMat D' d') := rfl
    have hsΦ : (s : Matrix (Fin n) (Fin n) K) = Φ' (a : PiMat D' d') := by rw [← has]; rfl
    constructor
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, hγΦ, hsΦ, ← map_mul, h1, map_mul]
    · rw [hγΦ, hsΦ, ← map_one Φ', ← map_sub, ← map_mul, h2]

end FieldFiveSU

end CFSG.StandardType
