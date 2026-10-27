module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClCorner
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClSU
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClMark

public section

namespace CFSG.StandardType

namespace ClNonsplit

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix LayerCores LayerFacts
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

@[expose] def GGNonsplitNbrHermInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K' : Subgroup G) (D : Type) [Field D] [Finite D]
    [CharP D 2] (d : ℕ) (T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D)
    (hT : IsInvol T), (∃ c : D, T (Matrix.scalar (Fin d) c) ≠ Matrix.scalar (Fin d) c) →
    ∀ S : Subgroup (GL (Fin d) D), S ≤ matUnitary hT →
      (∃ k, LayerFacts.ggDer (matUnitary hT) k ≤ S) → CFSG.IsQuasisimple S →
    ∀ φ : ↥S →* G, φ.range = K' → φ.ker ≤ Subgroup.center ↥S →
    ∀ f : ℕ, Nat.card D = (2 ^ f) ^ 2 → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ 2 ^ f - 1 →
      ¬ p ∣ 2 ^ f + 1 → ∀ x : G, (∃ k ∈ K', ∀ l ∈ K', x⁻¹ * l * x = k⁻¹ * l * k) →
        ¬ GGNbrClauseFiveMarking p x K'

section Semi

variable {K : Type} [Field K] {f n : ℕ}

theorem suAdj_smul (h : UnitaryFieldData 2 f K) (c : K) (X : Matrix (Fin n) (Fin n) K) :
    suAdj h (c • X) = h.bar c • suAdj h X := by
  ext i j
  simp [suAdj, Matrix.transpose_apply, map_mul]

variable {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] [∀ i, Algebra K (D i)] {d : Fin r → ℕ}
  {τ : PiMat D d → PiMat D d} {π : Fin r → Fin r}

theorem tauFix_scalar_algebraMap_of_semilinear (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {b : Fin r} (hb : π b = b) {ρ : K → K}
    (hτK : ∀ (c : K) (y : PiMat D d), τ (c • y) = ρ c • τ y) (c : K) :
    tauFix τ b (Matrix.scalar (Fin (d b)) (algebraMap K (D b) c)) =
      Matrix.scalar (Fin (d b)) (algebraMap K (D b) (ρ c)) := by
  classical
  have hsc : ∀ c' : K, Matrix.scalar (Fin (d b)) (algebraMap K (D b) c') =
      c' • (1 : Matrix (Fin (d b)) (Fin (d b)) (D b)) := by
    intro c'
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Algebra.smul_def]
    · simp [hij, Matrix.one_apply_ne hij]
  have h1 : (Pi.single b (Matrix.scalar (Fin (d b)) (algebraMap K (D b) c)) : PiMat D d) =
      c • piE D d b := by
    funext i
    by_cases hi : i = b
    · subst hi
      simp [piE, hsc]
    · simp [piE, hi]
  show τ (Pi.single b _) b = _
  rw [h1, hτK, hπ, hb, hsc]
  simp [piE]

end Semi

section Main

variable {K : Type} [Field K] {f n : ℕ} {G : Type} [Group G]

theorem not_ggNbrClauseFiveMarking_nbr_su (hHerm : GGNonsplitNbrHermInput) [Finite G]
    (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    {ψ : ↥(unitarySU 2 f K n) →* G} (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x) {A₀ B₀ : GL (Fin n) K}
    (hA₀ : (x, A₀) ∈ SUTorus.suPairs ψ) (hB₀ : (y, B₀) ∈ SUTorus.suPairs ψ) {X X' : Subgroup G}
    (hX : IsComponentOf X (ψ.range ⊓ Subgroup.centralizer {x})) (hpX : ¬ p ∣ Nat.card X)
    (hX' : IsComponentOf X' (ψ.range ⊓ Subgroup.centralizer {y})) (hXX' : X ≤ X') :
    ¬ GGNbrClauseFiveMarking p x X' := by
  classical
  have := h.finite
  have : CharP K 2 := h.charP
  have hcK : Nat.card K = (2 ^ f) ^ 2 := h.card_eq_sq
  have hpK : ¬ p ∣ Nat.card K - 1 := by
    rw [hcK, show (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) by
      simpa using Nat.sq_sub_sq (2 ^ f) 1]
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
    · exact hq2 h1
    · exact hq1 h1
  obtain ⟨A, hA, hAp⟩ := exists_mem_suPairs_pow_eq_one h hn hnq hker hp hpK hx hA₀
  obtain ⟨B, hB, hBp⟩ := exists_mem_suPairs_pow_eq_one h hn hnq hker hp hpK hy hB₀
  have hAB := mul_comm_of_mem_suPairs h hn hnq hker hp hpK hxy hA hB hAp
  have hAu := mem_unitaryOf_of_pow_eq_one h (by omega) hp hpK hA.1 hAp
  have hBu := mem_unitaryOf_of_pow_eq_one h (by omega) hp hpK hB.1 hBp
  obtain ⟨c₀, hc₀⟩ := exists_add_bar_eq_one h
  have hsymd : ∀ C : GL (Fin n) K, ∃ Y : Matrix (Fin n) (Fin n) K,
      (∀ g ∈ Subgroup.zpowers C, Y * (g : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K) * Y) ∧ Y + suAdj h Y = 1 := fun C =>
    ⟨c₀ • 1, fun g _ => by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one],
      by rw [suAdj_smul_one, ← add_smul, hc₀, one_smul]⟩
  obtain ⟨r, D, d, _, _, _, _, _, Φ, τ, hτ, π, hπ, Sf, hΦ, -, -, himg, hy0, hSle, hSn, hder,
    hq⟩ := exists_coreData (isInvol_suAdj (n := n) h) (natCast_card_zpowers_ne_zero hp hp2 hAp)
      (adj_stab_zpowers (isInvol_suAdj (n := n) h) hAu) (hsymd A)
  obtain ⟨r', D', d', _, _, _, _, _, Φ', τ', hτ', π', hπ', Sf', hΦ', hR', hτΦ', himg', hy',
    hSle', hSn', hder', hq'⟩ := exists_coreData (isInvol_suAdj (n := n) h)
      (natCast_card_zpowers_ne_zero hp hp2 hBp) (adj_stab_zpowers (isInvol_suAdj (n := n) h) hBu)
      (hsymd B)
  have hΦu : Function.Injective (Units.map Φ.toMonoidHom) :=
    Units.map_injective (f := Φ.toMonoidHom) hΦ
  have hΦu' : Function.Injective (Units.map Φ'.toMonoidHom) :=
    Units.map_injective (f := Φ'.toMonoidHom) hΦ'
  have hFx : IsCoreFamily (adjCent (Subgroup.zpowers A) (isInvol_suAdj (n := n) h))
      (fun c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥} =>
        (coreOf π hτ Sf c.1).map (Units.map Φ.toMonoidHom)) := by
    have h1 := (isCoreFamily_coreOf hτ hπ hSle hSn hder hq).map _ hΦu
    rwa [himg] at h1
  have hFy : IsCoreFamily (adjCent (Subgroup.zpowers B) (isInvol_suAdj (n := n) h))
      (fun c : {b : Fin r' // b ≤ π' b ∧ Sf' b ≠ ⊥} =>
        (coreOf π' hτ' Sf' c.1).map (Units.map Φ'.toMonoidHom)) := by
    have h1 := (isCoreFamily_coreOf hτ' hπ' hSle' hSn' hder' hq').map _ hΦu'
    rwa [himg'] at h1
  obtain ⟨hFx', hcardx⟩ := isCoreFamily_su h hFx
  obtain ⟨hFy', -⟩ := isCoreFamily_su h hFy
  rw [← centralizer_inducedMatrices_zpowers h hn hnq hker hA] at hFx'
  rw [← centralizer_inducedMatrices_zpowers h hn hnq hker hB] at hFy'
  have hEA : ∀ (z : G) (C : GL (Fin n) K), (z, C) ∈ SUTorus.suPairs ψ →
      ∀ e ∈ Subgroup.zpowers z, ∃ B', (e, B') ∈ SUTorus.suPairs ψ := by
    intro z C hzC e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ⟨C ^ k, (SUTorus.suPairs ψ).zpow_mem hzC k⟩
  have hcz : ∀ z : G, Subgroup.centralizer (Subgroup.zpowers z : Set G) =
      Subgroup.centralizer {z} := fun z => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hcz] at hX hX'
  obtain ⟨⟨b, hbπ, hSb⟩, hXeq⟩ := LayerPDiv.exists_eq_map_of_isComponentOf ψ hker
    (map_ggSUCent_le (hEA x A hA)) (normal_map_ggSUCent hker) (commutator_le_map_ggSUCent hker)
    _ hFx'.1 hFx'.2.1 hFx'.2.2.1 hFx'.2.2.2.1 hX
  set Sc := (coreOf π hτ Sf b).map (Units.map Φ.toMonoidHom) with hScdef
  have hXeq' : X = (Sc.comap (unitarySU 2 f K n).subtype).map ψ := hXeq
  have hpS : ¬ p ∣ Nat.card (Sf b) := by
    intro hd
    apply hpX
    rw [hXeq']
    refine LayerPDiv.dvd_card_map_of_perfect ψ hker
      (LayerFacts.ggCommutator_eq_of_isQuasisimple (hFx'.2.2.1 ⟨b, hbπ, hSb⟩)) hp ?_
    rw [hcardx ⟨b, hbπ, hSb⟩]
    show p ∣ Nat.card ((coreOf π hτ Sf b).map (Units.map Φ.toMonoidHom))
    rw [Subgroup.card_map_of_injective hΦu,
      Nat.card_congr (Equiv.ofBijective _ (bijective_coreOf hτ hπ hSle b))]
    exact hd
  have hMB := fix_of_not_dvd (isInvol_suAdj (n := n) h) hΦ hτ hπ himg hy0 hSle hder
    ((hq b).resolve_left hSb).1 hp hp2 hpS hBu hBp hAB
  obtain ⟨j₀, hc1, hc2, hπj₀, hSf'ne, hScle⟩ := exists_le_coreOf_of_fix
    (isInvol_suAdj (n := n) h) hΦ' hR' hτ' hπ' himg' hder' (hFx.2.2.1 ⟨b, hbπ, hSb⟩)
    ((hFx.1 ⟨b, hbπ, hSb⟩).trans inf_le_right) hMB
  set c' : {b : Fin r' // b ≤ π' b ∧ Sf' b ≠ ⊥} := ⟨j₀, le_of_eq hπj₀.symm, hSf'ne⟩ with hc'
  set Y := (coreOf π' hτ' Sf' j₀).map (Units.map Φ'.toMonoidHom) with hYdef
  have hYle : Y ≤ (unitarySU 2 f K n).subtype.range := by
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
  have hYcomp : IsComponentOf ((Y.comap (unitarySU 2 f K n).subtype).map ψ)
      (ψ.range ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G)) :=
    LinNonsplit.isComponentOf_map_of_le ψ hker (map_ggSUCent_le (hEA y B hB))
      (normal_map_ggSUCent hker) (hFy'.1 c') (hFy'.2.1 c') (hFy'.2.2.1 c')
  have hXY : X ≤ (Y.comap (unitarySU 2 f K n).subtype).map ψ := by
    rw [hXeq']
    exact Subgroup.map_mono (Subgroup.comap_mono hScle)
  have hX'eq : X' = (Y.comap (unitarySU 2 f K n).subtype).map ψ := by
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hX' hYcomp with h1 | h1
    · exact h1
    · exfalso
      have h2 : X' ≤ Subgroup.centralizer
          (((Y.comap (unitarySU 2 f K n).subtype).map ψ : Subgroup G) : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
      exact CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hX.2.2
        (hXX'.trans (h2.trans (Subgroup.centralizer_le hXY)))
  rw [hX'eq]
  have hrange' : ∀ X0 : Matrix (Fin n) (Fin n) K,
      X0 * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * X0 →
        X0 ∈ Set.range Φ' := fun X0 hX0 => (hR' X0).mpr fun g hg => commute_of_mem_zpowers hX0 hg
  have hcardD : Nat.card (D' j₀) = (2 ^ f) ^ 2 :=
    (card_eq_of_corner Φ' hΦ' hrange' inferInstance hc1 hc2).trans hcK
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
  have hpD : ¬ p ∣ Nat.card (D' j₀) - 1 := by
    rw [hcardD]
    rwa [hcK] at hpK
  let e2 : ↥(Y.comap (unitarySU 2 f K n).subtype) ≃* ↥Y :=
    ((Y.comap (unitarySU 2 f K n).subtype).equivMapOfInjective _
      (Subgroup.subtype_injective _)).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hYle))
  let e3 : ↥Y ≃* ↥(coreOf π' hτ' Sf' j₀) :=
    ((coreOf π' hτ' Sf' j₀).equivMapOfInjective _ hΦu').symm
  let e4 : ↥(coreOf π' hτ' Sf' j₀) ≃* ↥(Sf' j₀) :=
    MulEquiv.ofBijective _ (bijective_coreOf hτ' hπ' hSle' j₀)
  let ε : ↥(Sf' j₀) ≃* ↥(Y.comap (unitarySU 2 f K n).subtype) := (e2.trans (e3.trans e4)).symm
  set φ : ↥(Sf' j₀) →* G :=
    (ψ.comp (Y.comap (unitarySU 2 f K n).subtype).subtype).comp ε.toMonoidHom with hφ
  have hφrange : φ.range = (Y.comap (unitarySU 2 f K n).subtype).map ψ := by
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
    have h1 : ((ε z : ↥(Y.comap (unitarySU 2 f K n).subtype)) : ↥(unitarySU 2 f K n)) ∈ ψ.ker :=
      hz
    have h2 := Subgroup.mem_center_iff.mp (hker h1)
      ((ε w : ↥(Y.comap (unitarySU 2 f K n).subtype)) : ↥(unitarySU 2 f K n))
    apply ε.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    exact h2
  have hinn : ∃ k ∈ (Y.comap (unitarySU 2 f K n).subtype).map ψ,
      ∀ l ∈ (Y.comap (unitarySU 2 f K n).subtype).map ψ, x⁻¹ * l * x = k⁻¹ * l * k := by
    have hAB' : A ∈ adjCent (Subgroup.zpowers B) (isInvol_suAdj (n := n) h) := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun g hg => ?_, hAu⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact (Commute.zpow_left (show Commute B A from hAB.symm) k).eq
    rw [← himg'] at hAB'
    obtain ⟨a, haU, haA⟩ := hAB'
    have hap : a ^ p = 1 := hΦu' (by rw [map_pow, haA, hAp, map_one])
    have haj : coordHom D' d' j₀ a ∈ matUnitary hT := coordHom_mem_matUnitary hτ' hπ' hπj₀ haU
    have hajp : coordHom D' d' j₀ a ^ p = 1 := by rw [← map_pow, hap, map_one]
    have haS : coordHom D' d' j₀ a ∈ Sf' j₀ :=
      mem_core_of_pow_eq_one_herm hT hkj hSfle hderj hqj hp hp2 hpD haj hajp
    obtain ⟨ã, hãorb, hãa⟩ := exists_mem_orbitGroup_fix hτ' hπ' hπj₀ haj
    have hãcore : ã ∈ coreOf π' hτ' Sf' j₀ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (by rw [hãa]; exact haS), hãorb⟩
    have hãY : Units.map Φ'.toMonoidHom ã ∈ Y := ⟨ã, hãcore, rfl⟩
    obtain ⟨kk, hkk⟩ := hYle hãY
    refine ⟨ψ kk, ⟨kk, (show (unitarySU 2 f K n).subtype kk ∈ Y by rw [hkk]; exact hãY), rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨γ, hγcore, hγu⟩ := (Subgroup.mem_comap.mp hu : (unitarySU 2 f K n).subtype u ∈ Y)
    have hconjGL : A⁻¹ * (u : GL (Fin n) K) * A =
        ((kk⁻¹ * u * kk : ↥(unitarySU 2 f K n)) : GL (Fin n) K) := by
      have e := conj_eq_conj_of_mem_orbitGroup hτ' hπ' haU (Subgroup.mem_inf.mp hγcore).2 hãorb
        hãa
      have e' := congrArg (Units.map Φ'.toMonoidHom) e
      simp only [map_mul, map_inv] at e'
      rw [haA, hγu, ← hkk] at e'
      simpa using e'
    have hpair := (SUTorus.suPairs ψ).inv_mem hA
    rw [Prod.inv_mk] at hpair
    have h1 := (SUTorus.mem_suPairs.mp hpair).2 u (kk⁻¹ * u * kk)
      (hconjGL.symm.trans (by rw [inv_inv]))
    rw [inv_inv] at h1
    rw [h1, map_mul, map_mul, map_inv]
  exact hHerm G _ (D' j₀) (d' j₀) (tauFix τ' j₀) hT hkj (Sf' j₀) hSfle hderj hqj φ hφrange hφker
    f hcardD p hp hp2 hq1 hq2 x hinn

end Main

end ClNonsplit

section Tag

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits InnerDiagSU CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

theorem ClNonsplit.not_ggNbrClauseFiveMarking_nbr_su_antidiag
    (hHerm : ClNonsplit.GGNonsplitNbrHermInput) {G : Type} [Group G] [Finite G] {f m : ℕ}
    (hf : 1 ≤ f) (hn : 4 ≤ m + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x)
    (hxD : GGPsiInnerDiag (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)) ψ x)
    (hyD : GGPsiInnerDiag (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)) ψ y)
    {X X' : Subgroup G} (hX : IsComponentOf X (ψ.range ⊓ Subgroup.centralizer {x}))
    (hpX : ¬ p ∣ Nat.card X) (hX' : IsComponentOf X' (ψ.range ⊓ Subgroup.centralizer {y}))
    (hXX' : X ≤ X') : ¬ GGNbrClauseFiveMarking p x X' := by
  classical
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Finite (GaloisField 2 (2 * f)) := h.finite
  have : CharP (GaloisField 2 (2 * f)) 2 := h.charP
  obtain ⟨P, hP⟩ := exists_wittMatrix hF (m + 1)
  have hSU : SUid (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) =
      unitarySU 2 f (GaloisField 2 (2 * f)) (m + 1) := SUid_eq_statedSU hF (m + 1)
  set Φ := (conjEquiv P hP).trans (MulEquiv.subgroupCongr hSU) with hΦ
  set ψ₁ := ψ.comp Φ.symm.toMonoidHom with hψ₁
  have hr₁ : ψ₁.range = ψ.range := SUTorus.range_comp_symm ψ Φ
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 f (GaloisField 2 (2 * f)) (m + 1)) :=
    SUTorus.ker_comp_symm_le hker Φ
  have hpair : ∀ z : G, GGPsiInnerDiag (Unitary.rootDatum (card_galoisField_two_mul 2 f hf)
      (m + 1)) ψ z → ∃ C, (z, C) ∈ SUTorus.suPairs ψ₁ := by
    intro z hz
    obtain ⟨A, hA, hAc⟩ := suInnerDiagConj hF hn G ψ hker z hz
    have h1 : (z⁻¹, P * A * P⁻¹) ∈ SUTorus.suPairs ψ₁ :=
      SUTorus.mem_suPairs_transfer P hP hSU hA fun u => by
        rw [inv_inv]
        exact hAc u
    refine ⟨(P * A * P⁻¹)⁻¹, ?_⟩
    have h2 := (SUTorus.suPairs ψ₁).inv_mem h1
    rwa [Prod.inv_mk, inv_inv] at h2
  obtain ⟨A₀, hA₀⟩ := hpair x hxD
  obtain ⟨B₀, hB₀⟩ := hpair y hyD
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  rw [← hr₁] at hX hX'
  exact ClNonsplit.not_ggNbrClauseFiveMarking_nbr_su hHerm h (by omega) hnq hker₁ hp hp2 hq1 hq2
    hx hy hxy hA₀ hB₀ hX hpX hX' hXX'

theorem ggNonsplitNbrMarkingTag_PSU (hHerm : ClNonsplit.GGNonsplitNbrHermInput) :
    GGNonsplitNbrMarkingTag .PSU := by
  intro G _ _ n f
  by_cases hf : 1 ≤ f
  · have hU : ggU .PSU n f =
        ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [hU]
    intro ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K K' hK hpK hK' hKK' _
    obtain ⟨⟨-, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    have hn : 4 ≤ n := by
      have : 2 ≤ n / 2 := hrk
      omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← hrange] at hK hK'
    exact ClNonsplit.not_ggNbrClauseFiveMarking_nbr_su_antidiag hHerm hf hn hker hp hp2 hq1 hq2
      hx hy hxy hxD hyD hK hpK hK' hKK'
  · intro ψ G₀ hpres
    exact absurd hpres.1.1.2.1 hf

theorem ggNonsplitTag_PSU (hHerm : ClNonsplit.GGNonsplitNbrHermInput) : GGNonsplitTag .PSU :=
  ⟨ggNonsplitCompLiftTag_PSU, ggNonsplitNbrMarkingTag_PSU hHerm⟩

end Tag

end CFSG.StandardType
