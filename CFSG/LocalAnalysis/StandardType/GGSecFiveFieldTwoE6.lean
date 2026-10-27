module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeE6Inner
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExcCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExcOrbit
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoMemberModels
import CFSG.LocalAnalysis.StandardType.GGSelectedPOmegaMinusLong
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoE8
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExcOrbit
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc

public section

namespace CFSG.StandardType.FieldTwoE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
open CFSG.RankThree.PartOne.KE (d4Nodes)
open CFSG.RankThree.Chevalley (rootChar_pow_eq_one)

section Triality

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem not_triality_d4Class_E6_of_mod (S : LangSetup Tag.E6 L p₀)
    (hFr : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr))
    (hq : S.D.q % 3 = 2) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24)
    (hn1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hn2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) : False := by
  classical
  obtain ⟨v, hΨ, hρ⟩ := CFSG.StandardType.ExcThreeAtTwo.exists_pinned_d4Class_E6 S hT hap h1 i
    hrank hcard
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at hn1
  rw [componentOrbitLength_eq_one hfin hρ, mul_one] at hn2
  obtain ⟨Fr, hFr', hΦ'⟩ := hFr
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • γ := fun γ hγ =>
    S.rho_eq_smul_of_frob hFr' hΦ' hn hγ
  have hinv : ∀ β, IsRoot Tag.E6 β → rootChar a (w • β) = (rootChar a β)⁻¹ := by
    intro β hβ
    have h3 := rootChar_pow_eq_one hap β
    have hq' : S.D.q = 3 * (S.D.q / 3) + 2 := by omega
    rw [← hρw β hβ, S.frob.rootChar_eq a hT β hβ, hq', pow_add, pow_mul, h3, one_pow, one_mul,
      eq_inv_iff_mul_eq_one, ← pow_succ]
    exact h3
  have hker : ∀ γ ∈ Ψ, IsRoot Tag.E6 γ ∧ rootChar a γ = 1 := fun γ hγ => ⟨hγ.1.1, hγ.1.2⟩
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmaps : MapsJ Tag.E6 (d4Set Tag.E6) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action d4Base_E6 hmaps
  have hlin0 : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), w₀ • α = permLattice π α :=
    fun α hα => by
      have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set Tag.E6)
        (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
      rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hmem0 : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    rw [hlin0 α hα]
    refine ⟨?_, fun k hk => ?_⟩
    · rw [← hlin0 α hα]
      exact IsRoot.smul hα.1 w₀
    · have hk' : π.symm k ∉ d4Nodes Tag.E6 := fun h => hk (by
        have h' := hπ.mem_d4Set (show π.symm k ∈ d4Set Tag.E6 from h)
        rw [Equiv.apply_symm_apply] at h'
        exact h')
      exact hα.2 _ hk'
  have hconjW : ∀ y ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6),
      w₀ * y * w₀⁻¹ ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
    have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map (MulAut.conj w₀).toMonoidHom ≤
        parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
      rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨π j, hπ.mem_d4Set hj, ?_⟩
      change simple Tag.E6 (π j) = w₀ * simple Tag.E6 j * w₀⁻¹
      rw [← rootReflection_single, ← rootReflection_eq_conj (hw₀π j hj)]
    exact fun y hy => hle ⟨y, hy, rfl⟩
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply hn1
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have hπ2 : π * π ≠ 1 := by
    intro hππ
    apply hn2
    refine ⟨v * (u * (w₀ * u * w₀⁻¹)) * v⁻¹,
      hΨ ▸ conj_mem_closure_rootReflection v (mul_mem hu (hconjW u hu)), ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    have hγr : IsRoot Tag.E6 (v • α) := hγ.1.1
    have hw2 : w₀ • w₀ • α = α := by
      rw [hlin0 _ (hmem0 α hα), hlin0 α hα, ← permLattice_mul, hππ]
      rfl
    rw [Function.iterate_succ_apply, Function.iterate_one, hρw _ hγr,
      hρw _ ((isRoot_smul_iff w).2 hγr)]
    calc w • w • v • α = v • ((v⁻¹ * w * v) • (v⁻¹ * w * v) • α) := by
          simp only [mul_smul, smul_inv_smul]
      _ = v • (u • w₀ • u • w₀ • α) := by rw [hw₀]; simp only [mul_smul]
      _ = v • (u • (w₀ * u * w₀⁻¹) • w₀ • w₀ • α) := by simp only [mul_smul, inv_smul_smul]
      _ = (v * (u * (w₀ * u * w₀⁻¹)) * v⁻¹) • v • α := by
          rw [hw2]
          simp only [mul_smul, inv_smul_smul]
  have hπ3 : π * π * π = 1 := by
    have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
    have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
    have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
    rcases hπ.eq_cycle hπ1 hπ2 with rfl | rfl
    · have h := List.formPerm_pow_length_eq_one_of_nodup
        (l := [e6Idx (τ := Tag.E6) 1, e6Idx 2, e6Idx 4]) (by simp [h12, h14, h24])
      simpa [pow_succ, mul_assoc] using h
    · have h := List.formPerm_pow_length_eq_one_of_nodup
        (l := [e6Idx (τ := Tag.E6) 1, e6Idx 4, e6Idx 2]) (by simp [h12, h14, Ne.symm h24])
      simpa [pow_succ, mul_assoc] using h
  have hu2 : w₀ * (w₀ * u * w₀⁻¹) * w₀⁻¹ ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) :=
    hconjW _ (hconjW u hu)
  have hx : v * (u * (w₀ * u * w₀⁻¹) * (w₀ * (w₀ * u * w₀⁻¹) * w₀⁻¹)) * v⁻¹ ∈
      Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ Ψ, s = rootReflection γ} :=
    hΨ ▸ conj_mem_closure_rootReflection v (mul_mem (mul_mem hu (hconjW u hu)) hu2)
  have hux : ∀ γ ∈ Ψ, (w * w * w) • γ =
      (v * (u * (w₀ * u * w₀⁻¹) * (w₀ * (w₀ * u * w₀⁻¹) * w₀⁻¹)) * v⁻¹) • γ := by
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    have hw3 : w₀ • w₀ • w₀ • α = α := by
      rw [hlin0 _ (hmem0 _ (hmem0 α hα)), hlin0 _ (hmem0 α hα), hlin0 α hα, ← permLattice_mul,
        ← permLattice_mul, hπ3]
      rfl
    calc (w * w * w) • v • α =
          v • ((v⁻¹ * w * v) • (v⁻¹ * w * v) • (v⁻¹ * w * v) • α) := by
          simp only [mul_smul, smul_inv_smul]
      _ = v • (u • w₀ • u • w₀ • u • w₀ • α) := by rw [hw₀]; simp only [mul_smul]
      _ = v • (u • (w₀ * u * w₀⁻¹) • (w₀ * (w₀ * u * w₀⁻¹) * w₀⁻¹) • w₀ • w₀ • w₀ • α) := by
          simp only [mul_smul, inv_smul_smul]
      _ = (v * (u * (w₀ * u * w₀⁻¹) * (w₀ * (w₀ * u * w₀⁻¹) * w₀⁻¹)) * v⁻¹) • v • α := by
          rw [hw3]
          simp only [mul_smul, inv_smul_smul]
  have hinv3 : ∀ β, IsRoot Tag.E6 β → rootChar a ((w * w * w) • β) = (rootChar a β)⁻¹ := by
    intro β hβ
    have hβ1 : IsRoot Tag.E6 (w • β) := (isRoot_smul_iff w).2 hβ
    have hβ2 : IsRoot Tag.E6 (w • w • β) := (isRoot_smul_iff w).2 hβ1
    rw [mul_smul, mul_smul, hinv _ hβ2, hinv _ hβ1, hinv _ hβ, inv_inv]
  exact h1 (CFSG.LocalAnalysis.GLTheoremA.T171D4.rootDiagUnit_eq_one_of_inv_weyl_d4 hap hinv3 hΨ
    hker hx hux)

end Triality

section Main

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.StandardType.GGFinModel CFSG.StandardType.LieKnownR2.ExcPos
open CFSG.Open (StatedLieTag)


theorem ggSecFiveQTwoFieldTwoSelectedAt_E6 : GGSecFiveQTwoFieldTwoSelectedAt .E6 := by
  have ht4 : FieldTwoExc.GGExcFour .E6 := .inr (.inl rfl)
  refine FieldTwoExc.ggSecFiveQTwoFieldTwoSelectedAt_exc_of_noncentral ht4
    FieldTwoExc.exists_selectedSL2Model_E6 ?_
  intro G _ _ B Bs x L D J hC hq n f ψ hpres hdiag hnc
  obtain ⟨hf, hinj, F, i, hT, hap, h1, hqs, hL, hstd, hmem⟩ :=
    FieldTwoExc.exists_member_of_ggConfig_exc (Or.inl rfl) hC hq ψ hpres hdiag hnc
  subst hf
  obtain rfl : n = 0 := hpres.1.1.2.2
  have hLG0 : L ≤ ggG0 3 B x L D J := le_ggG0_left 3 B x L D J
  obtain ⟨-, hZ⟩ := FieldTwoExc.injective_and_center_eq_bot hpres.2.1.1 hpres.2.1.2
    (FieldTwoExc.center_ggU_exc_eq_bot (Or.inl rfl) 0)
  have hτ : langTag StatedLieTag.E6 = .D4 ∨ langTag StatedLieTag.E6 = .E6 ∨
      langTag StatedLieTag.E6 = .E7 ∨ langTag StatedLieTag.E6 = .E8 := Or.inr (Or.inl rfl)
  have hq2 : F.setup.D.q = 2 := F.q_eq
  have hlow : compRank (componentRoots (rootCharHom (F.coord x)) i) ≤ 3 →
      componentOrbitLength F.setup.ρ (componentRoots (rootCharHom (F.coord x)) i) = 1 ∧
        2 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i) ∧
        (twistKind F.setup.ρ (rootCharHom (F.coord x)) i = .suN →
          3 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i)) := fun h3 =>
    FieldTwoExc.orbit_eq_one_of_typeA hC hq hLG0 hZ F hT hap h1 hqs hL
      (FieldTwoExc.typeA_of_compRank_le_three hτ hstd h3)
  have h6 : (langTag StatedLieTag.E6).rank = 6 := rfl
  have horb : componentOrbitLength F.setup.ρ (componentRoots (rootCharHom (F.coord x)) i) = 1 := by
    by_cases h4 : 4 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i)
    · exact FieldTwoExc.orbit_eq_one_of_two_mul_lt F hT (by omega)
    · exact (hlow (by omega)).1
  have hsr := LangRat.componentOrbitLength_mul_compRank_le F.setup hT i
  obtain ⟨M, α, hCM, -, hrange, hker, -, -, hroots⟩ := hmem horb
  have finish : ∀ (t' : StatedLieTag) (n' : ℕ), M = ggU t' n' 1 →
      StatedLieAdmissible t' n' 2 1 → 2 ≤ (ggU t' n' 1).D.rank →
      (∃ δ : Fin (ggU t' n' 1).D.rank → ℤ, δ ∈ (ggU t' n' 1).D.roots ∧
        GGLongRoot (ggU t' n' 1).D δ ∧
        Nonempty (SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ)) →
      ∃ (t' : StatedLieTag) (n' : ℕ) (ψ' : (ggU t' n' 1).K →* G),
        StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
          ψ'.ker ≤ Subgroup.center (ggU t' n' 1).K ∧ ψ'.range = L ∧
          ∃ (γ : Fin (ggU .E6 0 1).D.rank → ℤ) (δ : Fin (ggU t' n' 1).D.rank → ℤ)
            (model : SelectedRoot.SelectedSL2Model (ggU .E6 0 1).D (GaloisField 2 1) γ)
            (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ),
            ∃ u₀ : (ggU .E6 0 1).K,
              ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp model.phi).range =
                (ψ'.comp model'.phi).range := by
    rintro t' n' hM hadm hrk ⟨δ, hδ, hlong, ⟨model'⟩⟩
    subst hM
    obtain ⟨β', hβ', -, k, hR, -⟩ := hroots δ hδ hlong
    have hαψ : ∀ m, α m ∈ ψ.range := fun m => by
      rw [hpres.2.1.1]
      exact hLG0 (hrange ▸ ⟨m, rfl⟩)
    let ψ₀ : (ggU t' n' 1).K →* (ggU .E6 0 1).K :=
      (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (α.codRestrict ψ.range hαψ)
    have hψψ₀ : ψ.comp ψ₀ = α := MonoidHom.ext fun m =>
      congrArg Subtype.val ((MonoidHom.ofInjective hinj).apply_symm_apply ⟨α m, hαψ m⟩)
    have hML : (L.comap ψ).map ψ = L :=
      Subgroup.map_comap_eq_self (by rw [hpres.2.1.1]; exact hLG0)
    have hrange₀ : ψ₀.range = L.comap ψ := by
      apply Subgroup.map_injective hinj
      rw [hML, ← MonoidHom.range_comp, hψψ₀, hrange]
    have hker₀ : ψ₀.ker ≤ Subgroup.center (ggU t' n' 1).K := fun m hm => hker (by
      rw [MonoidHom.mem_ker, ← hψψ₀, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hm, map_one])
    have hroot : ((ggU t' n' 1).D.rootGroup δ).map ψ₀ =
        ((ggU .E6 0 1).D.rootGroup β').map (MulAut.conj k).toMonoidHom := by
      apply Subgroup.map_injective hinj
      rw [Subgroup.map_map, hψψ₀, hR]
      rfl
    exact FieldTwoE8.selected_of_member ψ hinj hML ψ₀ hadm hrk hker₀ hrange₀ model' hβ' k hroot
  have hFr : ∃ Fr : GGL →+* GGL, (∀ c, Fr c = c ^ F.setup.D.q) ∧
      F.setup.D.Φ = Units.map (entrywiseHom Fr) :=
    ⟨ggFrobT 1, fun c => by rw [ggFrobT_apply, hq2, pow_one], by
      rw [show F.setup.D.Φ = ggPhi .E6 1 from F.Φ_eq]
      rfl⟩
  rcases hCM with ⟨hr1, -⟩ | ⟨-, hr2, -, hM⟩ | ⟨hkind, hM⟩ | ⟨-, hr4, -, hM⟩ | ⟨hkind, hM⟩ |
    ⟨-, hE⟩ | ⟨hkind, hexc⟩
  ·
    have := (hlow (by omega)).2.1
    omega
  ·
    exact finish .PSL _ hM
      ⟨Nat.prime_two, le_rfl, by omega, fun h => by have := (Prod.mk.inj h).1; omega,
        fun h => by have := (Prod.mk.inj h).1; omega⟩
      (show 2 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i) from hr2)
      (SelectedRoot.exists_selectedSL2Model_PSL_long hr2)
  ·
    have h3 : 3 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i) := by
      by_cases h4 : 4 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i)
      · omega
      · exact (hlow (by omega)).2.2 hkind
    exact finish .PSU _ hM
      ⟨Nat.prime_two, le_rfl, by omega, fun h => by have := (Prod.mk.inj h).1; omega⟩
      (show 2 ≤ (compRank (componentRoots (rootCharHom (F.coord x)) i) + 1) / 2 by omega)
      (SelectedRoot.exists_selectedSL2Model_PSU_long (by omega))
  ·
    obtain ⟨m, hm⟩ : ∃ m, compRank (componentRoots (rootCharHom (F.coord x)) i) = m + 4 :=
      ⟨_, (Nat.sub_add_cancel hr4).symm⟩
    rw [hm] at hM
    exact finish .POmegaPlus (m + 4) hM ⟨Nat.prime_two, le_rfl, by omega⟩
      (show 2 ≤ m + 4 by omega) (SelectedRoot.exists_selectedSL2Model_POmegaPlus_long (by omega))
  ·
    have h4 := FieldTwoExc.four_le_compRank_of_twoD hkind
    exact finish .POmegaMinus _ hM ⟨Nat.prime_two, le_rfl, h4⟩
      (show 2 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i) - 1 by omega)
      (SelectedRoot.exists_selectedSL2Model_POmegaMinus_long h4)
  ·
    exfalso
    rcases hE with ⟨-, h72, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩
    · exact h1 (rootDiagUnit_eq_one_of_ncard i (by rw [h72]; decide))
    · rw [horb, one_mul] at hsr
      omega
    · rw [horb, one_mul] at hsr
      omega
  ·
    exfalso
    rcases FieldTwoExc.exc_cases hkind with ⟨-, h72⟩ | ⟨h4, h24, hn1, hn2⟩
    · exact h1 (rootDiagUnit_eq_one_of_ncard i (by rw [h72]; decide))
    · exact not_triality_d4Class_E6_of_mod F.setup hFr (by rw [hq2]) hT hap h1 i h4 h24 hn1 hn2

end Main

end CFSG.StandardType.FieldTwoE6

end
