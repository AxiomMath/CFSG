module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.LieType.Chevalley.OrthogonalUnionBruhat

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ntpA2_ggCompFieldAt_of_centerQuotEquiv {G H : Type} [Group G] [Group H]
    {X : Subgroup G} {Y : Subgroup H} {Q : ℕ}
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* ↥Y ⧸ Subgroup.center ↥Y) (h : GGCompFieldAt Q X) :
    GGCompFieldAt Q Y := by
  obtain ⟨lab, hlab, hchar, hdeg, h1, h2, h3, hhas, R, instR, hR, ⟨φ⟩⟩ := h
  letI : Group R := instR
  refine ⟨lab, hlab, hchar, hdeg, h1, h2, h3, ?_, R, instR, hR, ⟨θ.symm.trans φ⟩⟩
  unfold GGHasLabel at hhas ⊢
  refine largeEvenRawDatum_mono ?_ hhas
  rintro R' _ I F ⟨ψ⟩
  exact ⟨θ.symm.trans ψ⟩

private lemma a2o_cube_eq_one_of_commute {α : Type} [Fintype α]
    (hcard : Fintype.card α = 3) (s r : Equiv.Perm α) (hs3 : s ^ 3 = 1) (hsne : s ≠ 1)
    (hcomm : r * s = s * r) : r ^ 3 = 1 := by
  let e : α ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  let s3 : Equiv.Perm (Fin 3) := e.permCongrHom s
  let r3 : Equiv.Perm (Fin 3) := e.permCongrHom r
  have key : ∀ s r : Equiv.Perm (Fin 3), s ^ 3 = 1 → s ≠ 1 → r * s = s * r → r ^ 3 = 1 := by
    decide
  have hs3' : s3 ^ 3 = 1 := by
    change (e.permCongrHom s) ^ 3 = 1
    rw [← map_pow, hs3, map_one]
  have hsne' : s3 ≠ 1 := by
    intro h
    apply hsne
    apply e.permCongrHom.injective
    rw [map_one]
    exact h
  have hcomm' : r3 * s3 = s3 * r3 := by
    change e.permCongrHom r * e.permCongrHom s = e.permCongrHom s * e.permCongrHom r
    rw [← map_mul, ← map_mul, hcomm]
  have hr3 : r3 ^ 3 = 1 := key s3 r3 hs3' hsne' hcomm'
  apply e.permCongrHom.injective
  rw [map_pow, map_one]
  change r3 ^ 3 = 1
  exact hr3

private lemma a2o_perm_three_transitive {α : Type} [Fintype α]
    (hcard : Fintype.card α = 3) (s : Equiv.Perm α) (hs3 : s ^ 3 = 1) (hsne : s ≠ 1) :
    ∀ i j : α, ∃ k : ℕ, (s ^ k) i = j := by
  let e : α ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  let s3 : Equiv.Perm (Fin 3) := e.permCongrHom s
  have key : ∀ t : Equiv.Perm (Fin 3), t ^ 3 = 1 → t ≠ 1 →
      ∀ x y : Fin 3, ∃ k : Fin 4, (t ^ (k : ℕ)) x = y := by
    decide
  have hs3' : s3 ^ 3 = 1 := by
    change (e.permCongrHom s) ^ 3 = 1
    rw [← map_pow, hs3, map_one]
  have hsne' : s3 ≠ 1 := by
    intro h
    apply hsne
    apply e.permCongrHom.injective
    rw [map_one]
    exact h
  intro i j
  obtain ⟨k, hk⟩ := key s3 hs3' hsne' (e i) (e j)
  refine ⟨(k : ℕ), ?_⟩
  have hmap : ∀ n : ℕ, (s3 ^ n) (e i) = e ((s ^ n) i) := by
    intro n
    rw [show s3 = e.permCongrHom s from rfl, ← map_pow]
    change e.permCongr (s ^ n) (e i) = e ((s ^ n) i)
    rw [Equiv.permCongr_def, Equiv.trans_apply, Equiv.trans_apply]
    simp
  rw [hmap] at hk
  exact e.injective hk

theorem ntpA2_orbitDichotomy
    (hS : LangNontoralStructure) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L)
    (hpair : OrderThreeOutsideConnected S a n) (hker : (rootCharKernel a).ncard = 18) :
    (∀ i : KernelComponent (rootCharHom a),
        componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) ∨
      (∀ i : KernelComponent (rootCharHom a),
        componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3) := by
  classical
  obtain ⟨hcard3, σ, hσne, hσ3, hσspan, hcompat, hlayer⟩ := hS L p₀ S a n hpair hker
  let I := KernelComponent (rootCharHom a)
  haveI hFin : Finite I := Nat.finite_of_card_ne_zero (by rw [hcard3]; norm_num)
  letI : Fintype I := Fintype.ofFinite _
  haveI : DecidableEq I := Classical.decEq _
  have hcardF : Fintype.card I = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard3
  have hT : rootDiagUnit .E6 a ∈ S.D.torus := hpair.2.1
  have hΨinj : Function.Injective (componentRoots (rootCharHom a)) := by
    intro i j h
    obtain ⟨β, hβ⟩ := Quotient.exists_rep i
    exact eq_of_mem_componentRoots (α := (β : kernelRoots (rootCharHom a)).1)
      (show (β : kernelRoots (rootCharHom a)).1 ∈ componentRoots (rootCharHom a) i from
        ⟨β.2, hβ⟩)
      (h ▸ (show (β : kernelRoots (rootCharHom a)).1 ∈ componentRoots (rootCharHom a) i from
        ⟨β.2, hβ⟩))
  have hkerρ : ∀ γ ∈ kernelRoots (rootCharHom a), S.ρ γ ∈ kernelRoots (rootCharHom a) := by
    intro γ hγ
    rw [kernelRoots_rootCharHom] at hγ ⊢
    exact ⟨(S.frob.isRoot_iff γ).2 hγ.1, by
      rw [S.frob.rootChar_eq a hT γ hγ.1, hγ.2, one_pow]⟩
  have himg : ∀ i : I, ∃ j : I,
      ⇑S.ρ '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) j :=
    fun i => CFSG.StandardType.TableCRes.exists_image_component_of_stable
      (χ := rootCharHom a) hkerρ S.frob.iform_eq i
  let ρbar : I → I := fun i => Classical.choose (himg i)
  have hρbar : ∀ i : I, ⇑S.ρ '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) (ρbar i) :=
    fun i => Classical.choose_spec (himg i)
  have hρbar_inj : Function.Injective ρbar := by
    intro i j hij
    apply hΨinj
    have h1 : ⇑S.ρ '' componentRoots (rootCharHom a) i =
        ⇑S.ρ '' componentRoots (rootCharHom a) j := by rw [hρbar i, hρbar j, hij]
    exact Set.image_injective.mpr S.ρ.injective h1
  let ρp : Equiv.Perm I :=
    Equiv.ofBijective ρbar ⟨hρbar_inj, Finite.injective_iff_surjective.mp hρbar_inj⟩
  have hρp_spec : ∀ i : I, ⇑S.ρ '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) (ρp i) := fun i => hρbar i
  have hcomm_point : ∀ i : I, ρp (σ i) = σ (ρp i) := by
    intro i
    apply hΨinj
    rw [← hρp_spec (σ i), ← hcompat i (ρp i) (hρp_spec i)]
  have hcomm : ρp * σ = σ * ρp := by
    ext i
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact hcomm_point i
  have hρp3 : ρp ^ 3 = 1 := a2o_cube_eq_one_of_commute hcardF σ ρp hσ3 hσne hcomm
  have hiter : ∀ (m : ℕ) (i : I),
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[m] '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) ((ρp : I → I)^[m] i) := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [Function.iterate_succ', Set.image_comp, ih i, hρp_spec, Function.iterate_succ_apply']
  have hcomm_iter : ∀ (m : ℕ) (i : I),
      (ρp : I → I)^[m] (σ i) = σ ((ρp : I → I)^[m] i) := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih i, hcomm_point]
  have hd_sigma : ∀ i : I,
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) (σ i)) =
        componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
    intro i
    unfold componentOrbitLength
    congr 1
    ext m
    constructor
    · rintro ⟨hm, hper⟩
      refine ⟨hm, ?_⟩
      rw [hiter m (σ i), hcomm_iter m i] at hper
      have hfix : (ρp : I → I)^[m] i = i := σ.injective (hΨinj hper)
      rw [hiter m i, hfix]
    · rintro ⟨hm, hper⟩
      refine ⟨hm, ?_⟩
      have hfix : (ρp : I → I)^[m] i = i := by
        apply hΨinj
        rw [← hiter m i, hper]
      rw [hiter m (σ i), hcomm_iter m i, hfix]
  have hd13 : ∀ i : I,
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∨
        componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3 := by
    intro i
    have h3iter : (ρp : I → I)^[3] i = i := by
      rw [← Equiv.Perm.coe_pow, hρp3]
      rfl
    have h3per : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[3] '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i := by
      rw [hiter 3 i, h3iter]
    have hPne : {m : ℕ | 0 < m ∧
        (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[m] '' componentRoots (rootCharHom a) i =
          componentRoots (rootCharHom a) i}.Nonempty :=
      ⟨3, by norm_num, h3per⟩
    have hpos : 0 < componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
      (Nat.sInf_mem hPne).1
    have hle : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≤ 3 :=
      Nat.sInf_le (show 3 ∈ {m : ℕ | 0 < m ∧
        (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[m] '' componentRoots (rootCharHom a) i =
          componentRoots (rootCharHom a) i} from ⟨by norm_num, h3per⟩)
    have hne2 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≠ 2 := by
      intro hd2
      have h1not : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[1] '' componentRoots (rootCharHom a) i ≠
          componentRoots (rootCharHom a) i := by
        intro h1
        have hle1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≤ 1 :=
          Nat.sInf_le (show 1 ∈ {m : ℕ | 0 < m ∧
            (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[m] '' componentRoots (rootCharHom a) i =
              componentRoots (rootCharHom a) i} from ⟨by norm_num, h1⟩)
        omega
      have hbi : (ρp : I → I) i ≠ i := by
        intro h
        refine h1not ?_
        calc (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[1] '' componentRoots (rootCharHom a) i
            = componentRoots (rootCharHom a) ((ρp : I → I)^[1] i) := hiter 1 i
          _ = componentRoots (rootCharHom a) (ρp i) := by simp
          _ = componentRoots (rootCharHom a) i := by simp [h]
      have h2per : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] '' componentRoots (rootCharHom a) i =
          componentRoots (rootCharHom a) i := by
        have h2mem : 2 ∈ {m : ℕ | 0 < m ∧
            (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[m] '' componentRoots (rootCharHom a) i =
              componentRoots (rootCharHom a) i} := by
          rw [← hd2]
          exact Nat.sInf_mem hPne
        exact h2mem.2
      have hbi2 : (ρp : I → I)^[2] i = i := by
        apply hΨinj
        rw [← hiter 2 i, h2per]
      have hstep : (ρp : I → I)^[3] i = (ρp : I → I) i := by
        rw [Function.iterate_succ_apply', hbi2]
      rw [h3iter] at hstep
      exact hbi hstep.symm
    omega
  have hσtrans : ∀ i j : I, ∃ k : ℕ, (σ ^ k) i = j :=
    a2o_perm_three_transitive hcardF σ hσ3 hσne
  have dconst : ∀ i j : I, componentOrbitLength S.ρ (componentRoots (rootCharHom a) j) =
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
    intro i j
    obtain ⟨k, hk⟩ := hσtrans i j
    have hstep : ∀ m : ℕ,
        componentOrbitLength S.ρ (componentRoots (rootCharHom a) ((σ ^ m) i)) =
          componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, hd_sigma ((σ ^ m) i), ih]
    rw [← hk]
    exact hstep k
  haveI : Nonempty I := (Fintype.card_pos_iff).mp (by rw [hcardF]; norm_num)
  let i₀ : I := Classical.choice ‹Nonempty I›
  rcases hd13 i₀ with h | h
  · left
    intro i
    rw [dconst i₀ i]
    exact h
  · right
    intro i
    rw [dconst i₀ i]
    exact h

end CFSG.StandardType.NTPlane

end
