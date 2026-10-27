module

public import CFSG.RankThree.PartOne.KC.OrthogonalNonsingStab
public import CFSG.Mathlib.LinearAlgebra.PerfectCentralizer
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
import CFSG.LieType.SeitzGeneration.OrthEx

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] [CharP K 2] in
private theorem apply_mem_of_commute_fixedFree_supported
    {W : Submodule K V} (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    {ρ g : V ≃ₗ[K] V} (hρ : ρ ∈ supportedDerived Q W)
    (hρfix : ∀ z ∈ W, ρ z = z → z = 0) (hcomm : Commute g ρ) :
    ∀ w ∈ W, g w ∈ W := by
  have hWon : PolarNondegOn Q W := polarNondegOn_of_nondegenerate hW
  have hdisp : ∀ x : V, ρ x - x ∈ W := by
    intro x
    obtain ⟨w, hw, p, hp, hwpx⟩ := suppExists_add_of_isCompl (isCompl_suppPerp hWon) x
    have hρp : ρ p = p := supportedDerived_apply_perp hρ hp
    have hρw : ρ w ∈ W := supportedDerived_apply_mem hρ hw
    have hx : ρ x - x = ρ w - w := by
      rw [← hwpx, map_add, hρp]
      abel
    rw [hx]
    exact Submodule.sub_mem W hρw hw
  let d : W →ₗ[K] W := ((ρ : V →ₗ[K] V) - 1).restrict (p := W) (q := W) fun x _ => hdisp x
  have hdker : ∀ x : W, d x = 0 → x = 0 := by
    intro x hx
    have hval : ρ (x : V) - (x : V) = 0 := by
      have h := congrArg Subtype.val hx
      simpa [d] using h
    exact Subtype.ext (hρfix (x : V) x.2 (sub_eq_zero.mp hval))
  have hdinj : Function.Injective d := by
    intro x y hxy
    exact sub_eq_zero.mp (hdker (x - y) (by rw [map_sub, hxy, sub_self]))
  have hdsurj : Function.Surjective d := LinearMap.surjective_of_injective hdinj
  intro w hw
  obtain ⟨y, hy⟩ := hdsurj ⟨w, hw⟩
  have hyval : ρ (y : V) - (y : V) = w := by
    have h := congrArg Subtype.val hy
    simpa [d] using h
  have hρcomm : g (ρ (y : V)) = ρ (g (y : V)) :=
    congrArg (fun e : V ≃ₗ[K] V => e (y : V)) hcomm.eq
  have hstep : g w = ρ (g (y : V)) - g (y : V) := by
    rw [← hyval, map_sub, hρcomm]
  rw [hstep]
  exact hdisp (g (y : V))

theorem apply_eq_of_perfect_commute_supportedDerived_nonsingular_basis
    {W : Submodule K V} (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWdim : finrank K W = 2) (b : Module.Basis (Fin 2) K W)
    (hQ0 : Q (b 0 : V) ≠ 0) (hQ1 : Q (b 1 : V) ≠ 0)
    (P : Subgroup (V ≃ₗ[K] V)) [Group.IsPerfect P]
    (hcomm : ∀ g : P, ∀ r ∈ supportedDerived Q W, Commute (g : V ≃ₗ[K] V) r) :
    ∀ g : P, ∀ w : W, (g : V ≃ₗ[K] V) (w : V) = w := by
  obtain ⟨ρ, hρ, hρfix⟩ :=
    exists_mem_supportedDerived_fixedFree_of_nonsingular_basis hW b hQ0 hQ1
  have hρO : ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    supportedDerived_le_orthogonalGroup (polarNondegOn_of_nondegenerate hW) hρ
  have hPW : ∀ g : P, ∀ w : W, (g : V ≃ₗ[K] V) (w : V) ∈ W := by
    intro g w
    exact apply_mem_of_commute_fixedFree_supported hW hρ hρfix (hcomm g ρ hρ) w w.2
  have haW : ∀ w : W, ρ (w : V) ∈ W := fun w => supportedDerived_apply_mem hρ w.2
  have hNS : ∀ c : K, ∃ w : W, ρ (w : V) ≠ c • (w : V) := by
    intro c
    refine ⟨b 0, ?_⟩
    intro heq
    have hQ : Q (ρ (b 0 : V)) = Q (b 0 : V) :=
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hρO (b 0 : V)
    have hc2 : c ^ 2 = 1 := by
      rw [heq, map_smul_eq_sq] at hQ
      exact mul_right_cancel₀ hQ0 (by simpa using hQ)
    have hc1 : c = 1 := CharTwo.sq_inj.mp (by simpa using hc2)
    have hfix : ρ (b 0 : V) = b 0 := by rw [heq, hc1, one_smul]
    exact b.ne_zero 0 (Subtype.ext (hρfix (b 0 : V) (b 0).2 hfix))
  exact CFSG.LinearAlgebra.fixes_plane_of_perfect_commute_nonscalar P W hWdim ρ hPW haW hNS
    (fun g => (hcomm g ρ hρ).symm)

omit [CharP K 2] in
private theorem exists_nonsingular_basis_of_hypPair
    {U : Type} [AddCommGroup U] [Module K U] {R : QuadraticForm K U}
    (hdim : finrank K U = 2) (P : HypPair R) (hK : 2 < Nat.card K) :
    ∃ b : Module.Basis (Fin 2) K U, R (b 0) ≠ 0 ∧ R (b 1) ≠ 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_pair zero_ne_one, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hK
  obtain ⟨μ, _, hμ⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hμ0 : μ ≠ 0 := by intro h; exact hμ (by simp [h])
  have hμ1 : μ ≠ 1 := by intro h; exact hμ (by simp [h])
  let v : U := P.e + P.f
  let w : U := P.e + μ • P.f
  have hv : R v = 1 := by
    simp only [v, QuadraticMap.map_add R, P.Q_e, P.Q_f, P.polar_ef, zero_add]
  have hw : R w = μ := by
    simp only [w, QuadraticMap.map_add R, P.Q_e, map_smul_eq_sq, P.Q_f,
      polar_smul_right_eq, P.polar_ef, mul_zero, mul_one, zero_add]
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hw
    exact hμ0 hw.symm
  have hlin : LinearIndependent K ![v, w] := by
    rw [linearIndependent_fin2]
    change w ≠ 0 ∧ ∀ a : K, a • w ≠ v
    refine ⟨hw0, ?_⟩
    intro a heq
    have he := congrArg (polar R P.e) heq
    have hf := congrArg (polar R P.f) heq
    simp only [v, w, polar_smul_right_eq, polar_add_right, P.polar_ee, P.polar_ff,
      P.polar_ef, P.polar_fe, mul_zero, mul_one, zero_add, add_zero] at he hf
    rw [hf, one_mul] at he
    exact hμ1 he
  let b : Module.Basis (Fin 2) K U :=
    basisOfLinearIndependentOfCardEqFinrank hlin (by simp [hdim])
  have hb0 : b 0 = v := by dsimp only [b]; simp
  have hb1 : b 1 = w := by dsimp only [b]; simp
  exact ⟨b, by rw [hb0, hv]; exact one_ne_zero, by rw [hb1, hw]; exact hμ0⟩

omit [CharP K 2] in
private theorem exists_nonsingular_basis_of_regular_plane
    {U : Type} [AddCommGroup U] [Module K U] {R : QuadraticForm K U}
    (hdim : finrank K U = 2) (hR : (polarBilin R).Nondegenerate)
    (hK : 2 < Nat.card K) :
    ∃ b : Module.Basis (Fin 2) K U, R (b 0) ≠ 0 ∧ R (b 1) ≠ 0 := by
  classical
  have : FiniteDimensional K U := .of_finrank_pos (by rw [hdim]; norm_num)
  by_cases haniso : ∀ u : U, R u = 0 → u = 0
  · let b : Module.Basis (Fin 2) K U := Module.finBasisOfFinrankEq K U hdim
    exact ⟨b, fun h => b.ne_zero 0 (haniso _ h), fun h => b.ne_zero 1 (haniso _ h)⟩
  · push Not at haniso
    obtain ⟨e, he, he0⟩ := haniso
    obtain ⟨P, _⟩ := CFSG.ClassicalGroups.Orthogonal.exists_hypPair hR he he0
    exact exists_nonsingular_basis_of_hypPair hdim P hK

theorem apply_eq_of_perfect_commute_supportedDerived_regular_plane
    {W : Submodule K V} (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWdim : finrank K W = 2) (hK : 2 < Nat.card K)
    (P : Subgroup (V ≃ₗ[K] V)) [Group.IsPerfect P]
    (hcomm : ∀ g : P, ∀ r ∈ supportedDerived Q W, Commute (g : V ≃ₗ[K] V) r) :
    ∀ g : P, ∀ w : W, (g : V ≃ₗ[K] V) (w : V) = w := by
  obtain ⟨b, hQ0, hQ1⟩ := exists_nonsingular_basis_of_regular_plane hWdim hW hK
  exact apply_eq_of_perfect_commute_supportedDerived_nonsingular_basis hW hWdim b hQ0 hQ1
    P hcomm

theorem supportedDerived_commute_of_perfect_centralizer_anchor
    {W A B : Submodule K V}
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWdim : finrank K W = 2) (hK : 2 < Nat.card K)
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hB : (polarBilin (Q.comp B.subtype)).Nondegenerate)
    (hWA : ∀ w ∈ W, ∀ a ∈ A, polar Q w a = 0)
    (hWB : ∀ w ∈ W, ∀ b ∈ B, polar Q w b = 0)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0)
    (P : Subgroup (V ≃ₗ[K] V)) [Group.IsPerfect P]
    (hP : P ≤ supportedDerived Q (W ⊔ A))
    (hcomm : ∀ g : P, ∀ r ∈ supportedDerived Q W, Commute (g : V ≃ₗ[K] V) r)
    {g h : V ≃ₗ[K] V} (hg : g ∈ P) (hh : h ∈ supportedDerived Q (W ⊔ B)) :
    Commute g h := by
  have hWon : PolarNondegOn Q W := polarNondegOn_of_nondegenerate hW
  have hWAon : PolarNondegOn Q (W ⊔ A) :=
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hWon
      (polarNondegOn_of_nondegenerate hA) hWA
  have hWBon : PolarNondegOn Q (W ⊔ B) :=
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hWon
      (polarNondegOn_of_nondegenerate hB) hWB
  have hWBreg : (polarBilin (Q.comp (W ⊔ B).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn hWBon
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    supportedDerived_le_orthogonalGroup hWAon (hP hg)
  have hgW : ∀ w ∈ W, g w = w := by
    intro w hw
    exact apply_eq_of_perfect_commute_supportedDerived_regular_plane hW hWdim hK
      P hcomm ⟨g, hg⟩ ⟨w, hw⟩
  have hBperp : B ≤ suppPerp Q (W ⊔ A) := by
    intro b hb
    rw [mem_suppPerp]
    intro x hx
    obtain ⟨w, hw, a, ha, rfl⟩ := Submodule.mem_sup.mp hx
    rw [polar_add_left, hWB w hw b hb, hAB a ha b hb, add_zero]
  have hgB : ∀ b ∈ B, g b = b := fun b hb =>
    supportedDerived_apply_perp (hP hg) (hBperp hb)
  have hgWB : ∀ x ∈ W ⊔ B, g x = x := by
    intro x hx
    obtain ⟨w, hw, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hgW w hw, hgB b hb]
  exact CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.commute_of_apply_eq hWBreg hgO hgWB
    (fun x hx => supportedDerived_apply_mem hh hx)
    (fun x hx => supportedDerived_apply_perp hh hx)

theorem represented_map_commute_of_perfect_centralizer_anchor
    {K V M G : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Group M] [Group G]
    {Q : QuadraticForm K V}
    (ρ : M →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ)
    (κ : M →* G) (hκ : Function.Injective κ)
    {W A B : Submodule K V}
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWdim : finrank K W = 2) (hK : 2 < Nat.card K)
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hB : (polarBilin (Q.comp B.subtype)).Nondegenerate)
    (hWA : ∀ w ∈ W, ∀ a ∈ A, polar Q w a = 0)
    (hWB : ∀ w ∈ W, ∀ b ∈ B, polar Q w b = 0)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0)
    (CW CA CB : Subgroup M)
    (hCW : CW.map ρ = supportedDerived Q W)
    (hCA : CA.map ρ = supportedDerived Q (W ⊔ A))
    (hCB : CB.map ρ = supportedDerived Q (W ⊔ B))
    (P : Subgroup G) [Group.IsPerfect P]
    (hP : P ≤ CA.map κ)
    (hcomm : ∀ g ∈ P, ∀ r ∈ CW.map κ, Commute g r) :
    ∀ g ∈ P, ∀ h ∈ CB.map κ, Commute g h := by
  have hPκ : P ≤ κ.range := hP.trans (Subgroup.map_le_range _ _)
  let PN := P.comap κ
  have : Group.IsPerfect PN := by
    let e : PN ≃* P := (Subgroup.equivMapOfInjective PN κ hκ).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hPκ))
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let PL := PN.map ρ
  have : Group.IsPerfect PL := Group.IsPerfect.map _
  have hPL : PL ≤ supportedDerived Q (W ⊔ A) := by
    rintro _ ⟨g, hg, rfl⟩
    have hgA : g ∈ CA := (Subgroup.mem_map_iff_mem hκ).mp (hP hg)
    rw [← hCA]
    exact Subgroup.mem_map.mpr ⟨g, hgA, rfl⟩
  have hcPL : ∀ g : PL, ∀ r ∈ supportedDerived Q W,
      Commute (g : V ≃ₗ[K] V) r := by
    intro g r hr
    obtain ⟨s, hs, hsg⟩ := g.2
    rw [← hCW] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    have hc := hcomm (κ s) hs (κ t) (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
    have heq : s * t = t * s := hκ (by simpa only [map_mul] using hc.eq)
    have hm : Commute (ρ s) (ρ t) := (show Commute s t from heq).map ρ
    exact hsg ▸ hm
  intro g hg h hh
  obtain ⟨s, rfl⟩ := hPκ hg
  obtain ⟨t, ht, rfl⟩ := hh
  have hs : ρ s ∈ PL := Subgroup.mem_map.mpr ⟨s, hg, rfl⟩
  have htB : ρ t ∈ supportedDerived Q (W ⊔ B) := by
    rw [← hCB]
    exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
  have hn := supportedDerived_commute_of_perfect_centralizer_anchor
    hW hWdim hK hA hB hWA hWB hAB PL hPL hcPL hs htB
  have heq : s * t = t * s := hρ (by simpa only [map_mul] using hn.eq)
  exact (show Commute s t from heq).map κ

end CFSG.RankThree.PartOne.KCOrthogonal

end
