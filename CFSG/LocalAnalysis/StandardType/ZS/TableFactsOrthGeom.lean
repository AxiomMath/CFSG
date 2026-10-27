module

public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction
public import CFSG.ClassicalGroups.Orthogonal.NormClass.Generation
import CFSG.ClassicalGroups.Orthogonal.RootGroupCard
import CFSG.LocalAnalysis.StandardType.ZS.TableOrth
import CFSG.LocalAnalysis.StandardType.ZS.ClassReflOrder
import CFSG.ClassicalGroups.Orthogonal.Represents
import CFSG.LocalAnalysis.StandardType.ZS.OrthReflect
import CFSG.Quasithin.Vol2.Ch11SecBL2OPSL
import CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

private theorem tfog_orderOf_reflect_pair (hp3 : 3 ≤ p) {Q : QuadraticForm (ZMod p) V}
    {a u : V} (ha : Q a ≠ 0) (ha' : Q (a + u) ≠ 0) (hu : Q u = 0)
    (hua : QuadraticMap.polarBilin Q u a = 0) (hu0 : u ≠ 0) :
    orderOf (CFSG.ClassicalGroups.Orthogonal.reflect Q a *
      CFSG.ClassicalGroups.Orthogonal.reflect Q (a + u)) = p := by
  rw [← owCr_orthRefl_eq_reflect Q ha, ← owCr_orthRefl_eq_reflect Q ha']
  exact owCr_order_orthRefl (Fact.out : p.Prime) hp3 Q a u ha ha' hu hua hu0

private theorem tfog_exists_norm_orth (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (h4 : 4 ≤ Module.finrank (ZMod p) V) {Q : QuadraticForm (ZMod p) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0) :
    ∃ a u : V, Q a = c ∧ Q u = 0 ∧ u ≠ 0 ∧
      QuadraticMap.polarBilin Q u a = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨a, -, hQa⟩ := CFSG.ClassicalGroups.Orthogonal.PolarNondegOn.exists_map_eq
    (K := ZMod p) (V := V) h2 (CFSG.ClassicalGroups.Orthogonal.polarNondegOn_top hQ)
    (by rw [finrank_top]; omega) c
  have hQa_ne : Q a ≠ 0 := by rw [hQa]; exact hc
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨u, hu0, huQ, hua⟩ := owCr_exists_isotropic_orth hodd Q hQ h4 a hQa_ne
  exact ⟨a, u, hQa, huQ, hu0, hua⟩

private theorem tfog_ker_flip_finrank [Module.Finite (ZMod p) V]
    {B : LinearMap.BilinForm (ZMod p) V} (hB : B.Nondegenerate)
    (hsymm : ∀ x y, B x y = B y x) {u : V} (hu0 : u ≠ 0) :
    Module.finrank (ZMod p) (LinearMap.ker (B.flip u)) =
      Module.finrank (ZMod p) V - 1 := by
  have hf : B.flip u ≠ 0 := by
    intro h
    apply hu0
    apply hB.1
    intro y
    have hy : B.flip u y = 0 := by rw [h]; rfl
    rw [LinearMap.BilinForm.flip_apply] at hy
    rw [hsymm u y, hy]
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero (K := ZMod p) (V₁ := V)
    (f := B.flip u) hf
  omega

private theorem tfog_exists_aniso_orth [Module.Finite (ZMod p) V]
    (h3 : 3 ≤ Module.finrank (ZMod p) V) {Q : QuadraticForm (ZMod p) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {u : V} (hu0 : u ≠ 0) :
    ∃ a : V, Q a ≠ 0 ∧ QuadraticMap.polar Q u a = 0 := by
  let B : LinearMap.BilinForm (ZMod p) V := QuadraticMap.polarBilin Q
  let S : Submodule (ZMod p) V := LinearMap.ker (B.flip u)
  have hsymm : ∀ x y, B x y = B y x := by
    intro x y
    show QuadraticMap.polarBilin Q x y = QuadraticMap.polarBilin Q y x
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
      ← QuadraticMap.polarBilin_apply_apply]
  have hSdim : Module.finrank (ZMod p) S = Module.finrank (ZMod p) V - 1 := by
    simpa [B, S] using tfog_ker_flip_finrank hQ hsymm hu0
  have hex : ∃ a ∈ S, Q a ≠ 0 := by
    by_contra h
    push Not at h
    have hSle : S ≤ LinearMap.BilinForm.orthogonal B S := by
      intro s hs
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro t ht
      rw [← hsymm s t]
      change QuadraticMap.polarBilin Q s t = 0
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
      rw [h (s + t) (S.add_mem hs ht), h s hs, h t ht]
      ring
    have hfin : Module.finrank (ZMod p) S ≤
        Module.finrank (ZMod p) (LinearMap.BilinForm.orthogonal B S) :=
      Submodule.finrank_mono hSle
    have horth : Module.finrank (ZMod p) (LinearMap.BilinForm.orthogonal B S) =
        Module.finrank (ZMod p) V - Module.finrank (ZMod p) S := by
      change Module.finrank (ZMod p)
        (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) S) = _
      exact LinearMap.BilinForm.finrank_orthogonal hQ S
    rw [horth] at hfin
    omega
  obtain ⟨a, haS, haQ⟩ := hex
  have hau : B a u = 0 := by
    have h1 : B.flip u a = 0 := by simpa [S, LinearMap.mem_ker] using haS
    simpa [LinearMap.BilinForm.flip_apply] using h1
  exact ⟨a, haQ, by rw [QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]; exact hau⟩

theorem exists_isotropic_perp_aniso (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (h3 : 3 ≤ Module.finrank (ZMod p) V) {Q : QuadraticForm (ZMod p) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    ∃ u a : V, u ≠ 0 ∧ Q u = 0 ∧ Q a ≠ 0 ∧ QuadraticMap.polar Q u a = 0 := by
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨u, hu0, huQ⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_isotropic_of_finrank_ge_three
      hodd Q hQ h3
  obtain ⟨a, haQ, hua⟩ := tfog_exists_aniso_orth h3 hQ hu0
  exact ⟨u, a, hu0, huQ, haQ, hua⟩

theorem exists_pair_orderOf_eq_of_isOrthType (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (h4 : 4 ≤ Module.finrank (ZMod p) V) {J : Subgroup (V ≃ₗ[ZMod p] V)} (hJ : IsOrthType p J) :
    ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p := by
  obtain ⟨Q, hQ, hcase⟩ := hJ
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hpolOf : ∀ {a u : V}, QuadraticMap.polarBilin Q u a = 0 →
      QuadraticMap.polar Q a u = 0 := by
    intro a u hua
    rw [QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]
    exact hua
  rcases hcase with hO | ⟨c, hc, hJc⟩
  · obtain ⟨a, u, hQa, huQ, hu0, hua⟩ :=
      tfog_exists_norm_orth hp h4 hQ (c := 1) one_ne_zero
    have hQa_ne : Q a ≠ 0 := by rw [hQa]; exact one_ne_zero
    have hpol : QuadraticMap.polar Q a u = 0 := hpolOf hua
    have ha' : Q (a + u) ≠ 0 := by
      rw [QuadraticMap.map_add Q a u, hQa, huQ, hpol, add_zero, add_zero]
      exact one_ne_zero
    refine ⟨CFSG.ClassicalGroups.Orthogonal.reflect Q a, ?_,
      CFSG.ClassicalGroups.Orthogonal.reflect Q (a + u), ?_, ?_, ?_, ?_⟩
    · rw [hO]; exact isIsom_reflect Q a
    · rw [hO]; exact isIsom_reflect Q (a + u)
    · exact isRefl_reflect hp hQa_ne
    · exact isRefl_reflect hp ha'
    · exact tfog_orderOf_reflect_pair hp3 hQa_ne ha' huQ hua hu0
  · obtain ⟨a, u, hQa, huQ, hu0, hua⟩ := tfog_exists_norm_orth hp h4 hQ hc
    have hQa_ne : Q a ≠ 0 := by rw [hQa]; exact hc
    have hpol : QuadraticMap.polar Q a u = 0 := hpolOf hua
    have ha' : Q (a + u) ≠ 0 := by
      rw [QuadraticMap.map_add Q a u, hQa, huQ, hpol, add_zero, add_zero]
      exact hc
    have hQa' : Q (a + u) = c := by
      rw [QuadraticMap.map_add Q a u, hQa, huQ, hpol, add_zero, add_zero]
    refine ⟨CFSG.ClassicalGroups.Orthogonal.reflect Q a, ?_,
      CFSG.ClassicalGroups.Orthogonal.reflect Q (a + u), ?_, ?_, ?_, ?_⟩
    · rw [hJc]
      exact Subgroup.subset_closure ((mem_classRefl_iff hp hQ hc _).mpr ⟨a, hQa, rfl⟩)
    · rw [hJc]
      exact Subgroup.subset_closure ((mem_classRefl_iff hp hQ hc _).mpr ⟨a + u, hQa', rfl⟩)
    · exact isRefl_reflect hp hQa_ne
    · exact isRefl_reflect hp ha'
    · exact tfog_orderOf_reflect_pair hp3 hQa_ne ha' huQ hua hu0

theorem exists_orderOf_eq_of_isOrthType (hp5 : 5 ≤ p) [Module.Finite (ZMod p) V]
    (h3 : 3 ≤ Module.finrank (ZMod p) V) {J : Subgroup (V ≃ₗ[ZMod p] V)} (hJ : IsOrthType p J) :
    ∃ g ∈ J, orderOf g = p := by
  have hp : p ≠ 2 := by omega
  have hp3 : 3 ≤ p := by omega
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h3' : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 (by omega)
  obtain ⟨Q, hQ, hcase⟩ := hJ
  obtain ⟨u, a, hu0, huQ, haQ, hua⟩ := exists_isotropic_perp_aniso hp h3 hQ
  have hpol : QuadraticMap.polar Q a u = 0 := by
    rw [QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]
    exact hua
  have ha' : Q (a + u) ≠ 0 := by
    rw [QuadraticMap.map_add Q a u, huQ, hpol, add_zero, add_zero]
    exact haQ
  have hab : Q a = Q (a + u) := by
    rw [QuadraticMap.map_add Q a u, huQ, hpol, add_zero, add_zero]
  rcases hcase with hO | ⟨c, hc, hJc⟩
  · refine ⟨CFSG.ClassicalGroups.Orthogonal.reflect Q a *
      CFSG.ClassicalGroups.Orthogonal.reflect Q (a + u), ?_, ?_⟩
    · rw [hO]
      exact isIsom_mul (isIsom_reflect Q a) (isIsom_reflect Q (a + u))
    · exact tfog_orderOf_reflect_pair hp3 haQ ha' huQ hua hu0
  · have hmem : CFSG.ClassicalGroups.Orthogonal.reflect Q a *
        CFSG.ClassicalGroups.Orthogonal.reflect Q (a + u) ∈
        Subgroup.closure (CFSG.ClassicalGroups.Orthogonal.reflect Q '' {x | Q x = c}) :=
      CFSG.ClassicalGroups.Orthogonal.reflect_mul_reflect_mem_closure_reflect
        (K := ZMod p) (V := V) h2 h3' hQ hab hc
    have hsub : CFSG.ClassicalGroups.Orthogonal.reflect Q '' {x | Q x = c} ⊆
        ClassRefl p Q c := by
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_classRefl_iff hp hQ hc _).mpr ⟨x, hx, rfl⟩
    refine ⟨CFSG.ClassicalGroups.Orthogonal.reflect Q a *
      CFSG.ClassicalGroups.Orthogonal.reflect Q (a + u), ?_, ?_⟩
    · rw [hJc]
      exact Subgroup.closure_mono hsub hmem
    · exact tfog_orderOf_reflect_pair hp3 haQ ha' huQ hua hu0

theorem exists_forall_isIsom_of_isOrthType_three (hp3 : p = 3) [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hJ : IsOrthType p J)
    (hd : ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    ∃ Q : QuadraticForm (ZMod p) V, (QuadraticMap.polarBilin Q).Nondegenerate ∧
      ∀ g, g ∈ J ↔ IsIsom p Q g := by
  obtain ⟨Q, hQ, hcase⟩ := hJ
  rcases hcase with hO | ⟨c, hc, hJc⟩
  · exact ⟨Q, hQ, hO⟩
  · exfalso
    obtain ⟨x, hxJ, y, hyJ, hxr, hyr, hxy⟩ := hd
    rw [hJc] at hxJ hyJ
    have := orderOf_mul_le_three_of_classRefl_three hp3 hQ hc hxJ hyJ hxr hyr
    omega

theorem pow_dvd_card_of_forall_isIsom (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    {Q : QuadraticForm (ZMod p) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hJ : ∀ g, g ∈ J ↔ IsIsom p Q g) :
    p ^ (Module.finrank (ZMod p) V - 2) ∣ Nat.card J := by
  by_cases hle : Module.finrank (ZMod p) V ≤ 2
  · have h0 : Module.finrank (ZMod p) V - 2 = 0 := by omega
    rw [h0, pow_zero]
    exact one_dvd _
  · have h3 : 3 ≤ Module.finrank (ZMod p) V := by omega
    obtain ⟨u, a, hu0, huQ, haQ, hua⟩ := exists_isotropic_perp_aniso hp h3 hQ
    have hroot : CFSG.ClassicalGroups.Orthogonal.rootGroup Q u ≤ J := by
      intro g hg
      obtain ⟨w, hw, hgw⟩ := CFSG.ClassicalGroups.Orthogonal.mem_rootGroup.mp hg
      rw [hJ, ← hgw]
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (CFSG.ClassicalGroups.Orthogonal.eichler_mem_orthogonalGroup Q u w)
    have hcard : Nat.card (CFSG.ClassicalGroups.Orthogonal.rootGroup Q u) =
        p ^ (Module.finrank (ZMod p) V - 2) := by
      rw [CFSG.ClassicalGroups.Orthogonal.card_rootGroup (K := ZMod p) (V := V) hQ huQ hu0,
        Nat.card_zmod]
    have hdvd := Subgroup.card_dvd_of_le hroot
    rwa [hcard] at hdvd

theorem commutator_mem_closure_classRefl_of_three_ne (hp : p ≠ 2) (hp3 : p ≠ 3)
    [Module.Finite (ZMod p) V]
    {Q : QuadraticForm (ZMod p) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p}
    (hc : c ≠ 0) {g h : V ≃ₗ[ZMod p] V} (hg : IsIsom p Q g) (hh : IsIsom p Q h) :
    g * h * g⁻¹ * h⁻¹ ∈ Subgroup.closure (ClassRefl p Q c) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hg
  have hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hh
  have hmem := CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_le_closure_reflect
    (K := ZMod p) (V := V) h2 h3 hQ hc (Subgroup.commutator_mem_commutator hgO hhO)
  rw [commutatorElement_def] at hmem
  have hsub : CFSG.ClassicalGroups.Orthogonal.reflect Q '' {x | Q x = c} ⊆
      ClassRefl p Q c := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_classRefl_iff hp hQ hc _).mpr ⟨x, hx, rfl⟩
  exact Subgroup.closure_mono hsub hmem

private theorem tfog_commutator_le_of_commutator_mem {Q : QuadraticForm (ZMod p) V}
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ g h : V ≃ₗ[ZMod p] V, IsIsom p Q g → IsIsom p Q h → g * h * g⁻¹ * h⁻¹ ∈ A) :
    (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).map
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype ≤ A := by
  rw [Subgroup.map_le_iff_le_comap, commutator, Subgroup.commutator_le]
  intro g hg h hh
  rw [Subgroup.mem_comap]
  exact hA g h (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2)
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp h.2)

private theorem tfog_sixty_le_card_psl2 (hp5 : 5 ≤ p) :
    60 ≤ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
  have hp2 : p ≠ 2 := by omega
  have htwo : 2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) =
      p * (p ^ 2 - 1) := CFSG.Quasithin.Vol2.Ch11.SecB.two_mul_card_psl2 hp2
  have hsq : 25 ≤ p ^ 2 := by
    have := Nat.pow_le_pow_left hp5 2
    norm_num at this ⊢
    exact this
  have h24 : 24 ≤ p ^ 2 - 1 := by omega
  have hprod : 120 ≤ p * (p ^ 2 - 1) := by
    have := Nat.mul_le_mul hp5 h24
    norm_num at this ⊢
    exact this
  have : 120 ≤ 2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [htwo]
    exact hprod
  omega

theorem sixty_le_card_of_commutator_mem (hp5 : 5 ≤ p) [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) V = 3) {Q : QuadraticForm (ZMod p) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ g h : V ≃ₗ[ZMod p] V, IsIsom p Q g → IsIsom p Q h → g * h * g⁻¹ * h⁻¹ ∈ A) :
    60 ≤ Nat.card A := by
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  have hK3 : Nat.card (ZMod p) ≠ 3 := by rw [Nat.card_zmod]; omega
  obtain ⟨-, -, e, -, -, hcomm, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_three_derived hodd hK3 Q hQ hdim
  have hle := tfog_commutator_le_of_commutator_mem A hA
  let _ : Finite V := Finite.of_equiv (Fin 3 → ZMod p)
      (Module.finBasisOfFinrankEq (ZMod p) V hdim).equivFun.toEquiv.symm
  let _ : Finite ↥A := Finite.of_injective (fun x : ↥A => (x.1 : V → V))
      (fun x y h => Subtype.ext (LinearEquiv.ext fun v => congrFun h v))
  have hcard_le := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective] at hcard_le
  have hcard_eq : Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [hcomm, Subgroup.card_map_of_injective e.symm.injective]
    exact Nat.card_congr
      (CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3.traceZeroSpecialImageEquiv (ZMod p)).toEquiv
  have h60 := tfog_sixty_le_card_psl2 hp5
  rw [← hcard_eq] at h60
  exact le_trans h60 hcard_le

theorem sixty_le_card_of_isOrthType_three (hp5 : 5 ≤ p) [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) V = 3) {J : Subgroup (V ≃ₗ[ZMod p] V)}
    (hJ : IsOrthType p J) : 60 ≤ Nat.card J := by
  have hp : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨Q, hQ, hcase⟩ := hJ
  refine sixty_le_card_of_commutator_mem hp5 hdim hQ J ?_
  intro g h hg hh
  rcases hcase with hO | ⟨c, hc, hJc⟩
  · rw [hO]
    exact isIsom_mul (isIsom_mul (isIsom_mul hg hh) (isIsom_inv hg)) (isIsom_inv hh)
  · rw [hJc]
    exact commutator_mem_closure_classRefl_of_three_ne hp hp3 hQ hc hg hh

end CFSG.StandardType.ZS.TableFacts

end
