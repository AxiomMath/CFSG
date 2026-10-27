module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SigmaDich
public import CFSG.RankThree.PartOne.K1214.SylowShape
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcAssembly
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossDefs
public import CFSG.LocalAnalysis.UniquenessCase.UCKQSTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open
open scoped commutatorElement

namespace PCentralAbelianAt

theorem of_rankLE1 {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : CFSG.LieType.SeitzGeneration.RankLE1 p K) : PCentralAbelianAt K p :=
  of_pRank_le_one hp2 (CFSG.SectionRank.pRank_le (Fact.out : p.Prime).one_lt fun E _ hE => by
    simpa using h E hE)

theorem of_sylowShape {K : Type} [Group K] [Finite K] {p r e : ℕ} [Fact p.Prime]
    (h : CFSG.RankThree.PartOne.K1214.SylowShape p r e K) : PCentralAbelianAt K p := by
  refine of_sylow_comm fun S => ?_
  obtain ⟨φ⟩ := h S S.isPGroup' S.not_dvd_index
  rw [isMulCommutative_iff]
  intro a b
  apply φ.injective
  rw [map_mul, map_mul, mul_comm]

theorem of_sylowTorus {K : Type} [Group K] [Finite K] {p m : ℕ} [Fact p.Prime]
    (h : CFSG.LieType.SeitzGeneration.SylowTorus K p m) : PCentralAbelianAt K p := by
  refine of_sylow_comm fun S => ?_
  rw [isMulCommutative_iff]
  intro a b
  exact Subtype.ext (CFSG.HardMathSupport.Timmesfeld.CrossChar.mul_comm_of_sylowTorus h S.isPGroup' a.2 b.2)

theorem of_sylow_le_comm {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] (P : Sylow p K)
    {A : Subgroup K} (hA : IsMulCommutative A) (hPA : (P : Subgroup K) ≤ A) : PCentralAbelianAt K p := by
  refine of_sylow P fun _ _ => ?_
  rw [isMulCommutative_iff] at hA ⊢
  intro a b
  have h := congrArg (fun x : A => (x : K)) (hA ⟨a, hPA a.2⟩ ⟨b, hPA b.2⟩)
  exact Subtype.ext (by simpa using h)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw in
theorem of_sylowFrameM
    {τ : Tag} {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] {w : WeylGroup τ}
    [Finite (adjointGroup τ F)] (h : SylowFrameM τ F p w) : PCentralAbelianAt (adjointGroup τ F) p := by
  obtain ⟨L, _, _, Fr, D, -, -, -, -, ⟨e⟩, S₀, hS₀⟩ := h
  haveI : Finite D.Γ := Finite.of_equiv _ e.toEquiv
  have hT := CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.isMulCommutative_torus D
  have hT' : IsMulCommutative (D.torus.subgroupOf D.Γ) := by
    rw [isMulCommutative_iff] at hT ⊢
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (fun x : ↥D.torus => x.1) (hT ⟨(a : D.Γ), Subgroup.mem_subgroupOf.mp a.2⟩
      ⟨(b : D.Γ), Subgroup.mem_subgroupOf.mp b.2⟩)
    simpa using h
  exact of_mulEquiv e (of_sylow_le_comm S₀ hT' hS₀)

open CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis in
theorem of_sylow_sigmaModel {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {G : Type} [Group G] [Finite G] {e a N : ℕ}
    (ha : 1 ≤ a) (h : ∀ P : Sylow p G, Nonempty (P ≃* sigmaModel p e a N)) : PCentralAbelianAt G p := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hm : N / e < p
  · exact of_sylow_comm (sylow_isMulCommutative_of_sigmaModel_of_lt hp hm h)
  · push Not at hm
    have hL : 1 < (Nat.digits p (N / e)).length := by
      rw [Nat.lt_digits_length_iff hp.one_lt]
      simpa using hm
    have hne : N / e ≠ 0 := by omega
    let i₁ : Fin (Nat.digits p (N / e)).length := ⟨(Nat.digits p (N / e)).length - 1, by omega⟩
    have hi₁ : 1 ≤ (i₁ : ℕ) := by
      show 1 ≤ (Nat.digits p (N / e)).length - 1
      omega
    have hpos : 0 < (Nat.digits p (N / e))[i₁] := by
      have hlast := Nat.getLast_digit_ne_zero p hne
      have heq : (Nat.digits p (N / e))[i₁] =
          (Nat.digits p (N / e)).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hne) := by
        rw [List.getLast_eq_getElem]
        rfl
      rw [heq]
      exact Nat.pos_of_ne_zero hlast
    let j₁ : Fin (Nat.digits p (N / e))[i₁] := ⟨0, hpos⟩
    obtain ⟨E, hE, hEcard⟩ := SigmaDich.exists_elemAbelian_wreathTower hp ha i₁ hi₁
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p G))
    obtain ⟨φ⟩ := h S
    let Ψ : wreathTower p (Multiplicative (ZMod (p ^ a))) i₁ →* G :=
      (S : Subgroup G).subtype.comp (φ.symm.toMonoidHom.comp (SigmaDich.sigmaEmbed p e a N i₁ j₁))
    have hΨ : Function.Injective Ψ :=
      Subtype.coe_injective.comp (φ.symm.injective.comp (SigmaDich.sigmaEmbed_injective p e a N i₁ j₁))
    exact of_elemAbelian hp ((isElemAbelian_map_iff_of_injective Ψ hΨ E).2 hE)
      (k := p) (by rw [Subgroup.card_map_of_injective hΨ]; exact hEcard) (by omega)

end PCentralAbelianAt

section Five

open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

noncomputable def qsTorus5 {L : Type} [Field L] (ζ : Lˣ) : Subgroup (GL (Fin 5) L) :=
  Subgroup.map (diagGL 5) (Subgroup.pi Set.univ fun _ => Subgroup.zpowers ζ)

theorem qsDiagGL_mem_torus5 {L : Type} [Field L] {ζ : Lˣ} {u : Fin 5 → Lˣ}
    (hu : ∀ i, u i ∈ Subgroup.zpowers ζ) : (diagGL 5 u : GL (Fin 5) L) ∈ qsTorus5 ζ :=
  Subgroup.mem_map.2 ⟨u, (Subgroup.mem_pi _).2 (fun i _ => hu i), rfl⟩

theorem qsPow_five_of_mem_torus5 {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 5) {g : GL (Fin 5) L}
    (hg : g ∈ qsTorus5 ζ) : g ^ 5 = 1 := by
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hg
  rw [← map_pow]
  have : u ^ 5 = 1 := by
    funext i
    have hx := (Subgroup.mem_pi _).1 hu i (Set.mem_univ i)
    have hcard : Nat.card (Subgroup.zpowers ζ) = 5 := by rw [Nat.card_zpowers, hζ]
    have h := pow_card_eq_one' (G := Subgroup.zpowers ζ) (x := ⟨u i, hx⟩)
    rw [hcard] at h
    simpa using congrArg Subtype.val h
  rw [this, map_one]

theorem qsPermGL_mem_normalizer_torus5 {L : Type} [Field L] {ζ : Lˣ} (σ : Equiv.Perm (Fin 5)) :
    (permGL 5 σ : GL (Fin 5) L) ∈ Subgroup.normalizer (qsTorus5 ζ : Set (GL (Fin 5) L)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hh
    rw [permGL_mul_diagGL_mul_inv]
    exact qsDiagGL_mem_torus5 (fun i => (Subgroup.mem_pi _).1 hu (σ⁻¹ i) (Set.mem_univ _))
  · intro hh
    obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.1 hh
    have : h = permGL 5 σ⁻¹ * diagGL 5 u * (permGL 5 σ⁻¹)⁻¹ := by
      rw [hu', map_inv, inv_inv]
      group
    rw [this, permGL_mul_diagGL_mul_inv]
    exact qsDiagGL_mem_torus5 (fun i => (Subgroup.mem_pi _).1 hu _ (Set.mem_univ _))

theorem qsIsPGroup_torus5_sup {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 5) :
    IsPGroup 5 ↥(qsTorus5 ζ ⊔ Subgroup.zpowers (permGL 5 (finRotate 5) : GL (Fin 5) L)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hT : IsPGroup 5 ↥(qsTorus5 ζ : Subgroup (GL (Fin 5) L)) := by
    intro x
    exact ⟨1, by apply Subtype.ext; simpa using qsPow_five_of_mem_torus5 hζ x.2⟩
  have hC : IsPGroup 5 ↥(Subgroup.zpowers (permGL 5 (finRotate 5) : GL (Fin 5) L)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (finRotate 5) ^ 5 = 1 := by decide
    rw [this, map_one]
  exact IsPGroup.to_sup_of_normal_left' hT hC (Subgroup.zpowers_le.2 (qsPermGL_mem_normalizer_torus5 _))

theorem qsCross_pca_projFive {L : Type} [Field L] [Finite L] {ζ : Lˣ} (hζ : orderOf ζ = 5)
    (H : Subgroup (GL (Fin 5) L)) (hd : diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1] ∈ H)
    (hc : permGL 5 (finRotate 5) ∈ H) : PCentralAbelianAt (StatedProj H) 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hv : ∀ i, (![ζ, ζ⁻¹, 1, 1, 1] : Fin 5 → Lˣ) i ∈ Subgroup.zpowers ζ := by
    intro i
    fin_cases i
    · exact Subgroup.mem_zpowers ζ
    · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers ζ)
    · exact Subgroup.one_mem _
    · exact Subgroup.one_mem _
    · exact Subgroup.one_mem _
  let π : H →* StatedProj H := QuotientGroup.mk' _
  let c' : H := ⟨permGL 5 (finRotate 5), hc⟩
  let d' : H := ⟨diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1], hd⟩
  let U : Subgroup (StatedProj H) := Subgroup.closure {π c', π d'}
  have hcU : π c' ∈ U := Subgroup.subset_closure (by simp)
  have hdU : π d' ∈ U := Subgroup.subset_closure (by simp)
  have hU : IsPGroup 5 U := by
    have hP := (qsIsPGroup_torus5_sup (L := L) hζ).comap_subtype (K := H)
    have hP' := hP.map π
    have hle : U ≤ Subgroup.map π (Subgroup.comap H.subtype
        (qsTorus5 ζ ⊔ Subgroup.zpowers (permGL 5 (finRotate 5) : GL (Fin 5) L))) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨c', Subgroup.mem_comap.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)), rfl⟩
      · exact ⟨d', Subgroup.mem_comap.2 (Subgroup.mem_sup_left (qsDiagGL_mem_torus5 hv)), rfl⟩
    exact hP'.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hd5 : π d' ^ 5 = 1 := by
    rw [← map_pow]
    have : d' ^ 5 = 1 := Subtype.ext (by
      show (diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1] : GL (Fin 5) L) ^ 5 = 1
      exact qsPow_five_of_mem_torus5 hζ (qsDiagGL_mem_torus5 hv))
    rw [this, map_one]
  refine PCentralAbelianAt.of_noncomm hU hdU hcU hd5 ?_
  intro hcomm
  let v : Fin 5 → Lˣ := ![ζ, ζ⁻¹, 1, 1, 1]
  let a : Fin 5 → Lˣ := fun i => v ((finRotate 5)⁻¹ i) * (v i)⁻¹
  have ζne : ζ⁻¹ ≠ 1 := by
    intro h
    have h1 : ζ = 1 := inv_eq_one.1 h
    rw [h1, orderOf_one] at hζ
    omega
  have r0 : (finRotate 5)⁻¹ 0 = 4 := by decide
  have r3 : (finRotate 5)⁻¹ 3 = 2 := by decide
  have ha0 : a 0 = ζ⁻¹ := by simp [a, v, r0]
  have ha3 : a 3 = 1 := by simp [a, v, r3]
  have hax : ((⁅c', d'⁆ : H) : GL (Fin 5) L) = diagGL 5 a := by
    show ⁅(permGL 5 (finRotate 5) : GL (Fin 5) L), (diagGL 5 v : GL (Fin 5) L)⁆ = diagGL 5 a
    rw [commutatorElement_def, permGL_mul_diagGL_mul_inv, ← map_inv, ← map_mul]
    rfl
  have h1 : π ⁅c', d'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  have h2 : ((⁅c', d'⁆ : H) : GL (Fin 5) L) ∈ StatedScalars (Fin 5) L :=
    Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
  rw [hax] at h2
  obtain ⟨s, hs⟩ := h2
  have e0 := congrArg (fun g : GL (Fin 5) L => (g : Matrix (Fin 5) (Fin 5) L) 0 0) hs
  have e3 := congrArg (fun g : GL (Fin 5) L => (g : Matrix (Fin 5) (Fin 5) L) 3 3) hs
  simp [coe_diagGL, Matrix.GeneralLinearGroup.coe_scalar, ha0, ha3] at e0 e3
  have h3 : (ζ : L)⁻¹ = 1 := by rw [← e0, e3, Units.val_one]
  exact ζne (Units.ext (by rw [Units.val_inv_eq_inv_val, h3, Units.val_one]))

end Five

end CFSG.LocalAnalysis.UniquenessCase.UCK
