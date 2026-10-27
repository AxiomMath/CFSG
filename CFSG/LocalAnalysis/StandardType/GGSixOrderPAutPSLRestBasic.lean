module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSL
public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueToralA

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace OrdPRest

section Matrices

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]
  {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem conj_pow {y : G} {A : GL (Fin (m + 1)) F}
    (hA : ∀ u, y⁻¹ * ψ u * y = ψ (InnerDiagA.conjSL A u)) (k : ℕ)
    (u : SpecialLinearGroup (Fin (m + 1)) F) :
    (y ^ k)⁻¹ * ψ u * y ^ k = ψ (InnerDiagA.conjSL (A ^ k) u) := by
  induction k generalizing u with
  | zero => rw [pow_zero, pow_zero, inv_one, one_mul, mul_one, RootPlaneA.conjSL_one]
  | succ k ih =>
    rw [pow_succ y, pow_succ' A, RootPlaneA.conjSL_mul, ← hA, ← ih]
    group

theorem exists_scalar_pow [CharP F 2] {p : ℕ} {y : G} {A : GL (Fin (m + 1)) F}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (hA : ∀ u, y⁻¹ * ψ u * y = ψ (InnerDiagA.conjSL A u)) (hyp : y ^ p = 1) :
    ∃ c : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin (m + 1)) c := by
  have h1 : conjAut (m + 1) F (A ^ p) = conjAut (m + 1) F 1 :=
    RootPlaneA.conjAut_eq_of_psi_eq hker fun u => by
      rw [← conj_pow hA p u, hyp, RootPlaneA.conjSL_one]
      group
  rw [map_one] at h1
  have h2 := AutPSL.mem_center_of_conjAut_eq_one (by omega) h1
  rw [GeneralLinearGroup.center_eq_range_scalar] at h2
  obtain ⟨c, hc⟩ := h2
  exact ⟨c, hc.symm⟩

theorem conjSL_scalar_mul (c : Fˣ) (A : GL (Fin (m + 1)) F)
    (u : SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL (GeneralLinearGroup.scalar (Fin (m + 1)) c * A) u =
      InnerDiagA.conjSL A u := by
  apply SpecialLinearGroup.toGL_injective
  rw [RootPlaneA.toGL_conjSL, RootPlaneA.toGL_conjSL]
  calc GeneralLinearGroup.scalar (Fin (m + 1)) c * A * SpecialLinearGroup.toGL u *
        (GeneralLinearGroup.scalar (Fin (m + 1)) c * A)⁻¹ =
      GeneralLinearGroup.scalar (Fin (m + 1)) c * (A * SpecialLinearGroup.toGL u * A⁻¹) *
        (GeneralLinearGroup.scalar (Fin (m + 1)) c)⁻¹ := by group
    _ = A * SpecialLinearGroup.toGL u * A⁻¹ := by
      rw [(TypeA.PGLTor.commute_scalar c _).eq, mul_inv_cancel_right]

theorem exists_pow_eq_one [CharP F 2] {p : ℕ} {y : G} {A : GL (Fin (m + 1)) F}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (hA : ∀ u, y⁻¹ * ψ u * y = ψ (InnerDiagA.conjSL A u)) (hyp : y ^ p = 1)
    (hroot : ∀ c : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin (m + 1)) c → ∃ μ : Fˣ, μ ^ p = c) :
    ∃ A' : GL (Fin (m + 1)) F, A' ^ p = 1 ∧ ∀ u, y⁻¹ * ψ u * y = ψ (InnerDiagA.conjSL A' u) := by
  obtain ⟨c, hc⟩ := exists_scalar_pow hker hA hyp
  obtain ⟨μ, hμ⟩ := hroot c hc
  refine ⟨GeneralLinearGroup.scalar (Fin (m + 1)) μ⁻¹ * A,
    TypeA.PGLTor.pow_eq_one_of_pow_eq_scalar_pow (by rw [hc, hμ]), fun u => ?_⟩
  rw [conjSL_scalar_mul, hA]

theorem commute_of_conj (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {z b : G}
    {X Y : GL (Fin (m + 1)) F} (hz : ∀ u, z⁻¹ * ψ u * z = ψ (InnerDiagA.conjSL X u))
    (hb : ∀ u, b⁻¹ * ψ u * b = ψ (InnerDiagA.conjSL Y u)) (hXY : X * Y = Y * X) :
    z * b = b * z := by
  have key : ∀ u, (z * b)⁻¹ * ψ u * (z * b) = (b * z)⁻¹ * ψ u * (b * z) := by
    intro u
    have e1 : (z * b)⁻¹ * ψ u * (z * b) = b⁻¹ * (z⁻¹ * ψ u * z) * b := by group
    have e2 : (b * z)⁻¹ * ψ u * (b * z) = z⁻¹ * (b⁻¹ * ψ u * b) * z := by group
    rw [e1, e2, hz, hb, hb, hz, ← RootPlaneA.conjSL_mul, ← RootPlaneA.conjSL_mul, hXY]
  have hmem : (b * z) * (z * b)⁻¹ ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    calc ψ u * ((b * z) * (z * b)⁻¹) =
        (b * z) * ((b * z)⁻¹ * ψ u * (b * z)) * (z * b)⁻¹ := by group
      _ = (b * z) * ((z * b)⁻¹ * ψ u * (z * b)) * (z * b)⁻¹ := by rw [key u]
      _ = (b * z) * (z * b)⁻¹ * ψ u := by group
  rw [hC, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem.symm

theorem conj_conj {y : G} {A : GL (Fin (m + 1)) F}
    (hA : ∀ u, y⁻¹ * ψ u * y = ψ (InnerDiagA.conjSL A u))
    (s u : SpecialLinearGroup (Fin (m + 1)) F) :
    ((ψ s)⁻¹ * y * ψ s)⁻¹ * ψ u * ((ψ s)⁻¹ * y * ψ s) =
      ψ (InnerDiagA.conjSL
        ((SpecialLinearGroup.toGL s)⁻¹ * A * SpecialLinearGroup.toGL s) u) := by
  have e : ((ψ s)⁻¹ * y * ψ s)⁻¹ * ψ u * ((ψ s)⁻¹ * y * ψ s) =
      (ψ s)⁻¹ * (y⁻¹ * ψ (s * u * s⁻¹) * y) * ψ s := by
    rw [map_mul, map_mul, map_inv]
    group
  rw [e, hA, ← map_inv ψ s, ← map_mul, ← map_mul]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_inv, RootPlaneA.toGL_conjSL, RootPlaneA.toGL_conjSL, map_mul,
    map_mul, map_inv]
  group

end Matrices

section Frame

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]
  {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem exists_sl_conj_diag {A' Q : GL (Fin (m + 1)) F} (A₀ : GL (Fin (m + 1)) F)
    (hQ : ((Q * A' * Q⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag) :
    ∃ s : SpecialLinearGroup (Fin (m + 1)) F,
      ((A₀ * ((SpecialLinearGroup.toGL s)⁻¹ * A' * SpecialLinearGroup.toGL s) * A₀⁻¹ :
        GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := by
  set δ : Fˣ := GeneralLinearGroup.det Q * (GeneralLinearGroup.det A₀)⁻¹ with hδ
  set D₁ : GL (Fin (m + 1)) F := InnerDiagA.diagGL (Pi.mulSingle 0 δ) with hD₁
  have hdetD : GeneralLinearGroup.det D₁ = δ := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, hD₁, InnerDiagA.coe_diagGL, det_diagonal,
      ← Units.coe_prod, Finset.prod_pi_mulSingle', ite_eq_left (Finset.mem_univ _)]
  have hdet : GeneralLinearGroup.det (Q⁻¹ * D₁ * A₀) = 1 := by
    rw [map_mul, map_mul, map_inv, hdetD, hδ]
    group
  obtain ⟨s, hs⟩ : Q⁻¹ * D₁ * A₀ ∈ (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  refine ⟨s, ?_⟩
  have hD₁diag : (D₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := by
    rw [hD₁, InnerDiagA.coe_diagGL]
    exact isDiag_diagonal _
  have hcomm := (RootPlaneA.commute_of_isDiag hD₁diag hQ).eq
  have e : A₀ * ((SpecialLinearGroup.toGL s)⁻¹ * A' * SpecialLinearGroup.toGL s) * A₀⁻¹ =
      Q * A' * Q⁻¹ := by
    rw [hs]
    calc A₀ * ((Q⁻¹ * D₁ * A₀)⁻¹ * A' * (Q⁻¹ * D₁ * A₀)) * A₀⁻¹ =
        D₁⁻¹ * (Q * A' * Q⁻¹ * D₁) := by group
      _ = D₁⁻¹ * (D₁ * (Q * A' * Q⁻¹)) := by rw [← hcomm]
      _ = Q * A' * Q⁻¹ := by group
  rw [e]
  exact hQ

theorem exists_conj_mem_centralizer (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    {Bs : Subgroup G} (hT : RootPlaneA.GGBstarToralA m F ψ Bs)
    (hBs : ∀ b ∈ Bs, ∃ A : GL (Fin (m + 1)) F, ∀ u, b⁻¹ * ψ u * b = ψ (InnerDiagA.conjSL A u))
    {y : G} {A' Q : GL (Fin (m + 1)) F}
    (hA' : ∀ u, y⁻¹ * ψ u * y = ψ (InnerDiagA.conjSL A' u))
    (hQ : ((Q * A' * Q⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag) :
    ∃ s : SpecialLinearGroup (Fin (m + 1)) F,
      (ψ s)⁻¹ * y * ψ s ∈ Subgroup.centralizer (Bs : Set G) := by
  obtain ⟨A₀, hA₀⟩ := hT
  obtain ⟨s, hs⟩ := exists_sl_conj_diag A₀ hQ
  refine ⟨s, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨Ab, hAb⟩ := hBs b hb
  set X := (SpecialLinearGroup.toGL s)⁻¹ * A' * SpecialLinearGroup.toGL s with hX
  have h1 := (RootPlaneA.commute_of_isDiag hs (hA₀ b hb Ab hAb)).eq
  have hXY : X * Ab = Ab * X := by
    have h2 : A₀ * (X * Ab) * A₀⁻¹ = A₀ * (Ab * X) * A₀⁻¹ := by
      calc A₀ * (X * Ab) * A₀⁻¹ = (A₀ * X * A₀⁻¹) * (A₀ * Ab * A₀⁻¹) := by group
        _ = (A₀ * Ab * A₀⁻¹) * (A₀ * X * A₀⁻¹) := h1
        _ = A₀ * (Ab * X) * A₀⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  exact (commute_of_conj hC (conj_conj hA' s) hAb hXY).symm

end Frame

section Setting

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {m f : ℕ} {F : Type}
  [Field F] [Finite F] {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem card_bstar_ge
    (hS : GGSixFusionSetting p Bs G₀ (SpecialLinear.rootDatum m F) .PSL (m + 1) f ψ)
    (hpF : p ∣ Nat.card F - 1) (hm : 1 ≤ m) : p ^ (m + 1 - 2) ≤ Nat.card Bs := by
  have hp := hS.prime
  obtain ⟨-, ⟨-, hker⟩, -, -⟩ := hS.presents
  have hd : 2 ≤ m + 1 := by omega
  set E₀ : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
    (TypeA.evalOne (p := p) (K := F) hd).ker.map (TypeA.diagSL p (m + 1) F) with hE₀
  have hE₀el : IsElemAbelian p E₀ := TypeA.isElemAbelian_map_diagSL _
  have hE₀card : Nat.card E₀ = p ^ (m + 1 - 2) := by
    rw [hE₀, Subgroup.card_map_of_injective TypeA.diagSL_injective,
      TypeA.card_ker_evalOne hp hpF hd]
  have hscal : ∀ g ∈ E₀, g ∈ scalars (m + 1) F → g = 1 := by
    rintro _ ⟨u, hu, rfl⟩ hgs
    obtain ⟨c, -, hc⟩ := mem_scalars.mp hgs
    have hu1 : (u : Fin (m + 1) → rootsOfUnity p F) ⟨1, by omega⟩ = 1 := hu
    have h1 := congrArg
      (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) F => M ⟨1, by omega⟩ ⟨1, by omega⟩) hc
    simp only [TypeA.coe_diagSL, diagonal_apply_eq, scalar_apply, TypeA.rootEnt, hu1] at h1
    have hc1 : (c : F) = 1 := by rw [← h1]; rfl
    ext i j
    rw [hc, hc1, map_one]
    rfl
  have hinj : Function.Injective (ψ.comp E₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hscal g g.2 (by rw [scalars_eq_center]; exact hker hg))
  have hEcard : Nat.card (E₀.map ψ) = p ^ (m + 1 - 2) := by
    have hrange : (ψ.comp E₀.subtype).range = E₀.map ψ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← hE₀card]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hEel : IsElemAbelian p (E₀.map ψ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, y, hy, rfl⟩ := b
      apply Subtype.ext
      change ψ x * ψ y = ψ y * ψ x
      rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE₀el hx hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE₀el.2 x hx, map_one]
  rw [← hEcard]
  exact hS.card_le_card_bstar hEel

theorem bstar_toral
    (hS : GGSixFusionSetting p Bs G₀ (SpecialLinear.rootDatum m F) .PSL (m + 1) f ψ)
    (h24 : GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G))) (hpF : p ∣ Nat.card F - 1) :
    RootPlaneA.GGBstarToralA m F ψ Bs := by
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hm : 2 ≤ m := hrank
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  refine RootPlaneA.ggBstarToralA_of_card hm hker hCψ hS.elem
    (fun b hb => RootPlaneA.exists_gl_of_psiInnerDiag hm hker (hS.innerDiag b hb)) hS.prime
    hS.ne_two hpF (card_bstar_ge hS hpF (by omega)) ?_
  exact (Nat.pow_le_pow_right hS.prime.pos (by norm_num : 3 ≤ 4)).trans (hS.pow_four_le h24)

end Setting

end OrdPRest

end CFSG.StandardType
