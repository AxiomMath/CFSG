module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueToralA
import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace StdPosA

private theorem toralA_of_card {m : ℕ} {F : Type} [Field F] [Finite F] {G : Type} [Group G]
    [Finite G] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G} {p : ℕ} {Bs : Subgroup G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hBs : IsElemAbelian p Bs)
    (hinn : ∀ b ∈ Bs, ∃ A : GL (Fin (m + 1)) F, ∀ u, b⁻¹ * ψ u * b = ψ (InnerDiagA.conjSL A u))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    (hc1 : p ^ (m - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤
      Nat.card ↥Bs)
    (hc3 : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs) :
    RootPlaneA.GGBstarToralA m F ψ Bs := by
  choose! Ab hAb using hinn
  have hrep : ∀ b ∈ Bs, ∀ A : GL (Fin (m + 1)) F,
      (∀ u, b⁻¹ * ψ u * b = ψ (InnerDiagA.conjSL A u)) →
        conjAut (m + 1) F A = conjAut (m + 1) F (Ab b) := fun b hb A hA =>
    RootPlaneA.conjAut_eq_of_psi_eq hker fun y => by rw [← hA y, ← hAb b hb y]
  have hprod : ∀ x ∈ Bs, ∀ y ∈ Bs,
      conjAut (m + 1) F (Ab (x * y)) = conjAut (m + 1) F (Ab y) * conjAut (m + 1) F (Ab x) := by
    intro x hx y hy
    rw [← map_mul]
    refine (hrep (x * y) (Bs.mul_mem hx hy) (Ab y * Ab x) fun u => ?_).symm
    rw [RootPlaneA.conjSL_mul, ← hAb y hy, ← hAb x hx]
    group
  let θ : ↥Bs →* MulAut (projectiveSL (m + 1) F) :=
    MonoidHom.mk' (fun b => conjAut (m + 1) F (Ab b)) fun x y => by
      change conjAut (m + 1) F (Ab ((x : G) * y)) =
        conjAut (m + 1) F (Ab x) * conjAut (m + 1) F (Ab y)
      rw [TableB.IsElemAbelian.comm hBs x.2 y.2, hprod y y.2 x x.2]
  have hθ : ∀ b : ↥Bs, θ b = conjAut (m + 1) F (Ab b) := fun _ => rfl
  have hkerC : ∀ b : ↥Bs, θ b = 1 → (b : G) ∈ Subgroup.centralizer (ψ.range : Set G) := by
    intro b hb1
    rw [hθ] at hb1
    obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one hb1
    obtain ⟨u, hu⟩ := LinTorus.exists_unit_of_coe_eq_scalar hc
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, rfl⟩
    have h1 := hAb b b.2 y
    rw [hu, LinTorus.conjSL_scalar] at h1
    calc ψ y * (b : G) = (b : G) * ((b : G)⁻¹ * ψ y * (b : G)) := by group
      _ = (b : G) * ψ y := by rw [h1]
  have hkerle : Nat.card θ.ker ≤
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨((x : ↥Bs) : G), (x : ↥Bs).2, hkerC x.1 (MonoidHom.mem_ker.mp x.2)⟩)
      fun x y hxy => ?_
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have hcard : Nat.card ↥Bs ≤
      Nat.card θ.range * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := by
    rw [← Subgroup.card_ker_mul_card_range θ, mul_comm]
    exact Nat.mul_le_mul_left _ hkerle
  have hpos : 0 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := Nat.card_pos
  have hc1' : p ^ (m + 1 - 2) ≤ Nat.card θ.range := by
    rw [show m + 1 - 2 = m - 1 by omega]
    exact Nat.le_of_mul_le_mul_right (hc1.trans hcard) hpos
  have hc3' : p ^ 3 ≤ Nat.card θ.range := Nat.le_of_mul_le_mul_right (hc3.trans hcard) hpos
  have hXel : IsElemAbelian p θ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, rfl⟩ := a
      obtain ⟨_, y, rfl⟩ := b
      apply Subtype.ext
      change θ x * θ y = θ y * θ x
      rw [← map_mul, ← map_mul, hBs.1.is_comm.comm x y]
    · rintro _ ⟨x, rfl⟩
      have hx : x ^ p = 1 := Subtype.ext (by simpa using hBs.2 x x.2)
      rw [← map_pow, hx, map_one]
  have hXI : (θ.range : Set (MulAut (projectiveSL (m + 1) F))) ⊆
      Set.range (conjAut (m + 1) F) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨Ab b, rfl⟩
  obtain ⟨A₀, hA₀⟩ := TypeA.ggPGLTorality_holds (K := F) (d := m + 1) hp hp2 hpF θ.range hXel
    hXI hc1' hc3'
  refine ⟨A₀, fun b hb A hA => ?_⟩
  have hmem : conjAut (m + 1) F A ∈ θ.range := by
    rw [hrep b hb A hA]
    exact ⟨⟨b, hb⟩, rfl⟩
  intro i j hij
  have h := hA₀ A hmem i j hij
  rwa [Units.val_mul, Units.val_mul]

theorem conjSL_isDiag_eq_torus {m : ℕ} {F : Type} [Field F] (hm : 2 ≤ m)
    {N : GL (Fin (m + 1)) F} (hN : (N : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag)
    {γ : Fin m → ℤ} (hγ : γ ∈ (SpecialLinear.rootDatum m F).roots) :
    ∃ h ∈ ggTorus (SpecialLinear.rootDatum m F),
      ∀ z ∈ (SpecialLinear.rootDatum m F).rootGroup γ, InnerDiagA.conjSL N z = h * z * h⁻¹ := by
  set e : Fin (m + 1) → F := Matrix.diag (N : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
  have hNe : (N : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal e :=
    hN.diagonal_diag.symm
  have he0 : ∀ l, e l ≠ 0 := by
    intro l
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero N
    rw [hNe, Matrix.det_diagonal] at hdet
    exact Finset.prod_ne_zero_iff.mp hdet l (Finset.mem_univ l)
  have hij : (SpecialLinear.idx m γ).1 ≠ (SpecialLinear.idx m γ).2 :=
    (SpecialLinear.idx_spec m hγ).1
  set i := (SpecialLinear.idx m γ).1
  set j := (SpecialLinear.idx m γ).2
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  set lam : F := e i * (e j)⁻¹
  have hlam : lam ≠ 0 := mul_ne_zero (he0 i) (inv_ne_zero (he0 j))
  set e' : Fin (m + 1) → F := fun l => (if l = i then lam else 1) * (if l = k then lam⁻¹ else 1)
  have he'0 : ∀ l, e' l ≠ 0 := fun l => by
    simp only [e']
    refine mul_ne_zero ?_ ?_ <;> split_ifs
    exacts [hlam, one_ne_zero, inv_ne_zero hlam, one_ne_zero]
  have hdet' : (Matrix.diagonal e').det = 1 := by
    rw [Matrix.det_diagonal]
    simp only [e', Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    exact mul_inv_cancel₀ hlam
  refine ⟨⟨Matrix.diagonal e', hdet'⟩, HypSixTypeA.mem_ggTorus_of_diagonal he'0 rfl,
    fun z hz => ?_⟩
  change z ∈ SpecialLinear.rootGroup m F γ at hz
  rw [SpecialLinear.rootGroup_eq_idx m F hγ] at hz
  obtain ⟨t, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij z).mp hz
  rw [← RootPlaneA.slConjugation_eq_conjSL,
    HypSixTypeA.slConjugation_diag_transvection he0 hNe hij t,
    HypSixTypeA.sl_diag_conj_transvection (h := ⟨Matrix.diagonal e', hdet'⟩) he'0 rfl hij t]
  have hei : e' i = lam := by simp [e', Ne.symm hki]
  have hej : e' j = 1 := by simp [e', Ne.symm hij, Ne.symm hkj]
  rw [hei, hej]
  simp only [lam]
  congr 1
  ring

theorem exists_stdPos_sl {m : ℕ} {F : Type} [Field F] [Finite F] {G : Type} [Group G]
    [Finite G] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G} {p : ℕ} {Bs : Subgroup G}
    (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hBs : IsElemAbelian p Bs)
    (hinn : ∀ b ∈ Bs, GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ b)
    (hc1 : p ^ (m - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤
      Nat.card ↥Bs)
    (hc3 : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs) :
    ∃ s : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
      GGKGPosStdPos (SpecialLinear.rootDatum m F) (ψ.comp (MulAut.conj s).toMonoidHom) Bs := by
  have hgl : ∀ b ∈ Bs, ∃ A : GL (Fin (m + 1)) F,
      ∀ u, b⁻¹ * ψ u * b = ψ (InnerDiagA.conjSL A u) :=
    fun b hb => RootPlaneA.exists_gl_of_psiInnerDiag hm hker (hinn b hb)
  obtain ⟨A₀, hA₀⟩ := toralA_of_card hker hBs hgl hp hp2 hpF hc1 hc3
  set a : F := (A₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det
  have ha0 : a ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A₀
  set e : Fin (m + 1) → F := fun l => if l = 0 then a else 1
  have hdetE : (Matrix.diagonal e).det = a := by
    rw [Matrix.det_diagonal]
    simp [e]
  set Δ₀ : GL (Fin (m + 1)) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal e)
    (by rw [hdetE]; exact ha0)
  have hΔval : (Δ₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal e := rfl
  have hdet1 : Matrix.GeneralLinearGroup.det (A₀⁻¹ * Δ₀) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hΔval,
      hdetE]
  obtain ⟨s, hs⟩ : A₀⁻¹ * Δ₀ ∈ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet1
  refine ⟨s, fun b hb γ hγ => ?_⟩
  obtain ⟨A, hA⟩ := hgl b hb
  set N : GL (Fin (m + 1)) F := A₀ * A * A₀⁻¹ with hN
  have hNd : (N : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := hA₀ b hb A hA
  have hNid : ((N⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := by
    rw [TypeA.coe_inv_of_diagonal hNd.diagonal_diag.symm]
    exact Matrix.isDiag_diagonal _
  obtain ⟨h, hh, hhz⟩ := conjSL_isDiag_eq_torus hm hNid hγ
  refine ⟨h, hh, fun z hz => ?_⟩
  have hb' : ∀ v, (b : G) * ψ v * b⁻¹ = ψ (InnerDiagA.conjSL A⁻¹ v) := by
    intro v
    have h1 := hA (InnerDiagA.conjSL A⁻¹ v)
    rw [← RootPlaneA.conjSL_mul, mul_inv_cancel, RootPlaneA.conjSL_one] at h1
    calc (b : G) * ψ v * b⁻¹ = b * (b⁻¹ * ψ (InnerDiagA.conjSL A⁻¹ v) * b) * b⁻¹ := by rw [h1]
      _ = ψ (InnerDiagA.conjSL A⁻¹ v) := by group
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hb', ← hhz z hz]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  simp only [RootPlaneA.toGL_conjSL, map_mul, map_inv, hs]
  have hcomm : Commute N⁻¹ Δ₀ :=
    RootPlaneA.commute_of_isDiag hNid (by rw [hΔval]; exact Matrix.isDiag_diagonal e)
  have hA' : A = A₀⁻¹ * N * A₀ := by rw [hN]; group
  rw [hA']
  calc _ = A₀⁻¹ * (N⁻¹ * Δ₀) * Matrix.SpecialLinearGroup.toGL z * (N⁻¹ * Δ₀)⁻¹ * A₀ := by group
    _ = A₀⁻¹ * (Δ₀ * N⁻¹) * Matrix.SpecialLinearGroup.toGL z * (Δ₀ * N⁻¹)⁻¹ * A₀ := by
      rw [hcomm.eq]
    _ = _ := by group

end StdPosA

end CFSG.StandardType

end
