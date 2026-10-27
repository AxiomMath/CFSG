module

public import CFSG.RankThree.PartTwo.Sec4.Item417ResProofTwoMain
public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofDiag
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofPerm
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofFrameP
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofUnitary
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec15.KSL3Two
open Matrix

namespace Res417Frame

variable {K : Type} [Field K]

theorem isMonomialWith_of_conj_diagonal {X : GL (Fin 3) K} {d : Fin 3 → K}
    (hd : Function.Injective d)
    (hX : ((X : Matrix (Fin 3) (Fin 3) K) * diagonal d *
      ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).IsDiag) :
    ∃ σ : Fin 3 → Fin 3, IsMonomialWith (X : Matrix (Fin 3) (Fin 3) K) σ := by
  set Δ : Matrix (Fin 3) (Fin 3) K := (X : Matrix (Fin 3) (Fin 3) K) * diagonal d *
    ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hΔ
  have hXD : (X : Matrix (Fin 3) (Fin 3) K) * diagonal d = Δ * X := by
    rw [hΔ, Matrix.mul_assoc _ _ (X : Matrix (Fin 3) (Fin 3) K), ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.mul_one]
  have hent : ∀ r i, (X : Matrix (Fin 3) (Fin 3) K) r i ≠ 0 → Δ r r = d i := by
    intro r i hri
    have h1 := congrFun (congrFun hXD r) i
    rw [Matrix.mul_diagonal, ← hX.diagonal_diag, Matrix.diagonal_mul] at h1
    simp only [Matrix.diag_apply] at h1
    have : (X : Matrix (Fin 3) (Fin 3) K) r i * (d i - Δ r r) = 0 := by linear_combination h1
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hri)).symm
  have hcol : ∀ i, ∃ r, (X : Matrix (Fin 3) (Fin 3) K) r i ≠ 0 := by
    intro i
    by_contra hall
    push Not at hall
    have h0 : (X : Matrix (Fin 3) (Fin 3) K).det = 0 :=
      Matrix.det_eq_zero_of_column_eq_zero i hall
    exact (X.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero h0
  choose σ hσ using hcol
  have hσinj : Function.Injective σ := by
    intro i i' h
    apply hd
    rw [← hent _ _ (hσ i), ← hent _ _ (hσ i'), h]
  have hσsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hσinj
  refine ⟨σ, fun i j => ⟨fun hji => ?_, fun hj => hj ▸ hσ i⟩⟩
  obtain ⟨i', rfl⟩ := hσsurj j
  have h1 := hent _ _ hji
  rw [hent _ _ (hσ i')] at h1
  rw [hd h1]

end Res417Frame

open Res417Frame

theorem coe_e_conj_of_isPGLAt {H : Type} [Group H] {L : Subgroup H} [L.Normal] {K : Type}
    [Field K] {π : Bool} {p f : ℕ} {e : L ≃* slPi π 3 (p ^ f) K} {a : H} {y : GL (Fin 3) K}
    (hy : IsPGLAt e a y) {t : H} (ht : t ∈ L) (ht' : a * t * a⁻¹ ∈ L) :
    ((e ⟨a * t * a⁻¹, ht'⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      y * (e ⟨t, ht⟩ : GL (Fin 3) K) * y⁻¹ := by
  have h1 := hy.2 (e ⟨t, ht⟩)
  rw [coe_slAct_eq] at h1
  rw [← h1]
  congr 3
  rw [MulEquiv.symm_apply_apply]

theorem coe_e_conj_of_isPGLAtP {H : Type} [Group H] {L : Subgroup H} [L.Normal] {K : Type}
    [Field K] {π : Bool} {p f : ℕ} {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {a : H}
    {y : GL (Fin 3) K} (hy : IsPGLAtP e a y) {t : H} (ht : t ∈ L) (ht' : a * t * a⁻¹ ∈ L) :
    ((e ⟨a * t * a⁻¹, ht'⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk y * (e ⟨t, ht⟩ : projImage (slPi π 3 (p ^ f) K)) *
        (ProjGenLinGroup.mk y)⁻¹ := by
  have h1 := hy.2 (e ⟨t, ht⟩)
  rw [coe_slAct_eqP] at h1
  rw [← h1]
  congr 3
  rw [MulEquiv.symm_apply_apply]

theorem item417SL3FrameEven_holds : Item417SL3FrameEven := by
  intro H _ _ L _ n K _ hK hq e A c hA _ hc3 hAc hpgl hb
  obtain ⟨b, hbA, hbL, hbc⟩ := hb
  have := hK.finite
  have h2 : (2 : K) = 0 := Res417Two.two_eq_zero_of_piField hK
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨-, hLC⟩ := mem_and_inf_centralizer_eq hK hq e hA hc3 hAc
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  set eb : GL (Fin 3) K := (e ⟨b, hbL⟩ : GL (Fin 3) K) with heb
  have hebZ : eb ∉ zPi true 3 (2 ^ n) K := by
    intro hz
    apply hbc
    rw [← hLC]
    exact ⟨hbL, mem_centralizer_of_scalar hbL (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)⟩
  have hb3 : b ^ 3 = 1 := hA.1.2 b hbA
  have heb3 : orderOf eb = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : eb ^ 3 = 1 := by
      rw [heb, ← Subgroup.coe_pow, ← map_pow]
      have : (⟨b, hbL⟩ : L) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hb3]; rfl)
      rw [this, map_one, Subgroup.coe_one]
    refine orderOf_eq_prime h3 fun h1 => hebZ ?_
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨g, -, hgD⟩ := rank3II_4_10_three hK hq hτ hτ1 (e ⟨b, hbL⟩).2 hebZ heb3
  set d : Fin 3 → K := ![τ, τ ^ 2, 1] with hddef
  have hd : Function.Injective d := Res417Two.injective_diagTau_entries hτ hτ1
  have hψb : ((g⁻¹ * eb * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    rw [hgD, coe_diagTau_eq_diagonal]
  have hψmul : ∀ X Y : GL (Fin 3) K, g⁻¹ * (X * Y) * g = (g⁻¹ * X * g) * (g⁻¹ * Y * g) :=
    fun X Y => by group
  have hψinj : ∀ X Y : GL (Fin 3) K, g⁻¹ * X * g = g⁻¹ * Y * g → X = Y := fun X Y h => by
    have := congrArg (fun Z => g * Z * g⁻¹) h
    simpa [mul_assoc] using this
  have hdiag : ∀ a ∈ A, ∀ y, IsPGLAt e a y →
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro a ha y hy
    apply isDiag_of_commute_diagonal hd
    have hc := isPGLAt_commute_of_mem hbL (hAcomm a ha b hbA) hy
    rw [← hψb, ← Units.val_mul, ← Units.val_mul, ← hψmul, ← hψmul, hc]
  have hcube : ∀ a ∈ A, ∀ y, IsPGLAt e a y → ∀ i j,
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i ^ 3 =
        ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) j j ^ 3 := by
    intro a ha y hy i j
    obtain ⟨ℓ, hℓ⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1
      (pow_three_mem_zPi hK hq (hA.1.2 a ha) hy)
    have h3 : ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
        (ℓ : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      have e1 : (g⁻¹ * y * g) ^ 3 = g⁻¹ * y ^ 3 * g := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      rw [← Units.val_pow_eq_pow_val, e1, ← hℓ,
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ℓ g⁻¹).eq, inv_mul_cancel_right,
        coe_scalar_eq_smul]
    have hD := hdiag a ha y hy
    have hk : ∀ k, ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k k ^ 3 = ℓ := by
      intro k
      have := congrFun (congrFun h3 k) k
      rw [← hD.diagonal_diag, Matrix.diagonal_pow, Matrix.diagonal_apply_eq] at this
      simpa using this
    rw [hk i, hk j]
  have hcent : ∀ m (hm : m ∈ L),
      ((g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).IsDiag → ∀ a ∈ A, a * m = m * a := by
    intro m hm hmD a ha
    obtain ⟨y, hy⟩ := hpgl a ha
    have hmL : a * m * a⁻¹ ∈ L := ‹L.Normal›.conj_mem m hm a
    have h1 := coe_e_conj_of_isPGLAt hy hm hmL
    have h2 : y * (e ⟨m, hm⟩ : GL (Fin 3) K) * y⁻¹ = (e ⟨m, hm⟩ : GL (Fin 3) K) := by
      apply hψinj
      have hc := commute_of_isDiag (hdiag a ha y hy) hmD
      have hc' : (g⁻¹ * y * g) * (g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g) =
          (g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g) * (g⁻¹ * y * g) := Units.ext (by
        rw [Units.val_mul, Units.val_mul]
        exact hc)
      calc g⁻¹ * (y * (e ⟨m, hm⟩ : GL (Fin 3) K) * y⁻¹) * g =
            (g⁻¹ * y * g) * (g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g) * (g⁻¹ * y * g)⁻¹ := by
              group
        _ = g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g := by rw [hc']; group
    rw [h2] at h1
    have h3 : (⟨a * m * a⁻¹, hmL⟩ : L) = ⟨m, hm⟩ :=
      e.injective (Subtype.ext h1)
    have h4 : a * m * a⁻¹ = m := congrArg Subtype.val h3
    calc a * m = a * m * a⁻¹ * a := by group
      _ = m * a := by rw [h4]
  have hsl : ∀ σ : Equiv.Perm (Fin 3), g * permGL σ * g⁻¹ ∈ slPi true 3 (2 ^ n) K := by
    intro σ
    rw [mem_slPi_true, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      det_permGL h2, mul_one, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one]
  let s : Equiv.Perm (Fin 3) →* slPi true 3 (2 ^ n) K :=
    ((MulAut.conj g).toMonoidHom.comp permGL).codRestrict _ hsl
  let Θ : Equiv.Perm (Fin 3) →* H := L.subtype.comp (e.symm.toMonoidHom.comp s)
  have hΘL : ∀ σ, Θ σ ∈ L := fun σ => (e.symm (s σ)).2
  have heΘ : ∀ σ, ((e ⟨Θ σ, hΘL σ⟩ : slPi true 3 (2 ^ n) K) : GL (Fin 3) K) =
      g * permGL σ * g⁻¹ := by
    intro σ
    have : (⟨Θ σ, hΘL σ⟩ : L) = e.symm (s σ) := rfl
    rw [this, MulEquiv.apply_symm_apply]
    rfl
  have hψΘ : ∀ σ, g⁻¹ * ((e ⟨Θ σ, hΘL σ⟩ : slPi true 3 (2 ^ n) K) : GL (Fin 3) K) * g =
      permGL σ := by
    intro σ
    rw [heΘ]
    group
  refine nonempty_autIn_equiv_perm Θ hΘL ?_ ?_ ?_
  ·
    intro σ a ha
    obtain ⟨y, hy⟩ := hpgl a ha
    have htL : Θ σ ∈ L := hΘL σ
    have ht'L : a * (Θ σ)⁻¹ * a⁻¹ ∈ L := ‹L.Normal›.conj_mem _ (L.inv_mem htL) a
    have hmL : Θ σ * (a * (Θ σ)⁻¹ * a⁻¹) ∈ L := L.mul_mem htL ht'L
    have hem : ((e ⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩ : slPi true 3 (2 ^ n) K) : GL (Fin 3) K) =
        (e ⟨Θ σ, htL⟩ : GL (Fin 3) K) * y * (e ⟨Θ σ, htL⟩ : GL (Fin 3) K)⁻¹ * y⁻¹ := by
      have e1 : (⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩ : L) =
          ⟨Θ σ, htL⟩ * ⟨a * (Θ σ)⁻¹ * a⁻¹, ht'L⟩ := rfl
      rw [e1, map_mul, Subgroup.coe_mul, coe_e_conj_of_isPGLAt hy (L.inv_mem htL) ht'L]
      have e2 : (⟨(Θ σ)⁻¹, L.inv_mem htL⟩ : L) = (⟨Θ σ, htL⟩ : L)⁻¹ := rfl
      rw [e2, map_inv, Subgroup.coe_inv]
      group
    have hψm : g⁻¹ * ((e ⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩ : slPi true 3 (2 ^ n) K) :
        GL (Fin 3) K) * g =
        permGL σ * (g⁻¹ * y * g) * (permGL σ)⁻¹ * (g⁻¹ * y * g)⁻¹ := by
      rw [hem, ← hψΘ σ]
      group
    obtain ⟨hmD, hm3⟩ := commutator_permGL σ (hdiag a ha y hy) (hcube a ha y hy)
    rw [← hψm] at hmD hm3
    have hmA : Θ σ * (a * (Θ σ)⁻¹ * a⁻¹) ∈ A := by
      refine mem_of_maximal_of_commute hA ?_ fun a' ha' => hcent _ hmL hmD a' ha'
      have h1 : ((e ⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩ : slPi true 3 (2 ^ n) K) :
          GL (Fin 3) K) ^ 3 = 1 := by
        have e1 : (g⁻¹ * ((e ⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩ : slPi true 3 (2 ^ n) K) :
            GL (Fin 3) K) * g) ^ 3 = g⁻¹ * ((e ⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩ :
              slPi true 3 (2 ^ n) K) : GL (Fin 3) K) ^ 3 * g := by
          simp only [pow_succ, pow_zero, one_mul]
          group
        rw [e1] at hm3
        calc ((e ⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩ : slPi true 3 (2 ^ n) K) :
              GL (Fin 3) K) ^ 3 =
            g * (g⁻¹ * ((e ⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩ : slPi true 3 (2 ^ n) K) :
              GL (Fin 3) K) ^ 3 * g) * g⁻¹ := by group
          _ = 1 := by rw [hm3]; group
      have h2' : (e ⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, h1]; rfl)
      rw [← map_pow, map_eq_one_iff _ e.injective] at h2'
      exact congrArg Subtype.val h2'
    have : Θ σ * a * (Θ σ)⁻¹ = (Θ σ * (a * (Θ σ)⁻¹ * a⁻¹)) * a := by group
    rw [this]
    exact A.mul_mem hmA ha
  ·
    intro σ hσ
    have h1 := hσ b hbA
    apply eq_one_of_permGL_commute hd
    rw [← hψb, ← hψΘ σ, ← Units.val_mul, ← Units.val_mul]
    congr 1
    have hbt : Θ σ * b * (Θ σ)⁻¹ = b := by rw [h1]; group
    have hbL' : Θ σ * b * (Θ σ)⁻¹ ∈ L := ‹L.Normal›.conj_mem b hbL (Θ σ)
    have h2 : (e ⟨Θ σ, hΘL σ⟩ : GL (Fin 3) K) * eb * (e ⟨Θ σ, hΘL σ⟩ : GL (Fin 3) K)⁻¹ = eb := by
      have e1 : (⟨Θ σ * b * (Θ σ)⁻¹, hbL'⟩ : L) =
          ⟨Θ σ, hΘL σ⟩ * ⟨b, hbL⟩ * (⟨Θ σ, hΘL σ⟩ : L)⁻¹ := rfl
      have e2 : (⟨Θ σ * b * (Θ σ)⁻¹, hbL'⟩ : L) = ⟨b, hbL⟩ := Subtype.ext hbt
      have := congrArg (fun x : L => ((e x : slPi true 3 (2 ^ n) K) : GL (Fin 3) K)) e1
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [← this, e2]
    calc g⁻¹ * ((e ⟨Θ σ, hΘL σ⟩ : slPi true 3 (2 ^ n) K) : GL (Fin 3) K) * g * (g⁻¹ * eb * g)
        = g⁻¹ * ((e ⟨Θ σ, hΘL σ⟩ : GL (Fin 3) K) * eb * (e ⟨Θ σ, hΘL σ⟩ : GL (Fin 3) K)⁻¹) *
            g * (g⁻¹ * ((e ⟨Θ σ, hΘL σ⟩ : slPi true 3 (2 ^ n) K) : GL (Fin 3) K) * g) := by
          group
      _ = _ := by rw [h2]
  ·
    intro l hl hlN
    have hlb : l * b * l⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hlN b).mp hbA
    have hlbL : l * b * l⁻¹ ∈ L := ‹L.Normal›.conj_mem b hbL l
    have hy := isPGLAt_of_mem e (fun h => absurd h (by decide)) hlbL
    have hD := hdiag _ hlb _ hy
    set X : GL (Fin 3) K := g⁻¹ * (e ⟨l, hl⟩ : GL (Fin 3) K) * g with hX
    have hconj : g⁻¹ * ((e ⟨l * b * l⁻¹, hlbL⟩ : slPi true 3 (2 ^ n) K) : GL (Fin 3) K) * g =
        X * (g⁻¹ * eb * g) * X⁻¹ := by
      have e1 : (⟨l * b * l⁻¹, hlbL⟩ : L) = ⟨l, hl⟩ * ⟨b, hbL⟩ * (⟨l, hl⟩ : L)⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hX,
        heb]
      group
    rw [hconj, Units.val_mul, Units.val_mul, hψb] at hD
    obtain ⟨σ₀, hσ₀⟩ := isMonomialWith_of_conj_diagonal hd hD
    obtain ⟨σ, hσ⟩ := exists_perm_of_isMonomialWith hσ₀
    refine ⟨σ, fun a ha => ?_⟩
    have hmL : (Θ σ)⁻¹ * l ∈ L := L.mul_mem (L.inv_mem (hΘL σ)) hl
    have hmD : ((g⁻¹ * (e ⟨(Θ σ)⁻¹ * l, hmL⟩ : GL (Fin 3) K) * g : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).IsDiag := by
      have e1 : (⟨(Θ σ)⁻¹ * l, hmL⟩ : L) = (⟨Θ σ, hΘL σ⟩ : L)⁻¹ * ⟨l, hl⟩ := rfl
      have e2 : g⁻¹ * ((e ⟨(Θ σ)⁻¹ * l, hmL⟩ : slPi true 3 (2 ^ n) K) : GL (Fin 3) K) * g =
          (permGL σ)⁻¹ * X := by
        rw [e1, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, ← hψΘ σ, hX]
        group
      rw [e2]
      exact hσ
    have hc := hcent _ hmL hmD a ha
    calc l * a * l⁻¹ = Θ σ * (((Θ σ)⁻¹ * l) * a) * l⁻¹ := by group
      _ = Θ σ * (a * ((Θ σ)⁻¹ * l)) * l⁻¹ := by rw [← hc]
      _ = Θ σ * a * (Θ σ)⁻¹ := by group

end CFSG.RankThree.PartTwo.Sec4

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec15.KSL3Two
open Matrix Res417Frame

theorem item417L3FrameEven_holds : Item417L3FrameEven := by
  intro H _ _ L _ n K _ hK hq e A c hA hA27 hc3 hAc hpgl hfr
  obtain ⟨b, hb, hbd⟩ := hfr
  have := hK.finite
  have h2 : (2 : K) = 0 := Res417Two.two_eq_zero_of_piField hK
  have hπ : true = false → UnitaryFieldData 2 n K := fun h => absurd h (by decide)
  have hq2 : 2 < 2 ^ n := by
    have hn := hK.one_le
    have hq' : 2 ^ n % 3 = 1 := hq
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h
    · norm_num at hq'
    · calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
  have : Group.IsPerfect (projImage (slPi true 3 (2 ^ n) K)) :=
    Sec13.isPerfect_projImage_slPi hK hq2
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨hEd, a₀, ha₀, y₀, hy₀, κ, hκ0, hy₀b⟩ :=
    exists_regular_liftP_of_frame hK hq hA hA27 hc3 hAc hpgl hb hbd hτ
  set d₀ : Fin 3 → K := fun i => κ * (![1, τ, τ ^ 2] : Fin 3 → K) i with hd₀def
  have hd₀ : Function.Injective d₀ := injective_smul_tau hτ hτ1 hκ0
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hd₀0 : ∀ i, d₀ i ≠ 0 := by
    intro i
    refine mul_ne_zero hκ0 ?_
    fin_cases i
    · exact one_ne_zero
    · exact hτ0
    · exact pow_ne_zero 2 hτ0
  set g : GL (Fin 3) K := (isUnit_frameMat hb).unit with hgdef
  have hgm : (g : Matrix (Fin 3) (Fin 3) K) = frameMat b := rfl
  have hfrm : ∀ (y : GL (Fin 3) K) (d : Fin 3 → K),
      (∀ i, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d i • b i) →
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    intro y d hyd
    have h1 := mul_frameMat_eq hyd
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hgm, h1, ← hgm, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hdiagR : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
      (pglHomP hK hq A hpgl).range →
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro y hy
    choose d hd using hEd y hy
    rw [hfrm y d hd]
    exact isDiag_diagonal d
  have hdiag : ∀ a ∈ A, ∀ y, IsPGLAtP e a y →
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag :=
    fun a ha y hy => hdiagR y (mk_mem_range_pglHomP ha hy)
  have hy₀D : ((g⁻¹ * y₀ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d₀ :=
    hfrm y₀ d₀ hy₀b
  have hψmul : ∀ X Y : GL (Fin 3) K, g⁻¹ * (X * Y) * g = (g⁻¹ * X * g) * (g⁻¹ * Y * g) :=
    fun X Y => by group
  have hψinj : ∀ X Y : GL (Fin 3) K, g⁻¹ * X * g = g⁻¹ * Y * g → X = Y := fun X Y h => by
    have := congrArg (fun Z => g * Z * g⁻¹) h
    simpa [mul_assoc] using this
  have hcube : ∀ a ∈ A, ∀ y, IsPGLAtP e a y → ∀ i j,
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i ^ 3 =
        ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) j j ^ 3 := by
    intro a ha y hy i j
    obtain ⟨ℓ, hℓ⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1
      (pow_three_mem_zPiP hK hq (hA.1.2 a ha) hy)
    have h3 : ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
        (ℓ : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      have e1 : (g⁻¹ * y * g) ^ 3 = g⁻¹ * y ^ 3 * g := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      rw [← Units.val_pow_eq_pow_val, e1, ← hℓ,
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ℓ g⁻¹).eq, inv_mul_cancel_right,
        coe_scalar_eq_smul]
    have hD := hdiag a ha y hy
    have hk : ∀ k, ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k k ^ 3 = ℓ := by
      intro k
      have := congrFun (congrFun h3 k) k
      rw [← hD.diagonal_diag, Matrix.diagonal_pow, Matrix.diagonal_apply_eq] at this
      simpa using this
    rw [hk i, hk j]
  have hcent : ∀ m (hm : m ∈ L) (s : GL (Fin 3) K),
      ((e ⟨m, hm⟩ : projImage (slPi true 3 (2 ^ n) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk s →
      ((g⁻¹ * s * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag →
      ∀ a ∈ A, a * m = m * a := by
    intro m hm s hms hsD a ha
    obtain ⟨y, hy⟩ := hpgl a ha
    have hmL : a * m * a⁻¹ ∈ L := ‹L.Normal›.conj_mem m hm a
    have h1 := coe_e_conj_of_isPGLAtP hy hm hmL
    have hc : y * s = s * y := by
      have hc := commute_of_isDiag (hdiag a ha y hy) hsD
      have hc' : (g⁻¹ * y * g) * (g⁻¹ * s * g) = (g⁻¹ * s * g) * (g⁻¹ * y * g) :=
        Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hc)
      apply hψinj
      rw [hψmul, hψmul, hc']
    rw [hms, ← map_inv, ← map_mul, ← map_mul, hc, mul_inv_cancel_right, ← hms] at h1
    have h3 : (⟨a * m * a⁻¹, hmL⟩ : L) = ⟨m, hm⟩ := e.injective (Subtype.ext h1)
    have h4 : a * m * a⁻¹ = m := congrArg Subtype.val h3
    calc a * m = a * m * a⁻¹ * a := by group
      _ = m * a := by rw [h4]
  have hsl : ∀ σ : Equiv.Perm (Fin 3), g * permGL σ * g⁻¹ ∈ slPi true 3 (2 ^ n) K := by
    intro σ
    rw [mem_slPi_true, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      det_permGL h2, mul_one, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one]
  let s : Equiv.Perm (Fin 3) →* slPi true 3 (2 ^ n) K :=
    ((MulAut.conj g).toMonoidHom.comp permGL).codRestrict _ hsl
  let Θ : Equiv.Perm (Fin 3) →* H :=
    L.subtype.comp (e.symm.toMonoidHom.comp ((projOf (slPi true 3 (2 ^ n) K)).comp s))
  have hΘL : ∀ σ, Θ σ ∈ L := fun σ => (e.symm _).2
  have heΘ : ∀ σ, ((e ⟨Θ σ, hΘL σ⟩ : projImage (slPi true 3 (2 ^ n) K)) :
      ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (g * permGL σ * g⁻¹) := by
    intro σ
    have : (⟨Θ σ, hΘL σ⟩ : L) = e.symm ((projOf (slPi true 3 (2 ^ n) K)) (s σ)) := rfl
    rw [this, MulEquiv.apply_symm_apply, coe_projOf]
    rfl
  refine nonempty_autIn_equiv_perm Θ hΘL ?_ ?_ ?_
  ·
    intro σ a ha
    obtain ⟨y, hy⟩ := hpgl a ha
    have htL : Θ σ ∈ L := hΘL σ
    have ht'L : a * (Θ σ)⁻¹ * a⁻¹ ∈ L := ‹L.Normal›.conj_mem _ (L.inv_mem htL) a
    have hmL : Θ σ * (a * (Θ σ)⁻¹ * a⁻¹) ∈ L := L.mul_mem htL ht'L
    set C : GL (Fin 3) K := (g * permGL σ * g⁻¹) * y * (g * permGL σ * g⁻¹)⁻¹ * y⁻¹ with hC
    have hem : ((e ⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩ : projImage (slPi true 3 (2 ^ n) K)) :
        ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk C := by
      have e1 : (⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩ : L) =
          ⟨Θ σ, htL⟩ * ⟨a * (Θ σ)⁻¹ * a⁻¹, ht'L⟩ := rfl
      rw [e1, map_mul, Subgroup.coe_mul, coe_e_conj_of_isPGLAtP hy (L.inv_mem htL) ht'L]
      have e2 : (⟨(Θ σ)⁻¹, L.inv_mem htL⟩ : L) = (⟨Θ σ, htL⟩ : L)⁻¹ := rfl
      rw [e2, map_inv, Subgroup.coe_inv, heΘ σ, hC]
      simp only [map_mul, map_inv]
      group
    have hψC : g⁻¹ * C * g = permGL σ * (g⁻¹ * y * g) * (permGL σ)⁻¹ * (g⁻¹ * y * g)⁻¹ := by
      rw [hC]
      group
    obtain ⟨hCD, hC3⟩ := commutator_permGL σ (hdiag a ha y hy) (hcube a ha y hy)
    rw [← hψC] at hCD hC3
    have hmA : Θ σ * (a * (Θ σ)⁻¹ * a⁻¹) ∈ A := by
      refine mem_of_maximal_of_commute hA ?_ fun a' ha' => hcent _ hmL C hem hCD a' ha'
      have hC1 : C ^ 3 = 1 := by
        have e1 : (g⁻¹ * C * g) ^ 3 = g⁻¹ * C ^ 3 * g := by
          simp only [pow_succ, pow_zero, one_mul]
          group
        rw [e1] at hC3
        calc C ^ 3 = g * (g⁻¹ * C ^ 3 * g) * g⁻¹ := by group
          _ = 1 := by rw [hC3]; group
      have h1 : (e ⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩) ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hem, ← map_pow, hC1, map_one, Subgroup.coe_one]
      rw [← map_pow, map_eq_one_iff _ e.injective] at h1
      exact congrArg Subtype.val h1
    have : Θ σ * a * (Θ σ)⁻¹ = (Θ σ * (a * (Θ σ)⁻¹ * a⁻¹)) * a := by group
    rw [this]
    exact A.mul_mem hmA ha
  ·
    intro σ hσ
    have key : ∀ σ : Equiv.Perm (Fin 3), (∃ k, σ k = k) ∨ σ ^ 3 = 1 := by decide
    rcases key σ with ⟨k, hk⟩ | h3
    · have h1 := hσ a₀ ha₀
      have ha₀L : a₀ * Θ σ * a₀⁻¹ ∈ L := ‹L.Normal›.conj_mem _ (hΘL σ) a₀
      have h2 := coe_e_conj_of_isPGLAtP hy₀ (hΘL σ) ha₀L
      have h3 : (⟨a₀ * Θ σ * a₀⁻¹, ha₀L⟩ : L) = ⟨Θ σ, hΘL σ⟩ := Subtype.ext (by
        change a₀ * Θ σ * a₀⁻¹ = Θ σ
        rw [← h1]
        group)
      rw [h3, heΘ] at h2
      have h4 : (g * permGL σ * g⁻¹)⁻¹ * (y₀ * (g * permGL σ * g⁻¹) * y₀⁻¹) ∈
          Subgroup.center (GL (Fin 3) K) := by
        rw [← ProjGenLinGroup.mk_eq_one]
        have : ProjGenLinGroup.mk ((g * permGL σ * g⁻¹)⁻¹ * (y₀ * (g * permGL σ * g⁻¹) * y₀⁻¹)) =
            (ProjGenLinGroup.mk (g * permGL σ * g⁻¹))⁻¹ *
              (ProjGenLinGroup.mk y₀ * ProjGenLinGroup.mk (g * permGL σ * g⁻¹) *
                (ProjGenLinGroup.mk y₀)⁻¹) := by
          simp only [map_mul, map_inv]
        rw [this, ← h2, inv_mul_cancel]
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h4
      obtain ⟨μ, hμ⟩ := h4
      have h5 : y₀ * (g * permGL σ * g⁻¹) * y₀⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) μ * (g * permGL σ * g⁻¹) := by
        rw [← (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ (g * permGL σ * g⁻¹)).eq, hμ]
        group
      have h6 : (g⁻¹ * y₀ * g) * permGL σ =
          GeneralLinearGroup.scalar (Fin 3) μ * (permGL σ * (g⁻¹ * y₀ * g)) := by
        calc (g⁻¹ * y₀ * g) * permGL σ =
            g⁻¹ * (y₀ * (g * permGL σ * g⁻¹) * y₀⁻¹) * g * (g⁻¹ * y₀ * g) := by group
          _ = g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) μ * (g * permGL σ * g⁻¹)) * g *
              (g⁻¹ * y₀ * g) := by rw [h5]
          _ = g⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ * g * (permGL σ * (g⁻¹ * y₀ * g)) := by
              group
          _ = GeneralLinearGroup.scalar (Fin 3) μ * (permGL σ * (g⁻¹ * y₀ * g)) := by
              rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ g⁻¹).eq,
                inv_mul_cancel_right]
      apply eq_one_of_diagonal_mul_permGL hd₀ hd₀0 (μ := (μ : K)) _ hk
      have h7 := congrArg (fun Z : GL (Fin 3) K => (Z : Matrix (Fin 3) (Fin 3) K)) h6
      simp only [Units.val_mul, hy₀D, coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul] at h7
      exact h7
    · have hΘA : Θ σ ∈ A := by
        refine mem_of_maximal_of_commute hA ?_ fun a ha => (hσ a ha).symm
        rw [← map_pow, h3, map_one]
      have hyΘ : IsPGLAtP e (Θ σ) (g * permGL σ * g⁻¹) :=
        isPGLAtP_of_mem e hπ (hΘL σ) (hsl σ) (heΘ σ)
      have hD := hdiag _ hΘA _ hyΘ
      apply eq_one_of_permGL_isDiag (K := K)
      have : g⁻¹ * (g * permGL σ * g⁻¹) * g = permGL σ := by group
      rw [this] at hD
      exact hD
  ·
    intro l hl hlN
    obtain ⟨s₀, hs₀, hs₀l⟩ := (e ⟨l, hl⟩).2
    have hel : ((e ⟨l, hl⟩ : projImage (slPi true 3 (2 ^ n) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk s₀ := hs₀l.symm
    set X : GL (Fin 3) K := g⁻¹ * s₀ * g with hX
    set Hd : Subgroup (GL (Fin 3) K) := ((pglHomP hK hq A hpgl).range.comap
      (QuotientGroup.mk' (StatedScalars (Fin 3) K))).map (MulAut.conj g⁻¹).toMonoidHom with hHd
    have hmemHd : ∀ u, u ∈ Hd ↔ ∃ y : GL (Fin 3) K,
        (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHomP hK hq A hpgl).range ∧
          g⁻¹ * y * g = u := by
      intro u
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y, hy, ?_⟩
        change g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹
        rw [inv_inv]
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y, hy, ?_⟩
        change g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * y * g
        rw [inv_inv]
    have hHdiag : ∀ u ∈ Hd, (u : Matrix (Fin 3) (Fin 3) K).IsDiag := by
      intro u hu
      obtain ⟨y, hy, rfl⟩ := (hmemHd u).mp hu
      exact hdiagR y hy
    have hsep : ∀ i j : Fin 3, i ≠ j →
        ∃ u ∈ Hd, (u : Matrix (Fin 3) (Fin 3) K) i i ≠ (u : Matrix (Fin 3) (Fin 3) K) j j := by
      intro i j hij
      refine ⟨g⁻¹ * y₀ * g, (hmemHd _).mpr ⟨y₀, mk_mem_range_pglHomP ha₀ hy₀, rfl⟩, ?_⟩
      rw [hy₀D, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      exact fun h => hij (hd₀ h)
    have hlinv : l⁻¹ ∈ L := L.inv_mem hl
    have hel' : ((e ⟨l⁻¹, hlinv⟩ : projImage (slPi true 3 (2 ^ n) K)) :
        ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk s₀⁻¹ := by
      have : (⟨l⁻¹, hlinv⟩ : L) = (⟨l, hl⟩ : L)⁻¹ := rfl
      rw [this, map_inv, Subgroup.coe_inv, hel, map_inv]
    have hnorm : ∀ u ∈ Hd, X⁻¹ * u * X ∈ Hd := by
      intro u hu
      obtain ⟨y, ⟨⟨a, ha⟩, hay⟩, rfl⟩ := (hmemHd u).mp hu
      obtain ⟨ya, hya⟩ := hpgl a ha
      rw [pglHomP_apply ⟨a, ha⟩ hya, QuotientGroup.eq] at hay
      obtain ⟨μ, hμ⟩ := hay
      have hyya : y = ya * GeneralLinearGroup.scalar (Fin 3) μ := by rw [hμ]; group
      have hla : l⁻¹ * a * l ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlN) a).mp ha
        rwa [inv_inv] at this
      have hy' : IsPGLAtP e (l⁻¹ * a * l) (s₀⁻¹ * ya * s₀) :=
        isPGLAtP_mul e (isPGLAtP_mul e (isPGLAtP_of_mem e hπ hlinv (inv_mem hs₀) hel') hya)
          (isPGLAtP_of_mem e hπ hl hs₀ hel)
      refine (hmemHd _).mpr ⟨s₀⁻¹ * y * s₀, ?_, by rw [hX]; group⟩
      have hmk : ((s₀⁻¹ * y * s₀ : GL (Fin 3) K) : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) =
          ((s₀⁻¹ * ya * s₀ : GL (Fin 3) K) : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) := by
        rw [QuotientGroup.eq]
        refine ⟨μ⁻¹, ?_⟩
        rw [hyya]
        have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ⁻¹ s₀⁻¹).eq
        calc GeneralLinearGroup.scalar (Fin 3) μ⁻¹ =
            s₀⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * s₀ := by
              rw [hc, inv_mul_cancel_right]
          _ = (s₀⁻¹ * (ya * GeneralLinearGroup.scalar (Fin 3) μ) * s₀)⁻¹ * (s₀⁻¹ * ya * s₀) := by
              rw [map_inv]
              group
      rw [hmk]
      exact mk_mem_range_pglHomP hla hy'
    obtain ⟨σ₀, hσ₀⟩ := exists_monomial_of_normalizes hHdiag hsep hnorm
    obtain ⟨σ, hσ⟩ := exists_perm_of_isMonomialWith hσ₀
    refine ⟨σ, fun a ha => ?_⟩
    have hmL : (Θ σ)⁻¹ * l ∈ L := L.mul_mem (L.inv_mem (hΘL σ)) hl
    have hem : ((e ⟨(Θ σ)⁻¹ * l, hmL⟩ : projImage (slPi true 3 (2 ^ n) K)) :
        ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk ((g * permGL σ * g⁻¹)⁻¹ * s₀) := by
      have e1 : (⟨(Θ σ)⁻¹ * l, hmL⟩ : L) = (⟨Θ σ, hΘL σ⟩ : L)⁻¹ * ⟨l, hl⟩ := rfl
      rw [e1, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, heΘ σ, hel]
      simp only [map_mul, map_inv]
    have hmD : ((g⁻¹ * ((g * permGL σ * g⁻¹)⁻¹ * s₀) * g : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).IsDiag := by
      have e2 : g⁻¹ * ((g * permGL σ * g⁻¹)⁻¹ * s₀) * g = (permGL σ)⁻¹ * X := by
        rw [hX]
        group
      rw [e2]
      exact hσ
    have hc := hcent _ hmL _ hem hmD a ha
    calc l * a * l⁻¹ = Θ σ * (((Θ σ)⁻¹ * l) * a) * l⁻¹ := by group
      _ = Θ σ * (a * ((Θ σ)⁻¹ * l)) * l⁻¹ := by rw [← hc]
      _ = Θ σ * a * (Θ σ)⁻¹ := by group

end CFSG.RankThree.PartTwo.Sec4
