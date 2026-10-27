module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3UniBlock
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly
open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.CALinearPrimary

private lemma slGL_scalar_apply {K : Type} [Field K] {N : ℕ} {c : Kˣ}
    {s : Matrix.SpecialLinearGroup (Fin N) K}
    (hc : (s : Matrix (Fin N) (Fin N) K) = Matrix.scalar (Fin N) (c : K)) (v : Fin N → K) :
    (((slGL N K) s : LinearMap.GeneralLinearGroup K (Fin N → K)) :
        Module.End K (Fin N → K)) v = (c : K) • v := by
  have htoGL : Matrix.SpecialLinearGroup.toGL s = Matrix.GeneralLinearGroup.scalar (Fin N) c := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    exact hc
  change (↑(Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL s)) :
      (Fin N → K) →ₗ[K] (Fin N → K)) v = (c : K) • v
  rw [htoGL]
  exact CFSG.LocalAnalysis.GLTheoremA.CanonU3.toLin_scalar_apply c v

private lemma exists_ne_primaryFactor_of_primaryComponent_ne_top
    {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {x : Module.End K V} (hsq : Squarefree (minpoly K x))
    {h : Polynomial K} (hh : h ∈ primaryFactors x)
    (hproper : primaryComponent x h ≠ ⊤) :
    ∃ b : primaryFactors x, b ≠ ⟨h, hh⟩ := by
  by_contra hcon
  push Not at hcon
  have hsingle : primaryFactors x = {h} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hh, ?_⟩
    intro a ha
    exact congrArg Subtype.val (hcon ⟨a, ha⟩)
  have hmin : minpoly K x = h := by
    have hp := prod_primaryFactors (x := x) hsq
    rw [hsingle, Finset.prod_singleton] at hp
    exact hp.symm
  have hzero : Polynomial.aeval x h = 0 := by
    rw [← hmin]
    exact minpoly.aeval K x
  apply hproper
  change LinearMap.ker (Polynomial.aeval x h) = ⊤
  rw [hzero, LinearMap.ker_zero]

private lemma primaryComponent_ne_top_of_not_scalar
    {K : Type} [Field K] [Finite K] {N : ℕ}
    {d : GL (Fin N) K} {h : Polynomial K}
    (hN : 1 ≤ N)
    (hh : h ∈ primaryFactors (glA d : Module.End K (Fin N → K)))
    (hdeg : h.natDegree = 1)
    (hdns : d ∉ LargeEvenScalars (Fin N) K) :
    primaryComponent (glA d : Module.End K (Fin N → K)) h ≠ ⊤ := by
  intro htop
  obtain ⟨c, hc⟩ := CFSG.LocalAnalysis.GLTheoremA.CanonU3.exists_scalar_of_primaryComponent_eq_top
    (K := K) (n := N) hN (A := d) (a := ⟨h, hh⟩) hdeg htop
  exact hdns ⟨c, hc.symm⟩

private lemma scalar_mem_specialFactor_eq_one_of_ne_top
    {K : Type} [Field K] [Finite K] {N : ℕ}
    {d : GL (Fin N) K} {h : Polynomial K}
    (hh : h ∈ primaryFactors (glA d : Module.End K (Fin N → K)))
    (hsq : Squarefree (minpoly K (glA d : Module.End K (Fin N → K))))
    (hproper : primaryComponent (glA d : Module.End K (Fin N → K)) h ≠ ⊤)
    {s : Matrix.SpecialLinearGroup (Fin N) K}
    (hs : s ∈ specialFactor d h) (hscal : s ∈ LinearFlag.scalars N K) : s = 1 := by
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.mp hscal
  obtain ⟨b, hbne⟩ := exists_ne_primaryFactor_of_primaryComponent_ne_top hsq hh hproper
  have hbne' : (b : Polynomial K) ≠ h := fun e => hbne (Subtype.ext e)
  have hbnz : primaryComponent (glA d : Module.End K (Fin N → K)) (b : Polynomial K) ≠ ⊥ :=
    primaryComponent_ne_bot hsq b.2
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbnz
  have hsl : slGL N K s ∈ linearSpecialBlock (glA d) h := hs
  have hact : (((slGL N K) s : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K)) v = v :=
    (mem_linearSpecialBlock.mp hsl).2.1 b b.2 hbne' v hv
  have hcv : (c : K) • v = v := by
    rw [← slGL_scalar_apply (K := K) (N := N) (c := c) hc v]
    exact hact
  have hcK : (c : K) = 1 := by
    have hzero : ((c : K) - 1) • v = 0 := by
      rw [sub_smul, one_smul, hcv, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv0)
  have hc1 : c = 1 := Units.ext (by simpa using hcK)
  apply Subtype.ext
  show (s : Matrix (Fin N) (Fin N) K) = 1
  rw [hc, hc1, Units.val_one]
  exact map_one (Matrix.scalar (Fin N))

private lemma scalar_eq_one_of_mem_scalars_of_card_two
    {K : Type} [Field K] [Finite K] {N : ℕ} (hK2 : Nat.card K = 2)
    {s : Matrix.SpecialLinearGroup (Fin N) K}
    (hscal : s ∈ LinearFlag.scalars N K) : s = 1 := by
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.mp hscal
  have hcard : Nat.card Kˣ = 1 := by
    rw [Nat.card_units K, hK2]
  haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hcard).1
  have hc1 : c = 1 := Subsingleton.elim c 1
  apply Subtype.ext
  show (s : Matrix (Fin N) (Fin N) K) = 1
  rw [hc, hc1, Units.val_one]
  exact map_one (Matrix.scalar (Fin N))

private lemma card_map_specialFactor_proj_of_inj
    {K : Type} [Field K] {N : ℕ} {d : GL (Fin N) K} {h : Polynomial K}
    (hinj : ∀ s ∈ specialFactor d h, LinearFlag.proj N K s = 1 → s = 1) :
    Nat.card ↥((specialFactor d h).map (LinearFlag.proj N K)) =
      Nat.card ↥(specialFactor d h) := by
  let g : ↥(specialFactor d h) →* ↥((specialFactor d h).map (LinearFlag.proj N K)) :=
    (LinearFlag.proj N K).subgroupMap (specialFactor d h)
  have hg : Function.Injective g := by
    intro x y hxy
    have hxy' : (LinearFlag.proj N K) (x : Matrix.SpecialLinearGroup (Fin N) K) =
        (LinearFlag.proj N K) (y : Matrix.SpecialLinearGroup (Fin N) K) :=
      congrArg Subtype.val hxy
    have hscal : (x : Matrix.SpecialLinearGroup (Fin N) K)⁻¹ *
        (y : Matrix.SpecialLinearGroup (Fin N) K) ∈ LinearFlag.scalars N K :=
      (LinearFlag.proj_eq_proj_iff).mp hxy'
    have hmem : (x : Matrix.SpecialLinearGroup (Fin N) K)⁻¹ *
        (y : Matrix.SpecialLinearGroup (Fin N) K) ∈ specialFactor d h :=
      mul_mem (inv_mem x.2) y.2
    have hproj : (LinearFlag.proj N K) ((x : Matrix.SpecialLinearGroup (Fin N) K)⁻¹ *
        (y : Matrix.SpecialLinearGroup (Fin N) K)) = 1 :=
      (LinearFlag.proj_eq_one_iff).mpr hscal
    have heq : (x : Matrix.SpecialLinearGroup (Fin N) K)⁻¹ *
        (y : Matrix.SpecialLinearGroup (Fin N) K) = 1 := hinj _ hmem hproj
    have hyx : (y : Matrix.SpecialLinearGroup (Fin N) K) =
        (x : Matrix.SpecialLinearGroup (Fin N) K) := by
      have h := congrArg (fun w => (x : Matrix.SpecialLinearGroup (Fin N) K) * w) heq
      simpa using h
    exact Subtype.ext hyx.symm
  have hsurj : Function.Surjective g :=
    MonoidHom.subgroupMap_surjective (LinearFlag.proj N K) (specialFactor d h)
  exact (Nat.card_congr (MulEquiv.ofBijective g ⟨hg, hsurj⟩).toEquiv).symm

theorem linShape_block
    {K : Type} [Field K] [Finite K]
    {N : ℕ}
    {J' : Subgroup (PSLg N K)} (hchar : CharP K 2) (hN : 2 ≤ N)
    {d : GL (Fin N) K} (hd3 : d ^ 3 ∈ LargeEvenScalars (Fin N) K)
    (hdns : d ∉ LargeEvenScalars (Fin N) K)
    {h : Polynomial K} (hh : h ∈ primaryFactors (glA d : Module.End K (Fin N → K)))
    (hgood : IsGoodFactor d h)
    {e : PSLg N K ≃* LinearFlag.projectiveSL N K}
    (heJ : J' = Subgroup.comap e.toMonoidHom ((specialFactor d h).map (LinearFlag.proj N K)))
    {E : Type} [Field E] [Finite E] {m j : ℕ}
    (hm : m = primaryMultiplicity (glA d : Module.End K (Fin N → K)) h) (hj : j = h.natDegree)
    (hcardE : Nat.card E = Nat.card K ^ j) (hj2 : j = 2 → Nat.card K = 2)
    {f : Matrix.SpecialLinearGroup (Fin m) E →* ↥J'} (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center _) :
    m = 3 → (j = 1 ∧ 3 ∣ Nat.card K - 1 ∨ j = 2) →
      ∃ z : Matrix.SpecialLinearGroup (Fin m) E, z ∈ Subgroup.center _ ∧ f z ≠ 1 := by
  intro hm3 hjcase
  have hpk : (3 : K) ≠ 0 := by
    intro h
    have h23 : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp h
    omega
  obtain ⟨c3, hc3⟩ : ∃ c3 : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin N) c3 = d ^ 3 := by
    simpa [LargeEvenScalars, CFSG.Open.StatedScalars] using hd3
  have hsq : Squarefree (minpoly K (glA d : Module.End K (Fin N → K))) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.squarefree_minpoly_glA
      (k := K) (n := N) (p := 3) hpk (A := d) (c := c3) hc3.symm
  have hinj : ∀ s ∈ specialFactor d h, LinearFlag.proj N K s = 1 → s = 1 := by
    intro s hs hproj
    have hscal : s ∈ LinearFlag.scalars N K := (LinearFlag.proj_eq_one_iff).mp hproj
    by_cases hK2 : Nat.card K = 2
    · exact scalar_eq_one_of_mem_scalars_of_card_two (K := K) (N := N) hK2 hscal
    · have hj1 : j = 1 := by
        rcases hjcase with ⟨hj1, _⟩ | hj2'
        · exact hj1
        · exact absurd (hj2 hj2') hK2
      have hdeg : h.natDegree = 1 := by rw [← hj]; exact hj1
      exact scalar_mem_specialFactor_eq_one_of_ne_top (K := K) (N := N) (d := d) (h := h) hh hsq
        (primaryComponent_ne_top_of_not_scalar (K := K) (N := N) (by omega) hh hdeg hdns) hs hscal
  have hcard_map : Nat.card ↥((specialFactor d h).map (LinearFlag.proj N K)) =
      Nat.card ↥(specialFactor d h) :=
    card_map_specialFactor_proj_of_inj (K := K) (N := N) (d := d) (h := h) hinj
  have hIrr : Irreducible h := irreducible_of_mem_primaryFactors hh
  haveI : Fact (Irreducible h) := ⟨hIrr⟩
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hcard_adj : Nat.card (AdjoinRoot h) = Nat.card E := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, ← hj, ← hcardE]
  have hmpos : 1 ≤ m := by omega
  have hcard_SL : Nat.card (Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin m) E) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := AdjoinRoot h) (n := m) hmpos,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := E) (n := m) hmpos,
        hcard_adj]
  obtain ⟨eSF⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_mulEquiv_specialFactor
    (k := K) (n := N) (A := d) hsq hh
  rw [← hm] at eSF
  have hcard_sf : Nat.card ↥(specialFactor d h) =
      Nat.card (Matrix.SpecialLinearGroup (Fin m) E) := by
    calc Nat.card ↥(specialFactor d h)
        = Nat.card (Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h)) :=
          (Nat.card_congr eSF.toEquiv).symm
      _ = Nat.card (Matrix.SpecialLinearGroup (Fin m) E) := hcard_SL
  have hcomap : ∀ L' : Subgroup (LinearFlag.projectiveSL N K),
      Nat.card ↥(Subgroup.comap e.toMonoidHom L') = Nat.card ↥L' := by
    intro L'
    have hmap : Subgroup.comap e.toMonoidHom L' = L'.map e.symm.toMonoidHom := by
      ext x
      constructor
      · intro hx
        exact ⟨e x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [hmap, Subgroup.card_map_of_injective (K := L') (f := e.symm.toMonoidHom) e.symm.injective]
  have hcard_J' : Nat.card ↥J' = Nat.card (Matrix.SpecialLinearGroup (Fin m) E) := by
    rw [heJ, hcomap ((specialFactor d h).map (LinearFlag.proj N K)), hcard_map, hcard_sf]
  have hker_bot : f.ker = ⊥ := by
    have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr hf
    have hquot : Nat.card (Matrix.SpecialLinearGroup (Fin m) E ⧸ f.ker) = Nat.card ↥J' := by
      calc Nat.card (Matrix.SpecialLinearGroup (Fin m) E ⧸ f.ker)
          = Nat.card ↥f.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
        _ = Nat.card ↥(⊤ : Subgroup ↥J') := by rw [hrange]
        _ = Nat.card ↥J' := Subgroup.card_top
    have hformula := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have hquot' : Nat.card (Matrix.SpecialLinearGroup (Fin m) E ⧸ f.ker) =
        Nat.card (Matrix.SpecialLinearGroup (Fin m) E) := hquot.trans hcard_J'
    rw [hquot'] at hformula
    have hpos : 0 < Nat.card (Matrix.SpecialLinearGroup (Fin m) E) := Nat.card_pos
    have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin m) E) * 1 =
        Nat.card (Matrix.SpecialLinearGroup (Fin m) E) * Nat.card ↥f.ker := by
      rw [mul_one]
      exact hformula
    exact Subgroup.eq_bot_of_card_eq f.ker
      (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  have hinj_f : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker_bot
  have h3 : 3 ∣ Nat.card E - 1 := by
    rcases hjcase with ⟨hj1, h3K⟩ | hj2'
    · rw [hcardE, hj1, pow_one]; exact h3K
    · rw [hcardE, hj2', hj2 hj2']; norm_num
  have h3units : 3 ∣ Nat.card Eˣ := by
    rw [Nat.card_units E]; exact h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Eˣ, orderOf ω = 3 := exists_prime_orderOf_dvd_card' 3 h3units
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hωE3 : (ω : E) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  let z : Matrix.SpecialLinearGroup (Fin m) E :=
    ⟨Matrix.scalar (Fin m) (ω : E), by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.det_smul, Matrix.det_one,
        mul_one, Fintype.card_fin, hm3, hωE3]⟩
  have hzmat : (z : Matrix (Fin m) (Fin m) E) = (ω : E) • 1 := by
    show Matrix.scalar (Fin m) (ω : E) = (ω : E) • 1
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hzmem : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E) :=
    CFSG.LieType.SeitzGeneration.mem_center_of_scalar hzmat
  have hz1 : z ≠ 1 := by
    intro hz
    have hscal1 : Matrix.scalar (Fin m) (ω : E) = (1 : Matrix (Fin m) (Fin m) E) := by
      have h := congrArg (fun w : Matrix.SpecialLinearGroup (Fin m) E =>
        (w : Matrix (Fin m) (Fin m) E)) hz
      simpa [z] using h
    have hωE1 : (ω : E) = 1 := by
      let i : Fin m := ⟨0, hmpos⟩
      have hii := congrFun (congrFun hscal1 i) i
      simpa [Matrix.scalar_apply, Matrix.one_apply_eq] using hii
    have hω1 : ω = 1 := Units.ext hωE1
    rw [hω1, orderOf_one] at hω
    omega
  have hzf : f z ≠ 1 := by
    intro hfz
    exact hz1 (hinj_f (by simpa using hfz))
  exact ⟨z, hzmem, hzf⟩

end CFSG.StandardType.TablePThreeKG

end
