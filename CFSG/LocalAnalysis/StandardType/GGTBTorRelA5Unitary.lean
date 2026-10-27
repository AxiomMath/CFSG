module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5Model
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5HypModel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitC1
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Unitary
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrCore
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAKit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm211
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Certificate8026Base

@[expose] public section

namespace CFSG.StandardType.RelA5

open CFSG CFSG.Assembly CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial Matrix Multiplicative

theorem embP_eq_embPow {n : ℕ} {K : Type} [Field K] {p : ℕ} [Fact p.Prime] (ζ : muSplit n K)
    (hζ : ζ ^ p = 1) : embP ζ hζ = embPow ζ hζ :=
  rfl

theorem hypSmall_eq_one_of_mem_center {n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) {F : (Fin 3 → muSplit n K) →* hypSU h 3 0}
    (hF : ∀ z, (((F z : hypSU h 3 0) : GL (HypIndex 3 0) K) :
      Matrix (HypIndex 3 0) (HypIndex 3 0) K) =
        diagonal (torusEntries h (fun i => ((z i : muSplit n K) : Kˣ)) (Fin.elim0)))
    (z : Fin 3 → muSplit n K) (hz : F z ∈ Subgroup.center (hypSU h 3 0)) : z = 1 := by
  have : CharP K 2 := h.charP
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.center_hypSU_eq_hypScalars_of_three_le h
    (ε := 0) (s := 3) (by norm_num) (by norm_num)
    (by simp only [ne_eq, Prod.mk.injEq]; omega)] at hz
  obtain ⟨c, -, -, hzc⟩ := hz
  have hmat : diagonal (torusEntries h (fun i => ((z i : muSplit n K) : Kˣ)) (Fin.elim0)) =
      diagonal (fun _ => (c : K)) := by
    rw [← hF z, hzc, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  funext i
  have h1 := congrFun (Matrix.diagonal_injective hmat) (.inl i)
  have h2 := congrFun (Matrix.diagonal_injective hmat) (.inr (.inr i))
  simp only [torusEntries] at h1 h2
  rw [bar_eq_of_mem_muSplit h (z i).2, ← h1] at h2
  have hz0 : ((z i : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hsq : ((z i : Kˣ) : K) * ((z i : Kˣ) : K) = 1 := by
    have := congrArg (fun x : K => x * ((z i : Kˣ) : K)) h2
    simpa [inv_mul_cancel₀ hz0] using this.symm
  have hz1 : ((z i : Kˣ) : K) = 1 := by
    have h3 : (((z i : Kˣ) : K) - 1) * (((z i : Kˣ) : K) - 1) = 0 := by
      have h4 : (((z i : Kˣ) : K) - 1) * (((z i : Kˣ) : K) - 1) =
          ((z i : Kˣ) : K) * ((z i : Kˣ) : K) - 1 - 2 * ((z i : Kˣ) : K) + 2 := by ring
      rw [h4, hsq, CharTwo.two_eq_zero, zero_mul, sub_self, sub_zero, add_zero]
    have := mul_self_eq_zero.mp h3
    exact sub_eq_zero.mp this
  exact Subtype.ext (Units.ext hz1)

theorem ggTorusTorW_relA5_unitary
    {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) :
    GGTorusTorW p 3 (2 ^ n - 1) 3 (CartanMatrix.C 3) (CoxeterMatrix.B 3)
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  classical
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, -⟩ := hTB
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq4 : 4 ≤ 2 ^ n := four_le_two_pow_of_dvd_sub_one hp hp2 hn hpq
  have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  have h : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have : CharP K 2 := h.charP
  have : Finite (LargeEvenSUGroup (Fin 6) K (2 ^ n)) := Finite.of_injective
    (fun x : LargeEvenSUGroup (Fin 6) K (2 ^ n) =>
      ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  obtain ⟨φc, hφcs, hφc⟩ := exists_cover_of_sections
    (QuotientGroup.mk' ((LargeEvenScalars (Fin 6) K).subgroupOf
      (LargeEvenSUGroup (Fin 6) K (2 ^ n))))
    (QuotientGroup.mk'_surjective _)
    (fun E _ _ π hπ hcen =>
      CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central hK
        (by decide : Even 6) (by norm_num) hq4 hπ hcen)
    ψ hψ hker hperf
  obtain ⟨Rm, hR⟩ := exists_isHypTransport (r := 3) (ε := 0) h
  let Θ : hypSU h 3 0 ≃* LargeEvenSUGroup (Fin 6) K (2 ^ n) := hypTransport h hR
  let Φ₀ : hypSU h 3 0 →* L' := φc.comp Θ.toMonoidHom
  have hΦ₀s : Function.Surjective Φ₀ := hφcs.comp Θ.surjective
  have hcenΘ : ∀ x : hypSU h 3 0, Θ x ∈ Subgroup.center (LargeEvenSUGroup (Fin 6) K (2 ^ n)) →
      x ∈ Subgroup.center (hypSU h 3 0) := by
    intro x hx
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    apply Θ.injective
    rw [map_mul, map_mul, hx (Θ y)]
  have hΦ₀ker : Φ₀.ker ≤ Subgroup.center (hypSU h 3 0) := by
    intro x hx
    apply hcenΘ
    have h1 : ψ (φc (Θ x)) = 1 := by
      have : φc (Θ x) = 1 := hx
      rw [this, map_one]
    rw [hφc] at h1
    exact scalars_le_center_statedSU ((QuotientGroup.eq_one_iff _).mp h1)
  have hHperf : commutator (hypSU h 3 0) = ⊤ := by
    have hS : commutator (LargeEvenSUGroup (Fin 6) K (2 ^ n)) = ⊤ :=
      (CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU (F := K) (p := 2) (f := n)
        hK (n := 6) (by norm_num)).commutator_eq_top
    have hsurj : Function.Surjective Θ.symm.toMonoidHom := Θ.symm.surjective
    rw [_root_.commutator_def, ← Subgroup.map_top_of_surjective _ hsurj,
      ← Subgroup.map_commutator, ← _root_.commutator_def, hS]
  have hZcard : Nat.card (Subgroup.center (hypSU h 3 0)) ∣ 2 ^ n + 1 := by
    have h1 : Nat.card (Subgroup.center (hypSU h 3 0)) =
        Nat.card (Subgroup.center (LargeEvenSUGroup (Fin 6) K (2 ^ n))) := by
      rw [← Subgroup.map_center_eq Θ]
      exact (Nat.card_congr ((Subgroup.center (hypSU h 3 0)).equivMapOfInjective
        Θ.toMonoidHom Θ.injective).toEquiv)
    rw [h1]
    exact card_center_statedSU_dvd hK (by norm_num)
  have hZp : ¬ p ∣ Nat.card (Subgroup.center (hypSU h 3 0)) := fun hd => hpq' (hd.trans hZcard)
  have hZm : Nat.Coprime (2 ^ n - 1) (Nat.card (Subgroup.center (hypSU h 3 0))) := by
    refine Nat.Coprime.coprime_dvd_right hZcard ?_
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : (2 ^ n + 1) = (2 ^ n - 1) + 2 := by omega
    rw [h2, Nat.coprime_self_add_right, Nat.coprime_two_right]
    exact Nat.Even.sub_odd h1 (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hZscal : ∀ z ∈ Subgroup.center (hypSU h 3 0), z ∈ hypScalars h 3 0 := by
    intro z hz
    rwa [CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.center_hypSU_eq_hypScalars_of_three_le h (ε := 0) (s := 3) (by norm_num) (by norm_num)
      (by simp only [ne_eq, Prod.mk.injEq]; omega)] at hz
  have hIp := NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd (d := 6) hK hn (by norm_num)
    (by omega) hp hpq'
  have hinn : ∀ a ∈ A, ∃ l : L', a = MulAut.conj l := by
    intro a ha
    obtain ⟨x, hxI, hx⟩ := hAI a ha
    have hxp : x ^ p = 1 := by
      have hap : a ^ p = 1 := hAe.2 a ha
      ext r
      obtain ⟨l, rfl⟩ := hψ r
      have hpow : ∀ k : ℕ, (x ^ k) (ψ l) = ψ ((a ^ k) l) := by
        intro k
        induction k generalizing l with
        | zero => rfl
        | succ k ih =>
          rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hx, ih]
      rw [hpow p, hap, MulAut.one_apply, MulAut.one_apply]
    obtain ⟨r, hr⟩ := hIp x hxI hxp
    obtain ⟨l, -, hl⟩ := exists_eq_conj_of_induced hψ hker hperf (a := a) (r := r) (fun l => by
      rw [← hx l, ← hr, MulAut.conj_apply])
    exact ⟨l, hl⟩
  obtain ⟨E₀, hE₀, hcardE₀, hAE₀, hE₀mem⟩ :=
    exists_elemAbelian_lift hp hHperf hΦ₀s hΦ₀ker hZp hAe hinn
  obtain ⟨ζ, hζ⟩ := exists_zeta_muSplit (n := n) (K := K) hK hpq
  have hζK : IsPrimitiveRoot ((ζ : Kˣ) : K) p := isPrimitiveRoot_coe hζ
  have h3' : p ^ 3 ≤ Nat.card E₀ := by rw [hcardE₀]; exact h3
  obtain ⟨g, hg⟩ := exists_conj_hypEntries h hp hp2 hpq hζK (by norm_num) E₀ hE₀ h3'
  obtain ⟨F, hF⟩ := exists_hypSmall h
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hgE : ∀ x ∈ E₀, ∃ f, g * x * g⁻¹ = F (embPow ζ hζp f) := by
    intro x hx
    obtain ⟨t, ht⟩ := hg x hx
    refine ⟨fun i => ofAdd (t i), ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [ht, ← embP_eq_embPow, hypSmall_embP h hF hζp]
    rfl
  let D : Subgroup (hypSU h 3 0) := ((embPow ζ hζp).range).map F
  have hDrange : D = (F.comp (embPow ζ hζp)).range := by
    rw [MonoidHom.range_comp]
  have hinjD : Function.Injective (F.comp (embPow ζ hζp)) :=
    (hypSmall_injective h F hF).comp (embPow_injective hζ)
  have hD_card : Nat.card D = p ^ 3 := by
    rw [hDrange, ← Nat.card_congr (MonoidHom.ofInjective hinjD).toEquiv]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have hE₀D : E₀.map (MulAut.conj g).toMonoidHom = D := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨f, hf⟩ := hgE x hx
      exact ⟨embPow ζ hζp f, ⟨f, rfl⟩, hf.symm⟩
    · rw [hD_card, Nat.card_congr ((E₀.equivMapOfInjective _
        (MulAut.conj g).injective).toEquiv.symm)]
      exact h3'
  let Φ : hypSU h 3 0 →* L' := Φ₀.comp (MulAut.conj g⁻¹).toMonoidHom
  have hΦs : Function.Surjective Φ := hΦ₀s.comp (MulAut.conj g⁻¹).surjective
  have hΦker : Φ.ker ≤ Subgroup.center (hypSU h 3 0) := by
    intro x hx
    have h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ Subgroup.center (hypSU h 3 0) := hΦ₀ker hx
    have h2 : x = g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ := by group
    rw [h2]
    exact (inferInstance : (Subgroup.center (hypSU h 3 0)).Normal).conj_mem _ h1 g
  have hDΦ : D.map Φ = E₀.map Φ₀ := by
    rw [← hE₀D, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    simp only [Φ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    congr 1
    group
  have hA' : A = (D.map Φ).map MulAut.conj := by
    rw [hDΦ]
    exact hAE₀
  have hmodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have : Finite (muSplit n K) := Finite.of_injective (fun x : muSplit n K => (x : Kˣ))
    Subtype.val_injective
  have : IsCyclic (muSplit n K) := subgroup_units_cyclic _
  have : NeZero (2 ^ n - 1) := ⟨by have := hmodd.pos; omega⟩
  let l : muSplit n K ≃* Multiplicative (ZMod (2 ^ n - 1)) :=
    mulEquivOfCyclicCardEq (by
      rw [card_muSplit hK, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  have hμ : ∀ x : muSplit n K, x ^ (2 ^ n - 1) = 1 := fun x =>
    Subtype.ext ((mem_rootsOfUnity _ _).mp x.2)
  have hZT : Subgroup.center (hypSU h 3 0) ≤ hypTorus h 3 0 := by
    intro z hz
    obtain ⟨c, -, -, hzc⟩ := hZscal z hz
    refine mem_hypTorus_of_scalar h z (c := (c : K)) ?_
    rw [hzc, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  obtain ⟨w, hw⟩ := exists_hypWeyl h F hF
  have hpt : ∀ z : Fin 3 → muSplit n K, (∀ i, z i ^ p = 1) →
      z ∈ (embPow ζ hζ.pow_eq_one).range := fun z hz => by
    rw [← embP_eq_embPow]
    exact (mem_range_embP_iff hζ z).mpr hz
  have hι : ∀ f, (((F.comp (embPow ζ hζp) f : hypSU h 3 0) : GL (HypIndex 3 0) K) :
      Matrix (HypIndex 3 0) (HypIndex 3 0) K) =
        diagonal (hypEntries ((ζ : Kˣ) : K) (fun i => toAdd (f i))) := fun f => by
    rw [MonoidHom.comp_apply, ← embP_eq_embPow]
    exact hypSmall_embP h hF hζp f
  exact ggTorusTorData_of_relA5Model hp2 hmodd Φ hΦs hΦker hHperf hZp hZm l hμ F
    (hypSmall_eq_one_of_mem_center h hF) (hypTorus h 3 0)
    (fun x hx y hy => hypTorus_commute h hx hy) (hypSmall_mem_hypTorus h F hF)
    (fun t ht htm => exists_eq_hypSmall_of_pow h F hF ht htm) hZT
    (mem_hypTorus_of_commute h F hF hp hp2 hpq) w hw ζ hζ hpt
    (fun x hx => ggKGUc_normalizer h hp ((ζ : Kˣ) : K) hζK (F.comp (embPow ζ hζp)) hι x hx) hA'

end CFSG.StandardType.RelA5
