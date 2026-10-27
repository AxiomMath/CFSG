module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.LocalAnalysis.StandardType.GGK1ALift
public import CFSG.LocalAnalysis.StandardType.GGK1AMult
public import CFSG.LocalAnalysis.StandardType.GGK1ABlocks
public import CFSG.LocalAnalysis.StandardType.GGK1AKind
public import CFSG.LocalAnalysis.StandardType.GGK1ANoglue
public import CFSG.LocalAnalysis.StandardType.GGK1ATransport
public import CFSG.LocalAnalysis.StandardType.GGK1ADvd
public import CFSG.LocalAnalysis.StandardType.GGK1ACenter
public import CFSG.LocalAnalysis.StandardType.GGK1AValid
public import CFSG.LocalAnalysis.StandardType.GGK1ASigma
public import CFSG.LocalAnalysis.StandardType.GGK1ABlocksLin
public import CFSG.LocalAnalysis.StandardType.GGK1ABlocksUni

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldLang

private theorem ggK1Ao_one_le_of_card_eq_two_pow {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) : 1 ≤ n := by
  by_contra h
  have hn : n = 0 := by omega
  subst hn
  rw [pow_zero] at hK
  have h1 := Finite.one_lt_card (α := K)
  omega

private theorem ggK1Ao_one_le_of_card_eq_sq {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) : 1 ≤ n := by
  by_contra h
  have hn : n = 0 := by omega
  subst hn
  rw [pow_zero, one_pow] at hK
  have h1 := Finite.one_lt_card (α := K)
  omega

private theorem ggK1Ao_not_dvd_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 2 :=
  fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

private theorem ggK1Ao_dvd_two_mul {p n : ℕ}
    (h : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    p ∣ 2 ^ (2 * n) - 1 ∨ p ∣ 2 ^ (2 * n) + 1 := by
  left
  have h2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by ring, pow_mul]
  have hsq : 2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    rw [h2, ← one_pow 2, Nat.sq_sub_sq]
    exact Nat.mul_comm _ _
  rw [hsq]
  rcases h with h | h
  · exact h.mul_right _
  · exact h.mul_left _

private theorem ggK1Ao_comps_mono {nfC nfB : ℕ} {D : GGKacDatum} {R : Type} [Group R]
    {φ : MulAut R} (hdiv : nfC ∣ nfB) (h : GGK1Comps nfB D R φ) :
    GGK1Comps nfC D R φ := by
  refine ⟨?_, h.2⟩
  rintro J hJ
  obtain ⟨o, ho, hqs, hdvd, hlab, hlabel⟩ := h.1 J hJ
  exact ⟨o, ho, hqs, hdiv.trans hdvd, hlab, hlabel⟩

private theorem ggK1A_bij_aux {D : GGKacDatum} {R : Type} [Group R] {e : MulAut R} {Q : Type}
    (compSub : Q → Subgroup R)
    (hcomp : ∀ i, CFSG.Assembly.IsComponentOf (compSub i) (ggFixSub e))
    (hinj : Function.Injective compSub)
    (hsurj : ∀ J, CFSG.Assembly.IsComponentOf J (ggFixSub e) → ∃ i, compSub i = J)
    (g : Q ≃ {k : Fin D.orbits.length // D.orbits[k].qs = true}) (blk : Q → GGKacOrbit)
    (hg : ∀ i, D.orbits[(g i).1] = blk i)
    (hlab : ∀ i, GGHasLabel (blk i).lab (↥(compSub i) ⧸ Subgroup.center ↥(compSub i))) :
    GGKacCompBij D R e := by
  let c : Q → {J : Subgroup R // CFSG.Assembly.IsComponentOf J (ggFixSub e)} :=
    fun i => ⟨compSub i, hcomp i⟩
  have hc : Function.Bijective c := by
    refine ⟨fun i j hij => hinj (congrArg Subtype.val hij), ?_⟩
    rintro ⟨J, hJ⟩
    obtain ⟨i, hi⟩ := hsurj J hJ
    exact ⟨i, Subtype.ext hi⟩
  let e' := Equiv.ofBijective c hc
  refine ⟨e'.symm.trans g, fun J => ?_⟩
  have hJ : J.1 = compSub (e'.symm J) := (congrArg Subtype.val (e'.apply_symm_apply J)).symm
  have hpos : D.orbits[((e'.symm.trans g) J).1] = blk (e'.symm J) := hg (e'.symm J)
  have transport : ∀ (lab : LargeEvenLabel) (X Y : Subgroup R), X = Y →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → GGHasLabel lab (↥Y ⧸ Subgroup.center ↥Y) := by
    intro lab X Y h
    subst h
    exact id
  rw [hpos]
  exact transport _ _ _ hJ.symm (hlab (e'.symm J))

theorem ggK1A_core_comp {p nf : ℕ} {tw : Bool} {m : List ℕ} {R : Type} [Group R] {x : R}
    (hnf : 1 ≤ nf) (F : ggK1ACo_Family p R x (ggMultDatumA p nf (ggMultOrd p nf) tw m)) :
    GGK1Comps nf (ggMultDatumA p nf (ggMultOrd p nf) tw m) R (MulAut.conj x) := by
  refine ⟨?_, ?_⟩
  · intro J hJ
    obtain ⟨i, hq, hJeq⟩ := F.hcomp J hJ
    rw [hJeq]
    have hqs := F.hqs i hq
    obtain ⟨hdvdn, hlam⟩ := ggK1ACo_orbit_arith hnf (F.hmem i hq) hqs
    exact ⟨F.blk i, F.hmem i hq, hqs, hdvdn, hlam, F.hlab i hq⟩
  · intro o ho hqs
    obtain ⟨i, hq, hi⟩ := F.hreal o ho hqs
    refine ⟨F.A i, F.hfactor i hq, ?_⟩
    rw [← hi]
    exact F.hlab i hq

theorem ggK1A_core_bij {p nf : ℕ} {tw : Bool} {m : List ℕ} {R : Type} [Group R] {x : R}
    (F : ggK1ACo_Family p R x (ggMultDatumA p nf (ggMultOrd p nf) tw m)) :
    GGKacCompBij (ggMultDatumA p nf (ggMultOrd p nf) tw m) R (MulAut.conj x) := by
  obtain ⟨g, hg⟩ := F.hbij
  refine ggK1A_bij_aux (fun i : {i : F.ι // CFSG.IsQuasisimple ↥(F.A i)} => F.A i.1)
    (fun i => F.hfactor i.1 i.2)
    (fun i j hij => Subtype.ext (ggK1ACo_component_inj F i.2 j.2 hij))
    (fun J hJ => by
      obtain ⟨i, hq, hJeq⟩ := F.hcomp J hJ
      exact ⟨⟨i, hq⟩, hJeq.symm⟩)
    g (fun i => F.blk i.1) hg (fun i => F.hlab i.1 i.2)

theorem ggK1A_core_A {p n r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) (hnotRA : ¬ (p ∣ r + 1 ∧ p ∣ 2 ^ n - 1))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n) :
    GGK1Core GGMultValidCl p ⟨.A, r, n⟩
      (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K))
        (Set.univ : Set (GL (Fin (r + 1)) K))) := by
  intro φ hφ hφp
  have hn : 1 ≤ n := ggK1Ao_one_le_of_card_eq_two_pow hK
  obtain ⟨xhat, hxp, hconj⟩ :=
    ggK1A_exists_lift (p := p) (nf := n) (N := r + 1) hp hK hnotRA φ hφ hφp
  obtain ⟨m, hm⟩ := ggK1A_mult_exists (p := p) (nf := n) (N := r + 1) hp hp2 hK hdvd hxp
  obtain ⟨B⟩ := ggK1ACo_blocks_exists (p := p) (nf := n) (N := r + 1) hp hp2 hn hK hdvd hxp hm
  have hnoglue := ggK1A_noglue (p := p) (nf := n) (N := r + 1) hp hp2 hn hK hnotRA hxp
  let Z0 := (LargeEvenScalars (Fin (r + 1)) K).subgroupOf (LargeEvenSLGroup (Fin (r + 1)) K)
  have hπ : Function.Surjective (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K)) :=
    QuotientGroup.mk'_surjective Z0
  have hker : (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K)).ker ≤
      Subgroup.center ↥(LargeEvenSLGroup (Fin (r + 1)) K) := by
    rw [show (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K)).ker = Z0 from
      QuotientGroup.ker_mk' _]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  obtain ⟨F⟩ := ggK1A_transport (p := p) (nf := n) (N := r + 1) (tw := false)
    (xhat := xhat) (m := m)
    (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K)) hπ hker hnoglue B
  refine ⟨ggMultDatumA p n (ggMultOrd p n) false m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ggK1A_core_valid (p := p) (nf := n) (N := r + 1) (d := ggMultOrd p n)
      hm hdvd rfl rfl
  · have hcomp : GGK1Comps n (ggMultDatumA p n (ggMultOrd p n) false m)
        (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K)) φ := by
      rw [← hconj]
      exact ggK1A_core_comp (p := p) (nf := n) (tw := false) hn F
    exact hcomp
  · rw [← hconj]
    exact ggK1A_core_dvd (p := p) (nf := n) (N := r + 1) (d := ggMultOrd p n)
      hp hp2 hn hK hdvd rfl hxp hm
  · rw [← hconj]
    exact ggK1A_core_center (p := p) (nf := n) (N := r + 1) (d := ggMultOrd p n)
      hp hp2 hn hK hdvd hnotRA rfl hxp hm
  · rw [← hconj]
    exact ggK1A_core_bij (p := p) (nf := n) (tw := false) F
  · rw [← hconj]
    exact ggK1A_core_sigma (p := p) (nf := n) (N := r + 1) hp hdvd hK hxp hm

theorem ggK1A_core_D3 {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) (hnotRA : ¬ (p ∣ 4 ∧ p ∣ 2 ^ n - 1))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n) :
    GGK1Core GGMultValidCl p ⟨.D, 3, n⟩
      (LargeEvenProj (LargeEvenSLGroup (Fin 4) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) K))
        (Set.univ : Set (GL (Fin 4) K))) := by
  intro φ hφ hφp
  have hn : 1 ≤ n := ggK1Ao_one_le_of_card_eq_two_pow hK
  obtain ⟨xhat, hxp, hconj⟩ :=
    ggK1A_exists_lift (p := p) (nf := n) (N := 4) hp hK hnotRA φ hφ hφp
  obtain ⟨m, hm⟩ := ggK1A_mult_exists (p := p) (nf := n) (N := 4) hp hp2 hK hdvd hxp
  obtain ⟨B⟩ := ggK1ACo_blocks_exists (p := p) (nf := n) (N := 4) hp hp2 hn hK hdvd hxp hm
  have hnoglue := ggK1A_noglue (p := p) (nf := n) (N := 4) hp hp2 hn hK hnotRA hxp
  let Z0 := (LargeEvenScalars (Fin 4) K).subgroupOf (LargeEvenSLGroup (Fin 4) K)
  have hπ : Function.Surjective (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) K)) :=
    QuotientGroup.mk'_surjective Z0
  have hker : (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) K)).ker ≤
      Subgroup.center ↥(LargeEvenSLGroup (Fin 4) K) := by
    rw [show (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) K)).ker = Z0 from
      QuotientGroup.ker_mk' _]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  obtain ⟨F⟩ := ggK1A_transport (p := p) (nf := n) (N := 4) (tw := false)
    (xhat := xhat) (m := m)
    (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) K)) hπ hker hnoglue B
  refine ⟨ggMultDatumA p n (ggMultOrd p n) false m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ggK1A_core_valid_D3 (p := p) (nf := n) (N := 4) (d := ggMultOrd p n)
      hm hdvd rfl rfl
  · have hcomp : GGK1Comps n (ggMultDatumA p n (ggMultOrd p n) false m)
        (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) φ := by
      rw [← hconj]
      exact ggK1A_core_comp (p := p) (nf := n) (tw := false) hn F
    exact hcomp
  · rw [← hconj]
    exact ggK1A_core_dvd (p := p) (nf := n) (N := 4) (d := ggMultOrd p n)
      hp hp2 hn hK hdvd rfl hxp hm
  · rw [← hconj]
    exact ggK1A_core_center (p := p) (nf := n) (N := 4) (d := ggMultOrd p n)
      hp hp2 hn hK hdvd hnotRA rfl hxp hm
  · rw [← hconj]
    exact ggK1A_core_bij (p := p) (nf := n) (tw := false) F
  · rw [← hconj]
    exact ggK1A_core_sigma (p := p) (nf := n) (N := 4) hp hdvd hK hxp hm

theorem ggK1A_core_twD2 {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) (hnotRA : ¬ (p ∣ 2 ∧ p ∣ (2 ^ n) ^ 2 - 1))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGK1Core GGMultValidCl p ⟨.twD, 2, n⟩
      (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K))
        (Set.univ : Set (GL (Fin 2) K))) := by
  intro φ hφ hφp
  have hn : 1 ≤ n := ggK1Ao_one_le_of_card_eq_sq hK
  have hnf : 1 ≤ 2 * n := by omega
  have hK' : Nat.card K = 2 ^ (2 * n) := by
    rw [hK, show 2 * n = n * 2 by ring, pow_mul]
  have hdvd' : p ∣ 2 ^ (2 * n) - 1 ∨ p ∣ 2 ^ (2 * n) + 1 := ggK1Ao_dvd_two_mul hdvd
  have hnotRA' : ¬ (p ∣ 2 ∧ p ∣ 2 ^ (2 * n) - 1) :=
    fun h => ggK1Ao_not_dvd_two hp hp2 h.1
  obtain ⟨xhat, hxp, hconj⟩ :=
    ggK1A_exists_lift (p := p) (nf := 2 * n) (N := 2) hp hK' hnotRA' φ hφ hφp
  obtain ⟨m, hm⟩ := ggK1A_mult_exists (p := p) (nf := 2 * n) (N := 2) hp hp2 hK' hdvd' hxp
  obtain ⟨B⟩ := ggK1ACo_blocks_exists (p := p) (nf := 2 * n) (N := 2) hp hp2 hnf hK' hdvd' hxp hm
  have hnoglue := ggK1A_noglue (p := p) (nf := 2 * n) (N := 2) hp hp2 hnf hK' hnotRA' hxp
  let Z0 := (LargeEvenScalars (Fin 2) K).subgroupOf (LargeEvenSLGroup (Fin 2) K)
  have hπ : Function.Surjective (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) :=
    QuotientGroup.mk'_surjective Z0
  have hker : (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)).ker ≤
      Subgroup.center ↥(LargeEvenSLGroup (Fin 2) K) := by
    rw [show (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)).ker = Z0 from
      QuotientGroup.ker_mk' _]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  obtain ⟨F⟩ := ggK1A_transport (p := p) (nf := 2 * n) (N := 2) (tw := false)
    (xhat := xhat) (m := m)
    (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) hπ hker hnoglue B
  refine ⟨ggMultDatumA p (2 * n) (ggMultOrd p (2 * n)) false m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ggK1A_core_valid_twD2 (p := p) (n := n) (N := 2) (d := ggMultOrd p (2 * n))
      hm hdvd rfl rfl
  · have hcomp : GGK1Comps (2 * n) (ggMultDatumA p (2 * n) (ggMultOrd p (2 * n)) false m)
        (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) φ := by
      rw [← hconj]
      exact ggK1A_core_comp (p := p) (nf := 2 * n) (tw := false) hnf F
    exact ggK1Ao_comps_mono (dvd_mul_left n 2) hcomp
  · rw [← hconj]
    exact ggK1A_core_dvd (p := p) (nf := 2 * n) (N := 2) (d := ggMultOrd p (2 * n))
      hp hp2 hnf hK' hdvd' rfl hxp hm
  · rw [← hconj]
    exact ggK1A_core_center (p := p) (nf := 2 * n) (N := 2) (d := ggMultOrd p (2 * n))
      hp hp2 hnf hK' hdvd' hnotRA' rfl hxp hm
  · rw [← hconj]
    exact ggK1A_core_bij (p := p) (nf := 2 * n) (tw := false) F
  · rw [← hconj]
    exact ggK1A_core_sigma (p := p) (nf := 2 * n) (N := 2) hp hdvd' hK' hxp hm

theorem ggK1A_core_twA {p n r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) (hnotRAu : ¬ (p ∣ r + 1 ∧ p ∣ 2 ^ n + 1))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGK1Core GGMultValidCl p ⟨.twA, r, n⟩
      (LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n)))
        (LargeEvenGUSet (Fin (r + 1)) K (2 ^ n))) := by
  intro φ hφ hφp
  have hn : 1 ≤ n := ggK1Ao_one_le_of_card_eq_sq hK
  obtain ⟨xhat, hxp, hconj⟩ :=
    ggK1A_uni_exists_lift (p := p) (nf := n) (N := r + 1) hp hdvd hK hnotRAu φ hφ hφp
  obtain ⟨m, hm⟩ := ggK1A_uni_mult_exists (p := p) (nf := n) (N := r + 1) hp hp2 hK hdvd hxp
  obtain ⟨B⟩ := ggK1ACo_uni_blocks_exists (p := p) (nf := n) (N := r + 1) hp hp2 hn hK hdvd hxp hm
  have hnoglue := ggK1A_uni_noglue (p := p) (nf := n) (N := r + 1) hp hp2 hn hK hnotRAu hxp
  let Z0 := (LargeEvenScalars (Fin (r + 1)) K).subgroupOf
    (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n))
  have hπ : Function.Surjective (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n))) :=
    QuotientGroup.mk'_surjective Z0
  have hker : (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n))).ker ≤
      Subgroup.center ↥(LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n)) := by
    rw [show (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n))).ker = Z0 from
      QuotientGroup.ker_mk' _]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  obtain ⟨F⟩ := ggK1A_transport (p := p) (nf := n) (N := r + 1) (tw := true)
    (xhat := xhat) (m := m)
    (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n))) hπ hker hnoglue B
  refine ⟨ggMultDatumA p n (ggMultOrd p n) true m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ggK1A_uni_core_valid (p := p) (nf := n) (N := r + 1) (d := ggMultOrd p n)
      hm hdvd rfl rfl
  · have hcomp : GGK1Comps n (ggMultDatumA p n (ggMultOrd p n) true m)
        (LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n))) φ := by
      rw [← hconj]
      exact ggK1A_core_comp (p := p) (nf := n) (tw := true) hn F
    exact hcomp
  · rw [← hconj]
    exact ggK1A_uni_core_dvd (p := p) (nf := n) (N := r + 1) (d := ggMultOrd p n)
      hp hp2 hn hK hdvd rfl hxp hm
  · rw [← hconj]
    exact ggK1A_uni_core_center (p := p) (nf := n) (N := r + 1) (d := ggMultOrd p n)
      hp hp2 hn hK hdvd hnotRAu rfl hxp hm
  · rw [← hconj]
    exact ggK1A_core_bij (p := p) (nf := n) (tw := true) F
  · rw [← hconj]
    exact ggK1A_uni_core_sigma (p := p) (nf := n) (N := r + 1) hp hdvd hK hnotRAu hxp hm

theorem ggK1A_core_twD3 {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) (hnotRAu : ¬ (p ∣ 4 ∧ p ∣ 2 ^ n + 1))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGK1Core GGMultValidCl p ⟨.twD, 3, n⟩
      (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
        (LargeEvenGUSet (Fin 4) K (2 ^ n))) := by
  intro φ hφ hφp
  have hn : 1 ≤ n := ggK1Ao_one_le_of_card_eq_sq hK
  obtain ⟨xhat, hxp, hconj⟩ :=
    ggK1A_uni_exists_lift (p := p) (nf := n) (N := 4) hp hdvd hK hnotRAu φ hφ hφp
  obtain ⟨m, hm⟩ := ggK1A_uni_mult_exists (p := p) (nf := n) (N := 4) hp hp2 hK hdvd hxp
  obtain ⟨B⟩ := ggK1ACo_uni_blocks_exists (p := p) (nf := n) (N := 4) hp hp2 hn hK hdvd hxp hm
  have hnoglue := ggK1A_uni_noglue (p := p) (nf := n) (N := 4) hp hp2 hn hK hnotRAu hxp
  let Z0 := (LargeEvenScalars (Fin 4) K).subgroupOf (LargeEvenSUGroup (Fin 4) K (2 ^ n))
  have hπ : Function.Surjective (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n))) :=
    QuotientGroup.mk'_surjective Z0
  have hker : (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n))).ker ≤
      Subgroup.center ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) := by
    rw [show (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n))).ker = Z0 from
      QuotientGroup.ker_mk' _]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  obtain ⟨F⟩ := ggK1A_transport (p := p) (nf := n) (N := 4) (tw := true)
    (xhat := xhat) (m := m)
    (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n))) hπ hker hnoglue B
  refine ⟨ggMultDatumA p n (ggMultOrd p n) true m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ggK1A_uni_core_valid_twD3 (p := p) (nf := n) (N := 4) (d := ggMultOrd p n)
      hm hdvd rfl rfl
  · have hcomp : GGK1Comps n (ggMultDatumA p n (ggMultOrd p n) true m)
        (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) φ := by
      rw [← hconj]
      exact ggK1A_core_comp (p := p) (nf := n) (tw := true) hn F
    exact hcomp
  · rw [← hconj]
    exact ggK1A_uni_core_dvd (p := p) (nf := n) (N := 4) (d := ggMultOrd p n)
      hp hp2 hn hK hdvd rfl hxp hm
  · rw [← hconj]
    exact ggK1A_uni_core_center (p := p) (nf := n) (N := 4) (d := ggMultOrd p n)
      hp hp2 hn hK hdvd hnotRAu rfl hxp hm
  · rw [← hconj]
    exact ggK1A_core_bij (p := p) (nf := n) (tw := true) F
  · rw [← hconj]
    exact ggK1A_uni_core_sigma (p := p) (nf := n) (N := 4) hp hdvd hK hnotRAu hxp hm

end CFSG.StandardType

end
