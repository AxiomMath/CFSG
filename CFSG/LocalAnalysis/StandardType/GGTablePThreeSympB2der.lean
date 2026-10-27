module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplit
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section SympB2derAux

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

private abbrev sympB2derCarrier (K : Type) [Field K] : Subgroup (GL (Fin 2 ⊕ Fin 2) K) :=
  ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆

private theorem sympB2der_conj_mem {K : Type} [Field K]
    {g : GL (Fin 2 ⊕ Fin 2) K} (hg : g ∈ LargeEvenSpGroup K 2)
    {h : GL (Fin 2 ⊕ Fin 2) K} (hh : h ∈ sympB2derCarrier K) :
    MulAut.conj g h ∈ sympB2derCarrier K := by
  have hSp_map : (LargeEvenSpGroup K 2).map
      (MulAut.conj g : GL (Fin 2 ⊕ Fin 2) K →* GL (Fin 2 ⊕ Fin 2) K) =
      LargeEvenSpGroup K 2 := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem hg hy) (inv_mem hg)
    · intro x hx
      exact ⟨g⁻¹ * x * g, mul_mem (mul_mem (inv_mem hg) hx) hg, by
        change g * (g⁻¹ * x * g) * g⁻¹ = x
        group⟩
  have hmap : (sympB2derCarrier K).map
      (MulAut.conj g : GL (Fin 2 ⊕ Fin 2) K →* GL (Fin 2 ⊕ Fin 2) K) =
      sympB2derCarrier K := by
    rw [sympB2derCarrier, Subgroup.map_commutator, hSp_map]
  rw [← hmap]
  exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩

private theorem sympB2der_mem_sp_of_mem_gspSet {K : Type} [Field K] (hKcard : Nat.card K = 2)
    {A : GL (Fin 2 ⊕ Fin 2) K} (hA : A ∈ LargeEvenGSpSet K 2) :
    A ∈ LargeEvenSpGroup K 2 := by
  obtain ⟨μ, hμ, hform⟩ := hA
  have hμ1 : μ = 1 := by
    have hunits : Nat.card Kˣ = 1 := by rw [Nat.card_units, hKcard]
    haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hunits).1
    have h := Subsingleton.eq_one (Units.mk0 μ hμ)
    simpa using congrArg Units.val h
  rw [hμ1, one_smul] at hform
  rw [show LargeEvenSpGroup K 2 = CFSG.Open.StatedSp 2 K from rfl]
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  rw [largeEvenSpForm_def] at hform
  simpa using hform

private theorem sympB2der_card_bound {K : Type} [Field K] [Finite K] (hKcard : Nat.card K = 2)
    {X : Type} [Group X] (A : Subgroup (MulAut X))
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (sympB2derCarrier K))
    (hinj : Function.Injective (ggInducedAut θ))
    (hInn : GGInducedInn A θ
      (LargeEvenMatConjImage (LargeEvenProjMk (sympB2derCarrier K)) (LargeEvenGSpSet K 2))) :
    Nat.card A ∣ 720 := by
  let H := sympB2derCarrier K
  let N : Subgroup ↥H := (LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf H
  haveI : N.Normal := inferInstance
  let φGL : ↥(LargeEvenSpGroup K 2) →* MulAut (GL (Fin 2 ⊕ Fin 2) K) :=
    (MulAut.conj).comp (LargeEvenSpGroup K 2).subtype
  have hH : ∀ g : ↥(LargeEvenSpGroup K 2), ∀ h ∈ H, φGL g h ∈ H := by
    intro g h hh
    exact sympB2der_conj_mem (g := (g : GL (Fin 2 ⊕ Fin 2) K)) g.2 hh
  let φH : ↥(LargeEvenSpGroup K 2) →* MulAut ↥H := restrictAutHom φGL H hH
  have hN : ∀ g : ↥(LargeEvenSpGroup K 2), ∀ z ∈ N, φH g z ∈ N := by
    intro g z hz
    have hz' : ((z : ↥H) : GL (Fin 2 ⊕ Fin 2) K) ∈ LargeEvenScalars (Fin 2 ⊕ Fin 2) K := by
      simpa [N, Subgroup.mem_subgroupOf] using hz
    have hcent : ((z : ↥H) : GL (Fin 2 ⊕ Fin 2) K) ∈
        Subgroup.center (GL (Fin 2 ⊕ Fin 2) K) := by
      rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
      exact hz'
    have hfix : φH g z = z := by
      apply Subtype.ext
      show (MulAut.conj (g : GL (Fin 2 ⊕ Fin 2) K)) ((z : ↥H) : GL (Fin 2 ⊕ Fin 2) K) =
        ((z : ↥H) : GL (Fin 2 ⊕ Fin 2) K)
      rw [MulAut.conj_apply]
      have hcomm := (Subgroup.mem_center_iff.mp hcent) (g : GL (Fin 2 ⊕ Fin 2) K)
      rw [hcomm]
      group
    rw [hfix]
    exact hz
  let Φ : ↥(LargeEvenSpGroup K 2) →* MulAut (LargeEvenProj H) :=
    quotientAutHom φH N hN
  have hcardG : Nat.card ↥(LargeEvenSpGroup K 2) = 720 := by
    rw [show LargeEvenSpGroup K 2 = CFSG.Open.StatedSp 2 K from rfl]
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hKcard]
    norm_num
  have hrange : Nat.card Φ.range ∣ 720 := by
    rw [← hcardG]
    exact Subgroup.card_range_dvd Φ
  have hI : (LargeEvenMatConjImage (LargeEvenProjMk H) (LargeEvenGSpSet K 2)) ⊆ Φ.range := by
    rintro φ ⟨A₀, hA₀, hgraph⟩
    have hA₀sp : A₀ ∈ LargeEvenSpGroup K 2 := sympB2der_mem_sp_of_mem_gspSet hKcard hA₀
    refine ⟨⟨A₀, hA₀sp⟩, ?_⟩
    ext x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    let h' : ↥H := ⟨A₀ * (h : GL (Fin 2 ⊕ Fin 2) K) * A₀⁻¹,
      sympB2der_conj_mem hA₀sp h.2⟩
    have hΦ : Φ ⟨A₀, hA₀sp⟩ (QuotientGroup.mk h) = QuotientGroup.mk h' := by
      change quotientAutHom φH N hN ⟨A₀, hA₀sp⟩ (QuotientGroup.mk h) = QuotientGroup.mk h'
      rw [quotientAutHom_mk]
      congr 1
    have hφ : φ (QuotientGroup.mk h) = QuotientGroup.mk h' := by
      have hh := hgraph h h' rfl
      simpa using hh
    rw [hΦ, hφ]
  have hAle : A.map (ggInducedAut θ) ≤ Φ.range := by
    rintro x ⟨a, ha, rfl⟩
    exact hI (hInn a ha)
  have hdvd : Nat.card (A.map (ggInducedAut θ)) ∣ 720 :=
    dvd_trans (Subgroup.card_dvd_of_le hAle) hrange
  rwa [Subgroup.card_map_of_injective hinj] at hdvd

private theorem sympB2der_raw {lab : LargeEvenLabel} (htag : lab.tag = .B2der)
    {Q : LargeEvenRawCont} (h : CFSG.StandardType.LargeEvenRawDatum lab Q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Q (LargeEvenProj (sympB2derCarrier K))
        (LargeEvenMatConjImage (LargeEvenProjMk (sympB2derCarrier K)) (LargeEvenGSpSet K 2))
        (LargeEvenMatFieldImage (LargeEvenProjMk (sympB2derCarrier K))) := by
  rcases lab with ⟨tag, rank, n⟩
  simp only [LargeEvenLabel.tag] at htag
  subst tag
  simp only [CFSG.StandardType.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeSymplectic] at h
  exact h

end SympB2derAux

theorem sympB2der_noDatum :
    ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
      ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X),
        ¬ DatumOn (fun t => t = .B2der) X A δ J := by
  intro X _ _ hX A δ J hD
  obtain ⟨hKLocal, -, hA3, hMarking⟩ := hD
  simp only [CFSG.StandardType.LargeEvenMarking, CFSG.Assembly.LargeEvenMarkingLegacy] at hMarking
  obtain ⟨-, lab, hlab, hraw⟩ := hMarking
  obtain ⟨R, hR, I, F, hcont⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hP⟩ := hcont
  have htag : lab.tag = .B2der := hP.1
  obtain ⟨K, hK, hKf, hKcard, hcont2⟩ := sympB2der_raw htag hraw
  obtain ⟨-, -, θ', hP'⟩ := hcont2
  have hInn := hP'.2.2
  have hinj : Function.Injective (ggInducedAut θ') :=
    ggInducedAut_injective_of_perfect hX θ'
  have hdvd : Nat.card A ∣ 720 := sympB2der_card_bound hKcard A θ' hinj hInn
  have hA3p : IsPGroup 3 A := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hKLocal.1.1.2 (x : MulAut X) x.2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hA3p.exists_card_eq
  have hdvd' : (3:ℕ) ^ n ∣ 720 := by rw [hn] at hdvd; exact hdvd
  have hn3 : 3 ≤ n := by
    by_contra h
    have hle : n ≤ 2 := by omega
    have hge : (3:ℕ) ^ 3 ≤ 3 ^ n := by rw [← hn]; exact hA3
    have hmono : (3:ℕ) ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
    have : (3:ℕ) ^ 3 ≤ 3 ^ 2 := le_trans hge hmono
    norm_num at this
  have : (3:ℕ) ^ 3 ∣ 720 := dvd_trans (pow_dvd_pow 3 hn3) hdvd'
  norm_num at this

end CFSG.StandardType.TablePThreeKG

end
