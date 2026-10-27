module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCoreTwo
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly UCoord

namespace Rk2U3

section Frame

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)
open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (permGL_mul_diagHom_mul_inv)

theorem exists_frameTorus {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hpd : ¬ p ∣ d) {E : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hE : IsElemAbelian p E)
    (hscE : ∀ g : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)),
      (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    ∃ τ : ↥(sumZero d p) →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)),
      Function.Injective τ ∧ τ.range = E ∧
        ∀ σ : Equiv.Perm (Fin d), ∃ w, ∀ f, w * τ f * w⁻¹ = τ (permAutV σ f) := by
  classical
  have hd : d ≠ 0 := by
    rintro rfl
    exact hpd (dvd_zero p)
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have h := TableBU.unitaryFieldData_of_card hK hn
  have : CharP K 2 := h.charP
  have : NeZero p := ⟨hp.ne_zero⟩
  have hnp : ∀ z ∈ (projU n (m + 1) K).ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    TableBUE.eq_one_of_mem_suScalars h hp hpd hz hzp
  obtain ⟨A, hAmap, -, hA, -⟩ :=
    TableBUE.exists_lift_of_noTorsion (projU n (m + 1) K) projU_surjective hp hnp hE
  obtain ⟨P, hP, hPd⟩ := TableBUE.exists_conj_diag h hp hpq hA
  obtain ⟨u, hord, huq⟩ : ∃ u : Kˣ, orderOf u = p ∧ u ^ (2 ^ n + 1) = 1 := by
    have := Fact.mk hp
    have hpK : p ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hK]
      have e : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        have := Nat.sq_sub_sq (2 ^ n) 1
        rwa [one_pow] at this
      rw [e]
      exact Dvd.dvd.mul_right hpq _
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hpK
    refine ⟨u, hu, ?_⟩
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, ← hu, pow_orderOf_eq_one, one_pow]
  have hu : u ^ p = 1 := hord ▸ pow_orderOf_eq_one u
  have hDmem : ∀ f : ↥(sumZero (m + 1) p), diagHom (m + 1) (UModel.uvec hu f) ∈
      unitarySU 2 n K (m + 1) := fun f =>
    TableBUE.diagHom_mem_unitarySU h (fun k => UModel.uvec_pow_norm hu huq f k)
      (UModel.prod_uvec hu hord f)
  set Dsu : ↥(sumZero (m + 1) p) →* ↥(unitarySU 2 n K (m + 1)) :=
    ((diagHom (m + 1)).comp (UModel.uvec hu)).codRestrict _ hDmem with hDsu
  have hDsu_coe : ∀ f, ((Dsu f : ↥(unitarySU 2 n K (m + 1))) : GL (Fin (m + 1)) K) =
      diagHom (m + 1) (UModel.uvec hu f) := fun f => rfl
  set τ : ↥(sumZero (m + 1) p) →* LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K (2 ^ n)) :=
    (frameMk h P hP).comp Dsu with hτ
  have hτapp : ∀ f, τ f = projU n (m + 1) K ((TableBUE.conjSU h P hP).symm (Dsu f)) :=
    fun f => rfl
  have hEA : ∀ e ∈ E, ∃ y ∈ A, projU n (m + 1) K y = e := by
    intro e he
    rw [← hAmap] at he
    obtain ⟨y, hy, rfl⟩ := he
    exact ⟨y, hy, rfl⟩
  have hcommA : ∀ f, ∀ y ∈ A, τ f * projU n (m + 1) K y = projU n (m + 1) K y * τ f := by
    intro f y hy
    obtain ⟨σ, hσ⟩ := hPd y hy
    have hc : (TableBUE.conjSU h P hP).symm (Dsu f) * y =
        y * (TableBUE.conjSU h P hP).symm (Dsu f) := by
      apply (TableBUE.conjSU h P hP).injective
      apply Subtype.ext
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul, hσ,
        hDsu_coe, ← map_mul, ← map_mul, mul_comm]
    rw [hτapp, ← map_mul, hc, map_mul]
  have hτE1 : ∀ f, τ f ∈ E := by
    intro f
    refine hscE (τ f) (fun e he => ?_) (by rw [← map_pow, pow_p_eq_one, map_one])
    obtain ⟨y, hy, rfl⟩ := hEA e he
    exact hcommA f y hy
  have hτE2 : ∀ e ∈ E, ∃ f, τ f = e := by
    intro e he
    obtain ⟨y, hy, rfl⟩ := hEA e he
    obtain ⟨σ, hσ⟩ := hPd y hy
    have hσp : ∀ k, σ k ^ p = 1 := by
      have h1 : (TableBUE.conjSU h P hP y) ^ p = 1 := by rw [← map_pow, hA.2 y hy, map_one]
      have h2 : diagHom (m + 1) (σ ^ p) = 1 := by
        rw [map_pow, ← hσ, ← Subgroup.coe_pow, h1, Subgroup.coe_one]
      have h3 : σ ^ p = 1 := diagHom_injective (m + 1) (by rw [h2, map_one])
      intro k
      exact congrFun h3 k
    have hσprod : ∏ k, σ k = 1 := by
      have h1 := ((mem_unitarySU_iff h).mp (TableBUE.conjSU h P hP y).2).1
      rw [hσ, det_diagHom] at h1
      exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact h1)
    obtain ⟨f, hf⟩ := UModel.exists_uvec_eq hu hord hσp hσprod
    refine ⟨f, ?_⟩
    rw [hτapp]
    congr 1
    apply (TableBUE.conjSU h P hP).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hDsu_coe, hf, hσ]
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    rw [hτapp] at hf
    have h1 := hnp _ (MonoidHom.mem_ker.mpr hf)
      (by rw [← map_pow, ← map_pow, pow_p_eq_one, map_one, map_one])
    have h2 : Dsu f = 1 := by
      have := congrArg (TableBUE.conjSU h P hP) h1
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    have h3 : UModel.uvec hu f = 1 := by
      apply diagHom_injective (m + 1)
      rw [map_one, ← hDsu_coe, h2, Subgroup.coe_one]
    apply UModel.uvec_injective hu hord
    rw [h3, map_one]
  have hτrange : τ.range = E := by
    ext e
    constructor
    · rintro ⟨f, rfl⟩
      exact hτE1 f
    · intro he
      exact hτE2 e he
  refine ⟨τ, hτinj, hτrange, fun σ => ?_⟩
  set M : ↥(unitarySU 2 n K (m + 1)) := ⟨permGL σ, SURep.permGL_mem_unitarySU h σ⟩ with hM
  refine ⟨frameMk h P hP M, fun f => ?_⟩
  have hMD : M * Dsu f * M⁻¹ = Dsu (permAutV σ f) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hDsu_coe, hDsu_coe,
      UModel.uvec_permAutV]
    exact permGL_mul_diagHom_mul_inv σ (UModel.uvec hu f)
  rw [hτ, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul, hMD]

end Frame

theorem crd_zpow {d p : ℕ} (f : ↥(sumZero d p)) (k : ℤ) (i : Fin d) :
    crd (f ^ k) i = (k : ZMod p) * crd f i := by
  rw [← zsmul_eq_mul]
  rfl

theorem exists_perm_not_mem_zpowers {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {f : ↥(sumZero 3 p)} (hf : f ≠ 1) :
    ∃ σ : Equiv.Perm (Fin 3), permAutV σ f ∉ Subgroup.zpowers f := by
  have := Fact.mk hp
  by_contra hcon
  push Not at hcon
  have key : ∀ σ : Equiv.Perm (Fin 3), ∃ k : ZMod p, ∀ i, crd f (σ⁻¹ i) = k * crd f i := by
    intro σ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcon σ)
    exact ⟨(k : ZMod p), fun i => by rw [← crd_permAutV, ← hk, crd_zpow]⟩
  obtain ⟨k₁, hk₁⟩ := key (Equiv.swap 0 1)
  obtain ⟨k₂, hk₂⟩ := key (Equiv.swap 0 2)
  have e₁ : crd f 1 = k₁ * crd f 0 := by simpa using hk₁ 0
  have e₁' : crd f 2 = k₁ * crd f 2 := by
    have h := hk₁ 2
    rwa [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)] at h
  have e₂ : crd f 2 = k₂ * crd f 0 := by simpa using hk₂ 0
  have e₂' : crd f 1 = k₂ * crd f 1 := by
    have h := hk₂ 1
    rwa [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)] at h
  have hsum : crd f 0 + crd f 1 + crd f 2 = 0 := by
    have h := sum_crd f
    rwa [Fin.sum_univ_three] at h
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')
  have ha : crd f 0 = 0 := by
    by_contra ha
    have h1 : k₂ * (1 - k₁) = 0 := by
      have : k₂ * (1 - k₁) * crd f 0 = 0 := by linear_combination -(1 - k₁) * e₂ + e₁'
      exact (mul_eq_zero.mp this).resolve_right ha
    have h2 : k₁ * (1 - k₂) = 0 := by
      have : k₁ * (1 - k₂) * crd f 0 = 0 := by linear_combination -(1 - k₂) * e₁ + e₂'
      exact (mul_eq_zero.mp this).resolve_right ha
    have h4 : 1 + k₁ + k₂ = 0 := by
      have : (1 + k₁ + k₂) * crd f 0 = 0 := by linear_combination hsum - e₁ - e₂
      exact (mul_eq_zero.mp this).resolve_right ha
    rcases mul_eq_zero.mp h1 with hk | hk
    · have hk' : k₁ = 0 := by
        have := h2
        rw [hk, sub_zero, mul_one] at this
        exact this
      exact one_ne_zero (by linear_combination h4 - hk' - hk : (1 : ZMod p) = 0)
    · have hk1 : k₁ = 1 := by linear_combination -hk
      have hk2 : k₂ = 1 := by
        have := h2
        rw [hk1, one_mul] at this
        linear_combination -this
      exact h3 (by linear_combination h4 - hk1 - hk2)
  apply hf
  refine ext_crd fun i => ?_
  rw [crd_one]
  fin_cases i
  · exact ha
  · show crd f 1 = 0
    rw [e₁, ha, mul_zero]
  · show crd f 2 = 0
    rw [e₂, ha, mul_zero]

theorem ggTorusNoLineTwo_of_frame {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {R : Type} [Group R]
    {I : Set (MulAut R)} (hZ : Subgroup.center R = ⊥) (hIp : GGOutdiagPrime p R I)
    (hcp : GGCenterPrime p R)
    (hfr : ∀ E : Subgroup R, IsElemAbelian p E →
      (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
      ∃ τ : ↥(sumZero 3 p) →* R, Function.Injective τ ∧ τ.range = E ∧
        ∀ σ : Equiv.Perm (Fin 3), ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (permAutV σ f)) :
    GGTorusNoLineTwo p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ hsc
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, -, hAΛ, hEab, -, hscE⟩ :=
    TwE6TB.exists_innerModel hp hZ hIp hcp ψ hψ hker hperf hA hAI hsc
  obtain ⟨τ, hτinj, hτE, hperm⟩ := hfr _ hEab hscE
  obtain ⟨s, hs, hsp⟩ := exists_section_of_centerPrime hp hψ hker hcpL
    (V := ↥(sumZero 3 p)) pow_p_eq_one τ
  have hΛs : ∀ f, Λ (τ f) = MulAut.conj (s f) := fun f => hΛeq (hs f)
  have hAs : ∀ a ∈ A, ∃ f, a = MulAut.conj (s f) := by
    intro a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have he : e ∈ τ.range := by
      rw [hτE]
      exact ha
    obtain ⟨f, rfl⟩ := he
    exact ⟨f, hΛs f⟩
  have hsinj : ∀ f g, MulAut.conj (s f) = MulAut.conj (s g) → f = g := fun f g h =>
    hτinj (hΛinj (by rw [hΛs, hΛs, h]))
  have hconj : ∀ (n : L') (σ : Equiv.Perm (Fin 3)),
      (∀ f, ψ n * τ f * (ψ n)⁻¹ = τ (permAutV σ f)) →
        ∀ f, n * s f * n⁻¹ = s (permAutV σ f) := by
    intro n σ hσ f
    refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ (hsp _)
    · rw [map_mul, map_mul, map_inv, hs, hs, hσ]
    · rw [conj_pow, hsp, mul_one, mul_inv_cancel]
  refine ⟨{n | ∃ σ : Equiv.Perm (Fin 3), ∀ f, ψ n * τ f * (ψ n)⁻¹ = τ (permAutV σ f)}, ?_, ?_⟩
  ·
    rintro n ⟨σ, hσ⟩ a ha
    obtain ⟨f, rfl⟩ := hAs a ha
    have he : n * (MulAut.conj (s f) n)⁻¹ = s (permAutV σ f * f⁻¹) := by
      rw [MulAut.conj_apply, map_mul, map_inv, ← hconj n σ hσ f]
      group
    rw [he]
    refine ⟨by rw [← map_pow, pow_p_eq_one, map_one], fun a' ha' => ?_⟩
    obtain ⟨g, rfl⟩ := hAs a' ha'
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, mul_comm g, mul_inv_cancel_right]
  ·
    intro _ a₀ ha₀ hne
    obtain ⟨f, rfl⟩ := hAs a₀ ha₀
    have hf : f ≠ 1 := by
      rintro rfl
      exact hne (by rw [map_one, map_one])
    obtain ⟨σ, hσ⟩ := exists_perm_not_mem_zpowers hp hp3 hf
    obtain ⟨w, hw⟩ := hperm σ
    obtain ⟨n, rfl⟩ := hψ w
    refine ⟨n, ⟨σ, hw⟩, fun hmem => hσ ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hconj n σ hw f] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← map_zpow, ← map_zpow] at hk
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hsinj _ _ hk⟩

theorem ggTorusNoLineTwo_unitary
    {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ n + 1) :
    GGTorusNoLineTwo p (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
        (LargeEvenGUSet (Fin 3) K (2 ^ n))) := by
  have hn1 : 1 ≤ n := by omega
  have hp3 : p ≠ 3 := by omega
  have hp2 : p ≠ 2 := by omega
  have hpd : ¬ p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  have hdq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  exact ggTorusNoLineTwo_of_frame hp hp3 (TableBUE.center_proj_eq_bot hK le_rfl hdq)
    (InndiagSU.ggOutdiagPrime_unitary hK hn1 le_rfl hdq hp hpq hpd)
    (StdSubRestU.ggCenterPrime_unitary hK hn1 le_rfl hdq hp hp2 hpd)
    fun _ hE hscE => exists_frameTorus hK hn1 hp hpq hpd hE hscE

end Rk2U3

theorem largeEvenLabelAll_rowPlainTwo_u3
    {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twA ∧ lab.rank = 2 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlainTwo p 0) := by
  have hrest : LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusLift p 0 R ∧ GGTorusNoLineTwo p R I := by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨ht, hl, hpn⟩ := h
    dsimp only at ht hl hpn
    subst ht hl
    have hn : 2 ≤ n := hlab.2.2 rfl
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := (TableBU.unitaryFieldData_of_card hK (by omega)).charP
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      TypeA.ggTorusLift_zero
        (two_dvd_card_statedProj_statedSU (d := 3) (f := n) (K := K) (by norm_num)),
      Rk2U3.ggTorusNoLineTwo_unitary hK hn hp hp5 hpn⟩
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_twA hlab h.1) hrest).mono
    fun _ _ _ _ ⟨hi, hl, hn⟩ => ⟨hi, hl, fun _ _ => hn⟩

end CFSG.StandardType

end
