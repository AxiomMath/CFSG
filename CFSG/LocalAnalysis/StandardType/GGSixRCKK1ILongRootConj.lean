module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IDefs
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.LieType.HighestRoot.RootsUnitary

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)
open CFSG.LieType.Steinberg CFSG.LieType.HighestRoot CFSG.ClassicalInvolution.ModelFacts
open CFSG.LieType.CurtisTits CFSG.LieType.Universal.Unitary

private theorem rckK1Ilrc_isLongestRoot_of_maxHeight
    {K : Type*} [Group K] {D : UniversalRootDatum K}
    (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅)
    {γ₀ : Fin D.rank → ℤ} (hγ₀ : γ₀ ∈ D.roots)
    (hmax : ∀ δ ∈ D.roots, ht δ ≤ ht γ₀) : IsLongestRoot D γ₀ := by
  have hrank : 0 < D.rank := by
    obtain ⟨w, i, -⟩ | ⟨w, i, -, -⟩ := hγ₀
    · exact Fin.pos i
    · exact Fin.pos i
  obtain ⟨r, hr⟩ := exists_isHighestRoot D hirr hdiv hrank
  have hdom : IsDominant D.isFiniteType γ₀ :=
    isDominant_of_ht_le D.isFiniteType fun k =>
      hmax _ (weylAction_mem_roots D.isFiniteType _ hγ₀)
  have h0 : (0 : Fin D.rank → ℤ) ≤ γ₀ := nonneg_of_isDominant D.isFiniteType hγ₀ hdom
  rcases hr.mem_roots with ⟨w, i, hwi⟩ | ⟨w, i, hi, hwi⟩
  · have hle : γ₀ ≤ r :=
      le_of_nonneg D.isFiniteType hirr hwi hr.longest hr.dominant hγ₀ h0
    have hht : ht γ₀ = ht r :=
      le_antisymm (hr.height_le γ₀ hγ₀) (hmax r hr.mem_roots)
    have hsum : ∑ k, (r - γ₀) k = 0 := by
      have h1 : (∑ k, r k) - (∑ k, γ₀ k) = 0 := by
        have : ht r = ht γ₀ := hht.symm
        simpa only [ht] using sub_eq_zero.mpr this
      calc ∑ k, (r - γ₀) k = (∑ k, r k) - (∑ k, γ₀ k) := by
            simp only [Pi.sub_apply, Finset.sum_sub_distrib]
        _ = 0 := h1
    have heq : γ₀ = r := by
      have hsub : r - γ₀ = 0 := by
        by_contra hne
        have h0' : 0 ≤ r - γ₀ := sub_nonneg.mpr hle
        have h1 := one_le_sum_of_nonneg h0' hne
        omega
      exact (sub_eq_zero.mp hsub).symm
    rw [heq]
    exact hr.isLongestRoot
  · rw [hdiv] at hi
    exact absurd hi (Set.notMem_empty i)

theorem rckK1Ilrc_isLongestRoot_of_longRoot
    {K : Type*} [Group K] {D : UniversalRootDatum K}
    (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅)
    {β : Fin D.rank → ℤ} (hβ : GGLongRoot D β) : IsLongestRoot D β := by
  obtain ⟨w, γ₀, hγ₀, hmax, hβeq⟩ := hβ
  have hL : IsLongestRoot D γ₀ :=
    rckK1Ilrc_isLongestRoot_of_maxHeight hirr hdiv hγ₀ hmax
  have hmap : IsLongestRoot D (weylAction D.isFiniteType w γ₀) := hL.map_weylAction w
  simpa [hβeq] using hmap

private theorem rckK1Ilrc_toStd_two_eq {n : ℕ} (hn : ¬ Even n) (hn3 : 3 ≤ n) :
    Unitary.toStd n (fun _ : Fin (n / 2) => (2 : ℤ)) =
      2 • Unitary.weight n ⟨0, by omega⟩ := by
  funext a
  have h0 : (0 : ℕ) < n / 2 := by omega
  simp only [Unitary.toStd, hn, ite_false, Unitary.weight, h0, dite_true, Pi.smul_apply]
  by_cases ha : a.val = 0
  · have : a = ⟨0, h0⟩ := Fin.ext ha
    subst this
    simp
  · have ha' : 0 < a.val := Nat.pos_of_ne_zero ha
    have hne : a ≠ ⟨0, h0⟩ := fun e => ha (by rw [e])
    simp [ha', Pi.single_eq_of_ne hne]

private theorem rckK1Ilrc_isLongestRoot_unitary_odd
    {F : Type} [Field F] [Finite F] {p f n : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hn : ¬ Even n) (hn3 : 3 ≤ n)
    {γ₀ : Fin (n / 2) → ℤ} (hγ₀ : γ₀ ∈ (Unitary.rootDatum hF n).roots)
    (hmax : ∀ δ ∈ (Unitary.rootDatum hF n).roots, ht δ ≤ ht γ₀) :
    IsLongestRoot (Unitary.rootDatum hF n) γ₀ := by
  let r : Fin (n / 2) → ℤ := fun _ => 2
  have hr : IsHighestRoot (Unitary.rootDatum hF n) r := isHighestRoot_unitary_odd hF hn hn3
  have hhteq : ht γ₀ = ht r := le_antisymm (hr.height_le γ₀ hγ₀) (hmax _ hr.mem_roots)
  have htoStd_two : Unitary.toStd n r = 2 • Unitary.weight n ⟨0, by omega⟩ :=
    rckK1Ilrc_toStd_two_eq hn hn3
  have hhtr : ht r = (n : ℤ) - 1 := by
    have h1 : 2 * ht r = SUExtras.lv n (Unitary.toStd n r) := SUExtras.two_mul_ht (n := n) r
    rw [htoStd_two, map_nsmul, SUExtras.lv_weight] at h1
    simp only [nsmul_eq_mul, mul_one, Nat.cast_ofNat] at h1
    omega
  have hroots : (Unitary.rootDatum hF n).roots = roots (Unitary.isFiniteType_cartan n)
      (Unitary.divisible n) := rfl
  rw [hroots, Unitary.roots_eq] at hγ₀
  rcases hγ₀ with ⟨i, j, hij, hi, hj, hji, hstd⟩ | ⟨i, hi, hstd⟩ | ⟨hne, i, hi, hstd⟩
  · have hth := SUExtras.ht_eq_of_weight_sub hstd.symm
    have hthji : (↑↑j : ℤ) - ↑↑i = (n : ℤ) - 1 := by linarith [hth, hhteq, hhtr]
    have hival : i.val = 0 := by omega
    have hjval : j.val = n - 1 := by omega
    have hji_eq : j = Fin.rev i := by
      apply Fin.ext
      rw [Fin.val_rev, hival]
      omega
    exact absurd hji_eq hji
  · have h1 := SUExtras.two_mul_ht γ₀
    rw [hstd, map_nsmul, SUExtras.lv_weight] at h1
    simp only [nsmul_eq_mul, mul_one, Nat.cast_ofNat] at h1
    have hival : i.val = 0 := by
      have : (↑↑i : ℤ) = 0 := by linarith [h1, hhteq, hhtr]
      omega
    have hito : i = ⟨0, by omega⟩ := Fin.ext (by simpa using hival)
    have hstd0 : Unitary.toStd n γ₀ = 2 • Unitary.weight n ⟨0, by omega⟩ := by
      rw [hstd, hito]
    have heq : γ₀ = r :=
      SUExtras.toStd_inj' (hstd0.trans htoStd_two.symm)
    rw [heq]
    exact hr.isLongestRoot
  · exfalso
    have h1 := SUExtras.two_mul_ht γ₀
    rw [hstd, SUExtras.lv_weight] at h1
    have hi0 : (0 : ℤ) ≤ (↑↑i : ℤ) := by exact_mod_cast Nat.zero_le i.val
    linarith [h1, hhteq, hhtr, hi0]

private theorem rckK1Ilrc_conj_of_isLongest
    {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hirr : IsIrreducible D.cartan)
    (hratio : ∀ i ∈ D.divisible, ∀ j,
      symmetrizer D.isFiniteType j < 4 * symmetrizer D.isFiniteType i)
    {β β' : Fin D.rank → ℤ} (hβL : IsLongestRoot D β) (hβ'L : IsLongestRoot D β') :
    ∃ u : K, (D.rootGroup β).map (MulAut.conj u).toMonoidHom = D.rootGroup β' := by
  obtain ⟨u, hu, -⟩ := exists_map_conj_rankOne_of_isLongest hct hirr hratio hβL hβ'L
  exact ⟨u, hu⟩

theorem rckK1I_longRootConj
    {t : StatedLieTag} {n f : ℕ} (ht : GGPosTag t) (hadm : StatedLieAdmissible t n 2 f)
    {β β' : Fin (ggU t n f).D.rank → ℤ} (hβ : β ∈ (ggU t n f).D.roots) (hlong : GGLongRoot (ggU t n f).D β)
    (hβ' : β' ∈ (ggU t n f).D.roots) (hlong' : GGLongRoot (ggU t n f).D β') :
    ∃ u : (ggU t n f).K,
      ((ggU t n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom = (ggU t n f).D.rootGroup β' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    obtain ⟨ν, H, hct, -⟩ := hasBruhatDatum .PSL (m + 1) 2 f Nat.prime_two (by trivial) hadm
    obtain ⟨hirr, hratio⟩ := cartanOK .PSL (m + 1) 2 f Nat.prime_two (by trivial) hadm
    have hdiv : (ggU .PSL (m + 1) f).D.divisible = ∅ := rfl
    exact rckK1Ilrc_conj_of_isLongest hct hirr hratio
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong)
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong')
  ·
    have hf : 1 ≤ f := hadm.2.1
    have hDm : modelUniv .PSU n 2 f Nat.prime_two =
        ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ :=
      modelUniv_PSU (p := 2) (f := f) (n := n) hf
    by_cases he : Even n
    · have hdiv : (ggU .PSU n f).D.divisible = ∅ := by
        change (modelUniv .PSU n 2 f Nat.prime_two).D.divisible = ∅
        rw [modelUniv_PSU (p := 2) (f := f) (n := n) hf]
        exact (unitary_even he).2
      obtain ⟨ν, H, hct, -⟩ := hasBruhatDatum .PSU n 2 f Nat.prime_two (by trivial) hadm
      obtain ⟨hirr, hratio⟩ := cartanOK .PSU n 2 f Nat.prime_two (by trivial) hadm
      exact rckK1Ilrc_conj_of_isLongest hct hirr hratio
        (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong)
        (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong')
    · have hn3 : 3 ≤ n := hadm.2.2.1
      have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
      have hggU : ggU .PSU n f =
          ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
              (GaloisField 2 (2 * f)) 2 f) n,
            Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
        simp only [ggU, lieUniversal, hf, ↓reduceDIte]
      revert β β' hβ hlong hβ' hlong'
      rw [hggU]
      intro β β' hβ hlong hβ' hlong'
      obtain ⟨ζ, hζ⟩ := Unitary.exists_traceZero_ne_zero hF
      have hct := Unitary.isCTGroupDatum (F := GaloisField 2 (2 * f)) hF n (by omega) ζ hζ
      obtain ⟨hc, hd⟩ := unitary_odd he
      have hirr : IsIrreducible (Unitary.rootDatum hF n).cartan := by
        show IsIrreducible (Unitary.cartan n)
        rw [hc]
        exact isIrreducible_transpose_cartanC (by omega)
      have hratio : ∀ i ∈ (Unitary.rootDatum hF n).divisible, ∀ j,
          symmetrizer (Unitary.rootDatum hF n).isFiniteType j <
            4 * symmetrizer (Unitary.rootDatum hF n).isFiniteType i := by
        intro i hi j
        have hi' : i ∈ Unitary.divisible n := hi
        rw [hd] at hi'
        exact symmetrizer_lt_four_mul_BC (by omega) hc _ i hi' j
      have hβL : IsLongestRoot (Unitary.rootDatum hF n) β := by
        obtain ⟨w, γ₀, hγ₀, hmax, hβeq⟩ := hlong
        have hL := rckK1Ilrc_isLongestRoot_unitary_odd (p := 2) (f := f) hF he hn3 hγ₀ hmax
        have hmap := hL.map_weylAction w
        simpa [IsLongestRoot, hβeq] using hmap
      have hβ'L : IsLongestRoot (Unitary.rootDatum hF n) β' := by
        obtain ⟨w, γ₀, hγ₀, hmax, hβeq⟩ := hlong'
        have hL := rckK1Ilrc_isLongestRoot_unitary_odd (p := 2) (f := f) hF he hn3 hγ₀ hmax
        have hmap := hL.map_weylAction w
        simpa [IsLongestRoot, hβeq] using hmap
      exact rckK1Ilrc_conj_of_isLongest hct hirr hratio hβL hβ'L
  ·
    obtain ⟨ν, H, hct, -⟩ := hasBruhatDatum .PSp n 2 f Nat.prime_two (by trivial) hadm
    obtain ⟨hirr, hratio⟩ := cartanOK .PSp n 2 f Nat.prime_two (by trivial) hadm
    have hdiv : (ggU .PSp n f).D.divisible = ∅ := rfl
    exact rckK1Ilrc_conj_of_isLongest hct hirr hratio
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong)
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong')
  ·
    have hn : 3 ≤ n := by have := hadm.2.2; omega
    have hDm : modelUniv .POmegaPlus n 2 f Nat.prime_two =
        ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
          Spin.plusDatum n (GaloisField 2 f) hn⟩ :=
      modelUniv_POmegaPlus (p := 2) (f := f) (n := n) hn
    obtain ⟨ν, H, hct, -⟩ := hasBruhatDatum .POmegaPlus n 2 f Nat.prime_two (by trivial) hadm
    obtain ⟨hirr, hratio⟩ := cartanOK .POmegaPlus n 2 f Nat.prime_two (by trivial) hadm
    have hdiv : (ggU .POmegaPlus n f).D.divisible = ∅ := by
      change (modelUniv .POmegaPlus n 2 f Nat.prime_two).D.divisible = ∅
      rw [modelUniv_POmegaPlus (p := 2) (f := f) (n := n) hn]
      rfl
    exact rckK1Ilrc_conj_of_isLongest hct hirr hratio
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong)
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong')
  ·
    obtain ⟨ν, H, hct, -⟩ := hasBruhatDatum .POmegaMinus n 2 f Nat.prime_two (by trivial) hadm
    obtain ⟨hirr, hratio⟩ := cartanOK .POmegaMinus n 2 f Nat.prime_two (by trivial) hadm
    have hdiv : (ggU .POmegaMinus n f).D.divisible = ∅ := rfl
    exact rckK1Ilrc_conj_of_isLongest hct hirr hratio
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong)
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong')
  ·
    obtain ⟨ν, H, hct, -⟩ := hasBruhatDatum .F4 n 2 f Nat.prime_two (by trivial) hadm
    obtain ⟨hirr, hratio⟩ := cartanOK .F4 n 2 f Nat.prime_two (by trivial) hadm
    have hdiv : (ggU .F4 n f).D.divisible = ∅ := rfl
    exact rckK1Ilrc_conj_of_isLongest hct hirr hratio
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong)
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong')
  ·
    obtain ⟨ν, H, hct, -⟩ := hasBruhatDatum .E6 n 2 f Nat.prime_two (by trivial) hadm
    obtain ⟨hirr, hratio⟩ := cartanOK .E6 n 2 f Nat.prime_two (by trivial) hadm
    have hdiv : (ggU .E6 n f).D.divisible = ∅ := rfl
    exact rckK1Ilrc_conj_of_isLongest hct hirr hratio
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong)
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong')
  ·
    obtain ⟨ν, H, hct, -⟩ := hasBruhatDatum .E7 n 2 f Nat.prime_two (by trivial) hadm
    obtain ⟨hirr, hratio⟩ := cartanOK .E7 n 2 f Nat.prime_two (by trivial) hadm
    have hdiv : (ggU .E7 n f).D.divisible = ∅ := rfl
    exact rckK1Ilrc_conj_of_isLongest hct hirr hratio
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong)
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong')
  ·
    obtain ⟨ν, H, hct, -⟩ := hasBruhatDatum .E8 n 2 f Nat.prime_two (by trivial) hadm
    obtain ⟨hirr, hratio⟩ := cartanOK .E8 n 2 f Nat.prime_two (by trivial) hadm
    have hdiv : (ggU .E8 n f).D.divisible = ∅ := rfl
    exact rckK1Ilrc_conj_of_isLongest hct hirr hratio
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong)
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong')
  ·
    obtain ⟨ν, H, hct, -⟩ := hasBruhatDatum .twistedE6 n 2 f Nat.prime_two (by trivial) hadm
    obtain ⟨hirr, hratio⟩ := cartanOK .twistedE6 n 2 f Nat.prime_two (by trivial) hadm
    have hdiv : (ggU .twistedE6 n f).D.divisible = ∅ := rfl
    exact rckK1Ilrc_conj_of_isLongest hct hirr hratio
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong)
      (rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong')

end CFSG.StandardType.RCKK1I
