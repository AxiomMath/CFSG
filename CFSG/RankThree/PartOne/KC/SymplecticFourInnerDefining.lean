module

public import CFSG.RankThree.PartOne.KC.SymplecticFourClassify
public import CFSG.RankThree.PartOne.KC.SymplecticTransvectionStd
public import CFSG.RankThree.PartOne.KC.LinearThreeFourInnerDefining
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer

public section

namespace CFSG.RankThree.PartOne.KCSymplecticInner

open Matrix CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCExpLog CFSG.RankThree.PartOne.KCSymplectic
open CFSG.RankThree.PartOne.KCSymplecticAdapted CFSG.RankThree.LocalRank
open CFSG.RankThree.Classical (siegelElt coe_siegelElt
  symplectic_four_square_zero_rank_two_centralizer_normal_prime_complements_trivial)

theorem normalPrimeComplementsTrivial_of_unipotent {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K p] (hK : Nat.card K = p ^ f)
    (hTv : ∀ (γ : K) (w : StatedSp 2 K), γ ≠ 0 →
      spMat w = 1 + γ • Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : K) →
      NormalPrimeComplementsTrivial p (MulAut.conj (proj 2 K w)))
    (u : StatedSp 2 K) (hup : u ^ p = 1) (hu1 : u ≠ 1) :
    NormalPrimeComplementsTrivial p (MulAut.conj (proj 2 K u)) := by
  have : Fact p.Prime := ⟨hp⟩
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K p 2).mp h'
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hupm : spMat u ^ p = 1 := by
    have h := congrArg (fun g : StatedSp 2 K => spMat g) hup
    simpa [spMat, Subgroup.coe_pow, Units.val_pow_eq_pow_val] using h
  have hMp : (spMat u - 1) ^ p = 0 := by
    rw [sub_pow_char_of_commute p (Commute.one_right _), one_pow, hupm, sub_self]
  have hM4 : (spMat u - 1) ^ (2 * 2) = 0 := by
    rw [← card_fin_sum_fin 2]
    exact pow_card_eq_zero_of_isNilpotent ⟨p, hMp⟩
  have hdp : 2 * 2 ≤ p := by omega
  have hKc := not_cast_eq_zero_of_lt (K := K) (p := p) (r := 2) hdp
  have huJ : (spMat u)ᵀ * formJ 2 K * spMat u = formJ 2 K :=
    SymplecticTorusWeyl.mem_statedSp_iff.mp u.2
  set N := logMat (2 * 2) (spMat u) with hN
  have hNJ : Nᵀ * formJ 2 K + formJ 2 K * N = 0 :=
    logMat_skew (finSumFinTwoMul 2) (by omega) hdp (formJ_mul_neg 2 K) (neg_formJ_mul 2 K) hM4
      huJ
  have hN4 : N ^ (2 * 2) = 0 := logMat_pow_eq_zero (finSumFinTwoMul 2) hM4
  have hexp : spMat u = expMat (2 * 2) N :=
    (expMat_logMat (finSumFinTwoMul 2) (by omega) hKc hM4).symm
  have hNne : N ≠ 0 := by
    intro h0
    apply hu1
    apply Subtype.ext
    apply Units.ext
    show spMat u = 1
    rw [hexp, h0]
    simp [expMat, Finset.sum_range_succ]
  have hdim : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by simp
  have hf4 : (Matrix.toLin' N) ^ 4 = 0 := by
    rw [← Matrix.toLin'_pow]
    have : N ^ 4 = 0 := hN4
    rw [this, map_zero]
  have hfne : Matrix.toLin' N ≠ 0 := fun h => hNne ((Matrix.toLin'.map_eq_zero_iff).mp h)
  obtain ⟨c, hli, hc⟩ := KCNilpotent.exists_chain_four hdim (Matrix.toLin' N) hf4 hfne
  simp only [Matrix.toLin'_apply] at hc
  rcases hc with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
  ·
    have hN3c : (N ^ 3) *ᵥ c 3 = c 0 := by
      rw [pow_three, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h3, h2, h1]
    have hN1 : N ^ (2 * 2 - 1) ≠ 0 := by
      intro h
      have h' : N ^ 3 = 0 := h
      rw [h', Matrix.zero_mulVec] at hN3c
      exact hli.ne_zero 0 hN3c.symm
    intro B hB S hSC hSn hSp
    exact symplectic_regular_unipotent_centralizer_normal_prime_complements_trivial hp hp3 hf
      (le_refl 2) hdp hK hNJ hN4 hN1 u hexp B hB S hSC hSn hSp
  ·
    obtain ⟨A, γ, hγ, hA, hNA⟩ := exists_isometry_of_chain_transvection hNJ hli h0 h1 h2 h3
    have hsq : (γ • (Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
        (γ • (Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = 0 := by
      simp
    obtain ⟨s, w, hsw, hw⟩ := exists_conj_of_isometry_mul_eq hexp hA hNA hsq
    have h' := NormalPrimeComplementsTrivial.of_conj_mul (proj 2 K s) (proj 2 K w)
      (hTv γ w hγ hw)
    rwa [← map_inv, ← map_mul, ← map_mul, ← hsw] at h'
  ·
    obtain ⟨A, D, hA, hDs, hD, hNA⟩ := exists_isometry_of_chain_square_zero hNJ h2K hli h0 h1 h2 h3
    have hsq : (Matrix.fromBlocks 0 D 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        Matrix.fromBlocks 0 D 0 0 = 0 := by
      rw [Matrix.fromBlocks_multiply]
      simp
    obtain ⟨s, w, hsw, hw⟩ := exists_conj_of_isometry_mul_eq hexp hA hNA hsq
    have hws : w = siegelElt hDs := by
      apply SymplecticTorusWeyl.statedSp_ext
      rw [coe_siegelElt]
      show spMat w = _
      rw [hw]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
    have hnpc : NormalPrimeComplementsTrivial p
        (MulAut.conj (proj 2 K (siegelElt hDs))) :=
      fun B hB S hSC hSn hSp =>
        symplectic_four_square_zero_rank_two_centralizer_normal_prime_complements_trivial hp hp3
          hf hK (le_refl 2) hDs hD B hB S hSC hSn hSp
    rw [← hws] at hnpc
    have h' := NormalPrimeComplementsTrivial.of_conj_mul (proj 2 K s) (proj 2 K w) hnpc
    rwa [← map_inv, ← map_mul, ← map_mul, ← hsw] at h'
  ·
    exact (not_chain_three_one_mat hNJ h2K hli h0 h1 h2 h3).elim

theorem not_dvd_card_scalars {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = p ^ f) : ¬ p ∣ Nat.card (spScalars 2 K) := by
  intro hdvd
  have h1 := hdvd.trans (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_scalars_dvd
    (r := 2) (K := K) (by norm_num))
  have hpq : p ∣ Nat.card K := hK ▸ dvd_pow_self p (by omega)
  have hpos : 1 ≤ Nat.card K := Finite.card_pos
  have := Nat.dvd_sub hpq h1
  rw [Nat.sub_sub_self hpos] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem symplectic_four_inner_defining_centralizer_local_cores_trivial {p f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = p ^ f)
    (B : Subgroup (MulAut (StatedProj (StatedSp 2 K))))
    (hB : (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ≤
      B)
    {a : MulAut (StatedProj (StatedSp 2 K))}
    (ha : a ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K))).range) (hord : orderOf a = p) :
    (∀ S : Subgroup (MulAut (StatedProj (StatedSp 2 K))), S ≤ B ⊓ Subgroup.centralizer {a} →
      (S.subgroupOf (B ⊓ Subgroup.centralizer {a})).Normal → ¬ p ∣ Nat.card S → S = ⊥) ∧
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hp.ne_zero)
  have := Fintype.ofFinite K
  have : CharP K p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact (show 4 ≤ p by omega).trans (Nat.le_self_pow (by omega) p)
  have hinj := conj_injective_statedProj_statedSp (r := 2) (K := K) (le_refl 2) h4
  have hne : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hap : a ^ p = 1 := hord ▸ pow_orderOf_eq_one a
  let ρ : StatedSp 2 K →* MulAut (StatedProj (StatedSp 2 K)) :=
    (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).comp
      (proj 2 K)
  have hker : ρ.ker = spScalars 2 K := by
    rw [← SymplecticHigher.ker_proj]
    ext g
    simp only [MonoidHom.mem_ker, ρ, MonoidHom.comp_apply]
    exact ⟨fun h => hinj (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  have hρ : a ∈ ρ.range := by
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective x
    exact ⟨g, rfl⟩
  obtain ⟨u, hua, hup⟩ := exists_lift_pow_eq_one ρ hp
    (by rw [hker]; exact not_dvd_card_scalars hp hf hK) hρ hap
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hne
    rw [← hua, map_one]
  have hTv : ∀ (γ : K) (w : StatedSp 2 K), γ ≠ 0 →
      spMat w = 1 + γ • Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : K) →
      NormalPrimeComplementsTrivial p (MulAut.conj (proj 2 K w)) :=
    fun γ w hγ hw => symplectic_transvection_std_normalPrimeComplementsTrivial hp hp3 hf hK hγ w
      (hw.trans (by simp [Matrix.smul_single]))
  have hmain : NormalPrimeComplementsTrivial p (MulAut.conj (proj 2 K u)) :=
    normalPrimeComplementsTrivial_of_unipotent hp hp3 hf hK hTv u hup hu1
  have hnpc : NormalPrimeComplementsTrivial p a := by
    rw [← hua]
    exact hmain
  exact ⟨fun S hSC hSn hSp => hnpc B hB S hSC hSn hSp,
    theta_centralizer_eq_bot_of_normalPrimeComplementsTrivial hp hnpc B hB⟩

end CFSG.RankThree.PartOne.KCSymplecticInner
