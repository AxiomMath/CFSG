module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarConfig
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarEnd
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarRealize
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverLin
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverPair
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyHypG0
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpConj
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueInj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.SeitzReduction.LinearPilot
open CFSG.StandardType.TypeAReflOver
open Matrix

private theorem ggGlue_dvd_card_J {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (h : GGTypeANbrCfg p B Bs x L D J n f y K)
    {φ₁ φ₂ : Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G}
    (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    (hJ : (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J) :
    p ∣ Nat.card J := by
  have hp : p.Prime := hC.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 3 ≤ n := hC.three_le
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hN3 : 3 ≤ N + 1 := hC.three_le
  have hFp : p ∣ Nat.card (GaloisField 2 f)ˣ := h.dvd_natCard_units
  obtain ⟨g, hg, hg1, hgp⟩ :=
    exists_orderP_mem_lowerLower (F := GaloisField 2 f) (X := G) (p := p) hFp (m := N)
      (by omega) hC.lifts.ker₁
  have hgJ : g ∈ J := by
    obtain ⟨s, hs⟩ := hg
    rw [← hs, ← hJ]
    exact ⟨slLowerBlockHom N (GaloisField 2 f) s, rfl⟩
  have h1 : orderOf (⟨g, hgJ⟩ : J) = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hgp hg1
  rw [← h1]
  exact orderOf_dvd_natCard _

private theorem ggGlue_mem_ggInduced_J {G : Type} [Group G] {p : ℕ}
    {Bs J : Subgroup G} {n f : ℕ} {x y : G}
    {φ₁ φ₂ : Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G}
    (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    (hJ : (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J)
    (j : Fin n) (hj : j.val + 1 = n) :
    hC.permAut₁ (Equiv.swap j.castSucc j.succ) ∈ ggInduced J Bs := by
  have hn : 3 ≤ n := hC.three_le
  let j' : Fin n := ⟨n - 2, by omega⟩
  have hjs : j'.succ = j.castSucc := by
    apply Fin.ext
    change (j' : Fin n).val + 1 = j.val
    have h1 : (j' : Fin n).val = n - 2 := rfl
    omega
  have hmem : φ₁ (slPerm hC.two (Equiv.swap j.castSucc j.succ)) ∈ J := by
    rw [← hJ]
    refine ⟨slPerm hC.two (Equiv.swap j' j), ?_⟩
    rw [MonoidHom.comp_apply, slLowerBlockHom_slPerm_swap hC.two j' j, hjs]
  exact ggConjAut_mem_ggInduced (H := J) hmem (hC.perm_mem_normalizer₁ _)

theorem GGFarCtx.eq_kThreeRefl_of_cross {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G}
    {K : Subgroup G} (hNC : GGTypeANbrCfg p B Bs x L D J n f y K)
    {φ₁ φ₂ φ₃ : Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G} {y₃ : G}
    (hX : GGFarCtx p Bs φ₁ φ₂ x y) (hX₃ : GGFarCtx p Bs φ₁ φ₃ x y₃) (hL : φ₁.range = L)
    (hJ : (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J)
    (j : Fin n) (hj : j.val + 1 = n) (κ : Additive ↥Bs ≃+ (Fin (n + 1) → ZMod p))
    (hκ₁ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (b : ↥Bs),
      κ (Additive.ofMul (hX.permAut₁ σ b)) = coordPerm p n σ (κ (Additive.ofMul b)))
    (hκ₂ : ∀ b : ↥Bs, κ (Additive.ofMul (hX.permAut₂ (Equiv.swap j.castSucc j.succ) b)) =
      kRefl p n (κ (Additive.ofMul b)))
    (hcomm : ∀ σ : Equiv.Perm (Fin (n + 1)), σ (Fin.last n) = Fin.last n →
      hX₃.permAut₂ (Equiv.swap j.castSucc j.succ) * hX.permAut₁ σ =
        hX.permAut₁ σ * hX₃.permAut₂ (Equiv.swap j.castSucc j.succ))
    (hrne : hX₃.permAut₂ (Equiv.swap j.castSucc j.succ) ≠
      hX.permAut₂ (Equiv.swap j.castSucc j.succ)) :
    p ∣ n + 3 ∧ ∀ b : ↥Bs,
      κ (Additive.ofMul (hX₃.permAut₂ (Equiv.swap j.castSucc j.succ) b)) =
        kThreeRefl p n (κ (Additive.ofMul b)) := by
  classical
  have hp : p.Prime := hX.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 3 ≤ n := hX.three_le
  have hjval : j.val = n - 1 := by omega
  have hNC' := hNC
  obtain ⟨hcfg, -, hInn, hNoTr, htypeA⟩ := hNC'
  obtain ⟨-, -, -, -, hnbr, -, -, hAJ⟩ := htypeA
  have hS : LargeEvenSStar p B x φ₁.range := by
    rw [hL]
    exact hcfg.1.2.2.2.2.2.2.1
  have hxN := hX.centralizer_x_le_normalizer hS
  let j' : Fin n := ⟨n - 2, by omega⟩
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap j.castSucc j.succ
  let t : MulAut ↥Bs := hX.permAut₁ σ
  let bbar : MulAut ↥Bs := hX.permAut₂ σ
  let r : MulAut ↥Bs := hX₃.permAut₂ σ
  let c : MulAut ↥Bs := hX₃.permAut₂ (Equiv.swap j'.castSucc j.succ)
  let w : MulAut ↥Bs := hX.permAut₂ (Equiv.swap j'.castSucc j.succ)
  have hjs : j'.succ = j.castSucc := by
    apply Fin.ext
    change (j' : Fin n).val + 1 = j.val
    have h1 : (j' : Fin n).val = n - 2 := rfl
    omega
  have hjsucc : j.succ = Fin.last n := by
    apply Fin.ext
    change j.val + 1 = n
    exact hj
  have hab : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ (i := j)).ne
  have hja : j'.castSucc ≠ j.castSucc := by
    intro hh
    have h2 : j' = j := Fin.castSucc_injective n hh
    have h3 : (j' : Fin n).val = j.val := congrArg Fin.val h2
    have h4 : (j' : Fin n).val = n - 2 := rfl
    omega
  have hja' : j'.castSucc ≠ j.succ := by
    intro hh
    have h2 : (j'.castSucc : Fin (n + 1)).val = (j.succ : Fin (n + 1)).val :=
      congrArg Fin.val hh
    simp only [Fin.val_castSucc, Fin.val_succ] at h2
    have h4 : (j' : Fin n).val = n - 2 := rfl
    omega
  have hperm₁ : hX₃.permAut₁ = hX.permAut₁ := rfl
  have ht_eq : t = hX₃.permAut₂ (Equiv.swap j'.castSucc j.castSucc) := by
    rw [show t = hX.permAut₁ σ from rfl, ← hperm₁, ← hX₃.permAut_compat j' j, hjs]
  have hctc_perm : Equiv.swap j'.castSucc j.succ * Equiv.swap j'.castSucc j.castSucc *
      Equiv.swap j'.castSucc j.succ = Equiv.swap j.castSucc j.succ := by
    have h1 : j.castSucc ≠ j'.castSucc := hja.symm
    have h := Equiv.swap_mul_swap_mul_swap (x := j.castSucc) (y := j'.castSucc)
      (z := j.succ) h1 hab
    rwa [Equiv.swap_comm j.castSucc j'.castSucc, Equiv.swap_comm j.succ j.castSucc] at h
  have hctc : c * t * c⁻¹ = r := by
    have himg : hX₃.permAut₂ (Equiv.swap j'.castSucc j.succ) *
        hX₃.permAut₂ (Equiv.swap j'.castSucc j.castSucc) *
        hX₃.permAut₂ (Equiv.swap j'.castSucc j.succ) = hX₃.permAut₂ σ := by
      simpa only [map_mul] using congrArg hX₃.permAut₂ hctc_perm
    have hc2 : c * c = 1 := by
      rw [show c = hX₃.permAut₂ (Equiv.swap j'.castSucc j.succ) from rfl, ← map_mul,
        Equiv.swap_mul_self, map_one]
    have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
    rw [hc_inv]
    rw [show c = hX₃.permAut₂ (Equiv.swap j'.castSucc j.succ) from rfl, ht_eq]
    exact himg
  have hwbw_perm : Equiv.swap j'.castSucc j.succ * Equiv.swap j.castSucc j.succ *
      Equiv.swap j'.castSucc j.succ = Equiv.swap j'.castSucc j.castSucc := by
    have h := Equiv.swap_mul_swap_mul_swap (x := j.castSucc) (y := j.succ)
      (z := j'.castSucc) hab hja.symm
    rwa [Equiv.swap_comm j.succ j'.castSucc] at h
  have hwbw : w * bbar * w⁻¹ = t := by
    have himg : hX.permAut₂ (Equiv.swap j'.castSucc j.succ) *
        hX.permAut₂ σ * hX.permAut₂ (Equiv.swap j'.castSucc j.succ) =
        hX.permAut₂ (Equiv.swap j'.castSucc j.castSucc) := by
      simpa only [map_mul] using congrArg hX.permAut₂ hwbw_perm
    have hcompat : hX.permAut₂ (Equiv.swap j'.castSucc j.castSucc) = t := by
      rw [← hX.permAut_compat j' j, hjs]
    have hw2 : w * w = 1 := by
      rw [show w = hX.permAut₂ (Equiv.swap j'.castSucc j.succ) from rfl, ← map_mul,
        Equiv.swap_mul_self, map_one]
    have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    rw [hw_inv]
    rw [show w = hX.permAut₂ (Equiv.swap j'.castSucc j.succ) from rfl,
      show bbar = hX.permAut₂ σ from rfl]
    exact himg.trans hcompat
  have ht2 : t * t = 1 := by
    rw [show t = hX.permAut₁ σ from rfl, ← map_mul, Equiv.swap_mul_self, map_one]
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htJ : t ∈ ggInduced J Bs := ggGlue_mem_ggInduced_J hX hJ j hj
  have ht_top : t ∈ ggInduced ⊤ Bs := by
    obtain ⟨g, hgJ, hgN, hgv⟩ := htJ
    exact ⟨g, Subgroup.mem_top g, hgN, hgv⟩
  have hw_ind : w ∈ ggInduced ⊤ Bs :=
    ggConjAut_mem_ggInduced (H := ⊤)
      (g := φ₂ (slPerm hX.two (Equiv.swap j'.castSucc j.succ))) (Subgroup.mem_top _)
      (hX.perm_mem_normalizer₂ _)
  have hc_ind : c ∈ ggInduced ⊤ Bs :=
    ggConjAut_mem_ggInduced (H := ⊤)
      (g := φ₃ (slPerm hX₃.two (Equiv.swap j'.castSucc j.succ))) (Subgroup.mem_top _)
      (hX₃.perm_mem_normalizer₂ _)
  have hpJ : p ∣ Nat.card J := ggGlue_dvd_card_J hNC hX hJ
  have ht_refl : GGIsReflection p t :=
    hX.permAut₁_swap_isReflection (a := j.castSucc) (b := j.succ) hab
  have hr_refl : GGIsReflection p r :=
    hX₃.permAut₂_swap_isReflection (a := j.castSucc) (b := j.succ) hab
  let Jt : Subgroup G := (blockSpecialLinear
    (K := GaloisField 2 f) ({j.castSucc, j.succ} : Finset (Fin (n + 1)))).map φ₁
  obtain ⟨ht_real, ht_JC, ht_pc, -⟩ :=
    hX.realize_permAut₁_swap hxN (a := j.castSucc) (b := j.succ) hab
  have conj_real : ∀ (u : MulAut ↥Bs), u ∈ ggInduced ⊤ Bs →
      ∀ (s : MulAut ↥Bs) (Js : Subgroup G), GGIsReflection p s → s ∈ ggInduced Js Bs →
        Js ≤ Subgroup.centralizer (ggFixG Bs s : Set G) →
        IsPComponent p (Js.subgroupOf (Subgroup.centralizer (ggFixG Bs s : Set G))) →
        ∃ Js' : Subgroup G, GGIsReflection p (u * s * u⁻¹) ∧
          u * s * u⁻¹ ∈ ggInduced Js' Bs ∧
          Js' ≤ Subgroup.centralizer (ggFixG Bs (u * s * u⁻¹) : Set G) ∧
          IsPComponent p (Js'.subgroupOf
            (Subgroup.centralizer (ggFixG Bs (u * s * u⁻¹) : Set G))) := by
    intro u hu s Js hs hind hJC hpc
    obtain ⟨g, hgN, -, hgu⟩ := exists_ggConjAut_eq_of_mem_ggInduced hu
    have h := ggRealization_conj hp hgN hs hind hJC hpc
    refine ⟨Js.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_⟩
    · rw [← hgu]; exact h.1
    · rw [← hgu]; exact h.2.1
    · rw [← hgu]; exact h.2.2.1
    · rw [← hgu]; exact h.2.2.2
  obtain ⟨Jr, hr_refl', hr_ind, hr_JC, hr_pc⟩ :=
    conj_real c hc_ind t Jt ht_refl ht_real ht_JC ht_pc
  rw [hctc] at hr_refl' hr_ind hr_JC hr_pc
  obtain ⟨Jwr, hwr_refl, hwr_ind, hwr_JC, hwr_pc⟩ :=
    conj_real w hw_ind r Jr hr_refl' hr_ind hr_JC hr_pc
  have hpair1 := ggRealizedRefl_mul_pow_eq_one hLB hcfg hInn hpJ hAJ hnbr
    hwr_refl hwr_ind hwr_JC hwr_pc ht_refl htJ
  have hconj_pow : ∀ (a : MulAut ↥Bs) (k : ℕ), (w * a * w⁻¹) ^ k = 1 → a ^ k = 1 := by
    intro a k hk
    have h1 : (MulAut.conj w) (a ^ k) = 1 := by
      rw [map_pow, MulAut.conj_apply]
      exact hk
    exact (MulAut.conj w).map_eq_one_iff.mp h1
  have hwt : w⁻¹ * t = bbar * w⁻¹ := by
    rw [← hwbw]
    group
  have hwrw : (w * r * w⁻¹) * t = w * (r * bbar) * w⁻¹ := by
    calc (w * r * w⁻¹) * t = w * r * (w⁻¹ * t) := by group
      _ = w * r * (bbar * w⁻¹) := by rw [hwt]
      _ = w * (r * bbar) * w⁻¹ := by group
  have hpairr : (r * bbar) ^ 2 = 1 ∨ (r * bbar) ^ 3 = 1 := by
    rcases hpair1 with h2 | h3
    · left
      refine hconj_pow (r * bbar) 2 ?_
      rwa [hwrw] at h2
    · right
      refine hconj_pow (r * bbar) 3 ?_
      rwa [hwrw] at h3
  obtain ⟨Jtrt, htrt_refl, htrt_ind, htrt_JC, htrt_pc⟩ :=
    conj_real t ht_top r Jr hr_refl' hr_ind hr_JC hr_pc
  obtain ⟨Jwtrt, hwtrt_refl, hwtrt_ind, hwtrt_JC, hwtrt_pc⟩ :=
    conj_real w hw_ind (t * r * t⁻¹) Jtrt htrt_refl htrt_ind htrt_JC htrt_pc
  have hpair2 := ggRealizedRefl_mul_pow_eq_one hLB hcfg hInn hpJ hAJ hnbr
    hwtrt_refl hwtrt_ind hwtrt_JC hwtrt_pc ht_refl htJ
  have hwrwt : (w * (t * r * t⁻¹) * w⁻¹) * t =
      w * ((t * r * t⁻¹) * bbar) * w⁻¹ := by
    calc (w * (t * r * t⁻¹) * w⁻¹) * t = w * (t * r * t⁻¹) * (w⁻¹ * t) := by group
      _ = w * (t * r * t⁻¹) * (bbar * w⁻¹) := by rw [hwt]
      _ = w * ((t * r * t⁻¹) * bbar) * w⁻¹ := by group
  have hpairr'' : ((t * r * t⁻¹) * bbar) ^ 2 = 1 ∨
      ((t * r * t⁻¹) * bbar) ^ 3 = 1 := by
    rcases hpair2 with h2 | h3
    · left
      refine hconj_pow ((t * r * t⁻¹) * bbar) 2 ?_
      rwa [hwrwt] at h2
    · right
      refine hconj_pow ((t * r * t⁻¹) * bbar) 3 ?_
      rwa [hwrwt] at h3
  have hpairr' : ((t * r * t) * bbar) ^ 2 = 1 ∨ ((t * r * t) * bbar) ^ 3 = 1 := by
    have h1 : t * r * t⁻¹ = t * r * t := by rw [ht_inv]
    rw [← h1]
    exact hpairr''
  have hbraid_perm : Equiv.swap j.castSucc j.succ * Equiv.swap j'.castSucc j.castSucc *
      Equiv.swap j.castSucc j.succ = Equiv.swap j'.castSucc j.castSucc *
        Equiv.swap j.castSucc j.succ * Equiv.swap j'.castSucc j.castSucc := by
    have h1 : Equiv.swap j.castSucc j.succ * Equiv.swap j'.castSucc j.castSucc *
        Equiv.swap j.castSucc j.succ = Equiv.swap j'.castSucc j.succ := by
      have h := Equiv.swap_mul_swap_mul_swap (x := j'.castSucc) (y := j.castSucc)
        (z := j.succ) hja hja'
      rwa [Equiv.swap_comm j.succ j'.castSucc] at h
    have h2 : Equiv.swap j'.castSucc j.castSucc * Equiv.swap j.castSucc j.succ *
        Equiv.swap j'.castSucc j.castSucc = Equiv.swap j'.castSucc j.succ := by
      have h := Equiv.swap_mul_swap_mul_swap (x := j.succ) (y := j.castSucc)
        (z := j'.castSucc) (Fin.castSucc_lt_succ (i := j)).ne.symm hja'.symm
      rwa [Equiv.swap_comm j.castSucc j'.castSucc, Equiv.swap_comm j.succ j.castSucc] at h
    rw [h1, h2]
  have hbraid : r * t * r = t * r * t := by
    have himg : hX₃.permAut₂ σ * hX₃.permAut₂ (Equiv.swap j'.castSucc j.castSucc) *
        hX₃.permAut₂ σ = hX₃.permAut₂ (Equiv.swap j'.castSucc j.castSucc) *
          hX₃.permAut₂ σ * hX₃.permAut₂ (Equiv.swap j'.castSucc j.castSucc) := by
      simpa only [map_mul] using congrArg hX₃.permAut₂ hbraid_perm
    calc r * t * r = hX₃.permAut₂ σ * hX₃.permAut₂ (Equiv.swap j'.castSucc j.castSucc) *
        hX₃.permAut₂ σ := by rw [show r = hX₃.permAut₂ σ from rfl, ht_eq]
      _ = hX₃.permAut₂ (Equiv.swap j'.castSucc j.castSucc) * hX₃.permAut₂ σ *
        hX₃.permAut₂ (Equiv.swap j'.castSucc j.castSucc) := himg
      _ = t * r * t := by rw [show r = hX₃.permAut₂ σ from rfl, ht_eq]
  have hrnet : r ≠ t := by
    intro hh
    apply hX₃.permAut₂_swap_ne_x hj
    rw [show hX₃.permAut₂ σ = hX.permAut₁ σ from hh]
    exact hX.permAut₁_fix_x σ
  have hr_ind' : r ∈ ggInduced ⊤ Bs := by
    obtain ⟨g, hgJ, hgN, hgv⟩ := hr_ind
    exact ⟨g, Subgroup.mem_top g, hgN, hgv⟩
  exact hX.eq_kThreeRefl_of_pairings j hj κ hκ₁ hκ₂ r hr_refl hr_ind' hcomm hbraid hrnet
    hpairr hpairr' hrne hNoTr

end CFSG.StandardType

end
