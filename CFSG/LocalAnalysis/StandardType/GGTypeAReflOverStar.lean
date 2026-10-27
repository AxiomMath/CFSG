module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarConfig
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarEnd
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarRealize
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverLin
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverPair
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyHypG0
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpConj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.SeitzReduction.LinearPilot
open CFSG.StandardType.TypeAReflOver
open Matrix

private theorem ggStar_dvd_card_J {G : Type} [Group G] [Finite G] {p : ℕ}
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

private theorem ggStar_mem_ggInduced_J {G : Type} [Group G] {p : ℕ}
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

theorem GGFarCtx.star_dichotomy {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G}
    {K : Subgroup G} (h : GGTypeANbrCfg p B Bs x L D J n f y K)
    {φ₁ φ₂ : Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G}
    (hC : GGFarCtx p Bs φ₁ φ₂ x y) (hL : φ₁.range = L) (hK : φ₂.range = K)
    (hJ : (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J)
    (j : Fin n) (hj : j.val + 1 = n) (κ : Additive ↥Bs ≃+ (Fin (n + 1) → ZMod p))
    (hκ₁ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (b : ↥Bs),
      κ (Additive.ofMul (hC.permAut₁ σ b)) = coordPerm p n σ (κ (Additive.ofMul b)))
    (hκ₂ : ∀ b : ↥Bs, κ (Additive.ofMul (hC.permAut₂ (Equiv.swap j.castSucc j.succ) b)) =
      kRefl p n (κ (Additive.ofMul b)))
    {m : ℕ} (E : Equiv.Perm (Fin (m + 1)) →* MulAut ↥Bs) (hEinj : Function.Injective E)
    (hEind : ∀ σ, E σ ∈ ggInduced ⊤ Bs)
    (hErefl : ∀ a b : Fin (m + 1), a ≠ b → GGIsReflection p (E (Equiv.swap a b)))
    (ι : Fin (n + 1) → Fin (m + 1)) (hιinj : Function.Injective ι)
    (π : Equiv.Perm (Fin (n + 1)) → Equiv.Perm (Fin (m + 1)))
    (hπ : ∀ σ, E (π σ) = hC.permAut₁ σ) (hπι : ∀ σ a, π σ (ι a) = ι (σ a))
    (hπz : ∀ σ w, w ∉ Set.range ι → π σ w = w) {z : Fin (m + 1)} (hz : z ∉ Set.range ι) :
    E (Equiv.swap (ι (Fin.last n)) z) = hC.permAut₂ (Equiv.swap j.castSucc j.succ) ∨
      (p ∣ n + 3 ∧ ∀ b : ↥Bs,
        κ (Additive.ofMul (E (Equiv.swap (ι (Fin.last n)) z) b)) =
          kThreeRefl p n (κ (Additive.ofMul b))) := by
  classical
  have hp : p.Prime := hC.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 3 ≤ n := hC.three_le
  have hjval : j.val = n - 1 := by omega
  have h' := h
  obtain ⟨hcfg, -, hInn, hNoTr, htypeA⟩ := h'
  obtain ⟨-, -, -, -, hnbr, -, -, hAJ⟩ := htypeA
  have hS : LargeEvenSStar p B x φ₁.range := by
    rw [hL]
    exact hcfg.1.2.2.2.2.2.2.1
  have hxN := hC.centralizer_x_le_normalizer hS
  let A : Fin (m + 1) := ι j.castSucc
  let B : Fin (m + 1) := ι (Fin.last n)
  let C : Fin (m + 1) := z
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap j.castSucc j.succ
  let t : MulAut ↥Bs := hC.permAut₁ σ
  let r : MulAut ↥Bs := E (Equiv.swap B C)
  let c : MulAut ↥Bs := E (Equiv.swap A C)
  let j' : Fin n := ⟨n - 2, by omega⟩
  let w : MulAut ↥Bs := hC.permAut₂ (Equiv.swap j'.castSucc j.succ)
  have hAB : A ≠ B := fun hh => Fin.castSucc_ne_last j (hιinj hh)
  have hAC : A ≠ C := fun hh => hz ⟨j.castSucc, hh⟩
  have hCB : C ≠ B := fun hh => hz ⟨Fin.last n, hh.symm⟩
  have hBA : B ≠ A := hAB.symm
  have hCA : C ≠ A := hAC.symm
  have hBC : B ≠ C := hCB.symm
  have hjs : j'.succ = j.castSucc := by
    apply Fin.ext
    change (j' : Fin n).val + 1 = j.val
    have h1 : (j' : Fin n).val = n - 2 := rfl
    omega
  have hjsucc : j.succ = Fin.last n := by
    apply Fin.ext
    change j.val + 1 = n
    exact hj
  have hπswap : ∀ {a b : Fin (n + 1)}, a ≠ b →
      π (Equiv.swap a b) = Equiv.swap (ι a) (ι b) := by
    intro a b hab
    ext x
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨y, rfl⟩ := hx
      rw [hπι (Equiv.swap a b) y, Function.Injective.swap_apply hιinj a b y]
    · rw [hπz (Equiv.swap a b) x hx]
      have h1 : x ≠ ι a := fun hh => hx ⟨a, hh.symm⟩
      have h2 : x ≠ ι b := fun hh => hx ⟨b, hh.symm⟩
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hπσ : π σ = Equiv.swap A B := by
    show π (Equiv.swap j.castSucc j.succ) = Equiv.swap (ι j.castSucc) (ι (Fin.last n))
    have h := hπswap (Fin.castSucc_lt_succ (i := j)).ne
    rw [h, hjsucc]
  have ht_eq : hC.permAut₁ σ = E (Equiv.swap A B) := by
    rw [← hπ σ, hπσ]
  have ht2 : t * t = 1 := by
    rw [show t = E (Equiv.swap A B) from ht_eq, ← map_mul, Equiv.swap_mul_self, map_one]
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hc2 : c * c = 1 := by
    rw [show c = E (Equiv.swap A C) from rfl, ← map_mul, Equiv.swap_mul_self, map_one]
  have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hw2 : w * w = 1 := by
    rw [show w = hC.permAut₂ (Equiv.swap j'.castSucc j.succ) from rfl, ← map_mul,
      Equiv.swap_mul_self, map_one]
  have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have htJ : t ∈ ggInduced J Bs := ggStar_mem_ggInduced_J hC hJ j hj
  have ht_top : t ∈ ggInduced ⊤ Bs := by
    obtain ⟨g, hgJ, hgN, hgv⟩ := htJ
    exact ⟨g, Subgroup.mem_top g, hgN, hgv⟩
  have hw_ind : w ∈ ggInduced ⊤ Bs := by
    exact ggConjAut_mem_ggInduced (H := ⊤)
      (g := φ₂ (slPerm hC.two (Equiv.swap j'.castSucc j.succ))) (Subgroup.mem_top _)
      (hC.perm_mem_normalizer₂ _)
  have hc_ind : c ∈ ggInduced ⊤ Bs := hEind (Equiv.swap A C)
  have hpJ : p ∣ Nat.card J := ggStar_dvd_card_J h hC hJ
  have hperm_ct : Equiv.swap A C * Equiv.swap B C * Equiv.swap A C = Equiv.swap A B := by
    have h := Equiv.swap_mul_swap_mul_swap (x := B) (y := C) (z := A) hBC hBA
    rwa [Equiv.swap_comm C A] at h
  have hcrc : c * r * c = t := by
    rw [show t = E (Equiv.swap A B) from ht_eq, show c = E (Equiv.swap A C) from rfl,
      show r = E (Equiv.swap B C) from rfl]
    simpa only [map_mul] using congrArg E hperm_ct
  have hctc : c * t * c⁻¹ = r := by
    have h1 : c * t * c = r := by
      calc c * t * c = c * (c * r * c) * c := by rw [hcrc]
        _ = (c * c) * r * (c * c) := by group
        _ = r := by rw [hc2, one_mul, mul_one]
    rw [hc_inv]
    exact h1
  have hcb : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ (i := j)).ne
  have hca : j.castSucc ≠ j'.castSucc := by
    intro hh
    have h1 : j = j' := Fin.castSucc_injective n hh
    have h2 : j.val = j'.val := congrArg Fin.val h1
    simp only [j'] at h2
    omega
  have hwbw : w * hC.permAut₂ σ * w⁻¹ = t := by
    have hperm : Equiv.swap j'.castSucc j.succ * Equiv.swap j.castSucc j.succ *
        Equiv.swap j'.castSucc j.succ = Equiv.swap j'.castSucc j.castSucc := by
      have h := Equiv.swap_mul_swap_mul_swap (x := j.castSucc) (y := j.succ) (z := j'.castSucc)
        hcb hca
      rwa [Equiv.swap_comm j.succ j'.castSucc] at h
    have himg : hC.permAut₂ (Equiv.swap j'.castSucc j.succ) *
        hC.permAut₂ (Equiv.swap j.castSucc j.succ) *
        hC.permAut₂ (Equiv.swap j'.castSucc j.succ) =
        hC.permAut₂ (Equiv.swap j'.castSucc j.castSucc) := by
      simpa only [map_mul] using congrArg hC.permAut₂ hperm
    have hcompat : hC.permAut₂ (Equiv.swap j'.castSucc j.castSucc) = t := by
      rw [← hC.permAut_compat j' j, hjs]
    calc w * hC.permAut₂ σ * w⁻¹
        = hC.permAut₂ (Equiv.swap j'.castSucc j.succ) *
            hC.permAut₂ (Equiv.swap j.castSucc j.succ) *
            hC.permAut₂ (Equiv.swap j'.castSucc j.succ) := by
          rw [show w = hC.permAut₂ (Equiv.swap j'.castSucc j.succ) from rfl, hw_inv,
            show σ = Equiv.swap j.castSucc j.succ from rfl]
      _ = hC.permAut₂ (Equiv.swap j'.castSucc j.castSucc) := himg
      _ = t := hcompat
  have hwt : w⁻¹ * t = hC.permAut₂ σ * w⁻¹ := by
    rw [← hwbw]
    group
  have hcomm : ∀ σ' : Equiv.Perm (Fin (n + 1)), σ' (Fin.last n) = Fin.last n →
      r * hC.permAut₁ σ' = hC.permAut₁ σ' * r := by
    intro σ' hσ'
    have hfix1 : π σ' (ι (Fin.last n)) = ι (Fin.last n) := by
      rw [hπι σ' (Fin.last n), hσ']
    have hfix2 : π σ' z = z := hπz σ' z hz
    have hconj : π σ' * Equiv.swap (ι (Fin.last n)) z * (π σ')⁻¹ =
        Equiv.swap (ι (Fin.last n)) z := by
      rw [← Equiv.swap_apply_apply (π σ') (ι (Fin.last n)) z, hfix1, hfix2]
    have hEconj : E (π σ') * E (Equiv.swap (ι (Fin.last n)) z) * (E (π σ'))⁻¹ =
        E (Equiv.swap (ι (Fin.last n)) z) := by
      simpa only [map_mul, map_inv] using congrArg E hconj
    have hswap : E (Equiv.swap (ι (Fin.last n)) z) * E (π σ') =
        E (π σ') * E (Equiv.swap (ι (Fin.last n)) z) := by
      have h2 := congrArg (fun v => v * E (π σ')) hEconj
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h2.symm
    calc r * hC.permAut₁ σ'
        = E (Equiv.swap B C) * E (π σ') := by rw [hπ σ']
      _ = E (π σ') * E (Equiv.swap B C) := hswap
      _ = hC.permAut₁ σ' * r := by rw [hπ σ']
  have hbraidP : Equiv.swap B C * Equiv.swap A B * Equiv.swap B C =
      Equiv.swap A B * Equiv.swap B C * Equiv.swap A B := by
    have h1 : Equiv.swap B C * Equiv.swap A B * Equiv.swap B C = Equiv.swap C A :=
      Equiv.swap_mul_swap_mul_swap hAB hAC
    have h2 : Equiv.swap A B * Equiv.swap B C * Equiv.swap A B = Equiv.swap A C := by
      have h := Equiv.swap_mul_swap_mul_swap (x := C) (y := B) (z := A) hCB hCA
      rwa [Equiv.swap_comm B A, Equiv.swap_comm C B] at h
    rw [h1, h2, Equiv.swap_comm C A]
  have hbraid : r * hC.permAut₁ σ * r = hC.permAut₁ σ * r * hC.permAut₁ σ := by
    have h := congrArg E hbraidP
    rw [show r = E (Equiv.swap B C) from rfl, ht_eq]
    simpa only [map_mul] using h
  have hrnet : r ≠ hC.permAut₁ σ := by
    intro hh
    have hEeq : E (Equiv.swap B C) = E (Equiv.swap A B) := by
      rw [← show r = E (Equiv.swap B C) from rfl, hh, ht_eq]
    have hperm : Equiv.swap B C = Equiv.swap A B := hEinj hEeq
    have hCA' : C = A := by
      have h1 := congrArg (fun e : Equiv.Perm (Fin (m + 1)) => e B) hperm
      simpa using h1
    exact hAC hCA'.symm
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
  have hab : j.castSucc ≠ j.succ := hcb
  let Jt : Subgroup G := (blockSpecialLinear
    (K := GaloisField 2 f) ({j.castSucc, j.succ} : Finset (Fin (n + 1)))).map φ₁
  obtain ⟨ht_real, ht_JC, ht_pc, -⟩ :=
    hC.realize_permAut₁_swap hxN (a := j.castSucc) (b := j.succ) hab
  have ht_refl : GGIsReflection p t :=
    hC.permAut₁_swap_isReflection (a := j.castSucc) (b := j.succ) hab
  obtain ⟨Jr, hr_refl, hr_ind, hr_JC, hr_pc⟩ :=
    conj_real c hc_ind t Jt ht_refl ht_real ht_JC ht_pc
  rw [hctc] at hr_refl hr_ind hr_JC hr_pc
  obtain ⟨Jwr, hwr_refl, hwr_ind, hwr_JC, hwr_pc⟩ :=
    conj_real w hw_ind r Jr hr_refl hr_ind hr_JC hr_pc
  have hpair1 := ggRealizedRefl_mul_pow_eq_one hLB hcfg hInn hpJ hAJ hnbr
    hwr_refl hwr_ind hwr_JC hwr_pc ht_refl htJ
  have hconj_pow : ∀ (a : MulAut ↥Bs) (k : ℕ), (w * a * w⁻¹) ^ k = 1 → a ^ k = 1 := by
    intro a k hk
    have h1 : (MulAut.conj w) (a ^ k) = 1 := by
      rw [map_pow, MulAut.conj_apply]
      exact hk
    exact (MulAut.conj w).map_eq_one_iff.mp h1
  have hwrw : (w * r * w⁻¹) * t = w * (r * hC.permAut₂ σ) * w⁻¹ := by
    calc (w * r * w⁻¹) * t = w * r * (w⁻¹ * t) := by group
      _ = w * r * (hC.permAut₂ σ * w⁻¹) := by rw [hwt]
      _ = w * (r * hC.permAut₂ σ) * w⁻¹ := by group
  have hpairr : (r * hC.permAut₂ σ) ^ 2 = 1 ∨ (r * hC.permAut₂ σ) ^ 3 = 1 := by
    rcases hpair1 with h2 | h3
    · left
      refine hconj_pow (r * hC.permAut₂ σ) 2 ?_
      rwa [hwrw] at h2
    · right
      refine hconj_pow (r * hC.permAut₂ σ) 3 ?_
      rwa [hwrw] at h3
  obtain ⟨Jtrt, htrt_refl, htrt_ind, htrt_JC, htrt_pc⟩ :=
    conj_real t ht_top r Jr hr_refl hr_ind hr_JC hr_pc
  obtain ⟨Jwtrt, hwtrt_refl, hwtrt_ind, hwtrt_JC, hwtrt_pc⟩ :=
    conj_real w hw_ind (t * r * t⁻¹) Jtrt htrt_refl htrt_ind htrt_JC htrt_pc
  have hpair2 := ggRealizedRefl_mul_pow_eq_one hLB hcfg hInn hpJ hAJ hnbr
    hwtrt_refl hwtrt_ind hwtrt_JC hwtrt_pc ht_refl htJ
  have hwrwt : (w * (t * r * t⁻¹) * w⁻¹) * t =
      w * ((t * r * t⁻¹) * hC.permAut₂ σ) * w⁻¹ := by
    calc (w * (t * r * t⁻¹) * w⁻¹) * t = w * (t * r * t⁻¹) * (w⁻¹ * t) := by group
      _ = w * (t * r * t⁻¹) * (hC.permAut₂ σ * w⁻¹) := by rw [hwt]
      _ = w * ((t * r * t⁻¹) * hC.permAut₂ σ) * w⁻¹ := by group
  have hpairr'' : ((t * r * t⁻¹) * hC.permAut₂ σ) ^ 2 = 1 ∨
      ((t * r * t⁻¹) * hC.permAut₂ σ) ^ 3 = 1 := by
    rcases hpair2 with h2 | h3
    · left
      refine hconj_pow ((t * r * t⁻¹) * hC.permAut₂ σ) 2 ?_
      rwa [hwrwt] at h2
    · right
      refine hconj_pow ((t * r * t⁻¹) * hC.permAut₂ σ) 3 ?_
      rwa [hwrwt] at h3
  have hpairr' : ((t * r * t) * hC.permAut₂ σ) ^ 2 = 1 ∨
      ((t * r * t) * hC.permAut₂ σ) ^ 3 = 1 := by
    have h1 : t * r * t⁻¹ = t * r * t := by rw [ht_inv]
    rw [← h1]
    exact hpairr''
  have hr_ind' : r ∈ ggInduced ⊤ Bs := by
    obtain ⟨g, hgJ, hgN, hgv⟩ := hr_ind
    exact ⟨g, Subgroup.mem_top g, hgN, hgv⟩
  by_cases hrne : r = hC.permAut₂ σ
  · exact Or.inl hrne
  · right
    exact hC.eq_kThreeRefl_of_pairings j hj κ hκ₁ hκ₂ r hr_refl hr_ind' hcomm hbraid hrnet
      hpairr hpairr' hrne hNoTr

end CFSG.StandardType

end
