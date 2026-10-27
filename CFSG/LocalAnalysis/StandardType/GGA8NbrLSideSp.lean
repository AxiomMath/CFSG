module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordDefsB
public import CFSG.LocalAnalysis.StandardType.GGA8NbrSpLift
public import CFSG.LocalAnalysis.StandardType.GGA8NbrSpFrame
public import CFSG.LocalAnalysis.StandardType.GGA8NbrSpJClass
public import CFSG.LocalAnalysis.StandardType.GGA8NbrSpJShape
public import CFSG.LocalAnalysis.StandardType.GGA8NbrSpJSp4
public import CFSG.LocalAnalysis.StandardType.GGA8NbrSpJSiegel
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGFieldNbrTableB
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrCentralizer
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType.A8Coord

open Certificates.A8Nbr476 CFSG.Assembly CFSG.Open CFSG.StandardType Matrix

private def a8ja_etaSign : Fin 3 → (ZMod 7)ˣ := ![1, 1, -1]

private theorem a8ja_etaSign_mem (i : Fin 3) : a8ja_etaSign i ∈ CoordSp.signs 7 := by
  fin_cases i <;> simp [a8ja_etaSign, CoordSp.mem_signs]

private theorem a8ja_symm_zero (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) : σ.symm 0 = 0 := by
  have h := congrArg σ.symm hσ
  simpa using h.symm

private def a8ja_perm4Fun (π : Equiv.Perm (Fin 3)) : Fin 4 → Fin 4 :=
  Fin.cases 0 (fun i => (π.symm i).succ)

private theorem a8ja_perm4Fun_zero (π : Equiv.Perm (Fin 3)) : a8ja_perm4Fun π 0 = 0 := rfl

private theorem a8ja_perm4Fun_succ (π : Equiv.Perm (Fin 3)) (i : Fin 3) :
    a8ja_perm4Fun π i.succ = (π.symm i).succ := rfl

private theorem a8ja_perm4Fun_injective (π : Equiv.Perm (Fin 3)) :
    Function.Injective (a8ja_perm4Fun π) := by
  intro a b hab
  revert b
  refine Fin.cases ?_ ?_ a
  · intro b
    refine Fin.cases ?_ ?_ b
    · intro _
      rfl
    · intro j h
      rw [a8ja_perm4Fun_zero, a8ja_perm4Fun_succ] at h
      exact absurd h.symm (Fin.succ_ne_zero (π.symm j))
  · intro i b
    refine Fin.cases ?_ ?_ b
    · intro h
      rw [a8ja_perm4Fun_zero, a8ja_perm4Fun_succ] at h
      exact absurd h (Fin.succ_ne_zero (π.symm i))
    · intro j h
      rw [a8ja_perm4Fun_succ, a8ja_perm4Fun_succ] at h
      congr 1
      exact π.symm.injective (Fin.succ_inj.mp h)

private theorem a8ja_perm4Fun_surjective (π : Equiv.Perm (Fin 3)) :
    Function.Surjective (a8ja_perm4Fun π) := by
  intro b
  refine Fin.cases ?_ ?_ b
  · exact ⟨0, a8ja_perm4Fun_zero π⟩
  · intro j
    refine ⟨(π j).succ, ?_⟩
    rw [a8ja_perm4Fun_succ, Equiv.symm_apply_apply]

private noncomputable def a8ja_perm4 (π : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (a8ja_perm4Fun π) ⟨a8ja_perm4Fun_injective π, a8ja_perm4Fun_surjective π⟩

private theorem a8ja_perm4_zero (π : Equiv.Perm (Fin 3)) : a8ja_perm4 π 0 = 0 :=
  a8ja_perm4Fun_zero π

private theorem a8ja_perm4_succ (π : Equiv.Perm (Fin 3)) (i : Fin 3) :
    a8ja_perm4 π i.succ = (π.symm i).succ :=
  a8ja_perm4Fun_succ π i

private theorem a8ja_perm4_symm_zero (π : Equiv.Perm (Fin 3)) : (a8ja_perm4 π).symm 0 = 0 := by
  rw [Equiv.symm_apply_eq, a8ja_perm4_zero]

private theorem a8ja_perm4_symm_succ (π : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (a8ja_perm4 π).symm i.succ = (π i).succ := by
  exact (Equiv.symm_apply_eq (a8ja_perm4 π)).mpr (by
    rw [a8ja_perm4_succ, Equiv.symm_apply_apply])

private theorem a8ja_vecMul_a8PermMat (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ZMod 7) (j : Fin 4) :
    vecMul v (a8PermMat σ) j = v (σ.symm j) := by
  have h : a8PermMat σ = σ.permMatrix (ZMod 7) := by
    ext i j
    simp [a8PermMat, Equiv.Perm.permMatrix, eq_comm]
  rw [h, Matrix.vecMul_permMatrix]
  rfl

private theorem a8ja_vecMul_perm4 (π : Equiv.Perm (Fin 3)) (s : Fin 3 → ZMod 7) (k : ℕ) :
    vecMul (Fin.cons (k : ZMod 7) s : Fin 4 → ZMod 7) (a8PermMat (a8ja_perm4 π)) =
      Fin.cons (k : ZMod 7) (s ∘ π) := by
  funext j
  rw [a8ja_vecMul_a8PermMat]
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [a8ja_perm4_symm_zero, Fin.cons_zero, Fin.cons_zero]
  · rw [a8ja_perm4_symm_succ, Fin.cons_succ, Fin.cons_succ]
    rfl

private noncomputable def a8ja_permSuccFun (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) :
    Fin 3 → Fin 3 :=
  fun i => Fin.pred (σ.symm i.succ) (by
    intro h
    have h1 : σ.symm i.succ = σ.symm 0 := by rw [h, a8ja_symm_zero σ hσ]
    exact Fin.succ_ne_zero i (σ.symm.injective h1))

private theorem a8ja_permSuccFun_injective (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) :
    Function.Injective (a8ja_permSuccFun σ hσ) := by
  intro i j hij
  have h2 : σ.symm i.succ = σ.symm j.succ := by
    have := congrArg Fin.succ hij
    simpa only [a8ja_permSuccFun, Fin.succ_pred] using this
  exact Fin.succ_inj.mp (σ.symm.injective h2)

private theorem a8ja_permSuccFun_surjective (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) :
    Function.Surjective (a8ja_permSuccFun σ hσ) := by
  intro j
  refine ⟨Fin.pred (σ j.succ) (by
      intro h
      have h1 : σ j.succ = σ 0 := by rw [h, hσ]
      exact Fin.succ_ne_zero j (σ.injective h1)), ?_⟩
  simp only [a8ja_permSuccFun, Fin.succ_pred, Equiv.symm_apply_apply, Fin.pred_succ]

private noncomputable def a8ja_permSucc (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) :
    Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (a8ja_permSuccFun σ hσ)
    ⟨a8ja_permSuccFun_injective σ hσ, a8ja_permSuccFun_surjective σ hσ⟩

private theorem a8ja_permSucc_apply (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) (i : Fin 3) :
    a8ja_permSucc σ hσ i = a8ja_permSuccFun σ hσ i := rfl

private theorem a8ja_permSucc_succ (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) (i : Fin 3) :
    (a8ja_permSucc σ hσ i).succ = σ.symm i.succ := by
  rw [a8ja_permSucc_apply]
  show Fin.succ (Fin.pred (σ.symm i.succ) _) = σ.symm i.succ
  rw [Fin.succ_pred]

private theorem a8ja_permSucc_symm (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) (i : Fin 3) :
    ((a8ja_permSucc σ hσ).symm i).succ = σ i.succ := by
  have h := a8ja_permSucc_succ σ hσ ((a8ja_permSucc σ hσ).symm i)
  rw [Equiv.apply_symm_apply] at h
  have h2 := congrArg σ h
  rw [Equiv.apply_symm_apply] at h2
  exact h2.symm

private theorem a8ja_perm4_permSucc (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) :
    a8ja_perm4 (a8ja_permSucc σ hσ) = σ := by
  apply Equiv.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [a8ja_perm4_zero, hσ]
  · rw [a8ja_perm4_succ, a8ja_permSucc_symm]

private theorem a8ja_cons_add_nsmul_single (k : ℕ) (s : Fin 3 → ZMod 7) :
    (Fin.cons 0 s : Fin 4 → ZMod 7) + k • (Pi.single 0 1 : Fin 4 → ZMod 7) =
      Fin.cons (k : ZMod 7) s := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [Pi.add_apply, Fin.cons_zero, Pi.smul_apply, Pi.single_eq_same, Fin.cons_zero]
    simp [nsmul_eq_mul]
  · rw [Pi.add_apply, Fin.cons_succ, Pi.smul_apply,
      Pi.single_eq_of_ne (Fin.succ_ne_zero i), Fin.cons_succ]
    simp

private theorem a8ja_vecMul_signThree (v : Fin 4 → ZMod 7) :
    vecMul v a8SignThree =
      Fin.cons (v 0) (fun i : Fin 3 => (a8ja_etaSign i : ZMod 7) * v i.succ) := by
  funext j
  fin_cases j
  · change (v ᵥ* a8SignThree) 0 =
        ((Fin.cons (v 0) (fun i : Fin 3 => (a8ja_etaSign i : ZMod 7) * v i.succ) :
          Fin 4 → ZMod 7) 0)
    simp [a8SignThree, a8ja_etaSign, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
      Matrix.diagonal, Fin.cons_zero]
  · change (v ᵥ* a8SignThree) 1 =
        ((Fin.cons (v 0) (fun i : Fin 3 => (a8ja_etaSign i : ZMod 7) * v i.succ) :
          Fin 4 → ZMod 7) 1)
    rw [show (1 : Fin 4) = (0 : Fin 3).succ from rfl, Fin.cons_succ]
    simp [a8SignThree, a8ja_etaSign, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.diagonal]
  · change (v ᵥ* a8SignThree) 2 =
        ((Fin.cons (v 0) (fun i : Fin 3 => (a8ja_etaSign i : ZMod 7) * v i.succ) :
          Fin 4 → ZMod 7) 2)
    rw [show (2 : Fin 4) = (1 : Fin 3).succ from rfl, Fin.cons_succ]
    simp [a8SignThree, a8ja_etaSign, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.diagonal]
  · change (v ᵥ* a8SignThree) 3 =
        ((Fin.cons (v 0) (fun i : Fin 3 => (a8ja_etaSign i : ZMod 7) * v i.succ) :
          Fin 4 → ZMod 7) 3)
    rw [show (3 : Fin 4) = (2 : Fin 3).succ from rfl, Fin.cons_succ]
    simp [a8SignThree, a8ja_etaSign, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.diagonal]

private theorem a8ja_centralizer_inf_eq {G : Type} [Group G] {L D : Subgroup G} {x y e : G}
    {k : ℕ} (hD : D = Subgroup.closure ({x, y} : Set G)) (hy : y = e * x ^ k)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (heL : e ∈ L) :
    L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({e} : Set G) := by
  apply le_antisymm
  · rintro l ⟨hlL, hlD⟩
    refine ⟨hlL, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hly : l * y = y * l := by
      have h1 : l ∈ Subgroup.centralizer ({x, y} : Set G) := by
        rwa [hD, Subgroup.centralizer_closure] at hlD
      exact (Subgroup.mem_centralizer_iff.mp h1 y (by simp)).symm
    have hlx : l * x = x * l := Subgroup.mem_centralizer_singleton_iff.mp (hLx hlL)
    have he_eq : e = y * (x ^ k)⁻¹ := by rw [hy]; group
    rw [he_eq]
    exact (show Commute l y from hly).mul_right
      (((show Commute l x from hlx).pow_right k).inv_right)
  · rintro l ⟨hlL, hle⟩
    refine ⟨hlL, ?_⟩
    rw [hD, Subgroup.centralizer_closure]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro g hg
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hgx | hgy
    · rw [hgx]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hLx hlL)).symm
    · rw [hgy]
      have hle' : l * e = e * l := Subgroup.mem_centralizer_singleton_iff.mp hle
      have hlx : l * x = x * l := Subgroup.mem_centralizer_singleton_iff.mp (hLx hlL)
      have hly : l * y = y * l := by
        rw [hy]
        exact (show Commute l e from hle').mul_right ((show Commute l x from hlx).pow_right k)
      exact hly.symm

private theorem a8ja_not_mem_zpowers {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 7 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 7 B x D J y K) : x ∉ Subgroup.zpowers y := by
  intro hx
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hDle : D ≤ Subgroup.zpowers y := by
    rw [hnb.2.1, Subgroup.closure_le]
    rintro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hzx | hzy
    · rw [hzx]; exact hx
    · rw [hzy]; exact Subgroup.mem_zpowers _
  have hy7 : y ^ 7 = 1 := hcfg.2.1.2.1.2 y hyBs
  have hord : orderOf y ≤ 7 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hy7)
  have hle : Nat.card D ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hDle
  rw [hcfg.2.2.1.2.2.1, Nat.card_zpowers] at hle
  omega

private theorem a8ja_conjAut_perm {G : Type} [Group G] {Bs L J : Subgroup G} {x : G}
    (hxB : x ∈ Bs) (ιB : Additive ↥Bs ≃+ (Fin 4 → ZMod 7))
    (hιBx : ιB (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)) = Pi.single 0 1)
    {ιE : Multiplicative (Fin 3 → ZMod 7) →* G}
    (hcoord : ∀ t : Fin 3 → ZMod 7, ∃ hb : ιE (Multiplicative.ofAdd t) ∈ Bs,
      ιB (Additive.ofMul (⟨ιE (Multiplicative.ofAdd t), hb⟩ : ↥Bs)) = Fin.cons 0 t)
    (hsplit : ∀ b ∈ Bs, ∃ e ∈ Bs ⊓ L, ∃ k : ℕ, b = e * x ^ k)
    (hErange : ιE.range = Bs ⊓ L) (π : Equiv.Perm (Fin 3)) {w : G} (hwJ : w ∈ J)
    (hwN : w ∈ Subgroup.normalizer (ιE.range : Set G)) (hwx : w * x = x * w)
    (hwact : ∀ t : Fin 3 → ZMod 7,
      w⁻¹ * ιE (Multiplicative.ofAdd t) * w = ιE (Multiplicative.ofAdd (t ∘ π))) :
    ∃ φ ∈ ggAutomizer J Bs, ∀ b : ↥Bs,
      ιB (Additive.ofMul (φ b)) =
        vecMul (ιB (Additive.ofMul b)) (a8PermMat (a8ja_perm4 π)) := by
  have hwNin : w⁻¹ ∈ Subgroup.normalizer (ιE.range : Set G) := Subgroup.inv_mem _ hwN
  have hxk : ∀ k : ℕ, w⁻¹ * x ^ k * w = x ^ k := by
    intro k
    have hc : Commute w x := hwx
    calc w⁻¹ * x ^ k * w = w⁻¹ * (x ^ k * w) := by group
      _ = w⁻¹ * (w * x ^ k) := by rw [← hc.pow_right k]
      _ = x ^ k := by group
  have hgN : w⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      obtain ⟨e, he, k, hbk⟩ := hsplit b hb
      have heE : e ∈ ιE.range := hErange.symm ▸ he
      have hweE : w⁻¹ * e * w ∈ ιE.range := by
        simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hwNin e).mp heE
      have hweB : w⁻¹ * e * w ∈ Bs := (hErange ▸ hweE : w⁻¹ * e * w ∈ Bs ⊓ L).1
      have hmem : w⁻¹ * (e * x ^ k) * w⁻¹⁻¹ = (w⁻¹ * e * w) * x ^ k := by
        rw [inv_inv]
        calc w⁻¹ * (e * x ^ k) * w = (w⁻¹ * e * w) * (w⁻¹ * x ^ k * w) := by group
          _ = (w⁻¹ * e * w) * x ^ k := by rw [hxk k]
      rw [hbk, hmem]
      exact Bs.mul_mem hweB (Bs.pow_mem hxB k)
    · intro hb
      have hb' : w⁻¹ * b * w ∈ Bs := by simpa only [inv_inv] using hb
      obtain ⟨e, he, k, hbk⟩ := hsplit (w⁻¹ * b * w) hb'
      have heE : e ∈ ιE.range := hErange.symm ▸ he
      have hweE : w * e * w⁻¹ ∈ ιE.range := (Subgroup.mem_normalizer_iff.mp hwN e).mp heE
      have hweB : w * e * w⁻¹ ∈ Bs := (hErange ▸ hweE : w * e * w⁻¹ ∈ Bs ⊓ L).1
      have hb_eq : b = (w * e * w⁻¹) * x ^ k := by
        calc b = w * (w⁻¹ * b * w) * w⁻¹ := by group
          _ = w * (e * x ^ k) * w⁻¹ := by rw [hbk]
          _ = (w * e * w⁻¹) * (w * x ^ k * w⁻¹) := by group
          _ = (w * e * w⁻¹) * x ^ k := by
                have : w * x ^ k * w⁻¹ = x ^ k := by
                  calc w * x ^ k * w⁻¹ = (w * x ^ k) * w⁻¹ := rfl
                    _ = (x ^ k * w) * w⁻¹ := by rw [(show Commute w x from hwx).pow_right k]
                    _ = x ^ k := by group
                rw [this]
      rw [hb_eq]
      exact Bs.mul_mem hweB (Bs.pow_mem hxB k)
  refine ⟨ggConjAut Bs hgN, ggConjAut_mem_ggAutomizer (Subgroup.inv_mem _ hwJ) hgN, ?_⟩
  intro b
  obtain ⟨e, he, k, hbk⟩ := hsplit b b.2
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hErange.symm ▸ he)
  obtain ⟨s, rfl⟩ := Multiplicative.ofAdd.surjective a
  obtain ⟨hb', hcoord_s⟩ := hcoord s
  have hbval : (b : G) = ιE (Multiplicative.ofAdd s) * x ^ k := by rw [hbk, ha]
  have hιBb : ιB (Additive.ofMul b) = Fin.cons (k : ZMod 7) s := by
    have hb_eq : b = (⟨ιE (Multiplicative.ofAdd s), hb'⟩ : ↥Bs) * (⟨x, hxB⟩ : ↥Bs) ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_pow]
      exact hbval
    calc ιB (Additive.ofMul b)
        = ιB (Additive.ofMul ((⟨ιE (Multiplicative.ofAdd s), hb'⟩ : ↥Bs) *
            (⟨x, hxB⟩ : ↥Bs) ^ k)) := by rw [hb_eq]
      _ = ιB (Additive.ofMul (⟨ιE (Multiplicative.ofAdd s), hb'⟩ : ↥Bs) +
            Additive.ofMul ((⟨x, hxB⟩ : ↥Bs) ^ k)) := by rw [ofMul_mul]
      _ = ιB (Additive.ofMul (⟨ιE (Multiplicative.ofAdd s), hb'⟩ : ↥Bs)) +
            ιB (Additive.ofMul ((⟨x, hxB⟩ : ↥Bs) ^ k)) := map_add ιB _ _
      _ = Fin.cons 0 s + k • ιB (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)) := by
            rw [hcoord_s, ofMul_pow, map_nsmul]
      _ = Fin.cons 0 s + k • (Pi.single 0 1 : Fin 4 → ZMod 7) := by rw [hιBx]
      _ = Fin.cons (k : ZMod 7) s := a8ja_cons_add_nsmul_single k s
  obtain ⟨hb2, hcoord2⟩ := hcoord (s ∘ π)
  have hgval : ((ggConjAut Bs hgN b : ↥Bs) : G) =
      ιE (Multiplicative.ofAdd (s ∘ π)) * x ^ k := by
    rw [ggConjAut_apply, hbval]
    simp only [inv_inv]
    calc w⁻¹ * (ιE (Multiplicative.ofAdd s) * x ^ k) * w
        = (w⁻¹ * ιE (Multiplicative.ofAdd s) * w) * (w⁻¹ * x ^ k * w) := by group
      _ = ιE (Multiplicative.ofAdd (s ∘ π)) * (w⁻¹ * x ^ k * w) := by rw [hwact s]
      _ = ιE (Multiplicative.ofAdd (s ∘ π)) * x ^ k := by rw [hxk k]
  have hιBb' : ιB (Additive.ofMul (ggConjAut Bs hgN b)) = Fin.cons (k : ZMod 7) (s ∘ π) := by
    have hb_eq2 : ggConjAut Bs hgN b = (⟨ιE (Multiplicative.ofAdd (s ∘ π)), hb2⟩ : ↥Bs) *
        (⟨x, hxB⟩ : ↥Bs) ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_pow]
      exact hgval
    calc ιB (Additive.ofMul (ggConjAut Bs hgN b))
        = ιB (Additive.ofMul ((⟨ιE (Multiplicative.ofAdd (s ∘ π)), hb2⟩ : ↥Bs) *
            (⟨x, hxB⟩ : ↥Bs) ^ k)) := by rw [hb_eq2]
      _ = ιB (Additive.ofMul (⟨ιE (Multiplicative.ofAdd (s ∘ π)), hb2⟩ : ↥Bs) +
            Additive.ofMul ((⟨x, hxB⟩ : ↥Bs) ^ k)) := by rw [ofMul_mul]
      _ = ιB (Additive.ofMul (⟨ιE (Multiplicative.ofAdd (s ∘ π)), hb2⟩ : ↥Bs)) +
            ιB (Additive.ofMul ((⟨x, hxB⟩ : ↥Bs) ^ k)) := map_add ιB _ _
      _ = Fin.cons 0 (s ∘ π) + k • ιB (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)) := by
            rw [hcoord2, ofMul_pow, map_nsmul]
      _ = Fin.cons 0 (s ∘ π) + k • (Pi.single 0 1 : Fin 4 → ZMod 7) := by rw [hιBx]
      _ = Fin.cons (k : ZMod 7) (s ∘ π) := a8ja_cons_add_nsmul_single k (s ∘ π)
  rw [hιBb', hιBb]
  exact (a8ja_vecMul_perm4 π s k).symm

theorem ggA8Nbr_lSideSp
    (hMp : GGInnerDiagMpInput) (hLB : GGLBalanceInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 7 B Bs x L D J)
    (hInnL : GGInnerDiagOn Bs L)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 3 2 3) {y : G} {K : Subgroup G}
    (hnb : GGNbr 7 B x D J y K)
    (hKm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1) :
    J ≤ K ∧ GGA8LSideB Bs D L J ⟨x, hcfg.tableB_facts.2.2.1⟩ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨ψ, hψinj, hψrange⟩ := ggA8Nbr_spLift hInnL hmod
  have hxB : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hx7 : orderOf x = 7 := hcfg.orderOf_x
  have hJcomp := hcfg.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hJcomp.1.trans inf_le_left
  have hJD : J ≤ Subgroup.centralizer (D : Set G) := hJcomp.1.trans inf_le_right
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hxcentL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hy_ne : y ≠ 1 := by
    intro hy1
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hnb.2.1, Subgroup.closure_le]
      rintro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hzx | hzy
      · rw [hzx]; exact Subgroup.mem_zpowers x
      · rw [hzy, hy1]; exact Subgroup.one_mem _
    have hle : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDle
    rw [hcfg.2.2.1.2.2.1, Nat.card_zpowers, hx7] at hle
    norm_num at hle
  have hyord : orderOf y = 7 := by
    have hy7 : y ^ 7 = 1 := hcfg.2.1.2.1.2 y hyBs
    exact orderOf_eq_prime hy7 hy_ne
  obtain ⟨A₀₁, ζ₁, hζ₁, -, -, hsplit, -, -⟩ :=
    ggA8Nbr_spFrame hMp hcfg hInnL ψ hψinj hψrange (e₀ := (1 : G))
      (Subgroup.mem_inf.mpr ⟨Subgroup.one_mem Bs, Subgroup.one_mem L⟩)
  obtain ⟨e₀, he₀, k, hy_eq⟩ := hsplit y hyBs
  have he₀_ne : e₀ ≠ 1 := by
    intro h1
    have hy_in : y ∈ Subgroup.zpowers x := by
      rw [hy_eq, h1, one_mul]
      exact Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), by rw [zpow_natCast]⟩
    have hyle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hy_in
    have hcard : Nat.card (Subgroup.zpowers y) = Nat.card (Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hyord, hx7]
    have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hyle hcard.symm.le
    exact a8ja_not_mem_zpowers hcfg hnb (heq ▸ Subgroup.mem_zpowers x)
  obtain ⟨A₀, ζ, hζ, hζo, hErange, hsplit', hβ, ιB, hιBx, hιBt, hιBmove⟩ :=
    ggA8Nbr_spFrame hMp hcfg hInnL ψ hψinj hψrange he₀
  obtain ⟨β, hβal, hβe⟩ := hβ
  have hb1 : CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd β) ≠ 1 := by
    rw [hβe]; exact he₀_ne
  have hcent_eq := a8ja_centralizer_inf_eq hnb.2.1 hy_eq hLx he₀.2
  have hcomp : CFSG.Assembly.IsComponentOf J
      (ψ.range ⊓ Subgroup.centralizer
        ({CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd β)} : Set G)) := by
    rw [hψrange, hβe, ← hcent_eq]
    exact hJcomp
  have hpF : 7 ∣ Nat.card (GaloisField 2 3) - 1 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hJ : CoordSp.SpCompShape ψ A₀ β J :=
    CoordSp.comp_of_aligned_shape (p := 7) (n := 3) (F := GaloisField 2 3)
      (by norm_num : (7 : ℕ) ≠ 2) hpF hψinj hζo hβal hb1 hcomp
  obtain ⟨w7, hw7J, hw7o⟩ := CoordSp.spCompShape_exists_orderOf (p := 7) (n := 3) hψinj hζo hJ
  have h7dvd : 7 ∣ Nat.card J := by
    have h := orderOf_dvd_natCard (⟨w7, hw7J⟩ : ↥J)
    rwa [Subgroup.orderOf_mk, hw7o] at h
  have hJK : J ≤ K := le_of_ggNbr hLB hcfg.1 hcfg.2.2 h7dvd hnb
  have hxcentJ : x ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact Subgroup.mem_centralizer_iff.mp hxcentL j (hJL hj)
  obtain ⟨T, hTne, hT2, hTJ, hET⟩ :=
    CoordSp.spCompShape_exists_twoSubgroup (p := 7) (n := 3) hψinj hJ
  have hBT : B ≤ Subgroup.normalizer (T : Set G) := by
    intro b hb
    obtain ⟨e, he, m, hbm⟩ := hsplit' b (hcfg.2.1.1 hb)
    have heE : e ∈ (CoordSp.frameHom ψ A₀ hζ).range := hErange.symm ▸ he
    have heN : e ∈ Subgroup.normalizer (T : Set G) := hET heE
    have hxN : x ∈ Subgroup.normalizer (T : Set G) :=
      Subgroup.centralizer_le_normalizer _ (by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        exact Subgroup.mem_centralizer_iff.mp hxcentL t (hJL (hTJ ht)))
    rw [hbm]
    exact Subgroup.mul_mem _ heN (Subgroup.pow_mem _ hxN m)
  have hCJleD : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D :=
    ggStdSubBstarCentralizer_of_twoSubgroup hcfg ⟨T, hTne, hT2, hTJ, hBT⟩
  have hZL : Subgroup.center L = ⊥ := by
    have h := center_range_statedSp_eq_bot ψ hψinj
    rw [← hψrange]
    exact h
  have hEx_disj : (CoordSp.frameHom ψ A₀ hζ).range ⊓ Subgroup.zpowers x = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hzE, hzx⟩ := Subgroup.mem_inf.mp hz
    have hzBsL : z ∈ Bs ⊓ L := hErange ▸ hzE
    obtain ⟨-, hzL⟩ := Subgroup.mem_inf.mp hzBsL
    have hzC : z ∈ Subgroup.centralizer (L : Set G) := Subgroup.zpowers_le.mpr hxcentL hzx
    have hzZ : (⟨z, hzL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hzC (l : G) l.2
    rw [hZL, Subgroup.mem_bot] at hzZ
    exact congrArg Subtype.val hzZ
  have hcent : Nat.card ((CoordSp.frameHom ψ A₀ hζ).range ⊓
      Subgroup.centralizer (J : Set G) : Subgroup G) ≤ 7 := by
    set K' : Subgroup G := (CoordSp.frameHom ψ A₀ hζ).range ⊓
        Subgroup.centralizer (J : Set G) with hK'
    have hK'leD : K' ≤ D := by
      intro z hz
      rw [hK'] at hz
      obtain ⟨hzE, hzCJ⟩ := Subgroup.mem_inf.mp hz
      obtain ⟨hzBs, -⟩ := Subgroup.mem_inf.mp (hErange ▸ hzE)
      exact hCJleD (Subgroup.mem_inf.mpr ⟨hzBs, hzCJ⟩)
    have hdisj : Subgroup.zpowers x ⊓ K' = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      obtain ⟨hzx, hzK'⟩ := Subgroup.mem_inf.mp hz
      rw [hK'] at hzK'
      have hzE : z ∈ (CoordSp.frameHom ψ A₀ hζ).range := (Subgroup.mem_inf.mp hzK').1
      have hmem : z ∈ (CoordSp.frameHom ψ A₀ hζ).range ⊓ Subgroup.zpowers x :=
        Subgroup.mem_inf.mpr ⟨hzE, hzx⟩
      rw [hEx_disj, Subgroup.mem_bot] at hmem
      exact hmem
    let f : ↥K' × ↥(Subgroup.zpowers x) → ↥D := fun q =>
      ⟨(q.1 : G) * (q.2 : G),
        D.mul_mem (hK'leD q.1.2) (Subgroup.zpowers_le.mpr hxD q.2.2)⟩
    have hf_inj : Function.Injective f := by
      rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
      have h' : (a1 : G) * (b1 : G) = (a2 : G) * (b2 : G) := congrArg Subtype.val h
      have h1 : (a2 : G)⁻¹ * (a1 : G) = (b2 : G) * (b1 : G)⁻¹ := by
        have := congrArg (fun z => (a2 : G)⁻¹ * z * (b1 : G)⁻¹) h'
        simpa [mul_assoc] using this
      have h1K : (a2 : G)⁻¹ * (a1 : G) ∈ K' := K'.mul_mem (K'.inv_mem a2.2) a1.2
      have h1x : (b2 : G) * (b1 : G)⁻¹ ∈ Subgroup.zpowers x :=
        (Subgroup.zpowers x).mul_mem b2.2 ((Subgroup.zpowers x).inv_mem b1.2)
      have h1bot : (a2 : G)⁻¹ * (a1 : G) ∈ (⊥ : Subgroup G) := by
        rw [← hdisj]
        exact Subgroup.mem_inf.mpr ⟨h1.symm ▸ h1x, h1K⟩
      have ha : (a2 : G)⁻¹ * (a1 : G) = 1 := Subgroup.mem_bot.mp h1bot
      have haeq : a1 = a2 := by
        apply Subtype.ext
        have := congrArg (fun z => (a2 : G) * z) ha
        simpa [mul_assoc] using this
      have hbeq : b1 = b2 := by
        apply Subtype.ext
        have h'' := h'
        rw [haeq] at h''
        exact mul_left_cancel h''
      rw [haeq, hbeq]
    have hcard_le : Nat.card (↥K' × ↥(Subgroup.zpowers x)) ≤ Nat.card ↥D :=
      Nat.card_le_card_of_injective f hf_inj
    rw [Nat.card_prod, Nat.card_zpowers, hx7, hcfg.2.2.1.2.2.1, pow_two] at hcard_le
    exact Nat.le_of_mul_le_mul_right hcard_le (by norm_num)
  have hβ0 : β ≠ 0 := by
    intro h0
    exact hb1 (by rw [h0]; exact map_one _)
  rcases CoordSp.spCompShape_refine (p := 7) (n := 3) hψinj hζo hβ0 hJ hcent with
    hzero | ⟨c, hc, hJeq, hall⟩
  · exfalso
    obtain ⟨hJeq, hZcard⟩ := hzero
    have hZ2 : (CoordSp.spClass β 0).card = 2 := by omega
    have hle : ((CoordSp.blockSp (F := GaloisField 2 3) (CoordSp.spClass β 0)).range).map
        (CoordSp.frameConj ψ A₀) ≤ K := hJeq ▸ hJK
    exact ggA8Nbr_spZblock_not_le_K hψinj A₀ hZ2 hKm hle
  · obtain ⟨h733, hperm⟩ := ggA8Nbr_spSiegel hψinj hall hJeq
    refine ⟨hJK, hCJleD, h733, ιB, hιBx, ?_, ?_⟩
    · intro σ hσ
      obtain ⟨w, hw, hwact⟩ := hperm (a8ja_permSucc σ hσ)
      have hwJ : w ∈ J := hw.1
      have hwN : w ∈ Subgroup.normalizer ((CoordSp.frameHom ψ A₀ hζ).range : Set G) := hw.2
      have hwx : w * x = x * w :=
        (Subgroup.mem_centralizer_iff.mp (hJD hwJ) x hxD).symm
      have hwact' : ∀ t : Fin 3 → ZMod 7,
          w⁻¹ * CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd t) * w =
            CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd (t ∘ a8ja_permSucc σ hσ)) := by
        intro t
        have h := hwact t
        rwa [show (fun i => t ((a8ja_permSucc σ hσ) i)) = (t ∘ a8ja_permSucc σ hσ)
          from rfl] at h
      obtain ⟨φ, hφ, hφact⟩ :=
        a8ja_conjAut_perm hxB ιB hιBx hιBt hsplit' hErange (a8ja_permSucc σ hσ)
          hwJ hwN hwx hwact'
      refine ⟨φ, hφ, fun b => ?_⟩
      rw [hφact b, a8ja_perm4_permSucc σ hσ]
    · obtain ⟨φ, hφ, hφact⟩ := hιBmove (1 : Equiv.Perm (Fin 3)) a8ja_etaSign a8ja_etaSign_mem
      refine ⟨φ, hφ, fun b => ?_⟩
      rw [hφact b, a8ja_vecMul_signThree]
      simp

end CFSG.StandardType.A8Coord

end
