module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordSplit
public import CFSG.LocalAnalysis.StandardType.GGA8NbrGlueB
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmDefs
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmLift
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmFrame
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmCompShape
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmTwoSub
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmSiegel
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmZblock
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType.A8Coord

open Certificates.A8Nbr476 CFSG.Assembly CFSG.Open CFSG.StandardType Matrix Multiplicative
open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def om8_etaSign : Fin 3 → (ZMod 7)ˣ := ![1, 1, -1]

private theorem om8_etaSign_mem (i : Fin 3) : om8_etaSign i ∈ CoordSp.signs 7 := by
  fin_cases i <;> simp [om8_etaSign, CoordSp.mem_signs]

private theorem om8_symm_zero (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) : σ.symm 0 = 0 := by
  have h := congrArg σ.symm hσ
  simpa using h.symm

private def om8_perm4Fun (π : Equiv.Perm (Fin 3)) : Fin 4 → Fin 4 :=
  Fin.cases 0 (fun i => (π.symm i).succ)

private theorem om8_perm4Fun_zero (π : Equiv.Perm (Fin 3)) : om8_perm4Fun π 0 = 0 := rfl

private theorem om8_perm4Fun_succ (π : Equiv.Perm (Fin 3)) (i : Fin 3) :
    om8_perm4Fun π i.succ = (π.symm i).succ := rfl

private theorem om8_perm4Fun_injective (π : Equiv.Perm (Fin 3)) :
    Function.Injective (om8_perm4Fun π) := by
  intro a b hab
  revert b
  refine Fin.cases ?_ ?_ a
  · intro b
    refine Fin.cases ?_ ?_ b
    · intro _
      rfl
    · intro j h
      rw [om8_perm4Fun_zero, om8_perm4Fun_succ] at h
      exact absurd h.symm (Fin.succ_ne_zero (π.symm j))
  · intro i b
    refine Fin.cases ?_ ?_ b
    · intro h
      rw [om8_perm4Fun_zero, om8_perm4Fun_succ] at h
      exact absurd h (Fin.succ_ne_zero (π.symm i))
    · intro j h
      rw [om8_perm4Fun_succ, om8_perm4Fun_succ] at h
      congr 1
      exact π.symm.injective (Fin.succ_inj.mp h)

private theorem om8_perm4Fun_surjective (π : Equiv.Perm (Fin 3)) :
    Function.Surjective (om8_perm4Fun π) := by
  intro b
  refine Fin.cases ?_ ?_ b
  · exact ⟨0, om8_perm4Fun_zero π⟩
  · intro j
    refine ⟨(π j).succ, ?_⟩
    rw [om8_perm4Fun_succ, Equiv.symm_apply_apply]

private noncomputable def om8_perm4 (π : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (om8_perm4Fun π) ⟨om8_perm4Fun_injective π, om8_perm4Fun_surjective π⟩

private theorem om8_perm4_zero (π : Equiv.Perm (Fin 3)) : om8_perm4 π 0 = 0 :=
  om8_perm4Fun_zero π

private theorem om8_perm4_succ (π : Equiv.Perm (Fin 3)) (i : Fin 3) :
    om8_perm4 π i.succ = (π.symm i).succ :=
  om8_perm4Fun_succ π i

private theorem om8_perm4_symm_zero (π : Equiv.Perm (Fin 3)) : (om8_perm4 π).symm 0 = 0 := by
  rw [Equiv.symm_apply_eq, om8_perm4_zero]

private theorem om8_perm4_symm_succ (π : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (om8_perm4 π).symm i.succ = (π i).succ := by
  exact (Equiv.symm_apply_eq (om8_perm4 π)).mpr (by
    rw [om8_perm4_succ, Equiv.symm_apply_apply])

private theorem om8_vecMul_a8PermMat (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ZMod 7) (j : Fin 4) :
    vecMul v (a8PermMat σ) j = v (σ.symm j) := by
  have h : a8PermMat σ = σ.permMatrix (ZMod 7) := by
    ext i j
    simp [a8PermMat, Equiv.Perm.permMatrix, eq_comm]
  rw [h, Matrix.vecMul_permMatrix]
  rfl

private theorem om8_vecMul_perm4 (π : Equiv.Perm (Fin 3)) (s : Fin 3 → ZMod 7) (k : ℕ) :
    vecMul (Fin.cons (k : ZMod 7) s : Fin 4 → ZMod 7) (a8PermMat (om8_perm4 π)) =
      Fin.cons (k : ZMod 7) (s ∘ π) := by
  funext j
  rw [om8_vecMul_a8PermMat]
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [om8_perm4_symm_zero, Fin.cons_zero, Fin.cons_zero]
  · rw [om8_perm4_symm_succ, Fin.cons_succ, Fin.cons_succ]
    rfl

private noncomputable def om8_permSuccFun (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) :
    Fin 3 → Fin 3 :=
  fun i => Fin.pred (σ.symm i.succ) (by
    intro h
    have h1 : σ.symm i.succ = σ.symm 0 := by rw [h, om8_symm_zero σ hσ]
    exact Fin.succ_ne_zero i (σ.symm.injective h1))

private theorem om8_permSuccFun_injective (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) :
    Function.Injective (om8_permSuccFun σ hσ) := by
  intro i j hij
  have h2 : σ.symm i.succ = σ.symm j.succ := by
    have := congrArg Fin.succ hij
    simpa only [om8_permSuccFun, Fin.succ_pred] using this
  exact Fin.succ_inj.mp (σ.symm.injective h2)

private theorem om8_permSuccFun_surjective (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) :
    Function.Surjective (om8_permSuccFun σ hσ) := by
  intro j
  refine ⟨Fin.pred (σ j.succ) (by
      intro h
      have h1 : σ j.succ = σ 0 := by rw [h, hσ]
      exact Fin.succ_ne_zero j (σ.injective h1)), ?_⟩
  simp only [om8_permSuccFun, Fin.succ_pred, Equiv.symm_apply_apply, Fin.pred_succ]

private noncomputable def om8_permSucc (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) :
    Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (om8_permSuccFun σ hσ)
    ⟨om8_permSuccFun_injective σ hσ, om8_permSuccFun_surjective σ hσ⟩

private theorem om8_permSucc_apply (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) (i : Fin 3) :
    om8_permSucc σ hσ i = om8_permSuccFun σ hσ i := rfl

private theorem om8_permSucc_succ (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) (i : Fin 3) :
    (om8_permSucc σ hσ i).succ = σ.symm i.succ := by
  rw [om8_permSucc_apply]
  show Fin.succ (Fin.pred (σ.symm i.succ) _) = σ.symm i.succ
  rw [Fin.succ_pred]

private theorem om8_permSucc_symm (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) (i : Fin 3) :
    ((om8_permSucc σ hσ).symm i).succ = σ i.succ := by
  have h := om8_permSucc_succ σ hσ ((om8_permSucc σ hσ).symm i)
  rw [Equiv.apply_symm_apply] at h
  have h2 := congrArg σ h
  rw [Equiv.apply_symm_apply] at h2
  exact h2.symm

private theorem om8_perm4_permSucc (σ : Equiv.Perm (Fin 4)) (hσ : σ 0 = 0) :
    om8_perm4 (om8_permSucc σ hσ) = σ := by
  apply Equiv.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [om8_perm4_zero, hσ]
  · rw [om8_perm4_succ, om8_permSucc_symm]

private theorem om8_cons_add_nsmul_single (k : ℕ) (s : Fin 3 → ZMod 7) :
    (Fin.cons 0 s : Fin 4 → ZMod 7) + k • (Pi.single 0 1 : Fin 4 → ZMod 7) =
      Fin.cons (k : ZMod 7) s := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [Pi.add_apply, Fin.cons_zero, Pi.smul_apply, Pi.single_eq_same, Fin.cons_zero]
    simp [nsmul_eq_mul]
  · rw [Pi.add_apply, Fin.cons_succ, Pi.smul_apply,
      Pi.single_eq_of_ne (Fin.succ_ne_zero i), Fin.cons_succ]
    simp

private theorem om8_vecMul_signThree (v : Fin 4 → ZMod 7) :
    vecMul v a8SignThree =
      Fin.cons (v 0) (fun i : Fin 3 => (om8_etaSign i : ZMod 7) * v i.succ) := by
  funext j
  fin_cases j
  · change (v ᵥ* a8SignThree) 0 =
        ((Fin.cons (v 0) (fun i : Fin 3 => (om8_etaSign i : ZMod 7) * v i.succ) :
          Fin 4 → ZMod 7) 0)
    simp [a8SignThree, om8_etaSign, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
      Matrix.diagonal, Fin.cons_zero]
  · change (v ᵥ* a8SignThree) 1 =
        ((Fin.cons (v 0) (fun i : Fin 3 => (om8_etaSign i : ZMod 7) * v i.succ) :
          Fin 4 → ZMod 7) 1)
    rw [show (1 : Fin 4) = (0 : Fin 3).succ from rfl, Fin.cons_succ]
    simp [a8SignThree, om8_etaSign, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.diagonal]
  · change (v ᵥ* a8SignThree) 2 =
        ((Fin.cons (v 0) (fun i : Fin 3 => (om8_etaSign i : ZMod 7) * v i.succ) :
          Fin 4 → ZMod 7) 2)
    rw [show (2 : Fin 4) = (1 : Fin 3).succ from rfl, Fin.cons_succ]
    simp [a8SignThree, om8_etaSign, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.diagonal]
  · change (v ᵥ* a8SignThree) 3 =
        ((Fin.cons (v 0) (fun i : Fin 3 => (om8_etaSign i : ZMod 7) * v i.succ) :
          Fin 4 → ZMod 7) 3)
    rw [show (3 : Fin 4) = (2 : Fin 3).succ from rfl, Fin.cons_succ]
    simp [a8SignThree, om8_etaSign, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.diagonal]

private theorem om8_centralizer_inf_eq {G : Type} [Group G] {L D : Subgroup G} {x y e : G}
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

private theorem om8_not_mem_zpowers {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
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

private theorem om8_conjAut_perm {G : Type} [Group G] {Bs L J : Subgroup G} {x : G}
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
        vecMul (ιB (Additive.ofMul b)) (a8PermMat (om8_perm4 π)) := by
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
      _ = Fin.cons (k : ZMod 7) s := om8_cons_add_nsmul_single k s
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
      _ = Fin.cons (k : ZMod 7) (s ∘ π) := om8_cons_add_nsmul_single k (s ∘ π)
  rw [hιBb', hιBb]
  exact (om8_vecMul_perm4 π s k).symm

private theorem om8_orderOf_frame_single {A : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)}
    (F : SevOm.Frame omQ 7 A 3) {u : Fin 3 → ZMod 7} (hu : u ≠ 0) :
    orderOf (F.ι (ofAdd u)) = 7 := by
  refine orderOf_eq_prime (F.pow_p (ofAdd u)) ?_
  intro h1
  apply hu
  have h2 : (ofAdd u : Multiplicative (Fin 3 → ZMod 7)) = 1 :=
    F.inj (h1.trans (map_one F.ι).symm)
  simpa using congrArg toAdd h2

private theorem om8_map_normalizer_le {M N : Type*} [Group M] [Group N] (f : M →* N)
    (K : Subgroup M) :
    (Subgroup.normalizer K).map f ≤ Subgroup.normalizer (K.map f) := by
  rintro _ ⟨g, hg, rfl⟩
  have hg' : ∀ x, x ∈ K ↔ g * x * g⁻¹ ∈ K := Subgroup.mem_normalizer_iff.mp hg
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨?_, ?_⟩
  · intro hy
    obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp hy
    exact ⟨g * x * g⁻¹, (hg' x).mp hx, by rw [map_mul, map_mul, map_inv, hxval]⟩
  · intro hy
    obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp hy
    refine ⟨g⁻¹ * x * g, (hg' (g⁻¹ * x * g)).mpr ?_, ?_⟩
    · rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact hx
    · rw [map_mul, map_mul, map_inv, hxval]; group

private theorem om8_class_seven_dvd {A : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)}
    (hAΩ : A ≤ omΩ) (F : SevOm.Frame omQ 7 A 3) (ζ : (GaloisField 2 3)ˣ)
    (hζ : orderOf ζ = 7) (hdim : ∀ i, finrank (GaloisField 2 3) (F.U i) = 2)
    (hal : CoordOm.FrameAligned F ζ) (hmoves : CoordOm.FrameMovesAll F (CoordSp.signs 7))
    {c : ZMod 7} (hc : c ≠ 0)
    {h : (GaloisField 2 3)[X]}
    (hh : h ∈ primaryFactors (F.ι (ofAdd fun _ : Fin 3 => c)).toLinearMap) (hX : h ≠ X - 1)
    (hm : primaryMultiplicity (F.ι (ofAdd fun _ : Fin 3 => c)).toLinearMap h = 3)
    {J : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)}
    (hJeq : J = specialBlock omQ (F.ι (ofAdd fun _ : Fin 3 => c)) h)
    (hJ : CFSG.Assembly.IsComponentOf J
      (omΩ ⊓ Subgroup.centralizer {F.ι (ofAdd fun _ : Fin 3 => c)})) :
    7 ∣ Nat.card J := by
  classical
  have hQ : (QuadraticMap.polarBilin omQ).Nondegenerate :=
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadMinus
      4 (GaloisField 2 3) (CFSG.LieType.Universal.minusCoeffs 2 3).1
      (CFSG.LieType.Universal.minusCoeffs 2 3).2 (by norm_num)
      (CFSG.LieType.Universal.minusCoeffs_irr 2 3)).1
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨-, hperm⟩ := omSiegel hAΩ F ζ hζ hdim hal hmoves hc hh hX hJeq hm
  have hxodd := F.oddOrderIsometry hQ (by norm_num) (by norm_num) hAΩ (ofAdd (fun _ : Fin 3 => c))
  obtain ⟨-, -, hnorm, -⟩ :=
    SevOm.exists_block_of_isComponentOf hxodd (by norm_num) (by norm_num) hJ
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  obtain ⟨w, hw, hwact⟩ := hperm σ
  let t : Fin 3 → ZMod 7 := Pi.single 0 1
  let x : OmV ≃ₗ[GaloisField 2 3] OmV := F.ι (ofAdd t)
  have hcomm : ∀ s t : Multiplicative (Fin 3 → ZMod 7),
      F.ι s * F.ι t = F.ι t * F.ι s := by
    intro s t
    calc F.ι s * F.ι t = F.ι (s * t) := (map_mul F.ι s t).symm
      _ = F.ι (t * s) := congrArg F.ι (mul_comm s t)
      _ = F.ι t * F.ι s := map_mul F.ι t s
  have hxmem : x ∈ isometryCentralizer omQ (F.ι (ofAdd fun _ : Fin 3 => c)) := by
    refine Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup (hAΩ (F.mem _)), ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hcomm (ofAdd t) (ofAdd (fun _ : Fin 3 => c)))
  have hx7 : x ^ 7 = 1 := F.pow_p (ofAdd t)
  have hxN : x ∈ Subgroup.normalizer (J : Set (OmV ≃ₗ[GaloisField 2 3] OmV)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg; exact hnorm x hxmem hx7 g hg
    · intro hg
      have hxinv : x⁻¹ ∈ isometryCentralizer omQ (F.ι (ofAdd fun _ : Fin 3 => c)) :=
        (isometryCentralizer omQ _).inv_mem hxmem
      have hxinvp : (x⁻¹) ^ 7 = 1 := by rw [inv_pow, hx7, inv_one]
      have h2 := hnorm x⁻¹ hxinv hxinvp (x * g * x⁻¹) hg
      rwa [show x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g by group] at h2
  have hxNinv : x⁻¹ ∈ Subgroup.normalizer (J : Set (OmV ≃ₗ[GaloisField 2 3] OmV)) :=
    Subgroup.inv_mem _ hxN
  have hxw : x⁻¹ * w * x ∈ J := (Subgroup.mem_normalizer_iff.mp hxNinv w).mp hw.1
  have hmem : w⁻¹ * x⁻¹ * w * x ∈ J := by
    have hh := J.mul_mem (J.inv_mem hw.1) hxw
    simpa only [mul_assoc] using hh
  have hcomm_eq : w⁻¹ * x⁻¹ * w * x = F.ι (ofAdd (t - t ∘ σ)) := by
    have hwx : w⁻¹ * x * w = F.ι (ofAdd (t ∘ σ)) := hwact t
    calc w⁻¹ * x⁻¹ * w * x
        = (w⁻¹ * x * w)⁻¹ * x := by group
      _ = (F.ι (ofAdd (t ∘ σ)))⁻¹ * F.ι (ofAdd t) := by rw [hwx]
      _ = F.ι (ofAdd (t - t ∘ σ)) := by
            rw [← map_inv, ← map_mul]
            congr 1
            apply toAdd.injective
            rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd]
            abel
  have hne : t - t ∘ σ ≠ 0 := by
    intro h0
    have h1 := congrFun h0 0
    have h2 : (t - t ∘ σ) 0 = 1 := by
      have hσ : σ 0 = 1 := Equiv.swap_apply_left 0 1
      simp only [Pi.sub_apply, Function.comp_apply, hσ, t, Pi.single_eq_same,
        Pi.single_eq_of_ne (show (0 : Fin 3) ≠ 1 by decide)]
      norm_num
    rw [h2] at h1
    exact one_ne_zero h1
  have hord : orderOf (w⁻¹ * x⁻¹ * w * x) = 7 := by
    rw [hcomm_eq]
    exact om8_orderOf_frame_single F hne
  have h := orderOf_dvd_natCard (⟨_, hmem⟩ : ↥J)
  rwa [Subgroup.orderOf_mk, hord] at h

theorem ggA8Nbr_lSideOm
    (hMp : GGInnerDiagMpInput) (hLB : GGLBalanceInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 7 B Bs x L D J)
    (hInnL : GGInnerDiagOn Bs L)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaMinus 4 2 3) {y : G}
    {K : Subgroup G} (hnb : GGNbr 7 B x D J y K)
    (hKm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1) :
    J ≤ K ∧ GGA8LSideB Bs D L J ⟨x, hcfg.tableB_facts.2.2.1⟩ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨φ, hinj, hrange⟩ := ggA8Nbr_omLift hInnL hmod
  have hin := ggA8Nbr_omInner hMp hInnL hmod
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
  obtain ⟨hsplit, hframe⟩ := ggA8Nbr_omFrame hcfg hin φ hinj hrange
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
    exact om8_not_mem_zpowers hcfg hnb (heq ▸ Subgroup.mem_zpowers x)
  obtain ⟨F, ζ, β, hmaxA, hζo, hdim, hal, hmoves, hβal, hφβ, ιB, hιBx, hιBt, hιBmove⟩ :=
    hframe e₀ he₀
  have hQ : (QuadraticMap.polarBilin omQ).Nondegenerate :=
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadMinus
      4 (GaloisField 2 3) (CFSG.LieType.Universal.minusCoeffs 2 3).1
      (CFSG.LieType.Universal.minusCoeffs 2 3).2 (by norm_num)
      (CFSG.LieType.Universal.minusCoeffs_irr 2 3)).1
  have hxodd : OddOrderIsometry omQ 7 (F.ι (ofAdd β)) :=
    F.oddOrderIsometry hQ (by norm_num) (by norm_num) (omA_le φ Bs) (ofAdd β)
  have hcommF : ∀ s t : Multiplicative (Fin 3 → ZMod 7), F.ι s * F.ι t = F.ι t * F.ι s := by
    intro s t
    calc F.ι s * F.ι t = F.ι (s * t) := (map_mul F.ι s t).symm
      _ = F.ι (t * s) := congrArg F.ι (mul_comm s t)
      _ = F.ι t * F.ι s := map_mul F.ι t s
  have hβ0 : β ≠ 0 := by
    intro h0
    have h1 : (⟨F.ι (ofAdd β), omA_le φ Bs (F.mem _)⟩ : ↥omΩ) = 1 := by
      apply Subtype.ext
      rw [h0]
      simpa using map_one F.ι
    have h2 : e₀ = 1 := by rw [← hφβ, h1, map_one]
    exact he₀_ne h2
  have hcent_eq := om8_centralizer_inf_eq hnb.2.1 hy_eq hLx he₀.2
  let ιβ : ↥omΩ := ⟨F.ι (ofAdd β), omA_le φ Bs (F.mem _)⟩
  have hcomp : CFSG.Assembly.IsComponentOf J
      (φ.range ⊓ Subgroup.centralizer ({φ ιβ} : Set G)) := by
    rw [hrange, hφβ, ← hcent_eq]
    exact hJcomp
  let JΩ : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV) := (J.comap φ).map omΩ.subtype
  have hcomp' : CFSG.Assembly.IsComponentOf J
      (φ.range ⊓ Subgroup.centralizer (φ '' ({ιβ} : Set ↥omΩ))) := by
    rw [Set.image_singleton]
    exact hcomp
  have htrans := CoordOm.isComponentOf_transport_set hinj ({ιβ} : Set ↥omΩ) hcomp'
  have hJΩ : CFSG.Assembly.IsComponentOf JΩ
      (omΩ ⊓ Subgroup.centralizer ({F.ι (ofAdd β)} : Set (OmV ≃ₗ[GaloisField 2 3] OmV))) := by
    have h := htrans.1
    rw [Set.image_singleton] at h
    exact h
  have hJΩmap : (J.comap φ).map φ = J := htrans.2
  have hcardJΩ : Nat.card JΩ = Nat.card J := by
    have h1 : Nat.card JΩ = Nat.card (J.comap φ) := by
      show Nat.card ((J.comap φ).map omΩ.subtype) = Nat.card (J.comap φ)
      rw [Subgroup.card_map_of_injective omΩ.subtype_injective]
    have h2 : Nat.card J = Nat.card (J.comap φ) := by
      have h3 : Nat.card ((J.comap φ).map φ) = Nat.card (J.comap φ) :=
        Subgroup.card_map_of_injective hinj
      rw [hJΩmap] at h3
      exact h3
    omega
  obtain ⟨TΩ, hTΩne, hTΩ2, hTΩJ, hATΩ⟩ := omComp_twoSubgroup (omA_le φ Bs) F hβ0 hJΩ
  have hTΩΩ : TΩ ≤ omΩ := hTΩJ.trans (hJΩ.1.trans inf_le_left)
  let T : Subgroup G := (TΩ.comap omΩ.subtype).map φ
  have hTne : T ≠ ⊥ := by
    intro hbot
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hTΩne
    have htΩ : t ∈ omΩ := hTΩΩ ht
    have hmem : φ ⟨t, htΩ⟩ ∈ T := ⟨⟨t, htΩ⟩, ht, rfl⟩
    have hmem' : φ ⟨t, htΩ⟩ ∈ (⊥ : Subgroup G) := hbot ▸ hmem
    rw [Subgroup.mem_bot] at hmem'
    apply ht1
    apply Subtype.ext
    have h2 := congrArg (fun z : ↥omΩ => (z : OmV ≃ₗ[GaloisField 2 3] OmV))
      (hinj (hmem'.trans (map_one φ).symm))
    simpa using h2
  have hT2 : IsPGroup 2 T :=
    (hTΩ2.comap_of_injective omΩ.subtype omΩ.subtype_injective).map φ
  have hTJ : T ≤ J := by
    rintro g ⟨g', hg', rfl⟩
    have hg'' : (g' : OmV ≃ₗ[GaloisField 2 3] OmV) ∈ JΩ := hTΩJ hg'
    obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp hg''
    have hgy : g' = y := Subtype.ext hyval.symm
    rw [hgy]
    exact hy
  have hAB : ∀ g : ↥omΩ, (g : OmV ≃ₗ[GaloisField 2 3] OmV) ∈ omA φ Bs ↔ φ g ∈ Bs := by
    intro g
    constructor
    · rintro ⟨y, hy, hyeq⟩
      have : y = g := Subtype.ext hyeq
      rw [← this]; exact hy
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hφA_mem : ∀ (a : OmV ≃ₗ[GaloisField 2 3] OmV) (ha : a ∈ omA φ Bs),
      φ ⟨a, omA_le φ Bs ha⟩ ∈ Bs := by
    intro a ha
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp ha
    have hyB : φ y ∈ Bs := Subgroup.mem_comap.mp hy
    have h1 : (⟨a, omA_le φ Bs ha⟩ : ↥omΩ) = y := Subtype.ext hyeq.symm
    rw [h1]; exact hyB
  have hEN : Bs ⊓ L ≤ Subgroup.normalizer (T : Set G) := by
    intro e he
    obtain ⟨heBs, heL⟩ := Subgroup.mem_inf.mp he
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hrange.symm ▸ heL)
    have haA : (a : OmV ≃ₗ[GaloisField 2 3] OmV) ∈ omA φ Bs :=
      (hAB a).mpr (by rw [ha]; exact heBs)
    have haN : (a : OmV ≃ₗ[GaloisField 2 3] OmV) ∈
        Subgroup.normalizer (TΩ : Set (OmV ≃ₗ[GaloisField 2 3] OmV)) := hATΩ haA
    have haNinv : (a : OmV ≃ₗ[GaloisField 2 3] OmV)⁻¹ ∈
        Subgroup.normalizer (TΩ : Set (OmV ≃ₗ[GaloisField 2 3] OmV)) := Subgroup.inv_mem _ haN
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
      have hconj : (a : OmV ≃ₗ[GaloisField 2 3] OmV) * (z' : OmV ≃ₗ[GaloisField 2 3] OmV) *
          (a : OmV ≃ₗ[GaloisField 2 3] OmV)⁻¹ ∈ TΩ :=
        (Subgroup.mem_normalizer_iff.mp haN _).mp hz'
      have hval : e * φ z' * e⁻¹ = φ (a * z' * a⁻¹) := by
        rw [map_mul, map_mul, map_inv, ha]
      rw [hval]
      exact ⟨a * z' * a⁻¹, hconj, rfl⟩
    · intro hz
      obtain ⟨z', hz', hzval⟩ := Subgroup.mem_map.mp hz
      have hconj : (a : OmV ≃ₗ[GaloisField 2 3] OmV)⁻¹ * (z' : OmV ≃ₗ[GaloisField 2 3] OmV) *
          (a : OmV ≃ₗ[GaloisField 2 3] OmV) ∈ TΩ :=
        (Subgroup.mem_normalizer_iff.mp haNinv _).mp hz'
      have hz_eq : z = φ (a⁻¹ * z' * a) := by
        rw [map_mul, map_mul, map_inv, ha, hzval]
        group
      rw [hz_eq]
      exact ⟨a⁻¹ * z' * a, hconj, rfl⟩
  have hTL : T ≤ L := hTJ.trans hJL
  have hxN : x ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact Subgroup.mem_centralizer_iff.mp hxcentL t (hTL ht))
  have hBT : B ≤ Subgroup.normalizer (T : Set G) := by
    intro b hb
    obtain ⟨e, he, m, hbm⟩ := hsplit b (hcfg.2.1.1 hb)
    have heN : e ∈ Subgroup.normalizer (T : Set G) := hEN he
    rw [hbm]
    exact Subgroup.mul_mem _ heN (Subgroup.pow_mem _ hxN m)
  have hCJleD : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D :=
    ggStdSubBstarCentralizer_of_twoSubgroup hcfg ⟨T, hTne, hT2, hTJ, hBT⟩
  have hqs : CFSG.Assembly.IsQuasisimple L := isQuasisimple_of_largeEvenMarking hInnL
  have hY : CFSG.IsQuasisimple ↥L := (TableBSymp.isQuasisimple_iff ↥L).mp hqs
  haveI : Group.IsPerfect ↥L := hY.1
  have hZL : Subgroup.center L = ⊥ := HalfRowData.center_eq_bot_of_pomegaMinus_two hmod
  have hEx_disj : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hzE, hzx⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨-, hzL⟩ := Subgroup.mem_inf.mp hzE
    have hzC : z ∈ Subgroup.centralizer (L : Set G) := Subgroup.zpowers_le.mpr hxcentL hzx
    have hzZ : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hzC (l : G) l.2
    rw [hZL, Subgroup.mem_bot] at hzZ
    exact congrArg Subtype.val hzZ
  have hcentE : Nat.card ((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) ≤ 7 := by
    set K' : Subgroup G := (Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G) with hK'
    have hK'leD : K' ≤ D := by
      intro z hz
      rw [hK'] at hz
      obtain ⟨hzE, hzCJ⟩ := Subgroup.mem_inf.mp hz
      obtain ⟨hzBs, -⟩ := Subgroup.mem_inf.mp hzE
      exact hCJleD (Subgroup.mem_inf.mpr ⟨hzBs, hzCJ⟩)
    have hdisj : Subgroup.zpowers x ⊓ K' = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      obtain ⟨hzx, hzK'⟩ := Subgroup.mem_inf.mp hz
      rw [hK'] at hzK'
      have hzE : z ∈ Bs ⊓ L := (Subgroup.mem_inf.mp hzK').1
      have hmem : z ∈ (Bs ⊓ L) ⊓ Subgroup.zpowers x := Subgroup.mem_inf.mpr ⟨hzE, hzx⟩
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
  have hABE : ∀ g : ↥omΩ,
      (g : OmV ≃ₗ[GaloisField 2 3] OmV) ∈ omA φ Bs ↔ φ g ∈ Bs ⊓ L := by
    intro g
    rw [hAB g]
    constructor
    · intro h; exact ⟨h, by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
    · intro h; exact h.1
  have hJLrange : J ≤ φ.range := by rw [hrange]; exact hJL
  have hcentA : Nat.card (omA φ Bs ⊓
      Subgroup.centralizer (JΩ : Set (OmV ≃ₗ[GaloisField 2 3] OmV)) :
      Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)) ≤ 7 :=
    (CoordOm.card_inf_centralizer_le_of_transport (Ω := omΩ) hinj (omA_le φ Bs) hABE
      hJLrange).trans hcentE
  have hshape := omCompShape (omA_le φ Bs) F ζ hζo hdim hal hmoves hβ0 hβal hJΩ hcentA
  rcases hshape with hzero | hclass
  ·
    obtain ⟨j, hβj, hβz, hfix, hJB, hall⟩ := hzero
    obtain ⟨i, hij⟩ : ∃ i : Fin 3, i ≠ j := by
      fin_cases j
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    let t : Fin 3 → ZMod 7 := Pi.single i 1
    have ht_ne : t ≠ 0 := by
      intro h0
      have h1 := congrFun h0 i
      simp [t] at h1
    have htmem : F.ι (ofAdd t) ∈ supportedBlock omQ (F.ι (ofAdd β)) (X - 1) := by
      refine mem_supportedBlock.mpr ⟨?_, ?_⟩
      · refine Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup (omA_le φ Bs (F.mem _)), ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommF (ofAdd t) (ofAdd β))
      · intro v hv
        rw [F.fix]
        intro i' hi' u hu
        have hi'i : i' = i := by
          by_contra hne
          exact hi' (by
            rw [toAdd_ofAdd]
            simp only [t, Pi.single_eq_of_ne hne])
        have hfixi : F.U i' ≤ fixedSpace (F.ι (ofAdd β)) := by
          rw [hi'i]
          exact F.le_fixedSpace (by rw [toAdd_ofAdd, hβz i hij])
        exact (hxodd.fixed_others).2 u (hfixi hu) v hv
    have hJt : F.ι (ofAdd t) ∈ JΩ := hall _ htmem (F.pow_p _)
    have h7Ω : 7 ∣ Nat.card JΩ := by
      have h := orderOf_dvd_natCard (⟨F.ι (ofAdd t), hJt⟩ : ↥JΩ)
      rwa [Subgroup.orderOf_mk, om8_orderOf_frame_single F ht_ne] at h
    have h7dvd : 7 ∣ Nat.card J := hcardJΩ ▸ h7Ω
    have hJK : J ≤ K := le_of_ggNbr hLB hcfg.1 hcfg.2.2 h7dvd hnb
    exfalso
    obtain ⟨h13, hZc⟩ := omZblock_thirteen_dvd (omA_le φ Bs) F hdim hβj hβz hJΩ hfix hJB hall
    have hle : (JΩ.comap omΩ.subtype).map φ ≤ K := by
      have heq : (JΩ.comap omΩ.subtype).map φ = J := by
        apply le_antisymm
        · rintro g ⟨g', hg', rfl⟩
          have hg'' : (g' : OmV ≃ₗ[GaloisField 2 3] OmV) ∈ JΩ := hg'
          obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp hg''
          have hgy : g' = y := Subtype.ext hyval.symm
          rw [hgy]
          exact Subgroup.mem_comap.mp hy
        · intro g hg
          obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp (hJΩmap.symm ▸ hg)
          have hyΩ : (y : OmV ≃ₗ[GaloisField 2 3] OmV) ∈ JΩ := ⟨y, hy, rfl⟩
          exact ⟨y, hyΩ, hyval⟩
      rw [heq]; exact hJK
    exact ggA8Nbr_omZblock_not_le_K φ hinj (hJΩ.1.trans inf_le_left) h13 hZc hKm hle
  ·
    obtain ⟨c, hc, hβc, h, hh, hX, hJeq, hm⟩ := hclass
    have hβfun : β = (fun _ : Fin 3 => c) := funext hβc
    have hJeq' : JΩ = specialBlock omQ (F.ι (ofAdd fun _ : Fin 3 => c)) h := by
      rw [hβfun] at hJeq; exact hJeq
    have hJΩ' : CFSG.Assembly.IsComponentOf JΩ
        (omΩ ⊓ Subgroup.centralizer {F.ι (ofAdd fun _ : Fin 3 => c)}) := by
      rw [hβfun] at hJΩ; exact hJΩ
    have hh' : h ∈ primaryFactors (F.ι (ofAdd fun _ : Fin 3 => c)).toLinearMap := by
      rwa [hβfun] at hh
    have hm' : primaryMultiplicity (F.ι (ofAdd fun _ : Fin 3 => c)).toLinearMap h = 3 := by
      rwa [hβfun] at hm
    have h7Ω : 7 ∣ Nat.card JΩ :=
      om8_class_seven_dvd (omA_le φ Bs) F ζ hζo hdim hal hmoves hc hh' hX hm' hJeq' hJΩ'
    have h7dvd : 7 ∣ Nat.card J := hcardJΩ ▸ h7Ω
    have hJK : J ≤ K := le_of_ggNbr hLB hcfg.1 hcfg.2.2 h7dvd hnb
    obtain ⟨h73Ω, hpermΩ⟩ := omSiegel (omA_le φ Bs) F ζ hζo hdim hal hmoves hc hh' hX hJeq' hm'
    have h73 : ∃ w ∈ J, orderOf w = 73 := by
      obtain ⟨w, hwJ, hword⟩ := h73Ω
      have hwΩ : w ∈ omΩ := (Subgroup.mem_inf.mp (hJΩ.1 hwJ)).1
      refine ⟨φ ⟨w, hwΩ⟩, ?_, ?_⟩
      · obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp hwJ
        have h1 : (⟨w, hwΩ⟩ : ↥omΩ) = y := Subtype.ext hyval.symm
        rw [h1]; exact hy
      · rw [orderOf_injective φ hinj, Subgroup.orderOf_mk, hword]
    let AΩ : Subgroup ↥omΩ := (omA φ Bs).comap omΩ.subtype
    let ιE : Multiplicative (Fin 3 → ZMod 7) →* G :=
      { toFun := fun s => φ ⟨F.ι s, omA_le φ Bs (F.mem s)⟩
        map_one' := by
          rw [← map_one φ]
          apply congrArg φ
          apply Subtype.ext
          simp
        map_mul' := fun s t => by
          rw [← map_mul]
          apply congrArg φ
          apply Subtype.ext
          exact map_mul F.ι s t }
    have hcoord : ∀ t : Fin 3 → ZMod 7, ∃ hb : ιE (ofAdd t) ∈ Bs,
        ιB (Additive.ofMul (⟨ιE (ofAdd t), hb⟩ : ↥Bs)) = Fin.cons 0 t := fun t => hιBt t
    have hAΩmap : AΩ.map φ = Bs ⊓ L := by
      ext g
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨hφA_mem (a : OmV ≃ₗ[GaloisField 2 3] OmV) ha,
          by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
      · rintro ⟨hgBs, hgL⟩
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hrange.symm ▸ hgL)
        have haA : (a : OmV ≃ₗ[GaloisField 2 3] OmV) ∈ omA φ Bs :=
          (hAB a).mpr (by rw [ha]; exact hgBs)
        exact ⟨a, haA, ha⟩
    have hErange : ιE.range = Bs ⊓ L := by
      rw [show ιE.range = AΩ.map φ from ?_, hAΩmap]
      ext g
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨⟨F.ι s, omA_le φ Bs (F.mem s)⟩, F.mem s, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨s, hs⟩ := F.exists_eq ha
        refine ⟨s, ?_⟩
        change φ ⟨F.ι s, omA_le φ Bs (F.mem s)⟩ = φ a
        congr 1
        exact Subtype.ext hs
    refine ⟨hJK, hCJleD, h73, ιB, hιBx, ?_, ?_⟩
    · intro σ hσ
      obtain ⟨w, hw, hwact⟩ := hpermΩ (om8_permSucc σ hσ)
      have hwΩ : w ∈ omΩ := (Subgroup.mem_inf.mp (hJΩ.1 hw.1)).1
      let wG : G := φ ⟨w, hwΩ⟩
      have hwGJ : wG ∈ J := by
        obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp hw.1
        have h1 : (⟨w, hwΩ⟩ : ↥omΩ) = y := Subtype.ext hyval.symm
        change φ ⟨w, hwΩ⟩ ∈ J
        rw [h1]; exact hy
      have hwAΩ : (⟨w, hwΩ⟩ : ↥omΩ) ∈ Subgroup.normalizer (AΩ : Set ↥omΩ) := by
        rw [Subgroup.mem_normalizer_iff]
        intro z
        constructor
        · intro hz
          exact (Subgroup.mem_normalizer_iff.mp hw.2 (z : OmV ≃ₗ[GaloisField 2 3] OmV)).mp hz
        · intro hz
          exact (Subgroup.mem_normalizer_iff.mp hw.2 (z : OmV ≃ₗ[GaloisField 2 3] OmV)).mpr hz
      have hwN : wG ∈ Subgroup.normalizer (ιE.range : Set G) := by
        have h1 : wG ∈ Subgroup.normalizer ((AΩ.map φ) : Set G) :=
          om8_map_normalizer_le φ AΩ (⟨⟨w, hwΩ⟩, hwAΩ, rfl⟩ : wG ∈ (Subgroup.normalizer AΩ).map φ)
        rwa [hAΩmap, ← hErange] at h1
      have hwL : wG ∈ L := by
        rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨⟨w, hwΩ⟩, rfl⟩
      have hwx : wG * x = x * wG := Subgroup.mem_centralizer_iff.mp hxcentL wG hwL
      have hwact' : ∀ t : Fin 3 → ZMod 7,
          wG⁻¹ * ιE (ofAdd t) * wG = ιE (ofAdd (t ∘ om8_permSucc σ hσ)) := by
        intro t
        have h1 : w⁻¹ * F.ι (ofAdd t) * w = F.ι (ofAdd (t ∘ om8_permSucc σ hσ)) := hwact t
        have hmem : w⁻¹ * F.ι (ofAdd t) * w ∈ omΩ := omA_le φ Bs (by rw [h1]; exact F.mem _)
        have h2 : (⟨w, hwΩ⟩ : ↥omΩ)⁻¹ * ⟨F.ι (ofAdd t), omA_le φ Bs (F.mem _)⟩ *
            ⟨w, hwΩ⟩ = ⟨w⁻¹ * F.ι (ofAdd t) * w, hmem⟩ := Subtype.ext rfl
        have hwG_eq : wG = φ ⟨w, hwΩ⟩ := rfl
        have hιE_eq : ιE (ofAdd t) = φ ⟨F.ι (ofAdd t), omA_le φ Bs (F.mem _)⟩ := rfl
        calc wG⁻¹ * ιE (ofAdd t) * wG
            = φ ((⟨w, hwΩ⟩ : ↥omΩ)⁻¹ * ⟨F.ι (ofAdd t), omA_le φ Bs (F.mem _)⟩ *
                ⟨w, hwΩ⟩) := by
              rw [hwG_eq, hιE_eq, ← map_inv, ← map_mul, ← map_mul]
          _ = φ ⟨w⁻¹ * F.ι (ofAdd t) * w, hmem⟩ := by rw [h2]
          _ = φ ⟨F.ι (ofAdd (t ∘ om8_permSucc σ hσ)), omA_le φ Bs (F.mem _)⟩ := by
              congr 1
              exact Subtype.ext h1
          _ = ιE (ofAdd (t ∘ om8_permSucc σ hσ)) := rfl
      obtain ⟨ψ, hψ, hψact⟩ := om8_conjAut_perm hxB ιB hιBx hcoord hsplit hErange
        (om8_permSucc σ hσ) hwGJ hwN hwx hwact'
      refine ⟨ψ, hψ, fun b => ?_⟩
      rw [hψact b, om8_perm4_permSucc σ hσ]
    · obtain ⟨ψ, hψ, hψact⟩ := hιBmove (1 : Equiv.Perm (Fin 3)) om8_etaSign om8_etaSign_mem
      refine ⟨ψ, hψ, fun b => ?_⟩
      rw [hψact b, om8_vecMul_signThree]
      simp

end CFSG.StandardType.A8Coord

end
