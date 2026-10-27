module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA0
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm52AuxSmear
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KHat
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Basic

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53A

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type u} [Group Γ]

theorem isElemAbelian_zpowers {p : ℕ} {a : Γ} (hap : a ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers a) := CFSG.Open.isElemAbelian_zpowers hap

theorem not_isSolvable_of_mem_lcal {X J : Subgroup Γ} (hJ : J ∈ lcal X) :
    ¬ Group.IsSolvable ↥J := by
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  intro hsol
  exact hnc (isMulCommutative_iff.mpr fun a b => IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)

theorem mem_map_conj_inv_iff {J : Subgroup Γ} {w : Γ} {z : Γ} :
    z ∈ J.map (MulAut.conj w⁻¹).toMonoidHom ↔ w * z * w⁻¹ ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change w * (w⁻¹ * y * w⁻¹⁻¹) * w⁻¹ ∈ J
    have : w * (w⁻¹ * y * w⁻¹⁻¹) * w⁻¹ = y := by group
    rwa [this]
  · intro h
    refine ⟨w * z * w⁻¹, h, ?_⟩
    change w⁻¹ * (w * z * w⁻¹) * w⁻¹⁻¹ = z
    group

theorem mem_normalizer_of_mem_normalizer_map_conj {J : Subgroup Γ} {a w : Γ}
    (h : a ∈ Subgroup.normalizer ((J.map (MulAut.conj w⁻¹).toMonoidHom : Subgroup Γ) : Set Γ)) :
    w * a * w⁻¹ ∈ Subgroup.normalizer (J : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h2 := Subgroup.mem_normalizer_iff.mp h (w⁻¹ * x * w)
  rw [mem_map_conj_inv_iff, mem_map_conj_inv_iff] at h2
  have e1 : w * (w⁻¹ * x * w) * w⁻¹ = x := by group
  have e2 : w * (a * (w⁻¹ * x * w) * a⁻¹) * w⁻¹ = w * a * w⁻¹ * x * (w * a * w⁻¹)⁻¹ := by group
  rw [e1, e2] at h2
  exact h2

theorem mem_khat_of_forall_normalizer [Finite Γ] {X : Subgroup Γ} (hsol : sol X = ⊥) {w : Γ}
    (hwX : w ∈ X) (h : ∀ J ∈ lcal X, w ∈ Subgroup.normalizer (J : Set Γ)) : w ∈ khat X := by
  by_cases hs : Group.IsSolvable ↥X
  · rw [khat_eq_of_isSolvable hs]
    exact hwX
  · have hl : ltilde X = lcal X := by
      rw [← mcal_eq_lcal_of_sol_eq_bot hsol]
      ext M
      simp [ltilde, hs]
    unfold khat
    rw [hl]
    refine Subgroup.mem_inf.mpr ⟨hwX, ?_⟩
    simp only [Subgroup.mem_iInf]
    exact fun J hJ => h J hJ

theorem normalizer_of_mem_khat [Finite Γ] {X : Subgroup Γ} (hsol : sol X = ⊥) {w : Γ}
    (hw : w ∈ khat X) : ∀ J ∈ lcal X, w ∈ Subgroup.normalizer (J : Set Γ) := by
  intro J hJ
  have hs : ¬ Group.IsSolvable ↥X := fun hs =>
    not_isSolvable_of_mem_lcal hJ
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (lcal_le hJ)))
  have hJl : J ∈ ltilde X := Or.inr ⟨hs, (mcal_eq_lcal_of_sol_eq_bot hsol).symm ▸ hJ⟩
  unfold khat at hw
  have := (Subgroup.mem_inf.mp hw).2
  simp only [Subgroup.mem_iInf] at this
  exact this J hJl

theorem equiv_conj_apply [Finite Γ] {S : Set (Subgroup Γ)} {K : Subgroup Γ}
    (hdp : IsDirectProduct S K) (z : (J : S) → (J : Subgroup Γ)) {J₀ : Subgroup Γ}
    (hJ₀ : J₀ ∈ S) {t : Γ} (ht : t ∈ J₀) :
    ((hdp.equiv z : K) : Γ) * t * ((hdp.equiv z : K) : Γ)⁻¹ =
      ((z ⟨J₀, hJ₀⟩ : J₀) : Γ) * t * ((z ⟨J₀, hJ₀⟩ : J₀) : Γ)⁻¹ := by
  classical
  set a : ↥J₀ := z ⟨J₀, hJ₀⟩ with ha
  let w : (J : S) → (J : Subgroup Γ) := Function.update z ⟨J₀, hJ₀⟩ 1
  have hz : z = Pi.mulSingle (⟨J₀, hJ₀⟩ : S) a * w := by
    funext J
    by_cases hJ : J = ⟨J₀, hJ₀⟩
    · subst hJ
      simp [w, ha]
    · simp [w, hJ]
  have hmul : hdp.equiv z = hdp.equiv (Pi.mulSingle (⟨J₀, hJ₀⟩ : S) a) * hdp.equiv w := by
    rw [← map_mul, ← hz]
  have h1 : ((hdp.equiv (Pi.mulSingle (⟨J₀, hJ₀⟩ : S) a) : K) : Γ) = (a : Γ) := by
    rw [hdp.equiv_apply_of_eq_one ⟨J₀, hJ₀⟩ _ (fun J' hJ' => Pi.mulSingle_eq_of_ne hJ' _)]
    simp
  have h2 : ((hdp.equiv w : K) : Γ) ∈ sSup (S \ {J₀}) := by
    have : hdp.coord hJ₀ (hdp.equiv w) = 1 := by
      rw [hdp.coord_equiv hJ₀]
      simp [w]
    exact (hdp.coord_eq_one_iff hJ₀ _).mp this
  have hc : t * ((hdp.equiv w : K) : Γ) = ((hdp.equiv w : K) : Γ) * t :=
    (hdp.commute_sSup_diff hJ₀ t ht _ h2).eq
  have hm : ((hdp.equiv w : K) : Γ) * t * ((hdp.equiv w : K) : Γ)⁻¹ = t := by
    rw [← hc]
    group
  rw [hmul, Subgroup.coe_mul, h1]
  calc (a : Γ) * ((hdp.equiv w : K) : Γ) * t * ((a : Γ) * ((hdp.equiv w : K) : Γ))⁻¹
      = (a : Γ) * (((hdp.equiv w : K) : Γ) * t * ((hdp.equiv w : K) : Γ)⁻¹) * (a : Γ)⁻¹ := by
        group
    _ = (a : Γ) * t * (a : Γ)⁻¹ := by rw [hm]

section Components

variable [Finite Γ] {p : ℕ} {X : Subgroup Γ}

theorem mem_normalizer_of_isSolvable_cen (hp : p.Prime) (hsol : sol X = ⊥) {a : Γ}
    (haX : a ∈ Subgroup.normalizer (X : Set Γ)) (hap : a ^ p = 1)
    (hcen : Group.IsSolvable ↥(X ⊓ Subgroup.centralizer {a})) {J : Subgroup Γ}
    (hJ : J ∈ lcal X) : a ∈ Subgroup.normalizer (J : Set Γ) := by
  by_contra hnJ
  set A := Subgroup.zpowers a with hA
  have hdp := isDirectProduct_lcal_kOf hsol
  have hAX : A ≤ Subgroup.normalizer (X : Set Γ) := Subgroup.zpowers_le.mpr haX
  have hperm : ∀ a' ∈ A, ∀ J' ∈ lcal X, J'.map (MulAut.conj a').toMonoidHom ∈ lcal X :=
    fun a' ha' J' hJ' => map_conj_mem_lcal hJ' (hAX ha')
  have hN : A ⊓ Subgroup.normalizer (J : Set Γ) = ⊥ :=
    Thm52Aux.zpowers_inf_normalizer_eq_bot hp hap hnJ
  have hproj := projIn_centralizer_eq hdp hperm hJ
  rw [hN] at hproj
  have hKC : kOf X ⊓ Subgroup.centralizer (A : Set Γ) ≤ X ⊓ Subgroup.centralizer {a} := by
    rw [hA, Thm52Aux.centralizer_zpowers_eq]
    exact inf_le_inf_right _ (kOf_le X)
  have hsurj : Function.Surjective ((hdp.coord hJ).comp
      (Subgroup.inclusion (inf_le_left : kOf X ⊓ Subgroup.centralizer (A : Set Γ) ≤ kOf X))) := by
    intro j
    have hj : (j : Γ) ∈ projIn (lcal X) J (kOf X ⊓ Subgroup.centralizer (A : Set Γ)) := by
      rw [hproj]
      refine Subgroup.mem_inf.mpr ⟨j.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
      rw [hh]
      simp
    obtain ⟨y, hy, hyj⟩ := (hdp.mem_projIn_iff hJ).mp hj
    exact ⟨⟨y, hy⟩, Subtype.ext hyj⟩
  have hsolK : Group.IsSolvable ↥(kOf X ⊓ Subgroup.centralizer (A : Set Γ)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKC)
  exact not_isSolvable_of_mem_lcal hJ (Group.isSolvable_of_surjective hsurj)

theorem commutator_mem_khat (hsol : sol X = ⊥) {a : Γ}
    (haX : a ∈ Subgroup.normalizer (X : Set Γ))
    (hnorm : ∀ J ∈ lcal X, a ∈ Subgroup.normalizer (J : Set Γ)) {w : Γ} (hw : w ∈ X) :
    ⁅a, w⁆ ∈ khat X := by
  have hwN : w ∈ Subgroup.normalizer (X : Set Γ) := Subgroup.le_normalizer hw
  have hgX : ⁅a, w⁆ ∈ X := by
    have h1 : a * w * a⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp haX w).mp hw
    have e : ⁅a, w⁆ = (a * w * a⁻¹) * w⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact mul_mem h1 (inv_mem hw)
  refine mem_khat_of_forall_normalizer hsol hgX fun J hJ => ?_
  have hJ₁ : J.map (MulAut.conj w⁻¹).toMonoidHom ∈ lcal X :=
    map_conj_mem_lcal hJ (inv_mem hwN)
  have h1 : w * a⁻¹ * w⁻¹ ∈ Subgroup.normalizer (J : Set Γ) :=
    mem_normalizer_of_mem_normalizer_map_conj (inv_mem (hnorm _ hJ₁))
  have e : ⁅a, w⁆ = a * (w * a⁻¹ * w⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (hnorm J hJ) h1

theorem perfRes_khat_le_kOf (hsol : sol X = ⊥)
    (hOut : ∀ J ∈ lcal X, ∀ P : Subgroup (MulAut ↥J), Group.IsPerfect ↥P →
      P ≤ (MulAut.conj : ↥J →* MulAut ↥J).range) :
    perfRes (khat X) ≤ kOf X := by
  classical
  have hdp := isDirectProduct_lcal_kOf hsol
  have hPperf : Group.IsPerfect ↥(perfRes (khat X)) := isPerfect_perfRes (khat X)
  have hPkhat : perfRes (khat X) ≤ khat X := perfRes_le _
  have hPJ : ∀ J ∈ lcal X, perfRes (khat X) ≤ Subgroup.normalizer (J : Set Γ) := fun J hJ g hg =>
    normalizer_of_mem_khat hsol (hPkhat hg) J hJ
  intro g hg
  have key : ∀ J : ↥(lcal X), ∃ j : ↥(J : Subgroup Γ), ∀ t : ↥(J : Subgroup Γ),
      (j : Γ) * t * (j : Γ)⁻¹ = g * t * g⁻¹ := by
    intro J
    let f : ↥(perfRes (khat X)) →* MulAut ↥(J : Subgroup Γ) :=
      (J.1.normalizerMonoidHom).comp (Subgroup.inclusion (hPJ J.1 J.2))
    have hperf : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
    have hin := hOut J.1 J.2 f.range hperf
    obtain ⟨j, hj⟩ := hin (f.mem_range.mpr ⟨⟨g, hg⟩, rfl⟩)
    refine ⟨j, fun t => ?_⟩
    have h1 := congrArg (fun φ : MulAut ↥(J : Subgroup Γ) => ((φ t : ↥(J : Subgroup Γ)) : Γ)) hj
    have h2 : ((f ⟨g, hg⟩ t : ↥(J : Subgroup Γ)) : Γ) = g * t * g⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe J.1 ⟨g, hPJ J.1 J.2 hg⟩ t
    simp only [MulAut.conj_apply] at h1
    rw [h2] at h1
    exact h1
  choose j hj using key
  set k : ↥(kOf X) := hdp.equiv j with hk
  set q : Γ := (k : Γ)⁻¹ * g with hq
  have hcomm : ∀ J ∈ lcal X, J ≤ Subgroup.centralizer ({q} : Set Γ) := by
    intro J hJ t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := equiv_conj_apply hdp j hJ ht
    have h2 := hj ⟨J, hJ⟩ ⟨t, ht⟩
    have h3 : g * t * g⁻¹ = (k : Γ) * t * (k : Γ)⁻¹ := by
      rw [hk, h1]
      exact h2.symm
    have h4 : q * t * q⁻¹ = t := by
      rw [hq]
      calc (k : Γ)⁻¹ * g * t * ((k : Γ)⁻¹ * g)⁻¹ = (k : Γ)⁻¹ * (g * t * g⁻¹) * (k : Γ) := by
            group
        _ = t := by rw [h3]; group
    calc t * q = (q * t * q⁻¹) * q := by rw [h4]
      _ = q * t := by group
  have hK : kOf X ≤ Subgroup.centralizer ({q} : Set Γ) := by
    rw [← hdp.sSup_eq]
    exact sSup_le hcomm
  have hqX : q ∈ X :=
    mul_mem (inv_mem ((kOf_le X) k.2)) ((khat_le X) (hPkhat hg))
  have hqC : q ∈ Subgroup.centralizer (kOf X : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hK hh)
  have hq1 : q = 1 := by
    have : q ∈ X ⊓ Subgroup.centralizer (kOf X : Set Γ) := Subgroup.mem_inf.mpr ⟨hqX, hqC⟩
    rw [centralizer_kOf_eq_bot hsol, Subgroup.mem_bot] at this
    exact this
  have : g = (k : Γ) := by
    rw [hq] at hq1
    exact (inv_mul_eq_one.mp hq1).symm
  rw [this]
  exact k.2

theorem perfRes_le_kOf_of_isSolvable_cen (hp : p.Prime) (hsol : sol X = ⊥)
    (hcop : Nat.Coprime p (Nat.card X)) {a : Γ} (haX : a ∈ Subgroup.normalizer (X : Set Γ))
    (hap : a ^ p = 1) (hcen : Group.IsSolvable ↥(X ⊓ Subgroup.centralizer {a}))
    (hOut : ∀ J ∈ lcal X, ∀ P : Subgroup (MulAut ↥J), Group.IsPerfect ↥P →
      P ≤ (MulAut.conj : ↥J →* MulAut ↥J).range) :
    perfRes X ≤ kOf X := by
  have hnorm : ∀ J ∈ lcal X, a ∈ Subgroup.normalizer (J : Set Γ) := fun J hJ =>
    mem_normalizer_of_isSolvable_cen hp hsol haX hap hcen hJ
  have hXN : X ≤ AChief.nrm (khat X) := fun x hx =>
    mem_normalizer_khat_of_mem_normalizer (Subgroup.le_normalizer hx)
  have haN : a ∈ AChief.nrm (khat X) := mem_normalizer_khat_of_mem_normalizer haX
  have hE : IsElemAbelian p (Subgroup.zpowers a) := isElemAbelian_zpowers hap
  have hEY : Subgroup.zpowers a ≤ Subgroup.normalizer (X : Set Γ) := Subgroup.zpowers_le.mpr haX
  have hEN : Subgroup.zpowers a ≤ AChief.nrm (khat X) := Subgroup.zpowers_le.mpr haN
  have himg := AChief.qimg_inf_centralizer hp hE hEY hEN hXN hcop
  have hqz : AChief.qimg (khat X) (Subgroup.zpowers a) =
      Subgroup.zpowers (AChief.qmap (khat X) ⟨a, haN⟩) := SolQuot.qimg_zpowers haN
  have htriv : AChief.qimg (khat X) X ≤
      Subgroup.centralizer ((AChief.qimg (khat X) (Subgroup.zpowers a) : Subgroup _) : Set _) := by
    rw [hqz, Thm52Aux.centralizer_zpowers_eq]
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (AChief.mem_qimg_iff (khat X) X z).mp hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : ⁅a, (x : Γ)⁆ ∈ khat X := commutator_mem_khat hsol haX hnorm hx
    have h1 : ⁅AChief.qmap (khat X) ⟨a, haN⟩, AChief.qmap (khat X) x⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hc)
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hcen' : AChief.qimg (khat X) (X ⊓ Subgroup.centralizer {a}) = AChief.qimg (khat X) X := by
    have := himg
    rw [Thm52Aux.centralizer_zpowers_eq] at this
    rw [this]
    exact inf_eq_left.mpr htriv
  have hsolq : Group.IsSolvable ↥(AChief.qimg (khat X) X) := by
    have h := Group.isSolvable_of_surjective (G := ↥(X ⊓ Subgroup.centralizer {a}))
      (SolQuot.qres_surjective (inf_le_left.trans hXN))
    rw [hcen'] at h
    exact h
  have hbot : CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual
      ↥(AChief.qimg (khat X) X) = ⊥ :=
    (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable).mpr hsolq
  have hmap := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq
    (SolQuot.qres (khat X) X hXN) (SolQuot.qres_surjective hXN)
  rw [hbot] at hmap
  have hle : CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥X ≤
      (SolQuot.qres (khat X) X hXN).ker := (Subgroup.map_eq_bot_iff _).mp hmap
  rw [SolQuot.ker_qres hXN] at hle
  have hperfN : perfRes X ≤ khat X := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hle (by exact hy))
  exact (le_perfRes_of_isPerfect (isPerfect_perfRes X) hperfN).trans
    (perfRes_khat_le_kOf hsol hOut)

end Components

end Thm53A

end CFSG.SignalizerFunctorTheorem.McBride.Near
