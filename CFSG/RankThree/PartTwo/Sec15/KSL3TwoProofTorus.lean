module

public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofDefs
public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofDiag
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace KSL3Two

open CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.RankThree.PartTwo.Sec16.ProofHess

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] def goodLiftSet (π : Bool) (q : ℕ) (K : Type) [Field K] (r : ℕ)
    (P : Subgroup (ProjGenLinGroup (Fin 3) K)) : Set (GL (Fin 3) K) :=
  {g | g ∈ slPi π 3 q K ∧ g ^ r = 1 ∧ ProjGenLinGroup.mk g ∈ P}

@[expose] noncomputable def goodLift (π : Bool) (q : ℕ) (K : Type) [Field K] (r : ℕ)
    (P : Subgroup (ProjGenLinGroup (Fin 3) K)) : Subgroup (GL (Fin 3) K) :=
  Subgroup.closure (goodLiftSet π q K r P)

theorem mem_goodLift_iff (hK : PiField π p f K) {r : ℕ} (hr3 : Nat.Coprime r 3)
    {P : Subgroup (ProjGenLinGroup (Fin 3) K)} (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    {g : GL (Fin 3) K} :
    g ∈ goodLift π (p ^ f) K r P ↔
      g ∈ slPi π 3 (p ^ f) K ∧ g ^ r = 1 ∧ ProjGenLinGroup.mk g ∈ P := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨one_mem _, one_pow _, by rw [map_one]; exact one_mem _⟩
    | mul x y _ _ hx hy =>
      have hc : x * y = y * x :=
        commute_of_mk_commute hK hx.1 hy.1 (hP _ hy.2.2 _ hx.2.2) hr3 hx.2.1
      refine ⟨mul_mem hx.1 hy.1, ?_, ?_⟩
      · rw [(show Commute x y from hc).mul_pow r, hx.2.1, hy.2.1, one_mul]
      · rw [map_mul]
        exact mul_mem hx.2.2 hy.2.2
    | inv x _ hx =>
      exact ⟨inv_mem hx.1, by rw [inv_pow, hx.2.1, inv_one], by rw [map_inv]; exact inv_mem hx.2.2⟩
  · intro hg
    exact Subgroup.subset_closure hg

theorem commute_of_mem_goodLift (hK : PiField π p f K) {r : ℕ} (hr3 : Nat.Coprime r 3)
    {P : Subgroup (ProjGenLinGroup (Fin 3) K)} (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    {s : GL (Fin 3) K} (hs : s ∈ slPi π 3 (p ^ f) K)
    (hsP : ∀ x ∈ P, ProjGenLinGroup.mk s * x = x * ProjGenLinGroup.mk s) {g : GL (Fin 3) K}
    (hg : g ∈ goodLift π (p ^ f) K r P) : s * g = g * s := by
  obtain ⟨hgS, hgr, hgP⟩ := (mem_goodLift_iff hK hr3 hP).mp hg
  exact (commute_of_mk_commute hK hgS hs (hsP _ hgP) hr3 hgr).symm

theorem mem_normalizer_goodLift (hK : PiField π p f K) {r : ℕ} (hr3 : Nat.Coprime r 3)
    {P : Subgroup (ProjGenLinGroup (Fin 3) K)} (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    {s : GL (Fin 3) K} (hs : s ∈ slPi π 3 (p ^ f) K)
    (hsN : ProjGenLinGroup.mk s ∈ Subgroup.normalizer (P : Set (ProjGenLinGroup (Fin 3) K))) :
    s ∈ Subgroup.normalizer (goodLift π (p ^ f) K r P : Set (GL (Fin 3) K)) := by
  have key : ∀ t ∈ slPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk t ∈ Subgroup.normalizer (P : Set (ProjGenLinGroup (Fin 3) K)) →
      ∀ g ∈ goodLift π (p ^ f) K r P, t * g * t⁻¹ ∈ goodLift π (p ^ f) K r P := by
    intro t ht htN g hg
    obtain ⟨hgS, hgr, hgP⟩ := (mem_goodLift_iff hK hr3 hP).mp hg
    refine (mem_goodLift_iff hK hr3 hP).mpr ⟨mul_mem (mul_mem ht hgS) (inv_mem ht), ?_, ?_⟩
    · rw [_root_.conj_pow, hgr, mul_one, mul_inv_cancel]
    · rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp htN _).mp hgP
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key s hs hsN g, fun h => ?_⟩
  have := key s⁻¹ (inv_mem hs) (by rw [map_inv]; exact inv_mem hsN) _ h
  simpa [mul_assoc] using this

theorem eq_one_of_mem_goodLift (hK : PiField π p f K) {r : ℕ} (hr3 : Nat.Coprime r 3)
    {P : Subgroup (ProjGenLinGroup (Fin 3) K)} (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    {g : GL (Fin 3) K} (hg : g ∈ goodLift π (p ^ f) K r P) (h1 : ProjGenLinGroup.mk g = 1) :
    g = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨hgS, hgr, -⟩ := (mem_goodLift_iff hK hr3 hP).mp hg
  rw [mk_eq_one_iff_mem_statedScalars] at h1
  obtain ⟨ε, rfl⟩ := h1
  have hε3 : ε ^ 3 = 1 := pow_three_eq_one_of_scalar_mem_slPi hπ hgS
  have hεr : ε ^ r = 1 := by
    rw [← map_pow] at hgr
    have h00 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hgr
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at h00
    exact Units.ext h00
  have hε1 : ε = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hr3
    (orderOf_dvd_of_pow_eq_one hεr) (orderOf_dvd_of_pow_eq_one hε3))
  rw [hε1, map_one]

theorem exists_mem_goodLift_mk_eq (hK : PiField π p f K) {r : ℕ} (hr3 : Nat.Coprime r 3)
    {P : Subgroup (ProjGenLinGroup (Fin 3) K)} (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hPS : P ≤ projImage (slPi π 3 (p ^ f) K)) (hPr : ∀ x ∈ P, x ^ r = 1)
    {x : ProjGenLinGroup (Fin 3) K} (hx : x ∈ P) :
    ∃ g ∈ goodLift π (p ^ f) K r P, ProjGenLinGroup.mk g = x := by
  have hord : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one (hPr x hx)
  have hcop : Nat.Coprime 3 (orderOf x) := Nat.Coprime.coprime_dvd_right hord hr3.symm
  obtain ⟨s, hs, hsx, hs1⟩ := exists_lift_pow_eq_one hK (hPS hx) hcop
  refine ⟨s, (mem_goodLift_iff hK hr3 hP).mpr ⟨hs, ?_, hsx ▸ hx⟩, hsx⟩
  obtain ⟨k, hk⟩ := hord
  rw [hk, pow_mul, hs1, one_pow]

@[expose] def diagGL (L : Type) [Field L] : Subgroup (GL (Fin 3) L) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) L).IsDiag}
  mul_mem' {a b} ha hb := by
    change ((a * b : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).IsDiag
    rw [Units.val_mul, ← (show (a : Matrix (Fin 3) (Fin 3) L).IsDiag from ha).diagonal_diag,
      ← (show (b : Matrix (Fin 3) (Fin 3) L).IsDiag from hb).diagonal_diag,
      Matrix.diagonal_mul_diagonal]
    exact Matrix.isDiag_diagonal _
  one_mem' := by
    change ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).IsDiag
    rw [Units.val_one]
    exact Matrix.isDiag_one
  inv_mem' {a} ha := by
    change ((a⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).IsDiag
    rw [Matrix.coe_units_inv, ← (show (a : Matrix (Fin 3) (Fin 3) L).IsDiag from ha).diagonal_diag,
      Matrix.inv_diagonal]
    exact Matrix.isDiag_diagonal _

theorem zpowers_sup_zpowers_eq {G : Type*} [Group G] {H : Subgroup G} [Finite H] {r : ℕ}
    (hr : r.Prime) (hHc : Nat.card H = r ^ 2) (hHr : ∀ x ∈ H, x ^ r = 1) {a b : G} (ha : a ∈ H)
    (ha1 : a ≠ 1) (hb : b ∈ H) (hab : b ∉ Subgroup.zpowers a) :
    Subgroup.zpowers a ⊔ Subgroup.zpowers b = H := by
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ H :=
    sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)
  have : Fact r.Prime := ⟨hr⟩
  have hfin : Finite (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hdvd : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) ∣ r ^ 2 :=
    hHc ▸ Subgroup.card_dvd_of_le hle
  have hao : orderOf a = r := orderOf_eq_prime (hHr a ha) ha1
  have hra : r ∣ Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) := by
    have h := Subgroup.card_dvd_of_le (le_sup_left :
      Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    rwa [Nat.card_zpowers, hao] at h
  obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow hr).mp hdvd
  have hi2 : i = 2 := by
    interval_cases i
    · rw [hik, pow_zero] at hra
      exact absurd (Nat.le_of_dvd one_pos hra) (by have := hr.two_le; omega)
    · exfalso
      apply hab
      have heq : Subgroup.zpowers a = Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hik, Nat.card_zpowers, hao, pow_one])
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    · rfl
  subst hi2
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hik, hHc])

theorem exists_frame (hK : PiField π p f K) {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) (hrp : r ≠ p)
    {P : Subgroup (ProjGenLinGroup (Fin 3) K)} (hPS : P ≤ projImage (slPi π 3 (p ^ f) K))
    (hPa : CFSG.Assembly.IsElemAbelian r P) (hPc : Nat.card P = r ^ 2) :
    ∃ θ : GL (Fin 3) K →* GL (Fin 3) (AlgebraicClosure K), Function.Injective θ ∧
      (∀ c : Kˣ, ∃ c' : AlgebraicClosure K, c' ≠ 0 ∧
        ((θ (GeneralLinearGroup.scalar (Fin 3) c) : GL (Fin 3) (AlgebraicClosure K)) :
          Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) = c' • 1) ∧
      (∀ s ∈ slPi π 3 (p ^ f) K,
        (∀ x ∈ P, ProjGenLinGroup.mk s * x = x * ProjGenLinGroup.mk s) →
        ((θ s : GL (Fin 3) (AlgebraicClosure K)) :
          Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)).IsDiag) ∧
      (∀ s ∈ slPi π 3 (p ^ f) K,
        ProjGenLinGroup.mk s ∈ Subgroup.normalizer (P : Set (ProjGenLinGroup (Fin 3) K)) →
        ∃ σ : Fin 3 → Fin 3, IsMonomialWith ((θ s : GL (Fin 3) (AlgebraicClosure K)) :
          Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) σ) ∧
      (∀ s : GL (Fin 3) K, ((θ s : GL (Fin 3) (AlgebraicClosure K)) :
          Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)).IsDiag →
        ∀ x ∈ P, ProjGenLinGroup.mk s * x = x * ProjGenLinGroup.mk s) := by
  have := hK.finite
  have : Finite (GL (Fin 3) K) := inferInstance
  have : Fact r.Prime := ⟨hr⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have : CharP K p := hK.charP
  have hr3' : Nat.Coprime r 3 := (Nat.coprime_primes hr Nat.prime_three).mpr hr3
  have hrK : (r : K) ≠ 0 := by
    intro h
    have hpr : p ∣ r := (CharP.cast_eq_zero_iff K p r).mp h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hK.prime hr).mp hpr).symm
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hPa.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set G := goodLift π (p ^ f) K r P with hG
  have hmem : ∀ g, g ∈ G ↔ g ∈ slPi π 3 (p ^ f) K ∧ g ^ r = 1 ∧ ProjGenLinGroup.mk g ∈ P :=
    fun g => mem_goodLift_iff hK hr3' hPcomm
  set μ : G →* ProjGenLinGroup (Fin 3) K := ProjGenLinGroup.mk.comp G.subtype with hμ
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (eq_one_of_mem_goodLift hK hr3' hPcomm g.2 hg)
  have hμrange : μ.range = P := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ((hmem g).mp g.2).2.2
    · intro hx
      obtain ⟨g, hg, hgx⟩ := exists_mem_goodLift_mk_eq hK hr3' hPcomm hPS hPa.2 hx
      exact ⟨⟨g, hg⟩, hgx⟩
  have hGc : Nat.card G = r ^ 2 := by
    rw [← hPc, ← hμrange]
    exact Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv
  have hGr : ∀ g ∈ G, g ^ r = 1 := fun g hg => ((hmem g).mp hg).2.1
  set L := AlgebraicClosure K with hL
  have : NeZero (r : K) := ⟨hrK⟩
  have hrL : (r : L) ≠ 0 := by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero _).mpr hrK
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L r
  set ι : GL (Fin 3) K →* GL (Fin 3) L := GeneralLinearGroup.map (algebraMap K L) with hι
  have hιm : ∀ g : GL (Fin 3) K, ((ι g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      (g : Matrix (Fin 3) (Fin 3) K).map (algebraMap K L) := fun g => rfl
  have hιinj : Function.Injective ι := by
    intro g g' h
    apply Units.ext
    ext i j
    have h' := congrArg (fun A : GL (Fin 3) L => (A : Matrix (Fin 3) (Fin 3) L) i j) h
    simp only [hιm, Matrix.map_apply] at h'
    exact (algebraMap K L).injective h'
  have hGfin : Finite G := inferInstance
  obtain ⟨a, haG, ha1⟩ : ∃ a ∈ G, a ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : G = ⊥ := eq_bot_iff.mpr fun g hg => (Subgroup.mem_bot).mpr (hall g hg)
    rw [hbot, Subgroup.card_bot] at hGc
    have := hr.two_le
    have : 1 < r ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  obtain ⟨b, hbG, hba⟩ : ∃ b ∈ G, b ∉ Subgroup.zpowers a := by
    by_contra hall
    push Not at hall
    have hle : G ≤ Subgroup.zpowers a := fun g hg => hall g hg
    have hzc : Nat.card (Subgroup.zpowers a) = r := by
      rw [Nat.card_zpowers, orderOf_eq_prime (hGr a haG) ha1]
    have : Finite (Subgroup.zpowers a) := Nat.finite_of_card_ne_zero (by rw [hzc]; exact hr.ne_zero)
    have hcard := Subgroup.card_le_of_le hle
    rw [hGc, hzc] at hcard
    have := hr.two_le
    nlinarith
  have hGeq := zpowers_sup_zpowers_eq hr hGc hGr haG ha1 hbG hba
  have hab : a * b = b * a := (commute_of_mk_commute hK ((hmem a).mp haG).1 ((hmem b).mp hbG).1
    (hPcomm _ ((hmem b).mp hbG).2.2 _ ((hmem a).mp haG).2.2) hr3' (hGr a haG))
  have hA : ((ι a : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hGr a haG, map_one, Units.val_one]
  have hB : ((ι b : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hGr b hbG, map_one, Units.val_one]
  have hAB : Commute ((ι a : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
      ((ι b : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
    change _ = _
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hab]
  obtain ⟨Q, hQ, α, β, hQα, hQβ⟩ := exists_conj_diag hrL hζ hA hB hAB
  set Qu : GL (Fin 3) L := hQ.unit with hQu
  have hQuQ : ((Qu : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = Q := rfl
  set θ : GL (Fin 3) K →* GL (Fin 3) L := (MulAut.conj Qu⁻¹).toMonoidHom.comp ι with hθ
  have hθapp : ∀ g, θ g = Qu⁻¹ * ι g * Qu := by
    intro g
    simp [hθ]
  have hθinj : Function.Injective θ := (MulAut.conj Qu⁻¹).injective.comp hιinj
  have hconjd : ∀ {g : GL (Fin 3) K} {d : Fin 3 → L},
      ((ι g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * Q = Q * diagonal d →
      θ g ∈ diagGL L := by
    intro g d h
    change ((θ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).IsDiag
    rw [hθapp, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hQuQ, h, ← Matrix.mul_assoc,
      ← hQuQ, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    exact Matrix.isDiag_diagonal _
  have hGdiag : ∀ g ∈ G, θ g ∈ diagGL L := by
    have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ (diagGL L).comap θ :=
      sup_le (Subgroup.zpowers_le.mpr (hconjd hQα)) (Subgroup.zpowers_le.mpr (hconjd hQβ))
    intro g hg
    rw [← hGeq] at hg
    exact hle hg
  set H := G.map θ with hH
  have hHdiag : ∀ u ∈ H, ((u : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).IsDiag := by
    rintro _ ⟨g, hg, rfl⟩
    exact hGdiag g hg
  have hHdet : ∀ u ∈ H, ((u : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hθapp, Units.val_mul, Units.val_mul, Matrix.det_units_conj', hιm, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, ((mem_slPi_iff hπ).mp ((hmem g).mp hg).1).2, map_one]
  have hHc : Nat.card H = r ^ 2 := by rw [hH, Subgroup.card_map_of_injective hθinj, hGc]
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hHc]; exact pow_ne_zero _ hr.ne_zero)
  have hHnc : ¬ IsCyclic H := by
    intro hcyc
    obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
    have hur : u ^ r = 1 := by
      obtain ⟨g, hg, hgu⟩ := u.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hgu, ← map_pow, hGr g hg, map_one, Subgroup.coe_one]
    have hdvd := orderOf_dvd_of_pow_eq_one hur
    rw [hu, hHc] at hdvd
    have := hr.two_le
    have := Nat.le_of_dvd hr.pos hdvd
    nlinarith
  have hsep := fun i j (hij : i ≠ j) => exists_ne_diag_of_not_isCyclic hHnc hHdiag hHdet hij
  refine ⟨θ, hθinj, fun c => ?_, fun s hs hsP => ?_, fun s hs hsN => ?_, fun s hsd => ?_⟩
  ·
    refine ⟨algebraMap K L (c : K), (map_ne_zero _).mpr c.ne_zero, ?_⟩
    have hιs : ((ι (GeneralLinearGroup.scalar (Fin 3) c) : GL (Fin 3) L) :
        Matrix (Fin 3) (Fin 3) L) = algebraMap K L (c : K) • 1 := by
      rw [hιm]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [GeneralLinearGroup.coe_scalar]
      · simp [GeneralLinearGroup.coe_scalar, hij]
    rw [hθapp, Units.val_mul, Units.val_mul, hιs, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  ·
    apply isDiag_of_commute hHdiag hsep
    rintro _ ⟨g, hg, rfl⟩
    have hc := commute_of_mem_goodLift hK hr3' hPcomm hs hsP hg
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hc]
  ·
    have hsG := mem_normalizer_goodLift hK hr3' hPcomm hs hsN
    refine exists_monomial_of_normalizes hHdiag hsep ?_
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨s⁻¹ * g * s, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hsG) g).mp hg
    rwa [inv_inv] at this
  ·
    intro x hx
    obtain ⟨g, hg, rfl⟩ := exists_mem_goodLift_mk_eq hK hr3' hPcomm hPS hPa.2 hx
    have hc := commute_of_isDiag hsd (hGdiag g hg)
    have hθc : θ (s * g) = θ (g * s) := by
      apply Units.ext
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul, hc]
    rw [← map_mul, ← map_mul, hθinj hθc]

theorem a3_lemma : ∀ σ σ' : Fin 3 → Fin 3, σ ∘ σ ∘ σ = id → σ' ∘ σ' ∘ σ' = id →
    σ = id ∨ σ' = id ∨ σ' ∘ σ = id ∨ σ' ∘ σ ∘ σ = id := by
  decide

theorem centralizes_of_normalizes (hK : PiField π p f K) {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    (hrp : r ≠ p) {P : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hPS : P ≤ projImage (slPi π 3 (p ^ f) K)) (hPa : CFSG.Assembly.IsElemAbelian r P)
    (hPc : Nat.card P = r ^ 2) {z₁ z₂ : ProjGenLinGroup (Fin 3) K}
    (hz₁S : z₁ ∈ projImage (slPi π 3 (p ^ f) K)) (hz₂S : z₂ ∈ projImage (slPi π 3 (p ^ f) K))
    (hz₁N : z₁ ∈ Subgroup.normalizer (P : Set (ProjGenLinGroup (Fin 3) K)))
    (hz₂N : z₂ ∈ Subgroup.normalizer (P : Set (ProjGenLinGroup (Fin 3) K)))
    (hz₁3 : z₁ ^ 3 = 1) (hz₂3 : z₂ ^ 3 = 1) :
    (∀ x ∈ P, z₁ * x = x * z₁) ∨ (∀ x ∈ P, z₂ * x = x * z₂) ∨
      (∀ x ∈ P, z₂ * z₁ * x = x * (z₂ * z₁)) ∨
      (∀ x ∈ P, z₂ * z₁ * z₁ * x = x * (z₂ * z₁ * z₁)) := by
  obtain ⟨θ, -, hscal, -, hmono, hcent⟩ := exists_frame hK hr hr3 hrp hPS hPa hPc
  obtain ⟨g₁, hg₁S, rfl⟩ := hz₁S
  obtain ⟨g₂, hg₂S, rfl⟩ := hz₂S
  obtain ⟨σ₁, hσ₁⟩ := hmono g₁ hg₁S hz₁N
  obtain ⟨σ₂, hσ₂⟩ := hmono g₂ hg₂S hz₂N
  have hcube : ∀ g : GL (Fin 3) K, ProjGenLinGroup.mk g ^ 3 = 1 → ∀ σ : Fin 3 → Fin 3,
      IsMonomialWith ((θ g : GL (Fin 3) (AlgebraicClosure K)) :
        Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) σ → σ ∘ σ ∘ σ = id := by
    intro g h3 σ hσ
    have hsc : g ^ 3 ∈ StatedScalars (Fin 3) K := by
      rw [← mk_eq_one_iff_mem_statedScalars, map_pow, h3]
    obtain ⟨c, hc⟩ := hsc
    obtain ⟨c', hc'0, hc'⟩ := hscal c
    have h1 : IsMonomialWith ((θ (g ^ 3) : GL (Fin 3) (AlgebraicClosure K)) :
        Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) (σ ∘ σ ∘ σ) := by
      rw [map_pow, pow_three, Units.val_mul, Units.val_mul]
      exact hσ.mul (hσ.mul hσ)
    have h2 : IsMonomialWith ((θ (g ^ 3) : GL (Fin 3) (AlgebraicClosure K)) :
        Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) id := by
      rw [← hc, hc']
      exact isMonomialWith_smul_one hc'0
    exact h1.unique h2
  rcases a3_lemma σ₁ σ₂ (hcube g₁ hz₁3 σ₁ hσ₁) (hcube g₂ hz₂3 σ₂ hσ₂) with h | h | h | h
  · left
    rw [h] at hσ₁
    exact hcent g₁ hσ₁.isDiag
  · right; left
    rw [h] at hσ₂
    exact hcent g₂ hσ₂.isDiag
  · right; right; left
    rw [← map_mul]
    have h12 := hσ₂.mul hσ₁
    rw [h, ← Units.val_mul, ← map_mul] at h12
    exact hcent (g₂ * g₁) h12.isDiag
  · right; right; right
    rw [← map_mul, ← map_mul]
    have h12 := (hσ₂.mul hσ₁).mul hσ₁
    have h' : (σ₂ ∘ σ₁) ∘ σ₁ = id := h
    rw [h', ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul] at h12
    exact hcent (g₂ * g₁ * g₁) h12.isDiag

end KSL3Two

open KSL3Two Sec4
open CFSG.Assembly.RankThreeEven (projImage)

theorem ks1521TorusCent : KS1521TorusCent := by
  intro X _ _ n hn hiso r hr hr3 P hPa hPc
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model hn hiso
  set S := projImage (slPi π 3 (2 ^ n) K) with hS
  set ψ : X →* Matrix.ProjGenLinGroup (Fin 3) K := S.subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hψS : ∀ x, ψ x ∈ S := fun x => (φ x).2
  have hP'S : P.map ψ ≤ S := by
    rintro _ ⟨x, -, rfl⟩
    exact hψS x
  have hP'a := CFSG.SectionRank.isElemAbelian_map hPa ψ
  have hP'c : Nat.card (P.map ψ) = r ^ 2 := by rw [Subgroup.card_map_of_injective hψinj, hPc]
  obtain ⟨θ, hθinj, -, hdiag, -, -⟩ := exists_frame hK hr (by omega) (by omega) hP'S hP'a hP'c
  have hC : ∀ w ∈ Subgroup.centralizer (P : Set X), ∀ g : GL (Fin 3) K,
      Matrix.ProjGenLinGroup.mk g = ψ w →
      ∀ u ∈ P.map ψ, Matrix.ProjGenLinGroup.mk g * u = u * Matrix.ProjGenLinGroup.mk g := by
    rintro w hw g hg _ ⟨u, hu, rfl⟩
    rw [hg, ← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hw u hu)]
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  apply hψinj
  obtain ⟨s, hs, hsx⟩ := hψS (x : X)
  obtain ⟨t, ht, hty⟩ := hψS (y : X)
  have hc := commute_of_isDiag (hdiag s hs (hC x x.2 s hsx)) (hdiag t ht (hC y y.2 t hty))
  have hθc : θ (s * t) = θ (t * s) := by
    apply Units.ext
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, hc]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, ← hsx, ← hty, ← map_mul, ← map_mul,
    hθinj hθc]

theorem ks1522TorusMeet : KS1522TorusMeet := by
  intro X _ _ n hn hiso r hr hr3 P hPa hPc E hEa hE9 hEN
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model hn hiso
  set S := projImage (slPi π 3 (2 ^ n) K) with hS
  set ψ : X →* Matrix.ProjGenLinGroup (Fin 3) K := S.subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hψS : ∀ x, ψ x ∈ S := fun x => (φ x).2
  have hP'S : P.map ψ ≤ S := by
    rintro _ ⟨x, -, rfl⟩
    exact hψS x
  have hP'a := CFSG.SectionRank.isElemAbelian_map hPa ψ
  have hP'c : Nat.card (P.map ψ) = r ^ 2 := by rw [Subgroup.card_map_of_injective hψinj, hPc]
  obtain ⟨z₁, hz₁E, hz₁1, z₂, hz₂E, hz₂⟩ :=
    CFSG.RankThree.PartTwo.Sec16.ProofHess.exists_two_of_card_nine hEa hE9
  have hN : ∀ z ∈ E, ψ z ∈ Subgroup.normalizer ((P.map ψ : Subgroup _) : Set _) :=
    fun z hz => Subgroup.le_normalizer_map ψ ⟨z, hEN hz, rfl⟩
  have h3 : ∀ z ∈ E, ψ z ^ 3 = 1 := fun z hz => by rw [← map_pow, hEa.2 z hz, map_one]
  have hcent : ∀ z : X, (∀ x ∈ P.map ψ, ψ z * x = x * ψ z) →
      z ∈ Subgroup.centralizer (P : Set X) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    apply hψinj
    rw [map_mul, map_mul]
    exact (hz _ ⟨u, hu, rfl⟩).symm
  have hz₂1 : z₂ ≠ 1 := fun h1 => hz₂ (h1 ▸ Subgroup.one_mem _)
  rcases centralizes_of_normalizes hK hr (by omega) (by omega) hP'S hP'a hP'c (hψS z₁) (hψS z₂)
      (hN z₁ hz₁E) (hN z₂ hz₂E) (h3 z₁ hz₁E) (h3 z₂ hz₂E) with h | h | h | h
  · exact ⟨z₁, hz₁E, hz₁1, hcent z₁ h⟩
  · exact ⟨z₂, hz₂E, hz₂1, hcent z₂ h⟩
  · refine ⟨z₂ * z₁, mul_mem hz₂E hz₁E, fun h1 => hz₂ ?_, hcent _ (by rw [map_mul]; exact h)⟩
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (Subgroup.mem_zpowers z₁)
  · refine ⟨z₂ * z₁ * z₁, mul_mem (mul_mem hz₂E hz₁E) hz₁E, fun h1 => hz₂ ?_,
      hcent _ (by rw [map_mul, map_mul]; exact h)⟩
    have : z₂ = (z₁ * z₁)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact h1)
    rw [this]
    exact inv_mem (mul_mem (Subgroup.mem_zpowers z₁) (Subgroup.mem_zpowers z₁))

end CFSG.RankThree.PartTwo.Sec15
