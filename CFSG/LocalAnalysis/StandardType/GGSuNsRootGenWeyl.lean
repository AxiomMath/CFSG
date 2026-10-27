module

public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUModel
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneCoord

public section

namespace CFSG.StandardType

namespace SuNsRootGen

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2
  CFSG.StandardType.UCoord CFSG.StandardType.UModel

variable {K : Type} [Field K] {n d p : ℕ} (h : UnitaryFieldData 2 n K)
  {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'} {A : Subgroup (MulAut L')}

@[expose] noncomputable def uvecSU (hp : p.Prime) {u : Kˣ} (hu : u ^ p = 1)
    (hord : orderOf u = p) (huq : u ^ (2 ^ n + 1) = 1) :
    ↥(sumZero d p) →* ↥(unitarySU 2 n K d) :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  ((diagHom d).comp (uvec hu)).codRestrict _ fun f =>
    TableBUE.diagHom_mem_unitarySU h (fun k => uvec_pow_norm hu huq f k)
      (prod_uvec hu hord f)

theorem coe_uvecSU (hp : p.Prime) {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p)
    (huq : u ^ (2 ^ n + 1) = 1) (f : ↥(sumZero d p)) :
    ((uvecSU h hp hu hord huq f : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
      diagHom d (uvec hu f) :=
  rfl

theorem uvecSU_pow (hp : p.Prime) {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p)
    (huq : u ^ (2 ^ n + 1) = 1) (f : ↥(sumZero d p)) :
    uvecSU h hp hu hord huq f ^ p = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, coe_uvecSU, ← map_pow]
  have hup : uvec hu f ^ p = 1 := funext fun k => uvec_pow_eq_one hu f k
  rw [hup, map_one]

private theorem pow_eq_one_of_diagHom {q : ℕ} {D : ↥(unitarySU 2 n K d)} {σ : Fin d → Kˣ}
    (hD : (D : GL (Fin d) K) = diagHom d σ) (hDp : D ^ q = 1) (k : Fin d) : σ k ^ q = 1 := by
  have h1 : (diagHom d σ) ^ q = 1 := by
    rw [← hD, ← Subgroup.coe_pow, hDp, Subgroup.coe_one]
  rw [← map_pow, ← map_one (diagHom (K := K) d)] at h1
  have h2 := diagHom_injective (K := K) d h1
  simpa using congrFun h2 k

private theorem prod_eq_one_of_diagHom (h : UnitaryFieldData 2 n K)
    {D : ↥(unitarySU 2 n K d)} {σ : Fin d → Kˣ}
    (hD : (D : GL (Fin d) K) = diagHom d σ) : ∏ k, σ k = 1 := by
  have hdet := ((mem_unitarySU_iff h).mp D.2).1
  rw [hD, det_diagHom] at hdet
  exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact hdet)

@[expose] noncomputable def torusMapUOf (hp : p.Prime) (hM : IsDiagTorusModelU p φ A)
    {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p) (huq : u ^ (2 ^ n + 1) = 1) :
    ↥(sumZero d p) →* ↥A where
  toFun f :=
    ⟨MulAut.conj (φ (uvecSU h hp hu hord huq f)),
      (hM _).mpr ⟨uvecSU h hp hu hord huq f,
        ⟨uvec hu f, coe_uvecSU h hp hu hord huq f⟩, uvecSU_pow h hp hu hord huq f, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    show MulAut.conj (φ (uvecSU h hp hu hord huq 1)) = 1
    rw [map_one (uvecSU h hp hu hord huq), map_one φ, map_one (MulAut.conj (G := L'))]
  map_mul' f g := by
    apply Subtype.ext
    show MulAut.conj (φ (uvecSU h hp hu hord huq (f * g))) =
      MulAut.conj (φ (uvecSU h hp hu hord huq f)) *
        MulAut.conj (φ (uvecSU h hp hu hord huq g))
    rw [map_mul (uvecSU h hp hu hord huq), map_mul φ, ← map_mul (MulAut.conj (G := L'))]

theorem torusMapUOf_apply (hp : p.Prime) (hM : IsDiagTorusModelU p φ A)
    {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p) (huq : u ^ (2 ^ n + 1) = 1)
    (f : ↥(sumZero d p)) :
    ((torusMapUOf h hp hM hu hord huq f : ↥A) : MulAut L') =
      MulAut.conj (φ (uvecSU h hp hu hord huq f)) :=
  rfl

theorem torusMapUOf_surjective (hp : p.Prime) (hM : IsDiagTorusModelU p φ A)
    {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p) (huq : u ^ (2 ^ n + 1) = 1) :
    Function.Surjective (torusMapUOf h hp hM hu hord huq) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro a
  obtain ⟨D, ⟨σ, hD⟩, hDp, ha⟩ := (hM (a : MulAut L')).mp a.2
  have hσp : ∀ k, σ k ^ p = 1 := pow_eq_one_of_diagHom hD hDp
  have hσprod : ∏ k, σ k = 1 := prod_eq_one_of_diagHom h hD
  obtain ⟨f, hf⟩ := exists_uvec_eq hu hord hσp hσprod
  have hDfeq : uvecSU h hp hu hord huq f = D := by
    apply Subtype.ext
    rw [coe_uvecSU, hf, hD]
  refine ⟨f, Subtype.ext ?_⟩
  rw [torusMapUOf_apply, hDfeq, ha]

theorem torusMapUOf_injective (hp : p.Prime) (hpd : ¬ p ∣ d) (hd : 3 ≤ d)
    (hφker : ∀ g, φ g = 1 → g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker)
    (hM : IsDiagTorusModelU p φ A) {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p)
    (huq : u ^ (2 ^ n + 1) = 1) :
    Function.Injective (torusMapUOf h hp hM hu hord huq) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [injective_iff_map_eq_one]
  intro f hf
  set D : ↥(unitarySU 2 n K d) := uvecSU h hp hu hord huq f with hDdef
  set σ : Fin d → Kˣ := uvec hu f with hσdef
  have hDmat : (D : GL (Fin d) K) = diagHom d σ := by
    rw [hDdef, hσdef]
    exact coe_uvecSU h hp hu hord huq f
  have hf' : MulAut.conj (φ D) = 1 := by
    have h1 := congrArg (fun a : ↥A => (a : MulAut L')) hf
    rw [torusMapUOf_apply, ← hDdef, Subgroup.coe_one] at h1
    exact h1
  have hcentral : ∀ x : L', φ D * x = x * φ D := by
    intro x
    have h1 : MulAut.conj (φ D) x = x := by
      rw [hf']
      rfl
    rw [MulAut.conj_apply] at h1
    calc φ D * x = (φ D * x * (φ D)⁻¹) * φ D := by group
      _ = x * φ D := by rw [h1]
  have hconst : ∀ a b : Fin d, σ a = σ b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    · obtain ⟨m, hma, hmb⟩ := SURep.exists_ne_ne hd a b
      set g : ↥(unitarySU 2 n K d) := SURep.swapU h a b with hgdef
      have hgcoe : (g : GL (Fin d) K) = permGL (Equiv.swap a b) := by
        rw [hgdef, coe_swapU_eq_permGL]
      have hPinv : (permGL (Equiv.swap a b) : GL (Fin d) K)⁻¹ = permGL (Equiv.swap a b) := by
        rw [← map_inv, Equiv.swap_inv]
      have hsw : (Equiv.swap a b).symm = Equiv.swap a b := by
        rw [← Equiv.Perm.inv_def, Equiv.swap_inv]
      have hcomm_phi : φ (D * g * D⁻¹ * g⁻¹) = 1 := by
        have hc := hcentral (φ g)
        simp only [map_mul, map_inv]
        rw [hc]
        group
      have hker : D * g * D⁻¹ * g⁻¹ ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker :=
        hφker _ hcomm_phi
      have hPDP : ∀ e : Fin d → Kˣ,
          permGL (Equiv.swap a b) * diagHom d e * permGL (Equiv.swap a b) =
            diagHom d (e ∘ Equiv.swap a b) := by
        intro e
        have h := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap a b) e
        rwa [hPinv, hsw] at h
      have hmat : ((D * g * D⁻¹ * g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
          diagHom d (fun k => σ k * (σ (Equiv.swap a b k))⁻¹) := by
        calc ((D * g * D⁻¹ * g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K)
            = diagHom d σ * permGL (Equiv.swap a b) * (diagHom d σ)⁻¹ *
                permGL (Equiv.swap a b) := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, hDmat, hgcoe, hPinv]
          _ = diagHom d σ * (permGL (Equiv.swap a b) * diagHom d (σ⁻¹) *
                permGL (Equiv.swap a b)) := by
              rw [← map_inv]
              group
          _ = diagHom d σ * diagHom d (σ⁻¹ ∘ Equiv.swap a b) := by
              rw [hPDP]
          _ = diagHom d (fun k => σ k * (σ (Equiv.swap a b k))⁻¹) := by
              rw [← map_mul]
              rfl
      rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, largeEvenScalars_def,
        MonoidHom.mem_range] at hker
      obtain ⟨c, hc⟩ := hker
      have hdiagc : diagHom d (fun k => σ k * (σ (Equiv.swap a b k))⁻¹) =
          Matrix.GeneralLinearGroup.scalar (Fin d) c := by
        rw [← hmat]
        exact hc.symm
      have hentry : ∀ x : Fin d, (σ x * (σ (Equiv.swap a b x))⁻¹ : K) = (c : K) := by
        intro x
        have h := congrFun (congrFun (congrArg (fun X : GL (Fin d) K =>
          (X : Matrix (Fin d) (Fin d) K)) hdiagc) x) x
        simpa [coe_diagHom] using h
      have hcm : (c : K) = 1 := by
        have h := hentry m
        rw [Equiv.swap_apply_of_ne_of_ne hma hmb] at h
        simpa using h.symm
      have hσab : σ a = σ b := by
        have h := hentry a
        rw [Equiv.swap_apply_left, hcm] at h
        exact mul_inv_eq_one.mp (Units.ext (by simpa using h))
      exact hσab
  have hσ1 : σ = 1 := by
    have hd0 : 0 < d := by omega
    set c : Kˣ := σ ⟨0, hd0⟩ with hcdef
    have hσc : ∀ k, σ k = c := fun k => hconst k ⟨0, hd0⟩
    have hcp : c ^ p = 1 := by
      rw [← hσc ⟨0, hd0⟩]
      exact uvec_pow_eq_one hu f ⟨0, hd0⟩
    have hcd : c ^ d = 1 := by
      have hprod : ∏ k, σ k = c ^ d := by
        rw [Finset.prod_congr rfl (fun k _ => hσc k), Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
      rw [← hprod]
      exact prod_uvec hu hord f
    have hc1 : c = 1 := by
      have h1 := pow_gcd_eq_one.mpr ⟨hcp, hcd⟩
      rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd),
        pow_one] at h1
    funext k
    rw [hσc k, hc1]
    rfl
  rw [hσdef] at hσ1
  exact uvec_injective hu hord (by rw [hσ1, map_one])

@[expose] noncomputable def torusEquivUOf (hp : p.Prime) (hpd : ¬ p ∣ d) (hd : 3 ≤ d)
    (hφker : ∀ g, φ g = 1 → g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker)
    (hM : IsDiagTorusModelU p φ A) {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p)
    (huq : u ^ (2 ^ n + 1) = 1) : ↥(sumZero d p) ≃* ↥A :=
  MulEquiv.ofBijective (torusMapUOf h hp hM hu hord huq)
    ⟨torusMapUOf_injective h hp hpd hd hφker hM hu hord huq,
      torusMapUOf_surjective h hp hM hu hord huq⟩

theorem torusEquivUOf_apply (hp : p.Prime) (hpd : ¬ p ∣ d) (hd : 3 ≤ d)
    (hφker : ∀ g, φ g = 1 → g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker)
    (hM : IsDiagTorusModelU p φ A) {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p)
    (huq : u ^ (2 ^ n + 1) = 1) (f : ↥(sumZero d p)) :
    ((torusEquivUOf h hp hpd hd hφker hM hu hord huq f : ↥A) : MulAut L') =
      MulAut.conj (φ (uvecSU h hp hu hord huq f)) :=
  rfl

theorem ggTorusWeylElt_swapU (hM : IsDiagTorusModelU p φ A) (i j : Fin d) :
    GGTorusWeylElt p A (φ (SURep.swapU h i j)) := by
  classical
  intro a ha
  obtain ⟨D, ⟨σ, hD⟩, hDp, rfl⟩ := (hM a).mp ha
  have hσp : ∀ k, σ k ^ p = 1 := pow_eq_one_of_diagHom hD hDp
  set w : ↥(unitarySU 2 n K d) := SURep.swapU h i j with hwdef
  set E : ↥(unitarySU 2 n K d) := w * D * w⁻¹ * D⁻¹ with hEdef
  have hEmat : (E : GL (Fin d) K) =
      diagHom d (fun k => σ (Equiv.swap i j k) * (σ k)⁻¹) := by
    rw [hEdef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hD, hwdef, coe_swapU_eq_permGL]
    rw [permGL_mul_diagHom_mul_inv, ← map_inv, ← map_mul]
    rfl
  have hEp : E ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hEmat, ← map_pow]
    have hup : (fun k => σ (Equiv.swap i j k) * (σ k)⁻¹) ^ p = 1 := by
      funext k
      rw [Pi.pow_apply, mul_pow, inv_pow, hσp, hσp, inv_one, mul_one]
      rfl
    rw [hup, map_one]
  have he : φ w * ((MulAut.conj (φ D)) (φ w))⁻¹ = φ E := by
    rw [hEdef, MulAut.conj_apply]
    simp only [map_mul, map_inv]
    group
  refine ⟨?_, ?_⟩
  · rw [he, ← map_pow, hEp, map_one]
  · intro a' ha'
    obtain ⟨D', ⟨τ, hD'⟩, hD'p, rfl⟩ := (hM a').mp ha'
    rw [he, MulAut.conj_apply]
    have hcommD : D' * E = E * D' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hD', hEmat]
      exact (diagHom_commute (K := K) τ _).eq
    have hcomm : φ D' * φ E = φ E * φ D' := by
      rw [← map_mul, ← map_mul, hcommD]
    rw [hcomm]
    group

theorem conj_swapU_mem_normalizer (hM : IsDiagTorusModelU p φ A) (i j : Fin d) :
    MulAut.conj (φ (SURep.swapU h i j)) ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  classical
  set w : ↥(unitarySU 2 n K d) := SURep.swapU h i j with hwdef
  set g : MulAut L' := MulAut.conj (φ w) with hgdef
  have hww : w⁻¹ = w := by
    apply Subtype.ext
    rw [Subgroup.coe_inv, hwdef, coe_swapU_eq_permGL, ← map_inv, Equiv.swap_inv]
  have hg_inv : g⁻¹ = g := by
    rw [hgdef, ← map_inv, ← map_inv, hww]
  have hgg : g * g = 1 := by
    nth_rewrite 2 [hg_inv.symm]
    exact mul_inv_cancel g
  have hkey : ∀ b ∈ A, g * b * g⁻¹ ∈ A := by
    intro b hb
    obtain ⟨D, ⟨σ, hD⟩, hDp, rfl⟩ := (hM b).mp hb
    have hmat : ((w * D * w⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
        diagHom d (σ ∘ Equiv.swap i j) := by
      have hsw : (Equiv.swap i j).symm = Equiv.swap i j := by
        rw [← Equiv.Perm.inv_def, Equiv.swap_inv]
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hD, hwdef, coe_swapU_eq_permGL,
        permGL_mul_diagHom_mul_inv, hsw]
    have hDp' : (w * D * w⁻¹) ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, hmat, ← map_pow]
      have hup : (σ ∘ Equiv.swap i j) ^ p = 1 := by
        funext k
        rw [Pi.pow_apply, Function.comp_apply]
        exact pow_eq_one_of_diagHom hD hDp (Equiv.swap i j k)
      rw [hup, map_one]
    refine (hM _).mpr ⟨w * D * w⁻¹, ⟨σ ∘ Equiv.swap i j, hmat⟩, hDp', ?_⟩
    rw [hgdef, ← map_inv, ← map_mul, ← map_mul]
    rw [show (φ w * φ D) * (φ w)⁻¹ = φ (w * D * w⁻¹) from by
      simp only [map_mul, map_inv]]
  rw [Subgroup.mem_set_normalizer_iff]
  intro b
  constructor
  · exact hkey b
  · intro hb
    have h1 := hkey (g * b * g⁻¹) hb
    have h2 : g * (g * b * g⁻¹) * g⁻¹ = b := by
      calc g * (g * b * g⁻¹) * g⁻¹ = (g * g) * b * (g⁻¹ * g⁻¹) := by group
        _ = b := by simp [hgg, hg_inv]
    rwa [h2] at h1

theorem ggConjAut_swapU_eq_of (hp : p.Prime) (hpd : ¬ p ∣ d) (hd : 3 ≤ d)
    (hφker : ∀ g, φ g = 1 → g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker)
    (hM : IsDiagTorusModelU p φ A) {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p)
    (huq : u ^ (2 ^ n + 1) = 1) (i j : Fin d) :
    ggConjAut A (conj_swapU_mem_normalizer h hM i j) =
      MulAut.congr (torusEquivUOf h hp hpd hd hφker hM hu hord huq)
        (permAutV (Equiv.swap i j)) := by
  classical
  refine MulEquiv.ext fun a => Subtype.ext ?_
  obtain ⟨f, hf⟩ := (torusEquivUOf h hp hpd hd hφker hM hu hord huq).surjective a
  rw [← hf]
  set w : ↥(unitarySU 2 n K d) := SURep.swapU h i j with hwdef
  have hDw : w * uvecSU h hp hu hord huq f * w⁻¹ =
      uvecSU h hp hu hord huq (permAutV (Equiv.swap i j) f) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_uvecSU, coe_uvecSU, hwdef,
      coe_swapU_eq_permGL, permGL_mul_diagHom_mul_inv, uvec_permAutV]
  have hval : ((ggConjAut A (conj_swapU_mem_normalizer h hM i j)
        (torusEquivUOf h hp hpd hd hφker hM hu hord huq f) : ↥A) : MulAut L') =
      MulAut.conj (φ (uvecSU h hp hu hord huq (permAutV (Equiv.swap i j) f))) := by
    rw [ggConjAut_apply, torusEquivUOf_apply]
    change MulAut.conj (φ w) * (MulAut.conj (φ (uvecSU h hp hu hord huq f))) *
        (MulAut.conj (φ w))⁻¹ = _
    rw [← map_mul, ← map_mul, ← map_inv]
    congr 1
    rw [← hDw]
    simp only [map_mul, map_inv]
  rw [hval]
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem isReflection_conj_swapU (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hpd : ¬ p ∣ d) (hd : 3 ≤ d)
    (hφker : ∀ g, φ g = 1 → g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker)
    (hM : IsDiagTorusModelU p φ A) {i j : Fin d} (hij : i ≠ j) :
    GGIsReflection p (ggConjAut A (conj_swapU_mem_normalizer h hM i j)) := by
  obtain ⟨u, hord, huq⟩ := exists_orderOf_eq_norm_one (ℓ := 2) (f := n) h hp hpq
  have hu : u ^ p = 1 := hord ▸ pow_orderOf_eq_one u
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one h.one_le hpq
  rw [ggConjAut_swapU_eq_of h hp hpd hd hφker hM hu hord huq i j]
  refine ggIsReflection_congr (torusEquivUOf h hp hpd hd hφker hM hu hord huq) ?_ ?_
  · rw [sq, ← permAutV_mul, Equiv.swap_mul_self, permAutV_one]
  · exact (isPseudoReflection_permAutV_swap hp hp2 hij).2

theorem pair_eq_of_ggConjAut_eq_swapU (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hpd : ¬ p ∣ d) (hd : 3 ≤ d)
    (hφker : ∀ g, φ g = 1 → g ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker)
    (hM : IsDiagTorusModelU p φ A) {i j k l : Fin d} (hij : i ≠ j) (hkl : k ≠ l)
    (heq : ggConjAut A (conj_swapU_mem_normalizer h hM i j) =
      ggConjAut A (conj_swapU_mem_normalizer h hM k l)) :
    ({i, j} : Finset (Fin d)) = {k, l} := by
  obtain ⟨u, hord, huq⟩ := exists_orderOf_eq_norm_one (ℓ := 2) (f := n) h hp hpq
  have hu : u ^ p = 1 := hord ▸ pow_orderOf_eq_one u
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one h.one_le hpq
  have h1 : MulAut.congr (torusEquivUOf h hp hpd hd hφker hM hu hord huq)
      (permAutV (Equiv.swap i j)) =
      MulAut.congr (torusEquivUOf h hp hpd hd hφker hM hu hord huq)
        (permAutV (Equiv.swap k l)) := by
    rw [← ggConjAut_swapU_eq_of h hp hpd hd hφker hM hu hord huq i j,
      ← ggConjAut_swapU_eq_of h hp hpd hd hφker hM hu hord huq k l]
    exact heq
  have h2 : permAutV (Equiv.swap i j) = permAutV (Equiv.swap k l) :=
    (MulAut.congr (torusEquivUOf h hp hpd hd hφker hM hu hord huq)).injective h1
  have h3 : Equiv.swap i j = Equiv.swap k l := permAutV_injective hp hp2 h2
  have hi : i ∈ ({k, l} : Finset (Fin d)) := by
    by_contra hi
    have hik : i ≠ k := fun h' => hi (by simp [h'])
    have hil : i ≠ l := fun h' => hi (by simp [h'])
    have h := congrArg (fun e : Equiv.Perm (Fin d) => e i) h3
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hik hil] at h
    exact hij h.symm
  have hj : j ∈ ({k, l} : Finset (Fin d)) := by
    by_contra hj
    have hjk : j ≠ k := fun h' => hj (by simp [h'])
    have hjl : j ≠ l := fun h' => hj (by simp [h'])
    have h := congrArg (fun e : Equiv.Perm (Fin d) => e j) h3
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hjk hjl] at h
    exact hij h
  have hsub : ({i, j} : Finset (Fin d)) ⊆ {k, l} := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi
    · exact hj
  exact Finset.eq_of_subset_of_card_le hsub
    (by rw [Finset.card_pair hkl, Finset.card_pair hij])

end SuNsRootGen

end CFSG.StandardType

end
