module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PerfectOddCoverLift
public import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.PerfectOddCover

open Matrix CFSG.Open CFSG.BenderSuzuki.MatrixGroups

universe u

section Sections

variable {S T E : Type*} [Group S] [Group T] [Group E]

theorem existsUnique_section_of_mulEquiv (e : S ≃* T) {ρ : E →* S}
    (h : ∃! σ : T →* E, ∀ t, (e.toMonoidHom.comp ρ) (σ t) = t) :
    ∃! σ : S →* E, ∀ s, ρ (σ s) = s := by
  obtain ⟨σ, hσ, huniq⟩ := h
  refine ⟨σ.comp e.toMonoidHom, fun s => e.injective (hσ (e s)), fun τ hτ => ?_⟩
  have h' : τ.comp e.symm.toMonoidHom = σ := huniq _ fun t => by simp [hτ]
  ext s
  simpa using DFunLike.congr_fun h' (e s)

end Sections

section Scalars

variable {K : Type} [Field K]

theorem pow_gcd_eq_one_of_scalar {S : Subgroup (GL (Fin 3) K)} (z : S) {c : K} {q : ℕ}
    (hz : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    (hN : c * c ^ q = 1) (h3 : c ^ 3 = 1) : z ^ Nat.gcd 3 (q + 1) = 1 := by
  have hc : c ^ Nat.gcd 3 (q + 1) = 1 := pow_gcd_eq_one.2 ⟨h3, by rw [pow_succ, mul_comm, hN]⟩
  apply Subtype.ext
  apply Units.ext
  simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hz, ← map_pow, hc, map_one,
    OneMemClass.coe_one, Units.val_one]

variable [Finite K]

theorem isCyclic_card_dvd_of_scalar {S : Subgroup (GL (Fin 3) K)} (Z : Subgroup S)
    (hZ : ∀ z ∈ Z, (z : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K)) {d : ℕ}
    (hd : ∀ z ∈ Z, z ^ d = 1) : IsCyclic Z ∧ Nat.card Z ∣ d := by
  have : IsCyclic (Subgroup.center (GL (Fin 3) K)) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact isCyclic_of_surjective (GeneralLinearGroup.scalar (Fin 3)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  let g : Z →* Subgroup.center (GL (Fin 3) K) :=
    (S.subtype.comp Z.subtype).codRestrict _ fun z => hZ z z.2
  have : IsCyclic Z := isCyclic_of_injective g fun a b h => by
    have h' : ((a : S) : GL (Fin 3) K) = ((b : S) : GL (Fin 3) K) :=
      congrArg (fun x : Subgroup.center (GL (Fin 3) K) => (x : GL (Fin 3) K)) h
    exact Subtype.ext (Subtype.ext h')
  refine ⟨this, ?_⟩
  rw [← IsCyclic.exponent_eq_card]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one fun z => Subtype.ext (by
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using hd z z.2)

end Scalars

theorem eq_bot_of_card_dvd_gcd {G : Type*} [Group G] (C : Subgroup G) {f : ℕ}
    (h : Nat.card C ∣ Nat.gcd 3 (2 ^ f + 1)) :
    (Even f → C = ⊥) ∧ (¬ 3 ∣ Nat.card C → C = ⊥) := by
  refine ⟨fun hf => ?_, fun h3 => ?_⟩
  · obtain ⟨m, rfl⟩ := hf
    have h4 : 2 ^ (m + m) % 3 = 1 := by
      rw [pow_add, ← mul_pow, Nat.pow_mod]
      norm_num
    have hcop : Nat.Coprime 3 (2 ^ (m + m) + 1) := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      omega
    rw [hcop] at h
    exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 h)
  · rcases (Nat.dvd_prime Nat.prime_three).1 (h.trans (Nat.gcd_dvd_left 3 _)) with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · rw [h1] at h3
      exact absurd (dvd_refl 3) h3

section Standard

variable {K : Type} [Field K] [Finite K]

theorem statedSU_existsUnique_section
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {E : Type*} [Group E] [Finite E] (ρ : E →* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) K)
    (hρ : Function.Surjective ρ) (hcen : ρ.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card ρ.ker)) :
    ∃! σ : CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) K →* E, ∀ s, ρ (σ s) = s := by
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hK
  obtain ⟨σ, hσ, huniq, -⟩ :=
    CFSG.SectionRank.EvenCover.even_unitary_three_central_odd_extension_splitting hK hf hρ hcen
      hodd
  exact ⟨σ, hσ, huniq⟩

theorem glaSU_existsUnique_section
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {E : Type*} [Group E] [Finite E] (ρ : E →* GLASUGroup (Fin 3) K (2 ^ f))
    (hρ : Function.Surjective ρ) (hcen : ρ.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card ρ.ker)) :
    ∃! σ : GLASUGroup (Fin 3) K (2 ^ f) →* E, ∀ s, ρ (σ s) = s :=
  statedSU_existsUnique_section hf hK ρ hρ hcen hodd

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits in
theorem mem_glaScalars_subgroupOf_iff {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (A : GLASUGroup (Fin 3) K (2 ^ f)) :
    A ∈ (GLAScalars (Fin 3) K).subgroupOf (GLASUGroup (Fin 3) K (2 ^ f)) ↔
      ∃ c : K, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c ∧
        c * c ^ 2 ^ f = 1 ∧ c ^ 3 = 1 := by
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hK
  rw [Subgroup.mem_subgroupOf, GLAScalars, CFSG.Assembly.largeEvenScalars_def]
  constructor
  · rintro ⟨u, hu⟩
    have hA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (u : K) := by
      rw [← hu, GeneralLinearGroup.coe_scalar]
    have hmem : (A : GL (Fin 3) K) ∈ SUid (unitaryInvolution K 2 f) 3 := by
      rw [SUid_eq_statedSU hK 3]
      exact A.2
    obtain ⟨hdet, hiso⟩ := mem_SUid.1 hmem
    refine ⟨u, hA, ?_, ?_⟩
    · have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hiso
      simp only [hA, conjTr, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
        Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, unitaryInvolution_apply,
        Matrix.one_apply] at h
      simpa [mul_comm] using h
    · rw [hA, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at hdet
      exact hdet
  · rintro ⟨c, hc, hN, -⟩
    refine ⟨Units.mk0 c (left_ne_zero_of_mul_eq_one hN), Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, hc]
    rfl

theorem glaScalars_subgroupOf_isCyclic_card_dvd {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) :
    IsCyclic ((GLAScalars (Fin 3) K).subgroupOf (GLASUGroup (Fin 3) K (2 ^ f))) ∧
      Nat.card ((GLAScalars (Fin 3) K).subgroupOf (GLASUGroup (Fin 3) K (2 ^ f))) ∣
        Nat.gcd 3 (2 ^ f + 1) := by
  refine isCyclic_card_dvd_of_scalar _ (fun z hz => ?_) (fun z hz => ?_)
  · rw [Subgroup.mem_subgroupOf, GLAScalars, CFSG.Assembly.largeEvenScalars_def,
      ← GeneralLinearGroup.center_eq_range_scalar] at hz
    exact hz
  · obtain ⟨c, hc, hN, h3⟩ := (mem_glaScalars_subgroupOf_iff hK z).1 hz
    exact pow_gcd_eq_one_of_scalar z hc hN h3

theorem perfect_odd_cover_unitary_scalarQuotient
    (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = 2 ^ (2 * f)) {L : Type u} [Group L] [Finite L] [Group.IsPerfect L]
    (η : L →* GLAProj (GLASUGroup (Fin 3) K (2 ^ f))) (hη : Function.Surjective η)
    (hcen : η.ker ≤ Subgroup.center L) (hodd : Odd (Nat.card η.ker)) :
    let S := GLASUGroup (Fin 3) K (2 ^ f)
    let Z := (GLAScalars (Fin 3) K).subgroupOf S
    (∀ A : S, A ∈ Z ↔ ∃ c : K, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) c ∧ c * c ^ 2 ^ f = 1 ∧ c ^ 3 = 1) ∧
    ∃ φ : S →* L, η.comp φ = GLAProjMk S ∧ (∀ ψ : S →* L, η.comp ψ = GLAProjMk S → ψ = φ) ∧
      Function.Surjective φ ∧ φ.ker ≤ Z ∧ Z.map φ = η.ker ∧
      (∃ e : S ⧸ φ.ker ≃* L, ∀ A, e (QuotientGroup.mk A) = φ A ∧
        η (e (QuotientGroup.mk A)) = GLAProjMk S A) ∧
      IsCyclic η.ker ∧ Nat.card η.ker = φ.ker.relIndex Z ∧
      Nat.card η.ker ∣ Nat.gcd 3 (2 ^ f + 1) ∧
      (Even f → η.ker = ⊥) ∧ (¬ 3 ∣ Nat.card η.ker → η.ker = ⊥) := by
  intro S Z
  have hK : Nat.card K = (2 ^ f) ^ 2 := by rw [hcard, ← pow_mul, mul_comm]
  have hZ : (GLAProjMk S).ker = Z := QuotientGroup.ker_mk' _
  obtain ⟨hcyc, hdvd⟩ : IsCyclic Z ∧ Nat.card Z ∣ Nat.gcd 3 (2 ^ f + 1) :=
    glaScalars_subgroupOf_isCyclic_card_dvd hK
  rw [← hZ] at hcyc hdvd
  obtain ⟨φ, hφ, huniq, hsurj, hker, hmap, he, hCcyc, hCcard, hCdvd⟩ :=
    perfect_odd_cover_of_split (S := S) (π := GLAProjMk S)
      (fun _ _ _ => glaSU_existsUnique_section hf hK) (QuotientGroup.mk'_surjective _) hdvd hη
      hcen hodd
  rw [hZ] at hker hmap hCcard
  exact ⟨mem_glaScalars_subgroupOf_iff hK, φ, hφ, huniq, hsurj, hker, hmap, he, hCcyc, hCcard,
    hCdvd, eq_bot_of_card_dvd_gcd _ hCdvd⟩

end Standard

section Hyperbolic

variable {K : Type} [Field K]

@[expose] def unitaryProj (J : HermitianForm 3 K) :
    J.specialSubgroup →* ProjectiveSpecialUnitaryMatrixGroup J :=
  ProjGenLinGroup.mk.subgroupMap J.specialSubgroup

@[simp] theorem coe_unitaryProj (J : HermitianForm 3 K) (A : J.specialSubgroup) :
    (unitaryProj J A : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (A : GL (Fin 3) K) :=
  rfl

theorem unitaryProj_surjective (J : HermitianForm 3 K) : Function.Surjective (unitaryProj J) :=
  MonoidHom.subgroupMap_surjective _ _

theorem mem_ker_unitaryProj_iff (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (A : J.specialSubgroup) :
    A ∈ (unitaryProj J).ker ↔
      ∃ c : K, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c ∧
        c * J.conj c = 1 ∧ c ^ 3 = 1 := by
  rw [MonoidHom.mem_ker, ← OneMemClass.coe_eq_one, coe_unitaryProj]
  exact UnitaryModel.special_mk_eq_one_iff J hJ A.2

variable [Finite K]

theorem ker_unitaryProj_isCyclic_card_dvd (J : HermitianForm 3 K) (f : ℕ)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    IsCyclic (unitaryProj J).ker ∧ Nat.card (unitaryProj J).ker ∣ Nat.gcd 3 (2 ^ f + 1) := by
  have hconj := CFSG.BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J (2 ^ f) hcard
    hfixed
  refine isCyclic_card_dvd_of_scalar _ (fun z hz => ?_) (fun z hz => ?_)
  · rw [MonoidHom.mem_ker, ← OneMemClass.coe_eq_one, coe_unitaryProj,
      ProjGenLinGroup.mk_eq_one] at hz
    exact hz
  · obtain ⟨c, hc, hN, h3⟩ := (mem_ker_unitaryProj_iff J hJ z).1 hz
    exact pow_gcd_eq_one_of_scalar z hc (by rwa [← hconj]) h3

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits in
theorem specialSubgroup_eq_SU [CharP K 2] (J : HermitianForm 3 K) (f : ℕ)
    (hconj : ∀ x, J.conj x = x ^ 2 ^ f) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    J.specialSubgroup = SU (unitaryInvolution K 2 f) 3 := by
  ext A
  rw [J.mem_specialSubgroup_iff, mem_SU]
  have hadj : J.conjTranspose (A : Matrix (Fin 3) (Fin 3) K) =
      conjTr (unitaryInvolution K 2 f) (A : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    simp [HermitianForm.conjTranspose, conjTr, hconj, iterateFrobenius_def]
  have hform : J.form = antidiag 3 := by
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [antidiag, Fin.rev]
  rw [hadj, hform, and_comm, Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one]

theorem nonempty_specialSubgroup_mulEquiv_statedSU (J : HermitianForm 3 K) (f : ℕ)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nonempty (J.specialSubgroup ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) K) := by
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hcard
  have hconj := CFSG.BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J (2 ^ f) hcard
    hfixed
  exact ⟨(MulEquiv.subgroupCongr (specialSubgroup_eq_SU J f hconj hJ)).trans
    (CFSG.LieType.Universal.Unitary.equivStatedSU hcard 3)⟩

theorem specialSubgroup_existsUnique_section
    (J : HermitianForm 3 K) {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {E : Type*} [Group E] [Finite E]
    (ρ : E →* J.specialSubgroup) (hρ : Function.Surjective ρ)
    (hcen : ρ.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card ρ.ker)) :
    ∃! σ : J.specialSubgroup →* E, ∀ s, ρ (σ s) = s := by
  obtain ⟨e⟩ := nonempty_specialSubgroup_mulEquiv_statedSU J f hcard hfixed hJ
  have hker : (e.toMonoidHom.comp ρ).ker = ρ.ker :=
    MonoidHom.ker_comp_of_injective ρ e.toMonoidHom e.injective
  exact existsUnique_section_of_mulEquiv e (statedSU_existsUnique_section hf hcard _
    (e.surjective.comp hρ) (hker ▸ hcen) (hker ▸ hodd))

theorem perfect_odd_cover_unitary
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {L : Type u} [Group L] [Finite L] [Group.IsPerfect L]
    (η : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hη : Function.Surjective η)
    (hcen : η.ker ≤ Subgroup.center L) (hodd : Odd (Nat.card η.ker)) :
    (∀ A : J.specialSubgroup, A ∈ (unitaryProj J).ker ↔
      ∃ c : K, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c ∧
        c * J.conj c = 1 ∧ c ^ 3 = 1) ∧
    ∃ φ : J.specialSubgroup →* L, η.comp φ = unitaryProj J ∧
      (∀ ψ : J.specialSubgroup →* L, η.comp ψ = unitaryProj J → ψ = φ) ∧
      Function.Surjective φ ∧ φ.ker ≤ (unitaryProj J).ker ∧
      (unitaryProj J).ker.map φ = η.ker ∧
      (∃ e : J.specialSubgroup ⧸ φ.ker ≃* L, ∀ A, e (QuotientGroup.mk A) = φ A ∧
        η (e (QuotientGroup.mk A)) = unitaryProj J A) ∧
      IsCyclic η.ker ∧ Nat.card η.ker = φ.ker.relIndex (unitaryProj J).ker ∧
      Nat.card η.ker ∣ Nat.gcd 3 (2 ^ f + 1) ∧
      (Even f → η.ker = ⊥) ∧ (¬ 3 ∣ Nat.card η.ker → η.ker = ⊥) := by
  obtain ⟨hcyc, hdvd⟩ := ker_unitaryProj_isCyclic_card_dvd J f hcard hfixed hJ
  obtain ⟨φ, hφ, huniq, hsurj, hker, hmap, he, hCcyc, hCcard, hCdvd⟩ :=
    perfect_odd_cover_of_split
      (fun _ _ _ => specialSubgroup_existsUnique_section J hf hcard hfixed hJ)
      (unitaryProj_surjective J) hdvd hη hcen hodd
  exact ⟨mem_ker_unitaryProj_iff J hJ, φ, hφ, huniq, hsurj, hker, hmap, he, hCcyc, hCcard,
    hCdvd, eq_bot_of_card_dvd_gcd _ hCdvd⟩

end Hyperbolic

end CFSG.ShultStronglyClosedTI.PerfectOddCover
