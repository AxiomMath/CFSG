module

public import CFSG.Sporadic.Co2Smith.GlNJG4

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.RankThree.Co2 CFSG.Certificates

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section G

variable
  {G : Type} [Group G] {z : G} (φ : centralizer ({z} : Set G) ≃* Cz)

theorem conj_mem_Jc (x : normalizer (Jc : Set K)) {j : K} (hj : j ∈ Jc) :
    (x : K) * j * (x : K)⁻¹ ∈ Jc :=
  (mem_normalizer_iff.1 x.2 j).1 hj

theorem conj_phiH_of_piG_eq [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (g : normalizer (JGc φ : Set G)) (x : normalizer (Jc : Set K)) (h : piG φ hz g = piK x)
    {j : K} (hj : j ∈ Jc) :
    (g : G) * phiH φ ⟨j, Jc_le_Cz hj⟩ * (g : G)⁻¹ =
      phiH φ ⟨(x : K) * j * (x : K)⁻¹, Jc_le_Cz (conj_mem_Jc x hj)⟩ := by
  have hS : Subgroup.closure (Set.range omK) ≤ Jc := by
    rw [closure_le]
    rintro _ ⟨k, rfl⟩
    exact omK_mem_Jc k
  refine closure_induction (p := fun j _ => ∀ hJ : j ∈ Jc,
      (g : G) * phiH φ ⟨j, Jc_le_Cz hJ⟩ * (g : G)⁻¹ =
        phiH φ ⟨(x : K) * j * (x : K)⁻¹, Jc_le_Cz (conj_mem_Jc x hJ)⟩)
    ?_ ?_ ?_ ?_ (Jc_le_closure_omK hj) hj
  · rintro _ ⟨k, rfl⟩ hJ
    have e1 := piG_spec φ hz g k
    rw [h] at e1
    have e2 : omCz (piK x k) = ⟨(x : K) * omK k * (x : K)⁻¹, Jc_le_Cz (conj_mem_Jc x hJ)⟩ :=
      Subtype.ext (piK_spec x k)
    rw [omG, e2] at e1
    exact e1.symm
  · intro hJ
    have e1 : (⟨1, Jc_le_Cz hJ⟩ : Cz) = 1 := rfl
    have e2 : (⟨(x : K) * 1 * (x : K)⁻¹, Jc_le_Cz (conj_mem_Jc x hJ)⟩ : Cz) = 1 :=
      Subtype.ext (by simp)
    rw [e1, e2, map_one, mul_one, mul_inv_cancel]
  · intro a b ha hb iha ihb hJ
    have haJ := hS ha
    have hbJ := hS hb
    have e1 : (⟨a * b, Jc_le_Cz hJ⟩ : Cz) = ⟨a, Jc_le_Cz haJ⟩ * ⟨b, Jc_le_Cz hbJ⟩ := rfl
    have e2 : (⟨(x : K) * (a * b) * (x : K)⁻¹, Jc_le_Cz (conj_mem_Jc x hJ)⟩ : Cz) =
        ⟨(x : K) * a * (x : K)⁻¹, Jc_le_Cz (conj_mem_Jc x haJ)⟩ *
          ⟨(x : K) * b * (x : K)⁻¹, Jc_le_Cz (conj_mem_Jc x hbJ)⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    rw [e1, e2, map_mul, map_mul, ← iha haJ, ← ihb hbJ]
    group
  · intro a ha iha hJ
    have haJ := hS ha
    have e1 : (⟨a⁻¹, Jc_le_Cz hJ⟩ : Cz) = (⟨a, Jc_le_Cz haJ⟩ : Cz)⁻¹ := rfl
    have e2 : (⟨(x : K) * a⁻¹ * (x : K)⁻¹, Jc_le_Cz (conj_mem_Jc x hJ)⟩ : Cz) =
        (⟨(x : K) * a * (x : K)⁻¹, Jc_le_Cz (conj_mem_Jc x haJ)⟩ : Cz)⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_inv]; group)
    rw [e1, e2, map_inv, map_inv, ← iha haJ]
    group


theorem piG_inj_L [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2) (hφz : φ (zH z) = z0C)
    {L : Subgroup G} (hL : IsNJComp φ L) {g g' : normalizer (JGc φ : Set G)}
    (hg : (g : G) ∈ L) (hg' : (g' : G) ∈ L) (h : piG φ hz g = piG φ hz g') : g = g' := by
  have h1 : piG φ hz (g * g'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := hL.inf _ (L.mul_mem hg (L.inv_mem hg')) (mem_JGc_of_piG_eq_one φ hz hφz h1)
  exact mul_inv_eq_one.1 (Subtype.ext h2)

@[expose] noncomputable def mKof {Lk : Subgroup K}
    (hLk : ∀ σ ∈ njAut, ∃ x : normalizer (Jc : Set K), (x : K) ∈ Lk ∧ piK x = σ)
    (x : normalizer (Jc : Set K)) : normalizer (Jc : Set K) :=
  Classical.choose (hLk (piK x) (piK_mem_njAut x))

theorem mKof_spec {Lk : Subgroup K}
    (hLk : ∀ σ ∈ njAut, ∃ x : normalizer (Jc : Set K), (x : K) ∈ Lk ∧ piK x = σ)
    (x : normalizer (Jc : Set K)) : (mKof hLk x : K) ∈ Lk ∧ piK (mKof hLk x) = piK x :=
  Classical.choose_spec (hLk (piK x) (piK_mem_njAut x))

theorem jK_mem {Lk : Subgroup K}
    (hLk : ∀ σ ∈ njAut, ∃ x : normalizer (Jc : Set K), (x : K) ∈ Lk ∧ piK x = σ)
    (x : normalizer (Jc : Set K)) : (x : K) * (mKof hLk x : K)⁻¹ ∈ Jc := by
  have h : piK (x * (mKof hLk x)⁻¹) = 1 := by
    rw [map_mul, map_inv, (mKof_spec hLk x).2, mul_inv_cancel]
  exact mem_Jc_of_piK_eq_one h

@[expose] noncomputable def lGof [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (hφz : φ (zH z) = z0C) {L : Subgroup G} (hL : IsNJComp φ L) {s : ℕ}
    (hLs : ∀ y : Cz, phiH φ y ∈ L ↔ (y : K) ∈ QKs s) (σ : Equiv.Perm (Fin 77))
    (hσ : σ ∈ njAut) : normalizer (JGc φ : Set G) :=
  Classical.choose (piG_L_surj φ hz hφz hL hLs hσ)

theorem lGof_spec [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (hφz : φ (zH z) = z0C) {L : Subgroup G} (hL : IsNJComp φ L) {s : ℕ}
    (hLs : ∀ y : Cz, phiH φ y ∈ L ↔ (y : K) ∈ QKs s) (σ : Equiv.Perm (Fin 77))
    (hσ : σ ∈ njAut) :
    (lGof φ hz hφz hL hLs σ hσ : G) ∈ L ∧ piG φ hz (lGof φ hz hφz hL hLs σ hσ) = σ :=
  Classical.choose_spec (piG_L_surj φ hz hφz hL hLs hσ)

@[expose] noncomputable def chartFun [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (hφz : φ (zH z) = z0C) {L : Subgroup G} (hL : IsNJComp φ L) {s : ℕ}
    (hLs : ∀ y : Cz, phiH φ y ∈ L ↔ (y : K) ∈ QKs s) {Lk : Subgroup K}
    (hLk : ∀ σ ∈ njAut, ∃ x : normalizer (Jc : Set K), (x : K) ∈ Lk ∧ piK x = σ)
    (x : normalizer (Jc : Set K)) : G :=
  phiH φ ⟨(x : K) * (mKof hLk x : K)⁻¹, Jc_le_Cz (jK_mem hLk x)⟩ *
    lGof φ hz hφz hL hLs (piK x) (piK_mem_njAut x)

theorem chartFun_mul [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (hφz : φ (zH z) = z0C) {L : Subgroup G} (hL : IsNJComp φ L) {s : ℕ}
    (hLs : ∀ y : Cz, phiH φ y ∈ L ↔ (y : K) ∈ QKs s) {Lk : Subgroup K}
    (hLkJ : ∀ x ∈ Lk, x ∈ Jc → x = 1)
    (hLk : ∀ σ ∈ njAut, ∃ x : normalizer (Jc : Set K), (x : K) ∈ Lk ∧ piK x = σ)
    (x y : normalizer (Jc : Set K)) :
    chartFun φ hz hφz hL hLs hLk (x * y) =
      chartFun φ hz hφz hL hLs hLk x * chartFun φ hz hφz hL hLs hLk y := by
  have hmm : mKof hLk (x * y) = mKof hLk x * mKof hLk y := by
    refine piK_inj_of_inf hLkJ (mKof_spec hLk _).1 (Lk.mul_mem (mKof_spec hLk x).1
      (mKof_spec hLk y).1) ?_
    rw [(mKof_spec hLk _).2, map_mul, map_mul, (mKof_spec hLk x).2, (mKof_spec hLk y).2]
  have hgg : lGof φ hz hφz hL hLs (piK (x * y)) (piK_mem_njAut (x * y)) =
      lGof φ hz hφz hL hLs (piK x) (piK_mem_njAut x) *
        lGof φ hz hφz hL hLs (piK y) (piK_mem_njAut y) := by
    refine piG_inj_L φ hz hφz hL (lGof_spec φ hz hφz hL hLs _ _).1
      (L.mul_mem (lGof_spec φ hz hφz hL hLs _ _).1 (lGof_spec φ hz hφz hL hLs _ _).1) ?_
    rw [(lGof_spec φ hz hφz hL hLs _ _).2, map_mul, map_mul, (lGof_spec φ hz hφz hL hLs _ _).2,
      (lGof_spec φ hz hφz hL hLs _ _).2]
  have hgm : piG φ hz (lGof φ hz hφz hL hLs (piK x) (piK_mem_njAut x)) = piK (mKof hLk x) := by
    rw [(lGof_spec φ hz hφz hL hLs _ _).2, (mKof_spec hLk x).2]
  have hj' := jK_mem hLk y
  have key := conj_phiH_of_piG_eq φ hz _ _ hgm hj'
  unfold chartFun
  rw [hgg]
  have e : (⟨(↑(x * y) : K) * (↑(mKof hLk (x * y)) : K)⁻¹, Jc_le_Cz (jK_mem hLk (x * y))⟩ : Cz) =
      ⟨(x : K) * (mKof hLk x : K)⁻¹, Jc_le_Cz (jK_mem hLk x)⟩ *
        ⟨(mKof hLk x : K) * ((y : K) * (mKof hLk y : K)⁻¹) * (mKof hLk x : K)⁻¹,
          Jc_le_Cz (conj_mem_Jc (mKof hLk x) hj')⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hmm, mul_inv_rev]
    group
  rw [e, map_mul, ← key, Subgroup.coe_mul]
  group

@[expose] noncomputable def chartOf [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (hφz : φ (zH z) = z0C) {L : Subgroup G} (hL : IsNJComp φ L) {s : ℕ}
    (hLs : ∀ y : Cz, phiH φ y ∈ L ↔ (y : K) ∈ QKs s) {Lk : Subgroup K}
    (hLkJ : ∀ x ∈ Lk, x ∈ Jc → x = 1)
    (hLk : ∀ σ ∈ njAut, ∃ x : normalizer (Jc : Set K), (x : K) ∈ Lk ∧ piK x = σ) :
    normalizer (Jc : Set K) →* G :=
  MonoidHom.mk' (chartFun φ hz hφz hL hLs hLk) (chartFun_mul φ hz hφz hL hLs hLkJ hLk)

theorem isNJChart_chartOf [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (hφz : φ (zH z) = z0C) {L : Subgroup G} (hL : IsNJComp φ L) {s : ℕ}
    (hLs : ∀ y : Cz, phiH φ y ∈ L ↔ (y : K) ∈ QKs s) {Lk : Subgroup K}
    (hLkJ : ∀ x ∈ Lk, x ∈ Jc → x = 1)
    (hLk : ∀ σ ∈ njAut, ∃ x : normalizer (Jc : Set K), (x : K) ∈ Lk ∧ piK x = σ)
    (hLkC : ∀ x ∈ Lk, x ∈ Cz → x ∈ QKs s) :
    IsNJChart φ (chartOf φ hz hφz hL hLs hLkJ hLk) := by
  intro x hx
  set m := mKof hLk x
  have hmz : (m : K) ∈ Cz := by
    rw [← piK_zero_iff, (mKof_spec hLk x).2]
    exact (piK_zero_iff x).2 hx
  have hmQ := hLkC _ (mKof_spec hLk x).1 hmz
  have hmL : phiH φ ⟨m, hmz⟩ ∈ L := (hLs ⟨m, hmz⟩).2 hmQ
  have hgN : phiH φ ⟨m, hmz⟩ ∈ normalizer (JGc φ : Set G) := phiH_mem_NG φ m.2
  have hg : lGof φ hz hφz hL hLs (piK x) (piK_mem_njAut x) = ⟨phiH φ ⟨m, hmz⟩, hgN⟩ := by
    refine piG_inj_L φ hz hφz hL (lGof_spec φ hz hφz hL hLs _ _).1 hmL ?_
    rw [(lGof_spec φ hz hφz hL hLs _ _).2, piG_phiH φ hz ⟨m, hmz⟩ m.2, ← (mKof_spec hLk x).2]
  show chartFun φ hz hφz hL hLs hLk x = _
  unfold chartFun
  rw [hg]
  show phiH φ _ * phiH φ _ = phiH φ ⟨x, hx⟩
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  show (x : K) * (m : K)⁻¹ * m = x
  group

end G

end CFSG.Sporadic.Co2Smith
