module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.K6b

open CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem comm_comm_eq_of_coprime (A K : Subgroup G) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card K)) (hsolv : Group.IsSolvable K) :
    ⁅⁅K, A⁆, A⁆ = ⁅K, A⁆ := by
  classical
  let : Subgroup.Normalizes A K := ⟨hAK⟩
  let : MulDistribMulAction (↥A) (↥K) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A K hAK
  let C : Subgroup (↥K) := CFSG.commutatorAction (A := ↥A) (G := ↥K)
  have hCmap : C.map K.subtype = ⁅K, A⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator K A hAK
  have hC2eq : CFSG.commutatorAction₂ (A := ↥A) (G := ↥K) = C :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_solvable_coprime
      (G := ↥K) (A := ↥A) hsolv hcop
  have hXle : ⁅⁅K, A⁆, A⁆ ≤ ⁅K, A⁆ :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp
      (Subgroup.normalizer_commutator_ge_right K A)
  have hcomm₂_le :
      (CFSG.commutatorAction₂ (A := ↥A) (G := ↥K)).map K.subtype ≤ ⁅⁅K, A⁆, A⁆ := by
    let S : Set (↥K) := {x : ↥K | ∃ a : ↥A, ∃ k : ↥K, k ∈ C ∧ x = k⁻¹ * (a • k)}
    calc
      (CFSG.commutatorAction₂ (A := ↥A) (G := ↥K)).map K.subtype =
          (Subgroup.closure S).map K.subtype := by
            rfl
      _ = Subgroup.closure (K.subtype '' S) := by
            simpa using (MonoidHom.map_closure (f := K.subtype) S)
      _ ≤ ⁅⁅K, A⁆, A⁆ := by
            refine (Subgroup.closure_le (K := ⁅⁅K, A⁆, A⁆)).2 ?_
            rintro _ ⟨y, hy, rfl⟩
            rcases hy with ⟨a, k, hkC, rfl⟩
            have hkX : (k : G) ∈ ⁅K, A⁆ := by
              rw [← hCmap]
              exact Subgroup.mem_map.mpr ⟨k, hkC, rfl⟩
            have hgen : ⁅((k : ↥K) : G)⁻¹, (a : G)⁆ ∈ ⁅⁅K, A⁆, A⁆ :=
              Subgroup.commutator_mem_commutator (H₁ := ⁅K, A⁆) (H₂ := A)
                (Subgroup.inv_mem (H := ⁅K, A⁆) hkX) a.2
            simpa [commutatorElement_def,
              Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc] using hgen
  apply le_antisymm hXle
  intro x hx
  have hx₂ : x ∈ (CFSG.commutatorAction₂ (A := ↥A) (G := ↥K)).map K.subtype := by
    rw [hC2eq, hCmap]
    exact hx
  exact hcomm₂_le hx₂

theorem comm_mem_of_odd {P A : Subgroup G} (hP : IsPGroup 2 P)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) {g : G} (hg : g ∈ A) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) {p : G} (hp : p ∈ P) : ⁅p, g⁆ ∈ ⁅⁅P, A⁆, A⁆ := by
  have hz : Subgroup.zpowers g ≤ A := (Subgroup.zpowers_le).mpr hg
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers g)) (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hdvd : Nat.card (Subgroup.zpowers g) ∣ m := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hgm
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (hm.of_dvd_nat hdvd))
  have hsolv : Group.IsSolvable P := by
    have : Group.IsNilpotent P := hP.isNilpotent
    infer_instance
  have h1 := comm_comm_eq_of_coprime (Subgroup.zpowers g) P (hz.trans hAP) hcop hsolv
  have h2 : ⁅p, g⁆ ∈ ⁅P, Subgroup.zpowers g⁆ :=
    Subgroup.commutator_mem_commutator hp (Subgroup.mem_zpowers g)
  rw [← h1] at h2
  exact Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hz) hz h2

theorem comm_comm_oTwoRes {X P : Subgroup G} (hP : IsPGroup 2 P)
    (hLP : oTwoRes X ≤ Subgroup.normalizer (P : Set G)) :
    ⁅⁅P, oTwoRes X⁆, oTwoRes X⁆ = ⁅P, oTwoRes X⁆ := by
  set L := oTwoRes X with hL
  have hNL : L ≤ Subgroup.normalizer ((⁅⁅P, L⁆, L⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right ⁅P, L⁆ L
  refine le_antisymm ((Subgroup.le_normalizer_iff_commutator_le_left).mp
    (Subgroup.normalizer_commutator_ge_right P L)) ?_
  rw [Subgroup.commutator_le]
  intro p hp l hl
  have hcl : l ∈ Subgroup.closure {x | x ∈ X ∧ ∃ m : ℕ, Odd m ∧ x ^ m = 1} := hl
  clear hl
  induction hcl using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨hgX, m, hm, hgm⟩ := hg
    exact comm_mem_of_odd hP hLP (Subgroup.subset_closure ⟨hgX, m, hm, hgm⟩) hm hgm hp
  | one => simp
  | mul a b ha hb iha ihb =>
    have e : ⁅p, a * b⁆ = ⁅p, a⁆ * (a * ⁅p, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine Subgroup.mul_mem _ iha ?_
    exact (Subgroup.mem_normalizer_iff.mp (hNL ha) _).mp ihb
  | inv a ha iha =>
    have e : ⁅p, a⁻¹⁆ = a⁻¹ * ⁅p, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hNL ((Subgroup.inv_mem _ ha))) _).mp
      (Subgroup.inv_mem _ iha)

end CFSG.Quasithin.F53.Stellmacher.S35.K6b
