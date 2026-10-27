module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisPerfect

public section

namespace CFSG.RankThree.PartOne

namespace KCRootAxis

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b

inductive Axis
  | one
  | two

variable {K : Type} [Field K] [CharP K 2]

theorem minorAut_uElt_zero_zero [Finite K] (c : K) :
    minorAut K (uElt 0 0 c 0) = uElt 0 c 0 0 := by
  apply antiSp_ext
  rw [glMat_minorAut, glMat_uElt, minorMap_uMat, glMat_uElt]
  simp

theorem minorAut_uElt_radA2 [Finite K] (a b c : K) :
    minorAut K (uElt a b c 0) = uElt 0 (c + a * b) (b ^ 2) (a ^ 2) := by
  apply antiSp_ext
  rw [glMat_minorAut, glMat_uElt, minorMap_uMat, glMat_uElt]
  simp

theorem exists_sq_eq [Finite K] (x : K) : ∃ y : K, y ^ 2 = x := by
  have hinj : Function.Injective (frobenius K 2) := frobenius_inj K 2
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp hinj x
  exact ⟨y, by simpa [frobenius_def] using hy⟩

theorem rootU₁_eq_map [Finite K] :
    rootU₁ K = (rootU₂ K).map (minorAut K).toMonoidHom := by
  ext z
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨uElt 0 0 b 0, ⟨b, rfl⟩, minorAut_uElt_zero_zero b⟩
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, minorAut_uElt_zero_zero c⟩

theorem radA1_eq_map [Finite K] :
    radA1 K = (radA2 K).map (minorAut K).toMonoidHom := by
  ext z
  constructor
  · rintro ⟨B, C, D, rfl⟩
    obtain ⟨a, ha⟩ := exists_sq_eq D
    obtain ⟨b, hb⟩ := exists_sq_eq C
    refine ⟨uElt a b (B + a * b) 0, ⟨a, b, B + a * b, rfl⟩, ?_⟩
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    show minorAut K (uElt a b (B + a * b) 0) = _
    rw [minorAut_uElt_radA2, ha, hb]
    congr 1
    linear_combination (a * b) * h2
  · rintro ⟨y, ⟨a, b, c, rfl⟩, rfl⟩
    exact ⟨c + a * b, b ^ 2, a ^ 2, minorAut_uElt_radA2 a b c⟩

variable (K) in
@[expose] def rootU : Axis → Subgroup (antiSp K)
  | .one => rootU₁ K
  | .two => rootU₂ K

variable (K) in
@[expose] def rootA : Axis → Subgroup (antiSp K)
  | .one => radA1 K
  | .two => radA2 K

variable (K) in
@[expose] noncomputable def sHom [Finite K] : Axis → SL₂ K →* antiSp K
  | .one => (minorAut K).toMonoidHom.comp (sHom₂ K)
  | .two => sHom₂ K

variable (K) in
@[expose] noncomputable def dHom [Finite K] : Axis → Kˣ →* antiSp K
  | .one => (minorAut K).toMonoidHom.comp (dHom₂ K)
  | .two => dHom₂ K

variable (K) in
@[expose] def rootCoord : Axis → K → antiSp K
  | .one => fun b => uElt 0 b 0 0
  | .two => fun c => uElt 0 0 c 0

variable (K) in
@[expose] noncomputable def vecOf [Finite K] : Axis → antiSp K → Fin 2 → K
  | .one => fun z => vecOf₂ ((minorAut K).symm z)
  | .two => vecOf₂

variable (K) in
@[expose] def rootC (i : Axis) : Subgroup (antiSp K) :=
  Subgroup.centralizer ((rootU K i : Subgroup (antiSp K)) : Set (antiSp K))

variable (K) in
@[expose] def rootN (i : Axis) : Subgroup (antiSp K) :=
  Subgroup.normalizer ((rootU K i : Subgroup (antiSp K)) : Set (antiSp K))

theorem rootAxisStructure_two [Finite K] (hK : 4 ≤ Nat.card K) :
    RootAxisStructure (rootU₂ K) (radA2 K) (sHom₂ K) (dHom₂ K) (fun c => uElt 0 0 c 0) vecOf₂ := by
  have hK2 : 2 < Nat.card K := by omega
  have hnormN : ∀ g, g ∈ Subgroup.normalizer (rootU₂ K : Set (antiSp K)) ↔ FirstCol g :=
    fun g => mem_normalizer_rootU₂_iff
  refine
    { A_le_C := radA2_le_centralizer_rootU₂
      s_mem_C := fun M => sElt_mem_rootC₂ M
      A_normal_C := fun g hg a ha => conj_mem_radA2 (centralizer_rootU₂_le_lineStab hg) ha
      C_decomp := fun g hg => ?_
      C_unique := fun a ha a' ha' M M' h => ?_
      C_perfect := isPerfect_rootC₂ hK
      C_pCore := ?_
      N_eq := ?_
      A_le_N := fun x hx => ?_
      ds_mem_N := fun l M => ?_
      A_normal_N := fun g hg a ha => conj_mem_radA2 ((hnormN g).mp hg) ha
      s_comm_d := fun M l => sElt_mul_dElt M l
      N_decomp := fun g hg => ?_
      N_unique := fun a ha a' ha' l l' M M' h => ?_
      quot_bijective := ⟨fun M => sElt_mem_rootC₂ M, quotS₂_bijective⟩
      S_center := sl2_center_eq_bot
      S_perfect := sl2_isPerfect hK
      S_pCore := sl2_pCore_eq_bot hK
      coord_mem := fun c => ⟨c, rfl⟩
      coord_surj := fun z hz => ?_
      vec_add := fun z hz w hw => vecOf₂_mul hz hw
      vec_surj := exists_vecOf₂_eq
      vec_ker := fun z hz => vecOf₂_eq_zero_iff hz
      vec_conj := fun M z hz => vecOf₂_conj M hz
      normal_eq_A := fun V hVC hVn hVA hVU => ?_
      d_coord := fun l x => ?_ }
  · obtain ⟨v, c, M, hgM⟩ := exists_aElt_mul_sElt hg
    exact ⟨aElt v c, aElt_mem_radA2 v c, M, hgM⟩
  · obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp ha
    obtain ⟨v', c', rfl⟩ := mem_radA2_iff.mp ha'
    have h' : aElt v c * (dElt 1 * sElt M) = aElt v' c' * (dElt 1 * sElt M') := by
      rw [dElt_one, one_mul, one_mul]
      exact h
    obtain ⟨hv, hc, -, hM⟩ := normalForm_unique h'
    exact ⟨by rw [hv, hc], hM⟩
  · exact pCore_rootC₂ hK
  · exact normalizer_rootU₂_eq.trans normalizer_radA2_eq.symm
  · exact (hnormN x).mpr (radA2_le_lineStab hx)
  · refine (hnormN _).mpr ?_
    have := firstCol_normalForm 0 0 l M
    rwa [aElt_zero_zero, one_mul] at this
  · obtain ⟨v, c, l, M, hgM⟩ := exists_normalForm ((hnormN g).mp hg)
    exact ⟨aElt v c, aElt_mem_radA2 v c, l, M, hgM⟩
  · obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp ha
    obtain ⟨v', c', rfl⟩ := mem_radA2_iff.mp ha'
    obtain ⟨hv, hc, hl, hM⟩ := normalForm_unique h
    exact ⟨by rw [hv, hc], hl, hM⟩
  · obtain ⟨c, rfl⟩ := hz
    exact ⟨c, rfl⟩
  · refine eq_radA2_of_normal hK2 hVC ?_ hVA hVU
    exact ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hVn g g.2 n hn⟩
  · have h := dElt_mul_aElt l 0 x
    rw [smul_zero, aElt_zero, aElt_zero] at h
    show dElt l * uElt 0 0 x 0 * (dElt l)⁻¹ = uElt 0 0 ((l : K) ^ 2 * x) 0
    rw [mul_inv_eq_iff_eq_mul]
    exact h

theorem rootAxisStructure_one [Finite K] (hK : 4 ≤ Nat.card K) :
    RootAxisStructure (rootU₁ K) (radA1 K) ((minorAut K).toMonoidHom.comp (sHom₂ K))
      ((minorAut K).toMonoidHom.comp (dHom₂ K)) (fun b => uElt 0 b 0 0)
      (fun z => vecOf₂ ((minorAut K).symm z)) :=
  (rootAxisStructure_two hK).map' (minorAut K) rootU₁_eq_map radA1_eq_map (fun _ => rfl)
    (fun _ => rfl) (fun c => (minorAut_uElt_zero_zero c).symm) (fun _ => rfl)

theorem even_symplectic_four_root_axis_centralizer_structure [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) :
    RootAxisStructure (rootU K i) (rootA K i) (sHom K i) (dHom K i) (rootCoord K i)
      (vecOf K i) := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  cases i
  · exact rootAxisStructure_one h4
  · exact rootAxisStructure_two h4

end KCRootAxis

end CFSG.RankThree.PartOne
