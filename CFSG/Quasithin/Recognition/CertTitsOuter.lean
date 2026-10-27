module

public import CFSG.Quasithin.Recognition.CertPermOuter
public import CFSG.Quasithin.Recognition.CertTitsSimpleMain
public import CFSG.Quasithin.Recognition.CertDataTitsOuter
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Quasithin.Recognition.CertTitsSimpleMain
public meta import CFSG.Quasithin.Recognition.CertDataTitsOuter
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertTitsOuterInputs
public import Certificates.Certificate8075
public import Certificates.Certificate8071
public import Certificates.Certificate8077
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate19953

public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem titsOuter_check :
    isInvA 1755 titsPiArr (invCand 1755 titsPiArr) = true ∧
    titsSift titsA = true ∧ titsSift titsB = true ∧
    titsSift (compA 1755 (compA 1755 titsPiArr (titsArray CFSG.Open.quasithinTitsData1))
      (invCand 1755 titsPiArr)) = true ∧
    titsSift (compA 1755 (compA 1755 titsPiArr (titsArray CFSG.Open.quasithinTitsData2))
      (invCand 1755 titsPiArr)) = true ∧
    titsSift titsPiArr = false ∧ titsLabelsNontrivial = true :=
  Certificates.certificate8075

private theorem titsGens_size'' : titsGens.size = 2 := by simp [titsGens]

private theorem titsGens_zero'' : titsGens[0]! = titsArray CFSG.Open.quasithinTitsData1 := by
  simp [titsGens]

private theorem titsGens_one'' : titsGens[1]! = titsArray CFSG.Open.quasithinTitsData2 := by
  simp [titsGens]

private theorem titsPairO_size' : titsPairO.size = 2 := by simp [titsPairO]

private theorem titsPairO_zero' : titsPairO[0]! = titsA := by simp [titsPairO]

private theorem titsPairO_one' : titsPairO[1]! = titsB := by simp [titsPairO]

private theorem titsBase_nodup' : titsBase.Nodup := by decide

@[expose] noncomputable def titsσ : Equiv.Perm (Fin 1755) :=
  permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData1)

@[expose] noncomputable def titsτ : Equiv.Perm (Fin 1755) :=
  permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData2)

@[expose] def titsModelJ : Subgroup (Equiv.Perm (Fin 1755)) :=
  Subgroup.closure {g | ∃ k < titsGens.size, permOfArr 1755 titsGens[k]! = g}

theorem titsModelJ_eq : titsModelJ = Subgroup.closure ({titsσ, titsτ} : Set (Equiv.Perm (Fin 1755))) := by
  unfold titsModelJ
  congr 1
  ext g
  rw [Set.mem_ofPred_eq, titsGens_size'', Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl (by rw [titsGens_zero'']; rfl)
    · exact Or.inr (by rw [titsGens_one'']; rfl)
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by rw [titsGens_zero'']; rfl⟩
    · exact ⟨1, by norm_num, by rw [titsGens_one'']; rfl⟩

theorem titsSift_iff
    {g : Array ℕ} {G : Equiv.Perm (Fin 1755)} (hG : Rep 1755 g G) :
    titsSift g = true ↔ G ∈ titsModelJ := by
  obtain ⟨-, -, hOS, hSO, hchain, -⟩ := titsChain_check
  exact mem_closure_iff_siftA (n := 1755) (by norm_num) (O := titsGens) (S := titsStrong)
    (W := titsRawWords) titsBase_nodup' (chunks := 4) (by norm_num) hOS hSO hchain hG

theorem exists_outer_titsJ :
    ∃ φ : MulAut ↥titsModelJ, φ ∉ (MulAut.conj : ↥titsModelJ →* MulAut ↥titsModelJ).range := by
  obtain ⟨hπ, hsa, hsb, hsσ, hsτ, hsπ, hnt⟩ := titsOuter_check
  obtain ⟨hp1, hp2, -⟩ := titsChain_check
  obtain ⟨hA, hB, -, -, hOS, hSO, hchain, -, hprim, -⟩ := titsPair_check
  have hrπ := rep_permOfArr hπ
  have hrσ := (rep_permOfArr hp1).1
  have hrτ := (rep_permOfArr hp2).1
  have hconj : ∀ t ∈ ({titsσ, titsτ} : Set (Equiv.Perm (Fin 1755))),
      permOfArr 1755 titsPiArr * t * (permOfArr 1755 titsPiArr)⁻¹ ∈ titsModelJ := by
    intro t ht
    rcases ht with rfl | ht
    · exact (titsSift_iff (rep_compA (rep_compA hrπ.1 hrσ) hrπ.2)).1 hsσ
    · rw [Set.mem_singleton_iff.1 ht]
      exact (titsSift_iff (rep_compA (rep_compA hrπ.1 hrτ) hrπ.2)).1 hsτ
  have hcj := conj_mem_closure_of_gen (permOfArr 1755 titsPiArr)
    (T := ({titsσ, titsτ} : Set (Equiv.Perm (Fin 1755))))
    (fun t ht => by rw [← titsModelJ_eq]; exact hconj t ht)
  have hπJ : permOfArr 1755 titsPiArr ∉ titsModelJ := fun hmem => by
    have := (titsSift_iff hrπ.1).2 hmem
    rw [hsπ] at this
    exact Bool.false_ne_true this
  have hAJ : permOfArr 1755 titsA ∈ titsModelJ := (titsSift_iff (rep_permOfArr hA).1).1 hsa
  have hBJ : permOfArr 1755 titsB ∈ titsModelJ := (titsSift_iff (rep_permOfArr hB).1).1 hsb
  have hle : Subgroup.closure {g | ∃ k < titsPairO.size, permOfArr 1755 titsPairO[k]! = g} ≤
      titsModelJ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨k, hk, rfl⟩
    rw [titsPairO_size'] at hk
    interval_cases k
    · rw [titsPairO_zero']; exact hAJ
    · rw [titsPairO_one']; exact hBJ
  have hSJ : ∀ j < titsPairStrong.size, permOfArr 1755 titsPairStrong[j]! ∈ titsModelJ := fun j hj =>
    hle (strong_mem_closure hOS hSO hchain j hj)
  have hSinv : ∀ j < titsPairStrong.size,
      isInvA 1755 titsPairStrong[j]! (rawInvs 1755 titsPairStrong)[j]! = true := fun j hj =>
    (chainCheckFacts hchain).strong_inv j hj
  have hnt' : ∀ p < 1755, p ≠ 0 → ∃ q < 1755, q ≠ p ∧ titsLabels[q]! = titsLabels[p]! := by
    intro p hp hp0
    have h := hnt
    simp only [titsLabelsNontrivial, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      beq_iff_eq, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rcases h p hp with h0 | ⟨q, hq, hne, hlab⟩
    · exact absurd h0 hp0
    · exact ⟨q, hq, hne, hlab⟩
  exact exists_outer_of_conj (permOfArr 1755 titsPiArr) hπJ (fun x hx => by
      rw [titsModelJ_eq]
      exact hcj x (by rw [← titsModelJ_eq]; exact hx)) fun c hc =>
    centralizer_eq_one_of_primCheck hSinv hSJ hprim hnt' c hc

theorem not_isSimpleGroup_mulAut_quasithinTits :
    ¬ IsSimpleGroup (MulAut CFSG.Open.quasithinTits) := by
  obtain ⟨φ, hφ⟩ := exists_outer_titsJ
  obtain ⟨hp1, hp2, -⟩ := titsChain_check
  have e : CFSG.Open.quasithinTits ≃* ↥titsModelJ :=
    (unitsClosurePairEquiv _ _ _ _ (coe_permOfArr_titsArray CFSG.Open.quasithinTitsData1 hp1)
      (coe_permOfArr_titsArray CFSG.Open.quasithinTitsData2 hp2)).trans
      (MulEquiv.subgroupCongr titsModelJ_eq.symm)
  have hsimple : IsSimpleGroup ↥titsModelJ := (MulEquiv.isSimpleGroup_congr e).1 isSimpleGroup_quasithinTits
  have hnonab : ∃ x y : ↥titsModelJ, x * y ≠ y * x := by
    by_contra hcomm
    have hcomm' : ∀ x y : ↥titsModelJ, x * y = y * x := fun x y =>
      by_contra fun h => hcomm ⟨x, y, h⟩
    have : IsMulCommutative ↥titsModelJ := ⟨⟨hcomm'⟩⟩
    have hp := IsSimpleGroup.prime_card (α := ↥titsModelJ)
    rw [titsModelJ_eq, titsσ, titsτ, card_closure_tits_perm] at hp
    exact absurd hp (by norm_num)
  intro h
  exact not_isSimpleGroup_mulAut_of_outer hnonab φ hφ ((MulEquiv.isSimpleGroup_congr (MulAut.congr e)).1 h)

theorem mulAut_models_not_simple :
    ¬ IsSimpleGroup (MulAut CFSG.Open.quasithinTits) ∧
      ¬ IsSimpleGroup (MulAut (CFSG.Open.PSU3 3 1)) :=
  ⟨not_isSimpleGroup_mulAut_quasithinTits, not_isSimpleGroup_mulAut_psu3⟩

end CFSG.Quasithin
