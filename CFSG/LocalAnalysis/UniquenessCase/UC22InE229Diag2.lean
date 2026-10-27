module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Swap
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag1
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_ne_two {s r : ℕ} (hs : Odd s) (hrs : r ∣ 2 ^ s - 1) : r ≠ 2 := by
  rintro rfl
  have hodd : Odd (2 ^ s - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, hs.pos.ne'⟩) odd_one
  exact Nat.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 hrs)

theorem uc22ine229_orderOf_mk {X : Subgroup G} (x : ↥X) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hx : orderOf x = r) : orderOf (QuotientGroup.mk x : Bar2 X) = r := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : orderOf (QuotientGroup.mk x : Bar2 X) ∣ r := by
    rw [← hx]
    exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) x
  rcases (Nat.dvd_prime hr).1 hdvd with h1 | h1
  · rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥X) ⟨x, h1⟩
    have h3 := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk : x ^ 2 ^ k = 1)
    rw [hx] at h3
    exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h3)) hr2
  · exact h1

theorem uc22ine229_exists_pow_orderOf_eq {X : Subgroup G} (x : ↥X) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hx : orderOf (QuotientGroup.mk x : Bar2 X) = r) :
    ∃ c : ℕ, orderOf (x ^ 2 ^ c) = r := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxr : x ^ r ∈ CFSG.pCore 2 ↥X := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    rw [QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥X) ⟨_, hxr⟩
  have hc' : (x ^ r) ^ 2 ^ c = 1 := congrArg Subtype.val hc
  have hcop : (orderOf (QuotientGroup.mk x : Bar2 X)).Coprime (2 ^ c) := by
    rw [hx]
    exact ((Nat.coprime_primes hr Nat.prime_two).2 hr2).pow_right c
  have hmk : orderOf (QuotientGroup.mk (x ^ 2 ^ c) : Bar2 X) = r := by
    rw [QuotientGroup.mk_pow, hcop.orderOf_pow, hx]
  refine ⟨c, Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) ?_⟩
  · rw [← pow_mul, mul_comm (2 ^ c), pow_mul, hc']
  · rw [← hmk]
    exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) _

theorem uc22ine229_mk_mem_center {M L L' : Subgroup G} (hL : L ∈ calC M) (hL' : L' ∈ calC M)
    (hne : L ≠ L') (l : ↥L)
    (hl : (QuotientGroup.mk (Subgroup.inclusion (CFSG.Quasithin.A3.subnormal_le hL.1) l) :
      Bar2 M) ∈ barImage M L') : (QuotientGroup.mk l : Bar2 L) ∈ center (Bar2 L) := by
  obtain ⟨e, he⟩ := uc22p22l_barImage_equiv hL
  refine Subgroup.mem_center_iff.2 fun y => e.injective (Subtype.ext ?_)
  rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, he]
  exact uc22p22l_barImage_commute hL hL' hne _ (e y).2 _ hl

theorem uc22ine229_exists_mem_conjClosure_normalizer {M T L : Subgroup G}
    (hT : IsSylowOf 2 T M) (hL : L ∈ calC M) (hc : (conjSetOf M L).ncard ≤ 2) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hZ : ¬ r ∣ Nat.card (center (Bar2 L)))
    (hone : ∀ T₀ : Subgroup G, IsPGroup 2 T₀ → T₀ ≤ normalizer (L : Set G) →
      IsSylowOf 2 (T₀ ⊓ L) L → ∃ x ∈ L, orderOf x = r ∧ x ∈ normalizer (T₀ : Set G)) :
    ∃ x ∈ conjClosure M L, orderOf x = r ∧ x ∈ normalizer (T : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hTL : IsSylowOf 2 (T ⊓ L) L := uc22p2214_isSylowOf_inf hT hL.1
  have hle : ∀ A ∈ conjSetOf M L, A ≤ conjClosure M L := fun A hA =>
    le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M L) => A) A hA le_rfl
  have hLS : L ∈ conjSetOf M L := ⟨1, M.one_mem, by ext x; simp⟩
  by_cases hTN : T ≤ normalizer (L : Set G)
  · obtain ⟨x, hxL, hxo, hxN⟩ := hone T hT.isPGroup hTN hTL
    exact ⟨x, hle L hLS hxL, hxo, hxN⟩
  obtain ⟨t, htT, htN⟩ := SetLike.not_le_iff_exists.1 hTN
  have htM : t ∈ M := hT.le htT
  have hmem : ∀ x z : G, z ∈ L.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * z * x ∈ L := fun x z => by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  obtain ⟨L', hL'⟩ : ∃ L', L' = L.map (MulAut.conj t).toMonoidHom := ⟨_, rfl⟩
  have hL'S : L' ∈ conjSetOf M L := ⟨t, htM, hL'⟩
  have hne : L ≠ L' := fun h => htN (mem_normalizer_iff.2 fun z => by
    have h1 := hmem t (t * z * t⁻¹)
    rw [← hL', ← h, show t⁻¹ * (t * z * t⁻¹) * t = z by group] at h1
    exact h1.symm)
  have hL'C : L' ∈ calC M := by
    have h := uc22p22u_calC_conj (le_normalizer : M ≤ normalizer (M : Set G)) hL (M.inv_mem htM)
    rwa [show uniqueFourConj t⁻¹ L = L' by rw [hL']; simp [uniqueFourConj]] at h
  have hdich : ∀ A ∈ conjSetOf M L, A = L ∨ A = L' := by
    intro A hA
    by_contra hcon
    push Not at hcon
    have h3 : ({L, L', A} : Set (Subgroup G)).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨L, L', A, hne, hcon.1.symm, hcon.2.symm, rfl⟩
    have h4 := Set.ncard_le_ncard (Set.insert_subset_iff.2 ⟨hLS, Set.insert_subset_iff.2
      ⟨hL'S, Set.singleton_subset_iff.2 hA⟩⟩) (Set.toFinite (conjSetOf M L))
    omega
  have hgen : ∀ x ∈ T, x ∈ T ⊓ normalizer (L : Set G) ∨
      t⁻¹ * x ∈ T ⊓ normalizer (L : Set G) := by
    intro x hx
    have h1 := fun z => hmem x (x * z * x⁻¹)
    simp only [show ∀ z, x⁻¹ * (x * z * x⁻¹) * x = z by intro z; group] at h1
    rcases hdich _ ⟨x, hT.le hx, rfl⟩ with h2 | h2
    · exact Or.inl (mem_inf.2 ⟨hx, mem_normalizer_iff.2 fun z => by rw [← h1 z, h2]⟩)
    · refine Or.inr (mem_inf.2 ⟨mul_mem (inv_mem htT) hx, mem_normalizer_iff.2 fun z => ?_⟩)
      rw [← h1 z, h2, hL', hmem, show t⁻¹ * x * z * (t⁻¹ * x)⁻¹ = t⁻¹ * (x * z * x⁻¹) * t by group]
  have hT₀ : IsSylowOf 2 ((T ⊓ normalizer (L : Set G)) ⊓ L) L := by
    rwa [inf_assoc, inf_eq_right.2 (le_normalizer : L ≤ normalizer (L : Set G))]
  obtain ⟨h, hhL, hho, hhN⟩ := hone _ (hT.isPGroup.to_le inf_le_left) inf_le_right hT₀
  have hhM : h ∈ M := hLM hhL
  have huL : t * h * t⁻¹ ∈ L' := by
    rw [hL', hmem, show t⁻¹ * (t * h * t⁻¹) * t = h by group]
    exact hhL
  have huM : t * h * t⁻¹ ∈ M := mul_mem (mul_mem htM hhM) (inv_mem htM)
  have ha : uc22p21cPi M ⟨h, hhM⟩ ∈ barImage M L := uc22p21c_mem_barImage.2 ⟨_, hhL, rfl⟩
  have hb : uc22p21cPi M ⟨t * h * t⁻¹, huM⟩ ∈ barImage M L' :=
    uc22p21c_mem_barImage.2 ⟨_, huL, rfl⟩
  have hab := uc22p22l_barImage_commute hL hL'C hne _ ha _ hb
  have hcT : h * (t * h * t⁻¹) * h⁻¹ * (t * h * t⁻¹)⁻¹ ∈ T := by
    have h1 := uc22p22u_commutator_mem_pCoreOf hhM huM hab
    rw [commutatorElement_def] at h1
    obtain ⟨Q, hQ⟩ := hT
    rw [← hQ]
    exact map_mono (CFSG.fitting_pCore_le_sylow Q) h1
  have hdN := uc22ine229_mul_conj_mem_normalizer inf_le_left htT hgen hhN hcT
  have har : uc22p21cPi M ⟨h, hhM⟩ ^ r = 1 := by
    rw [← uc22ine229_orderOf_mk ⟨h, hhM⟩ hr hr2 ((Subgroup.orderOf_coe _).symm.trans hho)]
    exact pow_orderOf_eq_one _
  have hbr : uc22p21cPi M ⟨t * h * t⁻¹, huM⟩ ^ r = 1 := by
    have h1 : (⟨t * h * t⁻¹, huM⟩ : ↥M) ^ r = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      change (t * h * t⁻¹) ^ r = 1
      rw [conj_pow, ← hho, pow_orderOf_eq_one, mul_one, mul_inv_cancel])
    rw [← map_pow, h1, map_one]
  have hab1 : uc22p21cPi M ⟨h, hhM⟩ * uc22p21cPi M ⟨t * h * t⁻¹, huM⟩ ≠ 1 := by
    intro h1
    have h2 : uc22p21cPi M ⟨h, hhM⟩ ∈ barImage M L' := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem hb
    have h4 := Subgroup.orderOf_dvd_natCard _ (uc22ine229_mk_mem_center hL hL'C hne ⟨h, hhL⟩ h2)
    rw [uc22ine229_orderOf_mk ⟨h, hhL⟩ hr hr2 ((Subgroup.orderOf_coe _).symm.trans hho)] at h4
    exact hZ h4
  have hdo : orderOf (QuotientGroup.mk (⟨h, hhM⟩ * ⟨t * h * t⁻¹, huM⟩ : ↥M) : Bar2 M) = r := by
    change orderOf (uc22p21cPi M (⟨h, hhM⟩ * ⟨t * h * t⁻¹, huM⟩)) = r
    rw [map_mul]
    exact orderOf_eq_prime (by rw [Commute.mul_pow hab, har, hbr, one_mul]) hab1
  obtain ⟨c, hc⟩ := uc22ine229_exists_pow_orderOf_eq _ hr hr2 hdo
  refine ⟨((⟨h, hhM⟩ * ⟨t * h * t⁻¹, huM⟩ : ↥M) ^ 2 ^ c : ↥M), ?_,
    by rw [Subgroup.orderOf_coe, hc], ?_⟩
  · rw [Subgroup.coe_pow]
    exact pow_mem (mul_mem (hle L hLS hhL) (hle L' hL'S huL)) _
  · rw [Subgroup.coe_pow]
    exact pow_mem hdN _

theorem uc22ine229_exists_mem_conjClosure_normalizer_of_isL2 {M T L : Subgroup G}
    (hT : IsSylowOf 2 T M) (hL : L ∈ calC M) (hc : (conjSetOf M L).ncard ≤ 2) {n s r : ℕ}
    (hX : IsL2 (Bar2 L) n) (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    ∃ x ∈ conjClosure M L, orderOf x = r ∧ x ∈ normalizer (T : Set G) := by
  haveI := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hX
  refine uc22ine229_exists_mem_conjClosure_normalizer hT hL hc hr (uc22ine229_ne_two hs hrs) ?_
    fun T₀ hT₀ hT₀L hS => uc22ine229_exists_mem_normalizer_of_isL2 hT₀ hT₀L hS hX hs hsn hr hrs
  rw [uc22p21k_center_eq_bot hL.2.2, Subgroup.card_bot]
  exact hr.not_dvd_one

theorem uc22ine229_exists_mem_conjClosure_normalizer_of_isSz
    {M T L : Subgroup G} (hT : IsSylowOf 2 T M) (hL : L ∈ calC M)
    (hc : (conjSetOf M L).ncard ≤ 2) {n s r : ℕ} (hX : IsSz (Bar2 L) n) (hs : Odd s)
    (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    ∃ x ∈ conjClosure M L, orderOf x = r ∧ x ∈ normalizer (T : Set G) := by
  haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hX
  refine uc22ine229_exists_mem_conjClosure_normalizer hT hL hc hr (uc22ine229_ne_two hs hrs) ?_
    fun T₀ hT₀ hT₀L hS => uc22ine229_exists_mem_normalizer_of_isSz hT₀ hT₀L hS hX hs hsn hr hrs
  rw [uc22p21k_center_eq_bot hL.2.2, Subgroup.card_bot]
  exact hr.not_dvd_one

end CFSG.LocalAnalysis.UniquenessCase.UC22
