module

public import CFSG.RankThree.PartOne.S13K.Sp6Comm
public import CFSG.RankThree.PartOne.S13K.Comm136
public import CFSG.RankThree.PartOne.S12.Sec138Loc
public import Certificates.Kernel.ThCent.Leaves

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.KFQ CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem sact_S (i : Fin 3) (a : Fin 3 → (Qext K)ˣ) :
    sact 1 (fun j => decide (j = i)) a = fun j => if j = i then (a j)⁻¹ else a j := by
  funext j
  by_cases h : j = i <;> simp [sact_apply, h]

theorem sact_S_mul_inv (i : Fin 3) (a : Fin 3 → (Qext K)ˣ) :
    sact 1 (fun j => decide (j = i)) a * a⁻¹ = evec ((a i)⁻¹ * (a i)⁻¹) i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [sact_S, evec]
  · simp [sact_S, evec, h]

theorem sact_S_sact_S (i : Fin 3) (a : Fin 3 → (Qext K)ˣ) :
    sact 1 (fun j => decide (j = i)) (sact 1 (fun j => decide (j = i)) a) = a := by
  funext j
  by_cases h : j = i <;> simp [sact_S, h]

theorem sact_S_comm (i j : Fin 3) (a : Fin 3 → (Qext K)ˣ) :
    sact 1 (fun k => decide (k = i)) (sact 1 (fun k => decide (k = j)) a) =
      sact 1 (fun k => decide (k = j)) (sact 1 (fun k => decide (k = i)) a) := by
  funext k
  by_cases hi : k = i
  · subst hi
    by_cases hj : k = j
    · subst hj
      simp [sact_S]
    · simp [sact_S, hj]
  · by_cases hj : k = j
    · subst hj
      simp [sact_S, hi]
    · simp [sact_S, hi, hj]

namespace Sp6Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
  (C : Sp6Ctx p A c L E f K)

@[expose] def cE : ↥E := ⟨c, C.R.c_mem⟩

theorem eT_congr {x y : Fin 3 → (Qext K)ˣ} {hx : ∀ i, x i ^ p = 1} {hy : ∀ i, y i ^ p = 1}
    (h : x = y) : C.eT x hx = C.eT y hy := by
  subst h
  rfl

theorem exists_decomp_eT (e : ↥E) :
    ∃ (a : Fin 3 → (Qext K)ˣ) (ha : ∀ i, a i ^ p = 1) (k : ℤ), e = C.eT a ha * C.cE ^ k := by
  obtain ⟨x, hx, k, hk⟩ := C.exists_decomp e.2
  obtain ⟨a, ha, hxa⟩ := hx
  have hxe : x = tor10 C.hpq' a ha := Subtype.ext hxa
  refine ⟨a, ha, k, Subtype.ext ?_⟩
  rw [hk, hxe]
  rfl

theorem tSgn_mem_torusImage (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) :
    C.tSgn π ε ∈ torusImage E L :=
  Sec12Three.mem_torusImage_iff.mpr ⟨C.phi (sg10 π ε), C.phi_mem_L _,
    C.mem_normalizer (sg10_hg1 C.hpq' π ε) (C.hg2_of_hg1 (sg10_hg1 C.hpq' π ε)), rfl⟩

theorem tSgn_fixes_c (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) : C.tSgn π ε C.cE = C.cE :=
  Sec13Base.fixes_c_of_mem_torusImage C.h C.R.c_mem (C.tSgn_mem_torusImage π ε)

theorem tSgn_apply_decomp (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) (a : Fin 3 → (Qext K)ˣ)
    (ha : ∀ i, a i ^ p = 1) (k : ℤ) :
    C.tSgn π ε (C.eT a ha * C.cE ^ k) = C.eT (sact π ε a) (sact_pow ha) * C.cE ^ k := by
  rw [map_mul, map_zpow, C.tSgn_apply_eT, C.tSgn_fixes_c]

theorem tSgn_sq_eq_one {π : Equiv.Perm (Fin 3)} {ε : Fin 3 → Bool}
    (hinv : ∀ (a : Fin 3 → (Qext K)ˣ), sact π ε (sact π ε a) = a) :
    C.tSgn π ε * C.tSgn π ε = 1 := by
  refine MulEquiv.ext fun e => ?_
  obtain ⟨a, ha, k, rfl⟩ := C.exists_decomp_eT e
  rw [MulAut.mul_apply, C.tSgn_apply_decomp, C.tSgn_apply_decomp, MulAut.one_apply]
  exact congrArg (fun x => x * C.cE ^ k) (C.eT_congr (hinv a))

theorem tSgn_comm_of_sact_comm {π π' : Equiv.Perm (Fin 3)} {ε ε' : Fin 3 → Bool}
    (hcomm : ∀ (a : Fin 3 → (Qext K)ˣ), sact π ε (sact π' ε' a) = sact π' ε' (sact π ε a)) :
    C.tSgn π ε * C.tSgn π' ε' = C.tSgn π' ε' * C.tSgn π ε := by
  refine MulEquiv.ext fun e => ?_
  obtain ⟨a, ha, k, rfl⟩ := C.exists_decomp_eT e
  rw [MulAut.mul_apply, MulAut.mul_apply, C.tSgn_apply_decomp, C.tSgn_apply_decomp,
    C.tSgn_apply_decomp, C.tSgn_apply_decomp]
  exact congrArg (fun x => x * C.cE ^ k) (C.eT_congr (hcomm a))

theorem tSgn_ne_one {π : Equiv.Perm (Fin 3)} {ε : Fin 3 → Bool}
    (hmv : ∃ (a : Fin 3 → (Qext K)ˣ) (_ : ∀ i, a i ^ p = 1), sact π ε a ≠ a) : C.tSgn π ε ≠ 1 := by
  obtain ⟨a, ha, hne⟩ := hmv
  intro h1
  apply hne
  have h2 := congrArg (fun m : MulAut E => m (C.eT a ha)) h1
  simp only [MulAut.one_apply] at h2
  rw [C.tSgn_apply_eT] at h2
  exact C.eT_injective h2

theorem tSgn_injective {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) (h5 : 5 ≤ p)
    {π π' : Equiv.Perm (Fin 3)} {ε ε' : Fin 3 → Bool} (h : C.tSgn π ε = C.tSgn π' ε') :
    π = π' ∧ ε = ε' := by
  refine sact_faithful hζ h5 (fun x hx => ?_)
  have h1 : C.tSgn π ε (C.eT x hx) = C.tSgn π' ε' (C.eT x hx) := by rw [h]
  rw [C.tSgn_apply_eT, C.tSgn_apply_eT] at h1
  exact C.eT_injective h1

theorem S_ne {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) (h5 : 5 ≤ p) {i j : Fin 3} (hij : i ≠ j) :
    C.tSgn 1 (fun k => decide (k = i)) ≠ C.tSgn 1 (fun k => decide (k = j)) := by
  intro h
  have := (C.tSgn_injective hζ h5 h).2
  have h2 := congrFun this i
  simp [hij] at h2

theorem S_comm (i j : Fin 3) :
    C.tSgn 1 (fun k => decide (k = i)) * C.tSgn 1 (fun k => decide (k = j)) =
      C.tSgn 1 (fun k => decide (k = j)) * C.tSgn 1 (fun k => decide (k = i)) :=
  C.tSgn_comm_of_sact_comm (fun a => sact_S_comm i j a)

theorem autMoved_tSgn_S {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) (hodd : Odd p)
    (i : Fin 3) :
    autMoved E (C.tSgn 1 (fun j => decide (j = i))) =
      Subgroup.zpowers (C.eT (evec ζ i) (evec_pow ζ hζ.pow_eq_one i)) := by
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  set t := C.tSgn 1 (fun j => decide (j = i)) with ht
  set m := C.eT (evec ζ i) (evec_pow ζ hζp i) with hm
  have hpow : ∀ (a : Fin 3 → (Qext K)ˣ), (∀ j, a j ^ p = 1) → ((a i)⁻¹ * (a i)⁻¹) ^ p = 1 := by
    intro a ha
    rw [mul_pow, inv_pow, ha i, inv_one, one_mul]
  have hgen : ∀ (a : Fin 3 → (Qext K)ˣ) (ha : ∀ j, a j ^ p = 1) (k : ℤ),
      t (C.eT a ha * C.cE ^ k) * (C.eT a ha * C.cE ^ k)⁻¹ =
        C.eT (evec ((a i)⁻¹ * (a i)⁻¹) i) (evec_pow _ (hpow a ha) i) := by
    intro a ha k
    rw [ht, C.tSgn_apply_decomp]
    have h1 : C.eT (sact 1 (fun j => decide (j = i)) a) (sact_pow ha) * C.cE ^ k *
        (C.eT a ha * C.cE ^ k)⁻¹ =
        C.eT (sact 1 (fun j => decide (j = i)) a) (sact_pow ha) * (C.eT a ha)⁻¹ := by
      group
    rw [h1, C.eT_inv, C.eT_mul]
    exact C.eT_congr (sact_S_mul_inv i a)
  apply le_antisymm
  · unfold autMoved
    rw [Subgroup.closure_le]
    rintro _ ⟨e, rfl⟩
    obtain ⟨a, ha, k, rfl⟩ := C.exists_decomp_eT e
    show t (C.eT a ha * C.cE ^ k) * (C.eT a ha * C.cE ^ k)⁻¹ ∈ Subgroup.zpowers m
    rw [hgen a ha k]
    obtain ⟨n, hn⟩ := exists_pow_eq hp hζ (hpow a ha)
    have hev : evec ((a i)⁻¹ * (a i)⁻¹) i = (evec ζ i) ^ n := by
      rw [← hn]
      funext j
      by_cases hj : j = i <;> simp [evec, hj]
    have hmn : C.eT (evec ((a i)⁻¹ * (a i)⁻¹) i) (evec_pow _ (hpow a ha) i) = m ^ n := by
      rw [hm, C.eT_pow]
      exact C.eT_congr hev
    rw [hmn]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers m) n
  · rw [Subgroup.zpowers_le]
    have hhalf : (p + 1) / 2 + (p + 1) / 2 = p + 1 := by
      obtain ⟨m', hm'⟩ := hodd
      omega
    set u₀ : (Qext K)ˣ := (ζ ^ ((p + 1) / 2))⁻¹ with hu₀def
    have hu₀ : u₀ ^ p = 1 := by
      rw [hu₀def, inv_pow, ← pow_mul, mul_comm, pow_mul, hζp, one_pow, inv_one]
    have hu₀2 : u₀⁻¹ * u₀⁻¹ = ζ := by
      rw [hu₀def, inv_inv, ← pow_add, hhalf, pow_succ, hζp, one_mul]
    have hv : ∀ j, (evec u₀ i) j ^ p = 1 := evec_pow u₀ hu₀ i
    have h1 := hgen (evec u₀ i) hv 0
    have hmem : t (C.eT (evec u₀ i) hv * C.cE ^ (0 : ℤ)) * (C.eT (evec u₀ i) hv * C.cE ^ (0 : ℤ))⁻¹ ∈
        autMoved E t := Subgroup.subset_closure ⟨_, rfl⟩
    rw [h1] at hmem
    have hi : (evec u₀ i) i = u₀ := by simp [evec]
    have hfun : evec (((evec u₀ i) i)⁻¹ * ((evec u₀ i) i)⁻¹) i = evec ζ i := by
      rw [hi, hu₀2]
    rw [C.eT_congr hfun] at hmem
    exact hmem

theorem isAutReflection_S (i : Fin 3) : IsAutReflection p E (C.tSgn 1 (fun j => decide (j = i))) := by
  have hp : p.Prime := C.h.prime
  have h5 : 5 ≤ p := Sec12Three.five_le C.h
  obtain ⟨ζ, hζ⟩ := exists_unit_primitiveRoot hp C.hp2 C.hpq'
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := zeta_ne_one hζ h5
  have hζi : ζ ≠ ζ⁻¹ := zeta_ne_inv hζ h5
  have hodd : Odd p := hp.odd_of_ne_two C.hp2
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsq : C.tSgn 1 (fun j => decide (j = i)) ^ 2 = 1 := by
      rw [sq]
      exact C.tSgn_sq_eq_one (fun a => sact_S_sact_S i a)
    refine orderOf_eq_prime hsq (C.tSgn_ne_one ⟨evec ζ i, evec_pow ζ hζp i, fun h => ?_⟩)
    have h2 := congrFun h i
    have h3 : ζ⁻¹ = ζ := by simpa [sact_S, evec] using h2
    exact hζi h3.symm
  · rw [C.autMoved_tSgn_S hζ hp hodd i, Nat.card_zpowers]
    have hm1 : (C.eT (evec ζ i) (evec_pow ζ hζp i)) ^ p = 1 := by
      rw [C.eT_pow]
      have h1 : (evec ζ i) ^ p = 1 := by
        funext j
        exact evec_pow ζ hζp i j
      exact (C.eT_congr h1).trans C.eT_one
    have hm2 : C.eT (evec ζ i) (evec_pow ζ hζp i) ≠ 1 := by
      intro h
      have h' : C.eT (evec ζ i) (evec_pow ζ hζp i) = C.eT (1 : Fin 3 → (Qext K)ˣ) (fun _ => one_pow _) :=
        h.trans C.eT_one.symm
      have h3 := congrFun (C.eT_injective h') i
      have h4 : ζ = 1 := by simpa [evec] using h3
      exact hζ1 h4
    exact orderOf_eq_prime hm1 hm2

theorem S_mem_reflectionSet (hF13 : Sec13Facts G p A c L E) (i : Fin 3) :
    C.tSgn 1 (fun j => decide (j = i)) ∈ reflectionSet p E :=
  ⟨C.isAutReflection_S i, L, hF13.inZeroStar, C.tSgn_mem_torusImage _ _⟩

end Sp6Ctx

theorem le_centralizer_symm {G : Type} [Group G] {A B : Subgroup G}
    (h : A ≤ Subgroup.centralizer (B : Set G)) : B ≤ Subgroup.centralizer (A : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact ((Subgroup.mem_centralizer_iff.mp (h hy)) x hx).symm

theorem no_four_local {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G} {f : ℕ}
    (hf : 2 ≤ f) (he : CFSG.twoLocalOddRank G = 3) {a b c d : MulAut E}
    (hKa : KFAt p E f a) (hKb : KFAt p E f b) (hKc : KFAt p E f c) (hKd : KFAt p E f d)
    (hab : kZero p E a ≤ Subgroup.centralizer (kZero p E b : Set G))
    (hac : kZero p E a ≤ Subgroup.centralizer (kZero p E c : Set G))
    (had : kZero p E a ≤ Subgroup.centralizer (kZero p E d : Set G))
    (hbc : kZero p E b ≤ Subgroup.centralizer (kZero p E c : Set G))
    (hbd : kZero p E b ≤ Subgroup.centralizer (kZero p E d : Set G))
    (hcd : kZero p E c ≤ Subgroup.centralizer (kZero p E d : Set G)) : False := by
  obtain ⟨r, hr, hr2, hrf⟩ := Sec138Loc.exists_odd_prime_dvd_two_pow_sub_one hf
  let K : Fin 4 → Subgroup G := ![kZero p E a, kZero p E b, kZero p E c, kZero p E d]
  have hcomm : ∀ i j, i ≠ j → K i ≤ Subgroup.centralizer (K j : Set G) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hab
    · exact hac
    · exact had
    · exact le_centralizer_symm hab
    · exact absurd rfl hij
    · exact hbc
    · exact hbd
    · exact le_centralizer_symm hac
    · exact le_centralizer_symm hbc
    · exact absurd rfl hij
    · exact hcd
    · exact le_centralizer_symm had
    · exact le_centralizer_symm hbd
    · exact le_centralizer_symm hcd
    · exact absurd rfl hij
  have hU : ∀ i, ∃ U : Subgroup (K i), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∃ x ∈ Subgroup.normalizer (U : Set (K i)), orderOf x = r ∧ ∃ u ∈ U, x * u * x⁻¹ ≠ u := by
    intro i
    fin_cases i
    · exact exists_two_subgroup_normalized_by_odd_prime hKa.2.1 hr hr2 hrf
    · exact exists_two_subgroup_normalized_by_odd_prime hKb.2.1 hr hr2 hrf
    · exact exists_two_subgroup_normalized_by_odd_prime hKc.2.1 hr hr2 hrf
    · exact exists_two_subgroup_normalized_by_odd_prime hKd.2.1 hr hr2 hrf
  have h4 : 4 ≤ RankThreeEven.localRank r G := four_le_localRank_of_commuting hr K hcomm hU
  have hrG : r ∣ Nat.card G := prime_dvd_card_of_localRank_pos hr (by omega)
  have h3 := Theta.localRank_le_twoLocalOddRank hr hr2 hrG
  omega

end CFSG.RankThree.PartOne.S13K
