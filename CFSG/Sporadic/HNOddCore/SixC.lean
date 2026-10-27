module

public import CFSG.Sporadic.HNOddCore.SixB
public import Certificates.Certificate2084
public import Certificates.Certificate2087
public import Certificates.Certificate2091
public import Certificates.Certificate2092
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Certificates.Native Equiv

theorem pinvs_get {n : ℕ} {S : Array (Array ℕ)} {s : ℕ} (hs : s < S.size) :
    (pinvs n S)[s]! = pinvCand n S[s]! := by
  rw [pinvs, getElem!_pos _ s (by simpa using hs), Array.getElem_map, ← getElem!_pos S s hs]

theorem om0Gens_size : om0Gens.size = 12 := six_parts.1

theorem prep_om0_inv
    {s : ℕ} (hs : s < 12) :
    PRep 1100 (pinvs 1100 om0Gens)[s]! (om0Perm s)⁻¹ := by
  rw [pinvs_get (by rw [om0Gens_size]; exact hs)]
  exact prep_inv_of_pisInv (prep_om0 hs) (six_parts.2.1 s hs)

theorem word_spec
    {w : List ℤ} (hw : plettersOK 12 w = true) :
    ∃ σ ∈ phi6.range, PRep 1100 (pword 1100 om0Gens (pinvs 1100 om0Gens) w) σ :=
  prep_pword_mem (fun _ hh => prep_om0 hh) (fun _ hh => prep_om0_inv hh)
    (fun _ hh => om0Perm_mem hh) w hw

theorem a_spec :
    ∃ σ ∈ phi6.range, PRep 1100 aArr σ := by
  rw [aArr_eq]
  obtain ⟨σ, hσ, hp⟩ := word_spec six_parts.2.2.1
  exact ⟨σ ^ SixData.ea, pow_mem hσ _, prep_ppowN hp _⟩

theorem b_spec :
    ∃ σ ∈ phi6.range, PRep 1100 bArr σ := by
  rw [bArr_eq]
  obtain ⟨σ, hσ, hp⟩ := word_spec six_parts.2.2.2.1
  exact ⟨σ ^ SixData.eb, pow_mem hσ _, prep_ppowN hp _⟩

@[expose] def aD : Perm (Fin 1100) := Monster.B.Co2.permOfArr 1100 aArr

@[expose] def bD : Perm (Fin 1100) := Monster.B.Co2.permOfArr 1100 bArr

theorem prep_aD :
    PRep 1100 aArr aD := by
  obtain ⟨σ, -, hp⟩ := a_spec
  rw [aD, permOfArr_eq_of_prep hp]
  exact hp

theorem prep_bD :
    PRep 1100 bArr bD := by
  obtain ⟨σ, -, hp⟩ := b_spec
  rw [bD, permOfArr_eq_of_prep hp]
  exact hp

theorem aD_mem :
    aD ∈ phi6.range := by
  obtain ⟨σ, hσ, hp⟩ := a_spec
  rw [aD, permOfArr_eq_of_prep hp]
  exact hσ

theorem bD_mem :
    bD ∈ phi6.range := by
  obtain ⟨σ, hσ, hp⟩ := b_spec
  rw [bD, permOfArr_eq_of_prep hp]
  exact hσ

theorem ne_of_peq_false {n : ℕ} {t u : Array ℕ} {g h : Perm (Fin n)} (ht : PRep n t g)
    (hu : PRep n u h) (he : peq n t u = false) : g ≠ h := fun e => by
  have := (peq_iff ht hu).2 e
  rw [he] at this
  exact Bool.false_ne_true this

theorem aD_sq :
    aD ^ 2 = 1 := by
  rw [pow_two]
  exact eq_of_peq (prep_pcomp prep_aD prep_aD) prep_pid six_parts.2.2.2.2.1

theorem aD_ne_one :
    aD ≠ 1 := ne_of_peq_false prep_aD prep_pid six_parts.2.2.2.2.2.1

theorem bD_pow :
    bD ^ 5 = 1 :=
  eq_of_peq (prep_ppowN prep_bD 5) prep_pid six_parts.2.2.2.2.2.2.1

theorem bD_ne_one :
    bD ≠ 1 := ne_of_peq_false prep_bD prep_pid six_parts.2.2.2.2.2.2.2.1

theorem abD_pow :
    (aD * bD) ^ 11 = 1 :=
  eq_of_peq (prep_ppowN (prep_pcomp prep_aD prep_bD) 11) prep_pid
    six_parts.2.2.2.2.2.2.2.2.1

theorem abD_ne_one :
    aD * bD ≠ 1 :=
  ne_of_peq_false (prep_pcomp prep_aD prep_bD) prep_pid six_parts.2.2.2.2.2.2.2.2.2.1

theorem abD_ne_ba :
    aD * bD ≠ bD * aD :=
  ne_of_peq_false (prep_pcomp prep_aD prep_bD) (prep_pcomp prep_bD prep_aD)
    six_parts.2.2.2.2.2.2.2.2.2.2.1

theorem orderOf_aD :
    orderOf aD = 2 := orderOf_eq_prime aD_sq aD_ne_one

theorem orderOf_bD :
    orderOf bD = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime bD_pow bD_ne_one

theorem orderOf_abD :
    orderOf (aD * bD) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime abD_pow abD_ne_one

abbrev Dsub : Subgroup (Perm (Fin 1100)) := Subgroup.closure ({aD, bD} : Set (Perm (Fin 1100)))

@[expose] def abD (k : ℕ) : Perm (Fin 1100) := if k = 0 then aD else bD

theorem prep_abD
    {k : ℕ} (hk : k < 2) :
    PRep 1100 (#[aArr, bArr] : Array (Array ℕ))[k]! (abD k) := by
  have key : ∀ (A B : Array ℕ) (a b : Perm (Fin 1100)), PRep 1100 A a → PRep 1100 B b →
      ∀ k < 2, PRep 1100 (#[A, B] : Array (Array ℕ))[k]! (if k = 0 then a else b) := by
    intro A B a b ha hb k hk
    interval_cases k
    · exact ha
    · exact hb
  exact key _ _ _ _ prep_aD prep_bD k hk

theorem range_abD : Set.range (fun k : Fin 2 => abD k) = ({aD, bD} : Set (Perm (Fin 1100))) := by
  have key : ∀ a b : Perm (Fin 1100),
      Set.range (fun k : Fin 2 => if (k : ℕ) = 0 then a else b) = {a, b} := by
    intro a b
    ext σ
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, rfl⟩
      fin_cases k
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  exact key aD bD

theorem Dsub_eq_arrGen :
    Dsub = arrGen 1100 #[aArr, bArr] := by
  rw [arrGen_eq (σ := abD) fun k hk => prep_abD (by simpa using hk)]
  show Subgroup.closure _ = Subgroup.closure _
  congr 1
  rw [← range_abD]
  ext σ
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k, by simp; omega⟩, rfl⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    exact ⟨⟨k, by simpa using hk⟩, rfl⟩

theorem card_Dsub :
    Nat.card Dsub = 44352000 := by
  rw [Dsub_eq_arrGen, card_arrGen_of_chainCheck (by norm_num) (by decide)
    six_parts.2.2.2.2.2.2.2.2.2.2.2.1]
  decide

theorem mem_Dsub_iff
    {t : Array ℕ} {g : Perm (Fin 1100)} (ht : PRep 1100 t g) :
    siftA 1100 lvArr dBaseArr 0 t = true ↔ g ∈ Dsub := by
  rw [Dsub_eq_arrGen, lvArr_eq]
  exact mem_arrGen_iff_sift (by norm_num) (by decide) six_parts.2.2.2.2.2.2.2.2.2.2.2.1 ht

theorem Dsub_le_range :
    Dsub ≤ phi6.range := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact aD_mem
  · exact bD_mem

theorem closure_abD :
    Subgroup.closure (Set.range fun k : Fin (#[aArr, bArr] : Array (Array ℕ)).size => abD k) =
      Dsub := by
  show Subgroup.closure _ = Subgroup.closure _
  congr 1
  rw [← range_abD]
  ext σ
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k, by simpa using k.2⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k, by simp; omega⟩, rfl⟩

theorem Dsub_transitive :
    ∀ p q : Fin 1100, ∃ g ∈ Dsub, g p = q := by
  have hc := six_parts.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold orbitOK at hc
  have h := orbit_eq_of_orbitCertOK (fun k hk => prep_abD (by simpa using hk)) hc
  dsimp only at h
  rw [closure_abD, PtList.range_eq_univ _ six_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at h
  rw [Set.eq_univ_iff_forall] at h
  intro p q
  obtain ⟨g1, hg1⟩ := h p
  obtain ⟨g2, hg2⟩ := h q
  simp only at hg1 hg2
  refine ⟨((g2 * g1⁻¹ : Dsub) : Perm (Fin 1100)), (g2 * g1⁻¹ : Dsub).2, ?_⟩
  have e : (g2 * g1⁻¹) • p = q := by
    rw [mul_smul, ← hg1, inv_smul_smul, hg2]
  exact e

end CFSG.Sporadic.HNOddCore
