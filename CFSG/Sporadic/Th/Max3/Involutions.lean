
module


public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10089

public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native

namespace InvRep

@[expose] noncomputable def kap :
    ↥M →* alternatingGroup (Fin 9) :=
  (kappa : AltQuot.MQ ≃* alternatingGroup (Fin 9)).toMonoidHom.comp AltQuot.proj

private theorem native_involution_facts :
    (∀ k : Fin 512, eqRows (mulRows (rowsNfAt k) (rowsNfAt k)) idRows = false ∨
      eqRows (rowsNfAt k) idRows = true ∨ eqRows (rowsNfAt k) rowsZ = true ∨
      eqRows (mulRows (rowsConj k) (rowsQ 0)) (mulRows (rowsNfAt k) (rowsConj k)) = true) ∧
    (∀ k : Fin 512, eqRows (mulRows (rowsXNf k) (rowsXNf k)) idRows = false ∨
      eqRows (mulRows (rowsNfAt (uIdx k)) rowsX) (mulRows (rowsXNf k) (rowsNfAt (uIdx k))) =
        true) ∧
    (∀ k : Fin 512, eqRows (mulRows (rowsDNf k) (rowsDNf k)) idRows = false) :=
  Certificates.certificate10089

theorem exists_nfAt_eq
    {g : J} (hg : g ∈ Q) : ∃ k : Fin 512, nfAt k = g := by
  obtain ⟨s, v, rfl⟩ := mem_Q_iff.1 hg
  have h := ZMod.val_lt s
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  have h5 := ZMod.val_lt (v 5)
  have h6 := ZMod.val_lt (v 6)
  have h7 := ZMod.val_lt (v 7)
  obtain ⟨k, hk⟩ : ∃ k : Fin 512, k.val = s.val + 2 * (v 0).val + 4 * (v 1).val +
      8 * (v 2).val + 16 * (v 3).val + 32 * (v 4).val + 64 * (v 5).val + 128 * (v 6).val +
      256 * (v 7).val := ⟨⟨_, by omega⟩, rfl⟩
  refine ⟨k, ?_⟩
  rw [nf_eq_nfN, nfAt]
  congr 1
  · omega
  · funext i
    fin_cases i <;> simp <;> omega

theorem exists_conj_of_mem_Q
    {m : J} (hm : m ∈ Q) (hsq : m * m = 1) (hne : m ≠ 1) :
    ∃ g ∈ M, g * m * g⁻¹ = z ∨ g * m * g⁻¹ = q 0 := by
  obtain ⟨k, rfl⟩ := exists_nfAt_eq hm
  rcases native_involution_facts.1 k with h | h | h | h
  · exact absurd hsq (((isRows_nfAt k).mul (isRows_nfAt k)).ne_of_eqRows IsRows.one h)
  · exact absurd ((isRows_nfAt k).eq_of_eqRows IsRows.one h) hne
  · exact ⟨1, M.one_mem, Or.inl (by simpa using (isRows_nfAt k).eq_of_eqRows isRows_z h)⟩
  · have hw := IsRows.word isRows_x isRows_y (conjWord k)
    have e : wordProd (conjWord k) * q 0 = nfAt k * wordProd (conjWord k) :=
      (hw.mul (isRows_q 0)).eq_of_eqRows ((isRows_nfAt k).mul hw) h
    refine ⟨(wordProd (conjWord k))⁻¹, M.inv_mem (wordProd_mem_M _), Or.inr ?_⟩
    rw [inv_inv, mul_assoc, ← e, inv_mul_cancel_left]

theorem kap_surjective :
    Function.Surjective kap :=
  kappa.surjective.comp AltQuot.proj_surjective

theorem kap_eq_iff
    {g h : ↥M} : kap g = kap h ↔ (g : J)⁻¹ * h ∈ Q :=
  kappa.injective.eq_iff.trans AltQuot.proj_eq_proj_iff

theorem kap_eq_one_iff
    {g : ↥M} : kap g = 1 ↔ (g : J) ∈ Q :=
  (map_eq_one_iff kappa kappa.injective).trans AltQuot.proj_eq_one_iff

theorem kap_genM
    (l : Gen) : (kap (genM l) : Equiv.Perm (Fin 9)) = Gen.eval aPerm bPerm l := by
  cases l
  · exact kappa_mk_x
  · exact kappa_mk_y

theorem kap_wordM
    (w : List Gen) :
    (kap (wordM w) : Equiv.Perm (Fin 9)) = (w.map (Gen.eval aPerm bPerm)).prod := by
  induction w with
  | nil => rw [wordM_nil, map_one]; rfl
  | cons l w ih => rw [wordM_cons, map_mul, Subgroup.coe_mul, ih, kap_genM]; rfl

theorem exists_conj_x_of_kap_altRep4
    {n : ↥M} (hsq : n * n = 1)
    (hk : (kap n : Equiv.Perm (Fin 9)) = altRep4) : ∃ h ∈ M, h * (n : J) * h⁻¹ = x := by
  have hsq' : (n : J) * n = 1 := by rw [← Subgroup.coe_mul, hsq, Subgroup.coe_one]
  have h1 : kap (genM .x) = kap n := Subtype.ext ((kap_genM .x).trans (aPerm_eq.trans hk.symm))
  obtain ⟨k, hk'⟩ := exists_nfAt_eq (kap_eq_iff.1 h1)
  have hn : (n : J) = x * nfAt k := by
    rw [hk']
    exact (mul_inv_cancel_left x _).symm
  rcases native_involution_facts.2.1 k with h | h
  · have hP := isRows_x.mul (isRows_nfAt k)
    refine absurd ?_ ((hP.mul hP).ne_of_eqRows IsRows.one h)
    rw [← hn]
    exact hsq'
  · have e : nfAt (uIdx k) * x = x * nfAt k * nfAt (uIdx k) :=
      ((isRows_nfAt _).mul isRows_x).eq_of_eqRows
        ((isRows_x.mul (isRows_nfAt k)).mul (isRows_nfAt _)) h
    refine ⟨(nfAt (uIdx k))⁻¹, Q_le_M (Q.inv_mem (AltQuot.nfAt_mem_Q _)), ?_⟩
    rw [hn, inv_inv, mul_assoc, ← e, inv_mul_cancel_left]

theorem kap_wordM_dWord :
    (kap (wordM dWord) : Equiv.Perm (Fin 9)) = altRep2 := by
  rw [kap_wordM]
  decide

theorem not_kap_altRep2
    {n : ↥M} (hsq : n * n = 1) :
    (kap n : Equiv.Perm (Fin 9)) ≠ altRep2 := by
  intro hk
  have hsq' : (n : J) * n = 1 := by rw [← Subgroup.coe_mul, hsq, Subgroup.coe_one]
  have h1 : kap (wordM dWord) = kap n := Subtype.ext (kap_wordM_dWord.trans hk.symm)
  obtain ⟨k, hk'⟩ := exists_nfAt_eq (kap_eq_iff.1 h1)
  have hn : (n : J) = wordProd dWord * nfAt k := by
    have e : (wordM dWord : J) = wordProd dWord := rfl
    rw [e] at hk'
    rw [hk']
    exact (mul_inv_cancel_left _ _).symm
  have hD := IsRows.word isRows_x isRows_y dWord
  have hP := hD.mul (isRows_nfAt k)
  refine (hP.mul hP).ne_of_eqRows IsRows.one (native_involution_facts.2.2 k) ?_
  rw [← hn]
  exact hsq'

theorem exists_conj_x_of_not_mem_Q
    {m : J} (hm : m ∈ M) (hQ : m ∉ Q) (hsq : m * m = 1) :
    ∃ g ∈ M, g * m * g⁻¹ = x := by
  have hσ1 : kap ⟨m, hm⟩ ≠ 1 := fun h => hQ (kap_eq_one_iff.1 h)
  have hmm : (⟨m, hm⟩ : ↥M) * ⟨m, hm⟩ = 1 := Subtype.ext hsq
  have hσsq : (kap ⟨m, hm⟩ : Equiv.Perm (Fin 9)) ^ 2 = 1 := by
    have h : kap ⟨m, hm⟩ * kap ⟨m, hm⟩ = 1 := by rw [← map_mul, hmm, map_one]
    rw [sq]
    exact congrArg Subtype.val h
  have hord : orderOf (kap ⟨m, hm⟩ : Equiv.Perm (Fin 9)) = 2 :=
    orderOf_eq_prime hσsq (fun h => hσ1 (Subtype.ext h))
  obtain ⟨g, hgA, hg⟩ := exists_conj_eq_of_orderOf_eq_two (kap ⟨m, hm⟩).2 hord
  obtain ⟨t, ht⟩ := kap_surjective ⟨g, hgA⟩
  have hnsq : (t * ⟨m, hm⟩ * t⁻¹) * (t * ⟨m, hm⟩ * t⁻¹) = (1 : ↥M) := by
    calc (t * ⟨m, hm⟩ * t⁻¹) * (t * ⟨m, hm⟩ * t⁻¹) = t * (⟨m, hm⟩ * ⟨m, hm⟩) * t⁻¹ := by group
      _ = 1 := by rw [hmm]; group
  have hkn : (kap (t * ⟨m, hm⟩ * t⁻¹) : Equiv.Perm (Fin 9)) =
      g * (kap ⟨m, hm⟩ : Equiv.Perm (Fin 9)) * g⁻¹ := by
    rw [map_mul, map_mul, map_inv, ht]
    rfl
  rcases hg with h2 | h4
  · exact absurd (hkn.trans h2) (not_kap_altRep2 hnsq)
  · obtain ⟨h, hhM, hh⟩ := exists_conj_x_of_kap_altRep4 hnsq (hkn.trans h4)
    refine ⟨h * t, M.mul_mem hhM t.2, ?_⟩
    rw [← hh]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

end InvRep

theorem max3_involution_representatives
    (m : J) (hm : m ∈ M) (h2 : orderOf m = 2) :
    ∃ g ∈ M, g * m * g⁻¹ = z ∨ g * m * g⁻¹ = q 0 ∨ g * m * g⁻¹ = x := by
  have hsq : m * m = 1 := by
    have h := pow_orderOf_eq_one m
    rwa [h2, sq] at h
  have hne : m ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at h2
    exact absurd h2 (by norm_num)
  by_cases hQ : m ∈ Q
  · obtain ⟨g, hg, h⟩ := InvRep.exists_conj_of_mem_Q hQ hsq hne
    exact ⟨g, hg, h.elim Or.inl (fun h' => Or.inr (Or.inl h'))⟩
  · obtain ⟨g, hg, h⟩ := InvRep.exists_conj_x_of_not_mem_Q hm hQ hsq
    exact ⟨g, hg, Or.inr (Or.inr h)⟩

end CFSG.Sporadic.Th.Max3
