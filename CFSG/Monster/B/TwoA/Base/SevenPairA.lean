module

public import CFSG.Monster.B.TwoA.Base.M22
public import CFSG.Monster.B.TwoA.Base.TwoPair
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import Mathlib.GroupTheory.GroupAction.ConjAct
public meta import CFSG.Monster.B.TwoA.Census.PermCert
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Base.SevenPairAInputs
public import Certificates.Certificate3052
public import Certificates.Certificate3017
public import Certificates.Certificate3029

public section

namespace CFSG.Monster.B.TwoA

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Census CFSG.Sporadic.Mathieu

open scoped Pointwise

theorem smul_eq_iff_conj {σ : Equiv.Perm (Fin 24)} {A : Finset (Set.powersetCard (Fin 24) 2)}
    (hinv : ∀ x, σ (σ x) = x) (H1 : ∀ x (h : x ≠ σ x), duad x (σ x) h ∈ A)
    (H2 : ∀ D ∈ A, ∃ x, ∃ h : x ≠ σ x, D = duad x (σ x) h) (p : Equiv.Perm (Fin 24)) :
    p • A = A ↔ p * σ * p⁻¹ = σ := by
  constructor
  · intro hA
    have hc : ∀ y, p (σ y) = σ (p y) := by
      intro y
      by_cases hy : y = σ y
      · rw [← hy]
        by_contra hne
        have hD := H1 (p y) hne
        rw [← hA, Finset.mem_smul_finset] at hD
        obtain ⟨D', hD', hpD⟩ := hD
        obtain ⟨z, hz, rfl⟩ := H2 D' hD'
        rw [smul_duad] at hpD
        have h1 := congrArg Subtype.val hpD
        rw [duad_val, duad_val] at h1
        have hpy : p y ∈ ({p • z, p • σ z} : Finset (Fin 24)) := by
          rw [h1]; exact Finset.mem_insert_self _ _
        simp only [Finset.mem_insert, Finset.mem_singleton, Equiv.Perm.smul_def] at hpy
        rcases hpy with h2 | h2
        · have := p.injective h2
          subst this
          exact hz hy
        · have := p.injective h2
          subst this
          exact hz (hy.trans (hinv z)).symm
      · have hD := H1 y hy
        have hpD : p • duad y (σ y) hy ∈ A := by
          rw [← hA]; exact Finset.smul_mem_smul_finset hD
        obtain ⟨z, hz, hz'⟩ := H2 _ hpD
        rw [smul_duad] at hz'
        have h1 := congrArg Subtype.val hz'
        rw [duad_val, duad_val, pair_eq_pair_iff (fun e => hy (smul_left_cancel p e)) hz] at h1
        simp only [Equiv.Perm.smul_def] at h1
        rcases h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
        · rw [h3, h2]
        · rw [h2, hinv, h3]
    refine Equiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := p.surjective x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    simp [hc]
  · intro h
    have hc : ∀ y, p (σ y) = σ (p y) := fun y => by
      have := congrArg (fun f : Equiv.Perm (Fin 24) => f (p y)) h
      simpa using this
    have hsub : p • A ⊆ A := by
      intro D hD
      rw [Finset.mem_smul_finset] at hD
      obtain ⟨D', hD', rfl⟩ := hD
      obtain ⟨z, hz, rfl⟩ := H2 D' hD'
      have hz' : p z ≠ σ (p z) := fun e => hz (p.injective (e.trans (hc z).symm))
      rw [smul_duad]
      convert H1 (p z) hz' using 1
      exact duad_congr _ _ rfl (hc z)
    exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])

@[expose] def A2 : Finset (Set.powersetCard (Fin 24) 2) :=
  {duad 2 3 (by decide), duad 4 5 (by decide), duad 6 7 (by decide)}

@[expose] def A3 : Finset (Set.powersetCard (Fin 24) 2) :=
  {duad 2 3 (by decide), duad 4 5 (by decide), duad 6 7 (by decide), duad 8 9 (by decide),
    duad 10 11 (by decide), duad 12 13 (by decide), duad 14 15 (by decide)}

@[expose] def sig2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

@[expose] def sig3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

theorem sig2_inv : ∀ x, sig2 (sig2 x) = x := by decide

theorem sig3_inv : ∀ x, sig3 (sig3 x) = x := by decide

theorem sig2_H1 : ∀ x (h : x ≠ sig2 x), duad x (sig2 x) h ∈ A2 := by decide

theorem sig3_H1 : ∀ x (h : x ≠ sig3 x), duad x (sig3 x) h ∈ A3 := by decide

theorem sig2_H2 : ∀ D ∈ A2, ∃ x, ∃ h : x ≠ sig2 x, D = duad x (sig2 x) h := by
  intro D hD
  simp only [A2, Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl | rfl
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩

theorem sig3_H2 : ∀ D ∈ A3, ∃ x, ∃ h : x ≠ sig3 x, D = duad x (sig3 x) h := by
  intro D hD
  simp only [A3, Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨8, by decide, rfl⟩
  · exact ⟨10, by decide, rfl⟩
  · exact ⟨12, by decide, rfl⟩
  · exact ⟨14, by decide, rfl⟩

@[expose] def FA2 : Subgroup AutPerm := Ppair ⊓ MulAction.stabilizer AutPerm A2

@[expose] def FA3 : Subgroup AutPerm := Ppair ⊓ MulAction.stabilizer AutPerm A3

theorem FA2_le_Ppair : FA2 ≤ Ppair := inf_le_left

theorem FA3_le_Ppair : FA3 ≤ Ppair := inf_le_left

theorem mem_stabilizer_A2_iff (p : AutPerm) :
    p ∈ MulAction.stabilizer AutPerm A2 ↔
      (p : Equiv.Perm (Fin 24)) * sig2 * (p : Equiv.Perm (Fin 24))⁻¹ = sig2 := by
  rw [MulAction.mem_stabilizer_iff]
  exact smul_eq_iff_conj sig2_inv sig2_H1 sig2_H2 _

theorem mem_stabilizer_A3_iff (p : AutPerm) :
    p ∈ MulAction.stabilizer AutPerm A3 ↔
      (p : Equiv.Perm (Fin 24)) * sig3 * (p : Equiv.Perm (Fin 24))⁻¹ = sig3 := by
  rw [MulAction.mem_stabilizer_iff]
  exact smul_eq_iff_conj sig3_inv sig3_H1 sig3_H2 _

@[expose] def tP : Equiv.Perm (Fin 24) where
  toFun := ![1, 0, 12, 13, 17, 18, 21, 23, 19, 16, 20, 22, 2, 3, 15, 14, 9, 4, 5, 8, 10, 6, 11, 7]
  invFun := ![1, 0, 12, 13, 17, 18, 21, 23, 19, 16, 20, 22, 2, 3, 15, 14, 9, 4, 5, 8, 10, 6, 11, 7]
  left_inv := by decide
  right_inv := by decide

theorem tP_mem : tP ∈ AutPerm := mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem tP_mem_Ppair : (⟨tP, tP_mem⟩ : AutPerm) ∈ Ppair :=
  (mem_Ppair_iff _).2 (.inr ⟨rfl, rfl⟩)

theorem mogA_mem_P0 : (⟨mogA, mogA_mem⟩ : AutPerm) ∈ P0 := (mem_P0_iff _).2 ⟨rfl, rfl⟩

theorem mogB_mem_P0 : (⟨mogB, mogB_mem⟩ : AutPerm) ∈ P0 := (mem_P0_iff _).2 ⟨rfl, rfl⟩

theorem P0_map_le_closure :
    P0.map AutPerm.subtype ≤ Subgroup.closure ({mogA, mogB} : Set (Equiv.Perm (Fin 24))) := by
  rintro _ ⟨p, hp, rfl⟩
  rw [← range_psiM] at hp
  obtain ⟨g, rfl⟩ := hp
  change psiHom g ∈ _
  have hg : (g : Equiv.Perm (Fin 22)) ∈ Subgroup.closure
      ({m22gA, m22gB} : Set (Equiv.Perm (Fin 22))) := by
    rw [← m22_eq]; exact g.2
  have h := Subgroup.mem_map_of_mem psiHom hg
  rw [MonoidHom.map_closure, Set.image_pair, psi_m22gA, psi_m22gB] at h
  exact h

theorem Pperm_eq_closure :
    Ppair.map AutPerm.subtype =
      Subgroup.closure ({mogA, mogB, tP} : Set (Equiv.Perm (Fin 24))) := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    have hsub : Subgroup.closure ({mogA, mogB} : Set (Equiv.Perm (Fin 24))) ≤
        Subgroup.closure {mogA, mogB, tP} :=
      Subgroup.closure_mono (fun x hx => by
        rcases hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl))
    have ht : tP ∈ Subgroup.closure ({mogA, mogB, tP} : Set (Equiv.Perm (Fin 24))) :=
      Subgroup.subset_closure (Or.inr (Or.inr rfl))
    rcases (mem_Ppair_iff p).1 hp with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact hsub (P0_map_le_closure ⟨p, (mem_P0_iff p).2 ⟨h0, h1⟩, rfl⟩)
    ·
      have hq : (⟨tP, tP_mem⟩ : AutPerm)⁻¹ * p ∈ P0 := by
        rw [mem_P0_iff]
        refine ⟨?_, ?_⟩
        · change tP⁻¹ ((p : Equiv.Perm (Fin 24)) 0) = 0
          rw [h0]; rfl
        · change tP⁻¹ ((p : Equiv.Perm (Fin 24)) 1) = 1
          rw [h1]; rfl
      have h2 := hsub (P0_map_le_closure ⟨_, hq, rfl⟩)
      have e : AutPerm.subtype p = tP * AutPerm.subtype ((⟨tP, tP_mem⟩ : AutPerm)⁻¹ * p) := by
        change (p : Equiv.Perm (Fin 24)) = tP * (tP⁻¹ * p)
        group
      rw [e]
      exact Subgroup.mul_mem _ ht h2
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact ⟨_, P0_le_Ppair mogA_mem_P0, rfl⟩
    · exact ⟨_, P0_le_Ppair mogB_mem_P0, rfl⟩
    · exact ⟨_, tP_mem_Ppair, rfl⟩

theorem gensP_perm : ∀ k < gensP.size, PermArr gensP[k]! = true := by decide +kernel

theorem decode_gensP_zero : decode gensP[0]! = mogA := by
  ext i
  rw [decode_apply (gensP_perm 0 (by decide))]
  revert i
  decide

theorem decode_gensP_one : decode gensP[1]! = mogB := by
  ext i
  rw [decode_apply (gensP_perm 1 (by decide))]
  revert i
  decide

theorem decode_gensP_two : decode gensP[2]! = tP := by
  ext i
  rw [decode_apply (gensP_perm 2 (by decide))]
  revert i
  decide

theorem decode_sig2Arr : decode sig2Arr = sig2 := by
  ext i
  rw [decode_apply (by decide +kernel)]
  revert i
  decide

theorem decode_sig3Arr : decode sig3Arr = sig3 := by
  ext i
  rw [decode_apply (by decide +kernel)]
  revert i
  decide

@[expose] noncomputable def conjGenP (k : ℕ) : ConjAct (Equiv.Perm (Fin 24)) :=
  ConjAct.toConjAct (decode gensP[k]!)

theorem conjP_act : ∀ k < gensP.size, ∀ a, PermArr a = true →
    decode (aconj gensP[k]! a) = conjGenP k • decode a := by
  intro k hk a ha
  rw [decode_aconj (gensP_perm k hk) ha, conjGenP, ConjAct.toConjAct_smul]

theorem conjGenP_image : conjGenP '' {k | k < gensP.size} =
    (ConjAct.toConjAct : Equiv.Perm (Fin 24) ≃* ConjAct (Equiv.Perm (Fin 24))).toMonoidHom ''
      {mogA, mogB, tP} := by
  have hs : gensP.size = 3 := rfl
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, hs, Set.mem_insert_iff, Set.mem_singleton_iff,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact ⟨mogA, Or.inl rfl, by rw [conjGenP, decode_gensP_zero]⟩
    · exact ⟨mogB, Or.inr (Or.inl rfl), by rw [conjGenP, decode_gensP_one]⟩
    · exact ⟨tP, Or.inr (Or.inr rfl), by rw [conjGenP, decode_gensP_two]⟩
  · rintro ⟨y, rfl | rfl | rfl, rfl⟩
    · exact ⟨0, by norm_num, by rw [conjGenP, decode_gensP_zero]⟩
    · exact ⟨1, by norm_num, by rw [conjGenP, decode_gensP_one]⟩
    · exact ⟨2, by norm_num, by rw [conjGenP, decode_gensP_two]⟩

@[expose] noncomputable def Pconj : Subgroup (ConjAct (Equiv.Perm (Fin 24))) :=
  (Ppair.map AutPerm.subtype).map
    (ConjAct.toConjAct : Equiv.Perm (Fin 24) ≃* ConjAct (Equiv.Perm (Fin 24))).toMonoidHom

theorem Pconj_eq_closure :
    Pconj = Subgroup.closure (conjGenP '' {k | k < gensP.size}) := by
  rw [Pconj, Pperm_eq_closure, conjGenP_image, MonoidHom.map_closure]

theorem orbA2Cert_ok : certOK aconj gensP sig2Arr orbA2Cert = true :=
  Certificates.certificate3052.1

theorem orbA3Cert_ok : certOK aconj gensP sig3Arr orbA3Cert = true :=
  Certificates.certificate3052.2.1

theorem orbA2Cert_size : orbA2Cert.pts.size = 1155 :=
  Certificates.certificate3052.2.2.1

theorem orbA3Cert_size : orbA3Cert.pts.size = 330 :=
  Certificates.certificate3052.2.2.2

theorem ncard_orbit_sig2 :
    (MulAction.orbit Pconj sig2).ncard = 1155
    := by
  rw [Pconj_eq_closure, ← decode_sig2Arr, ncard_orbit_of_certOK orbA2Cert_ok conjP_act,
    orbA2Cert_size]

theorem ncard_orbit_sig3 :
    (MulAction.orbit Pconj sig3).ncard = 330
    := by
  rw [Pconj_eq_closure, ← decode_sig3Arr, ncard_orbit_of_certOK orbA3Cert_ok conjP_act,
    orbA3Cert_size]

@[expose] noncomputable def toPconj : Ppair →* Pconj :=
  ((ConjAct.toConjAct : Equiv.Perm (Fin 24) ≃* ConjAct (Equiv.Perm (Fin 24))).toMonoidHom.comp
    (AutPerm.subtype.comp Ppair.subtype)).codRestrict Pconj fun p => ⟨_, ⟨p, p.2, rfl⟩, rfl⟩

theorem toPconj_surjective : Function.Surjective toPconj := by
  rintro ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩⟩
  exact ⟨⟨p, hp⟩, rfl⟩

theorem toPconj_smul (p : Ppair) (x : Equiv.Perm (Fin 24)) :
    toPconj p • x = ((p : AutPerm) : Equiv.Perm (Fin 24)) * x *
      ((p : AutPerm) : Equiv.Perm (Fin 24))⁻¹ :=
  ConjAct.toConjAct_smul _ _

theorem stabilizer_sig2_comap :
    (MulAction.stabilizer Pconj sig2).comap toPconj = FA2.subgroupOf Ppair := by
  ext p
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, FA2,
    Subgroup.mem_inf, mem_stabilizer_A2_iff, toPconj_smul]
  exact ⟨fun h => ⟨p.2, h⟩, fun h => h.2⟩

theorem stabilizer_sig3_comap :
    (MulAction.stabilizer Pconj sig3).comap toPconj = FA3.subgroupOf Ppair := by
  ext p
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, FA3,
    Subgroup.mem_inf, mem_stabilizer_A3_iff, toPconj_smul]
  exact ⟨fun h => ⟨p.2, h⟩, fun h => h.2⟩

theorem index_FA2 :
    (FA2.subgroupOf Ppair).index = 1155 := by
  rw [← stabilizer_sig2_comap, Subgroup.index_comap_of_surjective _ toPconj_surjective,
    MulAction.index_stabilizer, ncard_orbit_sig2]

theorem index_FA3 :
    (FA3.subgroupOf Ppair).index = 330 := by
  rw [← stabilizer_sig3_comap, Subgroup.index_comap_of_surjective _ toPconj_surjective,
    MulAction.index_stabilizer, ncard_orbit_sig3]

theorem natCard_FA2 :
    Nat.card FA2 = 768 := by
  have h := (FA2.subgroupOf Ppair).card_mul_index
  rw [index_FA2, natCard_Ppair,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe FA2_le_Ppair).toEquiv] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 1155) (h.trans (by norm_num))

theorem natCard_FA3 :
    Nat.card FA3 = 2688 := by
  have h := (FA3.subgroupOf Ppair).card_mul_index
  rw [index_FA3, natCard_Ppair,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe FA3_le_Ppair).toEquiv] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 330) (h.trans (by norm_num))

end CFSG.Monster.B.TwoA
