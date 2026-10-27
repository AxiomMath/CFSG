module

public import CFSG.Monster.B.TwoA.Census.MonoData
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.CodeAut.Bridge
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.ConjAct
public meta import CFSG.Monster.B.TwoA.Census.PermCert
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public meta import CFSG.Monster.B.TwoA.Census.MonoData
public import CFSG.Monster.B.TwoA.Census.PermClassesInputs
public import Certificates.Certificate3018
public import Certificates.Certificate3017

public section

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster.Code

theorem sylowCert_ok :
    certOK amul sylowGens idArr sylowCert = true :=
  Certificates.certificate3018.1
theorem cent1Cert_ok : certOK amul c1Gens idArr cent1Cert = true :=
  Certificates.certificate3018.2.1
theorem cent2Cert_ok : certOK amul c2Gens idArr cent2Cert = true :=
  Certificates.certificate3018.2.2.1
theorem orb1Cert_ok :
    certOK aconj abGens (seedArr.getD 1 #[]) orb1Cert = true :=
  Certificates.certificate3018.2.2.2.1
theorem orb2Cert_ok :
    certOK aconj abGens (seedArr.getD 2 #[]) orb2Cert = true :=
  Certificates.certificate3018.2.2.2.2.1

theorem sylowCert_size : sylowCert.pts.size = 1024 :=
  Certificates.certificate3018.2.2.2.2.2.1
theorem cent1Cert_size : cent1Cert.pts.size = 21504 :=
  Certificates.certificate3018.2.2.2.2.2.2.1
theorem cent2Cert_size : cent2Cert.pts.size = 7680 :=
  Certificates.certificate3018.2.2.2.2.2.2.2.1
theorem orb1Cert_size : orb1Cert.pts.size = 11385 :=
  Certificates.certificate3018.2.2.2.2.2.2.2.2.1
theorem orb2Cert_size : orb2Cert.pts.size = 31878 :=
  Certificates.certificate3018.2.2.2.2.2.2.2.2.2.1

theorem invIdx_sylow_length : (invIdx sylowCert).length = 191 :=
  Certificates.certificate3018.2.2.2.2.2.2.2.2.2.2.1

theorem invCovered_eq_true : invCovered = true :=
  Certificates.certificate3018.2.2.2.2.2.2.2.2.2.2.2.1

theorem getD_mem_of_lt {l : List (Array ℕ)} {k : ℕ} (hk : k < l.length) (d : Array ℕ) :
    l.getD k d ∈ l := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem getElem!_toArray_eq_getD (l : List (Array ℕ)) (k : ℕ) :
    l.toArray[k]! = l.getD k #[] := by
  by_cases hk : k < l.length
  · rw [getElem!_pos _ _ (by simpa using hk), List.getElem_toArray, List.getD_eq_getElem _ _ hk]
  · rw [getElem!_neg _ _ (by simpa using hk), List.getD_eq_default _ _ (by omega)]
    rfl

theorem sylowGens_perm : ∀ k < sylowGens.size, PermArr sylowGens[k]! = true := by
  intro k hk
  rw [sylowGens, getElem!_toArray_eq_getD]
  exact sylowGenArr_perm _ (getD_mem_of_lt (by simpa [sylowGens] using hk) _)

theorem c1Gens_perm : ∀ k < c1Gens.size, PermArr c1Gens[k]! = true := by
  intro k hk
  rw [c1Gens, getElem!_toArray_eq_getD]
  exact centGenArr_perm 1 (by norm_num) _
    (getD_mem_of_lt (by simpa [c1Gens, centGenArrs] using hk) _)

theorem c2Gens_perm : ∀ k < c2Gens.size, PermArr c2Gens[k]! = true := by
  intro k hk
  rw [c2Gens, getElem!_toArray_eq_getD]
  exact centGenArr_perm 2 (by norm_num) _
    (getD_mem_of_lt (by simpa [c2Gens, centGenArrs] using hk) _)

theorem abGens_perm : ∀ k < abGens.size, PermArr abGens[k]! = true := by
  intro k hk
  rw [abGens, getElem!_toArray_eq_getD]
  exact centGenArr_perm 0 (by norm_num) _
    (getD_mem_of_lt (by simpa [abGens, centGenArrs] using hk) _)

theorem image_gens_eq_range {l : List (Array ℕ)} {n : ℕ} (hn : l.length = n) :
    (fun k => decode l.toArray[k]!) '' {k | k < l.toArray.size} =
      Set.range fun k : Fin n => decode (l.getD k #[]) := by
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, List.size_toArray,
    getElem!_toArray_eq_getD]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hn ▸ hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, hn ▸ k.2, rfl⟩

theorem sylowGenArr_aut : ∀ a ∈ sylowGenArr, AutArr a :=
  Certificates.certificate3018.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem centGenArr_aut : ∀ j < 3, ∀ a ∈ centGenArrs j, AutArr a :=
  Certificates.certificate3018.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem seedArr_aut : ∀ a ∈ seedArr, AutArr a :=
  Certificates.certificate3018.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem sylowGen_mem (k : Fin 10) : sylowGen k ∈ AutPerm := by
  have hk : (k : ℕ) < sylowGenArr.length := by simp [sylowGenArr]
  exact mem_AutPerm_of_arr (sylowGenArr_perm _ (getD_mem_of_lt hk _))
    (sylowGenArr_aut _ (getD_mem_of_lt hk _))

theorem seedPerm_mem {j : ℕ} (hj : j < 3) : seedPerm j ∈ AutPerm :=
    by
  have hk : j < seedArr.length := by simpa [seedArr] using hj
  exact mem_AutPerm_of_arr (seedArr_perm _ (getD_mem_of_lt hk _))
    (seedArr_aut _ (getD_mem_of_lt hk _))

theorem centGen_mem {j k : ℕ} (hj : j < 3)
    (hk : k < (centGenArrs j).length) :
    centGen j k ∈ AutPerm :=
  mem_AutPerm_of_arr (centGenArr_perm j hj _ (getD_mem_of_lt hk _))
    (centGenArr_aut j hj _ (getD_mem_of_lt hk _))

@[expose] noncomputable def sylowSub : Subgroup (Equiv.Perm (Fin 24)) :=
  Subgroup.closure (Set.range fun k : Fin 10 => sylowGen k)

theorem sylowSub_eq :
    sylowSub = Subgroup.closure ((fun k => decode sylowGens[k]!) '' {k | k < sylowGens.size}) := by
  rw [sylowSub, sylowGens, image_gens_eq_range (n := 10) (by rfl)]
  rfl

theorem sylowSub_facts :
    Nat.card sylowSub = 1024 ∧
      ∀ x, x ∈ sylowSub ↔ ∃ i < sylowCert.pts.size, pt sylowCert i = x := by
  rw [sylowSub_eq, ← sylowCert_size]
  exact card_closure_of_certOK sylowGens_perm decode_idArr sylowCert_ok

theorem sylowSub_le : sylowSub ≤ AutPerm := by
  rw [sylowSub, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact sylowGen_mem k

theorem sylowSub_involutions :
    {x | x ∈ sylowSub ∧ x * x = 1 ∧ x ≠ 1} = pt sylowCert '' {i | i ∈ invIdx sylowCert} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hx, hxx, hx1⟩
    obtain ⟨i, hi, rfl⟩ := (sylowSub_facts.2 x).1 hx
    refine ⟨i, ?_, rfl⟩
    have hp := certOK_perm sylowCert_ok hi
    simp only [invIdx, List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq,
      bne_iff_ne, ne_eq]
    refine ⟨hi, ?_, ?_⟩
    · apply decode_inj (PermArr_amul hp hp) PermArr_idArr
      rw [decode_amul hp hp, decode_idArr]
      exact hxx
    · intro h
      apply hx1
      rw [pt, h, decode_idArr]
  · rintro ⟨i, hi, rfl⟩
    simp only [invIdx, List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq,
      bne_iff_ne, ne_eq] at hi
    obtain ⟨hi, hsq, hne⟩ := hi
    have hp := certOK_perm sylowCert_ok hi
    refine ⟨(sylowSub_facts.2 _).2 ⟨i, hi, rfl⟩, ?_, ?_⟩
    · rw [pt, ← decode_amul hp hp, hsq, decode_idArr]
    · intro h
      exact hne (decode_inj hp PermArr_idArr (by rw [← pt, h, decode_idArr]))

theorem invIdx_nodup : (invIdx sylowCert).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem ncard_sylowSub_involutions :
    {x | x ∈ sylowSub ∧ x * x = 1 ∧ x ≠ 1}.ncard = 191 := by
  rw [sylowSub_involutions, Set.InjOn.ncard_image]
  · rw [show {i | i ∈ invIdx sylowCert} = ((invIdx sylowCert).toFinset : Set ℕ) by ext; simp,
      Set.ncard_coe_finset, List.toFinset_card_of_nodup invIdx_nodup, invIdx_sylow_length]
  · intro i hi j hj e
    have hi' : i < sylowCert.pts.size := by
      have := hi
      simp only [Set.mem_ofPred_eq, invIdx, List.mem_filter, List.mem_range] at this
      exact this.1
    have hj' : j < sylowCert.pts.size := by
      have := hj
      simp only [Set.mem_ofPred_eq, invIdx, List.mem_filter, List.mem_range] at this
      exact this.1
    exact certOK_inj sylowCert_ok hi' hj' e

theorem factorization_card_AutPerm :
    (Nat.card AutPerm).factorization 2 = 10 := by
  rw [card_AutPerm, show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

@[expose] noncomputable def sylowP :
    Sylow 2 AutPerm :=
  Sylow.ofCard (sylowSub.subgroupOf AutPerm) (by
    rw [factorization_card_AutPerm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylowSub_le).toEquiv, sylowSub_facts.1]
    norm_num)

theorem coe_sylowP :
    (sylowP : Subgroup AutPerm) =
    sylowSub.subgroupOf AutPerm :=
  Sylow.coe_ofCard _ _

@[expose] noncomputable def conjGen (k : ℕ) : ConjAct (Equiv.Perm (Fin 24)) :=
  ConjAct.toConjAct (decode abGens[k]!)

theorem conj_act : ∀ k < abGens.size, ∀ a, PermArr a = true →
    decode (aconj abGens[k]! a) = conjGen k • decode a := by
  intro k hk a ha
  rw [decode_aconj (abGens_perm k hk) ha, conjGen, ConjAct.toConjAct_smul]

theorem decode_abGens_zero : decode abGens[0]! = bridgePA := by
  ext i
  rw [decode_apply (abGens_perm 0 (by decide)), bridgePA_image]
  revert i
  decide

theorem decode_abGens_one : decode abGens[1]! = bridgePB := by
  ext i
  rw [decode_apply (abGens_perm 1 (by decide)), bridgePB_image]
  revert i
  decide

theorem conjGen_image : conjGen '' {k | k < abGens.size} =
    (ConjAct.toConjAct : Equiv.Perm (Fin 24) ≃* ConjAct (Equiv.Perm (Fin 24))).toMonoidHom ''
      {bridgePA, bridgePB} := by
  have hs : abGens.size = 2 := rfl
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, hs, Set.mem_insert_iff, Set.mem_singleton_iff,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact ⟨bridgePA, Or.inl rfl, by rw [conjGen, decode_abGens_zero]⟩
    · exact ⟨bridgePB, Or.inr rfl, by rw [conjGen, decode_abGens_one]⟩
  · rintro ⟨y, rfl | rfl, rfl⟩
    · exact ⟨0, by norm_num, by rw [conjGen, decode_abGens_zero]⟩
    · exact ⟨1, by norm_num, by rw [conjGen, decode_abGens_one]⟩

theorem closure_conjGen :
    Subgroup.closure (conjGen '' {k | k < abGens.size}) =
    AutPerm.map
      (ConjAct.toConjAct : Equiv.Perm (Fin 24) ≃* ConjAct (Equiv.Perm (Fin 24))).toMonoidHom := by
  rw [conjGen_image, ← MonoidHom.map_closure, ← AutPerm_eq_closure]

@[expose] def conjClass (p : Equiv.Perm (Fin 24)) : Set (Equiv.Perm (Fin 24)) :=
  {x | ∃ g ∈ AutPerm, g * p * g⁻¹ = x}

theorem orbit_conjGen (p : Equiv.Perm (Fin 24)) :
    MulAction.orbit (Subgroup.closure (conjGen '' {k | k < abGens.size})) p = conjClass p := by
  rw [closure_conjGen]
  ext x
  simp only [MulAction.mem_orbit_iff, conjClass, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨_, g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, (ConjAct.toConjAct_smul g p).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨_, g, hg, rfl⟩, ConjAct.toConjAct_smul g p⟩

theorem conjClass_eq_image {j : ℕ} {c : TreeCert}
    (h : certOK aconj abGens (seedArr.getD j #[]) c = true) :
    conjClass (seedPerm j) = pt c '' {i | i < c.pts.size} := by
  rw [← orbit_conjGen, seedPerm]
  exact orbit_of_certOK (gensG := conjGen) h conj_act

theorem ncard_conjClass {j : ℕ} {c : TreeCert}
    (h : certOK aconj abGens (seedArr.getD j #[]) c = true) :
    (conjClass (seedPerm j)).ncard = c.pts.size := by
  rw [← orbit_conjGen, seedPerm]
  exact ncard_orbit_of_certOK (gensG := conjGen) h conj_act

theorem conjClass_conj {p x g : Equiv.Perm (Fin 24)} (hg : g ∈ AutPerm) (hx : x ∈ conjClass p) :
    g * x * g⁻¹ ∈ conjClass p := by
  obtain ⟨h, hh, rfl⟩ := hx
  exact ⟨g * h, AutPerm.mul_mem hg hh, by group⟩

@[expose] noncomputable def fixCount (x : Equiv.Perm (Fin 24)) : ℕ :=
  (Finset.univ.filter fun i => x i = i).card

theorem fixCount_conj (g x : Equiv.Perm (Fin 24)) : fixCount (g * x * g⁻¹) = fixCount x := by
  unfold fixCount
  conv_rhs => rw [← Finset.card_map g.toEmbedding]
  congr 1
  ext i
  rw [Finset.mem_filter, Finset.mem_map]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.toEmbedding_apply,
    Equiv.Perm.mul_apply]
  constructor
  · intro h
    refine ⟨g⁻¹ i, ?_, by simp⟩
    have := congrArg (fun y => g⁻¹ y) h
    simpa using this
  · rintro ⟨a, ha, rfl⟩
    simp [ha]

theorem fixCount_seed_one : fixCount (seedPerm 1) = 8 := by
  rw [fixCount, seedPerm, coe_decode (seedArr_perm _ (getD_mem_of_lt (by decide) _))]
  decide

theorem fixCount_seed_two : fixCount (seedPerm 2) = 0 := by
  rw [fixCount, seedPerm, coe_decode (seedArr_perm _ (getD_mem_of_lt (by decide) _))]
  decide

theorem fixCount_of_mem_conjClass {p x : Equiv.Perm (Fin 24)} (hx : x ∈ conjClass p) :
    fixCount x = fixCount p := by
  obtain ⟨g, -, rfl⟩ := hx
  exact fixCount_conj g p

theorem invCovered_spec {i : ℕ}
    (hi : i ∈ invIdx sylowCert) :
    pt sylowCert i ∈ conjClass (seedPerm 1) ∪ conjClass (seedPerm 2) := by
  have h := invCovered_eq_true
  simp only [invCovered, List.all_eq_true, Bool.or_eq_true] at h
  rcases h i hi with h1 | h2
  · left
    rw [conjClass_eq_image orb1Cert_ok]
    split at h1
    · rename_i j _
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
      exact ⟨j, h1.1, by rw [pt, pt, h1.2]⟩
    · exact absurd h1 (by decide)
  · right
    rw [conjClass_eq_image orb2Cert_ok]
    split at h2
    · rename_i j _
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
      exact ⟨j, h2.1, by rw [pt, pt, h2.2]⟩
    · exact absurd h2 (by decide)

theorem involution_mem_conjClass
    {t : Equiv.Perm (Fin 24)}
    (ht : t ∈ AutPerm) (htt : t * t = 1)
    (ht1 : t ≠ 1) : t ∈ conjClass (seedPerm 1) ∪ conjClass (seedPerm 2) := by
  set t' : AutPerm := ⟨t, ht⟩
  have hp : IsPGroup 2 (Subgroup.zpowers t') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa [sq] using htt)
    · exact fun h => ht1 (congrArg Subtype.val h)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq AutPerm Q sylowP
  have hmem : g * t' * g⁻¹ ∈ (sylowP : Subgroup AutPerm) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    have e : MulAut.conj g • t' = g * t' * g⁻¹ := rfl
    rw [← e]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers t'))
  rw [coe_sylowP, Subgroup.mem_subgroupOf] at hmem
  have hx : ((g : Equiv.Perm (Fin 24)) * t * (g : Equiv.Perm (Fin 24))⁻¹) ∈
      {x | x ∈ sylowSub ∧ x * x = 1 ∧ x ≠ 1} := by
    refine ⟨by simpa using hmem, ?_, ?_⟩
    · calc (g : Equiv.Perm (Fin 24)) * t * (g : Equiv.Perm (Fin 24))⁻¹ *
            ((g : Equiv.Perm (Fin 24)) * t * (g : Equiv.Perm (Fin 24))⁻¹)
          = (g : Equiv.Perm (Fin 24)) * (t * t) * (g : Equiv.Perm (Fin 24))⁻¹ := by group
        _ = 1 := by rw [htt]; group
    · intro h
      apply ht1
      calc t = (g : Equiv.Perm (Fin 24))⁻¹ * ((g : Equiv.Perm (Fin 24)) * t *
            (g : Equiv.Perm (Fin 24))⁻¹) * (g : Equiv.Perm (Fin 24)) := by group
        _ = 1 := by rw [h]; group
  rw [sylowSub_involutions] at hx
  obtain ⟨i, hi, e⟩ := hx
  have hc := invCovered_spec hi
  rw [e] at hc
  have hginv : (g : Equiv.Perm (Fin 24))⁻¹ ∈ AutPerm := AutPerm.inv_mem g.2
  have ht' : t = (g : Equiv.Perm (Fin 24))⁻¹ * ((g : Equiv.Perm (Fin 24)) * t *
      (g : Equiv.Perm (Fin 24))⁻¹) * ((g : Equiv.Perm (Fin 24))⁻¹)⁻¹ := by group
  rcases hc with hc | hc
  · exact Or.inl (ht' ▸ conjClass_conj hginv hc)
  · exact Or.inr (ht' ▸ conjClass_conj hginv hc)

@[expose] noncomputable def autConj : Subgroup (ConjAct (Equiv.Perm (Fin 24))) :=
  AutPerm.map (ConjAct.toConjAct : Equiv.Perm (Fin 24) ≃* ConjAct (Equiv.Perm (Fin 24))).toMonoidHom

theorem card_autConj : Nat.card autConj = 244823040 := by
  rw [autConj, Subgroup.card_map_of_injective (MulEquiv.injective _), card_AutPerm]

theorem mem_autConj {x : ConjAct (Equiv.Perm (Fin 24))} :
    x ∈ autConj ↔ ConjAct.ofConjAct x ∈ AutPerm := by
  rw [autConj, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    simpa using hg
  · intro h
    exact ⟨ConjAct.ofConjAct x, h, by simp⟩

noncomputable def stabEquiv (p : Equiv.Perm (Fin 24)) :
    MulAction.stabilizer autConj p ≃ (AutPerm ⊓ Subgroup.centralizer {p} : Subgroup _) where
  toFun h := ⟨ConjAct.ofConjAct h.1.1, by
    have hx := mem_autConj.1 h.1.2
    have hfix : h.1.1 • p = p := h.2
    rw [ConjAct.smul_def] at hfix
    refine Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have e : ConjAct.ofConjAct h.1.1 * p =
        ConjAct.ofConjAct h.1.1 * p * (ConjAct.ofConjAct h.1.1)⁻¹ * ConjAct.ofConjAct h.1.1 := by
      group
    rw [e, hfix]⟩
  invFun g := ⟨⟨ConjAct.toConjAct (g : Equiv.Perm (Fin 24)),
      mem_autConj.2 (by simpa using (Subgroup.mem_inf.1 g.2).1)⟩, by
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2
    show ConjAct.toConjAct (g : Equiv.Perm (Fin 24)) • p = p
    rw [ConjAct.toConjAct_smul]
    calc (g : Equiv.Perm (Fin 24)) * p * (g : Equiv.Perm (Fin 24))⁻¹ =
          p * g * (g : Equiv.Perm (Fin 24))⁻¹ := by rw [hc]
      _ = p := by group⟩
  left_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv g := by
    apply Subtype.ext
    simp

theorem card_centralizer_mul {j : ℕ} {c : TreeCert}
    (h : certOK aconj abGens (seedArr.getD j #[]) c = true) :
    Nat.card (AutPerm ⊓ Subgroup.centralizer {seedPerm j} : Subgroup _) * c.pts.size =
      244823040 := by
  have horb : (MulAction.orbit autConj (seedPerm j)).ncard = c.pts.size := by
    have := ncard_conjClass h
    rw [← orbit_conjGen, closure_conjGen] at this
    exact this
  rw [← Nat.card_congr (stabEquiv (seedPerm j)), ← horb, ← MulAction.index_stabilizer,
    Subgroup.card_mul_index, card_autConj]

theorem card_centralizer_one :
    Nat.card (AutPerm ⊓ Subgroup.centralizer {seedPerm 1} : Subgroup _) = 21504 := by
  have := card_centralizer_mul orb1Cert_ok
  rw [orb1Cert_size] at this
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (this.trans (by norm_num))

theorem card_centralizer_two :
    Nat.card (AutPerm ⊓ Subgroup.centralizer {seedPerm 2} : Subgroup _) = 7680 := by
  have := card_centralizer_mul orb2Cert_ok
  rw [orb2Cert_size] at this
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (this.trans (by norm_num))

theorem centGenArr_comm : ∀ j ∈ [1, 2], ∀ a ∈ centGenArrs j,
    amul a (seedArr.getD j #[]) = amul (seedArr.getD j #[]) a :=
  Certificates.certificate3018.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem centGen_comm {j : ℕ} (hj : j = 1 ∨ j = 2) {k : ℕ}
    (hk : k < (centGenArrs j).length) :
    centGen j k * seedPerm j = seedPerm j * centGen j k := by
  have hj' : j < 3 := by omega
  have hmem := getD_mem_of_lt hk #[]
  have ha := centGenArr_perm j hj' _ hmem
  have hs := seedArr_perm _ (getD_mem_of_lt (show j < seedArr.length by simp [seedArr]; omega) #[])
  rw [centGen, seedPerm, ← decode_amul ha hs, ← decode_amul hs ha,
    centGenArr_comm j (by simp; omega) _ hmem]

theorem closure_centGen_eq {j : ℕ} (hj : j = 1 ∨ j = 2) {gens : Array (Array ℕ)}
    (hg : gens = (centGenArrs j).toArray) :
    Subgroup.closure (Set.range fun k : Fin 5 => centGen j k) =
      Subgroup.closure ((fun k => decode gens[k]!) '' {k | k < gens.size}) := by
  subst hg
  rw [image_gens_eq_range (n := 5) (by rcases hj with rfl | rfl <;> rfl)]
  rfl

theorem centGenArrs_length {j : ℕ} (hj : j = 1 ∨ j = 2) : (centGenArrs j).length = 5 := by
  rcases hj with rfl | rfl <;> rfl

theorem centGen_mem_inf {j : ℕ} (hj : j = 1 ∨ j = 2) (k : Fin 5) :
    centGen j k ∈ AutPerm ⊓ Subgroup.centralizer {seedPerm j} := by
  have hk : (k : ℕ) < (centGenArrs j).length := by
    rw [centGenArrs_length hj]
    exact k.2
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨centGen_mem (by omega) hk, centGen_comm hj hk⟩

theorem closure_centGen_le {j : ℕ} (hj : j = 1 ∨ j = 2) :
    Subgroup.closure (Set.range fun k : Fin 5 => centGen j k) ≤
      AutPerm ⊓ Subgroup.centralizer {seedPerm j} := by
  rw [Subgroup.closure_le, Set.range_subset_iff]
  intro k
  rw [SetLike.mem_coe]
  exact centGen_mem_inf hj k

theorem closure_centGen_one :
    Subgroup.closure (Set.range fun k : Fin 5 => centGen 1 k) =
      AutPerm ⊓ Subgroup.centralizer {seedPerm 1} := by
  have hcard : Nat.card (Subgroup.closure (Set.range fun k : Fin 5 => centGen 1 k)) = 21504 := by
    rw [closure_centGen_eq (Or.inl rfl) (gens := c1Gens) rfl, ← cent1Cert_size]
    exact (card_closure_of_certOK c1Gens_perm decode_idArr cent1Cert_ok).1
  exact Subgroup.eq_of_le_of_card_ge (closure_centGen_le (Or.inl rfl))
    (by rw [hcard, card_centralizer_one])

theorem closure_centGen_two :
    Subgroup.closure (Set.range fun k : Fin 5 => centGen 2 k) =
      AutPerm ⊓ Subgroup.centralizer {seedPerm 2} := by
  have hcard : Nat.card (Subgroup.closure (Set.range fun k : Fin 5 => centGen 2 k)) = 7680 := by
    rw [closure_centGen_eq (Or.inr rfl) (gens := c2Gens) rfl, ← cent2Cert_size]
    exact (card_closure_of_certOK c2Gens_perm decode_idArr cent2Cert_ok).1
  exact Subgroup.eq_of_le_of_card_ge (closure_centGen_le (Or.inr rfl))
    (by rw [hcard, card_centralizer_two])

theorem seedArr_sq : ∀ j ∈ [1, 2], amul (seedArr.getD j #[]) (seedArr.getD j #[]) = idArr := by
  decide +kernel

theorem seedPerm_sq {j : ℕ} (hj : j = 1 ∨ j = 2) : seedPerm j * seedPerm j = 1 := by
  have hs := seedArr_perm _ (getD_mem_of_lt (show j < seedArr.length by simp [seedArr]; omega) #[])
  rw [seedPerm, ← decode_amul hs hs, seedArr_sq j (by rcases hj with rfl | rfl <;> simp),
    decode_idArr]

theorem fixCount_one : fixCount 1 = 24 := by
  simp [fixCount]

theorem seedPerm_ne_one {j : ℕ} (hj : j = 1 ∨ j = 2) : seedPerm j ≠ 1 := by
  intro h
  rcases hj with rfl | rfl
  · have := fixCount_seed_one
    rw [h, fixCount_one] at this
    omega
  · have := fixCount_seed_two
    rw [h, fixCount_one] at this
    omega

theorem conj_mem_involutions {g p : Equiv.Perm (Fin 24)} (hg : g ∈ AutPerm) (hp : p ∈ AutPerm)
    (hpp : p * p = 1) (hp1 : p ≠ 1) :
    g * p * g⁻¹ ∈ {t | t ∈ AutPerm ∧ t * t = 1 ∧ t ≠ 1} := by
  refine ⟨AutPerm.mul_mem (AutPerm.mul_mem hg hp) (AutPerm.inv_mem hg), ?_, ?_⟩
  · calc g * p * g⁻¹ * (g * p * g⁻¹) = g * (p * p) * g⁻¹ := by group
      _ = 1 := by rw [hpp]; group
  · intro h
    apply hp1
    calc p = g⁻¹ * (g * p * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group

theorem centGen_zero_zero : centGen 0 0 = bridgePA := by
  rw [centGen, show centGenArrs 0 = centGenArr0 from rfl, ← getElem!_toArray_eq_getD]
  exact decode_abGens_zero

theorem centGen_zero_one : centGen 0 1 = bridgePB := by
  rw [centGen, show centGenArrs 0 = centGenArr0 from rfl, ← getElem!_toArray_eq_getD]
  exact decode_abGens_one

theorem code_permutation_involution_classes :
    ((∀ k : Fin 10, sylowGen k ∈ AutPerm) ∧ sylowSub ≤ AutPerm ∧ Nat.card sylowSub = 1024 ∧
      (∃ P : Sylow 2 AutPerm, (P : Subgroup AutPerm) = sylowSub.subgroupOf AutPerm) ∧
      {x | x ∈ sylowSub ∧ x * x = 1 ∧ x ≠ 1}.ncard = 191) ∧
    (∀ j, j = 1 ∨ j = 2 → seedPerm j ∈ AutPerm ∧ seedPerm j * seedPerm j = 1 ∧ seedPerm j ≠ 1) ∧
    {t | t ∈ AutPerm ∧ t * t = 1 ∧ t ≠ 1} = conjClass (seedPerm 1) ∪ conjClass (seedPerm 2) ∧
    Disjoint (conjClass (seedPerm 1)) (conjClass (seedPerm 2)) ∧
    (conjClass (seedPerm 1)).ncard = 11385 ∧ (conjClass (seedPerm 2)).ncard = 31878 ∧
    fixCount (seedPerm 1) = 8 ∧ fixCount (seedPerm 2) = 0 ∧
    ((centGenArrs 1).length = 5 ∧
      Subgroup.closure (Set.range fun k : Fin 5 => centGen 1 k) =
        AutPerm ⊓ Subgroup.centralizer {seedPerm 1} ∧
      Nat.card (AutPerm ⊓ Subgroup.centralizer {seedPerm 1} : Subgroup _) = 21504) ∧
    ((centGenArrs 2).length = 5 ∧
      Subgroup.closure (Set.range fun k : Fin 5 => centGen 2 k) =
        AutPerm ⊓ Subgroup.centralizer {seedPerm 2} ∧
      Nat.card (AutPerm ⊓ Subgroup.centralizer {seedPerm 2} : Subgroup _) = 7680) ∧
    ((centGenArrs 0).length = 2 ∧ centGen 0 0 = bridgePA ∧ centGen 0 1 = bridgePB ∧
      AutPerm = Subgroup.closure {bridgePA, bridgePB}) := by
  have hinv : ∀ j, j = 1 ∨ j = 2 →
      seedPerm j ∈ AutPerm ∧ seedPerm j * seedPerm j = 1 ∧ seedPerm j ≠ 1 := fun j hj =>
    ⟨seedPerm_mem (by omega), seedPerm_sq hj, seedPerm_ne_one hj⟩
  refine ⟨⟨sylowGen_mem, sylowSub_le, sylowSub_facts.1, ⟨sylowP, coe_sylowP⟩,
    ncard_sylowSub_involutions⟩, hinv, ?_, ?_, ?_, ?_, fixCount_seed_one, fixCount_seed_two,
    ⟨centGenArrs_length (Or.inl rfl), closure_centGen_one, card_centralizer_one⟩,
    ⟨centGenArrs_length (Or.inr rfl), closure_centGen_two, card_centralizer_two⟩,
    ⟨rfl, centGen_zero_zero, centGen_zero_one, AutPerm_eq_closure⟩⟩
  · ext t
    constructor
    · rintro ⟨ht, htt, ht1⟩
      exact involution_mem_conjClass ht htt ht1
    · rintro (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩)
      · obtain ⟨h1, h2, h3⟩ := hinv 1 (Or.inl rfl)
        exact conj_mem_involutions hg h1 h2 h3
      · obtain ⟨h1, h2, h3⟩ := hinv 2 (Or.inr rfl)
        exact conj_mem_involutions hg h1 h2 h3
  · rw [Set.disjoint_left]
    intro x h1 h2
    have := (fixCount_of_mem_conjClass h1).symm.trans (fixCount_of_mem_conjClass h2)
    rw [fixCount_seed_one, fixCount_seed_two] at this
    omega
  · rw [ncard_conjClass orb1Cert_ok, orb1Cert_size]
  · rw [ncard_conjClass orb2Cert_ok, orb2Cert_size]

end CFSG.Monster.B.TwoA.Census
