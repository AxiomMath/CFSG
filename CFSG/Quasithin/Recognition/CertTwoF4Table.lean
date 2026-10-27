module

public import CFSG.Quasithin.Recognition.CertTwoF4Lattice
public import CFSG.Quasithin.Recognition.CertTitsVertex

public noncomputable section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits CFSG.LieType.BorelTits

theorem extSub_mono {M : Type*} [Group M] {A B : Subgroup M} {q : M}
    {hqA : q ∈ Subgroup.normalizer (A : Set M)} {hqA2 : q * q ∈ A}
    {hqB : q ∈ Subgroup.normalizer (B : Set M)} {hqB2 : q * q ∈ B} (h : A ≤ B) :
    extSub A q hqA hqA2 ≤ extSub B q hqB hqB2 :=
  fun _ hx => hx.imp (fun h1 => h h1) (fun h1 => h h1)

theorem not_mem_D_of_mem_coset
    {A : Subgroup (Equiv.Perm (Fin 1755))} (hAD : A ≤ titsD)
    {x : Equiv.Perm (Fin 1755)} (hx : x * tπ⁻¹ ∈ A) : x ∉ titsD := fun hxD => tπ_not_mem_D (by
  have h := titsD.mul_mem (titsD.inv_mem hxD) (hAD hx)
  simpa using titsD.inv_mem h)

theorem mem_of_mem_extSub_of_mem_D
    {A : Subgroup (Equiv.Perm (Fin 1755))} (hAD : A ≤ titsD)
    {hq : tπ ∈ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 1755)))} {hq2 : tπ * tπ ∈ A}
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ extSub A tπ hq hq2) (hxD : x ∈ titsD) : x ∈ A :=
  hx.elim id fun h => absurd hxD (not_mem_D_of_mem_coset hAD h)

@[expose] def twoF4S
    : Subgroup (Equiv.Perm (Fin 1755)) := extSub titsS tπ tπ_norm_S tπ_sq_S

@[expose] def twoF4H
    : Subgroup (Equiv.Perm (Fin 1755)) := extSub titsH tπ tπ_norm_H tπ_sq_H

@[expose] def twoF4N
    : Subgroup (Equiv.Perm (Fin 1755)) := extSub titsN tπ tπ_norm_N tπ_sq_N

@[expose] def twoF4P
    : Subgroup (Equiv.Perm (Fin 1755)) := extSub titsJ tπ tπ_norm_J tπ_sq_J

theorem twoF4S_le_twoF4H
    : twoF4S ≤ twoF4H := extSub_mono titsS_le_titsH

theorem twoF4S_le_twoF4N
    : twoF4S ≤ twoF4N := extSub_mono titsS_le_titsN

theorem twoF4P_le_twoF4H
    : twoF4P ≤ twoF4H := extSub_mono titsJ_le_titsH

theorem twoF4H_inf_twoF4N
    : twoF4H ⊓ twoF4N = twoF4S := by
  apply le_antisymm
  · rintro x ⟨hxH, hxN⟩
    by_cases hxD : x ∈ titsD
    · have h : x ∈ titsH ⊓ titsN :=
        ⟨mem_of_mem_extSub_of_mem_D titsH_le_titsD hxH hxD,
          mem_of_mem_extSub_of_mem_D titsN_le_titsD hxN hxD⟩
      rw [titsH_inf_titsN] at h
      exact le_extSub h
    · have h1 : x * tπ⁻¹ ∈ titsH := hxH.elim (fun h => absurd (titsH_le_titsD h) hxD) id
      have h2 : x * tπ⁻¹ ∈ titsN := hxN.elim (fun h => absurd (titsN_le_titsD h) hxD) id
      have h : x * tπ⁻¹ ∈ titsH ⊓ titsN := ⟨h1, h2⟩
      rw [titsH_inf_titsN] at h
      exact Or.inr h
  · exact le_inf twoF4S_le_twoF4H twoF4S_le_twoF4N

theorem titsH_le_normalizer_titsJ
    :
    titsH ≤ Subgroup.normalizer (titsJ : Set (Equiv.Perm (Fin 1755))) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer titsJ_le_titsH).1
    AT_Tits_intrinsic_local_pair.2.2.2.2.2.2.1

theorem titsJ_isPGroup
    : IsPGroup 2 titsJ :=
  IsPGroup.of_card (n := 9) (by rw [titsQJ_facts.2.2.2]; norm_num)

theorem jGen_comm_pi
    (k : Fin 3) : jGen k * tπ * (jGen k)⁻¹ * tπ⁻¹ ∈ titsJ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgi, -⟩ := jModel_check
  obtain ⟨-, -, -, -, -, -, -, hgc, -⟩ := twoF4Pi_check
  have hr := rep_compA (rep_compA (rep_compA (jGen_rep k) tπ_rep)
    (rep_inv_of_isInvA (jGen_rep k) (allLt_spec hgi k.2))) tπ_inv_rep
  exact mem_titsJ_of_sift hr (allLt_spec hgc k.2)

theorem exists_jGen_of_mem_gens {t : Equiv.Perm (Fin 1755)}
    (ht : ∃ w ∈ titsHWords, wordIn 13 titsT w = t) : ∃ k : Fin 3, jGen k = t := by
  obtain ⟨w, hw, rfl⟩ := ht
  rw [titsHWords_eq] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact ⟨0, by simp [jGen, titsHWords_eq]⟩
  · exact ⟨1, by simp [jGen, titsHWords_eq]⟩
  · exact ⟨2, by simp [jGen, titsHWords_eq]⟩

@[expose] def commPiSub
    : Subgroup (Equiv.Perm (Fin 1755)) where
  carrier := {h | h ∈ titsH ∧ h * tπ * h⁻¹ * tπ⁻¹ ∈ titsJ}
  mul_mem' := by
    rintro x y ⟨hxH, hxJ⟩ ⟨hyH, hyJ⟩
    refine ⟨titsH.mul_mem hxH hyH, ?_⟩
    have h1 : x * y * tπ * (x * y)⁻¹ * tπ⁻¹ =
        (x * (y * tπ * y⁻¹ * tπ⁻¹) * x⁻¹) * (x * tπ * x⁻¹ * tπ⁻¹) := by group
    rw [h1]
    exact titsJ.mul_mem ((Subgroup.mem_normalizer_iff.1 (titsH_le_normalizer_titsJ hxH) _).1 hyJ) hxJ
  one_mem' := ⟨titsH.one_mem, by simp⟩
  inv_mem' := by
    rintro x ⟨hxH, hxJ⟩
    refine ⟨titsH.inv_mem hxH, ?_⟩
    have h1 : x⁻¹ * tπ * x⁻¹⁻¹ * tπ⁻¹ = x⁻¹ * (x * tπ * x⁻¹ * tπ⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.1 (titsH_le_normalizer_titsJ (titsH.inv_mem hxH)) _).1
      (titsJ.inv_mem hxJ)

theorem titsH_le_commPiSub
    : titsH ≤ commPiSub := by
  unfold titsH titsWordGroup
  rw [Subgroup.closure_le]
  intro t ht
  obtain ⟨k, rfl⟩ := exists_jGen_of_mem_gens ht
  exact ⟨jGen_mem k, jGen_comm_pi k⟩

theorem comm_pi_mem_J
    {h : Equiv.Perm (Fin 1755)} (hh : h ∈ titsH) :
    h * tπ * h⁻¹ * tπ⁻¹ ∈ titsJ := (titsH_le_commPiSub hh).2

theorem titsH_le_normalizer_twoF4P
    :
    titsH ≤ Subgroup.normalizer (twoF4P : Set (Equiv.Perm (Fin 1755))) := fun h hh => by
  apply mem_normalizer_of_forall_conj_mem_f4
  intro p hp
  rcases hp with hp | hp
  · exact Or.inl ((Subgroup.mem_normalizer_iff.1 (titsH_le_normalizer_titsJ hh) p).1 hp)
  · refine Or.inr ?_
    have e : h * p * h⁻¹ * tπ⁻¹ = (h * (p * tπ⁻¹) * h⁻¹) * (h * tπ * h⁻¹ * tπ⁻¹) := by group
    rw [e]
    exact titsJ.mul_mem ((Subgroup.mem_normalizer_iff.1 (titsH_le_normalizer_titsJ hh) _).1 hp)
      (comm_pi_mem_J hh)

theorem tπ_norm_twoF4P
    : tπ ∈ Subgroup.normalizer (twoF4P : Set (Equiv.Perm (Fin 1755))) := by
  apply mem_normalizer_of_forall_conj_mem_f4
  intro p hp
  rcases hp with hp | hp
  · exact Or.inl ((Subgroup.mem_normalizer_iff.1 tπ_norm_J p).1 hp)
  · refine Or.inr ?_
    have e : tπ * p * tπ⁻¹ * tπ⁻¹ = tπ * (p * tπ⁻¹) * tπ⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 tπ_norm_J _).1 hp

theorem twoF4H_le_normalizer_twoF4P
    :
    twoF4H ≤ Subgroup.normalizer (twoF4P : Set (Equiv.Perm (Fin 1755))) := by
  intro x hx
  rcases hx with hx | hx
  · exact titsH_le_normalizer_twoF4P hx
  · have h := Subgroup.mul_mem _ (titsH_le_normalizer_twoF4P hx) tπ_norm_twoF4P
    simpa using h

theorem twoF4P_isPGroup
    : IsPGroup 2 twoF4P := isPGroup_extSub titsJ_isPGroup

theorem twoF4P_le_pCoreOf
    : twoF4P ≤ pCoreOf 2 twoF4H :=
  le_pCoreOf_of_le_normalizer 2 twoF4P_le_twoF4H twoF4H_le_normalizer_twoF4P twoF4P_isPGroup

theorem pCoreOf_twoF4H_le
    : pCoreOf 2 twoF4H ≤ twoF4P := by
  have hπQ : tπ ∈ pCoreOf 2 twoF4H := twoF4P_le_pCoreOf q_mem_extSub
  have hn : ∀ h ∈ titsH,
      h ∈ Subgroup.normalizer ((pCoreOf 2 twoF4H ⊓ titsH : Subgroup (Equiv.Perm (Fin 1755))) :
        Set (Equiv.Perm (Fin 1755))) := fun h hh => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1
      (le_normalizer_pCoreOf 2 twoF4H (le_extSub hh)) x
    constructor
    · rintro ⟨hxQ, hxH⟩
      exact ⟨h1.1 hxQ, titsH.mul_mem (titsH.mul_mem hh hxH) (titsH.inv_mem hh)⟩
    · rintro ⟨hxQ, hxH⟩
      refine ⟨h1.2 hxQ, ?_⟩
      have := titsH.mul_mem (titsH.mul_mem (titsH.inv_mem hh) hxH) hh
      simpa [mul_assoc] using this
  have hQH : pCoreOf 2 twoF4H ⊓ titsH ≤ titsJ := by
    rw [← pCoreOf_titsH]
    exact le_pCoreOf_of_le_normalizer 2 inf_le_right hn
      ((pCoreOf_isPGroup 2 twoF4H).to_le inf_le_left)
  intro x hx
  rcases pCoreOf_le 2 twoF4H hx with hxH | hxH
  · exact le_extSub (hQH ⟨hx, hxH⟩)
  · have h : x * tπ⁻¹ ∈ pCoreOf 2 twoF4H ⊓ titsH :=
      ⟨(pCoreOf 2 twoF4H).mul_mem hx ((pCoreOf 2 twoF4H).inv_mem hπQ), hxH⟩
    exact Or.inr (hQH h)

theorem pCoreOf_twoF4H
    : pCoreOf 2 twoF4H = twoF4P :=
  le_antisymm pCoreOf_twoF4H_le twoF4P_le_pCoreOf

theorem titsQS_baseCount
    : titsQS.baseCount = 5 := by
  show (finList 1755 titsSBase).length = 5
  simp [finList, titsCentral_check.1]

theorem mul_pi_not_mem_centralizer_S
    {y : Equiv.Perm (Fin 1755)} (hy : y ∈ titsS) :
    y * tπ ∉ Subgroup.centralizer (titsS : Set (Equiv.Perm (Fin 1755))) := by
  intro hc
  obtain ⟨-, -, -, -, -, -, -, -, hall, -⟩ := twoF4Pi_check
  have hyS : y ∈ titsQS.originalSubgroup := by
    rw [titsQS_facts.2.2.1]
    exact hy
  obtain ⟨a, ha, hp⟩ := all5_spec titsS_chainArrays (by norm_num : 0 < 4)
    titsLocalChains_check.2.1 titsQS_baseCount hall hyS
  have hcomm := (commutesAll_wordGroup_iff (hk := by rw [titsSArrs_size]; norm_num)
    (hb := by decide) (s := 9) (D := titsSDerivations)
    titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 titsQS_facts.2.1
    (rep_compA ha tπ_rep)).2 hc
  simp only [hcomm, Bool.not_true] at hp
  exact Bool.false_ne_true hp

theorem tπ_comm_titsZ
    : tπ * titsZ = titsZ * tπ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hz, -⟩ := twoF4Pi_check
  have h := eq_of_eqA (rep_compA (rep_compA tπ_rep titsZ_rep) tπ_inv_rep) titsZ_rep hz
  calc tπ * titsZ = tπ * titsZ * tπ⁻¹ * tπ := by group
    _ = titsZ * tπ := by rw [h]

theorem titsZ_mem_centralizer_twoF4S
    :
    titsZ ∈ Subgroup.centralizer (twoF4S : Set (Equiv.Perm (Fin 1755))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  rcases hs with hs | hs
  · exact Subgroup.mem_centralizer_iff.1 titsZ_mem_centralizer_S s hs
  · have h1 := Subgroup.mem_centralizer_iff.1 titsZ_mem_centralizer_S _ hs
    calc s * titsZ = (s * tπ⁻¹) * (tπ * titsZ) := by group
      _ = (s * tπ⁻¹) * (titsZ * tπ) := by rw [tπ_comm_titsZ]
      _ = ((s * tπ⁻¹) * titsZ) * tπ := by group
      _ = (titsZ * (s * tπ⁻¹)) * tπ := by rw [h1]
      _ = titsZ * s := by group

theorem mem_omegaOneCenter_twoF4HN_iff
    (x : Equiv.Perm (Fin 1755)) :
    x ∈ quasithinOmegaOneCenter (twoF4H ⊓ twoF4N) ↔ x = 1 ∨ x = titsZ := by
  rw [twoF4H_inf_twoF4N, mem_quasithinOmegaOneCenter_iff]
  constructor
  · rintro ⟨hxS, hxc, -⟩
    have hxc' : x ∈ Subgroup.centralizer (titsS : Set (Equiv.Perm (Fin 1755))) :=
      Subgroup.mem_centralizer_iff.2 fun s hs =>
        Subgroup.mem_centralizer_iff.1 hxc s (le_extSub hs)
    rcases hxS with hxS | hxS
    · have hmem : x ∈ ((Subgroup.center titsS).map titsS.subtype :
          Set (Equiv.Perm (Fin 1755))) := by
        refine ⟨⟨x, hxS⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc' g.1 g.2)
      rw [titsS_center] at hmem
      exact hmem
    · exfalso
      have h := mul_pi_not_mem_centralizer_S hxS
      rw [inv_mul_cancel_right] at h
      exact h hxc'
  · rintro (rfl | rfl)
    · exact ⟨one_mem _, one_mem _, one_pow 2⟩
    · exact ⟨le_extSub titsZ_mem_titsS, titsZ_mem_centralizer_twoF4S, by
        rw [pow_two]; exact titsZ_mul_self⟩

theorem pPel_get (i : Fin 1024) : pPel[(i : ℕ)]! =
    if (i : ℕ) < 512 then jPel[(i : ℕ)]! else compA 1755 jPel[(i : ℕ) - 512]! titsPiArr := by
  unfold pPel
  rw [getElem!_pos _ _ (by simp)]
  simp [Array.getElem_ofFn]

@[expose] def pEl (i : Fin 1024) : Equiv.Perm (Fin 1755) := permOfArr 1755 pPel[(i : ℕ)]!

@[expose] def pElAlt (i : Fin 1024) : Equiv.Perm (Fin 1755) :=
  if h : (i : ℕ) < 512 then jEl ⟨i, h⟩ else jEl ⟨(i : ℕ) - 512, by have := i.2; omega⟩ * tπ

theorem pElAlt_rep
    (i : Fin 1024) : Rep 1755 pPel[(i : ℕ)]! (pElAlt i) := by
  rw [pPel_get]
  unfold pElAlt
  by_cases h : (i : ℕ) < 512
  · simp only [h, dite_true, ite_true]
    exact jEl_rep ⟨i, h⟩
  · simp only [h, dite_false, ite_false]
    exact rep_compA (jEl_rep ⟨(i : ℕ) - 512, by have := i.2; omega⟩) tπ_rep

theorem pEl_eq
    (i : Fin 1024) : pEl i = pElAlt i := permOfArr_eq_of_rep' (pElAlt_rep i)

theorem pEl_rep
    (i : Fin 1024) : Rep 1755 pPel[(i : ℕ)]! (pEl i) := by
  rw [pEl_eq]
  exact pElAlt_rep i

theorem pEl_mem
    (i : Fin 1024) : pEl i ∈ twoF4P := by
  rw [pEl_eq]
  unfold pElAlt
  by_cases h : (i : ℕ) < 512
  · simp only [h, dite_true]
    exact Or.inl (jEl_mem _)
  · simp only [h, dite_false]
    refine Or.inr ?_
    simpa using jEl_mem ⟨(i : ℕ) - 512, by have := i.2; omega⟩

theorem pEl_surj
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ twoF4P) : ∃ i, pEl i = x := by
  rcases hx with hx | hx
  · obtain ⟨j, hj⟩ := jEl_surj hx
    refine ⟨⟨j, by have := j.2; omega⟩, ?_⟩
    rw [pEl_eq]
    unfold pElAlt
    simp only [Fin.is_lt, dite_true]
    exact hj
  · obtain ⟨j, hj⟩ := jEl_surj hx
    refine ⟨⟨(j : ℕ) + 512, by have := j.2; omega⟩, ?_⟩
    rw [pEl_eq]
    unfold pElAlt
    have h : ¬ ((j : ℕ) + 512 < 512) := by omega
    simp only [h, dite_false]
    have e : (⟨(j : ℕ) + 512 - 512, by omega⟩ : Fin 512) = j := Fin.ext (by simp)
    rw [e, hj]
    simp

theorem pEl_inj
    : Function.Injective pEl := by
  intro i j hij
  by_contra hne
  obtain ⟨-, -, -, -, -, -, -, hinj, -⟩ := pModel_check
  have h := allLt_spec (allLt_spec hinj i.2) j.2
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, bne_iff_ne, ne_eq] at h
  rcases h with h | ⟨p, hp, hne'⟩
  · exact hne (Fin.ext h)
  · have hp' : p < 1755 := by
      rw [jModel_check.2.1] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      omega
    apply hne'
    rw [(pEl_rep i).apply hp', (pEl_rep j).apply hp', hij]

theorem twoF4P_fix_base
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ twoF4P)
    (hfix : ∀ b : Fin 1755, ((b : ℕ) = 5 ∨ (b : ℕ) = 1 ∨ (b : ℕ) = 24 ∨ (b : ℕ) = 12) →
      x b = b) : x = 1 := by
  rcases hx with hx | hx
  · exact jEl_agree hx (one_mem _) fun b hb => hfix b hb
  · obtain ⟨j, hj⟩ := jEl_surj hx
    exfalso
    have hxe : x = jEl j * tπ := by rw [hj]; simp
    subst hxe
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hbase⟩ := twoF4Pi_check
    have h := allLt_spec hbase j.2
    have hall : titsJBase.all (fun p => (jPel[(j : ℕ)]!)[titsPiArr[p]!]! == p) = true := by
      rw [List.all_eq_true]
      intro p hp
      have hb : p = 5 ∨ p = 1 ∨ p = 24 ∨ p = 12 := by
        rw [jModel_check.2.1] at hp
        simpa using hp
      have hp' : p < 1755 := by omega
      have h1 := hfix ⟨p, hp'⟩ hb
      have e1 := (jEl_rep j) (tπ ⟨p, hp'⟩)
      have e2 := tπ_rep.apply hp'
      rw [beq_iff_eq, e2, e1]
      have h2 := congrArg Fin.val h1
      rw [Equiv.Perm.mul_apply] at h2
      exact h2
    rw [hall] at h
    simp at h

theorem twoF4P_agree
    {g h : Equiv.Perm (Fin 1755)} (hg : g ∈ twoF4P) (hh : h ∈ twoF4P)
    (hbase : ∀ b : Fin 1755, ((b : ℕ) = 5 ∨ (b : ℕ) = 1 ∨ (b : ℕ) = 24 ∨ (b : ℕ) = 12) →
      g b = h b) : g = h := by
  have h1 : g⁻¹ * h = 1 := twoF4P_fix_base (twoF4P.mul_mem (twoF4P.inv_mem hg) hh) fun b hb => by
    rw [Equiv.Perm.mul_apply, ← hbase b hb]
    simp
  exact inv_mul_eq_one.1 h1

theorem pEl_mul
    (i j : Fin 1024) : pEl (pOps.mul i j) = pEl i * pEl j := by
  obtain ⟨-, hmul, -⟩ := pModel_check
  have h := allLt_spec (allLt_spec hmul i.2) j.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlt, hall⟩ := h
  have hk : ((pOps.mul i j : Fin 1024) : ℕ) = (pMulT[(i : ℕ)]!)[(j : ℕ)]! := finPt_val hlt
  refine twoF4P_agree (pEl_mem _) (twoF4P.mul_mem (pEl_mem i) (pEl_mem j)) fun b hb => ?_
  have hb' : (b : ℕ) ∈ titsJBase := by
    rw [jModel_check.2.1]
    simpa using hb
  have h1 := List.all_eq_true.1 hall (b : ℕ) hb'
  rw [beq_iff_eq, ← hk] at h1
  have e1 := pEl_rep (pOps.mul i j) b
  have e2 := pEl_rep j b
  have e3 := pEl_rep i (pEl j b)
  apply Fin.ext
  rw [Equiv.Perm.mul_apply, ← e1, h1, e2]
  exact e3

theorem pEl_inv
    (i : Fin 1024) : pEl (pOps.inv i) = (pEl i)⁻¹ := by
  obtain ⟨-, -, hinv, -⟩ := pModel_check
  have h := allLt_spec hinv i.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlt, hinvA⟩, heq⟩ := h
  have hk : ((pOps.inv i : Fin 1024) : ℕ) = pInvT[(i : ℕ)]! := finPt_val hlt
  have hrep := rep_inv_of_isInvA (pEl_rep i) hinvA
  rw [← hk] at heq
  exact ((eqA_iff hrep (pEl_rep (pOps.inv i))).1 heq).symm

theorem pEl_one
    : pEl pOps.one = 1 := by
  obtain ⟨-, -, -, hlt, h, -⟩ := pModel_check
  have hk : ((pOps.one : Fin 1024) : ℕ) = pOneI := finPt_val hlt
  rw [← hk] at h
  exact ((eqA_iff (pEl_rep pOps.one) rep_idA).1 h)

theorem pEl_z
    : pEl pOps.zI = titsZ := by
  obtain ⟨-, -, -, -, -, hlt, h, -⟩ := pModel_check
  have hk : ((pOps.zI : Fin 1024) : ℕ) = pZI := finPt_val hlt
  rw [← hk] at h
  exact (eqA_iff (pEl_rep pOps.zI) titsZ_rep).1 h

theorem pGenArrs_get_lt
    {k : ℕ} (hk : k < 3) : pGenArrs[k]! = jGenArrs[k]! := by
  have hs : jGenArrs.size = 3 := jModel_check.2.2.1
  unfold pGenArrs
  rw [getElem!_pos _ k (by simp [hs]; omega), getElem!_pos jGenArrs k (by omega)]
  exact Array.getElem_push_lt (by omega)

theorem pGenArrs_get_three : pGenArrs[3]! = titsPiArr := by
  have hs : jGenArrs.size = 3 := jModel_check.2.2.1
  unfold pGenArrs
  have h : (jGenArrs.push titsPiArr)[jGenArrs.size]! = titsPiArr := by
    rw [getElem!_pos _ jGenArrs.size (by simp)]
    exact Array.getElem_push_eq
  rwa [hs] at h

@[expose] def pGen (k : Fin 4) : Equiv.Perm (Fin 1755) :=
  if h : (k : ℕ) < 3 then jGen ⟨k, h⟩ else tπ

theorem pGen_rep
    (k : Fin 4) : Rep 1755 pGenArrs[(k : ℕ)]! (pGen k) := by
  unfold pGen
  by_cases h : (k : ℕ) < 3
  · simp only [h, dite_true]
    rw [pGenArrs_get_lt h]
    exact jGen_rep ⟨k, h⟩
  · simp only [h, dite_false]
    have hk3 : (k : ℕ) = 3 := by have := k.2; omega
    rw [hk3, pGenArrs_get_three]
    exact tπ_rep

theorem pGen_mem
    (k : Fin 4) : pGen k ∈ twoF4H := by
  unfold pGen
  by_cases h : (k : ℕ) < 3
  · simp only [h, dite_true]
    exact le_extSub (jGen_mem ⟨k, h⟩)
  · simp only [h, dite_false]
    exact q_mem_extSub

theorem pEl_cj
    (k : Fin 4) (i : Fin 1024) : pEl (pCj k i) = pGen k * pEl i * (pGen k)⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, hgi, hcj, -⟩ := pModel_check
  have h := allLt_spec (allLt_spec hcj k.2) i.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlt, heq⟩ := h
  have hk : ((pCj k i : Fin 1024) : ℕ) = (pCjT[(k : ℕ)]!)[(i : ℕ)]! := finPt_val hlt
  have hinvA := allLt_spec hgi k.2
  have hrinv := rep_inv_of_isInvA (pGen_rep k) hinvA
  have hr := rep_compA (rep_compA (pGen_rep k) (pEl_rep i)) hrinv
  rw [← hk] at heq
  exact ((eqA_iff hr (pEl_rep (pCj k i))).1 heq).symm

theorem pEl_cc
    (i : Fin 1024) : pEl (pCc i) = jC * pEl i * jC⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcc, -⟩ := pModel_check
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hci, -⟩ := jModel_check
  have h := allLt_spec hcc i.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlt, heq⟩ := h
  have hk : ((pCc i : Fin 1024) : ℕ) = pCcT[(i : ℕ)]! := finPt_val hlt
  have hrinv := rep_inv_of_isInvA jC_rep hci
  have hr := rep_compA (rep_compA jC_rep (pEl_rep i)) hrinv
  rw [← hk] at heq
  exact ((eqA_iff hr (pEl_rep (pCc i))).1 heq).symm

@[expose] def pVTable
    : VTable twoF4H twoF4N 1024 where
  toVOps := pOps
  el := pEl
  el_inj := pEl_inj
  el_range := fun x => by
    rw [pCoreOf_twoF4H]
    exact ⟨fun hx => pEl_surj hx, fun ⟨i, hi⟩ => hi ▸ pEl_mem i⟩
  el_mul := pEl_mul
  el_inv := pEl_inv
  el_one := pEl_one
  Z_iff := fun x => by
    rw [mem_omegaOneCenter_twoF4HN_iff, pEl_z]

theorem VTable.card_pCoreOf {G : Type*} [Group G] {H L2 : Subgroup G} {N : ℕ}
    (T : VTable H L2 N) : Nat.card ↥(pCoreOf 2 H) = N := by
  have h := Nat.card_eq_of_bijective (α := Fin N) (β := ↥(pCoreOf 2 H))
    (fun i => ⟨T.el i, T.mem_pCoreOf_el i⟩) ⟨fun i j hij => T.el_inj (congrArg Subtype.val hij),
      fun ⟨y, hy⟩ => by
        obtain ⟨i, rfl⟩ := (T.el_range _).1 hy
        exact ⟨i, rfl⟩⟩
  rw [← h, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_pCoreOf_twoF4H
    : Nat.card (pCoreOf 2 twoF4H) = 1024 := pVTable.card_pCoreOf

theorem twoF4VertexFacts
    : TitsLikeVertexFacts twoF4H twoF4N := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hC⟩ := pModel_check
  refine titsLikeVertexFacts_of_table2 pVTable hC jC ?_ jC_pow_five ?_ pGen ?_ ?_
  · exact le_extSub jC_mem
  · exact pEl_cc
  · intro k
    exact pGen_mem k
  · exact pEl_cj

end CFSG.Quasithin
