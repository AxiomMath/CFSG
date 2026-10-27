module

public import CFSG.Sporadic.SuzRecog.GluingProof2
public import CFSG.Sporadic.SuzRecog.ModelGroups
public import Certificates.Certificate15120

public section

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
  CFSG.CosetTable CFSG.Certificates.CosetEnumeration CFSG.Sporadic.SuzRecog.LevelTwoData
  CFSG.Sporadic.SuzRecog.B0TwistData CFSG.Sporadic.SuzRecog.B0TwistCheck
  CFSG.Sporadic.SuzRecog.ModelGroupsCheck

namespace B0Twist

section Codes

variable {K Q : Type*} [Group K] [Group Q]

@[expose] def codeVal (L : ℕ → K) (c : ℕ) : K := if c % 2 = 0 then L (c / 2) else (L (c / 2))⁻¹

private theorem beq_mod_two_true {c : ℕ} (h : c % 2 = 0) : Nat.beq (Nat.mod c 2) 0 = true := by
  rw [Nat.beq_eq]
  exact h

private theorem beq_mod_two_false {c : ℕ} (h : c % 2 = 1) : Nat.beq (Nat.mod c 2) 0 = false := by
  cases hb : Nat.beq (Nat.mod c 2) 0 with
  | false => rfl
  | true =>
    have : c % 2 = 0 := Nat.eq_of_beq_eq_true hb
    omega

theorem codeVal_invCode (L : ℕ → K) (c : ℕ) : codeVal L (invCode c) = (codeVal L c)⁻¹ := by
  unfold invCode codeVal
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [beq_mod_two_true h, Bool.cond_true, Nat.succ_eq_add_one, ite_eq_right (by omega),
      ite_eq_left h, show (c + 1) / 2 = c / 2 by omega]
  · rw [beq_mod_two_false h, Bool.cond_false, Nat.pred_eq_sub_one, ite_eq_left (by omega),
      ite_eq_right (by omega), show (c - 1) / 2 = c / 2 by omega, inv_inv]

theorem evalWord_codeVal_map (φ : K →* Q) {kL : ℕ → K} {L : ℕ → Q} {S : ℕ → Prop}
    (hL : ∀ i, S i → L i = φ (kL i)) :
    ∀ w : List ℕ, (∀ c ∈ w, S (c / 2)) → evalWord (codeVal L) w = φ (evalWord (codeVal kL) w)
  | [], _ => by rw [evalWord_nil, evalWord_nil, map_one]
  | c :: w, hw => by
    have hc : codeVal L c = φ (codeVal kL c) := by
      unfold codeVal
      by_cases h : c % 2 = 0
      · rw [ite_eq_left h, ite_eq_left h]
        exact hL _ (hw c List.mem_cons_self)
      · rw [ite_eq_right h, ite_eq_right h, map_inv, hL _ (hw c List.mem_cons_self)]
    rw [evalWord_cons, evalWord_cons, map_mul, hc,
      evalWord_codeVal_map φ hL w fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')]

theorem evalWord_eq_one_of_subgroup {P G : Type*} [Group P] [Group G] {K' : Subgroup P}
    (f : ↥K' →* G) (kL : ℕ → ↥K') {mL : ℕ → P} {gL : ℕ → G} {S : ℕ → Prop}
    (hm : ∀ i, S i → mL i = K'.subtype (kL i)) (hg : ∀ i, S i → gL i = f (kL i))
    {w : List ℕ} (hw : ∀ c ∈ w, S (c / 2)) (h1 : evalWord (codeVal mL) w = 1) :
    evalWord (codeVal gL) w = 1 := by
  rw [evalWord_codeVal_map f hg w hw]
  have h2 := evalWord_codeVal_map K'.subtype hm w hw
  rw [h1] at h2
  have h3 : evalWord (codeVal kL) w = 1 := Subtype.ext h2.symm
  rw [h3, map_one]

end Codes

@[expose] noncomputable def h1 : Equiv.Perm (Fin 1782) := permC 1782 h1Arr

@[expose] noncomputable def h2 : Equiv.Perm (Fin 1782) := permC 1782 h2Arr

@[expose] noncomputable def ja : Equiv.Perm (Fin 1782) := permC 1782 aArr

@[expose] noncomputable def jb : Equiv.Perm (Fin 1782) := permC 1782 bArr

@[expose] noncomputable def tau : Equiv.Perm (Fin 1782) := permC 1782 tauArr

@[expose] noncomputable def mLetter : ℕ → Equiv.Perm (Fin 1782)
  | 0 => h1
  | 1 => h2
  | 2 => Model.rho1
  | 3 => ja
  | 4 => jb
  | 5 => tau
  | 6 => Model.w0
  | _ => 1

@[expose] noncomputable def mLetterT (i : ℕ) : Equiv.Perm (Fin 1782) :=
  if i = 5 then tau * suzInv 1 else mLetter i

section Checks

theorem tw_mem_check : twMemOK := Certificates.certificate15120.1

theorem tw_perms_check : twPermsOK = true := Certificates.certificate15120.2.1

theorem tw_members_check : twMembersOK = true := Certificates.certificate15120.2.2.1

theorem tw_comm_check : twCommOK = true := Certificates.certificate15120.2.2.2.1

theorem tw_tau_check : twTauOK = true := Certificates.certificate15120.2.2.2.2.1

theorem tw_rels_check : twRelsOK = true := Certificates.certificate15120.2.2.2.2.2

theorem tw_perms_parts : permOK h1Arr = true ∧ permOK h2Arr = true ∧ permOK aArr = true ∧
    permOK bArr = true ∧ permOK tauArr = true := by
  have h := tw_perms_check
  simp only [twPermsOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem rep_h1 : Rep 1782 h1Arr h1 := (rep_permC tw_perms_parts.1).1

theorem rep_h2 : Rep 1782 h2Arr h2 := (rep_permC tw_perms_parts.2.1).1

theorem rep_ja : Rep 1782 aArr ja := (rep_permC tw_perms_parts.2.2.1).1

theorem rep_jb : Rep 1782 bArr jb := (rep_permC tw_perms_parts.2.2.2.1).1

theorem rep_tau : Rep 1782 tauArr tau := (rep_permC tw_perms_parts.2.2.2.2).1

theorem tw_members_parts : inM h1Arr = true ∧ inM h2Arr = true ∧ inM aArr = true ∧
    inM bArr = true ∧ inM tauArr = true := by
  have h := tw_members_check
  simp only [twMembersOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem tw_comm_parts : commA h1Arr rhoArr = true ∧ commA h1Arr t1A = true ∧
    commA h2Arr rhoArr = true ∧ commA h2Arr t1A = true ∧ commA aArr rhoArr = true ∧
    commA aArr w0Arr = true ∧ commA aArr w1A = true ∧ commA bArr rhoArr = true ∧
    commA bArr w0Arr = true ∧ commA bArr w1A = true ∧ commA tauArr t1A = true := by
  have h := tw_comm_check
  simp only [twCommOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem tw_tau_parts : normR0 tauArr = true ∧
    eqA 1782 (conjA tauArr rhoArr) (invCand 1782 rhoArr) = true ∧
    twEvenAt tauArr 0 = false ∧ twEvenAt tauArr 1 = false ∧ twEvenAt tauArr 2 = false := by
  have h := tw_tau_check
  simp only [twTauOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem tw_rels_parts :
    (∀ w ∈ relsC ++ relsN, eqA 1782 (twWordA twGens w) (idA 1782) = true) ∧
      ∀ w ∈ relsT ++ [relX], eqA 1782 (twWordA twGensT w) (idA 1782) = true := by
  have h := tw_rels_check
  simp only [twRelsOK, Bool.and_eq_true, List.all_eq_true] at h
  exact h

end Checks

theorem rep_twWordA {S : Array (Array ℕ)} {mL : ℕ → Equiv.Perm (Fin 1782)}
    (hS : ∀ i < 7, Rep 1782 S[i]! (mL i)) :
    ∀ w : List ℕ, (∀ c ∈ w, c < 14) → Rep 1782 (twWordA S w) (evalWord (codeVal mL) w)
  | [], _ => by
    rw [twWordA, evalWord_nil]
    exact rep_idA
  | c :: w, hw => by
    have hc : c / 2 < 7 := by
      have := hw c List.mem_cons_self
      omega
    have hcode : Rep 1782 (twCodeA S c) (codeVal mL c) := by
      unfold twCodeA codeVal
      by_cases h : c % 2 = 0
      · rw [ite_eq_left h, ite_eq_left h]
        exact hS _ hc
      · rw [ite_eq_right h, ite_eq_right h]
        exact ModelGroups.rep_invCand (hS _ hc)
    rw [twWordA, evalWord_cons]
    exact rep_compA hcode (rep_twWordA hS w fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))

section Seven

variable {α : Type*} [Inhabited α] (x₀ x₁ x₂ x₃ x₄ x₅ x₆ : α)

theorem getElem!_seven :
    (#[x₀, x₁, x₂, x₃, x₄, x₅, x₆] : Array α)[0]! = x₀ ∧
      (#[x₀, x₁, x₂, x₃, x₄, x₅, x₆] : Array α)[1]! = x₁ ∧
      (#[x₀, x₁, x₂, x₃, x₄, x₅, x₆] : Array α)[2]! = x₂ ∧
      (#[x₀, x₁, x₂, x₃, x₄, x₅, x₆] : Array α)[3]! = x₃ ∧
      (#[x₀, x₁, x₂, x₃, x₄, x₅, x₆] : Array α)[4]! = x₄ ∧
      (#[x₀, x₁, x₂, x₃, x₄, x₅, x₆] : Array α)[5]! = x₅ ∧
      (#[x₀, x₁, x₂, x₃, x₄, x₅, x₆] : Array α)[6]! = x₆ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Seven

theorem rep_mLetter :
    ∀ i < 7, Rep 1782 twGens[i]! (mLetter i) := by
  have e := getElem!_seven h1Arr h2Arr rhoArr aArr bArr tauArr w0Arr
  intro i hi
  rw [twGens]
  interval_cases i
  · rw [e.1]
    exact rep_h1
  · rw [e.2.1]
    exact rep_h2
  · rw [e.2.2.1]
    exact ModelGroups.rep_rho1
  · rw [e.2.2.2.1]
    exact rep_ja
  · rw [e.2.2.2.2.1]
    exact rep_jb
  · rw [e.2.2.2.2.2.1]
    exact rep_tau
  · rw [e.2.2.2.2.2.2]
    exact ModelGroups.rep_w0

theorem rep_mLetterT :
    ∀ i < 7, Rep 1782 twGensT[i]! (mLetterT i) := by
  have e := getElem!_seven h1Arr h2Arr rhoArr aArr bArr (compA 1782 tauArr t1A) w0Arr
  intro i hi
  rw [twGensT]
  interval_cases i
  · rw [e.1]
    exact rep_h1
  · rw [e.2.1]
    exact rep_h2
  · rw [e.2.2.1]
    exact ModelGroups.rep_rho1
  · rw [e.2.2.2.1]
    exact rep_ja
  · rw [e.2.2.2.2.1]
    exact rep_jb
  · rw [e.2.2.2.2.2.1]
    exact rep_compA rep_tau ModelGroups.rep_t1
  · rw [e.2.2.2.2.2.2]
    exact ModelGroups.rep_w0

theorem twRels_lt : ∀ r ∈ twRels, ∀ c ∈ r, c < 14 := by decide

theorem relsC_letters : ∀ r ∈ relsC, ∀ c ∈ r, c / 2 < 5 := by decide

theorem relsN_letters : ∀ r ∈ relsN, ∀ c ∈ r, 2 ≤ c / 2 ∧ c / 2 < 7 := by decide

theorem relsTX_letters : ∀ r ∈ relsT ++ [relX], ∀ c ∈ r, c / 2 < 2 ∨ c / 2 = 5 ∨ c / 2 = 6 := by
  decide

theorem twRels_eq : twRels = (relsC ++ relsN) ++ (relsT ++ [relX]) := by
  simp only [twRels, List.append_assoc]

theorem evalWord_mLetter
    {w : List ℕ} (hw : w ∈ relsC ++ relsN) : evalWord (codeVal mLetter) w = 1 := by
  have hl : ∀ c ∈ w, c < 14 := twRels_lt w (by rw [twRels_eq]; exact List.mem_append_left _ hw)
  exact eq_of_eqA (rep_twWordA rep_mLetter w hl) rep_idA (tw_rels_parts.1 w hw)

theorem evalWord_mLetterT
    {w : List ℕ} (hw : w ∈ relsT ++ [relX]) :
    evalWord (codeVal mLetterT) w = 1 := by
  have hl : ∀ c ∈ w, c < 14 := twRels_lt w (by rw [twRels_eq]; exact List.mem_append_right _ hw)
  exact eq_of_eqA (rep_twWordA rep_mLetterT w hl) rep_idA (tw_rels_parts.2 w hw)

theorem rep_twRhoPowA :
    ∀ k : ℕ, Rep 1782 (twRhoPowA k) (Model.rho1 ^ k)
  | 0 => by
    rw [twRhoPowA, pow_zero]
    exact rep_idA
  | k + 1 => by
    rw [twRhoPowA, pow_succ']
    exact rep_compA ModelGroups.rep_rho1 (rep_twRhoPowA k)

theorem conj_mem_centralizer {P : Type*} [Group P] {s : Set P} {g c : P}
    (hg : g ∈ normalizer s) (hc : c ∈ centralizer s) : g * c * g⁻¹ ∈ centralizer s := by
  rw [mem_centralizer_iff] at hc ⊢
  intro r hr
  have hr' : g⁻¹ * r * g ∈ s := by
    have := (mem_set_normalizer_iff.1 (inv_mem hg) r).1 hr
    rwa [inv_inv] at this
  calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [hc _ hr']
    _ = g * c * g⁻¹ * r := by group

section Model

theorem tau_not_mem_B0Plus : tau ∉ B0Plus := by
  intro h
  have h2 : tau ∈ centralizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) ⊔ zpowers Model.rho1 :=
    (mem_inf.1 h).2
  have hN : Model.rho1 ∈ normalizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) :=
    (mem_inf.1 C1Model.rho1_mem_B0).2
  have hle : zpowers Model.rho1 ≤ normalizer
      ((centralizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) : Subgroup _) : Set _) := by
    rw [zpowers_le, mem_set_normalizer_iff]
    intro c
    constructor
    · exact conj_mem_centralizer hN
    · intro hc
      have := conj_mem_centralizer (inv_mem hN) hc
      rwa [show Model.rho1⁻¹ * (Model.rho1 * c * Model.rho1⁻¹) * Model.rho1⁻¹⁻¹ = c by group]
        at this
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hle] at h2
  obtain ⟨c, hc, z, hz, hcz⟩ := h2
  have hcz' : tau * z⁻¹ = c := by rw [← hcz, mul_inv_cancel_right]
  have hcen : ∀ n : ℕ, z⁻¹ = Model.rho1 ^ n → twEvenAt tauArr n = true := by
    intro n hn
    have hr := rep_compA rep_tau (rep_twRhoPowA n)
    have hc' : tau * Model.rho1 ^ n ∈ centralizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) := by
      rw [← hn, hcz']
      exact hc
    rw [mem_centralizer_iff] at hc'
    simp only [twEvenAt, Bool.and_eq_true]
    exact ⟨(ModelGroups.commA_iff hr ModelGroups.rep_w0).2 (hc' _ C1Model.w0_mem_R0).symm,
      (ModelGroups.commA_iff hr ModelGroups.rep_r1).2 (hc' _ C1Model.r1_mem_R0).symm⟩
  rcases (ModelGroups.mem_zpowers_of_orderOf_eq_three ModelGroups.orderOf_rho1).1 (inv_mem hz)
    with e | e | e
  · have := hcen 0 (by rw [e, pow_zero])
    rw [tw_tau_parts.2.2.1] at this
    exact Bool.false_ne_true this
  · have := hcen 1 (by rw [e, pow_one])
    rw [tw_tau_parts.2.2.2.1] at this
    exact Bool.false_ne_true this
  · have := hcen 2 (by rw [e, pow_two])
    rw [tw_tau_parts.2.2.2.2] at this
    exact Bool.false_ne_true this

theorem model_facts :
    (h1 ∈ invE 1 ∧ h1 ∈ Model.Crho1) ∧ (h2 ∈ invE 1 ∧ h2 ∈ Model.Crho1) ∧
      (ja ∈ Model.Crho1 ∧ ja ∈ Model.NR0) ∧ (jb ∈ Model.Crho1 ∧ jb ∈ Model.NR0) ∧
      (tau ∈ invE 1 ∧ tau ∈ Model.NR0 ∧ tau * suzInv 1 ∈ invE 1 ∧
        tau * Model.rho1 * tau⁻¹ = Model.rho1⁻¹) ∧
      Model.rho1 ∈ Model.Crho1 ∧ Model.rho1 ∈ B0Plus ∧ Model.w0 ∈ B0Plus ∧
      ModelGroups.rho2 ∉ zpowers Model.rho1 := by
  have hm := tw_members_parts
  have hc := tw_comm_parts
  have hinvE : ∀ {g : Equiv.Perm (Fin 1782)} {t : Array ℕ}, Rep 1782 t g → inM t = true →
      commA t t1A = true → g ∈ invE 1 := fun hg h1 h2 =>
    ModelGroups.mem_invE_one_iff.2
      ⟨(ModelGroups.commA_iff hg ModelGroups.rep_t1).1 h2, (inM_iff hg).1 h1⟩
  have hCr : ∀ {g : Equiv.Perm (Fin 1782)} {t : Array ℕ}, Rep 1782 t g → inM t = true →
      commA t rhoArr = true → g ∈ Model.Crho1 := fun hg h1 h2 =>
    ModelGroups.mem_Crho1_iff.2
      ⟨(ModelGroups.commA_iff hg ModelGroups.rep_rho1).1 h2, (inM_iff hg).1 h1⟩
  have hNR : ∀ {g : Equiv.Perm (Fin 1782)} {t : Array ℕ}, Rep 1782 t g → inM t = true →
      commA t w0Arr = true → commA t w1A = true → g ∈ Model.NR0 := fun hg h1 h2 h3 => by
    refine ModelGroups.mem_NR0.2 ⟨(inM_iff hg).1 h1,
      ModelGroups.mem_normalizer_R0_of_mem_centralizer ?_⟩
    rw [Model.R0, centralizer_closure, mem_centralizer_iff]
    rintro x (rfl | rfl)
    · exact ((ModelGroups.commA_iff hg ModelGroups.rep_w0).1 h2).symm
    · exact ((ModelGroups.commA_iff hg ModelGroups.rep_r1).1 h3).symm
  have htau : tau ∈ invE 1 := hinvE rep_tau hm.2.2.2.2 hc.2.2.2.2.2.2.2.2.2.2
  have ht1 : suzInv 1 ∈ invE 1 := ModelGroups.mem_invE_one_iff.2 ⟨rfl, ModelGroups.t1_mem_suzM⟩
  have hrho2 : ModelGroups.rho2 ∉ zpowers Model.rho1 := by
    intro h
    rcases (ModelGroups.mem_zpowers_of_orderOf_eq_three ModelGroups.orderOf_rho1).1 h with
      e | e | e
    · exact ModelGroups.rho2_ne_one e
    · exact ModelGroups.basic_facts.2.2.2 (Or.inl e.symm)
    · refine ModelGroups.basic_facts.2.2.2 (Or.inr ?_)
      rw [e]
      exact ModelGroups.rho1_mul_rho1_sq.symm
  refine ⟨⟨hinvE rep_h1 hm.1 hc.2.1, hCr rep_h1 hm.1 hc.1⟩,
    ⟨hinvE rep_h2 hm.2.1 hc.2.2.2.1, hCr rep_h2 hm.2.1 hc.2.2.1⟩,
    ⟨hCr rep_ja hm.2.2.1 hc.2.2.2.2.1, hNR rep_ja hm.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1⟩,
    ⟨hCr rep_jb hm.2.2.2.1 hc.2.2.2.2.2.2.2.1,
      hNR rep_jb hm.2.2.2.1 hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.1⟩,
    ⟨htau, ModelGroups.mem_NR0.2 ⟨(inM_iff rep_tau).1 hm.2.2.2.2,
      ModelGroups.mem_normalizer_R0_of_normR0 rep_tau tw_tau_parts.1⟩, mul_mem htau ht1,
      eq_of_eqA (ModelGroups.rep_conjA rep_tau ModelGroups.rep_rho1)
        (ModelGroups.rep_invCand ModelGroups.rep_rho1) tw_tau_parts.2.1⟩,
    ModelGroups.mem_Crho1_iff.2 ⟨rfl, ModelGroups.rho1_mem_suzM⟩,
    mem_inf.2 ⟨C1Model.rho1_mem_B0, mem_sup_right (mem_zpowers _)⟩,
    mem_inf.2 ⟨mem_inf.2 ⟨C1Model.w0_mem_invE, le_normalizer C1Model.w0_mem_R0⟩,
      mem_sup_left (mem_centralizer_iff.2 fun _ hx => C1Model.R0_comm hx C1Model.w0_mem_R0)⟩,
    hrho2⟩

@[expose] noncomputable def cLetter : ℕ → ↥Model.Crho1
  | 0 => ⟨h1, model_facts.1.2⟩
  | 1 => ⟨h2, model_facts.2.1.2⟩
  | 2 => ⟨Model.rho1, model_facts.2.2.2.2.2.1⟩
  | 3 => ⟨ja, model_facts.2.2.1.1⟩
  | 4 => ⟨jb, model_facts.2.2.2.1.1⟩
  | _ => 1

@[expose] noncomputable def nLetter : ℕ → ↥Model.NR0
  | 2 => ⟨Model.rho1, ModelGroups.rho1_mem_NR0⟩
  | 3 => ⟨ja, model_facts.2.2.1.2⟩
  | 4 => ⟨jb, model_facts.2.2.2.1.2⟩
  | 5 => ⟨tau, model_facts.2.2.2.2.1.2.1⟩
  | 6 => ⟨Model.w0, ModelGroups.w0_mem_NR0⟩
  | _ => 1

@[expose] noncomputable def tLetter : ℕ → ↥(invE 1)
  | 0 => ⟨h1, model_facts.1.1⟩
  | 1 => ⟨h2, model_facts.2.1.1⟩
  | 5 => ⟨tau * suzInv 1, model_facts.2.2.2.2.1.2.2.1⟩
  | 6 => ⟨Model.w0, C1Model.w0_mem_invE⟩
  | _ => 1

theorem mLetter_eq_cLetter : ∀ i, i < 5 → mLetter i = Model.Crho1.subtype (cLetter i) := by
  intro i hi
  interval_cases i <;> rfl

theorem mLetter_eq_nLetter : ∀ i, 2 ≤ i ∧ i < 7 → mLetter i = Model.NR0.subtype (nLetter i) := by
  rintro i ⟨hi, hi'⟩
  interval_cases i <;> rfl

theorem mLetterT_eq_tLetter : ∀ i, i < 2 ∨ i = 5 ∨ i = 6 →
    mLetterT i = (invE 1).subtype (tLetter i) := by
  rintro i (hi | rfl | rfl)
  · interval_cases i <;> rfl
  · rfl
  · rfl

end Model

section Letters

variable
  {G : Type} [Group G] {M : Subgroup G}

@[expose] noncomputable def gLetter (ψ : ↥Model.NR0 →* G) (Φ₂ : ↥Model.Crho1 →* G) (i : ℕ) : G :=
  if i < 5 then Φ₂ (cLetter i) else ψ (nLetter i)

theorem gLetter_rels (σ : ↥M ≃* ↥(invE 1)) (ψ : ↥Model.NR0 →* G) (Φ₂ : ↥Model.Crho1 →* G)
    (hbad : B0TwistAgree σ ψ)
    (hA : ∀ x (hx : x ∈ invE 1) (hxC : x ∈ Model.Crho1), Φ₂ ⟨x, hxC⟩ = (σ.symm ⟨x, hx⟩ : G))
    (hB : ∀ x (hxN : x ∈ Model.NR0) (hxC : x ∈ Model.Crho1), Φ₂ ⟨x, hxC⟩ = ψ ⟨x, hxN⟩) :
    ∀ r ∈ twRels, (∀ y ∈ r, y < 2 * 7) ∧ evalWord (codeVal (gLetter ψ Φ₂)) r = 1 := by
  intro r hr
  refine ⟨twRels_lt r hr, ?_⟩
  rw [twRels_eq, List.mem_append, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · exact evalWord_eq_one_of_subgroup Φ₂ cLetter (S := fun i => i < 5) mLetter_eq_cLetter
      (fun i hi => by rw [gLetter, ite_eq_left hi]) (relsC_letters r hr)
      (evalWord_mLetter (List.mem_append_left _ hr))
  · refine evalWord_eq_one_of_subgroup ψ nLetter (S := fun i => 2 ≤ i ∧ i < 7)
      mLetter_eq_nLetter (fun i hi => ?_) (relsN_letters r hr)
      (evalWord_mLetter (List.mem_append_right _ hr))
    obtain ⟨hi, hi'⟩ := hi
    rw [gLetter]
    by_cases h5 : i < 5
    · rw [ite_eq_left h5]
      interval_cases i
      · exact hB _ _ _
      · exact hB _ _ _
      · exact hB _ _ _
    · rw [ite_eq_right h5]
  · refine evalWord_eq_one_of_subgroup (M.subtype.comp σ.symm.toMonoidHom) tLetter
      (S := fun i => i < 2 ∨ i = 5 ∨ i = 6) mLetterT_eq_tLetter (fun i hi => ?_)
      (relsTX_letters r hr) (evalWord_mLetterT hr)
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, gLetter]
    rcases hi with hi | rfl | rfl
    · rw [ite_eq_left (by omega)]
      interval_cases i
      · exact hA _ _ _
      · exact hA _ _ _
    · rw [ite_eq_right (by omega)]
      exact hbad.2 _ _ model_facts.2.2.2.2.1.1 tau_not_mem_B0Plus _
    · rw [ite_eq_right (by omega)]
      exact hbad.1 _ model_facts.2.2.2.2.2.2.2.1 _ _

theorem gLetter_mem_normalizer (ψ : ↥Model.NR0 →* G) (Φ₂ : ↥Model.Crho1 →* G)
    (hB : ∀ x (hxN : x ∈ Model.NR0) (hxC : x ∈ Model.Crho1), Φ₂ ⟨x, hxC⟩ = ψ ⟨x, hxN⟩)
    {i : ℕ} (hi : i < 6) :
    gLetter ψ Φ₂ i ∈ normalizer (zpowers (gLetter ψ Φ₂ 2) : Set G) := by
  have key : ∀ g : G, (g * gLetter ψ Φ₂ 2 * g⁻¹ = gLetter ψ Φ₂ 2 ∨
      g * gLetter ψ Φ₂ 2 * g⁻¹ = (gLetter ψ Φ₂ 2)⁻¹) →
      g ∈ normalizer (zpowers (gLetter ψ Φ₂ 2) : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (g * gLetter ψ Φ₂ 2 * g⁻¹) = _
    rcases hg with hg | hg
    · rw [hg]
    · rw [hg, zpowers_inv]
  have h2 : gLetter ψ Φ₂ 2 = Φ₂ (cLetter 2) := by rw [gLetter, ite_eq_left (by norm_num)]
  apply key
  by_cases h5 : i < 5
  · left
    have hc : cLetter i * cLetter 2 = cLetter 2 * cLetter i :=
      Subtype.ext (ModelGroups.mem_Crho1_iff.1 (cLetter i).2).1
    rw [h2, gLetter, ite_eq_left h5, ← map_mul, ← map_inv, ← map_mul, hc, mul_inv_cancel_right]
  · right
    have h5' : i = 5 := by omega
    subst h5'
    have hr : gLetter ψ Φ₂ 2 = ψ ⟨Model.rho1, ModelGroups.rho1_mem_NR0⟩ := by
      rw [h2]
      exact hB _ _ _
    rw [hr, gLetter, ite_eq_right (by norm_num), ← map_mul, ← map_inv, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext model_facts.2.2.2.2.1.2.2.2

end Letters

end B0Twist

open B0Twist in
theorem b0TwistExcluded :
    B0TwistExcluded := by
  intro G _ _ _ S _ σ ψ Φ₂ hbad hA hB
  have hmem : codeVal (gLetter ψ Φ₂) 12 ∈
      closure (codeVal (gLetter ψ Φ₂) '' {c | c ∈ [0, 2, 4, 6, 8, 10]}) :=
    tw_mem_check G (codeVal (gLetter ψ Φ₂)) (fun x _ => codeVal_invCode _ x)
      (fun r hr => (gLetter_rels σ ψ Φ₂ hbad hA hB r hr).2)
  have hle : closure (codeVal (gLetter ψ Φ₂) '' {c | c ∈ [0, 2, 4, 6, 8, 10]}) ≤
      normalizer (zpowers (gLetter ψ Φ₂ 2) : Set G) := by
    rw [closure_le]
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c % 2 = 0 ∧ c / 2 < 6 := by
      change c ∈ [0, 2, 4, 6, 8, 10] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    rw [codeVal, ite_eq_left hc'.1]
    exact gLetter_mem_normalizer ψ Φ₂ hB hc'.2
  have hw := (mem_normalizer_iff.1 (hle hmem) (gLetter ψ Φ₂ 2)).1 (mem_zpowers _)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hw
  have hr : gLetter ψ Φ₂ 2 = ψ ⟨Model.rho1, ModelGroups.rho1_mem_NR0⟩ := by
    rw [gLetter, ite_eq_left (by norm_num)]
    exact hB _ _ _
  have hw0 : codeVal (gLetter ψ Φ₂) 12 = ψ ⟨Model.w0, ModelGroups.w0_mem_NR0⟩ := by
    rw [codeVal, ite_eq_left (by norm_num), gLetter, ite_eq_right (by norm_num)]
    rfl
  rw [hr, hw0] at hk
  set a : ↥Model.NR0 := ⟨Model.rho1, ModelGroups.rho1_mem_NR0⟩ with ha
  set b : ↥Model.NR0 := ⟨Model.w0, ModelGroups.w0_mem_NR0⟩ with hb
  have hy : ψ ((a ^ k)⁻¹ * (b * a * b⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_zpow, hk, map_mul, map_mul, map_inv, inv_mul_cancel]
  have hyv : (((a ^ k)⁻¹ * (b * a * b⁻¹) : ↥Model.NR0) : Equiv.Perm (Fin 1782)) =
      (Model.rho1 ^ k)⁻¹ * (Model.w0 * Model.rho1 * Model.w0⁻¹) := by
    rw [ha, hb]
    rfl
  have hyP : (((a ^ k)⁻¹ * (b * a * b⁻¹) : ↥Model.NR0) : Equiv.Perm (Fin 1782)) ∈ B0Plus := by
    rw [hyv]
    exact mul_mem (inv_mem (zpow_mem model_facts.2.2.2.2.2.2.1 k))
      (mul_mem (mul_mem model_facts.2.2.2.2.2.2.2.1 model_facts.2.2.2.2.2.2.1)
        (inv_mem model_facts.2.2.2.2.2.2.2.1))
  have hy1 := (mem_inf.1 (mem_inf.1 hyP).1).1
  have hσ := hbad.1 _ hyP hy1 ((a ^ k)⁻¹ * (b * a * b⁻¹)).2
  rw [Subtype.coe_eta, hy] at hσ
  have hone : σ.symm ⟨_, hy1⟩ = σ.symm 1 := by
    rw [map_one]
    exact Subtype.ext hσ.symm
  have hyv1 := congrArg Subtype.val (σ.symm.injective hone)
  rw [hyv] at hyv1
  apply model_facts.2.2.2.2.2.2.2.2
  refine mem_zpowers_iff.2 ⟨k, ?_⟩
  rw [ModelGroups.rho2]
  exact (inv_mul_eq_one.1 hyv1)

end CFSG.Sporadic.SuzRecog
