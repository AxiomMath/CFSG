module

public import CFSG.LargeExtraspecial.S63CD4Class
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocBase

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

@[expose] noncomputable def d4Ct : Subgroup D := Subgroup.closure (genSet cGH cGens.size)

theorem exists_conj_mem_of_classTreeOK {gs : Array (Array ℕ)} {x : Array ℕ}
    {T : Array (Array ℕ)} {P K : Array ℕ} {idx : Array ℕ → ℕ} {gH : ℕ → D}
    (hgs : ∀ k < gs.size, RepE d4E gs[k]! (gH k) ∧ gH k * gH k = 1) {x₀ : D}
    (hx : RepE d4E x x₀) (h : classTreeOK gs x T P K idx = true) :
    ∀ i < T.size, ∃ c ∈ Subgroup.closure (genSet gH gs.size), RepE d4E T[i]! (c * x₀ * c⁻¹) := by
  obtain ⟨-, h0, hall⟩ := classTreeOK_parts h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases (hall i hi).2.2 with rfl | ⟨hP, hK, hT⟩
    · exact ⟨1, Subgroup.one_mem _, by rw [h0]; simpa using hx⟩
    · obtain ⟨c, hcm, hc⟩ := ih _ hP (hP.trans hi)
      refine ⟨gH K[i]! * c, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hK, rfl⟩) hcm, ?_⟩
      rw [hT]
      have := repE_conjR (hgs _ hK).1 hc (hgs _ hK).2
      rwa [show gH K[i]! * (c * x₀ * c⁻¹) * (gH K[i]!)⁻¹ =
        gH K[i]! * c * x₀ * (gH K[i]! * c)⁻¹ by group] at this

section Cert


theorem locV_parts : gensOK cGens = true ∧
    (∀ k < cGens.size, locComm cGens[k]! t0R = true) ∧
    enumOK cGens locEC.El locEC.P locEC.K locEC.idx = true ∧ locEC.El.size = 3072 ∧
    locCz.T[0]! = z0R ∧ locIsInv locCz.T[1]! = true ∧ locIsInv locCz.T[5]! = true ∧
    mulR z0R locCz.T[1]! = locCz.T[5]! ∧ mulR locCz.T[1]! z0R = locCz.T[5]! ∧
    mulR z0R locCz.T[5]! = locCz.T[1]! ∧ mulR locCz.T[5]! z0R = locCz.T[1]! ∧
    mulR locCz.T[1]! locCz.T[5]! = z0R ∧ mulR locCz.T[5]! locCz.T[1]! = z0R ∧
    locComm t0R z0R = true ∧ locComm t0R locCz.T[1]! = true ∧ locComm t0R locCz.T[5]! = true ∧
    (∀ k < cGens.size, ∀ v ∈ [z0R, locCz.T[1]!, locCz.T[5]!],
      conjI cGens[k]! cGens[k]! v = z0R ∨ conjI cGens[k]! cGens[k]! v = locCz.T[1]! ∨
        conjI cGens[k]! cGens[k]! v = locCz.T[5]!) ∧
    classTreeOK cGens z0R locCzC.T locCzC.P locCzC.K locCzC.idx = true ∧
    memR locCzC.T locCzC.idx locCz.T[1]! = true ∧ memR locCzC.T locCzC.idx locCz.T[5]! = true ∧
    (∃ i < locEC.El.size, locComm locEC.El[i]! z0R = true ∧
      locComm locEC.El[i]! locCz.T[1]! = true ∧ locComm locEC.El[i]! locCz.T[5]! = true ∧
      (mulR locEC.El[i]! locEC.El[i]! = z0R ∨ mulR locEC.El[i]! locEC.El[i]! = locCz.T[1]! ∨
        mulR locEC.El[i]! locEC.El[i]! = locCz.T[5]!)) := by
  have h := loc_parts.2.2.2.1
  simp only [locVCheck, Bool.and_eq_true, EnumData.ok, beq_iff_eq, List.all_eq_true,
    List.mem_range, List.any_eq_true, Bool.or_eq_true, and_assoc, or_assoc] at h
  exact h

theorem cGens_hyp' : ∀ k < cGens.size, RepE d4E cGens[k]! (cGH k) ∧ cGH k * cGH k = 1 :=
  mul_self_of_gensOK (fun _ hk => repE_cGens hk) locV_parts.1

theorem gen_mem_Ct {k : ℕ} (hk : k < cGens.size) : cGH k ∈ d4Ct :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem exists_of_C {i : ℕ} (hi : i < locEC.El.size) : ∃ a ∈ d4Ct, RepE d4E locEC.El[i]! a :=
  exists_of_enumOK (fun _ hk => (cGens_hyp' _ hk).1) locV_parts.2.2.1 i hi

theorem card_d4Ct : Nat.card d4Ct = 3072 := by
  have := card_of_enumOK d4E_injective cGens_hyp' locV_parts.2.2.1
  rw [locV_parts.2.2.2.1] at this
  exact this

theorem d4Ct_le_centralizer : d4Ct ≤ Subgroup.centralizer ({d4t} : Set D) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact locComm_of_eq (repE_cGens hk) repE_t0R (locV_parts.2.1 k hk)

theorem centralizer_d4t_eq :
    Subgroup.centralizer ({d4t} : Set D) = d4Ct := by
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [card_trialityGroup8]; norm_num)
  refine (Subgroup.eq_of_le_of_card_ge d4Ct_le_centralizer ?_).symm
  rw [card_d4Ct]
  exact card_centralizer_d4t_le

theorem locF_parts : (∀ w ∈ cWords, (∀ k ∈ w, k < 8) ∧ fixesLine0 (locWordArr w) = true) ∧
    classTreeOK cGens (wordR d4Gens locU0Word) locCu.T locCu.P locCu.K locCu.idx = true ∧
    (∀ i < 819, locComm locCz.T[i]! t0R = false ∨ i = 0 ∨ i = 1 ∨ i = 5 ∨
      memR locCu.T locCu.idx locCz.T[i]! = true) ∧
    memR locEQ.El locEQ.idx t0R = true ∧
    locPairChain locET locEQ (wordR d4Gens locU0Word) = true := by
  have h := loc_parts.2.2.2.2.1
  simp only [locFusion, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun w hw => h1 w hw, h2, fun i hi => ?_, h4, h5⟩
  have := allLt_spec h3 hi
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', or_assoc] at this
  exact this

end Cert

section Model


theorem cWords_mem {k : ℕ} (hk : k < 4) : cWords.getD k [] ∈ cWords := by
  interval_cases k <;> simp [cWords]

theorem d4Ct_le_d4N : d4Ct ≤ d4N := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < 4 := by simpa [cGens_size] using hk
  obtain ⟨hw, hfix⟩ := locF_parts.1 _ (cWords_mem hk')
  exact mem_d4N_of_rep (rep_d4WordArr _ hw) hfix

end Model

end CFSG.Quasithin.D4Hex
