module

public import CFSG.Sporadic.Th.Recog.DModel
public import Certificates.Certificate687009

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Recognition.PresentedWords CFSG.CosetTable
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem wYD_twist (k : Twist) (j : Fin 6) :
    (wYD (k, false) j).map (fun l => (dLet l.1, l.2)) = wY k j := by
  revert k j
  decide

theorem coe_wprod_dPD (w : List (Fin 6 × Bool)) :
    ((wprod dPD w : ↥DP) : Equiv.Perm (Fin 51)) = wprod dP w :=
  map_wprod DP.subtype dPD w

theorem mem_normalizer_of_conj_le {g : Equiv.Perm (Fin 51)} (h : ∀ j, g * dP j * g⁻¹ ∈ DP) :
    g ∈ Subgroup.normalizer (DP : Set (Equiv.Perm (Fin 51))) := by
  have hle : DP.map (MulAut.conj g).toMonoidHom ≤ DP := by
    rw [show DP = Subgroup.closure (Set.range dP) from rfl, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact h j
  have hcard : Nat.card DP ≤ Nat.card (DP.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (Subgroup.eq_of_le_of_card_ge hle hcard)

noncomputable def piP (k : OutD) : Equiv.Perm (Fin 51) := CFSG.ONSchreier.permOfArr 51 (piTab k)

noncomputable def iotaP0 : Equiv.Perm (Fin 51) := CFSG.ONSchreier.permOfArr 51 iotaTab

section AutP

theorem tabRep_wTab_dP (w : List (Fin 6 × Bool)) :
    TabRep (wTab letArr (letInv ()) w) ((wprod dPD w : ↥DP) : Equiv.Perm (Fin 51)) := by
  rw [coe_wprod_dPD]
  exact tabRep_wTab tabRep_dP tabRep_letInv w

private theorem cert9_pi : piCheck () = true := Certificates.certificate687009.1
private theorem cert9_iota : iotaCheck () = true := Certificates.certificate687009.2.1
private theorem cert9_partner : partnerCheck () = true :=
  Certificates.certificate687009.2.2.1
private theorem cert9_gen : hGenCheck () = true := Certificates.certificate687009.2.2.2.1
private theorem cert9_inv : invsOK 51 (dEnum ()).tabs (dEnumInv ()) = true :=
  Certificates.certificate687009.2.2.2.2.1
private theorem cert9_cover : cover24Check () = true :=
  Certificates.certificate687009.2.2.2.2.2.1
private theorem cert9_aut : autCheck () = true := Certificates.certificate687009.2.2.2.2.2.2

theorem mem_outList (k : OutD) : k ∈ outList := by
  obtain ⟨k, b⟩ := k
  cases k <;> cases b <;> decide

private theorem pi_facts (k : OutD) :
    CFSG.ONSchreier.Native.pisInv 51 (piTab k) (invTab 51 (piTab k)) = true ∧
      (piTab k).size = 51 ∧ (invTab 51 (piTab k)).size = 51 ∧
      (∀ j : Fin 6, conjOK (invTab 51 (piTab k)) (piTab k) letArr[j.val]!
        (wTab letArr (letInv ()) (wYD k j)) = true) ∧
      conjOK (piTab k) (invTab 51 (piTab k)) letArr[0]! letArr[0]! = true ∧
      conjOK (piTab k) (invTab 51 (piTab k)) letArr[5]! letArr[5]! = true := by
  have h := cert9_pi
  simp only [piCheck, List.all_eq_true, Bool.and_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h k (mem_outList k)
  exact ⟨h1, beq_iff_eq.1 h2, beq_iff_eq.1 h3, h4, h5, h6⟩

theorem tabRep_piP (k : OutD) : TabRep (piTab k) (piP k) :=
  ⟨(pi_facts k).2.1, (CFSG.ONSchreier.prep_permOfArr (pi_facts k).1).1⟩

theorem tabRep_piP_inv (k : OutD) : TabRep (invTab 51 (piTab k)) (piP k)⁻¹ :=
  ⟨(pi_facts k).2.2.1, (CFSG.ONSchreier.prep_permOfArr (pi_facts k).1).2⟩

theorem piP_conj_letter (k : OutD) (j : Fin 6) :
    (piP k)⁻¹ * dP j * piP k = wprod dP (wYD k j) := by
  have h := (pi_facts k).2.2.2.1 j
  rw [conjOK] at h
  exact (((tabRep_piP_inv k).comp (tabRep_dP j)).comp (tabRep_piP k)).beq_iff
    (tabRep_wTab tabRep_dP tabRep_letInv _) |>.1 h

theorem piP_mem_normalizer (k : OutD) :
    piP k ∈ Subgroup.normalizer (DP : Set (Equiv.Perm (Fin 51))) := by
  have h := mem_normalizer_of_conj_le (g := (piP k)⁻¹) fun j => by
    rw [inv_inv, piP_conj_letter, ← coe_wprod_dPD]
    exact (wprod dPD (wYD k j)).2
  simpa using Subgroup.inv_mem _ h

private theorem iota_facts :
    CFSG.ONSchreier.Native.pisInv 51 iotaTab (invTab 51 iotaTab) = true ∧
      iotaTab.size = 51 ∧ (invTab 51 iotaTab).size = 51 ∧
      ∀ j : Fin 6, conjOK iotaTab (invTab 51 iotaTab) letArr[j.val]!
        (if j.val == 5 then (letInv ())[5]! else letArr[j.val]!) = true := by
  have h := cert9_iota
  simp only [iotaCheck, List.all_eq_true, Bool.and_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, beq_iff_eq.1 h2, beq_iff_eq.1 h3, h4⟩

theorem tabRep_iotaP0 : TabRep iotaTab iotaP0 :=
  ⟨iota_facts.2.1, (CFSG.ONSchreier.prep_permOfArr iota_facts.1).1⟩

theorem tabRep_iotaP0_inv : TabRep (invTab 51 iotaTab) iotaP0⁻¹ :=
  ⟨iota_facts.2.2.1, (CFSG.ONSchreier.prep_permOfArr iota_facts.1).2⟩

theorem iotaP0_conj (j : Fin 6) :
    iotaP0 * dP j * iotaP0⁻¹ = if j = 5 then (dP 5)⁻¹ else dP j := by
  have h := iota_facts.2.2.2 j
  rw [conjOK] at h
  have hl := (tabRep_iotaP0.comp (tabRep_dP j)).comp tabRep_iotaP0_inv
  by_cases hj : j = 5
  · subst hj
    rw [if_pos rfl]
    have h' : (if (5 : Fin 6).val == 5 then (letInv ())[5]! else letArr[(5 : Fin 6).val]!) =
        (letInv ())[5]! := rfl
    rw [h'] at h
    exact (hl.beq_iff (tabRep_letInv 5)).1 h
  · have hj' : (j.val == 5) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun h' => hj (Fin.ext h')
    rw [if_neg hj]
    simp only [hj', Bool.false_eq_true, ↓reduceIte] at h
    exact (hl.beq_iff (tabRep_dP j)).1 h

theorem iotaP0_mem_normalizer :
    iotaP0 ∈ Subgroup.normalizer (DP : Set (Equiv.Perm (Fin 51))) := by
  refine mem_normalizer_of_conj_le fun j => ?_
  rw [iotaP0_conj]
  split_ifs
  · exact DP.inv_mem (dP_mem 5)
  · exact dP_mem j

noncomputable def fP (k : OutD) : ↥DP ≃* ↥DP :=
  DP.normalizerMonoidHom ⟨piP k, piP_mem_normalizer k⟩

noncomputable def iotaP : ↥DP ≃* ↥DP := DP.normalizerMonoidHom ⟨iotaP0, iotaP0_mem_normalizer⟩

theorem fP_apply (k : OutD) (x : ↥DP) :
    (fP k x : Equiv.Perm (Fin 51)) = piP k * x * (piP k)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

theorem iotaP_apply (x : ↥DP) : (iotaP x : Equiv.Perm (Fin 51)) = iotaP0 * x * iotaP0⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

theorem fP_symm_letter (k : OutD) (j : Fin 6) : (fP k).symm (dPD j) = wprod dPD (wYD k j) := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [fP_apply, coe_wprod_dPD, ← piP_conj_letter]
  simp [mul_assoc]

theorem iotaP_letter (j : Fin 6) (hj : j ≠ 5) : iotaP (dPD j) = dPD j :=
  Subtype.ext (by rw [iotaP_apply, coe_dPD, iotaP0_conj, if_neg hj])

theorem iotaP_t : iotaP (dPD 5) = (dPD 5)⁻¹ :=
  Subtype.ext (by rw [iotaP_apply, coe_dPD, iotaP0_conj, if_pos rfl]; rfl)

theorem partnerP (k : Twist) (x : ↥DP) :
    fP (k, false) x =
      iotaP (fP (k, true) ((wprod dPD (mWord k))⁻¹ * x * wprod dPD (mWord k))) := by
  set m := wprod dPD (mWord k) with hm
  have h : (fP (k, false)).toMonoidHom = iotaP.toMonoidHom.comp
      ((fP (k, true)).toMonoidHom.comp (MulAut.conj m⁻¹).toMonoidHom) := by
    apply DP_hom_ext
    intro j
    apply Subtype.ext
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [fP_apply, iotaP_apply, fP_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_dPD, hm, coe_wprod_dPD]
    have hc := cert9_partner
    simp only [partnerCheck, List.all_eq_true, beq_iff_eq, List.mem_finRange, forall_const,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    have hk := hc k (by cases k <;> simp)
    have hmt := tabRep_wTab tabRep_dP tabRep_letInv (mWord k)
    have hmi := tabRep_wTab tabRep_dP tabRep_letInv (FreeGroup.invRev (mWord k))
    rw [wprod_invRev] at hmi
    have hl := ((tabRep_piP (k, false)).comp (tabRep_dP j)).comp (tabRep_piP_inv (k, false))
    have hr := ((tabRep_iotaP0.comp (((tabRep_piP (k, true)).comp
      ((hmi.comp (tabRep_dP j)).comp hmt)).comp (tabRep_piP_inv (k, true)))).comp
        tabRep_iotaP0_inv)
    exact (hl.eq_iff hr).1 (hk j)
  have := congrArg (fun φ => φ x) h
  simpa [MulAut.conj_apply] using this

noncomputable def hP (i : Fin 2) : ↥DP := wprod dPD (hW i)

noncomputable def x1P : ↥DP := wprod dPD x1W

theorem tabRep_tpow {x : Tab} {g : Equiv.Perm (Fin 51)} (h : TabRep x g) (n : ℕ) :
    TabRep (tpow x n) (g ^ n) := by
  induction n with
  | zero => exact TabRep.idTab
  | succ n ih => rw [pow_succ']; exact h.comp ih

theorem ord24_iff {x : Tab} {g : Equiv.Perm (Fin 51)} (h : TabRep x g) :
    ord24 x = true ↔ g ^ 24 = 1 ∧ g ^ 12 ≠ 1 ∧ g ^ 8 ≠ 1 := by
  simp only [ord24, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
    (tabRep_tpow h 24).beq_iff TabRep.idTab, (tabRep_tpow h 12).beq_iff TabRep.idTab,
    (tabRep_tpow h 8).beq_iff TabRep.idTab]
  tauto

private theorem gen_facts :
    (∀ j : Fin 6, wTab #[hTab 0, hTab 1] #[hInv 0, hInv 1] (lW j) = letArr[j.val]!) ∧
      ord24 (hTab 0) = true ∧
      ∀ S ∈ autTests, wTab #[hTab 0, hTab 1] #[hInv 0, hInv 1] S = idTab 51 := by
  have h := cert9_gen
  simp only [hGenCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem tabRep_hP : ∀ i : Fin 2,
    TabRep (#[hTab 0, hTab 1] : Array Tab)[i.val]! ((hP i : ↥DP) : Equiv.Perm (Fin 51)) := by
  intro i
  fin_cases i
  · exact tabRep_wTab_dP (hW 0)
  · exact tabRep_wTab_dP (hW 1)

theorem tabRep_hP_inv : ∀ i : Fin 2,
    TabRep (#[hInv 0, hInv 1] : Array Tab)[i.val]! ((hP i : ↥DP) : Equiv.Perm (Fin 51))⁻¹ := by
  intro i
  have h := fun i => tabRep_wTab_dP (FreeGroup.invRev (hW i))
  simp only [wprod_invRev, Subgroup.coe_inv] at h
  fin_cases i
  · exact h 0
  · exact h 1

theorem coe_wprod_hP (w : List (Fin 2 × Bool)) :
    ((wprod hP w : ↥DP) : Equiv.Perm (Fin 51)) =
      wprod (fun i => ((hP i : ↥DP) : Equiv.Perm (Fin 51))) w :=
  map_wprod DP.subtype hP w

theorem wprod_hP_lW (j : Fin 6) : wprod hP (lW j) = dPD j := by
  apply Subtype.ext
  rw [coe_wprod_hP]
  have h := (tabRep_wTab tabRep_hP tabRep_hP_inv (lW j))
  rw [gen_facts.1 j] at h
  exact h.perm_eq (tabRep_dP j)

theorem wprod_hP_tests (S : List (Fin 2 × Bool)) (hS : S ∈ autTests) : wprod hP S = 1 := by
  apply Subtype.ext
  rw [coe_wprod_hP]
  have h := (tabRep_wTab tabRep_hP tabRep_hP_inv S)
  rw [gen_facts.2.2 S hS] at h
  exact h.perm_eq TabRep.idTab

theorem hom_ext_hP {H : Type*} [Group H] {φ ψ : ↥DP →* H} (h0 : φ (hP 0) = ψ (hP 0))
    (h1 : φ (hP 1) = ψ (hP 1)) : φ = ψ := by
  have h : ∀ i, φ (hP i) = ψ (hP i) := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
  apply DP_hom_ext
  intro j
  rw [← wprod_hP_lW j, map_wprod, map_wprod]
  simp only [h]

theorem tabRep_hTab (i : Fin 2) : TabRep (hTab i) ((hP i : ↥DP) : Equiv.Perm (Fin 51)) :=
  tabRep_wTab_dP (hW i)

theorem tabRep_hInv (i : Fin 2) : TabRep (hInv i) (((hP i)⁻¹ : ↥DP) : Equiv.Perm (Fin 51)) := by
  have h := tabRep_wTab_dP (FreeGroup.invRev (hW i))
  rwa [wprod_invRev] at h

theorem tabRep_x1Tab : TabRep (x1Tab ()) ((x1P : ↥DP) : Equiv.Perm (Fin 51)) :=
  tabRep_wTab_dP x1W

theorem tabRep_x1Inv : TabRep (x1Inv ()) ((x1P⁻¹ : ↥DP) : Equiv.Perm (Fin 51)) := by
  have h := tabRep_wTab_dP (FreeGroup.invRev x1W)
  rwa [wprod_invRev] at h

theorem tabRep_twTab (k : OutD) (i : Fin 2) :
    TabRep (twTab k i) ((fP k (hP i) : ↥DP) : Equiv.Perm (Fin 51)) := by
  rw [fP_apply]
  exact ((tabRep_piP k).comp (tabRep_hTab i)).comp (tabRep_piP_inv k)

theorem exists_of_autPairOK {xt xit : Tab} {x₀ : ↥DP}
    (hx : TabRep xt (x₀ : Equiv.Perm (Fin 51)))
    (hxi : TabRep xit ((x₀⁻¹ : ↥DP) : Equiv.Perm (Fin 51)))
    (hpair : ∀ i < (dEnum ()).tabs.size, autPairOK (twList ()) (dEnum ()) (dEnumInv ()) xt xit
      (dEnum ()).tabs[i]! (dEnumInv ())[i]! = true)
    (y : ↥DP) (hy : ∀ S ∈ autTests, wprod ![x₀, y] S = 1) :
    ∃ (k : OutD) (m : ↥DP), m * fP k (hP 0) * m⁻¹ = x₀ ∧ m * fP k (hP 1) * m⁻¹ = y := by
  obtain ⟨i, hi, hyi⟩ := enumerates_DP.exists_pos y.2
  have hyinv : TabRep (dEnumInv ())[i]! ((y⁻¹ : ↥DP) : Equiv.Perm (Fin 51)) := by
    rw [Subgroup.coe_inv]
    exact invsOK_spec cert9_inv hi hyi
  have h := hpair i hi
  rw [autPairOK] at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, anyBelow_eq_true,
    Bool.and_eq_true] at h
  rcases h with h | ⟨f, hf, mi, hmi, h1, h2⟩
  · exfalso
    have hall : (autTests.all fun S =>
        wTab #[xt, (dEnum ()).tabs[i]!] #[xit, (dEnumInv ())[i]!] S == idTab 51) = true := by
      rw [List.all_eq_true]
      intro S hS
      have hG : ∀ j : Fin 2, TabRep (#[xt, (dEnum ()).tabs[i]!] : Array Tab)[j.val]!
          ((![x₀, y] j : ↥DP) : Equiv.Perm (Fin 51)) := by
        intro j
        fin_cases j
        · exact hx
        · exact hyi
      have hGI : ∀ j : Fin 2, TabRep (#[xit, (dEnumInv ())[i]!] : Array Tab)[j.val]!
          ((![x₀, y] j : ↥DP) : Equiv.Perm (Fin 51))⁻¹ := by
        intro j
        fin_cases j
        · simpa using hxi
        · simpa using hyinv
      have hw := tabRep_wTab hG hGI S
      have e : wprod (fun j => ((![x₀, y] j : ↥DP) : Equiv.Perm (Fin 51))) S =
          ((wprod ![x₀, y] S : ↥DP) : Equiv.Perm (Fin 51)) := (map_wprod DP.subtype _ S).symm
      rw [e, hy S hS] at hw
      exact (hw.beq_iff TabRep.idTab).2 rfl
    rw [hall] at h
    exact Bool.noConfusion h
  · rw [twList, List.mem_map] at hf
    obtain ⟨k, -, rfl⟩ := hf
    obtain ⟨m, hm, hmt⟩ := enumerates_DP.exists_elt hmi
    have hmi' := invsOK_spec cert9_inv hmi hmt
    refine ⟨k, ⟨m, hm⟩, Subtype.ext ?_, Subtype.ext ?_⟩
    · rw [conjOK] at h1
      exact (((hmt.comp (tabRep_twTab k 0)).comp hmi').beq_iff hx).1 h1
    · rw [conjOK] at h2
      exact (((hmt.comp (tabRep_twTab k 1)).comp hmi').beq_iff hyi).1 h2

theorem aut_of_root {xt xit : Tab} {x₀ : ↥DP} (hx : TabRep xt (x₀ : Equiv.Perm (Fin 51)))
    (hxi : TabRep xit ((x₀⁻¹ : ↥DP) : Equiv.Perm (Fin 51)))
    (hpair : ∀ i < (dEnum ()).tabs.size, autPairOK (twList ()) (dEnum ()) (dEnumInv ()) xt xit
      (dEnum ()).tabs[i]! (dEnumInv ())[i]! = true)
    (α : ↥DP ≃* ↥DP) (c : ↥DP) (hc : α (hP 0) = c * x₀ * c⁻¹) :
    ∃ (k : OutD) (m : ↥DP), ∀ x, α x = m * fP k x * m⁻¹ := by
  set φ : ↥DP →* ↥DP := (MulAut.conj c⁻¹).toMonoidHom.comp α.toMonoidHom with hφ
  have hφx : ∀ x, φ x = c⁻¹ * α x * c := fun x => by simp [hφ, MulAut.conj_apply]
  have hφ0 : φ (hP 0) = x₀ := by rw [hφx, hc]; group
  have hy : ∀ S ∈ autTests, wprod ![x₀, φ (hP 1)] S = 1 := by
    intro S hS
    have h := congrArg φ (wprod_hP_tests S hS)
    rw [map_wprod, map_one] at h
    rw [← h]
    congr 1
    funext i
    fin_cases i
    · exact hφ0.symm
    · rfl
  obtain ⟨k, m, h0, h1⟩ := exists_of_autPairOK hx hxi hpair (φ (hP 1)) hy
  refine ⟨k, c * m, fun x => ?_⟩
  have hext : α.toMonoidHom = (MulAut.conj (c * m)).toMonoidHom.comp (fP k).toMonoidHom := by
    apply hom_ext_hP
    · simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulAut.conj_apply, hc, ← h0]
      group
    · have h' : α (hP 1) = c * φ (hP 1) * c⁻¹ := by rw [hφx]; group
      simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulAut.conj_apply, h', ← h1]
      group
  have := congrArg (fun ψ => ψ x) hext
  simpa [MulAut.conj_apply, mul_assoc] using this

theorem autP (α : ↥DP ≃* ↥DP) : ∃ (k : OutD) (m : ↥DP), ∀ x, α x = m * fP k x * m⁻¹ := by
  have h24 := (ord24_iff (tabRep_hTab 0)).1 gen_facts.2.1
  have key : ∀ n : ℕ, ((α (hP 0) : ↥DP) : Equiv.Perm (Fin 51)) ^ n = 1 ↔
      ((hP 0 : ↥DP) : Equiv.Perm (Fin 51)) ^ n = 1 := by
    intro n
    rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, OneMemClass.coe_eq_one, OneMemClass.coe_eq_one,
      ← map_pow, MulEquiv.map_eq_one_iff]
  have hX24 : ((α (hP 0) : ↥DP) : Equiv.Perm (Fin 51)) ^ 24 = 1 ∧
      ((α (hP 0) : ↥DP) : Equiv.Perm (Fin 51)) ^ 12 ≠ 1 ∧
      ((α (hP 0) : ↥DP) : Equiv.Perm (Fin 51)) ^ 8 ≠ 1 := by
    exact ⟨(key 24).2 h24.1, fun h => h24.2.1 ((key 12).1 h), fun h => h24.2.2 ((key 8).1 h)⟩
  obtain ⟨i, hi, hXi⟩ := enumerates_DP.exists_pos (α (hP 0)).2
  have hc := cert9_cover
  simp only [cover24Check, Bool.and_eq_true, allBelow_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hc
  obtain ⟨⟨ho0, ho1⟩, hall⟩ := hc
  have ha := cert9_aut
  simp only [autCheck, allBelow_eq_true, Bool.and_eq_true] at ha
  have hord := (ord24_iff hXi).2 hX24
  have hA : ∀ a ∈ Set.range dP, ∃ j < letArr.size, TabRep letArr[j]! a := by
    rintro _ ⟨j, rfl⟩
    exact ⟨j.val, by rw [letArr_size_eq]; exact j.isLt, tabRep_dP j⟩
  have hgens : ∀ j < letArr.size, ∃ a ∈ Set.range dP, TabRep letArr[j]! a := by
    intro j hj
    rw [letArr_size_eq] at hj
    exact ⟨dP ⟨j, hj⟩, ⟨⟨j, hj⟩, rfl⟩, tabRep_dP ⟨j, hj⟩⟩
  rcases hall i hi with (h | h) | h
  · rw [hord] at h
    exact Bool.noConfusion h
  · obtain ⟨hcl, -, -⟩ := conj_orbit hA hgens (tabRep_hTab 0) ho0
    obtain ⟨c, hcm, hcr⟩ := hcl _ (mem_of_found h)
    exact aut_of_root (tabRep_hTab 0) (tabRep_hInv 0) (fun i hi => (ha i hi).1) α ⟨c, hcm⟩
      (Subtype.ext (hXi.perm_eq hcr))
  · obtain ⟨hcl, -, -⟩ := conj_orbit hA hgens tabRep_x1Tab ho1
    obtain ⟨c, hcm, hcr⟩ := hcl _ (mem_of_found h)
    exact aut_of_root tabRep_x1Tab tabRep_x1Inv (fun i hi => (ha i hi).2) α ⟨c, hcm⟩
      (Subtype.ext (hXi.perm_eq hcr))

end AutP

section AutD

noncomputable def fAut (k : OutD) : ↥DJ ≃* ↥DJ := eDP.symm.trans ((fP k).trans eDP)

noncomputable def iotaD : ↥DJ ≃* ↥DJ := eDP.symm.trans (iotaP.trans eDP)

noncomputable def mD (k : Twist) : ↥DJ := wprod dJD (mWord k)

theorem eDP_symm_letter (j : Fin 6) : eDP.symm (dJD j) = dPD j := by
  rw [MulEquiv.symm_apply_eq, eDP_letter]

theorem fAut_symm_letter (k : OutD) (j : Fin 6) :
    ((fAut k).symm (dJD j) : J) = wprod dJ (wYD k j) := by
  have h : (fAut k).symm (dJD j) = eDP ((fP k).symm (dPD j)) := by
    simp [fAut, MulEquiv.symm_trans_apply, eDP_symm_letter]
  rw [h, fP_symm_letter, eDP_wprod, coe_wprod_dJD]

theorem fAut_symm_letter_twist (k : Twist) (j : Fin 6) :
    ((fAut (k, false)).symm (dJD j) : J) = wprod hswJ (wY k j) := by
  rw [fAut_symm_letter, ← wYD_twist, wprod_comp_letters]
  rfl

theorem iotaD_letter (j : Fin 6) (hj : j ≠ 5) : iotaD (dJD j) = dJD j := by
  simp only [iotaD, MulEquiv.trans_apply, eDP_symm_letter, iotaP_letter j hj, eDP_letter]

theorem iotaD_t : iotaD (dJD 5) = (dJD 5)⁻¹ := by
  simp only [iotaD, MulEquiv.trans_apply, eDP_symm_letter, iotaP_t, map_inv, eDP_letter]

theorem eDP_symm_mD (k : Twist) : eDP.symm (mD k) = wprod dPD (mWord k) := eDP_symm_wprod _

theorem partner (k : Twist) (x : ↥DJ) :
    fAut (k, false) x = iotaD (fAut (k, true) ((mD k)⁻¹ * x * mD k)) := by
  simp only [fAut, iotaD, MulEquiv.trans_apply, map_mul, map_inv, eDP_symm_mD,
    MulEquiv.symm_apply_apply, partnerP k (eDP.symm x)]

theorem aut_DJ (α : ↥DJ ≃* ↥DJ) : ∃ (k : OutD) (m : ↥DJ), ∀ x, α x = m * fAut k x * m⁻¹ := by
  obtain ⟨k, m, hm⟩ := autP (eDP.trans (α.trans eDP.symm))
  refine ⟨k, eDP m, fun x => ?_⟩
  have h := congrArg eDP (hm (eDP.symm x))
  simpa [fAut, MulEquiv.trans_apply] using h

end AutD

end CFSG.Sporadic.Th.Recog
