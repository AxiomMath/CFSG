module

public import Certificates.Certificate260391
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSPerm

public section

namespace CFSG.Quasithin.B45Exc.HS

open CFSG.Quasithin.B45Exc.Tab CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Bridge.HSExcl CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem hs_syl_checks :
    hsUTab.check 4 = true ∧ hsUTab.forallGreedyI (fun _ => false) 6 [] = true ∧
      hsUTab.forallGreedyI hsPred4 4 [] = true ∧ hsUTab.forallGreedyI hsPred5 5 [] = true ∧
      hsGenWits.all (genWitOK hsGens hsUTab [hsA0A, hsA1A]) = true ∧
      hsDimWits.all dimWitOK = true :=
  Certificates.certificate260391

noncomputable abbrev hsSylPerm (j : ℕ) : Equiv.Perm (Fin 3850) := tp 3850 (hsCentTbl (j + 1))

theorem hsS_eq : hsS = Subgroup.closure {g | ∃ j < hsSylGens.length, g = hsSylPerm j} := by
  rw [hsS]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, hsSylowGenTbls, List.mem_toArray, List.mem_map,
    List.mem_range]
  constructor
  · rintro ⟨x, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, by simpa [hsSylGens] using hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨hsCentTbl (j + 1), ⟨j, by simpa [hsSylGens] using hj, rfl⟩, rfl⟩

theorem pRep_hsSylGens :
    ∀ j < hsSylGens.length, PRep 3850 (hsSylGens.getD j (pId 3850)) (hsSylPerm j) := by
  intro j hj
  have hj4 : j < 4 := by simpa [hsSylGens] using hj
  interval_cases j
  · exact pRep_hsSP (hs_perm_check.2.2 1 (by simp))
  · exact pRep_hsSP (hs_perm_check.2.2 2 (by simp))
  · exact pRep_hsSP (hs_perm_check.2.2 3 (by simp))
  · exact pRep_hsSP (hs_perm_check.2.2 4 (by simp))

theorem hsS_rec :
    ∀ x ∈ hsS, ∃ k < 1024, Rep 3850 hsSylAl[k]! x := by
  rw [hsS_eq]
  exact sylVerify_mem hs_syl_check hsSylPerm pRep_hsSylGens


theorem hsS_inv {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsS)
    (h2 : x * x = 1) (h1 : x ≠ 1) : ∃ i < hsUTab.m, x = hsUTab.perm i := by
  obtain ⟨k, hk, hrep⟩ := hsS_rec x hx
  have hkinv : k ∈ sylInv 3850 1024 hsSylAl := by
    rw [mem_sylInv]
    refine ⟨hk, fun h => h1 ((eqA_iff hrep rep_idA).1 h), ?_⟩
    exact (eqA_iff (rep_compA hrep hrep) rep_idA).2 h2
  obtain ⟨i, hi, hik⟩ := List.getElem_of_mem hkinv
  have hm : hsUTab.m = (sylInv 3850 1024 hsSylAl).length := by
    simp [InvTab.m, hsUTab, InvTab.build, hsUInv]
  have hxs : hsUTab.xs[i]! = hsSylAl[k]! := by
    have hx : hsUTab.xs = hsUInv := rfl
    rw [hx, hsUInv, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi, hik, Option.map_some, Option.getD_some]
  refine ⟨i, by rw [hm]; exact hi, ?_⟩
  have h := InvTab.rep_xs (by norm_num : 0 < 4) hs_syl_checks.1 (i := i) (by rw [hm]; exact hi)
  rw [hxs] at h
  exact hrep.unique h

theorem hsUFix_eq {i : ℕ} (hi : i < hsUTab.m) :
    (fixFinset (hsUTab.perm i)).card = hsUFix[i]! := by
  have hsz : i < hsUInv.size := hi
  have h := InvTab.rep_xs (by norm_num : 0 < 4) hs_syl_checks.1 hi
  rw [← fixCountA_eq h]
  simp [hsUFix, hsUTab, InvTab.build, hsz]

theorem hs_syl_sound {pred : List ℕ → Bool} {k : ℕ}
    (h : hsUTab.forallGreedyI pred k [] = true) (B : Subgroup (Equiv.Perm (Fin 3850)))
    (hBS : B ≤ hsS) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hcard : Nat.card B = 2 ^ k) :
    ∃ l : List ℕ, hsUTab.IsChain l ∧ pred l = true ∧
      ∀ x, x ∈ B ↔ ∃ s ∈ hsUTab.subprodsI l, x = hsUTab.perm s :=
  InvTab.forallGreedyI_sound (by norm_num) hs_syl_checks.1 h B hcomm hsq
    (fun x hx hx1 => hsS_inv (hBS hx) (hsq x hx) hx1) hcard

theorem hs_syl_card_le (B : Subgroup (Equiv.Perm (Fin 3850)))
    (hBS : B ≤ hsS) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 B := by
    intro x
    exact ⟨1, Subtype.ext (by simpa [pow_one, sq] using hsq x x.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  by_contra hlt
  push Not at hlt
  have hk6 : 6 ≤ k := by
    by_contra h6
    push Not at h6
    have : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 6) (G := ↥B)
    (by rw [hk]; exact Nat.pow_dvd_pow 2 hk6)
  set B' : Subgroup (Equiv.Perm (Fin 3850)) := K.map B.subtype with hB'
  have hcard : Nat.card B' = 2 ^ 6 := by
    rw [hB', Subgroup.card_map_of_injective (Subgroup.subtype_injective B), hK]
  have hB'B : ∀ x ∈ B', x ∈ B := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  obtain ⟨l, -, hl, -⟩ := hs_syl_sound hs_syl_checks.2.1 B' (fun x hx => hBS (hB'B x hx))
    (fun x hx y hy => hcomm x (hB'B x hx) y (hB'B y hy)) (fun x hx => hsq x (hB'B x hx)) hcard
  exact absurd hl (by decide)

theorem rep_hsA0A : Rep 3850 hsA0A (hsGen 0) := by
  have := pRep_hsA0P.1
  rwa [hsA0P_fst] at this

theorem rep_hsA1A : Rep 3850 hsA1A (hsGen 1) := by
  have := pRep_hsA1P.1
  rwa [hsA1P_fst] at this

theorem hs_gen_of_mem {w : GenWit} (hw : w ∈ hsGenWits)
    {B : Subgroup (Equiv.Perm (Fin 3850))} (hbasis : ∀ i ∈ w.basis, hsUTab.perm i ∈ B) :
    ∃ G ∈ hsP, hsP ≤ Subgroup.closure ((B : Set (Equiv.Perm (Fin 3850))) ∪
      (fun y => G * y * G⁻¹) '' (B : Set (Equiv.Perm (Fin 3850)))) := by
  have hok : genWitOK hsGens hsUTab [hsA0A, hsA1A] w = true :=
    List.all_eq_true.1 hs_syl_checks.2.2.2.2.1 w hw
  have hreg : RegIn 3850 hsP hsGens := regIn_hsP
  obtain ⟨G, hG, htgt⟩ := genWitOK_spec (by norm_num) hs_syl_checks.1 hreg hok
  refine ⟨G, hG, ?_⟩
  have hsub : regSet hsUTab w.basis G ⊆ (B : Set (Equiv.Perm (Fin 3850))) ∪
      (fun y => G * y * G⁻¹) '' (B : Set (Equiv.Perm (Fin 3850))) := by
    intro x hx
    rcases hx with ⟨i, hi, hxi⟩ | ⟨i, hi, hxi⟩
    · left
      rw [hxi]
      exact hbasis i hi
    · right
      exact ⟨_, hbasis i hi, hxi.symm⟩
  have h0 := htgt hsA0A (by simp) (hsGen 0) rep_hsA0A
  have h1 := htgt hsA1A (by simp) (hsGen 1) rep_hsA1A
  rw [hsP, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Subgroup.closure_mono hsub h0
  · exact Subgroup.closure_mono hsub h1

theorem hs_dim_of_mem {w : DimWit} (hw : w ∈ hsDimWits) :
    w.d < hsUTab.m ∧ w.c < hsUTab.m ∧ w.e < hsUTab.m ∧ w.e' < hsUTab.m ∧
      (fixFinset (hsUTab.perm w.d)).card = 46 ∧ (fixFinset (hsUTab.perm w.c)).card = 350 ∧
      ((fixFinset (hsUTab.perm w.e)).card = 170 ∨ (fixFinset (hsUTab.perm w.e)).card = 30) ∧
      ((fixFinset (hsUTab.perm w.e')).card = 170 ∨
        (fixFinset (hsUTab.perm w.e')).card = 30) ∧
      ∃ G ∈ hsP, G * hsUTab.perm w.c = hsUTab.perm w.c * G ∧
        (G * hsUTab.perm w.e * G⁻¹ * hsUTab.perm w.e') ^ 5 = 1 ∧
        G * hsUTab.perm w.e * G⁻¹ * hsUTab.perm w.e' ≠ 1 := by
  have hok : dimWitOK w = true := List.all_eq_true.1 hs_syl_checks.2.2.2.2.2 w hw
  simp only [dimWitOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hd, hc⟩, he⟩, he'⟩, hfd⟩, hfc⟩, hfe⟩, hfe'⟩, hcomm⟩, hord⟩ := hok
  have hT := hs_syl_checks.1
  refine ⟨hd, hc, he, he', (by rw [hsUFix_eq hd, hfd]), (by rw [hsUFix_eq hc, hfc]),
    (by rw [hsUFix_eq he]; exact hfe), (by rw [hsUFix_eq he']; exact hfe'), ?_⟩
  have hreg : RegIn 3850 hsP hsGens := regIn_hsP
  obtain ⟨G, hG, hGr⟩ := hreg.word w.g
  refine ⟨G, hG, ?_, ?_⟩
  · have hxc := pRep_elt (by norm_num) hT hc
    exact (eqA_iff (hGr.mul hxc).1 (hxc.mul hGr).1).1 hcomm
  · have hy : PRep 3850 (pMul 3850 (pConj 3850 (pWord 3850 hsGens w.g)
        (hsUTab.elt w.e, hsUTab.elt w.e)) (hsUTab.elt w.e', hsUTab.elt w.e'))
        (G * hsUTab.perm w.e * G⁻¹ * hsUTab.perm w.e') :=
      ((hGr.mul (pRep_elt (by norm_num) hT he)).mul hGr.inv).mul (pRep_elt (by norm_num) hT he')
    exact orderCheck_spec hy hord

theorem hs_syl_four (B : Subgroup (Equiv.Perm (Fin 3850)))
    (hBS : B ≤ hsS) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hcard : Nat.card B = 2 ^ 4) :
    (∃ x ∈ B, x ≠ 1 ∧ ((fixFinset x).card = 30 ∨ (fixFinset x).card = 46)) ∨
      ∃ G ∈ hsP, hsP ≤ Subgroup.closure ((B : Set (Equiv.Perm (Fin 3850))) ∪
        (fun y => G * y * G⁻¹) '' (B : Set (Equiv.Perm (Fin 3850)))) := by
  obtain ⟨l, -, hl, hmem⟩ := hs_syl_sound hs_syl_checks.2.2.1 B hBS hcomm hsq hcard
  have hB : ∀ s ∈ hsUTab.subprodsI l, hsUTab.perm s ∈ B := fun s hs => (hmem _).2 ⟨s, hs, rfl⟩
  simp only [hsPred4, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at hl
  rcases hl with ⟨s, hs, hsm, hfix⟩ | ⟨w, hw, hbasis⟩
  · refine Or.inl ⟨hsUTab.perm s, hB s hs, InvTab.perm_ne_one (by norm_num) hs_syl_checks.1 hsm,
      ?_⟩
    rw [hsUFix_eq hsm]
    exact hfix
  · exact Or.inr (hs_gen_of_mem hw fun i hi => hB i (hbasis i hi))

theorem hs_syl_five (B : Subgroup (Equiv.Perm (Fin 3850)))
    (hBS : B ≤ hsS) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hcard : Nat.card B = 2 ^ 5) :
    (∃ G ∈ hsP, hsP ≤ Subgroup.closure ((B : Set (Equiv.Perm (Fin 3850))) ∪
        (fun y => G * y * G⁻¹) '' (B : Set (Equiv.Perm (Fin 3850))))) ∧
      ∃ d ∈ B, ∃ c ∈ B, ∃ e ∈ B, ∃ e' ∈ B, (fixFinset d).card = 46 ∧
        (fixFinset c).card = 350 ∧ ((fixFinset e).card = 170 ∨ (fixFinset e).card = 30) ∧
        ((fixFinset e').card = 170 ∨ (fixFinset e').card = 30) ∧
        ∃ G ∈ hsP, G * c = c * G ∧ (G * e * G⁻¹ * e') ^ 5 = 1 ∧ G * e * G⁻¹ * e' ≠ 1 := by
  obtain ⟨l, -, hl, hmem⟩ := hs_syl_sound hs_syl_checks.2.2.2.1 B hBS hcomm hsq hcard
  have hB : ∀ s ∈ hsUTab.subprodsI l, hsUTab.perm s ∈ B := fun s hs => (hmem _).2 ⟨s, hs, rfl⟩
  simp only [hsPred5, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    List.contains_iff_mem] at hl
  obtain ⟨⟨w, hw, hbasis⟩, ⟨v, hv, hvs⟩⟩ := hl
  refine ⟨hs_gen_of_mem hw fun i hi => hB i (hbasis i hi), ?_⟩
  obtain ⟨-, -, -, -, hfd, hfc, hfe, hfe', G, hG, hGc, h5, h1⟩ := hs_dim_of_mem hv
  exact ⟨_, hB _ (hvs _ (by simp)), _, hB _ (hvs _ (by simp)), _, hB _ (hvs _ (by simp)),
    _, hB _ (hvs _ (by simp)), hfd, hfc, hfe, hfe', G, hG, hGc, h5, h1⟩

end CFSG.Quasithin.B45Exc.HS
