module

public import CFSG.Quasithin.Vol2.KGFactC31RuCoverNative
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Words
public import CFSG.Sporadic.Schreier.RuIso
public import CFSG.Sporadic.Schreier.RuCenters
public import CFSG.Sporadic.J4.QTElem
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.FourthPowerFacts

public section

namespace CFSG.Quasithin.KGC31.RuCover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits CFSG.Sporadic.Recognition.RuMultiplier
  CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.TwoRu CFSG.Sporadic.J4.QT
open scoped commutatorElement

theorem rep_prodA_aux {n : ℕ} {S : Array (Array ℕ)} {u : ℕ → Equiv.Perm (Fin n)}
    (hS : ∀ j < 3, Rep n S[j]! (u j)) (c : ℕ) : ∀ m ≤ 3,
    Rep n ((List.range m).foldl (fun acc j => if c.testBit j then compA n acc S[j]! else acc)
      (idA n)) (eta u m c)
  | 0, _ => by simpa [eta] using (rep_idA (n := n))
  | m + 1, hm => by
    rw [List.range_succ, List.foldl_append, eta_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs with h
    · exact rep_compA (rep_prodA_aux hS c m (by omega)) (hS m (by omega))
    · rw [mul_one]
      exact rep_prodA_aux hS c m (by omega)

theorem rep_prodA {n : ℕ} {S : Array (Array ℕ)} {u : ℕ → Equiv.Perm (Fin n)}
    (hS : ∀ j < 3, Rep n S[j]! (u j)) (c : ℕ) : Rep n (prodA n S c) (eta u 3 c) :=
  rep_prodA_aux hS c 3 le_rfl

theorem map_eta {G H : Type*} [Group G] [Group H] (f : G →* H) (u : ℕ → G) (c : ℕ) :
    ∀ m, f (eta u m c) = eta (fun j => f (u j)) m c
  | 0 => by simp [eta]
  | m + 1 => by
    rw [eta_succ, eta_succ, map_mul, map_eta f u c m]
    split_ifs <;> simp

@[expose] noncomputable def pGen (h : ℕ) : RuCover := if h = 0 then ruP0E else ruWE ruP1

@[expose] noncomputable def pElt (w : List ℤ) : RuCover := wordIn 2 pGen w

theorem pA_get0 : (pA ())[0]! = ruWordArr ruP0 := by simp [pA, p0A, ruWordArr]

theorem pA_get1 : (pA ())[1]! = ruWordArr ruP1 := by simp [pA, p1A, ruWordArr]

theorem eArr_get : ∀ i < 3, (eArr ())[i]! = eA i := by
  intro i hi
  interval_cases i <;> simp [eArr]

theorem nArr_get : ∀ j < 2, (nArr ())[j]! = nA j := by
  intro j hj
  interval_cases j <;> simp [nArr]

theorem aA_get0 : (aA ())[0]! = ruA0A := by simp [aA]

theorem aA_get1 : (aA ())[1]! = ruA1A := by simp [aA]

section Check

variable (hc : coverChk () = true)
include hc

theorem chk16240_parts :
    lettersOK gc (zword ruP0) = true ∧ lettersOK gc (zword ruP1) = true ∧
      allPermsOK 16240 (pA ()) = true ∧ (∀ i < 3, lettersOK 2 (eW.getD i []) = true) ∧
      (∀ j < 2, lettersOK 2 (nW.getD j []) = true) ∧ allPermsOK 16240 (nArr ()) = true ∧
      (∀ i < 3, eqA 16240 (compA 16240 (eArr ())[i]! (eArr ())[i]!) (idA 16240) = true) ∧
      (∀ i < 3, ∀ j < 3, eqA 16240 (compA 16240 (eArr ())[i]! (eArr ())[j]!)
        (compA 16240 (eArr ())[j]! (eArr ())[i]!) = true) ∧
      (∀ c < 8, eqA 16240 (prodA 16240 (eArr ()) c) (zA ()) = false) ∧
      ∀ j < 2, ∀ i < 3, eqA 16240 (compA 16240 (compA 16240 (nArr ())[j]! (eArr ())[i]!)
        (invCand 16240 (nArr ())[j]!)) (prodA 16240 (eArr ()) ((tabC.getD j []).getD i 0)) =
          true := by
  have h := ((Bool.and_eq_true _ _).mp hc).1
  unfold coverChk16240 at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem chk4060_parts :
    allPermsOK 4060 (aA ()) = true ∧
      (∀ i < 3, eqA 4060 (wordArr 4060 (aA ()) (eW.getD i [])) ruEArr[i]! = true) ∧
      eqA 4060 (wordArr 4060 (aA ()) (nW.getD 0 [])) ruNs0A = true ∧
      eqA 4060 (wordArr 4060 (aA ()) (nW.getD 1 [])) ruNs1A = true ∧
      ∀ k < 7, eqA 4060 ruEArr[k]! (prodA 4060 #[ruEArr[0]!, ruEArr[1]!, ruEArr[2]!]
        (eCode.getD k 0)) = true := by
  have h := ((Bool.and_eq_true _ _).mp hc).2
  unfold coverChk4060 at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

variable (hRho : ruRhoCheck = true)

theorem rep_pGen : ∀ h < 2, Rep 16240 (pA ())[h]! (ruRho' hRho (pGen h)) := by
  obtain ⟨h1, h2, -⟩ := chk16240_parts hc
  intro h hh
  interval_cases h
  · rw [pA_get0]
    exact rep_ruRho_ruWE hRho h1
  · rw [pA_get1]
    exact rep_ruRho_ruWE hRho h2

omit hc in
theorem ruRho'_pElt (w : List ℤ) :
    ruRho' hRho (pElt w) = wordIn 2 (fun h => ruRho' hRho (pGen h)) w := by
  rw [pElt, wordIn, wordIn, evalWord_map]
  rfl

theorem rep_pElt {w : List ℤ} (hw : lettersOK 2 w = true) :
    Rep 16240 (wordArr 16240 (pA ()) w) (ruRho' hRho (pElt w)) := by
  obtain ⟨-, -, h3, -⟩ := chk16240_parts hc
  rw [ruRho'_pElt]
  exact rep_wordArr (k := 2) (by decide) (rep_pGen hc hRho)
    (fun i hi => isInvA_of_allPermsOK h3 (by have : (pA ()).size = 2 := rfl; omega)) hw

theorem rep_eA : ∀ i < 3, Rep 16240 (eArr ())[i]! (ruRho' hRho (pElt (eW.getD i []))) := by
  obtain ⟨-, -, -, h4, -⟩ := chk16240_parts hc
  intro i hi
  rw [eArr_get i hi]
  exact rep_pElt hc hRho (h4 i hi)

theorem rep_nA : ∀ j < 2, Rep 16240 (nArr ())[j]! (ruRho' hRho (pElt (nW.getD j []))) := by
  obtain ⟨-, -, -, -, h5, -⟩ := chk16240_parts hc
  intro j hj
  rw [nArr_get j hj]
  exact rep_pElt hc hRho (h5 j hj)

theorem rep_zA : Rep 16240 (zA ()) (ruRho' hRho (ruWE ruZWord)) := by
  have hz : ruWE ruZWord = ruWE ruP0 * ruWE ruP0 := by rw [ruZWord, ruWE_append]
  rw [hz, map_mul]
  have h0 := rep_pGen hc hRho 0 (by norm_num)
  exact rep_compA h0 h0

omit hc hRho in
theorem ruJtoP_p0 (hTab : RuTabFact) : ruJtoP (ruπ hTab (pGen 0)) = ruA0 := by
  have e : pGen 0 = ruP0E := by simp [pGen]
  rw [e, ruπ_ruP0E hTab]
  exact ruJtoP_a

omit hc hRho in
theorem ruJtoP_p1 (hTab : RuTabFact) : ruJtoP (ruπ hTab (pGen 1)) = ruA1 := by
  have e : pGen 1 = PresentedGroup.mk _ (FreeGroup.mk ruP1) := by simp [pGen, ruWE]
  rw [e, ruπ_mk hTab, ruP1, lift_ruGen_surjB]
  exact ruJtoP_b

omit hRho in
theorem rep_pElt4060 (hTab : RuTabFact) {w : List ℤ} (hw : lettersOK 2 w = true) :
    Rep 4060 (wordArr 4060 (aA ()) w) (ruJtoP (ruπ hTab (pElt w))) := by
  obtain ⟨h1, -⟩ := chk4060_parts hc
  have e : ruJtoP (ruπ hTab (pElt w)) =
      wordIn 2 (fun h => ruJtoP (ruπ hTab (pGen h))) w := by
    rw [pElt, wordIn, wordIn, ← MonoidHom.comp_apply, evalWord_map]
    rfl
  rw [e]
  refine rep_wordArr (k := 2) (by decide) (fun h hh => ?_)
    (fun i hi => isInvA_of_allPermsOK h1 (by have : (aA ()).size = 2 := rfl; omega)) hw
  interval_cases h
  · rw [aA_get0, ruJtoP_p0 hTab]
    exact rep_ruA0
  · rw [aA_get1, ruJtoP_p1 hTab]
    exact rep_ruA1

omit hRho in
theorem ruJtoP_eW (hTab : RuTabFact) :
    ∀ i < 3, ruJtoP (ruπ hTab (pElt (eW.getD i []))) = ruEElt i := by
  obtain ⟨-, -, -, h4, -⟩ := chk16240_parts hc
  obtain ⟨-, h2, -⟩ := chk4060_parts hc
  intro i hi
  exact eq_of_eqA (rep_pElt4060 hc hTab (h4 i hi)) (rep_ruEElt (by omega)) (h2 i hi)

omit hRho in
theorem ruJtoP_nW0 (hTab : RuTabFact) :
    ruJtoP (ruπ hTab (pElt (nW.getD 0 []))) = ruNs0 := by
  obtain ⟨-, -, -, -, h5, -⟩ := chk16240_parts hc
  obtain ⟨-, -, h3, -⟩ := chk4060_parts hc
  exact eq_of_eqA (rep_pElt4060 hc hTab (h5 0 (by norm_num))) rep_ruNs0 h3

omit hRho in
theorem ruJtoP_nW1 (hTab : RuTabFact) :
    ruJtoP (ruπ hTab (pElt (nW.getD 1 []))) = ruNs1 := by
  obtain ⟨-, -, -, -, h5, -⟩ := chk16240_parts hc
  obtain ⟨-, -, -, h4, -⟩ := chk4060_parts hc
  exact eq_of_eqA (rep_pElt4060 hc hTab (h5 1 (by norm_num))) rep_ruNs1 h4

omit hRho
  in
theorem ruEElt_eq_eta : ∀ k < 7, ruEElt k = eta ruEElt 3 (eCode.getD k 0) := by
  obtain ⟨-, -, -, -, h5⟩ := chk4060_parts hc
  intro k hk
  have g : ∀ a b c : Array ℕ,
      (#[a, b, c])[0]! = a ∧ (#[a, b, c])[1]! = b ∧ (#[a, b, c])[2]! = c :=
    fun _ _ _ => ⟨rfl, rfl, rfl⟩
  refine eq_of_eqA (rep_ruEElt hk) (rep_prodA (fun j hj => ?_) _) (h5 k hk)
  interval_cases j
  · rw [(g _ _ _).1]
    exact rep_ruEElt (by norm_num)
  · rw [(g _ _ _).2.1]
    exact rep_ruEElt (by norm_num)
  · rw [(g _ _ _).2.2]
    exact rep_ruEElt (by norm_num)

end Check

theorem inf_ker_eq_bot {L Q : Type*} [Group L] [Finite L] [Group Q] (θ : L →* Q) {t : L}
    (ht : orderOf t = 2) (hker : θ.ker = Subgroup.zpowers t)
    (hcen : Subgroup.zpowers t ≤ Subgroup.center L) {e n : ℕ → L} (he : Elem e 3)
    (hconj : ∀ j < 2, ∀ i < 3, n j * e i * (n j)⁻¹ = eta e 3 ((tabC.getD j []).getD i 0))
    (het : ∀ c < 8, eta e 3 c ≠ t) {V M₀ : Subgroup L}
    (hV : ∀ v ∈ V, ∃ c, θ v = θ (eta e 3 c))
    (hM : ∀ m ∈ M₀, ∃ w ∈ Subgroup.closure {n 0, n 1}, θ m = θ w) (hVM : ⁅V, M₀⁆ = V) :
    V ⊓ θ.ker = ⊥ := by
  set U := Eg e 3 with hU
  have hnU : ∀ j < 2, ∀ u ∈ U, n j * u * (n j)⁻¹ ∈ U := by
    intro j hj u hu
    obtain ⟨c, -, rfl⟩ := (mem_Eg_iff he).1 hu
    rw [conj_eta he (n j) (fun i => (tabC.getD j []).getD i 0) (hconj j hj) le_rfl c]
    exact eta_mem_Eg 3 le_rfl _
  have hnorm : ∀ j < 2, n j ∈ Subgroup.normalizer (U : Set L) := by
    intro j hj
    have hle : U.map (MulAut.conj (n j)).toMonoidHom ≤ U := by
      rintro _ ⟨u, hu, rfl⟩
      exact hnU j hj u hu
    have heq := Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj (n j)).injective])
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  have hclos : Subgroup.closure {n 0, n 1} ≤ Subgroup.normalizer (U : Set L) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hnorm 0 (by norm_num)
    · exact hnorm 1 (by norm_num)
  have hcentral : ∀ z ∈ θ.ker, ∀ g : L, g * z = z * g := fun z hz =>
    Subgroup.mem_center_iff.mp (hcen (hker ▸ hz))
  have hcomm : ⁅V, M₀⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro v hv m hm
    obtain ⟨c, hcv⟩ := hV v hv
    obtain ⟨w, hw, hwm⟩ := hM m hm
    have hz₁ : (eta e 3 c)⁻¹ * v ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcv, inv_mul_cancel]
    have hz₂ : w⁻¹ * m ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwm, inv_mul_cancel]
    set z₁ := (eta e 3 c)⁻¹ * v with hz₁def
    set z₂ := w⁻¹ * m with hz₂def
    have hv' : v = eta e 3 c * z₁ := by rw [hz₁def]; group
    have hm' : m = w * z₂ := by rw [hz₂def]; group
    have h1 := hcentral z₁ hz₁
    have h2 := hcentral z₂ hz₂
    have hcm : ⁅v, m⁆ = ⁅eta e 3 c, w⁆ := by
      rw [hv', hm', commutatorElement_def, commutatorElement_def]
      calc eta e 3 c * z₁ * (w * z₂) * (eta e 3 c * z₁)⁻¹ * (w * z₂)⁻¹
          = eta e 3 c * (z₁ * w) * z₂ * z₁⁻¹ * (eta e 3 c)⁻¹ * z₂⁻¹ * w⁻¹ := by group
        _ = eta e 3 c * (w * z₁) * z₂ * z₁⁻¹ * (eta e 3 c)⁻¹ * z₂⁻¹ * w⁻¹ := by rw [h1 w]
        _ = eta e 3 c * w * (z₁ * z₂ * z₁⁻¹) * (eta e 3 c)⁻¹ * z₂⁻¹ * w⁻¹ := by group
        _ = eta e 3 c * w * (z₂ * z₁ * z₁⁻¹) * (eta e 3 c)⁻¹ * z₂⁻¹ * w⁻¹ := by rw [h2 z₁]
        _ = eta e 3 c * w * z₂ * (eta e 3 c)⁻¹ * z₂⁻¹ * w⁻¹ := by group
        _ = eta e 3 c * w * (z₂ * (eta e 3 c)⁻¹) * z₂⁻¹ * w⁻¹ := by group
        _ = eta e 3 c * w * ((eta e 3 c)⁻¹ * z₂) * z₂⁻¹ * w⁻¹ := by rw [h2 (eta e 3 c)⁻¹]
        _ = eta e 3 c * w * (eta e 3 c)⁻¹ * w⁻¹ := by group
    rw [hcm, commutatorElement_def]
    have hu : eta e 3 c ∈ U := eta_mem_Eg 3 le_rfl c
    have hwu : w * (eta e 3 c)⁻¹ * w⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hclos hw) _).mp (U.inv_mem hu)
    have e1 : eta e 3 c * w * (eta e 3 c)⁻¹ * w⁻¹ =
        eta e 3 c * (w * (eta e 3 c)⁻¹ * w⁻¹) := by group
    rw [e1]
    exact U.mul_mem hu hwu
  have hVU : V ≤ U := hVM ▸ hcomm
  rw [eq_bot_iff]
  rintro x ⟨hxV, hxK⟩
  obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff he).1 (hVU hxV)
  rw [hker] at hxK
  rcases eq_one_or_eq_of_mem_zpowers ht hxK with h1 | h1
  · rw [h1]
    exact Subgroup.one_mem _
  · exact absurd h1 (het c (by simpa using hc))

end CFSG.Quasithin.KGC31.RuCover

end
