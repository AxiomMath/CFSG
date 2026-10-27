module

public import CFSG.Timmesfeld.Exceptional.SigmaFarCheckTriv
public import CFSG.Timmesfeld.Exceptional.SigmaFarCheckK24
public import CFSG.Timmesfeld.Exceptional.SigmaFarCheck7560
public import Certificates.Certificate15952
public import CFSG.Timmesfeld.Exceptional.Coxeter

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G]

namespace SigmaFar

open TwoLines

theorem conj_x₁ {x₀ x₁ c : G} (h0 : x₀ * x₀ = 1) (h1 : x₁ * x₁ = 1) (hc : c * c = 1)
    (h03 : (x₀ * c) ^ 3 = 1) (h13 : (x₁ * c) ^ 3 = 1) :
    c * x₀ * x₁ * c * x₁ * (c * x₀ * x₁ * c)⁻¹ = x₀ := by
  have b0 := braid_of_mul_pow_three h0 hc h03
  have b1 := braid_of_mul_pow_three h1 hc h13
  have hinv : (c * x₀ * x₁ * c)⁻¹ = c * x₁ * x₀ * c := by
    simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right hc, inv_eq_of_mul_eq_one_right h0,
      inv_eq_of_mul_eq_one_right h1, mul_assoc]
  rw [hinv]
  calc c * x₀ * x₁ * c * x₁ * (c * x₁ * x₀ * c)
      = c * x₀ * (x₁ * c * x₁) * c * x₁ * x₀ * c := by group
    _ = c * x₀ * (c * x₁ * c) * c * x₁ * x₀ * c := by rw [b1]
    _ = c * x₀ * c * x₁ * (c * c) * x₁ * x₀ * c := by group
    _ = c * x₀ * c * (x₁ * x₁) * x₀ * c := by rw [hc]; group
    _ = (c * x₀ * c) * x₀ * c := by rw [h1]; group
    _ = x₀ * c * x₀ * x₀ * c := by rw [← b0]
    _ = x₀ * c * (x₀ * x₀) * c := by group
    _ = x₀ := by rw [h0, mul_one, mul_assoc, hc, mul_one]

theorem commute_x₁_p {x₀ x₁ : G} (h0 : x₀ * x₀ = 1) (h1 : x₁ * x₁ = 1)
    (h01 : (x₀ * x₁) ^ 4 = 1) : Commute x₁ ((x₀ * x₁) ^ 2) := by
  have key : x₁ * x₀ * x₁ * x₀ * x₁ = x₀ * x₁ * x₀ := by
    have e : x₀ * x₁ * x₀ * (x₁ * x₀ * x₁ * x₀ * x₁) = 1 := by
      rw [← h01]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [eq_inv_of_mul_eq_one_right e]
    simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right h0, inv_eq_of_mul_eq_one_right h1,
      mul_assoc]
  show x₁ * (x₀ * x₁) ^ 2 = (x₀ * x₁) ^ 2 * x₁
  rw [pow_two]
  calc x₁ * (x₀ * x₁ * (x₀ * x₁)) = x₁ * x₀ * x₁ * x₀ * x₁ := by simp only [mul_assoc]
    _ = x₀ * x₁ * x₀ := key
    _ = x₀ * x₁ * (x₀ * x₁) * x₁ := by simp only [mul_assoc, h1, mul_one]

theorem commute_d₁ {x₀ x₁ c : G} (h0 : x₀ * x₀ = 1) (h1 : x₁ * x₁ = 1) (hc : c * c = 1)
    (h01 : (x₀ * x₁) ^ 4 = 1) (h03 : (x₀ * c) ^ 3 = 1) (h13 : (x₁ * c) ^ 3 = 1) :
    Commute x₀ (c * x₀ * x₁ * c * (x₀ * x₁) ^ 2 * (c * x₀ * x₁ * c)⁻¹) := by
  have h := (Commute.conj_iff (c * x₀ * x₁ * c)).2 (commute_x₁_p h0 h1 h01)
  rwa [conj_x₁ h0 h1 hc h03 h13] at h

theorem d₁_mul_self {x₀ x₁ h : G} (h01 : (x₀ * x₁) ^ 4 = 1) :
    h * (x₀ * x₁) ^ 2 * h⁻¹ * (h * (x₀ * x₁) ^ 2 * h⁻¹) = 1 := by
  have hp : (x₀ * x₁) ^ 2 * (x₀ * x₁) ^ 2 = 1 := by rw [← pow_add]; exact h01
  calc h * (x₀ * x₁) ^ 2 * h⁻¹ * (h * (x₀ * x₁) ^ 2 * h⁻¹)
      = h * ((x₀ * x₁) ^ 2 * (x₀ * x₁) ^ 2) * h⁻¹ := by group
    _ = 1 := by rw [hp, mul_one, mul_inv_cancel]

theorem facts_of_relsD {x : Fin 3 → G} (hx : ∀ r ∈ relsD, signedProd x r = 1) :
    x 0 * x 0 = 1 ∧ x 1 * x 1 = 1 ∧ x 2 * x 2 = 1 ∧ (x 0 * x 1) ^ 4 = 1 ∧
      (x 0 * x 2) ^ 3 = 1 ∧ (x 1 * x 2) ^ 3 = 1 ∧
      ((x 0 * x 1) ^ 2 * signedProd x wD) ^ 2 = x 0 := by
  have r0 := hx [(0, true), (0, true)] (by simp [relsD, relsW])
  have r1 := hx [(1, true), (1, true)] (by simp [relsD, relsW])
  have r2 := hx [(2, true), (2, true)] (by simp [relsD, relsW])
  have r3 := hx (List.replicate 4 [(0, true), (1, true)]).flatten (by simp [relsD, relsW])
  have r4 := hx (List.replicate 3 [(0, true), (2, true)]).flatten (by simp [relsD, relsW])
  have r5 := hx (List.replicate 3 [(1, true), (2, true)]).flatten (by simp [relsD, relsW])
  have r6 := hx (wP ++ wD ++ (wP ++ wD) ++ [(0, true)]) (by simp [relsD])
  simp only [signedProd_replicate] at r3 r4 r5
  simp only [signedProd_append, signedProd_wP] at r6
  have h0 : x 0 * x 0 = 1 := by simpa [signedProd] using r0
  refine ⟨h0, by simpa [signedProd] using r1, by simpa [signedProd] using r2,
    by simpa [signedProd] using r3, by simpa [signedProd] using r4,
    by simpa [signedProd] using r5, ?_⟩
  have e : (x 0 * x 1) ^ 2 * signedProd x wD * ((x 0 * x 1) ^ 2 * signedProd x wD) * x 0 = 1 := by
    simpa [signedProd, mul_assoc] using r6
  have e2 := eq_inv_of_mul_eq_one_left e
  rw [inv_eq_of_mul_eq_one_right h0] at e2
  rw [pow_two]
  exact e2

theorem signedProd_wD_eq {x : Fin 3 → G} (h0 : x 0 * x 0 = 1) (h1 : x 1 * x 1 = 1)
    (h2 : x 2 * x 2 = 1) :
    signedProd x wD = x 2 * x 0 * x 1 * x 2 * (x 0 * x 1) ^ 2 * (x 2 * x 0 * x 1 * x 2)⁻¹ := by
  rw [signedProd_wD]
  simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right h0, inv_eq_of_mul_eq_one_right h1,
    inv_eq_of_mul_eq_one_right h2, mul_assoc]

theorem relsK_of_relsF3 {x : Fin 3 → G} (hx : ∀ r ∈ relsF3, signedProd x r = 1) :
    ∀ r ∈ relsK, signedProd ![x 0, x 1, signedProd x wD] r = 1 := by
  obtain ⟨h0, h1, h2, h01, h02, h12, hpd⟩ :=
    facts_of_relsD fun r hr => hx r (List.mem_append_left _ hr)
  have h3 := hx (List.replicate 3 wXD).flatten (by simp [relsF3])
  rw [signedProd_replicate, wXD, signedProd_append] at h3
  have hd := signedProd_wD_eq h0 h1 h2
  set d := signedProd x wD with hd_def
  have hcomm : Commute (x 0) d := by rw [hd]; exact commute_d₁ h0 h1 h2 h01 h02 h12
  have hdd : d * d = 1 := by rw [hd]; exact d₁_mul_self h01
  intro r hr
  simp only [relsK, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [signedProd] using h0
  · simpa [signedProd] using h1
  · simpa [signedProd] using hdd
  · rw [signedProd_replicate]; simpa [signedProd] using h01
  · rw [signedProd_replicate]
    have : (x 0 * d) ^ 2 = 1 := by
      rw [pow_two, mul_assoc, ← mul_assoc d, ← hcomm.eq, mul_assoc, hdd, mul_one, h0]
    simpa [signedProd] using this
  · rw [signedProd_append, signedProd_replicate]
    have : ((x 0 * x 1) ^ 2 * d) ^ 2 * x 0 = 1 := by rw [hpd, h0]
    simpa [signedProd, pow_two, mul_assoc] using this
  · rw [signedProd_replicate]
    simpa [signedProd] using h3

theorem mk_eq_one_F4 (w : List (Fin 3 × Bool))
    (hwalk : Exc.coverWalk (2 * 3) DataTriv.fx DataTriv.fy DataTriv.ffi 0 (w.map letterCode) =
      0) :
    PresentedGroup.mk (wordRels relsF4) (FreeGroup.mk w) = 1 :=
  Exc.mk_eq_one_of_coverWalk (N := 3787) (F := 11313) (fx := DataTriv.fx) (fc := DataTriv.fc)
    (fy := DataTriv.fy) (kind := DataTriv.kind) (wi := DataTriv.wi) (fs := DataTriv.fs)
    (ft := DataTriv.ft) (fo := DataTriv.fo) (refs := DataTriv.refs) (pl := DataTriv.pl)
    (ffi := DataTriv.ffi) (live := DataTriv.live) (rels := wordRels relsF4) relsF4
    DataTriv.words (fun w hw => ⟨w, hw, rfl⟩) Certificates.certificate15952.1
    DataTriv.live_zero (by norm_num) DataTriv.facts_all DataTriv.cover_all w hwalk

theorem mk_F4 : PresentedGroup.mk (wordRels relsF4) (FreeGroup.mk [(0, true)]) = 1 :=
  mk_eq_one_F4 _ Certificates.certificate15952.2.1

theorem card_K_le : Finite (PresentedGroup (wordRels relsK)) ∧
    Nat.card (PresentedGroup (wordRels relsK)) ≤ 24 := by
  have h := card_le_of_facts_presented (m := 3) (N := 24) (F := 72) (fx := DataK24.fx)
    (fc := DataK24.fc) (fy := DataK24.fy) (kind := DataK24.kind) (wi := DataK24.wi)
    (fs := DataK24.fs) (ft := DataK24.ft) (fo := DataK24.fo) (refs := DataK24.refs)
    (pl := DataK24.pl) (ffi := DataK24.ffi) (live := DataK24.live)
    (rels := wordRels relsK) relsK DataK24.words (fun w hw => ⟨w, hw, rfl⟩)
    Certificates.certificate15952.2.2.1 DataK24.live_zero (by norm_num) DataK24.facts_all
    DataK24.cover_all
  rwa [DataK24.liveCount_eq] at h

theorem mk_mem_of_coverWalk_sub {m : ℕ} {rels : Set (FreeGroup (Fin m))}
    {H : Subgroup (PresentedGroup rels)} {N F : ℕ}
    {fx fc fy kind wi fs ft fo refs pl ffi : ℕ → ℕ} {live : ℕ → Bool}
    (relWords subWords : List (List (Fin m × Bool))) (ws : List (List ℕ))
    (hrels : ∀ w ∈ relWords, FreeGroup.mk w ∈ rels)
    (hsubs : ∀ w ∈ subWords, PresentedGroup.mk rels (FreeGroup.mk w) ∈ H)
    (hws : derivedOK (2 * m) (invLetter m) (codes relWords) ws = true)
    (hlive0 : live 0 = true) (hN : 0 < N)
    (hfacts : factsOK N (2 * m + 1) fx fc fy kind wi fs ft fo refs pl (invLetter m) ws
      (codes subWords) 0 F = true)
    (hcover : coverOK N (2 * m) F fx fc fy (invLetter m) ffi live 0 (N * (2 * m)) = true)
    (w : List (Fin m × Bool))
    (hwalk : Exc.coverWalk (2 * m) fx fy ffi 0 (w.map letterCode) = 0) :
    PresentedGroup.mk rels (FreeGroup.mk w) ∈ H := by
  have hbase : ∀ r ∈ codes relWords, evalWord (presLetter rels) r = 1 := by
    intro r hr
    simp only [codes, List.mem_map] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    rw [evalWord_presLetter]
    exact PresentedGroup.one_of_mem (hrels v hv)
  have hlet : ∀ v ∈ ws ++ codes subWords, ∀ c ∈ v, c ≤ 2 * m := by
    intro v hv c hc
    rcases List.mem_append.mp hv with hv | hv
    · simp only [derivedOK, List.all_eq_true, Bool.and_eq_true, Nat.blt_eq] at hws
      exact Nat.lt_succ_iff.mp ((hws v hv).1 c hc)
    · have := lettersOK_codes subWords
      simp only [lettersOK, List.all_eq_true, Nat.blt_eq] at this
      exact Nat.le_of_lt (this v hv c hc)
  have hw : ∀ c ∈ w.map letterCode, c < 2 * m := by
    intro c hc
    obtain ⟨⟨i, b⟩, -, rfl⟩ := List.mem_map.mp hc
    simp only [letterCode]
    have := i.isLt
    split <;> omega
  have hsubs' : ∀ v ∈ codes subWords, evalWord (presLetter rels) v ∈ H := by
    intro v hv
    simp only [codes, List.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [evalWord_presLetter]
    exact hsubs u hu
  have h := Exc.evalWord_mem_of_coverWalk (H := H) (gen := presLetter rels) (inv := invLetter m)
    (fun c hc => presLetter_invLetter rels hc) hlet
    (evalWord_of_derivedOK (presLetter_eps rels)
      (fun c hc => presLetter_invLetter rels (Nat.le_of_lt hc)) hbase hws)
    hsubs' hlive0 hN hfacts hcover hw hwalk
  rwa [evalWord_presLetter] at h

theorem codes_subK : codes subK = Data7560.subs :=
  Certificates.certificate15952.2.2.2.1

theorem mk_wU_mem {H : Subgroup (PresentedGroup (wordRels relsF3))}
    (hsubs : ∀ w ∈ subK, PresentedGroup.mk (wordRels relsF3) (FreeGroup.mk w) ∈ H) :
    PresentedGroup.mk (wordRels relsF3) (FreeGroup.mk wU) ∈ H :=
  mk_mem_of_coverWalk_sub (m := 3) (rels := wordRels relsF3) (H := H) (N := 7585) (F := 22760)
    (fx := Data7560.fx) (fc := Data7560.fc)
    (fy := Data7560.fy) (kind := Data7560.kind) (wi := Data7560.wi) (fs := Data7560.fs)
    (ft := Data7560.ft) (fo := Data7560.fo) (refs := Data7560.refs) (pl := Data7560.pl)
    (ffi := Data7560.ffi) (live := Data7560.live) relsF3 subK Data7560.words
    (fun w hw => ⟨w, hw, rfl⟩) hsubs Certificates.certificate15952.2.2.2.2.1
    Data7560.live_zero (by norm_num) (by rw [codes_subK]; exact Data7560.facts_all)
    Data7560.cover_all wU Certificates.certificate15952.2.2.2.2.2.1

theorem σ_rels : ∀ w ∈ relsF3, signedProd σ w = 1 :=
  Certificates.certificate15952.2.2.2.2.2.2.1

theorem σ_wU : signedProd σ wU = 1 :=
  Certificates.certificate15952.2.2.2.2.2.2.2.1

theorem w24_inj : ∀ i j : Fin 24, signedProd τ (w24 i) = signedProd τ (w24 j) → i = j :=
  Certificates.certificate15952.2.2.2.2.2.2.2.2.1

theorem w24_one : ∀ i : Fin 24, signedProd τ (w24 i) = 1 → i = 0 :=
  Certificates.certificate15952.2.2.2.2.2.2.2.2.2

theorem mk_wU : PresentedGroup.mk (wordRels relsF3) (FreeGroup.mk wU) = 1 := by
  set x : Fin 3 → PresentedGroup (wordRels relsF3) := PresentedGroup.of with hxdef
  have hx : ∀ r ∈ relsF3, signedProd x r = 1 := fun r hr => signedProd_of_eq_one hr
  set y : Fin 3 → PresentedGroup (wordRels relsF3) := ![x 0, x 1, signedProd x wD] with hydef
  have hy : ∀ r ∈ relsK, signedProd y r = 1 := relsK_of_relsF3 hx
  set Φ := wordsHom relsK y hy with hΦ
  set ψ := wordsHom relsF3 σ σ_rels with hψ
  have hmk : ∀ w, PresentedGroup.mk (wordRels relsF3) (FreeGroup.mk w) = signedProd x w :=
    fun w => (signedProd_of relsF3 w).symm
  have hu : PresentedGroup.mk (wordRels relsF3) (FreeGroup.mk wU) ∈ Φ.range := by
    refine mk_wU_mem fun w hw => ?_
    simp only [subK, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨PresentedGroup.of 0, by rw [hΦ, wordsHom_of, hmk]; simp [y, signedProd]⟩
    · exact ⟨PresentedGroup.of 1, by rw [hΦ, wordsHom_of, hmk]; simp [y, signedProd]⟩
    · exact ⟨PresentedGroup.of 2, by rw [hΦ, wordsHom_of, hmk]; simp [y]⟩
  obtain ⟨k, hk⟩ := hu
  set π : Fin 24 → PresentedGroup (wordRels relsK) :=
    fun i => PresentedGroup.mk (wordRels relsK) (FreeGroup.mk (w24 i)) with hπ
  have hψy : (fun j => ψ (y j)) = τ := by
    funext j
    fin_cases j
    · simp [y, x, ψ, τ]
    · simp [y, x, ψ, τ]
    · simp only [y, x, ψ, τ]
      simp [wordsHom_signedProd]
  have hΨ : ∀ i, ψ (Φ (π i)) = signedProd τ (w24 i) := by
    intro i
    simp only [hπ]
    rw [← signedProd_of relsK, hΦ, wordsHom_signedProd, map_signedProd, hψy]
  have hinj : Function.Injective π := fun i j h => w24_inj i j (by rw [← hΨ, ← hΨ, h])
  obtain ⟨hfin, hcard⟩ := card_K_le
  have hbij := hinj.bijective_of_nat_card_le (by simpa using hcard)
  obtain ⟨i, hi⟩ := hbij.2 k
  have hψu : ψ (PresentedGroup.mk (wordRels relsF3) (FreeGroup.mk wU)) = 1 := by
    rw [hmk, hψ, wordsHom_signedProd]
    exact σ_wU
  rw [← hk, ← hi, hΨ] at hψu
  rw [← hk, ← hi, w24_one i hψu]
  show Φ (PresentedGroup.mk (wordRels relsK) (FreeGroup.mk [])) = 1
  rw [show (FreeGroup.mk [] : FreeGroup (Fin 3)) = 1 from rfl, map_one, map_one]

end SigmaFar

end CFSG.Timmesfeld.Moufang
