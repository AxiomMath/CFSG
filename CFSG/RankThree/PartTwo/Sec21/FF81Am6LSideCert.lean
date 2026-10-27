module

public import Certificates.Certificate799750
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSide

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec4.Item434Kit
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData

theorem mul_eq_of_code {x y z : H6} {cx cy cz : List ℕ} (hx : mat6 x = dec6 cx)
    (hy : mat6 y = dec6 cy) (hz : mat6 z = dec6 cz) (h : mul6 cx cy = cz) : x * y = z := by
  apply mat6_injective
  rw [map_mul, hx, hy, hz, ← dec6_mul6, h]

theorem conj_eq_of_code {g x y : H6} {cg cgi cx cy : List ℕ} (hg : mat6 g = dec6 cg)
    (hgi : mat6 g⁻¹ = dec6 cgi) (hx : mat6 x = dec6 cx) (hy : mat6 y = dec6 cy)
    (h : mul6 (mul6 cg cx) cgi = cy) : g * x * g⁻¹ = y := by
  apply mat6_injective
  rw [map_mul, map_mul, hg, hx, hgi, hy, ← dec6_mul6, ← dec6_mul6, h]

def lsX0p : List ℕ :=
  [1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1]

def lsX0m : List ℕ :=
  [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]

def lsX2m : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1]

def lsGam : List ℕ :=
  [1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0,
    0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0,
    0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]

def lsGamI : List ℕ :=
  [1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0,
    0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0,
    1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]

noncomputable def sigH : H6 := ofCode (lsSig, lsSig) (by decide +kernel)

noncomputable def x0pH : H6 := ofCode (lsX0p, lsX0p) (by decide +kernel)

noncomputable def x0mH : H6 := ofCode (lsX0m, lsX0m) (by decide +kernel)

noncomputable def x2pH : H6 := ofCode (lsX2p, lsX2p) (by decide +kernel)

noncomputable def x2mH : H6 := ofCode (lsX2m, lsX2m) (by decide +kernel)

noncomputable def gamH : H6 := ofCode (lsGam, lsGamI) (by decide +kernel)

theorem mat6_sigH : mat6 sigH = dec6 lsSig := mat6_ofCode _ _
theorem mat6_x0pH : mat6 x0pH = dec6 lsX0p := mat6_ofCode _ _
theorem mat6_x0mH : mat6 x0mH = dec6 lsX0m := mat6_ofCode _ _
theorem mat6_x2pH : mat6 x2pH = dec6 lsX2p := mat6_ofCode _ _
theorem mat6_x2pH_inv : mat6 x2pH⁻¹ = dec6 lsX2p := mat6_ofCode_inv _ _
theorem mat6_x2mH : mat6 x2mH = dec6 lsX2m := mat6_ofCode _ _
theorem mat6_gamH : mat6 gamH = dec6 lsGam := mat6_ofCode _ _
theorem mat6_gamH_inv : mat6 gamH⁻¹ = dec6 lsGamI := mat6_ofCode_inv _ _

section Facts

theorem mat6_v : mat6 (zH 0 * zH 1 ^ 2) = dec6 lsV := by
  have h := mat6_pow_mul 1 2 0
  rwa [pow_one, pow_zero, mul_one] at h

theorem mat6_vinv : mat6 (zH 0 ^ 2 * zH 1) = dec6 lsVInv := by
  have h := mat6_pow_mul 2 1 0
  rwa [pow_one, pow_zero, mul_one] at h

theorem mat6_u : mat6 (zH 0 * zH 1) = dec6 (vecCode 1 1 0) := by
  have h := mat6_pow_mul 1 1 0
  rwa [pow_one, pow_one, pow_zero, mul_one] at h

theorem inv_v : (zH 0 * zH 1 ^ 2)⁻¹ = zH 0 ^ 2 * zH 1 :=
  inv_eq_of_mul_eq_one_right (mul_eq_of_code mat6_v mat6_vinv
    (by rw [map_one, dec6_one6]) (by decide +kernel))

noncomputable def wH : H6 := x0pH * x0mH

theorem mat6_wH : mat6 wH = dec6 (mul6 lsX0p lsX0m) := by
  rw [wH, map_mul, mat6_x0pH, mat6_x0mH, dec6_mul6]

theorem gam_sig : gamH * sigH * gamH⁻¹ = x0pH :=
  conj_eq_of_code mat6_gamH mat6_gamH_inv mat6_sigH mat6_x0pH (by decide +kernel)

theorem gam_v : gamH * (zH 0 * zH 1 ^ 2) * gamH⁻¹ = wH :=
  conj_eq_of_code mat6_gamH mat6_gamH_inv mat6_v mat6_wH (by decide +kernel)

theorem gam_z2 : gamH * zH 2 * gamH⁻¹ = zH 2 :=
  conj_eq_of_code mat6_gamH mat6_gamH_inv (mat6_zH 2) (mat6_zH 2) (by decide +kernel)

theorem gam_x2p : gamH * x2pH * gamH⁻¹ = x2pH :=
  conj_eq_of_code mat6_gamH mat6_gamH_inv mat6_x2pH mat6_x2pH (by decide +kernel)

theorem x2p_mul_x2m : x2pH * x2mH = zH 2 :=
  mul_eq_of_code mat6_x2pH mat6_x2mH (mat6_zH 2) (by decide +kernel)

theorem x2p_sq : x2pH * x2pH = 1 :=
  mul_eq_of_code mat6_x2pH mat6_x2pH (by rw [map_one, dec6_one6]) (by decide +kernel)

theorem x0p_sq : x0pH * x0pH = 1 :=
  mul_eq_of_code mat6_x0pH mat6_x0pH (by rw [map_one, dec6_one6]) (by decide +kernel)

theorem x2p_conj_z2 : x2pH * zH 2 * x2pH⁻¹ = (zH 2)⁻¹ :=
  conj_eq_of_code mat6_x2pH mat6_x2pH_inv (mat6_zH 2) (mat6_zH_inv 2) (by decide +kernel)

end Facts

section Orders

theorem w_cube : wH * wH * wH = 1 := by
  apply mat6_injective
  rw [map_mul, map_mul, map_one, mat6_wH, ← dec6_mul6, ← dec6_mul6, ← dec6_one6]
  exact congrArg dec6 (by decide +kernel)

theorem w_ne_one : wH ≠ 1 := by
  intro h
  have h1 := congrArg mat6 h
  rw [mat6_wH, map_one, ← dec6_one6] at h1
  have h2 := dec6_injective (canon6_mul6 _ _) canon6_one6 h1
  revert h2
  decide +kernel

theorem x0p_ne_one : x0pH ≠ 1 := by
  intro h
  have h1 := congrArg mat6 h
  rw [mat6_x0pH, map_one, ← dec6_one6] at h1
  have h2 := dec6_injective (by decide +kernel) canon6_one6 h1
  revert h2
  decide +kernel

theorem x2p_ne_one : x2pH ≠ 1 := by
  intro h
  have h1 := congrArg mat6 h
  rw [mat6_x2pH, map_one, ← dec6_one6] at h1
  have h2 := dec6_injective (by decide +kernel) canon6_one6 h1
  revert h2
  decide +kernel

theorem orderOf_x0p : orderOf x0pH = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact x0p_sq) x0p_ne_one

theorem orderOf_x2p : orderOf x2pH = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact x2p_sq) x2p_ne_one

theorem orderOf_w : orderOf wH = 3 :=
  orderOf_eq_prime (by rw [pow_three']; exact w_cube) w_ne_one

theorem orderOf_z2 : orderOf (zH 2) = 3 := orderOf_z wreathFacts_zH 2

theorem six_le_card {S : Subgroup H6} {a b : H6} (ha : a ∈ S) (hb : b ∈ S) (ha2 : orderOf a = 2)
    (hb3 : orderOf b = 3) : 6 ≤ Nat.card S := by
  have h2 : 2 ∣ Nat.card S := by
    have := Subgroup.orderOf_dvd_natCard S ha
    rwa [ha2] at this
  have h3 : 3 ∣ Nat.card S := by
    have := Subgroup.orderOf_dvd_natCard S hb
    rwa [hb3] at this
  have h6 : 6 ∣ Nat.card S := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  exact Nat.le_of_dvd Nat.card_pos h6

end Orders

section Cert

theorem lside_check_parts : admCheck = true ∧ countCheck = true ∧ frameCheck = true := by
  have h : lsideCheck = true := Certificates.certificate799750
  simp only [lsideCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem val_one_or_two {a : ZMod 3} (ha : a ≠ 0) : a.val = 1 ∨ a.val = 2 := by
  fin_cases a
  · exact absurd rfl ha
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem exists_frame_conj {p₁ p₂ p₃ : Fin 3} {a₁ a₂ a₃ : ZMod 3} (h12 : p₁ ≠ p₂) (h23 : p₂ ≠ p₃)
    (h13 : p₁ ≠ p₃) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0) :
    ∃ ρ : H6, ρ * zH p₁ ^ a₁.val * ρ⁻¹ = zH 2 ∧ ρ * zH p₂ ^ a₂.val * ρ⁻¹ = zH 0 ∧
      ρ * zH p₃ ^ a₃.val * ρ⁻¹ = zH 1 := by
  have h := lside_check_parts.2.2
  simp only [frameCheck, List.all_eq_true] at h
  have hmem : ∀ {a : ZMod 3}, a ≠ 0 → a.val ∈ [1, 2] := by
    intro a ha
    rcases val_one_or_two ha with h | h <;> simp [h]
  have h1 := h p₁ (List.mem_finRange _) p₂ (List.mem_finRange _) p₃ (List.mem_finRange _)
    a₁.val (hmem ha₁) a₂.val (hmem ha₂) a₃.val (hmem ha₃)
  have hd : (p₁ != p₂ && p₂ != p₃ && p₁ != p₃) = true := by
    simp [bne_iff_ne, h12, h23, h13]
  rw [hd] at h1
  simp only [Bool.not_true, Bool.false_or, frameOne, Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨⟨hp, e1⟩, e2⟩, e3⟩ := h1
  have hx : ∀ (p : Fin 3) (a : ℕ), mat6 (zH p ^ a) = dec6 (powCode (zCode p) a) := fun p a => by
    rw [map_pow, mat6_zH, dec6_powCode]
  refine ⟨ofCode _ hp, ?_, ?_, ?_⟩
  · exact conj_eq_of_code (mat6_ofCode _ _) (mat6_ofCode_inv _ _) (hx _ _) (mat6_zH 2) e1
  · exact conj_eq_of_code (mat6_ofCode _ _) (mat6_ofCode_inv _ _) (hx _ _) (mat6_zH 0) e2
  · exact conj_eq_of_code (mat6_ofCode _ _) (mat6_ofCode_inv _ _) (hx _ _) (mat6_zH 1) e3

theorem lsAVec_three : aVec 3 = ![1, 1, 0] := by
  ext i
  fin_cases i <;> rfl

theorem lsAVec_four : aVec 4 = ![1, 2, 0] := by
  ext i
  fin_cases i <;> rfl

theorem lsAElt_three : aElt 3 = zH 0 * zH 1 := by
  rw [aElt, lsAVec_three]
  simp only [vecElt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 : ZMod 3).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_one,
    pow_zero, mul_one]

theorem lsAElt_four : aElt 4 = zH 0 * zH 1 ^ 2 := by
  rw [aElt, lsAVec_four]
  simp only [vecElt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 : ZMod 3).val = 1 from rfl, show (2 : ZMod 3).val = 2 from rfl,
    show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_zero, mul_one]

theorem inv_z0_pow {k : ℕ} (hk : k ≤ 3) : (zH 0 ^ k)⁻¹ = zH 0 ^ (3 - k) := by
  rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_cancel' hk, zH_pow_three]

theorem mat6_conjSig {k : ℕ} (hk : k ≤ 3) :
    mat6 (zH 0 ^ k * sigH * (zH 0 ^ k)⁻¹) = dec6 (lsSigK k) := by
  rw [inv_z0_pow hk, lsSigK, map_mul, map_mul, map_pow, map_pow, mat6_zH, mat6_sigH, dec6_mul6,
    dec6_mul6, dec6_powCode, dec6_powCode]

theorem adm_classify {s : H6} (hs2 : s * s = 1) (hs₂ : s * zH 2 = zH 2 * s)
    (hsu : s * (zH 0 * zH 1) = (zH 0 * zH 1) * s)
    (hsv : s * (zH 0 * zH 1 ^ 2) * s⁻¹ = (zH 0 * zH 1 ^ 2)⁻¹) :
    ∃ k : ℕ, k < 3 ∧ s = zH 0 ^ k * sigH * (zH 0 ^ k)⁻¹ := by
  have hy : s ∈ centSub 3 := by
    rw [centSub_eq, lsAElt_three, Subgroup.mem_centralizer_singleton_iff]
    exact hsu
  obtain ⟨t, ht, hcode, hcanon⟩ := exists_code_closure _ _ _ (cent_spec 3).2.1 hy
  have hadm : admCheck = true := lside_check_parts.1
  have hpt := allCheck_spec hadm ht
  set c := (closureT ((centGens 3).map Prod.fst)).getD t [] with hc
  have hs : mat6 s = dec6 c := hcode.symm
  have hsv' : s * (zH 0 * zH 1 ^ 2) = (zH 0 ^ 2 * zH 1) * s := by
    rw [← inv_v, ← hsv]
    group
  have hadm' : lsAdm c = true := by
    have e1 : mul6 c c = one6 := by
      refine dec6_injective (canon6_mul6 _ _) canon6_one6 ?_
      rw [dec6_mul6, ← hs, ← map_mul, hs2, map_one, dec6_one6]
    have e2 : commutes6 c (zCode 2) = true := commutes6_of_commute hs (mat6_zH 2) hs₂
    have e3 : mul6 c lsV = mul6 lsVInv c := by
      refine dec6_injective (canon6_mul6 _ _) (canon6_mul6 _ _) ?_
      rw [dec6_mul6, dec6_mul6, ← hs, ← mat6_v, ← mat6_vinv, ← map_mul, ← map_mul, hsv']
    simp only [lsAdm, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨e1, e2⟩, e3⟩
  simp only [hadm', Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hpt
  have key : ∀ k : ℕ, k < 3 → c = lsSigK k →
      ∃ k : ℕ, k < 3 ∧ s = zH 0 ^ k * sigH * (zH 0 ^ k)⁻¹ := by
    intro k hk hck
    refine ⟨k, hk, mat6_injective ?_⟩
    rw [mat6_conjSig (by omega), ← hck, hs]
  rcases hpt with (h | h) | h
  · exact key 0 (by norm_num) h
  · exact key 1 (by norm_num) h
  · exact key 2 (by norm_num) h

theorem card_inf_eq_count (l : List (List ℕ × List ℕ)) (hl : l.all pairCheck = true) (n : ℕ)
    (hok : closureOK (l.map Prod.fst) (closureT (l.map Prod.fst)) n = true) (R : Subgroup H6)
    (p : List ℕ → Bool)
    (hp : ∀ (g : H6) (c : List ℕ), mat6 g = dec6 c → canon6 c = true → (g ∈ R ↔ p c = true)) :
    Nat.card ↥(Subgroup.closure (genSet l hl) ⊓ R) = countP p (closureT (l.map Prod.fst)) := by
  classical
  have hok' := hok
  simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at hok'
  obtain ⟨⟨⟨-, hclosed⟩, hdist⟩, hcanon⟩ := hok'
  have himg : mat6 '' (Subgroup.closure (genSet l hl) : Set H6) =
      {y | ∃ t < (closureT (l.map Prod.fst)).size,
        dec6 ((closureT (l.map Prod.fst)).getD t []) = y} :=
    image_closure_eq dec6 one6 mul6 (l.map Prod.fst) mat6 dec6_one6 dec6_mul6
      (genSet l hl) (image_genSet l hl) _ hclosed
  generalize closureT (l.map Prod.fst) = tab at himg hdist hcanon ⊢
  have hrange : mat6 '' ((Subgroup.closure (genSet l hl) ⊓ R : Subgroup H6) : Set H6) =
      Set.range (fun t : {t : Fin tab.size // p (tab.getD t []) = true} =>
        dec6 (tab.getD t [])) := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨hgS, hgR⟩ := Subgroup.mem_inf.1 hg
      have hm : mat6 g ∈ mat6 '' (Subgroup.closure (genSet l hl) : Set H6) := ⟨g, hgS, rfl⟩
      rw [himg] at hm
      obtain ⟨t, ht, e⟩ := hm
      have hc : canon6 (tab.getD t []) = true := allCheck_spec hcanon ht
      exact ⟨⟨⟨t, ht⟩, (hp g _ e.symm hc).1 hgR⟩, e⟩
    · rintro ⟨⟨⟨t, ht⟩, hpt⟩, rfl⟩
      have hm : dec6 (tab.getD t []) ∈ mat6 '' (Subgroup.closure (genSet l hl) : Set H6) := by
        rw [himg]
        exact ⟨t, ht, rfl⟩
      obtain ⟨g, hgS, e⟩ := hm
      have hc : canon6 (tab.getD t []) = true := allCheck_spec hcanon ht
      exact ⟨g, Subgroup.mem_inf.2 ⟨hgS, (hp g _ e hc).2 hpt⟩, e⟩
  have hinj : Function.Injective
      (fun t : {t : Fin tab.size // p (tab.getD t []) = true} => dec6 (tab.getD t [])) := by
    intro t t' e
    apply Subtype.ext
    exact Fin.ext (distinctCheck_spec hdist t.1.2 t'.1.2
      (dec6_injective (allCheck_spec hcanon t.1.2) (allCheck_spec hcanon t'.1.2) e))
  calc Nat.card ↥(Subgroup.closure (genSet l hl) ⊓ R)
      = Nat.card (mat6 '' ((Subgroup.closure (genSet l hl) ⊓ R : Subgroup H6) : Set H6)) :=
        (Nat.card_image_of_injective mat6_injective _).symm
    _ = Nat.card {t : Fin tab.size // p (tab.getD t []) = true} := by
        rw [hrange]
        exact Nat.card_range_of_injective hinj
    _ = countP p tab := by
        rw [countP, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem centralizer_pair {G : Type*} [Group G] (a b : G) :
    Subgroup.centralizer ({a, b} : Set G) =
      Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b} := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

theorem centralizer_sup_eq {G : Type*} [Group G] (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  ext x
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_union, SetLike.mem_coe,
    or_imp, forall_and]

noncomputable def K4s : Subgroup H6 := Subgroup.closure ({zH 0 * zH 1 ^ 2, sigH} : Set H6)

noncomputable def J2s : Subgroup H6 := Subgroup.closure ({zH 2, x2pH} : Set H6)

theorem card_cen_K4s : Nat.card ↥(Subgroup.centralizer (K4s : Set H6)) = 36 := by
  have h : Subgroup.centralizer (K4s : Set H6) = centSub 4 ⊓ Subgroup.centralizer {sigH} := by
    rw [K4s, Subgroup.centralizer_closure, centralizer_pair, centSub_eq, lsAElt_four]
  rw [h]
  have hc := card_inf_eq_count (centGens 4) (pairs_spec.2.2.2 4) (centOrder 4) (cent_spec 4).2.1
    (Subgroup.centralizer {sigH}) (fun c => commutes6 c lsSig) (fun g c hg _ => by
      constructor
      · intro hgR
        exact commutes6_of_commute hg mat6_sigH (Subgroup.mem_centralizer_singleton_iff.1 hgR)
      · intro hcm
        exact Subgroup.mem_centralizer_singleton_iff.2 (commute_of_commutes6 hg mat6_sigH hcm))
  have hcount :
      countP (fun t => commutes6 t lsSig) (closureT ((centGens 4).map Prod.fst)) = 36 := by
    have h := lside_check_parts.2.1
    simp only [countCheck, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  exact hc.trans hcount

theorem card_cen_K4s_J2s :
    Nat.card ↥(Subgroup.centralizer ((K4s ⊔ J2s : Subgroup H6) : Set H6)) = 6 := by
  have h : Subgroup.centralizer ((K4s ⊔ J2s : Subgroup H6) : Set H6) = centSub 4 ⊓
      (Subgroup.centralizer {sigH} ⊓ (Subgroup.centralizer {zH 2} ⊓
        Subgroup.centralizer {x2pH})) := by
    rw [centralizer_sup_eq, K4s, J2s, Subgroup.centralizer_closure, Subgroup.centralizer_closure,
      centralizer_pair, centralizer_pair, centSub_eq, lsAElt_four]
    exact inf_assoc _ _ _
  rw [h]
  have hc := card_inf_eq_count (centGens 4) (pairs_spec.2.2.2 4) (centOrder 4) (cent_spec 4).2.1
    (Subgroup.centralizer {sigH} ⊓ (Subgroup.centralizer {zH 2} ⊓ Subgroup.centralizer {x2pH}))
    (fun c => commutes6 c lsSig && commutes6 c (zCode 2) && commutes6 c lsX2p)
    (fun g c hg _ => by
      simp only [Subgroup.mem_inf, Bool.and_eq_true]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨commutes6_of_commute hg mat6_sigH (Subgroup.mem_centralizer_singleton_iff.1 h1),
          commutes6_of_commute hg (mat6_zH 2) (Subgroup.mem_centralizer_singleton_iff.1 h2)⟩,
          commutes6_of_commute hg mat6_x2pH (Subgroup.mem_centralizer_singleton_iff.1 h3)⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (commute_of_commutes6 hg mat6_sigH h1),
          Subgroup.mem_centralizer_singleton_iff.2 (commute_of_commutes6 hg (mat6_zH 2) h2),
          Subgroup.mem_centralizer_singleton_iff.2 (commute_of_commutes6 hg mat6_x2pH h3)⟩)
  have hcount : countP (fun t => commutes6 t lsSig && commutes6 t (zCode 2) &&
      commutes6 t lsX2p) (closureT ((centGens 4).map Prod.fst)) = 6 := by
    have h := lside_check_parts.2.1
    simp only [countCheck, Bool.and_eq_true, beq_iff_eq] at h
    exact h.2
  exact hc.trans hcount

theorem commute_z0_pow_zH (k : ℕ) (j : Fin 3) : Commute (zH 0 ^ k) (zH j) :=
  (show Commute (zH 0) (zH j) from zH_comm 0 j).pow_left k

theorem inv_mul_mul_cancel_of_commute {y : H6} {k : ℕ} (hc : Commute (zH 0 ^ k) y) :
    (zH 0 ^ k)⁻¹ * y * zH 0 ^ k = y := by
  rw [mul_assoc, ← hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_frame_std {c₁ c₂ c₃ s g : H6} {p₁ p₂ p₃ : Fin 3} {a₁ a₂ a₃ : ZMod 3}
    (h12 : p₁ ≠ p₂) (h23 : p₂ ≠ p₃) (h13 : p₁ ≠ p₃) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (e₁ : g * zH p₁ ^ a₁.val * g⁻¹ = c₁) (e₂ : g * zH p₂ ^ a₂.val * g⁻¹ = c₂)
    (e₃ : g * zH p₃ ^ a₃.val * g⁻¹ = c₃) (hs2 : s * s = 1) (hs₁ : s * c₁ = c₁ * s)
    (hs₂₃ : s * (c₂ * c₃) = (c₂ * c₃) * s) (hs₄ : s * (c₂ * c₃ ^ 2) * s⁻¹ = (c₂ * c₃ ^ 2)⁻¹) :
    ∃ Φ : H6, Φ * c₁ * Φ⁻¹ = zH 2 ∧ Φ * (c₂ * c₃ ^ 2) * Φ⁻¹ = zH 0 * zH 1 ^ 2 ∧
      Φ * s * Φ⁻¹ = sigH ∧ Φ * (c₂ * c₃) * Φ⁻¹ = zH 0 * zH 1 := by
  obtain ⟨ρ, r1, r2, r3⟩ := exists_frame_conj h12 h23 h13 ha₁ ha₂ ha₃
  have k1 : MulAut.conj (ρ * g⁻¹) c₁ = zH 2 := by
    rw [MulAut.conj_apply, ← e₁, ← r1]
    group
  have k2 : MulAut.conj (ρ * g⁻¹) c₂ = zH 0 := by
    rw [MulAut.conj_apply, ← e₂, ← r2]
    group
  have k3 : MulAut.conj (ρ * g⁻¹) c₃ = zH 1 := by
    rw [MulAut.conj_apply, ← e₃, ← r3]
    group
  have kv : MulAut.conj (ρ * g⁻¹) (c₂ * c₃ ^ 2) = zH 0 * zH 1 ^ 2 := by
    rw [map_mul, map_pow, k2, k3]
  have ku : MulAut.conj (ρ * g⁻¹) (c₂ * c₃) = zH 0 * zH 1 := by
    rw [map_mul, k2, k3]
  obtain ⟨k, hk, hks⟩ := adm_classify (s := MulAut.conj (ρ * g⁻¹) s)
    (by rw [← map_mul, hs2, map_one])
    (by rw [← k1, ← map_mul, ← map_mul, hs₁])
    (by rw [← ku, ← map_mul, ← map_mul, hs₂₃])
    (by
      have h := congrArg (MulAut.conj (ρ * g⁻¹)) hs₄
      rw [map_mul, map_mul, map_inv, map_inv, kv] at h
      exact h)
  have hΦ : ∀ x : H6, (zH 0 ^ k)⁻¹ * ρ * g⁻¹ * x * ((zH 0 ^ k)⁻¹ * ρ * g⁻¹)⁻¹ =
      (zH 0 ^ k)⁻¹ * MulAut.conj (ρ * g⁻¹) x * zH 0 ^ k := by
    intro x
    rw [MulAut.conj_apply]
    group
  refine ⟨(zH 0 ^ k)⁻¹ * ρ * g⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [hΦ, k1]
    exact inv_mul_mul_cancel_of_commute (commute_z0_pow_zH k 2)
  · rw [hΦ, kv]
    exact inv_mul_mul_cancel_of_commute (Commute.mul_right (commute_z0_pow_zH k 0)
      (Commute.pow_right (commute_z0_pow_zH k 1) 2))
  · rw [hΦ, hks]
    group
  · rw [hΦ, ku]
    exact inv_mul_mul_cancel_of_commute (Commute.mul_right (commute_z0_pow_zH k 0)
      (commute_z0_pow_zH k 1))

theorem x2p_comm_u : x2pH * (zH 0 * zH 1) = (zH 0 * zH 1) * x2pH :=
  commute_of_commutes6 mat6_x2pH mat6_u (by decide +kernel)

theorem ne_of_card_closure {c₁ c₂ c₃ g : H6} {p₁ p₂ p₃ : Fin 3} {a₁ a₂ a₃ : ℕ} (h12 : p₁ ≠ p₂)
    (e₁ : g * zH p₁ ^ a₁ * g⁻¹ = c₁) (e₂ : g * zH p₂ ^ a₂ * g⁻¹ = c₂)
    (e₃ : g * zH p₃ ^ a₃ * g⁻¹ = c₃)
    (hc : Nat.card (Subgroup.closure ({c₁, c₂, c₃} : Set H6)) = 27) : p₁ ≠ p₃ := by
  intro h13
  subst h13
  have hmem : ∀ (p : Fin 3) (a : ℕ) (c : H6), g * zH p ^ a * g⁻¹ = c →
      p ∈ ({p₁, p₂} : Set (Fin 3)) →
      c ∈ (Subgroup.zpowers (zH p₁) ⊔ Subgroup.zpowers (zH p₂)).map
        (MulAut.conj g).toMonoidHom := by
    intro p a c e hp
    refine ⟨zH p ^ a, ?_, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; exact e⟩
    rcases hp with rfl | hp
    · exact Subgroup.mem_sup_left (pow_mem (Subgroup.mem_zpowers _) _)
    · rw [Set.mem_singleton_iff.1 hp]
      exact Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers _) _)
  have hle : Subgroup.closure ({c₁, c₂, c₃} : Set H6) ≤
      (Subgroup.zpowers (zH p₁) ⊔ Subgroup.zpowers (zH p₂)).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hmem p₁ a₁ _ e₁ (Or.inl rfl)
    · exact hmem p₂ a₂ _ e₂ (Or.inr rfl)
    · exact hmem p₁ a₃ _ e₃ (Or.inl rfl)
  have h9 := (isElemAbelian_sup_zpowers wreathFacts_zH h12).2
  have := Subgroup.card_le_of_le hle
  rw [hc, Subgroup.card_map_of_injective (MulAut.conj g).injective, h9] at this
  omega

theorem card_inf_cen_map {G : Type*} [Group G] (f : H6 →* G) (hf : Function.Injective f)
    (K : Subgroup H6) :
    Nat.card ↥(f.range ⊓ Subgroup.centralizer ((K.map f : Subgroup G) : Set G)) =
      Nat.card ↥(Subgroup.centralizer (K : Set H6)) := by
  have h : f.range ⊓ Subgroup.centralizer ((K.map f : Subgroup G) : Set G) =
      (Subgroup.centralizer (K : Set H6)).map f := by
    ext x
    constructor
    · rintro ⟨⟨y, rfl⟩, hx⟩
      refine ⟨y, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro k hk
      have := Subgroup.mem_centralizer_iff.1 hx (f k) (Subgroup.mem_map_of_mem f hk)
      exact hf (by rw [map_mul, map_mul]; exact this)
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨k, hk, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hy k hk]
  rw [h]
  exact Subgroup.card_map_of_injective hf

end Cert

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSide
