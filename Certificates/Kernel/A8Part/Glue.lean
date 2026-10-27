module

public import Certificates.Kernel.A8Part.GlueTwo
public import CFSG.Certificates.Kernel.A8Part.Sound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat

public section

namespace CertificateChecks.KernelA8Part.Glue

open Equiv CFSG.KC.CosetLat CFSG.KC.Misc.ClosW CFSG.KC.A8Part CertificateChecks.KernelA8Part
open CFSG.Quasithin.H13.KGA8 (mGens sGens patterns)
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat (evalW)
open CFSG.KC.Misc.Clos (ClosEnc clos_card treeAt sortAt closedAt letB_eq allN_iff andB_eq_true)

theorem hQ7 : ∀ k < 2, ∃ g ∈ Lm 7, wcode 4 g = QG k := by
  have h := ch7154s7a
  unfold subOK at h
  exact words_in (hLin (by norm_num)) (andB_eq_true h).1

noncomputable def q (l : ℕ) : Perm (Fin 8) := dec (QG l)

theorem q_code : ∀ l < 2, wcode 4 (q l) = QG l := fun l hl => dec_code' (hQ7 l hl)

noncomputable def qgens : List (Perm (Fin 8)) := [q 0, q 1]

noncomputable def Q0 : Subgroup (Perm (Fin 8)) := cl qgens

theorem hQG : ∀ k < qgens.length, QG k = wcode 4 (qgens.getD k 1) := by
  intro k hk
  have hk2 : k < 2 := hk
  interval_cases k
  · exact (q_code 0 (by norm_num)).symm
  · exact (q_code 1 (by norm_num)).symm

theorem hQin : ∀ k < 2, ∃ g ∈ Q0, wcode 4 g = QG k := in_cl hQG

theorem q_mem : ∀ l < 2, q l ∈ Q0 := fun l hl => by
  obtain ⟨g, hg, hge⟩ := hQin l hl
  exact mem_of_code ⟨g, hg, hge.trans (q_code l hl).symm⟩

theorem card_Q0 : Nat.card Q0 = 9 := by
  have h := ch7154s7a
  unfold subOK at h
  have hl := (allN_iff _ _).1 (andB_eq_true h).2
  obtain ⟨-, -, h3⟩ := clos_card henc qgens (G := QG) (N := 9) (E := fun i => SE (Nat.add 38 i))
    (PA := fun i => SP (Nat.add 38 i)) (SG := fun i => SS (Nat.add 38 i)) hQG (by norm_num)
    (fun k hk => (andB_eq_true (hl k hk)).1)
    (fun k hk => (andB_eq_true (andB_eq_true (hl k hk)).2).1)
  exact (h3 (CT := fun r => SC (Nat.add 47 r))
    (fun k hk => (andB_eq_true (andB_eq_true (hl k hk)).2).2)).1

theorem Q0_le_alt : Q0 ≤ alternatingGroup (Fin 8) := by
  rw [← hAeq, top_eq]
  exact cl_le hQG fun k hk => hQ7 k hk

theorem hHG_ex : ∀ a < 4, ∃ g ∈ AM, wcode 4 g = HG a := words_in hMGin (andB_eq_true ch7154h).1

noncomputable def hgens : List (Perm (Fin 8)) := decL HG 4

noncomputable def Hs : Subgroup (Perm (Fin 8)) := cl hgens

theorem hgens_length : hgens.length = 4 := decL_length _ _

theorem hHG : ∀ a < hgens.length, HG a = wcode 4 (hgens.getD a 1) :=
  decL_getD fun a ha => ⟨_, (hHG_ex a ha).choose_spec.2⟩

theorem hHE : ∀ k < 72, ∃ g ∈ Hs, wcode 4 g = HE k := by
  have h := (andB_eq_true (andB_eq_true ch7154h).2).2
  have hA : ∀ a < 4, ∃ g ∈ Hs, wcode 4 g = HG a := fun a ha =>
    in_cl hHG a (by rw [hgens_length]; exact ha)
  exact tree_in hA ((allN_iff _ _).1 h)

theorem conj_gen {a : ℕ} (ha : a < 4) :
    ∀ z ∈ Q0, hgens.getD a 1 * z * (hgens.getD a 1)⁻¹ ∈ Q0 := by
  set h := hgens.getD a 1 with hh
  have hcode : wcode 4 h = HG a := (hHG a (by rw [hgens_length]; exact ha)).symm
  have hgen : ∀ l < 2, h * q l * h⁻¹ ∈ Q0 := by
    intro l hl
    have hc := (allN_iff _ _).1 (andB_eq_true (andB_eq_true ch7154h).2).1 (2 * a + l)
      (by change 2 * a + l < 8; omega)
    beta_reduce at hc
    have e1 : Nat.div (2 * a + l) (nat_lit 2) = a := by
      change (2 * a + l) / 2 = a
      omega
    have e2 : Nat.mod (2 * a + l) (nat_lit 2) = l := by
      change (2 * a + l) % 2 = l
      omega
    rw [e1, e2] at hc
    obtain ⟨hlet, heq⟩ := andB_eq_true hc
    obtain ⟨g, hg, hge⟩ := wordG_in hQin hlet
    have e : h * q l = g * h := by
      apply henc.inj
      rw [henc.enc_mul, henc.enc_mul, hcode, q_code l hl, hge]
      exact Nat.eq_of_beq_eq_true heq
    rw [e, mul_inv_cancel_right]
    exact hg
  have hle : Q0 ≤ Q0.comap (MulAut.conj h).toMonoidHom := by
    rw [Q0, cl, Subgroup.closure_le]
    intro y hy
    simp only [qgens, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hy
    simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hy with rfl | rfl
    · exact hgen 0 (by norm_num)
    · exact hgen 1 (by norm_num)
  intro z hz
  have hz' := hle hz
  simpa [MulAut.conj_apply] using hz'

theorem hH : ∀ y ∈ Hs, ∀ z ∈ Q0, y * z * y⁻¹ ∈ Q0 := by
  intro y hy
  have hy' : y ∈ Submonoid.closure {g | g ∈ hgens} := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hy
  clear hy
  induction hy' using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 hx
    have e : hgens.getD a 1 = hgens[a] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some]
    rw [← e]
    exact conj_gen (by rw [hgens_length] at ha; exact ha)
  | one => intro z hz; simpa using hz
  | mul x w hx hw ihx ihw =>
    intro z hz
    have e : x * w * z * (x * w)⁻¹ = x * (w * z * w⁻¹) * x⁻¹ := by group
    rw [e]
    exact ihx _ (ihw z hz)

noncomputable def r (j : ℕ) : Perm (Fin 8) := dec (RS j)

noncomputable def rinv (j : ℕ) : Perm (Fin 8) := dec (RI j)

theorem r_code : ∀ j < 12, wcode 4 (r j) = RS j := fun j hj =>
  dec_code' (words_in hMGin (andB_eq_true ch7154rs).1 j hj)

theorem rinv_code {j : ℕ} (hj : j < 12) : wcode 4 (rinv j) = RI j :=
  dec_code' (words_in hMGin (andB_eq_true (andB_eq_true ch7154rs).2).1 j hj)

theorem rinv_eq {j : ℕ} (hj : j < 12) : rinv j = (r j)⁻¹ := by
  have h1 := (allN_iff _ _).1 (andB_eq_true (andB_eq_true ch7154rs).2).2 j hj
  have e : r j * rinv j = 1 := by
    apply henc.inj
    rw [henc.enc_mul, r_code j hj, rinv_code hj, henc.enc_one]
    exact Nat.eq_of_beq_eq_true h1
  exact eq_inv_of_mul_eq_one_right e

theorem hcovA : ∀ σ ∈ alternatingGroup (Fin 8), ∃ s ∈ S0, ∃ j < 12, ∃ y ∈ Hs,
    σ = s * r j * y := by
  intro σ hσ
  rw [← hAeq] at hσ
  obtain ⟨t, ht, i, hi, u, hu, rfl⟩ := ctab_sound henc mGens hMG hTE hU (by norm_num) hUE0 hCM σ hσ
  obtain ⟨s, hs, j, hj, y, hy, hsu⟩ := trans3_sound henc (S := S0) (H := Hs) (r := r) hTE hHE r_code
    (fun i hi => (allN_iff _ _).1 ch7154sy i hi) i hi u hu
  refine ⟨t * s⁻¹, S0.mul_mem ht (S0.inv_mem hs), j, hj, y, hy, ?_⟩
  have hu' : u = s⁻¹ * (r j * y) := by
    rw [← hsu]
    group
  rw [hu']
  group

noncomputable def Tgens (p : ℕ) : List (Perm (Fin 8)) := (tgW.getD p []).map (evalW sGens)

noncomputable def Tp (p : ℕ) : Subgroup (Perm (Fin 8)) := cl (Tgens p)

noncomputable def x (p : ℕ) : Perm (Fin 8) := sGens.getD (xk p) 1

theorem code_evalW : ∀ w : List ℕ, lettersG 3 w = true →
    wcode 4 (evalW sGens w) = wordG m8 one8 SG w
  | [], _ => henc.enc_one
  | l :: w, h => by
    have h' : CFSG.KC.Ord.andB (Nat.blt l 3) (lettersG 3 w) = true := h
    obtain ⟨hl, hw⟩ := andB_eq_true h'
    change wcode 4 (sGens.getD l 1 * evalW sGens w) = m8 (SG l) (wordG m8 one8 SG w)
    rw [henc.enc_mul, code_evalW w hw, bridgeS l (Nat.blt_eq.mp hl)]

theorem patAt {p : ℕ} (hp : p < 7) : ch7154pat p = true := by
  interval_cases p
  · exact ch7154pat0
  · exact ch7154pat1
  · exact ch7154pat2
  · exact ch7154pat3
  · exact ch7154pat4
  · exact ch7154pat5
  · exact ch7154pat6

theorem nT_eq (p : ℕ) : nT p = (Tgens p).length := by
  unfold nT
  rw [lenW_eq, getWW_eq, Tgens, List.length_map]

theorem Tgens_getD {p l : ℕ} (hl : l < (Tgens p).length) :
    (Tgens p).getD l 1 = evalW sGens ((tgW.getD p []).getD l []) := by
  have hl' : l < (tgW.getD p []).length := by simpa [Tgens] using hl
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hl']
  simp [Tgens]

theorem hTG {p : ℕ} (hp : p < 7) :
    ∀ l < (Tgens p).length, TGp p l = wcode 4 ((Tgens p).getD l 1) := by
  intro l hl
  have hw := (allN_iff _ _).1 (andB_eq_true (patAt hp)).1 l (by rw [nT_eq]; exact hl)
  beta_reduce at hw
  have e : Nat.add 0 l = l := Nat.zero_add l
  rw [e, getW_eq, getWW_eq] at hw
  obtain ⟨hlet, heq⟩ := andB_eq_true hw
  rw [Tgens_getD hl, code_evalW _ hlet]
  exact (Nat.eq_of_beq_eq_true heq).symm

theorem hTGin {p : ℕ} (hp : p < 7) : ∀ l < nT p, ∃ g ∈ Tp p, wcode 4 g = TGp p l := by
  intro l hl
  rw [nT_eq] at hl
  exact in_cl (hTG hp) l hl

theorem hPE {p : ℕ} (hp : p < 7) :
    ∀ m < 32, ∃ g ∈ Tp p, wcode 4 g = PE (Nat.add (Nat.mul 32 p) m) :=
  tree_in (hTGin hp) ((allN_iff _ _).1 (andB_eq_true (andB_eq_true (patAt hp)).2).1)

theorem xk_lt : ∀ p < 7, xk p < 3 := by
  decide +kernel

theorem x_code {p : ℕ} (hp : p < 7) : wcode 4 (x p) = SG (xk p) :=
  (bridgeS _ (xk_lt p hp)).symm

theorem hcos : ∀ p < 7, ∀ s ∈ S0, s ∈ Tp p ∨ s * (x p)⁻¹ ∈ Tp p := by
  intro p hp
  have h3 := (allN_iff _ _).1 (andB_eq_true (andB_eq_true (patAt hp)).2).2
  rw [← x_code hp] at h3
  exact cos_sound henc hTEx (hPE hp) h3

theorem getD_mem {G : Type*} [Group G] {K : Subgroup G} {gens : List G}
    (hgens : ∀ g ∈ gens, g ∈ K) (k : ℕ) : gens.getD k 1 ∈ K := by
  by_cases hk : k < gens.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact hgens _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact K.one_mem

theorem evalW_mem {G : Type*} [Group G] {K : Subgroup G} {gens : List G}
    (hgens : ∀ g ∈ gens, g ∈ K) : ∀ w : List ℕ, evalW gens w ∈ K
  | [] => K.one_mem
  | i :: w => K.mul_mem (getD_mem hgens i) (evalW_mem hgens w)

theorem evalW_mem_iff {G : Type*} [Group G] {H K : Subgroup G} (h2 : (H.subgroupOf K).index = 2)
    {gens : List G} (hgens : ∀ g ∈ gens, g ∈ K) {b : ℕ → Bool}
    (hb : ∀ k, b k = true ↔ gens.getD k 1 ∉ H) :
    ∀ w : List ℕ, evalW gens w ∈ H ↔ Even (w.countP b)
  | [] => by simp [evalW, H.one_mem]
  | i :: w => by
    have key := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨gens.getD i 1, getD_mem hgens i⟩)
      (b := ⟨evalW gens w, evalW_mem hgens w⟩)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
    change gens.getD i 1 * evalW gens w ∈ H ↔ _
    rw [key, evalW_mem_iff h2 hgens hb w, List.countP_cons]
    by_cases hi : gens.getD i 1 ∈ H
    · have hbi : b i = false := by
        cases h : b i
        · rfl
        · exact absurd hi ((hb i).mp h)
      rw [hbi]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      exact ⟨fun h => h.mp hi, fun h => ⟨fun _ => h, fun _ => hi⟩⟩
    · have hbi : b i = true := (hb i).mpr hi
      rw [hbi]
      simp only [↓reduceIte, Nat.even_add_one]
      exact ⟨fun h hc => hi (h.mpr hc), fun h => ⟨fun hm => absurd hm hi, fun hc => absurd hc h⟩⟩

theorem par : ∀ p < 7, ∀ w ∈ tgW.getD p [],
    (w.countP fun k => (patterns.getD p []).getD k false) % 2 = 0 := by
  decide +kernel

theorem pat_ex : ∀ b₀ b₁ b₂ : Bool, ¬ (b₀ = false ∧ b₁ = false ∧ b₂ = false) →
    ∃ p < 7, patterns.getD p [] = [b₀, b₁, b₂] := by
  decide

theorem hT : ∀ P ≤ S0, Nat.card P = 32 → ∃ p < 7, Tp p ≤ P := by
  classical
  intro P hPS hP
  have hmem : ∀ g ∈ sGens, g ∈ S0 := fun g hg => Subgroup.subset_closure hg
  have hidx : (P.subgroupOf S0).index = 2 := by
    have h := Subgroup.card_mul_index (P.subgroupOf S0)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv, hP, card_S0] at h
    omega
  have hne : ¬ (sGens.getD 0 1 ∈ P ∧ sGens.getD 1 1 ∈ P ∧ sGens.getD 2 1 ∈ P) := by
    rintro ⟨h0, h1, h2⟩
    have hle : S0 ≤ P := by
      rw [S0, cl, Subgroup.closure_le]
      intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
      have hi3 : i < 3 := hi
      interval_cases i
      · rwa [← List.getD_eq_getElem _ 1]
      · rwa [← List.getD_eq_getElem _ 1]
      · rwa [← List.getD_eq_getElem _ 1]
    have h := Subgroup.card_le_of_le hle
    rw [card_S0, hP] at h
    norm_num at h
  obtain ⟨p, hp, hpe⟩ := pat_ex (decide (sGens.getD 0 1 ∉ P)) (decide (sGens.getD 1 1 ∉ P))
    (decide (sGens.getD 2 1 ∉ P)) (by
      rintro ⟨h0, h1, h2⟩
      simp only [decide_eq_false_iff_not, not_not] at h0 h1 h2
      exact hne ⟨h0, h1, h2⟩)
  refine ⟨p, hp, ?_⟩
  have hb : ∀ k, (patterns.getD p []).getD k false = true ↔ sGens.getD k 1 ∉ P := by
    intro k
    rw [hpe]
    match k with
    | 0 => simp
    | 1 => simp
    | 2 => simp
    | k + 3 =>
      have hl : sGens.length = 3 := rfl
      rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by omega)]
      simp [P.one_mem]
  rw [Tp, cl, Subgroup.closure_le]
  intro t ht
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
  rw [SetLike.mem_coe, evalW_mem_iff hidx hmem hb w, Nat.even_iff]
  exact par p hp w hw

theorem KC_code {j l : ℕ} (hj : j < 12) (hl : l < 2) :
    KC (2 * j + l) = wcode 4 (r j * q l * (r j)⁻¹) := by
  have h := (allN_iff _ _).1 (andB_eq_true ch7154k).1 (2 * j + l)
    (by change 2 * j + l < 24; omega)
  beta_reduce at h
  have e1 : Nat.div (2 * j + l) (nat_lit 2) = j := by
    change (2 * j + l) / 2 = j
    omega
  have e2 : Nat.mod (2 * j + l) (nat_lit 2) = l := by
    change (2 * j + l) % 2 = l
    omega
  rw [e1, e2] at h
  rw [← rinv_eq hj, henc.enc_mul, henc.enc_mul, r_code j hj, q_code l hl, rinv_code hj]
  exact Nat.eq_of_beq_eq_true h

theorem KX_code {k i : ℕ} (hk : k < 3) (hi : i < 24) :
    KX (24 * k + i) = m8 (m8 (SG k) (KC i)) (SG k) := by
  have h := (allN_iff _ _).1 (andB_eq_true (andB_eq_true ch7154k).2).1 (24 * k + i)
    (by change 24 * k + i < 72; omega)
  beta_reduce at h
  have e1 : Nat.div (24 * k + i) (nat_lit 24) = k := by
    change (24 * k + i) / 24 = k
    omega
  have e2 : Nat.mod (24 * k + i) (nat_lit 24) = i := by
    change (24 * k + i) % 24 = i
    omega
  rw [e1, e2] at h
  exact Nat.eq_of_beq_eq_true h

theorem s_sq {k : ℕ} (hk : k < 3) : (sGens.getD k 1)⁻¹ = sGens.getD k 1 := by
  have h := (allN_iff _ _).1 (andB_eq_true (andB_eq_true ch7154k).2).2 k hk
  have e : sGens.getD k 1 * sGens.getD k 1 = 1 := by
    apply henc.inj
    rw [henc.enc_mul, ← bridgeS k hk, henc.enc_one]
    exact Nat.eq_of_beq_eq_true h
  exact (eq_inv_of_mul_eq_one_right e).symm

noncomputable def cE (p ci : ℕ) : Perm (Fin 8) := if ci % 2 = 0 then r (ci / 2) else x p * r (ci / 2)

theorem KCp_code {p ci l : ℕ} (hp : p < 7) (hci : ci < 24) (hl : l < 2) :
    KCp p ci l = wcode 4 (cE p ci * q l * (cE p ci)⁻¹) := by
  have hj : ci / 2 < 12 := by omega
  unfold KCp
  cases hb : Nat.beq (Nat.mod ci (nat_lit 2)) (nat_lit 0)
  · have h : ¬ ci % 2 = 0 := Nat.ne_of_beq_eq_false hb
    rw [cE, if_neg h]
    change KX (24 * xk p + (2 * (ci / 2) + l)) = _
    have hx : (x p)⁻¹ = x p := s_sq (xk_lt p hp)
    have e2 : x p * r (ci / 2) * q l * (x p * r (ci / 2))⁻¹ =
        x p * (r (ci / 2) * q l * (r (ci / 2))⁻¹) * x p := by
      rw [mul_inv_rev, hx]
      group
    rw [e2, henc.enc_mul, henc.enc_mul, x_code hp, KX_code (xk_lt p hp) (by omega), KC_code hj hl]
  · have h : ci % 2 = 0 := Nat.eq_of_beq_eq_true hb
    rw [cE, if_pos h]
    change KC (2 * (ci / 2) + l) = _
    exact KC_code hj hl

theorem JGen_in {p ci : ℕ} (hp : p < 7) (hci : ci < 24) {K : Subgroup (Perm (Fin 8))}
    (hT : Tp p ≤ K) (hQ : ∀ z ∈ Q0, cE p ci * z * (cE p ci)⁻¹ ∈ K) :
    ∀ l < nJ p, ∃ g ∈ K, wcode 4 g = JGen p ci l := by
  intro l hl
  have hnJ : nJ p = nT p + 2 := rfl
  rw [hnJ] at hl
  unfold JGen
  by_cases h : l < nT p
  · rw [Nat.blt_eq.mpr h]
    obtain ⟨g, hg, hge⟩ := hTGin hp l h
    exact ⟨g, hT hg, hge⟩
  · have hf : Nat.blt l (nT p) = false := by
      cases e : Nat.blt l (nT p)
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h
    rw [hf]
    have hl2 : l - nT p < 2 := by omega
    exact ⟨_, hQ _ (q_mem _ hl2), (KCp_code hp hci hl2).symm⟩

noncomputable def Jgens (g : ℕ) : List (Perm (Fin 8)) := decL (GGen g) (nGG g)

noncomputable def Jg (g : ℕ) : Subgroup (Perm (Fin 8)) := cl (Jgens g)

noncomputable def ρg (g a : ℕ) : Perm (Fin 8) := dec (JR (8 * g + a))

theorem Jgens_length (g : ℕ) : (Jgens g).length = nGG g := decL_length _ _

theorem gaAt {g : ℕ} (hg : g < 6) : ch7154ga g = true := by
  interval_cases g
  · exact ch7154ga0
  · exact ch7154ga1
  · exact ch7154ga2
  · exact ch7154ga3
  · exact ch7154ga4
  · exact ch7154ga5

theorem gtAt {g : ℕ} (hg : g < 6) : ch7154gt g = true := by
  interval_cases g
  · exact ch7154gt0
  · exact ch7154gt1
  · exact ch7154gt2
  · exact ch7154gt3
  · exact ch7154gt4
  · exact ch7154gt5

theorem mask_card : ∀ g < 6, (maskSet (nth (getW grp g) 2)).card = 4 := by
  decide +kernel

theorem nU_pos : ∀ g < 6, 0 < nth (getW grp g) 5 := by
  decide +kernel

theorem grp_fact {g : ℕ} (hg : g < 6) {K : Subgroup (Perm (Fin 8))} (hJK : Jg g ≤ K)
    (hKA : K ≤ AM) (hne : K ≠ AM) : ∃ S : Finset (Fin 8), S.card = 4 ∧ K ≤ partStab S := by
  have ha := gaAt hg
  unfold ch7154ga at ha
  rw [letB_eq, letB_eq, letB_eq, letB_eq] at ha
  obtain ⟨hgp, ha⟩ := andB_eq_true ha
  obtain ⟨hgc, ha⟩ := andB_eq_true ha
  obtain ⟨hps, ha⟩ := andB_eq_true ha
  obtain ⟨htr, ha⟩ := andB_eq_true ha
  obtain ⟨hjr, hbad⟩ := andB_eq_true ha
  have ht := gtAt hg
  unfold ch7154gt at ht
  rw [letB_eq, letB_eq, letB_eq, letB_eq, letB_eq, letB_eq] at ht
  obtain ⟨hu0, ht⟩ := andB_eq_true ht
  obtain ⟨htrans, hct⟩ := andB_eq_true ht
  have hgp' : gp g < 7 := Nat.blt_eq.mp hgp
  have hgc' : gci g < 24 := Nat.blt_eq.mp hgc
  have hex : ∀ l < nGG g, ∃ σ : Perm (Fin 8), wcode 4 σ = GGen g l := fun l hl => by
    obtain ⟨σ, -, hσ⟩ := JGen_in hgp' hgc' (K := ⊤) le_top (fun _ _ => Subgroup.mem_top _) l hl
    exact ⟨σ, hσ⟩
  have hJG : ∀ l < (Jgens g).length, GGen g l = wcode 4 ((Jgens g).getD l 1) := decL_getD hex
  have hJin : ∀ l < nGG g, ∃ σ ∈ Jg g, wcode 4 σ = GGen g l := fun l hl =>
    in_cl hJG l (by rw [Jgens_length]; exact hl)
  have hJB : Jg g ≤ partStab (maskSet (nth (getW grp g) 2)) := by
    refine cl_le hJG fun l hl => ⟨(Jgens g).getD l 1, ?_, (hJG l hl).symm⟩
    have h := (allN_iff _ _).1 hps l (by rw [Jgens_length] at hl; exact hl)
    beta_reduce at h
    rw [hJG l hl] at h
    exact psAt_sound _ h
  have hTJ := tree_in hJin ((allN_iff _ _).1 htr)
  have hρ_code : ∀ a < nth (getW grp g) 8,
      wcode 4 (ρg g a) = JR (Nat.add (Nat.mul 8 g) a) := fun a ha =>
    dec_code' (words_in hMGin hjr a ha)
  have hcov := ctab_cover henc mGens hMG (T := Jg g) (ρ := ρg g) hρ_code hTJ
    ((allN_iff _ _).1 htrans) (nU_pos g hg) hu0 ((allN_iff _ _).1 hct)
  have hρ : ∀ a < nth (getW grp g) 8, ρg g a ∈ partStab (maskSet (nth (getW grp g) 2)) ∨
      AM ≤ Jg g ⊔ Subgroup.closure {ρg g a} := by
    intro a ha
    have h := (allN_iff _ _).1 hbad a ha
    beta_reduce at h
    cases hb : Nat.beq (lenW (getWW (getWWW jbad g) a)) (nat_lit 0)
    · rw [hb] at h
      right
      have hA : ∀ l < Nat.succ (nGG g), ∃ σ ∈ Jg g ⊔ Subgroup.closure {ρg g a},
          wcode 4 σ = JGR g a l := by
        intro l hl
        unfold JGR
        by_cases h' : l < nGG g
        · rw [Nat.blt_eq.mpr h']
          obtain ⟨σ, hσ, hσe⟩ := hJin l h'
          exact ⟨σ, Subgroup.mem_sup_left hσ, hσe⟩
        · have hf : Nat.blt l (nGG g) = false := by
            cases e : Nat.blt l (nGG g)
            · rfl
            · exact absurd (Nat.blt_eq.mp e) h'
          rw [hf]
          exact ⟨ρg g a, Subgroup.mem_sup_right (Subgroup.subset_closure rfl), hρ_code a ha⟩
      exact cl_le hMG (words_in hA h)
    · rw [hb] at h
      left
      have h' : psAt (nth (getW grp g) 2) (wcode 4 (ρg g a)) = true := by
        rw [hρ_code a ha]
        exact h
      exact psAt_sound _ h'
  exact ⟨maskSet (nth (getW grp g) 2), mask_card g hg, le_of_dcover hJB hcov hρ hJK hKA hne⟩

theorem candAt' {p : ℕ} (hp : p < 7) : ch7154cand p = true := by
  interval_cases p
  · exact ch7154cand0
  · exact ch7154cand1
  · exact ch7154cand2
  · exact ch7154cand3
  · exact ch7154cand4
  · exact ch7154cand5
  · exact ch7154cand6

theorem hcand : ∀ p < 7, ∀ j < 12, ∀ c : Perm (Fin 8), (c = r j ∨ c = x p * r j) →
    ∀ K : Subgroup (Perm (Fin 8)), Tp p ≤ K → (∀ z ∈ Q0, c * z * c⁻¹ ∈ K) →
      K ≤ alternatingGroup (Fin 8) → K ≠ alternatingGroup (Fin 8) →
        ∃ S : Finset (Fin 8), S.card = 4 ∧ K ≤ partStab S := by
  intro p hp j hj c hc K hTK hQK hKA hne
  rw [← hAeq] at hKA hne
  obtain ⟨ci, hci, rfl⟩ : ∃ ci < 24, c = cE p ci := by
    rcases hc with rfl | rfl
    · refine ⟨2 * j, by omega, ?_⟩
      rw [cE, if_pos (show 2 * j % 2 = 0 by omega), show 2 * j / 2 = j by omega]
    · refine ⟨2 * j + 1, by omega, ?_⟩
      rw [cE, if_neg (show ¬ (2 * j + 1) % 2 = 0 by omega), show (2 * j + 1) / 2 = j by omega]
  have hJ := JGen_in hp hci hTK hQK
  have hl : (getWWW cand p).length = 24 := by
    rw [← lenWW_eq]
    exact Nat.eq_of_beq_eq_true (andB_eq_true (candAt' hp)).1
  have h := allIx_get (andB_eq_true (candAt' hp)).2 ci (by rw [hl]; exact hci)
  rw [Nat.zero_add] at h
  unfold candAt at h
  cases hb : Nat.beq (hd (getW ((getWWW cand p).getD ci []) (nat_lit 0))) (nat_lit 0)
  · rw [hb, letB_eq] at h
    obtain ⟨hg, hw⟩ := andB_eq_true h
    have hw' := words_in hJ hw
    have hJK : Jg _ ≤ K := cl_le (decL_getD fun l hl => by
        obtain ⟨σ, -, hσ⟩ := hw' l hl
        exact ⟨σ, hσ⟩) fun l hl => hw' l (by rw [Jgens_length] at hl; exact hl)
    exact grp_fact (Nat.blt_eq.mp hg) hJK hKA hne
  · rw [hb] at h
    exact absurd (le_antisymm hKA (cl_le hMG (words_in hJ h))) hne

theorem part : ∀ N : Subgroup (Perm (Fin 8)), N ≤ alternatingGroup (Fin 8) → 288 ∣ Nat.card N →
    N ≠ alternatingGroup (Fin 8) → ∃ S : Finset (Fin 8), S.card = 4 ∧
      ∀ g ∈ N, (∀ i, g i ∈ S ↔ i ∈ S) ∨ (∀ i, g i ∈ S ↔ i ∉ S) :=
  part_of_cands S0_le_alt card_S0 Q0_le_alt card_Q0 hcovA hH hcos hT hcand

end CertificateChecks.KernelA8Part.Glue

end
