module

public import CFSG.Monster.B.Fischer.InducedChecks
public import Certificates.Certificate16023

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

@[expose] def RepArr
    (g : F₀) (arr : Array ℕ) : Prop :=
  ∀ n < 3510, arr[n]! < 3510 ∧ decY arr[n]! = g • decY n

theorem RepArr.ι_smul
    {g : F₀} {arr : Array ℕ} (h : RepArr g arr) (y : Y) :
    (ι (g • y) : ℕ) = arr[(ι y : ℕ)]! := by
  obtain ⟨hlt, e⟩ := h (ι y) (ι y).2
  rw [decY_ι] at e
  rw [← e, ι_decY hlt]

theorem RepArr.mul
    {g h : F₀} {s x : Array ℕ} (hg : RepArr g s) (hh : RepArr h x)
    (hx : x.size = 3510) : RepArr (g * h) (amulN s x) := by
  intro n hn
  have hn' : n < x.size := hx ▸ hn
  have e : (amulN s x)[n]! = s[x[n]!]! := by
    rw [amulN, getElem!_pos _ _ (by rw [Array.size_map]; exact hn'), Array.getElem_map,
      getElem!_pos x n hn']
  obtain ⟨h1, e1⟩ := hh n hn
  obtain ⟨h2, e2⟩ := hg _ h1
  rw [e]
  exact ⟨h2, by rw [e2, e1, mul_smul]⟩

theorem genBinv_spec :
    ∀ t : Fin 22, ((psiHom (m22gB⁻¹ : Equiv.Perm (Fin 22)) (coordAt t : Fin 24)) : ℕ) =
      genBinv t + 2 :=
  Certificates.certificate16023.1

theorem letterPos_spec (z : ℤ) : ∀ t : Fin 22,
    ((psiHom (letterM22 z : CFSG.Blueprint.NativeSporadic.M22) (coordAt t : Fin 24)) : ℕ) =
      letterPos z t + 2 := by
  intro t
  unfold letterPos letterM22
  split_ifs
  · exact genA_spec t
  · rw [Subgroup.coe_inv, m22gA_inv]
    exact genA_spec t
  · exact genB_spec t
  · rw [Subgroup.coe_inv]
    exact genBinv_spec t

theorem letterPos_lt (z : ℤ) : ∀ t : Fin 22, letterPos z t < 22 := by
  intro t
  unfold letterPos
  split_ifs
  · exact genA_lt t
  · exact genA_lt t
  · exact genB_lt t
  · revert t; decide

theorem rho₀_letter (z : ℤ) (m : ℕ) :
    rho₀ (letterM22 z) (vecOf m) = vecOf (letterMask z m) :=
  rho₀_vecOf (letterPos_spec z) (letterPos_lt z) m

theorem rho₀_wordM22 (w : List ℤ) (m : ℕ) :
    rho₀ (wordM22 w) (vecOf m) = vecOf (wordMask w m) := by
  induction w with
  | nil =>
    rw [wordM22, List.map_nil, List.prod_nil, map_one]
    rfl
  | cons z w ih =>
    rw [wordM22, List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ← wordM22, ih,
      rho₀_letter]
    rfl

theorem letterM22_neg (z : ℤ) (hz : z ∈ ({1, -1, 2, -2} : Set ℤ)) :
    letterM22 (-z) = (letterM22 z)⁻¹ := by
  rcases hz with rfl | rfl | rfl | rfl
  · simp [letterM22]
  · have : m22a⁻¹ = m22a := Subtype.ext (by rw [Subgroup.coe_inv]; exact m22gA_inv)
    simp [letterM22, this]
  · simp [letterM22]
  · simp [letterM22]

theorem wordM22_append (w w' : List ℤ) : wordM22 (w ++ w') = wordM22 w * wordM22 w' := by
  rw [wordM22, List.map_append, List.prod_append]
  rfl

theorem wordM22_invWord (w : List ℤ) (hw : ∀ z ∈ w, z ∈ ({1, -1, 2, -2} : Set ℤ)) :
    wordM22 (invWord w) = (wordM22 w)⁻¹ := by
  induction w with
  | nil => simp [invWord, wordM22]
  | cons z w ih =>
    have hz := hw z (List.mem_cons_self ..)
    have ih' := ih fun x hx => hw x (List.mem_cons_of_mem _ hx)
    have e1 : invWord (z :: w) = invWord w ++ [-z] := by simp [invWord]
    have e2 : wordM22 [-z] = (letterM22 z)⁻¹ := by
      simp [wordM22, letterM22_neg z hz]
    rw [e1, wordM22_append, ih', e2,
      show wordM22 (z :: w) = letterM22 z * wordM22 w from rfl, mul_inv_rev]

theorem blockWord_letters :
    ∀ i < 77, ∀ z ∈ blockWord i, z ∈ ({1, -1, 2, -2} : Set ℤ) := by
  intro i hi z hz
  have : ∀ i < 77, ∀ z ∈ blockWord i, z = 1 ∨ z = 2 := Certificates.certificate16023.2
  rcases this i hi z hz with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))

theorem hRep_inv
    (i : ℕ) (hi : i < 77) : (hRep i)⁻¹ = wordM22 (invWord (blockWord i)) :=
  (wordM22_invWord _ (blockWord_letters i hi)).symm

theorem mem_KB_of_mem_D
    {κ : CFSG.Blueprint.NativeSporadic.M22}
    {x : Equiv.Perm (Fin 22) × Equiv.Perm (Fin 32)} (hx : x ∈ D) (h : x.1 = κ) : κ ∈ KB := by
  have hr : x.1 ∈ dFst.range := ⟨⟨x, hx⟩, rfl⟩
  rw [range_dFst] at hr
  have hmap := congrArg (Subgroup.map CFSG.Blueprint.NativeSporadic.M22.subtype) closure_gKB
  rw [MonoidHom.map_closure, ← Set.range_comp] at hmap
  have hr' : x.1 ∈ KB.map CFSG.Blueprint.NativeSporadic.M22.subtype := by
    rw [← hmap]
    exact hr
  obtain ⟨k, hk, e⟩ := hr'
  have : k = κ := Subtype.ext (e.trans h)
  exact this ▸ hk

theorem affCode_of_mem_D
    {κ : KB} {x : Equiv.Perm (Fin 22) × Equiv.Perm (Fin 32)} (hx : x ∈ D)
    (h : x.1 = ((κ : CFSG.Blueprint.NativeSporadic.M22) : Equiv.Perm (Fin 22))) :
    affCode κ = x.2 := by
  have hk : kbIncl κ = MonoidHom.ofInjective dFst_injective ⟨x, hx⟩ :=
    Subtype.ext (by rw [MonoidHom.ofInjective_apply, kbIncl_apply, dFst_apply]; exact h.symm)
  rw [affCode_apply, hk, MulEquiv.symm_apply_apply]

theorem getElem_extract_snd {x : Array ℕ} (hx : x.size = 54) {q : ℕ} (hq : q < 32) :
    (x.extract 22 54)[q]! = x[22 + q]! := by
  rw [getElem!_pos (x.extract 22 54) q (by rw [Array.size_extract, hx]; omega),
    getElem!_pos x (22 + q) (by omega), Array.getElem_extract]

theorem dCert_pts_mem_D
    {p : ℕ} (hp : p < dCert.pts.size) : dDec dCert.pts[p]! ∈ D :=
  (D_facts.1 _).2 ⟨p, hp, rfl⟩

theorem decY_lt22
    {n : ℕ} (hn : n < 22) : decY n = .inl (coordAt ⟨n, hn⟩) := by
  simp [decY, hn]

theorem decY_W
    {u : ℕ} (hu : u < 1024) : decY (22 + u) = .inr (.inl (wv u)) := by
  have h1 : ¬(22 + u < 22) := by omega
  have h2 : 22 + u < 1046 := by omega
  simp only [decY, h1, h2, ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left]

theorem decY_Z
    {i q : ℕ} (hi : i < 77) (hq : q < 32) :
    decY (1046 + 32 * i + q) = .inr (.inr (zMk (hRep i) (qv q))) := by
  have h0 : ¬(1046 + 32 * i + q < 22) := by omega
  have h0' : ¬(1046 + 32 * i + q < 1046) := by omega
  have h1 : (1046 + 32 * i + q - 1046) / 32 = i := by omega
  have h2 : (1046 + 32 * i + q - 1046) % 32 = q := by omega
  simp only [decY, h0, h0', ↓reduceDIte, ↓reduceIte, h1, h2]

theorem genAB_eq_letter (g : ℕ) : genAB g = letterM22 (genLetter g) := by
  unfold genAB genLetter letterM22
  split_ifs <;> simp_all

theorem kappa_spec
    {g i : ℕ} (hg : g < 2) (hi : i < 77) :
    wordM22 (kappaWord g i) = (hRep (zFib g i))⁻¹ * genAB g * hRep i := by
  obtain ⟨-, -, hj, -⟩ := check_Z g hg i hi
  rw [kappaWord, wordM22_append, wordM22_append, ← hRep_inv _ hj, genAB_eq_letter]
  simp [wordM22, hRep]

theorem repArr_gen_X
    {g : ℕ} (hg : g < 2) {n : ℕ} (h22 : n < 22) :
    (indM22Gen g)[n]! < 3510 ∧ decY (indM22Gen g)[n]! = kF (genAB g) • decY n := by
  have e := check_X g hg n h22
  have hlt : genAB' g n < 22 := genAB'_lt g ⟨n, h22⟩
  refine ⟨by rw [e]; omega, ?_⟩
  rw [e, decY_lt22 hlt, decY_lt22 h22, (smul_mk (genAB g) 1 0 0 _ 0).1,
    psiX_coordAt (genAB'_spec g hg) (genAB'_lt g)]

theorem repArr_gen_W
    {g : ℕ} (hg : g < 2) {u : ℕ} (hu : u < 1024) :
    (indM22Gen g)[22 + u]! < 3510 ∧ decY (indM22Gen g)[22 + u]! = kF (genAB g) • decY (22 + u) := by
  have e := check_W g hg u hu
  have hlt := linW_lt g hg u hu
  refine ⟨by rw [e]; omega, ?_⟩
  rw [e, decY_W hlt, decY_W hu, (smul_mk (genAB g) 1 0 (wv u) (coordAt 0) 0).2.1, rhoW_wv hg hu]

theorem repArr_gen_Z
    {g : ℕ} (hg : g < 2) {i q : ℕ} (hi : i < 77) (hq : q < 32) :
    (indM22Gen g)[1046 + 32 * i + q]! < 3510 ∧
      decY (indM22Gen g)[1046 + 32 * i + q]! = kF (genAB g) • decY (1046 + 32 * i + q) := by
  obtain ⟨hp, hext, hj, hval⟩ := check_Z g hg i hi
  have hprod0 := kappa_spec hg hi
  generalize hpdef : dFind (wordCat (kappaWord g i)) = p at hp hext hval
  generalize hjdef : zFib g i = j at hj hval hprod0
  generalize hxdef : dCert.pts[p]! = x at hext hval
  have hxv : dValid x = true := hxdef ▸ arrCertOK_valid dCert_ok hp
  have hmem : dDec x ∈ D := hxdef ▸ dCert_pts_mem_D hp
  have hαlt : x[22 + q]! < 32 := hxdef ▸ check_D_snd p (by rw [← dCert_size]; exact hp) q hq
  refine ⟨by rw [hval q hq]; omega, ?_⟩
  rw [hval q hq, decY_Z hj hαlt, decY_Z hi hq,
    (smul_mk (genAB g) (hRep i) 0 0 (coordAt 0) (qv q)).2.2.1]
  have hfst : (dDec x).1 = wordM22 (kappaWord g i) := by
    change decodeN 22 (x.extract 0 22) = _
    rw [hext]
    exact (wordCat_spec _).2
  have hκ : wordM22 (kappaWord g i) ∈ KB := mem_KB_of_mem_D hmem hfst
  have hcode : affCode ⟨_, hκ⟩ = (dDec x).2 := affCode_of_mem_D hmem hfst
  have hprod : genAB g * hRep i = hRep j * wordM22 (kappaWord g i) := by
    rw [hprod0]
    group
  have hA : affA ⟨_, hκ⟩ (qv q) = qv (x[22 + q]!) := by
    rw [affA_apply, qEquiv_symm_qv hq, hcode, qEquiv_apply]
    congr 1
    change (decodeN 32 (x.extract 22 54) ⟨q, hq⟩ : ℕ) = _
    rw [decodeN_apply (dValid_iff.1 hxv).2.2]
    exact getElem_extract_snd (dValid_iff.1 hxv).1 hq
  rw [hprod, show hRep j * wordM22 (kappaWord g i) =
    hRep j * ((⟨_, hκ⟩ : KB) : CFSG.Blueprint.NativeSporadic.M22) from rfl, zMk_mul, hA]

theorem repArr_gen
    {g : ℕ} (hg : g < 2) : RepArr (kF (genAB g)) (indM22Gen g) := by
  intro n hn
  rcases Nat.lt_or_ge n 22 with h22 | h22
  · exact repArr_gen_X hg h22
  rcases Nat.lt_or_ge n 1046 with h1046 | h1046
  · obtain ⟨u, rfl⟩ : ∃ u, n = 22 + u := ⟨n - 22, by omega⟩
    exact repArr_gen_W hg (by omega)
  · obtain ⟨i, q, hi, hq, rfl⟩ : ∃ i q, i < 77 ∧ q < 32 ∧ n = 1046 + 32 * i + q :=
      ⟨(n - 1046) / 32, (n - 1046) % 32, by omega, Nat.mod_lt _ (by norm_num), by omega⟩
    exact repArr_gen_Z hg hi hq

theorem repArr_a :
    RepArr (kF m22a) (indM22Gen 0) := repArr_gen (g := 0) (by norm_num)

theorem repArr_b :
    RepArr (kF m22b) (indM22Gen 1) := repArr_gen (g := 1) (by norm_num)

theorem rhoW_hRep_inv_wv
    (i : ℕ) (hi : i < 77) (m : ℕ) :
    rhoW (hRep i)⁻¹ (wv m) = K₀.mkQ (vecOf (wordMask (invWord (blockWord i)) (spreadW m))) := by
  rw [wv, rhoW_mkQ, hRep_inv i hi, rho₀_wordM22]

theorem wordMask_lt (w : List ℤ) {m : ℕ} (hm : m < 2 ^ 22) : wordMask w m < 2 ^ 22 := by
  induction w with
  | nil => exact hm
  | cons z w ih =>
    change letterMask z (wordMask w m) < 2 ^ 22
    exact gen_xor_lt (letterPos_lt z) _

theorem trans_shift
    {t i : ℕ} (ht : t < 10) (hi : i < 77) :
    U₀.mkQ (rhoW (hRep i)⁻¹ (wv (2 ^ t))) = qv (zShift t i) := by
  rw [rhoW_hRep_inv_wv i hi, ← qmk_apply, qv, qmk_eq_iff, ← vecOf_xor,
    vecOf_mem_K₀B_iff (Nat.xor_lt_two_pow (wordMask_lt _ (spreadW_lt _)) (spreadQ_lt _))]
  exact check_shift t ht i hi

@[expose] noncomputable def wBasis
    (t : ℕ) : F₀ := wF (wv (2 ^ t))

theorem repArr_trans
    {t : ℕ} (ht : t < 10) : RepArr (wBasis t) (indTransGen t) := by
  obtain ⟨hX, hW, hZ⟩ := check_T t ht
  intro n hn
  rcases Nat.lt_or_ge n 22 with h22 | h22
  · refine ⟨by rw [hX n h22]; omega, ?_⟩
    rw [hX n h22, decY_lt22 h22, wBasis, (smul_mk 1 1 (wv (2 ^ t)) 0 _ 0).2.2.2.1]
  rcases Nat.lt_or_ge n 1046 with h1046 | h1046
  · obtain ⟨u, rfl⟩ : ∃ u, n = 22 + u := ⟨n - 22, by omega⟩
    have hu : u < 1024 := by omega
    have hlt : u ^^^ 2 ^ t < 1024 :=
      Nat.xor_lt_two_pow (n := 10) hu (Nat.pow_lt_pow_right (by norm_num) ht)
    refine ⟨by rw [hW u hu]; omega, ?_⟩
    rw [hW u hu, decY_W hlt, decY_W hu, wBasis,
      (smul_mk 1 1 (wv (2 ^ t)) (wv u) (coordAt 0) 0).2.2.2.2.1, ← wv_xor, Nat.xor_comm]
  · obtain ⟨i, q, hi, hq, rfl⟩ : ∃ i q, i < 77 ∧ q < 32 ∧ n = 1046 + 32 * i + q :=
      ⟨(n - 1046) / 32, (n - 1046) % 32, by omega, Nat.mod_lt _ (by norm_num), by omega⟩
    obtain ⟨hsh, hval⟩ := hZ i hi
    have hlt : q ^^^ zShift t i < 32 := Nat.xor_lt_two_pow (n := 5) hq hsh
    refine ⟨by rw [hval q hq]; omega, ?_⟩
    rw [hval q hq, decY_Z hi hlt, decY_Z hi hq, wBasis,
      (smul_mk 1 (hRep i) (wv (2 ^ t)) 0 (coordAt 0) (qv q)).2.2.2.2.2, trans_shift ht hi,
      ← qv_xor]

end CFSG.Monster.B.Fischer
