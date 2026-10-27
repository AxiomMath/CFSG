module

public import CFSG.Monster.B.Fischer.InducedGens
public import CFSG.Monster.B.Fischer.InducedOrbitChecks

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu
  CFSG.Monster.B.TwoA.Census

@[expose, instance_reducible] noncomputable def wActK :
    MulAction CFSG.Blueprint.NativeSporadic.M22 W₀ where
  smul k w := rhoW k w
  one_smul w := by
    change rhoW 1 w = w
    rw [map_one]
    rfl
  mul_smul k l w := by
    change rhoW (k * l) w = rhoW k (rhoW l w)
    rw [map_mul]
    rfl

@[expose, instance_reducible] noncomputable def zActK :
    MulAction CFSG.Blueprint.NativeSporadic.M22 Z where
  smul := zK
  one_smul := zK_one
  mul_smul := zK_mul

@[expose] noncomputable def orbitW
    (w : W₀) : Set W₀ :=
  Set.range fun k : CFSG.Blueprint.NativeSporadic.M22 => rhoW k w

@[expose] noncomputable def orbitZ
    (z : Z) : Set Z :=
  Set.range fun k : CFSG.Blueprint.NativeSporadic.M22 => zK k z

theorem m22_induction {P : CFSG.Blueprint.NativeSporadic.M22 → Prop} (ha : P m22a) (hb : P m22b)
    (hmul : ∀ x y, P x → P y → P (x * y)) (hinv : ∀ x, P x → P x⁻¹) (h1 : P 1)
    (k : CFSG.Blueprint.NativeSporadic.M22) : P k := by
  have hk : k ∈ Subgroup.closure ({m22a, m22b} : Set CFSG.Blueprint.NativeSporadic.M22) := by
    rw [closure_pair_eq_top m22_eq]
    exact Subgroup.mem_top k
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy
  | inv x _ hx => exact hinv x hx

theorem exists_idx {a : Array ℕ} {u : ℕ} (hu : u ∈ a.toList) : ∃ i < a.size, a[i]! = u := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  have hi' : i < a.size := by simpa using hi
  exact ⟨i, hi', by rw [getElem!_pos a i hi', Array.getElem_toList]⟩

theorem mem_toList {a : Array ℕ} {i : ℕ} (hi : i < a.size) : a[i]! ∈ a.toList := by
  rw [getElem!_pos a i hi, ← Array.getElem_toList]
  exact List.getElem_mem _

section W

attribute [local instance] wActK

theorem orbitW_eq_orbit (w : W₀) :
    orbitW w = MulAction.orbit CFSG.Blueprint.NativeSporadic.M22 w := rfl

theorem wv_act :

    ∀ g < 2, ∀ u, decide (u < 1024) = true → wv (linW g u) = genAB g • wv u :=
  fun _ hg _ hu => (rhoW_wv hg (of_decide_eq_true hu)).symm

theorem wv_inj' :
    ∀ a b, decide (a < 1024) = true → decide (b < 1024) = true → wv a = wv b →
    a = b := fun _ _ ha hb e => wv_inj (of_decide_eq_true ha) (of_decide_eq_true hb) e

theorem orbitW_cert
    {s : ℕ} (hs : s ∈ [0, 1, 3, 7]) :
    orbitW (wv s) = (fun i => wv (wCert s).pts[i]!) '' {i | i < (wCert s).pts.size} := by
  rw [orbitW_eq_orbit, ← orbit_closure_eq closure_genAB]
  exact orbit_of_natCertOK (wCert_ok s hs) wv_act

theorem ncard_orbitW
    {s : ℕ} (hs : s ∈ [0, 1, 3, 7]) :
    (orbitW (wv s)).ncard = (wCert s).pts.size := by
  rw [orbitW_eq_orbit, ← orbit_closure_eq closure_genAB]
  exact ncard_orbit_of_natCertOK (wCert_ok s hs) wv_act wv_inj'

theorem mem_orbitW
    {s : ℕ} (hs : s ∈ [0, 1, 3, 7]) {u : ℕ} (hu : u ∈ (wCert s).pts.toList) :
    wv u ∈ orbitW (wv s) := by
  rw [orbitW_cert hs]
  obtain ⟨i, hi, rfl⟩ := exists_idx hu
  exact ⟨i, hi, rfl⟩

theorem orbitW_mem
    {s : ℕ} (hs : s ∈ [0, 1, 3, 7]) {w : W₀} (hw : w ∈ orbitW (wv s)) :
    ∃ u ∈ (wCert s).pts.toList, u < 1024 ∧ wv u = w := by
  rw [orbitW_cert hs] at hw
  obtain ⟨i, hi, rfl⟩ := hw
  exact ⟨_, mem_toList hi, of_decide_eq_true (natCertOK_valid (wCert_ok s hs) hi), rfl⟩

end W

@[expose] noncomputable def Lw (i : ℕ) : Set W₀ := {w | cosetWt w = i}

theorem orbitW_subset_Lw
    {w : W₀} : orbitW w ⊆ Lw (cosetWt w) := by
  rintro _ ⟨k, rfl⟩
  exact cosetWt_rhoW k w

theorem rhoW_mem_Lw
    (k : CFSG.Blueprint.NativeSporadic.M22) {i : ℕ} {w : W₀} (hw : w ∈ Lw i) :
    rhoW k w ∈ Lw i :=
  (cosetWt_rhoW k w).trans hw

@[expose] def seedWt (s : ℕ) : ℕ := if s = 0 then 0 else if s = 1 then 1 else if s = 3 then 2 else 3

theorem cosetWt_wv_seed
    {s : ℕ} (hs : s ∈ [0, 1, 3, 7]) : cosetWt (wv s) = seedWt s := by
  obtain ⟨h0, h1, h3, h7⟩ := cosetWt_seed
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h3
  · exact h7

theorem Lw_eq_orbitW
    {s : ℕ} (hs : s ∈ [0, 1, 3, 7]) : Lw (seedWt s) = orbitW (wv s) := by
  refine Set.Subset.antisymm (fun w hw => ?_) ((cosetWt_wv_seed hs) ▸ orbitW_subset_Lw)
  obtain ⟨u, hu, rfl⟩ := wv_surj w
  have key : ∀ s' ∈ [0, 1, 3, 7], u ∈ (wCert s').pts.toList → s' = s := by
    intro s' hs' hus'
    have h1 := orbitW_subset_Lw (mem_orbitW hs' hus')
    rw [cosetWt_wv_seed hs'] at h1
    have h2 : seedWt s' = seedWt s := h1.symm.trans hw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs hs'
    rcases hs with rfl | rfl | rfl | rfl <;> rcases hs' with rfl | rfl | rfl | rfl <;>
      simp_all [seedWt]
  rcases wCert_cover u hu with h | h | h | h
  · rw [← key 0 (by simp) h]; exact mem_orbitW (by simp) h
  · rw [← key 1 (by simp) h]; exact mem_orbitW (by simp) h
  · rw [← key 3 (by simp) h]; exact mem_orbitW (by simp) h
  · rw [← key 7 (by simp) h]; exact mem_orbitW (by simp) h

theorem orbitW_zero :
    orbitW 0 = {0} := by
  ext w
  simp only [orbitW, Set.mem_range, map_zero, Set.mem_singleton_iff]
  exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨1, h.symm⟩⟩

theorem W₀_cover
    (w : W₀) : w = 0 ∨ w ∈ Lw 1 ∨ w ∈ Lw 2 ∨ w ∈ Lw 3 := by
  obtain ⟨u, hu, rfl⟩ := wv_surj w
  rcases wCert_cover u hu with h | h | h | h
  · left
    have := mem_orbitW (s := 0) (by simp) h
    rwa [wv_zero, orbitW_zero] at this
  · exact Or.inr (Or.inl ((Lw_eq_orbitW (s := 1) (by simp)).symm ▸ mem_orbitW (by simp) h))
  · exact Or.inr (Or.inr (Or.inl ((Lw_eq_orbitW (s := 3) (by simp)).symm ▸
      mem_orbitW (by simp) h)))
  · exact Or.inr (Or.inr (Or.inr ((Lw_eq_orbitW (s := 7) (by simp)).symm ▸
      mem_orbitW (by simp) h)))

@[expose] noncomputable def decZn
    (n : ℕ) : Z := zMk (hRep (n / 32)) (qv (n % 32))

theorem decY_Zn
    {n : ℕ} (hn : n < 2464) : decY (1046 + n) = .inr (.inr (decZn n)) := by
  have := decY_Z (i := n / 32) (q := n % 32) (by omega) (Nat.mod_lt _ (by norm_num))
  rwa [show 1046 + 32 * (n / 32) + n % 32 = 1046 + n by omega] at this

theorem kF_smul_Z
    (k : CFSG.Blueprint.NativeSporadic.M22) (z : Z) :
    kF k • (.inr (.inr z) : Y) = .inr (.inr (zK k z)) := by
  obtain ⟨l, q, rfl⟩ := zMk_surj z
  exact (smul_mk k l 0 0 (coordAt 0) q).2.2.1

theorem kF_smul_W
    (k : CFSG.Blueprint.NativeSporadic.M22) (w : W₀) :
    kF k • (.inr (.inl w) : Y) = .inr (.inl (rhoW k w)) :=
  (smul_mk k 1 0 w (coordAt 0) 0).2.1

theorem decZn_inj
    {a b : ℕ} (ha : a < 2464) (hb : b < 2464) (h : decZn a = decZn b) : a = b := by
  have e : ∀ n (hn : n < 2464), decZn n = zEquiv (⟨n / 32, by omega⟩, qEquiv ⟨n % 32,
      Nat.mod_lt _ (by norm_num)⟩) := fun n _ => rfl
  rw [e a ha, e b hb] at h
  have h' := zEquiv.injective h
  simp only [Prod.mk.injEq, Fin.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h'
  omega

section Zsec

attribute [local instance] zActK

theorem decZn_act :
    ∀ g < 2, ∀ n, decide (n < 2464) = true →
    decZn (zAct g n) = genAB g • decZn n := by
  intro g hg n hn
  have hn' : n < 2464 := of_decide_eq_true hn
  have hrep : RepArr (kF (genAB g)) (indAB g) := (indAB_eq g hg).symm ▸ repArr_gen hg
  obtain ⟨hlt, e⟩ := hrep (1046 + n) (by omega)
  obtain ⟨hge, hlt'⟩ := zAct_range g hg n hn'
  have hz : (indAB g)[1046 + n]! = 1046 + zAct g n := by
    unfold zAct
    omega
  have hzlt : zAct g n < 2464 := by omega
  rw [hz, decY_Zn hzlt, decY_Zn hn', kF_smul_Z] at e
  exact Sum.inr_injective (Sum.inr_injective e)

theorem decZn_inj' :
    ∀ a b, decide (a < 2464) = true → decide (b < 2464) = true →
    decZn a = decZn b → a = b := fun _ _ ha hb e =>
  decZn_inj (of_decide_eq_true ha) (of_decide_eq_true hb) e

theorem orbitZ_eq_orbit
    (z : Z) : orbitZ z = MulAction.orbit CFSG.Blueprint.NativeSporadic.M22 z :=
  rfl

theorem orbitZ_cert
    {s : ℕ} (hs : s ∈ [0, 24, 1]) :
    orbitZ (decZn s) = (fun i => decZn (zCert s).pts[i]!) '' {i | i < (zCert s).pts.size} := by
  rw [orbitZ_eq_orbit, ← orbit_closure_eq closure_genAB]
  exact orbit_of_natCertOK (zCert_ok s hs) decZn_act

theorem ncard_orbitZ
    {s : ℕ} (hs : s ∈ [0, 24, 1]) :
    (orbitZ (decZn s)).ncard = (zCert s).pts.size := by
  rw [orbitZ_eq_orbit, ← orbit_closure_eq closure_genAB]
  exact ncard_orbit_of_natCertOK (zCert_ok s hs) decZn_act decZn_inj'

theorem mem_orbitZ
    {s : ℕ} (hs : s ∈ [0, 24, 1]) {n : ℕ} (hn : n ∈ (zCert s).pts.toList) :
    decZn n ∈ orbitZ (decZn s) := by
  rw [orbitZ_cert hs]
  obtain ⟨i, hi, rfl⟩ := exists_idx hn
  exact ⟨i, hi, rfl⟩

theorem orbitZ_mem
    {s : ℕ} (hs : s ∈ [0, 24, 1]) {z : Z} (hz : z ∈ orbitZ (decZn s)) :
    ∃ n ∈ (zCert s).pts.toList, n < 2464 ∧ decZn n = z := by
  rw [orbitZ_cert hs] at hz
  obtain ⟨i, hi, rfl⟩ := hz
  exact ⟨_, mem_toList hi, of_decide_eq_true (natCertOK_valid (zCert_ok s hs) hi), rfl⟩

end Zsec

@[expose] noncomputable def Z462 :
    Set Z := orbitZ (decZn 0)

@[expose] noncomputable def Z770 :
    Set Z := orbitZ (decZn 24)

@[expose] noncomputable def Z1232 :
    Set Z := orbitZ (decZn 1)

theorem decZn_surj
    (z : Z) : ∃ n < 2464, decZn n = z := by
  obtain ⟨⟨i, q⟩, rfl⟩ := zEquiv.surjective z
  obtain ⟨m, hm, rfl⟩ := qv_surj q
  refine ⟨32 * i + m, by omega, ?_⟩
  rw [decZn, zEquiv_apply, show (32 * (i : ℕ) + m) / 32 = i by omega,
    show (32 * (i : ℕ) + m) % 32 = m by omega]

theorem Z_cover
    (z : Z) : z ∈ Z462 ∨ z ∈ Z770 ∨ z ∈ Z1232 := by
  obtain ⟨n, hn, rfl⟩ := decZn_surj z
  rcases zCert_cover n hn with h | h | h
  · exact Or.inl (mem_orbitZ (by simp) h)
  · exact Or.inr (Or.inl (mem_orbitZ (by simp) h))
  · exact Or.inr (Or.inr (mem_orbitZ (by simp) h))

theorem zK_mem_orbitZ
    (k : CFSG.Blueprint.NativeSporadic.M22) {z z₀ : Z} (hz : z ∈ orbitZ z₀) :
    zK k z ∈ orbitZ z₀ := by
  obtain ⟨l, rfl⟩ := hz
  exact ⟨k * l, zK_mul k l z₀⟩

theorem kF_mul
    (k l : CFSG.Blueprint.NativeSporadic.M22) : kF (k * l) = kF k * kF l :=
  map_mul SemidirectProduct.inr k l

theorem amulN_size (s x : Array ℕ) : (amulN s x).size = x.size := by
  rw [amulN, Array.size_map]

theorem wordArr_size' (w : List ℤ) : (wordArr w).size = 3510 := by
  induction w with
  | nil => simp only [wordArr, List.foldr_nil, idArrN, List.size_toArray, List.length_range]
  | cons z w ih =>
    change (amulN (genArr z) (wordArr w)).size = 3510
    rw [amulN_size, ih]

theorem repArr_one :
    RepArr 1 (idArrN 3510) := by
  intro n hn
  rw [idArrN_get hn, one_smul]
  exact ⟨hn, rfl⟩

theorem genArr_one : genArr 1 = indM22Gen 0 := by
  simp only [genArr, ↓reduceIte, indA]

theorem genArr_two : genArr 2 = indM22Gen 1 := by
  simp only [genArr, Int.reduceEq, ↓reduceIte, indB]

theorem letterM22_one : letterM22 1 = m22a := by
  simp only [letterM22, ↓reduceIte]

theorem letterM22_two : letterM22 2 = m22b := by
  simp only [letterM22, Int.reduceEq, Int.reduceNeg, ↓reduceIte]

theorem repArr_word
    {w : List ℤ} (hw : ∀ z ∈ w, z = 1 ∨ z = 2) :
    RepArr (kF (wordM22 w)) (wordArr w) := by
  induction w with
  | nil =>
    rw [show wordM22 [] = 1 from rfl, show kF 1 = 1 from map_one SemidirectProduct.inr]
    exact repArr_one
  | cons z w ih =>
    have ih' := ih fun x hx => hw x (List.mem_cons_of_mem _ hx)
    rw [show wordM22 (z :: w) = letterM22 z * wordM22 w from rfl, kF_mul]
    have hl : RepArr (kF (letterM22 z)) (genArr z) := by
      rcases hw z (List.mem_cons_self ..) with rfl | rfl
      · rw [genArr_one, letterM22_one]
        exact repArr_a
      · rw [genArr_two, letterM22_two]
        exact repArr_b
    exact hl.mul ih' (wordArr_size' w)

@[expose] noncomputable def sElt (k : ℕ) : CFSG.Blueprint.NativeSporadic.M22 := wordM22 (sWord k)

@[expose] noncomputable def s2Elt (k : ℕ) : CFSG.Blueprint.NativeSporadic.M22 := wordM22 (s2Word k)

theorem repArr_sElt
    {k : ℕ} (hk : k < 4) : RepArr (kF (sElt k)) (sArrs[k]!) := by
  rw [sArrs_get k hk]
  exact repArr_word (sWord_letters k hk)

theorem repArr_s2Elt
    {k : ℕ} (hk : k < 3) : RepArr (kF (s2Elt k)) (s2Arrs[k]!) := by
  rw [s2Arrs_get k hk]
  exact repArr_word (s2Word_letters k hk)

theorem fixed_iff
    {g : F₀} {arr : Array ℕ} (h : RepArr g arr) {n : ℕ} (hn : n < 3510) :
    g • decY n = decY n ↔ arr[n]! = n := by
  obtain ⟨hlt, e⟩ := h n hn
  rw [← e]
  constructor
  · intro h'
    rw [← ι_decY hlt, h', ι_decY hn]
  · intro h'
    rw [h']

theorem sElt_fix_seed
    (k : ℕ) (hk : k < 4) : rhoW (sElt k) (wv 7) = wv 7 := by
  have := (fixed_iff (repArr_sElt hk) (n := 22 + 7) (by norm_num)).2 (sFix k hk)
  rw [decY_W (by norm_num), kF_smul_W] at this
  exact Sum.inl_injective (Sum.inr_injective this)

theorem eq_seed_of_fixed
    {w : W₀} (hw : w ∈ Lw 3) (hfix : ∀ k < 4, rhoW (sElt k) w = w) :
    w = wv 7 := by
  rw [show Lw 3 = orbitW (wv 7) from Lw_eq_orbitW (s := 7) (by simp)] at hw
  obtain ⟨u, hu, hult, rfl⟩ := orbitW_mem (by simp) hw
  have h : ∀ k < 4, (sArrs[k]!)[22 + u]! = 22 + u := by
    intro k hk
    refine (fixed_iff (repArr_sElt hk) (n := 22 + u) (by omega)).1 ?_
    rw [decY_W hult, kF_smul_W, hfix k hk]
  rw [sFix_W u hu h]

theorem eq_z24_of_fixed
    {z : Z} (hz : z ∈ Z770) (hfix : ∀ k < 4, zK (sElt k) z = z) :
    z = decZn 24 := by
  obtain ⟨n, hn, hnlt, rfl⟩ := orbitZ_mem (by simp) hz
  have h : ∀ k < 4, (sArrs[k]!)[1046 + n]! = 1046 + n := by
    intro k hk
    refine (fixed_iff (repArr_sElt hk) (n := 1046 + n) (by omega)).1 ?_
    rw [decY_Zn hnlt, kF_smul_Z, hfix k hk]
  rw [sFix_Z n hn h]

theorem s2Elt_fix_seed
    (k : ℕ) (hk : k < 3) : zK (s2Elt k) (decZn 1) = decZn 1 := by
  have := (fixed_iff (repArr_s2Elt hk) (n := 1046 + 1) (by norm_num)).2 (s2Fix k hk)
  rw [decY_Zn (by norm_num), kF_smul_Z] at this
  exact Sum.inr_injective (Sum.inr_injective this)

theorem eq_z1_or_of_fixed
    {z : Z} (hz : z ∈ Z1232) (hfix : ∀ k < 3, zK (s2Elt k) z = z) :
    z = decZn 1 ∨ z = decZn 277 := by
  obtain ⟨n, hn, hnlt, rfl⟩ := orbitZ_mem (by simp) hz
  have h : ∀ k < 3, (s2Arrs[k]!)[1046 + n]! = 1046 + n := by
    intro k hk
    refine (fixed_iff (repArr_s2Elt hk) (n := 1046 + n) (by omega)).1 ?_
    rw [decY_Zn hnlt, kF_smul_Z, hfix k hk]
  rcases s2Fix_Z n hn h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

abbrev L3 : Type := ↥(Lw 3)

abbrev Z770T :
    Type := ↥Z770

abbrev Z1232T :
    Type := ↥Z1232

@[expose] noncomputable def kL
    (k : CFSG.Blueprint.NativeSporadic.M22) (w : L3) : L3 :=
  ⟨rhoW k w, rhoW_mem_Lw k w.2⟩

@[expose] noncomputable def kZ7
    (k : CFSG.Blueprint.NativeSporadic.M22) (z : Z770T) : Z770T :=
  ⟨zK k z, zK_mem_orbitZ k z.2⟩

@[expose] noncomputable def kZ12
    (k : CFSG.Blueprint.NativeSporadic.M22) (z : Z1232T) : Z1232T :=
  ⟨zK k z, zK_mem_orbitZ k z.2⟩

@[expose] noncomputable def idxW (w : W₀) : ℕ := wEquiv.symm w

theorem idxW_wv {u : ℕ} (hu : u < 1024) : idxW (wv u) = u := by
  rw [idxW, show wv u = wEquiv ⟨u, hu⟩ from rfl, Equiv.symm_apply_apply]

@[expose] noncomputable def idxZ
    (z : Z) : ℕ :=
  32 * (zEquiv.symm z).1 + qEquiv.symm (zEquiv.symm z).2

theorem idxZ_decZn
    {n : ℕ} (hn : n < 2464) : idxZ (decZn n) = n := by
  have e : decZn n = zEquiv (⟨n / 32, by omega⟩, qEquiv ⟨n % 32, Nat.mod_lt _ (by norm_num)⟩) :=
    rfl
  rw [idxZ, e, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simp only
  omega

theorem L3_eq :
    Lw 3 = orbitW (wv 7) := Lw_eq_orbitW (s := 7) (by simp)

theorem L3_mem
    (w : L3) : ∃ u ∈ (wCert 7).pts.toList, u < 1024 ∧ wv u = w :=
  orbitW_mem (s := 7) (by simp) (show (w : W₀) ∈ orbitW (wv 7) from L3_eq ▸ w.2)

theorem sigma_mem
    (w : L3) : decZn (sigmaFun (idxW w)) ∈ Z770 := by
  obtain ⟨u, hu, hult, e⟩ := L3_mem w
  rw [← e, idxW_wv hult]
  exact mem_orbitZ (by simp) (sigma_check.2.1 u hu).1

@[expose] noncomputable def sigmaL
    (w : L3) : Z770T := ⟨decZn (sigmaFun (idxW w)), sigma_mem w⟩

theorem sigmaL_gen
    {g : ℕ} (hg : g < 2) (w : L3) :
    sigmaL (kL (genAB g) w) = kZ7 (genAB g) (sigmaL w) := by
  apply Subtype.ext
  obtain ⟨u, hu, hult, e⟩ := L3_mem w
  change decZn (sigmaFun (idxW (rhoW (genAB g) w))) = zK (genAB g) (decZn (sigmaFun (idxW w)))
  rw [← e, rhoW_wv hg hult, idxW_wv (linW_lt g hg u hult), idxW_wv hult,
    (sigma_check.2.1 u hu).2 g hg]
  have hz := (sigma_check.2.1 u hu).1
  obtain ⟨i, hi, hiu⟩ := exists_idx hz
  have hlt : sigmaFun u < 2464 := by
    rw [← hiu]
    exact of_decide_eq_true (natCertOK_valid (zCert_ok 24 (by simp)) hi)
  exact decZn_act g hg _ (decide_eq_true hlt)

theorem sigmaL_equivariant
    (k : CFSG.Blueprint.NativeSporadic.M22) (w : L3) :
    sigmaL (kL k w) = kZ7 k (sigmaL w) := by
  revert w
  refine m22_induction (P := fun k => ∀ w, sigmaL (kL k w) = kZ7 k (sigmaL w)) ?_ ?_ ?_ ?_ ?_ k
  · exact sigmaL_gen (g := 0) (by norm_num)
  · exact sigmaL_gen (g := 1) (by norm_num)
  · intro x y hx hy w
    have e1 : kL (x * y) w = kL x (kL y w) := Subtype.ext (by simp [kL, map_mul])
    have e2 : ∀ z, kZ7 (x * y) z = kZ7 x (kZ7 y z) := fun z => Subtype.ext (zK_mul x y z)
    rw [e1, hx, hy, e2]
  · intro x hx w
    have e : kL x (kL x⁻¹ w) = w := Subtype.ext (by
      change rhoW x (rhoW x⁻¹ w) = w
      exact rhoW_apply_inv x w)
    have e3 : ∀ z, kZ7 x⁻¹ (kZ7 x z) = z := fun z => Subtype.ext (by
      change zK x⁻¹ (zK x z) = z
      rw [← zK_mul, inv_mul_cancel, zK_one])
    have h1 := hx (kL x⁻¹ w)
    rw [e] at h1
    rw [h1, e3]
  · intro w
    have e1 : kL 1 w = w := Subtype.ext (by simp [kL])
    have e2 : ∀ z, kZ7 1 z = z := fun z => Subtype.ext (zK_one z)
    rw [e1, e2]

theorem natCard_L3 :
    Nat.card L3 = 770 := by
  rw [Nat.card_coe_set_eq, L3_eq, ncard_orbitW (by simp), wCert_size.2.2.2]

theorem natCard_Z770 :
    Nat.card Z770T = 770 := by
  rw [Nat.card_coe_set_eq, Z770, ncard_orbitZ (by simp), zCert_size.2.1]

theorem sigmaL_injective :
    Function.Injective sigmaL := by
  intro w w' h
  obtain ⟨u, hu, hult, e⟩ := L3_mem w
  obtain ⟨u', hu', hult', e'⟩ := L3_mem w'
  have h' : decZn (sigmaFun (idxW w)) = decZn (sigmaFun (idxW w')) := congrArg Subtype.val h
  rw [← e, ← e', idxW_wv hult, idxW_wv hult'] at h'
  have hlt : ∀ v ∈ (wCert 7).pts.toList, sigmaFun v < 2464 := by
    intro v hv
    obtain ⟨i, hi, hiv⟩ := exists_idx (sigma_check.2.1 v hv).1
    rw [← hiv]
    exact of_decide_eq_true (natCertOK_valid (zCert_ok 24 (by simp)) hi)
  have := sigma_check.2.2 u hu u' hu' (decZn_inj (hlt u hu) (hlt u' hu') h')
  apply Subtype.ext
  rw [← e, ← e', this]

theorem sigmaL_bijective :
    Function.Bijective sigmaL :=
  sigmaL_injective.bijective_of_nat_card_le (by rw [natCard_L3, natCard_Z770])

@[expose] noncomputable def sigmaEquiv :
    L3 ≃ Z770T := Equiv.ofBijective sigmaL sigmaL_bijective

@[expose] noncomputable def w7 :
    L3 := ⟨wv 7, L3_eq ▸ (⟨1, by simp⟩ : wv 7 ∈ orbitW (wv 7))⟩

theorem w7_val :
    (w7 : W₀) = wv 7 := rfl

theorem sigmaL_val
    (w : L3) : (sigmaL w : Z) = decZn (sigmaFun (idxW w)) := rfl

theorem kL_s_w7
    (k : ℕ) (hk : k < 4) : kL (sElt k) w7 = w7 := Subtype.ext (sElt_fix_seed k hk)

theorem L3_transitive
    (w : L3) : ∃ k, kL k w7 = w := by
  obtain ⟨k, hk⟩ := (show (w : W₀) ∈ orbitW (wv 7) from L3_eq ▸ w.2)
  exact ⟨k, Subtype.ext hk⟩

theorem eq_sigmaL
    {f : L3 → Z770T} (hf : ∀ k w, f (kL k w) = kZ7 k (f w)) : f = sigmaL := by
  have h7 : f w7 = sigmaL w7 := by
    have hfix : ∀ k < 4, zK (sElt k) (f w7 : Z) = f w7 := by
      intro k hk
      have := hf (sElt k) w7
      rw [kL_s_w7 k hk] at this
      exact (congrArg Subtype.val this).symm
    apply Subtype.ext
    rw [eq_z24_of_fixed (f w7).2 hfix, sigmaL_val, w7_val, idxW_wv (by norm_num),
      sigma_check.1]
  funext w
  obtain ⟨k, rfl⟩ := L3_transitive w
  rw [hf, h7, sigmaL_equivariant]

theorem centralizer_L3
    {c : Equiv.Perm L3} (hc : ∀ k w, c (kL k w) = kL k (c w)) : c = 1 := by
  have h7 : c w7 = w7 := by
    have hfix : ∀ k < 4, rhoW (sElt k) (c w7 : W₀) = c w7 := by
      intro k hk
      have := hc (sElt k) w7
      rw [kL_s_w7 k hk] at this
      exact (congrArg Subtype.val this).symm
    exact Subtype.ext (eq_seed_of_fixed (c w7).2 hfix)
  ext w
  obtain ⟨k, rfl⟩ := L3_transitive w
  rw [hc, h7]
  rfl

theorem tau_lt
    {n : ℕ} (hn : n ∈ (zCert 1).pts.toList) : tauFun n < 2464 := by
  obtain ⟨i, hi, hin⟩ := exists_idx (tau_check.2 n hn).1
  rw [← hin]
  exact of_decide_eq_true (natCertOK_valid (zCert_ok 1 (by simp)) hi)

theorem Z1232_mem
    (z : Z1232T) : ∃ n ∈ (zCert 1).pts.toList, n < 2464 ∧ decZn n = z :=
  orbitZ_mem (by simp) z.2

theorem tau_mem
    (z : Z1232T) : decZn (tauFun (idxZ z)) ∈ Z1232 := by
  obtain ⟨n, hn, hnlt, e⟩ := Z1232_mem z
  rw [← e, idxZ_decZn hnlt]
  exact mem_orbitZ (by simp) (tau_check.2 n hn).1

@[expose] noncomputable def tauL
    (z : Z1232T) : Z1232T := ⟨decZn (tauFun (idxZ z)), tau_mem z⟩

theorem tauL_decZn
    {n : ℕ} (hn : n ∈ (zCert 1).pts.toList) (hnlt : n < 2464) (h) :
    tauL ⟨decZn n, h⟩ = ⟨decZn (tauFun n), mem_orbitZ (by simp) (tau_check.2 n hn).1⟩ := by
  apply Subtype.ext
  change decZn (tauFun (idxZ (decZn n))) = _
  rw [idxZ_decZn hnlt]

theorem tauL_tauL
    (z : Z1232T) : tauL (tauL z) = z := by
  obtain ⟨n, hn, hnlt, e⟩ := Z1232_mem z
  apply Subtype.ext
  change decZn (tauFun (idxZ (decZn (tauFun (idxZ z))))) = z
  rw [← e, idxZ_decZn hnlt, idxZ_decZn (tau_lt hn), (tau_check.2 n hn).2.1]

theorem tauL_ne
    (z : Z1232T) : tauL z ≠ z := by
  obtain ⟨n, hn, hnlt, e⟩ := Z1232_mem z
  intro h
  have h' : decZn (tauFun (idxZ z)) = z := congrArg Subtype.val h
  rw [← e, idxZ_decZn hnlt] at h'
  exact (tau_check.2 n hn).2.2.1 (decZn_inj (tau_lt hn) hnlt h')

@[expose] noncomputable def tauPerm :
    Equiv.Perm Z1232T where
  toFun := tauL
  invFun := tauL
  left_inv := tauL_tauL
  right_inv := tauL_tauL

theorem tauPerm_apply
    (z : Z1232T) : tauPerm z = tauL z := rfl

theorem tauL_gen
    {g : ℕ} (hg : g < 2) (z : Z1232T) :
    tauL (kZ12 (genAB g) z) = kZ12 (genAB g) (tauL z) := by
  obtain ⟨n, hn, hnlt, e⟩ := Z1232_mem z
  apply Subtype.ext
  change decZn (tauFun (idxZ (zK (genAB g) z))) = zK (genAB g) (decZn (tauFun (idxZ z)))
  have hact := decZn_act g hg n (decide_eq_true hnlt)
  have hact' := decZn_act g hg (tauFun n) (decide_eq_true (tau_lt hn))
  change decZn (zAct g n) = zK (genAB g) (decZn n) at hact
  change decZn (zAct g (tauFun n)) = zK (genAB g) (decZn (tauFun n)) at hact'
  have hlt : zAct g n < 2464 := by
    have := zAct_range g hg n hnlt
    unfold zAct
    omega
  rw [← e, ← hact, idxZ_decZn hlt, idxZ_decZn hnlt, (tau_check.2 n hn).2.2.2 g hg, hact']

theorem tauL_equivariant
    (k : CFSG.Blueprint.NativeSporadic.M22) (z : Z1232T) :
    tauL (kZ12 k z) = kZ12 k (tauL z) := by
  revert z
  refine m22_induction (P := fun k => ∀ z, tauL (kZ12 k z) = kZ12 k (tauL z)) ?_ ?_ ?_ ?_ ?_ k
  · exact tauL_gen (g := 0) (by norm_num)
  · exact tauL_gen (g := 1) (by norm_num)
  · intro x y hx hy z
    have e2 : ∀ z, kZ12 (x * y) z = kZ12 x (kZ12 y z) := fun z => Subtype.ext (zK_mul x y z)
    rw [e2, hx, hy, e2]
  · intro x hx z
    have e2 : ∀ z, kZ12 x (kZ12 x⁻¹ z) = z := fun z => Subtype.ext (by
      change zK x (zK x⁻¹ z) = z
      rw [← zK_mul, mul_inv_cancel, zK_one])
    have e3 : ∀ z, kZ12 x⁻¹ (kZ12 x z) = z := fun z => Subtype.ext (by
      change zK x⁻¹ (zK x z) = z
      rw [← zK_mul, inv_mul_cancel, zK_one])
    have := hx (kZ12 x⁻¹ z)
    rw [e2] at this
    rw [this, e3]
  · intro z
    have e2 : ∀ z, kZ12 1 z = z := fun z => Subtype.ext (zK_one z)
    rw [e2, e2]

@[expose] noncomputable def z1 :
    Z1232T := ⟨decZn 1, ⟨1, zK_one _⟩⟩

theorem Z1232_transitive
    (z : Z1232T) : ∃ k, kZ12 k z1 = z := by
  obtain ⟨k, hk⟩ := z.2
  exact ⟨k, Subtype.ext hk⟩

theorem z1_val :
    (z1 : Z) = decZn 1 := rfl

theorem tauL_val
    (z : Z1232T) : (tauL z : Z) = decZn (tauFun (idxZ z)) := rfl

theorem tauL_z1 :
    (tauL z1 : Z) = decZn 277 := by
  rw [tauL_val, z1_val, idxZ_decZn (by norm_num), tau_check.1]

theorem centralizer_Z1232
    {c : Equiv.Perm Z1232T} (hc : ∀ k z, c (kZ12 k z) = kZ12 k (c z)) :
    c = 1 ∨ c = tauPerm := by
  have hfix : ∀ k < 3, zK (s2Elt k) (c z1 : Z) = c z1 := by
    intro k hk
    have e1 : kZ12 (s2Elt k) z1 = z1 := Subtype.ext (s2Elt_fix_seed k hk)
    have := hc (s2Elt k) z1
    rw [e1] at this
    exact (congrArg Subtype.val this).symm
  have hext : ∀ c' : Equiv.Perm Z1232T, (∀ k z, c' (kZ12 k z) = kZ12 k (c' z)) →
      c z1 = c' z1 → c = c' := by
    intro c' hc' h
    ext z
    obtain ⟨k, rfl⟩ := Z1232_transitive z
    rw [hc, hc', h]
  rcases eq_z1_or_of_fixed (c z1).2 hfix with h | h
  · left
    refine hext 1 (fun _ _ => rfl) (Subtype.ext h)
  · right
    refine hext tauPerm (fun k z => tauL_equivariant k z) (Subtype.ext ?_)
    rw [h, tauPerm_apply, tauL_z1]

theorem tauPerm_ne_one :
    tauPerm ≠ 1 := fun h => tauL_ne z1 (congrArg (· z1) h)

theorem natCard_centralizer_Z1232 :
    Nat.card {c : Equiv.Perm Z1232T // ∀ k z, c (kZ12 k z) = kZ12 k (c z)} = 2 := by
  have hset : {c : Equiv.Perm Z1232T | ∀ k z, c (kZ12 k z) = kZ12 k (c z)} =
      {1, tauPerm} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    refine ⟨centralizer_Z1232, ?_⟩
    rintro (rfl | rfl)
    · exact fun _ _ => rfl
    · exact fun k z => tauL_equivariant k z
  calc Nat.card {c : Equiv.Perm Z1232T // ∀ k z, c (kZ12 k z) = kZ12 k (c z)}
      = Nat.card ↥({1, tauPerm} : Set (Equiv.Perm Z1232T)) := by rw [← hset]; rfl
    _ = 2 := by rw [Nat.card_coe_set_eq, Set.ncard_pair tauPerm_ne_one.symm]

@[expose] def wCoord : Fin 10 → Fin 24 := ![2, 3, 4, 5, 6, 8, 9, 10, 12, 16]

theorem wCoord_mem : ∀ t, wCoord t ∈ X₀ := by decide

@[expose] noncomputable def bW' (t : Fin 10) : W₀ := wv (2 ^ (t : ℕ))

theorem spreadW_two_pow : ∀ t < 10, spreadW (2 ^ t) = 2 ^ freeW t := by decide +kernel

theorem wv_eq_sum (u : ℕ) : wv u = ∑ t : Fin 10, if u.testBit t then bW' t else 0 := by
  rw [wv, spreadW, vecOf_xorSel, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs
  · rw [bW', wv, spreadW_two_pow t t.2]
  · exact map_zero _

theorem span_bW' : Submodule.span (ZMod 2) (Set.range bW') = ⊤ := by
  rw [eq_top_iff]
  intro w _
  obtain ⟨u, -, rfl⟩ := wv_surj w
  rw [wv_eq_sum]
  refine Submodule.sum_mem _ fun t _ => ?_
  split_ifs
  · exact Submodule.subset_span ⟨t, rfl⟩
  · exact Submodule.zero_mem _

@[expose] noncomputable def bW :
    Module.Basis (Fin 10) (ZMod 2) W₀ :=
  basisOfTopLeSpanOfCardEqFinrank bW' span_bW'.ge (by rw [Fintype.card_fin, finrank_W₀])

theorem bW_eq (t : Fin 10) : bW t = bW' t := by
  rw [bW, coe_basisOfTopLeSpanOfCardEqFinrank]

theorem bW_apply
    (t : Fin 10) : bW t = K₀.mkQ (e ⟨wCoord t, wCoord_mem t⟩) := by
  rw [bW_eq, bW', wv, spreadW_two_pow t t.2, vecOf_two_pow ⟨freeW t, freeW_lt t⟩]
  congr 2
  apply Subtype.ext
  apply Fin.ext
  revert t
  decide

theorem wv_eq_sum_bW
    (u : ℕ) : wv u = ∑ t : Fin 10, if u.testBit t then bW t else 0 := by
  simp only [bW_eq]
  exact wv_eq_sum u

theorem L1_eq :
    Lw 1 = orbitW (wv 1) := Lw_eq_orbitW (s := 1) (by simp)

theorem L2_eq :
    Lw 2 = orbitW (wv 3) := Lw_eq_orbitW (s := 3) (by simp)

section Orb

attribute [local instance] wActK zActK

theorem orbitW_eq_of_mem
    {w v : W₀} (h : w ∈ orbitW v) : orbitW w = orbitW v :=
  MulAction.orbit_eq_iff.2 h

theorem orbitZ_eq_of_mem
    {z z' : Z} (h : z ∈ orbitZ z') : orbitZ z = orbitZ z' :=
  MulAction.orbit_eq_iff.2 h

end Orb

theorem orbitW_cases
    (w : W₀) :
    orbitW w = {0} ∨ orbitW w = Lw 1 ∨ orbitW w = Lw 2 ∨ orbitW w = Lw 3 := by
  rcases W₀_cover w with rfl | h | h | h
  · exact Or.inl orbitW_zero
  · rw [L1_eq] at h ⊢
    exact Or.inr (Or.inl (orbitW_eq_of_mem h))
  · rw [L2_eq] at h ⊢
    exact Or.inr (Or.inr (Or.inl (orbitW_eq_of_mem h)))
  · rw [L3_eq] at h ⊢
    exact Or.inr (Or.inr (Or.inr (orbitW_eq_of_mem h)))

theorem orbitZ_cases
    (z : Z) : orbitZ z = Z462 ∨ orbitZ z = Z770 ∨ orbitZ z = Z1232 := by
  rcases Z_cover z with h | h | h
  · exact Or.inl (orbitZ_eq_of_mem h)
  · exact Or.inr (Or.inl (orbitZ_eq_of_mem h))
  · exact Or.inr (Or.inr (orbitZ_eq_of_mem h))

theorem ι_decZn
    {n : ℕ} (hn : n < 2464) : (ι (.inr (.inr (decZn n))) : ℕ) = 1046 + n := by
  rw [← decY_Zn hn, ι_decY (by omega)]

theorem sigma_lt
    {u : ℕ} (hu : u ∈ (wCert 7).pts.toList) : sigmaFun u < 2464 := by
  obtain ⟨i, hi, hiu⟩ := exists_idx (sigma_check.2.1 u hu).1
  rw [← hiu]
  exact of_decide_eq_true (natCertOK_valid (zCert_ok 24 (by simp)) hi)

theorem wCert7_lt
    {u : ℕ} (hu : u ∈ (wCert 7).pts.toList) : u < 1024 := by
  obtain ⟨i, hi, rfl⟩ := exists_idx hu
  exact of_decide_eq_true (natCertOK_valid (wCert_ok 7 (by simp)) hi)

theorem zCert1_lt
    {n : ℕ} (hn : n ∈ (zCert 1).pts.toList) : n < 2464 := by
  obtain ⟨i, hi, rfl⟩ := exists_idx hn
  exact of_decide_eq_true (natCertOK_valid (zCert_ok 1 (by simp)) hi)

theorem ι_sigma
    (w : L3) : ∃ u ∈ (wCert 7).pts.toList, (ι (.inr (.inl (w : W₀))) : ℕ) = 22 + u ∧
    (ι (.inr (.inr (sigmaEquiv w : Z))) : ℕ) = 1046 + sigmaFun u := by
  obtain ⟨u, hu, hult, e⟩ := L3_mem w
  refine ⟨u, hu, by rw [← e, ι_wv hult], ?_⟩
  change (ι (.inr (.inr (sigmaL w : Z))) : ℕ) = _
  rw [sigmaL_val, ← e, idxW_wv hult, ι_decZn (sigma_lt hu)]

theorem ι_tau
    (z : Z1232T) : ∃ n ∈ (zCert 1).pts.toList, (ι (.inr (.inr (z : Z))) : ℕ) = 1046 + n ∧
    (ι (.inr (.inr (tauPerm z : Z))) : ℕ) = 1046 + tauFun n := by
  obtain ⟨n, hn, hnlt, e⟩ := Z1232_mem z
  refine ⟨n, hn, by rw [← e, ι_decZn hnlt], ?_⟩
  rw [tauPerm_apply, tauL_val, ← e, idxZ_decZn hnlt, ι_decZn (tau_lt hn)]

theorem Fischer_induced_Mathieu_orbits_and_centralizers :
    (∀ (k : CFSG.Blueprint.NativeSporadic.M22) (w : W₀),
      kF k • (.inr (.inl w) : Y) = .inr (.inl (rhoW k w))) ∧
    (∀ (k : CFSG.Blueprint.NativeSporadic.M22) (z : Z),
      kF k • (.inr (.inr z) : Y) = .inr (.inr (zK k z))) ∧
    orbitW 0 = {0} ∧ orbitW (wv 1) = Lw 1 ∧ orbitW (wv 3) = Lw 2 ∧ orbitW (wv 7) = Lw 3 ∧
    (∀ w : W₀, orbitW w = {0} ∨ orbitW w = Lw 1 ∨ orbitW w = Lw 2 ∨ orbitW w = Lw 3) ∧
    (Lw 1).ncard = 22 ∧ (Lw 2).ncard = 231 ∧ (Lw 3).ncard = 770 ∧
    (∀ z : Z, orbitZ z = Z462 ∨ orbitZ z = Z770 ∨ orbitZ z = Z1232) ∧
    Z462.ncard = 462 ∧ Z770.ncard = 770 ∧ Z1232.ncard = 1232 ∧
    (∃! σ : L3 ≃ Z770T, ∀ k w, σ (kL k w) = kZ7 k (σ w)) ∧
    (∀ k w, sigmaEquiv (kL k w) = kZ7 k (sigmaEquiv w)) ∧
    (∀ c : Equiv.Perm L3, (∀ k w, c (kL k w) = kL k (c w)) → c = 1) ∧
    Nat.card {c : Equiv.Perm Z1232T // ∀ k z, c (kZ12 k z) = kZ12 k (c z)} = 2 ∧
    (∀ k z, tauPerm (kZ12 k z) = kZ12 k (tauPerm z)) ∧ tauPerm ≠ 1 ∧
    (∀ c : Equiv.Perm Z1232T, (∀ k z, c (kZ12 k z) = kZ12 k (c z)) → c ≠ 1 → c = tauPerm) ∧
    tauPerm * tauPerm = 1 ∧ (∀ z, tauPerm z ≠ z) ∧
    Function.Bijective ι ∧
    (∀ x : X₀, (ι (.inl x) : ℕ) = ((x : Fin 24) : ℕ) - 2) ∧
    (∀ u < 1024,
      (ι (.inr (.inl (∑ t : Fin 10, if u.testBit t then bW t else 0))) : ℕ) = 22 + u) ∧
    (∀ i < 77, ∀ q < 32,
      (ι (.inr (.inr (zMk (hRep i) (∑ t : Fin 5, if q.testBit t then bQ t else 0)))) : ℕ) =
        1046 + 32 * i + q) ∧
    (∀ k : CFSG.Blueprint.NativeSporadic.M22, ∃ i < 77,
      B₀.map (psiHom (hRep i)).toEmbedding = B₀.map (psiHom k).toEmbedding) ∧
    (∀ i < 76, hexMask (B₀.map (psiHom (hRep i)).toEmbedding) <
      hexMask (B₀.map (psiHom (hRep (i + 1))).toEmbedding)) ∧
    (∀ y : Y, (ι (kF m22a • y) : ℕ) = (indM22Gen 0)[(ι y : ℕ)]!) ∧
    (∀ y : Y, (ι (kF m22b • y) : ℕ) = (indM22Gen 1)[(ι y : ℕ)]!) ∧
    (∀ (t : Fin 10) (y : Y), (ι (wF (bW t) • y) : ℕ) = (indTransGen t)[(ι y : ℕ)]!) ∧
    (∀ w : L3, ((ι (.inr (.inl (w : W₀))) : ℕ) - 22,
      (ι (.inr (.inr (sigmaEquiv w : Z))) : ℕ) - 1046) ∈ indSigma) ∧
    (∀ p ∈ indSigma, ∃ w : L3, (ι (.inr (.inl (w : W₀))) : ℕ) = 22 + p.1 ∧
      (ι (.inr (.inr (sigmaEquiv w : Z))) : ℕ) = 1046 + p.2) ∧
    (∀ z : Z1232T, ((ι (.inr (.inr (z : Z))) : ℕ) - 1046,
      (ι (.inr (.inr (tauPerm z : Z))) : ℕ) - 1046) ∈ indTau) ∧
    (∀ p ∈ indTau, ∃ z : Z1232T, (ι (.inr (.inr (z : Z))) : ℕ) = 1046 + p.1 ∧
      (ι (.inr (.inr (tauPerm z : Z))) : ℕ) = 1046 + p.2) := by
  refine ⟨kF_smul_W, kF_smul_Z, orbitW_zero, L1_eq.symm, L2_eq.symm, L3_eq.symm, orbitW_cases,
    ?_, ?_, ?_, orbitZ_cases, ?_, ?_, ?_, ?_, sigmaL_equivariant, fun c hc => centralizer_L3 hc,
    natCard_centralizer_Z1232, tauL_equivariant, tauPerm_ne_one,
    fun c hc h1 => (centralizer_Z1232 hc).resolve_left h1, Equiv.ext tauL_tauL, tauL_ne,
    ι_bijective, fun x => rfl, ?_, ?_, exists_hRep, ?_, repArr_a.ι_smul, repArr_b.ι_smul, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [L1_eq, ncard_orbitW (by simp), wCert_size.2.1]
  · rw [L2_eq, ncard_orbitW (by simp), wCert_size.2.2.1]
  · rw [L3_eq, ncard_orbitW (by simp), wCert_size.2.2.2]
  · rw [Z462, ncard_orbitZ (by simp), zCert_size.1]
  · rw [Z770, ncard_orbitZ (by simp), zCert_size.2.1]
  · rw [Z1232, ncard_orbitZ (by simp), zCert_size.2.2]
  · exact ⟨sigmaEquiv, sigmaL_equivariant, fun σ hσ => Equiv.coe_fn_injective (eq_sigmaL hσ)⟩
  · intro u hu
    rw [← wv_eq_sum_bW, ι_wv hu]
  · intro i hi q hq
    rw [← qv_eq_sum_bQ, ι_zMk hi hq]
  · intro i hi
    rw [hexad_hRep, hexad_hRep]
    exact hexMask_lt i hi
  · intro t y
    rw [bW_eq]
    exact (repArr_trans t.2).ι_smul y
  · intro w
    obtain ⟨u, hu, e1, e2⟩ := ι_sigma w
    rw [e1, e2, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    exact indSigma_graph u hu
  · intro p hp
    obtain ⟨hp1, hp2⟩ := indSigma_spec p hp
    have hlt := wCert7_lt hp1
    let w : L3 := ⟨wv p.1, L3_eq ▸ mem_orbitW (s := 7) (by simp) hp1⟩
    obtain ⟨u, hu, e1, e2⟩ := ι_sigma w
    have hu' : u = p.1 := by
      have := e1
      rw [show (w : W₀) = wv p.1 from rfl, ι_wv hlt] at this
      omega
    subst hu'
    exact ⟨w, e1, by rw [e2, hp2]⟩
  · intro z
    obtain ⟨n, hn, e1, e2⟩ := ι_tau z
    rw [e1, e2, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    exact indTau_graph n hn
  · intro p hp
    obtain ⟨hp1, hp2⟩ := indTau_spec p hp
    have hlt := zCert1_lt hp1
    let z : Z1232T := ⟨decZn p.1, mem_orbitZ (by simp) hp1⟩
    obtain ⟨n, hn, e1, e2⟩ := ι_tau z
    have hn' : n = p.1 := by
      have := e1
      rw [show (z : Z) = decZn p.1 from rfl, ι_decZn hlt] at this
      omega
    subst hn'
    exact ⟨z, e1, by rw [e2, hp2]⟩

end CFSG.Monster.B.Fischer
