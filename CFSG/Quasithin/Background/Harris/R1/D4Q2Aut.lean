module

public import CFSG.Quasithin.Background.Harris.R1.D4Q2Tab
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Model
public import Certificates.Certificate300206

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Co2.Native CFSG.Quasithin CFSG.Quasithin.D4Hex
open CFSG.Monster.B.Co2 (allLt_spec)

@[expose] noncomputable def y1D : D := d4Word (nWords.getD 0 [])

@[expose] noncomputable def y2D : D := d4Word (nWords.getD 1 [])

@[expose] noncomputable def zeD : D := d4Word (nWords.getD 2 [])

@[expose] noncomputable def r0D : D := d4Word (nWords.getD 3 [])

@[expose] noncomputable def s0D : D := d4Word (nWords.getD 4 [])

@[expose] noncomputable def gQ (i : Fin 14) : D :=
  if i.val < 7 then zeD ^ i.val * y1D * (zeD ^ i.val)⁻¹
  else zeD ^ (i.val - 7) * y2D * (zeD ^ (i.val - 7))⁻¹

@[expose] noncomputable def Q2 : Subgroup D := Subgroup.closure (Set.range gQ)

@[expose] noncomputable def Kc : Subgroup D := Subgroup.closure {zeD, r0D, s0D}

@[expose] noncomputable def cj (i : ℕ) (u : D) : D := zeD ^ i * u * (zeD ^ i)⁻¹

@[expose] noncomputable def phi (u v : D) (i : Fin 14) : D :=
  if i.val < 7 then cj i.val u else cj (i.val - 7) v

@[expose] def relVal {G : Type*} [Group G] (f : Fin 14 → G) (r : List (Fin 14 × Bool)) : G :=
  (r.map fun p => if p.2 then f p.1 else (f p.1)⁻¹).prod

theorem gQ_eq_phi : gQ = phi y1D y2D := by
  funext i
  rfl

theorem phi_lt {u v : D} {i : Fin 14} (h : i.val < 7) : phi u v i = cj i.val u := by
  simp [phi, h]

theorem phi_ge {u v : D} {i : Fin 14} (h : ¬ i.val < 7) : phi u v i = cj (i.val - 7) v := by
  simp [phi, h]

theorem cj_one (i : ℕ) : cj i 1 = 1 := by simp [cj]

theorem phi_inv (u v : D) (i : Fin 14) : (phi u v i)⁻¹ = phi u⁻¹ v⁻¹ i := by
  unfold phi cj
  split_ifs <;> simp [mul_inv_rev, mul_assoc]

theorem cj_succ (i : ℕ) (u : D) : zeD * cj i u * zeD⁻¹ = cj (i + 1) u := by
  unfold cj
  group

theorem relVal_map {G G' : Type*} [Group G] [Group G'] (φ : G →* G') (f : Fin 14 → G)
    (r : List (Fin 14 × Bool)) : φ (relVal f r) = relVal (fun j => φ (f j)) r := by
  unfold relVal
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  split_ifs <;> simp [map_inv]

theorem nWords_lt_nat {i : ℕ} (hi : i < 5) : ∀ k ∈ nWords.getD i [], k < 8 := by
  interval_cases i <;> decide

theorem gd_y1 : Gd y1A y1D := gd_word (nWords_lt_nat (by norm_num))

theorem gd_y2 : Gd y2A y2D := gd_word (nWords_lt_nat (by norm_num))

theorem gd_z : Gd zA zeD := gd_word (nWords_lt_nat (by norm_num))

theorem gd_r0 : Gd r0A r0D := gd_word (nWords_lt_nat (by norm_num))

theorem gd_s0 : Gd s0A s0D := gd_word (nWords_lt_nat (by norm_num))

theorem zpow_inv_eq (hz : zeD ^ 7 = 1) {i : ℕ} (hi : i ≤ 7) : (zeD ^ i)⁻¹ = zeD ^ (7 - i) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, Nat.add_sub_cancel' hi, hz]

theorem cj_mod (hz : zeD ^ 7 = 1) (i : ℕ) (u : D) : cj i u = cj (i % 7) u := by
  have h : zeD ^ i = zeD ^ (i % 7) := by
    conv_lhs => rw [← Nat.div_add_mod i 7, pow_add, pow_mul, hz, one_pow, one_mul]
  unfold cj
  rw [h]

theorem gd_zPowA {i : ℕ} (hi : i < 8) : Gd zPowA[i]! (zeD ^ i) := by
  have : zPowA[i]! = powRows 24 zA i := by
    rw [getElem!_pos zPowA i (by simp [zPowA, hi])]
    simp [zPowA]
  rw [this]
  exact gd_z.pow i

theorem gd_cjA (hz : zeD ^ 7 = 1) {i : ℕ} (hi : i < 7) {x : Array ℕ} {u : D} (hx : Gd x u) :
    Gd (cjA i x) (cj i u) := by
  have h1 := gd_zPowA (i := i) (by omega)
  have h2 := gd_zPowA (i := 7 - i) (by omega)
  have := (h1.mul hx).mul h2
  rw [← zpow_inv_eq hz (by omega)] at this
  exact this

theorem phiArr_getElem (u v : Array ℕ) {i : ℕ} (hi : i < 14) :
    (phiArr u v)[i]! = if i < 7 then cjA i u else cjA (i - 7) v := by
  rw [getElem!_pos (phiArr u v) i (by simp [phiArr, hi])]
  simp [phiArr]

theorem gd_phiArr (hz : zeD ^ 7 = 1) {U V : Array ℕ} {u v : D} (hU : Gd U u) (hV : Gd V v)
    (i : Fin 14) : Gd (phiArr U V)[i.val]! (phi u v i) := by
  have hi := i.isLt
  rw [phiArr_getElem U V hi]
  unfold phi
  split_ifs with h
  · exact gd_cjA hz h hU
  · exact gd_cjA hz (by omega) hV

theorem gd_phiArr_inv (hz : zeD ^ 7 = 1) {U V : Array ℕ} {u v : D} (hU : Gd U u⁻¹)
    (hV : Gd V v⁻¹) (i : Fin 14) : Gd (phiArr U V)[i.val]! (phi u v i)⁻¹ := by
  rw [phi_inv]
  exact gd_phiArr hz hU hV i

theorem gd_relValR {f : Fin 14 → D} {F Fi : Array (Array ℕ)}
    (hF : ∀ i : Fin 14, Gd F[i.val]! (f i)) (hFi : ∀ i : Fin 14, Gd Fi[i.val]! (f i)⁻¹)
    (r : List (Fin 14 × Bool)) : Gd (relValR F Fi r) (relVal f r) := by
  induction r with
  | nil => simpa [relValR, relVal] using gd_one
  | cons p r ih =>
    have e : relVal f (p :: r) = (if p.2 then f p.1 else (f p.1)⁻¹) * relVal f r := by
      simp [relVal]
    rw [e]
    show Gd (mulR (if p.2 then F[p.1.val]! else Fi[p.1.val]!) (relValR F Fi r)) _
    refine Gd.mul ?_ ih
    by_cases hp : p.2
    · simpa [hp] using hF p.1
    · simpa [hp] using hFi p.1

theorem relsOK_of {f : Fin 14 → D} {F Fi : Array (Array ℕ)}
    (hF : ∀ i : Fin 14, Gd F[i.val]! (f i)) (hFi : ∀ i : Fin 14, Gd Fi[i.val]! (f i)⁻¹)
    {rels : List (List (Fin 14 × Bool))} (h : ∀ r ∈ rels, relVal f r = 1) :
    relsOK F Fi rels = true := by
  unfold relsOK
  rw [List.all_eq_true]
  intro r hr
  rw [beq_iff_eq]
  exact (Gd.eq_iff (gd_relValR hF hFi r) gd_one).2 (h r hr)

theorem rel_of_relsOK {f : Fin 14 → D} {F Fi : Array (Array ℕ)}
    (hF : ∀ i : Fin 14, Gd F[i.val]! (f i)) (hFi : ∀ i : Fin 14, Gd Fi[i.val]! (f i)⁻¹)
    {rels : List (List (Fin 14 × Bool))} (h : relsOK F Fi rels = true) :
    ∀ r ∈ rels, relVal f r = 1 := by
  unfold relsOK at h
  rw [List.all_eq_true] at h
  intro r hr
  have := h r hr
  rw [beq_iff_eq] at this
  exact (Gd.eq_iff (gd_relValR hF hFi r) gd_one).1 this

theorem forall_mem_of_getElem {α : Type*} [Inhabited α] {a : Array α} {P : α → Prop}
    (h : ∀ i < a.size, P a[i]!) : ∀ x ∈ a, P x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  have := h i hi
  rwa [getElem!_pos a i hi] at this

theorem gd_one_inv : Gd oneR ((1 : D)⁻¹) := by simpa using gd_one

theorem gQ_lt {i : Fin 14} (h : i.val < 7) : gQ i = cj i.val y1D := by
  simp [gQ, cj, h]

theorem gQ_ge {i : Fin 14} (h : ¬ i.val < 7) : gQ i = cj (i.val - 7) y2D := by
  simp [gQ, cj, h]

theorem gQ_mem (i : Fin 14) : gQ i ∈ Q2 := Subgroup.subset_closure ⟨i, rfl⟩

theorem y1D_mem : y1D ∈ Q2 := by
  have : gQ 0 = y1D := by simp [gQ]
  exact this ▸ gQ_mem 0

theorem y2D_mem : y2D ∈ Q2 := by
  have : gQ 7 = y2D := by simp [gQ]
  exact this ▸ gQ_mem 7

theorem cj_mem (hz : zeD ^ 7 = 1) (i : ℕ) : cj i y1D ∈ Q2 ∧ cj i y2D ∈ Q2 := by
  rw [cj_mod hz i y1D, cj_mod hz i y2D]
  have hi : i % 7 < 7 := Nat.mod_lt _ (by norm_num)
  refine ⟨?_, ?_⟩
  · have := gQ_mem ⟨i % 7, by omega⟩
    rwa [gQ_lt hi] at this
  · have := gQ_mem ⟨7 + i % 7, by omega⟩
    rwa [gQ_ge (by simp), show 7 + i % 7 - 7 = i % 7 by omega] at this

theorem conj_mem_Q2_of (hz : zeD ^ 7 = 1) {q : D} (hq : q ∈ Q2) : zeD * q * zeD⁻¹ ∈ Q2 := by
  have key : Q2 ≤ Q2.comap (MulAut.conj zeD).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, rfl⟩
    show zeD * gQ j * zeD⁻¹ ∈ Q2
    by_cases h : j.val < 7
    · rw [gQ_lt h, cj_succ]
      exact (cj_mem hz _).1
    · rw [gQ_ge h, cj_succ]
      exact (cj_mem hz _).2
  exact key hq

section Cert

theorem cert_y1inv : mulR y1A y1iA = oneR := by
  obtain ⟨h, -⟩ := Certificates.certificate300206
  simpa using h

theorem cert_y2sq : mulR y2A y2A = oneR := by
  obtain ⟨-, h, -⟩ := Certificates.certificate300206
  simpa using h

theorem cert_z7 : powRows 24 zA 7 = oneR := by
  obtain ⟨-, -, h, -⟩ := Certificates.certificate300206
  simpa using h

theorem cert_y1sq : ¬ mulR y1A y1A = oneR := by
  obtain ⟨-, -, -, h, -⟩ := Certificates.certificate300206
  simpa using h

theorem cert_rel1 : relsOK (phiArr y1A oneR) (phiArr y1iA oneR) qR1 = true := by
  obtain ⟨-, -, -, -, h, -⟩ := Certificates.certificate300206
  exact h

theorem cert_rel2 : relsOK (phiArr oneR y2A) (phiArr oneR y2A) qR2 = true := by
  obtain ⟨-, -, -, -, -, h, -⟩ := Certificates.certificate300206
  exact h

theorem cert_rel12 : relsOK qGensA qGensInvA qR12 = true := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := Certificates.certificate300206
  exact h

theorem cert_tabQ : tabOK qGensA qGensInvA tabQ2 2048 = true := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := Certificates.certificate300206
  exact h

theorem cert_tabK : tabOK kGens kGensInv tabKc 42 = true := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate300206
  exact h

theorem cert_invQ : invOKT tQ = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate300206
  exact h

theorem cert_pair : pairCheck tQ tK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate300206
  exact h

theorem cert_comm : commCheck tK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate300206
  exact h

theorem cert_cube : cubeCheck tK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h⟩ := Certificates.certificate300206
  exact h

theorem zeD_pow_seven : zeD ^ 7 = 1 := by
  have g := gd_z.pow 7
  rw [cert_z7] at g
  exact (Gd.eq_iff g gd_one).1 rfl

theorem gd_y1i : Gd y1iA y1D⁻¹ := gd_y1.inv_of_mul (validR_powRows gd_y1.2 3) cert_y1inv

theorem gd_y2i : Gd y2A y2D⁻¹ := gd_y2.inv_of_mul gd_y2.2 cert_y2sq

theorem zeD_conj_mem {q : D} (hq : q ∈ Q2) : zeD * q * zeD⁻¹ ∈ Q2 :=
  conj_mem_Q2_of zeD_pow_seven hq

theorem gd_qGens (i : Fin 14) : Gd qGensA[i.val]! (gQ i) := by
  rw [gQ_eq_phi]
  exact gd_phiArr zeD_pow_seven gd_y1 gd_y2 i

theorem qGens_good : ∀ x ∈ qGensA, ∃ σ ∈ Q2, Gd x σ := by
  refine forall_mem_of_getElem fun i hi => ?_
  have hi' : i < 14 := by simpa [qGensA, phiArr] using hi
  exact ⟨gQ ⟨i, hi'⟩, gQ_mem _, gd_qGens ⟨i, hi'⟩⟩

theorem tQ_good : ∀ x ∈ tQ, ∃ σ ∈ Q2, Gd x σ := good_buildTabR qGens_good tabQ2

theorem tabQ_on : tabOKOn qGensA qGensInvA tQ (lookup (mkIdx tQ)) 2048 = true := cert_tabQ

theorem tQ_complete_rep : ∀ τ ∈ Q2, ∃ x ∈ tQ, RepE d4E x τ := by
  refine tab_complete_R (gi := qGensInvA) (idx := lookup (mkIdx tQ)) (N := 2048) ?_
    (oneR_mem_buildTabR _ _) tabQ_on
  rintro _ ⟨j, rfl⟩
  exact ⟨j.val, by simp [qGensA, phiArr], (gd_qGens j).1⟩

theorem tQ_complete {q : D} (hq : q ∈ Q2) : ∃ x ∈ tQ, Gd x q := by
  obtain ⟨x, hx, rx⟩ := tQ_complete_rep q hq
  obtain ⟨σ, -, hσ⟩ := tQ_good x hx
  exact ⟨x, hx, rx, hσ.2⟩

theorem card_Q2 : Nat.card Q2 = 2048 := by
  obtain ⟨hsize, hidx, -, -⟩ := tabOKOn_parts tabQ_on
  rw [card_eq_of_tab tQ_good hidx tQ_complete_rep, hsize]

theorem kGens_good : ∀ x ∈ kGens, ∃ σ ∈ Kc, Gd x σ := by
  refine forall_mem_of_getElem fun i hi => ?_
  have hi' : i < 3 := by simpa [kGens] using hi
  interval_cases i
  · exact ⟨zeD, Subgroup.subset_closure (by simp), gd_z⟩
  · exact ⟨r0D, Subgroup.subset_closure (by simp), gd_r0⟩
  · exact ⟨s0D, Subgroup.subset_closure (by simp), gd_s0⟩

theorem tK_good : ∀ x ∈ tK, ∃ σ ∈ Kc, Gd x σ := good_buildTabR kGens_good tabKc

theorem tabK_on : tabOKOn kGens kGensInv tK (lookup (mkIdx tK)) 42 = true := cert_tabK

theorem tK_complete_rep : ∀ τ ∈ Kc, ∃ x ∈ tK, RepE d4E x τ := by
  refine tab_complete_R (gi := kGensInv) (idx := lookup (mkIdx tK)) (N := 42) ?_
    (oneR_mem_buildTabR _ _) tabK_on
  intro σ hσ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  rcases hσ with rfl | rfl | rfl
  · exact ⟨0, by simp [kGens], gd_z.1⟩
  · exact ⟨1, by simp [kGens], gd_r0.1⟩
  · exact ⟨2, by simp [kGens], gd_s0.1⟩

theorem tK_complete {k : D} (hk : k ∈ Kc) : ∃ x ∈ tK, Gd x k := by
  obtain ⟨x, hx, rx⟩ := tK_complete_rep k hk
  obtain ⟨σ, -, hσ⟩ := tK_good x hx
  exact ⟨x, hx, rx, hσ.2⟩

theorem Kc_comm_zeD {k : D} (hk : k ∈ Kc) : k * zeD = zeD * k := by
  obtain ⟨x, hx, hxk⟩ := tK_complete hk
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hx
  have h := cert_comm
  unfold commCheck at h
  have := allLt_spec h hj
  rw [getElem!_pos tK j hj, beq_iff_eq] at this
  exact (Gd.eq_iff (hxk.mul gd_z) (gd_z.mul hxk)).1 this

theorem gd_s0i : Gd s0iA s0D⁻¹ := by
  obtain ⟨-, -, hinv, -⟩ := tabOKOn_parts tabK_on
  have h := hinv 2 (by simp [kGens])
  have h' : mulR s0A s0iA = oneR := by simpa [kGens, kGensInv] using h
  exact gd_s0.inv_of_mul (gd_s0.mul gd_s0).2 h'

theorem Kc_eq_s0D_of_cube {k : D} (hk : k ∈ Kc) (h3 : k * k * k = 1) (h1 : k ≠ 1) :
    k = s0D ∨ k = s0D⁻¹ := by
  obtain ⟨x, hx, hxk⟩ := tK_complete hk
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hx
  have hcube : mulR (mulR tK[j] tK[j]) tK[j] = oneR :=
    (Gd.eq_iff ((hxk.mul hxk).mul hxk) gd_one).2 h3
  have h := cert_cube
  unfold cubeCheck at h
  have := allLt_spec h hj
  rw [getElem!_pos tK j hj] at this
  simp only [hcube, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    beq_iff_eq] at this
  rcases this with (this | this) | this
  · exact absurd ((Gd.eq_iff hxk gd_one).1 this) h1
  · exact Or.inl ((Gd.eq_iff hxk gd_s0).1 this)
  · exact Or.inr ((Gd.eq_iff hxk gd_s0i).1 this)

theorem invOKT_mem {T : Array (Array ℕ)} (h : invOKT T = true) {x : Array ℕ} (hx : x ∈ T) :
    validR (invPow x) = true ∧ mulR x (invPow x) = oneR := by
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
  unfold invOKT at h
  have h1 := allLt_spec h hk
  rw [getElem!_pos T k hk] at h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact h1

theorem inv_of_mem_tQ {x : Array ℕ} (hx : x ∈ tQ) :
    validR (invPow x) = true ∧ mulR x (invPow x) = oneR :=
  invOKT_mem cert_invQ hx

theorem rel_transfer (α : ↥Q2 ≃* ↥Q2) (f : Fin 14 → ↥Q2) (g0 g1 : Fin 14 → D)
    (h0 : ∀ j, (f j : D) = g0 j) (h1 : ∀ j, (α (f j) : D) = g1 j) (r : List (Fin 14 × Bool))
    (h : relVal g0 r = 1) : relVal g1 r = 1 := by
  have e0 : relVal f r = 1 := by
    apply Subtype.ext
    have := relVal_map Q2.subtype f r
    simp only [Subgroup.subtype_apply] at this
    rw [this]
    simpa [h0] using h
  have e1 : relVal (fun j => α (f j)) r = 1 := by
    have := relVal_map α.toMonoidHom f r
    rw [e0, map_one] at this
    exact this.symm
  have e2 := relVal_map Q2.subtype (fun j => α (f j)) r
  simp only [Subgroup.subtype_apply] at e2
  rw [e1] at e2
  have e3 : relVal (fun j => (α (f j) : D)) r = 1 := by
    rw [← e2]
    rfl
  have e4 : g1 = fun j => (α (f j) : D) := funext fun j => (h1 j).symm
  rw [e4]
  exact e3

theorem cj_conj {κ : D} (hc : κ * zeD = zeD * κ) (i : ℕ) (u : D) :
    cj i (κ * u * κ⁻¹) = κ * cj i u * κ⁻¹ := by
  have h1 : zeD ^ i * κ = κ * zeD ^ i := ((Commute.pow_right hc i).eq).symm
  have h2 : κ⁻¹ * (zeD ^ i)⁻¹ = (zeD ^ i)⁻¹ * κ⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, h1]
  unfold cj
  calc zeD ^ i * (κ * u * κ⁻¹) * (zeD ^ i)⁻¹
      = (zeD ^ i * κ) * u * (κ⁻¹ * (zeD ^ i)⁻¹) := by simp only [mul_assoc]
    _ = (κ * zeD ^ i) * u * ((zeD ^ i)⁻¹ * κ⁻¹) := by rw [h1, h2]
    _ = κ * (zeD ^ i * u * (zeD ^ i)⁻¹) * κ⁻¹ := by simp only [mul_assoc]

theorem phi_conj {κ : D} (hc : κ * zeD = zeD * κ) (u v : D) (j : Fin 14) :
    phi (κ * u * κ⁻¹) (κ * v * κ⁻¹) j = κ * phi u v j * κ⁻¹ := by
  unfold phi
  split_ifs
  · exact cj_conj hc _ _
  · exact cj_conj hc _ _

theorem rel1_gens : ∀ r ∈ qR1, relVal (phi y1D 1) r = 1 :=
  rel_of_relsOK (F := phiArr y1A oneR) (Fi := phiArr y1iA oneR)
    (gd_phiArr zeD_pow_seven gd_y1 gd_one)
    (gd_phiArr_inv zeD_pow_seven gd_y1i gd_one_inv) cert_rel1

theorem rel2_gens : ∀ r ∈ qR2, relVal (phi 1 y2D) r = 1 :=
  rel_of_relsOK (F := phiArr oneR y2A) (Fi := phiArr oneR y2A)
    (gd_phiArr zeD_pow_seven gd_one gd_y2)
    (gd_phiArr_inv zeD_pow_seven gd_one_inv gd_y2i) cert_rel2

theorem rel12_gens : ∀ r ∈ qR12, relVal (phi y1D y2D) r = 1 :=
  rel_of_relsOK (F := qGensA) (Fi := qGensInvA)
    (gd_phiArr zeD_pow_seven gd_y1 gd_y2)
    (gd_phiArr_inv zeD_pow_seven gd_y1i gd_y2i) cert_rel12

theorem aut_cj (α : ↥Q2 ≃* ↥Q2)
    (hα : ∀ (q : D) (hq : q ∈ Q2),
      (α ⟨zeD * q * zeD⁻¹, zeD_conj_mem hq⟩ : D) = zeD * (α ⟨q, hq⟩ : D) * zeD⁻¹)
    (i : ℕ) (q : ↥Q2) :
    ∃ q' : ↥Q2, (q' : D) = zeD ^ i * q * (zeD ^ i)⁻¹ ∧
      (α q' : D) = zeD ^ i * (α q : D) * (zeD ^ i)⁻¹ := by
  induction i with
  | zero => exact ⟨q, by simp, by simp⟩
  | succ i ih =>
    obtain ⟨q', h1, h2⟩ := ih
    refine ⟨⟨zeD * q' * zeD⁻¹, zeD_conj_mem q'.2⟩, ?_, ?_⟩
    · show zeD * (q' : D) * zeD⁻¹ = _
      rw [h1]
      group
    · have := hα (q' : D) q'.2
      show (α ⟨zeD * (q' : D) * zeD⁻¹, _⟩ : D) = _
      rw [this]
      show zeD * (α q' : D) * zeD⁻¹ = _
      rw [h2]
      group

theorem exists_Kc_of_aut (α : ↥Q2 ≃* ↥Q2)
    (hα : ∀ (q : D) (hq : q ∈ Q2),
      (α ⟨zeD * q * zeD⁻¹, zeD_conj_mem hq⟩ : D) = zeD * (α ⟨q, hq⟩ : D) * zeD⁻¹) :
    ∃ k ∈ Kc, ∀ (q : D) (hq : q ∈ Q2), (α ⟨q, hq⟩ : D) = k * q * k⁻¹ := by
  have hz := zeD_pow_seven
  let y1' : ↥Q2 := ⟨y1D, y1D_mem⟩
  let y2' : ↥Q2 := ⟨y2D, y2D_mem⟩
  obtain ⟨a, ha⟩ : ∃ a : D, (α y1' : D) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : D, (α y2' : D) = b := ⟨_, rfl⟩
  have haQ : a ∈ Q2 := ha ▸ (α y1').2
  have hbQ : b ∈ Q2 := hb ▸ (α y2').2
  let g' : Fin 14 → ↥Q2 := fun j => ⟨gQ j, gQ_mem j⟩
  have hαg : ∀ j : Fin 14, (α (g' j) : D) = phi a b j := by
    intro j
    by_cases h : j.val < 7
    · obtain ⟨q', h1, h2⟩ := aut_cj α hα j.val y1'
      have : q' = g' j := Subtype.ext (h1.trans (gQ_lt h).symm)
      rw [← this, h2, phi_lt h, ha]
      rfl
    · obtain ⟨q', h1, h2⟩ := aut_cj α hα (j.val - 7) y2'
      have : q' = g' j := Subtype.ext (h1.trans (gQ_ge h).symm)
      rw [← this, h2, phi_ge h, hb]
      rfl
  have hrel1 : ∀ r ∈ qR1, relVal (phi a 1) r = 1 := by
    intro r hr
    refine rel_transfer α (fun j => if j.val < 7 then g' j else 1) (phi y1D 1) (phi a 1) ?_ ?_ r
      (rel1_gens r hr)
    · intro j
      by_cases h : j.val < 7
      · simp only [h, ↓reduceIte]
        rw [phi_lt h]
        exact gQ_lt h
      · simp only [h, ↓reduceIte]
        rw [phi_ge h, cj_one]
        rfl
    · intro j
      by_cases h : j.val < 7
      · simp only [h, ↓reduceIte]
        rw [hαg j, phi_lt h, phi_lt h]
      · simp only [h, ↓reduceIte]
        rw [map_one, phi_ge h, cj_one]
        rfl
  have hrel2 : ∀ r ∈ qR2, relVal (phi 1 b) r = 1 := by
    intro r hr
    refine rel_transfer α (fun j => if j.val < 7 then 1 else g' j) (phi 1 y2D) (phi 1 b) ?_ ?_ r
      (rel2_gens r hr)
    · intro j
      by_cases h : j.val < 7
      · simp only [h, ↓reduceIte]
        rw [phi_lt h, cj_one]
        rfl
      · simp only [h, ↓reduceIte]
        rw [phi_ge h]
        exact gQ_ge h
    · intro j
      by_cases h : j.val < 7
      · simp only [h, ↓reduceIte]
        rw [map_one, phi_lt h, cj_one]
        rfl
      · simp only [h, ↓reduceIte]
        rw [hαg j, phi_ge h, phi_ge h]
  have hrel12 : ∀ r ∈ qR12, relVal (phi a b) r = 1 := by
    intro r hr
    refine rel_transfer α g' (phi y1D y2D) (phi a b) (fun j => ?_) hαg r (rel12_gens r hr)
    exact congrFun gQ_eq_phi j
  obtain ⟨x, hx, hxa⟩ := tQ_complete haQ
  obtain ⟨y, hy, hyb⟩ := tQ_complete hbQ
  obtain ⟨hxv, hxm⟩ := inv_of_mem_tQ hx
  obtain ⟨hyv, hym⟩ := inv_of_mem_tQ hy
  have hxi : Gd (invPow x) a⁻¹ := hxa.inv_of_mul hxv hxm
  have hyi : Gd (invPow y) b⁻¹ := hyb.inv_of_mul hyv hym
  have hpr1 : pr1 x = true := by
    unfold pr1
    rw [Bool.and_eq_true]
    refine ⟨?_, relsOK_of (gd_phiArr hz hxa gd_one) (gd_phiArr_inv hz hxi gd_one_inv) hrel1⟩
    have hna : ¬ mulR x x = oneR := by
      intro hxx
      have haa : a * a = 1 := (Gd.eq_iff (hxa.mul hxa) gd_one).1 hxx
      have h1 : (y1' * y1' : ↥Q2) = 1 := by
        apply α.injective
        rw [map_mul, map_one]
        apply Subtype.ext
        show (α y1' : D) * (α y1' : D) = 1
        rw [ha]
        exact haa
      have h2 : y1D * y1D = 1 := congrArg Subtype.val h1
      exact cert_y1sq ((Gd.eq_iff (gd_y1.mul gd_y1) gd_one).2 h2)
    simpa using hna
  have hpr2 : pr2 y = true :=
    relsOK_of (gd_phiArr hz gd_one hyb) (gd_phiArr_inv hz gd_one_inv hyi) hrel2
  have h12 : relsOK (phiArr x y) (phiArr (invPow x) (invPow y)) qR12 = true :=
    relsOK_of (gd_phiArr hz hxa hyb) (gd_phiArr_inv hz hxi hyi) hrel12
  have hP : pairOK tK x y = true := by
    have h := cert_pair
    simp only [pairCheck, Array.all_eq_true', Array.mem_filter, and_imp] at h
    exact h x hx hpr1 y hy hpr2
  unfold pairOK at hP
  rw [h12, Bool.not_true, Bool.false_or, Array.any_eq_true'] at hP
  obtain ⟨k, hk, hkp⟩ := hP
  simp only [Bool.and_eq_true, beq_iff_eq] at hkp
  obtain ⟨κ, hκ, hgk⟩ := tK_good k hk
  have hak : a * κ = κ * y1D := (Gd.eq_iff (hxa.mul hgk) (hgk.mul gd_y1)).1 hkp.1
  have hbk : b * κ = κ * y2D := (Gd.eq_iff (hyb.mul hgk) (hgk.mul gd_y2)).1 hkp.2
  have hay : a = κ * y1D * κ⁻¹ := (mul_inv_eq_iff_eq_mul.2 hak.symm).symm
  have hby : b = κ * y2D * κ⁻¹ := (mul_inv_eq_iff_eq_mul.2 hbk.symm).symm
  have hcomm := Kc_comm_zeD hκ
  refine ⟨κ, hκ, ?_⟩
  have key : ∀ (q : D) (hq : q ∈ Subgroup.closure (Set.range gQ)),
      (α ⟨q, hq⟩ : D) = κ * q * κ⁻¹ := by
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      refine (hαg j).trans ?_
      rw [hay, hby, phi_conj hcomm, gQ_eq_phi]
    | one =>
      show (α 1 : D) = κ * 1 * κ⁻¹
      rw [map_one]
      simp
    | mul x y hx hy ihx ihy =>
      show (α (⟨x, hx⟩ * ⟨y, hy⟩ : ↥Q2) : D) = κ * (x * y) * κ⁻¹
      rw [map_mul, Subgroup.coe_mul, ihx, ihy]
      group
    | inv x hx ih =>
      show (α (⟨x, hx⟩⁻¹ : ↥Q2) : D) = κ * x⁻¹ * κ⁻¹
      rw [map_inv, Subgroup.coe_inv, ih]
      group
  intro q hq
  exact key q hq

end Cert

end CFSG.Quasithin.Background.Harris.R1.D4Vert
