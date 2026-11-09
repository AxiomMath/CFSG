module

public import Certificates.Data.Kernel.PermCent.B0Lit
public import Certificates.Data.Kernel.PermCent.B0Twin
public import Certificates.Data.Kernel.PermCent.SetWalkC
public import Certificates.Data.Kernel.PermCent.SplitC

public section

set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.B0T

open CFSG.ComponentClassification.CatFactsSmall.PSp43 Certificates.OmegaB0 CFSG.KC.Enum

@[expose] def fB : Nat := 17924097

@[expose] def ptsB : List Nat := [0, 15, 16, 20, 24]

@[expose] def mskP : List Nat := [18813149085697, 18813149085697, 17924097, 17924097]

@[expose] def mskA : List Nat := [18813149085697, 18813149085697, 18813149085697, 17924097]

@[expose] noncomputable def act1C (bs Φ : List (CV 45)) (allV : List (Fin 5 → ZMod 2))
    (S5 : List (Equiv.Perm (Fin 5))) (n : CV 45) : Bool :=
  S5.any fun σ => matchIdx (conjIdxC bs n) σ && decide (Equiv.Perm.sign σ = 1) && actEqC Φ allV n σ

@[expose] noncomputable def act2C (bs Φ : List (CV 45)) (allV : List (Fin 5 → ZMod 2))
    (S5 : List (Equiv.Perm (Fin 5))) (n : CV 45) : Bool :=
  S5.any fun σ => matchIdx (conjIdxC bs n) σ && actEqC Φ allV n σ

@[expose] noncomputable def act3C (bs Φ : List (CV 45)) (allV : List (Fin 5 → ZMod 2))
    (n : CV 45) (σ : Equiv.Perm (Fin 5)) : Bool :=
  matchIdx (conjIdxC bs n) σ && actEqC Φ allV n σ

@[expose] noncomputable def bits3C (bs Φ Bl : List (CV 45)) (allV : List (Fin 5 → ZMod 2))
    (S5 : List (Equiv.Perm (Fin 5))) (n : CV 45) : Nat :=
  Bool.rec 0 (bitsF (act3C bs Φ allV n) S5 0) (normBC Bl n)

theorem actC_of (L0 A0 bs Φ Bl : List (CV 45)) (allV : List (Fin 5 → ZMod 2))
    (S5 : List (Equiv.Perm (Fin 5)))
    (h1 : (L0.filter (normBC Bl)).all (act1C bs Φ allV S5) = true)
    (h2 : (A0.filter (normBC Bl)).all (act2C bs Φ allV S5) = true)
    (h3 : S5.all (fun σ => !decide (Equiv.Perm.sign σ = 1) ||
      (L0.filter (normBC Bl)).any fun n => act3C bs Φ allV n σ) = true) :
    actC L0 A0 bs Φ Bl allV S5 = true := by
  change ((L0.filter (normBC Bl)).all (act1C bs Φ allV S5) &&
    (A0.filter (normBC Bl)).all (act2C bs Φ allV S5) &&
    S5.all (fun σ => !decide (Equiv.Perm.sign σ = 1) ||
      (L0.filter (normBC Bl)).any fun n => act3C bs Φ allV n σ)) = true
  rw [h1, h2, h3]
  rfl

theorem nrm_of_normBC {Bl : List (CV 45)} {g : CV 45} (h : normBC Bl g = true) :
    (Bl.all fun s => decide (g * s * g⁻¹ ∈ Bl)) = true := by
  unfold normBC at h
  refine List.all_eq_true.2 fun s hs => ?_
  have := List.all_eq_true.1 h s hs
  rw [Bool.and_eq_true] at this
  exact this.1

@[expose] def finB : List (Fin 45) := [0, 15, 16, 20, 24]

theorem finB_map : finB.map (fun f => ((ev (1 : CV 45))⁻¹ f : Nat)) = ptsB := by
  rw [ev_one, inv_one]
  rfl

theorem finB_in : ∀ f ∈ finB, inMS fB f = true := by decide

theorem filter_all_of_walk {Bl : List (CV 45)} (hf : fixS fB Bl Bl = true)
    (L : List (List (CV 45) × Nat)) (hm : masksS fB L = true) (body : CV 45 → Bool)
    (hw : walkS body L 1 ptsB = true) :
    ((productsC (L.map Prod.fst)).filter (normBC Bl)).all body = true := by
  refine List.all_eq_true.2 fun g hg => ?_
  rw [List.mem_filter] at hg
  have h := walkS_sound body fB finB L 1 ptsB hm hw finB_map.symm g hg.1 (fun f hf' => by
    rw [one_mul]
    exact good_of_nrmS hf g (nrm_of_normBC hg.2) f (finB_in f hf'))
  rwa [one_mul] at h

theorem cover_of_walk {bs Φ Bl : List (CV 45)} {allV : List (Fin 5 → ZMod 2)}
    {S5 : List (Equiv.Perm (Fin 5))} (L : List (List (CV 45) × Nat))
    (hc : strictB (walkF (bits3C bs Φ Bl allV S5) L 1 ptsB 0)
      (fun r => coverF (fun σ => decide (Equiv.Perm.sign σ = 1)) r S5 0) = true) :
    S5.all (fun σ => !decide (Equiv.Perm.sign σ = 1) ||
      ((productsC (L.map Prod.fst)).filter (normBC Bl)).any fun n => act3C bs Φ allV n σ) = true := by
  rw [strictB_eqS] at hc
  refine List.all_eq_true.2 fun σ hσ => ?_
  cases hs : decide (Equiv.Perm.sign σ = 1)
  · rfl
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hσ
    have hb := coverF_sound _ _ S5 0 hc i hi hs
    rw [Nat.zero_add] at hb
    rcases walkF_sound _ i L 1 ptsB 0 hb with h | ⟨u, hu, h⟩
    · rw [not_inMS_zero] at h
      cases h
    · rw [one_mul] at h
      have hn : normBC Bl u = true := by
        cases hn : normBC Bl u
        · unfold bits3C at h
          rw [hn] at h
          change inMS 0 i = true at h
          rw [not_inMS_zero] at h
          cases h
        · rfl
      unfold bits3C at h
      rw [hn] at h
      obtain ⟨i', hi', hl, hx⟩ := bitsF_sound _ S5 0 i h
      rw [Nat.zero_add] at hi'
      subst hi'
      rw [Bool.not_true, Bool.false_or, List.any_eq_true]
      exact ⟨u, List.mem_filter.2 ⟨hu, hn⟩, hx⟩

theorem lvNP_eq : (levelsC QP45).map (·.map Subtype.val) = lvNP := by decide +kernel

theorem lvNA_eq : (levelsC QA45).map (·.map Subtype.val) = lvNA := by decide +kernel

theorem canon_of_lv {Q : CFSG.Certificates.RawSchreierDatum 45} {N : List (List Nat)}
    (h : (levelsC Q).map (·.map Subtype.val) = N) : ∀ l ∈ N, ∀ k ∈ l, Canon 45 k := by
  intro l hl k hk
  rw [← h] at hl
  obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hk
  exact c.2

@[expose] noncomputable def mkCV (k : Nat) (h : Canon 45 k) : CV 45 := ⟨k, h⟩

@[expose] noncomputable def lvC (N : List (List Nat)) (hN : ∀ l ∈ N, ∀ k ∈ l, Canon 45 k) :
    List (List (CV 45)) :=
  N.pmap (P := fun l => ∀ k ∈ l, Canon 45 k) (fun l hl => l.pmap mkCV hl) hN

theorem lvC_val (N : List (List Nat)) (hN : ∀ l ∈ N, ∀ k ∈ l, Canon 45 k) :
    (lvC N hN).map (·.map Subtype.val) = N := by
  unfold lvC
  rw [List.map_pmap]
  conv_rhs => rw [← List.map_id N]
  rw [← List.pmap_eq_map (p := fun l => ∀ k ∈ l, Canon 45 k) (H := hN)]
  refine List.pmap_congr_left _ fun l _ h₁ h₂ => ?_
  rw [List.map_pmap]
  conv_rhs => rw [← List.map_id l]
  rw [← List.pmap_eq_map (p := Canon 45) (H := h₂)]
  rfl

theorem levelsC_eq_lvC {Q : CFSG.Certificates.RawSchreierDatum 45} {N : List (List Nat)}
    (h : (levelsC Q).map (·.map Subtype.val) = N) : levelsC Q = lvC N (canon_of_lv h) := by
  have hi : Function.Injective (List.map (List.map (Subtype.val : CV 45 → Nat))) :=
    List.map_injective_iff.2 (List.map_injective_iff.2 Subtype.val_injective)
  exact hi (h.trans (lvC_val N _).symm)

@[expose] noncomputable def lvCP : List (List (CV 45)) := lvC lvNP (canon_of_lv lvNP_eq)

@[expose] noncomputable def lvCA : List (List (CV 45)) := lvC lvNA (canon_of_lv lvNA_eq)

theorem levelsC_QP45 : levelsC QP45 = lvCP := levelsC_eq_lvC lvNP_eq

theorem levelsC_QA45 : levelsC QA45 = lvCA := levelsC_eq_lvC lvNA_eq

@[expose] noncomputable def conjIdxE (bs : List (CV 45)) (n : CV 45) : List ℕ :=
  bs.map fun b => bs.findIdx fun c => eq22C n b c n

theorem conjIdxE_eq (bs : List (CV 45)) (n : CV 45) : conjIdxE bs n = conjIdxC bs n := by
  unfold conjIdxE conjIdxC
  simp only [eq22C_eq, mul_inv_eq_iff_eq_mul]

@[expose] def entS (σ : Equiv.Perm (Fin 5)) : List Nat × Bool :=
  ((List.finRange 5).map fun j => (σ j : ℕ), decide (Equiv.Perm.sign σ = 1))

theorem s5T_eq : (s5l ()).map entS = s5T := by decide +kernel

theorem bsC_len : ((bl ()).map cOf).length = 5 := rfl

theorem bsC_comm : ∀ a ∈ (bl ()).map cOf, ∀ b ∈ (bl ()).map cOf, a * b = b * a := by
  decide +kernel

theorem vecOfNat_vcode : ∀ v : Fin 5 → ZMod 2, vecOfNat (vcode v) = v := by decide +kernel

theorem vcode_lt (v : Fin 5 → ZMod 2) : vcode v < 32 := by
  have h : ∀ i, (v i).val < 2 := fun i => ZMod.val_lt (v i)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  unfold vcode
  omega

theorem phi0C_eq (v : Fin 5 → ZMod 2) : phi0C phC v =
    ((List.finRange 5).map fun j =>
      if v j = 1 then ((bl ()).map cOf).getD (j : ℕ) 1 else 1).prod := by
  unfold phi0C phC phiC
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (vcode_lt v)]
  simp only [Option.map_some, Option.getD_some, vecOfNat_vcode]

theorem conj_of_match {n : CV 45} {σ : Equiv.Perm (Fin 5)}
    (h : matchIdx (conjIdxC ((bl ()).map cOf) n) σ = true) (j : Fin 5) :
    n * ((bl ()).map cOf).getD (j : ℕ) 1 * n⁻¹ = ((bl ()).map cOf).getD (σ j : ℕ) 1 := by
  unfold matchIdx at h
  have hj := of_decide_eq_true (List.all_eq_true.1 h j (List.mem_finRange j))
  have hjl : (j : ℕ) < ((bl ()).map cOf).length := by rw [bsC_len]; exact j.2
  have hsl : (σ j : ℕ) < ((bl ()).map cOf).length := by rw [bsC_len]; exact (σ j).2
  unfold conjIdxC at hj
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hjl), List.getElem_map] at hj
  rw [List.getD_eq_getElem _ _ hjl, List.getD_eq_getElem _ _ hsl]
  have hf : List.findIdx (fun c => decide (n * ((bl ()).map cOf)[(j : ℕ)] * n⁻¹ = c))
      ((bl ()).map cOf) < ((bl ()).map cOf).length := by rw [← hj]; exact hsl
  have hp := List.findIdx_getElem (w := hf)
  have e : ((bl ()).map cOf)[List.findIdx
      (fun c => decide (n * ((bl ()).map cOf)[(j : ℕ)] * n⁻¹ = c)) ((bl ()).map cOf)] =
      ((bl ()).map cOf)[(σ j : ℕ)] := by
    congr 1
    exact hj.symm
  rw [e] at hp
  exact of_decide_eq_true hp

theorem conj_phi0_of_match {n : CV 45} {σ : Equiv.Perm (Fin 5)}
    (h : matchIdx (conjIdxC ((bl ()).map cOf) n) σ = true) (v : Fin 5 → ZMod 2) :
    n * phi0C phC v * n⁻¹ = phi0C phC (v ∘ σ.symm) := by
  rw [phi0C_eq, phi0C_eq]
  have hc : n * (List.map (fun j => if v j = 1 then ((bl ()).map cOf).getD (j : ℕ) 1 else 1)
      (List.finRange 5)).prod * n⁻¹ = (List.map (MulAut.conj n)
      (List.map (fun j => if v j = 1 then ((bl ()).map cOf).getD (j : ℕ) 1 else 1)
        (List.finRange 5))).prod := by
    rw [← map_list_prod]
    rfl
  rw [hc, List.map_map]
  set g : Fin 5 → CV 45 := fun k => if v k = 1 then ((bl ()).map cOf).getD (σ k : ℕ) 1 else 1
    with hg
  have h1 : (MulAut.conj n) ∘ (fun j => if v j = 1 then ((bl ()).map cOf).getD (j : ℕ) 1 else 1) =
      g := by
    funext k
    simp only [Function.comp_apply, MulAut.conj_apply, hg]
    split
    · exact conj_of_match h k
    · rw [mul_one, mul_inv_cancel]
  have h2 : (fun j => if (v ∘ σ.symm) j = 1 then ((bl ()).map cOf).getD (j : ℕ) 1 else 1) =
      g ∘ σ.symm := by
    funext k
    simp only [Function.comp_apply, hg, Equiv.apply_symm_apply]
  rw [h1, h2, ← List.map_map]
  have hm : ∀ k, g k = 1 ∨ g k ∈ (bl ()).map cOf := by
    intro k
    simp only [hg]
    split
    · right
      have hsl : (σ k : ℕ) < ((bl ()).map cOf).length := by rw [bsC_len]; exact (σ k).2
      rw [List.getD_eq_getElem _ _ hsl]
      exact List.getElem_mem hsl
    · left
      rfl
  have hp : ((List.finRange 5).map g).Pairwise Commute := by
    refine List.pairwise_of_forall_mem_list fun a ha b hb => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hb
    rcases hm k with hk | hk
    · rw [hk]
      exact Commute.one_left _
    · rcases hm l with hl | hl
      · rw [hl]
        exact Commute.one_right _
      · exact bsC_comm _ hk _ hl
  exact (((Equiv.Perm.map_finRange_perm σ.symm).map g).symm.prod_eq' hp)

theorem actEqC_of_match {n : CV 45} {σ : Equiv.Perm (Fin 5)}
    (h : matchIdx (conjIdxC ((bl ()).map cOf) n) σ = true) :
    actEqC phC (allVecs ()) n σ = true :=
  List.all_eq_true.2 fun v _ => decide_eq_true (conj_phi0_of_match h v)

theorem mem_allVecsB (v : Fin 5 → ZMod 2) : v ∈ allVecs () := by
  have hl := vcode_lt v
  refine List.mem_map.2 ⟨(vcode v + 31) % 32, List.mem_range.2 (Nat.mod_lt _ (by omega)), ?_⟩
  have e : ((vcode v + 31) % 32 + 1) % 32 = vcode v := by omega
  rw [e, vecOfNat_vcode]

theorem mem_blC {v : Fin 5 → ZMod 2} (hv : ∑ i, v i = 0) : phi0C phC v ∈ blC :=
  List.mem_map.2 ⟨v, List.mem_filter.2 ⟨mem_allVecsB v, decide_eq_true hv⟩, rfl⟩

theorem normBC_of_match {n : CV 45} {σ : Equiv.Perm (Fin 5)}
    (h : matchIdx (conjIdxC ((bl ()).map cOf) n) σ = true) : normBC blC n = true := by
  unfold normBC
  refine List.all_eq_true.2 fun b hb => ?_
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hb
  have hs : ∑ i, v i = 0 := of_decide_eq_true (List.mem_filter.1 hv).2
  have e1 : n * phi0C phC (v ∘ σ) * n⁻¹ = phi0C phC v := by
    rw [conj_phi0_of_match h]
    congr 1
    funext i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  have e2 : n⁻¹ * phi0C phC v * n = phi0C phC (v ∘ σ) := by
    rw [← e1]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [Bool.and_eq_true, conj_phi0_of_match h, e2]
  exact ⟨decide_eq_true (mem_blC ((Equiv.sum_comp σ.symm v).trans hs)),
    decide_eq_true (mem_blC ((Equiv.sum_comp σ v).trans hs))⟩

theorem matchIdx_ent (σ : Equiv.Perm (Fin 5)) : matchIdx (entS σ).1 σ = true := by
  unfold matchIdx entS
  refine List.all_eq_true.2 fun j _ => ?_
  simp [List.getD_eq_getElem?_getD]

theorem match_of_ent (n : CV 45) (σ : Equiv.Perm (Fin 5))
    (h : ((entS σ).1 == conjIdxE ((bl ()).map cOf) n) = true) :
    matchIdx (conjIdxC ((bl ()).map cOf) n) σ = true := by
  rw [beq_iff_eq] at h
  rw [← conjIdxE_eq, ← h, matchIdx_ent]

theorem act3T_sound (n : CV 45) (σ : Equiv.Perm (Fin 5))
    (h : ((entS σ).1 == conjIdxE ((bl ()).map cOf) n) = true) :
    act3C ((bl ()).map cOf) phC (allVecs ()) n σ = true := by
  have hm := match_of_ent n σ h
  unfold act3C
  rw [hm, actEqC_of_match hm]
  rfl

@[expose] noncomputable def act1T (bs : List (CV 45)) (n : CV 45) : Bool :=
  s5T.any fun e => (e.1 == conjIdxE bs n) && e.2

@[expose] noncomputable def act2T (bs : List (CV 45)) (n : CV 45) : Bool :=
  s5T.any fun e => e.1 == conjIdxE bs n

theorem act1T_sound (n : CV 45) (h : act1T ((bl ()).map cOf) n = true) :
    act1C ((bl ()).map cOf) phC (allVecs ()) (s5l ()) n = true := by
  unfold act1T at h
  rw [← s5T_eq, List.any_map, List.any_eq_true] at h
  obtain ⟨σ, hσ, h⟩ := h
  rw [Function.comp_apply, Bool.and_eq_true] at h
  have h3 := act3T_sound n σ h.1
  unfold act3C at h3
  unfold act1C
  refine List.any_eq_true.2 ⟨σ, hσ, ?_⟩
  rw [Bool.and_eq_true] at h3
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨h3.1, h.2⟩, h3.2⟩

theorem act2T_sound (n : CV 45) (h : act2T ((bl ()).map cOf) n = true) :
    act2C ((bl ()).map cOf) phC (allVecs ()) (s5l ()) n = true := by
  unfold act2T at h
  rw [← s5T_eq, List.any_map, List.any_eq_true] at h
  obtain ⟨σ, hσ, h⟩ := h
  rw [Function.comp_apply] at h
  unfold act2C
  exact List.any_eq_true.2 ⟨σ, hσ, act3T_sound n σ h⟩

@[expose] def permB5 (c : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun r => r.isEmpty)
    (fun x _ ih r => r.contains x && ih (r.erase x)) c

theorem permB5_perm : ∀ (c r : List Nat), permB5 c r = true → c.Perm r
  | [], r, h => by
    change r.isEmpty = true at h
    rw [List.isEmpty_iff] at h
    rw [h]
  | x :: t, r, h => by
    change (r.contains x && permB5 t (r.erase x)) = true at h
    rw [Bool.and_eq_true] at h
    have hx : x ∈ r := by simpa using h.1
    exact ((permB5_perm t _ h.2).cons x).trans (List.perm_cons_erase hx).symm

theorem perm5_any : ∀ a b c d e : Fin 5,
    permB5 [(a : ℕ), b, c, d, e] [0, 1, 2, 3, 4] = true →
      (s5T.any fun x => x.1 == [(a : ℕ), b, c, d, e]) = true := by
  decide +kernel

@[expose] noncomputable def act2Q (bs : List (CV 45)) (n : CV 45) : Bool :=
  permB5 (conjIdxE bs n) [0, 1, 2, 3, 4]

theorem act2T_of_act2Q (bs : List (CV 45)) (n : CV 45) (h : act2Q bs n = true) :
    act2T bs n = true := by
  unfold act2Q at h
  unfold act2T
  have hp := permB5_perm _ _ h
  generalize conjIdxE bs n = c at hp h ⊢
  have hl : c.length = 5 := hp.length_eq
  have hm : ∀ x ∈ c, x < 5 := fun x hx => by
    have h' := hp.subset hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    omega
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨c', _ | ⟨d, _ | ⟨e, _ | ⟨f, t⟩⟩⟩⟩⟩⟩
  all_goals try (simp only [List.length_cons, List.length_nil] at hl; omega)
  exact perm5_any ⟨a, hm a (by simp)⟩ ⟨b, hm b (by simp)⟩ ⟨c', hm c' (by simp)⟩
    ⟨d, hm d (by simp)⟩ ⟨e, hm e (by simp)⟩ h

@[expose] noncomputable def bits3T (bs : List (CV 45)) (n : CV 45) : Nat :=
  bitsF (fun e => e.1 == conjIdxE bs n) s5T 0

theorem cover_of_walkT (L : List (List (CV 45) × Nat))
    (hc : strictB (walkF (bits3T ((bl ()).map cOf)) L 1 ptsB 0)
      (fun r => coverF (fun σ => decide (Equiv.Perm.sign σ = 1)) r (s5l ()) 0) = true) :
    (s5l ()).all (fun σ => !decide (Equiv.Perm.sign σ = 1) ||
      ((productsC (L.map Prod.fst)).filter (normBC blC)).any fun n =>
        act3C ((bl ()).map cOf) phC (allVecs ()) n σ) = true := by
  rw [strictB_eqS] at hc
  refine List.all_eq_true.2 fun σ hσ => ?_
  cases hs : decide (Equiv.Perm.sign σ = 1)
  · rfl
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hσ
    have hb := coverF_sound _ _ (s5l ()) 0 hc i hi hs
    rw [Nat.zero_add] at hb
    rcases walkF_sound _ i L 1 ptsB 0 hb with h | ⟨u, hu, h⟩
    · rw [not_inMS_zero] at h
      cases h
    · rw [one_mul] at h
      unfold bits3T at h
      rw [← s5T_eq] at h
      obtain ⟨i', hi', hl, hx⟩ := bitsF_sound _ _ 0 i h
      rw [Nat.zero_add] at hi'
      subst hi'
      simp only [List.getElem_map] at hx
      rw [Bool.not_true, Bool.false_or, List.any_eq_true]
      exact ⟨u, List.mem_filter.2 ⟨hu, normBC_of_match (match_of_ent u _ hx)⟩, act3T_sound u _ hx⟩

end CFSG.Certificates.Kernel.PkCV.B0T

end
