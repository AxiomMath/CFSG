module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Rep
public meta import Mathlib.Algebra.Field.ZMod
public meta import CFSG.Quasithin.Background.JonesParshallWedge
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Inputs
public import Certificates.Certificate7053
public import Certificates.Certificate17000
public import Certificates.Certificate17022
public import Certificates.Certificate17026

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis
open scoped Matrix

theorem decodeV_xor (a b : ℕ) : decodeV (a ^^^ b) = decodeV a + decodeV b := by
  funext k
  simp only [decodeV, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit k <;> cases b.testBit k <;> decide

theorem decodeV_zero : decodeV 0 = 0 := by
  funext k
  simp [decodeV]

theorem decodeV_injective {a b : ℕ} (ha : a < 1024) (hb : b < 1024) (h : decodeV a = decodeV b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 10
  · have := congrFun h ⟨i, hi⟩
    simp only [decodeV] at this
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · have h2 : 1024 ≤ 2 ^ i := by
      calc 1024 = 2 ^ 10 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

@[expose] noncomputable def codeEquiv : Fin 1024 ≃ (Fin 10 → ZMod 2) :=
  Equiv.ofBijective (fun c => decodeV c) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨fun a b h => Fin.ext (decodeV_injective a.2 b.2 h), by simp⟩)

@[expose] def wordSL' (l : List ℕ) : G5 := (l.map trSL').prod

theorem l52_cols : ∀ t : Fin 25, ∀ l : Fin 10,
    (fun k => wedgeMat ((trSL' t : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l) =
      decodeV (l52Col.getD (10 * t + l) 0) :=
  Certificates.certificate7053.1

theorem decodeV_foldl (f : Fin 10 → ℕ) (P : Fin 10 → Bool) (L : List (Fin 10)) (a : ℕ) :
    decodeV (L.foldl (fun acc l => if P l then acc ^^^ f l else acc) a) =
      decodeV a + (L.map fun l => if P l then decodeV (f l) else 0).sum := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    split_ifs with h
    · rw [decodeV_xor, add_assoc]
    · rw [zero_add]

theorem wedgeRep_trSL' {t : ℕ} (ht : t < 25) (c : ℕ) :
    wedgeRep (trSL' t) (decodeV c) = decodeV (actC t c) := by
  rw [wedgeRep_apply', actC, decodeV_foldl, decodeV_zero, zero_add, ← Fin.sum_univ_def]
  funext k
  rw [Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro l _
  rw [congrFun (l52_cols ⟨t, ht⟩ l) k]
  change decodeV _ k * (if c.testBit l then 1 else 0) = (if c.testBit l then decodeV _ else 0) k
  by_cases h : c.testBit l <;> simp [h]

theorem wedgeRep_wordSL' {l : List ℕ} (hl : ∀ t ∈ l, t < 25) (c : ℕ)
    :
    wedgeRep (wordSL' l) (decodeV c) = decodeV (applyC l c) := by
  induction l with
  | nil =>
    change wedgeRep 1 (decodeV c) = decodeV c
    rw [map_one, Module.End.one_apply]
  | cons t l ih =>
    have h1 : wordSL' (t :: l) = trSL' t * wordSL' l := by simp [wordSL']
    rw [h1, map_mul, Module.End.mul_apply, ih (fun s hs => hl s (List.mem_cons_of_mem _ hs)),
      wedgeRep_trSL' (hl t List.mem_cons_self)]
    rfl

theorem l52_cert : ∀ c < 1024, c ≠ 0 →
    applyC (l52Words.getD c []) (l52BaseC (l52Cls.getD c false)) = c ∧
      ∀ t ∈ l52Words.getD c [], t < 25 :=
  Certificates.certificate7053.2.1

theorem l52_count_true :
    (Finset.univ.filter fun c : Fin 1024 => c.val ≠ 0 ∧ l52Cls.getD c false = true).card = 155 :=
  Certificates.certificate7053.2.2.1

theorem l52_count_false :
    (Finset.univ.filter fun c : Fin 1024 => c.val ≠ 0 ∧ l52Cls.getD c false = false).card =
      868 :=
  Certificates.certificate7053.2.2.2

@[expose] noncomputable def clsV (w : Fin 10 → ZMod 2) : Bool :=
  l52Cls.getD (codeEquiv.symm w) false

theorem decodeV_code (w : Fin 10 → ZMod 2) : decodeV (codeEquiv.symm w) = w :=
  codeEquiv.apply_symm_apply w

theorem code_ne_zero {w : Fin 10 → ZMod 2} : (codeEquiv.symm w).val ≠ 0 ↔ w ≠ 0 := by
  constructor
  · intro h hw
    apply h
    have : decodeV (codeEquiv.symm w) = decodeV 0 := by rw [decodeV_code, hw, decodeV_zero]
    exact decodeV_injective (codeEquiv.symm w).2 (by norm_num) this
  · intro hw h
    apply hw
    rw [← decodeV_code w, h, decodeV_zero]

theorem exists_wedgeRep_base {w : Fin 10 → ZMod 2} (hw : w ≠ 0) :
    ∃ g : G5, wedgeRep g (decodeV (l52BaseC (clsV w))) = w := by
  set c := codeEquiv.symm w with hc
  obtain ⟨h1, h2⟩ := l52_cert c c.2 (code_ne_zero.2 hw)
  refine ⟨wordSL' (l52Words.getD c []), ?_⟩
  rw [clsV, ← hc, wedgeRep_wordSL' h2, h1, hc, decodeV_code]

theorem exists_wedgeRep_eq {w w' : Fin 10 → ZMod 2} (hw : w ≠ 0)
    (hw' : w' ≠ 0)
    (h : clsV w = clsV w') : ∃ g : G5, wedgeRep g w = w' := by
  obtain ⟨g, hg⟩ := exists_wedgeRep_base hw
  obtain ⟨g', hg'⟩ := exists_wedgeRep_base hw'
  have key : wedgeRep g⁻¹ w = decodeV (l52BaseC (clsV w)) := by
    calc wedgeRep g⁻¹ w = wedgeRep g⁻¹ (wedgeRep g (decodeV (l52BaseC (clsV w)))) := by
          rw [hg]
      _ = decodeV (l52BaseC (clsV w)) := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  exact ⟨g' * g⁻¹, by rw [map_mul, Module.End.mul_apply, key, h, hg']⟩

theorem ncard_clsV (b : Bool) :
    ({w | w ≠ 0 ∧ clsV w = b} : Set (Fin 10 → ZMod 2)).ncard = if b then 155 else 868 := by
  have h1 : ({w | w ≠ 0 ∧ clsV w = b} : Set (Fin 10 → ZMod 2)) = codeEquiv.symm ⁻¹'
      ↑(Finset.univ.filter fun c : Fin 1024 => c.val ≠ 0 ∧ l52Cls.getD c false = b) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Finset.coe_filter, Finset.mem_univ,
      true_and, code_ne_zero, clsV]
  rw [h1, Set.ncard_preimage_of_injective_subset_range codeEquiv.symm.injective (by simp),
    Set.ncard_coe_finset]
  cases b
  · exact l52_count_false
  · exact l52_count_true

theorem orbitIn_trans {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {u v w : V}
    (huv : v ∈ orbitIn H u) (hvw : w ∈ orbitIn H v) : w ∈ orbitIn H u := by
  obtain ⟨h, hh, rfl⟩ := huv
  obtain ⟨h', hh', rfl⟩ := hvw
  exact ⟨h' * h, H.mul_mem hh' hh, rfl⟩

theorem bool_eq_of_ne {a b c : Bool} (h1 : b ≠ a) (h2 : c ≠ a) : b = c := by
  revert a b c
  decide

theorem orbitL52Ten :
    OrbitL52Ten := by
  intro V _ _ h2 hcard H ⟨φ⟩ hirr
  obtain ⟨e, γ, he1, he⟩ := exists_wedge_coords h2 hcard φ hirr
  have hne : ∀ {v : V}, v ≠ 1 → e v ≠ 0 := fun hv h => hv (e.injective (h.trans he1.symm))
  have hsame : ∀ v w : V, v ≠ 1 → w ≠ 1 → clsV (e v) = clsV (e w) → w ∈ orbitIn H v := by
    intro v w hv hw hvw
    obtain ⟨g, hg⟩ := exists_wedgeRep_eq (hne hv) (hne hw) hvw
    refine ⟨(γ.symm g : MulAut V), (γ.symm g).2, e.injective ?_⟩
    rw [he, MulEquiv.apply_symm_apply, hg]
  have hC : ∀ b : Bool, ({v | v ≠ 1 ∧ clsV (e v) = b} : Set V).ncard =
      if b then 155 else 868 := by
    intro b
    have h1 : ({v | v ≠ 1 ∧ clsV (e v) = b} : Set V) =
        e ⁻¹' {w | w ≠ 0 ∧ clsV w = b} := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · rintro ⟨hv, hb⟩
        exact ⟨hne hv, hb⟩
      · rintro ⟨hv, hb⟩
        exact ⟨fun h => hv (h ▸ he1), hb⟩
    rw [h1, Set.ncard_preimage_of_injective_subset_range e.injective (by simp), ncard_clsV]
  have h1023 : ∀ v : V, v ≠ 1 → orbitIn H v ≠ {x | x ≠ 1} := by
    intro v _ heq
    have h1 : Nat.card ↥(orbitIn H v) ∣ Nat.card ↥H := by
      rw [orbitIn_eq_orbit, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
      exact Subgroup.index_dvd_card _
    have h3 := ncard_ne_one (V := V)
    rw [hcard] at h3
    rw [heq, Nat.card_coe_set_eq, Nat.card_congr φ.toEquiv, card_G5,
      show ({x | x ≠ 1} : Set V).ncard = 1023 by omega] at h1
    norm_num at h1
  have horbit : ∀ v : V, v ≠ 1 →
      orbitIn H v = ({x | x ≠ 1 ∧ clsV (e x) = clsV (e v)} : Set V) := by
    intro v hv
    ext w
    constructor
    · intro hw
      refine ⟨ne_one_of_mem_orbitIn hv hw, ?_⟩
      by_contra hcw
      apply h1023 v hv
      ext x
      refine ⟨fun hx => ne_one_of_mem_orbitIn hv hx, fun hx => ?_⟩
      by_cases hxv : clsV (e x) = clsV (e v)
      · exact hsame v x hv hx hxv.symm
      · exact orbitIn_trans hw (hsame w x (ne_one_of_mem_orbitIn hv hw) hx
          (bool_eq_of_ne hcw hxv))
    · rintro ⟨hw, hwc⟩
      exact hsame v w hv hw hwc.symm
  refine ⟨fun v hv => ?_, fun v w hv hw hvw => ?_⟩
  · rw [horbit v hv, Nat.card_coe_set_eq, hC]
    cases clsV (e v) <;> simp
  · rw [horbit v hv, horbit w hw, Nat.card_coe_set_eq, Nat.card_coe_set_eq, hC, hC] at hvw
    have hcvw : clsV (e v) = clsV (e w) := by
      revert hvw
      cases clsV (e v) <;> cases clsV (e w) <;> simp
    exact hsame v w hv hw hcvw

end CFSG.Quasithin.H13.Orbit
