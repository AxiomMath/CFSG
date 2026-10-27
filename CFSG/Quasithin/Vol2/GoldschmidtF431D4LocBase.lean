module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Lines
public import Certificates.Certificate4237

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem locComm_iff {X Y : Array ℕ} {x y : D} (hX : validR X = true) (hY : validR Y = true)
    (hx : RepE d4E X x) (hy : RepE d4E Y y) : locComm X Y = true ↔ x * y = y * x := by
  have v1 : validR (mulR X Y) = true := validR_mulR (size_of_validR hX) hY
  have v2 : validR (mulR Y X) = true := validR_mulR (size_of_validR hY) hX
  simp only [locComm, beq_iff_eq]
  exact eq_iff_of_repE v1 v2 (repE_mul hx hy) (repE_mul hy hx)

theorem locComm_of_eq {X Y : Array ℕ} {x y : D} (hx : RepE d4E X x) (hy : RepE d4E Y y)
    (h : locComm X Y = true) : x * y = y * x := by
  simp only [locComm, beq_iff_eq] at h
  exact eq_of_repE d4E_injective (repE_mul hx hy) (h ▸ repE_mul hy hx)

theorem sqR_iff {X : Array ℕ} {x : D} (hX : validR X = true) (hx : RepE d4E X x) :
    mulR X X = oneR ↔ x * x = 1 :=
  eq_iff_of_repE (validR_mulR (size_of_validR hX) hX) validR_oneR (repE_mul hx hx) repE_one

theorem eqOneR_iff {X : Array ℕ} {x : D} (hX : validR X = true) (hx : RepE d4E X x) :
    X = oneR ↔ x = 1 :=
  eq_iff_of_repE hX validR_oneR hx repE_one

theorem locIsInv_iff {X : Array ℕ} {x : D} (hX : validR X = true) (hx : RepE d4E X x) :
    locIsInv X = true ↔ x * x = 1 ∧ x ≠ 1 := by
  unfold locIsInv
  rw [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne, sqR_iff hX hx]
  exact and_congr Iff.rfl (by rw [ne_eq, ne_eq, eqOneR_iff hX hx])

theorem repE_conjI {c c' X : Array ℕ} {g x : D} (hc : RepE d4E c g) (hc' : RepE d4E c' g⁻¹)
    (hX : RepE d4E X x) : RepE d4E (conjI c c' X) (g * x * g⁻¹) :=
  repE_mul (repE_mul hc hX) hc'

theorem mem_centralizer_conj' {G : Type*} [Group G] {a c x : G} :
    x ∈ Subgroup.centralizer ({c * a * c⁻¹} : Set G) ↔
      c⁻¹ * x * c ∈ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc c⁻¹ * x * c * a = c⁻¹ * (x * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * x) * c := by rw [h]
      _ = a * (c⁻¹ * x * c) := by group
  · intro h
    calc x * (c * a * c⁻¹) = c * (c⁻¹ * x * c * a) * c⁻¹ := by group
      _ = c * (a * (c⁻¹ * x * c)) * c⁻¹ := by rw [h]
      _ = (c * a * c⁻¹) * x := by group

theorem card_centralizer_conj' {G : Type*} [Group G] (a c : G) :
    Nat.card (Subgroup.centralizer ({c * a * c⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) :=
  Nat.card_congr
    { toFun := fun x => ⟨c⁻¹ * x * c, mem_centralizer_conj'.1 x.2⟩
      invFun := fun y => ⟨c * y * c⁻¹, mem_centralizer_conj'.2 (by simp [mul_assoc])⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }

theorem loc_parts :
    locCz.ok d4Gens z0R 819 = true ∧ locStepWords.all locStepOK = true ∧
    locTCheck locET = true ∧ locVCheck locCz locEC locCzC = true ∧
    locFusion locCz locCu locET locEQ = true ∧ locQCheck locCz locET locEQ = true := by
  have h := Certificates.certificate4237
  simp only [locCheck, locCheckOn, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem locCz_eq : locCz = cz := by
  rw [cz_eq]
  unfold locCz
  rfl

section Words


theorem d4GenG_sq {k : ℕ} (hk : k < 8) : d4GenG k * d4GenG k = 1 :=
  (gens_hyp k (by rw [d4Gens_size']; exact hk)).2

theorem d4Word_append (l₁ l₂ : List ℕ) : d4Word (l₁ ++ l₂) = d4Word l₁ * d4Word l₂ := by
  simp [d4Word, List.map_append, List.prod_append]

theorem d4Word_cons (k : ℕ) (w : List ℕ) : d4Word (k :: w) = d4GenG k * d4Word w := by
  simp [d4Word]

theorem d4Word_mul_reverse : ∀ w : List ℕ, (∀ k ∈ w, k < 8) →
    d4Word w * d4Word w.reverse = 1
  | [], _ => by simp [d4Word]
  | k :: w, hw => by
    have ih := d4Word_mul_reverse w (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk'))
    have hk : k < 8 := hw k List.mem_cons_self
    rw [List.reverse_cons, d4Word_append, d4Word_cons]
    have e2 : d4Word [k] = d4GenG k := by simp [d4Word]
    rw [e2]
    calc d4GenG k * d4Word w * (d4Word w.reverse * d4GenG k)
        = d4GenG k * (d4Word w * d4Word w.reverse) * d4GenG k := by group
      _ = 1 := by rw [ih, mul_one]; exact d4GenG_sq hk

theorem d4Word_reverse_inv {w : List ℕ} (hw : ∀ k ∈ w, k < 8) :
    (d4Word w)⁻¹ = d4Word w.reverse :=
  inv_eq_of_mul_eq_one_right (d4Word_mul_reverse w hw)

theorem repE_d4Word_reverse {w : List ℕ} (hw : ∀ k ∈ w, k < 8) :
    RepE d4E (wordR d4Gens w.reverse) (d4Word w)⁻¹ := by
  rw [d4Word_reverse_inv hw]
  exact repE_d4Word fun k hk => hw k (List.mem_reverse.1 hk)

theorem step_spec {s : ℕ} (hs : s < locSteps.size) (hall : locStepWords.all locStepOK = true) :
    ∃ g : D, RepE d4E locSteps[s]!.1 g ∧ RepE d4E locSteps[s]!.2 g⁻¹ ∧
      (g ∈ d4H ∨ g ∈ d4N) := by
  have hlen : s < locStepWords.length := by simpa [locSteps] using hs
  have hmem : locStepWords[s] ∈ locStepWords := List.getElem_mem hlen
  have hok := List.all_eq_true.1 hall _ hmem
  have hget : locSteps[s]! = locStepArr locStepWords[s] := by
    simp [locSteps, hlen]
  simp only [locStepOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hw, hflag⟩ := hok
  refine ⟨d4Word locStepWords[s].2, ?_, ?_, ?_⟩
  · rw [hget]
    exact repE_d4Word hw
  · rw [hget]
    exact repE_d4Word_reverse hw
  · have hr := rep_d4WordArr locStepWords[s].2 hw
    split_ifs at hflag with hf
    · left
      exact mem_d4H_of_rep hr (by simpa [locWordArr, d4WordArr] using hflag)
    · right
      exact mem_d4N_of_rep hr (by simpa [locWordArr, d4WordArr] using hflag)

end Words

end CFSG.Quasithin.D4Hex
