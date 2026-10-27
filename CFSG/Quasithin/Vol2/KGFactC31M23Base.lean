
module

public import CFSG.Quasithin.Vol2.KGFactC31Fix
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public import CFSG.Quasithin.Vol2.KGFactC31Act
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck
public import CFSG.Quasithin.Vol2.KGFactC31M23Data

public section

namespace CFSG.Quasithin.KGC31.M23

open CFSG.Open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31

abbrev G₀ : Type := ↥NativeSporadic.M23

theorem hn23 : (23 : ℕ) < 2 ^ 32 := by norm_num

theorem hgens : ∀ l, gensG l ∈ NativeSporadic.M23 := fun l => by
  rw [← m23Certificate_originalSubgroup]
  unfold gensG
  split_ifs
  · exact m23_gens_mem _ (by simp)
  · exact m23_gens_mem _ (by simp)

theorem hrep : ∀ l, Rep 23 (gensT l) (gensG l) := fun l => by
  unfold gensT gensG
  split_ifs
  · exact rep_toTable hn23 _
  · exact rep_toTable hn23 _

@[expose] def elt (w : List ℤ) : G₀ := ⟨wordG gensG w, wordG_mem_of _ hgens w⟩

theorem rep_elt (w : List ℤ) : Rep 23 (wordT 23 gensT w) ((elt w : G₀) : Equiv.Perm (Fin 23)) :=
  Rep.wordT hn23 w fun l _ => hrep l

theorem validM23 : ValidSchreier m23Certificate :=
  m23Certificate_check

@[expose] noncomputable def b0 : Equiv.Perm (Fin 23) := (elt (wW.headD []) : G₀)

theorem rep_b0 : Rep 23 b0T b0 := rep_elt _

@[expose] noncomputable def cbG : List (Equiv.Perm (Fin 23)) :=
  ((enumeration m23Certificate).filter fun h => decide (h * b0 = b0 * h)).reverse

theorem forall₂_cbT : List.Forall₂ (Rep 23) cbT cbG := by
  have h := filterProducts_spec (f := commT 23 b0T) (P := fun h => h * b0 = b0 * h)
    (fun T g hT => (commT_iff rep_b0 hT).trans eq_comm) (forall₂_levelTables hn23 m23Certificate)
    (Rep.idT hn23) (acc := []) (accG := []) .nil
  simp only [one_mul, List.map_id', List.append_nil] at h
  exact h

theorem card_eq_countP_cbT {f : Table → Bool}
    {P : Equiv.Perm (Fin 23) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep 23 T g → (f T = true ↔ P g)) (hPb : ∀ g, P g → g * b0 = b0 * g) :
    Nat.card {x : NativeSporadic.M23 // P x} = cbT.countP f := by
  rw [countP_eq_of_forall₂ forall₂_cbT (q := fun g => decide (P g))
    (fun T g hT _ => by rw [hfP T g hT, decide_eq_true_iff]), cbG, List.countP_reverse,
    List.countP_filter]
  have h := card_subtype_eq_countP NativeSporadic.M23 (enumeration m23Certificate)
    (enumeration_nodup _ validM23)
    (fun g => by rw [mem_enumeration_iff _ validM23, m23Certificate_originalSubgroup]) P
  rw [h]
  congr 1
  funext g
  by_cases hg : P g
  · simp [hg, hPb g hg]
  · simp [hg]

theorem card_le_cosetCount {f : Table → Bool}
    {P : Equiv.Perm (Fin 23) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep 23 T g → (f T = true ↔ P g)) {rsT : List Table}
    {rsG : List (Equiv.Perm (Fin 23))} (hrs : List.Forall₂ (Rep 23) rsT rsG)
    (hrsM : ∀ r ∈ rsG, r ∈ NativeSporadic.M23)
    (hP : ∀ g ∈ NativeSporadic.M23, P g → ∃ r ∈ rsG, g * b0 * g⁻¹ = r * b0 * r⁻¹) :
    Nat.card {g : NativeSporadic.M23 // P g} ≤ cosetCount 23 cbT rsT f := by
  classical
  refine (card_le_sum_coset b0 rsG P hP hrsM).trans (le_of_eq ?_)
  rw [cosetCount]
  refine (sum_map_eq_of_forall₂ hrs fun rT r hr hrm => ?_).symm
  have hr' : r ∈ NativeSporadic.M23 := hrsM r hrm
  rw [card_eq_countP_cbT (P := fun c => c * b0 = b0 * c ∧ P (r * c))
    (f := fun c => commT 23 b0T c && f (compT 23 rT c))]
  · rw [countP_eq_of_forall₂ forall₂_cbT (q := fun c => decide (c * b0 = b0 * c ∧ P (r * c)))
      (fun T g hT hg => ?_), countP_eq_of_forall₂ forall₂_cbT
      (q := fun c => decide (c * b0 = b0 * c ∧ P (r * c))) (fun T g hT hg => ?_)]
    · rw [Bool.and_eq_true, commT_iff rep_b0 hT, hfP _ _ (Rep.compT hr hT), decide_eq_true_iff]
      exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩
    · have hc : g * b0 = b0 * g := by
        rw [cbG, List.mem_reverse, List.mem_filter, decide_eq_true_iff] at hg
        exact hg.2
      rw [hfP _ _ (Rep.compT hr hT), decide_eq_true_iff]
      exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
  · intro T g hT
    rw [Bool.and_eq_true, commT_iff rep_b0 hT, hfP _ _ (Rep.compT hr hT)]
    exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩
  · exact fun g h => h.1

end CFSG.Quasithin.KGC31.M23

end
