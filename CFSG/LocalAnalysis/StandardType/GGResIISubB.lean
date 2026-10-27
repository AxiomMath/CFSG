module

public import CFSG.LocalAnalysis.StandardType.GGResIICell

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggStdTableB {R : Type} (ι : ℤ → R) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (ib ic : Fin n) (u v : R) : Fin (n + 1) → Vector R (n + 2) :=
  fun k => Vector.ofFn fun l =>
    if l.val = n + 1 then (if k.val = ib.val then ι 1 else ι 0) else ggStdEntry ι C ib ic u v k l

@[expose] def ggKNode {n : ℕ} (ib : Fin n) (r : Fin n) : Fin (n + 1) :=
  if r.val = ib.val then Fin.last n else r.castSucc

@[expose] def ggSubBAt (p : ℕ) [NeZero p] {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n)
    (v₀ : ℕ) (wits : List (ℕ × List (List ℕ) × GGCellWit n)) (u : ZMod p) : Bool :=
  match wits.find? (fun w => w.1 == u.val) with
  | some w =>
    (List.finRange n).all (fun j₀ => (List.finRange n).all fun j =>
      decide (∑ r : Fin n, (((w.2.1.getD j₀.val []).getD r.val 0 : ℕ) : ZMod p) *
        (ggStdTable (Int.cast) C ib ic u (v₀ : ZMod p) (ggKNode ib r)).get j.castSucc.castSucc =
          if j₀ = j then 1 else 0)) &&
    w.2.2.notW && ggCellWitCheck (ggStdTableB (Int.cast) C ib ic u (v₀ : ZMod p)) ib w.2.2
  | none => false

@[expose] def GGSubBCheck (p : ℕ) [NeZero p] {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n)
    (κ : List ℤ) (v₀ : ℕ) (wits : List (ℕ × List (List ℕ) × GGCellWit n)) : Prop :=
  (∀ i : Fin n, ((∑ j : Fin n, C i j * κ.getD j.val 0 : ℤ) : ZMod p) = 0) ∧
    ((κ.getD ib.val 0 : ℤ) : ZMod p) ≠ 0 ∧
    (v₀ : ZMod p) * ((κ.getD ib.val 0 : ℤ) : ZMod p) = ((κ.getD ic.val 0 : ℤ) : ZMod p) ∧
    ∀ u : ZMod p, u * ((κ.getD ib.val 0 : ℤ) : ZMod p) - ((κ.getD ic.val 0 : ℤ) : ZMod p) ≠ 0 →
      ggSubBAt p C ib ic v₀ wits u = true

@[expose] def GGSubBVac (p : ℕ) [NeZero p] {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib : Fin n)
    (κ : List ℤ) (i₀ : Fin n) : Prop :=
  (∀ i : Fin n, ((∑ j : Fin n, C i j * κ.getD j.val 0 : ℤ) : ZMod p) = 0) ∧
    ((κ.getD ib.val 0 : ℤ) : ZMod p) = 0 ∧ ((κ.getD i₀.val 0 : ℤ) : ZMod p) ≠ 0

section Sound

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem ggResII_subB_facts {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} (hsymm : ∀ i j, C i j = C j i)
    {ib ic : Fin n} (hbc : ib ≠ ic) {κ : Fin n → ℤ} (hκ : ∀ i : Fin n,
      ((∑ j : Fin n, C i j * κ j : ℤ) : ZMod p) = 0) {i₀ : Fin n} (hi₀ : ((κ i₀ : ℤ) : ZMod p) ≠ 0)
    {h : Fin (n + 1) → V} {x : V} {α : Fin (n + 1) → Module.Dual (ZMod p) V} {u v : ZMod p}
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTable (Int.cast) C ib ic u v) h x α)
    (hLI : LinearIndependent (ZMod p) fun i : Fin n => h i.castSucc)
    (hfix : ∀ w : V, (∀ i : Fin n, α i.castSucc w = 0) → w ∈ Submodule.span (ZMod p) {x})
    (hdep : h (Fin.last n) ∈ Submodule.span (ZMod p) (Set.range fun i : Fin n => h i.castSucc)) :
    u * ((κ ib : ℤ) : ZMod p) - ((κ ic : ℤ) : ZMod p) ≠ 0 ∧
      v * ((κ ib : ℤ) : ZMod p) - ((κ ic : ℤ) : ZMod p) = 0 := by
  have hpair : ∀ k l : Fin (n + 1), α k (h l) =
      ggStdEntry (Int.cast) C ib ic u v k l.castSucc := by
    intro k l
    rw [hT.1 k l]
    simp [ggStdTable, Vector.get_ofFn]
  have hxa : α (Fin.last n) x = 1 := by
    rw [hT.2]
    simp [ggStdTable, Vector.get_ofFn, ggStdEntry_ax]
  set z : V := ∑ i : Fin n, ((κ i : ℤ) : ZMod p) • h i.castSucc with hz
  have hzL : ∀ j : Fin n, α j.castSucc z = 0 := by
    intro j
    rw [hz, map_sum]
    simp only [map_smul, smul_eq_mul, hpair, ggStdEntry_LL]
    have := hκ j
    push_cast at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hfix z hzL)
  have hz0 : z ≠ 0 := by
    intro h0
    have := (Fintype.linearIndependent_iff.mp hLI) (fun i => ((κ i : ℤ) : ZMod p)) h0 i₀
    exact hi₀ this
  have hza : α (Fin.last n) z = -((κ ic : ℤ) : ZMod p) + u * ((κ ib : ℤ) : ZMod p) := by
    rw [hz, map_sum]
    simp only [map_smul, smul_eq_mul, hpair, ggStdEntry_aL]
    rw [← ggResII_sum_two hbc u (fun i => ((κ i : ℤ) : ZMod p))]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [mul_comm]
  refine ⟨fun h0 => ?_, ?_⟩
  · apply hz0
    have hc0 : c = 0 := by
      have h1 : α (Fin.last n) z = c := by rw [← hc, map_smul, hxa, smul_eq_mul, mul_one]
      rw [← h1, hza]
      linear_combination h0
    rw [← hc, hc0, zero_smul]
  · obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hdep
    have h1 : ∑ j : Fin n, ((κ j : ℤ) : ZMod p) * α j.castSucc (h (Fin.last n)) = 0 := by
      rw [← hd]
      simp only [map_sum, map_smul, smul_eq_mul, hpair, ggStdEntry_LL, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      have := hκ i
      push_cast at this
      calc ∑ j : Fin n, ((κ j : ℤ) : ZMod p) * (d i * ((C j i : ℤ) : ZMod p))
          = d i * ∑ j : Fin n, ((C i j : ℤ) : ZMod p) * ((κ j : ℤ) : ZMod p) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hsymm j i]
            ring
        _ = 0 := by rw [this, mul_zero]
    simp only [hpair, ggStdEntry_La] at h1
    have h2 := ggResII_sum_two hbc v (fun j => ((κ j : ℤ) : ZMod p))
    have h3 : ∑ j : Fin n, ((κ j : ℤ) : ZMod p) * (if j.val = ic.val then ((-1 : ℤ) : ZMod p)
        else if j.val = ib.val then v else ((0 : ℤ) : ZMod p)) =
        ∑ i : Fin n, (if i.val = ic.val then (-1 : ZMod p) else if i.val = ib.val then v else 0) *
          ((κ i : ℤ) : ZMod p) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp [mul_comm]
    rw [h3, h2] at h1
    linear_combination h1

theorem ggResII_subB_vacuous {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} (hsymm : ∀ i j, C i j = C j i)
    {ib ic : Fin n} (hbc : ib ≠ ic) {κ : List ℤ} {i₀ : Fin n} (hvac : GGSubBVac p C ib κ i₀)
    {h : Fin (n + 1) → V} {x : V} {α : Fin (n + 1) → Module.Dual (ZMod p) V} {u v : ZMod p}
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTable (Int.cast) C ib ic u v) h x α)
    (hLI : LinearIndependent (ZMod p) fun i : Fin n => h i.castSucc)
    (hfix : ∀ w : V, (∀ i : Fin n, α i.castSucc w = 0) → w ∈ Submodule.span (ZMod p) {x})
    (hdep : h (Fin.last n) ∈ Submodule.span (ZMod p) (Set.range fun i : Fin n => h i.castSucc)) :
    False := by
  obtain ⟨hκ, hb, hi₀⟩ := hvac
  obtain ⟨h1, h2⟩ := ggResII_subB_facts hsymm hbc (κ := fun i => κ.getD i.val 0) hκ hi₀ hT hLI hfix
    hdep
  simp only [hb, mul_zero, zero_sub] at h1 h2
  exact h1 h2

theorem ggResII_subB_sound {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} (hsymm : ∀ i j, C i j = C j i)
    {ib ic : Fin n} (hbc : ib ≠ ic) {κ : List ℤ} {v₀ : ℕ}
    {wits : List (ℕ × List (List ℕ) × GGCellWit n)} (hchk : GGSubBCheck p C ib ic κ v₀ wits)
    (hp2 : p ≠ 2) {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V} {u v : ZMod p}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTable (Int.cast) C ib ic u v) h x α)
    (hsep : ∀ w : V, (∀ k, α k w = 0) → w = 0)
    (hLI : LinearIndependent (ZMod p) fun i : Fin n => h i.castSucc)
    (hfix : ∀ w : V, (∀ i : Fin n, α i.castSucc w = 0) → w ∈ Submodule.span (ZMod p) {x})
    (hdep : h (Fin.last n) ∈ Submodule.span (ZMod p) (Set.range fun i : Fin n => h i.castSucc))
    {y : V} (hyK : ∀ k : Fin (n + 1), k ≠ ib.castSucc → α k y = 0)
    (hyx : y ∉ Submodule.span (ZMod p) {x}) :
    GGResIIConcl g h α ib := by
  obtain ⟨hκ, hb, hv₀, hat⟩ := hchk
  obtain ⟨hu, hv⟩ := ggResII_subB_facts hsymm hbc (κ := fun i => κ.getD i.val 0) hκ hb hT hLI hfix
    hdep
  have hvv : v = (v₀ : ZMod p) := by
    have : (v - (v₀ : ZMod p)) * ((κ.getD ib.val 0 : ℤ) : ZMod p) = 0 := by
      linear_combination hv - hv₀
    rcases mul_eq_zero.mp this with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 hb
  subst hvv
  have hu' := hat u hu
  unfold ggSubBAt at hu'
  split at hu'
  · rename_i w hw
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
      decide_eq_true_eq] at hu'
    obtain ⟨⟨hlam, hnw⟩, hwit⟩ := hu'
    have hpair : ∀ k l : Fin (n + 1), α k (h l) =
        (ggStdTable (Int.cast) C ib ic u (v₀ : ZMod p) k).get l.castSucc := by
      intro k l
      rw [hT.1 k l, RingHom.id_apply]
    by_cases hyU : y ∈ Submodule.span (ZMod p) (Set.range fun i : Fin n => h i.castSucc)
    ·
      exfalso
      apply hyx
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hyU
      have hK : ∀ r : Fin n, ∑ j : Fin n, d j * α (ggKNode ib r) (h j.castSucc) = 0 := by
        intro r
        have hne : ggKNode ib r ≠ ib.castSucc := by
          unfold ggKNode
          split_ifs with hr
          · intro h
            have h1 := congrArg Fin.val h
            simp only [Fin.val_last, Fin.coe_castSucc] at h1
            have := ib.isLt
            omega
          · intro h
            apply hr
            simpa using congrArg Fin.val h
        have := hyK _ hne
        rw [← hd, map_sum] at this
        simpa only [map_smul, smul_eq_mul] using this
      have hd0 : ∀ j₀ : Fin n, d j₀ = 0 := by
        intro j₀
        calc d j₀ = ∑ j : Fin n, d j * (if j₀ = j then 1 else 0) := by
              rw [Finset.sum_eq_single j₀ (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
                (fun h0 => absurd (Finset.mem_univ j₀) h0), if_pos rfl, mul_one]
          _ = ∑ j : Fin n, d j * ∑ r : Fin n, (((w.2.1.getD j₀.val []).getD r.val 0 : ℕ) :
                ZMod p) * α (ggKNode ib r) (h j.castSucc) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [← hlam j₀ j]
              congr 1
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [hpair]
          _ = ∑ r : Fin n, (((w.2.1.getD j₀.val []).getD r.val 0 : ℕ) : ZMod p) *
                ∑ j : Fin n, d j * α (ggKNode ib r) (h j.castSucc) := by
              simp only [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => ?_
              ring
          _ = 0 := Finset.sum_eq_zero fun r _ => by rw [hK r, mul_zero]
      rw [← hd]
      simp only [hd0, zero_smul, Finset.sum_const_zero]
      exact Submodule.zero_mem _
    ·
      set β := α ib.castSucc y with hβ
      have hβ0 : β ≠ 0 := by
        intro h0
        apply hyU
        have : y = 0 := hsep y fun k => by
          by_cases hk : k = ib.castSucc
          · rw [hk]; exact h0
          · exact hyK k hk
        rw [this]
        exact Submodule.zero_mem _
      have hTB : GGFTable (RingHom.id (ZMod p)) (ggStdTableB (Int.cast) C ib ic u (v₀ : ZMod p)) h
          (β⁻¹ • y) α := by
        constructor
        · intro k l
          rw [hT.1 k l]
          simp only [ggStdTable, ggStdTableB, Vector.get_ofFn, RingHom.id_apply, Fin.coe_castSucc]
          rw [if_neg (by omega)]
        · intro k
          simp only [ggStdTableB, Vector.get_ofFn, RingHom.id_apply, Fin.val_last, if_true,
            map_smul, smul_eq_mul]
          by_cases hk : k = ib.castSucc
          · subst hk
            simp only [Fin.coe_castSucc, if_true, Int.cast_one]
            rw [← hβ]
            exact inv_mul_cancel₀ hβ0
          · rw [hyK k hk, mul_zero]
            have : k.val ≠ ib.val := fun h => hk (Fin.ext (by simpa using h))
            simp [this]
      exact ggResII_cellWit_sound_nw hp2 hg h2 hTB hsep _ hnw hwit
  · exact absurd hu' (by simp)

end Sound

end CFSG.StandardType
