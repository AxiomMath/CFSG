module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuAdj
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuGrp
public import Certificates.Data.RuF45Geom

public section

namespace CFSG.Quasithin.H13.F45Ru

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

open scoped Pointwise

@[expose] noncomputable def kgen (i : ℕ) : ↥TA :=
  if h : i < 4 then ⟨titsGen i, titsGen_mem_titsA h⟩ else 1

theorem kgen_val {i : ℕ} (h : i < 4) : (kgen i).1 = titsGen i := by
  simp [kgen, h]

@[expose] noncomputable def letterElt : ℕ × Bool → ↥TA
  | (i, true) => kgen i
  | (i, false) => (kgen i)⁻¹

@[expose] noncomputable def wordElt : Word → ↥TA
  | [] => 1
  | l :: w => letterElt l * wordElt w

theorem invsOK_spec {n : ℕ} {G Gi : Array (Array ℕ)} (h : invsOK n G Gi = true) :
    ∀ i < G.size, isInvA n G[i]! Gi[i]! = true := by
  intro i hi
  simp only [invsOK, Bool.and_eq_true, beq_iff_eq] at h
  exact allLt_spec h.2 hi

theorem rep_lettArr {G Gi : Array (Array ℕ)} (hG : G = titsGenArrs)
    (hGi : invsOK 1755 G Gi = true) {l : ℕ × Bool} (hl : l.1 < 4) :
    Rep 1755 (lettArr G Gi l) (letterElt l).1 := by
  obtain ⟨i, b⟩ := l
  have hsz : G.size = 4 := by rw [hG]; exact titsGenArrs_size
  have hrep : Rep 1755 G[i]! (titsGen i) := by rw [hG]; exact titsGen_rep hl
  cases b
  · have hinv := invsOK_spec hGi i (by omega)
    have := rep_inv_of_isInvA hrep hinv
    simpa [lettArr, letterElt, kgen_val hl] using this
  · simpa [lettArr, letterElt, kgen_val hl] using hrep

theorem rep_evalArr {G Gi : Array (Array ℕ)} (hG : G = titsGenArrs)
    (hGi : invsOK 1755 G Gi = true) :
    ∀ w : Word, (∀ l ∈ w, l.1 < 4) → Rep 1755 (evalArr 1755 G Gi w) (wordElt w).1
  | [], _ => by
    simpa [evalArr, wordElt] using (rep_idA (n := 1755))
  | l :: w, hw => by
    have h1 := rep_lettArr hG hGi (hw l (List.mem_cons_self))
    have h2 := rep_evalArr hG hGi w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    simpa [evalArr, wordElt] using rep_compA h1 h2

theorem lineMapsP_iff {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (v w : Fin 2925) : lineMapsP titsLinePtArr a v w = true ↔ g • titsLine v = titsLine w := by
  constructor
  · intro h
    exact RuType.J47.lineMapsA_spec ha v w h
  · intro h
    rw [lineMapsP, List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    have hmem : titsLinePt v k ∈ titsLine v := RuType.J47.linePt_mem v hk'
    have h1 : g (titsLinePt v k) ∈ titsLine w := by
      rw [← h]
      exact Finset.smul_mem_smul_finset hmem
    have h2 := (RuType.J47.titsLine_mem_iff _ w).1 h1
    rw [← titsLinePt_val v hk', ha (titsLinePt v k)]
    exact h2

theorem lineHom_eq_iff (g : ↥TA) (v w : Fin 2925) :
    titsLineHom g v = w ↔ g.1 • titsLine v = titsLine w := by
  rw [← titsLine_lineHom]
  exact ⟨fun h => by rw [h], fun h => titsLine_injective h⟩

theorem actOK_iff {g : ↥TA} {a : Array ℕ} (ha : Rep 1755 a g.1) {y x : ℕ} (hy : y < 4680)
    (hx : x < 4680) : actOK titsLinePtArr a y x = true ↔ g • ofCode y = ofCode x := by
  by_cases hy1 : y < 1755
  · have hy' : actOK titsLinePtArr a y x = (decide (x < 1755) && a[y]! == x) := by
      simp [actOK, hy1]
    rw [ofCode_inl hy1, smul_inl, hy']
    by_cases hx1 : x < 1755
    · rw [ofCode_inl hx1]
      simp only [hx1, decide_true, Bool.true_and, beq_iff_eq, Sum.inl.injEq]
      rw [ha.apply hy1, Fin.ext_iff]
    · rw [ofCode_inr (by omega) hx]
      simp [hx1]
  · have hy' : actOK titsLinePtArr a y x = (decide (1755 ≤ x) && decide (x < 4680) &&
        lineMapsP titsLinePtArr a (y - 1755) (x - 1755)) := by
      simp [actOK, hy1]
    rw [ofCode_inr (by omega) hy, smul_inr, hy']
    by_cases hx1 : x < 1755
    · rw [ofCode_inl hx1]
      simp [hx1]
    · rw [ofCode_inr (by omega) hx]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Sum.inr.injEq]
      rw [lineHom_eq_iff]
      have := lineMapsP_iff ha ⟨y - 1755, by omega⟩ ⟨x - 1755, by omega⟩
      constructor
      · rintro ⟨-, h⟩
        exact this.1 h
      · intro h
        exact ⟨⟨by omega, hx⟩, this.2 h⟩

end CFSG.Quasithin.H13.F45Ru
