module

public import Certificates.Kernel.Co2Census.SpinK
public import Certificates.Kernel.Co2Census.S0
public import CFSG.Certificates.Kernel.Co2Census.SpinSound

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.KC.Co2Census Matrix

theorem castM_prod (l : List (Matrix (Fin 8) (Fin 8) ℤ)) : castM l.prod = (l.map castM).prod := by
  induction l with
  | nil => exact castM_one
  | cons a l ih => rw [List.prod_cons, castM_mul, ih, List.map_cons, List.prod_cons]

theorem lsp_spec {k : ℕ} (hk : k < 16) :
    WF8 (lspF k) ∧ decRP (lspF k) = castM (toMatZ (Native.spinMats ())[k]!) := by
  have h := List.all_eq_true.1 lsp_ok k (List.mem_range.2 hk)
  rw [beq_iff_eq] at h
  rw [h]
  exact ⟨wf_rowsP _, decRP_rowsP _⟩

theorem word_spec (w : List (Fin 8 × Bool)) :
    WF8 (wordRP lspF (w.map Native.sCode)) ∧
      decRP (wordRP lspF (w.map Native.sCode)) = castM (toMatZ (Native.wordZ (w.map Native.sCode))) := by
  have hL : ∀ k ∈ w.map Native.sCode, WF8 (lspF k) := fun k hk =>
    (lsp_spec (CFSG.KC.Co2SmithS.map_sCode_lt w k hk)).1
  refine ⟨wf_wordRP _ hL, ?_⟩
  rw [decRP_wordRP _ hL, toMatZ_wordZ, castM_prod, List.map_map, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  exact (lsp_spec (CFSG.KC.Co2SmithS.sCode_lt l)).2

theorem ab_spec {x : ℕ} (hx : x = 2 ∨ x = 3) :
    WF8 (abF x) ∧ decRP (abF x) =
      castM (spinHom (if x = 2 then aHat else bHat) : Matrix (Fin 8) (Fin 8) ℤ) := by
  have h := ab_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases hx with rfl | rfl
  · rw [abF, if_pos rfl, if_pos rfl, spinHom_aHat, h.1]
    exact word_spec _
  · rw [abF, if_neg (by norm_num), if_neg (by norm_num), spinHom_bHat, h.2]
    exact word_spec _

theorem gen_spec :
    ∀ w : List ℕ, (∀ x ∈ w, x = 2 ∨ x = 3) →
      WF8 (wordRP abF w) ∧ decRP (wordRP abF w) = castM (spinHom (genLift w) : Matrix (Fin 8) (Fin 8) ℤ)
  | [], _ => by
    refine ⟨wf_idRP, ?_⟩
    rw [show wordRP abF [] = idRP from rfl, decRP_idRP, genLift, List.foldr_nil, map_one,
      Units.val_one, castM_one]
  | x :: w, hw => by
    obtain ⟨h1, h2⟩ := ab_spec (hw x List.mem_cons_self)
    obtain ⟨ih1, ih2⟩ := gen_spec w fun y hy => hw y (List.mem_cons_of_mem _ hy)
    refine ⟨wf_mulRP h1 ih1, ?_⟩
    change decRP (mulRP (abF x) (wordRP abF w)) =
      castM (spinHom ((if x = 2 then aHat else bHat) * genLift w) : Matrix (Fin 8) (Fin 8) ℤ)
    rw [decRP_mulRP h1 ih1, h2, ih2, map_mul, Units.val_mul, castM_mul]

theorem gsp_spec {k l : ℕ}
    (hk : k < 6) (hl : l < (Native.chainGens[k]!).size) :
    WF8 (gspF k l) ∧ decRP (gspF k l) =
      castM (spinHom (genLift (Native.chainGens[k]!)[l]!) : Matrix (Fin 8) (Fin 8) ℤ) := by
  have h := List.all_eq_true.1 gsp_ok k (List.mem_range.2 hk)
  have h2 := List.all_eq_true.1 h l (List.mem_range.2 hl)
  rw [beq_iff_eq] at h2
  rw [h2]
  exact gen_spec _ (chainGens_letters k hk l hl)

theorem tsp_spec
    {k : ℕ} (hk : k < 6) :
    ∀ i < Native.chainOrb[k]!, WF8 (tspF (trOff k + i)) ∧
      decRP (tspF (trOff k + i)) = castM (spinHom (tLift k i) : Matrix (Fin 8) (Fin 8) ℤ) := by
  have h := List.all_eq_true.1 tsp_ok k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Nat.beq_eq] at h
  obtain ⟨h0, hs⟩ := h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [Nat.add_zero, h0, tLift_zero, map_one, Units.val_one, castM_one, decRP_idRP]
      exact ⟨wf_idRP, rfl⟩
    · obtain ⟨hp, hl, -⟩ := (trOK_spec hk).2 i hi hi0
      have hpar : (chainRec k).2.1[i]! = KernelCo2SmithS.PI (k + 1) 0 i := by
        rw [chainRec_rec hk, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
      have hlet : (chainRec k).2.2[i]! = KernelCo2SmithS.PI (k + 1) 1 i := by
        rw [chainRec_rec hk, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
      have he := (hs i hi).resolve_left hi0
      obtain ⟨g1, g2⟩ := gsp_spec hk hl
      obtain ⟨i1, i2⟩ := ih _ hp (hp.trans hi)
      rw [he, tLift_of_lt hi0 (by rw [hpar]; exact hp), hpar, hlet]
      refine ⟨wf_mulRP g1 i1, ?_⟩
      rw [decRP_mulRP g1 i1, g2, i2, map_mul, Units.val_mul, castM_mul]

theorem tsp_spec'
    {k i : ℕ} (hk : k < 6)
    (hi : i < Native.chainOrb[k]!) {j : ℕ} (hj : j = trOff k + i) :
    WF8 (tspF j) ∧ decRP (tspF j) = castM (spinHom (tLift k i) : Matrix (Fin 8) (Fin 8) ℤ) :=
  hj ▸ tsp_spec hk i hi

theorem spinMV_spec
    (n : ℕ) {v : List ℕ}
    (hv : v.length = 8) :
    decV (spinMV n v) = castM (spinHom (pLift n) : Matrix (Fin 8) (Fin 8) ℤ) *ᵥ decV v := by
  obtain ⟨a0, b0⟩ := tsp_spec' (k := 0) (i := n % 63) (by norm_num)
    (by rw [show Native.chainOrb[0]! = 63 from rfl]; omega) (j := n % 63)
    (by rw [show trOff 0 = 0 from rfl, Nat.zero_add])
  obtain ⟨a1, b1⟩ := tsp_spec' (k := 1) (i := n / 63 % 32) (by norm_num)
    (by rw [show Native.chainOrb[1]! = 32 from rfl]; omega) (j := 63 + n / 63 % 32) rfl
  obtain ⟨a2, b2⟩ := tsp_spec' (k := 2) (i := n / 2016 % 15) (by norm_num)
    (by rw [show Native.chainOrb[2]! = 15 from rfl]; omega) (j := 95 + n / 2016 % 15) rfl
  obtain ⟨a3, b3⟩ := tsp_spec' (k := 3) (i := n / 30240 % 8) (by norm_num)
    (by rw [show Native.chainOrb[3]! = 8 from rfl]; omega) (j := 110 + n / 30240 % 8) rfl
  obtain ⟨a4, b4⟩ := tsp_spec' (k := 4) (i := n / 241920 % 3) (by norm_num)
    (by rw [show Native.chainOrb[4]! = 3 from rfl]; omega) (j := 118 + n / 241920 % 3) rfl
  obtain ⟨a5, b5⟩ := tsp_spec' (k := 5) (i := n / 725760 % 2) (by norm_num)
    (by rw [show Native.chainOrb[5]! = 2 from rfl]; omega) (j := 121 + n / 725760 % 2) rfl
  have l5 := hv
  have l4 : (mvRP (tspF (121 + n / 725760 % 2)) v).length = 8 := by rw [length_mvRP, a5.1]
  have l3 : (mvRP (tspF (118 + n / 241920 % 3)) (mvRP (tspF (121 + n / 725760 % 2)) v)).length =
      8 := by rw [length_mvRP, a4.1]
  have l2 : (mvRP (tspF (110 + n / 30240 % 8)) (mvRP (tspF (118 + n / 241920 % 3))
      (mvRP (tspF (121 + n / 725760 % 2)) v))).length = 8 := by rw [length_mvRP, a3.1]
  have l1 : (mvRP (tspF (95 + n / 2016 % 15)) (mvRP (tspF (110 + n / 30240 % 8))
      (mvRP (tspF (118 + n / 241920 % 3)) (mvRP (tspF (121 + n / 725760 % 2)) v)))).length = 8 := by
    rw [length_mvRP, a2.1]
  have l0 : (mvRP (tspF (63 + n / 63 % 32)) (mvRP (tspF (95 + n / 2016 % 15))
      (mvRP (tspF (110 + n / 30240 % 8)) (mvRP (tspF (118 + n / 241920 % 3))
        (mvRP (tspF (121 + n / 725760 % 2)) v))))).length = 8 := by rw [length_mvRP, a1.1]
  rw [spinMV, decV_mvRP a0 l0, decV_mvRP a1 l1, decV_mvRP a2 l2, decV_mvRP a3 l3,
    decV_mvRP a4 l4, decV_mvRP a5 l5, b0, b1, b2, b3, b4, b5, pLift]
  simp only [map_mul, Units.val_mul, castM_mul, Matrix.mulVec_mulVec]

end CertificateChecks.KernelCo2Census

end
