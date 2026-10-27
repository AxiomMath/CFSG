module

public import CFSG.Quasithin.MS93.MSPHeis

public section

namespace CFSG.Quasithin.MS93.S59

open CFSG.Quasithin.MS93.MSP Matrix

variable {F : Type} [Field F]

theorem span_map_mat (g : Sp4 F) (x : V4 F) :
    (F ∙ x).map (mulVecLin (mat g)) = F ∙ (mat g *ᵥ x) := by
  rw [Submodule.map_span, Set.image_singleton, mulVecLin_apply]

theorem qPoint_span_map_conj (g : Sp4 F) (x : V4 F) :
    (qPoint (F ∙ x)).map (MulAut.conj g).toMonoidHom = qPoint (F ∙ (mat g *ᵥ x)) := by
  rw [qPoint_map_conj, span_map_mat]

theorem map_conj_le_of_mem {G : Type*} [Group G] {H K : Subgroup G} {g : G} (hHK : H ≤ K)
    (hg : g ∈ K) : H.map (MulAut.conj g).toMonoidHom ≤ K := by
  rintro _ ⟨y, hy, rfl⟩
  exact K.mul_mem (K.mul_mem hg (hHK hy)) (K.inv_mem hg)

theorem transv_mem_fixer_span {w x : V4 F} (h : form F x w = 0) (c : F) :
    transv w c ∈ fixer (F ∙ x) := by
  rw [mem_fixer]
  intro v hv
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [transv_mulVec, map_smul, smul_eq_mul, form_swap, h, neg_zero, mul_zero, mul_zero,
    zero_smul, add_zero]

theorem mulVec_ne_zero (g : Sp4 F) {x : V4 F} (hx : x ≠ 0) : mat g *ᵥ x ≠ 0 := by
  intro h
  refine hx (mulVec_mat_injective g ?_)
  show mat g *ᵥ x = mat g *ᵥ 0
  rw [h, mulVec_zero]

variable [CharP F 2]

theorem mulVec_eq_of_span_eq {e : Sp4 F} {n : ℕ} (hn : e ^ 2 ^ n = 1) {x : V4 F} (hx : x ≠ 0)
    (hex : F ∙ (mat e *ᵥ x) = F ∙ x) : mat e *ᵥ x = x := by
  have hmem : mat e *ᵥ x ∈ F ∙ x := hex ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  have hpow : ∀ m : ℕ, mat (e ^ m) *ᵥ x = c ^ m • x := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, one_smul, mat_one, one_mulVec]
    | succ m ih =>
      rw [pow_succ, mat_mul_mulVec, ← hc, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have h1 : c ^ 2 ^ n • x = x := by rw [← hpow, hn, mat_one, one_mulVec]
  have h2 : (c ^ 2 ^ n - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
  have h3 : c ^ 2 ^ n = 1 := by
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : (c - 1) ^ 2 ^ n = 0 := by rw [sub_pow_char_pow, h3, one_pow, sub_self]
  have h5 : c = 1 := sub_eq_zero.1 (pow_eq_zero_iff (by positivity) |>.1 h4)
  rw [← hc, h5, one_smul]

theorem fixer_span_sup_eq_top {x : V4 F} (hx : x ≠ 0) {E : Subgroup (Sp4 F)}
    (hE : IsPGroup 2 E) {e : Sp4 F} (heE : e ∈ E) (hex : mat e *ᵥ x ≠ x) :
    fixer (F ∙ x) ⊔ E = ⊤ := by
  set K := fixer (F ∙ x) ⊔ E with hK
  obtain ⟨n, hn⟩ := hE ⟨e, heE⟩
  have hn' : e ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  set y := mat e *ᵥ x with hy
  have hy0 : y ≠ 0 := mulVec_ne_zero e hx
  have hpne : F ∙ y ≠ F ∙ x := fun h => hex (mulVec_eq_of_span_eq hn' hx h)
  have hQx : qPoint (F ∙ x) ≤ K := (qPoint_le_fixer _).trans le_sup_left
  have heK : e ∈ K := Subgroup.mem_sup_right heE
  have hQy : qPoint (F ∙ y) ≤ K := by
    rw [hy, ← qPoint_span_map_conj]
    exact map_conj_le_of_mem hQx heK
  rw [eq_top_iff]
  by_cases hopp : F ∙ y ≤ perp (F ∙ x)
  ·
    have hnot : ¬ perp (F ∙ x) ≤ perp (F ∙ y) := by
      intro hle
      have h1 : F ∙ y ≤ F ∙ x := by
        have := perp_antitone hle
        rwa [perp_perp, perp_perp] at this
      exact hpne (Submodule.eq_of_le_of_finrank_eq h1
        (by rw [isPoint_span hy0, isPoint_span hx]))
    obtain ⟨w, hwx, hwy⟩ := Set.not_subset.1 hnot
    rw [SetLike.mem_coe, mem_perp_span] at hwx hwy
    have hfK : transv w 1 ∈ K := Subgroup.mem_sup_left (transv_mem_fixer_span hwx 1)
    set z := mat (transv w 1) *ᵥ y with hz
    have hz0 : z ≠ 0 := mulVec_ne_zero _ hy0
    have hQz : qPoint (F ∙ z) ≤ K := by
      rw [hz, ← qPoint_span_map_conj]
      exact map_conj_le_of_mem hQy hfK
    have hopp' : ¬ F ∙ z ≤ perp (F ∙ y) := by
      rw [Submodule.span_singleton_le_iff_mem, mem_perp_span, hz, transv_mulVec, map_add,
        map_smul, form_self, zero_add, smul_eq_mul, one_mul]
      intro h0
      have h1 : form F w y = -form F y w := form_swap y w
      rw [h1, neg_mul, neg_eq_zero] at h0
      exact hwy (mul_self_eq_zero.1 h0)
    exact (qPoint_sup_qPoint_eq_top (isPoint_span hy0) (isPoint_span hz0) hopp').ge.trans
      (sup_le hQy hQz)
  · exact (qPoint_sup_qPoint_eq_top (isPoint_span hx) (isPoint_span hy0) hopp).ge.trans
      (sup_le hQx hQy)

end CFSG.Quasithin.MS93.S59
