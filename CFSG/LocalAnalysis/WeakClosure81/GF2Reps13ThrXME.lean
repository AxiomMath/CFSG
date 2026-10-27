module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXMD
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXMB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXL

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W}

omit [Finite W] in
private theorem w16g_finsum_eq_four {X : Subgroup (MulAut W)}
    (u₁ u₂ c d : s13IsoComps X)
    (h12 : u₁ ≠ u₂) (h1c : u₁ ≠ c) (h1d : u₁ ≠ d)
    (h2c : u₂ ≠ c) (h2d : u₂ ≠ d) (hcd : c ≠ d)
    (f : ↥(s13IsoComps X) → ZMod 3)
    (hf : ∀ U, U ≠ u₁ → U ≠ u₂ → U ≠ c → U ≠ d → f U = 0) :
    ∑ᶠ U, f U = f u₁ + f u₂ + f c + f d := by
  classical
  have hsupp : Function.support f ⊆
      (↑({u₁, u₂, c, d} : Finset ↥(s13IsoComps X)) : Set ↥(s13IsoComps X)) := by
    intro U hU
    simp only [Function.mem_support] at hU
    by_contra hnot
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact hU (hf U hnot.1 hnot.2.1 hnot.2.2.1 hnot.2.2.2)
  rw [finsum_eq_finsetSum_of_support_subset f hsupp]
  have h1 : u₁ ∉ ({u₂, c, d} : Finset ↥(s13IsoComps X)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h12, h1c, h1d⟩
  have h2 : u₂ ∉ ({c, d} : Finset ↥(s13IsoComps X)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h2c, h2d⟩
  have h3 : c ∉ ({d} : Finset ↥(s13IsoComps X)) := by
    simpa using hcd
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3, Finset.sum_singleton]
  ring

theorem w16g_tetra_XD (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    {a : MulAut W} {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} {q r : ↥X}
    {u₁ u₂ c d : s13IsoComps X} (F : TetraFrame A X Q a lam q r u₁ u₂ c d) :
    s13XSupp X {(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} =
      Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W) := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  have hqQ : (q : MulAut W) ∈ Q := by rw [F.hQq]; exact Subgroup.mem_zpowers _
  have hrQa : (r : MulAut W) ∈ Q.map (MulAut.conj a).toMonoidHom := by
    rw [F.hQr]; exact Subgroup.mem_zpowers _
  have hqX : (q : MulAut W) ∈ X := h.hQX hqQ
  have hrX : (r : MulAut W) ∈ X := by
    obtain ⟨qq, hqq, hqqr⟩ := Subgroup.mem_map.mp hrQa
    have hmem : MulAut.conj a qq ∈ X := by
      simpa [MulAut.conj_apply] using h.hXA a F.ha qq (h.hQX hqq)
    have hqqr' : MulAut.conj a qq = (r : MulAut W) := by simpa using hqqr
    rwa [hqqr'] at hmem
  have hmap1 : Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom = Q := by
    rw [show MulAut.conj (1 : MulAut W) = 1 from by ext w; simp]
    exact Subgroup.map_id Q
  have hqx : ∀ x : ↥X,
      ∑ᶠ U : ↥(s13IsoComps X), lam U (Additive.ofMul q) * lam U (Additive.ofMul x) = 0 := by
    intro x
    exact s13_three_orthogonal h hH0 hQ3 he F.hl (1 : MulAut W) A.one_mem q
      (by rw [hmap1]; exact hqQ) x
  have hrx : ∀ x : ↥X,
      ∑ᶠ U : ↥(s13IsoComps X), lam U (Additive.ofMul r) * lam U (Additive.ofMul x) = 0 :=
    fun x => s13_three_orthogonal h hH0 hQ3 he F.hl a F.ha r hrQa x
  let qv : Fin 4 → ZMod 3 :=
    ![lam u₁ (Additive.ofMul q), lam u₂ (Additive.ofMul q), lam c (Additive.ofMul q), 0]
  let rv : Fin 4 → ZMod 3 :=
    ![lam u₁ (Additive.ofMul r), lam u₂ (Additive.ofMul r), 0, lam d (Additive.ofMul r)]
  let yv : ↥X → Fin 4 → ZMod 3 := fun x =>
    ![lam u₁ (Additive.ofMul x), lam u₂ (Additive.ofMul x), lam c (Additive.ofMul x),
      lam d (Additive.ofMul x)]
  have hfour : ∀ (f : ↥(s13IsoComps X) → ZMod 3),
      (∀ U, U ≠ u₁ → U ≠ u₂ → U ≠ c → U ≠ d → f U = 0) →
      ∑ᶠ U, f U = f u₁ + f u₂ + f c + f d :=
    fun f hf => w16g_finsum_eq_four u₁ u₂ c d F.h12 F.h1c F.h1d F.h2c F.h2d F.hcd f hf
  have hq_d : lam d (Additive.ofMul q) = 0 := by
    by_contra hne
    rcases (F.hq d).mp hne with h | h | h
    · exact F.h1d h.symm
    · exact F.h2d h.symm
    · exact F.hcd h.symm
  have hr_c : lam c (Additive.ofMul r) = 0 := by
    by_contra hne
    rcases (F.hr c).mp hne with h | h | h
    · exact F.h1c h.symm
    · exact F.h2c h.symm
    · exact F.hcd h
  have hqrx : ∑ᶠ U : ↥(s13IsoComps X),
      lam U (Additive.ofMul q) * lam U (Additive.ofMul r) =
      lam u₁ (Additive.ofMul q) * lam u₁ (Additive.ofMul r) +
      lam u₂ (Additive.ofMul q) * lam u₂ (Additive.ofMul r) +
      lam c (Additive.ofMul q) * lam c (Additive.ofMul r) +
      lam d (Additive.ofMul q) * lam d (Additive.ofMul r) := by
    refine hfour _ (fun U h1 h2 h3 _ => ?_)
    have hqU : lam U (Additive.ofMul q) = 0 := by
      by_contra hne
      rcases (F.hq U).mp hne with h | h | h
      · exact h1 h
      · exact h2 h
      · exact h3 h
    rw [hqU, zero_mul]
  have horth : qv ⬝ᵥ rv = 0 := by
    have hqr := hqx r
    rw [hqrx] at hqr
    rw [hq_d, zero_mul, add_zero, hr_c, mul_zero, add_zero] at hqr
    have hdot : qv ⬝ᵥ rv =
        lam u₁ (Additive.ofMul q) * lam u₁ (Additive.ofMul r) +
        lam u₂ (Additive.ofMul q) * lam u₂ (Additive.ofMul r) +
        lam c (Additive.ofMul q) * lam c (Additive.ofMul r) +
        lam d (Additive.ofMul q) * lam d (Additive.ofMul r) := by
      simp [qv, rv, dotProduct, Fin.sum_univ_four, hr_c, hq_d]
    rw [hdot, hq_d, zero_mul, add_zero, hr_c, mul_zero, add_zero]
    exact hqr
  have hdot1 : ∀ x : ↥X, qv ⬝ᵥ yv x = 0 := by
    intro x
    have hqvx : qv ⬝ᵥ yv x =
        lam u₁ (Additive.ofMul q) * lam u₁ (Additive.ofMul x) +
        lam u₂ (Additive.ofMul q) * lam u₂ (Additive.ofMul x) +
        lam c (Additive.ofMul q) * lam c (Additive.ofMul x) + 0 := by
      simp [qv, yv, dotProduct, Fin.sum_univ_four]
    rw [hqvx]
    have h4 : ∑ᶠ U : ↥(s13IsoComps X),
        lam U (Additive.ofMul q) * lam U (Additive.ofMul x) =
        lam u₁ (Additive.ofMul q) * lam u₁ (Additive.ofMul x) +
        lam u₂ (Additive.ofMul q) * lam u₂ (Additive.ofMul x) +
        lam c (Additive.ofMul q) * lam c (Additive.ofMul x) + 0 := by
      have hf : ∀ U, U ≠ u₁ → U ≠ u₂ → U ≠ c → U ≠ d →
          lam U (Additive.ofMul q) * lam U (Additive.ofMul x) = 0 := by
        intro U h1 h2 h3 _
        have hqU : lam U (Additive.ofMul q) = 0 := by
          by_contra hne
          rcases (F.hq U).mp hne with h | h | h
          · exact h1 h
          · exact h2 h
          · exact h3 h
        rw [hqU, zero_mul]
      rw [hfour (fun U => lam U (Additive.ofMul q) * lam U (Additive.ofMul x)) hf,
        hq_d, zero_mul]
    rw [← h4, hqx x]
  have hdot2 : ∀ x : ↥X, rv ⬝ᵥ yv x = 0 := by
    intro x
    have hrvx : rv ⬝ᵥ yv x =
        lam u₁ (Additive.ofMul r) * lam u₁ (Additive.ofMul x) +
        lam u₂ (Additive.ofMul r) * lam u₂ (Additive.ofMul x) +
        0 + lam d (Additive.ofMul r) * lam d (Additive.ofMul x) := by
      simp [rv, yv, dotProduct, Fin.sum_univ_four]
    rw [hrvx]
    have h4 : ∑ᶠ U : ↥(s13IsoComps X),
        lam U (Additive.ofMul r) * lam U (Additive.ofMul x) =
        lam u₁ (Additive.ofMul r) * lam u₁ (Additive.ofMul x) +
        lam u₂ (Additive.ofMul r) * lam u₂ (Additive.ofMul x) +
        0 + lam d (Additive.ofMul r) * lam d (Additive.ofMul x) := by
      have hf : ∀ U, U ≠ u₁ → U ≠ u₂ → U ≠ c → U ≠ d →
          lam U (Additive.ofMul r) * lam U (Additive.ofMul x) = 0 := by
        intro U h1 h2 _ h4
        have hrU : lam U (Additive.ofMul r) = 0 := by
          by_contra hne
          rcases (F.hr U).mp hne with h | h | h
          · exact h1 h
          · exact h2 h
          · exact h4 h
        rw [hrU, zero_mul]
      rw [hfour (fun U => lam U (Additive.ofMul r) * lam U (Additive.ofMul x)) hf,
        hr_c, zero_mul]
    rw [← h4, hrx x]
  apply le_antisymm
  · intro x hx
    have hxX : x ∈ X := (mem_s13XSupp.mp hx).1
    let x' : ↥X := ⟨x, hxX⟩
    have hxker : ∀ U : s13IsoComps X,
        (U : Subgroup W) ∉ ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W),
          (d : Subgroup W)} : Set (Subgroup W)) → x ∈ s13KerOn X (U : Subgroup W) :=
      fun U hU => (mem_s13XSupp.mp hx).2 U U.2 hU
    have hxcoord : ∀ U : s13IsoComps X,
        (U : Subgroup W) ∉ ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W),
          (d : Subgroup W)} : Set (Subgroup W)) →
        lam U (Additive.ofMul x') = 0 :=
      fun U hU => ((F.hl U).2 x').mpr (hxker U hU)
    have hcore := w16g_core qv rv (yv x')
      (by simpa [qv] using (F.hq u₁).mpr (Or.inl rfl))
      (by simpa [qv] using (F.hq u₂).mpr (Or.inr (Or.inl rfl)))
      (by simpa [qv] using (F.hq c).mpr (Or.inr (Or.inr rfl)))
      (by simp [qv])
      (by simpa [rv] using (F.hr u₁).mpr (Or.inl rfl))
      (by simpa [rv] using (F.hr u₂).mpr (Or.inr (Or.inl rfl)))
      (by simp [rv])
      (by simpa [rv] using (F.hr d).mpr (Or.inr (Or.inr rfl)))
      horth (hdot1 x') (hdot2 x')
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hcore
    let z' : ↥X := q ^ α.val * r ^ β.val
    have hzU : ∀ U : s13IsoComps X, lam U (Additive.ofMul z') =
        α * lam U (Additive.ofMul q) + β * lam U (Additive.ofMul r) := by
      intro U
      have hz' : Additive.ofMul z' =
          Additive.ofMul (q ^ α.val) + Additive.ofMul (r ^ β.val) := by
        rw [show z' = q ^ α.val * r ^ β.val from rfl, ofMul_mul]
      rw [hz', map_add, ofMul_pow, map_nsmul, ofMul_pow, map_nsmul]
      rw [nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hcoord : ∀ U : s13IsoComps X,
        lam U (Additive.ofMul x') = lam U (Additive.ofMul z') := by
      intro U
      rw [hzU U]
      by_cases hU1 : U = u₁
      · subst hU1
        simpa [qv, rv, yv] using (congrFun hαβ 0).symm
      · by_cases hU2 : U = u₂
        · subst hU2
          simpa [qv, rv, yv] using (congrFun hαβ 1).symm
        · by_cases hUc : U = c
          · subst hUc
            simpa [qv, rv, yv, hr_c] using (congrFun hαβ 2).symm
          · by_cases hUd : U = d
            · subst hUd
              simpa [qv, rv, yv, hq_d] using (congrFun hαβ 3).symm
            · have hUD : (U : Subgroup W) ∉ ({(u₁ : Subgroup W), (u₂ : Subgroup W),
                  (c : Subgroup W), (d : Subgroup W)} : Set (Subgroup W)) := by
                intro hD
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
                rcases hD with h | h | h | h
                · exact hU1 (Subtype.ext h)
                · exact hU2 (Subtype.ext h)
                · exact hUc (Subtype.ext h)
                · exact hUd (Subtype.ext h)
              have hUq : lam U (Additive.ofMul q) = 0 := by
                by_contra hne
                rcases (F.hq U).mp hne with h | h | h
                · exact hU1 h
                · exact hU2 h
                · exact hUc h
              have hUr : lam U (Additive.ofMul r) = 0 := by
                by_contra hne
                rcases (F.hr U).mp hne with h | h | h
                · exact hU1 h
                · exact hU2 h
                · exact hUd h
              rw [hUq, hUr, hxcoord U hUD]
              ring
    have hxz : x' = z' := coord_injective h.hW hp3 hp32 h.hXe F.hl hcoord
    have hx_eq : x = (q : MulAut W) ^ α.val * (r : MulAut W) ^ β.val := by
      have := congrArg (fun y : ↥X => (y : MulAut W)) hxz
      simpa [x', z'] using this
    rw [hx_eq]
    exact Subgroup.mul_mem_sup
      (Subgroup.pow_mem (Subgroup.zpowers (q : MulAut W))
        (Subgroup.mem_zpowers (q : MulAut W)) α.val)
      (Subgroup.pow_mem (Subgroup.zpowers (r : MulAut W))
        (Subgroup.mem_zpowers (r : MulAut W)) β.val)
  · refine sup_le ?_ ?_
    · have hLX : Subgroup.zpowers (q : MulAut W) ≤ X := Subgroup.zpowers_le.mpr hqX
      refine (le_s13XSupp_iff h.hW hp3 hp32 h.hXe hLX).mpr ?_
      rw [← F.hQq, F.hsq]
      intro U hU
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU
      rcases hU with rfl | rfl | rfl <;> simp
    · have hLX : Subgroup.zpowers (r : MulAut W) ≤ X := Subgroup.zpowers_le.mpr hrX
      refine (le_s13XSupp_iff h.hW hp3 hp32 h.hXe hLX).mpr ?_
      rw [← F.hQr, F.hsr]
      intro U hU
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU
      rcases hU with rfl | rfl | rfl <;> simp

end CFSG.LocalAnalysis.WeakClosure81
