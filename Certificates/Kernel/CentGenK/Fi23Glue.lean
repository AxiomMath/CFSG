module

public import Certificates.Kernel.CentGenK.Fi23
public import Certificates.Kernel.SlpRelC.Fi23Glue
public import CFSG.Certificates.Kernel.SlpGMem

public section

namespace CertificateChecks.KernelCentGenK.Fi23

open CFSG.KC.Enum CFSG.KS.SlpRel CFSG.KS.Mat3 CFSG.KD.Fi23M CFSG.Sporadic.Fi23
open CertificateChecks.KernelSlpRel (Fi23Rep fi23Rep_mul fi23Rep_one fi23_hinit)

theorem fiCgK_conj {m3 : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat} {mt : Nat → Nat}
    {lo₀ ci₀ rm₀ one₀ : Nat} {nz : Nat → Nat → Bool} {prog : List (List Nat)}
    {ps : List (List Nat × List Nat)} {ne : List Nat}
    (h : (strictB lo₀ fun lo => strictB ci₀ fun ci => strictB rm₀ fun rm => strictB one₀ fun one =>
      strictB (mt (nat_lit 0)) fun a => strictB (mt (nat_lit 1)) fun b =>
        CFSG.KC.SlpRel.slpRelK strictB (m3 (nat_lit 253) (nat_lit 64009) lo ci rm) one Nat.beq
          (nz one) [a, b] prog ps ne) = true) :
    CFSG.KC.SlpRel.slpRelK strictB (m3 (nat_lit 253) (nat_lit 64009) lo₀ ci₀ rm₀) one₀ Nat.beq
      (nz one₀) [mt (nat_lit 0), mt (nat_lit 1)] prog ps ne = true := by
  simp only [strictB_eq] at h
  exact h

theorem pa_length : 2 + pa.length ≤ Nat.add r1 3 := by decide +kernel

theorem is_lt : is1 - 1 < 2 + pa.length ∧ is2 - 1 < 2 + pa.length := by decide +kernel

theorem ra_rb_gt : Nat.add r1 3 < ra ∧ Nat.add r1 3 < rb := by decide +kernel

theorem pb_letters : ∀ w ∈ pb, ∀ l ∈ w, l ∈ [is1, is2] ∨ Nat.add r1 3 < l := by decide +kernel

section Model

variable {G : Type*} [Group G] {φ : G →* Matrix (Fin 253) (Fin 253) (ZMod 3)}

theorem fiNeOne_spec {X : Nat} {g : G} (hX : Fi23Rep φ X g) (h : fiNeOne ONE X = true) :
    g ≠ 1 := by
  rintro rfl
  exact CertificateChecks.KernelFi23M.ne_one hX.1 h (by rw [hX.2, map_one])

theorem fi23_cg_of_seeds (hφ : Function.Injective φ) {gA gB : G}
    (hA : mat3 253 64009 (RB 1) = φ gA) (hB : mat3 253 64009 (RB 2) = φ gB) :
    ∃ e f s₁ s₂ : G, gA ∈ Subgroup.closure ({s₁, s₂} : Set G) ∧
      gB ∈ Subgroup.closure ({s₁, s₂} : Set G) ∧ e ^ 5 = 1 ∧ f ^ 5 = 1 ∧ e * f = f * e ∧
      e ≠ 1 ∧ (∀ k < 5, f ≠ e ^ k) ∧ s₁ * e = e * s₁ ∧ s₂ * f = f * s₂ := by
  have h := ch17254_ok
  unfold fiCgK at h
  have hc := fiCgK_conj (m3 := CFSG.KC.Ord.mul3s) (mt := MT) (lo₀ := LO) (ci₀ := CI) (rm₀ := RM)
    (one₀ := ONE) (nz := fiNeOne) h
  obtain ⟨hp, hn⟩ := slpRelK_sound (Rep := Fi23Rep φ) (frc := strictB)
    (mul := CFSG.KC.Ord.mul3s (nat_lit 253) (nat_lit 64009) LO CI RM) (one := ONE) (eq := Nat.beq)
    (nz := fiNeOne ONE) (init := [MT 0, MT 1]) (gens := [gA, gB])
    (fun _ _ _ _ hX hY => fi23Rep_mul hX hY) fi23Rep_one strictB_eq
    (fun _ _ _ _ hX hY e => hφ (by rw [← hX.2, ← hY.2, Nat.eq_of_beq_eq_true e]))
    (fun _ _ hX hz => fiNeOne_spec hX hz) (fi23_hinit hA hB) hc
  have hsplit : slpG prog [gA, gB] = slpG pb (slpG pa [gA, gB]) := slpG_append pa pb _
  generalize hR : slpG prog [gA, gB] = R at hp hn hsplit
  have P : ∀ u v, (u, v) ∈ ps →
      (u.map fun l => R.getD (l - 1) 1).prod = (v.map fun l => R.getD (l - 1) 1).prod :=
    fun u v huv => hp (u, v) huv
  have N : ∀ l ∈ ne, R.getD (l - 1) 1 ≠ 1 := hn
  set r : ℕ → G := fun l => R.getD (l - 1) 1 with hr
  have h1 : r 1 = gA := by
    change R.getD (1 - 1) 1 = gA
    rw [hsplit, slpG_getD_lt _ _ (by rw [slpG_length]; simp only [List.length_cons, List.length_nil]; omega),
      slpG_getD_lt _ _ (by simp)]
    rfl
  have h2 : r 2 = gB := by
    change R.getD (2 - 1) 1 = gB
    rw [hsplit, slpG_getD_lt _ _ (by rw [slpG_length]; simp only [List.length_cons, List.length_nil]; omega),
      slpG_getD_lt _ _ (by simp)]
    rfl
  have pe5 := P [ie, ie, ie, ie, ie] [] (by simp [ps])
  have pf5 := P [jf, jf, jf, jf, jf] [] (by simp [ps])
  have pef := P [ie, jf] [jf, ie] (by simp [ps])
  have p1 := P [is1, ie] [ie, is1] (by simp [ps])
  have p2 := P [is2, jf] [jf, is2] (by simp [ps])
  have c1 := P [r1] [jf, ie] (by simp [ps])
  have c2 := P [Nat.add r1 1] [r1, ie] (by simp [ps])
  have c3 := P [Nat.add r1 2] [Nat.add r1 1, ie] (by simp [ps])
  have c4 := P [Nat.add r1 3] [Nat.add r1 2, ie] (by simp [ps])
  have pa' := P [ra] [1] (by simp [ps])
  have pb' := P [rb] [2] (by simp [ps])
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at pe5 pf5 pef
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at p1 p2 c1 c2
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at c3 c4 pa' pb'
  have he5 : r ie ^ 5 = 1 := by
    rw [← pe5]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hf5 : r jf ^ 5 = 1 := by
    rw [← pf5]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have ne1 : r ie ≠ 1 := N ie (by simp [ne])
  have nf : r jf ≠ 1 := N jf (by simp [ne])
  have n4 : r (Nat.add r1 3) ≠ 1 := N _ (by simp [ne])
  have n3 : r (Nat.add r1 2) ≠ 1 := N _ (by simp [ne])
  have n2 : r (Nat.add r1 1) ≠ 1 := N _ (by simp [ne])
  have n1 : r r1 ≠ 1 := N _ (by simp [ne])
  have hfe : ∀ k < 5, r jf ≠ r ie ^ k := by
    intro k hk hfk
    have e5k : r jf * r ie ^ (5 - k) = 1 := by
      rw [hfk, ← pow_add, Nat.add_sub_cancel' hk.le, he5]
    interval_cases k
    · exact nf (by simpa using hfk)
    · apply n4
      rw [c4, c3, c2, c1, ← e5k]
      simp only [Nat.reduceSub, pow_succ, pow_zero, one_mul, mul_assoc]
    · apply n3
      rw [c3, c2, c1, ← e5k]
      simp only [Nat.reduceSub, pow_succ, pow_zero, one_mul, mul_assoc]
    · apply n2
      rw [c2, c1, ← e5k]
      simp only [Nat.reduceSub, pow_succ, pow_zero, one_mul, mul_assoc]
    · apply n1
      rw [c1, ← e5k]
      simp only [Nat.reduceSub, pow_succ, pow_zero, one_mul, mul_assoc]
  have hmem : ∀ l, Nat.add r1 3 < l → r l ∈ Subgroup.closure ({r is1, r is2} : Set G) := by
    intro l hl
    have := slpG_mem (Subgroup.closure ({r is1, r is2} : Set G)) [is1, is2] (Nat.add r1 3) pb
      (slpG pa [gA, gB]) pb_letters (fun m hm => ?_) l (Or.inr hl)
    · change R.getD (l - 1) 1 ∈ _
      rw [hsplit]
      exact this
    rcases hm with hm | hm
    · have hlen : (slpG pa [gA, gB]).length = 2 + pa.length := by
        rw [slpG_length]
        simp [Nat.add_comm]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · have e : (slpG pa [gA, gB]).getD (is1 - 1) 1 = r is1 := by
          change _ = R.getD (is1 - 1) 1
          rw [hsplit, slpG_getD_lt pb (slpG pa [gA, gB]) (by rw [hlen]; exact is_lt.1)]
        rw [e]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · have e : (slpG pa [gA, gB]).getD (is2 - 1) 1 = r is2 := by
          change _ = R.getD (is2 - 1) 1
          rw [hsplit, slpG_getD_lt pb (slpG pa [gA, gB]) (by rw [hlen]; exact is_lt.2)]
        rw [e]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [List.getD_eq_default _ _ (by rw [slpG_length]; simp; have := pa_length; omega)]
      exact Subgroup.one_mem _
  refine ⟨r ie, r jf, r is1, r is2, ?_, ?_, he5, hf5, pef, ne1, hfe, p1, p2⟩
  · have := hmem ra ra_rb_gt.1
    rwa [pa', h1] at this
  · have := hmem rb ra_rb_gt.2
    rwa [pb', h2] at this

end Model

section Concrete


theorem fi23_cg_exists :
    ∃ e f s₁ s₂ : GL (Fin 253) (ZMod 3), Subgroup.closure {s₁, s₂} = J ∧ e ∈ J ∧ f ∈ J ∧
      e ^ 5 = 1 ∧ f ^ 5 = 1 ∧ e * f = f * e ∧ e ≠ 1 ∧ (∀ k < 5, f ≠ e ^ k) ∧
      s₁ * e = e * s₁ ∧ s₂ * f = f * s₂ := by
  obtain ⟨e, f, s₁, s₂, ha, hb, he, hf, hef, he1, hfe, h₁, h₂⟩ :=
    fi23_cg_of_seeds KernelSlpRel.fi23Hom_injective KernelSlpRel.fi23Hom_a
      KernelSlpRel.fi23Hom_b
  have hs : Subgroup.closure ({s₁, s₂} : Set J) = ⊤ := by
    rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ha
    · exact hb
  refine ⟨e, f, s₁, s₂, ?_, e.2, f.2, by simpa using congrArg Subtype.val he,
    by simpa using congrArg Subtype.val hf, by simpa using congrArg Subtype.val hef,
    fun h => he1 (Subtype.ext (by simpa using h)),
    fun k hk h => hfe k hk (Subtype.ext (by simpa using h)),
    by simpa using congrArg Subtype.val h₁, by simpa using congrArg Subtype.val h₂⟩
  have hm := congrArg (Subgroup.map J.subtype) hs
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    Set.image_pair] at hm
  exact hm

end Concrete

end CertificateChecks.KernelCentGenK.Fi23

end
