module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKS9Rep
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Chain3
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Chain4

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.L829N CFSG.RankThree.SubgroupLists

theorem nk_s9_kantor (hSch : NKLeafSchurL32) (hSL3 : NKLeafSL3Rep)
    (hConj : ∀ (X : Type) [Group X], IsPSL 3 2 1 X → ∀ a b : X, orderOf a = 2 → orderOf b = 2 →
      IsConj a b)
    {E : Type} [Field E] [Finite E] [CharP E 2] (hE2 : Nat.card E = 2 ∨ Nat.card E = 4) {d : ℕ}
    (t : GL (Fin d) E) (ht : IsTransvectionK t) (K₀ N : Subgroup (GL (Fin d) E))
    (hN : N = Subgroup.closure {x | ∃ k ∈ K₀, x = k * t * k⁻¹}) (hKN : K₀ ≤ N) (htN : t ∈ N)
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B)
    (hirrN : CFSG.RankThree.SubgroupLists.IsIrreducibleOn (s9cRep hA hB).range)
    (hτ : IsTransvectionK (s9cRep hA hB ⟨t, htN⟩))
    {Ks : Type} [Group Ks] (hKs3 : IsPSL 3 2 1 Ks) (σ : K₀ →* Ks) (hσ : Function.Surjective σ)
    (hkerρ : ((s9cRep hA hB).comp (Subgroup.inclusion hKN)).ker ≤ σ.ker)
    (hK₀perf : commutator ↥K₀ = ⊤)
    (hnormN : ∀ g ∈ N, ∀ k ∈ K₀, g * k * g⁻¹ ∈ K₀ ∧ g⁻¹ * k * g ∈ K₀)
    (hQ : ∃ Q : Subgroup (GL (Fin d) E), Q ≤ K₀ ∧ (∀ q ∈ Q, ∃ m : ℕ, q ^ 2 ^ m = 1) ∧
      (∀ q ∈ Q, ∀ x ∈ K₀, x * q * x⁻¹ ∈ Q) ∧ (∀ q ∈ Q, t * q * t⁻¹ ∈ Q) ∧
      (∃ k₀ ∈ K₀, ∀ x ∈ K₀, ∃ q ∈ Q, t * x * t⁻¹ = q * (k₀ * x * k₀⁻¹)) ∧
      (∀ z : ↥K₀, σ z = 1 → ∀ x ∈ K₀, ∃ q ∈ Q, (z : GL (Fin d) E) * x * (z : GL (Fin d) E)⁻¹ =
        q * x)) :
    ∃ hn : Module.finrank E (s9cSub A B) = 3,
      ∃ P : GL (Fin (Module.finrank E (s9cSub A B))) E,
        ∀ g : GL (Fin (Module.finrank E (s9cSub A B))) E, g ∈ (s9cRep hA hB).range ↔
          P * g * P⁻¹ ∈ (s9cJ (E := E) hn).range := by
  classical
  obtain ⟨Q, hQK, hQ2, hQK₀, hQt, ⟨k₀, hk₀, hvin⟩, hcen⟩ := hQ
  set ρN := s9cRep hA hB with hρN
  have hts : t * t = 1 := nk_transvection_sq ht
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right hts
  have hQN : ∀ g ∈ N, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q ∧ g⁻¹ * q * g ∈ Q := by
    intro g hg
    rw [hN] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      intro q hq
      have h1 : k⁻¹ * q * k ∈ Q := by
        have := hQK₀ q hq k⁻¹ (K₀.inv_mem hk)
        simpa using this
      have h2 := hQt _ h1
      have h3 := hQK₀ _ h2 k hk
      have e : k * t * k⁻¹ * q * (k * t * k⁻¹)⁻¹ = k * (t * (k⁻¹ * q * k) * t⁻¹) * k⁻¹ := by
        group
      have hconj : (k * t * k⁻¹)⁻¹ = k * t * k⁻¹ := by
        calc (k * t * k⁻¹)⁻¹ = k * t⁻¹ * k⁻¹ := by group
          _ = k * t * k⁻¹ := by rw [ht']
      refine ⟨by rw [e]; exact h3, ?_⟩
      have e1 : (k * t * k⁻¹)⁻¹ * q * (k * t * k⁻¹) = k * t * k⁻¹ * q * (k * t * k⁻¹)⁻¹ := by
        rw [hconj]
      rw [e1, e]
      exact h3
    | one =>
      intro q hq
      exact ⟨by simpa using hq, by simpa using hq⟩
    | mul a b _ _ ha hb =>
      intro q hq
      refine ⟨?_, ?_⟩
      · have h1 := (ha _ (hb q hq).1).1
        have e : a * b * q * (a * b)⁻¹ = a * (b * q * b⁻¹) * a⁻¹ := by group
        rw [e]
        exact h1
      · have h1 := (hb _ (ha q hq).2).2
        have e : (a * b)⁻¹ * q * (a * b) = b⁻¹ * (a⁻¹ * q * a) * b := by group
        rw [e]
        exact h1
    | inv a _ ha =>
      intro q hq
      refine ⟨?_, ?_⟩
      · have := (ha q hq).2
        simpa using this
      · have := (ha q hq).1
        simpa using this
  have hQN' : ∀ q ∈ Q, q ∈ N := fun q hq => hKN (hQK hq)
  let R : Subgroup (GL (Fin (Module.finrank E (s9cSub A B))) E) := (Q.subgroupOf N).map ρN
  have hRp : IsPGroup 2 R := by
    intro g
    obtain ⟨q, hq, hqg⟩ := Subgroup.mem_map.mp g.2
    obtain ⟨m, hm⟩ := hQ2 q.1 (Subgroup.mem_subgroupOf.mp hq)
    refine ⟨m, Subtype.ext ?_⟩
    have h1 : q ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
    show (g : GL (Fin (Module.finrank E (s9cSub A B))) E) ^ 2 ^ m = 1
    rw [← hqg, ← map_pow, h1, map_one]
  have hRnorm : ∀ g ∈ ρN.range, ∀ r ∈ R, g⁻¹ * r * g ∈ R := by
    rintro _ ⟨g₀, rfl⟩ r hr
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hr
    refine Subgroup.mem_map.mpr ⟨g₀⁻¹ * q * g₀, ?_, by simp [map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf]
    have := (hQN g₀.1 g₀.2 q.1 (Subgroup.mem_subgroupOf.mp hq)).2
    simpa using this
  have hRbot : R = ⊥ := nk_two_group_trivial ρN.range R hirrN hRp hRnorm
  have hQtriv : ∀ q : N, (q : GL (Fin d) E) ∈ Q → ρN q = 1 := by
    intro q hq
    have : ρN q ∈ R := Subgroup.mem_map.mpr ⟨q, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rw [hRbot, Subgroup.mem_bot] at this
    exact this
  set ρK : K₀ →* GL (Fin (Module.finrank E (s9cSub A B))) E :=
    ρN.comp (Subgroup.inclusion hKN) with hρK
  have hKbN : ρK.range ≤ ρN.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x, hKN x.2⟩, rfl⟩
  have hinner : ∃ kb ∈ ρK.range, ∀ x ∈ ρK.range,
      ρN ⟨t, htN⟩ * x * (ρN ⟨t, htN⟩)⁻¹ = kb * x * kb⁻¹ := by
    refine ⟨ρK ⟨k₀, hk₀⟩, ⟨⟨k₀, hk₀⟩, rfl⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    obtain ⟨q, hq, hqe⟩ := hvin x x.2
    have hqN : q ∈ N := hQN' q hq
    have e : (⟨t, htN⟩ : N) * ⟨x, hKN x.2⟩ * (⟨t, htN⟩ : N)⁻¹ =
        ⟨q, hqN⟩ * (⟨k₀, hKN hk₀⟩ * ⟨x, hKN x.2⟩ * ⟨k₀, hKN hk₀⟩⁻¹) :=
      Subtype.ext (by simpa using hqe)
    have := congrArg ρN e
    simp only [map_mul, map_inv, hQtriv ⟨q, hqN⟩ hq, one_mul] at this
    exact this
  have hnormal : ∀ g ∈ ρN.range, ∀ k ∈ ρK.range, g * k * g⁻¹ ∈ ρK.range := by
    rintro _ ⟨m, rfl⟩ _ ⟨x, rfl⟩
    refine ⟨⟨(m : GL (Fin d) E) * (x : GL (Fin d) E) * (m : GL (Fin d) E)⁻¹,
      (hnormN m.1 m.2 x.1 x.2).1⟩, ?_⟩
    have hmem : (m : GL (Fin d) E) * (x : GL (Fin d) E) * (m : GL (Fin d) E)⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem m.2 (hKN x.2)) (N.inv_mem m.2)
    have e : (⟨(m : GL (Fin d) E) * (x : GL (Fin d) E) * (m : GL (Fin d) E)⁻¹, hmem⟩ : N) =
        m * ⟨(x : GL (Fin d) E), hKN x.2⟩ * m⁻¹ := by
      apply Subtype.ext
      simp [mul_assoc]
    show ρN ⟨(m : GL (Fin d) E) * (x : GL (Fin d) E) * (m : GL (Fin d) E)⁻¹, hmem⟩ =
      ρN m * ρN ⟨(x : GL (Fin d) E), hKN x.2⟩ * (ρN m)⁻¹
    rw [e, map_mul, map_mul, map_inv]
  have hgenK : ρN.range = Subgroup.closure
      {x | ∃ k ∈ ρK.range, x = k * ρN ⟨t, htN⟩ * k⁻¹} := by
    apply le_antisymm
    · have key : ∀ g ∈ Subgroup.closure {x : GL (Fin d) E | ∃ k ∈ K₀, x = k * t * k⁻¹},
          ∃ hgN : g ∈ N, ρN ⟨g, hgN⟩ ∈ Subgroup.closure
            {s | ∃ k ∈ ρK.range, s = k * ρN ⟨t, htN⟩ * k⁻¹} := by
        intro g hg
        induction hg using Subgroup.closure_induction with
        | mem x hx =>
          obtain ⟨k, hk, rfl⟩ := hx
          have hxN : k * t * k⁻¹ ∈ N := by
            rw [hN]; exact Subgroup.subset_closure ⟨k, hk, rfl⟩
          refine ⟨hxN, Subgroup.subset_closure ⟨ρN ⟨k, hKN hk⟩, ⟨⟨k, hk⟩, rfl⟩, ?_⟩⟩
          have e : (⟨k * t * k⁻¹, hxN⟩ : N) = ⟨k, hKN hk⟩ * ⟨t, htN⟩ * ⟨k, hKN hk⟩⁻¹ := by
            apply Subtype.ext
            simp [mul_assoc]
          rw [e, map_mul, map_mul, map_inv]
        | one =>
          refine ⟨N.one_mem, ?_⟩
          have e : (⟨1, N.one_mem⟩ : N) = 1 := rfl
          rw [e, map_one]
          exact Subgroup.one_mem _
        | mul x y _ _ hx hy =>
          obtain ⟨h1, c1⟩ := hx
          obtain ⟨h2, c2⟩ := hy
          refine ⟨N.mul_mem h1 h2, ?_⟩
          have e : (⟨x * y, N.mul_mem h1 h2⟩ : N) = ⟨x, h1⟩ * ⟨y, h2⟩ := rfl
          rw [e, map_mul]
          exact Subgroup.mul_mem _ c1 c2
        | inv x _ hx =>
          obtain ⟨h1, c1⟩ := hx
          refine ⟨N.inv_mem h1, ?_⟩
          have e : (⟨x⁻¹, N.inv_mem h1⟩ : N) = ⟨x, h1⟩⁻¹ := rfl
          rw [e, map_inv]
          exact Subgroup.inv_mem _ c1
      rintro g ⟨h, rfl⟩
      obtain ⟨_, hC⟩ := key h.1 (by rw [← hN]; exact h.2)
      exact hC
    · rw [Subgroup.closure_le]
      rintro s ⟨x, hx, rfl⟩
      have hτ' : ρN ⟨t, htN⟩ ∈ ρN.range := MonoidHom.mem_range.mpr ⟨⟨t, htN⟩, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hKbN hx) hτ') (Subgroup.inv_mem _ (hKbN hx))
  have hsurjR : Function.Surjective ρK.rangeRestrict := MonoidHom.rangeRestrict_surjective ρK
  have hperfb : commutator ↥ρK.range = ⊤ := by
    have key : (commutator ↥K₀).map ρK.rangeRestrict = commutator ↥ρK.range := by
      rw [commutator_def K₀, commutator_def ρK.range, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hsurjR]
    rw [← key, hK₀perf]
    exact Subgroup.map_top_of_surjective _ hsurjR
  have hkerR : ρK.rangeRestrict.ker ≤ σ.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hkerρ
  let πb : ↥ρK.range →* Ks := (MonoidHom.liftOfSurjective ρK.rangeRestrict hsurjR) ⟨σ, hkerR⟩
  have hπapply : ∀ x : K₀, πb (ρK.rangeRestrict x) = σ x := by
    intro x
    simp [πb, MonoidHom.liftOfSurjective]
  have hπsurj : Function.Surjective πb := by
    intro y
    obtain ⟨x, hx⟩ := hσ y
    exact ⟨ρK.rangeRestrict x, by rw [hπapply, hx]⟩
  have hcenK : ∀ z : ↥ρK.range, πb z = 1 → ∀ x : ↥ρK.range, x * z = z * x := by
    intro z hz x'
    obtain ⟨z₀, rfl⟩ := hsurjR z
    obtain ⟨x₀, rfl⟩ := hsurjR x'
    rw [hπapply] at hz
    obtain ⟨q, hq, hqe⟩ := hcen z₀ hz x₀ x₀.2
    have hqN : q ∈ N := hQN' q hq
    have e : (⟨(z₀ : GL (Fin d) E), hKN z₀.2⟩ : N) * ⟨x₀, hKN x₀.2⟩ *
        (⟨(z₀ : GL (Fin d) E), hKN z₀.2⟩ : N)⁻¹ = ⟨q, hqN⟩ * ⟨x₀, hKN x₀.2⟩ :=
      Subtype.ext (by simpa using hqe)
    have := congrArg ρN e
    simp only [map_mul, map_inv, hQtriv ⟨q, hqN⟩ hq, one_mul] at this
    apply Subtype.ext
    simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict]
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  obtain ⟨hn, P, hP⟩ := nk_s9_replacement hSch hSL3 hConj hE2 ρK.range ρN.range hKbN hnormal
    hirrN (ρN ⟨t, htN⟩) hτ (MonoidHom.mem_range.mpr ⟨⟨t, htN⟩, rfl⟩) hgenK hinner hKs3 πb
    hπsurj hperfb hcenK
  refine ⟨hn, P, fun g => ?_⟩
  rw [hP g, MonoidHom.mem_range]
  constructor
  · rintro ⟨M, hdet, hM⟩
    exact ⟨⟨M, hdet⟩, Units.ext ((s9cJ_val hn ⟨M, hdet⟩).trans hM.symm)⟩
  · rintro ⟨M', hM'⟩
    refine ⟨M'.1, M'.2, ?_⟩
    have := congrArg (fun x : GL (Fin (Module.finrank E (s9cSub A B))) E =>
      (x : Matrix (Fin (Module.finrank E (s9cSub A B))) (Fin (Module.finrank E (s9cSub A B))) E)) hM'
    simp only [s9cJ_val] at this
    exact this.symm

end CFSG.Quasithin.H13.L829NK
