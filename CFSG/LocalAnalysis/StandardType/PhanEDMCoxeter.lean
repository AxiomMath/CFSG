module

public import TauCeti.GroupTheory.Coxeter.Parabolic
public import Mathlib.GroupTheory.DoubleCoset

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

@[expose] def IsMinimalDoubleCosetRep (K J : Set B) (ω : W) : Prop :=
  ∀ a ∈ cs.parabolic K, ∀ b ∈ cs.parabolic J, cs.length ω ≤ cs.length (a * ω * b)

theorem exists_isMinimalDoubleCosetRep (K J : Set B) (w : W) :
    ∃ a ∈ cs.parabolic K, ∃ b ∈ cs.parabolic J,
      cs.IsMinimalDoubleCosetRep K J (a * w * b) := by
  classical
  have hex : ∃ n : ℕ, ∃ a ∈ cs.parabolic K, ∃ b ∈ cs.parabolic J,
      cs.length (a * w * b) = n :=
    ⟨_, 1, one_mem _, 1, one_mem _, rfl⟩
  obtain ⟨a, ha, b, hb, hmin⟩ := Nat.find_spec hex
  refine ⟨a, ha, b, hb, fun a' ha' b' hb' => ?_⟩
  rw [hmin]
  have heq : a' * (a * w * b) * b' = (a' * a) * w * (b * b') := by
    simp only [mul_assoc]
  exact Nat.find_le ⟨a' * a, mul_mem ha' ha, b * b', mul_mem hb hb',
    congrArg cs.length heq.symm⟩

variable {cs}

theorem IsMinimalDoubleCosetRep.exists_decomp {K J : Set B} {ω : W}
    (hω : cs.IsMinimalDoubleCosetRep K J ω) {a b : W} (ha : a ∈ cs.parabolic K)
    (hb : b ∈ cs.parabolic J) :
    ∃ a' ∈ cs.parabolic K, ∃ b' ∈ cs.parabolic J, a * ω * b = a' * ω * b' ∧
      cs.length (a * ω * b) = cs.length a' + cs.length ω + cs.length b' := by
  obtain ⟨α, hαred, hαJ, hα⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic ha
  obtain ⟨β, hβred, hβJ, hβ⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hb
  obtain ⟨μ, hμred, hμ⟩ := cs.exists_isReduced ω
  obtain ⟨σ, hσsub, hσred, hσprod⟩ := cs.exists_isReduced_sublist (α ++ μ ++ β)
  obtain ⟨r, β', hσeq, hrsub, hβ'sub⟩ := List.sublist_append_iff.mp hσsub
  obtain ⟨α', μ', hreq, hα'sub, hμ'sub⟩ := List.sublist_append_iff.mp hrsub
  have hσdecomp : σ = α' ++ μ' ++ β' := by rw [hσeq, hreq]
  have hα'mem : cs.wordProd α' ∈ cs.parabolic K :=
    cs.wordProd_mem_parabolic fun i hi => hαJ i (hα'sub.subset hi)
  have hβ'mem : cs.wordProd β' ∈ cs.parabolic J :=
    cs.wordProd_mem_parabolic fun i hi => hβJ i (hβ'sub.subset hi)
  have h1 : cs.wordProd (α ++ μ ++ β) = a * ω * b := by
    rw [cs.wordProd_append, cs.wordProd_append, hα, hβ, hμ.symm]
  have h2 : cs.wordProd (α' ++ μ' ++ β') =
      cs.wordProd α' * cs.wordProd μ' * cs.wordProd β' := by
    rw [cs.wordProd_append, cs.wordProd_append]
  have hmain : a * ω * b = cs.wordProd α' * cs.wordProd μ' * cs.wordProd β' := by
    rw [← h1, ← hσprod, hσdecomp, h2]
  have hmul0 : cs.wordProd μ' =
      (cs.wordProd α')⁻¹ * (a * ω * b) * (cs.wordProd β')⁻¹ := by
    rw [hmain]; group
  have hmul : cs.wordProd μ' =
      ((cs.wordProd α')⁻¹ * a) * ω * (b * (cs.wordProd β')⁻¹) := by
    rw [hmul0]; group
  have hlen_le : cs.length ω ≤ cs.length (cs.wordProd μ') := by
    rw [hmul]
    exact hω _ (mul_mem (inv_mem hα'mem) ha) _ (mul_mem hb (inv_mem hβ'mem))
  have hμlen : cs.length ω = μ.length := by rw [hμ]; exact hμred.eq
  have hlen_ge : cs.length (cs.wordProd μ') ≤ cs.length ω := by
    calc cs.length (cs.wordProd μ') ≤ μ'.length := cs.length_wordProd_le μ'
      _ ≤ μ.length := hμ'sub.length_le
      _ = cs.length ω := hμlen.symm
  have hlen_eq : cs.length (cs.wordProd μ') = cs.length ω := le_antisymm hlen_ge hlen_le
  have hμ'len : μ'.length = μ.length := by
    have h := cs.length_wordProd_le μ'
    have h2 := hμ'sub.length_le
    omega
  have hμ'eq : μ' = μ := hμ'sub.eq_of_length hμ'len
  have hm_eq : cs.wordProd μ' = ω := by rw [hμ'eq]; exact hμ.symm
  have hσπ : cs.wordProd σ = cs.wordProd α' * ω * cs.wordProd β' := by
    rw [hσdecomp, h2, hm_eq]
  have hσlen : σ.length = cs.length (cs.wordProd α' * ω * cs.wordProd β') := by
    rw [← hσred.eq, hσπ]
  have hfinal_eq : a * ω * b = cs.wordProd α' * ω * cs.wordProd β' := by
    rw [hmain, hm_eq]
  refine ⟨cs.wordProd α', hα'mem, cs.wordProd β', hβ'mem, hfinal_eq, le_antisymm ?_ ?_⟩
  · rw [hfinal_eq]
    calc cs.length (cs.wordProd α' * ω * cs.wordProd β')
        ≤ cs.length (cs.wordProd α' * ω) + cs.length (cs.wordProd β') :=
          cs.length_mul_le _ _
      _ ≤ (cs.length (cs.wordProd α') + cs.length ω) + cs.length (cs.wordProd β') := by
          have h := cs.length_mul_le (cs.wordProd α') ω
          omega
  · rw [hfinal_eq]
    calc cs.length (cs.wordProd α') + cs.length ω + cs.length (cs.wordProd β')
        ≤ α'.length + μ.length + β'.length := by
          have hα' := cs.length_wordProd_le α'
          have hβ' := cs.length_wordProd_le β'
          omega
      _ = σ.length := by rw [hσdecomp, List.length_append, List.length_append, hμ'eq]
      _ = cs.length (cs.wordProd α' * ω * cs.wordProd β') := hσlen

theorem IsMinimalDoubleCosetRep.eq_of_eq_mul_mul {K J : Set B} {ω ω' : W}
    (hω : cs.IsMinimalDoubleCosetRep K J ω) (hω' : cs.IsMinimalDoubleCosetRep K J ω') {a b : W}
    (ha : a ∈ cs.parabolic K) (hb : b ∈ cs.parabolic J) (h : ω' = a * ω * b) : ω' = ω := by
  obtain ⟨a', ha', b', hb', heq, hlen⟩ := hω.exists_decomp ha hb
  have hωeq : ω = a⁻¹ * ω' * b⁻¹ := by rw [h]; group
  have hle : cs.length ω' ≤ cs.length ω := by
    calc cs.length ω' ≤ cs.length (a⁻¹ * ω' * b⁻¹) :=
          hω' a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)
      _ = cs.length ω := by rw [← hωeq]
  have hlen' : cs.length ω' = cs.length a' + cs.length ω + cs.length b' := by
    rw [h]; exact hlen
  have ha'0 : cs.length a' = 0 := by omega
  have hb'0 : cs.length b' = 0 := by omega
  rw [h, heq, cs.length_eq_zero_iff.mp ha'0, cs.length_eq_zero_iff.mp hb'0, one_mul, mul_one]

variable (cs)

theorem isMinimalDoubleCosetRep_iff {K J : Set B} {ω : W} :
    cs.IsMinimalDoubleCosetRep K J ω ↔
      (∀ j ∈ J, ¬ cs.IsRightDescent ω j) ∧ ∀ k ∈ K, ¬ cs.IsLeftDescent ω k := by
  constructor
  · intro hω
    constructor
    · intro j hj hdesc
      have h := hω 1 (one_mem _) (cs.simple j) (cs.simple_mem_parabolic hj)
      rw [one_mul] at h
      have hlt : cs.length (ω * cs.simple j) < cs.length ω := hdesc
      omega
    · intro k hk hdesc
      have h := hω (cs.simple k) (cs.simple_mem_parabolic hk) 1 (one_mem _)
      rw [mul_one] at h
      have hlt : cs.length (cs.simple k * ω) < cs.length ω := hdesc
      omega
  · rintro ⟨hr, hl⟩
    obtain ⟨a₀, ha₀, b₀, hb₀, hω₀⟩ := cs.exists_isMinimalDoubleCosetRep K J ω
    obtain ⟨a', ha', b', hb', heq, hlen⟩ := hω₀.exists_decomp (inv_mem ha₀) (inv_mem hb₀)
    have hωdecomp : ω = a' * (a₀ * ω * b₀) * b' :=
      (show ω = a₀⁻¹ * (a₀ * ω * b₀) * b₀⁻¹ by group).trans heq
    have hlen' : cs.length ω = cs.length a' + cs.length (a₀ * ω * b₀) + cs.length b' :=
      (congrArg cs.length (show ω = a₀⁻¹ * (a₀ * ω * b₀) * b₀⁻¹ by group)).trans hlen
    have ha'1 : a' = 1 := by
      by_contra ha'ne
      obtain ⟨k, hk, hkdesc⟩ := cs.exists_rightDescent_mem_of_mem_parabolic_of_ne_one
        (inv_mem ha') (inv_ne_one.mpr ha'ne)
      have hkleft : cs.IsLeftDescent a' k := cs.isRightDescent_inv_iff.mp hkdesc
      refine (hl k hk) ?_
      have hle : cs.length (cs.simple k * ω) ≤ cs.length (cs.simple k * a') +
          cs.length (a₀ * ω * b₀) + cs.length b' := by
        conv_lhs => rw [hωdecomp]
        rw [← mul_assoc, ← mul_assoc]
        calc cs.length (((cs.simple k * a') * (a₀ * ω * b₀)) * b')
            ≤ cs.length ((cs.simple k * a') * (a₀ * ω * b₀)) + cs.length b' :=
              cs.length_mul_le _ _
          _ ≤ (cs.length (cs.simple k * a') + cs.length (a₀ * ω * b₀)) +
                cs.length b' := by
              have h := cs.length_mul_le (cs.simple k * a') (a₀ * ω * b₀)
              omega
      have hlt : cs.length (cs.simple k * a') + cs.length (a₀ * ω * b₀) + cs.length b' <
          cs.length ω := by
        rw [hlen']
        have hk' := cs.isLeftDescent_iff.mp hkleft
        omega
      exact lt_of_le_of_lt hle hlt
    have hb'1 : b' = 1 := by
      by_contra hb'ne
      obtain ⟨j, hj, hjdesc⟩ := cs.exists_rightDescent_mem_of_mem_parabolic_of_ne_one hb' hb'ne
      refine (hr j hj) ?_
      have hle : cs.length (ω * cs.simple j) ≤ cs.length a' +
          cs.length (a₀ * ω * b₀) + cs.length (b' * cs.simple j) := by
        conv_lhs => rw [hωdecomp]
        calc cs.length ((a' * (a₀ * ω * b₀) * b') * cs.simple j)
            = cs.length ((a' * (a₀ * ω * b₀)) * (b' * cs.simple j)) := by
              congr 1; group
          _ ≤ cs.length (a' * (a₀ * ω * b₀)) + cs.length (b' * cs.simple j) :=
              cs.length_mul_le _ _
          _ ≤ (cs.length a' + cs.length (a₀ * ω * b₀)) + cs.length (b' * cs.simple j) := by
              have h := cs.length_mul_le a' (a₀ * ω * b₀)
              omega
      have hlt : cs.length a' + cs.length (a₀ * ω * b₀) + cs.length (b' * cs.simple j) <
          cs.length ω := by
        rw [hlen']
        have hj' := cs.isRightDescent_iff.mp hjdesc
        omega
      exact lt_of_le_of_lt hle hlt
    have hωeq₀ : ω = a₀ * ω * b₀ := by
      calc ω = a' * (a₀ * ω * b₀) * b' := hωdecomp
        _ = a₀ * ω * b₀ := by rw [ha'1, hb'1, one_mul, mul_one]
    rwa [← hωeq₀] at hω₀

theorem eq_of_forall_ascent {J : Set B} {u v : W}
    (hul : ∀ j ∈ J, cs.length (cs.simple j * u) = cs.length u + 1)
    (hur : ∀ j ∈ J, cs.length (u * cs.simple j) = cs.length u + 1)
    (hvl : ∀ j ∈ J, cs.length (cs.simple j * v) = cs.length v + 1)
    (hvr : ∀ j ∈ J, cs.length (v * cs.simple j) = cs.length v + 1)
    (h : v ∈ DoubleCoset.doubleCoset u (cs.parabolic J) (cs.parabolic J)) : u = v := by
  have hmin_u : cs.IsMinimalDoubleCosetRep J J u :=
    cs.isMinimalDoubleCosetRep_iff.mpr
      ⟨fun j hj => cs.not_isRightDescent_iff.mpr (hur j hj),
       fun k hk => cs.not_isLeftDescent_iff.mpr (hul k hk)⟩
  have hmin_v : cs.IsMinimalDoubleCosetRep J J v :=
    cs.isMinimalDoubleCosetRep_iff.mpr
      ⟨fun j hj => cs.not_isRightDescent_iff.mpr (hvr j hj),
       fun k hk => cs.not_isLeftDescent_iff.mpr (hvl k hk)⟩
  obtain ⟨x, hx, y, hy, huv⟩ := DoubleCoset.mem_doubleCoset.mp h
  exact (hmin_u.eq_of_eq_mul_mul hmin_v hx hy huv).symm

theorem length_le_of_forall_ascent {J : Set B} {u v : W}
    (hul : ∀ j ∈ J, cs.length (cs.simple j * u) = cs.length u + 1)
    (hur : ∀ j ∈ J, cs.length (u * cs.simple j) = cs.length u + 1)
    (hv : v ∈ DoubleCoset.doubleCoset u (cs.parabolic J) (cs.parabolic J)) :
    cs.length u ≤ cs.length v := by
  have hmin_u : cs.IsMinimalDoubleCosetRep J J u :=
    cs.isMinimalDoubleCosetRep_iff.mpr
      ⟨fun j hj => cs.not_isRightDescent_iff.mpr (hur j hj),
       fun k hk => cs.not_isLeftDescent_iff.mpr (hul k hk)⟩
  obtain ⟨x, hx, y, hy, huv⟩ := DoubleCoset.mem_doubleCoset.mp hv
  rw [huv]
  exact hmin_u x hx y hy

end CoxeterSystem

end
