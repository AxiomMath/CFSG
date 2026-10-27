module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

variable {G : Type _} [Group G] (p : ℕ) (S : Sylow p G)

/-- The focal subgroup `F` as defined in Theorem 1.17. -/
def CFSG.feitThompsonFocalSubgroup : Subgroup G :=
  Subgroup.closure {z : G | ∃ x : G, x ∈ (S : Subgroup G) ∧ ∃ y : G, y ∈ (S : Subgroup G) ∧
    IsConj x y ∧ z = x⁻¹ * y}

/-- The focal subgroup is contained in the Sylow subgroup `S`. -/
lemma CFSG.focalSubgroup_le_sylow : feitThompsonFocalSubgroup p S ≤ (S : Subgroup G) := by
  unfold feitThompsonFocalSubgroup
  apply (Subgroup.closure_le (K := (S : Subgroup G))).2
  intro z hz
  rcases hz with ⟨x, hx, y, hy, _, rfl⟩
  exact (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hx) hy

/-- Conjugation preserves the relation `IsConj`. -/
lemma CFSG.isConj_conj {x y : G} (h : IsConj x y) (g : G) : IsConj (g * x * g⁻¹) (g * y * g⁻¹) := by
  rcases isConj_iff.1 h with ⟨c, hc⟩
  refine isConj_iff.2 ⟨g * c * g⁻¹, ?_⟩
  calc
    (g * c * g⁻¹) * (g * x * g⁻¹) * (g * c * g⁻¹)⁻¹ = g * (c * x * c⁻¹) * g⁻¹ := by group
    _ = g * y * g⁻¹ := by rw [hc]

/-- The focal subgroup is normal in `S`. -/
instance CFSG.focalSubgroup_normal_in_sylow : ((feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G)).Normal := by
  have hF_le : feitThompsonFocalSubgroup p S ≤ S := focalSubgroup_le_sylow p S
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hF_le).mpr ?_
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro f
  have conj_mem : ∀ h, h ∈ (S : Subgroup G) → ∀ x, x ∈ feitThompsonFocalSubgroup p S → h * x * h⁻¹ ∈ feitThompsonFocalSubgroup p S := by
    intro h hh x hx
    unfold feitThompsonFocalSubgroup at hx
    refine Subgroup.closure_induction (p := fun z hz => h * z * h⁻¹ ∈ feitThompsonFocalSubgroup p S) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with ⟨a, ha, b, hb, hab, rfl⟩
      have ha' : h * a * h⁻¹ ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hh ha) ((S : Subgroup G).inv_mem hh)
      have hb' : h * b * h⁻¹ ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hh hb) ((S : Subgroup G).inv_mem hh)
      have hab' : IsConj (h * a * h⁻¹) (h * b * h⁻¹) := isConj_conj hab h
      have H : h * (a⁻¹ * b) * h⁻¹ = (h * a * h⁻¹)⁻¹ * (h * b * h⁻¹) := by group
      rw [H]
      exact Subgroup.subset_closure ⟨_, ha', _, hb', hab', rfl⟩
    · -- one
      simp
    · -- multiplication
      intro a b ha hb ha' hb'
      have H : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
      rw [H]
      exact (feitThompsonFocalSubgroup p S).mul_mem ha' hb'
    · -- inverse
      intro a ha ha'
      have H : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
      rw [H]
      exact (feitThompsonFocalSubgroup p S).inv_mem ha'
  constructor
  · intro hf
    exact conj_mem g hg f hf
  · intro hf'
    have hg_inv : g⁻¹ ∈ (S : Subgroup G) := (S : Subgroup G).inv_mem hg
    have := conj_mem g⁻¹ hg_inv (g * f * g⁻¹) hf'
    -- compute: g⁻¹ * (g * f * g⁻¹) * (g⁻¹)⁻¹ = f
    have H : g⁻¹ * (g * f * g⁻¹) * (g⁻¹)⁻¹ = f := by group
    rw [H] at this
    exact this

/-- For any `a, b ∈ S`, the element `(a b)⁻¹ * (b a)` belongs to `F`. -/
lemma CFSG.commutator_mem_focalSubgroup (a b : G) (ha : a ∈ (S : Subgroup G)) (hb : b ∈ (S : Subgroup G)) :
    (a * b)⁻¹ * (b * a) ∈ feitThompsonFocalSubgroup p S := by
  have hab : a * b ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem ha hb
  have hba : b * a ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hb ha
  have hconj : IsConj (a * b) (b * a) := by
    refine isConj_iff.2 ⟨b, ?_⟩
    group
  exact Subgroup.subset_closure ⟨a * b, hab, b * a, hba, hconj, rfl⟩


/-- The quotient group `S / F` is a commutative group. -/
instance CFSG.commGroupQuotient : CommGroup ((S : Subgroup G) ⧸ (feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G)) := by
  haveI h_normal : ((feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G)).Normal := focalSubgroup_normal_in_sylow p S
  have h_comm : ∀ x y : (S : Subgroup G) ⧸ (feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G), x * y = y * x := by
    intro x y
    refine QuotientGroup.induction_on x ?_
    intro a
    refine QuotientGroup.induction_on y ?_
    intro b
    apply QuotientGroup.eq.mpr
    have h_cond := commutator_mem_focalSubgroup p S a.1 b.1 a.2 b.2
    have h_mem_S : (a.1 * b.1)⁻¹ * (b.1 * a.1) ∈ (S : Subgroup G) := by
      apply (S : Subgroup G).mul_mem
      · exact (S : Subgroup G).inv_mem ((S : Subgroup G).mul_mem a.2 b.2)
      · exact (S : Subgroup G).mul_mem b.2 a.2
    have h_mem_subgroup : (⟨(a.1 * b.1)⁻¹ * (b.1 * a.1), h_mem_S⟩ : (S : Subgroup G)) ∈
        (feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G) := by
      rwa [Subgroup.mem_subgroupOf]
    exact h_mem_subgroup
  exact { mul_comm := h_comm }

/-- The canonical projection from `S` to the quotient by its focal subgroup. -/
def π : (S : Subgroup G) →* (S : Subgroup G) ⧸ (feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G) :=
  QuotientGroup.mk' ((feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G))

/-- The projection `π` sends elements of the focal subgroup to the identity. -/
lemma π_focal (f : G) (hf : f ∈ feitThompsonFocalSubgroup p S) (hfS : f ∈ (S : Subgroup G)) :
    π p S ⟨f, hfS⟩ = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.2 hf)

/-- Equality in the quotient: two elements of `S` that differ by an element of the focal subgroup have equal images under `π`. -/
lemma π_eq_of_diff_mem_focal (a b : G) (ha : a ∈ (S : Subgroup G)) (hb : b ∈ (S : Subgroup G))
    (h : a⁻¹ * b ∈ feitThompsonFocalSubgroup p S) : π p S ⟨a, ha⟩ = π p S ⟨b, hb⟩ := by
  apply QuotientGroup.eq.2
  exact Subgroup.mem_subgroupOf.2 h


section Transfer

/-- The transfer homomorphism `G →* (S : Subgroup G) ⧸ (feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G)`. -/
noncomputable def CFSG.transferHom [Finite G] [Fact p.Prime] :
    G →* (S : Subgroup G) ⧸ (feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G) :=
  MonoidHom.transfer (π p S)

/-- The derived subgroup of `G` is contained in the kernel of `transferHom`. -/
theorem CFSG.derivedSubgroup_le_ker_transferHom [Finite G] [Fact p.Prime] :
    derivedSubgroup G ≤ (transferHom p S).ker := by
  set_option maxHeartbeats 800000 in
  exact Abelianization.commutator_subset_ker (transferHom p S)

/-- The transfer of an element `s ∈ S` equals `π (s ^ index)`. -/
theorem CFSG.transferHom_eq_focalQuotientProj_pow_index [Finite G] [Fact p.Prime]
    (s : G) (hs : s ∈ (S : Subgroup G)) :
    transferHom p S s = π p S ⟨s ^ (S : Subgroup G).index, (S : Subgroup G).pow_mem hs _⟩ := by
  classical
  let Q := G ⧸ (S : Subgroup G)
  haveI : Fintype Q := Subgroup.fintypeQuotientOfFiniteIndex
  haveI : MulAction.QuotientAction G (S : Subgroup G) := MulAction.left_quotientAction (H := (S : Subgroup G))
  let orbitQ := Quotient (MulAction.orbitRel (Subgroup.zpowers s) Q)
  haveI : Fintype orbitQ := Quotient.fintype _
  rw [transferHom, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  -- Express each factor as π (s ^ m)
  have hfactor_eq : ∀ q : orbitQ,
      π p S ⟨(Quotient.out (Quotient.out q))⁻¹ * s ^ Function.minimalPeriod (s • ·) (Quotient.out q) * Quotient.out (Quotient.out q),
        by
          haveI : MulAction.QuotientAction G (S : Subgroup G) := MulAction.left_quotientAction (H := (S : Subgroup G))
          exact QuotientGroup.out_conj_pow_minimalPeriod_mem (H := (S : Subgroup G)) s (Quotient.out q)
        ⟩ = π p S ⟨s ^ Function.minimalPeriod (s • ·) (Quotient.out q),
        (S : Subgroup G).pow_mem hs _⟩ := by
    intro q
    let t : Q := Quotient.out q
    let x : G := Quotient.out t
    have hpow : s ^ Function.minimalPeriod (s • ·) t ∈ (S : Subgroup G) :=
      (S : Subgroup G).pow_mem hs _
    have hfactor : (Quotient.out (Quotient.out q))⁻¹ * s ^ Function.minimalPeriod (s • ·) t * Quotient.out (Quotient.out q) ∈ (S : Subgroup G) := by
      haveI : MulAction.QuotientAction G (S : Subgroup G) := MulAction.left_quotientAction (H := (S : Subgroup G))
      exact QuotientGroup.out_conj_pow_minimalPeriod_mem (H := (S : Subgroup G)) s t
    have hdiff : (s ^ Function.minimalPeriod (s • ·) t)⁻¹ * (x⁻¹ * s ^ Function.minimalPeriod (s • ·) t * x) ∈ feitThompsonFocalSubgroup p S := by
      -- this is exactly transfer_factor_div_mem_focalSubgroup, but we can inline
      have hconj : IsConj (s ^ Function.minimalPeriod (s • ·) t) (x⁻¹ * s ^ Function.minimalPeriod (s • ·) t * x) := by
        refine isConj_iff.2 ⟨x⁻¹, ?_⟩
        simp
      exact Subgroup.subset_closure ⟨s ^ Function.minimalPeriod (s • ·) t, hpow,
        x⁻¹ * s ^ Function.minimalPeriod (s • ·) t * x, hfactor, hconj, rfl⟩
    apply (π_eq_of_diff_mem_focal p S (s ^ Function.minimalPeriod (s • ·) t)
      (x⁻¹ * s ^ Function.minimalPeriod (s • ·) t * x) hpow hfactor hdiff).symm
  rw [Finset.prod_congr rfl (fun q _ => hfactor_eq q)]
  -- A lemma that π sends a power to a power
  have π_pow (n : ℕ) : π p S ⟨s ^ n, (S : Subgroup G).pow_mem hs n⟩ = (π p S ⟨s, hs⟩) ^ n := by
    simpa using map_pow (π p S) (⟨s, hs⟩ : (S : Subgroup G)) n
  simp_rw [π_pow]
  -- product of powers in a commutative group
  rw [Finset.prod_pow_eq_pow_sum]
  -- sum of minimal periods equals index
  have hsum : ∑ q : orbitQ, Function.minimalPeriod (s • ·) (Quotient.out q) = (S : Subgroup G).index := by
    calc
      ∑ q : orbitQ, Function.minimalPeriod (s • ·) (Quotient.out q)
          = ∑ q : orbitQ, Nat.card (MulAction.orbit (Subgroup.zpowers s) (Quotient.out q)) := by
            refine Finset.sum_congr rfl fun q _ => ?_
            haveI : Fintype (MulAction.orbit (Subgroup.zpowers s) (Quotient.out q)) := inferInstance
            have h := MulAction.minimalPeriod_eq_card (a := s) (b := Quotient.out q)
            rw [← Nat.card_eq_fintype_card] at h
            exact h
      _ = Nat.card (Σ q : orbitQ, MulAction.orbit (Subgroup.zpowers s) (Quotient.out q)) := by
            rw [Nat.card_sigma]
      _ = Nat.card Q := by
            rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits (Subgroup.zpowers s) Q)]
      _ = (S : Subgroup G).index := by rw [Subgroup.index_eq_card]
  rw [hsum]

/-- If an element `s` of a Sylow `p`-subgroup `S` satisfies `s ^ index ∈ F`, then `s` itself lies in `F`. -/
lemma CFSG.mem_focalSubgroup_of_pow_index_mem [Finite G] [Fact p.Prime] (s : G) (hs : s ∈ (S : Subgroup G))
    (hpow : s ^ (S : Subgroup G).index ∈ feitThompsonFocalSubgroup p S) : s ∈ feitThompsonFocalSubgroup p S := by
  have hS : IsPGroup p (S : Subgroup G) := S.isPGroup'
  have hn : ¬ p ∣ (S : Subgroup G).index := Sylow.not_dvd_index S
  -- The quotient `Q = S / F` is a p‑group.
  let Q := (S : Subgroup G) ⧸ (feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G)
  have hQ : IsPGroup p Q := hS.to_quotient _
  -- Since `p` is prime, `¬ p ∣ index` implies `p.Coprime index`.
  have h_coprime : p.Coprime (S : Subgroup G).index :=
    (Fact.out (p := p.Prime)).coprime_iff_not_dvd.mpr hn
  -- The map `x ↦ x ^ index` is an automorphism of `Q`.
  let h_pow_equiv := hQ.powEquiv h_coprime
  -- Compute `π (s ^ index)` in two ways.
  have hπ_pow_eq : π p S ⟨s ^ (S : Subgroup G).index, (S : Subgroup G).pow_mem hs _⟩ =
      (π p S ⟨s, hs⟩) ^ (S : Subgroup G).index := by
    simpa using map_pow (π p S) ⟨s, hs⟩ (S : Subgroup G).index
  have hπ_pow_one : π p S ⟨s ^ (S : Subgroup G).index, (S : Subgroup G).pow_mem hs _⟩ = 1 :=
    π_focal p S (s ^ (S : Subgroup G).index) hpow ((S : Subgroup G).pow_mem hs _)
  rw [hπ_pow_eq] at hπ_pow_one
  -- Hence `(π s) ^ index = 1`.
  have h_πs_pow : (π p S ⟨s, hs⟩) ^ (S : Subgroup G).index = 1 := hπ_pow_one
  -- Because `powEquiv` is injective, `π s` must be 1.
  have h_πs_one : π p S ⟨s, hs⟩ = 1 := by
    have h_eq : h_pow_equiv (π p S ⟨s, hs⟩) = 1 := by
      dsimp [h_pow_equiv]
      exact h_πs_pow
    have h_pow_one : h_pow_equiv (1 : Q) = 1 := by
      dsimp [h_pow_equiv]
      simp
    have h_symm_one : h_pow_equiv.symm 1 = 1 := by
      rw [Equiv.symm_apply_eq]
      exact h_pow_one.symm
    calc
      π p S ⟨s, hs⟩ = h_pow_equiv.symm (h_pow_equiv (π p S ⟨s, hs⟩)) := by simp
      _ = h_pow_equiv.symm 1 := by rw [h_eq]
      _ = 1 := h_symm_one
  -- `π s = 1` means `s` belongs to the kernel of the projection, i.e. to `F`.
  haveI := focalSubgroup_normal_in_sylow p S
  have h_mem : (⟨s, hs⟩ : (S : Subgroup G)) ∈ (feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G) :=
    (QuotientGroup.eq_one_iff (N := (feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G)) (x := (⟨s, hs⟩ : (S : Subgroup G)))).mp h_πs_one
  rw [Subgroup.mem_subgroupOf] at h_mem
  exact h_mem

end Transfer

/-
**Kind**: Theorem
**Note**: Theorem 1.17
**Stmt**:
Let $G$ be a finite group.
Let $p$ be a prime.
Let $S$ be a Sylow $p$-subgroup of $G$.
Then
\[ S \cap G' = \langle x^{-1} y | x, y \in S and x is conjugate to y in G \rangle. \]
-/

public theorem CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (S : Sylow p G) :
    ((S : Subgroup G) ⊓ derivedSubgroup G) =
      Subgroup.closure {z : G | ∃ x : G, x ∈ (S : Subgroup G) ∧ ∃ y : G, y ∈ (S : Subgroup G) ∧
        IsConj x y ∧ z = x⁻¹ * y} := by
  set F := feitThompsonFocalSubgroup p S with hF_def
  have hF_le_S : F ≤ (S : Subgroup G) := by
    unfold F
    exact focalSubgroup_le_sylow p S
  have hF_le_G' : F ≤ derivedSubgroup G := by
    unfold F
    apply (Subgroup.closure_le (K := derivedSubgroup G)).2
    intro z hz
    rcases hz with ⟨x, hx, y, hy, hxy, rfl⟩
    have h_gen : x⁻¹ * y ∈ derivedSubgroup G := by
      have h_abel : Abelianization.of (x⁻¹ * y) = 1 := by
        rcases hxy with ⟨c, hc⟩
        have hc' := congr_arg Abelianization.of hc
        simp [map_mul] at hc'
        -- hc' : of c * of x * (of c)⁻¹ = of y
        -- Since Abelianization G is abelian, we can rearrange
        have hxy' : Abelianization.of x = Abelianization.of y := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hc'
        calc
          Abelianization.of (x⁻¹ * y) = (Abelianization.of x)⁻¹ * Abelianization.of y := by simp
          _ = (Abelianization.of x)⁻¹ * Abelianization.of x := by rw [hxy']
          _ = 1 := by simp
      have h_mem : x⁻¹ * y ∈ (Abelianization.of : G →* Abelianization G).ker := by
        rw [MonoidHom.mem_ker]
        exact h_abel
      rw [Abelianization.ker_of] at h_mem
      exact h_mem
    exact h_gen
  have h_left : ((S : Subgroup G) ⊓ derivedSubgroup G) ≤ F := by
    intro s hs
    rcases hs with ⟨hsS, hsG'⟩
    have hV : transferHom p S s = 1 := by
      have h_ker : s ∈ (transferHom p S).ker := derivedSubgroup_le_ker_transferHom p S hsG'
      rw [MonoidHom.mem_ker] at h_ker
      exact h_ker
    have h_transfer : transferHom p S s = π p S ⟨s ^ (S : Subgroup G).index, (S : Subgroup G).pow_mem hsS _⟩ :=
      transferHom_eq_focalQuotientProj_pow_index p S s hsS
    have h_pi_eq_one : π p S ⟨s ^ (S : Subgroup G).index, (S : Subgroup G).pow_mem hsS _⟩ = 1 :=
      Eq.trans (Eq.symm h_transfer) hV
    have h_pow : s ^ (S : Subgroup G).index ∈ F := by
      let h_s_pow_mem := (S : Subgroup G).pow_mem hsS (S : Subgroup G).index
      haveI := focalSubgroup_normal_in_sylow p S
      have h_mem : (⟨s ^ (S : Subgroup G).index, h_s_pow_mem⟩ : (S : Subgroup G)) ∈
          (feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G) :=
        (QuotientGroup.eq_one_iff (N := (feitThompsonFocalSubgroup p S).subgroupOf (S : Subgroup G)) (x := (⟨s ^ (S : Subgroup G).index, h_s_pow_mem⟩ : (S : Subgroup G)))).mp h_pi_eq_one
      exact (Subgroup.mem_subgroupOf.mp h_mem)
    exact mem_focalSubgroup_of_pow_index_mem p S s hsS h_pow
  have h_right : F ≤ ((S : Subgroup G) ⊓ derivedSubgroup G) :=
    le_inf hF_le_S hF_le_G'
  simpa [F, feitThompsonFocalSubgroup] using le_antisymm h_left h_right
