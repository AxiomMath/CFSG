module

public import CFSG.Quasithin.EmptyFaithful.SzC4S8CMat

public section

namespace CFSG.Quasithin.SzC4S8C

open CFSG.Assembly.LowTwoRank CFSG.Quasithin

section ModExtract

variable {G : Type} [Group G] {A V W : Subgroup G} {F : Type} [Field F] [Fintype F]
  {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)} {α : ↥A →* ↥Γ} {k : ℕ}

theorem iter_dual (hF : Fintype.card F = 2) (h : IsSumOfNaturalModulesVia A V W α true k)
    (g : ↥A) (hg : moduleAct true (α g : Matrix.GeneralLinearGroup (Fin 3) F) = cmF hF) :
    ∃ β : ↥V →* Multiplicative (Fin k → Fin 3 → F), Function.Surjective β ∧
      β.ker = W.subgroupOf V ∧
      ∀ (n : ℕ) (u u' : ↥V), (u' : G) = (g : G) ^ n * u * ((g : G) ^ n)⁻¹ → ∀ i : Fin k,
        Multiplicative.toAdd (β u') i =
          (fun v => (cmF hF).mulVec v)^[n] (Multiplicative.toAdd (β u) i) := by
  obtain ⟨hAV, -, β, hs, hk, he⟩ := h
  refine ⟨β, hs, hk, ?_⟩
  intro n
  induction n with
  | zero =>
    intro u u' hu i
    have : u' = u := Subtype.ext (by simpa using hu)
    rw [this]
    rfl
  | succ n ih =>
    intro u u' hu i
    have hgn : (g : G) ^ n ∈ A := A.pow_mem g.2 n
    have hmem : (g : G) ^ n * u * ((g : G) ^ n)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hAV hgn) u).mp u.2
    have hu'' : (u' : G) = (g : G) * ((g : G) ^ n * u * ((g : G) ^ n)⁻¹) * (g : G)⁻¹ := by
      rw [hu, pow_succ']
      group
    have h1 := he g ⟨_, hmem⟩ u' hu'' i
    rw [h1, hg, Function.iterate_succ_apply']
    congr 1
    exact ih u ⟨_, hmem⟩ rfl i

theorem rel_dual (hF : Fintype.card F = 2) (h : IsSumOfNaturalModulesVia A V W α true k)
    (g : ↥A) (hg : moduleAct true (α g : Matrix.GeneralLinearGroup (Fin 3) F) = cmF hF) :
    ∀ v ∈ V, ∃ w ∈ W, (g : G) ^ 3 * v * ((g : G) ^ 3)⁻¹ =
      w * (((g : G) ^ 2 * v * ((g : G) ^ 2)⁻¹) * v) := by
  obtain ⟨β, -, hk, hit⟩ := iter_dual hF h g hg
  intro v hv
  have hmem : ∀ n : ℕ, (g : G) ^ n * v * ((g : G) ^ n)⁻¹ ∈ V := fun n =>
    (Subgroup.mem_normalizer_iff.mp (h.1 (A.pow_mem g.2 n)) v).mp hv
  let u : ↥V := ⟨v, hv⟩
  let u3 : ↥V := ⟨_, hmem 3⟩
  let u2 : ↥V := ⟨_, hmem 2⟩
  have hu3 := hit 3 u u3 rfl
  have hu2 := hit 2 u u2 rfl
  have hker : u3 * (u2 * u)⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul]
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, toAdd_one, Pi.zero_apply]
    rw [hu3 i, hu2 i, cmF_rel hF]
    abel
  rw [hk, Subgroup.mem_subgroupOf] at hker
  refine ⟨_, hker, ?_⟩
  show _ = ((u3 : G) * ((u2 : G) * (u : G))⁻¹) * ((u2 : G) * (u : G))
  rw [inv_mul_cancel_right]

theorem orbit_dual (hF : Fintype.card F = 2) (h : IsSumOfNaturalModulesVia A V W α true 1)
    (g : ↥A) (hg : moduleAct true (α g : Matrix.GeneralLinearGroup (Fin 3) F) = cmF hF) :
    ∀ v ∈ V, v ∉ W → ∀ u ∈ V, u ∉ W →
      ∃ n : ℕ, u * ((g : G) ^ n * v * ((g : G) ^ n)⁻¹)⁻¹ ∈ W := by
  obtain ⟨β, -, hk, hit⟩ := iter_dual hF h g hg
  intro v hv hvW u hu huW
  have hmem : ∀ n : ℕ, (g : G) ^ n * v * ((g : G) ^ n)⁻¹ ∈ V := fun n =>
    (Subgroup.mem_normalizer_iff.mp (h.1 (A.pow_mem g.2 n)) v).mp hv
  have hne : ∀ y : ↥V, (y : G) ∉ W → Multiplicative.toAdd (β y) 0 ≠ 0 := by
    intro y hy h0
    apply hy
    have hy1 : y ∈ β.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simpa using h0
    rw [hk, Subgroup.mem_subgroupOf] at hy1
    exact hy1
  obtain ⟨n, hn⟩ := cmF_orbit hF _ _ (hne ⟨v, hv⟩ hvW) (hne ⟨u, hu⟩ huW)
  refine ⟨n, ?_⟩
  have h1 := hit n ⟨v, hv⟩ ⟨_, hmem n⟩ rfl 0
  have hker : (⟨u, hu⟩ : ↥V) * (⟨_, hmem n⟩ : ↥V)⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [h1, hn]
  rw [hk, Subgroup.mem_subgroupOf] at hker
  exact hker

end ModExtract

end CFSG.Quasithin.SzC4S8C
