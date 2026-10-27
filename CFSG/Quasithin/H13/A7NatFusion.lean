module

public import CFSG.Quasithin.H13.A7HyperplaneConfine
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.A7NatPre
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped Pointwise

theorem zmod_two_eq_of_ne_zero_iff : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b := by
  decide

theorem exists_alternating_permAct7_eq {v w : Fin 7 → ZMod 2}
    (h : hammingNorm v = hammingNorm w) :
    ∃ σ ∈ alternatingGroup (Fin 7), permAct7 σ v = w := by
  classical
  have hs : (Finset.univ.filter fun i => v i ≠ 0) ∈
      Set.powersetCard (Fin 7) (hammingNorm v) := rfl
  have ht : (Finset.univ.filter fun i => w i ≠ 0) ∈
      Set.powersetCard (Fin 7) (hammingNorm v) := h.symm
  have := Set.powersetCard.isPretransitive_alternatingGroup (α := Fin 7) (n := hammingNorm v)
    (by simp)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7))
    (⟨_, hs⟩ : Set.powersetCard (Fin 7) (hammingNorm v)) ⟨_, ht⟩
  have hgs : g • (Finset.univ.filter fun i => v i ≠ 0) = Finset.univ.filter fun i => w i ≠ 0 :=
    congrArg Subtype.val hg
  refine ⟨g, g.2, ?_⟩
  funext i
  rw [permAct7_apply]
  apply zmod_two_eq_of_ne_zero_iff
  have h1 : i ∈ g • (Finset.univ.filter fun i => v i ≠ 0) ↔
      i ∈ Finset.univ.filter fun i => w i ≠ 0 := by rw [hgs]
  rw [← Finset.inv_smul_mem_iff] at h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
  exact h1

section Orbits

variable {G : Type*} [Group G] {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem A7NatPre.exists_conj_of_weight (h : A7NatPre T L V ψ) {u w : V}
    (huw : hammingNorm (vec ψ u) = hammingNorm (vec ψ w)) :
    ∃ l ∈ L, (w : G) = l * u * l⁻¹ := by
  obtain ⟨σ, hσ, hσuw⟩ := exists_alternating_permAct7_eq huw
  obtain ⟨l, hl, hact⟩ := h.Lonto σ hσ
  let y : V := ⟨l * u * l⁻¹, (mem_normalizer_iff.1 (h.L_le hl) u).1 u.2⟩
  have hy : vec ψ y = vec ψ w := by rw [hact u y rfl, hσuw]
  exact ⟨l, hl, congrArg Subtype.val (vec_injective ψ hy).symm⟩

end Orbits

theorem weight_of_mem_evenWeight : ∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 → v ≠ 0 →
    hammingNorm v = 2 ∨ hammingNorm v = 4 ∨ hammingNorm v = 6 := by
  decide +kernel

theorem base_vectors_weight :
    hammingNorm (Pi.single 0 1 + Pi.single 1 1 : Fin 7 → ZMod 2) = 2 ∧
    hammingNorm (Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1 :
      Fin 7 → ZMod 2) = 4 ∧
    hammingNorm ((Pi.single 0 1 + Pi.single 1 1) +
      (Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1) : Fin 7 → ZMod 2) = 6 := by
  decide +kernel

theorem base_vectors_mem :
    (Pi.single 0 1 + Pi.single 1 1 : Fin 7 → ZMod 2) ∈ evenWeight 7 ∧
    (Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1 : Fin 7 → ZMod 2) ∈
      evenWeight 7 := by
  rw [mem_evenWeight, mem_evenWeight]
  decide +kernel

section Fusion

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem A7NatPre.exists_aligned_central (hT : quasithinIsSylowTwo T) (h : A7NatPre T L V ψ) :
    ∃ ψ' : V ≃* Multiplicative (evenWeight 7), A7NatPre T L V ψ' ∧
      ∀ m, m = 2 ∨ m = 4 ∨ m = 6 →
        ∃ x : V, hammingNorm (vec ψ' x) = m ∧ (x : G) ∈ centralizer (T : Set G) := by
  obtain ⟨ψ', h', hTalign⟩ := h.exists_aligned hT
  have hTP : ∀ t ∈ T, ∃ σ ∈ sevenP, IsCoordAct ψ' t σ := fun t ht => by
    obtain ⟨σ, hσ⟩ := h'.Nact t (h'.T_le ht)
    exact ⟨σ, ((hTalign σ).1 ⟨t, ht, hσ⟩).1, hσ⟩
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  obtain ⟨hb2, hb4⟩ := base_vectors_mem
  obtain ⟨hw2, hw4, hw6⟩ := base_vectors_weight
  have hfix : ∀ {e : Fin 7 → ZMod 2}, e ∈ evenWeight 7 → (∀ g ∈ sevenP, permAct7 g e = e) →
      ∃ x : V, vec ψ' x = e ∧ (x : G) ∈ centralizer (T : Set G) := by
    intro e he hfe
    obtain ⟨x, hx⟩ := exists_vec_eq ψ' he
    refine ⟨x, hx, hZC (mem_omegaOneCenter_of_fixed h'.le_T ψ' hTP h'.T_le ?_)⟩
    intro g hg
    rw [hx]
    exact hfe g hg
  have hf2 : ∀ g ∈ sevenP, permAct7 g (Pi.single 0 1 + Pi.single 1 1 : Fin 7 → ZMod 2) =
      Pi.single 0 1 + Pi.single 1 1 := fun g hg => sevenP_fix hg (Or.inl rfl)
  have hf4 : ∀ g ∈ sevenP, permAct7 g
      (Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1 : Fin 7 → ZMod 2) =
      Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1 :=
    fun g hg => sevenP_fix hg (Or.inr rfl)
  refine ⟨ψ', h', fun m hm => ?_⟩
  rcases hm with rfl | rfl | rfl
  · obtain ⟨x, hx, hxc⟩ := hfix hb2 hf2
    exact ⟨x, by rw [hx]; exact hw2, hxc⟩
  · obtain ⟨x, hx, hxc⟩ := hfix hb4 hf4
    exact ⟨x, by rw [hx]; exact hw4, hxc⟩
  · obtain ⟨x, hx, hxc⟩ := hfix (Submodule.add_mem _ hb2 hb4)
      (fun g hg => by rw [map_add, hf2 g hg, hf4 g hg])
    exact ⟨x, by rw [hx]; exact hw6, hxc⟩

omit [Finite G] in
theorem mem_normalizer_of_conjugate_eq {V : Subgroup G} {n : G} (h : CFSG.conjugate V n = V) :
    n ∈ normalizer (V : Set G) := by
  rw [mem_normalizer_iff]
  intro z
  rw [← mem_conjugate_iff_mem, h]

theorem A7NatPre.exists_conj_of_conj (h331 : Stmt3_3_1) (hyp : Hyp1223 G T L V)
    (h : A7NatPre T L V ψ) {u w : V} {g : G} (hg : (w : G) = g * u * g⁻¹) :
    ∃ l ∈ L, (w : G) = l * u * l⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hu : u = 1
  · refine ⟨1, one_mem _, ?_⟩
    rw [hg, hu]
    simp
  obtain ⟨ψ', h', hcent⟩ := h.exists_aligned_central hyp.sylow
  have hwt : ∀ x : V, x ≠ 1 →
      hammingNorm (vec ψ' x) = 2 ∨ hammingNorm (vec ψ' x) = 4 ∨ hammingNorm (vec ψ' x) = 6 :=
    fun x hx => weight_of_mem_evenWeight _ (vec_mem ψ' x) (by rwa [ne_eq, vec_eq_zero_iff])
  have hw : w ≠ 1 := by
    intro hw1
    apply hu
    apply Subtype.ext
    have h1 : g * (u : G) * g⁻¹ = 1 := by rw [← hg, hw1]; rfl
    calc (u : G) = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨x, hx, hxc⟩ := hcent _ (hwt u hu)
  obtain ⟨y, hy, hyc⟩ := hcent _ (hwt w hw)
  obtain ⟨l₁, -, hl₁x⟩ := h'.exists_conj_of_weight (u := u) (w := x) hx.symm
  obtain ⟨l₂, -, hl₂y⟩ := h'.exists_conj_of_weight (u := w) (w := y) hy.symm
  set k := l₂ * g * l₁⁻¹ with hk
  have hyx : (y : G) = k * x * k⁻¹ := by
    rw [hl₂y, hg, hl₁x, hk]
    group
  obtain ⟨Ts, hTs⟩ : ∃ Ts : Sylow 2 G, (Ts : Subgroup G) = T :=
    ⟨_, IsPGroup.toSylow_coe hyp.sylow.1 hyp.sylow.2⟩
  have hxc' : (x : G) ∈ centralizer ((Ts : Subgroup G) : Set G) := by rw [hTs]; exact hxc
  have hyc' : k⁻¹⁻¹ * x * k⁻¹ ∈ centralizer ((Ts : Subgroup G) : Set G) := by
    rw [inv_inv, ← hyx, hTs]
    exact hyc
  obtain ⟨n, hn, hnx⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer Ts (x : G) k⁻¹ hxc' hyc'
  rw [inv_inv, ← hyx] at hnx
  have hnM : n ∈ normalizer (L : Set G) := by
    obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
    obtain ⟨-, -, -, hNT, -⟩ := h331B L hyp.maximal hyp.quasisimple
    rw [hyp.conjClosure_eq] at hNT
    exact hNT (by rw [← hTs]; exact hn)
  have hy1 : y ≠ 1 := by
    intro hy1
    rw [hy1, vec_one] at hy
    rcases hwt w hw with h2 | h2 | h2 <;> rw [← hy] at h2 <;> simp at h2
  have hnV : n ∈ normalizer (V : Set G) := by
    rcases h'.TI n hnM with hVn | hVn
    · exact mem_normalizer_of_conjugate_eq hVn
    · exfalso
      have hmem : (y : G) ∈ V ⊓ CFSG.conjugate V n := by
        refine ⟨y.2, ?_⟩
        show (y : G) ∈ CFSG.conjugate V n
        rw [mem_conjugate_iff_mem, hnx]
        have : n * (n⁻¹ * (x : G) * n) * n⁻¹ = x := by group
        rw [this]
        exact x.2
      rw [hVn, mem_bot] at hmem
      exact hy1 (Subtype.ext hmem)
  obtain ⟨τ, hτ⟩ := h'.Nact _ (inv_mem hnV)
  have hτxy := hτ x y (by rw [hnx, inv_inv])
  have hwt_eq : hammingNorm (vec ψ' u) = hammingNorm (vec ψ' w) := by
    rw [← hx, ← hy, hτxy, hammingNorm_permAct7]
  exact h'.exists_conj_of_weight hwt_eq

end Fusion

end CFSG.Quasithin.H13.A7
