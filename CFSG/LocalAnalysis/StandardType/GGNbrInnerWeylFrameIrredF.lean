module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFrameIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LieType.SeitzGeneration

theorem ggSCWeylIrred_of_sylowTorus_frameF {G₀ : Type} [Group G₀] {p N : ℕ} (hp : p.Prime)
    (u : ZMod p) (hu : u ≠ 1) (s n : G₀) (hs : orderOf s = p)
    (hn : n * s * n⁻¹ = s ^ u.val) (hZ : Disjoint (Subgroup.zpowers s) (Subgroup.center G₀))
    {R : Type} [Group R] [Finite R] (hT : SylowTorus R p N) (ρ : Fin N → G₀ →* R)
    (hρ : ∀ i, Function.Injective (ρ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ρ i A) (ρ j B))
    (f : Fin N → Fin N) (hf : ∀ i, f i ≠ i)
    (hmove : ∀ i : Fin N, ∃ (g : R) (t : ZMod p), t ≠ 0 ∧
      g * ρ i s * g⁻¹ = ρ (f i) (s ^ t.val))
    (hconn : ∀ S : Finset (Fin N), S.Nonempty → (∀ i, i ∈ S ↔ f i ∈ S) → S = Finset.univ)
    (r : ℕ) : GGSCWeylIrred p r R := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨e, m, he_inj, he_single, hm_conj⟩ :=
    exists_frameTorus_of_commutingFrames hp u s n hs hn hZ ρ hρ hc
  let E : Subgroup R := e.range
  have hE : IsElemAbelian p E := by
    change IsElemAbelian p e.range
    refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
    · obtain ⟨v, hv⟩ := a.2
      obtain ⟨w, hw⟩ := b.2
      show (a : R) * (b : R) = (b : R) * (a : R)
      rw [← hv, ← hw, ← map_mul, ← map_mul]
      congr 1
      exact mul_comm v w
    · obtain ⟨v, hv⟩ := hx
      rw [← hv, ← map_pow, ← ofAdd_toAdd v, ← ofAdd_nsmul,
        ZModModule.char_nsmul_eq_zero, ofAdd_zero, map_one]
  have hcardE : Nat.card E = p ^ N := by
    change Nat.card e.range = p ^ N
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective he_inj, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
  have hmN : ∀ i, m i ∈ Subgroup.normalizer (E : Set R) := fun i =>
    frameScale_mem_normalizer_range u e m hm_conj i
  have hfus : ∀ i : Fin N, ∃ t : ZMod p, t ≠ 0 ∧
      ∃ n' ∈ Subgroup.normalizer (E : Set R),
        n' * e (Multiplicative.ofAdd (Pi.single i (1 : ZMod p))) * n'⁻¹ =
          e (Multiplicative.ofAdd (Pi.single (f i) t)) := by
    intro i
    obtain ⟨g, t, ht, hgt⟩ := hmove i
    obtain ⟨P, hEP, hPcomm, hPΩ⟩ := exists_sylow_of_sylowTorus_elemAbelian hp hT hE hcardE
    have hx : e (Multiplicative.ofAdd (Pi.single i (1 : ZMod p))) ∈ (P : Subgroup R) :=
      hEP ⟨_, rfl⟩
    have hy : e (Multiplicative.ofAdd (Pi.single (f i) t)) ∈ (P : Subgroup R) := hEP ⟨_, rfl⟩
    have hg : g * e (Multiplicative.ofAdd (Pi.single i (1 : ZMod p))) * g⁻¹ =
        e (Multiplicative.ofAdd (Pi.single (f i) t)) := by
      rw [he_single, he_single, ZMod.val_one, pow_one]
      exact hgt
    obtain ⟨n', hnP, hnconj⟩ :=
      exists_mem_normalizer_conj_of_commutative_sylow P hPcomm hx hy hg
    exact ⟨t, ht, n', ggFrame_mem_normalizer_of_le_and_pow_eq_one hEP hE.2 hPΩ hnP, hnconj⟩
  have hirr : GGWeylIrred E := by
    refine ggWeylIrred_range_of_frame e u hu (fun i => ⟨m i, hmN i, hm_conj i⟩) ?_
    intro T hTinv hscT ⟨i₀, hi₀⟩
    choose t ht n' hn' hn'eq using hfus
    have hiff : ∀ i, Multiplicative.ofAdd (Pi.single i (1 : ZMod p)) ∈ T ↔
        Multiplicative.ofAdd (Pi.single (f i) (1 : ZMod p)) ∈ T := by
      intro i
      constructor
      · intro hi
        have h1 := hTinv (n' i) (hn' i) _ hi _ (hn'eq i)
        exact frameTorus_single_mem_of_scaling u hu T hscT h1
          (by simpa using ht i)
      · intro hi
        have h1 : Multiplicative.ofAdd (Pi.single (f i) (t i)) ∈ T := by
          have := T.pow_mem hi (t i).val
          rwa [frameTorus_single_pow, ZMod.natCast_zmod_val, mul_one] at this
        refine hTinv (n' i)⁻¹ (Subgroup.inv_mem _ (hn' i)) _ h1 _ ?_
        rw [← hn'eq i]
        group
    have hS := hconn (Finset.univ.filter fun i =>
      Multiplicative.ofAdd (Pi.single i (1 : ZMod p)) ∈ T) ⟨i₀, by simpa using hi₀⟩
      (fun i => by simpa using hiff i)
    intro i
    have hmem : i ∈ Finset.univ.filter fun i =>
        Multiplicative.ofAdd (Pi.single i (1 : ZMod p)) ∈ T := by
      rw [hS]
      exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hmem).2
  intro E₁ hE₁ _ _ hsc
  obtain ⟨c, hcE⟩ := exists_conj_eq_of_selfCentralizing_of_sylowTorus hp hT hE hcardE hE₁ hsc
  rw [hcE]
  exact ggWeylIrred_map (MulAut.conj c) hirr

end CFSG.StandardType

end
