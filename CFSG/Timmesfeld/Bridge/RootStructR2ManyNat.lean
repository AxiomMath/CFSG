module

public import CFSG.Timmesfeld.Bridge.RootStructWTINatSum
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

public section

namespace CFSG.Timmesfeld.Bridge.QuotMod

open Matrix CFSG.Timmesfeld
open CFSG.Timmesfeld.ARS.NaturalModule (diagElt diagElt_mulVec)

variable {G : Type*} [Group G] {K : Type*} [Field K]
  {X N N₀ : Subgroup G} (hH : Hyp X N N₀) (φ : ↥X ≃* SpecialLinearGroup (Fin 2) K)
  {k : ℕ} {Nf : Fin k → Subgroup G} {θ : Fin k → (Fin 2 → K) → G}
  (hθ : ∀ i, N₀ ≤ Nf i ∧ Higman.IsNaturalQuotient φ (Nf i) N₀ (θ i))
  (hsup : N₀ ⊔ ⨆ i, Nf i = N)

include hsup in
theorem le_of_sup (i : Fin k) : Nf i ≤ N :=
  hsup ▸ le_sup_of_le_right (le_iSup Nf i)

include hθ hsup in
theorem θ_mem (i : Fin k) (v : Fin 2 → K) : θ i v ∈ N :=
  le_of_sup hsup i ((hθ i).2.mem v)

include hθ in
theorem θ_zero_mem (i : Fin k) : θ i 0 ∈ N₀ := by
  have := (hθ i).2.map_add 0 0
  simp only [add_zero, _root_.mul_inv_rev] at this
  simpa using N₀.inv_mem this

include hH hθ hsup in
theorem mem_of_diag_conj [Finite G] [Finite K]
    (hcard : Nat.card N = Nat.card N₀ * Nat.card K ^ (2 * k)) {t : Kˣ} (ht : t ≠ 1)
    {n : G} (hn : n ∈ N)
    (hfix : n⁻¹ * ((φ.symm (diagElt t) : G) * n * (φ.symm (diagElt t) : G)⁻¹) ∈
      N₀) :
    n ∈ N₀ := by
  classical
  have := hH.normal
  let _ : CommGroup (↥N ⧸ N₀.subgroupOf N) :=
    { (inferInstance : Group (↥N ⧸ N₀.subgroupOf N)) with
      mul_comm := fun u v => by
        obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective u
        obtain ⟨n', rfl⟩ := QuotientGroup.mk_surjective v
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have := hH.comm _ (N.inv_mem n'.2) _ (N.inv_mem n.2)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
        convert this using 1
        group }
  set ψ : Fin k → (Fin 2 → K) → Additive (↥N ⧸ N₀.subgroupOf N) :=
    fun i v => mk N₀ ⟨θ i v, θ_mem φ hθ hsup i v⟩ with hψ
  have hψ0 : ∀ i, ψ i 0 = 0 := fun i => (mk_eq_zero_iff _).2 (θ_zero_mem φ hθ i)
  have hψadd : ∀ i v w, ψ i (v + w) = ψ i v + ψ i w := by
    intro i v w
    rw [hψ]
    dsimp only
    rw [← mk_mul, eq_comm, mk_eq_mk_iff]
    simpa using (hθ i).2.map_add v w
  let Θ : (Fin k → Fin 2 → K) →+ Additive (↥N ⧸ N₀.subgroupOf N) :=
    { toFun := fun c => ∑ i, ψ i (c i)
      map_zero' := Finset.sum_eq_zero fun i _ => hψ0 i
      map_add' := fun c c' => by
        simp only [Pi.add_apply, hψadd]
        exact Finset.sum_add_distrib }
  have hΘ : ∀ c, Θ c = ∑ i, ψ i (c i) := fun c => rfl
  have hsingle : ∀ i v, Θ (Pi.single i v) = ψ i v := by
    intro i v
    rw [hΘ, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, hψ0]
    · simp
  have hsurj : Function.Surjective Θ := by
    let S : Subgroup G :=
      { carrier := {g | ∃ hg : g ∈ N, mk N₀ ⟨g, hg⟩ ∈ Set.range Θ}
        mul_mem' := by
          rintro g g' ⟨hg, c, hc⟩ ⟨hg', c', hc'⟩
          refine ⟨N.mul_mem hg hg', c + c', ?_⟩
          rw [map_add, hc, hc']
          rfl
        one_mem' := ⟨N.one_mem, 0, by rw [map_zero]; rfl⟩
        inv_mem' := by
          rintro g ⟨hg, c, hc⟩
          refine ⟨N.inv_mem hg, -c, ?_⟩
          rw [map_neg, hc]
          rfl }
    have hN₀N : N₀ ≤ N := hsup ▸ le_sup_left
    have hN₀S : N₀ ≤ S := fun g hg =>
      ⟨hN₀N hg, 0, by rw [map_zero]; exact ((mk_eq_zero_iff _).2 hg).symm⟩
    have hNfS : ∀ i, Nf i ≤ S := by
      intro i g hg
      obtain ⟨v, hv⟩ := (hθ i).2.exists_eq g hg
      refine ⟨le_of_sup hsup i hg, Pi.single i v, ?_⟩
      rw [hsingle, hψ]
      exact (mk_eq_mk_iff _ _).2 hv
    have hNS : N ≤ S := hsup ▸ sup_le hN₀S (iSup_le hNfS)
    intro v
    obtain ⟨g, rfl⟩ := mk_surjective (N₀ := N₀) v
    obtain ⟨_, c, hc⟩ := hNS g.2
    exact ⟨c, hc⟩
  have hcardV : Nat.card (Additive (↥N ⧸ N₀.subgroupOf N)) = Nat.card K ^ (2 * k) := by
    have hL := Subgroup.card_eq_card_quotient_mul_card_subgroup (N₀.subgroupOf N)
    have hN₀ : Nat.card ↥(N₀.subgroupOf N) = Nat.card N₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hsup ▸ le_sup_left)).toEquiv
    rw [hN₀, hcard, mul_comm] at hL
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hL.symm
  have hbij : Function.Bijective Θ := by
    refine hsurj.bijective_of_nat_card_le ?_
    rw [hcardV, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2),
      Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin, Fintype.card_fin, ← pow_mul,
      mul_comm]
  set h := φ.symm (diagElt t) with hh
  have hφh : φ h = diagElt t := by rw [hh, MulEquiv.apply_symm_apply]
  have hconjψ : ∀ i v,
      mk N₀ (conjN hH (h : G) h.2 ⟨θ i v, θ_mem φ hθ hsup i v⟩) =
        ψ i ((diagElt t : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by
    intro i v
    rw [hψ]
    dsimp only
    rw [mk_eq_mk_iff]
    have := (hθ i).2.map_mulVec h v
    rw [hφh] at this
    have e := N₀.inv_mem this
    simp only [_root_.mul_inv_rev, inv_inv] at e
    simpa [conjN] using e
  let cV : Additive (↥N ⧸ N₀.subgroupOf N) →+ Additive (↥N ⧸ N₀.subgroupOf N) :=
    MonoidHom.toAdditive (conjQ hH (h : G) h.2)
  have hcV : ∀ g : N, cV (mk N₀ g) = mk N₀ (conjN hH (h : G) h.2 g) := fun g => rfl
  have hcVΘ : ∀ c, cV (Θ c) =
      Θ (fun i => (diagElt t : Matrix (Fin 2) (Fin 2) K) *ᵥ c i) := by
    intro c
    rw [hΘ, hΘ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψ]
    dsimp only
    rw [hcV, hconjψ]
  obtain ⟨c, hc⟩ := hsurj (mk N₀ ⟨n, hn⟩)
  have hfix' : cV (mk N₀ ⟨n, hn⟩) = mk N₀ ⟨n, hn⟩ := by
    rw [hcV, eq_comm, mk_eq_mk_iff]
    simpa [conjN] using hfix
  rw [← hc, hcVΘ] at hfix'
  have hcc := hbij.1 hfix'
  have ht1 : (t : K) ≠ 1 := fun h' => ht (Units.ext h')
  have ht2 : ((t⁻¹ : Kˣ) : K) ≠ 1 := fun h' => ht (by
    have : t⁻¹ = 1 := Units.ext h'
    rwa [inv_eq_one] at this)
  have hc0 : c = 0 := by
    funext i
    have e0 : (t : K) * c i 0 = c i 0 := by
      have := congrFun (congrFun hcc i) 0
      rw [diagElt_mulVec] at this
      simpa using this
    have e1 : ((t⁻¹ : Kˣ) : K) * c i 1 = c i 1 := by
      have := congrFun (congrFun hcc i) 1
      rw [diagElt_mulVec] at this
      simpa using this
    have z0 : c i 0 = 0 := by
      have h' : ((t : K) - 1) * c i 0 = 0 := by rw [sub_mul, one_mul, e0, sub_self]
      rcases mul_eq_zero.1 h' with h' | h'
      · exact absurd (sub_eq_zero.1 h') ht1
      · exact h'
    have z1 : c i 1 = 0 := by
      have h' : (((t⁻¹ : Kˣ) : K) - 1) * c i 1 = 0 := by rw [sub_mul, one_mul, e1, sub_self]
      rcases mul_eq_zero.1 h' with h' | h'
      · exact absurd (sub_eq_zero.1 h') ht2
      · exact h'
    funext j
    fin_cases j
    · exact z0
    · exact z1
  rw [hc0, map_zero, eq_comm, mk_eq_zero_iff] at hc
  exact hc

end CFSG.Timmesfeld.Bridge.QuotMod
