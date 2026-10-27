module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLinePermB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggFixLine_P_card {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    Nat.card ↥(Subgroup.closure (Set.range r)) = N.factorial := by
  have hp : p ≠ 2 := S.odd
  have hN2 : 2 ≤ N := by have := S.five_le; omega
  have hPerm : Nat.card (Equiv.Perm (Fin (N - 1 + 1))) = N.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    have hN : N - 1 + 1 = N := by omega
    rw [hN]
  calc Nat.card ↥(Subgroup.closure (Set.range r))
      = Nat.card ↥(l6kp_eta S).range :=
        Nat.card_congr (Equiv.ofInjective _ (l6kp_eta_inj S))
    _ = Nat.card ↥(l6kp_rhoHom (p := p) (N := N)).range := by rw [l6kp_eta_range S]
    _ = Nat.card (Equiv.Perm (Fin (N - 1 + 1))) :=
        (Nat.card_congr (Equiv.ofInjective _
          (l6kp_rho_inj (p := p) (N := N) hN2 hp))).symm
    _ = N.factorial := hPerm


private lemma l6kp_perm_normal_abelian_bot {N : ℕ} (hN : 5 ≤ N)
    (H : Subgroup (Equiv.Perm (Fin N))) [H.Normal]
    (hab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : H = ⊥ := by
  by_contra hne
  haveI hnt : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  have hle : alternatingGroup (Fin N) ≤ H :=
    Equiv.Perm.alternatingGroup_le_of_normal (α := Fin N) (N := H) (by simpa using hN)
      (inferInstance : Nontrivial ↥H)
  haveI : Nontrivial (Fin N) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  have hcomm : ⁅alternatingGroup (Fin N), alternatingGroup (Fin N)⁆ = ⊥ := by
    rw [Subgroup.commutator_self_eq_bot_iff]
    exact isMulCommutative_iff.mpr (fun (a b : ↥(alternatingGroup (Fin N))) =>
      Subtype.ext (hab a.1 (hle a.2) b.1 (hle b.2)))
  have hA : alternatingGroup (Fin N) = ⊥ := by
    have h := commutator_alternatingGroup_eq_self (α := Fin N) (by simpa using hN)
    rw [hcomm] at h
    exact h.symm
  have hfac : 120 ≤ N.factorial := by
    have h := Nat.factorial_le hN
    norm_num at h
    exact h
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin N)
  rw [hA] at h2
  have hbot : Nat.card (⊥ : Subgroup (Equiv.Perm (Fin N))) = 1 := by simp
  rw [hbot, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h2
  omega

theorem ggFixLine_P_abelian_normal_trivial {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) (K : Subgroup (V ≃ₗ[ZMod p] V))
    (hKP : K ≤ Subgroup.closure (Set.range r))
    (hKn : ∀ g ∈ Subgroup.closure (Set.range r), ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hKab : ∀ k ∈ K, ∀ k' ∈ K, k * k' = k' * k) : K = ⊥ := by
  have hp : p ≠ 2 := S.odd
  have hN2 : 2 ≤ N := by have := S.five_le; omega
  have hN5 : 5 ≤ N := S.five_le
  let P : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range r)
  let η := l6kp_eta S
  let ρ := l6kp_rhoHom (p := p) (N := N)
  let Rg : Subgroup (l6kp_H0 p (N - 1 + 1) ≃ₗ[ZMod p] l6kp_H0 p (N - 1 + 1)) := ρ.range
  let ρ' : Equiv.Perm (Fin (N - 1 + 1)) →* Rg :=
    ρ.codRestrict Rg (fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  let η' : ↥P →* Rg :=
    η.codRestrict Rg (fun x => by
      change η x ∈ ρ.range
      rw [← l6kp_eta_range S]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hρ'surj : Function.Surjective ρ' := by
    rintro ⟨y, hy⟩
    obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hy
    exact ⟨σ, Subtype.ext hσ⟩
  have hη'surj : Function.Surjective η' := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ η.range := by rw [l6kp_eta_range S]; exact hy
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hy'
    exact ⟨g, Subtype.ext hg⟩
  let K' : Subgroup ↥P := K.subgroupOf P
  haveI hK'norm : K'.Normal := ⟨fun k hk g => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hKn g.1 g.2 k.1 hk⟩
  let K3 : Subgroup Rg := Subgroup.map η' K'
  have hK3normal : K3.Normal := Subgroup.Normal.map hK'norm η' hη'surj
  have hK3ab : ∀ a ∈ K3, ∀ b ∈ K3, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul]
    exact congrArg η' (Subtype.ext (hKab k.1 (Subgroup.mem_subgroupOf.mp hk) l.1
      (Subgroup.mem_subgroupOf.mp hl)))
  let K2 : Subgroup (Equiv.Perm (Fin (N - 1 + 1))) := Subgroup.comap ρ' K3
  haveI hK2norm : K2.Normal := Subgroup.Normal.comap hK3normal ρ'
  have hρ'inj : Function.Injective ρ' := by
    intro a b hab
    apply l6kp_rho_inj (p := p) (N := N) hN2 hp
    have := congrArg (fun x : Rg => (x : l6kp_H0 p (N - 1 + 1) ≃ₗ[ZMod p]
      l6kp_H0 p (N - 1 + 1))) hab
    simpa [ρ'] using this
  have hK2ab : ∀ a ∈ K2, ∀ b ∈ K2, a * b = b * a := by
    intro a ha b hb
    apply hρ'inj
    rw [map_mul, map_mul]
    exact hK3ab (ρ' a) ha (ρ' b) hb
  have hK2bot : K2 = ⊥ := l6kp_perm_normal_abelian_bot (N := N - 1 + 1)
    (show 5 ≤ N - 1 + 1 by omega) K2 hK2ab
  refine le_antisymm ?_ bot_le
  intro k hk
  rw [Subgroup.mem_bot]
  have hkP : k ∈ P := hKP hk
  let k' : K' := ⟨⟨k, hkP⟩, hk⟩
  have hηk : η' k' ∈ K3 := Subgroup.mem_map.mpr ⟨k', k'.2, rfl⟩
  obtain ⟨σ, hσ⟩ := hρ'surj (η' k')
  have hσK2 : σ ∈ K2 := by
    show ρ' σ ∈ K3
    rw [hσ]
    exact hηk
  have hσ1 : σ = 1 := by
    have : σ ∈ (⊥ : Subgroup (Equiv.Perm (Fin (N - 1 + 1)))) := by rwa [← hK2bot]
    simpa using this
  have hη1 : η' k' = 1 := by rw [← hσ, hσ1]; exact map_one ρ'
  have hval : η k'.1 = 1 := by
    have := congrArg (fun x : Rg => (x : l6kp_H0 p (N - 1 + 1) ≃ₗ[ZMod p]
      l6kp_H0 p (N - 1 + 1))) hη1
    simpa [η', k'] using this
  have hk1p : k'.1 = 1 := l6kp_eta_inj S (hval.trans (map_one η).symm)
  simpa [k'] using congrArg (fun x : ↥P => x.1) hk1p

end CFSG.StandardType

end



