module

public import CFSG.LocalAnalysis.StandardType.GGDepAOdd
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem ggDepAThree_six_le_N {p N : ℕ} [Fact p.Prime] (hp3 : p = 3) {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x' : V} (F : GGDepAFrame p N h α x')
    (hdim : Module.finrank (ZMod p) V = N) : 6 ≤ N := by
  obtain ⟨-, -, -, -, h4⟩ := hH.1.tableB_facts
  rw [card_eq_of_ggLin ι] at h4
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, hdim] at h4
  have h4N : 4 ≤ N := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 h4
  have hdvd : 3 ∣ N := hp3 ▸ F.dvd
  obtain ⟨k, hk⟩ := hdvd
  omega

theorem ggDepAThree_stab {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {h : Fin (6 - 1) → V}
    {α : Fin (6 - 1) → Module.Dual (ZMod 3) V} {x : V} (F : GGDepAFrame 3 6 h α x)
    (r : Fin (6 - 1) → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i) :
    ∃ H : Subgroup (V ≃ₗ[ZMod 3] V), H ≤ Subgroup.closure (Set.range r) ∧
      (∀ g ∈ H, g x = x) ∧ 720 ≤ Nat.card H := by
  classical
  obtain ⟨ρ, -, hρmem, hρx, hρf⟩ :=
    ggDepAOdd_perm_embed (p := 3) (N := 6) (by norm_num) (by norm_num) F r hr
  refine ⟨ρ.range, ?_, ?_, ?_⟩
  · rintro g ⟨σ, rfl⟩
    exact hρmem σ
  · rintro g ⟨σ, rfl⟩
    exact hρx σ
  · have hinj : Function.Injective ρ := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro σ hσ
      apply hρf σ
      intro i
      have h1 : ρ σ = 1 := MonoidHom.mem_ker.mp hσ
      rw [h1]
      rfl
    have hcard : Nat.card ρ.range = 720 := by
      have h := Subgroup.card_ker_mul_card_range ρ
      rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hinj, Subgroup.card_bot, one_mul] at h
      rw [h, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    omega

end CFSG.StandardType
