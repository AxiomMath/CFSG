module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T1

open S35.Std S35.II

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' m γ' : Geo H M}

omit [Finite G] in
theorem back_facts (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    vtype m = true ∧ vtype γ' = false ∧ γ' ≠ α' ∧ dist β m + 2 = bMin H M ∧
      dist β γ' + 3 = bMin H M := by
  obtain ⟨hm, hγ, d1, d2⟩ := hb
  have hd := hp.dist_eq
  have hm' : vtype m = true := vtype_nbr_S5 hp.vδ' hm
  refine ⟨hm', vtype_nbr_S3 hm' hγ, ?_, by omega, by omega⟩
  rintro rfl
  omega

theorem Wb_le_stab (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    Wb β ≤ stab γ' := by
  obtain ⟨-, -, -, -, h1⟩ := back_facts hp hb
  refine iSup₂_le fun ρ hρ => Vn_le_stab_dist hS ?_
  have h2 := dist_triangle rfl ρ β γ'
  omega

omit [Finite G] in
theorem eq_or_eq_of_relIndex_two {T N D : Subgroup G} (hTN : T ≤ N) (hND : N ≤ D)
    (h2 : T.relIndex D = 2) : N = T ∨ N = D := by
  have hmul := Subgroup.relIndex_mul_relIndex T N D hTN hND
  rw [h2] at hmul
  have hdvd : T.relIndex N ∣ 2 := ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hTN
  · right
    rw [h] at hmul
    have : N.relIndex D = 1 := by omega
    exact le_antisymm hND (Subgroup.relIndex_eq_one.mp this)

@[expose] def ArcFull (δ l ρ : Geo H M) : Prop :=
  stab ρ ⊓ stab l ≤ (Qv δ ⊓ Qv l) ⊔ Qv ρ

omit [Finite G] in
theorem arcFull_smul (g : ↥(H ⊔ M)) (δ l ρ : Geo H M) :
    ArcFull (g • δ) (g • l) (g • ρ) ↔ ArcFull δ l ρ := by
  unfold ArcFull
  rw [stab_smul, stab_smul, Qv_smul, Qv_smul, Qv_smul, ← conjSub_inf, ← conjSub_inf,
    ← conjSub_sup, conjSub_le_conjSub_iff']

theorem arcN_le (hS : Sit H M S) {δ l ρ : Geo H M} (hρ : l ∈ nbrs ρ) :
    (Qv δ ⊓ Qv l) ⊔ Qv ρ ≤ stab ρ ⊓ stab l := by
  refine sup_le (le_inf ?_ ?_) (le_inf (pCoreOf_le 2 _) (Qv_le_stab hS hρ))
  · exact inf_le_right.trans (Qv_le_stab hS (mem_nbrs_symm.mp hρ))
  · exact inf_le_right.trans (pCoreOf_le 2 _)

end S35.T1

end F53.Stellmacher

end CFSG.Quasithin
