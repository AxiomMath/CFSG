module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

open S35.II

namespace S35.T21

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

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
  refine sup_le (le_inf ?_ ?_) (le_inf (pCoreOf_le 2 _) (Std.Qv_le_stab hS hρ))
  · exact inf_le_right.trans (Std.Qv_le_stab hS (Std.mem_nbrs_symm.mp hρ))
  · exact inf_le_right.trans (pCoreOf_le 2 _)

theorem arcFull_iff_not_le (hS : Sit H M S) (hT : NbarThat H M) (hF : ThatFacts H M)
    {δ l ρ : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) (hρ : l ∈ nbrs ρ) (hne : ρ ≠ δ) :
    ArcFull δ l ρ ↔ ¬ (Qv δ ⊓ Qv l) ⊔ Qv ρ ≤ That2 ρ l := by
  have hρ5 : vtype ρ = false :=
    Std.vtype_nbr_S3 (Std.vtype_nbr_S5 hδ hl) (Std.mem_nbrs_symm.mp hρ)
  obtain ⟨-, hD, hidx⟩ := hF ρ l hρ5 hρ
  have h1 := hT δ l ρ hδ hl hρ hne
  have h2 := arcN_le hS (δ := δ) hρ
  have hmul := Subgroup.relIndex_mul_relIndex (That2 ρ l) ((Qv δ ⊓ Qv l) ⊔ Qv ρ)
    (stab ρ ⊓ stab l) h1 h2
  rw [hidx] at hmul
  constructor
  · intro hfull hle
    have h3 : stab ρ ⊓ stab l ≤ That2 ρ l := hfull.trans hle
    have := Subgroup.relIndex_eq_one.mpr h3
    omega
  · intro hnle
    have hA : ((That2 ρ l).relIndex ((Qv δ ⊓ Qv l) ⊔ Qv ρ)) ≠ 1 := fun h =>
      hnle (Subgroup.relIndex_eq_one.mp h)
    have hdvd : ((That2 ρ l).relIndex ((Qv δ ⊓ Qv l) ⊔ Qv ρ)) ∣ 2 := ⟨_, hmul.symm⟩
    have hA2 : ((That2 ρ l).relIndex ((Qv δ ⊓ Qv l) ⊔ Qv ρ)) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h hA
      · exact h
    rw [hA2] at hmul
    have : (((Qv δ ⊓ Qv l) ⊔ Qv ρ).relIndex (stab ρ ⊓ stab l)) = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp this

theorem nbarDich (hS : Sit H M S) (hT : NbarThat H M) (hF : ThatFacts H M) :
    NbarDich H M := by
  by_cases hfull : NbarFull H M
  · exact Or.inl hfull
  · right
    unfold NbarFull at hfull
    push Not at hfull
    obtain ⟨δ₀, l₀, ρ₀, hδ₀, hl₀, hρ₀, hne₀, hn₀⟩ := hfull
    intro δ l ρ hδ hl hρ hne
    by_contra hnle
    have hfa := (arcFull_iff_not_le hS hT hF hδ hl hρ hne).mpr hnle
    obtain ⟨g, hg1, hg2, hg3⟩ := Std.arc_trans hS hδ hl hρ hne hδ₀ hl₀ hρ₀ hne₀
    apply hn₀
    have := (arcFull_smul g δ l ρ).mpr hfa
    rw [hg1, hg2, hg3] at this
    exact this

end S35.T21

end F53.Stellmacher

end CFSG.Quasithin
