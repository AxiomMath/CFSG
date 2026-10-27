module

public import CFSG.RankThree.GF2n.Smith81.S81E7Form
public import CFSG.RankThree.GF2n.Smith81.S81XOps
public import CFSG.LieType.Steinberg.Minuscule.Unipotent

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model


variable {K : Type} [Field K]

@[expose] def NearW (a b : Fin e7Data.d) : Prop :=
  ∀ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ → pr a γ = 1 → pr b γ = -1 →
    e7Data.wt a = e7Data.wt b + MinData.toWeight γ

@[expose] def SpecW (a b : Fin e7Data.d) : Prop := ¬ NearW a b ∧ b ≠ opp a

theorem nearW_iff (a b : Fin e7Data.d) : NearW a b ↔ ∀ k : Fin 126,
    pr a ((Tag.rootCertificate .E7).root k) = 1 → pr b ((Tag.rootCertificate .E7).root k) = -1 →
      e7Data.wt a = e7Data.wt b + MinData.toWeight ((Tag.rootCertificate .E7).root k) :=
  forall_isRoot_iff fun γ => pr a γ = 1 → pr b γ = -1 →
    e7Data.wt a = e7Data.wt b + MinData.toWeight γ

instance (a b : Fin e7Data.d) : Decidable (NearW a b) :=
  decidable_of_iff _ (nearW_iff a b).symm

instance (a b : Fin e7Data.d) : Decidable (SpecW a b) := by unfold SpecW; infer_instance

@[expose] def prHom (a : Fin e7Data.d) : (Fin (Tag.rank .E7) → ℤ) →+ ℤ where
  toFun γ := pr a γ
  map_zero' := by simp [pr]
  map_add' γ δ := by simp [pr, dotProduct_add]

@[expose] def levA (a : Fin e7Data.d) : Fin e7Data.d → ℤ :=
  e7Data.fgrade (prHom a)

@[expose] def dE7 : ℤ := (Tag.cartan .E7).det

theorem dE7_pos : 0 < dE7 := MinData.det_cartan_pos posDef_cartan_E7

theorem levA_shift (a : Fin e7Data.d) {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    {b : Fin e7Data.d} (hb : pr b γ = -1) : levA a (shift γ b) = levA a b + dE7 * pr a γ :=
  e7Data.isGrading_fgrade (prHom a) b (shift γ b) γ (wt_shift hγ hb)

private theorem sum_ite_eq_of_nodup {α M : Type*} [DecidableEq α] [AddCommMonoid M] (L : List α)
    (hnd : L.Nodup) (δ : α) (f : α → M) :
    (L.map fun γ => if γ = δ then f γ else 0).sum = if δ ∈ L then f δ else 0 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons, ih hnd.2]
    by_cases hx : x = δ
    · subst hx
      simp [hnd.1]
    · simp [hx, Ne.symm hx]

variable [CharP K 2]

set_option maxRecDepth 20000 in
theorem rootOp_raises {a : Fin e7Data.d} {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (ha : pr a γ = 1) : Raises (levA a) dE7 (e7Data.rootOp K γ) := by
  intro b b' hne
  rw [rootOp_single hγ] at hne
  by_cases hb : pr b γ = -1
  · rw [if_pos hb, Finsupp.single_apply] at hne
    by_cases h : shift γ b = b'
    · rw [← h, levA_shift a hγ hb, ha, mul_one]
    · rw [if_neg h] at hne
      exact absurd rfl hne
  · rw [if_neg hb] at hne
    exact absurd rfl hne

set_option maxRecDepth 20000 in
theorem coef_prod (a : Fin e7Data.d) (L : List (Fin (Tag.rank .E7) → ℤ))
    (hL : ∀ γ ∈ L, IsRoot .E7 γ ∧ pr a γ = 1) (hnd : L.Nodup)
    (c : (Fin (Tag.rank .E7) → ℤ) → K) (b : Fin e7Data.d) (δ : Fin (Tag.rank .E7) → ℤ)
    (hδ : IsRoot .E7 δ) (hb : pr b δ = -1) :
    ((L.map fun γ => (1 : Module.End K (V K)) + c γ • e7Data.rootOp K γ).prod)
        (Finsupp.single b 1) (shift δ b) = if δ ∈ L then c δ else 0 := by
  have hR : ∀ γ ∈ L, Raises (levA a) dE7 (e7Data.rootOp K γ) := fun γ hγ =>
    rootOp_raises (hL γ hγ).1 (hL γ hγ).2
  by_cases hδa : pr a δ = 1
  · have hlev : levA a (shift δ b) = levA a b + dE7 := by
      rw [levA_shift a hδ hb, hδa, mul_one]
    rw [prod_coord (levA a) dE7_pos L (fun γ => e7Data.rootOp K γ) c hR b (shift δ b) hlev]
    have hterm : ∀ γ ∈ L, c γ * (e7Data.rootOp K γ (Finsupp.single b 1)) (shift δ b) =
        if γ = δ then c γ else 0 := by
      intro γ hγ
      rw [rootOp_single (hL γ hγ).1]
      by_cases hbγ : pr b γ = -1
      · rw [if_pos hbγ, Finsupp.single_apply]
        by_cases h : γ = δ
        · subst h
          simp
        · have hne : shift γ b ≠ shift δ b := fun e => h (toWeight_injective posDef_cartan_E7 (by
            have h1 := wt_shift (hL γ hγ).1 hbγ
            have h2 := wt_shift hδ hb
            rw [e] at h1
            exact add_left_cancel (h1.symm.trans h2)))
          rw [if_neg hne, if_neg h, mul_zero]
      · rw [if_neg hbγ]
        by_cases h : γ = δ
        · exfalso
          subst h
          exact hbγ hb
        · simp [h]
    rw [List.map_congr_left hterm, sum_ite_eq_of_nodup L hnd δ c]
  · have hδL : δ ∉ L := fun h => hδa (hL δ h).2
    rw [if_neg hδL]
    have hlt : levA a (shift δ b) < levA a b + dE7 := by
      rw [levA_shift a hδ hb]
      rcases pr_mem hδ a with h | h | h
      · rw [h]
        have := dE7_pos
        linarith
      · rw [h]
        have := dE7_pos
        linarith
      · exact absurd h hδa
    have hne : shift δ b ≠ b := by
      intro e
      have h1 := wt_shift hδ hb
      rw [e] at h1
      have h2 : MinData.toWeight δ = 0 := add_left_cancel (h1.symm.trans (add_zero _).symm)
      have h3 := form_self_root posDef_cartan_E7 hδ
      rw [h2, zero_dotProduct] at h3
      exact absurd h3 (by norm_num)
    exact prod_coord_low (levA a) dE7_pos L (fun γ => e7Data.rootOp K γ) c hR b (shift δ b) hne hlt

end CFSG.RankThree.GF2n.Smith81.E7X
