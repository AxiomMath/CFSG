module

public import CFSG.Quasithin.Background.H158TBfs
public import CFSG.Quasithin.Background.HMathieuFacts24Base

public section

namespace CFSG.Quasithin.H158T

open CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

theorem factor_AutPerm :
    (Nat.card ↥AutPerm).factorization 2 = 10 := by
  rw [card_AutPerm, show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num]
  exact factorization_eq Nat.prime_two (by norm_num)

theorem card_sylow_two {T : Subgroup (Equiv.Perm (Fin 24))}
    (hT : CFSG.Quasithin.IsSylowIn 2 T AutPerm) :
    Nat.card ↥(T.subgroupOf AutPerm) = 2 ^ (Nat.card ↥AutPerm).factorization 2 := by
  obtain ⟨hle, hpg, hnd⟩ := hT
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hcard : Nat.card ↥(T.subgroupOf AutPerm) = 2 ^ n := by
    rw [← hn]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hmul := Subgroup.card_mul_index (T.subgroupOf AutPerm)
  rw [hcard] at hmul
  have hnd' : ¬ 2 ∣ (T.subgroupOf AutPerm).index := hnd
  have hf := factorization_eq (a := n) Nat.prime_two hnd'
  rw [hmul] at hf
  rw [hcard, hf]

noncomputable abbrev qSub : Subgroup ↥AutPerm :=
  (phi24 : T24s2.Elem →* ↥AutPerm).range

theorem phi24_injective :
    Function.Injective (phi24 : T24s2.Elem →* ↥AutPerm) :=
  T24s2.toSub_injective AutPerm _

theorem card_qSub :
    Nat.card ↥(qSub : Subgroup ↥AutPerm) = 2 ^ 10 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective phi24_injective).toEquiv, card_T24s2,
    factor_AutPerm]

def qPerms : Set (Equiv.Perm (Fin 24)) :=
  {σ | ∃ p : T24s2.Elem, T24s2.perm p = σ}

theorem gen_mem_qPerms {g : Array ℕ} (hg : g ∈ genList) :
    ∃ σ ∈ qPerms, ∀ i : Fin 24, (σ i : ℕ) = g[(i : ℕ)]! := by
  obtain ⟨k, hk, hgk⟩ := Array.mem_iff_getElem.1 (T24s2_gen_mem hg)
  have hkn : k < T24s2.n := by rw [← T24s2.size_elems]; exact hk
  refine ⟨T24s2.perm ⟨k, hkn⟩, ⟨⟨k, hkn⟩, rfl⟩, fun i => ?_⟩
  have harr : T24s2.arr ⟨k, hkn⟩ = g := by
    unfold PT.arr
    rw [getElem!_pos _ k hk]
    exact hgk
  rw [PT.perm_val, harr]

theorem exists_conj_sylow
    {T : Subgroup (Equiv.Perm (Fin 24))} (hT : CFSG.Quasithin.IsSylowIn 2 T AutPerm) :
    ∃ h : Equiv.Perm (Fin 24), h ∈ AutPerm ∧ ∀ σ ∈ qPerms, h⁻¹ * σ * h ∈ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := card_sylow_two hT
  have hH : IsPGroup 2 ↥(qSub : Subgroup ↥AutPerm) := IsPGroup.of_card (n := 10) card_qSub
  obtain ⟨g, hg⟩ :=
    exists_conj_le_range (T.subgroupOf AutPerm).subtype Subtype.val_injective hsyl hH
  refine ⟨((g⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)), (g⁻¹).2, ?_⟩
  intro σ hσ
  obtain ⟨p, rfl⟩ := hσ
  have hy : phi24 p ∈ (qSub : Subgroup ↥AutPerm) := ⟨p, rfl⟩
  have h1 := hg _ hy
  rw [Subgroup.range_subtype, Subgroup.mem_subgroupOf] at h1
  have e1 : (((g⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)))⁻¹ = (g : Equiv.Perm (Fin 24)) := by
    rw [← Subgroup.coe_inv, inv_inv]
  have e2 : (g : Equiv.Perm (Fin 24)) * T24s2.perm p *
      ((g⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)) =
      ((g * phi24 p * g⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  rw [e1, e2]
  exact h1

end CFSG.Quasithin.H158T
