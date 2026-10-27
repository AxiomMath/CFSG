module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.SteinbergCBIrreducibleTI

public section

namespace CFSG.Quasithin.SteinbergCB

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem nq_index_two_centralizer_Sylow_transfer [Finite G] (T : Sylow 2 G) {M : Subgroup G}
    (_hTM : (T : Subgroup G) ≤ M) {u : G} (huT : u ∈ (T : Subgroup G)) (hu : orderOf u = 2)
    (hQ : CFSG.QuasithinUnique.IsSylowTwoOf ((T : Subgroup G) ⊓ centralizer {u})
      (M ⊓ centralizer {u}))
    (hTQ : ((T : Subgroup G) ⊓ centralizer {u}).relIndex T ≤ 2)
    (hZ : ∀ z ∈ (T : Subgroup G), (∀ t ∈ (T : Subgroup G), t * z = z * t) → orderOf z = 2 →
      centralizer {z} ≤ M)
    (hM : ∀ g : G, M ⊓ centralizer {u} ≤ MulAut.conj g⁻¹ • M → MulAut.conj g⁻¹ • M = M) :
    CFSG.QuasithinUnique.IsSylowTwoOf ((T : Subgroup G) ⊓ centralizer {u}) (centralizer {u}) ∧
      ((T : Subgroup G) ⊓ centralizer {u} = T → centralizer {u} ≤ M) := by
  set C := centralizer ({u} : Set G) with hC
  set Q := (T : Subgroup G) ⊓ C with hQdef
  have hQp : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  have huQ : u ∈ Q := mem_inf.2 ⟨huT, mem_centralizer_singleton_iff.2 rfl⟩
  refine ⟨⟨inf_le_right, hQp, fun hdvd => ?_⟩, fun hQT => ?_⟩
  ·
    have hQ'p : IsPGroup 2 (Q.subgroupOf C) := hQp.of_equiv (subgroupOfEquivOfLe inf_le_right).symm
    obtain ⟨S', hS'⟩ := hQ'p.exists_le_sylow
    have hne : Q.subgroupOf C ≠ S' := by
      intro h
      have := S'.not_dvd_index
      rw [← h] at this
      exact this hdvd
    obtain ⟨a, ha⟩ := hQ'p.exists_card_eq
    obtain ⟨b, hb⟩ := S'.isPGroup'.exists_card_eq
    have hab : a < b := by
      have hle : a ≤ b := by
        have := card_dvd_of_le hS'
        rw [ha, hb] at this
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        apply hne
        exact eq_of_le_of_card_ge hS' (by rw [ha, hb, h])
    have hQcard : Nat.card (Q.subgroupOf C) = Nat.card Q :=
      Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
    have hS'card : 2 * Nat.card Q ≤ Nat.card S' := by
      rw [← hQcard, ha, hb, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) hab
    have hTcard : Nat.card T ≤ 2 * Nat.card Q := by
      have h := card_mul_index (Q.subgroupOf T)
      rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h
      change Nat.card Q * Q.relIndex T = Nat.card T at h
      rw [← h]
      calc Nat.card Q * Q.relIndex T ≤ Nat.card Q * 2 := Nat.mul_le_mul_left _ hTQ
        _ = 2 * Nat.card Q := mul_comm _ _
    set S := (S' : Subgroup C).map C.subtype with hSdef
    have hScard : Nat.card S = Nat.card S' := card_map_of_injective C.subtype_injective
    have hSp : IsPGroup 2 S := S'.isPGroup'.map _
    obtain ⟨P, hSP⟩ := hSp.exists_le_sylow
    have hPcard : Nat.card P = Nat.card T := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    have hSP' : S = P := eq_of_le_of_card_ge hSP (by omega)
    have hSC : S ≤ C := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have huS : u ∈ S :=
      ⟨⟨u, (mem_inf.1 huQ).2⟩, hS' (by simpa [mem_subgroupOf] using huQ), rfl⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P T
    have hgT : ∀ x ∈ S, g * x * g⁻¹ ∈ (T : Subgroup G) := fun x hx => by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ (hSP' ▸ hx)
    have hTS : ∀ t ∈ (T : Subgroup G), g⁻¹ * t * g ∈ S := fun t ht => by
      rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
        MulAut.smul_def, MulAut.conj_apply, inv_inv] at ht
      rw [hSP']
      exact ht
    set z := g * u * g⁻¹ with hz
    have hzT : z ∈ (T : Subgroup G) := hgT u huS
    have hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t := by
      intro t ht
      have h1 := mem_centralizer_singleton_iff.1 (hSC (hTS t ht))
      have e1 : t * z = g * ((g⁻¹ * t * g) * u) * g⁻¹ := by rw [hz]; group
      have e2 : z * t = g * (u * (g⁻¹ * t * g)) * g⁻¹ := by rw [hz]; group
      rw [e1, e2, h1]
    have hzo : orderOf z = 2 := by
      rw [hz, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hu]
    have hCz := hZ z hzT hzc hzo
    have hCM : C ≤ MulAut.conj g⁻¹ • M := by
      intro x hx
      rw [mem_conj_inv_smul_iff]
      apply hCz
      rw [mem_centralizer_singleton_iff]
      have h1 := mem_centralizer_singleton_iff.1 hx
      calc g * x * g⁻¹ * z = g * (x * u) * g⁻¹ := by rw [hz]; group
        _ = g * (u * x) * g⁻¹ := by rw [h1]
        _ = z * (g * x * g⁻¹) := by rw [hz]; group
    have hMg := hM g (inf_le_right.trans hCM)
    have hCM' : C ≤ M := hMg ▸ hCM
    have heq : M ⊓ C = C := inf_eq_right.2 hCM'
    have := hQ.2.2
    rw [heq] at this
    exact this hdvd
  ·
    have huc : ∀ t ∈ (T : Subgroup G), t * u = u * t := by
      intro t ht
      rw [← hQT] at ht
      exact mem_centralizer_singleton_iff.1 (mem_inf.1 ht).2
    exact hZ u huT huc hu

end CFSG.Quasithin.SteinbergCB
