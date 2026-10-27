module

public import CFSG.Quasithin.Vol2.Ch3E215MC
public import CFSG.Quasithin.Vol2.Ch3E215MD
public import CFSG.Quasithin.Vol2.Ch3E213MSL2PairE

public section

namespace CFSG.Quasithin.Ch3E215M

open CFSG.Open CFSG.QuasithinUnique B6 CFSG.GorensteinWalter CFSG.BenderSuzuki.MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL projUpperTriangular)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem bruhat_of_qrc_psl2 {H M : Subgroup G} (hMH : M ≤ H) {I V : Subgroup H} {g : H}
    (hI : I = V ⊔ CFSG.conjugate V g) (hgI : g ∈ I) (hVM : V ≤ M.subgroupOf H) {L : Type*}
    [Group L] (ψ : ↥I →* L) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ (M.subgroupOf H ⊓ I).subgroupOf I) {k : Type} [Field k] [Finite k] {m : ℕ}
    (hk : Nat.card k = 2 ^ m) (e : L ≃* projectiveSL 2 k)
    (hB : ((M.subgroupOf H ⊓ I).subgroupOf I).map (e.toMonoidHom.comp ψ) =
      projUpperTriangular 2 k) :
    (∀ x ∈ I.map H.subtype, x ∈ M ⊓ I.map H.subtype ∨ ∃ m₁ ∈ M ⊓ I.map H.subtype,
      ∃ m₂ ∈ M ⊓ I.map H.subtype, x = m₁ * (g : G)⁻¹ * m₂) ∧
    (M ⊓ I.map H.subtype).relIndex (I.map H.subtype) = 2 ^ m + 1 := by
  set M₀ := M.subgroupOf H ⊓ I with hM₀
  set Ψ : ↥I →* PSL2MatrixGroup k :=
    (H13.QRC.p2PSLEquiv k).toMonoidHom.comp (e.toMonoidHom.comp ψ) with hΨ
  have hΨs : Function.Surjective Ψ :=
    (H13.QRC.p2PSLEquiv k).surjective.comp (e.surjective.comp hψ)
  have hΨk : Ψ.ker ≤ M₀.subgroupOf I := fun x hx => hker (by
    rw [MonoidHom.mem_ker] at hx ⊢
    simpa [hΨ] using hx)
  have hΨB : (M₀.subgroupOf I).map Ψ = psl2Borel k := by
    rw [hΨ, ← Subgroup.map_map, hB]
    exact H13.QRC.map_p2Equiv_projUpperTriangular
  have hg' : g⁻¹ ∈ I := I.inv_mem hgI
  have hgB : Ψ ⟨g⁻¹, hg'⟩ ∉ psl2Borel k := by
    intro hmem
    rw [← hΨB] at hmem
    have hgM₀ : g⁻¹ ∈ M₀ := mem_of_map_mem hΨk hmem
    have hgM : g ∈ M.subgroupOf H := by simpa using (M.subgroupOf H).inv_mem hgM₀.1
    have hIM : I ≤ M.subgroupOf H := by
      rw [hI]
      refine sup_le hVM ?_
      rintro _ ⟨v, hv, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact (M.subgroupOf H).mul_mem ((M.subgroupOf H).mul_mem
        ((M.subgroupOf H).inv_mem hgM) (hVM hv)) hgM
    have htop : M₀.subgroupOf I = ⊤ := Subgroup.subgroupOf_eq_top.2 (le_inf hIM le_rfl)
    have hΨB' := hΨB
    rw [htop, Subgroup.map_top_of_surjective _ hΨs] at hΨB'
    have h1 := index_psl2Borel hk
    rw [← hΨB', Subgroup.index_top] at h1
    have : 0 < 2 ^ m := by positivity
    omega
  have hBru := bruhat_of_surjective hg' Ψ hΨk (by rw [hΨB]; exact bruhat_psl2Borel hk hgB)
  have hidx := relIndex_eq_index_map Ψ hΨs hΨk
  rw [hΨB, index_psl2Borel hk] at hidx
  have hMap : M₀.map H.subtype = M ⊓ I.map H.subtype := by
    rw [Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hMH]
  have hcoe : H.subtype g⁻¹ = (g : G)⁻¹ := rfl
  refine ⟨?_, ?_⟩
  · have h1 := bruhat_map H.subtype hBru
    rwa [hMap, hcoe] at h1
  · rw [← hMap, Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective, hidx]

theorem e215Concl_of_pair {H T M V K : Subgroup G} (hS : Ch3E213M.Setting H T M V K)
    {T' : Sylow 2 ↥H} (hT' : (T' : Subgroup H) = T.subgroupOf H)
    (hP : Ch3E213M.SL2Pair.Pair T' (M.subgroupOf H) (V.subgroupOf H)) : E215Concl H T M V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  obtain ⟨m, g, hm, hgI, hVI, hsyl, hNI, hMI, hJ1, hcharI, L, ψ, hψs, hψk, k', _, hk', eL,
    hBor⟩ := hP
  rw [hT'] at hsyl hMI
  have hVMI : V.subgroupOf H ≤ inSubgroup (CFSG.pCore 2)
      (M.subgroupOf H ⊓ (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g)) := by
    rw [hMI]
    exact le_inf (fun x hx => hS.hyp.le_T hx) le_sup_left
  obtain ⟨hIX, hpair, hker⟩ := Ch3E213M.pair_of_qrc_kerIn hTH hMH hS.hyp.le_T hS.hyp.normal_T
    hS.hyp.elem rfl hgI hsyl (fun x hx => (hNI ⟨hx.2, hx.1⟩).1) hVMI hJ1
  obtain ⟨hc2, hne⟩ := Ch3E213M.charTwo_ne_of_qrc hVH hcharI hVI
  rw [hIX] at hc2 hne
  have hψk' :
      ψ.ker = CFSG.pCore 2 ↥(V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) := by
    rw [hψk, hJ1, inSubgroup]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have : Finite k' := Nat.finite_of_card_ne_zero (by rw [hk']; positivity)
  have hcard : (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹)).relIndex
      (Ch3n.pairI V (g : G)⁻¹) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    rw [hker, ← hIX, Ch3E213M.relIndex_pCoreOf_map_subtype,
      Ch3E213M.SL2Pair.card_quotient_pCore_eq hψs hψk', Nat.card_congr eL.toEquiv,
      Ch3E213M.card_projectiveSL_two_pow hk']
  have h9 : m = 3 → ∃ c ∈ Ch3n.pairI V (g : G)⁻¹, orderOf c = 9 := fun hm3 => by
    subst hm3
    obtain ⟨c, hc9⟩ := Ch3E213M.exists_orderOf_nine_projectiveSL hk'
    obtain ⟨x, hx, hx9⟩ := Ch3E213M.SL2Pair.exists_orderOf_nine_of_surjective hψs
      (c := eL.symm c) (by rw [MulEquiv.orderOf_eq, hc9])
    exact ⟨x, hIX ▸ hx, hx9⟩
  have hVM : V.subgroupOf H ≤ M.subgroupOf H :=
    hVMI.trans ((Subgroup.map_subtype_le _).trans inf_le_left)
  have hker' : ψ.ker ≤ (M.subgroupOf H ⊓ (V.subgroupOf H ⊔
      CFSG.conjugate (V.subgroupOf H) g)).subgroupOf
        (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) := fun x hx => by
    rw [hψk] at hx
    exact Subgroup.mem_subgroupOf.2 (kerIn_le (Subgroup.mem_subgroupOf.1 hx))
  obtain ⟨hBru, hidx⟩ := bruhat_of_qrc_psl2 hMH rfl hgI hVM ψ hψs hker' hk' eL hBor
  rw [hIX] at hBru hidx
  exact ⟨(g : G)⁻¹, H.inv_mem g.2, hpair, hc2, hne,
    Ch3E213M.relIndex_le_of_psl2 hpair hc2 hm hcard h9,
    e215DataOf_of_psl2 hpair hc2 hm hcard h9 hBru hidx⟩

end CFSG.Quasithin.Ch3E215M
