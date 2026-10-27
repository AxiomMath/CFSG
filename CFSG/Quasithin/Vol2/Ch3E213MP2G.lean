module

public import CFSG.Quasithin.Vol2.Ch3E213MP2F
public import CFSG.Quasithin.Vol2.Ch3E213MP4A

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)

theorem pkgSzPaired
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) : PkgSzPaired := by
  intro G _ _ H T M V K hS h1 n hn hSz _
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', -⟩ :=
    qrcHyp_of_hyp28 hS.hyp hS.charTwo
  have := hel
  have hVQ' : 4 ≤ (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) := by
    rw [relIndex_subgroupOf_inf_pCore hVH]
    exact hS.four_le
  have hVQn : ¬ V.subgroupOf H ≤ CFSG.pCore 2 H := by
    intro h
    rw [inf_eq_left.2 h, Subgroup.relIndex_self] at hVQ'
    omega
  obtain ⟨a, ha, hna, k, _, _, hk, ⟨θ⟩⟩ := exists_equiv_suzukiGroup_of_isSz hSz
  rw [hna] at hk
  obtain ⟨t₀, ht₀T, -, hK, hc, hd⟩ := exists_paired_of_case1' h38 hS h1
  obtain ⟨φ⟩ := nonempty_mulEquiv_star hMH K
  set π := QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤) with hπ
  set K₁ := barIn M H K with hK₁
  set K₂ := K₁.map (MulAut.conj (π t₀)).toMonoidHom with hK₂
  have θ₁ : K₁ ≃* CFSG.Blueprint.suzukiGroup a k := φ.trans θ
  have θ₂ : K₂ ≃* CFSG.Blueprint.suzukiGroup a k :=
    (K₁.equivMapOfInjective _ (MulAut.conj (π t₀)).injective).symm.trans θ₁
  obtain ⟨-, -, -, hKn, hCK, hKS, ⟨hSB, hBtop, hBmax⟩, -, hEcard, hEO⟩ :=
    H13.QRC.bender_section_setup hS.not_solvable T' hTn hTM' hMH' hmax' hVT' hVM'
  rw [hK] at hKn hCK hKS
  set S := (T' : Subgroup H).map π with hSdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hS2 : IsPGroup 2 S := T'.isPGroup'.map π
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.2
    ⟨le_top, hS2, by
      rw [Subgroup.relIndex_top_right, hSdef, ← Sylow.coe_mapSurjective hπs T']
      exact (T'.mapSurjective hπs).not_dvd_index⟩
  have hs : π t₀ ∈ S := ⟨t₀, by rw [hT']; exact ht₀T, rfl⟩
  set E := (V.subgroupOf H).map π with hEdef
  have : CFSG.IsElementaryAbelian 2 E := CFSG.IsElementaryAbelian.map π
  have hES : E ≤ S := Subgroup.map_mono hVT'
  have hSE : S ≤ Subgroup.normalizer (E : Set _) :=
    (Subgroup.map_mono hTV').trans (Subgroup.le_normalizer_map π)
  have hE4 : 4 ≤ Nat.card E := hEcard ▸ hVQ'
  obtain ⟨x₁, L₁, hx₁L, hL₁K, hLeq, hel₂, hE₂S, hsyl, hcore, hO2, hO2P, hmodel⟩ :=
    P2.paired_suzuki_quotient ha hk θ₁ θ₂ hc hd hKn hCK hSsyl hKS hs rfl hSB hBtop hBmax hEO
      hES hSE hE4
  have := hel₂
  have hFA : ∀ f ∈ L₁, ∀ b ∈ (E ⊔ K₁) ⊓ K₂, f * b = b * f := fun f hf b hb =>
    hc f (hL₁K hf) b hb.2
  have hFAb : L₁ ⊓ ((E ⊔ K₁) ⊓ K₂) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf hL₁K inf_le_right).trans hd.le)
  have hF : (∃ ℓ a : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ 1 ≤ a ∧ Nonempty (L₁ ≃* DihedralGroup (ℓ ^ a)) ∧
        Nat.card ↥((E ⊔ (E ⊔ K₁) ⊓ K₂) ⊓ L₁) = 2) ∨
      (∃ (f : ℕ) (k : Type) (_ : Field k), 2 ≤ f ∧ Nat.card k = 2 ^ f ∧
        Nonempty (L₁ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k)) ∨
      ∃ (b : ℕ) (k : Type) (_ : Field k), 1 ≤ b ∧ Nat.card k = 2 ^ (2 * b + 1) ∧
        Nonempty (L₁ ≃* CFSG.Blueprint.suzukiGroup b k) := by
    rcases hmodel with ⟨ℓ, hℓ, hℓ2, ⟨eD⟩, h2, -⟩ | ⟨b, hb, heL⟩
    · exact Or.inl ⟨ℓ, 1, hℓ, hℓ2, le_rfl, ⟨eD.trans (by rw [pow_one])⟩, h2⟩
    · exact Or.inr (Or.inr ⟨b, GaloisField 2 (2 * b + 1), inferInstance, hb,
        GaloisField.card 2 (2 * b + 1) (by omega), heL⟩)
  obtain ⟨g, hgI, hVI, -, h9⟩ := H13.QRC.qrc_original_pair_lift_retains_central_second_factor
    hcharH T' hTn hTM' hMH' hmax' hVT' hTV' hVM' hVQn hFA hFAb (Subgroup.mem_sup_left hx₁L)
    hLeq.symm hF hsyl inf_le_right hcore hO2 hO2P (P2.inf_sup_eq_sup_inf hFA hE₂S)
    (P2.inf_sup_eq_sup_inf hFA (hE₂S.trans hSB))
  dsimp only at h9
  obtain ⟨-, -, -, -, -, -, -, hTIsyl, -, -, hJcore, hJO, -, -, hcharI, hO2MI, hNV, ψ, hψs,
    hψker, -⟩ := h9
  rw [hT'] at hTIsyl hO2MI
  have hVMI : V.subgroupOf H ≤ inSubgroup (CFSG.pCore 2)
      (M.subgroupOf H ⊓ (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g)) := by
    rw [hO2MI]
    exact le_inf (hT' ▸ hVT') le_sup_left
  obtain ⟨hIX, hpair, hker⟩ := pair_of_qrc_kerIn hTH hMH hS.hyp.le_T hS.hyp.normal_T
    hS.hyp.elem rfl hgI hTIsyl (fun x hx => (hNV ⟨hx.2, hx.1⟩).1) hVMI (hJcore.symm.trans hJO)
  obtain ⟨hc2, hne⟩ := charTwo_ne_of_qrc hVH hcharI hVI
  rw [hIX] at hc2 hne
  have hψk' :
      ψ.ker = CFSG.pCore 2 ↥(V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g) := by
    rw [hψker, hJO, inSubgroup]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have hcard : (kerIn (M ⊓ Ch3n.pairI V (g : G)⁻¹) (Ch3n.pairI V (g : G)⁻¹)).relIndex
      (Ch3n.pairI V (g : G)⁻¹) = Nat.card L₁ := by
    rw [hker, ← hIX, relIndex_pCoreOf_map_subtype, P4.card_quotient_pCore_eq hψs hψk']
  refine ⟨(g : G)⁻¹, H.inv_mem g.2, hpair, hc2, hne, ?_⟩
  rcases hmodel with ⟨ℓ, hℓ, hℓ2, -, -, hcardL⟩ | ⟨b, hb, ⟨eL⟩⟩
  · exact relIndex_le_of_dihedral hpair hc2 hℓ hℓ2 (a := 1) le_rfl
      (by rw [hcard, hcardL, pow_one])
  · have hcardF : Nat.card (GaloisField 2 (2 * b + 1)) = 2 ^ (2 * b + 1) :=
      GaloisField.card 2 (2 * b + 1) (by omega)
    refine relIndex_le_of_sz hpair hc2 (n := 2 * b + 1) (by omega) ?_
    rw [hcard, Nat.card_congr eL.toEquiv, CFSG.LieType.Ree.suzuki_order hcardF]
    ring

end CFSG.Quasithin.Ch3E213M
