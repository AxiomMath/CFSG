module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Steps

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223

variable {G : Type} [Group G] [Finite G]

theorem inf_normalizer_le_of_isChar {T Mc M S I : Subgroup G} (h5 : StageLemma15205)
    (hs : Setting152 T Mc M) (hST : S ≤ T) (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hMI : M ⊓ I ≤ Mc ⊓ I) {Q : Subgroup G} (hQS : Q ≤ S) (hQ0 : Q ≠ ⊥)
    (hchar : (Q.subgroupOf S).Characteristic) :
    I ⊓ Subgroup.normalizer (Q : Set G) ≤ Mc ⊓ I := by
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) :=
    hTS.trans (normalizer_le_normalizer_of_characteristic_subgroupOf hQS hchar)
  have hQ2 : IsPGroup 2 Q := hs.qtfe.sylow.1.to_le (hQS.trans hST)
  have hQN : Q ≤ pCoreOf 2 (Subgroup.normalizer (Q : Set G)) :=
    le_pCoreOf_of_le_normalizer Subgroup.le_normalizer le_rfl hQ2
  have hO : pCoreOf 2 (Subgroup.normalizer (Q : Set G)) ≠ ⊥ := fun h =>
    hQ0 (eq_bot_iff.mpr (h ▸ hQN))
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have hTM' : InM T M' := ⟨hM'.1, hTQ.trans hM'.2⟩
  rcases (h5 G T Mc M hs M').mp hTM' with hMM | hMM
  · intro x hx
    have hxM : x ∈ M := hMM ▸ hM'.2 hx.2
    exact hMI ⟨hxM, hx.1⟩
  · intro x hx
    have hxM : x ∈ Mc := hMM ▸ hM'.2 hx.2
    exact ⟨hxM, hx.1⟩

theorem cgsIn_le_of_concl_i {T Mc M S I : Subgroup G} (h5 : StageLemma15205)
    (hs : Setting152 T Mc M) (hST : S ≤ T) (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hMI : M ⊓ I ≤ Mc ⊓ I) : cgsIn I S ≤ Mc ⊓ I := by
  unfold cgsIn
  refine iSup_le fun Q => iSup_le fun hQS => iSup_le fun hQ0 => iSup_le fun hchar => ?_
  exact inf_normalizer_le_of_isChar h5 hs hST hTS hMI hQS hQ0 hchar

omit [Finite G] in
theorem isChiBlock2_of_isChi0Block {X L : Subgroup G} (h : IsChi0Block X L) : IsChiBlock2 X L :=
  ⟨h.1, h.2.elim Or.inl fun h' => Or.inr
    (h'.elim (fun h3 => ⟨3, by decide, h3⟩) fun h5 => ⟨5, by decide, h5⟩)⟩

theorem reduction15223P3_of (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (h5 : StageLemma15205) (h17 : StageLemma15217) (h18 : StageLemma15218) :
    Reduction15223P3 := by
  intro G _ _ T Mc M hs H hH B₀ hB₀ I hI hchar hi
  have hsyl : IsSylowTwoOf (sOf152 T Mc M B₀) I := (h18 G T Mc M hs H hH B₀ hB₀ I hI.1).sylow
  have hidx : (sOf152 T Mc M B₀).relIndex T = 2 := (h17 G T Mc M hs B₀ hB₀ I hI.1).2.2
  have hST : sOf152 T Mc M B₀ ≤ T := inf_le_left
  have hTS : T ≤ Subgroup.normalizer (sOf152 T Mc M B₀ : Set G) := by
    have : ((sOf152 T Mc M B₀).subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hidx
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hST).mp this
  have hsq : IsSQTKIn I := by
    have := hs.qtfe.simple
    exact sqtkGroup_of_pCoreOf_ne_bot hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian hI.1.inH.2
  obtain ⟨r, Lb, -, hLb, hprod⟩ := hC129 G I (sOf152 T Mc M B₀) (Mc ⊓ I) hsq hchar hsyl
    (cgsIn_le_of_concl_i h5 hs hST hTS hi) inf_le_right
  exact ⟨r, Lb, fun i => isChiBlock2_of_isChi0Block (hLb i).1, hprod⟩

end S15223

end CFSG.Quasithin
