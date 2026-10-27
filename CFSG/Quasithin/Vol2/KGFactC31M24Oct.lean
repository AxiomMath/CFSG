module

public import CFSG.Quasithin.Vol2.KGFactC31M24Set
public import CFSG.Quasithin.Vol2.KGFactC31NatSec
public import CFSG.Quasithin.Vol2.KGFactC31Blk
public import CFSG.Quasithin.Vol2.KGFactC31M24Nor

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native Matrix _root_.Certificates

@[expose] def matOf (k : ℕ) (masks : List (List ℕ)) (j : ℕ) : Matrix (Fin k) (Fin k) (ZMod 2) :=
  Matrix.of fun r i => maskVec k ((masks.getD j []).getD i 0) r

theorem conj_gen {k : ℕ} {ws : List (List ℤ)} {masks : List (List ℕ)} {v : Fin k → G₀}
    {bs : List Table}
    (hbs : List.Forall₂ (Rep 24) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 24))))
    (h : ((ws.map fun w => tab (wordG gensG w)).zip masks).all
      (fun p => masksOK 24 bs (toTable p.1) p.2) = true) {j : ℕ} (hj : j < ws.length)
    (hjm : j < masks.length) (i : Fin k) :
    elt (ws.getD j []) * v i * (elt (ws.getD j []))⁻¹ = eElt v fun r => matOf k masks j r i := by
  have hmem : ((ws.map fun w => tab (wordG gensG w))[j]'(by simpa using hj), masks[j]) ∈
      (ws.map fun w => tab (wordG gensG w)).zip masks := by
    rw [List.mem_iff_getElem]
    exact ⟨j, by rw [List.length_zip, List.length_map]; omega, by simp⟩
  have h1 := List.all_eq_true.mp h _ hmem
  beta_reduce at h1
  simp only [List.getElem_map, tab_eq] at h1
  have hT : Rep 24 (toTable (wordG gensG ws[j])) (wordG gensG ws[j]) := rep_toTable hn24 _
  have h2 := conj_of_masksOK hn24 hbs hT h1 i
  apply Subtype.ext
  rw [List.getD_eq_getElem _ _ hj]
  show wordG gensG ws[j] * ((v i : G₀) : Equiv.Perm (Fin 24)) * (wordG gensG ws[j])⁻¹ = _
  rw [h2]
  have hE : eElt (fun i => ((v i : G₀) : Equiv.Perm (Fin 24))) (fun r => matOf k masks j r i) =
      ((eElt v fun r => matOf k masks j r i : G₀) : Equiv.Perm (Fin 24)) :=
    (map_eElt NativeSporadic.M24.subtype _).symm
  rw [← hE]
  congr 1
  funext r
  simp [matOf, List.getElem?_eq_getElem hjm]

theorem moGenW_length : moGenW.length = 2 := rfl
theorem moMasks_length : moMasks.length = 2 := rfl

theorem conj_mo {j : ℕ} (hj : j < 2) (i : Fin 4) :
    elt (moGenW.getD j []) * vO i * (elt (moGenW.getD j []))⁻¹ =
      eElt vO fun r => matOf 4 moMasks j r i :=
  conj_gen forall₂_o c_masks_mo (by rw [moGenW_length]; exact hj)
    (by rw [moMasks_length]; exact hj) i

theorem moGen_mem {j : ℕ} (hj : j < 2) : elt (moGenW.getD j []) ∈ Mo := by
  have hj' : j < moGenW.length := by rw [moGenW_length]; exact hj
  have hmem : moGenW.getD j [] ∈ moGenW := by
    rw [List.getD_eq_getElem _ _ hj']
    exact List.getElem_mem hj'
  exact elt_mem_genOf hmem

theorem trans_mo : ∀ c : Fin 4 → ZMod 2, c ≠ 0 →
    (matStep (matOf 4 moMasks 0) (matOf 4 moMasks 1))^[7] {c} = Finset.univ.erase 0 := by
  decide +kernel

theorem not_isPGroup_sl4 : ¬ IsPGroup 2 ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  rw [E16.card_statedSL4] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 20160)
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

variable {A : Type} [Group A] [Finite A]

theorem concl_octad
    {S M₀ R M V : Subgroup A}
    (h : Setup S M₀ R M V) {f : G₀ →* A} (hf : Iso f) (hR : R = (eSub basis_o).map f) {y : A}
    (hy : y ∈ M₀) (hyR : y ∉ R) : Concl S M₀ R M V := by
  have hvA : EBasis fun i => f (vO i) := basis_o.map hf.inj
  have hRA : R = eSub hvA := by rw [hR, eSub_map basis_o hf.inj]
  have hN : Subgroup.normalizer (R : Set A) = (eNorm basis_o).map f := by
    rw [hR, hf.map_normalizer]
  have hMoN : Mo.map f ≤ Subgroup.normalizer (R : Set A) := by
    rw [hN]
    exact Subgroup.map_mono Mo_le
  have hRc : Nat.card R = 16 := by rw [hR, hf.card_map, card_eSub]; norm_num
  have hNc : Nat.card (Subgroup.normalizer (R : Set A)) = 322560 := by
    rcases card_normalizer_eq hf h.R_ne_bot (by rw [hRc]; norm_num) h.hrad hMoN
        (by rw [card_Mo]; norm_num) with
      ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
    · exact h1
    all_goals rw [hRc] at h2; norm_num at h2
  have hNeq : Subgroup.normalizer (R : Set A) = Mo.map f :=
    (Subgroup.eq_of_le_of_card_ge hMoN (by rw [hNc, hf.card_map, card_Mo])).symm
  have hCR : Subgroup.centralizer (R : Set A) = R := by
    rw [hR, ← hf.map_centralizer, cent_o]
  have hNN : Subgroup.normalizer (R : Set A) ≤ eNorm hvA := by
    show Subgroup.normalizer (R : Set A) ≤ Subgroup.normalizer (eSub hvA : Set A)
    rw [← hRA]
  have hker : (E16.eNHom hvA hNN).ker = R.subgroupOf (Subgroup.normalizer (R : Set A)) :=
    ker_eNHom hvA hNN (by rw [← hRA, hCR]; exact inf_eq_right.mpr Subgroup.le_normalizer)
  have hsurj : Function.Surjective (E16.eNHom hvA hNN) := by
    have h1 := card_range_eq Subgroup.le_normalizer (E16.eNHom hvA hNN) hker
    rw [hRc, hNc] at h1
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ (by rw [E16.card_statedSL4]; omega)
  have : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) :=
    E16.isSimpleGroup_statedSL4
  have hM₀N := h.hM₀R
  have hsupN : M₀ ⊔ R ≤ Subgroup.normalizer (R : Set A) := sup_le hM₀N Subgroup.le_normalizer
  have hnorm : Subgroup.normalizer (R : Set A) ≤
      Subgroup.normalizer ((M₀ ⊔ R : Subgroup A) : Set A) := fun n hn =>
    mem_normalizer_sup (h.normal_in_normalizer hn) hn
  have hMR : M₀ ⊔ R = Subgroup.normalizer (R : Set A) := by
    rcases simple_of_surj _ hsurj hker (M₀ ⊔ R) le_sup_right hsupN hnorm with h1 | h1
    · exact absurd (le_sup_left.trans h1.le hy) hyR
    · exact h1
  have hRNV : R ≤ Subgroup.normalizer (V : Set A) :=
    h.hRC.trans (Subgroup.centralizer_le_normalizer _)
  have hVN : Subgroup.normalizer (R : Set A) ≤ Subgroup.normalizer (V : Set A) := by
    rw [← hMR]
    exact sup_le h.hM₀V hRNV
  have hgN : ∀ j < 2, f (elt (moGenW.getD j [])) ∈ Subgroup.normalizer (V : Set A) :=
    fun j hj => hVN (hNeq ▸ ⟨_, moGen_mem hj, rfl⟩)
  have hVR' : V ≤ eSub hvA := hRA ▸ h.hVR
  have hVeq : V = eSub hvA := by
    rcases eq_bot_or_eq_of_trans hvA trans_mo (conj_map (fun i => conj_mo (by norm_num) i) f)
        (conj_map (fun i => conj_mo (by norm_num) i) f) hVR' (hgN 0 (by norm_num))
        (hgN 1 (by norm_num)) with h1 | h1
    · exact absurd h1 h.hVne
    · exact h1
  have hVR2 : V = R := hVeq.trans hRA.symm
  have hRM₀ : R ≤ M₀ := hVR2 ▸ h.hVM₀
  have hM₀eq : M₀ = Subgroup.normalizer (R : Set A) := by
    rw [← hMR, sup_eq_left.mpr hRM₀]
  have hM₀N' : M₀ ≤ eNorm hvA := hM₀eq.le.trans hNN
  have hCM₀ : M₀ ⊓ Subgroup.centralizer (eSub hvA : Set A) = R := by
    rw [← hRA, hCR]
    exact inf_eq_right.mpr hRM₀
  have hker₀ := ker_eNHom hvA hM₀N' hCM₀
  have hcM₀ : Nat.card M₀ = 322560 := by rw [hM₀eq, hNc]
  have hsurj₀ : Function.Surjective (E16.eNHom hvA hM₀N') := by
    have h1 := card_range_eq hRM₀ (E16.eNHom hvA hM₀N') hker₀
    rw [hRc, hcM₀] at h1
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ (by rw [E16.card_statedSL4]; omega)
  have hO : pCoreOf 2 M₀ = R := pCoreOf_eq_of_surj hRM₀ h.hR2 _ hsurj₀ hker₀
    (noNormalTwo_of_simple not_isPGroup_sl4)
  have hpk : CFSG.pCore 2 ↥M₀ = (E16.eNHom hvA hM₀N').ker := by
    rw [← Hex.pCoreOf_subgroupOf' M₀, hO, hker₀]
  have hpsl : IsPSL 4 2 1 (ModO2 M₀) := E16.isPSL_of_equiv4
    ((QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hsurj₀))
  have hext : IsExt ↥M₀ (fun N _ => IsE2 4 N) (fun Y _ => IsPSL 4 2 1 Y) := by
    have hn : (R.subgroupOf M₀).Normal := by rw [← hker₀]; exact MonoidHom.normal_ker _
    exact ⟨R.subgroupOf M₀, hn, ⟨(Subgroup.subgroupOfEquivOfLe hRM₀).trans
      ((MulEquiv.subgroupCongr hRA).trans (ecoords hvA))⟩, E16.isPSL_of_equiv4
        ((QuotientGroup.quotientMulEquivOfEq hker₀.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective _ hsurj₀))⟩
  have hRCA : R ≤ Subgroup.centralizer (eSub hvA : Set A) := by
    rw [← hRA, hCR]
  have hXC : (M₀ ⊔ R) ⊓ Subgroup.centralizer (eSub hvA : Set A) = R := by
    rw [sup_eq_left.mpr hRM₀, hCM₀]
  have hsum : IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R))
      (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) false 1 := by
    rw [hVeq]
    exact sum_natural_of_surj hvA hM₀N' hRCA hsurj₀ hXC
  have hM₀ : conjClosure M₀ M = M₀ := conjClosure_eq_self' h.hMN
  refine ⟨Or.inr (Or.inr (Or.inl ⟨h.hSs, Or.inr (Or.inl ?_)⟩)),
    Or.inr (Or.inl ⟨4, Or.inr rfl, hpsl, Or.inl ⟨1, le_rfl, hsum⟩⟩), ?_⟩
  · rw [hM₀]
    exact hext
  · refine summand_of_card ?_
    rw [hVR2, hRc]

end CFSG.Quasithin.KGC31.M24

end
