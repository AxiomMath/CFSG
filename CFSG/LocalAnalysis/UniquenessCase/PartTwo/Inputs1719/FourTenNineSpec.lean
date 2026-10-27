module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenNineModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenNineCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Spec
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenQ9

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6
  CFSG.LocalAnalysis.WeakClosure81.NFA6.Core

theorem psl29_le_of_genCheck {L : List (List ℕ)} {words : List (List (List ℕ))}
    (h : genCheck L words = true) {H : Subgroup P10} (hL : ∀ c ∈ L, ∃ x ∈ H, code x = c) :
    A6Models.psl29 ≤ H := by
  have hgens : ∀ j : ℕ, j < 3 → pslGens.getD j 1 ∈ H := by
    intro j hj
    have h2 := List.all_eq_true.mp h j (List.mem_range.mpr hj)
    simp only [wordOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h2
    obtain ⟨hletters, hprod⟩ := h2
    have hmem : ∀ a ∈ words.getD j [], ∃ σ ∈ H, code σ = a :=
      fun a ha => hL a (List.contains_iff_mem.mp (hletters a ha))
    obtain ⟨σ, hσH, hσc⟩ := eval_word_mem (words.getD j []) 1 H.one_mem hmem
    rw [code_one] at hσc
    have hgc : code (pslGens.getD j 1) = Core.pslGenC.getD j [] := by
      rw [← pslGens_code]
      have hj' : j < pslGens.length := by simpa [pslGens] using hj
      exact (getD_map_code pslGens j hj').symm
    have e : σ = pslGens.getD j 1 := code_injective (by rw [hσc, hprod, hgc])
    rw [← e]
    exact hσH
  rw [psl29_eq, closure_le]
  intro g hg
  simp only [pslGens, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
  rcases hg with rfl | rfl | rfl
  · exact hgens 0 (by norm_num)
  · exact hgens 1 (by norm_num)
  · exact hgens 2 (by norm_num)

theorem mem_map_conj_iff {T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    {E : List (List ℕ)} (hET : E.all TL.contains = true) {A : Subgroup P10}
    (hA : ∀ x, x ∈ A ↔ code x ∈ E) (γ x : P10) :
    x ∈ A.map (MulAut.conj γ).toMonoidHom ↔ code x ∈ conjL (code γ) (code γ⁻¹) E := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [conjL, List.mem_map]
    refine ⟨code a, (hA a).mp ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← code_mul, ← code_mul]
  · intro hx
    rw [conjL, List.mem_map] at hx
    obtain ⟨e, he, hee⟩ := hx
    have heTL : e ∈ TL := List.contains_iff_mem.mp (List.all_eq_true.mp hET e he)
    obtain ⟨a, ha, rfl⟩ := hT.surj e heTL
    refine ⟨a, (hA a).mpr he, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    apply code_injective
    rw [code_mul, code_mul]
    exact hee

theorem code_mem_centL {T₀ B : Subgroup P10} {TL F : List (List ℕ)} (hT : Desc T₀ TL)
    (hFT : F.all TL.contains = true) (hB : ∀ x, x ∈ B ↔ code x ∈ F) {x : P10}
    (hx : x ∈ T₀ ⊓ centralizer (B : Set P10)) : code x ∈ centL TL F := by
  rw [centL, List.mem_filter]
  refine ⟨(hT.mem x).mp hx.1, ?_⟩
  rw [List.all_eq_true]
  intro f hf
  have hfTL : f ∈ TL := List.contains_iff_mem.mp (List.all_eq_true.mp hFT f hf)
  obtain ⟨b, hb, rfl⟩ := hT.surj f hfTL
  rw [ccomm_iff]
  exact (Subgroup.mem_centralizer_iff.mp hx.2 b ((hB b).mpr hf)).symm

private theorem sup_eq_of_desc_genCheck {G T₀ K : Subgroup P10} {TL KL : List (List ℕ)}
    (hT : Desc T₀ TL) (hK : Desc K KL) (hKG : K ≤ G) (hsup : A6Models.psl29 ⊔ T₀ = G)
    {words : List (List (List ℕ))} (hw : genCheck (KL ++ TL) words = true) : K ⊔ T₀ = G := by
  have hle : A6Models.psl29 ≤ K ⊔ T₀ := by
    refine psl29_le_of_genCheck hw (H := K ⊔ T₀) ?_
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨x, hx, rfl⟩ := hK.surj c hc
      exact ⟨x, Subgroup.mem_sup_left hx, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := hT.surj c hc
      exact ⟨x, Subgroup.mem_sup_right hx, rfl⟩
  refine le_antisymm ?_ ?_
  · exact sup_le hKG (hsup ▸ le_sup_right)
  · rw [← hsup]
    exact sup_le hle le_sup_right

theorem fourTenMember_of_sThreeCheck {G T₀ B : Subgroup P10} {TL F : List (List ℕ)}
    (hT : Desc T₀ TL) (hT2 : IsPGroup 2 T₀) (hsup : A6Models.psl29 ⊔ T₀ = G)
    (hFT : F.all TL.contains = true) (hB : ∀ x, x ∈ B ↔ code x ∈ F)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) {en : FTEntry} (h : sThreeCheck TL F en = true)
    (hw : genCheck (en.K.lit ++ TL) en.words = true) : FourTenMember G T₀ B := by
  simp only [sThreeCheck, Bool.and_eq_true, and_assoc, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨hok, hgc, hcent, hlen, hk, hki, hkmul, he, hnot⟩ := h
  have hgcS : ∀ c ∈ en.K.gc, ∃ x ∈ (A6Models.psl29 : Set P10) ∪ (T₀ : Set P10), code x = c := by
    intro c hc
    have h1 : pslLit.contains c = true ∨ TL.contains c = true := by
      simpa only [Bool.or_eq_true] using List.all_eq_true.mp hgc c hc
    rcases h1 with h1 | h1
    · obtain ⟨x, hx, rfl⟩ := exists_psl29_of_code (List.contains_iff_mem.mp h1)
      exact ⟨x, Set.mem_union_left _ hx, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := hT.surj c (List.contains_iff_mem.mp h1)
      exact ⟨x, Set.mem_union_right _ hx, rfl⟩
  obtain ⟨K, hKle, hK, hKnd⟩ := SubData.exists_desc hok hgcS
  have hS : Subgroup.closure ((A6Models.psl29 : Set P10) ∪ (T₀ : Set P10)) = G := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, hsup]
  rw [hS] at hKle
  have hcenK : T₀ ⊓ centralizer (B : Set P10) ≤ K := by
    intro x hx
    exact (hK.mem x).mpr (List.contains_iff_mem.mp (List.all_eq_true.mp hcent (code x)
      (code_mem_centL hT hFT hB hx)))
  have hcardK : Nat.card K = en.K.lit.length := hK.card hKnd
  have hcardKT : Nat.card (K ⊓ T₀ : Subgroup P10) = (en.K.lit.filter TL.contains).length :=
    (hK.inf hT).card (hKnd.filter _)
  have hcard3 : Nat.card K = 3 * Nat.card (K ⊓ T₀ : Subgroup P10) := by
    rw [hcardK, hcardKT, hlen]
  obtain ⟨κ, hκK, hκc⟩ := hK.surj en.k (List.contains_iff_mem.mp hk)
  obtain ⟨κ', hκ'K, hκ'c⟩ := hK.surj en.ki (List.contains_iff_mem.mp hki)
  have hκ'inv : κ' = κ⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    apply code_injective
    rw [code_mul, hκc, hκ'c, hkmul, code_one]
  have heF : en.e ∈ F := List.contains_iff_mem.mp he
  have heTL : en.e ∈ TL := List.contains_iff_mem.mp (List.all_eq_true.mp hFT en.e heF)
  obtain ⟨ε, hεT, hεc⟩ := hT.surj en.e heTL
  have hεB : ε ∈ B := (hB ε).mpr (by rw [hεc]; exact heF)
  have hεcen : ε ∈ centralizer (B : Set P10) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hBc b hb ε hεB
  have hεKT : ε ∈ K ⊓ T₀ := ⟨hcenK ⟨hεT, hεcen⟩, hεT⟩
  have hcode : code (κ * ε * κ⁻¹) = cmul (cmul en.k en.e) en.ki := by
    rw [code_mul, code_mul, hκc, hεc, ← hκ'inv, hκ'c]
  have hnot' : cmul (cmul en.k en.e) en.ki ∉ en.K.lit.filter TL.contains := by
    intro hmem
    rw [List.contains_iff_mem.mpr hmem] at hnot
    exact Bool.noConfusion hnot
  have hnotKT : κ * ε * κ⁻¹ ∉ K ⊓ T₀ := by
    intro hmem
    exact hnot' (hcode ▸ ((hK.inf hT).mem (κ * ε * κ⁻¹)).mp hmem)
  have hNK : ¬ K ≤ Subgroup.normalizer ((K ⊓ T₀ : Subgroup P10) : Set P10) := by
    intro hle
    exact hnotKT ((Subgroup.mem_normalizer_iff.mp (hle hκK) ε).mp hεKT)
  have hrel : (K ⊓ T₀ : Subgroup P10).relIndex K = 3 := by
    have h := Subgroup.relIndex_mul_card (H := K ⊓ T₀) (K := K)
    rw [inf_eq_left.mpr inf_le_left, hcard3] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hSyl : IsSylowIn 2 (K ⊓ T₀) K :=
    ⟨inf_le_left, hT2.to_le inf_le_right, by rw [hrel]; norm_num⟩
  have hOle : pCoreOf 2 K ≤ K ⊓ T₀ := pCoreOf_le_of_isSylowIn hSyl
  have hAO : ¬ B ≤ pCoreOf 2 K := by
    intro hle
    have hεO : ε ∈ pCoreOf 2 K := hle hεB
    have hκN : κ ∈ Subgroup.normalizer (pCoreOf 2 K : Set P10) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hκK
    exact hnotKT (hOle ((Subgroup.mem_normalizer_iff.mp hκN ε).mp hεO))
  exact Or.inl ⟨K, hKle, hcenK, hcard3, hNK, hAO,
    sup_eq_of_desc_genCheck hT hK hKle hsup hw⟩

theorem fourTenMember_of_cFiveCheck {G T₀ B : Subgroup P10} {TL F : List (List ℕ)}
    (hT : Desc T₀ TL) (hsup : A6Models.psl29 ⊔ T₀ = G) (hFT : F.all TL.contains = true)
    (hB : ∀ x, x ∈ B ↔ code x ∈ F) {en : FTEntry} (h : cFiveCheck TL F en = true)
    (hw : genCheck (en.K.lit ++ TL) en.words = true) : FourTenMember G T₀ B := by
  simp only [cFiveCheck, Bool.and_eq_true, and_assoc, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨hok, hgc, hkL, hlen, hcent, he, hne⟩ := h
  obtain ⟨ξ, hξpsl, hξc⟩ := exists_psl29_of_code (List.contains_iff_mem.mp hkL)
  obtain ⟨hK, hKnd⟩ := SubData.spec hok (gens := [ξ]) (by rw [hgc]; simp [hξc])
  have hKdef : Subgroup.closure {g | g ∈ [ξ]} = Subgroup.zpowers ξ := by
    rw [Subgroup.zpowers_eq_closure]
    congr 1
    ext g
    simp
  have hξG : ξ ∈ G := by
    rw [← hsup]
    exact Subgroup.mem_sup_left hξpsl
  have hKG : Subgroup.closure {g | g ∈ [ξ]} ≤ G := hKdef ▸ Subgroup.zpowers_le.mpr hξG
  have horder : orderOf ξ = 5 := by
    rw [← Nat.card_zpowers, ← hKdef, hK.card hKnd, hlen]
  have hcenN : T₀ ⊓ centralizer (B : Set P10) ≤
      Subgroup.normalizer (Subgroup.zpowers ξ : Set P10) := by
    intro t ht
    have h1 : t ∈ Subgroup.normalizer
        (Subgroup.closure {g | g ∈ [ξ]} : Set P10) :=
      normT_spec hK (List.all_eq_true.mp hcent (code t) (code_mem_centL hT hFT hB ht)) rfl
    rwa [hKdef] at h1
  have heF : en.e ∈ F := List.contains_iff_mem.mp he
  have heTL : en.e ∈ TL := List.contains_iff_mem.mp (List.all_eq_true.mp hFT en.e heF)
  obtain ⟨ε, hεT, hεc⟩ := hT.surj en.e heTL
  have hεB : ε ∈ B := (hB ε).mpr (by rw [hεc]; exact heF)
  have hεξ : ε * ξ ≠ ξ * ε := by
    intro hc
    have h1 : ccomm (code ε) (code ξ) = true := ccomm_iff.mpr hc
    rw [hεc, hξc, hne] at h1
    exact Bool.noConfusion h1
  refine Or.inr ⟨ξ, hξG, horder, hcenN, ⟨ε, hεB, hεξ⟩, ?_⟩
  have h := sup_eq_of_desc_genCheck hT hK hKG hsup hw
  rwa [hKdef] at h

theorem ftEntry_spec {G T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    (hT2 : IsPGroup 2 T₀) (hsup : A6Models.psl29 ⊔ T₀ = G) {en : FTEntry}
    (h : ftEntryCheck TL en = true) {A : Subgroup P10} (hAe : IsElemAbelian 2 A)
    (hA : ∀ x, x ∈ A ↔ code x ∈ en.E) :
    ∃ g ∈ G, A.map (MulAut.conj g).toMonoidHom ≤ T₀ ∧
      FourTenMember G T₀ (A.map (MulAut.conj g).toMonoidHom) := by
  simp only [ftEntryCheck, Bool.and_eq_true, and_assoc, beq_iff_eq] at h
  obtain ⟨hET, hgL, hgiL, hgmul, hconj, hbif, hw⟩ := h
  obtain ⟨γ, hγpsl, hγc⟩ := exists_psl29_of_code (List.contains_iff_mem.mp hgL)
  obtain ⟨γ', hγ'psl, hγ'c⟩ := exists_psl29_of_code (List.contains_iff_mem.mp hgiL)
  have hγ'inv : γ' = γ⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    apply code_injective
    rw [code_mul, hγc, hγ'c, hgmul, code_one]
  set B : Subgroup P10 := A.map (MulAut.conj γ).toMonoidHom with hBdef
  have hB : ∀ x, x ∈ B ↔ code x ∈ conjL en.g en.gi en.E := by
    intro x
    rw [hBdef, mem_map_conj_iff hT hET hA γ x, hγc, ← hγ'inv, hγ'c]
  have hBT : B ≤ T₀ := by
    intro x hx
    exact (hT.mem x).mpr (List.contains_iff_mem.mp (List.all_eq_true.mp hconj (code x)
      ((hB x).mp hx)))
  have hBe : IsElemAbelian 2 B := by
    rw [hBdef]
    exact hAe.map (MulAut.conj γ).toMonoidHom
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => hBe.comm ha hb
  refine ⟨γ, ?_, hBT, ?_⟩
  · rw [← hsup]
    exact Subgroup.mem_sup_left hγpsl
  · cases hfive : en.five
    · rw [hfive, Bool.cond_false] at hbif
      exact fourTenMember_of_sThreeCheck hT hT2 hsup hconj hB hBc hbif hw
    · rw [hfive, Bool.cond_true] at hbif
      exact fourTenMember_of_cFiveCheck hT hsup hconj hB hbif hw

theorem fourTenModel_of_check {G T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    (hsyl : IsSylowIn 2 T₀ G) (hsup : A6Models.psl29 ⊔ T₀ = G) {ens : List FTEntry}
    (hseed : seedCheck TL (ens.map FTEntry.E) = true)
    (hens : ens.all (ftEntryCheck TL) = true) : FourTenModel G T₀ := by
  refine ⟨hsyl, fun A hAT hAe hA4 => ?_⟩
  obtain ⟨E, hE, hAE⟩ := seed_spec hT hseed hAT hAe hA4
  obtain ⟨en, hen, rfl⟩ := List.mem_map.mp hE
  exact ftEntry_spec hT hsyl.2.1 hsup (List.all_eq_true.mp hens en hen) hAe hAE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenQ9
