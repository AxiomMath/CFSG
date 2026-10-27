module

public import CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProofM12
public import CFSG.RankThree.PartTwo.Toolkit.M12Facts
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.GH74.M12.Hyp CFSG.RankThree.Asc83Table Subgroup

namespace Step1914MoreSProof

theorem m12a_eq : (CFSG.Sporadic.Mathieu.m12a : G12) =
    wE wES * wE wFR * wE wFW * wE wEW * wE wER * wE wFW * wE wER * wE wFR := by
  rw [eq_iff_tbl]
  simp only [tblG_mul, tbl_wE]
  rw [tbl_m12gA]
  decide +kernel

theorem m12b_eq : (CFSG.Sporadic.Mathieu.m12b : G12) =
    wE wFR * wE wEW * wE wFW * wE wER * wE wEW * wE wER * wE wFW * wE wEW * wE wER * wE wES := by
  rw [eq_iff_tbl]
  simp only [tblG_mul, tbl_wE]
  rw [tbl_m12gB]
  decide +kernel

theorem normalizer_E_sup_normalizer_F :
    normalizer (E : Set G12) ⊔ normalizer (F : Set G12) = ⊤ := by
  have hg : ∀ w, tbl (wE w).1 = wordT w := tbl_wE
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := gl_tables
  set N := normalizer (E : Set G12) ⊔ normalizer (F : Set G12) with hN
  have hE : ∀ {g : G12}, g ∈ normalizer (closure (Set.range basisE.vec) : Set G12) → g ∈ N :=
    fun hg' => le_sup_left (a := normalizer (E : Set G12)) (by rwa [basisE.closure_range] at hg')
  have hF : ∀ {g : G12}, g ∈ normalizer (closure (Set.range basisF.vec) : Set G12) → g ∈ N :=
    fun hg' => le_sup_right (b := normalizer (F : Set G12)) (by rwa [basisF.closure_range] at hg')
  have hER : wE wER ∈ N := hE (basisE.mem_normalizer_of_conj 2 2 0 2
    (conj_eq_of_tbl (hg _) tbl_z tbl_z tbl_x h1) (conj_eq_of_tbl (hg _) tbl_x tbl_z tbl_x h2))
  have hES : wE wES ∈ N := hE (basisE.mem_normalizer_of_conj 2 0 0 1
    (conj_eq_of_tbl (hg _) tbl_z tbl_z tbl_x h3) (conj_eq_of_tbl (hg _) tbl_x tbl_z tbl_x h4))
  have hEW : wE wEW ∈ N := hE (basisE.mem_normalizer_of_conj 0 1 1 0
    (conj_eq_of_tbl (hg _) tbl_z tbl_z tbl_x h5) (conj_eq_of_tbl (hg _) tbl_x tbl_z tbl_x h6))
  have hFR : wE wFR ∈ N := hF (basisF.mem_normalizer_of_conj 2 2 0 2
    (conj_eq_of_tbl (hg _) tbl_z tbl_z tbl_y h7) (conj_eq_of_tbl (hg _) tbl_y tbl_z tbl_y h8))
  have hFW : wE wFW ∈ N := hF (basisF.mem_normalizer_of_conj 0 1 1 0
    (conj_eq_of_tbl (hg _) tbl_z tbl_z tbl_y h11) (conj_eq_of_tbl (hg _) tbl_y tbl_z tbl_y h12))
  have ha : (CFSG.Sporadic.Mathieu.m12a : G12) ∈ N := by
    rw [m12a_eq]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hES hFR) hFW) hEW) hER)
      hFW) hER) hFR
  have hb : (CFSG.Sporadic.Mathieu.m12b : G12) ∈ N := by
    rw [m12b_eq]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hFR
      hEW) hFW) hER) hEW) hER) hFW) hEW) hER) hES
  rw [eq_top_iff, ← CFSG.Sporadic.Mathieu.closure_pair_eq_top CFSG.Sporadic.Mathieu.m12_eq
    CFSG.Sporadic.Mathieu.m12a.2 CFSG.Sporadic.Mathieu.m12b.2, closure_le]
  rintro g (rfl | rfl)
  · exact ha
  · exact hb

@[expose] def NormGenAt (G : Type) [Group G] (P : Subgroup G) : Prop :=
  ∀ E₀ F₀ : Subgroup G, E₀ ≤ P → F₀ ≤ P → E₀ ≠ F₀ → Nat.card E₀ = 9 → Nat.card F₀ = 9 →
    Nonempty (Sec4.autIn ⊤ E₀ ≃* GL (Fin 2) (ZMod 3)) →
    Nonempty (Sec4.autIn ⊤ F₀ ≃* GL (Fin 2) (ZMod 3)) →
      normalizer (E₀ : Set G) ⊔ normalizer (F₀ : Set G) = ⊤

theorem normGenAt_map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') {P : Subgroup G}
    (h : NormGenAt G P) : NormGenAt G' (P.map φ.toMonoidHom) := by
  intro E₀ F₀ hE hF hne hE9 hF9 ⟨eE⟩ ⟨eF⟩
  have hle : ∀ {B : Subgroup G'}, B ≤ P.map φ.toMonoidHom → B.map φ.symm.toMonoidHom ≤ P := by
    intro B hB
    have h1 := Subgroup.map_mono (f := φ.symm.toMonoidHom) hB
    rwa [Sec4.Sporadic.map_symm_map] at h1
  have hcard : ∀ {B : Subgroup G'}, Nat.card B = 9 → Nat.card (B.map φ.symm.toMonoidHom) = 9 :=
    fun hB => by rw [Subgroup.card_map_of_injective φ.symm.injective, hB]
  have hne' : E₀.map φ.symm.toMonoidHom ≠ F₀.map φ.symm.toMonoidHom := fun heq => by
    apply hne
    rw [← Sec4.Sporadic.map_map_symm φ E₀, ← Sec4.Sporadic.map_map_symm φ F₀, heq]
  have hgen := h _ _ (hle hE) (hle hF) hne' (hcard hE9) (hcard hF9)
    ⟨(Sec4.Sporadic.autInTopCongr φ.symm E₀).symm.trans eE⟩
    ⟨(Sec4.Sporadic.autInTopCongr φ.symm F₀).symm.trans eF⟩
  have hmap := congrArg (Subgroup.map φ.toMonoidHom) hgen
  rw [Subgroup.map_sup, ← Toolkit.normalizer_map_equiv, ← Toolkit.normalizer_map_equiv,
    Sec4.Sporadic.map_map_symm, Sec4.Sporadic.map_map_symm,
    Subgroup.map_top_of_surjective _ φ.surjective] at hmap
  exact hmap

theorem normGenAt_P0 :
    NormGenAt G12 P0 := by
  intro E₀ F₀ hE hF hne hE9 hF9 hEa hFa
  have hmem : ∀ {B : Subgroup G12}, B ≤ P0 → Nat.card B = 9 →
      Nonempty (Sec4.autIn ⊤ B ≃* GL (Fin 2) (ZMod 3)) → B = E ∨ B = F := by
    intro B hB hB9 ⟨e⟩
    have hB' : B ∈ ({E, F, A, A'} : Set (Subgroup G12)) := nine_eq ▸ ⟨hB, hB9⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB'
    have h48 : Nat.card (Sec4.autIn ⊤ B) = 48 := by
      rw [Nat.card_congr e.toEquiv]
      exact card_GL23
    rcases hB' with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rw [h, Sec4.Sporadic.card_autIn_top, card_automizer_A] at h48
      omega
    · exfalso
      obtain ⟨eA⟩ := automizer_A'
      rw [h, Sec4.Sporadic.card_autIn_top, Nat.card_congr eA.toEquiv, Nat.card_perm,
        Nat.card_eq_fintype_card, Fintype.card_fin] at h48
      norm_num [Nat.factorial] at h48
  rcases hmem hE hE9 hEa with rfl | rfl <;> rcases hmem hF hF9 hFa with rfl | rfl
  · exact absurd rfl hne
  · exact normalizer_E_sup_normalizer_F
  · rw [sup_comm]
    exact normalizer_E_sup_normalizer_F
  · exact absurd rfl hne

end Step1914MoreSProof

open Step1914MoreSProof in
theorem step1914MoreM12Gen :
    Step1914MoreM12Gen := by
  intro X _ _ hX E₀ F₀ hne hp hE9 hF9 hEa hFa
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  exact Sec4.Sporadic.forall_sylow_of_P0 NormGenAt (fun _ _ _ _ φ _ h => normGenAt_map φ h)
    normGenAt_P0 X hX S E₀ F₀ (le_sup_left.trans hS) (le_sup_right.trans hS) hne hE9 hF9 hEa hFa

open Step1914MoreSProof in
theorem step1914MoreSM12_of
    (htri : Step1914Tri) (h131 : Sec13.Item131) (h132 : Sec13.Item132) (h133 : Sec13.Item133)
    (h134 : Sec13.Item134) (h48 : Sec4.Item4_8) (h13S : Sec17.Item13Setup)
    (hPGL : Sec13.Item137InvertPGL) (h195 : Item195) : Step1914MoreSM12 :=
  step1914MoreSM12_of_gen htri h131 h132 h133 h134 h48 h13S hPGL h195 step1914MoreM12Gen

end CFSG.RankThree.PartTwo.Sec19
