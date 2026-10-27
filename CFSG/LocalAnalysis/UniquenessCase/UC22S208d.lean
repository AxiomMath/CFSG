module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20b
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s208d_shape_cases (hE : UC22P20gExcFacts) {X : Type} [Group X] (hs : UC22P20gShape X)
    (hnab : ∃ a b : X, a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple X ∨ (∃ n : ℕ, 2 < n ∧ IsSzL2Product X n) ∨ IsSU3CentralSquare X := by
  rcases hs with ⟨n, hn, h | h | h | h | h | h | h | h | h | h | h | h | h | h⟩ | h | h | h | h |
      h | ⟨n, hn, h⟩ | h
  · exact Or.inl (uc22p20g_qs_Sz hnab h).1
  · exact Or.inl (uc22p20g_qs_L2 hnab hn h).1
  · exact Or.inl (uc22p20g_qs_L3 hnab hn h).1
  · exact Or.inl (uc22p20g_qs_U3 hnab hn h).1
  · exact Or.inl (uc22p20g_qs_L4 hnab hn h).1
  · exact Or.inl (uc22p20g_qs_U4 hnab (by omega) h).1
  · exact Or.inl (uc22p20g_qs_G2 hE hnab (by omega) h).1
  · exact Or.inl (uc22p20g_qs_3D4 hE hnab (by omega) h).1
  · exact Or.inl (uc22p20g_qs_2F4 hE hnab (by omega) h).1
  · exact Or.inl (uc22p20g_qs_Sp4 hnab hn h).1
  · exact Or.inl (uc22p20g_qs_SL3 hn h).1
  · exact Or.inl (uc22p20g_qs_SU3 hn h).1
  · exact Or.inl (uc22p20g_qs_Sp6 hnab hn h).1
  · exact Or.inl (uc22p20g_qs_Om8m hnab (by omega) h).1
  · exact Or.inl (uc22p20g_qs_U4 hnab le_rfl h).1
  · exact Or.inl (uc22p20g_qs_U5 hnab le_rfl h).1
  · exact Or.inl (uc22p20g_qs_Om8m hnab (by norm_num) h).1
  · exact Or.inl (uc22p20g_qs_3D4 hE hnab (by norm_num) h).1
  · exact Or.inl (uc22p20g_qs_3D4 hE hnab (by norm_num) h).1
  · exact Or.inr (Or.inl ⟨n, hn, h⟩)
  · exact Or.inr (Or.inr h)

theorem s208d_orbit_two (D : Data G) (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h1930 : H1930 D)
    {C : Subgroup G} (hL : uc22p20bOrb D.T C ∈ calL D.T D.M)
    (hC : C ∈ calC (uc22p20bOrb D.T C)) {t : G} (ht : t ∈ D.T) (hne : uc22p20bCj t C ≠ C) :
    (∀ s ∈ D.T, uc22p20bCj s C = C ∨ uc22p20bCj s C = uc22p20bCj t C) ∧
      ((∃ n : ℕ, 2 < n ∧ IsSzL2Product (Bar2 (uc22p20bOrb D.T C)) n ∧
          (IsSz (Bar2 C) n ∨ IsL2 (Bar2 C) n)) ∨
        (IsSU3CentralSquare (Bar2 (uc22p20bOrb D.T C)) ∧ IsSU3 (Bar2 C) 3)) := by
  set L := uc22p20bOrb D.T C
  have hOT : OTwoE ↥L = ⊤ := uc22p20o_oTwoE_top D hL
  have hcC : CFSG.Quasithin.cComp L = Set.range (fun s : D.T => uc22p20bCj (s : G) C) :=
    uc22p20p_cComp_eq_range D hL hC rfl
  have hmem : ∀ s ∈ D.T, uc22p20bCj s C ∈ CFSG.Quasithin.cComp L := fun s hs => by
    rw [hcC]
    exact ⟨⟨s, hs⟩, rfl⟩
  have hle : ∀ s ∈ D.T, uc22p20bCj s C ≤ L := fun s hs => uc22p20b_cj_le_orb hs
  have hCt : uc22p20bCj 1 C = C := uc22p20b_cj_one C
  let img : Subgroup G → Subgroup (Bar2 L) := fun K =>
    (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hiso : ∀ s ∈ D.T, Nonempty (Bar2 C ≃* ↥(img (uc22p20bCj s C))) := by
    intro s hs
    obtain ⟨e, -⟩ := uc22p20d_bar2Equiv (hle s hs)
      (CFSG.Quasithin.subnormal_of_mem_cComp (hmem s hs))
    obtain ⟨f⟩ := uc22p20d_bar2_conj s C
    exact ⟨f.trans e⟩
  have hqs : ∀ s ∈ D.T, CFSG.Open.IsQuasisimple ↥(img (uc22p20bCj s C)) := by
    intro s hs
    obtain ⟨e⟩ := hiso s hs
    exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hC.2.2
  have hnab : ∀ s ∈ D.T, ∃ a ∈ img (uc22p20bCj s C), ∃ b ∈ img (uc22p20bCj s C), a * b ≠ b * a := by
    intro s hs
    obtain ⟨a, b, hab⟩ := uc22p20g_nonab_of_quasisimple (hqs s hs)
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  have hcomm : ∀ s ∈ D.T, ∀ s' ∈ D.T, uc22p20bCj s C ≠ uc22p20bCj s' C →
      ∀ a ∈ img (uc22p20bCj s C), ∀ b ∈ img (uc22p20bCj s' C), a * b = b * a :=
    fun s hs s' hs' hne' => uc22p20d_commute_images hOT (hmem s hs) (hmem s' hs') hne'
  have hinj : ∀ s ∈ D.T, ∀ s' ∈ D.T, uc22p20bCj s C ≠ uc22p20bCj s' C →
      img (uc22p20bCj s C) ≠ img (uc22p20bCj s' C) := by
    intro s hs s' hs' hne' heq
    obtain ⟨a, ha, b, hb, hab⟩ := hnab s hs
    exact hab (hcomm s hs s' hs' hne' a ha b (heq ▸ hb))
  have hsup : ⨆ s : D.T, img (uc22p20bCj (s : G) C) = ⊤ := by
    have h1 : ⨆ s : D.T, (uc22p20bCj (s : G) C).subgroupOf L = ⊤ := by
      apply Subgroup.map_injective L.subtype_injective
      rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
      have h2 : ∀ s : D.T, ((uc22p20bCj (s : G) C).subgroupOf L).map L.subtype =
          uc22p20bCj (s : G) C := fun s => Subgroup.map_subgroupOf_eq_of_le (hle s s.2)
      simp_rw [h2]
      rfl
    show ⨆ s : D.T,
      ((uc22p20bCj (s : G) C).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤
    rw [← Subgroup.map_iSup, h1, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hnorm : ∀ s ∈ D.T, (img (uc22p20bCj s C)).Normal := by
    intro s hs
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    refine iSup_le fun s' => ?_
    by_cases h : uc22p20bCj (s' : G) C = uc22p20bCj s C
    · rw [h]
      exact Subgroup.le_normalizer
    · refine le_trans (fun b hb => ?_) (Subgroup.centralizer_le_normalizer _)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm s hs s' s'.2 (fun e => h e.symm) a ha b hb
  have hsn : ∀ s ∈ D.T, CFSG.Open.IsSubnormal (img (uc22p20bCj s C)) ⊤ := fun s hs =>
    .step le_top ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).2
      (Subgroup.normalizer_eq_top_iff.2 (hnorm s hs)).ge) (.refl ⊤)
  have horb : ∀ N₁ N₂ : Subgroup (Bar2 L),
      (∀ s ∈ D.T, img (uc22p20bCj s C) = N₁ ∨ img (uc22p20bCj s C) = N₂) →
      ∀ s ∈ D.T, uc22p20bCj s C = C ∨ uc22p20bCj s C = uc22p20bCj t C := by
    intro N₁ N₂ hfac s hs
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have d1 := hinj s hs 1 D.T.one_mem (by rw [hCt]; exact h1)
    have d2 := hinj s hs t ht h2
    have d3 := hinj t ht 1 D.T.one_mem (by rw [hCt]; exact hne)
    rcases hfac s hs with e1 | e1 <;> rcases hfac 1 D.T.one_mem with e2 | e2 <;>
      rcases hfac t ht with e3 | e3 <;>
      first
        | exact d1 (e1.trans e2.symm)
        | exact d2 (e1.trans e3.symm)
        | exact d3 (e3.trans e2.symm)
  have hshape : UC22P20gShape (Bar2 L) := h207 h1930 L hL
  have hLnab : ∃ a b : Bar2 L, a * b ≠ b * a := by
    obtain ⟨a, -, b, -, hab⟩ := hnab 1 D.T.one_mem
    exact ⟨a, b, hab⟩
  obtain ⟨φ⟩ := hiso 1 D.T.one_mem
  rcases s208d_shape_cases hE hshape hLnab with hq | ⟨n, hn, hP⟩ | hSq
  ·
    exfalso
    have hN₂ : (⨆ (s : D.T) (_ : uc22p20bCj (s : G) C ≠ C), img (uc22p20bCj (s : G) C)) ≤
        centralizer (img C : Set (Bar2 L)) := by
      refine iSup₂_le fun s h b hb => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [← hCt] at ha
      exact hcomm 1 D.T.one_mem s s.2 (by rw [hCt]; exact fun e => h e.symm) a ha b hb
    refine uc22p20g_not_quasisimple_of_commuting hq (N₁ := img C)
      (N₂ := ⨆ (s : D.T) (_ : uc22p20bCj (s : G) C ≠ C), img (uc22p20bCj (s : G) C)) ?_ ?_ ?_ ?_
    · rw [eq_top_iff, ← hsup]
      refine iSup_le fun s => ?_
      by_cases h : uc22p20bCj (s : G) C = C
      · rw [h]
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le s h le_rfl)
    · exact fun a ha b hb => Subgroup.mem_centralizer_iff.1 (hN₂ hb) a ha
    · have h1 := hnab 1 D.T.one_mem
      rw [hCt] at h1
      exact h1
    · obtain ⟨a, ha, b, hb, hab⟩ := hnab t ht
      have hle₂ : img (uc22p20bCj t C) ≤
          ⨆ (s : D.T) (_ : uc22p20bCj (s : G) C ≠ C), img (uc22p20bCj (s : G) C) :=
        le_iSup₂_of_le (f := fun (s : D.T) (_ : uc22p20bCj (s : G) C ≠ C) =>
          img (uc22p20bCj (s : G) C)) ⟨t, ht⟩ hne le_rfl
      exact ⟨a, hle₂ ha, b, hle₂ hb, hab⟩
  ·
    obtain ⟨A, B, _, _, ⟨e⟩, hA, hB⟩ := hP
    let f₁ : A →* Bar2 L := e.symm.toMonoidHom.comp (MonoidHom.inl A B)
    let f₂ : B →* Bar2 L := e.symm.toMonoidHom.comp (MonoidHom.inr A B)
    have hf₁ : Function.Injective f₁ :=
      e.symm.injective.comp (fun a a' h => by simpa using congrArg Prod.fst h)
    have hf₂ : Function.Injective f₂ :=
      e.symm.injective.comp (fun b b' h => by simpa using congrArg Prod.snd h)
    have hx : ∀ x : Bar2 L, x = f₁ (e x).1 * f₂ (e x).2 := by
      intro x
      simp only [f₁, f₂, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
        MulEquiv.coe_toMonoidHom]
      rw [← map_mul]
      simp
    have hsup₁₂ : f₁.range ⊔ f₂.range = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [hx x]
      exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
    have hcomm₁₂ : ∀ a ∈ f₁.range, ∀ b ∈ f₂.range, a * b = b * a := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      simp only [f₁, f₂, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
        MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul]
      simp
    have hAs := uc22p20g_simple_nonab_SzL2 hn hA
    have hBs := uc22p20g_simple_nonab_SzL2 hn hB
    have hAq : CFSG.Open.IsQuasisimple A := by
      have := hAs.1
      exact uc22p22a_isQuasisimple_of_simple hAs.2
    have hBq : CFSG.Open.IsQuasisimple B := by
      have := hBs.1
      exact uc22p22a_isQuasisimple_of_simple hBs.2
    have hq₁ : CFSG.Open.IsQuasisimple ↥f₁.range :=
      CFSG.Open.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hf₁).symm hAq
    have hq₂ : CFSG.Open.IsQuasisimple ↥f₂.range :=
      CFSG.Open.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hf₂).symm hBq
    have hfac : ∀ s ∈ D.T, img (uc22p20bCj s C) = f₁.range ∨ img (uc22p20bCj s C) = f₂.range :=
      fun s hs => uc22p20g_eq_of_components hsup₁₂ hcomm₁₂ hq₁ hq₂ (hqs s hs) (hsn s hs)
    refine ⟨horb _ _ hfac, Or.inl ⟨n, hn, ⟨A, B, inferInstance, inferInstance, ⟨e⟩, hA, hB⟩, ?_⟩⟩
    rcases hfac 1 D.T.one_mem with h | h
    · have ψ : Bar2 C ≃* A :=
        φ.trans ((MulEquiv.subgroupCongr h).trans (MonoidHom.ofInjective hf₁).symm)
      rcases hA with hA | hA
      · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv ψ.symm hA)
      · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv ψ.symm hA)
    · have ψ : Bar2 C ≃* B :=
        φ.trans ((MulEquiv.subgroupCongr h).trans (MonoidHom.ofInjective hf₂).symm)
      rcases hB with hB | hB
      · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv ψ.symm hB)
      · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv ψ.symm hB)
  ·
    have hSq' := hSq
    obtain ⟨K₁, K₂, hsup₁₂, hcomm₁₂, hK₁, hK₂, -⟩ := hSq'
    have hfac : ∀ s ∈ D.T, img (uc22p20bCj s C) = K₁ ∨ img (uc22p20bCj s C) = K₂ :=
      fun s hs => uc22p20g_eq_of_components hsup₁₂ hcomm₁₂ hK₁.1 hK₂.1 (hqs s hs) (hsn s hs)
    refine ⟨horb _ _ hfac, Or.inr ⟨hSq, ?_⟩⟩
    rcases hfac 1 D.T.one_mem with h | h
    · exact uc22p20p_isSU3_of_mulEquiv (φ.trans (MulEquiv.subgroupCongr h)).symm hK₁
    · exact uc22p20p_isSU3_of_mulEquiv (φ.trans (MulEquiv.subgroupCongr h)).symm hK₂

theorem s208d_orb_eq_sup (D : Data G) (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h1930 : H1930 D)
    {C : Subgroup G} (hL : uc22p20bOrb D.T C ∈ calL D.T D.M)
    (hC : C ∈ calC (uc22p20bOrb D.T C)) {t : G} (ht : t ∈ D.T) (hne : uc22p20bCj t C ≠ C) :
    uc22p20bOrb D.T C = C ⊔ uc22p20bCj t C := by
  have h := (s208d_orbit_two D hE h207 h1930 hL hC ht hne).1
  refine le_antisymm (iSup_le fun s => ?_) (sup_le (uc22p20b_le_orb D.T C) (uc22p20b_cj_le_orb ht))
  rcases h s s.2 with h' | h'
  · rw [h']
    exact le_sup_left
  · rw [h']
    exact le_sup_right

end CFSG.LocalAnalysis.UniquenessCase.UC22
