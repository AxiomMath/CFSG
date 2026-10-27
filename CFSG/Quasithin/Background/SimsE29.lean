module

public import CFSG.Quasithin.Background.SimsE2Defs
public import CFSG.Quasithin.Background.E1ElevenIso
public import CFSG.Quasithin.Vol2.E2NineStarSQTK
public import CFSG.Quasithin.Background.B5NonSQTK
public import CFSG.Quasithin.Vol2.E2NinePullback

open scoped Pointwise commutatorElement

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E29

theorem conjSubgroup_eq_conjSub_inv {G : Type} [Group G] (V : Subgroup G) (g : G) :
    conjSubgroup V g = B6.conjSub g⁻¹ V := by
  ext x
  rw [B6.mem_conjSub, mem_conjSubgroup_iff, inv_inv]

theorem nParam_star_of_kerIn_eq_bot {Γ : Type} [Group Γ] [Finite Γ] {M H : Subgroup Γ}
    (hJ : kerIn M H = ⊥) : E1.nParam (⊤ : Subgroup (E2.StarQuot M H)) = E1.nParam H := by
  have h0 : (kerIn M H).subgroupOf H = ⊥ := by rw [hJ]; simp
  rw [E1.Eleven.nParam_top_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq h0).trans (QuotientGroup.quotientBot (G := ↥H))),
    ← E1.nParam_subgroupOf H]

theorem isSp4Full_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {k : ℕ}
    (h : IsSp4Full k B) : IsSp4Full k A :=
  E2.isSp4C_of_mulEquiv e h

theorem map_rootGroupOfParabolic_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (P : Subgroup A) :
    (rootGroupOfParabolic P).map e.toMonoidHom = rootGroupOfParabolic (P.map e.toMonoidHom) :=
  E2.map_rootGroupOf_equiv e P

theorem exists_isInIHTV_of_star {Γ : Type} [Group Γ] [Finite Γ] {H T M V : Subgroup Γ}
    (h : E2.Hyp28 H T M V) {I₀ : Subgroup (E2.StarQuot M H)}
    (hI₀ : IsInIHTV (⊤ : Subgroup (E2.StarQuot M H)) (E2.star M H T) (E2.star M H M)
      (E2.star M H V) I₀) :
    ∃ I : Subgroup Γ, IsInIHTV H T M V I := by
  have := E2P.finite_starQuot M H
  obtain ⟨-, ⟨g₀, hg₀, hgen₀⟩, hsyl₀, hcl₀, k, ⟨m, hm⟩, hc⟩ := hI₀
  obtain ⟨g, hgH, hgI, hIeq, hsyl⟩ := E2.exists_pullback h
    ⟨g₀⁻¹, I₀.inv_mem hg₀, by rw [hgen₀, conjSubgroup_eq_conjSub_inv]⟩ hsyl₀
  set I := V ⊔ B6.conjSub g V with hIdef
  have hVH := h.le_H
  have hIH : I ≤ H := sup_le hVH (by
    intro w hw
    rw [B6.mem_conjSub] at hw
    have := H.mul_mem (H.mul_mem hgH (hVH hw)) (H.inv_mem hgH)
    simpa [mul_assoc] using this)
  have hVI : V ≤ I := le_sup_left
  rw [← hIeq] at hcl₀ hc
  refine ⟨I, hIH, ⟨g⁻¹, I.inv_mem hgI, by rw [conjSubgroup_eq_conjSub_inv, inv_inv]⟩, hsyl,
    E2.isSylowTwoOf_pCoreOf_kerIn_of_star h hgH hcl₀, k,
    ⟨m, (nParam_star_of_kerIn_eq_bot (E2P.kerIn_star M H)).symm.trans hm⟩, ?_⟩
  set e := E2.starEquiv M hIH with he
  have hMI : (E2.star (M ⊓ I) I (M ⊓ I)).map e.toMonoidHom =
      E2.star (E2.star M H M ⊓ E2.star M H I) (E2.star M H I)
        (E2.star M H M ⊓ E2.star M H I) := by
    rw [E2.map_starEquiv hIH inf_le_right, E2P.star_inf_M]
  have hVe : (E2.star (M ⊓ I) I V).map e.toMonoidHom =
      E2.star (E2.star M H M ⊓ E2.star M H I) (E2.star M H I) (E2.star M H V) :=
    E2.map_starEquiv hIH hVI
  rcases hc with ⟨hk, hY, hB⟩ | ⟨hk, p, a, hp, hp2, ha, ⟨d⟩⟩ | ⟨hO, hk, hY, hB, hV, hP⟩
  · refine Or.inl ⟨hk, ?_, E2.isBorelIn_of_map_equiv e (hMI ▸ hB)⟩
    rcases hY with hY | hY
    · exact Or.inl (E2.isPSL_of_mulEquiv e hY)
    · exact Or.inr (E2.isSz_of_mulEquiv' e hY)
  · exact Or.inr (Or.inl ⟨hk, p, a, hp, hp2, ha, ⟨e.trans d⟩⟩)
  · refine Or.inr (Or.inr ⟨?_, hk, isSp4Full_of_mulEquiv e hY,
      E2.isBorelIn_of_map_equiv e (hMI ▸ hB), ?_, ?_⟩)
    · obtain ⟨n, hn⟩ := hO
      exact ⟨n, E2.isSp4Prime_oTwoUpper_of_starTop hn⟩
    ·
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have hTI : (E2.star (M ⊓ I) I (T ⊓ I)).map e.toMonoidHom ≤
          E2.star (E2.star M H M ⊓ E2.star M H I) (E2.star M H I)
            (E2.star M H T ⊓ E2.star M H I) := by
        rw [E2.map_starEquiv hIH inf_le_right]
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono _
          (le_inf (E2.star_mono inf_le_left) (E2.star_mono inf_le_right)))
      have h1 := Subgroup.mem_centralizer_iff.1 (hV (hVe ▸ ⟨x, hx, rfl⟩ : e x ∈ _))
        (e t) (hTI ⟨t, ht, rfl⟩)
      apply e.injective
      rw [map_mul, map_mul]
      exact h1
    ·
      intro P hPmax hMP hVP
      apply hP (P.map e.toMonoidHom) (E2.isMaxParabolic2_map_equiv e hPmax)
        (hMI ▸ Subgroup.map_mono hMP)
      rw [← hVe, ← map_rootGroupOfParabolic_equiv]
      exact Subgroup.map_mono hVP

end E29

section e29


theorem e29
    (h27 : E27Stmt) {Γ : Type} [Group Γ] [Finite Γ] (H T M V : Subgroup Γ)
    (h : E2.Hyp28 H T M V) :
    H ⊓ Subgroup.normalizer (V : Set Γ) ≤ M ∧
    (¬ IsL33Exception (⊤ : Subgroup (E2.StarQuot M H)) (E2.star M H V) →
      ∃ I : Subgroup Γ, IsInIHTV H T M V I) ∧
    ∀ I : Subgroup Γ, IsInIHTV H T M V I →
      ((⁅kerIn M H, I⁆ ≤ pCoreOf 2 H ∧ pCoreOf 2 H ≤ Subgroup.normalizer (I : Set Γ)) ∧
        kerIn M H ≤ Subgroup.normalizer (oTwoUpper I : Set Γ)) ∧
      (CharTwo H → CharTwo I) := by
  refine ⟨h.inf_normalizer_le, fun hL => ?_, fun I hI => ?_⟩
  · have := E2P.finite_starQuot M H
    have hsq := ASInputs.as_E_2_9_starSQTK_of asA21SQTKSection Γ H T M V h
    have h' := h.star hsq
    obtain ⟨I₀, hI₀⟩ := h27 (E2.StarQuot M H) ⊤ (E2.star M H T) (E2.star M H M)
      (E2.star M H V) h'.minParabolic hsq (E2P.kerIn_star M H) h'.ne_bot h'.elem h'.le_T
      h'.normal_T h'.le_pCoreOf hL
    exact E29.exists_isInIHTV_of_star h hI₀
  · obtain ⟨hIH, ⟨g, hgI, rfl⟩, -⟩ := hI
    have hg : g⁻¹ ∈ H := H.inv_mem (hIH hgI)
    rw [E29.conjSubgroup_eq_conjSub_inv]
    exact ⟨⟨⟨E2.commutator_kerIn_le h hg, E2.pCoreOf_le_normalizer h hg⟩,
      E2.kerIn_le_normalizer_oTwoUpper h hg⟩, E2.charTwo_of_charTwo h hg⟩

end e29

end CFSG.Quasithin.SimsE2
