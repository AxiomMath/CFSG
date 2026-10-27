module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Image

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_z3_ker (h : S16kBase D V₀ V L hV)
    (hZ : IsCyclicOrd ↥(lBar V₀ V hV L) 3) (hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6)
    {A : Subgroup G} (hAM : A ≤ D.M) (hA : IsElemAbelian 3 A) (hA4 : Nat.card A = 3 ^ 4)
    (hN : ¬ Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      ((barSub V₀ V hV A : Subgroup (MulAut (Vtil V₀ V hV))) : Set (MulAut (Vtil V₀ V hV)))) :
    False := by
  classical
  obtain ⟨hrk3, e, φ, hcompat, -, hM, hAbar⟩ := s16k_z3_image_torus h hZ hrk hAM hA hA4
  have h3sig : 3 ∈ D.sig := s16k_z3_three_mem_sig h hZ hrk
  have hker : 3 ∣ Nat.card (F11.CTilde D.M V₀ V) :=
    s16g_dvd_card_cTilde D h.std h.setting h3sig hrk3
  have hMst : D.M ≤ stabTil V₀ V := s16g_le_stabTil h.setting
  have hAbar_le : barSub V₀ V hV A ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hAM
  obtain ⟨g, hgM, hgN⟩ : ∃ g : MulAut (Vtil V₀ V hV), g ∈ Mbar D.M V₀ V hV ∧
      g ∉ Subgroup.normalizer
        ((barSub V₀ V hV A : Subgroup (MulAut (Vtil V₀ V hV))) : Set _) := by
    by_contra hc
    push Not at hc
    exact hN fun x hx => hc x hx
  have hgNscal : φ g ∈ Subgroup.normalizer (s16kScal : Set S16kGL6) :=
    hM (Subgroup.mem_map.2 ⟨g, hgM, rfl⟩)
  have hsymm : (s16kDiag : Subgroup S16kGL6).map φ.symm.toMonoidHom = barSub V₀ V hV A := by
    rw [← hAbar, Subgroup.map_map,
      show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ from by ext a; simp,
      Subgroup.map_id]
  have hNormSymm : (Subgroup.normalizer (s16kDiag : Set S16kGL6)).map φ.symm.toMonoidHom =
      Subgroup.normalizer (barSub V₀ V hV A : Set (MulAut (Vtil V₀ V hV))) := by
    rw [Subgroup.map_equiv_normalizer_eq, hsymm]
  have hgDiag : φ g ∉ Subgroup.normalizer (s16kDiag : Set S16kGL6) := by
    intro hmem
    apply hgN
    have h2 : g ∈ (Subgroup.normalizer (s16kDiag : Set S16kGL6)).map φ.symm.toMonoidHom :=
      Subgroup.mem_map.2 ⟨φ g, hmem, by simp⟩
    rwa [hNormSymm] at h2
  refine s16g_false_of_fix_ker (hV := hV) D h.std h.setting Nat.prime_three h3sig hker hMst ?_
  intro x hx1
  have hx0 : Multiplicative.toAdd (e x) ≠ 0 := by
    intro h0
    have h1 : e x = 1 := toAdd_eq_zero.mp h0
    exact hx1 (e.injective (by rw [h1, map_one]))
  obtain ⟨k, hk, d, hd, hd1, hdv⟩ :=
    s16k_z3_cover hgNscal hgDiag (Multiplicative.toAdd (e x)) hx0
  have hsub : ((barSub V₀ V hV A : Set (MulAut (Vtil V₀ V hV))) ∪ {g}) ⊆
      (Mbar D.M V₀ V hV : Set _) := by
    intro y hy
    rcases hy with hy | hy
    · exact hAbar_le hy
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hgM
  have hK_le : Subgroup.closure
      ((barSub V₀ V hV A : Set (MulAut (Vtil V₀ V hV))) ∪ {g}) ≤ Mbar D.M V₀ V hV :=
    (Subgroup.closure_le _).2 hsub
  have himage_sub : (s16kDiag : Set S16kGL6) ∪ {φ g} ⊆
      φ.toMonoidHom '' ((barSub V₀ V hV A : Set (MulAut (Vtil V₀ V hV))) ∪ {g}) := by
    intro y hy
    rcases hy with hy | hy
    · have hy' : y ∈ (barSub V₀ V hV A).map φ.toMonoidHom := by rw [hAbar]; exact hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy'
      exact ⟨z, Or.inl hz, hzy⟩
    · rw [Set.mem_singleton_iff] at hy
      exact ⟨g, Or.inr rfl, hy.symm⟩
  have hk' : k ∈ (Subgroup.closure
      ((barSub V₀ V hV A : Set (MulAut (Vtil V₀ V hV))) ∪ {g})).map φ.toMonoidHom := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono himage_sub hk
  obtain ⟨kt, hkt, hktφ⟩ := Subgroup.mem_map.1 hk'
  have hd' : d ∈ (barSub V₀ V hV A).map φ.toMonoidHom := by rw [hAbar]; exact hd
  obtain ⟨ā, hā, hāφ⟩ := Subgroup.mem_map.1 hd'
  let a : MulAut (Vtil V₀ V hV) := kt⁻¹ * ā * kt
  have hφa : φ a = k⁻¹ * d * k := by
    change φ.toMonoidHom (kt⁻¹ * ā * kt) = k⁻¹ * d * k
    rw [map_mul, map_mul, map_inv, hktφ, hāφ]
  have hkd1 : k⁻¹ * d * k ≠ 1 := by
    intro h1
    apply hd1
    have hc : k * (k⁻¹ * d * k) * k⁻¹ = d := by group
    rw [← hc, h1]
    group
  have hane : a ≠ 1 := fun ha1 => hkd1 (by rw [← hφa, ha1]; simp)
  have hax : a x = x := by
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [hcompat a x, hφa, hdv]
  have hAstab : A ≤ stabTil V₀ V := hAM.trans hMst
  have hāne : ā ≠ 1 := by
    intro h1
    apply hd1
    rw [← hāφ, h1]
    simp
  have hktrange : kt ∈ (barHom V₀ V hV hMst).range := by
    rw [range_barHom]
    exact hK_le hkt
  obtain ⟨mk, hmk⟩ := MonoidHom.mem_range.1 hktrange
  have hārange : ā ∈ (barHom V₀ V hV hAstab).range := by
    rw [range_barHom]
    exact hā
  obtain ⟨a₀A, ha₀A⟩ := MonoidHom.mem_range.1 hārange
  have ha₀Ane : a₀A ≠ 1 := by
    intro h1
    apply hāne
    rw [← ha₀A, h1]
    simp
  have hpow : a₀A ^ 3 = 1 := Subtype.ext (hA.2 (a₀A : G) a₀A.2)
  have hdvd : orderOf a₀A ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hpow
  have hordA : orderOf a₀A = 3 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (orderOf a₀A) hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.1 h1) ha₀Ane
    · exact h3
  let a₀ : ↥D.M := Subgroup.inclusion hAM a₀A
  have hbar0 : barHom V₀ V hV hMst a₀ = ā := by
    have hsub' : Subgroup.inclusion hMst a₀ = Subgroup.inclusion hAstab a₀A := Subtype.ext rfl
    change actTil V₀ V hV (Subgroup.inclusion hMst a₀) = ā
    rw [hsub']
    simpa only [barHom, MonoidHom.comp_apply] using ha₀A
  have hord0 : orderOf a₀ = 3 := by
    have h1 : orderOf a₀ = orderOf (a₀A : G) := Subgroup.orderOf_mk (a₀A : G) (hAM a₀A.2)
    rw [h1, Subgroup.orderOf_coe a₀A, hordA]
  let m : ↥D.M := mk⁻¹ * a₀ * mk
  have hmbar : barHom V₀ V hV hMst m = a := by
    change barHom V₀ V hV hMst (mk⁻¹ * a₀ * mk) = kt⁻¹ * ā * kt
    rw [map_mul, map_mul, map_inv, hmk, hbar0]
  have hmo : orderOf m = 3 := by
    have hh := MulEquiv.orderOf_eq (MulAut.conj mk⁻¹) a₀
    rw [MulAut.conj_apply, inv_inv] at hh
    change orderOf (mk⁻¹ * a₀ * mk) = 3
    rw [hh, hord0]
  have hmbar_ne : barHom V₀ V hV hMst m ≠ 1 := by
    rw [hmbar]
    exact hane
  have hmbar_fix : barHom V₀ V hV hMst m x = x := by
    rw [hmbar]
    exact hax
  exact ⟨m, hmo, hmbar_ne, hmbar_fix⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
