module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKAltFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16k_exists_permVec_coreMod {n : ℕ} (hn : 3 ≤ n) :
    ∃ m : G6.PermMod n, m ∈ G6.coreMod n ∧ m ≠ 1 ∧ m ≠ G6.allOnes n := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h10 : i1 ≠ i0 := by
    intro h
    have : (1 : ℕ) = 0 := by simpa [i0, i1] using congrArg Fin.val h
    omega
  have h20 : i2 ≠ i0 := by
    intro h
    have : (2 : ℕ) = 0 := by simpa [i0, i2] using congrArg Fin.val h
    omega
  have h21 : i2 ≠ i1 := by
    intro h
    have : (2 : ℕ) = 1 := by simpa [i1, i2] using congrArg Fin.val h
    omega
  have h01 : i0 ≠ i1 := fun h => h10 h.symm
  let f : Fin n → ZMod 2 := fun j => if j = i0 ∨ j = i1 then 1 else 0
  refine ⟨Multiplicative.ofAdd f, ?_, ?_, ?_⟩
  · rw [G6.mem_coreMod]
    change (∑ j : Fin n, f j) = 0
    have hf : ∀ j : Fin n, f j = (if j = i0 then (1 : ZMod 2) else 0) +
        (if j = i1 then (1 : ZMod 2) else 0) := by
      intro j
      by_cases hj0 : j = i0
      · subst hj0; simp [f, h01]
      · by_cases hj1 : j = i1
        · subst hj1; simp [f, h10]
        · simp [f, hj0, hj1]
    have hsum0 : (∑ j : Fin n, (if j = i0 then (1 : ZMod 2) else 0)) = 1 := by
      rw [Finset.sum_eq_single i0]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ i0) h
    have hsum1 : (∑ j : Fin n, (if j = i1 then (1 : ZMod 2) else 0)) = 1 := by
      rw [Finset.sum_eq_single i1]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ i1) h
    rw [Finset.sum_congr rfl (fun j _ => hf j), Finset.sum_add_distrib, hsum0, hsum1]
    decide
  · intro h1
    have h0 : f i0 = 0 := congrFun (ofAdd_eq_one.1 h1) i0
    have h1' : f i0 = 1 := by simp [f, h01]
    rw [h1'] at h0
    exact one_ne_zero h0
  · intro h1
    have h0 : f i2 = 1 := by
      have h2 : f = (fun _ : Fin n => (1 : ZMod 2)) :=
        Multiplicative.ofAdd.injective (by simpa [G6.allOnes] using h1)
      exact congrFun h2 i2
    have h2' : f i2 = 0 := by simp [f, h20, h21]
    rw [h2'] at h0
    exact zero_ne_one h0

theorem s16k_false_of_alt_fix (h : S16gRowCtx D V₀ V L hV) {n : ℕ} (hn : 5 ≤ n)
    (hN : AlternatingNatural (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig) (hn3 : 3 * p ≤ n) : False := by
  obtain ⟨π, hπ⟩ := hN
  unfold FFModel.RealizesVia FFModel.altDn at hπ
  obtain ⟨hπs, _hZU, _hkerle, _hHU, _hHZ, _hsec, _hker, β, _hβs, hβk, hβe⟩ := hπ
  have hUt : commSub ⊤ (lBar V₀ V hV L) = ⊤ := h.comm_top
  haveI hAlt : IsSimpleGroup (FFModel.altDn n).Gam := by
    change IsSimpleGroup ↥(alternatingGroup (Fin n))
    exact alternatingGroup.isSimpleGroup (by simpa using hn)
  have hπi : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp (by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hker | hker
    · exact hker
    · exfalso
      have hπ1 : π = 1 := MonoidHom.ker_eq_top_iff.mp hker
      haveI : IsSimpleGroup (↥(lBar V₀ V hV L) ⧸ Subgroup.center ↥(lBar V₀ V hV L)) :=
        h.quasi.2
      haveI : Nontrivial ↥(lBar V₀ V hV L) :=
        (QuotientGroup.mk'_surjective (Subgroup.center ↥(lBar V₀ V hV L))).nontrivial
      have htop : (⊤ : Subgroup ↥(lBar V₀ V hV L)) = ⊥ := by
        rw [← MonoidHom.range_eq_top.mpr hπs, hπ1]
        exact MonoidHom.range_one
      exact (bot_lt_top : (⊥ : Subgroup ↥(lBar V₀ V hV L)) < ⊤).ne' htop)
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV h.setting.hyp151.le
  refine s16g_false_of_fix D h.std (hV := hV) h.setting hp hpσ ?_
  intro x hx1
  have hxU : x ∈ commSub ⊤ (lBar V₀ V hV L) := by rw [hUt]; trivial
  have build : ∀ a : G6.PermMod n, a ∈ G6.coreMod n → a ≠ 1 → a ≠ G6.allOnes n →
      (x ∈ fixV (lBar V₀ V hV L) ∨ ∃ m : ↥(G6.coreMod n), (m : G6.PermMod n) = a ∧
        β ⟨x, hxU⟩ = QuotientGroup.mk m) →
      ∃ B : Subgroup (MulAut (Vtil V₀ V hV)), B ≤ Mbar D.M V₀ V hV ∧ IsPGroup p B ∧
        ¬ IsCyclic ↥B ∧ ∀ b ∈ B, b x = x := by
    intro a ha ha1 ha2 hcase
    obtain ⟨B₀, hB₀p, hB₀c, hB₀fix⟩ := s16k_alt_fix_noncyclic n hp hp2 hn3 a ha ha1 ha2
    let F : ↥(alternatingGroup (Fin n)) →* MulAut (Vtil V₀ V hV) :=
      (lBar V₀ V hV L).subtype.comp π
    let B : Subgroup (MulAut (Vtil V₀ V hV)) := B₀.map F
    have hBH : B ≤ lBar V₀ V hV L := by
      intro y hy
      obtain ⟨b₀, _hb₀, rfl⟩ := Subgroup.mem_map.mp hy
      exact (π b₀).2
    refine ⟨B, hBH.trans hle, ?_, ?_, ?_⟩
    · exact hB₀p.map F
    · intro hcyc
      haveI : IsCyclic ↥(B₀.map F) := hcyc
      exact hB₀c (isCyclic_of_injective
        (Subgroup.equivMapOfInjective B₀ F
          ((lBar V₀ V hV L).subtype_injective.comp hπi)).toMonoidHom
        (Subgroup.equivMapOfInjective B₀ F
          ((lBar V₀ V hV L).subtype_injective.comp hπi)).injective)
    · intro b hb
      obtain ⟨b₀, hb₀, hb_eq⟩ := Subgroup.mem_map.mp hb
      rw [← hb_eq]
      rcases hcase with hxfix | ⟨m, hm_eq, hβx⟩
      · exact (mem_fixV.1 hxfix) ((lBar V₀ V hV L).subtype (π b₀)) (π b₀).2
      · haveI : Fact p.Prime := ⟨hp⟩
        have hperm : G6.permAct n
            (b₀ : Equiv.Perm (Fin n)) (m : G6.PermMod n) ∈
            G6.coreMod n := G6.permAct_mem_coreMod _ m.2
        have hfxU : ((π b₀ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) x ∈
            commSub ⊤ (lBar V₀ V hV L) := by rw [hUt]; trivial
        have hkey := hβe b₀ ⟨x, hxU⟩ m hfxU hperm hβx
        have hfixm : G6.permAct n
            (b₀ : Equiv.Perm (Fin n)) (m : G6.PermMod n) =
            (m : G6.PermMod n) := by
          rw [hm_eq]
          exact hB₀fix b₀ hb₀
        have hm_eq' : (⟨G6.permAct n
            (b₀ : Equiv.Perm (Fin n)) (m : G6.PermMod n),
            hperm⟩ : ↥(G6.coreMod n)) = m := Subtype.ext hfixm
        have hβb : β ⟨((π b₀ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) x, hfxU⟩ =
            β ⟨x, hxU⟩ := by
          have hkey' : β ⟨((π b₀ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) x, hfxU⟩ =
              QuotientGroup.mk ⟨G6.permAct n
                (b₀ : Equiv.Perm (Fin n)) (m : G6.PermMod n),
                hperm⟩ := hkey
          rw [hkey', hm_eq']
          exact hβx.symm
        have hmemU : ((π b₀ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) x * x⁻¹ ∈
            commSub ⊤ (lBar V₀ V hV L) := by rw [hUt]; trivial
        have h5 : (⟨((π b₀ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) x, hfxU⟩ :
              ↥(commSub ⊤ (lBar V₀ V hV L))) * (⟨x, hxU⟩ :
              ↥(commSub ⊤ (lBar V₀ V hV L)))⁻¹ =
            ⟨((π b₀ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) x * x⁻¹, hmemU⟩ :=
          Subtype.ext rfl
        have h4 : β (⟨((π b₀ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) x * x⁻¹, hmemU⟩ :
            ↥(commSub ⊤ (lBar V₀ V hV L))) = 1 := by
          rw [← h5, map_mul, map_inv, hβb, mul_inv_cancel]
        have hZmem : ((π b₀ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) x * x⁻¹ ∈
            fixV (lBar V₀ V hV L) := by
          have hZ : ((π b₀ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) x * x⁻¹ ∈
              commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) :=
            (hβk ⟨_, hmemU⟩).mp h4
          exact hZ.2
        obtain ⟨k, hk⟩ := hB₀p.exists_orderOf_eq_pow (⟨b₀, hb₀⟩ : ↥B₀)
        have hord : orderOf b₀ = p ^ k := by rw [← Subgroup.orderOf_mk b₀ hb₀, hk]
        have hb1 : b₀ ^ p ^ k = 1 := hord ▸ pow_orderOf_eq_one b₀
        have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
        have h1 : (π b₀ : ↥(lBar V₀ V hV L)) ^ p ^ k = 1 :=
          (map_pow π b₀ (p ^ k)).symm.trans (by rw [hb1]; exact map_one π)
        have hpow : ((π b₀ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) ^ p ^ k = 1 := by
          simpa using congrArg
            (fun g : ↥(lBar V₀ V hV L) => (g : MulAut (Vtil V₀ V hV))) h1
        have hZfix : ∀ z ∈ fixV (lBar V₀ V hV L),
            ((π b₀ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) z = z :=
          fun z hz => (mem_fixV.1 hz) (π b₀) (π b₀).2
        exact s16g_apply_eq_of_odd (s15_Infra_vtil_sq_eq_one V₀ V hV) hodd hpow hZfix hZmem
  have hmain : ∃ a : G6.PermMod n, a ∈ G6.coreMod n ∧ a ≠ 1 ∧ a ≠ G6.allOnes n ∧
      (x ∈ fixV (lBar V₀ V hV L) ∨ ∃ m : ↥(G6.coreMod n), (m : G6.PermMod n) = a ∧
        β ⟨x, hxU⟩ = QuotientGroup.mk m) := by
    by_cases hxfix : x ∈ fixV (lBar V₀ V hV L)
    · obtain ⟨a, ha, ha1, ha2⟩ := s16k_exists_permVec_coreMod (by omega : 3 ≤ n)
      exact ⟨a, ha, ha1, ha2, Or.inl hxfix⟩
    · have hβx1 : β ⟨x, hxU⟩ ≠ 1 := by
        intro h1
        have hxZ : x ∈ commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) := by
          simpa using (hβk ⟨x, hxU⟩).mp h1
        exact hxfix hxZ.2
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨x, hxU⟩)
      refine ⟨(m : G6.PermMod n), m.2, ?_, ?_, Or.inr ⟨m, rfl, hm.symm⟩⟩
      · intro h1
        exact hβx1 (by rw [← hm, show m = 1 from Subtype.ext h1]; simp)
      · intro h2
        exact hβx1 (by
          have hmem : m ∈ (Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n).subgroupOf
              (G6.coreMod n) := by
            refine Subgroup.mem_subgroupOf.mpr ?_
            refine ⟨?_, m.2⟩
            rw [h2]
            exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
          rw [← hm]
          exact (QuotientGroup.eq_one_iff m).mpr hmem)
  obtain ⟨a, ha, ha1, ha2, hcase⟩ := hmain
  exact build a ha ha1 ha2 hcase

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
