module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c1610_mbar_le_normalizer_lbar (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (h3 : Case168_3 D V₀ V hV L) :
    Mbar D.M V₀ V hV ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
  have h151 : Hyp151 D V₀ V L := hc.setting.hyp151
  have hWsq : ∀ x : Vtil V₀ V hV, x * x = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := mkTil_surjective V₀ V hV x
    rw [← map_mul, ← sq, IntMod.sq_eq_one y, map_one]
  have hWcard : Nat.card (Vtil V₀ V hV) = 2 ^ 6 := by
    have hp : IsPGroup 2 (Vtil V₀ V hV) := by
      intro x
      refine ⟨1, ?_⟩
      simpa [pow_two] using hWsq x
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
    have h6 : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6 := h3.2.1
    unfold rk at h6
    rw [Subgroup.card_top, hn, padicValNat.prime_pow] at h6
    rw [hn, h6]
  intro φ hφ
  obtain ⟨m, hmM, rfl⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  by_contra hne
  have hgne : (m : G) ∉ nBar D.M V₀ V hV L := by
    intro hmem
    have h1 := (s15_Infra_mem_nBar_iff h151.hyp125 hV hmM).1 hmem
    have h2 := s15_Infra_barSub_conjSubgroup V₀ V hV m.2 L
    rw [h1] at h2
    apply hne
    have hinv : (actTil V₀ V hV m)⁻¹ ∈
        normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h2.symm
    have := (normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).inv_mem hinv
    simpa using this
  have hc1 : ⁅lBar V₀ V hV L, barSub V₀ V hV (conjSubgroup L (m : G))⁆ = ⊥ := by
    have hproof : h151.isElemAbelian = hV := Subsingleton.elim _ _
    have h := (s15_Kbar_commute_conj h151 (m := (1 : G)) (m' := (m : G))
      D.M.one_mem hmM (by simpa using hgne)).1
    rw [hproof] at h
    simpa [lBar, conjSubgroup_one] using h
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let Lb₁ : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV (conjSubgroup L (m : G))
  haveI hEx : CFSG.IsExtraspecial 3 ↥Lb := h3.1.1
  have hLbcard : Nat.card ↥Lb = 27 := by
    dsimp only [Lb]
    rw [h3.1.2.1]
    norm_num
  have hLb₁card : Nat.card ↥Lb₁ = 27 := by
    dsimp only [Lb₁]
    have h2 := s15_Infra_barSub_conjSubgroup V₀ V hV m.2 L
    rw [h2, Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact hLbcard
  have hcomm : ∀ a : ↥Lb, ∀ b : ↥Lb₁,
      (a : MulAut (Vtil V₀ V hV)) * (b : MulAut (Vtil V₀ V hV)) =
        (b : MulAut (Vtil V₀ V hV)) * (a : MulAut (Vtil V₀ V hV)) := by
    intro a b
    have hle : Lb ≤ Subgroup.centralizer (Lb₁ : Set (MulAut (Vtil V₀ V hV))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc1
    have hb := (Subgroup.mem_centralizer_iff.1 (hle a.2)) (b : MulAut (Vtil V₀ V hV)) b.2
    exact hb.symm
  let f : ↥Lb × ↥Lb₁ →* MulAut (Vtil V₀ V hV) :=
    { toFun := fun p => (p.1 : MulAut (Vtil V₀ V hV)) * (p.2 : MulAut (Vtil V₀ V hV))
      map_one' := by simp
      map_mul' := fun p q => by
        show ((p.1 * q.1 : ↥Lb) : MulAut (Vtil V₀ V hV)) *
              ((p.2 * q.2 : ↥Lb₁) : MulAut (Vtil V₀ V hV)) =
            ((p.1 : MulAut (Vtil V₀ V hV)) * (p.2 : MulAut (Vtil V₀ V hV))) *
              ((q.1 : MulAut (Vtil V₀ V hV)) * (q.2 : MulAut (Vtil V₀ V hV)))
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        calc ((p.1 : MulAut (Vtil V₀ V hV)) * (q.1 : MulAut (Vtil V₀ V hV))) *
                ((p.2 : MulAut (Vtil V₀ V hV)) * (q.2 : MulAut (Vtil V₀ V hV)))
            = (p.1 : MulAut (Vtil V₀ V hV)) *
                ((q.1 : MulAut (Vtil V₀ V hV)) * (p.2 : MulAut (Vtil V₀ V hV))) *
                  (q.2 : MulAut (Vtil V₀ V hV)) := by group
          _ = (p.1 : MulAut (Vtil V₀ V hV)) *
                ((p.2 : MulAut (Vtil V₀ V hV)) * (q.1 : MulAut (Vtil V₀ V hV))) *
                  (q.2 : MulAut (Vtil V₀ V hV)) := by rw [hcomm q.1 p.2]
          _ = ((p.1 : MulAut (Vtil V₀ V hV)) * (p.2 : MulAut (Vtil V₀ V hV))) *
                ((q.1 : MulAut (Vtil V₀ V hV)) * (q.2 : MulAut (Vtil V₀ V hV))) := by group }
  have hker : Nat.card ↥f.ker ≤ 3 := by
    let emb : ↥f.ker → ↥(Subgroup.center ↥Lb) := fun p =>
      ⟨p.1.1, by
        rw [Subgroup.mem_center_iff]
        intro a
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hb : (p.1.1 : MulAut (Vtil V₀ V hV)) *
            (p.1.2 : MulAut (Vtil V₀ V hV)) = 1 := by
          have h := MonoidHom.mem_ker.1 p.2
          change (p.1.1 : MulAut (Vtil V₀ V hV)) *
            (p.1.2 : MulAut (Vtil V₀ V hV)) = 1 at h
          exact h
        have h1 := eq_inv_of_mul_eq_one_left hb
        have hab : Commute (a : MulAut (Vtil V₀ V hV))
            (p.1.2 : MulAut (Vtil V₀ V hV)) := hcomm a p.1.2
        rw [h1]
        exact hab.inv_right⟩
    have hinj : Function.Injective emb := by
      intro p q hpq
      have h1 : (p.1.1 : ↥Lb) = q.1.1 := congrArg Subtype.val hpq
      have h2 : (p.1.1 : MulAut (Vtil V₀ V hV)) = (q.1.1 : MulAut (Vtil V₀ V hV)) :=
        congrArg Subtype.val h1
      have hp : (p.1.1 : MulAut (Vtil V₀ V hV)) *
          (p.1.2 : MulAut (Vtil V₀ V hV)) = 1 := by
        have h := MonoidHom.mem_ker.1 p.2
        change (p.1.1 : MulAut (Vtil V₀ V hV)) *
          (p.1.2 : MulAut (Vtil V₀ V hV)) = 1 at h
        exact h
      have hq : (q.1.1 : MulAut (Vtil V₀ V hV)) *
          (q.1.2 : MulAut (Vtil V₀ V hV)) = 1 := by
        have h := MonoidHom.mem_ker.1 q.2
        change (q.1.1 : MulAut (Vtil V₀ V hV)) *
          (q.1.2 : MulAut (Vtil V₀ V hV)) = 1 at h
        exact h
      have hpv : (p.1.2 : MulAut (Vtil V₀ V hV)) = (p.1.1 : MulAut (Vtil V₀ V hV))⁻¹ :=
        eq_inv_of_mul_eq_one_right hp
      have hqv : (q.1.2 : MulAut (Vtil V₀ V hV)) = (q.1.1 : MulAut (Vtil V₀ V hV))⁻¹ :=
        eq_inv_of_mul_eq_one_right hq
      apply Subtype.ext
      apply Prod.ext
      · exact h1
      · apply Subtype.ext
        rw [hpv, hqv, h2]
    have hle := Nat.card_le_card_of_injective emb hinj
    calc Nat.card ↥f.ker ≤ Nat.card ↥(Subgroup.center ↥Lb) := hle
      _ = 3 := CFSG.IsExtraspecial.center_order_p 3 ↥Lb
  have hcard : Nat.card ↥f.ker * Nat.card ↥f.range = 3 ^ 6 := by
    rw [card_ker_mul_card_range f, Nat.card_prod, hLbcard, hLb₁card]
    norm_num
  have h243 : 243 ∣ Nat.card ↥f.range := by
    set k := Nat.card ↥f.ker with hk
    set r := Nat.card ↥f.range with hr
    have hkr : k * r = 3 ^ 6 := hcard
    have hk1 : 1 ≤ k := by
      rw [hk]
      haveI : Nonempty ↥f.ker := ⟨1⟩
      exact Nat.card_pos
    have hk3 : k ≤ 3 := by
      rw [hk]
      exact hker
    interval_cases k
    · have : r = 729 := by omega
      exact ⟨3, by omega⟩
    · exfalso; omega
    · have : r = 243 := by omega
      exact ⟨1, by omega⟩
  have hrange_dvd : Nat.card ↥f.range ∣ Nat.card (MulAut (Vtil V₀ V hV)) :=
    Subgroup.card_subgroup_dvd_card f.range
  have h243aut : 243 ∣ Nat.card (MulAut (Vtil V₀ V hV)) := h243.trans hrange_dvd
  have hAut : Nat.card (MulAut (Vtil V₀ V hV)) = 20158709760 := by
    rw [CFSG.GH74.GLS.Bg.TwoGroups.L218.card_mulAut_two hWsq 6 hWcard]
    norm_num [Fin.prod_univ_succ]
  rw [hAut] at h243aut
  norm_num at h243aut

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
