module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.WeakClosure81.FourteenNine
public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barSub_ne_bot_of_card_le_two (D : Data G) (h127 : R127 D) {V₀ V L : Subgroup G}
    (hV : Hyp125 D V₀ V) (hL : L ∈ calC D.M) (h7 : UniqueMax D.M L)
    (hV₀ : Nat.card V₀ ≤ 2) : barSub V₀ V hV.isElemAbelian L ≠ ⊥ := by
  classical
  intro hbot
  have hP := hV.pairFacts
  have hLM : L ≤ D.M := hL.1.le
  have hLct : L ≤ F11.CTilde D.M V₀ V :=
    (WeakClosure81.barSub_eq_bot_iff (M := D.M) (V₀ := V₀) (V := V) (B := L)
      hP.elemAbelian hP.le_normalizer hP.le_normalizer₀ hLM).1 hbot
  have hsq : ∀ x ∈ L, ∀ v ∈ V, x * (x * v * x⁻¹) * x⁻¹ = v := by
    intro x hx v hv
    obtain ⟨hxM, hxs, hx1⟩ := (mem_cTilde_iff hP.elemAbelian hP.le_normalizer).1 (hLct hx)
    set c : G := x * v * x⁻¹ * v⁻¹ with hcdef
    have hc : c ∈ V₀ := (actTil_eq_one_iff V₀ V hP.elemAbelian ⟨x, hxs⟩).1 hx1 v hv
    have hfix : ∀ d ∈ V₀, x * d * x⁻¹ = d := by
      intro d hd0
      by_cases hd1 : d = 1
      · rw [hd1, mul_one, mul_inv_cancel]
      · have hdn : x * d * x⁻¹ ∈ V₀ :=
          (Subgroup.mem_normalizer_iff.mp (hP.le_normalizer₀ hxM) d).1 hd0
        have hdn1 : x * d * x⁻¹ ≠ 1 := by
          intro h
          apply hd1
          have h2 : d = x⁻¹ * (x * d * x⁻¹) * x := by group
          rw [h, mul_one] at h2
          simpa using h2
        have hV0gt : 1 < Nat.card V₀ := by
          rw [Subgroup.one_lt_card_iff_ne_bot]
          intro hb
          exact hd1 (Subgroup.mem_bot.mp (hb ▸ hd0))
        have hV0eq : Nat.card V₀ = 2 := by omega
        obtain ⟨z, -, hzu⟩ := (Nat.card_eq_two_iff' (1 : ↥V₀)).mp hV0eq
        have hdeq : (⟨d, hd0⟩ : ↥V₀) = z :=
          hzu ⟨d, hd0⟩ (fun h => hd1 (Subtype.ext_iff.mp h))
        have hdneq : (⟨x * d * x⁻¹, hdn⟩ : ↥V₀) = z :=
          hzu ⟨x * d * x⁻¹, hdn⟩ (fun h => hdn1 (Subtype.ext_iff.mp h))
        exact (Subtype.ext_iff.mp (hdeq.trans hdneq.symm)).symm
    have hc2 : c * c = 1 := by
      rw [← pow_two]
      exact hP.elemAbelian₀.2 _ hc
    have hcv : x * v * x⁻¹ = c * v := by
      rw [hcdef]
      group
    calc x * (x * v * x⁻¹) * x⁻¹
        = (x * c * x⁻¹) * (x * v * x⁻¹) := by
            rw [hcdef]
            group
      _ = c * (x * v * x⁻¹) := by rw [hfix _ hc]
      _ = c * (c * v) := by rw [hcv]
      _ = v := by rw [← mul_assoc, hc2, one_mul]
  have hcommut : ∀ x ∈ L, ∀ y ∈ L, ∀ v ∈ V, ⁅x, y⁆ * v * ⁅x, y⁆⁻¹ = v := by
    intro x hx y hy v hv
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := hP.le_normalizer (hLM hx)
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := hP.le_normalizer (hLM hy)
    have hyv : y * v * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyN v).1 hv
    have hy' : y⁻¹ * v * y = y * v * y⁻¹ := by
      have h := hsq y hy v hv
      have h2 := congrArg (fun z => y⁻¹ * z * y) h
      simpa [mul_assoc] using h2.symm
    have hx' : x⁻¹ * (y * v * y⁻¹) * x = x * (y * v * y⁻¹) * x⁻¹ := by
      have h := hsq x hx (y * v * y⁻¹) hyv
      have h2 := congrArg (fun z => x⁻¹ * z * x) h
      simpa [mul_assoc] using h2.symm
    have hfin := hsq (x * y) (L.mul_mem hx hy) v hv
    rw [commutatorElement_def]
    calc x * y * x⁻¹ * y⁻¹ * v * (x * y * x⁻¹ * y⁻¹)⁻¹
        = x * (y * (x⁻¹ * (y⁻¹ * v * y) * x) * y⁻¹) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * (y * v * y⁻¹) * x) * y⁻¹) * x⁻¹ := by rw [hy']
      _ = x * (y * (x * (y * v * y⁻¹) * x⁻¹) * y⁻¹) * x⁻¹ := by rw [hx']
      _ = v := by
            simpa [mul_assoc, mul_inv_rev] using hfin
  have hCL : ⁅L, L⁆ ≤ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h := hcommut x hx y hy v hv
    have h' : ⁅x, y⁆ * v = v * ⁅x, y⁆ := by
      calc ⁅x, y⁆ * v = (⁅x, y⁆ * v * ⁅x, y⁆⁻¹) * ⁅x, y⁆ := by group
        _ = v * ⁅x, y⁆ := by rw [h]
    exact h'.symm
  have hcommV : L ≤ Subgroup.centralizer (V : Set G) := by
    rw [← hL.2.1]
    exact hCL
  have hcomm : ∀ x ∈ L, ∀ v ∈ V, x * v = v * x := by
    intro x hx v hv
    exact ((Subgroup.mem_centralizer_iff.mp (hcommV hx)) v hv).symm
  have hnti : ¬ CFSG.CGT.Timmesfeld75.IsTI V := (twelve_nine D h127 hV).1
  rw [CFSG.CGT.Timmesfeld75.IsTI] at hnti
  push_neg at hnti
  obtain ⟨g, hgne, hgne'⟩ := hnti
  have hgM : g ∉ D.M := by
    intro hg
    have hconj : CFSG.CGT.Timmesfeld75.conjSubgroup g V = V :=
      (CFSG.CGT.Timmesfeld75.mem_normalizer_iff_conjSubgroup_eq).1 (hP.le_normalizer hg)
    exact hgne' (by rw [hconj, inf_idem])
  obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hgne
  have hv1' : (v : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvV : (v : G) ∈ V := (Subgroup.mem_inf.mp v.2).1
  have hvg : (v : G) ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g V := (Subgroup.mem_inf.mp v.2).2
  have hv2eq : (v : G) ^ 2 = 1 := hP.elemAbelian.2 (v : G) hvV
  have hv2 : IsPGroup 2 (Subgroup.zpowers (v : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hv2eq hv1']
    norm_num
  have hxconj : ∀ x ∈ L, x * (v : G) * x⁻¹ = (v : G) := by
    intro x hx
    rw [hcomm x hx (v : G) hvV]
    group
  have hLcent : L ≤ Subgroup.centralizer ((Subgroup.zpowers (v : G)) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : x * (v : G) ^ n * x⁻¹ = (v : G) ^ n := by
      rw [← conj_zpow, hxconj x hx]
    have h2 : x * (v : G) ^ n = (v : G) ^ n * x := by
      have := congrArg (· * x) h1
      simpa [mul_assoc] using this
    exact h2.symm
  have hLnorm : L ≤ Subgroup.normalizer ((Subgroup.zpowers (v : G)) : Set G) :=
    hLcent.trans (Subgroup.centralizer_le_normalizer _)
  have hNM : Subgroup.normalizer ((Subgroup.zpowers (v : G)) : Set G) ≤ D.M :=
    WeakClosure81.normalizer_le_of_inCalU h7 hLnorm (Subgroup.zpowers_ne_bot.mpr hv1') hv2
  have hCnorm : Subgroup.centralizer ({(v : G)} : Set G) ≤ D.M := by
    refine (le_trans ?_ hNM)
    intro x hx
    have hxv : x * (v : G) = (v : G) * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hxv' : x * (v : G) * x⁻¹ = (v : G) := by rw [hxv]; group
    have hxC : x ∈ Subgroup.centralizer ((Subgroup.zpowers (v : G)) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h1 : x * (v : G) ^ n * x⁻¹ = (v : G) ^ n := by
        rw [← conj_zpow, hxv']
      have h2 : x * (v : G) ^ n = (v : G) ^ n * x := by
        have := congrArg (· * x) h1
        simpa [mul_assoc] using this
      exact h2.symm
    exact Subgroup.centralizer_le_normalizer _ hxC
  obtain ⟨v', hv'V, hv'eq⟩ := Subgroup.mem_map.mp hvg
  have hLgv : L.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
    intro y hy
    obtain ⟨x, hxL, rfl⟩ := Subgroup.mem_map.mp hy
    have hxv' : x * v' = v' * x := hcomm x hxL v' hv'V
    rw [Subgroup.mem_centralizer_singleton_iff]
    show g * x * g⁻¹ * (v : G) = (v : G) * (g * x * g⁻¹)
    rw [← hv'eq]
    calc g * x * g⁻¹ * (g * v' * g⁻¹) = g * (x * v') * g⁻¹ := by group
      _ = g * (v' * x) * g⁻¹ := by rw [hxv']
      _ = (g * v' * g⁻¹) * (g * x * g⁻¹) := by group
  have hLgM : L.map (MulAut.conj g).toMonoidHom ≤ D.M := hLgv.trans hCnorm
  have hLconj : L ≤ CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ D.M := by
    intro x hx
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    have hxM : (MulAut.conj g) x ∈ D.M :=
      hLgM (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    simpa [MulAut.conj_apply, mul_assoc] using hxM
  have hmax : CFSG.Open.rankThreeIsMaxTwoLocal (CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ D.M) :=
    UC6.isMaxTwoLocal_conj D.maxLocal g
  have hmem : CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ D.M ∈ calMOf L := ⟨hmax, hLconj⟩
  rw [show calMOf L = {D.M} from h7] at hmem
  have hEq : CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ D.M = D.M := Set.mem_singleton_iff.mp hmem
  have hginv : g⁻¹ ∈ Subgroup.normalizer (D.M : Set G) :=
    (CFSG.CGT.Timmesfeld75.mem_normalizer_iff_conjSubgroup_eq).2 hEq
  rw [UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal] at hginv
  exact hgM (by simpa using D.M.inv_mem hginv)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
