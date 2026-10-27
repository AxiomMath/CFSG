module

public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog

theorem G2_weyl_eq_one_or_neg_of_scalar_mod {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    {w : WeylGroup .G2} {a : ZMod p}
    (h : ∀ (v : Fin Tag.G2.rank → ℤ) (i : Fin Tag.G2.rank), a * ((w • v) i : ZMod p) = v i) :
    (w = 1 ∧ a = 1) ∨ ((∀ v : Fin Tag.G2.rank → ℤ, w • v = -v) ∧ a = -1) := by
  have ha : a ≠ 0 := by
    rintro rfl
    have h0 := h g2a g2ia
    rw [zero_mul, g2a_ia, Int.cast_one] at h0
    exact zero_ne_one h0
  have off : ∀ (v : Fin Tag.G2.rank → ℤ) (i : Fin Tag.G2.rank) (e : ℤ), v i = 0 →
      (w • v) i = e → e ≠ 0 → e.natAbs ≤ 3 → False := by
    intro v i e hv hwv he0 he3
    have h0 := h v i
    rw [hv, hwv, Int.cast_zero, mul_eq_zero] at h0
    exact h0.elim ha fun he => not_dvd_of_natAbs_lt he0 (by omega)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd e p).1 he)
  rcases g2_weyl_cases w with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨weyl_G2_ext (by rw [h1, one_smul]) (by rw [h2, one_smul]), ?_⟩
    have h0 := h g2a g2ia
    rwa [h1, g2a_ia, Int.cast_one, mul_one] at h0
  · exact (off g2r g2ia 1 g2r_ia (by rw [h2]; rfl) (by decide) (by decide)).elim
  · exact (off g2a g2ir 3 g2a_ir (by rw [h1]; rfl) (by decide) (by decide)).elim
  · exact (off g2a g2ir 3 g2a_ir (by rw [h1]; rfl) (by decide) (by decide)).elim
  · exact (off g2a g2ir (-3) g2a_ir (by rw [h1]; rfl) (by decide) (by decide)).elim
  · exact (off g2a g2ir (-3) g2a_ir (by rw [h1]; rfl) (by decide) (by decide)).elim
  · exact (off g2a g2ir 3 g2a_ir (by rw [h1]; rfl) (by decide) (by decide)).elim
  · exact (off g2a g2ir (-3) g2a_ir (by rw [h1]; rfl) (by decide) (by decide)).elim
  · exact (off g2a g2ir 3 g2a_ir (by rw [h1]; rfl) (by decide) (by decide)).elim
  · exact (off g2a g2ir (-3) g2a_ir (by rw [h1]; rfl) (by decide) (by decide)).elim
  · exact (off g2r g2ia (-1) g2r_ia (by rw [h2]; rfl) (by decide) (by decide)).elim
  · refine Or.inr ⟨fun v => ?_, ?_⟩
    · conv_lhs => rw [g2_eq_smul_add v]
      conv_rhs => rw [g2_eq_smul_add v]
      rw [smul_add, smul_comm _ (v g2ia), smul_comm _ (v g2ir), h1, h2, neg_add, smul_neg,
        smul_neg]
    · have h0 := h g2a g2ia
      rw [h1, Pi.neg_apply, g2a_ia, Int.cast_neg, Int.cast_one, mul_neg_one] at h0
      exact neg_eq_iff_eq_neg.1 h0

variable {k : Type} [Field k]

theorem exists_units_orderOf_eq_of_dvd_card_sub_one [Finite k] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card k - 1) : ∃ ζ : kˣ, orderOf ζ = p := by
  have : Fact p.Prime := ⟨hp⟩
  exact exists_prime_orderOf_dvd_card' p (by rwa [Nat.card_units])

theorem rootChar_mulSingle_eq_zpow {τ : Tag} (i : Fin τ.rank) (ζ : kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (Pi.mulSingle i ζ) v = ζ ^ v i := by
  rw [rootChar, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, one_zpow])
    (fun hi => absurd (Finset.mem_univ i) hi), Pi.mulSingle_eq_same]

theorem rootDiagUnit_mulSingle_mem_torusTorsion {p : ℕ} {ζ : kˣ} (hζ : orderOf ζ = p)
    (i : Fin Tag.G2.rank) : rootDiagUnit .G2 (Pi.mulSingle i ζ) ∈ torusTorsion k p := by
  rw [rootDiagUnit_mem_torusTorsion_iff, ← Pi.mulSingle_pow, ← hζ, pow_orderOf_eq_one,
    Pi.mulSingle_one]

theorem natCast_mul_smul_apply_eq_of_rootChar {τ : Tag} {p : ℕ} {ζ : kˣ} (hζ : orderOf ζ = p)
    {i : Fin τ.rank} {w : WeylGroup τ} {m : ℕ}
    (h : ∀ v : Fin τ.rank → ℤ,
      rootChar (Pi.mulSingle i ζ ^ m) (w • v) = rootChar (Pi.mulSingle i ζ) v)
    (v : Fin τ.rank → ℤ) : (m : ZMod p) * ((w • v) i : ZMod p) = v i := by
  have h0 := h v
  rw [rootChar_pow_tuple, rootChar_mulSingle_eq_zpow, rootChar_mulSingle_eq_zpow, ← zpow_natCast,
    ← zpow_mul, zpow_eq_zpow_iff_modEq, hζ, ← ZMod.intCast_eq_intCast_iff] at h0
  rw [← h0]
  push_cast
  ring

theorem G2_eq_one_of_mem_rootCharStabilizer {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) {ζ : kˣ}
    (hζ : orderOf ζ = p) {w : WeylGroup .G2}
    (hw : ∀ i, w ∈ rootCharStabilizer (Pi.mulSingle i ζ)) : w = 1 := by
  have h : ∀ (v : Fin Tag.G2.rank → ℤ) (i : Fin Tag.G2.rank),
      (1 : ZMod p) * ((w • v) i : ZMod p) = v i := fun v i => by
    have hwi : ∀ v : Fin Tag.G2.rank → ℤ,
        rootChar (Pi.mulSingle i ζ) (w • v) = rootChar (Pi.mulSingle i ζ) v := hw i
    have := natCast_mul_smul_apply_eq_of_rootChar (m := 1) hζ (fun v => by
      rw [pow_one]; exact hwi v) v
    rwa [Nat.cast_one] at this
  rcases G2_weyl_eq_one_or_neg_of_scalar_mod hp3 h with ⟨h1, -⟩ | ⟨-, h1⟩
  · exact h1
  · have : Fact (2 < p) := ⟨by omega⟩
    exact absurd h1.symm ZMod.neg_one_ne_one

theorem G2_root_eq_or_natAbs_ia_le {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    α = g2r ∨ α = -g2r ∨ (α g2ia ≠ 0 ∧ (α g2ia).natAbs ≤ 2) := by
  rcases g2_root_cases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr ⟨by decide, by decide⟩)

theorem G2_eq_g2r_of_mem_rootCharKernel {p : ℕ} (hp3 : 3 < p) {ζ : kˣ} (hζ : orderOf ζ = p)
    {α : Fin Tag.G2.rank → ℤ}
    (hα : α ∈ rootCharKernel (Pi.mulSingle g2ia ζ) ∩ {β | IsRoot .G2 β ∧ 0 < height β}) :
    α = g2r := by
  obtain ⟨⟨hroot, hchar⟩, -, hpos⟩ := hα
  rw [rootChar_mulSingle_eq_zpow, ← orderOf_dvd_iff_zpow_eq_one, hζ] at hchar
  rcases G2_root_eq_or_natAbs_ia_le hroot with rfl | rfl | ⟨h0, h2⟩
  · rfl
  · exact absurd hpos (by decide)
  · exact absurd hchar (not_dvd_of_natAbs_lt h0 (by omega))

theorem isElementaryAbelian_torusTorsion (p : ℕ) :
    CFSG.IsElementaryAbelian p (torusTorsion k p) := by
  have hTcomm := (triangular_borel_structure.{0, 0} .G2 k).1
  exact
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact hTcomm _ (torusTorsion_le_torusGroup p x.2) _ (torusTorsion_le_torusGroup p y.2))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [SubgroupClass.coe_pow, (mem_torusTorsion_iff.1 x.2).2]
        rfl) }

theorem G2_adjointGroup_inf_centralizer_torusTorsion [Finite k] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ Nat.card k - 1) :
    adjointGroup .G2 k ⊓ Subgroup.centralizer (torusTorsion k p : Set (ModGL .G2 k)) =
      torusGroup .G2 k := by
  have : Fact p.Prime := ⟨hp⟩
  have hTcomm := (triangular_borel_structure.{0, 0} .G2 k).1
  refine le_antisymm (fun z hz => ?_) (le_inf torusGroup_le_adjointGroup_G2 fun h hh =>
    Subgroup.mem_centralizer_iff.2 fun x hx => hTcomm _ (torusTorsion_le_torusGroup p hx) _ hh)
  obtain ⟨hzC, hzV⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one hp hpq
  have hX : ∀ i, z ∈ toralCentralizer .G2 k (Pi.mulSingle i ζ) := fun i =>
    mem_toralCentralizer.2 ⟨hzC, by
      rw [Subgroup.mem_centralizer_iff.1 hzV _ (rootDiagUnit_mulSingle_mem_torusTorsion hζ i),
        mul_inv_cancel_right]⟩
  have hB := Chevalley_toral_centralizer_Bruhat_factors .G2 k (Pi.mulSingle g2ia ζ)
  obtain ⟨w, hw, h, hh, u, hu, v, hv, hz1⟩ := hB.1 z (hX g2ia)
  obtain ⟨w', hw', h', hh', u', hu', v', hv', hz2⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors .G2 k (Pi.mulSingle g2ir ζ)).1 z (hX g2ir)
  obtain ⟨hww, -, -, -⟩ := hB.2.1 w w' h h' u u' v v' hh hh'
    (rootSpan_le_posUnipotent (fun α hα => hα.2) hu)
    (rootSpan_le_posUnipotent (fun α hα => hα.2) hu')
    (rootSpan_mono Set.inter_subset_right hv) (rootSpan_mono Set.inter_subset_right hv')
    (hz1.symm.trans hz2)
  rw [← hww] at hw'
  have hw1 : w = 1 := G2_eq_one_of_mem_rootCharStabilizer hp3 hζ fun i => by
    rcases fin_G2_cases i with rfl | rfl
    · exact hw
    · exact hw'
  subst hw1
  have hbot : rootSpan .G2 k (∅ : Set (Fin Tag.G2.rank → ℤ)) = ⊥ := by simp [rootSpan]
  rw [inversionSet_one, Set.inter_empty, hbot, Subgroup.mem_bot] at hv
  subst hv
  have hS : rootCharKernel (Pi.mulSingle g2ia ζ) ∩ {β | IsRoot .G2 β ∧ 0 < height β} ⊆ {g2r} :=
    fun α hα => G2_eq_g2r_of_mem_rootCharKernel hp3 hζ hα
  have hur : u ∈ rootSubgroup .G2 k g2r := by
    have := rootSpan_mono hS hu
    rwa [rootSpan_singleton] at this
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hur
  rw [canonicalRep_one, mul_one, mul_one] at hz1
  have hfix := (mem_toralCentralizer.1 (hX g2ir)).2
  have e1 := conj_rootDiagUnit_of_mem_torusGroup (Pi.mulSingle g2ir ζ) hh
  have e2 := rootDiagUnit_conj_pinnedX (Pi.mulSingle g2ir ζ) isRoot_g2r c
  rw [rootChar_mulSingle_eq_zpow, g2r_ir, zpow_one] at e2
  have e3 : rootDiagUnit .G2 (Pi.mulSingle g2ir ζ) * (h * pinnedX .G2 k g2r c) *
      (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ))⁻¹ = h * pinnedX .G2 k g2r ((ζ : k) * c) := by
    calc _ = (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ) * h *
          (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ))⁻¹) *
          (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ) * pinnedX .G2 k g2r c *
            (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ))⁻¹) := by group
      _ = _ := by rw [e1, e2]
  rw [hz1, e3] at hfix
  have hc := pinnedX_injective .G2 k g2r (mul_left_cancel hfix)
  have hζ1 : (ζ : k) ≠ 1 := fun h1 => by
    rw [show ζ = 1 from Units.ext h1, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  have hc0 : c = 0 := by
    have : ((ζ : k) - 1) * c = 0 := by rw [sub_mul, one_mul, hc, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hζ1)
  rw [hz1, hc0, pinnedX_zero, mul_one]
  exact hh

theorem mem_normalizer_torusTorsion_of_mem_normalizer {p : ℕ} {g : ModGL .G2 k}
    (hg : g ∈ Subgroup.normalizer (torusGroup .G2 k : Set (ModGL .G2 k))) :
    g ∈ Subgroup.normalizer (torusTorsion k p : Set (ModGL .G2 k)) := by
  refine Subgroup.mem_normalizer_iff.2 fun x => ?_
  rw [mem_torusTorsion_iff, mem_torusTorsion_iff, conj_pow, conj_eq_one_iff,
    ← Subgroup.mem_normalizer_iff.1 hg x]

theorem mul_canonicalRep_mem_adjointGroup_inf_normalizer {p : ℕ} {h : ModGL .G2 k}
    (hh : h ∈ torusGroup .G2 k) (w : WeylGroup .G2) :
    h * canonicalRep (coxeterSystem .G2) k w ∈
      adjointGroup .G2 k ⊓ Subgroup.normalizer (torusTorsion k p : Set (ModGL .G2 k)) :=
  Subgroup.mem_inf.2 ⟨mul_mem (torusGroup_le_adjointGroup_G2 hh)
      (canonicalRep_mem_adjointGroup (coxeterSystem .G2) k w),
    mem_normalizer_torusTorsion_of_mem_normalizer
      (mul_mem (Subgroup.le_normalizer hh) (canonicalRep_mem_normalizer (R := k) w))⟩

theorem eq_and_eq_of_mul_canonicalRep_eq {τ : Tag} {h h' : ModGL τ k}
    (hh : h ∈ torusGroup τ k) (hh' : h' ∈ torusGroup τ k) {w w' : WeylGroup τ}
    (heq : h * canonicalRep (coxeterSystem τ) k w = h' * canonicalRep (coxeterSystem τ) k w') :
    h = h' ∧ w = w' := by
  obtain ⟨hw, hhh, -, -⟩ := (Chevalley_toral_centralizer_Bruhat_factors τ k 1).2.1 w w' h h' 1 1 1
    1 hh hh' (one_mem _) (one_mem _) (one_mem _) (one_mem _) (by simpa only [mul_one] using heq)
  exact ⟨hhh, hw⟩

theorem G2_exists_eq_mul_canonicalRep_of_mem_normalizer [Finite k] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ Nat.card k - 1) {g : ModGL .G2 k}
    (hg : g ∈ adjointGroup .G2 k ⊓ Subgroup.normalizer (torusTorsion k p : Set (ModGL .G2 k))) :
    ∃ h ∈ torusGroup .G2 k, ∃ w : WeylGroup .G2, g = h * canonicalRep (coxeterSystem .G2) k w := by
  obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 hg
  have hTB := triangular_borel_structure.{0, 0} .G2 k
  have hB := Chevalley_toral_centralizer_Bruhat_factors .G2 k 1
  have hg1 : g ∈ toralCentralizer .G2 k 1 :=
    mem_toralCentralizer.2 ⟨hgC, by rw [rootDiagUnit_one, one_mul, inv_one, mul_one]⟩
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgeq⟩ := hB.1 g hg1
  have huU : u ∈ posUnipotent .G2 k := rootSpan_le_posUnipotent (fun α hα => hα.2) hu
  have hvI : v ∈ rootSpan .G2 k (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have hnN := canonicalRep_mem_normalizer (R := k) w
  have hnC := canonicalRep_mem_adjointGroup (coxeterSystem .G2) k w
  set n := canonicalRep (coxeterSystem .G2) k w with hn
  have key : ∀ x ∈ torusTorsion k p, g * x * g⁻¹ = n * x * n⁻¹ := by
    intro x hx
    have hxT := torusTorsion_le_torusGroup p hx
    have hyT := torusTorsion_le_torusGroup p ((Subgroup.mem_normalizer_iff.1 hgN x).1 hx)
    have htT : n * x * n⁻¹ ∈ torusGroup .G2 k := (Subgroup.mem_normalizer_iff.1 hnN x).1 hxT
    have hu' : (n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹)⁻¹⁻¹ ∈ posUnipotent .G2 k :=
      (Subgroup.mem_normalizer_iff.1 (hTB.2.2.1 (inv_mem htT)) u).1 huU
    have hv' : x⁻¹ * v * x⁻¹⁻¹ ∈ rootSpan .G2 k (inversionSet w) := by
      have hmap := map_rootSpan_of_forall (S := inversionSet w)
        (f := (MulAut.conj x⁻¹).toMonoidHom) fun α hα =>
          map_conj_rootSubgroup_of_mem_torusGroup (inv_mem hxT) hα.1
      rw [← hmap]
      exact ⟨v, hvI, rfl⟩
    have heq : h * (n * x * n⁻¹) * ((n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹)⁻¹⁻¹) * n *
        (x⁻¹ * v * x⁻¹⁻¹) = g * x * g⁻¹ * h * u * n * v := by
      rw [hgeq]
      group
    obtain ⟨-, h1, -⟩ := hB.2.1 w w _ _ _ _ _ _ (mul_mem hh htT) (mul_mem hyT hh) hu' huU hv' hvI
      heq
    exact (mul_left_cancel (h1.trans (hTB.1 _ hyT _ hh))).symm
  have hm : n⁻¹ * g ∈
      adjointGroup .G2 k ⊓ Subgroup.centralizer (torusTorsion k p : Set (ModGL .G2 k)) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hnC) hgC,
      Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    calc x * (n⁻¹ * g) = n⁻¹ * (n * x * n⁻¹) * g := by group
      _ = n⁻¹ * (g * x * g⁻¹) * g := by rw [key x hx]
      _ = n⁻¹ * g * x := by group
  rw [G2_adjointGroup_inf_centralizer_torusTorsion hp hp3 hpq] at hm
  exact ⟨n * (n⁻¹ * g) * n⁻¹, (Subgroup.mem_normalizer_iff.1 hnN _).1 hm, w, by rw [← hn]; group⟩

theorem G2_weyl_eq_one_or_neg_of_conj_eq_pow [Finite k] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card k - 1) {h : ModGL .G2 k} (hh : h ∈ torusGroup .G2 k) (w : WeylGroup .G2)
    (a : ZMod p)
    (hconj : ∀ x ∈ torusTorsion k p, h * canonicalRep (coxeterSystem .G2) k w * x *
      (h * canonicalRep (coxeterSystem .G2) k w)⁻¹ = x ^ a.val) :
    (w = 1 ∧ a = 1) ∨ ((∀ v : Fin Tag.G2.rank → ℤ, w • v = -v) ∧ a = -1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hTcomm := (triangular_borel_structure.{0, 0} .G2 k).1
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one hp hpq
  refine G2_weyl_eq_one_or_neg_of_scalar_mod hp3 fun v i => ?_
  have hnN := canonicalRep_mem_normalizer (R := k) w
  obtain ⟨n, hn⟩ : ∃ n, canonicalRep (coxeterSystem .G2) k w = n := ⟨_, rfl⟩
  rw [hn] at hnN hconj
  have hsT : n * rootDiagUnit .G2 (Pi.mulSingle i ζ) * n⁻¹ ∈ torusGroup .G2 k :=
    (Subgroup.mem_normalizer_iff.1 hnN _).1 (rootDiagUnit_mem_torusGroup_G2 _)
  have h1 := hconj _ (rootDiagUnit_mulSingle_mem_torusTorsion hζ i)
  have h2 : h * n * rootDiagUnit .G2 (Pi.mulSingle i ζ) * (h * n)⁻¹ =
      n * rootDiagUnit .G2 (Pi.mulSingle i ζ) * n⁻¹ := by
    calc _ = h * (n * rootDiagUnit .G2 (Pi.mulSingle i ζ) * n⁻¹) * h⁻¹ := by group
      _ = _ := by rw [hTcomm h hh _ hsT, mul_inv_cancel_right]
  rw [h2, rootDiagUnit_pow] at h1
  have h3 := (rootDiagUnit_eq_conj_canonicalRep_iff (τ := .G2) (K := k)
    (Pi.mulSingle i ζ ^ a.val) (Pi.mulSingle i ζ) w).1 (by rw [hn]; exact h1.symm)
  have := natCast_mul_smul_apply_eq_of_rootChar hζ h3 v
  rwa [ZMod.natCast_zmod_val] at this

theorem mul_canonicalRep_conj_eq_inv_of_smul_eq_neg {τ : Tag} {h : ModGL τ k}
    (hh : h ∈ torusGroup τ k) {w : WeylGroup τ} (hw : ∀ v : Fin τ.rank → ℤ, w • v = -v)
    {x : ModGL τ k} (hx : x ∈ torusGroup τ k) :
    h * canonicalRep (coxeterSystem τ) k w * x * (h * canonicalRep (coxeterSystem τ) k w)⁻¹ =
      x⁻¹ := by
  have hTcomm := (triangular_borel_structure.{0, 0} τ k).1
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  have hinv : (rootDiagUnit τ b)⁻¹ = rootDiagUnit τ b⁻¹ := (map_inv (rootDiagUnitHom τ k) b).symm
  have hn := ((rootDiagUnit_eq_conj_canonicalRep_iff b⁻¹ b w).2 fun v => by
    rw [hw, rootChar_inv_apply, rootChar_neg_eq_inv, inv_inv]).symm
  have hbT : rootDiagUnit τ b⁻¹ ∈ torusGroup τ k := by
    rw [← hinv]
    exact inv_mem hx
  calc _ = h * (canonicalRep (coxeterSystem τ) k w * rootDiagUnit τ b *
        (canonicalRep (coxeterSystem τ) k w)⁻¹) * h⁻¹ := by group
    _ = (rootDiagUnit τ b)⁻¹ := by rw [hn, hTcomm h hh _ hbT, mul_inv_cancel_right, hinv]

theorem G2_toral_prime_plane_centralizer_and_scalar_normalizers (k : Type) [Field k] [Finite k]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card k - 1) :
    CFSG.IsElementaryAbelian p (torusTorsion k p) ∧ Nat.card (torusTorsion k p) = p ^ 2 ∧
    adjointGroup .G2 k ⊓ Subgroup.centralizer (torusTorsion k p : Set (ModGL .G2 k)) =
      torusGroup .G2 k ∧
    (∀ g ∈ adjointGroup .G2 k ⊓ Subgroup.normalizer (torusTorsion k p : Set (ModGL .G2 k)),
      ∃ h ∈ torusGroup .G2 k, ∃ w : WeylGroup .G2,
        g = h * canonicalRep (coxeterSystem .G2) k w) ∧
    (∀ h ∈ torusGroup .G2 k, ∀ h' ∈ torusGroup .G2 k, ∀ w w' : WeylGroup .G2,
      h * canonicalRep (coxeterSystem .G2) k w = h' * canonicalRep (coxeterSystem .G2) k w' →
        h = h' ∧ w = w') ∧
    (∀ h ∈ torusGroup .G2 k, ∀ w : WeylGroup .G2, h * canonicalRep (coxeterSystem .G2) k w ∈
      adjointGroup .G2 k ⊓ Subgroup.normalizer (torusTorsion k p : Set (ModGL .G2 k))) ∧
    (∀ h ∈ torusGroup .G2 k, ∀ (w : WeylGroup .G2) (a : ZMod p),
      (∀ x ∈ torusTorsion k p, h * canonicalRep (coxeterSystem .G2) k w * x *
        (h * canonicalRep (coxeterSystem .G2) k w)⁻¹ = x ^ a.val) →
      (w = 1 ∧ a = 1) ∨ ((∀ v : Fin Tag.G2.rank → ℤ, w • v = -v) ∧ a = -1)) ∧
    (∀ h ∈ torusGroup .G2 k, ∀ w : WeylGroup .G2, (∀ v : Fin Tag.G2.rank → ℤ, w • v = -v) →
      ∀ x ∈ torusTorsion k p, h * canonicalRep (coxeterSystem .G2) k w * x *
        (h * canonicalRep (coxeterSystem .G2) k w)⁻¹ = x⁻¹) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  exact ⟨isElementaryAbelian_torusTorsion p, natCard_torusTorsion hpq,
    G2_adjointGroup_inf_centralizer_torusTorsion hp hp3 hpq,
    fun g hg => G2_exists_eq_mul_canonicalRep_of_mem_normalizer hp hp3 hpq hg,
    fun h hh h' hh' w w' heq => eq_and_eq_of_mul_canonicalRep_eq hh hh' heq,
    fun h hh w => mul_canonicalRep_mem_adjointGroup_inf_normalizer hh w,
    fun h hh w a hconj => G2_weyl_eq_one_or_neg_of_conj_eq_pow hp hp3 hpq hh w a hconj,
    fun h hh w hw x hx => mul_canonicalRep_conj_eq_inv_of_smul_eq_neg hh hw
      (torusTorsion_le_torusGroup p hx)⟩

end CFSG.RankThree.Chevalley
