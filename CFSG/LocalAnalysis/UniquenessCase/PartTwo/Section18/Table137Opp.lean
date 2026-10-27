module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.LineChar
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93a
public import CFSG.CGT.PushingUpLit.CGT6K1.InnerEven
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement Matrix

theorem nonempty_bar2_opp_equiv_of_surjective {G S : Type} [Group G] [Group S] [Finite G]
    {p : ℕ} (hp : p.Prime) (C : Subgroup G) (g : ↥C →* S) (hg : Function.Surjective g)
    (hker : IsPGroup 2 g.ker) (hS : CFSG.Open.IsQuasisimple S) (hS2 : CFSG.pCore 2 S = ⊥)
    {x : S} (hx : x ∉ Subgroup.center S) (hxp : ∃ k : ℕ, orderOf x = p ^ k) :
    Nonempty (Bar2 (Opp p C) ≃* S) := by
  classical
  have hOC : Opp p C ≤ C := (Subgroup.closure_le C).mpr fun _ h => h.1
  let g' : ↥(Opp p C) →* S := g.comp (Subgroup.inclusion hOC)
  have hN : g'.range.Normal := by
    refine ⟨fun y hy s => ?_⟩
    obtain ⟨o, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := hg s
    refine ⟨⟨(c : G) * o * (c : G)⁻¹, F09.conj_mem_opp_self c.2 o.2⟩, ?_⟩
    have hco : Subgroup.inclusion hOC ⟨(c : G) * o * (c : G)⁻¹, F09.conj_mem_opp_self c.2 o.2⟩ =
        c * Subgroup.inclusion hOC o * c⁻¹ := Subtype.ext rfl
    simp only [g', MonoidHom.comp_apply, hco, map_mul, map_inv]
  obtain ⟨c₀, hc₀⟩ := hg x
  obtain ⟨a, m, hpm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c₀).ne' p hp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hpm (dvd_zero p)
  have hc : orderOf (c₀ ^ m) = p ^ a := by
    rw [orderOf_pow_of_dvd hm0 (hord ▸ dvd_mul_left m (p ^ a)), hord,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hcO : ((c₀ ^ m : ↥C) : G) ∈ Opp p C :=
    Subgroup.subset_closure ⟨(c₀ ^ m).2, a, by rw [Subgroup.orderOf_coe, hc]⟩
  have hxm : x ^ m ∉ Subgroup.center S := by
    intro hxm
    obtain ⟨k, hk⟩ := hxp
    have hcop : m.Coprime (orderOf x) := by
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_comm).mp ((hp.coprime_iff_not_dvd).mpr hpm))
    obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hcop
    exact hx (hr ▸ Subgroup.pow_mem _ hxm r)
  have hmem : x ^ m ∈ g'.range := ⟨⟨_, hcO⟩, by
    simp only [g', MonoidHom.comp_apply]
    rw [← hc₀, ← map_pow]
    rfl⟩
  have htop : g'.range = ⊤ := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hS g'.range with
      h | h
    · exact absurd (h hmem) hxm
    · exact h
  have hker' : IsPGroup 2 g'.ker := by
    have h := hker.comap_of_injective (Subgroup.inclusion hOC) (Subgroup.inclusion_injective hOC)
    rwa [MonoidHom.comap_ker] at h
  exact CFSG.RankThree.PartTwo.Sec15.Proof15Res7.nonempty_quot_pCore_two_equiv g'
    (MonoidHom.range_eq_top.mp htop) hker' hS2

theorem mem_vecStab_subtype {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {M : Subgroup (GL ι F)} {w : ι → F} {g : ↥M} :
    g ∈ KTabC.vecStab M.subtype w ↔ ((g : GL ι F) : Matrix ι ι F) *ᵥ w = w := Iff.rfl

@[expose] def centVecEquivVecStab {W : Type} [Group W] {H : Subgroup (MulAut W)}
    {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] {M : Subgroup (GL ι F)}
    (ε : ↥H ≃* ↥M) (v : W) (w : ι → F)
    (hiff : ∀ l : ↥H, (l : MulAut W) v = v ↔
      ((ε l : GL ι F) : Matrix ι ι F) *ᵥ w = w) :
    ↥(centVec H v) ≃* ↥(KTabC.vecStab M.subtype w) where
  toFun c := ⟨ε ⟨c, (centVec.mem_centVec.mp c.2).1⟩,
    (hiff _).mp (centVec.mem_centVec.mp c.2).2⟩
  invFun g := ⟨((ε.symm g : ↥H) : MulAut W), centVec.mem_centVec.mpr
    ⟨(ε.symm g).2, (hiff _).mpr (by rw [MulEquiv.apply_symm_apply]; exact g.2)⟩⟩
  left_inv c := by
    apply Subtype.ext
    simp
  right_inv g := by
    apply Subtype.ext
    simp
  map_mul' c d := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul]
    rfl

theorem nonempty_bar2_opp_centVec_equiv {W : Type} [Group W] [Finite (MulAut W)]
    {H : Subgroup (MulAut W)} {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {M : Subgroup (GL ι F)} (ε : ↥H ≃* ↥M) (v : W) (w : ι → F)
    (hiff : ∀ l : ↥H, (l : MulAut W) v = v ↔ ((ε l : GL ι F) : Matrix ι ι F) *ᵥ w = w)
    {S : Type} [Group S] (σ : ↥(KTabC.vecStab M.subtype w) →* S) (hσ : Function.Surjective σ)
    (hker : IsPGroup 2 σ.ker) (hS : CFSG.Open.IsQuasisimple S) (hS2 : CFSG.pCore 2 S = ⊥)
    {p : ℕ} (hp : p.Prime) {x : S} (hx : x ∉ Subgroup.center S)
    (hxp : ∃ k : ℕ, orderOf x = p ^ k) :
    Nonempty (Bar2 (Opp p (centVec H v)) ≃* S) := by
  let e := centVecEquivVecStab ε v w hiff
  refine nonempty_bar2_opp_equiv_of_surjective hp (centVec H v) (σ.comp e.toMonoidHom)
    (hσ.comp e.surjective) ?_ hS hS2 hx hxp
  have h := hker.comap_of_injective e.toMonoidHom e.injective
  rwa [MonoidHom.comap_ker] at h

theorem opp_centVec_eq_bot_of_vecStab {W : Type} [Group W]
    {H : Subgroup (MulAut W)} {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {M : Subgroup (GL ι F)} (ε : ↥H ≃* ↥M) (v : W) (w : ι → F)
    (hiff : ∀ l : ↥H, (l : MulAut W) v = v ↔ ((ε l : GL ι F) : Matrix ι ι F) *ᵥ w = w)
    {p : ℕ} (h1 : ∀ g : ↥(KTabC.vecStab M.subtype w), ∀ k : ℕ, orderOf g = p ^ k → g = 1) :
    Opp p (centVec H v) = ⊥ := by
  let e := centVecEquivVecStab ε v w hiff
  refine le_bot_iff.mp ((Subgroup.closure_le _).mpr ?_)
  rintro y ⟨hy, k, hk⟩
  have hk' : orderOf (e ⟨y, hy⟩) = p ^ k := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hk]
  have h := h1 _ k hk'
  have : (⟨y, hy⟩ : ↥(centVec H v)) = 1 := e.injective (by rw [h, map_one])
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

theorem nonempty_bar2_opp_equiv_of_le_range {G T : Type} [Group G] [Group T] [Finite G]
    {p : ℕ} (hp : p.Prime) (C : Subgroup G) (g : ↥C →* T) (hker : IsPGroup 2 g.ker)
    {S : Subgroup T} (hSle : S ≤ g.range)
    (hpS : ∀ c : ↥C, (∃ k : ℕ, orderOf c = p ^ k) → g c ∈ S)
    (hS : CFSG.Open.IsQuasisimple S) (hS2 : CFSG.pCore 2 S = ⊥)
    {x : S} (hx : x ∉ Subgroup.center S) (hxp : ∃ k : ℕ, orderOf x = p ^ k) :
    Nonempty (Bar2 (Opp p C) ≃* S) := by
  classical
  have hOC : Opp p C ≤ C := (Subgroup.closure_le C).mpr fun _ h => h.1
  have hmemS : ∀ o : ↥(Opp p C), g (Subgroup.inclusion hOC o) ∈ S := by
    have hle : Opp p C ≤ (S.comap g).map C.subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hy, k, hk⟩
      exact ⟨⟨y, hy⟩, hpS ⟨y, hy⟩ ⟨k, by rw [Subgroup.orderOf_mk, hk]⟩, rfl⟩
    intro o
    obtain ⟨c, hc, hco⟩ := hle o.2
    have hc' : c = Subgroup.inclusion hOC o := Subtype.ext hco
    rw [← hc']
    exact hc
  let g' : ↥(Opp p C) →* ↥S := (g.comp (Subgroup.inclusion hOC)).codRestrict S hmemS
  have hg' : ∀ o, ((g' o : ↥S) : T) = g (Subgroup.inclusion hOC o) := fun _ => rfl
  have hN : g'.range.Normal := by
    refine ⟨fun y hy s => ?_⟩
    obtain ⟨o, rfl⟩ := hy
    obtain ⟨c, hc⟩ := hSle s.2
    refine ⟨⟨(c : G) * o * (c : G)⁻¹, F09.conj_mem_opp_self c.2 o.2⟩, ?_⟩
    have hco : Subgroup.inclusion hOC ⟨(c : G) * o * (c : G)⁻¹, F09.conj_mem_opp_self c.2 o.2⟩ =
        c * Subgroup.inclusion hOC o * c⁻¹ := Subtype.ext rfl
    apply Subtype.ext
    rw [hg', hco, map_mul, map_mul, map_inv, hc, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hg']
  obtain ⟨c₀, hc₀⟩ := hSle x.2
  obtain ⟨a, m, hpm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c₀).ne' p hp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hpm (dvd_zero p)
  have hc : orderOf (c₀ ^ m) = p ^ a := by
    rw [orderOf_pow_of_dvd hm0 (hord ▸ dvd_mul_left m (p ^ a)), hord,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hcO : ((c₀ ^ m : ↥C) : G) ∈ Opp p C :=
    Subgroup.subset_closure ⟨(c₀ ^ m).2, a, by rw [Subgroup.orderOf_coe, hc]⟩
  have hxm : x ^ m ∉ Subgroup.center S := by
    intro hxm
    obtain ⟨k, hk⟩ := hxp
    have hcop : m.Coprime (orderOf x) := by
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_comm).mp ((hp.coprime_iff_not_dvd).mpr hpm))
    obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hcop
    exact hx (hr ▸ Subgroup.pow_mem _ hxm r)
  have hincl : Subgroup.inclusion hOC ⟨((c₀ ^ m : ↥C) : G), hcO⟩ = c₀ ^ m := Subtype.ext rfl
  have hmem : x ^ m ∈ g'.range := ⟨⟨_, hcO⟩, Subtype.ext (by
    rw [hg', hincl, map_pow, hc₀, Subgroup.coe_pow])⟩
  have htop : g'.range = ⊤ := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hS g'.range with
      h | h
    · exact absurd (h hmem) hxm
    · exact h
  have hker' : IsPGroup 2 g'.ker := by
    have h := hker.comap_of_injective (Subgroup.inclusion hOC) (Subgroup.inclusion_injective hOC)
    rw [MonoidHom.comap_ker] at h
    have hk : g'.ker = (g.comp (Subgroup.inclusion hOC)).ker := by
      ext o
      simp only [MonoidHom.mem_ker]
      constructor
      · intro h1
        have := congrArg Subtype.val h1
        rwa [hg'] at this
      · intro h1
        exact Subtype.ext (by rw [hg']; exact h1)
    rwa [hk]
  exact CFSG.RankThree.PartTwo.Sec15.Proof15Res7.nonempty_quot_pCore_two_equiv g'
    (MonoidHom.range_eq_top.mp htop) hker' hS2

@[expose] def vecStabEquivOfIff {ι ι' F : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] [Field F] {M : Subgroup (GL ι F)} {M' : Subgroup (GL ι' F)}
    (φ : ↥M ≃* ↥M') (x : ι → F) (y : ι' → F)
    (hiff : ∀ g : ↥M, ((g : GL ι F) : Matrix ι ι F) *ᵥ x = x ↔
      ((φ g : GL ι' F) : Matrix ι' ι' F) *ᵥ y = y) :
    ↥(KTabC.vecStab M.subtype x) ≃* ↥(KTabC.vecStab M'.subtype y) where
  toFun g := ⟨φ g.1, (hiff g.1).mp g.2⟩
  invFun g := ⟨φ.symm g.1, (hiff _).mpr (by rw [MulEquiv.apply_symm_apply]; exact g.2)⟩
  left_inv g := Subtype.ext (φ.symm_apply_apply g.1)
  right_inv g := Subtype.ext (φ.apply_symm_apply g.1)
  map_mul' g g' := Subtype.ext (map_mul φ g.1 g'.1)

section SL2

open scoped MatrixGroups

theorem sl2_inputs {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ Nat.card F + 1) :
    CFSG.Open.IsQuasisimple SL(2, F) ∧ CFSG.pCore 2 SL(2, F) = ⊥ ∧
      ∃ x : SL(2, F), x ∉ Subgroup.center SL(2, F) ∧ ∃ k : ℕ, orderOf x = p ^ k := by
  classical
  haveI := Fintype.ofFinite F
  have hq : CFSG.Open.IsQuasisimple SL(2, F) := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact CFSG.CGT.PushingUpLit.BHS.isQuasisimple_special_linear_two ⟨s, hs⟩
  have hZ : Subgroup.center SL(2, F) = ⊥ :=
    CFSG.CGT.PushingUpLit.CGT6K1.center_SL_two_eq_bot_of_charTwo
  refine ⟨hq, le_bot_iff.mp (hZ ▸ GL83.I243.pCore_le_center Nat.prime_two hq), ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have hdvd : p ∣ Nat.card SL(2, F) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F,
      CFSG.ClassicalGroups.Unitary.sq_sub_one_eq (Nat.card F) hq1]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hpq _) _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨x, ?_, 1, by rw [pow_one, hx]⟩
  rw [hZ, Subgroup.mem_bot]
  rintro rfl
  rw [orderOf_one] at hx
  exact hp.one_lt.ne hx

end SL2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
