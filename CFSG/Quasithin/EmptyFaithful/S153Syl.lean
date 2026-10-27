module

public import CFSG.Quasithin.EmptyFaithful.S153Plus
public import CFSG.Quasithin.EmptyFaithful.S153Baum

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

section Conj

variable {G : Type} [Group G]

private theorem mem_map_conj_iff (K : Subgroup G) (g x : G) :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

private theorem isMaxTwoLocal_map_conj_aux {K : Subgroup G} (hK : quasithinIsMaxTwoLocal K) (g : G) :
    quasithinIsMaxTwoLocal (K.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨?_, fun H hH hle => ?_⟩
  · obtain ⟨P, hP, hP2, hPM⟩ := hK.1
    refine ⟨P.map (MulAut.conj g).toMonoidHom, ?_, hP2.map _, ?_⟩
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
    · rw [hPM]
      exact Subgroup.map_equiv_normalizer_eq P (MulAut.conj g)
  · have hH' : IsTwoLocal (H.map (MulAut.conj g⁻¹).toMonoidHom) := by
      obtain ⟨P, hP, hP2, hPH⟩ := hH
      refine ⟨P.map (MulAut.conj g⁻¹).toMonoidHom, ?_, hP2.map _, ?_⟩
      · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective]
      · rw [hPH]
        exact Subgroup.map_equiv_normalizer_eq P (MulAut.conj g⁻¹)
    have hKH : K ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro m hm
      rw [mem_map_conj_iff, inv_inv]
      apply hle
      rw [mem_map_conj_iff]
      simpa [mul_assoc] using hm
    have heq := hK.2 _ hH' hKH
    ext x
    rw [mem_map_conj_iff, ← heq, mem_map_conj_iff, inv_inv]
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]

theorem isUniqueM_of_map_conj {X M : Subgroup G} {g : G} (hg : g ∈ M)
    (hU : IsUniqueM (X.map (MulAut.conj g).toMonoidHom) M) : IsUniqueM X M := by
  have hXM : X ≤ M := fun x hx => by
    have h1 : g * x * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := by
      rw [mem_map_conj_iff]
      simpa [mul_assoc] using hx
    have h2 := hU.1.2 h1
    have := M.mul_mem (M.mul_mem (M.inv_mem hg) h2) hg
    simpa [mul_assoc] using this
  refine ⟨⟨hU.1.1, hXM⟩, fun M' hM' => ?_⟩
  have h1 : quasithinIsMaxTwoLocal (M'.map (MulAut.conj g).toMonoidHom) :=
    isMaxTwoLocal_map_conj_aux hM'.1 g
  have h2 : X.map (MulAut.conj g).toMonoidHom ≤ M'.map (MulAut.conj g).toMonoidHom :=
    Subgroup.map_mono hM'.2
  have h3 := hU.2 _ ⟨h1, h2⟩
  ext x
  have e : x ∈ M' ↔ g * x * g⁻¹ ∈ M'.map (MulAut.conj g).toMonoidHom := by
    rw [mem_map_conj_iff]
    simp [mul_assoc]
  rw [e, h3]
  constructor
  · intro hx
    have := M.mul_mem (M.mul_mem (M.inv_mem hg) hx) hg
    simpa [mul_assoc] using this
  · intro hx
    exact M.mul_mem (M.mul_mem hg hx) (M.inv_mem hg)

private theorem conj_map_eq_of_mem_normalizer_aux {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) : S.map (MulAut.conj g).toMonoidHom = S := by
  ext x
  rw [mem_map_conj_iff]
  have := Subgroup.mem_normalizer_iff.mp (inv_mem hg) x
  simpa using this.symm

end Conj

section Generic

variable {G : Type} [Group G]

private theorem exists_odd_not_mem_of_oTwoUpper {K C : Subgroup G} (h : ¬ oTwoUpper K ≤ C) :
    ∃ z ∈ oTwoUpper K, Odd (orderOf z) ∧ z ∉ C := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hxK, hxodd⟩
  exact hcon x (mem_oTwoUpper_of_odd hxK hxodd) hxodd

end Generic

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem Y153_not_le_centralizer (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    ¬ Y153 Mc M ≤ Subgroup.centralizer (VZ T M : Set G) := by
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  intro hle
  have e : autI h.elemAbelian (Y153 Mc M) = oTwoUpper (autI h.elemAbelian M) :=
    h.autOn_Y153 h113
  rw [autI_eq_bot_of_le_centralizer h.elemAbelian hle] at e
  exact hS.oTwoUpper_ne_bot e.symm

theorem exists_mem_Yplus_acts (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) :
    ∃ (hV : IsElemAbelian 2 (VZ T M))
      (L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) hV))) (tb : MulAut (IntMod (VZ T M) hV)),
      OfourStruct (autI hV M) L₁ L₂ tb ∧ V₁ = (commV L₁).map (inclMod hV) ∧
        V₂ = (commV L₂).map (inclMod hV) ∧
        ∃ (y : G) (hy : y ∈ Subgroup.normalizer (VZ T M : Set G)),
          y ∈ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ∧
            convI hV ⟨y, hy⟩ ∈ L₂ ∧ orderOf (convI hV ⟨y, hy⟩) = 3 := by
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, -⟩ := D.model
  refine ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, ?_⟩
  subst hV₁
  obtain ⟨x, hxL, hx3, hx1⟩ := exists_orderThree hS.nat₂
  have hxord : orderOf x = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hx3 hx1
  have hxM : x ∈ autI hV M := hS.L₂_le hxL
  have hxO : x ∈ oTwoUpper (autI hV M) :=
    mem_oTwoUpper_of_odd hxM (by rw [hxord]; decide)
  have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
  have hxY : x ∈ autI hV (Y153 Mc M) := by rw [e]; exact hxO
  obtain ⟨g, hgY, hg⟩ := (mem_autI hV).1 hxY
  have hgC : (g : G) ∈ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) := by
    refine (mem_centralizer_map_inclMod_iff hV g.2 (commV L₁)).2 fun u hu => ?_
    have hgx : convI hV ⟨(g : G), g.2⟩ = x := hg
    rw [hgx]
    exact hS.L₂_fix₁ hxL hu
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper
    (Y153 Mc M ⊓ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G)) (x := (g : G)) ⟨hgY, hgC⟩
  have hyN : (g : G) ^ 2 ^ k ∈ Subgroup.normalizer (VZ T M : Set G) :=
    Subgroup.pow_mem _ g.2 _
  refine ⟨(g : G) ^ 2 ^ k, hyN, hk, ?_, ?_⟩
  · have : convI hV ⟨(g : G) ^ 2 ^ k, hyN⟩ = x ^ 2 ^ k := by
      rw [← hg, ← map_pow]
      rfl
    rw [this]
    exact Subgroup.pow_mem _ hxL _
  · have : convI hV ⟨(g : G) ^ 2 ^ k, hyN⟩ = x ^ 2 ^ k := by
      rw [← hg, ← map_pow]
      rfl
    rw [this, Nat.Coprime.orderOf_pow, hxord]
    rw [hxord]
    exact Nat.Coprime.pow_right k (by norm_num)

theorem Yplus_not_le_centralizer (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) :
    ¬ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ≤
      Subgroup.centralizer (VZ T M : Set G) := by
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, y, hy, hyY, -, hord⟩ :=
    h.exists_mem_Yplus_acts h113 D
  intro hle
  have h1 : convI hV ⟨y, hy⟩ = 1 := (convI_eq_one_iff hV ⟨y, hy⟩).2 (hle hyY)
  rw [h1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem isSylowTwoOf_Sgp153 (h11 : StageLemma14111) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) {Yp I : Subgroup G} (hYpM : Yp ≤ M)
    (hz : ∃ z ∈ Yp, Odd (orderOf z) ∧ z ∉ Subgroup.centralizer (VZ T M : Set G))
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) : IsSylowTwoOf (Sgp153 T V₁) I := by
  classical
  obtain ⟨z, hzY, hzodd, hzC⟩ := hz
  set S : Subgroup G := Sgp153 T V₁ with hSdef
  have hST : S ≤ T := inf_le_left
  have hSI : S ≤ I := le_sup_right.trans hI.1.1
  have hYpI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hS2 : IsPGroup 2 S := (h.qtfe.sylow.1).to_le hST
  have hL6 := h.lemma_15_3_6 h11 D
  have hNS : Subgroup.normalizer (S : Set G) ≤ M := hL6.2.1.1.trans hL6.2.1.2
  have hTN : T ≤ Subgroup.normalizer (S : Set G) := h.T_le_normalizer_Sgp153 D
  have hidx : S.relIndex T = 2 := D.relIndex_nS h
  obtain ⟨P, hPsyl, hSP⟩ := A4.exists_isSylowTwoOf_ge hSI hS2
  by_cases hPS : P = S
  · exact hPS ▸ hPsyl
  exfalso
  have hP2 : IsPGroup 2 P := hPsyl.2.1
  have hPI : P ≤ I := hPsyl.1
  have hQ : ¬ (P ⊓ Subgroup.normalizer (S : Set G) ≤ S) := fun hle =>
    hPS (eq_of_inf_normalizer_le hP2 hSP hle).symm
  obtain ⟨n₀, hn₀Q, hn₀S⟩ := IsConcreteLE.not_le_iff_exists.mp hQ
  set Q : Subgroup G := P ⊓ Subgroup.normalizer (S : Set G) with hQdef
  have hSQ : S ≤ Q := le_inf hSP Subgroup.le_normalizer
  have hQ2 : IsPGroup 2 Q := hP2.to_le inf_le_left
  have hQI : Q ≤ I := inf_le_left.trans hPI
  have hQN : Q ≤ Subgroup.normalizer (S : Set G) := inf_le_right
  have hTsyl : IsSylowTwoOf T (Subgroup.normalizer (S : Set G)) :=
    A4.isSylowTwoOf_mono h.isSylowTwoOf hTN hNS
  obtain ⟨P', hP'syl, hQP'⟩ := A4.exists_isSylowTwoOf_ge hQN hQ2
  obtain ⟨g, hgN, hgP'⟩ := A4.exists_conj_of_isSylowTwoOf hTsyl hP'syl
  have hP'g : P' = T.map (MulAut.conj g).toMonoidHom := by
    ext y
    rw [mem_map_conj_iff]
    exact hgP' y
  have hgM : g ∈ M := hNS hgN
  have hSg : S.map (MulAut.conj g).toMonoidHom = S := conj_map_eq_of_mem_normalizer_aux hgN
  have hidx' : S.relIndex P' = 2 := by
    have h1 := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) S T
      (MulAut.conj g).injective
    rw [hSg] at h1
    rw [hP'g, h1, hidx]
  have hQP : Q = P' := by
    have h1 := Subgroup.relIndex_mul_relIndex S Q P' hSQ hQP'
    rw [hidx'] at h1
    have hne : S.relIndex Q ≠ 1 := fun h1' => hn₀S (Subgroup.relIndex_eq_one.mp h1' hn₀Q)
    have hdvd : S.relIndex Q ∣ 2 := ⟨_, h1.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h2 | h2
    · exact absurd h2 hne
    · rw [h2] at h1
      have h3 : Q.relIndex P' = 1 := by omega
      exact le_antisymm hQP' (Subgroup.relIndex_eq_one.mp h3)
  set c' : G →* G := (MulAut.conj g⁻¹).toMonoidHom with hc'
  have hTc : P'.map c' = T := by
    rw [hP'g, Subgroup.map_map]
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hc', MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      exact ⟨x, hx, by simp [hc', MulAut.conj_apply, mul_assoc]⟩
  have hYpc : Yp.map c' ≤ M := by
    rintro _ ⟨y, hy, rfl⟩
    have := M.mul_mem (M.mul_mem (M.inv_mem hgM) (hYpM hy)) hgM
    simpa [hc', MulAut.conj_apply, inv_inv] using this
  have hXe : (Yp ⊔ P').map c' = Yp.map c' ⊔ T := by rw [Subgroup.map_sup, hTc]
  have hX'T : T ≤ Yp.map c' ⊔ T := le_sup_right
  have hX'M : Yp.map c' ⊔ T ≤ M := sup_le hYpc h.T_le
  rcases h.lemma_15_3_2_four hX'T hX'M with hi | ⟨-, hU⟩
  ·
    apply hzC
    have hz' : g⁻¹ * z * g ∈ opResidual 2 (Yp.map c' ⊔ T) := by
      refine Subgroup.subset_closure ⟨Subgroup.mem_sup_left ⟨z, hzY, ?_⟩, ?_⟩
      · simp [hc']
      · have : orderOf (g⁻¹ * z * g) = orderOf z := by
          have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
          simpa [MulAut.conj_apply] using this
        rw [this]
        exact Nat.coprime_two_right.mpr hzodd
    have hcz := Subgroup.mem_centralizer_iff.mp (hi hz')
    rw [Subgroup.mem_centralizer_iff]
    intro v₀ hv₀
    have hgV : g⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer (M.inv_mem hgM)
    have hv : g⁻¹ * v₀ * g ∈ VZ T M := by
      have := (Subgroup.mem_normalizer_iff.mp hgV v₀).mp hv₀
      simpa using this
    have h1 := hcz _ hv
    calc v₀ * z = g * ((g⁻¹ * v₀ * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * (g⁻¹ * v₀ * g)) * g⁻¹ := by rw [h1]
      _ = z * v₀ := by group
  ·
    have hU' : IsUniqueM (Yp ⊔ P') M := by
      refine isUniqueM_of_map_conj (g := g⁻¹) (M.inv_mem hgM) ?_
      rw [hXe]
      exact hU
    have hle : Yp ⊔ P' ≤ I := sup_le hYpI (hQP ▸ hQI)
    exact hI.2 (le_of_isUniqueM hU' ⟨hle, hI.1.2⟩)

end Hyp153

namespace Hyp15310

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem lemma_15_3_11_one (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) {I : Subgroup G}
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) : IsSylowTwoOf (Sgp153 T V₁) I := by
  rcases h.cases with hY | ⟨-, hY⟩
  · subst hY
    obtain ⟨z, hz, hzo, hzC⟩ := exists_odd_not_mem_of_oTwoUpper
      (h.hyp.Y153_not_le_centralizer h113)
    exact h.hyp.isSylowTwoOf_Sgp153 h11 h.decomp (Y153_le Mc M) ⟨z, hz, hzo, hzC⟩ hI
  · subst hY
    obtain ⟨z, hz, hzo, hzC⟩ := exists_odd_not_mem_of_oTwoUpper
      (h.hyp.Yplus_not_le_centralizer h113 h.decomp)
    exact h.hyp.isSylowTwoOf_Sgp153 h11 h.decomp
      ((oTwoUpper_le _).trans (inf_le_left.trans (Y153_le Mc M))) ⟨z, hz, hzo, hzC⟩ hI

end Hyp15310

end CFSG.Quasithin
