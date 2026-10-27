module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem14Syl
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem14Irr

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isO2Trivial_of_isTwoReducedIn_tildeOf {V₁ H X : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (V₁ : Set G)) (hX : X ≤ Subgroup.normalizer (V₁ : Set G))
    (hred : IsTwoReducedIn (tildeOf V₁ H) (tildeOf V₁ X)) :
    IsO2Trivial H (centralizerMod V₁ H X) := by
  intro P hPH hPN hP2
  have hcomm : ∀ (x u : Subgroup.normalizer (V₁ : Set G)),
      (x : G) * u * (x : G)⁻¹ * (u : G)⁻¹ ∈ V₁ → tmk V₁ u * tmk V₁ x = tmk V₁ x * tmk V₁ u := by
    intro x u hxu
    have h1 : tmk V₁ (x * u * x⁻¹ * u⁻¹) = 1 := secMk_eq_one_iff.mpr hxu
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc tmk V₁ u * tmk V₁ x =
        (tmk V₁ x * tmk V₁ u * (tmk V₁ x)⁻¹ * (tmk V₁ u)⁻¹)⁻¹ * (tmk V₁ x * tmk V₁ u) := by group
      _ = tmk V₁ x * tmk V₁ u := by rw [h1, inv_one, one_mul]
  have h1 := hred.2.2.2 (tildeOf V₁ P) (secImg_mono hPH) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hy
      exact secMk_mem_normalizer_secImg (hPN hx)) (by
      intro d hd
      obtain ⟨p, hp, rfl⟩ := mem_secImg.1 hd
      obtain ⟨k, hk⟩ := hP2 p hp
      have hk' : ((p ^ 2 ^ k : Subgroup.normalizer (V₁ : Set G)) : G) ∈ centralizerMod V₁ H X := by
        simpa using hk
      refine ⟨k, ?_⟩
      rw [← map_pow]
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      obtain ⟨u, hu, rfl⟩ := mem_secImg.1 hy
      exact hcomm (p ^ 2 ^ k) u ((mem_centralizerMod.mp hk').2.2 u hu))
  intro p hp
  have hpN : p ∈ Subgroup.normalizer (V₁ : Set G) := hH (hPH hp)
  refine mem_centralizerMod.mpr ⟨hPH hp, hpN, fun u hu => ?_⟩
  have h2 := Subgroup.mem_centralizer_iff.mp
    (h1 (secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (x := ⟨p, hpN⟩) hp))
    (tmk V₁ ⟨u, hX hu⟩) (secMk_mem_secImg hu)
  exact commutator_mem_of_secMk_commute h2.symm

namespace Hyp611Nat

variable {T M L V : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem lOne_eq_oTwoUpper (L U : Subgroup G) : lOne L U = oTwoUpper (lOne L U) :=
  le_antisymm ((Subgroup.closure_le _).mpr fun _ hx =>
    mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2) (oTwoUpper_le _)

omit [Finite G] in
theorem lOne_lOne (L U : Subgroup G) : lOne (lOne L U) U = lOne L U := by
  have hle : lOne L U ≤ Subgroup.normalizer (U : Set G) := (oTwoUpper_le _).trans inf_le_right
  have h1 : lOne L U ⊓ Subgroup.normalizer (U : Set G) = lOne L U := inf_eq_left.mpr hle
  show oTwoUpper (lOne L U ⊓ Subgroup.normalizer (U : Set G)) = lOne L U
  rw [h1]
  exact (lOne_eq_oTwoUpper L U).symm

theorem almostSpecialHyp_fix (h432 : Stmt4_3_2) (h : Hyp611Nat G T M L V n) {t : G}
    (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
      (M ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G))) :
    AlmostSpecialHyp V (V ⊓ Subgroup.centralizer ({t} : Set G))
      (lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)))
      (T ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G))
      (Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G)) := by
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  have hlOne : lOne L U ≤ L ⊓ Subgroup.normalizer (U : Set G) := oTwoUpper_le _
  have hV := h.toHyp611.isElemAbelian
  have hVU : V ≤ Subgroup.centralizer (U : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun u hu => B2F.isElemAbelian_comm hV hu.1 hv
  have h1 := h.lemma_6_1_14_one h432 htT ht hSyl
  have hUcard : Nat.card U = 2 ^ n := h.card_fix_of_fieldAut htT ht
  exact
    { elemAbelian := hV
      ne_bot := by
        intro h0
        rw [h0, Subgroup.card_bot] at hUcard
        have : 1 < 2 ^ n := Nat.one_lt_two_pow (by have := h.two_le; omega)
        omega
      le_V := inf_le_left
      oTwo_eq := lOne_eq_oTwoUpper L U
      V_le_T := le_inf h.toHyp611.le_T (hVU.trans (Subgroup.centralizer_le_normalizer _))
      T_le_normV₁ := inf_le_right
      T_le_normV := inf_le_left.trans h.toHyp611.T_le_normalizer
      T_le_normL := by
        intro x hx
        refine normalizer_le_normalizer_oTwoUpper _ ?_
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨h.T_le_normalizer_L hx.1, Subgroup.le_normalizer hx.2⟩
      sylow_LT := E6.isSylowIn_of_le hSyl le_sup_right
        (sup_le (hlOne.trans (inf_le_inf_right _ h.L_le)) (inf_le_inf_right _ h.T_le))
      H_le := le_rfl
      lOne_sup_le := sup_le ((oTwoUpper_le _).trans inf_le_right) inf_le_right
      sylow_H := h1.2.2
      charTwo := (h.lemma_6_1_14_two htT).1
      irred := by
        rw [lOne_lOne]
        exact h.irred_fix htT ht }

theorem conjClosure_le_pCoreOf_centralizer (h432 : Stmt4_3_2) (h : Hyp611Nat G T M L V n)
    {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
      (M ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G))) :
    conjClosure V (Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G)) ≤
      pCoreOf 2 (Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set H := Subgroup.normalizer (U : Set G) with hH
  have hA := h.almostSpecialHyp_fix h432 htT ht hSyl
  have hV := h.toHyp611.isElemAbelian
  have hVUQ : conjClosure V H ≤ pCoreOf 2 H := by
    intro x hx
    have hcc := hA.conjClosure_le_N
    have hQ := omegaOneCenterOf_le _ ((secImg_le_iff.1 hA.G22_one.2) ⟨x, hcc hx⟩ hx)
    exact (secMk_mem_secImg_iff hA.V₁_le_pCoreOf).1 hQ
  have hVUC : conjClosure V H ≤ Subgroup.centralizer (U : Set G) := by
    refine conjClosure_le fun g hg v hv => ?_
    have hvC : v ∈ Subgroup.centralizer (U : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun u hu => B2F.isElemAbelian_comm hV hu.1 hv
    exact (Subgroup.mem_normalizer_iff.mp (F7.normalizer_le_normalizer_centralizer _ hg) v).mp hvC
  have hX : pCoreOf 2 H ⊓ Subgroup.centralizer (U : Set G) ≤
      pCoreOf 2 (Subgroup.centralizer (U : Set G)) := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
    intro c hc
    have hcN : c ∈ H := Subgroup.centralizer_le_normalizer _ hc
    have h1 := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hcN)
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hc)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨a, b⟩ => ⟨(h1 x).mp a, (h2 x).mp b⟩, fun ⟨a, b⟩ => ⟨(h1 x).mpr a, (h2 x).mpr b⟩⟩
  exact fun x hx => hX ⟨hVUQ hx, hVUC hx⟩

theorem lemma_6_1_14_four (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (h : Hyp611Nat G T M L V n)
    {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
      (M ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G))) :
    IsElemAbelian 2 (conjClosure V (Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))) ∧
      IsReducedMod (Subgroup.normalizer
          ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
        (conjClosure V (Subgroup.normalizer
          ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G)))
        (V ⊓ Subgroup.centralizer ({t} : Set G)) ∧
      ⁅pCoreOf 2 (Subgroup.normalizer
          ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G)),
        conjClosure V (Subgroup.normalizer
          ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))⁆ ≤
        V ⊓ Subgroup.centralizer ({t} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set H := Subgroup.normalizer (U : Set G) with hH
  set R := ch6Q T V ⊔ Subgroup.zpowers t with hR
  have hA := h.almostSpecialHyp_fix h432 htT ht hSyl
  have hV := h.toHyp611.isElemAbelian
  have hcc := hA.conjClosure_le_N
  have hcomm : ∀ x ∈ conjClosure V H, ∀ q ∈ pCoreOf 2 H, x * q * x⁻¹ * q⁻¹ ∈ U := by
    intro x hx q hq
    have hqN : q ∈ Subgroup.normalizer (U : Set G) := pCoreOf_le 2 H hq
    have hmemY := (secImg_le_iff.1 hA.G22_one.2) ⟨x, hcc hx⟩ hx
    have hqQ : tmk U ⟨q, hqN⟩ ∈ tildeOf U (pCoreOf 2 H) := secMk_mem_secImg hq
    have hxy : tmk U ⟨x, hcc hx⟩ * tmk U ⟨q, hqN⟩ = tmk U ⟨q, hqN⟩ * tmk U ⟨x, hcc hx⟩ :=
      (mem_centralizer_of_mem_omegaOneCenterOf hmemY hqQ).symm
    exact commutator_mem_of_secMk_commute hxy
  have h1 := h.lemma_6_1_14_one h432 htT ht hSyl
  have hVUR : conjClosure V H ≤ R :=
    (h.conjClosure_le_pCoreOf_centralizer h432 htT ht hSyl).trans
      (pCoreOf_two_le_of_isSylowTwoOf h1.1)
  have hW0 := (h.lemma_6_1_14_three h6110 htT ht).1
  have hf : ∀ g ∈ H, ∀ v ∈ V, g * v * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg v hv
    have hle : conjSubgroup V g⁻¹ ≤ R := by
      intro x hx
      apply hVUR
      have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ V := mem_conjSubgroup_iff.mp hx
      have e : x = g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ := by group
      rw [e]
      exact mem_conjClosure hg hx'
    have hmem : conjSubgroup V g⁻¹ ∈ gammaSet V 0 R :=
      ⟨hle, g⁻¹, le_rfl, mQuot_self _⟩
    have hgv : g * v * g⁻¹ ∈ conjSubgroup V g⁻¹ := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hv
    exact (hW0 (le_wClos hmem hgv)).2
  have hpair : ∀ x ∈ {x | ∃ h' ∈ H, ∃ z ∈ V, h' * z * h'⁻¹ = x},
      ∀ y ∈ {x | ∃ h' ∈ H, ∃ z ∈ V, h' * z * h'⁻¹ = x}, x * y = y * x := by
    rintro _ ⟨g, hg, v, hv, rfl⟩ _ ⟨g', hg', v', hv', rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp (hf (g'⁻¹ * g) (H.mul_mem (H.inv_mem hg') hg) v hv)
      v' hv'
    calc (g * v * g⁻¹) * (g' * v' * g'⁻¹) =
        g' * (((g'⁻¹ * g) * v * (g'⁻¹ * g)⁻¹) * v') * g'⁻¹ := by group
      _ = g' * (v' * ((g'⁻¹ * g) * v * (g'⁻¹ * g)⁻¹)) * g'⁻¹ := by rw [hc]
      _ = (g' * v' * g'⁻¹) * (g * v * g⁻¹) := by group
  have hsq : ∀ x ∈ {x | ∃ h' ∈ H, ∃ z ∈ V, h' * z * h'⁻¹ = x}, x ^ 2 = 1 := by
    rintro _ ⟨g, -, v, hv, rfl⟩
    rw [conj_pow, hV.2 v hv, mul_one, mul_inv_cancel]
  have hEA : IsElemAbelian 2 (conjClosure V H) := F7.isElemAbelian_closure _ hpair hsq
  have hcommVU : ∀ x ∈ conjClosure V H, ∀ y ∈ conjClosure V H, x * y = y * x :=
    fun x hx y hy => B2F.isElemAbelian_comm hEA hx hy
  refine ⟨hEA, ⟨(inf_le_left : U ≤ V).trans (le_conjClosure V H), hcc,
    le_normalizer_conjClosure V H, le_rfl, fun u hu v hv => ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [hcommVU u hu v hv, mul_inv_cancel_right, mul_inv_cancel]
    exact U.one_mem
  · rw [hEA.2 u hu]
    exact U.one_mem
  · exact isO2Trivial_of_isTwoReducedIn_tildeOf le_rfl hcc hA.G22_four
  · rw [Subgroup.commutator_le]
    intro q hq x hx
    have := U.inv_mem (hcomm x hx q hq)
    have e : (x * q * x⁻¹ * q⁻¹)⁻¹ = ⁅q, x⁆ := by
      rw [commutatorElement_def]
      group
    rwa [e] at this

end Hyp611Nat

end CFSG.Quasithin.H13
