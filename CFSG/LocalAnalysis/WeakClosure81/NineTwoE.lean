module

public import CFSG.LocalAnalysis.WeakClosure81.NineTwoB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V K S X : Subgroup G} {p : ℕ}

theorem Nine2Hyp.ne_bot (h : Nine2Hyp V K S X p) : X ≠ ⊥ := by
  intro hX
  have hlt := h.base.irred.1
  have hle : nineFrattini X ≤ X := Subgroup.map_subtype_le _
  rw [hX] at hlt hle
  exact (ne_of_lt hlt) (le_antisymm hle bot_le)

theorem TwoPTwo.pCore_quot_eq_map (h : TwoPTwo K S X p) :
    CFSG.Open.pCore p (↥K ⧸ CFSG.Open.pCore 2 ↥K) =
      (X.subgroupOf K).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)) := by
  let Q := ↥K
  let R0 : Subgroup Q := CFSG.pCore 2 Q
  let π : Q →* Q ⧸ R0 := QuotientGroup.mk' R0
  let P0 : Subgroup Q := E1.oTwoP Q p
  let X0 : Subgroup Q := X.subgroupOf K
  have hmap : P0.map π = CFSG.pCore p (Q ⧸ R0) := by
    show (E1.oTwoP Q p).map π = _
    rw [E1.oTwoP]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R0) _
  have hP0eq : P0 = X0 ⊔ R0 := by
    have hmapS : P0.map K.subtype = (X0 ⊔ R0).map K.subtype := by
      rw [show P0.map K.subtype = pCoreOf 2 K ⊔ X from map_oTwoP_eq_sup h,
        Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le h.sylowP.le]
      exact sup_comm _ _
    exact Subgroup.map_injective K.subtype_injective hmapS
  have hRbot : R0.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  calc CFSG.pCore p (Q ⧸ R0) = P0.map π := hmap.symm
    _ = (X0 ⊔ R0).map π := by rw [hP0eq]
    _ = X0.map π ⊔ R0.map π := Subgroup.map_sup _ _ _
    _ = X0.map π := by rw [hRbot, sup_bot_eq]

theorem nine_two_card_barO2 (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p)
    {A : Subgroup G} (hA : A ∈ nineOmegaIn V K S) :
    Nat.card (E1.barO2 ↥K (A.subgroupOf K)) = 2 := by
  have hAK : A ≤ K := hA.2.trans h.base.sylowTwo.le
  have hcard : Nat.card (E1.barO2 ↥K (A.subgroupOf K)) =
      (CFSG.pCore 2 ↥K).relIndex (A.subgroupOf K) := by
    rw [show E1.barO2 ↥K (A.subgroupOf K) =
        (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) from rfl,
      ← Subgroup.relIndex_ker (K := A.subgroupOf K)
        (f := QuotientGroup.mk' (CFSG.pCore 2 ↥K)),
      QuotientGroup.ker_mk']
  have hrel : (CFSG.pCore 2 ↥K).relIndex (A.subgroupOf K) = (pCoreOf 2 K).relIndex A := by
    have h : (pCoreOf 2 K).relIndex A =
        (CFSG.pCore 2 ↥K).relIndex (A.subgroupOf K) := by
      conv_lhs => rw [show A = (A.subgroupOf K).map K.subtype
        from (Subgroup.map_subgroupOf_eq_of_le hAK).symm]
      exact Subgroup.relIndex_map_map_of_injective (CFSG.pCore 2 ↥K) (A.subgroupOf K)
        K.subtype_injective
    exact h.symm
  rw [hcard, hrel, nine_two_relIndex hV hm h hA]

theorem nine_two_commutator_eq (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p)
    {A : Subgroup G} (hA : A ∈ nineOmegaIn V K S) :
    ⁅CFSG.Open.pCore p (↥K ⧸ CFSG.Open.pCore 2 ↥K), E1.barO2 ↥K (A.subgroupOf K)⁆ =
      CFSG.Open.pCore p (↥K ⧸ CFSG.Open.pCore 2 ↥K) := by
  have hbase : TwoPTwo K S X p := h.base.toTwoPTwoIrred.toTwoPTwo
  have hAK : A ≤ K := hA.2.trans h.base.sylowTwo.le
  let Q := ↥K
  let R0 : Subgroup Q := CFSG.pCore 2 Q
  let π : Q →* Q ⧸ R0 := QuotientGroup.mk' R0
  let B : Subgroup Q := A.subgroupOf K
  let P : Subgroup (Q ⧸ R0) := CFSG.Open.pCore p (Q ⧸ R0)
  haveI : P.Normal := E1.instNormalPCore p (Q ⧸ R0)
  have hmapP : P = (X.subgroupOf K).map π := TwoPTwo.pCore_quot_eq_map hbase
  refine le_antisymm (Subgroup.commutator_le_left P (E1.barO2 Q B)) ?_
  intro z hzP
  have hzP' : z ∈ (X.subgroupOf K).map π := hmapP ▸ hzP
  obtain ⟨x0, hx0B, hx0eq⟩ := Subgroup.mem_map.mp hzP'
  have hx0X : (x0 : G) ∈ X := Subgroup.mem_subgroupOf.mp hx0B
  obtain ⟨-, -, -, hAnotR⟩ := mem_omegaSet.mp hA.1
  obtain ⟨a, haA, haR⟩ := SetLike.not_le_iff_exists.mp hAnotR
  have haK : a ∈ K := hAK haA
  have ha2 : a * a = 1 := by
    have := (isElemAbelian_of_mem_omegaSet hV.1 hA.1).2 a haA
    simpa [pow_two] using this
  have hBmem : (⟨a, haK⟩ : Q) ∈ B := Subgroup.mem_subgroupOf.mpr haA
  have hāmem : π ⟨a, haK⟩ ∈ E1.barO2 Q B := Subgroup.mem_map_of_mem π hBmem
  haveI : Fact p.Prime := ⟨h.base.prime⟩
  have hodd : Odd (orderOf (π x0)) := by
    obtain ⟨c, hc⟩ := h.base.sylowP.isPGroup.exists_orderOf_eq_pow
      (⟨(x0 : G), hx0X⟩ : ↥X)
    have hx0ord : orderOf (x0 : G) = p ^ c :=
      (Subgroup.orderOf_mk (x0 : G) hx0X).symm.trans hc
    have hodd' : Odd (orderOf (x0 : G)) := by
      rw [hx0ord]
      exact (h.base.prime.odd_of_ne_two h.base.odd).pow
    have hx0eqord : orderOf (x0 : G) = orderOf x0 := (Subgroup.orderOf_mk (x0 : G) x0.2).symm
    rw [hx0eqord] at hodd'
    exact Odd.of_dvd_nat hodd' (orderOf_map_dvd π x0)
  obtain ⟨k, hk⟩ := hodd.exists_bit1
  let y : Q ⧸ R0 := (π x0) ^ (k + 1)
  have hprod_mem : (⟨a, haK⟩ * x0 * ⟨a, haK⟩⁻¹ * x0 : Q) ∈ R0 := by
    have hcoe : ((⟨a, haK⟩ * x0 * ⟨a, haK⟩⁻¹ * x0 : Q) : G)
        = a * (x0 : G) * a⁻¹ * (x0 : G) := rfl
    exact (CFSG.mem_openPCoreOf_iff
      (p := 2) (H := K) (⟨a, haK⟩ * x0 * ⟨a, haK⟩⁻¹ * x0 : Q)).mp (by
        rw [hcoe]
        exact nine_two_inv hV hm h hA haA haR hx0X)
  have hconj : π ⟨a, haK⟩ * π x0 * (π ⟨a, haK⟩)⁻¹ = (π x0)⁻¹ := by
    have h1 : π (⟨a, haK⟩ * x0 * ⟨a, haK⟩⁻¹ * x0) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hprod_mem
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    exact mul_eq_one_iff_eq_inv.mp h1
  have hconj' : MulAut.conj (π ⟨a, haK⟩) (π x0) = (π x0)⁻¹ := by
    rw [MulAut.conj_apply]
    exact hconj
  have hyconj : π ⟨a, haK⟩ * y * (π ⟨a, haK⟩)⁻¹ = y⁻¹ := by
    have h1 : π ⟨a, haK⟩ * y * (π ⟨a, haK⟩)⁻¹ =
        MulAut.conj (π ⟨a, haK⟩) y := (MulAut.conj_apply _ _).symm
    rw [h1, show y = (π x0) ^ (k + 1) from rfl, map_pow, hconj', inv_pow]
  have hy2 : y ^ 2 = π x0 := by
    show ((π x0) ^ (k + 1)) ^ 2 = π x0
    rw [← pow_mul]
    have hk' : (k + 1) * 2 = orderOf (π x0) + 1 := by omega
    rw [hk', pow_succ, pow_orderOf_eq_one, one_mul]
  have hāinv : (π ⟨a, haK⟩)⁻¹ = π ⟨a, haK⟩ := by
    apply inv_eq_of_mul_eq_one_left
    rw [← map_mul]
    have h1 : (⟨a, haK⟩ : Q) * ⟨a, haK⟩ = 1 := by
      ext
      exact ha2
    rw [h1, map_one]
  have hcomm : ⁅y, π ⟨a, haK⟩⁆ = π x0 := by
    have hyinv : π ⟨a, haK⟩ * y⁻¹ * (π ⟨a, haK⟩)⁻¹ = y := by
      have h1 : π ⟨a, haK⟩ * y⁻¹ * (π ⟨a, haK⟩)⁻¹ =
          (π ⟨a, haK⟩ * y * (π ⟨a, haK⟩)⁻¹)⁻¹ := by group
      rw [h1, hyconj, inv_inv]
    rw [commutatorElement_def,
      show y * π ⟨a, haK⟩ * y⁻¹ * (π ⟨a, haK⟩)⁻¹ =
        y * (π ⟨a, haK⟩ * y⁻¹ * (π ⟨a, haK⟩)⁻¹) by group, hyinv, ← pow_two]
    exact hy2
  have hx0P : π x0 ∈ P :=
    le_of_eq hmapP.symm (Subgroup.mem_map_of_mem π hx0B)
  have hyP : y ∈ P := P.pow_mem hx0P (k + 1)
  have hmem : ⁅y, π ⟨a, haK⟩⁆ ∈ ⁅P, E1.barO2 Q B⁆ :=
    Subgroup.commutator_mem_commutator hyP hāmem
  rw [hcomm] at hmem
  exact hx0eq ▸ hmem

theorem nine_two_eOne (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p)
    {A : Subgroup G} (hA : A ∈ nineOmegaIn V K S) : E1.EOne ↥K (A.subgroupOf K) := by
  have hbase : TwoPTwo K S X p := h.base.toTwoPTwoIrred.toTwoPTwo
  refine ⟨p, h.base.prime, h.base.odd, h.base.oTwoPTwo, ?_, ?_, ?_⟩
  · intro hbot
    have hmapP := TwoPTwo.pCore_quot_eq_map hbase
    have hXleR : X.subgroupOf K ≤ CFSG.pCore 2 ↥K := by
      have h1 : (X.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) = ⊥ :=
        hmapP.symm.trans hbot
      rw [Subgroup.map_eq_bot_iff] at h1
      rwa [QuotientGroup.ker_mk'] at h1
    have hXle : X ≤ pCoreOf 2 K := by
      intro x hxX
      have hxK : x ∈ K := h.base.sylowP.le hxX
      have hmem : (⟨x, hxK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
        hXleR (Subgroup.mem_subgroupOf.mpr hxX)
      exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := K) ⟨x, hxK⟩).mpr hmem
    have hbotX : X = ⊥ := by
      rw [← inf_eq_left.mpr hXle]
      exact TwoPTwo.sylowP_inf_pCoreOf hbase
    exact h.ne_bot hbotX
  · exact (nine_two_commutator_eq hV hm h hA).symm
  · exact nine_two_card_barO2 hV hm h hA

theorem nine_two_isE (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p)
    {A : Subgroup G} (hA : A ∈ nineOmegaIn V K S) : E1.IsE 1 K S A K := by
  refine ⟨le_rfl, ?_, ?_, Or.inl ⟨nine_two_eOne hV hm h hA, ?_⟩⟩
  · exact le_inf (E1.tauOf_le K S A) ((E1.tauOf_le K S A).trans h.base.sylowTwo.le)
  · rw [inf_eq_left.mpr h.base.sylowTwo.le]
    exact h.base.sylowTwo
  · rw [nine_two_card_barO2 hV hm h hA]
    norm_num

end CFSG.LocalAnalysis.WeakClosure81
