module

public import CFSG.Quasithin.EmptyFaithful.S152L27

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem exists_ne_one_mem_inf_of_relIndex [Finite G] {V U A : Subgroup G} (hAV : A ≤ V)
    (hA : 2 < Nat.card A) (hidx : U.relIndex V = 2) :
    ∃ w ∈ U ⊓ A, w ≠ 1 := by
  by_contra hne
  have hbot : U ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    refine Subgroup.mem_bot.2 ?_
    by_contra h1
    exact hne ⟨w, hw, h1⟩
  have h1 : U.relIndex A * Nat.card ↥(U ⊓ A) = Nat.card A := Subgroup.relIndex_mul_card U A
  rw [hbot, Subgroup.card_bot, mul_one] at h1
  have h2 : U.relIndex A ≤ U.relIndex V :=
    Subgroup.relIndex_le_of_le_right hAV (by rw [hidx]; norm_num)
  omega

theorem centralizer_le_centralizer_conjSub [Finite G] {M Mc ZS Z V U : Subgroup G}
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hV₂ : IsElemAbelian 2 V) (hZS : ZS ≤ V)
    (hcard : Nat.card ZS = 4) (hMc : Mc = Subgroup.centralizer (Z : Set G))
    (hU : IsUniqueM (Mc ⊓ Subgroup.centralizer (ZS : Set G)) Mc)
    (hidx : U.relIndex V = 2) {m : G} (hm : m ∈ M) :
    Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer (conjSub m Z : Set G) := by
  have hZS' : conjSub m ZS ≤ V := by
    have := conjSub_mono m hZS
    rwa [F7.conjSub_eq_of_mem_normalizer (hMV hm)] at this
  have hcard' : 2 < Nat.card (conjSub m ZS) := by
    have : Nat.card (conjSub m ZS) = Nat.card ZS :=
      Subgroup.card_map_of_injective (MulAut.conj m).injective
    omega
  obtain ⟨w, hw, hw1⟩ := exists_ne_one_mem_inf_of_relIndex hZS' hcard' hidx
  obtain ⟨hwU, hwZ⟩ := Subgroup.mem_inf.1 hw
  have hzZ : m⁻¹ * w * m ∈ ZS := mem_conjSub.1 hwZ
  have hz1 : m⁻¹ * w * m ≠ 1 := by
    intro h
    apply hw1
    have : w = m * (m⁻¹ * w * m) * m⁻¹ := by group
    rw [this, h]
    group
  have hz2 : (m⁻¹ * w * m) ^ 2 = 1 := hV₂.2 _ (hZS hzZ)
  have hC := centralizer_le_of_isUniqueM_zs hU hzZ hz2 hz1
  intro x hx
  have hxw : w * x = x * w := Subgroup.mem_centralizer_iff.1 hx w hwU
  have hcomm : (m⁻¹ * w * m) * (m⁻¹ * x * m) = (m⁻¹ * x * m) * (m⁻¹ * w * m) := by
    calc (m⁻¹ * w * m) * (m⁻¹ * x * m) = m⁻¹ * (w * x) * m := by group
      _ = m⁻¹ * (x * w) * m := by rw [hxw]
      _ = (m⁻¹ * x * m) * (m⁻¹ * w * m) := by group
  have hxz : m⁻¹ * x * m ∈ Subgroup.centralizer ({m⁻¹ * w * m} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact hcomm
  rw [conjSub_centralizer, mem_conjSub, ← hMc]
  exact hC hxz

theorem centralizer_hyperplane_le [Finite G] {M Mc ZS Z V U : Subgroup G}
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hV₂ : IsElemAbelian 2 V) (hZS : ZS ≤ V)
    (hcard : Nat.card ZS = 4) (hMc : Mc = Subgroup.centralizer (Z : Set G))
    (hU : IsUniqueM (Mc ⊓ Subgroup.centralizer (ZS : Set G)) Mc) (hVZ : V = conjClosure Z M)
    (hidx : U.relIndex V = 2) :
    Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  conv_lhs => rw [hVZ]
  refine conjClosure_le fun h hh z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxC := centralizer_le_centralizer_conjSub hMV hV₂ hZS hcard hMc hU hidx hh hx
  exact (Subgroup.mem_centralizer_iff.1 hxC _ (mul_mem_conjSub hz)).symm

theorem two_le_rParam [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : ∀ U : Subgroup G, U ≤ V → U.relIndex V = 2 →
      Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    (2 : ℕ∞) ≤ E3.rParam V := by
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hnot⟩ := hU
  have hpow := E3.relIndex_eq_two_pow hVp U
  have h2 : 2 ≤ E3.mQuot V U := by
    by_contra hlt
    have hlt' : E3.mQuot V U < 2 := Nat.lt_of_not_le hlt
    interval_cases hq : E3.mQuot V U
    · have hUeq : U = V := (E3.mQuot_eq_zero_iff hVp hUV).1 hq
      subst hUeq
      exact hnot (Subgroup.centralizer_le_normalizer _)
    · exact hnot (h U hUV (by simpa using hpow))
  exact_mod_cast h2

theorem one_lt_sParam {V : Subgroup G} (hV : IsElemAbelian 2 V) (hr : (2 : ℕ∞) ≤ E3.rParam V)
    (hm : 2 ≤ E3.mParam (autI hV ⊤)) : 1 < E3.sParam hV := by
  unfold E3.sParam
  have h2 : (2 : ℕ∞) ≤ min (E3.rParam V) ((E3.mParam (autI hV ⊤) : ℕ) : ℕ∞) :=
    le_min hr (by exact_mod_cast hm)
  have hfin : min (E3.rParam V) ((E3.mParam (autI hV ⊤) : ℕ) : ℕ∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (min_le_right _ _)
  have := ENat.toNat_le_toNat h2 hfin
  simp at this
  omega

end CFSG.Quasithin
