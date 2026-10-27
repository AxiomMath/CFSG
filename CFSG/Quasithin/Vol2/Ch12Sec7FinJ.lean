module

public import CFSG.Quasithin.Vol2.Ch12Sec7FinH
public import CFSG.Quasithin.Vol2.Ch12Sec7FinI
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Vol2.Ch12Sec7FinC
public import CFSG.Quasithin.Vol2.Ch12Sec7L23e

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits E3
open scoped IsMulCommutative

namespace S127

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_map_conj (a b : G) (X : Subgroup G) :
    (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      X.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

omit [Finite G] in
theorem conjSubgroup_inv_eq_map (X : Subgroup G) (g : G) :
    conjSubgroup X g⁻¹ = X.map (MulAut.conj g).toMonoidHom := by
  rw [conjSubgroup, inv_inv]

omit [Finite G] in
theorem map_conj_centralizer (c : G) (X : Subgroup G) :
    (Subgroup.centralizer (X : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer (X.map (MulAut.conj c).toMonoidHom : Set G) := by
  rw [← conjSubgroup_inv_eq_map, ← conjSubgroup_inv_eq_map, conjSubgroup_centralizer]

omit [Finite G] in
theorem map_conj_le_normalizer (c : G) {X Y : Subgroup G}
    (h : X ≤ Subgroup.normalizer (Y : Set G)) :
    X.map (MulAut.conj c).toMonoidHom ≤
      Subgroup.normalizer (Y.map (MulAut.conj c).toMonoidHom : Set G) := by
  rw [← conjSubgroup_inv_eq_map, ← conjSubgroup_inv_eq_map, ← conjSubgroup_normalizer]
  exact conjSubgroup_mono_left _ h

theorem relIndex_inf_centralizer_conj (c : G) (X Y : Subgroup G) :
    (X.map (MulAut.conj c).toMonoidHom ⊓
        Subgroup.centralizer (Y.map (MulAut.conj c).toMonoidHom : Set G)).relIndex
      (X.map (MulAut.conj c).toMonoidHom) =
      (X ⊓ Subgroup.centralizer (Y : Set G)).relIndex X := by
  rw [← map_conj_centralizer, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective]

omit [Finite G] in
theorem le_normalizer_inf_centralizer_of {X P W : Subgroup G}
    (hP : X ≤ Subgroup.normalizer (P : Set G)) (hW : X ≤ Subgroup.normalizer (W : Set G)) :
    X ≤ Subgroup.normalizer ((P ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
  have key : ∀ x ∈ X, ∀ u ∈ P ⊓ Subgroup.centralizer (W : Set G),
      x * u * x⁻¹ ∈ P ⊓ Subgroup.centralizer (W : Set G) := fun x hx u hu =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hP hx) u).1 (Subgroup.mem_inf.1 hu).1,
      conj_mem_centralizer_V (hW hx) (Subgroup.mem_inf.1 hu).2⟩
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key x hx u, fun hu => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ hu
  rwa [show x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u by group] at this

theorem le_normalizer_cClos (V : Subgroup G) (k : ℕ) (H₁ : Subgroup G) :
    H₁ ≤ Subgroup.normalizer (cClos V k (pCoreOf 2 H₁) : Set G) :=
  le_normalizer_inf_centralizer_of (le_normalizer_pCoreOf 2 H₁)
    ((le_normalizer_pCoreOf 2 H₁).trans (normalizer_le_normalizer_wClos _))

omit [Finite G] in
theorem centralizer_subgroupOf_eq {A H₁ : Subgroup G} (hA : A ≤ H₁) :
    Subgroup.centralizer ((A.subgroupOf H₁ : Subgroup ↥H₁) : Set ↥H₁) =
      (Subgroup.centralizer (A : Set G)).subgroupOf H₁ := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    exact congrArg Subtype.val (h ⟨a, hA ha⟩ (by simpa [Subgroup.mem_subgroupOf] using ha))
  · intro h a ha
    exact Subtype.ext (h a ha)

omit [Finite G] in
theorem isElemAbelian_subgroupOf {A H₁ : Subgroup G} (hA : IsElemAbelian 2 A) :
    IsElemAbelian 2 (A.subgroupOf H₁) := CFSG.Open.IsElemAbelian.subgroupOf hA H₁

theorem false_of_h1Data (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h2 : Lemma12_7_2) (h10 : Lemma12_7_10) (h22 : Lemma12_7_22)
    {T L V : Subgroup G} {t z : G} (hS : Setting1274 G T L V t z) {H : Subgroup G}
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hL1T : L1 T L V ⊔ T = H ⊓ Subgroup.normalizer (L : Set G)) (hr : 3 < rParam V)
    {g : G} {H₁ : Subgroup G} (hH₁H : H₁ ≤ H) (hAT : conjSubgroup V g ≤ T)
    (hAH₁ : conjSubgroup V g ≤ H₁) (hT₁ : IsSylowIn 2 (T ⊓ H₁) H₁)
    (hτ : E1.tauOf H T (conjSubgroup V g) ≤ H₁)
    (hpsl : IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥H₁ ⧸ CFSG.pCore 2 ↥H₁))))
    (hAO : ¬ conjSubgroup V g ≤ pCoreOf 2 H₁) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, hV64, -⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  have hy := hS.hyp.hyp
  have hVe : IsElemAbelian 2 V := ⟨hcomm, fun v hv => sq_eq_one_of_mem hy hv⟩
  set A := conjSubgroup V g with hAdef
  have hAe : IsElemAbelian 2 A := isElemAbelian_conjSubgroup hVe g
  have hS' : IsSylowIn 2 T H :=
    ⟨hHs.1.1, hy.sylow.1, fun h => hy.sylow.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hHs.1.1))⟩
  have hrk : rk ↥V = 6 := by rw [rk, hV64, padicValNat.prime_pow]
  have hrkA : rk ↥A = 6 := by rw [hAdef, rk_conjSubgroup, hrk]
  have hrA : rParam A = rParam V := rParam_conj V g
  have h2r : ((2 : ℕ) : ℕ∞) < rParam V := lt_trans (by norm_num) hr
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥H₁) with hφ
  have hAe' : IsElemAbelian 2 (A.subgroupOf H₁) := isElemAbelian_subgroupOf hAe
  have hE : E1.IsE 2 H T A H₁ :=
    isE_two hH₁H hAT hAH₁ hT₁ hτ hpsl hAO (card_map_le_four hpsl hAe')
  have h5 : 5 ∣ Nat.card ↥(oTwoUpper H₁) := by
    have h60 := Vol2.Ch10.SecB.C11AmS.card_of_isPSL_two_two_two hpsl
    have hmap : oTwoUpper (⊤ : Subgroup (↥H₁ ⧸ CFSG.pCore 2 ↥H₁)) =
        (oTwoUpper (⊤ : Subgroup ↥H₁)).map φ := by
      rw [← oTwoUpper_map, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have hsub : oTwoUpper (⊤ : Subgroup ↥H₁) = (oTwoUpper H₁).subgroupOf H₁ := by
      rw [← Subgroup.subgroupOf_self, A4.oTwoUpper_subgroupOf le_rfl]
    have hdvd := Subgroup.card_map_dvd (oTwoUpper (⊤ : Subgroup ↥H₁)) φ
    rw [← hmap, h60, hsub] at hdvd
    have hc : Nat.card ↥((oTwoUpper H₁).subgroupOf H₁) = Nat.card ↥(oTwoUpper H₁) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (oTwoUpper_le H₁)).toEquiv
    rw [hc] at hdvd
    exact (by norm_num : 5 ∣ 60).trans hdvd
  have hK₁M := not_le_M h1222 h2 hS hL1T ((oTwoUpper_le H₁).trans hH₁H) h5
  have hne : ⁅twoResidual H₁, cClos V 2 T⁆ ≠ ⊥ := by
    intro hc
    apply hK₁M
    rw [← F6.twoResidual_eq_oTwoUpper]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc).trans
      ((h22 G T L V t z hS).2.2.2.1 hr)
  have hA0 : A ∈ gammaSet V 0 T := ⟨hAT, g, le_rfl, mQuot_self _⟩
  obtain ⟨-, hK₁D, hAD⟩ := e3_17_one hVe hS' (i := 0) (j := 2) (k := 2) (by norm_num) h2r
    (by rw [hrk]; norm_num) hA0 hE hne
  set D := cClos V 2 (pCoreOf 2 H₁) with hDdef
  set B := A ⊓ pCoreOf 2 H₁ with hBdef
  have hmB : mQuot A B ≤ 2 := by
    have := e3_17_mQuot hAe hS' hAT le_rfl (by rw [mQuot_self]) hE
    simpa using this
  have hBW : B ≤ wClos V 2 (pCoreOf 2 H₁) := by
    have := e3_17_B_le hAe hS' (i := 0) (j := 2) (k := 2) (by norm_num) (by rw [hrkA]; norm_num)
      hAT le_rfl (by rw [mQuot_self]) hE
    rwa [hAdef, wClos_conjV] at this
  have hDB : D ≤ Subgroup.centralizer (B : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hBW)
  have hDN : D ≤ Subgroup.normalizer (A : Set G) := by
    have := e3_17_cent_le hAe hS' (i := 0) (j := 2) (k := 2) (by norm_num) (by rw [hrA]; exact h2r)
      (by rw [hrkA]; norm_num) hAT le_rfl (by rw [mQuot_self]) hE
    rw [hAdef, wClos_conjV] at this
    exact inf_le_right.trans this
  have hDA : ¬ D ≤ Subgroup.centralizer (A : Set G) := by
    intro h
    apply hAD
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (Subgroup.le_centralizer_iff.1 h)
  have hAV : A.map (MulAut.conj g).toMonoidHom = V := by
    rw [← conjSubgroup_inv_eq_map, hAdef, conjSubgroup_conj_inv]
  have hB'V : B.map (MulAut.conj g).toMonoidHom ≤ V := hAV ▸ Subgroup.map_mono inf_le_left
  have hmB' : mQuot V (B.map (MulAut.conj g).toMonoidHom) ≤ 2 := by
    rw [← hAV, ← conjSubgroup_inv_eq_map, ← conjSubgroup_inv_eq_map, mQuot_conjSubgroup]
    exact hmB
  have hD'N : D.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (V : Set G) :=
    hAV ▸ map_conj_le_normalizer g hDN
  have hD'B : D.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer (B.map (MulAut.conj g).toMonoidHom : Set G) := by
    rw [← map_conj_centralizer]
    exact Subgroup.map_mono hDB
  have hD'V : ¬ D.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    apply hDA
    rw [← hAV, ← map_conj_centralizer] at h
    rwa [Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective] at h
  obtain ⟨l, hl, hBl, hDl⟩ := eq_V2_of_corank_le_two h331 h1222 h2 h10 hS.toSetting1273 hB'V
    hmB' hD'N hD'B hD'V
  rw [map_conj_map_conj] at hBl hDl
  set c := l * g with hc
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := hy.irrPlus.2.2.1 hl
  have hAc : A.map (MulAut.conj c).toMonoidHom = V := by
    rw [hc, ← map_conj_map_conj, hAV, map_conj_of_mem_normalizer hlN]
  obtain ⟨-, -, -, -, ⟨hV2line, -, -, -, -, -⟩, -, -⟩ := h2 G T L V hS.hyp
  have hB16 : Nat.card B = 16 := by
    rw [← hV2line.2, ← hBl, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hA64 : Nat.card A = 64 := by rw [hAdef, card_conjSubgroup, hV64]; norm_num
  have hA4 : Nat.card ↥((A.subgroupOf H₁).map φ) = 4 := by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', ← pCoreOf_subgroupOf,
      Subgroup.relIndex_subgroupOf hAH₁]
    have hmul := Subgroup.relIndex_mul_card (H := pCoreOf 2 H₁) (K := A)
    rw [inf_comm, ← hBdef, hB16, hA64] at hmul
    omega
  have hDH₁ : D ≤ H₁ := inf_le_left.trans (pCoreOf_le 2 H₁)
  have hNDH : H₁ ≤ Subgroup.normalizer (D : Set G) := le_normalizer_cClos V 2 H₁
  have hDn : (D.subgroupOf H₁).Normal :=
    ⟨fun n hn h => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.1 (hNDH h.2) n).1 hn⟩
  have hK' : ¬ oTwoUpper (⊤ : Subgroup ↥H₁) ≤
      Subgroup.centralizer ((D.subgroupOf H₁ : Subgroup ↥H₁) : Set ↥H₁) := by
    intro h
    apply hK₁D
    rw [F6.twoResidual_eq_oTwoUpper, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    have hxH : x ∈ H₁ := oTwoUpper_le H₁ hx
    have hx' : (⟨x, hxH⟩ : ↥H₁) ∈ oTwoUpper (⊤ : Subgroup ↥H₁) := by
      rw [← Subgroup.subgroupOf_self, A4.oTwoUpper_subgroupOf le_rfl, Subgroup.mem_subgroupOf]
      exact hx
    have hc' := h hx'
    rw [centralizer_subgroupOf_eq hDH₁, Subgroup.mem_subgroupOf] at hc'
    exact hc'
  have hc8 := not_relIndex_le_two hpsl hDn hAe' hA4 hK'
  have hinf : D.subgroupOf H₁ ⊓ (Subgroup.centralizer (A : Set G)).subgroupOf H₁ =
      (D ⊓ Subgroup.centralizer (A : Set G)).subgroupOf H₁ := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [centralizer_subgroupOf_eq hAH₁, hinf, Subgroup.relIndex_subgroupOf hDH₁] at hc8
  have h3 : 2 < (D ⊓ Subgroup.centralizer (A : Set G)).relIndex D := by omega
  have hVDc : V ≤ Subgroup.normalizer (D.map (MulAut.conj c).toMonoidHom : Set G) := by
    rw [← hAc]
    exact map_conj_le_normalizer c (hAH₁.trans hNDH)
  have h3c : 2 < (D.map (MulAut.conj c).toMonoidHom ⊓ Subgroup.centralizer (V : Set G)).relIndex
      (D.map (MulAut.conj c).toMonoidHom) := by
    rw [← hAc, relIndex_inf_centralizer_conj]
    exact h3
  obtain ⟨hV2Dc, hidxc⟩ := V2_le_of_le_sup h1222 h2 hS.hyp hDl hVDc h3c
  obtain ⟨k, hkK⟩ := exists_le_map_sup_conj hpsl hAe' hA4
  have hkDc : c * (k : G) * c⁻¹ ∈
      Subgroup.normalizer (D.map (MulAut.conj c).toMonoidHom : Set G) :=
    map_conj_le_normalizer c (le_refl (Subgroup.normalizer (D : Set G))) ⟨k, hNDH k.2, rfl⟩
  have hP := isPGroup_sup_conj h2 h22 h1222 hS hV2Dc hidxc hkDc
  have hone : ∀ X : Subgroup G, X.map (MulAut.conj (1 : G)).toMonoidHom = X := fun X => by
    ext x
    simp
  have hVA : V.map (MulAut.conj c⁻¹).toMonoidHom = A := by
    rw [← hAc, map_conj_map_conj, inv_mul_cancel, hone]
  have hVkA : (V.map (MulAut.conj (c * (k : G) * c⁻¹)).toMonoidHom).map
      (MulAut.conj c⁻¹).toMonoidHom = A.map (MulAut.conj (k : G)).toMonoidHom := by
    rw [map_conj_map_conj, show c⁻¹ * (c * (k : G) * c⁻¹) = (k : G) * c⁻¹ by group,
      ← map_conj_map_conj, hVA]
  have hPA : IsPGroup 2 ↥(A ⊔ A.map (MulAut.conj (k : G)).toMonoidHom) := by
    have := hP.map (MulAut.conj c⁻¹).toMonoidHom
    rwa [Subgroup.map_sup, hVA, hVkA] at this
  set X := A.subgroupOf H₁ ⊔ (A.subgroupOf H₁).map (MulAut.conj k).toMonoidHom with hX
  have hXmap : X.map H₁.subtype = A ⊔ A.map (MulAut.conj (k : G)).toMonoidHom := by
    rw [hX, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAH₁, Subgroup.map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hAH₁ hy⟩, hy, rfl⟩
  have hX2 : IsPGroup 2 ↥X := by
    rw [← hXmap] at hPA
    exact hPA.of_equiv (Subgroup.equivMapOfInjective X H₁.subtype H₁.subtype_injective).symm
  have hK2 : IsPGroup 2 ↥(oTwoUpper (⊤ : Subgroup (↥H₁ ⧸ CFSG.pCore 2 ↥H₁))) :=
    (hX2.map φ).to_le hkK
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hK2
  rw [Vol2.Ch10.SecB.C11AmS.card_of_isPSL_two_two_two hpsl] at hn
  have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 60)
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem false_of_l24 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h2 : Lemma12_7_2) (h10 : Lemma12_7_10) (h11 : Lemma12_7_11) (h22 : Lemma12_7_22)
    {T L V : Subgroup G} {t z : G} (hS : Setting1274 G T L V t z) {H : Subgroup G}
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hpsl : IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))))
    (hL1T : L1 T L V ⊔ T = H ⊓ Subgroup.normalizer (L : Set G)) (hr : 3 < rParam V) : False := by
  obtain ⟨g, hgT, hgO⟩ := exists_conj_not_le h11 hS hHs
  have hT := hS.hyp.hyp.sylow
  have hS' : IsSylowIn 2 (T ⊓ H) H := by
    rw [inf_of_le_left hHs.1.1]
    exact ⟨hHs.1.1, hT.1, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hHs.1.1))⟩
  exact false_of_h1Data h331 h1222 h2 h10 h22 hS hHs hL1T hr le_rfl (hgT.trans inf_le_left)
    ((hgT.trans inf_le_left).trans hHs.1.1) hS' ((E1.tauOf_le H T _).trans hHs.1.1) hpsl hgO

end S127

end CFSG.Quasithin.H13
