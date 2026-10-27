module

public import CFSG.Quasithin.H13.L32NLem14331f
public import CFSG.Quasithin.Background.F6Cat
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.A5Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14331

theorem map_pCoreOf_subgroupOf' {G : Type*} [Group G] {I X : Subgroup G} (hXI : X ≤ I) :
    (pCoreOf 2 (X.subgroupOf I)).map I.subtype = pCoreOf 2 X := by
  set e : ↥(X.subgroupOf I) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXI
  have h := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
  unfold pCoreOf
  rw [Subgroup.map_map, ← h, Subgroup.map_map]
  rfl

end L14331

namespace L14328

open L14331

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem exists_ctx_of (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h12810 : Lemma12_8_10) (h : Hyp14310One G T L V)
    (hlt : fsuV1 T V < centerOf (fsuU T V)) {V₂ : Subgroup G} {g : G}
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgN : g ∉ l32nH T V) :
    ∃ _ : IsMulCommutative ↥V, ∃ (z b l : G), Ctx G T L V V₂ g z b l := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have hs := h.setting1282One h13322 hV hV₂
  obtain ⟨hc, S⟩ := L14332.exists_setting h1332 h1334 h1222 h hV₂
  obtain ⟨z, -, b, hz, hz1, -, -, hbV, hbV₂⟩ := S.exists_basis
  obtain ⟨haV₂, ha1⟩ := conj_z_mem S hV₂ hgP hgN hz hz1
  have hzV₂ : z ∈ V₂ := hV₂.2 hz
  have hzV : z ∈ V := hV₂.1.1 hzV₂
  have haV : g⁻¹ * z * g ∈ V := hV₂.1.1 haV₂
  obtain ⟨l, hlL, hl3, hla, hlz, hlb⟩ := S.exists_rot haV hzV hbV hz1
    (fun h1 => hbV₂ (h1 ▸ one_mem _)) (fun h1 => ha1 (h1 ▸ hz)) (fun h1 => hbV₂ (h1 ▸ haV₂))
    (fun h1 => hbV₂ (h1 ▸ hzV₂)) (fun h1 => hbV₂ (h1 ▸ V₂.mul_mem haV₂ hzV₂))
  obtain ⟨hUT, hTU⟩ := (hs.almostSpecial h1222 h12213).G22_three
  exact ⟨hc, z, b, l, ⟨h, hlt, hV₂, hs, hgP, hgN, S, hz, hz1, hbV, hbV₂, hlL, hl3, hla,
    hlz, hlb, hUT, hTU, (h12810 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN).2.1.symm,
    L128P.i128_eq_sup h1222 h12213 hs⟩⟩

variable {V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx

variable {g z b l : G} (C : Ctx G T L V V₂ g z b l) (D : HatModelU (fsuU T V)) {e : G}
include C

theorem pow_two_pow_of_mem_P_inf_H (h1222 : Stmt12_2_2) {x : G} (hxP : x ∈ p128 T L V)
    (hxH : x ∈ l32nH T V) : ∃ n : ℕ, x ^ 2 ^ n = 1 := by
  have hzz := C.mul_self_V C.z_V
  have hfix : ∀ {y : G}, y ∈ l32nH T V → y * z * y⁻¹ = z := by
    intro y hy
    have h1 := (Subgroup.mem_normalizer_iff.mp hy z).mp C.z_mem
    rcases C.S.eq_of_mem_V1 C.z_mem C.z_ne h1 with h2 | h2
    · exfalso
      apply C.z_ne
      calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
        _ = 1 := by rw [h2]; group
    · exact h2
  have hxz := hfix hxH
  have hxV₂ : x ∈ Subgroup.normalizer (V₂ : Set G) :=
    L128P.p128_le_normalizer le_rfl C.plane.1 hxP
  have hxa1 : x * (g⁻¹ * z * g) * x⁻¹ ∈ V₂ :=
    (Subgroup.mem_normalizer_iff.mp hxV₂ _).mp C.a_mem
  have hxa : x * (g⁻¹ * z * g) * x⁻¹ = g⁻¹ * z * g ∨
      x * (g⁻¹ * z * g) * x⁻¹ = z * (g⁻¹ * z * g) := by
    have hne1 : x * (g⁻¹ * z * g) * x⁻¹ ≠ 1 := by
      intro h1
      apply C.a_nmem
      rw [show g⁻¹ * z * g = x⁻¹ * (x * (g⁻¹ * z * g) * x⁻¹) * x by group, h1,
        show x⁻¹ * 1 * x = 1 by group]
      exact one_mem _
    rcases C.V2_cases hxa1 hne1 with h | h | h
    · exfalso
      apply C.a_nmem
      have : g⁻¹ * z * g = z := by
        calc g⁻¹ * z * g = x⁻¹ * (x * (g⁻¹ * z * g) * x⁻¹) * x := by group
          _ = x⁻¹ * z * x := by rw [h]
          _ = x⁻¹ * (x * z * x⁻¹) * x := by rw [hxz]
          _ = z := by group
      rw [this]
      exact C.z_mem
    · exact Or.inl h
    · exact Or.inr h
  have hx2a : (x * x) * (g⁻¹ * z * g) * (x * x)⁻¹ = g⁻¹ * z * g := by
    rcases hxa with h | h
    · rw [show (x * x) * (g⁻¹ * z * g) * (x * x)⁻¹ = x * (x * (g⁻¹ * z * g) * x⁻¹) * x⁻¹ by
        group, h, h]
    · rw [show (x * x) * (g⁻¹ * z * g) * (x * x)⁻¹ = x * (x * (g⁻¹ * z * g) * x⁻¹) * x⁻¹ by
        group, h, show x * (z * (g⁻¹ * z * g)) * x⁻¹ =
          (x * z * x⁻¹) * (x * (g⁻¹ * z * g) * x⁻¹) by group, hxz, h, ← mul_assoc, hzz,
        one_mul]
  have hx2z : (x * x) * z * (x * x)⁻¹ = z := by
    rw [show (x * x) * z * (x * x)⁻¹ = x * (x * z * x⁻¹) * x⁻¹ by group, hxz, hxz]
  have hx2C : x * x ∈ Subgroup.centralizer (V₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have key : (x * x) * v * (x * x)⁻¹ = v := by
      by_cases hv1 : v = 1
      · rw [hv1]; group
      rcases C.V2_cases hv hv1 with rfl | rfl | rfl
      · exact hx2z
      · exact hx2a
      · rw [show (x * x) * (z * (g⁻¹ * z * g)) * (x * x)⁻¹ =
          ((x * x) * z * (x * x)⁻¹) * ((x * x) * (g⁻¹ * z * g) * (x * x)⁻¹) by group,
          hx2z, hx2a]
    calc v * (x * x) = (x * x) * v * (x * x)⁻¹ * (x * x) := by rw [key]
      _ = (x * x) * v := by group
  obtain ⟨k, hk⟩ := L128P.isPGroup_centralizer_p128 h1222 C.setting.hyp C.setting.v1
    C.setting.le ⟨x * x, (p128 T L V).mul_mem hxP hxP, hx2C⟩
  refine ⟨k + 1, ?_⟩
  have hk' : (x * x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  calc x ^ 2 ^ (k + 1) = (x ^ 2) ^ 2 ^ k := by
        rw [← pow_mul]
        congr 1
        ring
    _ = 1 := by rw [sq]; exact hk'

theorem caseI_inf_P (X : CaseI T L V g D e) :
    (kA T V (l⁻¹ * e * l) ⊔ T) ⊓ p128 T L V = T := by
  have hKTH : kA T V (l⁻¹ * e * l) ⊔ T ≤ l32nH T V := sup_le (C.caseI_K_H D X) C.setting.v1.2.2
  have hT := C.S.hH.sylow
  have h2 : IsPGroup 2 ↥((kA T V (l⁻¹ * e * l) ⊔ T) ⊓ p128 T L V) := by
    intro x
    obtain ⟨n, hn⟩ := C.pow_two_pow_of_mem_P_inf_H X.h1222 x.2.2 (hKTH x.2.1)
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hle : T ≤ (kA T V (l⁻¹ * e * l) ⊔ T) ⊓ p128 T L V := le_inf le_sup_right L128P.le_p128
  have := (hT.1.toSylow hT.2).is_maximal' h2 (by rw [IsPGroup.toSylow_coe]; exact hle)
  rw [this, IsPGroup.toSylow_coe]

theorem quotient_P (h1222 : Stmt12_2_2) :
    Nonempty (↥(p128 T L V) ⧸ CFSG.Open.pCore 2 ↥(p128 T L V) ≃* Equiv.Perm (Fin 3)) := by
  have h := L128P.nonempty_mulEquiv_perm_three h1222 C.setting.hyp C.setting.v1 C.setting.v2
    C.setting.le
  rw [L128P.oTwoUpper_sup_eq C.setting.hyp] at h
  exact h

theorem caseI_triple (X : CaseI T L V g D e) :
    F6.IsGoldschmidtTripleIn ((kA T V (l⁻¹ * e * l) ⊔ T) ⊔ p128 T L V)
      (kA T V (l⁻¹ * e * l) ⊔ T) (p128 T L V) := by
  refine ⟨rfl, C.caseI_quotient_KT D X, C.quotient_P X.h1222, ?_⟩
  rw [C.caseI_inf_P D X]
  exact A5.isSylowTwoOf_of_le C.S.hH.sylow (le_sup_right.trans le_sup_left)

theorem caseI_le_centralizer (X : CaseI T L V g D e) :
    (kA T V (l⁻¹ * e * l) ⊔ T) ⊔ p128 T L V ≤ Subgroup.centralizer ({e} : Set G) := by
  have heZ : e ∈ centerOf (fsuU T V) := by
    have := X.he
    rw [C.zI] at this
    exact this.1
  have h2 : Nat.card ↥(centerOf (i128 T L V (fsuV1 T V))) = 2 := by
    have hle := C.card_zI_le X.h14325 X.h1222 X.h12213 X.h12810 X.h12813
    have hpos : 1 < Nat.card ↥(centerOf (i128 T L V (fsuV1 T V))) := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact ⟨⟨⟨e, X.he⟩, 1, fun h => X.he1 (congrArg Subtype.val h)⟩⟩
    omega
  have hP : p128 T L V ≤ Subgroup.centralizer ({e} : Set G) := by
    intro p hp
    have hpN : p ∈ Subgroup.normalizer (centerOf (i128 T L V (fsuV1 T V)) : Set G) :=
      L14332.normalizer_le_normalizer_centerOf _ (le_normalizer_conjClosure _ _ hp)
    have hpe : p * e * p⁻¹ ∈ centerOf (i128 T L V (fsuV1 T V)) :=
      (Subgroup.mem_normalizer_iff.mp hpN e).mp X.he
    have hne : p * e * p⁻¹ ≠ 1 := by
      intro h1
      apply X.he1
      calc e = p⁻¹ * (p * e * p⁻¹) * p := by group
        _ = 1 := by rw [h1]; group
    rcases eq_one_or_eq_of_card_two h2 X.he X.he1 hpe with h | h
    · exact absurd h hne
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc p * e = p * e * p⁻¹ * p := by group
        _ = e * p := by rw [h]
  refine sup_le (sup_le ?_ (L128P.le_p128.trans hP)) hP
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (C.caseI_K_Z D X hk) e heZ).symm

theorem caseI_pCoreOf_ne_bot (X : CaseI T L V g D e) :
    pCoreOf 2 ((kA T V (l⁻¹ * e * l) ⊔ T) ⊔ p128 T L V) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := (kA T V (l⁻¹ * e * l) ⊔ T) ⊔ p128 T L V with hI
  have heZ : e ∈ centerOf (fsuU T V) := by
    have := X.he
    rw [C.zI] at this
    exact this.1
  have heI : e ∈ I :=
    ((le_sup_right : T ≤ kA T V (l⁻¹ * e * l) ⊔ T).trans le_sup_left) (C.U_T heZ.1)
  have hcen := C.caseI_le_centralizer D X
  have hle : Subgroup.zpowers e ≤ pCoreOf 2 I := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.zpowers_le.mpr heI) (fun x hx => ?_) ?_
    · rw [Subgroup.mem_normalizer_iff]
      have hc : Commute x e := Subgroup.mem_centralizer_singleton_iff.mp (hcen hx)
      have hxe : ∀ k : ℤ, x * e ^ k * x⁻¹ = e ^ k := fun k => by
        rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      intro y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, (hxe k).symm⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, (mul_left_cancel (mul_right_cancel (hk.symm.trans (hxe k).symm))).symm⟩
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact X.he2) X.he1]
      norm_num
  intro h
  apply X.he1
  have := hle (Subgroup.mem_zpowers e)
  rw [h, Subgroup.mem_bot] at this
  exact this

theorem caseI_f618 (hF618 : F6.TheoremF618Cat) (X : CaseI T L V g D e) :
    IsGoldschmidtAmalgam
        (((kA T V (l⁻¹ * e * l) ⊔ T).subgroupOf ((kA T V (l⁻¹ * e * l) ⊔ T) ⊔ p128 T L V)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥((kA T V (l⁻¹ * e * l) ⊔ T) ⊔ p128 T L V))))
        (((p128 T L V).subgroupOf ((kA T V (l⁻¹ * e * l) ⊔ T) ⊔ p128 T L V)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥((kA T V (l⁻¹ * e * l) ⊔ T) ⊔ p128 T L V)))) ∧
      F6.F618ConclusionCat
        (((kA T V (l⁻¹ * e * l) ⊔ T).subgroupOf ((kA T V (l⁻¹ * e * l) ⊔ T) ⊔ p128 T L V)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥((kA T V (l⁻¹ * e * l) ⊔ T) ⊔ p128 T L V))))
        (((p128 T L V).subgroupOf ((kA T V (l⁻¹ * e * l) ⊔ T) ⊔ p128 T L V)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥((kA T V (l⁻¹ * e * l) ⊔ T) ⊔ p128 T L V)))) := by
  set K := kA T V (l⁻¹ * e * l) with hK
  set I := (K ⊔ T) ⊔ p128 T L V with hI
  have htriple := C.caseI_triple D X
  rcases htriple.goldschmidt_mod_pPrimeCore with ⟨-, hAm, -⟩ | ⟨h1, h2, -, -, -⟩
  · have := C.hyp.fsu.simple
    have hSQ : CFSG.SectionRank.IsSQTKCat ↥I :=
      (qtkeCore_of_cat C.hyp.fsu.nonabelian C.hyp.fsu.qtke).1 _ (C.caseI_pCoreOf_ne_bot D X)
    exact ⟨hAm, hF618 _ _ _ hAm.toIsGoldschmidtTriple
      ⟨↥I, inferInstance, inferInstance, hSQ, ⟨MulEquiv.refl _⟩⟩⟩
  ·
    exfalso
    have hKTI : K ⊔ T ≤ I := le_sup_left
    have hPI : p128 T L V ≤ I := le_sup_right
    have heq : pCoreOf 2 (K ⊔ T) = pCoreOf 2 (p128 T L V) := by
      have e1 := map_pCoreOf_subgroupOf' hKTI
      have e2 := map_pCoreOf_subgroupOf' hPI
      rw [← e1, ← e2, h1, h2]
    have hKTH : K ⊔ T ≤ l32nH T V := sup_le (C.caseI_K_H D X) C.setting.v1.2.2
    have hU : fsuU T V ≤ pCoreOf 2 (K ⊔ T) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (C.U_T.trans le_sup_right)
        (hKTH.trans (le_normalizer_conjClosure _ _)) (C.S.hH.sylow.1.to_le C.U_T)
    rw [heq, ← L128P.oTwoUpper_sup_eq C.setting.hyp] at hU
    have hUC := hU.trans (L128P.pCoreOf_le_centralizer X.h1222 C.setting.hyp C.setting.v1
      C.setting.v2 C.setting.le)
    obtain ⟨ua, -, hua, -, -⟩ := C.exists_dual_ab D X.h1222 X.h12213
    obtain ⟨u, hu, rfl⟩ := D.π_surj ua
    have hcomm : u * (g⁻¹ * z * g) * u⁻¹ * (g⁻¹ * z * g)⁻¹ = 1 := by
      rw [← Subgroup.mem_centralizer_iff.mp (hUC hu) _ C.a_mem]
      group
    have h0 := (D.B_spec u hu _ (V_le_U C.a_V)).mpr hcomm
    rw [h0] at hua
    exact zero_ne_one hua

end Ctx

end L14328

end CFSG.Quasithin.H13
