module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3Lift
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3SzT
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Sp
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Sz
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BBar
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

section Torus

variable {Γ : Type} [Group Γ] [Finite Γ]

open CFSG.LieType.Ree in
theorem uc22r899c3_not_dvd_normalizer_Sz {K S : Subgroup Γ}
    {n : ℕ} (hK : IsSz K n) {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ (2 * n) + 1) (hq : q.Prime) (hq2 : q ≠ 2) (hqn : q ∣ 2 ^ n - 1)
    (hS : IsSylowOf q S K) : ∀ y ∈ K, y ∈ normalizer (S : Set Γ) → orderOf y ≠ p := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q, rfl⟩ := hS
  intro y hyK hyN hord
  have hmem : ∀ s : K, s ∈ (Q : Subgroup K) ↔ (s : Γ) ∈ (Q : Subgroup K).map K.subtype :=
    fun s => (Subgroup.mem_map_iff_mem K.subtype_injective).symm
  have hyQ : (⟨y, hyK⟩ : K) ∈ normalizer ((Q : Subgroup K) : Set K) := by
    refine Subgroup.mem_normalizer_iff.2 fun s => ?_
    rw [hmem s, hmem (⟨y, hyK⟩ * s * ⟨y, hyK⟩⁻¹)]
    exact Subgroup.mem_normalizer_iff.1 hyN s
  obtain ⟨a, F, hFf, hFfin, e, ha, rfl, hF, hST, hC⟩ :=
    uc22r899c3_suzuki_torus_frame hK hq2 hqn Q
  have hyS : e ⟨y, hyK⟩ ∈ normalizer
      ((Subgroup.map e.toMonoidHom (Q : Subgroup K) : Subgroup _) : Set _) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hyQ
  have hyT := uc22r8100b_normalizer_le hST (suzuki_borel_structure hF).2.1 hC hyS
  have hyo : orderOf (e ⟨y, hyK⟩) = p :=
    (MulEquiv.orderOf_eq e _).trans ((Subgroup.orderOf_coe (⟨y, hyK⟩ : K)).symm.trans hord)
  have hp2' : p ∣ 2 → False := fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  rcases uc22r899c3_suzuki_normalizer_torus ha hF
    (fun t ht => (Subgroup.mem_normalizer_iff.1 hyT t).1 ht) with hT | hT
  ·
    have h1 : p ∣ 2 ^ (2 * a + 1) - 1 := by
      rw [← hyo, ← (suzuki_borel_structure hF).2.2.1]
      exact Subgroup.orderOf_dvd_natCard _ hT
    have h2 := Nat.dvd_sub hpn (h1.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left _ 2)))
    have h3 : 2 ^ (2 * (2 * a + 1)) + 1 - (2 ^ (2 * (2 * a + 1)) - 1) = 2 := by
      have := Nat.one_le_two_pow (n := 2 * (2 * a + 1))
      omega
    exact hp2' (h3 ▸ h2)
  ·
    obtain ⟨μ, hμ⟩ := mem_suzukiT_iff.1 hT
    have h1 : e ⟨y, hyK⟩ = suzukiDElt a F μ * suzukiWElt a F := by
      rw [hμ, mul_assoc, suzukiWElt_mul_self, mul_one]
    have h2 : e ⟨y, hyK⟩ ^ 2 = 1 := by
      rw [h1, sq, mul_assoc, ← mul_assoc (suzukiWElt a F), suzukiWElt_D_W hF, suzukiDElt_mul,
        mul_inv_cancel, suzukiDElt_one]
    exact hp2' (by rw [← hyo]; exact orderOf_dvd_of_pow_eq_one h2)

theorem uc22r899c3_centralizes_Sz {n m p q : ℕ}
    {K S : Subgroup Γ} (hK : IsSz K n) (hn : n = p * m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqm : q ∣ 2 ^ m - 1) (hS : IsSylowOf q S K) {d : Γ}
    (hdK : d ∈ normalizer (K : Set Γ)) (hdS : d ∈ normalizer (S : Set Γ)) (hdp : d ^ p = 1)
    {t : Γ} (htS : t ∈ S) (hto : orderOf t = q) : d * t = t * d := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q, rfl⟩ := hS
  have htK : t ∈ K := Subgroup.map_subtype_le _ htS
  have hmem : ∀ y : K, y ∈ (Q : Subgroup K) ↔ (y : Γ) ∈ (Q : Subgroup K).map K.subtype :=
    fun y => (Subgroup.mem_map_iff_mem K.subtype_injective).symm
  set ψ : MulAut K := K.normalizerMonoidHom ⟨d, hdK⟩ with hψ
  have hψapp : ∀ x : K, ((ψ x : K) : Γ) = d * x * d⁻¹ := fun x => rfl
  have hψQ : ∀ x : K, x ∈ (Q : Subgroup K) ↔ ψ x ∈ (Q : Subgroup K) := by
    intro x
    rw [hmem, hmem, hψapp]
    exact Subgroup.mem_normalizer_iff.1 hdS x
  have hψp : ψ ^ p = 1 := by
    rw [hψ, ← map_pow]
    have : (⟨d, hdK⟩ : normalizer (K : Set Γ)) ^ p = 1 := Subtype.ext hdp
    rw [this, map_one]
  have htQ : (⟨t, htK⟩ : K) ∈ (Q : Subgroup K) := (hmem _).2 htS
  have hfix := uc22r899c3_fixes_of_aut_Sz hK hn hp hp2 hq2 hqm Q ψ hψQ hψp htQ
    ((Subgroup.orderOf_coe (⟨t, htK⟩ : K)).symm.trans hto)
  exact mul_inv_eq_iff_eq_mul.1 (congrArg Subtype.val hfix)

theorem uc22r899c3_card_inf_le_Sz {K B : Subgroup Γ} {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : IsSz K n) (hB : IsElemAbelian p B) : Nat.card (B ⊓ K : Subgroup Γ) ≤ p := by
  have h1 := uc22s21r8100_card_le_of_isSz hK hp hp2
    ((hB.mono (inf_le_left : B ⊓ K ≤ B)).subgroupOf K)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : B ⊓ K ≤ K)).toEquiv] at h1

theorem uc22r899c3_exists_centralizing_D_Sz
    {K₁ K₂ A₀ : Subgroup Γ} {n m p q : ℕ} (hK₁ : IsSz K₁ n) (hK₂ : IsSz K₂ n)
    (hn : n = p * m) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ (2 * n) + 1) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqm : q ∣ 2 ^ m - 1) (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hA₀ : IsElemAbelian p A₀) (hA₀c : Nat.card A₀ = p ^ 4)
    (hA₀N₁ : A₀ ≤ normalizer (K₁ : Set Γ)) (hA₀N₂ : A₀ ≤ normalizer (K₂ : Set Γ)) {t₁ t₂ : Γ}
    (ht₁ : t₁ ∈ K₁) (ht₂ : t₂ ∈ K₂) (hto₁ : orderOf t₁ = q) (hto₂ : orderOf t₂ = q) :
    ∃ D : Subgroup Γ, IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧
      ∀ d ∈ D, d * t₁ = t₁ * d ∧ d * t₂ = t₂ * d := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hqn : q ∣ 2 ^ n - 1 :=
    hqm.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨p, by rw [hn, mul_comm]⟩)
  obtain ⟨S₁, hS₁, ht₁S⟩ := uc22r8100b_exists_sylow_mem ht₁ hto₁
  obtain ⟨S₂, hS₂, ht₂S⟩ := uc22r8100b_exists_sylow_mem ht₂ hto₂
  have h12 : K₁ ≤ normalizer (K₂ : Set Γ) := fun a ha => Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm)
  have h21 : K₂ ≤ normalizer (K₁ : Set Γ) := fun b hb => Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.2 fun a ha => hcomm a ha b hb)
  have h2S₁ : K₂ ≤ normalizer (S₁ : Set Γ) := fun b hb => Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.2 fun s hs => hcomm s (hS₁.le hs) b hb)
  obtain ⟨D₁, hD₁H, hD₁el, hD₁c⟩ := uc22r8100b_exists_elemAbelian_le_normalizer hp hq
    (K := K₁) (H := normalizer (K₁ : Set Γ) ⊓ normalizer (K₂ : Set Γ)) (S := S₁) (A := A₀)
    (le_inf Subgroup.le_normalizer h12) inf_le_left hS₁
    (uc22r899c3_not_dvd_normalizer_Sz hK₁ hp hp2 hpn hq hq2 hqn hS₁) hA₀ (le_inf hA₀N₁ hA₀N₂)
  obtain ⟨D₂, hD₂H, hD₂el, hD₂c⟩ := uc22r8100b_exists_elemAbelian_le_normalizer hp hq
    (K := K₂) (H := (normalizer (K₁ : Set Γ) ⊓ normalizer (K₂ : Set Γ)) ⊓ normalizer (S₁ : Set Γ))
    (S := S₂) (A := D₁) (le_inf (le_inf h21 Subgroup.le_normalizer) h2S₁)
    (inf_le_left.trans inf_le_right) hS₂
    (uc22r899c3_not_dvd_normalizer_Sz hK₂ hp hp2 hpn hq hq2 hqn hS₂) hD₁el hD₁H
  have hD₂2 : p ^ 2 ≤ Nat.card D₂ := by
    have h : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card D₂ :=
      calc p ^ 2 * p ^ 2 = Nat.card (A₀ ⊓ K₁ : Subgroup Γ) * Nat.card D₁ := by
            rw [← hD₁c, hA₀c]; ring
        _ ≤ p * (Nat.card (D₁ ⊓ K₂ : Subgroup Γ) * Nat.card D₂) := by
            rw [← hD₂c]
            exact Nat.mul_le_mul_right _ (uc22r899c3_card_inf_le_Sz hp hp2 hK₁ hA₀)
        _ ≤ p * (p * Nat.card D₂) := Nat.mul_le_mul_left _
            (Nat.mul_le_mul_right _ (uc22r899c3_card_inf_le_Sz hp hp2 hK₂ hD₁el))
        _ = p ^ 2 * Nat.card D₂ := by ring
    exact Nat.le_of_mul_le_mul_left h (pow_pos hp.pos 2)
  obtain ⟨D, hDD, hDel, hDc⟩ := UC6S846.exists_card_p_sq hp hD₂el hD₂2
  refine ⟨D, hDel, hDc, fun d hd => ?_⟩
  obtain ⟨⟨⟨hdK₁, hdK₂⟩, hdS₁⟩, hdS₂⟩ := hD₂H (hDD hd)
  have hdp : d ^ p = 1 := hDel.2 d hd
  exact ⟨uc22r899c3_centralizes_Sz hK₁ hn hp hp2 hq hq2 hqm hS₁ hdK₁ hdS₁ hdp ht₁S hto₁,
    uc22r899c3_centralizes_Sz hK₂ hn hp hp2 hq hq2 hqm hS₂ hdK₂ hdS₂ hdp ht₂S hto₂⟩

end Torus

variable {G : Type} [Group G] [Finite G]

theorem uc22r899c3_exists_comm_lift_Sz {M K₁ K₂ A₀ : Subgroup G}
    {n m p q : ℕ} (h₁ : K₁ ∈ calC M) (h₂ : K₂ ∈ calC M) (hne : K₁ ≠ K₂)
    (hS₁ : IsSz (Bar2 K₁) n) (hS₂ : IsSz (Bar2 K₂) n) (hn : n = p * m) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ (2 * n) + 1) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqm : q ∣ 2 ^ m - 1) (hA₀M : A₀ ≤ M) (hA₀ : IsElemAbelian p A₀)
    (hA₀c : Nat.card A₀ = p ^ 4) (hA₀N₁ : A₀ ≤ normalizer (K₁ : Set G))
    (hA₀N₂ : A₀ ≤ normalizer (K₂ : Set G)) {a₁ a₂ : G} (ha₁ : a₁ ∈ K₁) (ha₂ : a₂ ∈ K₂)
    (ha₁o : orderOf a₁ = q) (ha₂o : orderOf a₂ = q) :
    ∃ A : Subgroup G, A ≤ M ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
      ∀ e ∈ zpowers a₁ ⊔ zpowers a₂, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hPn : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  have hK₁M : K₁ ≤ M := uc22p22a_le_of_isSubnormal h₁.1
  have hK₂M : K₂ ≤ M := uc22p22a_le_of_isSubnormal h₂.1
  have hdisj : Disjoint (A₀.subgroupOf M) (uc22p21cPi M).ker := by
    refine Subgroup.disjoint_def.2 fun {x} hxA hxk => ?_
    exact uc22r8100b_eq_one_of_mem_pCore ((QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hxk))
      (hp.odd_of_ne_two hp2) (Subtype.ext (hA₀.2 (x : G) hxA))
  have hA₀el : IsElemAbelian p (barImage M A₀) := (hA₀.subgroupOf M).map (uc22p21cPi M)
  have hA₀card : Nat.card (barImage M A₀) = p ^ 4 := by
    rw [← hA₀c, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀M).toEquiv]
    exact UC6S846.card_map_of_disjoint_ker (uc22p21cPi M) (A₀.subgroupOf M) hdisj
  have hord : ∀ {a : G} (ha : a ∈ M), orderOf a = q → orderOf (uc22p21cPi M ⟨a, ha⟩) = q := by
    intro a ha hao
    have hx : orderOf (⟨a, ha⟩ : ↥M) = q := (Subgroup.orderOf_coe (⟨a, ha⟩ : ↥M)).symm.trans hao
    have hdvd : orderOf (uc22p21cPi M ⟨a, ha⟩) ∣ q := by
      rw [← hx]
      exact orderOf_map_dvd (uc22p21cPi M) _
    refine ((Nat.dvd_prime hq).1 hdvd).resolve_left fun h1 => ?_
    have hxq : (⟨a, ha⟩ : ↥M) ^ q = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
    have h2 := uc22r8100b_eq_one_of_mem_pCore
      ((QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h1)) (hq.odd_of_ne_two hq2) hxq
    rw [h2, orderOf_one] at hx
    exact hq.one_lt.ne hx
  obtain ⟨e₁, -⟩ := uc22p22l_barImage_equiv h₁
  obtain ⟨e₂, -⟩ := uc22p22l_barImage_equiv h₂
  obtain ⟨D, hDel, hDc, hDcomm⟩ := uc22r899c3_exists_centralizing_D_Sz
    (CFSG.Blueprint.LieModel.of_mulEquiv e₁ hS₁) (CFSG.Blueprint.LieModel.of_mulEquiv e₂ hS₂) hn hp
    hp2 hpn hq hq2 hqm (uc22p22l_barImage_commute h₁ h₂ hne) hA₀el hA₀card
    (uc22r8100b_barImage_le_normalizer hA₀N₁) (uc22r8100b_barImage_le_normalizer hA₀N₂)
    (uc22p21c_mem_barImage.2 ⟨⟨a₁, hK₁M ha₁⟩, ha₁, rfl⟩)
    (uc22p21c_mem_barImage.2 ⟨⟨a₂, hK₂M ha₂⟩, ha₂, rfl⟩) (hord (hK₁M ha₁) ha₁o)
    (hord (hK₂M ha₂) ha₂o)
  exact uc22r899c3_exists_lift hp hp2 hDel hDc (hK₁M ha₁) (hK₂M ha₂) hDcomm

theorem uc22r899c3_sp_of_odd_factor_Sz {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n m : ℕ}
    (hSz : IsSz (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hp : p ∈ D.sig) (hn : n = p * m)
    (hpn : p ∣ 2 ^ (2 * n) + 1) (hrm : r ∣ 2 ^ m - 1) : IsStronglyPEmbedded r D.M := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h1 := Nat.mod_eq_zero_of_dvd hpn
    rw [pow_mul, Nat.add_mod, Nat.pow_mod] at h1
    norm_num at h1
  have hshape : ∀ K ∈ conjSetOf D.M L, IsSz (Bar2 K) n := by
    rintro K ⟨g, -, rfl⟩
    obtain ⟨e⟩ := uc22p20d_bar2_conj g L
    exact CFSG.Blueprint.LieModel.of_mulEquiv e hSz
  refine uc22s21r899_sp_of_lift hSg hfour h614 h76 hL hc3 (Or.inr hSz) hs hsn hr hrs hp hp3 ?_
  intro K₁ h1S K₂ h2S hne A₀ hA₀M hA₀ hA₀c hA₀N a₁ a₂ ha₁ ha₂ ha₁o ha₂o
  exact uc22r899c3_exists_comm_lift_Sz (uc22p2214_calC_of_mem_conjSetOf hL h1S)
    (uc22p2214_calC_of_mem_conjSetOf hL h2S) hne (hshape K₁ h1S) (hshape K₂ h2S) hn hpp hp2 hpn hr
    (uc22ine229_ne_two hs hrs) hrm hA₀M hA₀ hA₀c (hA₀N K₁ h1S) (hA₀N K₂ h2S) ha₁ ha₂ ha₁o ha₂o

end CFSG.LocalAnalysis.UniquenessCase.UC22
