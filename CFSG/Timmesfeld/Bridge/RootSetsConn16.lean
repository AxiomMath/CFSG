module

public import CFSG.Timmesfeld.Bridge.RootSetsConn14
public import CFSG.Timmesfeld.Bridge.OddTranspQ
public import CFSG.Timmesfeld.Bridge.RootSetsConn13

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity
open scoped commutatorElement

variable {G : Type} [Group G] {D : Set G}

theorem eq_one_or_eq_of_mem_zpowers {K : Type*} [Group K] {t y : K} (ht : t * t = 1)
    (hy : y ∈ Subgroup.zpowers t) : y = 1 ∨ y = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, ht, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, ht, one_zpow, one_mul]

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem exists_mem_sylow_not_mem (hC : ConnCex D) (h : Step6 D a b c x z P) (S : Sylow 2 G) :
    ∃ s ∈ D, s ∈ S ∧ s ∉ P := by
  have := hC.setting.finite
  have hD := hC.setting.root
  have hN := hC.setting.normal
  obtain ⟨d, hd, e, he, h4⟩ := hC.setting.nondeg
  have hd2 := hD.mul_self_eq_one hd
  have he2 := hD.mul_self_eq_one he
  have hH : IsPGroup 2 (Subgroup.closure ({d, e} : Set G)) :=
    isPGroup_two_closure_pair hd2 he2 (k := 2) (by rw [show 2 ^ 2 = 4 by norm_num, ← h4,
      pow_orderOf_eq_one])
  obtain ⟨S', hS'⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  have hmem : ∀ y ∈ Subgroup.closure ({d, e} : Set G), g * y * g⁻¹ ∈ S := fun y hy => by
    rw [← hg]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ (hS' hy)
  by_contra hall
  push Not at hall
  have hdP := hall _ (hN g d hd) (hmem d (Subgroup.subset_closure (by simp)))
  have heP := hall _ (hN g e he) (hmem e (Subgroup.subset_closure (by simp)))
  have hc : Commute d e := (Commute.conj_iff g).1
    (h.commute_of_mem hC (hN g d hd) (hN g e he) hdP heP)
  have hdvd : orderOf (d * e) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one hd2 he2).1 hc)
  rw [h4] at hdvd
  exact absurd (Nat.le_of_dvd two_pos hdvd) (by norm_num)

theorem exists_mem_normalizer_not_mem (hC : ConnCex D) (h : Step6 D a b c x z P) :
    ∃ f ∈ D, f ∈ Subgroup.normalizer (P : Set G) ∧ f ∉ P := by
  have := hC.setting.finite
  have hN := hC.setting.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hPS⟩ := h.hP2.exists_le_sylow
  obtain ⟨s, hs, hsS, hsP⟩ := h.exists_mem_sylow_not_mem hC S
  have hle : Subgroup.closure (D ∩ (S : Set G)) ≤ S :=
    (Subgroup.closure_le _).2 fun y hy => hy.2
  have hT2 : IsPGroup 2 (Subgroup.closure (D ∩ (S : Set G))) := S.isPGroup'.to_le hle
  have hne : Subgroup.closure {y | y ∈ D ∧ y ∈ P} ≠ Subgroup.closure (D ∩ (S : Set G)) := by
    intro heq
    apply hsP
    rw [h.hPL, heq]
    exact Subgroup.subset_closure ⟨hs, hsS⟩
  obtain ⟨y, ⟨hyD, -⟩, hyP, hyN⟩ := exists_mem_normalizer_of_closure_ne hT2
    (S := D ∩ (S : Set G)) (T := {y | y ∈ D ∧ y ∈ P})
    (fun g hg t ht => ⟨hN g t ht.1, S.mul_mem (S.mul_mem (hle hg) ht.2) (S.inv_mem (hle hg))⟩)
    rfl (fun y hy => ⟨hy.1, hPS hy.2⟩) hne
  rw [← h.hPL] at hyP hyN
  exact ⟨y, hyD, hyN, hyP⟩

theorem mul_conj_mem (hC : ConnCex D) (h : Step6 D a b c x z P) {f : G} (hf : f ∈ D)
    (hfN : f ∈ Subgroup.normalizer (P : Set G)) {ℓ : G} (hℓ : ℓ ∈ D) (hℓP : ℓ ∈ P)
    (hfℓ : ¬ Commute f ℓ) :
    ℓ * (f * ℓ * f⁻¹) ∈ D ∧ ℓ * (f * ℓ * f⁻¹) ∈ P ∧ Commute f (ℓ * (f * ℓ * f⁻¹)) := by
  have hD := hC.setting.root
  have hN := hC.setting.normal
  have hP : ∀ p, p ∈ P ↔ f * p * f⁻¹ ∈ P := fun p => Subgroup.mem_normalizer_iff.1 hfN p
  have hS := h.isPGroup_sup_zpowers hC hf hfN
  have h4 := orderOf_mul_eq_four_of_isPGroup hD hS hf hℓ
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers f)) (Subgroup.mem_sup_left hℓP) hfℓ
  have hcm : Commute ℓ (f * ℓ * f⁻¹) :=
    h.commute_of_mem hC hℓ (hN f ℓ hℓ) hℓP ((hP ℓ).1 hℓP)
  have hsq : ℓ * (f * ℓ * f⁻¹) = (f * ℓ) ^ 2 := by
    rw [hcm.eq, pow_two, hD.inv_eq hf]
    group
  refine ⟨hsq ▸ hD.sq_mem hf hℓ h4, P.mul_mem hℓP ((hP ℓ).1 hℓP), ?_⟩
  have hf2 := hD.mul_self_eq_one hf
  have hfi := hD.inv_eq hf
  show f * (ℓ * (f * ℓ * f⁻¹)) = ℓ * (f * ℓ * f⁻¹) * f
  calc f * (ℓ * (f * ℓ * f⁻¹)) = f * (f * ℓ * f⁻¹ * ℓ) := by rw [hcm.eq]
    _ = ℓ * (f * ℓ * f⁻¹) * f := by
      rw [hfi, show f * (f * ℓ * f * ℓ) = f * f * ℓ * f * ℓ by group, hf2, one_mul,
        show ℓ * (f * ℓ * f) * f = ℓ * f * ℓ * (f * f) by group, hf2, mul_one]

theorem commute_of_mul_mem_qcore (hB : OddTranspBender) (h3 : Step6ThreeProductHyp)
    (hC : ConnCex D) (h : Step6 D a b c x z P) {f : G} (hf : f ∈ D)
    (hfN : f ∈ Subgroup.normalizer (P : Set G)) {t : G} (ht : t ∈ D) (htP : t ∈ P)
    (hft : Commute f t) {ℓ : G} (hℓ : ℓ ∈ D) (hℓP : ℓ ∈ P) (hq : ℓ * t ∈ qcore D x P) :
    Commute f ℓ := by
  have hN := hC.setting.normal
  have h1 := h.conj_mul_mem_qcore hB h3 hC hfN hℓ ht hℓP htP hq
  rw [hft.eq, mul_inv_cancel_right] at h1
  exact h.commute_of_mul_conj_mem_qcore hC hf hfN hℓ hℓP
    (mul_mem_qcore_trans hC ht hq (mul_mem_qcore_comm hC (hN f ℓ hℓ) ht h1))

theorem commutatorElement_eq (hC : ConnCex D) (h : Step6 D a b c x z P) {t : G} (ht : t ∈ D)
    (htP : t ∈ P) {q : lsub D x P} (hq : q ∈ CFSG.pCore 2 (lsub D x P)) {y : lsub D x P}
    (hy : y ∈ Subgroup.zpowers (⟨t, mem_lsub_of_mem ht htP⟩ : lsub D x P)) :
    ((⁅q, y⁆ : lsub D x P) : G) = 1 ∨
      ∃ ℓ ∈ D, ℓ ∈ P ∧ ℓ * t ∈ qcore D x P ∧ ((⁅q, y⁆ : lsub D x P) : G) = ℓ * t := by
  have hD := hC.setting.root
  have hN := hC.setting.normal
  set tX : lsub D x P := ⟨t, mem_lsub_of_mem ht htP⟩ with htX
  have ht2 : tX * tX = 1 := Subtype.ext (hD.mul_self_eq_one ht)
  rcases eq_one_or_eq_of_mem_zpowers ht2 hy with rfl | rfl
  · left
    rw [commutatorElement_one_right]
    rfl
  right
  have hℓD : (q : G) * t * (q : G)⁻¹ ∈ D := hN _ t ht
  have hcomm : ((⁅q, tX⁆ : lsub D x P) : G) = (q : G) * t * (q : G)⁻¹ * t := by
    rw [commutatorElement_def]
    change (q : G) * t * (q : G)⁻¹ * t⁻¹ = (q : G) * t * (q : G)⁻¹ * t
    rw [hD.inv_eq ht]
  have hQ : ((⁅q, tX⁆ : lsub D x P) : G) ∈ qcore D x P := by
    refine ⟨⁅q, tX⁆, ?_, rfl⟩
    have : ⁅q, tX⁆ = q * (tX * q⁻¹ * tX⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact (CFSG.pCore 2 _).mul_mem hq
      (CFSG.pCore_normal.conj_mem _ ((CFSG.pCore 2 _).inv_mem hq) tX)
  have hℓX : (q : G) * t * (q : G)⁻¹ ∈ lsub D x P :=
    (lsub D x P).mul_mem ((lsub D x P).mul_mem q.2 (mem_lsub_of_mem ht htP))
      ((lsub D x P).inv_mem q.2)
  have hℓP : (q : G) * t * (q : G)⁻¹ ∈ P := by
    refine h.mem_of_isPGroup hC (h.isPGroup_sup_qcore hC)
      (fun l _ hlP => Subgroup.mem_sup_left hlP) hℓD
      (Subgroup.mem_centralizer_singleton_iff.1 (h.lsub_le_centralizer hℓX)) ?_
    have : (q : G) * t * (q : G)⁻¹ = ((⁅q, tX⁆ : lsub D x P) : G) * t := by
      rw [hcomm, mul_assoc _ t t, hD.mul_self_eq_one ht, mul_one]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hQ) (Subgroup.mem_sup_left htP)
  exact ⟨_, hℓD, hℓP, hcomm ▸ hQ, hcomm⟩

theorem commute_of_mem_commutator (hB : OddTranspBender) (h3 : Step6ThreeProductHyp)
    (hC : ConnCex D) (h : Step6 D a b c x z P) {f : G} (hf : f ∈ D)
    (hfN : f ∈ Subgroup.normalizer (P : Set G)) {t : G} (ht : t ∈ D) (htP : t ∈ P)
    (hft : Commute f t) {w : lsub D x P}
    (hw : w ∈ ⁅CFSG.pCore 2 (lsub D x P),
      Subgroup.zpowers (⟨t, mem_lsub_of_mem ht htP⟩ : lsub D x P)⁆) :
    Commute f (w : G) := by
  have hle : ⁅CFSG.pCore 2 (lsub D x P),
      Subgroup.zpowers (⟨t, mem_lsub_of_mem ht htP⟩ : lsub D x P)⁆ ≤
      (Subgroup.centralizer ({f} : Set G)).comap (lsub D x P).subtype := by
    rw [Subgroup.commutator_le]
    intro q hq y hy
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    rcases h.commutatorElement_eq hC ht htP hq hy with h1 | ⟨ℓ, hℓ, hℓP, hq', heq⟩
    · rw [Subgroup.coe_subtype, h1, one_mul, mul_one]
    · rw [Subgroup.coe_subtype, heq]
      exact ((h.commute_of_mul_mem_qcore hB h3 hC hf hfN ht htP hft hℓ hℓP hq').mul_right
        hft).eq.symm
  have hw' := hle hw
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hw'
  exact hw'.symm

theorem exists_conj_mul_mem_qcore (hB : OddTranspBender) (hC : ConnCex D)
    (h : Step6 D a b c x z P) {e₁ e₂ : G} (he₁ : e₁ ∈ D) (he₂ : e₂ ∈ D) (he₁P : e₁ ∈ P)
    (he₂P : e₂ ∈ P) :
    ∃ g : G, g ∈ Subgroup.normalizer (P : Set G) ∧ g * e₁ * g⁻¹ * e₂ ∈ qcore D x P := by
  classical
  have := hC.setting.finite
  have hD := hC.setting.root
  have hN := hC.setting.normal
  set X := lsub D x P with hX
  set Q := CFSG.pCore 2 X with hQ
  set π := QuotientGroup.mk' Q with hπ
  have hBX := h.isBenderGroup_pCore hB hC
  obtain ⟨Sb, hSb⟩ := h.exists_sylow_ge hC
  set eX₁ : X := ⟨e₁, mem_lsub_of_mem he₁ he₁P⟩
  set eX₂ : X := ⟨e₂, mem_lsub_of_mem he₂ he₂P⟩
  have hmemS : ∀ y : X, (y : G) ∈ P → π y ∈ Sb := fun y hy => hSb ⟨y, hy, rfl⟩
  have hinv : ∀ y : X, (y : G) ∈ D → π y * π y = 1 := fun y hy => by
    rw [← map_mul, show y * y = 1 from Subtype.ext (hD.mul_self_eq_one hy), map_one]
  have hne1 : ∀ y : X, (y : G) ∈ D → π y ≠ 1 := fun y hy h1 =>
    h.not_mem_qcore hC hy ⟨y, (QuotientGroup.eq_one_iff y).1 h1, rfl⟩
  have hcen : ∀ y : X, (y : G) ∈ D → (y : G) ∈ P → π y ∈ Sb ∧ ∀ q ∈ Sb, Commute q (π y) :=
    fun y hy hyP => ⟨hmemS y hyP, fun q hq =>
      (Asc72.IsBenderGroup.commute_of_mul_self_eq_one hBX Sb (hmemS y hyP) (hinv y hy) q hq).symm⟩
  obtain ⟨gb, hgbN, hgb⟩ := Asc72.IsBenderGroup.exists_normalizer_conj hBX Sb
    (hcen eX₁ he₁ he₁P) (hne1 eX₁ he₁) (hcen eX₂ he₂ he₂P) (hne1 eX₂ he₂)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q gb
  refine ⟨g, h.mem_normalizer_of_conj_mem_L hC fun ℓ hℓ hℓP => ?_, ?_⟩
  · set lX : X := ⟨ℓ, mem_lsub_of_mem hℓ hℓP⟩
    have hyD : ((g * lX * g⁻¹ : X) : G) ∈ D := hN _ ℓ hℓ
    have hyS : π (g * lX * g⁻¹) ∈ Sb := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hgbN (π lX)).1 (hmemS lX hℓP)
    exact h.mem_of_mem_sylow hC hSb hyD hyS
  · refine ⟨g * eX₁ * g⁻¹ * eX₂, (QuotientGroup.eq_one_iff _).1 ?_, rfl⟩
    change π (g * eX₁ * g⁻¹ * eX₂) = 1
    rw [map_mul, map_mul, map_mul, map_inv, hgb, hinv eX₂ he₂]

theorem exists_mem_normalizer_commute (hB : OddTranspBender) (h3 : Step6ThreeProductHyp)
    (hC : ConnCex D) (h : Step6 D a b c x z P) {e : G} (he : e ∈ D) (heP : e ∈ P) :
    ∃ f ∈ D, f ∈ Subgroup.normalizer (P : Set G) ∧ f ∉ P ∧ Commute f e := by
  have hN := hC.setting.normal
  obtain ⟨f₀, hf₀, hf₀N, hf₀P⟩ := h.exists_mem_normalizer_not_mem hC
  obtain ⟨ℓ, hℓ, hℓP, hfℓ⟩ : ∃ ℓ ∈ D, ℓ ∈ P ∧ ¬ Commute f₀ ℓ := by
    by_contra hall
    push Not at hall
    exact hf₀P (h.hcent f₀ hf₀ hall)
  obtain ⟨htD, htP, hft⟩ := h.mul_conj_mem hC hf₀ hf₀N hℓ hℓP hfℓ
  set t := ℓ * (f₀ * ℓ * f₀⁻¹) with ht
  obtain ⟨g, hgN, hgt⟩ := h.exists_conj_mul_mem_qcore hB hC htD he htP heP
  have hP : ∀ p, p ∈ P ↔ g * p * g⁻¹ ∈ P := fun p => Subgroup.mem_normalizer_iff.1 hgN p
  refine ⟨g * f₀ * g⁻¹, hN g f₀ hf₀, ?_, fun hP' => hf₀P ((hP f₀).2 hP'), ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hf₀N) (Subgroup.inv_mem _ hgN)
  · exact h.commute_of_mul_mem_qcore hB h3 hC (hN g f₀ hf₀)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hf₀N) (Subgroup.inv_mem _ hgN))
      (hN g t htD) ((hP t).1 htP) ((Commute.conj_iff g).2 hft) he heP
      (mul_mem_qcore_comm hC (hN g t htD) he hgt)

theorem pCore_commute (hB : OddTranspBender) (h3 : Step6ThreeProductHyp) (hC : ConnCex D)
    (h : Step6 D a b c x z P) {p q : lsub D x P} (hp : p ∈ CFSG.pCore 2 (lsub D x P))
    (hq : q ∈ CFSG.pCore 2 (lsub D x P)) : Commute p q := by
  have := hC.setting.finite
  obtain ⟨SK, hmemS, a', b', c', n, hK⟩ := h.exists_thirdKindHyp hB hC
  obtain ⟨f, hf, hfN, hfP, hfa⟩ := h.exists_mem_normalizer_commute hB h3 hC h.ha h.haP
  obtain ⟨hcen, hmem⟩ := OddTransp.oddTranspCommutatorQ _ _ _ _ _ _ _ hK
  have hw := hmem ⟨a, mem_lsub_of_mem h.ha h.haP⟩
    ⟨h.mem_lclass hC h.ha h.haP, hmemS ⟨a, mem_lsub_of_mem h.ha h.haP⟩ h.haP⟩ p hp q hq
  have hfw := h.commute_of_mem_commutator hB h3 hC hf hfN h.ha h.haP hfa hw
  exact commutatorElement_eq_one_iff_commute.1
    (h.eq_one_of_commute_center hC hf hfN hfP (hcen p hp q hq) hfw)

end Step6

end CFSG.Timmesfeld.Bridge
