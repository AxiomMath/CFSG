module

public import CFSG.RankThree.GF2n.Stroth80.Sec713O2XActs
public import CFSG.RankThree.GF2n.Stroth80.OrderThreeOrbit
public import CFSG.RankThree.GF2n.Stroth80.Sec713Y
public import CFSG.RankThree.GF2n.Stroth80.Sec85CommMod
public import CFSG.Quasithin.Recognition.F112Crit.CoprimeCentralizer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem sec713_comm_CN_mem_Z0 (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (hCRW : Sec7CRWStatement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {x : G} (hxD : x ∈ O2NormPre M Q Z Z0)
    (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z)
    (hxW : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t) :
    ∀ k ∈ hc.CN t, ⁅k, x⁆ ∈ Z0 := by
  intro k hk
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨-, hDN, -⟩ := sec713_O2NormPre_facts hc ht hZ0
  have hxN := hDN hxD
  have hxM : x ∈ M := hxN.1.1
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS⟩ := tensorSetup_of_34 h34 G M Q Z B hc n hs.toSec5.width
    hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen
  obtain ⟨hkR, hkV⟩ := Ctx.mem_CN.mp hk
  have hkM : k ∈ M := hc.Rt_le_M t hkR
  have hQn : ∀ m ∈ M, m ∈ Subgroup.normalizer (Q : Set G) := fun m hm => hc.hyp.Q_normal.2 hm
  obtain ⟨hxR, hxV'⟩ := sec7_normalizes_of_zt hZt hZcard hc hs hZ0 hxN
  have hxRn : x ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G) :=
    conjSubgroup_eq_self_iff.mp hxR
  have hxVn : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp hxV'
  have hkVn : k ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht hkR
  have hkcR : ⁅k, x⁆ ∈ Rt M (LB M Q B) t := by
    have h1 : x * k⁻¹ * x⁻¹ ∈ Rt M (LB M Q B) t :=
      (Subgroup.mem_normalizer_iff.mp hxRn k⁻¹).mp ((Rt M (LB M Q B) t).inv_mem hkR)
    have e : ⁅k, x⁆ = k * (x * k⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Rt M (LB M Q B) t).mul_mem hkR h1
  refine hCRW G M Q Z B hc n t hs Z0 hZ0 _ hkcR ?_
  have hVW := sec7_V_le_W h310chi hc hs
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hWc : ∀ {l : G}, l ∈ Subgroup.normalizer (Q : Set G) →
      l ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) →
      (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), l * w * l⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t)) ∧
      (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), l⁻¹ * w * l ∈ Wt Q (Vt M (LB M Q B) B Z t)) := by
    intro l hlQ hlV
    refine ⟨fun w hw => conj_mem_Wt hlQ hlV hw, fun w hw => ?_⟩
    have := conj_mem_Wt (Subgroup.inv_mem _ hlQ) (Subgroup.inv_mem _ hlV) hw
    simpa using this
  obtain ⟨hkW, hkW'⟩ := hWc (hQn k hkM) hkVn
  obtain ⟨hxW1, hxW'⟩ := hWc (hQn x hxM) hxVn
  exact commutator_comm_mem_Z hQn hS.conj sec39_Z_le_Vt hVW hWQ hkM hxM hkW hkW' hxW1 hxW'
    hkV hxV (sec7_N_comm_W_le_V h52a hA hc hs k hk) hxW

theorem sec713_CN_le_O2NormPre (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hA : Sec7AExistsStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : hc.CN t ≤ O2NormPre M Q Z Z0 := by
  intro k hk
  have hle := CN_le_pCore_two_MbarPrime h34 h51 hA hZt hZcard hc hs hZ0
  have hkN : k ∈ NormH0 M Z Z0 := sec8_Rt_le_NormH0 hc hZ0 (Ctx.mem_CN.mp hk).1
  have hkM : k ∈ M := hkN.1.1
  have hkH : QuotientGroup.mk' (Q.subgroupOf M) ⟨k, hkM⟩ ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨k, hkM⟩, Subgroup.mem_subgroupOf.mpr hkN.1, rfl⟩
  have hkK : QuotientGroup.mk' (Q.subgroupOf M) ⟨k, hkM⟩ ∈ bar M Q (NormH0 M Z Z0) :=
    Subgroup.mem_map.mpr ⟨⟨k, hkM⟩, Subgroup.mem_subgroupOf.mpr hkN, rfl⟩
  set k' : ↥(MbarPrime M Q Z Z0) :=
    ⟨⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨k, hkM⟩, hkH⟩, Subgroup.mem_subgroupOf.mpr hkK⟩
  have hk' : k' ∈ ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
      (MbarPrime M Q Z Z0) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_map.mpr ⟨⟨k, hkM⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩))
  exact mem_O2NormPre.mpr ⟨hkM, k', hle hk', rfl⟩

theorem sec713_mem_normalizer_bar {A : Subgroup G} {g : G} (hg : g ∈ M)
    (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) :
    QuotientGroup.mk' (Q.subgroupOf M) ⟨g, hg⟩ ∈
      Subgroup.normalizer (bar M Q A : Set (Mbar M Q)) := by
  refine Subgroup.mem_normalizer_fintype fun u hu => ?_
  obtain ⟨a, haA, rfl⟩ := mem_bar_iff_exists_lift.mp hu
  refine mem_bar_iff_exists_lift.mpr ⟨⟨g, hg⟩ * a * ⟨g, hg⟩⁻¹, hA _ haA, ?_⟩
  simp only [map_mul, map_inv]

theorem step713Coprime_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h51 : Stroth51Statement) (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hCRW : Sec7CRWStatement) : Step713CoprimeStatement := by
  intro G _ _ M Q Z B _ hc n t hs hn4 Z0 hZ0 x hx hxN hxR hxV hxW
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨hD2, hDN, -⟩ := sec713_O2NormPre_facts hc ht hZ0
  have hxD : x ∈ O2NormPre M Q Z Z0 := mem_O2NormPre.mpr hx
  have hND : hc.CN t ≤ O2NormPre M Q Z Z0 :=
    sec713_CN_le_O2NormPre h34 h51 hA hZt hZcard hc hs hZ0
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun k hk => (Ctx.mem_CN.mp hk).1
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hZN : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  have hxM : x ∈ M := (hDN hxD).1.1
  obtain ⟨y, hyR, hyQ, hy3, hyC⟩ :=
    sec713Y_of_inputs h34 h311a h51 hA hPts G M Q Z B hc n t hs Z0 hZ0
  have hyN0 : y ∈ NormH0 M Z Z0 := sec8_Rt_le_NormH0 hc hZ0 hyR
  have hyM : y ∈ M := hRM hyR
  have hNn : ∀ g ∈ NormH0 M Z Z0, ∀ a ∈ hc.CN t, g * a * g⁻¹ ∈ hc.CN t := fun g hg a ha =>
    (Subgroup.mem_normalizer_iff.mp
      (conjSubgroup_eq_self_iff.mp (sec7_conj_CN_eq hZt hZcard hc hs hZ0 hg)) a).mp ha
  set π := QuotientGroup.mk' (Q.subgroupOf M)
  set Nb : Subgroup (Mbar M Q) := bar M Q (hc.CN t)
  set Db : Subgroup (Mbar M Q) := bar M Q (O2NormPre M Q Z Z0)
  set Zb : Subgroup (Mbar M Q) := bar M Q Z0
  set yb : Mbar M Q := π ⟨y, hyM⟩ with hyb
  set xb : Mbar M Q := π ⟨x, hxM⟩ with hxb
  have hlift : ∀ {S : Subgroup G}, ∀ u ∈ bar M Q S, ∃ g : G, ∃ hg : g ∈ M,
      g ∈ S ∧ π ⟨g, hg⟩ = u := by
    intro S u hu
    obtain ⟨g, hgS, hgu⟩ := mem_bar_iff_exists_lift.mp hu
    exact ⟨g, g.2, hgS, hgu⟩
  have hbar : ∀ {S : Subgroup G} {g : G} (hg : g ∈ M), g ∈ S → π ⟨g, hg⟩ ∈ bar M Q S :=
    fun hg hgS => mem_bar_iff_exists_lift.mpr ⟨⟨_, hg⟩, hgS, rfl⟩
  have hbarmono : ∀ {S T : Subgroup G}, S ≤ T → bar M Q S ≤ bar M Q T := by
    intro S T hST u hu
    obtain ⟨g, hgS, rfl⟩ := mem_bar_iff_exists_lift.mp hu
    exact mem_bar_iff_exists_lift.mpr ⟨g, hST hgS, rfl⟩
  have hDb2 : IsPGroup 2 ↥Db := (hD2.comap_subtype (K := M)).map π
  have hNb2 : IsPGroup 2 ↥Nb :=
    ((sec712_isPGroup_CN h34 h51 hA hc hs hZ0).comap_subtype (K := M)).map π
  have hyb3 : yb ^ 3 = 1 := by
    rw [hyb, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hy3))
  have hyb1 : yb ≠ 1 := by
    intro h
    exact hyQ (by simpa using Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have hyord : orderOf yb = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hyb3 hyb1
  have hyDb : yb ∈ Subgroup.normalizer (Db : Set (Mbar M Q)) :=
    sec713_mem_normalizer_bar hyM fun a ha => conj_mem_O2NormPre hyN0 ha
  have hyNb : yb ∈ Subgroup.normalizer (Nb : Set (Mbar M Q)) :=
    sec713_mem_normalizer_bar hyM fun a ha => hNn y hyN0 a ha
  have hxcomm : ∀ u ∈ Subgroup.zpowers yb, xb * u * xb⁻¹ * u⁻¹ ∈ Nb := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hyk : y ^ k ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).zpow_mem hyR k
    have hmem : ((⟨x, hxM⟩ * ⟨y, hyM⟩ ^ k * ⟨x, hxM⟩⁻¹ * (⟨y, hyM⟩ ^ k)⁻¹ : ↥M) : G) ∈
        hc.CN t := by
      have := hxR _ hyk
      simpa [commutatorElement_def] using this
    have h1 : π (⟨x, hxM⟩ * ⟨y, hyM⟩ ^ k * ⟨x, hxM⟩⁻¹ * (⟨y, hyM⟩ ^ k)⁻¹) ∈ Nb :=
      mem_bar_iff_exists_lift.mpr ⟨_, hmem, rfl⟩
    simpa [hyb, hxb] using h1
  have hoddX : Odd (Nat.card ↥(Subgroup.zpowers yb)) := by
    rw [Nat.card_zpowers, hyord]
    decide
  obtain ⟨nb, hnb, cb, -, hcb, hxbeq⟩ := CFSG.Quasithin.F112Crit.exists_mul_centralizer_of_comm_mem
    hDb2 hoddX (hbarmono hND)
    (Subgroup.zpowers_le.mpr hyDb) (Subgroup.zpowers_le.mpr hyNb) (hbar hxM hxD) hxcomm
  obtain ⟨k₀, hk₀M, hk₀N, hk₀b⟩ := hlift nb hnb
  set x' := k₀⁻¹ * x with hx'def
  have hx'M : x' ∈ M := M.mul_mem (M.inv_mem hk₀M) hxM
  have hx'D : x' ∈ O2NormPre M Q Z Z0 :=
    (O2NormPre M Q Z Z0).mul_mem ((O2NormPre M Q Z Z0).inv_mem (hND hk₀N)) hxD
  have hx'N : x' ∉ hc.CN t := by
    intro h
    apply hxN
    have : x = k₀ * x' := by rw [hx'def]; group
    rw [this]
    exact (hc.CN t).mul_mem hk₀N h
  have hx'b : π ⟨x', hx'M⟩ = cb := by
    have e : (⟨x', hx'M⟩ : ↥M) = ⟨k₀, hk₀M⟩⁻¹ * ⟨x, hxM⟩ := rfl
    rw [e, map_mul, map_inv, hk₀b, hxbeq]
    group
  have hx'y : π ⟨x', hx'M⟩ * yb = yb * π ⟨x', hx'M⟩ := by
    rw [hx'b]
    exact hcb yb (Subgroup.mem_zpowers yb)
  have hx'V : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x', v⁆ ∈ Z :=
    sec713_comm_Vt_of_O2 hZt hZcard hc hs hZ0 x' hx'D
  have hk₀V : k₀⁻¹ ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht (hNR ((hc.CN t).inv_mem hk₀N))
  have hx'W : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x', w⁆ ∈ Vt M (LB M Q B) B Z t := by
    intro w hw
    have e : ⁅x', w⁆ = (k₀⁻¹ * ⁅x, w⁆ * k₀⁻¹⁻¹) * ⁅k₀⁻¹, w⁆ := by
      rw [hx'def]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem
      ((Subgroup.mem_normalizer_iff.mp hk₀V _).mp (hxW w hw))
      (sec7_N_comm_W_le_V h52a hA hc hs _ ((hc.CN t).inv_mem hk₀N) w hw)
  have hNx' : ∀ k ∈ hc.CN t, ⁅k, x'⁆ ∈ Z0 :=
    sec713_comm_CN_mem_Z0 h34 h310chi hCRW h52a hA hZt hZcard hc hs hZ0 hx'D hx'V hx'W
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0 hZN
  have hNNc : ∀ a ∈ hc.CN t, ∀ b ∈ hc.CN t, ⁅a, b⁆ ∈ Z0 := hopp.2.2.2.2.2.2.1
  have hZbN : Zb ≤ Nb := hbarmono hZN
  have hN2' : ∀ a ∈ Nb, ∃ k : ℕ, a ^ (2 ^ k) = 1 := by
    intro a ha
    obtain ⟨k, hk⟩ := hNb2 ⟨a, ha⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hπc : ∀ {a b : G} (ha : a ∈ M) (hb : b ∈ M), ⁅π ⟨a, ha⟩, π ⟨b, hb⟩⁆ =
      π ⟨⁅a, b⁆, M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)⟩ := by
    intro a b ha hb
    rw [← map_commutatorElement]
    rfl
  have hcommQ : ∀ {a b : G} (ha : a ∈ M) (hb : b ∈ M), ⁅a, b⁆ ∈ Q →
      π ⟨a, ha⟩ * π ⟨b, hb⟩ = π ⟨b, hb⟩ * π ⟨a, ha⟩ := by
    intro a b ha hb h
    have h1 := (commutator_mem_iff_bar (M := M) (Q := Q) ⟨a, ha⟩ ⟨b, hb⟩).mp h
    exact (commutatorElement_eq_one_iff_mul_comm).mp h1
  have hNNb : ∀ a ∈ Nb, ∀ b ∈ Nb, ⁅a, b⁆ ∈ Zb := by
    intro a ha b hb
    obtain ⟨a', haM, haN, rfl⟩ := hlift a ha
    obtain ⟨b', hbM, hbN, rfl⟩ := hlift b hb
    rw [hπc haM hbM]
    exact hbar _ (hNNc a' haN b' hbN)
  have hZc : ∀ z ∈ Zb, ∀ a ∈ Nb, a * z = z * a := by
    intro z hz a ha
    obtain ⟨z', hzM, hzZ, rfl⟩ := hlift z hz
    obtain ⟨a', haM, haN, rfl⟩ := hlift a ha
    exact (hcommQ hzM haM (hZ0.comm_mem hzZ (hNR haN))).symm
  have hyZ : ∀ z ∈ Zb, yb * z = z * yb := by
    intro z hz
    obtain ⟨z', hzM, hzZ, rfl⟩ := hlift z hz
    exact (hcommQ hzM hyM (hZ0.comm_mem hzZ hyR)).symm
  have hyNb' : ∀ a ∈ Nb, yb * a * yb⁻¹ ∈ Nb := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hyNb a).mp ha
  have hCy : ∀ a ∈ Nb, yb * a = a * yb → a ∈ Zb := by
    intro a ha hya
    obtain ⟨a', haM, haN, rfl⟩ := hlift a ha
    have h1 : ⁅yb, π ⟨a', haM⟩⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hya
    have h2 : ⁅y, a'⁆ ∈ Q := (commutator_mem_iff_bar (M := M) (Q := Q) ⟨y, hyM⟩ ⟨a', haM⟩).mpr h1
    exact hbar haM (hyC a' haN h2)
  have hxNb : ∀ a ∈ Nb, ⁅a, π ⟨x', hx'M⟩⁆ ∈ Zb := by
    intro a ha
    obtain ⟨a', haM, haN, rfl⟩ := hlift a ha
    rw [hπc haM hx'M]
    exact hbar _ (hNx' a' haN)
  have key := exists_comm_eq_of_order_three hZbN hN2' hNNb hZc hyb3 hyNb' hyZ hCy hx'y hxNb
  refine ⟨x', mem_O2NormPre.mp hx'D, hx'N, fun m hm => ?_⟩
  have hmM : m ∈ M := hRM (hNR hm)
  obtain ⟨zb, hzb, heq⟩ := key (π ⟨m, hmM⟩) (hbar hmM hm)
  obtain ⟨z, hzM, hzZ, rfl⟩ := hlift zb hzb
  refine ⟨z, hzZ, ?_⟩
  rw [hπc hmM hx'M, hπc hzM hx'M] at heq
  have h1 := QuotientGroup.eq.mp heq
  have h2 := Subgroup.mem_subgroupOf.mp h1
  have h3 : (⁅z, x'⁆)⁻¹ * ⁅m, x'⁆ ∈ Q := by simpa using Q.inv_mem h2
  have e : ⁅m, x'⁆ * (⁅z, x'⁆)⁻¹ = ⁅m, x'⁆ * ((⁅z, x'⁆)⁻¹ * ⁅m, x'⁆) * (⁅m, x'⁆)⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2
    (M.mul_mem (M.mul_mem (M.mul_mem hmM hx'M) (M.inv_mem hmM)) (M.inv_mem hx'M))) _).mp h3

end CFSG.RankThree.GF2n.Stroth80
