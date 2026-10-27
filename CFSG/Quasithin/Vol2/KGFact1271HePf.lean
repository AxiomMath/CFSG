module

public import CFSG.Quasithin.Vol2.KGFact1271He
public import CFSG.Quasithin.Vol2.Ch12Sec7Thm7
public import CFSG.Quasithin.Vol2.Ch12Sec7L5c
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInner

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB CFSG.Sporadic.HeldB.Native
  CFSG.QuasithinUnique.Id2519.HeInner

namespace S127.HeExcl

theorem conj_mem_thetaOf {G : Type} [Group G] {H : Subgroup G} {h : G} (hh : h ∈ H) {x : G}
    (hx : x ∈ thetaOf H) : h * x * h⁻¹ ∈ thetaOf H := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    exact Subgroup.subset_closure
      ⟨H.mul_mem (H.mul_mem hh hy.1) (H.inv_mem hh), by rw [orderOf_conj_eq]; exact hy.2⟩
  | one => simp
  | mul a b _ _ ha hb =>
    have e : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
    rw [e]
    exact (thetaOf H).mul_mem ha hb
  | inv a _ ha =>
    have e : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
    rw [e]
    exact (thetaOf H).inv_mem ha

theorem eq_bot_or_le_of_commutator_eq {X : Type*} [Group X] {D K : Subgroup X}
    [IsSimpleGroup ↥D] (hXD : commutator X ≤ D) (hK : K.Normal) (hKK : ⁅K, K⁆ = K) :
    K = ⊥ ∨ D ≤ K := by
  have hKD : K ≤ D := by
    rw [← hKK]
    exact (Subgroup.commutator_mono le_top le_top).trans (by rw [← commutator_def]; exact hXD)
  have := hK.subgroupOf D
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf D) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hKD
  · right
    rwa [Subgroup.subgroupOf_eq_top] at h

theorem false_of_mulEquiv_heInnerGrp0
    {C : Type*} [Group C] (φ : C ≃* ↥heInnerGrp0)
    {N : Subgroup C} (hN : N.Normal) (hNN : ⁅N, N⁆ = N) (h5 : 5 ∣ Nat.card ↥N)
    (h7 : ¬ 7 ∣ Nat.card ↥N) : False := by
  set ψ : C →* ↥heXp.originalSubgroup := heRes0.comp φ.toMonoidHom with hψ
  have hsurj : Function.Surjective ψ := heRes0_surjective.comp φ.surjective
  have hK : (N.map ψ).Normal := hN.map ψ hsurj
  have hKK : ⁅N.map ψ, N.map ψ⁆ = N.map ψ := by rw [← Subgroup.map_commutator, hNN]
  have := heDp_simple
  have : IsSimpleGroup ↥(heDp.originalSubgroup.subgroupOf heXp.originalSubgroup) :=
    (Subgroup.subgroupOfEquivOfLe heDp_le_heXp).isSimpleGroup
  rcases eq_bot_or_le_of_commutator_eq commutator_le_subgroupOf hK hKK with hb | hle
  ·
    have hNk : N.map φ.toMonoidHom ≤ heRes0.ker := by
      rintro _ ⟨n, hn, rfl⟩
      have hmem : ψ n ∈ N.map ψ := Subgroup.mem_map_of_mem ψ hn
      rw [hb, Subgroup.mem_bot] at hmem
      exact hmem
    have hd := Subgroup.card_dvd_of_le hNk
    rw [card_ker_heRes0, Subgroup.card_map_of_injective φ.injective] at hd
    have h54 := dvd_trans h5 hd
    norm_num at h54
  ·
    have h1 := Subgroup.card_dvd_of_le hle
    have h2 := Subgroup.card_map_dvd N ψ
    have h3 : Nat.card ↥(heDp.originalSubgroup.subgroupOf heXp.originalSubgroup) = 20160 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe heDp_le_heXp).toEquiv, card_heDp]
    rw [h3] at h1
    exact h7 (dvd_trans (by norm_num : 7 ∣ 20160) (dvd_trans h1 h2))

theorem false_of_mulEquiv_heCent1
    {C : Type*} [Group C]
    (φ : C ≃* ↥(centralizerIn heP heT1P)) {N : Subgroup C} (h5 : 5 ∣ Nat.card ↥N) : False := by
  have h1 := Subgroup.card_subgroup_dvd_card N
  rw [Nat.card_congr φ.toEquiv, card_heP_cent1] at h1
  have h := dvd_trans h5 h1
  norm_num at h

end S127.HeExcl

open S127.HeExcl in
theorem he1271Excl_of
    (h74 : Lemma12_7_4) : He1271Excl := by
  intro G _ _ T L V h ⟨e⟩ t ht h18 hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime (S127.sq_eq_one_of_mem h.hyp ht) (S127.ne_one_of_relIndex h18 (by decide))
  obtain ⟨-, -, ⟨-, -, htheta, ha5, hperf⟩, -, -⟩ := (h74 G T L V h).2 t ht h18
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
  set Lt : Subgroup G := oTwoUpper (L ⊓ C) with hLt
  have hLtC : Lt ≤ C := (oTwoUpper_le _).trans inf_le_right
  have hθ : Lt = thetaOf C := by rw [htheta, inf_eq_right.mpr hle]
  obtain ⟨e5⟩ := ha5
  have h60 : Nat.card (↥Lt ⧸ CFSG.pCore 2 ↥Lt) = 60 := by
    rw [Nat.card_congr e5.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    rfl
  have hcard : Nat.card ↥Lt = Nat.card ↥(CFSG.pCore 2 ↥Lt) * 60 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Lt), h60, mul_comm]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Lt))
  set N : Subgroup ↥C := Lt.subgroupOf C with hNdef
  have hNcard : Nat.card ↥N = Nat.card ↥Lt :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLtC).toEquiv
  have h5 : 5 ∣ Nat.card ↥N := by
    rw [hNcard, hcard]
    exact Dvd.dvd.mul_left (by norm_num) _
  have h7 : ¬ 7 ∣ Nat.card ↥N := by
    rw [hNcard, hcard, ha]
    intro hd
    exact (by norm_num : ¬ 7 ∣ 60)
      ((Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 7 2)).dvd_of_dvd_mul_left hd)
  have hN : N.Normal := ⟨fun n hn c => by
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    rw [hθ] at hn ⊢
    exact conj_mem_thetaOf c.2 hn⟩
  have hNmap : N.map C.subtype = Lt := by
    rw [hNdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLtC]
  have hNN : ⁅N, N⁆ = N := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, hNmap]
    exact S127.L5.commutator_eq_self hperf
  set θe : G ≃* heP := e.trans heEquivP with hθe
  have ht2' : orderOf ((θe t : heP) : Equiv.Perm (Fin 8330)) = 2 := by
    rw [Subgroup.orderOf_coe, orderOf_mulEquiv_apply, ht2]
  let f : ↥C ≃* ↥(centralizerIn heP ((θe t : heP) : Equiv.Perm (Fin 8330))) :=
    (centralizerEquiv θe t).trans (heCentralizerEquiv (θe t))
  rcases involution_conj_cases (θe t).2 ht2' with ⟨c, hc, hct⟩ | ⟨c, hc, hct⟩
  · exact false_of_mulEquiv_heInnerGrp0
      (f.trans (((MulEquiv.subgroupCongr (by rw [hct]; rfl)).trans
        (infCentralizerConjEquiv hc (heGenPerm 0))).trans
        (MulEquiv.subgroupCongr heInnerGrp0_eq.symm))) hN hNN h5 h7
  · exact false_of_mulEquiv_heCent1 (f.trans ((MulEquiv.subgroupCongr (by rw [hct]; rfl)).trans
      (infCentralizerConjEquiv hc heT1P))) h5

end CFSG.Quasithin.H13
