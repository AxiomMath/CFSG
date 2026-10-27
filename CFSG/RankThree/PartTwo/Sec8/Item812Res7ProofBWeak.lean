module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofLocal
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofPaExp
import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofLocalRank
import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofTools
import CFSG.RankThree.PartTwo.Sec8.Item86ResProofOrders
import CFSG.RankThree.PartTwo.Sec11.TwoStarProofComponent
import CFSG.RankThree.PartTwo.KFacts.K412Conjugacy
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSp)
open Item812Res3 (IsMaxPSub)

namespace Item812Res7

section Generic

theorem exists_orderOf_nine_projSL : ∃ x : projSL 2 (GaloisField 2 3), orderOf x = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  obtain ⟨S, hScyc, hScard, -⟩ := CFSG.Glauberman.Dickson.h84_nonsplit_torus_data hF
  have h9 : Nat.card S = 9 := by rw [hScard, hF]; norm_num
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S)
  have hgo : orderOf g = 9 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, h9]
  refine ⟨(Sec4.projSLEquivPSL (GaloisField 2 3)).symm (g : Matrix.ProjectiveSpecialLinearGroup
    (Fin 2) (GaloisField 2 3)), ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hgo]

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_le_of_isMaxPSub {H P T : Subgroup G} (hP : IsMaxPSub 3 P H)
    (hT : IsPGroup 3 T) (hTH : T ≤ H) : ∃ k ∈ H, ∀ t ∈ T, k * t * k⁻¹ ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Sylow 3 H :=
    { toSubgroup := P.subgroupOf H
      isPGroup' := hP.2.1.comap_subtype
      is_maximal' := fun {Q} hQ hPQ => by
        have hQG : IsPGroup 3 (Q.map H.subtype) := hQ.map _
        have hPQ' : P ≤ Q.map H.subtype := fun x hx =>
          ⟨⟨x, hP.1 hx⟩, hPQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
        have heq := hP.2.2 _ hQG hPQ' (Subgroup.map_subtype_le Q)
        rw [← heq]
        exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective Q).symm }
  obtain ⟨k, hk⟩ := KFacts.K412.exists_conj_le_sylow (hT.comap_subtype (K := H)) S
  refine ⟨k, k.2, fun t ht => ?_⟩
  have h1 : (MulAut.conj k).toMonoidHom ⟨t, hTH ht⟩ ∈ (S : Subgroup H) :=
    hk ⟨⟨t, hTH ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  exact Subgroup.mem_subgroupOf.mp h1

end Generic

section Pa

variable {G : Type} [Group G] [Finite G]
variable {A : Subgroup G} {a : G} {X Y P Q R Pa : Subgroup G}

open Item812Res4

theorem pa_le_normalizer_a (hY : IsYQuot Y) (hc : Fin812Pre A a X Y P Q R Pa)
    (hAab : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) :
    Pa ≤ Subgroup.normalizer (A : Set G) := by
  intro p hp
  have hpB := pa_le_normalizer_b hY hc hAab haA ha1 hA81 hYa hp
  have hpa : p * a = a * p := Subgroup.mem_centralizer_singleton_iff.mp (hc.pa_max.1 hp)
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨i, y, hy, rfl⟩ := exists_eq_zpow_mul_of_mem_a hc hAab haA hx
  have h1 : p * a ^ i * p⁻¹ = a ^ i := by
    rw [(Commute.zpow_right (show Commute p a from hpa) i).eq, mul_inv_cancel_right]
  have h2 : p * y * p⁻¹ ∈ sec8B A X := (Subgroup.mem_normalizer_iff.mp hpB y).mp hy
  have e : p * (a ^ i * y) * p⁻¹ = (p * a ^ i * p⁻¹) * (p * y * p⁻¹) := by group
  rw [e, h1]
  exact A.mul_mem (A.zpow_mem haA i) (b_le_a h2)

theorem card_le_of_abelian_le_pa (hW : KF812WreathCent) (hY : IsYQuot Y)
    (hc : Fin812Pre A a X Y P Q R Pa) (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) {T : Subgroup G} (hTPa : T ≤ Pa)
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) {w : G} (hwT : w ∈ T) (hw9 : orderOf w = 9) :
    Nat.card T ≤ 27 := by
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hB27 := card_b hc hAab haA ha1 hA81
  have hBab := isElemAbelian_of_le hAab (b_le_a (A := A) (X := X))
  obtain ⟨i, y, hy, hwy⟩ := exists_eq_zpow_mul_of_mem_pa hc hYa (hTPa hwT)
  have hyB : y ∉ sec8B A X := by
    intro hyB
    have hwA : w ∈ A := hwy ▸ A.mul_mem (A.zpow_mem haA i) (b_le_a hyB)
    have h3 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one (hAab.2 w hwA)
    rw [hw9] at h3
    norm_num at h3
  have hD := card_inf_centralizer_le hW hY inf_le_right (isPGroup_pa_inf_y hc)
    (b_le_pa_inf_y hc) hBab hB27 hy hyB
  set D := sec8B A X ⊓ Subgroup.centralizer {y} with hDdef
  have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ D, u * v = v * u := by
    intro u hu v hv
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact congrArg Subtype.val
      (hAab.1.is_comm.comm ⟨a ^ j, A.zpow_mem haA j⟩ ⟨v, b_le_a hv.1⟩)
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hsup9 : Nat.card (Subgroup.zpowers a ⊔ D : Subgroup G) ≤ 9 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1] at hcard
    have hpos : 0 < Nat.card (Subgroup.zpowers a ⊓ D : Subgroup G) := Nat.card_pos
    nlinarith
  have hTA : A ⊓ T ≤ Subgroup.zpowers a ⊔ D := by
    intro s hs
    obtain ⟨j, x, hx, rfl⟩ := exists_eq_zpow_mul_of_mem_a hc hAab haA hs.1
    have hsw := hTc _ hs.2 w hwT
    rw [hwy] at hsw
    have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp (hYa hy.2)
    have hxa : x * a = a * x := congrArg Subtype.val
      (hAab.1.is_comm.comm ⟨x, b_le_a hx⟩ ⟨a, haA⟩)
    have hxy : x * y = y * x := by
      have h1 : Commute x (a ^ i) := Commute.zpow_right hxa i
      have h2 : Commute y (a ^ j) := Commute.zpow_right hya j
      have h3 : Commute (a ^ i) (a ^ j) := Commute.zpow_zpow_self a i j
      have hL : a ^ j * x * (a ^ i * y) = a ^ j * a ^ i * (x * y) := by
        rw [show a ^ j * x * (a ^ i * y) = a ^ j * (x * a ^ i) * y by group, h1.eq]
        group
      have hR : a ^ i * y * (a ^ j * x) = a ^ j * a ^ i * (y * x) := by
        rw [show a ^ i * y * (a ^ j * x) = a ^ i * (y * a ^ j) * x by group, h2.eq,
          show a ^ i * (a ^ j * y) * x = (a ^ i * a ^ j) * (y * x) by group, h3.eq]
      exact mul_left_cancel (hL.symm.trans (hsw.trans hR))
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers a j)
      ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxy⟩
  have hATcard : Nat.card (A ⊓ T : Subgroup G) ≤ 9 :=
    (Subgroup.card_le_of_le hTA).trans hsup9
  have hPa := card_pa_le hc ha3 ha1 hYa
  have hS81 : Nat.card (Pa ⊓ Y : Subgroup G) ≤ 81 :=
    card_le_of_le hY inf_le_right (isPGroup_pa_inf_y hc)
  have hTN : T ≤ Subgroup.normalizer (A : Set G) :=
    hTPa.trans (pa_le_normalizer_a hY hc hAab haA ha1 hA81 hYa)
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hTN
  have h2 : Nat.card (A ⊔ T : Subgroup G) ≤ Nat.card Pa :=
    Subgroup.card_le_of_le (sup_le hc.le_pa hTPa)
  rw [hA81] at h1
  have h3 : 81 * Nat.card T ≤ 243 * 9 := by
    rw [← h1]
    exact Nat.mul_le_mul (h2.trans (hPa.trans (by omega))) hATcard
  omega

end Pa

section Comm

variable {G : Type} [Group G] [Finite G]

theorem sup_comm_of_commute {E F : Subgroup G} (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hF : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hEF : ∀ x ∈ E, ∀ y ∈ F, x * y = y * x) :
    ∀ x ∈ E ⊔ F, ∀ y ∈ E ⊔ F, x * y = y * x := by
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E F hEF
  intro x hx y hy
  have hx' : x ∈ ((E ⊔ F : Subgroup G) : Set G) := hx
  have hy' : y ∈ ((E ⊔ F : Subgroup G) : Set G) := hy
  rw [hset] at hx' hy'
  obtain ⟨u₁, hu₁, v₁, hv₁, rfl⟩ := hx'
  obtain ⟨u₂, hu₂, v₂, hv₂, rfl⟩ := hy'
  have h1 := hEF u₂ hu₂ v₁ hv₁
  have h2 := hEF u₁ hu₁ v₂ hv₂
  have h3 := hE u₁ hu₁ u₂ hu₂
  have h4 := hF v₁ hv₁ v₂ hv₂
  calc u₁ * v₁ * (u₂ * v₂) = u₁ * (v₁ * u₂) * v₂ := by group
    _ = u₁ * (u₂ * v₁) * v₂ := by rw [h1]
    _ = (u₁ * u₂) * (v₁ * v₂) := by group
    _ = (u₂ * u₁) * (v₂ * v₁) := by rw [h3, h4]
    _ = u₂ * (u₁ * v₂) * v₁ := by group
    _ = u₂ * (v₂ * u₁) * v₁ := by rw [h2]
    _ = u₂ * v₂ * (u₁ * v₁) := by group

end Comm

end Item812Res7

section Final

open Item812Res4

namespace Item812Res7

theorem exists_fin812Pre (hS : Fin812PaSplit) (hBq : Fin812BEq) (hQR : Fin812QR)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X Y : Subgroup G} {n : ℕ} (h : Sec8Final G A c L a b X Y n) :
    ∃ P Q R Pa : Subgroup G, Fin812Pre A a X Y P Q R Pa := by
  have hAab := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have ha1 : a ≠ 1 := h.a_ne_one
  have hA81 : Nat.card A = 81 := h.card_eq
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hYa := le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y
  have hY : IsYQuot Y := h.item89_Y
  have haY : a ∉ Y := not_mem_of_mem_thetaComponentsAt ha3 ha1 h.mem_thetaComponentsAt_Y hY
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc x hx a haA)
  obtain ⟨Pa, hPa, hAPa⟩ := exists_isMaxPSub_le (isPGroup_of_isElemAbelian hAab) hAC
  have hpaeq := hS G A c L a b X Y n h Pa hPa hAPa
  have hBeq := hBq G A c L a b X Y n h
  have hB27 : Nat.card (sec8B A X) = 27 := by
    have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ sec8B A X, u * v = v * u := by
      intro u hu v hv
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact hAc _ (A.zpow_mem haA j) v (b_le_a hv)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    have hsup : Subgroup.zpowers a ⊔ (sec8B A X) = A := by
      refine le_antisymm (sup_le ((Subgroup.zpowers_le).mpr haA) b_le_a) fun x hx => ?_
      have hx' : x ∈ ((Subgroup.zpowers a ⊔ (Pa ⊓ Y) : Subgroup G) : Set G) := by
        rw [hpaeq]
        exact hAPa hx
      have hcomm' : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Pa ⊓ Y, u * v = v * u := by
        intro u hu v hv
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        exact (Commute.zpow_left (show Commute a v from
          (Subgroup.mem_centralizer_singleton_iff.mp (hYa hv.2)).symm) j).eq
      rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm').2] at hx'
      obtain ⟨u, hu, v, hv, huv⟩ := hx'
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hvA : v ∈ A := by
        have : v = (a ^ j)⁻¹ * x := by rw [← huv]; group
        rw [this]
        exact A.mul_mem (A.inv_mem (A.zpow_mem haA j)) hx
      have hvB : v ∈ sec8B A X := by
        rw [hBeq]
        exact ⟨hvA, hv.2⟩
      rw [← huv]
      exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers a j) hvB
    have hinf : Subgroup.zpowers a ⊓ (sec8B A X) = ⊥ := by
      have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
      have hdvd : Nat.card (Subgroup.zpowers a ⊓ (sec8B A X) : Subgroup G) ∣ 3 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers a ⊓ (sec8B A X) ≤ _)
        rwa [Nat.card_zpowers, hao] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have heq : Subgroup.zpowers a ⊓ (sec8B A X) = Subgroup.zpowers a :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hao])
        have haB : a ∈ sec8B A X := by
          have : a ∈ Subgroup.zpowers a ⊓ (sec8B A X) := by
            rw [heq]
            exact Subgroup.mem_zpowers a
          exact this.2
        rw [hBeq] at haB
        exact haY haB.2
    rw [hsup, hinf, Subgroup.card_bot, mul_one, hA81, Nat.card_zpowers,
      orderOf_eq_prime ha3 ha1] at hcard
    omega
  have hPaN : Pa ≤ Subgroup.normalizer ((sec8B A X) : Set G) := by
    have hBS : sec8B A X ≤ Pa ⊓ Y :=
      le_inf (b_le_a.trans hAPa) (by rw [hBeq]; exact inf_le_right)
    have hS81 : Nat.card (Pa ⊓ Y : Subgroup G) ≤ 3 * Nat.card (sec8B A X) := by
      rw [hB27]
      exact (card_le_of_le hY inf_le_right (hPa.2.1.to_le inf_le_left)).trans (by norm_num)
    have hSN : Pa ⊓ Y ≤ Subgroup.normalizer ((sec8B A X) : Set G) :=
      le_normalizer_of_card_le (hPa.2.1.to_le inf_le_left) hBS hS81
    intro p hp
    have hp' : p ∈ ((Subgroup.zpowers a ⊔ (Pa ⊓ Y) : Subgroup G) : Set G) := by
      rw [hpaeq]
      exact hp
    have hcomm' : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Pa ⊓ Y, u * v = v * u := by
      intro u hu v hv
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (Commute.zpow_left (show Commute a v from
        (Subgroup.mem_centralizer_singleton_iff.mp (hYa hv.2)).symm) j).eq
    rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm').2] at hp'
    obtain ⟨u, hu, v, hv, rfl⟩ := hp'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    refine Subgroup.mul_mem _ ?_ (hSN hv)
    exact Item812Res3.mem_normalizer_of_forall_commute fun x hx =>
      hAc _ (A.zpow_mem haA j) x (b_le_a hx)
  obtain ⟨Q, hQ, hPaQ⟩ := exists_isMaxPSub_normalized hPa.2.1
    (fun p hp => mem_normalizer_centralizer (hPaN hp))
  obtain ⟨R, hqeq, hrc, hcr, hrp, hbr, hor, hoq, hrw⟩ :=
    hQR G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  have hAQ : A ≤ Q := by
    have hAB : A ≤ Subgroup.centralizer ((sec8B A X) : Set G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => hAc y (b_le_a hy) x hx
    have hQA := hQ.2.2 _ (isPGroup_sup hQ.2.1 (isPGroup_of_isElemAbelian hAab)
      (hAPa.trans hPaQ)) le_sup_left (sup_le hQ.1 hAB)
    exact hQA ▸ le_sup_right
  have hanr : a ∉ R := fun haR => by
    have haB : a ∈ sec8B A X := hor a haR ha3
    rw [hBeq] at haB
    exact haY haB.2
  exact ⟨R ⊔ Pa, Q, R, Pa,
    ⟨hPa, hAPa, hpaeq, hBeq, hQ, hPaQ, hqeq, hrc, hcr, hrp, hbr, hor, hAQ, hoq, hanr, hrw, rfl⟩⟩

open Item86ResProof in
theorem exists_orderOf_nine {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a b : G} {X Y : Subgroup G} {n : ℕ} (h : Sec8Final G A c L a b X Y n)
    {e : G} (heB : e ∈ sec8B A X) (heb : e ∉ Subgroup.zpowers b) :
    ∃ w : G, orderOf w = 9 ∧ w * b = b * w ∧ w * e = e * w ∧
      Nat.card ((Subgroup.zpowers b ⊔ Subgroup.zpowers e) ⊔ Subgroup.zpowers w : Subgroup G) =
        81 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb1 : b ≠ 1 := h.isGammaIndex.2.1
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have heA : e ∈ A := b_le_a heB
  have he3 : e ^ 3 = 1 := hAab.2 e heA
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := by
    obtain ⟨X', -, hX'⟩ := h.pairRel.2.2.1
    rw [← hX']
    exact Subgroup.map_subtype_le X'
  obtain ⟨m, hm⟩ := h.item810 e heB heb
  have hm1 : 1 ≤ m := one_le_of_isGammaIndex hm
  have hX1 : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 (3 * 1))) := by
    simpa using h.item89_X
  have hT1 : IsGammaType (X ⧸ aschbacherSolvableCore 3 X) 1 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hX1))))
  have hm' : m = 1 := eq_of_isGammaType hm1 le_rfl (isGammaType_of_isGammaIndex hm) hT1
  subst hm'
  set K := inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({e} : Set G)) with hKdef
  have hKX : K ≤ X ⊓ Subgroup.centralizer ({e} : Set G) := Subgroup.map_subtype_le _
  have hL2 : Nonempty (imageModTheta X K ≃* projSL 2 (GaloisField 2 3)) := by
    obtain ⟨-, -, -, ⟨k, hk, hkm, hke, -⟩ | ⟨-, hL⟩⟩ := hm
    · obtain ⟨eX⟩ := hX1
      exact ((sigF4_of_reeF4 le_rfl ⟨k, hk, hkm, hke⟩).false_of_sigSp4
        (sigSp4_of_projSp le_rfl eX) le_rfl).elim
    · simpa using hL
  obtain ⟨ι⟩ := hL2
  have hZ : Subgroup.center (imageModTheta X K) = ⊥ :=
    Sec11.TwoStarProof.center_eq_bot_of_projSL ι
  obtain ⟨x₀, hx₀⟩ := exists_orderOf_nine_projSL
  set yb : imageModTheta X K := ι.symm x₀ with hyb
  have hyb9 : orderOf yb = 9 := by rw [hyb, MulEquiv.orderOf_eq, hx₀]
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 X) with hπ
  obtain ⟨k₀, hk₀K, hk₀⟩ := yb.2
  have hk₀o : orderOf (π k₀) = 9 := by
    rw [show π k₀ = (yb : X ⧸ aschbacherSolvableCore 3 X) from hk₀, Subgroup.orderOf_coe, hyb9]
  obtain ⟨s, r', hr', ho⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos k₀).ne' 3
    (by norm_num)
  have hr'0 : r' ≠ 0 := fun h0 => hr' (h0 ▸ dvd_zero 3)
  set w₀ : X := k₀ ^ r' with hw₀
  have hcop : Nat.Coprime 9 r' := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hr')
  have hπw : orderOf (π w₀) = 9 := by
    rw [hw₀, map_pow, orderOf_pow' _ hr'0, hk₀o, hcop.gcd_eq_one, Nat.div_one]
  have hw9' : w₀ ^ 9 = 1 := by
    have hmem : w₀ ^ 9 ∈ aschbacherSolvableCore 3 X := by
      rw [← QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 X)]
      change π (w₀ ^ 9) = 1
      rw [map_pow, ← hπw, pow_orderOf_eq_one]
    have hpow : (w₀ ^ 9) ^ 3 ^ s = 1 := by
      rw [hw₀, ← pow_mul, ← pow_mul, show r' * (9 * 3 ^ s) = (3 ^ s * r') * 9 by ring, ← ho,
        pow_mul, pow_orderOf_eq_one, one_pow]
    exact KFacts.eq_one_of_pow_three_pow_eq_one (Item812Res4.not_dvd_card_core X) hmem hpow
  have hw₀o : orderOf w₀ = 9 := by
    refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hw9') ?_
    rw [← hπw]
    exact orderOf_map_dvd π w₀
  have hw₀K : w₀ ∈ K.subgroupOf X := (K.subgroupOf X).pow_mem hk₀K r'
  set w : G := (w₀ : G) with hwdef
  have hw9 : orderOf w = 9 := by rw [hwdef, Subgroup.orderOf_coe, hw₀o]
  have hwK : w ∈ K := Subgroup.mem_subgroupOf.mp hw₀K
  have hwe : w * e = e * w := Subgroup.mem_centralizer_singleton_iff.mp (hKX hwK).2
  have hwb : w * b = b * w := Subgroup.mem_centralizer_singleton_iff.mp (hXb (hKX hwK).1)
  set E := Subgroup.zpowers b ⊔ Subgroup.zpowers e with hEdef
  have hE9 : Nat.card E = 3 ^ 2 :=
    Item812Res3.card_sup_zpowers_eq_sq Nat.prime_three hb3 hb1 he3 heb (hAc b hbA e heA)
  have hEA : E ≤ A := sup_le ((Subgroup.zpowers_le).mpr hbA) ((Subgroup.zpowers_le).mpr heA)
  have hEK : ∀ u ∈ E, ∀ k ∈ K, u * k = k * u := by
    have hle : E ≤ Subgroup.centralizer (K : Set G) := by
      refine sup_le ((Subgroup.zpowers_le).mpr ?_) ((Subgroup.zpowers_le).mpr ?_)
      · exact Subgroup.mem_centralizer_iff.mpr fun k hk =>
          (Subgroup.mem_centralizer_singleton_iff.mp (hXb (hKX hk).1))
      · exact Subgroup.mem_centralizer_iff.mpr fun k hk =>
          (Subgroup.mem_centralizer_singleton_iff.mp (hKX hk).2)
    intro u hu k hk
    exact (Subgroup.mem_centralizer_iff.mp (hle hu) k hk).symm
  have hw3E : w ^ 3 ∉ E := by
    intro hw3
    have hc3 : π (w₀ ^ 3) ∈ imageModTheta X K := ⟨w₀ ^ 3, (K.subgroupOf X).pow_mem hw₀K 3, rfl⟩
    have hcen : (⟨π (w₀ ^ 3), hc3⟩ : imageModTheta X K) ∈ Subgroup.center (imageModTheta X K) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨_, ⟨k', hk', rfl⟩⟩
      apply Subtype.ext
      change π k' * π (w₀ ^ 3) = π (w₀ ^ 3) * π k'
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have h1 := hEK (w ^ 3) hw3 k' (Subgroup.mem_subgroupOf.mp hk')
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      exact h1.symm
    rw [hZ, Subgroup.mem_bot] at hcen
    have h3 : π w₀ ^ 3 = 1 := by
      rw [← map_pow]
      exact congrArg Subtype.val hcen
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hπw] at this
    norm_num at this
  have hinf : E ⊓ Subgroup.zpowers w = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvE, hvw⟩
    rw [Subgroup.mem_bot]
    by_contra hv1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hvw
    have hv3 : (w ^ k) ^ 3 = 1 := hAab.2 _ (hEA hvE)
    have h9 : (9 : ℤ) ∣ k * 3 := by
      rw [← zpow_natCast, ← zpow_mul] at hv3
      have := orderOf_dvd_iff_zpow_eq_one.mpr hv3
      rwa [hw9] at this
    obtain ⟨k', hk'⟩ : ∃ k' : ℤ, k = 3 * k' := ⟨k / 3, by omega⟩
    have hle : Subgroup.zpowers (w ^ k) ≤ Subgroup.zpowers (w ^ 3) := by
      rw [Subgroup.zpowers_le, hk', zpow_mul, zpow_ofNat]
      exact Subgroup.zpow_mem_zpowers (w ^ 3) k'
    have ho3 : orderOf (w ^ 3) = 3 := by
      rw [orderOf_pow' _ (by norm_num), hw9]
      norm_num
    have hov : orderOf (w ^ k) = 3 := orderOf_eq_prime hv3 hv1
    have heq : Subgroup.zpowers (w ^ k) = Subgroup.zpowers (w ^ 3) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, ho3, hov])
    apply hw3E
    have : w ^ 3 ∈ Subgroup.zpowers (w ^ k) := heq ▸ Subgroup.mem_zpowers _
    exact (Subgroup.zpowers_le.mpr hvE) this
  have hEw : ∀ u ∈ E, ∀ v ∈ Subgroup.zpowers w, u * v = v * u := by
    have hle : E ≤ Subgroup.centralizer ({w} : Set G) :=
      sup_le ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr hwb.symm))
        ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr hwe.symm))
    intro u hu v hv
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have huw : u * w = w * u := Subgroup.mem_centralizer_singleton_iff.mp (hle hu)
    exact (Commute.zpow_right huw j).eq
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E _ hEw
  rw [hinf, Subgroup.card_bot, mul_one, hE9, Nat.card_zpowers, hw9] at hcard
  exact ⟨w, hw9, hwb, hwe, by rw [hcard]; norm_num⟩

theorem not_conj_mem_b (hW : KF812WreathCent) {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {c : G} {L : Subgroup G} {a b : G} {X Y : Subgroup G} {n : ℕ}
    (h : Sec8Final G A c L a b X Y n) {P Q R Pa : Subgroup G} (hc : Fin812Pre A a X Y P Q R Pa)
    {e : G} (heB : e ∈ sec8B A X) (k : G) (hek : e = k * a * k⁻¹) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have haA : a ∈ A := h.a_mem
  have ha1 : a ≠ 1 := h.a_ne_one
  have hA81 : Nat.card A = 81 := h.card_eq
  have hYa := le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y
  have hY : IsYQuot Y := h.item89_Y
  have hbA : b ∈ A := h.isGammaIndex.1
  have hB27 := card_b hc hAab haA ha1 hA81
  obtain ⟨e', he'B, he'b, hsub⟩ : ∃ e' ∈ sec8B A X, e' ∉ Subgroup.zpowers b ∧
      ∀ x : G, x * e' = e' * x → x * b = b * x → x * e = e * x := by
    by_cases heb : e ∈ Subgroup.zpowers b
    · have hnle : ¬ sec8B A X ≤ Subgroup.zpowers b := by
        intro hle
        have h1 := Subgroup.card_le_of_le hle
        rw [hB27, Nat.card_zpowers] at h1
        have h2 : orderOf b ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) (hAab.2 b hbA)
        omega
      obtain ⟨e', he'B, he'b⟩ := Set.not_subset.mp hnle
      refine ⟨e', he'B, he'b, fun x _ hxb => ?_⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp heb
      exact (Commute.zpow_right (show Commute x b from hxb) j).eq
    · exact ⟨e, heB, heb, fun x hxe _ => hxe⟩
  obtain ⟨w, hw9, hwb, hwe', hcard⟩ := exists_orderOf_nine h he'B he'b
  set S := (Subgroup.zpowers b ⊔ Subgroup.zpowers e') ⊔ Subgroup.zpowers w with hSdef
  have he'A : e' ∈ A := b_le_a he'B
  have heA : e ∈ A := b_le_a heB
  have hEA : Subgroup.zpowers b ⊔ Subgroup.zpowers e' ≤ A :=
    sup_le ((Subgroup.zpowers_le).mpr hbA) ((Subgroup.zpowers_le).mpr he'A)
  have hwe : w * e = e * w := hsub w hwe' hwb
  have hSC : S ≤ Subgroup.centralizer ({e} : Set G) := by
    refine sup_le (hEA.trans fun x hx => ?_) ((Subgroup.zpowers_le).mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hAc x hx e heA)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hwe
  have hEw : ∀ u ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers e', ∀ v ∈ Subgroup.zpowers w,
      u * v = v * u := by
    have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers e' ≤ Subgroup.centralizer ({w} : Set G) :=
      sup_le ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr hwb.symm))
        ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr hwe'.symm))
    intro u hu v hv
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hle hu)) j).eq
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x :=
    sup_comm_of_commute (fun x hx y hy => hAc x (hEA hx) y (hEA hy))
      (fun x hx y hy => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_zpow_self w i j).eq) hEw
  set T := S.map (MulAut.conj k⁻¹).toMonoidHom with hTdef
  have hTH : T ≤ Subgroup.centralizer ({a} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    have hse : s * e = e * s := Subgroup.mem_centralizer_singleton_iff.mp (hSC hs)
    rw [Subgroup.mem_centralizer_singleton_iff]
    change k⁻¹ * s * k⁻¹⁻¹ * a = a * (k⁻¹ * s * k⁻¹⁻¹)
    rw [hek] at hse
    calc k⁻¹ * s * k⁻¹⁻¹ * a = k⁻¹ * (s * (k * a * k⁻¹)) * k := by group
      _ = k⁻¹ * (k * a * k⁻¹ * s) * k := by rw [hse]
      _ = a * (k⁻¹ * s * k⁻¹⁻¹) := by group
  have hTcard : Nat.card T = 3 ^ 4 := by
    rw [hTdef, Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hcard]
    norm_num
  obtain ⟨k', -, hk'⟩ := exists_conj_le_of_isMaxPSub hc.pa_max (IsPGroup.of_card hTcard) hTH
  set T' := T.map (MulAut.conj k').toMonoidHom with hT'def
  have hT'Pa : T' ≤ Pa := by
    rintro _ ⟨t, ht, rfl⟩
    exact hk' t ht
  have hT'comm : ∀ x ∈ T', ∀ y ∈ T', x * y = y * x := by
    rintro _ ⟨_, ⟨s₁, hs₁, rfl⟩, rfl⟩ _ ⟨_, ⟨s₂, hs₂, rfl⟩, rfl⟩
    have h1 := congrArg (fun s => (MulAut.conj k').toMonoidHom ((MulAut.conj k⁻¹).toMonoidHom s))
      (hScomm s₁ hs₁ s₂ hs₂)
    simpa only [map_mul] using h1
  have hwT' : (MulAut.conj k').toMonoidHom ((MulAut.conj k⁻¹).toMonoidHom w) ∈ T' :=
    ⟨_, ⟨w, Subgroup.mem_sup_right (Subgroup.mem_zpowers w), rfl⟩, rfl⟩
  have hw'9 : orderOf ((MulAut.conj k').toMonoidHom ((MulAut.conj k⁻¹).toMonoidHom w)) = 9 := by
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
    exact hw9
  have h27 := card_le_of_abelian_le_pa hW hY hc hAab haA ha1 hA81 hYa hT'Pa hT'comm hwT' hw'9
  have hT'card : Nat.card T' = 3 ^ 4 := by
    rw [hT'def, Subgroup.card_map_of_injective (MulAut.conj k').injective, hTcard]
  rw [hT'card] at h27
  norm_num at h27

end Item812Res7

theorem fin812BWeak_of (h84 : Pair84A) (hBq : Fin812BEq) (hQR : Fin812QR)
    (hW : KF812WreathCent) : Fin812BWeak := by
  intro G _ _ A c L a b X Y n h g hgB
  obtain ⟨P, Q, R, Pa, hc⟩ := Item812Res7.exists_fin812Pre (fin812PaSplit_of_84 h84) hBq hQR h
  have hAab := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have ha1 : a ≠ 1 := h.a_ne_one
  have hA81 : Nat.card A = 81 := h.card_eq
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hYa := le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y
  have hY : IsYQuot Y := h.item89_Y
  have hle : (sec8B A X).map (MulAut.conj g).toMonoidHom ≤ sec8B A X := by
    rintro _ ⟨y, hy, rfl⟩
    by_contra hu
    have huA : (MulAut.conj g).toMonoidHom y ∈ A := hgB ⟨y, hy, rfl⟩
    obtain ⟨r, -, k, hk⟩ := exists_conj_eq_zpow hW hY hc hAab haA ha1 hA81 hYa huA hu
    have hgy : (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := rfl
    have hk3 : a ^ k = a ^ (k % 3) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
      rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ha3, one_zpow, mul_one]
    obtain h0 | h1 | h2 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    · apply hu
      rw [hk, hk3, h0, zpow_zero, mul_one, mul_inv_cancel]
      exact (sec8B A X).one_mem
    · have hgy' : g * y * g⁻¹ = r * a * r⁻¹ := by rw [← hgy, hk, hk3, h1, zpow_one]
      refine Item812Res7.not_conj_mem_b hW h hc hy (g⁻¹ * r) ?_
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = g⁻¹ * (r * a * r⁻¹) * g := by rw [hgy']
        _ = g⁻¹ * r * a * (g⁻¹ * r)⁻¹ := by group
    · have ha2 : a ^ (2 : ℤ) = a⁻¹ := by
        have e : a ^ (2 : ℤ) = a⁻¹ * a ^ 3 := by group
        rw [e, ha3, mul_one]
      have hgy' : g * y * g⁻¹ = r * a⁻¹ * r⁻¹ := by rw [← hgy, hk, hk3, h2, ha2]
      refine Item812Res7.not_conj_mem_b hW h hc ((sec8B A X).inv_mem hy) (g⁻¹ * r) ?_
      have hinv : g * y⁻¹ * g⁻¹ = r * a * r⁻¹ := by
        calc g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
          _ = (r * a⁻¹ * r⁻¹)⁻¹ := by rw [hgy']
          _ = r * a * r⁻¹ := by group
      calc y⁻¹ = g⁻¹ * (g * y⁻¹ * g⁻¹) * g := by group
        _ = g⁻¹ * (r * a * r⁻¹) * g := by rw [hinv]
        _ = g⁻¹ * r * a * (g⁻¹ * r)⁻¹ := by group
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

end Final

end CFSG.RankThree.PartTwo.Sec8
