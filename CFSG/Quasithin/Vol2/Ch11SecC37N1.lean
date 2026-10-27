module

public import CFSG.Quasithin.Vol2.Ch11SecC37E

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_le_of_normal_sylow {X P D E : Subgroup G}
    (hP : QuasithinUnique.IsSylowTwoOf P X) (hPn : X ≤ Subgroup.normalizer (P : Set G))
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D X) (hEX : E ≤ X) (hE : Odd (Nat.card E)) :
    ∃ p ∈ P, E ≤ D.map (MulAut.conj p).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := E ⊔ P with hY
  have hPY : P ≤ Y := le_sup_right
  have hEY : E ≤ Y := le_sup_left
  have hYX : Y ≤ X := sup_le hEX hP.1
  set N : Subgroup ↥Y := P.subgroupOf Y with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPY).mpr (hYX.trans hPn)
  have hP2 : IsPGroup 2 ↥N := hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm
  have hNsolv : Group.IsSolvable ↥N := by
    have := hP2.isNilpotent
    infer_instance
  have hPE : P ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h2 : IsPGroup 2 ↥(P ⊓ E) := hP.2.1.to_le inf_le_left
    obtain ⟨k, hk⟩ := h2 ⟨x, hx⟩
    have h1 : orderOf x ∣ Nat.card E := by
      rw [← Subgroup.orderOf_mk x hx.2]
      exact orderOf_dvd_natCard _
    have h3 : orderOf x ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    rcases j with _ | j
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hj
    · exact absurd (hj ▸ hE.of_dvd_nat h1) (by rw [Nat.odd_iff, pow_succ]; simp)
  have hPD : P ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h2 : IsPGroup 2 ↥(P ⊓ D) := hP.2.1.to_le inf_le_left
    obtain ⟨k, hk⟩ := h2 ⟨x, hx⟩
    have h1 : orderOf x ∣ Nat.card D := by
      rw [← Subgroup.orderOf_mk x hx.2]
      exact orderOf_dvd_natCard _
    have h3 : orderOf x ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    rcases j with _ | j
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hj
    · exact absurd (hj ▸ hD.2.1.of_dvd_nat h1) (by rw [Nat.odd_iff, pow_succ]; simp)
  obtain ⟨k, hk⟩ := hD.2.2
  have hcardX : Nat.card X = 2 ^ k * Nat.card D := by
    have h1 := Subgroup.relIndex_mul_card D X
    rw [inf_eq_left.mpr hD.1, hk] at h1
    exact h1.symm
  have hcardP : Nat.card P = 2 ^ k := by
    obtain ⟨a, ha⟩ := hP.2.1.exists_card_eq
    have h1 := Subgroup.card_mul_index (P.subgroupOf X)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv, ha, hcardX] at h1
    have hodd : Odd (P.subgroupOf X).index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hP.2.2)
    rw [ha, SecA.eq_of_two_pow_mul_odd hodd hD.2.1 h1]
  have hXPD : ∀ x ∈ X, ∃ p ∈ P, ∃ d ∈ D, x = p * d := by
    let f : ↥P × ↥D → ↥X := fun pd => ⟨(pd.1 : G) * pd.2, X.mul_mem (hP.1 pd.1.2) (hD.1 pd.2.2)⟩
    have hf : Function.Injective f := by
      rintro ⟨p, d⟩ ⟨p', d'⟩ h
      have h1 : (p : G) * d = p' * d' := congrArg Subtype.val h
      have h2 : (p' : G)⁻¹ * p = d' * (d : G)⁻¹ := by
        calc (p' : G)⁻¹ * p = (p' : G)⁻¹ * (p * d) * (d : G)⁻¹ := by group
          _ = (p' : G)⁻¹ * (p' * d') * (d : G)⁻¹ := by rw [h1]
          _ = d' * (d : G)⁻¹ := by group
      have h3 : (p' : G)⁻¹ * p ∈ P ⊓ D :=
        ⟨P.mul_mem (P.inv_mem p'.2) p.2, h2 ▸ D.mul_mem d'.2 (D.inv_mem d.2)⟩
      rw [hPD, Subgroup.mem_bot] at h3
      have hp : p = p' := Subtype.ext (inv_mul_eq_one.mp h3).symm
      subst hp
      have hd : d = d' := Subtype.ext (mul_left_cancel h1)
      rw [hd]
    have hcard : Nat.card X ≤ Nat.card (↥P × ↥D) := by
      rw [Nat.card_prod, hcardP, hcardX]
    have hbij := hf.bijective_of_nat_card_le hcard
    intro x hx
    obtain ⟨⟨p, d⟩, hpd⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨p, p.2, d, d.2, (congrArg Subtype.val hpd).symm⟩
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    have h1 : Nat.card N = 2 ^ k := by
      rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv, hcardP]
    have h2 : ¬ 2 ∣ N.index := by
      intro h2
      apply hP.2.2
      have h3 : P.relIndex Y * Y.relIndex X = P.relIndex X :=
        Subgroup.relIndex_mul_relIndex P Y X hPY hYX
      exact (h2.trans (Dvd.intro _ h3))
    rw [h1]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)
  have hE' : (N : Set ↥Y) * ((E.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    have hEP : E ≤ Subgroup.normalizer (P : Set G) := hEX.trans hPn
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_le_normalizer hEP
      (show (y : G) ∈ P ⊔ E by rw [sup_comm]; exact y.2)
    refine Set.mem_mul.mpr ⟨⟨a, hPY ha⟩, ha, ⟨b, hEY hb⟩, hb, Subtype.ext ?_⟩
    exact hab.symm
  have hD' : (N : Set ↥Y) * ((D.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨p, hp, d, hd, hpd⟩ := hXPD y (hYX y.2)
    have hdY : d ∈ Y := by
      have : d = p⁻¹ * y := by rw [hpd]; group
      rw [this]
      exact Y.mul_mem (Y.inv_mem (hPY hp)) y.2
    refine Set.mem_mul.mpr ⟨⟨p, hPY hp⟩, hp, ⟨d, hdY⟩, hd, Subtype.ext ?_⟩
    exact hpd.symm
  have hNE : N ⊓ E.subgroupOf Y = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have : (x : G) ∈ P ⊓ E := ⟨hx1, hx2⟩
    rw [hPE, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hND : N ⊓ D.subgroupOf Y = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have : (x : G) ∈ P ⊓ D := ⟨hx1, hx2⟩
    rw [hPD, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  obtain ⟨m, hm, hKeq⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy N hNsolv
    hcop hD' hE' hND hNE
  refine ⟨((m⁻¹ : ↥Y) : G), P.inv_mem hm, fun e he => ?_⟩
  have he' : (⟨e, hEY he⟩ : ↥Y) ∈ E.subgroupOf Y := he
  rw [hKeq] at he'
  obtain ⟨x, hx, hxe⟩ := he'
  refine ⟨x, hx, ?_⟩
  have := congrArg Subtype.val hxe
  simpa [MulAut.conj_apply] using this

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem image_K_inf_M {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {φ : ↥(oTwoUpper H) →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hφs : Function.Surjective φ) (hφker : ∀ y, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 (oTwoUpper H)) :
    ((Subgroup.normalizer (L : Set G)).subgroupOf (oTwoUpper H)).map φ ≠ ⊤ ∧
      2 ^ n ∣ Nat.card (((Subgroup.normalizer (L : Set G)).subgroupOf (oTwoUpper H)).map φ) := by
  have hT := s.sylow
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := s.hyp.normal
  refine ⟨fun hBt => s.h31.hstar.2.1 ((oTwoUpper_sup_eq hT).ge.trans (sup_le (le_of_map_eq_top
    (fun y hy => hTM (s.pCoreOf_K_le_T ((hφker y).mp hy))) hBt) hTM)), ?_⟩
  have hodd' : ¬ 2 ∣ ((Subgroup.normalizer (L : Set G)).subgroupOf (oTwoUpper H)).index := by
    have h2 : ((Subgroup.normalizer (L : Set G)).subgroupOf (oTwoUpper H)).index ∣
        ((T ⊓ oTwoUpper H).subgroupOf (oTwoUpper H)).index :=
      Subgroup.relIndex_dvd_of_le_left (oTwoUpper H) (inf_le_left.trans hTM)
    have h3 := F7.isSylowTwoOf_odd_relIndex (F7.isSylowTwoOf_inf_normal hT hKH
      (s.h31.hstar.1.1.trans (le_normalizer_oTwoUpper H)))
    exact fun h => h3 (h.trans h2)
  exact two_pow_dvd_card_map hF hφs hodd'

theorem pow_eq_one_of_odd (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) (hB : FactSL2Borel)
    {x : G} (hx : x ∈ H ⊓ Subgroup.normalizer (L : Set G)) (hodd : Odd (orderOf x)) :
    x ^ (2 ^ n - 1) = 1 := by
  obtain ⟨F, _, _, hF, φ, hφs, hφker⟩ := s.exists_phi h1135 h1136
  have hxK : x ∈ oTwoUpper H := mem_oTwoUpper_of_odd hx.1 hodd
  obtain ⟨hBtop, hdvd⟩ := s.image_K_inf_M hF hφs hφker
  have hxB : φ ⟨x, hxK⟩ ∈ ((Subgroup.normalizer (L : Set G)).subgroupOf (oTwoUpper H)).map φ :=
    Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hx.2)
  have hodd2 : Odd (orderOf (φ ⟨x, hxK⟩)) :=
    hodd.of_dvd_nat ((orderOf_map_dvd φ _).trans (by rw [Subgroup.orderOf_mk]))
  have hpow := hB F n s.two_le hF _ hBtop hdvd _ hxB hodd2
  rw [← map_pow] at hpow
  have hmem : x ^ (2 ^ n - 1) ∈ pCoreOf 2 (oTwoUpper H) := by
    have := (hφker _).mp hpow
    simpa using this
  exact pow_eq_one_of_mem_pGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hodd hmem

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
