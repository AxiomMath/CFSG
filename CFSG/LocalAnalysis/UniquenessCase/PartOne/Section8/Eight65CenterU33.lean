module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.U33SmallIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SylowInfCenter
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25OddA
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Conj
public import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterLie

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup

private theorem card_inf_centralizer_Psub :
    Nat.card ↥(CFSG.GH74.KGroups.U33.QP.originalSubgroup ⊓
      Subgroup.centralizer
        (CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub :
          Set (Equiv.Perm (Fin 28)))) = 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Subgroup (Equiv.Perm (Fin 28)) :=
    Subgroup.closure {CFSG.GH74.KGroups.U33.pa, CFSG.GH74.KGroups.U33.pb}
  let A : Subgroup (Equiv.Perm (Fin 28)) :=
    Subgroup.closure {CFSG.GH74.KGroups.U33.pa, CFSG.GH74.KGroups.U33.pb,
      CFSG.GH74.KGroups.U33.sg0}
  let Q : Subgroup (Equiv.Perm (Fin 28)) := CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub
  have hPdef : P = CFSG.GH74.KGroups.U33.QP.originalSubgroup :=
    CFSG.GH74.KGroups.U33.QP_closure.symm
  have hPA : P ≤ A := CFSG.GH74.KGroups.U33.P_le_A
  have hQleP : Q ≤ P := by
    rw [hPdef]
    intro g hg
    exact (CFSG.SignalizerFunctorTheorem.NonLocalExc.mem_Psub.mp hg).1
  have hPcard : Nat.card P = 6048 := by
    rw [hPdef]
    rw [CFSG.GH74.KGroups.card_group CFSG.GH74.KGroups.U33.QP
      CFSG.GH74.KGroups.U33.QP_ok]
    exact (CFSG.GH74.KGroups.U33.QP_valid).2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hE9pu, hE9pt2, -, -, -, hCpx1, hCpx2, -, -⟩ :=
    Certificates.certificate5133
  have hQcard : Nat.card Q = 27 :=
    CFSG.SignalizerFunctorTheorem.NonLocalExc.card_Psub
  have hQexp : ∀ q ∈ Q, q ^ 3 = 1 := fun q hq =>
    (CFSG.SignalizerFunctorTheorem.NonLocalExc.mem_Psub.mp hq).2.2
  have hQnonab : ¬ IsMulCommutative ↥Q := by
    intro hcomm
    obtain ⟨-, -, -, z, -, -, hz1, ⟨x, hxB, y, hyB, hx3, hy3, hxyz⟩, -⟩ :=
      Certificates.certificate14953
    have hxQ : x ∈ Q :=
      CFSG.SignalizerFunctorTheorem.NonLocalExc.mem_Psub_iff_Bsub.mpr ⟨hxB, hx3⟩
    have hyQ : y ∈ Q :=
      CFSG.SignalizerFunctorTheorem.NonLocalExc.mem_Psub_iff_Bsub.mpr ⟨hyB, hy3⟩
    have hcommxy : x * y = y * x :=
      congrArg Subtype.val (mul_comm' (⟨x, hxQ⟩ : ↥Q) ⟨y, hyQ⟩)
    have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by rw [hcommxy]; group
    exact hz1 (hxyz.trans h1)
  haveI : Nontrivial ↥Q :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hQcard]; norm_num)
  have hQgroup : IsPGroup 3 ↥Q := IsPGroup.of_card (n := 3) (by rw [hQcard]; norm_num)
  have hxexists : ∃ x : ↥Q, x ∉ Subgroup.center ↥Q := by
    by_contra h
    push Not at h
    refine hQnonab (Subgroup.center_eq_top_iff.mp ?_)
    rw [eq_top_iff]
    intro x _
    exact h x
  obtain ⟨xQ, hxQnc⟩ := hxexists
  have hxQ : (xQ : Equiv.Perm (Fin 28)) ∈ Q := xQ.2
  have hx1Q : xQ ≠ 1 := fun h => hxQnc (h.symm ▸ Subgroup.one_mem _)
  have hx1 : (xQ : Equiv.Perm (Fin 28)) ≠ 1 := fun h => hx1Q (Subtype.ext h)
  have hx3 : (xQ : Equiv.Perm (Fin 28)) ^ 3 = 1 := hQexp _ hxQ
  have hxQ3 : xQ ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  haveI hnt : Nontrivial ↥(Subgroup.center ↥Q) := hQgroup.center_nontrivial
  obtain ⟨zC, hzC1⟩ := exists_ne (1 : ↥(Subgroup.center ↥Q))
  let zQ : ↥Q := zC.1
  have hzcenter : zQ ∈ Subgroup.center ↥Q := zC.2
  have hzQ : (zQ : Equiv.Perm (Fin 28)) ∈ Q := zQ.2
  have hz1Q : zQ ≠ 1 := fun h => hzC1 (Subtype.ext h)
  have hz1 : (zQ : Equiv.Perm (Fin 28)) ≠ 1 := fun h => hz1Q (Subtype.ext h)
  have hz3 : (zQ : Equiv.Perm (Fin 28)) ^ 3 = 1 := hQexp _ hzQ
  have hzx : zQ ≠ xQ := fun h => hxQnc (h ▸ hzcenter)
  have hzx2 : zQ ≠ xQ ^ 2 := by
    intro h
    have hmem : xQ ^ 2 ∈ Subgroup.center ↥Q := h ▸ hzcenter
    have hinv : (xQ ^ 2)⁻¹ ∈ Subgroup.center ↥Q := (Subgroup.center ↥Q).inv_mem hmem
    have hmul : xQ ^ 2 * xQ = 1 := by rw [← pow_succ, hxQ3]
    have hxeq : xQ = (xQ ^ 2)⁻¹ := (inv_eq_of_mul_eq_one_right hmul).symm
    exact hxQnc (by rw [hxeq]; exact hinv)
  have hxz : (xQ : Equiv.Perm (Fin 28)) * (zQ : Equiv.Perm (Fin 28)) =
      (zQ : Equiv.Perm (Fin 28)) * (xQ : Equiv.Perm (Fin 28)) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcenter xQ)
  have hZne_top : Subgroup.center ↥Q ≠ ⊤ := fun h =>
    hQnonab (Subgroup.center_eq_top_iff.mp h)
  have hZne_bot : Subgroup.center ↥Q ≠ ⊥ := by
    intro hbot
    have hnt : Nontrivial ↥(Subgroup.center ↥Q) := hQgroup.center_nontrivial
    rw [Subgroup.nontrivial_iff_ne_bot] at hnt
    exact hnt hbot
  have hZdvd : Nat.card ↥(Subgroup.center ↥Q) ∣ 27 := by
    have := Subgroup.card_subgroup_dvd_card (Subgroup.center ↥Q)
    rwa [hQcard] at this
  have hZcard : Nat.card ↥(Subgroup.center ↥Q) = 3 := by
    have hZdvd' : Nat.card ↥(Subgroup.center ↥Q) ∣ 3 ^ 3 := by
      rwa [show (27 : ℕ) = 3 ^ 3 by norm_num] at hZdvd
    obtain ⟨k, hk, hZeq⟩ :=
      (Nat.dvd_prime_pow (p := 3) (m := 3) Nat.prime_three).mp hZdvd'
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk3 with rfl | rfl | rfl | rfl
    · exfalso
      have h1 : Nat.card ↥(Subgroup.center ↥Q) = 1 := by rw [hZeq]; norm_num
      exact hZne_bot ((Subgroup.card_eq_one (H := Subgroup.center ↥Q)).mp h1)
    · simpa using hZeq
    · exfalso
      have hquot : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 3 := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
          (s := Subgroup.center ↥Q) (α := ↥Q)
        rw [hQcard, hZeq] at h
        norm_num at h
        refine mul_right_cancel₀ (by norm_num : (9 : ℕ) ≠ 0) ?_
        rw [show (3 * 9 : ℕ) = 27 by norm_num]
        simpa using h.symm
      haveI : IsCyclic (↥Q ⧸ Subgroup.center ↥Q) := isCyclic_of_prime_card hquot
      exact hQnonab (isMulCommutative_of_isCyclic_quotient_center_self ↥Q)
    · exfalso
      apply hZne_top
      exact Subgroup.eq_of_le_of_card_ge le_top
        (by rw [Subgroup.card_top, hQcard, hZeq]; norm_num)
  let C : Subgroup (Equiv.Perm (Fin 28)) :=
    P ⊓ Subgroup.centralizer (Q : Set (Equiv.Perm (Fin 28)))
  have hCeq : C = (Subgroup.center ↥Q).map Q.subtype := by
    apply le_antisymm
    · intro g hgC
      have hgC' : g ∈ C := hgC
      obtain ⟨hgP, hgcent⟩ := hgC
      have hgA : g ∈ A := hPA hgP
      have hgord : orderOf g ∣ 6048 := by
        have := Subgroup.orderOf_dvd_natCard P hgP
        rwa [hPcard] at this
      have hgord' : orderOf g ∣ 2 ^ 5 * 3 ^ 3 * 7 := by
        rwa [show (6048 : ℕ) = 2 ^ 5 * 3 ^ 3 * 7 by norm_num] at hgord
      have hodd : ¬ 2 ∣ orderOf g := by
        intro h2dvd
        obtain ⟨h2el, h2ord⟩ := exists_prime_orderOf_dvd_card'
          (G := ↥(Subgroup.zpowers g)) 2 (by rw [Nat.card_zpowers]; exact h2dvd)
        have h2mem : (h2el : Equiv.Perm (Fin 28)) ∈ C :=
          (Subgroup.zpowers_le.mpr hgC') h2el.2
        have h2ord' : orderOf (h2el : Equiv.Perm (Fin 28)) = 2 := by
          rw [Subgroup.orderOf_coe]; exact h2ord
        have h2A : (h2el : Equiv.Perm (Fin 28)) ∈ A := hPA h2mem.1
        obtain ⟨r, hr, a, ha, haconj⟩ :=
          CFSG.GH74.KGroups.U33.invol_A (h2el : Equiv.Perm (Fin 28)) h2A h2ord'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have hE9r : CFSG.GH74.KGroups.E9At A r := by
          rcases hr with rfl | rfl
          · exact hE9pu
          · exact hE9pt2
        have hE9h : CFSG.GH74.KGroups.E9At A (h2el : Equiv.Perm (Fin 28)) := by
          rw [haconj]
          exact CFSG.GH74.KGroups.e9At_conj ha hE9r
        have hxh : (xQ : Equiv.Perm (Fin 28)) * (h2el : Equiv.Perm (Fin 28)) =
            (h2el : Equiv.Perm (Fin 28)) * (xQ : Equiv.Perm (Fin 28)) :=
          Subgroup.mem_centralizer_iff.mp h2mem.2 _ hxQ
        have hzh : (zQ : Equiv.Perm (Fin 28)) * (h2el : Equiv.Perm (Fin 28)) =
            (h2el : Equiv.Perm (Fin 28)) * (zQ : Equiv.Perm (Fin 28)) :=
          Subgroup.mem_centralizer_iff.mp h2mem.2 _ hzQ
        have key := hE9h (xQ : Equiv.Perm (Fin 28)) (hPA (hQleP hxQ)) hx1
          (zQ : Equiv.Perm (Fin 28)) (hPA (hQleP hzQ)) hx3 hz3 hxz hxh hzh
        rcases key with h1 | h1 | h1
        · exact hz1 h1
        · exact hzx (Subtype.ext h1)
        · exact hzx2 (Subtype.ext (by rw [Subgroup.coe_pow]; exact h1))
      have hnot7 : ¬ 7 ∣ orderOf g := by
        intro h7dvd
        obtain ⟨h7el, h7ord⟩ := exists_prime_orderOf_dvd_card'
          (G := ↥(Subgroup.zpowers g)) 7 (by rw [Nat.card_zpowers]; exact h7dvd)
        have h7mem : (h7el : Equiv.Perm (Fin 28)) ∈ C :=
          (Subgroup.zpowers_le.mpr hgC') h7el.2
        have h7ord' : orderOf (h7el : Equiv.Perm (Fin 28)) = 7 := by
          rw [Subgroup.orderOf_coe]; exact h7ord
        have h7x : (h7el : Equiv.Perm (Fin 28)) ∈
            Subgroup.centralizer ({(xQ : Equiv.Perm (Fin 28))} :
              Set (Equiv.Perm (Fin 28))) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp h7mem.2 _ hxQ).symm
        have hdvdH : 7 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer
            ({(xQ : Equiv.Perm (Fin 28))} : Set (Equiv.Perm (Fin 28)))) := by
          have h := Subgroup.orderOf_dvd_natCard
            (P ⊓ Subgroup.centralizer
              ({(xQ : Equiv.Perm (Fin 28))} : Set (Equiv.Perm (Fin 28))))
            (x := (h7el : Equiv.Perm (Fin 28))) ⟨h7mem.1, h7x⟩
          rwa [h7ord'] at h
        have hle : P ⊓ Subgroup.centralizer
            ({(xQ : Equiv.Perm (Fin 28))} : Set (Equiv.Perm (Fin 28))) ≤
            A ⊓ Subgroup.centralizer
              ({(xQ : Equiv.Perm (Fin 28))} : Set (Equiv.Perm (Fin 28))) :=
          inf_le_inf hPA le_rfl
        have hdvdA : 7 ∣ Nat.card ↥(A ⊓ Subgroup.centralizer
            ({(xQ : Equiv.Perm (Fin 28))} : Set (Equiv.Perm (Fin 28)))) :=
          hdvdH.trans (Subgroup.card_dvd_of_le hle)
        rw [CFSG.GH74.KGroups.card_inf_centralizer_eq] at hdvdA
        have hxord3 : orderOf (xQ : Equiv.Perm (Fin 28)) = 3 :=
          orderOf_eq_prime hx3 hx1
        have hcentax : CFSG.GH74.KGroups.centCard A (xQ : Equiv.Perm (Fin 28)) = 216 ∨
            CFSG.GH74.KGroups.centCard A (xQ : Equiv.Perm (Fin 28)) = 18 := by
          obtain ⟨r, hr, a, ha, haconj⟩ :=
            CFSG.GH74.KGroups.U33.three_A (xQ : Equiv.Perm (Fin 28))
              (hPA (hQleP hxQ)) hxord3
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · left
            rw [haconj, CFSG.GH74.KGroups.centCard_conj A a
              CFSG.GH74.KGroups.U33.px1
              (CFSG.GH74.KGroups.normal_iff_of_mem ha), hCpx1]
          · right
            rw [haconj, CFSG.GH74.KGroups.centCard_conj A a
              CFSG.GH74.KGroups.U33.px2
              (CFSG.GH74.KGroups.normal_iff_of_mem ha), hCpx2]
        rcases hcentax with hc | hc <;> rw [hc] at hdvdA <;> norm_num at hdvdA
      have hunique : ∀ {d : ℕ}, Nat.Prime d → d ∣ orderOf g → d = 3 := by
        intro d hd hdn
        have hd6048 : d ∣ (2 ^ 5 * 3 ^ 3) * 7 := hdn.trans hgord'
        rcases hd.dvd_mul.mp hd6048 with h | h7
        · rcases hd.dvd_mul.mp h with h2 | h3
          · have h2' : d = 2 :=
              (Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp (hd.dvd_of_dvd_pow h2)
            exact absurd (h2' ▸ hdn) hodd
          · exact (Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp (hd.dvd_of_dvd_pow h3)
        · have h7' : d = 7 := (Nat.prime_dvd_prime_iff_eq hd Nat.prime_seven).mp h7
          exact absurd (h7' ▸ hdn) hnot7
      have hpow3 : ∃ j, orderOf g = 3 ^ j := by
        have hpos : orderOf g ≠ 0 :=
          (Nat.pos_of_dvd_of_pos hgord (by norm_num)).ne'
        exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hpos
          (fun hd hdn => hunique hd hdn)⟩
      obtain ⟨j, hj⟩ := hpow3
      have hK3 : IsPGroup 3 ↥(Subgroup.zpowers g) :=
        IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
      have hKnorm : Subgroup.zpowers g ≤
          Subgroup.normalizer (Q : Set (Equiv.Perm (Fin 28))) := by
        rw [Subgroup.zpowers_le]
        exact Subgroup.centralizer_le_normalizer (Q : Set (Equiv.Perm (Fin 28))) hgcent
      have hKQ3 : IsPGroup 3
          (Subgroup.zpowers g ⊔ Q : Subgroup (Equiv.Perm (Fin 28))) :=
        hK3.to_sup_of_normal_right' hQgroup hKnorm
      obtain ⟨n, hn⟩ := hKQ3.exists_card_eq
      have hsup_le : (Subgroup.zpowers g ⊔ Q : Subgroup (Equiv.Perm (Fin 28))) ≤ P :=
        sup_le (Subgroup.zpowers_le.mpr hgP) hQleP
      have hdvd : Nat.card ↥(Subgroup.zpowers g ⊔ Q :
          Subgroup (Equiv.Perm (Fin 28))) ∣ 6048 := by
        have := Subgroup.card_dvd_of_le hsup_le
        rwa [hPcard] at this
      have hn3 : n ≤ 3 := by
        by_contra hn3
        push Not at hn3
        have hdvd' : 3 ^ n ∣ 6048 := by rwa [hn] at hdvd
        have h4 : 3 ^ 4 ∣ 3 ^ n := Nat.pow_dvd_pow 3 (by omega)
        exact (by norm_num : ¬ (3 ^ 4 : ℕ) ∣ 6048) (h4.trans hdvd')
      have hsupcard : Nat.card ↥(Subgroup.zpowers g ⊔ Q :
          Subgroup (Equiv.Perm (Fin 28))) = 27 := by
        have hle : Nat.card ↥(Subgroup.zpowers g ⊔ Q :
            Subgroup (Equiv.Perm (Fin 28))) ≤ 27 := by
          rw [hn]
          calc 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
            _ = 27 := by norm_num
        have hge : 27 ≤ Nat.card ↥(Subgroup.zpowers g ⊔ Q :
            Subgroup (Equiv.Perm (Fin 28))) := by
          rw [← hQcard]
          exact Subgroup.card_le_of_le (le_sup_right :
            Q ≤ Subgroup.zpowers g ⊔ Q)
        omega
      have hQeq : Q = (Subgroup.zpowers g ⊔ Q :
          Subgroup (Equiv.Perm (Fin 28))) :=
        Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hsupcard, hQcard])
      have hgQ : g ∈ Q := by
        have hgmem : g ∈ (Subgroup.zpowers g ⊔ Q :
            Subgroup (Equiv.Perm (Fin 28))) :=
          Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
        rwa [← hQeq] at hgmem
      refine Subgroup.mem_map.mpr ⟨⟨g, hgQ⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgcent (y : Equiv.Perm (Fin 28)) y.2)
    · rintro g ⟨zQ, hzQmem, rfl⟩
      refine ⟨hQleP zQ.2, ?_⟩
      change Q.subtype zQ ∈
        (Subgroup.centralizer (Q : Set (Equiv.Perm (Fin 28))) :
          Set (Equiv.Perm (Fin 28)))
      refine (Subgroup.mem_centralizer_iff
        (s := (Q : Set (Equiv.Perm (Fin 28))))).mpr ?_
      intro y hy
      have h := Subgroup.mem_center_iff.mp hzQmem (⟨y, hy⟩ : ↥Q)
      exact congrArg Subtype.val h
  have hCcard : Nat.card ↥C = 3 := by
    rw [hCeq, Subgroup.card_map_of_injective Q.subtype_injective, hZcard]
  simpa [C, hPdef, Q] using hCcard

theorem u33_card_centralizer_sylow_three
    (Q : Sylow 3 ↥(CFSG.GH74.KGroups.U33.QP.originalSubgroup)) :
    Nat.card (Subgroup.centralizer
      ((Q : Subgroup ↥(CFSG.GH74.KGroups.U33.QP.originalSubgroup)) :
        Set ↥(CFSG.GH74.KGroups.U33.QP.originalSubgroup))) = 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Subgroup (Equiv.Perm (Fin 28)) := CFSG.GH74.KGroups.U33.QP.originalSubgroup
  have hPcard : Nat.card P = 6048 := by
    rw [show P = CFSG.GH74.KGroups.U33.QP.originalSubgroup from rfl]
    rw [CFSG.GH74.KGroups.card_group CFSG.GH74.KGroups.U33.QP
      CFSG.GH74.KGroups.U33.QP_ok]
    exact (CFSG.GH74.KGroups.U33.QP_valid).2
  have hPsub_le : CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub ≤ P := by
    intro g hg
    exact (CFSG.SignalizerFunctorTheorem.NonLocalExc.mem_Psub.mp hg).1
  let Qsub : Subgroup ↥P := CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub.subgroupOf P
  have hQsub_card : Nat.card Qsub = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPsub_le).toEquiv]
    exact CFSG.SignalizerFunctorTheorem.NonLocalExc.card_Psub
  have hQsub_p : IsPGroup 3 Qsub := IsPGroup.of_card (n := 3) (by rw [hQsub_card]; norm_num)
  haveI : Finite ↥Qsub := Nat.finite_of_card_ne_zero (by rw [hQsub_card]; norm_num)
  have hQsub_index : ¬ 3 ∣ Qsub.index := by
    rw [Subgroup.index_eq_card_div, hQsub_card, hPcard]
    norm_num
  let Q0 : Sylow 3 ↥P := hQsub_p.toSylow hQsub_index
  have hQ0_coe : (Q0 : Subgroup ↥P) = Qsub := rfl
  have hQ0_card : Nat.card (Subgroup.centralizer ((Q0 : Subgroup ↥P) : Set ↥P)) = 3 := by
    rw [hQ0_coe]
    have hbridge : (Subgroup.centralizer (Qsub : Set ↥P)).map P.subtype =
        P ⊓ Subgroup.centralizer (CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub :
          Set (Equiv.Perm (Fin 28))) := by
      have h := CFSG.LocalAnalysis.ComponentInitial.map_centralizer_subgroupOf
        (G := Equiv.Perm (Fin 28)) (P := P)
        (Q := CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub) hPsub_le
      rw [inf_comm] at h
      simpa [Qsub] using h
    calc Nat.card (Subgroup.centralizer (Qsub : Set ↥P))
        = Nat.card ((Subgroup.centralizer (Qsub : Set ↥P)).map P.subtype) :=
          (Subgroup.card_map_of_injective P.subtype_injective).symm
      _ = Nat.card ↥(P ⊓ Subgroup.centralizer
            (CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub :
              Set (Equiv.Perm (Fin 28)))) := by rw [hbridge]
      _ = 3 := card_inf_centralizer_Psub
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥P) Q0 Q
  have hQconj : (Q : Subgroup ↥P) = (Q0 : Subgroup ↥P).map
      (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  calc Nat.card (Subgroup.centralizer ((Q : Subgroup ↥P) : Set ↥P))
      = Nat.card (Subgroup.centralizer
          (((Q0 : Subgroup ↥P).map (MulAut.conj g).toMonoidHom :
            Subgroup ↥P) : Set ↥P)) := by rw [hQconj]
    _ = Nat.card (Subgroup.centralizer ((Q0 : Subgroup ↥P) : Set ↥P)) := by
        have hconj := CFSG.GF2Type.Smith1979W3.Cert690.centralizer_conjSub
          (Q0 : Subgroup ↥P) g
        change Nat.card (Subgroup.centralizer
          (CFSG.GF2Type.Smith1979W3.Cert690.conjSub (Q0 : Subgroup ↥P) g :
            Set ↥P)) = Nat.card (Subgroup.centralizer ((Q0 : Subgroup ↥P) : Set ↥P))
        rw [hconj]
        rw [CFSG.GF2Type.Smith1979W3.Cert690.conjSub,
          Subgroup.card_map_of_injective (MulAut.conj g).injective]
    _ = 3 := hQ0_card

theorem u33_centralizer_sylow_three
    {X : Type} [Group X]
    (hX : CFSG.Blueprint.LieModel X .PSU 3 3 1)
    (P : Sylow 3 X) :
    Nat.card (Subgroup.centralizer ((P : Subgroup X) : Set X)) = 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hX
  haveI : Finite X := Finite.of_equiv _ e.toEquiv.symm
  let P' : Sylow 3 ↥(CFSG.GH74.KGroups.U33.QP.originalSubgroup) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P
  have hP' : (P' : Subgroup ↥(CFSG.GH74.KGroups.U33.QP.originalSubgroup)) =
      (P : Subgroup X).map e.toMonoidHom := by
    simp [P']
  have hcent : Nat.card (Subgroup.centralizer
      ((P' : Subgroup ↥(CFSG.GH74.KGroups.U33.QP.originalSubgroup)) :
        Set ↥(CFSG.GH74.KGroups.U33.QP.originalSubgroup))) =
      Nat.card (Subgroup.centralizer ((P : Subgroup X) : Set X)) := by
    have himg : ((P' : Subgroup ↥(CFSG.GH74.KGroups.U33.QP.originalSubgroup)) :
        Set ↥(CFSG.GH74.KGroups.U33.QP.originalSubgroup)) =
        e '' ((P : Subgroup X) : Set X) := by
      rw [hP']
      rfl
    calc Nat.card (Subgroup.centralizer
          ((P' : Subgroup ↥(CFSG.GH74.KGroups.U33.QP.originalSubgroup)) :
            Set ↥(CFSG.GH74.KGroups.U33.QP.originalSubgroup)))
        = Nat.card (Subgroup.centralizer (e '' ((P : Subgroup X) : Set X))) := by
            rw [himg]
      _ = Nat.card ((Subgroup.centralizer ((P : Subgroup X) : Set X)).map
            e.toMonoidHom) := by
            rw [CFSG.GF2Type.Smith1979W3.Cert690.map_centralizer_mulEquiv]
      _ = Nat.card (Subgroup.centralizer ((P : Subgroup X) : Set X)) := by
            rw [Subgroup.card_map_of_injective e.injective]
  rw [← hcent]
  exact u33_card_centralizer_sylow_three P'

theorem u33_aut_centralizer_sylow_three
    {X : Type} [Group X]
    (hX : CFSG.Blueprint.LieModel X .PSU 3 3 1)
    {Q : Subgroup X}
    (hQext : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    (hQsyl : ∃ P : Sylow 3 X, (P : Subgroup X) = Q)
    {φ : MulAut X} (hφ3 : φ ^ 3 = 1) (hφQ : ∀ q ∈ Q, φ q = q) :
    ∃ g ∈ Q, φ = MulAut.conj g := by
  classical
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hX
  haveI : Finite X := Finite.of_equiv _ e.toEquiv.symm
  rcases eq_or_ne φ 1 with h1 | h1
  · refine ⟨1, Q.one_mem, ?_⟩
    rw [h1]
    exact (map_one (MulAut.conj : X →* MulAut X)).symm
  have hφord : orderOf φ = 3 := by
    have hdvd : orderOf φ ∣ 3 := orderOf_dvd_of_pow_eq_one hφ3
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  have hout : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.not_three_dvd_card_outer_of_lieModel_psu3
      hX
  have hinn : φ ∈ CFSG.Quasithin.H13.innAut X :=
    CFSG.Quasithin.H13.OddSyl.mem_innAut_of_not_dvd (S := X) (r := 3) (by norm_num) hφord hout
  obtain ⟨g, hg⟩ := hinn
  have hgconj : MulAut.conj g = φ := hg
  have hgC : g ∈ Subgroup.centralizer (Q : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h := hφQ q hq
    rw [← hgconj] at h
    rw [MulAut.conj_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hcard : Nat.card (Subgroup.centralizer (Q : Set X)) = 3 := by
    obtain ⟨P, rfl⟩ := hQsyl
    exact u33_centralizer_sylow_three hX P
  have hZle : (Subgroup.center ↥Q).map Q.subtype ≤
      Subgroup.centralizer (Q : Set X) := by
    rintro z ⟨z₀, hz₀, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h := Subgroup.mem_center_iff.mp hz₀ (⟨q, hq⟩ : ↥Q)
    have h2 : q * (z₀ : X) = (z₀ : X) * q := congrArg Subtype.val h
    simpa using h2
  have hZcard : Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3 :=
    center_card_three_of_isExtraspecialExpP hQext
  have hZeq : (Subgroup.center ↥Q).map Q.subtype = Subgroup.centralizer (Q : Set X) :=
    Subgroup.eq_of_le_of_card_ge hZle (by rw [hZcard, hcard])
  have hgZ : g ∈ (Subgroup.center ↥Q).map Q.subtype := hZeq ▸ hgC
  have hgQ : g ∈ Q := by
    obtain ⟨z, hz, hzg⟩ := hgZ
    rw [← hzg]
    exact z.2
  exact ⟨g, hgQ, hgconj.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
