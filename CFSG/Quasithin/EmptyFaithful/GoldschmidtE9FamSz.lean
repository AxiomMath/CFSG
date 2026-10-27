module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamDefs
public import CFSG.Quasithin.EmptyFaithful.T1521SSzW

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.E9.Sz

open CFSG.Open CFSG.QuasithinUnique CFSG.Goldschmidt.G3a CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem mem_of_relIndex_dvd_three {w : G} {H₀ : Subgroup G}
    (hidx : H₀.relIndex (Subgroup.zpowers w) ∣ 3) (h3 : ¬ 3 ∣ orderOf w) : w ∈ H₀ := by
  have h1 : H₀.relIndex (Subgroup.zpowers w) ∣ orderOf w := by
    have := Subgroup.relIndex_dvd_card H₀ (Subgroup.zpowers w)
    rwa [Nat.card_zpowers] at this
  have hcop : Nat.Coprime 3 (orderOf w) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have h2 : H₀.relIndex (Subgroup.zpowers w) = 1 :=
    Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hidx h1)
  exact Subgroup.relIndex_eq_one.mp h2 (Subgroup.mem_zpowers w)

theorem mem_normalizer_of_subgroupOf {L P : Subgroup G} (hP : P ≤ L) {w : ↥L}
    (hw : w ∈ Subgroup.normalizer ((P.subgroupOf L : Subgroup ↥L) : Set ↥L)) :
    (w : G) ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact (Subgroup.mem_normalizer_iff.mp hw ⟨x, hP hx⟩).mp hx
  · intro hx
    have hxL : x ∈ L := by
      have := L.mul_mem (L.inv_mem w.2) (L.mul_mem (hP hx) w.2)
      simpa [mul_assoc] using this
    exact (Subgroup.mem_normalizer_iff.mp hw ⟨x, hxL⟩).mpr hx

section Torus

variable [Finite G]

theorem exists_torus {L P : Subgroup G} (hL : SzComponent1521 L) (hP : IsSylowTwoOf P L) :
    ∃ z : G, z ∈ L ∧ z ∈ Subgroup.normalizer (P : Set G) ∧ Odd (orderOf z) ∧ ¬ 3 ∣ orderOf z ∧
      ∀ s ∈ P, (∀ y ∈ L, ⁅s, z⁆ * y = y * ⁅s, z⁆) → ∀ y ∈ L, s * y = y * s := by
  classical
  obtain ⟨e, he⟩ := hL.sz
  set Z := Subgroup.center ↥L with hZdef
  let π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let PS : Sylow 2 ↥L := A4.toSylow hP
  have hZP : Z ≤ (PS : Subgroup ↥L) := hL.center_two.le_sylow_of_normal PS
  let T : Sylow 2 (↥L ⧸ Z) := PS.mapSurjective hπ
  have hT : (T : Subgroup (↥L ⧸ Z)) = (PS : Subgroup ↥L).map π := Sylow.coe_mapSurjective hπ PS
  obtain ⟨hodde, -, D, hD, -, -, hDc⟩ := SBc2.exists_data he T
  obtain ⟨d, hdD, hgen⟩ := hD.exists_gen
  obtain ⟨l, rfl⟩ := hπ d
  have hodd : Odd (orderOf (l : ↥L ⧸ Z)) :=
    hD.odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard D hdD)
  obtain ⟨k, hk, hkπ⟩ := SzQuot1521.exists_odd_pow_lift hL.center_two hodd
  set z' : ↥L := l ^ k with hz'
  have hπz : π z' = π l := hkπ
  refine ⟨(z' : G), z'.2, ?_, ?_, ?_, ?_⟩
  · refine mem_normalizer_of_subgroupOf hP.1 ?_
    refine SzQuot1521.mem_normalizer_of_map_mem hZP ?_
    rw [show ((z' : ↥L) : ↥L ⧸ Z) = π l from hkπ]
    have h1 := hD.le hdD
    rw [hT] at h1
    exact h1
  · rw [Subgroup.orderOf_coe]
    exact hk
  · intro h3
    rw [Subgroup.orderOf_coe] at h3
    have hd1 : π z' ^ Nat.card D = 1 := by
      rw [hπz]
      exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard D hdD)
    have hmemZ : z' ^ Nat.card D ∈ Z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hd1
    obtain ⟨j, hj⟩ := hL.center_two ⟨z' ^ Nat.card D, hmemZ⟩
    have hj' : (z' ^ Nat.card D) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hdvd : orderOf z' ∣ Nat.card D * 2 ^ j :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hj')
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h3.trans hdvd) with h | h
    · rw [hDc] at h
      have h2 := SBc2.two_pow_mod_three hodde
      generalize 2 ^ e = x at h h2
      omega
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
  · intro s hs hcomm y hy
    set s' : ↥L := ⟨s, hP.1 hs⟩ with hs'
    have hπsT : π s' ∈ (T : Subgroup (↥L ⧸ Z)) := by
      rw [hT]
      exact ⟨s', hs, rfl⟩
    have hc : ⁅s', z'⁆ ∈ Z := by
      refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
      have := hcomm g g.2
      simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] at this ⊢
      exact this.symm
    have h1 : π ⁅s', z'⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hc
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hπz] at h1
    have h3 : π s' = 1 := hD.eq_one_of_commute_gen hgen hπsT h1.symm
    have h4 : s' ∈ Z := (QuotientGroup.eq_one_iff s').mp h3
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h4 ⟨y, hy⟩).symm

end Torus

end CFSG.Quasithin.E9.Sz

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nrmE9_Sz (h37 : A37ForSQTK) (h38 : A38ForSQTK) {X S L : Subgroup G} (hStd : Std1521 X S L)
    (hc : IsComponentOf L X) (hZ : IsPGroup 2 ↥(Subgroup.center ↥L))
    (hty : (∃ e : ℕ, IsSz e ↥L) ∨ IsSz 3 (↥L ⧸ CFSG.pCore 2 ↥L)) : NrmE9 S L := by
  have hL : SzComponent1521 L := SzComponent1521.of_cases hc.2.2 hZ hty
  have hS : ∀ m ∈ S, ∃ k : ℕ, m ^ 2 ^ k = 1 := by
    intro m hm
    obtain ⟨k, hk⟩ := hStd.sylow.2.1 ⟨m, hm⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have horb := a3Orbits_of_a37_a38 (G := G) h37 h38 X S L hStd.sqtk hStd.sylow hStd.comp
  obtain ⟨z, hzL, hzN, hzodd, hz3, hzkey⟩ := Sz.exists_torus hL hStd.sylowL
  have hzB : z ∈ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := ⟨hzL, hzN⟩
  rcases horb.2 with hnorm | ⟨t, htS, htN, hpair, -, hint, -⟩
  · have hJ : thompsonJ S ≤ innerPart1521 S L := by
      refine (thompsonJ_le_self151 S).trans fun x hx => ?_
      obtain ⟨l, hl, c, hc', rfl⟩ := hL.exists_mul hStd.sylowL hS hx (hnorm x hx)
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hc')
    refine nrmE9_of_inner hJ (H := Subgroup.zpowers z) ?_ ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact hzB
    · rw [Nat.card_zpowers]
      exact hzodd
    · intro H₀ _ hidx
      have hzH₀ : z ∈ H₀ := Sz.mem_of_relIndex_dvd_three hidx hz3
      refine ⟨fun v hvS hvN _ hvH l hl => ?_, fun x hx hxH => ?_⟩
      · obtain ⟨s, hs, c, hc', rfl⟩ := hL.exists_mul hStd.sylowL hS hvS hvN
        have hcz : z * c = c * z := Subgroup.mem_centralizer_iff.mp hc'.2 z hzL
        have hsz : s * z = z * s := by
          have h1 : (s * z) * c = (z * s) * c :=
            calc s * z * c = s * (z * c) := by rw [mul_assoc]
              _ = s * (c * z) := by rw [hcz]
              _ = s * c * z := by rw [mul_assoc]
              _ = z * (s * c) := hvH z hzH₀
              _ = z * s * c := by rw [mul_assoc]
          exact mul_right_cancel h1
        have h2 : ⁅s, z⁆ = 1 := by rw [commutatorElement_def, hsz]; group
        have hscent := hzkey s hs (fun y _ => by rw [h2, one_mul, mul_one])
        have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc'.2 l hl
        calc s * c * l = s * (c * l) := by rw [mul_assoc]
          _ = s * (l * c) := by rw [hcl]
          _ = s * l * c := by rw [mul_assoc]
          _ = l * s * c := by rw [hscent l hl]
          _ = l * (s * c) := by rw [mul_assoc]
      · have h2 : ⁅x, z⁆ = 1 := by rw [commutatorElement_def, hxH z hzH₀]; group
        have hxc := hzkey x hx.1 (fun y _ => by rw [h2, one_mul, mul_one])
        exact ⟨hx.1.2, Subgroup.mem_centralizer_iff.mpr fun y hy => (hxc y hy).symm⟩
  · have hW : WreathData1521 X S L t :=
      ⟨le_of_mem_cComp hStd.comp, htS, hStd.sylow.1 htS, htN, horb.1, hpair, hint⟩
    have hz'L' : t * z * t⁻¹ ∈ conjByElt t L := WreathData1521.conj_mem_conjByElt' hzL
    have hcomm : z * (t * z * t⁻¹) = (t * z * t⁻¹) * z := hW.commute hL hzL hz'L'
    obtain ⟨w, hw⟩ : ∃ w : G, w = z * (t * z * t⁻¹) := ⟨_, rfl⟩
    have hwpow : w ^ orderOf z = 1 := by
      rw [hw, Commute.mul_pow hcomm, conj_pow, pow_orderOf_eq_one]
      simp
    have hwdvd : orderOf w ∣ orderOf z := orderOf_dvd_of_pow_eq_one hwpow
    have hwodd : Odd (orderOf w) := hzodd.of_dvd_nat hwdvd
    have hw3 : ¬ 3 ∣ orderOf w := fun h => hz3 (h.trans hwdvd)
    refine ⟨Subgroup.zpowers w, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.zpowers_le, hw]
      refine Subgroup.mul_mem _ (le_conjJoin hzB) ?_
      exact Subgroup.mem_iSup_of_mem (⟨t, htS⟩ : S) ⟨z, hzB, by simp [MulAut.conj_apply]⟩
    · refine le_trans ?_ (normalizer_le_normalizer_thompsonJ S)
      rw [Subgroup.zpowers_le, hw]
      exact hW.diag_mem_normalizer hL hStd.sylowL hS hzB
    · rw [Nat.card_zpowers]
      exact hwodd
    · intro H₀ _ hidx
      have hwH₀ : w ∈ H₀ := Sz.mem_of_relIndex_dvd_three hidx hw3
      refine ⟨fun v hvS hvN _ hvH l hl => ?_, fun x hx hxH => ?_⟩
      · obtain ⟨s, hs, c, hc', rfl⟩ := hL.exists_mul hStd.sylowL hS hvS hvN
        have hvL' : s * c ∈ Subgroup.normalizer ((conjByElt t L : Subgroup G) : Set G) :=
          hW.normalizer_conj hvS hvN
        have hAL : s * c * z * (s * c)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hvN z).mp hzL
        have hBL' : s * c * (t * z * t⁻¹) * (s * c)⁻¹ ∈ conjByElt t L :=
          (Subgroup.mem_normalizer_iff.mp hvL' _).mp hz'L'
        have hAB : (s * c * z * (s * c)⁻¹) * (s * c * (t * z * t⁻¹) * (s * c)⁻¹) =
            z * (t * z * t⁻¹) := by
          have h1 := hvH w hwH₀
          rw [hw] at h1
          calc (s * c * z * (s * c)⁻¹) * (s * c * (t * z * t⁻¹) * (s * c)⁻¹)
              = (s * c) * (z * (t * z * t⁻¹)) * (s * c)⁻¹ := by group
            _ = z * (t * z * t⁻¹) := by rw [h1]; group
        obtain ⟨ζ, hζ⟩ : ∃ ζ : G, ζ = z⁻¹ * (s * c * z * (s * c)⁻¹) := ⟨_, rfl⟩
        have hζL' : ζ ∈ conjByElt t L := by
          have e : ζ = (t * z * t⁻¹) * (s * c * (t * z * t⁻¹) * (s * c)⁻¹)⁻¹ := by
            rw [hζ, ← mul_inv_eq_of_eq_mul hAB.symm]
            group
          rw [e]
          exact (conjByElt t L).mul_mem hz'L' ((conjByElt t L).inv_mem hBL')
        have hcent := hW.inf_central hL ζ ⟨by rw [hζ]; exact L.mul_mem (L.inv_mem hzL) hAL, hζL'⟩
        have hcz : c * z = z * c := (Subgroup.mem_centralizer_iff.mp hc'.2 z hzL).symm
        have hA : s * c * z * (s * c)⁻¹ = s * z * s⁻¹ :=
          calc s * c * z * (s * c)⁻¹ = s * (c * z) * c⁻¹ * s⁻¹ := by group
            _ = s * (z * c) * c⁻¹ * s⁻¹ := by rw [hcz]
            _ = s * z * s⁻¹ := by group
        have hAζ : s * z * s⁻¹ = z * ζ := by rw [hζ, ← hA]; group
        have hcommζ : ⁅s, z⁆ = ζ := by
          rw [commutatorElement_def, hAζ, ← hcent z hzL]
          group
        have hscent := hzkey s hs (fun y hy => by rw [hcommζ]; exact hcent y hy)
        have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc'.2 l hl
        calc s * c * l = s * (c * l) := by rw [mul_assoc]
          _ = s * (l * c) := by rw [hcl]
          _ = s * l * c := by rw [mul_assoc]
          _ = l * s * c := by rw [hscent l hl]
          _ = l * (s * c) := by rw [mul_assoc]
      · have hxw : x * w = w * x := hxH w hwH₀
        rw [hw] at hxw
        have hxz' : x * (t * z * t⁻¹) = (t * z * t⁻¹) * x := hW.commute hL hx.1.2 hz'L'
        have hxz : x * z = z * x := by
          have h1 : (x * z) * (t * z * t⁻¹) = (z * x) * (t * z * t⁻¹) :=
            calc x * z * (t * z * t⁻¹) = x * (z * (t * z * t⁻¹)) := by rw [mul_assoc]
              _ = (z * (t * z * t⁻¹)) * x := hxw
              _ = z * ((t * z * t⁻¹) * x) := by rw [mul_assoc]
              _ = z * (x * (t * z * t⁻¹)) := by rw [hxz']
              _ = z * x * (t * z * t⁻¹) := (mul_assoc z x _).symm
          exact mul_right_cancel h1
        have h2 : ⁅x, z⁆ = 1 := by rw [commutatorElement_def, hxz]; group
        have hxc := hzkey x hx.1 (fun y _ => by rw [h2, one_mul, mul_one])
        exact ⟨hx.1.2, Subgroup.mem_centralizer_iff.mpr fun y hy => (hxc y hy).symm⟩

end CFSG.Quasithin.E9
