module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootFirstCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.OddTranspositions.PartThree.Wong.RootData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] (D : RootData G)

private theorem centralizer_map_mulEquiv (φ : G ≃* G) (H : Subgroup G) :
    centralizer ((H.map φ.toMonoidHom : Subgroup G) : Set G) =
      (centralizer (H : Set G)).map φ.toMonoidHom := by
  apply le_antisymm
  · intro x hx
    refine ⟨φ.symm x, ?_, by simp⟩
    rw [mem_centralizer_iff] at hx
    change φ.symm x ∈ centralizer (H : Set G)
    rw [mem_centralizer_iff]
    intro h hh
    have h' := hx (φ h) (Subgroup.mem_map_of_mem φ.toMonoidHom hh)
    have h'' := congrArg φ.symm h'
    simpa using h''
  · rintro x ⟨y, hy, rfl⟩
    change y ∈ centralizer (H : Set G) at hy
    rw [mem_centralizer_iff] at hy
    change φ.toMonoidHom y ∈
      centralizer ((H.map φ.toMonoidHom : Subgroup G) : Set G)
    rw [mem_centralizer_iff]
    intro z hz
    obtain ⟨h, hh, rfl⟩ := hz
    simpa only [map_mul] using congrArg φ.toMonoidHom (hy h hh)

private theorem le_oddCore_of_odd_of_relIndex_four [Finite G]
    {Q H K : Subgroup G} (hHK : H ≤ K) (hidx : Q.relIndex K = 4)
    [(Q.subgroupOf K).Normal] (hodd : Odd (Nat.card H)) : H ≤ Q := by
  let f : K →* K ⧸ Q.subgroupOf K := QuotientGroup.mk' (Q.subgroupOf K)
  have hker : f.ker = Q.subgroupOf K := QuotientGroup.ker_mk' _
  have hrsub : (Q.subgroupOf K).relIndex (H.subgroupOf K) = Q.relIndex H :=
    Subgroup.relIndex_subgroupOf hHK
  have hcard : Nat.card ((H.subgroupOf K).map f) =
      (Q.subgroupOf K).relIndex (H.subgroupOf K) := by
    rw [← Subgroup.relIndex_ker (K := H.subgroupOf K) f, hker]
  have hquot : Nat.card (K ⧸ Q.subgroupOf K) = 4 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hdivK : Nat.card ((H.subgroupOf K).map f) ∣ Nat.card (K ⧸ Q.subgroupOf K) := by
    simpa using Subgroup.card_dvd_of_le (le_top : (H.subgroupOf K).map f ≤ ⊤)
  have hdiv4 : Nat.card ((H.subgroupOf K).map f) ∣ 4 := by
    rwa [hquot] at hdivK
  have hdiv : Nat.card ((H.subgroupOf K).map f) ∣ Nat.card (H.subgroupOf K) :=
    Subgroup.card_map_dvd (H.subgroupOf K) f
  have hcardH : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  have hdivH : Nat.card ((H.subgroupOf K).map f) ∣ Nat.card H := by
    rwa [hcardH] at hdiv
  have hoddn : Odd (Nat.card ((H.subgroupOf K).map f)) := hodd.of_dvd_nat hdivH
  set n := Nat.card ((H.subgroupOf K).map f) with hn_def
  have hnodd : Odd n := by rw [hn_def]; exact hoddn
  have hdiv4n : n ∣ 4 := by rw [hn_def]; exact hdiv4
  have hcop4 : Nat.Coprime 4 n := by
    have h2 : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hnodd
    simpa using h2.pow_left 2
  have hn1 : n = 1 := Nat.eq_one_of_dvd_coprimes hcop4 hdiv4n dvd_rfl
  have hn : Nat.card ((H.subgroupOf K).map f) = 1 := by
    rw [hn_def] at hn1
    exact hn1
  have hmapbot : (H.subgroupOf K).map f = ⊥ := Subgroup.card_eq_one.mp hn
  intro x hx
  have hxK : x ∈ K := hHK hx
  have hmem : (⟨x, hxK⟩ : K) ∈ H.subgroupOf K := hx
  have hfx : f ⟨x, hxK⟩ ∈ (H.subgroupOf K).map f :=
    Subgroup.mem_map_of_mem f hmem
  rw [hmapbot, mem_bot] at hfx
  have hkerx : (⟨x, hxK⟩ : K) ∈ f.ker := MonoidHom.mem_ker.mpr hfx
  rwa [hker] at hkerx

private theorem oddCore_eq_pPrimeCore (H : Type*) [Group H] :
    CFSG.oddCore H = CFSG.pPrimeCore 2 H := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

private theorem isPGroup_of_coprime_order_eq_one [Finite G] {p : ℕ} (hp : p.Prime)
    (h : ∀ x : G, Nat.Coprime p (orderOf x) → x = 1) : IsPGroup p G := by
  rw [isPGroup_iff_orderOf_dvd_pow]
  intro x
  obtain ⟨k, m, hpm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.ne_one
  have hpk : p ^ k ∣ orderOf x := ⟨m, hn⟩
  have hyorder : orderOf (x ^ p ^ k) = m := by
    rw [orderOf_pow_of_dvd (x := x) (n := p ^ k) (pow_ne_zero k hp.ne_zero) hpk, hn,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos k)]
  have hcop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
  have hy : x ^ p ^ k = 1 := by
    rw [← hyorder] at hcop
    exact h _ hcop
  exact ⟨k, orderOf_dvd_iff_pow_eq_one.mpr hy⟩

private theorem root_three_eq :
    D.P3 = D.D1.map (MulAut.conj (D.h2 * D.y)⁻¹).toMonoidHom := by
  rw [P3_eq_map_D2 D, D2_eq_map_D1 D, Subgroup.map_map]
  change D.D1.map ((MulAut.conj D.y⁻¹).toMonoidHom.comp
    (MulAut.conj D.h2⁻¹).toMonoidHom) =
    D.D1.map (MulAut.conj (D.h2 * D.y)⁻¹).toMonoidHom
  rw [show (MulAut.conj D.y⁻¹).toMonoidHom.comp (MulAut.conj D.h2⁻¹).toMonoidHom =
      (MulAut.conj (D.h2 * D.y)⁻¹).toMonoidHom by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group]

private theorem normalizer_Q_h2y [Finite G] :
    D.h2 * D.y ∈ normalizer (D.Q : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hNR⟩ := diagonal_unipotent_local_data D
  obtain ⟨-, -, -, -, -, -, hND1Q⟩ := odd_complement_of_diagonal_centralizer D
  obtain ⟨-, -, -, hNRQ, -, -⟩ := elementary_abelian_three_space D
  have h2H : D.h2 ∈ D.H := Subgroup.subset_closure (by simp)
  have hHR : D.H ≤ normalizer (D.R : Set G) := by
    have h := hNR ▸ inf_le_left
    exact (le_sup_right.trans le_sup_left).trans h
  exact normalizer (D.Q : Set G) |>.mul_mem (hNRQ (hHR h2H))
    (hND1Q D.outer.y_mem_normalizer)

private theorem map_Q_conj_h2y [Finite G] :
    D.Q.map (MulAut.conj (D.h2 * D.y)⁻¹).toMonoidHom = D.Q := by
  have hgN : D.h2 * D.y ∈ normalizer (D.Q : Set G) := normalizer_Q_h2y D
  apply le_antisymm
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact (mem_normalizer_iff.mp (inv_mem hgN) q).mp hq
  · intro x hx
    refine ⟨(D.h2 * D.y) * x * (D.h2 * D.y)⁻¹,
      (mem_normalizer_iff.mp hgN x).mp hx, ?_⟩
    simp [MulAut.conj_apply]
    group

private theorem centralizer_third_root_eq :
    centralizer (D.P3 : Set G) =
      (centralizer (D.D1 : Set G)).map (MulAut.conj (D.h2 * D.y)⁻¹).toMonoidHom := by
  rw [root_three_eq D]
  exact centralizer_map_mulEquiv _ _

private theorem root_three_odd_core [Finite G] :
    (CFSG.oddCore (centralizer (D.P3 : Set G))).map
      (centralizer (D.P3 : Set G)).subtype = D.Q := by
  let C1 : Subgroup G := centralizer (D.D1 : Set G)
  let C3 : Subgroup G := centralizer (D.P3 : Set G)
  let g : G := D.h2 * D.y
  let φ : MulAut G := MulAut.conj g⁻¹
  have hC3 : C3 = C1.map φ.toMonoidHom := centralizer_third_root_eq D
  let e : ↥C1 ≃* ↥C3 :=
    (MulEquiv.subgroupMap φ C1).trans (MulEquiv.subgroupCongr hC3).symm
  have hpC : CFSG.pPrimeCore 2 C3 =
      (CFSG.pPrimeCore 2 C1).map e.toMonoidHom :=
    (CFSG.pPrimeCore_map_iso (p := 2) e).symm
  have hcomp : C3.subtype.comp e.toMonoidHom = φ.toMonoidHom.comp C1.subtype := by
    ext c
    rfl
  change (CFSG.oddCore C3).map C3.subtype = D.Q
  rw [oddCore_eq_pPrimeCore, hpC, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    ← oddCore_eq_pPrimeCore]
  change D.Q.map φ.toMonoidHom = D.Q
  exact map_Q_conj_h2y D

private theorem root_three_P3_le_V [Finite G] : D.P3 ≤ D.V := by
  obtain ⟨-, -, hQset, -, -, -, -⟩ := odd_complement_of_diagonal_centralizer D
  obtain ⟨-, -, -, -, -, -, hQV⟩ := first_root_centralizer_odd_core D
  have hD2R : D.D2 ≤ D.R := by
    intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    change D.q1 a * D.q2 a⁻¹ ∈ D.P1 ⊔ D.P2
    exact Subgroup.mul_mem_sup (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
      (MonoidHom.mem_range.mpr ⟨a⁻¹, rfl⟩)
  have hP3R : D.P3 ≤ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom := by
    rw [P3_eq_map_D2 D]
    exact Subgroup.map_mono hD2R
  have hP3Q : D.P3 ≤ D.Q := by
    intro x hx
    have hx' : x ∈ (D.Q : Set G) := by
      rw [hQset]
      simpa using Set.mul_mem_mul (hP3R hx) D.R.one_mem
    simpa using hx'
  exact (hQV ▸ le_sup_right : D.P3 ≤ D.Q ⊓ D.V).trans inf_le_right

private theorem root_three_P3_le_centralizer :
    D.P3 ≤ centralizer (D.P3 : Set G) := by
  haveI : IsMulCommutative D.P3 := by
    change IsMulCommutative D.q3.range
    infer_instance
  exact Subgroup.le_centralizer (H := D.P3)

private theorem root_three_P1_le_centralizer [Finite G] :
    D.P1 ≤ centralizer (D.P3 : Set G) := by
  obtain ⟨-, -, -, -, hP1comm, -, -⟩ := first_root_centralizer_odd_core D
  have hP3V : D.P3 ≤ D.V := root_three_P3_le_V D
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact (hP1comm x hx y (hP3V hy)).symm

private theorem root_three_V_nilpotent [Finite G] : Group.IsNilpotent D.V := by
  obtain ⟨-, -, -, -, hP1comm, hcommVV, -⟩ := first_root_centralizer_odd_core D
  rw [Subgroup.isNilpotent_iff_lowerCentralSeries]
  refine ⟨2, ?_⟩
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
    Subgroup.lowerCentralSeries_zero, Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hP1cent : D.P1 ≤ centralizer (D.V : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact (hP1comm x hx y hy).symm
  exact hcommVV.trans hP1cent

private theorem root_three_intersection_le_Q [Finite G] :
    D.V ⊓ centralizer (D.P3 : Set G) ≤ D.Q := by
  let C1 : Subgroup G := centralizer (D.D1 : Set G)
  let C3 : Subgroup G := centralizer (D.P3 : Set G)
  let φ : MulAut G := MulAut.conj (D.h2 * D.y)⁻¹
  let ψ : MulAut G := MulAut.conj (D.h2 * D.y)
  obtain ⟨-, hidxQ, -, -, -, -, -⟩ := odd_complement_of_diagonal_centralizer D
  have hC3 : C3 = C1.map φ.toMonoidHom := centralizer_third_root_eq D
  have hφQ : D.Q.map φ.toMonoidHom = D.Q := map_Q_conj_h2y D
  have hoddV : Odd (Nat.card D.V) := odd_card_V D
  change D.V ⊓ C3 ≤ D.Q
  have hodd : Odd (Nat.card (D.V ⊓ C3 : Subgroup G)) :=
    hoddV.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hle : (D.V ⊓ C3).map ψ.toMonoidHom ≤ C1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxC3 : x ∈ C3 := hx.2
    rw [hC3] at hxC3
    obtain ⟨c, hc, hcx⟩ := hxC3
    rw [← hcx]
    have hcancel : ψ.toMonoidHom (φ.toMonoidHom c) = c := by
      simp only [φ, ψ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hcancel]
    exact hc
  have hQleC1 : D.Q ≤ C1 := by
    rw [RootData.Q]
    rintro x ⟨q, hq, rfl⟩
    exact q.2
  have hQsub : D.Q.subgroupOf C1 = CFSG.oddCore C1 := by
    apply Subgroup.map_injective C1.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hQleC1]
    rfl
  haveI hQnormal : (D.Q.subgroupOf C1).Normal := hQsub ▸ CFSG.oddCore_normal C1
  have hleQ : (D.V ⊓ C3).map ψ.toMonoidHom ≤ D.Q :=
    le_oddCore_of_odd_of_relIndex_four hle hidxQ (by
      rw [Subgroup.card_map_of_injective ψ.injective]
      exact hodd)
  intro x hx
  have hψx : ψ x ∈ D.Q := hleQ (Subgroup.mem_map_of_mem ψ.toMonoidHom hx)
  have hxeq : φ (ψ x) = x := by
    simp only [φ, ψ, MulAut.conj_apply]
    group
  have hmem : φ (ψ x) ∈ D.Q.map φ.toMonoidHom :=
    Subgroup.mem_map_of_mem φ.toMonoidHom hψx
  rw [hφQ] at hmem
  rwa [hxeq] at hmem

private theorem root_three_intersection [Finite G] :
    D.V ⊓ centralizer (D.P3 : Set G) = D.P1 ⊔ D.P3 := by
  obtain ⟨-, -, -, hP1V, -, -, hQV⟩ := first_root_centralizer_odd_core D
  have hVCQ : D.V ⊓ centralizer (D.P3 : Set G) ≤ D.Q :=
    root_three_intersection_le_Q D
  have hVC : D.V ⊓ centralizer (D.P3 : Set G) ≤ D.P1 ⊔ D.P3 := by
    have h : D.V ⊓ centralizer (D.P3 : Set G) ≤ D.Q ⊓ D.V :=
      le_inf hVCQ inf_le_left
    rwa [hQV] at h
  exact le_antisymm hVC
    (sup_le (le_inf hP1V (root_three_P1_le_centralizer D))
      (le_inf (root_three_P3_le_V D) (root_three_P3_le_centralizer D)))

private theorem root_three_five_prime_element_centralizes_P3 [Finite G] (x : ↥D.V)
    (hcop : Nat.Coprime 5 (orderOf x)) :
    (x : G) ∈ centralizer (D.P3 : Set G) := by
  have hP3V : D.P3 ≤ D.V := root_three_P3_le_V D
  have hVnil : Group.IsNilpotent D.V := root_three_V_nilpotent D
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
  have hyV : D.q3 a ∈ D.V := hP3V (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  let y' : D.V := ⟨D.q3 a, hyV⟩
  have hP3mem : D.q3 a ∈ D.P3 := MonoidHom.mem_range.mpr ⟨a, rfl⟩
  have hord : orderOf y' ∣ 5 := by
    have h := Subgroup.orderOf_dvd_natCard D.P3 hP3mem
    rw [card_P3 D] at h
    simpa [y', Subgroup.orderOf_mk] using h
  have hcop' : Nat.Coprime (orderOf x) (orderOf y') :=
    hcop.symm.of_dvd_right hord
  haveI : Group.IsNilpotent ↥D.V := hVnil
  have hc := Group.IsNilpotent.commute_of_orderOf_coprime (G := ↥D.V) hcop'
  have hcG : Commute (x : G) (D.q3 a) := by
    rw [commute_iff_eq]
    have h := congrArg Subtype.val hc.eq
    simpa [y'] using h
  exact hcG.symm

private theorem root_three_sup_P1_P3_isPGroup [Finite G] :
    IsPGroup 5 (D.P1 ⊔ D.P3 : Subgroup G) := by
  have hP1pg : IsPGroup 5 D.P1 := by
    apply IsPGroup.of_card (n := 1)
    rw [card_P1 D]
    norm_num
  have hP3pg : IsPGroup 5 D.P3 := by
    apply IsPGroup.of_card (n := 1)
    rw [card_P3 D]
    norm_num
  have hP1cent : D.P1 ≤ centralizer (D.P3 : Set G) := root_three_P1_le_centralizer D
  exact IsPGroup.to_sup_of_normal_right' hP1pg hP3pg
    (hP1cent.trans (Subgroup.centralizer_le_normalizer _))

private theorem root_three_five_prime_element_eq_one [Finite G] (x : ↥D.V)
    (hcop : Nat.Coprime 5 (orderOf x)) : x = 1 := by
  have hcommP3 := root_three_five_prime_element_centralizes_P3 D x hcop
  have hxV : (x : G) ∈ D.V := x.2
  have hxsup : (x : G) ∈ D.P1 ⊔ D.P3 := by
    have hmem : (x : G) ∈ D.V ⊓ centralizer (D.P3 : Set G) := ⟨hxV, hcommP3⟩
    rwa [root_three_intersection D] at hmem
  have hsupPg : IsPGroup 5 (D.P1 ⊔ D.P3 : Subgroup G) :=
    root_three_sup_P1_P3_isPGroup D
  let X : Subgroup G := D.P1 ⊔ D.P3
  let xX : X := ⟨(x : G), hxsup⟩
  obtain ⟨k, hk⟩ := hsupPg.exists_orderOf_dvd_pow xX
  have hcop' : Nat.Coprime 5 (orderOf (x : G)) := by simpa using hcop
  have hk' : orderOf (x : G) ∣ 5 ^ k := by
    simpa [X, xX, Subgroup.orderOf_mk] using hk
  have hone : orderOf (x : G) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hcop'.pow_left k) hk' dvd_rfl
  exact Subtype.ext (orderOf_eq_one_iff.mp hone)

private theorem root_three_isPGroup [Finite G] : IsPGroup 5 D.V := by
  apply isPGroup_of_coprime_order_eq_one (by norm_num)
  intro x hcop
  exact root_three_five_prime_element_eq_one D x hcop

theorem third_root_centralizer_and_five_group [Finite G] :
    D.P3 = D.D1.map (MulAut.conj (D.h2 * D.y)⁻¹).toMonoidHom ∧
    (CFSG.oddCore (centralizer (D.P3 : Set G))).map (centralizer (D.P3 : Set G)).subtype = D.Q ∧
    D.V ⊓ centralizer (D.P3 : Set G) = D.P1 ⊔ D.P3 ∧ IsPGroup 5 D.V := by
  exact ⟨root_three_eq D, root_three_odd_core D, root_three_intersection D,
    root_three_isPGroup D⟩

end CFSG.OddTranspositions.PartThree.Wong.RootData
