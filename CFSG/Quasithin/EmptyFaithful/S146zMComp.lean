module

public import CFSG.Quasithin.Background.A3Structure36ABasic
public import CFSG.Quasithin.EmptyFaithful.S146zMRk
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.SectionRank

section Aux

variable {X : Type*} [Group X]

theorem zmQuasisimple_normal_le_center_or_eq_top (hq : CFSG.IsQuasisimple X) (N : Subgroup X)
    [N.Normal] : N ≤ Subgroup.center X ∨ N = ⊤ := by
  let π := QuotientGroup.mk' (Subgroup.center X)
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  have hnormal : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hker : N ≤ π.ker := N.map_eq_bot_iff.mp hbot
    simpa only [π, QuotientGroup.ker_mk'] using hker
  · right
    have hsup : N ⊔ Subgroup.center X = ⊤ := by
      have hcomap := Subgroup.comap_map_eq π N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator X ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hq.1.commutator_eq_top] at hderived
    exact top_unique hderived

theorem le_center_of_quasisimple (hq : CFSG.IsQuasisimple X) (D : Subgroup X) [D.Normal]
    (hDs : Group.IsSolvable D) : D ≤ Subgroup.center X := by
  rcases zmQuasisimple_normal_le_center_or_eq_top hq D with h | h
  · exact h
  · exfalso
    have e : ↥D ≃* X := (MulEquiv.subgroupCongr h).trans Subgroup.topEquiv
    have hsolv : Group.IsSolvable X :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hne : x * y ≠ y * x := fun h' => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h'])
    have : Nontrivial X := ⟨⟨x * y, y * x, hne⟩⟩
    have := hq.1
    exact Group.IsPerfect.not_isSolvable X hsolv

omit [Group X] in
theorem zmInf_eq_bot_of_two_three {Y : Type*} [Group Y] [Finite Y] {D F : Subgroup Y}
    (hD : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card D → ℓ = 2 ∨ ℓ = 3)
    (hF : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card F → ℓ ≠ 2 ∧ ℓ ≠ 3) : D ⊓ F = ⊥ := by
  have hcop : Nat.Coprime (Nat.card D) (Nat.card F) := Nat.coprime_of_dvd fun r hr h1 h2 => by
    rcases hD r hr h1 with rfl | rfl
    · exact (hF 2 hr h2).1 rfl
    · exact (hF 3 hr h2).2 rfl
  exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot

theorem zm_center_le_fittingSubgroup (X : Type*) [Group X] :
    Subgroup.center X ≤ CFSG.fittingSubgroup X := by
  unfold CFSG.fittingSubgroup
  exact le_sSup (show Subgroup.center X ∈ {N : Subgroup X | N.Normal ∧ Group.IsNilpotent N} from
    ⟨inferInstance, inferInstance⟩)

variable [Finite X]

theorem le_center_of_coprime_fitting (hq : CFSG.IsQuasisimple (X ⧸ CFSG.fittingSubgroup X))
    (hF : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (CFSG.fittingSubgroup X) → ℓ ≠ 2 ∧ ℓ ≠ 3)
    (D : Subgroup X) [D.Normal] (hDs : Group.IsSolvable D)
    (hD : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card D → ℓ = 2 ∨ ℓ = 3) : D ≤ Subgroup.center X := by
  set F := CFSG.fittingSubgroup X with hFdef
  have hinf : D ⊓ F = ⊥ := zmInf_eq_bot_of_two_three hD hF
  let π := QuotientGroup.mk' F
  have hDmap : (D.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have hDmaps : Group.IsSolvable ↥(D.map π) :=
    Group.isSolvable_of_surjective (f := π.subgroupMap D) (π.subgroupMap_surjective D)
  have hc := le_center_of_quasisimple hq (D.map π) hDmaps
  intro d hd
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : g * d * g⁻¹ * d⁻¹ ∈ D := by
    have := ‹D.Normal›.conj_mem d hd g
    exact D.mul_mem this (D.inv_mem hd)
  have h2 : g * d * g⁻¹ * d⁻¹ ∈ F := by
    have hd' : π d ∈ Subgroup.center (X ⧸ F) := hc (Subgroup.mem_map_of_mem π hd)
    have hcomm := Subgroup.mem_center_iff.mp hd' (π g)
    have h3 : π (g * d * g⁻¹ * d⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    exact (QuotientGroup.eq_one_iff _).mp h3
  have h3 : g * d * g⁻¹ * d⁻¹ ∈ D ⊓ F := ⟨h1, h2⟩
  rw [hinf, Subgroup.mem_bot] at h3
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h3)

end Aux

section Comp

variable {Q : Type} [Group Q] [Finite Q]

@[expose] def SQTKList3Dvd : Prop :=
  ∀ (S : Type) [Group S] [Finite S], CFSG.Milestones.SQTKSimpleList S → ¬ 3 ∣ Nat.card S →
    ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.SuzukiModel S 2 f

theorem three_dvd_card_sl_two (p : ℕ) (hp : 1 < p) :
    3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  have : Fact (1 < p) := ⟨hp⟩
  let A : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩
  have hA3 : A ^ 3 = 1 := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [A, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  have hA1 : A ≠ 1 := by
    intro h
    have := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
      (B : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
    simp [A] at this
  have hord : orderOf A = 3 := orderOf_eq_prime hA3 hA1
  rw [← hord]
  exact orderOf_dvd_natCard A

theorem cComp_inf_central {J : Subgroup Q} (hA : A36StrongCat J) {K : Subgroup Q} [K.Normal] (hKs : Group.IsSolvable K)
    (hK : ∀ r : ℕ, r.Prime → r ∣ Nat.card K → r = 2 ∨ r = 3) :
    ∀ x ∈ J ⊓ K, ∀ j ∈ J, x * j = j * x := by
  set D : Subgroup ↥J := K.subgroupOf J with hD
  let φ : ↥D →* ↥K := (J.subtype.comp D.subtype).codRestrict K fun x => Subgroup.mem_subgroupOf.mp x.2
  have hφ : Function.Injective φ := fun x y h => by
    have h' : ((x : ↥J) : Q) = ((y : ↥J) : Q) := congrArg (fun z : ↥K => (z : Q)) h
    exact Subtype.ext (Subtype.ext h')
  have hDs : Group.IsSolvable ↥D := Group.isSolvable_of_isSolvable_injective hφ
  have hD23 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card D → ℓ = 2 ∨ ℓ = 3 := fun ℓ hℓ hd =>
    hK ℓ hℓ (hd.trans (Subgroup.card_dvd_of_injective φ hφ))
  have hDc : D ≤ Subgroup.center ↥J := by
    rcases hA.1 with ⟨hc, -, -⟩ | ⟨hc, -, -⟩ | h3 | h4
    · exact le_center_of_quasisimple hc.1 D hDs
    · exact le_center_of_quasisimple hc.1 D hDs
    · obtain ⟨p, hp, hp3, -, hel, -⟩ := h3
      refine le_center_of_coprime_fitting hA.2.1.2.1 (fun ℓ hℓ hd => ?_) D hDs hD23
      obtain ⟨e⟩ := hel
      have : NeZero p := ⟨hp.ne_zero⟩
      have hcard : Nat.card (CFSG.fittingSubgroup ↥J) = p ^ 2 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
          Nat.card_zmod, Nat.card_fin]
      rw [hcard] at hd
      have hℓp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow hd)
      omega
    · obtain ⟨-, -, -, h4⟩ := h4
      refine le_center_of_coprime_fitting hA.2.1.2.1 (fun ℓ hℓ hd => ?_) D hDs hD23
      have := (h4 ℓ hℓ hd).1
      omega
  intro x hx j hj
  have hxD : (⟨x, hx.1⟩ : ↥J) ∈ D := Subgroup.mem_subgroupOf.mpr hx.2
  have := Subgroup.mem_center_iff.mp (hDc hxD) ⟨j, hj⟩
  exact congrArg Subtype.val this.symm

theorem cComp_centralizes_of_a36 {J : Subgroup Q} (hJ : J ∈ cComp (⊤ : Subgroup Q))
    (hA : A36StrongCat J) {K : Subgroup Q} [K.Normal] (hKs : Group.IsSolvable K)
    (hK : ∀ r : ℕ, r.Prime → r ∣ Nat.card K → r = 2 ∨ r = 3) : ⁅J, K⁆ = ⊥ := by
  have hperf : ⁅J, J⁆ = J := perfect_of_mem_cComp hJ
  have hnorm : J ≤ Subgroup.normalizer (K : Set Q) :=
    le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
  have hJKJ : ⁅J, K⁆ ≤ J := (cComp_commutator_perfectCore hJ le_top hKs hnorm).1
  have hcentJ : ∀ x ∈ ⁅J, K⁆, ∀ j ∈ J, x * j = j * x := fun x hx j hj =>
    cComp_inf_central hA hKs hK x ⟨hJKJ hx, Subgroup.commutator_le_right J K hx⟩ j hj
  have h1 : ⁅⁅J, K⁆, J⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (hcentJ x hx j hj).symm
  have h2 : ⁅⁅K, J⁆, J⁆ = ⊥ := by rw [Subgroup.commutator_comm K J]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := J) (H₂ := J) (H₃ := K) h1 h2
  rwa [hperf] at h3

theorem cComp_simple_suzuki_of_a36 (hlist : SQTKList3Dvd) (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup Q) ≤ 2)
    {J : Subgroup Q} (hJ : J ∈ cComp (⊤ : Subgroup Q)) (hA : A36StrongCat J)
    {K : Subgroup Q} [K.Normal] (hKs : Group.IsSolvable K)
    (hK : ∀ r : ℕ, r.Prime → r ∣ Nat.card K → r = 2 ∨ r = 3)
    {E : Subgroup Q} (hEK : E ≤ K) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2) :
    ⁅J, K⁆ = ⊥ ∧ IsSimpleGroup ↥J ∧ ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.SuzukiModel ↥J 2 f := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcent := cComp_centralizes_of_a36 hJ hA hKs hK
  have hinfc := cComp_inf_central hA hKs hK
  have hN3 : ∀ y : ↥J, orderOf y = 3 → y ∈ Subgroup.center ↥J := by
    intro y hy
    have hyQ : orderOf (y : Q) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
    have hJC : J ≤ Subgroup.centralizer (K : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcent
    have hyE : (y : Q) ∈ E :=
      zmEq_of_orderOf_centralizes hrk hE hEc hyQ fun e he =>
        Subgroup.mem_centralizer_iff.mp (hJC y.2) e (hEK he)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hinfc y ⟨y.2, hEK hyE⟩ g g.2 |>.symm)
  have hnotsolv := not_isSolvable_of_mem_cComp hJ
  have hperf : Group.IsPerfect ↥J := A36A.isPerfect_of_mem_cComp hJ
  refine ⟨hcent, ?_⟩
  rcases hA.1 with ⟨hc, hsimp, hlistJ⟩ | ⟨hc, hZ3, -⟩ | h3 | h4
  · refine ⟨hsimp, hlist ↥J hlistJ fun h3dvd => ?_⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 3 h3dvd
    have hyc := hN3 y hy
    have hcen : Subgroup.center ↥J = ⊥ := by
      rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center ↥J) with h | h
      · exact h
      · exfalso
        apply hnotsolv
        exact Group.isSolvable_of_comm fun a b =>
          (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    rw [hcen, Subgroup.mem_bot] at hyc
    rw [hyc, orderOf_one] at hy
    exact absurd hy (by norm_num)
  · exfalso
    have h3dvd : 3 ∣ Nat.card ↥J := hZ3 ▸ Subgroup.card_subgroup_dvd_card (Subgroup.center ↥J)
    obtain ⟨g, hg3, hgc⟩ := exists_orderOf_not_mem_center_of_card_center (L := ↥J)
      (Or.inr hZ3) Nat.prime_three (by norm_num) h3dvd
    exact hgc (hN3 g hg3)
  · exfalso
    obtain ⟨p, hp, hp3, -, hel, ψdata⟩ := h3
    obtain ⟨-, ψ, hψs, -, -⟩ := ψdata
    have h3dvd : 3 ∣ Nat.card ↥J :=
      (three_dvd_card_sl_two p hp.one_lt).trans (Subgroup.card_dvd_of_surjective hψs)
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 3 h3dvd
    have hyc := hN3 y hy
    have hyF : y ∈ CFSG.fittingSubgroup ↥J := zm_center_le_fittingSubgroup ↥J hyc
    obtain ⟨e⟩ := hel
    have : NeZero p := ⟨hp.ne_zero⟩
    have hcard : Nat.card (CFSG.fittingSubgroup ↥J) = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
    have h3F : 3 ∣ p ^ 2 := by
      rw [← hcard, ← hy]
      exact (Subgroup.orderOf_coe ⟨y, hyF⟩ ▸ orderOf_dvd_natCard (⟨y, hyF⟩ : CFSG.fittingSubgroup ↥J))
    have h3p : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h3F)
    omega
  · exfalso
    obtain ⟨-, -, ⟨eSL⟩, hF⟩ := h4
    have h3dvd : 3 ∣ Nat.card ↥J := by
      have h1 : 3 ∣ Nat.card (↥J ⧸ CFSG.fittingSubgroup ↥J) := by
        rw [Nat.card_congr eSL.toEquiv]
        exact three_dvd_card_sl_two 5 (by norm_num)
      exact h1.trans (Subgroup.card_quotient_dvd_card _)
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 3 h3dvd
    have hyc := hN3 y hy
    have hyF : y ∈ CFSG.fittingSubgroup ↥J := zm_center_le_fittingSubgroup ↥J hyc
    have h3F : 3 ∣ Nat.card (CFSG.fittingSubgroup ↥J) := by
      rw [← hy]
      exact (Subgroup.orderOf_coe ⟨y, hyF⟩ ▸ orderOf_dvd_natCard (⟨y, hyF⟩ : CFSG.fittingSubgroup ↥J))
    have := (hF 3 Nat.prime_three h3F).1
    omega

end Comp

end CFSG.Quasithin
