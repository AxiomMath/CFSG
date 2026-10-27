module

public import CFSG.RankThree.GF2n.Tim77.Cor2AlphaBasic
public import CFSG.Holt.StarCase.Lemma26Basic
public import CFSG.LargeExtraspecial.S111SHCor3
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions CFSG.Open Subgroup
open CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

structure ShultSetup (S : Sylow 2 G) (t : G) : Prop where
  ne_one : t ≠ 1
  sq : t * t = 1
  mem : t ∈ (S : Subgroup G)
  central : ∀ s ∈ (S : Subgroup G), s * t = t * s
  abelian : IsMulCommutative ↥(CFSG.LargeExtraspecial.S11.wcl t)

@[expose] def Cor2BetaShape (Y : Subgroup G) : Prop :=
  ∃ (r : ℕ) (X : Fin r → Subgroup G), (∀ i, X i ≤ Y) ∧ (∀ i, ((X i).subgroupOf Y).Normal) ∧
    (∀ i j, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j, x * y = y * x) ∧ (⨆ i, X i) = Y ∧
    ∀ i, IsCoveringOf Tim77Cor2BetaList ↥(X i) ∨ HasNormalTwoComplement ↥(X i)

structure Cor2BetaDecomp (H E Y : Subgroup G) : Prop where
  E_le : E ≤ H
  E_eq : E = sSup {K : Subgroup G | IsComponentOf K H}
  Y_le : Y ≤ H
  sup_eq : E ⊔ Y = H
  comm : ∀ e ∈ E, ∀ y ∈ Y, e * y = y * e
  E_normal : E.Normal
  Y_normal : Y.Normal
  Y_compl : HasNormalTwoComplement ↥Y
  E_shape : ∃ (r : ℕ) (K : Fin r → Subgroup G), (∀ i, K i ≤ E) ∧
    (∀ i, ((K i).subgroupOf H).Normal) ∧
    (∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) ∧ (⨆ i, K i) = E ∧
    ∀ i, IsCoveringOf Tim77Cor2BetaList ↥(K i)

theorem cor2Beta_eq_one_of_odd {N : Subgroup G} (hN : Odd (Nat.card N)) {c : G} (hc : c ∈ N)
    (h : c * c = 1) : c = 1 := by
  have h1 : orderOf c ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hc
  have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
  have h3 : Nat.Coprime (orderOf c) 2 :=
    (Nat.Coprime.coprime_dvd_left h1 hN.coprime_two_right)
  have : orderOf c = 1 := Nat.Coprime.eq_one_of_dvd h3 h2
  exact orderOf_eq_one_iff.mp this

theorem cor2Beta_exists_central_mem {A : Subgroup G} (hA : IsElemAbelian 2 A) (hA1 : A ≠ ⊥)
    (S : Sylow 2 G) (hS : (S : Subgroup G) ≤ normalizer (A : Set G)) :
    ∃ t ∈ A, t ≠ 1 ∧ t ∈ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), s * t = t * s := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  have hsup : IsPGroup 2 ↥((S : Subgroup G) ⊔ A) :=
    S.isPGroup'.to_sup_of_normal_right' hp2 hS
  have hAS : A ≤ (S : Subgroup G) := sup_eq_left.mp (S.is_maximal' hsup le_sup_left)
  haveI : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  haveI hN : (A.subgroupOf (S : Subgroup G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAS).mpr hS
  have hne : A.subgroupOf (S : Subgroup G) ≠ ⊥ := by
    intro h
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hAS ha⟩ : ↥(S : Subgroup G)) ∈ A.subgroupOf (S : Subgroup G) := ha
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  obtain ⟨⟨m, hm⟩, hm1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hmA, hmZ⟩ := Subgroup.mem_inf.mp hm
  refine ⟨(m : G), hmA, fun h => hm1 (Subtype.ext (Subtype.ext h)), m.2, fun s hs => ?_⟩
  have := Subgroup.mem_center_iff.mp hmZ ⟨s, hs⟩
  exact congrArg Subtype.val this

theorem cor2Beta_conj_mem_wac {A : Subgroup G} (hroot : IsRootType 2 A) {t : G} (ht : t ∈ A)
    (ht1 : t ≠ 1) {g : G} (hc : (g * t * g⁻¹) * t = t * (g * t * g⁻¹)) :
    g * t * g⁻¹ ∈ WAC A := by
  have hy : g * t * g⁻¹ ∈ conjSubgroup g A := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using ht
  have hy1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply ht1
    have := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using this
  have ht' : t ∈ conjSubgroup 1 A := by
    rw [CFSG.RankThree.GF2n.conjSubgroup_one]
    exact ht
  have key := commute_of_mem_conj hroot hy hy1 ht' ht1 hc
  have hle : conjSubgroup g A ≤ Subgroup.centralizer (A : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : a ∈ conjSubgroup 1 A := by
      rw [CFSG.RankThree.GF2n.conjSubgroup_one]
      exact ha
    exact (key b hb a ha').symm
  exact conj_le_WAC hle hy

theorem cor2Beta_wcl_le_wac {A : Subgroup G} (hroot : IsRootType 2 A) {t : G} (ht : t ∈ A)
    (ht1 : t ≠ 1) : CFSG.LargeExtraspecial.S11.wcl t ≤ WAC A := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨m, hm, hc⟩
  rw [hm]
  refine cor2Beta_conj_mem_wac hroot ht ht1 ?_
  rw [← hm]
  exact hc

theorem cor2Beta_isMulCommutative_wcl {A : Subgroup G} (hroot : IsRootType 2 A)
    (hW : ⁅WAC A, WAC A⁆ = ⊥) {t : G} (ht : t ∈ A) (ht1 : t ≠ 1) :
    IsMulCommutative ↥(CFSG.LargeExtraspecial.S11.wcl t) := by
  have hle := cor2Beta_wcl_le_wac hroot ht ht1
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hW
  have ha : (a : G) ∈ WAC A := hle a.2
  have hb : (b : G) ∈ WAC A := hle b.2
  exact (Subgroup.mem_centralizer_iff.mp (h1 hb) a ha)

theorem cor2Beta_wac_commute {A : Subgroup G} : ∀ w ∈ WAC A, ∀ a ∈ A, a * w = w * a := by
  intro w hw a ha
  exact Subgroup.mem_centralizer_iff.mp (WAC_le_centralizer A hw) a ha

theorem cor2Beta_wcl_commute {A : Subgroup G} (hroot : IsRootType 2 A) {t : G} (ht : t ∈ A)
    (ht1 : t ≠ 1) : ∀ w ∈ CFSG.LargeExtraspecial.S11.wcl t, ∀ a ∈ A, a * w = w * a :=
  fun _ hw a ha => cor2Beta_wac_commute _ (cor2Beta_wcl_le_wac hroot ht ht1 hw) a ha

theorem cor2Beta_isMulCommutative_of_centralizes {A : Subgroup G} (hroot : IsRootType 2 A)
    {a t : G} (ha : a ∈ A) (ha1 : a ≠ 1) (ht : t ∈ A) (ht1 : t ≠ 1)
    (h : ∀ x ∈ normalClosure ({t} : Set G), a * x = x * a) :
    IsMulCommutative ↥(normalClosure (A : Set G)) := by
  have ha' : a ∈ conjSubgroup 1 A := by
    rw [CFSG.RankThree.GF2n.conjSubgroup_one]
    exact ha
  have hAA : ∀ (g : G), ∀ x ∈ conjSubgroup g A, ∀ b ∈ A, x * b = b * x := by
    intro g x hx b hb
    have hy : g * t * g⁻¹ ∈ conjSubgroup g A := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using ht
    have hy1 : g * t * g⁻¹ ≠ 1 := by
      intro h'
      apply ht1
      have := congrArg (fun x => g⁻¹ * x * g) h'
      simpa [mul_assoc] using this
    have hyN : g * t * g⁻¹ ∈ normalClosure ({t} : Set G) :=
      (inferInstance : (normalClosure ({t} : Set G)).Normal).conj_mem t
        (subset_normalClosure (Set.mem_singleton t)) g
    have key := commute_of_mem_conj hroot hy hy1 ha' ha1 (h _ hyN).symm
    have hb' : b ∈ conjSubgroup 1 A := by
      rw [CFSG.RankThree.GF2n.conjSubgroup_one]
      exact hb
    exact key x hx b hb'
  have hgen : ∀ x ∈ Group.conjugatesOfSet (A : Set G), ∀ y ∈ Group.conjugatesOfSet (A : Set G),
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨a₁, ha₁, hc₁⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨a₂, ha₂, hc₂⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c₁, rfl⟩ := isConj_iff.mp hc₁
    obtain ⟨c₂, rfl⟩ := isConj_iff.mp hc₂
    have hy' : (c₁⁻¹ * c₂) * a₂ * (c₁⁻¹ * c₂)⁻¹ ∈ conjSubgroup (c₁⁻¹ * c₂) A := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using ha₂
    have h3 := hAA (c₁⁻¹ * c₂) _ hy' a₁ ha₁
    calc c₁ * a₁ * c₁⁻¹ * (c₂ * a₂ * c₂⁻¹)
        = c₁ * (a₁ * ((c₁⁻¹ * c₂) * a₂ * (c₁⁻¹ * c₂)⁻¹)) * c₁⁻¹ := by group
      _ = c₁ * (((c₁⁻¹ * c₂) * a₂ * (c₁⁻¹ * c₂)⁻¹) * a₁) * c₁⁻¹ := by rw [← h3]
      _ = c₂ * a₂ * c₂⁻¹ * (c₁ * a₁ * c₁⁻¹) := by group
  have hcomm : ∀ x y : G, x ∈ Subgroup.closure (Group.conjugatesOfSet (A : Set G)) →
      y ∈ Subgroup.closure (Group.conjugatesOfSet (A : Set G)) → Commute x y := by
    intro x y hx hy
    induction hx, hy using Subgroup.closure_induction₂ with
    | mem x y hx hy => exact hgen x hx y hy
    | one_left x hx => exact Commute.one_left x
    | one_right x hx => exact Commute.one_right x
    | mul_left x y z hx hy hz h1 h2 => exact h1.mul_left h2
    | mul_right y z x hy hz hx h1 h2 => exact h1.mul_right h2
    | inv_left x y hx hy h => exact h.inv_left
    | inv_right x y hx hy h => exact h.inv_right
  exact ⟨⟨fun x y => Subtype.ext (hcomm x y x.2 y.2)⟩⟩

theorem cor2Beta_oddNormal_commute {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (h4 : 4 ≤ Nat.card A) {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N)) :
    ∀ n ∈ N, ∀ x ∈ normalClosure (A : Set G), n * x = x * n := by
  classical
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by simpa [sq] using hA.2 x hx
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hcon
    rw [this, Subgroup.card_bot] at h4
    omega
  have hzp : Nat.card (Subgroup.zpowers a) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hA2 a haA))
  obtain ⟨b, hbA, hba⟩ : ∃ b ∈ A, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ Subgroup.zpowers a := hcon
    have := Subgroup.card_le_of_le hle
    omega
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hba
    have : b = a⁻¹ := by
      calc b = a⁻¹ * (a * b) := by group
        _ = a⁻¹ := by rw [h, mul_one]
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hNn : ∀ g : G, g ∈ normalizer (N : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    trivial
  have hcent : ∀ w ∈ A, w ≠ 1 → ∀ n ∈ N, w * n = n * w → n ∈ Subgroup.centralizer (A : Set G) := by
    intro w hw hw1 n hn hwn
    have hnN : n ∈ normalizer (A : Set G) :=
      mem_normalizer_of_commute_of_isTI hTI hw hw1 hwn.symm
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : n * x * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hnN x).mp hx
    have hcA : n * x * n⁻¹ * x⁻¹ ∈ A := A.mul_mem h1 (A.inv_mem hx)
    have hcN : n * x * n⁻¹ * x⁻¹ ∈ N := by
      have h2 : x * n⁻¹ * x⁻¹ ∈ N := by
        simpa using (inferInstance : N.Normal).conj_mem n⁻¹ (N.inv_mem hn) x
      have e : n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) := by group
      rw [e]
      exact N.mul_mem hn h2
    have hc1 : n * x * n⁻¹ * x⁻¹ = 1 := cor2Beta_eq_one_of_odd hN hcN (hA2 _ hcA)
    calc x * n = (n * x * n⁻¹ * x⁻¹) * (x * n) := by rw [hc1, one_mul]
      _ = n * x := by group
  have hle : N ≤ Subgroup.centralizer (A : Set G) := by
    refine CFSG.Holt.StarLemma26.le_of_forall_commute_mem hN (hA2 a haA) (hA2 b hbA)
      (hAc a haA b hbA) (hNn a) (hNn b) ?_
    intro w hw n hn hwn
    rcases hw with rfl | rfl | rfl
    · exact hcent w haA ha1 n hn hwn
    · exact hcent w hbA hb1 n hn hwn
    · exact hcent (a * b) (A.mul_mem haA hbA) hab1 n hn hwn
  intro n hn x hx
  have hx' : x ∈ Subgroup.closure (Group.conjugatesOfSet (A : Set G)) := hx
  have hsub : Subgroup.closure (Group.conjugatesOfSet (A : Set G)) ≤
      Subgroup.centralizer ({n} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    obtain ⟨a₁, ha₁, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨g, rfl⟩ := isConj_iff.mp hc
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hg : g⁻¹ * n * g ∈ Subgroup.centralizer (A : Set G) :=
      hle (by simpa using (inferInstance : N.Normal).conj_mem n hn g⁻¹)
    have h1 := Subgroup.mem_centralizer_iff.mp hg a₁ ha₁
    calc g * a₁ * g⁻¹ * n = g * (a₁ * (g⁻¹ * n * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * n * g) * a₁) * g⁻¹ := by rw [← h1]
      _ = n * (g * a₁ * g⁻¹) := by group
  have := Subgroup.mem_centralizer_singleton_iff.mp (hsub hx')
  exact this.symm

theorem cor2Beta_commute_of_centralizes {A : Subgroup G} (hTI : IsTI A) (hroot : IsRootType 2 A)
    {t : G} (ht : t ∈ A) (ht1 : t ≠ 1)
    (hnab : ¬ IsMulCommutative ↥(normalClosure (A : Set G)))
    {z : G} (hz : ∀ h ∈ normalClosure ({t} : Set G), z * h = h * z) :
    ∀ a ∈ A, a * z = z * a := by
  intro a ha
  have htH : t ∈ normalClosure ({t} : Set G) := subset_normalClosure (Set.mem_singleton t)
  have hzN : z ∈ normalizer (A : Set G) := mem_normalizer_of_commute_of_isTI hTI ht ht1 (hz t htH)
  have hcA : a * z * a⁻¹ * z⁻¹ ∈ A := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hzN a⁻¹).mp (A.inv_mem ha)
    have e : a * z * a⁻¹ * z⁻¹ = a * (z * a⁻¹ * z⁻¹) := by group
    rw [e]
    exact A.mul_mem ha h1
  have hHn : (normalClosure ({t} : Set G)).Normal := inferInstance
  have hcH : ∀ x ∈ normalClosure ({t} : Set G),
      (a * z * a⁻¹ * z⁻¹) * x = x * (a * z * a⁻¹ * z⁻¹) := by
    intro x hx
    have hx1 : a⁻¹ * x * a ∈ normalClosure ({t} : Set G) := by
      simpa using hHn.conj_mem x hx a⁻¹
    have h1 := hz _ hx1
    have h2 := hz x hx
    have e1 : (a * z * a⁻¹) * x = x * (a * z * a⁻¹) := by
      calc (a * z * a⁻¹) * x = a * (z * (a⁻¹ * x * a)) * a⁻¹ := by group
        _ = a * ((a⁻¹ * x * a) * z) * a⁻¹ := by rw [h1]
        _ = x * (a * z * a⁻¹) := by group
    have e2 : z⁻¹ * x = x * z⁻¹ := by
      calc z⁻¹ * x = z⁻¹ * (x * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * x) * z⁻¹ := by rw [h2]
        _ = x * z⁻¹ := by group
    calc (a * z * a⁻¹ * z⁻¹) * x = (a * z * a⁻¹) * (z⁻¹ * x) := by group
      _ = (a * z * a⁻¹) * (x * z⁻¹) := by rw [e2]
      _ = ((a * z * a⁻¹) * x) * z⁻¹ := by group
      _ = (x * (a * z * a⁻¹)) * z⁻¹ := by rw [e1]
      _ = x * (a * z * a⁻¹ * z⁻¹) := by group
  by_cases hc1 : a * z * a⁻¹ * z⁻¹ = 1
  · have : a * z = z * a := by
      calc a * z = (a * z * a⁻¹ * z⁻¹) * (z * a) := by group
        _ = z * a := by rw [hc1, one_mul]
    exact this
  · exact absurd (cor2Beta_isMulCommutative_of_centralizes hroot hcA hc1 ht ht1 hcH) hnab

theorem cor2Beta_mul_self_of_abelian {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hab : IsMulCommutative ↥(normalClosure (A : Set G))) :
    ∀ x ∈ normalClosure (A : Set G), x * x = 1 := by
  intro x hx
  have hx' : x ∈ Subgroup.closure (Group.conjugatesOfSet (A : Set G)) := hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨g, rfl⟩ := isConj_iff.mp hc
    have h2 : a * a = 1 := by simpa [sq] using hA.2 a ha
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  | one => simp
  | mul y z hy hz ihy ihz =>
    have hyG : y ∈ normalClosure (A : Set G) := hy
    have hzG : z ∈ normalClosure (A : Set G) := hz
    have hc : y * z = z * y :=
      congrArg Subtype.val (hab.is_comm.comm ⟨y, hyG⟩ ⟨z, hzG⟩)
    have e : y * z * (y * z) = (y * y) * (z * z) := by
      calc y * z * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [← hc]
        _ = (y * y) * (z * z) := by group
    rw [e, ihy hyG, ihz hzG, one_mul]
  | inv y hy ih =>
    have hyG : y ∈ normalClosure (A : Set G) := hy
    have := ih hyG
    calc y⁻¹ * y⁻¹ = (y * y)⁻¹ := by group
      _ = 1 := by rw [this]; simp

theorem cor2Beta_shape_of_abelian {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hab : IsMulCommutative ↥(normalClosure (A : Set G))) :
    Cor2BetaShape (normalClosure (A : Set G)) := by
  have h2 := cor2Beta_mul_self_of_abelian hA hab
  refine ⟨1, fun _ => normalClosure (A : Set G), fun _ => le_rfl, fun _ => ?_,
    fun i j hij => absurd (Subsingleton.elim i j) hij, ?_, fun _ => Or.inr ?_⟩
  · rw [Subgroup.subgroupOf_self]
    infer_instance
  · exact iSup_const
  · refine ⟨⊥, inferInstance, ?_, inferInstance, fun g => ?_⟩
    · rw [Subgroup.card_bot]
      exact odd_one
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      refine ⟨1, ?_⟩
      rw [pow_one, pow_two, ← QuotientGroup.mk_mul]
      have : x * x = 1 := Subtype.ext (h2 x x.2)
      rw [this]
      rfl

theorem cor2Beta_four_le_card {A : Subgroup G} (hA : IsElemAbelian 2 A) {t a : G} (ht : t ∈ A)
    (ht1 : t ≠ 1) (ha : a ∈ A) (hat : a ∉ Subgroup.zpowers t) : 4 ≤ Nat.card A := by
  have hp : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hle : Subgroup.zpowers t ≤ A := Subgroup.zpowers_le.mpr ht
  have hcard2 : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa [sq] using hA.2 t ht) ht1
  by_contra h4
  push Not at h4
  have hn1 : n ≤ 1 := by
    by_contra hn2
    push Not at hn2
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hAle : Nat.card A ≤ Nat.card (Subgroup.zpowers t) := by
    rw [hn, hcard2]
    calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 2 := by norm_num
  exact hat (Subgroup.eq_of_le_of_card_ge hle hAle ▸ ha)

theorem cor2Beta_mem_wcl_of_commute {A : Subgroup G} (hroot : IsRootType 2 A) {t a : G}
    (ht : t ∈ A) (ht1 : t ≠ 1) (ha : a ∈ A) (ha1 : a ≠ 1) (g : G)
    (h : a * (g * t * g⁻¹) = (g * t * g⁻¹) * a) :
    g * t * g⁻¹ ∈ CFSG.LargeExtraspecial.S11.wcl t := by
  have hy : g * t * g⁻¹ ∈ conjSubgroup g A := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using ht
  have hy1 : g * t * g⁻¹ ≠ 1 := by
    intro h'
    apply ht1
    have := congrArg (fun x => g⁻¹ * x * g) h'
    simpa [mul_assoc] using this
  have ha' : a ∈ conjSubgroup 1 A := by
    rw [CFSG.RankThree.GF2n.conjSubgroup_one]
    exact ha
  have ht' : t ∈ conjSubgroup 1 A := by
    rw [CFSG.RankThree.GF2n.conjSubgroup_one]
    exact ht
  have key := commute_of_mem_conj hroot hy hy1 ha' ha1 h.symm
  exact CFSG.LargeExtraspecial.S11.subset_wcl t ⟨g, rfl, key _ hy t ht'⟩

end CFSG.RankThree.GF2n.Tim77
