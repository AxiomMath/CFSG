module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148VNON
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VONCent3
public import CFSG.RankThree.PartTwo.Sec14.Ronan148DGen
import CFSG.RankThree.PartTwo.Sec14.Ronan148VOmega6
import CFSG.RankThree.PartTwo.Sec14.Ronan148VA5Inner
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
public import CFSG.RankThree.PartOne.S12.Sec159Tools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148 Ronan148J
open CFSG.RankThree.Native.ONTriple
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem img148_inf_centralizer_le (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {a : G}
    (ha : a ∈ A) (ha3 : a ^ 3 = 1) :
    img148 A Y Y ⊓ Subgroup.centralizer {alpha148 A Y a ha} ≤
      img148 A Y (Y ⊓ Subgroup.centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx
  obtain ⟨y, hyM, hyY, rfl⟩ := mem_img148_iff.mp hx.1
  have hc : QuotientGroup.mk' (ker148 A Y) ⟨y, hyM⟩ * alpha148 A Y a ha =
      alpha148 A Y a ha * QuotientGroup.mk' (ker148 A Y) ⟨y, hyM⟩ :=
    Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hU : ∀ u ∈ Subgroup.zpowers a, u * y * u⁻¹ * y⁻¹ ∈ pPrimeCoreOf 3 Y := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hakA : a ^ k ∈ A := A.zpow_mem ha k
    have hakM : a ^ k ∈ Y ⊔ A := Subgroup.mem_sup_right hakA
    have hck : QuotientGroup.mk' (ker148 A Y) ⟨a ^ k, hakM⟩ =
        (alpha148 A Y a ha) ^ k := by
      rw [alpha148_eq_mk', ← map_zpow]
      rfl
    have hcomm : Commute (QuotientGroup.mk' (ker148 A Y) ⟨a ^ k, hakM⟩)
        (QuotientGroup.mk' (ker148 A Y) ⟨y, hyM⟩) := by
      rw [hck]
      exact (Commute.zpow_left hc.symm k)
    have hmem : (⟨a ^ k, hakM⟩ : ↥(Y ⊔ A)) * ⟨y, hyM⟩ * (⟨a ^ k, hakM⟩ : ↥(Y ⊔ A))⁻¹ *
        (⟨y, hyM⟩ : ↥(Y ⊔ A))⁻¹ ∈ ker148 A Y := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      have e := hcomm.eq
      simp only [QuotientGroup.mk'_apply] at e
      rw [e]
      group
    exact Subgroup.mem_subgroupOf.mp hmem
  have hp : IsPGroup 3 (Subgroup.zpowers a) := Sec4.Ronan148V.isPGroup_zpowers_of_pow_three ha3
  have hVp : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 Y) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
  have hUV : Subgroup.zpowers a ≤ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) :=
    Subgroup.zpowers_le.mpr ((hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)) ha)
  have hyV : y ∈ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) := le_normalizer_pPrimeCoreOf 3 Y hyY
  obtain ⟨v, hv, hfix⟩ := CFSG.RankThree.PartOne.Sec159.exists_fixed_in_coset hp hVp hUV hyV hU
  have hvY : v ∈ Y := pPrimeCoreOf_le 3 Y hv
  refine mem_img148_iff.mpr ⟨y * v, Subgroup.mem_sup_left (Y.mul_mem hyY hvY),
    Subgroup.mem_inf.mpr ⟨Y.mul_mem hyY hvY, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hfix a (Subgroup.mem_zpowers a)
    calc y * v * a = a * (y * v) * a⁻¹ * a := by rw [h]
      _ = a * (y * v) := by group
  · rw [mk'_ker148_eq_iff]
    show (y * v)⁻¹ * y ∈ pPrimeCoreOf 3 Y
    rw [mul_inv_rev, inv_mul_cancel_right]
    exact inv_mem hv

end Quot

section ON


theorem le_of_ON {Q : Type} [Group Q] [Finite Q] {Aq Jq : Subgroup Q}
    (hAab : ∀ x ∈ Aq, ∀ y ∈ Aq, x * y = y * x) (hA3 : ∀ a ∈ Aq, a ^ 3 = 1)
    (hF3 : ∀ w : Q, w ∈ Subgroup.centralizer (Aq : Set Q) → w ^ 3 = 1 → w ∈ Aq)
    (hA27 : Nat.card Aq = 27) (hAJ : Aq ≤ Subgroup.normalizer (Jq : Set Q)) (ψ : ↥Jq ≃* GM)
    (hZ3 : Nat.card (Subgroup.center ↥Jq) = 3) {dq : Q} (hdA : dq ∈ Aq) (hdJ : dq ∈ Jq)
    (hd1 : dq ≠ 1) (hdC : ∀ x ∈ Jq, dq * x = x * dq) : Aq ≤ Jq := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨j, hjAJ, hjnc⟩, hCD⟩ :=
    exists_noncentral_and_sup_eq_of_ON hAab hA3 hF3 hA27 hAJ ψ hZ3 hdA hdJ hd1 hdC
  have hd3 : dq ^ 3 = 1 := hA3 dq hdA
  have hjd : j ∉ Subgroup.zpowers dq := by
    intro h
    obtain ⟨y, hy, hjy⟩ := hjnc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hjy
    rw [← hk]
    exact (Commute.zpow_left (hdC y hy) k).eq
  have h9 : Nat.card ↥(Subgroup.zpowers dq ⊔ Subgroup.zpowers j) = 9 :=
    card_zpowers_sup_zpowers_eq_nine (hAab dq hdA j hjAJ.1) hd3 hd1 (hA3 j hjAJ.1) hjd
  have hsub : Subgroup.zpowers dq ⊔ Subgroup.zpowers j ≤ Aq ⊓ Jq :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hdA, hdJ⟩) (Subgroup.zpowers_le.mpr hjAJ)
  by_contra hnot
  have hAJ9 : Aq ⊓ Jq = Subgroup.zpowers dq ⊔ Subgroup.zpowers j := by
    have hdvd : Nat.card ↥(Aq ⊓ Jq) ∣ 27 := hA27 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hge : 9 ≤ Nat.card ↥(Aq ⊓ Jq) := h9 ▸ Subgroup.card_le_of_le hsub
    have hne : Nat.card ↥(Aq ⊓ Jq) ≠ 27 := by
      intro h27
      apply hnot
      have heq : Aq ⊓ Jq = Aq :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hA27])
      exact heq ▸ inf_le_right
    have h9' : Nat.card ↥(Aq ⊓ Jq) = 9 := by
      rw [show (27 : ℕ) = 3 ^ 3 by norm_num] at hdvd
      obtain ⟨i, hi, hiq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      rw [hiq] at hge hne ⊢
      interval_cases i <;> simp_all
    exact (Subgroup.eq_of_le_of_card_ge hsub (by rw [h9, h9'])).symm
  set j' : ↥Jq := ⟨j, hjAJ.2⟩ with hj'
  have hj'3 : j' ^ 3 = 1 := Subtype.ext (by simpa using hA3 j hjAJ.1)
  have hj'z : j' ∉ Subgroup.center ↥Jq := by
    intro hz
    obtain ⟨y, hy, hjy⟩ := hjnc
    exact hjy (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz ⟨y, hy⟩).symm))
  obtain ⟨x, hx3, hxj, hxn⟩ := CFSG.RankThree.PartTwo.Sec13.ON134.exists_centralizer ψ hj'3 hj'z
  have hxj' : (x : Q) * j = j * x := by simpa using congrArg Subtype.val hxj
  have hxA : (x : Q) ∈ Subgroup.centralizer (Aq : Set Q) := by
    have hle : Aq ⊓ Subgroup.centralizer (Jq : Set Q) ⊔ Aq ⊓ Jq ≤
        Subgroup.centralizer ({(x : Q)} : Set Q) := by
      refine sup_le (fun a ha => ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp ha.2 x x.2).symm
      · rw [hAJ9]
        refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        · exact hdC x x.2
        · exact hxj'.symm
    rw [hCD] at hle
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  have hxAq : (x : Q) ∈ Aq := hF3 _ hxA (by simpa using congrArg Subtype.val hx3)
  have hxAJ : (x : Q) ∈ Subgroup.zpowers dq ⊔ Subgroup.zpowers j := hAJ9 ▸ ⟨hxAq, x.2⟩
  apply hxn
  set d' : ↥Jq := ⟨dq, hdJ⟩ with hd'
  have hd'Z : d' ∈ Subgroup.center ↥Jq := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hdC g g.2).symm
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hZd : Subgroup.center ↥Jq = Subgroup.zpowers d' :=
    (zpowers_eq_of_card_three hZ3 hd'Z hd'1).symm
  have hmap : (Subgroup.zpowers j' ⊔ Subgroup.center ↥Jq).map Jq.subtype =
      Subgroup.zpowers dq ⊔ Subgroup.zpowers j := by
    rw [Subgroup.map_sup, hZd, MonoidHom.map_zpowers, MonoidHom.map_zpowers, sup_comm]
    rfl
  have hx' : Jq.subtype x ∈ (Subgroup.zpowers j' ⊔ Subgroup.center ↥Jq).map Jq.subtype := by
    rw [hmap]
    exact hxAJ
  exact (Subgroup.mem_map_iff_mem Jq.subtype_injective).mp hx'

theorem alpha148_not_mem_center {A Y : Subgroup G} [(ker148 A Y).Normal]
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) {Jq : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} {d a : G} (hdA : d ∈ A)
    (hdJ : alpha148 A Y d hdA ∈ Jq) (hZ : Subgroup.center ↥Jq = Subgroup.zpowers ⟨_, hdJ⟩)
    (ha : a ∈ A) (haJ : alpha148 A Y a ha ∈ Jq) (had : a ∉ Subgroup.zpowers d) :
    (⟨alpha148 A Y a ha, haJ⟩ : ↥Jq) ∉ Subgroup.center ↥Jq := by
  intro hz
  rw [hZ] at hz
  have h1 : alpha148 A Y a ha ∈ Subgroup.zpowers (alpha148 A Y d hdA) := by
    have := Subgroup.mem_map_of_mem Jq.subtype hz
    rwa [MonoidHom.map_zpowers] at this
  apply had
  rcases inner_a5_mem_zpowers (alpha148_pow_three hA3 hdA) h1 with h | h | h
  · rw [alpha148_injective hA3 ha A.one_mem (h.trans alpha148_one'.symm)]
    exact one_mem _
  · rw [alpha148_injective hA3 ha hdA h]
    exact Subgroup.mem_zpowers d
  · rw [alpha148_injective hA3 ha (A.inv_mem hdA) (h.trans (alpha148_inv hdA).symm)]
    exact inv_mem (Subgroup.mem_zpowers d)

theorem zpowers_mem_omegaA_of_innerON {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {B Lb : Subgroup G} {b d : G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) {Jq : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hAJq : img148 A Y A ≤ Jq) (ψ : ↥Jq ≃* GM) (hdA : d ∈ A)
    (hZ : Subgroup.center ↥Jq = Subgroup.zpowers ⟨_, hAJq (alpha148_mem_img148 hdA)⟩)
    {a : G} (ha : a ∈ A) (had : a ∉ Subgroup.zpowers d) : Subgroup.zpowers a ∈ omegaA A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  have hbΩ : Subgroup.zpowers b ∈ omegaA A := hc.2.1
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
  have hbd : b ∉ Subgroup.zpowers d := by
    intro hbd'
    have hB9 : Nat.card B = 9 := by
      have := hB.2
      rw [hA.2] at this
      omega
    have hBle : B ≤ Subgroup.zpowers d := by
      rw [hc.1, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hbd'
      · exact Subgroup.mem_zpowers _
    have hcard := Subgroup.card_le_of_le hBle
    rw [hB9, Nat.card_zpowers, orderOf_eq_prime (hA3 d hdA) hd1] at hcard
    omega
  set E : Subgroup ↥Jq := (img148 A Y A).subgroupOf Jq with hE
  have hEc : Nat.card E = 27 := by
    rw [← hAE.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJq).toEquiv
  have hEe : Late.IsE27 E := by
    refine ⟨⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩, hEc⟩
    · exact hAab _ (Subgroup.mem_subgroupOf.mp x.2) _ (Subgroup.mem_subgroupOf.mp y.2)
    · exact Subtype.ext (by simpa using hAE.1.2 _ (Subgroup.mem_subgroupOf.mp hx))
  set b' : ↥Jq := ⟨alpha148 A Y b hbA, hAJq (alpha148_mem_img148 hbA)⟩ with hb'
  set a' : ↥Jq := ⟨alpha148 A Y a ha, hAJq (alpha148_mem_img148 ha)⟩ with ha'
  have hb'E : b' ∈ E := Subgroup.mem_subgroupOf.mpr (alpha148_mem_img148 hbA)
  have ha'E : a' ∈ E := Subgroup.mem_subgroupOf.mpr (alpha148_mem_img148 ha)
  obtain ⟨g, hgN, hgmap⟩ := CFSG.RankThree.PartTwo.Sec13.ON134.transitive ψ hEe hb'E ha'E
    (alpha148_not_mem_center hA3 hdA _ hZ hbA _ hbd)
    (alpha148_not_mem_center hA3 hdA _ hZ ha _ had)
  have hgA : (g : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈
      Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    refine Item148HJ.mem_normalizer_of_conj_mem fun x hx => ?_
    have hxE : (⟨x, hAJq hx⟩ : ↥Jq) ∈ E := Subgroup.mem_subgroupOf.mpr hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hgN ⟨x, hAJq hx⟩).mp hxE
    have h2 := Subgroup.mem_subgroupOf.mp h1
    simpa using h2
  obtain ⟨w, hwN, hwg⟩ := exists_normalizer_lift148 hAp hgA
  have hwbA : (w : G) * b * (w : G)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hwN b).mp hbA
  have hα : alpha148 A Y ((w : G) * b * (w : G)⁻¹) hwbA ∈
      Subgroup.zpowers (alpha148 A Y a ha) := by
    rw [alpha148_conj w hbA hwbA, hwg]
    have h1 : g * b' * g⁻¹ ∈ (Subgroup.zpowers b').map (MulAut.conj g).toMonoidHom :=
      ⟨b', Subgroup.mem_zpowers b', rfl⟩
    rw [hgmap] at h1
    have h2 := Subgroup.mem_map_of_mem Jq.subtype h1
    rw [MonoidHom.map_zpowers] at h2
    simpa using h2
  have hwba : (w : G) * b * (w : G)⁻¹ ∈ Subgroup.zpowers a := by
    rcases inner_a5_mem_zpowers (alpha148_pow_three hA3 ha) hα with h | h | h
    · rw [alpha148_injective hA3 hwbA A.one_mem (h.trans alpha148_one'.symm)]
      exact one_mem _
    · rw [alpha148_injective hA3 hwbA ha h]
      exact Subgroup.mem_zpowers a
    · rw [alpha148_injective hA3 hwbA (A.inv_mem ha) (h.trans (alpha148_inv ha).symm)]
      exact inv_mem (Subgroup.mem_zpowers a)
  have hwb1 : (w : G) * b * (w : G)⁻¹ ≠ 1 := by
    intro h0
    apply hb1
    calc b = (w : G)⁻¹ * ((w : G) * b * (w : G)⁻¹) * (w : G) := by group
      _ = 1 := by rw [h0]; group
  have ha1 : a ≠ 1 := fun h => had (h ▸ one_mem _)
  have hzz : Subgroup.zpowers ((w : G) * b * (w : G)⁻¹) = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwba) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (hA3 a ha) ha1,
        orderOf_eq_prime (hA3 _ hwbA) hwb1])
  have hΩ := (map_conj_mem_omegaA_iff (F := Subgroup.zpowers b) hwN).mpr hbΩ
  rw [MonoidHom.map_zpowers] at hΩ
  rw [← hzz]
  simpa [MulAut.conj_apply] using hΩ

theorem exists_le_img148_deltaZero_of_innerON (h142 : Concl142S14) {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) [(ker148 A Y).Normal]
    {Jq : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hJqY : Jq ≤ img148 A Y Y)
    (hAJq : img148 A Y A ≤ Jq) (ψ : ↥Jq ≃* GM) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hZ : Subgroup.center ↥Jq = Subgroup.zpowers ⟨_, hAJq (alpha148_mem_img148 hdA)⟩)
    {a : G} (ha : a ∈ A) (had : a ∉ Subgroup.zpowers d) (haΩ : Subgroup.zpowers a ∈ omegaA A) :
    ∃ K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), K ≤ Jq ∧ K ≤ img148 A Y (deltaZero A (lB A) Y) ∧
      K ≤ Subgroup.centralizer {alpha148 A Y a ha} ∧
      Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6)) ∧ Group.IsPerfect ↥K ∧
      ∃ x ∈ img148 A Y A, ∃ y ∈ K, x * y ≠ y * x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAq3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  set u := alpha148 A Y a ha with hu
  have huA : u ∈ img148 A Y A := alpha148_mem_img148 ha
  set u' : ↥Jq := ⟨u, hAJq huA⟩ with hu'
  have hu'3 : u' ^ 3 = 1 := Subtype.ext (by simpa using hAq3 u huA)
  have hu'z : u' ∉ Subgroup.center ↥Jq := alpha148_not_mem_center hA3 hdA _ hZ ha _ had
  have hu'1 : u' ≠ 1 := fun h => hu'z (h ▸ one_mem _)
  obtain ⟨K0, hK0t, hK0p, hCu, hu0, hZK⟩ :=
    Sec4.Ronan148V.exists_centralizer_eq_sup_of_ON ψ hu'3 hu'z
  have hK0C : K0 ≤ Subgroup.centralizer {u'} := hCu ▸ le_sup_right
  set E : Subgroup ↥Jq := (img148 A Y A).subgroupOf Jq with hE
  have hEc : Nat.card E = 27 := by
    rw [← hAE.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJq).toEquiv
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    Subtype.ext (hAab _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := fun x hx =>
    Subtype.ext (by simpa using hAq3 _ (Subgroup.mem_subgroupOf.mp hx))
  have hu'E : u' ∈ E := Subgroup.mem_subgroupOf.mpr huA
  set d' : ↥Jq := ⟨alpha148 A Y d hdA, hAJq (alpha148_mem_img148 hdA)⟩ with hd'
  have hd'E : d' ∈ E := Subgroup.mem_subgroupOf.mpr (alpha148_mem_img148 hdA)
  have hd'Z : d' ∈ Subgroup.center ↥Jq := hZ ▸ Subgroup.mem_zpowers d'
  have hd'K : d' ∈ K0 := hZK hd'Z
  have hd'1 : d' ≠ 1 := by
    intro h
    apply hd1
    exact alpha148_injective hA3 hdA A.one_mem ((congrArg Subtype.val h).trans alpha148_one'.symm)
  have hK0N : K0 ≤ Subgroup.normalizer (Subgroup.zpowers u' : Set ↥Jq) := by
    intro k hk
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hK0C hk)).symm i).eq
  have hdec : E = Subgroup.zpowers u' ⊔ (E ⊓ K0) := by
    refine le_antisymm (fun e he => ?_) (sup_le (Subgroup.zpowers_le.mpr hu'E) inf_le_left)
    have heC : e ∈ Subgroup.centralizer {u'} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hEab e he u' hu'E
    rw [hCu] at heC
    obtain ⟨n, hn, k, hk, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hK0N heC
    have hkE : k ∈ E := by
      have e1 : k = n⁻¹ * (n * k) := by group
      rw [e1]
      exact E.mul_mem (E.inv_mem (Subgroup.zpowers_le.mpr hu'E hn)) he
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨hkE, hk⟩)
  have hE9 : Nat.card ↥(E ⊓ K0) = 9 := by
    have hcomm : ∀ x ∈ Subgroup.zpowers u', ∀ y ∈ E ⊓ K0, x * y = y * x := by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hK0C hy.2)).symm i).eq
    have hint : Subgroup.zpowers u' ⊓ (E ⊓ K0) = ⊥ := by
      rw [eq_bot_iff, ← hu0]
      exact fun x hx => ⟨hx.1, hx.2.2⟩
    have h := card_sup_eq_mul_of_commute hcomm hint
    rw [← hdec, hEc, Nat.card_zpowers, orderOf_eq_prime hu'3 hu'1] at h
    omega
  have hd'3 : Nat.card (Subgroup.zpowers d') = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hE3 d' hd'E) hd'1]
  obtain ⟨x', hx'EK, hx'd⟩ : ∃ x' ∈ E ⊓ K0, x' ∉ Subgroup.zpowers d' := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (fun y hy => hall y hy : E ⊓ K0 ≤ Subgroup.zpowers d')
    rw [hE9, hd'3] at this
    omega
  have hxnc : ∃ y ∈ K0, x' * y ≠ y * x' := by
    by_contra hall
    push Not at hall
    set d'' : ↥K0 := ⟨d', hd'K⟩ with hd''
    have hd''Z : d'' ∈ Subgroup.center ↥K0 := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hd'Z) g)
    have hd''1 : d'' ≠ 1 := fun h => hd'1 (congrArg Subtype.val h)
    have hcen : Subgroup.center ↥K0 = Subgroup.zpowers d'' :=
      (zpowers_eq_of_card_three hK0t.1 hd''Z hd''1).symm
    have hx'Z : (⟨x', hx'EK.2⟩ : ↥K0) ∈ Subgroup.center ↥K0 := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hall g g.2).symm
    rw [hcen] at hx'Z
    apply hx'd
    have := Subgroup.mem_map_of_mem K0.subtype hx'Z
    rwa [MonoidHom.map_zpowers] at this
  have h9dx : Nat.card ↥(Subgroup.zpowers d' ⊔ Subgroup.zpowers x') = 9 :=
    card_zpowers_sup_zpowers_eq_nine (hEab d' hd'E x' hx'EK.1) (hE3 d' hd'E) hd'1
      (hE3 x' hx'EK.1) hx'd
  have hEK : E ⊓ K0 = Subgroup.zpowers d' ⊔ Subgroup.zpowers x' :=
    (Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hd'E, hd'K⟩))
        (Subgroup.zpowers_le.mpr hx'EK))
      (by rw [h9dx, hE9])).symm
  have hEgen : E = Subgroup.zpowers u' ⊔ (Subgroup.zpowers d' ⊔ Subgroup.zpowers x') := by
    rw [← hEK]
    exact hdec
  set K := K0.map Jq.subtype with hK
  have eK : ↥K0 ≃* ↥K := K0.equivMapOfInjective _ Jq.subtype_injective
  have hKt : Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6)) :=
    KFacts.KS14.isTripleCover_congr eK hK0t
  have hKp : Group.IsPerfect ↥K := by
    haveI := hK0p
    exact Group.IsPerfect.ofSurjective (f := eK.toMonoidHom) eK.surjective
  have hKJ : K ≤ Jq := Subgroup.map_subtype_le K0
  have hKC : K ≤ Subgroup.centralizer {u} := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hK0C hk))
  set xq : ↥(Y ⊔ A) ⧸ ker148 A Y := (x' : ↥(Y ⊔ A) ⧸ ker148 A Y) with hxq
  have hxqA : xq ∈ img148 A Y A := Subgroup.mem_subgroupOf.mp hx'EK.1
  have hxqK : xq ∈ K := ⟨x', hx'EK.2, rfl⟩
  have hxqnc : ∃ y ∈ K, xq * y ≠ y * xq := by
    obtain ⟨y, hyK, hxy⟩ := hxnc
    exact ⟨y, ⟨y, hyK, rfl⟩, fun h => hxy (Subtype.ext h)⟩
  have hAgen : img148 A Y A = Subgroup.zpowers u ⊔
      (Subgroup.zpowers (alpha148 A Y d hdA) ⊔ Subgroup.zpowers xq) := by
    have h1 : E.map Jq.subtype = img148 A Y A := by
      rw [hE, Subgroup.subgroupOf_map_subtype, inf_of_le_left hAJq]
    rw [← h1, hEgen, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hKX : K ≤ img148 A Y (deltaZero A (lB A) Y) := by
    refine le_of_forall_commutator_le_tripleCover hKt hKp hxqK (hAq3 xq hxqA) hxqnc ?_
    intro V hVK hV3 hxV
    have hAV : img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      rw [hAgen]
      refine sup_le ?_ (sup_le ?_ (Subgroup.zpowers_le.mpr hxV))
      · rw [Subgroup.zpowers_le]
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact Subgroup.mem_centralizer_singleton_iff.mp (hKC (hVK hv))
      · rw [Subgroup.zpowers_le]
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hvJ : v ∈ Jq := hKJ (hVK hv)
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hd'Z) ⟨v, hvJ⟩)
    have hVb : V ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({a} : Set G)) := fun v hv =>
      img148_inf_centralizer_le hY.2 ha (hA3 a ha) ⟨hJqY (hKJ (hVK hv)), hKC (hVK hv)⟩
    exact (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hxqA)).trans
      (commutator_le_img148_deltaZero_of_point h142 hS hY haΩ V hVb hV3 hAV)
  exact ⟨K, hKJ, hKX, hKC, hKt, hKp, xq, hxqA, hxqnc⟩

end ON

section Certificates



theorem img148_le_deltaZero_of_innerON (h142 : Concl142S14) {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) [(ker148 A Y).Normal]
    {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hdJ : d ∈ J) (hdc : d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y))
    (hJON : Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON) :
    img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) := by
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  obtain ⟨-, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hJp : Group.IsPerfect ↥(img148 A Y J) := by
    have : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
    exact isPerfect_img148 hJM
  obtain ⟨ψ⟩ := CFSG.RankThree.PartTwo.Sec13.ON134.nonempty_equiv_model hJp hJON
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAq3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  set dα := alpha148 A Y d hdA with hdαdef
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hdJα : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdJ, rfl⟩
  have hdα1 : dα ≠ 1 := by
    intro h
    apply hd1
    exact alpha148_injective hA3 hdA (Subgroup.one_mem A) (by rw [← hdαdef, h]; rfl)
  have hdJ' := HJRes2.le_centralizer_of_mem_sectionCentralizer hdA hdc
  have hdC : ∀ x ∈ img148 A Y J, dα * x = x * dα := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hdJ' hx)).symm
  have hAJα : img148 A Y A ≤ img148 A Y J :=
    le_of_ON hAab hAq3 hF3 hAE.2 (img148_le_normalizer hAJ) ψ hJON.1 hdαA hdJα hdα1 hdC
  have hZ : Subgroup.center ↥(img148 A Y J) =
      Subgroup.zpowers ⟨_, hAJα (alpha148_mem_img148 hdA)⟩ := by
    have hd'Z : (⟨dα, hdJα⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hdC g g.2).symm
    exact (zpowers_eq_of_card_three hJON.1 hd'Z fun h => hdα1 (congrArg Subtype.val h)).symm
  set E : Subgroup ↥(img148 A Y J) := (img148 A Y A).subgroupOf (img148 A Y J) with hE
  have hEc : Nat.card E = 27 := by
    rw [← hAE.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJα).toEquiv
  have hEe : Late.IsE27 E := by
    refine ⟨⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩, hEc⟩
    · exact hAab _ (Subgroup.mem_subgroupOf.mp x.2) _ (Subgroup.mem_subgroupOf.mp y.2)
    · exact Subtype.ext (by simpa using hAq3 _ (Subgroup.mem_subgroupOf.mp hx))
  set 𝒦 : Set (Subgroup ↥(img148 A Y J)) := {K | K.map (img148 A Y J).subtype ≤
    img148 A Y (deltaZero A (lB A) Y)} with h𝒦def
  have hgen : sSup 𝒦 = ⊤ := by
    refine Ronan148D.onTripleGenE27 ↥(img148 A Y J) hJp hJON E hEe 𝒦 fun u hu huz => ?_
    have huA : (u : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y A := Subgroup.mem_subgroupOf.mp hu
    obtain ⟨a, haM, haA, hau⟩ := mem_img148_iff.mp huA
    have hαa : alpha148 A Y a haA = u := (alpha148_eq_mk' haA).trans hau
    have had : a ∉ Subgroup.zpowers d := by
      intro had
      apply huz
      rw [hZ]
      have hdz : alpha148 A Y a haA ∈ Subgroup.zpowers dα := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp had
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        rw [hdαdef, alpha148_eq_mk', alpha148_eq_mk', ← map_zpow]
        rfl
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdz
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_zpow]
      rw [hk]
      exact hαa
    have haΩ := zpowers_mem_omegaA_of_innerON hS hB hc hAJα ψ hdA hZ haA had
    obtain ⟨K, hKJ, hKX, hKC, hKt, hKp, x, hxA, y, hyK, hxy⟩ :=
      exists_le_img148_deltaZero_of_innerON h142 hS hY (img148_mono hJY) hAJα ψ hdA hd1 hZ haA
        had haΩ
    have eKK : ↥(K.subgroupOf (img148 A Y J)) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKJ
    refine ⟨K.subgroupOf (img148 A Y J), ?_, ?_, ?_, ?_, ?_⟩
    · show (K.subgroupOf (img148 A Y J)).map (img148 A Y J).subtype ≤ _
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hKJ]
      exact hKX
    · intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hKC (Subgroup.mem_subgroupOf.mp hk))
      rw [hαa] at h
      simpa using h
    · haveI := hKp
      exact Group.IsPerfect.ofSurjective (f := eKK.symm.toMonoidHom) eKK.symm.surjective
    · rw [Nat.card_congr eKK.toEquiv, HJRes2.card_of_isTripleCover_six hKt]
    · intro hEC
      have hxE : (⟨x, hAJα hxA⟩ : ↥(img148 A Y J)) ∈ E := Subgroup.mem_subgroupOf.mpr hxA
      have hyK' : (⟨y, hKJ hyK⟩ : ↥(img148 A Y J)) ∈ K.subgroupOf (img148 A Y J) :=
        Subgroup.mem_subgroupOf.mpr hyK
      have h := Subgroup.mem_centralizer_iff.mp (hEC hxE) _ hyK'
      apply hxy
      exact (congrArg Subtype.val h).symm
  have hle' : sSup 𝒦 ≤ (img148 A Y (deltaZero A (lB A) Y)).subgroupOf (img148 A Y J) :=
    sSup_le fun K hK k hk => Subgroup.mem_subgroupOf.mpr (hK ⟨k, hk, rfl⟩)
  intro x hx
  have hxK : (⟨x, hx⟩ : ↥(img148 A Y J)) ∈ sSup 𝒦 := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp (hle' hxK)

theorem step148HJNormalInnerONCent3_holds (h142 : Concl142S14) :
    Step148HJNormalInnerONCent3 := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJON hdYd hXJ hnJX hXle
  let := ker148_normal hY.2
  exact (hnJX (img148_le_deltaZero_of_innerON h142 hS hY hB hc hJ hAJ (hYdJ hdYd) hdc hJON)).elim

theorem step148HJNormalInnerONCent2_holds (h142 : Concl142S14) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h143 : Ronan148Q.Item143QS14) :
    Ronan148A.Step148HJNormalInnerONCent2 :=
  step148HJNormalInnerONCent2_of_cent3 h134 h48 h143 (step148HJNormalInnerONCent3_holds h142)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
