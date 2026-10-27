module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T1
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.N588T

open Subgroup CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)
open CFSG.LocalAnalysis.RankThreeTheoremC (KFactInnerAction KFactWeakClosure)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree (DichThree CentralFusionAt)

section Generic

variable {X : Type} [Group X] [Finite X]

theorem exists_conj_eq_of_not_dvd (hout : ¬ 3 ∣ Nat.card (Outer X)) {α : MulAut X}
    (hα : α ^ 3 = 1) : ∃ j : X, MulAut.conj j = α := by
  have h1 : (QuotientGroup.mk' (inner X) α) ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have h2 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1)
    (orderOf_dvd_natCard (QuotientGroup.mk' (inner X) α))
  have hcop : Nat.Coprime 3 (Nat.card (Outer X)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hout
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at h2
  obtain ⟨j, hj⟩ := (QuotientGroup.eq_one_iff _).mp h2
  exact ⟨j, hj⟩

theorem isPGroup_zpowers_of_pow {j : X} (hj : j ^ 3 = 1) : IsPGroup 3 (zpowers j) := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hj) with h1 | h3
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3, pow_one])

theorem two_le_pRank_of_not_isCyclic {T : Subgroup X} (hT : IsPGroup 3 T) (hnc : ¬ IsCyclic T) :
    2 ≤ CFSG.Open.pRank 3 T := by
  haveI : Fact (IsPGroup 3 T) := ⟨hT⟩
  obtain ⟨E, -, hEcard, hEel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  haveI := hEel
  refine CFSG.SectionRank.le_pRank (by norm_num) (Subgroup.map_subtype_le E)
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mp
      CFSG.IsElementaryAbelian.map_subtype) ?_
  rw [Subgroup.card_map_of_injective T.subtype_injective, hEcard]

theorem map_conj_zpowers_eq {j g : X} (h : g * j * g⁻¹ ∈ zpowers j) :
    (zpowers j).map (MulAut.conj g).toMonoidHom = zpowers j := by
  have hle : (zpowers j).map (MulAut.conj g).toMonoidHom ≤ zpowers j := by
    rw [MonoidHom.map_zpowers]
    exact (Subgroup.zpowers_le).mpr (by simpa [MulAut.conj_apply] using h)
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

theorem false_of_weakClosure (hWC : KFactWeakClosure) [IsSimpleGroup X]
    (hK : CFSG.Open.IsKGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) (hc : center X = ⊥)
    (hdvd : 3 ∣ Nat.card X) {T : Subgroup X} (hT : IsSylowOf 3 T ⊤) (hab : IsMulCommutative T)
    (h2 : 2 ≤ CFSG.Open.pRank 3 T) {j : X} (hjT : j ∈ T) (hjo : orderOf j = 3)
    (hkey : ∀ k : X, k⁻¹ * j * k ∈ T → k⁻¹ * j * k ∈ zpowers j) : False := by
  obtain ⟨P, hP⟩ := N588A.exists_sylow_of_isSylowOf_top hT
  haveI : IsSimpleGroup (⊤ : Subgroup X) := (Subgroup.topEquiv (G := X)).isSimpleGroup
  have hnab' : ∃ a b : (⊤ : Subgroup X), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun e => hab (congrArg Subtype.val e)⟩
  have hcat : CFSG.Open.IsCatalogGroup (⊤ : Subgroup X) :=
    hK.isCatalogGroup_of_surjective ⊤ hnab' (MonoidHom.id _) Function.surjective_id
  have hcen : Subgroup.centralizer ((⊤ : Subgroup X) : Set X) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hc]
  have hdvd' : 3 ∣ Nat.card (⊤ : Subgroup X) := by rw [Subgroup.card_top]; exact hdvd
  obtain ⟨g, hg1, hg2⟩ := hWC 3 Nat.prime_three (by norm_num) X ⊤ inferInstance inferInstance
    hnab' hcat hcen hdvd' P (top_sup_eq _) (hP ▸ hab) (by rw [inf_top_eq, hP]; exact h2)
    (zpowers j) (by rw [hP]; exact (Subgroup.zpowers_le).mpr hjT)
    (by rw [Nat.card_zpowers, hjo])
  apply hg2
  have hgj : g * j * g⁻¹ ∈ T := by
    rw [← hP]
    exact hg1 ⟨j, Subgroup.mem_zpowers j, by simp [MulAut.conj_apply]⟩
  exact map_conj_zpowers_eq (by simpa using hkey g⁻¹ (by simpa using hgj))

theorem false_of_isCyclic (hperf : Group.IsPerfect X) (hdvd : 3 ∣ Nat.card X) {T : Subgroup X}
    (hT : IsSylowOf 3 T ⊤) (hTc : IsCyclic T) {j : X} (hjT : j ∈ T) (hjo : orderOf j = 3)
    (hkey : ∀ n ∈ Subgroup.normalizer (T : Set X), n * j = j * n) : False := by
  have hNC : Subgroup.normalizer (T : Set X) ≤ Subgroup.centralizer (T : Set X) := by
    intro n hn
    have hTC : T ≤ Subgroup.centralizer (T : Set X) := fun x hx => by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact N588A.mul_comm_of_isCyclic hTc hy hx
    have hCN : Subgroup.centralizer (T : Set X) ≤ Subgroup.normalizer (T : Set X) :=
      Subgroup.centralizer_le_normalizer _
    have hCnormal : ((Subgroup.centralizer (T : Set X)).subgroupOf
        (Subgroup.normalizer (T : Set X))).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      have hgy : ((g : X))⁻¹ * y * g ∈ T := (Subgroup.mem_normalizer_iff''.mp g.2 y).mp hy
      have hxy := hx _ hgy
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc y * (g * x * (g : X)⁻¹) = g * ((((g : X))⁻¹ * y * g) * x) * (g : X)⁻¹ := by group
        _ = g * (x * (((g : X))⁻¹ * y * g)) * (g : X)⁻¹ := by rw [hxy]
        _ = g * x * (g : X)⁻¹ * y := by group
    have hnm : n ^ ((Subgroup.centralizer (T : Set X)).subgroupOf
        (Subgroup.normalizer (T : Set X))).index ∈ Subgroup.centralizer (T : Set X) := by
      have hpow := Subgroup.pow_index_mem ((Subgroup.centralizer (T : Set X)).subgroupOf
        (Subgroup.normalizer (T : Set X))) (⟨n, hn⟩ : Subgroup.normalizer (T : Set X))
      simpa using Subgroup.mem_subgroupOf.mp hpow
    have hm : ¬ 3 ∣ ((Subgroup.centralizer (T : Set X)).subgroupOf
        (Subgroup.normalizer (T : Set X))).index := by
      have hsylN : IsSylowOf 3 T (Subgroup.normalizer (T : Set X)) :=
        hT.of_le (hTC.trans hCN) le_top
      have hidx := (isSylowOf_iff.mp hsylN).2.2
      rw [← Subgroup.relIndex_mul_relIndex T _ _ hTC hCN] at hidx
      exact fun hd => hidx (dvd_mul_of_dvd_right hd _)
    exact N588A.mem_centralizer_of_isCyclic Nat.prime_three ⟨1, rfl⟩ hTc hT.isPGroup hn hm hnm
      hjT hjo (hkey n hn)
  obtain ⟨P, hP⟩ := N588A.exists_sylow_of_isSylowOf_top hT
  have hPT : (P : Set X) = (T : Set X) := congrArg (fun H : Subgroup X => (H : Set X)) hP
  have hNC' : Subgroup.normalizer (P : Set X) ≤ Subgroup.centralizer (P : Set X) := by
    rw [hPT]
    exact hNC
  exact N588A.not_dvd_card_of_normalizer_le_centralizer hperf P hNC' hdvd

theorem false_of_centralFusion (hF : CentralFusionAt X) {T : Subgroup X} (hT : IsSylowOf 3 T ⊤)
    {j : X} (hjT : j ∈ T) (hjo : orderOf j = 3) (hjc : ∀ t ∈ T, j * t = t * j)
    (hkey : ∀ k : X, k⁻¹ * j * k ∈ T → k⁻¹ * j * k ∈ zpowers j) : False := by
  obtain ⟨P, hP⟩ := N588A.exists_sylow_of_isSylowOf_top hT
  obtain ⟨g, hgN, hg⟩ := hF.2 P (zpowers j) (by rw [hP]; exact (Subgroup.zpowers_le).mpr hjT)
    (fun a ha t ht => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (hjc t (hP ▸ ht)) i).eq)
    (by rw [Nat.card_zpowers, hjo])
  apply hg
  have hgj : g * j * g⁻¹ ∈ T := by
    rw [← hP]
    exact (Subgroup.mem_normalizer_iff.mp hgN j).mp (hP ▸ hjT)
  exact map_conj_zpowers_eq (by simpa using hkey g⁻¹ (by simpa using hgj))

end Generic

namespace Hyp3

variable {G : Type} [Group G] [Finite G] {S Z : Subgroup G}

theorem not_hasNoncommPair (h : Hyp3 G S Z) : ¬ HasNoncommPair 3 G := by
  rintro ⟨x, y, hx, hy, hxy, hQ⟩
  obtain ⟨g, hg⟩ := N588A.exists_le_conjugate h.sylow hQ
  have hxS : g * x * g⁻¹ ∈ S :=
    N588A.mem_conjugate_iff.mp (hg (Subgroup.subset_closure (Set.mem_insert x {y})))
  have hyS : g * y * g⁻¹ ∈ S := N588A.mem_conjugate_iff.mp
    (hg (Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))))
  have hx' : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx, mul_one, mul_inv_cancel]
  have hy' : (g * y * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hy, mul_one, mul_inv_cancel]
  have hc := h.omega _ hxS hx' _ hyS hy'
  apply hxy
  have e : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
    calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      _ = (g * y * g⁻¹) * (g * x * g⁻¹) := hc
      _ = g * (y * x) * g⁻¹ := by group
  simpa using mul_left_cancel (mul_right_cancel e)

theorem exists_decomp (h : Hyp3 G S Z) {J : Subgroup G}
    (hJC : J ⊓ Subgroup.centralizer (J : Set G) = ⊥) {z j : G} (hzZ : z ∈ Z) (hjJ : j ∈ J)
    (hjS : j ∈ S) (hjx : ∀ x ∈ J, j * x * j⁻¹ = z * x * z⁻¹) :
    ∃ c : G, z = j * c ∧ c ∈ Subgroup.centralizer (J : Set G) ∧ c ∈ S ∧ c ^ 3 = 1 ∧
      j ^ 3 = 1 := by
  set c : G := j⁻¹ * z with hc
  have hzeq : z = j * c := by rw [hc, mul_inv_cancel_left]
  have hcJ : c ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have e := hjx x hx
    calc x * c = j⁻¹ * (j * x * j⁻¹) * z := by rw [hc]; group
      _ = j⁻¹ * (z * x * z⁻¹) * z := by rw [e]
      _ = c * x := by rw [hc]; group
  have hcomm : Commute j c := Subgroup.mem_centralizer_iff.mp hcJ j hjJ
  have hcS : c ∈ S := S.mul_mem (S.inv_mem hjS) (h.le hzZ)
  have hz3 := h.pow_eq_one hzZ
  rw [hzeq, hcomm.mul_pow] at hz3
  have hj3 : j ^ 3 = 1 := by
    have hjc : j ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hz3
    have hmem : j ^ 3 ∈ J ⊓ Subgroup.centralizer (J : Set G) :=
      ⟨J.pow_mem hjJ 3, hjc ▸ Subgroup.inv_mem _ (Subgroup.pow_mem _ hcJ 3)⟩
    rwa [hJC, Subgroup.mem_bot] at hmem
  have hc3 : c ^ 3 = 1 := by rwa [hj3, one_mul] at hz3
  exact ⟨c, hzeq, hcJ, hcS, hc3, hj3⟩

theorem conj_mem_zpowers (h : Hyp3 G S Z) {J : Subgroup G}
    (hJC : J ⊓ Subgroup.centralizer (J : Set G) = ⊥) {z j c : G} (hZz : Z = zpowers z)
    (hzeq : z = j * c) (hjJ : j ∈ J) (hcJ : c ∈ Subgroup.centralizer (J : Set G))
    (hcS : c ∈ S) (hc3 : c ^ 3 = 1) (hj3 : j ^ 3 = 1) {k : G} (hkJ : k ∈ J)
    (hk : k⁻¹ * j * k ∈ S) : ∃ i : ℤ, k⁻¹ * j * k = j ^ i ∧ (c ≠ 1 → k⁻¹ * j * k = j) := by
  have hck : k⁻¹ * c * k = c := by
    have e : k * c = c * k := Subgroup.mem_centralizer_iff.mp hcJ k hkJ
    calc k⁻¹ * c * k = k⁻¹ * (c * k) := by group
      _ = k⁻¹ * (k * c) := by rw [e]
      _ = c := by group
  have hzk : k⁻¹ * z * k = (k⁻¹ * j * k) * c := by
    calc k⁻¹ * z * k = (k⁻¹ * j * k) * (k⁻¹ * c * k) := by rw [hzeq]; group
      _ = (k⁻¹ * j * k) * c := by rw [hck]
  have hzkS : k⁻¹ * z * k ∈ S := by
    rw [hzk]
    exact S.mul_mem hk hcS
  have hZk : CFSG.conjugate Z k ≤ S := by
    intro x hx
    rw [N588A.mem_conjugate_iff, hZz] at hx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
    have e : x = (k⁻¹ * z * k) ^ i := by
      rw [show k⁻¹ * z * k = k⁻¹ * z * k⁻¹⁻¹ by rw [inv_inv], conj_zpow, hi]
      group
    rw [e]
    exact S.zpow_mem hzkS i
  have hZk' := h.wc k hZk
  have hzkZ : k⁻¹ * z * k ∈ Z := by
    rw [← hZk', N588A.mem_conjugate_iff]
    have hzZ : z ∈ Z := hZz ▸ Subgroup.mem_zpowers z
    simpa [mul_assoc] using hzZ
  rw [hZz] at hzkZ
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hzkZ
  have hcomm : Commute j c := Subgroup.mem_centralizer_iff.mp hcJ j hjJ
  rw [hzk, hzeq, hcomm.mul_zpow] at hi
  have hkey : (j ^ i)⁻¹ * (k⁻¹ * j * k) = c ^ (i - 1) := by
    have e1 : k⁻¹ * j * k = j ^ i * c ^ i * c⁻¹ := by rw [hi, mul_inv_cancel_right]
    rw [e1, zpow_sub_one]
    group
  have hmem : c ^ (i - 1) ∈ J ⊓ Subgroup.centralizer (J : Set G) := by
    refine ⟨?_, Subgroup.zpow_mem _ hcJ _⟩
    rw [← hkey]
    exact J.mul_mem (J.inv_mem (J.zpow_mem hjJ i))
      (J.mul_mem (J.mul_mem (J.inv_mem hkJ) hjJ) hkJ)
  rw [hJC, Subgroup.mem_bot] at hmem
  rw [hmem] at hkey
  have e2 : k⁻¹ * j * k = j ^ i := by
    rw [← mul_one (j ^ i), ← hkey, mul_inv_cancel_left]
  refine ⟨i, e2, fun hc1 => ?_⟩
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hdvd : ((orderOf c : ℕ) : ℤ) ∣ i - 1 := orderOf_dvd_iff_zpow_eq_one.mpr hmem
  rw [hco] at hdvd
  have hti : j ^ (i - 1) = 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.mp
    exact (Int.natCast_dvd_natCast.mpr (orderOf_dvd_of_pow_eq_one hj3)).trans hdvd
  rw [e2]
  calc j ^ i = j ^ (i - 1) * j := by rw [← zpow_add_one, sub_add_cancel]
    _ = j := by rw [hti, one_mul]

theorem le_and_isCyclic (hM3 : UCK.KMult3Ab) (hD : DichThree) (hIA : KFactInnerAction)
    (hWC : KFactWeakClosure) (h : Hyp3 G S Z) (hcore : CFSG.pPrimeCore 3 G = ⊥)
    {J : Subgroup G} (hJ : CFSG.IsComponent J)
    (hZJ : ¬ Z ≤ Subgroup.centralizer (J : Set G)) :
    Z ≤ J ∧ IsCyclic (S.subgroupOf J) := by
  have hc := h.center_eq_bot hM3 hcore hJ
  haveI hs : IsSimpleGroup J := N588A.isSimpleGroup_of_center_eq_bot hJ.1.2.1 hc
  have hnab := exists_ne_of_isComponent hJ
  have hKJ : CFSG.Open.IsKGroup J := h.isKGroup.subgroup J
  have hcat : CFSG.Open.IsCatalogGroup J :=
    h.isKGroup.isCatalogGroup_of_surjective J hnab (MonoidHom.id J) Function.surjective_id
  have hdvd := dvd_card_of_isComponent hcore hJ
  have hJC := N588A.Hyp.inf_centralizer_eq_bot hc
  have hTsyl := h.isSylowOf_subgroupOf hJ.2
  obtain ⟨z, hzZ, hz1⟩ := (Subgroup.bot_or_exists_ne_one Z).resolve_left h.ne_bot
  have hZz := h.eq_zpowers hzZ hz1
  have hzN : z ∈ Subgroup.normalizer (J : Set G) := h.le_normalizer_of_isComponent hcore hJ hzZ
  set α : MulAut J := J.normalizerMonoidHom ⟨z, hzN⟩ with hα
  have hαx : ∀ x : J, ((α x : J) : G) = z * x * z⁻¹ := fun x => rfl
  have hα3 : α ^ 3 = 1 := by
    have hz3 : (⟨z, hzN⟩ : Subgroup.normalizer (J : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using h.pow_eq_one hzZ)
    rw [hα, ← map_pow, hz3, map_one]
  have hαT : ∀ x ∈ S.subgroupOf J, α x = x := fun x hx => Subtype.ext (by
    rw [hαx, h.comm hzZ (Subgroup.mem_subgroupOf.mp hx), mul_inv_cancel_right])
  obtain ⟨j, hjα, hjT, hcase⟩ : ∃ j : J, MulAut.conj j = α ∧ j ∈ S.subgroupOf J ∧
      (IsMulCommutative (S.subgroupOf J) ∨ CentralFusionAt J) := by
    by_cases hab : IsMulCommutative (S.subgroupOf J)
    · obtain ⟨P, hP⟩ := N588A.exists_sylow_of_isSylowOf_top hTsyl
      obtain ⟨g, hgP, hg⟩ := hIA 3 Nat.prime_three (by norm_num) J hs hnab hcat P
        (P.ne_bot_of_dvd_card hdvd) (hP ▸ hab) α ⟨1, by rw [pow_one]; exact hα3⟩
        (fun g hg => by
          ext x
          simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
            hαT g (hP ▸ hg)])
      exact ⟨g, hg.symm, hP ▸ hgP, Or.inl hab⟩
    · rcases (hD J hs hnab hcat hdvd).1 with hall | hpair | hrank | hfus
      · obtain ⟨P, hP⟩ := N588A.exists_sylow_of_isSylowOf_top hTsyl
        exact absurd (hP ▸ hall P) hab
      · exact absurd (hpair.map J.subtype J.subtype_injective) h.not_hasNoncommPair
      · exact absurd hrank (by have := h.pRank_top_le_three J; omega)
      · obtain ⟨j, hj⟩ := exists_conj_eq_of_not_dvd hfus.1 hα3
        refine ⟨j, hj, ?_, Or.inr hfus⟩
        have hj3 : j ^ 3 = 1 := by
          have h1 : MulAut.conj (j ^ 3) = 1 := by rw [map_pow, hj, hα3]
          have h2 : j ^ 3 ∈ center J := by
            rw [Subgroup.mem_center_iff]
            intro y
            have e := congrArg (fun f : MulAut J => f y) h1
            simp only [MulAut.conj_apply, MulAut.one_apply] at e
            calc y * j ^ 3 = j ^ 3 * y * (j ^ 3)⁻¹ * j ^ 3 := by rw [e]
              _ = j ^ 3 * y := by group
          rw [hc, Subgroup.mem_bot] at h2
          exact h2
        have hjc : ∀ t ∈ S.subgroupOf J, t * j = j * t := fun t ht => by
          have e := hαT t ht
          rw [← hj, MulAut.conj_apply] at e
          calc t * j = j * t * j⁻¹ * j := by rw [e]
            _ = j * t := by group
        have hN : zpowers j ≤ Subgroup.normalizer ((S.subgroupOf J : Subgroup J) : Set J) :=
          ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_iff.mpr hjc)).trans
            (Subgroup.centralizer_le_normalizer _)
        have hQ := IsPGroup.to_sup_of_normal_left' hTsyl.isPGroup (isPGroup_zpowers_of_pow hj3) hN
        have heq := hTsyl.eq_of_le le_sup_left le_top hQ
        exact heq ▸ (le_sup_right : zpowers j ≤ S.subgroupOf J ⊔ zpowers j) (mem_zpowers j)
  have hjx : ∀ x ∈ J, (j : G) * x * (j : G)⁻¹ = z * x * z⁻¹ := fun x hx => by
    have e := congrArg (fun f : MulAut J => ((f ⟨x, hx⟩ : J) : G)) hjα
    simpa [MulAut.conj_apply, hαx] using e
  have hjc : ∀ t ∈ S.subgroupOf J, j * t = t * j := fun t ht => by
    have e := hαT t ht
    rw [← hjα, MulAut.conj_apply] at e
    calc j * t = j * t * j⁻¹ * j := by group
      _ = t * j := by rw [e]
  have hjS : (j : G) ∈ S := Subgroup.mem_subgroupOf.mp hjT
  obtain ⟨c, hzeq, hcJ, hcS, hc3, hj3⟩ := h.exists_decomp hJC hzZ j.2 hjS hjx
  have hj1 : j ≠ 1 := by
    intro hj1
    apply hZJ
    rw [hZz, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    have e := hjx x hx
    rw [hj1, Subgroup.coe_one, one_mul, inv_one, mul_one] at e
    calc x * z = z * x * z⁻¹ * z := by rw [← e]
      _ = z * x := by group
  have hjo : orderOf j = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hj3)) hj1
  have hkeyZ : ∀ k : J, k⁻¹ * j * k ∈ S.subgroupOf J → k⁻¹ * j * k ∈ zpowers j := by
    intro k hk
    obtain ⟨i, hi, -⟩ := h.conj_mem_zpowers hJC hZz hzeq j.2 hcJ hcS hc3 hj3 k.2
      (by simpa using Subgroup.mem_subgroupOf.mp hk)
    exact ⟨i, Subtype.ext (by simp [hi])⟩
  have hkeyN : c ≠ 1 → ∀ n ∈ Subgroup.normalizer ((S.subgroupOf J : Subgroup J) : Set J),
      n * j = j * n := by
    intro hc1 n hn
    have hnj : n⁻¹ * j * n ∈ S.subgroupOf J := (Subgroup.mem_normalizer_iff''.mp hn j).mp hjT
    obtain ⟨-, -, hfix⟩ := h.conj_mem_zpowers hJC hZz hzeq j.2 hcJ hcS hc3 hj3 n.2
      (by simpa using Subgroup.mem_subgroupOf.mp hnj)
    have e : (n : G)⁻¹ * j * n = j := hfix hc1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (n : G) * j = n * ((n : G)⁻¹ * j * n) := by rw [e]
      _ = j * n := by group
  rcases hcase with hab | hfus
  · by_cases hTc : IsCyclic (S.subgroupOf J)
    · by_cases hc1 : c = 1
      · refine ⟨?_, hTc⟩
        rw [hZz, Subgroup.zpowers_le, hzeq, hc1, mul_one]
        exact j.2
      · exact (false_of_isCyclic hJ.1.1 hdvd hTsyl hTc hjT hjo (hkeyN hc1)).elim
    · exact (false_of_weakClosure hWC hKJ hnab hc hdvd hTsyl hab
        (two_le_pRank_of_not_isCyclic hTsyl.isPGroup hTc) hjT hjo hkeyZ).elim
  · exact (false_of_centralFusion hfus hTsyl hjT hjo hjc hkeyZ).elim

end Hyp3

end CFSG.LocalAnalysis.UniquenessCase.UCK.N588T
