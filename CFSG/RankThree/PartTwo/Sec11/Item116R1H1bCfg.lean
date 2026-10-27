module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1CD
public import CFSG.RankThree.PartTwo.Sec11.Item116R1H1bPure
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient

public section

section

open CFSG Subgroup CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta
open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartTwo.Sec11

section Certified


@[expose] def ZElement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      ResidueR1 G A c a d → IsSurvivingCase L →
        ∃ (z : G) (v k : ℕ), z ∈ L ∧ 2 ≤ v ∧ orderOf z = 3 ^ v ∧ z ^ 3 ^ (v - 1) = d ∧
          z * c = c * z ∧ z * d = d * z ∧ a * z * a⁻¹ = z ^ k ∧
          3 ^ (v - 1) ∣ k - 1 ∧ ¬ 3 ^ v ∣ k - 1

end Certified

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta
open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartTwo.Sec11

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem h1b_map_normalized_by_centralizer {H : Type*} [Group H] [Finite H] (N0 : Subgroup H)
    [N0.Normal] (hN0 : ¬ 3 ∣ Nat.card N0) {x : H} (hx3 : x ^ 3 = 1) (S : Subgroup H)
    (hS : ∀ g ∈ Subgroup.centralizer ({x} : Set H), ∀ s ∈ S, g * s * g⁻¹ ∈ S) :
    ∀ g ∈ Subgroup.centralizer ({(QuotientGroup.mk' N0 x : H ⧸ N0)} : Set (H ⧸ N0)),
      ∀ n ∈ S.map (QuotientGroup.mk' N0), g * n * g⁻¹ ∈ S.map (QuotientGroup.mk' N0) := by
  have hA : IsPGroup 3 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hx3
  have hcen := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 N0 hN0
    (Subgroup.zpowers x) hA
  intro g hg n hn
  have hg' : g ∈ Subgroup.centralizer
      (((Subgroup.zpowers x).map (QuotientGroup.mk' N0) : Subgroup (H ⧸ N0)) : Set (H ⧸ N0)) := by
    rw [MonoidHom.map_zpowers, aq_centralizer_zpowers_eq]
    exact hg
  rw [← hcen] at hg'
  obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hg'
  rw [aq_centralizer_zpowers_eq] at hg₀
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hn
  have key : QuotientGroup.mk' N0 g₀ * QuotientGroup.mk' N0 s * (QuotientGroup.mk' N0 g₀)⁻¹ =
      QuotientGroup.mk' N0 (g₀ * s * g₀⁻¹) := by
    simp only [map_mul, map_inv]
  rw [key]
  exact Subgroup.mem_map_of_mem _ (hS g₀ hg₀ s hs)

theorem not_three_dvd_orderOf_of_mem_thetaCent (p : G) {s : G} (hs : s ∈ thetaCent p) :
    ¬ 3 ∣ orderOf s := by
  unfold thetaCent inSubgroup at hs
  obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp hs
  have h3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 (CAt p)) :=
    (solvable_prime_complement_core_characterization (H := CAt p) Nat.prime_three).2.2.1
  subst hts
  show ¬ 3 ∣ orderOf (t : G)
  rw [Subgroup.orderOf_coe]
  intro hdvd
  exact h3 (dvd_trans hdvd (Subgroup.orderOf_dvd_natCard _ ht))

theorem h1b_step3 (hP2b : Item116P2b) (hP2c : Item116P2c) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) (hR1 : ResidueR1 G A c a d) :
    ∀ x ∈ thetaCent (c * d), x * a = a * x → x * c * x⁻¹ * c⁻¹ ∈ thetaCent a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hD8, n, hnW, hnc, hnd, hna⟩ := hR1
  obtain ⟨K₁, K₂, h1, h2, hne, hZ1, hZ2, hdK, hcK, -, -⟩ :=
    aComponentData hP2b hP2c h45 h hT hD8 hnW hnc hnd hna
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcA : c ∈ A := h.mem_A
  have hdA : d ∈ A := h.d_mem
  have haA : a ∈ A := h.a_mem
  have hc1 : c ≠ 1 := h.ne_one
  have hd1 : d ≠ 1 := fun h1' => h.not_mem_zpowers (h1' ▸ Subgroup.one_mem _)
  have hcC : c ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c hcA a haA)
  have hdC : d ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm d hdA a haA)
  obtain ⟨c', hc'⟩ : ∃ x : CAt a, (x : G) = c := ⟨⟨c, hcC⟩, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ x : CAt a, (x : G) = d := ⟨⟨d, hdC⟩, rfl⟩
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simp [hc', hexp c hcA])
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simp [hd', hexp d hdA])
  have hc'1 : c' ≠ 1 := fun h1' => hc1 (by rw [← hc', h1', Subgroup.coe_one])
  have hd'1 : d' ≠ 1 := fun h1' => hd1 (by rw [← hd', h1', Subgroup.coe_one])
  have hc'd : c' * d' = d' * c' := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc', hd']
    exact hcomm c hcA d hdA)
  have hcd'3 : (c' * d') ^ 3 = 1 := by
    rw [(show Commute c' d' from hc'd).mul_pow 3, hc'3, hd'3, mul_one]
  have h3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 (CAt a)) :=
    (solvable_prime_complement_core_characterization (H := CAt a) Nat.prime_three).2.2.1
  have hqc3 : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) c' : QAt a) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hc'3, map_one])
      (mk_ne_one_of_pow_three (aschbacherSolvableCore 3 (CAt a)) h3 hc'3 hc'1)
  have hqd3 : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) d' : QAt a) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hd'3, map_one])
      (mk_ne_one_of_pow_three (aschbacherSolvableCore 3 (CAt a)) h3 hd'3 hd'1)
  have hΘC : thetaCent (c * d) ≤ Subgroup.centralizer ({c * d} : Set G) := by
    unfold thetaCent inSubgroup
    exact Subgroup.map_subtype_le _
  have hΘnorm : ∀ g : G, g ∈ Subgroup.centralizer ({c * d} : Set G) →
      ∀ s ∈ thetaCent (c * d), g * s * g⁻¹ ∈ thetaCent (c * d) := fun g hg s hs =>
    CFSG.RankThree.GroupTheory.conj_mem_inSubgroup_aschbacherSolvableCore
      (Subgroup.le_normalizer hg) hs
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup (CAt a),
      S = (thetaCent (c * d) ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf
        (Subgroup.centralizer ({a} : Set G)) := ⟨_, rfl⟩
  have hSmem : ∀ s : CAt a, s ∈ S ↔ (s : G) ∈ thetaCent (c * d) := by
    intro s
    rw [hSdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', s.2⟩⟩
  have hS : ∀ g ∈ Subgroup.centralizer ({c' * d'} : Set (CAt a)), ∀ s ∈ S,
      g * s * g⁻¹ ∈ S := by
    intro g hg s hs
    have hgcd : (g : G) * (c * d) = (c * d) * (g : G) := by
      have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
      simpa only [Subgroup.coe_mul, hc', hd'] using this
    rw [hSmem] at hs ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hΘnorm (g : G) (Subgroup.mem_centralizer_singleton_iff.mpr hgcd) _ hs
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup (QAt a),
      N = S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) := ⟨_, rfl⟩
  have hN3 : ∀ y ∈ N, ¬ 3 ∣ orderOf y := by
    intro y hy
    rw [hNdef] at hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    have h1' : ¬ 3 ∣ orderOf (s : G) :=
      not_three_dvd_orderOf_of_mem_thetaCent (c * d) ((hSmem s).mp hs)
    rw [Subgroup.orderOf_coe] at h1'
    intro hdvd
    exact h1' (dvd_trans hdvd
      (orderOf_map_dvd (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) s))
  have hNC : N ≤ Subgroup.centralizer
      ({(QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) c' *
        QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) d' : QAt a)} : Set (QAt a)) := by
    intro y hy
    rw [hNdef] at hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsc : s * (c' * d') = (c' * d') * s := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hc', hd']
      exact Subgroup.mem_centralizer_singleton_iff.mp (hΘC ((hSmem s).mp hs))
    have := congrArg (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) hsc
    simpa only [map_mul] using this
  have hNn : ∀ g ∈ Subgroup.centralizer
      ({(QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) c' *
        QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) d' : QAt a)} : Set (QAt a)),
      ∀ y ∈ N, g * y * g⁻¹ ∈ N := by
    intro g hg y hy
    have hg' : g ∈ Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) (c' * d')} : Set (QAt a)) := by
      rw [map_mul]
      exact hg
    rw [hNdef] at hy ⊢
    exact h1b_map_normalized_by_centralizer (aschbacherSolvableCore 3 (CAt a)) h3 hcd'3 S hS
      g hg' y hy
  have hmain := three_free_normal_le_centralizer_pair
    (c := QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) c')
    (d := QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) d')
    h1 h2 hne hZ1 hZ2 (hdK d' hd') (hcK c' hc') hqd3 hqc3 N hN3 hNC hNn
  intro x hx hxa
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxa
  obtain ⟨x', hx'⟩ : ∃ y : CAt a, (y : G) = x := ⟨⟨x, hxC⟩, rfl⟩
  have hx'S : x' ∈ S := (hSmem x').mpr (by rw [hx']; exact hx)
  have hmem : QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) x' ∈ N := by
    rw [hNdef]
    exact Subgroup.mem_map_of_mem _ hx'S
  have hcomm' : QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) x' *
      QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) c' =
      QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) c' *
      QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) x' :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hmain hmem)).1
  have hP : QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) (x' * c' * x'⁻¹ * c'⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcomm']
    group
  have hθ : x' * c' * x'⁻¹ * c'⁻¹ ∈ aschbacherSolvableCore 3 (CAt a) :=
    (QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 (CAt a)) _).mp hP
  unfold thetaCent inSubgroup
  refine Subgroup.mem_map.mpr ⟨x' * c' * x'⁻¹ * c'⁻¹, hθ, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hx', hc']

end Certified

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta
open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartTwo.Sec11

theorem h1b_mem_normalizer_inf_centralizer {G : Type*} [Group G] {P : Subgroup G} {c a : G}
    (hc : c ∈ normalizer (P : Set G)) (hca : c * a = a * c) :
    c ∈ normalizer ((P ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hP := Subgroup.mem_normalizer_iff.mp hc x
  have hca' : Commute c a := hca
  have hC : x ∈ Subgroup.centralizer ({a} : Set G) ↔
      c * x * c⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      exact ((hca'.mul_left (show Commute x a from hx)).mul_left hca'.inv_left).eq
    · intro hx
      have hy : Commute (c * x * c⁻¹) a := hx
      have h2 : Commute (c⁻¹ * (c * x * c⁻¹) * c) a :=
        (hca'.inv_left.mul_left hy).mul_left hca'
      have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
      rw [e] at h2
      exact h2.eq
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hP, hC]

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem h1b_prime_config (hP2b : Item116P2b) (hP2c : Item116P2c) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) (hR1 : ResidueR1 G A c a d)
    (hKF : KFAt L a) {z : G} {v k : ℕ} (hv : 2 ≤ v) (hzo : orderOf z = 3 ^ v)
    (hzd : z ^ 3 ^ (v - 1) = d) (hzc : z * c = c * z) (hzd' : z * d = d * z)
    (haz : a * z * a⁻¹ = z ^ k) (hk1 : 3 ^ (v - 1) ∣ k - 1) (hk2 : ¬ 3 ^ v ∣ k - 1)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    ∀ x ∈ inSubgroup (twoQ q) (thetaCent (c * d)),
      c * x * c⁻¹ * x⁻¹ ∈ inSubgroup (CFSG.pCore 2) (thetaCent (c * d)) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs := h.toSec11Std hT
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u := fun u hu w hw =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨w, hw⟩)
  have hcA := h.mem_A
  have hdA := h.d_mem
  have haA := h.a_mem
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hcdA : c * d ∈ A := mul_mem hcA hdA
  have hcd : c * d = d * c := hcomm c hcA d hdA
  have hca : c * a = a * c := hcomm c hcA a haA
  obtain ⟨δ, hδz, hδ3, hcδ, haδ, hzδ, hazδ, m, hm3, hδm⟩ :=
    zElement_pure hv hzo hzd hzc haz hk1 hk2
  have hT3 : IsPGroup 3 (Subgroup.closure ({z, a, c} : Set G)) :=
    zElement_isPGroup hzo haz hzc (hcomm a haA c hcA) hc3 ha3
  set Θ := thetaCent (c * d) with hΘ
  have h3Θ : ¬ 3 ∣ Nat.card Θ := not_three_dvd_card_inSubgroup_theta _
  have hΘC : Θ ≤ Subgroup.centralizer ({c * d} : Set G) := Subgroup.map_subtype_le _
  have hNΘ : ∀ y ∈ Subgroup.centralizer ({c * d} : Set G), y ∈ normalizer (Θ : Set G) :=
    fun y hy => Sec6.normalizer_le_normalizer_theta _ (Subgroup.le_normalizer hy)
  have hzC : z ∈ Subgroup.centralizer ({c * d} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc z * (c * d) = (z * c) * d := by group
      _ = (c * z) * d := by rw [hzc]
      _ = c * (z * d) := by group
      _ = c * (d * z) := by rw [hzd']
      _ = c * d * z := by group
  have haC : a ∈ Subgroup.centralizer ({c * d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a haA (c * d) hcdA)
  have hcC : c ∈ Subgroup.centralizer ({c * d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c hcA (c * d) hcdA)
  have hTΘ : Subgroup.closure ({z, a, c} : Set G) ≤ normalizer (Θ : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hNΘ _ hzC
    · exact hNΘ _ haC
    · exact hNΘ _ hcC
  obtain ⟨P, hPq, hPM, hTP, hPmul⟩ := exists_invariant_sylow_complement hq hq3 hT3 h3Θ hTΘ
  have hPΘ : P ≤ Θ := hPM.trans (Subgroup.map_subtype_le _)
  have hzT : z ∈ Subgroup.closure ({z, a, c} : Set G) := Subgroup.subset_closure (by simp)
  have haT : a ∈ Subgroup.closure ({z, a, c} : Set G) := Subgroup.subset_closure (by simp)
  have hcT : c ∈ Subgroup.closure ({z, a, c} : Set G) := Subgroup.subset_closure (by simp)
  have hδT : δ ∈ Subgroup.closure ({z, a, c} : Set G) :=
    (Subgroup.zpowers_le.mpr hzT) hδz
  have hstep3 := h1b_step3 hP2b hP2c h45 h hT hR1
  obtain ⟨-, -, n, hnW, hnc, hnd, hna⟩ := hR1
  have hna' : n * a * n⁻¹ ∈ Subgroup.zpowers a := by
    rw [hna]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hθU := commutator_theta_le_pCore_of_kf h45 hs h.inf_eq_zpowers h.not_mem_zpowers hnd hna'
    hKF
  have hX : IsPGroup q (P ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) := hPq.to_inf_left
  have hcX := h1b_mem_normalizer_inf_centralizer (hTP hcT) hca
  have hU2 : IsPGroup 2 (inSubgroup (CFSG.pCore 2) (thetaCent a)) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.isPGroup_inSubgroup_pCore 2 _
  have hXc := h1b_step4_pure hc3 (thetaCent a) (inSubgroup (CFSG.pCore 2) (thetaCent a))
    (P ⊓ Subgroup.centralizer ({a} : Set G)) hU2 hq2 hX hq hq3 hcX
    (fun x hx => hstep3 x (hPΘ hx.1) (Subgroup.mem_centralizer_singleton_iff.mp hx.2))
    (fun t ht => by
      have := hθU (Subgroup.commutator_mem_commutator ht hcA)
      rwa [commutatorElement_def] at this)
  have hC : ∀ x ∈ P, a * x = x * a → c * x = x * c := by
    intro x hx hax
    exact (hXc x ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hax.symm⟩).symm
  have hδc : ∃ e : ℕ, ¬ 3 ∣ e ∧ ∀ x ∈ P, δ * x * δ⁻¹ = c ^ e * x * (c ^ e)⁻¹ := by
    refine ⟨2 * m, by omega, fun x hx => ?_⟩
    have hxC : x * (c * d) = (c * d) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hΘC (hPΘ hx))
    rw [hδm]
    exact h1b_conj_pow_of_commute hcd hc3 hxC m
  have hcP := h1b_prime_pure hq2 hq3 hPq c a z δ (hTP hcT) (hTP haT) (hTP hzT) (hTP hδT) hc3 ha3
    hδ3 hca hzc.symm hcδ haδ hzδ hazδ hδc hC
  intro x hx
  obtain ⟨y, hy, u, hu, rfl⟩ := hPmul x hx
  have hNU : ∀ g ∈ normalizer (Θ : Set G),
      g ∈ normalizer ((inSubgroup (CFSG.pCore 2) Θ : Subgroup G) : Set G) := fun g hg =>
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 Θ hg
  have hcU : c * u * c⁻¹ ∈ inSubgroup (CFSG.pCore 2) Θ :=
    (Subgroup.mem_normalizer_iff.mp (hNU c (hNΘ c hcC)) u).mp hu
  have hyU := hNU y (Subgroup.le_normalizer (hPΘ hy))
  have hcy : c * y * c⁻¹ = y := by
    rw [hcP y hy]
    group
  have key : c * (y * u) * c⁻¹ * (y * u)⁻¹ = y * ((c * u * c⁻¹) * u⁻¹) * y⁻¹ := by
    calc c * (y * u) * c⁻¹ * (y * u)⁻¹ = (c * y * c⁻¹) * (c * u * c⁻¹) * u⁻¹ * y⁻¹ := by group
      _ = y * ((c * u * c⁻¹) * u⁻¹) * y⁻¹ := by rw [hcy]; group
  rw [key]
  have hin : (c * u * c⁻¹) * u⁻¹ ∈ inSubgroup (CFSG.pCore 2) Θ :=
    Subgroup.mul_mem _ hcU (Subgroup.inv_mem _ hu)
  exact (Subgroup.mem_normalizer_iff.mp hyU _).mp hin

theorem h1b_of_zElement (hP2b : Item116P2b) (hP2c : Item116P2c) (h45 : Sec4.Item4_5)
    (hZ : ZElement) (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G)
    (hR1 : ResidueR1 G A c a d) (hS : IsSurvivingCase L) (hKF : KFAt L a) :
    ∀ v ∈ inSubgroup twoFitting (thetaCent (c * d)),
      c * v * c⁻¹ * v⁻¹ ∈ inSubgroup (CFSG.pCore 2) (thetaCent (c * d)) := by
  obtain ⟨z, w, k, -, hw, hzo, hzd, hzc, hzd', haz, hk1, hk2⟩ := hZ G A c L a R Y d h hT hR1 hS
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ y ∈ A, u * y = y * u := fun u hu y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨y, hy⟩)
  have hcdA : c * d ∈ A := mul_mem h.mem_A h.d_mem
  have hcC : c ∈ Subgroup.centralizer ({c * d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c h.mem_A (c * d) hcdA)
  have hcN : c ∈ normalizer ((thetaCent (c * d) : Subgroup G) : Set G) :=
    Sec6.normalizer_le_normalizer_theta _ (Subgroup.le_normalizer hcC)
  exact h1b_fitting_of_primes (thetaCent (c * d)) c hcN (not_three_dvd_card_inSubgroup_theta _)
    (fun q hq hq2 hq3 x hx =>
      h1b_prime_config hP2b hP2c h45 h hT hR1 hKF hw hzo hzd hzc hzd' haz hk1 hk2 hq hq2 hq3 x hx)

end Certified

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta

namespace CFSG.RankThree.PartTwo.Sec11

section Certified


theorem h1bAtCD_of_zElement (hP2b : Item116P2b) (hP2c : Item116P2c) (h45 : Sec4.Item4_5)
    (hZ : ZElement) : H1bAtCD := by
  intro G _ _ A c L a R Y d h hT hR1 hS hKF
  exact h1b_of_zElement hP2b hP2c h45 hZ h hT hR1 hS hKF

theorem twoStarAtCD_of_zElement (hP2b : Item116P2b) (hP2c : Item116P2c) (h45 : Sec4.Item4_5)
    (hZ : ZElement) (hD : CensusD) (hK : SuzukiAutFacts) : ResidueR1TwoStarCD :=
  twoStarAtCD_of_suzuki (h1bAtCD_of_zElement hP2b hP2c h45 hZ) hD hK

end Certified

end CFSG.RankThree.PartTwo.Sec11

end
