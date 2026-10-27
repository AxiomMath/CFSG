module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SENeDSeven
import CFSG.RankThree.PartTwo.Sec13.Item136Moreover
import CFSG.RankThree.PartTwo.Sec13.Item136Transfer
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofBalTools
import CFSG.RankThree.PartTwo.Sec13.Item136
import CFSG.RankThree.PartTwo.Sec13.Item131bProofHeis
import CFSG.RankThree.PartTwo.Sec13.Item13NotSLTwo
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec13.Item137ProofOrbit
public import CFSG.RankThree.PartTwo.Sec13.Item13Prod

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_centralized_component {c : G} (hc : orderOf c = 3)
    {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hmax : ∀ F : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F → E ≤ F →
      Nat.card F ≤ Nat.card E)
    (hEN : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 c) (h3 : 3 ∣ Nat.card K)
    (hEK : ∀ x ∈ (E.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)))),
      ∀ k ∈ (K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)))), x * k = k * x)
    (hEKc : ∀ x ∈ (E.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)))),
      x ∈ (K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) →
      x ∈ Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
          ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hN
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 N) with hπ
  have hKN : K ≤ N := le_normalizer_zpowers_of_mem hK
  have hK₁ := subgroupOf_normalizer_mem_thetaComponents hK
  set Kb := (K.subgroupOf N).map π with hKb
  have hKc := isComponent_map_of_mem_thetaComponents Nat.prime_three hK₁
  have hcN : c ∈ N := Subgroup.le_normalizer (Subgroup.mem_zpowers c)
  set cb := π ⟨c, hcN⟩ with hcb
  have hcK : ∀ x ∈ Kb, cb * x = x * cb := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [hcb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hkC := Sec6.le_centralizer_of_mem_thetaComponentsAt hK (Subgroup.mem_subgroupOf.mp hk)
    exact (Subgroup.mem_centralizer_singleton_iff.mp hkC).symm
  have hzK : ∀ z ∈ Subgroup.zpowers cb, ∀ x ∈ Kb, z * x = x * z := by
    intro z hz x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left (hcK x hx) i))
  set E₁ := E.subgroupOf N with hE₁
  set Eb := E₁.map π with hEb
  have hE3 : IsPGroup 3 E₁ := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hE.2 _ (Subgroup.mem_subgroupOf.mp x.2)
  have hEb3 : ∀ x ∈ Eb, x ^ 3 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow]
    have : e ^ 3 = 1 := Subtype.ext (by simpa using hE.2 _ (Subgroup.mem_subgroupOf.mp he))
    rw [this, map_one]
  have hEbc : ∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩
    rw [← map_mul, ← map_mul]
    have := hE.1
    have hef : (e : G) * f = f * e := congrArg Subtype.val
      (mul_comm' (⟨(e : G), Subgroup.mem_subgroupOf.mp he⟩ : E)
        ⟨(f : G), Subgroup.mem_subgroupOf.mp hf⟩)
    congr 1
    exact Subtype.ext hef
  have hk3 : ∀ k ∈ Kb, k ^ 3 = 1 → k ∈ Eb := by
    intro k hk hk3
    by_contra hkE
    set B := Eb ⊔ Subgroup.zpowers k with hB
    have hEbk : Eb ≤ Subgroup.normalizer (Subgroup.zpowers k : Set _) := by
      intro x hx
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (hEK x hx k hk).symm i)
    have hBdec : ∀ b ∈ B, ∃ x ∈ Eb, ∃ i : ℤ, x * k ^ i = b := by
      intro b hb
      have hb' : b ∈ ((Eb ⊔ Subgroup.zpowers k : Subgroup _) : Set _) := hb
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hEbk] at hb'
      obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hb'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ⟨x, hx, i, rfl⟩
    have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
      intro a ha b hb
      obtain ⟨x, hx, i, rfl⟩ := hBdec a ha
      obtain ⟨y, hy, j, rfl⟩ := hBdec b hb
      have hxk : Commute x k := hEK x hx k hk
      have hyk : Commute y k := hEK y hy k hk
      have hxy : Commute x y := hEbc x hx y hy
      exact (Commute.mul_left (hxy.mul_right (hxk.zpow_right j))
        (((hyk.zpow_right i).symm).mul_right (Commute.zpow_zpow_self k i j))).eq
    have hB3 : ∀ b ∈ B, b ^ 3 = 1 := by
      intro b hb
      obtain ⟨x, hx, i, rfl⟩ := hBdec b hb
      have hxk : Commute x k := hEK x hx k hk
      rw [(hxk.zpow_right i).mul_pow, hEb3 x hx, one_mul, ← zpow_natCast, ← zpow_mul,
        mul_comm, zpow_mul, zpow_natCast, hk3, one_zpow]
    have hBp : IsPGroup 3 B := fun b => ⟨1, Subtype.ext (by simpa using hB3 b b.2)⟩
    obtain ⟨S, hES, -, hS3, hSB⟩ := exists_isPGroup_le_map_eq (M := ⊤) hBp
      (by rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact le_top)
      hE3 le_top le_sup_left
    have hinj := injOn_mk_of_isPGroup Nat.prime_three hS3
    have hSc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
      intro s hs t ht
      refine hinj (S.mul_mem hs ht) (S.mul_mem ht hs) ?_
      rw [map_mul, map_mul]
      have hsB : π s ∈ B := hSB ▸ Subgroup.mem_map_of_mem π hs
      have htB : π t ∈ B := hSB ▸ Subgroup.mem_map_of_mem π ht
      exact hBc _ hsB _ htB
    have hS3' : ∀ s ∈ S, s ^ 3 = 1 := by
      intro s hs
      refine hinj (S.pow_mem hs 3) S.one_mem ?_
      have hsB : π s ∈ B := hSB ▸ Subgroup.mem_map_of_mem π hs
      rw [map_pow, hB3 _ hsB, map_one]
    set F := S.map N.subtype with hF
    have hFab : CFSG.Assembly.IsElemAbelian 3 F := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
      · obtain ⟨_, ⟨s, hs, rfl⟩⟩ := a
        obtain ⟨_, ⟨t, ht, rfl⟩⟩ := b
        exact Subtype.ext (by simpa using congrArg Subtype.val (hSc s hs t ht))
      · rintro _ ⟨s, hs, rfl⟩
        simpa using congrArg Subtype.val (hS3' s hs)
    have hEF : E ≤ F := by
      intro e he
      exact ⟨⟨e, hEN he⟩, hES (Subgroup.mem_subgroupOf.mpr he), rfl⟩
    have hcardE : Nat.card Eb = Nat.card E := by
      rw [hEb, card_map_eq_of_injOn π (injOn_mk_of_isPGroup Nat.prime_three hE3)]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
    have hcardF : Nat.card F = Nat.card B := by
      rw [hF, Subgroup.card_map_of_injective N.subtype_injective, ← hSB,
        card_map_eq_of_injOn π hinj]
    have hlt : Nat.card Eb < Nat.card B := by
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hkE ?_)
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers k)
    have := hmax F hFab hEF
    omega
  have hKperf : Group.IsPerfect Kb := hKc.1.1
  set Z := (Subgroup.zpowers cb).subgroupOf Kb with hZdef
  have hZc : Z ≤ Subgroup.center Kb := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (hzK _ (Subgroup.mem_subgroupOf.mp hz) _ x.2).symm
  have hZ3 : Nat.card Z ≤ 3 := by
    have h1 : Nat.card Z ≤ Nat.card (Subgroup.zpowers cb) :=
      Nat.card_le_card_of_injective (fun z => (⟨(z : _), Subgroup.mem_subgroupOf.mp z.2⟩ :
        Subgroup.zpowers cb)) (fun a b hab => Subtype.ext (Subtype.ext
          (congrArg Subtype.val hab :)))
    have h2 : Nat.card (Subgroup.zpowers cb) ≤ 3 := by
      rw [Nat.card_zpowers]
      have : orderOf cb ∣ orderOf c := by
        refine (orderOf_map_dvd π _).trans ?_
        rw [Subgroup.orderOf_mk]
      rw [hc] at this
      exact Nat.le_of_dvd (by norm_num) this
    exact h1.trans h2
  have hZall : ∀ x : Kb, x ^ 3 = 1 → x ∈ Z := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx3 : (x : N ⧸ aschbacherSolvableCore 3 N) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hx, Subgroup.coe_one]
    exact hEKc _ (hk3 _ x.2 hx3) x.2
  have hnd := not_three_dvd_card_of_forall_pow_three_mem hKperf Z hZc hZ3 hZall
  apply hnd
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hkN : (k : G) ∈ N := hKN k.2
  set k₁ : N := ⟨k, hkN⟩
  have hk₁ : orderOf k₁ = 3 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hk]
  have hk3' : IsPGroup 3 (Subgroup.zpowers k₁) := by
    rintro ⟨x, hx⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hk₁,
      pow_orderOf_eq_one, one_zpow]
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hk3'
  have hkb : orderOf (π k₁) = 3 := by
    have hk13 : k₁ ^ 3 = 1 := hk₁ ▸ pow_orderOf_eq_one k₁
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hk13, map_one]
    · intro h1
      have : k₁ = 1 := hinj (Subgroup.mem_zpowers k₁) (Subgroup.one_mem _) (by rw [h1, map_one])
      rw [this, orderOf_one] at hk₁
      exact absurd hk₁ (by norm_num)
  have hmem : π k₁ ∈ Kb := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr k.2)
  have hdvd := Subgroup.orderOf_dvd_natCard Kb hmem
  rwa [hkb] at hdvd

theorem commute_of_ne_thetaComponentsAt {c : G} {K L : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 c) (hL : L ∈ thetaComponentsAt 3 c) (hKL : K ≠ L) :
    ∀ x ∈ (K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)))),
      ∀ y ∈ (L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)))), x * y = y * x := by
  set N := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hN
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 N) with hπ
  have hKN : K ≤ N := le_normalizer_zpowers_of_mem hK
  have hLN : L ≤ N := le_normalizer_zpowers_of_mem hL
  have hK₁ := subgroupOf_normalizer_mem_thetaComponents hK
  have hL₁ := subgroupOf_normalizer_mem_thetaComponents hL
  have hne₁ : K.subgroupOf N ≠ L.subgroupOf N := by
    intro h
    apply hKL
    have h' := congrArg (Subgroup.map N.subtype) h
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hKN, inf_eq_left.mpr hLN] at h'
  have hKc := isComponent_map_of_mem_thetaComponents Nat.prime_three hK₁
  have hLc := isComponent_map_of_mem_thetaComponents Nat.prime_three hL₁
  have hneb : (K.subgroupOf N).map π ≠ (L.subgroupOf N).map π := fun h =>
    hne₁ ((theta_component_quotient_correspondence Nat.prime_three).1.injOn hK₁ hL₁ h)
  have hcomm : ⁅(K.subgroupOf N).map π, (L.subgroupOf N).map π⁆ = ⊥ :=
    (LocalCores.distinct_components_commute hKc hLc).resolve_left hneb
  intro x hx y hy
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
  exact (Subgroup.mem_centralizer_iff.mp this y hy).symm

theorem eq_or_eq_of_le_sup {d : G} (hd : orderOf d = 3) {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hmax : ∀ F : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F → E ≤ F →
      Nat.card F ≤ Nat.card E)
    (hEC : E ≤ Subgroup.centralizer ({d} : Set G)) {K K₁ : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 d) (hK₁ : K₁ ∈ thetaComponentsAt 3 d) (hKK₁ : K₁ ≠ K)
    (hEK : E ≤ K ⊔ K₁) (hEN : E ≤ Subgroup.normalizer (K : Set G))
    (hCE : E ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers d)
    {K₂ : Subgroup G} (hK₂ : K₂ ∈ thetaComponentsAt 3 d) (h3 : 3 ∣ Nat.card K₂) :
    K₂ = K ∨ K₂ = K₁ := by
  by_contra hne
  push Not at hne
  obtain ⟨h2K, h2K₁⟩ := hne
  set N := Subgroup.normalizer (Subgroup.zpowers d : Set G) with hN
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 N) with hπ
  have hENd : E ≤ N := hEC.trans (centralizer_le_normalizer_zpowers d)
  have hKN : K ≤ N := le_normalizer_zpowers_of_mem hK
  have hK₁N : K₁ ≤ N := le_normalizer_zpowers_of_mem hK₁
  have hc2 := commute_of_ne_thetaComponentsAt hK₂ hK h2K
  have hc21 := commute_of_ne_thetaComponentsAt hK₂ hK₁ h2K₁
  have hK₁K : K₁ ≤ Subgroup.normalizer (K : Set G) := by
    have h1 := hK₁
    have h2 := hK
    rw [thetaComponentsAt_eq_thetaComponentsIn] at h1 h2
    exact Sec14.BalTools.le_normalizer_of_ne_in h1 h2 hKK₁
  refine false_of_centralized_component hd hE hmax hENd hK₂ h3 ?_ ?_
  · rintro _ ⟨e, he, rfl⟩ k hk
    have he' : (e : G) ∈ ((K₁ ⊔ K : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hEK (Subgroup.mem_subgroupOf.mp he)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hK₁K] at he'
    obtain ⟨b, hb, a, ha, hba⟩ := Set.mem_mul.mp he'
    have hbN : b ∈ N := hK₁N hb
    have haN : a ∈ N := hKN ha
    have hsplit : π e = π ⟨b, hbN⟩ * π ⟨a, haN⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hba.symm
    have hb' : π ⟨b, hbN⟩ ∈ (K₁.subgroupOf N).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hb)
    have ha' : π ⟨a, haN⟩ ∈ (K.subgroupOf N).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha)
    rw [hsplit]
    have h1 := hc21 k hk _ hb'
    have h2 := hc2 k hk _ ha'
    calc π ⟨b, hbN⟩ * π ⟨a, haN⟩ * k = π ⟨b, hbN⟩ * (π ⟨a, haN⟩ * k) := by group
      _ = π ⟨b, hbN⟩ * (k * π ⟨a, haN⟩) := by rw [h2]
      _ = (π ⟨b, hbN⟩ * k) * π ⟨a, haN⟩ := by group
      _ = (k * π ⟨b, hbN⟩) * π ⟨a, haN⟩ := by rw [h1]
      _ = k * (π ⟨b, hbN⟩ * π ⟨a, haN⟩) := by group
  · rintro _ ⟨e, he, rfl⟩ hek
    have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he
    have hmemC : (e : G) ∈ Sec4.thetaQuotCentralizer K := by
      refine mem_thetaQuotCentralizer_of_mk_commute hK (g := e) (hEN heE) fun l hl => ?_
      have hl' : π l ∈ (K.subgroupOf N).map π :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hl)
      exact hc2 _ hek _ hl'
    have hed : (e : G) ∈ Subgroup.zpowers d := by
      have h1 : (e : G) ∈ E ⊓ Sec4.thetaQuotCentralizer K := Subgroup.mem_inf.mpr ⟨heE, hmemC⟩
      rw [hCE] at h1
      exact h1
    exact mk_mem_zpowers_of_mem hed e.2

theorem false_of_heis_inverting {E K : Subgroup G} {d : G} (hD : Sec13Data G E d K)
    (hdK : d ∈ K) (hH : Sec4.IsHeisCentral (lBarA d K E) (K ⧸ aschbacherSolvableCore 3 K))
    (hZ3 : Nat.card (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) = 3)
    {t : G} (htd : t * d * t⁻¹ = d⁻¹) (htE : t ∈ Subgroup.normalizer (E : Set G))
    (htK : t ∈ Subgroup.normalizer (K : Set G))
    (hEt : ∀ e ∈ E, t * e * t⁻¹ * e⁻¹ ∈ Subgroup.zpowers d) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (Subgroup.zpowers d : Set G) with hN
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 N) with hπ
  set Ab := lBarA d K E with hAb
  set Λ := (Sec12.lBar d K).subgroupOf Ab with hΛ
  set z := mkC (L := K) hD.mem_A with hz
  obtain ⟨U, hU, hUΛ, hUV, hZU⟩ := isHeisCentral_facts hD hH
  have hzΛ : z ∈ Λ := mkC_mem_lBar hD hdK
  have hzc : ∀ x : Ab, z * x = x * z := fun x =>
    (Subgroup.mem_center_iff.mp (mkC_mem_center hD) x).symm
  have hzo : orderOf z = 3 := orderOf_mkC hD
  have hcenΛ : ∀ v : Ab, v ∈ Λ → (∀ w ∈ Λ, v * w = w * v) → v ∈ Subgroup.zpowers z := by
    intro v hv hvc
    have hle : Subgroup.zpowers (⟨z, hzΛ⟩ : Λ) ≤ Subgroup.center Λ := by
      rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hzc w).symm
    have hcard : Nat.card (Subgroup.center Λ) ≤ Nat.card (Subgroup.zpowers (⟨z, hzΛ⟩ : Λ)) := by
      rw [card_center_lBar hD, hZ3, Nat.card_zpowers, Subgroup.orderOf_mk, hzo]
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    have hvZ : (⟨v, hv⟩ : Λ) ∈ Subgroup.center Λ := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hvc w w.2).symm
    rw [← heq] at hvZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvZ
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hUΛz : ∀ x : Ab, x ∈ U → x ∈ Λ → x ∈ Subgroup.zpowers z := fun x hxU hxΛ =>
    hcenΛ x hxΛ fun w hw => hUΛ x hxU w hw
  have hzU : z ∈ U := by
    have hcardUΛ : Nat.card (U ⊓ Λ : Subgroup Ab) = 3 := by
      rw [← hZU, Subgroup.card_map_of_injective U.subtype_injective, hU.1.2.2.2]
    have hle : U ⊓ Λ ≤ Subgroup.zpowers z := fun x hx => hUΛz x hx.1 hx.2
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardUΛ, Nat.card_zpowers, hzo])
    have : z ∈ U ⊓ Λ := heq ▸ Subgroup.mem_zpowers z
    exact this.1
  have hUnΛ : U ≤ Subgroup.normalizer (Λ : Set Ab) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (hUΛ u hu w hw).symm)
  have hcentU : ∀ x : Ab, (∀ w ∈ Λ, x * w = w * x) → x ∈ U := by
    intro x hxc
    have hx : x ∈ ((U ⊔ Λ : Subgroup Ab) : Set Ab) := by rw [hUV]; exact Subgroup.mem_top x
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUnΛ] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hx
    have hvc : ∀ w ∈ Λ, v * w = w * v := by
      intro w hw
      have h1 := hxc w hw
      have h2 := hUΛ u hu w hw
      calc v * w = u⁻¹ * (u * v * w) := by group
        _ = u⁻¹ * (w * (u * v)) := by rw [h1]
        _ = u⁻¹ * (w * u) * v := by group
        _ = u⁻¹ * (u * w) * v := by rw [h2]
        _ = w * v := by group
    exact mul_mem hu (Subgroup.zpowers_le.mpr hzU (hcenΛ v hv hvc))
  have hdN : t ∈ N := by
    rw [hN, Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (t * d * t⁻¹) = _
    rw [htd, Subgroup.zpowers_inv]
  set t' : N := ⟨t, hdN⟩ with ht'
  have htKE : t ∈ Subgroup.normalizer ((K ⊔ E : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htK,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htE]
  have hσ : ∀ x : Ab, π t' * (x : N ⧸ aschbacherSolvableCore 3 N) * (π t')⁻¹ ∈ Ab := by
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    refine ⟨t' * k * t'⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp htKE k).mp (Subgroup.mem_subgroupOf.mp hk)
  set σ : Ab →* Ab := ((MulAut.conj (π t')).toMonoidHom.comp Ab.subtype).codRestrict Ab hσ
    with hσdef
  have hσapp : ∀ x : Ab, ((σ x : Ab) : N ⧸ aschbacherSolvableCore 3 N) =
      π t' * (x : N ⧸ aschbacherSolvableCore 3 N) * (π t')⁻¹ := fun x => rfl
  have hσΛ : ∀ {s : G} (hs : s ∈ N), s ∈ Subgroup.normalizer (K : Set G) → ∀ v : Ab, v ∈ Λ →
      π ⟨s, hs⟩ * (v : N ⧸ aschbacherSolvableCore 3 N) * (π ⟨s, hs⟩)⁻¹ ∈ Sec12.lBar d K := by
    intro s hs hsK v hv
    obtain ⟨k, hk, hkv⟩ := Subgroup.mem_subgroupOf.mp hv
    refine ⟨⟨s, hs⟩ * k * (⟨s, hs⟩ : N)⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hsK k).mp (Subgroup.mem_subgroupOf.mp hk)
    · rw [map_mul, map_mul, map_inv, hkv]
  have hσΛ' : ∀ v ∈ Λ, σ v ∈ Λ := fun v hv =>
    Subgroup.mem_subgroupOf.mpr (by rw [hσapp]; exact hσΛ hdN htK v hv)
  have htiN : t⁻¹ ∈ N := inv_mem hdN
  have hti : π ⟨t⁻¹, htiN⟩ = (π t')⁻¹ := by rw [← map_inv]; rfl
  have hσU : ∀ u ∈ U, σ u ∈ U := by
    intro u hu
    refine hcentU _ fun w hw => ?_
    have hw'Λ := hσΛ htiN (inv_mem htK) w hw
    set w' : Ab := ⟨π ⟨t⁻¹, htiN⟩ * (w : N ⧸ aschbacherSolvableCore 3 N) *
      (π ⟨t⁻¹, htiN⟩)⁻¹, lBar_le_lBarA hw'Λ⟩ with hw'
    have hw'Λ' : w' ∈ Λ := Subgroup.mem_subgroupOf.mpr hw'Λ
    have hσw' : σ w' = w := by
      apply Subtype.ext
      rw [hσapp, hw']
      simp only [hti, inv_inv]
      group
    rw [← hσw', ← map_mul, ← map_mul, hUΛ u hu w' hw'Λ']
  have hσz : σ z = z⁻¹ := by
    apply Subtype.ext
    rw [hσapp, Subgroup.coe_inv]
    change π t' * π ⟨d, Subgroup.le_normalizer (Subgroup.mem_zpowers d)⟩ * (π t')⁻¹ =
      (π ⟨d, Subgroup.le_normalizer (Subgroup.mem_zpowers d)⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht']
    exact htd
  have hσE : ∀ e : E, ∃ j : ℤ, σ (aBarHom hD e) = z ^ j * aBarHom hD e := by
    intro e
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hEt e e.2)
    refine ⟨j, Subtype.ext ?_⟩
    rw [hσapp, Subgroup.coe_mul, Subgroup.coe_zpow, aBarHom_apply]
    change π t' * π ⟨(e : G), _⟩ * (π t')⁻¹ =
      (π ⟨d, Subgroup.le_normalizer (Subgroup.mem_zpowers d)⟩) ^ j * π ⟨(e : G), _⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← map_zpow, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, ht']
    rw [hj]
    group
  have hdecAb : ∀ x : Ab, ∃ v ∈ Λ, ∃ e : E, x = v * aBarHom hD e := by
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    have hk' : (k : G) ∈ ((K ⊔ E : Subgroup G) : Set G) := Subgroup.mem_subgroupOf.mp hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hD.le_normalizer] at hk'
    obtain ⟨a, ha, e, he, hae⟩ := Set.mem_mul.mp hk'
    have haN : a ∈ N := le_normalizer_zpowers_of_mem hD.mem_thetaComponentsAt ha
    have haL : π ⟨a, haN⟩ ∈ Sec12.lBar d K :=
      ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    refine ⟨⟨π ⟨a, haN⟩, lBar_le_lBarA haL⟩, Subgroup.mem_subgroupOf.mpr haL, ⟨e, he⟩, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, aBarHom_apply]
    change π k = π ⟨a, haN⟩ * π ⟨e, _⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hae.symm
  have hσUz : ∀ u ∈ U, σ u * u⁻¹ ∈ Subgroup.zpowers z := by
    intro u hu
    refine hUΛz _ (mul_mem (hσU u hu) (inv_mem hu)) ?_
    obtain ⟨v, hv, e, rfl⟩ := hdecAb u
    obtain ⟨j, hj⟩ := hσE e
    rw [map_mul, hj, show σ v * (z ^ j * aBarHom hD e) * (v * aBarHom hD e)⁻¹ =
      σ v * z ^ j * v⁻¹ by group]
    exact mul_mem (mul_mem (hσΛ' v hv) (zpow_mem hzΛ j)) (inv_mem hv)
  obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ : ∃ u₁ ∈ U, ∃ u₂ ∈ U, ⁅u₁, u₂⁆ ≠ 1 := by
    by_contra hall
    push Not at hall
    have hcomm : commutator U = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      have h1 := hall a a.2 b b.2
      rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact Subtype.ext h1.symm
    have h3 := hU.1.2.2.2
    rw [← hU.1.2.1, hcomm, Subgroup.card_bot] at h3
    norm_num at h3
  have hγ : ⁅u₁, u₂⁆ ∈ Subgroup.zpowers z := by
    have h1 : (⁅(⟨u₁, hu₁⟩ : U), ⟨u₂, hu₂⟩⁆ : U) ∈ commutator U :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [hU.1.2.1] at h1
    have h2 : ((⁅(⟨u₁, hu₁⟩ : U), ⟨u₂, hu₂⟩⁆ : U) : Ab) ∈ (Subgroup.center U).map U.subtype :=
      ⟨_, h1, rfl⟩
    rw [hZU] at h2
    have h3 : ((⁅(⟨u₁, hu₁⟩ : U), ⟨u₂, hu₂⟩⁆ : U) : Ab) = ⁅u₁, u₂⁆ := by
      simp [commutatorElement_def]
    rw [h3] at h2
    exact hUΛz _ h2.1 h2.2
  have hfix : σ ⁅u₁, u₂⁆ = ⁅u₁, u₂⁆ := by
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hσUz u₁ hu₁)
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hσUz u₂ hu₂)
    have h1 : σ u₁ = z ^ a * u₁ := by rw [ha]; group
    have h2 : σ u₂ = z ^ b * u₂ := by rw [hb]; group
    have hca : ∀ x : Ab, z ^ a * x = x * z ^ a := fun x =>
      ((show Commute z x from hzc x).zpow_left a).eq
    have hcb : ∀ x : Ab, z ^ b * x = x * z ^ b := fun x =>
      ((show Commute z x from hzc x).zpow_left b).eq
    rw [map_commutatorElement, h1, h2, commutatorElement_def, commutatorElement_def]
    calc z ^ a * u₁ * (z ^ b * u₂) * (z ^ a * u₁)⁻¹ * (z ^ b * u₂)⁻¹ =
        z ^ a * (u₁ * (z ^ b * u₂) * u₁⁻¹) * (z ^ a)⁻¹ * (z ^ b * u₂)⁻¹ := by group
      _ = u₁ * (z ^ b * u₂) * u₁⁻¹ * (z ^ b * u₂)⁻¹ := by rw [hca]; group
      _ = z ^ b * (u₁ * u₂ * u₁⁻¹ * u₂⁻¹) * (z ^ b)⁻¹ := by
          rw [show u₁ * (z ^ b * u₂) = z ^ b * u₁ * u₂ by rw [← mul_assoc, ← hcb]]; group
      _ = u₁ * u₂ * u₁⁻¹ * u₂⁻¹ := by rw [hcb]; group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hγ
  rw [← hk, map_zpow, hσz, inv_zpow, ← zpow_neg] at hfix
  have h2k : z ^ (2 * k) = 1 := by
    calc z ^ (2 * k) = z ^ k * z ^ k := by rw [two_mul, zpow_add]
      _ = z ^ (-k) * z ^ k := by rw [hfix]
      _ = 1 := by rw [← zpow_add, neg_add_cancel, zpow_zero]
  have h3 : (3 : ℤ) ∣ 2 * k := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h2k
    rwa [hzo] at this
  have hk3 : (3 : ℤ) ∣ k := by omega
  apply hne
  rw [← hk]
  obtain ⟨m, rfl⟩ := hk3
  have hz3 : z ^ (3 : ℤ) = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hzo] at h
    exact_mod_cast h
  rw [zpow_mul, hz3, one_zpow]

theorem isTripleCover_of_mulEquiv {X X' Y : Type*} [Group X] [Group X'] [Group Y]
    (e : X ≃* X') (h : Sec4.IsTripleCover X' Y) : Sec4.IsTripleCover X Y := by
  obtain ⟨h3, ⟨f⟩⟩ := h
  have hc : (Subgroup.center X).map (e : X →* X') = Subgroup.center X' :=
    Subgroup.map_center_eq e
  refine ⟨?_, ⟨(QuotientGroup.congr _ _ e hc).trans f⟩⟩
  rw [← h3, ← hc, Subgroup.card_map_of_injective e.injective]

theorem step138ENeDHeisT_of (h131 : Item131) (hspor : SporadicModels131) :
    Step138ENeDHeisT := by
  intro G _ _ A c L E F x y t hfr hΩ K hK hdK hT hH hN
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set d := ⁅x, y⁆ with hd
  have h := hfr.hH.1
  have hXF := mem_partTwoF_of_hyp138 hfr.hH
  have hD : Sec13Data G E d K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := hΩ
      mem_lA := hK }
  have hE3 : CFSG.Assembly.IsElemAbelian 3 E := hfr.hH.2.2.2.1
  have hdo : orderOf d = 3 := orderOf_eq_prime hfr.hd3 hfr.hd1
  obtain ⟨h7, -, hEcl⟩ := case7_of_mem h131 hspor hD hdK
  have hty : Item131bProof.HeisType (K ⧸ aschbacherSolvableCore 3 K) := by
    rcases h7 with hSL | ⟨-, hlist⟩
    · exact absurd hSL (notSLTwoOfHypT_of h131 hspor G E d K hD hT)
    · exact hlist
  have hZ3 := Item131bProof.card_center_eq_three hty
  obtain ⟨U, hzU, hU9, hU3, hUΛ, hUΛz, hAbU⟩ := exists_U_of_isHeisCentral hD hdK hH hZ3
  obtain ⟨E', hE'le, hE'ab, hE'27, hE'θ, hE'K, -⟩ :=
    exists_E_of_U hD hdK hzU hU9 hU3 hUΛ hUΛz hAbU
  obtain ⟨-, hE'cl⟩ := hEcl E' hE'le hE'ab hE'27 hE'θ hE'K
  have hE'C : E' ≤ Subgroup.centralizer ({d} : Set G) :=
    hE'le.trans (inf_le_left.trans (sup_le hD.le_centralizer hD.A_le_centralizer))
  have hE'T : E' ∉ partTwoT G := fun hET => by
    have h1 := hT.2.2 d hΩ
    rw [Set.eq_empty_iff_forall_notMem] at h1
    exact h1 E' ⟨hET, hE'C⟩
  obtain ⟨-, ⟨K₁, hK₁, hEKK₁, hK₁6⟩, -⟩ := hE'cl hE'T
  have hK₁K : K₁ ≠ K := by
    rintro rfl
    exact Item131bProof.not_isTripleCover_six hty hK₁6
  have hmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B →
      Nat.card B ≤ Nat.card E := fun B hB hEB => by rw [hXF.1.2.1 B hB hEB]
  have hCEset := sectionCentralizer_eq_inf hK.2.1
  rw [hK.2.2.1] at hCEset
  have hCE : E ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers d :=
    SetLike.coe_injective hCEset.symm
  have htK : t ∈ Subgroup.normalizer (K : Set G) := by
    have hzx : Subgroup.zpowers (t * d * t⁻¹) = Subgroup.zpowers d := by
      rw [hfr.htd, Subgroup.zpowers_inv]
    have hKtθ : K.map (MulAut.conj t).toMonoidHom ∈ thetaComponentsAt 3 d := by
      have h1 := ((map_conj_mem_lA_iff (c := d) (L := K) hfr.htE).mpr hK).1
      rw [thetaComponentsAt_eq_thetaComponentsIn, centralizer_singleton_eq_of_zpowers_eq hzx] at h1
      exact h1
    have h3 : 3 ∣ Nat.card (K.map (MulAut.conj t).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, ← hdo]
      exact Subgroup.orderOf_dvd_natCard K hdK
    rcases eq_or_eq_of_le_sup hdo hE3 hmax hD.A_le_centralizer hK.1 hK₁ hK₁K hEKK₁ hK.2.1 hCE
      hKtθ h3 with h1 | h1
    · exact map_conj_eq_iff_mem_normalizer.mp h1
    · exfalso
      subst h1
      set eI := K.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
      have e : K ⧸ aschbacherSolvableCore 3 K ≃*
          K.map (MulAut.conj t).toMonoidHom ⧸
            aschbacherSolvableCore 3 (K.map (MulAut.conj t).toMonoidHom) :=
        QuotientGroup.congr _ _ eI (aschbacherSolvableCore_map_mulEquiv Nat.prime_three eI)
      exact Item131bProof.not_isTripleCover_six hty (isTripleCover_of_mulEquiv e hK₁6)
  exact false_of_heis_inverting hD hdK hH hZ3 hfr.htd hfr.htE htK hfr.hEt

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
