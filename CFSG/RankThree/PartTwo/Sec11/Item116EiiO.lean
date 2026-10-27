module

public import CFSG.RankThree.PartTwo.Sec11.Item116Eii
import CFSG.RankThree.PartTwo.Sec11.Item116TheoremO
import CFSG.RankThree.PartTwo.Sec6.Item68

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (fusionIsSylowIn)
open CFSG.Goldschmidt (oddCoreOf)
open scoped commutatorElement

namespace TheoremO

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_three {c : G} (hc3 : c ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers c) := by
  rintro ⟨y, hy⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨1, Subtype.ext ?_⟩
  change (c ^ k) ^ (3 ^ 1) = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]

theorem not_three_dvd_card_of_isPGroup_two {P : Subgroup G} (hP : IsPGroup 2 P) :
    ¬ 3 ∣ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hdvd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn] at hdvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow hdvd)
  omega

omit [Finite G] in
theorem exists_commute_lift_commutator {K₁ K₂ T₀ : Subgroup G} (hTK : T₀ ≤ K₁)
    (hT₀ : IsPGroup 2 T₀) (hD : Odd (Nat.card (⁅K₁, K₂⁆ : Subgroup G))) {z : G} (hz : z ∈ K₂) :
    ∃ x : G, x⁻¹ * z ∈ ⁅K₁, K₂⁆ ∧ x ∈ Subgroup.centralizer (T₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := ⁅K₁, K₂⁆ with hDdef
  set M := Subgroup.normalizer (D : Set G) with hM
  have hDM : D ≤ M := Subgroup.le_normalizer
  have hK₁M : K₁ ≤ M := Subgroup.normalizer_commutator_ge_left K₁ K₂
  have hK₂M : K₂ ≤ M := Subgroup.normalizer_commutator_ge_right K₁ K₂
  have hN : (D.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDM).mpr le_rfl
  have hN2 : ¬ 2 ∣ Nat.card (D.subgroupOf M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv]
    exact fun h2 => (Nat.not_even_iff_odd.mpr hD) (even_iff_two_dvd.mpr h2)
  have hP : IsPGroup 2 (T₀.subgroupOf M) := hT₀.comap_subtype
  obtain ⟨x, hxz, hxT⟩ := exists_commute_lift (D.subgroupOf M) hN2 hP
    (z := ⟨z, hK₂M hz⟩) (fun t ht => by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.commutator_mem_commutator (hTK (Subgroup.mem_subgroupOf.mp ht)) hz)
  refine ⟨x, Subgroup.mem_subgroupOf.mp hxz, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
  have h1 := hxT ⟨t, hK₁M (hTK ht)⟩ (Subgroup.mem_subgroupOf.mpr ht)
  exact congrArg Subtype.val h1

theorem le_centralizer_of_O'' {C T₀ Q K₁ K₂ : Subgroup G} {c : G} {Z' : Subgroup C}
    (hZ' : Z' ∈ thetaComponents 3 C) (hTC : T₀ ≤ C) (hTK : T₀ ≤ K₁)
    (hK₂Z : K₂ ≤ Z'.map C.subtype) (hcK : c ∈ K₂)
    (hZK : Z'.map C.subtype ≤ K₂ ⊔ inSubgroup (aschbacherSolvableCore 3) C)
    (hDθ : ⁅K₁, K₂⁆ ≤ inSubgroup (aschbacherSolvableCore 3) C)
    (hDodd : Odd (Nat.card (⁅K₁, K₂⁆ : Subgroup G)))
    (hcodd : Odd (Nat.card
      (⁅inSubgroup (aschbacherSolvableCore 3) C, Subgroup.zpowers c⁆ : Subgroup G)))
    (hc3 : c ^ 3 = 1) (hcT : c ∈ Subgroup.centralizer (T₀ : Set G)) (hT₀ : IsPGroup 2 T₀)
    (hQ : IsPGroup 2 Q)
    (hQN : Subgroup.centralizer (T₀ : Set G) ≤ Subgroup.normalizer (Q : Set G)) :
    Q ⊓ C ≤ Subgroup.centralizer ({c} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := aschbacherSolvableCore 3 C with hNdef
  set θC := inSubgroup (aschbacherSolvableCore 3) C with hθC
  set π := QuotientGroup.mk' N with hπ
  have hθCC : θC ≤ C := Subgroup.map_subtype_le _
  have hmemθ : ∀ u : C, (u : G) ∈ θC ↔ u ∈ N := fun u =>
    Subgroup.mem_map_iff_mem C.subtype_injective
  have hCθ : C ≤ Subgroup.normalizer (θC : Set G) :=
    Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta C)
  have hK₂C : K₂ ≤ C := hK₂Z.trans (Subgroup.map_subtype_le Z')
  have hcC : c ∈ C := hK₂C hcK
  set c₁ : C := ⟨c, hcC⟩ with hc₁
  have hc₁Z' : c₁ ∈ Z' := by
    obtain ⟨z, hz, hzc⟩ := hK₂Z hcK
    rwa [show c₁ = z from Subtype.ext hzc.symm]
  have hJ' := isComponent_map_of_mem_thetaComponents Nat.prime_three hZ'
  set T₁ := T₀.comap C.subtype with hT₁
  set X := (Z'.map π).comap π ⊓ Subgroup.centralizer (T₁ : Set C) with hX
  have hXmap : X.map π = Z'.map π := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le _ _)
    · rintro _ ⟨y, hy, rfl⟩
      have hyK : (y : G) ∈ ((K₂ ⊔ θC : Subgroup G) : Set G) := hZK ⟨y, hy, rfl⟩
      rw [Subgroup.coe_mul_of_left_le_normalizer_right K₂ θC (hK₂C.trans hCθ)] at hyK
      obtain ⟨z, hz, w, hw, hzw⟩ := hyK
      obtain ⟨x, hxz, hxT⟩ := exists_commute_lift_commutator hTK hT₀ hDodd hz
      have hxC : x ∈ C := by
        have h1 : x = z * (x⁻¹ * z)⁻¹ := by group
        rw [h1]
        exact C.mul_mem (hK₂C hz) (C.inv_mem (hθCC (hDθ hxz)))
      have hπx : π ⟨x, hxC⟩ = π y := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← hmemθ]
        have h1 : ((⟨x, hxC⟩⁻¹ * y : C) : G) = (x⁻¹ * z) * w := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [← hzw]
          group
        rw [h1]
        exact θC.mul_mem (hDθ hxz) hw
      have hxX1 : π ⟨x, hxC⟩ ∈ Z'.map π := by
        rw [hπx]
        exact Subgroup.mem_map_of_mem _ hy
      have hxX2 : (⟨x, hxC⟩ : C) ∈ Subgroup.centralizer (T₁ : Set C) :=
        Subgroup.mem_centralizer_iff.mpr fun t ht =>
          Subtype.ext (Subgroup.mem_centralizer_iff.mp hxT (t : G) ht)
      exact ⟨⟨x, hxC⟩, ⟨hxX1, hxX2⟩, hπx⟩
  have hc₁X : c₁ ∈ X := by
    refine ⟨Subgroup.mem_map_of_mem _ hc₁Z', Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcT (t : G) ht)
  set Q₁ := Q.comap C.subtype with hQ₁
  have hQ₁2 : IsPGroup 2 Q₁ := hQ.comap_subtype
  have hXN : X ≤ Subgroup.normalizer (Q₁ : Set C) := by
    intro x hx
    have hxT : (x : G) ∈ Subgroup.centralizer (T₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx.2 ⟨t, hTC ht⟩ ht)
    have hxQ := hQN hxT
    rw [Subgroup.mem_normalizer_iff]
    intro q
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    exact Subgroup.mem_normalizer_iff.mp hxQ q
  have hJN : Z'.map π ≤
      Subgroup.normalizer ((Q₁.map π : Subgroup (C ⧸ N)) : Set (C ⧸ N)) := by
    rw [← hXmap]
    exact (Subgroup.map_mono hXN).trans (Subgroup.le_normalizer_map _)
  have hsolv : Group.IsSolvable (Q₁.map π) := by
    have := (hQ₁2.map π).isNilpotent
    infer_instance
  have h5 := commutator_eq_bot_of_isComponent_le_normalizer hJ' hsolv hJN
  have hXQN : ⁅X, Q₁⁆ ≤ N := by
    rw [← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator, hXmap]
    exact h5
  have hQc : ⁅Q ⊓ C, Subgroup.zpowers c⁆ ≤ θC := by
    rw [Subgroup.commutator_le]
    intro q hq y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hk : c₁ ^ k ∈ X := X.zpow_mem hc₁X k
    have hq₁ : (⟨q, hq.2⟩ : C) ∈ Q₁ := hq.1
    have h1 := hXQN (Subgroup.commutator_mem_commutator hk hq₁)
    rw [← hmemθ] at h1
    have h2 := θC.inv_mem h1
    have h3 : ((⁅c₁ ^ k, (⟨q, hq.2⟩ : C)⁆ : C) : G)⁻¹ = q * c ^ k * q⁻¹ * (c ^ k)⁻¹ := by
      have hc₁c : ((c₁ : C) : G) = c := rfl
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow,
        hc₁c]
      group
    rwa [h3] at h2
  have hcQ : Subgroup.zpowers c ≤ Subgroup.normalizer ((Q ⊓ C : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact CFSG.RankThreeEvenClassification.Helpers.normalizes_inf_of_normalizes_both
      (Subgroup.zpowers c) Q C (Subgroup.zpowers_le.mpr (hQN hcT))
      (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hcC)) (Subgroup.mem_zpowers c)
  have hcθ : Subgroup.zpowers c ≤ Subgroup.normalizer (θC : Set G) :=
    Subgroup.zpowers_le.mpr (hCθ hcC)
  set D' := (Q ⊓ C) ⊓ θC with hD'
  have hcD' : Subgroup.zpowers c ≤ Subgroup.normalizer (D' : Set G) :=
    CFSG.RankThreeEvenClassification.Helpers.normalizes_inf_of_normalizes_both _ _ _ hcQ hcθ
  have hD'2 : IsPGroup 2 D' := hQ.to_le (inf_le_left.trans inf_le_left)
  have hD'c : ⁅D', Subgroup.zpowers c⁆ = ⊥ := by
    rw [eq_bot_iff, ← inf_eq_bot_of_isPGroup_of_odd hD'2 hcodd]
    exact le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hcD')
      (Subgroup.commutator_mono inf_le_right le_rfl)
  have hQcD : ⁅Q ⊓ C, Subgroup.zpowers c⁆ ≤ D' :=
    le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hcQ) hQc
  have hQ2 : IsPGroup 2 (Q ⊓ C : Subgroup G) := hQ.to_le inf_le_left
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
    Nat.prime_three (Subgroup.zpowers c) (Q ⊓ C) (isPGroup_zpowers_of_pow_three hc3)
    (not_three_dvd_card_of_isPGroup_two hQ2) hcQ
  have hbot : ⁅Q ⊓ C, Subgroup.zpowers c⁆ = ⊥ := by
    rw [← hidem, eq_bot_iff, ← hD'c]
    exact Subgroup.commutator_mono hQcD le_rfl
  rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot

theorem false_of_charTwo_O'' (hchar : CFSG.Assembly.IsCharTwoType G) {F T₀ : Subgroup G}
    {c : G} (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : 9 ≤ Nat.card F) (hcF : c ∈ F)
    (hc1 : c ≠ 1) (hT₀ : IsPGroup 2 T₀) (hT₀1 : T₀ ≠ ⊥)
    (hFT : F ≤ Subgroup.centralizer (T₀ : Set G))
    (hY : ∀ e ∈ F, e ∉ Subgroup.zpowers c →
      ∃ Y' ∈ thetaComponentsAt 3 e, ∃ K₁ K₂ : Subgroup G, T₀ ≤ K₁ ∧ K₂ ≤ Y' ∧ c ∈ K₂ ∧
        Y' ≤ K₂ ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) ∧
        ⁅K₁, K₂⁆ ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) ∧
        Odd (Nat.card (⁅K₁, K₂⁆ : Subgroup G)) ∧
        Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ({e} : Set G)), Subgroup.zpowers c⁆ : Subgroup G))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, heF, hec, hQe⟩ :=
    exists_not_mem_zpowers_commutator_ne_bot hchar hF hF9 hcF hc1 hT₀ hT₀1 hFT
  obtain ⟨Y', hY', K₁, K₂, hTK, hK₂Y, hcK, hYK, hDθ, hDodd, hcodd⟩ := hY e heF hec
  apply hQe
  obtain ⟨Z', hZ', rfl⟩ := hY'
  have hTC : T₀ ≤ Subgroup.centralizer ({e} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hFT heF) t ht)
  have hQN : Subgroup.centralizer (T₀ : Set G) ≤ Subgroup.normalizer
      (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (T₀ : Set G)) : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore 2 (Subgroup.centralizer (T₀ : Set G))))
  have h := le_centralizer_of_O'' hZ' hTC hTK hK₂Y hcK hYK hDθ hDodd hcodd (hF.2 c hcF)
    (hFT hcF) hT₀ (CFSG.pCore_isPGroup.map _) hQN
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer,
    ← GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
  exact h

end General

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G}

theorem mem_map_conj_sec11K_of_conj_mem_zpowers (h45 : Sec4.Item4_5)
    (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hdc : d ∉ Subgroup.zpowers c) {n : G} (hnd : n * d * n⁻¹ ∈ Subgroup.zpowers c) :
    c ∈ (sec11K L a).map (MulAut.conj n).toMonoidHom := by
  have hdK : d ∈ sec11K L a := mem_sec11K_d h45 h hdL hdc
  have hd1 : d ≠ 1 := fun h1 => hdc (by rw [h1]; exact Subgroup.one_mem _)
  have hnd1 : n * d * n⁻¹ ≠ 1 := fun h1 => hd1 (by
    calc d = n⁻¹ * (n * d * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have heq := zpowers_eq_of_mem_of_ne_one hc3 hnd hnd1
  have hmem : n * d * n⁻¹ ∈ (sec11K L a).map (MulAut.conj n).toMonoidHom :=
    ⟨d, hdK, by simp [MulAut.conj_apply]⟩
  exact Subgroup.zpowers_le.mpr hmem (heq ▸ Subgroup.mem_zpowers c)

theorem false_of_bcD8_of_O'' (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})))
    (hdc : d ∉ Subgroup.zpowers c) {n : G} (hnd : n * d * n⁻¹ ∈ Subgroup.zpowers c)
    (hna : n * a * n⁻¹ ∈ Subgroup.zpowers a) (hYn : Y.map (MulAut.conj n).toMonoidHom ≠ Y)
    (hYK : Y = sec11K L a ⊔ inSubgroup (aschbacherSolvableCore 3) Y)
    (hO1 : Odd (Nat.card
      (⁅sec11K L a, (sec11K L a).map (MulAut.conj n).toMonoidHom⁆ : Subgroup G)))
    (hO2 : Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)), Subgroup.zpowers c⁆ : Subgroup G))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θa := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) with hθa
  set K := sec11K L a with hK
  set Kn := K.map (MulAut.conj n).toMonoidHom with hKn
  set Yn := Y.map (MulAut.conj n).toMonoidHom with hYn'
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcA := h.mem_A
  have haA := h.a_mem
  have hc1 := h.ne_one
  have hcB : c ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  have haB : a ∉ Subgroup.closure ({c, d} : Set G) := fun ha =>
    Item116Fusion.not_mem_innerPreimage h (Item116Fusion.closure_le_innerPreimage h hdL ha)
  have hac : a ∉ Subgroup.zpowers c := fun ha => haB (Subgroup.zpowers_le.mpr hcB ha)
  set F := Subgroup.closure ({c, a} : Set G) with hF
  have hFA : F ≤ A := by
    rw [hF, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hcA
    · exact haA
  have hFe : CFSG.Assembly.IsElemAbelian 3 F :=
    ⟨⟨⟨fun x y => Subtype.ext (hcomm _ (hFA x.2) _ (hFA y.2))⟩⟩, fun x hx => hexp x (hFA hx)⟩
  have hF9 : Nat.card F = 9 :=
    Item116Fusion.card_closure_pair_eq_nine hexp hcomm hcA haA hc1 hac
  have hcF : c ∈ F := Subgroup.subset_closure (by simp)
  obtain ⟨t, htK, ht2⟩ := exists_orderOf_eq_two_mem_sec11K h45 h hdL hdc
  have hT₀ : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hT₀1 : Subgroup.zpowers t ≠ ⊥ := fun h0 => ht1 (Subgroup.zpowers_eq_bot.mp h0)
  have htLa : t ∈ L ⊓ Subgroup.centralizer ({a} : Set G) := Subgroup.map_subtype_le _ htK
  have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hFT : F ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    rw [← GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, hF,
      Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with rfl | rfl
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hLc htLa.1)).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp htLa.2).symm
  have hna1 : n * a * n⁻¹ ≠ 1 := fun h1 => h.a_ne_one (by
    calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)
  have hYnL : Yn ∈ thetaComponentsAt 3 a := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj n) h.mem_thetaComponentsAt_Y
    rwa [MulAut.conj_apply, thetaComponentsAt_eq_of_zpowers_eq
      (zpowers_eq_of_mem_of_ne_one (hexp a haA) hna hna1)] at h1
  have hDθa : ⁅K, Kn⁆ ≤ θa :=
    (Subgroup.commutator_mono h.sec11K_le (Subgroup.map_mono h.sec11K_le)).trans
      (Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y hYnL
        hYn.symm)
  have hθYn : inSubgroup (aschbacherSolvableCore 3) Yn ≤ θa := by
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hYnL]
    exact inf_le_right
  have hYnK : Yn ≤ Kn ⊔ θa := by
    have h1 : Yn = Kn ⊔ inSubgroup (aschbacherSolvableCore 3) Yn := by
      rw [hYn', hKn, ← map_inSubgroup_aschbacherSolvableCore, ← Subgroup.map_sup, ← hYK]
    rw [h1]
    exact sup_le_sup_left hθYn _
  have hcKn : c ∈ Kn := mem_map_conj_sec11K_of_conj_mem_zpowers h45 h hdL hdc hnd
  have htr := Item116Fusion.exists_transvection_eq h hdL hWB hirr hdc
  refine false_of_charTwo_O'' h.charTwoType hFe hF9.ge hcF hc1 hT₀ hT₀1 hFT fun e heF hec => ?_
  obtain ⟨b, hb, he⟩ := exists_zpowers_eq_mul (hcomm c hcA a haA) (hexp a haA) heF hec
  obtain ⟨w, -, hwB, hwa⟩ := htr b (Subgroup.zpowers_le.mpr hcB hb)
  have hwc : w * c * w⁻¹ = c := hwB c hcB
  have he' : Subgroup.zpowers e = Subgroup.zpowers (w * a * w⁻¹) := by
    rw [hwa]
    exact he
  have hCe : Subgroup.centralizer ({e} : Set G) =
      (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj w).toMonoidHom := by
    rw [centralizer_eq_of_zpowers_eq he', map_centralizer_singleton, MulAut.conj_apply]
  have hθe : inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) =
      θa.map (MulAut.conj w).toMonoidHom := by
    rw [hCe, hθa, map_inSubgroup_aschbacherSolvableCore]
  have hKw : K.map (MulAut.conj w).toMonoidHom = K := map_conj_sec11K_eq h45 h hwc hwa hb
  have hcw : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwc]
  refine ⟨Yn.map (MulAut.conj w).toMonoidHom, ?_, K, Kn.map (MulAut.conj w).toMonoidHom,
    Subgroup.zpowers_le.mpr htK, Subgroup.map_mono (Subgroup.map_mono h.sec11K_le), ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [thetaComponentsAt_eq_of_zpowers_eq he', ← MulAut.conj_apply]
    exact map_mem_thetaComponentsAt (MulAut.conj w) hYnL
  · have := Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom hcKn
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwc] at this
  · rw [hθe, ← Subgroup.map_sup]
    exact Subgroup.map_mono hYnK
  · rw [hθe, ← hKw, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hDθa
  · have heq : (⁅K, Kn.map (MulAut.conj w).toMonoidHom⁆ : Subgroup G) =
        (⁅K, Kn⁆ : Subgroup G).map (MulAut.conj w).toMonoidHom := by
      rw [Subgroup.map_commutator, hKw]
    rw [heq, Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact hO1
  · have heq : (⁅θa.map (MulAut.conj w).toMonoidHom, Subgroup.zpowers c⁆ : Subgroup G) =
        (⁅θa, Subgroup.zpowers c⁆ : Subgroup G).map (MulAut.conj w).toMonoidHom := by
      rw [Subgroup.map_commutator, hcw]
    rw [hθe, heq, Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact hO2

end Certified

end TheoremO

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G}

theorem not_Eii (hP2b : Item116P2b) (hP2c : Item116P2c) (h45 : Sec4.Item4_5)
    (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})))
    (hRG : CFSG.ABGLocalTools.IsSylowOf 3 R ⊤) (hdc : d ∉ Subgroup.zpowers c)
    (hD8 : ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c))
    {n : G} (hnW : n ∈ Subgroup.normalizer (A : Set G)) (hnc : n * c * n⁻¹ ∈ Subgroup.zpowers d)
    (hnd : n * d * n⁻¹ ∈ Subgroup.zpowers c) (hna : n * a * n⁻¹ = a⁻¹) {S : Subgroup G}
    (hS : fusionIsSylowIn 2 S
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))) :
    ⁅S, A⁆ ≠ ⊥ := by
  intro hSA
  have hAe := h.mem_partTwoF.1
  have hA3 : IsPGroup 3 A :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_isPGroup 3 A hAe
  have hYn := hP2b G A c L a R Y h d hdL hWB hirr hRG hdc hD8 n hnW hnc hnd hna
  have hYK := hP2c G A c L a R Y h d hdL hWB hirr hRG hdc hD8 n hnW hnc hnd hna
  have hna' : n * a * n⁻¹ ∈ Subgroup.zpowers a := by
    rw [hna]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hO1 := commutator_KKn_odd_of_Eii h45 h hdL hdc hnW hna' hYn hS hSA
  have hAθ : A ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)) : Subgroup G) : Set G) :=
    (CFSG.RankThreeEvenClassification.Helpers.commutative_plane_le_element_centralizer A hAe.1 a
      h.a_mem).trans (Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta _))
  have hle := Eii.commutator_le_oddCoreOf hA3 (not_three_dvd_card_inSubgroup_theta _)
    (isSolvable_inSubgroup_theta _) hAθ hS hSA
  have hO2 := Eii.odd_card_of_le_oddCoreOf
    ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr h.mem_A)).trans hle)
  exact TheoremO.false_of_bcD8_of_O'' h45 h hdL hWB hirr hdc hnd hna' hYn hYK hO1 hO2

end Certified

end CFSG.RankThree.PartTwo.Sec11
