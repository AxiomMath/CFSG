module

public import CFSG.RankThree.PartTwo.Late.Glue
import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
import CFSG.RankThree.CentralCover.FourGroupWitness
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree.PartTwo
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_of_le {p : ℕ} {E V : Subgroup G} (hV : CFSG.Assembly.IsElemAbelian p V)
    (hEV : E ≤ V) : CFSG.Assembly.IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hV hEV

theorem exists_elemAbelian_le_of_le_pRank_three {X : Subgroup G} {k : ℕ}
    (hk : k ≤ CFSG.Open.pRank 3 X) :
    ∃ E : Subgroup G, E ≤ X ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₀, hE₀X, hE₀, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) X
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E₀) 3 (n := k)
    (by rw [hcard]; exact pow_dvd_pow 3 hk)
  refine ⟨K.map E₀.subtype, (Subgroup.map_subtype_le K).trans hE₀X, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, ⟨x, -, rfl⟩⟩ ⟨_, ⟨y, -, rfl⟩⟩
    apply Subtype.ext
    change (x : G) * y = y * x
    exact congrArg Subtype.val (hE₀.1.is_comm.comm x y)
  · rintro _ ⟨x, -, rfl⟩
    exact hE₀.2 x x.2
  · rw [Subgroup.card_map_of_injective E₀.subtype_injective, hK]

theorem two_le_pRank_of_elemAbelian {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (h9 : 9 ≤ Nat.card E) : 2 ≤ CFSG.Open.pRank 3 E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hE3.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra! hlt
    have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hk2.trans (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hE hk)

theorem isE27_sup_zpowers {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) {x : G} (hx : x ∉ E) (hx3 : x ^ 3 = 1)
    (hxE : ∀ e ∈ E, e * x = x * e) : IsE27 (E ⊔ Subgroup.zpowers x) := by
  have hx1 : x ≠ 1 := fun h => hx (h ▸ E.one_mem)
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hZc : Subgroup.zpowers x ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr hxE)
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (E : Set G) :=
    hZc.trans (Subgroup.centralizer_le_normalizer _)
  have hZ3 : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hord]
  have hdisj : E ⊓ Subgroup.zpowers x = ⊥ := by
    have hdvd : Nat.card (E ⊓ Subgroup.zpowers x : Subgroup G) ∣ 3 :=
      hZ3 ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_right : E ⊓ Subgroup.zpowers x ≤ _)
        (by rw [h, hZ3])
      have hxEZ : x ∈ E ⊓ Subgroup.zpowers x := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hx (Subgroup.mem_inf.mp hxEZ).1
  have hcard : Nat.card (E ⊔ Subgroup.zpowers x : Subgroup G) = 27 := by
    rw [CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hle hdisj, hE9, hZ3]
  have hEE : E ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hE.1
  have hZZ : Subgroup.zpowers x ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hcomm : IsMulCommutative (E ⊔ Subgroup.zpowers x : Subgroup G) := by
    rw [← Subgroup.le_centralizer_iff_isMulCommutative]
    refine sup_le ?_ ?_
    · exact Subgroup.le_centralizer_iff.mpr (sup_le hEE hZc)
    · exact Subgroup.le_centralizer_iff.mpr (sup_le (Subgroup.le_centralizer_iff.mpr hZc) hZZ)
  refine ⟨⟨hcomm, fun y hy => ?_⟩, hcard⟩
  have hy' : y ∈ ((E : Set G) * (Subgroup.zpowers x : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left E _ hle]
    exact hy
  obtain ⟨e, he, z, hz, rfl⟩ := hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hc : Commute e (x ^ k) := Commute.zpow_right (hxE e he) k
  rw [hc.mul_pow, hE.2 e he, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hx3, one_zpow]

theorem isCyclic_of_forall_elemAbelian_card_le_three {C : Subgroup G} (hC : IsPGroup 3 C)
    (h : ∀ F : Subgroup G, F ≤ C → CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 3) :
    IsCyclic C := by
  have hr : CFSG.pRank 3 C ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    refine CFSG.SectionRank.pRank_le (by norm_num) fun F _ hF => ?_
    have hmap := CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 C.subtype F hF
    have := h (F.map C.subtype) (Subgroup.map_subtype_le F) hmap
    rwa [Subgroup.card_map_of_injective C.subtype_injective, ← pow_one 3] at this
  rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification Nat.prime_three
    hC).mp hr with hcyc | ⟨h32, -⟩
  · exact hcyc
  · norm_num at h32

theorem card_le_three_mul_card_inf {U C V : Subgroup G}
    (hCU : C ≤ Subgroup.centralizer (U : Set G)) (hC : IsCyclic C) (hVW : V ≤ U ⊔ C)
    (hV : CFSG.Assembly.IsElemAbelian 3 V) : Nat.card V ≤ 3 * Nat.card (V ⊓ U : Subgroup G) := by
  set W := U ⊔ C with hWdef
  have hCN : C ≤ Subgroup.normalizer (U : Set G) :=
    hCU.trans (Subgroup.centralizer_le_normalizer _)
  have hWN : W ≤ Subgroup.normalizer (U : Set G) := sup_le Subgroup.le_normalizer hCN
  have hN : (U.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hWN
  let π : W →* W ⧸ U.subgroupOf W := QuotientGroup.mk' (U.subgroupOf W)
  have hsurj : Function.Surjective (π.comp (Subgroup.inclusion (le_sup_right : C ≤ W))) := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    have hw : (w : G) ∈ ((U : Set G) * (C : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left U C hCN]
      exact w.2
    obtain ⟨u, hu, c, hc, hwuc⟩ := hw
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [MonoidHom.comp_apply]
    change π _ = π w
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨⟨u, (le_sup_left : U ≤ W) hu⟩, Subgroup.mem_subgroupOf.mpr hu, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]
    rw [← Subgroup.mem_centralizer_iff.mp (hCU hc) u hu]
    exact hwuc
  have hQ : IsCyclic (W ⧸ U.subgroupOf W) := isCyclic_of_surjective _ hsurj
  let g : V.subgroupOf W →* W ⧸ U.subgroupOf W := π.comp (V.subgroupOf W).subtype
  have hrange : Nat.card g.range ≤ 3 := by
    have hexp : Monoid.exponent g.range ∣ 3 := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun q => ?_
      obtain ⟨⟨v, hv⟩, hq⟩ := q.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hq, ← map_pow]
      have hv3 : (⟨v, hv⟩ : V.subgroupOf W) ^ 3 = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        exact hV.2 _ (Subgroup.mem_subgroupOf.mp hv)
      rw [hv3, map_one, Subgroup.coe_one]
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by norm_num) hexp
  have hker : Nat.card g.ker ≤ Nat.card (V ⊓ U : Subgroup G) := by
    refine Nat.card_le_card_of_injective (fun x => (⟨((x : V.subgroupOf W) : W), ?_⟩ :
      (V ⊓ U : Subgroup G))) ?_
    · refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp (x : V.subgroupOf W).2, ?_⟩
      have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have : ((x : V.subgroupOf W) : W) ∈ U.subgroupOf W :=
        (QuotientGroup.eq_one_iff _).mp hx
      exact Subgroup.mem_subgroupOf.mp this
    · intro x y hxy
      have h' := congrArg Subtype.val hxy
      simp only at h'
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
  have hcardV : Nat.card V = Nat.card (V.subgroupOf W) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW).toEquiv.symm
  rw [hcardV, ← Subgroup.card_mul_index g.ker, Subgroup.index_ker, mul_comm]
  exact Nat.mul_le_mul hrange hker

theorem centralizer_le_of_conditions {P M U : Subgroup G} (hP : IsPGroup 3 P) (hPM : P ≤ M)
    (hUP : U ≤ P) (hC1 : ∀ V : Subgroup G, IsE27 V → V ≤ M → gamma 2 V ≤ M)
    (hU2 : 1 < CFSG.Open.pRank 3 U)
    (hW3 : 2 < CFSG.Open.pRank 3 (U ⊔ (P ⊓ Subgroup.centralizer (U : Set G)))) :
    Subgroup.centralizer (U : Set G) ≤ M := by
  suffices h : ∃ E V : Subgroup G, E ≤ U ∧ 2 ≤ CFSG.Open.pRank 3 E ∧ E ≤ V ∧ IsE27 V ∧ V ≤ M by
    obtain ⟨E, V, hEU, hE2, hEV, hV, hVM⟩ := h
    calc Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer (E : Set G) :=
          Subgroup.centralizer_le hEU
      _ ≤ Subgroup.normalizer (E : Set G) := Subgroup.centralizer_le_normalizer _
      _ ≤ gamma 2 V := normalizer_le_gamma hEV hE2
      _ ≤ M := hC1 V hV hVM
  have hUM : U ≤ M := hUP.trans hPM
  have hWP : U ⊔ (P ⊓ Subgroup.centralizer (U : Set G)) ≤ P := sup_le hUP inf_le_left
  obtain ⟨V, hVW, hV, hV27⟩ := exists_elemAbelian_le_of_le_pRank_three (k := 3) hW3
  have hVE : IsE27 V := ⟨hV, by rw [hV27]; norm_num⟩
  by_cases h1 : 2 < CFSG.Open.pRank 3 U
  · obtain ⟨V₀, hV₀U, hV₀, hV₀27⟩ := exists_elemAbelian_le_of_le_pRank_three (k := 3) h1
    have hV₀E : IsE27 V₀ := ⟨hV₀, by rw [hV₀27]; norm_num⟩
    exact ⟨V₀, V₀, hV₀U, by rw [hV₀E.pRank_eq]; norm_num, le_rfl, hV₀E, hV₀U.trans hUM⟩
  obtain ⟨E₁, hE₁U, hE₁, hE₁9⟩ := exists_elemAbelian_le_of_le_pRank_three (k := 2) hU2
  have hE₁r : 2 ≤ CFSG.Open.pRank 3 E₁ := two_le_pRank_of_elemAbelian hE₁ (by rw [hE₁9]; norm_num)
  by_cases h2 : ∃ E₀ : Subgroup G, E₀ ≤ U ⊓ Subgroup.centralizer (U : Set G) ∧
      CFSG.Assembly.IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 9
  · obtain ⟨E₀, hE₀, hE₀a, hE₀9⟩ := h2
    have hE₀U : E₀ ≤ U := hE₀.trans inf_le_left
    have hWC : U ⊔ (P ⊓ Subgroup.centralizer (U : Set G)) ≤
        Subgroup.centralizer (E₀ : Set G) := by
      refine sup_le (Subgroup.le_centralizer_iff.mpr (hE₀.trans inf_le_right)) ?_
      exact inf_le_right.trans (Subgroup.centralizer_le hE₀U)
    obtain ⟨v, hvV, hvE⟩ : ∃ v ∈ V, v ∉ E₀ := by
      by_contra! hall
      have := Subgroup.card_le_of_le (show V ≤ E₀ from fun v hv => hall v hv)
      rw [hV27, hE₀9] at this
      norm_num at this
    refine ⟨E₀, E₀ ⊔ Subgroup.zpowers v, hE₀U, two_le_pRank_of_elemAbelian hE₀a hE₀9.ge,
      le_sup_left, isE27_sup_zpowers hE₀a hE₀9 hvE (hV.2 v hvV) fun e he => ?_, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mp (hWC (hVW hvV)) e he
    · exact sup_le (hE₀U.trans hUM) (Subgroup.zpowers_le.mpr (hPM (hWP (hVW hvV))))
  by_cases h3 : ∃ x ∈ P ⊓ Subgroup.centralizer (U : Set G), x ^ 3 = 1 ∧ x ∉ U
  · obtain ⟨x, hxC, hx3, hxU⟩ := h3
    refine ⟨E₁, E₁ ⊔ Subgroup.zpowers x, hE₁U, hE₁r, le_sup_left,
      isE27_sup_zpowers hE₁ hE₁9 (fun h => hxU (hE₁U h)) hx3 fun e he => ?_, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxC).2 e (hE₁U he)
    · exact sup_le (hE₁U.trans hUM) (Subgroup.zpowers_le.mpr (hPM (Subgroup.mem_inf.mp hxC).1))
  push Not at h2 h3
  have hcyc : IsCyclic (P ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) := by
    refine isCyclic_of_forall_elemAbelian_card_le_three (hP.to_le inf_le_left) fun F hFC hF => ?_
    have hFZ : F ≤ U ⊓ Subgroup.centralizer (U : Set G) := fun y hy =>
      ⟨h3 y (hFC hy) (hF.2 y hy), (Subgroup.mem_inf.mp (hFC hy)).2⟩
    have hF3 : IsPGroup 3 F := fun x => ⟨1, Subtype.ext (by simpa using hF.2 x x.2)⟩
    obtain ⟨k, hk⟩ := hF3.exists_card_eq
    by_contra hlt
    have hk2 : 2 ≤ k := by
      by_contra! hk1
      have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) 3 (n := 2)
      (by rw [hk]; exact pow_dvd_pow 3 hk2)
    refine h2 (K.map F.subtype) ((Subgroup.map_subtype_le K).trans hFZ)
      (isElemAbelian_of_le hF (Subgroup.map_subtype_le K)) ?_
    rw [Subgroup.card_map_of_injective F.subtype_injective, hK]
    norm_num
  have hcard := card_le_three_mul_card_inf inf_le_right hcyc hVW hV
  rw [hV27] at hcard
  refine ⟨V ⊓ U, V, inf_le_right, two_le_pRank_of_elemAbelian (isElemAbelian_of_le hV inf_le_left)
    (by omega), inf_le_left, hVE, hVW.trans (hWP.trans hPM)⟩

theorem gammaZeroLemma : GammaZeroLemma G := by
  intro P M hP hPM hC1 hC2
  rw [gammaZero_le_iff]
  intro U hUP hU2 hW3 g hg
  have hCM := centralizer_le_of_conditions hP hPM hUP hC1 hU2 hW3
  obtain ⟨V, hVW, hV, hV27⟩ := exists_elemAbelian_le_of_le_pRank_three (k := 3) hW3
  have hVE : IsE27 V := ⟨hV, by rw [hV27]; norm_num⟩
  have hWP : U ⊔ (P ⊓ Subgroup.centralizer (U : Set G)) ≤ P := sup_le hUP inf_le_left
  refine hC2 V g hVE (hVW.trans (hWP.trans hPM)) ?_
  have hVUC : V ≤ U ⊔ Subgroup.centralizer (U : Set G) :=
    hVW.trans (sup_le_sup_left inf_le_right U)
  rw [Subgroup.map_le_iff_le_comap]
  refine hVUC.trans (sup_le (fun u hu => ?_) fun c hc => ?_)
  · rw [Subgroup.mem_comap]
    exact hUP.trans hPM ((Subgroup.mem_normalizer_iff.mp hg u).mp hu)
  · rw [Subgroup.mem_comap]
    apply hCM
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : g⁻¹ * u * g ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) u).mp hu
      simpa using this
    have hcu := Subgroup.mem_centralizer_iff.mp hc _ hu'
    change u * (g * c * g⁻¹) = g * c * g⁻¹ * u
    calc u * (g * c * g⁻¹) = g * ((g⁻¹ * u * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * u * g)) * g⁻¹ := by rw [hcu]
      _ = g * c * g⁻¹ * u := by group

theorem rank3II_19_20 (h1912 : Item1912) : Item1920 :=
  rank3II_19_20_reduction (fun _ _ _ => gammaZeroLemma) h1912

theorem item2011_of_item2010_item1912 (h2010 : Item2010) (h1912 : Item1912) : Item2011 :=
  rank3II_20_11_reduction h2010 (rank3II_19_20 h1912)

end CFSG.RankThree.PartTwo.Late
