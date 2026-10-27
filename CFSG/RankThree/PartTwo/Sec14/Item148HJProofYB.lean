module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofCover
import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Item148HJ

theorem le_inSubgroup_perfectResidual {X : Type*} [Group X] [Finite X] {S T : Subgroup X}
    (hST : S ≤ T) (hS : Group.IsPerfect S) : S ≤ inSubgroup perfectResidual T := by
  have hS' : Group.IsPerfect (S.subgroupOf T) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hST).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have h := (perfect_residual_transport (MonoidHom.id ↥T)).2.2 _ hS'
  have h' := Subgroup.map_mono (f := T.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hST] at h'

theorem eq_top_of_pow_mem {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) {D : Subgroup Q}
    (hD : D.Normal) {m : ℕ} (hm : Nat.Coprime m 3) (hpow : ∀ w : Q, w ^ m ∈ D) {w₀ : Q}
    (hw₀3 : w₀ ^ 3 = 1) (hw₀ : w₀ ∉ Subgroup.center Q) : D = ⊤ := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hD with h | h
  · exact h
  · exfalso
    apply hw₀
    have hm3 : (m * (m % 3)) % 3 = 1 := by
      have h1 : m % 3 = 1 ∨ m % 3 = 2 := by
        have := Nat.Coprime.symm hm
        have h0 : m % 3 ≠ 0 := fun h0 => by
          have : 3 ∣ m := Nat.dvd_of_mod_eq_zero h0
          exact absurd (Nat.Coprime.coprime_dvd_left this hm) (by norm_num)
        omega
      rcases h1 with h1 | h1 <;> simp [Nat.mul_mod, h1]
    have key : w₀ = (w₀ ^ m) ^ (m % 3) := by
      rw [← pow_mul, ← Nat.mod_add_div (m * (m % 3)) 3, hm3, pow_add, pow_mul, hw₀3, one_pow,
        mul_one, pow_one]
    rw [key]
    exact pow_mem (h (hpow w₀)) _

theorem eq_bot_of_normal_of_quasisimple' {Q : Type*} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (hZ : IsPGroup 3 (Subgroup.center Q)) (h3Q : 3 ∣ Nat.card Q) {M : Subgroup Q}
    (hM : M.Normal) (hM3 : ¬ 3 ∣ Nat.card M) : M = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hM with h | h
  · exfalso
    apply hM3
    rw [h, Subgroup.card_top]
    exact h3Q
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hZ.to_le h)
    rcases n with _ | n
    · exact Subgroup.eq_bot_of_card_eq M (by rw [hn, pow_zero])
    · exact absurd (hn ▸ dvd_pow_self 3 (Nat.succ_ne_zero n)) hM3

theorem alternatingGroup_five_facts :
    IsQuasisimple (alternatingGroup (Fin 5)) ∧ Subgroup.center (alternatingGroup (Fin 5)) = ⊥ ∧
      ∃ w : alternatingGroup (Fin 5), w ^ 3 = 1 ∧ w ≠ 1 := by
  have hne : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
      ⟨Equiv.swap 1 2 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
      fun h => ?_⟩
    have := congrArg Subtype.val h
    revert this
    decide
  obtain ⟨hq, hc⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hne
  exact ⟨hq, hc, ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    Subtype.ext (by decide), fun h => absurd (congrArg Subtype.val h) (by decide)⟩

theorem isPerfect_inSubgroup_perfectResidual {X : Type*} [Group X] [Finite X] (T : Subgroup X) :
    Group.IsPerfect ↥(inSubgroup perfectResidual T) := by
  have h := (perfect_residual_characterization (G := ↥T)).2.2.1
  exact Group.IsPerfect.ofSurjective
    (f := ((perfectResidual ↥T).equivMapOfInjective _ (Subgroup.subtype_injective _)).toMonoidHom)
    (MulEquiv.surjective _)

theorem not_dvd_card_comap {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    {U : Subgroup Y} (hU : ¬ 3 ∣ Nat.card U) (hk : ¬ 3 ∣ Nat.card f.ker) :
    ¬ 3 ∣ Nat.card (U.comap f) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hg' : orderOf (g : X) = 3 := by rw [Subgroup.orderOf_coe]; exact hg
  have h1 : orderOf (f g) ∣ 3 := hg' ▸ orderOf_map_dvd f g
  have h2 : orderOf (f g) ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U g.2
  have h3' : orderOf (f g) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) hU
  have hker : (g : X) ∈ f.ker := orderOf_eq_one_iff.mp h3'
  apply hk
  have := Subgroup.orderOf_dvd_natCard f.ker hker
  rwa [hg'] at this

theorem aschbacherSolvableCore_eq_ker {K Y : Type*} [Group K] [Group Y] [Finite K] [Finite Y]
    (φ : K →* Y) (hq : IsQuasisimple φ.range) (hZ : IsPGroup 3 (Subgroup.center φ.range))
    (h3 : 3 ∣ Nat.card φ.range) (hs : Group.IsSolvable φ.ker) (hk3 : ¬ 3 ∣ Nat.card φ.ker) :
    aschbacherSolvableCore 3 K = φ.ker := by
  obtain ⟨-, -, hθ3, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  apply le_antisymm
  · have hn : ((aschbacherSolvableCore 3 K).map φ.rangeRestrict).Normal :=
      (aschbacherSolvableCore_normal 3 K).map _ φ.rangeRestrict_surjective
    have h3' : ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 K).map φ.rangeRestrict) := fun h =>
      hθ3 (h.trans (Subgroup.card_map_dvd _ _))
    have hb := eq_bot_of_normal_of_quasisimple' hq hZ h3 hn h3'
    intro m hm
    have : φ.rangeRestrict m ∈ (aschbacherSolvableCore 3 K).map φ.rangeRestrict :=
      Subgroup.mem_map_of_mem _ hm
    rw [hb, Subgroup.mem_bot] at this
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val this
  · exact hmax _ (MonoidHom.normal_ker φ) hs hk3

end Item148HJ

section Main

variable {G : Type} [Group G] [Finite G]

theorem le_sup_residual {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) {Q : Subgroup G}
    (hQ : Q ∈ scriptQZero A (lB A)) (hQB : Q ≤ Subgroup.centralizer (B : Set G)) :
    Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔
      inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) := by
  set C := Subgroup.centralizer (B : Set G) with hCdef
  set N := pPrimeCoreOf 3 C with hNdef
  set J := inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) with hJdef
  have hD := h.toSec13Data
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hAC : A ≤ C := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAab y (hB.1 hy) x hx
  have hCA : Subgroup.centralizer (A : Set G) ≤ C := Subgroup.centralizer_le hB.1
  have hJN : C ≤ Subgroup.normalizer (J : Set G) :=
    Item148HJ.centralizer_le_normalizer_residual h hc
  have hCNJ : C ≤ Subgroup.normalizer ((N ⊔ J : Subgroup G) : Set G) :=
    le_normalizer_sup (le_normalizer_pPrimeCoreOf 3 C) hJN
  have h1 := hQ.1.2 B hB
  rw [inf_eq_left.mpr hQB, qBound, Item148HJ.lB_eq_residual h hB hc, sup_right_comm] at h1
  rw [hQ.2]
  exact (Subgroup.commutator_mono h1 le_rfl).trans (commutator_sup_le148 (hAC.trans hCNJ)
    (((pPrimeCoreOf_le 3 _).trans hCA).trans hCNJ) (pPrimeCoreOf_le 3 _))

theorem step148YBShape_holds : Step148YBShape := by
  intro G _ _ A c L h Y hY hs B hB hnot b d Lb hc
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (B : Set G) with hCdef
  set N := pPrimeCoreOf 3 C with hNdef
  set J := inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) with hJdef
  have hJC : J ≤ C := Item148HJ.residual_le_centralizer hc
  have hJN : C ≤ Subgroup.normalizer (J : Set G) :=
    Item148HJ.centralizer_le_normalizer_residual h hc
  have hJlB : J ≤ lB A B := Item148HJ.residual_le_lB hc
  obtain ⟨hdL, hrange, hq, hZ, hperfR, htc, -⟩ := Item148HJ.resProj_facts h hB hc
  obtain ⟨a₀, ha₀, ha₀d, -⟩ := Item148HJ.exists_mem_not_mem_zpowers h hB hc
  have ha₀J : a₀ ∈ J := Item148HJ.inf_le_residual h hB hc ha₀
  obtain ⟨j₀, hj₀J, hj₀⟩ := Item148HJ.exists_commutator_not_mem h hB hc ha₀ ha₀d
  have hD := h.toSec13Data
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hAC : A ≤ C := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAab y (hB.1 hy) x hx
  have hCN : C ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hN3 : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 C
  have hJNθ : ∀ x ∈ J, x ∈ N → x ∈ inSubgroup (aschbacherSolvableCore 3) Lb := by
    intro x hxJ hxN
    have hMn : (N.subgroupOf J).Normal :=
      Subgroup.normal_subgroupOf_iff_le_normalizer_inf.mpr
        (Late.le_normalizer_inf (hJC.trans hCN) Subgroup.le_normalizer)
    have hM3 : ¬ 3 ∣ Nat.card (N.subgroupOf J) := fun h3 =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3 (h3.trans (by
        rw [← Subgroup.card_map_of_injective J.subtype_injective, Subgroup.subgroupOf_map_subtype]
        exact Subgroup.card_dvd_of_le inf_le_left))
    exact (Item148HJ.mem_ker_resProj ⟨x, hxJ⟩).mp
      (Item148HJ.le_ker_of_normal _ hq hZ hMn hM3 (Subgroup.mem_subgroupOf.mpr hxN))
  have hθN : ∀ x ∈ J, x ∈ inSubgroup (aschbacherSolvableCore 3) Lb → x ∈ N := by
    intro x hxJ hxθ
    have hS := Item148HJ.sec14Std_of_isLBConfig h hc
    have hbB : b ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert b {d})
    have hCLb : C ≤ Subgroup.normalizer (Lb : Set G) :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)).trans
        (centralizer_le_normalizer_of_j2 hS (Item148HJ.j2_of_isLBConfig hc))
    have hθn : C ≤ Subgroup.normalizer
        ((inSubgroup (aschbacherSolvableCore 3) Lb : Subgroup G) : Set G) :=
      hCLb.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
        Lb _ (solvable_prime_complement_core_characterization Nat.prime_three).2.1)
    obtain ⟨-, -, hθ3, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
    have hle : inSubgroup (aschbacherSolvableCore 3) Lb ⊓ C ≤ N :=
      le_pPrimeCoreOf inf_le_right (Late.le_normalizer_inf hθn Subgroup.le_normalizer)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hθ3 (h3.trans (by
          refine (Subgroup.card_dvd_of_le inf_le_left).trans ?_
          rw [inSubgroup, Subgroup.card_map_of_injective Lb.subtype_injective])))
    exact hle ⟨hxθ, hJC hxJ⟩
  set N₀ := CFSG.pPrimeCore 3 ↥C with hN₀def
  have hN₀3 : Nat.Coprime 3 (Nat.card N₀) := CFSG.pPrimeCore_coprime_card
  set π := QuotientGroup.mk' N₀ with hπdef
  set JH := J.subgroupOf C with hJHdef
  set 𝔍 := JH.map π with h𝔍def
  have hNsub : N.subgroupOf C = N₀ := by
    rw [hNdef, pPrimeCoreOf, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
  have hJHn : JH.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJC).mpr hJN
  have hcomap𝔍 : 𝔍.comap π = N₀ ⊔ JH := by
    rw [h𝔍def, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  have hsup : (N ⊔ J).subgroupOf C = N₀ ⊔ JH := by
    rw [Subgroup.subgroupOf_sup (pPrimeCoreOf_le 3 C) hJC, hNsub]
  set ψ₁ : ↥J →* (↥C ⧸ N₀) := π.comp (Subgroup.inclusion hJC) with hψ₁
  have hψ₁r : ψ₁.range = 𝔍 := by rw [hψ₁, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : ψ₁.ker = (Item148HJ.resProj Lb d).ker := by
    ext j
    rw [MonoidHom.mem_ker, Item148HJ.mem_ker_resProj, hψ₁, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hj
      exact hJNθ j j.2 ⟨_, hj, rfl⟩
    · intro hj
      obtain ⟨n, hn, hnj⟩ := hθN j j.2 hj
      have : n = Subgroup.inclusion hJC j := Subtype.ext hnj
      exact this ▸ hn
  let e𝔍 : ↥𝔍 ≃* ↥(Item148HJ.resProj Lb d).range :=
    (MulEquiv.subgroupCongr hψ₁r.symm).trans (Item148HJ.rangeEquivOfKerEq ψ₁ _ hker)
  have h𝔍tc : Sec4.IsTripleCover ↥𝔍 (alternatingGroup (Fin 6)) :=
    KFacts.KS14.isTripleCover_congr e𝔍.symm htc
  have h𝔍p : Group.IsPerfect ↥𝔍 :=
    Group.IsPerfect.ofSurjective (f := e𝔍.symm.toMonoidHom) e𝔍.symm.surjective
  have h𝔍q : IsQuasisimple ↥𝔍 := CFSG.LocalCores.isQuasisimple_of_mulEquiv e𝔍.symm hq
  set a₀C : ↥C := ⟨a₀, hAC ha₀.1⟩ with ha₀C
  set x := π a₀C with hxdef
  have hx𝔍 : x ∈ 𝔍 := ⟨a₀C, Subgroup.mem_subgroupOf.mpr ha₀J, rfl⟩
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, ← map_pow]
    have : a₀C ^ 3 = 1 := Subtype.ext (by simpa using hD.isElemAbelian.2 a₀ ha₀.1)
    rw [this, map_one]
  have hcommJ : ∀ u ∈ J, ∀ v ∈ J, ⁅u, v⁆ ∈ J := fun u hu v hv =>
    Subgroup.commutator_mem_commutator hu hv |> (Subgroup.commutator_le_self J)
  have hxZ : ∃ y ∈ 𝔍, x * y ≠ y * x := by
    refine ⟨π ⟨j₀, hJC hj₀J⟩, ⟨_, Subgroup.mem_subgroupOf.mpr hj₀J, rfl⟩, fun hxy => hj₀ ?_⟩
    have hcm : π ⁅(⟨j₀, hJC hj₀J⟩ : ↥C), a₀C⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hxy.symm
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcm
    exact hJNθ _ (hcommJ _ hj₀J _ ha₀J) ⟨_, hcm, rfl⟩
  set YC := Y ⊓ C with hYCdef
  set YCH := YC.subgroupOf C with hYCHdef
  set Tt := YCH.map π ⊓ 𝔍 with hTtdef
  have ha₀YC : a₀ ∈ Subgroup.normalizer (YC : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hY.2 ha₀.1, Subgroup.le_normalizer (hAC ha₀.1)⟩
  have hconj : ∀ (g : ↥C) {X : Subgroup G}, (g : G) ∈ Subgroup.normalizer (X : Set G) →
      g ∈ Subgroup.normalizer ((X.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    intro g X hX
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hX y
  have hxT : x ∈ Subgroup.normalizer (Tt : Set (↥C ⧸ N₀)) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer_map π ⟨a₀C, hconj a₀C ha₀YC, rfl⟩, Subgroup.le_normalizer hx𝔍⟩
  have hQprops : ∀ Q ∈ collectionIn (scriptQZero A (lB A)) YC,
      (Q.subgroupOf C).map π ≤ Tt ∧ ¬ 3 ∣ Nat.card ((Q.subgroupOf C).map π) ∧
        x ∈ Subgroup.normalizer (((Q.subgroupOf C).map π : Subgroup (↥C ⧸ N₀)) : Set _) ∧
        Q ≤ N ⊔ J := by
    intro Q hQ
    obtain ⟨hQ0, hQYC⟩ := hQ
    have hQC : Q ≤ C := hQYC.trans inf_le_right
    have hQNJ : Q ≤ N ⊔ J := le_sup_residual h hB hc hQ0 hQC
    refine ⟨le_inf (Subgroup.map_mono (Subgroup.comap_mono hQYC)) ?_, ?_, ?_, hQNJ⟩
    · have h1 : Q.subgroupOf C ≤ N₀ ⊔ JH := hsup ▸ Subgroup.comap_mono hQNJ
      calc (Q.subgroupOf C).map π ≤ (N₀ ⊔ JH).map π := Subgroup.map_mono h1
        _ = 𝔍 := by
          rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),
            bot_sup_eq]
    · intro h3
      have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ0.1.1.2.1
      apply hQ3
      refine h3.trans ((Subgroup.card_map_dvd _ π).trans ?_)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv]
    · exact Subgroup.le_normalizer_map π ⟨a₀C, hconj a₀C (hQ0.1.1.2.2 ha₀.1), rfl⟩
  set M := YC ⊓ (N ⊔ J) with hMdef
  have hMT : ∀ m ∈ M, ∃ hmC : m ∈ C, π ⟨m, hmC⟩ ∈ Tt := by
    intro m hm
    refine ⟨hm.1.2, ⟨_, Subgroup.mem_subgroupOf.mpr hm.1, rfl⟩, ?_⟩
    have : (⟨m, hm.1.2⟩ : ↥C) ∈ 𝔍.comap π := by
      rw [hcomap𝔍, ← hsup]
      exact Subgroup.mem_subgroupOf.mpr hm.2
    exact this
  have hTM : ∀ t ∈ Tt, ∃ m : ↥C, (m : G) ∈ M ∧ π m = t := by
    rintro t ⟨⟨m, hm, rfl⟩, ht⟩
    have : m ∈ 𝔍.comap π := ht
    rw [hcomap𝔍, ← hsup] at this
    exact ⟨m, ⟨Subgroup.mem_subgroupOf.mp hm, Subgroup.mem_subgroupOf.mp this⟩, rfl⟩
  rcases Item148HJ.triple_cover_dichotomy_in h𝔍tc h𝔍p hx𝔍 hx3 hxZ inf_le_right hxT with
    hα | ⟨hP, hPU⟩
  ·
    exfalso
    apply hnot
    have hCNJ : C ≤ Subgroup.normalizer ((N ⊔ J : Subgroup G) : Set G) :=
      le_normalizer_sup hCN hJN
    have hYCM : YC ≤ Subgroup.normalizer (M : Set G) :=
      Late.le_normalizer_inf Subgroup.le_normalizer (inf_le_right.trans hCNJ)
    have hOM : pPrimeCoreOf 3 M ≤ pPrimeCoreOf 3 YC :=
      le_pPrimeCoreOf ((pPrimeCoreOf_le 3 M).trans inf_le_left)
        (hYCM.trans (normalizer_le_normalizer_pPrimeCoreOf 3 M)) (coprime_card_pPrimeCoreOf 3 M)
    refine sSup_le fun Q hQ => ?_
    obtain ⟨hQT, hQ3, hxQ, hQNJ⟩ := hQprops Q hQ
    obtain ⟨-, hQYC⟩ := hQ
    have hQC : Q ≤ C := hQYC.trans inf_le_right
    have hTQ := hα _ hQT hQ3 hxQ
    set U := (Q.subgroupOf C).map π with hUdef
    have hQN : (U.comap π).map C.subtype = Q ⊔ N := by
      rw [hUdef, Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le hQC, ← hNsub,
        Subgroup.map_subgroupOf_eq_of_le (pPrimeCoreOf_le 3 C)]
    have hMQN : M ≤ Subgroup.normalizer ((Q ⊔ N : Subgroup G) : Set G) := by
      intro m hm
      obtain ⟨hmC, hmT⟩ := hMT m hm
      have h1 : (⟨m, hmC⟩ : ↥C) ∈ Subgroup.normalizer ((U.comap π : Subgroup ↥C) : Set ↥C) :=
        Subgroup.le_normalizer_comap π (hTQ hmT)
      rw [← hQN]
      exact Subgroup.le_normalizer_map C.subtype ⟨_, h1, rfl⟩
    have hcop : Nat.Coprime 3 (Nat.card (M ⊓ (Q ⊔ N) : Subgroup G)) := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_
      have h3' := h3.trans (Subgroup.card_dvd_of_le inf_le_right)
      rw [← hQN, Subgroup.card_map_of_injective C.subtype_injective] at h3'
      refine Item148HJ.not_dvd_card_comap π hQ3 ?_ h3'
      rw [QuotientGroup.ker_mk']
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN₀3
    have hQM : Q ≤ pPrimeCoreOf 3 M :=
      (le_inf (le_inf hQYC hQNJ) le_sup_left).trans (le_pPrimeCoreOf inf_le_left
        (Late.le_normalizer_inf Subgroup.le_normalizer hMQN) hcop)
    exact hQM.trans hOM
  set P := inSubgroup perfectResidual Tt with hPdef
  have hPT : P ≤ Tt := Subgroup.map_subtype_le _
  have hPperf : Group.IsPerfect ↥P := Item148HJ.isPerfect_inSubgroup_perfectResidual Tt
  obtain ⟨hPq, hPZ, w₀, hw₀3, hw₀⟩ : IsQuasisimple ↥P ∧ IsPGroup 3 (Subgroup.center ↥P) ∧
      ∃ w₀ : ↥P, w₀ ^ 3 = 1 ∧ w₀ ∉ Subgroup.center ↥P := by
    rcases hP with hP5 | hP𝔍
    · obtain ⟨e⟩ := hP5
      obtain ⟨hq5, hc5, w, hw3, hw1⟩ := Item148HJ.alternatingGroup_five_facts
      have hcP : Subgroup.center ↥P = ⊥ := by
        have hmap := Subgroup.map_center_eq e
        rw [hc5] at hmap
        exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq5, by rw [hcP]; exact
        IsPGroup.of_bot, e.symm w, by rw [← map_pow, hw3, map_one], fun hc => hw1 ?_⟩
      rw [hcP, Subgroup.mem_bot] at hc
      simpa using congrArg e hc
    · let e' : ↥P ≃* ↥𝔍 := MulEquiv.subgroupCongr hP𝔍
      have hcard : Nat.card (Subgroup.center ↥P) = 3 := by
        have h1 := h𝔍tc.1
        rwa [← Subgroup.map_center_eq e', Subgroup.card_map_of_injective e'.injective] at h1
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm h𝔍q,
        IsPGroup.of_card (n := 1) (by rw [hcard, pow_one]), ⟨x, by rw [hP𝔍]; exact hx𝔍⟩,
        Subtype.ext (by simpa using hx3), fun hc => ?_⟩
      obtain ⟨y, hy, hxy⟩ := hxZ
      have hyP : y ∈ P := by rw [hP𝔍]; exact hy
      exact hxy (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hyP⟩).symm)
  have hw₀1 : w₀ ≠ 1 := fun h1 => hw₀ (h1 ▸ Subgroup.one_mem _)
  have hP3 : 3 ∣ Nat.card ↥P := by
    have h := orderOf_dvd_natCard w₀
    rwa [orderOf_eq_prime hw₀3 hw₀1] at h
  set YJ := Y ⊓ J with hYJdef
  have hYJC : YJ ≤ C := inf_le_right.trans hJC
  have hYJYC : YJ ≤ YC := le_inf inf_le_left hYJC
  set YBH := inSubgroup perfectResidual (YJ.subgroupOf C) with hYBHdef
  set YB := inSubgroup perfectResidual YJ with hYBdef
  have hYBYJ : YB ≤ YJ := Subgroup.map_subtype_le _
  have hYBYC : YB ≤ YC := hYBYJ.trans hYJYC
  have hYBC : YB ≤ C := hYBYC.trans inf_le_right
  have hYBmap : YBH.map C.subtype = YB := by
    rw [hYBHdef, Item148HJ.map_inSubgroup_perfectResidual, Subgroup.map_subgroupOf_eq_of_le hYJC]
  have hYBsub : YB.subgroupOf C = YBH := by
    rw [← hYBmap, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
  have hYJT : (YJ.subgroupOf C).map π ≤ Tt :=
    le_inf (Subgroup.map_mono (Subgroup.comap_mono hYJYC))
      (Subgroup.map_mono (Subgroup.comap_mono inf_le_right))
  have hTnorm : Tt ≤ Subgroup.normalizer (((YJ.subgroupOf C).map π : Subgroup _) : Set _) := by
    intro t ht
    obtain ⟨m, hmM, rfl⟩ := hTM t ht
    have hmYJ : (m : G) ∈ Subgroup.normalizer (YJ : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hmM.1.1, hJN hmM.1.2⟩
    exact Subgroup.le_normalizer_map π ⟨m, hconj m hmYJ, rfl⟩
  have hpowJ : ∀ g : ↥C, (g : G) ∈ N ⊔ J → (g : G) ^ Nat.card N₀ ∈ J := by
    intro g hg
    set ρ := QuotientGroup.mk' JH with hρ
    have hg' : g ∈ N₀ ⊔ JH := hsup ▸ Subgroup.mem_subgroupOf.mpr hg
    have hJρ : JH.map ρ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
    have h1 : ρ g ∈ N₀.map ρ := by
      have := Subgroup.mem_map_of_mem ρ hg'
      rwa [Subgroup.map_sup, hJρ, sup_bot_eq] at this
    have h2 : ρ g ^ Nat.card N₀ = 1 := orderOf_dvd_iff_pow_eq_one.mp
      ((Subgroup.orderOf_dvd_natCard _ h1).trans (Subgroup.card_map_dvd N₀ ρ))
    rw [← map_pow, hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    simpa using Subgroup.mem_subgroupOf.mp h2
  set D := ((YJ.subgroupOf C).map π).subgroupOf P with hDdef
  have hDn : D.Normal := Subgroup.normal_subgroupOf_iff_le_normalizer_inf.mpr
    (Late.le_normalizer_inf (hPT.trans hTnorm) Subgroup.le_normalizer)
  have hpow : ∀ w : ↥P, w ^ Nat.card N₀ ∈ D := by
    intro w
    obtain ⟨m, hmM, hmw⟩ := hTM w (hPT w.2)
    rw [hDdef, Subgroup.mem_subgroupOf, Subgroup.coe_pow, ← hmw, ← map_pow]
    refine ⟨m ^ Nat.card N₀, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    rw [Subgroup.coe_pow]
    exact ⟨pow_mem hmM.1.1 _, hpowJ m hmM.2⟩
  have hD : D = ⊤ := Item148HJ.eq_top_of_pow_mem hPq hDn hN₀3.symm hpow hw₀3 hw₀
  have hPle : P ≤ (YJ.subgroupOf C).map π := fun w hw => by
    have : (⟨w, hw⟩ : ↥P) ∈ D := hD ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have hYBP : YBH.map π = P := by
    rw [hYBHdef, Item148HJ.map_inSubgroup_perfectResidual]
    apply le_antisymm
    · exact Item148HJ.le_inSubgroup_perfectResidual ((Subgroup.map_subtype_le _).trans hYJT)
        (Item148HJ.isPerfect_inSubgroup_perfectResidual _)
    · exact Item148HJ.le_inSubgroup_perfectResidual hPle hPperf
  set φ : ↥YB →* (↥C ⧸ N₀) := π.comp (Subgroup.inclusion hYBC) with hφ
  have hφr : φ.range = P := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range, hYBsub, hYBP]
  have hφker : ∀ y : ↥YB, y ∈ φ.ker ↔ (y : G) ∈ N := by
    intro y
    rw [MonoidHom.mem_ker]
    change π (Subgroup.inclusion hYBC y) = 1 ↔ _
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hNsub,
      Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hΘs : Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) Lb) := by
    have := (solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three).1
    exact Group.isSolvable_of_surjective (Lb.subtype.subgroupMap_surjective _)
  have hkers : Group.IsSolvable ↥φ.ker := by
    let f : ↥φ.ker →* ↥(inSubgroup (aschbacherSolvableCore 3) Lb) :=
      (YB.subtype.comp φ.ker.subtype).codRestrict _ fun y =>
        hJNθ _ (hYBYJ y.1.2).2 ((hφker y.1).mp y.2)
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab => ?_
    have hab' := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext hab')
  have hker3 : ¬ 3 ∣ Nat.card ↥φ.ker := by
    intro h3
    have hle : φ.ker.map YB.subtype ≤ N := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hφker y).mp hy
    have h3' : 3 ∣ Nat.card N := by
      refine h3.trans ?_
      rw [← Subgroup.card_map_of_injective YB.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3 h3'
  have hθYB : aschbacherSolvableCore 3 ↥YB = φ.ker :=
    Item148HJ.aschbacherSolvableCore_eq_ker φ (hφr ▸ hPq) (hφr ▸ hPZ) (hφr ▸ hP3) hkers hker3
  let eYB : (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) ≃* ↥P :=
    ((QuotientGroup.quotientMulEquivOfEq hθYB).trans (QuotientGroup.quotientKerEquivRange φ)).trans
      (MulEquiv.subgroupCongr hφr)
  have hYCYJ : YC ≤ Subgroup.normalizer (YJ : Set G) :=
    Late.le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer) (inf_le_right.trans hJN)
  have hYCYB : YC ≤ Subgroup.normalizer (YB : Set G) :=
    hYCYJ.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
      YJ _ (perfect_residual_characterization (G := ↥YJ)).2.1)
  have hYBperf : Group.IsPerfect ↥YB := Item148HJ.isPerfect_inSubgroup_perfectResidual YJ
  have hmem : YB ∈ thetaComponentsIn YC := by
    let e : ↥(YB.subgroupOf YC) ≃* ↥YB := Subgroup.subgroupOfEquivOfLe hYBYC
    refine mem_thetaComponentsIn_iff.mpr ⟨hYBYC, ?_, ?_, ?_⟩
    · exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    · exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hYBYC).mpr hYCYB).isSubnormal
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (quotThetaEquiv e.symm)
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv eYB.symm hPq)
  refine ⟨YB, hmem, ?_, ?_, (hYBYJ.trans (inf_le_right.trans hJlB)).trans le_sup_right⟩
  · rcases hP with hP5 | hP𝔍
    · obtain ⟨e⟩ := hP5
      exact Or.inr ⟨eYB.trans e⟩
    · exact Or.inl (KFacts.KS14.isTripleCover_congr
        (eYB.trans (MulEquiv.subgroupCongr hP𝔍)).symm h𝔍tc)
  ·
    refine sSup_le fun Q hQ => ?_
    obtain ⟨hQT, hQ3, -, -⟩ := hQprops Q hQ
    obtain ⟨-, hQYC⟩ := hQ
    have hQC : Q ≤ C := hQYC.trans inf_le_right
    have hQP := hPU _ hQT hQ3
    have hNYC : N ⊓ YC ≤ pPrimeCoreOf 3 YC :=
      inf_le_pPrimeCoreOf148 (inf_le_right.trans hCN) hN3
    intro q hq
    have hqP : π ⟨q, hQC hq⟩ ∈ YBH.map π := by
      rw [hYBP]
      exact hQP ⟨⟨q, hQC hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    obtain ⟨y, hy, hyq⟩ := hqP
    have hyYB : (y : G) ∈ YB := by
      rw [← hYBmap]
      exact ⟨y, hy, rfl⟩
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← hNsub,
      Subgroup.mem_subgroupOf] at hyq
    have hn : (y : G)⁻¹ * q ∈ N ⊓ YC :=
      Subgroup.mem_inf.mpr ⟨by simpa using hyq, mul_mem (inv_mem (hYBYC hyYB)) (hQYC hq)⟩
    have hq' : q = (y : G) * ((y : G)⁻¹ * q) := by group
    rw [hq']
    exact mul_mem (Subgroup.mem_sup_right hyYB) (Subgroup.mem_sup_left (hNYC hn))

end Main

end CFSG.RankThree.PartTwo.Sec14
