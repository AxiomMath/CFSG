module

public import CFSG.RankThree.PartTwo.J2Residue.ConfigFacts
public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import TauCeti.GroupTheory.Commutator
import TauCeti.GroupTheory.SemidirectProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.Blueprint.NativeSporadic
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_sup_commutator_map_conj_of_isPerfect {L Q : Subgroup G} {q : G}
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hL : Group.IsPerfect L) (hq : q ∈ Q) :
    L ≤ ⁅L, L.map (MulAut.conj q).toMonoidHom⁆ ⊔ Q := by
  haveI : Group.IsPerfect L := hL
  have hex : ∀ b ∈ L, ∃ c ∈ Q, q * b * q⁻¹ = b * c := by
    intro b hb
    refine ⟨b⁻¹ * q * b * q⁻¹, ?_, by group⟩
    have hb' : b⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem (hLQ hb)
    have h1 : b⁻¹ * q * b ∈ Q := by
      simpa using (Subgroup.mem_normalizer_iff.mp hb' q).mp hq
    exact Q.mul_mem h1 (Q.inv_mem hq)
  have hpt : ∀ a ∈ L, ∀ b ∈ L, ⁅a, b⁆ ∈ ⁅L, L.map (MulAut.conj q).toMonoidHom⁆ ⊔ Q := by
    intro a ha b hb
    obtain ⟨c, hcQ, hbc⟩ := hex b hb
    have hmem : ⁅a, b * c⁆ ∈ ⁅L, L.map (MulAut.conj q).toMonoidHom⁆ := by
      refine Subgroup.commutator_mem_commutator ha ?_
      rw [← hbc]
      exact Subgroup.mem_map_of_mem (MulAut.conj q).toMonoidHom hb
    have hacQ : ⁅a, c⁆ ∈ Q := by
      have h : a * c * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ ha) c).mp hcQ
      rw [commutatorElement_def]
      exact Q.mul_mem h (Q.inv_mem hcQ)
    have hQ : b * ⁅a, c⁆ * b⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hLQ hb) _).mp hacQ
    rw [show ⁅a, b⁆ = ⁅a, b * c⁆ * (b * ⁅a, c⁆ * b⁻¹)⁻¹ by
      rw [commutatorElement_mul_right_eq_mul_conj]
      group]
    exact Subgroup.mul_mem_sup hmem (Q.inv_mem hQ)
  have hle : ⁅L, L⁆ ≤ ⁅L, L.map (MulAut.conj q).toMonoidHom⁆ ⊔ Q := by
    rw [Subgroup.commutator_le]
    exact hpt
  rwa [Subgroup.commutator_eq_self] at hle

theorem isPGroup_closure_pair_of_orderOf_eq_three {b d : G}
    (hb : orderOf b = 3) (hd : orderOf d = 3) (hbd : Commute b d) :
    IsPGroup 3 (Subgroup.closure ({b, d} : Set G)) := by
  classical
  set B : Subgroup G := Subgroup.closure ({b, d} : Set G) with hB
  have hB_eq : B = Subgroup.zpowers b ⊔ Subgroup.zpowers d := by
    rw [hB]
    simpa using (Subgroup.finsetSup_zpowers ({b, d} : Finset G)).symm
  have hcent : Subgroup.zpowers d ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    simpa using (hbd.zpow_zpow l 1).eq
  have hnorm : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hb3 : b ^ (3 : ℕ) = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hd3 : d ^ (3 : ℕ) = 1 := by rw [← hd]; exact pow_orderOf_eq_one d
  have hb3z : b ^ (3 : ℤ) = 1 := by simpa using hb3
  have hd3z : d ^ (3 : ℤ) = 1 := by simpa using hd3
  rw [isPGroup_iff_exists_pow_pow_eq_one]
  refine ⟨1, ?_⟩
  rintro ⟨x, hxB⟩
  have hxmem : x ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers d := by
    rw [← hB_eq]; exact hxB
  obtain ⟨y, hy, z, hz, hyz⟩ := (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left hnorm).mp hxmem
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hx : x = b ^ m * d ^ n := hyz
  apply Subtype.ext
  change (x : G) ^ (3 : ℕ) = 1
  rw [hx]
  have hbm3 : (b ^ m) ^ (3 : ℕ) = 1 := by
    have h1 : (b ^ m) ^ (3 : ℕ) = (b ^ m) ^ (3 : ℤ) := (zpow_natCast (b ^ m) 3).symm
    rw [h1, ← zpow_mul, show m * (3 : ℤ) = (3 : ℤ) * m by rw [mul_comm], zpow_mul, hb3z, one_zpow]
  have hdn3 : (d ^ n) ^ (3 : ℕ) = 1 := by
    have h1 : (d ^ n) ^ (3 : ℕ) = (d ^ n) ^ (3 : ℤ) := (zpow_natCast (d ^ n) 3).symm
    rw [h1, ← zpow_mul, show n * (3 : ℤ) = (3 : ℤ) * n by rw [mul_comm], zpow_mul, hd3z, one_zpow]
  have h1 : (b ^ m * d ^ n) ^ (3 : ℕ) = (b ^ m * d ^ n) ^ (3 : ℤ) :=
    (zpow_natCast (b ^ m * d ^ n) 3).symm
  rw [h1, (hbd.zpow_zpow m n).mul_zpow]
  rw [show (b ^ m) ^ (3 : ℤ) = 1 by simpa using hbm3,
    show (d ^ n) ^ (3 : ℤ) = 1 by simpa using hdn3, mul_one]

omit [Finite G] in
private theorem closure_pair_eq_closure_of_mem_of_notMem_zpowers {b d e : G}
    (hb : orderOf b = 3) (hbd : Commute b d) (he : e ∈ Subgroup.closure ({b, d} : Set G))
    (hed : e ∉ Subgroup.zpowers d) :
    Subgroup.closure ({b, d} : Set G) = Subgroup.closure ({e, d} : Set G) := by
  classical
  set B : Subgroup G := Subgroup.closure ({b, d} : Set G) with hB
  have hB_eq : B = Subgroup.zpowers b ⊔ Subgroup.zpowers d := by
    rw [hB]
    simpa using (Subgroup.finsetSup_zpowers ({b, d} : Finset G)).symm
  have hcent : Subgroup.zpowers d ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    simpa using (hbd.zpow_zpow l 1).eq
  have hnorm : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hmem : e ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers d := by
    rw [← hB_eq]; exact he
  obtain ⟨x, hx, y, hy, hxy⟩ := (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left hnorm).mp hmem
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have heq : b ^ m * d ^ n = e := hxy.symm
  have hb3 : b ^ (3 : ℕ) = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hb3z : b ^ (3 : ℤ) = 1 := by simpa using hb3
  have h3m : ¬ (3 : ℤ) ∣ m := by
    intro hdiv
    obtain ⟨k, hk⟩ := hdiv
    have hbm : b ^ m = 1 := by
      rw [hk, zpow_mul, hb3z]
      simp
    apply hed
    rw [← heq, hbm, one_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers d) n
  have hgcd : Int.gcd m (orderOf b : ℤ) = Int.gcd (1 : ℤ) (orderOf b : ℤ) := by
    rw [hb]
    norm_num
    rw [Int.gcd_eq_natAbs_gcd_natAbs]
    have h3 : ¬ 3 ∣ m.natAbs := by
      intro h
      exact h3m ((Int.ofNat_dvd_left (n := 3) (z := m)).mpr h)
    have hcop : Nat.Coprime 3 m.natAbs := (Nat.prime_three.coprime_iff_not_dvd).mpr h3
    have h := hcop.gcd_eq_one
    rw [Nat.gcd_comm]
    exact h
  have hzp : Subgroup.zpowers (b ^ m) = Subgroup.zpowers b := by
    have := (Subgroup.zpowers_eq_zpowers_iff' b m 1).mpr hgcd
    simpa using this
  have hbm_eq : b ^ m = e * (d ^ n)⁻¹ := by
    rw [← heq]; group
  have hbm_mem : b ^ m ∈ Subgroup.closure ({e, d} : Set G) := by
    rw [hbm_eq]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) n))
  have hb_in : b ∈ Subgroup.zpowers (b ^ m) := by
    rw [hzp]
    exact Subgroup.mem_zpowers b
  have hb_mem : b ∈ Subgroup.closure ({e, d} : Set G) :=
    (Subgroup.zpowers_le.mpr hbm_mem) hb_in
  apply le_antisymm
  · rw [hB, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hb_mem
    · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact he
    · exact Subgroup.subset_closure (by simp)

omit [Finite G] in
private theorem false_of_commutator_le_theta {LB LBt T : Subgroup G} {d : G}
    (hLBnormT : LB ≤ Subgroup.normalizer (T : Set G))
    (hLBperf : Group.IsPerfect LB)
    (hLBt_solv : Group.IsSolvable LBt)
    (hLBt_le : LBt ≤ LB ⊔ T)
    (hLBle : LB ≤ LBt ⊔ T)
    (hd : d ∈ LB) (hdT : d ∉ T) : False := by
  set K : Subgroup G := LB ⊔ T with hK
  have hLBK : LB ≤ K := le_sup_left
  have hTK : T ≤ K := le_sup_right
  have hLBtK : LBt ≤ K := hLBt_le
  have hTnormK : (T.subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hLBnormT
  letI : (T.subgroupOf K).Normal := hTnormK
  let π := QuotientGroup.mk' (T.subgroupOf K)
  have hLBperfK : Group.IsPerfect (LB.subgroupOf K) := by
    haveI : Group.IsPerfect LB := hLBperf
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hLBK).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLBK).symm.surjective
  have hperfImage : Group.IsPerfect ((LB.subgroupOf K).map π) :=
    Group.IsPerfect.map π
  have hLBt_solvK : Group.IsSolvable (LBt.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hLBtK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLBtK).injective
  have hsolvImage : Group.IsSolvable ((LBt.subgroupOf K).map π) :=
    Group.isSolvable_of_surjective (π.subgroupMap_surjective (LBt.subgroupOf K))
  have hleImage : (LB.subgroupOf K).map π ≤ (LBt.subgroupOf K).map π := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hw
    have hxG : (x : G) ∈ LBt ⊔ T := hLBle (Subgroup.mem_subgroupOf.mp hx)
    have hxK : (⟨x, hLBK (Subgroup.mem_subgroupOf.mp hx)⟩ : K) ∈
        (LBt ⊔ T).subgroupOf K := Subgroup.mem_subgroupOf.mpr hxG
    rw [Subgroup.subgroupOf_sup hLBtK hTK] at hxK
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hxK
    refine ⟨y, hy, ?_⟩
    have hxeq : (⟨x, hLBK (Subgroup.mem_subgroupOf.mp hx)⟩ : K) = y * z := hyz.symm
    have hzker : π z = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hz
    rw [show π (⟨x, hLBK (Subgroup.mem_subgroupOf.mp hx)⟩ : K) = π y by
      rw [hxeq, map_mul, hzker, mul_one]]
  have hsolvLBImage : Group.IsSolvable ((LB.subgroupOf K).map π) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hleImage)
  have hdK : (⟨d, hLBK hd⟩ : K) ∈ LB.subgroupOf K := Subgroup.mem_subgroupOf.mpr hd
  have hdImage_ne : π ⟨d, hLBK hd⟩ ≠ 1 := by
    intro h
    apply hdT
    have := (QuotientGroup.eq_one_iff (N := T.subgroupOf K) _).mp h
    exact Subgroup.mem_subgroupOf.mp this
  have hne : (LB.subgroupOf K).map π ≠ ⊥ := by
    intro hbot
    have hmem : π ⟨d, hLBK hd⟩ ∈ (LB.subgroupOf K).map π :=
      Subgroup.mem_map_of_mem π hdK
    rw [hbot] at hmem
    exact hdImage_ne (Subgroup.mem_bot.mp hmem)
  haveI : Nontrivial ((LB.subgroupOf K).map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact Group.IsPerfect.not_isSolvable _ hsolvLBImage

private theorem map_conj_mem_thetaComponentsAt {L : Subgroup G} {b t : G}
    (hL : L ∈ thetaComponentsAt 3 b)
    (ht : t ∈ Subgroup.centralizer ({b} : Set G)) :
    L.map (MulAut.conj t).toMonoidHom ∈ thetaComponentsAt 3 b := by
  set C := Subgroup.centralizer ({b} : Set G)
  rcases hL with ⟨L₀, hL₀, rfl⟩
  let σ : C ≃* C := C.normalizerMonoidHom ⟨t, C.le_normalizer ht⟩
  refine ⟨L₀.map σ, map_mulEquiv_mem_thetaComponents Nat.prime_three σ hL₀, ?_⟩
  change Subgroup.map C.subtype (Subgroup.map σ.toMonoidHom L₀) =
    Subgroup.map (MulAut.conj t).toMonoidHom (Subgroup.map C.subtype L₀)
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] in
private theorem commutator_mem_theta_of_ne {H : Type} [Group H] [Finite H]
    {L₁ L₂ : Subgroup H} (h₁ : L₁ ∈ thetaComponents 3 H)
    (h₂ : L₂ ∈ thetaComponents 3 H) (hne : L₁ ≠ L₂) :
    ⁅L₁, L₂⁆ ≤ aschbacherSolvableCore 3 H := by
  set N := aschbacherSolvableCore 3 H
  set π := QuotientGroup.mk' N
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) Nat.prime_three
  have hK₁ := isComponent_map_of_mem_thetaComponents Nat.prime_three h₁
  have hK₂ := isComponent_map_of_mem_thetaComponents Nat.prime_three h₂
  have hKne : L₁.map π ≠ L₂.map π := fun h => hne (hbij.injOn h₁ h₂ h)
  have hcomm := (LocalCores.distinct_components_commute hK₁ hK₂).resolve_left hKne
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 : ⁅π x, π y⁆ ∈ ⁅L₁.map π, L₂.map π⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem π hx)
      (Subgroup.mem_map_of_mem π hy)
  rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h1
  exact h1

private theorem commutator_le_theta_of_ne {L₁ L₂ : Subgroup G} {b : G}
    (h₁ : L₁ ∈ thetaComponentsAt 3 b) (h₂ : L₂ ∈ thetaComponentsAt 3 b) (hne : L₁ ≠ L₂) :
    ⁅L₁, L₂⁆ ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) := by
  set H := Subgroup.centralizer ({b} : Set G)
  rcases h₁ with ⟨L₁₀, hL₁₀, hL₁_eq⟩
  rcases h₂ with ⟨L₂₀, hL₂₀, hL₂_eq⟩
  have hne' : L₁₀ ≠ L₂₀ := fun h => hne (by rw [← hL₁_eq, ← hL₂_eq, h])
  have hcomm : ⁅L₁₀, L₂₀⁆ ≤ aschbacherSolvableCore 3 H :=
    commutator_mem_theta_of_ne hL₁₀ hL₂₀ hne'
  rw [← hL₁_eq, ← hL₂_eq, ← Subgroup.map_commutator]
  exact Subgroup.map_mono hcomm

private theorem exists_fixed_of_coprime_action {F₁ F₂ B : Subgroup G}
    (hBF₁ : B ≤ Subgroup.normalizer (F₁ : Set G))
    (hBF₂ : B ≤ Subgroup.normalizer (F₂ : Set G))
    (hF₁N : F₁ ≤ Subgroup.normalizer (F₂ : Set G))
    (hF₂ltF₁ : F₂ < F₁)
    (hcop : Nat.Coprime (Nat.card B) (Nat.card (F₂.subgroupOf F₁)))
    (hF₂solv : Group.IsSolvable (F₂.subgroupOf F₁))
    (htriv : ⁅F₁, B⁆ ≤ F₂) :
    ∀ f : F₁, ∃ c : F₁, (∀ b : B, (b : G) * (c : G) * (b : G)⁻¹ = (c : G)) ∧
      c⁻¹ * f ∈ F₂.subgroupOf F₁ := by
  letI : Subgroup.Normalizes B F₁ := ⟨hBF₁⟩
  letI act : MulDistribMulAction B F₁ := Subgroup.conjMulDistribMulActionOfLeNormalizer B F₁ hBF₁
  have hF₂norm : (F₂.subgroupOf F₁).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hF₁N (g : F₁).2) (n : G)).mp hn
  letI : (F₂.subgroupOf F₁).Normal := hF₂norm
  have hF₂inv : CFSG.IsInvariant B F₁ (F₂.subgroupOf F₁) := by
    refine ⟨fun b x => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change (x : G) ∈ F₂ ↔ ((b : G) * (x : G) * (b : G)⁻¹) ∈ F₂
    exact Subgroup.mem_normalizer_iff.mp (hBF₂ b.2) (x : G)
  intro f
  have hside : ∀ b : B, (f : F₁)⁻¹ * (b • f) ∈ F₂.subgroupOf F₁ := by
    intro b
    have hmem : ⁅((f : F₁)⁻¹ : G), (b : G)⁆ ∈ ⁅F₁, B⁆ :=
      Subgroup.commutator_mem_commutator (F₁.inv_mem f.2) b.2
    have hmemF₂ : ⁅((f : F₁)⁻¹ : G), (b : G)⁆ ∈ F₂ := htriv hmem
    have hsmul : (((b : B) • f : F₁) : G) = (b : G) * (f : G) * (b : G)⁻¹ :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe B F₁ b f
    rw [Subgroup.mem_subgroupOf]
    change ((f : G)⁻¹ * (((b : B) • f : F₁) : G)) ∈ F₂
    rw [hsmul]
    have : (f : G)⁻¹ * ((b : G) * (f : G) * (b : G)⁻¹) = ⁅((f : F₁)⁻¹ : G), (b : G)⁆ := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact hmemF₂
  obtain ⟨c, hc, hcf⟩ :=
    CFSG.SolvableHall.exists_fixed_of_coset_fixed (F₂.subgroupOf F₁) hF₂inv hF₂solv hcop f hside
  refine ⟨c, ?_, hcf⟩
  intro b
  have hfix : b • c = c := (MulAction.mem_fixedPoints.mp hc) b
  have hsmul : (((b : B) • c : F₁) : G) = (b : G) * (c : G) * (b : G)⁻¹ :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe B F₁ b c
  rw [← hsmul, hfix]

private theorem T_le_normalizer_L {L LB Θ : Subgroup G} {b d : G}
    (hJ : J2Config L d LB) (hLb : L ∈ thetaComponentsAt 3 b)
    (hΘ3 : ¬ 3 ∣ Nat.card Θ) {Y : Subgroup G}
    (hLBY : LB ≤ Y)
    (hYB : Y ≤ Subgroup.centralizer (Subgroup.closure ({b, d} : Set G) : Set G))
    (hYΘ : Y ≤ Subgroup.normalizer (Θ : Set G)) :
    Θ ⊓ Subgroup.centralizer (Subgroup.closure ({b, d} : Set G) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  set B : Subgroup G := Subgroup.closure ({b, d} : Set G) with hB
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  set T : Subgroup G := Θ ⊓ Subgroup.centralizer (B : Set G) with hT
  change T ≤ Subgroup.normalizer (L : Set G)
  have hTleΘ : T ≤ Θ := inf_le_left
  have hLBnormΘ : LB ≤ Subgroup.normalizer (Θ : Set G) := hLBY.trans hYΘ
  have hLBnormCB : LB ≤ Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) :=
    hLBY.trans (hYB.trans Subgroup.le_normalizer)
  have hLBnormT : LB ≤ Subgroup.normalizer (T : Set G) := by
    intro l hl
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hLBnormΘ hl, hLBnormCB hl⟩
  have hT3 : ¬ 3 ∣ Nat.card T := fun h => hΘ3 (h.trans (Subgroup.card_dvd_of_le hTleΘ))
  have hdT : d ∉ T := by
    intro hdTmem
    have hdLB : d ∈ LB := J2Config.mem_lB hJ
    have hdO₂ : d ∈ CFSG.Open.pCoreOf 2 LB :=
      J2Config.inf_le_pCoreOf hJ hLBnormT hT3 (Subgroup.mem_inf.mpr ⟨hdTmem, hdLB⟩)
    have hdvd : 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 LB) := by
      have := Subgroup.orderOf_dvd_natCard (CFSG.Open.pCoreOf 2 LB) hdO₂
      rwa [hJ.orderOf_d] at this
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) LB) Nat.prime_three (by norm_num) hdvd
  intro t ht
  have htΘ : t ∈ Θ := ht.1
  have htCB : t ∈ Subgroup.centralizer (B : Set G) := ht.2
  have htb : t * b = b * t := by
    have h := Subgroup.mem_centralizer_iff.mp htCB b (Subgroup.subset_closure (by simp))
    exact h.symm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hne' : L ≠ L.map (MulAut.conj t).toMonoidHom := fun h => hne h.symm
  have hLt_mem : L.map (MulAut.conj t).toMonoidHom ∈ thetaComponentsAt 3 b :=
    map_conj_mem_thetaComponentsAt hLb (Subgroup.mem_centralizer_singleton_iff.mpr htb)
  have hcommθ : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) C :=
    commutator_le_theta_of_ne hLb hLt_mem hne'
  have hLBleL : LB ≤ L := (J2Config.lB_le hJ).trans inf_le_left
  have hLBcommθ : ⁅LB, LB.map (MulAut.conj t).toMonoidHom⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) C :=
    (Subgroup.commutator_mono hLBleL
      (Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hLBleL)).trans hcommθ
  have hLBcomm_solv : Group.IsSolvable (⁅LB, LB.map (MulAut.conj t).toMonoidHom⁆ : Subgroup G) := by
    have hθsolv : Group.IsSolvable (aschbacherSolvableCore 3 C) :=
      (solvable_prime_complement_core_characterization Nat.prime_three).1
    have hsolv : Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) C) :=
      Group.isSolvable_of_surjective
        (MonoidHom.subgroupMap_surjective C.subtype (aschbacherSolvableCore 3 C))
    haveI : Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) C) := hsolv
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLBcommθ)
  have hLBt_le : LB.map (MulAut.conj t).toMonoidHom ≤ LB ⊔ T := by
    rintro x ⟨l, hl, rfl⟩
    have hlt : l * t * l⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hLBnormT hl) t).mp ht
    have htinv : l * t⁻¹ * l⁻¹ ∈ T := by
      have := T.inv_mem hlt
      simpa [mul_assoc] using this
    have hx : t * l * t⁻¹ = t * (l * t⁻¹ * l⁻¹) * l := by group
    change t * l * t⁻¹ ∈ LB ⊔ T
    rw [hx, sup_comm]
    exact Subgroup.mul_mem_sup (T.mul_mem ht htinv) hl
  have hcomm_le : ⁅LB, LB.map (MulAut.conj t).toMonoidHom⁆ ≤ LB ⊔ T :=
    (Subgroup.commutator_mono le_sup_left hLBt_le).trans (Subgroup.commutator_le_self (LB ⊔ T))
  have hLBle : LB ≤ ⁅LB, LB.map (MulAut.conj t).toMonoidHom⁆ ⊔ T :=
    le_sup_commutator_map_conj_of_isPerfect hLBnormT (J2Config.isPerfect_lB hJ) ht
  exact false_of_commutator_le_theta hLBnormT (J2Config.isPerfect_lB hJ) hLBcomm_solv
    hcomm_le hLBle (J2Config.mem_lB hJ) hdT

theorem exists_commutator_not_mem_of_alpha {L LB Θ : Subgroup G} {b d e : G}
    (hJ : J2Config L d LB) (hLb : L ∈ thetaComponentsAt 3 b) (hb : orderOf b = 3)
    (hbd : Commute b d) (he : e ∈ Subgroup.closure {b, d}) (hed : e ∉ Subgroup.zpowers d)
    (hΘ3 : ¬ 3 ∣ Nat.card Θ) (hΘe : Θ ≤ Subgroup.centralizer ({e} : Set G)) {Y : Subgroup G}
    (hLBY : LB ≤ Y) (hBY : Subgroup.closure {b, d} ≤ Y)
    (hYB : Y ≤ Subgroup.centralizer (Subgroup.closure {b, d} : Set G))
    (hYΘ : Y ≤ Subgroup.normalizer (Θ : Set G)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    {F₁ F₂ : Subgroup G} (hF₁ : F₁ ≤ CFSG.Open.pCoreOf r Θ)
    (hch : CFSG.ABGLocalTools.IsChiefFactorUnder r Y F₁ F₂)
    (hU : ∃ u ∈ CFSG.Open.pCoreOf 2 LB, ∃ f ∈ F₁, ⁅f, u⁆ ∉ F₂) :
    ∃ f ∈ F₁, ⁅f, d⁆ ∉ F₂ := by
  by_contra hcon
  push Not at hcon
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  let B : Subgroup G := Subgroup.closure ({b, d} : Set G)
  let T : Subgroup G := Θ ⊓ Subgroup.centralizer (B : Set G)
  have hB_eq : B = Subgroup.closure ({e, d} : Set G) :=
    closure_pair_eq_closure_of_mem_of_notMem_zpowers hb hbd he hed
  have hB3 : IsPGroup 3 B :=
    isPGroup_closure_pair_of_orderOf_eq_three hb hJ.orderOf_d hbd
  have hF₁_le_Θ : F₁ ≤ Θ := hF₁.trans (CFSG.LieType.BorelTits.pCoreOf_le r Θ)
  have hF₁r : IsPGroup r F₁ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := r) Θ).to_le hF₁
  have hF₂r : IsPGroup r F₂ := hF₁r.to_le hch.1.le
  have hF₁3 : ¬ 3 ∣ Nat.card F₁ :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hF₁r Nat.prime_three (by omega)
  have hF₂normSub : (F₂.subgroupOf F₁).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hch.2.2.2.1 (g : G) g.2 (n : G) hn
  have hF₁N : F₁ ≤ Subgroup.normalizer (F₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hch.1.le).mp hF₂normSub
  have hBF₁ : B ≤ Subgroup.normalizer (F₁ : Set G) := hBY.trans hch.2.1
  have hBF₂ : B ≤ Subgroup.normalizer (F₂ : Set G) := hBY.trans hch.2.2.1
  have hLBnormF₁ : LB ≤ Subgroup.normalizer (F₁ : Set G) := hLBY.trans hch.2.1
  have he_centralizes : ∀ f ∈ F₁, ⁅f, e⁆ = 1 := by
    intro f hf
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hΘe (hF₁_le_Θ hf)))
  have htriv : ⁅F₁, B⁆ ≤ F₂ := by
    have h := TauCeti.commutator_closure_closure_le (X := (F₁ : Set G))
      (Y := ({e, d} : Set G)) (N := F₂) ?_ ?_ ?_
    · simpa [Subgroup.closure_eq, ← hB_eq] using h
    · simpa [Subgroup.closure_eq] using hF₁N
    · simpa [hB_eq] using hBF₂
    · intro x hx y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · rw [he_centralizes x hx]; exact F₂.one_mem
      · exact hcon x hx
  have hF₂rSub : IsPGroup r (F₂.subgroupOf F₁) :=
    hF₂r.of_equiv (Subgroup.subgroupOfEquivOfLe hch.1.le).symm
  have hF₂solv : Group.IsSolvable (F₂.subgroupOf F₁) := by
    haveI : Group.IsNilpotent (F₂.subgroupOf F₁) := hF₂rSub.isNilpotent
    exact IsNilpotent.to_isSolvable
  have hcop : Nat.Coprime (Nat.card B) (Nat.card (F₂.subgroupOf F₁)) := by
    have hcop' : Nat.Coprime (Nat.card B) (Nat.card F₂) :=
      IsPGroup.coprime_card_of_ne 3 r (by omega) B F₂ hB3 hF₂r
    rw [CFSG.natCard_subgroupOf_eq F₂ F₁ hch.1.le]
    exact hcop'
  have hlift := exists_fixed_of_coprime_action hBF₁ hBF₂ hF₁N hch.1 hcop hF₂solv htriv
  have hT_le_Cd : T ≤ Subgroup.centralizer ({d} : Set G) := by
    intro t ht
    have htd : t * d = d * t := by
      have h := Subgroup.mem_centralizer_iff.mp ht.2 d (Subgroup.subset_closure (by simp))
      exact h.symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr htd
  have hTnormL : T ≤ Subgroup.normalizer (L : Set G) :=
    T_le_normalizer_L hJ hLb hΘ3 hLBY hYB hYΘ
  have hTnormLB : T ≤ Subgroup.normalizer (LB : Set G) := by
    rw [J2Config.lB_eq hJ]
    have h : T ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({d} : Set G)) : Set G) := by
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hTnormL hx, (hT_le_Cd.trans Subgroup.le_normalizer) hx⟩
    exact h.trans
      (CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map
        (L ⊓ Subgroup.centralizer ({d} : Set G)))
  have hcentralizes : ∀ c ∈ F₁ ⊓ Subgroup.centralizer (B : Set G), ∀ l ∈ LB,
      (c : G) * l = l * c := by
    intro c hc l hl
    have hcF₁ : (c : G) ∈ F₁ := hc.1
    have hcCB : (c : G) ∈ Subgroup.centralizer (B : Set G) := hc.2
    have hcT : (c : G) ∈ T := Subgroup.mem_inf.mpr ⟨hF₁_le_Θ hcF₁, hcCB⟩
    have hcNormLB : (c : G) ∈ Subgroup.normalizer (LB : Set G) := hTnormLB hcT
    have hcl_LB : ⁅c, l⁆ ∈ LB := by
      have hconj : c * l * c⁻¹ ∈ LB := (Subgroup.mem_normalizer_iff.mp hcNormLB l).mp hl
      rw [commutatorElement_def]
      exact LB.mul_mem hconj (LB.inv_mem hl)
    have hcl_F₁ : ⁅c, l⁆ ∈ F₁ := by
      have hlN : l ∈ Subgroup.normalizer (F₁ : Set G) := hch.2.1 (hLBY hl)
      have hconj : l * c⁻¹ * l⁻¹ ∈ F₁ :=
        (Subgroup.mem_normalizer_iff.mp hlN c⁻¹).mp (F₁.inv_mem hcF₁)
      rw [commutatorElement_def]
      rw [show c * l * c⁻¹ * l⁻¹ = c * (l * c⁻¹ * l⁻¹) by group]
      exact F₁.mul_mem hcF₁ hconj
    have hcl_inf : ⁅c, l⁆ ∈ F₁ ⊓ LB := Subgroup.mem_inf.mpr ⟨hcl_F₁, hcl_LB⟩
    have hcl_O₂ : ⁅c, l⁆ ∈ CFSG.Open.pCoreOf 2 LB :=
      J2Config.inf_le_pCoreOf hJ hLBnormF₁ hF₁3 hcl_inf
    have hone : ⁅c, l⁆ = 1 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hdisj : Disjoint (CFSG.Open.pCoreOf 2 LB) F₁ :=
        IsPGroup.disjoint_of_ne 2 r (by omega) _ _ (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) LB) hF₁r
      have hxbot : ⁅c, l⁆ ∈ CFSG.Open.pCoreOf 2 LB ⊓ F₁ :=
        Subgroup.mem_inf.mpr ⟨hcl_O₂, hcl_F₁⟩
      rw [hdisj.eq_bot] at hxbot
      exact Subgroup.mem_bot.mp hxbot
    exact commutatorElement_eq_one_iff_mul_comm.mp hone
  obtain ⟨u, huO₂, f, hfF₁, hfu⟩ := hU
  have huLB : u ∈ LB := (CFSG.LieType.BorelTits.pCoreOf_le 2 LB) huO₂
  obtain ⟨c, hc_fixed, hc_coset⟩ := hlift ⟨f, hfF₁⟩
  have hcF₁ : (c : G) ∈ F₁ := c.2
  have hcCB : (c : G) ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxeq : x * (c : G) * x⁻¹ = (c : G) := hc_fixed ⟨x, hx⟩
    calc x * (c : G) = (x * (c : G) * x⁻¹) * x := by group
      _ = (c : G) * x := by rw [hxeq]
  have hcu : (c : G) * u = u * (c : G) := hcentralizes c ⟨hcF₁, hcCB⟩ u huLB
  have hf₂ : (c : G)⁻¹ * (f : G) ∈ F₂ := by
    have := Subgroup.mem_subgroupOf.mp hc_coset
    simpa using this
  have huN : u ∈ Subgroup.normalizer (F₂ : Set G) := hch.2.2.1 (hLBY huLB)
  have huf₂ : ⁅u, (c : G)⁻¹ * (f : G)⁆ ∈ F₂ := by
    have hconj : u * ((c : G)⁻¹ * (f : G)) * u⁻¹ ∈ F₂ :=
      (Subgroup.mem_normalizer_iff.mp huN ((c : G)⁻¹ * (f : G))).mp hf₂
    rw [commutatorElement_def]
    exact F₂.mul_mem hconj (F₂.inv_mem hf₂)
  have hf₂_comm : ⁅(c : G)⁻¹ * (f : G), u⁆ ∈ F₂ := by
    have h : ⁅(c : G)⁻¹ * (f : G), u⁆ = ⁅u, (c : G)⁻¹ * (f : G)⁆⁻¹ := by
      rw [commutatorElement_inv]
    rw [h]
    exact F₂.inv_mem huf₂
  have hcu_one : ⁅(c : G), u⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcu
  have hfuF₂ : ⁅(f : G), u⁆ ∈ F₂ := by
    have hf_eq : (f : G) = (c : G) * ((c : G)⁻¹ * (f : G)) := by group
    rw [hf_eq, commutatorElement_mul_left_eq_conj_mul]
    have h1 : (c : G) * ⁅(c : G)⁻¹ * (f : G), u⁆ * (c : G)⁻¹ ∈ F₂ :=
      (Subgroup.mem_normalizer_iff.mp (hF₁N hcF₁) _).mp hf₂_comm
    rw [hcu_one, mul_one]
    exact h1
  exact hfu hfuF₂

end CFSG.RankThree.PartTwo.J2Residue
