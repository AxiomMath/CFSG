module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S3KBase
import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofTools
import CFSG.RankThree.PartTwo.Sec18.Item182
public import CFSG.RankThree.PartTwo.Sec8.Hering611SImg2
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Xsub (K V : Subgroup G) : Subgroup G :=
  inSubgroup perfectResidual (K ⊓ Subgroup.normalizer (V : Set G))

private theorem mem_of_pow_coprime {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal]
    {a b : Γ} (hab : a⁻¹ * b ∈ N) {m k : ℕ} (hm : a ^ m ∈ N) (hk : b ^ k ∈ N)
    (hmk : Nat.Coprime m k) : b ∈ N := by
  have h1 : (QuotientGroup.mk a : Γ ⧸ N) = QuotientGroup.mk b := QuotientGroup.eq.mpr hab
  have hm' : (QuotientGroup.mk b : Γ ⧸ N) ^ m = 1 := by
    rw [← h1, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hm
  have hk' : (QuotientGroup.mk b : Γ ⧸ N) ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have hg : (QuotientGroup.mk b : Γ ⧸ N) = 1 := (pow_eq_one_iff_of_coprime hmk).mp ⟨hm', hk'⟩
  exact (QuotientGroup.eq_one_iff b).mp hg

theorem Xsub_perfect (K V : Subgroup G) : Group.IsPerfect (Xsub K V) := by
  obtain ⟨-, -, hperf, -⟩ :=
    CFSG.perfect_residual_characterization (G := ↥(K ⊓ Subgroup.normalizer (V : Set G)))
  exact Group.IsPerfect.map (K ⊓ Subgroup.normalizer (V : Set G)).subtype

theorem Xsub_le_K (K V : Subgroup G) : Xsub K V ≤ K :=
  (Subgroup.map_subtype_le _).trans inf_le_left

theorem Xsub_le_normalizer (K V : Subgroup G) : Xsub K V ≤ Subgroup.normalizer (V : Set G) :=
  (Subgroup.map_subtype_le _).trans inf_le_right

theorem imageSub_normalizer {K V : Subgroup G}
    (hθ : ¬ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) (hVK : V ≤ K)
    (hV2 : IsPGroup 2 V) :
    imageSub K (K ⊓ Subgroup.normalizer (V : Set G)) =
      Subgroup.normalizer (imageSub K V : Set (K ⧸ aschbacherSolvableCore 3 K)) := by
  apply le_antisymm
  · rintro t ht
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp ht
    have hkN : (k : G) ∈ Subgroup.normalizer (V : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hk)).2
    apply mem_normalizer_of_conj_mem
    rintro y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
    have hvV : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
    have hmem : ((k * v * k⁻¹ : K) : G) ∈ V := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp hkN (v : G)).mp hvV
    have heq : QuotientGroup.mk' (aschbacherSolvableCore 3 K) k *
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) v *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k)⁻¹ =
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) (k * v * k⁻¹) := by
      simp only [map_mul, map_inv]
    rw [heq]
    exact mk_mem_imageSub hmem
  · intro wb hwb
    obtain ⟨w, hwN, hwπ⟩ := exists_lift_normalizer_gen hVK hV2 hθ hwb
    rw [← hwπ]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨w.2, hwN⟩))

theorem imageSub_Xsub {K V : Subgroup G}
    (hθ : ¬ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) (hVK : V ≤ K)
    (hV2 : IsPGroup 2 V) :
    imageSub K (Xsub K V) =
      inSubgroup perfectResidual
        (Subgroup.normalizer (imageSub K V : Set (K ⧸ aschbacherSolvableCore 3 K))) := by
  have h1 : imageSub K (Xsub K V) =
      inSubgroup perfectResidual (imageSub K (K ⊓ Subgroup.normalizer (V : Set G))) :=
    CFSG.RankThree.PartTwo.Sec15.Proof15Res7.map_inSubgroup_perfectResidual_subgroupOf
      inf_le_left (QuotientGroup.mk' (aschbacherSolvableCore 3 K))
  rw [h1, imageSub_normalizer hθ hVK hV2]

theorem mem_Xsub_of_mk_mem {p : ℕ} [Fact p.Prime] {K V : Subgroup G}
    (hθp : ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) {x : G} (hxK : x ∈ K)
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) (hxp : ∃ n : ℕ, x ^ (p ^ n) = 1)
    (hmem : QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨x, hxK⟩ ∈ imageSub K (Xsub K V)) :
    x ∈ Xsub K V := by
  obtain ⟨n, hn⟩ := hxp
  have hXH : Xsub K V ≤ K ⊓ Subgroup.normalizer (V : Set G) := Subgroup.map_subtype_le _
  have hxH : x ∈ K ⊓ Subgroup.normalizer (V : Set G) := Subgroup.mem_inf.mpr ⟨hxK, hxN⟩
  have hXn : ((Xsub K V).subgroupOf (K ⊓ Subgroup.normalizer (V : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr
      (CFSG.RankThree.PartTwo.Sec18.le_normalizer_inSubgroup_perfectResidual _)
  obtain ⟨y, hy, hyπ⟩ := Subgroup.mem_map.mp hmem
  have hyX : (y : G) ∈ Xsub K V := Subgroup.mem_subgroupOf.mp hy
  have hyH : (y : G) ∈ K ⊓ Subgroup.normalizer (V : Set G) := hXH hyX
  have hwπ : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (y⁻¹ * ⟨x, hxK⟩) = 1 := by
    rw [map_mul, map_inv, hyπ, inv_mul_cancel]
  have hwθ : ((y⁻¹ * ⟨x, hxK⟩ : K) : G) ∈ inSubgroup (aschbacherSolvableCore 3) K := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hwπ
    exact Subgroup.mem_map.mpr ⟨_, hwπ, rfl⟩
  have hwcoe : ((y⁻¹ * ⟨x, hxK⟩ : K) : G) = (y : G)⁻¹ * x := by simp
  have hwH : ((y⁻¹ * ⟨x, hxK⟩ : K) : G) ∈ K ⊓ Subgroup.normalizer (V : Set G) := by
    rw [hwcoe]
    exact (K ⊓ Subgroup.normalizer (V : Set G)).mul_mem
      ((K ⊓ Subgroup.normalizer (V : Set G)).inv_mem hyH) hxH
  have hwpow : ((y⁻¹ * ⟨x, hxK⟩ : K) : G) ^ Nat.card (inSubgroup (aschbacherSolvableCore 3) K)
      = 1 := by
    have h1 := orderOf_dvd_iff_pow_eq_one.mp
      (orderOf_dvd_natCard (⟨_, hwθ⟩ : inSubgroup (aschbacherSolvableCore 3) K))
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_pow] at h2
    exact h2
  have hcop : Nat.Coprime (p ^ n) (Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hθp)
  obtain ⟨a, ha⟩ : ∃ a : ↥(K ⊓ Subgroup.normalizer (V : Set G)), (a : G) = x :=
    ⟨⟨x, hxH⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ↥(K ⊓ Subgroup.normalizer (V : Set G)),
      (b : G) = ((y⁻¹ * ⟨x, hxK⟩ : K) : G) := ⟨⟨_, hwH⟩, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ↥(K ⊓ Subgroup.normalizer (V : Set G)), (c : G) = (y : G)⁻¹ :=
    ⟨⟨(y : G)⁻¹, (K ⊓ Subgroup.normalizer (V : Set G)).inv_mem hyH⟩, rfl⟩
  have hcX : c ∈ (Xsub K V).subgroupOf (K ⊓ Subgroup.normalizer (V : Set G)) :=
    Subgroup.mem_subgroupOf.mpr (by rw [hc]; exact (Xsub K V).inv_mem hyX)
  have hcb : c * a = b := Subtype.ext (by rw [Subgroup.coe_mul, ha, hc, hb, hwcoe])
  have hab : a⁻¹ * b ∈ (Xsub K V).subgroupOf (K ⊓ Subgroup.normalizer (V : Set G)) := by
    rw [← hcb]
    have h2 := hXn.conj_mem c hcX a⁻¹
    simpa [mul_assoc] using h2
  have hm : a ^ (p ^ n) ∈ (Xsub K V).subgroupOf (K ⊓ Subgroup.normalizer (V : Set G)) := by
    have h3 : a ^ (p ^ n) = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ha]; simpa using hn)
    rw [h3]
    exact one_mem _
  have hk : b ^ Nat.card (inSubgroup (aschbacherSolvableCore 3) K) ∈
      (Xsub K V).subgroupOf (K ⊓ Subgroup.normalizer (V : Set G)) := by
    have h3 : b ^ Nat.card (inSubgroup (aschbacherSolvableCore 3) K) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, hb]; simpa using hwpow)
    rw [h3]
    exact one_mem _
  have hbX := mem_of_pow_coprime ((Xsub K V).subgroupOf (K ⊓ Subgroup.normalizer (V : Set G)))
    hab hm hk hcop
  have hwX : ((y⁻¹ * ⟨x, hxK⟩ : K) : G) ∈ Xsub K V := by
    rw [← hb]
    exact Subgroup.mem_subgroupOf.mp hbX
  have hxy : x = (y : G) * ((y⁻¹ * ⟨x, hxK⟩ : K) : G) := by
    rw [hwcoe]
    group
  rw [hxy]
  exact (Xsub K V).mul_mem hyX hwX

theorem Xsub_le_closure {K V : Subgroup G} {a : G} (haK : a ∈ K)
    (haX : a ∈ Xsub K V)
    (hnc : Subgroup.closure {z : K ⧸ aschbacherSolvableCore 3 K | ∃ x ∈ imageSub K (Xsub K V),
        z = x * QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩ * x⁻¹} =
      imageSub K (Xsub K V)) :
    Xsub K V ≤ Subgroup.closure {z : G | ∃ x ∈ Xsub K V, z = x * a * x⁻¹} := by
  have hXK : Xsub K V ≤ K := Xsub_le_K K V
  have hXperf : Group.IsPerfect (Xsub K V) := Xsub_perfect K V
  have hθs : Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) K) :=
    (Sec6.theta_solvable_and_not_dvd K).1
  set X : Subgroup G := Xsub K V with hX
  set Z : Subgroup G := Subgroup.closure {z : G | ∃ x ∈ X, z = x * a * x⁻¹} with hZ
  have hZX : Z ≤ X := by
    show Subgroup.closure _ ≤ X
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨x, hx, rfl⟩
    exact X.mul_mem (X.mul_mem hx haX) (X.inv_mem hx)
  have hconj : ∀ k ∈ X, ∀ h ∈ Z, k * h * k⁻¹ ∈ Z := by
    intro k hk h hh
    have hle : Z ≤ Z.comap (MulAut.conj k).toMonoidHom := by
      show Subgroup.closure _ ≤ Z.comap (MulAut.conj k).toMonoidHom
      refine (Subgroup.closure_le _).mpr ?_
      rintro s ⟨x, hx, rfl⟩
      show k * (x * a * x⁻¹) * k⁻¹ ∈ Z
      exact Subgroup.subset_closure ⟨k * x, X.mul_mem hk hx, by group⟩
    exact hle hh
  have hN : (Z.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff hZX).mpr fun h k hh hk => hconj k hk h hh
  have himZ : imageSub K X ≤ imageSub K Z := by
    rw [← hnc]
    refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨x', hx', rfl⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx'
    have hkX : (k : G) ∈ X := Subgroup.mem_subgroupOf.mp hk
    have hmem : ((k * ⟨a, haK⟩ * k⁻¹ : K) : G) ∈ Z := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.subset_closure ⟨k, hkX, rfl⟩
    have heq : QuotientGroup.mk' (aschbacherSolvableCore 3 K) k *
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩ *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k)⁻¹ =
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) (k * ⟨a, haK⟩ * k⁻¹) := by
      simp only [map_mul, map_inv]
    rw [heq]
    exact mk_mem_imageSub hmem
  have hdec : ∀ x : X, ∃ k : X, (k : G) ∈ Z ∧
      ((k⁻¹ * x : X) : G) ∈ inSubgroup (aschbacherSolvableCore 3) K := by
    rintro ⟨x, hxX⟩
    have hxK : x ∈ K := hXK hxX
    have hx1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨x, hxK⟩ ∈ imageSub K X :=
      mk_mem_imageSub hxX
    obtain ⟨k', hk', hπk⟩ := Subgroup.mem_map.mp (himZ hx1)
    have hkZ : (k' : G) ∈ Z := Subgroup.mem_subgroupOf.mp hk'
    have hkX : (k' : G) ∈ X := hZX hkZ
    have hw1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (k'⁻¹ * ⟨x, hxK⟩) = 1 := by
      rw [map_mul, map_inv, hπk, inv_mul_cancel]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw1
    refine ⟨⟨k', hkX⟩, hkZ, ?_⟩
    exact Subgroup.mem_map.mpr ⟨_, hw1, rfl⟩
  have hsolvT : Group.IsSolvable ↥(X ⊓ inSubgroup (aschbacherSolvableCore 3) K) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective
        (inf_le_right : X ⊓ inSubgroup (aschbacherSolvableCore 3) K ≤
          inSubgroup (aschbacherSolvableCore 3) K))
  have hφs : Function.Surjective ((QuotientGroup.mk' (Z.subgroupOf X)).comp
      (Subgroup.inclusion (inf_le_left : X ⊓ inSubgroup (aschbacherSolvableCore 3) K ≤ X))) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf X) q
    obtain ⟨k, hkZ, hθk⟩ := hdec x
    refine ⟨⟨((k⁻¹ * x : X) : G), Subgroup.mem_inf.mpr ⟨(k⁻¹ * x : X).2, hθk⟩⟩, ?_⟩
    have hk1 : QuotientGroup.mk' (Z.subgroupOf X) k = 1 :=
      (QuotientGroup.eq_one_iff k).mpr (Subgroup.mem_subgroupOf.mpr hkZ)
    show QuotientGroup.mk' (Z.subgroupOf X) (k⁻¹ * x) = QuotientGroup.mk' (Z.subgroupOf X) x
    rw [map_mul, map_inv, hk1, inv_one, one_mul]
  have hQs : Group.IsSolvable (X ⧸ Z.subgroupOf X) := Group.isSolvable_of_surjective hφs
  have hres : CFSG.perfectResidual ↥X = ⊤ := by
    have hP : Group.IsPerfect ↥X := hXperf
    unfold CFSG.perfectResidual
    simp
  have hsub : CFSG.perfectResidual ↥X ≤ Z.subgroupOf X :=
    (CFSG.perfect_residual_characterization (G := ↥X)).2.2.2.2.1 (Z.subgroupOf X) |>.mp hQs
  rw [hres] at hsub
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (hsub (Subgroup.mem_top (⟨x, hx⟩ : X)))

end CFSG.RankThree.PartTwo.Sec8.Hering611
