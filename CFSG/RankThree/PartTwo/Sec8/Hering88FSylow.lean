module

public import CFSG.RankThree.PartTwo.Sec8.Item87ProofTools
import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
import CFSG.RankThree.PartTwo.Sec8.Item86Res2ProofIndep
import CFSG.GH74.Generic.S1.KL3L2

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88F

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

theorem commute_of_isPGroup_three_sl2 {F : Type} [Field F] [Finite F] [CharP F 2]
    (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hP : IsPGroup 3 P) :
    ∀ u ∈ P, ∀ v ∈ P, u * v = v * u := by
  intro u hu v hv
  by_cases hbot : P = ⊥
  · rw [hbot, Subgroup.mem_bot] at hu hv
    subst hu
    subst hv
    simp
  · haveI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hbot
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : Nontrivial (Subgroup.center P) := hP.center_nontrivial
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center P)
    have hz1' : (z : Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 := by
      intro h
      apply hz1
      exact Subtype.ext (Subtype.ext h)
    have hnc : (z : Matrix.SpecialLinearGroup (Fin 2) F) ∉
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Item86ResProof.center_specialLinearGroup_two_eq_bot, Subgroup.mem_bot]
      exact hz1'
    have hG : ∀ c : F, ((z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ≠
        c • (1 : Matrix (Fin 2) (Fin 2) F) := by
      intro c hc
      apply hnc
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨c, ?_, ?_⟩
      · have hdet := (z : Matrix.SpecialLinearGroup (Fin 2) F).2
        rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
        exact hdet
      · rw [hc]
        ext i j
        by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    have hcomm : ∀ w ∈ P, ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      intro w hw
      have h := (Subgroup.mem_center_iff.mp hz) ⟨w, hw⟩
      have h' := congrArg (fun x : P => ((x : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)) h
      simpa using h'
    exact Subtype.ext (CFSG.GH74.Generic.S1.KL3L2.commute_of_commute_nonscalar hG (hcomm u hu)
      (hcomm v hv))

theorem commute_of_isPGroup_of_imageModTheta {G : Type} [Group G] [Finite G] {L K : Subgroup G}
    (hKL : K ≤ L) {f : ℕ} (hf : 2 ≤ f)
    (e : imageModTheta L K ≃* projSL 2 (GaloisField 2 f))
    {P : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 3 P) :
    ∀ u ∈ P, ∀ v ∈ P, u * v = v * u := by
  classical
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := KFacts.nonempty_sl2_mulEquiv_projSL hF
  set ρ := Item87Proof.modThetaOnto hKL with hρ
  set Φ : K →* projSL 2 (GaloisField 2 f) := e.toMonoidHom.comp ρ with hΦ
  have hP' : IsPGroup 3 (P.subgroupOf K) := hP.comap_of_injective K.subtype K.subtype_injective
  have hQ : IsPGroup 3 ((P.subgroupOf K).map Φ) := hP'.map Φ
  have hQ' : IsPGroup 3 (((P.subgroupOf K).map Φ).comap φ.toMonoidHom) :=
    hQ.comap_of_injective φ.toMonoidHom φ.injective
  intro u hu v hv
  set u' : K := ⟨u, hPK hu⟩ with hu'
  set v' : K := ⟨v, hPK hv⟩ with hv'
  have hmem : ∀ w : K, w ∈ P.subgroupOf K → φ.symm (Φ w) ∈
      ((P.subgroupOf K).map Φ).comap φ.toMonoidHom := fun w hw => by
    rw [Subgroup.mem_comap]
    change φ (φ.symm (Φ w)) ∈ _
    rw [MulEquiv.apply_symm_apply]
    exact ⟨w, hw, rfl⟩
  have hcomm := commute_of_isPGroup_three_sl2 _ hQ' _ (hmem u' hu) _ (hmem v' hv)
  have hΦ1 : Φ (u' * v' * u'⁻¹ * v'⁻¹) = 1 := by
    have h1 : Φ u' * Φ v' = Φ v' * Φ u' := by
      have := congrArg φ hcomm
      simpa using this
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group
  set c : G := u * v * u⁻¹ * v⁻¹ with hc
  have hcP : c ∈ P := P.mul_mem (P.mul_mem (P.mul_mem hu hv) (P.inv_mem hu)) (P.inv_mem hv)
  have hcK : (⟨c, hPK hcP⟩ : K) = u' * v' * u'⁻¹ * v'⁻¹ := rfl
  have hker : (⟨c, hPK hcP⟩ : K) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    apply e.injective
    rw [map_one]
    have := hΦ1
    rw [← hcK] at this
    exact this
  obtain ⟨k, hk⟩ := hP ⟨c, hcP⟩
  have hk' : c ^ 3 ^ k = 1 := by
    have := congrArg (fun x : P => (x : G)) hk
    simpa using this
  have hord : orderOf (⟨⟨c, hPK hcP⟩, hker⟩ : ρ.ker) ∣ Nat.card ρ.ker := orderOf_dvd_natCard _
  have hord' : orderOf (⟨⟨c, hPK hcP⟩, hker⟩ : ρ.ker) = orderOf c := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
  rw [hord'] at hord
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk')
  have hj0 : j = 0 := by
    by_contra hj0
    apply Item87Proof.not_three_dvd_card_ker_modThetaOnto hKL
    rw [hj] at hord
    exact (dvd_pow_self 3 hj0).trans hord
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  have hc1 : u * v * u⁻¹ * v⁻¹ = 1 := hj
  calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
    _ = v * u := by rw [hc1, one_mul]

theorem sylow_comm_imageModTheta {G : Type} [Group G] [Finite G] {Y T : Subgroup G} (hTY : T ≤ Y)
    (hT : ∀ P : Subgroup G, P ≤ T → IsPGroup 3 P → ∀ u ∈ P, ∀ v ∈ P, u * v = v * u)
    (Q : Sylow 3 (imageModTheta Y T)) :
    ∀ a b : (Q : Subgroup (imageModTheta Y T)), a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective (Item87Proof.modThetaOnto_surjective hTY) 3 Q
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  have ha' : a ∈ (P : Subgroup T).map (Item87Proof.modThetaOnto hTY) := ha
  have hb' : b ∈ (P : Subgroup T).map (Item87Proof.modThetaOnto hTY) := hb
  obtain ⟨a₀, ha₀, rfl⟩ := ha'
  obtain ⟨b₀, hb₀, rfl⟩ := hb'
  have hPG : IsPGroup 3 ((P : Subgroup T).map T.subtype) := P.2.map T.subtype
  have hle : (P : Subgroup T).map T.subtype ≤ T := Subgroup.map_subtype_le _
  have h := hT _ hle hPG (a₀ : G) ⟨a₀, ha₀, rfl⟩ (b₀ : G) ⟨b₀, hb₀, rfl⟩
  apply Subtype.ext
  change Item87Proof.modThetaOnto hTY a₀ * Item87Proof.modThetaOnto hTY b₀ =
    Item87Proof.modThetaOnto hTY b₀ * Item87Proof.modThetaOnto hTY a₀
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext h)

theorem false_of_central_three {G : Type} [Group G] [Finite G] {Y T : Subgroup G} (hTY : T ≤ Y)
    (hT : ∀ P : Subgroup G, P ≤ T → IsPGroup 3 P → ∀ u ∈ P, ∀ v ∈ P, u * v = v * u)
    (hperf : Group.IsPerfect (imageModTheta Y T)) {z : imageModTheta Y T} (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1) (hzc : ∀ y, z * y = y * z) : False := by
  haveI := hperf
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hZc : Subgroup.zpowers z ≤ Subgroup.center (imageModTheta Y T) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro y
    exact (hzc y).symm
  haveI : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center hZc
  have hbot := KFacts.KS14.eq_bot_of_isPerfect_of_sylow_comm hZc (fun p hp hpZ P => ?_)
  · apply hz1
    have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  · have hcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hord]
    rw [hcard] at hpZ
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpZ
    subst hp3
    exact sylow_comm_imageModTheta hTY hT P

theorem false_of_central_three_of_eq {G : Type} [Group G] [Finite G] {Y T : Subgroup G}
    (hTY : T ≤ Y)
    (hT : ∀ P : Subgroup G, P ≤ T → IsPGroup 3 P → ∀ u ∈ P, ∀ v ∈ P, u * v = v * u)
    {S : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)} (hS : imageModTheta Y T = S)
    (hperf : Group.IsPerfect S) {z : Y ⧸ aschbacherSolvableCore 3 Y} (hzS : z ∈ S) (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1) (hzc : ∀ y ∈ S, z * y = y * z) : False := by
  subst hS
  refine false_of_central_three hTY hT hperf (z := ⟨z, hzS⟩) ?_ ?_ ?_
  · intro h
    exact hz1 (congrArg Subtype.val h)
  · exact Subtype.ext hz3
  · intro y
    exact Subtype.ext (hzc y y.2)

end Hering88F

end CFSG.RankThree.PartTwo.Sec8
