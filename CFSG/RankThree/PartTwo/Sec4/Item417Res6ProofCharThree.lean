module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofCharThree
import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeU33Tools
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG Item434CharThree
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open scoped MatrixGroups
open Res417Five

namespace Res417Six

theorem eq_one_of_pow_three_of_isPGroup_two {M : Type*} [Group M] [Finite M] {T : Subgroup M}
    (hT : IsPGroup 2 T) {x : M} (hxT : x ∈ T) (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨x, hxT⟩
  have h1 : orderOf (⟨x, hxT⟩ : T) ∣ 3 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (by rw [Subgroup.coe_pow, hx3, Subgroup.coe_one])
  have h2 : orderOf (⟨x, hxT⟩ : T) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h3 : orderOf (⟨x, hxT⟩ : T) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h3)

theorem le_centralizer_of_commutator_pow_three {M : Type*} [Group M] [Finite M]
    {U F T : Subgroup M} (hFU : F ≤ U)
    (hU : ∀ v ∈ U, v ≠ 1 → ∀ w : M, w * v = v * w → ∀ r ∈ U, (r * w * r⁻¹ * w⁻¹) ^ 3 = 1)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : 9 ≤ Nat.card F) (hT : IsPGroup 2 T)
    (hFT : F ≤ Subgroup.normalizer (T : Set M)) :
    T ≤ Subgroup.centralizer (F : Set M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := T)).mp hT
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hF (by norm_num; exact hF9) hFT
    hcop fun v hvF hv1 => ?_
  rintro w ⟨hwT, hwv⟩
  have hwv' : w * v = v * w := Subgroup.mem_centralizer_singleton_iff.mp hwv
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have h3 := hU v (hFU hvF) hv1 w hwv' r (hFU hr)
  have hT' : r * w * r⁻¹ * w⁻¹ ∈ T :=
    T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hFT hr) w).mp hwT) (T.inv_mem hwT)
  have h1 := eq_one_of_pow_three_of_isPGroup_two hT hT' h3
  have key : r * w = (r * w * r⁻¹ * w⁻¹) * (w * r) := by group
  rw [key, h1, one_mul]

theorem le_centralizer_of_map {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y) {F T : Subgroup X}
    (h : T.map ψ.toMonoidHom ≤ Subgroup.centralizer (F.map ψ.toMonoidHom : Set Y)) :
    T ≤ Subgroup.centralizer (F : Set X) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have := Subgroup.mem_centralizer_iff.mp (h ⟨t, ht, rfl⟩) (ψ f) ⟨f, hf, rfl⟩
  apply ψ.injective
  simpa [map_mul] using this

theorem isElemAbelian_map_hom {X Y : Type*} [Group X] [Group Y] (ψ : X →* Y) {F : Subgroup X}
    (hF : CFSG.Assembly.IsElemAbelian 3 F) : CFSG.Assembly.IsElemAbelian 3 (F.map ψ) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
    show (x : Y) * y = y * x
    have hab : a * b = b * a := congrArg Subtype.val (hF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [← hax, ← hby, ← map_mul, ← map_mul, hab]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hF.2 a ha, map_one]

theorem map_trans_conj {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y) (g : Y) (F : Subgroup X) :
    F.map (ψ.trans (MulAut.conj g⁻¹)).toMonoidHom =
      (F.map ψ.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem le_centralizer_projSL_three {e : ℕ} (he : 1 ≤ e)
    (F T : Subgroup (projSL 3 (GaloisField 3 e))) (hF : CFSG.Assembly.IsElemAbelian 3 F)
    (hF9 : 9 ≤ Nat.card F) (hT : IsPGroup 2 T) (hFT : F ≤ Subgroup.normalizer (T : Set _)) :
    T ≤ Subgroup.centralizer (F : Set _) := by
  set K := GaloisField 3 e with hKdef
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite SL(3, K) := Finite.of_injective _ Subtype.val_injective
  have hK3 : Nat.card K = 3 ^ e := GaloisField.card 3 e (by omega)
  let φ : projSL 3 K ≃* SL(3, K) := (slEquivProjSL K).symm
  have hF₁ := isElemAbelian_map_hom φ.toMonoidHom hF
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := heis K)
    (by rw [card_heis, hK3, factorization_card_SL_three (by omega), ← pow_mul, mul_comm])
    (Sec5.isPGroup_of_isElemAbelian hF₁)
  set ψ : projSL 3 K ≃* SL(3, K) := φ.trans (MulAut.conj g⁻¹) with hψ
  have hF₂le : F.map ψ.toMonoidHom ≤ heis K := by
    rw [hψ, map_trans_conj]
    exact Item434AltPerm.map_conj_inv_le hg
  have hF₂ := isElemAbelian_map_hom ψ.toMonoidHom hF
  obtain ⟨a₀, b₀, -, hle⟩ := exists_le_lineSub hF₂le fun x hx y hy =>
    congrArg Subtype.val (hF₂.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine le_centralizer_of_map ψ (le_centralizer_of_commutator_pow_three hle ?_ hF₂ ?_
    (hT.map _) ?_)
  · intro v hv hv1 w hwv r hr
    exact pow_three_eq_one_of_mem_heis (commutator_mem_heis hv hv1 hwv hr)
  · rw [Subgroup.card_map_of_injective ψ.injective]
    exact hF9
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hFT

theorem le_centralizer_projSU_three {e : ℕ} (he : 1 ≤ e)
    (F T : Subgroup (projSU 3 3 e)) (hF : CFSG.Assembly.IsElemAbelian 3 F)
    (hF9 : 9 ≤ Nat.card F) (hT : IsPGroup 2 T) (hFT : F ≤ Subgroup.normalizer (T : Set _)) :
    T ≤ Subgroup.centralizer (F : Set _) := by
  set K := GaloisField 3 (2 * e) with hKdef
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card K = (3 ^ e) ^ 2 := card_galois_two_mul (by omega)
  have hσ := unitaryInvolution_involutive hK
  have : Finite (SU (unitaryInvolution K 3 e) 3) := Finite.of_injective _ Subtype.val_injective
  let φ : projSU 3 3 e ≃* SU (unitaryInvolution K 3 e) 3 := (suEquivProjSU (by omega)).symm
  have hF₁ := isElemAbelian_map_hom φ.toMonoidHom hF
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := heisU hσ)
    (by rw [card_heisU hK, factorization_card_SU_three (by omega), ← pow_mul, mul_comm])
    (Sec5.isPGroup_of_isElemAbelian hF₁)
  set ψ : projSU 3 3 e ≃* SU (unitaryInvolution K 3 e) 3 := φ.trans (MulAut.conj g⁻¹) with hψ
  have hF₂le : F.map ψ.toMonoidHom ≤ heisU hσ := by
    rw [hψ, map_trans_conj]
    exact Item434AltPerm.map_conj_inv_le hg
  have hF₂ := isElemAbelian_map_hom ψ.toMonoidHom hF
  refine le_centralizer_of_map ψ (le_centralizer_of_commutator_pow_three hF₂le ?_ hF₂ ?_
    (hT.map _) ?_)
  · intro v hv hv1 w hwv r hr
    exact commutator_pow_three_heisU hv hv1 hwv hr
  · rw [Subgroup.card_map_of_injective ψ.injective]
    exact hF9
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hFT

theorem k417NoActLThreeThree_holds : K417NoActLThreeThree := fun _ he1 _ =>
  ⟨fun F T hF hF9 hT hFT => le_centralizer_projSL_three he1 F T hF hF9 hT hFT,
    fun F T hF hF9 hT hFT => le_centralizer_projSU_three he1 F T hF hF9 hT hFT⟩

end Res417Six

end CFSG.RankThree.PartTwo.Sec4
