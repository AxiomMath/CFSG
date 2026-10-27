module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofTools
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.KF.SymCtxMatrix
import CFSG.RankThree.PartOne.KF.SUSylow
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofChevTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (SU equivStatedSU)
open Res417Three Res417Five

namespace Res417Six

theorem gcd_four_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Nat.gcd 4 (2 ^ n + 1) = 1 := by
  have h2 : Odd (2 ^ n + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr h2)
  simpa using this

theorem card_galoisField_two_mul {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := by
  rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]

noncomputable def unitarySUEquivProjSU {n : ℕ} (hn : 1 ≤ n) :
    unitarySU 2 n (GaloisField 2 (2 * n)) 4 ≃* projSU 4 2 n :=
  (projEquivOfBot (scalars_subgroupOf_eq_bot (card_galoisField_two_mul hn) (by norm_num)
    (gcd_four_two_pow_add_one hn))).symm.trans (projSUEquivStatedProj 4 2 n).symm

theorem three_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  have h := (two_pow_mod_three n).2 hn
  generalize 2 ^ n = m at h ⊢
  omega

theorem k417DatumU4Odd_holds : K417DatumU4Odd := by
  intro n hn D hD
  obtain ⟨hDe, hmax, -⟩ := hD
  have hn1 : 1 ≤ n := hn.pos
  set K := GaloisField 2 (2 * n) with hKdef
  have hK : Nat.card K = (2 ^ n) ^ 2 := card_galoisField_two_mul hn1
  have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn1, GaloisField.card 2 (2 * n) (by omega)⟩
  have h3 : 3 ∣ 2 ^ n + 1 := three_dvd_two_pow_add_one hn
  have hDexp : ∀ x ∈ D, x ^ 3 = 1 := hDe.2
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU Nat.prime_three h3 (unitarySUEquivProjSU hn1) D
    hDexp hDcomm
  set T : Subgroup (unitarySU 2 n K 4) := (torusSU 3 4 K).subgroupOf (unitarySU 2 n K 4)
    with hTdef
  have hTexp : ∀ t ∈ T, t ^ 3 = 1 := by
    intro t ht
    obtain ⟨d, hd1, -, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp ht)
    apply Subtype.ext
    show (t : GL (Fin 4) K) ^ 3 = 1
    rw [← hd, diagU_pow, show d ^ 3 = 1 from funext hd1, diagU_one]
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    obtain ⟨d, -, -, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp hs)
    obtain ⟨d', -, -, hd'⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp ht)
    apply Subtype.ext
    show (s : GL (Fin 4) K) * t = t * s
    rw [← hd, ← hd', diagU_mul, diagU_mul, mul_comm d d']
  have hmap : D.map (ψ.symm.trans (MulAut.conj 1)).toMonoidHom = T := by
    refine map_eq_of_conj_le ψ.symm hmax hTcomm hTexp fun x hx => ?_
    rw [one_mul, inv_one, mul_one]
    exact Subgroup.mem_subgroupOf.mpr (hψ _ (by rw [MulEquiv.apply_symm_apply]; exact hx))
  have hdvd : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have h1 : 2 ^ n + 1 ∣ (2 ^ n) ^ 2 - 1 := by
      have : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
        have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        zify [Nat.one_le_pow 2 (2 ^ n) (by omega), hq]
        ring
      rw [this]
      exact dvd_mul_left _ _
    exact h3.trans h1
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_three hdvd
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have := hζ.dvd_of_pow_eq_one 2 h
    norm_num at this
  have hdist : ∀ i j : Fin 4, i ≠ j → ∃ x ∈ torusSU 3 4 K, ent x i i ≠ ent x j j :=
    fun i j hij => torusSU_char_distinct hζ3 hζ2 hij
  obtain ⟨SM⟩ := SymCtx.ofMatrixGroup (unitarySU 2 n K 4) (torusSU_le_unitarySU hU h3)
    (fun σ => permGL_mem_unitarySU hU σ) hdist
  refine ⟨?_, ?_⟩
  · rw [card_eq_of_map_eq _ hmap, SM.card_F (m := 3) rfl (by norm_num) ⟨ζ, hζ⟩]
    norm_num
  · obtain ⟨φ⟩ := nonempty_autIn_mulEquiv_of_map_eq _ hmap
    exact ⟨φ.trans (SM.weylEquiv Nat.prime_three (by norm_num) ⟨ζ, hζ⟩)⟩

noncomputable def projSUEquivSU {n : ℕ} (hn : 1 ≤ n) :
    projSU 4 2 n ≃* SU (unitaryInvolution (GaloisField 2 (2 * n)) 2 n) 4 :=
  (unitarySUEquivProjSU hn).symm.trans (equivStatedSU (card_galoisField_two_mul hn) 4).symm

theorem k417DatumU4Even_holds : K417DatumU4Even := by
  intro n hn1 hev D hD
  obtain ⟨hDe, hmax, -⟩ := hD
  set K := GaloisField 2 (2 * n) with hKdef
  have hK : Nat.card K = (2 ^ n) ^ 2 := card_galoisField_two_mul hn1
  set σ : K ≃+* K := unitaryInvolution K 2 n with hσdef
  have hσ : ∀ c : K, σ c = c ^ 2 ^ n := fun c => unitaryInvolution_apply K 2 n c
  have hpq : 3 ∣ 2 ^ n - 1 := three_dvd_two_pow_sub_one hev
  let e₀ : projSU 4 2 n ≃* SU σ 4 := projSUEquivSU hn1
  set T : Subgroup (SU σ 4) := (d8Tor 3 K 4).subgroupOf (SU σ 4) with hTdef
  have hTexp : ∀ t ∈ T, t ^ 3 = 1 := by
    intro t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((t : SU σ 4) : GL (Fin 4) K) ^ 3 = 1
    rw [← hv]
    show diagU (d8Vec 4 v) ^ 3 = 1
    rw [diagU_pow, d8Vec_pow_eq_one, diagU_one]
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((s : SU σ 4) : GL (Fin 4) K) * (t : GL (Fin 4) K) =
      (t : GL (Fin 4) K) * (s : GL (Fin 4) K)
    rw [← hv, ← hw]
    show diagU (d8Vec 4 v) * diagU (d8Vec 4 w) = diagU (d8Vec 4 w) * diagU (d8Vec 4 v)
    rw [diagU_mul, diagU_mul, mul_comm (d8Vec 4 v) (d8Vec 4 w)]
  have hD'exp : ∀ x ∈ D.map e₀.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show e₀ x ^ 3 = 1
    rw [← map_pow, hDe.2 x hx, map_one]
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_su (Or.inl rfl) d8Comb_four hK Nat.prime_three
    (by norm_num) hpq _ hD'exp
  have hmap : D.map (e₀.trans (MulAut.conj g)).toMonoidHom = T :=
    map_eq_of_conj_le e₀ hmax hTcomm hTexp fun x hx => hg _ ⟨x, hx, rfl⟩
  have hdvd : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have h1 : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := by
      have : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
        have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        zify [Nat.one_le_pow 2 (2 ^ n) (by omega), hq]
        ring
      rw [this]
      exact dvd_mul_right _ _
    exact hpq.trans h1
  have hζ := exists_primitiveRoot_three hdvd
  have hσfix : ∀ u : rootsOfUnity 3 K, σ ((u : Kˣ) : K) = (u : Kˣ) := by
    intro u
    have h1 : (u : Kˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp u.2
    have h2 : (u : Kˣ) ^ (2 ^ n - 1) = 1 := by
      obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, h1, one_pow]
    rw [hσ, ← Units.val_pow_eq_pow_val]
    have : (u : Kˣ) ^ 2 ^ n = (u : Kˣ) := by
      calc (u : Kˣ) ^ 2 ^ n = (u : Kˣ) ^ (2 ^ n - 1) * (u : Kˣ) := by
            rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
        _ = (u : Kˣ) := by rw [h2, one_mul]
    rw [this]
  have hT4 : ∀ v : D8Mod 3 K, (diagU (d8Vec 4 v) : GL (Fin 4) K) ∈ SU σ 4 :=
    fun v => d8Vec_mem_SU (Or.inl rfl) d8Comb_four σ hσfix v
  have hP4 : ∀ τ : Equiv.Perm (Fin 4), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (permGL τ : GL (Fin 4) K) ∈ SU σ 4 := fun τ hτ => permGL_mem_SU σ τ hτ
  obtain ⟨SM⟩ := exists_d8ctx d8Comb_four d8Comb2_four Nat.prime_three (by norm_num) hζ
    (SU σ 4) hT4 hP4
  refine ⟨?_, ?_⟩
  · rw [card_eq_of_map_eq _ hmap, SM.card_F (by norm_num) hζ]
    norm_num
  · obtain ⟨φ⟩ := nonempty_autIn_mulEquiv_of_map_eq _ hmap
    exact ⟨φ.trans (SM.weylEquiv Nat.prime_three (by norm_num) hζ)⟩

end Res417Six

end CFSG.RankThree.PartTwo.Sec4
