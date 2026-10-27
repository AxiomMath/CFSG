module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofTools
import CFSG.RankThree.PartOne.KF.ClsSpUpper
import CFSG.RankThree.PartOne.KF.SpSylow
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofChevTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.LieType.BorelTits
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Unitary (conjTr)
open Res417Three Res417Five

namespace Res417Six

noncomputable def projSpEquivSp (K : Type) [Field K] [Finite K] [CharP K 2] :
    projSp 2 K ≃* StatedSp 2 K :=
  (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSp 2 K)).symm.trans
    (KFU.spEquivProj (K := K) (by norm_num)).symm

theorem not_three_dvd_two_pow_sub_one {n : ℕ} (hn : Odd n) : ¬ 3 ∣ 2 ^ n - 1 := by
  have h := (two_pow_mod_three n).2 hn
  generalize 2 ^ n = m at h ⊢
  omega

theorem three_dvd_two_pow_sub_one {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  have h := (two_pow_mod_three n).1 hn
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp h.symm

theorem exists_primitiveRoot_three {K : Type} [Field K] [Finite K]
    (hdvd : 3 ∣ Nat.card K - 1) : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd' : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd'
  refine ⟨z, ?_⟩
  have := IsPrimitiveRoot.orderOf z
  rwa [hz] at this

theorem k417NoDatumSp4Odd_holds : K417NoDatumSp4Odd := by
  intro n hn D hD
  obtain ⟨hDe, -, F, hFD, hF9, T, hT2, hFT, hTF⟩ := hD
  set K := GaloisField 2 n with hKdef
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Nat.not_odd_zero hn
  have hK : Nat.card K = 2 ^ n := GaloisField.card 2 n hn0
  let e : projSp 2 K ≃* StatedSp 2 K := projSpEquivSp K
  have hT1 : T ≠ ⊥ := by
    rintro rfl
    exact hTF bot_le
  set F' : Subgroup (StatedSp 2 K) := F.map e.toMonoidHom with hF'
  set T' : Subgroup (StatedSp 2 K) := T.map e.toMonoidHom with hT'
  have hT'2 : IsPGroup 2 T' := hT2.map _
  have hT'1 : T' ≠ ⊥ := by
    intro h
    apply hT1
    rw [hT', Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h
    exact h
  have hF'T' : F' ≤ Subgroup.normalizer (T' : Set (StatedSp 2 K)) := by
    rw [hF', hT', ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hFT
  have hcomm : ∀ g ∈ F', ∀ h ∈ F', g * h = h * g := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show e x * e y = e y * e x
    have hxy : x * y = y * x :=
      congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hFD hx⟩ ⟨y, hFD hy⟩)
    rw [← map_mul, ← map_mul, hxy]
  have hexp : ∀ g ∈ F', g ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show e x ^ 3 = 1
    rw [← map_pow, hDe.2 x (hFD hx), map_one]
  have hdiv : ∀ i : ℕ, 0 < i → i < 2 → ¬ 3 ∣ Nat.card K ^ i - 1 := by
    intro i hi hi2
    obtain rfl : i = 1 := by omega
    rw [pow_one, hK]
    exact not_three_dvd_two_pow_sub_one hn
  obtain ⟨a, ha1, ha2, hcard⟩ := card_le_of_normalizes (spForm 2 K) (natRep (StatedSp 2 K))
    (isIsometric_natRep_statedSp 2 K) (natRep_injective _) Nat.prime_three (by norm_num)
    (natCast_ne_zero_of_ne_two Nat.prime_three (by norm_num)) (d := 2) (by norm_num) hdiv
    hT'2 hT'1 hF'T' hcomm hexp
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at ha2 hcard
  have hF'card : Nat.card F' = Nat.card F := Subgroup.card_map_of_injective e.injective
  have ha2' : a ≤ 2 := by omega
  have hle : 3 ^ (a / 2) * 3 ^ ((2 + 2 - 2 * a) / 2) ≤ 3 := by
    interval_cases a <;> norm_num
  omega

theorem k417DatumSp4Even_holds : K417DatumSp4Even := by
  intro n hn1 hev D hD
  obtain ⟨hDe, hmax, -⟩ := hD
  set K := GaloisField 2 n with hKdef
  have hK : Nat.card K = 2 ^ n := GaloisField.card 2 n (by omega)
  have hdvd : 3 ∣ Nat.card K - 1 := by rw [hK]; exact three_dvd_two_pow_sub_one hev
  have hζ := exists_primitiveRoot_three hdvd
  let e₀ : projSp 2 K ≃* spRev K := (projSpEquivSp K).trans (spRevEquiv K)
  set T : Subgroup (spRev K) := (d8Tor 3 K 4).subgroupOf (spRev K) with hTdef
  have hTexp : ∀ t ∈ T, t ^ 3 = 1 := by
    intro t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((t : spRev K) : GL (Fin 4) K) ^ 3 = 1
    rw [← hv]
    show diagU (d8Vec 4 v) ^ 3 = 1
    rw [diagU_pow, d8Vec_pow_eq_one, diagU_one]
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((s : spRev K) : GL (Fin 4) K) * (t : GL (Fin 4) K) =
      (t : GL (Fin 4) K) * (s : GL (Fin 4) K)
    rw [← hv, ← hw]
    show diagU (d8Vec 4 v) * diagU (d8Vec 4 w) = diagU (d8Vec 4 w) * diagU (d8Vec 4 v)
    rw [diagU_mul, diagU_mul, mul_comm]
  have hD'exp : ∀ x ∈ D.map e₀.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show e₀ x ^ 3 = 1
    rw [← map_pow, hDe.2 x hx, map_one]
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_sp Nat.prime_three (by norm_num) hdvd _ hD'exp
  have hmap : D.map (e₀.trans (MulAut.conj g)).toMonoidHom = T :=
    map_eq_of_conj_le e₀ hmax hTcomm hTexp fun x hx => hg _ ⟨x, hx, rfl⟩
  have hT4 : ∀ v : D8Mod 3 K, (diagU (d8Vec 4 v) : GL (Fin 4) K) ∈ spRev K := fun v => by
    rw [d8Vec_four]
    exact diagU_dvec4_mem_spRev _ _
  have hP4 : ∀ τ : Equiv.Perm (Fin 4), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (permGL τ : GL (Fin 4) K) ∈ spRev K := fun τ hτ => by
    rw [mem_spRev_iff]
    simpa [conjTr] using permGL_gram (RingEquiv.refl K) τ hτ
  obtain ⟨SM⟩ := exists_d8ctx d8Comb_four d8Comb2_four Nat.prime_three (by norm_num) hζ
    (spRev K) hT4 hP4
  refine ⟨?_, ?_⟩
  · rw [card_eq_of_map_eq _ hmap, SM.card_F (by norm_num) hζ]
    norm_num
  · obtain ⟨φ⟩ := nonempty_autIn_mulEquiv_of_map_eq _ hmap
    exact ⟨φ.trans (SM.weylEquiv Nat.prime_three (by norm_num) hζ)⟩

end Res417Six

end CFSG.RankThree.PartTwo.Sec4
