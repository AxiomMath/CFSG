module

public import CFSG.RankThree.SubgroupLists.CliffordPrime
import CFSG.Quasithin.EmptyFaithful.A38c15IrrMono
import CFSG.GroupTheory.ThreeTranspositions.NormalCores
public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.GL3Excl

open Matrix CFSG.RepresentationTheory
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.SubgroupLists (IsTransitiveMonomial translate mulVec_mem_translate)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem perm_three_fact : ∀ σ τ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 →
    (τ * σ = σ * τ → τ * τ = 1 → τ = 1) ∧ ∀ i, σ i ≠ i := by
  decide

theorem false_of_isTransitiveMonomial {r p : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hp : p.Prime)
    (hp2 : p ≠ 2) {W : Subgroup (GL (Fin 3) (ZMod r))} (hmono : IsTransitiveMonomial W)
    {Y : Subgroup W} (hY : IsStronglyPEmbedded p Y) {t₁ y : GL (Fin 3) (ZMod r)} (ht₁ : t₁ ∈ W)
    (ht₁d : (t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![-1, 1, 1]) (hy : y ∈ W)
    (hyp : y ^ p = 1) {α : Fin 3 → ZMod r}
    (hyd : (y : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal α) (hyns : ∃ i j, α i ≠ α j) :
    False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  have hneg : (-1 : ZMod r) ≠ 1 := by
    haveI : Fact (2 < r) := ⟨lt_of_le_of_ne (Fact.out : r.Prime).two_le (Ne.symm hr2)⟩
    exact ZMod.neg_one_ne_one
  obtain ⟨L, hL, hrk, hperm, -⟩ := hmono
  have hinj := CFSG.Quasithin.A38c15.monoLines_injective hL hrk
  set π := CFSG.Quasithin.A38c15.monoLineHom hinj hperm with hπ
  have hfixL : ∀ g ∈ π.ker, ∀ i, translate (g : GL (Fin 3) (ZMod r)) (L i) = L i :=
    fun g hg => CFSG.Quasithin.A38c15.translate_eq_of_mem_monoLineHom_ker hinj hperm hg
  have hcomm : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a * b = b * a := fun a ha b hb =>
    Subtype.ext (CFSG.Quasithin.A38c15.mono_mul_comm_of_translate_eq hL hrk (hfixL a ha)
      (hfixL b hb))
  let y' : W := ⟨y, hy⟩
  let t' : W := ⟨t₁, ht₁⟩
  have hy1 : y ≠ 1 := by
    rintro rfl
    obtain ⟨i, j, hij⟩ := hyns
    have hi := congrArg (fun M : Matrix (Fin 3) (Fin 3) (ZMod r) => M i i) hyd
    have hj := congrArg (fun M : Matrix (Fin 3) (Fin 3) (ZMod r) => M j j) hyd
    simp only [Units.val_one, one_apply_eq, diagonal_apply_eq] at hi hj
    exact hij (hi.symm.trans hj)
  have hy'p : y' ^ p = 1 := Subtype.ext hyp
  have hσ1 : π y' ≠ 1 := by
    intro hyk
    let P : Subgroup W :=
      { carrier := {g | g ∈ π.ker ∧ g ^ p = 1}
        mul_mem' := fun {a b} ha hb => ⟨π.ker.mul_mem ha.1 hb.1, by
          rw [Commute.mul_pow (hcomm a ha.1 b hb.1), ha.2, hb.2, one_mul]⟩
        one_mem' := ⟨π.ker.one_mem, one_pow p⟩
        inv_mem' := fun {a} ha => ⟨π.ker.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
    have hPn : P.Normal := ⟨fun a ha g => ⟨π.normal_ker.conj_mem a ha.1 g, by
      rw [conj_pow, ha.2, mul_one, mul_inv_cancel]⟩⟩
    have hPp : IsPGroup p P := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext x.2.2⟩
    have hle : P ≤ CFSG.pCore p W := le_sSup ⟨hPn, hPp⟩
    rw [CFSG.GroupTheory.ThreeTranspositions.pCore_eq_bot_of_isStronglyPEmbedded hp hY] at hle
    have hyP : y' ∈ P := ⟨MonoidHom.mem_ker.mpr hyk, hy'p⟩
    exact hy1 (congrArg Subtype.val (Subgroup.mem_bot.mp (hle hyP)))
  have hσp : π y' ^ p = 1 := by rw [← map_pow, hy'p, map_one]
  obtain rfl : p = 3 := by
    have h6 : p ∣ 2 * 3 := by
      have h := orderOf_dvd_card (x := π y')
      rwa [orderOf_eq_prime hσp hσ1, Fintype.card_perm, Fintype.card_fin] at h
    rcases (Nat.Prime.dvd_mul hp).mp h6 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
  obtain ⟨hcent, hfpf⟩ := perm_three_fact (π y') (π t') hσp hσ1
  have hty : t₁ * y = y * t₁ := Units.ext (by
    rw [Units.val_mul, Units.val_mul, ht₁d, hyd, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _)
  have htt : t₁ * t₁ = 1 := Units.ext (by
    rw [Units.val_mul, ht₁d, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp)
  have htL : ∀ i, translate t₁ (L i) = L i := hfixL t' (MonoidHom.mem_ker.mpr (hcent
    (by rw [← map_mul, ← map_mul, show t' * y' = y' * t' from Subtype.ext hty])
    (by rw [← map_mul, show t' * t' = 1 from Subtype.ext htt, map_one])))
  have hc : ∀ i, ∃ c : ZMod r, ∀ x ∈ L i, (t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ x = c • x := by
    intro i
    obtain ⟨c, hc⟩ := CFSG.Quasithin.A38c15.monoLine_exists_smul (hrk i)
      (f := Matrix.toLin' (t₁ : Matrix (Fin 3) (Fin 3) (ZMod r))) fun x hx => by
        have h := mulVec_mem_translate (g := t₁) hx
        rwa [htL i] at h
    exact ⟨c, fun x hx => by simpa [Matrix.toLin'_apply] using hc x hx⟩
  choose c hc using hc
  obtain ⟨k, hk⟩ : ∃ k, c k ≠ 1 := by
    by_contra hall
    push Not at hall
    have hfix : ∀ x : Fin 3 → ZMod r, (t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ x = x := by
      intro x
      have hx : x ∈ ⨆ i, L i := by
        rw [hL.submodule_iSup_eq_top]
        trivial
      refine Submodule.iSup_induction L
        (motive := fun x => (t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ x = x) hx
        (fun i x hx => by rw [hc i x hx, hall i, one_smul]) (by simp) ?_
      intro u w hu hw
      rw [Matrix.mulVec_add, hu, hw]
    have h0 := congrFun (hfix (Pi.single 0 1)) 0
    rw [ht₁d, mulVec_diagonal] at h0
    exact hneg (by simpa using h0)
  obtain ⟨v₀, hv₀, -⟩ := finrank_eq_one_iff'.mp (hrk k)
  have hv0 : (v₀ : Fin 3 → ZMod r) ≠ 0 := fun h => hv₀ (Subtype.ext h)
  have hv12 : ∀ i, i ≠ 0 → (v₀ : Fin 3 → ZMod r) i = 0 := by
    intro i hi
    have h := congrFun (hc k v₀ v₀.2) i
    have h1 : ![(-1 : ZMod r), 1, 1] i = 1 := by
      fin_cases i
      · exact absurd rfl hi
      · simp
      · simp
    rw [ht₁d, mulVec_diagonal, h1, one_mul, Pi.smul_apply, smul_eq_mul] at h
    have h2 : (1 - c k) * (v₀ : Fin 3 → ZMod r) i = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hk))
  have hyv : (y : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ v₀ = α 0 • (v₀ : Fin 3 → ZMod r) := by
    funext i
    rw [hyd, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i = 0
    · rw [hi]
    · rw [hv12 i hi, mul_zero, mul_zero]
  have hmem1 : (y : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ v₀ ∈ L k := by
    rw [hyv]
    exact (L k).smul_mem _ v₀.2
  have hmem2 : (y : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ v₀ ∈ L (π y' k) := by
    rw [← CFSG.Quasithin.A38c15.translate_monoLineHom hinj hperm y' k]
    exact mulVec_mem_translate v₀.2
  have hzero := Submodule.disjoint_def.mp (hL.submodule_iSupIndep.pairwiseDisjoint (hfpf k)) _
    hmem2 hmem1
  apply hv0
  calc (v₀ : Fin 3 → ZMod r)
      = ((y⁻¹ * y : GL (Fin 3) (ZMod r)) : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ v₀ := by
        rw [inv_mul_cancel, Units.val_one, one_mulVec]
    _ = 0 := by rw [Units.val_mul, ← mulVec_mulVec, hzero, mulVec_zero]

end CFSG.LocalAnalysis.UniquenessCase.GL3Excl
