module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.SectionRank.AlternatingCover
import CFSG.RankThree.Theta.ThreeCoreComponentNormalization
import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open Equiv Equiv.Perm
open CFSG.Assembly.RankThreeEven (localRank)

@[expose] def tenCyc0 : Perm (Fin 10) := swap 0 1 * swap 1 2

@[expose] def tenCyc1 : Perm (Fin 10) := swap 3 4 * swap 4 5

@[expose] def tenCyc2 : Perm (Fin 10) := swap 6 7 * swap 7 8

@[expose] def tenParam (v : Fin 3 → ZMod 3) : Perm (Fin 10) :=
  tenCyc0 ^ (v 0).val * tenCyc1 ^ (v 1).val * tenCyc2 ^ (v 2).val

theorem tenParam_add : ∀ v w : Fin 3 → ZMod 3, tenParam (v + w) = tenParam v * tenParam w := by
  decide +kernel

theorem tenParam_zero : tenParam 0 = 1 := by decide +kernel

theorem tenParam_eq_one : ∀ v : Fin 3 → ZMod 3, tenParam v = 1 → v = 0 := by decide +kernel

theorem tenParam_sign : ∀ v : Fin 3 → ZMod 3, sign (tenParam v) = 1 := by decide +kernel

@[expose] def kleinParam (w : Fin 2 → ZMod 2) : Perm (Fin 10) :=
  (swap 0 1 * swap 2 9) ^ (w 0).val * (swap 0 2 * swap 1 9) ^ (w 1).val

theorem kleinParam_add : ∀ v w : Fin 2 → ZMod 2,
    kleinParam (v + w) = kleinParam v * kleinParam w := by
  decide +kernel

theorem kleinParam_zero : kleinParam 0 = 1 := by decide +kernel

theorem kleinParam_eq_one : ∀ w : Fin 2 → ZMod 2, kleinParam w = 1 → w = 0 := by decide +kernel

theorem kleinParam_sign : ∀ w : Fin 2 → ZMod 2, sign (kleinParam w) = 1 := by decide +kernel

theorem tenParam_conj_kleinParam : ∀ (v : Fin 3 → ZMod 3) (w : Fin 2 → ZMod 2),
    ∃ w' : Fin 2 → ZMod 2, tenParam v * kleinParam w * (tenParam v)⁻¹ = kleinParam w' := by
  decide +kernel

@[expose] def tenHom : Multiplicative (Fin 3 → ZMod 3) →* alternatingGroup (Fin 10) where
  toFun v := ⟨tenParam (Multiplicative.toAdd v), tenParam_sign _⟩
  map_one' := Subtype.ext tenParam_zero
  map_mul' v w := Subtype.ext (tenParam_add (Multiplicative.toAdd v) (Multiplicative.toAdd w))

theorem tenHom_injective : Function.Injective tenHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro v hv
  have h : tenParam (Multiplicative.toAdd v) = 1 := congrArg Subtype.val hv
  exact Subgroup.mem_bot.2 (Multiplicative.toAdd.injective (tenParam_eq_one _ h))

@[expose] def kleinHom : Multiplicative (Fin 2 → ZMod 2) →* alternatingGroup (Fin 10) where
  toFun w := ⟨kleinParam (Multiplicative.toAdd w), kleinParam_sign _⟩
  map_one' := Subtype.ext kleinParam_zero
  map_mul' v w := Subtype.ext (kleinParam_add (Multiplicative.toAdd v) (Multiplicative.toAdd w))

theorem kleinHom_injective : Function.Injective kleinHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  have h : kleinParam (Multiplicative.toAdd w) = 1 := congrArg Subtype.val hw
  exact Subgroup.mem_bot.2 (Multiplicative.toAdd.injective (kleinParam_eq_one _ h))

theorem three_le_localRank_alternating {n : ℕ} (hn : 10 ≤ n) :
    3 ≤ localRank 3 (alternatingGroup (Fin n)) := by
  set ι := CFSG.SectionRank.altEmbed hn
  have hι := CFSG.SectionRank.altEmbed_injective hn
  set φ := ι.comp tenHom
  set κ := ι.comp kleinHom
  have hφ : Function.Injective φ := hι.comp tenHom_injective
  have hκ : Function.Injective κ := hι.comp kleinHom_injective
  have hκcard : Nat.card κ.range = 2 ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hκ).toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hφE := CFSG.RankThree.PartTwo.Census.isElemAbelian_range (p := 3) (fun a => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext b
    change 3 • (Multiplicative.toAdd a b) = 0
    generalize Multiplicative.toAdd a b = x
    revert x
    decide) φ
  refine CFSG.RankThree.Theta.le_localRank_of_le_normalizer (q := 3) (by norm_num) (U := κ.range)
    (W := φ.range) ?_ (IsPGroup.of_card hκcard) hφE.1 hφE.2 ?_ ?_
  · intro h
    have h1 : κ (Multiplicative.ofAdd ![1, 0]) ∈ κ.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one κ] at h1
    exact absurd (hκ h1) (by decide)
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  · refine CFSG.RankThree.PartTwo.Census.le_normalizer_of_conj_mem ?_
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    obtain ⟨w', hw'⟩ := tenParam_conj_kleinParam (Multiplicative.toAdd v) (Multiplicative.toAdd w)
    refine ⟨Multiplicative.ofAdd w', ?_⟩
    change ι (kleinHom (Multiplicative.ofAdd w')) = ι (tenHom v) * ι (kleinHom w) * (ι (tenHom v))⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hw'.symm

end CFSG.RankThree.PartTwo.Sec4.Census
