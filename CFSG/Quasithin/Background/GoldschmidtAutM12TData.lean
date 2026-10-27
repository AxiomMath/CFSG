module

public import CFSG.Quasithin.Background.GoldschmidtAutM12Core
public import CFSG.Quasithin.Recognition.M12AmalAutJFacts
public import CFSG.Quasithin.Recognition.M12AmalAutFeit
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Open CFSG.Quasithin.M12AmalAut

namespace AutM12Recog

@[expose] def powIdx (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => telMul (powIdx i m) i

theorem powIdx_lt {i : ℕ} (hi : i < 128) (m : ℕ) : powIdx i m < 128 := by
  induction m with
  | zero => show 0 < 128; norm_num
  | succ m ih => exact (telMul_chk _ ih i hi).1

theorem telG_pow' {i : ℕ} (hi : i < 128) (m : ℕ) : telG i ^ m = telG (powIdx i m) := by
  induction m with
  | zero => rw [pow_zero]; exact telG_zero_idx.symm
  | succ m ih => rw [pow_succ, ih, telG_mul (powIdx_lt hi m) hi]; rfl

theorem tel_exp8 : ∀ i < 128, powIdx i 8 = 0 := by decide +kernel

theorem exp_autT (x : ↥autData.T) : x ^ 8 = 1 := by
  obtain ⟨i, hi, hx⟩ := exists_idx_of_mem_T x.2
  apply Subtype.ext
  show (x : AutG) ^ 8 = 1
  rw [hx, telG_pow' hi, tel_exp8 i hi]
  exact telG_zero_idx

theorem isElemAbelian_map_subtype (B : Subgroup ↥autData.T)
    (hB : CFSG.Assembly.IsElemAbelian 2 B) :
    CFSG.Open.IsElemAbelian 2 (B.map autData.T.subtype) := CFSG.Open.IsElemAbelian.map hB _

theorem elemAbelian_autT (B : Subgroup ↥autData.T) (hB : CFSG.Assembly.IsElemAbelian 2 B) :
    Nat.card B ≤ 16 ∧ (Nat.card B = 16 → B.map autData.T.subtype = Esub) := by
  have hB'le : B.map autData.T.subtype ≤ autData.T := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcard : Nat.card (B.map autData.T.subtype) = Nat.card B :=
    (Nat.card_congr (B.equivMapOfInjective _ autData.T.subtype_injective).toEquiv).symm
  obtain ⟨X, hXfam, hX⟩ := elemAbelian_mem_fam _ _ hB'le (isElemAbelian_map_subtype B hB) rfl
  obtain ⟨hlen, hX16, hnd, hlt, -⟩ := famTab_bound_chk X hXfam
  have hc := card_of_idx hnd hlt hX
  refine ⟨by rw [← hcard, hc]; exact hlen, fun h16 => ?_⟩
  have hXe : X = eIdx := hX16 (by rw [← hc, hcard, h16])
  ext g
  rw [hX g, hXe]
  exact Iff.rfl

theorem tProps_autT : TProps ↥autData.T where
  card := by rw [aut_card_T]; norm_num
  exp := exp_autT
  rank := fun B hB => (elemAbelian_autT B hB).1
  uniq := fun B B' hB hB' hc hc' => by
    have h1 := (elemAbelian_autT B hB).2 hc
    have h2 := (elemAbelian_autT B' hB').2 hc'
    exact Subgroup.map_injective autData.T.subtype_injective (h1.trans h2.symm)
  hasE16 := by
    refine ⟨Esub.subgroupOf autData.T, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
    · rintro ⟨⟨a, ha⟩, ha'⟩ ⟨⟨b, hb⟩, hb'⟩
      apply Subtype.ext
      apply Subtype.ext
      show a * b = b * a
      exact congrArg Subtype.val (Esub_elem.1.is_comm.comm ⟨a, ha'⟩ ⟨b, hb'⟩)
    · rintro ⟨a, ha⟩ ha'
      apply Subtype.ext
      exact Esub_elem.2 a ha'
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Esub_le_T).toEquiv]
      exact card_Esub

variable {D : Type} [Group D]

theorem exists_sylow_autT
    {G₁ G₂ : Subgroup D} (h : IsGoldschmidtTriple G₁ G₂)
    (ho : IsGoldCaseAutM12Cat G₁ G₂) :
    ∃ S : Sylow 2 D, Nonempty (↥(S : Subgroup D) ≃* ↥autData.T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨W, _, _, K₁, K₂, hW, ⟨-, -, -, S, hSK⟩, φ₁, φ₂, hag₁, hag₂⟩, -⟩ := ho
  obtain ⟨eW⟩ := hW
  obtain ⟨m⟩ := autM12PermModel
  let ε : W ≃* AutG := eW.trans m.symm
  have eT : ↥(G₁ ⊓ G₂) ≃* ↥(S : Subgroup W) :=
    (infMulEquivOfAmalgamIso φ₁ φ₂ hag₁ hag₂).trans (MulEquiv.subgroupCongr hSK.symm)
  obtain ⟨S', ⟨ι⟩⟩ := exists_sylow_mulEquiv ε S
  have ι' : ↥(S' : Subgroup AutG) ≃* ↥autData.T :=
    Sylow.equiv S' (aut_syl.1.toSylow aut_syl.2)
  obtain ⟨T₀, hT₀⟩ := h.sylow
  exact ⟨T₀, ⟨(MulEquiv.subgroupCongr hT₀).trans (eT.trans (ι.trans ι'))⟩⟩

end AutM12Recog

end CFSG.Quasithin.F6
