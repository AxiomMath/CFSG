module

public import CFSG.Sporadic.Co2Smith.QEnum
public import CFSG.Sporadic.Co2Smith.SmithCo2

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] noncomputable def qE
    (e : ℕ) : CFSG.pCore 2 Cz :=
  ⟨⟨qElt e, Qsub_le_Cz (qElt_mem e)⟩, mem_pCore_Cz (qElt_mem e)⟩

theorem exists_qE
    (q : CFSG.pCore 2 Cz) : ∃ e < 512, ∃ _n < 1, qE e = q := by
  have hq : ((q : Cz) : K) ∈ Qsub :=
    Subgroup.mem_subgroupOf.mp ((Subgroup.ext_iff.mp pCore_Cz (q : Cz)).mp q.2)
  obtain ⟨e, he, h⟩ := exists_qElt hq
  exact ⟨e, he, 0, Nat.one_pos, Subtype.ext (Subtype.ext h)⟩

theorem qE_injOn
    {e e' : ℕ} (he : e < 512) (he' : e' < 512) (h : qE e = qE e') : e = e' :=
  qElt_injOn he he' (congrArg (fun q : CFSG.pCore 2 Cz => ((q : Cz) : K)) h)

@[expose] noncomputable def ceInv (y : Cz) : ℕ :=
  Nat.card {q : CFSG.pCore 2 Cz // (q : Cz) * y = y * q}

theorem ceInv_conj (h y : Cz) : ceInv (h * y * h⁻¹) = ceInv y := by
  unfold ceInv
  have hn : (CFSG.pCore 2 Cz).Normal := CFSG.pCore_normal
  refine Nat.card_congr
    { toFun := fun q => ⟨⟨h⁻¹ * q * h, by simpa using hn.conj_mem _ q.1.2 h⁻¹⟩, ?_⟩
      invFun := fun q => ⟨⟨h * q * h⁻¹, hn.conj_mem _ q.1.2 h⟩, ?_⟩
      left_inv := fun q => Subtype.ext (Subtype.ext (by simp [mul_assoc]))
      right_inv := fun q => Subtype.ext (Subtype.ext (by simp [mul_assoc])) }
  · have e := q.2
    calc h⁻¹ * (q : Cz) * h * y = h⁻¹ * ((q : Cz) * (h * y * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * y * h⁻¹) * q) * h := by rw [e]
      _ = y * (h⁻¹ * q * h) := by group
  · have e := q.2
    calc h * (q : Cz) * h⁻¹ * (h * y * h⁻¹) = h * ((q : Cz) * y) * h⁻¹ := by group
      _ = h * (y * q) * h⁻¹ := by rw [e]
      _ = h * y * h⁻¹ * (h * q * h⁻¹) := by group

@[expose] noncomputable def invEInv (y : Cz) : ℕ :=
  Nat.card {q : CFSG.pCore 2 Cz // y * q * (y * q) = 1}

theorem invEInv_conj
    (h y : Cz) : invEInv (h * y * h⁻¹) = invEInv y := by
  unfold invEInv
  have hn : (CFSG.pCore 2 Cz).Normal := CFSG.pCore_normal
  refine Nat.card_congr
    { toFun := fun q => ⟨⟨h⁻¹ * q * h, by simpa using hn.conj_mem _ q.1.2 h⁻¹⟩, ?_⟩
      invFun := fun q => ⟨⟨h * q * h⁻¹, hn.conj_mem _ q.1.2 h⟩, ?_⟩
      left_inv := fun q => Subtype.ext (Subtype.ext (by simp [mul_assoc]))
      right_inv := fun q => Subtype.ext (Subtype.ext (by simp [mul_assoc])) }
  · have e := q.2
    calc y * (h⁻¹ * (q : Cz) * h) * (y * (h⁻¹ * q * h)) =
        h⁻¹ * (h * y * h⁻¹ * q * (h * y * h⁻¹ * q)) * h := by group
      _ = 1 := by rw [e]; group
  · have e := q.2
    calc h * y * h⁻¹ * (h * (q : Cz) * h⁻¹) * (h * y * h⁻¹ * (h * q * h⁻¹)) =
        h * (y * q * (y * q)) * h⁻¹ := by group
      _ = 1 := by rw [e]; group

end CFSG.Sporadic.Co2Smith
