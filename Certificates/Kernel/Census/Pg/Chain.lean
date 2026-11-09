module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWData
public import Certificates.Data.Kernel.W16Pg
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Enum.ZCSound
import CFSG.Certificates.Kernel.W16PgSound
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPg

@[expose] def dNil : List (List ℤ) := []

end CertificateChecks.KernelPg

end

#ks_rawchain CertificateChecks.KernelPg.C 128 8 0
  CFSG.EvenSporadicStandard.Fin76b.W16.sgsArr CFSG.EvenSporadicStandard.Fin76b.W16.baseArr 36
  CertificateChecks.KernelPg.dNil
#kmisc_packarrs CertificateChecks.KernelPg.ET CFSG.EvenSporadicStandard.Fin76b.W16.eTab 5

public section

namespace CertificateChecks.KernelPg

open CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
  CFSG.KC.W16Pg

theorem bS : ∀ j < 36, arrBind sgsArr[j]! 128 8 (C.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bE : ∀ a < 32, arrBind eTab[a]! 32 5 (ET a) = true := by
  intro a ha
  interval_cases a <;> quickRfl

theorem perm : allN 36 (fun j => permOK 128 8 (mask 8) (128 * 8) (C.S j) (C.SI j)) = true := by
  quickRfl

theorem bget : ∀ t < 6, baseArr[t]! = pg 8 (mask 8) C.BP t := by decide +kernel

theorem orbProd : ((List.range 6).map fun i => rcnt (C.LR i)).prod = 3317760 := by decide +kernel

theorem table_ok : tableG (mulCK ET) = true := by decide +kernel

theorem gen_ok : genG (mulCK ET) = true := by
  simp only [genG, ← Array.all_toList]
  decide +kernel

end CertificateChecks.KernelPg

end

namespace CertificateChecks.KernelPg

open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw CFSG.KC.W16Pg CFSG.KC.EnumSound

noncomputable def pgcGen (S : Nat → Nat) (BP : Nat) : Bool :=
  (List.range 36).all fun j => (pg 8 (mask 8) (S j) 0 == 0) &&
    (List.range 128).all fun a => (List.range 6).all fun t =>
      pg 8 (mask 8) (S j) (mulCK ET a (pg 8 (mask 8) BP t)) ==
        mulCK ET (pg 8 (mask 8) (S j) a) (pg 8 (mask 8) (S j) (pg 8 (mask 8) BP t))

theorem pgc_gen_ok : pgcGen C.S C.BP = true := by quickRfl

theorem pgc_dA : ∀ i < 8, ∀ j < 8, ∀ k < 8, dMul (dMul i j) k = dMul i (dMul j k) := by
  decide +kernel

theorem pgc_dL : ∀ i < 8, ∀ j < 8, dMul i j < 8 := by decide +kernel

theorem pgc_dZ : ∀ i < 8, dMul i 2 = dMul 2 i := by decide +kernel

theorem pgc_dec : ∀ a < 128, decD a < 8 := by decide +kernel

theorem pgc_eL (a b : Nat) : mulEK ET a b < 32 := pg5_lt _ _

theorem pgc_eT : eT < 32 := by decide

theorem pgc_eA_b : allN 32 (fun a => allN 32 fun b => allN 32 fun c =>
    Nat.beq (mulEK ET (mulEK ET a b) c) (mulEK ET a (mulEK ET b c))) = true := by quickRfl

theorem pgc_eA : ∀ a < 32, ∀ b < 32, ∀ c < 32,
    mulEK ET (mulEK ET a b) c = mulEK ET a (mulEK ET b c) := fun a ha b hb c hc =>
  Nat.eq_of_beq_eq_true (PK.allN_iff.1 (PK.allN_iff.1 (PK.allN_iff.1 pgc_eA_b a ha) b hb) c hc)

theorem pgc_eZ : ∀ k < 32, mulEK ET k eT = mulEK ET eT k := by decide +kernel

theorem pgc_F : ∀ i < 8, ∀ k < 32, ixPK ET (dMul i 2) (mulEK ET k eT) = ixPK ET i k := by
  decide +kernel

theorem pgc_P : ∀ i < 8, ∀ k < 32, (decD (ixPK ET i k) = i ∧ ixPK ET i k % 32 = k) ∨
    (decD (ixPK ET i k) = dMul i 2 ∧ ixPK ET i k % 32 = mulEK ET k eT) := by
  decide +kernel

theorem pgc_key1 {i k j l : Nat} (hi : i < 8) (hk : k < 32) (hj : j < 8) (hl : l < 32) :
    ixPK ET (dMul (decD (ixPK ET i k)) j) (mulEK ET (ixPK ET i k % 32) l) =
      ixPK ET (dMul i j) (mulEK ET k l) := by
  rcases pgc_P i hi k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, pgc_dA i hi 2 (by norm_num) j hj, ← pgc_dZ j hj,
      ← pgc_dA i hi j hj 2 (by norm_num), pgc_eA k hk eT pgc_eT l hl, ← pgc_eZ l hl,
      ← pgc_eA k hk l hl eT pgc_eT]
    exact pgc_F _ (pgc_dL i hi j hj) _ (pgc_eL k l)

theorem pgc_key2 {i k j l : Nat} (hi : i < 8) (hk : k < 32) (hj : j < 8) (hl : l < 32) :
    ixPK ET (dMul j (decD (ixPK ET i k))) (mulEK ET l (ixPK ET i k % 32)) =
      ixPK ET (dMul j i) (mulEK ET l k) := by
  rcases pgc_P i hi k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, ← pgc_dA j hj i hi 2 (by norm_num), ← pgc_eA l hl k hk eT pgc_eT]
    exact pgc_F _ (pgc_dL j hj i hi) _ (pgc_eL l k)

theorem pgc_assoc {a b c : Nat} (ha : a < 128) (hb : b < 128) (hc : c < 128) :
    mulCK ET (mulCK ET a b) c = mulCK ET a (mulCK ET b c) := by
  have h32 : ∀ x : Nat, x % 32 < 32 := fun x => Nat.mod_lt _ (by norm_num)
  unfold mulCK
  rw [pgc_key1 (pgc_dL _ (pgc_dec a ha) _ (pgc_dec b hb)) (pgc_eL _ _) (pgc_dec c hc) (h32 c),
    pgc_key2 (pgc_dL _ (pgc_dec b hb) _ (pgc_dec c hc)) (pgc_eL _ _) (pgc_dec a ha) (h32 a),
    pgc_dA _ (pgc_dec a ha) _ (pgc_dec b hb) _ (pgc_dec c hc),
    pgc_eA _ (h32 a) _ (h32 b) _ (h32 c)]

theorem pgc_hom {m : Nat → Nat → Nat} {σ : Nat → Nat}
    (hlt : ∀ a < 128, ∀ b < 128, m a b < 128)
    (hA : ∀ a < 128, ∀ b < 128, ∀ c < 128, m (m a b) c = m a (m b c))
    (h1 : ∀ a < 128, m a 0 = a) (hs : ∀ a < 128, σ a < 128) (hs0 : σ 0 = 0)
    (hB : ∀ t < 6, baseArr[t]! < 128)
    (hgen : ∀ a < 128, ∀ t < 6, σ (m a baseArr[t]!) = m (σ a) (σ baseArr[t]!))
    (hG : genG m = true) : ∀ a < 128, ∀ c < 128, σ (m a c) = m (σ a) (σ c) := by
  unfold genG at hG
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range, beq_iff_eq] at hG
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h0⟩, hglt⟩, hcov⟩, hpar⟩, -⟩ := hG
  have key : ∀ j, j < 128 → ∀ a < 128, σ (m a genElems[j]!) = m (σ a) (σ genElems[j]!) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj a ha
      rcases j with _ | j'
      · rw [h0, h1 a ha, hs0, h1 (σ a) (hs a ha)]
      · obtain ⟨⟨hp, ht⟩, he⟩ := hpar j' (by omega)
        have hplt : genElems[genPar[j' + 1]!]! < 128 := hglt _ (by omega)
        have hg6 := hB _ ht
        rw [← he, ← hA a ha _ hplt _ hg6, hgen _ (hlt a ha _ hplt) _ ht,
          ih _ hp (by omega) a ha, hA _ (hs a ha) _ (hs _ hplt) _ (hs _ hg6), ← hgen _ hplt _ ht]
  intro a ha c hc
  obtain ⟨j, hj, rfl⟩ := hcov c hc
  exact key j hj a ha

theorem pgc_base : ∀ t < 6, baseArr[t]! < 128 := by decide +kernel

public section

theorem aut_ok : autK ET C.S = true := by
  have ht := table_ok
  unfold tableG at ht
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at ht
  have hlt : ∀ a < 128, ∀ b < 128, mulCK ET a b < 128 := ht.1.1.1.1.1.1
  have h1 : ∀ a < 128, mulCK ET a 0 = a := fun a ha => (ht.1.1.1.1.1.2 a ha).1.1.1.1.2
  have hG := pgc_gen_ok
  unfold pgcGen at hG
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hG
  unfold autK
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  intro j hj
  have hp := PK.allN_iff.1 perm j hj
  obtain ⟨-, -, hpr⟩ := permOK_sound hp
  obtain ⟨g, hg, -⟩ := permOK_perm hp
  obtain ⟨hs0, hgen⟩ := hG j hj
  refine ⟨⟨fun a ha => (hpr a ha).1, fun a ha b hb => ?_⟩, fun a ha => ?_⟩
  · refine pgc_hom (σ := pg 8 (mask 8) (C.S j)) hlt (fun a ha b hb c hc => pgc_assoc ha hb hc) h1
      (fun a ha => (hpr a ha).1) hs0 pgc_base (fun a ha t ht => ?_) gen_ok a ha b hb
    rw [bget t ht]
    exact hgen a ha t ht
  · exact ⟨g⁻¹ ⟨a, ha⟩, (g⁻¹ ⟨a, ha⟩).2,
      (hg _).trans (congrArg Fin.val (g.apply_symm_apply ⟨a, ha⟩))⟩

theorem cand_ok : candG (mulCK ET) = true := by decide +kernel

end

end CertificateChecks.KernelPg
