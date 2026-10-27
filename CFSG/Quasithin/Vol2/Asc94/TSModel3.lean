module

public import CFSG.Quasithin.Vol2.Asc94.TSModel1

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

@[expose] def TQ : Set Hc := {q | q ∈ Qh ∧ q * q = 1 ∧ q ≠ 1 ∧ q ∉ U1 ∧ q ∉ U2}

@[expose] def tz : Hc := mkH !![1, 0, 0, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem cm_tz : cm tz = !![1, 0, 0, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1] := rfl

@[expose] def tabQ : Fin 42 → Matrix (Fin 5) (Fin 5) (ZMod 2) := ![
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 0, 1, 0, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 1, 0, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 1, 0, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 1, 0, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 0, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 0, 1, 1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 0, 1, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 1, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 1, 1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 1, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 1, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 0, 1, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 0, 1, 0, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 1, 0, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 1, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 1, 0, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 1, 0, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 1, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 1, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 1, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 1, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 1, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 0, 1, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 0, 1, 1, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 0, 1, 1, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 1, 1, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 1, 1, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 1, 1, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 1, 1, 1, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]]

@[expose] def tabG : Fin 42 → Matrix (Fin 5) (Fin 5) (ZMod 2) := ![
  !![1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 1, 1, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 1, 1, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 0, 1, 0; 0, 1, 1, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 1, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 1, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 1, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 1, 1, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 1, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 1, 0, 0; 0, 0, 1, 0, 0; 0, 0, 1, 1, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 1, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 1, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 1, 1, 0, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 0, 1, 0; 0, 1, 1, 0, 0; 0, 0, 0, 0, 1],
  !![1, 0, 1, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 1, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 1, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 1, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 1, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 1, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 1, 1, 0; 0, 0, 0, 0, 1],
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 1, 1, 1, 0; 0, 0, 0, 0, 1]]

theorem tabQ_det : ∀ k, (tabQ k).det = 1 := by decide +kernel

theorem tabQ_col : ∀ k i, tabQ k i 0 = (1 : Mt) i 0 := by decide +kernel

theorem tabQ_row : ∀ k j, tabQ k 4 j = (1 : Mt) 4 j := by decide +kernel

theorem tabG_det : ∀ k, (tabG k).det = 1 := by decide +kernel

theorem tabG_col : ∀ k i, tabG k i 0 = (1 : Mt) i 0 := by decide +kernel

theorem tabG_row : ∀ k j, tabG k 4 j = (1 : Mt) 4 j := by decide +kernel

theorem tabG_conj : ∀ k, tabG k * tabQ k =
    !![1, 0, 0, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] * tabG k := by
  decide +kernel

theorem tabQ_inj_dec : ∀ a b : Fin 42, tabQ a = tabQ b → a = b := by decide +kernel

theorem suppIn_iff_pairs {S : Fin 5 → Fin 5 → Prop} {M : Mt} :
    SuppIn S M ↔ ∀ p : Fin 5 × Fin 5, ¬ S p.1 p.2 → M p.1 p.2 = 0 :=
  ⟨fun h p hp => h p.1 p.2 hp, fun h i j hij => h (i, j) hij⟩

theorem tabQ_TQ : ∀ k, (∀ p : Fin 5 × Fin 5, ¬ SQ p.1 p.2 → (tabQ k - 1) p.1 p.2 = 0) ∧
    tabQ k * tabQ k = 1 ∧ tabQ k ≠ 1 ∧
    ¬ (∀ p : Fin 5 × Fin 5, ¬ S1 p.1 p.2 → (tabQ k - 1) p.1 p.2 = 0) ∧
    ¬ (∀ p : Fin 5 × Fin 5, ¬ S2 p.1 p.2 → (tabQ k - 1) p.1 p.2 = 0) := by
  decide +kernel

theorem cover_dec : ∀ p : QPar,
    (1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2) *
      ((1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2)) = 1 →
    (1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2) ≠ 1 →
    ¬ (∀ q : Fin 5 × Fin 5, ¬ S1 q.1 q.2 →
        ((1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2) - 1) q.1 q.2 = 0) →
    ¬ (∀ q : Fin 5 × Fin 5, ¬ S2 q.1 q.2 →
        ((1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2) - 1) q.1 q.2 = 0) →
    ∃ k, (1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2) = tabQ k := by
  decide +kernel

theorem TQ_cover {q : Hc} (hq : q ∈ TQ) : ∃ k, cm q = tabQ k := by
  obtain ⟨hqQ, hqsq, hq1, hqU1, hqU2⟩ := hq
  obtain ⟨p, hp⟩ := Fq_bij.2 ⟨q, hqQ⟩
  have hpq : phiQ p = q := congrArg Subtype.val hp
  have hcm : cm q = (1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2) := by
    rw [← hpq, cm_phiQ]
  have hM : (1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2) *
      ((1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2)) = 1 := by
    rw [← hcm, ← cm_mul, hqsq, cm_one]
  have hne : (1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2) ≠ 1 := fun h =>
    hq1 (Subtype.ext (Subtype.ext (hcm.trans h)))
  have hU1' : ¬ (∀ q : Fin 5 × Fin 5, ¬ S1 q.1 q.2 →
      ((1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2) - 1) q.1 q.2 = 0) := fun h =>
    hqU1 ((mem_patSub hS1).2 (by rw [hcm]; exact suppIn_iff_pairs.2 h))
  have hU2' : ¬ (∀ q : Fin 5 × Fin 5, ¬ S2 q.1 q.2 →
      ((1 + NuP p.1 p.2.1 p.2.2) * (1 + NtP p.2.2) - 1) q.1 q.2 = 0) := fun h =>
    hqU2 ((mem_patSub hS2).2 (by rw [hcm]; exact suppIn_iff_pairs.2 h))
  obtain ⟨k, hk⟩ := cover_dec p hM hne hU1' hU2'
  exact ⟨k, hcm.trans hk⟩

theorem cm_injective : Function.Injective cm := fun _ _ h => Subtype.ext (Subtype.ext h)

theorem mem_TQ_of_cm {q : Hc} (h1 : SuppIn SQ (cm q - 1)) (h2 : cm q * cm q = 1)
    (h3 : cm q ≠ 1) (h4 : ¬ SuppIn S1 (cm q - 1)) (h5 : ¬ SuppIn S2 (cm q - 1)) : q ∈ TQ := by
  show q ∈ Qh ∧ q * q = 1 ∧ q ≠ 1 ∧ q ∉ U1 ∧ q ∉ U2
  refine ⟨(mem_Qh_iff q).2 h1, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    show cm (q * q) = cm 1
    rw [cm_mul, cm_one]
    exact h2
  · intro h
    exact h3 (by rw [h, cm_one])
  · intro h
    exact h4 ((mem_patSub hS1).1 h)
  · intro h
    exact h5 ((mem_patSub hS2).1 h)

theorem TQ_conj_tz {q : Hc} (hq : q ∈ TQ) : ∃ g : Hc, q = g⁻¹ * tz * g := by
  obtain ⟨k, hk⟩ := TQ_cover hq
  obtain ⟨g, hgM⟩ : ∃ g : Hc, cm g = tabG k :=
    ⟨mkH (tabG k) (tabG_det k) (tabG_col k) (tabG_row k), rfl⟩
  have hgq : g * q = tz * g := by
    apply Subtype.ext
    apply Subtype.ext
    show cm (g * q) = cm (tz * g)
    rw [cm_mul, cm_mul, hgM, hk, cm_tz]
    exact tabG_conj k
  refine ⟨g, ?_⟩
  calc q = g⁻¹ * (g * q) := (inv_mul_cancel_left g q).symm
    _ = g⁻¹ * (tz * g) := by rw [hgq]
    _ = g⁻¹ * tz * g := (mul_assoc _ _ _).symm

theorem tz_mem_TQ : tz ∈ TQ := by
  show tz ∈ Qh ∧ tz * tz = 1 ∧ tz ≠ 1 ∧ tz ∉ U1 ∧ tz ∉ U2
  refine ⟨(mem_Qh_iff tz).2 ?_, ?_, ?_, ?_, ?_⟩
  · rw [cm_tz]
    exact suppIn_iff_pairs.2 (by decide +kernel)
  · apply Subtype.ext
    apply Subtype.ext
    show cm (tz * tz) = cm 1
    rw [cm_mul, cm_one, cm_tz]
    decide +kernel
  · intro h
    have h' := congrArg cm h
    rw [cm_one, cm_tz] at h'
    exact absurd h' (by decide +kernel)
  · intro h
    have h' := (mem_patSub hS1).1 h
    rw [cm_tz] at h'
    exact absurd (h' 1 4 (by decide)) (by decide +kernel)
  · intro h
    have h' := (mem_patSub hS2).1 h
    rw [cm_tz] at h'
    exact absurd (h' 0 3 (by decide)) (by decide +kernel)

theorem tabQ_mem (k : Fin 42) : tabQ k ∈ cm '' TQ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := tabQ_TQ k
  refine ⟨mkH (tabQ k) (tabQ_det k) (tabQ_col k) (tabQ_row k), ?_, cm_mkH _ _ _ _⟩
  refine mem_TQ_of_cm ?_ ?_ ?_ ?_ ?_
  · rw [cm_mkH]; exact suppIn_iff_pairs.2 h1
  · rw [cm_mkH]; exact h2
  · rw [cm_mkH]; exact h3
  · rw [cm_mkH]; exact fun h => h4 (suppIn_iff_pairs.1 h)
  · rw [cm_mkH]; exact fun h => h5 (suppIn_iff_pairs.1 h)

theorem cm_image_TQ : cm '' TQ = Set.range tabQ := by
  ext M
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨k, hk⟩ := TQ_cover hq
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    exact tabQ_mem k

theorem tabQ_inj : Function.Injective tabQ := fun a b h => tabQ_inj_dec a b h

theorem ncard_TQ : TQ.ncard = 42 := by
  rw [← Set.ncard_image_of_injective TQ cm_injective, cm_image_TQ,
    Set.ncard_range_of_injective tabQ_inj, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem tz_cent_aux (X : Mt) (hdet : X.det = 1) (hc : ∀ i : Fin 5, X i 0 = (1 : Mt) i 0)
    (hr : ∀ j : Fin 5, X 4 j = (1 : Mt) 4 j) (e21 : X 2 1 = 0) (e31 : X 3 1 = 0)
    (e32 : X 3 2 = 0) (e33 : X 3 3 = 1) (e11 : X 1 1 = 1) :
    ∀ i j : Fin 5, j ≤ i → X i j = (1 : Mt) i j := by
  have hlow : ∀ i j : Fin 5, j < i → X i j = 0 := by
    intro i j hji
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hji (by decide)
      | simp [hc, hr, e21, e31, e32, Matrix.one_apply]
  have hd := Matrix.det_of_isUpperTriangular (M := X) (by
    intro i j hji
    exact hlow i j hji)
  have h00 : X 0 0 = 1 := by rw [hc 0, Matrix.one_apply_eq]
  have h44 : X 4 4 = 1 := by rw [hr 4, Matrix.one_apply_eq]
  have h22 : X 2 2 = 1 := by
    rw [hdet, Fin.prod_univ_five, h00, e11, e33, h44] at hd
    simpa using hd.symm
  have hdiag : ∀ i : Fin 5, X i i = 1 := by
    intro i
    fin_cases i <;> simp [h00, e11, h22, e33, h44]
  intro i j hji
  rcases hji.lt_or_eq with hlt | rfl
  · rw [hlow i j hlt, Matrix.one_apply_ne (ne_of_gt hlt)]
  · rw [hdiag _, Matrix.one_apply_eq]

theorem tz_cent_le_Tm : ∀ h : Hc, h * tz = tz * h → h ∈ Tm := by
  intro h hc
  have hm : cm h * cm tz = cm tz * cm h := by
    rw [← cm_mul, ← cm_mul, hc]
  rw [cm_tz] at hm
  have hc0 := cm_col0 h
  have hr4 := cm_row4 h
  have h00 : cm h 0 0 = 1 := by rw [hc0 0, Matrix.one_apply_eq]
  have h44 : cm h 4 4 = 1 := by rw [hr4 4, Matrix.one_apply_eq]
  have e21 : cm h 2 1 = 0 := by
    have e := congrFun (congrFun hm 2) 4
    simp [Matrix.mul_apply, Fin.sum_univ_five] at e
    linear_combination e
  have e31 : cm h 3 1 = 0 := by
    have e := congrFun (congrFun hm 3) 4
    simp [Matrix.mul_apply, Fin.sum_univ_five] at e
    linear_combination e
  have e32 : cm h 3 2 = 0 := by
    have e := congrFun (congrFun hm 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_five] at e
    linear_combination e
  have e33 : cm h 3 3 = 1 := by
    have e := congrFun (congrFun hm 0) 3
    simp [Matrix.mul_apply, Fin.sum_univ_five] at e
    linear_combination -e + h00
  have e11 : cm h 1 1 = 1 := by
    have e := congrFun (congrFun hm 1) 4
    simp [Matrix.mul_apply, Fin.sum_univ_five] at e
    linear_combination e + h44
  have hdet : (cm h).det = 1 := h.1.2
  have hA := tz_cent_aux (cm h) hdet hc0 hr4 e21 e31 e32 e33 e11
  rw [mem_Tm]
  intro i j hij
  rw [Matrix.sub_apply, hA i j (not_lt.1 hij), sub_self]

end CFSG.Quasithin.A94.L52
