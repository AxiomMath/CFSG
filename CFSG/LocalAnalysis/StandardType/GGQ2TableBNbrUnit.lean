module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU
import CFSG.LocalAnalysis.StandardType.GGQ2CensusChainA
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module
open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private theorem tbnu_mem_closure_adjacent {N n : ℕ} {s : Fin (n + 1) ↪o Fin N}
    {L : Type} [Group L] (F : Equiv.Perm (Fin N) →* L) (p q : Fin (n + 1)) :
    F (Equiv.swap (s p) (s q)) ∈
      Subgroup.closure (Set.range fun i : Fin n => F (Equiv.swap (s i.castSucc) (s i.succ))) := by
  let H := Subgroup.closure (Set.range fun i : Fin n => F (Equiv.swap (s i.castSucc) (s i.succ)))
  have hgen : ∀ i : Fin n, F (Equiv.swap (s i.castSucc) (s i.succ)) ∈ H :=
    fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have key : ∀ d : ℕ, ∀ p q : Fin (n + 1), p ≤ q → (q : ℕ) - (p : ℕ) = d →
      F (Equiv.swap (s p) (s q)) ∈ H := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro p q hpq hd
      rcases lt_or_eq_of_le hpq with hlt | heq
      · by_cases hadj : (q : ℕ) = (p : ℕ) + 1
        ·
          have hp : (p : ℕ) < n := by
            have hq : (q : ℕ) < n + 1 := q.isLt
            omega
          let i : Fin n := ⟨(p : ℕ), hp⟩
          have hsi : s i.castSucc = s p := by congr 1
          have hsj : s i.succ = s q := by
            congr 1
            exact Fin.ext (by simp [i, hadj])
          rw [← hsi, ← hsj]
          exact hgen i
        ·
          let r : Fin (n + 1) := ⟨(q : ℕ) - 1, by have := q.isLt; omega⟩
          have hrv : (r : ℕ) = (q : ℕ) - 1 := rfl
          have hpr : p ≤ r := by
            rw [Fin.le_def]
            simp only [hrv]
            omega
          have hprne : p ≠ r := by
            intro h
            have h' : (p : ℕ) = (r : ℕ) := by rw [h]
            rw [hrv] at h'
            omega
          have hrq : r < q := by
            rw [Fin.lt_def]
            simp only [hrv]
            omega
          have h1 : F (Equiv.swap (s r) (s q)) ∈ H := by
            refine ih 1 (by omega) r q (le_of_lt hrq) ?_
            rw [hrv]
            omega
          have h2 : F (Equiv.swap (s p) (s r)) ∈ H := by
            refine ih ((r : ℕ) - (p : ℕ)) ?_ p r hpr rfl
            rw [hrv]
            omega
          have hxy : s p ≠ s r := fun h => hprne (s.injective h)
          have hxz : s p ≠ s q := fun h => ne_of_lt hlt (s.injective h)
          have hswap : Equiv.swap (s p) (s q) =
              Equiv.swap (s r) (s q) * Equiv.swap (s p) (s r) * Equiv.swap (s r) (s q) := by
            rw [Equiv.swap_mul_swap_mul_swap hxy hxz, Equiv.swap_comm]
          rw [hswap, map_mul, map_mul]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h1
      · subst heq
        rw [Equiv.swap_self, show F (Equiv.refl (Fin N)) = 1 from map_one F]
        exact H.one_mem
  rcases le_total p q with hpq | hqp
  · exact key _ p q hpq rfl
  · rw [Equiv.swap_comm]
    exact key _ q p hqp rfl

private theorem tbnu_castSucc_inj {N n : ℕ} {s : Fin (n + 1) ↪o Fin N} {p q : Fin n} :
    s (p.castSucc) = s (q.castSucc) ↔ p = q := by
  constructor
  · intro h
    have h' : (p.castSucc : ℕ) = (q.castSucc : ℕ) := congrArg Fin.val (s.injective h)
    exact Fin.ext (by simpa using h')
  · rintro rfl
    rfl

private theorem tbnu_castSucc_eq_succ {N n : ℕ} {s : Fin (n + 1) ↪o Fin N} {p q : Fin n} :
    s (p.castSucc) = s (q.succ) ↔ (q : ℕ) + 1 = (p : ℕ) := by
  constructor
  · intro h
    have h' : (p.castSucc : ℕ) = (q.succ : ℕ) := congrArg Fin.val (s.injective h)
    simp only [Fin.val_castSucc, Fin.val_succ] at h'
    omega
  · intro h
    exact congrArg s (Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))

private theorem tbnu_succ_eq_castSucc {N n : ℕ} {s : Fin (n + 1) ↪o Fin N} {p q : Fin n} :
    s (p.succ) = s (q.castSucc) ↔ (p : ℕ) + 1 = (q : ℕ) := by
  constructor
  · intro h
    have h' : (p.succ : ℕ) = (q.castSucc : ℕ) := congrArg Fin.val (s.injective h)
    simp only [Fin.val_castSucc, Fin.val_succ] at h'
    omega
  · intro h
    exact congrArg s (Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))

private theorem tbnu_pairingQ {N n : ℕ} {s : Fin (n + 1) ↪o Fin N} (i j : Fin n) :
    UnitRaw.diffFun N (s i.castSucc) (s i.succ)
      ((UnitRaw.oneLine N).mkQ
        (Pi.single (s j.castSucc) (1 : ZMod 3) - Pi.single (s j.succ) 1)) =
      (CartanMatrix.A n i j : ZMod 3) := by
  rw [UnitRaw.diffFun_mk]
  simp only [Pi.sub_apply, Pi.single_apply]
  by_cases hij : i = j
  · subst hij
    have h1 : ¬ (s i.castSucc = s i.succ) := by
      intro h
      have h' : (i.castSucc : ℕ) = (i.succ : ℕ) := congrArg Fin.val (s.injective h)
      simp only [Fin.val_castSucc, Fin.val_succ] at h'
      omega
    have h2 : ¬ (s i.succ = s i.castSucc) := fun h => h1 h.symm
    have hc : CartanMatrix.A n i i = 2 := by simp [CartanMatrix.A]
    rw [hc, if_pos rfl, if_neg h1, if_neg h2, if_pos rfl]
    norm_num
  · by_cases h1 : (i : ℕ) + 1 = (j : ℕ)
    · have hsc : s i.succ = s j.castSucc := (tbnu_succ_eq_castSucc).mpr h1
      have hcc : ¬ (s i.castSucc = s j.castSucc) := fun h => hij ((tbnu_castSucc_inj).mp h)
      have hcs : ¬ (s i.castSucc = s j.succ) := by
        intro h
        have h' := (tbnu_castSucc_eq_succ).mp h
        omega
      have hss : ¬ (s i.succ = s j.succ) := by
        intro h
        have h' : (i.succ : ℕ) = (j.succ : ℕ) := congrArg Fin.val (s.injective h)
        simp only [Fin.val_succ] at h'
        omega
      have hc : CartanMatrix.A n i j = -1 := by
        simp [CartanMatrix.A, hij, h1]
      rw [hc, if_neg hcc, if_neg hcs, if_pos hsc, if_neg hss]
      norm_num
    · by_cases h2 : (j : ℕ) + 1 = (i : ℕ)
      · have hcs : s i.castSucc = s j.succ := (tbnu_castSucc_eq_succ).mpr h2
        have hcc : ¬ (s i.castSucc = s j.castSucc) := fun h => hij ((tbnu_castSucc_inj).mp h)
        have hsc : ¬ (s i.succ = s j.castSucc) := by
          intro h
          have h' := (tbnu_succ_eq_castSucc).mp h
          omega
        have hss : ¬ (s i.succ = s j.succ) := by
          intro h
          have h' : (i.succ : ℕ) = (j.succ : ℕ) := congrArg Fin.val (s.injective h)
          simp only [Fin.val_succ] at h'
          omega
        have hc : CartanMatrix.A n i j = -1 := by
          simp [CartanMatrix.A, hij, h2]
        rw [hc, if_neg hcc, if_pos hcs, if_neg hsc, if_neg hss]
        norm_num
      · have hcc : ¬ (s i.castSucc = s j.castSucc) := fun h => hij ((tbnu_castSucc_inj).mp h)
        have hcs : ¬ (s i.castSucc = s j.succ) := by
          intro h
          have h' := (tbnu_castSucc_eq_succ).mp h
          omega
        have hsc : ¬ (s i.succ = s j.castSucc) := by
          intro h
          have h' := (tbnu_succ_eq_castSucc).mp h
          omega
        have hss : ¬ (s i.succ = s j.succ) := by
          intro h
          have h' : (i.succ : ℕ) = (j.succ : ℕ) := congrArg Fin.val (s.injective h)
          simp only [Fin.val_succ] at h'
          omega
        have hc : CartanMatrix.A n i j = 0 := by
          simp [CartanMatrix.A, hij, h1, h2]
        rw [hc, if_neg hcc, if_neg hcs, if_neg hsc, if_neg hss]
        norm_num

private theorem tbnu_swap_apply_sub {N : ℕ} {x y : Fin N} (hxy : x ≠ y) (w : UnitRaw.W N) :
    (fun k => w (Equiv.swap x y k)) =
      w - (w x - w y) • (Pi.single x (1 : ZMod 3) - Pi.single y 1) := by
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
  by_cases hx : k = x
  · subst hx
    rw [Equiv.swap_apply_left]
    simp [hxy]
  · by_cases hy : k = y
    · subst hy
      rw [Equiv.swap_apply_right]
      simp [Ne.symm hxy]
    · rw [Equiv.swap_apply_def]
      simp [hx, hy]

private theorem tbnu_refl_applyQ {N n : ℕ} {s : Fin (n + 1) ↪o Fin N} (i : Fin n)
    (v : UnitRaw.Vfull N) :
    UnitRaw.permEquivQ N (Equiv.swap (s i.castSucc) (s i.succ)) v =
      v - UnitRaw.diffFun N (s i.castSucc) (s i.succ) v •
        (UnitRaw.oneLine N).mkQ
          (Pi.single (s i.castSucc) (1 : ZMod 3) - Pi.single (s i.succ) 1) := by
  have hxy : s i.castSucc ≠ s i.succ := by
    intro h
    have h' : (i.castSucc : ℕ) = (i.succ : ℕ) := congrArg Fin.val (s.injective h)
    simp only [Fin.val_castSucc, Fin.val_succ] at h'
    omega
  induction v using Submodule.Quotient.induction_on with
  | H w =>
    change UnitRaw.permEquivQ N (Equiv.swap (s i.castSucc) (s i.succ))
        ((UnitRaw.oneLine N).mkQ w) =
      (UnitRaw.oneLine N).mkQ w -
        UnitRaw.diffFun N (s i.castSucc) (s i.succ) ((UnitRaw.oneLine N).mkQ w) •
          (UnitRaw.oneLine N).mkQ
            (Pi.single (s i.castSucc) (1 : ZMod 3) - Pi.single (s i.succ) 1)
    rw [UnitRaw.permEquivQ_mk, Equiv.symm_swap, UnitRaw.diffFun_mk, tbnu_swap_apply_sub hxy w,
      map_sub, map_smul]

private theorem tbnu_refl_applyH {N n : ℕ} {s : Fin (n + 1) ↪o Fin N} (i : Fin n)
    (v : ↥(UnitRaw.heart N)) :
    UnitRaw.permEquivH N (Equiv.swap (s i.castSucc) (s i.succ)) v =
      v - UnitRaw.diffFun N (s i.castSucc) (s i.succ) (v : UnitRaw.Vfull N) •
        (⟨(UnitRaw.oneLine N).mkQ
            (Pi.single (s i.castSucc) (1 : ZMod 3) - Pi.single (s i.succ) 1),
          UnitRaw.mkQ_single_sub_single_mem_heart N _ _⟩ : ↥(UnitRaw.heart N)) := by
  apply Subtype.ext
  rw [UnitRaw.coe_permEquivH, Submodule.coe_sub, Submodule.coe_smul]
  exact tbnu_refl_applyQ i (v : UnitRaw.Vfull N)

private theorem tbnu_ker_iffQ {N n : ℕ} {S : Finset (Fin N)} {s : Fin (n + 1) ↪o Fin N}
    (hrange : Set.range s = (S : Set (Fin N))) (v : UnitRaw.Vfull N) :
    (∀ i : Fin n, UnitRaw.diffFun N (s i.castSucc) (s i.succ) v = 0) ↔
      v ∈ UnitRaw.cent S := by
  constructor
  · intro h
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (UnitRaw.oneLine N) v
    have hadj : ∀ i : Fin n, w (s i.castSucc) = w (s i.succ) := by
      intro i
      have hi := h i
      rw [UnitRaw.diffFun_mk] at hi
      exact sub_eq_zero.mp hi
    have hchain : ∀ q : Fin (n + 1), w (s q) = w (s 0) := by
      intro q
      induction q using Fin.induction with
      | zero => rfl
      | succ i ih =>
        rw [← hadj i]
        exact ih
    rw [UnitRaw.mem_cent_iff]
    refine ⟨w, rfl, ?_⟩
    intro x hx y hy
    obtain ⟨p, hp⟩ : ∃ p : Fin (n + 1), s p = x := by
      have hx' : x ∈ Set.range s := by rw [hrange]; exact hx
      exact hx'
    obtain ⟨q, hq⟩ : ∃ q : Fin (n + 1), s q = y := by
      have hy' : y ∈ Set.range s := by rw [hrange]; exact hy
      exact hy'
    rw [← hp, ← hq, hchain p, hchain q]
  · intro hv i
    rw [UnitRaw.mem_cent_iff] at hv
    obtain ⟨w, hw, hconst⟩ := hv
    have h : w (s i.castSucc) = w (s i.succ) := hconst _ (by
      exact Finset.mem_coe.mp (by rw [← hrange]; exact Set.mem_range_self _)) _ (by
      exact Finset.mem_coe.mp (by rw [← hrange]; exact Set.mem_range_self _))
    rw [← hw, UnitRaw.diffFun_mk]
    exact sub_eq_zero.mpr h

private theorem tbnu_ker_iffH {N n : ℕ} {S : Finset (Fin N)} {s : Fin (n + 1) ↪o Fin N}
    (hrange : Set.range s = (S : Set (Fin N))) (v : ↥(UnitRaw.heart N)) :
    (∀ i : Fin n, UnitRaw.diffFun N (s i.castSucc) (s i.succ) (v : UnitRaw.Vfull N) = 0) ↔
      v ∈ UnitRaw.centH S :=
  tbnu_ker_iffQ hrange (v : UnitRaw.Vfull N)

private theorem tbnu_closureQ (N : ℕ) (S : Finset (Fin N)) {n : ℕ}
    (s : Fin (n + 1) ↪o Fin N) (hrange : Set.range s = (S : Set (Fin N))) :
    Subgroup.closure (Set.range fun i : Fin n =>
      UnitRaw.permEquivQ N (Equiv.swap (s i.castSucc) (s i.succ))) =
      UnitRaw.normalizerOf S := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro T ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨s i.castSucc, by
        exact Finset.mem_coe.mp (by rw [← hrange]; exact Set.mem_range_self _), s i.succ, by
        exact Finset.mem_coe.mp (by rw [← hrange]; exact Set.mem_range_self _), rfl⟩
  · change Subgroup.closure
        {T | ∃ i ∈ S, ∃ j ∈ S, T = UnitRaw.permEquivQ N (Equiv.swap i j)} ≤
      Subgroup.closure (Set.range fun i : Fin n =>
        UnitRaw.permEquivQ N (Equiv.swap (s i.castSucc) (s i.succ)))
    rw [Subgroup.closure_le]
    rintro T ⟨i, hi, j, hj, rfl⟩
    obtain ⟨p, rfl⟩ : ∃ p, s p = i := by
      have hi' : i ∈ Set.range s := by rw [hrange]; exact hi
      exact hi'
    obtain ⟨q, rfl⟩ : ∃ q, s q = j := by
      have hj' : j ∈ Set.range s := by rw [hrange]; exact hj
      exact hj'
    exact tbnu_mem_closure_adjacent (UnitRaw.permHomQ N) p q

private theorem tbnu_closureH (N : ℕ) (S : Finset (Fin N)) {n : ℕ}
    (s : Fin (n + 1) ↪o Fin N) (hrange : Set.range s = (S : Set (Fin N))) :
    Subgroup.closure (Set.range fun i : Fin n =>
      UnitRaw.permEquivH N (Equiv.swap (s i.castSucc) (s i.succ))) =
      UnitRaw.normalizerOfH S := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro T ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨s i.castSucc, by
        exact Finset.mem_coe.mp (by rw [← hrange]; exact Set.mem_range_self _), s i.succ, by
        exact Finset.mem_coe.mp (by rw [← hrange]; exact Set.mem_range_self _), rfl⟩
  · change Subgroup.closure
        {T | ∃ i ∈ S, ∃ j ∈ S, T = UnitRaw.permEquivH N (Equiv.swap i j)} ≤
      Subgroup.closure (Set.range fun i : Fin n =>
        UnitRaw.permEquivH N (Equiv.swap (s i.castSucc) (s i.succ)))
    rw [Subgroup.closure_le]
    rintro T ⟨i, hi, j, hj, rfl⟩
    obtain ⟨p, rfl⟩ : ∃ p, s p = i := by
      have hi' : i ∈ Set.range s := by rw [hrange]; exact hi
      exact hi'
    obtain ⟨q, rfl⟩ : ∃ q, s q = j := by
      have hj' : j ∈ Set.range s := by rw [hrange]; exact hj
      exact hj'
    exact tbnu_mem_closure_adjacent (UnitRaw.permHomH N) p q

private noncomputable def tbnu_corootFull (N n : ℕ) (s : Fin (n + 1) ↪o Fin N) :
    Fin n → UnitRaw.Vfull N :=
  fun i => (UnitRaw.oneLine N).mkQ
    (Pi.single (s i.castSucc) (1 : ZMod 3) - Pi.single (s i.succ) 1)

private noncomputable def tbnu_rootFull (N n : ℕ) (s : Fin (n + 1) ↪o Fin N) :
    Fin n → Module.Dual (ZMod 3) (UnitRaw.Vfull N) :=
  fun i => UnitRaw.diffFun N (s i.castSucc) (s i.succ)

private noncomputable def tbnu_reflFull (N n : ℕ) (s : Fin (n + 1) ↪o Fin N) :
    Fin n → (UnitRaw.Vfull N ≃ₗ[ZMod 3] UnitRaw.Vfull N) :=
  fun i => UnitRaw.permEquivQ N (Equiv.swap (s i.castSucc) (s i.succ))

private noncomputable def tbnu_corootHeart (N n : ℕ) (s : Fin (n + 1) ↪o Fin N) :
    Fin n → ↥(UnitRaw.heart N) :=
  fun i => ⟨(UnitRaw.oneLine N).mkQ
      (Pi.single (s i.castSucc) (1 : ZMod 3) - Pi.single (s i.succ) 1),
    UnitRaw.mkQ_single_sub_single_mem_heart N _ _⟩

private noncomputable def tbnu_rootHeart (N n : ℕ) (s : Fin (n + 1) ↪o Fin N) :
    Fin n → Module.Dual (ZMod 3) (↥(UnitRaw.heart N)) :=
  fun i => (UnitRaw.diffFun N (s i.castSucc) (s i.succ)).comp (UnitRaw.heart N).subtype

private noncomputable def tbnu_reflHeart (N n : ℕ) (s : Fin (n + 1) ↪o Fin N) :
    Fin n → (↥(UnitRaw.heart N) ≃ₗ[ZMod 3] ↥(UnitRaw.heart N)) :=
  fun i => UnitRaw.permEquivH N (Equiv.swap (s i.castSucc) (s i.succ))

private theorem tbnu_pairingFull {N n : ℕ} {s : Fin (n + 1) ↪o Fin N} (i j : Fin n) :
    tbnu_rootFull N n s i (tbnu_corootFull N n s j) =
      (CartanMatrix.A n i j : ZMod 3) := by
  unfold tbnu_rootFull tbnu_corootFull
  exact tbnu_pairingQ i j

private theorem tbnu_pairingHeart {N n : ℕ} {s : Fin (n + 1) ↪o Fin N} (i j : Fin n) :
    tbnu_rootHeart N n s i (tbnu_corootHeart N n s j) =
      (CartanMatrix.A n i j : ZMod 3) := by
  unfold tbnu_rootHeart tbnu_corootHeart
  exact tbnu_pairingQ i j

private theorem tbnu_refl_applyFull {N n : ℕ} {s : Fin (n + 1) ↪o Fin N} (i : Fin n)
    (v : UnitRaw.Vfull N) :
    tbnu_reflFull N n s i v = v - tbnu_rootFull N n s i v • tbnu_corootFull N n s i := by
  unfold tbnu_reflFull tbnu_rootFull tbnu_corootFull
  exact tbnu_refl_applyQ i v

private theorem tbnu_refl_applyHeart {N n : ℕ} {s : Fin (n + 1) ↪o Fin N} (i : Fin n)
    (v : ↥(UnitRaw.heart N)) :
    tbnu_reflHeart N n s i v = v - tbnu_rootHeart N n s i v • tbnu_corootHeart N n s i := by
  unfold tbnu_reflHeart tbnu_rootHeart tbnu_corootHeart
  exact tbnu_refl_applyH i v

private theorem tbnu_closureFull (N : ℕ) (S : Finset (Fin N)) {n : ℕ}
    (s : Fin (n + 1) ↪o Fin N) (hrange : Set.range s = (S : Set (Fin N))) :
    Subgroup.closure (Set.range (tbnu_reflFull N n s)) = UnitRaw.normalizerOf S := by
  unfold tbnu_reflFull
  exact tbnu_closureQ N S s hrange

private theorem tbnu_closureHeart (N : ℕ) (S : Finset (Fin N)) {n : ℕ}
    (s : Fin (n + 1) ↪o Fin N) (hrange : Set.range s = (S : Set (Fin N))) :
    Subgroup.closure (Set.range (tbnu_reflHeart N n s)) = UnitRaw.normalizerOfH S := by
  unfold tbnu_reflHeart
  exact tbnu_closureH N S s hrange

private theorem tbnu_ker_iffFull {N n : ℕ} {S : Finset (Fin N)} {s : Fin (n + 1) ↪o Fin N}
    (hrange : Set.range s = (S : Set (Fin N))) (v : UnitRaw.Vfull N) :
    (∀ i : Fin n, tbnu_rootFull N n s i v = 0) ↔ v ∈ UnitRaw.cent S := by
  unfold tbnu_rootFull
  exact tbnu_ker_iffQ hrange v

private theorem tbnu_ker_iffHeart {N n : ℕ} {S : Finset (Fin N)} {s : Fin (n + 1) ↪o Fin N}
    (hrange : Set.range s = (S : Set (Fin N))) (v : ↥(UnitRaw.heart N)) :
    (∀ i : Fin n, tbnu_rootHeart N n s i v = 0) ↔ v ∈ UnitRaw.centH S := by
  unfold tbnu_rootHeart
  exact tbnu_ker_iffH hrange v


private noncomputable def tbnu_datumFull (N : ℕ) (S : Finset (Fin N)) (hS : 4 ≤ S.card) :
    CodeWeylDatum (unitFullEntry N) S := by
  classical
  let R : RawFrameData := unitFullEntry N
  change CodeWeylDatum R S
  let n := S.card - 1
  have hn : 1 ≤ n := by omega
  have hcard : S.card = n + 1 := by omega
  let s : Fin (n + 1) ↪o Fin N := S.orderEmbOfFin hcard
  have hrange : Set.range s = (S : Set (Fin N)) := by
    simp [s]
  exact
    { ι := Fin n
      coxeter := CoxeterMatrix.A n
      cartan := CartanMatrix.A n
      coroot := tbnu_corootFull N n s
      root := tbnu_rootFull N n s
      isWeyl := Or.inl ⟨n, Equiv.refl _, hn, Or.inl rfl⟩
      isCartan := ggIntCartan_A n
      pairing := fun i j => tbnu_pairingFull i j
      refl := tbnu_reflFull N n s
      refl_apply := fun i v => tbnu_refl_applyFull i v
      closure_refl := tbnu_closureFull N S s hrange
      ker_iff := fun v => tbnu_ker_iffFull hrange v }

private noncomputable def tbnu_datumHeart (N : ℕ) (S : Finset (Fin N)) (hS : 4 ≤ S.card) :
    CodeWeylDatum (unitHeartEntry N) S := by
  classical
  let R : RawFrameData := unitHeartEntry N
  change CodeWeylDatum R S
  let n := S.card - 1
  have hn : 1 ≤ n := by omega
  have hcard : S.card = n + 1 := by omega
  let s : Fin (n + 1) ↪o Fin N := S.orderEmbOfFin hcard
  have hrange : Set.range s = (S : Set (Fin N)) := by
    simp [s]
  let h : Fin n → ↥(UnitRaw.heart N) := fun i =>
    ⟨(UnitRaw.oneLine N).mkQ
        (Pi.single (s i.castSucc) (1 : ZMod 3) - Pi.single (s i.succ) 1),
      UnitRaw.mkQ_single_sub_single_mem_heart N _ _⟩
  exact
    { ι := Fin n
      coxeter := CoxeterMatrix.A n
      cartan := CartanMatrix.A n
      coroot := tbnu_corootHeart N n s
      root := tbnu_rootHeart N n s
      isWeyl := Or.inl ⟨n, Equiv.refl _, hn, Or.inl rfl⟩
      isCartan := ggIntCartan_A n
      pairing := fun i j => tbnu_pairingHeart i j
      refl := tbnu_reflHeart N n s
      refl_apply := fun i v => tbnu_refl_applyHeart i v
      closure_refl := tbnu_closureHeart N S s hrange
      ker_iff := fun v => tbnu_ker_iffHeart hrange v }

theorem nbrWeylData_unitFull (N : ℕ) : NbrWeylData (unitFullEntry N) := by
  intro v S _ hadm _ _
  exact ⟨tbnu_datumFull N S hadm.2⟩

theorem nbrWeylData_unitHeart (N : ℕ) : NbrWeylData (unitHeartEntry N) := by
  intro v S _ hadm _ _
  exact ⟨tbnu_datumHeart N S hadm.2.2⟩

end

end CFSG.StandardType.GGQ2Frame

end
