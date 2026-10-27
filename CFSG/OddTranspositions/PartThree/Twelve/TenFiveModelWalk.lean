module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelWalkAux
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

@[expose] def fiveReflectionsFixing (k : ℕ) (ε π : Bool) (c : Fin (k + 1) → ZMod 5) :
    Set (GL (Fin (k + 1)) (ZMod 5)) :=
  {g | g ∈ fiveReflections k ε π ∧
    (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = c}

open FiveWalk

theorem five_two_mul_ne : ∀ c : ZMod 5, c ≠ 0 → 2 * c ≠ c ∧ 2 * c ≠ -c := by decide

theorem fiveReflOf_mul_mem_closure_of_pairing_ne {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    (c : Fin (k + 1) → ZMod 5) {x y : Fin (k + 1) → ZMod 5}
    (hQ : fiveForm k ε y y = fiveForm k ε x x) (hx : fiveForm k ε x x ≠ 0)
    (hxπ : IsSquare (fiveForm k ε x x) ↔ (!π) = true)
    (hxy1 : fiveForm k ε x y ≠ fiveForm k ε x x)
    (hxy2 : fiveForm k ε x y ≠ -fiveForm k ε x x)
    (hxc : fiveForm k ε x c = 0) (hyc : fiveForm k ε y c = 0) :
    fiveReflOf k ε x * fiveReflOf k ε y ∈ Subgroup.closure (fiveReflectionsFixing k ε π c) := by
  have hsign : ¬ IsSquare (fiveForm k ε x x) ↔ π = true := by cases π <;> simp_all
  rcases five_sq_class_opposite (fiveForm k ε x x) (fiveForm k ε x y) hx hxy1 hxy2 with
    ⟨hu_ne, husq⟩ | ⟨hu_ne, husq⟩
  ·
    have huQ : fiveForm k ε (x - y) (x - y) = 2 * fiveForm k ε x x - 2 * fiveForm k ε x y := by
      rw [fiveNorm_sub, hQ]; ring
    have husign : IsSquare (fiveForm k ε (x - y) (x - y)) ↔ π = true := by
      rw [huQ]; exact husq.trans hsign
    have huc : fiveForm k ε (x - y) c = 0 := by
      rw [fiveForm_sub_left, hxc, hyc]; ring
    have ht_mem : fiveReflOf k ε (x - y) ∈ fiveReflectionsFixing k ε π c := by
      refine ⟨fiveReflOf_mem (by rw [huQ]; exact hu_ne) husign, ?_⟩
      rw [fiveReflOf_mulVec, fiveForm_comm k ε c (x - y), huc, mul_zero, zero_mul, zero_smul]
      abel
    have htx : (((fiveReflOf k ε (x - y) : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x) = y :=
      fiveReflOf_sub_mulVec k ε hQ (by rwa [huQ])
    have ht2 : fiveReflOf k ε (x - y) * fiveReflOf k ε (x - y) = 1 := fiveReflOf_mul_self k ε (x - y)
    have hconj : fiveReflOf k ε (x - y) * fiveReflOf k ε x * (fiveReflOf k ε (x - y))⁻¹ =
        fiveReflOf k ε y := by
      rw [conj_fiveReflOf (hg := fiveForm_fiveReflOf k ε (x - y)) x, htx]
    have hry : fiveReflOf k ε y =
        fiveReflOf k ε (x - y) * fiveReflOf k ε x * fiveReflOf k ε (x - y) := by
      rw [← hconj, inv_eq_of_mul_eq_one_right ht2]
    have hprod : fiveReflOf k ε x * fiveReflOf k ε y =
        (fiveReflOf k ε x * fiveReflOf k ε (x - y) * fiveReflOf k ε x) *
          fiveReflOf k ε (x - y) := by
      rw [hry]; group
    have hxinv : (fiveReflOf k ε x)⁻¹ = fiveReflOf k ε x :=
      inv_eq_of_mul_eq_one_right (fiveReflOf_mul_self k ε x)
    have hconj2 : fiveReflOf k ε x * fiveReflOf k ε (x - y) * fiveReflOf k ε x =
        fiveReflOf k ε (((fiveReflOf k ε x : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ (x - y)) := by
      calc fiveReflOf k ε x * fiveReflOf k ε (x - y) * fiveReflOf k ε x
          = fiveReflOf k ε x * fiveReflOf k ε (x - y) * (fiveReflOf k ε x)⁻¹ := by rw [hxinv]
        _ = fiveReflOf k ε (((fiveReflOf k ε x : GL (Fin (k + 1)) (ZMod 5)) :
              Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ (x - y)) :=
            conj_fiveReflOf (hg := fiveForm_fiveReflOf k ε x) (x - y)
    have hw_mem : fiveReflOf k ε (((fiveReflOf k ε x : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ (x - y)) ∈
        fiveReflectionsFixing k ε π c := by
      refine ⟨fiveReflOf_mem ?_ ?_, ?_⟩
      · rw [fiveNorm_fiveReflOf, huQ]; exact hu_ne
      · rw [fiveNorm_fiveReflOf]; exact husign
      · rw [fiveReflOf_mulVec]
        have hcw : fiveForm k ε c (((fiveReflOf k ε x : GL (Fin (k + 1)) (ZMod 5)) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ (x - y)) = 0 := by
          rw [fiveForm_comm k ε c, fiveForm_fiveReflOf_eq_zero_of_perp k ε hxc huc]
        rw [hcw, mul_zero, zero_mul, zero_smul]
        abel
    rw [hprod, hconj2]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure hw_mem) (Subgroup.subset_closure ht_mem)
  ·
    have huQ : fiveForm k ε (x + y) (x + y) = 2 * fiveForm k ε x x + 2 * fiveForm k ε x y := by
      rw [fiveNorm_add, hQ]; ring
    have husign : IsSquare (fiveForm k ε (x + y) (x + y)) ↔ π = true := by
      rw [huQ]; exact husq.trans hsign
    have huc : fiveForm k ε (x + y) c = 0 := by
      rw [fiveForm_add_left, hxc, hyc]; ring
    have ht_mem : fiveReflOf k ε (x + y) ∈ fiveReflectionsFixing k ε π c := by
      refine ⟨fiveReflOf_mem (by rw [huQ]; exact hu_ne) husign, ?_⟩
      rw [fiveReflOf_mulVec, fiveForm_comm k ε c (x + y), huc, mul_zero, zero_mul, zero_smul]
      abel
    have htx : (((fiveReflOf k ε (x + y) : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x) = -y :=
      fiveReflOf_add_mulVec k ε hQ (by rwa [huQ])
    have ht2 : fiveReflOf k ε (x + y) * fiveReflOf k ε (x + y) = 1 := fiveReflOf_mul_self k ε (x + y)
    have hconj : fiveReflOf k ε (x + y) * fiveReflOf k ε x * (fiveReflOf k ε (x + y))⁻¹ =
        fiveReflOf k ε y := by
      rw [conj_fiveReflOf (hg := fiveForm_fiveReflOf k ε (x + y)) x, htx]
      exact fiveReflOf_neg k ε y
    have hry : fiveReflOf k ε y =
        fiveReflOf k ε (x + y) * fiveReflOf k ε x * fiveReflOf k ε (x + y) := by
      rw [← hconj, inv_eq_of_mul_eq_one_right ht2]
    have hprod : fiveReflOf k ε x * fiveReflOf k ε y =
        (fiveReflOf k ε x * fiveReflOf k ε (x + y) * fiveReflOf k ε x) *
          fiveReflOf k ε (x + y) := by
      rw [hry]; group
    have hxinv : (fiveReflOf k ε x)⁻¹ = fiveReflOf k ε x :=
      inv_eq_of_mul_eq_one_right (fiveReflOf_mul_self k ε x)
    have hconj2 : fiveReflOf k ε x * fiveReflOf k ε (x + y) * fiveReflOf k ε x =
        fiveReflOf k ε (((fiveReflOf k ε x : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ (x + y)) := by
      calc fiveReflOf k ε x * fiveReflOf k ε (x + y) * fiveReflOf k ε x
          = fiveReflOf k ε x * fiveReflOf k ε (x + y) * (fiveReflOf k ε x)⁻¹ := by rw [hxinv]
        _ = fiveReflOf k ε (((fiveReflOf k ε x : GL (Fin (k + 1)) (ZMod 5)) :
              Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ (x + y)) :=
            conj_fiveReflOf (hg := fiveForm_fiveReflOf k ε x) (x + y)
    have hw_mem : fiveReflOf k ε (((fiveReflOf k ε x : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ (x + y)) ∈
        fiveReflectionsFixing k ε π c := by
      refine ⟨fiveReflOf_mem ?_ ?_, ?_⟩
      · rw [fiveNorm_fiveReflOf, huQ]; exact hu_ne
      · rw [fiveNorm_fiveReflOf]; exact husign
      · rw [fiveReflOf_mulVec]
        have hcw : fiveForm k ε c (((fiveReflOf k ε x : GL (Fin (k + 1)) (ZMod 5)) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ (x + y)) = 0 := by
          rw [fiveForm_comm k ε c, fiveForm_fiveReflOf_eq_zero_of_perp k ε hxc huc]
        rw [hcw, mul_zero, zero_mul, zero_smul]
        abel
    rw [hprod, hconj2]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure hw_mem) (Subgroup.subset_closure ht_mem)

theorem exists_fiveForm_orth_eq {k : ℕ} (hk : 4 ≤ k) (ε : Bool) {a : Fin (k + 1) → ZMod 5}
    (ha : fiveForm k ε a a ≠ 0) (b : Fin (k + 1) → ZMod 5) {d : ZMod 5} (hd : d ≠ 0) :
    ∃ z, fiveForm k ε z a = 0 ∧ fiveForm k ε z b = 0 ∧ fiveForm k ε z z = d := by
  obtain ⟨w₁, w₂, h1a, h1b, h1n, h2a, h2b, h2n, h12⟩ :=
    exists_two_aniso_perp hk ε ha (b := b)
  obtain ⟨α, β, hαβ⟩ := five_exists_sq_comb (fiveForm k ε w₁ w₁) (fiveForm k ε w₂ w₂) d h1n h2n
  refine ⟨α • w₁ + β • w₂, ?_, ?_, ?_⟩
  · rw [fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left, h1a, h2a, mul_zero, mul_zero,
      add_zero]
  · rw [fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left, h1b, h2b, mul_zero, mul_zero,
      add_zero]
  · rw [fiveNorm_add_smul, h12, mul_zero, add_zero]
    exact hαβ

theorem fiveReflOf_mul_mem_closure_of_pairing_eq {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    (c : Fin (k + 1) → ZMod 5) {x y : Fin (k + 1) → ZMod 5}
    (hQ : fiveForm k ε y y = fiveForm k ε x x) (hx : fiveForm k ε x x ≠ 0)
    (hxπ : IsSquare (fiveForm k ε x x) ↔ (!π) = true)
    (hb : fiveForm k ε x y = fiveForm k ε x x ∨ fiveForm k ε x y = -fiveForm k ε x x)
    (hxc : fiveForm k ε x c = 0) (hyc : fiveForm k ε y c = 0) :
    fiveReflOf k ε x * fiveReflOf k ε y ∈ Subgroup.closure (fiveReflectionsFixing k ε π c) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨s, hsQ, hsx, hsy, hsc, hy_eq⟩ : ∃ s, fiveForm k ε s s = 0 ∧ fiveForm k ε s x = 0 ∧
      fiveForm k ε s y = 0 ∧ fiveForm k ε s c = 0 ∧ (y = s + x ∨ y = s - x) := by
    rcases hb with hb | hb
    · exact ⟨y - x, by rw [fiveNorm_sub, hQ, fiveForm_comm k ε y x, hb]; ring,
        by rw [fiveForm_sub_left, fiveForm_comm k ε y x, hb, sub_self],
        by rw [fiveForm_sub_left, hQ, hb, sub_self],
        by rw [fiveForm_sub_left, hyc, hxc, sub_self],
        Or.inl (by abel)⟩
    · exact ⟨y + x, by rw [fiveNorm_add, hQ, fiveForm_comm k ε y x, hb]; ring,
        by rw [fiveForm_add_left, fiveForm_comm k ε y x, hb]; ring,
        by rw [fiveForm_add_left, hQ, hb]; ring,
        by rw [fiveForm_add_left, hyc, hxc, add_zero],
        Or.inr (by abel)⟩
  by_cases hs0 : s = 0
  · have hyx : y = x ∨ y = -x := by
      rcases hy_eq with h | h
      · left; rw [hs0, zero_add] at h; exact h
      · right; rw [hs0, zero_sub] at h; exact h
    rcases hyx with h | h
    · rw [h, fiveReflOf_mul_self]; exact Subgroup.one_mem _
    · rw [h]
      have hneg : fiveReflOf k ε (-x) = fiveReflOf k ε x := fiveReflOf_neg k ε x
      rw [hneg, fiveReflOf_mul_self k ε x]
      exact Subgroup.one_mem _
  · have hz : ∃ z, fiveForm k ε z z = fiveForm k ε x x ∧ fiveForm k ε x z = 0 ∧
        fiveForm k ε z y ≠ fiveForm k ε x x ∧ fiveForm k ε z y ≠ -fiveForm k ε x x ∧
        fiveForm k ε z c = 0 := by
      by_cases hex : ∃ t, fiveForm k ε t x = 0 ∧ fiveForm k ε t c = 0 ∧ fiveForm k ε s t ≠ 0
      · obtain ⟨t, htx, htc, hst⟩ := hex
        obtain ⟨t₁, hst₁, ht₁x, ht₁c⟩ : ∃ t₁, fiveForm k ε s t₁ = 1 ∧ fiveForm k ε t₁ x = 0 ∧
            fiveForm k ε t₁ c = 0 := by
          refine ⟨(fiveForm k ε s t)⁻¹ • t, ?_, ?_, ?_⟩
          · rw [fiveForm_smul_right]; exact inv_mul_cancel₀ hst
          · rw [fiveForm_smul_left, htx, mul_zero]
          · rw [fiveForm_smul_left, htc, mul_zero]
        obtain ⟨t', hst', ht'Q, ht'x, ht'c⟩ : ∃ t', fiveForm k ε s t' = 1 ∧
            fiveForm k ε t' t' = 0 ∧ fiveForm k ε t' x = 0 ∧ fiveForm k ε t' c = 0 := by
          refine ⟨t₁ - ((2 : ZMod 5)⁻¹ * fiveForm k ε t₁ t₁) • s, ?_, ?_, ?_, ?_⟩
          · rw [fiveForm_sub_right, fiveForm_smul_right, hst₁, hsQ, mul_zero]; ring
          · rw [fiveForm_sub_smul_expand, fiveForm_comm k ε t₁ s, hst₁, hsQ, mul_one, mul_zero,
              add_zero, five_inv_two]
            ring_nf
            rw [five_eq_zero]; ring
          · rw [fiveForm_sub_left, fiveForm_smul_left, ht₁x, hsx, mul_zero]; ring
          · rw [fiveForm_sub_left, fiveForm_smul_left, ht₁c, hsc, mul_zero]; ring
        have hsx' : fiveForm k ε x s = 0 := by rw [fiveForm_comm k ε x s]; exact hsx
        have ht'x' : fiveForm k ε x t' = 0 := by rw [fiveForm_comm k ε x t']; exact ht'x
        set z : Fin (k + 1) → ZMod 5 := (4 : ZMod 5) • s + (2 * fiveForm k ε x x) • t' with hzdef
        have hzQ : fiveForm k ε z z = fiveForm k ε x x := by
          rw [hzdef, fiveNorm_add_smul, hsQ, ht'Q, hst']
          ring_nf
          rw [five_num_16, mul_one]
        have hzx : fiveForm k ε x z = 0 := by
          rw [hzdef, fiveForm_add_right, fiveForm_smul_right, fiveForm_smul_right, hsx', ht'x',
            mul_zero, mul_zero, add_zero]
        have hzy_val : fiveForm k ε z y = 2 * fiveForm k ε x x := by
          have hyt' : fiveForm k ε y t' = 1 := by
            rcases hy_eq with h | h
            · rw [h, fiveForm_add_left, hst', ht'x']; ring
            · rw [h, fiveForm_sub_left, hst', ht'x']; ring
          have ht'y : fiveForm k ε t' y = 1 := by rw [fiveForm_comm k ε t' y]; exact hyt'
          rw [hzdef, fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left, hsy, ht'y,
            mul_zero, mul_one]; ring
        have hzc : fiveForm k ε z c = 0 := by
          rw [hzdef, fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left, hsc, ht'c,
            mul_zero, mul_zero]; ring
        exact ⟨z, hzQ, hzx, by rw [hzy_val]; exact (five_two_mul_ne (fiveForm k ε x x) hx).1,
          by rw [hzy_val]; exact (five_two_mul_ne (fiveForm k ε x x) hx).2, hzc⟩
      · push Not at hex
        obtain ⟨z, hzx0, hzc0, hzQ0⟩ := exists_fiveForm_orth_eq hk ε hx c (d := fiveForm k ε x x) hx
        have hzx' : fiveForm k ε x z = 0 := by rw [fiveForm_comm k ε x z]; exact hzx0
        have hsz : fiveForm k ε s z = 0 := hex z hzx0 hzc0
        have hzy0 : fiveForm k ε z y = 0 := by
          rcases hy_eq with h | h
          · rw [h, fiveForm_add_right, fiveForm_comm k ε z s, hsz, hzx0]; ring
          · rw [h, fiveForm_sub_right, fiveForm_comm k ε z s, hsz, hzx0]; ring
        exact ⟨z, hzQ0, hzx', by rw [hzy0]; exact fun h => hx h.symm,
          by rw [hzy0]; exact fun h => hx (neg_eq_zero.mp h.symm), hzc0⟩
    obtain ⟨z, hzQ, hzx, hzy1, hzy2, hzc⟩ := hz
    have hzy : fiveForm k ε y y = fiveForm k ε z z := by rw [hzQ, hQ]
    have hz_ne : fiveForm k ε z z ≠ 0 := by rw [hzQ]; exact hx
    have hzπ : IsSquare (fiveForm k ε z z) ↔ (!π) = true := by rw [hzQ]; exact hxπ
    have hzy1' : fiveForm k ε z y ≠ fiveForm k ε z z := by rw [hzQ]; exact hzy1
    have hzy2' : fiveForm k ε z y ≠ -fiveForm k ε z z := by rw [hzQ]; exact hzy2
    have hxz1 : fiveForm k ε x z ≠ fiveForm k ε x x := by rw [hzx]; exact fun h => hx h.symm
    have hxz2 : fiveForm k ε x z ≠ -fiveForm k ε x x := by
      rw [hzx]; exact fun h => hx (neg_eq_zero.mp h.symm)
    have h1 := fiveReflOf_mul_mem_closure_of_pairing_ne hk ε π c hzQ hx hxπ hxz1 hxz2 hxc hzc
    have h2 := fiveReflOf_mul_mem_closure_of_pairing_ne hk ε π c hzy hz_ne hzπ hzy1' hzy2' hzc hyc
    have hzz : fiveReflOf k ε z * fiveReflOf k ε z = 1 := fiveReflOf_mul_self k ε z
    have hsplit : fiveReflOf k ε x * fiveReflOf k ε y =
        (fiveReflOf k ε x * fiveReflOf k ε z) * (fiveReflOf k ε z * fiveReflOf k ε y) := by
      rw [mul_assoc (fiveReflOf k ε x) (fiveReflOf k ε z) (fiveReflOf k ε z * fiveReflOf k ε y),
        ← mul_assoc (fiveReflOf k ε z) (fiveReflOf k ε z) (fiveReflOf k ε y), hzz, one_mul]
    rw [hsplit]
    exact Subgroup.mul_mem _ h1 h2

theorem fiveReflOf_mul_mem_closure_of_norm_eq {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    (c : Fin (k + 1) → ZMod 5) {x y : Fin (k + 1) → ZMod 5}
    (hQ : fiveForm k ε y y = fiveForm k ε x x) (hx : fiveForm k ε x x ≠ 0)
    (hxπ : IsSquare (fiveForm k ε x x) ↔ (!π) = true)
    (hxc : fiveForm k ε x c = 0) (hyc : fiveForm k ε y c = 0) :
    fiveReflOf k ε x * fiveReflOf k ε y ∈ Subgroup.closure (fiveReflectionsFixing k ε π c) := by
  by_cases hb : fiveForm k ε x y = fiveForm k ε x x ∨ fiveForm k ε x y = -fiveForm k ε x x
  · exact fiveReflOf_mul_mem_closure_of_pairing_eq hk ε π c hQ hx hxπ hb hxc hyc
  · push Not at hb
    exact fiveReflOf_mul_mem_closure_of_pairing_ne hk ε π c hQ hx hxπ hb.1 hb.2 hxc hyc

theorem fiveReflOf_mul_mem_closure_fiveReflectionsFixing {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    (c : Fin (k + 1) → ZMod 5) {x y : Fin (k + 1) → ZMod 5}
    (hx : fiveForm k ε x x ≠ 0) (hxπ : IsSquare (fiveForm k ε x x) ↔ (!π) = true)
    (hy : fiveForm k ε y y ≠ 0) (hyπ : IsSquare (fiveForm k ε y y) ↔ (!π) = true)
    (hxc : fiveForm k ε x c = 0) (hyc : fiveForm k ε y c = 0) :
    fiveReflOf k ε x * fiveReflOf k ε y ∈ Subgroup.closure (fiveReflectionsFixing k ε π c) := by
  obtain ⟨l, hl⟩ := exists_sq_mul_eq_of_isSquare_iff hy hx (hyπ.trans hxπ.symm)
  have hl0 : l ≠ 0 := by
    have hne : l ^ 2 * fiveForm k ε y y ≠ 0 := by rw [hl]; exact hx
    rintro rfl
    exact hne (by norm_num)
  have hQ : fiveForm k ε (l • y) (l • y) = fiveForm k ε x x := by
    rw [fiveForm_smul_left, fiveForm_smul_right,
      show l * (l * fiveForm k ε y y) = l ^ 2 * fiveForm k ε y y by ring, hl]
  have hy'c : fiveForm k ε (l • y) c = 0 := by
    rw [fiveForm_smul_left, hyc, mul_zero]
  have hmain := fiveReflOf_mul_mem_closure_of_norm_eq hk ε π c hQ hx hxπ hxc hy'c
  rwa [fiveReflOf_smul k ε y hl0] at hmain

theorem mul_mem_fiveReflectionGroup_of_mem_fiveReflections_not {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {g h : GL (Fin (k + 1)) (ZMod 5)} (hg : g ∈ fiveReflections k ε (!π))
    (hh : h ∈ fiveReflections k ε (!π)) : g * h ∈ fiveReflectionGroup k ε π := by
  obtain ⟨x, hx, hxπ, rfl⟩ := exists_eq_fiveReflOf hg
  obtain ⟨y, hy, hyπ, rfl⟩ := exists_eq_fiveReflOf hh
  have hmem := fiveReflOf_mul_mem_closure_fiveReflectionsFixing hk ε π
    (0 : Fin (k + 1) → ZMod 5) hx hxπ hy hyπ (by simp) (by simp)
  have hle : Subgroup.closure (fiveReflectionsFixing k ε π (0 : Fin (k + 1) → ZMod 5)) ≤
      fiveReflectionGroup k ε π := by
    rw [Subgroup.closure_le]
    intro r hr
    exact Subgroup.subset_closure hr.1
  exact hle hmem

end CFSG.OddTranspositions.PartThree
