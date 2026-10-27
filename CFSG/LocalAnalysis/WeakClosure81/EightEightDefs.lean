module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import Certificates.Kernel.Sporadic.Fi22.C2068

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor IsLieOver)

variable {G : Type} [Group G] [Finite G]

@[expose] def kerMV (V H : Subgroup G) : Subgroup G :=
  ((normalizer (V : Set G)).subgroupOf H).normalCore.map H.subtype

theorem mem_kerMV_iff {V H : Subgroup G} {x : G} :
    x ∈ kerMV V H ↔ x ∈ H ∧ ∀ h ∈ H, h * x * h⁻¹ ∈ normalizer (V : Set G) := by
  unfold kerMV
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun h hh => ?_⟩
    have := hy ⟨h, hh⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, fun b => by simpa [Subgroup.mem_subgroupOf] using h b b.2, rfl⟩

theorem kerMV_le_self (V H : Subgroup G) : kerMV V H ≤ H := fun _ hx => (mem_kerMV_iff.mp hx).1

theorem kerMV_le_normalizer (V H : Subgroup G) : kerMV V H ≤ normalizer (V : Set G) :=
  fun x hx => by simpa using (mem_kerMV_iff.mp hx).2 1 H.one_mem

theorem conj_mem_kerMV {V H : Subgroup G} {h x : G} (hh : h ∈ H) (hx : x ∈ kerMV V H) :
    h * x * h⁻¹ ∈ kerMV V H := by
  rw [mem_kerMV_iff] at hx ⊢
  refine ⟨H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh), fun k hk => ?_⟩
  have := hx.2 (k * h) (H.mul_mem hk hh)
  simpa [mul_assoc] using this

theorem le_kerMV_of_normal {V H N : Subgroup G} (hNH : N ≤ H)
    (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hNM : N ≤ normalizer (V : Set G)) :
    N ≤ kerMV V H := fun n hn =>
  mem_kerMV_iff.mpr ⟨hNH hn, fun h hh => hNM (hNn h hh n hn)⟩

@[expose] def oTwoMod (N K : Subgroup G) : Subgroup G :=
  ⨆ W ∈ {W : Subgroup G | N ≤ W ∧ W ≤ K ∧ (W.subgroupOf K).Normal ∧
    ∀ w ∈ W, ∃ k : ℕ, w ^ (2 ^ k) ∈ N}, W

@[expose] def IsComponentModN (N M L : Subgroup G) : Prop :=
  (N.subgroupOf M).Normal ∧ N ≤ L ∧ L ≤ M ∧ IsSubnormal L M ∧
    HasQuotShape L (N : Set G) (fun X _ => IsQuasisimple X)

@[expose] def IsMaxParabolicMod (N L P : Subgroup G) : Prop :=
  N ≤ P ∧ P < L ∧ (∀ Y : Subgroup G, P < Y → Y ≤ L → Y = L) ∧
    ∃ S : Subgroup G, N ≤ S ∧ S ≤ L ∧ (∀ s ∈ S, ∃ k : ℕ, s ^ (2 ^ k) ∈ N) ∧
      ¬ 2 ∣ S.relIndex L ∧ L ⊓ normalizer (S : Set G) ≤ P

@[expose] def ActsOnDynkinMod (N L : Subgroup G) (t : G) : Prop :=
  t ∈ normalizer (L : Set G) ∧ ∃ P : Subgroup G, IsMaxParabolicMod N L P ∧
    ∀ l ∈ L, conjSubgroup P (t⁻¹ * l) ≠ P

@[expose] def fStarMod (N H : Subgroup G) : Subgroup G :=
  ((CFSG.Open.genFittingFStar (↥H ⧸ (N.subgroupOf H).normalCore)).comap
    (QuotientGroup.mk' (N.subgroupOf H).normalCore)).map H.subtype

@[expose] def IsCalL1 (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, Odd n ∧ 1 < n ∧ (IsL2 X n ∨ IsSz X n ∨ IsL3 X n)

@[expose] def IsCalL0 (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 2 < n ∧ IsLieOver X n) ∨ Is3D4 X 1 ∨ Is3D4 X 2 ∨ IsU4 X 2 ∨ IsU5 X 2 ∨
    IsOmega8m X 2 ∨ IsAlt X 9

@[expose] def calLT (P : ∀ (X : Type) [Group X], Prop) (H T : Subgroup G) : Set (Subgroup G) :=
  {X | T ≤ X ∧ X < H ∧ ¬ HasCompFactor X P}

@[expose] def lGen (P : ∀ (X : Type) [Group X], Prop) (H T : Subgroup G) : Subgroup G :=
  ⨆ X ∈ calLT P H T, X

@[expose] def calNIn (H T : Subgroup G) : Set (Subgroup G) :=
  {X | T ≤ X ∧ X < H ∧ ∀ Y : Subgroup G, X < Y → Y ≤ H → Y = H}

theorem isSylowIn_of_le_of_le {p : ℕ} {P K K' : Subgroup G} (hP : IsSylowIn p P K)
    (hPK' : P ≤ K') (hK'K : K' ≤ K) : IsSylowIn p P K' := by
  refine ⟨hPK', hP.isPGroup, fun h => hP.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P K' K hPK' hK'K]
  exact h.mul_right _

theorem exists_mem_calNIn_of_lt {H T Y : Subgroup G} (hTY : T ≤ Y) (hYH : Y < H) :
    ∃ X ∈ calNIn H T, Y ≤ X := by
  classical
  let S : Set (Subgroup G) := {Z | Y ≤ Z ∧ Z < H}
  obtain ⟨Z, ⟨hYZ, hZH⟩, hmax⟩ := Set.Finite.exists_maximalFor
    (fun Z : Subgroup G => Nat.card Z) S (Set.toFinite S) ⟨Y, le_rfl, hYH⟩
  refine ⟨Z, ⟨hTY.trans hYZ, hZH, fun Y' hZY' hY'H => ?_⟩, hYZ⟩
  by_contra hne
  have hY'lt : Y' < H := lt_of_le_of_ne hY'H hne
  have hcard := Subgroup.card_lt_of_lt hZY'
  have h2 : Nat.card Y' ≤ Nat.card Z := hmax ⟨hYZ.trans hZY'.le, hY'lt⟩ hcard.le
  omega

theorem frattini_argument {p : ℕ} [Fact p.Prime] {H N P : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hP : IsSylowIn p P N) {h : G} (hh : h ∈ H) :
    ∃ k ∈ N, ∃ n ∈ H ⊓ normalizer (P : Set G), h = k * n := by
  have hHN : H ≤ normalizer (N : Set G) := (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hN
  obtain ⟨k, hk, hkx⟩ := Ch1Sec3.exists_conj_of_isSylowIn hP
    (Ch1Sec3.isSylowIn_map_conj hP (hHN hh))
  refine ⟨k, hk, k⁻¹ * h, Subgroup.mem_inf.mpr ⟨H.mul_mem (H.inv_mem (hNH hk)) hh, ?_⟩,
    by group⟩
  refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
  have h1 : h * z * h⁻¹ ∈ P.map (MulAut.conj h).toMonoidHom ↔ z ∈ P := by
    constructor
    · rintro ⟨y, hy, hyz⟩
      have : y = z := by simpa [mul_assoc] using hyz
      exact this ▸ hy
    · intro hz
      exact ⟨z, hz, by simp⟩
  rw [← h1, hkx]
  have e : k⁻¹ * (h * z * h⁻¹) * k = k⁻¹ * h * z * (k⁻¹ * h)⁻¹ := by group
  rw [e]

@[expose] def InFSq (j : ℕ) (H : Subgroup G) : Prop :=
  CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InF j (⊤ : Subgroup (Bar2 H))

structure Hyp88 (V H T : Subgroup G) (i : ℕ) : Prop where
  hyp7 : Hyp7 V
  calH : IsCalH V H
  kgroup : CFSG.Open.IsKGroup ↥H
  sylow : IsSylowIn 2 T (H ⊓ normalizer (V : Set G))
  wne : E3.wClos V 0 T ≠ V
  rank : 2 < rk ↥V
  notLe : ¬ H ≤ normalizer (V : Set G)
  i_le : i ≤ 1
  normW : H ⊓ normalizer (E3.wClos V i T : Set G) ≤ normalizer (V : Set G)
  centr : CentralizersInM V H T

theorem Hyp88.of_le {V H T X : Subgroup G} {i : ℕ} (h : Hyp88 V H T i) (hTX : T ≤ X)
    (hXH : X ≤ H) (hXM : ¬ X ≤ normalizer (V : Set G)) : Hyp88 V X T i where
  hyp7 := h.hyp7
  calH := isCalH_of_le h.hyp7.1 h.calH h.sylow hTX hXH
  kgroup := h.kgroup.of_le hXH
  sylow := isSylowIn_of_le_of_le h.sylow (le_inf hTX (h.sylow.le.trans inf_le_right))
    (inf_le_inf_right _ hXH)
  wne := h.wne
  rank := h.rank
  notLe := hXM
  i_le := h.i_le
  normW := (inf_le_inf_right _ hXH).trans h.normW
  centr := fun z hz hzc hz1 => (inf_le_inf_right _ hXH).trans (h.centr z hz hzc hz1)

@[expose] def Concl881 (V H : Subgroup G) : Prop :=
  CFSG.Open.pRank 3 H ≤ 1 →
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 (normalizer (V : Set G)) →
    HasCompFactor H IsCalL1

@[expose] def Concl882 (V H : Subgroup G) : Prop :=
  CFSG.Open.pRank 3 H ≤ 3 →
    (∀ p : ℕ, p.Prime → p ≠ 2 → 3 < CFSG.Open.pRank p H →
      CFSG.Open.pRank p (H ⊓ normalizer (V : Set G)) ≤ 1) →
    HasCompFactor H IsCalL0

theorem not_concl881_iff {V H : Subgroup G} :
    ¬ Concl881 V H ↔ CFSG.Open.pRank 3 H ≤ 1 ∧
      CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 (normalizer (V : Set G)) ∧
      ¬ HasCompFactor H IsCalL1 := by
  unfold Concl881
  tauto

theorem not_concl882_iff {V H : Subgroup G} :
    ¬ Concl882 V H ↔ CFSG.Open.pRank 3 H ≤ 3 ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → 3 < CFSG.Open.pRank p H →
        CFSG.Open.pRank p (H ⊓ normalizer (V : Set G)) ≤ 1) ∧
      ¬ HasCompFactor H IsCalL0 := by
  unfold Concl882
  tauto

structure MinCex88 (V H T : Subgroup G) (i : ℕ) : Prop where
  hyp : Hyp88 V H T i
  fail : ¬ (Concl881 V H ∧ Concl882 V H)
  min : ∀ (H' T' : Subgroup G) (i' : ℕ), Hyp88 V H' T' i' → ¬ (Concl881 V H' ∧ Concl882 V H') →
    Nat.card H ≤ Nat.card H'

theorem MinCex88.concl_of_lt {V H T X : Subgroup G} {i : ℕ} (h : MinCex88 V H T i)
    (hX : Hyp88 V X T i) (hXH : X < H) : Concl881 V X ∧ Concl882 V X := by
  by_contra hfail
  exact absurd (Subgroup.card_lt_of_lt hXH) (not_lt.mpr (h.min X T i hX hfail))

@[expose] def Asch5_11 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (H T : Subgroup Q),
    CFSG.Open.IsKGroup ↥H → IsSylowIn 2 T H → T < H → ¬ HasCompFactor H IsCalL0 →
    H ≠ lGen IsCalL0 H T →
    (∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p H ≤ 3 ∨ CFSG.Open.pRank p (lGen IsCalL0 H T) ≤ 1) →
    (calNIn H T = {lGen IsCalL0 H T} ∧
      (IsSolvable ↥H ∨ ∃ L : Subgroup Q, IsComponentModN (OInf H) H L ∧ L ⊔ T = H)) ∧
    (InFSq 1 H ∨
      (InFSq 2 H ∧ ∃ L : Subgroup Q, IsComponentModN (OInf H) H L ∧ L ⊔ T = H ∧
        (HasQuotShape L (OInf H : Set Q) (fun X _ => IsL2 X 2) ∨
          HasQuotShape L (OInf H : Set Q) (fun X _ => IsU3 X 2) ∨
          ((HasQuotShape L (OInf H : Set Q) (fun X _ => IsL3 X 2) ∨
              HasQuotShape L (OInf H : Set Q) (fun X _ => IsSp4 X 2)) ∧
            ∃ t ∈ T, ActsOnDynkinMod (OInf H) L t))))

@[expose] def Asch5_13 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (H T : Subgroup Q),
    CFSG.Open.IsKGroup ↥H → IsSylowIn 2 T H → T < H → CFSG.Open.pRank 3 H ≤ 1 →
    ¬ HasCompFactor H IsCalL1 → H ≠ lGen IsCalL1 H T →
    calNIn H T = {lGen IsCalL1 H T} ∧
      (InFSq 1 H ∨ ∃ n : ℕ, 1 ≤ n ∧
        (HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set Q)
            (fun X _ => IsL2 X (2 * n)) ∨
          HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set Q)
            (fun X _ => IsU3 X (2 * n))))

end CFSG.LocalAnalysis.WeakClosure81

end
