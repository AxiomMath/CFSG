module

public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofStatements
public import CFSG.RankThree.PartTwo.Sec10.Sec10XStepsU

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory

namespace Step1012ClaimProof


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

omit
  [Finite G] in
theorem mem_centralizer_closure_pair_iff {a d x : G} :
    x ∈ Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) ↔
      x * a = a * x ∧ x * d = d * x := by
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩

omit
  [Finite G] in
theorem isPGroup_autIn {X S : Subgroup G} (hX2 : IsPGroup 2 X) :
    IsPGroup 2 (Sec4.autIn X S) :=
  ((hX2.to_le inf_le_left).comap_subtype
    (K := Subgroup.normalizer (S : Set G))).map S.normalizerMonoidHom

theorem automizer_type (hGL : KS1012GL34) (h : Sec10Std G A c L a R)
    {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) {S : Subgroup G}
    (hSab : IsMulCommutative S) (hSpow : ∀ s ∈ S, s ^ 2 = 1)
    (hSA : A ≤ Subgroup.normalizer (S : Set G))
    (hSc : S ⊓ Subgroup.centralizer ({c} : Set G) = sec10U L a)
    (hSd : S ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) {w : G}
    (hwS : w ∈ Subgroup.normalizer (S : Set G)) (hwa : w * a * w⁻¹ = a)
    (hwd : w * d * w⁻¹ = d) (hwc : w * c * w⁻¹ = c * d) {X : Subgroup G}
    (hX2 : IsPGroup 2 X) (hXA : A ≤ Subgroup.normalizer (X : Set G))
    (hXN : X ≤ Subgroup.normalizer (S : Set G))
    (hXB : X ≤ Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G))
    (hXS : ¬ X ≤ Subgroup.centralizer (S : Set G)) :
    Sec4.IsSLThreePiAt (inSubgroup perfectResidual (Sec4.autIn
        (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S)) 4 ∨
      Sec4.IsTripleCover (inSubgroup perfectResidual (Sec4.autIn
        (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S))
        (alternatingGroup (Fin 6)) := by
  have hdA := h.d_mem_A hdL
  set CB := Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) with hCB
  set Y := Sec4.autIn CB S with hY
  set φ := S.normalizerMonoidHom with hφ
  have hφapp : ∀ {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G)) (s : S),
      ((φ ⟨g, hg⟩ s : S) : G) = g * s * g⁻¹ := fun hg s =>
    Sec4.normalizerMonoidHom_apply_coe hg s
  have hdN : d ∈ Subgroup.normalizer (S : Set G) := hSA hdA
  have hcN : c ∈ Subgroup.normalizer (S : Set G) := hSA h.mem_A
  have hdCB : d ∈ CB := mem_centralizer_closure_pair_iff.mpr ⟨h.comm hdA h.a_mem, rfl⟩
  have hcCB : c ∈ CB :=
    mem_centralizer_closure_pair_iff.mpr ⟨h.comm h.mem_A h.a_mem, h.comm h.mem_A hdA⟩
  have hwCB : w ∈ CB := by
    refine mem_centralizer_closure_pair_iff.mpr ⟨?_, ?_⟩
    · calc w * a = w * a * w⁻¹ * w := by group
        _ = a * w := by rw [hwa]
    · calc w * d = w * d * w⁻¹ * w := by group
        _ = d * w := by rw [hwd]
  set z := φ ⟨d, hdN⟩ with hz
  set x := φ ⟨c, hcN⟩ with hx
  set w' := φ ⟨w, hwS⟩ with hw'
  have hzY : z ∈ Y := Sec4.mem_autIn_iff.mpr ⟨d, hdN, hdCB, rfl⟩
  have hxY : x ∈ Y := Sec4.mem_autIn_iff.mpr ⟨c, hcN, hcCB, rfl⟩
  have hwY : w' ∈ Y := Sec4.mem_autIn_iff.mpr ⟨w, hwS, hwCB, rfl⟩
  have hzc : ∀ y ∈ Y, y * z = z * y := by
    intro y hy
    obtain ⟨g, hgN, hgCB, rfl⟩ := Sec4.mem_autIn_iff.mp hy
    rw [hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_closure_pair_iff.mp hgCB).2
  have hz3 : z ^ 3 = 1 := by
    rw [hz, ← map_pow]
    have : (⟨d, hdN⟩ : Subgroup.normalizer (S : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using h.pow_three hdA)
    rw [this, map_one]
  have hzfix : ∀ s : S, z s = s → s = 1 := by
    intro s hs
    have h1 := congrArg Subtype.val hs
    rw [hz, hφapp] at h1
    have hsd : (s : G) * d = d * s := by
      calc (s : G) * d = d * s * d⁻¹ * d := by rw [h1]
        _ = d * s := by group
    have hmem : (s : G) ∈ S ⊓ Subgroup.centralizer ({d} : Set G) :=
      ⟨s.2, Subgroup.mem_centralizer_singleton_iff.mpr hsd⟩
    rw [hSd, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← map_pow]
    have : (⟨c, hcN⟩ : Subgroup.normalizer (S : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using h.pow_three h.mem_A)
    rw [this, map_one]
  have hxfix : ∀ s : S, x s = s ↔ (s : G) ∈ Subgroup.centralizer ({c} : Set G) := by
    intro s
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hs
      have h1 := congrArg Subtype.val hs
      rw [hx, hφapp] at h1
      calc (s : G) * c = c * s * c⁻¹ * c := by rw [h1]
        _ = c * s := by group
    · intro hs
      apply Subtype.ext
      rw [hx, hφapp, ← hs, mul_inv_cancel_right]
  have hx4 : Nat.card {s : S // x s = s} = 4 := by
    rw [← (Sec10XSteps.sec10U_facts h).2.1, ← hSc]
    exact Nat.card_congr
      { toFun := fun s => ⟨s.1, s.1.2, (hxfix s.1).mp s.2⟩
        invFun := fun t => ⟨⟨t, t.2.1⟩, (hxfix ⟨t, t.2.1⟩).mpr t.2.2⟩
        left_inv := fun s => rfl
        right_inv := fun t => rfl }
  have hwx : w' * x * w'⁻¹ = x * z := by
    rw [hw', hx, hz, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hwc
  set T := Sec4.autIn X S with hT
  have hTY : T ≤ Y := by
    intro t ht
    obtain ⟨g, hgN, hgX, rfl⟩ := Sec4.mem_autIn_iff.mp ht
    exact Sec4.mem_autIn_iff.mpr ⟨g, hgN, hXB hgX, rfl⟩
  have hT1 : T ≠ ⊥ := by
    intro hbot
    apply hXS
    intro g hg
    have hφg : φ ⟨g, hXN hg⟩ = 1 := by
      have hmem : φ ⟨g, hXN hg⟩ ∈ T := Sec4.mem_autIn_iff.mpr ⟨g, hXN hg, hg, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hφg ⟨s, hs⟩)
    rw [hφapp, MulAut.one_apply] at h1
    calc s * g = g * s * g⁻¹ * g := by rw [h1]
      _ = g * s := by group
  have hconjT : ∀ (y : G) (hy : y ∈ A), ∀ t ∈ T, φ ⟨y, hSA hy⟩ * t * (φ ⟨y, hSA hy⟩)⁻¹ ∈ T := by
    intro y hy t ht
    obtain ⟨g, hgN, hgX, rfl⟩ := Sec4.mem_autIn_iff.mp ht
    have hygX : y * g * y⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hXA hy) g).mp hgX
    refine Sec4.mem_autIn_iff.mpr ⟨y * g * y⁻¹, hXN hygX, hygX, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hxT : x ∈ Subgroup.normalizer (T : Set (MulAut S)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨hconjT c h.mem_A t, fun ht => ?_⟩
    have h1 := hconjT c⁻¹ (A.inv_mem h.mem_A) _ ht
    have h2 : φ ⟨c⁻¹, hSA (A.inv_mem h.mem_A)⟩ = x⁻¹ := by
      rw [hx, ← map_inv]
      rfl
    rw [h2, inv_inv] at h1
    simpa [mul_assoc] using h1
  exact hGL S (fun s t => hSab.1.comm s t) (fun s => Subtype.ext (by simpa using hSpow s s.2))
    Y z x w' hzY hxY hwY hzc hz3 hzfix hx3 hx4 hwx ⟨T, hTY, hT1, isPGroup_autIn hX2, hxT⟩

end Step1012ClaimProof

end CFSG.RankThree.PartTwo.Sec10
