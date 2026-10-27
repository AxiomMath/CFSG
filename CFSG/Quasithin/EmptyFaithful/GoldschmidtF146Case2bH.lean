module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bG
public import CFSG.Quasithin.EmptyFaithful.S151S9UPerf

public section

namespace CFSG.Quasithin.F146Field.Case2b

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped MatrixGroups commutatorElement

section Fields2

variable {G : Type} [Group G] [Finite G] {T M H K : Subgroup G}
  {c : Case2a.Setting T M H K}

omit [Finite G] in
theorem mem_cComp_sup_of_normalizes {X R : Subgroup G} (hK : X ∈ cComp X)
    (hR : R ≤ Subgroup.normalizer (X : Set G)) : X ∈ cComp (X ⊔ R) := by
  obtain ⟨hne, hperf, -, hmin⟩ := hK
  have hnorm : X ⊔ R ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hR
  refine ⟨hne, hperf, A3.subnormal_of_normal le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hnorm), ?_⟩
  intro K' hlt hK'ne hK'perf hsub
  exact hmin K' hlt hK'ne hK'perf (A3.subnormal_of_le_of_le hsub hlt.le le_sup_left)

section Levi2

variable {F : Type} [Field F] [Finite F] {m : ℕ}

theorem cComp_K1 {P1 : Subgroup (E2.StarQuot (H ⊓ M) H)} (hP1 : P1 ≤ E2.star (H ⊓ M) H K)
    (hm : 2 ≤ m) (hF : Nat.card F = 2 ^ m) (g : ↥(perfectCore P1) →* SL(2, F))
    (hg : Function.Surjective g) (hk : IsPGroup 2 g.ker) :
    K1 c P1 ∈ cComp (K1 c P1 ⊔ S1421.sOf T (K1 c P1)) := by
  obtain ⟨ψ, hψ, hsolv, -⟩ := isL2Quot_K1 (c := c) hP1 hm hF g hg hk
  have : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
  have hK4 := exists_four hm hF
  have hs := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple hK4
  have hne : K1 c P1 ≠ ⊥ := by
    intro h
    obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_nonabelian hK4
    have : Subsingleton ↥(K1 c P1) := by
      rw [h]
      infer_instance
    obtain ⟨x, rfl⟩ := hψ a
    obtain ⟨y, rfl⟩ := hψ b
    exact hab (by rw [← map_mul, ← map_mul, Subsingleton.elim (x * y) (y * x)])
  have hself := S151S9U.mem_cComp_self_of_simple_quotient ψ hψ hne (perfectCore_perfect _) hsolv
  exact mem_cComp_sup_of_normalizes hself inf_le_right

theorem not_le_K1 {P1 : Subgroup (E2.StarQuot (H ⊓ M) H)} (hP1 : P1 ≤ E2.star (H ⊓ M) H K)
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)))
    (hUsyl : IsSylowTwoOf (E2.star (H ⊓ M) H (T ⊓ K)) (E2.star (H ⊓ M) H K))
    (hUperf : E2.star (H ⊓ M) H (T ⊓ K) ≤ perfectCore P1)
    (hm : 2 ≤ m) (hF : Nat.card F = 2 ^ m) (g : ↥(perfectCore P1) →* SL(2, F))
    (hg : Function.Surjective g) : ¬ K1 c P1 ≤ M := by
  intro hKM
  have hWN : perfectCore P1 ≤
      Subgroup.normalizer ((E2.star (H ⊓ M) H (T ⊓ K) : Subgroup (E2.StarQuot (H ⊓ M) H)) :
        Set (E2.StarQuot (H ⊓ M) H)) := by
    intro w hw
    rw [← star_K1 (c := c) hP1] at hw
    obtain ⟨h, hhK1, rfl⟩ := Case2a.exists_of_mem_star hw
    have hmem : (h : E2.StarQuot (H ⊓ M) H) ∈ E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K) :=
      GoldS146R.mem_imgJ.mpr ⟨h, ⟨⟨h.2, hKM hhK1⟩, K1_le P1 hhK1⟩, rfl⟩
    rw [Case2a.star_inf_eq c hB] at hmem
    exact hmem.2
  have : (E2.star (H ⊓ M) H (T ⊓ K) |>.subgroupOf (perfectCore P1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUperf).mpr hWN
  have hsyl : IsSylowTwoOf (E2.star (H ⊓ M) H (T ⊓ K)) (perfectCore P1) :=
    B6.isSylowTwoOf_mono hUsyl hUperf ((perfectCore_le P1).trans hP1)
  have h2 : IsPGroup 2 ((E2.star (H ⊓ M) H (T ⊓ K)).subgroupOf (perfectCore P1)) :=
    hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hUperf).symm
  exact false_of_normal_sylow hm hF g hg h2 hsyl.2.2

theorem borel_le_K1 {P1 : Subgroup (E2.StarQuot (H ⊓ M) H)} (hP1 : P1 ≤ E2.star (H ⊓ M) H K)
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)))
    (hUsyl : IsSylowTwoOf (E2.star (H ⊓ M) H (T ⊓ K)) (E2.star (H ⊓ M) H K))
    (hUP : E2.star (H ⊓ M) H (T ⊓ K) ≤ P1)
    (hUperf : E2.star (H ⊓ M) H (T ⊓ K) ≤ perfectCore P1) :
    K1 c P1 ⊓ Subgroup.normalizer ((T ⊓ K1 c P1 : Subgroup G) : Set G) ≤ M := by
  rintro x ⟨hxK1, hxN⟩
  have hYH : K1 c P1 ≤ H := (K1_le P1).trans c.le_H
  have hxH : x ∈ H := hYH hxK1
  have hJH := Case2a.kerIn_le_H M H
  have hst : IsSylowTwoOf (E2.star (H ⊓ M) H (T ⊓ K1 c P1)) (E2.star (H ⊓ M) H (K1 c P1)) :=
    Case2a.isSylowTwoOf_star hYH (sylow_K1 hUP)
  have hle : E2.star (H ⊓ M) H (T ⊓ K1 c P1) ≤ E2.star (H ⊓ M) H (T ⊓ K) :=
    GoldS146R.imgJ_mono (inf_le_inf_left T (K1_le P1))
  have hUs_le : E2.star (H ⊓ M) H (T ⊓ K) ≤ E2.star (H ⊓ M) H (K1 c P1) := by
    rw [star_K1 (c := c) hP1]
    exact hUperf
  have heq : E2.star (H ⊓ M) H (T ⊓ K) = E2.star (H ⊓ M) H (T ⊓ K1 c P1) :=
    hst.eq_of_le hle hUs_le hUsyl.2.1
  have hmem : ((⟨x, hxH⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈
      E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K) := by
    rw [Case2a.star_inf_eq c hB]
    refine ⟨(Case2a.mem_star_iff c.le_H hJH _).mpr (Subgroup.mem_sup_left (K1_le P1 hxK1)), ?_⟩
    rw [heq]
    exact Case2a.mk_mem_normalizer_star (inf_le_right.trans hYH) hJH hxN
  rw [Case2a.mem_star_iff (inf_le_left.trans inf_le_left) hJH] at hmem
  exact ((sup_le inf_le_left kerIn_le : (H ⊓ M) ⊓ K ⊔ kerIn (H ⊓ M) H ≤ H ⊓ M) hmem).2

end Levi2

end Fields2

end CFSG.Quasithin.F146Field.Case2b
