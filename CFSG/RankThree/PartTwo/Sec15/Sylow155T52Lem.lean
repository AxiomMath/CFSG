module

public import CFSG.Assembly.Defs
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Lift
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155T52

variable {M : Type*} [Group M] [Finite M]

private theorem mem_of_pow_three_eq_one {E P : Subgroup M}
    (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hEmax : ∀ E' : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E' → E ≤ E' → E' = E)
    (hPE : P ≤ Subgroup.centralizer (E : Set M)) {x : M} (hx : x ∈ P) (hx3 : x ^ 3 = 1) :
    x ∈ E := by
  by_contra hxE
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hE', -⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hE hxE hx3
    (fun e he => Subgroup.mem_centralizer_iff.mp (hPE hx) e he)
  apply hxE
  rw [← hEmax _ hE' le_sup_left]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

private theorem mem_normalizer_of_conj_mem {E : Subgroup M} {g : M}
    (hg : ∀ e ∈ E, g * e * g⁻¹ ∈ E) : g ∈ Subgroup.normalizer (E : Set M) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective
    (MulAut.conj g).injective).ge
  rintro _ ⟨e, he, rfl⟩
  exact hg e he

theorem exists_mem_normalizer_not_commute (N : Subgroup M) [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {E : Subgroup M} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hEmax : ∀ E' : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E' → E ≤ E' → E' = E)
    {Y : Subgroup (M ⧸ N)} (hYn : ∀ q : M ⧸ N, q ∈ Subgroup.normalizer (Y : Set (M ⧸ N)))
    {u : M ⧸ N} (huY : u ∈ Y) (hu3 : u ^ 3 = 1) {y : M ⧸ N} (hyY : y ∈ Y) (huy : u * y ≠ y * u)
    (hEY : ∀ e ∈ E, QuotientGroup.mk' N e ∈ Y → ∀ z ∈ Y,
      QuotientGroup.mk' N e * z = z * QuotientGroup.mk' N e) :
    ∃ d ∈ Subgroup.normalizer (E : Set M), (∃ k : ℕ, d ^ 3 ^ k = 1) ∧
      ∃ e ∈ E, d * e * d⁻¹ ≠ e := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hH
  push Not at hH
  have hEc : E ≤ Subgroup.centralizer (E : Set M) := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨x, hx⟩)
  set Ps : Set (Subgroup M) :=
    {P | IsPGroup 3 P ∧ E ≤ P ∧ P ≤ Subgroup.centralizer (E : Set M)}
  have hfin : Finite (Subgroup M) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨P, ⟨hP3, hEP, hPc⟩, hPmax⟩ :=
    (Set.toFinite Ps).exists_maximal ⟨E, hE.isPGroup, le_rfl, hEc⟩
  have hΩ : ∀ x ∈ P, x ^ 3 = 1 → x ∈ E := fun x hx hx3 =>
    mem_of_pow_three_eq_one hE hEmax hPc hx hx3
  obtain ⟨S, hPS⟩ := hP3.exists_le_sylow
  have hPeq : P = S := by
    by_contra hne
    have hlt : P.subgroupOf S < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hne
      refine le_antisymm hPS fun x hx => ?_
      have hx' : (⟨x, hx⟩ : (S : Subgroup M)) ∈ P.subgroupOf S := htop ▸ Subgroup.mem_top _
      exact hx'
    haveI : Group.IsNilpotent (S : Subgroup M) := S.isPGroup'.isNilpotent
    obtain ⟨g, hgN, hgP⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hlt)
    have hgPn : ∀ x ∈ P, (g : M) * x * (g : M)⁻¹ ∈ P := by
      intro x hx
      have h := (Subgroup.mem_normalizer_iff.mp hgN ⟨x, hPS hx⟩).mp hx
      exact h
    have hgE : (g : M) ∈ Subgroup.normalizer (E : Set M) := by
      refine mem_normalizer_of_conj_mem fun e he => hΩ _ (hgPn e (hEP he)) ?_
      rw [show (g : M) * e * (g : M)⁻¹ = MulAut.conj (g : M) e from rfl, ← map_pow,
        hE.2 e he, map_one]
    obtain ⟨k, hk⟩ := S.isPGroup' g
    have hk' : (g : M) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hgc := hH _ hgE ⟨k, hk'⟩
    have hP'S : P ⊔ Subgroup.zpowers (g : M) ≤ S :=
      sup_le hPS (Subgroup.zpowers_le.mpr g.2)
    have hP'c : P ⊔ Subgroup.zpowers (g : M) ≤ Subgroup.centralizer (E : Set M) := by
      refine sup_le hPc (Subgroup.zpowers_le.mpr ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have h1 := hgc e he
      calc e * (g : M) = ((g : M) * e * (g : M)⁻¹) * (g : M) := by rw [h1]
        _ = (g : M) * e := by group
    have hle := hPmax ⟨S.isPGroup'.to_le hP'S, hEP.trans le_sup_left, hP'c⟩ le_sup_left
    exact hgP (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  have hπs : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  set T : Sylow 3 (M ⧸ N) := S.mapSurjective hπs with hTdef
  have hu : IsPGroup 3 (Subgroup.zpowers u) := by
    rintro ⟨x, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change ((fun n : ℤ => u ^ n) k) ^ 3 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3, one_zpow]
  obtain ⟨T', hT'⟩ := hu.exists_le_sylow
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq (M ⧸ N) T' T
  have hu'T : q * u * q⁻¹ ∈ (T : Subgroup (M ⧸ N)) := by
    rw [← hq, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨u, hT' (Subgroup.mem_zpowers u), rfl⟩
  have hTmap : (T : Subgroup (M ⧸ N)) = P.map (QuotientGroup.mk' N) := by
    rw [hTdef, Sylow.coe_mapSurjective, hPeq]
  rw [hTmap] at hu'T
  obtain ⟨x, hxP, hxu⟩ := hu'T
  have hx3 : x ^ 3 = 1 := by
    have hinj := Sylow155T51.injective_mk_comp_subtype N hN hP3
    have h1 : ((QuotientGroup.mk' N).comp P.subtype) (⟨x, hxP⟩ ^ 3) =
        ((QuotientGroup.mk' N).comp P.subtype) 1 := by
      rw [map_pow, map_one]
      change QuotientGroup.mk' N x ^ 3 = 1
      rw [hxu, show q * u * q⁻¹ = MulAut.conj q u from rfl, ← map_pow, hu3, map_one]
    simpa using congrArg Subtype.val (hinj h1)
  have hxE : x ∈ E := hΩ x hxP hx3
  have hu'Y : QuotientGroup.mk' N x ∈ Y := by
    rw [hxu]
    exact (Subgroup.mem_normalizer_iff.mp (hYn q) u).mp huY
  have hy'Y : q * y * q⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hYn q) y).mp hyY
  have hc := hEY x hxE hu'Y _ hy'Y
  rw [hxu] at hc
  apply huy
  have h2 : q * (u * y) * q⁻¹ = q * (y * u) * q⁻¹ := by
    calc q * (u * y) * q⁻¹ = (q * u * q⁻¹) * (q * y * q⁻¹) := by group
      _ = (q * y * q⁻¹) * (q * u * q⁻¹) := hc
      _ = q * (y * u) * q⁻¹ := by group
  simpa using h2

end CFSG.RankThree.PartTwo.Sec15.Sylow155T52
