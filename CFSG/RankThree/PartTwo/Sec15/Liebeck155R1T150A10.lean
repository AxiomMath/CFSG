module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Tau
import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Alt
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent162
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds

open Equiv Equiv.Perm

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150.A10

private def t0 : Perm (Fin 10) := c[0, 1, 2]
private def b1 : Perm (Fin 10) := c[3, 4, 5]
private def b2 : Perm (Fin 10) := c[6, 7, 8]
private def g0 : Perm (Fin 10) := swap 0 3 * swap 1 4 * swap 2 5 * swap 7 8

private def fB (x : Multiplicative (ZMod 3 × ZMod 3)) : Perm (Fin 10) :=
  b1 ^ (Multiplicative.toAdd x).1.val * b2 ^ (Multiplicative.toAdd x).2.val

private theorem fB_one : fB 1 = 1 := by decide
private theorem fB_mul : ∀ x y, fB (x * y) = fB x * fB y := by decide
private theorem fB_inj : Function.Injective fB := by
  intro x y h
  revert x y h
  decide

private theorem t0_pow_three : t0 ^ 3 = 1 := by decide
private theorem t0_isThreeCycle : t0.IsThreeCycle := card_support_eq_three_iff.mp (by decide)
private theorem orderOf_t0 : orderOf t0 = 3 := orderOf_eq_prime t0_pow_three (by decide)
private theorem b1_not_mem : b1 ∉ Subgroup.zpowers t0 := by
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_t0]
  decide
private theorem sign_g0 : sign g0 = 1 := by decide
private theorem g0_t0 : g0 * t0 * g0⁻¹ = b1 := by decide

private def homB : Multiplicative (ZMod 3 × ZMod 3) →* Perm (Fin 10) where
  toFun := fB
  map_one' := fB_one
  map_mul' := fB_mul

private def B0 : Subgroup (Perm (Fin 10)) := homB.range

private theorem card_B0 : Nat.card B0 = 9 := by
  rw [B0, ← Nat.card_congr (MonoidHom.ofInjective (f := homB) fB_inj).toEquiv]
  rw [Nat.card_eq_fintype_card]
  rfl

private theorem B0_sign : ∀ x, sign (fB x) = 1 := by decide
private theorem B0_disj : ∀ x, Disjoint (fB x).support t0.support := by decide
private theorem g0_fB : ∀ x, g0 * fB x * g0⁻¹ =
    t0 ^ (Multiplicative.toAdd x).1.val *
      fB (Multiplicative.ofAdd (0, 2 * (Multiplicative.toAdd x).2)) := by
  decide

private theorem b1_mem_B0 : b1 ∈ B0 := ⟨Multiplicative.ofAdd (1, 0), by decide⟩

private theorem g0_le : (Subgroup.zpowers t0 ⊔ B0).map (MulAut.conj g0).toMonoidHom ≤
    Subgroup.zpowers t0 ⊔ B0 := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
    show g0 * t0 * g0⁻¹ ∈ _
    rw [g0_t0]
    exact Subgroup.mem_sup_right b1_mem_B0
  · rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_comap]
    show g0 * fB x * g0⁻¹ ∈ _
    rw [g0_fB]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
      (Subgroup.mem_sup_right ⟨_, rfl⟩)

private theorem g0_mem_normalizer : g0 ∈ Subgroup.normalizer
    ((Subgroup.zpowers t0 ⊔ B0 : Subgroup (Perm (Fin 10))) : Set _) := by
  set E := (Subgroup.zpowers t0 ⊔ B0 : Subgroup (Perm (Fin 10))) with hE
  have heq : E.map (MulAut.conj g0).toMonoidHom = E :=
    Subgroup.eq_of_le_of_card_ge g0_le (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g0).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← heq]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨h', hh', hEq⟩ := hh
    have : h' = h := by
      have := hEq
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      exact mul_left_cancel (mul_right_cancel this)
    rw [← this]
    exact hh'

private def F0 : Subgroup (Perm (Fin 10)) :=
  ((alternatingGroup.ofSubtype t0.supportᶜ).range).map (alternatingGroup (Fin 10)).subtype

private theorem mem_F0 {x : Perm (Fin 10)} :
    x ∈ F0 ↔ x ∈ alternatingGroup (Fin 10) ∧ Disjoint x.support t0.support := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, alternatingGroup.mem_range_ofSubtype_iff] at hy
    exact ⟨y.2, Finset.subset_compl_iff_disjoint_right.mp hy⟩
  · rintro ⟨hx, hd⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, alternatingGroup.mem_range_ofSubtype_iff]
    exact Finset.subset_compl_iff_disjoint_right.mpr hd

private instance : Nontrivial ↥(t0.supportᶜ : Finset (Fin 10)) :=
  ⟨⟨⟨3, by decide⟩, ⟨4, by decide⟩, by decide⟩⟩

private theorem card_F0 : Nat.card F0 = 2520 := by
  rw [F0, Subgroup.card_map_of_injective (alternatingGroup (Fin 10)).subtype_injective,
    ← Nat.card_congr (MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).toEquiv,
    Nat.card_eq_fintype_card, card_alternatingGroup]
  rw [Fintype.card_coe, Finset.card_compl]
  decide

private theorem B0_le_F0 : B0 ≤ F0 := by
  rintro _ ⟨x, rfl⟩
  exact mem_F0.mpr ⟨(mem_alternatingGroup).mpr (B0_sign x), B0_disj x⟩

public theorem perm10_exists_move (s : Perm (Fin 10)) (hs : s.IsThreeCycle)
    (B : Subgroup (Perm (Fin 10))) (hBalt : B ≤ alternatingGroup (Fin 10))
    (hBdisj : ∀ b ∈ B, Disjoint b.support s.support) (hB9 : Nat.card B = 9) :
    ∃ g ∈ alternatingGroup (Fin 10),
      g ∈ Subgroup.normalizer ((Subgroup.zpowers s ⊔ B : Subgroup (Perm (Fin 10))) : Set _) ∧
      g * s * g⁻¹ ∉ Subgroup.zpowers s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π, hπ⟩ : ∃ π : Perm (Fin 10), π * s * π⁻¹ = t0 := by
    have : IsConj s t0 := isConj_iff_cycleType_eq.mpr (hs.trans t0_isThreeCycle.symm)
    exact isConj_iff.mp this
  set B' := B.map (MulAut.conj π).toMonoidHom with hB'
  have hsupp : t0.support = s.support.map π.toEmbedding := by
    rw [← hπ, support_conj]
  have hB'F : B' ≤ F0 := by
    rintro _ ⟨b, hb, rfl⟩
    refine mem_F0.mpr ⟨?_, ?_⟩
    · show π * b * π⁻¹ ∈ alternatingGroup (Fin 10)
      exact (alternatingGroup.normal (α := Fin 10)).conj_mem b (hBalt hb) π
    · show Disjoint (π * b * π⁻¹).support t0.support
      rw [support_conj, hsupp, Finset.disjoint_map]
      exact hBdisj b hb
  have hB'9 : Nat.card B' = 9 := by
    rw [hB', Subgroup.card_map_of_injective (MulAut.conj π).injective]
    exact hB9
  have hcardF : Nat.card ↥F0 = 2520 := card_F0
  have hsyl : ∀ P : Subgroup (Perm (Fin 10)), P ≤ F0 → Nat.card P = 9 →
      ∃ S : Sylow 3 ↥F0, (S : Subgroup ↥F0) = P.subgroupOf F0 := by
    intro P hPF hP9
    have hc : Nat.card (P.subgroupOf F0) = 9 := by
      rw [← hP9]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPF).toEquiv
    have hp : IsPGroup 3 (P.subgroupOf F0) := IsPGroup.of_card (n := 2) (by rw [hc]; norm_num)
    have hi : ¬ 3 ∣ (P.subgroupOf F0).index := by
      have h := Subgroup.card_mul_index (P.subgroupOf F0)
      rw [hc, hcardF] at h
      omega
    exact ⟨hp.toSylow hi, IsPGroup.toSylow_coe hp hi⟩
  obtain ⟨S₁, hS₁⟩ := hsyl B' hB'F hB'9
  obtain ⟨S₂, hS₂⟩ := hsyl B0 B0_le_F0 card_B0
  obtain ⟨κ, hκ⟩ := MulAction.exists_smul_eq ↥F0 S₁ S₂
  have hκt : (κ : Perm (Fin 10)) * t0 * (κ : Perm (Fin 10))⁻¹ = t0 := by
    have hd := (mem_F0.mp κ.2).2
    have hc : Commute (κ : Perm (Fin 10)) t0 := (disjoint_iff_disjoint_support.mpr hd).commute
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hκB : B'.map (MulAut.conj (κ : Perm (Fin 10))).toMonoidHom = B0 := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      have hxS₂ : (⟨x, B0_le_F0 hx⟩ : ↥F0) ∈ (S₂ : Subgroup ↥F0) := by
        rw [hS₂, Subgroup.mem_subgroupOf]; exact hx
      rw [← hκ, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxS₂
      obtain ⟨y, hy, hyx⟩ := hxS₂
      rw [hS₁, Subgroup.mem_subgroupOf] at hy
      refine ⟨y, hy, ?_⟩
      have := congrArg Subtype.val hyx
      simpa using this
    · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hB'9, card_B0]
  set ρ : Perm (Fin 10) := (κ : Perm (Fin 10)) * π with hρ
  have hρs : ρ * s * ρ⁻¹ = t0 := by
    rw [hρ, mul_inv_rev, show (κ : Perm (Fin 10)) * π * s * (π⁻¹ * (κ : Perm (Fin 10))⁻¹) =
      (κ : Perm (Fin 10)) * (π * s * π⁻¹) * (κ : Perm (Fin 10))⁻¹ by group, hπ, hκt]
  have hρB : B.map (MulAut.conj ρ).toMonoidHom = B0 := by
    rw [← hκB, hB', Subgroup.map_map]
    congr 1
  have hρE : (Subgroup.zpowers s ⊔ B).map (MulAut.conj ρ).toMonoidHom =
      Subgroup.zpowers t0 ⊔ B0 := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hρB]
    congr 2
  refine ⟨ρ⁻¹ * g0 * ρ, ?_, ?_, ?_⟩
  · rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, sign_g0, mul_one,
      Int.units_mul_self]
  · have hn := g0_mem_normalizer
    rw [← hρE, ← Subgroup.map_equiv_normalizer_eq] at hn
    obtain ⟨g, hg, hgg⟩ := hn
    have : g = ρ⁻¹ * g0 * ρ := by
      have h2 : ρ * g * ρ⁻¹ = g0 := by simpa [MulAut.conj_apply] using hgg
      rw [← h2]; group
    rw [← this]; exact hg
  · intro h
    have h1 : ρ * (ρ⁻¹ * g0 * ρ * s * (ρ⁻¹ * g0 * ρ)⁻¹) * ρ⁻¹ ∈
        (Subgroup.zpowers s).map (MulAut.conj ρ).toMonoidHom := ⟨_, h, rfl⟩
    rw [MonoidHom.map_zpowers] at h1
    have h2 : ρ * (ρ⁻¹ * g0 * ρ * s * (ρ⁻¹ * g0 * ρ)⁻¹) * ρ⁻¹ = g0 * t0 * g0⁻¹ := by
      rw [← hρs]; group
    have h3 : (MulAut.conj ρ).toMonoidHom s = t0 := by simpa [MulAut.conj_apply] using hρs
    rw [h2, g0_t0, h3] at h1
    exact b1_not_mem h1

public theorem alt10_exists_move (s : alternatingGroup (Fin 10))
    (hs : (s : Perm (Fin 10)).IsThreeCycle) (B : Subgroup (alternatingGroup (Fin 10)))
    (hBdisj : ∀ b ∈ B, Disjoint (b : Perm (Fin 10)).support (s : Perm (Fin 10)).support)
    (hB9 : Nat.card B = 9) :
    ∃ g : alternatingGroup (Fin 10),
      (∀ w ∈ Subgroup.zpowers s ⊔ B, g * w * g⁻¹ ∈ Subgroup.zpowers s ⊔ B) ∧
        g * s * g⁻¹ ∉ Subgroup.zpowers s := by
  set ι := (alternatingGroup (Fin 10)).subtype with hι
  have hιinj : Function.Injective ι := Subgroup.subtype_injective _
  obtain ⟨g, hg, hgN, hgs⟩ := perm10_exists_move (s : Perm (Fin 10)) hs (B.map ι)
    (Subgroup.map_subtype_le B) (by rintro _ ⟨b, hb, rfl⟩; exact hBdisj b hb)
    (by rw [Subgroup.card_map_of_injective hιinj]; exact hB9)
  have hE : (Subgroup.zpowers s ⊔ B).map ι = Subgroup.zpowers (s : Perm (Fin 10)) ⊔ B.map ι := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  refine ⟨⟨g, hg⟩, fun w hw => ?_, fun h => ?_⟩
  · have h1 : ι w ∈ (Subgroup.zpowers s ⊔ B).map ι := Subgroup.mem_map_of_mem ι hw
    rw [hE] at h1
    have h2 := (Subgroup.mem_normalizer_iff.mp hgN (ι w)).mp h1
    rw [← hE] at h2
    rw [← Subgroup.mem_map_iff_mem hιinj]
    exact h2
  · apply hgs
    have h1 : ι (⟨g, hg⟩ * s * (⟨g, hg⟩ : alternatingGroup (Fin 10))⁻¹) ∈
        (Subgroup.zpowers s).map ι := Subgroup.mem_map_of_mem ι h
    rw [MonoidHom.map_zpowers] at h1
    exact h1

public theorem alt10_conj_injective : Function.Injective
    (MulAut.conj : alternatingGroup (Fin 10) →* MulAut (alternatingGroup (Fin 10))) := by
  intro x y h
  have hZ : Subgroup.center (alternatingGroup (Fin 10)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hz : y⁻¹ * x ∈ Subgroup.center (alternatingGroup (Fin 10)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h' := congrArg (fun φ : MulAut (alternatingGroup (Fin 10)) => φ g) h
    simp only [MulAut.conj_apply] at h'
    calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹) * x := by group
      _ = y⁻¹ * (x * g * x⁻¹) * x := by rw [h']
      _ = y⁻¹ * x * g := by group
  rw [hZ, Subgroup.mem_bot] at hz
  exact (inv_mul_eq_one.mp hz).symm

public theorem alt10_conj_threeCycle {σ : MulAut (alternatingGroup (Fin 10))} (h3 : σ ^ 3 = 1)
    (h1 : σ ≠ 1) {K : Subgroup (alternatingGroup (Fin 10))} (hK : K ≤ Sec4.autFix σ)
    [Group.IsPerfect K] (hKc : 9 ∣ Nat.card K) :
    ∃ s : alternatingGroup (Fin 10), MulAut.conj s = σ ∧ (s : Perm (Fin 10)).IsThreeCycle ∧
      K ≤ (alternatingGroup.ofSubtype (s : Perm (Fin 10)).supportᶜ).range := by
  obtain ⟨s, rfl⟩ := Sec4.cubeInner_of_not_three_dvd_card_outer
    (Sec4.RonanK429.not_three_dvd_outer_alternatingGroup (by norm_num : 5 ≤ 10)) σ h3
  have hs3 : s ^ 3 = 1 := by
    have h' : MulAut.conj (s ^ 3) = MulAut.conj 1 := by rw [map_pow, h3, map_one]
    exact alt10_conj_injective h'
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact h1 (map_one _)
  set τ : Perm (Fin 10) := (s : Perm (Fin 10)) with hτ
  have hτ3 : τ ^ 3 = 1 := by
    have := congrArg Subtype.val hs3
    simpa [hτ] using this
  have hτ1 : τ ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hord : orderOf τ ∣ 3 := orderOf_dvd_of_pow_eq_one hτ3
  have hmem : ∀ m ∈ τ.cycleType, m = 3 := fun m hm => by
    have h2 := two_le_of_mem_cycleType hm
    have hd := (dvd_of_mem_cycleType hm).trans hord
    have : m ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    interval_cases m
    · norm_num at hd
    · rfl
  set k := Multiset.card τ.cycleType with hk
  have hrep : τ.cycleType = Multiset.replicate k 3 := Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hsupp : τ.support.card = 3 * k := by
    rw [← sum_cycleType, hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hsum : 3 * k ≤ 10 := by
    have := τ.support.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr fun h0 =>
    hτ1 (card_cycleType_eq_zero.mp (by rw [← hk]; exact h0))
  have hconj : MulAut.conj s = CFSG.Quasithin.SteinbergCB.conjPerm 10 τ := by
    ext x
    rw [CFSG.Quasithin.SteinbergCB.conjPerm_apply]
    rfl
  have hKR : K ≤ (alternatingGroup.ofSubtype τ.supportᶜ).range := by
    rw [hconj] at hK
    exact Sec4.Ronan148R.le_range_ofSubtype_of_card_cycleType_le (by omega) hK
  have hΩ : Fintype.card ↥(τ.supportᶜ) = 10 - 3 * k := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hsupp]
  have hdvd : Nat.card K ∣ Nat.card (alternatingGroup.ofSubtype τ.supportᶜ).range :=
    Subgroup.card_dvd_of_le hKR
  have hcardR : Nat.card (alternatingGroup.ofSubtype τ.supportᶜ).range =
      Nat.card (alternatingGroup ↥(τ.supportᶜ)) :=
    (Nat.card_congr (MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).toEquiv).symm
  have hdvd2 : Nat.card (alternatingGroup ↥(τ.supportᶜ)) ∣ (10 - 3 * k).factorial := by
    rw [← hΩ, ← Fintype.card_perm, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card _
  have hk1' : k = 1 := by
    by_contra hne
    have h24 : (10 - 3 * k).factorial ∣ 24 :=
      (Nat.factorial_dvd_factorial (by omega : 10 - 3 * k ≤ 4)).trans (by decide)
    have h9 := hKc.trans (hdvd.trans (hcardR ▸ hdvd2)) |>.trans h24
    omega
  refine ⟨s, rfl, ?_, hKR⟩
  show τ.cycleType = {3}
  rw [hrep, hk1']
  rfl

section Frattini

variable {H S : Type*} [Group H] [Finite H] [Group S]

public theorem le_sylow_eq (ρ : H →* MulAut S) {A : Subgroup H}
    (hAinj : ∀ a ∈ A, ρ a = 1 → a = 1)
    (hcent : ∀ x ∈ Subgroup.centralizer (A : Set H), x ^ 3 = 1 → x ∈ A)
    (T : Subgroup H) (hT3 : IsPGroup 3 T) (hAT : A ≤ T) (hTN : T ≤ (A.map ρ).comap ρ) :
    T = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  have hlt : ¬ T ≤ A := fun h => hne (le_antisymm h hAT)
  obtain ⟨t, htT, htA⟩ := Set.not_subset.mp hlt
  obtain ⟨a, haA, hat⟩ := hTN htT
  set M : Subgroup T := (ρ.ker).subgroupOf T with hM
  have hMne : M ≠ ⊥ := by
    intro hbot
    have hk : (⟨a⁻¹ * t, T.mul_mem (T.inv_mem (hAT haA)) htT⟩ : T) ∈ M := by
      rw [hM, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, map_mul, map_inv, hat, inv_mul_cancel]
    rw [hbot, Subgroup.mem_bot] at hk
    have : a⁻¹ * t = 1 := congrArg Subtype.val hk
    exact htA (by rw [← (eq_of_inv_mul_eq_one this)]; exact haA)
  have : M.Normal := by rw [hM]; infer_instance
  have : Group.IsNilpotent T := hT3.isNilpotent
  obtain ⟨⟨z, hzMZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hMne)
  have hzM : z ∈ M := (Subgroup.mem_inf.mp hzMZ).1
  have hzZ : z ∈ Subgroup.center T := (Subgroup.mem_inf.mp hzMZ).2
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hdvd : 3 ∣ Nat.card (Subgroup.zpowers z) := by
    rw [Nat.card_zpowers]
    obtain ⟨e, he⟩ := hT3 z
    have hd : orderOf z ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one he
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hio
      exact hz1' hio
    rw [hio]
    exact dvd_pow_self 3 hi0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers z) 3 hdvd
  have hwM : (w : T) ∈ M := (Subgroup.zpowers_le.mpr hzM) w.2
  have hwZ : (w : T) ∈ Subgroup.center T := (Subgroup.zpowers_le.mpr hzZ) w.2
  have hw3 : ((w : T) : H) ^ 3 = 1 := by
    have := pow_orderOf_eq_one w
    rw [hw] at this
    have := congrArg (fun x : Subgroup.zpowers z => ((x : T) : H)) this
    simpa using this
  have hwC : ((w : T) : H) ∈ Subgroup.centralizer (A : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := Subgroup.mem_center_iff.mp hwZ ⟨a, hAT ha⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    exact h2
  have hwA := hcent _ hwC hw3
  have hwk : ρ ((w : T) : H) = 1 := by
    have := hwM
    rw [hM, Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at this
    exact this
  have hw1 := hAinj _ hwA hwk
  have : orderOf w = 1 := by
    rw [orderOf_eq_one_iff]
    exact Subtype.ext (Subtype.ext hw1)
  rw [hw] at this
  exact absurd this (by norm_num)

public theorem exists_normalizer_moving (ρ : H →* MulAut S) {A : Subgroup H}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA3 : IsPGroup 3 A)
    (hAinj : ∀ a ∈ A, ρ a = 1 → a = 1)
    (hcent : ∀ x ∈ Subgroup.centralizer (A : Set H), x ^ 3 = 1 → x ∈ A)
    {c : H} (hc : c ∈ A) {h : H}
    (hhN : ∀ a ∈ A, ∃ a' ∈ A, ρ (h * a * h⁻¹) = ρ a')
    (hhc : ∀ k : ℤ, ρ (h * c * h⁻¹) ≠ ρ (c ^ k)) :
    ∃ y ∈ Subgroup.normalizer (A : Set H), y * c * y⁻¹ ∉ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup H := (A.map ρ).comap ρ with hN
  have hAN : A ≤ N := Subgroup.le_comap_map ρ A
  set A' : Subgroup H := A.map (MulAut.conj h).toMonoidHom with hA'
  have hA'N : A' ≤ N := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨a', ha', he⟩ := hhN a ha
    exact ⟨a', ha', he.symm⟩
  have hAN3 : IsPGroup 3 (A.subgroupOf N) :=
    hA3.of_equiv (Subgroup.subgroupOfEquivOfLe hAN).symm
  obtain ⟨Q, hQ⟩ := hAN3.exists_le_sylow
  have hQA : ((Q : Subgroup N).map N.subtype) = A := by
    refine le_sylow_eq ρ hAinj hcent _ (Q.isPGroup'.map N.subtype) ?_ ?_
    · intro a ha
      exact ⟨⟨a, hAN ha⟩, hQ (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
  have hQeq : (Q : Subgroup N) = A.subgroupOf N := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf, ← hQA]
      exact ⟨x, hx, rfl⟩
    · intro hx; exact hQ hx
  have hcardA' : Nat.card (A'.subgroupOf N) = Nat.card (Q : Subgroup N) := by
    rw [hQeq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'N).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hA',
      Subgroup.card_map_of_injective (MulAut.conj h).injective]
  let Q' : Sylow 3 N := Sylow.ofCard (A'.subgroupOf N) (by rw [hcardA', Q.card_eq_multiplicity])
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N Q' Q
  set y : H := (n : H) * h with hy
  have hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A := by
    intro a ha
    have h1 : (⟨h * a * h⁻¹, hA'N ⟨a, ha, rfl⟩⟩ : N) ∈ (Q' : Subgroup N) := by
      show (⟨h * a * h⁻¹, _⟩ : N) ∈ A'.subgroupOf N
      rw [Subgroup.mem_subgroupOf]
      exact ⟨a, ha, rfl⟩
    have h2 : n * (⟨h * a * h⁻¹, hA'N ⟨a, ha, rfl⟩⟩ : N) * n⁻¹ ∈ (Q : Subgroup N) := by
      rw [← hn, Sylow.coe_subgroup_smul]
      exact ⟨_, h1, rfl⟩
    rw [hQeq, Subgroup.mem_subgroupOf] at h2
    have : (((n * (⟨h * a * h⁻¹, hA'N ⟨a, ha, rfl⟩⟩ : N) * n⁻¹ : N)) : H) = y * a * y⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy, mul_inv_rev]
      group
    rw [this] at h2
    exact h2
  have hyN : y ∈ Subgroup.normalizer (A : Set H) := by
    have hle : A.map (MulAut.conj y).toMonoidHom ≤ A := by
      rintro _ ⟨a, ha, rfl⟩
      exact hyA a ha
    have heq : A.map (MulAut.conj y).toMonoidHom = A :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective (MulAut.conj y).injective])
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact hyA x hx
    · intro hx
      rw [← heq] at hx
      obtain ⟨x', hx', hxe⟩ := hx
      have : x' = x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxe
        exact mul_left_cancel (mul_right_cancel hxe)
      rw [← this]; exact hx'
  refine ⟨y, hyN, ?_⟩
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  obtain ⟨an, han, hρn⟩ := n.2
  obtain ⟨ac, hac, hρc⟩ := hhN c hc
  have hcomm : ρ an * ρ ac = ρ ac * ρ an := by
    rw [← map_mul, ← map_mul, hAab an han ac hac]
  have hρy : ρ (y * c * y⁻¹) = ρ (h * c * h⁻¹) := by
    have : y * c * y⁻¹ = (n : H) * (h * c * h⁻¹) * (n : H)⁻¹ := by rw [hy]; group
    rw [this, map_mul, map_mul, map_inv, hρc, ← hρn, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  exact hhc k (by rw [← hρy, ← hk])

end Frattini

section Abstract

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank

public theorem coe_mem_normalizer_of_subgroupOf {G : Type*} [Group G] {H A : Subgroup G}
    (hAH : A ≤ H) {y : ↥H}
    (hy : y ∈ Subgroup.normalizer ((A.subgroupOf H : Subgroup ↥H) : Set ↥H)) :
    (y : G) ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have := (Subgroup.mem_normalizer_iff.mp hy ⟨a, hAH ha⟩).mp (Subgroup.mem_subgroupOf.mpr ha)
    exact Subgroup.mem_subgroupOf.mp this
  · intro ha
    have haH : a ∈ H := by
      have h2 : a = (y : G)⁻¹ * ((y : G) * a * (y : G)⁻¹) * (y : G) := by group
      rw [h2]
      exact H.mul_mem (H.mul_mem (H.inv_mem y.2) (hAH ha)) y.2
    have := (Subgroup.mem_normalizer_iff.mp hy ⟨a, haH⟩).mpr (Subgroup.mem_subgroupOf.mpr ha)
    exact Subgroup.mem_subgroupOf.mp this

variable {Y : Type} [Group Y] [Finite Y]

public theorem exists_normalizer_moving_of_a10 {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y)
    {A : Subgroup Y} (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (Λ : Set Y))
    (hcent : ∀ x ∈ Subgroup.centralizer (A : Set Y), x ^ 3 = 1 → x ∈ A)
    {c : Y} (hcA : c ∈ A) (hc : c ∉ Sec4.thetaQuotCentralizer Λ)
    {L : Subgroup Y} (hLΛ : L ≤ Λ) (hLc : L ≤ Subgroup.centralizer ({c} : Set Y))
    (hLperf : Group.IsPerfect L) {J : Type} [Group J] (hJs : IsSimpleGroup J)
    (φ : ↥L →* J) (hφ : Function.Surjective φ) (hφ3 : ¬ 3 ∣ Nat.card φ.ker)
    (hAL : Nat.card ↥(A ⊓ L) = 9)
    (e : Pump.ThetaCenterQuot Λ ≃* alternatingGroup (Fin 10)) :
    ∃ y ∈ Subgroup.normalizer (A : Set Y), y * c * y⁻¹ ∉ Subgroup.zpowers c := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  let πS : ↥Λ →* Pump.ThetaCenterQuot Λ :=
    (QuotientGroup.mk' (Subgroup.center (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ))).comp
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Λ))
  have hπS : Function.Surjective πS :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  let πe : ↥Λ →* alternatingGroup (Fin 10) := e.toMonoidHom.comp πS
  have hπe : Function.Surjective πe := e.surjective.comp hπS
  set N := Subgroup.normalizer (Λ : Set Y) with hN
  have hΛN : Λ ≤ N := Subgroup.le_normalizer
  let ρ : ↥N →* MulAut (alternatingGroup (Fin 10)) :=
    (MulAut.congr e).toMonoidHom.comp (Pump.actOnS Λ)
  have hρapp : ∀ (x : ↥N) (l : ↥Λ), ρ x (πe l) = πe (Λ.normalizerMonoidHom x l) := by
    intro x l
    show e ((Pump.actOnS Λ x) (e.symm (e (πS l)))) = e (πS (Λ.normalizerMonoidHom x l))
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hinner : ∀ (x : Y) (hx : x ∈ Λ), ρ ⟨x, hΛN hx⟩ = MulAut.conj (πe ⟨x, hx⟩) := by
    intro x hx
    ext t : 1
    obtain ⟨l, rfl⟩ := hπe t
    rw [hρapp, MulAut.conj_apply]
    have h1 : Λ.normalizerMonoidHom ⟨x, hΛN hx⟩ l = ⟨x, hx⟩ * l * ⟨x, hx⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hcN : c ∈ N := hAN hcA
  obtain ⟨cN, hcNc⟩ : ∃ cN : ↥N, (cN : Y) = c := ⟨⟨c, hcN⟩, rfl⟩
  have hcNA : cN ∈ A.subgroupOf N := by rw [Subgroup.mem_subgroupOf, hcNc]; exact hcA
  have hσ3 : ρ cN ^ 3 = 1 := by
    have h : cN ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hcNc, hc3]; rfl)
    rw [← map_pow, h, map_one]
  have hσ1 : ρ cN ≠ 1 := by
    intro h
    apply Pump.actOnS_ne_one hΛ hcN hc
    have hcN' : cN = ⟨c, hcN⟩ := Subtype.ext hcNc
    apply (MulAut.congr e).injective
    rw [map_one, ← hcN']
    exact h
  have : Group.IsPerfect L := hLperf
  have hL'perf : Group.IsPerfect (L.subgroupOf Λ) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLΛ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLΛ).symm.surjective
  set K : Subgroup (alternatingGroup (Fin 10)) := (L.subgroupOf Λ).map πe with hK
  have hKperf : Group.IsPerfect K := Group.IsPerfect.map πe
  have hKfix : K ≤ Sec4.autFix (ρ cN) := by
    rintro _ ⟨l, hl, rfl⟩
    show ρ cN (πe l) = πe l
    rw [hρapp]
    congr 1
    apply Subtype.ext
    show (cN : Y) * (l : Y) * (cN : Y)⁻¹ = l
    have hlc : (l : Y) * c = c * (l : Y) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (Subgroup.mem_subgroupOf.mp hl))
    rw [hcNc, ← hlc, mul_inv_cancel_right]
  have hJp : Group.IsPerfect J := Group.IsPerfect.ofSurjective (f := φ) hφ
  have hJc : Subgroup.center J = ⊥ := Pump.center_eq_bot_of_simple hJs hJp
  have hθΛY : aschbacherSolvableCore 3 ↥Λ = (aschbacherSolvableCore 3 Y).subgroupOf Λ :=
    aschbacherSolvableCore_eq_subgroupOf Nat.prime_three hΛ.2.1
  have hθsol : Group.IsSolvable (aschbacherSolvableCore 3 Y) :=
    (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).1
  have hker0 : (aschbacherSolvableCore 3 Y).subgroupOf L ≤ φ.ker :=
    Pump.le_ker_of_normalizes hJs hJp L (aschbacherSolvableCore 3 Y) hθsol
      (fun m _ k hk => Subgroup.Normal.conj_mem inferInstance k hk m) φ hφ
  have hinj3 : ∀ (l : Y) (hl : l ∈ L), l ^ 3 = 1 → πe ⟨l, hLΛ hl⟩ = 1 → l = 1 := by
    intro l hl hl3 h1
    have h2 : πS ⟨l, hLΛ hl⟩ = 1 := e.injective (h1.trans (map_one e).symm)
    have h3 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Λ) ⟨l, hLΛ hl⟩ ∈
        Subgroup.center (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ) := (QuotientGroup.eq_one_iff _).mp h2
    have h4 : φ ⟨l, hl⟩ = 1 := by
      have hz : φ ⟨l, hl⟩ ∈ Subgroup.center J := by
        rw [Subgroup.mem_center_iff]
        intro j
        obtain ⟨m, rfl⟩ := hφ j
        have hm := Subgroup.mem_center_iff.mp h3
          (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Λ) ⟨(m : Y), hLΛ m.2⟩)
        have hm2 : (((⟨(m : Y), hLΛ m.2⟩ * ⟨l, hLΛ hl⟩ : ↥Λ)) : ↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ) =
            ((⟨l, hLΛ hl⟩ * ⟨(m : Y), hLΛ m.2⟩ : ↥Λ) : ↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ) := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
          exact hm
        have hm3 := QuotientGroup.eq.mp hm2
        rw [hθΛY, Subgroup.mem_subgroupOf] at hm3
        have hmem : (m * ⟨l, hl⟩)⁻¹ * (⟨l, hl⟩ * m) ∈ φ.ker := hker0 (by
          rw [Subgroup.mem_subgroupOf]
          simpa using hm3)
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one] at hmem
        exact hmem
      rw [hJc, Subgroup.mem_bot] at hz
      exact hz
    let k : ↥φ.ker := ⟨⟨l, hl⟩, h4⟩
    have hk3 : k ^ 3 = 1 := Subtype.ext (Subtype.ext (by simpa using hl3))
    have hko : orderOf k ∣ 3 := orderOf_dvd_of_pow_eq_one hk3
    rcases (Nat.dvd_prime Nat.prime_three).mp hko with h | h
    · have := orderOf_eq_one_iff.mp h
      exact congrArg (fun x : ↥φ.ker => ((x : ↥L) : Y)) this
    · exact absurd (h ▸ orderOf_dvd_natCard k) hφ3
  have hALΛ : A ⊓ L ≤ Λ := inf_le_right.trans hLΛ
  set B : Subgroup (alternatingGroup (Fin 10)) := ((A ⊓ L).subgroupOf Λ).map πe with hBdef
  have hBK : B ≤ K := Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
  have hB9 : Nat.card B = 9 := by
    have hinj : Function.Injective (πe.subgroupMap ((A ⊓ L).subgroupOf Λ)) := by
      intro x y hxy
      have h1 : πe ((x : ↥Λ)⁻¹ * (y : ↥Λ)) = 1 := by
        rw [map_mul, map_inv, inv_mul_eq_one]
        exact congrArg Subtype.val hxy
      have hxB := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp x.2)
      have hyB := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp y.2)
      have hmemL : ((x : ↥Λ) : Y)⁻¹ * ((y : ↥Λ) : Y) ∈ L := L.mul_mem (L.inv_mem hxB.2) hyB.2
      have hmemA : ((x : ↥Λ) : Y)⁻¹ * ((y : ↥Λ) : Y) ∈ A := A.mul_mem (A.inv_mem hxB.1) hyB.1
      have h4 := hinj3 _ hmemL (hA.2 _ hmemA) h1
      exact Subtype.ext (Subtype.ext (inv_mul_eq_one.mp h4))
    rw [hBdef, ← Nat.card_congr (Equiv.ofBijective _
      ⟨hinj, MonoidHom.subgroupMap_surjective πe ((A ⊓ L).subgroupOf Λ)⟩),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hALΛ).toEquiv, hAL]
  obtain ⟨s, hsσ, hs3, hKs⟩ := alt10_conj_threeCycle hσ3 hσ1 hKfix
    (by rw [← hB9]; exact Subgroup.card_dvd_of_le hBK)
  have hdisj : ∀ b ∈ B, Disjoint (b : Perm (Fin 10)).support (s : Perm (Fin 10)).support := by
    intro b hb
    have h1 := hKs (hBK hb)
    rw [alternatingGroup.mem_range_ofSubtype_iff] at h1
    exact Finset.subset_compl_iff_disjoint_right.mp h1
  have hKF : ∀ (b : Y) (hb : b ∈ A ⊓ L), ρ ⟨b, hΛN (hALΛ hb)⟩ ≠ ρ cN := by
    intro b hb h
    rw [hinner b (hALΛ hb), ← hsσ] at h
    have hbs : πe ⟨b, hALΛ hb⟩ = s := alt10_conj_injective h
    have hsB : s ∈ B := by
      rw [← hbs]
      exact Subgroup.mem_map_of_mem πe (Subgroup.mem_subgroupOf.mpr hb)
    have h0 : (s : Perm (Fin 10)).support = ∅ := disjoint_self.mp (hdisj s hsB)
    have h3 := hs3.card_support
    rw [h0, Finset.card_empty] at h3
    exact absurd h3 (by norm_num)
  have hnormAL : ∀ x ∈ A,
      Subgroup.zpowers x ≤ Subgroup.normalizer ((A ⊓ L : Subgroup Y) : Set Y) := by
    intro x hx
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      hcommA a (Subgroup.mem_inf.mp ha).1 x hx)
  have hgen : ∀ x ∈ A, x ∉ A ⊓ L → (A ⊓ L) ⊔ Subgroup.zpowers x = A := by
    intro x hxA hxL
    have hDA : (A ⊓ L) ⊔ Subgroup.zpowers x ≤ A := sup_le inf_le_left (Subgroup.zpowers_le.mpr hxA)
    have h9 : 9 ∣ Nat.card ↥((A ⊓ L) ⊔ Subgroup.zpowers x) :=
      hAL ▸ Subgroup.card_dvd_of_le le_sup_left
    have h27 : Nat.card ↥((A ⊓ L) ⊔ Subgroup.zpowers x) ∣ 27 :=
      hA27 ▸ Subgroup.card_dvd_of_le hDA
    have hne : Nat.card ↥((A ⊓ L) ⊔ Subgroup.zpowers x) ≠ 9 := by
      intro h
      have h' := Subgroup.eq_of_le_of_card_ge (le_sup_left : A ⊓ L ≤ (A ⊓ L) ⊔ Subgroup.zpowers x)
        (by rw [h, hAL])
      exact hxL (h' ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
    have hD27 : Nat.card ↥((A ⊓ L) ⊔ Subgroup.zpowers x) = 27 := by
      generalize Nat.card ↥((A ⊓ L) ⊔ Subgroup.zpowers x) = d at h9 h27 hne
      have hle : d ≤ 27 := Nat.le_of_dvd (by norm_num) h27
      interval_cases d <;> omega
    exact Subgroup.eq_of_le_of_card_ge hDA (by rw [hD27, hA27])
  have hAinj : ∀ a ∈ A.subgroupOf N, ρ a = 1 → a = 1 := by
    intro a ha h1
    have haA : (a : Y) ∈ A := Subgroup.mem_subgroupOf.mp ha
    by_cases haL : (a : Y) ∈ A ⊓ L
    · have h2 : ρ ⟨(a : Y), hΛN (hALΛ haL)⟩ = 1 := h1
      rw [hinner _ (hALΛ haL)] at h2
      have h3 : πe ⟨(a : Y), hALΛ haL⟩ = 1 :=
        alt10_conj_injective (h2.trans (map_one MulAut.conj).symm)
      exact Subtype.ext (hinj3 _ (Subgroup.mem_inf.mp haL).2 (hA.2 _ haA) h3)
    · exfalso
      have hcD : c ∈ (((A ⊓ L) ⊔ Subgroup.zpowers (a : Y) : Subgroup Y) : Set Y) := by
        rw [SetLike.mem_coe, hgen _ haA haL]
        exact hcA
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hnormAL _ haA)] at hcD
      obtain ⟨b, hb, w, hw, hbw⟩ := Set.mem_mul.mp hcD
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      apply hKF b hb
      have hcN' : cN = ⟨b, hΛN (hALΛ hb)⟩ * a ^ k :=
        Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_zpow, hcNc]; exact hbw.symm)
      rw [hcN', map_mul, map_zpow, h1, one_zpow, mul_one]
  have hcL : c ∉ A ⊓ L := fun h => hKF c h (by congr 1; exact Subtype.ext hcNc.symm)
  have hAeq : (A ⊓ L) ⊔ Subgroup.zpowers c = A := hgen c hcA hcL
  have hρA : ∀ a ∈ A.subgroupOf N, ∃ w ∈ Subgroup.zpowers s ⊔ B, ρ a = MulAut.conj w := by
    intro a ha
    have haD : (a : Y) ∈ (((A ⊓ L) ⊔ Subgroup.zpowers c : Subgroup Y) : Set Y) := by
      rw [SetLike.mem_coe, hAeq]
      exact Subgroup.mem_subgroupOf.mp ha
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hnormAL _ hcA)] at haD
    obtain ⟨b, hb, w, hw, hbw⟩ := Set.mem_mul.mp haD
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine ⟨πe ⟨b, hALΛ hb⟩ * s ^ k, Subgroup.mul_mem _
      (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem πe (Subgroup.mem_subgroupOf.mpr hb)))
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers s) k)), ?_⟩
    have ha' : a = ⟨b, hΛN (hALΛ hb)⟩ * cN ^ k :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_zpow, hcNc]; exact hbw.symm)
    rw [ha', map_mul, map_zpow, hinner b (hALΛ hb), map_mul, map_zpow, hsσ]
  have hsurjA : Subgroup.zpowers s ⊔ B ≤ ((A.subgroupOf N).map ρ).comap MulAut.conj := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, hsσ]
      exact ⟨cN, hcNA, rfl⟩
    · rintro _ ⟨b₀, hb₀, rfl⟩
      rw [Subgroup.mem_comap]
      have hb₀' : ((b₀ : ↥Λ) : Y) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hb₀
      exact ⟨⟨(b₀ : Y), hΛN b₀.2⟩, Subgroup.mem_subgroupOf.mpr hb₀'.1, hinner (b₀ : Y) b₀.2⟩
  obtain ⟨g, hgN, hgs⟩ := alt10_exists_move s hs3 B hdisj hB9
  obtain ⟨x, rfl⟩ := hπe g
  have hρh : ρ ⟨(x : Y), hΛN x.2⟩ = MulAut.conj (πe x) := hinner (x : Y) x.2
  have hsρ : ρ cN = MulAut.conj s := hsσ.symm
  obtain ⟨y, hyN, hyc⟩ := exists_normalizer_moving ρ (A := A.subgroupOf N)
    (fun a ha b hb => Subtype.ext
      (hcommA _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb)))
    (fun a => ⟨1, Subtype.ext (Subtype.ext
      (by simpa using hA.2 _ (Subgroup.mem_subgroupOf.mp a.2)))⟩)
    hAinj
    (fun z hz hz3 => by
      rw [Subgroup.mem_subgroupOf]
      refine hcent (z : Y) (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_)
        (by simpa using congrArg Subtype.val hz3)
      have h' := Subgroup.mem_centralizer_iff.mp hz ⟨a, hAN ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
      exact congrArg Subtype.val h')
    hcNA (h := ⟨(x : Y), hΛN x.2⟩)
    (fun a ha => by
      obtain ⟨w, hw, hρw⟩ := hρA a ha
      obtain ⟨a', ha', hρa'⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp (hsurjA (hgN w hw)))
      refine ⟨a', ha', ?_⟩
      rw [hρa']
      simp only [map_mul, map_inv, hρh, hρw])
    (fun k hk => by
      apply hgs
      have e1 : ρ (⟨(x : Y), hΛN x.2⟩ * cN * ⟨(x : Y), hΛN x.2⟩⁻¹) =
          MulAut.conj (πe x * s * (πe x)⁻¹) := by
        simp only [map_mul, map_inv, hρh, hsρ]
      have e2 : ρ (cN ^ k) = MulAut.conj (s ^ k) := by
        simp only [map_zpow, hsρ]
      rw [alt10_conj_injective (e1.symm.trans (hk.trans e2))]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers s) k)
  refine ⟨(y : Y), coe_mem_normalizer_of_subgroupOf hAN hyN, fun hmem => hyc ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hcNc]
  exact hk

end Abstract

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150.A10

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Sylow155R1

public theorem res1T150A10_of (h149 : Sec16.Item149S14) {Q : ∀ (X : Type) [Group X], Prop}
    {P : ∀ (Y : Type) [Group Y], Prop} : Res1T150A10 Q P := by
  intro G _ _ A c L X K Y M T P' Yc z τ j hj hj1
  set Yj := Subgroup.centralizer ({j} : Set G) with hYj
  intro Λ hΛ hAΛ c' hc' hLΛ hc'Λ h7 h10
  obtain ⟨e7⟩ := h7
  obtain ⟨e⟩ := h10
  have hAY : A ≤ Yj := fun a ha => Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]
    exact (Subgroup.mem_centralizer_iff.mp (τ.j_le_centralizer hj) a ha).symm
  have hLY : L ≤ Yj := τ.l_le.trans (τ.x_le_centralizer_of_mem_j (h149 G A c L τ.std) hj)
  have hA27 : Nat.card (A.subgroupOf Yj) = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv).trans τ.std.card_eq
  have hcA : c' ∈ A.subgroupOf Yj := by
    rw [Subgroup.mem_subgroupOf, hc']
    exact τ.std.mem_A
  have hcent : ∀ x ∈ Subgroup.centralizer ((A.subgroupOf Yj : Subgroup ↥Yj) : Set ↥Yj),
      x ^ 3 = 1 → x ∈ A.subgroupOf Yj := by
    intro x hx hx3
    rw [Subgroup.mem_subgroupOf]
    refine Sec15.mem_of_mem_partTwoF τ.std.mem_partTwoF (by simpa using congrArg Subtype.val hx3)
      fun a ha => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' := Subgroup.mem_centralizer_iff.mp hx ⟨a, hAY ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val h'
  have hLperf : Group.IsPerfect (L.subgroupOf Yj) := by
    have := τ.isPerfect_l
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLY).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLY).symm.surjective
  let φ₀ : ↥L →* alternatingGroup (Fin 7) :=
    e7.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
  have hφ₀ : Function.Surjective φ₀ := e7.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerφ₀ : φ₀.ker = aschbacherSolvableCore 3 ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    change e7 (x : ↥L ⧸ aschbacherSolvableCore 3 ↥L) = 1 ↔ _
    rw [e7.map_eq_one_iff, QuotientGroup.eq_one_iff]
  let ε := Subgroup.subgroupOfEquivOfLe hLY
  let φ : ↥(L.subgroupOf Yj) →* alternatingGroup (Fin 7) := φ₀.comp ε.toMonoidHom
  have hφ : Function.Surjective φ := hφ₀.comp ε.surjective
  have hφ3 : ¬ 3 ∣ Nat.card φ.ker := by
    have h1 : φ.ker = φ₀.ker.comap ε.toMonoidHom := (MonoidHom.comap_ker _ _).symm
    rw [h1, Subgroup.comap_equiv_eq_map_symm', Subgroup.card_map_of_injective ε.symm.injective,
      hkerφ₀]
    exact three_not_dvd_card_aschbacherSolvableCore
  have hAL : Nat.card ↥(A.subgroupOf Yj ⊓ L.subgroupOf Yj) = 9 := by
    have hhyp := τ.at_of.1
    have h1 : A.subgroupOf Yj ⊓ L.subgroupOf Yj = (A ⊓ L).subgroupOf Yj := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hAY)).toEquiv]
    have h2 := hhyp.2
    rw [τ.std.card_eq] at h2
    omega
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨y, hyN, hyc⟩ := A10.exists_normalizer_moving_of_a10 hΛ
    (Pump.isElemAbelian_subgroupOf τ.std.isElemAbelian) hA27 hAΛ hcent hcA hc'Λ
    (fun x hx => (Subgroup.mem_inf.mp (hLΛ hx)).1) (fun x hx => (Subgroup.mem_inf.mp (hLΛ hx)).2)
    hLperf inferInstance φ hφ hφ3 hAL e
  have hyNG : (y : G) ∈ Subgroup.normalizer (A : Set G) :=
    A10.coe_mem_normalizer_of_subgroupOf hAY hyN
  have hyc' : (y : G) * c * (y : G)⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp (τ.norm hyNG) c).mp (Subgroup.mem_zpowers c)
  apply hyc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyc'
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc']
  exact hk

public theorem res1Thm150b_of_lists (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hK7 : K150For (alternatingGroup (Fin 7))) (hK22 : K150For CFSG.Blueprint.NativeSporadic.M22)
    {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
    (hQ : ∀ (X : Type) [Group X], Q X →
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨ Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
    (h149 : Sec16.Item149S14) (hQs : Res1QE9 Q) : Res1Thm150b Q P :=
  res1Thm150b_of h1 h2 h45 h48 hK7 hK22 hQ h149 hQs (res1T150A10_of h149)

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
