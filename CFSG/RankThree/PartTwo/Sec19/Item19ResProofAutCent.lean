module

public import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3
public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19ResProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section Abstract

variable {Y : Type*} [Group Y] [Finite Y]

theorem commute_of_card_le_nine {Z : Type*} [Group Z] [Finite Z] (hZ : IsPGroup 3 Z)
    (h9 : Nat.card Z ≤ 9) (a b : Z) : a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
  have hk2 : k ≤ 2 := by
    by_contra h
    have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k
  · have : Subsingleton Z := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
    exact Subsingleton.elim _ _
  · have : IsCyclic Z := isCyclic_of_prime_card (by simpa using hk)
    exact (IsCyclic.isMulCommutative (α := Z)).is_comm.comm a b
  · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hk).is_comm.comm a b

theorem card_eq_of_not_comm {P : Subgroup Y} (hP : IsPGroup 3 P) (h27 : Nat.card P ≤ 27)
    (hnab : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) : Nat.card P = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_contra hne
  have hk2 : Nat.card P ≤ 9 := by
    interval_cases k <;> simp_all
  exact hab (congrArg Subtype.val (commute_of_card_le_nine hP hk2 ⟨a, ha⟩ ⟨b, hb⟩))

theorem commute_of_le_center {P : Type*} [Group P] [Finite P] (h27 : Nat.card P = 27)
    {N : Subgroup P} (hN9 : Nat.card N = 9) (hNZ : N ≤ Subgroup.center P) (a b : P) :
    a * b = b * a := by
  have hZ := Subgroup.card_dvd_of_le hNZ
  have hZ27 : Nat.card (Subgroup.center P) ∣ 27 := h27 ▸ Subgroup.card_subgroup_dvd_card _
  have hidx := Subgroup.index_mul_card (Subgroup.center P)
  rw [h27] at hidx
  have hcases : Nat.card (Subgroup.center P) = 9 ∨ Nat.card (Subgroup.center P) = 27 := by
    rw [hN9] at hZ
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card (Subgroup.center P) ∣ 3 ^ 3 by norm_num; exact hZ27)
    interval_cases k
    · rw [hk'] at hZ; norm_num at hZ
    · rw [hk'] at hZ; norm_num at hZ
    · left; rw [hk']; norm_num
    · right; rw [hk']; norm_num
  have hcyc : IsCyclic (P ⧸ Subgroup.center P) := by
    rcases hcases with h | h
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      refine isCyclic_of_prime_card (p := 3) ?_
      rw [← Subgroup.index_eq_card]
      rw [h] at hidx
      omega
    · have h1 : Nat.card (P ⧸ Subgroup.center P) = 1 := by
        rw [← Subgroup.index_eq_card]
        rw [h] at hidx
        omega
      have : Subsingleton (P ⧸ Subgroup.center P) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact isCyclic_of_subsingleton
  exact (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (QuotientGroup.mk' (Subgroup.center P)) (by rw [QuotientGroup.ker_mk'])).is_comm.comm a b

theorem mem_of_commute_of_sylow_bound {N : Subgroup Y} (hN9 : Nat.card N = 9)
    (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (h27 : ∀ P : Subgroup Y, IsPGroup 3 P → Nat.card P ≤ 27)
    {P₀ : Subgroup Y} (hP₀ : IsPGroup 3 P₀) (hP₀nab : ∃ a ∈ P₀, ∃ b ∈ P₀, a * b ≠ b * a)
    {α : Y} (hα : ∃ k : ℕ, α ^ 3 ^ k = 1) (hαN : ∀ n ∈ N, α * n = n * α) : α ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN3 : IsPGroup 3 N := IsPGroup.of_card (n := 2) (by rw [hN9]; norm_num)
  have hα3 : IsPGroup 3 (Subgroup.zpowers α) := by
    obtain ⟨k, hk⟩ := hα
    rintro ⟨_, n, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change (α ^ n) ^ 3 ^ k = 1
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hk,
      _root_.one_zpow]
  have hαnorm : Subgroup.zpowers α ≤ Subgroup.normalizer (N : Set Y) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro n
    have key : ∀ m ∈ N, α * m * α⁻¹ = m := fun m hm => by
      rw [hαN m hm]; group
    constructor
    · intro hn
      rw [key n hn]
      exact hn
    · intro hn
      have h1 := key _ hn
      have h2 : n = α * n * α⁻¹ := by
        calc n = α⁻¹ * (α * n * α⁻¹) * α := by group
          _ = α⁻¹ * (α * (α * n * α⁻¹) * α⁻¹) * α := by rw [h1]
          _ = α * n * α⁻¹ := by group
      rw [h2]
      exact hn
  have hQ := hN3.to_sup_of_normal_left' hα3 hαnorm
  obtain ⟨P, hQP⟩ := hQ.exists_le_sylow
  have hNP : N ≤ (P : Subgroup Y) := le_sup_left.trans hQP
  have hαP : α ∈ (P : Subgroup Y) := hQP (Subgroup.mem_sup_right (Subgroup.mem_zpowers α))
  obtain ⟨P₁, hP₀P₁⟩ := hP₀.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P₁ P
  have hPnab : ∃ a ∈ (P : Subgroup Y), ∃ b ∈ (P : Subgroup Y), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hP₀nab
    have hmem : ∀ x ∈ (P₁ : Subgroup Y), g * x * g⁻¹ ∈ (P : Subgroup Y) := by
      intro x hx
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨x, hx, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    refine ⟨g * a * g⁻¹, hmem a (hP₀P₁ ha), g * b * g⁻¹, hmem b (hP₀P₁ hb), fun h => hab ?_⟩
    have h' : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
        _ = g * b * g⁻¹ * (g * a * g⁻¹) := h
        _ = g * (b * a) * g⁻¹ := by group
    simpa using h'
  have hP27 : Nat.card (P : Subgroup Y) = 27 :=
    card_eq_of_not_comm P.isPGroup' (h27 _ P.isPGroup') hPnab
  set C : Subgroup Y := (P : Subgroup Y) ⊓ Subgroup.centralizer (N : Set Y) with hC
  have hNC : N ≤ C := fun n hn => Subgroup.mem_inf.mpr ⟨hNP hn,
    Subgroup.mem_centralizer_iff.mpr fun m hm => hNab m hm n hn⟩
  have hαC : α ∈ C := Subgroup.mem_inf.mpr ⟨hαP,
    Subgroup.mem_centralizer_iff.mpr fun m hm => (hαN m hm).symm⟩
  have hCP : C ≤ (P : Subgroup Y) := inf_le_left
  have hCne : C ≠ (P : Subgroup Y) := by
    intro hCeq
    obtain ⟨a, ha, b, hb, hab⟩ := hPnab
    apply hab
    have hN'9 : Nat.card (N.subgroupOf (P : Subgroup Y)) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv, hN9]
    have hN'Z : N.subgroupOf (P : Subgroup Y) ≤ Subgroup.center (P : Subgroup Y) := by
      intro n hn
      rw [Subgroup.mem_center_iff]
      intro x
      have hxC : (x : Y) ∈ C := by rw [hCeq]; exact x.2
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxC).2 n
        (Subgroup.mem_subgroupOf.mp hn)
      exact Subtype.ext this.symm
    exact congrArg Subtype.val
      (commute_of_le_center hP27 hN'9 hN'Z ⟨a, ha⟩ ⟨b, hb⟩)
  have hCcard : Nat.card C = 9 := by
    have h1 := Subgroup.card_dvd_of_le hCP
    have h2 := Subgroup.card_dvd_of_le hNC
    rw [hP27] at h1
    rw [hN9] at h2
    have h3 : Nat.card C ≠ 27 := fun h => hCne (Subgroup.eq_of_le_of_card_ge hCP (by omega))
    obtain ⟨m, hm⟩ := h2
    rcases m with _ | _ | _ | _ | m
    · rw [hm] at h1; norm_num at h1
    · omega
    · rw [hm] at h1; norm_num at h1
    · omega
    · have := Nat.le_of_dvd (by norm_num) h1
      omega
  have hCN : C = N := (Subgroup.eq_of_le_of_card_ge hNC (by rw [hCcard, hN9])).symm
  exact hCN ▸ hαC

end Abstract

section Complement

variable {Y : Type*} [Group Y] [Finite Y]

theorem eq_conj_of_fix_normal {S : Subgroup Y} [S.Normal]
    (hSab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (Q : Sylow 2 Y) (hSQ : S ⊔ (Q : Subgroup Y) = ⊤)
    (hCQ : ∀ t ∈ (Q : Subgroup Y), (∀ s ∈ S, t * s = s * t) → t = 1)
    (α : MulAut Y) (hα : ∀ s ∈ S, α s = s) : ∃ s ∈ S, α = MulAut.conj s := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q (α • Q)
  have hg' : g ∈ ((S ⊔ (Q : Subgroup Y) : Subgroup Y) : Set Y) := by
    rw [hSQ]
    exact Subgroup.mem_top g
  rw [Subgroup.normal_mul, Set.mem_mul] at hg'
  obtain ⟨s, hs, t, ht, rfl⟩ := hg'
  have htQ : t • Q = Q := Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer ht)
  have hsQ : s • Q = α • Q := by rw [← hg, mul_smul, htQ]
  set β : MulAut Y := (MulAut.conj s)⁻¹ * α with hβ
  have hβapp : ∀ x, β x = s⁻¹ * α x * s := fun x => by
    rw [hβ, MulAut.mul_apply, ← map_inv, MulAut.conj_apply, inv_inv]
  have hβS : ∀ x ∈ S, β x = x := fun x hx => by
    rw [hβapp, hα x hx, mul_assoc, ← hSab s hs x hx]
    group
  have hβQ : ∀ u ∈ (Q : Subgroup Y), β u ∈ (Q : Subgroup Y) := by
    intro u hu
    have h1 : α u ∈ ((α • Q : Sylow 2 Y) : Subgroup Y) := by
      rw [Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨u, hu, rfl⟩
    rw [← hsQ, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨u', hu', hu'e⟩ := h1
    rw [MulAut.smul_def, MulAut.conj_apply] at hu'e
    rw [hβapp, ← hu'e]
    simpa [mul_assoc] using hu'
  have hβQfix : ∀ u ∈ (Q : Subgroup Y), β u = u := by
    intro u hu
    have hw : u⁻¹ * β u ∈ (Q : Subgroup Y) := mul_mem (inv_mem hu) (hβQ u hu)
    have hwS : ∀ x ∈ S, u⁻¹ * β u * x = x * (u⁻¹ * β u) := by
      intro x hx
      have hux : u * x * u⁻¹ ∈ S := (inferInstance : S.Normal).conj_mem x hx u
      have h1 : β u * x * (β u)⁻¹ = u * x * u⁻¹ := by
        have h2 := hβS _ hux
        rw [map_mul, map_mul, map_inv, hβS x hx] at h2
        exact h2
      calc u⁻¹ * β u * x = u⁻¹ * (β u * x * (β u)⁻¹) * β u := by group
        _ = u⁻¹ * (u * x * u⁻¹) * β u := by rw [h1]
        _ = x * (u⁻¹ * β u) := by group
    have h1 := hCQ _ hw hwS
    calc β u = u * (u⁻¹ * β u) := by group
      _ = u := by rw [h1, mul_one]
  have hβ1 : β = 1 := by
    have hle : S ⊔ (Q : Subgroup Y) ≤
        MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id Y) :=
      sup_le (fun x hx => hβS x hx) (fun x hx => hβQfix x hx)
    rw [hSQ] at hle
    ext x
    exact hle (Subgroup.mem_top x)
  refine ⟨s, hs, ?_⟩
  calc α = MulAut.conj s * β := by rw [hβ]; group
    _ = MulAut.conj s := by rw [hβ1, mul_one]

end Complement

section Bound

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)

theorem finite_mulAut (X : Type*) [Group X] [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun e : MulAut X => (e : X → X)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem card_le_of_isPGroup {X : Type*} [Group X] [Finite X] (hX : (Nat.card X).factorization 3 = 2)
    (hOut : ¬ 9 ∣ Nat.card (Outer X)) (P : Subgroup (MulAut X)) (hP : IsPGroup 3 P) :
    Nat.card P ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_mulAut X
  have hA := Subgroup.card_mul_index (inner X)
  rw [Subgroup.index_eq_card] at hA
  have hinnX : Nat.card (inner X) ∣ Nat.card X := Subgroup.card_range_dvd _
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hI0 : Nat.card (inner X) ≠ 0 := Nat.card_pos.ne'
  have hO0 : Nat.card (Outer X) ≠ 0 := Nat.card_pos.ne'
  have hI : (Nat.card (inner X)).factorization 3 ≤ 2 := by
    rw [← hX]
    exact (Nat.factorization_le_iff_dvd hI0 hX0).mpr hinnX 3
  have hO : (Nat.card (Outer X)).factorization 3 ≤ 1 := by
    by_contra h
    exact hOut ((Nat.Prime.pow_dvd_iff_le_factorization (k := 2) Nat.prime_three hO0).mpr
      (by omega))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd : 3 ^ k ∣ Nat.card (MulAut X) := hk ▸ Subgroup.card_subgroup_dvd_card P
  rw [← hA] at hdvd
  have hk3 : k ≤ 3 := by
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (Nat.mul_ne_zero hI0 hO0)).mp hdvd
    rw [Nat.factorization_mul hI0 hO0, Finsupp.add_apply] at h1
    omega
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 27 := by norm_num

theorem not_three_dvd_of_mod_nine {p e : ℕ} (h3 : p ^ e % 3 ≠ 0) (h91 : p ^ e % 9 ≠ 1)
    (h98 : p ^ e % 9 ≠ 8) : ¬ 3 ∣ e := by
  rintro ⟨k, rfl⟩
  rw [pow_mul'] at h3 h91 h98
  have hr : (p ^ k) ^ 3 % 9 = (p ^ k % 9) ^ 3 % 9 := Nat.pow_mod _ _ _
  have hr3 : (p ^ k) ^ 3 % 3 = ((p ^ k % 9) % 3) ^ 3 % 3 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 9), ← Nat.pow_mod]
  have hlt : p ^ k % 9 < 9 := Nat.mod_lt _ (by norm_num)
  interval_cases h : p ^ k % 9 <;> simp_all

theorem not_nine_dvd_card_outer {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi X p e) (hq2 : p ^ e ≠ 2) (h91 : p ^ e % 9 ≠ 1)
    (h98 : p ^ e % 9 ≠ 8) : ¬ 9 ∣ Nat.card (Outer X) := by
  have hp : p.Prime := Fact.out
  have h3e : ¬ 3 ∣ e := not_three_dvd_of_mod_nine (by rcases hiso with ⟨h, -⟩ | ⟨h, -⟩ <;> omega)
    h91 h98
  have hcop : Nat.Coprime 9 (2 * e) := by
    have h1 : Nat.Coprime 3 (2 * e) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (fun h => by
        rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
        · omega
        · exact h3e h)
    simpa using Nat.Coprime.pow_left 2 h1
  rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
    have hd := higher_linear_outer_order_divides_field_gcd_bound hp he (le_refl 3) hK
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (Sec4.projSLEquivProjectiveSL 3 (GaloisField p e))).toEquiv,
      ← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ).toEquiv]
      at hd
    intro h9
    have h9' := hcop.dvd_of_dvd_mul_left (h9.trans hd)
    have h3 : Nat.gcd 3 (p ^ e - 1) ∣ 3 := Nat.gcd_dvd_left _ _
    have := Nat.le_of_dvd (by norm_num) (h9'.trans h3)
    omega
  · have hd := Sec4.card_outer_projSU_dvd 3 p e he (le_refl 3) (by omega)
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ).toEquiv]
      at hd
    intro h9
    have h9' := hcop.dvd_of_dvd_mul_left (h9.trans hd)
    omega

end Bound

section Model

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem phaseGL_pow_three {τ : K} (hτ : τ ^ 3 = 1) : phaseGL hτ ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_phaseGL, Units.val_one]
  have hτ' : τ * τ * τ = 1 := by rw [← hτ]; ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, hτ']

theorem mk_mem_normalizer_projImage (hπ : π = false → UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) :
    ProjGenLinGroup.mk g ∈ Subgroup.normalizer
      ((projImage (slPi π 3 (p ^ f) K) : Subgroup (ProjGenLinGroup (Fin 3) K)) :
        Set (ProjGenLinGroup (Fin 3) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨g * s * g⁻¹, conj_mem_slPi hπ hg hs, by simp [map_mul, map_inv]⟩
  · rintro ⟨s, hs, hse⟩
    refine ⟨g⁻¹ * s * g, by simpa using conj_mem_slPi hπ (inv_mem hg) hs, ?_⟩
    rw [map_mul, map_mul, map_inv, hse]
    group

theorem isPGroup_zpowers_of_pow_three {M : Type*} [Group M] {x : M} (h : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  rintro ⟨_, n, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  change (x ^ n) ^ 3 ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, h,
    _root_.one_zpow]

theorem exists_not_comm_threeSubgroup_model (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Finite K] [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] :
    ∃ P₀ : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K))), IsPGroup 3 P₀ ∧
      ∃ a ∈ P₀, ∃ b ∈ P₀, a * b ≠ b * a := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set M := projImage (slPi π 3 (p ^ f) K) with hM
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hZ := center_projImage_eq_bot hK hq
  have hinj := Sec4.Item434Kit.conj_injective_of_center_eq_bot hZ
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨dM, cM, hdM, hcM, hdc, hdo, -, -⟩ := Step1915WProof.exists_heisPair hK hq hτ hτ1
  have ht := mk_mem_normalizer_projImage hπ (phaseGL_mem_glPi hK hq hτ)
  set δ : MulAut M := M.normalizerMonoidHom ⟨_, ht⟩ with hδ
  have hδd : δ dM = dM := Subtype.ext (by
    rw [hδ, normalizerMonoidHom_apply_coe, hdM, mk_phase_diagTau])
  have hδc : δ cM = dM * cM := Subtype.ext (by
    rw [hδ, normalizerMonoidHom_apply_coe, hcM, mk_phase_cycThree, Subgroup.coe_mul, hdM, hcM])
  have hδ3 : δ ^ 3 = 1 := by
    rw [hδ, ← map_pow]
    have h1 : (⟨_, ht⟩ : Subgroup.normalizer ((M : Subgroup (ProjGenLinGroup (Fin 3) K)) :
        Set (ProjGenLinGroup (Fin 3) K))) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← map_pow, phaseGL_pow_three, map_one]
      rfl)
    rw [h1, map_one]
  set a : MulAut M := MulAut.conj dM with ha
  set b : MulAut M := MulAut.conj cM with hb
  have hab : a * b = b * a := by rw [ha, hb, ← map_mul, hdc, map_mul]
  have hd3 : dM ^ 3 = 1 := by simpa [hdo] using pow_orderOf_eq_one dM
  have hc3 : cM ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hcM, ← map_pow, cycThree_pow_three, map_one]
    rfl)
  have ha3 : a ^ 3 = 1 := by rw [ha, ← map_pow, hd3, map_one]
  have hb3 : b ^ 3 = 1 := by rw [hb, ← map_pow, hc3, map_one]
  set N₀ : Subgroup (MulAut M) := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hN₀
  have hN₀3 : IsPGroup 3 N₀ := (isPGroup_zpowers_of_pow_three ha3).to_sup_of_normal_left'
    (isPGroup_zpowers_of_pow_three hb3)
    (Subgroup.zpowers_le.mpr (Sec12.mem_normalizer_zpowers_of_commute hab.symm))
  have hδa : δ * a * δ⁻¹ = a := by
    rw [ha, KFacts.mul_mulAutConj_mul_inv, hδd]
  have hδb : δ * b * δ⁻¹ = a * b := by
    rw [hb, KFacts.mul_mulAutConj_mul_inv, hδc, map_mul]
  have hδN : Subgroup.zpowers δ ≤ Subgroup.normalizer (N₀ : Set (MulAut M)) := by
    have := finite_mulAut M
    rw [Subgroup.zpowers_le]
    refine Sec13.Item138Proof.mem_normalizer_sup_zpowers ?_ ?_
    · rw [hδa]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    · rw [hδb]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  refine ⟨N₀ ⊔ Subgroup.zpowers δ,
    hN₀3.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_three hδ3) hδN,
    δ, Subgroup.mem_sup_right (Subgroup.mem_zpowers δ),
    b, Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)), ?_⟩
  intro h
  have h1 : δ * b * δ⁻¹ = b := by rw [h]; group
  rw [hδb] at h1
  have h2 : a = 1 := by
    calc a = a * b * b⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel]
  have h3 : dM = 1 := hinj (by rw [← ha, h2, map_one])
  rw [h3, orderOf_one] at hdo
  omega

theorem exists_not_comm_threeSubgroup {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) (hperf : Group.IsPerfect X) :
    ∃ P₀ : Subgroup (MulAut X), IsPGroup 3 P₀ ∧ ∃ a ∈ P₀, ∃ b ∈ P₀, a * b ≠ b * a := by
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model he hiso
  have := hK.finite
  have : Group.IsPerfect (projImage (slPi π 3 (p ^ e) K)) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  obtain ⟨P₀, hP₀, a, ha, b, hb, hab⟩ := exists_not_comm_threeSubgroup_model hK hq
  set F : MulAut (projImage (slPi π 3 (p ^ e) K)) →* MulAut X :=
    (MulAut.congr ψ.symm).toMonoidHom with hF
  refine ⟨P₀.map F, hP₀.map F, F a, Subgroup.mem_map_of_mem F ha, F b,
    Subgroup.mem_map_of_mem F hb, fun h => hab ?_⟩
  apply (MulAut.congr ψ.symm).injective
  rw [map_mul, map_mul]
  exact h

end Model

section Two

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

theorem transitive_sylow {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi X p e) (h91 : p ^ e % 9 ≠ 1) (h98 : p ^ e % 9 ≠ 8) (S : Sylow 3 X) :
    ∀ x ∈ (S : Subgroup X), x ≠ 1 → ∀ y ∈ (S : Subgroup X), y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((S : Subgroup X) : Set X), n * x * n⁻¹ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hS9, -⟩ := Step1915WProof.ks1917Lie3Sylow X p e he hiso h91 h98 S
  have h9 : (Nat.card X).factorization 3 = 2 :=
    Sec13.Item138Proof.factorization_card_three_eq_two he hiso (by omega)
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hπ : π = false → UnitaryFieldData p e K := fun h => by subst h; exact hK.unitary
  set M := projImage (slPi π 3 (p ^ e) K) with hM
  have h9M : (Nat.card M).factorization 3 = 2 := by rw [← Nat.card_congr φ.toEquiv, h9]
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨dM, cM, hdM, hcM, hdc, hdo, hco, hcd⟩ := Step1915WProof.exists_heisPair hK hq hτ hτ1
  set E := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hco hcd (by
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_left hdc k).eq)), Nat.card_zpowers, hdo]
  set S₀ := Sylow.ofCard E (by rw [hE9, h9M]; norm_num) with hS₀
  have hS'card : Nat.card (S.map φ.toMonoidHom) = 3 ^ (Nat.card M).factorization 3 := by
    rw [Subgroup.card_map_of_injective φ.injective, hS9, h9M]
    norm_num
  set S' := Sylow.ofCard (S.map φ.toMonoidHom) hS'card with hS'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq M S₀ S'
  have hmemS' : ∀ w ∈ E, k * w * k⁻¹ ∈ (S.map φ.toMonoidHom : Subgroup M) := by
    intro w hw
    have : k * w * k⁻¹ ∈ ((k • S₀ : Sylow 3 M) : Subgroup M) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨w, hw, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hk] at this
    exact this
  set x₁ := φ.symm (k * dM * k⁻¹) with hx₁
  set x₂ := φ.symm (k * cM * k⁻¹) with hx₂
  have hxS' : ∀ w ∈ E, φ.symm (k * w * k⁻¹) ∈ (S : Subgroup X) := by
    intro w hw
    obtain ⟨y, hy, hye⟩ := hmemS' w hw
    have : φ.symm (k * w * k⁻¹) = y := by
      rw [← hye]
      exact φ.symm_apply_apply y
    rw [this]
    exact hy
  have hx₁S : x₁ ∈ (S : Subgroup X) := hxS' _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers dM))
  have hx₂S : x₂ ∈ (S : Subgroup X) := hxS' _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers cM))
  have hx₁₂ : x₁ * x₂ = x₂ * x₁ := by
    apply φ.injective
    rw [map_mul, map_mul, hx₁, hx₂, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    calc k * dM * k⁻¹ * (k * cM * k⁻¹) = k * (dM * cM) * k⁻¹ := by group
      _ = k * (cM * dM) * k⁻¹ := by rw [hdc]
      _ = k * cM * k⁻¹ * (k * dM * k⁻¹) := by group
  have hx₂o : orderOf x₂ = 3 := by
    rw [hx₂, MulEquiv.orderOf_eq, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hco]
  have hx₂x₁ : x₂ ∉ Subgroup.zpowers x₁ := by
    intro h
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hcd
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    have h1 := congrArg φ hj
    rw [map_zpow, hx₁, hx₂, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, conj_zpow]
      at h1
    have h2 := congrArg (fun w => k⁻¹ * w * k) h1
    simpa [mul_assoc] using h2
  have hsup9 : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup X) = 9 := by
    rw [Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hx₂o hx₂x₁ (by
      rintro _ ⟨j, rfl⟩
      exact ((Commute.zpow_left hx₁₂ j).eq)), Nat.card_zpowers, hx₁,
      MulEquiv.orderOf_eq, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hdo]
  have hSeq : (S : Subgroup X) = Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hx₁S)
      (Subgroup.zpowers_le.mpr hx₂S)) (by rw [hsup9, hS9])).symm
  obtain ⟨ĝ, hĝ, hĝk⟩ := k.2
  set e : (⊤ : Subgroup X) ≃* M := Subgroup.topEquiv.trans φ with he
  have he₁ : ((e ⟨x₁, Subgroup.mem_top x₁⟩ : M) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (ĝ * diagTau hτ * ĝ⁻¹) := by
    rw [he, MulEquiv.trans_apply, Subgroup.topEquiv_apply, hx₁, MulEquiv.apply_symm_apply,
      map_mul, map_mul, map_inv, hĝk]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hdM]
  have he₂ : ((e ⟨x₂, Subgroup.mem_top x₂⟩ : M) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (ĝ * cycThree * ĝ⁻¹) := by
    rw [he, MulEquiv.trans_apply, Subgroup.topEquiv_apply, hx₂, MulEquiv.apply_symm_apply,
      map_mul, map_mul, map_inv, hĝk]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcM]
  have htr := transitive_of_normal_form hK hq e hτ hτ1 (slPi_le_glPi hπ hĝ)
    (Subgroup.mem_top x₁) (Subgroup.mem_top x₂) he₁ he₂
  intro x hxS hx1 y hyS hy1
  rw [hSeq] at hxS hyS
  obtain ⟨n, ⟨-, hnN⟩, hnxy⟩ := htr x hxS hx1 y hyS hy1
  exact ⟨n, hSeq ▸ hnN, hnxy⟩

theorem factorization_seventyTwo_two : (72 : ℕ).factorization 2 = 3 := by
  rw [show (72 : ℕ) = 2 ^ 3 * 9 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 9)]
  simp

theorem autCent_of_eq_two {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi X p e) (hq2 : p ^ e = 2) (h91 : p ^ e % 9 ≠ 1) (h98 : p ^ e % 9 ≠ 8)
    (S : Sylow 3 X) (hS9 : Nat.card (S : Subgroup X) = 9)
    (hSab : ∀ a ∈ (S : Subgroup X), ∀ b ∈ (S : Subgroup X), a * b = b * a)
    (α : MulAut X) (hαS : ∀ s ∈ (S : Subgroup X), α s = s) :
    ∃ s ∈ (S : Subgroup X), α = MulAut.conj s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX72 : Nat.card X = 72 := by
    obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
    have hc := Sec13.card_projImage_slPi_mul_three hK hq
    rw [← Nat.card_congr φ.toEquiv, hq2] at hc
    cases π
    · norm_num at hc
      omega
    · exfalso
      change p ^ e % 3 = 1 at hq
      rw [hq2] at hq
      norm_num at hq
  have htr := transitive_sylow he hiso h91 h98 S
  obtain ⟨x, hxS, hx1⟩ : ∃ x ∈ (S : Subgroup X), x ≠ 1 := by
    by_contra h
    push Not at h
    have : (S : Subgroup X) = ⊥ := eq_bot_iff.mpr fun y hy => Subgroup.mem_bot.mpr (h y hy)
    rw [this, Subgroup.card_bot] at hS9
    omega
  set N := Subgroup.normalizer ((S : Subgroup X) : Set X) with hN
  let _ : MulAction N X := MulAction.compHom X ((MulAut.conj : X →* MulAut X).comp N.subtype)
  have hsmul : ∀ (n : N) (y : X), n • y = (n : X) * y * (n : X)⁻¹ := fun _ _ => rfl
  have horb : ((S : Subgroup X) : Set X) \ {1} ⊆ MulAction.orbit N x := by
    rintro y ⟨hyS, hy1⟩
    obtain ⟨n, hn, hny⟩ := htr x hxS hx1 y hyS hy1
    refine ⟨⟨n, hn⟩, ?_⟩
    change (⟨n, hn⟩ : N) • x = y
    rw [hsmul]
    exact hny
  have hcard8 : (((S : Subgroup X) : Set X) \ {1}).ncard = 8 := by
    rw [Set.ncard_sdiff_singleton_of_mem (one_mem (S : Subgroup X)), ← Nat.card_coe_set_eq]
    change Nat.card (S : Subgroup X) - 1 = 8
    rw [hS9]
  have horb8 : 8 ≤ (MulAction.orbit N x).ncard :=
    hcard8 ▸ Set.ncard_le_ncard horb (Set.toFinite _)
  have hidx := MulAction.index_stabilizer N x
  have hSN : (S : Subgroup X) ≤ N := Subgroup.le_normalizer
  have hSstab : (S : Subgroup X).subgroupOf N ≤ MulAction.stabilizer N x := by
    intro n hn
    rw [MulAction.mem_stabilizer_iff, hsmul, hSab _ (Subgroup.mem_subgroupOf.mp hn) x hxS]
    group
  have hSsub9 : Nat.card ((S : Subgroup X).subgroupOf N) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv, hS9]
  have hstab9 : 9 ≤ Nat.card (MulAction.stabilizer N x) :=
    hSsub9 ▸ Subgroup.card_le_of_le hSstab
  have hNcard := Subgroup.card_mul_index (MulAction.stabilizer N x)
  have hNle : Nat.card N ≤ 72 := by
    have := Subgroup.card_le_of_le (le_top : N ≤ ⊤)
    rwa [Subgroup.card_top, hX72] at this
  have hst : Nat.card (MulAction.stabilizer N x) = 9 := by
    rw [hidx] at hNcard
    nlinarith
  have hN72 : Nat.card N = 72 := by
    rw [hidx] at hNcard
    nlinarith
  have hNtop : N = ⊤ := Subgroup.eq_top_of_card_eq N (by rw [hN72, hX72])
  have hSn : (S : Subgroup X).Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  have hstabS : (S : Subgroup X).subgroupOf N = MulAction.stabilizer N x :=
    Subgroup.eq_of_le_of_card_ge hSstab (by rw [hst, hSsub9])
  have hC : ∀ t : X, t * x = x * t → t ∈ (S : Subgroup X) := by
    intro t ht
    have htN : t ∈ N := hNtop ▸ Subgroup.mem_top t
    have hmem : (⟨t, htN⟩ : N) ∈ MulAction.stabilizer N x := by
      rw [MulAction.mem_stabilizer_iff, hsmul]
      change t * x * t⁻¹ = x
      rw [ht]
      group
    rw [← hstabS] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨Q⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hQ8 : Nat.card (Q : Subgroup X) = 8 := by
    rw [Sylow.card_eq_multiplicity, hX72, factorization_seventyTwo_two]
    norm_num
  have hSQ : (S : Subgroup X) ⊔ (Q : Subgroup X) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 : 9 ∣ Nat.card ((S : Subgroup X) ⊔ (Q : Subgroup X) : Subgroup X) :=
      hS9 ▸ Subgroup.card_dvd_of_le le_sup_left
    have h2 : 8 ∣ Nat.card ((S : Subgroup X) ⊔ (Q : Subgroup X) : Subgroup X) :=
      hQ8 ▸ Subgroup.card_dvd_of_le le_sup_right
    have h3 : 72 ∣ Nat.card ((S : Subgroup X) ⊔ (Q : Subgroup X) : Subgroup X) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
    have h4 : Nat.card ((S : Subgroup X) ⊔ (Q : Subgroup X) : Subgroup X) ≤ 72 :=
      hX72 ▸ (Subgroup.card_le_of_le le_top).trans (by rw [Subgroup.card_top])
    have h5 := Nat.le_of_dvd (Nat.card_pos) h3
    omega
  have hCQ : ∀ t ∈ (Q : Subgroup X), (∀ s ∈ (S : Subgroup X), t * s = s * t) → t = 1 := by
    intro t htQ hts
    have htS := hC t (hts x hxS)
    have h9 : orderOf t ∣ 9 := by
      have := orderOf_dvd_natCard (⟨t, htS⟩ : (S : Subgroup X))
      rwa [Subgroup.orderOf_mk, hS9] at this
    have h8 : orderOf t ∣ 8 := by
      have := orderOf_dvd_natCard (⟨t, htQ⟩ : (Q : Subgroup X))
      rwa [Subgroup.orderOf_mk, hQ8] at this
    have h1 : orderOf t ∣ 1 := (Nat.dvd_gcd h9 h8).trans (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  exact eq_conj_of_fix_normal hSab Q hSQ hCQ α hαS

end Two

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv φ.symm, h,
    Subgroup.map_bot]

theorem ks1917Lie3AutCent : KS1917Lie3AutCent := by
  intro X _ _ p e _ he hiso h91 h98 S α hα hαS
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hS9, -⟩ := Step1915WProof.ks1917Lie3Sylow X p e he hiso h91 h98 S
  have hSab : ∀ a ∈ (S : Subgroup X), ∀ b ∈ (S : Subgroup X), a * b = b * a := by
    intro a ha b hb
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := (S : Subgroup X))
      (by rw [hS9]; norm_num)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h
  by_cases hq2 : p ^ e = 2
  · exact autCent_of_eq_two he hiso hq2 h91 h98 S hS9 hSab α hαS
  have h9 : (Nat.card X).factorization 3 = 2 :=
    Sec13.Item138Proof.factorization_card_three_eq_two he hiso (by omega)
  have hp : p.Prime := Fact.out
  have hq2' : 2 < p ^ e := by
    have : 2 ≤ p ^ e := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    omega
  obtain ⟨hperf, hZ⟩ : Group.IsPerfect X ∧ Subgroup.center X = ⊥ := by
    rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · obtain ⟨hP, hZP⟩ := Sec13.isPerfect_center_projSL p e he hq
      exact ⟨Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective,
        center_eq_bot_of_mulEquiv φ hZP⟩
    · obtain ⟨hP, hZP⟩ := Sec13.isPerfect_center_projSU p e he hq hq2'
      exact ⟨Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective,
        center_eq_bot_of_mulEquiv φ hZP⟩
  have hinj := Sec4.Item434Kit.conj_injective_of_center_eq_bot hZ
  set N : Subgroup (MulAut X) := (S : Subgroup X).map (MulAut.conj : X →* MulAut X) with hNdef
  have hN9 : Nat.card N = 9 := by rw [hNdef, Subgroup.card_map_of_injective hinj, hS9]
  have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, hSab x hx y hy, map_mul]
  have hαN : ∀ n ∈ N, α * n = n * α := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 := KFacts.mul_mulAutConj_mul_inv α s
    rw [hαS s hs] at h1
    calc α * MulAut.conj s = α * MulAut.conj s * α⁻¹ * α := by group
      _ = MulAut.conj s * α := by rw [h1]
  have := finite_mulAut X
  have h27 := card_le_of_isPGroup h9 (not_nine_dvd_card_outer he hiso hq2 h91 h98)
  obtain ⟨P₀, hP₀, hP₀nab⟩ := exists_not_comm_threeSubgroup he hiso hperf
  obtain ⟨s, hs, hse⟩ := mem_of_commute_of_sylow_bound hN9 hNab h27 hP₀ hP₀nab hα hαN
  exact ⟨s, hs, hse.symm⟩

end CFSG.RankThree.PartTwo.Sec19.Item19ResProof
