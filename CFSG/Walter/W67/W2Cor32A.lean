module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.HallFoundations
import CFSG.Walter.W67.W1Prop24B
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Walter.ReeOrder.JT.Section2
public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise
open CFSG.RankThreeEvenClassification.Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_eq_of_supplement {D H M : Subgroup G} (hDM : D ≤ M)
    (hsupp : ∀ x ∈ M, ∃ d ∈ D, ∃ c ∈ H, x = d * c) : H.relIndex D = H.relIndex M := by
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE H hDM)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE H hDM).injective, fun y => ?_⟩)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨d, hd, c, hc, hx⟩ := hsupp x x.2
  refine ⟨QuotientGroup.mk ⟨d, hd⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq]
  rw [Subgroup.mem_subgroupOf]
  have : ((Subgroup.inclusion hDM ⟨d, hd⟩)⁻¹ * x : M) = (c : G) := by
    simp [hx]
  rw [this]
  exact hc

omit [Finite G] in
theorem card_mul_card_inf_of_supplement {D H M : Subgroup G} (hDM : D ≤ M) (hHM : H ≤ M)
    (hsupp : ∀ x ∈ M, ∃ d ∈ D, ∃ c ∈ H, x = d * c) :
    Nat.card M * Nat.card (D ⊓ H : Subgroup G) = Nat.card D * Nat.card H := by
  have h1 := Subgroup.relIndex_mul_card (H := H) (K := M)
  have h2 := Subgroup.relIndex_mul_card (H := H) (K := D)
  rw [inf_eq_left.mpr hHM, ← relIndex_eq_of_supplement hDM hsupp] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

omit [Finite G] in
theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (A.subgroupOf N) (B.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  exact h

theorem jGroup_no_odd_subgroup {L : Type} [Group L] [Finite L] (hJ1 : J1Prop L)
    (hJ2 : J2Prop L) (hJ2e : J2Extra L) (Y : Subgroup L) (hY : Odd (Nat.card Y))
    (hdvd : 7 * 11 * 19 ∣ Nat.card Y) : False := by
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨-, hcard, -⟩ := hJ1
  have hYL : Nat.card Y ∣ 1463 * 15 * 8 := by
    have := Subgroup.card_subgroup_dvd_card Y
    rw [hcard] at this
    norm_num at this ⊢
    exact this
  have hY' : Nat.card Y ∣ 1463 * 15 := by
    have hcop : Nat.Coprime (Nat.card Y) 8 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hY)
    exact hcop.dvd_of_dvd_mul_right hYL
  obtain ⟨k, hk⟩ := hdvd
  rw [show 7 * 11 * 19 = 1463 by norm_num] at hk
  have hk15 : k ∣ 15 := by
    rw [hk] at hY'
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hY'
  obtain ⟨Q⟩ : Nonempty (Sylow 7 Y) := inferInstance
  have hQ7 : Nat.card (Q : Subgroup Y) = 7 := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    have hdvdj : 7 ^ j ∣ 1463 * 15 := hj ▸ (Subgroup.card_subgroup_dvd_card _).trans hY'
    have hj1 : j ≤ 1 := by
      by_contra hj2
      push Not at hj2
      have : 7 ^ 2 ∣ 1463 * 15 := (pow_dvd_pow 7 hj2).trans hdvdj
      norm_num at this
    have hj0 : j ≠ 0 := by
      intro hj0
      rw [hj0, pow_zero] at hj
      exact Q.ne_bot_of_dvd_card (by rw [hk]; exact dvd_mul_of_dvd_left (by norm_num) _)
        (Subgroup.card_eq_one.mp hj)
    have : j = 1 := by omega
    rw [hj, this, pow_one]
  set P' := (Q : Subgroup Y).map Y.subtype
  have hP'7 : Nat.card P' = 7 := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hQ7]
  have hfac : (Nat.card L).factorization 7 = 1 := by
    rw [hcard]
    have : 2 ^ 3 * 3 * 5 * 7 * 11 * 19 = 7 ^ 1 * 25080 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  set P := Sylow.ofCard P' (by rw [hP'7, hfac, pow_one])
  have hPc : ((P : Subgroup L)) = P' := Sylow.coe_ofCard _ _
  have hN42 : Nat.card (Subgroup.normalizer ((P : Subgroup L) : Set L)) = 42 := by
    have h3 := hJ2.2.2 7 P (Or.inl rfl)
    obtain ⟨-, hidx⟩ := h3
    have hC := hJ2e.2.1 7 (Or.inl rfl) P
    simp only [show (7 : ℕ) ≠ 11 by norm_num, ite_false] at hidx
    have hCN : Subgroup.centralizer ((P : Subgroup L) : Set L) ≤
        Subgroup.normalizer ((P : Subgroup L) : Set L) := Subgroup.centralizer_le_normalizer _
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ((P : Subgroup L) : Set L))
      (K := Subgroup.normalizer ((P : Subgroup L) : Set L))
    rw [inf_eq_left.mpr hCN] at h1
    have h6 : (Subgroup.centralizer ((P : Subgroup L) : Set L)).relIndex
        (Subgroup.normalizer ((P : Subgroup L) : Set L)) = 6 := hidx
    have hP7 : Nat.card (P : Subgroup L) = 7 := by rw [hPc, hP'7]
    rw [h6, hC, hP7] at h1
    omega
  let NQ := Subgroup.normalizer ((Q : Subgroup Y) : Set Y)
  have hNQdvd : Nat.card NQ ∣ 42 := by
    have hmap : NQ.map Y.subtype ≤ Subgroup.normalizer ((P : Subgroup L) : Set L) := by
      rw [hPc, JT.map_normalizer_of_injective Y.subtype Y.subtype_injective]
      exact inf_le_right
    rw [← hN42, ← Subgroup.card_map_of_injective Y.subtype_injective]
    exact Subgroup.card_dvd_of_le hmap
  have hNQodd : Odd (Nat.card NQ) := Odd.of_dvd_nat hY (Subgroup.card_subgroup_dvd_card NQ)
  have hNQ21 : Nat.card NQ ∣ 21 := by
    have hcop : Nat.Coprime (Nat.card NQ) 2 := Nat.coprime_two_right.mpr hNQodd
    exact hcop.dvd_of_dvd_mul_left (by rw [show (2 : ℕ) * 21 = 42 by norm_num]; exact hNQdvd)
  have hNQ7 : 7 ∣ Nat.card NQ := by
    rw [← hQ7]
    exact Subgroup.card_dvd_of_le Subgroup.le_normalizer
  have hmod := card_sylow_modEq_one 7 Y
  rw [Sylow.card_eq_index_normalizer Q] at hmod
  have hidx7 : NQ.index % 7 = 1 := hmod
  have hmul : Nat.card NQ * NQ.index = 1463 * k := by rw [NQ.card_mul_index, hk]
  have hNQcases : Nat.card NQ = 7 ∨ Nat.card NQ = 21 := by
    have hNQle : Nat.card NQ ≤ 21 := Nat.le_of_dvd (by norm_num) hNQ21
    have hpos : 0 < Nat.card NQ := Nat.card_pos
    interval_cases hc : Nat.card NQ <;> omega
  have hkcases : k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 15 := by
    have hkle : k ≤ 15 := Nat.le_of_dvd (by norm_num) hk15
    interval_cases k <;> omega
  rcases hNQcases with h | h <;> rw [h] at hmul <;> rcases hkcases with rfl | rfl | rfl | rfl <;>
    omega

theorem card_normalizer_of_R6 {L : Type} [Group L] [Finite L] {C : Subgroup L}
    (hab : IsMulCommutative C) (hC1 : 1 < Nat.card C)
    (h6 : ((Subgroup.centralizer (C : Set L)).subgroupOf (Subgroup.normalizer (C : Set L))).index
      = 6)
    (hcent : ∀ c ∈ C, c ≠ 1 → Subgroup.centralizer ({c} : Set L) = C) :
    Nat.card (Subgroup.normalizer (C : Set L)) = 6 * Nat.card C := by
  have hCC : Subgroup.centralizer (C : Set L) = C := by
    apply le_antisymm
    · obtain ⟨⟨c, hc⟩, hc1⟩ := (Subgroup.one_lt_card_iff_ne_bot C).mp hC1 |>
        (Subgroup.ne_bot_iff_exists_ne_one).mp
      calc Subgroup.centralizer (C : Set L) ≤ Subgroup.centralizer ({c} : Set L) :=
            Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hc)
        _ = C := hcent c hc fun h => hc1 (Subtype.ext h)
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hCN : Subgroup.centralizer (C : Set L) ≤ Subgroup.normalizer (C : Set L) :=
    Subgroup.centralizer_le_normalizer _
  have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (C : Set L))
    (K := Subgroup.normalizer (C : Set L))
  rw [inf_eq_left.mpr hCN] at h1
  change ((Subgroup.centralizer (C : Set L)).subgroupOf _).index * _ = _ at h1
  rw [h6, hCC] at h1
  exact h1.symm

theorem exists_conj_le_of_hall {L : Type} [Group L] [Finite L] {r : ℕ} [Fact r.Prime]
    {C N : Subgroup L} (hcop : Nat.Coprime (Nat.card C) C.index) (hr : r ∣ Nat.card C)
    (hN : IsPGroup r N) : ∃ g : L, ∀ x ∈ N, g * x * g⁻¹ ∈ C := by
  obtain ⟨R⟩ : Nonempty (Sylow r C) := inferInstance
  set R' := (R : Subgroup C).map C.subtype
  have hR'C : R' ≤ C := Subgroup.map_subtype_le _
  have hi : C.index.factorization r = 0 := Nat.factorization_eq_zero_of_not_dvd fun hri =>
    (Nat.Prime.one_lt Fact.out).ne' (Nat.eq_one_of_dvd_coprimes hcop hr hri)
  have hR' : Nat.card R' = r ^ (Nat.card L).factorization r := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity,
      ← C.card_mul_index, Nat.factorization_mul (Nat.card_pos (α := C)).ne'
        C.index_ne_zero_of_finite, Finsupp.add_apply, hi, add_zero]
  obtain ⟨P, hP⟩ := hN.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L P (Sylow.ofCard R' hR')
  refine ⟨g, fun x hx => hR'C ?_⟩
  have h1 : g * x * g⁻¹ ∈ ((g • P : Sylow r L) : Subgroup L) := by
    rw [Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P : Subgroup L) (hP hx)
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rw [hg, Sylow.coe_ofCard] at h1
  exact h1

theorem no_odd_subgroup_of_hall_pair {L : Type} [Group L] [Finite L] (C : Bool → Subgroup L)
    (hab : ∀ s, IsMulCommutative (C s)) (hC1 : ∀ s, 1 < Nat.card (C s))
    (hhall : ∀ s, Nat.Coprime (Nat.card (C s)) (C s).index)
    (h6 : ∀ s, ((Subgroup.centralizer (C s : Set L)).subgroupOf
      (Subgroup.normalizer (C s : Set L))).index = 6)
    (hcent : ∀ s, ∀ c ∈ C s, c ≠ 1 → Subgroup.centralizer ({c} : Set L) = C s)
    (hcop : Nat.Coprime (Nat.card (C true)) (Nat.card (C false)))
    (hcop6 : ∀ s, Nat.Coprime 6 (Nat.card (C s)))
    (Y : Subgroup L) (hY : Odd (Nat.card Y)) (p : Bool → ℕ) (hp : ∀ s, (p s).Prime)
    (hpC : ∀ s, p s ∣ Nat.card (C s)) (hpY : ∀ s, p s ∣ Nat.card Y) : False := by
  have : Group.IsSolvable Y := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hY
  have hpne : p true ≠ p false := fun h =>
    (Nat.Prime.one_lt (hp true)).ne' (Nat.eq_one_of_dvd_coprimes hcop (hpC true) (h ▸ hpC false))
  obtain ⟨Z₀, hZ₀⟩ := hall_exists_of_solvable (G := Y) {p true, p false}
  have hpZ : ∀ s, p s ∣ Nat.card Z₀ := by
    intro s
    have h1 := Z₀.card_mul_index
    have h2 : ¬ p s ∣ Z₀.index := fun h => by
      have := hZ₀.2 (p s) (hp s) h
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at this
      cases s <;> simp_all
    exact ((Nat.Prime.dvd_mul (hp s)).mp (h1 ▸ hpY s)).resolve_right h2
  have : Nontrivial Z₀ := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    exact lt_of_lt_of_le (Nat.Prime.one_lt (hp true)) (Nat.le_of_dvd Nat.card_pos (hpZ true))
  obtain ⟨N₀, hN₀⟩ := exists_minimal_nontrivial_normal (G := Z₀)
  obtain ⟨r, hr, -, d, hd, hN₀card⟩ := minimal_normal_solvable_elementary N₀ hN₀ inferInstance
  have : Fact r.Prime := ⟨hr⟩
  have hrZ : r ∣ Nat.card Z₀ := by
    have := Subgroup.card_subgroup_dvd_card N₀
    rw [hN₀card] at this
    exact (dvd_pow_self r hd.ne').trans this
  obtain ⟨s, hrs⟩ : ∃ s, r = p s := by
    have := hZ₀.1 r hr hrZ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  set ιY := Y.subtype
  set ιZ := Z₀.subtype
  set Z : Subgroup L := Z₀.map ιY
  set N : Subgroup L := (N₀.map ιZ).map ιY
  have hNr : IsPGroup r N := by
    refine IsPGroup.of_card (n := d) ?_
    rw [Subgroup.card_map_of_injective Y.subtype_injective,
      Subgroup.card_map_of_injective Z₀.subtype_injective, hN₀card]
  have hN1 : N ≠ ⊥ := by
    intro h
    have h1 := congrArg (fun X : Subgroup L => Nat.card X) h
    simp only [Subgroup.card_bot] at h1
    rw [Subgroup.card_map_of_injective Y.subtype_injective,
      Subgroup.card_map_of_injective Z₀.subtype_injective, hN₀card] at h1
    exact (Nat.one_lt_pow hd.ne' hr.one_lt).ne' h1
  obtain ⟨g, hg⟩ := exists_conj_le_of_hall (hhall s) (hrs ▸ hpC s) hNr
  have hZN : Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (C s : Set L) := by
    obtain ⟨⟨c, hc⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hN1
    have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
    rintro _ ⟨z, hz, rfl⟩
    change g * z * g⁻¹ ∈ _
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    have hzc : (z₀ : L) * c * (z₀ : L)⁻¹ ∈ N := by
      obtain ⟨n₁, hn₁, rfl⟩ := hc
      obtain ⟨n₀, hn₀, rfl⟩ := hn₁
      have := hN₀.1.1.conj_mem n₀ hn₀ ⟨z₀, hz₀⟩
      exact ⟨_, ⟨_, this, rfl⟩, rfl⟩
    set w := g * (z₀ : L) * g⁻¹
    have hwc : w * (g * c * g⁻¹) * w⁻¹ = g * ((z₀ : L) * c * (z₀ : L)⁻¹) * g⁻¹ := by
      simp only [w]
      group
    have hc' : g * c * g⁻¹ ∈ C s := hg c hc
    have hwc' : w * (g * c * g⁻¹) * w⁻¹ ∈ C s := hwc ▸ hg _ hzc
    have hne1 : w * (g * c * g⁻¹) * w⁻¹ ≠ 1 := by
      rw [hwc]
      intro h1
      apply hc1'
      have := congrArg (fun x => (g * (z₀ : L))⁻¹ * x * (g * (z₀ : L))) h1
      simpa [mul_assoc] using this
    have hne1' : g * c * g⁻¹ ≠ 1 := by
      intro h1
      apply hc1'
      have := congrArg (fun x => g⁻¹ * x * g) h1
      simpa [mul_assoc] using this
    refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
    rw [← hcent s _ hwc' hne1]
    rw [← hcent s _ hc' hne1'] at hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc w * x * w⁻¹ * (w * (g * c * g⁻¹) * w⁻¹) = w * (x * (g * c * g⁻¹)) * w⁻¹ := by group
      _ = w * ((g * c * g⁻¹) * x) * w⁻¹ := by rw [hx]
      _ = w * (g * c * g⁻¹) * w⁻¹ * (w * x * w⁻¹) := by group
  have hcard : Nat.card Z₀ ∣ 6 * Nat.card (C s) := by
    rw [← card_normalizer_of_R6 (hab s) (hC1 s) (h6 s) (hcent s),
      ← Subgroup.card_map_of_injective Y.subtype_injective,
      ← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective]
    exact Subgroup.card_dvd_of_le hZN
  have hp' := (hpZ (!s)).trans hcard
  rcases (Nat.Prime.dvd_mul (hp (!s))).mp hp' with h | h
  · exact (Nat.Prime.one_lt (hp (!s))).ne' (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.symm (hcop6 (!s))) (hpC (!s)) h)
  · cases s
    · exact (Nat.Prime.one_lt (hp true)).ne' (Nat.eq_one_of_dvd_coprimes hcop (hpC true) h)
    · exact (Nat.Prime.one_lt (hp false)).ne' (Nat.eq_one_of_dvd_coprimes hcop h (hpC false))

end CFSG.Walter.W67
