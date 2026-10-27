module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT8Abs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Pointwise IsMulCommutative

variable {W : Type} [CommGroup W]

private lemma card_subgroupOf_of_le {G : Type*} [Group G] {E U : Subgroup G} (hU : U ≤ E) :
    Nat.card ↥(U.subgroupOf E) = Nat.card U := by
  rw [← Subgroup.card_subtype E (U.subgroupOf E), Subgroup.map_subgroupOf_eq_of_le hU]

theorem s15_T8_xbar [Finite W] {Mb : Subgroup (MulAut W)} {B : Fin 4 → Subgroup (MulAut W)}
    {Y : Fin 4 → Subgroup W} {r : ℕ} (hB : T8Blocks Mb B Y r) {S : Subgroup (MulAut W)}
    (hS : 3 ^ (4 * r - 3) ≤ Nat.card ↥((⨆ j, B j) ⊓ S)) :
    ∃ N : Subgroup (MulAut W), N ≤ Mb ∧ (∀ q ∈ Mb, ∀ x ∈ N, q * x * q⁻¹ ∈ N) ∧
      IsElemAbelian 3 N ∧ (∃ n : ℕ, 1 < n ∧ Nat.card N = 3 ^ n) ∧ N ≤ ⁅Mb, Mb⁆ ∧
      1 < pRank 3 (N ⊓ S) := by
  classical
  let E : Subgroup (MulAut W) := ⨆ j, B j
  let N : Subgroup (MulAut W) := ⁅E, Mb⁆
  have hEdef : E = ⨆ j, B j := rfl
  have hNdef : N = ⁅E, Mb⁆ := rfl
  have hr : 2 ≤ r := hB.two_le
  rw [← hEdef] at hS
  have hE_le_Mb : E ≤ Mb := by
    rw [hEdef]
    exact iSup_le fun j => hB.le j
  have hB0E : B 0 ≤ E := by
    rw [hEdef]
    exact le_iSup B 0
  have hcomm : Pairwise fun i j : Fin 4 =>
      ∀ x y : MulAut W, x ∈ B i → y ∈ B j → Commute x y :=
    fun i j hij x y hx hy => hB.commute i j hij x hx y hy
  have hind : iSupIndep B := by
    rw [iSupIndep_def]
    intro j
    rw [disjoint_iff]
    simpa only [Set.mem_setOf_eq] using hB.indep j
  let φ : (∀ j : Fin 4, B j) →* MulAut W := Subgroup.noncommPiCoprod (H := B) hcomm
  have hφinj : Function.Injective φ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have hφrange : φ.range = E := by
    rw [hEdef]
    exact Subgroup.noncommPiCoprod_range (hcomm := hcomm)
  have hdom_comm : ∀ u v : (∀ j : Fin 4, B j), u * v = v * u := by
    intro u v
    funext j
    haveI := hB.comm j
    exact mul_comm' (u j) (v j)
  have hdom3 : ∀ u : (∀ j : Fin 4, B j), u ^ 3 = 1 := by
    intro u
    funext j
    simpa only [Pi.pow_apply, Pi.one_apply] using Subtype.ext (hB.cube j (u j) (u j).2)
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have hxφ : x ∈ φ.range := by rwa [hφrange]
    have hyφ : y ∈ φ.range := by rwa [hφrange]
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hxφ
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.1 hyφ
    rw [← map_mul, ← map_mul, hdom_comm u v]
  have hEexp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    have hxφ : x ∈ φ.range := by rwa [hφrange]
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hxφ
    rw [← map_pow, hdom3 u, map_one]
  have hEcard : Nat.card E = 3 ^ (4 * r) := by
    have h1 : Nat.card (∀ j : Fin 4, B j) = Nat.card E := by
      rw [← hφrange]
      exact Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    calc Nat.card E = Nat.card (∀ j : Fin 4, B j) := h1.symm
      _ = ∏ j : Fin 4, Nat.card (B j) := Nat.card_pi
      _ = ∏ _j : Fin 4, 3 ^ r := Finset.prod_congr rfl (fun j _ => hB.card j)
      _ = (3 ^ r) ^ 4 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = 3 ^ (4 * r) := by rw [← pow_mul, Nat.mul_comm]
  have hNle_E : N ≤ E := by
    rw [hNdef, Subgroup.commutator_le]
    intro e he q hq
    have hconj : q * e⁻¹ * q⁻¹ ∈ E := hB.normal q hq e⁻¹ (E.inv_mem he)
    have heq : ⁅e, q⁆ = e * (q * e⁻¹ * q⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact E.mul_mem he hconj
  have hNormal : ∀ q ∈ Mb, ∀ x ∈ N, q * x * q⁻¹ ∈ N := by
    intro q hq x hx
    have hmem : q ∈ Subgroup.normalizer ((⁅E, Mb⁆ : Subgroup (MulAut W)) :
        Set (MulAut W)) :=
      Subgroup.normalizer_commutator_ge_right (H₁ := E) (H₂ := Mb) hq
    have hx' : x ∈ (⁅E, Mb⁆ : Subgroup (MulAut W)) := by rwa [← hNdef]
    have hres : q * x * q⁻¹ ∈ (⁅E, Mb⁆ : Subgroup (MulAut W)) :=
      (Subgroup.mem_normalizer_iff.mp hmem x).mp hx'
    rwa [← hNdef] at hres
  have hNle_Mb : N ≤ Mb := by
    rw [hNdef]
    exact Subgroup.commutator_le_of_le hE_le_Mb le_rfl
  have hNle_MbMb : N ≤ ⁅Mb, Mb⁆ := by
    rw [hNdef]
    exact Subgroup.commutator_mono hE_le_Mb le_rfl
  have hN_el : IsElemAbelian 3 N :=
    ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext
        (hEab a.1 (hNle_E a.2) b.1 (hNle_E b.2))),
      fun x hx => hEexp x (hNle_E hx)⟩
  have hE_eq : E = B 0 ⊔ N := by
    refine le_antisymm ?_ (sup_le hB0E hNle_E)
    rw [hEdef]
    refine iSup_le fun j => ?_
    obtain ⟨q, hq, hqj⟩ := hB.trans j
    rw [hqj]
    rintro b ⟨b₀, hb₀, rfl⟩
    have hcommN : ⁅q, b₀⁆ ∈ N := by
      have hmem : ⁅q, b₀⁆ ∈ ⁅Mb, E⁆ :=
        Subgroup.commutator_mem_commutator (H₁ := Mb) (H₂ := E) hq (hB0E hb₀)
      rwa [Subgroup.commutator_comm, ← hNdef] at hmem
    have hb : (MulAut.conj q).toMonoidHom b₀ = ⁅q, b₀⁆ * b₀ := by
      simp only [commutatorElement_def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hb]
    exact (B 0 ⊔ N).mul_mem (Subgroup.mem_sup_right hcommN) (Subgroup.mem_sup_left hb₀)
  have hN_lower : 3 ^ (3 * r) ≤ Nat.card N := by
    haveI hEcomm : IsMulCommutative ↥E :=
      IsMulCommutative.of_comm (fun a b => Subtype.ext (hEab a.1 a.2 b.1 b.2))
    have hsup : (B 0).subgroupOf E ⊔ N.subgroupOf E = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hB0E hNle_E, hE_eq, Subgroup.subgroupOf_self]
    have hinf : (B 0).subgroupOf E ⊓ N.subgroupOf E = (B 0 ⊓ N).subgroupOf E := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    have hcard := card_sup_mul_card_inf ((B 0).subgroupOf E) (N.subgroupOf E)
    have hs : Nat.card ↥((B 0).subgroupOf E ⊔ N.subgroupOf E) = 3 ^ (4 * r) := by
      rw [hsup, Subgroup.card_top, hEcard]
    have hi : Nat.card ↥((B 0).subgroupOf E ⊓ N.subgroupOf E) = Nat.card ↥(B 0 ⊓ N) := by
      rw [hinf, card_subgroupOf_of_le (E := E) (U := B 0 ⊓ N) (inf_le_left.trans hB0E)]
    have hu : Nat.card ↥((B 0).subgroupOf E) = 3 ^ r := by
      rw [card_subgroupOf_of_le (E := E) (U := B 0) hB0E, hB.card 0]
    have hk : Nat.card ↥(N.subgroupOf E) = Nat.card N :=
      card_subgroupOf_of_le (E := E) (U := N) hNle_E
    have hformula : 3 ^ (4 * r) * Nat.card ↥(B 0 ⊓ N) = 3 ^ r * Nat.card N := by
      calc 3 ^ (4 * r) * Nat.card ↥(B 0 ⊓ N)
          = Nat.card ↥((B 0).subgroupOf E ⊔ N.subgroupOf E) *
              Nat.card ↥((B 0).subgroupOf E ⊓ N.subgroupOf E) := by rw [← hs, ← hi]
        _ = Nat.card ↥((B 0).subgroupOf E) * Nat.card ↥(N.subgroupOf E) := hcard
        _ = 3 ^ r * Nat.card N := by rw [hu, hk]
    have hpos : 1 ≤ Nat.card ↥(B 0 ⊓ N) := Nat.card_pos
    have hbound : 3 ^ (4 * r) ≤ 3 ^ r * Nat.card N := by
      calc 3 ^ (4 * r) = 3 ^ (4 * r) * 1 := (mul_one _).symm
        _ ≤ 3 ^ (4 * r) * Nat.card ↥(B 0 ⊓ N) := Nat.mul_le_mul_left _ hpos
        _ = 3 ^ r * Nat.card N := hformula
    have hsplit : 3 ^ (4 * r) = 3 ^ r * 3 ^ (3 * r) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit] at hbound
    exact Nat.le_of_mul_le_mul_left hbound (Nat.pow_pos (by norm_num : 0 < 3))
  have hN_isPGroup : IsPGroup 3 ↥N := fun x =>
    ⟨1, by simpa using Subtype.ext (hN_el.2 x.1 x.2)⟩
  have h27 : 3 ^ 3 ≤ Nat.card ↥(N ⊓ S) := by
    haveI hEcomm : IsMulCommutative ↥E :=
      IsMulCommutative.of_comm (fun a b => Subtype.ext (hEab a.1 a.2 b.1 b.2))
    have hNC : N ⊓ (E ⊓ S) = N ⊓ S := by
      ext x
      constructor
      · intro hx
        exact ⟨(Subgroup.mem_inf.mp hx).1,
          (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).2⟩
      · intro hx
        exact ⟨(Subgroup.mem_inf.mp hx).1,
          ⟨hNle_E (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩⟩
    have hsup_le : N ⊔ (E ⊓ S) ≤ E := sup_le hNle_E inf_le_left
    have hNCE : N ⊓ (E ⊓ S) ≤ E := inf_le_right.trans inf_le_left
    have hsupw : N.subgroupOf E ⊔ (E ⊓ S).subgroupOf E = (N ⊔ (E ⊓ S)).subgroupOf E :=
      (Subgroup.subgroupOf_sup hNle_E inf_le_left).symm
    have hinfw : N.subgroupOf E ⊓ (E ⊓ S).subgroupOf E =
        (N ⊓ (E ⊓ S)).subgroupOf E := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    have hcard := card_sup_mul_card_inf (N.subgroupOf E) ((E ⊓ S).subgroupOf E)
    have hs : Nat.card ↥(N.subgroupOf E ⊔ (E ⊓ S).subgroupOf E) =
        Nat.card ↥(N ⊔ (E ⊓ S)) := by
      rw [hsupw]
      exact card_subgroupOf_of_le (E := E) (U := N ⊔ (E ⊓ S)) hsup_le
    have hi : Nat.card ↥(N.subgroupOf E ⊓ (E ⊓ S).subgroupOf E) = Nat.card ↥(N ⊓ S) := by
      rw [hinfw, card_subgroupOf_of_le (E := E) (U := N ⊓ (E ⊓ S)) hNCE, hNC]
    have hu : Nat.card ↥(N.subgroupOf E) = Nat.card N :=
      card_subgroupOf_of_le (E := E) (U := N) hNle_E
    have hk : Nat.card ↥((E ⊓ S).subgroupOf E) = Nat.card ↥(E ⊓ S) :=
      card_subgroupOf_of_le (E := E) (U := E ⊓ S) inf_le_left
    have hformula : Nat.card ↥(N ⊔ (E ⊓ S)) * Nat.card ↥(N ⊓ S) =
        Nat.card N * Nat.card ↥(E ⊓ S) := by
      calc Nat.card ↥(N ⊔ (E ⊓ S)) * Nat.card ↥(N ⊓ S)
          = Nat.card ↥(N.subgroupOf E ⊔ (E ⊓ S).subgroupOf E) *
              Nat.card ↥(N.subgroupOf E ⊓ (E ⊓ S).subgroupOf E) := by rw [← hs, ← hi]
        _ = Nat.card ↥(N.subgroupOf E) * Nat.card ↥((E ⊓ S).subgroupOf E) := hcard
        _ = Nat.card N * Nat.card ↥(E ⊓ S) := by rw [hu, hk]
    have hsteps : 3 ^ (3 * r) * 3 ^ (4 * r - 3) ≤ Nat.card ↥(N ⊓ S) * Nat.card E := by
      calc 3 ^ (3 * r) * 3 ^ (4 * r - 3) ≤ Nat.card N * Nat.card ↥(E ⊓ S) :=
              Nat.mul_le_mul hN_lower hS
        _ = Nat.card ↥(N ⊔ (E ⊓ S)) * Nat.card ↥(N ⊓ S) := hformula.symm
        _ ≤ Nat.card E * Nat.card ↥(N ⊓ S) :=
              Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hsup_le)
        _ = Nat.card ↥(N ⊓ S) * Nat.card E := Nat.mul_comm _ _
    rw [hEcard] at hsteps
    have hexp : 3 ^ (3 * r) * 3 ^ (4 * r - 3) = 3 ^ (3 * r - 3) * 3 ^ (4 * r) := by
      have h : 3 * r + (4 * r - 3) = (3 * r - 3) + 4 * r := by omega
      calc 3 ^ (3 * r) * 3 ^ (4 * r - 3) = 3 ^ (3 * r + (4 * r - 3)) :=
            (pow_add 3 (3 * r) (4 * r - 3)).symm
        _ = 3 ^ ((3 * r - 3) + 4 * r) := by rw [h]
        _ = 3 ^ (3 * r - 3) * 3 ^ (4 * r) := pow_add 3 (3 * r - 3) (4 * r)
    rw [hexp] at hsteps
    have hcancel : 3 ^ (3 * r - 3) ≤ Nat.card ↥(N ⊓ S) :=
      Nat.le_of_mul_le_mul_right hsteps (Nat.pow_pos (by norm_num : 0 < 3))
    have h33 : 3 ^ 3 ≤ 3 ^ (3 * r - 3) :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mpr (by omega)
    exact h33.trans hcancel
  have hP_el : IsElemAbelian 3 (N ⊓ S) :=
    ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext
        (hEab a.1 (hNle_E (Subgroup.mem_inf.mp a.2).1)
          b.1 (hNle_E (Subgroup.mem_inf.mp b.2).1))),
      fun x hx => hEexp x (hNle_E (Subgroup.mem_inf.mp hx).1)⟩
  have hP_isPGroup : IsPGroup 3 ↥(N ⊓ S) := fun x =>
    ⟨1, by simpa using Subtype.ext (hP_el.2 x.1 x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP_isPGroup
  have hk3 : 3 ≤ k := by
    have hk' : 3 ^ 3 ≤ 3 ^ k := by rwa [hk] at h27
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hk'
  have hk_le : k ≤ pRank 3 (N ⊓ S) := by
    refine le_csSup ?_ ⟨N ⊓ S, le_rfl, hP_el, hk⟩
    refine ⟨Nat.card (MulAut W), ?_⟩
    rintro m ⟨E', -, hE'el, hE'card⟩
    have h1 : m < 3 ^ m := Nat.lt_pow_self (by norm_num : 1 < 3)
    have h2 : Nat.card E' ≤ Nat.card (MulAut W) := Subgroup.card_le_card_group E'
    have h3 : m < Nat.card E' := by rwa [← hE'card] at h1
    omega
  have hprank : 1 < pRank 3 (N ⊓ S) := by omega
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hN_isPGroup
  have hn3 : 3 * r ≤ n := by
    have hn' : 3 ^ (3 * r) ≤ 3 ^ n := by rwa [hn] at hN_lower
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hn'
  exact ⟨N, hNle_Mb, hNormal, hN_el, ⟨n, by omega, hn⟩, hNle_MbMb, hprank⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
