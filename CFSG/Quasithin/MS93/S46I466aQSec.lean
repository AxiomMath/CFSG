module

public import CFSG.Quasithin.MS93.S46I467TLab
public import CFSG.Quasithin.MS93.S46Ker
public import CFSG.Quasithin.MS93.S4AFAbs
public import CFSG.Quasithin.MS93.S4AFSec

public section

namespace CFSG.Quasithin.MS93.S46.QMix

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S4A.F
open scoped commutatorElement

section Grp

variable {𝔾 : Type*} [Group 𝔾]

theorem relIndex_ne_zero_of_finite' {H K : Subgroup 𝔾} [Finite K] : H.relIndex K ≠ 0 := by
  intro h0
  have := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [h0, zero_mul] at this
  exact Nat.card_pos.ne' this.symm

theorem commutator_sup_le_of {H₁ H₂ A N : Subgroup 𝔾}
    (hN₁ : H₁ ≤ Subgroup.normalizer (N : Set 𝔾)) (hN₂ : H₂ ≤ Subgroup.normalizer (N : Set 𝔾))
    (h₁ : ⁅H₁, A⁆ ≤ N) (h₂ : ⁅H₂, A⁆ ≤ N) : ⁅H₁ ⊔ H₂, A⁆ ≤ N := by
  let S : Subgroup 𝔾 :=
    { carrier := {y | y ∈ Subgroup.normalizer (N : Set 𝔾) ∧ ∀ x ∈ A, ⁅y, x⁆ ∈ N}
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, k₁⟩ ⟨hy₂, k₂⟩
        refine ⟨mul_mem hy₁ hy₂, fun x hx => ?_⟩
        have e : ⁅y₁ * y₂, x⁆ = y₁ * ⁅y₂, x⁆ * y₁⁻¹ * ⁅y₁, x⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.mp hy₁ _).mp (k₂ x hx)) (k₁ x hx)
      inv_mem' := by
        rintro y ⟨hy, k⟩
        refine ⟨inv_mem hy, fun x hx => ?_⟩
        have e : ⁅y⁻¹, x⁆ = y⁻¹ * ⁅y, x⁆⁻¹ * y := by
          simp only [commutatorElement_def]; group
        rw [e]
        have hy' : y⁻¹ ∈ Subgroup.normalizer (N : Set 𝔾) := inv_mem hy
        have := (Subgroup.mem_normalizer_iff.mp hy' _).mp (inv_mem (k x hx))
        simpa [mul_assoc] using this }
  have hS : H₁ ⊔ H₂ ≤ S := by
    refine sup_le (fun y hy => ⟨hN₁ hy, fun x hx => ?_⟩) (fun y hy => ⟨hN₂ hy, fun x hx => ?_⟩)
    · exact h₁ (Subgroup.commutator_mem_commutator hy hx)
    · exact h₂ (Subgroup.commutator_mem_commutator hy hx)
  rw [Subgroup.commutator_le]
  intro y hy x hx
  exact (hS hy).2 x hx

theorem exists_mem_sq_mem_commutator_mem {Q P : Subgroup 𝔾} [Finite Q] (hQ : IsPGroup 2 Q)
    (hPQ : P ≤ Q) (hQP : Q ≤ Subgroup.normalizer (P : Set 𝔾)) (hne : P ≠ Q) :
    ∃ q ∈ Q, q ∉ P ∧ q ^ 2 ∈ P ∧ ∀ r ∈ Q, ⁅q, r⁆ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (P.subgroupOf Q).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPQ).mpr hQP
  have hmk : ∀ x : ↥Q, (x : ↥Q ⧸ P.subgroupOf Q) = 1 ↔ (x : 𝔾) ∈ P := fun x => by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hQb : IsPGroup 2 (↥Q ⧸ P.subgroupOf Q) := hQ.to_quotient _
  have : Nontrivial (↥Q ⧸ P.subgroupOf Q) := by
    obtain ⟨q, hqQ, hqP⟩ : ∃ q ∈ Q, q ∉ P := by
      by_contra hno
      push Not at hno
      exact hne (le_antisymm hPQ hno)
    refine ⟨⟨((⟨q, hqQ⟩ : ↥Q) : ↥Q ⧸ P.subgroupOf Q), 1, fun he => hqP ?_⟩⟩
    exact (hmk ⟨q, hqQ⟩).mp he
  have hZ := hQb.center_nontrivial
  have hZp : IsPGroup 2 ↥(Subgroup.center (↥Q ⧸ P.subgroupOf Q)) := hQb.to_subgroup _
  obtain ⟨k, hk, hcard⟩ := (hZp.nontrivial_iff_card).mp hZ
  have : Fintype ↥(Subgroup.center (↥Q ⧸ P.subgroupOf Q)) := Fintype.ofFinite _
  have hdvd : 2 ∣ Fintype.card ↥(Subgroup.center (↥Q ⧸ P.subgroupOf Q)) := by
    rw [Fintype.card_eq_nat_card, hcard]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 2 hdvd
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (z : ↥Q ⧸ P.subgroupOf Q)
  have hzc : ∀ w : ↥Q ⧸ P.subgroupOf Q, (z : ↥Q ⧸ P.subgroupOf Q) * w = w * z :=
    fun w => (Subgroup.mem_center_iff.mp z.2 w).symm
  refine ⟨q, q.2, fun hqP => ?_, ?_, fun r hr => ?_⟩
  · have h1 : (z : ↥Q ⧸ P.subgroupOf Q) = 1 := by rw [← hq]; exact (hmk q).mpr hqP
    have h2 : z = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hz
    omega
  · have h1 : ((q ^ 2 : ↥Q) : ↥Q ⧸ P.subgroupOf Q) = 1 := by
      rw [QuotientGroup.mk_pow, hq, ← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one,
        Subgroup.coe_one]
    have := (hmk (q ^ 2)).mp h1
    rwa [Subgroup.coe_pow] at this
  · have h1 : ((⁅q, ⟨r, hr⟩⁆ : ↥Q) : ↥Q ⧸ P.subgroupOf Q) = 1 := by
      rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, hq, hzc, mul_assoc, mul_assoc,
        mul_inv_cancel_left, mul_inv_cancel]
    have := (hmk _).mp h1
    simpa [commutatorElement_def] using this

end Grp

section Abs

theorem eq_of_card_commV_lt {H : Type*} [Group H] {F : Type} [Field F] [Finite F] {n : ℕ}
    {X : Type} [CommGroup X] [Finite X] (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1)
    {ψ : H →* SL3 F} (hψ : Function.Surjective ψ) {σ : H →* MulAut X} (hker : ψ.ker ≤ σ.ker)
    {a : H} (ha1 : ψ a ≠ 1) (ha2 : ψ a * ψ a = 1)
    (hlt : Nat.card (commV (Subgroup.zpowers (σ a))) < Nat.card F) (g : H) (x : X) :
    σ g x = x := by
  by_contra hne
  have := le_card_commV_zpowers hF hX2 (liftRho ψ hψ σ hker) (liftRho_nt hψ hker ⟨g, x, hne⟩)
    ha1 ha2
  rw [liftRho_apply] at this
  omega

end Abs

section Section

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem commutator_stab_le_of_section {y : Vtx (puAmalgam h.le)} (hy : IsMVtx _ y)
    {A B C : Subgroup (puAmalgam h.le).Universal} (hAs : A ≤ stab _ y)
    (hAn : stab (puAmalgam h.le) y ≤ Subgroup.normalizer (A : Set (puAmalgam h.le).Universal))
    (hBn : stab (puAmalgam h.le) y ≤ Subgroup.normalizer (B : Set (puAmalgam h.le).Universal))
    (hBC : B ≤ C) (hCA : C ≤ A) (hA2 : ∀ a ∈ A, a ^ 2 ∈ B) (hAA : ⁅A, A⁆ ≤ B)
    (hAQ : ⁅A, Qv (puAmalgam h.le) y⁆ ≤ B) {t : (puAmalgam h.le).Universal}
    (ht : t ∈ stab (puAmalgam h.le) y) (htQ : t ∉ Qv (puAmalgam h.le) y)
    (ht2 : t ^ 2 ∈ Qv (puAmalgam h.le) y) (hCt : ∀ c ∈ C, ⁅c, t⁆ ∈ B)
    (hidx : C.relIndex A < Fintype.card F) : ⁅A, stab (puAmalgam h.le) y⁆ ≤ B := by
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have hBA : B ≤ A := hBC.trans hCA
  have : Finite ↥(stab (puAmalgam h.le) y) := finite_stab h hy
  have : Finite ↥A := Finite.of_injective _ (Subgroup.inclusion_injective hAs)
  have : Finite ↥C := Finite.of_injective _ (Subgroup.inclusion_injective hCA)
  obtain ⟨ψ₀, hψ₀s, hψ₀⟩ := exists_natural_Uloc h hφ hy
  have hψs : Function.Surjective (toSL3 ψ₀) := toSL3_surjective hψ₀s
  obtain ⟨X, _, π, ρ, hπs, hπk, hρ⟩ := exists_quotient_conj (K := stab (puAmalgam h.le) y) hAn
    hBA hBn (fun v hv w hw => hAA (Subgroup.commutator_mem_commutator hv hw))
  have : Finite X := Finite.of_surjective π hπs
  have hX2 : ∀ x : X, x ^ 2 = 1 := by
    intro x
    obtain ⟨v, rfl⟩ := hπs x
    rw [← map_pow]
    refine (hπk _).mpr ?_
    rw [Subgroup.coe_pow]
    exact hA2 v v.2
  have hQA : ⁅Qv (puAmalgam h.le) y, A⁆ ≤ B := by rw [Subgroup.commutator_comm]; exact hAQ
  have hker : (toSL3 ψ₀).ker ≤ ρ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    have hkQ : (k : (puAmalgam h.le).Universal) ∈ Qv (puAmalgam h.le) y :=
      (toSL3_eq_one_iff_mem_qv h hφ hy hψ₀ k).mp hk
    ext x
    obtain ⟨v, rfl⟩ := hπs x
    rw [hρ, MulAut.one_apply]
    have h1 : π (conjOn hAn k v) * (π v)⁻¹ = 1 := by
      rw [← map_inv, ← map_mul]
      refine (hπk _).mpr ?_
      have e : ((conjOn hAn k v * v⁻¹ : ↥A) : (puAmalgam h.le).Universal) =
          ⁅(k : (puAmalgam h.le).Universal), (v : (puAmalgam h.le).Universal)⁆ := by
        rw [Subgroup.coe_mul, coe_conjOn_apply, Subgroup.coe_inv, commutatorElement_def]
      rw [e]
      exact hQA (Subgroup.commutator_mem_commutator hkQ v.2)
    exact mul_inv_eq_one.mp h1
  set a : ↥(stab (puAmalgam h.le) y) := ⟨t, ht⟩ with ha
  have ha1 : toSL3 ψ₀ a ≠ 1 := fun h1 => htQ ((toSL3_eq_one_iff_mem_qv h hφ hy hψ₀ a).mp h1)
  have ha2 : toSL3 ψ₀ a * toSL3 ψ₀ a = 1 := by
    rw [← map_mul]
    refine (toSL3_eq_one_iff_mem_qv h hφ hy hψ₀ _).mpr ?_
    have e : ((a * a : ↥(stab (puAmalgam h.le) y)) : (puAmalgam h.le).Universal) = t ^ 2 := by
      rw [sq]; rfl
    rw [e]
    exact ht2
  have hlt : Nat.card (commV (Subgroup.zpowers (ρ a))) < Nat.card F := by
    have hcf := card_commV_mul_card_fixV_zpowers (ρ a)
    set S : Subgroup X := (C.subgroupOf A).map π with hS
    have hSfix : S ≤ fixV (Subgroup.zpowers (ρ a)) := by
      rintro _ ⟨c, hc, rfl⟩
      rw [mem_fixV]
      intro g hg
      have hfix : ρ a (π c) = π c := by
        rw [hρ]
        have h1 : π (conjOn hAn a c) * (π c)⁻¹ = 1 := by
          rw [← map_inv, ← map_mul]
          refine (hπk _).mpr ?_
          have e : ((conjOn hAn a c * c⁻¹ : ↥A) : (puAmalgam h.le).Universal) =
              ⁅(c : (puAmalgam h.le).Universal), t⁆⁻¹ := by
            rw [Subgroup.coe_mul, coe_conjOn_apply, Subgroup.coe_inv, commutatorElement_inv,
              commutatorElement_def]
          rw [e]
          exact B.inv_mem (hCt c (Subgroup.mem_subgroupOf.mp hc))
        exact mul_inv_eq_one.mp h1
      have hst : Subgroup.zpowers (ρ a) ≤ MulAction.stabilizer (MulAut X) (π c) := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hfix
      have := hst hg
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
    have hcardS : Nat.card S = B.relIndex C := by
      rw [← card_pre hπk hBA hπs S, hS, pre_map hπk hBC hCA]
    have hcardX : Nat.card X = B.relIndex A := by
      rw [← Subgroup.card_top (G := X), ← card_pre hπk hBA hπs ⊤, pre_top]
    have htow := Subgroup.relIndex_mul_relIndex B C A hBC hCA
    have hle : Nat.card S ≤ Nat.card (fixV (Subgroup.zpowers (ρ a))) :=
      Subgroup.card_le_of_le hSfix
    have hpos : 0 < B.relIndex C := Nat.pos_of_ne_zero relIndex_ne_zero_of_finite'
    have h1 : Nat.card (commV (Subgroup.zpowers (ρ a))) * B.relIndex C ≤
        C.relIndex A * B.relIndex C := by
      calc Nat.card (commV (Subgroup.zpowers (ρ a))) * B.relIndex C
          ≤ Nat.card (commV (Subgroup.zpowers (ρ a))) *
              Nat.card (fixV (Subgroup.zpowers (ρ a))) :=
            Nat.mul_le_mul_left _ (hcardS ▸ hle)
        _ = C.relIndex A * B.relIndex C := by rw [hcf, hcardX, ← htow, mul_comm]
    have h2 := Nat.le_of_mul_le_mul_right h1 hpos
    rw [Nat.card_eq_fintype_card (α := F)]
    omega
  have htriv := eq_of_card_commV_lt hFn hX2 hψs hker ha1 ha2 hlt
  have hfix := commutator_pre_le_of_fix hρ (C := ⊤) (S := ⊥) (fun k c _ => by
    rw [htriv k c, mul_inv_cancel]; exact Subgroup.one_mem _)
  rwa [pre_top, pre_bot hπk hBA] at hfix

end Section

end CFSG.Quasithin.MS93.S46.QMix
