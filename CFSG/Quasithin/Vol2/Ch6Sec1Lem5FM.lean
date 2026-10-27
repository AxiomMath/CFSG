module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FL
public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.Quasithin.Vol2.Ch10SecECase1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

section A6

open Equiv

theorem isSimpleGroup_alt_six_ch615 : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem card_alt_six_ch615 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  have := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_perm, Nat.card_fin, show Nat.factorial 6 = 720 from rfl] at this
  omega

theorem not_isSolvable_alt_six_ch615 : ¬ Group.IsSolvable ↥(alternatingGroup (Fin 6)) := by
  intro hs
  have := isSimpleGroup_alt_six_ch615
  have hc := IsSimpleGroup.comm_iff_isSolvable.mpr hs
  have h := hc ⟨swap 0 1 * swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
    ⟨swap 2 3 * swap 3 4, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
  have h' := congrArg Subtype.val h
  revert h'
  decide

theorem exists_eq_conj_alt_six_ch615 (α : MulAut ↥(alternatingGroup (Fin 6)))
    (hα : Odd (orderOf α)) : ∃ g, α = MulAut.conj g := by
  have hP := CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six
  have hinn : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥(alternatingGroup (Fin 6)) := by
    obtain ⟨k, hk⟩ := hP (QuotientGroup.mk'
      (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(alternatingGroup (Fin 6))) α)
    have hdvd := orderOf_map_dvd (QuotientGroup.mk'
      (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(alternatingGroup (Fin 6)))) α
    have h1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_right k (hα.of_dvd_nat hdvd).coprime_two_right)
      (orderOf_dvd_of_pow_eq_one hk)
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨g, hg⟩ := hinn
  exact ⟨g, hg.symm⟩

theorem selfNormalizing_alt_six_ch615 : ∀ S₀ : Subgroup ↥(alternatingGroup (Fin 6)),
    IsSylowTwoOf S₀ ⊤ → ∀ g, (∀ s ∈ S₀, g * s * g⁻¹ ∈ S₀) → g ∈ S₀ := by
  obtain ⟨P, hP⟩ := CFSG.LieType.SteinbergBR.SmallAlt.exists_selfNormalizing_six
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPs : IsSylowTwoOf (P : Subgroup ↥(alternatingGroup (Fin 6))) ⊤ :=
    ⟨le_top, P.isPGroup', fun h2 => by
      change 2 ∣ (P : Subgroup ↥(alternatingGroup (Fin 6))).relIndex ⊤ at h2
      rw [Subgroup.relIndex_top_right] at h2
      exact P.not_dvd_index h2⟩
  have hP' : Subgroup.normalizer (((P : Subgroup ↥(alternatingGroup (Fin 6))) :
      Set ↥(alternatingGroup (Fin 6)))) = (P : Subgroup ↥(alternatingGroup (Fin 6))) := hP
  refine selfNormalizing_of_sylow_ch615 hPs fun g hg => ?_
  have := mem_normalizer_of_conj_mem_l32_ch615 hg
  rwa [hP'] at this

theorem index_ge_six_alt_six_ch615 (R : Subgroup ↥(alternatingGroup (Fin 6))) (hR : R ≠ ⊤) :
    6 ≤ R.index := by
  have := isSimpleGroup_alt_six_ch615
  rcases (Subgroup.normalCore_normal R).eq_bot_or_eq_top with hb | ht
  · have hinj : Function.Injective
        (MulAction.toPermHom ↥(alternatingGroup (Fin 6)) (↥(alternatingGroup (Fin 6)) ⧸ R)) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hb]
    have h := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm (α := ↥(alternatingGroup (Fin 6)) ⧸ R), ← Subgroup.index,
      card_alt_six_ch615] at h
    by_contra hlt
    have h5 : R.index ≤ 5 := by omega
    have := Nat.factorial_le h5
    rw [show Nat.factorial 5 = 120 from rfl] at this
    omega
  · exact absurd (top_le_iff.mp (ht ▸ Subgroup.normalCore_le R)) hR

theorem card_sylow_alt_six_ch615 {S₀ : Subgroup ↥(alternatingGroup (Fin 6))}
    (hS₀ : IsSylowTwoOf S₀ ⊤) : Nat.card S₀ = 8 := by
  obtain ⟨-, hS2, hodd⟩ := hS₀
  change ¬ 2 ∣ S₀.relIndex ⊤ at hodd
  rw [Subgroup.relIndex_top_right] at hodd
  have h := S₀.card_mul_index
  rw [card_alt_six_ch615] at h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
  rw [hk] at h ⊢
  have hk9 : k < 9 := by
    by_contra hk'
    have h1 : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hk')
    have h2 : 2 ^ k ≤ 360 := Nat.le_of_dvd (by norm_num) ⟨_, h.symm⟩
    omega
  interval_cases k <;> omega

theorem mem_of_conj_mem_overgroup_alt_six_ch615 {S₀ : Subgroup ↥(alternatingGroup (Fin 6))}
    (hS₀ : IsSylowTwoOf S₀ ⊤) {R₀ : Subgroup ↥(alternatingGroup (Fin 6))} (hSR : S₀ ≤ R₀)
    (hRS : R₀ ≠ S₀) (hR : Group.IsSolvable ↥R₀) (g : ↥(alternatingGroup (Fin 6)))
    (hg : ∀ r ∈ R₀, g * r * g⁻¹ ∈ R₀) : g ∈ R₀ := by
  have := isSimpleGroup_alt_six_ch615
  have h8 := card_sylow_alt_six_ch615 hS₀
  have hRtop : R₀ ≠ ⊤ := fun h => by
    subst h
    have := hR
    exact not_isSolvable_alt_six_ch615 (Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(alternatingGroup (Fin 6))) ≃* _).toMonoidHom)
      (MulEquiv.surjective _))
  have hidxR := index_ge_six_alt_six_ch615 R₀ hRtop
  have hcR := R₀.card_mul_index
  rw [card_alt_six_ch615] at hcR
  obtain ⟨k, hk⟩ : 8 ∣ Nat.card R₀ := h8 ▸ Subgroup.card_dvd_of_le hSR
  rw [hk] at hcR
  have hk1 : k ≠ 1 := fun h => hRS (Subgroup.eq_of_le_of_card_ge hSR (by rw [hk, h, h8])).symm
  have hk7 : k ≤ 7 := by
    by_contra hk'
    have := Nat.mul_le_mul (show 8 * 8 ≤ 8 * k by omega) hidxR
    omega
  set N := Subgroup.normalizer (R₀ : Set ↥(alternatingGroup (Fin 6))) with hN
  have hgN : g ∈ N := mem_normalizer_of_conj_mem_l32_ch615 hg
  have hRN : R₀ ≤ N := Subgroup.le_normalizer
  have hNtop : N ≠ ⊤ := fun h => by
    have hn : R₀.Normal := Subgroup.normalizer_eq_top_iff.mp h
    rcases hn.eq_bot_or_eq_top with hb | ht
    · rw [hb, Subgroup.card_bot] at hk
      omega
    · exact hRtop ht
  have hidxN := index_ge_six_alt_six_ch615 N hNtop
  have hcN := N.card_mul_index
  rw [card_alt_six_ch615] at hcN
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hRN
  rw [hk] at hj
  rw [hj] at hcN
  have hj1 : j = 1 := by
    interval_cases k <;> (try omega) <;>
    · have hj3 : j ≤ 2 := by
        by_contra hj'
        have := Nat.mul_le_mul (show 3 ≤ j by omega) hidxN
        nlinarith
      interval_cases j <;> omega
  have hNR : N = R₀ := (Subgroup.eq_of_le_of_card_ge hRN (by rw [hj, hk, hj1, mul_one])).symm
  rw [← hNR]
  exact hgN

theorem dLemmaFacts_alt_six_ch615 {Γ : Type*} [Group Γ] [Finite Γ] {F : Subgroup Γ}
    (e : ↥F ≃* ↥(alternatingGroup (Fin 6))) : DLemmaFacts_ch615 F :=
  dLemmaFacts_of_mulEquiv_ch615 e not_isSolvable_alt_six_ch615 exists_eq_conj_alt_six_ch615
    selfNormalizing_alt_six_ch615 fun _ hS₀ _ hSR hRS hR g hg =>
      mem_of_conj_mem_overgroup_alt_six_ch615 hS₀ hSR hRS hR g hg

end A6

section Case4

variable {Γ : Type*} [Group Γ]

theorem commutator_sup_zpowers_le_ch615 {E : Subgroup Γ} {t : Γ}
    (ht : t ∈ Subgroup.normalizer (E : Set Γ)) :
    ⁅E ⊔ Subgroup.zpowers t, E ⊔ Subgroup.zpowers t⁆ ≤ E := by
  have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (E : Set Γ) := Subgroup.zpowers_le.mpr ht
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left E (Subgroup.zpowers t) hle
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← SetLike.mem_coe, hcoe] at hx hy
  obtain ⟨e₁, he₁, u, hu, rfl⟩ := hx
  obtain ⟨e₂, he₂, v, hv, rfl⟩ := hy
  have huv : u⁻¹ * v = v * u⁻¹ := by
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_zpow_self t a b).inv_left.eq
  have h1 : u * e₂ * u⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hle hu) e₂).mp he₂
  have h2 : v * e₁⁻¹ * v⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hle hv) e₁⁻¹).mp (E.inv_mem he₁)
  have key : ⁅e₁ * u, e₂ * v⁆ = e₁ * (u * e₂ * u⁻¹) * (v * e₁⁻¹ * v⁻¹) * e₂⁻¹ := by
    rw [commutatorElement_def]
    calc e₁ * u * (e₂ * v) * (e₁ * u)⁻¹ * (e₂ * v)⁻¹
        = e₁ * u * e₂ * (v * u⁻¹) * e₁⁻¹ * v⁻¹ * e₂⁻¹ := by group
      _ = e₁ * u * e₂ * (u⁻¹ * v) * e₁⁻¹ * v⁻¹ * e₂⁻¹ := by rw [huv]
      _ = e₁ * (u * e₂ * u⁻¹) * (v * e₁⁻¹ * v⁻¹) * e₂⁻¹ := by group
  rw [key]
  exact E.mul_mem (E.mul_mem (E.mul_mem he₁ h1) h2) (E.inv_mem he₂)

theorem commutator_sup_le_ch615 {G₁ G₂ : Subgroup Γ} (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hab : ∀ a ∈ G₂, ∀ b ∈ G₂, a * b = b * a) : ⁅G₁ ⊔ G₂, G₁ ⊔ G₂⁆ ≤ G₁ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute_ch615 hc).mp hx
  obtain ⟨c, hc', d, hd, rfl⟩ := (mem_sup_iff_of_commute_ch615 hc).mp hy
  have h1 : b * c = c * b := (hc c hc' b hb).symm
  have h2 : b * d = d * b := hab b hb d hd
  have h3 : d * a⁻¹ = a⁻¹ * d := by
    have h := hc a ha d hd
    calc d * a⁻¹ = a⁻¹ * (a * d) * a⁻¹ := by group
      _ = a⁻¹ * (d * a) * a⁻¹ := by rw [h]
      _ = a⁻¹ * d := by group
  have key : ⁅a * b, c * d⁆ = a * c * a⁻¹ * c⁻¹ := by
    rw [commutatorElement_def]
    calc a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹
        = a * (b * c) * d * b⁻¹ * a⁻¹ * d⁻¹ * c⁻¹ := by group
      _ = a * c * (b * d) * b⁻¹ * a⁻¹ * d⁻¹ * c⁻¹ := by rw [h1]; group
      _ = a * c * (d * b) * b⁻¹ * a⁻¹ * d⁻¹ * c⁻¹ := by rw [h2]
      _ = a * c * (d * a⁻¹) * d⁻¹ * c⁻¹ := by group
      _ = a * c * (a⁻¹ * d) * d⁻¹ * c⁻¹ := by rw [h3]
      _ = a * c * a⁻¹ * c⁻¹ := by group
  rw [key]
  exact G₁.mul_mem (G₁.mul_mem (G₁.mul_mem ha hc') (G₁.inv_mem ha)) (G₁.inv_mem hc')

theorem commutator_eq_self_ch615 {F : Subgroup Γ} (hs : IsSimpleGroup ↥F)
    (hns : ¬ Group.IsSolvable ↥F) : ⁅F, F⁆ = F := by
  have hc : commutator ↥F = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥F) with h | h
    · exfalso
      apply hns
      have : IsMulCommutative ↥F := (commutator_eq_bot_iff ↥F).mp h
      infer_instance
    · exact h
  exact Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hc)

theorem conj_mem_commutator_ch615 {Gs : Subgroup Γ} {x : Γ}
    (hx : x ∈ Subgroup.normalizer (Gs : Set Γ)) {c : Γ} (hc : c ∈ ⁅Gs, Gs⁆) :
    x * c * x⁻¹ ∈ ⁅Gs, Gs⁆ := by
  have hle : Gs.map (MulAut.conj x).toMonoidHom ≤ Gs := by
    rintro _ ⟨g, hg, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx g).mp hg
  have h : x * c * x⁻¹ ∈ (⁅Gs, Gs⁆).map (MulAut.conj x).toMonoidHom := ⟨c, hc, rfl⟩
  rw [Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono hle hle h

variable [Finite Γ]

theorem mem_normalizer_of_perfect_ch615 {Gs E G₁ : Subgroup Γ} (hG₁ : ⁅G₁, G₁⁆ = G₁)
    (hG₁Gs : G₁ ≤ Gs) (hGs : ⁅Gs, Gs⁆ ≤ E) (hE : ⁅E, E⁆ ≤ G₁) {x : Γ}
    (hx : x ∈ Subgroup.normalizer (Gs : Set Γ)) : x ∈ Subgroup.normalizer (G₁ : Set Γ) := by
  set P := G₁.map (MulAut.conj x).toMonoidHom with hPdef
  have hP : ⁅P, P⁆ = P := by rw [hPdef, ← Subgroup.map_commutator, hG₁]
  have hPGs : P ≤ Gs := by
    rintro _ ⟨g, hg, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx g).mp (hG₁Gs hg)
  have hPE : P ≤ E := by
    rw [← hP]
    exact (Subgroup.commutator_mono hPGs hPGs).trans hGs
  have hPG₁ : P ≤ G₁ := by
    rw [← hP]
    exact (Subgroup.commutator_mono hPE hPE).trans hE
  exact mem_normalizer_of_conj_mem_l32_ch615 fun g hg => hPG₁ ⟨g, hg, rfl⟩

omit [Finite Γ] in
theorem le_commutator_of_outer_ch615 {Gs G₂ : Subgroup Γ} {t : Γ} (htGs : t ∈ Gs)
    (hG₂Gs : G₂ ≤ Gs) (h3 : Nat.card G₂ = 3) (ht : t ∈ Subgroup.normalizer (G₂ : Set Γ))
    (hout : ¬ ∃ g ∈ G₂, ∀ x ∈ G₂, t * x * t⁻¹ = g * x * g⁻¹) : G₂ ≤ ⁅Gs, Gs⁆ := by
  have hx : ∃ x ∈ G₂, t * x * t⁻¹ ≠ x := by
    by_contra h
    exact hout ⟨1, G₂.one_mem, fun x hx => by
      rw [show t * x * t⁻¹ = x from by_contra fun hne => h ⟨x, hx, hne⟩]
      group⟩
  obtain ⟨x, hxG, hxt⟩ := hx
  have hcm : ⁅t, x⁆ ∈ ⁅Gs, Gs⁆ := Subgroup.commutator_mem_commutator htGs (hG₂Gs hxG)
  have hcG : ⁅t, x⁆ ∈ G₂ := by
    rw [commutatorElement_def]
    exact G₂.mul_mem ((Subgroup.mem_normalizer_iff.mp ht x).mp hxG) (G₂.inv_mem hxG)
  have hc1 : ⁅t, x⁆ ≠ 1 := fun h => hxt (by
    rw [commutatorElement_eq_one_iff_mul_comm] at h
    rw [h, mul_inv_cancel_right])
  have : Fact (Nat.card G₂).Prime := ⟨h3 ▸ Nat.prime_three⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((⁅Gs, Gs⁆).subgroupOf G₂) with h | h
  · exfalso
    have h1 : (⟨⁅t, x⁆, hcG⟩ : ↥G₂) ∈ (⁅Gs, Gs⁆).subgroupOf G₂ := hcm
    rw [h, Subgroup.mem_bot] at h1
    exact hc1 (congrArg Subtype.val h1)
  · intro y hy
    have h1 : (⟨y, hy⟩ : ↥G₂) ∈ (⁅Gs, Gs⁆).subgroupOf G₂ := by
      rw [h]
      exact Subgroup.mem_top _
    exact h1

theorem mem_normalizer_of_eq_inf_ch615 {C G₁ G₂ : Subgroup Γ} {x : Γ} (hG₂ : G₂ ≤ C)
    (hC : ∀ y ∈ C, (∀ g ∈ G₁, y * g = g * y) → y ∈ G₂)
    (hG₂c : ∀ y ∈ G₂, ∀ g ∈ G₁, y * g = g * y)
    (hxC : ∀ c ∈ C, x * c * x⁻¹ ∈ C) (hx₁ : x ∈ Subgroup.normalizer (G₁ : Set Γ)) :
    x ∈ Subgroup.normalizer (G₂ : Set Γ) := by
  refine mem_normalizer_of_conj_mem_l32_ch615 fun y hy => hC _ (hxC y (hG₂ hy)) fun g hg => ?_
  have hg' : x⁻¹ * g * x ∈ G₁ := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx₁) g).mp hg
    simpa using this
  have h := hG₂c y hy _ hg'
  calc x * y * x⁻¹ * g = x * (y * (x⁻¹ * g * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * g * x) * y) * x⁻¹ := by rw [h]
    _ = g * (x * y * x⁻¹) := by group

theorem conj_eq_of_odd_of_card_three_ch615 {G₂ : Subgroup Γ} (h3 : Nat.card G₂ = 3) {d : Γ}
    (hd : d ∈ Subgroup.normalizer (G₂ : Set Γ)) (hodd : Odd (orderOf d)) {y : Γ}
    (hy : y ∈ G₂) : d * y * d⁻¹ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic ↥G₂ := isCyclic_of_prime_card h3
  set φ := G₂.normalizerMonoidHom ⟨d, hd⟩ with hφ
  have h1 : orderOf φ ∣ orderOf d := by
    have := orderOf_map_dvd G₂.normalizerMonoidHom ⟨d, hd⟩
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf φ ∣ 2 := by
    have := orderOf_dvd_natCard φ
    rwa [IsCyclic.card_mulAut, h3, Nat.totient_prime Nat.prime_three] at this
  have hφ1 : φ = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.Coprime.eq_one_of_dvd (Odd.of_dvd_nat hodd h1).coprime_two_right h2
  have := congrArg (fun β : MulAut ↥G₂ => ((β ⟨y, hy⟩ : ↥G₂) : Γ)) hφ1
  simpa [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe] using this

omit [Finite Γ] in
theorem commute_of_card_three_ch615 {G₂ : Subgroup Γ} (h3 : Nat.card G₂ = 3) :
    ∀ a ∈ G₂, ∀ b ∈ G₂, a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite ↥G₂ := Nat.finite_of_card_ne_zero (by rw [h3]; norm_num)
  have : IsCyclic ↥G₂ := isCyclic_of_prime_card h3
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥G₂)
  intro a ha b hb
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
  have := (Commute.zpow_zpow_self g i j).eq
  rw [hi, hj] at this
  exact congrArg Subtype.val this

end Case4

theorem commV_mono_ch615 {W : Type*} [CommGroup W] {X Y : Subgroup (MulAut W)} (h : X ≤ Y) :
    commV X ≤ commV Y :=
  Subgroup.closure_mono fun _ ⟨x, hx, v, hv⟩ => ⟨x, h hx, v, hv⟩

theorem fix_of_mem_commV_ch615 {W : Type*} [CommGroup W] {G₁ G₂ : Subgroup (MulAut W)}
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hinf : commV G₁ ⊓ commV G₂ = ⊥)
    {g : MulAut W} (hg : g ∈ G₁) {w : W} (hw : w ∈ commV G₂) : g w = w := by
  have h1 : g w * w⁻¹ ∈ commV G₁ := Subgroup.subset_closure ⟨g, hg, w, rfl⟩
  have h2 : g w * w⁻¹ ∈ commV G₂ :=
    (commV G₂).mul_mem (mem_commV_of_conj_ch615 (fun x hx => by
      rw [hc g hg x hx, mul_inv_cancel_right]; exact hx) hw) ((commV G₂).inv_mem hw)
  have h3 : g w * w⁻¹ ∈ commV G₁ ⊓ commV G₂ := ⟨h1, h2⟩
  rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h3
  exact h3

section Cx

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem val_mem_commutator_ch615 {U : Subgroup G} (hU : IsElemAbelian 2 U) {F : Subgroup G}
    {w : IntMod U hU} (hw : w ∈ commV (autI hU F)) : w.val ∈ ⁅U, F⁆ :=
  CFSG.Quasithin.Vol2.Ch10.SecE.val_mem_commutator_of_mem_commV hU hw

end Cx

namespace Cx615C

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

theorem exists_of_b56Case4_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (h4 : B56Case4 (ffJ (autI hU (borelL T L ⊔ H)))) :
    ∃ z ∈ quasithinOmegaOneCenter T ⊓ ⁅UX615 T L H, borelL T L ⊔ H⁆,
      z ≠ 1 ∧ (∃ d ∈ borelL T L, Odd (orderOf d) ∧ d ≠ 1 ∧ d * z * d⁻¹ = z) ∧
      ¬ (borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G) ≤
        Subgroup.normalizer ((borelL T L : Subgroup G) : Set G) := by
  classical
  obtain ⟨G₁, G₂, t, hGs, -, hcomm, ⟨e₁⟩, h3, -, -, hdir, -, h4c, ht₁, ht₂, -, hout₂⟩ := h4
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hs₁ : IsSimpleGroup ↥G₁ := by
    have := isSimpleGroup_alt_six_ch615
    exact e₁.isSimpleGroup
  have hns₁ : ¬ Group.IsSolvable ↥G₁ := fun h => not_isSolvable_alt_six_ch615 (by
    have := h
    exact Group.isSolvable_of_surjective (f := e₁.toMonoidHom) e₁.surjective)
  have hZ₁ := center_of_isSimpleGroup_ch615 hs₁ hns₁
  have hperf := commutator_eq_self_ch615 hs₁ hns₁
  have hab₂ := commute_of_card_three_ch615 h3
  have hGsX : ffJ (autI hU (borelL T L ⊔ H)) ≤ autI hU (borelL T L ⊔ H) := B6.ffJ_le _
  have hG₁Gs : G₁ ≤ ffJ (autI hU (borelL T L ⊔ H)) := by
    rw [hGs]
    exact le_sup_left.trans le_sup_left
  have hG₂Gs : G₂ ≤ ffJ (autI hU (borelL T L ⊔ H)) := by
    rw [hGs]
    exact le_sup_right.trans le_sup_left
  have htGs : t ∈ ffJ (autI hU (borelL T L ⊔ H)) := by
    rw [hGs]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htE : t ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup _) : Set (MulAut _)) := by
    refine mem_normalizer_of_conj_mem_l32_ch615 fun y hy => ?_
    have hle : (G₁ ⊔ G₂).map (MulAut.conj t).toMonoidHom ≤ G₁ ⊔ G₂ := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨g, hg, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp ht₁ g).mp hg
      · rintro _ ⟨g, hg, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp ht₂ g).mp hg
    exact hle ⟨y, hy, rfl⟩
  have hGsc : ⁅ffJ (autI hU (borelL T L ⊔ H)), ffJ (autI hU (borelL T L ⊔ H))⁆ ≤ G₁ ⊔ G₂ := by
    rw [hGs]
    exact commutator_sup_zpowers_le_ch615 htE
  have hEc := commutator_sup_le_ch615 hcomm hab₂
  have hXN₁ : ∀ x ∈ autI hU (borelL T L ⊔ H), x ∈ Subgroup.normalizer (G₁ : Set (MulAut _)) :=
    fun x hx => mem_normalizer_of_perfect_ch615 hperf hG₁Gs hGsc hEc (B6.le_normalizer_ffJ _ hx)
  have hG₂c := le_commutator_of_outer_ch615 htGs hG₂Gs h3 ht₂ hout₂
  have hXN₂ : ∀ x ∈ autI hU (borelL T L ⊔ H), x ∈ Subgroup.normalizer (G₂ : Set (MulAut _)) :=
    fun x hx => mem_normalizer_of_eq_inf_ch615 hG₂c
      (fun y hy hyc => mem_of_commute_ch615 hcomm hZ₁ (hGsc hy) hyc)
      (fun y hy g hg => (hcomm g hg y hy).symm)
      (fun _ hc => conj_mem_commutator_ch615 (B6.le_normalizer_ffJ _ hx) hc) (hXN₁ x hx)
  have hDsX : autI hU D ≤ autI hU (borelL T L ⊔ H) := autI_mono hU (hD.1.trans le_sup_left)
  have hDsodd : ∀ d ∈ autI hU D, Odd (orderOf d) := by
    have hodd : Odd (Nat.card (autI hU D)) := by
      rw [(c.autI_hall_ch615 hU hD).2, ← (c.hall_ch615 hD).2]
      exact hD.2.1
    exact fun d hd => Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hd)
  have hDs₂ : ∀ d ∈ autI hU D, ∀ y ∈ G₂, d * y * d⁻¹ = y := fun d hd y hy =>
    conj_eq_of_odd_of_card_three_ch615 h3 (hXN₂ d (hDsX hd)) (hDsodd d hd) hy
  by_cases hDc : autI hU D ≤ Subgroup.centralizer (G₁ : Set (MulAut _))
  ·
    exfalso
    apply c.not_hall_normalizes_ch615 hU hD hN
    intro y hy k hk
    have hkE : k ∈ G₁ ⊔ G₂ := hGsc (((c.le_commutator_ch615 hU).trans
      (Subgroup.commutator_mono (c.le_ffJ_ch615 hU).2 (c.le_ffJ_ch615 hU).1)) hk)
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute_ch615 hcomm).mp hkE
    have hya : y * a * y⁻¹ = a := by
      rw [← Subgroup.mem_centralizer_iff.mp (hDc hy) a ha, mul_inv_cancel_right]
    have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [e, hya, hDs₂ y hy b hb]
    exact hk
  have hTsX : autI hU T ≤ autI hU (borelL T L ⊔ H) := autI_mono hU (c.hH.1.1.trans le_sup_right)
  have hG₁X : G₁ ≤ autI hU (borelL T L ⊔ H) := hG₁Gs.trans hGsX
  have hG₁n : (G₁.subgroupOf (autI hU (borelL T L ⊔ H))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hG₁X).mpr fun x hx => hXN₁ x hx
  have hS₁ : IsSylowTwoOf (autI hU T ⊓ G₁) G₁ :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal (c.isSylowTwoOf_autI_ch615 hU) hG₁X
      hG₁n.isSubnormal
  obtain ⟨-, hout, hNS, hself⟩ := dLemmaFacts_alt_six_ch615 e₁
  obtain ⟨d, hdD, hdF, hd1, -⟩ := exists_mem_of_not_le_centralizer_ch615 hout hZ₁
    hS₁.isPGroup hS₁.le (hNS _ hS₁) (hself _ hS₁) (inf_le_left.trans (autI_mono hU le_sup_right))
    (autI_mono hU (hD.1.trans le_sup_left)) (c.isSolvable_autI_ch615 hU)
    (fun x hx => hXN₁ x (hDsX hx)) hDsodd (fun y hy ho => c.mem_autI_borelL_of_odd_ch615 hU hy ho)
    (fun p hp hp2 x hx y hy hxp hyp hxy hx1 =>
      c.mem_zpowers_of_autI_borelL_prime_ch615 hU hp hp2 hx hy hxp hyp hxy hx1) hDc
  have hV₂ : commV G₂ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at h4c
    norm_num at h4c
  obtain ⟨w, hwV, hw1, hwT⟩ := exists_fix_ch615 IntMod.sq_eq_one (c.isPGroup_autI_ch615 hU) hV₂
    fun s hs w hw => mem_commV_of_conj_ch615
      (fun x hx => (Subgroup.mem_normalizer_iff.mp (hXN₂ s (hTsX hs)) x).mp hx) hw
  have hG₁w : ∀ g ∈ G₁, g w = w := fun g hg => fix_of_mem_commV_ch615 hcomm hdir.2 hg hwV
  have hTX : T ≤ borelL T L ⊔ H := c.hH.1.1.trans le_sup_right
  have hUT : UX615 T L H ≤ T :=
    c.U_red_ch615.1.trans (F7.isSylowTwoOf_pCoreOf_le (c.hyp.toHyp5_0_1.isSylowTwoOf hTX))
  set z := w.val with hz
  have hzU : z ∈ UX615 T L H := w.val_mem
  have hfix : ∀ g (hg : g ∈ Subgroup.normalizer (UX615 T L H : Set G)),
      convI hU ⟨g, hg⟩ w = w → g * z * g⁻¹ = z := fun g hg h => by
    have := congrArg IntMod.val h
    rwa [convI_apply_val] at this
  have hzC : z ∈ Subgroup.centralizer (T : Set G) := Subgroup.mem_centralizer_iff.mpr fun s hs => by
    have hsN := hXN (hTX hs)
    have h1 := hfix s hsN (hwT _ (convI_mem_autI hU hs hsN))
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [h1]
  have hz2 : z ^ 2 = 1 := by simpa [pow_two] using hU.2 z hzU
  have hzZ : z ∈ quasithinOmegaOneCenter T :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hUT hzU, hzC, hz2⟩
  have hz1 : z ≠ 1 := fun h => hw1 (IntMod.val_injective (by rw [← hz, h, IntMod.val_one]))
  have hzc : z ∈ ⁅UX615 T L H, borelL T L ⊔ H⁆ :=
    val_mem_commutator_ch615 hU (commV_mono_ch615 (hG₂Gs.trans hGsX) hwV)
  obtain ⟨⟨dG, hdN⟩, hdGD, rfl⟩ := (mem_autI hU).mp hdD
  have hdG1 : dG ≠ 1 := fun h => hd1 (by
    have : (⟨dG, hdN⟩ : ↥(Subgroup.normalizer (UX615 T L H : Set G))) = 1 := Subtype.ext h
    rw [this, map_one])
  have hdGodd : Odd (orderOf dG) := Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard D hdGD)
  refine ⟨z, ⟨hzZ, hzc⟩, hz1, ⟨dG, hD.1 hdGD, hdGodd, hdG1, hfix dG hdN (hG₁w _ hdF)⟩, ?_⟩
  intro hle
  have hsub : G₁ ≤ autI hU ((borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G)) := by
    intro g hg
    obtain ⟨⟨x, hxN⟩, hxX, rfl⟩ := (mem_autI hU).mp (hG₁X hg)
    have hxz := hfix x hxN (hG₁w _ hg)
    have hxc : x ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc x * z = x * z * x⁻¹ * x := by group
          _ = z * x := by rw [hxz])
    exact (mem_autI hU).mpr ⟨⟨x, hxN⟩, ⟨hxX, hxc⟩, rfl⟩
  have hBn := C124.autI_conj_mem hU hle
  have hn : ((autI hU (borelL T L) ⊓ G₁).subgroupOf G₁).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hBn _ (hsub g.2) _ hx.1, G₁.mul_mem (G₁.mul_mem g.2 hx.2) (G₁.inv_mem g.2)⟩⟩
  rcases hn.eq_bot_or_eq_top with hb | ht
  · have hdB : convI hU ⟨dG, hdN⟩ ∈ autI hU (borelL T L) := convI_mem_autI hU (hD.1 hdGD) hdN
    have h1 : (⟨_, hdF⟩ : ↥G₁) ∈ (autI hU (borelL T L) ⊓ G₁).subgroupOf G₁ := ⟨hdB, hdF⟩
    rw [hb, Subgroup.mem_bot] at h1
    exact hd1 (congrArg Subtype.val h1)
  · have hG₁B : G₁ ≤ autI hU (borelL T L ⊔ T) := fun g hg => by
      have h1 : (⟨g, hg⟩ : ↥G₁) ∈ (autI hU (borelL T L) ⊓ G₁).subgroupOf G₁ := by
        rw [ht]
        exact Subgroup.mem_top _
      exact autI_mono hU le_sup_left h1.1
    have := c.isSolvable_autI_ch615 hU
    exact hns₁ (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hG₁B)
      (Subgroup.inclusion_injective _))

end Cx615C

theorem res615EFF_of_case1 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (hB56 : AsB56)
    (hcases : ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ),
      Cx615C G T M L V H n → ∀ hU : IsElemAbelian 2 (UX615 T L H),
      ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) →
      B56Case1 (ffJ (autI hU (borelL T L ⊔ H))) →
      ∃ z ∈ quasithinOmegaOneCenter T ⊓ ⁅UX615 T L H, borelL T L ⊔ H⁆,
        z ≠ 1 ∧ (∃ d ∈ borelL T L, Odd (orderOf d) ∧ d ≠ 1 ∧ d * z * d⁻¹ = z) ∧
        ¬ (borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer ((borelL T L : Subgroup G) : Set G)) :
    Res615EFF :=
  res615EFF_of_cases14 h331 h432 hB56 fun G _ _ T M L V H n c hU hN h => by
    rcases h with h1 | h4
    · exact hcases G T M L V H n c hU hN h1
    · exact c.exists_of_b56Case4_ch615 hU hN h4

end CFSG.Quasithin.H13
