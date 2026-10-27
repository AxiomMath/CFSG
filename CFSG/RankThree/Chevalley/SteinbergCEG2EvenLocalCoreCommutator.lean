module

public import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenQPlusTorus
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenSplitPrime
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenCyclotomicTori
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
open Subgroup
open scoped Pointwise commutatorElement

namespace EvenG2

section Generic

variable {C : Type*} [Group C]

theorem odd_card_of_le_comap_map_conj (hinj : Function.Injective (MulAut.conj : C →* MulAut C))
    {B : Subgroup (MulAut C)} {X : Subgroup C} (hX : Odd (Nat.card X)) {W : Subgroup B}
    (hW : W ≤ (X.map (MulAut.conj : C →* MulAut C)).comap B.subtype) : Odd (Nat.card W) := by
  refine Odd.of_dvd_nat hX ?_
  rw [← Subgroup.card_map_of_injective B.subtype_injective,
    ← Subgroup.card_map_of_injective (K := X) hinj]
  exact Subgroup.card_dvd_of_le (Subgroup.map_le_iff_le_comap.2 hW)

variable [Finite C]

theorem odd_card_commutator_of_alternative
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {p : ℕ} (hp : p.Prime)
    {B : Subgroup (MulAut C)} (hB : (MulAut.conj : C →* MulAut C).range ≤ B)
    (hcomm : ∀ a b : MulAut C, ⁅a, b⁆ ∈ (MulAut.conj : C →* MulAut C).range)
    {E : Subgroup B} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (x : C)
    (hxE : (⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B) ∈ E)
    (halt : Odd (Nat.card (centralizer ({x} : Set C))) ∨
      (CFSG.IsQuasisimple (⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ :
          Subgroup C) ∧
        Odd (Nat.card (centralizer ({x} : Set C) ⊓
          centralizer ((⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ : Subgroup C) :
            Set C) : Subgroup C)))) :
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)), E⁆ : Subgroup B)) := by
  classical
  set b : B := ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ with hb
  set S := inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set B)) with hS
  have hSM : S ≤ centralizer ({b} : Set B) := Subgroup.map_subtype_le _
  have hEM : E ≤ centralizer ({b} : Set B) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (hE e he b hxE)
  have hfixM : ∀ m ∈ centralizer ({b} : Set B), (m : MulAut C) x = x :=
    fun m hm => apply_eq_of_commute_conj hinj
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hm))
  have hgenY : ∀ s ∈ S, ∀ e ∈ E, ∃ c ∈ centralizer ({x} : Set C),
      MulAut.conj c = ((⁅s, e⁆ : B) : MulAut C) := by
    intro s hs e he
    have hct : ⁅s, e⁆ ∈ centralizer ({b} : Set B) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hSM hs) (hEM he)) (inv_mem (hSM hs))) (inv_mem (hEM he))
    obtain ⟨c, hc⟩ : ((⁅s, e⁆ : B) : MulAut C) ∈ (MulAut.conj : C →* MulAut C).range := by
      rw [show ((⁅s, e⁆ : B) : MulAut C) = ⁅(s : MulAut C), (e : MulAut C)⁆ from
        map_commutatorElement B.subtype s e]
      exact hcomm _ _
    refine ⟨c, Subgroup.mem_centralizer_singleton_iff.2 (hinj ?_), hc⟩
    have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hct)
    simp only [Subgroup.coe_mul] at h1
    rw [map_mul, map_mul, hc]
    exact h1
  rcases halt with hodd | ⟨hRq, hodd⟩
  · refine odd_card_of_le_comap_map_conj hinj hodd ?_
    rw [Subgroup.commutator_le]
    intro s hs e he
    obtain ⟨c, hc, hce⟩ := hgenY s hs e he
    exact ⟨c, hc, hce⟩
  ·
    have hRY : (⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ : Subgroup C) ≤
        centralizer ({x} : Set C) :=
      Subgroup.commutator_le.2 fun u hu v hv => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)
    have hfixR := aschbacherSolvableCore_fixes_quasisimple hinj hp hB x hRY
      (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hRq
    refine odd_card_of_le_comap_map_conj hinj hodd ?_
    rw [Subgroup.commutator_le]
    intro s hs e he
    obtain ⟨c, hc, hce⟩ := hgenY s hs e he
    refine ⟨c, Subgroup.mem_inf.2 ⟨hc, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩, hce⟩
    have he' : ((e : B) : MulAut C)⁻¹ x = x := by
      nth_rewrite 1 [← hfixM e (hEM he)]
      exact MulAut.inv_apply_self _ _ _
    have h1 : (MulAut.conj c) r = r := by
      rw [hce, show ((⁅s, e⁆ : B) : MulAut C) = ⁅(s : MulAut C), (e : MulAut C)⁆ from
        map_commutatorElement B.subtype s e]
      exact commutatorElement_apply_of_fixed (hfixR s hs r hr)
        (hfixR s hs _ (apply_mem_commutator_centralizer_of_apply_eq he' hr))
    rw [MulAut.conj_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm

end Generic

theorem even_G2_commutator_mem_range_conj {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (a b : MulAut (adjointGroup .G2 K)) :
    ⁅a, b⁆ ∈ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range := by
  obtain ⟨-, Θ, -, -, hΘker, -⟩ := even_G2_exact_automorphism_normal_form hf K hK
  obtain ⟨φ₀, -, -, hφgen, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ₀, hφgen⟩
  rw [← hΘker, MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact IsMulCommutative.is_comm.comm _ _

theorem dvd_cases_of_dvd_ordG2 {q p : ℕ} (hq : 1 ≤ q) (hp : p.Prime)
    (h : p ∣ CFSG.Open.ordG2 q) (hpq : ¬ p ∣ q) :
    p ∣ q - 1 ∨ p ∣ q + 1 ∨ p ∣ q ^ 2 + q + 1 ∨ p ∣ q ^ 2 - q + 1 := by
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have h6 : q ^ 6 - 1 = (q - 1) * (q + 1) * (q ^ 2 + q + 1) * (q ^ 2 - q + 1) := by
    have : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
    zify [hq, hq2, this]
    ring
  have h2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    zify [hq, this]
    ring
  rw [CFSG.Open.ordG2, h6, h2] at h
  rcases hp.dvd_mul.1 h with h | h
  · rcases hp.dvd_mul.1 h with h | h
    · exact absurd (hp.dvd_of_dvd_pow h) hpq
    · rcases hp.dvd_mul.1 h with h | h
      · rcases hp.dvd_mul.1 h with h | h
        · rcases hp.dvd_mul.1 h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · rcases hp.dvd_mul.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem centralizer_alternative_split_of_charTwo {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K - 1) {x : adjointGroup .G2 K} (hx : orderOf x = p) :
    Odd (Nat.card (centralizer ({x} : Set (adjointGroup .G2 K)))) ∨
      (CFSG.IsQuasisimple (⁅centralizer ({x} : Set (adjointGroup .G2 K)),
          centralizer ({x} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ∧
        Odd (Nat.card (centralizer ({x} : Set (adjointGroup .G2 K)) ⊓
          centralizer ((⁅centralizer ({x} : Set (adjointGroup .G2 K)),
            centralizer ({x} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) :
              Set (adjointGroup .G2 K)) : Subgroup (adjointGroup .G2 K)))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq6 := six_le_card_of_dvd hp hp3 hpq
  have hPx : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨g, hg⟩ :=
    exists_conj_map_le_of_not_dvd_index (not_dvd_index_torusGroup_G2 hp hp3 hpq) hPx
  have hgx : g * x * g⁻¹ ∈ (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K) :=
    hg ⟨x, Subgroup.mem_zpowers x, rfl⟩
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgx
  have hao : orderOf (rootDiagUnit .G2 a) = p := by
    rw [← ha, orderOf_injective _ (adjointGroup .G2 K).subtype_injective,
      show g * x * g⁻¹ = (MulAut.conj g).toMonoidHom x from rfl,
      orderOf_injective _ (MulAut.conj g).injective x, hx]
  rcases toral_centralizer_cases_G2_of_charTwo K hp hp3 hpq a hao with ⟨-, hMH⟩ |
    ⟨α, hα, -, -, -, hcomm, hZ, hZH⟩
  · obtain ⟨φ, hφ⟩ := exists_injective_of_toralCentralizer_eq_torusGroup ha hMH
    exact Or.inl (odd_card_of_injective_pi_units φ hφ)
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfin⟩ :=
      even_Chevalley_pinned_root_SL2_maps .G2 K hα
    obtain ⟨hsimple, -, hnonab⟩ := hfin inferInstance (by omega)
    have := hsimple
    have hQq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1
    obtain ⟨-, hRq, φ, hφ⟩ := derived_centralizer_data ha hcomm hQq hZ hZH
    exact Or.inr ⟨hRq, odd_card_of_injective_pi_units φ hφ⟩

theorem centralizer_alternative_qplus_of_charTwo {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K + 1) (K₂ : Type) [Field K₂] [Algebra K K₂]
    (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K)
    {x : adjointGroup .G2 K} (hx : orderOf x = p) :
    Odd (Nat.card (centralizer ({x} : Set (adjointGroup .G2 K)))) ∨
      (CFSG.IsQuasisimple (⁅centralizer ({x} : Set (adjointGroup .G2 K)),
          centralizer ({x} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ∧
        Odd (Nat.card (centralizer ({x} : Set (adjointGroup .G2 K)) ⊓
          centralizer ((⁅centralizer ({x} : Set (adjointGroup .G2 K)),
            centralizer ({x} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) :
              Set (adjointGroup .G2 K)) : Subgroup (adjointGroup .G2 K)))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, z, -, -, -, -, -, -, -, -, ⟨S₀, hS₀T⟩, -, hroot, hTuniq, hcases⟩ :=
    even_G2_qplus_torus_and_fixed_root_centralizers K hp hp3 hpq K₂ hdeg σ hσ
  have : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  have : Finite K₂ := Module.finite_of_finite K
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  set ψ : ModGL .G2 K →* ModGL .G2 K₂ :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K K₂)) with hψ
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .G2) (algebraMap K K₂))
  let ε : adjointGroup .G2 K ≃* conjEntrywiseImage K g :=
    (adjointGroup .G2 K).equivMapOfInjective ψ hψinj
  have hPx : IsPGroup p (Subgroup.zpowers (ε x)) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, MulEquiv.orderOf_eq ε x, hx, pow_one])
  obtain ⟨Q', hQ'⟩ := hPx.exists_le_sylow
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq (conjEntrywiseImage K g) Q' S₀
  have hux : MulAut.conj u • ε x ∈ (S₀ : Subgroup (conjEntrywiseImage K g)) := by
    have h1 : MulAut.conj u • ε x ∈ MulAut.conj u • (Q' : Subgroup (conjEntrywiseImage K g)) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hQ' (Subgroup.mem_zpowers _))
    rwa [← Sylow.coe_subgroup_smul, hu] at h1
  set F : adjointGroup .G2 K →* ModGL .G2 K₂ := (conjEntrywiseImage K g).subtype.comp
    ((MulAut.conj u).toMonoidHom.comp ε.toMonoidHom) with hFdef
  have hF : Function.Injective F := (conjEntrywiseImage K g).subtype_injective.comp
    ((MulAut.conj u).injective.comp ε.injective)
  have hFT : F x ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g :=
    Subgroup.mem_subgroupOf.1 (hS₀T hux)
  obtain ⟨a, ha, -⟩ := hTuniq _ hFT
  have hFrange : F.range = conjEntrywiseImage K g := by
    rw [hFdef, MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _
      ((MulAut.conj u).surjective.comp ε.surjective), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hmapF : (centralizer ({x} : Set (adjointGroup .G2 K))).map F =
      conjEntrywiseImage K g ⊓ centralizer {rootDiagUnit .G2 a} := by
    rw [SteinbergBN.map_centralizer_singleton_of_injective F hF x, hFrange, ← ha]
  have hTa : rootDiagUnit .G2 a ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g := ha ▸ hFT
  have hao : orderOf (rootDiagUnit .G2 a) = p := by
    rw [ha, orderOf_injective F hF x, hx]
  by_cases hkerE : rootCharKernel a = ∅
  ·
    obtain ⟨φ, hφ⟩ := SteinbergBN.exists_injective_of_map_le_torusGroup F hF
      (X := centralizer ({x} : Set (adjointGroup .G2 K))) (by
        rw [hmapF, (hcases a hTa hao).1 hkerE]
        exact inf_le_left)
    exact Or.inl (odd_card_of_injective_pi_units φ hφ)
  ·
    obtain ⟨α, hα, -, hcomm, hZ, hZH⟩ := (hcases a hTa hao).2.1 hkerE
    obtain ⟨_, -, hsimple, -, hnonab⟩ := hroot α hα
    have := hsimple
    have hQq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1
    obtain ⟨-, hRq, φ, hφ⟩ :=
      SteinbergBN.derived_centralizer_data_of_map F hF hmapF hcomm hQq hZ hZH
    exact Or.inr ⟨hRq, odd_card_of_injective_pi_units φ hφ⟩

theorem odd_card_centralizer_cyclotomic_of_charTwo {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {ε : ℤ} (hε : ε = -1 ∨ ε = 1) {d : ℕ}
    (hd : (d : ℤ) = (Nat.card K : ℤ) ^ 2 + ε * Nat.card K + 1) (hpd : p ∣ d)
    {x : adjointGroup .G2 K} (hx : orderOf x = p) :
    Odd (Nat.card (centralizer ({x} : Set (adjointGroup .G2 K)))) := by
  obtain ⟨T, -, -, -, -, hcent⟩ :=
    even_G2_cyclotomic_three_six_tori_and_prime_centralizers K ε hε d hd hp hp3 hpd
  obtain ⟨-, -, -, hcard, hodd⟩ := hcent x hx
  rw [hcard]
  exact hodd

end EvenG2

open EvenG2

theorem even_G2_odd_card_commutator_inner {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (B : Subgroup (MulAut (adjointGroup .G2 K)))
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (t : B) (htE : t ∈ E) (ht1 : t ≠ 1)
    (htinn : (t : MulAut (adjointGroup .G2 K)) ∈
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) :
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)), E⁆ :
      Subgroup B)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hE
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) ⟨a, ha⟩
    simpa using congrArg Subtype.val h
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  obtain ⟨x, hx⟩ := htinn
  have htx : t = ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
  subst htx
  have htp : orderOf (⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B) = p :=
    orderOf_eq_prime (hEpow _ htE) ht1
  have hxp : orderOf x = p := by
    rw [← orderOf_injective _ hinj x, ← htp, Subgroup.orderOf_mk]
  refine odd_card_commutator_of_alternative hinj hp hB (even_G2_commutator_mem_range_conj hf hK)
    hEcomm x htE ?_
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq2 : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
  have hpC : p ∣ CFSG.Open.ordG2 (Nat.card K) := by
    rw [← card_adjointGroup_G2, ← hxp]
    exact orderOf_dvd_natCard x
  have hp2 : ¬ p ∣ Nat.card K := fun h => by
    rw [hK] at h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  rcases dvd_cases_of_dvd_ordG2 hq1 hp hpC hp2 with h | h | h | h
  · exact centralizer_alternative_split_of_charTwo hp hp3 h hxp
  · exact centralizer_alternative_qplus_of_charTwo hp hp3 h (FiniteField.Extension K 2 2)
      (FiniteField.finrank_extension K 2 2) (FiniteField.Extension.frob K 2 2).toRingEquiv
      (fun c => FiniteField.Extension.frob_apply K 2 2 (x := c)) hxp
  · exact Or.inl (odd_card_centralizer_cyclotomic_of_charTwo hp hp3 (Or.inr rfl)
      (d := Nat.card K ^ 2 + Nat.card K + 1) (by push_cast; ring) h hxp)
  · exact Or.inl (odd_card_centralizer_cyclotomic_of_charTwo hp hp3 (Or.inl rfl)
      (d := Nat.card K ^ 2 - Nat.card K + 1) (by push_cast [Nat.cast_sub hq2]; ring) h hxp)

end CFSG.RankThree.Chevalley
