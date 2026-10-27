module

import CFSG.Quasithin.MS93.S33SL
import CFSG.Quasithin.MS93.S33SpCoord
public import CFSG.Quasithin.MS93.S34RLin

public section

namespace CFSG.Quasithin.MS93.S34F

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section Field

variable {F : Type} [Field F] [Fintype F]

theorem ringHom_eq_id_of_iterate {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : Odd n)
    {σ : F →+* F} {e : ℕ} (hσ : ∀ x, σ^[2 ^ e] x = x) (x : F) : σ x = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hbij : Function.Bijective σ :=
    ⟨σ.injective, Finite.injective_iff_surjective.mp σ.injective⟩
  have hmap : ∀ y : ZMod 2, σ (algebraMap (ZMod 2) F y) = algebraMap (ZMod 2) F y := fun y =>
    congrArg (fun f : ZMod 2 →+* F => f y)
      (Subsingleton.elim (σ.comp (algebraMap (ZMod 2) F)) (algebraMap (ZMod 2) F))
  let σ' : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective σ hbij) hmap
  have hσ'x : ∀ y, σ' y = σ y := fun _ => rfl
  have hit : ∀ (m : ℕ) (y : F), (σ' ^ m) y = σ^[m] y := by
    intro m
    induction m with
    | zero => intro y; rfl
    | succ m ih =>
      intro y
      rw [pow_succ, AlgEquiv.mul_apply, ih, hσ'x, Function.iterate_succ_apply]
  have hpow : σ' ^ (2 ^ e) = 1 := by
    ext y
    rw [hit, hσ]
    rfl
  have hfin : Module.finrank (ZMod 2) F = n := by
    have h1 := FiniteField.pow_finrank_eq_card 2 F
    rw [hcard] at h1
    exact Nat.pow_right_injective le_rfl h1
  have hcardG : Nat.card (F ≃ₐ[ZMod 2] F) = n := by
    rw [IsGalois.card_aut_eq_finrank, hfin]
  have h1 : orderOf σ' ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hpow
  have h2 : orderOf σ' ∣ n := hcardG ▸ orderOf_dvd_natCard σ'
  have hcop : Nat.Coprime (2 ^ e) n := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hn)
  have h3 : orderOf σ' = 1 := Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  rw [← hσ'x, orderOf_eq_one_iff.mp h3]
  rfl

omit [Fintype F] in
theorem iterate_smul {ι : Type} {f : (ι → F) → (ι → F)} {σ : F →+* F}
    (hσ : ∀ (c : F) (x : ι → F), f (c • x) = σ c • f x) (m : ℕ) (c : F) (x : ι → F) :
    f^[m] (c • x) = σ^[m] c • f^[m] x := by
  induction m generalizing c x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      hσ, ih]

theorem linear_of_iterate {ι : Type} [Nonempty ι] [DecidableEq ι] {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hn : Odd n) {f : (ι → F) → (ι → F)} {σ : F →+* F}
    (hσ : ∀ (c : F) (x : ι → F), f (c • x) = σ c • f x) {e : ℕ}
    (hit : ∀ x, f^[2 ^ e] x = x) : ∀ (c : F) (x : ι → F), f (c • x) = c • f x := by
  have hσit : ∀ c, σ^[2 ^ e] c = c := by
    intro c
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h1 := iterate_smul hσ (2 ^ e) c (Pi.single i 1)
    simp only [hit] at h1
    have h2 := congrFun h1 i
    simpa using h2.symm
  intro c x
  rw [hσ, ringHom_eq_id_of_iterate hcard hn hσit c]

end Field

section Linear

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem le_linPart_of_odd_sl (h : PUHyp M T L) {F : Type} [Field F] [Fintype F]
    {a : ↥L →* ↥(StatedSL 3 F)} {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 3 → F)}
    {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : Odd n) (ha : Function.Surjective a)
    (hβ : Function.Surjective β) (hβker : β.ker = (⊥ : Subgroup G).subgroupOf (Uq M T L))
    (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (a l : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i)) :
    T ≤ S34R.linPart h β := by
  intro y hyT
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  have hyV := hTV hyT
  obtain ⟨f, hf⟩ := S33.exists_isCoordAct' hβ hβker hyV
  obtain ⟨σ, hσ⟩ := S33.exists_semilinear_of_mem h ha hβ hβker hβα (h.le hyT) hf
  obtain ⟨e, he⟩ := h.isPGroup ⟨y, hyT⟩
  have he' : y ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  have hit : ∀ x, (⇑f)^[2 ^ e] x = x := S33.iterate_eq_of_pow_eq_one hβ hyV hf he'
  have hlin := linear_of_iterate hcard hn hσ hit
  have hbot : y ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  obtain ⟨γ, hγ⟩ := S34R.exists_gl_of_linear hβ hβker hyV hbot hf hlin
  exact ⟨hyT, ⟨γ, Subgroup.mem_top γ⟩, hγ⟩

theorem le_linPart_of_odd_sp (h : PUHyp M T L) {F : Type} [Field F] [Fintype F]
    {a : ↥L →* ↥(StatedSp 2 F)}
    {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 2 ⊕ Fin 2 → F)}
    {k : ℕ} (hcard : Fintype.card F = 2 ^ k) (hk : Odd k) (ha : Function.Surjective a)
    (hβ : Function.Surjective β)
    (hβker : β.ker = (Uq M T L ⊓ Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L))
    (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (a l : GL (Fin 2 ⊕ Fin 2) F)).mulVec (Multiplicative.toAdd (β u) i)) :
    T ≤ S34R.linPart h β := by
  intro y hyT
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  have hTZ : T ≤ Subgroup.normalizer
      ((Uq M T L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    h.le.trans (le_normalizer_inf (le_normalizer_Uq h.le_normalizer)
      (le_normalizer_centralizer h.le_normalizer))
  have hyV := hTV hyT
  obtain ⟨f, hf⟩ := exists_isCoordAct hβ hβker hyV (hTZ hyT)
  obtain ⟨f', hf'⟩ := exists_isCoordAct hβ hβker (inv_mem hyV) (hTZ (inv_mem hyT))
  obtain ⟨σ, hσ⟩ := S33.exists_semilinear_sp ha
    (h.L_le.trans (le_normalizer_Uq h.le_normalizer)) hβ (S33.isCoordAct_of_natSp hβα) hyV
    (h.le_normalizer (h.le hyT)) hf hf'
  obtain ⟨e, he⟩ := h.isPGroup ⟨y, hyT⟩
  have he' : y ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  have hit : ∀ x, (⇑f)^[2 ^ e] x = x := by
    intro x
    have h1 := S33.isCoordAct_iterate' hyV hf (2 ^ e)
    rw [he'] at h1
    exact congrFun (IsCoordAct.unique hβ (one_mem _) h1 isCoordAct_one) x
  have hlin := linear_of_iterate hcard hk hσ hit
  obtain ⟨γ, hγ⟩ := S34R.exists_gl_of_linear hβ hβker hyV (hTZ hyT) hf hlin
  exact ⟨hyT, ⟨γ, Subgroup.mem_top γ⟩, hγ⟩

end Linear

section Even

variable {G : Type} [Group G]

@[expose] def IsSL3UEven (M T L : Subgroup G) : Prop :=
  Xq M = Zq M L ⊔ Uq M T L ∧ Zq M L ⊓ Uq M T L = ⊥ ∧
    ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 4 ^ m ∧ Function.Surjective α ∧
        IsSumOfNaturalModulesVia L (Uq M T L) ⊥ α false 1

@[expose] def IsSp4UEven (M T L : Subgroup G) : Prop :=
  ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSp 2 F)),
    1 ≤ m ∧ Fintype.card F = 4 ^ m ∧ Function.Surjective α ∧
    IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α false 1

variable {M T L : Subgroup G}

theorem four_pow_eq (m : ℕ) : (4 : ℕ) ^ m = 2 ^ (2 * m) := by
  rw [pow_mul]
  norm_num

theorem IsSL3UEven.isSL3U (hU : IsSL3UEven M T L) : IsSL3U M T L := by
  obtain ⟨hX, hZU, m, F, _, _, α, hcard, hα, hnat⟩ := hU
  exact ⟨hX, hZU, 2 * m, F, inferInstance, inferInstance, α, by rw [hcard, four_pow_eq], hα,
    hnat⟩

theorem IsSp4UEven.isSp4U (hU : IsSp4UEven M T L) : IsSp4U M T L := by
  obtain ⟨m, F, _, _, α, hm, hcard, hα, hnat⟩ := hU
  exact Or.inl ⟨2 * m, F, inferInstance, inferInstance, α, by omega,
    by rw [hcard, four_pow_eq], hα, hnat⟩

variable [Finite G]

theorem isSL3UEven_of_nonfull (h : PUHyp M T L) (hU : IsSL3U M T L) (hF : ¬ IsSL3Full M T L) :
    IsSL3UEven M T L := by
  obtain ⟨hX, hZU, n, F, _, _, a, hcard, ha, hnat⟩ := hU
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hn
  · refine ⟨hX, hZU, m, F, inferInstance, inferInstance, a, ?_, ha, hnat⟩
    rw [hcard, four_pow_eq, two_mul]
  · obtain ⟨-, -, β, hβ, hβker, hβα⟩ := hnat
    exact (hF (S34R.sl3Full_of_le_linPart h hcard ha hX hZU hβ hβker hβα
      (le_linPart_of_odd_sl h hcard hn ha hβ hβker hβα))).elim

theorem isSp4UEven_of_nonfull (h : PUHyp M T L) (hU : IsSp4U M T L) (hF : ¬ IsSp4Full M T L) :
    IsSp4UEven M T L := by
  rcases hU with ⟨k, F, _, _, a, hk, hcard, ha, hnat⟩ | ⟨a, ha, hnat⟩
  · rcases Nat.even_or_odd k with ⟨m, rfl⟩ | hko
    · refine ⟨m, F, inferInstance, inferInstance, a, by omega, ?_, ha, hnat⟩
      rw [hcard, four_pow_eq, two_mul]
    · obtain ⟨hLV, hZV, β, hβ, hβker, hβα⟩ := hnat
      exact (hF (S34R.sp4Full_of_le_linPart h hk hcard ha hLV hZV hβ hβker hβα
        (le_linPart_of_odd_sp h hcard hko ha hβ hβker hβα))).elim
  · exact (hF ⟨1, ZMod 2, inferInstance, inferInstance, a, le_rfl, by simp, ha, hnat⟩).elim

end Even

end CFSG.Quasithin.MS93.S34F
