module

public import CFSG.Quasithin.MS93.S33SpCoord
public import CFSG.Quasithin.MS93.S33F2
public import CFSG.Quasithin.MS93.S33Faith

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G]

section Count

variable {V Z : Subgroup G} {ι : Type} {F : Type} [Field F]
  {β : ↥V →* Multiplicative (Fin 1 → ι → F)}

theorem card_le_card_inf_mul [Finite G] [Finite ι] [Finite F] (hβker : β.ker = Z.subgroupOf V)
    {K : Subgroup G}
    (hK : K ≤ V) (P : AddSubgroup (ι → F))
    (hKP : ∀ u : ↥V, (u : G) ∈ K → Multiplicative.toAdd (β u) 0 ∈ P) :
    Nat.card K ≤ Nat.card ↥(V ⊓ Z) * Nat.card P := by
  let φ : ↥K →* Multiplicative (ι → F) :=
    { toFun := fun k => Multiplicative.ofAdd (Multiplicative.toAdd (β ⟨k, hK k.2⟩) 0)
      map_one' := by
        rw [show (⟨((1 : ↥K) : G), hK (1 : ↥K).2⟩ : ↥V) = 1 from rfl, map_one]
        rfl
      map_mul' := fun x y => by
        have : (⟨((x * y : ↥K) : G), hK (x * y).2⟩ : ↥V) = ⟨x, hK x.2⟩ * ⟨y, hK y.2⟩ := rfl
        rw [this, map_mul, toAdd_mul, Pi.add_apply, ofAdd_add] }
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at h1
  have hker : Nat.card φ.ker ≤ Nat.card ↥(V ⊓ Z) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : ↥K) : G), hK k.1.2, ?_⟩) ?_
    · have hk := k.2
      rw [MonoidHom.mem_ker] at hk
      have h0 : Multiplicative.toAdd (β ⟨k, hK k.1.2⟩) 0 = 0 := by
        simpa [φ] using congrArg Multiplicative.toAdd hk
      have hβ1 : β ⟨k, hK k.1.2⟩ = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        rw [Subsingleton.elim i 0, h0]
        rfl
      have : (⟨k, hK k.1.2⟩ : ↥V) ∈ β.ker := hβ1
      rw [hβker, Subgroup.mem_subgroupOf] at this
      exact this
    · intro a b hab
      have := congrArg (fun x : ↥(V ⊓ Z) => (x : G)) hab
      exact Subtype.ext (Subtype.ext this)
  have hrange : Nat.card φ.range ≤ Nat.card P := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨Multiplicative.toAdd (x : Multiplicative (ι → F)), ?_⟩) ?_
    · obtain ⟨_, ⟨k, rfl⟩⟩ := x
      exact hKP ⟨k, hK k.2⟩ k.2
    · intro a b hab
      have := congrArg (fun x : ↥P => (x : ι → F)) hab
      exact Subtype.ext (Multiplicative.toAdd.injective this)
  rw [← h1]
  exact Nat.mul_le_mul hker hrange

theorem card_eq_card_inf_mul [Finite G] (hβ : Function.Surjective β)
    (hβker : β.ker = Z.subgroupOf V) :
    Nat.card ↥V = Nat.card ↥(V ⊓ Z) * Nat.card (ι → F) := by
  have h1 := Subgroup.card_mul_index β.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hβ, Subgroup.card_top, hβker] at h1
  have h2 : Nat.card ↥(Z.subgroupOf V) = Nat.card ↥(V ⊓ Z) := by
    rw [← Subgroup.inf_subgroupOf_left, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← h1, h2]
  exact congrArg _ (Nat.card_congr (Multiplicative.toAdd.trans (Equiv.funUnique (Fin 1) (ι → F))))

end Count

section Linear

variable {F : Type} [Field F] [Fintype F]

theorem card_fix_mul_le_of_linear_v4 {f : MSP.V4 F →+ MSP.V4 F}
    (hlin : ∀ (c : F) (x : MSP.V4 F), f (c • x) = c • f x) (hne : ∃ x, f x ≠ x) :
    Nat.card (KGNat.fixAdd f) * Fintype.card F ≤ Fintype.card F ^ 4 := by
  let fl : MSP.V4 F →ₗ[F] MSP.V4 F :=
    { toFun := f, map_add' := map_add f, map_smul' := hlin }
  set K := LinearMap.ker (fl - LinearMap.id) with hK
  have hKfix : ∀ x, x ∈ K ↔ x ∈ KGNat.fixAdd f := by
    intro x
    rw [hK, LinearMap.mem_ker, KGNat.mem_fixAdd, LinearMap.sub_apply, sub_eq_zero]
    rfl
  have hcard : Nat.card (KGNat.fixAdd f) = Nat.card K := by
    apply Nat.card_congr
    exact { toFun := fun x => ⟨x, (hKfix x).2 x.2⟩, invFun := fun x => ⟨x, (hKfix x).1 x.2⟩,
            left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hKne : K ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx⟩ := hne
    have : x ∈ K := htop ▸ Submodule.mem_top
    exact hx ((hKfix x).1 this)
  have hdim : Module.finrank F K ≤ 3 := by
    have h3 := Submodule.finrank_lt (s := K) hKne
    have h4 : Module.finrank F (MSP.V4 F) = 4 := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp
    omega
  rw [hcard, Module.natCard_eq_pow_finrank (K := F) (V := ↥K), Nat.card_eq_fintype_card]
  calc Fintype.card F ^ Module.finrank F K * Fintype.card F
      ≤ Fintype.card F ^ 3 * Fintype.card F :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hdim)
    _ = Fintype.card F ^ 4 := by ring

omit [Field F] in
theorem card_v4 : Nat.card (MSP.V4 F) = Fintype.card F ^ 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  simp

theorem four_le_index_v4 {f : MSP.V4 F →+ MSP.V4 F} {σ : F →+* F}
    (hσ : ∀ (c : F) (x : MSP.V4 F), f (c • x) = σ c • f x) (hF : 4 ≤ Fintype.card F)
    (hne : ∃ x, f x ≠ x) : Nat.card (KGNat.fixAdd f) * 4 ≤ Fintype.card F ^ 4 := by
  by_cases hlin : ∀ c : F, σ c = c
  · have hl : ∀ (c : F) (x : MSP.V4 F), f (c • x) = c • f x := fun c x => by rw [hσ, hlin]
    have := card_fix_mul_le_of_linear_v4 hl hne
    calc Nat.card (KGNat.fixAdd f) * 4 ≤ Nat.card (KGNat.fixAdd f) * Fintype.card F :=
          Nat.mul_le_mul_left _ hF
      _ ≤ _ := this
  · push Not at hlin
    have hsq := MSP.card_fixAdd_sq_le hσ hlin
    rw [card_v4] at hsq
    set q := Fintype.card F
    set C := Nat.card (KGNat.fixAdd f)
    have hq2 : 4 ≤ q ^ 2 := by
      calc 4 ≤ 2 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hC : C ≤ q ^ 2 := by
      by_contra hlt
      push Not at hlt
      have : (q ^ 2) ^ 2 < C ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
      have e : (q ^ 2) ^ 2 = q ^ 4 := by ring
      omega
    calc C * 4 ≤ q ^ 2 * q ^ 2 := Nat.mul_le_mul hC hq2
      _ = q ^ 4 := by ring

end Linear

section SpM

variable [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {α : ↥L →* ↥(StatedSp 2 F)} {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 2 ⊕ Fin 2 → F)}

theorem le_normalizer_Uq_inf_Zq (h : PUHyp M T L) :
    M ≤ Subgroup.normalizer ((Uq M T L ⊓ Zq M L : Subgroup G) : Set G) :=
  le_normalizer_inf (le_normalizer_Uq h.le_normalizer) (le_normalizer_Zq h.le_normalizer)

omit [Fintype F] in
theorem exists_isCoordAct_sp (h : PUHyp M T L) (hβ : Function.Surjective β)
    (hβker : β.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L)) {m : G} (hm : m ∈ M) :
    ∃ f : MSP.V4 F →+ MSP.V4 F, IsCoordAct β m f :=
  exists_isCoordAct hβ hβker (le_normalizer_Uq h.le_normalizer hm) (le_normalizer_Uq_inf_Zq h hm)

omit [Fintype F] in
theorem mem_actTriv_of_fix (h : PUHyp M T L)
    (hβker : β.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L)) {m : G} (hm : m ∈ M)
    {f : MSP.V4 F → MSP.V4 F} (hf : IsCoordAct β m f) (hid : ∀ x, f x = x) :
    m ∈ actTriv h := by
  refine ⟨hm, fun u hu => ?_⟩
  have hv := conj_mem_of_mem_normalizer (le_normalizer_Uq (T := T) h.le_normalizer hm) ⟨u, hu⟩
  have he := hf ⟨u, hu⟩ ⟨_, hv⟩ rfl
  rw [hid] at he
  have hc := mul_inv_mem_of_coord_eq hβker he
  simp only at hc
  have hcomm := isMulCommutative_subgroup_iff.mp h.isElemAbelian_Uq.1
  have e : ⁅u, m⁆ = u * ((m * u * m⁻¹)⁻¹ * u) * u⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e, hcomm _ hu _ hc.1, mul_inv_cancel_right]
  exact hc.2.2

variable (h : PUHyp M T L) (hα : Function.Surjective α) (hβ : Function.Surjective β)
  (hβker : β.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L))
  (hβα : ∀ l : ↥L, IsCoordAct β l (MSP.mat (α l)).mulVec)
include h hα hβ hβker hβα

theorem four_le_relIndex_centralizer_sp (hF : 4 ≤ Fintype.card F) {m : G} (hm : m ∈ M)
    (hnt : ¬ Uq M T L ≤ Subgroup.centralizer ({m} : Set G)) :
    4 ≤ (Subgroup.centralizer ({m} : Set G)).relIndex (Uq M T L) := by
  have hmV := le_normalizer_Uq (T := T) h.le_normalizer hm
  have hmL := h.le_normalizer hm
  have hLV : L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.L_le.trans (le_normalizer_Uq h.le_normalizer)
  obtain ⟨f, hf⟩ := exists_isCoordAct_sp h hβ hβker hm
  obtain ⟨f', hf'⟩ := exists_isCoordAct_sp h hβ hβker (inv_mem hm)
  obtain ⟨σ, hσ⟩ := exists_semilinear_sp hα hLV hβ hβα hmV hmL hf hf'
  have hne : ∃ x, f x ≠ x := by
    by_contra hall
    push Not at hall
    apply hnt
    have hc := centralizer_of_actTriv h (mem_actTriv_of_fix h hβker hm hf hall)
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (Subgroup.mem_centralizer_iff.mp hc u hu).symm
  have h4 := four_le_index_v4 hσ hF hne
  have hfix : Nat.card ↥(Subgroup.centralizer ({m} : Set G) ⊓ Uq M T L) ≤
      Nat.card ↥(Uq M T L ⊓ (Uq M T L ⊓ Zq M L)) * Nat.card (KGNat.fixAdd f) := by
    refine card_le_card_inf_mul hβker inf_le_right _ fun u hu => ?_
    rw [KGNat.mem_fixAdd]
    have hc : (u : G) = m * u * m⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp hu.1 m rfl
      rw [this, mul_inv_cancel_right]
    exact (hf u u hc).symm
  have hU := card_eq_card_inf_mul hβ hβker
  rw [card_v4] at hU
  have hmul := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({m} : Set G))
    (K := Uq M T L)
  set r := (Subgroup.centralizer ({m} : Set G)).relIndex (Uq M T L)
  set c := Nat.card ↥(Uq M T L ⊓ (Uq M T L ⊓ Zq M L))
  set x := Nat.card (KGNat.fixAdd f)
  have hc0 : 0 < c := Nat.card_pos
  have hx0 : 0 < x := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have h1 : c * Fintype.card F ^ 4 ≤ r * (c * x) := by
    rw [← hU, ← hmul]
    exact Nat.mul_le_mul_left _ hfix
  have h2 : r * (c * x) < 4 * (c * x) := Nat.mul_lt_mul_of_pos_right hlt (Nat.mul_pos hc0 hx0)
  have h3 : 4 * (c * x) ≤ c * Fintype.card F ^ 4 := by
    calc 4 * (c * x) = c * (x * 4) := by ring
      _ ≤ c * Fintype.card F ^ 4 := Nat.mul_le_mul_left _ h4
  omega

theorem relIndex_eq_two_of_nonlinear_sp {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {E : Subgroup G} (hEM : E ≤ M)
    (hEQ : ∀ e ∈ E, e ∈ Subgroup.centralizer (Uq M T L : Set G) → e ∈ pCoreOf 2 M)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hUE : ⁅Uq M T L, E⁆ ≤ E)
    (hnl : ∃ e ∈ E, ∃ f : MSP.V4 F → MSP.V4 F, IsCoordAct β e f ∧
      ¬ ∀ (c : F) (x : MSP.V4 F), f (c • x) = c • f x) :
    (pCoreOf 2 M).relIndex E = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  have hTV : E ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    hEM.trans (le_normalizer_Uq h.le_normalizer)
  have hLV : L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.L_le.trans (le_normalizer_Uq h.le_normalizer)
  have hsemi : ∀ e ∈ E, ∀ g : MSP.V4 F →+ MSP.V4 F, IsCoordAct β e g →
      ∃ σ : F →+* F, ∀ (c : F) (x : MSP.V4 F), g (c • x) = σ c • g x := by
    intro e he g hg
    obtain ⟨g', hg'⟩ := exists_isCoordAct_sp h hβ hβker (inv_mem (hEM he))
    exact exists_semilinear_sp hα hLV hβ hβα (hTV he) (h.le_normalizer (hEM he)) hg hg'
  obtain ⟨e₀, he₀, f₀', hf₀', hnl₀⟩ := hnl
  obtain ⟨f₀, hf₀⟩ := exists_isCoordAct_sp h hβ hβker (hEM (he₀))
  have hff₀ : f₀' = f₀ := IsCoordAct.unique hβ (hTV (he₀)) hf₀' hf₀
  obtain ⟨σ₀, hσ₀⟩ := hsemi e₀ he₀ f₀ hf₀
  have hne₀ : ∃ c, σ₀ c ≠ c := by
    by_contra hall
    push Not at hall
    apply hnl₀
    intro c x
    rw [hff₀, hσ₀, hall]
  have hA : ∀ e ∈ E, (∀ f : MSP.V4 F → MSP.V4 F, IsCoordAct β e f →
      ∀ (c : F) (x : MSP.V4 F), f (c • x) = c • f x) → e ∈ pCoreOf 2 M := by
    intro e he hlin
    obtain ⟨g, hg⟩ := exists_isCoordAct_sp h hβ hβker (hEM he)
    have hfg : ∀ x, f₀ (g x - x) = g x - x := by
      intro x
      obtain ⟨u, rfl⟩ := exists_coord_eq hβ x
      have hc : ⁅e, (u : G)⁆ ∈ Uq M T L := by
        rw [commutatorElement_def]
        exact mul_mem (conj_mem_of_mem_normalizer (hTV he) u) (inv_mem u.2)
      have hcE : ⁅e, (u : G)⁆ ∈ E := hUE (by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator he u.2)
      have hcrd := crd_commutator_kernel (hTV he) hg u hc
      have he₀c : e₀ ∈ Subgroup.centralizer (E : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy => hEab y hy e₀ he₀
      have hfix := fix_of_mem_centralizer' (u := ⟨_, hc⟩) he₀c hf₀ hcE
      rw [hcrd] at hfix
      exact hfix
    have hid := eq_id_of_quadratic' hσ₀ hne₀ (hlin g hg) hfg
    exact hEQ e he (centralizer_of_actTriv h (mem_actTriv_of_fix h hβker (hEM he) hg hid))
  have hσinv : ∀ e ∈ E, ∀ g : MSP.V4 F →+ MSP.V4 F, IsCoordAct β e g →
      ∀ σ : F →+* F, (∀ (c : F) (x : MSP.V4 F), g (c • x) = σ c • g x) → ∀ c, σ (σ c) = c := by
    intro e he g hg σ hσ c
    have hpow := isCoordAct_iterate' (hTV he) hg 2
    rw [hE2 e he] at hpow
    have hgg : ∀ x, g (g x) = x := fun x => by
      have := congrFun (IsCoordAct.unique hβ (one_mem _) hpow isCoordAct_one) x
      simpa using this
    have hx₀ : (Pi.single (Sum.inl 0) 1 : MSP.V4 F) ≠ 0 := fun h0 => by
      simpa using congrFun h0 (Sum.inl 0)
    have h1 := hgg (c • Pi.single (Sum.inl 0) 1)
    rw [hσ, hσ, hgg] at h1
    exact smul_left_injective F hx₀ h1
  have hnt : ∀ e ∈ E, e ∉ pCoreOf 2 M → ∀ g : MSP.V4 F →+ MSP.V4 F, IsCoordAct β e g →
      ∀ σ : F →+* F, (∀ (c : F) (x : MSP.V4 F), g (c • x) = σ c • g x) → ∃ c, σ c ≠ c := by
    intro e he hn g hg σ hσ
    by_contra hall
    push Not at hall
    exact hn (hA e he fun f hf c x => by
      rw [IsCoordAct.unique hβ (hTV he) hf hg, hσ, hall])
  have hC : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ∉ pCoreOf 2 M → e₂ ∉ pCoreOf 2 M →
      e₁ * e₂ ∈ pCoreOf 2 M := by
    intro e₁ he₁ e₂ he₂ hn₁ hn₂
    obtain ⟨g₁, hg₁⟩ := exists_isCoordAct_sp h hβ hβker (hEM (he₁))
    obtain ⟨g₂, hg₂⟩ := exists_isCoordAct_sp h hβ hβker (hEM (he₂))
    obtain ⟨σ₁, hσ₁⟩ := hsemi e₁ he₁ g₁ hg₁
    obtain ⟨σ₂, hσ₂⟩ := hsemi e₂ he₂ g₂ hg₂
    have heq := ringHom_eq_of_involutive (hσinv e₁ he₁ g₁ hg₁ σ₁ hσ₁)
      (hσinv e₂ he₂ g₂ hg₂ σ₂ hσ₂) (hnt e₁ he₁ hn₁ g₁ hg₁ σ₁ hσ₁) (hnt e₂ he₂ hn₂ g₂ hg₂ σ₂ hσ₂)
    apply hA _ (mul_mem he₁ he₂)
    intro f hf c x
    have hf12 := hg₁.mul (hTV (he₂)) hg₂
    rw [IsCoordAct.unique hβ (hTV ((mul_mem he₁ he₂))) hf hf12]
    simp only [Function.comp_apply]
    rw [hσ₂, hσ₁, heq, hσinv e₂ he₂ g₂ hg₂ σ₂ hσ₂]
  have he₀Q : e₀ ∉ pCoreOf 2 M := by
    intro hQ
    apply hnl₀
    have hcU : e₀ ∈ Subgroup.centralizer (Uq M T L : Set G) :=
      ((inf_centralizer_Uq h).ge hQ).2
    have hid : IsCoordAct β e₀ id := by
      intro u v huv
      have : v = u := by
        apply Subtype.ext
        rw [huv, ← Subgroup.mem_centralizer_iff.mp hcU u u.2, mul_inv_cancel_right]
      rw [this]
      rfl
    rw [IsCoordAct.unique hβ (hTV (he₀)) hf₀' hid]
    intro c x
    rfl
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨e₀, he₀⟩, fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hb : (b : G) ∈ pCoreOf 2 M
  · refine Or.inr ⟨hb, fun h' => he₀Q ?_⟩
    have := mul_mem (inv_mem hb) h'
    simpa using this
  · exact Or.inl ⟨hC b b.2 e₀ he₀ hb he₀Q, hb⟩

end SpM

end CFSG.Quasithin.MS93.S33
