module

public import CFSG.Quasithin.Vol2.Ch11SecB414A
public import CFSG.Quasithin.Vol2.Ch11SecB414K
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.Quasithin.Background.C3Defs

public section

namespace CFSG.Quasithin.H13.Ch4.B414

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix

section SL2

variable {F : Type} [Field F] [CharP F 2]

theorem eq_one_or_fpf (M : Matrix (Fin 2) (Fin 2) F) (hdet : M.det = 1) (h3 : M ^ 3 = 1) :
    M = 1 ∨ ∀ x : Fin 2 → F, M *ᵥ x = x → x = 0 := by
  by_cases h : ∀ x : Fin 2 → F, M *ᵥ x = x → x = 0
  · exact Or.inr h
  left
  push Not at h
  obtain ⟨x, hx, hx0⟩ := h
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two] at hdet
  have e0 := congrFun hx 0
  have e1 := congrFun hx 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  have hd0 : ((M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0) * x 0 = 0 := by
    linear_combination (M 1 1 - 1) * e0 - M 0 1 * e1
  have hd1 : ((M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0) * x 1 = 0 := by
    linear_combination (M 0 0 - 1) * e1 - M 1 0 * e0
  have hdM : (M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0 = 0 := by
    by_contra hne
    apply hx0
    funext i
    fin_cases i
    · exact (mul_eq_zero.mp hd0).resolve_left hne
    · exact (mul_eq_zero.mp hd1).resolve_left hne
  have htr : M 0 0 + M 1 1 = 0 := by linear_combination -hdM + hdet + h2
  have hsq : M * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination M 0 0 * htr - hdet - h2
    · linear_combination M 0 1 * htr
    · linear_combination M 1 0 * htr
    · linear_combination M 1 1 * htr - hdet - h2
  calc M = M * (M * M) := by rw [hsq, mul_one]
    _ = M ^ 3 := by rw [pow_succ', sq]
    _ = 1 := h3

omit [CharP F 2] in
theorem det_of_mem_statedSL {A : GL (Fin 2) F} (hA : A ∈ StatedSL 2 F) :
    (A : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hA

end SL2

section Card

variable {G : Type} [Group G] [Finite G] {V Z : Subgroup G} [Fact (IsElem V Z)]

omit [Finite G] in
theorem card_secPre (W : AddSubgroup (SecU V Z)) :
    Nat.card (secPre V Z W) = Nat.card W * Nat.card Z := by
  classical
  let ψ : ↥(secPre V Z W) →* Multiplicative (SecU V Z) :=
    { toFun := fun g => Multiplicative.ofAdd (secπ V Z ⟨g, (secPre_le V Z W) g.2⟩)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hker : Nat.card ψ.ker = Nat.card Z := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1, (secπ_eq_zero_iff V Z _).mp g.2⟩
        invFun := fun z => ⟨⟨z, le_secPre V Z W z.2⟩,
          (secπ_eq_zero_iff V Z ⟨z, (Fact.out : IsElem V Z).le z.2⟩).mpr z.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrange : Nat.card ψ.range = Nat.card W := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative (SecU V Z)), ?_⟩
        invFun := fun w => ⟨Multiplicative.ofAdd (w : SecU V Z), ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · obtain ⟨g, hg⟩ := x.2
      rw [← hg]
      obtain ⟨_, h⟩ := g.2
      exact h
    · obtain ⟨v, hv⟩ := secπ_surjective V Z (w : SecU V Z)
      exact ⟨⟨v, v.2, hv ▸ w.2⟩, congrArg Multiplicative.ofAdd hv⟩
  have h := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange] at h
  rw [← h, mul_comm]

end Card

section Chief

variable {G : Type} [Group G] [Finite G] {V Z : Subgroup G} [Fact (IsElem V Z)]
  {Γ : Subgroup G} (hΓV : Γ ≤ normalizer (V : Set G)) (hΓZ : Γ ≤ normalizer (Z : Set G))

omit [Finite G] in
theorem secRep_sub (γ : ↥Γ) (v : ↥V) :
    secRep V Z Γ hΓV hΓZ γ (secπ V Z v) - secπ V Z v =
      secπ V Z (conjV V γ (hΓV γ.2) v * v⁻¹) := by
  rw [secRep_secπ, secπ_mul, secπ_inv, sub_eq_add_neg]

omit [Finite G] in
theorem secImg_mono {J₁ J₂ : Subgroup G} (h : J₁ ≤ J₂) : secImg V Z J₁ ≤ secImg V Z J₂ := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

theorem card_chief {L : Subgroup G} (hLΓ : L ≤ Γ) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 4)
    (hnat : ∀ C₁ C₂ : Subgroup G, Z ≤ C₁ → C₁ < C₂ → C₂ ≤ V →
      L ≤ normalizer (C₁ : Set G) → L ≤ normalizer (C₂ : Set G) →
      (∀ J : Subgroup G, C₁ ≤ J → J ≤ C₂ → L ≤ normalizer (J : Set G) → J = C₁ ∨ J = C₂) →
      (∃ l ∈ L, ∃ c ∈ C₂, l * c * l⁻¹ * c⁻¹ ∉ C₁) →
      ∃ N' : Subgroup ↥L, IsNaturalSection L C₂ C₁ N' (StatedSL 2 F))
    {γ : ↥Γ} (hγL : (γ : G) ∈ L) (hγ3 : secRep V Z Γ hΓV hΓZ (γ ^ 3) = 1)
    {A B : AddSubgroup (SecU V Z)}
    (hA : ∀ l : ↥Γ, (l : G) ∈ L → ∀ u ∈ A, secRep V Z Γ hΓV hΓZ l u ∈ A)
    (hB : ∀ l : ↥Γ, (l : G) ∈ L → ∀ u ∈ B, secRep V Z Γ hΓV hΓZ l u ∈ B) (hBA : B < A)
    (hch : ∀ C : AddSubgroup (SecU V Z),
      (∀ l : ↥Γ, (l : G) ∈ L → ∀ u ∈ C, secRep V Z Γ hΓV hΓZ l u ∈ C) →
      B ≤ C → C ≤ A → C = B ∨ C = A) :
    Nat.card A = Nat.card (fixRel (secRep V Z Γ hΓV hΓZ γ).toAddMonoidHom B A) ∨
      Nat.card A = 16 * Nat.card (fixRel (secRep V Z Γ hΓV hΓZ γ).toAddMonoidHom B A) := by
  classical
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 2) (by norm_num) (by rw [Nat.card_eq_fintype_card, hF]; norm_num)
  set t := (secRep V Z Γ hΓV hΓZ γ).toAddMonoidHom with htdef
  set C₁ := secPre V Z B with hC₁
  set C₂ := secPre V Z A with hC₂
  have hC₁₂ : C₁ < C₂ := lt_of_le_of_ne ((secPre_le_secPre_iff V Z).mpr hBA.le)
    fun h => hBA.ne (secPre_injective V Z h)
  have hLC₁ := le_normalizer_secPre V Z hΓV hΓZ hLΓ fun l hl u hu => hB l hl u hu
  have hLC₂ := le_normalizer_secPre V Z hΓV hΓZ hLΓ fun l hl u hu => hA l hl u hu
  have hchJ : ∀ J : Subgroup G, C₁ ≤ J → J ≤ C₂ → L ≤ normalizer (J : Set G) →
      J = C₁ ∨ J = C₂ := by
    intro J hJ₁ hJ₂ hLJ
    have hZJ : Z ≤ J := (le_secPre V Z B).trans hJ₁
    have hJV : J ≤ V := hJ₂.trans (secPre_le V Z A)
    have hBC : B ≤ secImg V Z J := by
      rw [← secImg_secPre V Z B]
      exact secImg_mono hJ₁
    have hCA : secImg V Z J ≤ A := by
      rw [← secImg_secPre V Z A]
      exact secImg_mono hJ₂
    rcases hch _ (fun l hl u hu => secImg_stable V Z hΓV hΓZ (hLJ hl) hu) hBC hCA with h | h
    · left
      rw [← secPre_secImg V Z hZJ hJV, h]
    · right
      rw [← secPre_secImg V Z hZJ hJV, h]
  have hta : ∀ c : ↥V, t (secπ V Z c) - secπ V Z c ∈ B ↔
      (γ : G) * c * (γ : G)⁻¹ * (c : G)⁻¹ ∈ C₁ := by
    intro c
    rw [htdef, LinearMap.toAddMonoidHom_coe, secRep_sub]
    exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩
  have hmemA : ∀ c : ↥V, secπ V Z c ∈ A ↔ (c : G) ∈ C₂ :=
    fun c => ⟨fun h => ⟨c.2, h⟩, fun ⟨_, h⟩ => h⟩
  have hmemB : ∀ c : ↥V, secπ V Z c ∈ B ↔ (c : G) ∈ C₁ :=
    fun c => ⟨fun h => ⟨c.2, h⟩, fun ⟨_, h⟩ => h⟩
  by_cases hnt : ∃ l ∈ L, ∃ c ∈ C₂, l * c * l⁻¹ * c⁻¹ ∉ C₁
  swap
  ·
    left
    push Not at hnt
    have hfix : fixRel t B A = A := by
      refine le_antisymm (fun a ha => ha.1) (fun a ha => ⟨ha, ?_⟩)
      obtain ⟨c, rfl⟩ := secπ_surjective V Z a
      exact (hta c).mpr (hnt _ hγL c ((hmemA c).mp ha))
    rw [hfix]
  obtain ⟨N', -, αW, -, -, βW, hβs, hβk, hβe⟩ :=
    hnat C₁ C₂ (le_secPre V Z B) hC₁₂ (secPre_le V Z A) hLC₁ hLC₂ hchJ hnt
  set g : ↥L := ⟨γ, hγL⟩ with hg
  set M : Matrix (Fin 2) (Fin 2) F := ((αW g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    with hM
  have hβker : ∀ c : ↥C₂, βW c = 1 ↔ (c : G) ∈ C₁ := fun c => by
    rw [← MonoidHom.mem_ker, hβk, mem_subgroupOf]
  have hβeq : ∀ c c' : ↥C₂, βW c = βW c' ↔ (c : G) * (c' : G)⁻¹ ∈ C₁ := fun c c' => by
    have h := hβker (c * c'⁻¹)
    rw [map_mul, map_inv, mul_inv_eq_one] at h
    exact h
  have h16 : Nat.card A = 16 * Nat.card B := by
    have h1 := Subgroup.card_ker_mul_card_range βW
    rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top, hβk,
      Nat.card_congr (subgroupOfEquivOfLe hC₁₂.le).toEquiv] at h1
    have h2 : Nat.card (Multiplicative (Fin 2 → F)) = 16 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card (α := F),
        hF]
      norm_num
    rw [h2, hC₁, hC₂, card_secPre, card_secPre] at h1
    have hZ : 0 < Nat.card Z := Nat.card_pos
    have := h1.symm
    nlinarith [this]
  have hact : ∀ c : ↥C₂, ∀ h : (γ : G) * c * (γ : G)⁻¹ ∈ C₂,
      Multiplicative.toAdd (βW ⟨_, h⟩) = M *ᵥ Multiplicative.toAdd (βW c) :=
    fun c h => hβe g c ⟨_, h⟩ rfl
  have hdet : M.det = 1 := det_of_mem_statedSL (αW g).2
  have hM3 : M ^ 3 = 1 := by
    have hpow : ∀ w : Fin 2 → F, M ^ 3 *ᵥ w = w := by
      intro w
      obtain ⟨c, hc⟩ := hβs (Multiplicative.ofAdd w)
      have hc3 : (g ^ 3 : ↥L) * (c : G) * ((g ^ 3 : ↥L) : G)⁻¹ ∈ C₂ :=
        (mem_normalizer_iff.mp (hLC₂ (g ^ 3).2) c).mp c.2
      have h1 := hβe (g ^ 3) c ⟨_, hc3⟩ rfl
      have h2 : βW ⟨_, hc3⟩ = βW c := by
        rw [hβeq]
        have h3 := (secRep_eq_one_iff V Z Γ hΓV hΓZ (γ ^ 3)).mp hγ3 c (secPre_le V Z A c.2)
        exact le_secPre V Z B (by simpa using h3)
      rw [h2, hc, map_pow, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val] at h1
      exact h1.symm
    ext i j
    have := congrFun (hpow (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  rcases eq_one_or_fpf M hdet hM3 with h1 | hfpf
  ·
    left
    suffices hfix : fixRel t B A = A by rw [hfix]
    refine le_antisymm (fun a ha => ha.1) (fun a ha => ⟨ha, ?_⟩)
    obtain ⟨c, rfl⟩ := secπ_surjective V Z a
    have hc2 : (c : G) ∈ C₂ := (hmemA c).mp ha
    have hgc : (γ : G) * c * (γ : G)⁻¹ ∈ C₂ := (mem_normalizer_iff.mp (hLC₂ hγL) c).mp hc2
    have h2 := hact ⟨c, hc2⟩ hgc
    rw [h1, Matrix.one_mulVec] at h2
    have h3 := (hβeq ⟨_, hgc⟩ ⟨c, hc2⟩).mp (by
      apply Multiplicative.toAdd.injective
      exact h2)
    exact (hta c).mpr h3
  ·
    right
    have hfix : fixRel t B A = B := by
      refine le_antisymm (fun a ha => ?_) (fun b hb => ⟨hBA.le hb, B.sub_mem (hB γ hγL b hb) hb⟩)
      obtain ⟨c, rfl⟩ := secπ_surjective V Z a
      have hc2 : (c : G) ∈ C₂ := (hmemA c).mp ha.1
      have hgc : (γ : G) * c * (γ : G)⁻¹ ∈ C₂ := (mem_normalizer_iff.mp (hLC₂ hγL) c).mp hc2
      have h3 : βW ⟨_, hgc⟩ = βW ⟨c, hc2⟩ := (hβeq _ _).mpr ((hta c).mp ha.2)
      have h4 := hact ⟨c, hc2⟩ hgc
      rw [h3] at h4
      have h5 := hfpf _ h4.symm
      have h6 : βW ⟨c, hc2⟩ = 1 := Multiplicative.toAdd.injective h5
      exact (hmemB c).mpr ((hβker _).mp h6)
    rw [hfix, h16]

end Chief

end CFSG.Quasithin.H13.Ch4.B414
