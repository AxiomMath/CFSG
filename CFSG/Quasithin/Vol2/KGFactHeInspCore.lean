module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeA
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.Quasithin.H13.KGInsp

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KGH91
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open Matrix

variable {X : Type} [Group X]

theorem conj_mem_pCoreOf {N : Subgroup X} {g x : X} (hg : g ∈ N) (hx : x ∈ pCoreOf 2 N) :
    g * x * g⁻¹ ∈ pCoreOf 2 N :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N hg) x).mp hx

section Natural

variable {Y W₁ W₂ : Subgroup X} (C₁ : NatCoord Y W₁ 3)

theorem card_sl3 : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three]

theorem card_Y : Nat.card Y = 168 * Nat.card C₁.ρ.ker := by
  rw [← card_sl3, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective C₁.ρ
    C₁.ρ_surj).toEquiv, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

theorem exists_ne_one (C₁ : NatCoord Y W₁ 3) : ∃ a ∈ W₁, a ≠ 1 := by
  obtain ⟨a, ha, hE⟩ := C₁.surj (Pi.single 0 1)
  refine ⟨a, ha, fun h => ?_⟩
  rw [h, C₁.E_one] at hE
  have := congrFun hE 0
  simp at this

variable [Finite X] {N : Subgroup X} (hYN : Y ≤ N)
include hYN

theorem inf_le_ker : (Y ⊓ pCoreOf 2 N).subgroupOf Y ≤ C₁.ρ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := (Y ⊓ pCoreOf 2 N).subgroupOf Y with hK
  have hKn : K.Normal := ⟨fun k hk y => by
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    refine ⟨Y.mul_mem (Y.mul_mem y.2 hk.1) (Y.inv_mem y.2), ?_⟩
    exact conj_mem_pCoreOf (hYN y.2) hk.2⟩
  have hK2 : IsPGroup 2 K := by
    have h := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le
      (inf_le_right : Y ⊓ pCoreOf 2 N ≤ pCoreOf 2 N)
    exact h.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hmap : (K.map C₁.ρ).Normal := Subgroup.Normal.map hKn C₁.ρ C₁.ρ_surj
  have hbot := NatCoord.eq_bot_of_normal_isPGroup (le_refl 3) (hK2.map C₁.ρ)
  rw [Subgroup.map_eq_bot_iff] at hbot
  exact hbot

theorem rho_conj_eq {p : X} (hp : p ∈ pCoreOf 2 N) (y : Y)
    (hpy : p * (y : X) * p⁻¹ ∈ Y) : C₁.ρ ⟨p * (y : X) * p⁻¹, hpy⟩ = C₁.ρ y := by
  have hc : p * (y : X) * p⁻¹ * (y : X)⁻¹ ∈ Y ⊓ pCoreOf 2 N := by
    refine ⟨Y.mul_mem hpy (Y.inv_mem y.2), ?_⟩
    have h1 : (y : X) * p⁻¹ * (y : X)⁻¹ ∈ pCoreOf 2 N :=
      conj_mem_pCoreOf (hYN y.2) ((pCoreOf 2 N).inv_mem hp)
    have h2 := (pCoreOf 2 N).mul_mem hp h1
    simpa [mul_assoc] using h2
  have hker := inf_le_ker C₁ hYN (x := ⟨_, hc.1⟩) (by
    rw [Subgroup.mem_subgroupOf]
    exact hc)
  rw [MonoidHom.mem_ker] at hker
  have e : (⟨p * (y : X) * p⁻¹, hpy⟩ : Y) = ⟨_, hc.1⟩ * y := by
    apply Subtype.ext
    simp
  rw [e, map_mul, hker, one_mul]

theorem card_inf_le : Nat.card ↥(pCoreOf 2 N ⊓ Y) ≤ Nat.card C₁.ρ.ker := by
  rw [inf_comm, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  exact Subgroup.card_le_of_le (inf_le_ker C₁ hYN)

theorem false_of_card_le (hNY : N ≤ Subgroup.normalizer (Y : Set X)) {C₂ : NatCoord Y W₂ 3}
    (hdual : ∀ y, C₂.ρ y = slGraphAut 3 (ZMod 2) (C₁.ρ y))
    (hcard : Nat.card N ≤ 168 * Nat.card (pCoreOf 2 N)) {t : X} (htN : t ∈ N)
    (ht : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₂) : False := by
  set P := pCoreOf 2 N with hP
  have hYP : Y ≤ Subgroup.normalizer (P : Set X) :=
    hYN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N)
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hYP
  have hinf := card_inf_le C₁ hYN
  have hY := card_Y C₁
  have hle : P ⊔ Y ≤ N := sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 N) hYN
  have hNeq : P ⊔ Y = N := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hk : 0 < Nat.card C₁.ρ.ker := Nat.card_pos
    have h1 : Nat.card ↥(P ⊔ Y) * Nat.card C₁.ρ.ker ≥ Nat.card P * Nat.card Y :=
      hprod ▸ Nat.mul_le_mul_left _ hinf
    rw [hY] at h1
    have h2 : Nat.card ↥(P ⊔ Y) ≥ 168 * Nat.card P := by
      by_contra h
      push Not at h
      have := Nat.mul_lt_mul_of_pos_right h hk
      nlinarith
    omega
  have htPY : t ∈ ((P ⊔ Y : Subgroup X) : Set X) := by rw [hNeq]; exact htN
  rw [Subgroup.coe_mul_of_right_le_normalizer_left P Y hYP] at htPY
  obtain ⟨p, hp, y₀, hy₀, rfl⟩ := htPY
  have hpN : p ∈ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N hp
  have hconjY : ∀ y ∈ Y, p * y * p⁻¹ ∈ Y := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hNY hpN) y).mp hy
  have hfW : ∀ a ∈ W₁, p * a * p⁻¹ ∈ W₂ := by
    intro a ha
    have h1 : y₀⁻¹ * a * y₀⁻¹⁻¹ ∈ W₁ := C₁.conj_mem ⟨y₀⁻¹, Y.inv_mem hy₀⟩ ha
    have h2 : p * y₀ * (y₀⁻¹ * a * y₀⁻¹⁻¹) * (p * y₀)⁻¹ ∈ W₂ := ht _ h1
    have e : p * a * p⁻¹ = p * y₀ * (y₀⁻¹ * a * y₀⁻¹⁻¹) * (p * y₀)⁻¹ := by group
    rw [e]
    exact h2
  have hfl : ∀ (l : ↥Y), ∀ a ∈ W₁, p * ((l : X) * a * (l : X)⁻¹) * p⁻¹ =
      (l : X) * (p * a * p⁻¹) * (l : X)⁻¹ := by
    intro l a ha
    set l' : Y := ⟨p * l * p⁻¹, hconjY l l.2⟩ with hl'
    have hρ : C₂.ρ l' = C₂.ρ l := by rw [hdual, hdual, hl', rho_conj_eq C₁ hYN hp l]
    have hb : p * a * p⁻¹ ∈ W₂ := hfW a ha
    have hact : (l' : X) * (p * a * p⁻¹) * (l' : X)⁻¹ = (l : X) * (p * a * p⁻¹) * (l : X)⁻¹ :=
      C₂.inj _ (C₂.conj_mem l' hb) _ (C₂.conj_mem l hb) (by
        rw [C₂.conj l' _ hb, C₂.conj l _ hb, hρ])
    rw [← hact, hl']
    group
  have h1 := NatCoord.eq_one_of_dual C₁ (le_refl 3) hdual hfW
    (fun a _ b _ => by group) hfl
  obtain ⟨a, ha, hne⟩ := exists_ne_one C₁
  apply hne
  have h2 := h1 a ha
  have : a = p⁻¹ * (p * a * p⁻¹) * p := by group
  rw [this, h2]
  group

end Natural

theorem normalizer_ne_top [Finite X] [IsSimpleGroup X] (hX : Nat.card X ≠ 168) {Y W₁ : Subgroup X}
    (C₁ : NatCoord Y W₁ 3) (hK : IsPGroup 2 C₁.ρ.ker) :
    Subgroup.normalizer (Y : Set X) ≠ ⊤ := by
  intro htop
  have hYn : Y.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hY := card_Y C₁
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with h | h
  · have h1 : Nat.card Y = 1 := by rw [h, Subgroup.card_bot]
    have : 0 < Nat.card C₁.ρ.ker := Nat.card_pos
    omega
  · set K := C₁.ρ.ker.map Y.subtype with hKdef
    have hKn : K.Normal := ⟨fun k hk g => by
      obtain ⟨k', hk', rfl⟩ := hk
      have hg : g ∈ Y := h ▸ Subgroup.mem_top g
      refine ⟨⟨g, hg⟩ * k' * ⟨g, hg⟩⁻¹, (C₁.ρ.normal_ker).conj_mem k' hk' ⟨g, hg⟩, ?_⟩
      simp⟩
    have hKc : Nat.card K = Nat.card C₁.ρ.ker :=
      Subgroup.card_map_of_injective Y.subtype_injective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hK0 | hK1
    · apply hX
      have h1 : Nat.card C₁.ρ.ker = 1 := by rw [← hKc, hK0, Subgroup.card_bot]
      rw [← Subgroup.card_top (G := X), ← h, hY, h1]
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2 : IsPGroup 2 K := hK.map Y.subtype
      rw [hK1] at h2
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp h2)
      have h3 : 3 ∣ Nat.card (⊤ : Subgroup X) := by
        rw [← h, hY]
        exact Dvd.dvd.mul_right (by norm_num) _
      rw [hn] at h3
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

theorem false_of_inner [Finite X] [IsSimpleGroup X] (hX : Nat.card X ≠ 168)
    (hinn : ∀ α : MulAut X, ∃ g : X, α = MulAut.conj g)
    (hN : ∀ Y : Subgroup X, (∃ R : Subgroup X, IsSylowTwoOf R ⊤ ∧
        R ≤ Subgroup.normalizer (Y : Set X)) → 168 ∣ Nat.card Y →
      Subgroup.normalizer (Y : Set X) ≠ ⊤ →
      Nat.card (Subgroup.normalizer (Y : Set X)) ≤
        168 * Nat.card (pCoreOf 2 (Subgroup.normalizer (Y : Set X)))) :
    ¬ HeInspCfg X 3 := by
  rintro ⟨Y, W₁, W₂, C₁, C₂, τ, -, -, -, hK, hdual, hτY, hτW, hsyl⟩
  obtain ⟨t, rfl⟩ := hinn τ
  have htN : t ∈ Subgroup.normalizer (Y : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hτY
  have hcard := hN Y (hsyl rfl) (by rw [card_Y C₁]; exact dvd_mul_right _ _)
    (normalizer_ne_top hX C₁ hK)
  exact false_of_card_le C₁ Subgroup.le_normalizer le_rfl hdual hcard htN
    (fun w hw => by simpa using hτW w hw)

end CFSG.Quasithin.H13.KGInsp
