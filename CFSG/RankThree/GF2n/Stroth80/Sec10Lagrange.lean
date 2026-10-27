module

public import CFSG.RankThree.GF2n.Stroth80.GlobalModelData

public section

namespace CFSG.RankThree.GF2n.Tim79.QuadModel

open scoped commutatorElement

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

private theorem B_nondegenerate (M₀ : QuadModel QF V K γ) : M₀.B.Nondegenerate := by
  refine ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => ?_⟩
  rw [B_comm, hy f, neg_zero]

private theorem finite_K_of_gammaReg [Finite G] (R : GammaReg QF V γ) : Finite K :=
  Finite.of_surjective (fun w : V => γ (w : G)) fun s => by
    obtain ⟨a, ha, rfl⟩ := R.surj s
    exact ⟨⟨a, ha⟩, rfl⟩

private theorem B_eq_zero_of_mem_span (M₀ : QuadModel QF V K γ) {S : AddSubgroup M₀.E}
    (hS : ∀ x ∈ S, ∀ y ∈ S, M₀.B x y = 0) {x y : M₀.E}
    (hx : x ∈ Submodule.span K (S : Set M₀.E)) (hy : y ∈ Submodule.span K (S : Set M₀.E)) :
    M₀.B x y = 0 :=
  Submodule.span_induction₂ (p := fun x y _ _ => M₀.B x y = 0)
    (fun a b ha hb => hS a ha b hb)
    (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ _ _ _ _ _ ha hb => by simp [map_add, LinearMap.add_apply, ha, hb])
    (fun _ _ _ _ _ _ ha hb => by simp [map_add, ha, hb])
    (fun _ _ _ _ _ ha => by simp [map_smul, LinearMap.smul_apply, ha])
    (fun _ _ _ _ _ ha => by simp [map_smul, LinearMap.smul_apply, ha]) hx hy

private theorem two_mul_finrank_span_le_of_isotropic (M₀ : QuadModel QF V K γ)
    {S : AddSubgroup M₀.E} (hS : ∀ x ∈ S, ∀ y ∈ S, M₀.B x y = 0) :
    2 * Module.finrank K (Submodule.span K (S : Set M₀.E)) ≤ Module.finrank K M₀.E := by
  haveI : Module.Finite K M₀.E := M₀.fin
  have hle : Submodule.span K (S : Set M₀.E) ≤
      M₀.B.orthogonal (Submodule.span K (S : Set M₀.E)) := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact B_eq_zero_of_mem_span M₀ hS hy hx
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal (B_nondegenerate M₀)] at h1
  have h2 := Submodule.finrank_le (Submodule.span K (S : Set M₀.E))
  omega

private theorem eq_of_gamma_eq (M₀ : QuadModel QF V K γ) (R : GammaReg QF V γ) {u v : G}
    (hu : u ∈ V) (hv : v ∈ V) (h : γ u = γ v) : u = v := by
  have hvv : γ (v * v) = 0 := by
    have hvQ : v ∈ QF := R.V_le hv
    have hπ : M₀.π v = 0 := (M₀.π_ker v hvQ).mpr hv
    rw [show v * v = v ^ 2 by rw [pow_two], M₀.sq_eq v hvQ, hπ]
    exact M₀.Qf_zero
  have h2 : γ v + γ v = 0 := by rw [← R.add v hv v hv, hvv]
  have h1 : γ (u * v) = 0 := by rw [R.add u hu v hv, h, h2]
  have huv : u * v = 1 := R.inj _ (V.mul_mem hu hv) h1
  have hv2 : v ^ 2 = 1 :=
    R.inj _ (by rw [pow_two]; exact V.mul_mem hv hv) (by rw [pow_two]; exact hvv)
  calc u = u * v * v := by rw [mul_assoc, ← pow_two, hv2, mul_one]
    _ = 1 * v := by rw [huv]
    _ = v := one_mul v

private theorem B_eq_zero_on_img (M₀ : QuadModel QF V K γ) (R : GammaReg QF V γ)
    {A : Subgroup G} (hAQ : A ≤ QF) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∀ e ∈ M₀.img A, ∀ f ∈ M₀.img A, M₀.B e f = 0 := by
  intro e he f hf
  obtain ⟨a, haA, haQ, rfl⟩ := he
  obtain ⟨b, hbA, hbQ, rfl⟩ := hf
  exact (comm_iff_B M₀ R haQ hbQ).mp (hA a haA b hbA)

private theorem card_img_sq [Finite G] (M₀ : QuadModel QF V K γ) (R : GammaReg QF V γ)
    {A : Subgroup G} (hAQ : A ≤ QF) (hVA : V ≤ A)
    (hcard : Nat.card A ^ 2 = Nat.card QF * Nat.card V) :
    Nat.card (M₀.img A) ^ 2 = Nat.card M₀.E := by
  have h1 : Nat.card A = Nat.card V * Nat.card (M₀.img A) := card_eq M₀ hAQ hVA
  have himgQ : M₀.img QF = ⊤ := by
    refine le_antisymm le_top ?_
    intro e _
    obtain ⟨y, hyQ, hπ⟩ := M₀.π_surj e
    exact ⟨y, hyQ, hyQ, hπ⟩
  have h2 : Nat.card QF = Nat.card V * Nat.card M₀.E := by
    have h := card_eq M₀ (S := QF) le_rfl R.V_le
    rwa [himgQ, AddSubgroup.card_top] at h
  have h4 : Nat.card V ^ 2 * Nat.card (M₀.img A) ^ 2 =
      Nat.card V ^ 2 * Nat.card M₀.E := by
    calc Nat.card V ^ 2 * Nat.card (M₀.img A) ^ 2 =
          (Nat.card V * Nat.card (M₀.img A)) ^ 2 := by ring
      _ = Nat.card A ^ 2 := by rw [h1]
      _ = Nat.card QF * Nat.card V := hcard
      _ = (Nat.card V * Nat.card M₀.E) * Nat.card V := by rw [h2]
      _ = Nat.card V ^ 2 * Nat.card M₀.E := by ring
  exact Nat.eq_of_mul_eq_mul_left (pow_pos Nat.card_pos 2) h4

private theorem card_span_img_sq [Finite G] (M₀ : QuadModel QF V K γ) (R : GammaReg QF V γ)
    {A : Subgroup G} (hAQ : A ≤ QF) (hVA : V ≤ A)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card A ^ 2 = Nat.card QF * Nat.card V) :
    Nat.card (Submodule.span K (M₀.img A : Set M₀.E)) ^ 2 = Nat.card M₀.E := by
  haveI : Finite K := finite_K_of_gammaReg R
  haveI : Module.Finite K M₀.E := M₀.fin
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hWc : Nat.card (Submodule.span K (M₀.img A : Set M₀.E)) =
      Nat.card K ^ Module.finrank K (Submodule.span K (M₀.img A : Set M₀.E)) :=
    Module.natCard_eq_pow_finrank
  have hEc : Nat.card M₀.E = Nat.card K ^ Module.finrank K M₀.E :=
    Module.natCard_eq_pow_finrank
  have h1 : Nat.card (Submodule.span K (M₀.img A : Set M₀.E)) ^ 2 =
      Nat.card K ^ (2 * Module.finrank K (Submodule.span K (M₀.img A : Set M₀.E))) := by
    rw [Nat.mul_comm (2 : ℕ) _, hWc, pow_mul]
  have hle : Nat.card (Submodule.span K (M₀.img A : Set M₀.E)) ^ 2 ≤ Nat.card M₀.E :=
    calc Nat.card (Submodule.span K (M₀.img A : Set M₀.E)) ^ 2
        = Nat.card K ^ (2 * Module.finrank K (Submodule.span K (M₀.img A : Set M₀.E))) := h1
      _ ≤ Nat.card K ^ Module.finrank K M₀.E :=
          Nat.pow_le_pow_right Nat.card_pos
            (two_mul_finrank_span_le_of_isotropic M₀ (B_eq_zero_on_img M₀ R hAQ hA))
      _ = Nat.card M₀.E := hEc.symm
  have hsub : (M₀.img A : Set M₀.E) ⊆
      (Submodule.span K (M₀.img A : Set M₀.E) : Set M₀.E) :=
    fun z hz => Submodule.subset_span hz
  have hSWle : Nat.card (M₀.img A) ≤ Nat.card (Submodule.span K (M₀.img A : Set M₀.E)) :=
    Nat.card_le_card_of_injective (fun z : M₀.img A =>
      (⟨z.1, hsub z.2⟩ : Submodule.span K (M₀.img A : Set M₀.E)))
      (fun a b h => Subtype.ext (congrArg
        (fun z : Submodule.span K (M₀.img A : Set M₀.E) => (z : M₀.E)) h))
  refine le_antisymm hle ?_
  rw [← card_img_sq M₀ R hAQ hVA hcard]
  exact Nat.pow_le_pow_left hSWle 2

private theorem two_mul_finrank_span_img [Finite G] (M₀ : QuadModel QF V K γ)
    (R : GammaReg QF V γ) {A : Subgroup G} (hAQ : A ≤ QF) (hVA : V ≤ A)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card A ^ 2 = Nat.card QF * Nat.card V) :
    2 * Module.finrank K (Submodule.span K (M₀.img A : Set M₀.E)) =
      Module.finrank K M₀.E := by
  haveI : Finite K := finite_K_of_gammaReg R
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Module.Finite K M₀.E := M₀.fin
  have hWc : Nat.card (Submodule.span K (M₀.img A : Set M₀.E)) =
      Nat.card K ^ Module.finrank K (Submodule.span K (M₀.img A : Set M₀.E)) :=
    Module.natCard_eq_pow_finrank
  have hEc : Nat.card M₀.E = Nat.card K ^ Module.finrank K M₀.E :=
    Module.natCard_eq_pow_finrank
  have h1 : Nat.card (Submodule.span K (M₀.img A : Set M₀.E)) ^ 2 =
      Nat.card K ^ (2 * Module.finrank K (Submodule.span K (M₀.img A : Set M₀.E))) := by
    rw [Nat.mul_comm (2 : ℕ) _, hWc, pow_mul]
  have h3 : Nat.card K ^ (2 * Module.finrank K (Submodule.span K (M₀.img A : Set M₀.E))) =
      Nat.card K ^ Module.finrank K M₀.E := by
    rw [← h1, card_span_img_sq M₀ R hAQ hVA hA hcard, hEc]
  refine Nat.pow_right_injective ?_ h3
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

private theorem span_img_eq [Finite G] (M₀ : QuadModel QF V K γ) (R : GammaReg QF V γ)
    {A : Subgroup G} (hAQ : A ≤ QF) (hVA : V ≤ A)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card A ^ 2 = Nat.card QF * Nat.card V) :
    (Submodule.span K (M₀.img A : Set M₀.E) : Set M₀.E) = (M₀.img A : Set M₀.E) := by
  haveI : Finite K := finite_K_of_gammaReg R
  haveI : Module.Finite K M₀.E := M₀.fin
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hWleS : Nat.card (Submodule.span K (M₀.img A : Set M₀.E)) ≤ Nat.card (M₀.img A) :=
    (Nat.pow_le_pow_iff_left (show (2 : ℕ) ≠ 0 by norm_num)).mp
      (by rw [card_span_img_sq M₀ R hAQ hVA hA hcard, card_img_sq M₀ R hAQ hVA hcard])
  have hsub : (M₀.img A : Set M₀.E) ⊆
      (Submodule.span K (M₀.img A : Set M₀.E) : Set M₀.E) :=
    fun z hz => Submodule.subset_span hz
  exact (Set.Finite.eq_of_subset_of_card_le (s := (M₀.img A : Set M₀.E))
    (t := (Submodule.span K (M₀.img A : Set M₀.E) : Set M₀.E))
    (Set.toFinite _) hsub hWleS).symm

private theorem orthogonal_span_img [Finite G] (M₀ : QuadModel QF V K γ) (R : GammaReg QF V γ)
    {A : Subgroup G} (hAQ : A ≤ QF) (hVA : V ≤ A)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card A ^ 2 = Nat.card QF * Nat.card V) :
    M₀.B.orthogonal (Submodule.span K (M₀.img A : Set M₀.E)) =
      Submodule.span K (M₀.img A : Set M₀.E) := by
  haveI : Module.Finite K M₀.E := M₀.fin
  have hle : Submodule.span K (M₀.img A : Set M₀.E) ≤
      M₀.B.orthogonal (Submodule.span K (M₀.img A : Set M₀.E)) := by
    intro y hy
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro z hz
    exact B_eq_zero_of_mem_span M₀ (B_eq_zero_on_img M₀ R hAQ hA) hz hy
  have heq : Submodule.span K (M₀.img A : Set M₀.E) =
      M₀.B.orthogonal (Submodule.span K (M₀.img A : Set M₀.E)) := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [LinearMap.BilinForm.finrank_orthogonal (B_nondegenerate M₀)]
    have h2 := two_mul_finrank_span_img M₀ R hAQ hVA hA hcard
    omega
  exact heq.symm

theorem exists_comm_eq_of_lagrangian [Finite G] (M₀ : QuadModel QF V K γ)
    (R : GammaReg QF V γ) {A : Subgroup G} (hAQ : A ≤ QF) (hVA : V ≤ A)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card A ^ 2 = Nat.card QF * Nat.card V) {x : G} (hx : x ∈ QF) (hxA : x ∉ A)
    {v : G} (hv : v ∈ V) : ∃ a ∈ A, ⁅x, a⁆ = v := by
  have hWorth := orthogonal_span_img M₀ R hAQ hVA hA hcard
  have hmem : ∀ e : M₀.E, e ∈ Submodule.span K (M₀.img A : Set M₀.E) ↔ e ∈ M₀.img A :=
    fun e => Set.ext_iff.mp (span_img_eq M₀ R hAQ hVA hA hcard) e
  have hxW : M₀.π x ∉ Submodule.span K (M₀.img A : Set M₀.E) := by
    intro h
    exact hxA ((mem_img_iff M₀ hVA hx).mp ((hmem (M₀.π x)).mp h))
  obtain ⟨w₀, hw₀W, hw₀⟩ : ∃ w ∈ Submodule.span K (M₀.img A : Set M₀.E),
      M₀.B (M₀.π x) w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hxW
    have horth : M₀.π x ∈
        M₀.B.orthogonal (Submodule.span K (M₀.img A : Set M₀.E)) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro z hz
      rw [M₀.B_comm, hcon z hz, neg_zero]
    rwa [hWorth] at horth
  have honto : ∀ s : K, ∃ w ∈ Submodule.span K (M₀.img A : Set M₀.E),
      M₀.B (M₀.π x) w = s := by
    intro s
    exact ⟨(s / M₀.B (M₀.π x) w₀) • w₀, Submodule.smul_mem _ _ hw₀W,
      by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hw₀]⟩
  obtain ⟨w, hwW, hw⟩ := honto (γ v)
  obtain ⟨a, haA, haQ, haπ⟩ := (mem_img M₀).mp ((hmem w).mp hwW)
  refine ⟨a, haA, ?_⟩
  refine eq_of_gamma_eq M₀ R (M₀.comm_mem x hx a haQ) hv ?_
  rw [M₀.comm_eq x hx a haQ, haπ, hw]

end CFSG.RankThree.GF2n.Tim79.QuadModel

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem StrothHyp.exists_comm_eq_of_lagrangian [Finite G]
    {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {A : Subgroup G} (hAQ : A ≤ Q) (hZA : Z ≤ A)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card A ^ 2 = Nat.card Q * Nat.card Z) {x : G} (hx : x ∈ Q) (hxA : x ∉ A)
    {z : G} (hz : z ∈ Z) : ∃ a ∈ A, ⁅x, a⁆ = z := by
  obtain ⟨K, hK, hfin, hch, γ, M₀, hD⟩ := stroth_globalModelData H
  exact Tim79.QuadModel.exists_comm_eq_of_lagrangian M₀ hD.reg hAQ hZA hA hcard hx hxA hz

end CFSG.RankThree.GF2n.Stroth80
