module

public import CFSG.Milestones.ASVolI.C135.NA
public import CFSG.Milestones.ASVolI.C135.P2
public import CFSG.Quasithin.Vol2.Ch4Sec3C135Lin

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4.C135 (cnj coe_cnj slNat slNat_surjective dualHom coe_dualHom
  dualHom_dualHom moduleAct_true_eq le_normalizer_centerOf mix mix_apply exists_mix_of_commute)
open CFSG.Quasithin.H13.Ch4 (dact)
open scoped Matrix commutatorElement

variable {G : Type} [Group G] [Finite G]

section Pairing

variable {Q L W₁ W₂ : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F}
  {βU : ↥(centerOf Q) →* Multiplicative (Fin 3 → F)}
  {β₁ : ↥W₁ →* Multiplicative (Fin 3 → F)} {β₂ : ↥W₂ →* Multiplicative (Fin 3 → F)}

theorem burnsideC135_pairing (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ centerOf Q) :
    ∃ B : (Fin 3 → F) → (Fin 3 → F) → (Fin 3 → F),
      (∀ (a : ↥W₁) (b : ↥W₂) (u : ↥(centerOf Q)), (u : G) = a * b * (a : G)⁻¹ * (b : G)⁻¹ →
        Multiplicative.toAdd (βU u) =
          B (Multiplicative.toAdd (β₁ a)) (Multiplicative.toAdd (β₂ b))) ∧
      (∀ (γ : Matrix.SpecialLinearGroup (Fin 3) F) (x z : Fin 3 → F),
        B (((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)
          (((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z) =
        (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ B x z) ∧
      (∀ (c : F) (x : Fin 3 → F), B x (c • x) = 0) ∧
      (∀ x z z', B x (z + z') = B x z + B x z') ∧
      (∀ x x' z, B (x + x') z = B x z + B x' z) := by
  classical
  have hLU : L ≤ Subgroup.normalizer (centerOf Q : Set G) :=
    burnsideC135_le_normalizer_centerOf hD.normQ
  let cm : ↥W₁ → ↥W₂ → ↥(centerOf Q) := fun a b =>
    ⟨(a : G) * b * (a : G)⁻¹ * (b : G)⁻¹, hcomm _ (hD.le_Q₁ a.2) _ (hD.le_Q₂ b.2)⟩
  have hwell : ∀ (a a' : ↥W₁) (b b' : ↥W₂), β₁ a = β₁ a' → β₂ b = β₂ b' → cm a b = cm a' b' := by
    intro a a' b b' ha hb
    have hka : a⁻¹ * a' ∈ β₁.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, ha, inv_mul_cancel]
    have hkb : b⁻¹ * b' ∈ β₂.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hb, inv_mul_cancel]
    rw [hD.dual₁_ker, Subgroup.mem_subgroupOf] at hka
    rw [hD.dual₂_ker, Subgroup.mem_subgroupOf] at hkb
    have hka' : (a : G)⁻¹ * a' ∈ centerOf Q := by simpa using hka
    have hkb' : (b : G)⁻¹ * b' ∈ centerOf Q := by simpa using hkb
    apply Subtype.ext
    show (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ = (a' : G) * b' * (a' : G)⁻¹ * (b' : G)⁻¹
    have ha' : (a' : G) = a * ((a : G)⁻¹ * a') := by group
    have hb' : (b' : G) = b * ((b : G)⁻¹ * b') := by group
    rw [ha', hb']
    exact (burnsideC135_commutator_mul_central (burnsideC135_U_comm hka' (hD.le_Q₂ b.2))
      (burnsideC135_U_comm hkb' (hD.le_Q₁ a.2))
      (burnsideC135_U_comm hkb' (hD.le_Q₁ (hD.le₁ hka')))).symm
  have hcmL : ∀ (l : ↥L) (a : ↥W₁) (b : ↥W₂),
      ((cm ⟨(l : G) * a * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hD.norm₁ l.2) _).mp a.2⟩
        ⟨(l : G) * b * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hD.norm₂ l.2) _).mp b.2⟩ :
          ↥(centerOf Q)) : G) = (l : G) * (cm a b) * (l : G)⁻¹ := by
    intro l a b
    show (l : G) * a * (l : G)⁻¹ * ((l : G) * b * (l : G)⁻¹) * ((l : G) * a * (l : G)⁻¹)⁻¹ *
      ((l : G) * b * (l : G)⁻¹)⁻¹ = (l : G) * ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) * (l : G)⁻¹
    group
  let s₁ : (Fin 3 → F) → ↥W₁ := fun x => Function.surjInv hD.dual₁_onto (Multiplicative.ofAdd x)
  let s₂ : (Fin 3 → F) → ↥W₂ := fun z => Function.surjInv hD.dual₂_onto (Multiplicative.ofAdd z)
  have hs₁ : ∀ x, β₁ (s₁ x) = Multiplicative.ofAdd x := fun x => Function.surjInv_eq _ _
  have hs₂ : ∀ z, β₂ (s₂ z) = Multiplicative.ofAdd z := fun z => Function.surjInv_eq _ _
  let Bf : (Fin 3 → F) → (Fin 3 → F) → (Fin 3 → F) := fun x z =>
    Multiplicative.toAdd (βU (cm (s₁ x) (s₂ z)))
  have hBf : ∀ (a : ↥W₁) (b : ↥W₂), Bf (Multiplicative.toAdd (β₁ a)) (Multiplicative.toAdd (β₂ b)) =
      Multiplicative.toAdd (βU (cm a b)) := by
    intro a b
    show Multiplicative.toAdd (βU (cm (s₁ _) (s₂ _))) = _
    rw [hwell (s₁ _) a (s₂ _) b (by rw [hs₁]; rfl) (by rw [hs₂]; rfl)]
  refine ⟨Bf, fun a b u hu => ?_, fun γ x z => ?_, fun c x => ?_, fun x z z' => ?_,
    fun x x' z => ?_⟩
  · have e : u = cm a b := Subtype.ext hu
    rw [e, hBf]
  · obtain ⟨l, hl⟩ := hD.alpha_onto γ
    set a' : ↥W₁ := ⟨(l : G) * s₁ x * (l : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hD.norm₁ l.2) _).mp (s₁ x).2⟩ with ha'
    set b' : ↥W₂ := ⟨(l : G) * s₂ z * (l : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hD.norm₂ l.2) _).mp (s₂ z).2⟩ with hb'
    have h1 : Multiplicative.toAdd (β₁ a') =
        ((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x := by
      rw [hD.dual₁_act l (s₁ x) a' rfl, hs₁, hl, coe_dualHom]
      rfl
    have h2 : Multiplicative.toAdd (β₂ b') =
        ((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z := by
      rw [hD.dual₂_act l (s₂ z) b' rfl, hs₂, hl, coe_dualHom]
      rfl
    rw [← h1, ← h2, hBf]
    have hmemU : (l : G) * (cm (s₁ x) (s₂ z)) * (l : G)⁻¹ ∈ centerOf Q :=
      (Subgroup.mem_normalizer_iff.mp (hLU l.2) _).mp (cm (s₁ x) (s₂ z)).2
    have e1 : cm a' b' = ⟨_, hmemU⟩ := Subtype.ext (hcmL l (s₁ x) (s₂ z))
    rw [e1, hD.natU_act l (cm (s₁ x) (s₂ z)) ⟨_, hmemU⟩ rfl, hl]
  ·
    have hBfeq : ∀ (γ : Matrix.SpecialLinearGroup (Fin 3) F) (x z : Fin 3 → F),
        Bf (((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)
          (((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z) =
        (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ Bf x z := by
      intro γ x z
      obtain ⟨l, hl⟩ := hD.alpha_onto γ
      set a' : ↥W₁ := ⟨(l : G) * s₁ x * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hD.norm₁ l.2) _).mp (s₁ x).2⟩ with ha'
      set b' : ↥W₂ := ⟨(l : G) * s₂ z * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hD.norm₂ l.2) _).mp (s₂ z).2⟩ with hb'
      have h1 : Multiplicative.toAdd (β₁ a') =
          ((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x := by
        rw [hD.dual₁_act l (s₁ x) a' rfl, hs₁, hl, coe_dualHom]
        rfl
      have h2 : Multiplicative.toAdd (β₂ b') =
          ((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z := by
        rw [hD.dual₂_act l (s₂ z) b' rfl, hs₂, hl, coe_dualHom]
        rfl
      rw [← h1, ← h2, hBf]
      have hmemU : (l : G) * (cm (s₁ x) (s₂ z)) * (l : G)⁻¹ ∈ centerOf Q :=
        (Subgroup.mem_normalizer_iff.mp (hLU l.2) _).mp (cm (s₁ x) (s₂ z)).2
      have e1 : cm a' b' = ⟨_, hmemU⟩ := Subtype.ext (hcmL l (s₁ x) (s₂ z))
      rw [e1, hD.natU_act l (cm (s₁ x) (s₂ z)) ⟨_, hmemU⟩ rfl, hl]
    revert x
    refine CFSG.Quasithin.H13.Ch4.C135.eq_zero_of_dual_equivariant (fun x => Bf x (c • x))
      fun γ v => ?_
    show Bf _ (c • _) = _
    rw [← Matrix.mulVec_smul, hBfeq]
  ·
    have hmul : β₂ (s₂ z * s₂ z') = β₂ (s₂ (z + z')) := by
      rw [map_mul, hs₂, hs₂, hs₂]
      rfl
    have h1 : Bf x (z + z') = Multiplicative.toAdd (βU (cm (s₁ x) (s₂ z * s₂ z'))) := by
      show Multiplicative.toAdd (βU (cm (s₁ x) (s₂ (z + z')))) = _
      rw [hwell (s₁ x) (s₁ x) (s₂ (z + z')) (s₂ z * s₂ z') rfl hmul.symm]
    have hc' : (cm (s₁ x) (s₂ z') : G) * s₂ z = s₂ z * cm (s₁ x) (s₂ z') :=
      burnsideC135_U_comm (cm (s₁ x) (s₂ z')).2 (hD.le_Q₂ (s₂ z).2)
    have h2 : cm (s₁ x) (s₂ z * s₂ z') = cm (s₁ x) (s₂ z) * cm (s₁ x) (s₂ z') := by
      apply Subtype.ext
      show (s₁ x : G) * (s₂ z * s₂ z') * (s₁ x : G)⁻¹ * ((s₂ z : G) * s₂ z')⁻¹ =
        (s₁ x : G) * s₂ z * (s₁ x : G)⁻¹ * (s₂ z : G)⁻¹ *
          ((s₁ x : G) * s₂ z' * (s₁ x : G)⁻¹ * (s₂ z' : G)⁻¹)
      have hc'' : ((s₁ x : G) * s₂ z' * (s₁ x : G)⁻¹ * (s₂ z' : G)⁻¹) * s₂ z =
          s₂ z * ((s₁ x : G) * s₂ z' * (s₁ x : G)⁻¹ * (s₂ z' : G)⁻¹) := hc'
      calc (s₁ x : G) * (s₂ z * s₂ z') * (s₁ x : G)⁻¹ * ((s₂ z : G) * s₂ z')⁻¹ =
            (s₁ x : G) * s₂ z * (s₁ x : G)⁻¹ * (s₂ z : G)⁻¹ *
              (((s₂ z : G) * ((s₁ x : G) * s₂ z' * (s₁ x : G)⁻¹ * (s₂ z' : G)⁻¹)) *
                (s₂ z : G)⁻¹) := by group
        _ = (s₁ x : G) * s₂ z * (s₁ x : G)⁻¹ * (s₂ z : G)⁻¹ *
              ((((s₁ x : G) * s₂ z' * (s₁ x : G)⁻¹ * (s₂ z' : G)⁻¹) * s₂ z) *
                (s₂ z : G)⁻¹) := by rw [hc'']
        _ = _ := by group
    rw [h1, h2, map_mul, toAdd_mul]
  ·
    have hmul : β₁ (s₁ x * s₁ x') = β₁ (s₁ (x + x')) := by
      rw [map_mul, hs₁, hs₁, hs₁]
      rfl
    have h1 : Bf (x + x') z = Multiplicative.toAdd (βU (cm (s₁ x * s₁ x') (s₂ z))) := by
      show Multiplicative.toAdd (βU (cm (s₁ (x + x')) (s₂ z))) = _
      rw [hwell (s₁ (x + x')) (s₁ x * s₁ x') (s₂ z) (s₂ z) hmul.symm rfl]
    have hc' : (cm (s₁ x') (s₂ z) : G) * s₁ x = s₁ x * cm (s₁ x') (s₂ z) :=
      burnsideC135_U_comm (cm (s₁ x') (s₂ z)).2 (hD.le_Q₁ (s₁ x).2)
    have h2 : cm (s₁ x * s₁ x') (s₂ z) = cm (s₁ x) (s₂ z) * cm (s₁ x') (s₂ z) := by
      apply Subtype.ext
      show ((s₁ x : G) * s₁ x') * s₂ z * ((s₁ x : G) * s₁ x')⁻¹ * (s₂ z : G)⁻¹ =
        (s₁ x : G) * s₂ z * (s₁ x : G)⁻¹ * (s₂ z : G)⁻¹ *
          ((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹)
      have hc'' : ((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹) * s₁ x =
          s₁ x * ((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹) := hc'
      have hc3 : ((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹) *
          ((s₁ x : G) * s₂ z * (s₁ x : G)⁻¹ * (s₂ z : G)⁻¹) =
          ((s₁ x : G) * s₂ z * (s₁ x : G)⁻¹ * (s₂ z : G)⁻¹) *
            ((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹) :=
        burnsideC135_U_comm (cm (s₁ x') (s₂ z)).2
          (hcomm _ (hD.le_Q₁ (s₁ x).2) _ (hD.le_Q₂ (s₂ z).2)).1
      have hc4 : ((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹) * s₂ z =
          s₂ z * ((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹) :=
        burnsideC135_U_comm (cm (s₁ x') (s₂ z)).2 (hD.le_Q₂ (s₂ z).2)
      calc ((s₁ x : G) * s₁ x') * s₂ z * ((s₁ x : G) * s₁ x')⁻¹ * (s₂ z : G)⁻¹ =
            (s₁ x : G) * (((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹) * s₂ z) *
              (s₁ x : G)⁻¹ * (s₂ z : G)⁻¹ := by group
        _ = (s₁ x : G) * (s₂ z * ((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹)) *
              (s₁ x : G)⁻¹ * (s₂ z : G)⁻¹ := by rw [hc4]
        _ = (s₁ x : G) * s₂ z * (((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹) *
              (s₁ x : G)⁻¹) * (s₂ z : G)⁻¹ := by group
        _ = (s₁ x : G) * s₂ z * ((s₁ x : G)⁻¹ *
              ((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹)) * (s₂ z : G)⁻¹ := by
            congr 2
            calc ((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹) * (s₁ x : G)⁻¹ =
                  (s₁ x : G)⁻¹ * ((s₁ x : G) *
                    ((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹)) * (s₁ x : G)⁻¹ := by
                  group
              _ = (s₁ x : G)⁻¹ * (((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹) *
                    (s₁ x : G)) * (s₁ x : G)⁻¹ := by rw [← hc'']
              _ = _ := by group
        _ = ((s₁ x : G) * s₂ z * (s₁ x : G)⁻¹ * (s₂ z : G)⁻¹) *
              (s₂ z * ((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹) * (s₂ z : G)⁻¹) := by
            group
        _ = ((s₁ x : G) * s₂ z * (s₁ x : G)⁻¹ * (s₂ z : G)⁻¹) *
              ((s₁ x' : G) * s₂ z * (s₁ x' : G)⁻¹ * (s₂ z : G)⁻¹) := by
            rw [← hc4]; group
    rw [h1, h2, map_mul, toAdd_mul]

theorem burnsideC135_comm_cross (hF : Fintype.card F = 2)
    (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ centerOf Q)
    (a : ↥W₁) (b : ↥W₂) (u : ↥(centerOf Q)) (hu : (u : G) = a * b * (a : G)⁻¹ * (b : G)⁻¹) :
    Multiplicative.toAdd (βU u) = Multiplicative.toAdd (β₁ a) ⨯₃ Multiplicative.toAdd (β₂ b) := by
  classical
  have h01 : ∀ c : F, c = 0 ∨ c = 1 := by
    intro c
    by_contra hc
    push Not at hc
    have h3 : 2 < Fintype.card F :=
      Fintype.two_lt_card_iff.mpr ⟨0, 1, c, zero_ne_one, hc.1.symm, hc.2.symm⟩
    omega
  obtain ⟨B, hB, hBeq, hB0, hadd₂, hadd₁⟩ := burnsideC135_pairing hD hcomm
  have hBz : ∀ z, B 0 z = 0 := fun z => by
    have := hadd₁ 0 0 z
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hBz' : ∀ x, B x 0 = 0 := fun x => by
    have := hadd₂ x 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hsmul₁ : ∀ (c : F) x y, B (c • x) y = c • B x y := by
    intro c x y
    rcases h01 c with rfl | rfl
    · rw [zero_smul, zero_smul, hBz]
    · rw [one_smul, one_smul]
  have hsmul₂ : ∀ (c : F) x y, B x (c • y) = c • B x y := by
    intro c x y
    rcases h01 c with rfl | rfl
    · rw [zero_smul, zero_smul, hBz']
    · rw [one_smul, one_smul]
  obtain ⟨μ, hμ⟩ := burnsideC135_eq_smul_cross B hadd₁ hadd₂ hsmul₁ hsmul₂
    (fun x => by simpa using hB0 1 x) hBeq
  have hμ1 : μ = 1 := by
    rcases h01 μ with h | h
    · exfalso
      obtain ⟨w, hw⟩ := hD.dual₁_onto (Multiplicative.ofAdd (Pi.single 0 1))
      obtain ⟨y, hy⟩ := hD.dual₂_onto (Multiplicative.ofAdd (Pi.single 1 1))
      have hwU : (w : G) ∉ centerOf Q := by
        intro h'
        have h1 : w ∈ β₁.ker := by
          rw [hD.dual₁_ker, Subgroup.mem_subgroupOf]
          exact h'
        rw [MonoidHom.mem_ker, hw] at h1
        have := congrFun (congrArg Multiplicative.toAdd h1) 0
        simp at this
      have hwy : (w : G) * y = y * w := by
        have hmem := hcomm _ (hD.le_Q₁ w.2) _ (hD.le_Q₂ y.2)
        have h1 := hB w y ⟨_, hmem⟩ rfl
        rw [hμ, h, zero_smul] at h1
        have h2 : βU ⟨_, hmem⟩ = βU 1 := by
          rw [map_one]
          exact Multiplicative.toAdd.injective h1
        have h3 := congrArg Subtype.val (burnsideC135_βU_injective hD h2)
        have h4 : (w : G) * y * (w : G)⁻¹ * (y : G)⁻¹ = 1 := h3
        calc (w : G) * y = ((w : G) * y * (w : G)⁻¹ * (y : G)⁻¹) * (y * w) := by group
          _ = y * w := by rw [h4, one_mul]
      obtain ⟨c, hc⟩ := (burnsideC135_commute_iff hD hcomm w hwU y).mp hwy
      rw [hw, hy] at hc
      have := congrFun hc 1
      simp at this
    · exact h
  rw [hB a b u hu, hμ, hμ1, one_smul]

end Pairing

section Mix

variable {X L : Subgroup G} {F : Type} [Field F] {α : ↥L →* ↥(StatedSL 3 F)}

theorem burnsideC135_exists_mix (hα : IsModO2Surj L α) (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G))
    {β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F)} (hβs : Function.Surjective β)
    (hβk : β.ker = (centerOf (c134Q X L)).subgroupOf (c134Q X L))
    (hβeq : ∀ (a : ↥L) (u v : ↥(c134Q X L)), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        (moduleAct true (α a : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i))
    {t : G} (ht : t ∈ pCoreOf 2 X) :
    ∃ c : Matrix (Fin 2) (Fin 2) F, ∀ (q q' : ↥(c134Q X L)), (q' : G) = t * q * t⁻¹ →
      Multiplicative.toAdd (β q') = mix c (Multiplicative.toAdd (β q)) := by
  classical
  have hXQ : X ≤ Subgroup.normalizer (c134Q X L : Set G) := CFSG.Quasithin.H13.Ch4.le_normalizer_c134Q hXL
  have htN : t ∈ Subgroup.normalizer (c134Q X L : Set G) := hXQ (pCoreOf_le 2 X ht)
  have hXU : X ≤ Subgroup.normalizer (centerOf (c134Q X L) : Set G) := le_normalizer_centerOf hXQ
  have htU := hXU (pCoreOf_le 2 X ht)
  have hcong : ∀ {g : G} (hg : g ∈ Subgroup.normalizer (c134Q X L : Set G)),
      g ∈ Subgroup.normalizer (centerOf (c134Q X L) : Set G) → ∀ q q' : ↥(c134Q X L), β q = β q' →
        β (cnj hg q) = β (cnj hg q') := by
    intro g hg hgU q q' h
    have h1 : q⁻¹ * q' ∈ β.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at h1
    have h2 : (cnj hg q)⁻¹ * cnj hg q' ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      have e : (((cnj hg q)⁻¹ * cnj hg q' : ↥(c134Q X L)) : G) = g * (((q⁻¹ * q' : ↥(c134Q X L)) : G)) * g⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_cnj]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp hgU _).mp h1
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  choose sec hsec using hβs
  let T : (Fin 2 → Fin 3 → F) →+ (Fin 2 → Fin 3 → F) :=
    { toFun := fun v => Multiplicative.toAdd (β (cnj htN (sec (Multiplicative.ofAdd v))))
      map_zero' := by
        have h0 : β (sec (Multiplicative.ofAdd 0)) = β 1 := by rw [hsec, map_one]; rfl
        rw [hcong htN htU _ _ h0]
        have e : cnj htN (1 : ↥(c134Q X L)) = 1 := Subtype.ext (by simp [coe_cnj])
        rw [e, map_one]
        rfl
      map_add' := fun v w => by
        have h1 : β (sec (Multiplicative.ofAdd (v + w))) =
            β (sec (Multiplicative.ofAdd v) * sec (Multiplicative.ofAdd w)) := by
          rw [hsec, map_mul, hsec, hsec]
          rfl
        have e : cnj htN (sec (Multiplicative.ofAdd v) * sec (Multiplicative.ofAdd w)) =
            cnj htN (sec (Multiplicative.ofAdd v)) * cnj htN (sec (Multiplicative.ofAdd w)) :=
          Subtype.ext (by simp only [coe_cnj, Subgroup.coe_mul]; group)
        show Multiplicative.toAdd (β (cnj htN (sec (Multiplicative.ofAdd (v + w))))) = _
        rw [hcong htN htU _ _ h1, e, map_mul, toAdd_mul] }
  have hT : ∀ q : ↥(c134Q X L), T (Multiplicative.toAdd (β q)) = Multiplicative.toAdd (β (cnj htN q)) := by
    intro q
    show Multiplicative.toAdd (β (cnj htN (sec (Multiplicative.ofAdd (Multiplicative.toAdd
      (β q)))))) = _
    rw [hcong htN htU _ q (by rw [hsec]; rfl)]
  have hρ := slNat_surjective hα.1
  have hdact : ∀ (g : ↥L) (q : ↥(c134Q X L)) (hg : (g : G) ∈ Subgroup.normalizer (c134Q X L : Set G)),
      Multiplicative.toAdd (β (cnj hg q)) =
        dact ((dualHom (slNat α g) : Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) (Multiplicative.toAdd (β q)) := by
    intro g q hg
    funext i
    rw [hβeq g q (cnj hg q) rfl i, moduleAct_true_eq]
    rfl
  obtain ⟨c, hc⟩ := exists_mix_of_commute T (fun γ v => by
    obtain ⟨g, hg⟩ := hρ (dualHom γ)
    have hγ : dualHom (slNat α g) = γ := by rw [hg, dualHom_dualHom]
    have hgN : (g : G) ∈ Subgroup.normalizer (c134Q X L : Set G) := hXQ (hLX g.2)
    obtain ⟨q, rfl⟩ : ∃ q : ↥(c134Q X L), Multiplicative.toAdd (β q) = v :=
      ⟨sec (Multiplicative.ofAdd v), by rw [hsec]; rfl⟩
    have h1 : dact ((γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
        (Multiplicative.toAdd (β q)) = Multiplicative.toAdd (β (cnj hgN q)) := by
      rw [hdact g q hgN, hγ]
    rw [h1, hT, hT]
    have hcQ : t * g * t⁻¹ * (g : G)⁻¹ ∈ c134Q X L := by
      have h2 := Subgroup.commutator_mem_commutator ht g.2
      rwa [commutatorElement_def] at h2
    have e : cnj htN (cnj hgN q) = ⟨t * g * t⁻¹ * (g : G)⁻¹, hcQ⟩ *
        cnj hgN (cnj htN q) * ⟨t * g * t⁻¹ * (g : G)⁻¹, hcQ⟩⁻¹ :=
      Subtype.ext (by simp only [coe_cnj, Subgroup.coe_mul, Subgroup.coe_inv]; group)
    have e2 : β (⟨t * g * t⁻¹ * (g : G)⁻¹, hcQ⟩ * cnj hgN (cnj htN q) *
        ⟨t * g * t⁻¹ * (g : G)⁻¹, hcQ⟩⁻¹) = β (cnj hgN (cnj htN q)) := by
      rw [map_mul, map_mul, map_inv, mul_comm (β ⟨_, hcQ⟩) (β (cnj hgN (cnj htN q))), mul_assoc,
        mul_inv_cancel, mul_one]
    rw [e, e2, hdact g (cnj htN q) hgN, hγ])
  refine ⟨c, fun q q' hq' => ?_⟩
  have e : q' = cnj htN q := Subtype.ext (by rw [coe_cnj]; exact hq')
  rw [e, ← hT, hc]

end Mix

end CFSG.ASVolI

end
