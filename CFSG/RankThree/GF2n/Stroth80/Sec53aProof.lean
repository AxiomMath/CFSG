module

public import CFSG.RankThree.GF2n.Stroth80.Sec10CardU
public import CFSG.RankThree.GF2n.Stroth80.Sec34CaseB
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClConj
public import CFSG.RankThree.GF2n.Stroth80.Sec53cProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Img

variable {QF Vc : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem quadModel_img_inf (M₀ : Tim79.QuadModel QF Vc K γ) {S T : Subgroup G}
    (hVS : Vc ≤ S) (hVT : Vc ≤ T) (hSQ : S ≤ QF) (hTQ : T ≤ QF) :
    M₀.img (S ⊓ T) = M₀.img S ⊓ M₀.img T := by
  refine le_antisymm (fun e he => ⟨M₀.img_mono inf_le_left he,
    M₀.img_mono inf_le_right he⟩) ?_
  rintro e ⟨heS, heT⟩
  obtain ⟨x, hxS, hxQ, hx⟩ := (Tim79.QuadModel.mem_img M₀).mp heS
  obtain ⟨y, hyT, hyQ, hy⟩ := (Tim79.QuadModel.mem_img M₀).mp heT
  have hyx : y⁻¹ * x ∈ Vc :=
    (Tim79.QuadModel.pi_eq_iff M₀ hyQ hxQ).mp (by rw [hy, hx])
  have hxT : x ∈ T := by
    have e : x = y * (y⁻¹ * x) := by group
    rw [e]
    exact T.mul_mem hyT (hVT hyx)
  exact (Tim79.QuadModel.mem_img M₀).mpr ⟨x, ⟨hxS, hxT⟩, hxQ, hx⟩

end Img

theorem Ctx.img_vone_smul (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {C : Subgroup G} (hcC : Ctx M Q Z C) (hnoC : NoA2 Q Z (LB M Q C))
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) :
    ∀ (c : K) (e : M₀.E),
      e ∈ M₀.img (Vone Q B C (Vt M (LB M Q B) B Z t)) →
        c • e ∈ M₀.img (Vone Q B C (Vt M (LB M Q B) B Z t)) := by
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hZQB : Z ≤ Q ⊓ QB B := le_inf hZQ hc.Z_le_QB.1
  have hZQC : Z ≤ Q ⊓ QB C := le_inf hZQ hcC.Z_le_QB.1
  have hA1Q : Q ⊓ QB B ≤ Q := inf_le_left
  have hA2Q : Q ⊓ QB C ≤ Q := inf_le_left
  have hA1 : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Q ⊓ QB B) →
      c • e ∈ M₀.img (Q ⊓ QB B) := by
    intro c e he
    exact (hc.mem_imgQInfQB_iff (X := B) hs.width hs.n_gt hs.noA2 hD (c • e)).mp
      ((imgQInfQB M₀ B).smul_mem c
        ((hc.mem_imgQInfQB_iff (X := B) hs.width hs.n_gt hs.noA2 hD e).mpr he))
  have hA2 : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Q ⊓ QB C) →
      c • e ∈ M₀.img (Q ⊓ QB C) := by
    intro c e he
    exact (hcC.mem_imgQInfQB_iff (X := C) hs.width hs.n_gt hnoC hD (c • e)).mp
      ((imgQInfQB M₀ C).smul_mem c
        ((hcC.mem_imgQInfQB_iff (X := C) hs.width hs.n_gt hnoC hD e).mpr he))
  have hVK : ∀ (c : K) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V :=
    fun c e he => hc.smul_mem_img_Vt hD t c he
  have hS1 : ∀ (c : K) (e : M₀.E), e ∈ M₀.img ((Q ⊓ QB B) ⊔ V) →
      c • e ∈ M₀.img ((Q ⊓ QB B) ⊔ V) := by
    intro c e he
    rw [quadModel_img_sup M₀ hA1Q hVQ] at he ⊢
    obtain ⟨a, ha, v, hv, rfl⟩ := AddSubgroup.mem_sup.mp he
    rw [smul_add]
    exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left (hA1 c a ha))
      (AddSubgroup.mem_sup_right (hVK c v hv))
  have hS2 : ∀ (c : K) (e : M₀.E), e ∈ M₀.img ((Q ⊓ QB C) ⊔ V) →
      c • e ∈ M₀.img ((Q ⊓ QB C) ⊔ V) := by
    intro c e he
    rw [quadModel_img_sup M₀ hA2Q hVQ] at he ⊢
    obtain ⟨a, ha, v, hv, rfl⟩ := AddSubgroup.mem_sup.mp he
    rw [smul_add]
    exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left (hA2 c a ha))
      (AddSubgroup.mem_sup_right (hVK c v hv))
  intro c e he
  have hinf := quadModel_img_inf M₀ (S := (Q ⊓ QB B) ⊔ V) (T := (Q ⊓ QB C) ⊔ V)
    (sec39_Z_le_Vt.trans (le_sup_right : V ≤ (Q ⊓ QB B) ⊔ V))
    (sec39_Z_le_Vt.trans (le_sup_right : V ≤ (Q ⊓ QB C) ⊔ V))
    (sup_le hA1Q hVQ) (sup_le hA2Q hVQ)
  rw [Vone, hinf] at he ⊢
  exact ⟨hS1 c e he.1, hS2 c e he.2⟩

theorem Ctx.card_Wt_mul_card_vone (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {C : Subgroup G} (hcC : Ctx M Q Z C) (hnoC : NoA2 Q Z (LB M Q C)) :
    Nat.card ↥(Wt Q (Vone Q B C (Vt M (LB M Q B) B Z t))) *
        Nat.card ↥(Vone Q B C (Vt M (LB M Q B) B Z t)) = Nat.card Q * Nat.card Z := by
  obtain ⟨K, iF, iFin, iChar, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  letI := iF
  letI := iFin
  letI := iChar
  exact card_Wt_mul_card_eq_of_gammaReg M₀ hD.reg
    (vone_le_Q (hc.Vt_le_Q t)) Z_le_vone (hc.img_vone_smul hs hcC hnoC hD)

theorem Ctx.card_Wt_eq_card_Wt_vone_mul (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {C : Subgroup G} (hcC : Ctx M Q Z C) (hnoC : NoA2 Q Z (LB M Q C))
    (hV1 : Nat.card ↥(Vone Q B C (Vt M (LB M Q B) B Z t)) =
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z) :
    Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) =
      Nat.card ↥(Wt Q (Vone Q B C (Vt M (LB M Q B) B Z t))) * Nat.card Z := by
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set V1 : Subgroup G := Vone Q B C V with hV1def
  set W : Subgroup G := Wt Q V with hWdef
  set W1 : Subgroup G := Wt Q V1 with hW1def
  have hW : Nat.card ↥W * Nat.card ↥V = Nat.card Q * Nat.card Z :=
    hc.card_Wt_mul_card_Vt t
  have hW1 : Nat.card ↥W1 * Nat.card ↥V1 = Nat.card Q * Nat.card Z :=
    hc.card_Wt_mul_card_vone hs hcC hnoC
  have hVpos : 0 < Nat.card ↥V := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hVpos ?_
  calc Nat.card ↥W * Nat.card ↥V
      = Nat.card Q * Nat.card Z := hW
    _ = Nat.card ↥W1 * Nat.card ↥V1 := hW1.symm
    _ = Nat.card ↥W1 * (Nat.card ↥V * Nat.card Z) := by rw [hV1]
    _ = Nat.card ↥W1 * Nat.card Z * Nat.card ↥V := by ring

theorem stroth53a_of_vone_card_odd
    (hVone : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ (C V V₁ : Subgroup G), C = conjSubgroup r B → V = Vt M (LB M Q B) B Z t →
        V₁ = Vone Q B C V → Nat.card ↥V₁ = Nat.card V * Nat.card Z)
    (hOdd : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t → Odd n) :
    Stroth53aStatement := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane C V W V₁ W₁ hC hV hW hV1 hW1
  subst hC
  subst hV
  subst hW
  subst hV1
  subst hW1
  refine ⟨hVone G M Q Z B hc n t hs hsp r hr hplane (conjSubgroup r B) (Vt M (LB M Q B) B Z t)
      (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) rfl rfl rfl, ?_,
    hOdd G M Q Z B hc n t hs hsp r hr hplane⟩
  exact Ctx.card_Wt_eq_card_Wt_vone_mul hc hs (hc.conj_of_mem (hc.Rt_le_M t hr))
    (hc.noA2_conj hs.noA2 (hc.Rt_le_M t hr))
    (hVone G M Q Z B hc n t hs hsp r hr hplane (conjSubgroup r B) (Vt M (LB M Q B) B Z t)
      (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) rfl rfl rfl)

end CFSG.RankThree.GF2n.Stroth80
