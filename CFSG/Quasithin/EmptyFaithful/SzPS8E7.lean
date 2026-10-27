module

public import CFSG.Quasithin.EmptyFaithful.SzPS8E7Bor
public import CFSG.Quasithin.EmptyFaithful.SzPS8Frame
public import CFSG.Quasithin.EmptyFaithful.SzPS8AxA
public import CFSG.Quasithin.EmptyFaithful.SzPS8A5
public import CFSG.Quasithin.EmptyFaithful.SzPS8Defs
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.Adapters.GeneralizedFitting
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Bridge
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Class
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveComponents
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.Quasithin.EmptyFaithful.SzPS8E7Lift
public import CFSG.Quasithin.EmptyFaithful.SzPS8Model
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4E9

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.GoldS146R CFSG.LieType.BorelTits
open CFSG.Quasithin.G11
open scoped MatrixGroups

namespace SzPS8

section Helpers

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem inH_sup_T (hyp : Hyp1421 G T M) (h : Hyp1281Two G T M (yOfL22 T M)) {Y : Subgroup G}
    (hYH : Y ≤ mcOf T) : InH T (Y ⊔ T) := by
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have hsylH : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH
  have hH : pCoreOf 2 (mcOf T) ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hyp.mc_max.1
  refine ⟨le_sup_right, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 (Y ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_two_le_of_isSylowTwoOf hsylH).trans le_sup_right)
      ((sup_le hYH hTH).trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  intro h0
  exact hH (le_bot_iff.mp (h0 ▸ h1))

theorem isSylowTwoOf_inf_T (hyp : Hyp1421 G T M) {K₀ : Subgroup G}
    (hTN : T ≤ Subgroup.normalizer (K₀ : Set G)) :
    IsSylowTwoOf (T ⊓ K₀) K₀ := by
  have hsylLT : IsSylowTwoOf T (K₀ ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right
  have hsub : IsSubnormal K₀ (K₀ ⊔ T) :=
    IsSubnormal.step le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTN)) (IsSubnormal.refl _)
  exact A312.isSylowTwoOf_inf_of_subnormal hsub hsylLT

theorem range_rhoRes (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M) {K₀ : Subgroup G}
    (hK₀H : K₀ ≤ mcOf T) :
    (rhoRes h D hK₀H).range =
      ((K₀.subgroupOf (mcOf T)).map (rhoΓ h D)).map (D.img (mcOf T)).subtype := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨rhoΓ h D (Subgroup.inclusion hK₀H y), ⟨Subgroup.inclusion hK₀H y, y.2, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩

theorem sImg_le_range (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M) {K₀ : Subgroup G}
    (hK₀H : K₀ ≤ mcOf T) : sImg h D hK₀H ≤ (rhoRes h D hK₀H).range :=
  Subgroup.map_le_range _ _

theorem isPGroup_sImg (hyp : Hyp1421 G T M) (h : Hyp1281Two G T M (yOfL22 T M))
    (D : HatModel T M) {K₀ : Subgroup G} (hK₀H : K₀ ≤ mcOf T) :
    IsPGroup 2 ↥(sImg h D hK₀H) := by
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have hsylH : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH
  have h1 : IsPGroup 2 ↥(T ⊓ K₀) := hsylH.2.1.to_le inf_le_left
  have h2 : IsPGroup 2 ↥((T ⊓ K₀).subgroupOf K₀) :=
    h1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  exact h2.map (rhoRes h D hK₀H)

theorem relIndex_sImg_odd (hyp : Hyp1421 G T M) (h : Hyp1281Two G T M (yOfL22 T M))
    (D : HatModel T M) {K₀ : Subgroup G} (hK₀H : K₀ ≤ mcOf T)
    (hTN : T ≤ Subgroup.normalizer (K₀ : Set G))
    (hker : ∀ x : ↥(mcOf T), (x : G) ∈ K₀ → S143V.rhoH h D x = 1 → (x : G) ∈ T) :
    ¬ 2 ∣ (sImg h D hK₀H).relIndex (rhoRes h D hK₀H).range := by
  have hS := isSylowTwoOf_inf_T hyp hTN
  have h1 := relIndex_eq_relIndex_map (rhoRes h D hK₀H) (T₀ := (T ⊓ K₀).subgroupOf K₀)
    (K := ⊤) le_top (fun k _ hk => Subgroup.mem_subgroupOf.mpr
      ⟨hker (Subgroup.inclusion hK₀H k) k.2 hk, k.2⟩)
  rw [Subgroup.relIndex_top_right, Subgroup.map_top] at h1
  have h2 : (T ⊓ K₀).relIndex K₀ = (sImg h D hK₀H).relIndex (rhoRes h D hK₀H).range := h1
  intro hd
  have h3 : 2 ∣ (T ⊓ K₀).relIndex K₀ := h2 ▸ hd
  exact hS.2.2 h3

theorem conj_mem_sImg (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M) {K₀ : Subgroup G}
    (hK₀H : K₀ ≤ mcOf T) (hTN : T ≤ Subgroup.normalizer (K₀ : Set G)) {t : G} (ht : t ∈ T)
    {y : D.V ≃ₗ[ZMod 2] D.V} (hy : y ∈ sImg h D hK₀H) :
    S143V.rhoH h D ⟨t, h.almostSpecialHyp_g1.T_le_H ht⟩ * y *
      (S143V.rhoH h D ⟨t, h.almostSpecialHyp_g1.T_le_H ht⟩)⁻¹ ∈ sImg h D hK₀H := by
  obtain ⟨s, hs, rfl⟩ := hy
  have hs' : (s : G) ∈ T ⊓ K₀ := Subgroup.mem_subgroupOf.mp hs
  have hconj : t * (s : G) * t⁻¹ ∈ K₀ :=
    (Subgroup.mem_normalizer_iff.mp (hTN ht) (s : G)).mp hs'.2
  refine ⟨⟨t * (s : G) * t⁻¹, hconj⟩, Subgroup.mem_subgroupOf.mpr
    ⟨T.mul_mem (T.mul_mem ht hs'.1) (T.inv_mem ht), hconj⟩, ?_⟩
  have e1 : Subgroup.inclusion hK₀H ⟨t * (s : G) * t⁻¹, hconj⟩ =
      ⟨t, h.almostSpecialHyp_g1.T_le_H ht⟩ * Subgroup.inclusion hK₀H s *
        ⟨t, h.almostSpecialHyp_g1.T_le_H ht⟩⁻¹ := rfl
  show S143V.rhoH h D (Subgroup.inclusion hK₀H ⟨t * (s : G) * t⁻¹, hconj⟩) = _
  rw [e1, map_mul, map_mul, map_inv]
  rfl

end Helpers

section NormalizerHelpers

theorem mem_normalizer_of_conj {Ω : Type*} [Group Ω] {N : Subgroup Ω} {g : Ω}
    (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N) (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) :
    g ∈ Subgroup.normalizer (N : Set Ω) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

end NormalizerHelpers

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem false_of_noswap (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G)
    (hnab : ¬ IsMulCommutative ↥(uOfL22 T M)) (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h35 : Lemma1435) (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hE22 : E2.E22StatementNoN)
    (hF : FieldOne1432) (D : HatModel T M) {F : Subgroup ↥(D.img (mcOf T))} (hFn : F.Normal)
    (θ : ↥F ≃* SL(2, GaloisField 2 2) × SL(2, GaloisField 2 2))
    (hCF : ∀ x : ↥(D.img (mcOf T)), (∀ f ∈ F, x * f = f * x) → x ∈ F)
    (hno : ∀ γ : ↥(D.img (mcOf T)),
      (AxA.sub1 F θ).map (MulAut.conj γ).toMonoidHom = AxA.sub1 F θ) : False := by
  classical
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  have : IsSimpleGroup SL(2, GaloisField 2 2) :=
    CFSG.ComponentClassification.Asc75T4.isSimpleGroup_sl2 le_rfl
  have : Finite ↥(D.img (mcOf T)) := Finite.of_surjective _ (rhoΓ_surjective h1281 D)
  have hnc : ¬ IsMulCommutative SL(2, GaloisField 2 2) := not_isMulCommutative_sl2_gf (by norm_num)
  have hFn' : ∀ (γ : ↥(D.img (mcOf T))), ∀ f ∈ F, γ * f * γ⁻¹ ∈ F := fun γ f hf =>
    hFn.conj_mem f hf γ
  have hPn := imgΓ_cZU_normal h1281 D
  have hPc : ∀ (γ : ↥(D.img (mcOf T))), ∀ p ∈ imgΓ h1281 D (cZU T M),
      γ * p * γ⁻¹ ∈ imgΓ h1281 D (cZU T M) := fun γ p hp => hPn.conj_mem p hp γ
  have hsub := AxA.sub_le_of_normal hnc θ hFn' hCF hPc (imgΓ_cZU_ne_bot h1281 hnab D)
  have hA₁n : (AxA.sub1 F θ).Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ ∈ (AxA.sub1 F θ).map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
    rwa [hno g] at h1⟩
  have hA₂n : (AxA.sub2 F θ).Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ ∈ (AxA.sub2 F θ).map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
    rcases AxA.map_conj_sub2 hnc θ hFn' g with h | h
    · exfalso
      have hle : AxA.sub2 F θ ≤ AxA.sub1 F θ := by
        intro a ha
        have h2 : g * a * g⁻¹ ∈ (AxA.sub2 F θ).map (MulAut.conj g).toMonoidHom := ⟨a, ha, rfl⟩
        rw [h] at h2
        have h3 : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ ∈
            (AxA.sub1 F θ).map (MulAut.conj g⁻¹).toMonoidHom := ⟨_, h2, rfl⟩
        rw [hno g⁻¹] at h3
        simpa [mul_assoc] using h3
      have heq : AxA.sub2 F θ = AxA.sub1 F θ :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [AxA.card_sub1 F θ, AxA.card_sub2 F θ])
      exact AxA.sub1_ne_sub2 F θ heq.symm
    · rwa [h] at h1⟩
  rcases hsub with h1 | h2
  · exact false_of_normal_sl2_four hyp hnot hnab h11 h113 h35 h37 h39 hE22 hF D hA₁n
      (AxA.sub1Equiv F θ) h1
  · exact false_of_normal_sl2_four hyp hnot hnab h11 h113 h35 h37 h39 hE22 hF D hA₂n
      (AxA.sub2Equiv F θ) h2

theorem false_of_swap
    (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G) (hnab : ¬ IsMulCommutative ↥(uOfL22 T M))
    (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435) (h37 : A37ForSQTK)
    (h39 : A39ForSQTK) (hE22 : E2.E22StatementNoN) (hF : FieldOne1432) (D : HatModel T M)
    {F : Subgroup ↥(D.img (mcOf T))} (hFn : F.Normal)
    (θ : ↥F ≃* SL(2, GaloisField 2 2) × SL(2, GaloisField 2 2))
    (hCF : ∀ x : ↥(D.img (mcOf T)), (∀ f ∈ F, x * f = f * x) → x ∈ F)
    (hnat : IsNaturalMatrixModule (F.map (D.img (mcOf T)).subtype)
      (CFSG.Assembly.LowTwoRank.StatedOmega
        (CFSG.Assembly.LowTwoRank.StatedQuadPlus 2 (GaloisField 2 2))))
    (hswap : ∃ γ : ↥(D.img (mcOf T)),
      (AxA.sub1 F θ).map (MulAut.conj γ).toMonoidHom ≠ AxA.sub1 F θ) : False := by
  classical
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  have hTH : T ≤ mcOf T := h1281.almostSpecialHyp_g1.T_le_H
  have : IsSimpleGroup SL(2, GaloisField 2 2) :=
    CFSG.ComponentClassification.Asc75T4.isSimpleGroup_sl2 le_rfl
  have : Finite ↥(D.img (mcOf T)) := Finite.of_surjective _ (rhoΓ_surjective h1281 D)
  have hnc : ¬ IsMulCommutative SL(2, GaloisField 2 2) := not_isMulCommutative_sl2_gf (by norm_num)
  have hFn' : ∀ (γ : ↥(D.img (mcOf T))), ∀ f ∈ F, γ * f * γ⁻¹ ∈ F := fun γ f hf =>
    hFn.conj_mem f hf γ
  have hdich := AxA.map_conj_sub1 hnc θ hFn'
  have hPn := imgΓ_cZU_normal h1281 D
  have hPc : ∀ (γ : ↥(D.img (mcOf T))), ∀ p ∈ imgΓ h1281 D (cZU T M),
      γ * p * γ⁻¹ ∈ imgΓ h1281 D (cZU T M) := fun γ p hp => hPn.conj_mem p hp γ
  have hsubP := AxA.sub_le_of_normal hnc θ hFn' hCF hPc (imgΓ_cZU_ne_bot h1281 hnab D)
  obtain ⟨γ₀, hγ₀⟩ := hswap
  have hγ₀2 : (AxA.sub1 F θ).map (MulAut.conj γ₀).toMonoidHom = AxA.sub2 F θ :=
    (hdich γ₀).resolve_left hγ₀
  have hFP : F ≤ imgΓ h1281 D (cZU T M) := by
    rw [← AxA.sub1_sup_sub2 F θ]
    refine sup_le ?_ ?_
    · rcases hsubP with h1 | h2
      · exact h1
      · intro a ha
        have h3 : γ₀ * a * γ₀⁻¹ ∈ (AxA.sub1 F θ).map (MulAut.conj γ₀).toMonoidHom :=
          ⟨a, ha, rfl⟩
        rw [hγ₀2] at h3
        have := hPc γ₀⁻¹ _ (h2 h3)
        simpa [mul_assoc] using this
    · rcases hsubP with h1 | h2
      · intro a ha
        rw [← hγ₀2] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        exact hPc γ₀ b (h1 hb)
      · exact h2
  have hA₁F : AxA.sub1 F θ ≤ F := AxA.sub1_le F θ
  have hA₁n : ((AxA.sub1 F θ).subgroupOf F).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact AxA.conj_mem_sub1 θ g.2 hn⟩
  have hA₁s : IsSimpleGroup ↥(AxA.sub1 F θ) := (AxA.sub1Equiv F θ).isSimpleGroup
  have hA₂s : IsSimpleGroup ↥(AxA.sub2 F θ) := (AxA.sub2Equiv F θ).isSimpleGroup
  have hA₁nc : ¬ IsMulCommutative ↥(AxA.sub1 F θ) :=
    not_isMulCommutative_of_sl2_gf (by norm_num) (AxA.sub1Equiv F θ)
  have hA₂nc : ¬ IsMulCommutative ↥(AxA.sub2 F θ) :=
    not_isMulCommutative_of_sl2_gf (by norm_num) (AxA.sub2Equiv F θ)
  obtain ⟨L₁, hL₁, hL₁ρ⟩ := exists_lift_xSub (h := h1281) (D := D) hyp h39 hFP hA₁F hA₁n hA₁s hA₁nc
  have hX1 : centerOf (uOfL22 T M) ≤ xSub h1281 D F := centerOf_le_xSub
  have hX2 : xSub h1281 D F ≤ cZU T M := xSub_le_cZU
  have hXn := xSub_normal (h := h1281) (D := D) hFn
  have hXH : xSub h1281 D F ≤ mcOf T := hX2.trans cZU_le
  have hL₁X : L₁ ≤ xSub h1281 D F := le_of_mem_cComp hL₁
  have hL₁H : L₁ ≤ mcOf T := hL₁X.trans hXH
  set Tb : Subgroup ↥(D.img (mcOf T)) := (T.subgroupOf (mcOf T)).map (rhoΓ h1281 D) with hTb
  have hsylH : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH
  have hTbodd : ¬ 2 ∣ Tb.index := fun hd =>
    hsylH.2.2 (hd.trans (Subgroup.index_map_dvd (T.subgroupOf (mcOf T)) (rhoΓ_surjective h1281 D)))
  obtain ⟨tb, htb, htbswap⟩ := AxA.exists_mem_of_swap hdich hTbodd ⟨γ₀, hγ₀⟩
  obtain ⟨y₀, hy₀, rfl⟩ := htb
  have ht₀T : (y₀ : G) ∈ T := Subgroup.mem_subgroupOf.mp hy₀
  have ht₀H : (y₀ : G) ∈ mcOf T := y₀.2
  have hy₀2 : (AxA.sub1 F θ).map (MulAut.conj (rhoΓ h1281 D y₀)).toMonoidHom =
      AxA.sub2 F θ := (hdich _).resolve_left htbswap
  obtain ⟨hL₂, hL₂ρ⟩ := conj_cZU_lift h1281 D hXn hL₁ ht₀H hL₁ρ
  have hL₂ρ' : (((L₁.map (MulAut.conj (y₀ : G)).toMonoidHom).subgroupOf (mcOf T)).map
      (rhoΓ h1281 D)) = AxA.sub2 F θ := hL₂ρ.trans hy₀2
  set L₂ : Subgroup G := L₁.map (MulAut.conj (y₀ : G)).toMonoidHom with hL₂def
  have hL₂X : L₂ ≤ xSub h1281 D F := le_of_mem_cComp hL₂
  have hne : L₁ ≠ L₂ := fun h => AxA.sub1_ne_sub2 F θ (by rw [← hL₁ρ, ← hL₂ρ', h])
  have hLconj : ∀ t ∈ T, L₁.map (MulAut.conj t).toMonoidHom = L₁ ∨
      L₁.map (MulAut.conj t).toMonoidHom = L₂ := by
    intro t ht
    have htH : t ∈ mcOf T := hTH ht
    obtain ⟨hLt, hLtρ⟩ := conj_cZU_lift h1281 D hXn hL₁ htH hL₁ρ
    rcases hdich (rhoΓ h1281 D ⟨t, htH⟩) with hd | hd
    · left
      exact eq_of_cZU_lift_eq hyp h1281 h37 D hX1 hX2 hLt hL₁ (hLtρ.trans hd) hL₁ρ hA₁s hA₁nc
    · right
      exact eq_of_cZU_lift_eq hyp h1281 h37 D hX1 hX2 hLt hL₂ (hLtρ.trans hd) hL₂ρ' hA₂s hA₂nc
  have hK₀ : conjClosure L₁ T = L₁ ⊔ L₂ := by
    apply le_antisymm
    · apply conjClosure_le
      intro t ht l hl
      have hmem : t * l * t⁻¹ ∈ L₁.map (MulAut.conj t).toMonoidHom := ⟨l, hl, rfl⟩
      rcases hLconj t ht with h | h
      · rw [h] at hmem
        exact Subgroup.mem_sup_left hmem
      · rw [h] at hmem
        exact Subgroup.mem_sup_right hmem
    · refine sup_le (le_conjClosure _ _) ?_
      rintro _ ⟨l, hl, rfl⟩
      exact mem_conjClosure ht₀T hl
  have hK₀H : conjClosure L₁ T ≤ mcOf T := by
    rw [hK₀]
    exact sup_le hL₁H (hL₂X.trans hXH)
  have hK₀P : conjClosure L₁ T ≤ cZU T M := by
    rw [hK₀]
    exact sup_le (hL₁X.trans hX2) (hL₂X.trans hX2)
  have hK₀img : ((conjClosure L₁ T).subgroupOf (mcOf T)).map (rhoΓ h1281 D) = F := by
    rw [hK₀, Subgroup.subgroupOf_sup hL₁H (hL₂X.trans hXH), Subgroup.map_sup, hL₁ρ, hL₂ρ',
      AxA.sub1_sup_sub2]
  have hF0 : F ≠ ⊥ := by
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥(AxA.sub1 F θ))
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨(a : ↥(D.img (mcOf T))), hA₁F a.2⟩, fun h => ha ?_⟩
    apply Subtype.ext
    exact congrArg (fun x : ↥F => (x : ↥(D.img (mcOf T)))) h
  have hcomm : ⁅L₁, conjSub (y₀ : G) L₁⁆ ≤ pCoreOf 2 (conjClosure L₁ T ⊔ T) := by
    have hHX : pCoreOf 2 (xSub h1281 D F) ≠ ⊥ := pCoreOf_ne_bot_of_le_cZU h1281 hX1 hX2
    have hc2 := lemma_1_2_1_two hyp.qtke hyp.simple hyp.nonabelian h37 hHX hL₁ hL₂ hne
    have hcomm' : ⁅L₁, L₂⁆ ≤ pCoreOf 2 (xSub h1281 D F) := hc2.1.trans hc2.2
    have hKTH : conjClosure L₁ T ⊔ T ≤ mcOf T := sup_le hK₀H hTH
    have hHN : mcOf T ≤
        Subgroup.normalizer ((pCoreOf 2 (xSub h1281 D F) : Subgroup G) : Set G) := by
      have hN : mcOf T ≤ Subgroup.normalizer ((xSub h1281 D F : Subgroup G) : Set G) := fun x hx =>
        Subgroup.mem_normalizer_iff.mpr fun p => ⟨fun hp => hXn x hx p hp, fun hp => by
          have := hXn x⁻¹ ((mcOf T).inv_mem hx) _ hp
          simpa [mul_assoc] using this⟩
      exact hN.trans (normalizer_le_normalizer_pCoreOf 2 _)
    have hN' : pCoreOf 2 (xSub h1281 D F) ⊓ (conjClosure L₁ T ⊔ T) ≤
        pCoreOf 2 (conjClosure L₁ T ⊔ T) := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ?_
      · intro j hj
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · rintro ⟨hx1, hx2⟩
          refine ⟨(Subgroup.mem_normalizer_iff.mp (hHN (hKTH hj)) x).mp hx1, ?_⟩
          exact (conjClosure L₁ T ⊔ T).mul_mem ((conjClosure L₁ T ⊔ T).mul_mem hj hx2)
            ((conjClosure L₁ T ⊔ T).inv_mem hj)
        · rintro ⟨hx1, hx2⟩
          refine ⟨(Subgroup.mem_normalizer_iff.mp (hHN (hKTH hj)) x).mpr hx1, ?_⟩
          have := (conjClosure L₁ T ⊔ T).mul_mem ((conjClosure L₁ T ⊔ T).mul_mem
            ((conjClosure L₁ T ⊔ T).inv_mem hj) hx2) hj
          simpa [mul_assoc] using this
      · exact (pCoreOf_isPGroup 2 _).to_le inf_le_left
    refine (le_inf hcomm' ?_).trans hN'
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have h1 : a ∈ conjClosure L₁ T ⊔ T := Subgroup.mem_sup_left (by
      rw [hK₀]; exact Subgroup.mem_sup_left ha)
    have h2 : b ∈ conjClosure L₁ T ⊔ T := Subgroup.mem_sup_left (by
      rw [hK₀]; exact Subgroup.mem_sup_right hb)
    rw [commutatorElement_def]
    exact (conjClosure L₁ T ⊔ T).mul_mem ((conjClosure L₁ T ⊔ T).mul_mem
      ((conjClosure L₁ T ⊔ T).mul_mem h1 h2) ((conjClosure L₁ T ⊔ T).inv_mem h1))
      ((conjClosure L₁ T ⊔ T).inv_mem h2)
  have hnorm : (y₀ : G) ∉ Subgroup.normalizer (L₁ : Set G) := fun htn =>
    hne (A38.map_conj_eq_iff.mpr htn).symm
  have hpair : IsPairIn T L₁ := ⟨(y₀ : G), ht₀T, hnorm, hK₀, hcomm⟩
  have hL₁Hc : L₁ ∈ cComp (mcOf T) := cComp_mem_of_subnormal (xSub_isSubnormal hFn) hL₁
  have hKc : L₁ ∈ cComp (conjClosure L₁ T ⊔ T) :=
    cComp_mem_of_le hL₁Hc ((le_conjClosure L₁ T).trans le_sup_left) (sup_le hK₀H hTH)
  obtain ⟨-, ⟨eK⟩⟩ := kbar_of_cZU_lift h1281 D hX2 hL₁ hL₁ρ hA₁s hA₁nc
  have hsimp : IsSimpleGroup (KBar L₁) := eK.isSimpleGroup
  obtain ⟨eS⟩ : Nonempty (SL(2, GaloisField 2 2) ≃* ↥(alternatingGroup (Fin 5))) := by
    obtain ⟨e⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
    exact ⟨(CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 2)).symm.trans e⟩
  have hshape : (∃ n, IsPSL 2 2 n (KBar L₁)) ∨ (∃ n, IsSz n (KBar L₁)) ∨ IsAlt 5 (KBar L₁) :=
    Or.inr (Or.inr ⟨eK.trans ((AxA.sub1Equiv F θ).trans eS)⟩)
  have hHTM : IsHTM T M (conjClosure L₁ T ⊔ T) :=
    ⟨inH_sup_T hyp h1281 hK₀H, fun hle =>
      not_le_M_of_normal_image h1281 hnab D hFn hK₀img hF0 (le_sup_left.trans hle)⟩
  have hBM : conjClosure L₁ T ⊓
      Subgroup.normalizer ((T ⊓ conjClosure L₁ T : Subgroup G) : Set G) ≤ M := by
    have hTN : T ≤ Subgroup.normalizer ((conjClosure L₁ T : Subgroup G) : Set G) :=
      le_normalizer_conjClosure L₁ T
    have hker : ∀ x : ↥(mcOf T), (x : G) ∈ conjClosure L₁ T → S143V.rhoH h1281 D x = 1 →
        (x : G) ∈ T := fun x hx hx1 => cZU_ker_le_T h1281 D (hK₀P hx) hx1
    have hrange : (rhoRes h1281 D hK₀H).range = F.map (D.img (mcOf T)).subtype := by
      rw [range_rhoRes, hK₀img]
    have hS'F : sImg h1281 D hK₀H ≤ F.map (D.img (mcOf T)).subtype :=
      hrange ▸ sImg_le_range h1281 D hK₀H
    obtain ⟨θ', e, hint, hS⟩ := exists_model_sylow hnat hS'F (isPGroup_sImg hyp h1281 D hK₀H)
      (by rw [← hrange]; exact relIndex_sImg_odd hyp h1281 D hK₀H hTN hker)
    obtain ⟨hS1, hS2, hi1, hi2, hgen⟩ := frame_sylow hS'F θ' e hint hS
    have hFg : ∀ (t : G) (ht : t ∈ mcOf T), S143V.rhoH h1281 D ⟨t, ht⟩ ∈
        Subgroup.normalizer ((F.map (D.img (mcOf T)).subtype : Subgroup _) : Set _) := by
      intro t ht
      have key : ∀ (u : G) (hu : u ∈ mcOf T), ∀ x ∈ F.map (D.img (mcOf T)).subtype,
          S143V.rhoH h1281 D ⟨u, hu⟩ * x * (S143V.rhoH h1281 D ⟨u, hu⟩)⁻¹ ∈
            F.map (D.img (mcOf T)).subtype := by
        intro u hu x hx
        obtain ⟨f, hf, rfl⟩ := hx
        refine ⟨rhoΓ h1281 D ⟨u, hu⟩ * f * (rhoΓ h1281 D ⟨u, hu⟩)⁻¹,
          hFn.conj_mem f hf _, ?_⟩
        simp only [map_mul, map_inv]
        rfl
      refine mem_normalizer_of_conj (key t ht) (fun x hx => ?_)
      have := key t⁻¹ ((mcOf T).inv_mem ht) x hx
      rw [show (⟨t⁻¹, (mcOf T).inv_mem ht⟩ : ↥(mcOf T)) = (⟨t, ht⟩ : ↥(mcOf T))⁻¹ from rfl,
        map_inv, inv_inv] at this
      exact this
    have hSg : ∀ (t : G) (ht : t ∈ T), S143V.rhoH h1281 D ⟨t, hTH ht⟩ ∈
        Subgroup.normalizer ((sImg h1281 D hK₀H : Subgroup _) : Set _) := by
      intro t ht
      refine mem_normalizer_of_conj (fun x hx => conj_mem_sImg h1281 D hK₀H hTN ht hx)
        (fun x hx => ?_)
      have := conj_mem_sImg h1281 D hK₀H hTN (T.inv_mem ht) hx
      rw [show (⟨t⁻¹, hTH (T.inv_mem ht)⟩ : ↥(mcOf T)) = (⟨t, hTH ht⟩ : ↥(mcOf T))⁻¹ from rfl,
        map_inv, inv_inv] at this
      exact this
    refine borel_le_M_of_two_overgroups hyp hnot h35 h1281 D hK₀H hTN hker hS1 hS2
      (fun g hg => ⟨(yOne_le _ _ hg).2, hrange ▸ (yOne_le _ _ hg).1⟩)
      (fun g hg => ⟨(yTwo_le _ _ hg).2, hrange ▸ (yTwo_le _ _ hg).1⟩)
      (fun t ht => normalizer_yOne (hFg t (hTH ht)) (hSg t ht))
      (fun t ht => normalizer_yTwo (hFg t (hTH ht)) (hSg t ht)) hi1 hi2
      (fun g hg => hgen ⟨hrange ▸ hg.2, hg.1⟩)
  exact false_of_bender_pair_borel hE22 hF hyp hnot hHTM hKc hpair hsimp hshape hBM

theorem excl7S
    (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435) (h37 : A37ForSQTK)
    (h39 : A39ForSQTK) (hE22 : E2.E22StatementNoN) (hF : FieldOne1432) :
    Lemma14315Excl7S := by
  intro G _ _ T M hyp hnot hnab D g hg hc7
  exfalso
  obtain ⟨⟨hd, ⟨θ⟩, hX⟩, hnat⟩ := hc7
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  have : Finite ↥(D.img (mcOf T)) := Finite.of_surjective _ (rhoΓ_surjective h1281 D)
  have hFn := CFSG.ClassicalInvolution.genFittingFStar_normal ↥(D.img (mcOf T))
  have hCF : ∀ x : ↥(D.img (mcOf T)), (∀ f ∈ genFittingFStar ↥(D.img (mcOf T)),
      x * f = f * x) → x ∈ genFittingFStar ↥(D.img (mcOf T)) := fun x hx =>
    CFSG.Adapters.generalized_fitting_self_centralizing _
      (Subgroup.mem_centralizer_iff.mpr fun f hf => (hx f hf).symm)
  by_cases hsw : ∃ γ : ↥(D.img (mcOf T)),
      (AxA.sub1 (genFittingFStar ↥(D.img (mcOf T))) θ).map (MulAut.conj γ).toMonoidHom ≠
        AxA.sub1 (genFittingFStar ↥(D.img (mcOf T))) θ
  · exact false_of_swap hyp hnot hnab h11 h113 h35 h37 h39 hE22 hF D hFn θ hCF hnat hsw
  · push Not at hsw
    exact false_of_noswap hyp hnot hnab h11 h113 h35 h37 h39 hE22 hF D hFn θ hCF hsw

end Main

end SzPS8

end CFSG.Quasithin
