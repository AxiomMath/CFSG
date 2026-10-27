module

public import CFSG.RankThree.GF2n.Smith81.OrthE1B7bHeart
public import CFSG.RankThree.GF2n.Smith81.OrthE1B7bCard
public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormT3

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.OrthTN

section Coord

variable {G : Type} [Group G] {M Q Z : Subgroup G}

@[expose] def b7b_coordHom (AM : ActionModel M Q Z) (θ : AM.M₀.E ≃ₗ[AM.K] Cube 3 AM.K) :
    ↥(H0 M Z) →* (Cube 3 AM.K ≃ₗ[AM.K] Cube 3 AM.K) where
  toFun x := θ.symm.trans ((AM.φ x).trans θ)
  map_one' := by
    refine LinearEquiv.ext fun v => ?_
    simp
  map_mul' x y := by
    refine LinearEquiv.ext fun v => ?_
    simp

theorem b7b_coordHom_apply (AM : ActionModel M Q Z) (θ : AM.M₀.E ≃ₗ[AM.K] Cube 3 AM.K)
    (x : ↥(H0 M Z)) (v : Cube 3 AM.K) : b7b_coordHom AM θ x v = θ (AM.φ x (θ.symm v)) := rfl

theorem b7b_coordHom_eq_one_iff (AM : ActionModel M Q Z) (θ : AM.M₀.E ≃ₗ[AM.K] Cube 3 AM.K)
    (x : ↥(H0 M Z)) : b7b_coordHom AM θ x = 1 ↔ (x : G) ∈ Q := by
  rw [← AM.φ_ker]
  constructor
  · intro h
    refine LinearEquiv.ext fun e => ?_
    have := LinearEquiv.congr_fun h (θ e)
    rw [b7b_coordHom_apply, LinearEquiv.symm_apply_apply] at this
    exact θ.injective this
  · intro h
    refine LinearEquiv.ext fun v => ?_
    rw [b7b_coordHom_apply, h]
    simp

theorem b7b_factorAct_img (AM : ActionModel M Q Z) (θ0 : AM.M₀.E ≃ₗ[AM.K] Tensor3 AM.K)
    (F : Subgroup G) (i : Fin 3)
    (act : Matrix (Fin 2) (Fin 2) AM.K → Tensor3 AM.K → Tensor3 AM.K)
    (hact : ∀ A T, tensor3Cube AM.K (act A T) = actMap i A (tensor3Cube AM.K T))
    (h : FactorAct AM θ0 F act) :
    (F.subgroupOf (H0 M Z)).map (b7b_coordHom AM (θ0.trans (tensor3Cube AM.K))) =
      cubeF 3 AM.K i := by
  set θ : AM.M₀.E ≃ₗ[AM.K] Cube 3 AM.K := θ0.trans (tensor3Cube AM.K) with hθ
  have key : ∀ (x : ↥(H0 M Z)) (A : Matrix (Fin 2) (Fin 2) AM.K),
      (∀ e, θ0 (AM.φ x e) = act A (θ0 e)) → ∀ v, b7b_coordHom AM θ x v = actMap i A v := by
    intro x A hx v
    rw [b7b_coordHom_apply]
    have e1 : θ (AM.φ x (θ.symm v)) = tensor3Cube AM.K (θ0 (AM.φ x (θ.symm v))) := rfl
    rw [e1, hx, hact]
    have e2 : tensor3Cube AM.K (θ0 (θ.symm v)) = v := θ.apply_symm_apply v
    rw [e2]
  refine Subgroup.ext fun g => ⟨?_, ?_⟩
  · rintro ⟨x, hxF, rfl⟩
    obtain ⟨A, hA, hx⟩ := h.1 x (Subgroup.mem_subgroupOf.mp hxF)
    exact mem_cubeF.mpr ⟨A, hA, key x A hx⟩
  · intro hg
    obtain ⟨A, hA, hgA⟩ := mem_cubeF.mp hg
    obtain ⟨x, hxF, hx⟩ := h.2 A hA
    refine ⟨x, Subgroup.mem_subgroupOf.mpr hxF, ?_⟩
    refine LinearEquiv.ext fun v => ?_
    rw [key x A hx v, hgA v]

theorem b7b_img_sup {H : Subgroup G} {Γ : Type*} [Group Γ] (ρ : ↥H →* Γ) {A B : Subgroup G}
    (hA : A ≤ H) (hB : B ≤ H) :
    ((A ⊔ B).subgroupOf H).map ρ = (A.subgroupOf H).map ρ ⊔ (B.subgroupOf H).map ρ := by
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

end Coord

section Main


theorem b7b_of (hB1 : B1Statement) (hB6 : B6Statement) (hT : TripleStatement)
    (hSplit : RtSplitStatement) : B7bStatement := by
  intro G _ _ M Q Z B t hH D S₁ hS₁ hLS hidx hne
  rcases (caseE1_iff M Q Z B t).mp hH.case with hPlus | hMinus
  swap
  · exact ((hB1 G M Q Z B t hH D.g D.hg).1 hMinus).elim
  obtain ⟨AM⟩ := ActionModel.nonempty hH.ctx.hyp
  have hN'g : conjSubgroup D.g (Nt M (LB M Q B) t) ≤ Nt M (LB M Q B) t ⊔ D.Fb :=
    le_sup_of_le_right D.N'_le_Fb
  obtain ⟨⟨θ0, -, hY, hFb, hFc⟩, -⟩ :=
    hT G M Q Z B t hH AM D.g D.hg hPlus D.Fb D.Fc D.Y D.two hN'g D.two'
  obtain ⟨hLBE, hE0L, hnorm, -⟩ := hB6 G M Q Z B t hH D
  let θ : AM.M₀.E ≃ₗ[AM.K] Cube 3 AM.K := θ0.trans (tensor3Cube AM.K)
  let ρ := b7b_coordHom AM θ
  have hqK : 4 ≤ Nat.card AM.K := by rw [AM.glob.card]; exact hH.ctx.hyp.q4
  have hLH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hH.ctx
  have hE0H : D.Y ⊔ D.Fb ⊔ D.Fc ≤ H0 M Z := hE0L.trans hLH
  have hYH : D.Y ≤ H0 M Z := le_sup_left.trans (le_sup_left.trans hE0H)
  have hFbH : D.Fb ≤ H0 M Z := le_sup_right.trans (le_sup_left.trans hE0H)
  have hFcH : D.Fc ≤ H0 M Z := le_sup_right.trans hE0H
  have himgY := b7b_factorAct_img AM θ0 D.Y 0 tensor3Act0 tensor3Cube_act0 hY
  have himgFb := b7b_factorAct_img AM θ0 D.Fb 1 tensor3Act1 tensor3Cube_act1 hFb
  have himgFc := b7b_factorAct_img AM θ0 D.Fc 2 tensor3Act2 tensor3Cube_act2 hFc
  have himgE : ((D.Y ⊔ D.Fb ⊔ D.Fc).subgroupOf (H0 M Z)).map ρ = cubeE 3 AM.K := by
    rw [b7b_img_sup ρ (sup_le hYH hFbH) hFcH, b7b_img_sup ρ hYH hFbH, himgY, himgFb, himgFc]
    exact (cubeE_eq_sup hqK).symm
  have hLBH : LB M Q B ≤ H0 M Z := hLBE.trans hE0H
  have hQLB : Q ≤ LB M Q B := le_sup_left
  have hQH : Q ≤ H0 M Z := hQLB.trans hLBH
  obtain ⟨s, hsS, hsLB⟩ : ∃ s ∈ S₁, s ∉ LB M Q B := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm (fun s hs => hcon s hs) hLS)
  have hsLgen : s ∈ Lgen M (LB M Q B) := hS₁.2.1 hsS
  have hidx2 : ((LB M Q B).subgroupOf S₁).index = 2 := by
    have h1 : ((LB M Q B).subgroupOf S₁).index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      intro htop
      apply hsLB
      have : (⟨s, hsS⟩ : ↥S₁) ∈ (LB M Q B).subgroupOf S₁ := by rw [htop]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    have h0 : ((LB M Q B).subgroupOf S₁).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 : ((LB M Q B).subgroupOf S₁).index ≤ 2 := hidx
    omega
  haveI : ((LB M Q B).subgroupOf S₁).Normal := Subgroup.normal_of_index_eq_two hidx2
  have hnLB : ∀ l ∈ LB M Q B, s * l * s⁻¹ ∈ LB M Q B := by
    intro l hl
    have := Subgroup.Normal.conj_mem (inferInstance : ((LB M Q B).subgroupOf S₁).Normal)
      ⟨l, hLS hl⟩ (Subgroup.mem_subgroupOf.mpr hl) ⟨s, hsS⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hnLB' : ∀ l ∈ LB M Q B, s⁻¹ * l * s ∈ LB M Q B := by
    intro l hl
    have := Subgroup.Normal.conj_mem (inferInstance : ((LB M Q B).subgroupOf S₁).Normal)
      ⟨l, hLS hl⟩ (Subgroup.mem_subgroupOf.mpr hl) (⟨s, hsS⟩ : ↥S₁)⁻¹
    simpa using Subgroup.mem_subgroupOf.mp this
  have hs2 : s * s ∈ LB M Q B := by
    have := Subgroup.pow_index_mem ((LB M Q B).subgroupOf S₁) (⟨s, hsS⟩ : ↥S₁)
    rw [hidx2] at this
    have h' := Subgroup.mem_subgroupOf.mp this
    simpa [pow_two] using h'
  have hsN : s ∈ Subgroup.normalizer (LB M Q B : Set G) :=
    Subgroup.mem_normalizer_fintype fun l hl => hnLB l hl
  have hconj : conjSubgroup s (D.Y ⊔ D.Fb ⊔ D.Fc) = D.Y ⊔ D.Fb ⊔ D.Fc := hnorm s hsLgen hsN
  let s' : ↥(H0 M Z) := ⟨s, hLH hsLgen⟩
  have hnE : ∀ x ∈ cubeE 3 AM.K, ρ s' * x * (ρ s')⁻¹ ∈ cubeE 3 AM.K := by
    intro x hx
    rw [← himgE] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← himgE]
    refine ⟨s' * y * s'⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    have e : ((s' * y * s'⁻¹ : ↥(H0 M Z)) : G) = s * (y : G) * s⁻¹ := by simp [s']
    rw [e]
    have h1 : s * (y : G) * s⁻¹ ∈ conjSubgroup s (D.Y ⊔ D.Fb ⊔ D.Fc) := by
      rw [mem_conjSubgroup]
      have e2 : s⁻¹ * (s * (y : G) * s⁻¹) * s = y := by group
      rw [e2]
      exact Subgroup.mem_subgroupOf.mp hy
    rwa [hconj] at h1
  have hnE' : ∀ x ∈ cubeE 3 AM.K, (ρ s')⁻¹ * x * ρ s' ∈ cubeE 3 AM.K := by
    intro x hx
    rw [← himgE] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← himgE]
    refine ⟨s'⁻¹ * y * s', Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    have e : ((s'⁻¹ * y * s' : ↥(H0 M Z)) : G) = s⁻¹ * (y : G) * s := by simp [s']
    rw [e]
    have h1 : (y : G) ∈ conjSubgroup s (D.Y ⊔ D.Fb ⊔ D.Fc) := by
      rw [hconj]
      exact Subgroup.mem_subgroupOf.mp hy
    exact mem_conjSubgroup.mp h1
  set L : Subgroup ↥(H0 M Z) := (LB M Q B).subgroupOf (H0 M Z) with hLdef
  have hker : ∀ x, ρ x = 1 → x ∈ L := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hQLB ((b7b_coordHom_eq_one_iff AM θ x).mp hx))
  have hkerEq : ρ.ker = Q.subgroupOf (H0 M Z) := Subgroup.ext fun x => by
    rw [MonoidHom.mem_ker, b7b_coordHom_eq_one_iff, Subgroup.mem_subgroupOf]
  have hcardL : Nat.card (L.map ρ) = Nat.card AM.K ^ 3 := by
    have h1 := b7b_card_map_mul_card_ker ρ L
    have hLinf : L ⊓ ρ.ker = ρ.ker :=
      inf_eq_right.mpr fun x hx => hker x (MonoidHom.mem_ker.mp hx)
    rw [hLinf, hkerEq] at h1
    have hQcard : Nat.card ↥(Q.subgroupOf (H0 M Z)) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
    have hLcard : Nat.card L = Nat.card (LB M Q B) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLBH).toEquiv
    rw [hQcard, hLcard, b7b_card_LB_of_split hSplit hH, ← AM.glob.card] at h1
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hQpos (by rw [h1, mul_comm])
  have hLE : L.map ρ ≤ cubeE 3 AM.K := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← himgE]
    exact ⟨y, Subgroup.mem_subgroupOf.mpr (hLBE (Subgroup.mem_subgroupOf.mp hy)), rfl⟩
  have hs'L : s' ∉ L := fun h => hsLB (Subgroup.mem_subgroupOf.mp h)
  have hs'2 : s' * s' ∈ L := Subgroup.mem_subgroupOf.mpr (by simpa [s'] using hs2)
  have hnL'' : ∀ l ∈ L, s'⁻¹ * l * s' ∈ L := fun l hl =>
    Subgroup.mem_subgroupOf.mpr (by
      simpa [s'] using hnLB' (l : G) (Subgroup.mem_subgroupOf.mp hl))
  obtain ⟨l, hl, hsq, hall⟩ := b7b_abstract hqK ρ L hker hcardL hLE s' hs'L hs'2 hnL'' hnE hnE'
  have hlLB : (l : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hl
  refine ⟨s * (l : G), S₁.mul_mem hsS (hLS hlLB), ?_, ?_, ?_⟩
  · intro h
    apply hsLB
    simpa using (LB M Q B).mul_mem h ((LB M Q B).inv_mem hlLB)
  · have := (b7b_coordHom_eq_one_iff AM θ (s' * l * (s' * l))).mp hsq
    simpa [s'] using this
  · intro h hh hmem
    exact hall ⟨h, hLH hh⟩ (by rw [Subgroup.mem_subgroupOf]; simpa [s'] using hmem)

end Main

end CFSG.RankThree.GF2n.Smith81.Smith23E1

end
