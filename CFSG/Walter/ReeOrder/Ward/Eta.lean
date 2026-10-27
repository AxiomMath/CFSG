module

public import CFSG.Walter.ReeOrder.Ward.Special
public import CFSG.Walter.ReeOrder.Ward.LSums
public import CFSG.Walter.ReeOrder.Ward.Mult

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct
open CFSG.PSL2Table CFSG.TwoRankLowerBound.Helpers

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} (S : WardSetup G L q e IV)

structure EtaData where
  η : S.W.RFam → G → ℂ
  η' : S.W.RFam → G → ℂ
  ε : ℤ
  ε' : ℤ
  mem : ∀ i, η i ∈ BlocksIrr G
  mem' : ∀ i, η' i ∈ BlocksIrr G
  inj : Function.Injective η
  inj' : Function.Injective η'
  ε_eq : ε = 1 ∨ ε = -1
  ε'_eq : ε' = 1 ∨ ε' = -1
  disj : ∀ i k, η i ≠ η' k
  ma_other : ∀ χ ∈ BlocksIrr G, ∀ i j, (S.ma χ i.1 : ℤ) - S.ma χ j.1 =
    ε * ((if χ = η i then 1 else 0) - (if χ = η j then 1 else 0))
  mb_other : ∀ χ ∈ BlocksIrr G, ∀ i j, (S.mb χ i.1 : ℤ) - S.mb χ j.1 =
    ε' * ((if χ = η' i then 1 else 0) - (if χ = η' j then 1 else 0))
  ma_η : ∀ i j, ∀ θ ∈ BlocksIrr L, (S.ma (η i) θ : ℤ) - S.ma (η j) θ =
    ε * ((if θ = i.1 then 1 else 0) - (if θ = j.1 then 1 else 0))
  mb_η : ∀ i j, ∀ θ ∈ BlocksIrr L, S.mb (η i) θ = S.mb (η j) θ
  ma_η' : ∀ i j, ∀ θ ∈ BlocksIrr L, S.ma (η' i) θ = S.ma (η' j) θ
  mb_η' : ∀ i j, ∀ θ ∈ BlocksIrr L, (S.mb (η' i) θ : ℤ) - S.mb (η' j) θ =
    ε' * ((if θ = i.1 then 1 else 0) - (if θ = j.1 then 1 else 0))
  val : ∀ x : G, (∀ a : G, a⁻¹ * x * a ∉ S.Kset) → ∀ i j, η i x = η j x
  val' : ∀ x : G, (∀ a : G, a⁻¹ * x * a ∉ S.Kset) → ∀ i j, η' i x = η' j x

theorem ψ_inj (ε : Subgroup.zpowers S.J → ℂ) (hε : ε 1 = 1) {θ θ' : L → ℂ}
    (h : S.ψ ε θ = S.ψ ε θ') : θ = θ' := by
  funext y
  have := congrFun h ⟨S.κ y, S.κ_mem_centralizer y⟩
  rwa [S.ψ_κ ε hε, S.ψ_κ ε hε] at this

theorem ψ_one_ne_sgn {θ θ' : L → ℂ} (hθ : θ ∈ BlocksIrr L) (hθ' : θ' ∈ BlocksIrr L) :
    S.ψ 1 θ ≠ S.ψ (signChar _) θ' := by
  intro h
  have hJ : S.J * S.κ 1 ∈ Subgroup.centralizer ({S.J} : Set G) := by
    rw [map_one, mul_one]
    exact S.J_mem_centralizer
  have := congrFun h ⟨S.J * S.κ 1, hJ⟩
  rw [S.ψ_Jκ, S.ψ_Jκ, S.signChar_Jz, Pi.one_apply] at this
  have h1 := blocksIrr_identity_re_pos ⟨θ, hθ⟩
  have h2 := blocksIrr_identity_re_pos ⟨θ', hθ'⟩
  have h3 := congrArg Complex.re this
  simp only [one_mul, neg_mul, Complex.neg_re] at h3
  dsimp only at h1 h2
  linarith

theorem ψ_eq_iff (ε : Subgroup.zpowers S.J → ℂ) (hε : ε 1 = 1) {θ θ' : L → ℂ} :
    S.ψ ε θ = S.ψ ε θ' ↔ θ = θ' :=
  ⟨S.ψ_inj ε hε, fun h => h ▸ rfl⟩

theorem not_Kset {h : G} (hh : h ∈ Subgroup.centralizer ({S.J} : Set G)) (hK : h ∉ S.Kset) :
    ∃ y : L, (∀ g : L, g⁻¹ * y * g ∈ S.W.Ro → g⁻¹ * y * g = 1) ∧
      (h = S.κ y ∨ h = S.J * S.κ y) := by
  obtain ⟨y, hy⟩ := (S.mem_centralizer_iff h).mp hh
  refine ⟨y, fun g hg => ?_, hy⟩
  by_contra hne
  exact hK ⟨y, ⟨g, hg, hne⟩, hy⟩

theorem ψ_agree (ε : Subgroup.zpowers S.J → ℂ) (hε : ε 1 = 1) {θ θ' : L → ℂ}
    (hθ : θ ∈ S.W.RFam) (hθ' : θ' ∈ S.W.RFam) (h : Subgroup.centralizer ({S.J} : Set G))
    (hK : (h : G) ∉ S.Kset) : S.ψ ε θ h = S.ψ ε θ' h := by
  obtain ⟨y, hy, hh | hh⟩ := S.not_Kset h.2 hK
  · have : h = ⟨S.κ y, S.κ_mem_centralizer y⟩ := Subtype.ext hh
    rw [this, S.ψ_κ ε hε, S.ψ_κ ε hε, S.W.R_agree hθ hθ' hy]
  · have : h = ⟨S.J * S.κ y, hh ▸ h.2⟩ := Subtype.ext hh
    rw [this, S.ψ_Jκ, S.ψ_Jκ, S.W.R_agree hθ hθ' hy]

theorem card_RFam_ge : 6 ≤ S.W.RFam.card := by
  have h1 := S.W.cardR
  have h2 := S.q_ge
  rcases S.W.e_eq with rfl | rfl <;> omega

theorem card_RFam_two : 2 ≤ Fintype.card S.W.RFam := by
  rw [Fintype.card_coe]
  have := S.card_RFam_ge
  omega

theorem res_apply (χ : G → ℂ) (h : Subgroup.centralizer ({S.J} : Set G)) :
    S.res χ h = χ h := rfl

theorem mult_of_res_eq {χ χ' : G → ℂ} (ε₀ : Subgroup.zpowers S.J → ℂ) (c : ℤ) {θ₁ θ₂ : L → ℂ}
    (hres : ∀ h : Subgroup.centralizer ({S.J} : Set G),
      χ h - c * S.ψ ε₀ θ₁ h = χ' h - c * S.ψ ε₀ θ₂ h) (θ : L → ℂ) (ε₁ : _)
    (hε₁ : ε₁ ∈ BlocksIrr (Subgroup.zpowers S.J))
    (hθ : θ ∈ BlocksIrr L) (hψ₁ : S.ψ ε₀ θ₁ ∈ BlocksIrr (Subgroup.centralizer ({S.J} : Set G)))
    (hψ₂ : S.ψ ε₀ θ₂ ∈ BlocksIrr (Subgroup.centralizer ({S.J} : Set G))) :
    BlocksInnerProduct (S.res χ) (S.ψ ε₁ θ) - BlocksInnerProduct (S.res χ') (S.ψ ε₁ θ) =
      c * ((if S.ψ ε₀ θ₁ = S.ψ ε₁ θ then 1 else 0) - (if S.ψ ε₀ θ₂ = S.ψ ε₁ θ then 1 else 0)) := by
  have hfun : S.res χ - S.res χ' = (c : ℂ) • (S.ψ ε₀ θ₁ - S.ψ ε₀ θ₂) := by
    funext h
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, res_apply]
    linear_combination hres h
  have hψ := S.ψ_mem hε₁ hθ
  rw [← blocksInnerProduct_sub_left, hfun, blocksInnerProduct_smul_left,
    blocksInnerProduct_sub_left, blocksInnerProduct_irr hψ₁ hψ, blocksInnerProduct_irr hψ₂ hψ]

theorem exists_etaData (S : WardSetup G L q e) : Nonempty S.EtaData := by
  set H := Subgroup.centralizer ({S.J} : Set G) with hH
  set ι := S.W.RFam
  have hK := S.Kset_special
  have h1K := S.one_not_Kset
  have hsgn1 : signChar (Subgroup.zpowers S.J) 1 = 1 := by simp [signChar]
  obtain ⟨η, ε, hηmem, hηinj, hε, hind, hres, hmult, hval⟩ :=
    exceptional_characters S.card_RFam_two hK h1K (fun i : ι => S.ψ 1 i.1)
      (fun i => S.ψ_one_mem (S.W.R_mem i.2))
      (fun i j h => Subtype.ext (S.ψ_inj 1 rfl h))
      (fun i j h hh => S.ψ_agree 1 rfl i.2 j.2 h hh)
  obtain ⟨η', ε', hηmem₂, hηinj₂, hε₂, hind₂, hres₂, hmult₂, hval₂⟩ :=
    exceptional_characters S.card_RFam_two hK h1K (fun i : ι => S.ψ (signChar _) i.1)
      (fun i => S.ψ_sgn_mem (S.W.R_mem i.2))
      (fun i j h => Subtype.ext (S.ψ_inj _ hsgn1 h))
      (fun i j h hh => S.ψ_agree _ hsgn1 i.2 j.2 h hh)
  have hdisj : ∀ i k, η i ≠ η' k := by
    apply exceptional_disjoint hK (fun i : ι => S.ψ 1 i.1) (fun i : ι => S.ψ (signChar _) i.1)
      η η' ε ε' hηmem hηmem₂ hηinj hηinj₂ hε hε₂ hind hind₂
    · intro k l
      have hk := isClassFunction_of_mem (S.ψ_sgn_mem (S.W.R_mem k.2))
      have hl := isClassFunction_of_mem (S.ψ_sgn_mem (S.W.R_mem l.2))
      intro g c
      simp only [Pi.sub_apply]
      rw [hk, hl]
    · intro k l h hh
      simp only [Pi.sub_apply]
      rw [S.ψ_agree _ hsgn1 k.2 l.2 h hh, sub_self]
    · intro i j k l
      rw [blocksInnerProduct_sub_sub (S.ψ_one_mem (S.W.R_mem i.2)) (S.ψ_one_mem (S.W.R_mem j.2))
        (S.ψ_sgn_mem (S.W.R_mem k.2)) (S.ψ_sgn_mem (S.W.R_mem l.2))]
      simp [S.ψ_one_ne_sgn (S.W.R_mem i.2) (S.W.R_mem k.2),
        S.ψ_one_ne_sgn (S.W.R_mem i.2) (S.W.R_mem l.2),
        S.ψ_one_ne_sgn (S.W.R_mem j.2) (S.W.R_mem k.2),
        S.ψ_one_ne_sgn (S.W.R_mem j.2) (S.W.R_mem l.2)]
    · intro i
      have : 2 ≤ Fintype.card ι := S.card_RFam_two
      obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
      exact ⟨j, hj⟩
    · intro k
      have : 2 ≤ Fintype.card ι := S.card_RFam_two
      obtain ⟨l, hl⟩ := Fintype.exists_ne_of_one_lt_card (by omega) k
      exact ⟨l, hl⟩
  have hint : ∀ {a b : ℤ} {c : ℂ}, ((a : ℂ) - b = (c : ℂ)) → ∀ d : ℤ, c = d → a - b = d := by
    intro a b c h d hd
    rw [hd] at h
    exact_mod_cast h
  refine ⟨{
    η := η
    η' := η'
    ε := ε
    ε' := ε'
    mem := hηmem
    mem' := hηmem₂
    inj := hηinj
    inj' := hηinj₂
    ε_eq := hε
    ε'_eq := hε₂
    disj := hdisj
    ma_other := ?_
    mb_other := ?_
    ma_η := ?_
    mb_η := ?_
    ma_η' := ?_
    mb_η' := ?_
    val := hval
    val' := hval₂ }⟩
  · intro χ hχ i j
    have h : BlocksInnerProduct (S.res χ) (S.ψ 1 i.1) -
        BlocksInnerProduct (S.res χ) (S.ψ 1 j.1) =
        ε * ((if χ = η i then 1 else 0) - (if χ = η j then 1 else 0)) := hmult χ hχ i j
    rw [S.inner_res_ψ_one hχ (S.W.R_mem i.2), S.inner_res_ψ_one hχ (S.W.R_mem j.2)] at h
    have : ((S.ma χ i.1 : ℤ) : ℂ) - ((S.ma χ j.1 : ℤ) : ℂ) =
        (((ε * ((if χ = η i then 1 else 0) - (if χ = η j then 1 else 0)) : ℤ)) : ℂ) := by
      push_cast at h ⊢
      rw [h]
    exact_mod_cast this
  · intro χ hχ i j
    have h : BlocksInnerProduct (S.res χ) (S.ψ (signChar _) i.1) -
        BlocksInnerProduct (S.res χ) (S.ψ (signChar _) j.1) =
        ε' * ((if χ = η' i then 1 else 0) - (if χ = η' j then 1 else 0)) := hmult₂ χ hχ i j
    rw [S.inner_res_ψ_sgn hχ (S.W.R_mem i.2), S.inner_res_ψ_sgn hχ (S.W.R_mem j.2)] at h
    have : ((S.mb χ i.1 : ℤ) : ℂ) - ((S.mb χ j.1 : ℤ) : ℂ) =
        (((ε' * ((if χ = η' i then 1 else 0) - (if χ = η' j then 1 else 0)) : ℤ)) : ℂ) := by
      push_cast at h ⊢
      rw [h]
    exact_mod_cast this
  · intro i j θ hθ
    have h := S.mult_of_res_eq 1 ε (hres i j) θ 1 (one_mem_blocksIrr _) hθ
      (S.ψ_one_mem (S.W.R_mem i.2)) (S.ψ_one_mem (S.W.R_mem j.2))
    rw [S.inner_res_ψ_one (hηmem i) hθ, S.inner_res_ψ_one (hηmem j) hθ] at h
    have : ((S.ma (η i) θ : ℤ) : ℂ) - ((S.ma (η j) θ : ℤ) : ℂ) =
        (((ε * ((if θ = i.1 then 1 else 0) - (if θ = j.1 then 1 else 0)) : ℤ)) : ℂ) := by
      push_cast at h ⊢
      rw [h]
      simp only [S.ψ_eq_iff 1 rfl]
      by_cases h1 : i.1 = θ <;> by_cases h2 : j.1 = θ <;>
        simp only [@eq_comm _ θ, h1, h2, ↓reduceIte]
    exact_mod_cast this
  · intro i j θ hθ
    have h := S.mult_of_res_eq 1 ε (hres i j) θ (signChar _)
      (signChar_mem_blocksIrr S.card_Z) hθ
      (S.ψ_one_mem (S.W.R_mem i.2)) (S.ψ_one_mem (S.W.R_mem j.2))
    rw [S.inner_res_ψ_sgn (hηmem i) hθ, S.inner_res_ψ_sgn (hηmem j) hθ] at h
    simp only [S.ψ_one_ne_sgn (S.W.R_mem i.2) hθ, S.ψ_one_ne_sgn (S.W.R_mem j.2) hθ,
      ↓reduceIte, sub_self, mul_zero, sub_eq_zero] at h
    exact_mod_cast h
  · intro i j θ hθ
    have h := S.mult_of_res_eq (signChar _) ε' (hres₂ i j) θ 1
      (one_mem_blocksIrr _) hθ (S.ψ_sgn_mem (S.W.R_mem i.2)) (S.ψ_sgn_mem (S.W.R_mem j.2))
    rw [S.inner_res_ψ_one (hηmem₂ i) hθ, S.inner_res_ψ_one (hηmem₂ j) hθ] at h
    simp only [Ne.symm (S.ψ_one_ne_sgn hθ (S.W.R_mem i.2)),
      Ne.symm (S.ψ_one_ne_sgn hθ (S.W.R_mem j.2)), ↓reduceIte, sub_self, mul_zero,
      sub_eq_zero] at h
    exact_mod_cast h
  · intro i j θ hθ
    have h := S.mult_of_res_eq (signChar _) ε' (hres₂ i j) θ (signChar _)
      (signChar_mem_blocksIrr S.card_Z) hθ (S.ψ_sgn_mem (S.W.R_mem i.2))
      (S.ψ_sgn_mem (S.W.R_mem j.2))
    rw [S.inner_res_ψ_sgn (hηmem₂ i) hθ, S.inner_res_ψ_sgn (hηmem₂ j) hθ] at h
    have : ((S.mb (η' i) θ : ℤ) : ℂ) - ((S.mb (η' j) θ : ℤ) : ℂ) =
        (((ε' * ((if θ = i.1 then 1 else 0) - (if θ = j.1 then 1 else 0)) : ℤ)) : ℂ) := by
      push_cast at h ⊢
      rw [h]
      simp only [S.ψ_eq_iff _ hsgn1]
      by_cases h1 : i.1 = θ <;> by_cases h2 : j.1 = θ <;>
        simp only [@eq_comm _ θ, h1, h2, ↓reduceIte]
    exact_mod_cast this

end WardSetup

end CFSG.Walter.Ward
