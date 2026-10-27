module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aYAbelian
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aCYtauConcrete
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aYneBot
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aXIrreducible
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aCBY
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aYFix
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aY1Fix
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aY2Fix
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aTauT1
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aZStarFull
public import Certificates.Data.ExceptionalSL3

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.B1_invariant_of_torus
    (h : FF81Hyp b L) (hT : KF_Sp6Torus)
    (hTF : KF_Sp6TorusFree) (hOut : KF_Sp62Out)
    (hnoL : ∀ g : G, g * b * g⁻¹ ∉ L)
    {b₁ b₂ b₃ τ : G}
    (hτL : τ ∈ L) (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hb₁ne : b₁ ≠ 1)
    (hE3 : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hself : L ⊓ CenS (Subgroup.closure ({b₁, b₂, b₃} : Set G)) =
      Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hmono : ∀ n ∈ L, n ∈ Nor (Subgroup.closure ({b₁, b₂, b₃} : Set G)) →
      ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 27)
    (hτ2 : orderOf τ = 2) (hb : τ * b * τ⁻¹ = b)
    (hinv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹)
    {t₁ s c : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))}
    (ht₁X : t₁ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    (hsX : s ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    (hcX : c ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    (ht₁ : t₁ ⟨b, Subgroup.subset_closure (by simp)⟩ =
          ⟨b, Subgroup.subset_closure (by simp)⟩ ∧
        t₁ ⟨b₁, Subgroup.subset_closure (by simp)⟩ =
          (⟨b₁, Subgroup.subset_closure (by simp)⟩)⁻¹ ∧
        t₁ ⟨b₂, Subgroup.subset_closure (by simp)⟩ =
          ⟨b₂, Subgroup.subset_closure (by simp)⟩ ∧
        t₁ ⟨b₃, Subgroup.subset_closure (by simp)⟩ =
          ⟨b₃, Subgroup.subset_closure (by simp)⟩)
    (hs : s ⟨b, Subgroup.subset_closure (by simp)⟩ =
          ⟨b, Subgroup.subset_closure (by simp)⟩ ∧
        s ⟨b₁, Subgroup.subset_closure (by simp)⟩ =
          ⟨b₂, Subgroup.subset_closure (by simp)⟩ ∧
        s ⟨b₂, Subgroup.subset_closure (by simp)⟩ =
          ⟨b₁, Subgroup.subset_closure (by simp)⟩ ∧
        s ⟨b₃, Subgroup.subset_closure (by simp)⟩ =
          ⟨b₃, Subgroup.subset_closure (by simp)⟩)
    (hc : c ⟨b, Subgroup.subset_closure (by simp)⟩ =
          ⟨b, Subgroup.subset_closure (by simp)⟩ ∧
        c ⟨b₁, Subgroup.subset_closure (by simp)⟩ =
          ⟨b₂, Subgroup.subset_closure (by simp)⟩ ∧
        c ⟨b₂, Subgroup.subset_closure (by simp)⟩ =
          ⟨b₃, Subgroup.subset_closure (by simp)⟩ ∧
        c ⟨b₃, Subgroup.subset_closure (by simp)⟩ =
          ⟨b₁, Subgroup.subset_closure (by simp)⟩)
    (hmove : ∃ σ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G)),
      σ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) ∧
      σ ⟨b, Subgroup.subset_closure (by simp)⟩ ∉
        Subgroup.zpowers (⟨b, Subgroup.subset_closure (by simp)⟩ :
          ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))))
    (hB1irr : ∀ U : Subgroup ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G)),
      U ≤ ((Subgroup.closure ({b₁, b₂, b₃} : Set G)).subgroupOf (Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) →
      (∀ σ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G)),
        σ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) →
        σ * FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE3 hb hinv) =
          FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE3 hb hinv) * σ →
        Subgroup.map σ U = U) →
      U = ⊥ ∨ U = ((Subgroup.closure ({b₁, b₂, b₃} : Set G)).subgroupOf (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))) :
    ∀ σ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G)),
      σ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) →
      Subgroup.map σ ((Subgroup.closure ({b₁, b₂, b₃} : Set G)).subgroupOf (Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) =
        (Subgroup.closure ({b₁, b₂, b₃} : Set G)).subgroupOf (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) := by
  intro σ hσX
  by_contra hσne
  classical
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  let B₁ : Subgroup G := Subgroup.closure ({b₁, b₂, b₃} : Set G)
  have hbB : b ∈ B := Subgroup.subset_closure (by simp)
  have hb₁B : b₁ ∈ B := Subgroup.subset_closure (by simp)
  have hb₂B : b₂ ∈ B := Subgroup.subset_closure (by simp)
  have hb₃B : b₃ ∈ B := Subgroup.subset_closure (by simp)
  let bB : ↥B := ⟨b, hbB⟩
  let b₁B : ↥B := ⟨b₁, hb₁B⟩
  let b₂B : ↥B := ⟨b₂, hb₂B⟩
  let b₃B : ↥B := ⟨b₃, hb₃B⟩
  let X : Subgroup (MulAut ↥B) := FF81X B
  have hτN : τ ∈ Nor B := FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE3 hb hinv
  let τX : MulAut ↥B := FF81X.tau hτN
  have hτXmem : τX ∈ X := by
    show τX ∈ FF81X B
    exact ⟨⟨τ, hτN⟩, rfl⟩
  have hττ : τ * τ = 1 := by
    have hp := pow_orderOf_eq_one τ
    rw [hτ2, pow_two] at hp
    exact hp
  have hτX2 : τX * τX = 1 := by
    show Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩ *
      Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩ = 1
    rw [← map_mul]
    have h2 : (⟨τ, hτN⟩ : ↥(Nor B)) * ⟨τ, hτN⟩ = 1 := Subtype.ext hττ
    rw [h2, map_one]
  have hτXb : τX bB = bB := by
    apply Subtype.ext
    show ((Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩) bB : G) = (bB : G)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simpa [bB] using hb
  have hτX₁ : τX b₁B = b₁B⁻¹ := by
    apply Subtype.ext
    show ((Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩) b₁B : G) = (b₁B : G)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simpa [b₁B] using hinv.1
  have hτX₂ : τX b₂B = b₂B⁻¹ := by
    apply Subtype.ext
    show ((Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩) b₂B : G) = (b₂B : G)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simpa [b₂B] using hinv.2.1
  have hτX₃ : τX b₃B = b₃B⁻¹ := by
    apply Subtype.ext
    show ((Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩) b₃B : G) = (b₃B : G)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simpa [b₃B] using hinv.2.2
  have hB₁_eq : B₁ = Subgroup.closure ({b₁, b₂, b₃} : Set G) := rfl
  have hB_eq : B = Subgroup.zpowers b ⊔ B₁ := by
    show Subgroup.closure ({b, b₁, b₂, b₃} : Set G) =
      Subgroup.zpowers b ⊔ Subgroup.closure ({b₁, b₂, b₃} : Set G)
    have hset : ({b, b₁, b₂, b₃} : Set G) = ({b} ∪ {b₁, b₂, b₃} : Set G) := by
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [Subgroup.zpowers_eq_closure, ← Subgroup.closure_union, hset]
  have hE4 : IsElemAb 3 4 B := FF81Hyp.isElemAb_B4 h hb₁ hb₂ hb₃ hE3 hbB
  have hB1not : ∃ σ' : MulAut ↥B, σ' ∈ X ∧
      Subgroup.map σ' (B₁.subgroupOf B) ≠ B₁.subgroupOf B :=
    ⟨σ, hσX, hσne⟩
  have hirr : ∀ U : Subgroup ↥B, (∀ σ : MulAut ↥B, σ ∈ X → Subgroup.map σ U = U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hU
    exact FF81Hyp.X_irreducible_of_move hB_eq hB₁_eq hE4 hbB hb₁B hb₂B hb₃B
      hτXmem hτX2 hτXb hτX₁ hτX₂ hτX₃ hB1irr hmove hB1not hU
  have hZ := FF81Hyp.X_eq_oddCore_mul_centralizer_tau_of_no_conj h hnoL hτL hb₁ hb₂ hb₃
    hE3 hb₁ne hτ2 hb hinv hbB hb₁B hb₂B hb₃B hτXmem hτX2 rfl
  have hmap : ∀ σ : MulAut ↥B, σ ∈ X → σ * τX = τX * σ →
      Subgroup.map σ (Subgroup.zpowers bB) = Subgroup.zpowers bB :=
    fun σ hσ hcomm => FF81Hyp.cen_X_tau_maps_b h hτL hb₁ hb₂ hb₃ hE3 hτ2 hb hinv hbB hσ hcomm
  have hYne : oddCore X ≠ ⊥ :=
    FF81Hyp.oddCore_ne_bot_of_move hτXmem hZ hbB hmove hmap
  have hCY : ∀ g : X, g ∈ oddCore X →
      (g : MulAut ↥B) * τX = τX * (g : MulAut ↥B) → (g : MulAut ↥B) = 1 :=
    fun g hg hcomm => FF81Hyp.CYtau_eq_one h hTF hOut hτL hb₁ hb₂ hb₃ hE3 hself hmono hrk
      hE4 hτ2 hb hinv hbB hb₁B hb₂B hb₃B hτN ht₁X hsX hcX ht₁ hs hc hg hcomm
  have hYab : ∀ a b : X, a ∈ oddCore X → b ∈ oddCore X → a * b = b * a :=
    FF81Hyp.oddCore_commute_of_CYtau hτXmem hτX2 hCY
  have hB3 : IsPGroup 3 ↥B := by
    haveI : IsElementaryAbelian 3 ↥B := hE4.1
    exact IsElementaryAbelian.isPGroup 3 ↥B
  have hBnt : Nontrivial ↥B := by
    refine ⟨bB, 1, ?_⟩
    intro h1
    have hb1 : b = 1 := congrArg (fun x : ↥B => (x : G)) h1
    have hord := h.ord
    rw [hb1, orderOf_one] at hord
    norm_num at hord
  have h3 : ¬ 3 ∣ Nat.card ↥(oddCore X) :=
    FF81Hyp.not_three_dvd_oddCore hB3 hBnt hirr hYab
  let Yb : Subgroup (MulAut ↥B) := (oddCore X).map X.subtype
  have hYX : Yb ≤ X := Subgroup.map_subtype_le (oddCore X)
  have hYnorm : ∀ σ : MulAut ↥B, σ ∈ X → ∀ y : MulAut ↥B, y ∈ Yb →
      σ * y * σ⁻¹ ∈ Yb := by
    intro σ hσ y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨⟨σ, hσ⟩ * g * ⟨σ, hσ⟩⁻¹,
      (oddCore_normal X).conj_mem g hg ⟨σ, hσ⟩, rfl⟩
  have hYne' : Yb ≠ ⊥ := by
    intro hbot
    apply hYne
    have h' : (oddCore X).map X.subtype = (⊥ : Subgroup ↥X).map X.subtype := by
      show Yb = (⊥ : Subgroup ↥X).map X.subtype
      rw [hbot, Subgroup.map_bot]
    exact Subgroup.map_injective X.subtype_injective h'
  have hCBY := FF81Hyp.cen_eq_bot_of_irreducible hYX hYnorm hYne' hirr
  have hb₁B_ne : b₁B ≠ 1 := by
    intro h1
    apply hb₁ne
    have h := congrArg (fun x : ↥B => (x : G)) h1
    simpa [b₁B] using h
  have hYfix : ∀ y : X, y ∈ oddCore X → (y : MulAut ↥B) b₁B = b₁B := by
    intro y hy
    haveI hEab : IsElementaryAbelian 3 ↥B := hE4.1
    have hpow3 : ∀ x : ↥B, x ^ 3 = 1 := fun x =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 ↥B) x
    have hbB_ne : bB ≠ 1 := by
      intro h1
      have hb1 : b = 1 := congrArg (fun x : ↥B => (x : G)) h1
      have hord := h.ord
      rw [hb1, orderOf_one] at hord
      norm_num at hord
    have hb₁B_ne : b₁B ≠ 1 := by
      intro h1
      apply hb₁ne
      have h := congrArg (fun x : ↥B => (x : G)) h1
      simpa [b₁B] using h
    have hord_bB : orderOf bB = 3 := orderOf_eq_prime (hpow3 bB) hbB_ne
    have hord_b₁B : orderOf b₁B = 3 := orderOf_eq_prime (hpow3 b₁B) hb₁B_ne
    have hcard_bB : Nat.card (Subgroup.zpowers bB) = 3 := by
      rw [Nat.card_zpowers, hord_bB]
    have hcard_b₁B : Nat.card (Subgroup.zpowers b₁B) = 3 := by
      rw [Nat.card_zpowers, hord_b₁B]
    have ht₁b : t₁ bB = bB := by simpa [bB] using ht₁.1
    have ht₁b₁ : t₁ b₁B = b₁B⁻¹ := by simpa [b₁B] using ht₁.2.1
    have ht₁b₂ : t₁ b₂B = b₂B := by simpa [b₂B] using ht₁.2.2.1
    have ht₁b₃ : t₁ b₃B = b₃B := by simpa [b₃B] using ht₁.2.2.2
    have hgen_top : Subgroup.closure ({bB, b₁B, b₂B, b₃B} : Set ↥B) = ⊤ := by
      have hset : ({bB, b₁B, b₂B, b₃B} : Set ↥B) =
          ((↑) : ↥B → G) ⁻¹' ({b, b₁, b₂, b₃} : Set G) := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
        constructor
        · rintro (rfl | rfl | rfl | rfl) <;> simp [bB, b₁B, b₂B, b₃B]
        · rintro (h | h | h | h)
          · exact Or.inl (Subtype.ext (by simpa [bB] using h))
          · exact Or.inr (Or.inl (Subtype.ext (by simpa [b₁B] using h)))
          · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by simpa [b₂B] using h))))
          · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by simpa [b₃B] using h))))
      rw [hset]
      exact Subgroup.closure_closure_coe_preimage
    have ht₁2 : t₁ * t₁ = 1 := by
      have hgen : Set.EqOn ((t₁ * t₁ : MulAut ↥B) : ↥B →* ↥B)
          ((1 : MulAut ↥B) : ↥B →* ↥B) ({bB, b₁B, b₂B, b₃B} : Set ↥B) := by
        intro x hx
        rcases hx with rfl | rfl | rfl | rfl
        · simp [MulAut.mul_apply, ht₁b]
        · simp [MulAut.mul_apply, ht₁b₁]
        · simp [MulAut.mul_apply, ht₁b₂]
        · simp [MulAut.mul_apply, ht₁b₃]
      have h := MonoidHom.eqOn_closure hgen
      rw [hgen_top] at h
      ext x
      have hx := h (Subgroup.mem_top x)
      simpa using hx
    have hcommτt : t₁ * τX = τX * t₁ := by
      have hgen : Set.EqOn ((t₁ * τX : MulAut ↥B) : ↥B →* ↥B)
          ((τX * t₁ : MulAut ↥B) : ↥B →* ↥B) ({bB, b₁B, b₂B, b₃B} : Set ↥B) := by
        intro x hx
        rcases hx with rfl | rfl | rfl | rfl
        · simp [MulAut.mul_apply, ht₁b, hτXb]
        · simp [MulAut.mul_apply, ht₁b₁, hτX₁]
        · simp [MulAut.mul_apply, ht₁b₂, hτX₂]
        · simp [MulAut.mul_apply, ht₁b₃, hτX₃]
      have h := MonoidHom.eqOn_closure hgen
      rw [hgen_top] at h
      ext x
      have hx := h (Subgroup.mem_top x)
      simpa using hx
    have hτt₁2 : (τX * t₁) * (τX * t₁) = 1 := by
      calc (τX * t₁) * (τX * t₁) = τX * (t₁ * τX) * t₁ := by group
        _ = τX * (τX * t₁) * t₁ := by rw [hcommτt]
        _ = (τX * τX) * (t₁ * t₁) := by group
        _ = 1 := by rw [hτX2, ht₁2, one_mul]
    have hτt₁inv : (τX * t₁)⁻¹ = τX * t₁ := inv_eq_of_mul_eq_one_right hτt₁2
    let Y : Subgroup ↥X := oddCore X
    haveI hYnormal : Y.Normal := oddCore_normal X
    letI hYcomm : CommGroup ↥Y :=
      { (inferInstance : Group ↥Y) with
        mul_comm := fun a b => Subtype.ext (hYab (a : ↥X) (b : ↥X) a.2 b.2) }
    have hYodd : Odd (Nat.card ↥Y) := CFSG.ABGLocalTools.odd_card_oddCore (H := ↥X)
    let τX' : X := ⟨τX, hτXmem⟩
    let t₁' : X := ⟨t₁, ht₁X⟩
    have hτX'2 : τX' * τX' = 1 := Subtype.ext hτX2
    have ht₁'2 : t₁' * t₁' = 1 := Subtype.ext ht₁2
    have hcommX : τX' * t₁' = t₁' * τX' := Subtype.ext hcommτt.symm
    let τY : @MulAut ↥Y hYcomm.toMul :=
      { toFun := fun z => MulAut.conjNormal τX' z
        invFun := fun z => MulAut.conjNormal τX'⁻¹ z
        left_inv := fun z => by
          change MulAut.conjNormal τX'⁻¹ (MulAut.conjNormal τX' z) = z
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
        right_inv := fun z => by
          change MulAut.conjNormal τX' (MulAut.conjNormal τX'⁻¹ z) = z
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rfl
        map_mul' := fun z w => by
          change MulAut.conjNormal τX' (z * w) =
            MulAut.conjNormal τX' z * MulAut.conjNormal τX' w
          rw [map_mul] }
    let tY : @MulAut ↥Y hYcomm.toMul :=
      { toFun := fun z => MulAut.conjNormal t₁' z
        invFun := fun z => MulAut.conjNormal t₁'⁻¹ z
        left_inv := fun z => by
          change MulAut.conjNormal t₁'⁻¹ (MulAut.conjNormal t₁' z) = z
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
        right_inv := fun z => by
          change MulAut.conjNormal t₁' (MulAut.conjNormal t₁'⁻¹ z) = z
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rfl
        map_mul' := fun z w => by
          change MulAut.conjNormal t₁' (z * w) =
            MulAut.conjNormal t₁' z * MulAut.conjNormal t₁' w
          rw [map_mul] }
    have hτY2 : τY * τY = 1 := by
      apply MulEquiv.ext
      intro z
      change MulAut.conjNormal τX' (MulAut.conjNormal τX' z) = z
      rw [← MulAut.mul_apply, ← map_mul, hτX'2, map_one]
      rfl
    have htY2 : tY * tY = 1 := by
      apply MulEquiv.ext
      intro z
      change MulAut.conjNormal t₁' (MulAut.conjNormal t₁' z) = z
      rw [← MulAut.mul_apply, ← map_mul, ht₁'2, map_one]
      rfl
    have hcommY : τY * tY = tY * τY := by
      apply MulEquiv.ext
      intro z
      change MulAut.conjNormal τX' (MulAut.conjNormal t₁' z) =
        MulAut.conjNormal t₁' (MulAut.conjNormal τX' z)
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hcommX]
    have hfreeY : ∀ z : ↥Y, τY z = z → z = 1 := by
      intro z hz
      have hz' : MulAut.conjNormal τX' z = z := hz
      have hzX : (z : X) * τX' = τX' * (z : X) := by
        have h := congrArg (fun w : ↥Y => (w : X)) hz'
        rw [MulAut.conjNormal_apply] at h
        have hτX'inv : τX'⁻¹ = τX' := inv_eq_of_mul_eq_one_right hτX'2
        calc (z : X) * τX' = (τX' * (z : X) * (τX')⁻¹) * τX' := by rw [h]
          _ = τX' * (z : X) := by
              rw [show τX' * (z : X) * (τX')⁻¹ * τX'
                  = τX' * (z : X) * ((τX')⁻¹ * τX') by group,
                inv_mul_cancel, mul_one]
      have h1 : ((z : X) : MulAut ↥B) = 1 := by
        have hmem : (z : X) ∈ oddCore X := z.2
        have hc := hCY (z : X) hmem (by
          have h2 := congrArg (fun w : X => (w : MulAut ↥B)) hzX
          simpa using h2)
        simpa using hc
      exact Subtype.ext (Subtype.ext h1)
    obtain ⟨a, bY, ha, hb, hyab⟩ :=
      CFSG.exists_fixed_mul_fixed_of_fixedPointFree_mul (A := ↥Y) hYodd τY tY hτY2 htY2
        hcommY hfreeY ⟨y, hy⟩
    have ha' : MulAut.conjNormal (τX' * t₁') a = a := by
      have h1 : MulAut.conjNormal τX' (MulAut.conjNormal t₁' a) = a := by
        have h := ha
        change τY (tY a) = a at h
        exact h
      rw [map_mul]
      exact h1
    have ha_comm : (a : MulAut ↥B) * (τX * t₁) = (τX * t₁) * (a : MulAut ↥B) := by
      have h3 : ((τX' * t₁') : X) * (a : X) * ((τX' * t₁') : X)⁻¹ = (a : X) := by
        have h := congrArg (fun w : ↥Y => (w : X)) ha'
        rw [MulAut.conjNormal_apply] at h
        exact h
      have h4 : (τX * t₁) * (a : MulAut ↥B) * (τX * t₁)⁻¹ = (a : MulAut ↥B) := by
        simpa using congrArg (fun w : X => (w : MulAut ↥B)) h3
      have h4' : (τX * t₁) * (a : MulAut ↥B) * (τX * t₁) = (a : MulAut ↥B) := by
        simpa [hτt₁inv] using h4
      calc (a : MulAut ↥B) * (τX * t₁)
          = ((τX * t₁) * (a : MulAut ↥B) * (τX * t₁)) * (τX * t₁) := by rw [h4']
        _ = (τX * t₁) * (a : MulAut ↥B) * ((τX * t₁) * (τX * t₁)) := by group
        _ = (τX * t₁) * (a : MulAut ↥B) := by rw [hτt₁2, mul_one]
    have hb' : MulAut.conjNormal t₁' bY = bY := hb
    have ht₁inv : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right ht₁2
    have hb_comm : (bY : MulAut ↥B) * t₁ = t₁ * (bY : MulAut ↥B) := by
      have h3 : (t₁' : X) * (bY : X) * (t₁' : X)⁻¹ = (bY : X) := by
        have h := congrArg (fun w : ↥Y => (w : X)) hb'
        rw [MulAut.conjNormal_apply] at h
        exact h
      have h4 : t₁ * (bY : MulAut ↥B) * t₁⁻¹ = (bY : MulAut ↥B) := by
        simpa using congrArg (fun w : X => (w : MulAut ↥B)) h3
      have h4' : t₁ * (bY : MulAut ↥B) * t₁ = (bY : MulAut ↥B) := by
        simpa [ht₁inv] using h4
      calc (bY : MulAut ↥B) * t₁
          = (t₁ * (bY : MulAut ↥B) * t₁) * t₁ := by rw [h4']
        _ = t₁ * (bY : MulAut ↥B) * (t₁ * t₁) := by group
        _ = t₁ * (bY : MulAut ↥B) := by rw [ht₁2, mul_one]
    have hb_not_B₁ : b ∉ B₁ := by
      intro hbB₁
      have hB_le_B₁ : B ≤ B₁ := by
        show Subgroup.closure ({b, b₁, b₂, b₃} : Set G) ≤ B₁
        refine (Subgroup.closure_le B₁).mpr ?_
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact hbB₁
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
      have hB₁_le_B : B₁ ≤ B := by
        show Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ B
        refine (Subgroup.closure_le B).mpr ?_
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
      have hBeq : B = B₁ := le_antisymm hB_le_B₁ hB₁_le_B
      have h81 : Nat.card B = 81 := by
        have h := hE4.2
        rw [h]
        norm_num
      have h27 : Nat.card B₁ = 27 := by
        have h := hE3.2
        rw [h]
        norm_num
      rw [hBeq, h27] at h81
      norm_num at h81
    have hbB_not_zp : bB ∉ Subgroup.zpowers b₁B := by
      intro hmem
      apply hb_not_B₁
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hval : b = b₁ ^ k := by
        have h := congrArg (fun x : ↥B => (x : G)) hk
        simpa [bB, b₁B, Subgroup.coe_zpow] using h.symm
      rw [hval]
      exact B₁.zpow_mem (Subgroup.subset_closure (by simp)) k
    have hinf : Subgroup.zpowers bB ⊓ Subgroup.zpowers b₁B = ⊥ := by
      by_contra hne
      have hdvd : Nat.card (Subgroup.zpowers bB ⊓ Subgroup.zpowers b₁B : Subgroup ↥B) ∣ 3 := by
        rw [← hcard_b₁B]
        exact Subgroup.card_dvd_of_le (inf_le_right :
          Subgroup.zpowers bB ⊓ Subgroup.zpowers b₁B ≤ Subgroup.zpowers b₁B)
      have hcard_int : Nat.card (Subgroup.zpowers bB ⊓ Subgroup.zpowers b₁B : Subgroup ↥B) = 3 := by
        have hne1 : Nat.card (Subgroup.zpowers bB ⊓ Subgroup.zpowers b₁B : Subgroup ↥B) ≠ 1 := by
          intro h1
          exact hne ((Subgroup.eq_bot_iff_card _).mpr h1)
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd h hne1
        · exact h
      have heq : Subgroup.zpowers bB ⊓ Subgroup.zpowers b₁B = Subgroup.zpowers b₁B :=
        Subgroup.eq_of_le_of_card_ge (inf_le_right :
          Subgroup.zpowers bB ⊓ Subgroup.zpowers b₁B ≤ Subgroup.zpowers b₁B)
          (by rw [hcard_b₁B, hcard_int])
      have hle' : Subgroup.zpowers b₁B ≤ Subgroup.zpowers bB := by
        rw [← heq]
        exact (inf_le_left : Subgroup.zpowers bB ⊓ Subgroup.zpowers b₁B ≤ Subgroup.zpowers bB)
      have heq' : Subgroup.zpowers b₁B = Subgroup.zpowers bB :=
        Subgroup.eq_of_le_of_card_ge hle' (by rw [hcard_bB, hcard_b₁B])
      apply hbB_not_zp
      rw [heq']
      exact Subgroup.mem_zpowers bB
    let C₁ : Subgroup ↥B := Subgroup.zpowers bB ⊔ Subgroup.zpowers b₁B
    have hcardC₁ : Nat.card C₁ = 9 := by
      obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
        (Subgroup.zpowers bB) (Subgroup.zpowers b₁B) (fun x _ y _ => mul_comm' x y)
      rw [hinf, Subgroup.card_bot, mul_one, hcard_bB, hcard_b₁B] at hcard
      simpa [C₁] using hcard
    have hC₁ea : IsElementaryAbelian 3 C₁ :=
      { toIsMulCommutative := IsMulCommutative.of_comm (fun x y => mul_comm' x y)
        exponent_dvd_p := by
          rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
          intro x
          apply Subtype.ext
          exact hpow3 (x : ↥B) }
    have hC : IsElemAb 3 2 C₁ := by
      refine ⟨hC₁ea, ?_⟩
      rw [hcardC₁]
      norm_num
    have hBsup1 : B = (Subgroup.zpowers b ⊔ Subgroup.zpowers b₁) ⊔
        (Subgroup.zpowers b₂ ⊔ Subgroup.zpowers b₃) := by
      show Subgroup.closure ({b, b₁, b₂, b₃} : Set G) =
        (Subgroup.zpowers b ⊔ Subgroup.zpowers b₁) ⊔
          (Subgroup.zpowers b₂ ⊔ Subgroup.zpowers b₃)
      rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
      simp only [← Subgroup.closure_union]
      congr 1
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]
    have hBsup2 : B = (Subgroup.zpowers b ⊔ (Subgroup.zpowers b₂ ⊔ Subgroup.zpowers b₃)) ⊔
        Subgroup.zpowers b₁ := by
      show Subgroup.closure ({b, b₁, b₂, b₃} : Set G) =
        (Subgroup.zpowers b ⊔ (Subgroup.zpowers b₂ ⊔ Subgroup.zpowers b₃)) ⊔
          Subgroup.zpowers b₁
      rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
      simp only [← Subgroup.closure_union]
      congr 1
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc,
        or_comm, or_left_comm]
    let Y₁ : Subgroup (MulAut ↥B) :=
      Yb ⊓ Subgroup.centralizer ({τX * t₁} : Set (MulAut ↥B))
    have hCmem : ∀ v : ↥B, v ∈ C₁ ↔ (τX * t₁) v = v := by
      intro v
      exact (FF81Hyp.fix_tau_mul_t1 hBsup1 hE4 hbB hb₁B hb₂B hb₃B
        hτXb hτX₁ hτX₂ hτX₃ ht₁.1 ht₁.2.1 ht₁.2.2.1 ht₁.2.2.2 v).symm
    have hYb_odd : Odd (Nat.card Yb) := by
      have hcard : Nat.card Yb = Nat.card ↥(oddCore X) := by
        show Nat.card ((oddCore X).map X.subtype) = Nat.card ↥(oddCore X)
        rw [Subgroup.card_map_of_injective X.subtype_injective]
      rw [hcard]
      exact hYodd
    have hcopY : Nat.Coprime (Nat.card ↥(oddCore X)) 6 := by
      have h2 : Nat.Coprime (Nat.card ↥(oddCore X)) 2 := hYodd.coprime_two_right
      have h3' : Nat.Coprime (Nat.card ↥(oddCore X)) 3 := by
        rw [Nat.coprime_comm]
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
      have h6 : Nat.Coprime (Nat.card ↥(oddCore X)) (2 * 3) :=
        Nat.coprime_mul_iff_right.mpr ⟨h2, h3'⟩
      simpa using h6
    have hcopY₁ : Nat.Coprime (Nat.card Y₁) 6 := by
      have hdvd : Nat.card Y₁ ∣ Nat.card Yb := Subgroup.card_dvd_of_le inf_le_left
      have hcard : Nat.card Yb = Nat.card ↥(oddCore X) := by
        show Nat.card ((oddCore X).map X.subtype) = Nat.card ↥(oddCore X)
        rw [Subgroup.card_map_of_injective X.subtype_injective]
      have hdvd' : Nat.card Y₁ ∣ Nat.card ↥(oddCore X) := by rwa [hcard] at hdvd
      exact hcopY.coprime_dvd_left hdvd'
    have haY₁ : (a : MulAut ↥B) ∈ Y₁ := by
      refine ⟨Subgroup.mem_map_of_mem X.subtype a.2, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr ha_comm
    have ha_fix : (a : MulAut ↥B) b₁B = b₁B := by
      have hres := MulAut.eq_on_fixed_of_commute_card_nine (Y₁ := Y₁) (τ := τX) (t := t₁)
        (C := C₁) hCmem hC hcopY₁ (fun z hz =>
          Subgroup.mem_centralizer_singleton_iff.mp hz.2)
      exact hres (a : MulAut ↥B) haY₁ b₁B
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers b₁B))
    let Y₂ : Subgroup (MulAut ↥B) :=
      Yb ⊓ Subgroup.centralizer ({t₁} : Set (MulAut ↥B))
    have hY₂_odd : Odd (Nat.card Y₂) := by
      have hdvd : Nat.card Y₂ ∣ Nat.card Yb := Subgroup.card_dvd_of_le inf_le_left
      exact Odd.of_dvd_nat hYb_odd hdvd
    obtain ⟨himage, hcover⟩ := FF81Hyp.commutator_t1 hBsup2 hE4 hbB hb₁B hb₂B hb₃B
      ht₁.1 ht₁.2.1 ht₁.2.2.1 ht₁.2.2.2
    have hbY₂ : (bY : MulAut ↥B) ∈ Y₂ := by
      refine ⟨Subgroup.mem_map_of_mem X.subtype bY.2, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr hb_comm
    have hb_fix : (bY : MulAut ↥B) b₁B = b₁B := by
      have hres := MulAut.eq_on_zpowers_of_commute_card_three (Y₂ := Y₂) (t := t₁)
        (b₁ := b₁B) hY₂_odd hcard_b₁B (fun z hz =>
          Subgroup.mem_centralizer_singleton_iff.mp hz.2) himage hcover
      exact hres (bY : MulAut ↥B) hbY₂
    have hy_eq : (y : MulAut ↥B) = (a : MulAut ↥B) * (bY : MulAut ↥B) := by
      have h := congrArg (fun w : ↥Y => (w : X)) hyab
      have h2 := congrArg (fun w : X => (w : MulAut ↥B)) h
      simpa using h2
    calc (y : MulAut ↥B) b₁B
        = ((a : MulAut ↥B) * (bY : MulAut ↥B)) b₁B := by rw [hy_eq]
      _ = (a : MulAut ↥B) ((bY : MulAut ↥B) b₁B) :=
            MulAut.mul_apply ↥B (a : MulAut ↥B) (bY : MulAut ↥B) b₁B
      _ = (a : MulAut ↥B) b₁B := by rw [hb_fix]
      _ = b₁B := ha_fix
  have hfixYb : ∀ y : MulAut ↥B, y ∈ Yb → y b₁B = b₁B := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    exact hYfix g hg
  exact hb₁B_ne (hCBY b₁B hfixYb)

end CFSG.RankThree.PartTwo.Sec21.FF81
