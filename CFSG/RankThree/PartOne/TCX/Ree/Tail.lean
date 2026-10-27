module

public import CFSG.RankThree.PartOne.TCX.Ree.Engine
public import CFSG.RankThree.PartOne.TCX.Ree.Claims

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.TCX.F4
open CFSG.RankThree.PartOne.TCX
open CFSG.Assembly.LowTwoRank (StatedLieTag)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Phi

variable {τ : Tag} {C : Type} [Group C] {L : Type} [Field L]

theorem phi0_psiG {ι : C →* ModGL τ L} (hιC : ∀ y, ι y ∈ adjointGroup τ L)
    (F₀ : MulAut (adjointGroup τ L)) (α₀ : MulAut C)
    (hα₀ : ∀ y, ι (α₀ y) = Fext F₀ (ι y)) {g₀ n₀ : ModGL τ L} (hg₀C : g₀ ∈ adjointGroup τ L)
    (hg₀ : Fext F₀ g₀ = g₀ * n₀) (k : ℕ) (y : C) :
    (fun v => n₀ * Fext F₀ v * n₀⁻¹)^[k] (psiG ι g₀ 1 y) = psiG ι g₀ 1 ((α₀ ^ k) y) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, psiG_intertwine_R hιC F₀ α₀ hα₀ hg₀C hg₀ (map_one α₀) y, ih,
      pow_succ, MulAut.mul_apply]

theorem exists_psiG_of_mem_Rg {ι : C →* ModGL τ L} {g₀ u : ModGL τ L} (hu : u ∈ Rg ι g₀) :
    ∃ y : C, u = psiG ι g₀ 1 y := by
  obtain ⟨y, hy⟩ := mem_Rg.1 hu
  refine ⟨y, ?_⟩
  rw [psiG_apply, one_mul, inv_one, mul_one, hy]
  group

end Phi

section Tail

variable {τ : Tag} {C : Type} [Group C] [Finite C] {L : Type} [Field L]

theorem singleLayerData_of_layer (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hιC : ∀ y, ι y ∈ adjointGroup τ L) (F₀ : MulAut (adjointGroup τ L)) (α₀ : MulAut C)
    (hα₀ : ∀ y, ι (α₀ y) = Fext F₀ (ι y)) {p : ℕ} (hα₀p : α₀ ^ p = 1) (hp : p.Prime)
    (hp2 : p ≠ 2) {g₀ n₀ : ModGL τ L} (hg₀C : g₀ ∈ adjointGroup τ L)
    (hg₀ : Fext F₀ g₀ = g₀ * n₀)
    (hodd : ∀ h ∈ torusGroup τ L, ∃ m : ℕ, Odd m ∧ h ^ m = 1)
    (hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    (hQS : ∀ u ∈ rootSpan τ L S, n₀ * Fext F₀ u * n₀⁻¹ ∈ rootSpan τ L S)
    (hPq : CFSG.IsQuasisimple ↥(rootSpan τ L S ⊓ Rg ι g₀))
    (hPcent : ∀ q ∈ rootSpan τ L S, (∀ u ∈ rootSpan τ L S ⊓ Rg ι g₀, q * u = u * q) → q = 1)
    (hmodelP : ∃ (t' : StatedLieTag) (n' f'' : ℕ), 1 ≤ f'' ∧
      LieModel (↥(rootSpan τ L S ⊓ Rg ι g₀) ⧸ Subgroup.center ↥(rootSpan τ L S ⊓ Rg ι g₀))
        t' n' 2 (p * f''))
    {e₁ e₂ : ModGL τ L} (he₁ : e₁ ∈ rootSpan τ L S ⊓ Rg ι g₀)
    (he₂ : e₂ ∈ rootSpan τ L S ⊓ Rg ι g₀) (hf₁ : n₀ * Fext F₀ e₁ * n₀⁻¹ = e₁)
    (hf₂ : n₀ * Fext F₀ e₂ * n₀⁻¹ = e₂) (ho₁ : ∃ k : ℕ, orderOf e₁ = 2 ^ k)
    (ho₂ : ∃ k : ℕ, orderOf e₂ = 2 ^ k) (hnc : e₁ * e₂ ≠ e₂ * e₁)
    (h2P : ∀ d ∈ rootSpan τ L S ⊓ Rg ι g₀, d * e₁ = e₁ * d → ∃ k : ℕ, orderOf d = 2 ^ k)
    (hmoveP : ∃ u ∈ rootSpan τ L S ⊓ Rg ι g₀, n₀ * Fext F₀ u * n₀⁻¹ ≠ u)
    {x : C} (hx : orderOf x = p) (c : C) (hcα : α₀ c = c)
    (hc : g₀⁻¹ * ι (c * x * c⁻¹) * g₀ ∈ torusGroup τ L ⊓
      Subgroup.centralizer (rootSpan τ L S : Set (ModGL τ L)))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = g₀⁻¹ * ι (c * x * c⁻¹) * g₀ →
      rootCharKernel a ⊆ S) :
    SingleLayerData p α₀ (Subgroup.centralizer ({x} : Set C)) := by
  classical
  set P : Subgroup (ModGL τ L) := rootSpan τ L S ⊓ Rg ι g₀ with hPdef
  have hPadj : ∀ u ∈ P, u ∈ adjointGroup τ L := fun u hu =>
    CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L S (Subgroup.mem_inf.1 hu).1
  have hφmem : ∀ u ∈ P, n₀ * Fext F₀ u * n₀⁻¹ ∈ P := by
    intro u hu
    obtain ⟨huQ, huR⟩ := Subgroup.mem_inf.1 hu
    refine Subgroup.mem_inf.2 ⟨hQS u huQ, ?_⟩
    obtain ⟨y, rfl⟩ := exists_psiG_of_mem_Rg huR
    have := phi0_psiG hιC F₀ α₀ hα₀ hg₀C hg₀ 1 y
    rw [Function.iterate_one, pow_one] at this
    rw [this]
    exact psiG_mem_Rg ι g₀ 1 _
  let τ' : ↥P →* ↥P :=
    { toFun := fun u => ⟨n₀ * Fext F₀ (u : ModGL τ L) * n₀⁻¹, hφmem _ u.2⟩
      map_one' := by
        apply Subtype.ext
        change n₀ * Fext F₀ 1 * n₀⁻¹ = 1
        rw [Fext_one]
        group
      map_mul' := fun u v => by
        apply Subtype.ext
        change n₀ * Fext F₀ ((u : ModGL τ L) * v) * n₀⁻¹ =
          n₀ * Fext F₀ (u : ModGL τ L) * n₀⁻¹ * (n₀ * Fext F₀ (v : ModGL τ L) * n₀⁻¹)
        rw [Fext_mul F₀ (hPadj _ u.2) (hPadj _ v.2)]
        group }
  have hτ' : ∀ u : ↥P, ((τ' u : ↥P) : ModGL τ L) = n₀ * Fext F₀ (u : ModGL τ L) * n₀⁻¹ :=
    fun u => rfl
  have hτp : ∀ u : ↥P, (⇑τ')^[p] u = u := by
    intro u
    apply Subtype.ext
    have hit : ∀ (k : ℕ) (v : ↥P), (((⇑τ')^[k] v : ↥P) : ModGL τ L) =
        (fun w => n₀ * Fext F₀ w * n₀⁻¹)^[k] (v : ModGL τ L) := by
      intro k
      induction k with
      | zero => intro v; rfl
      | succ k ih =>
        intro v
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
        rfl
    rw [hit]
    obtain ⟨y, hy⟩ := exists_psiG_of_mem_Rg (Subgroup.mem_inf.1 u.2).2
    rw [hy, phi0_psiG hιC F₀ α₀ hα₀ hg₀C hg₀ p y, hα₀p]
    rfl
  let e₁' : ↥P := ⟨e₁, he₁⟩
  let e₂' : ↥P := ⟨e₂, he₂⟩
  have hclaims : ∀ {G : Type} [Group G] (α : MulAut G) (φ : ↥P →* G), Function.Injective φ →
      (∀ d, α (φ d) = φ (τ' d)) → ∀ Q : Subgroup G, φ.range = Q → LayerClaimsF4 p α Q := by
    intro G _ α φ hφ hαφ Q hQ
    refine layerClaims_of_pair hp hp2 τ' hτp hmodelP (e₁ := e₁') (e₂ := e₂')
      (Subtype.ext hf₁) (Subtype.ext hf₂)
      (by obtain ⟨k, hk⟩ := ho₁; exact ⟨k, by rw [← hk]; exact (Subgroup.orderOf_coe e₁').symm⟩)
      (by obtain ⟨k, hk⟩ := ho₂; exact ⟨k, by rw [← hk]; exact (Subgroup.orderOf_coe e₂').symm⟩)
      (fun h => hnc (congrArg Subtype.val h))
      (fun d₀ hd => by
        obtain ⟨k, hk⟩ := h2P d₀ d₀.2 (congrArg Subtype.val hd)
        exact ⟨k, by rw [← hk, Subgroup.orderOf_coe]⟩) ?_ α φ hφ hαφ hQ
    obtain ⟨u, hu, hne⟩ := hmoveP
    exact ⟨⟨u, hu⟩, fun h => hne (congrArg Subtype.val h)⟩
  refine singleLayerData_of_engineR ι hι hιC F₀ α₀ hα₀ hg₀C hg₀ hodd hp hstab hS hSn hPq hPcent hx c
    hcα hc hkerZ ⟨↥P, inferInstance, P.subtype, τ', Subtype.val_injective, ?_, fun d => rfl, ?_⟩
  · rw [Subgroup.range_subtype]
  · intro G _ α φ hφ hαφ Q hQ
    exact hclaims α φ hφ hαφ Q hQ

end Tail

end CFSG.RankThree.PartOne.TCX.Ree
