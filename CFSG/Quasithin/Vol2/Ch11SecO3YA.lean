module

public import CFSG.Quasithin.Vol2.KGNatComm
public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.Vol2.Ch11SecANat

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF.O3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_mem_of_commutator {V₃ V₁ W A O : Subgroup G} {y : G}
    (hV : V₃ ≤ ⁅V₃, A⁆ ⊔ V₁) (hV₁₃ : V₁ ≤ V₃) (hV₃W : V₃ ≤ W) (hWA : ⁅W, A⁆ ≤ V₃)
    (hVO : ⁅V₃, O⁆ ≤ V₁) (hON : O ≤ Subgroup.normalizer (V₃ : Set G))
    (hyW : y ∈ Subgroup.normalizer (W : Set G)) (hyO : y ∈ Subgroup.normalizer (O : Set G))
    (hyV₁ : ∀ z ∈ V₁, y * z * y⁻¹ ∈ V₁) (hyA : ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ O) :
    ∀ v ∈ V₃, y * v * y⁻¹ ∈ V₃ := by
  suffices hle : V₃ ≤ conjSubgroup V₃ y from fun v hv => mem_conjSubgroup_iff.mp (hle hv)
  refine hV.trans (sup_le ?_ fun z hz => mem_conjSubgroup_iff.mpr (hV₁₃ (hyV₁ z hz)))
  rw [Subgroup.commutator_le]
  intro v hv a ha
  rw [mem_conjSubgroup_iff]
  set o := y * a * y⁻¹ * a⁻¹ with ho
  have hoO : o ∈ O := hyA a ha
  have ho' : y⁻¹ * o * y ∈ O := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyO) o).mp hoO
    simpa using this
  have hv' : y * v * y⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hyW v).mp (hV₃W hv)
  have h1 : y * ⁅v, y⁻¹ * o * y⁆ * y⁻¹ ∈ V₁ :=
    hyV₁ _ (hVO (Subgroup.commutator_mem_commutator hv ho'))
  have h2 : o * ⁅y * v * y⁻¹, a⁆ * o⁻¹ ∈ V₃ :=
    (Subgroup.mem_normalizer_iff.mp (hON hoO) _).mp
      (hWA (Subgroup.commutator_mem_commutator hv' ha))
  have heq : y * ⁅v, a⁆ * y⁻¹ =
      (y * ⁅v, y⁻¹ * o * y⁆ * y⁻¹) * (o * ⁅y * v * y⁻¹, a⁆ * o⁻¹) := by
    simp only [ho, commutatorElement_def]
    group
  rw [heq]
  exact V₃.mul_mem (hV₁₃ h1) h2

variable [Finite G]

theorem conj_comm_mem_of_isNaturalSection {A V Z : Subgroup G} {N : Subgroup ↥A} {F : Type}
    [Field F] [Fintype F] (h : IsNaturalSection A V Z N (Assembly.LowTwoRank.StatedSL 2 F))
    {y : G}
    (hyN : y ∈ Subgroup.normalizer (V : Set G)) (hyZ : ∀ z ∈ Z, y * z * y⁻¹ ∈ Z)
    (hcomm : ∀ a ∈ A, ∀ v ∈ V, y * (a * v * a⁻¹) * y⁻¹ * (a * (y * v * y⁻¹) * a⁻¹)⁻¹ ∈ Z)
    (hcop : Nat.Coprime (orderOf y) (Fintype.card F - 1)) :
    ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ Z := by
  obtain ⟨hAV, α, hα, -, β, hβ, hβker, hequiv⟩ := h
  let B : ↥V → (Fin 2 → F) := fun v => Multiplicative.toAdd (β v)
  have hBmul : ∀ u v : ↥V, B (u * v) = B u + B v := fun u v => by
    simp only [B, map_mul, toAdd_mul]
  have hBinv : ∀ u : ↥V, B u⁻¹ = - B u := fun u => by
    simp only [B, map_inv, toAdd_inv]
  have hBker : ∀ u : ↥V, B u = 0 ↔ (u : G) ∈ Z := fun u => by
    rw [← Subgroup.mem_subgroupOf, ← hβker, MonoidHom.mem_ker]
    exact toAdd_eq_zero
  have hBsurj : Function.Surjective B := fun w => by
    obtain ⟨v, hv⟩ := hβ (Multiplicative.ofAdd w)
    exact ⟨v, by simp only [B, hv, toAdd_ofAdd]⟩
  have hBeq : ∀ u v : ↥V, B u = B v ↔ ((u * v⁻¹ : ↥V) : G) ∈ Z := fun u v => by
    rw [← hBker, hBmul, hBinv, ← sub_eq_add_neg, sub_eq_zero]
  let σ := SecA.conjV V y hyN
  have hσv : ∀ v : ↥V, ((σ v : ↥V) : G) = y * v * y⁻¹ := SecA.conjV_apply_coe V hyN
  have hfac : ∀ u v : ↥V, B u = B v → B (σ u) = B (σ v) := by
    intro u v huv
    rw [hBeq] at huv ⊢
    rw [← map_inv, ← map_mul, hσv]
    exact hyZ _ huv
  let s := Function.surjInv hBsurj
  have hs : ∀ w, B (s w) = w := Function.surjInv_eq hBsurj
  let φ : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun w => B (σ (s w))
      map_zero' := by
        have h0 : B (s 0) = B 1 := by rw [hs]; exact ((hBker 1).mpr Z.one_mem).symm
        change B (σ (s 0)) = 0
        rw [hfac _ _ h0, map_one, hBker]
        exact Z.one_mem
      map_add' := fun w₁ w₂ => by
        have h0 : B (s (w₁ + w₂)) = B (s w₁ * s w₂) := by rw [hs, hBmul, hs, hs]
        change B (σ (s (w₁ + w₂))) = B (σ (s w₁)) + B (σ (s w₂))
        rw [hfac _ _ h0, map_mul, hBmul] }
  have hφ : ∀ v : ↥V, φ (B v) = B (σ v) := fun v => hfac _ _ (hs (B v))
  have hT : ∀ (γ : ↥(Assembly.LowTwoRank.StatedSL 2 F)) (x : Fin 2 → F),
      φ ((KGNat.linModelNat (Assembly.LowTwoRank.StatedSL 2 F)).lin γ x) =
        (KGNat.linModelNat (Assembly.LowTwoRank.StatedSL 2 F)).lin γ (φ x) := by
    intro γ x
    obtain ⟨a, rfl⟩ := hα γ
    obtain ⟨v, rfl⟩ := hBsurj x
    rw [KGNat.linModelNat_lin, KGNat.linModelNat_lin]
    have hav : (a : G) * v * (a : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hAV a.2) v).mp v.2
    have hav' : (a : G) * (σ v : G) * (a : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hAV a.2) _).mp (σ v).2
    have h1 : B ⟨_, hav⟩ = ((α a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec (B v) :=
      hequiv a v ⟨_, hav⟩ rfl
    have h2 : B ⟨_, hav'⟩ =
        ((α a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec (B (σ v)) :=
      hequiv a (σ v) ⟨_, hav'⟩ rfl
    calc φ (((α a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec (B v))
        = φ (B ⟨_, hav⟩) := by rw [h1]
      _ = B (σ ⟨_, hav⟩) := hφ _
      _ = B ⟨_, hav'⟩ := by
          rw [hBeq]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσv]
          exact hcomm a a.2 v v.2
      _ = ((α a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec (φ (B v)) := by rw [h2, hφ]
  obtain ⟨c, hc⟩ := KGNat.commutant_statedSL (le_refl 2) φ hT
  have hcv : ∀ v : ↥V, B (σ v) = c • B v := fun v => by rw [← hφ, hc]
  have hpowc : ∀ j : ℕ, ∀ v : ↥V, (((σ ^ j) v : ↥V) : G) = y ^ j * v * (y ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro v; simp
    | succ j ih => intro v; rw [pow_succ', MulAut.mul_apply, hσv, ih, pow_succ']; group
  have hpow : ∀ j : ℕ, ∀ v : ↥V, B ((σ ^ j) v) = c ^ j • B v := by
    intro j
    induction j with
    | zero => intro v; rw [pow_zero, pow_zero, one_smul, MulAut.one_apply]
    | succ j ih => intro v; rw [pow_succ', MulAut.mul_apply, hcv, ih, smul_smul, pow_succ']
  obtain ⟨v₀, hv₀⟩ := hBsurj (Pi.single 0 1)
  have hσk : (σ ^ orderOf y) v₀ = v₀ :=
    Subtype.ext (by rw [hpowc, pow_orderOf_eq_one, one_mul, inv_one, mul_one])
  have hck : c ^ orderOf y = 1 := by
    have h1 := hpow (orderOf y) v₀
    rw [hσk, hv₀] at h1
    have h2 := congrFun h1 0
    simpa using h2.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (orderOf_pos y).ne'] at hck
    exact zero_ne_one hck
  have hc1 : c = 1 := by
    have h1 : c ^ Nat.gcd (orderOf y) (Fintype.card F - 1) = 1 :=
      pow_gcd_eq_one.mpr ⟨hck, FiniteField.pow_card_sub_one_eq_one c hc0⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
  intro v hv
  have h1 := hcv ⟨v, hv⟩
  rw [hc1, one_smul, hBeq] at h1
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hσv] using h1

end CFSG.Quasithin.Vol2.Ch11.SecF.O3
