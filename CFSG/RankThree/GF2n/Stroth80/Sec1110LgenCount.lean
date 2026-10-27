module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110LgenCoord
import CFSG.ClassicalGroups.SpecialLinear.FixedHyperplanePair

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.SpecialLinear
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] {n : ℕ}

private theorem exists_linear_of_semilinear {K F E : Type} [Field K] [Field F] [AddCommGroup E]
    [Module K E] (θ : K ≃+* F) (ι : (Fin n → F) →+ E)
    (hι : ∀ (c : K) (x : Fin n → F), c • ι x = ι (θ c • x)) (β : E →ₗ[K] K) :
    ∃ μ : (Fin n → F) →ₗ[F] F, ∀ x, μ x = 0 ↔ β (ι x) = 0 := by
  refine ⟨{ toFun := fun x => θ (β (ι x))
            map_add' := fun x x' => by simp only [map_add]
            map_smul' := fun a x => ?_ }, fun x => ?_⟩
  · have h1 : ι (a • x) = θ.symm a • ι x := by rw [hι, RingEquiv.apply_symm_apply]
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [h1, map_smul, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply]
  · show θ (β (ι x)) = 0 ↔ β (ι x) = 0
    exact map_eq_zero_iff θ θ.injective

private theorem act_eq_of_comm_mem {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    {φH0 : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φH0 m (M₀.π x))
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) {V : Subgroup G}
    (hZV : Z ≤ V) {y : H0 M Z}
    (hy : ∀ c ∈ V ⊓ Subgroup.centralizer (B : Set G), ⁅(y : G), c⁆ ∈ Z) {e : M₀.E}
    (heV : e ∈ M₀.img V) (heB : M₀.B e b = 0) : φH0 y e = e := by
  obtain ⟨c, hcC, hcQ, rfl⟩ := (Tim79.QuadModel.img_centralizer hD.reg hc.le hB).mpr heB
  have hcV : c ∈ V := (M₀.mem_img_iff hZV hcQ).mp heV
  have hyM : (y : G) ∈ M := (y.2 : (y : G) ∈ M ⊓ Subgroup.centralizer (Z : Set G)).1
  have hycQ : (y : G) * c * (y : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hyM) c).mp hcQ
  rw [← hφπ y c hcQ]
  exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hcQ hycQ).mp (hy c ⟨hcV, hcC.2⟩)

private theorem XbarCore.exists_functionals (hc : Ctx M Q Z B) (hn : 3 ≤ n)
    (S : XbarCore M Q Z B n) {Y : Subgroup G} (hYX : Y ≤ XbarPre M Q Z B)
    (hY₁ : ∀ y ∈ Y, ∀ c ∈ S.V₁ ⊓ Subgroup.centralizer (B : Set G), ⁅y, c⁆ ∈ Z)
    (hY₂ : ∀ y ∈ Y, ∀ c ∈ S.V₂ ⊓ Subgroup.centralizer (B : Set G), ⁅y, c⁆ ∈ Z) :
    ∃ μ₁ μ₂ : (Fin n → S.F) →ₗ[S.F] S.F, ∀ y (hy : y ∈ Y),
      (∀ v, μ₁ v = 0 →
        ((S.φ ⟨y, hYX hy⟩ : GL (Fin n) S.F) : Matrix (Fin n) (Fin n) S.F) *ᵥ v = v) ∧
      ∀ u, μ₂ u = 0 →
        (((S.φ ⟨y, hYX hy⟩)⁻¹ : GL (Fin n) S.F) : Matrix (Fin n) (Fin n) S.F)ᵀ *ᵥ u = u := by
  obtain ⟨K, _, _, _, γ, M₀, hD, φH0, hφπ, -, -, C, hW₁, hW₂⟩ := S.exists_coord hc hn
  obtain ⟨b, -, -, hB, -, -⟩ := hc.dictB hD
  obtain ⟨μ₁, hμ₁⟩ := exists_linear_of_semilinear C.θ₁ C.inl C.smul_inl (M₀.B.flip b)
  obtain ⟨μ₂, hμ₂⟩ := exists_linear_of_semilinear C.θ₂ C.inr C.smul_inr (M₀.B.flip b)
  refine ⟨μ₁, μ₂, fun y hy => ⟨fun v hv => ?_, fun u hu => ?_⟩⟩
  · have h1 := act_eq_of_comm_mem hc hD hφπ hB S.Z_le₁ (y := ⟨y, XbarPre_le_H0 hc (hYX hy)⟩)
      (hY₁ y hy) ((hW₁ _).mpr (C.inl_mem_W₁ v)) (by simpa using (hμ₁ v).mp hv)
    have h2 : (φH0.comp (Subgroup.inclusion (XbarPre_le_H0 hc))) ⟨y, hYX hy⟩ (C.inl v) =
        C.inl v := h1
    rw [C.ρ_inl] at h2
    exact C.inl_injective h2
  · have h1 := act_eq_of_comm_mem hc hD hφπ hB S.Z_le₂ (y := ⟨y, XbarPre_le_H0 hc (hYX hy)⟩)
      (hY₂ y hy) ((hW₂ _).mpr (C.inr_mem_W₂ u)) (by simpa using (hμ₂ u).mp hu)
    have h2 : (φH0.comp (Subgroup.inclusion (XbarPre_le_H0 hc))) ⟨y, hYX hy⟩ (C.inr u) =
        C.inr u := h1
    rw [C.ρ_inr] at h2
    exact C.inr_injective h2

theorem XbarCore.card_le_of_comm_mem_Z (hc : Ctx M Q Z B) (hn : 3 ≤ n)
    (S : XbarCore M Q Z B n) {Y : Subgroup G} (hYX : Y ≤ XbarPre M Q Z B)
    (hY₁ : ∀ y ∈ Y, ∀ c ∈ S.V₁ ⊓ Subgroup.centralizer (B : Set G), ⁅y, c⁆ ∈ Z)
    (hY₂ : ∀ y ∈ Y, ∀ c ∈ S.V₂ ⊓ Subgroup.centralizer (B : Set G), ⁅y, c⁆ ∈ Z) :
    Nat.card Y ≤ Nat.card Q * Nat.card Z := by
  obtain ⟨μ₁, μ₂, hμ⟩ := S.exists_functionals hc hn hYX hY₁ hY₂
  let ψ : ↥Y →* GL (Fin n) S.F := S.φ.comp (Subgroup.inclusion hYX)
  have hcard : Nat.card ψ.ker * Nat.card ψ.range = Nat.card Y := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker : Nat.card ψ.ker ≤ Nat.card Q := by
    refine Nat.card_le_card_of_injective (fun y => (⟨((y : ↥Y) : G), ?_⟩ : ↥Q)) ?_
    · have h1 : Subgroup.inclusion hYX (y : ↥Y) ∈ S.φ.ker := y.2
      rw [S.ker_eq] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    · intro y₁ y₂ h
      have h' : ((y₁ : ↥Y) : G) = ((y₂ : ↥Y) : G) := congrArg (fun x : ↥Q => (x : G)) h
      exact Subtype.ext (Subtype.ext h')
  have hrange : Nat.card ψ.range ≤ Nat.card Z := by
    refine (Nat.card_le_card_of_injective (fun g : ↥ψ.range => (⟨(g : GL (Fin n) S.F), ?_⟩ :
      {g : GL (Fin n) S.F // (∀ v, μ₁ v = 0 → (g : Matrix (Fin n) (Fin n) S.F) *ᵥ v = v) ∧
        ∀ u, μ₂ u = 0 → ((g⁻¹ : GL (Fin n) S.F) : Matrix (Fin n) (Fin n) S.F)ᵀ *ᵥ u = u}))
      ?_).trans ((card_fix_ker_natDual_le μ₁ μ₂).trans S.card.le)
    · obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp g.2
      rw [← hy]
      exact hμ (y : G) y.2
    · intro g₁ g₂ h
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
  rw [← hcard]
  exact Nat.mul_le_mul hker hrange

end CFSG.RankThree.GF2n.Stroth80
