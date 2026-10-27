module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Stroth80.Sec12Decomp
public import CFSG.RankThree.GF2n.Stroth80.Sec311SLTorus
public import CFSG.RankThree.GF2n.Stroth80.Sec12Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Model

variable {K : Type} [Field K] {γ : G → K}

theorem QuadModel.card_orthogonal_mul_card [Finite K] (M₀ : Tim79.QuadModel Q Z K γ)
    (W : Submodule K M₀.E) :
    Nat.card ↥(M₀.B.orthogonal W) * Nat.card ↥W = Nat.card M₀.E := by
  haveI : Module.Finite K M₀.E := M₀.fin
  have h1 : Nat.card ↥(M₀.B.orthogonal W) =
      Nat.card K ^ Module.finrank K ↥(M₀.B.orthogonal W) := Module.natCard_eq_pow_finrank
  have h2 : Nat.card ↥W = Nat.card K ^ Module.finrank K ↥W := Module.natCard_eq_pow_finrank
  have h3 : Nat.card M₀.E = Nat.card K ^ Module.finrank K M₀.E := Module.natCard_eq_pow_finrank
  have h4 := LinearMap.BilinForm.finrank_orthogonal (modelB_nondegenerate M₀) W
  have h5 : Module.finrank K ↥(M₀.B.orthogonal W) + Module.finrank K ↥W =
      Module.finrank K M₀.E := by
    have := Submodule.finrank_le W
    omega
  rw [h1, h2, h3, ← pow_add, h5]

private theorem img_Wt_eq_orthogonal_span (M₀ : Tim79.QuadModel Q Z K γ)
    (R : Tim79.GammaReg Q Z γ) {X : Subgroup G} (hXQ : X ≤ Q) {e : M₀.E} :
    e ∈ M₀.img (Wt Q X) ↔
      e ∈ M₀.B.orthogonal (Submodule.span K (M₀.img X : Set M₀.E)) := by
  rw [mem_img_Wt_iff M₀ R hXQ, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    have hle : Submodule.span K (M₀.img X : Set M₀.E) ≤ LinearMap.ker (M₀.B.flip e) :=
      Submodule.span_le.mpr fun v hv => by
        show M₀.B v e = 0
        rw [Tim79.QuadModel.B_comm, h v hv, neg_zero]
    intro w hw
    simpa [LinearMap.BilinForm.flip_apply] using hle hw
  · intro h v hv
    have h1 := h v (Submodule.subset_span hv)
    rwa [Tim79.QuadModel.B_comm, neg_eq_zero] at h1

private theorem Z_le_Wt (M₀ : Tim79.QuadModel Q Z K γ) (R : Tim79.GammaReg Q Z γ)
    {X : Subgroup G} (hXQ : X ≤ Q) : Z ≤ Wt Q X := by
  intro z hz
  refine Subgroup.mem_inf.mpr ⟨R.V_le hz, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  refine (Tim79.QuadModel.comm_iff_B M₀ R (hXQ hx) (R.V_le hz)).mpr ?_
  rw [(M₀.π_ker z (R.V_le hz)).mpr hz]
  simp

private theorem card_Q_eq_card_Z_mul (M₀ : Tim79.QuadModel Q Z K γ)
    (R : Tim79.GammaReg Q Z γ) : Nat.card Q = Nat.card Z * Nat.card M₀.E := by
  have himgQ : M₀.img Q = ⊤ := by
    refine le_antisymm le_top ?_
    intro e _
    obtain ⟨y, hyQ, hπ⟩ := M₀.π_surj e
    exact ⟨y, hyQ, hyQ, hπ⟩
  have h := Tim79.QuadModel.card_eq M₀ (S := Q) le_rfl R.V_le
  rwa [himgQ, AddSubgroup.card_top] at h

private theorem card_img_Wt_mul_card_img_le [Finite K] (M₀ : Tim79.QuadModel Q Z K γ)
    (R : Tim79.GammaReg Q Z γ) {X : Subgroup G} (hXQ : X ≤ Q) :
    Nat.card (M₀.img (Wt Q X)) * Nat.card (M₀.img X) ≤ Nat.card M₀.E := by
  haveI : Module.Finite K M₀.E := M₀.fin
  haveI : Finite M₀.E := Module.finite_of_finite K
  set Sp := Submodule.span K (M₀.img X : Set M₀.E) with hSp
  have himgXle : Nat.card (M₀.img X) ≤ Nat.card ↥Sp :=
    Nat.card_le_card_of_injective
      (fun z : M₀.img X => (⟨z.1, Submodule.subset_span z.2⟩ : Sp))
      (fun a b h => Subtype.ext (congrArg (fun z : Sp => (z : M₀.E)) h))
  have h1 : Nat.card (M₀.img (Wt Q X)) ≤ Nat.card ↥(M₀.B.orthogonal Sp) :=
    Nat.card_le_card_of_injective
      (fun z : M₀.img (Wt Q X) => (⟨z.1, (img_Wt_eq_orthogonal_span M₀ R hXQ).mp z.2⟩ :
        M₀.B.orthogonal Sp))
      (fun a b h => Subtype.ext (congrArg (fun z : M₀.B.orthogonal Sp => (z : M₀.E)) h))
  calc Nat.card (M₀.img (Wt Q X)) * Nat.card (M₀.img X)
      ≤ Nat.card ↥(M₀.B.orthogonal Sp) * Nat.card ↥Sp := Nat.mul_le_mul h1 himgXle
    _ = Nat.card M₀.E := QuadModel.card_orthogonal_mul_card M₀ Sp

theorem card_Wt_mul_card_le_of_gammaReg [Finite K] (M₀ : Tim79.QuadModel Q Z K γ)
    (R : Tim79.GammaReg Q Z γ) {X : Subgroup G} (hXQ : X ≤ Q) (hZX : Z ≤ X) :
    Nat.card ↥(Wt Q X) * Nat.card X ≤ Nat.card Q * Nat.card Z := by
  have hWtcard : Nat.card ↥(Wt Q X) = Nat.card Z * Nat.card (M₀.img (Wt Q X)) :=
    Tim79.QuadModel.card_eq M₀ inf_le_left (Z_le_Wt M₀ R hXQ)
  have hXcard : Nat.card X = Nat.card Z * Nat.card (M₀.img X) :=
    Tim79.QuadModel.card_eq M₀ hXQ hZX
  have hQcard := card_Q_eq_card_Z_mul M₀ R
  have hstep := card_img_Wt_mul_card_img_le M₀ R hXQ
  calc Nat.card ↥(Wt Q X) * Nat.card X
      = Nat.card Z * Nat.card Z * (Nat.card (M₀.img (Wt Q X)) * Nat.card (M₀.img X)) := by
        rw [hWtcard, hXcard]; ring
    _ ≤ Nat.card Z * Nat.card Z * Nat.card M₀.E := Nat.mul_le_mul_left _ hstep
    _ = Nat.card Q * Nat.card Z := by rw [hQcard]; ring

end Model

theorem StrothHyp.card_Wt_mul_card_le (H : StrothHyp M Q Z) {X : Subgroup G} (hXQ : X ≤ Q)
    (hZX : Z ≤ X) : Nat.card ↥(Wt Q X) * Nat.card X ≤ Nat.card Q * Nat.card Z := by
  obtain ⟨K, hK, hfin, hch, γ, M₀, hD⟩ := stroth_globalModelData H
  exact card_Wt_mul_card_le_of_gammaReg M₀ hD.reg hXQ hZX

private theorem toAdd_psi_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {V Z : Subgroup G} [hN : (Z.subgroupOf V).Normal]
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    (hker : ∀ w : V, ψ (QuotientGroup.mk w) = 1 ↔ (w : G) ∈ Z) {w : V}
    (hwZ : (w : G) ∉ Z) : Multiplicative.toAdd (ψ (QuotientGroup.mk w)) ≠ 0 := by
  intro h0
  exact hwZ ((hker w).mp (by simpa using congrArg Multiplicative.ofAdd h0))

private theorem SLMNat.mem_of_not_mem_Z {hc : Ctx M Q Z B} {t : G} {m : ℕ}
    (h : SLMNat hc t m) (hm : 2 ≤ m) {X : Subgroup G} (hZX : Z ≤ X)
    (hXV : X ≤ Vt M (LB M Q B) B Z t)
    (hX : Rt M (LB M Q B) t ≤ Subgroup.normalizer (X : Set G))
    {x v : G} (hxX : x ∈ X) (hxZ : x ∉ Z) (hvV : v ∈ Vt M (LB M Q B) B Z t) (hvZ : v ∉ Z) :
    v ∈ X := by
  set V := Vt M (LB M Q B) B Z t
  obtain ⟨K, hK, hfin, -, φ, hφrange, -, hSA⟩ := h
  obtain ⟨hRnV, hZn, ψ, hψ⟩ := hSA
  haveI := hZn
  have hker : ∀ w : V, ψ (QuotientGroup.mk w) = 1 ↔ (w : G) ∈ Z := by
    intro w
    rw [← map_one ψ, ψ.injective.eq_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hxV : x ∈ V := hXV hxX
  obtain ⟨g, hgS, hgv⟩ := exists_statedSL_mulVec_eq_of_ne_zero hm
    (toAdd_psi_ne_zero ψ hker (w := ⟨x, hxV⟩) hxZ)
    (toAdd_psi_ne_zero ψ hker (w := ⟨v, hvV⟩) hvZ)
  obtain ⟨r, hrφ⟩ := MonoidHom.mem_range.mp (hφrange ▸ hgS)
  have hrR : (r : G) ∈ Rt M (LB M Q B) t := r.2
  have hrX : (r : G) * x * (r : G)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp (hX hrR) x).mp hxX
  have hrV : (r : G) * x * (r : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hRnV hrR) x).mp hxV
  have hquot : QuotientGroup.mk' (Z.subgroupOf V) ⟨(r : G) * x * (r : G)⁻¹, hrV⟩ =
      QuotientGroup.mk' (Z.subgroupOf V) ⟨v, hvV⟩ := by
    refine ψ.injective (Multiplicative.toAdd.injective ?_)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      hψ r ⟨x, hxV⟩ ⟨(r : G) * x * (r : G)⁻¹, hrV⟩ rfl, hrφ, hgv]
  have h1 : QuotientGroup.mk' (Z.subgroupOf V)
      ((⟨(r : G) * x * (r : G)⁻¹, hrV⟩ : V)⁻¹ * ⟨v, hvV⟩) = 1 := by
    rw [map_mul, map_inv, hquot, inv_mul_cancel]
  have hmemZ : ((⟨(r : G) * x * (r : G)⁻¹, hrV⟩ : V)⁻¹ * ⟨v, hvV⟩ : V) ∈ Z.subgroupOf V :=
    (QuotientGroup.eq_one_iff _).mp h1
  have hzX : ((r : G) * x * (r : G)⁻¹)⁻¹ * v ∈ X := hZX hmemZ
  have hv : v = ((r : G) * x * (r : G)⁻¹) * (((r : G) * x * (r : G)⁻¹)⁻¹ * v) := by group
  rw [hv]
  exact X.mul_mem hrX hzX

theorem SLMNat.eq_or_eq_of_le_normalizer {hc : Ctx M Q Z B} {t : G} {m : ℕ}
    (h : SLMNat hc t m) (hm : 2 ≤ m) {X : Subgroup G} (hZX : Z ≤ X)
    (hXV : X ≤ Vt M (LB M Q B) B Z t)
    (hX : Rt M (LB M Q B) t ≤ Subgroup.normalizer (X : Set G)) :
    X = Z ∨ X = Vt M (LB M Q B) B Z t := by
  by_cases hXZ : X = Z
  · exact Or.inl hXZ
  right
  have hlt : ¬ X ≤ Z := fun hle => hXZ (le_antisymm hle hZX)
  obtain ⟨x, hxX, hxZ⟩ := SetLike.not_le_iff_exists.mp hlt
  refine le_antisymm hXV fun v hvV => ?_
  by_cases hvZ : v ∈ Z
  · exact hZX hvZ
  exact SLMNat.mem_of_not_mem_Z h hm hZX hXV hX hxX hxZ hvV hvZ

end CFSG.RankThree.GF2n.Stroth80
