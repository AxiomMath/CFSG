module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Five

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Model

variable {K : Type} [Field K] {γ : G → K}

theorem card_Wt_mul_card_eq_of_gammaReg [Finite K] (M₀ : Tim79.QuadModel Q Z K γ)
    (R : Tim79.GammaReg Q Z γ) {X : Subgroup G} (hXQ : X ≤ Q) (hZX : Z ≤ X)
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img X → c • e ∈ M₀.img X) :
    Nat.card ↥(Wt Q X) * Nat.card X = Nat.card Q * Nat.card Z := by
  set S : Submodule K M₀.E := imgSub M₀ X hS with hSdef
  have himgS : ∀ e : M₀.E, e ∈ S ↔ e ∈ M₀.img X := fun e => by
    rw [hSdef]
    exact mem_imgSub
  have himg : ∀ e : M₀.E, e ∈ M₀.img (Wt Q X) ↔ e ∈ M₀.B.orthogonal S := by
    intro e
    rw [mem_img_Wt_iff M₀ R hXQ, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h v hv
      have h0 := h v ((himgS v).mp hv)
      rwa [Tim79.QuadModel.B_comm, neg_eq_zero] at h0
    · intro h v hv
      have h0 := h v ((himgS v).mpr hv)
      rwa [Tim79.QuadModel.B_comm, neg_eq_zero] at h0
  have hZW : Z ≤ Wt Q X := fun z hz => Subgroup.mem_inf.mpr ⟨R.V_le hz,
    Subgroup.mem_centralizer_iff.mpr fun x hx => (Tim79.QuadModel.comm_iff_B M₀ R
      (hXQ hx) (R.V_le hz)).mpr (by rw [(M₀.π_ker z (R.V_le hz)).mpr hz]; simp)⟩
  have hWtcard := Tim79.QuadModel.card_eq M₀ (S := Wt Q X) inf_le_left hZW
  have hXcard := Tim79.QuadModel.card_eq M₀ (S := X) hXQ hZX
  have himgWt : Nat.card (M₀.img (Wt Q X)) = Nat.card ↥(M₀.B.orthogonal S) :=
    Nat.card_congr (Equiv.subtypeEquivRight himg)
  have himgX : Nat.card (M₀.img X) = Nat.card ↥S :=
    Nat.card_congr (Equiv.subtypeEquivRight fun e => (himgS e).symm)
  have horth := QuadModel.card_orthogonal_mul_card M₀ S
  have himgQ : M₀.img Q = ⊤ := by
    refine le_antisymm le_top ?_
    intro e _
    obtain ⟨y, hyQ, hπ⟩ := M₀.π_surj e
    exact ⟨y, hyQ, hyQ, hπ⟩
  have hQcard : Nat.card Q = Nat.card Z * Nat.card M₀.E := by
    have h := Tim79.QuadModel.card_eq M₀ (S := Q) le_rfl R.V_le
    rwa [himgQ, AddSubgroup.card_top] at h
  calc Nat.card ↥(Wt Q X) * Nat.card X
      = Nat.card Z * Nat.card Z *
          (Nat.card (M₀.img (Wt Q X)) * Nat.card (M₀.img X)) := by
        rw [hWtcard, hXcard]; ring
    _ = Nat.card Z * Nat.card Z * Nat.card M₀.E := by
        rw [himgWt, himgX, horth]
    _ = Nat.card Q * Nat.card Z := by rw [hQcard]; ring

end Model

theorem Ctx.card_Wt_mul_card_Vt (hc : Ctx M Q Z B) (t : G) :
    Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card ↥(Vt M (LB M Q B) B Z t) =
      Nat.card Q * Nat.card Z := by
  obtain ⟨K, hK, hfin, hch, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  haveI : Finite K := hfin
  exact card_Wt_mul_card_eq_of_gammaReg M₀ hD.reg (hc.Vt_le_Q t) le_sup_left
    fun c e he => hc.smul_mem_img_Vt hD t c he

theorem Good103.card_Ut_eq (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {m : ℕ} (hm : SLMNat hc t m) :
    Nat.card ↥(Ut Q Z t) = Nat.card Z ^ (2 * m + 1) := by
  let V : Subgroup G := Vt M (LB M Q B) B Z t
  let W : Subgroup G := Wt Q V
  let U : Subgroup G := Ut Q Z t
  let T : Subgroup G := Tt Q Z V t
  have hVT : V = T := (stroth_10_5 h34 h311a hspread) G M Q Z B hc n t H ht
  have hUQ : U ≤ Q := hc.Ut_le_Q ht.1.2.1
  have hTQ : T ≤ Q :=
    Tt_le_Q hc.Z_le_Q (hc.hyp.Q_normal.2 (hc.LB_le_M ht.1.mem_LB))
  have hUN : U ≤ Subgroup.normalizer (T : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun u hu x hx => ?_
    have hcomm : ⁅u, x⁆ ∈ Z := comm_mem_Z hc.hyp (hUQ hu) (hTQ hx)
    have hconj : u * x * u⁻¹ = ⁅u, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [hconj]
    exact T.mul_mem (show ⁅u, x⁆ ∈ T from Subgroup.mem_sup_right hcomm) hx
  haveI : ((Tt Q Z V t).subgroupOf (Ut Q Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hUN
  have hchi : IsChiIso Q (Rt M (LB M Q B) t) W U T t :=
    hc.isChiIso_Wt_Ut_Tt ht.1.mem_LB hVT.le
  have hcard := card_mul_card_of_isChiIso hchi inf_le_left
    (sup_le_sup_right (Subgroup.commutator_mono inf_le_left le_rfl) Z)
  have hcardQ : Nat.card Q * Nat.card V = Nat.card W * Nat.card U := by
    rw [← hVT] at hcard
    exact hcard
  have hWV : Nat.card W * Nat.card V = Nat.card Q * Nat.card Z :=
    Ctx.card_Wt_mul_card_Vt hc t
  have hVcard : Nat.card V = Nat.card Z ^ (m + 1) := SLMNat.card_Vt hm
  have hZU : Nat.card Z * Nat.card U = Nat.card V * Nat.card V := by
    have e : Nat.card Q * (Nat.card V * Nat.card V) =
        Nat.card Q * (Nat.card Z * Nat.card U) := by
      calc Nat.card Q * (Nat.card V * Nat.card V)
          = (Nat.card Q * Nat.card V) * Nat.card V := by ring
        _ = (Nat.card W * Nat.card U) * Nat.card V := by rw [hcardQ]
        _ = (Nat.card W * Nat.card V) * Nat.card U := by ring
        _ = (Nat.card Q * Nat.card Z) * Nat.card U := by rw [hWV]
        _ = Nat.card Q * (Nat.card Z * Nat.card U) := by ring
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos e).symm
  have hZU' : Nat.card Z * Nat.card U = Nat.card Z * Nat.card Z ^ (2 * m + 1) := by
    rw [hZU, hVcard, ← pow_add, ← pow_succ']
    congr 1
    omega
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hZU'

end CFSG.RankThree.GF2n.Stroth80
