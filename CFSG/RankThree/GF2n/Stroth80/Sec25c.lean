module

public import CFSG.RankThree.GF2n.Stroth80.DictB
public import CFSG.RankThree.GF2n.Stroth80.QuadIso

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem GlobalModelData.finrank_E (h : GlobalModelData M Q Z γ M₀) {w : ℕ} (hw : Width Q Z w)
    (hK : 1 < Nat.card K) : Module.finrank K M₀.E = 2 * w := by
  have h1 : Nat.card Q = Nat.card Z * Nat.card (M₀.img Q) := M₀.card_eq le_rfl h.reg.V_le
  have himg : Nat.card (M₀.img Q) = Nat.card M₀.E := by
    refine Nat.card_congr (Equiv.subtypeUnivEquiv fun v => ?_)
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj v
    exact M₀.pi_mem_img hx hx
  have h2 : Nat.card M₀.E = Nat.card K ^ Module.finrank K M₀.E := Module.natCard_eq_pow_finrank
  unfold Width at hw
  rw [h1, himg, h2, ← h.card] at hw
  have h3 : Nat.card K ^ (Module.finrank K M₀.E + 1) = Nat.card K ^ (2 * w + 1) := by
    rw [pow_succ, mul_comm]
    exact hw
  have := Nat.pow_right_injective hK h3
  omega

theorem Ctx.mem_center_iff_centralizer_B (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {y : G} (hy : y ∈ Q ⊓ Subgroup.centralizer (B : Set G)) :
    (∀ x ∈ Q ⊓ Subgroup.centralizer (B : Set G), y * x = x * y) ↔ y ∈ Z ⊔ B := by
  obtain ⟨b, hb0, hbs, hB, hcent, hcard⟩ := hc.dictB h
  constructor
  · intro hyc
    have h1 : ∀ v, M₀.B v b = 0 → M₀.B (M₀.π y) v = 0 := by
      intro v hv
      obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj v
      have hxC : x ∈ Q ⊓ Subgroup.centralizer (B : Set G) := ⟨hxQ, (hcent x hxQ).mpr hv⟩
      exact (M₀.comm_iff_B h.reg hy.1 hxQ).mp (hyc x hxC)
    obtain ⟨c, hc'⟩ := Tim79.QuadModel.exists_smul_of_orthogonal hb0 h1
    have : M₀.π y ∈ M₀.img (Z ⊔ B) := M₀.img_mono le_sup_right ((hB _).mpr ⟨c, hc'⟩)
    exact (M₀.mem_img_iff le_sup_left hy.1).mp this
  · intro hyZB x hx
    have hle : Z ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun z hz => ?_) (fun u hu => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hc.hyp.toHyp79.V_central hz hx.1)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx.2 u hu)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hyZB)

theorem Ctx.commutator_centralizer_B (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {w : ℕ}
    (hw : Width Q Z w) (hw2 : 2 ≤ w) :
    ⁅Q ⊓ Subgroup.centralizer (B : Set G), Q ⊓ Subgroup.centralizer (B : Set G)⁆ = Z := by
  obtain ⟨b, hb0, hbs, hB, hcent, hcard⟩ := hc.dictB h
  have hK : 1 < Nat.card K := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  have hdim := h.finrank_E hw hK
  refine le_antisymm (Subgroup.commutator_le.mpr fun x hx y hy =>
    hc.hyp.toHyp79.comm_mem_V hx.1 hy.1) fun z hz => ?_
  obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v : M₀.E, M₀.B u b = 0 ∧ M₀.B v b = 0 ∧ M₀.B u v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    set f : M₀.E →ₗ[K] K := M₀.B.flip b with hf
    have hker : LinearMap.ker f ≤ Submodule.span K {b} := by
      intro u hu
      obtain ⟨c, hc'⟩ := Tim79.QuadModel.exists_smul_of_orthogonal hb0 (v := u) (fun v hv =>
        by by_contra hne; exact hne (by
          have := hcon u v hu hv
          exact this))
      exact Submodule.mem_span_singleton.mpr ⟨c, hc'.symm⟩
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 : Module.finrank K (LinearMap.range f) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range f)
      simpa using this
    have h3 : Module.finrank K (LinearMap.ker f) ≤ 1 := by
      calc Module.finrank K (LinearMap.ker f) ≤ Module.finrank K (Submodule.span K {b}) :=
            Submodule.finrank_mono hker
        _ = 1 := finrank_span_singleton hb0
        _ ≤ 1 := le_rfl
    omega
  set s := γ z with hs
  set u' := (s / M₀.B u v) • u with hu'
  have hu'b : M₀.B u' b = 0 := by rw [hu', map_smul, LinearMap.smul_apply, hu, smul_zero]
  have hu'v : M₀.B u' v = s := by
    rw [hu', map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ huv]
  obtain ⟨x, hxQ, hx⟩ := M₀.π_surj u'
  obtain ⟨y, hyQ, hy⟩ := M₀.π_surj v
  have hxC : x ∈ Q ⊓ Subgroup.centralizer (B : Set G) := ⟨hxQ, (hcent x hxQ).mpr (hx ▸ hu'b)⟩
  have hyC : y ∈ Q ⊓ Subgroup.centralizer (B : Set G) := ⟨hyQ, (hcent y hyQ).mpr (hy ▸ hv)⟩
  have hcomm : ⁅x, y⁆ = z := by
    refine Tim79.eq_of_map_eq_of_additive h.reg.add h.reg.inj (M₀.comm_mem x hxQ y hyQ) hz ?_
    rw [M₀.comm_eq x hxQ y hyQ, hx, hy, hu'v]
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator hxC hyC

end CFSG.RankThree.GF2n.Stroth80
