module

public import CFSG.Quasithin.EmptyFaithful.SzN6Borel
public import CFSG.Quasithin.EmptyFaithful.SzN5Label

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

section Generic

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem szN6_RL_sylow_of_quotient (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (ctx : Ctx15316 T Mc M V₁ V₂ Yp I L t) {Q : Type} [Group Q] (ρ : ↥L →* Q)
    (hρ : Function.Surjective ρ) (hk : IsPGroup 2 ρ.ker)
    (hQ : ∀ Ū Y : Subgroup Q, IsSylowTwoOf Ū ⊤ → Ū ≤ Y → Y ≠ ⊤ →
      Y ≤ Subgroup.normalizer (Ū : Set Q)) :
    IsSylowTwoOf (R153 T V₁ Yp ⊓ L) L := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := ctx.ctx.hyp
  have hI : IsHPlus Yp (Sgp153 T V₁) M I := ctx.ctx.inH
  have hF : Facts15311 T M V₁ Yp I := ctx.facts
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ ctx.conc.1
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hS₀ : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    S153D.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hLI) hF.sylow
  have hYN : Yp ≤ Subgroup.normalizer (L : Set G) := S153D.Yp_le_normalizer h37 h38 hh hI hLI
  have hYI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hYM : Yp ≤ M := by
    intro y hy
    have h1 : y ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := ⟨hYI hy, Subgroup.le_normalizer hy⟩
    rw [hF.norm_eq] at h1
    exact h1.1
  have hSM : Sgp153 T V₁ ≤ M := fun x hx => hh.hyp.T_le hx.1
  have hSYp : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := S153D.Sgp153_le_normalizer_Yp hh
  have hX₀ne : M ⊓ L ≠ L := fun h => ctx.conc.2.1 (le_inf (inf_eq_right.mp h) hLle)
  have hS₀X : Sgp153 T V₁ ⊓ L ≤ M ⊓ L := inf_le_inf_right L hSM
  have hX₀N : M ⊓ L ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) :=
    SzN6.L_normalizes_of_proper_overgroup ρ hρ hk hQ hS₀ hS₀X inf_le_right hX₀ne
  have hS₀X₀ : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) (M ⊓ L) := A4.isSylowTwoOf_mono hS₀ hS₀X inf_le_right
  have hconj : ∀ y ∈ Yp, ∀ x ∈ Sgp153 T V₁ ⊓ L, y * x * y⁻¹ ∈ Sgp153 T V₁ ⊓ L := by
    intro y hy x hx
    have hDle : B6.conjSub y (Sgp153 T V₁ ⊓ L) ≤ Sgp153 T V₁ ⊓ L := by
      refine S153D.le_of_normal_sylow hS₀X₀ hX₀N (S153F.isPGroup_conjSub hS₀.2.1 y) ?_
      intro z hz
      have hz' : y⁻¹ * z * y ∈ Sgp153 T V₁ ⊓ L := B6.mem_conjSub.mp hz
      have hzX := hS₀X hz'
      have hzy : z = y * (y⁻¹ * z * y) * y⁻¹ := by group
      refine ⟨?_, ?_⟩
      · rw [hzy]
        exact M.mul_mem (M.mul_mem (hYM hy) hzX.1) (M.inv_mem (hYM hy))
      · rw [hzy]
        exact (Subgroup.mem_normalizer_iff.mp (hYN hy) _).mp hzX.2
    have hxy : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    have hmem : y * x * y⁻¹ ∈ B6.conjSub y (Sgp153 T V₁ ⊓ L) := by
      rw [B6.mem_conjSub, hxy]
      exact hx
    exact hDle hmem
  let H : Subgroup G := Yp ⊔ Sgp153 T V₁
  let K : Subgroup ↥H := Subgroup.normalCore ((Sgp153 T V₁).subgroupOf H)
  let A : Subgroup G := K.map H.subtype
  have hSH : Sgp153 T V₁ ≤ H := le_sup_right
  have hAH : A ≤ H := Subgroup.map_subtype_le K
  have hAS : A ≤ Sgp153 T V₁ := by
    rintro _ ⟨k, hk', rfl⟩
    exact Subgroup.mem_subgroupOf.mp (Subgroup.normalCore_le _ hk')
  have hAp : IsPGroup 2 A := hF.sylow.2.1.to_le hAS
  have hAK : A.subgroupOf H = K := Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
  have hAn : (A.subgroupOf H).Normal := by
    rw [hAK]
    exact Subgroup.normalCore_normal _
  have hAR : A ≤ pCoreOf 2 H := le_pCoreOf 2 hAH hAn hAp
  have hS₀A : Sgp153 T V₁ ⊓ L ≤ A := by
    intro x hx
    have hxH : x ∈ H := hSH hx.1
    refine ⟨⟨x, hxH⟩, fun b => ?_, rfl⟩
    obtain ⟨g, hgH⟩ := b
    have hg' : g ∈ Sgp153 T V₁ ⊔ Yp := by
      have hgH' : g ∈ Yp ⊔ Sgp153 T V₁ := hgH
      rwa [sup_comm] at hgH'
    have hg'' : g ∈ ((Sgp153 T V₁ : Subgroup G) : Set G) * (Yp : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hSYp]
      exact hg'
    obtain ⟨s, hs, y, hy, rfl⟩ := hg''
    rw [Subgroup.mem_subgroupOf]
    have hyx := (hconj y hy x hx).1
    have hcalc : s * y * x * (s * y)⁻¹ = s * (y * x * y⁻¹) * s⁻¹ := by group
    show s * y * x * (s * y)⁻¹ ∈ Sgp153 T V₁
    rw [hcalc]
    exact (Sgp153 T V₁).mul_mem ((Sgp153 T V₁).mul_mem hs hyx) ((Sgp153 T V₁).inv_mem hs)
  have hS₀R : Sgp153 T V₁ ⊓ L ≤ R153 T V₁ Yp := hS₀A.trans hAR
  refine ⟨inf_le_right, (pCoreOf_isPGroup 2 _).to_le inf_le_left, fun hdvd =>
    hS₀.2.2 (hdvd.trans (Subgroup.index_dvd_of_le ?_))⟩
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact ⟨hS₀R hx, x.2⟩

end Generic

section Lin2

theorem lin2RLSylow_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) : Lin2RLSylow := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t ctx hn
  obtain ⟨n, hn1, F, hF, hFin, hcard, α, hαs, hαk, -⟩ := hn
  have hnat : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hnat
  have hk : IsPGroup 2 α.ker := hαk ▸ CFSG.pCore_isPGroup
  exact szN6_RL_sylow_of_quotient h37 h38 ctx α hαs hk SzN6.sl2_proper_overgroup_le_normalizer

end Lin2

end CFSG.Quasithin
