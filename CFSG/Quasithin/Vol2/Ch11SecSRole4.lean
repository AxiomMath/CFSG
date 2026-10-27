module

public import CFSG.Quasithin.Vol2.Ch11SecSRole3
public import CFSG.Quasithin.Vol2.Ch11SecSCartan

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem lOf_two_eq_J (hPT : FactParabTwo) (hLevi : FactL34Levi) (hT : FactPGL34Torus)
    (hC : CartanFacts) (hN : NatFacts) (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (cL : CartanL L V₁ V₂ X)
    (hP : ParData T K (LOf L V₁) P₁ P₂) {J I' U₁ U₂ : Subgroup G} (hJ : Hyp11 G T J I' 2)
    (hU₁ : IsVi T J I' 2 1 U₁) (hU₂ : IsVi T J I' 2 2 U₂) (hcart : IsCartanX T J X)
    (hR1 : LOf J U₁ = k0Of K P₂) (hK₀J : k0Of K P₂ ≤ J) (hL₂J : LOf L V₂ ≤ J) (hXJ : X ≤ J) :
    LOf J U₂ = LOf L V₂ := by
  have hD := h.inspData_k0Of hLevi hT hN h1102 cL hP hJ.normal hK₀J hL₂J hXJ
  have hS₁ := isL24Sub_lOf hN h1102 hJ (Or.inl rfl) hU₁
  have hS₂ := isL24Sub_lOf hN h1102 hJ (Or.inr rfl) hU₂
  obtain ⟨-, h2⟩ := hPT _ hJ.shape _ hD.syl _ _ _ ⟨hD.ne₂, hD.p₂, hD.n₂, hD.sl₂⟩ hS₁ hS₂
  have hSI : QuasithinUnique.IsSylowTwoOf (T ⊓ J) J :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
      le_sup_left (sup_le Subgroup.le_normalizer hJ.normal)
  have hOT : pCoreOf 2 J ≤ T := (pCoreOf_two_le_of_isSylowTwoOf hSI).trans inf_le_left
  have hL₁J : LOf J U₁ ≤ J := (perfectCore_le _).trans inf_le_left
  have hL₂J' : LOf J U₂ ≤ J := (perfectCore_le _).trans inf_le_left
  obtain ⟨cJ, -, -⟩ := cartan_of hC hN hG2 h1102 hJ hU₁ hU₂ hcart
  have hX9 : Nat.card ↥X = 9 := card_cartan cL
    (fun _ hx => cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan hx)
    (cartan_inf_lOf_inf_sectionCentralizer hN h1102 h.hyp h.v₁ h.cartan)
  rcases h2 with h2 | h2 | h2
  · exfalso
    apply hD.ne
    rw [h2, hR1]
  · exact (eq_of_modO2Image_eq_of_perfect hL₂J hL₂J' (perfectCore_perfect _)
      (perfectCore_perfect _) (hOT.trans h.T_le_normalizer_L₂)
      (hOT.trans (T_le_normalizer_lOf hJ.normal hU₂.2)) h2).symm
  · exact (lOf_ne_of_cartanL cJ hX9 (eq_of_modO2Image_eq_of_perfect hL₁J hL₂J'
      (perfectCore_perfect _) (perfectCore_perfect _)
      (hOT.trans (T_le_normalizer_lOf hJ.normal hU₁.2))
      (hOT.trans (T_le_normalizer_lOf hJ.normal hU₂.2)) h2)).elim

theorem le_centralizer_U₁ (hNP : NatPointFacts) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) {J I' U₁ : Subgroup G} (hJ : Hyp11 G T J I' 2)
    (hU₁ : IsVi T J I' 2 1 U₁) (hcart : IsCartanX T J X)
    (hCV : fsuV T I' ⊓ Subgroup.centralizer (J : Set G) = ⊥)
    (hZK : ⁅quasithinOmegaOneCenter T, K⁆ = ⊥) : K ≤ Subgroup.centralizer (U₁ : Set G) := by
  obtain ⟨ha, d, hdD, hd⟩ := natPoint_J hNP h1102 hJ hU₁ hcart hCV
  obtain ⟨z, hz, hz1⟩ := exists_omegaOneCenter_fsuV hJ
  have hz1' : (⟨z, hz.1⟩ : ↥(fsuV T I')) ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  obtain ⟨hzU, -⟩ := ha _ hz1' (fixed_of_omegaOneCenter hz.1 hz.2)
  obtain ⟨⟨x, hxN⟩, hxX, rfl⟩ := hdD
  have hne := hd _ hzU hz1'
  have hZC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZK
  have hzK : z ∈ Subgroup.centralizer (K : Set G) := hZC hz.2
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := h.cartan_le_normalizer_K hN h1102 hxX
  have hXU : X ≤ Subgroup.normalizer (U₁ : Set G) :=
    cartan_le_normalizer_Vi hN h1102 hJ (Or.inl rfl) hU₁ hcart
  have hzU' : z ∈ U₁ := hzU
  have hyU : x * z * x⁻¹ ∈ U₁ := (Subgroup.mem_normalizer_iff.mp (hXU hxX) z).mp hzU'
  have hyz : x * z * x⁻¹ ≠ z := by
    intro heq
    apply hne
    apply Subtype.ext
    change ((conjV (fsuV T I') x hxN ⟨z, hz.1⟩ : ↥(fsuV T I')) : G) = z
    rw [conjV_apply_coe]
    exact heq
  have hy1 : x * z * x⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [this, h1]
    group
  have hyK : x * z * x⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : x⁻¹ * k * x ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxK) k).mp hk
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hzK _ hk'
    calc k * (x * z * x⁻¹) = x * ((x⁻¹ * k * x) * z) * x⁻¹ := by group
      _ = x * (z * (x⁻¹ * k * x)) * x⁻¹ := by rw [hc]
      _ = x * z * x⁻¹ * k := by group
  have hUC := le_of_card_four (card_vi_one hU₁ hCV) hzU' hyU hz1 hy1 hyz.symm hzK hyK
  exact Subgroup.le_centralizer_iff.mp hUC

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
