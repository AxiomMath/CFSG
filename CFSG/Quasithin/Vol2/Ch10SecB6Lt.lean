module

public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch10SecABasicL0
public import CFSG.Quasithin.Vol2.Ch10SecBSetup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem lt_or_lt (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {H K₁ K₂ : Subgroup G}
    (hH : InM (fsuL0 T L ⊔ T1 T L) H) (hHM : H ≠ fsuM T L) (hLK₁ : L ≤ K₁)
    (hLK₂ : CFSG.conjugate L t ≤ K₂) (hK₁H : K₁ ≤ H) (hK₂H : K₂ ≤ H)
    (hn₁ : (K₁.subgroupOf H).Normal) (hn₂ : (K₂.subgroupOf H).Normal) :
    L < K₁ ∨ CFSG.conjugate L t < K₂ := by
  by_contra hcon
  rw [not_or] at hcon
  have h1 : L = K₁ := eq_of_le_of_not_lt hLK₁ hcon.1
  have h2 : CFSG.conjugate L t = K₂ := eq_of_le_of_not_lt hLK₂ hcon.2
  have hN₁ := (Subgroup.normal_subgroupOf_iff_le_normalizer hK₁H).mp hn₁
  have hN₂ := (Subgroup.normal_subgroupOf_iff_le_normalizer hK₂H).mp hn₂
  have hHM' : H ≤ fsuM T L := by
    intro h hh
    show h ∈ Subgroup.normalizer (fsuL0 T L : Set G)
    have e1 := hN₁ hh
    have e2 := hN₂ hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at e1 e2 ⊢
    rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn, h2, h1, Subgroup.map_sup, e1, e2]
  exact hHM ((hH.1.2 _ (fsuM_isMaxTwoLocal h331 hyp).1 hHM').symm)

theorem modO2Image_ne {H S X K : Subgroup G} (hS : IsSylowTwoOf S H) (hX : X ∈ lFamily S)
    (hKc : K ∈ cComp H) (hXK : X < K) : modO2Image H X ≠ modO2Image H K := by
  intro heq
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hKXS : K ≤ X ⊔ S := by
    intro k hk
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨k, hKH hk⟩ : ↥H) ∈ modO2Image H X := by
      rw [heq]
      exact Subgroup.mem_map_of_mem _ (show (⟨k, hKH hk⟩ : ↥H) ∈ K.subgroupOf H from hk)
    obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.mp hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxk
    have hO : ((x⁻¹ * ⟨k, hKH hk⟩ : ↥H) : G) ∈ pCoreOf 2 H := by
      exact ⟨_, hxk, rfl⟩
    have hOS : ((x⁻¹ * ⟨k, hKH hk⟩ : ↥H) : G) ∈ S := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS hO
    have hk' : k = (x : G) * ((x⁻¹ * ⟨k, hKH hk⟩ : ↥H) : G) := by
      simp
    rw [hk']
    exact (X ⊔ S).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hOS)
  have hsubK : IsSubnormal X K :=
    A4.subnormal_of_le_of_le (subnormal_of_mem_cComp (show X ∈ cComp (X ⊔ S) from hX))
      hXK.le hKXS
  have hsubH : IsSubnormal X H := A4.subnormal_trans hsubK (subnormal_of_mem_cComp hKc)
  have hX0 : X ≠ ⊥ := ne_bot_of_mem_cComp (show X ∈ cComp (X ⊔ S) from hX)
  have hXp : ⁅X, X⁆ = X := perfect_of_mem_cComp (show X ∈ cComp (X ⊔ S) from hX)
  exact not_subnormal_of_mem_cComp hKc hXK hX0 hXp hsubH

theorem commutator_le_pCoreOf_H (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    {H K₁ K₂ : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (h₁ : K₁ ∈ cComp H) (h₂ : K₂ ∈ cComp H)
    (hne : K₁ ≠ K₂) : ⁅K₁, K₂⁆ ≤ pCoreOf 2 H :=
  (Vol2Native.lemma_1_2_1_two hK h37 hH h₁ h₂ hne).1.trans
    (Vol2Native.lemma_1_2_1_two hK h37 hH h₁ h₂ hne).2

end CFSG.Quasithin.Vol2.Ch10.SecB
