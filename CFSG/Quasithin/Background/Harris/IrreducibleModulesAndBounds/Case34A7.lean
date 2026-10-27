module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case34A7Dual6
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case34A7NotDual
public import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPLAux
public import CFSG.CGT.T75K.ExoticHat

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open

namespace Case34A7

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem case4_of_data {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    {f : ↥L ≃* ↥(alternatingGroup (Fin 7))} {β : ↥(permCore 7) →ₗ[ZMod 2] V}
    (hβ : PermCoreData f β) (hd : Module.finrank (ZMod 2) V = 6) (hm3 : m ≤ 3) :
    G93Case4 L m := by
  have hb := h.bound
  refine ⟨⟨by omega, hd, hm3, ?_⟩, endIsField_one_of_permCore h.H_irr hβ,
    selfDual_of_permCore hβ⟩
  refine ⟨f, β, hβ.1.2, fun u => ?_, hβ.2⟩
  have hβ0 : β 0 = 0 := map_zero β
  constructor
  · intro hu
    left
    exact hβ.1.1 (hu.trans hβ0.symm)
  · rintro (hu | ⟨hev, -⟩)
    · rw [hu, hβ0]
    · exact absurd hev (by decide)

theorem case3_of_data {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (f : ↥L ≃* ↥(alternatingGroup (Fin 7))) (hd : Module.finrank (ZMod 2) V = 4) :
    G93Case3 Γ L m := by
  have hb := h.bound
  have hV : Nat.card V = 16 := by
    have := natCard_multiplicative (V := V)
    rw [hd] at this
    exact this
  have hLcard : Nat.card ↥L = 2520 := by
    rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 7 (by rw [hLcard]; norm_num)
  have hgL : ((x : ↥L) : GLV V) ∈ L := x.2
  have hg : orderOf ((x : ↥L) : GLV V) = 7 := by rw [Subgroup.orderOf_coe]; exact hx
  have hΓL : Γ = L := by
    have hLΓ : L ≤ Γ := h.L_comp.1
    refine le_antisymm (fun γ hγ => ?_) hLΓ
    have hcomm : ∀ a b : Multiplicative V, a * b = b * a := fun a b => mul_comm a b
    obtain ⟨hcardM, hsimple⟩ := CFSG.AGLEmbedding.BlockAltSevenPL.card_mulAut_eq_and_isSimpleGroup
      (W := Multiplicative V) hcomm multiplicative_sq_eq_one
      (by rw [natCard_multiplicative, hd])
    have hcardH : Nat.card ↥(toMulSub L) = 2520 := by rw [natCard_toMulSub, hLcard]
    have hmem : linEquivMulAut γ ∈ Subgroup.normalizer (toMulSub L : Set (MulAut (Multiplicative V))) :=
      toMulSub_le_normalizer h.H_normal le_rfl ⟨γ, hγ, rfl⟩
    have := CFSG.AGLEmbedding.BlockAltSevenPL.mem_of_mem_normalizer_of_index_eight hcardM hcardH hmem
    exact linEquivMulAut_mem_toMulSub.1 this
  have hAL : A ≤ L := hΓL ▸ h.A_le
  have hm2 : m ≤ 2 := by
    let ι : ↥A →* ↥(alternatingGroup (Fin 7)) := f.toMonoidHom.comp (Subgroup.inclusion hAL)
    have hι : Function.Injective ι := f.injective.comp (Subgroup.inclusion_injective hAL)
    have h1 : m ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥(alternatingGroup (Fin 7))) :=
      CFSG.SectionRank.le_pRank_of_injective Nat.one_lt_two
        (fun a b => h.A_elem.1.is_comm.comm a b)
        (fun a => Subtype.ext (by simpa using h.A_elem.2 (a : GLV V) a.2)) h.A_card ι hι
        (le_top)
    exact h1.trans CFSG.CGT.T75K.twoRank_alternatingGroup_seven_le_two'
  refine ⟨⟨by omega, hm2, hd, ?_, hΓL.symm⟩, endIsField_one_of_order_seven h.H_irr hgL hg hV,
    not_selfDual_of_order_seven h.H_irr hgL hg hV⟩
  exact ⟨(MulEquiv.subgroupCongr hΓL).trans f⟩

theorem case34_A7 {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hX : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7))) :
    G93Concl Γ L m := by
  obtain ⟨e⟩ := hX
  obtain ⟨f, h4, h8, hm3, hd⟩ := data h e
  rcases hd with hd4 | ⟨hd6, β, hβ⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl (case3_of_data h f hd4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (case4_of_data h hβ hd6 hm3)))))

end Case34A7

theorem case34_A7 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hX : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7))) :
    G93Concl Γ L m :=
  Case34A7.case34_A7 h hX

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
