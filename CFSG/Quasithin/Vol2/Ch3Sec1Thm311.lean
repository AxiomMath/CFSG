module

public import CFSG.Quasithin.Vol2.Ch3Sec1Defs
public import CFSG.Quasithin.EmptyFaithful.QTKELocal

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowTwoOf_of_isSylowTwo {T H : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTH : T ≤ H) : IsSylowTwoOf T H :=
  ⟨hTH, hT.1, fun h => hT.2 (h.trans (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTH))⟩

omit [Finite G] in
theorem exists_sylow_coe_eq {T : Subgroup G} (hT : quasithinIsSylowTwo T) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = T :=
  ⟨hT.1.toSylow hT.2, rfl⟩

theorem charTwo_of_inH' (hK : quasithinIsQTKECat G) {T H : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hH : InH T H) : CharTwo H := by
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hT
  exact charTwo_of_inH hK.2.1 S hH

theorem isSQTKSub_of_inH (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {T H : Subgroup G} (hH : InH T H) : IsSQTKSub H :=
  ⟨kGroup_of_pCoreOf_ne_bot hK hs hnab hH.2, stronglyQuasithin_of_pCoreOf_ne_bot hK hH.2⟩

theorem hypC51_of_311 (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : quasithinIsQTKECat G) {T : Subgroup G} (hT : quasithinIsSylowTwo T) {M₀ H R : Subgroup G}
    (hM₀ : InH T M₀) (hH : InH T H) (hu : ∃ N : Subgroup G, IsUniqueMaxOver H T N)
    (hRT : R ≤ T) (hRS : IsSylowTwoOf R (oTwoUpper H ⊔ R))
    (hRn : M₀ ≤ Subgroup.normalizer (R : Set G)) : HypC51 H M₀ R T :=
  ⟨isSQTKSub_of_inH hK hs hnab hH, isSQTKSub_of_inH hK hs hnab hM₀, charTwo_of_inH' hK hT hH,
    isSylowTwoOf_of_isSylowTwo hT hH.1, hu, hRT, hM₀.1, hRS, hRn⟩

theorem theorem311_of_C58 (hC : TheoremC58) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G) {T : Subgroup G}
    (hT : quasithinIsSylowTwo T) {M₀ H R : Subgroup G} (hM₀ : InH T M₀) (hH : InH T H)
    (hu : ∃ N : Subgroup G, IsUniqueMaxOver H T N) (hR1 : R ≠ ⊥) (hRT : R ≤ T)
    (hRS : IsSylowTwoOf R (oTwoUpper H ⊔ R)) (hRn : M₀ ≤ Subgroup.normalizer (R : Set G)) :
    ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ R ∧ M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G) :=
  hC G T hs hnab hK hT H M₀ R (hypC51_of_311 hs hnab hK hT hM₀ hH hu hRT hRS hRn) hR1

theorem theorem311Stmt_of_C58 (hC : TheoremC58) : Theorem311Stmt :=
  fun _ _ _ _ hs hnab hK hT _ _ _ hM₀ hH hu hR1 hRT hRS hRn =>
    theorem311_of_C58 hC hs hnab hK hT hM₀ hH hu hR1 hRT hRS hRn

namespace Hyp315Base

variable {T M M₀ H V : Subgroup G}

theorem inH_M₀ (h : Hyp315Base T M M₀ H V) (hT : quasithinIsSylowTwo T) (hM : InM T M) :
    InH T M₀ := by
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hT
  exact inH_of_le S h.T_le h.le_M (inH_of_inM hM)

omit [Finite G] in
theorem inH_H (h : Hyp315Base T M M₀ H V) : InH T H := h.hStar.1

omit [Finite G] in
theorem T_le_M (h : Hyp315Base T M M₀ H V) : T ≤ M := h.T_le.trans h.le_M

theorem isUniqueMaxOver (h : Hyp315Base T M M₀ H V) (hT : quasithinIsSylowTwo T) :
    IsUniqueMaxOver H T (H ⊓ M) := by
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hT
  exact h.hStar.isUniqueMaxOver S h.T_le_M

omit [Finite G] in
theorem pCoreOf_le_T (h : Hyp315Base T M M₀ H V) : pCoreOf 2 M₀ ≤ T :=
  h.centralizer ▸ inf_le_left

theorem hyp311 (h : Hyp315Base T M M₀ H V) (hT : quasithinIsSylowTwo T) (hM : InM T M) :
    InH T M₀ ∧ InH T H ∧ (∃ N : Subgroup G, IsUniqueMaxOver H T N) ∧ pCoreOf 2 M₀ ≠ ⊥ ∧
      pCoreOf 2 M₀ ≤ T ∧ M₀ ≤ Subgroup.normalizer (pCoreOf 2 M₀ : Set G) :=
  ⟨h.inH_M₀ hT hM, h.inH_H, ⟨_, h.isUniqueMaxOver hT⟩, (h.inH_M₀ hT hM).2, h.pCoreOf_le_T,
    le_normalizer_pCoreOf 2 M₀⟩

theorem exists_normal_of_sylow (hC : TheoremC58) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hM : InM T M) (h : Hyp315Base T M M₀ H V)
    (hRS : IsSylowTwoOf (pCoreOf 2 M₀) (oTwoUpper H ⊔ pCoreOf 2 M₀)) :
    ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
      M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.hyp311 hT hM
  exact theorem311_of_C58 hC hs hnab hK hT h1 h2 h3 h4 h5 hRS h6

end Hyp315Base

end CFSG.Quasithin
