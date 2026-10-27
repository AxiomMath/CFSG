module

public import CFSG.Quasithin.EmptyFaithful.S153WSwap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Pair
public import CFSG.Quasithin.EmptyFaithful.S153WC56

public section

namespace CFSG.QuasithinUnique.AppCS2W

open CFSG.QuasithinUnique.AppCS2 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

structure WTwo (H S L : Subgroup G) (t x : G) where
  C : WCfg2 H S L t
  C' : WCfg2 H S (conjR L t) t⁻¹
  hx : x ∈ normalizer (S : Set G)
  hUV : ⁅blockU L, conjR (blockU L) x⁆ ≠ ⊥
  M₀ : Subgroup G
  hSM : S ≤ M₀
  hC52 : C5.NoCommonNormal S H M₀
  h2 : S.relIndex M₀ = 2
  hxM : x ∈ M₀
  hxS : x ∉ S

namespace WTwo

variable {t x : G} (X : WTwo H S L t x)
include X

theorem hVE : X.C.P.im (conjR (blockU L) x) = Estd := X.C.im_V_eq X.hx X.hUV

theorem U₂_le_D₁ : blockU2 L t ≤ s2I S L := by
  intro u hu
  refine ⟨X.C.D.blockU2_le_baum X.C.P.toPiData hu, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
  exact X.C.D.comm_elem a ha u (X.C.D.blockU2_le_L₂ hu)

theorem U₁_le_D₂ : blockU L ≤ s2I S (conjR L t) := by
  intro u hu
  refine ⟨X.C.U_le_baum hu, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
  exact (X.C.D.comm_elem u (X.C.D.blockU_le_L hu) b hb).symm

theorem V₁_comm_U₂ {v u : G} (hv : v ∈ conjR (blockU L) x) (hu : u ∈ blockU2 L t) :
    v * u = u * v :=
  Subgroup.mem_centralizer_iff.1 (X.C.D1_le_centralizer_V X.hx X.hVE (X.U₂_le_D₁ hu)) v hv

theorem conjR_V₁_cases {g : G} (hg : g ∈ S) :
    conjR (conjR (blockU L) x) g = conjR (blockU L) x ∨
      conjR (conjR (blockU L) x) g = conjR (blockU2 L t) x := by
  have hxg : x * g * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 X.hx g).1 hg
  have e : conjR (conjR (blockU L) x) g = conjR (conjR (blockU L) (x * g * x⁻¹)) x := by
    rw [WDbl.conjR_conjR, WDbl.conjR_conjR]
    congr 1
    group
  rw [e]
  rcases X.C.D.conjR_blockU_cases hxg with h | h
  · left; rw [h]
  · right; rw [h]

theorem conjR_V₂_cases {g : G} (hg : g ∈ S) :
    conjR (conjR (blockU2 L t) x) g = conjR (blockU L) x ∨
      conjR (conjR (blockU2 L t) x) g = conjR (blockU2 L t) x := by
  have hxg : x * g * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 X.hx g).1 hg
  have e : conjR (conjR (blockU2 L t) x) g = conjR (conjR (blockU2 L t) (x * g * x⁻¹)) x := by
    rw [WDbl.conjR_conjR, WDbl.conjR_conjR]
    congr 1
    group
  rw [e]
  by_cases hN : x * g * x⁻¹ ∈ normalizer (L : Set G)
  · right; rw [(X.C.D.conjR_blockU_of_mem ⟨hxg, hN⟩).2]
  · left; rw [(X.C.D.conjR_blockU_of_not_mem hxg hN).2]

theorem conjR_V₁_t : conjR (conjR (blockU L) x) t = conjR (blockU2 L t) x := by
  rcases X.conjR_V₁_cases X.C.D.ht with h | h
  · exfalso
    have hcomm : ⁅blockU2 L t, conjR (blockU L) x⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact X.V₁_comm_U₂ hv hu
    apply X.hUV
    have h1 : conjR ⁅blockU L, conjR (blockU L) x⁆ t =
        ⁅blockU2 L t, conjR (conjR (blockU L) x) t⁆ := conjR_comm_aux t
    rw [h, hcomm] at h1
    exact Lin2.conjR_eq_bot_iff.1 h1
  · exact h

theorem hUV₂ : ⁅blockU2 L t, conjR (blockU2 L t) x⁆ ≠ ⊥ := by
  intro h
  apply X.hUV
  have h1 : conjR ⁅blockU L, conjR (blockU L) x⁆ t =
      ⁅blockU2 L t, conjR (conjR (blockU L) x) t⁆ := conjR_comm_aux t
  rw [X.conjR_V₁_t, h] at h1
  exact Lin2.conjR_eq_bot_iff.1 h1

theorem hVE₂ : X.C'.P.im (conjR (blockU2 L t) x) = Estd := by
  have := X.C'.im_V_eq X.hx (by rw [blockU_L₂]; exact X.hUV₂)
  rwa [blockU_L₂] at this

theorem V₂_comm_U₁ {v u : G} (hv : v ∈ conjR (blockU2 L t) x) (hu : u ∈ blockU L) :
    v * u = u * v := by
  have hD := X.C'.D1_le_centralizer_V X.hx (by rw [blockU_L₂]; exact X.hVE₂) (X.U₁_le_D₂ hu)
  rw [blockU_L₂] at hD
  exact Subgroup.mem_centralizer_iff.1 hD v hv

theorem V₁_comm_V₂ {a b : G} (ha : a ∈ conjR (blockU L) x) (hb : b ∈ conjR (blockU2 L t) x) :
    a * b = b * a := by
  have ha' : x * a * x⁻¹ ∈ blockU L := mem_conjSubgroup_iff.1 ha
  have hb' : x * b * x⁻¹ ∈ blockU2 L t := mem_conjSubgroup_iff.1 hb
  have hc : (x * a * x⁻¹) * (x * b * x⁻¹) = (x * b * x⁻¹) * (x * a * x⁻¹) :=
    X.C.D.U1_comm_U2 _ ha' _ hb'
  have e1 : (x * a * x⁻¹) * (x * b * x⁻¹) = x * (a * b) * x⁻¹ := by group
  have e2 : (x * b * x⁻¹) * (x * a * x⁻¹) = x * (b * a) * x⁻¹ := by group
  rw [e1, e2] at hc
  have := mul_left_cancel (mul_right_cancel hc)
  exact this

theorem U₂_V₁_bot : ⁅blockU2 L t, conjR (blockU L) x⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact X.V₁_comm_U₂ hv hu

theorem U₁_V₂_bot : ⁅blockU L, conjR (blockU2 L t) x⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact X.V₂_comm_U₁ hv hu

theorem s2SI_le_N_V₁ : s2SI S L ≤ normalizer (conjR (blockU L) x : Set G) := by
  intro g hg
  rw [← Lin2.conjR_eq_self_iff]
  rcases X.conjR_V₁_cases hg.1 with h | h
  · exact h
  · exfalso
    have hU := (X.C.D.conjR_blockU_of_mem hg).1
    have h1 : conjR ⁅blockU L, conjR (blockU L) x⁆ g =
        ⁅conjR (blockU L) g, conjR (conjR (blockU L) x) g⁆ := conjR_comm_aux g
    rw [hU, h, X.U₁_V₂_bot] at h1
    exact X.hUV (Lin2.conjR_eq_bot_iff.1 h1)

theorem s2SI_le_N_V₂ : s2SI S L ≤ normalizer (conjR (blockU2 L t) x : Set G) := by
  intro g hg
  rw [← Lin2.conjR_eq_self_iff]
  rcases X.conjR_V₂_cases hg.1 with h | h
  · exfalso
    have hU := (X.C.D.conjR_blockU_of_mem hg).2
    have h1 : conjR ⁅blockU2 L t, conjR (blockU2 L t) x⁆ g =
        ⁅conjR (blockU2 L t) g, conjR (conjR (blockU2 L t) x) g⁆ := conjR_comm_aux g
    rw [hU, h, X.U₂_V₁_bot] at h1
    exact X.hUV₂ (Lin2.conjR_eq_bot_iff.1 h1)
  · exact h

theorem conjR_V₁_of_not_mem {g : G} (hg : g ∈ S) (hn : g ∉ normalizer (L : Set G)) :
    conjR (conjR (blockU L) x) g = conjR (blockU2 L t) x ∧
      conjR (conjR (blockU2 L t) x) g = conjR (blockU L) x := by
  obtain ⟨hU1, hU2⟩ := X.C.D.conjR_blockU_of_not_mem hg hn
  refine ⟨?_, ?_⟩
  · rcases X.conjR_V₁_cases hg with h | h
    · exfalso
      have h1 : conjR ⁅blockU L, conjR (blockU L) x⁆ g =
          ⁅conjR (blockU L) g, conjR (conjR (blockU L) x) g⁆ := conjR_comm_aux g
      rw [hU1, h, X.U₂_V₁_bot] at h1
      exact X.hUV (Lin2.conjR_eq_bot_iff.1 h1)
    · exact h
  · rcases X.conjR_V₂_cases hg with h | h
    · exact h
    · exfalso
      have h1 : conjR ⁅blockU2 L t, conjR (blockU2 L t) x⁆ g =
          ⁅conjR (blockU2 L t) g, conjR (conjR (blockU2 L t) x) g⁆ := conjR_comm_aux g
      rw [hU2, h, X.U₁_V₂_bot] at h1
      exact X.hUV₂ (Lin2.conjR_eq_bot_iff.1 h1)

theorem mem_s2SI_of_normalizer_V₁ {g : G} (hg : g ∈ S)
    (hN : g ∈ normalizer (conjR (blockU L) x : Set G)) : g ∈ s2SI S L := by
  by_contra hn
  have hn' : g ∉ normalizer (L : Set G) := fun h => hn ⟨hg, h⟩
  have h := (X.conjR_V₁_of_not_mem hg hn').1
  have hV : conjR (conjR (blockU L) x) g = conjR (blockU L) x := Lin2.conjR_eq_self_iff.2 hN
  rw [hV] at h
  apply X.hUV
  rw [h]
  exact X.U₁_V₂_bot

theorem mem_s2SI_of_comm_V₁ {g : G} (hg : g ∈ S)
    (hc : ∀ v ∈ conjR (blockU L) x, g * v = v * g) : g ∈ s2SI S L :=
  X.mem_s2SI_of_normalizer_V₁ hg
    (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun v hv => (hc v hv).symm))

end WTwo

end CFSG.QuasithinUnique.AppCS2W
