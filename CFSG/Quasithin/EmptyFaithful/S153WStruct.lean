module

public import CFSG.Quasithin.EmptyFaithful.S153WPair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Struct

public section

namespace CFSG.QuasithinUnique.AppCS2W

open CFSG.QuasithinUnique.AppCS2 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

namespace WCfg2

variable {t : G} (C : WCfg2 H S L t)
include C

theorem Q1_decomp {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ baum S)) :
    ∃ u ∈ blockU L, ∃ d ∈ s2I S L, u * d = q := by
  have hq' := hq
  rw [C.D.Q1_eq_sup, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right (blockU L) (s2I S L) C.U_le_normalizer_D1] at hq'
  obtain ⟨u, hu, d, hd, hud⟩ := hq'
  exact ⟨u, hu, d, hd, hud⟩

end WCfg2

namespace WTwo

variable {t x : G} (X : WTwo H S L t x)
include X

theorem baumD_eq : baumD S L = s2I S L ⊓ s2I S (conjR L t) :=
  baumD_eq_of_hjoin X.C.D.hjoin

theorem Q₂_decomp {q : G} (hq : q ∈ pCoreOf 2 (conjR L t ⊔ baum S)) :
    ∃ u ∈ blockU2 L t, ∃ d ∈ s2I S (conjR L t), u * d = q := by
  obtain ⟨u, hu, d, hd, h⟩ := X.C'.Q1_decomp hq
  rw [blockU_L₂] at hu
  exact ⟨u, hu, d, hd, h⟩

theorem exists_V₂_mul {b : G} (hb : b ∈ baum S) :
    ∃ v ∈ conjR (blockU2 L t) x, v⁻¹ * b ∈ pCoreOf 2 (conjR L t ⊔ baum S) := by
  have := X.C'.exists_mem_V_mul_Q1 X.hx (by rw [blockU_L₂]; exact X.hVE₂) hb
  rwa [blockU_L₂] at this

theorem cent_U₂_V₂ :
    blockU2 L t ⊓ centralizer (conjR (blockU2 L t) x : Set G) =
        blockU2 L t ⊓ conjR (blockU2 L t) x ∧
      blockU2 L t ⊓ conjR (blockU2 L t) x =
        conjR (blockU2 L t) x ⊓ centralizer (blockU2 L t : Set G) := by
  have := X.C'.cent_U_V X.hx (by rw [blockU_L₂]; exact X.hVE₂)
  rw [blockU_L₂] at this
  exact ⟨this.2.1, this.2.2⟩

theorem D₁_le_C_V₁ : s2I S L ≤ centralizer (conjR (blockU L) x : Set G) :=
  X.C.D1_le_centralizer_V X.hx X.hVE

theorem cent_U₁_V₁ :
    blockU L ⊓ centralizer (conjR (blockU L) x : Set G) = blockU L ⊓ conjR (blockU L) x ∧
      blockU L ⊓ conjR (blockU L) x = conjR (blockU L) x ⊓ centralizer (blockU L : Set G) := by
  have := X.C.cent_U_V X.hx X.hVE
  exact ⟨this.2.1, this.2.2⟩

theorem B_decomp {b : G} (hb : b ∈ baum S) :
    ∃ w₁ ∈ blockU L ⊔ conjR (blockU L) x, ∃ w₂ ∈ blockU2 L t ⊔ conjR (blockU2 L t) x,
      ∃ d ∈ baumD S L, b = w₁ * w₂ * d := by
  obtain ⟨v₁, hv₁, hq⟩ := X.C.exists_mem_V_mul_Q1 X.hx X.hVE hb
  obtain ⟨u, hu, d₁, hd₁, hud⟩ := X.C.Q1_decomp hq
  obtain ⟨v₂, hv₂, hq₂⟩ := X.exists_V₂_mul hd₁.1
  obtain ⟨u₂, hu₂, d₂, hd₂, hud₂⟩ := X.Q₂_decomp hq₂
  have hd₁₂ : d₁ = v₂ * (u₂ * d₂) := by rw [hud₂]; group
  have hb₁ : b = v₁ * (u * d₁) := by rw [hud]; group
  have hd₂eq : d₂ = u₂⁻¹ * (v₂⁻¹ * d₁) := by
    have : u₂ * d₂ = v₂⁻¹ * d₁ := hud₂
    calc d₂ = u₂⁻¹ * (u₂ * d₂) := by group
      _ = u₂⁻¹ * (v₂⁻¹ * d₁) := by rw [this]
  have hcU : ∀ a ∈ blockU L, a * d₂ = d₂ * a := by
    intro a ha
    have c1 : Commute a u₂ := X.C.D.U1_comm_U2 a ha u₂ hu₂
    have c2 : Commute a v₂ := (X.V₂_comm_U₁ hv₂ ha).symm
    have c3 : Commute a d₁ :=
      Subgroup.mem_centralizer_iff.1 hd₁.2 a (X.C.D.blockU_le_L ha)
    rw [hd₂eq]
    exact ((c1.inv_right).mul_right ((c2.inv_right).mul_right c3)).eq
  have hcV : ∀ a ∈ conjR (blockU L) x, a * d₂ = d₂ * a := by
    intro a ha
    have c1 : Commute a u₂ := X.V₁_comm_U₂ ha hu₂
    have c2 : Commute a v₂ := X.V₁_comm_V₂ ha hv₂
    have c3 : Commute a d₁ := Subgroup.mem_centralizer_iff.1 (X.D₁_le_C_V₁ hd₁) a ha
    rw [hd₂eq]
    exact ((c1.inv_right).mul_right ((c2.inv_right).mul_right c3)).eq
  have hd₂B : d₂ ∈ baum S ⊓ centralizer (blockU L : Set G) :=
    ⟨hd₂.1, Subgroup.mem_centralizer_iff.2 fun a ha => hcU a ha⟩
  rw [← X.C.D.Q1_eq_inf] at hd₂B
  obtain ⟨e, he, d', hd', hed⟩ := X.C.Q1_decomp hd₂B
  have hed' : e * d' = d₂ := hed
  have heV : e ∈ conjR (blockU L) x := by
    have hcomm : ∀ a ∈ conjR (blockU L) x, a * e = e * a := by
      intro a ha
      have c1 : Commute a d₂ := hcV a ha
      have c2 : Commute a d' := Subgroup.mem_centralizer_iff.1 (X.D₁_le_C_V₁ hd') a ha
      have : e = d₂ * d'⁻¹ := by rw [← hed']; group
      rw [this]
      exact (c1.mul_right c2.inv_right).eq
    have h1 : e ∈ blockU L ⊓ centralizer (conjR (blockU L) x : Set G) :=
      ⟨he, Subgroup.mem_centralizer_iff.2 fun a ha => hcomm a ha⟩
    rw [X.cent_U₁_V₁.1] at h1
    exact h1.2
  have hd'₂ : d' ∈ s2I S (conjR L t) := by
    have h1 : e⁻¹ * d₂ ∈ s2I S (conjR L t) :=
      (s2I S (conjR L t)).mul_mem ((s2I S (conjR L t)).inv_mem (X.U₁_le_D₂ he)) hd₂
    have : d' = e⁻¹ * d₂ := by rw [← hed']; group
    rw [this]
    exact h1
  have hdD : d' ∈ baumD S L := by
    rw [X.baumD_eq]
    exact ⟨hd', hd'₂⟩
  have hev : e * (v₂ * u₂) = (v₂ * u₂) * e := by
    have c1 : Commute e v₂ := (X.V₂_comm_U₁ hv₂ he).symm
    have c2 : Commute e u₂ := X.C.D.U1_comm_U2 e he u₂ hu₂
    exact (c1.mul_right c2).eq
  have hcu : u * v₂ = v₂ * u := (X.V₂_comm_U₁ hv₂ hu).symm
  refine ⟨v₁ * u * e, ?_, v₂ * u₂, ?_, d', hdD, ?_⟩
  · exact (blockU L ⊔ conjR (blockU L) x).mul_mem
      ((blockU L ⊔ conjR (blockU L) x).mul_mem (Subgroup.mem_sup_right hv₁)
        (Subgroup.mem_sup_left hu)) (Subgroup.mem_sup_left he)
  · exact (blockU2 L t ⊔ conjR (blockU2 L t) x).mul_mem (Subgroup.mem_sup_right hv₂)
      (Subgroup.mem_sup_left hu₂)
  · rw [hb₁, hd₁₂, ← hed']
    calc v₁ * (u * (v₂ * (u₂ * (e * d')))) = v₁ * u * ((v₂ * u₂) * e) * d' := by group
      _ = v₁ * u * (e * (v₂ * u₂)) * d' := by rw [hev]
      _ = v₁ * u * e * (v₂ * u₂) * d' := by group

theorem baum_eq :
    baum S = baumD S L ⊔ blockU0 S L ⊔ conjR (blockU0 S L) x := by
  have hU0 : blockU0 S L = U0 L t := X.C.D.blockU0_eq
  have hU1 : blockU L ≤ blockU0 S L := by rw [hU0]; exact le_sup_left
  have hU2 : blockU2 L t ≤ blockU0 S L := by rw [hU0]; exact le_sup_right
  have hV1 : conjR (blockU L) x ≤ conjR (blockU0 S L) x := C5.conjSubgroup_mono hU1 x
  have hV2 : conjR (blockU2 L t) x ≤ conjR (blockU0 S L) x := C5.conjSubgroup_mono hU2 x
  have hU0B : blockU0 S L ≤ baum S := by rw [hU0]; exact X.C.D.U0_le_baum X.C.P.toPiData
  have hVB : conjR (blockU0 S L) x ≤ baum S := by
    have := C5.conjSubgroup_mono hU0B x
    rwa [C5.conjSubgroup_eq_self (normalizer_le_normalizer_baum S X.hx)] at this
  apply le_antisymm
  · intro b hb
    obtain ⟨w₁, hw₁, w₂, hw₂, d, hd, rfl⟩ := X.B_decomp hb
    have hR₁ : blockU L ⊔ conjR (blockU L) x ≤ baumD S L ⊔ blockU0 S L ⊔ conjR (blockU0 S L) x :=
      sup_le (hU1.trans (le_sup_right.trans le_sup_left)) (hV1.trans le_sup_right)
    have hR₂ : blockU2 L t ⊔ conjR (blockU2 L t) x ≤
        baumD S L ⊔ blockU0 S L ⊔ conjR (blockU0 S L) x :=
      sup_le (hU2.trans (le_sup_right.trans le_sup_left)) (hV2.trans le_sup_right)
    exact mul_mem (mul_mem (hR₁ hw₁) (hR₂ hw₂)) (Subgroup.mem_sup_left (Subgroup.mem_sup_left hd))
  · exact sup_le (sup_le inf_le_left hU0B) hVB

end WTwo

end CFSG.QuasithinUnique.AppCS2W
