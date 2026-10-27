module

public import CFSG.Quasithin.EmptyFaithful.S152L27B
public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def HeNoSmallCommutatorModule : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (K T X Q E L N : Subgroup Γ),
    X = K ⊔ T → (∀ g ∈ X, ∀ k ∈ K, g * k * g⁻¹ ∈ K) →
    Nonempty (OTwoQuot K ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) → IsSylowTwoOf T X →
    E ≤ T → (∀ t ∈ T, ∀ e ∈ E, t * e * t⁻¹ ∈ E) → Q ≤ X → IsPGroup 2 Q →
    IsChiefStep X Q L N → ¬ ⁅N, E⁆ ≤ L → 8 * Nat.card L ≤ Nat.card ↥(⁅N, E⁆ ⊔ L)

section Counting

variable {G : Type*} [Group G] [Finite G]

theorem card_sup_le_mul_card152 {Vc Z L : Subgroup G} (hZVc : Z ≤ Vc) (hZL : Z ≤ L)
    (hn : Vc ≤ Subgroup.normalizer (L : Set G)) {k : ℕ} (hcard : Nat.card Vc ≤ k * Nat.card Z) :
    Nat.card ↥(Vc ⊔ L) ≤ k * Nat.card L := by
  have hprod : ((Vc ⊔ L : Subgroup G) : Set G) = (Vc : Set G) * (L : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Vc L hn
  have hmul := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient L (Vc : Set G)
  rw [← hprod] at hmul
  have hc : Nat.card ↥(Vc ⊔ L) =
      Nat.card L * Nat.card (((Vc : Set G).image (↑) : Set (G ⧸ L))) := hmul
  have himg : Nat.card (((Vc : Set G).image (↑) : Set (G ⧸ L))) ≤ k := by
    let Zs : Subgroup ↥Vc := Z.subgroupOf Vc
    let f : ↥Vc ⧸ Zs → G ⧸ L := Quotient.lift (fun v : ↥Vc => ((v : G) : G ⧸ L)) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ Zs := QuotientGroup.leftRel_apply.mp hab
      have hz : (a : G)⁻¹ * (b : G) ∈ Z := Subgroup.mem_subgroupOf.mp hab'
      show ((a : G) : G ⧸ L) = ((b : G) : G ⧸ L)
      rw [QuotientGroup.eq]
      exact hZL hz)
    have hsub : (((Vc : Set G).image (↑) : Set (G ⧸ L))) ⊆ Set.range f := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨QuotientGroup.mk ⟨a, ha⟩, rfl⟩
    have hq : Nat.card (↥Vc ⧸ Zs) * Nat.card Zs = Nat.card Vc :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup Zs).symm
    have hZs : Nat.card Zs = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZVc).toEquiv
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    have hqk : Nat.card (↥Vc ⧸ Zs) ≤ k := by
      rw [hZs] at hq
      by_contra hlt
      push Not at hlt
      have : k * Nat.card Z < Nat.card (↥Vc ⧸ Zs) * Nat.card Z :=
        Nat.mul_lt_mul_of_pos_right hlt hZpos
      omega
    calc Nat.card (((Vc : Set G).image (↑) : Set (G ⧸ L)))
        = Set.ncard ((Vc : Set G).image (↑) : Set (G ⧸ L)) := Nat.card_coe_set_eq _
      _ ≤ Set.ncard (Set.range f) := Set.ncard_le_ncard hsub
      _ = Nat.card (Set.range f) := (Nat.card_coe_set_eq _).symm
      _ ≤ Nat.card (↥Vc ⧸ Zs) :=
          Nat.card_le_card_of_surjective (Set.rangeFactorization f)
            (fun b => by obtain ⟨_, y, rfl⟩ := b; exact ⟨y, rfl⟩)
      _ ≤ k := hqk
  rw [hc, mul_comm]
  exact Nat.mul_le_mul_right _ himg

end Counting

section HeBranch

variable {G : Type} [Group G] [Finite G]

theorem false_of_he_small_commutator (hHe : HeNoSmallCommutatorModule) {Kc T X Q V Z : Subgroup G}
    (hKc : Nonempty (OTwoQuot Kc ≃* CFSG.Blueprint.NativeSporadic.Carrier .He))
    (hXKT : X = Kc ⊔ T) (hXn : ∀ g ∈ X, ∀ k ∈ Kc, g * k * g⁻¹ ∈ Kc) (hsyl : IsSylowTwoOf T X)
    (hQ : IsPGroup 2 Q) (hQT : Q ≤ T) (hQX : ∀ g ∈ X, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hchar : ∀ x ∈ X, (∀ q ∈ Q, q * x = x * q) → x ∈ Q)
    (hVT : V ≤ T) (hVTn : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) (hV16 : Nat.card V = 16)
    (hVQ : ¬ V ≤ Q) (hVOX : ¬ V ≤ pCoreOf 2 X)
    (hZ : IsPGroup 2 Z) (hZV : Z ≤ V) (hZQ : Z ≤ Q) (hZcard : 2 ≤ Nat.card Z)
    (hZc : ∀ g ∈ X, ∀ z ∈ Z, g * z * g⁻¹ = z) : False := by
  have hTX : T ≤ X := hsyl.1
  have hVX : V ≤ X := hVT.trans hTX
  have hQXle : Q ≤ X := hQT.trans hTX
  obtain ⟨L, N, hLN, hZL, hNVL⟩ := exists_chiefStep_of_not_le_pCoreOf (X := X) (Q := Q) (ZS := Z)
    (Z := Z) (V := V) hQ hZ hZQ (fun g hg s hs => by rw [hZc g hg s hs]; exact hs)
    (fun g hg s hs => by rw [hZc g hg s hs]; simp) hZc hQX hchar hVX hVOX
  have hNQ : N ≤ Q := hLN.1.1
  have hcommVc : ⁅N, V⁆ ≤ V ⊓ Q := by
    refine Subgroup.commutator_le.mpr fun n hn v hv => ?_
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · exact V.mul_mem (hVTn n (hQT (hNQ hn)) v hv) (V.inv_mem hv)
    · have h1 : v * n⁻¹ * v⁻¹ ∈ Q := hQX v (hVX hv) n⁻¹ (Q.inv_mem (hNQ hn))
      have := Q.mul_mem (hNQ hn) h1
      simpa [mul_assoc] using this
  have hVc_lt : V ⊓ Q < V := lt_of_le_of_ne inf_le_left fun h => hVQ (h ▸ inf_le_right)
  have hcardVc : Nat.card (V ⊓ Q : Subgroup G) ≤ 8 := by
    have hlt := Subgroup.card_lt_of_lt hVc_lt
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le (inf_le_left : V ⊓ Q ≤ V)
    rw [hV16] at hc hlt
    rcases c with _ | _ | c
    · omega
    · omega
    · have e : Nat.card (V ⊓ Q : Subgroup G) * (c + 1 + 1) =
          Nat.card (V ⊓ Q : Subgroup G) * c + Nat.card (V ⊓ Q : Subgroup G) * 2 := by ring
      omega
  have hVcn : V ⊓ Q ≤ Subgroup.normalizer (L : Set G) := by
    intro g hg
    have hgX : g ∈ X := hTX (hQT hg.2)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hLN.2.1.2 g hgX x hx, fun hx => ?_⟩
    have := hLN.2.1.2 g⁻¹ (X.inv_mem hgX) _ hx
    simpa [mul_assoc] using this
  have hsup := card_sup_le_mul_card152 (k := 4) (le_inf hZV hZQ) hZL hVcn (by omega)
  have hcard1 : Nat.card ↥(⁅N, V⁆ ⊔ L) ≤ 4 * Nat.card L :=
    (Subgroup.card_le_of_le (sup_le_sup_right hcommVc L)).trans hsup
  have h8 := hHe G Kc T X Q V L N hXKT hXn hKc hsyl hVT hVTn hQXle hQ hLN hNVL
  have hLpos : 0 < Nat.card L := Nat.card_pos
  omega

end HeBranch

end CFSG.Quasithin
