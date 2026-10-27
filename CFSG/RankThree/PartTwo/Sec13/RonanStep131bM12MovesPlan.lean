module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12Mixed

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def M12Hyp {G : Type} [Group G] [Finite G] (Y : Subgroup G) : Prop :=
  haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  Nonempty (Y ⧸ solvableRadical Y ≃* CFSG.Blueprint.NativeSporadic.M12)

structure RhoData {G : Type} [Group G] [Finite G] (E L : Subgroup G) (b c ρ : G) : Prop where
  pow_three : ρ ^ 3 = 1
  not_mem : ρ ∉ E
  comm_b : ρ * b = b * ρ
  mem_normalizer_E : ρ ∈ Subgroup.normalizer (E : Set G)
  mem_normalizer_L : ρ ∈ Subgroup.normalizer (L : Set G)
  mem_inner : ρ ∈ L ⊔ Sec4.thetaQuotCentralizer L
  comm_E : ∀ e ∈ E, ρ * e * ρ⁻¹ * e⁻¹ ∈ Subgroup.zpowers c

@[expose] def S1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y → M12Hyp Y →
      ∀ X : Subgroup G, IsPGroup 3 X → X ≤ Subgroup.centralizer ({b} : Set G) →
        Nat.card {x : G // x ∈ X ∧ x ^ 3 = 1} ≤ 81

@[expose] def S2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      b ∉ E ⊓ Sec4.thetaQuotCentralizer L → b ∉ E ⊓ L →
      ∀ (t : G) (EY : Subgroup G), InvData E b c Y t EY →
        t ∉ Subgroup.normalizer (L : Set G) → ∃ ρ : G, RhoData E L b c ρ

@[expose] def S3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      b ∉ E ⊓ Sec4.thetaQuotCentralizer L → b ∉ E ⊓ L →
      a ∉ L ⊔ Sec4.thetaQuotCentralizer L

@[expose] def S4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B N S₁ S₂ : Subgroup G),
    (∀ R : Subgroup G, IsPGroup 3 R → R ≤ B → Nat.card {x : G // x ∈ R ∧ x ^ 3 = 1} ≤ 81) →
    N ≤ B → S₁ ≤ N → S₂ ≤ N → IsPGroup 3 S₁ → IsPGroup 3 S₂ → Nat.card S₁ = 81 →
    Nat.card S₂ = 81 → (∀ x ∈ S₁, x ^ 3 = 1) → (∀ x ∈ S₂, x ^ 3 = 1) →
    ∃ g ∈ N, ∀ x ∈ S₁, g * x * g⁻¹ ∈ S₂

@[expose] def S5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      Nat.card (E ⊔ F : Subgroup G) = 81 ∧ IsPGroup 3 (E ⊔ F : Subgroup G) ∧
        (∀ x ∈ (E ⊔ F : Subgroup G), x ^ 3 = 1) ∧
        (E ⊔ F : Subgroup G) ≤ Subgroup.normalizer (E : Set G) ⊓
          Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.normalizer (L : Set G)

@[expose] def S6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y → ∀ ρ : G, RhoData E L b c ρ →
      Nat.card (E ⊔ Subgroup.zpowers ρ : Subgroup G) = 81 ∧
        IsPGroup 3 (E ⊔ Subgroup.zpowers ρ : Subgroup G) ∧
        (∀ x ∈ (E ⊔ Subgroup.zpowers ρ : Subgroup G), x ^ 3 = 1) ∧
        (E ⊔ Subgroup.zpowers ρ : Subgroup G) ≤ Subgroup.normalizer (E : Set G) ⊓
          Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.normalizer (L : Set G)

@[expose] def S7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      E ≤ L ⊔ Sec4.thetaQuotCentralizer L

theorem conj_mem_sup_thetaQuotCentralizer {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {k x : G} (hk : k ∈ Subgroup.normalizer (L : Set G))
    (hx : x ∈ L ⊔ Sec4.thetaQuotCentralizer L) :
    k * x * k⁻¹ ∈ L ⊔ Sec4.thetaQuotCentralizer L := by
  have hle : L ⊔ Sec4.thetaQuotCentralizer L ≤
      (L ⊔ Sec4.thetaQuotCentralizer L).comap (MulAut.conj k).toMonoidHom := by
    refine sup_le (fun l hl => ?_) (fun d hd => ?_)
    · change k * l * k⁻¹ ∈ L ⊔ Sec4.thetaQuotCentralizer L
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hk l).mp hl)
    · change k * d * k⁻¹ ∈ L ⊔ Sec4.thetaQuotCentralizer L
      exact Subgroup.mem_sup_right (Sec6.conj_mem_thetaQuotCentralizer hd hk)
  exact hle hx

theorem m12MovesL_of_parts (h1 : S1) (h2 : S2) (h3 : S3) (h4 : S4) (h5 : S5) (h6 : S6)
    (h7 : S7) (hmix : YCfgMixed) : M12MovesL := by
  intro G _ _ A c L E F a b R Y hY _ hM t EY hd htL
  obtain ⟨hbC, hbL⟩ := hmix G A c L E F a b R Y hY
  obtain ⟨ρ, hρ⟩ := h2 G A c L E F a b R Y hY hbC hbL t EY hd htL
  obtain ⟨hc1, hp1, he1, hN1⟩ := h5 G A c L E F a b R Y hY
  obtain ⟨hc2, hp2, he2, hN2⟩ := h6 G A c L E F a b R Y hY ρ hρ
  have hM' : M12Hyp Y := hM
  have hΩ := h1 G A c L E F a b R Y hY hM'
  have hNB : (Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.normalizer (L : Set G)) ≤ Subgroup.centralizer ({b} : Set G) :=
    inf_le_left.trans inf_le_right
  obtain ⟨g, hgN, hg⟩ := h4 G (Subgroup.centralizer ({b} : Set G)) _ (E ⊔ F)
    (E ⊔ Subgroup.zpowers ρ) hΩ hNB hN1 hN2 hp1 hp2 hc1 hc2 he1 he2
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := hgN.2
  have hIn : (E ⊔ Subgroup.zpowers ρ : Subgroup G) ≤ L ⊔ Sec4.thetaQuotCentralizer L :=
    sup_le (h7 G A c L E F a b R Y hY) (Subgroup.zpowers_le.mpr hρ.mem_inner)
  have hga : g * a * g⁻¹ ∈ L ⊔ Sec4.thetaQuotCentralizer L :=
    hIn (hg a (Subgroup.mem_sup_right hY.haF))
  have ha : a ∈ L ⊔ Sec4.thetaQuotCentralizer L := by
    have h := conj_mem_sup_thetaQuotCentralizer (inv_mem hgL) hga
    rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at h
  exact h3 G A c L E F a b R Y hY hbC hbL ha

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
