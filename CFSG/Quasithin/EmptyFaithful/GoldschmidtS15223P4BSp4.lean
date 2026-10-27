module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BAut
public import CFSG.Quasithin.EmptyFaithful.S153F20
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBRank2
public import CFSG.Timmesfeld.Transvection.PresSp
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

namespace S15223P4

namespace B

section Center

variable {G : Type} [Group G]

theorem center_quot_eq_bot_of_isSp4Quot {X : Subgroup G} (h : IsSp4Quot X) :
    Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥ := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hnat : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hcard]; norm_num
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hnat
  rw [eq_bot_iff]
  intro x hx
  have hc : e x ∈ Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSp 2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
  rw [CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num)] at hc
  have h1 : e x = 1 := Subgroup.mem_bot.1 hc
  exact Subgroup.mem_bot.2 (e.injective (by rw [h1, map_one]))

theorem inf_pCoreOf_sup_le {X R : Subgroup G} [Finite G] : X ⊓ pCoreOf 2 (X ⊔ R) ≤ pCoreOf 2 X := by
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((pCoreOf_isPGroup 2 (X ⊔ R)).to_le inf_le_right)
  intro g hg
  have h1 : g ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer hg
  have h2 : g ∈ Subgroup.normalizer (pCoreOf 2 (X ⊔ R) : Set G) :=
    le_normalizer_pCoreOf 2 (X ⊔ R) (Subgroup.mem_sup_left hg)
  rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, h1 h, h2 h]

end Center

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem inf_centralizer_V_le_pCoreOf (c : P4Ctx T Mc M H B₀ I X)
    (hZ : Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥) :
    X ⊓ Subgroup.centralizer (P4V M I X : Set G) ≤ pCoreOf 2 X := fun _ hx =>
  inf_pCoreOf_sup_le ⟨hx.1, centralizer_le_pCoreOf_of_center_eq_bot c.R_norm hZ
    c.c27.1.2.1 ⟨Subgroup.mem_sup_left hx.1, hx.2⟩⟩

theorem not_Sp4 (kB : SolvOvergroupsInBorel) (c : P4Ctx T Mc M H B₀ I X)
    (f : P4Fact T Mc M H B₀ I X) (hSp : IsSp4Quot X)
    (hpar : IsParabolic2 (autOn X (P4V M I X)) (autOn (MX M I X) (P4V M I X))) : False := by
  have hXN := X_le_normalizer_V c
  have hYA : oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X) ≤
      Subgroup.normalizer ((sOf152 T Mc M B₀ ⊓ X : Subgroup G) : Set G) :=
    kB G X (sOf152 T Mc M B₀ ⊓ X) _ (Or.inr hSp) f.sylow le_sup_right (Y_le_X f) f.solv_Y
  have hCV := inf_centralizer_V_le_pCoreOf c (center_quot_eq_bot_of_isSp4Quot hSp)
  have hΛ : IsSylowTwoOf (autOn (sOf152 T Mc M B₀ ⊓ X) (P4V M I X)) (autOn X (P4V M I X)) :=
    Setup.isSylowTwoOf_autOn f.sylow hXN
  have hAM : autOn (sOf152 T Mc M B₀ ⊓ X) (P4V M I X) ≤ autOn (MX M I X) (P4V M I X) :=
    autOn_le_autOn _ (A_le_MX c)
  have hnorm := GoldMLB.normalizer_le_of_isParabolic2 hpar hΛ hAM
  refine not_K_le_MX c fun k hk => ?_
  have hkX : k ∈ X := f.K_le hk
  have hkN : k ∈ Subgroup.normalizer (P4V M I X : Set G) := hXN hkX
  have hkA := hYA (Subgroup.mem_sup_left hk)
  have hκX : conjAct (P4V M I X) ⟨k, hkN⟩ ∈ autOn X (P4V M I X) :=
    mem_autOn_iff'.2 ⟨⟨k, hkN⟩, hkX, rfl⟩
  obtain ⟨m, hmM, hm⟩ := mem_autOn_iff'.1
    (hnorm ⟨hκX, conjAct_mem_normalizer_autOn ⟨k, hkN⟩ hkA⟩)
  have h1 : conjAct (P4V M I X) (m⁻¹ * ⟨k, hkN⟩) = 1 := by
    rw [map_mul, map_inv, hm, inv_mul_cancel]
  have h2 := (conjAct_eq_one_iff' _ _).1 h1
  have h3 : (m : G)⁻¹ * k ∈ pCoreOf 2 X :=
    hCV ⟨X.mul_mem (X.inv_mem (hmM.2)) hkX, by simpa using h2⟩
  have h4 : (m : G) * ((m : G)⁻¹ * k) ∈ MX M I X :=
    (MX M I X).mul_mem hmM (pCoreOf_le_MX c f h3)
  simpa using h4

end B

end S15223P4

end CFSG.Quasithin
