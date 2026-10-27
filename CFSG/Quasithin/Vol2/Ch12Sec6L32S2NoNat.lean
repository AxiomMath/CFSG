module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2Defs
public import CFSG.Quasithin.Background.RonanD35SL
public import CFSG.Quasithin.H13.A6S1385b

public section

namespace CFSG.Quasithin.H13.L1232S2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.H13
  CFSG.Quasithin.H13.A6

attribute [local instance] commGroupOfFact

theorem autSub_top_eq_map' {W : Type} [CommGroup W] (X : Subgroup (MulAut W)) :
    autSub X (⊤ : Subgroup W) =
      X.map (MulAut.congr (Subgroup.topEquiv (G := W)).symm).toMonoidHom := by
  ext φ
  rw [mem_autSub]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, by ext u; rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, mem_stabSub_top x⟩, hx, by ext u; rfl⟩

theorem isFFModule_of_autSub_top {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    (h : IsFFModule (autSub X (⊤ : Subgroup W))) : IsFFModule X := by
  rw [autSub_top_eq_map'] at h
  exact (E3.isFFModule_map_congr_iff (Subgroup.topEquiv (G := W)).symm).1 h

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (h : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, h])

theorem leafNoNat_holds : LeafNoNat := by
  intro hNo G _ _ T L V _ F H K c I hV₁I hIU hkerI hHI
  have h := c.f918
  haveI hFe := factElem h hIU
  intro hnat
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hTH : T ≤ H := h.T_le_H
  have hXH : K ⊔ T ≤ H := sup_le hKH hTH
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hW2 : ∀ w : ↥(tildeOf F.V1 (conjClosure I H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by
      simpa using (Fact.out : IsElemAbelian 2 (tildeOf F.V1 (conjClosure I H))).2 w w.2)
  have hW : ∀ w : ↥(tildeOf F.V1 (conjClosure I H)), w * w = 1 := fun w => by
    rw [← sq]; exact hW2 w
  let ρ : ↥(K ⊔ T) →* MulAut ↥(tildeOf F.V1 (conjClosure I H)) :=
    (actH h.H_le_normalizer_V₁ hIH).comp (Subgroup.inclusion hXH)
  have hρQ : ∀ x : ↥(K ⊔ T), (x : G) ∈ pCoreOf 2 H → ρ x = 1 := fun x hx =>
    h.actH_eq_one_of_mem_pCoreOf hIU (x := Subgroup.inclusion hXH x) hx
  have hρK : ∀ x : ↥(K ⊔ T), (x : G) ∈ K → ρ x = 1 →
      ∀ k ∈ K, (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
    intro x hxK hρx k hk
    have h1 : ∀ u ∈ conjClosure I H, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ F.V1 :=
      (A6Tv.actH_eq_one_iff h.H_le_normalizer_V₁ hIHN hIH (Subgroup.inclusion hXH x)).1 hρx
    have hxQ : (x : G) ∈ pCoreOf 2 H := hkerI x hxK h1
    have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
    have hk' : k * (x : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (hQn (hKH hk)) _).mp ((pCoreOf 2 H).inv_mem hxQ)
    have e : (x : G) * k * (x : G)⁻¹ * k⁻¹ = (x : G) * (k * (x : G)⁻¹ * k⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem hxQ hk'
  obtain ⟨K', _, _, hK', π, hπ⟩ := hnat
  have : CharP K' 2 := charP_two_of_card hK'
  have hFF1 : IsFFModule (autSub (autIH F.V1 I H K) (⊤ : Subgroup ↥(tildeOf F.V1 (conjClosure I H)))) :=
    RonanD35.isFFModule_of_natSL hW (le_stabSub_top _)
      (fun g _ z hz => by rw [Subgroup.mem_bot] at hz; rw [hz, map_one]) le_rfl hπ
  have hFF2 := isFFModule_of_autSub_top hFF1
  have hLle : autIH F.V1 I H K ≤ ρ.range := by
    rw [autIH_eq_map h hKH]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨(x : G), Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)⟩, rfl⟩
  exact hNo G T L V F c.hyp c.hZ H K c.isHK c.case1 h _ hW2 ρ hρQ hρK
    (B1Red.isFFModule_mono hLle hFF2)

end CFSG.Quasithin.H13.L1232S2
