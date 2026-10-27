module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3EGeo
public import CFSG.Quasithin.Recognition.F112WChief
public import CFSG.Quasithin.EmptyFaithful.SzF53B3EStep

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace F53B3.NoE

variable {G : Type} [Group G]

theorem oTwoUpper_le_oTwoRes (H : Subgroup G) : oTwoUpper H ≤ oTwoRes H :=
  Subgroup.closure_mono fun x hx => ⟨hx.1, orderOf x, hx.2, pow_orderOf_eq_one x⟩

theorem commute_of_oTwoRes {H : Subgroup G} {x : G}
    (hx2 : ∀ g ∈ H, ⁅g, x⁆ * ⁅g, x⁆ = 1)
    (hcen : ∀ l ∈ oTwoRes H, l * ⁅l, x⁆ = ⁅l, x⁆ * l) :
    ∀ l ∈ oTwoRes H, l * x = x * l := by
  have hle : oTwoRes H ≤ Subgroup.centralizer ({x} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro l ⟨hlH, m, hm, hlm⟩
    have hl : l ∈ oTwoRes H := Subgroup.subset_closure ⟨hlH, m, hm, hlm⟩
    have h1 := comm_eq_one_of_odd_pow hm hlm (hx2 l hlH) (hcen l hl)
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp (hle hl) x rfl).symm

variable [Finite G]

theorem no_E_core {H S E V C Z : Subgroup G}
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) (hE : F53EData H S E)
    (horth3 : ∀ F L X : Subgroup G, IsOrthSec F L X → ∀ d ∈ F, d ∉ cSecIn F L X →
      d ^ 3 ∈ cSecIn F L X → ∃ x ∈ X, x ∉ L ∧ d * x * d⁻¹ * x⁻¹ ∈ L)
    (hEQ : E ≤ pCoreOf 2 H) (hF : VertexFacts H V C Z)
    {d : G} (hd : d ∈ H) (hdQ : d ∉ pCoreOf 2 H) (hd3 : d ^ 3 ∈ pCoreOf 2 H)
    (hfix : ∀ y ∈ V, d * y * d⁻¹ * y⁻¹ ∈ C → y ∈ C)
    (hK : ⁅pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G), oTwoRes H⁆ ≤ V)
    (hS2 : E ⊓ V ≤ C → ∀ e ∈ E, ∀ v ∈ V, ⁅e, v⁆ ∈ Z) : False := by
  have hEH : E ≤ H := hEQ.trans (pCoreOf_le 2 H)
  have normE : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E := fun h hh e he =>
    (Subgroup.mem_normalizer_iff.mp (hE.normal hh) e).mp he
  have hEnorm : IsNormalIn H E E := ⟨le_rfl, normE⟩
  have Esq : ∀ x ∈ E, x * x = 1 := fun x hx => by
    rw [← sq]; exact isElemAbelian_pow_eq_one hE.abelian hx
  have commE : ∀ g ∈ H, ∀ x ∈ E, ⁅g, x⁆ ∈ E := fun g hg x hx =>
    E.mul_mem (normE g hg x hx) (E.inv_mem hx)
  have hx2 : ∀ x ∈ E, ∀ g ∈ H, ⁅g, x⁆ * ⁅g, x⁆ = 1 := fun x hx g hg => Esq _ (commE g hg x hx)
  have commE' : ∀ x ∈ E, ∀ l ∈ H, ⁅x, l⁆ ∈ E := fun x hx l hl => by
    rw [← commutatorElement_inv l x]; exact E.inv_mem (commE l hl x hx)
  have hD : E ⊓ V ≤ C := by
    have hBn : IsNormalIn H E (E ⊓ V) :=
      ⟨inf_le_left, fun g hg x hx => ⟨normE g hg x hx.1, hF.normV g hg x hx.2⟩⟩
    have hAn : IsNormalIn H E (E ⊓ V ⊓ C) :=
      ⟨inf_le_left.trans inf_le_left, fun g hg x hx =>
        ⟨⟨normE g hg x hx.1.1, hF.normV g hg x hx.1.2⟩, hF.normC g hg x hx.2⟩⟩
    have hBA := eq_of_key hq hE horth3 hd hdQ hd3 hAn hBn inf_le_left
      fun x hx hdx => ⟨hx, hfix x hx.2 hdx.2⟩
    exact fun x hx => (show x ∈ E ⊓ V ⊓ C by rw [← hBA]; exact hx).2
  have hP : Pairing H E V Z :=
    ⟨⟨hEH, normE, hF.normV, hF.comm_V, hF.central, hF.sq_Z⟩, hS2 hD⟩
  have hcube := hF.hcube hd3
  have hE₀ : IsNormalIn H E (E ⊓ Subgroup.centralizer (V : Set G)) := by
    refine ⟨inf_le_left, fun g hg x hx => ⟨normE g hg x hx.1, ?_⟩⟩
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 (g⁻¹ * v * g)
      (by simpa using hF.normV g⁻¹ (H.inv_mem hg) v hv)
    calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * v := by group
  have hE₁ : IsNormalIn H E (E ⊓ Subgroup.centralizer (C : Set G)) := by
    refine ⟨inf_le_left, fun g hg x hx => ⟨normE g hg x hx.1, ?_⟩⟩
    refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 (g⁻¹ * c * g)
      (by simpa using hF.normC g⁻¹ (H.inv_mem hg) c hc)
    calc c * (g * x * g⁻¹) = g * ((g⁻¹ * c * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * c * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * c := by group
  have hle₀₁ : E ⊓ Subgroup.centralizer (V : Set G) ≤ E ⊓ Subgroup.centralizer (C : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le hF.C_le_V)
  have hE10 : E ⊓ Subgroup.centralizer (C : Set G) = E ⊓ Subgroup.centralizer (V : Set G) := by
    refine eq_of_key hq hE horth3 hd hdQ hd3 hE₀ hE₁ hle₀₁ ?_
    intro x hx hdx
    refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hC : ∀ c ∈ C, ⁅x, c⁆ = 1 := fun c hc =>
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hx.2 c hc).symm
    have hk := hP.key hF.C_le_V hd hx.1 hw hC
      (exists_mod hd hF.normV hF.normC hF.comm_V hfix hcube hw)
    have hdwV : d * w * d⁻¹ * w⁻¹ ∈ V :=
      V.mul_mem (hF.normV d hd w hw) (V.inv_mem hw)
    have h1 : ⁅⁅d, x⁆, ⁅d, w⁆⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hdx.2 _ hdwV).symm
    rw [h1] at hk
    exact (commutatorElement_eq_one_iff_mul_comm.mp hk.symm).symm
  have hEL : ∀ e ∈ E, ∀ l ∈ oTwoRes H, ⁅e, l⁆ ∈ E ⊓ Subgroup.centralizer (V : Set G) := by
    intro e he l hl
    have hlH : l ∈ H := oTwoRes_le H hl
    rw [← hE10]
    refine ⟨commE' e he l hlH, Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩
    exact (commutatorElement_eq_one_iff_mul_comm.mp
      (hP.comm_comm_eq_one hF.C_le_V he hlH hc (hF.C_cent c hc l hl))).symm
  have hS4 : ∀ x ∈ E ⊓ Subgroup.centralizer (V : Set G), ∀ l ∈ oTwoRes H, l * x = x * l := by
    intro x hx
    refine commute_of_oTwoRes (hx2 x hx.1) fun l hl => ?_
    have hlH : l ∈ H := oTwoRes_le H hl
    have hxK : x ∈ pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G) := ⟨hEQ hx.1, hx.2⟩
    have h1 : ⁅x, l⁆ ∈ V := hK (Subgroup.commutator_mem_commutator hxK hl)
    have h2 : ⁅l, x⁆ ∈ V := by rw [← commutatorElement_inv x l]; exact V.inv_mem h1
    have h3 : ⁅l, x⁆ ∈ C := hD ⟨commE l hlH x hx.1, h2⟩
    have h4 := hF.C_cent _ h3 l hl
    calc l * ⁅l, x⁆ = (l * ⁅l, x⁆ * l⁻¹) * l := by group
      _ = ⁅l, x⁆ * l := by rw [h4]
  have hS5 : ∀ x ∈ E, ∀ l ∈ oTwoRes H, l * x = x * l := by
    intro x hx
    refine commute_of_oTwoRes (hx2 x hx) fun l hl => ?_
    have h1 : ⁅l, x⁆ ∈ E ⊓ Subgroup.centralizer (V : Set G) := by
      rw [← commutatorElement_inv x l]
      exact (E ⊓ Subgroup.centralizer (V : Set G)).inv_mem (hEL x hx l hl)
    exact hS4 _ h1 l hl
  have hcomm : ⁅E, oTwoUpper H⁆ = ⊥ := by
    refine le_bot_iff.mp ((Subgroup.commutator_le).mpr fun e he l hl => ?_)
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (hS5 e he l (oTwoUpper_le_oTwoRes H hl)).symm
  have h0 : IsChiefSeriesFrom H E E 0 :=
    (F112W.isChiefSeriesFrom_zero_iff hEH hEQ hEnorm).mpr hcomm
  have := F112W.isChiefSeriesFrom_unique hEH hE.chief h0
  omega

end F53B3.NoE

namespace F53B3

theorem no_E_of_fixed {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
    (hB : B3Facts H M S) (hBl : B3Block H M S)
    (hN : ∀ β : Geo H M, vtype β = false → ⁅Kq β, oTwoRes (stab β)⁆ ≤ Vn β)
    (hnat3 : ∀ F L X : Subgroup G, IsNatSec F L X → ∀ d ∈ F, d ∉ cSecIn F L X →
      d ^ 3 ∈ cSecIn F L X → ∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ L → x ∈ L)
    (horth3 : ∀ F L X : Subgroup G, IsOrthSec F L X → ∀ d ∈ F, d ∉ cSecIn F L X →
      d ^ 3 ∈ cSecIn F L X → ∃ x ∈ X, x ∉ L ∧ d * x * d⁻¹ * x⁻¹ ∈ L)
    {E : Subgroup G} (hE : F53EData H S E) : False := by
  have hA : F53Amalgam H M S := hB.amalgam
  obtain ⟨β, hvt, hst⟩ : ∃ β : Geo H M, vtype β = false ∧ stab β = H :=
    ⟨γ₀ (H ⊔ M) H M, vtype_γ₀, stab_γ₀ hA.amalgam.le₁⟩
  have hq := hA.quot_left
  have hSyl : IsSylowTwoOf S H := hA.amalgam.sylow₁
  have hEQ : E ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hE.le.trans hSyl.1) hE.normal (hSyl.2.1.to_le hE.le)
  have normE : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E := fun h hh e he =>
    (Subgroup.mem_normalizer_iff.mp (hE.normal hh) e).mp he
  obtain ⟨d, hd, hdQ, hd3⟩ := NoE.exists_three_element hq
  have hF := NoE.VertexFacts.of_geometry hB hBl hvt hst
  have hNat : IsNatSec H (Cv β) (Vn β) := by
    have := hB.nat β hvt
    rwa [hst] at this
  have hfix := NoE.hfix_of_nat3 hF hq hNat hnat3 hd hdQ hd3
  have hK : ⁅pCoreOf 2 H ⊓ Subgroup.centralizer (Vn β : Set G), oTwoRes H⁆ ≤ Vn β := by
    have := hN β hvt
    unfold Kq Qv at this
    rw [hst] at this
    exact this
  exact NoE.no_E_core hq hE horth3 hEQ hF hd hdQ hd3 hfix hK
    fun hD => NoE.pair_mem_Z hB hBl hvt hst hEQ normE hD

end F53B3

end CFSG.Quasithin
