module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3O4Vertex
public import CFSG.Quasithin.EmptyFaithful.SzF53A1
public import CFSG.Quasithin.Recognition.F112WChief

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace F53B3.NoEO

variable {G : Type} [Group G]

theorem oTwoUpper_le_oTwoRes (H : Subgroup G) : oTwoUpper H ≤ oTwoRes H :=
  Subgroup.closure_mono fun x hx => ⟨hx.1, orderOf x, hx.2, pow_orderOf_eq_one x⟩

variable [Finite G]

theorem pow_mul_card_le_of_between {H U W N : Subgroup G} {n : ℕ}
    (h : F112W.IsChiefSeriesBetween H U W N n)
    (hstep : ∀ L' N' : Subgroup G, IsChiefStep H U L' N' → ¬ IsCentralStep H L' N' →
      Nat.card N' = 16 * Nat.card L') : 16 ^ n * Nat.card W ≤ Nat.card N := by
  induction h with
  | refl => simp
  | central hs _ _ ih => exact ih.trans (Subgroup.card_le_of_le hs.2.2.1.le)
  | @noncentral N L n hs hnc _ ih =>
    rw [hstep _ _ hs hnc]
    calc 16 ^ (n + 1) * Nat.card W = 16 * (16 ^ n * Nat.card W) := by ring
      _ ≤ 16 * Nat.card L := Nat.mul_le_mul_left 16 ih

theorem no_E_core_orth {H S E V Z : Subgroup G}
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) (hE : F53EData H S E)
    (hEQ : E ≤ pCoreOf 2 H) (hF : OrthVertex H V Z)
    (hK : ⁅pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G), oTwoRes H⁆ ≤ V) : False := by
  have hEH : E ≤ H := hEQ.trans (pCoreOf_le 2 H)
  have normE : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E := fun h hh e he =>
    (Subgroup.mem_normalizer_iff.mp (hE.normal hh) e).mp he
  have hEnorm : IsNormalIn H E E := ⟨le_rfl, normE⟩
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm hE.abelian hx hy
  set K : Subgroup G := pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G) with hKdef
  have hVK : V ≤ K := fun v hv =>
    ⟨hF.V_le_Q hv, Subgroup.mem_centralizer_iff.mpr fun w hw => hF.comm_V w hw v hv⟩
  have hKnorm : ∀ g ∈ H, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hg) k).mp hk.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hk.2 (g⁻¹ * v * g)
      (by simpa using hF.normV g⁻¹ (H.inv_mem hg) v hv)
    calc v * (g * k * g⁻¹) = g * ((g⁻¹ * v * g) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = (g * k * g⁻¹) * v := by group
  have hK16 : K.relIndex (pCoreOf 2 H) ≤ 16 := hF.relIndex_le_sixteen
  have hcommK : ∀ N : Subgroup G, N ≤ K → ⁅N, oTwoUpper H⁆ ≤ V := fun N hN =>
    (Subgroup.commutator_mono hN (oTwoUpper_le_oTwoRes H)).trans hK
  have hcommE : ∀ N : Subgroup G, N ≤ E → ⁅N, oTwoUpper H⁆ ≤ E := fun N hN =>
    (Subgroup.commutator_mono hN le_rfl).trans
      (F112W.commutator_le_self_of_le_normalizer ((oTwoUpper_le H).trans hE.normal))
  have hseries : ∀ L N : Subgroup G, IsChiefStep H E L N → ¬ IsCentralStep H L N →
      Nat.card N = 16 * Nat.card L := fun L N hs hnc => hE.card_eq_sixteen_mul hq hs hnc
  have hW : IsNormalIn H E (E ⊓ V) :=
    ⟨inf_le_left, fun g hg x hx => ⟨normE g hg x hx.1, hF.normV g hg x hx.2⟩⟩
  have hη : F112W.eta H E E = 2 := (F112W.isChiefSeriesFrom_iff_eta hEH hEnorm).mp hE.chief
  by_cases hEK : E ≤ K
  ·
    have hc : ⁅E, oTwoUpper H⁆ ≤ E ⊓ V := le_inf (hcommE E le_rfl) (hcommK E hEK)
    have h1 : F112W.eta H E E = F112W.eta H E (E ⊓ V) :=
      F112W.eta_eq_of_commutator_le hEH hEQ hW hEnorm inf_le_left hc
    have h3 : IsChiefSeriesFrom H E (E ⊓ V) 2 :=
      (F112W.isChiefSeriesFrom_iff_eta hEH hW).mpr (h1.symm.trans hη)
    have h4 := SzF53A1.pow_le_card_of_series h3 hseries
    have h5 : Nat.card ↥(E ⊓ V) ≤ Nat.card V := Subgroup.card_le_of_le inf_le_right
    have h6 := Subgroup.relIndex_mul_card (H := Z) (K := V)
    rw [hF.orth.relIndex_eq, inf_eq_left.mpr hF.Z_le_V, hF.card_Z] at h6
    rw [show (16 : ℕ) ^ 2 = 256 by norm_num] at h4
    omega
  ·
    have hCVE : V ⊓ Subgroup.centralizer (E : Set G) = Z := by
      have hZle : Z ≤ V ⊓ Subgroup.centralizer (E : Set G) := fun z hz =>
        ⟨hF.Z_le_V hz, Subgroup.mem_centralizer_iff.mpr fun e he => by
          have h1 := hF.central z hz e (hEH he)
          calc e * z = (e * z * e⁻¹) * e := by group
            _ = z * e := by rw [h1]⟩
      have hnormC : IsNormalIn H V (V ⊓ Subgroup.centralizer (E : Set G)) := by
        refine ⟨inf_le_left, fun g hg x hx => ⟨hF.normV g hg x hx.1, ?_⟩⟩
        refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
        have h1 := Subgroup.mem_centralizer_iff.mp hx.2 (g⁻¹ * e * g)
          (by simpa using normE g⁻¹ (H.inv_mem hg) e he)
        calc e * (g * x * g⁻¹) = g * ((g⁻¹ * e * g) * x) * g⁻¹ := by group
          _ = g * (x * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
          _ = (g * x * g⁻¹) * e := by group
      rcases hF.orth.irred _ hZle inf_le_left (D14.le_normalizer_of_isNormalIn hnormC) with h | h
      · exact h
      · exfalso
        apply hEK
        intro e he
        refine ⟨hEQ he, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
        have hv' : v ∈ V ⊓ Subgroup.centralizer (E : Set G) := by rw [h]; exact hv
        exact (Subgroup.mem_centralizer_iff.mp hv'.2 e he).symm
    have hWZ : E ⊓ V ≤ Z := fun x hx => by
      rw [← hCVE]
      exact ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun e he => hEab e he x hx.1⟩
    have hN : IsNormalIn H E (E ⊓ K) :=
      ⟨inf_le_left, fun g hg x hx => ⟨normE g hg x hx.1, hKnorm g hg x hx.2⟩⟩
    have hWN : E ⊓ V ≤ E ⊓ K := inf_le_inf_left E hVK
    have hc : ⁅E ⊓ K, oTwoUpper H⁆ ≤ E ⊓ V :=
      le_inf (hcommE _ inf_le_left) (hcommK _ inf_le_right)
    have h1 : F112W.eta H E (E ⊓ K) = F112W.eta H E (E ⊓ V) :=
      F112W.eta_eq_of_commutator_le hEH hEQ hW hN hWN hc
    have h0 : F112W.eta H E (E ⊓ V) = 0 := by
      rw [F112W.eta_eq_zero_iff hEH hEQ hW]
      refine le_bot_iff.mp ((Subgroup.commutator_le).mpr fun w hw l hl => ?_)
      rw [Subgroup.mem_bot]
      have h2 := hF.central w (hWZ hw) l ((oTwoUpper_le H) hl)
      refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
      calc w * l = (l * w * l⁻¹) * l := by rw [h2]
        _ = l * w := by group
    obtain ⟨a, ha⟩ := F112W.exists_isChiefSeriesBetween hN E hEnorm inf_le_left
    have hadd := F112W.eta_eq_add hEH hN ha
    obtain rfl : a = 2 := by omega
    have hpow := pow_mul_card_le_of_between ha hseries
    have hcard : K.relIndex E * Nat.card ↥(K ⊓ E) = Nat.card E :=
      Subgroup.relIndex_mul_card K E
    have hne : K.relIndex (pCoreOf 2 H) ≠ 0 := by
      have : K.IsFiniteRelIndex (pCoreOf 2 H) := Subgroup.isFiniteRelIndex_of_finiteIndex
      exact Subgroup.relIndex_ne_zero
    have hidx : K.relIndex E ≤ 16 := (Subgroup.relIndex_le_of_le_right hEQ hne).trans hK16
    rw [inf_comm] at hcard
    have hpos : 0 < Nat.card ↥(E ⊓ K) := Nat.card_pos
    have hmul := Nat.mul_le_mul_right (Nat.card ↥(E ⊓ K)) hidx
    rw [show (16 : ℕ) ^ 2 = 256 by norm_num] at hpow
    omega

end F53B3.NoEO

namespace F53B3

theorem no_E_orth {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
    (hB : B3FactsO H M S) (hBl : B3Block H M S) (hC1 : OrthC1 H M S)
    (hN : ∀ β : Geo H M, vtype β = false → ⁅Kq β, oTwoRes (stab β)⁆ ≤ Vn β)
    {E : Subgroup G} (hE : F53EData H S E) : False := by
  have hA : F53Amalgam H M S := hB.amalgam
  obtain ⟨β, hvt, hst⟩ : ∃ β : Geo H M, vtype β = false ∧ stab β = H :=
    ⟨γ₀ (H ⊔ M) H M, vtype_γ₀, stab_γ₀ hA.amalgam.le₁⟩
  have hSyl : IsSylowTwoOf S H := hA.amalgam.sylow₁
  have hEQ : E ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hE.le.trans hSyl.1) hE.normal (hSyl.2.1.to_le hE.le)
  have hF := NoEO.OrthVertex.of_geometry hB hBl hC1 hvt hst
  have hK : ⁅pCoreOf 2 H ⊓ Subgroup.centralizer (Vn β : Set G), oTwoRes H⁆ ≤ Vn β := by
    have := hN β hvt
    unfold Kq Qv at this
    rw [hst] at this
    exact this
  exact NoEO.no_E_core_orth hA.quot_left hE hEQ hF hK

end F53B3

end CFSG.Quasithin
