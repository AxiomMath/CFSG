module

public import CFSG.Quasithin.Vol2.Ch10SecKRSm
public import CFSG.Quasithin.Vol2.Ch10SecKRSd
public import CFSG.Quasithin.Vol2.Ch10SecQ9G11
public import CFSG.Quasithin.Vol2.Ch10SecQ9G13

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

abbrev CE (t w : G) : Subgroup G :=
  Subgroup.centralizer ({t * w * t⁻¹} : Set G) ⊓ Subgroup.centralizer ({w} : Set G)

omit [Finite G] in
theorem conj_mem_theta {X : Subgroup G} {g : G} (hX : ∀ x ∈ X, g * x * g⁻¹ ∈ X) {x : G}
    (hx : x ∈ theta X) : g * x * g⁻¹ ∈ theta X := by
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    refine mem_theta (hX z hz.1) ?_
    rw [conj_pow, hz.2, mul_one, mul_inv_cancel]
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

variable (c : Conf T L I t w J) (hTw : T ⊓ Subgroup.centralizer ({w} : Set G) = T1 T L)
include c hTw

theorem Conf.conj_mem_theta_CE (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {x : G} (hx : x ∈ theta (CE t w)) :
    t⁻¹ * x * t ∈ theta (CE t w) := by
  have := conj_mem_theta (g := t⁻¹) (fun y hy => by
    simpa using Conf.conj_mem_CE c hTw h37 h38 hy) hx
  simpa using this

theorem Conf.conj_mem_theta_CE' (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {x : G} (hx : x ∈ theta (CE t w)) :
    t * x * t⁻¹ ∈ theta (CE t w) :=
  conj_mem_theta (fun _ hy => Conf.conj_mem_CE' c hTw h37 h38 hy) hx

omit hTw in
theorem Conf.theta_CE_le_J (h38 : Vol2Native.A38ForSQTKCat) (h318 : A318Facts)
    (h36' : A36ForSQTK) (hE : Ch11.SecA.FactA318ExclTwo) (hK7L5 : C10P4F.FactK7L5)
    (hVe : IsElemAbelian 2 (VI T L I J w)) (hq : CFSG.Open.IsQuasisimple ↥(autI hVe J))
    (e5 : ↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    theta (CE t w) ≤ J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine (Subgroup.closure_le J).mpr fun x hx => ?_
  by_cases h1 : x = 1
  · rw [h1]
    exact J.one_mem
  · exact C10P4F.Conf.mem_J_of_orderOf_three' c h38 h318 h36' hE eJ
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e5 (C10P4F.isQuasisimple_of_open' hq))
      (C10P4F.center_SL_eq_bot 5) C10P4F.three_dvd_card_SL5 C10P4F.two_le_pRank_SL5 hK7L5
      hx.1.2 (orderOf_eq_prime hx.2 h1)

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
