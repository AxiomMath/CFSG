module

public import CFSG.Quasithin.H13.L32NItems144CTL2
public import CFSG.Quasithin.H13.L32NItems144CTL1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444CTL

open L1444

variable {G : Type} [Group G] [Finite G]

section Setup

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem exists_swap_invol {x : G} (hxW : x ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hxQ : x ∉ pCoreOf 2 (l32nH T V)) (h1 : Q₁.map (MulAut.conj x).toMonoidHom = Q₂)
    (h2 : Q₂.map (MulAut.conj x).toMonoidHom = Q₁) :
    ∃ σ ∈ CFSG.conjugate (l32nW T V V₂) g, σ ∉ pCoreOf 2 (l32nH T V) ∧ σ * σ = 1 ∧
      (∀ q ∈ Q₁, σ * q * σ⁻¹ ∈ Q₂) ∧ (∀ q ∈ Q₂, σ * q * σ⁻¹ ∈ Q₁) := by
  have hx12 : ∀ q ∈ Q₁, x * q * x⁻¹ ∈ Q₂ := fun q hq => by
    rw [← h1]
    exact ⟨q, hq, by simp⟩
  have hx21 : ∀ q ∈ Q₂, x * q * x⁻¹ ∈ Q₁ := fun q hq => by
    rw [← h2]
    exact ⟨q, hq, by simp⟩
  obtain ⟨v, hv, hxv⟩ := S.exists_invol hxW hxQ
  have hvU : v ∈ Q₁ ⊔ Q₂ := S.sup ▸ V_le_U hv
  have hv₁ : v ∈ Subgroup.normalizer (Q₁ : Set G) :=
    sup_le Subgroup.le_normalizer ((Subgroup.le_centralizer_iff.mp S.cfg.comm).trans
      (Subgroup.centralizer_le_normalizer _)) hvU
  have hv₂ : v ∈ Subgroup.normalizer (Q₂ : Set G) :=
    sup_le (S.cfg.comm.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer hvU
  refine ⟨x * v, (CFSG.conjugate (l32nW T V V₂) g).mul_mem hxW (S.V_le_Wg hv), fun h => hxQ ?_,
    hxv, fun q hq => ?_, fun q hq => ?_⟩
  · have := (pCoreOf 2 (l32nH T V)).mul_mem h ((pCoreOf 2 (l32nH T V)).inv_mem (S.V_le_Q hv))
    simpa using this
  · have h3 : v * q * v⁻¹ ∈ Q₁ := (Subgroup.mem_normalizer_iff.mp hv₁ q).mp hq
    have h4 := hx12 _ h3
    rwa [show x * (v * q * v⁻¹) * x⁻¹ = x * v * q * (x * v)⁻¹ by group] at h4
  · have h3 : v * q * v⁻¹ ∈ Q₂ := (Subgroup.mem_normalizer_iff.mp hv₂ q).mp hq
    have h4 := hx21 _ h3
    rwa [show x * (v * q * v⁻¹) * x⁻¹ = x * v * q * (x * v)⁻¹ by group] at h4

theorem exists_mem_V_mul_mem {e : G} (he : e ∈ Subgroup.centralizer (fsuU T V : Set G)) :
    ∃ m ∈ V, e * m⁻¹ ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => S.comm_V hx hy
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using S.elem.2 x x.2)⟩
  have hodd : ¬ 2 ∣ (fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g).relIndex L := by
    rw [S.relIndex_TL]
    decide
  obtain ⟨m, hm, hml⟩ := SBc8.exists_mul_centralizer_of_cocycle S.L_le_normV hVc hV2 S.TL_le_L
    hodd (fun v hv => by rw [← Subgroup.mem_centralizer_iff.mp he v (V_le_U hv)]; group)
    (fun l hl => S.comm_mem_V he hl)
    (fun p hp => by rw [S.comm_TL he hp]; group)
  refine ⟨m, hm, T.mul_mem (S.cent_le_T he) (T.inv_mem (S.QT (S.V_le_Q hm))),
    Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  calc l * (e * m⁻¹) = l * (e * m⁻¹) * l⁻¹ * l := by group
    _ = e * m⁻¹ * l := by rw [hml l hl]

theorem exists_mul_pow_mem_normalizer {σ c : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hσ2 : σ * σ = 1) (h21 : ∀ q ∈ Q₂, σ * q * σ⁻¹ ∈ Q₁)
    (hcK : c ∈ oTwoUpper (l32nH T V))
    (hcfpf : ∀ (hcN : c ∈ Subgroup.normalizer (fsuU T V : Set G)) (w : D.V),
      D.ρ ⟨c, hcN⟩ w = w → w = 0)
    (hσc : σ * c * σ⁻¹ * c⁻¹ ∈ pCoreOf 2 (l32nH T V)) {k : G}
    (hkK : k ∈ oTwoUpper (l32nH T V)) :
    ∃ j : ℕ, k * c ^ j ∈
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  have hσH : σ ∈ l32nH T V := S.Wg_le_H hσW
  have hσinv : σ⁻¹ = σ := (eq_inv_of_mul_eq_one_left hσ2).symm
  have hKn : σ ∈ Subgroup.normalizer (oTwoUpper (l32nH T V) : Set G) :=
    le_normalizer_oTwoUpper _ hσH
  have hsK : σ * k * σ⁻¹ ∈ oTwoUpper (l32nH T V) :=
    (Subgroup.mem_normalizer_iff.mp hKn k).mp hkK
  have hsK' : σ * k⁻¹ * σ⁻¹ ∈ oTwoUpper (l32nH T V) :=
    (Subgroup.mem_normalizer_iff.mp hKn _).mp ((oTwoUpper _).inv_mem hkK)
  have hk'K : k * (σ * k * σ⁻¹) ∈ oTwoUpper (l32nH T V) := (oTwoUpper _).mul_mem hkK hsK
  have hk'σ : σ * (k * (σ * k * σ⁻¹)) * σ⁻¹ * (k * (σ * k * σ⁻¹))⁻¹ ∈
      pCoreOf 2 (l32nH T V) := by
    have e : σ * (k * (σ * k * σ⁻¹)) * σ⁻¹ * (k * (σ * k * σ⁻¹))⁻¹ =
        (σ * k * σ⁻¹) * k * (σ * k * σ⁻¹)⁻¹ * k⁻¹ := by
      calc σ * (k * (σ * k * σ⁻¹)) * σ⁻¹ * (k * (σ * k * σ⁻¹))⁻¹ =
          σ * k * σ * k * σ⁻¹ * σ⁻¹ * σ * k⁻¹ * σ⁻¹ * k⁻¹ := by group
        _ = σ * k * σ⁻¹ * k * σ * σ⁻¹ * σ * k⁻¹ * σ⁻¹ * k⁻¹ := by rw [hσinv]
        _ = (σ * k * σ⁻¹) * k * (σ * k * σ⁻¹)⁻¹ * k⁻¹ := by group
    rw [e]
    exact S.comm_mem_Q_of_mem_K hsK hkK
  obtain ⟨j, hj⟩ := exists_pow_inv_mul_mem_Q S hσH hσ2 h21 hcK hcfpf hσc hk'K hk'σ
  have haK : k * σ * k⁻¹ * σ⁻¹ ∈ oTwoUpper (l32nH T V) := by
    rw [show k * σ * k⁻¹ * σ⁻¹ = k * (σ * k⁻¹ * σ⁻¹) by group]
    exact (oTwoUpper _).mul_mem hkK hsK'
  have haσ : σ * (k * σ * k⁻¹ * σ⁻¹) * σ⁻¹ * (k * σ * k⁻¹ * σ⁻¹) ∈ pCoreOf 2 (l32nH T V) := by
    have hσσ : σ⁻¹ * σ⁻¹ = 1 := by rw [← mul_inv_rev, hσ2, inv_one]
    have e : σ * (k * σ * k⁻¹ * σ⁻¹) * σ⁻¹ * (k * σ * k⁻¹ * σ⁻¹) = 1 := by
      calc σ * (k * σ * k⁻¹ * σ⁻¹) * σ⁻¹ * (k * σ * k⁻¹ * σ⁻¹) =
          σ * k * σ * k⁻¹ * (σ⁻¹ * σ⁻¹) * k * σ * k⁻¹ * σ⁻¹ := by group
        _ = σ * k * σ * k⁻¹ * k * σ * k⁻¹ * σ⁻¹ := by rw [hσσ]; group
        _ = σ * k * (σ * σ) * k⁻¹ * σ⁻¹ := by group
        _ = 1 := by rw [hσ2]; group
    rw [e]
    exact one_mem _
  have haN := mem_normalizer_of_inv S hσW haK haσ
  have hc₁ := S.comm_mem_Q_of_mem_K hsK hkK
  have hQn : l32nH T V ≤ Subgroup.normalizer (pCoreOf 2 (l32nH T V) : Set G) :=
    le_normalizer_pCoreOf (r := 2) (l32nH T V)
  have hkH : k ∈ l32nH T V := oTwoUpper_le _ hkK
  have hcH : c ∈ l32nH T V := oTwoUpper_le _ hcK
  have hq₃ : k * ((σ * k * σ⁻¹) * k * (σ * k * σ⁻¹)⁻¹ * k⁻¹)⁻¹ * k⁻¹ ∈
      pCoreOf 2 (l32nH T V) :=
    (Subgroup.mem_normalizer_iff.mp (hQn hkH) _).mp ((pCoreOf 2 _).inv_mem hc₁)
  have hk3 := S.cube_mem_Q_of_mem_K hkK
  have hlast : (c ^ j)⁻¹ * ((k * ((σ * k * σ⁻¹) * k * (σ * k * σ⁻¹)⁻¹ * k⁻¹)⁻¹ * k⁻¹)⁻¹ *
      k ^ 3) * c ^ j ∈ pCoreOf 2 (l32nH T V) := by
    have h1 := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer _).inv_mem (hQn ((l32nH T V).pow_mem hcH j))) _).mp
      ((pCoreOf 2 _).mul_mem ((pCoreOf 2 _).inv_mem hq₃) hk3)
    rwa [inv_inv] at h1
  refine ⟨j, ?_⟩
  have heq : k * c ^ j = (k * σ * k⁻¹ * σ⁻¹)⁻¹ * ((c ^ j)⁻¹ * (k * (σ * k * σ⁻¹)))⁻¹ *
      ((c ^ j)⁻¹ * ((k * ((σ * k * σ⁻¹) * k * (σ * k * σ⁻¹)⁻¹ * k⁻¹)⁻¹ * k⁻¹)⁻¹ *
        k ^ 3) * c ^ j) := by
    group
  rw [heq]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ haN)
    (Q_le_normalizer S (Subgroup.inv_mem _ hj))) (Q_le_normalizer S hlast)

end Setup

end L1444CTL

end CFSG.Quasithin.H13
