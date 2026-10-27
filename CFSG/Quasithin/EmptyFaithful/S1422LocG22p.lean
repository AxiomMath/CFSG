module

public import CFSG.Quasithin.EmptyFaithful.S1422LocBasic
public import CFSG.Quasithin.EmptyFaithful.S1422LocAut
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}

theorem g22p_local (S : Setting1422 T M Y H) (hC : CaseG22P H (Y ⊔ T)) :
    H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  obtain ⟨-, hq6, -, hQ, -⟩ := hC
  obtain ⟨e₀⟩ := nonempty_mulEquiv_Z4StarQ8_of_isCentralProductZ4Q8 hQ
  let e : ↥(pCoreOf 2 H) ≃* Z4StarQ8Model := e₀.trans z4StarQ8EquivModel
  obtain ⟨z, hz, hz1, hz2, -⟩ := S.exists_z
  have hzcen : z ∈ centerOf (pCoreOf 2 H) := by
    obtain ⟨P, hP⟩ := S.exists_sylow
    exact omegaOneCenter_le_centerOf_pCoreOf H P (hP ▸ S.T_le_H) S.charTwo_H (hP ▸ hz)
  have hzQ : z ∈ pCoreOf 2 H := hzcen.1
  have hez : e ⟨z, hzQ⟩ = ⟨2, 0, 0⟩ := by
    have hc : ∀ q : Z4StarQ8Model, e ⟨z, hzQ⟩ * q = q * e ⟨z, hzQ⟩ := by
      intro q
      obtain ⟨q', rfl⟩ := e.surjective q
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hzcen.2 (q' : G) q'.2).symm
    have hsq : e ⟨z, hzQ⟩ * e ⟨z, hzQ⟩ = 1 := by
      rw [← map_mul]
      have : (⟨z, hzQ⟩ : ↥(pCoreOf 2 H)) * ⟨z, hzQ⟩ = 1 := Subtype.ext (by simpa [sq] using hz2)
      rw [this, map_one]
    rcases z4q8_central_involution _ hc hsq with h | h
    · exact absurd (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))) hz1
    · exact h
  have hcomm : ∀ x ∈ pCoreOf 2 H, ∀ y ∈ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro x hx y hy
    let x' : ↥(pCoreOf 2 H) := ⟨x, hx⟩
    let y' : ↥(pCoreOf 2 H) := ⟨y, hy⟩
    have h1 := z4q8_comm_mem (e x') (e y')
    have h2 : e (x' * y' * x'⁻¹ * y'⁻¹) = e x' * e y' * (e x')⁻¹ * (e y')⁻¹ := by
      simp only [map_mul, map_inv]
    rcases h1 with h | h
    · rw [← h2, ← map_one e] at h
      have h3 : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val (e.injective h)
      rw [h3]
      exact Subgroup.one_mem _
    · rw [← h2, ← hez] at h
      have h3 : x * y * x⁻¹ * y⁻¹ = z := congrArg Subtype.val (e.injective h)
      rw [h3]
      exact hz
  have hMcN := S.Mc_le_normalizer_pCoreOf_H hcomm
  have hQeq := S.pCoreOf_H_eq_Mc hcomm
  let φ : ↥(Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) →* MulAut ↥(pCoreOf 2 H) :=
    (conjAct (pCoreOf 2 H)).comp (Subgroup.inclusion hMcN)
  have hker : ∀ x : ↥(Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)), x ∈ φ.ker →
      (x : G) ∈ pCoreOf 2 H := by
    intro x hx
    have hx' : (x : G) ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
      A4.conjAct_eq_one_iff.mp (MonoidHom.mem_ker.mp hx)
    rw [hQeq]
    exact S.charTwo_Mc ⟨x.2, hQeq ▸ hx'⟩
  have hkercard : Nat.card φ.ker ≤ 4 := by
    let κ : φ.ker → {c : Z4StarQ8Model // ∀ q : Z4StarQ8Model, c * q = q * c} := fun x =>
      ⟨e ⟨(x : G), hker x x.2⟩, by
        intro q
        obtain ⟨q', rfl⟩ := e.surjective q
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        have : (x : G) ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
          A4.conjAct_eq_one_iff.mp (MonoidHom.mem_ker.mp x.2)
        exact (Subgroup.mem_centralizer_iff.mp this (q' : G) q'.2).symm⟩
    have hκ : Function.Injective κ := by
      intro x y hxy
      have h1 := e.injective (congrArg Subtype.val hxy)
      exact Subtype.ext (Subtype.ext (Subtype.mk.inj h1))
    calc Nat.card φ.ker ≤ Nat.card {c : Z4StarQ8Model // ∀ q : Z4StarQ8Model, c * q = q * c} :=
          Nat.card_le_card_of_injective _ hκ
      _ = 4 := by rw [Nat.card_eq_fintype_card, z4q8_card_central]
  have hrange : Nat.card φ.range ≤ 48 := by
    have h1 : Nat.card φ.range ≤ Nat.card (MulAut ↥(pCoreOf 2 H)) := Subgroup.card_le_card_group _
    have h2 : Nat.card (MulAut ↥(pCoreOf 2 H)) = Nat.card (MulAut Z4StarQ8Model) :=
      Nat.card_congr (MulAut.congr e).toEquiv
    exact h1.trans (h2 ▸ card_mulAut_z4StarQ8Model_le)
  have hMc : Nat.card (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤ 192 := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h1
    rw [← h1]
    calc Nat.card φ.ker * Nat.card φ.range ≤ 4 * 48 := Nat.mul_le_mul hkercard hrange
      _ = 192 := by norm_num
  have hH96 : Nat.card H = 96 := by
    rw [card_eq_card_oTwoQuot_mul, hQ.1]
    have h6 : Nat.card (oTwoQuot ↥H) = 6 := by rw [hq6.card le_rfl]; norm_num
    rw [h6]
  obtain ⟨P, hP⟩ := S.exists_sylow
  have hTK : ¬ 2 ∣ (T.subgroupOf (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))).index := by
    have h := not_dvd_index_subgroupOf_of_sylow P (hP.le.trans S.T_le_Mc)
    rwa [hP] at h
  have hodd := odd_relIndex_of_le S.T_le_H S.H_le_centralizer hTK
  have hcard := card_eq_card_mul_relIndex S.H_le_centralizer
  rw [hH96] at hcard
  rw [hcard] at hMc
  have h1 : H.relIndex (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) = 1 := by
    obtain ⟨j, hj⟩ := hodd
    omega
  exact le_antisymm S.H_le_centralizer (Subgroup.relIndex_eq_one.mp h1)

end Setting1422

end CFSG.Quasithin
