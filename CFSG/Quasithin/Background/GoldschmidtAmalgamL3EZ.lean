module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3EKey

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3E

open GoldAmL3

open scoped commutatorElement

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

omit [Finite D] in
theorem comm_mul_left_of_comm {x y ζ : D} (h : x * ⁅y, ζ⁆ = ⁅y, ζ⁆ * x) :
    ⁅x * y, ζ⁆ = ⁅y, ζ⁆ * ⁅x, ζ⁆ := by
  rw [comm_mul_left, conj_eq_of_comm h]

theorem Ctx.centerP_le_K (c : Ctx A B z V) {ζ : D} (hζ : ζ ∈ centerOf (pCoreOf 2 B)) :
    ζ ∈ Ksub A B := by
  have hc : ∀ p ∈ pCoreOf 2 B, p * ζ = ζ * p := fun p hp =>
    Subgroup.mem_centralizer_iff.mp hζ.2 p hp
  have h : ζ ∈ pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) :=
    ⟨hζ.1, Subgroup.mem_centralizer_iff.mpr fun u hu => hc u (c.U_le_P hu)⟩
  rw [c.hyp.pCoreOf_inf_centralizer_eq_coreIn] at h
  exact h

namespace Gen

variable {c : Ctx A B z V} (g : Gen c)

@[expose] def ω : D := g.u₀ * (g.u₁ * g.u₂)

theorem ω_mem_Q : g.ω ∈ pCoreOf 2 A :=
  (pCoreOf 2 A).mul_mem g.u₀_mem_Q ((pCoreOf 2 A).mul_mem g.u₁_mem_Q g.u₂_mem_Q)

theorem comm_u₀_ω : ⁅g.u₀, g.ω⁆ = z := by
  unfold ω
  rw [c.comm_mul_W g.u₀_mem_W g.u₀_mem_Q ((pCoreOf 2 A).mul_mem g.u₁_mem_Q g.u₂_mem_Q),
    c.comm_mul_W g.u₀_mem_W g.u₁_mem_Q g.u₂_mem_Q, g.comm01, g.comm02, g.z₂_mul_z₁]
  simp

theorem ω_mem_P : g.ω ∈ pCoreOf 2 B := by
  have hωT : g.ω ∈ A ⊓ B := c.Q_le_T g.ω_mem_Q
  rw [c.hyp.pCoreOf_eq_centralizerMod]
  refine ⟨hωT.2, ?_, fun u hu => ?_⟩
  · have hc : g.ω * z = z * g.ω := Subgroup.mem_centralizer_iff.mp c.hyp.natural.z_mem.2 g.ω hωT
    exact mem_normalizer_zpowers_of_mul_comm hc
  · obtain ⟨v, hv, h | h⟩ := g.U_form hu
    · rw [h]
      have : g.ω * v * g.ω⁻¹ * v⁻¹ = 1 := by
        rw [(c.V_comm hv g.ω_mem_Q).symm]; group
      rw [this]; exact Subgroup.one_mem _
    · rw [h]
      have h1 : ⁅g.ω, v * g.u₀⁆ = ⁅g.ω, g.u₀⁆ := c.comm_V_mul_right hv g.u₀_mem_Q g.ω_mem_Q
      have h2 : ⁅g.ω, g.u₀⁆ = z := by
        rw [← commutatorElement_inv, g.comm_u₀_ω]; exact c.inv_eq_self c.z_mem_V
      have h3 : g.ω * (v * g.u₀) * g.ω⁻¹ * (v * g.u₀)⁻¹ = ⁅g.ω, v * g.u₀⁆ := rfl
      rw [h3, h1, h2]
      exact Subgroup.mem_zpowers z

include g in
theorem centerP_le_M {ζ : D} (hζ : ζ ∈ centerOf (pCoreOf 2 B)) : ζ ∈ Msub A B V := by
  have hζK := c.centerP_le_K hζ
  have hζQ : ζ ∈ pCoreOf 2 A := c.K_le_Q hζK
  have h0 : ⁅g.u₀, ζ⁆ = 1 :=
    comm_eq_one_iff.mpr (c.hyp.comm_of_mem_coreIn hζK g.u₀ g.u₀_mem)
  have hωζ : ⁅g.ω, ζ⁆ = 1 :=
    comm_eq_one_iff.mpr (Subgroup.mem_centralizer_iff.mp hζ.2 g.ω g.ω_mem_P)
  have h1V : ⁅g.u₁, ζ⁆ ∈ V := c.comm_W_Q g.u₁_mem_W hζQ
  have h2V : ⁅g.u₂, ζ⁆ ∈ V := c.comm_W_Q g.u₂_mem_W hζQ
  have hu₁₂ : g.u₁ * g.u₂ ∈ Wsub A B V := (Wsub A B V).mul_mem g.u₁_mem_W g.u₂_mem_W
  have hprod : ⁅g.ω, ζ⁆ = (⁅g.u₂, ζ⁆ * ⁅g.u₁, ζ⁆) * ⁅g.u₀, ζ⁆ := by
    unfold ω
    rw [comm_mul_left_of_comm (c.V_comm (c.comm_W_Q hu₁₂ hζQ) g.u₀_mem_Q).symm,
      comm_mul_left_of_comm (c.V_comm h2V g.u₁_mem_Q).symm]
  rw [h0, mul_one] at hprod
  rw [hωζ] at hprod
  have h12 : ⁅g.u₁, ζ⁆ = ⁅g.u₂, ζ⁆ := by
    have h := mul_eq_one_iff_eq_inv.mp hprod.symm
    rw [h]; exact (c.inv_eq_self h1V).symm ▸ rfl
  have h1 := g.theta1_eq_one hζQ h0 h12
  have h2 : ⁅g.u₂, ζ⁆ = 1 := by rw [← h12]; exact h1
  exact g.mem_M_of_comm hζQ h0 h1 h2

end Gen

theorem Ctx.W_not_le_P (c : Ctx A B z V) : ¬ Wsub A B V ≤ pCoreOf 2 B := fun h => by
  have h4 := c.hyp.four_le_critDist_iff.mpr h
  have h3 := c.crit_eq
  omega

theorem Ctx.T_eq_P_sup_W (c : Ctx A B z V) : A ⊓ B = pCoreOf 2 B ⊔ Wsub A B V := by
  have hW : Wsub A B V ≤ A ⊓ B := (c.W_le_Q).trans c.Q_le_T
  have hle : pCoreOf 2 B ⊔ Wsub A B V ≤ A ⊓ B := sup_le c.P_le_T hW
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 B) (pCoreOf 2 B ⊔ Wsub A B V) (A ⊓ B)
    le_sup_left hle
  rw [c.hyp.gold.relIndex_pCoreOf_T_right] at hmul
  have hdvd : (pCoreOf 2 B ⊔ Wsub A B V).relIndex (A ⊓ B) ∣ 2 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle
  · exfalso
    rw [h2] at hmul
    have h3 : (pCoreOf 2 B).relIndex (pCoreOf 2 B ⊔ Wsub A B V) = 1 := by omega
    exact c.W_not_le_P (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h3))

theorem Gen.centerP_le_centerT {c : Ctx A B z V} (g : Gen c) {ζ : D}
    (hζ : ζ ∈ centerOf (pCoreOf 2 B)) : ζ ∈ centerOf (A ⊓ B) := by
  have hM := g.centerP_le_M hζ
  refine ⟨c.P_le_T hζ.1, ?_⟩
  have hle : pCoreOf 2 B ⊔ Wsub A B V ≤ Subgroup.centralizer ({ζ} : Set D) := by
    refine sup_le (fun p hp => ?_) (fun w hw => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.mp hζ.2 p hp).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((c.mem_M_iff.mp hM).2 w hw).symm
  refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
  have ht' : t ∈ Subgroup.centralizer ({ζ} : Set D) := hle (by rw [← c.T_eq_P_sup_W]; exact ht)
  exact (Subgroup.mem_centralizer_iff.mp ht' ζ (Set.mem_singleton ζ)).symm

theorem Ctx.centerT_le_centerP (c : Ctx A B z V) {ω : D} (hω : ω ∈ centerOf (A ⊓ B)) :
    ω ∈ centerOf (pCoreOf 2 B) :=
  ⟨c.hyp.gold.centerOf_le_pCoreOf_right hω, Subgroup.mem_centralizer_iff.mpr fun p hp =>
    Subgroup.mem_centralizer_iff.mp hω.2 p (c.P_le_T hp)⟩

omit [Finite D] in
theorem Ctx.centerP_conj (_c : Ctx A B z V) {x ζ : D} (hx : x ∈ B)
    (hζ : ζ ∈ centerOf (pCoreOf 2 B)) : x * ζ * x⁻¹ ∈ centerOf (pCoreOf 2 B) := by
  refine ⟨pCoreOf_conj_mem hx hζ.1, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
  have hp' : x⁻¹ * p * x⁻¹⁻¹ ∈ pCoreOf 2 B := pCoreOf_conj_mem (B.inv_mem hx) hp
  have h := Subgroup.mem_centralizer_iff.mp hζ.2 _ hp'
  calc p * (x * ζ * x⁻¹) = x * ((x⁻¹ * p * x⁻¹⁻¹) * ζ) * x⁻¹ := by group
    _ = x * (ζ * (x⁻¹ * p * x⁻¹⁻¹)) * x⁻¹ := by rw [h]
    _ = (x * ζ * x⁻¹) * p := by group

theorem Gen.centerT_central_B {c : Ctx A B z V} (g : Gen c) {ω : D}
    (hω : ω ∈ centerOf (A ⊓ B)) : ∀ y ∈ B, y * ω * y⁻¹ = ω := by
  set C : Subgroup D := B ⊓ Subgroup.centralizer ((centerOf (pCoreOf 2 B) : Subgroup D) : Set D)
    with hC
  have hTC : A ⊓ B ≤ C := fun t ht => ⟨ht.2, Subgroup.mem_centralizer_iff.mpr fun ζ hζ =>
    (Subgroup.mem_centralizer_iff.mp (g.centerP_le_centerT hζ).2 t ht).symm⟩
  have hN : B ≤ Subgroup.normalizer (C : Set D) := by
    refine le_normalizer_of_conj fun x hx g' hg' => ⟨B.mul_mem (B.mul_mem hx hg'.1) (B.inv_mem hx),
      Subgroup.mem_centralizer_iff.mpr fun ζ hζ => ?_⟩
    have hζ' : x⁻¹ * ζ * x⁻¹⁻¹ ∈ centerOf (pCoreOf 2 B) := c.centerP_conj (B.inv_mem hx) hζ
    have h := Subgroup.mem_centralizer_iff.mp hg'.2 _ hζ'
    calc ζ * (x * g' * x⁻¹) = x * ((x⁻¹ * ζ * x⁻¹⁻¹) * g') * x⁻¹ := by group
      _ = x * (g' * (x⁻¹ * ζ * x⁻¹⁻¹)) * x⁻¹ := by rw [h]
      _ = (x * g' * x⁻¹) * ζ := by group
  have hCB : C = B := c.eq_right_of_normal hTC inf_le_left hN
  intro y hy
  have hyC : y ∈ C := by rw [hCB]; exact hy
  have := Subgroup.mem_centralizer_iff.mp hyC.2 ω (c.centerT_le_centerP hω)
  rw [← this]; group

theorem Gen.centerT_central_A {c : Ctx A B z V} (g : Gen c) {ω : D}
    (hω : ω ∈ centerOf (A ⊓ B)) (hA : ∀ y ∈ A, y * ω * y⁻¹ = ω) : ω = 1 := by
  have hB := g.centerT_central_B hω
  have hnorm : ∀ X : Subgroup D, (∀ y ∈ X, y * ω * y⁻¹ = ω) →
      X ≤ Subgroup.normalizer ((Subgroup.zpowers ω : Subgroup D) : Set D) := by
    intro X hX y hy
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have hy' : y * ω * y⁻¹ = ω := hX y hy
    have hconj : ∀ k : ℤ, y * ω ^ k * y⁻¹ = ω ^ k := by
      intro k
      have := map_zpow (MulAut.conj y) ω k
      simpa [MulAut.conj_apply, hy'] using this
    constructor
    · rintro ⟨k, rfl⟩
      rw [hconj k]; exact ⟨k, rfl⟩
    · intro hn
      obtain ⟨k, hk⟩ := hn
      refine ⟨k, ?_⟩
      have h2 : y * ω ^ k * y⁻¹ = y * n * y⁻¹ := by rw [hconj k]; exact hk
      have := mul_left_cancel (mul_right_cancel h2)
      exact this
  have hle : Subgroup.zpowers ω ≤ A ⊓ B := Subgroup.zpowers_le.mpr hω.1
  have hbot := c.hyp.gold.eq_bot_of_normalizes (hnorm A hA) (hnorm B hB) hle
  have : ω ∈ (⊥ : Subgroup D) := by rw [← hbot]; exact Subgroup.mem_zpowers ω
  simpa using this

end GoldAmL3E

end F6

end CFSG.Quasithin
