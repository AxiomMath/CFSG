module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8314
public import CFSG.Quasithin.Vol2.Ch3T326H2
public import CFSG.Quasithin.Vol2.Ch7Lem761End

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Stmt8_3_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
        fsuV T I ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))

namespace Ch8313

theorem normalizer_zpowers_eq {x : G} (hx : orderOf x = 2) :
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx
    exact absurd hx (by norm_num)
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have h1 := (Subgroup.mem_normalizer_iff.mp hg x).mp (Subgroup.mem_zpowers x)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hk' : x ^ (k % 2) = g * x * g⁻¹ := by
      have h2 := zpow_mod_orderOf x k
      rw [hx] at h2
      push_cast at h2
      rw [h2, hk]
    have hcases : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hcases with h0 | h0
    · rw [h0, zpow_zero] at hk'
      exfalso
      apply hx1
      have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [e, ← hk']
      group
    · rw [h0, zpow_one] at hk'
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [← hk']
  · intro hg
    rw [Subgroup.mem_normalizer_iff]
    have hc : ∀ n : ℤ, g * x ^ n * g⁻¹ = x ^ n := fun n => by
      have h1 : Commute g x := hg
      rw [(h1.zpow_right n).eq, mul_inv_cancel_right]
    intro y
    constructor
    · intro hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [hc]
      exact Subgroup.zpow_mem_zpowers x n
    · intro hy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      have e : y = x ^ n := by
        have h2 : g * y * g⁻¹ = g * x ^ n * g⁻¹ := by rw [← hn, hc]
        exact mul_left_cancel (mul_right_cancel h2)
      rw [e]
      exact Subgroup.zpow_mem_zpowers x n

theorem card_centralizer_conj (z h : G) :
    Nat.card (Subgroup.centralizer ({h * z * h⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  have e : Subgroup.centralizer ({h * z * h⁻¹} : Set G) =
      (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj h).toMonoidHom := by
    ext c
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
    constructor
    · intro hc
      refine ⟨h⁻¹ * c * h, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have e1 : h⁻¹ * c * h * z = h⁻¹ * (c * (h * z * h⁻¹)) * h := by group
        rw [e1, hc]
        group
      · simp [MulAut.conj_apply, mul_assoc]
    · rintro ⟨d, hd, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hd
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc h * d * h⁻¹ * (h * z * h⁻¹) = h * (d * z) * h⁻¹ := by group
        _ = h * (z * d) * h⁻¹ := by rw [hd]
        _ = h * z * h⁻¹ * (h * d * h⁻¹) := by group
  rw [e, Subgroup.card_map_of_injective (MulAut.conj h).injective]

theorem fsuV_eq_fsuVM [Finite G] {T L I : Subgroup G} [IsMulCommutative ↥(fsuV T I)]
    (h326 : Stmt3_2_6C) (hyp : Hyp7_0_2 G T L I) (hrow : Row711L3Wreath T L I) :
    fsuV T I = fsuVM T L I := by
  rcases stmt3_2_6Lt_of_C h326 G T L I hyp.fsu hrow.1 with ⟨-, -, h, -⟩ | h
  · exact h
  · exact absurd ⟨hrow.1, h⟩ hyp.notThree

end Ch8313

theorem stmt8_3_13_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h326 : Stmt3_2_6C) (h3104 : Stmt3_2_10_four) (h3106 : Stmt3_2_10_six)
    (h8312 : Stmt8_3_12) : Stmt8_3_13 := by
  intro G _ _ T L I hyp h731 hc hrow z hz2 hzV g x h hxg hxV hxz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
  have hMV : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [hVVM]
    exact le_normalizer_conjClosure _ _
  have hVp : IsVplus T L I (fsuV T I) := by
    by_cases hcase : L ≠ conjClosure L T ∧ Case326VM T L I
    · exact Or.inl ⟨hcase.1, hcase.2, hVVM⟩
    · exact Or.inr ⟨hcase, rfl⟩
  have hJ := thompsonJ_le_centralizer_fsuV h37 h38 h39 hyp hV hN
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hTsyl : ∀ K : Subgroup G, T ≤ K → IsSylowIn 2 T K := fun K hTK =>
    ⟨hTK, hyp.fsu.sylow.1, fun h2 => hyp.fsu.sylow.2
      (h2.trans (Subgroup.relIndex_dvd_index_of_le hTK))⟩
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun k hk => by
      rw [Set.mem_singleton_iff.1 hk]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hx2 : orderOf x = 2 := by
    have hsc : SemiconjBy h z (h * z * h⁻¹) := by
      change h * z = h * z * h⁻¹ * h
      group
    rw [hxz, ← hsc.orderOf_eq, hz2]
  have hx1 : x ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  have hNx := Ch8313.normalizer_zpowers_eq hx2
  have hodd := h3104 G T L I (fsuV T I) hyp.fsu hVp hJ (Subgroup.zpowers x)
    (Subgroup.zpowers_le.mpr hxV)
  rw [hNx] at hodd
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 2
    (bot_le : (⊥ : Subgroup G) ≤ fsuM T L ⊓ Subgroup.centralizer ({x} : Set G)) IsPGroup.of_bot
  have hPx : IsSylowIn 2 P (Subgroup.centralizer ({x} : Set G)) := by
    refine ⟨hP.le.trans inf_le_right, hP.isPGroup, fun h2 => ?_⟩
    have h3 : P.relIndex (fsuM T L ⊓ Subgroup.centralizer ({x} : Set G)) *
        (fsuM T L ⊓ Subgroup.centralizer ({x} : Set G)).relIndex
          (Subgroup.centralizer ({x} : Set G)) =
        P.relIndex (Subgroup.centralizer ({x} : Set G)) :=
      Subgroup.relIndex_mul_relIndex _ _ _ hP.le inf_le_right
    rw [← h3] at h2
    rcases (Nat.prime_two.dvd_mul).mp h2 with h3 | h3
    · exact hP.not_dvd_relIndex h3
    · exact hodd h3
  have hPcard : Nat.card P = Nat.card T := by
    rw [hPx.card_eq, (hTsyl _ hTz).card_eq, hxz, Ch8313.card_centralizer_conj]
  obtain ⟨m, hmM, hmP⟩ := B3.exists_conj_le_sylow_sub hTM hyp.fsu.sylow.1
    (hTsyl _ hTM).not_dvd_relIndex (hP.le.trans inf_le_left) hP.isPGroup
  have hmPT : B3.cj m P = T := by
    refine Subgroup.eq_of_le_of_card_ge hmP ?_
    rw [← hPcard]
    exact le_of_eq (Subgroup.card_map_of_injective (MulAut.conj m).injective).symm
  have hmx : m * x * m⁻¹ = z := by
    have hmxC : m * x * m⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rw [← hmPT] at ht
      have h1 : m⁻¹ * t * m ∈ P := B3.mem_cj.1 ht
      have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hPx.le h1)
      calc t * (m * x * m⁻¹) = m * ((m⁻¹ * t * m) * x) * m⁻¹ := by group
        _ = m * (x * (m⁻¹ * t * m)) * m⁻¹ := by rw [h2]
        _ = m * x * m⁻¹ * t := by group
    have hmxT : m * x * m⁻¹ ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hMV hmM) x).mp hxV, hmxC⟩
    rw [hzV] at hmxT
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmxT
    have hk' : z ^ (k % 2) = m * x * m⁻¹ := by
      have h2 := zpow_mod_orderOf z k
      rw [hz2] at h2
      push_cast at h2
      rw [h2, hk]
    have hcases : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hcases with h0 | h0
    · rw [h0, zpow_zero] at hk'
      exfalso
      apply hx1
      have e : x = m⁻¹ * (m * x * m⁻¹) * m := by group
      rw [e, ← hk']
      group
    · rw [h0, zpow_one] at hk'
      exact hk'.symm
  have hVQ := h8312 G T L I hyp h731 hc hrow z hz2 hzV
  set Qz := pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) with hQz
  have hQzC : Qz ≤ Subgroup.centralizer ({z} : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hQzN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Qz : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hxe : x = m⁻¹ * z * m⁻¹⁻¹ := by
    rw [← hmx]
    group
  have hVO : fsuV T I ≤ pCoreOf 2 (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) :
      Set G)) := by
    rw [hNx]
    have hle : CFSG.Quasithin.conjSub m⁻¹ Qz ≤ pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).map _)
      · intro y hy
        have hy' := CFSG.Quasithin.mem_conjSub.mp hy
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hQzC hy')
        rw [Subgroup.mem_centralizer_singleton_iff, hxe]
        calc y * (m⁻¹ * z * m⁻¹⁻¹) = m⁻¹ * (m⁻¹⁻¹ * y * m⁻¹ * z) * m⁻¹⁻¹ := by group
          _ = m⁻¹ * (z * (m⁻¹⁻¹ * y * m⁻¹)) * m⁻¹⁻¹ := by rw [h1]
          _ = m⁻¹ * z * m⁻¹⁻¹ * y := by group
      · intro c hcx
        have hc' : m⁻¹⁻¹ * c * m⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have h1 := Subgroup.mem_centralizer_singleton_iff.mp hcx
          rw [hxe] at h1
          calc m⁻¹⁻¹ * c * m⁻¹ * z = m⁻¹⁻¹ * (c * (m⁻¹ * z * m⁻¹⁻¹)) * m⁻¹ := by group
            _ = m⁻¹⁻¹ * ((m⁻¹ * z * m⁻¹⁻¹) * c) * m⁻¹ := by rw [h1]
            _ = z * (m⁻¹⁻¹ * c * m⁻¹) := by group
        have hn := Subgroup.mem_normalizer_iff.mp (hQzN hc')
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [CFSG.Quasithin.mem_conjSub, CFSG.Quasithin.mem_conjSub, hn]
        have e : m⁻¹⁻¹ * c * m⁻¹ * (m⁻¹⁻¹ * y * m⁻¹) * (m⁻¹⁻¹ * c * m⁻¹)⁻¹ =
            m⁻¹⁻¹ * (c * y * c⁻¹) * m⁻¹ := by group
        rw [e]
    refine le_trans ?_ hle
    intro v hv
    rw [CFSG.Quasithin.mem_conjSub, inv_inv]
    exact hVQ ((Subgroup.mem_normalizer_iff.mp (hMV hmM) v).mp hv)
  have hcomm := h3106 G T L I (fsuV T I) hyp.fsu hVp hJ (Subgroup.zpowers x)
    (Subgroup.zpowers_le.mpr hxV) hVO (not_isFFStarOffender_autOn h37 h38 h39 hyp hV hN) g
    (Subgroup.zpowers_le.mpr hxg)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  exact Subgroup.le_centralizer_iff.mp hcomm

end CFSG.Quasithin.H13
