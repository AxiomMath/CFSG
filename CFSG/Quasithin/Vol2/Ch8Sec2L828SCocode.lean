module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828SBt

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section L828SCocode

variable {G : Type} [Group G] [Finite G]

theorem s828_autOn_pCore_le {L V : Subgroup G} :
    autOn (pCoreOf 2 L) V ≤ pCoreOf 2 (autOn L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (CFSG.Quasithin.AutOn.autOn_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
    (CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
    (CFSG.Quasithin.AutOn.isPGroup_autOn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L))

theorem s828_lu_centralizes_B {T L I H : Subgroup G} {h : G} {k : ℕ}
    [IsMulCommutative ↥(fsuV T I)] (hMB3 : MB3_828) (hcard : Mathieu.StmtH13Card)
    (hV : IsElemAbelian 2 (fsuV T I)) (hL0 : fsuL0 T L = L) (hC5 : Concl825 T L I h k)
    (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAL : ch82A (fsuV T I) h ≤ Subgroup.normalizer (L : Set G))
    (hAe : IsElemAbelian 2 (ch82A (fsuV T I) h))
    (hB : ch82B (fsuV T I) h = ⁅fsuV T I, ch82A (fsuV T I) h⁆ ⊔
      ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h)
    (hrow : Case8_2 T L I) :
    ∀ w ∈ pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h)), ∀ b ∈ ch82B (fsuV T I) h,
      ⁅w, b⁆ ∈ ch82U (fsuV T I) h := by
  have hAp : IsPGroup 2 ↥(ch82A (fsuV T I) h) := B6.isPGroup_of_isElemAbelian hAe
  have hLUN : ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans hLN)
  have hX : autOn (ch82A (fsuV T I) h) (fsuV T I) ≤
      Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I))) :=
    autOn_le_normalizer_82 hAL
  have hXe : IsElemAbelian2 (autOn (ch82A (fsuV T I) h) (fsuV T I)) :=
    isElemAbelian2_of_828 (isElemAbelian_autOn_82 hAe)
  have hrows := rows_hlu82_828 hcard hL0 hV hC5 hAN hAp
  have hrowsDisj : (BinaryNineTensor (autOn L (fsuV T I)) ⊤ ⊥ 1 ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 4 ∧
        rk ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 4) ∨
      (MathieuCode22 (autOn L (fsuV T I)) ⊤ ⊥ ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 5 ∧
        rkIdx (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 6) ∨
      (MathieuCode24 (autOn L (fsuV T I)) ⊤ ⊥ ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 6 ∧
        rkIdx (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 7) ∨
      (MathieuCocode24 (autOn L (fsuV T I)) ⊤ ⊥ ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 6 ∧
        rk ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 3) := by
    rcases hrow with hr | hr | hr | hr
    · exact Or.inl (hrows.1 hr)
    · exact Or.inr (Or.inl (hrows.2.1 hr))
    · exact Or.inr (Or.inr (Or.inl (hrows.2.2.1 hr)))
    · exact Or.inr (Or.inr (Or.inr (hrows.2.2.2 hr)))
  have hm3 := hMB3 (fsuV T I) (autOn L (fsuV T I)) (autOn (ch82A (fsuV T I) h) (fsuV T I)) hX hXe
    hrowsDisj
  intro w hw b hb
  have hwV : w ∈ Subgroup.normalizer (fsuV T I : Set G) :=
    hLUN (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hw)
  have hx : CFSG.Quasithin.conjAct (fsuV T I) ⟨w, hwV⟩ ∈
      pCoreOf 2 (perfectCore (autOn L (fsuV T I) ⊓
        stabSub (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))))) := by
    rw [s828_perfect_autOn_LU hLN hAN]
    exact s828_autOn_pCore_le
      (CFSG.Quasithin.AutOn.conjAct_mem_autOn ⟨w, hwV⟩ hw)
  have hb' : b ∈ fsuV T I ⊓ pCoreOf 2 (ch82I (fsuV T I) h) := hb
  have hbV : b ∈ fsuV T I := (Subgroup.mem_inf.mp hb').1
  have hbB' : b ∈ (s828BPrime (autOn L (fsuV T I))
      (autOn (ch82A (fsuV T I) h) (fsuV T I))).map (fsuV T I).subtype := by
    rw [← s828_B'_eq_map hLN hAN hAL, ← hB]
    exact hb
  obtain ⟨bm, hbm, hbeq⟩ := Subgroup.mem_map.mp hbB'
  have hbm_eq : bm = ⟨b, hbV⟩ := Subtype.ext hbeq
  have hy := Subgroup.mem_map_of_mem (fsuV T I).subtype (hm3 _ hx bm hbm)
  rw [s828_fixV_map (L := L) hAN] at hy
  have e : ((CFSG.Quasithin.conjAct (fsuV T I) ⟨w, hwV⟩ bm * bm⁻¹ : ↥(fsuV T I)) : G) =
      ⁅w, b⁆ := by
    rw [hbm_eq, Subgroup.coe_mul, Subgroup.coe_inv, CFSG.Quasithin.AutOn.coe_conjAct_apply,
      commutatorElement_def]
  rw [← e]
  exact hy

theorem s828_lu_centralizes_A {T L I H : Subgroup G} {h : G} {k : ℕ}
    [IsMulCommutative ↥(fsuV T I)] (hMB3 : MB3_828) (hcard : Mathieu.StmtH13Card)
    (hV : IsElemAbelian 2 (fsuV T I)) (hL0 : fsuL0 T L = L) (hC5 : Concl825 T L I h k)
    (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAL : ch82A (fsuV T I) h ≤ Subgroup.normalizer (L : Set G))
    (hAe : IsElemAbelian 2 (ch82A (fsuV T I) h))
    (hB : ch82B (fsuV T I) h = ⁅fsuV T I, ch82A (fsuV T I) h⁆ ⊔
      ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h)
    (hrow : Case8_2 T L I) (hhI : h ∈ ch82I (fsuV T I) h)
    (hIN : ch82I (fsuV T I) h ≤ Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G))
    (hcen : ∀ u ∈ ch82U (fsuV T I) h, ∀ i ∈ ch82I (fsuV T I) h, i * u * i⁻¹ = u) :
    ∀ w ∈ pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h)), ∀ a ∈ ch82A (fsuV T I) h,
      ⁅w, a⁆ ∈ ch82U (fsuV T I) h := by
  have hB' := s828_lu_centralizes_B (H := H) hMB3 hcard hV hL0 hC5 hLN hAN hAL hAe hB hrow
  intro w hw a ha
  have ha' : a ∈ B6.conjSub h (fsuV T I) ⊓ pCoreOf 2 (ch82I (fsuV T I) h) := ha
  have hhN : h⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h)) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (hIN (Subgroup.inv_mem _ hhI))
  have hw' : h⁻¹ * w * h ∈ pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h)) := by
    have := (Subgroup.mem_normalizer_iff.mp hhN w).mp hw
    simpa using this
  have hbh : h⁻¹ * a * h ∈ ch82B (fsuV T I) h := by
    refine ⟨B6.mem_conjSub.mp (Subgroup.mem_inf.mp ha').1, ?_⟩
    have hPN : h⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.inv_mem _ hhI)
    have := (Subgroup.mem_normalizer_iff.mp hPN a).mp (Subgroup.mem_inf.mp ha').2
    simpa using this
  have hz := hB' (h⁻¹ * w * h) hw' (h⁻¹ * a * h) hbh
  have e : ⁅w, a⁆ = h * ⁅h⁻¹ * w * h, h⁻¹ * a * h⁆ * h⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e, hcen _ hz h hhI]
  exact hz

theorem s828_lu_centralizes_P {T L I H : Subgroup G} {h : G} {k : ℕ}
    [IsMulCommutative ↥(fsuV T I)] (hMB3 : MB3_828) (hcard : Mathieu.StmtH13Card)
    (hV : IsElemAbelian 2 (fsuV T I)) (hL0 : fsuL0 T L = L) (hC5 : Concl825 T L I h k)
    (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAL : ch82A (fsuV T I) h ≤ Subgroup.normalizer (L : Set G))
    (hAe : IsElemAbelian 2 (ch82A (fsuV T I) h))
    (hB : ch82B (fsuV T I) h = ⁅fsuV T I, ch82A (fsuV T I) h⁆ ⊔
      ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h)
    (hrow : Case8_2 T L I) (hhI : h ∈ ch82I (fsuV T I) h)
    (hIN : ch82I (fsuV T I) h ≤ Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G))
    (hcen : ∀ u ∈ ch82U (fsuV T I) h, ∀ i ∈ ch82I (fsuV T I) h, i * u * i⁻¹ = u)
    (hPeq : pCoreOf 2 (ch82I (fsuV T I) h) = ch82A (fsuV T I) h ⊔ ch82B (fsuV T I) h) :
    ∀ w ∈ pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h)), ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h),
      ⁅w, p⁆ ∈ ch82U (fsuV T I) h := by
  intro w hw
  have hA := s828_lu_centralizes_A (H := H) hMB3 hcard hV hL0 hC5 hLN hAN hAL hAe hB hrow hhI hIN
    hcen w hw
  have hB' := s828_lu_centralizes_B (H := H) hMB3 hcard hV hL0 hC5 hLN hAN hAL hAe hB hrow w hw
  let S : Subgroup G :=
    { carrier := {p | p ∈ ch82I (fsuV T I) h ∧ ⁅w, p⁆ ∈ ch82U (fsuV T I) h}
      one_mem' := ⟨(ch82I (fsuV T I) h).one_mem, by
        simpa [commutatorElement_def] using (ch82U (fsuV T I) h).one_mem⟩
      mul_mem' := by
        rintro p q ⟨hp, hpz⟩ ⟨hq, hqz⟩
        refine ⟨(ch82I (fsuV T I) h).mul_mem hp hq, ?_⟩
        have e : ⁅w, p * q⁆ = ⁅w, p⁆ * (p * ⁅w, q⁆ * p⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e, hcen _ hqz p hp]
        exact (ch82U (fsuV T I) h).mul_mem hpz hqz
      inv_mem' := by
        rintro p ⟨hp, hpz⟩
        refine ⟨(ch82I (fsuV T I) h).inv_mem hp, ?_⟩
        have e : ⁅w, p⁻¹⁆ = p⁻¹ * ⁅w, p⁆⁻¹ * p⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e, hcen _ ((ch82U (fsuV T I) h).inv_mem hpz) p⁻¹ ((ch82I (fsuV T I) h).inv_mem hp)]
        exact (ch82U (fsuV T I) h).inv_mem hpz }
  have hAS : ch82A (fsuV T I) h ≤ S := fun a ha => by
    have ha' : a ∈ B6.conjSub h (fsuV T I) ⊓ pCoreOf 2 (ch82I (fsuV T I) h) := ha
    exact ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 _ (Subgroup.mem_inf.mp ha').2, hA a ha⟩
  have hBS : ch82B (fsuV T I) h ≤ S := fun b hb => by
    have hb' : b ∈ fsuV T I ⊓ pCoreOf 2 (ch82I (fsuV T I) h) := hb
    exact ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 _ (Subgroup.mem_inf.mp hb').2, hB' b hb⟩
  intro p hp
  have hpS : p ∈ S := sup_le hAS hBS (hPeq ▸ hp)
  exact hpS.2

theorem s828_comm_P_U {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hC : Concl822 T L I H h k) (hUZ : ch82U (fsuV T I) h = ch82ZI (fsuV T I) h)
    (hP : E2.Pair (ch82I (fsuV T I) h) (T ⊓ ch82I (fsuV T I) h)
      (fsuM T L ⊓ ch82I (fsuV T I) h) (fsuV T I) h)
    (hPeq : pCoreOf 2 (ch82I (fsuV T I) h) = ch82A (fsuV T I) h ⊔ ch82B (fsuV T I) h) :
    ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h), ∀ q ∈ pCoreOf 2 (ch82I (fsuV T I) h),
      ⁅p, q⁆ ∈ ch82U (fsuV T I) h := by
  have hZc : ch82ZI (fsuV T I) h ≤ Subgroup.centralizer (ch82I (fsuV T I) h : Set G) :=
    hC.2.2.2.2.1
  intro p hp q hq
  obtain ⟨⟨z, hz, hpq⟩, -⟩ := s828_comm_mod_Z hP hPeq hp hq
  have hzI : ∀ i ∈ ch82I (fsuV T I) h, i * z * i⁻¹ = z := fun i hi => by
    have := (Subgroup.mem_centralizer_iff.mp (hZc hz)) i hi
    rw [this]
    group
  have hpI : p ∈ ch82I (fsuV T I) h := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hp
  have hqI : q ∈ ch82I (fsuV T I) h := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
  have key : ⁅p, q⁆ = z := by
    rw [commutatorElement_def]
    calc p * q * p⁻¹ * q⁻¹ = q * p * z * p⁻¹ * q⁻¹ := by rw [hpq]
      _ = q * (p * z * p⁻¹) * q⁻¹ := by group
      _ = q * z * q⁻¹ := by rw [hzI p hpI]
      _ = z := hzI q hqI
  rw [key, hUZ]
  exact hz

theorem s828_cocode_clauses12 {T L I H : Subgroup G} {h : G} {k : ℕ}
    [IsMulCommutative ↥(fsuV T I)]
    (hE214 : ASInputs.AS_E_2_14) (hMB0 : MB0_828) (hMB3 : MB3_828) (hSyl : Sylow822VB_828)
    (hcard : Mathieu.StmtH13Card) (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I)
    (h821 : Hyp8_2_1 T L I) (hrow : Case8_2 T L I) (hH : IsHStar T (fsuM T L) H) (hh : h ∈ H)
    (hC : Concl822 T L I H h k) (hC5 : Concl825 T L I h k) (hL0 : fsuL0 T L = L)
    (hV : IsElemAbelian 2 (fsuV T I)) (hVT : fsuV T I ≤ T)
    (hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAL : ch82A (fsuV T I) h ≤ Subgroup.normalizer (L : Set G))
    (hIN : ch82I (fsuV T I) h ≤ Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G))
    (hVB : ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ≤ ch82B (fsuV T I) h) :
    (∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h), ∀ q ∈ pCoreOf 2 (ch82I (fsuV T I) h),
        ⁅p, q⁆ ∈ ch82U (fsuV T I) h) ∧
      (∀ w ∈ pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h)),
        ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h), ⁅w, p⁆ ∈ ch82U (fsuV T I) h) := by
  have hk2 : k ≤ 2 := by
    rcases hrow with hr | hr | hr | hr
    · have : (k : ℕ∞) = 1 := hC5.1.symm.trans (hC5.2.2.2.1 hr).1
      have : k = 1 := by exact_mod_cast this
      omega
    · have : (k : ℕ∞) = 1 := hC5.1.symm.trans (hC5.2.2.2.2.1 hr).1
      have : k = 1 := by exact_mod_cast this
      omega
    · have : (k : ℕ∞) = 1 := hC5.1.symm.trans (hC5.2.2.2.2.2.1 hr).1
      have : k = 1 := by exact_mod_cast this
      omega
    · have : (k : ℕ∞) = 2 := hC5.1.symm.trans (hC5.2.2.2.2.2.2.1 hr).1
      have : k = 2 := by exact_mod_cast this
      omega
  have hPeq := s828_pCore_eq_sup (hE214 := hE214) hC hk2
  have hP := s828_pair hV hVT hTV hC
  have hUZ : ch82U (fsuV T I) h = ch82ZI (fsuV T I) h := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hUZ', -, -⟩ := hC5
    exact hUZ'
  have hcen : ∀ u ∈ ch82U (fsuV T I) h, ∀ i ∈ ch82I (fsuV T I) h, i * u * i⁻¹ = u := by
    intro u hu i hi
    have hu' : u ∈ ch82ZI (fsuV T I) h := hUZ ▸ hu
    have := (Subgroup.mem_centralizer_iff.mp (hC.2.2.2.2.1 hu')) i hi
    rw [this]
    group
  have hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hA7, -, -, -, -, -, -, -, -⟩ := hC
    rw [hA7]
    exact inf_le_right
  have hAe : IsElemAbelian 2 (ch82A (fsuV T I) h) :=
    isElemAbelian_of_le_conjSub_82 hV inf_le_left
  have hB := s828_prop21 hyp h731 h821 hrow hH hh hC hC5 hMB0 hSyl hcard hV hL0 hVT hTV hLN hAL
    hVB
  refine ⟨s828_comm_P_U hC hUZ hP hPeq, ?_⟩
  exact s828_lu_centralizes_P (H := H) hMB3 hcard hV hL0 hC5 hLN hAN hAL hAe hB hrow hC.2.1 hIN
    hcen hPeq

end L828SCocode

end CFSG.Quasithin.H13
