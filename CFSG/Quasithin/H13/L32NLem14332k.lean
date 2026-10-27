module

public import CFSG.Quasithin.H13.L32NLem14332j
public import CFSG.Quasithin.H13.L32NLem14332h

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement MatrixGroups

namespace L14332

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g a : G}
  {D : HatModelU (fsuU T V)} {K : Subgroup G}

omit [Finite G] in
theorem le_normalizer_commutator (hKn : l32nH T V ≤ Subgroup.normalizer (K : Set G)) :
    l32nH T V ≤ Subgroup.normalizer ((⁅fsuU T V, K⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (l32nH_le_normalizer_fsuU T V hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKn hh)]

theorem fsuU_le_commutator (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (C : Ctx14332 G T L V V₂ g a D) (hii : Case14323ii T V g D)
    (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V) (hK : K ∈ cComp (l32nH T V)) :
    fsuU T V ≤ ⁅fsuU T V, K⁆ := by
  have := finite_linearEquiv D
  obtain ⟨_, S⟩ := exists_setting h1332 h1334 h1222 C.hyp C.plane
  have hN := le_normalizer_commutator (le_normalizer_cComp hii hQ hK)
  set U₀ := ⁅fsuU T V, K⁆ with hU₀
  obtain ⟨z, -, b, hz, hz1, -, -, hbV, hbV₂⟩ := S.exists_basis
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hzV₂ : z ∈ V₂ := C.plane.2 hz
  have haV : a ∈ V := C.plane.1.1 C.aV₂
  obtain ⟨x, hxL, hx3, hxz, hxa, hxb⟩ := S.exists_rot hzV haV hbV
    (fun h => C.a1 (h ▸ one_mem _)) (fun h => hbV₂ (h ▸ one_mem _))
    (fun h => C.a1 (h ▸ hz)) (fun h => hbV₂ (h ▸ hzV₂)) (fun h => hbV₂ (h ▸ C.aV₂))
    (fun h => hbV₂ (h ▸ mul_mem hzV₂ C.aV₂))
  have hxH : x ∈ l32nH T V := S.mem_g1 hz hz1 hxz
  have hxK : x ∈ K := mem_cComp_of_odd hii hQ hK hxH (by decide : Odd 3) hx3
  have hbU : b ∈ fsuU T V := C.V_U hbV
  have ha : a ∈ U₀ := by
    have h1 : ⁅b, x⁆ ∈ U₀ := Subgroup.commutator_mem_commutator hbU hxK
    have e : ⁅b, x⁆ = a⁻¹ := by
      rw [commutatorElement_def, show b * x * b⁻¹ * x⁻¹ = b * (x * b * x⁻¹)⁻¹ by group, hxb]
      group
    rw [e] at h1
    simpa using U₀.inv_mem h1
  have hb : b ∈ U₀ := by
    have h1 : ⁅a, x⁆ ∈ U₀ := Subgroup.commutator_mem_commutator C.aU hxK
    have e : ⁅a, x⁆ = a * b⁻¹ := by
      rw [commutatorElement_def, show a * x * a⁻¹ * x⁻¹ = a * (x * a * x⁻¹)⁻¹ by group, hxa]
    rw [e] at h1
    have := U₀.mul_mem (U₀.inv_mem h1) ha
    simpa [mul_assoc] using this
  have hz0 : z ∈ U₀ := by
    have haZ : a ∉ centerOf (fsuU T V) := fun hm =>
      C.pi_ne ((L128A.HatU.π_eq_zero_iff D C.aU).mpr hm)
    obtain ⟨u, huU, hua⟩ : ∃ u ∈ fsuU T V, u * a ≠ a * u := by
      by_contra hne
      push Not at hne
      exact haZ (Subgroup.mem_inf.mpr ⟨C.aU, Subgroup.mem_centralizer_iff.mpr fun u hu =>
        hne u hu⟩)
    have hne1 : ⁅u, a⁆ ≠ 1 := by
      rw [Ne, commutatorElement_eq_one_iff_mul_comm]
      exact hua
    have hcz : ⁅u, a⁆ = z := (S.eq_of_mem_V1 hz hz1 (C.comm u huU a C.aU)).resolve_left hne1
    have h1 : u * a * u⁻¹ ∈ U₀ := (Subgroup.mem_normalizer_iff.mp (hN (C.U_le huU)) a).mp ha
    rw [← hcz, commutatorElement_def]
    exact U₀.mul_mem h1 (U₀.inv_mem ha)
  have hV : V ≤ U₀ := by
    have hV1 : ∀ c ∈ fsuV1 T V, c ∈ U₀ := fun c hc => by
      rcases S.eq_of_mem_V1 hz hz1 hc with rfl | rfl
      · exact U₀.one_mem
      · exact hz0
    have hV₂ : ∀ w ∈ V₂, w ∈ U₀ := by
      intro w hw
      rcases C.V₂_cases w hw with hw1 | ⟨c, hc, rfl⟩
      · exact hV1 w hw1
      · exact U₀.mul_mem ha (hV1 c hc)
    intro v hv
    rcases S.mem_V hbV hbV₂ hv with hv2 | hv2
    · exact hV₂ v hv2
    · have := U₀.mul_mem (U₀.inv_mem hb) (hV₂ _ hv2)
      simpa using this
  exact conjClosure_le fun h hh v hv => (Subgroup.mem_normalizer_iff.mp (hN hh) v).mp (hV hv)

theorem fsuU_eq_commutator (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h14323 : Lemma14323Rest) (C : Ctx14332 G T L V V₂ g a D)
    (hii : Case14323ii T V g D) (hd : Module.finrank (ZMod 2) D.V = 4)
    (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V) (hQT : pCoreOf 2 (l32nH T V) ≤ T)
    (hK : K ∈ cComp (l32nH T V)) : fsuU T V = ⁅pCoreOf 2 K, K⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  have hKn := le_normalizer_cComp hii hQ hK
  have hUU₀ := fsuU_le_commutator h1332 h1334 h1222 C hii hQ hK
  have hUK : fsuU T V ≤ K := hUU₀.trans (Subgroup.commutator_le.mpr fun u hu k hk => by
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hKn (C.U_le hu)) k).mp hk) (inv_mem hk))
  have hUO : fsuU T V ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUK
      (hKH.trans (l32nH_le_normalizer_fsuU T V)) C.U2
  have hOQ : pCoreOf 2 K ≤ pCoreOf 2 (l32nH T V) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
      (hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  apply le_antisymm (hUU₀.trans (Subgroup.commutator_mono hUO le_rfl))
  calc ⁅pCoreOf 2 K, K⁆ ≤ ⁅pCoreOf 2 (l32nH T V), K⁆ := Subgroup.commutator_mono hOQ le_rfl
    _ = ⁅K, pCoreOf 2 (l32nH T V)⁆ := Subgroup.commutator_comm _ _
    _ ≤ fsuU T V := commutator_K_Q_le h1222 h12213 h14323 C hii hd hQ hQT hK

theorem f4_cases : ∀ c : RuType.F4, c = 0 ∨ c = 1 ∨ c = RuType.F4.ω ∨ c = 1 + RuType.F4.ω := by
  decide

theorem eq_bot_or_eq_top_of_transvections (W : AddSubgroup (Fin 2 → RuType.F4))
    (h12 : ∀ c, (c = 1 ∨ c = RuType.F4.ω) → ∀ w ∈ W, ![w 0 + c * w 1, w 1] ∈ W)
    (h21 : ∀ c, (c = 1 ∨ c = RuType.F4.ω) → ∀ w ∈ W, ![w 0, c * w 0 + w 1] ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hA : ∀ w ∈ W, ∀ c, ![c * w 1, 0] ∈ W := by
    have h1 : ∀ w ∈ W, ∀ c, (c = 1 ∨ c = RuType.F4.ω) → ![c * w 1, 0] ∈ W := by
      intro w hw c hc
      have e : ![c * w 1, 0] = ![w 0 + c * w 1, w 1] - w := by
        ext i
        fin_cases i <;> simp
      rw [e]
      exact W.sub_mem (h12 c hc w hw) hw
    intro w hw c
    rcases f4_cases c with rfl | rfl | rfl | rfl
    · have e : ![(0 : RuType.F4) * w 1, 0] = 0 := by
        ext i
        fin_cases i <;> simp
      rw [e]
      exact W.zero_mem
    · exact h1 w hw 1 (Or.inl rfl)
    · exact h1 w hw _ (Or.inr rfl)
    · have e : ![(1 + RuType.F4.ω) * w 1, 0] = ![1 * w 1, 0] + ![RuType.F4.ω * w 1, 0] := by
        ext i
        fin_cases i <;> simp [add_mul]
      rw [e]
      exact W.add_mem (h1 w hw 1 (Or.inl rfl)) (h1 w hw _ (Or.inr rfl))
  have hB : ∀ w ∈ W, ∀ c, ![0, c * w 0] ∈ W := by
    have h1 : ∀ w ∈ W, ∀ c, (c = 1 ∨ c = RuType.F4.ω) → ![0, c * w 0] ∈ W := by
      intro w hw c hc
      have e : ![0, c * w 0] = ![w 0, c * w 0 + w 1] - w := by
        ext i
        fin_cases i <;> simp
      rw [e]
      exact W.sub_mem (h21 c hc w hw) hw
    intro w hw c
    rcases f4_cases c with rfl | rfl | rfl | rfl
    · have e : ![0, (0 : RuType.F4) * w 0] = 0 := by
        ext i
        fin_cases i <;> simp
      rw [e]
      exact W.zero_mem
    · exact h1 w hw 1 (Or.inl rfl)
    · exact h1 w hw _ (Or.inr rfl)
    · have e : ![0, (1 + RuType.F4.ω) * w 0] = ![0, 1 * w 0] + ![0, RuType.F4.ω * w 0] := by
        ext i
        fin_cases i <;> simp [add_mul]
      rw [e]
      exact W.add_mem (h1 w hw 1 (Or.inl rfl)) (h1 w hw _ (Or.inr rfl))
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨⟨w, hw⟩, hw0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hW
  have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hfull : (∀ s, ![s, 0] ∈ W) ∧ ∀ t, ![0, t] ∈ W := by
    by_cases hw1 : w 1 = 0
    · have hw00 : w 0 ≠ 0 := by
        intro h
        apply hw0'
        ext i
        fin_cases i
        · exact h
        · exact hw1
      have h2 : ∀ t, ![0, t] ∈ W := fun t => by
        have := hB w hw (t * (w 0)⁻¹)
        rwa [mul_assoc, inv_mul_cancel₀ hw00, mul_one] at this
      refine ⟨fun s => ?_, h2⟩
      have := hA _ (h2 1) s
      simpa using this
    · have h1 : ∀ s, ![s, 0] ∈ W := fun s => by
        have := hA w hw (s * (w 1)⁻¹)
        rwa [mul_assoc, inv_mul_cancel₀ hw1, mul_one] at this
      refine ⟨h1, fun t => ?_⟩
      have := hB _ (h1 1) t
      simpa using this
  rw [eq_top_iff]
  intro v _
  have e : v = ![v 0, 0] + ![0, v 1] := by
    ext i
    fin_cases i <;> simp
  rw [e]
  exact W.add_mem (hfull.1 _) (hfull.2 _)

theorem transvection_eq_mul (c : RuType.F4) (hc : c = 1 ∨ c = RuType.F4.ω) :
    (∃ A B : SL(2, RuType.F4), A ^ 3 = 1 ∧ B ^ 3 = 1 ∧
      ((A * B : SL(2, RuType.F4)) : Matrix (Fin 2) (Fin 2) RuType.F4) = !![1, c; 0, 1]) ∧
    ∃ A B : SL(2, RuType.F4), A ^ 3 = 1 ∧ B ^ 3 = 1 ∧
      ((A * B : SL(2, RuType.F4)) : Matrix (Fin 2) (Fin 2) RuType.F4) = !![1, 0; c, 1] := by
  rcases hc with rfl | rfl
  · exact ⟨⟨⟨!![⟨2⟩, 0; 0, ⟨3⟩], by rw [Matrix.det_fin_two_of]; decide⟩,
      ⟨!![⟨3⟩, ⟨3⟩; 0, ⟨2⟩], by rw [Matrix.det_fin_two_of]; decide⟩, by decide, by decide,
      by decide⟩, ⟨⟨!![⟨2⟩, 0; 0, ⟨3⟩], by rw [Matrix.det_fin_two_of]; decide⟩,
      ⟨!![⟨3⟩, 0; ⟨2⟩, ⟨2⟩], by rw [Matrix.det_fin_two_of]; decide⟩, by decide, by decide,
      by decide⟩⟩
  · exact ⟨⟨⟨!![⟨2⟩, 0; 0, ⟨3⟩], by rw [Matrix.det_fin_two_of]; decide⟩,
      ⟨!![⟨3⟩, 1; 0, ⟨2⟩], by rw [Matrix.det_fin_two_of]; decide⟩, by decide, by decide,
      by decide⟩, ⟨⟨!![⟨2⟩, 0; 0, ⟨3⟩], by rw [Matrix.det_fin_two_of]; decide⟩,
      ⟨!![⟨3⟩, 0; ⟨3⟩, ⟨2⟩], by rw [Matrix.det_fin_two_of]; decide⟩, by decide, by decide,
      by decide⟩⟩

theorem mem_kd_of_odd (hii : Case14323ii T V g D) (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V)
    (hK : K ∈ cComp (l32nH T V)) {γ : ↥(D.img (l32nH T V))} {m : ℕ} (hm : Odd m)
    (hγ : γ ^ m = 1) : γ ∈ (K.subgroupOf (l32nH T V)).map (imgHom D) := by
  have hidx := index_kd hii hQ hK
  set Kd := (K.subgroupOf (l32nH T V)).map (imgHom D) with hKd
  by_contra hγK
  obtain ⟨j, rfl⟩ := hm
  have h2 : γ ^ 2 ∈ Kd := Subgroup.sq_mem_of_index_two hidx _
  have h1 : γ ^ (2 * j + 1) ∈ Kd := by
    rw [hγ]
    exact Kd.one_mem
  rw [pow_succ, pow_mul] at h1
  exact hγK (by simpa using Kd.mul_mem (Kd.inv_mem (Kd.pow_mem h2 j)) h1)

theorem eq_bot_or_eq_top_of_invariant (hii : Case14323ii T V g D)
    (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V) (hK : K ∈ cComp (l32nH T V))
    (W : AddSubgroup D.V)
    (hW : ∀ k ∈ K, ∀ hkN : k ∈ Subgroup.normalizer (fsuU T V : Set G), ∀ w ∈ W,
      D.ρ ⟨k, hkN⟩ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  obtain ⟨φ, ψ, hψ⟩ := hii.natural
  set Kd := (K.subgroupOf (l32nH T V)).map (imgHom D) with hKd
  have hact : ∀ A B : SL(2, RuType.F4), A ^ 3 = 1 → B ^ 3 = 1 → ∀ w ∈ W,
      ((A * B : SL(2, RuType.F4)) : Matrix (Fin 2) (Fin 2) RuType.F4).mulVec (ψ w) ∈
        W.map ψ.toAddMonoidHom := by
    intro A B hA hB w hw
    have hγA : φ.symm (SemidirectProduct.inl A) ∈ Kd := mem_kd_of_odd hii hQ hK
      (by decide : Odd 3) (by rw [← map_pow, ← map_pow, hA, map_one, map_one])
    have hγB : φ.symm (SemidirectProduct.inl B) ∈ Kd := mem_kd_of_odd hii hQ hK
      (by decide : Odd 3) (by rw [← map_pow, ← map_pow, hB, map_one, map_one])
    obtain ⟨⟨k, hkH⟩, hk, hkγ⟩ := Kd.mul_mem hγA hγB
    refine ⟨D.ρ ⟨k, l32nH_le_normalizer_fsuU T V hkH⟩ w,
      hW k (Subgroup.mem_subgroupOf.mp hk) _ w hw, ?_⟩
    have h1 := hψ (imgHom D ⟨k, hkH⟩) w
    rw [imgHom_apply] at h1
    show ψ _ = _
    rw [h1, hkγ, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← map_mul]
    simp [RuType.sigmaAct, RuType.frobVec]
  rcases eq_bot_or_eq_top_of_transvections (W.map ψ.toAddMonoidHom)
    (fun c hc w hw => by
      obtain ⟨⟨A, B, hA, hB, hAB⟩, -⟩ := transvection_eq_mul c hc
      obtain ⟨w', hw', rfl⟩ := hw
      have := hact A B hA hB w' hw'
      rw [hAB] at this
      convert this using 1
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two])
    (fun c hc w hw => by
      obtain ⟨-, ⟨A, B, hA, hB, hAB⟩⟩ := transvection_eq_mul c hc
      obtain ⟨w', hw', rfl⟩ := hw
      have := hact A B hA hB w' hw'
      rw [hAB] at this
      convert this using 1
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]) with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have : ψ w ∈ W.map ψ.toAddMonoidHom := ⟨w, hw, rfl⟩
    rw [h, AddSubgroup.mem_bot] at this
    exact (AddSubgroup.mem_bot).mpr (by simpa using this)
  · right
    rw [eq_top_iff]
    intro w _
    have : ψ w ∈ W.map ψ.toAddMonoidHom := h ▸ AddSubgroup.mem_top _
    obtain ⟨w', hw', hw'w⟩ := this
    rw [show w = w' from ψ.injective hw'w.symm]
    exact hw'

end L14332

end CFSG.Quasithin.H13
