module

public import CFSG.Quasithin.Background.Harris.R1.D4L2BAsm
public import CFSG.Quasithin.Background.Harris.R1.D4L2BSigma
public import CFSG.Quasithin.Background.Harris.R1.D4SetL2B

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.F112W CFSG.Quasithin.D4Hex CFSG.LargeExtraspecial.S63

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

omit [Finite G] in
theorem conj_mem_pCoreOf' {H : Subgroup G} {g : G} (hg : g ∈ H) {q : G}
    (hq : q ∈ pCoreOf 2 H) : g * q * g⁻¹ ∈ pCoreOf 2 H := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hq
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * k * (⟨g, hg⟩ : H)⁻¹, ?_, ?_⟩
  · exact Subgroup.Normal.conj_mem (CFSG.LieType.BorelTits.pCore_normal (r := 2) (G := H)) k hk _
  · simp

theorem exists_l2B_iso
    (hF : D4NFacts) (hset : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) (hSK : S ≤ K1)
    (e : ↥K1 ≃* ↥d4H)
    (heS : ∀ k : ↥K1, (k : G) ∈ S ↔ ((e k : D) ∈ d4U))
    (heV : ∀ k : ↥K1, (k : G) ∈ conjClosure Zs L2 ↔ ((e k : D) ∈ d4V)) :
    ∃ ψ : ↥(L2 ⊔ bigB K1 L2 S) ≃* ↥d4N, ∀ (b : G) (hb : b ∈ bigB K1 L2 S),
      (ψ ⟨b, Subgroup.mem_sup_right hb⟩ : D) = (e ⟨b, bigB_le_K1 hset hR hSK hb⟩ : D) := by
  classical
  have hBK : bigB K1 L2 S ≤ K1 := bigB_le_K1 hset hR hSK
  have hQS : pCoreOf 2 (L2 ⊔ S) ≤ S := SzR1.MNU.pCore_le_S_of_setting hset hR
  have hVQ : conjClosure Zs L2 ≤ pCoreOf 2 (L2 ⊔ S) := SzR1.MNU.V_le_pCore_of_setting hset hR
  have hQeq : pCoreOf 2 (L2 ⊔ S) = S ⊓ Subgroup.centralizer (conjClosure Zs L2 : Set G) :=
    SzR1.MNU.pCore_eq_of_setting hset hR
  have hVK : conjClosure Zs L2 ≤ K1 := hVQ.trans (hQS.trans hSK)
  have hV4 : Nat.card (conjClosure Zs L2) = 4 := hset.V_card
  have hV2 : ∀ v ∈ conjClosure Zs L2, v * v = 1 := fun v hv => by
    have := (SzR1.MNU.V_elemAbelian_of_setting hset hR).2 v hv
    rwa [pow_two] at this
  have hBX : bigB K1 L2 S ≤ L2 ⊔ bigB K1 L2 S := le_sup_right
  have hPX : L2 ⊔ S ≤ L2 ⊔ bigB K1 L2 S :=
    sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hXV : L2 ⊔ bigB K1 L2 S ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
    sup_le (le_normalizer_conjClosure Zs L2) (F112J2.bigB_le_normalizer_V hset hR)
  have hXQ : ∀ x ∈ L2 ⊔ bigB K1 L2 S, ∀ q ∈ pCoreOf 2 (L2 ⊔ S), x * q * x⁻¹ ∈ pCoreOf 2 (L2 ⊔ S) := by
    intro x hx q hq
    have h1 := pCoreOf_L2B hset hR hSK
    rw [← h1] at hq ⊢
    exact conj_mem_pCoreOf' hx hq
  have heS' : ∀ k ∈ K1, k ∈ S ↔ ebar e k ∈ d4U := fun k hk => by
    rw [ebar_of_mem e hk]; exact heS ⟨k, hk⟩
  have heV' : ∀ k ∈ K1, k ∈ conjClosure Zs L2 ↔ ebar e k ∈ d4V := fun k hk => by
    rw [ebar_of_mem e hk]; exact heV ⟨k, hk⟩
  have hUH : d4U ≤ d4H := hF.U_le_H
  have hVH : d4V ≤ d4H := hF.V_le_H
  have hBH : d4B ≤ d4H := inf_le_left
  have hQ2U : Q2 ≤ d4U := by rw [← hF.cent]; exact inf_le_left
  have hBt : ∀ k ∈ K1, k ∈ bigB K1 L2 S ↔ ebar e k ∈ d4B := by
    intro k hk
    rw [bigB_eq_of_le hset hR hSK, Subgroup.mem_inf, ← hF.normalizer_U]
    exact ⟨fun h => (mem_normalizer_ebar_iff e hUH heS' hSK hk).mp h.2,
      fun h => ⟨hk, (mem_normalizer_ebar_iff e hUH heS' hSK hk).mpr h⟩⟩
  have hCt : ∀ k ∈ K1, k ∈ Subgroup.centralizer (conjClosure Zs L2 : Set G) ↔
      ebar e k ∈ Subgroup.centralizer (d4V : Set D) := fun k hk =>
    mem_centralizer_ebar_iff e hVH heV' hVK hk
  have hQt : ∀ k ∈ K1, k ∈ pCoreOf 2 (L2 ⊔ S) ↔ ebar e k ∈ Q2 := by
    intro k hk
    rw [hQeq, ← hF.cent, Subgroup.mem_inf, Subgroup.mem_inf, heS' k hk, hCt k hk]
  have hQK : pCoreOf 2 (L2 ⊔ S) ≤ K1 := hQS.trans hSK
  have hZ : ∀ q ∈ pCoreOf 2 (L2 ⊔ S), (∀ q' ∈ pCoreOf 2 (L2 ⊔ S), q * q' = q' * q) →
      q ∈ conjClosure Zs L2 := by
    intro q hq hqc
    have hqK : q ∈ K1 := hQK hq
    refine (heV' q hqK).mpr (hF.center _ ((hQt q hqK).mp hq) fun y hy => ?_)
    obtain ⟨x, hxK, rfl⟩ := exists_ebar_eq e (hUH (hQ2U hy))
    have hxQ : x ∈ pCoreOf 2 (L2 ⊔ S) := (hQt x hxK).mpr hy
    rw [← ebar_mul e hqK hxK, ← ebar_mul e hxK hqK, hqc x hxQ]
  obtain ⟨Y1, hY1K, hY1e⟩ := exists_ebar_eq e (hBH hF.y1_mem)
  obtain ⟨Y2, hY2K, hY2e⟩ := exists_ebar_eq e (hBH hF.y2_mem)
  obtain ⟨T, hTK, hTe⟩ := exists_ebar_eq e (hBH hF.ze_mem)
  obtain ⟨R0, hR0K, hR0e⟩ := exists_ebar_eq e (hBH hF.r0_mem)
  have hY1B : Y1 ∈ bigB K1 L2 S := (hBt Y1 hY1K).mpr (hY1e ▸ hF.y1_mem)
  have hY2B : Y2 ∈ bigB K1 L2 S := (hBt Y2 hY2K).mpr (hY2e ▸ hF.y2_mem)
  have hTB : T ∈ bigB K1 L2 S := (hBt T hTK).mpr (hTe ▸ hF.ze_mem)
  have hR0B : R0 ∈ bigB K1 L2 S := (hBt R0 hR0K).mpr (hR0e ▸ hF.r0_mem)
  have hY1Q : Y1 ∈ pCoreOf 2 (L2 ⊔ S) := (hQt Y1 hY1K).mpr (hY1e ▸ y1D_mem)
  have hY2Q : Y2 ∈ pCoreOf 2 (L2 ⊔ S) := (hQt Y2 hY2K).mpr (hY2e ▸ y2D_mem)
  have hT7 : T ^ 7 = 1 := by
    refine (ebar_eq_one_iff e (K1.pow_mem hTK 7)).mp ?_
    rw [ebar_pow e hTK, hTe]
    exact zeD_pow_seven
  have hR2 : R0 * R0 = 1 := by
    refine (ebar_eq_one_iff e (K1.mul_mem hR0K hR0K)).mp ?_
    rw [ebar_mul e hR0K hR0K, hR0e]
    exact r0D_sq
  have hBcard : Nat.card (bigB K1 L2 S) = 28672 := by
    rw [← hF.card_B]
    apply Nat.card_congr
    refine Equiv.ofBijective
      (fun b : ↥(bigB K1 L2 S) => (⟨ebar e b, (hBt b (hBK b.2)).mp b.2⟩ : ↥d4B)) ⟨?_, ?_⟩
    · intro a b hab
      exact Subtype.ext (ebar_inj e (hBK a.2) (hBK b.2) (congrArg Subtype.val hab))
    · intro y
      obtain ⟨x, hx, hxy⟩ := exists_ebar_eq e (hBH y.2)
      exact ⟨⟨x, (hBt x hx).mpr (hxy ▸ y.2)⟩, Subtype.ext hxy⟩
  have hgen : Subgroup.closure ({Y1, Y2, T, R0} : Set G) = bigB K1 L2 S := by
    have hCB : Subgroup.closure ({Y1, Y2, T, R0} : Set G) ≤ bigB K1 L2 S := by
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    refine le_antisymm hCB fun b hb => ?_
    have hbK : b ∈ K1 := hBK hb
    have hmem : ebar e b ∈ Subgroup.closure ({y1D, y2D, zeD, r0D} : Set D) := by
      rw [hF.closure_B]; exact (hBt b hbK).mp hb
    have key : ∀ y ∈ Subgroup.closure ({y1D, y2D, zeD, r0D} : Set D),
        ∃ x ∈ Subgroup.closure ({Y1, Y2, T, R0} : Set G), ebar e x = y := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact ⟨Y1, Subgroup.subset_closure (by simp), hY1e⟩
        · exact ⟨Y2, Subgroup.subset_closure (by simp), hY2e⟩
        · exact ⟨T, Subgroup.subset_closure (by simp), hTe⟩
        · exact ⟨R0, Subgroup.subset_closure (by simp), hR0e⟩
      | one => exact ⟨1, Subgroup.one_mem _, ebar_one e⟩
      | mul y y' _ _ ihy ihy' =>
        obtain ⟨x, hx, rfl⟩ := ihy
        obtain ⟨x', hx', rfl⟩ := ihy'
        exact ⟨x * x', Subgroup.mul_mem _ hx hx',
          ebar_mul e (hBK (hCB hx)) (hBK (hCB hx'))⟩
      | inv y _ ih =>
        obtain ⟨x, hx, rfl⟩ := ih
        exact ⟨x⁻¹, Subgroup.inv_mem _ hx, ebar_inv e (hBK (hCB hx))⟩
    obtain ⟨x, hxC, hxb⟩ := key _ hmem
    have : x = b := ebar_inj e (hBK (hCB hxC)) hbK hxb
    exact this ▸ hxC
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Zs, z ≠ 1 := by
    have hne : Zs ≠ ⊥ := by
      intro h
      have := hset.card_Z
      rw [h, Subgroup.card_bot] at this
      omega
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  have hzV : z ∈ conjClosure Zs L2 := le_conjClosure Zs L2 hzZ
  have hTz : T * z * T⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp (F112J2.bigB_le_centralizer_Z hset hR hTB) z hzZ
    rw [← this]; group
  have hTV : T ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
    F112J2.bigB_le_normalizer_V hset hR hTB
  have hTV' : ∀ v ∈ conjClosure Zs L2, T * v * T⁻¹ ∈ conjClosure Zs L2 := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hTV v).mp hv
  have hTcentV : ∀ v ∈ conjClosure Zs L2, T * v * T⁻¹ = v := fun v hv =>
    conj_eq_of_pow_seven hV4 hV2 hTV' hT7 hzV hz1 hTz hv
  have hB7 : 7 ∣ Nat.card (bigB K1 L2 S) := by rw [hBcard]; norm_num
  obtain ⟨s, hsP, hs3o, hsT, hsC⟩ : ∃ s ∈ L2 ⊔ S, orderOf s = 3 ∧ s * T = T * s ∧
      s ∉ Subgroup.centralizer (conjClosure Zs L2 : Set G) := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    by_cases hT1 : T = 1
    · obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(bigB K1 L2 S)) 7 hB7
      obtain ⟨s, hs, h3, -, hn⟩ := exists_three_comm hset hR hSK (t : G) t.2
        (by rw [Subgroup.orderOf_coe]; exact ht)
      exact ⟨s, hs, h3, by rw [hT1]; simp, hn⟩
    · have h7 : orderOf T = 7 := by
        have hd : orderOf T ∣ 7 := orderOf_dvd_of_pow_eq_one hT7
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hT1
        · exact h
      exact exists_three_comm hset hR hSK T hTB h7
  have hs3 : s * s * s = 1 := by
    have := pow_orderOf_eq_one s
    rw [hs3o] at this
    simpa [pow_succ, mul_assoc] using this
  have hsX : s ∈ L2 ⊔ bigB K1 L2 S := hPX hsP
  obtain ⟨w, hwV, hsw⟩ : ∃ w ∈ conjClosure Zs L2, s * w * s⁻¹ ≠ w := by
    by_contra hcon
    push Not at hcon
    apply hsC
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := hcon v hv
    calc v * s = (s * v * s⁻¹) * s := by rw [this]
      _ = s * v := by group
  have hsV : s ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G) := hXV hsX
  obtain ⟨ε, hε⟩ := exists_equiv_ebar e hQK (hQ2U.trans hUH) hQt
  have hεT : ∀ q q' : ↥(pCoreOf 2 (L2 ⊔ S)), (q' : G) = T * q * T⁻¹ →
      (ε q' : D) = zeD * (ε q : D) * zeD⁻¹ := by
    intro q q' hq'
    rw [hε, hε, hq', ebar_conj e hTK (hQK q.2), hTe]
  have hTX : T ∈ L2 ⊔ bigB K1 L2 S := hBX hTB
  obtain ⟨s', hs'eq, hs'act⟩ := exists_s_action ε hF.kc_cent (hXQ s hsX) (hXQ T hTX) hεT hsT hs3
    ⟨w, hVQ hwV, hsw⟩
  have hs'X : s' ∈ L2 ⊔ bigB K1 L2 S := by
    rcases hs'eq with h | h <;> rw [h]
    · exact hsX
    · exact Subgroup.inv_mem _ hsX
  have hs'3 : s' * s' * s' = 1 := by
    rcases hs'eq with h | h <;> rw [h]
    · exact hs3
    · calc s⁻¹ * s⁻¹ * s⁻¹ = (s * s * s)⁻¹ := by group
        _ = 1 := by rw [hs3]; simp
  have hs'T : s' * T = T * s' := by
    rcases hs'eq with h | h <;> rw [h]
    · exact hsT
    · exact (Commute.inv_left (show Commute s T from hsT) : Commute s⁻¹ T)
  obtain ⟨w', hw'V, hs'w'⟩ : ∃ w' ∈ conjClosure Zs L2, s' * w' * s'⁻¹ ≠ w' := by
    rcases hs'eq with h | h <;> rw [h]
    · exact ⟨w, hwV, hsw⟩
    · refine ⟨s * w * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsV w).mp hwV, fun h => hsw ?_⟩
      have e1 : s⁻¹ * (s * w * s⁻¹) * s⁻¹⁻¹ = w := by group
      rw [e1] at h
      exact h.symm
  have hs'V : s' ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G) := hXV hs'X
  have hs'V' : ∀ v ∈ conjClosure Zs L2, s' * v * s'⁻¹ ∈ conjClosure Zs L2 := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hs'V v).mp hv
  have hR0X : R0 ∈ L2 ⊔ bigB K1 L2 S := hBX hR0B
  have hR0V : R0 ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G) := hXV hR0X
  have hQC : ∀ q ∈ pCoreOf 2 (L2 ⊔ S), ∀ v ∈ conjClosure Zs L2, v * q = q * v := by
    intro q hq v hv
    have : q ∈ Subgroup.centralizer (conjClosure Zs L2 : Set G) := by
      rw [hQeq] at hq; exact hq.2
    exact Subgroup.mem_centralizer_iff.mp this v hv
  have hact : ∀ q ∈ pCoreOf 2 (L2 ⊔ S), ebar e (s' * q * s'⁻¹) = s0D * ebar e q * s0D⁻¹ := by
    intro q hq
    have h1 := hs'act ⟨q, hq⟩ ⟨s' * q * s'⁻¹, hXQ s' hs'X q hq⟩ rfl
    rw [hε, hε] at h1
    exact h1
  obtain ⟨c, hc⟩ : ∃ c : G, c = R0 * s' * R0⁻¹ * s' := ⟨_, rfl⟩
  have hcX : c ∈ L2 ⊔ bigB K1 L2 S := by
    rw [hc]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hR0X hs'X)
      (Subgroup.inv_mem _ hR0X)) hs'X
  have hcQ : ∀ q ∈ pCoreOf 2 (L2 ⊔ S), c * q * c⁻¹ = q := by
    intro q hq
    have hR0iX : R0⁻¹ ∈ L2 ⊔ bigB K1 L2 S := Subgroup.inv_mem _ hR0X
    have hq1 := hXQ s' hs'X q hq
    have hq2 := hXQ R0⁻¹ hR0iX _ hq1
    have hq3 := hXQ s' hs'X _ hq2
    have hq4 := hXQ R0 hR0X _ hq3
    have e0 : c * q * c⁻¹ = R0 * (s' * (R0⁻¹ * (s' * q * s'⁻¹) * R0⁻¹⁻¹) * s'⁻¹) * R0⁻¹ := by
      rw [hc]; group
    refine ebar_inj e (hQK (e0 ▸ hq4)) (hQK hq) ?_
    rw [e0, ebar_conj e hR0K (hQK hq3), hact _ hq2, ebar_conj e (K1.inv_mem hR0K) (hQK hq1),
      hact q hq, ebar_inv e hR0K, hR0e]
    calc r0D * (s0D * (r0D⁻¹ * (s0D * ebar e q * s0D⁻¹) * r0D⁻¹⁻¹) * s0D⁻¹) * r0D⁻¹ =
        (r0D * s0D * r0D⁻¹ * s0D) * ebar e q * (r0D * s0D * r0D⁻¹ * s0D)⁻¹ := by group
      _ = ebar e q := by rw [r0D_s0D]; group
  have hccomm : ∀ q ∈ pCoreOf 2 (L2 ⊔ S), c * q = q * c := by
    intro q hq
    calc c * q = (c * q * c⁻¹) * c := by group
      _ = q * c := by rw [hcQ q hq]
  have hcQ' : c ∈ pCoreOf 2 (L2 ⊔ S) := by
    refine centralizer_pCore_L2B_le hset hR hSK ⟨hcX, ?_⟩
    intro q hq
    exact (hccomm q hq).symm
  have hcV : c ∈ conjClosure Zs L2 := hZ c hcQ' hccomm
  obtain ⟨u, huV, hu3, huR⟩ := exists_adjust hV4 hV2 hs'V hR0V hs'3 hR2 hw'V hs'w'
    (by rw [← hc]; exact hcV)
  have huQ : u ∈ pCoreOf 2 (L2 ⊔ S) := hVQ huV
  have hS0X : s' * u ∈ L2 ⊔ bigB K1 L2 S :=
    Subgroup.mul_mem _ hs'X (hPX (pCoreOf_le 2 (L2 ⊔ S) huQ))
  have hu_comm : ∀ q ∈ pCoreOf 2 (L2 ⊔ S), u * q = q * u := fun q hq => hQC q hq u huV
  have huT : u * T = T * u := by
    calc u * T = (T * u * T⁻¹) * T := by rw [hTcentV u huV]
      _ = T * u := by group
  have hS0T : s' * u * T = T * (s' * u) := by
    calc s' * u * T = s' * (u * T) := by group
      _ = s' * (T * u) := by rw [huT]
      _ = (s' * T) * u := by group
      _ = (T * s') * u := by rw [hs'T]
      _ = T * (s' * u) := by group
  have hS0conj : ∀ y ∈ pCoreOf 2 (L2 ⊔ S), s' * u * y * (s' * u)⁻¹ = s' * y * s'⁻¹ := by
    intro y hy
    calc s' * u * y * (s' * u)⁻¹ = s' * (u * y * u⁻¹) * s'⁻¹ := by group
      _ = s' * y * s'⁻¹ := by rw [hu_comm y hy]; group
  have hY1S : s' * u * Y1 * (s' * u)⁻¹ ∈ K1 := by
    rw [hS0conj Y1 hY1Q]; exact hQK (hXQ s' hs'X Y1 hY1Q)
  have hY2S : s' * u * Y2 * (s' * u)⁻¹ ∈ K1 := by
    rw [hS0conj Y2 hY2Q]; exact hQK (hXQ s' hs'X Y2 hY2Q)
  have hrel : ∀ r ∈ nRels, evalWord ![Y1, Y2, T, R0, s' * u] r = 1 :=
    relators_hold e hY1K hY2K hTK hR0K hY1e hY2e hTe hR0e hu3 (by rw [hS0T]; group) huR hY1S
      (by rw [hS0conj Y1 hY1Q, hact Y1 hY1Q, hY1e]) hY2S
      (by rw [hS0conj Y2 hY2Q, hact Y2 hY2Q, hY2e])
  have hS0B : s' * u ∉ bigB K1 L2 S := by
    intro hmem
    have hcent := Subgroup.mem_centralizer_iff.mp
      (F112J2.bigB_le_centralizer_Z hset hR hmem) z hzZ
    apply conj_ne_of_cube hV4 hV2 hs'V' hs'3 hw'V hs'w' hzV hz1
    calc s' * z * s'⁻¹ = s' * (u * z * u⁻¹) * s'⁻¹ := by
          rw [commute_of_sq hV2 huV hzV]; group
      _ = (s' * u) * z * (s' * u)⁻¹ := by group
      _ = z := by rw [← hcent]; group
  let eB : ↥(bigB K1 L2 S) →* D :=
    d4H.subtype.comp (e.toMonoidHom.comp (Subgroup.inclusion hBK))
  have heB : ∀ (y : G) (hy : y ∈ bigB K1 L2 S) (hyK : y ∈ K1), eB ⟨y, hy⟩ = ebar e y := by
    intro y hy hyK
    rw [ebar_of_mem e hyK]
    rfl
  obtain ⟨ψ, hψ⟩ := exists_iso_of_relators hF hBX hY1B hY2B hTB hR0B hS0X hrel hgen hS0B
    (card_L2B_eq hset hR hSK) hBcard eB ((heB Y1 hY1B hY1K).trans hY1e)
    ((heB Y2 hY2B hY2K).trans hY2e) ((heB T hTB hTK).trans hTe)
    ((heB R0 hR0B hR0K).trans hR0e)
  exact ⟨ψ, hψ⟩

end CFSG.Quasithin.Background.Harris.R1.D4Vert
