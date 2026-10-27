module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23NXB
public import CFSG.Quasithin.Vol2.Ch5Sec2M23BSW
public import CFSG.Quasithin.Vol2.Ch5Sec2M23GL4
public import CFSG.Quasithin.Vol2.Ch5Sec2M23NX

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.M23Norm3 CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Fischer

variable {G : Type} [Group G] [Finite G]

theorem card_centralizer_eq_or_of_setting
    (h526 : Stmt5_2_6) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4)
    (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {w j : G} (hw3 : orderOf w = 3) (hj2 : orderOf j = 2)
    (hwj : w * j = j * w) :
    Nat.card (Subgroup.centralizer ({w} : Set G)) = 36 ∨
      Nat.card (Subgroup.centralizer ({w} : Set G)) = 180 := by
  obtain ⟨y, u, r, -, hy3, huU, hu1, hyu, hru, hry, hcent, hCU⟩ :=
    exists_y_u_of_setting h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS
  obtain ⟨hUea, -, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hU2 : ∀ e ∈ pCoreOf 2 M2, e * e = 1 := fun e he => by rw [← sq]; exact hUea.2 e he
  have hUc : ∀ e ∈ pCoreOf 2 M2, ∀ f ∈ pCoreOf 2 M2, e * f = f * e := fun e he f hf =>
    congrArg Subtype.val (hUea.1.1.comm ⟨e, he⟩ ⟨f, hf⟩)
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hU2 u huU) hu1
  have huE : u ∈ pCoreOf 2 M2 ⊓ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_inf.mpr ⟨huU, Subgroup.mem_centralizer_singleton_iff.mpr hyu.symm⟩
  have hinv : ∀ i j : G, orderOf i = 2 → orderOf j = 2 → ∃ g : G, g * i * g⁻¹ = j :=
    fun i j hi hj => stmt5_2_13_of hQ h5211 h526 h1284 hSz hU4 hsp G T M L V H B D L₂ n M2 π hyp
      hM23 hS i j hi hj
  have h9 := not_nine_dvd_card_centralizer hQ h5211 hyp hM23 hS huU hu1
  have hy := card_centralizer_eq_or_of_bsw hy3 hu2 huE inf_le_right
    (fun e he => hU2 e (Subgroup.mem_inf.mp he).1)
    (fun e he f hf => hUc e (Subgroup.mem_inf.mp he).1 f (Subgroup.mem_inf.mp hf).1) hCU
    (fun g hgy hgu => by
      obtain ⟨e, he, hey, a, hga⟩ := hcent g hgy hgu
      exact ⟨e, Subgroup.mem_inf.mpr ⟨he, Subgroup.mem_centralizer_singleton_iff.mpr hey⟩, a, hga⟩)
    hru hry hinv h9
  obtain ⟨g, hg⟩ := exists_conj_eq_or_eq_inv_of_commute hy3 hu2 hyu hinv h9 hw3 hj2 hwj
  rw [card_centralizer_eq_of_conj hg]
  exact hy

theorem card_centralizer_of_mem_centralizerModO2
    (h526 : Stmt5_2_6) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4)
    (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) (hV : IsVFacts M L) {z : G} (hzM : z ∈ M)
    (hzC : z ∈ centralizerModO2 L) (hz3 : orderOf z = 3) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) = 36 ∨
      Nat.card (Subgroup.centralizer ({z} : Set G)) = 180 := by
  have hCL := card_centralizer_inf_L hV hzM hzC hz3
  have h2 : 2 ∣ Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [hCL]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hj2 : orderOf (j : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hj
  have hzj : z * j = j * z :=
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp j.2).2).symm
  exact card_centralizer_eq_or_of_setting h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS hz3 hj2 hzj

theorem s1245_mem_normalizer_k4Sub :
    s1245 ∈ Subgroup.normalizer (k4Sub : Set (Perm (Fin 7))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨σ, hσ, rfl⟩
    exact perm7_facts.2.2.2.2.2.1 σ hσ
  · exact (Subgroup.card_map_of_injective (MulAut.conj s1245).injective).ge

theorem s1245_conj_E9 {σ : Perm (Fin 7)} (hσ : σ ∈ E9Sub) :
    s1245 * σ * s1245⁻¹ = σ⁻¹ := by
  obtain ⟨a, b, rfl⟩ := hσ
  have h1 : s1245 * c123 ^ a * s1245⁻¹ = (c123 ^ a)⁻¹ := by
    rw [← conj_pow, perm7_facts.2.2.2.2.2.2.2.2.2.2.2.2.1, inv_pow]
  have h2 : s1245 * c456 ^ b * s1245⁻¹ = (c456 ^ b)⁻¹ := by
    rw [← conj_pow, perm7_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1, inv_pow]
  have hc : Commute c123 c456 := perm7_facts.2.2.2.2.2.2.1
  calc s1245 * (c123 ^ a * c456 ^ b) * s1245⁻¹
      = (s1245 * c123 ^ a * s1245⁻¹) * (s1245 * c456 ^ b * s1245⁻¹) := by
        simp only [mul_assoc, inv_mul_cancel_left]
    _ = (c123 ^ a)⁻¹ * (c456 ^ b)⁻¹ := by rw [h1, h2]
    _ = (c123 ^ a * c456 ^ b)⁻¹ := by
        rw [mul_inv_rev]
        exact ((hc.pow_pow a b).inv_inv).eq

theorem exists_inv_of_setting
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {x : G} (hxM2 : x ∈ M2) (hxM : x ∈ M) (hx3 : orderOf x = 3)
    (hxE : π ⟨x, hxM2⟩ ∈ E9Sub) : ∃ r ∈ M, r * x * r⁻¹ = x⁻¹ := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hUle, -, -⟩ := inf_L_facts_of_setting h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hUM : pCoreOf 2 M2 ≤ M := hUle.trans (inf_le_right.trans hyp.L_le)
  have hs : s1245 ∈ π.range := by
    rw [hS.range_eq]
    exact Equiv.Perm.mem_alternatingGroup.mpr perm7_facts.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hs
  have hmM : (m : G) ∈ M := mem_M_of_mem_normalizer_k4Sub h526 h527 h1284 hSz hU4 hsp hQ hyp hM23
    hS m (by rw [hm]; exact s1245_mem_normalizer_k4Sub)
  have hmx : (m : G) * x * (m : G)⁻¹ ∈ M2 := M2.mul_mem (M2.mul_mem m.2 hxM2) (M2.inv_mem m.2)
  have hπ : π ⟨(m : G) * x * (m : G)⁻¹, hmx⟩ = π ⟨x⁻¹, M2.inv_mem hxM2⟩ := by
    have e1 : (⟨(m : G) * x * (m : G)⁻¹, hmx⟩ : ↥M2) = m * ⟨x, hxM2⟩ * m⁻¹ := rfl
    have e2 : (⟨x⁻¹, M2.inv_mem hxM2⟩ : ↥M2) = (⟨x, hxM2⟩ : ↥M2)⁻¹ := rfl
    rw [e1, e2, map_mul, map_mul, map_inv, map_inv, hm]
    exact s1245_conj_E9 hxE
  have hmx3 : orderOf ((m : G) * x * (m : G)⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx3
  have hxi3 : orderOf x⁻¹ = 3 := by rw [orderOf_inv]; exact hx3
  obtain ⟨g, hg, hgx⟩ := exists_conj_mem_sup_of_map_eq_three hS.ker_eq
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2) (CFSG.LieType.BorelTits.pCoreOf_le 2 M2) hmx
    (M2.inv_mem hxM2) hmx3 hxi3 hπ
  have hgM : g ∈ M := by
    refine (sup_le hUM ?_) hg
    rw [Subgroup.zpowers_le]
    exact M.mul_mem (M.mul_mem hmM hxM) (M.inv_mem hmM)
  refine ⟨g * m, M.mul_mem hgM hmM, ?_⟩
  rw [← hgx]
  group

theorem exists_x_of_setting
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    ∃ x : G, x ∈ M ⊓ centralizerModO2 L ∧ orderOf x = 3 ∧
      Subgroup.centralizer ({x} : Set G) ≤ M ∧
      Nat.card (Subgroup.centralizer ({x} : Set G)) = 180 ∧ ∃ r ∈ M, r * x * r⁻¹ = x⁻¹ := by
  obtain ⟨x, hxM2, hxMC, hx3, hxE⟩ :=
    exists_mem_centralizerModO2_of_setting h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.mp hxMC
  have hV := isVFacts_of_setting h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hEM := preE9_le_M h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hE := card_preE9 hQ hyp hM23 hS
  have hxpre : x ∈ preE9 M2 π := ⟨⟨x, hxM2⟩, hxE, rfl⟩
  obtain ⟨W, hW, hW180⟩ := exists_le_centralizer_dvd_card hV hEM hE hxpre hxM hxC hx3
  have hC := card_centralizer_of_mem_centralizerModO2 h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS
    hV hxM hxC hx3
  have hWC : W ≤ Subgroup.centralizer ({x} : Set G) := hW.trans inf_le_right
  have hd := Subgroup.card_dvd_of_le hWC
  have h180 : Nat.card (Subgroup.centralizer ({x} : Set G)) = 180 := by
    rcases hC with h | h
    · exfalso
      rw [h] at hd
      have := hW180.trans hd
      norm_num at this
    · exact h
  have hWeq : W = Subgroup.centralizer ({x} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hWC (by rw [h180]; exact Nat.le_of_dvd Nat.card_pos hW180)
  refine ⟨x, hxMC, hx3, ?_, h180,
    exists_inv_of_setting h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS hxM2 hxM hx3 hxE⟩
  rw [← hWeq]
  exact hW.trans inf_le_left

omit [Finite G] in
theorem normalizer_zpowers_le_of {M : Subgroup G} {x r : G} (hx3 : orderOf x = 3)
    (hCM : Subgroup.centralizer ({x} : Set G) ≤ M) (hrM : r ∈ M) (hr : r * x * r⁻¹ = x⁻¹) :
    Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ M := by
  intro m hm
  rcases (mem_normalizer_zpowers_iff_of_order_three hx3).mp hm with h | h
  · apply hCM
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m * x = m * x * m⁻¹ * m := by group
      _ = x * m := by rw [h]
  · have hr' : r * x⁻¹ * r⁻¹ = x := by
      calc r * x⁻¹ * r⁻¹ = (r * x * r⁻¹)⁻¹ := by group
        _ = x := by rw [hr, inv_inv]
    have hrm : r * m ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc r * m * x = r * (m * x * m⁻¹) * r⁻¹ * (r * m) := by group
        _ = x * (r * m) := by rw [h, hr']
    have := M.mul_mem (M.inv_mem hrM) (hCM hrm)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this

omit [Finite G] in
theorem card_normalizer_zpowers {x r : G} (hx3 : orderOf x = 3) (hr : r * x * r⁻¹ = x⁻¹) :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers x : Set G)) =
      2 * Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  set N := Subgroup.normalizer (Subgroup.zpowers x : Set G) with hN
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hxx : x ≠ x⁻¹ := by
    intro h
    have h1 : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel x
    have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
    rw [hx3] at hd
    norm_num at hd
  have hmemC : ∀ g : G, g ∈ C ↔ g * x * g⁻¹ = x := by
    intro g
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      rw [h]
      group
    · intro h
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h]
  have hCN : C ≤ N := fun g hg =>
    (mem_normalizer_zpowers_iff_of_order_three hx3).mpr (Or.inl ((hmemC g).mp hg))
  have hrN : r ∈ N := (mem_normalizer_zpowers_iff_of_order_three hx3).mpr (Or.inr hr)
  have hidx : (C.subgroupOf N).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨r, hrN⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rw [hmemC, hmemC]
    have hbr : (b : G) * r * x * ((b : G) * r)⁻¹ = ((b : G) * x * (b : G)⁻¹)⁻¹ := by
      calc (b : G) * r * x * ((b : G) * r)⁻¹ = (b : G) * (r * x * r⁻¹) * (b : G)⁻¹ := by group
        _ = ((b : G) * x * (b : G)⁻¹)⁻¹ := by rw [hr]; group
    rw [hbr]
    rcases (mem_normalizer_zpowers_iff_of_order_three hx3).mp b.2 with h | h
    · rw [h]
      exact Or.inr ⟨rfl, fun h' => hxx h'.symm⟩
    · rw [h, inv_inv]
      exact Or.inl ⟨rfl, fun h' => hxx h'.symm⟩
  have h1 := Subgroup.card_mul_index (C.subgroupOf N)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv] at h1
  omega

theorem normalizer_le_and_gammaL2_of {M L : Subgroup G} (hV : IsVFacts M L) {x r : G}
    (hxM : x ∈ M) (hxC : x ∈ centralizerModO2 L) (hx3 : orderOf x = 3)
    (hCM : Subgroup.centralizer ({x} : Set G) ≤ M)
    (hC180 : Nat.card (Subgroup.centralizer ({x} : Set G)) = 180) (hrM : r ∈ M)
    (hr : r * x * r⁻¹ = x⁻¹) :
    Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ M ∧
      Nonempty (↥(M ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set G)) ≃* ↥(GammaL2 F4)) := by
  have hNM := normalizer_zpowers_le_of hx3 hCM hrM hr
  refine ⟨hNM, ?_⟩
  rw [inf_of_le_right hNM]
  have hMV : M ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hV.normal.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hfpf : IsFpfThree (pCoreOf 2 L) x :=
    { sq := hV.sq
      comm := hV.comm
      conj_mem := fun v hv => (Subgroup.mem_normalizer_iff.mp (hMV hxM) v).mp hv
      fpf := fun v hv hxv => eq_one_of_mem_pCoreOf_L_of_commute hV hxM hxC hx3 hv hxv
      cube := by rw [← hx3]; exact pow_orderOf_eq_one x }
  have hN360 : Nat.card (Subgroup.normalizer (Subgroup.zpowers x : Set G)) = 360 := by
    rw [card_normalizer_zpowers hx3 hr, hC180]
  refine nonempty_mulEquiv_gammaL2 hfpf hV.card (hNM.trans hMV)
    (fun m hm => (mem_normalizer_zpowers_iff_of_order_three hx3).mp hm) ?_ hN360
  intro m hm hmc
  have hmM := hNM hm
  have hmV : m ∈ pCoreOf 2 L := hV.cent (Subgroup.mem_inf.mpr ⟨hmM,
    Subgroup.mem_centralizer_iff.mpr fun v hv => (hmc v hv).symm⟩)
  rcases (mem_normalizer_zpowers_iff_of_order_three hx3).mp hm with h | h
  · exact hfpf.fpf m hmV (by
      calc x * m = m * x * m⁻¹ * m := by rw [h]
        _ = m * x := by group)
  · exfalso
    have hmx : m * x = x⁻¹ * m := by
      calc m * x = m * x * m⁻¹ * m := by group
        _ = x⁻¹ * m := by rw [h]
    have hxinv : x⁻¹ = x * x := inv_eq_of_mul_eq_one_left hfpf.cube3
    have h1 : x * m * x⁻¹ = m * x := by
      calc x * m * x⁻¹ = x * m * (x * x) := by rw [hxinv]
        _ = x * (m * x) * x := by group
        _ = x * (x⁻¹ * m) * x := by rw [hmx]
        _ = m * x := by group
    have h2 : x * m * x⁻¹ ∈ pCoreOf 2 L := hfpf.conj_mem m hmV
    rw [h1] at h2
    have hxV : x ∈ pCoreOf 2 L := by
      have := (pCoreOf 2 L).mul_mem ((pCoreOf 2 L).inv_mem hmV) h2
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hV.sq x hxV)
    rw [hx3] at hd
    norm_num at hd

omit [Finite G] in
theorem mem_pCoreOf_of_mem_centralizerModO2_of_lie
    {L : Subgroup G} (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 2) {g : G} (hgL : g ∈ L)
    (hgC : g ∈ centralizerModO2 L) : g ∈ pCoreOf 2 L := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hlie
  have hmemN : ∀ a : ↥L, a ∈ CFSG.pCore 2 ↥L ↔ (a : G) ∈ pCoreOf 2 L := by
    intro a
    constructor
    · intro ha
      exact ⟨a, ha, rfl⟩
    · rintro ⟨b, hb, hba⟩
      have : b = a := Subtype.ext hba
      rwa [← this]
  have hVN : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hcen : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨g, hgL⟩ ∈
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) q
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      hmemN]
    have hc := commutator_mem_pCoreOf_of_centralizerModO2 hgC l.2
    have hk : g⁻¹ * (l : G)⁻¹ ∈ L := L.mul_mem (L.inv_mem hgL) (L.inv_mem l.2)
    have h1 := (Subgroup.mem_normalizer_iff.mp (hVN hk) _).mp hc
    have e : (((l * ⟨g, hgL⟩)⁻¹ * (⟨g, hgL⟩ * l) : ↥L) : G) =
        g⁻¹ * (l : G)⁻¹ * (g * l * g⁻¹ * (l : G)⁻¹) * (g⁻¹ * (l : G)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h1
  have hcen' : e (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨g, hgL⟩) ∈
      Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro a
    have h1 := congrArg e (hcen (e.symm a))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hcen'
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨g, hgL⟩ = 1 := by
    have := congrArg e.symm hcen'
    rwa [MulEquiv.symm_apply_apply, map_one] at this
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact (hmemN _).mp h1

omit [Finite G] in
theorem eq_one_of_isPGroup_two_three {A B : Subgroup G} (hA : IsPGroup 2 A) (hB : IsPGroup 3 B)
    {g : G} (hgA : g ∈ A) (hgB : g ∈ B) : g = 1 := by
  obtain ⟨a, ha⟩ := hA ⟨g, hgA⟩
  obtain ⟨b, hb⟩ := hB ⟨g, hgB⟩
  have h1 : orderOf g ∣ 2 ^ a :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val ha)
  have h2 : orderOf g ∣ 3 ^ b :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hb)
  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) := Nat.Coprime.pow a b (by norm_num)
  have hc : Nat.Coprime (orderOf g) (orderOf g) := (hcop.coprime_dvd_left h1).coprime_dvd_right h2
  rw [Nat.coprime_self] at hc
  exact orderOf_eq_one_iff.mp hc

theorem card_eq_three_of_isSylowIn {M L : Subgroup G}
    (hV : IsVFacts M L) (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 2)
    (hcard : ∀ z ∈ M ⊓ centralizerModO2 L, orderOf z = 3 →
      Nat.card (Subgroup.centralizer ({z} : Set G)) = 36 ∨
        Nat.card (Subgroup.centralizer ({z} : Set G)) = 180)
    {X : Subgroup G} (hX : CFSG.Quasithin.IsSylowIn 3 X (M ⊓ centralizerModO2 L)) {x : G}
    (hx : x ∈ M ⊓ centralizerModO2 L) (hx3 : orderOf x = 3) : Nat.card X = 3 := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := M ⊓ centralizerModO2 L with hCdef
  have hXC := hX.le
  have h3C : 3 ∣ Nat.card C := by
    have := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)
    rwa [Nat.card_zpowers, hx3] at this
  have hrel : Nat.card X * X.relIndex C = Nat.card C := by
    have h1 := Subgroup.card_mul_index (X.subgroupOf C)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv] at h1
  have h3X : 3 ∣ Nat.card X := by
    rw [← hrel] at h3C
    exact ((Nat.Prime.dvd_mul Nat.prime_three).mp h3C).resolve_right hX.not_dvd_relIndex
  have hXp : IsPGroup 3 X := hX.isPGroup
  have hntX : Nontrivial X := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Nat.le_of_dvd Nat.card_pos h3X
    omega
  have hZ := hXp.center_nontrivial
  have hZp : IsPGroup 3 (Subgroup.center ↥X) := hXp.to_subgroup _
  obtain ⟨k, hk, hZcard⟩ := hZp.nontrivial_iff_card.mp hZ
  have h3Z : 3 ∣ Nat.card (Subgroup.center ↥X) := by
    rw [hZcard]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3Z
  have hz3 : orderOf ((z : ↥X) : G) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  have hzX : ((z : ↥X) : G) ∈ X := (z : ↥X).2
  have hzC := hXC hzX
  obtain ⟨hzM, hzC'⟩ := Subgroup.mem_inf.mp hzC
  have hXz : X ≤ Subgroup.centralizer ({((z : ↥X) : G)} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨g, hg⟩)
  have hCz := hcard _ hzC hz3
  have hCL := card_centralizer_inf_L hV hzM hzC' hz3
  have hdisj : Disjoint (L ⊓ Subgroup.centralizer ({((z : ↥X) : G)} : Set G)) X := by
    rw [Subgroup.disjoint_def]
    intro g hgCL hgX
    have hgL : g ∈ L := (Subgroup.mem_inf.mp hgCL).1
    have hgV : g ∈ pCoreOf 2 L :=
      mem_pCoreOf_of_mem_centralizerModO2_of_lie hlie hgL (Subgroup.mem_inf.mp (hXC hgX)).2
    exact eq_one_of_isPGroup_two_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hXp hgV hgX
  have hXN : X ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer ({((z : ↥X) : G)} : Set G) : Subgroup G) : Set G) := by
    intro g hg
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hV.normal (Subgroup.mem_inf.mp (hXC hg)).1,
      Subgroup.le_normalizer (hXz hg)⟩
  have hsup := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (L ⊓ Subgroup.centralizer ({((z : ↥X) : G)} : Set G)) X hXN hdisj
  have hle : L ⊓ Subgroup.centralizer ({((z : ↥X) : G)} : Set G) ⊔ X ≤
      Subgroup.centralizer ({((z : ↥X) : G)} : Set G) := sup_le inf_le_right hXz
  have hd := Subgroup.card_dvd_of_le hle
  rw [hsup, hCL] at hd
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hX3 : Nat.card X ∣ 3 := by
    rcases hCz with h | h
    · exfalso
      rw [h] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    · rw [h, show (180 : ℕ) = 60 * 3 by norm_num] at hd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd
  exact Nat.dvd_antisymm hX3 h3X

theorem exists_conj_mem_of_isSylowIn {C X : Subgroup G} (hX : CFSG.Quasithin.IsSylowIn 3 X C)
    {x : G} (hxC : x ∈ C) (hx3 : orderOf x = 3) : ∃ c ∈ C, c * x * c⁻¹ ∈ X := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x' : ↥C := ⟨x, hxC⟩
  have hx'3 : orderOf x' = 3 := by rw [← Subgroup.orderOf_coe]; exact hx3
  have hP : IsPGroup 3 (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'3, pow_one])
  obtain ⟨S0, hS0⟩ := hP.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C S0 hX.toSylow
  have h1 : c * x' * c⁻¹ ∈ ((c • S0 : Sylow 3 ↥C) : Subgroup ↥C) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x', hS0 (Subgroup.mem_zpowers x'), rfl⟩
  rw [hc, CFSG.Quasithin.IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at h1
  exact ⟨c, c.2, h1⟩

theorem stmt5_2_15_of
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four) :
    Stmt5_2_15 := by
  intro G _ _ T M L V H B D L₂ n M2 π hyp hM23 hS X hX
  obtain ⟨hn2, -, -, -, -⟩ := setting_K_facts h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  subst hn2
  obtain ⟨x, hxC, hx3, hCM, hC180, r, hrM, hr⟩ :=
    exists_x_of_setting h526 h527 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS
  have hV := isVFacts_of_setting h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hX3 := card_eq_three_of_isSylowIn hV hyp.lie (fun z hz hz3 =>
    card_centralizer_of_mem_centralizerModO2 h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS hV
      (Subgroup.mem_inf.mp hz).1 (Subgroup.mem_inf.mp hz).2 hz3) hX hxC hx3
  obtain ⟨c, hcC, hcX⟩ := exists_conj_mem_of_isSylowIn hX hxC hx3
  have hcM : c ∈ M := (Subgroup.mem_inf.mp hcC).1
  have hx'3 : orderOf (c * x * c⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx3
  have hXeq : X = Subgroup.zpowers (c * x * c⁻¹) :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcX)
      (by rw [hX3, Nat.card_zpowers, hx'3])).symm
  have hx'C : c * x * c⁻¹ ∈ M ⊓ centralizerModO2 L :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hcC hxC) (Subgroup.inv_mem _ hcC)
  have hCM' : Subgroup.centralizer ({c * x * c⁻¹} : Set G) ≤ M := by
    intro g hg
    have hg' : c⁻¹ * g * c ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      calc c⁻¹ * g * c * x = c⁻¹ * (g * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * g) * c := by rw [hg]
        _ = x * (c⁻¹ * g * c) := by group
    have e : g = c * (c⁻¹ * g * c) * c⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hcM (hCM hg')) (M.inv_mem hcM)
  have hC180' : Nat.card (Subgroup.centralizer ({c * x * c⁻¹} : Set G)) = 180 := by
    rw [card_centralizer_conj]
    exact hC180
  have hr' : (c * r * c⁻¹) * (c * x * c⁻¹) * (c * r * c⁻¹)⁻¹ = (c * x * c⁻¹)⁻¹ := by
    calc (c * r * c⁻¹) * (c * x * c⁻¹) * (c * r * c⁻¹)⁻¹ = c * (r * x * r⁻¹) * c⁻¹ := by group
      _ = (c * x * c⁻¹)⁻¹ := by rw [hr]; group
  have hr'M : c * r * c⁻¹ ∈ M := M.mul_mem (M.mul_mem hcM hrM) (M.inv_mem hcM)
  obtain ⟨hNM, hiso⟩ := normalizer_le_and_gammaL2_of hV (Subgroup.mem_inf.mp hx'C).1
    (Subgroup.mem_inf.mp hx'C).2 hx'3 hCM' hC180' hr'M hr'
  rw [hXeq]
  exact ⟨hNM, F4, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, F4.card], hiso⟩

end CFSG.Quasithin.H13
