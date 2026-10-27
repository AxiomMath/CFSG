module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerB
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverCore
public import CFSG.GH74.GLS.Stage2.Local.P34Sp4Max
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915K2a
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413StrAux1

public noncomputable section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag Subgroup
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

private theorem commutator_eq_bot_of_le_centralizer_of_perfect
    {H : Type*} [Group H] {A Q : Subgroup H} (hQ : ⁅Q, Q⁆ = Q)
    (h : ⁅A, Q⁆ ≤ Subgroup.centralizer (Q : Set H)) : ⁅A, Q⁆ = ⊥ := by
  have hfirst : ⁅⁅A, Q⁆, Q⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h
  have hsecond : ⁅⁅Q, A⁆, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_comm Q A]; exact hfirst
  have hrot : ⁅⁅Q, Q⁆, A⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hsecond hfirst
  rw [hQ, ← Subgroup.commutator_comm A Q] at hrot
  exact hrot

private theorem a1413StrSwapProj_mem_centralizer_u1 (h2 : (2 : K) ≠ 0) :
    a1413StrSwapProj (K := K) ∈
      centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))) := by
  have hsu1 : a1413StrSwapProj (K := K) * u1 K * (a1413StrSwapProj (K := K))⁻¹ ∈ E2 K := by
    have h1 : a1413StrSwapProj (K := K) * u1 K * (a1413StrSwapProj (K := K))⁻¹ ∈
        (E1 K).map (MulAut.conj (a1413StrSwapProj (K := K))).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨u1 K, u1_mem_E1, rfl⟩
    rwa [a1413StrConjSwap_E1] at h1
  have hcent : ∀ y ∈ E2 K,
      (a1413StrSwapProj (K := K) * u1 K * (a1413StrSwapProj (K := K))⁻¹) * y =
        y * (a1413StrSwapProj (K := K) * u1 K * (a1413StrSwapProj (K := K))⁻¹) := by
    intro y hy
    have hy' : y ∈ (E1 K).map (MulAut.conj (a1413StrSwapProj (K := K))).toMonoidHom := by
      rwa [a1413StrConjSwap_E1]
    obtain ⟨e, he, rfl⟩ := hy'
    have heu : u1 K * e = e * u1 K :=
      (mem_centralizer_singleton_iff.mp (X0_le_centralizer (E1_le_X0 h2 he))).symm
    calc (a1413StrSwapProj (K := K) * u1 K * (a1413StrSwapProj (K := K))⁻¹) *
          (a1413StrSwapProj (K := K) * e * (a1413StrSwapProj (K := K))⁻¹)
        = a1413StrSwapProj (K := K) * (u1 K * e) * (a1413StrSwapProj (K := K))⁻¹ := by group
      _ = a1413StrSwapProj (K := K) * (e * u1 K) * (a1413StrSwapProj (K := K))⁻¹ := by
            rw [heu]
      _ = (a1413StrSwapProj (K := K) * e * (a1413StrSwapProj (K := K))⁻¹) *
          (a1413StrSwapProj (K := K) * u1 K * (a1413StrSwapProj (K := K))⁻¹) := by group
  rcases a1413Str_eq_one_or_u1_of_central_E2 h2 hsu1 hcent with h | h
  · exfalso
    have h1 : u1 K = 1 := by
      calc u1 K = (a1413StrSwapProj (K := K))⁻¹ *
            (a1413StrSwapProj (K := K) * u1 K * (a1413StrSwapProj (K := K))⁻¹) *
            a1413StrSwapProj (K := K) := by group
        _ = (a1413StrSwapProj (K := K))⁻¹ * 1 * a1413StrSwapProj (K := K) := by rw [h]
        _ = 1 := by group
    exact u1_ne_one h2 h1
  · rw [mem_centralizer_singleton_iff]
    calc a1413StrSwapProj (K := K) * u1 K
        = (a1413StrSwapProj (K := K) * u1 K * (a1413StrSwapProj (K := K))⁻¹) *
            a1413StrSwapProj (K := K) := by group
      _ = u1 K * a1413StrSwapProj (K := K) := by rw [h]

private theorem psp4_u1_derived_le_of_normalized (hodd : Odd (Nat.card K))
    (h7 : 7 ≤ Nat.card K)
    (N : Subgroup (StatedProj (StatedSp 2 K)))
    (hNC : N ≤ centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))))
    (hN : ∀ c ∈ centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))), ∀ n ∈ N,
      c * n * c⁻¹ ∈ N)
    (hu1N : u1 K ∈ N) (hNne : ¬ N ≤ zpowers (u1 K)) :
    X0 K ≤ N := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  let Cu : Subgroup (StatedProj (StatedSp 2 K)) :=
    centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))
  let M : Subgroup (StatedProj (StatedSp 2 K)) := N ⊓ X0 K
  have hMCu : M ≤ Cu := fun m hm => X0_le_centralizer (Subgroup.mem_inf.mp hm).2
  have hMc : ∀ c ∈ Cu, ∀ m ∈ M, c * m * c⁻¹ ∈ M := by
    intro c hc m hm
    obtain ⟨hmN, hmX⟩ := Subgroup.mem_inf.mp hm
    exact Subgroup.mem_inf.mpr
      ⟨hN c hc m hmN, conj_mem_map_centralizer (T1 K) hc hmX⟩
  have hMne : ¬ M ≤ zpowers (u1 K) := by
    intro hMle
    have hNX : ⁅N, X0 K⁆ ≤ N ⊓ X0 K := by
      rw [Subgroup.commutator_le]
      intro n hn x hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hxN : x * n⁻¹ * x⁻¹ ∈ N := hN x (X0_le_centralizer hx) n⁻¹ (N.inv_mem hn)
        rw [commutatorElement_def]
        have := N.mul_mem hn hxN
        simpa only [mul_assoc] using this
      · have hnC : n ∈ Cu := hNC hn
        have hconj : n * x * n⁻¹ ∈ X0 K := conj_mem_map_centralizer (T1 K) hnC hx
        rw [commutatorElement_def]
        exact (X0 K).mul_mem hconj ((X0 K).inv_mem hx)
    have hcomm : ⁅N, X0 K⁆ ≤ zpowers (u1 K) := hNX.trans hMle
    have hcent : ⁅N, X0 K⁆ ≤ Subgroup.centralizer (X0 K : Set (StatedProj (StatedSp 2 K))) := by
      refine hcomm.trans ?_
      rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact mem_centralizer_singleton_iff.mp (X0_le_centralizer hx)
    have hbot : ⁅N, X0 K⁆ = ⊥ :=
      commutator_eq_bot_of_le_centralizer_of_perfect (a1413StrPerfect_X0 h2 h4) hcent
    have hNle : N ≤ Subgroup.centralizer (X0 K : Set (StatedProj (StatedSp 2 K))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    rw [a1413StrCentralizer_X0 h2 h4] at hNle
    exact hNne hNle
  have hN1 : ((M ⊓ E1 K).subgroupOf (E1 K)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    exact Subgroup.mem_inf.mpr
      ⟨hMc k (E1_le_centralizer_u1 h2 hk) h (Subgroup.mem_inf.mp hh).1,
        (E1 K).mul_mem ((E1 K).mul_mem hk (Subgroup.mem_inf.mp hh).2) ((E1 K).inv_mem hk)⟩
  have hN2 : ((M ⊓ E2 K).subgroupOf (E2 K)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    exact Subgroup.mem_inf.mpr
      ⟨hMc k (E2_le_centralizer_u1 h2 hk) h (Subgroup.mem_inf.mp hh).1,
        (E2 K).mul_mem ((E2 K).mul_mem hk (Subgroup.mem_inf.mp hh).2) ((E2 K).inv_mem hk)⟩
  have hMsCu : a1413StrSwapProj (K := K) ∈ Cu := a1413StrSwapProj_mem_centralizer_u1 h2
  have hMs : M.map (MulAut.conj (a1413StrSwapProj (K := K))).toMonoidHom = M := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨m, hm, rfl⟩
      exact hMc (a1413StrSwapProj (K := K)) hMsCu m hm
    · intro x hx
      refine ⟨(a1413StrSwapProj (K := K))⁻¹ * x * a1413StrSwapProj (K := K), ?_, ?_⟩
      · exact hMc ((a1413StrSwapProj (K := K))⁻¹) (Cu.inv_mem hMsCu) x hx
      · change a1413StrSwapProj (K := K) *
            ((a1413StrSwapProj (K := K))⁻¹ * x * a1413StrSwapProj (K := K)) *
            (a1413StrSwapProj (K := K))⁻¹ = x
        group
  rcases quasisimple_normal_subgroups (Q := E1 K) (isQuasisimple_E1 h2 h4) hN1 with h1top | h1cen
  · have hE1le : E1 K ≤ M := by
      intro e he
      have hmem : (⟨e, he⟩ : E1 K) ∈ (M ⊓ E1 K).subgroupOf (E1 K) := h1top ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hmem).1
    have hE2le : E2 K ≤ M := by
      have hmap := Subgroup.map_mono hE1le
        (f := (MulAut.conj (a1413StrSwapProj (K := K))).toMonoidHom)
      rwa [a1413StrConjSwap_E1, hMs] at hmap
    have : X0 K ≤ M := by
      rw [a1413StrX0_eq_sup h2]; exact sup_le hE1le hE2le
    exact this.trans inf_le_left
  · rcases quasisimple_normal_subgroups (Q := E2 K) (isQuasisimple_E2 h2 h4) hN2 with h2top | h2cen
    · have hE2le : E2 K ≤ M := by
        intro e he
        have hmem : (⟨e, he⟩ : E2 K) ∈ (M ⊓ E2 K).subgroupOf (E2 K) := h2top ▸ Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp hmem).1
      have hE1le : E1 K ≤ M := by
        have hmap := Subgroup.map_mono hE2le
          (f := (MulAut.conj (a1413StrSwapProj (K := K))).toMonoidHom)
        rwa [a1413StrConjSwap_E2, hMs] at hmap
      have : X0 K ≤ M := by
        rw [a1413StrX0_eq_sup h2]; exact sup_le hE1le hE2le
      exact this.trans inf_le_left
    · have hcent1 : ⁅M, E1 K⁆ ≤ Subgroup.centralizer (E1 K : Set (StatedProj (StatedSp 2 K))) := by
        rw [Subgroup.commutator_le]
        intro m hm e he
        have hmemM : ⁅m, e⁆ ∈ M := by
          have heM : e * m⁻¹ * e⁻¹ ∈ M :=
            hMc e (E1_le_centralizer_u1 h2 he) m⁻¹ (M.inv_mem hm)
          rw [commutatorElement_def]
          have := M.mul_mem hm heM
          simpa only [mul_assoc] using this
        have hmemE1 : ⁅m, e⁆ ∈ E1 K := by
          have hconj : m * e * m⁻¹ ∈ E1 K := conj_mem_E1 h2 (Subgroup.mem_inf.mp hm).2 he
          rw [commutatorElement_def]
          exact (E1 K).mul_mem hconj ((E1 K).inv_mem he)
        have hmem : (⟨⁅m, e⁆, hmemE1⟩ : E1 K) ∈ (M ⊓ E1 K).subgroupOf (E1 K) :=
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hmemM, hmemE1⟩)
        have hc : (⟨⁅m, e⁆, hmemE1⟩ : E1 K) ∈ Subgroup.center (E1 K) := h1cen hmem
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc) ⟨y, hy⟩)
      have hcent2 : ⁅M, E2 K⁆ ≤ Subgroup.centralizer (E2 K : Set (StatedProj (StatedSp 2 K))) := by
        rw [Subgroup.commutator_le]
        intro m hm e he
        have hmemM : ⁅m, e⁆ ∈ M := by
          have heM : e * m⁻¹ * e⁻¹ ∈ M :=
            hMc e (E2_le_centralizer_u1 h2 he) m⁻¹ (M.inv_mem hm)
          rw [commutatorElement_def]
          have := M.mul_mem hm heM
          simpa only [mul_assoc] using this
        have hmemE2 : ⁅m, e⁆ ∈ E2 K := by
          have hconj : m * e * m⁻¹ ∈ E2 K := conj_mem_E2 h2 (Subgroup.mem_inf.mp hm).2 he
          rw [commutatorElement_def]
          exact (E2 K).mul_mem hconj ((E2 K).inv_mem he)
        have hmem : (⟨⁅m, e⁆, hmemE2⟩ : E2 K) ∈ (M ⊓ E2 K).subgroupOf (E2 K) :=
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hmemM, hmemE2⟩)
        have hc : (⟨⁅m, e⁆, hmemE2⟩ : E2 K) ∈ Subgroup.center (E2 K) := h2cen hmem
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc) ⟨y, hy⟩)
      have hMcent1 : M ≤ Subgroup.centralizer (E1 K : Set (StatedProj (StatedSp 2 K))) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact commutator_eq_bot_of_le_centralizer_of_perfect
          (Subgroup.isPerfect_iff.mp (isQuasisimple_E1 h2 h4).1) hcent1
      have hMcent2 : M ≤ Subgroup.centralizer (E2 K : Set (StatedProj (StatedSp 2 K))) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact commutator_eq_bot_of_le_centralizer_of_perfect
          (Subgroup.isPerfect_iff.mp (isQuasisimple_E2 h2 h4).1) hcent2
      have hMle : M ≤ zpowers (u1 K) := by
        have hMcentX : M ≤ Subgroup.centralizer (X0 K : Set (StatedProj (StatedSp 2 K))) := by
          intro m hm
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_X0 h2 hx
          have hm1 : a * m = m * a := Subgroup.mem_centralizer_iff.mp (hMcent1 hm) a ha
          have hm2 : b * m = m * b := Subgroup.mem_centralizer_iff.mp (hMcent2 hm) b hb
          calc (a * b) * m = a * (b * m) := by group
            _ = a * (m * b) := by rw [hm2]
            _ = (a * m) * b := by group
            _ = (m * a) * b := by rw [hm1]
            _ = m * (a * b) := by group
        rwa [a1413StrCentralizer_X0 h2 h4] at hMcentX
      exact absurd hMle hMne

theorem psp4_derived_le_of_normalized (hodd : Odd (Nat.card K)) (h7 : 7 ≤ Nat.card K)
    {z : StatedProj (StatedSp 2 K)} (hz : IsConj (u1 K) z)
    (N : Subgroup (StatedProj (StatedSp 2 K)))
    (hNC : N ≤ centralizer ({z} : Set (StatedProj (StatedSp 2 K))))
    (hN : ∀ c ∈ centralizer ({z} : Set (StatedProj (StatedSp 2 K))), ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hzN : z ∈ N) (hNz : ¬ N ≤ zpowers z) :
    ⁅centralizer ({z} : Set (StatedProj (StatedSp 2 K))),
        centralizer ({z} : Set (StatedProj (StatedSp 2 K)))⁆ ≤ N := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  obtain ⟨r, hr⟩ := isConj_iff.mp hz
  let φ : MulAut (StatedProj (StatedSp 2 K)) := MulAut.conj r
  have hφ : φ (u1 K) = z := by
    change MulAut.conj r (u1 K) = z
    rw [MulAut.conj_apply]; exact hr
  have hCu : (centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))).map φ.toMonoidHom =
      centralizer ({z} : Set (StatedProj (StatedSp 2 K))) := by
    rw [a1413StrMapCentralizerSingleton φ (u1 K), hφ]
  have hXz : ⁅centralizer ({z} : Set (StatedProj (StatedSp 2 K))),
      centralizer ({z} : Set (StatedProj (StatedSp 2 K)))⁆ =
      (X0 K).map φ.toMonoidHom := by
    rw [← hCu, ← Subgroup.map_commutator, a1413StrCommutator_C_eq_X0 h2 h4]
  let N' : Subgroup (StatedProj (StatedSp 2 K)) := N.map φ.symm.toMonoidHom
  have hNmap : N'.map φ.toMonoidHom = N := by
    show (N.map φ.symm.toMonoidHom).map φ.toMonoidHom = N
    rw [Subgroup.map_map]
    rw [show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ from
      MonoidHom.ext (fun x => by simp)]
    exact Subgroup.map_id N
  have hNC' : N' ≤ centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))) := by
    intro n hn
    obtain ⟨n₀, hn₀, rfl⟩ := Subgroup.mem_map.mp hn
    have hn₀C : n₀ ∈ centralizer ({z} : Set (StatedProj (StatedSp 2 K))) := hNC hn₀
    have : n₀ ∈ (centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))).map φ.toMonoidHom := by
      rw [hCu]; exact hn₀C
    obtain ⟨c, hc, hcφ⟩ := Subgroup.mem_map.mp this
    rw [← hcφ]; simpa using hc
  have hN'' : ∀ c ∈ centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))), ∀ n ∈ N',
      c * n * c⁻¹ ∈ N' := by
    intro c hc n hn
    obtain ⟨n₀, hn₀, rfl⟩ := Subgroup.mem_map.mp hn
    have hcφ : φ c ∈ centralizer ({z} : Set (StatedProj (StatedSp 2 K))) := by
      rw [← hCu]; exact Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
    have hmem : φ c * n₀ * (φ c)⁻¹ ∈ N := hN (φ c) hcφ n₀ hn₀
    refine Subgroup.mem_map.mpr ⟨φ c * n₀ * (φ c)⁻¹, hmem, ?_⟩
    rw [map_mul, map_mul, map_inv]
    simp
  have hu1N' : u1 K ∈ N' := by
    refine Subgroup.mem_map.mpr ⟨z, hzN, ?_⟩
    rw [← hφ]; simp
  have hNne' : ¬ N' ≤ zpowers (u1 K) := by
    intro hle
    apply hNz
    have hmap := Subgroup.map_mono hle (f := φ.toMonoidHom)
    rw [hNmap, MonoidHom.map_zpowers] at hmap
    change N ≤ zpowers (φ (u1 K)) at hmap
    rwa [hφ] at hmap
  have hbase : X0 K ≤ N' := psp4_u1_derived_le_of_normalized hodd h7 N' hNC' hN'' hu1N' hNne'
  rw [hXz]
  calc (X0 K).map φ.toMonoidHom ≤ N'.map φ.toMonoidHom := Subgroup.map_mono hbase
    _ = N := hNmap

private theorem eq_u1_of_mem_X0_of_conj (hodd : Odd (Nat.card K))
    {x : StatedProj (StatedSp 2 K)} (hx : x ∈ X0 K)
    (hconj : ∃ g, g⁻¹ * x * g = u1 K) : x = u1 K := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hx1 : x ≠ 1 := by
    rintro rfl
    obtain ⟨g, hg⟩ := hconj
    exact u1_ne_one h2 (by rw [← hg]; simp)
  obtain ⟨A, hAproj, hAsq⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm2.L915.k2a_exists_lift_sq_one hconj
  obtain ⟨⟨p, q⟩, hpq⟩ := (mem_X0 h2).mp hx
  set B : StatedSp 2 K := blkSL K (p, q) with hBdef
  have hBproj : proj 2 K B = x := hpq
  have hBsq : B * B = 1 := by
    rcases eq_or_eq_neg_of_proj_eq (a := A) (b := B) (by rw [hAproj, hBproj]) with h | h
    · have hAB : B = A := sp_ext h
      rw [hAB]; exact hAsq
    · have hA' : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
        have := congrArg (fun y : StatedSp 2 K =>
          ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hAsq
        simpa using this
      refine sp_ext ?_
      rw [Subgroup.coe_mul, Units.val_mul, h, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
      simpa using hA'
  have hBT : B * T1 K = T1 K * B :=
    mem_centralizer_singleton_iff.mp ((mem_centralizer_T1_iff h2).mpr ⟨(p, q), rfl⟩)
  have hprojNegS : proj 2 K (negS (K := K)) = 1 := by
    rw [← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff]
    exact Or.inr (coe_negS)
  rcases eq_of_commute_T1 h2 hBsq hBT with h | h | h | h
  · exact absurd (by rw [← hBproj, h, map_one]) hx1
  · exact absurd (by rw [← hBproj, h, hprojNegS]) hx1
  · rw [← hBproj, h]
    rfl
  · rw [← hBproj, h, map_mul, hprojNegS, one_mul]
    rfl

private theorem psp4_u1_sup_conj_derived_eq_top (hodd : Odd (Nat.card K))
    (h7 : 7 ≤ Nat.card K) (h : StatedProj (StatedSp 2 K))
    (hne : h * u1 K * h⁻¹ ≠ u1 K)
    (hcomm : (h * u1 K * h⁻¹) * u1 K = u1 K * (h * u1 K * h⁻¹)) :
    X0 K ⊔ (X0 K).map (MulAut.conj h).toMonoidHom = ⊤ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  let Cu : Subgroup (StatedProj (StatedSp 2 K)) :=
    centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))
  let z' : StatedProj (StatedSp 2 K) := h * u1 K * h⁻¹
  have hz'Cu : z' ∈ Cu := mem_centralizer_singleton_iff.mpr hcomm
  have hz'Xh : z' ∈ (X0 K).map (MulAut.conj h).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨u1 K, (E1_le_X0 h2) u1_mem_E1, rfl⟩
  have hz'notX : z' ∉ X0 K := by
    intro hmem
    refine hne (eq_u1_of_mem_X0_of_conj hodd hmem ?_)
    exact ⟨h, by change h⁻¹ * (h * u1 K * h⁻¹) * h = u1 K; group⟩
  have hnot_le : ¬ (X0 K).map (MulAut.conj h).toMonoidHom ≤ Cu := by
    intro hle
    have hmem : h⁻¹ * u1 K * h ∈
        Subgroup.centralizer (X0 K : Set (StatedProj (StatedSp 2 K))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : h * x * h⁻¹ ∈ Cu := hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      have hcommx : (h * x * h⁻¹) * u1 K = u1 K * (h * x * h⁻¹) :=
        mem_centralizer_singleton_iff.mp hx'
      calc x * (h⁻¹ * u1 K * h)
          = h⁻¹ * ((h * x * h⁻¹) * u1 K) * h := by group
        _ = h⁻¹ * (u1 K * (h * x * h⁻¹)) * h := by rw [hcommx]
        _ = (h⁻¹ * u1 K * h) * x := by group
    rw [a1413StrCentralizer_X0 h2 h4] at hmem
    have hx0 : h⁻¹ * u1 K * h ∈ X0 K :=
      Subgroup.zpowers_le.mpr ((E1_le_X0 h2) u1_mem_E1) hmem
    have heq : h⁻¹ * u1 K * h = u1 K :=
      eq_u1_of_mem_X0_of_conj hodd hx0 ⟨h⁻¹, by group⟩
    have hz'u1 : z' = u1 K := by
      calc z' = h * (h⁻¹ * u1 K * h) * h⁻¹ := by rw [heq]
        _ = u1 K := by group
    exact hne hz'u1
  have hCu_le_sup : Cu ≤ X0 K ⊔ Subgroup.zpowers z' := by
    obtain ⟨a, haCu, haX0, hall⟩ :=
      Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp (a1413StrRelIndex_X0_C h2)
    intro b hb
    rcases hall b hb with hab | hbX
    · rcases hall z' hz'Cu with haz | hz
      · have hx : (a * z')⁻¹ * (a * b) ∈ X0 K :=
          (X0 K).mul_mem ((X0 K).inv_mem haz) hab
        have hbz : b = z' * ((a * z')⁻¹ * (a * b)) := by group
        rw [hbz]
        exact (X0 K ⊔ Subgroup.zpowers z').mul_mem
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩))
          (Subgroup.mem_sup_left hx)
      · exact absurd hz hz'notX
    · exact Subgroup.mem_sup_left hbX
  have hCu_le : Cu ≤ X0 K ⊔ (X0 K).map (MulAut.conj h).toMonoidHom :=
    hCu_le_sup.trans (sup_le le_sup_left (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hz'Xh)))
  have hlt : Cu < X0 K ⊔ (X0 K).map (MulAut.conj h).toMonoidHom := by
    refine lt_of_le_of_ne hCu_le ?_
    intro heq
    exact hnot_le (le_sup_right.trans (le_of_eq heq.symm))
  exact (CFSG.GH74.GLS.Stage2.Local.P34.isCoatom_centralizer_u1 (F := K) hodd).2 _ hlt

theorem psp4_sup_conj_derived_eq_top (hodd : Odd (Nat.card K)) (h7 : 7 ≤ Nat.card K)
    {z : StatedProj (StatedSp 2 K)} (hz : IsConj (u1 K) z) (h : StatedProj (StatedSp 2 K))
    (hne : h * z * h⁻¹ ≠ z) (hcomm : (h * z * h⁻¹) * z = z * (h * z * h⁻¹)) :
    ⁅centralizer ({z} : Set (StatedProj (StatedSp 2 K))),
        centralizer ({z} : Set (StatedProj (StatedSp 2 K)))⁆ ⊔
      (⁅centralizer ({z} : Set (StatedProj (StatedSp 2 K))),
        centralizer ({z} : Set (StatedProj (StatedSp 2 K)))⁆).map
          (MulAut.conj h).toMonoidHom = ⊤ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  obtain ⟨r, hr⟩ := isConj_iff.mp hz
  let φ : MulAut (StatedProj (StatedSp 2 K)) := MulAut.conj r
  have hφ : φ (u1 K) = z := by
    change MulAut.conj r (u1 K) = z
    rw [MulAut.conj_apply]; exact hr
  have hCu : (centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))).map φ.toMonoidHom =
      centralizer ({z} : Set (StatedProj (StatedSp 2 K))) := by
    rw [a1413StrMapCentralizerSingleton φ (u1 K), hφ]
  have hX : ⁅centralizer ({z} : Set (StatedProj (StatedSp 2 K))),
      centralizer ({z} : Set (StatedProj (StatedSp 2 K)))⁆ = (X0 K).map φ.toMonoidHom := by
    rw [← hCu, ← Subgroup.map_commutator, a1413StrCommutator_C_eq_X0 h2 h4]
  let h' : StatedProj (StatedSp 2 K) := r⁻¹ * h * r
  have hφh' : φ h' = h := by
    change MulAut.conj r (r⁻¹ * h * r) = h
    rw [MulAut.conj_apply]; group
  have hne' : h' * u1 K * h'⁻¹ ≠ u1 K := by
    intro heq
    exact hne (by
      have := congrArg φ heq
      simpa only [map_mul, map_inv, hφh', hφ] using this)
  have hcomm' : (h' * u1 K * h'⁻¹) * u1 K = u1 K * (h' * u1 K * h'⁻¹) := by
    apply φ.injective
    simpa only [map_mul, map_inv, hφh', hφ] using hcomm
  have hsum : ((X0 K).map (MulAut.conj h').toMonoidHom).map φ.toMonoidHom =
      ((X0 K).map φ.toMonoidHom).map (MulAut.conj h).toMonoidHom := by
    simp only [Subgroup.map_map]
    rw [show φ.toMonoidHom.comp (MulAut.conj h').toMonoidHom =
        (MulAut.conj h).toMonoidHom.comp φ.toMonoidHom from
      MonoidHom.ext (fun x => by
        change r * ((r⁻¹ * h * r) * x * (r⁻¹ * h * r)⁻¹) * r⁻¹ =
          h * (r * x * r⁻¹) * h⁻¹
        group)]
  have hmain := psp4_u1_sup_conj_derived_eq_top hodd h7 h' hne' hcomm'
  have hmap : (X0 K).map φ.toMonoidHom ⊔
      ((X0 K).map φ.toMonoidHom).map (MulAut.conj h).toMonoidHom = ⊤ := by
    have := congrArg (Subgroup.map φ.toMonoidHom) hmain
    rwa [Subgroup.map_sup, Subgroup.map_top, MonoidHom.range_eq_top.mpr φ.surjective,
      hsum] at this
  rwa [hX]

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
