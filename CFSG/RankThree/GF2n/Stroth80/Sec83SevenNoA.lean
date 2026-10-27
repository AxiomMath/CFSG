module

public import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
public import CFSG.RankThree.GF2n.Stroth80.Sec83SevenReduce
public import CFSG.RankThree.GF2n.Stroth80.Sec8Inv
public import CFSG.RankThree.GF2n.Stroth80.Sec5PtsCore
public import CFSG.RankThree.GF2n.Stroth80.AddAutDescent
public import CFSG.RankThree.GF2n.Stroth80.Sec83UpperModule
public import CFSG.RankThree.GF2n.Stroth80.Sp4ModTrans

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_hypPlane_of_spMNat (h34 : Stroth34Statement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hsp : SpMNat hc t m) :
    ∃ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t := by
  classical
  obtain ⟨K, iK, iF, hK, φ, hφ, hker, hact⟩ := hsp
  letI := iK
  letI := iF
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  haveI := hn
  have ht : t ∈ LB M Q B := hs.mem
  have hnat : SpNat hc t :=
    ⟨K, inferInstance, inferInstance, hK, m, hm, φ, hφ, hker, hc.Rt_normalizes_Vt ht, hn, ψ, hψ⟩
  have hchi := stroth310Chi_of_34 h34 G M Q Z B hc n t hs (Or.inl hnat)
  have hnotQB := stroth310NotQB_of_34 h34 G M Q Z B hc n t hs (Or.inl hnat)
  have hperp := stroth310Perp_of_34 h34 G M Q Z B hc n t hs hnotQB
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  let D := hc.natCommData ht hchi.1 hchi.2
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨nn, γ, M₀, h, θ, hθ⟩ :=
    hc.exists_globalRingEquiv ht hK addCommutantScalar_statedSp φ hφ ψ hψ
  obtain ⟨b₀, hb₀B, hu0, hBiff⟩ := hc.exists_point_of_le hBV ψ h θ hθ
  set u := secVec ψ b₀ with hu
  have C' : ∀ (b : ↥(Vt M (LB M Q B) B Z t)), secVec ψ b ≠ 0 →
      ∀ x : Fin m ⊕ Fin m → K, pairVec D ψ b x = 1 ↔ spForm m K (secVec ψ b) x = 0 :=
    fun b hb x => hc.pairVec_eq_one_iff_spForm ht D φ hφ ψ hψ h θ hθ hb x
  obtain ⟨u', huu'⟩ : ∃ u' : Fin m ⊕ Fin m → K, spForm m K u u' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (spForm_nondegenerate.1 u hcon)
  have hu'0 : u' ≠ 0 := fun h0 => huu' (by rw [h0, map_zero])
  obtain ⟨r, hru⟩ := exists_mulVec_eq_of_range φ hφ (exists_statedSp_mulVec_eq hu0 hu'0)
  have hr0 : (r : G) * (b₀ : G) * (r : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hVR r.2) b₀).mp b₀.2
  set c₀ : ↥(Vt M (LB M Q B) B Z t) := ⟨(r : G) * b₀ * (r : G)⁻¹, hr0⟩ with hc₀
  have hc₀vec : secVec ψ c₀ = (φ r : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u :=
    hψ r b₀ c₀ rfl
  obtain ⟨y, hy⟩ := exists_kapVec D ψ (secVec ψ c₀)
  refine ⟨(r : G), r.2, (y : G), y.2, ?_, (b₀ : G), hb₀B, ?_⟩
  ·
    have h1 : ⁅(y : G), t⁆ * (c₀ : G)⁻¹ ∈ Z :=
      (secVec_eq_iff ψ ⟨⁅(y : G), t⁆, D.comm_t_mem y y.2⟩ c₀).mp hy
    have hc₀C : (c₀ : G) ∈ conjSubgroup (r : G) B := by
      rw [mem_conjSubgroup]
      show (r : G)⁻¹ * ((r : G) * (b₀ : G) * (r : G)⁻¹) * (r : G) ∈ B
      rw [show (r : G)⁻¹ * ((r : G) * (b₀ : G) * (r : G)⁻¹) * (r : G) = (b₀ : G) by group]
      exact hb₀B
    have e : ⁅(y : G), t⁆ = (⁅(y : G), t⁆ * (c₀ : G)⁻¹) * (c₀ : G) := by group
    rw [e]
    exact (conjSubgroup (r : G) B ⊔ Z).mul_mem (Subgroup.mem_sup_right h1)
      (Subgroup.mem_sup_left hc₀C)
  ·
    have hsp : spForm m K u ((φ r : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0 := by
      rw [hru]
      exact huu'
    have h2 : pairVec D ψ b₀ (secVec ψ c₀) ≠ 1 := fun h1 => by
      have h3 := (C' b₀ hu0 (secVec ψ c₀)).mp h1
      rw [hc₀vec] at h3
      exact hsp h3
    rwa [pairVec_eq D ψ b₀ y hy] at h2

theorem sec8Inv_of_sec8Pts (h53 : Stroth53Statement)
    (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t)
    (hrR : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    {K : Type} [Field K] [Finite K]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K} {u u' : Fin 2 ⊕ Fin 2 → K}
    (hpts : Sec8Pts hc t r 2 K φ u u') :
    ∀ ρ ∈ Rt M (LB M Q B) t,
      conjSubgroup ρ (Sec8V1 M Q Z B t r) = Sec8V1 M Q Z B t r ∧
      conjSubgroup ρ (Sec8W1 M Q Z B t r) = Sec8W1 M Q Z B t r := by
  have hsp : SpNat hc t := hpts.spNat
  have hb := h53.2.1 G M Q Z B hc n t hs hsp r hrR hplane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl
  have hcd := h53.2.2.1 G M Q Z B hc n t hs hsp r hrR hplane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  obtain ⟨hVA1, hA1W, -, -, -, -, -, -, -, -⟩ := hcd
  have hVW : Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r := hVA1.trans hA1W
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt hs.mem
  have hV1V : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r :=
    le_inf le_sup_right le_sup_right
  have hV1Q : Sec8V1 M Q Z B t r ≤ Q :=
    inf_le_left.trans (sup_le inf_le_left hVQ)
  have hRV : Rt M (LB M Q B) t ≤
      Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := hc.Rt_normalizes_Vt hs.mem
  have hQN : Q ≤ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := by
    refine sec8_le_normalizer_of_conj fun x hx y hy => ?_
    have hc' : ⁅x, y⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hx (hV1Q hy)
    rw [show x * y * x⁻¹ = ⁅x, y⁆ * y by rw [commutatorElement_def]; group]
    exact (Sec8V1 M Q Z B t r).mul_mem (hV1V (sec39_Z_le_Vt hc')) hy
  have hBN : QB B ⊓ M ≤ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := by
    refine sec8_le_normalizer_of_conj fun g hg y hy => ?_
    have hgR : g ∈ Rt M (LB M Q B) t :=
      le_Rt (LB M Q B) hs.mem (Subgroup.mem_sup_right hg)
    exact sec8_conj_mem_of_QB hc hBV hVQ hZV hV1V hg.1 (hRV hgR) hy.1 hy
  have hCN : QB (conjSubgroup r B) ⊓ M ≤
      Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := by
    refine sec8_le_normalizer_of_conj fun g hg y hy => ?_
    have hgR : g ∈ Rt M (LB M Q B) t :=
      hc.LB_conj_le_Rt_of_mem hs.mem hrR (Subgroup.mem_sup_right hg)
    have hCV : conjSubgroup r B ≤ Vt M (LB M Q B) B Z t := by
      intro x hx
      rw [mem_conjSubgroup] at hx
      have h1 := (Subgroup.mem_normalizer_iff.mp (hRV hrR) (r⁻¹ * x * r)).mp (hBV hx)
      rwa [show r * (r⁻¹ * x * r) * r⁻¹ = x by group] at h1
    exact sec8_conj_mem_of_QB (hc.conj_of_mem (hc.Rt_le_M t hrR)) hCV hVQ hZV hV1V
      hg.1 (hRV hgR) hy.2 hy
  have hLB : LB M Q B ≤ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) :=
    sup_le hQN hBN
  have hLC : LB M Q (conjSubgroup r B) ≤
      Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := sup_le hQN hCN
  have hNN : hc.CN t ≤ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := by
    refine sec8_le_normalizer_of_conj fun x hx y hy => ?_
    have hxy : ⁅x, y⁆ ∈ Sec8V1 M Q Z B t r := hb.2 x hx y (hVW hy)
    rw [show x * y * x⁻¹ = ⁅x, y⁆ * y by rw [commutatorElement_def]; group]
    exact (Sec8V1 M Q Z B t r).mul_mem hxy hy
  have hRN : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := by
    have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
        LspGL 2 K u' := by
      rw [hc.LB_conj (hc.Rt_le_M t hrR)]
      exact hpts.hL'
    have hle : Rt M (LB M Q B) t ≤
        hc.CN t ⊔ (LB M Q B ⊔ LB M Q (conjSubgroup r B)) :=
      le_sup_secSp (m := 2) (R := Rt M (LB M Q B) t) (N := hc.CN t)
        (L₁ := LB M Q B) (L₂ := LB M Q (conjSubgroup r B)) φ hpts.range hpts.ker
        hpts.uu' hpts.hL hL2
    exact hle.trans (sup_le hNN (sup_le hLB hLC))
  have hQNQ : Q ≤ Subgroup.normalizer (Q : Set G) :=
    fun x hx => hc.hyp.Q_normal.2 (hc.hyp.Q_normal.1 hx)
  have hLBNQ : LB M Q B ≤ Subgroup.normalizer (Q : Set G) :=
    fun x hx => hc.hyp.Q_normal.2 (hc.LB_le_M hx)
  have hLCNQ : LB M Q (conjSubgroup r B) ≤ Subgroup.normalizer (Q : Set G) :=
    fun x hx => hc.hyp.Q_normal.2 (sup_le hc.hyp.Q_normal.1 inf_le_right hx)
  have hNNQ : hc.CN t ≤ Subgroup.normalizer (Q : Set G) :=
    fun x hx => hc.hyp.Q_normal.2 (hc.Rt_le_M t (Ctx.mem_CN.mp hx).1)
  have hQW : Q ≤ Subgroup.normalizer (Sec8W1 M Q Z B t r : Set G) :=
    sec8_le_normalizer_of_conj fun x hx y hy =>
      (Subgroup.mem_normalizer_iff.mp (sec8_Wt_mem_normalizer (hQNQ hx) (hQN hx)) y).mp hy
  have hBW : QB B ⊓ M ≤ Subgroup.normalizer (Sec8W1 M Q Z B t r : Set G) :=
    sec8_le_normalizer_of_conj fun x hx y hy =>
      (Subgroup.mem_normalizer_iff.mp
        (sec8_Wt_mem_normalizer (hLBNQ (Subgroup.mem_sup_right hx))
          (hLB (Subgroup.mem_sup_right hx))) y).mp hy
  have hCW : QB (conjSubgroup r B) ⊓ M ≤
      Subgroup.normalizer (Sec8W1 M Q Z B t r : Set G) :=
    sec8_le_normalizer_of_conj fun x hx y hy =>
      (Subgroup.mem_normalizer_iff.mp
        (sec8_Wt_mem_normalizer (hLCNQ (Subgroup.mem_sup_right hx))
          (hLC (Subgroup.mem_sup_right hx))) y).mp hy
  have hNW : hc.CN t ≤ Subgroup.normalizer (Sec8W1 M Q Z B t r : Set G) := by
    refine sec8_le_normalizer_of_conj fun x hx y hy => ?_
    have hxy : ⁅x, y⁆ ∈ Sec8V1 M Q Z B t r := hb.2 x hx y hy
    rw [show x * y * x⁻¹ = ⁅x, y⁆ * y by rw [commutatorElement_def]; group]
    exact (Sec8W1 M Q Z B t r).mul_mem (hVW hxy) hy
  have hRW : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Sec8W1 M Q Z B t r : Set G) := by
    have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
        LspGL 2 K u' := by
      rw [hc.LB_conj (hc.Rt_le_M t hrR)]
      exact hpts.hL'
    have hle : Rt M (LB M Q B) t ≤
        hc.CN t ⊔ (LB M Q B ⊔ LB M Q (conjSubgroup r B)) :=
      le_sup_secSp (m := 2) (R := Rt M (LB M Q B) t) (N := hc.CN t)
        (L₁ := LB M Q B) (L₂ := LB M Q (conjSubgroup r B)) φ hpts.range hpts.ker
        hpts.uu' hpts.hL hL2
    exact hle.trans (sup_le hNW (sup_le (sup_le hQW hBW) (sup_le hQW hCW)))
  intro ρ hρ
  exact ⟨sec8_conjSubgroup_eq_of_mem_normalizer (hRN hρ),
    sec8_conjSubgroup_eq_of_mem_normalizer (hRW hρ)⟩

theorem sec83_count_A_of_sec8Pts (h53 : Stroth53Statement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K} {u u' : Fin m ⊕ Fin m → K}
    (hs : Sec5Hyp hc n t) (hrR : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (hinv : ∀ ρ ∈ Rt M (LB M Q B) t,
      conjSubgroup ρ (Sec8V1 M Q Z B t r) = Sec8V1 M Q Z B t r ∧
      conjSubgroup ρ (Sec8W1 M Q Z B t r) = Sec8W1 M Q Z B t r)
    (hpts : Sec8Pts hc t r m K φ u u') :
    ∃ a : ℕ, 2 * n = a * 2 ^ m + 4 * m + 2 ∧
      Nat.card ↥(Sec8V1 M Q Z B t r) = Nat.card Z ^ (2 * m + 2) ∧
      Nat.card ↥(Sec8W1 M Q Z B t r) =
        Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Z ^ (a * 2 ^ m) := by
  classical
  haveI := hpts.charP
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  obtain ⟨hV1c, hWc, -⟩ := h53.1 G M Q Z B hc n t hs hpts.spNat r hrR hplane
    (conjSubgroup r B) (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    (Sec8V1 M Q Z B t r) (Sec8W1 M Q Z B t r) rfl rfl rfl rfl rfl
  have hb := h53.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hplane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl
  have hcd := h53.2.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hplane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have he := h53.2.2.2.2 G M Q Z B hc n t hs hpts.spNat (Rt M (LB M Q B) t)
    (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl
  have hV := hpts.card_V
  obtain ⟨-, hN, -⟩ := hpts.act
  haveI := hN
  have hchi := card_mul_card_of_isChiIso he (inf_le_left : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q)
    (sec39_Z_le_Vt : Z ≤ Vt M (LB M Q B) B Z t)
  have hLeR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hL'eR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem hs.mem hrR
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hpts.hL'
  obtain ⟨a, ha⟩ := stroth_2_1_ii_secSp (m := m) (by have := hpts.two_le; omega) φ hpts.range
    hpts.ker (fun ρ hρ x hx => conj_mem_of_conjSubgroup_eq (hinv ρ hρ).2 hx)
    (fun ρ hρ x hx => conj_mem_of_conjSubgroup_eq (hinv ρ hρ).1 hx) hb.2 hcd hLeR hL'eR hpts.uu'
    hpts.hL hL2
  have g2 : Nat.card ↥(Sec8V1 M Q Z B t r) = Nat.card Z ^ (2 * m + 2) := by
    rw [hV1c, hV]
    ring
  have g3 : Nat.card ↥(Sec8W1 M Q Z B t r) =
      Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Z ^ (a * 2 ^ m) := by
    rw [ha, hpts.card, mul_comm (2 ^ m) a]
  refine ⟨a, ?_, g2, g3⟩
  have hw : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.width
  have h1 : Nat.card Z ^ (2 * n + 2) = Nat.card Z ^ (4 * m + 4 + a * 2 ^ m) := by
    calc Nat.card Z ^ (2 * n + 2) = Nat.card Q * Nat.card Z := by rw [hw]; ring
      _ = Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card (Vt M (LB M Q B) B Z t) := hchi
      _ = (Nat.card ↥(Sec8W1 M Q Z B t r) * Nat.card Z) * Nat.card Z ^ (2 * m + 1) := by
          rw [hWc, hV]
      _ = Nat.card Z ^ (4 * m + 4 + a * 2 ^ m) := by rw [g3, g2]; ring
  have h2 := Nat.pow_right_injective hq2 h1
  omega

theorem sec83seven_main_of_sec8Pts (h34 : Stroth34Statement)
    (h53 : Stroth53Statement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {K : Type} [Field K] [Finite K]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K} {u u' : Fin 2 ⊕ Fin 2 → K}
    (hs : Sec5Hyp hc n t) (hrR : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (hinv : ∀ ρ ∈ Rt M (LB M Q B) t,
      conjSubgroup ρ (Sec8V1 M Q Z B t r) = Sec8V1 M Q Z B t r ∧
      conjSubgroup ρ (Sec8W1 M Q Z B t r) = Sec8W1 M Q Z B t r)
    (hpts : Sec8Pts hc t r 2 K φ u u') (hn7 : n = 7) :
    False := by
  have hTrans := sp4ModTransStatement_holds
  classical
  haveI := hpts.charP
  have h8 : Sec8Hyp hc n t := ⟨hs, 2, hpts.two_le, hpts.spMNat⟩
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hL'R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem hs.mem hrR
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  obtain ⟨a, hn, hV1c, hW1c⟩ := sec83_count_A_of_sec8Pts h53 hs hrR hplane hinv hpts
  have ha : a = 1 := by
    subst hn7
    norm_num at hn
    omega
  subst ha
  have hcardV1 : Nat.card ↥(Sec8V1 M Q Z B t r) = Nat.card Z ^ 6 := by
    rw [hV1c]
  have hcardW1 : Nat.card ↥(Sec8W1 M Q Z B t r) = Nat.card Z ^ 10 := by
    rw [hW1c, hcardV1, ← pow_add]
    norm_num
  have hb := h53.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hplane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl
  have hcd := h53.2.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hplane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  obtain ⟨hVA1, hA1W, hVA2, hA2W, hsup, hinf, hcomm, hsq, hA1c, hA2c⟩ := hcd
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hW₁Q : Sec8W1 M Q Z B t r ≤ Q := inf_le_left
  have hV₁W₁ : Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r := hVA1.trans hA1W
  have hnormW1 : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Sec8W1 M Q Z B t r,
      ρ * x * ρ⁻¹ ∈ Sec8W1 M Q Z B t r := fun ρ hρ x hx =>
    conj_mem_of_conjSubgroup_eq (hinv ρ hρ).2 hx
  have hnormV1 : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Sec8V1 M Q Z B t r,
      ρ * x * ρ⁻¹ ∈ Sec8V1 M Q Z B t r := fun ρ hρ x hx =>
    conj_mem_of_conjSubgroup_eq (hinv ρ hρ).1 hx
  have hSecX : SecHyp (Rt M (LB M Q B) t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) :=
    ⟨hV₁W₁, hcomm, hsq, hnormW1, hnormV1⟩
  obtain ⟨X, _, _, κ, hκ⟩ := exists_sectionModule hSecX
  haveI : Finite X := hκ.finite
  have hXcard : Nat.card X = Nat.card Z ^ 4 := by
    have h1 := natCard_eq_of_isSecMod hV₁W₁ hκ
    rw [hcardW1, hcardV1] at h1
    have h2 : Nat.card Z ^ 6 * Nat.card X = Nat.card Z ^ 6 * Nat.card Z ^ 4 := by
      rw [← h1, ← pow_add]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have hkerAct : ∀ x ∈ φ.ker, ∀ a : X, x • a = a := by
    intro x hx a
    obtain ⟨w, hw⟩ := hκ.surj (Multiplicative.ofAdd a)
    have hwa : Multiplicative.toAdd (κ w) = a := by rw [hw]; rfl
    have hxN : (x : G) ∈ hc.CN t := by
      rw [hpts.ker] at hx
      exact Subgroup.mem_subgroupOf.mp hx
    have hxw : ⁅(x : G), (w : G)⁆ ∈ Sec8V1 M Q Z B t r := hb.2 (x : G) hxN w w.2
    have hxwW : ⁅(x : G), (w : G)⁆ ∈ Sec8W1 M Q Z B t r := hV₁W₁ hxw
    have h1 := smul_toAdd_sub_eq hκ hnormW1 x w hxwW
    have h2 : κ ⟨⁅(x : G), (w : G)⁆, hxwW⟩ = 1 := (hκ.ker _).mpr hxw
    rw [h2, toAdd_one, sub_eq_zero] at h1
    rw [← hwa]
    exact h1
  obtain ⟨π, hπ⟩ := exists_addAut_hom_of_range φ hpts.range hkerAct
  have hnontriv : π ≠ 1 := by
    intro hπ1
    have hall : ∀ (x : ↥(Rt M (LB M Q B) t)) (a : X), x • a = a := by
      intro x a
      have hx : φ x ∈ StatedSp 2 K := by
        rw [← hpts.range]
        exact ⟨x, rfl⟩
      rw [← hπ x hx a, hπ1]
      rfl
    have hW₁V₁ : Sec8W1 M Q Z B t r ≤ Sec8V1 M Q Z B t r := by
      intro w hw
      have hcomm_all : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅ρ, w⁆ ∈ Sec8V1 M Q Z B t r := by
        intro ρ hρ
        have hρw : ⁅ρ, w⁆ ∈ Sec8W1 M Q Z B t r := by
          rw [commutatorElement_def]
          exact (Sec8W1 M Q Z B t r).mul_mem (hnormW1 ρ hρ w hw) ((Sec8W1 M Q Z B t r).inv_mem hw)
        have h1 := smul_toAdd_sub_eq hκ hnormW1 ⟨ρ, hρ⟩ ⟨w, hw⟩ hρw
        rw [hall, sub_self] at h1
        exact (hκ.ker _).mp (Multiplicative.toAdd.injective h1.symm)
      have hwA1 := (hA1c w hw).mpr fun l hl => hcomm_all l (hLR hl)
      have hwA2 := (hA2c w hw).mpr fun l hl => hcomm_all l (hL'R hl)
      rw [← hinf]
      exact ⟨hwA1, hwA2⟩
    have h1 := Subgroup.card_le_of_le hW₁V₁
    rw [hcardW1, hcardV1] at h1
    have h2 : Nat.card Z ^ 6 < Nat.card Z ^ 10 := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have htrans := hTrans K (by have := hc.hyp.q4; rw [hpts.card]; exact this) X hκ.two
    (by rw [hXcard, hpts.card]) π hnontriv
  have h35B := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hV1V : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r := le_inf le_sup_right le_sup_right
  have hQV : Q ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := by
    refine sec8_le_normalizer_of_conj fun x hx y hy => ?_
    have hc' : ⁅x, y⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hx (hVQ hy)
    rw [show x * y * x⁻¹ = ⁅x, y⁆ * y by rw [commutatorElement_def]; group]
    exact (Vt M (LB M Q B) B Z t).mul_mem (sec39_Z_le_Vt hc') hy
  have hcommV1 : ∀ x ∈ Sec8W1 M Q Z B t r, ∀ y ∈ Sec8V1 M Q Z B t r, x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm
  have hV1sq : ∀ v ∈ Sec8V1 M Q Z B t r, v ^ 2 = 1 := by
    intro v hv
    have hv' : v ∈ (Q ⊓ QB B) ⊔ Vt M (LB M Q B) B Z t := hv.1
    obtain ⟨a, ha, v₀, hv₀, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (H := Q ⊓ QB B) (K := Vt M (LB M Q B) B Z t) (fun x hx => hQV hx.1) hv'
    have haV₁ : a ∈ Sec8V1 M Q Z B t r := by
      have := (Sec8V1 M Q Z B t r).mul_mem hv ((Sec8V1 M Q Z B t r).inv_mem (hV1V hv₀))
      simpa using this
    have h1 : a ^ 2 = 1 := hc.inf_QB_elemAbelian.2 a ha
    have h2 : v₀ ^ 2 = 1 := (hc.Vt_isElemAbelian h35B hs.mem hs.notQ).2 v₀ hv₀
    have h3 : Commute a v₀ := hcommV1 a (hV₁W₁ haV₁) v₀ (hV1V hv₀)
    rw [h3.mul_pow, h1, h2, one_mul]
  set A₁ := QB B ⊓ Sec8W1 M Q Z B t r ⊔ Sec8V1 M Q Z B t r with hA₁
  set A₂ := QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r ⊔ Sec8V1 M Q Z B t r with hA₂
  have hA1sq : ∀ x ∈ A₁, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨a, ha, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (H := QB B ⊓ Sec8W1 M Q Z B t r) (K := Sec8V1 M Q Z B t r)
      (sec8_le_normalizer_of_conj (S := QB B ⊓ Sec8W1 M Q Z B t r) fun y hy w hw => by
        rw [hcommV1 y hy.2 w hw, mul_inv_cancel_right]
        exact hw) hx
    have h1 : a ^ 2 = 1 := hc.inf_QB_elemAbelian.2 a ⟨hW₁Q ha.2, ha.1⟩
    have h2 : v ^ 2 = 1 := hV1sq v hv
    have h3 : Commute a v := hcommV1 a ha.2 v hv
    rw [h3.mul_pow, h1, h2, one_mul]
  have hA2sq : ∀ x ∈ A₂, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨a, ha, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (H := QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) (K := Sec8V1 M Q Z B t r)
      (sec8_le_normalizer_of_conj (S := QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r)
        fun y hy w hw => by
          rw [hcommV1 y hy.2 w hw, mul_inv_cancel_right]
          exact hw) hx
    have h1 : a ^ 2 = 1 := hcC.inf_QB_elemAbelian.2 a ⟨hW₁Q ha.2, ha.1⟩
    have h2 : v ^ 2 = 1 := hV1sq v hv
    have h3 : Commute a v := hcommV1 a ha.2 v hv
    rw [h3.mul_pow, h1, h2, one_mul]
  have hex : (∃ a ∈ A₁, a ∉ Sec8V1 M Q Z B t r) ∨ (∃ a ∈ A₂, a ∉ Sec8V1 M Q Z B t r) := by
    by_contra hcon
    push Not at hcon
    have hle : Sec8W1 M Q Z B t r ≤ Sec8V1 M Q Z B t r := by
      rw [← hsup]
      exact sup_le (fun a ha => hcon.1 a ha) (fun a ha => hcon.2 a ha)
    have h1 := Subgroup.card_le_of_le hle
    rw [hcardW1, hcardV1] at h1
    have h2 : Nat.card Z ^ 6 < Nat.card Z ^ 10 := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have key : ∀ (Ai : Subgroup G), Ai ≤ Sec8W1 M Q Z B t r → Sec8V1 M Q Z B t r ≤ Ai →
      (∀ x ∈ Ai, x ^ 2 = 1) → (∃ a ∈ Ai, a ∉ Sec8V1 M Q Z B t r) →
      ∀ w ∈ Sec8W1 M Q Z B t r, w ∉ Sec8V1 M Q Z B t r → w ^ 2 = 1 := by
    intro Ai hAiW hVAi hAisq ⟨a, haA, haV⟩ w hw hwV
    have hya : Multiplicative.toAdd (κ ⟨a, hAiW haA⟩) ≠ 0 := fun h =>
      haV ((hκ.ker _).mp (Multiplicative.toAdd.injective h))
    have hyw : Multiplicative.toAdd (κ ⟨w, hw⟩) ≠ 0 := fun h =>
      hwV ((hκ.ker _).mp (Multiplicative.toAdd.injective h))
    obtain ⟨g, hg⟩ := htrans _ _ hya hyw
    have hgφ : (g : GL (Fin 2 ⊕ Fin 2) K) ∈ φ.range := by
      rw [hpts.range]
      exact g.2
    obtain ⟨ρ, hρ⟩ := hgφ
    have hρS : φ ρ ∈ StatedSp 2 K := by
      rw [hρ]
      exact g.2
    have hgeq : g = ⟨φ ρ, hρS⟩ := Subtype.ext hρ.symm
    rw [hgeq, hπ ρ hρS] at hg
    obtain ⟨ρ', hρ'R⟩ := ρ
    have hact := hκ.act ⟨ρ', hρ'R⟩ ⟨a, hAiW haA⟩
      ⟨ρ' * a * ρ'⁻¹, hnormW1 ρ' hρ'R a (hAiW haA)⟩ rfl
    rw [hg] at hact
    have hact' : κ ⟨ρ' * a * ρ'⁻¹, hnormW1 ρ' hρ'R a (hAiW haA)⟩ = κ ⟨w, hw⟩ := by
      rw [hact]
      rfl
    have hv₁ : (ρ' * a * ρ'⁻¹) * w⁻¹ ∈ Sec8V1 M Q Z B t r := (hκ.eq_iff _ _).mp hact'
    have hv'' : ρ'⁻¹ * ((ρ' * a * ρ'⁻¹) * w⁻¹)⁻¹ * ρ' ∈ Sec8V1 M Q Z B t r := by
      simpa using hnormV1 ρ'⁻¹ ((Rt M (LB M Q B) t).inv_mem hρ'R) _
        ((Sec8V1 M Q Z B t r).inv_mem hv₁)
    have hxA : (ρ'⁻¹ * ((ρ' * a * ρ'⁻¹) * w⁻¹)⁻¹ * ρ') * a ∈ Ai :=
      Ai.mul_mem (hVAi hv'') haA
    have hw_eq : w = ρ' * ((ρ'⁻¹ * ((ρ' * a * ρ'⁻¹) * w⁻¹)⁻¹ * ρ') * a) * ρ'⁻¹ := by group
    rw [hw_eq, conj_pow, hAisq _ hxA]
    group
  have hsqW1 : ∀ w ∈ Sec8W1 M Q Z B t r, w ^ 2 = 1 := by
    intro w hw
    by_cases hwV : w ∈ Sec8V1 M Q Z B t r
    · exact hV1sq w hwV
    · rcases hex with ⟨a, haA, haV⟩ | ⟨a, haA, haV⟩
      · exact key A₁ hA1W hVA1 hA1sq ⟨a, haA, haV⟩ w hw hwV
      · exact key A₂ hA2W hVA2 hA2sq ⟨a, haA, haV⟩ w hw hwV
  have habel : ∀ a ∈ Sec8W1 M Q Z B t r, ∀ b ∈ Sec8W1 M Q Z B t r, a * b = b * a := by
    intro a ha b hb
    have h1 := hsqW1 a ha
    have h2 := hsqW1 b hb
    have h3 := hsqW1 (a * b) ((Sec8W1 M Q Z B t r).mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rwa [sq] at h1)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rwa [sq] at h2)
    have hab' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rwa [sq] at h3)
    calc a * b = (a * b)⁻¹ := hab'.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha', hb']
  have hZW₁ : Z ≤ Sec8W1 M Q Z B t r := fun z hz => ⟨hZQ hz,
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hz (hV₁W₁.trans hW₁Q hv)).symm⟩
  have hAB := sec83W1_card_le_of_comm hc hs hV₁W₁ hW₁Q hZW₁ habel
  rw [hcardW1, hn7] at hAB
  have h2 : Nat.card Z ^ (7 + 1) < Nat.card Z ^ 10 := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

theorem sec83SevenStatement_of_minimal' (h34 : Stroth34Statement) (h53 : Stroth53Statement)
    (hPts : Sec5NatPointsSpStatement) : Sec83SevenStatement := by
  intro G _ _ M Q Z B hc n t hs hsp hn
  have h8 : Sec8Hyp hc n t := ⟨hs, 2, le_rfl, hsp⟩
  obtain ⟨r, hrR, hplane⟩ := hc.exists_hypPlane_of_spMNat h34 hs (by norm_num) hsp
  obtain ⟨K, iK, iF, hK, m', hm', φ, u, u', hrange, hker, hact, huu', hL, hL'⟩ :=
    hPts G M Q Z B hc n t hs h8.spNat r hrR hplane
  letI := iK
  letI := iF
  have hpts : Sec8Pts hc t r m' K φ u u' := ⟨hm', hK, hrange, hker, hact, huu', hL, hL'⟩
  obtain rfl : m' = 2 := hpts.spMNat.m_unique hsp
  exact sec83seven_main_of_sec8Pts h34 h53 hs hrR hplane
    (sec8Inv_of_sec8Pts h53 hc hs hrR hplane hpts) hpts hn
end CFSG.RankThree.GF2n.Stroth80
