module

public import CFSG.Quasithin.Vol2.Ch12Sec6L26q

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.LieType.BorelTits CFSG.Quasithin.F7 S126 S126L1a S126P S126E S126F S126L19 S126L19a
  S126L24 Equiv
open scoped commutatorElement

namespace S126L211

abbrev t3 (a b c : Fin 8) : Perm (Fin 8) := swap a b * swap b c

theorem tau10_eq : tau 1 0 = t3 0 1 2 * t3 1 2 3 := by decide

theorem tau20_eq : tau 2 0 = t3 0 2 1 * t3 2 1 3 := by decide

theorem tau01_eq : tau 0 1 = t3 4 5 6 * t3 5 6 7 := by decide

theorem tau02_eq : tau 0 2 = t3 4 6 5 * t3 6 5 7 := by decide

theorem t3_mem {a b c : Fin 8} (hab : a ≠ b) (hbc : b ≠ c) :
    t3 a b c ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hbc]
  rfl

theorem t3_pow : ∀ a b c : Fin 8, a ≠ b → b ≠ c → a ≠ c → t3 a b c ^ 3 = 1 := by decide

theorem t3_block : ∀ a b c : Fin 8, (a.val < 4 ↔ b.val < 4) → (b.val < 4 ↔ c.val < 4) →
    ∀ i : Fin 8, (i.val < 4 ↔ (t3 a b c i).val < 4) := by decide

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem exists_R1_of_E16 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {ν : Perm (Fin 8)} (hν : ν ∈ E16) :
    ∃ r ∈ Ri T L F.V1, r ∈ Subgroup.normalizer (V : Set G) ∧ ActsAs F r ν := by
  obtain ⟨-, hXV, hXV1, -⟩ := sup_le_normalizers h1222 F hH
  have hR := inf_centralizerMod_le_R1 h1222 F hH hZ
  have hgen : ∀ a b c a' b' c' : Fin 8, a ≠ b → b ≠ c → a ≠ c → a' ≠ b' → b' ≠ c' → a' ≠ c' →
      (a.val < 4 ↔ b.val < 4) → (b.val < 4 ↔ c.val < 4) → (a'.val < 4 ↔ b'.val < 4) →
      (b'.val < 4 ↔ c'.val < 4) → t3 a b c * t3 a' b' c' ∈ E16 →
      ∃ r ∈ Ri T L F.V1, r ∈ Subgroup.normalizer (V : Set G) ∧
        ActsAs F r (t3 a b c * t3 a' b' c') := by
    intro a b c a' b' c' hab hbc hac hab' hbc' hac' h1 h2 h1' h2' hE
    obtain ⟨l, hl, hlV, hla⟩ := S126L1b.exists_mem_L1 F (t3_mem hab hbc) (t3_pow a b c hab hbc hac)
      (t3_block a b c h1 h2)
    obtain ⟨l', hl', hlV', hla'⟩ := S126L1b.exists_mem_L1 F (t3_mem hab' hbc')
      (t3_pow a' b' c' hab' hbc' hac') (t3_block a' b' c' h1' h2')
    have hll : l * l' ∈ Li L F.V1 := (Li L F.V1).mul_mem hl hl'
    have hact := hla.mul hla' hlV'
    refine ⟨l * l', hR ⟨Subgroup.mem_sup_left hll, ?_⟩, Subgroup.mul_mem _ hlV hlV', hact⟩
    exact S126L24.mem_centralizerMod_of_E16 (Subgroup.mul_mem _ hlV hlV')
      (hXV1 (Subgroup.mem_sup_left hll)) hact hE
  have g10 := hgen 0 1 2 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (tau10_eq ▸ tau_mem 1 0)
  have g20 := hgen 0 2 1 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (tau20_eq ▸ tau_mem 2 0)
  have g01 := hgen 4 5 6 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (tau01_eq ▸ tau_mem 0 1)
  have g02 := hgen 4 6 5 6 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (tau02_eq ▸ tau_mem 0 2)
  rw [← tau10_eq] at g10
  rw [← tau20_eq] at g20
  rw [← tau01_eq] at g01
  rw [← tau02_eq] at g02
  set S : Set (Perm (Fin 8)) := {σ | ∃ r ∈ Ri T L F.V1, r ∈ Subgroup.normalizer (V : Set G) ∧
    ActsAs F r σ} with hS
  have hmul : ∀ σ ∈ S, ∀ τ ∈ S, σ * τ ∈ S := by
    rintro σ ⟨r, hr, hrV, hra⟩ τ ⟨r', hr', hrV', hra'⟩
    exact ⟨r * r', (Ri T L F.V1).mul_mem hr hr', Subgroup.mul_mem _ hrV hrV', hra.mul hra' hrV'⟩
  have hpow : ∀ σ ∈ S, ∀ n : ℕ, σ ^ n ∈ S := by
    rintro σ ⟨r, hr, hrV, hra⟩ n
    exact ⟨r ^ n, (Ri T L F.V1).pow_mem hr n, Subgroup.pow_mem _ hrV n, hra.pow hrV n⟩
  obtain ⟨u, v, rfl⟩ := hν
  rw [tau_decomp u v]
  exact hmul _ (hmul _ (hpow _ g10 _) _ (hpow _ g20 _)) _ (hmul _ (hpow _ g01 _) _ (hpow _ g02 _))


theorem not_cent_V5 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {p : G} (hpL : p ∈ Li L F.V1)
    (hp3 : p ^ 3 = 1) (hp1 : p ≠ 1) :
    ¬ ∀ y ∈ F.V5, p * y * p⁻¹ * y⁻¹ ∈ F.V1 := by
  intro hcent
  obtain ⟨-, hXV, hXV1, -⟩ := sup_le_normalizers h1222 F hH
  have hinj := beta_injective F hZ
  have hpL' : p ∈ L := S126L19b.L1_le_L F hpL
  have hpV : p ∈ Subgroup.normalizer (V : Set G) := hXV (Subgroup.mem_sup_left hpL)
  set σ := S126T2.psiP F hH ⟨p, hpL'⟩ with hσ
  have hact : ActsAs F p σ := S126T2.actsAs_psiP F hH ⟨p, hpL'⟩
  have hcm : p ∈ centralizerMod F.V1 ⊤ F.V5 :=
    ⟨Subgroup.mem_top _, hXV1 (Subgroup.mem_sup_left hpL), hcent⟩
  have hE := mem_E16_of_cent (cent_of_mem_centralizerMod hpV hact hcm)
  have hσσ : σ * σ = 1 := by
    obtain ⟨u, v, huv⟩ := hE
    rw [huv, tau_mul, xr_self, xr_self, tau_zero]
  have hσ3 : σ ^ 3 = 1 := by
    have h1 := hact.pow hpV 3
    rw [hp3] at h1
    exact (h1.unique (ActsAs.one F) (Subgroup.one_mem _))
  have hσ1 : σ = 1 := by
    calc σ = σ ^ 3 * (σ * σ)⁻¹ := by group
      _ = 1 := by rw [hσ3, hσσ, inv_one, mul_one]
  rw [hσ1] at hact
  have hpC := mem_centralizer_of_actsAs_one' hinj hpV hact
  obtain ⟨n, hn⟩ := S126T2.isPGroup_CL h1222 hH ⟨p, hpL', hpC⟩
  have h2 : p ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact hp1 (S126L26.eq_one_of_two_three' h2 hp3)

theorem le_sup_comm (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (h : HypF91 T V L F.V1 F.V5 H) {p : G} (hpL : p ∈ Li L F.V1) (hp3 : p ^ 3 = 1)
    (hp1 : p ≠ 1)
    (hnorm : ∀ g ∈ Li L F.V1 ⊔ T, ∀ x ∈ Subgroup.zpowers p, ∃ x' ∈ Subgroup.zpowers p,
      x'⁻¹ * (g * x * g⁻¹) ∈ pCoreOf 2 H) :
    F.V5 ≤ F.V1 ⊔ ⁅F.V5, Subgroup.zpowers p⁆ := by
  have hL1T5 : Li L F.V1 ⊔ T ≤ Subgroup.normalizer (F.V5 : Set G) := h.L₁T_normalizes_Vp
  have hL1TH : Li L F.V1 ⊔ T ≤ H := h.L₁T_le_H
  have hV5U : F.V5 ≤ conjClosure F.V5 H := le_conjClosure F.V5 H
  have hpH : p ∈ H := hL1TH (Subgroup.mem_sup_left hpL)
  set W := F.V1 ⊔ ⁅F.V5, Subgroup.zpowers p⁆ with hW
  have hpN5 : Subgroup.zpowers p ≤ Subgroup.normalizer (F.V5 : Set G) :=
    Subgroup.zpowers_le.mpr (hL1T5 (Subgroup.mem_sup_left hpL))
  have hWV5 : W ≤ F.V5 := sup_le h.V₁_le_Vp
    ((Subgroup.le_normalizer_iff_commutator_le_left).mp hpN5)
  have hconj : ∀ g ∈ Li L F.V1 ⊔ T, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hg w hw
    have hgH := hL1TH hg
    have hle : W ≤ W.comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun z hz => ?_) ?_
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (h.H_normalizes_V₁ hgH) z).mp
          hz)
      · rw [Subgroup.commutator_le]
        intro y hy x hx
        show g * ⁅y, x⁆ * g⁻¹ ∈ W
        obtain ⟨x', hx', hq⟩ := hnorm g hg x hx
        set q := x'⁻¹ * (g * x * g⁻¹) with hqdef
        have hy' : g * y * g⁻¹ ∈ F.V5 := (Subgroup.mem_normalizer_iff.mp (hL1T5 hg) y).mp hy
        have e : g * ⁅y, x⁆ * g⁻¹ = ⁅g * y * g⁻¹, x'⁆ * (x' * ⁅g * y * g⁻¹, q⁆ * x'⁻¹) := by
          rw [hqdef]
          simp only [commutatorElement_def]
          group
        rw [e]
        refine Subgroup.mul_mem _ (Subgroup.mem_sup_right
          (Subgroup.commutator_mem_commutator hy' hx')) (Subgroup.mem_sup_left ?_)
        have hx'H : x' ∈ H := (Subgroup.zpowers_le.mpr hpH) hx'
        have h1 : ⁅g * y * g⁻¹, q⁆ ∈ F.V1 := by
          rw [commutatorElement_def]
          exact h.commutator_conjClosure_le _ (hV5U hy') q hq
        exact (Subgroup.mem_normalizer_iff.mp (h.H_normalizes_V₁ hx'H) _).mp h1
    exact hle hw
  have hWn : Li L F.V1 ⊔ T ≤ Subgroup.normalizer (W : Set G) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hconj g hg w hw, fun hw => ?_⟩
    have := hconj g⁻¹ ((Li L F.V1 ⊔ T).inv_mem hg) _ hw
    simpa [mul_assoc] using this
  rcases h.irred W le_sup_left hWV5 hWn with h1 | h1
  · exfalso
    apply not_cent_V5 h1222 F hH hZ hpL hp3 hp1
    intro y hy
    have h2 : ⁅y, p⁆ ∈ W := Subgroup.mem_sup_right
      (Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers p))
    rw [h1] at h2
    have e : p * y * p⁻¹ * y⁻¹ = ⁅y, p⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact F.V1.inv_mem h2
  · rw [← h1]

omit [IsMulCommutative ↥V] in
theorem mem_centralizer_of_comm {V₁ Vp H : Subgroup G} (h : HypF91 T V L V₁ Vp H)
    (hC5 : Subgroup.centralizer (Vp : Set G) ≤ Subgroup.centralizer (V : Set G)) {p : G}
    (hpH : p ∈ H) (hpV : p ∈ Subgroup.normalizer (V : Set G))
    (hfpf : Vp ≤ V₁ ⊔ ⁅Vp, Subgroup.zpowers p⁆) {r : G} (hrH : r ∈ H)
    (hr5 : ∀ y ∈ Vp, r * y * r⁻¹ * y⁻¹ ∈ V₁) (hrp : ⁅r, p⁆ ∈ Subgroup.centralizer (V : Set G)) :
    r ∈ Subgroup.centralizer (V : Set G) := by
  have hcen : ∀ z ∈ V₁, ∀ a ∈ H, z * a = a * z := fun z hz a ha =>
    Subgroup.mem_centralizer_iff.mp (h.H_le_centralizer ha) z hz
  have hCN : ∀ x ∈ Subgroup.normalizer (V : Set G), ∀ c ∈ Subgroup.centralizer (V : Set G),
      x * c * x⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro x hx c hc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : x⁻¹ * y * x ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) y).mp hy
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hy'
    calc y * (x * c * x⁻¹) = x * ((x⁻¹ * y * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * y * x)) * x⁻¹ := by rw [h1]
      _ = x * c * x⁻¹ * y := by group
  have hpow : ∀ n : ℕ, ⁅r, p ^ n⁆ ∈ Subgroup.centralizer (V : Set G) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : ⁅r, p ^ (n + 1)⁆ = ⁅r, p ^ n⁆ * (p ^ n * ⁅r, p⁆ * (p ^ n)⁻¹) := by
        simp only [commutatorElement_def, pow_succ]
        group
      rw [e]
      exact Subgroup.mul_mem _ ih (hCN _ (Subgroup.pow_mem _ hpV n) _ hrp)
  have hcomm : ⁅Vp, Subgroup.zpowers p⁆ ≤ Subgroup.centralizer ({r} : Set G) := by
    rw [Subgroup.commutator_le]
    intro y hy x hx
    rw [← mem_powers_iff_mem_zpowers] at hx
    obtain ⟨n, rfl⟩ := hx
    have hyV : y ∈ V := h.Vp_le_V hy
    have hyH : y ∈ H := h.Vp_le_H hy
    have hxH : p ^ n ∈ H := H.pow_mem hpH n
    have hxV : p ^ n ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hpV n
    set c := ⁅r, p ^ n⁆ with hc
    have hcC := hpow n
    have hcH : c ∈ H := by
      rw [hc, commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hrH hxH) (H.inv_mem hrH)) (H.inv_mem hxH)
    set z := r * y * r⁻¹ * y⁻¹ with hz
    have hzV : z ∈ V₁ := hr5 y hy
    have hry : r * y * r⁻¹ = z * y := by rw [hz]; group
    have hrx : r * p ^ n * r⁻¹ = c * p ^ n := by rw [hc, commutatorElement_def]; group
    have hw : p ^ n * y⁻¹ * (p ^ n)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hxV _).mp (V.inv_mem hyV)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : r * ⁅y, p ^ n⁆ * r⁻¹ = ⁅z * y, c * p ^ n⁆ := by
      rw [← hry, ← hrx]
      simp only [commutatorElement_def]
      group
    have e2a : ⁅z * y, c * p ^ n⁆ = ⁅y, c * p ^ n⁆ := by
      have hw' : y * (c * p ^ n) * y⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem hyH (H.mul_mem hcH hxH)) (H.inv_mem hyH)
      have h1 := hcen z hzV _ hw'
      calc ⁅z * y, c * p ^ n⁆ = z * (y * (c * p ^ n) * y⁻¹) * z⁻¹ * (c * p ^ n)⁻¹ := by
            simp only [commutatorElement_def]
            group
        _ = (y * (c * p ^ n) * y⁻¹) * z * z⁻¹ * (c * p ^ n)⁻¹ := by rw [h1]
        _ = ⁅y, c * p ^ n⁆ := by
            simp only [commutatorElement_def]
            group
    have e2b : ⁅y, c * p ^ n⁆ = ⁅y, p ^ n⁆ := by
      have hc2 := Subgroup.mem_centralizer_iff.mp hcC _ hw
      calc ⁅y, c * p ^ n⁆ = y * (c * (p ^ n * y⁻¹ * (p ^ n)⁻¹)) * c⁻¹ := by
            simp only [commutatorElement_def]
            group
        _ = y * ((p ^ n * y⁻¹ * (p ^ n)⁻¹) * c) * c⁻¹ := by rw [hc2]
        _ = ⁅y, p ^ n⁆ := by
            simp only [commutatorElement_def]
            group
    calc ⁅y, p ^ n⁆ * r = (r * ⁅y, p ^ n⁆ * r⁻¹) * r := by rw [e1, e2a, e2b]
      _ = r * ⁅y, p ^ n⁆ := by group
  have hV1r : V₁ ≤ Subgroup.centralizer ({r} : Set G) := fun z hz => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcen z hz r hrH
  have hle : Vp ≤ Subgroup.centralizer ({r} : Set G) := hfpf.trans (sup_le hV1r hcomm)
  apply hC5
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

omit [Finite G] [IsMulCommutative ↥V] in
theorem conj_mem_centralizer {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) {c : G}
    (hc : c ∈ Subgroup.centralizer (V : Set G)) :
    x * c * x⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : x⁻¹ * y * x ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) y).mp hy
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hc _ hy'
  calc y * (x * c * x⁻¹) = x * ((x⁻¹ * y * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * y * x)) * x⁻¹ := by rw [h1]
    _ = x * c * x⁻¹ * y := by group

omit [Finite G] [IsMulCommutative ↥V] in
theorem le_normalizer_O {X : Subgroup G} (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) :
    X ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  have key : ∀ y ∈ X, ∀ c ∈ L ⊓ Subgroup.centralizer (V : Set G),
      y * c * y⁻¹ ∈ L ⊓ Subgroup.centralizer (V : Set G) := fun y hy c hc =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hXL hy) c).mp hc.1, conj_mem_centralizer (hXV hy) hc.2⟩
  refine ⟨fun hc => key x hx c hc, fun hc => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ hc
  simpa [mul_assoc] using this

omit [Finite G] in
theorem actsAs_one_of_mem (F : Frame126 T L V) {x : G}
    (hx : x ∈ Subgroup.centralizer (V : Set G)) : ActsAs F x 1 := by
  intro v w hw
  have hwv : w = v := Subtype.ext (by
    rw [hw, (Subgroup.mem_centralizer_iff.1 hx v v.2).symm]
    group)
  rw [hwv, dAct_one]

theorem comm_O_le_V (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (h : HypF91 T V L F.V1 F.V5 H)
    (hC5 : Subgroup.centralizer (F.V5 : Set G) ≤ Subgroup.centralizer (V : Set G)) {p : G}
    (hpL : p ∈ Li L F.V1) (hp3 : p ^ 3 = 1) (hfpf : F.V5 ≤ F.V1 ⊔ ⁅F.V5, Subgroup.zpowers p⁆)
    (hcard : Nat.card ↥⁅Ri T L F.V1, Subgroup.zpowers p⁆ ≤ 2 ^ 9) :
    ⁅L ⊓ Subgroup.centralizer (V : Set G), Subgroup.zpowers p⁆ ≤ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  obtain ⟨hXL, hXV, hXV1, -⟩ := sup_le_normalizers h1222 F hH
  have hinj := beta_injective F hZ
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hXV
  have hL1L : Li L F.V1 ≤ L := S126L19b.L1_le_L F
  have hpL' : p ∈ L := hL1L hpL
  have hpV : p ∈ Subgroup.normalizer (V : Set G) := hLV hpL'
  have hpH : p ∈ H := h.L₁T_le_H (Subgroup.mem_sup_left hpL)
  have hR1T : Ri T L F.V1 ≤ T :=
    pCoreOf_le_of_le_normalizer hyp.sylow (le_sup_right.trans Subgroup.le_normalizer)
  have hR1H : Ri T L F.V1 ≤ H := (pCoreOf_le 2 _).trans h.L₁T_le_H
  set O := L ⊓ Subgroup.centralizer (V : Set G) with hO
  have hO2 : IsPGroup 2 O := S126T2.isPGroup_CL h1222 hH
  have hON : L ⊔ T ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_O (sup_le Subgroup.le_normalizer hTL) (sup_le hLV hTV)
  have hOT : O ≤ T := by
    have h1 : O ≤ pCoreOf 2 (L ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_left) hON hO2
    rw [← h.cT] at h1
    exact h1.trans inf_le_left
  have hOR : O ≤ Ri T L F.V1 :=
    le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
      ((S126L19b.L1_le_L F |> fun h => sup_le_sup_right h T).trans hON) hO2
  set N := ⁅Ri T L F.V1, Subgroup.zpowers p⁆ with hN
  have hNL : N ≤ L := by
    rw [hN, Subgroup.commutator_le]
    intro r hr x hx
    have hxL : x ∈ L := (Subgroup.zpowers_le.mpr hpL') hx
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTL (hR1T hr)) x).mp hxL) (L.inv_mem hxL)
  have hceq := S126L19a.card_eq F hH hNL
  set σ := S126T2.psiP F hH ⟨p, hpL'⟩ with hσ
  have hpa : ActsAs F p σ := S126T2.actsAs_psiP F hH ⟨p, hpL'⟩
  have hlift : ∀ uv : Fin 4 × Fin 4, ∃ r ∈ Ri T L F.V1, r ∈ Subgroup.normalizer (V : Set G) ∧
      ActsAs F r (tau uv.1 uv.2) := fun uv =>
    exists_R1_of_E16 h1222 F hH hZ (tau_mem uv.1 uv.2)
  choose r hrR hrV hra using hlift
  have hrN : ∀ uv, ⁅r uv, p⁆ ∈ N := fun uv =>
    Subgroup.commutator_mem_commutator (hrR uv) (Subgroup.mem_zpowers p)
  let f : Fin 4 × Fin 4 → ↥((N.subgroupOf L).map (S126L19a.psi F hH)) := fun uv =>
    ⟨S126L19a.psi F hH ⟨⁅r uv, p⁆, hNL (hrN uv)⟩,
      ⟨⟨⁅r uv, p⁆, hNL (hrN uv)⟩, Subgroup.mem_subgroupOf.mpr (hrN uv), rfl⟩⟩
  have hcommV : ∀ uv, ⁅r uv, p⁆ ∈ Subgroup.normalizer (V : Set G) := fun uv => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hrV uv) hpV)
      (Subgroup.inv_mem _ (hrV uv))) (Subgroup.inv_mem _ hpV)
  have hfa : ∀ uv, ActsAs F ⁅r uv, p⁆ (tau uv.1 uv.2 * σ * (tau uv.1 uv.2)⁻¹ * σ⁻¹) := fun uv => by
    rw [commutatorElement_def]
    exact (hra uv).commutator hpa (hrV uv) hpV
  have hfinj : Function.Injective f := by
    intro uv uv' heq
    have h1 : S126T2.psiP F hH ⟨⁅r uv, p⁆, hNL (hrN uv)⟩ =
        S126T2.psiP F hH ⟨⁅r uv', p⁆, hNL (hrN uv')⟩ := by
      have := congrArg (fun z : ↥((N.subgroupOf L).map (S126L19a.psi F hH)) =>
        ((z : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8))) heq
      exact this
    have h2 : tau uv.1 uv.2 * σ * (tau uv.1 uv.2)⁻¹ * σ⁻¹ =
        tau uv'.1 uv'.2 * σ * (tau uv'.1 uv'.2)⁻¹ * σ⁻¹ := by
      rw [(hfa uv).unique (S126T2.actsAs_psiP F hH ⟨_, hNL (hrN uv)⟩) (hcommV uv),
        (hfa uv').unique (S126T2.actsAs_psiP F hH ⟨_, hNL (hrN uv')⟩) (hcommV uv'), h1]
    set ρ := (r uv')⁻¹ * r uv with hρ
    have hρR : ρ ∈ Ri T L F.V1 := (Ri T L F.V1).mul_mem ((Ri T L F.V1).inv_mem (hrR uv')) (hrR uv)
    have hρV : ρ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hrV uv')) (hrV uv)
    have hρa : ActsAs F ρ ((tau uv'.1 uv'.2)⁻¹ * tau uv.1 uv.2) :=
      (hra uv').inv.mul (hra uv) (hrV uv)
    have hρpV : ⁅ρ, p⁆ ∈ Subgroup.normalizer (V : Set G) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hρV hpV)
        (Subgroup.inv_mem _ hρV)) (Subgroup.inv_mem _ hpV)
    have hρp1 : ActsAs F ⁅ρ, p⁆ 1 := by
      have h3 : ActsAs F ⁅ρ, p⁆ (((tau uv'.1 uv'.2)⁻¹ * tau uv.1 uv.2) * σ *
          ((tau uv'.1 uv'.2)⁻¹ * tau uv.1 uv.2)⁻¹ * σ⁻¹) := by
        rw [commutatorElement_def]
        exact hρa.commutator hpa hρV hpV
      have e : ((tau uv'.1 uv'.2)⁻¹ * tau uv.1 uv.2) * σ *
          ((tau uv'.1 uv'.2)⁻¹ * tau uv.1 uv.2)⁻¹ * σ⁻¹ = 1 := by
        calc ((tau uv'.1 uv'.2)⁻¹ * tau uv.1 uv.2) * σ *
            ((tau uv'.1 uv'.2)⁻¹ * tau uv.1 uv.2)⁻¹ * σ⁻¹ =
            (tau uv'.1 uv'.2)⁻¹ * (tau uv.1 uv.2 * σ * (tau uv.1 uv.2)⁻¹ * σ⁻¹) *
              (tau uv'.1 uv'.2 * σ * (tau uv'.1 uv'.2)⁻¹ * σ⁻¹)⁻¹ * tau uv'.1 uv'.2 := by group
          _ = 1 := by rw [h2]; group
      rw [e] at h3
      exact h3
    have hρpC := mem_centralizer_of_actsAs_one' hinj hρpV hρp1
    have hρ5 : ∀ y ∈ F.V5, ρ * y * ρ⁻¹ * y⁻¹ ∈ F.V1 :=
      (S126L24.mem_centralizerMod_of_E16 hρV (hXV1 (Subgroup.mem_sup_right (hR1T hρR))) hρa
        (E16.mul_mem (E16.inv_mem (tau_mem _ _)) (tau_mem _ _))).2.2
    have hρC := mem_centralizer_of_comm h hC5 hpH hpV hfpf (hR1H hρR) hρ5 hρpC
    have h4 : (tau uv'.1 uv'.2)⁻¹ * tau uv.1 uv.2 = 1 :=
      hρa.unique (actsAs_one_of_mem F hρC) hρV
    have h5 : tau uv.1 uv.2 = tau uv'.1 uv'.2 := by
      rw [← mul_left_cancel_iff (a := (tau uv'.1 uv'.2)⁻¹), h4, inv_mul_cancel]
    obtain ⟨hu, hv⟩ := tau_inj h5
    exact Prod.ext hu hv
  have h16 : 16 ≤ Nat.card ↥((N.subgroupOf L).map (S126L19a.psi F hH)) := by
    have := Nat.card_le_card_of_injective f hfinj
    simpa using this
  set X := ⁅O, Subgroup.zpowers p⁆ with hX
  have hpO : Subgroup.zpowers p ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.zpowers_le.mpr (hON (Subgroup.mem_sup_left hpL'))
  have hXO : X ≤ O := (Subgroup.le_normalizer_iff_commutator_le_left).mp hpO
  have hXNC : X ≤ N ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (Subgroup.commutator_mono hOR le_rfl) (hXO.trans inf_le_right)
  have hX32 : Nat.card X ≤ 32 := by
    have h1 := Subgroup.card_le_of_le hXNC
    have h2 : 16 * Nat.card ↥(N ⊓ Subgroup.centralizer (V : Set G)) ≤ 2 ^ 9 := by
      calc 16 * Nat.card ↥(N ⊓ Subgroup.centralizer (V : Set G)) ≤
          Nat.card ↥((N.subgroupOf L).map (S126L19a.psi F hH)) *
            Nat.card ↥(N ⊓ Subgroup.centralizer (V : Set G)) := Nat.mul_le_mul_right _ h16
        _ = Nat.card N := hceq.symm
        _ ≤ 2 ^ 9 := hcard
    omega
  set X₀ := ⁅V, Subgroup.zpowers p⁆ with hX₀
  have hVL : V ≤ L := by
    rw [← hyp.irrPlus.2.2.2.1, Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTL (h.V_le_T hv)) l).mp hl) (L.inv_mem hl)
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := fun v hv => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact S126L1b.comm_of_mem hw hv
  have hX₀X : X₀ ≤ X := Subgroup.commutator_mono (le_inf hVL hVC) le_rfl
  have hX₀16 : 16 ≤ Nat.card X₀ := by
    have hY := Subgroup.commutator_mono h.Vp_le_V (le_refl (Subgroup.zpowers p))
    have hV1N : F.V1 ≤ Subgroup.normalizer ((⁅F.V5, Subgroup.zpowers p⁆ : Subgroup G) : Set G) := by
      intro z hz
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hzH : ∀ a ∈ H, z * a = a * z := fun a ha =>
        Subgroup.mem_centralizer_iff.mp (h.H_le_centralizer ha) z hz
      have hYH : ⁅F.V5, Subgroup.zpowers p⁆ ≤ H := by
        rw [Subgroup.commutator_le]
        intro y hy x hx
        have hxH : x ∈ H := (Subgroup.zpowers_le.mpr hpH) hx
        rw [commutatorElement_def]
        exact H.mul_mem (H.mul_mem (H.mul_mem (h.Vp_le_H hy) hxH) (H.inv_mem (h.Vp_le_H hy)))
          (H.inv_mem hxH)
      constructor
      · intro hy
        have e : z * y * z⁻¹ = y := by rw [hzH y (hYH hy)]; group
        rw [e]
        exact hy
      · intro hy
        have hyH : y ∈ H := by
          have h1 := hYH hy
          have e : y = z⁻¹ * (z * y * z⁻¹) * z := by group
          rw [e]
          have hz' : z ∈ H := by
            have := h.V₁_le_V hz
            exact h.V_le_H this
          exact H.mul_mem (H.mul_mem (H.inv_mem hz') h1) hz'
        have e : z * y * z⁻¹ = y := by rw [hzH y hyH]; group
        rw [← e]
        exact hy
    have h1 := card_sup_le_mul hV1N
    have h2 := Subgroup.card_le_of_le hfpf
    rw [S126L24.card_V5 hinj, h.card_V₁] at *
    have h3 : Nat.card ↥⁅F.V5, Subgroup.zpowers p⁆ ≤ Nat.card X₀ := Subgroup.card_le_of_le hY
    omega
  have hidx : X₀.relIndex X = 1 ∨ X₀.relIndex X = 2 := by
    have h1 := (X₀.subgroupOf X).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₀X).toEquiv] at h1
    change Nat.card X₀ * X₀.relIndex X = Nat.card X at h1
    have hXpos : 0 < Nat.card X := Nat.card_pos
    rcases Nat.lt_or_ge (X₀.relIndex X) 3 with h2 | h2
    · rcases Nat.lt_or_ge (X₀.relIndex X) 1 with h3 | h3
      · exfalso
        have : X₀.relIndex X = 0 := by omega
        rw [this, mul_zero] at h1
        omega
      · omega
    · exfalso
      have : Nat.card X₀ * 3 ≤ Nat.card X₀ * X₀.relIndex X := Nat.mul_le_mul_left _ h2
      omega
  have hpX : Subgroup.zpowers p ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.normalizer_commutator_ge_right O (Subgroup.zpowers p)
  have hpX₀ : Subgroup.zpowers p ≤ Subgroup.normalizer (X₀ : Set G) :=
    Subgroup.normalizer_commutator_ge_right V (Subgroup.zpowers p)
  have hXX₀ : ⁅X, Subgroup.zpowers p⁆ ≤ X₀ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hyX : y * x⁻¹ * y⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hpX hy) _).mp (X.inv_mem hx)
    have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    by_cases hx0 : x ∈ X₀
    · exact X₀.mul_mem hx0 ((Subgroup.mem_normalizer_iff.mp (hpX₀ hy) _).mp (X₀.inv_mem hx0))
    · rcases hidx with h2 | h2
      · exact absurd (Subgroup.relIndex_eq_one.mp h2 hx) hx0
      · rcases S126L26.mem_or_inv_mul_mem h2 hx hx0 hyX with h3 | h3
        · exfalso
          apply hx0
          have h4 := X₀.inv_mem h3
          have h5 : x = y⁻¹ * (y * x⁻¹ * y⁻¹)⁻¹ * y := by group
          rw [h5]
          have hyi : y⁻¹ ∈ Subgroup.zpowers p := (Subgroup.zpowers p).inv_mem hy
          have := (Subgroup.mem_normalizer_iff.mp (hpX₀ hyi) _).mp h4
          simpa [mul_assoc] using this
        ·
          have hsq : x ^ 2 ∈ X₀ := by
            have := Subgroup.sq_mem_of_index_two (H := X₀.subgroupOf X) h2 ⟨x, hx⟩
            rw [Subgroup.mem_subgroupOf] at this
            simpa using this
          have e : x * (y * x⁻¹ * y⁻¹) = x ^ 2 * (x⁻¹ * (y * x⁻¹ * y⁻¹)) := by group
          rw [e]
          exact X₀.mul_mem hsq h3
  have hidem : ⁅X, Subgroup.zpowers p⁆ = X := by
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers p)) (Nat.card O) := by
      obtain ⟨n, hn⟩ := hO2.exists_card_eq
      rw [hn, Nat.card_zpowers]
      exact Nat.Coprime.pow_right n (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hp3)
        (by norm_num))
    exact S126Cop.comm_comm_eq hpO hcop
  have hX₀V : X₀ ≤ V := (Subgroup.le_normalizer_iff_commutator_le_left).mp
    (Subgroup.zpowers_le.mpr hpV)
  rw [← hidem]
  exact hXX₀.trans hX₀V

theorem comm_O_L_le_V (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {H : Subgroup G} (h : HypF91 T V L F.V1 F.V5 H) {p : G} (hpL : p ∈ L) (hp3 : p ^ 3 = 1)
    (hp1 : p ≠ 1) (hpO : ⁅L ⊓ Subgroup.centralizer (V : Set G), Subgroup.zpowers p⁆ ≤ V) :
    ∀ l ∈ L, ∀ o ∈ L ⊓ Subgroup.centralizer (V : Set G), l * o * l⁻¹ * o⁻¹ ∈ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  set O := L ⊓ Subgroup.centralizer (V : Set G) with hO
  have hO2 : IsPGroup 2 O := S126T2.isPGroup_CL h1222 hH
  have hLO : L ≤ Subgroup.normalizer (O : Set G) := le_normalizer_O Subgroup.le_normalizer hLV
  set C := centralizerMod V L O with hC
  have hpC : p ∈ C := by
    refine ⟨hpL, hLV hpL, fun u hu => ?_⟩
    have h1 := hpO (Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers p))
    have e : p * u * p⁻¹ * u⁻¹ = ⁅u, p⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact V.inv_mem h1
  have hCn : ∀ g ∈ L, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    obtain ⟨hcL, hcN, hcO⟩ := hc
    refine ⟨L.mul_mem (L.mul_mem hg hcL) (L.inv_mem hg), Subgroup.mul_mem _ (Subgroup.mul_mem _
      (hLV hg) hcN) (Subgroup.inv_mem _ (hLV hg)), fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (hLO (L.inv_mem hg)) u).mp hu
      simpa using this
    have h1 := hcO _ hu'
    have h2 : g * (c * (g⁻¹ * u * g) * c⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV hg) _).mp h1
    have e : g * c * g⁻¹ * u * (g * c * g⁻¹)⁻¹ * u⁻¹ =
        g * (c * (g⁻¹ * u * g) * c⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact h2
  set N' := (C.subgroupOf L).map (S126L19a.psi F hH) with hN'
  have hN'n : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨c, hc, rfl⟩ := hn
    obtain ⟨l, rfl⟩ := S126L19a.psi_surjective F hH g
    refine ⟨l * c * l⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hCn _ l.2 _ (Subgroup.mem_subgroupOf.mp hc)
  have hpsi1 : S126L19a.psi F hH ⟨p, hpL⟩ ≠ 1 := by
    intro h1
    have hpC' := (S126L19a.psi_eq_one_iff F hH _).mp h1
    obtain ⟨n, hn⟩ := hO2 ⟨p, hpL, hpC'⟩
    have h2 : p ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact hp1 (S126L26.eq_one_of_two_three' h2 hp3)
  have hA8 : IsSimpleGroup ↥(alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hN'top : N' = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N' with h1 | h1
    · exfalso
      have : S126L19a.psi F hH ⟨p, hpL⟩ ∈ N' := ⟨⟨p, hpL⟩, Subgroup.mem_subgroupOf.mpr hpC, rfl⟩
      rw [h1, Subgroup.mem_bot] at this
      exact hpsi1 this
    · exact h1
  have hLCO : ∀ l ∈ L, l ∈ C ⊔ O := by
    intro l hl
    have h1 : S126L19a.psi F hH ⟨l, hl⟩ ∈ N' := hN'top ▸ Subgroup.mem_top _
    obtain ⟨c, hc, hce⟩ := h1
    have h2 : S126L19a.psi F hH (c⁻¹ * ⟨l, hl⟩) = 1 := by rw [map_mul, map_inv, hce, inv_mul_cancel]
    have h3 := (S126L19a.psi_eq_one_iff F hH _).mp h2
    have h4 : (c : G)⁻¹ * l ∈ O := ⟨L.mul_mem (L.inv_mem c.2) hl, by simpa using h3⟩
    have e : l = (c : G) * ((c : G)⁻¹ * l) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hc) h4
  have hOC : O ≤ Subgroup.normalizer (C : Set G) := fun o ho => by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => hCn o ho.1 c hc, fun hc => ?_⟩
    have := hCn o⁻¹ (L.inv_mem ho.1) _ hc
    simpa [mul_assoc] using this
  have hLC : L ≤ C := by
    have h1 : oTwoUpper L ≤ C := oTwoUpper_le_of_pow_mem fun x hx =>
      S126L24.exists_pow_mem_of_mem_sup hOC hO2 (hLCO x hx)
    have h2 : oTwoUpper L = L := by rw [← oTwoRes_eq_oTwoUpper]; exact h.oTwoRes_eq
    rw [h2] at h1
    exact h1
  intro l hl o ho
  exact (hLC hl).2.2 o ho

end S126L211

end CFSG.Quasithin.H13
