module

public import CFSG.Quasithin.Background.RonanF95Core
public import CFSG.Quasithin.Background.RonanF95XY
public import CFSG.Quasithin.Background.RonanF95Dih
public import CFSG.Quasithin.Background.RonanF95Q8
public import CFSG.Quasithin.Background.RonanF95Dihedral

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

section Fin

variable [Finite G]

namespace HypF91

variable {T V L V₁ Vp H : Subgroup G}

omit [Finite G] in
theorem conj_eq_of_mem_V₁' (h : HypF91 T V L V₁ Vp H) {k c : G} (hk : k ∈ H)
    (hc : c ∈ V₁) : k * c * k⁻¹ = c := by
  have := Subgroup.mem_centralizer_iff.mp (h.H_le_centralizer hk) c hc
  rw [← this]
  group

theorem F95_six_core (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    {g : G} (hg : g ∈ H)
    (hI : ¬ ∀ x ∈ V ⊔ conjSub g⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H)
    {j : ℕ} (hj : j = 1 ∨ j = 2) (hX : Nat.card Vp = 2 ^ (2 * j + 1))
    (hcase : (j = 1 ∧ ⁅V, H ⊓ Subgroup.centralizer (Vp : Set G)⁆ ≤ V₁) ∨
      (j = 2 ∧ H ⊓ Subgroup.centralizer (Vp : Set G) = H ⊓ Subgroup.centralizer (V : Set G))) :
    CFSG.Quasithin.H13.IsQ8CentralPow (2 * j) ↥(Vp ⊔ conjSub g⁻¹ Vp) ∧
      ∃ m : ℕ, (m = 3 ∨ (j = 2 ∧ (m = 5 ∨ m = 6))) ∧
        Nonempty (↥(autOn (tildeOf V₁ (V ⊔ conjSub g⁻¹ V)) (tildeOf V₁ (conjClosure Vp H))) ≃*
          DihedralGroup m) := by
  have hH := h.H_normalizes_V₁
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hUH : conjClosure Vp H ≤ H := hUQ.trans (pCoreOf_le 2 H)
  obtain ⟨a₀, ha₀V, ha₀₀, hZV, ha₀Q⟩ := h.exists_a₀ hidx hV
  have hFive := h.F95_5 hidx hV hyp5 hg hI
  obtain ⟨hD1, hD2, hD3, hD4⟩ := h.F95_dict hidx hV hyp5 hg hI ha₀V ha₀₀ hZV
  have hVgH : conjSub g⁻¹ V ≤ H := h.conjSub_inv_le_H hg
  have hVpU : Vp ≤ conjClosure Vp H := le_conjClosure Vp H
  have hVpgU : conjSub g⁻¹ Vp ≤ conjClosure Vp H := conjSub_inv_le_U hg hVpU
  have hPU : Vp ⊔ conjSub g⁻¹ Vp ≤ conjClosure Vp H := sup_le hVpU hVpgU
  have hV₁g : conjSub g⁻¹ V₁ = V₁ := F7.conjSub_eq_of_mem_normalizer (hH (H.inv_mem hg))
  have hV₁Vpg : V₁ ≤ conjSub g⁻¹ Vp := by
    rw [← hV₁g]
    exact conjSub_mono _ h.V₁_le_Vp
  have hV₁P : V₁ ≤ Vp ⊔ conjSub g⁻¹ Vp := h.V₁_le_Vp.trans le_sup_left
  have hXP : Vp ≤ Vp ⊔ conjSub g⁻¹ Vp := le_sup_left
  have hYP : conjSub g⁻¹ Vp ≤ Vp ⊔ conjSub g⁻¹ Vp := le_sup_right
  have hb₀V : g⁻¹ * a₀ * g ∈ conjSub g⁻¹ V := by
    rw [mem_conjSub, inv_inv]
    have : g * (g⁻¹ * a₀ * g) * g⁻¹ = a₀ := by group
    rw [this]
    exact ha₀V
  have hi2 : (g⁻¹ * a₀ * g) * (g⁻¹ * a₀ * g) = 1 := by
    have : (g⁻¹ * a₀ * g) * (g⁻¹ * a₀ * g) = g⁻¹ * (a₀ * a₀) * g := by group
    rw [this, ha₀₀]
    group
  have hcen : ∀ z ∈ V₁, ∀ p ∈ Vp ⊔ conjSub g⁻¹ Vp, p * z = z * p := fun z hz p hp => by
    have := h.conj_eq_of_mem_V₁' (hUH (hPU hp)) hz
    rwa [mul_inv_eq_iff_eq_mul] at this
  have hsq : ∀ p ∈ Vp ⊔ conjSub g⁻¹ Vp, p * p ∈ V₁ := fun p hp => by
    have := h.sq_mem_conjClosure p (hPU hp)
    rwa [pow_two] at this
  have hcomm : ∀ p ∈ Vp ⊔ conjSub g⁻¹ Vp, ∀ r ∈ Vp ⊔ conjSub g⁻¹ Vp,
      p * r * p⁻¹ * r⁻¹ ∈ V₁ := fun p hp r hr =>
    h.commutator_conjClosure_le p (hPU hp) r (hUQ (hPU hr))
  have hIN := h.F95_I_normalizes hidx hV hg
  have hvmem : a₀ ∈ V ⊔ conjSub g⁻¹ V := Subgroup.mem_sup_left ha₀V
  have himem : g⁻¹ * a₀ * g ∈ V ⊔ conjSub g⁻¹ V := Subgroup.mem_sup_right hb₀V
  have hvN : ∀ p ∈ Vp ⊔ conjSub g⁻¹ Vp, a₀ * p * a₀⁻¹ ∈ Vp ⊔ conjSub g⁻¹ Vp := fun p hp =>
    (Subgroup.mem_normalizer_iff.mp (hIN hvmem) p).mp hp
  have hvN' : ∀ p ∈ Vp ⊔ conjSub g⁻¹ Vp, a₀⁻¹ * p * a₀ ∈ Vp ⊔ conjSub g⁻¹ Vp := fun p hp => by
    have := (Subgroup.mem_normalizer_iff.mp (hIN ((V ⊔ conjSub g⁻¹ V).inv_mem hvmem)) p).mp hp
    simpa using this
  have hiN : ∀ p ∈ Vp ⊔ conjSub g⁻¹ Vp, (g⁻¹ * a₀ * g) * p * (g⁻¹ * a₀ * g)⁻¹ ∈
      Vp ⊔ conjSub g⁻¹ Vp := fun p hp =>
    (Subgroup.mem_normalizer_iff.mp (hIN himem) p).mp hp
  have hiN' : ∀ p ∈ Vp ⊔ conjSub g⁻¹ Vp, (g⁻¹ * a₀ * g)⁻¹ * p * (g⁻¹ * a₀ * g) ∈
      Vp ⊔ conjSub g⁻¹ Vp := fun p hp => by
    have := (Subgroup.mem_normalizer_iff.mp (hIN ((V ⊔ conjSub g⁻¹ V).inv_mem himem)) p).mp hp
    simpa using this
  have hv₁ : ∀ z ∈ V₁, a₀ * z * a₀⁻¹ = z := fun z hz =>
    h.conj_eq_of_mem_V₁' (h.V_le_H ha₀V) hz
  have hi₁ : ∀ z ∈ V₁, (g⁻¹ * a₀ * g) * z * (g⁻¹ * a₀ * g)⁻¹ = z := fun z hz =>
    h.conj_eq_of_mem_V₁' (hVgH hb₀V) hz
  have hXY : Vp ⊓ conjSub g⁻¹ Vp = V₁ := by
    refine le_antisymm ?_ (le_inf h.V₁_le_Vp hV₁Vpg)
    intro x hx
    have hxH : x ∈ H := hUH (hVpU hx.1)
    have hbot : tildeOf V₁ (Vp ⊓ conjSub g⁻¹ Vp) = ⊥ := by
      rw [tildeOf_inf h.V₁_le_Vp]
      exact hFive.tilde_Vp_inf
    have hmem : toTilde hH ⟨x, hxH⟩ ∈ tildeOf V₁ (Vp ⊓ conjSub g⁻¹ Vp) :=
      (mem_tildeOf_iff hH (inf_le_left.trans (hVpU.trans hUH))).mpr ⟨⟨x, hxH⟩, hx, rfl⟩
    rw [hbot] at hmem
    exact (toTilde_eq_one_iff hH).mp (Subgroup.mem_bot.mp hmem)
  have hXe : ∀ x ∈ Vp, x * x = 1 := fun x hx => by
    have := isElemAbelian_pow_eq_one h.elemAbelian_Vp hx
    rwa [pow_two] at this
  have hXc : ∀ x ∈ Vp, ∀ x' ∈ Vp, x * x' = x' * x := fun x hx x' hx' =>
    isElemAbelian_comm h.elemAbelian_Vp hx hx'
  have hYabel : IsElemAbelian 2 (conjSub g⁻¹ Vp) := F7.isElemAbelian_conjSub h.elemAbelian_Vp
  have hYe : ∀ y ∈ conjSub g⁻¹ Vp, y * y = 1 := fun y hy => by
    have := isElemAbelian_pow_eq_one hYabel hy
    rwa [pow_two] at this
  have hYc : ∀ y ∈ conjSub g⁻¹ Vp, ∀ y' ∈ conjSub g⁻¹ Vp, y * y' = y' * y := fun y hy y' hy' =>
    isElemAbelian_comm hYabel hy hy'
  have hXYcard : Nat.card Vp = Nat.card (conjSub g⁻¹ Vp) := (card_conjSub _ _).symm
  have hcard : Nat.card V₁ = 2 := h.card_V₁
  have hjpos : 0 < j := by omega
  have hcase' : (Nat.card Vp = 2 ^ 3 ∧ ∃ p ∈ Vp ⊔ conjSub g⁻¹ Vp, ∃ r ∈ Vp ⊔ conjSub g⁻¹ Vp,
        p * r ≠ r * p) ∨
      (Nat.card Vp = 2 ^ 5 ∧ ∀ y ∈ conjSub g⁻¹ Vp, (∀ x ∈ Vp, y * x = x * y) → y ∈ V₁) := by
    rcases hcase with ⟨hj1, hc⟩ | ⟨hj2, hc⟩
    · left
      subst hj1
      refine ⟨by simpa using hX, ?_⟩
      by_contra hab
      push Not at hab
      have hYle : conjSub g⁻¹ Vp ≤ V₁ := fun y hy => by
        have hyP : y ∈ Vp ⊔ conjSub g⁻¹ Vp := Subgroup.mem_sup_right hy
        have hyC : y ∈ H ⊓ Subgroup.centralizer (Vp : Set G) :=
          ⟨hUH (hVpgU hy), Subgroup.mem_centralizer_iff.mpr fun x hx =>
            hab x (Subgroup.mem_sup_left hx) y hyP⟩
        have hcm : a₀ * y * a₀⁻¹ * y⁻¹ ∈ ⁅V, H ⊓ Subgroup.centralizer (Vp : Set G)⁆ :=
          Subgroup.commutator_mem_commutator ha₀V hyC
        have hyVp := (hD1 y hyP).mp (hc hcm)
        have hmem : y ∈ Vp ⊓ conjSub g⁻¹ Vp := ⟨hyVp, hy⟩
        rwa [hXY] at hmem
      have h1 := Subgroup.card_le_of_le hYle
      rw [← hXYcard, hX, hcard] at h1
      norm_num at h1
    · right
      subst hj2
      refine ⟨by simpa using hX, fun y hy hyc => ?_⟩
      have hyP : y ∈ Vp ⊔ conjSub g⁻¹ Vp := Subgroup.mem_sup_right hy
      have hyC : y ∈ H ⊓ Subgroup.centralizer (Vp : Set G) :=
        ⟨hUH (hVpgU hy), Subgroup.mem_centralizer_iff.mpr fun x hx => (hyc x hx).symm⟩
      rw [hc] at hyC
      have hcm : a₀ * y = y * a₀ := (Subgroup.mem_centralizer_iff.mp hyC.2 a₀ ha₀V)
      have e : a₀ * y * a₀⁻¹ * y⁻¹ = 1 := by rw [hcm]; group
      have hyVp := (hD1 y hyP).mp (by rw [e]; exact V₁.one_mem)
      have hmem : y ∈ Vp ⊓ conjSub g⁻¹ Vp := ⟨hyVp, hy⟩
      rwa [hXY] at hmem
  have hnd : ∀ p ∈ Vp ⊔ conjSub g⁻¹ Vp, (∀ r ∈ Vp ⊔ conjSub g⁻¹ Vp, p * r = r * p) → p ∈ V₁ :=
    RonanF95.center_le (V₁ := V₁) (P := Vp ⊔ conjSub g⁻¹ Vp) (Xg := Vp) (Yg := conjSub g⁻¹ Vp)
      (v := a₀) (i := g⁻¹ * a₀ * g) (hcard := hcard) (hV₁P := hV₁P) (hcen := hcen) (hsq := hsq)
      (hcomm := hcomm) (hvN := hvN) (hvN' := hvN') (hiN := hiN) (hiN' := hiN') (hv₁ := hv₁)
      (hi₁ := hi₁) (hv2 := ha₀₀) (hi2 := hi2) (hXP := hXP) (hYP := hYP) (hV₁X := h.V₁_le_Vp)
      (hV₁Y := hV₁Vpg) (hX1 := hD1) (hX2 := hD2) (hY1 := hD3) (hY2 := hD4) (hXY := hXY)
      (hXYs := rfl) (hXe := hXe) (hXc := hXc) (hYe := hYe) (hYc := hYc) (hXYcard := hXYcard)
      (hcase := hcase')
  have hXcases : Nat.card Vp = 2 ^ 3 ∨ Nat.card Vp = 2 ^ 5 := by
    rcases hj with rfl | rfl
    · left
      simpa using hX
    · right
      simpa using hX
  have hgm := RonanF95.ggt_main (V₁ := V₁) (P := Vp ⊔ conjSub g⁻¹ Vp) (Xg := Vp)
    (Yg := conjSub g⁻¹ Vp) (v := a₀) (i := g⁻¹ * a₀ * g) (hcard := hcard) (hV₁P := hV₁P)
    (hcen := hcen) (hsq := hsq) (hcomm := hcomm) (hvN := hvN) (hvN' := hvN') (hiN := hiN)
    (hiN' := hiN') (hv₁ := hv₁) (hi₁ := hi₁) (hv2 := ha₀₀) (hi2 := hi2) (hXP := hXP)
    (hYP := hYP) (hV₁X := h.V₁_le_Vp) (hV₁Y := hV₁Vpg) (hX1 := hD1) (hX2 := hD2) (hY1 := hD3)
    (hY2 := hD4) (hXY := hXY) (hXYs := rfl) (hXe := hXe) (hXc := hXc) (hYe := hYe) (hYc := hYc)
    (hXYcard := hXYcard) (hnd := hnd) (hX := hXcases)
  have hnab : ∃ p ∈ Vp ⊔ conjSub g⁻¹ Vp, ∃ r ∈ Vp ⊔ conjSub g⁻¹ Vp, p * r ≠ r * p := by
    by_contra hab
    push Not at hab
    have hle : Vp ≤ V₁ := fun x hx =>
      hnd x (Subgroup.mem_sup_left hx) fun r hr => hab x (Subgroup.mem_sup_left hx) r hr
    have h1 := Subgroup.card_le_of_le hle
    rw [hX, hcard] at h1
    rcases hj with rfl | rfl <;> norm_num at h1
  have hQ8 := RonanF95.isQ8CentralPow_of_special (V₁ := V₁) (P := Vp ⊔ conjSub g⁻¹ Vp)
    (Xg := Vp) (Yg := conjSub g⁻¹ Vp) hcard hV₁P hcen hsq hcomm hnd hXP hYP h.V₁_le_Vp hV₁Vpg
    hXY rfl hXe hXc hYe hYc hXYcard hjpos hX hnab
  refine ⟨hQ8, ?_⟩
  obtain ⟨σ, τ, -, -, hcl, hσ2, hτ2, hord⟩ :=
    h.F95_gens hidx hV hyp5 hg hI ha₀V ha₀₀ hZV ha₀Q
  have hk2 : ¬ (σ * τ) ^ 2 = 1 := by
    intro h2
    obtain ⟨p, hp, hpn⟩ := hgm.1
    exact hpn ((hord 2).mp h2 p hp)
  have h1ne : orderOf (σ * τ) ≠ 1 := fun h1 => hk2 (by rw [orderOf_eq_one_iff.mp h1]; simp)
  have h2ne : orderOf (σ * τ) ≠ 2 := fun h2 => hk2 (by rw [← h2]; exact pow_orderOf_eq_one _)
  have hdih : ∀ m, 3 ≤ m → orderOf (σ * τ) = m →
      Nonempty (↥(autOn (tildeOf V₁ (V ⊔ conjSub g⁻¹ V)) (tildeOf V₁ (conjClosure Vp H))) ≃*
        DihedralGroup m) := fun m hm hom => by
    obtain ⟨e⟩ := RonanF95.nonempty_mulEquiv_dihedral hm hσ2 hτ2 hom
    rw [hcl] at e
    exact ⟨e⟩
  rcases hgm.2 with h3 | ⟨h5', h56⟩
  · have h3' : (σ * τ) ^ 3 = 1 := (hord 3).mpr h3
    have hdvd : orderOf (σ * τ) ∣ 3 := orderOf_dvd_of_pow_eq_one h3'
    have hm3 : orderOf (σ * τ) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · exact absurd h1 h1ne
      · exact h1
    exact ⟨3, Or.inl rfl, hdih 3 le_rfl hm3⟩
  · have hj2 : j = 2 := by
      rcases hj with rfl | rfl
      · exfalso
        rw [hX] at h5'
        norm_num at h5'
      · rfl
    rcases h56 with h5 | h6
    · have h5' : (σ * τ) ^ 5 = 1 := (hord 5).mpr h5
      have hdvd : orderOf (σ * τ) ∣ 5 := orderOf_dvd_of_pow_eq_one h5'
      have hm5 : orderOf (σ * τ) = 5 := by
        rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h1
        · exact absurd h1 h1ne
        · exact h1
      exact ⟨5, Or.inr ⟨hj2, Or.inl rfl⟩, hdih 5 (by norm_num) hm5⟩
    · have h6' : (σ * τ) ^ 6 = 1 := (hord 6).mpr h6
      have hdvd : orderOf (σ * τ) ∣ 6 := orderOf_dvd_of_pow_eq_one h6'
      have hle : orderOf (σ * τ) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      have hm36 : orderOf (σ * τ) = 3 ∨ orderOf (σ * τ) = 6 := by
        generalize orderOf (σ * τ) = m at hdvd hle h1ne h2ne
        interval_cases m <;> omega
      rcases hm36 with hm3 | hm6
      · exact ⟨3, Or.inl rfl, hdih 3 le_rfl hm3⟩
      · exact ⟨6, Or.inr ⟨hj2, Or.inr rfl⟩, hdih 6 (by norm_num) hm6⟩

theorem card_V_eq (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2) :
    Nat.card V = Nat.card Vp * 2 := by
  have h1 := Subgroup.card_mul_index (Vp.subgroupOf V)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Vp_le_V).toEquiv] at h1
  rw [← h1]
  change Nat.card Vp * Vp.relIndex V = _
  rw [hidx]

theorem F95_six (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2) (hV : ¬ V ≤ pCoreOf 2 H)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    {g : G} (hg : g ∈ H)
    (hI : ¬ ∀ x ∈ V ⊔ conjSub g⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H)
    (hc : ⁅V, H ⊓ Subgroup.centralizer (Vp : Set G)⁆ ≤ V₁) :
    (Nat.card V = 2 ^ 4 →
      CFSG.Quasithin.H13.IsQ8CentralPow 2 ↥(Vp ⊔ conjSub g⁻¹ Vp) ∧
        Nonempty (↥(autOn (tildeOf V₁ (V ⊔ conjSub g⁻¹ V)) (tildeOf V₁ (conjClosure Vp H))) ≃*
          DihedralGroup 3)) ∧
    (Nat.card V = 2 ^ 6 →
      H ⊓ Subgroup.centralizer (Vp : Set G) = H ⊓ Subgroup.centralizer (V : Set G) →
      CFSG.Quasithin.H13.IsQ8CentralPow 4 ↥(Vp ⊔ conjSub g⁻¹ Vp) ∧
        (Nonempty (↥(autOn (tildeOf V₁ (V ⊔ conjSub g⁻¹ V)) (tildeOf V₁ (conjClosure Vp H))) ≃*
            DihedralGroup 3) ∨
          Nonempty (↥(autOn (tildeOf V₁ (V ⊔ conjSub g⁻¹ V)) (tildeOf V₁ (conjClosure Vp H))) ≃*
            DihedralGroup 5) ∨
          Nonempty (↥(autOn (tildeOf V₁ (V ⊔ conjSub g⁻¹ V)) (tildeOf V₁ (conjClosure Vp H))) ≃*
            DihedralGroup 6))) := by
  have hcV := h.card_V_eq hidx
  refine ⟨fun h4 => ?_, fun h6 hC => ?_⟩
  · have hX : Nat.card Vp = 2 ^ (2 * 1 + 1) := by omega
    obtain ⟨hQ, m, hm, hD⟩ := h.F95_six_core hidx hV hyp5 hg hI (j := 1) (Or.inl rfl) hX
      (Or.inl ⟨rfl, hc⟩)
    refine ⟨hQ, ?_⟩
    rcases hm with rfl | ⟨hj, -⟩
    · exact hD
    · omega
  · have hX : Nat.card Vp = 2 ^ (2 * 2 + 1) := by omega
    obtain ⟨hQ, m, hm, hD⟩ := h.F95_six_core hidx hV hyp5 hg hI (j := 2) (Or.inr rfl) hX
      (Or.inr ⟨rfl, hC⟩)
    refine ⟨hQ, ?_⟩
    rcases hm with rfl | ⟨-, rfl | rfl⟩
    · exact Or.inl hD
    · exact Or.inr (Or.inl hD)
    · exact Or.inr (Or.inr hD)

end HypF91

end Fin

end CFSG.Quasithin
