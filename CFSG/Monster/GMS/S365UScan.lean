module

public import CFSG.Monster.GMS.S365UKInputs
public import CFSG.Certificates.Kernel.Co1M.U45Sound
public import CFSG.Sporadic.Co1.Module.OddLit
public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Sporadic.Co1.Module.OddNative

public section

namespace CFSG.Monster.GMS.S365

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.Module.Odd CFSG.KC.U45 CFSG.KC.SortTree CFSG.KC.Co1F2 CFSG.KC.M1F2
  CFSG.KC.Odd73

@[expose] def Good45 (a b c : Co1) (v : Fin 24 → ZMod 2) : Prop :=
  v ∈ co1Orbit 2 ∧ (∃ p, v = p + co1Act a p) ∧ (∃ p, v = p + co1Act b p) ∧
    ∃ p, v = p + co1Act c p

@[expose] def UK45 (nw : ℕ) (a b : Co1) : Prop :=
  ∃ v₁ v₂, (2 ≤ nw → v₁ ≠ v₂) ∧ Good45 a b (a * b) v₁ ∧ Good45 a b (a * b) v₂

theorem good45_conj (g : Co1) {a b c : Co1} {v : Fin 24 → ZMod 2} (h : Good45 a b c v) :
    Good45 (g * a * g⁻¹) (g * b * g⁻¹) (g * c * g⁻¹) (co1Act g v) := by
  obtain ⟨hv, ⟨p₁, h₁⟩, ⟨p₂, h₂⟩, ⟨p₃, h₃⟩⟩ := h
  have key : ∀ (c : Co1) (p : Fin 24 → ZMod 2),
      co1Act (g * c * g⁻¹) (co1Act g p) = co1Act g (co1Act c p) := fun c p => by
    calc co1Act (g * c * g⁻¹) (co1Act g p) = (co1Act (g * c * g⁻¹) * co1Act g) p :=
          (Module.End.mul_apply _ _ _).symm
      _ = co1Act (g * c * g⁻¹ * g) p := by rw [← map_mul]
      _ = co1Act (g * c) p := by rw [show g * c * g⁻¹ * g = g * c by group]
      _ = co1Act g (co1Act c p) := by rw [map_mul, Module.End.mul_apply]
  refine ⟨Leech.co1Act_mem_co1Orbit hv g, ⟨co1Act g p₁, ?_⟩, ⟨co1Act g p₂, ?_⟩,
    ⟨co1Act g p₃, ?_⟩⟩
  · rw [key, ← map_add, ← h₁]
  · rw [key, ← map_add, ← h₂]
  · rw [key, ← map_add, ← h₃]

theorem UK45.conj {nw : ℕ} {a b : Co1} (h : UK45 nw a b) (g : Co1) :
    UK45 nw (g * a * g⁻¹) (g * b * g⁻¹) := by
  obtain ⟨v₁, v₂, hne, h1, h2⟩ := h
  have hprod : g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
  have hinv : ∀ u : Fin 24 → ZMod 2, co1Act g⁻¹ (co1Act g u) = u := fun u => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  refine ⟨co1Act g v₁, co1Act g v₂, fun hn e => hne hn (by rw [← hinv v₁, ← hinv v₂, e]), ?_, ?_⟩
  · rw [hprod]
    exact good45_conj g h1
  · rw [hprod]
    exact good45_conj g h2

theorem UK45.swap {nw : ℕ} {a b : Co1} (h : UK45 nw a b) (hab : a * b = b * a) : UK45 nw b a := by
  obtain ⟨v₁, v₂, hne, ⟨g1, a1, b1, c1⟩, ⟨g2, a2, b2, c2⟩⟩ := h
  rw [hab] at c1 c2
  exact ⟨v₁, v₂, hne, ⟨g1, b1, a1, c1⟩, ⟨g2, b2, a2, c2⟩⟩

theorem UK45.toMul {nw : ℕ} {a b : Co1} (h : UK45 nw a b) (ha : a * a = 1) :
    UK45 nw a (a * b) := by
  obtain ⟨v₁, v₂, hne, ⟨g1, a1, b1, c1⟩, ⟨g2, a2, b2, c2⟩⟩ := h
  have e : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  refine ⟨v₁, v₂, hne, ⟨g1, a1, c1, ?_⟩, ⟨g2, a2, c2, ?_⟩⟩
  · rw [e]
    exact b1
  · rw [e]
    exact b2

theorem act45 {x : Co1} {M : ℕ} (hx : PM73 x M) (p : ℕ) :
    toVecD 24 (opK (trK 24 M) p) = toVecD 24 p + co1Act x (toVecD 24 p) := by
  have e : opK (trK 24 M) p = p ^^^ vmF 24 (trK 24 M) p := rfl
  rw [e, toVecD_xor, ← pm73_act hx p]
  rfl

theorem good45_of_wit
    {a b : Co1} {A B : ℕ}
    (ha : PM73 a A) (hb : PM73 b B) {e : List ℕ} {o : ℕ}
    (hw : witK (trK 24 A) (trK 24 B) (trK 24 (mulF 24 A B)) e o = true)
    (h4 : type4U (getL 0 e o) = true) :
    getL 0 e o < 2 ^ 24 ∧ Good45 a b (a * b) (toVecD 24 (getL 0 e o)) := by
  obtain ⟨hlt, h1, h2, h3⟩ := witK_spec hw
  refine ⟨hlt, ?_, ⟨toVecD 24 (getL 0 e (o + 1)), ?_⟩, ⟨toVecD 24 (getL 0 e (o + 2)), ?_⟩,
    ⟨toVecD 24 (getL 0 e (o + 3)), ?_⟩⟩
  · rw [CFSG.Sporadic.Co1.Module.Pairs.co1Orbit_two, CFSG.Sporadic.Co1.Module.Pairs.orbit_Co1_eq]
    exact (type4N_iff _ hlt).1 h4
  · rw [← act45 ha, h1]
  · rw [← act45 hb, h2]
  · rw [← act45 (pm73_mul ha hb), h3]

theorem uk45_of_wit2
    {nw : ℕ} {a b : Co1}
    {A B : ℕ} (ha : PM73 a A) (hb : PM73 b B) {e : List ℕ}
    (hw : wit2K nw (trK 24 A) (trK 24 B) (trK 24 (mulF 24 A B)) e = true)
    (h4 : type4U (getL 0 e 2) = true ∧ type4U (getL 0 e (lastO nw)) = true) : UK45 nw a b := by
  obtain ⟨w1, w2, hd⟩ := wit2K_spec hw
  obtain ⟨l1, g1⟩ := good45_of_wit ha hb w1 h4.1
  obtain ⟨l2, g2⟩ := good45_of_wit ha hb w2 h4.2
  exact ⟨_, _, fun hn e => hd hn (toVecD_injective l1 l2 e), g1, g2⟩

section Scan

variable {W : OddW} {H : Subgroup Co1}

theorem s73_conj45 {n t : Co1} (hn : n ∈ H) (ht : t ∈ S73 H) : n * t * n⁻¹ ∈ S73 H :=
  ⟨H.mul_mem (H.mul_mem hn ht.1) (H.inv_mem hn), ht.2.trans (isConj_iff.2 ⟨n, rfl⟩)⟩

theorem cl73_conj45 {n t : Co1} (hn : n ∈ H) (ht : t ∈ Cl73 H) : n * t * n⁻¹ ∈ Cl73 H := by
  obtain ⟨m, hm, rfl⟩ := ht
  exact ⟨n * m, H.mul_mem hn hm, by group⟩

theorem rho_ne_one45 (hS : (S73 H).ncard = 182919) : reg 27 ≠ 1 := by
  intro h1
  have := finite73
  have hsub : S73 H ⊆ {1} := fun t ht => by
    have h := ht.2
    rw [h1] at h
    exact isConj_one_right.1 h
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hS, Set.ncard_singleton] at h
  omega

theorem bray45 (hW : OddOK W) (hH : OddHyp73 H) {SI : List ℕ}
    (hst : ∀ i < nS, stRec W.T.wl W.T.wp W.T.tab SI i = true) :
    ∀ i < nS, ∀ y, PM73 y (val73 W i) → ∃ c ∈ H ⊓ Subgroup.centralizer {reg 27}, ∃ s < nS,
      s ∈ SI ∧ ∃ z, PM73 z (val73 W s) ∧ y = c * z * c⁻¹ := by
  suffices key : ∀ L i, i < nS → levF 576 W.T.wl (W.T.tab i) ≤ L → ∀ y, PM73 y (val73 W i) →
      ∃ c ∈ H ⊓ Subgroup.centralizer {reg 27}, ∃ s < nS, s ∈ SI ∧ ∃ z, PM73 z (val73 W s) ∧
        y = c * z * c⁻¹ from
    fun i hi => key _ i hi le_rfl
  intro L
  induction L with
  | zero =>
    intro i hi hL y hy
    rcases stRec_spec (hst i hi) with ⟨h0, -⟩ | hm
    · exact absurd (Nat.le_zero.1 hL) h0
    · exact ⟨1, Subgroup.one_mem _, i, hi, hm, y, hy, by group⟩
  | succ L ih =>
    intro i hi hL y hy
    rcases stRec_spec (hst i hi) with ⟨h0, hl8⟩ | hm
    · obtain ⟨hp, -, hlev, hact⟩ := (rec73_spec hW hi).2 h0
      have hl10 : letF 576 W.T.wl W.T.wp (W.T.tab i) < 10 := by omega
      obtain ⟨xp, hxp, -⟩ := rec73_sem hW hH _ hp
      have hb := pm73_letter hW hl10
      have hbi : PM73 (reg (getL 0 I73 (letF 576 W.T.wl W.T.wp (W.T.tab i))))⁻¹
          (getL 0 W.R (getL 0 Ii73 (letF 576 W.T.wl W.T.wp (W.T.tab i)))) := by
        have := pm73_letteri hW hl10
        rwa [hH.gen_inv _ hl10] at this
      have hX : PM73 (reg (getL 0 I73 (letF 576 W.T.wl W.T.wp (W.T.tab i))) * xp *
          (reg (getL 0 I73 (letF 576 W.T.wl W.T.wp (W.T.tab i))))⁻¹) (val73 W i) := by
        rw [← hact, act73_lt hl10]
        exact pm73_conj hxp hb hbi
      have hyx := pm73_inj hy hX
      obtain ⟨c, hc, s, hs, hsm, z, hz, e⟩ := ih _ hp (by omega) xp hxp
      refine ⟨reg (getL 0 I73 (letF 576 W.T.wl W.T.wp (W.T.tab i))) * c,
        Subgroup.mul_mem _ (Subgroup.mem_inf.2 ⟨hH.gen_mem _ hl10,
          Subgroup.mem_centralizer_singleton_iff.2 (hH.bray _ hl8)⟩) hc, s, hs, hsm, z, hz, ?_⟩
      rw [hyx, e]
      group
    · exact ⟨1, Subgroup.one_mem _, i, hi, hm, y, hy, by group⟩


theorem start45 (hW : OddOK W) (hH : OddHyp73 H) (hS : (S73 H).ncard = 182919) {nw : ℕ}
    {U : UW} (hU : UOK W nw U) {e : List ℕ} (he : e ∈ U.SE) {y : Co1}
    (hy : PM73 y (val73 W (getL 0 e 0))) (hc : y * reg 27 = reg 27 * y)
    (hm : reg 27 * y ∈ S73 H) : UK45 nw (reg 27) y := by
  obtain ⟨x, hx, hinj⟩ := recs73 hW hH
  have hSeq := s73_eq hH hS hx hinj
  have h27 : PM73 (reg 27) (W.reg 27) := pm73_reg hW (by norm_num)
  obtain ⟨-, hcase⟩ := stE_spec ((allE_iff _ _).1 hU.se e he)
  rcases hcase with hne | hgap | hwit
  · exact absurd (pm73_eq (pm73_mul h27 hy) (pm73_mul hy h27) (canon73_mulF _ _)
      (canon73_mulF _ _) hc.symm) hne
  · rw [← hSeq] at hm
    obtain ⟨k, hk, hxk⟩ := hm
    exact absurd (pm73_eq (hx k hk).1 (pm73_mul h27 hy) (canon73_val hW hk) (canon73_mulF _ _) hxk)
      (gapK_spec hgap (fun i j hij hj => val73_strict hW hij hj) k hk)
  · exact uk45_of_wit2 h27 hy hwit (hU.t4 e (List.mem_append_left _ he))

theorem c545 (hW : OddOK W) (hH : OddHyp73 H) (hS : (S73 H).ncard = 182919) {nw : ℕ}
    {U : UW} (hU : UOK W nw U) {e : List ℕ} (he : e ∈ U.CE) {y : Co1}
    (hy : PM73 y (val73 W (getL 0 e 0))) (hm : reg 86 * y ∈ S73 H) (hn : reg 86 * y ∉ Cl73 H) :
    UK45 nw (reg 86) y := by
  obtain ⟨x, hx, hinj⟩ := recs73 hW hH
  have hSeq := s73_eq hH hS hx hinj
  have h86 : PM73 (reg 86) (W.reg 86) := pm73_reg hW (by norm_num)
  obtain ⟨-, -, hcase⟩ := c5E_spec ((allE_iff _ _).1 hU.ce e he)
  rcases hcase with hX | hgap | ⟨hj, hjv, hj5⟩ | hwit
  · have hy' : PM73 y (W.reg 86) := by
      have : val73 W (getL 0 e 0) = W.reg 86 := hX
      rwa [this] at hy
    have e1 : y = reg 86 := pm73_inj hy' h86
    have hsq : reg 86 * reg 86 = 1 :=
      @sq_of_conj73 Co1 _ (reg 27) (reg 86) hH.ρ_sq hH.t₁_conj
    rw [e1, hsq] at hm
    exact absurd (isConj_one_right.1 hm.2.symm) (rho_ne_one45 hS)
  · rw [← hSeq] at hm
    obtain ⟨k, hk, hxk⟩ := hm
    exact absurd (pm73_eq (hx k hk).1 (pm73_mul h86 hy) (canon73_val hW hk) (canon73_mulF _ _) hxk)
      (gapK_spec hgap (fun i j hij hj => val73_strict hW hij hj) k hk)
  · have hxj : PM73 (x (getL 0 e 1)) (mulF 24 (W.reg 86) (val73 W (getL 0 e 0))) := by
      have := (hx _ hj).1
      have e2 : val73 W (getL 0 e 1) = mulF 24 (W.reg 86) (val73 W (getL 0 e 0)) := hjv
      rwa [e2] at this
    have e3 : x (getL 0 e 1) = reg 86 * y := pm73_inj hxj (pm73_mul h86 hy)
    exact absurd (by rw [← e3]; exact sem73_conj hH (hx _ hj).2 hj5) hn
  · exact uk45_of_wit2 h86 hy hwit (hU.t4 e (List.mem_append_right _ he))

theorem cover545 (hW : OddOK W) {nw : ℕ} {U : UW} (hU : UOK W nw U) :
    ∀ i < nS, clsA (W.aux i) = 5 → ∃ e ∈ U.CE, getL 0 e 0 = i := by
  classical
  intro i hi h5
  obtain ⟨-, hnd⟩ := incE_spec U.CE 0 hU.cinc
  have hlen : (headsE U.CE).length = 759 := by
    rw [headsE_eq, List.length_map, ← lenE_eq]
    exact hU.clen
  have hsub : (headsE U.CE).toFinset ⊆ (Finset.range nS).filter (fun j => clsA (W.aux j) = 5) := by
    intro h hh
    rw [List.mem_toFinset, headsE_eq, List.mem_map] at hh
    obtain ⟨e, he, rfl⟩ := hh
    obtain ⟨hlt, hc, -⟩ := c5E_spec ((allE_iff _ _).1 hU.ce e he)
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hlt, hc⟩
  have hcard : ((Finset.range nS).filter (fun j => clsA (W.aux j) = 5)).card = 759 := by
    have h := cnt73 hW (c := 3) (by norm_num)
    have e3 : {i | i < nS ∧ clsA (W.aux i) = 3 + 2} =
        ↑((Finset.range nS).filter (fun j => clsA (W.aux j) = 5)) := by
      ext i
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
    have e4 : getL 0 [7168, 2048, 28672, 759] 3 = 759 := rfl
    rw [e3, Set.ncard_coe_finset, e4] at h
    exact h
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [hcard, List.toFinset_card_of_nodup hnd, hlen])
  have hmem : i ∈ (headsE U.CE).toFinset := by
    rw [heq]
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, h5⟩
  rw [List.mem_toFinset, headsE_eq, List.mem_map] at hmem
  exact hmem

theorem uk45_of_S (hW : OddOK W) {nw : ℕ} {U : UW} (hU : UOK W nw U) (hH : OddHyp73 H)
    (hS : (S73 H).ncard = 182919) {a b : Co1} (ha : a ∈ S73 H) (hb : b ∈ S73 H)
    (hab : a * b = b * a) (hab' : a * b ∈ S73 H) : UK45 nw a b := by
  obtain ⟨x, hx, hinj⟩ := recs73 hW hH
  have hSeq := s73_eq hH hS hx hinj
  have hheads := (eqL_iff _ _).1 hU.heads
  have hρ : ∀ d ∈ S73 H, d * reg 27 = reg 27 * d → reg 27 * d ∈ S73 H → UK45 nw (reg 27) d := by
    intro d hd hc hm
    rw [← hSeq] at hd
    obtain ⟨i, hi, rfl⟩ := hd
    obtain ⟨c, hcK, s, -, hsm, z, hz, e⟩ := bray45 hW hH hU.st i hi (x i) (hx i hi).1
    obtain ⟨hcH, hcρ⟩ := Subgroup.mem_inf.1 hcK
    have hcρ' : c * reg 27 = reg 27 * c :=
      (Subgroup.mem_centralizer_iff.1 hcρ (reg 27) (Set.mem_singleton _)).symm
    have hci : c⁻¹ * reg 27 = reg 27 * c⁻¹ := by
      calc c⁻¹ * reg 27 = c⁻¹ * (reg 27 * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * reg 27) * c⁻¹ := by rw [hcρ']
        _ = reg 27 * c⁻¹ := by group
    have hzc : z = c⁻¹ * x i * c := by
      rw [e]
      group
    have hzρ : z * reg 27 = reg 27 * z := by
      calc z * reg 27 = c⁻¹ * x i * (c * reg 27) := by
            rw [hzc]
            group
        _ = c⁻¹ * x i * (reg 27 * c) := by rw [hcρ']
        _ = c⁻¹ * (x i * reg 27) * c := by group
        _ = c⁻¹ * (reg 27 * x i) * c := by rw [hc]
        _ = (c⁻¹ * reg 27) * x i * c := by group
        _ = (reg 27 * c⁻¹) * x i * c := by rw [hci]
        _ = reg 27 * z := by
            rw [hzc]
            group
    have hzm : reg 27 * z ∈ S73 H := by
      have e1 : reg 27 * z = c⁻¹ * (reg 27 * x i) * c⁻¹⁻¹ := by
        calc reg 27 * z = (reg 27 * c⁻¹) * x i * c := by
              rw [hzc]
              group
          _ = (c⁻¹ * reg 27) * x i * c := by rw [hci]
          _ = c⁻¹ * (reg 27 * x i) * c⁻¹⁻¹ := by group
      rw [e1]
      exact s73_conj45 (H.inv_mem hcH) hm
    rw [← hheads, headsE_eq, List.mem_map] at hsm
    obtain ⟨en, hen, hens⟩ := hsm
    have hz' : PM73 z (val73 W (getL 0 en 0)) := by
      rw [hens]
      exact hz
    have h := (start45 hW hH hS hU hen hz' hzρ hzm).conj c
    have e2 : c * reg 27 * c⁻¹ = reg 27 := by
      rw [hcρ']
      group
    rwa [e2, ← e] at h
  have hcl : ∀ c ∈ Cl73 H, ∀ d ∈ S73 H, c * d = d * c → c * d ∈ S73 H → UK45 nw c d := by
    intro c hc d hd hcd hcd'
    obtain ⟨n, hn, rfl⟩ := hc
    have hd' : n⁻¹ * d * n ∈ S73 H := by
      have := s73_conj45 (H.inv_mem hn) hd
      rwa [inv_inv] at this
    have hm' : reg 27 * (n⁻¹ * d * n) ∈ S73 H := by
      have e1 : reg 27 * (n⁻¹ * d * n) = n⁻¹ * (n * reg 27 * n⁻¹ * d) * n⁻¹⁻¹ := by group
      rw [e1]
      exact s73_conj45 (H.inv_mem hn) hcd'
    have hc' : n⁻¹ * d * n * reg 27 = reg 27 * (n⁻¹ * d * n) := by
      calc n⁻¹ * d * n * reg 27 = n⁻¹ * (d * (n * reg 27 * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * reg 27 * n⁻¹) * d) * n := by rw [hcd]
        _ = reg 27 * (n⁻¹ * d * n) := by group
    have h := (hρ _ hd' hc' hm').conj n
    have e2 : n * (n⁻¹ * d * n) * n⁻¹ = d := by group
    rwa [e2] at h
  have ht1 : ∀ a ∈ S73 H, a ∉ Cl73 H → ∀ b ∈ S73 H, b ∉ Cl73 H → a * b ∈ S73 H →
      a * b ∉ Cl73 H → UK45 nw a b := by
    intro a ha hna b hb hnb hab' hnab
    obtain ⟨n, hn, hor⟩ := S_cover73 hW hH hS a ha
    rcases hor with hor | hor
    swap
    · exact absurd ⟨n, hn, hor⟩ hna
    have hb' : n⁻¹ * b * n ∈ S73 H := by
      have := s73_conj45 (H.inv_mem hn) hb
      rwa [inv_inv] at this
    have hnb' : n⁻¹ * b * n ∉ Cl73 H := fun h => hnb (by
      have := cl73_conj45 hn h
      rwa [show n * (n⁻¹ * b * n) * n⁻¹ = b by group] at this)
    have e1 : reg 86 * (n⁻¹ * b * n) = n⁻¹ * (a * b) * n⁻¹⁻¹ := by
      rw [hor]
      group
    have hm : reg 86 * (n⁻¹ * b * n) ∈ S73 H := by
      rw [e1]
      exact s73_conj45 (H.inv_mem hn) hab'
    have hnm : reg 86 * (n⁻¹ * b * n) ∉ Cl73 H := fun h => hnab (by
      have := cl73_conj45 hn h
      rwa [e1, show n * (n⁻¹ * (a * b) * n⁻¹⁻¹) * n⁻¹ = a * b by group] at this)
    rw [← hSeq] at hb'
    obtain ⟨i, hi, hxi⟩ := hb'
    have h5 : clsA (W.aux i) = 5 := by
      by_contra h5
      exact hnb' (hxi ▸ sem73_conj hH (hx i hi).2 h5)
    obtain ⟨e, he, hei⟩ := cover545 hW hU i hi h5
    have hy : PM73 (x i) (val73 W (getL 0 e 0)) := by
      rw [hei]
      exact (hx i hi).1
    rw [← hxi] at hm hnm
    have h := (c545 hW hH hS hU he hy hm hnm).conj n
    rwa [← hor, hxi, show n * (n⁻¹ * b * n) * n⁻¹ = b by group] at h
  by_cases hA : a ∈ Cl73 H
  · exact hcl a hA b hb hab hab'
  by_cases hB : b ∈ Cl73 H
  · exact (hcl b hB a ha hab.symm (by rw [← hab]; exact hab')).swap hab.symm
  by_cases hAB : a * b ∈ Cl73 H
  · have haa : a * a = 1 := @sq_of_conj73 Co1 _ (reg 27) a hH.ρ_sq ha.2
    have e1 : a * b * a = b := by
      calc a * b * a = b * a * a := by rw [hab]
        _ = b := by rw [mul_assoc, haa, mul_one]
    have e2 : a * b * a = a * (a * b) := by rw [e1, ← mul_assoc, haa, one_mul]
    have h := ((hcl (a * b) hAB a ha e2 (by rw [e1]; exact hb)).swap e2).toMul haa
    rwa [← mul_assoc, haa, one_mul] at h
  · exact ht1 a ha hA b hb hB hab' hAB

end Scan

end CFSG.Monster.GMS.S365

end
