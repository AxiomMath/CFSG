module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeA1

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G} {F0 : Type} [Field F0] [Finite F0]
  [CharP F0 2] {m : ℕ} {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)}

private noncomputable def qtwoDB3_a2_chart (hbase : QTwoUnitBase p B Bs x L ψ ε) :
    ↥Bs → Fin m → F0ˣ :=
  fun s => Classical.choose (qtwoDB3_ind_exists hbase s.2)

private theorem qtwoDB3_a2_chart_spec (hbase : QTwoUnitBase p B Bs x L ψ ε) (s : ↥Bs) :
    qTwoChartTwoThree_induces ψ (s : G) (qtwoDB3_a2_chart hbase s) :=
  Classical.choose_spec (qtwoDB3_ind_exists hbase s.2)

private theorem qtwoDB3_a2_ratio_eq (hbase : QTwoUnitBase p B Bs x L ψ ε) (hm3 : 3 ≤ m)
    {a b : Fin m} {s : G} {c c' : Fin m → F0ˣ}
    (hc : qTwoChartTwoThree_induces ψ s c) (hc' : qTwoChartTwoThree_induces ψ s c') :
    c' a * (c' b)⁻¹ = c a * (c b)⁻¹ := by
  obtain ⟨l, hl⟩ := qtwoDB3_ind_scalar hbase.card_field hm3 hbase.hyp.ker hc hc'
  rw [hl a, hl b, mul_comm l (c a), mul_comm l (c b)]
  group

private theorem qtwoDB3_a2_ratio_apply (hbase : QTwoUnitBase p B Bs x L ψ ε) (hm3 : 3 ≤ m)
    {a b : Fin m} (s : ↥Bs) {c : Fin m → F0ˣ}
    (hc : qTwoChartTwoThree_induces ψ (s : G) c) :
    qtwoDB3_a2_chart hbase s a * (qtwoDB3_a2_chart hbase s b)⁻¹ = c a * (c b)⁻¹ :=
  qtwoDB3_a2_ratio_eq hbase hm3 hc (qtwoDB3_a2_chart_spec hbase s)

private noncomputable def qtwoDB3_a2_ratioHom (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hm3 : 3 ≤ m) (a b : Fin m) : ↥Bs →* F0ˣ :=
  MonoidHom.mk' (fun s => qtwoDB3_a2_chart hbase s a * (qtwoDB3_a2_chart hbase s b)⁻¹)
    (by
      intro s t
      have h1 : qTwoChartTwoThree_induces ψ ((s : G) * (t : G))
          (qtwoDB3_a2_chart hbase s * qtwoDB3_a2_chart hbase t) :=
        qtwoDB3_ind_mul (qtwoDB3_a2_chart_spec hbase s) (qtwoDB3_a2_chart_spec hbase t)
      have h2 : qTwoChartTwoThree_induces ψ ((s : G) * (t : G))
          (qtwoDB3_a2_chart hbase (s * t)) := by
        simpa only [Subgroup.coe_mul] using qtwoDB3_a2_chart_spec hbase (s * t)
      have h := qtwoDB3_a2_ratio_eq hbase hm3 (a := a) (b := b) h1 h2
      rw [h]
      simp only [Pi.mul_apply, mul_inv_rev]
      ac_rfl)

theorem qtwoDB3_exists_Hab (hbase : QTwoUnitBase p B Bs x L ψ ε) (hm : 5 ≤ m) {a b : Fin m}
    (hab : a ≠ b) :
    ∃ H : Subgroup G, H ≤ Bs ∧ x ∈ H ∧ Nat.card ↥Bs = 3 * Nat.card ↥H ∧
      ∀ s : ↥Bs, ((s : G) ∈ H ↔
        ∀ c : Fin m → F0ˣ, qTwoChartTwoThree_induces ψ (s : G) c → c a = c b) := by
  classical
  have hm3 : 3 ≤ m := by omega
  let r : ↥Bs →* F0ˣ := qtwoDB3_a2_ratioHom hbase hm3 a b
  have hF0units : Nat.card F0ˣ = 3 := by
    rw [Nat.card_units, hbase.card_field]
  have hrange : Nat.card ↥r.range = 3 := by
    haveI : Fintype F0 := Fintype.ofFinite F0
    haveI : Fintype F0ˣ := Fintype.ofFinite F0ˣ
    have hcard3 : Fintype.card F0ˣ = 3 := by
      rw [← Nat.card_eq_fintype_card, hF0units]
    obtain ⟨ω, hω⟩ := Fintype.exists_ne_of_one_lt_card (by rw [hcard3]; norm_num) (1 : F0ˣ)
    have hωmem : ω ∈ r.range := by
      obtain ⟨b₀, hb₀Bs, hb₀ind⟩ := hbase.full (Function.update (fun _ : Fin m => 1) a ω)
      refine MonoidHom.mem_range.mpr ⟨⟨b₀, hb₀Bs⟩, ?_⟩
      have hratio := qtwoDB3_a2_ratio_apply hbase hm3 (a := a) (b := b)
        ⟨b₀, hb₀Bs⟩ hb₀ind
      show qtwoDB3_a2_chart hbase ⟨b₀, hb₀Bs⟩ a *
        (qtwoDB3_a2_chart hbase ⟨b₀, hb₀Bs⟩ b)⁻¹ = ω
      rw [hratio]
      simp [Function.update_of_ne (a := b) (a' := a) (Ne.symm hab)]
    have hrange_ne_bot : r.range ≠ ⊥ := by
      intro hbot
      rw [hbot] at hωmem
      exact hω (by simpa using hωmem)
    have h1lt : 1 < Nat.card ↥r.range := by
      by_contra hle
      exact hrange_ne_bot (Subgroup.eq_bot_of_card_le (H := r.range) (Nat.le_of_not_lt hle))
    have hdvd : Nat.card ↥r.range ∣ 3 := by
      have h := Subgroup.card_subgroup_dvd_card r.range
      rwa [hF0units] at h
    rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd (Nat.card ↥r.range) hdvd with
      h | h
    · omega
    · exact h
  refine ⟨r.ker.map Bs.subtype, Subgroup.map_subtype_le r.ker, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_map]
    refine ⟨⟨x, hbase.x_mem⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    obtain ⟨l, hl⟩ := (qtwoDB3_ind_ker hbase hm3 hbase.x_mem
      (qtwoDB3_a2_chart_spec hbase ⟨x, hbase.x_mem⟩)).2 (Subgroup.mem_zpowers x)
    show qtwoDB3_a2_chart hbase ⟨x, hbase.x_mem⟩ a *
      (qtwoDB3_a2_chart hbase ⟨x, hbase.x_mem⟩ b)⁻¹ = 1
    rw [hl a, hl b]
    group
  · have hcard := Subgroup.card_ker_mul_card_range r
    have hHz : Nat.card ↥(r.ker.map Bs.subtype) = Nat.card ↥r.ker :=
      Subgroup.card_subtype Bs r.ker
    rw [hHz]
    rw [hrange, mul_comm] at hcard
    exact hcard.symm
  · intro s
    have hmem : ((s : G) ∈ r.ker.map Bs.subtype) ↔ r s = 1 := by
      constructor
      · intro hs
        rw [Subgroup.mem_map] at hs
        obtain ⟨y, hy, hyeq⟩ := hs
        have hys : y = s := Subtype.ext (by simpa using hyeq)
        rw [MonoidHom.mem_ker] at hy
        rwa [hys] at hy
      · intro hs
        rw [Subgroup.mem_map]
        exact ⟨s, MonoidHom.mem_ker.mpr hs, rfl⟩
    rw [hmem]
    constructor
    · intro hr c hc
      have hratio := qtwoDB3_a2_ratio_apply hbase hm3 (a := a) (b := b) s hc
      rw [← mul_inv_eq_one]
      rw [← hratio]
      exact hr
    · intro hall
      have hcv := hall (qtwoDB3_a2_chart hbase s) (qtwoDB3_a2_chart_spec hbase s)
      show qtwoDB3_a2_chart hbase s a * (qtwoDB3_a2_chart hbase s b)⁻¹ = 1
      rw [hcv, mul_inv_cancel]

private theorem qtwoDB3_a2_perm_mulVec (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    Matrix.mulVec
      (((ggPermSU (K := F0) (f := 1) (n := m) σ : Su F0 2 1 m) : GL (Fin m) F0) :
        Matrix (Fin m) (Fin m) F0) (Pi.single i 1) = Pi.single (σ⁻¹ i) 1 := by
  have hcoe : (((ggPermSU (K := F0) (f := 1) (n := m) σ : Su F0 2 1 m) :
      GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = σ.permMatrix F0 := rfl
  rw [hcoe, Matrix.permMatrix_mulVec]
  funext j
  simp only [Function.comp_apply, Pi.single_apply]
  exact if_congr (Equiv.eq_symm_apply σ).symm rfl rfl

private theorem qtwoDB3_a2_conj_induces {b : G} {c : Fin m → F0ˣ}
    (hc : qTwoChartTwoThree_induces ψ b c) (σ : Equiv.Perm (Fin m)) :
    qTwoChartTwoThree_induces ψ
      (ψ (ggPermSU (K := F0) (f := 1) (n := m) σ) * b *
        (ψ (ggPermSU (K := F0) (f := 1) (n := m) σ))⁻¹) (fun i => c (σ i)) := by
  have h := qTwoChartTwoThree_induces_conj hc
    (u := ggPermSU (K := F0) (f := 1) (n := m) σ) (σ := σ⁻¹)
    (qtwoDB3_a2_perm_mulVec σ)
  have h' : (fun i => c ((σ⁻¹).symm i)) = fun i => c (σ i) := by
    funext i
    rfl
  rw [h'] at h
  exact h

private theorem qtwoDB3_a2_comm_induces {s : G} {c : Fin m → F0ˣ}
    (hc : qTwoChartTwoThree_induces ψ s c) (σ : Equiv.Perm (Fin m)) :
    qTwoChartTwoThree_induces ψ
      (s * (ψ (ggPermSU (K := F0) (f := 1) (n := m) σ) * s⁻¹ *
        (ψ (ggPermSU (K := F0) (f := 1) (n := m) σ))⁻¹))
      (c * (fun i => c (σ i))⁻¹) := by
  have h1 := qtwoDB3_a2_conj_induces (qtwoDB3_ind_inv hc) σ
  exact qtwoDB3_ind_mul hc h1

private theorem qtwoDB3_a2_perm_conj_mem (hbase : QTwoUnitBase p B Bs x L ψ ε)
    {s : G} (hs : s ∈ Bs) (σ : Equiv.Perm (Fin m)) :
    ψ (ggPermSU (K := F0) (f := 1) (n := m) σ) * s *
      (ψ (ggPermSU (K := F0) (f := 1) (n := m) σ))⁻¹ ∈ Bs := by
  have h := hbase.perm σ⁻¹ ⟨s, hs⟩
  have hmem : ((((ε σ⁻¹ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ⟨s, hs⟩ : ↥Bs) : G) ∈ Bs :=
    (((ε σ⁻¹ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ⟨s, hs⟩).2
  rwa [h, inv_inv] at hmem

private theorem qtwoDB3_a2_comm_mem_inf (hbase : QTwoUnitBase p B Bs x L ψ ε)
    {s : G} (hs : s ∈ Bs) (σ : Equiv.Perm (Fin m)) :
    s * (ψ (ggPermSU (K := F0) (f := 1) (n := m) σ) * s⁻¹ *
      (ψ (ggPermSU (K := F0) (f := 1) (n := m) σ))⁻¹) ∈ Bs ⊓ L := by
  have hBs : s * (ψ (ggPermSU (K := F0) (f := 1) (n := m) σ) * s⁻¹ *
      (ψ (ggPermSU (K := F0) (f := 1) (n := m) σ))⁻¹) ∈ Bs :=
    Bs.mul_mem hs (qtwoDB3_a2_perm_conj_mem hbase (Bs.inv_mem hs) σ)
  have hgL : ψ (ggPermSU (K := F0) (f := 1) (n := m) σ) ∈ L := by
    rw [← hbase.range]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hsL : s * ψ (ggPermSU (K := F0) (f := 1) (n := m) σ) * s⁻¹ ∈ L :=
    ((Subgroup.mem_normalizer_iff.mp (qtwoDB3_bs_le_normalizer hbase hs))
      (ψ (ggPermSU (K := F0) (f := 1) (n := m) σ))).1 hgL
  have hL : s * (ψ (ggPermSU (K := F0) (f := 1) (n := m) σ) * s⁻¹ *
      (ψ (ggPermSU (K := F0) (f := 1) (n := m) σ))⁻¹) ∈ L := by
    have h := L.mul_mem hsL (L.inv_mem hgL)
    simpa only [mul_assoc] using h
  exact ⟨hBs, hL⟩

private noncomputable def qtwoDB3_a2_M (Q : Subgroup G) : Subgroup (Fin m → F0ˣ) where
  carrier := {c | ∃ q ∈ Q, qTwoChartTwoThree_induces ψ q c}
  one_mem' := ⟨1, Q.one_mem, qtwoDB3_ind_one⟩
  mul_mem' := by
    rintro c c' ⟨q, hq, hcq⟩ ⟨q', hq', hcq'⟩
    exact ⟨q * q', Q.mul_mem hq hq', qtwoDB3_ind_mul hcq hcq'⟩
  inv_mem' := by
    rintro c ⟨q, hq, hcq⟩
    exact ⟨q⁻¹, Q.inv_mem hq, qtwoDB3_ind_inv hcq⟩

private def qtwoDB3_a2_d (i j : Fin m) (t : F0ˣ) : Fin m → F0ˣ :=
  Function.update (Function.update (fun _ => 1) i t) j t⁻¹

private theorem qtwoDB3_a2_d_eq (i j : Fin m) (hij : i ≠ j) (t : F0ˣ) :
    (fun k => Function.update (fun _ : Fin m => (1 : F0ˣ)) i t k *
      (Function.update (fun _ : Fin m => (1 : F0ˣ)) i t (Equiv.swap i j k))⁻¹) =
    qtwoDB3_a2_d i j t := by
  funext k
  rw [qtwoDB3_a2_d]
  by_cases hki : k = i
  · rw [hki]
    simp [Function.update_of_ne (a := j) (a' := i) (Ne.symm hij),
      Function.update_of_ne (a := i) (a' := j) hij]
  · by_cases hkj : k = j
    · rw [hkj]
      simp [Function.update_of_ne (a := j) (a' := i) (Ne.symm hij)]
    · simp [Equiv.swap_apply_of_ne_of_ne hki hkj,
        Function.update_of_ne (a := k) (a' := i) hki,
        Function.update_of_ne (a := k) (a' := j) hkj]

private theorem qtwoDB3_a2_d_mem_M (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (Q : Subgroup G) (hQ : Bs ⊓ L ≤ Q) {i j : Fin m} (hij : i ≠ j) (t : F0ˣ) :
    qtwoDB3_a2_d i j t ∈ qtwoDB3_a2_M (ψ := ψ) Q := by
  obtain ⟨s, hsBs, hsind⟩ := hbase.full (Function.update (fun _ : Fin m => (1 : F0ˣ)) i t)
  let g : G := ψ (ggPermSU (K := F0) (f := 1) (n := m) (Equiv.swap i j))
  have hcommQ : s * (g * s⁻¹ * g⁻¹) ∈ Q :=
    hQ (qtwoDB3_a2_comm_mem_inf hbase hsBs (Equiv.swap i j))
  have hind := qtwoDB3_a2_comm_induces hsind (Equiv.swap i j)
  refine ⟨s * (g * s⁻¹ * g⁻¹), hcommQ, ?_⟩
  rw [← qtwoDB3_a2_d_eq i j hij t]
  exact hind

private def qtwoDB3_a2_C1 : Subgroup (Fin m → F0ˣ) where
  carrier := {c | ∏ i, c i = 1}
  one_mem' := by simp
  mul_mem' := by
    intro c c' hc hc'
    have hc1 : (∏ i, c i) = 1 := hc
    have hc2 : (∏ i, c' i) = 1 := hc'
    change (∏ i, c i * c' i) = 1
    rw [Finset.prod_mul_distrib, hc1, hc2, mul_one]
  inv_mem' := by
    intro c hc
    have hc1 : (∏ i, c i) = 1 := hc
    change (∏ i, (c i)⁻¹) = 1
    rw [Finset.prod_inv_distrib, hc1, inv_one]

private theorem qtwoDB3_a2_prod_d_eq (j0 : Fin m) (c : Fin m → F0ˣ)
    (hc : ∏ i, c i = 1) :
    (∏ k ∈ Finset.univ.erase j0, qtwoDB3_a2_d k j0 (c k)) = c := by
  funext r
  rw [Finset.prod_apply]
  by_cases hr : r = j0
  · subst hr
    have hval : ∀ k ∈ Finset.univ.erase r, qtwoDB3_a2_d k r (c k) r = (c k)⁻¹ := by
      intro k hk
      simp [qtwoDB3_a2_d]
    rw [Finset.prod_congr rfl hval, Finset.prod_inv_distrib]
    have h := Finset.mul_prod_erase (Finset.univ) c (Finset.mem_univ r)
    rw [hc] at h
    have hP : (∏ x ∈ Finset.univ.erase r, c x) = (c r)⁻¹ :=
      eq_inv_of_mul_eq_one_right h
    rw [hP, inv_inv]
  · have hmem : r ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩
    have h0 : ∀ k ∈ Finset.univ.erase j0, k ≠ r → qtwoDB3_a2_d k j0 (c k) r = 1 := by
      intro k hk hkr
      simp [qtwoDB3_a2_d, Function.update_of_ne (a := r) (a' := j0) hr,
        Function.update_of_ne (a := r) (a' := k) (Ne.symm hkr)]
    have h1 : qtwoDB3_a2_d r j0 (c r) r = c r := by
      simp [qtwoDB3_a2_d, Function.update_of_ne (a := r) (a' := j0) hr]
    rw [Finset.prod_eq_single r h0 (fun h => absurd hmem h), h1]

private theorem qtwoDB3_a2_C1_le_M (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (Q : Subgroup G) (hQ : Bs ⊓ L ≤ Q) (hm : 2 ≤ m) :
    qtwoDB3_a2_C1 ≤ qtwoDB3_a2_M (ψ := ψ) Q := by
  intro c hc
  let j0 : Fin m := ⟨m - 1, by omega⟩
  have hprod : c = ∏ k ∈ Finset.univ.erase j0, qtwoDB3_a2_d k j0 (c k) :=
    (qtwoDB3_a2_prod_d_eq j0 c hc).symm
  rw [hprod]
  exact (qtwoDB3_a2_M (ψ := ψ) Q).prod_mem fun k hk =>
    qtwoDB3_a2_d_mem_M hbase Q hQ (Finset.mem_erase.mp hk).1 (c k)

private theorem qtwoDB3_a2_prod_scalar (l : F0ˣ) (c : Fin m → F0ˣ) :
    (∏ i, l * c i) = l ^ m * ∏ i, c i := by
  rw [Finset.prod_mul_distrib]
  congr 1
  simp [Finset.prod_const, Fintype.card_fin]

theorem qtwoDB3_card_aug (hbase : QTwoUnitBase p B Bs x L ψ ε) (hm : 5 ≤ m) :
    3 ^ (m - 1) ≤ Nat.card ↥(Subgroup.zpowers x ⊔ (Bs ⊓ L)) := by
  classical
  have hm3 : 3 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  let S : Subgroup G := Bs ⊓ L
  let Q : Subgroup G := Subgroup.zpowers x ⊔ S
  show 3 ^ (m - 1) ≤ Nat.card ↥Q
  have hQBs : Q ≤ Bs :=
    sup_le (Subgroup.zpowers_le.mpr hbase.x_mem) inf_le_left
  let H : Subgroup F0ˣ := (powMonoidHom m : F0ˣ →* F0ˣ).range
  let q : F0ˣ →* F0ˣ ⧸ H := QuotientGroup.mk' H
  let Θ : ↥Bs →* F0ˣ ⧸ H :=
    MonoidHom.mk' (fun s => q (∏ i, qtwoDB3_a2_chart hbase s i)) (by
      intro s t
      have h1 : qTwoChartTwoThree_induces ψ ((s : G) * (t : G))
          (qtwoDB3_a2_chart hbase s * qtwoDB3_a2_chart hbase t) :=
        qtwoDB3_ind_mul (qtwoDB3_a2_chart_spec hbase s) (qtwoDB3_a2_chart_spec hbase t)
      have h2 : qTwoChartTwoThree_induces ψ ((s : G) * (t : G))
          (qtwoDB3_a2_chart hbase (s * t)) := by
        simpa only [Subgroup.coe_mul] using qtwoDB3_a2_chart_spec hbase (s * t)
      obtain ⟨l, hl⟩ :=
        qtwoDB3_ind_scalar hbase.card_field hm3 hbase.hyp.ker h1 h2
      have hmain : (∏ i, qtwoDB3_a2_chart hbase (s * t) i) =
          l ^ m * ((∏ i, qtwoDB3_a2_chart hbase s i) *
            (∏ i, qtwoDB3_a2_chart hbase t i)) := by
        rw [Finset.prod_congr rfl (fun i _ => hl i), qtwoDB3_a2_prod_scalar]
        congr 1
        change (∏ i, qtwoDB3_a2_chart hbase s i * qtwoDB3_a2_chart hbase t i) =
          (∏ i, qtwoDB3_a2_chart hbase s i) * ∏ i, qtwoDB3_a2_chart hbase t i
        rw [Finset.prod_mul_distrib]
      have hlm : q (l ^ m) = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact MonoidHom.mem_range.mpr ⟨l, rfl⟩
      rw [hmain, map_mul, map_mul, hlm, one_mul])
  have hker : ∀ s : ↥Bs, Θ s = 1 → (s : G) ∈ Q := by
    intro s hs
    have hsH : (∏ i, qtwoDB3_a2_chart hbase s i) ∈ H := by
      rw [← QuotientGroup.ker_mk' H]
      exact MonoidHom.mem_ker.mpr hs
    obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hsH
    rw [powMonoidHom_apply] at hl
    let c : Fin m → F0ˣ := fun i => l⁻¹ * qtwoDB3_a2_chart hbase s i
    have hcind : qTwoChartTwoThree_induces ψ (s : G) c :=
      qtwoDB3_ind_smul (ψ := ψ) l⁻¹ (qtwoDB3_a2_chart_spec hbase s)
    have hcprod : (∏ i, c i) = 1 := by
      rw [qtwoDB3_a2_prod_scalar, ← hl, inv_pow, inv_mul_cancel]
    have hcM : c ∈ qtwoDB3_a2_M (ψ := ψ) Q :=
      qtwoDB3_a2_C1_le_M hbase Q le_sup_right hm2 hcprod
    obtain ⟨q', hq'Q, hq'ind⟩ := hcM
    have hq'Bs : q' ∈ Bs := hQBs hq'Q
    have hsq' : (s : G) * q'⁻¹ ∈ Bs := Bs.mul_mem s.2 (Bs.inv_mem hq'Bs)
    have hsqi : qTwoChartTwoThree_induces ψ ((s : G) * q'⁻¹) (fun _ => 1) := by
      have h := qtwoDB3_ind_mul hcind (qtwoDB3_ind_inv hq'ind)
      have h' : c * c⁻¹ = (fun _ : Fin m => (1 : F0ˣ)) := by
        funext i
        rw [Pi.mul_apply, Pi.inv_apply, mul_inv_cancel]
      rwa [h'] at h
    have hmem_x : (s : G) * q'⁻¹ ∈ Subgroup.zpowers x :=
      (qtwoDB3_ind_ker hbase hm3 hsq' hsqi).mp ⟨1, fun i => rfl⟩
    have hxQ : (s : G) * q'⁻¹ ∈ Q := Subgroup.mem_sup_left hmem_x
    have heq : (s : G) = ((s : G) * q'⁻¹) * q' := by group
    rw [heq]
    exact Q.mul_mem hxQ hq'Q
  have hcard_ker : 3 ^ (m - 1) ≤ Nat.card ↥Θ.ker := by
    have hcard := Subgroup.card_ker_mul_card_range Θ
    rw [hbase.card_bs] at hcard
    have hF0units : Nat.card F0ˣ = 3 := by rw [Nat.card_units, hbase.card_field]
    have hrange_le : Nat.card ↥Θ.range ≤ 3 := by
      have h1 : Nat.card ↥Θ.range ≤ Nat.card ↥(⊤ : Subgroup (F0ˣ ⧸ H)) :=
        Subgroup.card_le_of_le le_top
      rw [Subgroup.card_top] at h1
      refine le_trans h1 ?_
      have hdiv : Nat.card (F0ˣ ⧸ H) ∣ 3 := by
        have h := Subgroup.card_quotient_dvd_card H
        rwa [hF0units] at h
      exact Nat.le_of_dvd (by norm_num) hdiv
    have hle : 3 ^ (m - 1) * 3 ≤ Nat.card ↥Θ.ker * 3 := by
      calc 3 ^ (m - 1) * 3 = 3 ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm1]
        _ = Nat.card ↥Θ.ker * Nat.card ↥Θ.range := hcard.symm
        _ ≤ Nat.card ↥Θ.ker * 3 := Nat.mul_le_mul_left _ hrange_le
    exact le_of_mul_le_mul_right hle (by norm_num)
  have hker_map_le : Θ.ker.map Bs.subtype ≤ Q := by
    rintro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨s, hs, rfl⟩ := hg
    exact hker s (MonoidHom.mem_ker.mp hs)
  have hker_card : Nat.card ↥Θ.ker ≤ Nat.card ↥Q := by
    have h1 : Nat.card ↥(Θ.ker.map Bs.subtype) ≤ Nat.card ↥Q :=
      Subgroup.card_le_of_le hker_map_le
    rwa [Subgroup.card_subtype Bs Θ.ker] at h1
  exact le_trans hcard_ker hker_card

theorem qtwoDB3_aug_eq_of_not_dvd (hbase : QTwoUnitBase p B Bs x L ψ ε) (hm : 5 ≤ m)
    (hm3' : ¬ 3 ∣ m) : Subgroup.zpowers x ⊔ (Bs ⊓ L) = Bs := by
  classical
  have hm3 : 3 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  let S : Subgroup G := Bs ⊓ L
  let Q : Subgroup G := Subgroup.zpowers x ⊔ S
  have hQBs : Q ≤ Bs :=
    sup_le (Subgroup.zpowers_le.mpr hbase.x_mem) inf_le_left
  refine le_antisymm hQBs fun g hg => ?_
  let s : ↥Bs := ⟨g, hg⟩
  have hF0units : Nat.card F0ˣ = 3 := by rw [Nat.card_units, hbase.card_field]
  have hcop : Nat.Coprime (Nat.card F0ˣ) m := by
    rw [hF0units]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3'
  obtain ⟨l, hl⟩ : ∃ l : F0ˣ, l ^ m = ∏ i, qtwoDB3_a2_chart hbase s i :=
    ⟨(powCoprime hcop).symm (∏ i, qtwoDB3_a2_chart hbase s i),
      (powCoprime hcop).apply_symm_apply _⟩
  let c : Fin m → F0ˣ := fun i => l⁻¹ * qtwoDB3_a2_chart hbase s i
  have hcind : qTwoChartTwoThree_induces ψ (s : G) c :=
    qtwoDB3_ind_smul (ψ := ψ) l⁻¹ (qtwoDB3_a2_chart_spec hbase s)
  have hcprod : (∏ i, c i) = 1 := by
    rw [qtwoDB3_a2_prod_scalar, ← hl, inv_pow, inv_mul_cancel]
  have hcM : c ∈ qtwoDB3_a2_M (ψ := ψ) Q :=
    qtwoDB3_a2_C1_le_M hbase Q le_sup_right hm2 hcprod
  obtain ⟨q', hq'Q, hq'ind⟩ := hcM
  have hq'Bs : q' ∈ Bs := hQBs hq'Q
  have hsq' : (s : G) * q'⁻¹ ∈ Bs := Bs.mul_mem s.2 (Bs.inv_mem hq'Bs)
  have hsqi : qTwoChartTwoThree_induces ψ ((s : G) * q'⁻¹) (fun _ => 1) := by
    have h := qtwoDB3_ind_mul hcind (qtwoDB3_ind_inv hq'ind)
    have h' : c * c⁻¹ = (fun _ : Fin m => (1 : F0ˣ)) := by
      funext i
      rw [Pi.mul_apply, Pi.inv_apply, mul_inv_cancel]
    rwa [h'] at h
  have hmem_x : (s : G) * q'⁻¹ ∈ Subgroup.zpowers x :=
    (qtwoDB3_ind_ker hbase hm3 hsq' hsqi).mp ⟨1, fun i => rfl⟩
  have hxQ : (s : G) * q'⁻¹ ∈ Q := Subgroup.mem_sup_left hmem_x
  have heq : (s : G) = ((s : G) * q'⁻¹) * q' := by group
  change (s : G) ∈ Q
  rw [heq]
  exact Q.mul_mem hxQ hq'Q

theorem qtwoDB3_card_inf (hbase : QTwoUnitBase p B Bs x L ψ ε) (hm : 5 ≤ m) :
    9 ≤ Nat.card ↥(Bs ⊓ L) := by
  classical
  let S : Subgroup G := Bs ⊓ L
  let Q : Subgroup G := Subgroup.zpowers x ⊔ S
  have hS_le_L : (S : Set G) ⊆ (L : Set G) := inf_le_right
  have hcent : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) := by
    rw [← hbase.cent]
    exact inf_le_right
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set G) :=
    le_trans (le_trans hcent (Subgroup.centralizer_le hS_le_L))
      (Subgroup.centralizer_le_normalizer (S : Set G))
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers x) S hnorm
  let f : ↥(Subgroup.zpowers x) × ↥S → ↥Q := fun p =>
    ⟨(p.1 : G) * (p.2 : G),
      Q.mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    have hg' : g ∈ (↑(Subgroup.zpowers x ⊔ S) : Set G) := hg
    rw [hcoe, Set.mem_mul] at hg'
    obtain ⟨a, ha, b, hb, hab⟩ := hg'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hcardQ : Nat.card ↥Q ≤ 3 * Nat.card ↥S := by
    have hxcard : Nat.card ↥(Subgroup.zpowers x) = 3 := by
      haveI : Fintype G := Fintype.ofFinite G
      rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, hbase.x_order]
    have hle := Nat.card_le_card_of_surjective f hsurj
    rw [Nat.card_prod, hxcard] at hle
    exact hle
  have haug := qtwoDB3_card_aug hbase hm
  change 9 ≤ Nat.card ↥S
  have h3 : 3 ^ (m - 2) ≤ Nat.card ↥S := by
    have hpow : 3 ^ (m - 2) * 3 = 3 ^ (m - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [← hpow] at haug
    have hle : 3 ^ (m - 2) * 3 ≤ Nat.card ↥S * 3 :=
      calc 3 ^ (m - 2) * 3 ≤ Nat.card ↥Q := haug
        _ ≤ 3 * Nat.card ↥S := hcardQ
        _ = Nat.card ↥S * 3 := Nat.mul_comm 3 _
    exact le_of_mul_le_mul_right hle (by norm_num)
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ (m - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ Nat.card ↥S := h3

end CFSG.StandardType.QTwo

end
