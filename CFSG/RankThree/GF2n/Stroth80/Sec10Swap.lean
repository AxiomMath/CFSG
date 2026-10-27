module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Conj
import CFSG.RankThree.GF2n.Stroth80.Sec103Root
public import CFSG.RankThree.GF2n.Stroth80.Sec10Four

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Sec10Hyp.conjG {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) (g : G) :
    Sec10Hyp (hc.conjBy g) n where
  width := H.width.conjG g
  n_gt := H.n_gt
  noA2 := by
    rw [Smith81.LB_conj]
    exact (Smith81.noA2_conj_iff g).mpr H.noA2
  gen := H.gen.conjG g
  alt := by
    intro t ht hQ
    have ht' : g⁻¹ * t * g ∈ LB M Q B := by
      rw [Smith81.LB_conj g M Q B] at ht
      exact mem_conjSubgroup.mp ht
    have hQ' : g⁻¹ * t * g ∉ Q := by
      intro hq
      apply hQ
      have h : g * (g⁻¹ * t * g) * g⁻¹ ∈ conjSubgroup g Q :=
        Subgroup.mem_map_of_mem _ hq
      rwa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at h
    rcases H.alt (g⁻¹ * t * g) ht' hQ' with h | h
    · left
      have hg := congrArg (conjSubgroup g) h
      rw [← Smith81.Rt_conj, ← Smith81.LB_conj] at hg
      simpa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group] using hg
    · right
      have := SLlike.conjG h g
      simpa [mul_assoc] using this
  ex := by
    obtain ⟨t, ht, hQ, hsl⟩ := H.ex
    refine ⟨g * t * g⁻¹, ?_, ?_, SLlike.conjG hsl g⟩
    · rw [Smith81.LB_conj]
      exact Subgroup.mem_map_of_mem _ ht
    · intro hq
      apply hQ
      have h : g⁻¹ * (g * t * g⁻¹) * g ∈ Q := mem_conjSubgroup.mp hq
      rwa [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at h

theorem Sec10Hyp.of_eq {M' Q' Z' B' : Subgroup G} {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) (hc' : Ctx M' Q' Z' B') (hM : M = M') (hQ : Q = Q') (hZ : Z = Z')
    (hB : B = B') : Sec10Hyp hc' n := by
  subst hM hQ hZ hB
  exact H

theorem SLMNat.of_eq {M' Q' Z' B' : Subgroup G} {hc : Ctx M Q Z B} {t : G} {m : ℕ}
    (h : SLMNat hc t m) (hc' : Ctx M' Q' Z' B') (hM : M = M') (hQ : Q = Q') (hZ : Z = Z')
    (hB : B = B') : SLMNat hc' t m := by
  subst hM hQ hZ hB
  exact h

theorem Sec10Hyp.exists_conj_pair (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {A D : Subgroup G} (hA : ∃ h : G, A = conjSubgroup h Z)
    (hD : ∃ h : G, D = conjSubgroup h Z) (hDA : D ≤ QB A) (hne : D ≠ A) :
    ∃ k : G, conjSubgroup k Z = A ∧ conjSubgroup k B = D := by
  obtain ⟨h, hAeq⟩ := hA
  have hQB : QB A = conjSubgroup h Q := by
    rw [hAeq, Smith81.QB_conj_eq hc.hyp h]
  have hD'Q : conjSubgroup h⁻¹ D ≤ Q := by
    have h1 : conjSubgroup h⁻¹ D ≤ conjSubgroup h⁻¹ (QB A) := Subgroup.map_mono hDA
    rw [hQB] at h1
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
  have hD'ne : conjSubgroup h⁻¹ D ≠ Z := by
    intro hZ
    apply hne
    calc D = conjSubgroup h (conjSubgroup h⁻¹ D) := by
          rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      _ = conjSubgroup h Z := by rw [hZ]
      _ = A := hAeq.symm
  have hc' : Ctx M Q Z (conjSubgroup h⁻¹ D) :=
    { hyp := hc.hyp
      conj := by
        obtain ⟨d, hd⟩ := hD
        exact ⟨h⁻¹ * d, by rw [hd, conjSubgroup_mul]⟩
      le := hD'Q
      ne := hD'ne }
  obtain ⟨r, hrM, hrD⟩ := H.rootTrans h34 hspread (conjSubgroup h⁻¹ D) hc'
  refine ⟨h * r, ?_, ?_⟩
  · rw [conjSubgroup_mul, hc.conj_Z_eq hrM]
    exact hAeq.symm
  · rw [conjSubgroup_mul, hrD, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]

theorem Sec10Hyp.exists_conj_swap (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    ∃ g : G, conjSubgroup g Z = Y ∧ conjSubgroup g B = B := by
  have hBQB : B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.2.2.2.1
  have hBY : B ≠ Y := by
    intro h
    apply ht.2.2.1
    have hyB : t ∈ B := by
      rw [h]
      exact hs.mem
    exact hc.le hyB
  exact H.exists_conj_pair h34 hspread hs.conj hc.conj hBQB hBY

theorem sit_swap {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) {g : G}
    (hgZ : conjSubgroup g Z = Y) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z := by
  have h12 := Smith81.smith_1_12 hs
  refine ⟨?_, ?_, hz, hz1, ?_, ?_⟩
  · simpa [hgZ] using hs.hyp.conj g
  · exact ⟨g⁻¹, by rw [← hgZ, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]⟩
  · have hzcent : z ∈ Subgroup.centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h12.1 hy)).2 z hz).symm
    have hzN : z ∈ Subgroup.normalizer (Y : Set G) :=
      Subgroup.centralizer_le_normalizer (Y : Set G) hzcent
    rw [← Smith81.normalizer_conj_eq hs.hyp g]
    simpa [hgZ] using hzN
  · have hZY : Z ⊓ QB Y = ⊥ := Smith81.Z_inf_QB_eq_bot hs h12
    rw [← Smith81.QB_conj_eq hs.hyp g, hgZ]
    intro hzQB
    have hmem : z ∈ Z ⊓ QB Y := Subgroup.mem_inf.mpr ⟨hz, hzQB⟩
    rw [hZY, Subgroup.mem_bot] at hmem
    exact hz1 hmem

private theorem Vt_le_iSup_sup_Z (h57 : Stroth57Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G}
    (hs : Sit M Q Z Y t) :
    Vt M (LB M Q B) B Z t ≤
      (⨆ (C : Subgroup G) (_ : Ctx M Q Z C) (_ : C ≤ QB Y), C) ⊔ Z := by
  refine sec39_Vt_le (le_sup_right : Z ≤
    (⨆ (C : Subgroup G) (_ : Ctx M Q Z C) (_ : C ≤ QB Y), C) ⊔ Z) ?_
  intro m hm htm
  obtain ⟨w, hwQ, a, haX, ha1, haQB⟩ := H.exists_conj_mem_QB_zpowers h57 ht.1 hm htm
  have hwm : w * m ∈ M := M.mul_mem (hs.hyp.Q_normal.1 hwQ) hm
  have hX : Ctx M Q Z (conjSubgroup (w * m) B) := hc.conj_of_mem hwm
  have htX : t ∈ QB (conjSubgroup (w * m) B) := hX.mem_QB_of_inf_QB_zpowers hs haX ha1 haQB
  have hXQY : conjSubgroup (w * m) B ≤ QB Y :=
    hs.hyp.le_QB_of_mem_QB hX.conj hs.conj hs.mem hs.ne_one htX
  have hXS : conjSubgroup (w * m) B ≤
      ⨆ (C : Subgroup G) (_ : Ctx M Q Z C) (_ : C ≤ QB Y), C :=
    le_iSup_of_le (conjSubgroup (w * m) B)
      (le_iSup_of_le hX (le_iSup_of_le hXQY le_rfl))
  intro b hb
  have hxX : w * b * w⁻¹ ∈ conjSubgroup (w * m) B := by
    rw [conjSubgroup_mul]
    exact Subgroup.mem_map_of_mem _ hb
  have hb_eq : b = (w * b * w⁻¹) * ⁅(w * b * w⁻¹)⁻¹, w⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hb_eq]
  exact Subgroup.mul_mem_sup (hXS hxX)
    (Smith81.comm_mem_Z hs.hyp (Q.inv_mem (hX.le hxX)) (Q.inv_mem hwQ))

theorem Good103.iSup_root_eq (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    ⨆ (C : Subgroup G) (_ : Ctx M Q Z C) (_ : C ≤ QB Y), C = Q ⊓ QB Y := by
  have h57 : Stroth57Statement := stroth_5_7 h34 hspread
  set S : Subgroup G := ⨆ (C : Subgroup G) (_ : Ctx M Q Z C) (_ : C ≤ QB Y), C with hS
  have hS_le_Q : S ≤ Q := iSup_le fun C => iSup_le fun hC => iSup_le fun _ => hC.le
  have hS_le_QBY : S ≤ QB Y := iSup_le fun C => iSup_le fun _ => iSup_le fun hCY => hCY
  have hS_norm : S ≤ Subgroup.normalizer (Z : Set G) := fun x hx =>
    hs.hyp.Z_normal.2 (hs.hyp.Q_normal.1 (hS_le_Q hx))
  refine le_antisymm ?_ ?_
  · refine iSup_le fun C => iSup_le fun hC => iSup_le fun hCY => le_inf hC.le hCY
  · have hVle : Vt M (LB M Q B) B Z t ≤ S ⊔ Z := by
      rw [hS]
      exact Vt_le_iSup_sup_Z h57 H ht hs
    intro a ha
    have haV : a ∈ Vt M (LB M Q B) B Z t := by
      rw [Good103.Vt_eq ht hs]
      exact Subgroup.mem_sup_left ha
    obtain ⟨s, hsS, z', hz', hsz⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer hS_norm (hVle haV)
    have hz'QB : z' ∈ QB Y := by
      have h1 : s⁻¹ * a ∈ QB Y := (QB Y).mul_mem ((QB Y).inv_mem (hS_le_QBY hsS)) ha.2
      rwa [← hsz, show s⁻¹ * (s * z') = z' by group] at h1
    have hz'Z : z' ∈ Z ⊓ QB Y := Subgroup.mem_inf.mpr ⟨hz', hz'QB⟩
    rw [Smith81.Z_inf_QB_eq_bot hs (Smith81.smith_1_12 hs), Subgroup.mem_bot] at hz'Z
    rw [hz'Z, mul_one] at hsz
    exact hsz ▸ hsS

private theorem swap_opposite_ctx {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) {g : G}
    (hgZ : conjSubgroup g Z = Y)
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B)
    {C : Subgroup G} (hC : Ctx M Q Z C) (hCY : C ≤ QB Y) :
    Ctx (conjSubgroup g M) (conjSubgroup g Q) Y C := by
  have hQc : conjSubgroup g Q = QB Y := by
    rw [← Smith81.QB_conj_eq hs.hyp g, hgZ]
  have hZY : Z = conjSubgroup g⁻¹ Y := by
    rw [← hgZ, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hYne_bot : Y ≠ ⊥ := by
    obtain ⟨k, hk⟩ := hs.conj
    intro hbot
    have hcard : Nat.card Z = 1 := by
      rw [← CFSG.RankThree.GF2n.card_conjSubgroup k Z, ← hk, hbot, Subgroup.card_bot]
    have := hC.hyp.q4
    omega
  have hCYne : C ≠ Y := by
    intro hCYeq
    apply hYne_bot
    rw [eq_bot_iff]
    intro y hy
    have hmem : y ∈ Y ⊓ Q := ⟨hy, hC.le (hCYeq ▸ hy)⟩
    rwa [hs.X_inf_Q, Subgroup.mem_bot] at hmem
  exact
    { hyp := hcY.hyp
      conj := by
        obtain ⟨k, hk⟩ := hC.conj
        refine ⟨k * g⁻¹, ?_⟩
        calc C = conjSubgroup k Z := hk
          _ = conjSubgroup k (conjSubgroup g⁻¹ Y) := by rw [hZY]
          _ = conjSubgroup (k * g⁻¹) Y := conjSubgroup_conjSubgroup k g⁻¹ Y
      le := by rw [hQc]; exact hCY
      ne := hCYne }

private theorem conj_le_Vt_swap (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {g : G} (hgZ : conjSubgroup g Z = Y)
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B) (H' : Sec10Hyp hcY n)
    {z : G} (hz : z ∈ Z) (hsz : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z)
    {C : Subgroup G} (hC : Ctx M Q Z C) (hCY : C ≤ QB Y) :
    C ≤ Vt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B) B Y z := by
  have hC' := swap_opposite_ctx hs hgZ hcY hC hCY
  have hzLB : z ∈ LB (conjSubgroup g M) (conjSubgroup g Q) B :=
    Subgroup.mem_sup_right ⟨(Ctx.Z_le_QB hc).1 hz, hsz.memM⟩
  have hRT : RootTrans (conjSubgroup g M) (conjSubgroup g Q) Y B :=
    rootTrans_of_all h34 hcY (H'.toSec5 hzLB hsz.notQ)
      (hspread G (conjSubgroup g M) (conjSubgroup g Q) Y B hcY n
        H'.width H'.n_gt H'.noA2 H'.gen)
  obtain ⟨m', hm'M, hm'C⟩ := hRT C hC'
  have hLBconj : conjSubgroup m' (LB (conjSubgroup g M) (conjSubgroup g Q) B) =
      LB (conjSubgroup g M) (conjSubgroup g Q) C := by
    rw [← hm'C]
    exact (hcY.LB_conj hm'M).symm
  have hZQBC : Z ≤ QB C :=
    hc.hyp.le_QB_of_le_QB hC.conj ⟨1, by rw [conjSubgroup_one]⟩ hC.ne
      (by rw [hc.hyp.QB_Z]; exact hC.le)
  have hzLBC : z ∈ conjSubgroup m' (LB (conjSubgroup g M) (conjSubgroup g Q) B) := by
    rw [hLBconj]
    exact Subgroup.mem_sup_right ⟨hZQBC hz, hsz.memM⟩
  have hCV := sec39_conjB_le_Vt (M := conjSubgroup g M)
    (L := LB (conjSubgroup g M) (conjSubgroup g Q) B) (B := B) (Z := Y) (t := z) hm'M hzLBC
  rwa [hm'C] at hCV

private theorem inf_QB_le_Vt_swap (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {g : G}
    (hgZ : conjSubgroup g Z = Y) (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B)
    (H' : Sec10Hyp hcY n) {z : G} (hz : z ∈ Z)
    (hsz : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z) :
    Q ⊓ QB Y ≤ Vt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B) B Y z := by
  rw [← Good103.iSup_root_eq h34 hspread H ht hs]
  refine iSup_le fun C => iSup_le fun hC => iSup_le fun hCY => ?_
  exact conj_le_Vt_swap h34 hspread H ht hs hgZ hcY H' hz hsz hC hCY

theorem Sec10Hyp.conj_le_sup_of_conj_LB_eq (h34 : Stroth34Statement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {r : G} (hr : r ∈ M)
    (heq : conjSubgroup r (LB M Q B) = LB M Q B) : conjSubgroup r B ≤ B ⊔ Z := by
  have h35 := (stroth_3_5 h34 hc H.width H.n_gt H.noA2 H.gen).2.1
  intro x hx
  rw [mem_conjSubgroup] at hx
  set b : G := r⁻¹ * x * r with hb
  have hxCQt : r * b * r⁻¹ ∈ CQt Q Z (LB M Q B) := by
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hr) b).mp (hc.le hx)
    · intro l hl
      have hl' : l ∈ conjSubgroup r (LB M Q B) := by
        rw [heq]; exact hl
      obtain ⟨l₀, hl₀, rfl⟩ := hl'
      have hbCQt : b ∈ CQt Q Z (LB M Q B) := by
        rw [h35]; exact Subgroup.mem_sup_left hx
      have hcommZ := hbCQt.2 l₀ hl₀
      rw [show (MulEquiv.toMonoidHom (MulAut.conj r)) l₀ = r * l₀ * r⁻¹ by
        simp [MulAut.conj_apply]]
      rw [show ⁅r * l₀ * r⁻¹, r * b * r⁻¹⁆ = r * ⁅l₀, b⁆ * r⁻¹ by
        simp only [commutatorElement_def]; group]
      exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hr) _).mp hcommZ
  rw [h35] at hxCQt
  rwa [show r * (r⁻¹ * x * r) * r⁻¹ = x by group] at hxCQt

private theorem card_inf_QB_sup_Y {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) :
    Nat.card ↥((Q ⊓ QB Y) ⊔ Y) = Nat.card Z * Nat.card ↥(Q ⊓ QB Y) := by
  have hA_normY : Q ⊓ QB Y ≤ Subgroup.normalizer (Y : Set G) :=
    inf_le_right.trans hs.QB_le_normalizer
  have hAY : (Q ⊓ QB Y) ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨hxQ, -⟩, hxY⟩ := Subgroup.mem_inf.mp hx
    have hmem : x ∈ Y ⊓ Q := ⟨hxY, hxQ⟩
    rwa [hs.X_inf_Q, Subgroup.mem_bot] at hmem
  have hYcard : Nat.card Y = Nat.card Z := by
    obtain ⟨k, hk⟩ := hs.conj
    rw [hk, CFSG.RankThree.GF2n.card_conjSubgroup]
  have h := card_sup_mul_card_inf_of_normalizer (A := Y) (C := Q ⊓ QB Y) hA_normY
  rw [sup_comm, inf_comm Y (Q ⊓ QB Y), hAY, Subgroup.card_bot, mul_one, hYcard] at h
  exact h

private theorem card_inf_QB_le_card_Z {hc : Ctx M Q Z B} {Y : Subgroup G} {t : G}
    (hs : Sit M Q Z Y t)
    (hBQBY : B ≤ QB Y) (hAle : Q ⊓ QB Y ≤ B ⊔ Y) :
    Nat.card ↥(Q ⊓ QB Y) ≤ Nat.card Z := by
  have hYcard : Nat.card Y = Nat.card Z := by
    obtain ⟨k, hk⟩ := hs.conj
    rw [hk, CFSG.RankThree.GF2n.card_conjSubgroup]
  have hBcard : Nat.card B = Nat.card Z := by
    obtain ⟨b, hb⟩ := hc.conj
    rw [hb, CFSG.RankThree.GF2n.card_conjSubgroup]
  have hcardA := card_inf_QB_sup_Y hs
  have hB_normY : B ≤ Subgroup.normalizer (Y : Set G) := hBQBY.trans hs.QB_le_normalizer
  have hcardBY : Nat.card ↥(B ⊔ Y) ≤ Nat.card Z * Nat.card Z := by
    have h := card_sup_mul_card_inf_of_normalizer (A := Y) (C := B) hB_normY
    have hpos : 0 < Nat.card ↥(Y ⊓ B) := Nat.card_pos
    have hle : Nat.card ↥(Y ⊔ B) ≤ Nat.card ↥(Y ⊔ B) * Nat.card ↥(Y ⊓ B) :=
      Nat.le_mul_of_pos_right _ hpos
    calc Nat.card ↥(B ⊔ Y) = Nat.card ↥(Y ⊔ B) := by rw [sup_comm]
      _ ≤ Nat.card ↥(Y ⊔ B) * Nat.card ↥(Y ⊓ B) := hle
      _ = Nat.card ↥Y * Nat.card ↥B := h
      _ = Nat.card Z * Nat.card Z := by rw [hYcard, hBcard]
  have hsup : (Q ⊓ QB Y) ⊔ Y ≤ B ⊔ Y := by exact sup_le hAle le_sup_right
  have hle1 : Nat.card ↥(Q ⊓ QB Y) * Nat.card Z ≤ Nat.card Z * Nat.card Z := by
    calc Nat.card ↥(Q ⊓ QB Y) * Nat.card Z = Nat.card Z * Nat.card ↥(Q ⊓ QB Y) :=
          Nat.mul_comm _ _
      _ = Nat.card ↥((Q ⊓ QB Y) ⊔ Y) := hcardA.symm
      _ ≤ Nat.card ↥(B ⊔ Y) :=
          Nat.card_le_card_of_injective (Subgroup.inclusion hsup)
            (Subgroup.inclusion_injective hsup)
      _ ≤ Nat.card Z * Nat.card Z := hcardBY
  exact Nat.le_of_mul_le_mul_right hle1 Nat.card_pos

private theorem Rt_ne_LB_swap (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {g : G} (hgZ : conjSubgroup g Z = Y)
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B) (H' : Sec10Hyp hcY n)
    {m : ℕ} (hm : SLMNat hc t m) {z : G} (hz : z ∈ Z)
    (hsz : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z) (hBQBY : B ≤ QB Y) :
    Rt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B) z ≠
      LB (conjSubgroup g M) (conjSubgroup g Q) B := by
  intro hRt
  have hzL' : z ∈ LB (conjSubgroup g M) (conjSubgroup g Q) B :=
    Subgroup.mem_sup_right ⟨(Ctx.Z_le_QB hc).1 hz, hsz.memM⟩
  have hBm : ∀ m' ∈ conjSubgroup g M,
      z ∈ conjSubgroup m' (LB (conjSubgroup g M) (conjSubgroup g Q) B) →
        conjSubgroup m' B ≤ B ⊔ Y := by
    intro m' hm' hzm
    have h : conjSubgroup m' (LB (conjSubgroup g M) (conjSubgroup g Q) B) ≤
        Rt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B) z := by
      unfold Rt
      exact le_iSup₂_of_le m' hm' (le_iSup_of_le hzm le_rfl)
    have hle : conjSubgroup m' (LB (conjSubgroup g M) (conjSubgroup g Q) B) ≤
        LB (conjSubgroup g M) (conjSubgroup g Q) B := by rwa [hRt] at h
    have heq : conjSubgroup m' (LB (conjSubgroup g M) (conjSubgroup g Q) B) =
        LB (conjSubgroup g M) (conjSubgroup g Q) B :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [CFSG.RankThree.GF2n.card_conjSubgroup])
    exact H'.conj_le_sup_of_conj_LB_eq h34 hm' heq
  have hVle : Vt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B) B Y z ≤
      B ⊔ Y := sec39_Vt_le le_sup_right hBm
  have hAle : Q ⊓ QB Y ≤ B ⊔ Y :=
    (inf_QB_le_Vt_swap h34 hspread H ht hs hgZ hcY H' hz hsz).trans hVle
  have hAleq := card_inf_QB_le_card_Z (hc := hc) hs hBQBY hAle
  have hA0card : Nat.card ↥(Q ⊓ QB Y) = Nat.card Z ^ m :=
    Good103.card_inf_QB_eq_pow hc ht hs (SLMNat.card_Vt hm)
  have hm2 : 2 ≤ m := by
    obtain ⟨m0, hm0, hsl⟩ := SLlike.exists_SLMNat (H.slLike ht.1)
    have hEq : m = m0 := SLMNat.unique hm hsl
    omega
  have hlt : Nat.card Z < Nat.card Z ^ m := by
    have h := Nat.pow_lt_pow_right (show 1 < Nat.card Z by have := hc.hyp.q4; omega)
      (show 1 < m by omega)
    simpa using h
  rw [hA0card] at hAleq
  omega

private theorem good101_swap (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {g : G} (hgZ : conjSubgroup g Z = Y)
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B) (H' : Sec10Hyp hcY n)
    {m : ℕ} (hm : SLMNat hc t m) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hsz : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z) (hBQBY : B ≤ QB Y) :
    Good101 (conjSubgroup g M) (conjSubgroup g Q) Y B z := by
  have hy : g * z * g⁻¹ ∈ Y := by
    rw [← hgZ]
    exact mem_conjSubgroup.mpr (by rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group]; exact hz)
  have hy1 : g * z * g⁻¹ ≠ 1 := by
    intro hy1
    apply hz1
    have h := congrArg (fun w => g⁻¹ * w * g) hy1
    rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at h
    simpa using h
  refine ⟨⟨g⁻¹, g * z * g⁻¹, hy, hy1, by group⟩, hsz.memM, hsz.notQ,
    (Ctx.Z_le_QB hc).1 hz, ?_⟩
  exact Rt_ne_LB_swap h34 hspread H ht hs hgZ hcY H' hm hz hsz hBQBY

private theorem Vt_swap_eq (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {g : G} (hgZ : conjSubgroup g Z = Y)
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B) (H' : Sec10Hyp hcY n)
    {z : G} (hz : z ∈ Z) (hz101 : Good101 (conjSubgroup g M) (conjSubgroup g Q) Y B z)
    (hsz : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z) :
    Vt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B) B Y z =
      (Q ⊓ QB Y) ⊔ Y := by
  have h57 : Stroth57Statement := stroth_5_7 h34 hspread
  have hupper := Sec10Hyp.Vt_le h57 H' hz101
  have hQc : conjSubgroup g Q = QB Y := by
    rw [← Smith81.QB_conj_eq hs.hyp g, hgZ]
  have hInf : conjSubgroup g Q ⊓ QB (Subgroup.zpowers z) = Q ⊓ QB Y := by
    rw [inf_QB_zpowers_eq hsz, hQc, hc.hyp.QB_Z, inf_comm]
  rw [hInf] at hupper
  refine le_antisymm hupper ?_
  refine sup_le ?_ sec39_Z_le_Vt
  exact inf_QB_le_Vt_swap h34 hspread H ht hs hgZ hcY H' hz hsz

private theorem good103_swap (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {g : G} (hgZ : conjSubgroup g Z = Y)
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B) (H' : Sec10Hyp hcY n)
    {m : ℕ} (hm : SLMNat hc t m) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hsz : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z) (hBQBY : B ≤ QB Y) :
    Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B z := by
  have hz101 := good101_swap h34 hspread H ht hs hgZ hcY H' hm hz hz1 hsz hBQBY
  refine ⟨hz101, ?_⟩
  have hV := Vt_swap_eq h34 hspread H ht hs hgZ hcY H' hz hz101 hsz
  have hQc : conjSubgroup g Q = QB Y := by
    rw [← Smith81.QB_conj_eq hs.hyp g, hgZ]
  have hInf : conjSubgroup g Q ⊓ QB (Subgroup.zpowers z) = Q ⊓ QB Y := by
    rw [inf_QB_zpowers_eq hsz, hQc, hc.hyp.QB_Z, inf_comm]
  rw [hV, hInf]

private theorem SLMNat_swap_eq (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {g : G} (hgZ : conjSubgroup g Z = Y)
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B) (H' : Sec10Hyp hcY n)
    {m : ℕ} (hm : SLMNat hc t m) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hsz : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z) (hBQBY : B ≤ QB Y) :
    SLMNat hcY z m := by
  have hz101 := good101_swap h34 hspread H ht hs hgZ hcY H' hm hz hz1 hsz hBQBY
  obtain ⟨m', -, hSL'⟩ := SLlike.exists_SLMNat (H'.slLike hz101)
  have hVY := Vt_swap_eq h34 hspread H ht hs hgZ hcY H' hz hz101 hsz
  have hA0card : Nat.card ↥(Q ⊓ QB Y) = Nat.card Z ^ m :=
    Good103.card_inf_QB_eq_pow hc ht hs (SLMNat.card_Vt hm)
  have hYcard : Nat.card Y = Nat.card Z := by
    obtain ⟨k, hk⟩ := hs.conj
    rw [hk, CFSG.RankThree.GF2n.card_conjSubgroup]
  have hVcard : Nat.card ↥(Vt (conjSubgroup g M)
      (LB (conjSubgroup g M) (conjSubgroup g Q) B) B Y z) = Nat.card Z ^ (m + 1) := by
    rw [hVY, card_inf_QB_sup_Y hs, hA0card, pow_succ]
    ring
  have hEq : Nat.card Z ^ (m' + 1) = Nat.card Z ^ (m + 1) := by
    rw [← hYcard, ← SLMNat.card_Vt hSL', hVcard, hYcard]
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hmm : m' = m := by
    have h := Nat.pow_right_injective hq2 hEq
    omega
  rwa [hmm] at hSL'

private theorem swap_ctx {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G}
    (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {g : G}
    (hgZ : conjSubgroup g Z = Y) (hgB : conjSubgroup g B = B) (hBQBY : B ≤ QB Y) :
    ∃ hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B, Sec10Hyp hcY n := by
  have hQc : conjSubgroup g Q = QB Y := by
    rw [← Smith81.QB_conj_eq hs.hyp g, hgZ]
  have hBY : B ≠ Y := by
    intro hBY
    exact ht.2.2.1 (hc.le (hBY.symm ▸ hs.mem))
  obtain ⟨b, hb⟩ := hc.conj
  let hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B :=
    { hyp := by simpa [hgZ] using hs.hyp.conj g
      conj := by
        refine ⟨b * g⁻¹, ?_⟩
        rw [← hgZ, conjSubgroup_conjSubgroup, show b * g⁻¹ * g = b by group, hb]
      le := by rw [hQc]; exact hBQBY
      ne := hBY }
  exact ⟨hcY, (H.conjG g).of_eq hcY rfl rfl hgZ hgB⟩

theorem Good103.exists_swap (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n m : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (hm : SLMNat hc t m) :
    ∃ g : G, conjSubgroup g Z = Y ∧ conjSubgroup g B = B ∧
      ∃ hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B, Sec10Hyp hcY n ∧
        ∀ z ∈ Z, z ≠ 1 →
          Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z ∧
          Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B z ∧
          Vt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B) B Y z =
            (Q ⊓ QB Y) ⊔ Y ∧
          SLMNat hcY z m := by
  obtain ⟨g, hgZ, hgB⟩ := Sec10Hyp.exists_conj_swap h34 hspread H ht.1 hs
  have hBQBY : B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.1.2.2.2.1
  obtain ⟨hcY, H'⟩ := swap_ctx H ht.1 hs hgZ hgB hBQBY
  refine ⟨g, hgZ, hgB, hcY, H', ?_⟩
  intro z hz hz1
  have hsz : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z := sit_swap hs hgZ hz hz1
  exact ⟨hsz,
    good103_swap h34 hspread H ht hs hgZ hcY H' hm hz hz1 hsz hBQBY,
    Vt_swap_eq h34 hspread H ht hs hgZ hcY H'
      hz (good101_swap h34 hspread H ht hs hgZ hcY H' hm hz hz1 hsz hBQBY) hsz,
    SLMNat_swap_eq h34 hspread H ht hs hgZ hcY H' hm hz hz1 hsz hBQBY⟩
