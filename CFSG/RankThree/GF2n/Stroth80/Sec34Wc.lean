module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Symm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem Ctx.conj_B_mem_BZ_of_3_1 (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) {a : G} (haM : a ∈ M)
    (haL : a ∈ Subgroup.normalizer (LB M Q B : Set G)) {u : G} (hu : u ∈ B) :
    a * u * a⁻¹ ∈ (B ⊔ Z : Subgroup G) := by
  by_contra hnot
  have huC : u ∈ CQt Q Z (LB M Q B) := ⟨hc.le hu, fun t ht => hc.comm_B_mem_Z ht hu⟩
  refine hc.no_involution_CQt hw hn hno ⟨a * u * a⁻¹, hc.conj_mem_CQt haM haL huC, hnot, ?_⟩
  rw [conj_pow, hc.isElemAbelian_B.2 u hu, mul_one, mul_inv_cancel]

theorem Ctx.weaklyClosed_of_3_1 (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {m : G} (hm : m ∈ M)
    (hmN : conjSubgroup m (LB M Q B) ≤ Subgroup.normalizer (LB M Q B : Set G)) :
    conjSubgroup m (LB M Q B) = LB M Q B := by
  have hc' := hc.conj_of_mem hm
  have hno' := hc.noA2_conj hno hm
  have hBle : ∀ a ∈ LB M Q (conjSubgroup m B), ∀ u ∈ B, a * u * a⁻¹ ∈ (B ⊔ Z : Subgroup G) := by
    intro a ha u hu
    have haL : a ∈ Subgroup.normalizer (LB M Q B : Set G) := hmN (by rwa [← hc.LB_conj hm])
    exact hc.conj_B_mem_BZ_of_3_1 hw hn hno (hc'.LB_le_M ha) haL hu
  have hBZ : ∀ a ∈ LB M Q (conjSubgroup m B), ∀ u ∈ B, ⁅a, u⁆ ∈ Z := fun a ha =>
    hc.comm_mem_Z_of_normalizes (hc'.LB_le_M ha) (hc'.LB_centralizes_Z ha)
      (hc'.sq_mem_Q_of_mem_LB ha) (hBle a ha)
  have hBle' : B ≤ conjSubgroup m B ⊔ Z := by
    intro u hu
    by_contra hnot
    exact hc'.no_involution_CQt hw hn hno'
      ⟨u, ⟨hc.le hu, fun t ht => hBZ t ht u hu⟩, hnot, hc.isElemAbelian_B.2 u hu⟩
  have hZB : (conjSubgroup m B ⊔ Z : Subgroup G) = B ⊔ Z := by
    have hle1 : (B ⊔ Z : Subgroup G) ≤ conjSubgroup m B ⊔ Z := sup_le hBle' le_sup_right
    exact (Subgroup.eq_of_le_of_card_ge hle1 (by
      rw [hc'.card_sup_Z, hc.card_sup_Z, card_conjSubgroup])).symm
  have hB'le : conjSubgroup m B ≤ Z ⊔ B := by
    rw [sup_comm, ← hZB]
    exact le_sup_left
  obtain ⟨p, hp, hpB⟩ := hc.exists_conj_of_le_ZB hc' hB'le
  have hpL : p ∈ LB M Q B := Subgroup.mem_sup_left hp
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hp
  have hLp : conjSubgroup p (LB M Q B) = LB M Q B :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hpL)
  rw [← hc.LB_conj hm, ← hpB, hc.LB_conj hpM, hLp]

theorem Ctx.mem_normalizer_LB_iff' (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {a : G} (haM : a ∈ M) :
    a ∈ Subgroup.normalizer (LB M Q B : Set G) ↔
      a ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
  constructor
  · intro haL
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hBN : B ≤ Subgroup.normalizer (Z : Set G) := fun u hu =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.le hu))
    obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN hx
    have e : a * (u * z) * a⁻¹ = (a * u * a⁻¹) * (a * z * a⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hc.conj_B_mem_BZ_of_3_1 hw hn hno haM haL hu)
      (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 haM) z).mp hz))
  · intro haV
    have hc' := hc.conj_of_mem haM
    have hVa : conjSubgroup a (B ⊔ Z : Subgroup G) = B ⊔ Z := conjSubgroup_eq_self_iff.mpr haV
    have hle : conjSubgroup a B ≤ Z ⊔ B := by
      have h1 : conjSubgroup a B ≤ conjSubgroup a (B ⊔ Z : Subgroup G) :=
        Subgroup.map_mono le_sup_left
      rw [hVa, sup_comm] at h1
      exact h1
    obtain ⟨p, hp, hpB⟩ := hc.exists_conj_of_le_ZB hc' hle
    have hpL : p ∈ LB M Q B := Subgroup.mem_sup_left hp
    have hpM : p ∈ M := hc.hyp.Q_normal.1 hp
    have hLp : conjSubgroup p (LB M Q B) = LB M Q B :=
      conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hpL)
    refine conjSubgroup_eq_self_iff.mp ?_
    rw [← hc.LB_conj haM, ← hpB, hc.LB_conj hpM, hLp]

theorem Ctx.Spure_conj (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) :
    (hc.conj_of_mem hm).Spure = conjSubgroup m hc.Spure := by
  have hCQ : Q ⊓ Subgroup.centralizer ((conjSubgroup m B : Subgroup G) : Set G) =
      conjSubgroup m (Q ⊓ Subgroup.centralizer (B : Set G)) := by
    rw [conjSubgroup_inf, conjSubgroup_centralizer, hc.conj_Q_eq hm]
  have hBZ : (conjSubgroup m B ⊔ Z : Subgroup G) = conjSubgroup m (B ⊔ Z) := by
    rw [conjSubgroup_sup', hc.conj_Z_eq hm]
  ext t
  rw [Ctx.mem_Spure, mem_conjSubgroup, Ctx.mem_Spure, hc.LB_conj hm, mem_conjSubgroup, hCQ, hBZ]
  refine and_congr_right fun _ => ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · have h1 := h (m * y * m⁻¹) (mem_conjSubgroup.mpr (by
      rw [show m⁻¹ * (m * y * m⁻¹) * m = y by group]
      exact hy))
    rw [mem_conjSubgroup] at h1
    have e : m⁻¹ * ⁅t, m * y * m⁻¹⁆ * m = ⁅m⁻¹ * t * m, y⁆ := by
      simp only [commutatorElement_def]; group
    rwa [e] at h1
  · rw [mem_conjSubgroup] at hy ⊢
    have h1 := h _ hy
    have e : ⁅m⁻¹ * t * m, m⁻¹ * y * m⁆ = m⁻¹ * ⁅t, y⁆ * m := by
      simp only [commutatorElement_def]; group
    rwa [e] at h1

theorem Ctx.le_QB_conj_of_exists_comm (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ conjSubgroup m B)
    (hx1 : x ≠ 1) (_hxC : x ∈ Subgroup.centralizer (B : Set G))
    (htx : ∃ t ∈ hc.Spure, t ∉ Q ∧ ⁅t, x⁆ ∈ Z) : B ≤ QB (conjSubgroup m B) := by
  have hC : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hnoC := hc.noA2_conj hno hm
  set C := conjSubgroup m B
  have hxQ : x ∈ Q := hC.le hx
  obtain ⟨t, htS, htQ, htx⟩ := htx
  obtain ⟨k, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  have htM : t ∈ M := hc.LB_le_M htS.1
  obtain ⟨hQn, hQn'⟩ := hc.conj_mem_Q_of_mem_M htM
  obtain ⟨T, hTπ, hTiso, -⟩ := h.linear_of_centralizes htM (hc.LB_centralizes_Z htS.1)
  obtain ⟨-, hTr⟩ := hc.Spure_act h hB hcent htS hTπ
  have hne : ∃ e, T e ≠ e := by
    by_contra hcon
    push Not at hcon
    exact htQ (mem_Q_of_pi_conj_eq (M₀ := M₀) hc.hyp htM fun x hx => by rw [hTπ x hx, hcon])
  have hdim := Tim79.QuadModel.finrank_range_eq_two (T := (T : M₀.E →ₗ[GaloisField 2 k] M₀.E))
    hTiso hb0 hbs hTr hne
  have hT2 : ∀ e, T (T e) = e := by
    intro e
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
    rw [← hTπ y hyQ, ← hTπ _ (hQn y hyQ)]
    have : t * (t * y * t⁻¹) * t⁻¹ = t ^ 2 * y * (t ^ 2)⁻¹ := by rw [pow_two]; group
    rw [this, Tim79.QuadModel.pi_conj_self (M₀ := M₀) (hc.sq_mem_Q_of_mem_LB htS.1) hyQ]
  have hnz : ∃ v ∈ LinearMap.range ((T : M₀.E →ₗ[GaloisField 2 k] M₀.E) - 1), M₀.Qf v ≠ 0 := by
    have hnel := hc.not_elemAbelian_comm_Spure hno htS htQ
    rw [isElemAbelian_comm_zpowers_iff M₀ h.reg T hQn hQn' hTπ] at hnel
    push Not at hnel
    exact hnel
  have hxZ : x ∉ Z := fun hxZ => hx1 (by
    have : x ∈ Z ⊓ C := ⟨hxZ, hx⟩
    rw [hC.inf_eq_bot, Subgroup.mem_bot] at this
    exact this)
  have hπx : M₀.π x ≠ 0 := fun h0 => hxZ ((M₀.π_ker x hxQ).mp h0)
  have hTx : T (M₀.π x) = M₀.π x := by
    rw [← hTπ x hxQ]
    exact (M₀.comm_mem_iff hxQ (hQn x hxQ)).mp htx
  obtain ⟨c₀, -, -, hCline, -⟩ := hC.dictB h
  have hTC : ∀ v ∈ M₀.img C, T v = v := by
    intro v hv
    obtain ⟨s, rfl⟩ := (hCline v).mp hv
    obtain ⟨s₀, hs₀⟩ := (hCline _).mp (M₀.pi_mem_img hx hxQ)
    have hs₀0 : s₀ ≠ 0 := fun h0 => hπx (by rw [hs₀, h0, zero_smul])
    have hc₀ : T c₀ = c₀ := by
      have : c₀ = s₀⁻¹ • M₀.π x := by rw [hs₀, smul_smul, inv_mul_cancel₀ hs₀0, one_smul]
      rw [this, map_smul, hTx]
    rw [map_smul, hc₀]
  have hle : conjSubgroup t C ≤ Z ⊔ C := by
    intro y hy
    have hc' := mem_conjSubgroup.mp hy
    set c := t⁻¹ * y * t with hcdef
    have hy' : y = t * c * t⁻¹ := by rw [hcdef]; group
    have hcQ : c ∈ Q := hC.le hc'
    have hyQ : y ∈ Q := hy' ▸ hQn c hcQ
    have hπ : M₀.π y = M₀.π c := by
      rw [hy', hTπ c hcQ, hTC _ (M₀.pi_mem_img hc' hcQ)]
    have hz : c⁻¹ * y ∈ Z := (M₀.pi_eq_iff hcQ hyQ).mp hπ.symm
    have : y = c * (c⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc') (Subgroup.mem_sup_left hz)
  have hC' : Ctx M Q Z (conjSubgroup t C) := hC.conj_of_mem htM
  obtain ⟨p, hpQ, hpC⟩ := hC.exists_conj_of_le_ZB hC' hle
  set a := p⁻¹ * t with ha
  have haM : a ∈ M := M.mul_mem (M.inv_mem (hc.hyp.Q_normal.1 hpQ)) htM
  have haC : conjSubgroup a C = C := by
    rw [ha, conjSubgroup_mul, ← hpC, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have haπ : ∀ y ∈ Q, M₀.π (a * y * a⁻¹) = T (M₀.π y) := by
    intro y hy
    have e : a * y * a⁻¹ = p⁻¹ * (t * y * t⁻¹) * p⁻¹⁻¹ := by rw [ha]; group
    rw [e, Tim79.QuadModel.pi_conj_self (M₀ := M₀) (Q.inv_mem hpQ) (hQn y hy), hTπ y hy]
  have haQ : conjSubgroup a Q = Q := hC.conj_Q_eq haM
  have haQB : conjSubgroup a (QB C) = QB C := by
    rw [← QB_conj, haC]
  set X := Q ⊓ QB C with hX
  have haX : conjSubgroup a X = X := by
    rw [hX, conjSubgroup_inf, haQ, haQB]
  have hZX : Z ≤ X := le_inf hC.Z_le_Q hC.Z_le_QB.1
  have hXQ : X ≤ Q := inf_le_left
  have hUs : ∀ e ∈ M₀.img X, M₀.Qf e = 0 :=
    (M₀.isElemAbelian_iff h.reg hXQ).mp hC.inf_QB_elemAbelian
  have hTU : ∀ e ∈ M₀.img X, T e ∈ M₀.img X := by
    rintro _ ⟨y, hyX, hyQ, rfl⟩
    have hmem : a * y * a⁻¹ ∈ conjSubgroup a X := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hyX
    rw [haX] at hmem
    rw [← haπ y hyQ]
    exact M₀.pi_mem_img hmem hmem.1
  have hcard33 := (hC.card_of_3_3 hw (by omega) hnoC (stroth_3_3 hC hw (by omega))).2
  have hcardX : Nat.card X = Nat.card Z * Nat.card (M₀.img X) := M₀.card_eq hXQ hZX
  have hKZ : Nat.card (GaloisField 2 k) = Nat.card Z := h.card
  have hcardU : Nat.card (M₀.img X) = Nat.card (GaloisField 2 k) ^ n := by
    rw [hKZ]
    have h1 : Nat.card Z * Nat.card (M₀.img X) = Nat.card Z * Nat.card Z ^ n := by
      rw [← hcardX, hX, hcard33, pow_succ, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hK : 1 < Nat.card (GaloisField 2 k) := by
    rw [hKZ]
    have := hc.hyp.q4
    omega
  have hdimE := h.finrank_E hw hK
  obtain ⟨W, hWU, hWperp⟩ := exists_submodule_of_card_eq M₀ hdimE hUs hcardU
  have hbW : b ∈ W :=
    mem_of_perp_le_of_stable M₀ (T := (T : M₀.E →ₗ[GaloisField 2 k] M₀.E)) hTiso hT2 hb0 hbs hdim
      hnz hTr (fun w hw => hUs w ((hWU w).mp hw)) (fun w hw => (hWU _).mpr (hTU w ((hWU w).mp hw)))
      hWperp
  intro u hu
  have huQ : u ∈ Q := hc.le hu
  obtain ⟨s, hs⟩ := (hB _).mp (M₀.pi_mem_img hu huQ)
  have hπu : M₀.π u ∈ M₀.img X := by
    rw [hs]
    exact (hWU _).mp (W.smul_mem s hbW)
  exact ((M₀.mem_img_iff hZX huQ).mp hπu).2

theorem Ctx.conj_le_QB_of_exists_comm (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ conjSubgroup m B)
    (hx1 : x ≠ 1) (hxC : x ∈ Subgroup.centralizer (B : Set G))
    (htx : ∃ t ∈ hc.Spure, t ∉ Q ∧ ⁅t, x⁆ ∈ Z) : conjSubgroup m B ≤ QB B := by
  have hBC : B ≤ QB (conjSubgroup m B) :=
    hc.le_QB_conj_of_exists_comm hw hn hno hm hx hx1 hxC htx
  by_cases hCB : conjSubgroup m B = B
  · rw [hCB]
    exact hc.B_le_QB
  · obtain ⟨g, hg⟩ := hc.conj
    have hC : ∃ h : G, conjSubgroup m B = conjSubgroup h Z :=
      ⟨m * g, by rw [hg, conjSubgroup_mul]⟩
    exact hc.hyp.le_QB_of_le_QB ⟨g, hg⟩ hC (Ne.symm hCB) hBC

end CFSG.RankThree.GF2n.Stroth80
