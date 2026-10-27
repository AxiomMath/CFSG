module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Action
public import CFSG.RankThree.GF2n.Stroth80.Sec34Model

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.LB_conj_mem_BZ (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {x : G}
    (hx : x ∈ (B ⊔ Z : Subgroup G)) : t * x * t⁻¹ ∈ (B ⊔ Z : Subgroup G) := by
  have hBN : B ≤ Subgroup.normalizer (Z : Set G) := fun u hu =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.le hu))
  obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN hx
  have e : t * (u * z) * t⁻¹ = ⁅t, u⁆ * (u * (t * z * t⁻¹)) := by
    simp only [commutatorElement_def]; group
  rw [e, hc.LB_centralizes_Z ht z hz]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hc.comm_B_mem_Z ht hu))
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hz))

@[expose] def Ctx.Spure (hc : Ctx M Q Z B) : Subgroup G where
  carrier := {t | t ∈ LB M Q B ∧
    ∀ y ∈ Q ⊓ Subgroup.centralizer (B : Set G), ⁅t, y⁆ ∈ (B ⊔ Z : Subgroup G)}
  mul_mem' := by
    rintro a b ⟨ha, hay⟩ ⟨hb, hby⟩
    refine ⟨(LB M Q B).mul_mem ha hb, fun y hy => ?_⟩
    have e : ⁅a * b, y⁆ = (a * ⁅b, y⁆ * a⁻¹) * ⁅a, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (B ⊔ Z : Subgroup G).mul_mem (hc.LB_conj_mem_BZ ha (hby y hy)) (hay y hy)
  one_mem' := by
    refine ⟨(LB M Q B).one_mem, fun y _ => ?_⟩
    rw [show ⁅(1 : G), y⁆ = 1 by simp [commutatorElement_def]]
    exact (B ⊔ Z : Subgroup G).one_mem
  inv_mem' := by
    rintro a ⟨ha, hay⟩
    refine ⟨(LB M Q B).inv_mem ha, fun y hy => ?_⟩
    have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := hc.LB_conj_mem_BZ ((LB M Q B).inv_mem ha) ((B ⊔ Z : Subgroup G).inv_mem (hay y hy))
    simpa using this

theorem Ctx.mem_Spure {hc : Ctx M Q Z B} {t : G} :
    t ∈ hc.Spure ↔ t ∈ LB M Q B ∧
      ∀ y ∈ Q ⊓ Subgroup.centralizer (B : Set G), ⁅t, y⁆ ∈ (B ⊔ Z : Subgroup G) := Iff.rfl

theorem Ctx.Q_le_Spure (hc : Ctx M Q Z B) : Q ≤ hc.Spure := fun x hx =>
  ⟨Subgroup.mem_sup_left hx, fun y hy =>
    Subgroup.mem_sup_right (hc.hyp.toHyp79.comm_mem_V hx hy.1)⟩

theorem Ctx.Spure_le_H0 (hc : Ctx M Q Z B) : hc.Spure ≤ H0 M Z := fun t ht =>
  ⟨hc.LB_le_M ht.1, Subgroup.mem_centralizer_iff.mpr fun z hz => by
    have := hc.LB_centralizes_Z ht.1 z hz
    calc z * t = (t * z * t⁻¹) * t := by rw [this]
      _ = t * z := by group⟩

theorem Ctx.Spure_le_Q_iff (hc : Ctx M Q Z B) : hc.Spure ≤ Q ↔ Conc34' M Q Z B := by
  constructor
  · intro hS t ht hcomm
    exact hS ⟨Subgroup.mem_sup_right ht, hcomm⟩
  · intro hC t ht
    obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB ht.1
    have hsZ : ∀ z ∈ Z, s * z * s⁻¹ ∈ Z := fun z hz =>
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hs.2) z).mp hz
    have hs' : s ∈ Q := hC s hs fun x hx => by
      have e : ⁅s * y, x⁆ = (s * ⁅y, x⁆ * s⁻¹) * ⁅s, x⁆ := by
        simp only [commutatorElement_def]; group
      have h1 : ⁅y, x⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hy hx.1
      have h2 : ⁅s, x⁆ = (s * ⁅y, x⁆ * s⁻¹)⁻¹ * ⁅s * y, x⁆ := by rw [e]; group
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right (hsZ _ h1)))
        (ht.2 x hx)
    exact Q.mul_mem hs' hy

theorem Ctx.conj_mem_Q_of_mem_M (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M) :
    (∀ x ∈ Q, t * x * t⁻¹ ∈ Q) ∧ ∀ x ∈ Q, t⁻¹ * x * t ∈ Q := by
  refine ⟨fun x hx => (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 htM) x).mp hx,
    fun x hx => ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem htM)) x).mp hx
  simpa using this

section Act

variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.Spure_act (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {t : G} (ht : t ∈ hc.Spure) {T : M₀.E → M₀.E}
    (hT : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) :
    T b = b ∧ ∀ y : M₀.E, M₀.B y b = 0 → ∃ c : K, T y = y + c • b := by
  have hQn := (hc.conj_mem_Q_of_mem_M (hc.LB_le_M ht.1)).1
  have hle : (B ⊔ Z : Subgroup G) ≤ M₀.lift (M₀.img B) := by
    refine sup_le (fun u hu => ⟨hc.le hu, M₀.pi_mem_img hu (hc.le hu)⟩) (fun z hz => ?_)
    refine ⟨h.reg.V_le hz, ?_⟩
    rw [(M₀.π_ker z (h.reg.V_le hz)).mpr hz]
    exact AddSubgroup.zero_mem _
  refine ⟨?_, fun y hy => ?_⟩
  · obtain ⟨u, huB, huQ, hu⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul _ b).symm⟩
    rw [← hu, ← hT u huQ]
    exact (M₀.comm_mem_iff huQ (hQn u huQ)).mp (hc.comm_B_mem_Z ht.1 huB)
  · obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj y
    have hcomm := ht.2 x ⟨hxQ, (hcent x hxQ).mpr hy⟩
    have hπ : M₀.π ⁅t, x⁆ = T (M₀.π x) - M₀.π x := by
      rw [show ⁅t, x⁆ = (t * x * t⁻¹) * x⁻¹ by rw [commutatorElement_def],
        M₀.π_mul _ (hQn x hxQ) _ (Q.inv_mem hxQ), hT x hxQ, Tim79.QuadModel.pi_inv M₀ hxQ,
        sub_eq_add_neg]
    obtain ⟨s, hs⟩ := (hB _).mp (hle hcomm).2
    refine ⟨s, ?_⟩
    rw [hπ] at hs
    rw [← hs]
    abel

end Act

theorem Ctx.card_comm_Spure (hc : Ctx M Q Z B) {t : G} (ht : t ∈ hc.Spure) (htQ : t ∉ Q) :
    Nat.card ↥(⁅Q, Subgroup.zpowers t⁆ ⊔ Z) = Nat.card Z ^ 3 := by
  obtain ⟨m, γ, M₀, hm, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  have htM : t ∈ M := hc.LB_le_M ht.1
  obtain ⟨hQn, hQn'⟩ := hc.conj_mem_Q_of_mem_M htM
  obtain ⟨T, hTπ, hTiso, -⟩ := h.linear_of_centralizes htM (hc.LB_centralizes_Z ht.1)
  obtain ⟨hTb, hTr⟩ := hc.Spure_act h hB hcent ht hTπ
  have hne : ∃ e, T e ≠ e := by
    by_contra hcon
    push Not at hcon
    exact htQ (mem_Q_of_pi_conj_eq (M₀ := M₀) hc.hyp htM fun x hx => by rw [hTπ x hx, hcon])
  have hfin := Tim79.QuadModel.finrank_range_eq_two (T := (T : M₀.E →ₗ[GaloisField 2 m] M₀.E))
    hTiso hb0 hbs hTr hne
  rw [card_comm_zpowers_sup M₀ h.reg T hQn hQn' hTπ, hfin, h.card]
  ring

theorem Ctx.not_elemAbelian_comm_Spure (hc : Ctx M Q Z B) (hno : NoA2 Q Z (LB M Q B)) {t : G}
    (ht : t ∈ hc.Spure) (htQ : t ∉ Q) : ¬ IsElemAbelian 2 ⁅Q, Subgroup.zpowers t⁆ := by
  intro hel
  exact hno t ht.1 ⟨hc.hyp.Q_normal.2 (hc.LB_le_M ht.1), htQ, hc.sq_mem_Q_of_mem_LB ht.1,
    hc.card_comm_Spure ht htQ, hel⟩

theorem Ctx.card_Spure_le (hc : Ctx M Q Z B) (hno : NoA2 Q Z (LB M Q B)) :
    Nat.card hc.Spure ≤ Nat.card Q * Nat.card Z ^ 2 := by
  obtain ⟨m, γ, M₀, hm, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  let Φ : ↥hc.Spure →* (M₀.E ≃ₗ[GaloisField 2 m] M₀.E) :=
    φ.comp (Subgroup.inclusion hc.Spure_le_H0)
  have hΦπ : ∀ (s : ↥hc.Spure) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = Φ s (M₀.π x) := fun s x hx =>
    hφπ (Subgroup.inclusion hc.Spure_le_H0 s) x hx
  have hΦker : ∀ s : ↥hc.Spure, Φ s = 1 ↔ (s : G) ∈ Q := fun s =>
    hφker (Subgroup.inclusion hc.Spure_le_H0 s)
  have hQS : Q ≤ hc.Spure := hc.Q_le_Spure
  have hkerΦ : Φ.ker = Q.subgroupOf hc.Spure := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hΦker s
  have hcard : Nat.card hc.Spure = Nat.card Q * Nat.card Φ.range := by
    have h1 : Nat.card Φ.ker = Nat.card Q := by
      rw [hkerΦ]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv
    rw [← h1, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hΛ : Nat.card Φ.range ≤ Nat.card (GaloisField 2 m) ^ 2 := by
    refine card_le_sq_of_eichler_group M₀ Φ.range hb0 hbs ?_ ?_ ?_ ?_
    · rintro _ ⟨s, rfl⟩ e
      exact hφiso (Subgroup.inclusion hc.Spure_le_H0 s) e
    · rintro _ ⟨s, rfl⟩
      exact (hc.Spure_act h hB hcent s.2 (hΦπ s)).1
    · rintro _ ⟨s, rfl⟩ y hy
      exact (hc.Spure_act h hB hcent s.2 (hΦπ s)).2 y hy
    · rintro _ ⟨s, rfl⟩ hv
      by_contra hne
      have hsQ : (s : G) ∉ Q := fun hsQ => hne ((hΦker s).mpr hsQ)
      obtain ⟨hQn, hQn'⟩ := hc.conj_mem_Q_of_mem_M (hc.LB_le_M s.2.1)
      refine hc.not_elemAbelian_comm_Spure hno s.2 hsQ ?_
      rw [isElemAbelian_comm_zpowers_iff M₀ h.reg (Φ s) hQn hQn' (hΦπ s)]
      exact hv
  calc Nat.card hc.Spure = Nat.card Q * Nat.card Φ.range := hcard
    _ ≤ Nat.card Q * Nat.card (GaloisField 2 m) ^ 2 := Nat.mul_le_mul_left _ hΛ
    _ = Nat.card Q * Nat.card Z ^ 2 := by rw [h.card]

theorem Ctx.Spure_le_Q_of_conc34 (hc : Ctx M Q Z B) (h : Conc34 M Q Z B) : hc.Spure ≤ Q := by
  rw [hc.Spure_le_Q_iff]
  obtain ⟨n, h1, h2, h3, h4⟩ := hc.exists_swap'
  have hC : conjSubgroup n (QB B ⊓ Subgroup.centralizer (Z : Set G)) =
      Q ⊓ Subgroup.centralizer (B : Set G) := by
    rw [conjSubgroup_inf, conjSubgroup_centralizer, h2, h3]
  have hC' := hc.conj_centralizer_B h1 h4
  have hXC : conjSubgroup n (QB B ⊓ M ⊓ hc.Spure) ≤ Q ⊓ Subgroup.centralizer (B : Set G) := by
    rw [← hC]
    refine Subgroup.map_mono fun y hy => ?_
    rw [← hc.QB_inf_M_eq]
    exact hy.1
  have hXL : ∀ x ∈ conjSubgroup n (QB B ⊓ M ⊓ hc.Spure), ∀ l ∈ LB M Q B,
      ⁅l, x⁆ ∈ (B ⊔ Z : Subgroup G) := by
    intro x hx l hl
    have hxQ : x ∈ Q := (hXC hx).1
    have hs' := mem_conjSubgroup.mp hx
    obtain ⟨l₀, hl₀, q, hq, rfl⟩ := hc.exists_mul_of_mem_LB hl
    have hl₀Z : ∀ z ∈ Z, l₀ * z * l₀⁻¹ ∈ Z := fun z hz =>
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hl₀.2) z).mp hz
    have hl₀C : l₀ ∈ conjSubgroup n (Q ⊓ Subgroup.centralizer (B : Set G)) := by
      rw [hC', ← hc.QB_inf_M_eq]
      exact hl₀
    have hy := mem_conjSubgroup.mp hl₀C
    have h5 : ⁅n⁻¹ * x * n, n⁻¹ * l₀ * n⁆ ∈ (B ⊔ Z : Subgroup G) := hs'.2.2 _ hy
    have h5' : ⁅n⁻¹ * l₀ * n, n⁻¹ * x * n⁆ ∈ (B ⊔ Z : Subgroup G) := by
      have := (B ⊔ Z : Subgroup G).inv_mem h5
      rwa [commutatorElement_inv] at this
    have h7 : ⁅l₀, x⁆ ∈ (B ⊔ Z : Subgroup G) := by
      have e : ⁅l₀, x⁆ = n * ⁅n⁻¹ * l₀ * n, n⁻¹ * x * n⁆ * n⁻¹ := by
        simp only [commutatorElement_def]; group
      have : n * ⁅n⁻¹ * l₀ * n, n⁻¹ * x * n⁆ * n⁻¹ ∈ conjSubgroup n (B ⊔ Z : Subgroup G) :=
        ⟨_, h5', by show (MulAut.conj n) _ = _; rw [MulAut.conj_apply]⟩
      rw [conjSubgroup_sup', h3, h4, sup_comm] at this
      rwa [e]
    have e : ⁅l₀ * q, x⁆ = (l₀ * ⁅q, x⁆ * l₀⁻¹) * ⁅l₀, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (B ⊔ Z : Subgroup G).mul_mem
      (Subgroup.mem_sup_right (hl₀Z _ (hc.hyp.toHyp79.comm_mem_V hq hxQ))) h7
  intro s hs hcomm
  have hsT : s ∈ QB B ⊓ M ⊓ hc.Spure := ⟨hs, Subgroup.mem_sup_right hs, hcomm⟩
  have hx : n * s * n⁻¹ ∈ conjSubgroup n (QB B ⊓ M ⊓ hc.Spure) :=
    mem_conjSubgroup.mpr (by simpa [mul_assoc] using hsT)
  have hxB : n * s * n⁻¹ ∈ QB B := (h _ hXC hXL hx).2
  rw [← h1, mem_conjSubgroup] at hxB
  simpa [mul_assoc] using hxB

theorem Ctx.conc34_iff_Spure_le_Q (hc : Ctx M Q Z B) : Conc34 M Q Z B ↔ hc.Spure ≤ Q :=
  ⟨hc.Spure_le_Q_of_conc34, fun h => hc.conc34_of_star (hc.Spure_le_Q_iff.mp h)⟩

theorem Ctx.comm_mem_inf_of_mem_LB (hc : Ctx M Q Z B) {t y : G} (ht : t ∈ LB M Q B)
    (hy : y ∈ Q ⊓ Subgroup.centralizer (B : Set G)) : ⁅t, y⁆ ∈ Q ⊓ QB B := by
  obtain ⟨s, hs, q, hq, rfl⟩ := hc.exists_mul_of_mem_LB ht
  have hsZ : ∀ z ∈ Z, s * z * s⁻¹ ∈ Z := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hs.2) z).mp hz
  have hZ : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have e : ⁅s * q, y⁆ = (s * ⁅q, y⁆ * s⁻¹) * ⁅s, y⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Q ⊓ QB B).mul_mem (hZ (hsZ _ (hc.hyp.toHyp79.comm_mem_V hq hy.1)))
    (hc.comm_mem_inf ⟨hs.1, hc.QB_inf_M_le hs⟩ hy)

theorem Ctx.mem_Spure_of_c2 (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (hcard : Nat.card ↥(⁅Q, Subgroup.zpowers t⁆ ⊔ Z) = Nat.card Z ^ 3)
    (hnel : ¬ IsElemAbelian 2 ⁅Q, Subgroup.zpowers t⁆) : t ∈ hc.Spure := by
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, -, hB, hcent, -⟩ := hc.dictB h
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨hQn, hQn'⟩ := hc.conj_mem_Q_of_mem_M htM
  obtain ⟨T, hTπ, hTiso, -⟩ := h.linear_of_centralizes htM (hc.LB_centralizes_Z ht)
  have hT2 : ∀ e, T (T e) = e := by
    intro e
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
    rw [← hTπ y hyQ, ← hTπ _ (hQn y hyQ)]
    have : t * (t * y * t⁻¹) * t⁻¹ = t ^ 2 * y * (t ^ 2)⁻¹ := by rw [pow_two]; group
    rw [this, Tim79.QuadModel.pi_conj_self (M₀ := M₀) (hc.sq_mem_Q_of_mem_LB ht) hyQ]
  have hdim : Module.finrank (GaloisField 2 m)
      (LinearMap.range ((T : M₀.E →ₗ[GaloisField 2 m] M₀.E) - 1)) = 2 := by
    have h1 := card_comm_zpowers_sup M₀ h.reg T hQn hQn' hTπ
    rw [hcard, h.card] at h1
    have hZ4 : 4 ≤ Nat.card Z := hc.hyp.q4
    have h2 : Nat.card Z * Nat.card Z ^ 2 = Nat.card Z * Nat.card Z ^ Module.finrank
        (GaloisField 2 m) (LinearMap.range ((T : M₀.E →ₗ[GaloisField 2 m] M₀.E) - 1)) := by
      rw [← h1]; ring
    exact (Nat.pow_right_injective (by omega) (Nat.eq_of_mul_eq_mul_left (by omega) h2)).symm
  have hnz : ∃ v ∈ LinearMap.range ((T : M₀.E →ₗ[GaloisField 2 m] M₀.E) - 1), M₀.Qf v ≠ 0 := by
    rw [isElemAbelian_comm_zpowers_iff M₀ h.reg T hQn hQn' hTπ] at hnel
    push Not at hnel
    exact hnel
  have hsing : ∀ e ∈ M₀.img (Q ⊓ QB B), M₀.Qf e = 0 :=
    (M₀.isElemAbelian_iff h.reg (inf_le_left : Q ⊓ QB B ≤ Q)).mp hc.inf_QB_elemAbelian
  have hπ : ∀ x ∈ Q, M₀.π ⁅t, x⁆ = T (M₀.π x) - M₀.π x := fun x hxQ => by
    rw [show ⁅t, x⁆ = (t * x * t⁻¹) * x⁻¹ by rw [commutatorElement_def],
      M₀.π_mul _ (hQn x hxQ) _ (Q.inv_mem hxQ), hTπ x hxQ, Tim79.QuadModel.pi_inv M₀ hxQ,
      sub_eq_add_neg]
  have hU : ∀ e : M₀.E, M₀.B e b = 0 →
      M₀.Qf ((T : M₀.E →ₗ[GaloisField 2 m] M₀.E) e - e) = 0 := by
    intro e he
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    have hr := hc.comm_mem_inf_of_mem_LB ht ⟨hxQ, (hcent x hxQ).mpr he⟩
    have := hsing _ (M₀.pi_mem_img hr hr.1)
    rwa [hπ x hxQ] at this
  have hmain := eichler_of_involution M₀ (T := (T : M₀.E →ₗ[GaloisField 2 m] M₀.E))
    hTiso hT2 hb0 hdim hnz hU
  refine hc.mem_Spure.mpr ⟨ht, fun y hy => ?_⟩
  obtain ⟨hyQ, hyC⟩ := hy
  have hr := hc.comm_mem_inf_of_mem_LB ht ⟨hyQ, hyC⟩
  obtain ⟨c, hc'⟩ := hmain (M₀.π y) ((hcent y hyQ).mp hyC)
  have hc'' : T (M₀.π y) = M₀.π y + c • b := hc'
  have hmem : M₀.π ⁅t, y⁆ ∈ M₀.img B := (hB _).mpr ⟨c, by rw [hπ y hyQ, hc'']; abel⟩
  exact (M₀.mem_img_iff le_sup_right hr.1).mp (M₀.img_mono le_sup_left hmem)

theorem Ctx.Spure_conj_mem_Z_iff (hc : Ctx M Q Z B) {t : G} (ht : t ∈ hc.Spure) (z : G) :
    t * z * t⁻¹ ∈ Z ↔ z ∈ Z :=
  (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hc.LB_le_M ht.1)) z).symm

theorem Ctx.exists_Spure_comm_mem_Z (hc : Ctx M Q Z B)
    (hS : Nat.card Q * Nat.card Z < Nat.card hc.Spure) {x : G} (hxQ : x ∈ Q)
    (hxC : x ∈ Subgroup.centralizer (B : Set G)) :
    ∃ t ∈ hc.Spure, t ∉ Q ∧ ⁅t, x⁆ ∈ Z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨K, hK⟩ : ∃ K : Subgroup hc.Spure, ∀ t : hc.Spure, t ∈ K ↔ ⁅(t : G), x⁆ ∈ Z := by
    refine ⟨{ carrier := {t | ⁅(t : G), x⁆ ∈ Z}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun _ => Iff.rfl⟩
    · intro a b ha hb
      have e : ⁅(a : G) * (b : G), x⁆ = ((a : G) * ⁅(b : G), x⁆ * (a : G)⁻¹) * ⁅(a : G), x⁆ := by
        simp only [commutatorElement_def]; group
      show ⁅(a : G) * (b : G), x⁆ ∈ Z
      rw [e]
      exact Z.mul_mem ((hc.Spure_conj_mem_Z_iff a.2 _).mpr hb) ha
    · show ⁅((1 : hc.Spure) : G), x⁆ ∈ Z
      rw [show ⁅((1 : hc.Spure) : G), x⁆ = 1 by simp [commutatorElement_def]]
      exact Z.one_mem
    · intro a ha
      have e : ⁅(a : G)⁻¹, x⁆ = (a : G)⁻¹ * ⁅(a : G), x⁆⁻¹ * (a : G) := by
        simp only [commutatorElement_def]; group
      show ⁅(a : G)⁻¹, x⁆ ∈ Z
      rw [e]
      have := (hc.Spure_conj_mem_Z_iff (hc.Spure.inv_mem a.2) _).mpr (Z.inv_mem ha)
      rwa [inv_inv] at this
  have hmem : ∀ t : hc.Spure, ⁅x, (t : G)⁆ ∈ (B ⊔ Z : Subgroup G) := fun t => by
    rw [← commutatorElement_inv]
    exact (B ⊔ Z : Subgroup G).inv_mem (t.2.2 x ⟨hxQ, hxC⟩)
  have hiff : ∀ a b : hc.Spure, a⁻¹ * b ∈ K ↔ ⁅x, (a : G)⁆⁻¹ * ⁅x, (b : G)⁆ ∈ Z := by
    intro a b
    rw [hK]
    have e : ⁅(a : G)⁻¹ * (b : G), x⁆ =
        (a : G)⁻¹ * (⁅x, (a : G)⁆⁻¹ * ⁅x, (b : G)⁆)⁻¹ * (a : G) := by
      simp only [commutatorElement_def]; group
    show ⁅(a : G)⁻¹ * (b : G), x⁆ ∈ Z ↔ _
    rw [e]
    have h1 := hc.Spure_conj_mem_Z_iff (hc.Spure.inv_mem a.2)
      (⁅x, (a : G)⁆⁻¹ * ⁅x, (b : G)⁆)⁻¹
    rw [inv_inv] at h1
    rw [h1, Subgroup.inv_mem_iff]
  have hbB : Nat.card B = Nat.card Z := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg]
    exact card_conjSubgroup g Z
  have hrel : Z.relIndex (B ⊔ Z) = Nat.card Z := by
    have h := Subgroup.relIndex_mul_card Z (B ⊔ Z)
    rw [inf_eq_left.mpr le_sup_right, hc.card_sup_Z, hbB] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hidx : K.index ≤ Nat.card Z := by
    rw [← hrel]
    refine Nat.card_le_card_of_injective (Quotient.lift (s := QuotientGroup.leftRel K)
      (fun t : hc.Spure => (QuotientGroup.mk ⟨⁅x, (t : G)⁆, hmem t⟩ :
        ↥(B ⊔ Z) ⧸ Z.subgroupOf (B ⊔ Z))) fun a b hab => ?_) ?_
    · exact QuotientGroup.eq.mpr ((hiff a b).mp (QuotientGroup.leftRel_apply.mp hab))
    · rintro ⟨a⟩ ⟨b⟩ h
      have h3 : (⟨⁅x, (a : G)⁆, hmem a⟩ : ↥(B ⊔ Z))⁻¹ * ⟨⁅x, (b : G)⁆, hmem b⟩ ∈
          Z.subgroupOf (B ⊔ Z) := QuotientGroup.eq.mp h
      exact Quotient.sound' (QuotientGroup.leftRel_apply.mpr ((hiff a b).mpr h3))
  have hKQ : Nat.card K ≤ Nat.card Q := by
    refine Nat.card_le_card_of_injective (fun t : K => (⟨((t : hc.Spure) : G), ?_⟩ : Q)) ?_
    · by_contra hnot
      exact hcon _ (t : hc.Spure).2 hnot ((hK _).mp t.2)
    · intro s t h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
  have h1 := Subgroup.card_mul_index K
  exact (not_le.mpr hS) (h1 ▸ Nat.mul_le_mul hKQ hidx)

theorem Ctx.conj_mem_Spure (hc : Ctx M Q Z B) (hno : NoA2 Q Z (LB M Q B)) {m t : G} (hm : m ∈ M)
    (ht : t ∈ hc.Spure) (hmt : m * t * m⁻¹ ∈ LB M Q B) : m * t * m⁻¹ ∈ hc.Spure := by
  by_cases htQ : t ∈ Q
  · exact hc.Q_le_Spure ((hc.conj_mem_Q_of_mem_M hm).1 t htQ)
  · have hQ : conjSubgroup m Q = Q := hc.conj_Q_eq hm
    refine hc.mem_Spure_of_c2 hmt ?_ ?_
    · rw [card_comm_zpowers_conj hQ (hc.conj_Z_eq hm) t]
      exact hc.card_comm_Spure ht htQ
    · rw [isElemAbelian_comm_zpowers_conj (hc.hyp.Q_normal.2 hm) t]
      exact hc.not_elemAbelian_comm_Spure hno ht htQ

theorem Ctx.le_QB_conj_of_card_Spure (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (hS : Nat.card Q * Nat.card Z < Nat.card hc.Spure) {m : G}
    (hm : m ∈ M) {x : G} (hx : x ∈ conjSubgroup m B) (hx1 : x ≠ 1)
    (hxC : x ∈ Subgroup.centralizer (B : Set G)) : B ≤ QB (conjSubgroup m B) := by
  have hC : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hnoC := hc.noA2_conj hno hm
  set C := conjSubgroup m B
  have hxQ : x ∈ Q := hC.le hx
  obtain ⟨t, htS, htQ, htx⟩ := hc.exists_Spure_comm_mem_Z hS hxQ hxC
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

end CFSG.RankThree.GF2n.Stroth80
