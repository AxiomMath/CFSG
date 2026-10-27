module

public import CFSG.RankThree.GF2n.Stroth80.Sec34CaseB
public import CFSG.RankThree.GF2n.Stroth80.Sec10Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec34Cubic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem card_range_LB_action {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) :
    Nat.card (φ.comp (Subgroup.inclusion hc.LB_le_H0_cb)).range = Nat.card K ^ (n - 1) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hLH0 : LB M Q B ≤ H0 M Z := hc.LB_le_H0_cb
  have hQL : Q ≤ LB M Q B := le_sup_left
  let ΦL : ↥(LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp (Subgroup.inclusion hLH0)
  have hΦLker : ∀ r : ↥(LB M Q B), ΦL r = 1 ↔ (r : G) ∈ Q := fun r =>
    hφker (Subgroup.inclusion hLH0 r)
  have hcardL : Nat.card (LB M Q B) = Nat.card Q * Nat.card ΦL.range := by
    have hker : ΦL.ker = Q.subgroupOf (LB M Q B) := by
      ext r
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hΦLker r
    have h1 : Nat.card ΦL.ker = Nat.card Q := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
    rw [← h1, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hcardΛ : Nat.card ΦL.range = Nat.card K ^ (n - 1) := by
    have h33 := (hc.card_of_3_3 hw hn1 hno (stroth_3_3 hc hw hn1)).1
    rw [hcardL] at h33
    rw [Nat.eq_of_mul_eq_mul_left Nat.card_pos h33, h.card]
  exact hcardΛ

private theorem exists_flagData_LB_of_action {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B))
    (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    (hφiso : ∀ (m : H0 M Z) e, M₀.Qf (φ m e) = M₀.Qf e)
    {b : M₀.E} (hb0 : b ≠ 0) (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {W : Submodule K M₀.E} (hWmem : ∀ e, e ∈ M₀.img (Q ⊓ QB B) ↔ e ∈ W)
    (hWperp : ∀ v, (∀ u ∈ W, M₀.B v u = 0) → v ∈ W) (hbW : b ∈ W) :
    ∃ Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E),
      Λ = (φ.comp (Subgroup.inclusion hc.LB_le_H0_cb)).range ∧ FlagData M₀ b W Λ := by
  classical
  have hLH0 : LB M Q B ≤ H0 M Z := hc.LB_le_H0_cb
  let ΦL : ↥(LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp (Subgroup.inclusion hLH0)
  have hΦLπ : ∀ (r : ↥(LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((r : G) * x * (r : G)⁻¹) = ΦL r (M₀.π x) := fun r x hx =>
    hφπ (Subgroup.inclusion hLH0 r) x hx
  have hΦLker : ∀ r : ↥(LB M Q B), ΦL r = 1 ↔ (r : G) ∈ Q := fun r =>
    hφker (Subgroup.inclusion hLH0 r)
  have hWs : ∀ w ∈ W, M₀.Qf w = 0 := fun w hw' =>
    (M₀.isElemAbelian_iff h.reg (inf_le_left : Q ⊓ QB B ≤ Q)).mp hc.inf_QB_elemAbelian w
      ((hWmem w).mpr hw')
  have hfix : ∀ r : ↥(LB M Q B), ΦL r b = b := by
    intro r
    obtain ⟨u, huB, huQ, hu⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul K b).symm⟩
    rw [← hu, ← hΦLπ r u huQ]
    exact (M₀.comm_mem_iff huQ ((hc.conj_mem_Q_of_mem_M (hc.LB_le_M r.2)).1 u huQ)).mp
      (hc.comm_B_mem_Z r.2 huB)
  have hflag := fun r : ↥(LB M Q B) => hc.LB_act_flag hw hn hno h hB r.2
    (T := (ΦL r : M₀.E →ₗ[K] M₀.E)) (fun x hx => hΦLπ r x hx)
  refine ⟨ΦL.range, rfl, ?_⟩
  refine ⟨hb0, hbW, hWs, hWperp, ?_, ?_, ?_, ?_, ?_⟩
  · rintro T hT e
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hT
    exact hφiso (Subgroup.inclusion hLH0 r) e
  · rintro T hT
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hT
    exact hfix r
  · rintro T hT y hy
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hT
    exact (hWmem _).mp ((hflag r).2.2 y hy)
  · rintro T hT e he
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hT
    exact (hflag r).2.1 e ((hWmem e).mpr he)
  · rintro T hT T' hT'
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hT
    obtain ⟨r', rfl⟩ := MonoidHom.mem_range.mp hT'
    have hcr : (⁅r, r'⁆ : ↥(LB M Q B)) ∈ ΦL.ker := by
      rw [MonoidHom.mem_ker, hΦLker]
      exact hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator r.2 r'.2)
    have h1 := map_commutatorElement ΦL r r'
    rw [MonoidHom.mem_ker.mp hcr] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1.symm

private theorem flagGroup_faithful_LB {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    {W : Submodule K M₀.E} (hWmem : ∀ e, e ∈ M₀.img (Q ⊓ QB B) ↔ e ∈ W)
    {Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E)}
    (hΛrange : Λ = (φ.comp (Subgroup.inclusion hc.LB_le_H0_cb)).range) :
    ∀ T ∈ Λ, (∀ e ∈ W, T e = e) → T = 1 := by
  classical
  intro T hT hTW
  rw [hΛrange] at hT
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hT
  have hLH0 : LB M Q B ≤ H0 M Z := hc.LB_le_H0_cb
  have hΦLπ : ∀ (r : ↥(LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((r : G) * x * (r : G)⁻¹) = φ (Subgroup.inclusion hLH0 r) (M₀.π x) := fun r x hx =>
    hφπ (Subgroup.inclusion hLH0 r) x hx
  have hrQ : (r : G) ∈ Q := by
    refine hc.mem_Q_of_comm_inf_QB_LB hw hn hno r.2 fun d hd => ?_
    have hdQ : d ∈ Q := (Subgroup.mem_inf.mp hd).1
    have hrd : (r : G) * d * (r : G)⁻¹ ∈ Q :=
      (hc.conj_mem_Q_of_mem_M (hc.LB_le_M r.2)).1 d hdQ
    refine (M₀.comm_mem_iff hdQ hrd).mpr ?_
    rw [hΦLπ r d hdQ]
    exact hTW _ ((hWmem _).mp (M₀.pi_mem_img hd hdQ))
  exact (hφker (Subgroup.inclusion hLH0 r)).mpr hrQ

private theorem flagGroup_mem_Spure_LB {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E)}
    (hΛrange : Λ = (φ.comp (Subgroup.inclusion hc.LB_le_H0_cb)).range)
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ)
    (hTS : ∀ y, M₀.B y b = 0 → T y - y ∈ Submodule.span K {b}) :
    ∃ t ∈ hc.Spure, ∃ ht : t ∈ H0 M Z, φ ⟨t, ht⟩ = T := by
  classical
  rw [hΛrange] at hT
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hT
  have hLH0 : LB M Q B ≤ H0 M Z := hc.LB_le_H0_cb
  have hΦLπ : ∀ (r : ↥(LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((r : G) * x * (r : G)⁻¹) =
        (φ.comp (Subgroup.inclusion hLH0)) r (M₀.π x) := fun r x hx =>
    hφπ (Subgroup.inclusion hLH0 r) x hx
  have hrS : (r : G) ∈ hc.Spure := by
    refine hc.mem_Spure.mpr ⟨r.2, fun y hy => ?_⟩
    obtain ⟨hyQ, hyC⟩ := hy
    obtain ⟨hQn, hQn'⟩ := hc.conj_mem_Q_of_mem_M (hc.LB_le_M r.2)
    have hkQ : ⁅(r : G), y⁆ ∈ Q := by
      rw [show ⁅(r : G), y⁆ = ((r : G) * y * (r : G)⁻¹) * y⁻¹ by rw [commutatorElement_def]]
      exact Q.mul_mem (hQn y hyQ) (Q.inv_mem hyQ)
    have hπ : M₀.π ⁅(r : G), y⁆ =
        (φ.comp (Subgroup.inclusion hLH0)) r (M₀.π y) - M₀.π y := by
      rw [show ⁅(r : G), y⁆ = ((r : G) * y * (r : G)⁻¹) * y⁻¹ by rw [commutatorElement_def],
        M₀.π_mul _ (hQn y hyQ) _ (Q.inv_mem hyQ), hΦLπ r y hyQ,
        Tim79.QuadModel.pi_inv M₀ hyQ, sub_eq_add_neg]
    obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.mp (hTS _ ((hcent y hyQ).mp hyC))
    have hmem : M₀.π ⁅(r : G), y⁆ ∈ M₀.img B := (hB _).mpr ⟨c, by rw [hπ, ← hc']⟩
    exact (M₀.mem_img_iff le_sup_right hkQ).mp (M₀.img_mono le_sup_left hmem)
  exact ⟨r, hrS, hLH0 r.2, rfl⟩

theorem Ctx.exists_flagData_LB {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    (hφiso : ∀ (m : H0 M Z) e, M₀.Qf (φ m e) = M₀.Qf e)
    {b : M₀.E} (hb0 : b ≠ 0) (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {W : Submodule K M₀.E} (hWmem : ∀ e, e ∈ M₀.img (Q ⊓ QB B) ↔ e ∈ W)
    (hWperp : ∀ v, (∀ u ∈ W, M₀.B v u = 0) → v ∈ W) (hbW : b ∈ W) :
    ∃ Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E), FlagData M₀ b W Λ ∧
      (∀ T ∈ Λ, (∀ e ∈ W, T e = e) → T = 1) ∧ Nat.card Λ = Nat.card K ^ (n - 1) ∧
      ∀ T ∈ Λ, (∀ y, M₀.B y b = 0 → T y - y ∈ Submodule.span K {b}) →
        ∃ t ∈ hc.Spure, ∃ ht : t ∈ H0 M Z, φ ⟨t, ht⟩ = T := by
  obtain ⟨Λ, hΛdef, hFD⟩ :=
    exists_flagData_LB_of_action hc hw hn hno h φ hφπ hφker hφiso hb0 hB hcent hWmem hWperp hbW
  refine ⟨Λ, hFD, ?_, ?_, ?_⟩
  · exact flagGroup_faithful_LB hc hw hn hno φ hφπ hφker hWmem hΛdef
  · rw [hΛdef]
    exact card_range_LB_action hc hw hn hno h φ hφker
  · intro T hT hTS
    exact flagGroup_mem_Spure_LB hc φ hφπ hB hcent hΛdef hT hTS

theorem Ctx.n_ne_three_five_of_conc34 (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hno : NoA2 Q Z (LB M Q B)) (h34 : Conc34 M Q Z B) : n ≠ 3 ∧ n ≠ 5 := by
  rcases Nat.lt_or_ge 2 n with hn | hn
  swap
  · omega
  have hS : hc.Spure ≤ Q := hc.Spure_le_Q_of_conc34 h34
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨b, hb0, -, hB, hcent, -⟩ := hc.dictB h
  obtain ⟨W, hWmem, hWn, hWperp, -⟩ := hc.lagr hw hn hno h
  have hbW : b ∈ W := (hWmem b).mp
    (M₀.img_mono (le_inf hc.le hc.B_le_QB) ((hB b).mpr ⟨1, (one_smul _ b).symm⟩))
  obtain ⟨Λ, hFD, hinj, hcard, hSp⟩ :=
    hc.exists_flagData_LB hw hn hno h φ hφπ hφker hφiso hb0 hB hcent hWmem hWperp hbW
  obtain ⟨f₁, hf₁⟩ := Tim79.QuadModel.exists_B_ne_zero hb0
  have hf₀ : M₀.B ((M₀.B f₁ b)⁻¹ • f₁) b = 1 := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₁]
  have hbW0 : (⟨b, hbW⟩ : W) ≠ 0 := fun h0 => hb0 (congrArg Subtype.val h0)
  have hsurj := hFD.psi_surj hinj hf₀ (card_dual_ker_eval hWn ⟨b, hbW⟩ hbW0) hcard
  have hN : ∀ T ∈ Λ,
      (∀ y, M₀.B y b = 0 → T y - y ∈ Submodule.span (GaloisField 2 m) {b}) → T = 1 := by
    intro T hT hTb
    obtain ⟨t, htS, ht, rfl⟩ := hSp T hT hTb
    exact (hφker ⟨t, ht⟩).mpr (hS htS)
  have hK : 1 < Nat.card (GaloisField 2 m) := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  exact hFD.n_ne_three_five hf₀ hsurj hN (h.finrank_E hw hK) hWn

theorem Ctx.n_ne_three_five (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) :
    n ≠ 3 ∧ n ≠ 5 := by
  rcases Nat.lt_or_ge 2 n with hn | hn
  · exact hc.n_ne_three_five_of_conc34 hw hno (h34 G M Q Z B hc n hw hn hno hgen)
  · omega

theorem Sec10Hyp.n_ne_three_five (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) : n ≠ 3 ∧ n ≠ 5 :=
  hc.n_ne_three_five h34 H.width H.noA2 H.gen

theorem Sec10Hyp.false_of_five (h34 : Stroth34Statement) {hc : Ctx M Q Z B}
    (H : Sec10Hyp hc 5) : False :=
  (H.n_ne_three_five h34).2 rfl

end CFSG.RankThree.GF2n.Stroth80
