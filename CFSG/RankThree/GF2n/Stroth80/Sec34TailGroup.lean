module

public import CFSG.RankThree.GF2n.Stroth80.Sec34TailOvoid
import CFSG.RankThree.GF2n.Stroth80.Sec39
public import CFSG.RankThree.GF2n.Stroth80.Sec34Spure

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Model

omit [Finite G]

private theorem unit_eq_one_of_mul_self {K : Type*} [Field K] [CharP K 2] (u : Kˣ)
    (hu : u * u = 1) : u = 1 := by
  have h1 : (u : K) * u = 1 := by rw [← Units.val_mul, hu, Units.val_one]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : ((u : K) - 1) * ((u : K) - 1) = 0 := by
    linear_combination h1 + (1 - (u : K)) * h2
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp (mul_self_eq_zero.mp h3))

private theorem closure_hom_eq_one {Γ K : Type*} [Group Γ] [Field K] [CharP K 2] {X : Set Γ}
    (hX : ∀ x ∈ X, x * x = 1) (χ : Subgroup.closure X →* Kˣ) : χ = 1 := by
  refine MonoidHom.ext fun g => ?_
  obtain ⟨g, hg⟩ := g
  rw [MonoidHom.one_apply]
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    apply unit_eq_one_of_mul_self
    rw [← map_mul]
    have e : (⟨x, Subgroup.subset_closure hx⟩ : Subgroup.closure X) *
        ⟨x, Subgroup.subset_closure hx⟩ = 1 := Subtype.ext (hX x hx)
    rw [e, map_one]
  | one => exact map_one χ
  | mul x y hx hy ihx ihy =>
    have e : (⟨x * y, Subgroup.mul_mem _ hx hy⟩ : Subgroup.closure X) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e, map_mul, ihx, ihy, one_mul]
  | inv x hx ih =>
    have e : (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : Subgroup.closure X) = (⟨x, hx⟩)⁻¹ := rfl
    rw [e, map_inv, ih, inv_one]

variable {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel QF V K γ}

private theorem mem_range_of_eichler {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e)
    {b : M₀.E} (hb0 : b ≠ 0) (hbs : M₀.Qf b = 0)
    (hr : ∀ y, M₀.B y b = 0 → ∃ c : K, T y = y + c • b) (hne : ∃ e, T e ≠ e) :
    b ∈ LinearMap.range (T - 1) := by
  obtain ⟨e, he⟩ := hne
  by_cases hA : ∀ y, M₀.B y b = 0 → T y = y
  · exact absurd (Tim79.QuadModel.eq_one_of_fix_perp hT hb0 hbs hA e) he
  · push Not at hA
    obtain ⟨y₀, hy₀, hTy₀⟩ := hA
    obtain ⟨c₀, hc₀⟩ := hr y₀ hy₀
    have hc₀0 : c₀ ≠ 0 := by
      rintro rfl
      exact hTy₀ (by rw [hc₀, zero_smul, add_zero])
    exact ⟨c₀⁻¹ • y₀, by
      rw [map_smul, LinearMap.sub_apply, Module.End.one_apply, hc₀, add_sub_cancel_left,
        smul_smul, inv_mul_cancel₀ hc₀0, one_smul]⟩

private theorem not_smul_of_mem_range {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e)
    {b b' : M₀.E} (hbb' : M₀.B b b' ≠ 0) (hTb' : T b' = b')
    (hb'R : b' ∈ LinearMap.range (T - 1)) {μ : K} (hTb : T b = μ • b) : False := by
  have h1 := Tim79.QuadModel.B_iso hT b b'
  rw [hTb, hTb', map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  have hμ : μ = 1 := by
    have h2 : (μ - 1) * M₀.B b b' = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hbb')
  rw [hμ, one_smul] at hTb
  obtain ⟨f, hf⟩ := hb'R
  apply hbb'
  rw [← hf, LinearMap.sub_apply, Module.End.one_apply, map_sub, ← Tim79.QuadModel.B_iso hT b f,
    hTb, sub_self]

end Model

private theorem Ctx.LB_le_H0_aux (hc : Ctx M Q Z B) : LB M Q B ≤ H0 M Z := fun t ht =>
  ⟨hc.LB_le_M ht, Subgroup.mem_centralizer_iff.mpr fun z hz => by
    have := hc.LB_centralizes_Z ht z hz
    calc z * t = (t * z * t⁻¹) * t := by rw [this]
      _ = t * z := by group⟩

private theorem Ctx.conj_LB_le_H0_aux (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) :
    conjSubgroup m (LB M Q B) ≤ H0 M Z := by
  rw [← hc.LB_conj hm]
  exact (hc.conj_of_mem hm).LB_le_H0_aux

private theorem Ctx.conj_LB_eq_of_le_sup (hc : Ctx M Q Z B) {a : G} (haM : a ∈ M)
    (hle : conjSubgroup a B ≤ Z ⊔ B) : conjSubgroup a (LB M Q B) = LB M Q B := by
  obtain ⟨p, hp, hpB⟩ := hc.exists_conj_of_le_ZB (hc.conj_of_mem haM) hle
  have hpL : p ∈ LB M Q B := Subgroup.mem_sup_left hp
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hp
  have hLp : conjSubgroup p (LB M Q B) = LB M Q B :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hpL)
  rw [← hc.LB_conj haM, ← hpB, hc.LB_conj hpM, hLp]

private theorem Ctx.Spure_conj_aux (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) :
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

private theorem Ctx.exists_conj_not_le_sup (hc : Ctx M Q Z B) :
    ∃ m ∈ M, ¬ conjSubgroup m B ≤ B ⊔ Z := by
  by_contra hcon
  push Not at hcon
  apply hc.not_commutative_genB
  have hle : (⨆ (m : G) (_ : m ∈ M), conjSubgroup m B) ≤ Q ⊓ QB B :=
    iSup₂_le fun m hm => (hcon m hm).trans (sup_comm B Z ▸ hc.ZB_le_inf)
  haveI : IsMulCommutative ↥(Q ⊓ QB B) := hc.inf_QB_elemAbelian.1
  exact fun x hx y hy => setLike_mul_comm (hle hx) (hle hy)

private theorem Ctx.conj_le_of_commute (hc : Ctx M Q Z B)
    (horth : ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) →
      conjSubgroup m B ≤ B ⊔ Z)
    {m₁ m₂ : G} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    (hcomm : ∀ x ∈ conjSubgroup m₂ B, ∀ y ∈ conjSubgroup m₁ B, x * y = y * x) :
    conjSubgroup m₂ B ≤ conjSubgroup m₁ B ⊔ Z := by
  have hm : m₁⁻¹ * m₂ ∈ M := M.mul_mem (M.inv_mem hm₁) hm₂
  have he : conjSubgroup m₁ (conjSubgroup (m₁⁻¹ * m₂) B) = conjSubgroup m₂ B := by
    rw [← conjSubgroup_mul, mul_inv_cancel_left]
  have h1 : conjSubgroup (m₁⁻¹ * m₂) B ≤ B ⊔ Z := by
    refine horth _ hm fun x hx y hy => ?_
    have hx' : m₁ * x * m₁⁻¹ ∈ conjSubgroup m₂ B := by
      rw [← he, mem_conjSubgroup]
      simpa [mul_assoc] using hx
    have hy' : m₁ * y * m₁⁻¹ ∈ conjSubgroup m₁ B := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hy
    have h2 := hcomm _ hx' _ hy'
    have h3 : m₁ * (x * y) * m₁⁻¹ = m₁ * (y * x) * m₁⁻¹ := by
      calc m₁ * (x * y) * m₁⁻¹ = (m₁ * x * m₁⁻¹) * (m₁ * y * m₁⁻¹) := by group
        _ = (m₁ * y * m₁⁻¹) * (m₁ * x * m₁⁻¹) := h2
        _ = m₁ * (y * x) * m₁⁻¹ := by group
    simpa using h3
  have h2 : conjSubgroup m₁ (conjSubgroup (m₁⁻¹ * m₂) B) ≤ conjSubgroup m₁ (B ⊔ Z) :=
    Subgroup.map_mono h1
  rwa [he, conjSubgroup_sup', hc.conj_Z_eq hm₁] at h2

section Glue

variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

private theorem img_le_of_le_sup_Z (h : GlobalModelData M Q Z γ M₀) {C D : Subgroup G}
    (hC : C ≤ Q) (hDC : D ≤ C ⊔ Z) : M₀.img D ≤ M₀.img C := by
  have hle : C ⊔ Z ≤ M₀.lift (M₀.img C) := by
    refine sup_le (fun u hu => ⟨hC hu, M₀.pi_mem_img hu (hC hu)⟩) (fun z hz => ?_)
    refine ⟨h.reg.V_le hz, ?_⟩
    rw [(M₀.π_ker z (h.reg.V_le hz)).mpr hz]
    exact AddSubgroup.zero_mem _
  rintro _ ⟨x, hxD, -, rfl⟩
  exact (hle (hDC hxD)).2

private theorem Ctx.sing_fixed_aux (hc : Ctx M Q Z B) (hw : Width Q Z 3)
    (hno : NoA2 Q Z (LB M Q B)) (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hLB : LB M Q B ≤ H0 M Z) (v : M₀.E)
    (hv : ∀ t ∈ (φ.comp (Subgroup.inclusion hLB)).range, t v = v) (hv0 : M₀.Qf v = 0) :
    ∃ s : K, v = s • b := by
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj v
  have hxC : x ∈ CQt Q Z (LB M Q B) := by
    refine ⟨hxQ, fun t ht => ?_⟩
    have htQ := (hc.conj_mem_Q_of_mem_M (hc.LB_le_M ht)).1 x hxQ
    refine (M₀.comm_mem_iff hxQ htQ).mpr ?_
    have h1 : M₀.π (t * x * t⁻¹) = φ (Subgroup.inclusion hLB ⟨t, ht⟩) (M₀.π x) :=
      hφπ (Subgroup.inclusion hLB ⟨t, ht⟩) x hxQ
    rw [h1]
    exact hv _ ⟨⟨t, ht⟩, rfl⟩
  have hx2 : x ^ 2 = 1 := (M₀.sq_iff_Qf h.reg hxQ).mpr hv0
  have hxBZ : x ∈ (B ⊔ Z : Subgroup G) := by
    by_contra hnot
    exact hc.no_involution_CQt hw (by norm_num) hno ⟨x, hxC, hnot, hx2⟩
  exact (hB _).mp (img_le_of_le_sup_Z h hc.le le_rfl (M₀.pi_mem_img hxBZ hxQ))

private theorem Ctx.mem_range_of_Spure (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {b : M₀.E} (hb0 : b ≠ 0) (hbs : M₀.Qf b = 0)
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {t : G} (ht : t ∈ hc.Spure) {T : M₀.E ≃ₗ[K] M₀.E}
    (hT : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) (hTiso : ∀ e, M₀.Qf (T e) = M₀.Qf e)
    (hT1 : T ≠ 1) : T b = b ∧ b ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) := by
  obtain ⟨hTb, hr⟩ := hc.Spure_act h hB hcent ht hT
  refine ⟨hTb, mem_range_of_eichler (T := (T : M₀.E →ₗ[K] M₀.E)) hTiso hb0 hbs hr ?_⟩
  by_contra hcon
  push Not at hcon
  exact hT1 (LinearEquiv.ext hcon)

private theorem Ctx.conj_LB_eq_of_fix_line (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {a : G} (haM : a ∈ M) {T : M₀.E →ₗ[K] M₀.E}
    (hT : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x)) {μ : K} (hTb : T b = μ • b) :
    conjSubgroup a (LB M Q B) = LB M Q B := by
  refine hc.conj_LB_eq_of_le_sup haM fun y hy => ?_
  obtain ⟨u, hu, rfl⟩ : ∃ u ∈ B, a * u * a⁻¹ = y :=
    ⟨a⁻¹ * y * a, mem_conjSubgroup.mp hy, by group⟩
  have huQ : u ∈ Q := hc.le hu
  have hyQ : a * u * a⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M haM).1 u huQ
  obtain ⟨s, hs⟩ := (hB _).mp (M₀.pi_mem_img hu huQ)
  have hπ : M₀.π (a * u * a⁻¹) ∈ M₀.img B := by
    rw [hT u huQ, hs, map_smul, hTb, smul_smul]
    exact (hB _).mpr ⟨_, rfl⟩
  exact (M₀.mem_img_iff le_sup_left hyQ).mp (M₀.img_mono le_sup_right hπ)

private theorem Ctx.conj_mem_range_LB (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hLB : LB M Q B ≤ H0 M Z) (a : H0 M Z)
    (hmap : Submodule.map (φ a : M₀.E →ₗ[K] M₀.E) (Submodule.span K {b}) = Submodule.span K {b})
    {t : M₀.E ≃ₗ[K] M₀.E} (ht : t ∈ (φ.comp (Subgroup.inclusion hLB)).range) :
    φ a * t * (φ a)⁻¹ ∈ (φ.comp (Subgroup.inclusion hLB)).range := by
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ • b = φ a b := by
    have := Submodule.mem_map_of_mem (f := (φ a : M₀.E →ₗ[K] M₀.E))
      (Submodule.mem_span_singleton_self b)
    rw [hmap] at this
    exact Submodule.mem_span_singleton.mp this
  have haM : (a : G) ∈ M := (a.2 : (a : G) ∈ M ⊓ _).1
  have hLa := hc.conj_LB_eq_of_fix_line h hB haM (T := (φ a : M₀.E →ₗ[K] M₀.E)) (hφπ a)
    hμ.symm
  obtain ⟨x, rfl⟩ := ht
  have hmem : (a : G) * (x : G) * (a : G)⁻¹ ∈ LB M Q B := by
    have h1 : (a : G) * (x : G) * (a : G)⁻¹ ∈ conjSubgroup (a : G) (LB M Q B) := by
      rw [mem_conjSubgroup,
        show (a : G)⁻¹ * ((a : G) * (x : G) * (a : G)⁻¹) * (a : G) = x by group]
      exact x.2
    rwa [hLa] at h1
  refine ⟨⟨_, hmem⟩, ?_⟩
  show φ (Subgroup.inclusion hLB ⟨_, hmem⟩) = φ a * φ (Subgroup.inclusion hLB x) * (φ a)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

private theorem Ctx.card_range_LB (hc : Ctx M Q Z B) (hw : Width Q Z 3)
    (hno : NoA2 Q Z (LB M Q B)) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)} (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    (hLB : LB M Q B ≤ H0 M Z) :
    Nat.card (φ.comp (Subgroup.inclusion hLB)).range = Nat.card K ^ 2 := by
  have hkerΦ : (φ.comp (Subgroup.inclusion hLB)).ker = Q.subgroupOf (LB M Q B) := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφker (Subgroup.inclusion hLB s)
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hcard : Nat.card (LB M Q B) =
      Nat.card Q * Nat.card (φ.comp (Subgroup.inclusion hLB)).range := by
    have h1 : Nat.card (φ.comp (Subgroup.inclusion hLB)).ker = Nat.card Q := by
      rw [hkerΦ]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
    rw [← h1, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have h33 := (hc.card_of_3_3 hw (by norm_num) hno (stroth_3_3 hc hw (by norm_num))).1
  rw [h33] at hcard
  rw [h.card]
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard).symm

private theorem Ctx.exists_tsing_aux (hc : Ctx M Q Z B) (hw : Width Q Z 3)
    (hno : NoA2 Q Z (LB M Q B)) (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) :
    ∃ W : Submodule K M₀.E, (∀ u ∈ W, M₀.Qf u = 0) ∧ Module.finrank K W = 3 ∧ b ∈ W := by
  have hK : 1 < Nat.card K := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  have hXQ : Q ⊓ QB B ≤ Q := inf_le_left
  have hZX : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hUs : ∀ e ∈ M₀.img (Q ⊓ QB B), M₀.Qf e = 0 :=
    (M₀.isElemAbelian_iff h.reg hXQ).mp hc.inf_QB_elemAbelian
  have hcard33 := (hc.card_of_3_3 hw (by norm_num) hno (stroth_3_3 hc hw (by norm_num))).2
  have hcardU : Nat.card (M₀.img (Q ⊓ QB B)) = Nat.card K ^ 3 := by
    have h1 := M₀.card_eq hXQ hZX
    rw [h.card]
    have h2 : Nat.card Z * Nat.card (M₀.img (Q ⊓ QB B)) = Nat.card Z * Nat.card Z ^ 3 := by
      rw [← h1, hcard33]
      ring
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
  obtain ⟨W, hWU, -⟩ := exists_submodule_of_card_eq M₀ (w := 3) (h.finrank_E hw hK) hUs hcardU
  refine ⟨W, fun u hu => hUs u ((hWU u).mp hu), ?_, (hWU b).mpr (M₀.img_mono
    (le_sup_right.trans hc.ZB_le_inf) ((hB b).mpr ⟨1, (one_smul _ b).symm⟩))⟩
  have h1 : Nat.card W = Nat.card (M₀.img (Q ⊓ QB B)) :=
    Nat.card_congr (Equiv.subtypeEquivRight hWU)
  have h2 : Nat.card W = Nat.card K ^ Module.finrank K W := Module.natCard_eq_pow_finrank
  rw [hcardU, h2] at h1
  exact Nat.pow_right_injective hK h1

private theorem Ctx.exists_moves_aux (hc : Ctx M Q Z B) (hw : Width Q Z 3)
    (hno : NoA2 Q Z (LB M Q B)) (hS : hc.Spure = LB M Q B)
    (horth : ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) →
      conjSubgroup m B ≤ B ⊔ Z)
    (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    (hφiso : ∀ (m : H0 M Z) e, M₀.Qf (φ m e) = M₀.Qf e) :
    ∃ m ∈ M, ∃ x : H0 M Z, (x : G) ∈ conjSubgroup m (LB M Q B) ∧
      ¬ ∃ μ : K, φ x b = μ • b := by
  obtain ⟨m, hm, hmB⟩ := hc.exists_conj_not_le_sup
  have hc' := hc.conj_of_mem hm
  obtain ⟨b', hb'0, hb's, hB', hcent', -⟩ := hc'.dictB h
  have hnc : ¬ ∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x := fun h' => hmB (horth m hm h')
  rw [M₀.commute_iff h.reg hc'.le hc.le] at hnc
  push Not at hnc
  obtain ⟨e, he, f, hf, hef⟩ := hnc
  obtain ⟨s, rfl⟩ := (hB' e).mp he
  obtain ⟨s', rfl⟩ := (hB f).mp hf
  have hbb' : M₀.B b b' ≠ 0 := by
    intro h0
    apply hef
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Tim79.QuadModel.B_comm b' b, h0,
      neg_zero, mul_zero]
  obtain ⟨t₀, ht₀L, ht₀Q⟩ : ∃ t₀ ∈ LB M Q B, t₀ ∉ Q := by
    by_contra hcon
    push Not at hcon
    have h33 := (hc.card_of_3_3 hw (by norm_num) hno (stroth_3_3 hc hw (by norm_num))).1
    have hle := Subgroup.card_le_of_le (show LB M Q B ≤ Q from hcon)
    rw [h33] at hle
    have hZ := hc.hyp.q4
    have hQ : 0 < Nat.card Q := Nat.card_pos
    norm_num at hle
    nlinarith
  have htL : m * t₀ * m⁻¹ ∈ conjSubgroup m (LB M Q B) :=
    mem_conjSubgroup.mpr (by simpa [mul_assoc] using ht₀L)
  have htQ : m * t₀ * m⁻¹ ∉ Q := fun h' => ht₀Q (by
    simpa [mul_assoc] using (hc.conj_mem_Q_of_mem_M hm).2 _ h')
  have htS : m * t₀ * m⁻¹ ∈ hc'.Spure := by
    rw [hc.Spure_conj_aux hm, hS]
    exact htL
  have htH : m * t₀ * m⁻¹ ∈ H0 M Z := hc.conj_LB_le_H0_aux hm htL
  refine ⟨m, hm, ⟨_, htH⟩, htL, ?_⟩
  rintro ⟨μ, hμ⟩
  have hT1 : φ ⟨_, htH⟩ ≠ 1 := fun h1 => htQ ((hφker _).mp h1)
  obtain ⟨hTb', hb'R⟩ :=
    hc'.mem_range_of_Spure h hb'0 hb's hB' hcent' htS (hφπ ⟨_, htH⟩) (hφiso _) hT1
  exact not_smul_of_mem_range (T := (φ ⟨_, htH⟩ : M₀.E →ₗ[K] M₀.E)) (hφiso _) hbb' hTb' hb'R hμ

private theorem Ctx.orth_aux (hc : Ctx M Q Z B)
    (horth : ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) →
      conjSubgroup m B ≤ B ⊔ Z)
    (h : GlobalModelData M Q Z γ M₀) {p p' : M₀.E} {m₁ m₂ : G} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    (hp0 : p ≠ 0) (hp : p ∈ M₀.img (conjSubgroup m₁ B)) (hp' : p' ∈ M₀.img (conjSubgroup m₂ B))
    (hnp : ∀ c : K, p' ≠ c • p) : M₀.B p p' ≠ 0 := by
  intro h0
  have hc₁ := hc.conj_of_mem hm₁
  have hc₂ := hc.conj_of_mem hm₂
  obtain ⟨b₁, -, -, hB₁, -, -⟩ := hc₁.dictB h
  obtain ⟨b₂, -, -, hB₂, -, -⟩ := hc₂.dictB h
  obtain ⟨s₁, rfl⟩ := (hB₁ p).mp hp
  obtain ⟨s₂, rfl⟩ := (hB₂ p').mp hp'
  have hs₁ : s₁ ≠ 0 := fun h' => hp0 (by rw [h', zero_smul])
  have hs₂ : s₂ ≠ 0 := fun h' => hnp 0 (by rw [h', zero_smul, zero_smul])
  have h12 : M₀.B b₁ b₂ = 0 := by
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, hs₁, hs₂, false_or]
      using h0
  have hcomm : ∀ x ∈ conjSubgroup m₂ B, ∀ y ∈ conjSubgroup m₁ B, x * y = y * x := by
    rw [M₀.commute_iff h.reg hc₂.le hc₁.le]
    intro e he f hf
    obtain ⟨t₂, rfl⟩ := (hB₂ e).mp he
    obtain ⟨t₁, rfl⟩ := (hB₁ f).mp hf
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Tim79.QuadModel.B_comm b₂ b₁, h12,
      neg_zero, mul_zero]
  have hle := img_le_of_le_sup_Z h hc₁.le (hc.conj_le_of_commute horth hm₁ hm₂ hcomm)
  obtain ⟨r, hr⟩ := (hB₁ _).mp (hle hp')
  exact hnp (r * s₁⁻¹) (by rw [hr, smul_smul, mul_assoc, inv_mul_cancel₀ hs₁, mul_one])

private theorem Ctx.conj_mem_img_aux (hc : Ctx M Q Z B) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (a : H0 M Z) {m : G} {p : M₀.E} (hp : p ∈ M₀.img (conjSubgroup m B)) :
    φ a p ∈ M₀.img (conjSubgroup ((a : G) * m) B) := by
  obtain ⟨x, hxB, hxQ, rfl⟩ := hp
  have haM : (a : G) ∈ M := (a.2 : (a : G) ∈ M ⊓ _).1
  rw [← hφπ a x hxQ]
  refine M₀.pi_mem_img ?_ ((hc.conj_mem_Q_of_mem_M haM).1 x hxQ)
  rw [conjSubgroup_mul, mem_conjSubgroup,
    show (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * (a : G) = x by group]
  exact hxB

private theorem Ctx.span_aux (hc : Ctx M Q Z B) (hgen : GenByB M Q B)
    (h : GlobalModelData M Q Z γ M₀) :
    Submodule.span K {p : M₀.E | p ≠ 0 ∧ ∃ m ∈ M, p ∈ M₀.img (conjSubgroup m B)} = ⊤ := by
  set P := {p : M₀.E | p ≠ 0 ∧ ∃ m ∈ M, p ∈ M₀.img (conjSubgroup m B)}
  have hle : (⨆ (m : G) (_ : m ∈ M), conjSubgroup m B) ≤
      M₀.lift (Submodule.span K P).toAddSubgroup := by
    refine iSup₂_le fun m hm y hy => ?_
    have hyQ : y ∈ Q := (hc.conj_of_mem hm).le hy
    refine ⟨hyQ, ?_⟩
    by_cases hy0 : M₀.π y = 0
    · rw [hy0]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨hy0, m, hm, M₀.pi_mem_img hy hyQ⟩
  refine eq_top_iff.mpr fun e _ => ?_
  obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
  have hgen' : Q = ⨆ (m : G) (_ : m ∈ M), conjSubgroup m B := hgen
  have hx' : x ∈ ⨆ (m : G) (_ : m ∈ M), conjSubgroup m B := by
    rw [← hgen']
    exact hx
  exact (hle hx').2

end Glue

theorem stroth34_caseA_false (hHKS : HKSStatement) (hSL2 : SL2ModuleDimStatement)
    (hc : Ctx M Q Z B) (hw : Width Q Z 3) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hS : hc.Spure = LB M Q B)
    (horth : ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) →
      conjSubgroup m B ≤ B ⊔ Z) : False := by
  obtain ⟨k, γ, M₀, hkZ, h⟩ := stroth_globalModelDataGF hc.hyp
  have hk : 2 ≤ k := by
    by_contra hlt
    have h4 := hc.hyp.q4
    rw [hkZ] at h4
    interval_cases k <;> simp at h4
  have hK : 1 < Nat.card (GaloisField 2 k) := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  have hdim : Module.finrank (GaloisField 2 k) M₀.E = 6 := by rw [h.finrank_E hw hK]
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  have hLB : LB M Q B ≤ H0 M Z := hc.LB_le_H0_aux
  set X : Set (M₀.E ≃ₗ[GaloisField 2 k] M₀.E) :=
    {T | ∃ m ∈ M, ∃ x : H0 M Z, (x : G) ∈ conjSubgroup m (LB M Q B) ∧ φ x = T}
  have hXr : Subgroup.closure X ≤ φ.range :=
    (Subgroup.closure_le _).mpr fun T ⟨_, _, x, _, hT⟩ => ⟨x, hT⟩
  have hHQ : ∀ T ∈ Subgroup.closure X, ∀ e, M₀.Qf (T e) = M₀.Qf e := by
    intro T hT e
    obtain ⟨x, rfl⟩ := hXr hT
    exact hφiso x e
  have hXsq : ∀ T ∈ X, T * T = 1 := by
    rintro _ ⟨m, hm, x, hx, rfl⟩
    rw [← map_mul]
    refine (hφker _).mpr ?_
    have hx' : (x : G) ∈ LB M Q (conjSubgroup m B) := by
      rw [hc.LB_conj hm]
      exact hx
    have := (hc.conj_of_mem hm).sq_mem_Q_of_mem_LB hx'
    rw [pow_two] at this
    exact this
  set Λ := (φ.comp (Subgroup.inclusion hLB)).range
  have hΛH : Λ ≤ Subgroup.closure X := by
    rintro _ ⟨x, rfl⟩
    refine Subgroup.subset_closure ⟨1, M.one_mem, Subgroup.inclusion hLB x, ?_, rfl⟩
    rw [conjSubgroup_one]
    exact x.2
  have hΛcomm : ∀ t ∈ Λ, ∀ t' ∈ Λ, t * t' = t' * t := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have hxy : ⁅(x : G), (y : G)⁆ ∈ Q :=
      hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator x.2 y.2)
    have h1 : (φ.comp (Subgroup.inclusion hLB)) (x * y * x⁻¹ * y⁻¹) = 1 :=
      (hφker (Subgroup.inclusion hLB (x * y * x⁻¹ * y⁻¹))).mpr
        (by simpa [commutatorElement_def] using hxy)
    rw [← map_mul, ← map_mul]
    have e : x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    rw [e, map_mul, h1, one_mul]
  have hΛsq : ∀ t ∈ Λ, t * t = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    refine (hφker (Subgroup.inclusion hLB (x * x))).mpr ?_
    have := hc.sq_mem_Q_of_mem_LB x.2
    rw [pow_two] at this
    exact this
  have hΛb : ∀ t ∈ Λ, t b = b := by
    rintro _ ⟨x, rfl⟩
    have hxS : (x : G) ∈ hc.Spure := by
      rw [hS]
      exact x.2
    exact (hc.Spure_act h hB hcent hxS (hφπ (Subgroup.inclusion hLB x))).1
  have hΛE : ∀ t ∈ Λ, t ≠ 1 →
      b ∈ LinearMap.range ((t : M₀.E →ₗ[GaloisField 2 k] M₀.E) - 1) := by
    rintro _ ⟨x, rfl⟩ ht1
    have hxS : (x : G) ∈ hc.Spure := by
      rw [hS]
      exact x.2
    exact (hc.mem_range_of_Spure h hb0 hbs hB hcent hxS (hφπ (Subgroup.inclusion hLB x))
      (hφiso _) ht1).2
  have hΛnorm : ∀ T ∈ Subgroup.closure X,
      Submodule.map (T : M₀.E →ₗ[GaloisField 2 k] M₀.E) (Submodule.span (GaloisField 2 k) {b}) =
        Submodule.span (GaloisField 2 k) {b} → ∀ t ∈ Λ, T * t * T⁻¹ ∈ Λ := by
    intro T hT hmap t ht
    obtain ⟨a, rfl⟩ := hXr hT
    exact hc.conj_mem_range_LB h hB hφπ hLB a hmap ht
  have hmoves : ∃ T ∈ Subgroup.closure X,
      Submodule.map (T : M₀.E →ₗ[GaloisField 2 k] M₀.E) (Submodule.span (GaloisField 2 k) {b}) ≠
        Submodule.span (GaloisField 2 k) {b} := by
    obtain ⟨m, hm, x, hx, hnot⟩ := hc.exists_moves_aux hw hno hS horth h hB hφπ hφker hφiso
    refine ⟨φ x, Subgroup.subset_closure ⟨m, hm, x, hx, rfl⟩, fun hmap => hnot ?_⟩
    have := Submodule.mem_map_of_mem (f := (φ x : M₀.E →ₗ[GaloisField 2 k] M₀.E))
      (Submodule.mem_span_singleton_self b)
    rw [hmap] at this
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨μ, hμ.symm⟩
  obtain ⟨W, hWs, hWdim, hbW⟩ := hc.exists_tsing_aux hw hno h hB
  set P : Set M₀.E := {p | p ≠ 0 ∧ ∃ m ∈ M, p ∈ M₀.img (conjSubgroup m B)}
  have hbP : b ∈ P := ⟨hb0, 1, M.one_mem, by
    rw [conjSubgroup_one]
    exact (hB b).mpr ⟨1, (one_smul _ b).symm⟩⟩
  have hP0 : ∀ p ∈ P, p ≠ 0 ∧ M₀.Qf p = 0 := by
    rintro p ⟨hp0, m, hm, hp⟩
    have hc' := hc.conj_of_mem hm
    exact ⟨hp0, (M₀.isElemAbelian_iff h.reg hc'.le).mp hc'.isElemAbelian_B p hp⟩
  have hPsmul : ∀ p ∈ P, ∀ c : GaloisField 2 k, c ≠ 0 → c • p ∈ P := by
    rintro p ⟨hp0, m, hm, hp⟩ c hc0
    obtain ⟨b', -, -, hB', -, -⟩ := (hc.conj_of_mem hm).dictB h
    obtain ⟨s, rfl⟩ := (hB' _).mp hp
    exact ⟨smul_ne_zero hc0 hp0, m, hm, (hB' _).mpr ⟨c * s, by rw [smul_smul]⟩⟩
  have hPH : ∀ T ∈ Subgroup.closure X, ∀ p ∈ P, T p ∈ P := by
    intro T hT p hp
    obtain ⟨a, rfl⟩ := hXr hT
    obtain ⟨hp0, m, hm, hpm⟩ := hp
    exact ⟨(φ a).map_ne_zero_iff.mpr hp0, (a : G) * m,
      M.mul_mem (a.2 : (a : G) ∈ M ⊓ _).1 hm, hc.conj_mem_img_aux hφπ a hpm⟩
  have hPorth : ∀ p ∈ P, ∀ p' ∈ P, (∀ c : GaloisField 2 k, p' ≠ c • p) → M₀.B p p' ≠ 0 := by
    rintro p ⟨hp0, m₁, hm₁, hp⟩ p' ⟨-, m₂, hm₂, hp'⟩ hnp
    exact hc.orth_aux horth h hm₁ hm₂ hp0 hp hp' hnp
  exact stroth34_ovoid_false hHKS hSL2 hk M₀.E hdim M₀.B M₀.Qf M₀.Qf_smul M₀.Qf_add M₀.alt M₀.nondeg
    (Subgroup.closure X) hHQ (closure_hom_eq_one hXsq) b hb0 hbs W hWs hWdim hbW Λ hΛH
    (hc.card_range_LB hw hno h hφker hLB) hΛcomm hΛsq hΛb hΛE
    (hc.sing_fixed_aux hw hno h hB hφπ hLB) hΛnorm hmoves P hbP hP0 hPsmul hPH hPorth
    (hc.span_aux hgen h)

end CFSG.RankThree.GF2n.Stroth80
