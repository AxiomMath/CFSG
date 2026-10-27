module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec3Action
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.LB_le_H0 (hc : Ctx M Q Z B) : LB M Q B ≤ H0 M Z := fun l hl =>
  ⟨hc.LB_le_M hl, Subgroup.mem_centralizer_iff.mpr fun z hz => by
    have := hc.LB_centralizes_Z hl z hz
    calc z * l = (l * z * l⁻¹) * l := by rw [this]
      _ = l * z := by group⟩

theorem Ctx.LB_conj_le_Rt (hc : Ctx M Q Z B) {m t : G} (hm : m ∈ M)
    (htm : t ∈ conjSubgroup m (LB M Q B)) : LB M Q (conjSubgroup m B) ≤ Rt M (LB M Q B) t := by
  rw [hc.LB_conj hm]
  unfold Rt
  exact le_iSup₂_of_le m hm (le_iSup_of_le htm le_rfl)

theorem Ctx.Rt_le_H0 (hc : Ctx M Q Z B) (t : G) : Rt M (LB M Q B) t ≤ H0 M Z := by
  unfold Rt
  refine iSup₂_le fun m hm => iSup_le fun _ => ?_
  rw [← hc.LB_conj hm]
  exact (hc.conj_of_mem hm).LB_le_H0

theorem Ctx.isPGroup_range_LB (hc : Ctx M Q Z B) {E : Type*} [Group E] (φ : ↥(H0 M Z) →* E)
    (hφQ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) :
    IsPGroup 2 (φ.comp (Subgroup.inclusion hc.LB_le_H0)).range := by
  intro g
  obtain ⟨T', l, rfl⟩ := g
  refine ⟨1, Subtype.ext ?_⟩
  show ((φ.comp (Subgroup.inclusion hc.LB_le_H0)) l) ^ (2 ^ 1) = 1
  rw [← map_pow]
  exact (hφQ (Subgroup.inclusion hc.LB_le_H0 (l ^ (2 ^ 1)))).mpr (by
    simpa using hc.sq_mem_Q_of_mem_LB l.2)

theorem Ctx.actionHom_sq_eq_one (hc : Ctx M Q Z B) {E : Type*} [Group E] (φ : ↥(H0 M Z) →* E)
    (hφQ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) {t : G} (ht : t ∈ LB M Q B) :
    φ ⟨t, hc.LB_le_H0 ht⟩ ^ 2 = 1 := by
  rw [← map_pow, hφQ]
  simpa using hc.sq_mem_Q_of_mem_LB ht

section Model

variable {K : Type} [Field K] {γ : G → K}

omit [Finite G] in
@[expose] def imgSub (M₀ : Tim79.QuadModel Q Z K γ) (S : Subgroup G)
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img S → c • e ∈ M₀.img S) : Submodule K M₀.E where
  toAddSubmonoid := (M₀.img S).toAddSubmonoid
  smul_mem' c e he := hS c e he

omit [Finite G] in
theorem mem_imgSub {M₀ : Tim79.QuadModel Q Z K γ} {S : Subgroup G}
    {hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img S → c • e ∈ M₀.img S} {e : M₀.E} :
    e ∈ imgSub M₀ S hS ↔ e ∈ M₀.img S := Iff.rfl

omit [Finite G] in
theorem mem_img_Wt_iff (M₀ : Tim79.QuadModel Q Z K γ) (R : Tim79.GammaReg Q Z γ)
    {V : Subgroup G} (hVQ : V ≤ Q) {e : M₀.E} :
    e ∈ M₀.img (Wt Q V) ↔ ∀ v ∈ M₀.img V, M₀.B e v = 0 := by
  constructor
  · rintro ⟨x, hxW, hxQ, rfl⟩ _ ⟨y, hyV, hyQ, rfl⟩
    exact (M₀.comm_iff_B R hxQ hyQ).mp (Subgroup.mem_centralizer_iff.mp hxW.2 y hyV).symm
  · intro he
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    refine ⟨x, ⟨hxQ, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩, hxQ, rfl⟩
    refine (M₀.comm_iff_B R (hVQ hy) hxQ).mpr ?_
    rw [Tim79.QuadModel.B_comm, he _ (M₀.pi_mem_img hy (hVQ hy)), neg_zero]

omit [Finite G] in
theorem smul_mem_img_Wt (M₀ : Tim79.QuadModel Q Z K γ) (R : Tim79.GammaReg Q Z γ)
    {V : Subgroup G} (hVQ : V ≤ Q) (c : K) {e : M₀.E} (he : e ∈ M₀.img (Wt Q V)) :
    c • e ∈ M₀.img (Wt Q V) := by
  rw [mem_img_Wt_iff M₀ R hVQ] at he ⊢
  intro v hv
  rw [map_smul, LinearMap.smul_apply, he v hv, smul_zero]

omit [Finite G] in
theorem conj_mem_Wt {V : Subgroup G} {l x : G} (hlQ : l ∈ Subgroup.normalizer (Q : Set G))
    (hlV : l ∈ Subgroup.normalizer (V : Set G)) (hx : x ∈ Wt Q V) : l * x * l⁻¹ ∈ Wt Q V := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hlQ x).mp hx.1,
    Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  have hv' : l⁻¹ * v * l ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlV) v).mp hv
    simpa using this
  have hc1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hv'
  calc v * (l * x * l⁻¹) = l * ((l⁻¹ * v * l) * x) * l⁻¹ := by group
    _ = l * (x * (l⁻¹ * v * l)) * l⁻¹ := by rw [hc1]
    _ = l * x * l⁻¹ * v := by group

omit [Finite G] in
theorem Tt_le_Q {V : Subgroup G} {t : G} (hZQ : Z ≤ Q)
    (htQ : t ∈ Subgroup.normalizer (Q : Set G)) : Tt Q Z V t ≤ Q := by
  refine sup_le ?_ hZQ
  rw [Subgroup.commutator_le]
  intro w hw s hs
  have hsn : s ∈ Subgroup.normalizer (Q : Set G) := (Subgroup.zpowers_le.mpr htQ) hs
  have h1 : s * w⁻¹ * s⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hsn _).mp (Q.inv_mem hw.1)
  rw [show ⁅w, s⁆ = w * (s * w⁻¹ * s⁻¹) by rw [commutatorElement_def]; group]
  exact Q.mul_mem hw.1 h1

variable {M₀ : Tim79.QuadModel Q Z K γ}

theorem StrothHyp.comm_action (H : StrothHyp M Q Z) {a b : G} (ha : a ∈ M) (hb : b ∈ M)
    (hab : ⁅a, b⁆ ∈ Q) {Sa Sb : M₀.E → M₀.E}
    (hSa : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = Sa (M₀.π x))
    (hSb : ∀ x ∈ Q, M₀.π (b * x * b⁻¹) = Sb (M₀.π x)) (e : M₀.E) : Sa (Sb e) = Sb (Sa e) := by
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
  have hQn : ∀ {g : G}, g ∈ M → ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun {g} hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 hg) y).mp hy
  have hbx := hQn hb x hxQ
  have hax := hQn ha x hxQ
  rw [← hSb x hxQ, ← hSa _ hbx, ← hSa x hxQ, ← hSb _ hax]
  have e : a * (b * x * b⁻¹) * a⁻¹ = ⁅a, b⁆ * (b * (a * x * a⁻¹) * b⁻¹) * ⁅a, b⁆⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e, Tim79.QuadModel.pi_conj_self hab (hQn hb _ hax)]

theorem StrothHyp.mem_img_Tt_iff (H : StrothHyp M Q Z) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (V : Subgroup G) (t : H0 M Z) (hT2 : φ t ^ 2 = 1) {e : M₀.E} :
    e ∈ M₀.img (Tt Q Z V t) ↔ ∃ w ∈ M₀.img (Wt Q V), ((φ t : M₀.E →ₗ[K] M₀.E) - 1) w = e := by
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hQn : ∀ {g : G}, g ∈ M → ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := fun {g} hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 hg) x).mp hx
  have htM : (t : G) ∈ M := t.2.1
  have hTk : ∀ k : ℤ, φ t ^ k = 1 ∨ φ t ^ k = φ t := by
    intro k
    have h2 : φ t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hT2]
    rw [zpow_eq_zpow_emod k h2]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left; rw [hk, zpow_zero]
    · right; rw [hk, zpow_one]
  constructor
  · rintro ⟨x, hxT, -, rfl⟩
    let R : AddSubgroup M₀.E :=
      (M₀.img (Wt Q V)).map ((φ t : M₀.E →ₗ[K] M₀.E) - 1).toAddMonoidHom
    have hle : Tt Q Z V t ≤ M₀.lift R := by
      refine sup_le ?_ fun z hz => ⟨hZQ hz, by
        rw [(M₀.π_ker z (hZQ hz)).mpr hz]; exact R.zero_mem⟩
      rw [Subgroup.commutator_le]
      intro w hw s hs
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      have hwQ : w ∈ Q := hw.1
      have hsQ : (t : G) ^ k * w⁻¹ * ((t : G) ^ k)⁻¹ ∈ Q :=
        hQn (M.zpow_mem htM k) _ (Q.inv_mem hwQ)
      rw [show ⁅w, (t : G) ^ k⁆ = w * ((t : G) ^ k * w⁻¹ * ((t : G) ^ k)⁻¹) by
        rw [commutatorElement_def]; group]
      refine ⟨Q.mul_mem hwQ hsQ, ?_⟩
      have hπk : M₀.π ((t : G) ^ k * w⁻¹ * ((t : G) ^ k)⁻¹) = (φ t ^ k) (M₀.π w⁻¹) := by
        have := hφπ (t ^ k) w⁻¹ (Q.inv_mem hwQ)
        simp only [map_zpow, SubgroupClass.coe_zpow] at this
        exact this
      show M₀.π (w * ((t : G) ^ k * w⁻¹ * ((t : G) ^ k)⁻¹)) ∈ R
      rw [M₀.π_mul _ hwQ _ hsQ, hπk]
      rcases hTk k with hk | hk <;> rw [hk]
      · simp [M₀.pi_inv hwQ]
      · refine AddSubgroup.mem_map.mpr ⟨M₀.π w⁻¹,
          M₀.pi_mem_img (Subgroup.inv_mem _ hw) (Q.inv_mem hwQ), ?_⟩
        show ((φ t : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π w⁻¹) = _
        rw [M₀.pi_inv hwQ]
        simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_neg]
        abel
    exact AddSubgroup.mem_map.mp (hle hxT).2
  · rintro ⟨_, ⟨x, hxW, hxQ, rfl⟩, rfl⟩
    have htx : (t : G) * x⁻¹ * (t : G)⁻¹ ∈ Q := hQn htM _ (Q.inv_mem hxQ)
    have hcomm : ⁅x, (t : G)⁆ = x * ((t : G) * x⁻¹ * (t : G)⁻¹) := by
      rw [commutatorElement_def]; group
    have hmem : -(((φ t : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π x)) ∈ M₀.img (Tt Q Z V t) := by
      refine ⟨⁅x, (t : G)⁆, Subgroup.mem_sup_left
        (Subgroup.commutator_mem_commutator hxW (Subgroup.mem_zpowers _)),
        by rw [hcomm]; exact Q.mul_mem hxQ htx, ?_⟩
      rw [hcomm, M₀.π_mul _ hxQ _ htx, hφπ t x⁻¹ (Q.inv_mem hxQ), M₀.pi_inv hxQ, map_neg]
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]
      abel
    simpa using (M₀.img (Tt Q Z V t)).neg_mem hmem

theorem StrothHyp.smul_mem_img_Tt (H : StrothHyp M Q Z) (R : Tim79.GammaReg Q Z γ)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {V : Subgroup G} (hVQ : V ≤ Q) (t : H0 M Z) (hT2 : φ t ^ 2 = 1) (c : K) {e : M₀.E}
    (he : e ∈ M₀.img (Tt Q Z V t)) : c • e ∈ M₀.img (Tt Q Z V t) := by
  obtain ⟨w, hw, rfl⟩ := (H.mem_img_Tt_iff φ hφπ V t hT2).mp he
  exact (H.mem_img_Tt_iff φ hφπ V t hT2).mpr
    ⟨c • w, smul_mem_img_Wt M₀ R hVQ c hw, by rw [map_smul]⟩

theorem StrothHyp.mem_img_Tt_of_comm (H : StrothHyp M Q Z)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {V : Subgroup G} (t : H0 M Z) (hT2 : φ t ^ 2 = 1) {l : G} (hlM : l ∈ M)
    (hlV : l ∈ Subgroup.normalizer (V : Set G)) (hlt : ⁅l, (t : G)⁆ ∈ Q) (S : M₀.E →+ M₀.E)
    (hS : ∀ x ∈ Q, M₀.π (l * x * l⁻¹) = S (M₀.π x)) {e : M₀.E}
    (he : e ∈ M₀.img (Tt Q Z V t)) : S e ∈ M₀.img (Tt Q Z V t) := by
  obtain ⟨w, hw, rfl⟩ := (H.mem_img_Tt_iff φ hφπ V t hT2).mp he
  refine (H.mem_img_Tt_iff φ hφπ V t hT2).mpr ⟨S w, ?_, ?_⟩
  · obtain ⟨x, hxW, hxQ, rfl⟩ := hw
    rw [← hS x hxQ]
    exact M₀.pi_mem_img (conj_mem_Wt (H.Q_normal.2 hlM) hlV hxW)
      ((Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 hlM) x).mp hxQ)
  · have hc := H.comm_action hlM t.2.1 hlt hS (fun x hx => hφπ t x hx) w
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub]
    rw [hc]

end Model

theorem Ctx.img_Vt_le_of_invariant (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {K : Type} [Field K] [Finite K]
    [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    (t : G) (Sp : Submodule K M₀.E) (hSp0 : Sp ≠ ⊥)
    (hSp : ∀ l ∈ Rt M (LB M Q B) t, ∀ S : M₀.E ≃ₗ[K] M₀.E,
      (∀ x ∈ Q, M₀.π (l * x * l⁻¹) = S (M₀.π x)) → (∀ e, M₀.Qf (S e) = M₀.Qf e) →
        ∀ v ∈ Sp, S v ∈ Sp) :
    ∀ v ∈ M₀.img (Vt M (LB M Q B) B Z t), v ∈ Sp := by
  obtain ⟨φ, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hle : Vt M (LB M Q B) B Z t ≤ M₀.lift Sp.toAddSubgroup := by
    refine sec39_Vt_le (fun z hz => ⟨hZQ hz, by
      rw [(M₀.π_ker z (hZQ hz)).mpr hz]; exact AddSubgroup.zero_mem _⟩) fun m hm htm => ?_
    have hcC : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
    have hLCR := hc.LB_conj_le_Rt hm htm
    have hLCH := hcC.LB_le_H0
    let Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E) := (φ.comp (Subgroup.inclusion hLCH)).range
    have hΛS : ∀ g ∈ Λ, ∀ v ∈ Sp, g v ∈ Sp := by
      rintro _ ⟨l, rfl⟩ v hv
      exact hSp l (hLCR l.2) (φ (Subgroup.inclusion hLCH l)) (hφπ (Subgroup.inclusion hLCH l))
        (hφiso _) v hv
    obtain ⟨f, hfS, hf0, hfix⟩ :=
      exists_fixed_vector_of_isPGroup Λ (hcC.isPGroup_range_LB φ hφQ) Sp hΛS hSp0
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj f
    have hxC : x ∈ CQt Q Z (LB M Q (conjSubgroup m B)) := by
      refine ⟨hxQ, fun l hl => ?_⟩
      have hmem : φ (Subgroup.inclusion hLCH ⟨l, hl⟩) ∈ Λ := ⟨⟨l, hl⟩, rfl⟩
      have h1 := hfix _ hmem
      rw [← hφπ _ x hxQ] at h1
      exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ
        ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hcC.LB_le_M hl)) x).mp hxQ)).mpr h1
    rw [hc.CQt_conj hm h35] at hxC
    obtain ⟨b, -, -, hB, -, -⟩ := hcC.dictB h
    have hle' : conjSubgroup m B ⊔ Z ≤ M₀.lift (M₀.img (conjSubgroup m B)) := sup_le
      (fun u hu => ⟨hcC.le hu, M₀.pi_mem_img hu (hcC.le hu)⟩)
      (fun z hz => ⟨hZQ hz, by
        rw [(M₀.π_ker z (hZQ hz)).mpr hz]; exact AddSubgroup.zero_mem _⟩)
    obtain ⟨s, hs⟩ := (hB _).mp (hle' hxC).2
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hf0 (by rw [hs, zero_smul])
    have hbS : b ∈ Sp := by
      have := Sp.smul_mem s⁻¹ hfS
      rwa [hs, smul_smul, inv_mul_cancel₀ hs0, one_smul] at this
    intro c hcm
    have hcQ : c ∈ Q := hcC.le hcm
    obtain ⟨s', hs'⟩ := (hB _).mp (M₀.pi_mem_img hcm hcQ)
    refine ⟨hcQ, ?_⟩
    show M₀.π c ∈ Sp
    rw [hs']
    exact Sp.smul_mem s' hbS
  rintro _ ⟨x, hxV, -, rfl⟩
  exact (hle hxV).2

theorem Ctx.Tt_le_Z_or_Vt_le_Tt (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {t : G} (ht : t ∈ LB M Q B) :
    Tt Q Z (Vt M (LB M Q B) B Z t) t ≤ Z ∨
      Vt M (LB M Q B) B Z t ≤ Tt Q Z (Vt M (LB M Q B) B Z t) t := by
  set V := Vt M (LB M Q B) B Z t
  by_cases hTZ : Tt Q Z V t ≤ Z
  · exact Or.inl hTZ
  right
  obtain ⟨n, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφQ, -⟩ := exists_actionHom_H0 hc.hyp h
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hZT : Z ≤ Tt Q Z V t := le_sup_right
  have hTQ : Tt Q Z V t ≤ Q := Tt_le_Q hc.Z_le_Q (hc.hyp.Q_normal.2 (hc.LB_le_M ht))
  have htH := hc.LB_le_H0 ht
  have hT2 := hc.actionHom_sq_eq_one φ hφQ ht
  let Sp : Submodule (GaloisField 2 n) M₀.E := imgSub M₀ (Tt Q Z V t)
    (fun c _ he => hc.hyp.smul_mem_img_Tt h.reg φ hφπ hVQ ⟨t, htH⟩ hT2 c he)
  have hSp0 : Sp ≠ ⊥ := by
    obtain ⟨x, hxT, hxZ⟩ := SetLike.not_le_iff_exists.mp hTZ
    intro hbot
    have h0 : M₀.π x ∈ Sp := mem_imgSub.mpr (M₀.pi_mem_img hxT (hTQ hxT))
    rw [hbot, Submodule.mem_bot] at h0
    exact hxZ ((M₀.π_ker x (hTQ hxT)).mp h0)
  have hinv := hc.img_Vt_le_of_invariant h35 h t Sp hSp0 fun l hl S hS _ v hv =>
    mem_imgSub.mpr (hc.hyp.mem_img_Tt_of_comm φ hφπ ⟨t, htH⟩ hT2 (hc.Rt_le_M t hl)
      (hc.Rt_normalizes_Vt ht hl) (hc.Rt_comm_mem_Q hl) S.toAddMonoidHom hS (mem_imgSub.mp hv))
  intro x hxV
  exact (M₀.mem_img_iff hZT (hVQ hxV)).mp (mem_imgSub.mp (hinv _ (M₀.pi_mem_img hxV (hVQ hxV))))

end CFSG.RankThree.GF2n.Stroth80
