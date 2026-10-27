module

public import CFSG.RankThree.PartOne.Q1327.Defs
public import CFSG.RankThree.PartOne.K1327.Assemble

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.K1327 CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 100000

theorem psl_two_deg_unique {X : Type} [Group X] {f g : ℕ}
    (h1 : StatedClassicalModel X .PSL 2 2 f) (h2 : StatedClassicalModel X .PSL 2 2 g) : f = g :=
  CFSG.RankThree.PartOne.K1320.psl_two_degree_eq h1 h2

variable {G : Type} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem kfAt_deg_unique {E : Subgroup G} {t : MulAut E} {f g : ℕ} (h1 : KFAt p E f t)
    (h2 : KFAt p E g t) : f = g :=
  psl_two_deg_unique h1.2.1 h2.2.1

omit [Finite G] in
theorem kfAt_not_two_mul {E : Subgroup G} {t : MulAut E} {f : ℕ} (h1 : KFAt p E f t)
    (h2 : KFAt p E (2 * f) t) : False := by
  have h3 := kfAt_deg_unique h1 h2
  have h4 : 1 ≤ f := h1.2.1.1.2.1
  omega

theorem d8_invols : ∀ a b x : DihedralGroup 4, a * a = 1 → b * b = 1 → (a * b) ^ 4 = 1 →
    (a * b) ^ 2 ≠ 1 → x * x = 1 → x ≠ 1 →
    x = a ∨ x = b ∨ x = b * a * b⁻¹ ∨ x = a * b * a⁻¹ ∨ x = (a * b) ^ 2 := by decide

theorem d8_class : ∀ a b y : DihedralGroup 4, a * a = 1 → b * b = 1 → (a * b) ^ 4 = 1 →
    (a * b) ^ 2 ≠ 1 → y * a * y⁻¹ ≠ a → y * a * y⁻¹ = b * a * b⁻¹ := by decide

theorem d8_central : ∀ a b g : DihedralGroup 4, a * a = 1 → b * b = 1 → (a * b) ^ 4 = 1 →
    (a * b) ^ 2 ≠ 1 → g * (a * b) ^ 2 = (a * b) ^ 2 * g := by decide

section Identify

variable {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem type_f_eq (fr : Row8Frame p A L E f K) (h : Sec12Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E) (hZ : Subgroup.center L = ⊥)
    (hcard : Nat.card E = p ^ 3) (eL : ↥(torusImage E L) ≃* DihedralGroup 4) {t : MulAut E}
    (ht : t ∈ reflectionSet p E) (htL : t ∈ torusImage E L) (hKt : KFAt p E f t) :
    t = fr.r₀ ∨ t = fr.r₀' := by
  have hp := h.prime
  set a : DihedralGroup 4 := eL ⟨fr.r₀, fr.mem₀L⟩ with ha
  set b : DihedralGroup 4 := eL ⟨fr.r₁, fr.mem₁L⟩ with hb
  set x : DihedralGroup 4 := eL ⟨t, htL⟩ with hx
  have hr02 : fr.r₀ * fr.r₀ = 1 := RefFacts.mul_self_eq_one fr.mem₀.1
  have hr12 : fr.r₁ * fr.r₁ = 1 := RefFacts.mul_self_eq_one fr.mem₁.1
  have ht2 : t * t = 1 := RefFacts.mul_self_eq_one ht.1
  have hmul : ∀ (u v : MulAut E) (hu : u ∈ torusImage E L) (hv : v ∈ torusImage E L),
      eL ⟨u, hu⟩ * eL ⟨v, hv⟩ = eL ⟨u * v, (torusImage E L).mul_mem hu hv⟩ := fun u v hu hv => by
    rw [← map_mul]; rfl
  have hinv : ∀ (u : MulAut E) (hu : u ∈ torusImage E L),
      (eL ⟨u, hu⟩)⁻¹ = eL ⟨u⁻¹, (torusImage E L).inv_mem hu⟩ := fun u hu => by
    rw [← map_inv]; rfl
  have hone : eL (1 : ↥(torusImage E L)) = 1 := map_one _
  have ha2 : a * a = 1 := by
    rw [ha, hmul, ← hone]
    congr 1
    exact Subtype.ext hr02
  have hb2 : b * b = 1 := by
    rw [hb, hmul, ← hone]
    congr 1
    exact Subtype.ext hr12
  have hab4 : orderOf (a * b) = 4 := by
    have : a * b = eL (⟨fr.r₀, fr.mem₀L⟩ * ⟨fr.r₁, fr.mem₁L⟩) := by rw [map_mul]
    rw [this, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact fr.ord₀₁
  have hab4' : (a * b) ^ 4 = 1 := by
    have := pow_orderOf_eq_one (a * b)
    rwa [hab4] at this
  have hab2 : (a * b) ^ 2 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hab4] at this
    omega
  have hx2 : x * x = 1 := by
    rw [hx, hmul, ← hone]
    congr 1
    exact Subtype.ext ht2
  have hx1 : x ≠ 1 := by
    intro h1
    have h3 : (⟨t, htL⟩ : ↥(torusImage E L)) = 1 := eL.injective (h1.trans hone.symm)
    have h4 : t = 1 := congrArg Subtype.val h3
    have h5 := ht.1.1
    rw [h4, orderOf_one] at h5
    omega
  have hxL : ∀ (u : MulAut E) (hu : u ∈ torusImage E L), eL ⟨u, hu⟩ = x → u = t := fun u hu hux =>
    congrArg Subtype.val (eL.injective hux)
  obtain ⟨w₀, hw₀L, hw₀N, hw₀⟩ := Sec12Three.mem_torusImage_iff.1 fr.mem₀L
  have hw₀' : conjAut E w₀ hw₀N = fr.r₀ := hw₀
  rcases d8_invols a b x ha2 hb2 hab4' hab2 hx2 hx1 with h1 | h1 | h1 | h1 | h1
  · left
    exact (hxL _ _ h1.symm).symm
  · exfalso
    have : t = fr.r₁ := (hxL _ _ h1.symm).symm
    rw [this] at hKt
    exact kfAt_not_two_mul hKt fr.kf₁
  · right
    have hxL' : (fr.r₁ * fr.r₀ * fr.r₁⁻¹) ∈ torusImage E L :=
      (torusImage E L).mul_mem ((torusImage E L).mul_mem fr.mem₁L fr.mem₀L)
        ((torusImage E L).inv_mem fr.mem₁L)
    have hxe : eL ⟨fr.r₁ * fr.r₀ * fr.r₁⁻¹, hxL'⟩ = b * a * b⁻¹ := by
      rw [ha, hb, hinv, hmul, hmul]
    have htr : t = fr.r₁ * fr.r₀ * fr.r₁⁻¹ := (hxL _ _ (hxe.trans h1.symm)).symm
    have hxw : conjAut E fr.w fr.wE ∈ torusImage E L :=
      Sec12Three.mem_torusImage_iff.2 ⟨fr.w, fr.wL, fr.wE, rfl⟩
    set y : DihedralGroup 4 := eL ⟨conjAut E fr.w fr.wE, hxw⟩ with hy
    have hr0' : eL ⟨fr.r₀', fr.mem₀'L⟩ = y * a * y⁻¹ := by
      rw [ha, hy, hinv, hmul, hmul]
      congr 1
      apply Subtype.ext
      simpa using fr.hw
    have hne : y * a * y⁻¹ ≠ a := by
      intro h2
      apply fr.r₀_ne h hF13 hZ
      have := eL.injective (h2.symm.trans hr0'.symm)
      exact congrArg Subtype.val this
    have h3 := d8_class a b y ha2 hb2 hab4' hab2 hne
    have h4 : eL ⟨fr.r₀', fr.mem₀'L⟩ = eL ⟨fr.r₁ * fr.r₀ * fr.r₁⁻¹, hxL'⟩ := by
      rw [hr0', h3, hxe]
    have h5 := congrArg Subtype.val (eL.injective h4)
    exact htr.trans h5.symm
  · exfalso
    have hxL' : (fr.r₀ * fr.r₁ * fr.r₀⁻¹) ∈ torusImage E L :=
      (torusImage E L).mul_mem ((torusImage E L).mul_mem fr.mem₀L fr.mem₁L)
        ((torusImage E L).inv_mem fr.mem₀L)
    have hxe : eL ⟨fr.r₀ * fr.r₁ * fr.r₀⁻¹, hxL'⟩ = a * b * a⁻¹ := by
      rw [ha, hb, hinv, hmul, hmul]
    have htr : t = fr.r₀ * fr.r₁ * fr.r₀⁻¹ := (hxL _ _ (hxe.trans h1.symm)).symm
    have hkf : KFAt p E (2 * f) (conjAut E w₀ hw₀N * fr.r₁ * (conjAut E w₀ hw₀N)⁻¹) :=
      fr.kf₁.conj hw₀N
    rw [hw₀'] at hkf
    rw [htr] at hKt
    exact kfAt_not_two_mul hKt hkf
  · exfalso
    have hu : (fr.r₀ * fr.r₁) ^ 2 ∈ torusImage E L :=
      (torusImage E L).pow_mem ((torusImage E L).mul_mem fr.mem₀L fr.mem₁L) 2
    have hxe : eL ⟨(fr.r₀ * fr.r₁) ^ 2, hu⟩ = (a * b) ^ 2 := by
      have : (a * b) ^ 2 = eL ((⟨fr.r₀, fr.mem₀L⟩ * ⟨fr.r₁, fr.mem₁L⟩ : ↥(torusImage E L)) ^ 2) := by
        rw [map_pow, map_mul]
      rw [this]
      rfl
    have htu : t = (fr.r₀ * fr.r₁) ^ 2 := (hxL _ _ (hxe.trans h1.symm)).symm
    have hcen : ∀ g ∈ torusImage E L, g * t = t * g := by
      intro g hg
      have h6 : eL ⟨g, hg⟩ * x = x * eL ⟨g, hg⟩ := by
        rw [h1]
        exact d8_central a b _ ha2 hb2 hab4' hab2
      have h7 : eL (⟨g, hg⟩ * ⟨t, htL⟩) = eL (⟨t, htL⟩ * ⟨g, hg⟩) := by
        rw [map_mul, map_mul]
        exact h6
      exact congrArg Subtype.val (eL.injective h7)
    have h8 := fixS_u h hF hcard hZ htL ht2 (fun h1 => hx1 (by
      rw [hx]; simp [h1])) hcen
    have h9 := ht.1.2
    rw [h8.2] at h9
    have hp1 := hp.one_lt
    nlinarith [h9]

end Identify

section Transfer

variable {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem ident_ss {r : ℕ} {R : Subgroup G} {s s' zs : MulAut E} (fr : Row8Frame p A L E f K)
    (H : Hyp G p A c L E f r R s s' zs) (hZ : Subgroup.center L = ⊥) (hcard : Nat.card E = p ^ 3)
    (eL : ↥(torusImage E L) ≃* DihedralGroup 4) :
    (s = fr.r₀ ∧ s' = fr.r₀') ∨ (s = fr.r₀' ∧ s' = fr.r₀) := by
  have h1 := type_f_eq fr H.h12 H.hF H.hF13 hZ hcard eL H.hs H.hsL H.hKs
  have h2 := type_f_eq fr H.h12 H.hF H.hF13 hZ hcard eL H.hs' H.hs'L H.hKs'
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact absurd rfl H.hss'
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl H.hss'

theorem R_eq_lft (fr : Row8Frame p A L E f K) (h : Sec12Hyp G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hZ : Subgroup.center L = ⊥) {r : ℕ} (hr : r.Prime)
    (hrq : r ∣ Nat.card K - 1) {R : Subgroup G} (hRcard : Nat.card R = r) (hRL : R ≤ L)
    (hR0 : R ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G))
    (hR0' : R ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G)) : R = fr.lft (Rr K r) := by
  set R' : Subgroup (StatedProj (StatedSL 4 K)) := (R.subgroupOf L).map fr.ε with hR'
  set S : Subgroup ↥(M8 K) := R'.comap (q8 K) with hS
  have hSmap : S.map (q8 K) = R' := Subgroup.map_comap_eq_self_of_surjective q8_surj R'
  have hRS : R = fr.lft S := by
    show R = pullG fr.ε (S.map (q8 K))
    rw [hSmap]
    exact eq_pullG_of_map (fr.inj hZ) hRL rfl
  have hK0 : kZero p E fr.r₀ = fr.lft (slB K 0 1) := fr.kz₀ h hF13 hZ
  have hK0' : kZero p E fr.r₀' = fr.lft (slB K 2 3) := fr.kz₀' h hF13 hZ
  have hLtop : fr.lft ⊤ = L := liftM_top q8_surj
  have hA : R ≤ fr.lft ⊤ ⊓ Subgroup.centralizer (fr.lft (slB K 0 1) : Set G) :=
    le_inf (by rw [hLtop]; exact hRL) (by rw [← hK0]; exact hR0)
  rw [fr.lft_cent hZ] at hA
  have hB : R ≤ fr.lft (⊤ ⊓ Subgroup.centralizer (slB K 0 1 : Set ↥(M8 K))) ⊓
      Subgroup.centralizer (fr.lft (slB K 2 3) : Set G) := le_inf hA (by rw [← hK0']; exact hR0')
  rw [fr.lft_cent hZ] at hB
  have hSle : S ≤ (⊤ ⊓ Subgroup.centralizer (slB K 0 1 : Set ↥(M8 K))) ⊓
      Subgroup.centralizer (slB K 2 3 : Set ↥(M8 K)) :=
    (fr.lft_le_iff).1 (by rw [← hRS]; exact hB)
  have hSR : S ≤ (Tl K).range := by
    intro x hx
    have h1 := hSle hx
    have h2 : x ∈ Subgroup.centralizer ((slB K 0 1 ⊔ slB K 2 3 : Subgroup ↥(M8 K)) :
        Set ↥(M8 K)) := mem_centralizer_sup.2 ⟨h1.1.2, h1.2⟩
    rwa [centralizer_slB_blocks] at h2
  have hcardS : Nat.card S = r := by
    rw [← fr.lft_card hZ S, ← hRS]
    exact hRcard
  have hSeq := eq_Rr_of_card hr hrq S hSR hcardS
  rw [hRS, hSeq]

theorem core_of_hyp (fr : Row8Frame p A L E f K) {r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}
    (H : Hyp G p A c L E f r R s s' zs) (Bd : Bridge p E) (hcard : Nat.card E = p ^ 3)
    (hRid : R = fr.lft (Rr K r)) (hss : (s = fr.r₀ ∧ s' = fr.r₀') ∨ (s = fr.r₀' ∧ s' = fr.r₀)) :
    fr.Core c r zs := by
  subst hRid
  have hL₀ := fr.mem₀L
  have hL₁ := fr.mem₁L
  have hmem : ∀ x ∈ torusImage E L, zs ≠ x := fun x hx h1 => H.hzL (h1 ▸ hx)
  have hcls := Bd.zstar_class H.h12 hcard fr.mem₀ fr.mem₁ H.hzs fr.ord₀₁ (H.hzc _ hL₀)
    (H.hzc _ hL₁) (hmem _ hL₀) (hmem _ hL₁)
    (hmem _ ((torusImage E L).mul_mem ((torusImage E L).mul_mem hL₀ hL₁)
      ((torusImage E L).inv_mem hL₀)))
    (hmem _ ((torusImage E L).mul_mem ((torusImage E L).mul_mem hL₁ hL₀)
      ((torusImage E L).inv_mem hL₁)))
  have hconj : ∃ g ∈ reflectionGroup p E, g * fr.r₁ * g⁻¹ = zs := by
    rcases hcls with ⟨g, hgX, hg⟩ | h2
    · exfalso
      obtain ⟨y, hy, hyg⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hgX)
      have hkf : KFAt p E f zs := by
        rw [← hg, ← hyg]
        exact fr.kf₀.conj hy
      exact kfAt_not_two_mul hkf H.hKz
    · exact h2
  have hcent : kZero p E zs ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G) ∧
      kZero p E zs ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G) := by
    rcases hss with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]
      exact ⟨H.hzs_s, H.hzs_s'⟩
    · rw [← h1, ← h2]
      exact ⟨H.hzs_s', H.hzs_s⟩
  exact ⟨H.hzs, H.hzc, H.hzL, H.hmov, hconj, H.hKz, hcent.1, hcent.2, H.hRz, H.hRnorm⟩

end Transfer

section ThetaCommute

variable {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem theta_commute (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) {r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}
    (H : Hyp G p A c L E f r R s s' zs) : ∀ v ∈ Vof p (Jof p R), Commute v c := by
  have h := H.h12
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcard : Nat.card E = p ^ 3 := by rw [H.hEA]; exact h.A_card
  have hcE : c ∈ E := h.A_le_E h.c_mem
  obtain ⟨eX⟩ := H.hweyl
  obtain ⟨z, hz⟩ := exists_inverter h H.hF13 eX
  obtain ⟨Bd⟩ := exists_bridge h H.hF13 hcard eX
  obtain ⟨hZ, -, K, _, _, _, ⟨fr⟩⟩ :=
    row8Frame_of hGA h H.hF H.hF13 H.hEA (by have := H.hf2; omega) H.hpf H.hmodel
  obtain ⟨eL⟩ := exists_eL h H.hF hcard hz H.hf2 H.hmodel
  have hrq : r ∣ Nat.card K - 1 := by rw [fr.hK]; exact H.hrf
  have hss := ident_ss fr H hZ hcard eL
  have hR0 : R ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G) ∧
      R ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G) := by
    rcases hss with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]
      exact ⟨H.hRs, H.hRs'⟩
    · rw [← h1, ← h2]
      exact ⟨H.hRs', H.hRs⟩
  have hRid : R = fr.lft (Rr K r) :=
    R_eq_lft fr h H.hF13 hZ H.hr hrq H.hRcard H.hRL hR0.1 hR0.2
  have hcore : fr.Core c r zs := core_of_hyp fr H Bd hcard hRid hss
  have hRE := H.hRE
  have hR0a := hR0.1
  have hR0b := hR0.2
  subst hRid
  set R := fr.lft (Rr K r) with hRdef
  set J := Jof p R with hJdef
  have hEM : ∀ e ∈ E, e ∈ Subgroup.centralizer (R : Set G) := fun e he => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hRE x hx e he
  have hEJ : ∀ e ∈ E, e ∈ J := fun e he =>
    mem_Jof_of_pow hp (hEM e he) (Sec12Three.pow_eq_one_of_mem_E h he)
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  have hdat := RefFacts.ElemData.of_isElementaryAbelian hp hp2 hE
  have hBcard : Nat.card (autFixedInG E zs) = p ^ 2 := by
    have h1 := RefFacts.card_eq_inf_fixed_mul hdat hcore.mem.1 (B := ⊤) le_top
    rw [Subgroup.card_top, top_inf_eq, hcard] at h1
    have h2 : Nat.card ↥(autFixed E zs) = p ^ 2 := by
      have : Nat.card ↥(autFixed E zs) * p = p ^ 2 * p := by rw [← h1]; ring
      exact Nat.eq_of_mul_eq_mul_right hp.pos this
    show Nat.card ↥((autFixed E zs).map E.subtype) = p ^ 2
    rw [Subgroup.card_map_of_injective E.subtype_injective, h2]
  have hBE : autFixedInG E zs ≤ E := Subgroup.map_subtype_le _
  have hB : IsElemAbelian p (autFixedInG E zs) :=
    ⟨(isElementaryAbelian_of_le' hE hBE).toIsMulCommutative, fun x hx =>
      Sec12Three.pow_eq_one_of_mem_E h (hBE hx)⟩
  have hBV : autFixedInG E zs ≤ Subgroup.normalizer (Vof p J : Set G) := fun b hb =>
    le_normalizer_Vof p J (hEJ b (hBE hb))
  have hVsc := Vof_solvable_coprime hp J
  have hcomm : ∀ b ∈ autFixedInG E zs, b ≠ 1 →
      ∀ u ∈ Vof p J ⊓ Subgroup.centralizer ({b} : Set G), Commute u c := by
    intro b hb hb1 u hu
    exact line_commute hS hRe hTwo hFull h H.hF H.hF13 H.hT H.hEA H.hpf hz Bd fr hZ H.hr hrq
      hcore hR0a hR0b hRE hb hb1 hu.1 (Subgroup.mem_centralizer_singleton_iff.1 hu.2)
  exact commute_of_commute_centralizers hp hB hBcard hBV hVsc.2 hcomm

end ThetaCommute

section RefData

variable {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem refData (hGA : CFSG.Open.GriessAllModelsStatement)
    {r : ℕ} {R : Subgroup G} {s s' zs : MulAut E} (H : Hyp G p A c L E f r R s s' zs) :
    ∃ a a' b g₀ : MulAut E, a ∈ reflectionSet p E ∧ a' ∈ reflectionSet p E ∧ b ∈ reflectionSet p E ∧
      a ∈ torusImage E L ∧ a' ∈ torusImage E L ∧ b ∈ torusImage E L ∧
      ((s = a ∧ s' = a') ∨ (s = a' ∧ s' = a)) ∧ a * a' = a' * a ∧ a ≠ a' ∧
      orderOf (a * b) = 4 ∧ (∃ g ∈ reflectionGroup p E, g * a * g⁻¹ = a') ∧
      (∀ g ∈ torusImage E L, g * (a * a') = (a * a') * g) ∧
      autFixedInG E (a * a') = Subgroup.zpowers c ∧
      (∀ g ∈ torusImage E L, ∀ hcE : c ∈ E, g ⟨c, hcE⟩ = ⟨c, hcE⟩) ∧
      g₀ ∈ reflectionGroup p E ∧ g₀ * b * g₀⁻¹ = zs ∧
      zs ≠ a ∧ zs ≠ b ∧ zs ≠ a * b * a⁻¹ ∧ zs ≠ b * a * b⁻¹ := by
  have h := H.h12
  have hp := h.prime
  have hcard : Nat.card E = p ^ 3 := by rw [H.hEA]; exact h.A_card
  have hcE : c ∈ E := h.A_le_E h.c_mem
  obtain ⟨eX⟩ := H.hweyl
  obtain ⟨z, hz⟩ := exists_inverter h H.hF13 eX
  obtain ⟨Bd⟩ := exists_bridge h H.hF13 hcard eX
  obtain ⟨hZ, -, K, _, _, _, ⟨fr⟩⟩ :=
    row8Frame_of hGA h H.hF H.hF13 H.hEA (by have := H.hf2; omega) H.hpf H.hmodel
  obtain ⟨eL⟩ := exists_eL h H.hF hcard hz H.hf2 H.hmodel
  have hrq : r ∣ Nat.card K - 1 := by rw [fr.hK]; exact H.hrf
  have hss := ident_ss fr H hZ hcard eL
  have hR0 : R ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G) ∧
      R ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G) := by
    rcases hss with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]
      exact ⟨H.hRs, H.hRs'⟩
    · rw [← h1, ← h2]
      exact ⟨H.hRs', H.hRs⟩
  have hRid : R = fr.lft (Rr K r) :=
    R_eq_lft fr h H.hF13 hZ H.hr hrq H.hRcard H.hRL hR0.1 hR0.2
  have hcore : fr.Core c r zs := core_of_hyp fr H Bd hcard hRid hss
  obtain ⟨hcomm₀, hu2, hu1, hucen⟩ := fr.u_data h H.hF13 hZ eL
  have huL : fr.r₀ * fr.r₀' ∈ torusImage E L := (torusImage E L).mul_mem fr.mem₀L fr.mem₀'L
  obtain ⟨hfixu, -⟩ := fixS_u h H.hF hcard hZ huL hu2 hu1 hucen
  obtain ⟨g₀, hg₀X, hg₀⟩ := hcore.conj
  have hL₀ := fr.mem₀L
  have hL₁ := fr.mem₁L
  refine ⟨fr.r₀, fr.r₀', fr.r₁, g₀, fr.mem₀, fr.mem₀', fr.mem₁, hL₀, fr.mem₀'L, hL₁, hss, hcomm₀,
    fr.r₀_ne h H.hF13 hZ, fr.ord₀₁, ?_, hucen, hfixu,
    fun g hg hcE => apply_c_of_mem_torusImage' h hcE hg, hg₀X, hg₀,
    fun h1 => hcore.notL (h1 ▸ hL₀), fun h1 => hcore.notL (h1 ▸ hL₁),
    fun h1 => hcore.notL (h1 ▸ (torusImage E L).mul_mem ((torusImage E L).mul_mem hL₀ hL₁)
      ((torusImage E L).inv_mem hL₀)),
    fun h1 => hcore.notL (h1 ▸ (torusImage E L).mul_mem ((torusImage E L).mul_mem hL₁ hL₀)
      ((torusImage E L).inv_mem hL₁))⟩
  have hxw : conjAut E fr.w fr.wE ∈ torusImage E L :=
    Sec12Three.mem_torusImage_iff.2 ⟨fr.w, fr.wL, fr.wE, rfl⟩
  exact ⟨conjAut E fr.w fr.wE, torusImage_le_reflectionGroup H.hF hxw, fr.hw.symm⟩

end RefData

end CFSG.RankThree.PartOne.Q1327
