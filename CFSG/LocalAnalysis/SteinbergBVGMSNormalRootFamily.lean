module

public import CFSG.LocalAnalysis.SteinbergBTGMSNormalRootSinger

public section

namespace CFSG.LocalAnalysis.SteinbergBV

open Subgroup CFSG CFSG.LocalAnalysis
open scoped Pointwise

variable {D : Type*} [Group D]

theorem mem_map_conj_iff {S : Subgroup D} {g x : D} :
    x ∈ S.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩

theorem map_conj_mul (S : Subgroup D) (g h : D) :
    S.map (MulAut.conj (g * h)).toMonoidHom =
      (S.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map, map_mul]
  rfl

theorem map_conj_one (S : Subgroup D) : S.map (MulAut.conj (1 : D)).toMonoidHom = S := by
  rw [map_one]
  exact Subgroup.map_id S

theorem map_conj_inv_map_conj (S : Subgroup D) (g : D) :
    (S.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = S := by
  rw [← map_conj_mul, inv_mul_cancel, map_conj_one]

theorem map_conj_le_map_conj_iff {S T : Subgroup D} (g : D) :
    S.map (MulAut.conj g).toMonoidHom ≤ T.map (MulAut.conj g).toMonoidHom ↔ S ≤ T :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

theorem map_conj_eq_self_iff {S : Subgroup D} {g : D} :
    S.map (MulAut.conj g).toMonoidHom = S ↔ g ∈ normalizer (S : Set D) := by
  rw [mem_normalizer_iff]
  constructor
  · intro h x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h, mem_map_conj_iff] at hx
      simpa [mul_assoc] using hx
  · intro h
    ext x
    rw [mem_map_conj_iff]
    constructor
    · intro hx
      have := (h (g⁻¹ * x * g)).1 hx
      simpa [mul_assoc] using this
    · intro hx
      exact (h _).2 (by simpa [mul_assoc] using hx)

theorem card_map_conj (S : Subgroup D) (g : D) :
    Nat.card (S.map (MulAut.conj g).toMonoidHom) = Nat.card S :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem le_normalizer_of_le_of_comm {Q W : Subgroup D} (hQW : Q ≤ W)
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) : W ≤ normalizer (Q : Set D) := by
  intro w hw
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hW w hw x (hQW hx), mul_inv_cancel_right]
    exact hx
  · intro hx
    have hx' : x = w⁻¹ * (w * x * w⁻¹) * w := by group
    rw [hx', hW w⁻¹ (inv_mem hw) _ (hQW hx), inv_mul_cancel_right]
    exact hx

theorem eq_of_sylow_le {p : ℕ} {G U W : Subgroup D} (T : Sylow p G)
    (hT : (T : Subgroup G) = U.subgroupOf G) (hUG : U ≤ G) (hWG : W ≤ G) (hUW : U ≤ W)
    (hWp : IsPGroup p W) : W = U := by
  have hWp' : IsPGroup p (W.subgroupOf G) := hWp.of_equiv (subgroupOfEquivOfLe hWG).symm
  have hle : (T : Subgroup G) ≤ W.subgroupOf G := by
    rw [hT]
    intro x hx
    exact hUW hx
  have h := T.is_maximal' hWp' hle
  rw [hT] at h
  have h' := Subgroup.subgroupOf_inj.1 h
  rwa [inf_of_le_left hWG, inf_of_le_left hUG] at h'

section Data

variable {J R X U P : Subgroup D} {n : ℕ}

theorem gms_R_le_centralizer_U (h : GMSNormalRootData J R X U P n) :
    R ≤ centralizer (U : Set D) := by
  obtain ⟨-, -, -, ⟨-, -, hXC⟩, ⟨-, hUX, -, -⟩, -⟩ := h
  exact le_centralizer_iff.1 (hUX.trans hXC)

theorem gms_isElementaryAbelian_V (h : GMSNormalRootData J R X U P n) :
    IsElementaryAbelian 2 ↥(U ⊔ R) := by
  have hRU := gms_R_le_centralizer_U h
  obtain ⟨-, -, ⟨hRel, -, -⟩, -, ⟨hUel, -, -, -⟩, -⟩ := h
  exact SteinbergBT.isElementaryAbelian_sup_of_centralizes hUel hRel hRU

theorem gms_comm_V (h : GMSNormalRootData J R X U P n) :
    ∀ a ∈ U ⊔ R, ∀ b ∈ U ⊔ R, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val
    ((gms_isElementaryAbelian_V h).toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem gms_isPGroup_V (h : GMSNormalRootData J R X U P n) :
    IsPGroup 2 ↥(U ⊔ R) := by
  have := gms_isElementaryAbelian_V h
  exact IsElementaryAbelian.isPGroup 2 _

theorem gms_sq_V (h : GMSNormalRootData J R X U P n) :
    ∀ v ∈ U ⊔ R, v ^ 2 = 1 := fun v hv => by
  have := gms_isElementaryAbelian_V h
  exact elemPow_eq_one_of_isElementaryAbelian v hv

theorem gms_isPGroup_P (h : GMSNormalRootData J R X U P n) : IsPGroup 2 P := by
  obtain ⟨-, -, -, -, -, -, ⟨hPN, ⟨TP, hTP⟩, -⟩⟩ := h
  have h1 : IsPGroup 2 (P.subgroupOf (normalizer (R : Set D))) := hTP ▸ TP.isPGroup'
  exact h1.of_equiv (subgroupOfEquivOfLe hPN)

theorem gms_R_mem : R ∈ gmsRootConjugates (U ⊔ R) R :=
  ⟨1, by rw [inv_one, map_conj_one], le_sup_right⟩

theorem gms_card_of_mem {W Q : Subgroup D} (hQ : Q ∈ gmsRootConjugates W R) :
    Nat.card Q = Nat.card R := by
  obtain ⟨g, rfl, -⟩ := hQ
  exact card_map_conj R g⁻¹

theorem gms_inf_eq_bot [Finite D] (h : GMSNormalRootData J R X U P n) {Q Z : Subgroup D}
    (hQ : Q ∈ gmsRootConjugates (U ⊔ R) R) (hZ : Z ∈ gmsRootConjugates (U ⊔ R) R)
    (hQZ : Q ≠ Z) : Q ⊓ Z = ⊥ := by
  have hsq := gms_sq_V h
  have hV2 := gms_isPGroup_V h
  obtain ⟨-, ⟨-, htight⟩, ⟨-, hRJ, T, hT⟩, -⟩ := h
  obtain ⟨a, rfl, hQV⟩ := hQ
  obtain ⟨b, rfl, hZV⟩ := hZ
  by_contra hne
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hw1' : w ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
  obtain ⟨hwQ, hwZ⟩ := mem_inf.1 hw
  have hwR : a * w * a⁻¹ ∈ R := by
    have := mem_map_conj_iff.1 hwQ
    rwa [inv_inv] at this
  have hwR' : b * w * b⁻¹ ∈ R := by
    have := mem_map_conj_iff.1 hwZ
    rwa [inv_inv] at this
  set y := a * w * a⁻¹ with hy
  have hyJ : y ∈ J := hRJ hwR
  have hyJ' : y ∈ J.map (MulAut.conj (b * a⁻¹)⁻¹).toMonoidHom := by
    rw [mem_map_conj_iff, inv_inv]
    have : b * a⁻¹ * y * (b * a⁻¹)⁻¹ = b * w * b⁻¹ := by
      rw [hy]
      group
    rw [this]
    exact hRJ hwR'
  have hy2 : orderOf y = 2 := by
    apply orderOf_eq_prime
    · have h2 := hsq w (hQV hwQ)
      calc y ^ 2 = a * w ^ 2 * a⁻¹ := by rw [hy, sq, sq]; group
        _ = 1 := by rw [h2]; group
    · intro h1
      apply hw1'
      have : w = a⁻¹ * y * a := by rw [hy]; group
      rw [this, h1]
      group
  have heven : ¬Odd (Nat.card ↥(J ⊓ J.map (MulAut.conj (b * a⁻¹)⁻¹).toMonoidHom)) := by
    rw [Nat.not_odd_iff_even, even_iff_two_dvd]
    have hdvd := Subgroup.orderOf_dvd_natCard (J ⊓ J.map (MulAut.conj (b * a⁻¹)⁻¹).toMonoidHom)
      (mem_inf.2 ⟨hyJ, hyJ'⟩)
    rwa [hy2] at hdvd
  have hN : b * a⁻¹ ∈ normalizer (J : Set D) := by
    by_contra hnot
    exact heven (htight _ hnot)
  have hJeq : J.map (MulAut.conj (a * b⁻¹)).toMonoidHom = J := by
    rw [map_conj_eq_self_iff]
    have : a * b⁻¹ = (b * a⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hN
  set R' := R.map (MulAut.conj (a * b⁻¹)).toMonoidHom with hR'
  have hR'J : R' ≤ J := by
    rw [hR', ← hJeq]
    exact (map_conj_le_map_conj_iff _).2 hRJ
  have hRV : R ≤ (U ⊔ R).map (MulAut.conj a).toMonoidHom := by
    have := (map_conj_le_map_conj_iff a).2 hQV
    rwa [← map_conj_mul, mul_inv_cancel, map_conj_one] at this
  have hR'V : R' ≤ (U ⊔ R).map (MulAut.conj a).toMonoidHom := by
    have := (map_conj_le_map_conj_iff a).2 hZV
    rwa [← map_conj_mul] at this
  have hW2 : IsPGroup 2 ↥(R ⊔ R') :=
    (hV2.map (MulAut.conj a).toMonoidHom).to_le (sup_le hRV hR'V)
  have hW := eq_of_sylow_le T hT hRJ (sup_le hRJ hR'J) le_sup_left hW2
  have hR'R : R' = R := by
    apply Subgroup.eq_of_le_of_card_ge (hW ▸ le_sup_right)
    rw [hR', card_map_conj]
  apply hQZ
  have e : a⁻¹ * (a * b⁻¹) = b⁻¹ := by group
  rw [← e, map_conj_mul, ← hR', hR'R]

theorem gms_exists_to_R [Finite D] (h : GMSNormalRootData J R X U P n) {Q : Subgroup D}
    (hQ : Q ∈ gmsRootConjugates (U ⊔ R) R) :
    ∃ x ∈ normalizer ((U ⊔ R : Subgroup D) : Set D), Q.map (MulAut.conj x).toMonoidHom = R := by
  have hweak := (SteinbergBT.gms_normal_root_singer_action_and_weak_closure h).2.2.2.2.2.2.1
  have hcomm := gms_comm_V h
  have hV2 := gms_isPGroup_V h
  obtain ⟨-, -, -, -, -, -, ⟨-, ⟨TP, hTP⟩, -⟩⟩ := h
  obtain ⟨g, rfl, hQV⟩ := hQ
  have hRV' : R ≤ (U ⊔ R).map (MulAut.conj g).toMonoidHom := by
    have := (map_conj_le_map_conj_iff g).2 hQV
    rwa [← map_conj_mul, mul_inv_cancel, map_conj_one] at this
  have hV'comm : ∀ a ∈ (U ⊔ R).map (MulAut.conj g).toMonoidHom,
      ∀ b ∈ (U ⊔ R).map (MulAut.conj g).toMonoidHom, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group, hcomm a ha b hb]
    group
  have hV'N : (U ⊔ R).map (MulAut.conj g).toMonoidHom ≤ normalizer (R : Set D) :=
    le_normalizer_of_le_of_comm hRV' hV'comm
  have hV'2 : IsPGroup 2 (((U ⊔ R).map (MulAut.conj g).toMonoidHom).subgroupOf
      (normalizer (R : Set D))) :=
    (hV2.map _).of_equiv (subgroupOfEquivOfLe hV'N).symm
  obtain ⟨T', hT'⟩ := hV'2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (normalizer (R : Set D)) T' TP
  refine ⟨(c : D) * g, ?_, ?_⟩
  · have hle : CFSG.conjugate (U ⊔ R) ((c : D) * g)⁻¹ ≤ P := by
      intro y hy
      rw [CFSG.conjugate, inv_inv] at hy
      obtain ⟨v, hv, rfl⟩ := hy
      have hgv : g * v * g⁻¹ ∈ (U ⊔ R).map (MulAut.conj g).toMonoidHom := ⟨v, hv, rfl⟩
      have hmem : (⟨g * v * g⁻¹, hV'N hgv⟩ : normalizer (R : Set D)) ∈ (T' : Subgroup _) :=
        hT' hgv
      have hmem' : MulAut.conj c • (⟨g * v * g⁻¹, hV'N hgv⟩ : normalizer (R : Set D)) ∈
          ((c • T' : Sylow 2 _) : Subgroup _) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ hmem
      rw [hc, hTP, mem_subgroupOf] at hmem'
      have e : ((MulAut.conj c • (⟨g * v * g⁻¹, hV'N hgv⟩ : normalizer (R : Set D)) :
          normalizer (R : Set D)) : D) = (c : D) * g * v * ((c : D) * g)⁻¹ := by
        rw [MulAut.smul_def, MulAut.conj_apply]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e] at hmem'
      have e' : (MulAut.conj ((c : D) * g)).toMonoidHom v = (c : D) * g * v * ((c : D) * g)⁻¹ := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [e']
      exact hmem'
    have := hweak _ hle
    rw [CFSG.conjugate, inv_inv] at this
    exact map_conj_eq_self_iff.1 this
  · rw [← map_conj_mul, show (c : D) * g * g⁻¹ = c by group]
    exact map_conj_eq_self_iff.2 c.2

theorem gms_isPretransitive [Finite D] (h : GMSNormalRootData J R X U P n) :
    MulAction.IsPretransitive (normalizer ((U ⊔ R : Subgroup D) : Set D))
      (gmsRootConjugates (U ⊔ R) R) := by
  refine ⟨fun Q Z => ?_⟩
  obtain ⟨x, hx, hxQ⟩ := gms_exists_to_R h Q.2
  obtain ⟨y, hy, hyZ⟩ := gms_exists_to_R h Z.2
  refine ⟨⟨y⁻¹ * x, mul_mem (inv_mem hy) hx⟩, Subtype.ext ?_⟩
  change Q.1.map (MulAut.conj (y⁻¹ * x)).toMonoidHom = Z.1
  rw [map_conj_mul, hxQ]
  calc R.map (MulAut.conj y⁻¹).toMonoidHom =
      (Z.1.map (MulAut.conj y).toMonoidHom).map (MulAut.conj y⁻¹).toMonoidHom := by rw [hyZ]
    _ = Z.1 := map_conj_inv_map_conj _ _

end Data

section Rho

theorem gms_rho_apply (V : Subgroup D) (l : normalizer (V : Set D)) (v : V) :
    ((V.normalizerMonoidHom l v : V) : D) = l * v * (l : D)⁻¹ :=
  rfl

theorem gms_map_rho {V S : Subgroup D} (hSV : S ≤ V) (l : normalizer (V : Set D)) :
    ((S.subgroupOf V).map (V.normalizerMonoidHom l).toMonoidHom).map V.subtype =
      S.map (MulAut.conj (l : D)).toMonoidHom := by
  rw [Subgroup.map_map]
  have e : V.subtype.comp (V.normalizerMonoidHom l).toMonoidHom =
      (MulAut.conj (l : D)).toMonoidHom.comp V.subtype := by
    ext v
    rfl
  rw [e, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hSV]

theorem gms_rho_smul_eq_iff {V S : Subgroup D} (hSV : S ≤ V) (l : normalizer (V : Set D)) :
    V.normalizerMonoidHom l • S.subgroupOf V = S.subgroupOf V ↔
      (l : D) ∈ normalizer (S : Set D) := by
  rw [← map_conj_eq_self_iff, ← gms_map_rho hSV l]
  constructor
  · intro h
    change (S.subgroupOf V).map (V.normalizerMonoidHom l).toMonoidHom = S.subgroupOf V at h
    rw [h, Subgroup.map_subgroupOf_eq_of_le hSV]
  · intro h
    change (S.subgroupOf V).map (V.normalizerMonoidHom l).toMonoidHom = S.subgroupOf V
    apply Subgroup.map_injective V.subtype_injective
    rw [h, Subgroup.map_subgroupOf_eq_of_le hSV]

@[expose] def gmsRootStabilizer (V R : Subgroup D) : Subgroup (MulAut V) :=
  V.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut V) (R.subgroupOf V)

@[expose] def gmsSingerImage (X U V : Subgroup D) : Subgroup (MulAut V) :=
  ((X ⊓ normalizer (U : Set D)).subgroupOf (normalizer (V : Set D))).map V.normalizerMonoidHom

@[expose] def gmsRootKernel (V R : Subgroup D) : Subgroup (normalizer (V : Set D)) :=
  ⨅ Q : gmsRootConjugates V R,
    (normalizer ((Q : Subgroup D) : Set D)).subgroupOf (normalizer (V : Set D))

theorem comap_gmsRootStabilizer {V R : Subgroup D} (hRV : R ≤ V) :
    (gmsRootStabilizer V R).comap V.normalizerMonoidHom =
      (normalizer (R : Set D)).subgroupOf (normalizer (V : Set D)) := by
  ext l
  rw [Subgroup.mem_comap, gmsRootStabilizer, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    mem_subgroupOf, gms_rho_smul_eq_iff hRV]
  exact ⟨fun h => h.2, fun h => ⟨⟨l, rfl⟩, h⟩⟩

end Rho

section Linear

variable {J R X U P : Subgroup D} {n : ℕ}

theorem mem_normalizer_of_conj_mem {S : Subgroup D} {l : D} (h1 : ∀ x ∈ S, l * x * l⁻¹ ∈ S)
    (h2 : ∀ x ∈ S, l⁻¹ * x * l ∈ S) : l ∈ normalizer (S : Set D) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [show l⁻¹ * (l * x * l⁻¹) * l = x by group] at this

theorem gms_inf_X [Finite D] (h : GMSNormalRootData J R X U P n) : (U ⊔ R) ⊓ X = U := by
  have hV2 := gms_isPGroup_V h
  obtain ⟨-, -, -, -, ⟨-, hUX, ⟨TU, hTU⟩, -⟩, -⟩ := h
  exact eq_of_sylow_le TU hTU hUX inf_le_right (le_inf le_sup_left hUX) (hV2.to_le inf_le_left)

theorem gms_NXU_le_L [Finite D] (h : GMSNormalRootData J R X U P n) :
    X ⊓ normalizer (U : Set D) ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) :=
  (SteinbergBT.gms_normal_root_singer_action_and_weak_closure h).2.2.2.2.2.2.2.2.2.1

theorem gms_NXU_inf_CV [Finite D] (h : GMSNormalRootData J R X U P n) :
    X ⊓ normalizer (U : Set D) ⊓ centralizer ((U ⊔ R : Subgroup D) : Set D) =
      X ⊓ centralizer (U : Set D) :=
  (SteinbergBT.gms_normal_root_singer_action_and_weak_closure h).2.2.2.2.2.2.2.2.2.2

theorem gms_LR_normalizes [Finite D] (h : GMSNormalRootData J R X U P n) {l : D}
    (hlV : l ∈ normalizer ((U ⊔ R : Subgroup D) : Set D)) (hlR : l ∈ normalizer (R : Set D)) :
    l ∈ normalizer (X : Set D) ∧ l ∈ normalizer (U : Set D) ∧
      l ∈ normalizer ((X ⊓ normalizer (U : Set D) : Subgroup D) : Set D) ∧
      l ∈ normalizer ((X ⊓ centralizer (U : Set D) : Subgroup D) : Set D) := by
  have hVX := gms_inf_X h
  obtain ⟨-, -, -, ⟨hXN, hXnormal, -⟩, ⟨-, hUX, -, -⟩, -⟩ := h
  have hconjX : ∀ m ∈ normalizer (R : Set D), ∀ x ∈ X, m * x * m⁻¹ ∈ X := by
    intro m hm x hx
    have := hXnormal.conj_mem ⟨x, hXN hx⟩ hx ⟨m, hm⟩
    exact this
  have hlX : l ∈ normalizer (X : Set D) :=
    mem_normalizer_of_conj_mem (hconjX l hlR) fun x hx => by
      have := hconjX l⁻¹ (inv_mem hlR) x hx
      rwa [inv_inv] at this
  have hconjU : ∀ m ∈ normalizer ((U ⊔ R : Subgroup D) : Set D), m ∈ normalizer (R : Set D) →
      ∀ u ∈ U, m * u * m⁻¹ ∈ U := by
    intro m hmV hmR u hu
    rw [← hVX]
    exact mem_inf.2 ⟨(mem_normalizer_iff.1 hmV u).1 (mem_sup_left hu), hconjX m hmR u (hUX hu)⟩
  have hlU : l ∈ normalizer (U : Set D) :=
    mem_normalizer_of_conj_mem (hconjU l hlV hlR) fun x hx => by
      have := hconjU l⁻¹ (inv_mem hlV) (inv_mem hlR) x hx
      rwa [inv_inv] at this
  refine ⟨hlX, hlU, ?_, ?_⟩
  · refine mem_normalizer_of_conj_mem (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxX, hxN⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨(mem_normalizer_iff.1 hlX x).1 hxX,
        mul_mem (mul_mem hlU hxN) (inv_mem hlU)⟩
    · obtain ⟨hxX, hxN⟩ := mem_inf.1 hx
      have h1 := (mem_normalizer_iff.1 (inv_mem hlX) x).1 hxX
      rw [inv_inv] at h1
      exact mem_inf.2 ⟨h1, mul_mem (mul_mem (inv_mem hlU) hxN) hlU⟩
  · have hcen : ∀ m ∈ normalizer (U : Set D), ∀ c ∈ centralizer (U : Set D),
        m * c * m⁻¹ ∈ centralizer (U : Set D) := by
      intro m hm c hc
      rw [mem_centralizer_iff]
      intro u hu
      have hu' : m⁻¹ * u * m⁻¹⁻¹ ∈ U := (mem_normalizer_iff.1 (inv_mem hm) u).1 hu
      rw [inv_inv] at hu'
      have hcu := mem_centralizer_iff.1 hc _ hu'
      calc u * (m * c * m⁻¹) = m * ((m⁻¹ * u * m) * c) * m⁻¹ := by group
        _ = m * (c * (m⁻¹ * u * m)) * m⁻¹ := by rw [hcu]
        _ = m * c * m⁻¹ * u := by group
    refine mem_normalizer_of_conj_mem (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxX, hxC⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨(mem_normalizer_iff.1 hlX x).1 hxX, hcen l hlU x hxC⟩
    · obtain ⟨hxX, hxC⟩ := mem_inf.1 hx
      have h1 := (mem_normalizer_iff.1 (inv_mem hlX) x).1 hxX
      rw [inv_inv] at h1
      have h2 := hcen l⁻¹ (inv_mem hlU) x hxC
      rw [inv_inv] at h2
      exact mem_inf.2 ⟨h1, h2⟩

end Linear

section Singer

variable {J R X U P : Subgroup D} {n : ℕ}

theorem rho_eq_one_iff {V : Subgroup D} (l : normalizer (V : Set D)) :
    V.normalizerMonoidHom l = 1 ↔ (l : D) ∈ centralizer (V : Set D) := by
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, mem_subgroupOf]

theorem range_rho_comp_inclusion {V N : Subgroup D} (hN : N ≤ normalizer (V : Set D)) :
    (V.normalizerMonoidHom.comp (Subgroup.inclusion hN)).range =
      (N.subgroupOf (normalizer (V : Set D))).map V.normalizerMonoidHom := by
  ext α
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨Subgroup.inclusion hN g, g.2, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩

theorem ker_rho_comp_inclusion {V N : Subgroup D} (hN : N ≤ normalizer (V : Set D)) :
    (V.normalizerMonoidHom.comp (Subgroup.inclusion hN)).ker =
      (N ⊓ centralizer (V : Set D)).subgroupOf N := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, rho_eq_one_iff, mem_subgroupOf, mem_inf]
  exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩

theorem gms_singer_image_equiv [Finite D] (h : GMSNormalRootData J R X U P n) :
    ∃ e : GMSNormalizerQuotient X U ≃* gmsSingerImage X U (U ⊔ R),
      ∀ (c : GMSNormalizerQuotient X U) (u : U),
        ((e c : MulAut ↥(U ⊔ R)) ⟨u, mem_sup_left u.2⟩ : D) = (gmsQuotConjAct X U c u : D) := by
  have hNV := gms_NXU_le_L h
  have hkerV := gms_NXU_inf_CV h
  set φ := (U ⊔ R).normalizerMonoidHom.comp (Subgroup.inclusion hNV) with hφ
  have hker : φ.ker = (X ⊓ centralizer (U : Set D)).subgroupOf (X ⊓ normalizer (U : Set D)) := by
    rw [hφ, ker_rho_comp_inclusion, hkerV]
  have hrange : φ.range = gmsSingerImage X U (U ⊔ R) := by
    rw [hφ, range_rho_comp_inclusion]
    rfl
  refine ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange), ?_⟩
  intro c u
  induction c using QuotientGroup.induction_on with
  | H g => rfl

theorem gms_singer_image_le [Finite D] (h : GMSNormalRootData J R X U P n) :
    gmsSingerImage X U (U ⊔ R) ≤ gmsRootStabilizer (U ⊔ R) R := by
  have hXC : X ≤ centralizer (R : Set D) := h.2.2.2.1.2.2
  rintro _ ⟨l, hl, rfl⟩
  have hlR : (l : D) ∈ normalizer (R : Set D) :=
    centralizer_le_normalizer _ (hXC (mem_inf.1 (mem_subgroupOf.1 hl)).1)
  have : l ∈ (gmsRootStabilizer (U ⊔ R) R).comap (U ⊔ R).normalizerMonoidHom := by
    rw [comap_gmsRootStabilizer le_sup_right, mem_subgroupOf]
    exact hlR
  exact this

theorem gms_singer_image_normal [Finite D] (h : GMSNormalRootData J R X U P n) :
    ((gmsSingerImage X U (U ⊔ R)).subgroupOf (gmsRootStabilizer (U ⊔ R) R)).Normal := by
  constructor
  intro a ha b
  rw [mem_subgroupOf] at ha ⊢
  obtain ⟨⟨l, hlb⟩, -⟩ := mem_inf.1 b.2
  have hl : l ∈ (gmsRootStabilizer (U ⊔ R) R).comap (U ⊔ R).normalizerMonoidHom := by
    change (U ⊔ R).normalizerMonoidHom l ∈ gmsRootStabilizer (U ⊔ R) R
    rw [hlb]
    exact b.2
  rw [comap_gmsRootStabilizer le_sup_right, mem_subgroupOf] at hl
  obtain ⟨-, -, hlN, -⟩ := gms_LR_normalizes h l.2 hl
  obtain ⟨g, hg, hga⟩ := ha
  rw [SetLike.mem_coe, mem_subgroupOf] at hg
  have hNV := gms_NXU_le_L h
  refine ⟨⟨(l : D) * g * (l : D)⁻¹, hNV ((mem_normalizer_iff.1 hlN g).1 hg)⟩,
    (mem_normalizer_iff.1 hlN g).1 hg, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hlb, ← hga]
  have e : (⟨(l : D) * g * (l : D)⁻¹, hNV ((mem_normalizer_iff.1 hlN g).1 hg)⟩ :
      normalizer ((U ⊔ R : Subgroup D) : Set D)) = l * g * l⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]

end Singer

section Delta

theorem gmsRootConjugateAction_apply (V R : Subgroup D) (l : normalizer (V : Set D))
    (Q : gmsRootConjugates V R) :
    ((gmsRootConjugateAction V R l Q : gmsRootConjugates V R) : Subgroup D) =
      (Q : Subgroup D).map (MulAut.conj (l : D)).toMonoidHom :=
  rfl

theorem ker_gmsRootConjugateAction (V R : Subgroup D) :
    (gmsRootConjugateAction V R).ker = gmsRootKernel V R := by
  ext l
  rw [MonoidHom.mem_ker, gmsRootKernel, Subgroup.mem_iInf]
  constructor
  · intro h Q
    rw [mem_subgroupOf, ← map_conj_eq_self_iff, ← gmsRootConjugateAction_apply, h]
    rfl
  · intro h
    refine Equiv.ext fun Q => Subtype.ext ?_
    have hQ := h Q
    rw [mem_subgroupOf, ← map_conj_eq_self_iff] at hQ
    rw [gmsRootConjugateAction_apply, hQ]
    rfl

theorem centralizer_le_gmsRootKernel (V R : Subgroup D) :
    (centralizer (V : Set D)).subgroupOf (normalizer (V : Set D)) ≤ gmsRootKernel V R := by
  intro l hl
  rw [mem_subgroupOf] at hl
  rw [gmsRootKernel, Subgroup.mem_iInf]
  intro Q
  obtain ⟨-, -, hQV⟩ := Q.2
  rw [mem_subgroupOf]
  refine mem_normalizer_of_conj_mem (fun x hx => ?_) (fun x hx => ?_)
  · rw [← mem_centralizer_iff.1 hl x (hQV hx), mul_inv_cancel_right]
    exact hx
  · have hl' := inv_mem hl
    rw [← mem_centralizer_iff.1 hl' x (hQV hx), inv_mul_cancel_right]
    exact hx

end Delta

section Node

variable {J R X U P : Subgroup D} {n : ℕ}

theorem gms_normal_root_actual_linear_family_and_kernels [Finite D]
    (h : GMSNormalRootData J R X U P n) :
    IsElementaryAbelian 2 ↥(U ⊔ R) ∧ Nat.card U = 2 ^ n ∧ 3 ≤ n ∧
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card R = 2 ^ m ∧
    (∀ Q ∈ gmsRootConjugates (U ⊔ R) R, Q ≤ U ⊔ R ∧ Nat.card Q = 2 ^ m) ∧
    (∀ Q ∈ gmsRootConjugates (U ⊔ R) R, ∀ Z ∈ gmsRootConjugates (U ⊔ R) R, Q ≠ Z →
      Q ⊓ Z = ⊥) ∧
    MulAction.IsPretransitive (normalizer ((U ⊔ R : Subgroup D) : Set D))
      (gmsRootConjugates (U ⊔ R) R) ∧
    (U ⊔ R).normalizerMonoidHom.ker = (centralizer ((U ⊔ R : Subgroup D) : Set D)).subgroupOf
      (normalizer ((U ⊔ R : Subgroup D) : Set D)) ∧
    (gmsRootStabilizer (U ⊔ R) R).comap (U ⊔ R).normalizerMonoidHom =
      (normalizer (R : Set D)).subgroupOf (normalizer ((U ⊔ R : Subgroup D) : Set D)) ∧
    (U ⊔ R) ⊓ X = U ∧
    X ⊓ normalizer (U : Set D) ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) ∧
    (∀ l ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ normalizer (R : Set D),
      l ∈ normalizer (X : Set D) ∧ l ∈ normalizer (U : Set D) ∧
        l ∈ normalizer ((X ⊓ normalizer (U : Set D) : Subgroup D) : Set D) ∧
        l ∈ normalizer ((X ⊓ centralizer (U : Set D) : Subgroup D) : Set D)) ∧
    gmsSingerImage X U (U ⊔ R) ≤ gmsRootStabilizer (U ⊔ R) R ∧
    ((gmsSingerImage X U (U ⊔ R)).subgroupOf (gmsRootStabilizer (U ⊔ R) R)).Normal ∧
    (∀ α ∈ gmsSingerImage X U (U ⊔ R), ∀ r : ↥(U ⊔ R), (r : D) ∈ R → α r = r) ∧
    (∀ α ∈ gmsSingerImage X U (U ⊔ R), α • U.subgroupOf (U ⊔ R) = U.subgroupOf (U ⊔ R)) ∧
    IsCyclic (gmsSingerImage X U (U ⊔ R)) ∧
    Nat.card (gmsSingerImage X U (U ⊔ R)) = 2 ^ n - 1 ∧
    (∀ u v : ↥(U ⊔ R), (u : D) ∈ U → (v : D) ∈ U → u ≠ 1 → v ≠ 1 →
      ∃! α : gmsSingerImage X U (U ⊔ R), (α : MulAut ↥(U ⊔ R)) u = v) ∧
    (∀ g (hg : g ∈ X ⊓ normalizer (U : Set D)),
      (U ⊔ R).normalizerMonoidHom ⟨g, gms_NXU_le_L h hg⟩ = 1 ↔
        g ∈ X ⊓ centralizer (U : Set D)) ∧
    (gmsRootConjugateAction (U ⊔ R) R).ker = gmsRootKernel (U ⊔ R) R ∧
    (centralizer ((U ⊔ R : Subgroup D) : Set D)).subgroupOf
      (normalizer ((U ⊔ R : Subgroup D) : Set D)) ≤ gmsRootKernel (U ⊔ R) R ∧
    (∃ π' : (U ⊔ R).normalizerMonoidHom.range →* Equiv.Perm (gmsRootConjugates (U ⊔ R) R),
      (∀ l, π' ((U ⊔ R).normalizerMonoidHom.rangeRestrict l) =
        gmsRootConjugateAction (U ⊔ R) R l) ∧
      π'.ker = (gmsRootKernel (U ⊔ R) R).map (U ⊔ R).normalizerMonoidHom.rangeRestrict) ∧
    Nonempty (↥((gmsRootKernel (U ⊔ R) R).map (U ⊔ R).normalizerMonoidHom) ≃*
      ↥(gmsRootKernel (U ⊔ R) R) ⧸
        ((U ⊔ R).normalizerMonoidHom.comp (gmsRootKernel (U ⊔ R) R).subtype).ker) ∧
    ((U ⊔ R).normalizerMonoidHom.comp (gmsRootKernel (U ⊔ R) R).subtype).ker =
      ((centralizer ((U ⊔ R : Subgroup D) : Set D)).subgroupOf
        (normalizer ((U ⊔ R : Subgroup D) : Set D))).subgroupOf (gmsRootKernel (U ⊔ R) R) := by
  classical
  have h0 := h
  have hVel := gms_isElementaryAbelian_V h
  have hNV := gms_NXU_le_L h
  have hkerV := gms_NXU_inf_CV h
  have hRne := GMSNormalRootData.ne_bot h
  obtain ⟨e, he⟩ := gms_singer_image_equiv h
  obtain ⟨hn3, -, ⟨hRel, -, -⟩, ⟨-, -, hXC⟩, ⟨-, -, -, hUcard⟩, ⟨hcyc, hqcard, hreg⟩, -⟩ := h
  have : IsElementaryAbelian 2 R := hRel
  obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 R).exists_card_eq
  have hm1 : 1 ≤ m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    rw [hm0', pow_zero] at hm
    exact hRne (Subgroup.eq_bot_of_card_eq R hm)
  have hker := Subgroup.normalizerMonoidHom_ker (U ⊔ R)
  set ρ := (U ⊔ R).normalizerMonoidHom with hρ
  set π := gmsRootConjugateAction (U ⊔ R) R with hπ
  have hπker := ker_gmsRootConjugateAction (U ⊔ R) R
  have hCK := centralizer_le_gmsRootKernel (U ⊔ R) R
  have hρπ : ρ.rangeRestrict.ker ≤ π.ker := by
    rw [MonoidHom.ker_rangeRestrict, hker, hπker]
    exact hCK
  set π' := (ρ.rangeRestrict.liftOfRightInverse (Function.surjInv ρ.rangeRestrict_surjective)
    (Function.surjInv_eq ρ.rangeRestrict_surjective)) ⟨π, hρπ⟩ with hπ'
  have hπ'apply : ∀ l, π' (ρ.rangeRestrict l) = π l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨π, hρπ⟩ l
  have hπ'ker : π'.ker = (gmsRootKernel (U ⊔ R) R).map ρ.rangeRestrict := by
    ext α
    obtain ⟨l, rfl⟩ := ρ.rangeRestrict_surjective α
    rw [MonoidHom.mem_ker, hπ'apply]
    constructor
    · intro hl
      exact ⟨l, hπker ▸ hl, rfl⟩
    · rintro ⟨l', hl', hll'⟩
      have hl'π : π l' = 1 := by
        rw [← MonoidHom.mem_ker, hπker]
        exact hl'
      rw [← hπ'apply, hll', hπ'apply] at hl'π
      exact hl'π
  have hrange : (ρ.comp (gmsRootKernel (U ⊔ R) R).subtype).range =
      (gmsRootKernel (U ⊔ R) R).map ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerK : (ρ.comp (gmsRootKernel (U ⊔ R) R).subtype).ker =
      ((centralizer ((U ⊔ R : Subgroup D) : Set D)).subgroupOf
        (normalizer ((U ⊔ R : Subgroup D) : Set D))).subgroupOf (gmsRootKernel (U ⊔ R) R) := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, mem_subgroupOf, ← hker, MonoidHom.mem_ker]
    rfl
  refine ⟨hVel, hUcard, hn3, m, hm1, hm, fun Q hQ => ⟨?_, (gms_card_of_mem hQ).trans hm⟩,
    fun Q hQ Z hZ hQZ => gms_inf_eq_bot h0 hQ hZ hQZ, gms_isPretransitive h0, hker,
    comap_gmsRootStabilizer le_sup_right, gms_inf_X h0, hNV,
    fun l hl => gms_LR_normalizes h0 (mem_inf.1 hl).1 (mem_inf.1 hl).2,
    gms_singer_image_le h0, gms_singer_image_normal h0, ?_, ?_,
    isCyclic_of_surjective e.toMonoidHom e.surjective, (Nat.card_congr e.symm.toEquiv).trans hqcard,
    ?_, ?_, hπker, hCK, ⟨π', hπ'apply, hπ'ker⟩,
    ⟨(MulEquiv.subgroupCongr hrange.symm).trans (QuotientGroup.quotientKerEquivRange _).symm⟩,
    hkerK⟩
  · obtain ⟨-, -, hle⟩ := hQ
    exact hle
  · rintro _ ⟨l, hl, rfl⟩ r hr
    rw [SetLike.mem_coe, mem_subgroupOf] at hl
    apply Subtype.ext
    rw [gms_rho_apply, ← mem_centralizer_iff.1 (hXC (mem_inf.1 hl).1) r hr, mul_inv_cancel_right]
  · rintro _ ⟨l, hl, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hl
    exact (gms_rho_smul_eq_iff le_sup_left l).2 (mem_inf.1 hl).2
  · intro u v hu hv hu1 hv1
    have hu1' : (⟨u, hu⟩ : U) ≠ 1 := fun h1 =>
      hu1 (Subtype.ext (by simpa using congrArg (fun x : U => (x : D)) h1))
    have hv1' : (⟨v, hv⟩ : U) ≠ 1 := fun h1 =>
      hv1 (Subtype.ext (by simpa using congrArg (fun x : U => (x : D)) h1))
    obtain ⟨c, hc, hcu⟩ := hreg ⟨u, hu⟩ ⟨v, hv⟩ hu1' hv1'
    have hformula : ∀ c' : GMSNormalizerQuotient X U,
        (((e c' : MulAut ↥(U ⊔ R)) u : ↥(U ⊔ R)) : D) = (gmsQuotConjAct X U c' ⟨u, hu⟩ : D) :=
      fun c' => he c' ⟨u, hu⟩
    refine ⟨e c, Subtype.ext ?_, fun α hα => ?_⟩
    · rw [hformula, hc]
    · have hα' : gmsQuotConjAct X U (e.symm α) ⟨u, hu⟩ = ⟨v, hv⟩ := by
        apply Subtype.ext
        rw [← hformula, MulEquiv.apply_symm_apply]
        exact congrArg Subtype.val hα
      rw [← hcu (e.symm α) hα', MulEquiv.apply_symm_apply]
  · intro g hg
    rw [rho_eq_one_iff]
    change g ∈ centralizer ((U ⊔ R : Subgroup D) : Set D) ↔ _
    rw [← hkerV]
    exact ⟨fun hc => mem_inf.2 ⟨hg, hc⟩, fun hc => (mem_inf.1 hc).2⟩

end Node

end CFSG.LocalAnalysis.SteinbergBV
