module

public import CFSG.RankThree.GF2n.Smith81.Lin26Two
public import CFSG.RankThree.GF2n.Smith81.Lin213Outside
public import CFSG.RankThree.GF2n.Smith81.Lin26Normal

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Pointwise Matrix

variable {G : Type} [Group G]

section RankOne

variable {V : Subgroup G} {t : G}

theorem comm_mul_of_abelian (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V) {v w : G} (hv : v ∈ V) (hw : w ∈ V) :
    ⁅t, v * w⁆ = ⁅t, v⁆ * ⁅t, w⁆ := by
  have h1 : ⁅t, v * w⁆ = (t * v * t⁻¹) * (((t * w * t⁻¹) * w⁻¹) * v⁻¹) := by
    simp only [commutatorElement_def]; group
  have h2 : ⁅t, v⁆ * ⁅t, w⁆ = (t * v * t⁻¹) * (v⁻¹ * ((t * w * t⁻¹) * w⁻¹)) := by
    simp only [commutatorElement_def]; group
  rw [h1, h2, hab _ (V.mul_mem (htV w hw) (V.inv_mem hw)) _ (V.inv_mem hv)]

theorem comm_mem_of_normalizes (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V) {v : G} (hv : v ∈ V) :
    ⁅t, v⁆ ∈ V := by
  rw [commutatorElement_def]
  exact V.mul_mem (htV v hv) (V.inv_mem hv)

theorem comm_comm_eq_one (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hsq : ∀ v ∈ V, v * v = 1)
    (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (ht : t * t = 1) {v : G} (hv : v ∈ V) :
    ⁅t, ⁅t, v⁆⁆ = 1 := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set a := t * v * t⁻¹ with ha
  have haV : a ∈ V := htV v hv
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a haV)
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hsq v hv)
  have hta : t * a * t⁻¹ = v := by
    rw [ha, hti]
    calc t * (t * v * t) * t = (t * t) * v * (t * t) := by group
      _ = v := by rw [ht, one_mul, mul_one]
  have hc : ⁅t, v⁆ = a * v := by rw [commutatorElement_def, ← ha, hvi]
  rw [hc, commutatorElement_def]
  have e : t * (a * v) * t⁻¹ = (t * a * t⁻¹) * (t * v * t⁻¹) := by group
  rw [e, hta, ← ha, hab v hv a haV, mul_inv_cancel]

theorem rankOne_comm [Finite G] {Z : Subgroup G} (hZV : Z ≤ V)
    (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hsq : ∀ v ∈ V, v * v = 1)
    (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (ht : t * t = 1) (htZ : ∀ z ∈ Z, t * z = z * t)
    (hV : Nat.card V = Nat.card Z ^ 3) (hdim : HasDimOn V Z 1 t) {v : G} (hv : v ∈ V)
    (hz : ⁅t, v⁆ ∈ Z) : ⁅t, v⁆ = 1 ∧ ∃ w ∈ V, ∃ z ∈ Z, v = ⁅t, w⁆ * z := by
  classical
  let f : V →* G :=
    { toFun := fun v => ⁅t, (v : G)⁆
      map_one' := by simp
      map_mul' := fun v w => comm_mul_of_abelian hab htV v.2 w.2 }
  have hf : ∀ w : V, f w = ⁅t, (w : G)⁆ := fun _ => rfl
  set F : Subgroup G := f.range with hFdef
  have hFV : F ≤ V := by
    rintro _ ⟨w, rfl⟩
    exact comm_mem_of_normalizes htV w.2
  have hFc : F = ⁅V, Subgroup.zpowers t⁆ := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      rw [hf, ← commutatorElement_inv]
      exact Subgroup.inv_mem _
        (Subgroup.commutator_mem_commutator w.2 (Subgroup.mem_zpowers t))
    · rw [Subgroup.commutator_le]
      intro a ha s hs
      rcases eq_one_or_eq_of_mem_zpowers ht hs with rfl | rfl
      · rw [commutatorElement_one_right]; exact F.one_mem
      · rw [← inv_inv ⁅a, s⁆, commutatorElement_inv]
        exact F.inv_mem ⟨⟨a, ha⟩, rfl⟩
  have hFZ : Nat.card ↥(F ⊔ Z) = Nat.card Z ^ 2 := by
    have := hdim; unfold HasDimOn at this; rw [← hFc] at this; exact this
  have hZN : Z ≤ Subgroup.normalizer (F : Set G) :=
    le_normalizer_of_comm fun c hc a ha => (hab a (hFV ha) c (hZV hc)).symm
  have hprod := card_sup_mul_card_inf_of_normalizer (A := F) (C := Z) hZN
  set Kz : Subgroup V := Z.comap f with hKz
  have hidx : Kz.index = Z.relIndex F := Subgroup.index_comap Z f
  have hrel := Subgroup.relIndex_mul_card (H := Z) (K := F)
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hFpos : 0 < Nat.card ↥(F ⊓ Z) := Nat.card_pos
  have hrelq : Z.relIndex F = Nat.card Z := by
    rw [inf_comm] at hrel
    have h3 : Nat.card ↥(F ⊔ Z) * Nat.card ↥(F ⊓ Z) =
        Z.relIndex F * Nat.card ↥(F ⊓ Z) * Nat.card Z := by rw [hprod, hrel]
    rw [hFZ, pow_two] at h3
    have h4 : Nat.card Z * Nat.card Z * Nat.card ↥(F ⊓ Z) =
        (Z.relIndex F * Nat.card Z) * Nat.card ↥(F ⊓ Z) := by rw [h3]; ring
    have h5 := Nat.eq_of_mul_eq_mul_right hFpos h4
    exact (Nat.eq_of_mul_eq_mul_right hZpos h5).symm
  have hKcard : Nat.card Kz = Nat.card Z ^ 2 := by
    have h := Subgroup.card_mul_index Kz
    rw [hidx, hrelq, hV] at h
    have h' : Nat.card Kz * Nat.card Z = Nat.card Z ^ 2 * Nat.card Z := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hZpos h'
  set K' : Subgroup G := Kz.map V.subtype with hK'
  have hK'card : Nat.card K' = Nat.card Z ^ 2 := by
    rw [hK', Subgroup.card_map_of_injective V.subtype_injective, hKcard]
  have hle : F ⊔ Z ≤ K' := by
    refine sup_le ?_ ?_
    · rintro _ ⟨w, rfl⟩
      refine ⟨⟨_, comm_mem_of_normalizes htV w.2⟩, ?_, rfl⟩
      change ⁅t, ⁅t, (w : G)⁆⁆ ∈ Z
      rw [comm_comm_eq_one hab hsq htV ht w.2]
      exact Z.one_mem
    · intro z hz
      refine ⟨⟨z, hZV hz⟩, ?_, rfl⟩
      change ⁅t, z⁆ ∈ Z
      rw [commutatorElement_def, htZ z hz, mul_inv_cancel_right, mul_inv_cancel]
      exact Z.one_mem
  have heq : F ⊔ Z = K' := Subgroup.eq_of_le_of_card_ge hle (by rw [hK'card, hFZ])
  have hvK : v ∈ F ⊔ Z := by rw [heq]; exact ⟨⟨v, hv⟩, hz, rfl⟩
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right F Z
    (le_normalizer_of_comm fun c hc a ha => (hab a (hZV ha) c (hFV hc)).symm)
  have hvK' : v ∈ ((F ⊔ Z : Subgroup G) : Set G) := hvK
  rw [hset] at hvK'
  obtain ⟨y, ⟨w, rfl⟩, z, hzZ, rfl⟩ := hvK'
  refine ⟨?_, w, w.2, z, hzZ, rfl⟩
  have hzV : z ∈ V := hZV hzZ
  rw [show (fun x1 x2 => x1 * x2) (f w) z = f w * z from rfl, hf,
    comm_mul_of_abelian hab htV (comm_mem_of_normalizes htV w.2) hzV,
    comm_comm_eq_one hab hsq htV ht w.2, one_mul, commutatorElement_def, htZ z hzZ,
    mul_inv_cancel_right, mul_inv_cancel]

end RankOne

theorem eq_one_of_mul_mul_eq' {F : Type} [Field F] [CharP F 2] {A B : Matrix (Fin 2) (Fin 2) F}
    (hA : A.det = 1) (h : ∀ X, A * X * B = X) : B = 1 := by
  have hAB : A * B = 1 := by simpa using h 1
  have hBA : B * A = 1 := mul_eq_one_comm.mp hAB
  have hcomm : ∀ X, A * X = X * A := by
    intro X
    calc A * X = A * X * (B * A) := by rw [hBA, Matrix.mul_one]
      _ = A * X * B * A := by simp only [Matrix.mul_assoc]
      _ = X * A := by rw [h X]
  obtain ⟨c, hc⟩ : A ∈ Set.range (Matrix.scalar (Fin 2)) :=
    Matrix.mem_range_scalar_iff_commute_single'.mpr fun i j => (hcomm _).symm
  have hc1 : c = 1 := by
    have hdet : (Matrix.scalar (Fin 2) c).det = c ^ 2 := by
      simp [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two, sq]
    rw [hc, hA] at hdet
    have : c ^ 2 = 1 ^ 2 := by rw [← hdet, one_pow]
    exact CharTwo.sq_inj.mp this
  have hA1 : A = 1 := by rw [← hc, hc1]; simp
  simpa [hA1] using hAB

section TMAux

variable [Finite G] {M Q Z B : Subgroup G} {TM : TensorModel M Q Z B}

theorem exists_phi_eq' (g : Matrix (Fin 2) (Fin 2) TM.F) (hg : g.det = 1) :
    ∃ s : ↥(Lgen M (LB M Q B)), (TM.φ s : Matrix (Fin 2) (Fin 2) TM.F) = g := by
  have hmem : Matrix.GeneralLinearGroup.mkOfDetNeZero g (by rw [hg]; exact one_ne_zero) ∈
      TM.φ.range := by
    rw [TM.φ_range]
    exact StatedAPI.mem_statedSL_iff.mpr (by simpa using hg)
  obtain ⟨s, hs⟩ := hmem
  exact ⟨s, by rw [hs]; rfl⟩

theorem exists_matrix_form' (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M)
    (T : TM.M₀.E ≃ₗ[TM.K] TM.M₀.E)
    (hTπ : ∀ x ∈ Q, TM.M₀.π (t * x * t⁻¹) = T (TM.M₀.π x)) :
    ∃ P H : Matrix (Fin 2) (Fin 2) TM.F, P.det = 1 ∧ IsUnit H.det ∧
      ∀ e, TM.Φ (T e) = P * TM.Φ e * H := by
  set T' : Matrix (Fin 2) (Fin 2) TM.F →+ Matrix (Fin 2) (Fin 2) TM.F :=
    (TM.Φ.symm.trans (T.toAddEquiv.trans TM.Φ)).toAddMonoidHom
  have hT'_apply : ∀ X, T' X = TM.Φ (T (TM.Φ.symm X)) := fun X => rfl
  have hbij : Function.Bijective T' := (TM.Φ.symm.trans (T.toAddEquiv.trans TM.Φ)).bijective
  have hlin : ∀ (c : TM.F) X, T' (c • X) = c • T' X := by
    intro c X
    obtain ⟨k, rfl⟩ := TM.ε.surjective c
    rw [hT'_apply, hT'_apply]
    have h1 : TM.Φ.symm (TM.ε k • X) = k • TM.Φ.symm X := by
      rw [AddEquiv.symm_apply_eq, TM.smul, AddEquiv.apply_symm_apply]
    rw [h1, map_smul, TM.smul]
  have hT : ∀ g : Matrix (Fin 2) (Fin 2) TM.F, g.det = 1 →
      ∃ g' : Matrix (Fin 2) (Fin 2) TM.F, ∀ X, T' (g * X) = g' * T' X := by
    intro g hg
    obtain ⟨s, hs⟩ := exists_phi_eq' (TM := TM) g hg
    have hsM : (s : G) ∈ M := hc.Lgen_le_M s.2
    have hs' : t * (s : G) * t⁻¹ ∈ Lgen M (LB M Q B) :=
      (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M (LB M Q B) htM) _).mp s.2
    refine ⟨(TM.φ ⟨_, hs'⟩ : Matrix (Fin 2) (Fin 2) TM.F), fun X => ?_⟩
    obtain ⟨x, hxQ, hx⟩ := TM.M₀.π_surj (TM.Φ.symm X)
    have hX : X = TM.Φ (TM.M₀.π x) := by rw [hx, AddEquiv.apply_symm_apply]
    rw [hX, hT'_apply, hT'_apply, AddEquiv.symm_apply_apply, ← hs, ← TM.act s x hxQ,
      AddEquiv.symm_apply_apply, ← hTπ _ (conj_mem_Q hc.hyp hsM hxQ), ← hTπ _ hxQ,
      ← TM.act ⟨_, hs'⟩ _ (conj_mem_Q hc.hyp htM hxQ)]
    have e : t * ((s : G) * x * (s : G)⁻¹) * t⁻¹ =
        (t * (s : G) * t⁻¹) * (t * x * t⁻¹) * (t * (s : G) * t⁻¹)⁻¹ := by group
    rw [e]
  obtain ⟨P₀, H₀, hP₀, hH₀, hform⟩ := exists_mul_mul_of_intertwine T' hbij hlin hT
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' P₀.det
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [mul_zero] at hr; exact hP₀.ne_zero hr
  refine ⟨r⁻¹ • P₀, r • H₀, ?_, ?_, fun e => ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin, hr, ← sq, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 hr0)]
  · rw [Matrix.det_smul]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hr0)).mul hH₀
  · have := hform (TM.Φ e)
    rw [hT'_apply, AddEquiv.symm_apply_apply] at this
    rw [this]
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hr0]

end TMAux

section World

variable [Finite G] {M Q Z B : Subgroup G} {V₁ V₂ : Subgroup G}

theorem Q_le_LgenLB : Q ≤ Lgen M (LB M Q B) :=
  (le_sup_left : Q ≤ Q ⊔ (QB B ⊓ M)).trans (le_Lgen_self M (LB M Q B))

theorem Z_comm (H : StrothHyp M Q Z) {z q : G} (hz : z ∈ Z) (hq : q ∈ Q) : z * q = q * z := by
  have h : z ∈ cen Q := H.hZ ▸ hz
  rw [cen_eq] at h
  exact (Subgroup.mem_centralizer_iff.mp h.2 q hq).symm

theorem conj_mem_of_normalizer {V : Subgroup G} {t : G} (h : t ∈ Subgroup.normalizer (V : Set G))
    {v : G} (hv : v ∈ V) : t * v * t⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp h v).mp hv

theorem comm_eq_one_of_mem_Z (hc : Ctx M Q Z B) (SS : OddSetup M Q Z B V₁ V₂)
    (hc₁ : Nat.card V₁ = Nat.card Z ^ 3) (hc₂ : Nat.card V₂ = Nat.card Z ^ 3)
    {x : G} (hxL : x ∈ Lgen M (LB M Q B)) (hx2 : x * x = 1)
    (hd₁ : HasDimOn V₁ Z 1 x) (hd₂ : HasDimOn V₂ Z 1 x) {d : G} (hd : d ∈ Q)
    (hdZ : ⁅x, d⁆ ∈ Z) : ⁅x, d⁆ = 1 ∧ ∃ e ∈ Q, ∃ z ∈ Z, d = ⁅x, e⁆ * z := by
  have H := hc.hyp
  have hxZ : ∀ z ∈ Z, x * z = z * x := fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (Lgen_le_H0 hc hxL).2 z hz).symm
  have hx₁ : ∀ v ∈ V₁, x * v * x⁻¹ ∈ V₁ := fun v hv => conj_mem_of_normalizer (SS.normV x hxL) hv
  have hx₂ : ∀ v ∈ V₂, x * v * x⁻¹ ∈ V₂ := fun v hv => conj_mem_of_normalizer (SS.normV' x hxL) hv
  have hQ₂ : ∀ a ∈ Q, ∀ v ∈ V₂, a * v * a⁻¹ ∈ V₂ := fun a ha v hv =>
    conj_mem_of_normalizer (SS.normV' a (Q_le_LgenLB ha)) hv
  have R₁ := fun {v : G} (hv : v ∈ V₁) (hz : ⁅x, v⁆ ∈ Z) =>
    rankOne_comm SS.ZV SS.abV SS.sqV hx₁ hx2 hxZ hc₁ hd₁ hv hz
  have R₂ := fun {v : G} (hv : v ∈ V₂) (hz : ⁅x, v⁆ ∈ Z) =>
    rankOne_comm SS.ZV' SS.abV' SS.sqV' hx₂ hx2 hxZ hc₂ hd₂ hv hz
  obtain ⟨a, ha, b, hb, rfl⟩ := SS.dec d hd
  have hdec : ∀ a' b' : G, ⁅x, a' * b'⁆ = ⁅x, a'⁆ * (a' * ⁅x, b'⁆ * a'⁻¹) := fun a' b' => by
    simp only [commutatorElement_def]; group
  have hp₁ : ⁅x, a⁆ ∈ V₁ := comm_mem_of_normalizes hx₁ ha
  have hr₂ : a * ⁅x, b⁆ * a⁻¹ ∈ V₂ := hQ₂ a (SS.VQ ha) _ (comm_mem_of_normalizes hx₂ hb)
  rw [hdec] at hdZ
  have hp₂ : ⁅x, a⁆ ∈ V₂ := by
    have : ⁅x, a⁆ = (⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹)) * (a * ⁅x, b⁆ * a⁻¹)⁻¹ := by group
    rw [this]
    exact V₂.mul_mem (SS.ZV' hdZ) (V₂.inv_mem hr₂)
  have hpZ : ⁅x, a⁆ ∈ Z := by rw [← SS.int]; exact ⟨hp₁, hp₂⟩
  obtain ⟨hp1, a₀, ha₀, za, hza, hae⟩ := R₁ ha hpZ
  rw [hp1, one_mul] at hdZ
  have hbZ : ⁅x, b⁆ ∈ Z := by
    have hcomm := Z_comm H hdZ (SS.VQ ha)
    have e : ⁅x, b⁆ = a⁻¹ * ((a * ⁅x, b⁆ * a⁻¹) * a) := by group
    rw [e, hcomm, inv_mul_cancel_left]
    exact hdZ
  obtain ⟨hb1, b₀, hb₀, zb, hzb, hbe⟩ := R₂ hb hbZ
  refine ⟨by rw [hdec, hp1, hb1]; group, a₀ * b₀, Q.mul_mem (SS.VQ ha₀) (SS.V'Q hb₀), ?_⟩
  set c := ⁅x, b₀⁆ with hcdef
  have hcQ : c ∈ Q := SS.V'Q (comm_mem_of_normalizes hx₂ hb₀)
  have ha₀Q : a₀ ∈ Q := SS.VQ ha₀
  refine ⟨⁅x, a₀ * b₀⁆⁻¹ * (a * b), ?_, by group⟩
  rw [hae, hbe, hdec, ← hcdef]
  have hzaC : za * c = c * za := Z_comm H hza hcQ
  have e : (⁅x, a₀⁆ * (a₀ * c * a₀⁻¹))⁻¹ * (⁅x, a₀⁆ * za * (c * zb)) =
      ⁅a₀, c⁻¹⁆ * (c⁻¹ * (za * c)) * zb := by
    simp only [commutatorElement_def]; group
  rw [e, hzaC, inv_mul_cancel_left]
  exact Z.mul_mem (Z.mul_mem (comm_mem_Z H ha₀Q (Q.inv_mem hcQ)) hza) hzb

theorem conjSubgroup_injective {A C : Subgroup G} {m : G}
    (h : conjSubgroup m A = conjSubgroup m C) : A = C := by
  ext v
  have h1 : m * v * m⁻¹ ∈ conjSubgroup m A ↔ m * v * m⁻¹ ∈ conjSubgroup m C := by rw [h]
  simp only [mem_conjSubgroup] at h1
  simpa [mul_assoc] using h1

theorem oddSetup_conj_V (SS : OddSetup M Q Z B V₁ V₂) (hc₁ : Nat.card V₁ = Nat.card Z ^ 3)
    (hc₂ : Nat.card V₂ = Nat.card Z ^ 3) {m : G} (hm : m ∈ M) :
    (conjSubgroup m V₁ = V₁ ∧ conjSubgroup m V₂ = V₂) ∨
      (conjSubgroup m V₁ = V₂ ∧ conjSubgroup m V₂ = V₁) := by
  have H := SS.hyp
  have key : ∀ {W W' : Subgroup G}, OddSetup M Q Z B W W' → Nat.card W = Nat.card Z ^ 3 →
      Nat.card W' = Nat.card Z ^ 3 → conjSubgroup m W = W ∨ conjSubgroup m W = W' := by
    intro W W' S hW hW'
    have hsub : (conjSubgroup m W : Set G) ⊆ (W : Set G) ∪ (W' : Set G) := by
      intro w hw
      have hw' : m⁻¹ * w * m ∈ W := mem_conjSubgroup.mp hw
      by_cases hw1 : w = 1
      · left; rw [hw1]; exact W.one_mem
      have hv1 : m⁻¹ * w * m ≠ 1 := fun h => hw1 (by
        have : w = m * (m⁻¹ * w * m) * m⁻¹ := by group
        rw [this, h]; group)
      have hvQ : m⁻¹ * w * m ∈ Q := S.VQ hw'
      have hcl : InZClass Z (m⁻¹ * w * m) := (S.p31 _ hvQ hv1).mpr (Or.inl hw')
      have hwQ : w ∈ Q := by
        have := conj_mem_Q H hm hvQ
        rwa [show m * (m⁻¹ * w * m) * m⁻¹ = w by group] at this
      have hwcl : InZClass Z w := by
        have := (inZClass_conj_iff (Z := Z) m).mpr hcl
        rwa [show m * (m⁻¹ * w * m) * m⁻¹ = w by group] at this
      exact (S.p31 w hwQ hw1).mp hwcl
    have hcard : Nat.card (conjSubgroup m W) = Nat.card Z ^ 3 := by rw [card_conjSubgroup, hW]
    rcases SubgroupClass.subset_union.mp hsub with h | h
    · left; exact Subgroup.eq_of_le_of_card_ge h (by rw [hcard, hW])
    · right; exact Subgroup.eq_of_le_of_card_ge h (by rw [hcard, hW'])
  have hne : V₁ ≠ V₂ := by
    intro h
    have h1 : V₁ = Z := by rw [← SS.int, h, inf_idem]
    have hq := H.q4
    rw [h1] at hc₁
    have : Nat.card Z ^ 1 < Nat.card Z ^ 3 :=
      Nat.pow_lt_pow_right (by omega) (by norm_num)
    rw [pow_one] at this
    omega
  rcases key SS hc₁ hc₂ with h1 | h1 <;> rcases key SS.symm hc₂ hc₁ with h2 | h2
  · exact Or.inl ⟨h1, h2⟩
  · exact absurd (conjSubgroup_injective (h1.trans h2.symm)) hne
  · exact absurd (conjSubgroup_injective (h1.trans h2.symm)) hne
  · exact Or.inr ⟨h1, h2⟩

theorem exists_mem_ne_one_ne {X : Subgroup G} (hX : 3 ≤ Nat.card X) (x : G) :
    ∃ y ∈ X, y ≠ 1 ∧ y ≠ x := by
  by_contra h
  push Not at h
  have hsub : (X : Set G) ⊆ {1, x} := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]; exact Set.mem_insert _ _
    · rw [h y hy hy1]; exact Set.mem_insert_of_mem _ rfl
  have h1 : Nat.card X = (X : Set G).ncard := (Nat.card_coe_set_eq _)
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({1, x} : Set G).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  omega

theorem exists_cent_not_mem {V Z : Subgroup G} (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hsq : ∀ v ∈ V, v * v = 1) {t : G} (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (ht : t * t = 1)
    (hV : Nat.card Z ^ 2 < Nat.card V) : ∃ b ∈ V, b ∉ Z ∧ t * b * t⁻¹ = b := by
  classical
  let f : V →* G :=
    { toFun := fun v => ⁅t, (v : G)⁆
      map_one' := by simp
      map_mul' := fun v w => comm_mul_of_abelian hab htV v.2 w.2 }
  have hrk : Nat.card f.range ≤ Nat.card (f.ker.map V.subtype) := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨⟨_, comm_mem_of_normalizes htV w.2⟩, MonoidHom.mem_ker.mpr
      (comm_comm_eq_one hab hsq htV ht w.2), rfl⟩
  rw [Subgroup.card_map_of_injective V.subtype_injective] at hrk
  have hkr := Subgroup.card_ker_mul_card_range f
  by_contra hno
  push Not at hno
  have hkZ : Nat.card f.ker ≤ Nat.card Z := by
    rw [← Subgroup.card_map_of_injective V.subtype_injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨w, hw, rfl⟩
    by_contra hwZ
    apply hno _ w.2 hwZ
    have : ⁅t, (w : G)⁆ = 1 := hw
    rw [commutatorElement_def] at this
    calc t * w * t⁻¹ = (t * w * t⁻¹ * (w : G)⁻¹) * w := by group
      _ = w := by rw [this, one_mul]
  have : Nat.card V ≤ Nat.card Z ^ 2 := by
    rw [← hkr, pow_two]
    exact Nat.mul_le_mul hkZ (hrk.trans hkZ)
  omega

theorem Sit.conj_V_eq (SS : OddSetup M Q Z B V₁ V₂) (hc₁ : Nat.card V₁ = Nat.card Z ^ 3)
    (hc₂ : Nat.card V₂ = Nat.card Z ^ 3) {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) :
    conjSubgroup x V₁ = V₁ ∧ conjSubgroup x V₂ = V₂ := by
  have H := SS.hyp
  have hq := H.q4
  have h12 := smith_1_12 hs
  have hXsq : ∀ y ∈ X, y * y = 1 := by
    intro y hy
    obtain ⟨g, hg⟩ := hs.conj
    rw [hg, mem_conjSubgroup] at hy
    have h1 := Z_sq H hy
    have e : y * y = g * ((g⁻¹ * y * g) ^ 2) * g⁻¹ := by rw [pow_two]; group
    rw [e, h1]; group
  have hXM : ∀ y ∈ X, y ∈ M := fun y hy => (h12.1 hy).1
  have hx0 : ∃ x₀ ∈ X, x₀ ≠ 1 ∧ conjSubgroup x₀ V₁ = V₁ := by
    rcases oddSetup_conj_V SS hc₁ hc₂ hs.memM with h | h
    · exact ⟨x, hs.mem, hs.ne_one, h.1⟩
    obtain ⟨y, hyX, hy1, hyx⟩ :=
      exists_mem_ne_one_ne (X := X) (by rw [IsZConjugate.card_eq hs.conj]; omega) x
    rcases oddSetup_conj_V SS hc₁ hc₂ (hXM y hyX) with h' | h'
    · exact ⟨y, hyX, hy1, h'.1⟩
    refine ⟨x * y, X.mul_mem hs.mem hyX, ?_, ?_⟩
    · intro e
      apply hyx
      rw [eq_inv_of_mul_eq_one_right e]
      exact inv_eq_of_mul_eq_one_right hs.x_sq
    · rw [conjSubgroup_mul, h'.1, h.2]
  obtain ⟨x₀, hx₀X, hx₀1, hx₀V⟩ := hx0
  have hx₀V' : ∀ v ∈ V₁, x₀ * v * x₀⁻¹ ∈ V₁ := fun v hv => by
    rw [← hx₀V, mem_conjSubgroup]
    simpa [mul_assoc] using hv
  have hV₁gt : Nat.card Z ^ 2 < Nat.card V₁ := by
    rw [hc₁]; exact Nat.pow_lt_pow_right (by omega) (by norm_num)
  obtain ⟨b, hbV, hbZ, hbc⟩ :=
    exists_cent_not_mem SS.abV SS.sqV hx₀V' (hXsq x₀ hx₀X) hV₁gt
  have hb1 : b ≠ 1 := fun h => hbZ (h ▸ Z.one_mem)
  obtain ⟨g, z, hz, hz1, rfl⟩ := (SS.p31 b (SS.VQ hbV) hb1).mpr (Or.inl hbV)
  obtain ⟨h, hh⟩ := hs.conj
  set X' := conjSubgroup g⁻¹ X with hX'def
  have hX' : IsZConjugate Z X' := ⟨g⁻¹ * h, by rw [hX'def, hh, conjSubgroup_mul]⟩
  have hmemX' : ∀ y ∈ X, g⁻¹ * y * g ∈ X' := fun y hy => by
    rw [hX'def, mem_conjSubgroup]
    simpa [mul_assoc] using hy
  have hcomm : ∀ y ∈ X, (g⁻¹ * y * g) * z = z * (g⁻¹ * y * g) := by
    have hx₀' : g⁻¹ * x₀ * g ∈ M := by
      refine Sec117.mem_M_of_conj_mem_Z H hz hz1 ?_
      have e : g⁻¹ * x₀ * g * z * (g⁻¹ * x₀ * g)⁻¹ =
          g⁻¹ * (x₀ * (g * z * g⁻¹) * x₀⁻¹) * g := by group
      rw [e, hbc]
      simpa [mul_assoc] using hz
    have hx₀'1 : g⁻¹ * x₀ * g ≠ 1 := fun e => hx₀1 (by
      have : x₀ = g * (g⁻¹ * x₀ * g) * g⁻¹ := by group
      rw [this, e]; group)
    by_cases hQ : g⁻¹ * x₀ * g ∈ Q
    · have hX'Q : X' ≤ Q := root_le_Q H hX' (hmemX' x₀ hx₀X) hQ hx₀'1
      intro y hy
      exact (Z_comm H hz (hX'Q (hmemX' y hy))).symm
    · have hs' : Sit M Q Z X' (g⁻¹ * x₀ * g) := ⟨H, hX', hmemX' x₀ hx₀X, hx₀'1, hx₀', hQ⟩
      have h12' := smith_1_12 hs'
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (h12'.1 (hmemX' y hy)).2 z hz).symm
  have hxb : x⁻¹ * (g * z * g⁻¹) * x = g * z * g⁻¹ := by
    have h1 := hcomm x hs.mem
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hs.x_sq
    rw [hxi]
    calc x * (g * z * g⁻¹) * x = g * ((g⁻¹ * x * g) * z) * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * (g⁻¹ * x * g) * g⁻¹ := by rw [h1]
      _ = g * z * ((g⁻¹ * (x * x) * g)) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hs.x_sq]; group
  rcases oddSetup_conj_V SS hc₁ hc₂ hs.memM with h' | h'
  · exact h'
  · exfalso
    apply hbZ
    have hb2 : g * z * g⁻¹ ∈ V₂ := by
      rw [← h'.1, mem_conjSubgroup, hxb]
      exact hbV
    rw [← SS.int]
    exact ⟨hbV, hb2⟩

theorem hasDimOn_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂) {X : Subgroup G} {x : G}
    (hs : Sit M Q Z X x) (hxL : x ∈ Lgen M (LB M Q B)) :
    HasDimOn V₁ Z 1 x ∧ HasDimOn V₂ Z 1 x := by
  obtain ⟨k, hk1, hk2, h1, h2⟩ := linRankBoundStatement_holds G M Q Z B 2 V₁ V₂ hc hS x hxL
    hs.notQ (by rw [hs.x_sq]; exact Q.one_mem)
  obtain rfl : k = 1 := by omega
  exact ⟨h1, h2⟩

theorem Sit.comm_eq_one (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂)
    (SS : OddSetup M Q Z B V₁ V₂) {X : Subgroup G} {x : G} (hs : Sit M Q Z X x)
    (hxL : x ∈ Lgen M (LB M Q B)) {d : G} (hd : d ∈ Q) (hdZ : ⁅x, d⁆ ∈ Z) :
    ⁅x, d⁆ = 1 ∧ ∃ e ∈ Q, ∃ z ∈ Z, d = ⁅x, e⁆ * z := by
  obtain ⟨-, -, -, -, -, -, -, -, hc₁, hc₂⟩ := hS.basic
  obtain ⟨hd₁, hd₂⟩ := hasDimOn_two hc hS hs hxL
  exact comm_eq_one_of_mem_Z hc SS hc₁ hc₂ hxL hs.x_sq hd₁ hd₂ hd hdZ

theorem comm_mem_commutator_zpowers {V : Subgroup G} {x v : G} (hv : v ∈ V) :
    ⁅x, v⁆ ∈ ⁅V, Subgroup.zpowers x⁆ := by
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers x))

theorem Sit.exists_root_le_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂)
    (hBV : B ≤ V₁ ∨ B ≤ V₂) (SS : OddSetup M Q Z B V₁ V₂)
    (hL : ∀ (X' : Subgroup G) (x' : G), Sit M Q Z X' x' → x' ∈ Lgen M (LB M Q B))
    {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) :
    ∃ C : Subgroup G, IsZConjugate Z C ∧ C ≤ V₁ ∧ C ≠ Z ∧ C ≤ Q ⊓ QB X ∧
      C ⊔ Z = ⁅V₁, Subgroup.zpowers x⁆ ⊔ Z := by
  have H := hc.hyp
  obtain ⟨-, -, -, -, -, -, -, -, hc₁, hc₂⟩ := hS.basic
  have hxL := hL X x hs
  obtain ⟨hd₁, -⟩ := hasDimOn_two hc hS hs hxL
  have hxZ : ∀ z ∈ Z, x * z = z * x := fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (Lgen_le_H0 hc hxL).2 z hz).symm
  have hx₁ : ∀ v ∈ V₁, x * v * x⁻¹ ∈ V₁ := fun v hv => conj_mem_of_normalizer (SS.normV x hxL) hv
  have hq := H.q4
  obtain ⟨q', hq'V, hcZ⟩ : ∃ q' ∈ V₁, ⁅x, q'⁆ ∉ Z := by
    by_contra hno
    push Not at hno
    have hle : ⁅V₁, Subgroup.zpowers x⁆ ⊔ Z ≤ Z := by
      refine sup_le ?_ le_rfl
      rw [Subgroup.commutator_le]
      intro v hv s hs'
      rcases eq_one_or_eq_of_mem_zpowers hs.x_sq hs' with rfl | rfl
      · rw [commutatorElement_one_right]; exact Z.one_mem
      · rw [← commutatorElement_inv]; exact Z.inv_mem (hno v hv)
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card ↥(⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) = Nat.card Z ^ 2 := hd₁
    have : Nat.card Z ^ 1 < Nat.card Z ^ 2 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    rw [pow_one] at this
    omega
  set c := ⁅x, q'⁆ with hcdef
  have hcV : c ∈ V₁ := comm_mem_of_normalizes hx₁ hq'V
  have hc1 : c ≠ 1 := fun h => hcZ (h ▸ Z.one_mem)
  obtain ⟨g, z, hz, hz1, hcg⟩ := (SS.p31 c (SS.VQ hcV) hc1).mpr (Or.inl hcV)
  set C := conjSubgroup g Z with hCdef
  have hCconj : IsZConjugate Z C := ⟨g, rfl⟩
  have hcC : c ∈ C := by rw [hCdef, mem_conjSubgroup, hcg]; simpa [mul_assoc] using hz
  obtain ⟨hCV, hCQ, hCZ⟩ := SS.root_le_V hCconj hcC hcV hcZ
  have hCctx : Ctx M Q Z C := ⟨H, ⟨g, rfl⟩, hCQ, hCZ⟩
  have hxc : x * c * x⁻¹ = c := by
    have h := comm_comm_eq_one SS.abV SS.sqV hx₁ hs.x_sq hq'V
    rw [← hcdef, commutatorElement_def] at h
    calc x * c * x⁻¹ = (x * c * x⁻¹ * c⁻¹) * c := by group
      _ = c := by rw [h, one_mul]
  set x' := g⁻¹ * x * g with hx'def
  have hx'M : x' ∈ M := by
    refine Sec117.mem_M_of_conj_mem_Z H hz hz1 ?_
    have e : x' * z * x'⁻¹ = g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g := by rw [hx'def]; group
    rw [e, ← hcg, hxc, hcg]
    simpa [mul_assoc] using hz
  obtain ⟨h, hh⟩ := hs.conj
  set X' := conjSubgroup g⁻¹ X with hX'def
  have hX' : IsZConjugate Z X' := ⟨g⁻¹ * h, by rw [hX'def, hh, conjSubgroup_mul]⟩
  have hmemX' : ∀ y ∈ X, g⁻¹ * y * g ∈ X' := fun y hy => by
    rw [hX'def, mem_conjSubgroup]
    simpa [mul_assoc] using hy
  have hx'1 : x' ≠ 1 := fun e => hs.ne_one (by
    have : x = g * x' * g⁻¹ := by rw [hx'def]; group
    rw [this, e]; group)
  have hXC : X ≤ QB C := by
    by_contra hXC
    have hQ : x' ∉ Q := by
      intro hQ
      apply hXC
      have hX'Q : X' ≤ Q := root_le_Q H hX' (hmemX' x hs.mem) hQ hx'1
      intro y hy
      rw [hCdef, QB_conj_eq H g, mem_conjSubgroup]
      exact hX'Q (hmemX' y hy)
    have hs' : Sit M Q Z X' x' := ⟨H, hX', hmemX' x hs.mem, hx'1, hx'M, hQ⟩
    have hq'C : q' ∈ QB C := by
      have := (LinSetup.inf_QB_eq_two_of_le hc hS hBV hCctx).1 hCV
      rw [← this] at hq'V
      exact hq'V.2
    have hdQ : g⁻¹ * q' * g ∈ Q := by
      rw [hCdef, QB_conj_eq H g, mem_conjSubgroup] at hq'C
      exact hq'C
    have hcomm : ⁅x', g⁻¹ * q' * g⁆ = z := by
      have e : ⁅x', g⁻¹ * q' * g⁆ = g⁻¹ * c * g := by
        rw [hx'def, hcdef]; simp only [commutatorElement_def]; group
      rw [e, hcg]; group
    have := (Sit.comm_eq_one hc hS SS hs' (hL X' x' hs') hdQ (hcomm ▸ hz)).1
    exact hz1 (hcomm ▸ this)
  have hCX : C ≤ QB X := (IsZConjugate.le_QB_iff H hCconj hs.conj).mp hXC
  refine ⟨C, hCconj, hCV, hCZ, le_inf hCQ hCX, ?_⟩
  have hle : C ⊔ Z ≤ ⁅V₁, Subgroup.zpowers x⁆ ⊔ Z := by
    refine sup_le ?_ le_sup_right
    intro c' hc'
    have hc'V := hCV hc'
    have hxc' : x * c' = c' * x := hs.QB_comm_X hs.mem (hCX hc')
    have h1 : ⁅x, c'⁆ = 1 := by rw [commutatorElement_def, hxc']; group
    obtain ⟨-, w, hw, z', hz', hc'eq⟩ := rankOne_comm SS.ZV SS.abV SS.sqV hx₁ hs.x_sq hxZ hc₁
      hd₁ hc'V (h1 ▸ Z.one_mem)
    rw [hc'eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (comm_mem_commutator_zpowers hw))
      (Subgroup.mem_sup_right hz')
  have hCZbot : C ⊓ Z = ⊥ := by
    rw [inf_comm, hCdef]
    exact inf_conjSubgroup_eq_bot_of_isTI H.ti (hCdef ▸ hCZ)
  have hcard : Nat.card ↥(C ⊔ Z) = Nat.card Z ^ 2 := by
    rw [card_sup_of_comm_inf_bot (fun a ha b hb => SS.abV a (hCV ha) b (SS.ZV hb)) hCZbot,
      IsZConjugate.card_eq hCconj, pow_two]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact hd₁.le)

section Clauses

variable {X : Subgroup G} {x : G}

theorem c4_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂) (hBV : B ≤ V₁)
    (SS : OddSetup M Q Z B V₁ V₂)
    (hL : ∀ (X' : Subgroup G) (x' : G), Sit M Q Z X' x' → x' ∈ Lgen M (LB M Q B))
    (hs : Sit M Q Z X x) : ∀ z' ∈ Z, InZClass Z (x * z') → z' = 1 := by
  intro z' hz' hcl
  by_contra hz1
  have H := hc.hyp
  obtain ⟨A, hA, -, -, hAle, -⟩ := Sit.exists_root_le_two hc hS (Or.inl hBV) SS hL hs
  have hAQ : A ≤ Q := hAle.trans inf_le_left
  have hAX : A ≤ QB X := hAle.trans inf_le_right
  obtain ⟨hAZ, -, -⟩ := lin29_of_sit hs hA hAQ hAX
  have hxA : x ∈ QB A := (IsZConjugate.le_QB_iff H hA hs.conj).mpr hAX hs.mem
  have hZA : z' ∈ QB A := SS.Z_le_QB hA hAQ hz'
  have hZAbot : Z ⊓ A = ⊥ := by
    obtain ⟨g, rfl⟩ := hA
    exact inf_conjSubgroup_eq_bot_of_isTI H.ti hAZ
  obtain ⟨g, hg⟩ := hA
  have hx'Q : g⁻¹ * x * g ∈ Q := by
    rw [hg, QB_conj_eq H g] at hxA
    exact mem_conjSubgroup.mp hxA
  have hz''Q : g⁻¹ * z' * g ∈ Q := by
    rw [hg, QB_conj_eq H g] at hZA
    exact mem_conjSubgroup.mp hZA
  have hxQ : x ∉ Q := hs.notQ
  have hx1 : x ≠ 1 := hs.ne_one
  have hx'1 : g⁻¹ * x * g ≠ 1 := fun h => hx1 (by
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]; group)
  have hz''1 : g⁻¹ * z' * g ≠ 1 := fun h => hz1 (by
    have : z' = g * (g⁻¹ * z' * g) * g⁻¹ := by group
    rw [this, h]; group)
  have hz''Z : g⁻¹ * z' * g ∉ Z := by
    intro h
    apply hz''1
    have hz'A : z' ∈ A := by
      rw [hg, mem_conjSubgroup]; simpa [mul_assoc] using h
    have : z' ∈ Z ⊓ A := ⟨hz', hz'A⟩
    rw [hZAbot, Subgroup.mem_bot] at this
    rw [this]; group
  have hx'cl : InZClass Z (g⁻¹ * x * g) := by
    have := (inZClass_conj_iff (Z := Z) (v := x) g⁻¹).mpr
      (inZClass_of_mem_root hs.conj hs.mem hs.ne_one)
    simpa using this
  have hwcl : InZClass Z (g⁻¹ * x * g * (g⁻¹ * z' * g)) := by
    have := (inZClass_conj_iff (Z := Z) (v := x * z') g⁻¹).mpr hcl
    simpa [mul_assoc] using this
  have hw1 : g⁻¹ * x * g * (g⁻¹ * z' * g) ≠ 1 := by
    intro h
    have h1 : x * z' = 1 := by
      have : x * z' = g * (g⁻¹ * x * g * (g⁻¹ * z' * g)) * g⁻¹ := by group
      rw [this, h]; group
    apply hxQ
    have : x = z'⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact Q.inv_mem (H.Z_normal.1 hz')
  set Y : Subgroup G := conjSubgroup g⁻¹ Z with hYdef
  have hY : IsZConjugate Z Y := ⟨g⁻¹, rfl⟩
  have hz''Y : g⁻¹ * z' * g ∈ Y := by
    rw [hYdef, mem_conjSubgroup]; simpa [mul_assoc] using hz'
  rcases (SS.p31 _ hz''Q hz''1).mp (inZClass_of_mem_root hY hz''Y hz''1) with hV | hV
  · obtain ⟨hYV, hYQ, hYZ⟩ := SS.root_le_V hY hz''Y hV hz''Z
    have hα := (LinSetup.inf_QB_eq_two_of_le hc hS (Or.inl hBV) ⟨H, hY, hYQ, hYZ⟩).1 hYV
    exact c4_core SS hxQ hx'Q hx'1 hz''Q hz''Z hV hx'cl hwcl hw1 (hα ▸ inf_le_right)
  · obtain ⟨hYV, hYQ, hYZ⟩ := SS.symm.root_le_V hY hz''Y hV hz''Z
    have hα := (LinSetup.inf_QB_eq_two_of_le hc hS (Or.inl hBV) ⟨H, hY, hYQ, hYZ⟩).2 hYV
    exact c4_core SS.symm hxQ hx'Q hx'1 hz''Q hz''Z hV hx'cl hwcl hw1 (hα ▸ inf_le_right)

theorem c5_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂) (hBV : B ≤ V₁)
    (SS : OddSetup M Q Z B V₁ V₂)
    (hL : ∀ (X' : Subgroup G) (x' : G), Sit M Q Z X' x' → x' ∈ Lgen M (LB M Q B))
    (hs : Sit M Q Z X x) : (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z := by
  have H := hc.hyp
  have hxL := hL X x hs
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    intro d hd
    have h1 : ⁅x, d⁆ = 1 := by
      rw [commutatorElement_def, hs.QB_comm_X hs.mem hd.2]; group
    obtain ⟨-, e, he, z, hz, rfl⟩ := Sit.comm_eq_one hc hS SS hs hxL hd.1 (h1 ▸ Z.one_mem)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (comm_mem_commutator_zpowers he))
      (Subgroup.mem_sup_right hz)
  · obtain ⟨C₁, -, -, -, hC₁, hC₁Z⟩ := Sit.exists_root_le_two hc hS (Or.inl hBV) SS hL hs
    obtain ⟨C₂, -, -, -, hC₂, hC₂Z⟩ :=
      Sit.exists_root_le_two hc hS.symm (Or.inr hBV) SS.symm hL hs
    have hle₁ : ⁅V₁, Subgroup.zpowers x⁆ ≤ (Q ⊓ QB X) ⊔ Z :=
      le_sup_left.trans (hC₁Z ▸ sup_le_sup_right hC₁ Z)
    have hle₂ : ⁅V₂, Subgroup.zpowers x⁆ ≤ (Q ⊓ QB X) ⊔ Z :=
      le_sup_left.trans (hC₂Z ▸ sup_le_sup_right hC₂ Z)
    refine sup_le ?_ le_sup_right
    rw [Subgroup.commutator_le]
    intro d hd s hs'
    rcases eq_one_or_eq_of_mem_zpowers hs.x_sq hs' with rfl | rfl
    · rw [commutatorElement_one_right]; exact Subgroup.one_mem _
    rw [← commutatorElement_inv]
    refine Subgroup.inv_mem _ ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := SS.dec d hd
    have hdec : ⁅s, a * b⁆ = ⁅s, a⁆ * (⁅s, b⁆ * ⁅⁅s, b⁆⁻¹, a⁆) := by
      simp only [commutatorElement_def]; group
    rw [hdec]
    have hbQ : ⁅s, b⁆ ∈ Q :=
      SS.V'Q (comm_mem_of_normalizes (fun v hv => conj_mem_of_normalizer (SS.normV' s hxL) hv) hb)
    refine Subgroup.mul_mem _ (hle₁ (comm_mem_commutator_zpowers ha))
      (Subgroup.mul_mem _ (hle₂ (comm_mem_commutator_zpowers hb)) (Subgroup.mem_sup_right ?_))
    exact comm_mem_Z H (Q.inv_mem hbQ) (SS.VQ ha)

theorem c7_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂) (SS : OddSetup M Q Z B V₁ V₂)
    (hs : Sit M Q Z X x) (hxL : x ∈ Lgen M (LB M Q B))
    (hc4 : ∀ z' ∈ Z, InZClass Z (x * z') → z' = 1) :
    ∀ g q : G, q ∈ Q → g * x * g⁻¹ = x * q → ∃ q' ∈ Q, g * x * g⁻¹ = q' * x * q'⁻¹ := by
  intro g q hq hgq
  have H := hc.hyp
  have hx2 := hs.x_sq
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hsq : x * q * (x * q) = 1 := by
    rw [← hgq]
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hcomm : ⁅x, q⁆ = (q ^ 2)⁻¹ := by
    have e1 : x * q * x⁻¹ = q⁻¹ := by
      rw [hxi]
      calc x * q * x = (x * q * (x * q)) * q⁻¹ := by group
        _ = q⁻¹ := by rw [hsq, one_mul]
    rw [commutatorElement_def, e1, pow_two, mul_inv_rev]
  have hqZ : ⁅x, q⁆ ∈ Z := by rw [hcomm]; exact Z.inv_mem (sq_mem_Z H hq)
  obtain ⟨-, e, he, z₁, hz₁, hqe⟩ := Sit.comm_eq_one hc hS SS hs hxL hq hqZ
  have hz₁e : z₁ * e⁻¹ = e⁻¹ * z₁ := Z_comm H hz₁ (Q.inv_mem he)
  have hxq : x * q = e * (x * z₁) * e⁻¹ := by
    rw [hqe, commutatorElement_def]
    calc x * (x * e * x⁻¹ * e⁻¹ * z₁) = (x * x) * e * x⁻¹ * (e⁻¹ * z₁) := by group
      _ = e * x * (z₁ * e⁻¹) := by rw [hx2, hxi, ← hz₁e]; group
      _ = e * (x * z₁) * e⁻¹ := by group
  have hcl : InZClass Z (x * z₁) := by
    have h0 : InZClass Z (g * x * g⁻¹) :=
      (inZClass_conj_iff g).mpr (inZClass_of_mem_root hs.conj hs.mem hs.ne_one)
    rw [hgq, hxq] at h0
    exact (inZClass_conj_iff e).mp h0
  have := hc4 z₁ hz₁ hcl
  subst this
  exact ⟨e, he, by rw [hgq, hxq, mul_one]⟩

theorem c8_two (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B 2 V₁ V₂) (hs : Sit M Q Z X x) (hxL : x ∈ Lgen M (LB M Q B))
    (hc7 : ∀ g q : G, q ∈ Q → g * x * g⁻¹ = x * q → ∃ q' ∈ Q, g * x * g⁻¹ = q' * x * q'⁻¹) :
    ∃ K : Subgroup G, K ≤ M ∧ K ⊓ Q = ⊥ ∧ K ⊔ Q = M ∧ ∃ q ∈ Q, q * x * q⁻¹ ∈ K := by
  obtain ⟨K, _, _, _, γ, M₀, gm, c, hcM, ν, hν, hcπ⟩ := lin26Scalar_of_two G M Q Z B V₁ V₂ hb hc hS
  obtain ⟨p, hp, hp2, A, hQA, hAM, hAn, hpow, hAc, c', hcA, hfpf⟩ :=
    exists_scalar_normal_of_scalar hc.hyp gm (Lgen_le_H0 hc) hcM hν hcπ
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ2 : IsPGroup 2 Q := by
    rw [hc.hyp.hQ]
    exact (inSubgroup_pCore_two M).1
  have hxM : x ∈ M := hs.memM
  obtain ⟨K, hKM, hKQ, hKs, hxK⟩ := exists_compl_mem_of_frattini hp2 hQ2 hQA hAM
    hc.hyp.Q_normal.2 hAn hpow hcA hfpf hxM fun a ha => by
      have h1 : x⁻¹ * (a * x * a⁻¹ * x⁻¹) * x⁻¹⁻¹ ∈ Q :=
        conj_mem_Q hc.hyp (M.inv_mem hxM) (hAc a ha x hxL)
      have e : x⁻¹ * (a * x * a⁻¹ * x⁻¹) * x⁻¹⁻¹ = x⁻¹ * a * x * a⁻¹ := by group
      rw [e] at h1
      exact hc7 a _ h1 (by group)
  exact ⟨K, hKM, hKQ, hKs, 1, Q.one_mem, by simpa using hxK⟩

end Clauses

section Tensor

theorem tm_eq_plane (TM : TensorModel M Q Z B) {V : Subgroup G} (hZV : Z ≤ V) (hVQ : V ≤ Q)
    (hN : Lgen M (LB M Q B) ≤ Subgroup.normalizer (V : Set G))
    (hcard : Nat.card V = Nat.card Z ^ 3) : ∃ u : Fin 2 → TM.F, u ≠ 0 ∧ V = TM.plane u := by
  let Y : AddSubgroup (Matrix (Fin 2) (Fin 2) TM.F) :=
    (TM.M₀.img V).comap TM.Φ.symm.toAddMonoidHom
  have hYmem : ∀ X, X ∈ Y ↔ TM.Φ.symm X ∈ TM.M₀.img V := fun X => Iff.rfl
  have hY : ∀ g : Matrix (Fin 2) (Fin 2) TM.F, g.det = 1 → ∀ X ∈ Y, g * X ∈ Y := by
    intro g hg X hX
    obtain ⟨s, hs⟩ := exists_phi_eq' (TM := TM) g hg
    rw [hYmem] at hX ⊢
    obtain ⟨v, hvV, hvQ, hv⟩ := hX
    have hX' : X = TM.Φ (TM.M₀.π v) := by rw [hv, AddEquiv.apply_symm_apply]
    have hsv : (s : G) * v * (s : G)⁻¹ ∈ V := conj_mem_of_normalizer (hN s.2) hvV
    refine ⟨(s : G) * v * (s : G)⁻¹, hsv, hVQ hsv, ?_⟩
    rw [AddEquiv.eq_symm_apply, TM.act s v hvQ, hs, hX']
  have hcard' : Nat.card Y = Nat.card TM.F ^ 2 := by
    have h1 := TM.M₀.card_eq hVQ hZV
    have h2 : Nat.card Y = Nat.card (TM.M₀.img V) :=
      Nat.card_congr (TM.Φ.symm.toEquiv.subtypeEquiv fun X => hYmem X)
    rw [h2, TM.card_F]
    rw [hcard, pow_succ', Nat.mul_comm] at h1
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    rw [Nat.mul_comm (Nat.card Z)] at h1
    exact (Nat.eq_of_mul_eq_mul_right hZpos h1).symm
  obtain ⟨u, hu, hYu⟩ := eq_planeAdd_of_card Y hY hcard'
  refine ⟨u, hu, ?_⟩
  ext y
  rw [TensorModel.mem_plane_iff, ← hYu, hYmem, AddEquiv.symm_apply_apply]
  constructor
  · intro hy
    exact ⟨hVQ hy, (TM.M₀.mem_img_iff hZV (hVQ hy)).mpr hy⟩
  · rintro ⟨hyQ, hy⟩
    exact (TM.M₀.mem_img_iff hZV hyQ).mp hy

theorem eq_one_of_vecMul_eq {F : Type} [Field F] {Hm : Matrix (Fin 2) (Fin 2) F}
    {u₁ u₂ : Fin 2 → F} (hu₁ : u₁ ≠ 0) (hne : ∀ c : F, u₂ ≠ c • u₁) (h₁ : u₁ ᵥ* Hm = u₁)
    (h₂ : u₂ ᵥ* Hm = u₂) : Hm = 1 := by
  have hD := det_ne_zero_of_ne_smul hu₁ hne
  have e : ∀ (u : Fin 2 → F), u ᵥ* Hm = u → ∀ j, u 0 * Hm 0 j + u 1 * Hm 1 j = u j := by
    intro u hu j
    have := congrFun hu j
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using this
  have a0 := e u₁ h₁ 0
  have a1 := e u₁ h₁ 1
  have b0 := e u₂ h₂ 0
  have b1 := e u₂ h₂ 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true]
  · apply mul_left_cancel₀ hD
    linear_combination u₂ 1 * a0 - u₁ 1 * b0
  · apply mul_left_cancel₀ hD
    linear_combination u₂ 1 * a1 - u₁ 1 * b1
  · apply mul_left_cancel₀ hD
    linear_combination u₁ 0 * b0 - u₂ 0 * a0
  · apply mul_left_cancel₀ hD
    linear_combination u₁ 0 * b1 - u₂ 0 * a1

theorem tm_mem_Lgen (TM : TensorModel M Q Z B) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B 2 V₁ V₂) {t : G} (ht : t ∈ H0 M Z) (ht2 : t * t = 1)
    (h₁ : conjSubgroup t V₁ = V₁) (h₂ : conjSubgroup t V₂ = V₂) : t ∈ Lgen M (LB M Q B) := by
  have H := hc.hyp
  obtain ⟨hZ₁, hV₁Q, hZ₂, hV₂Q, hint, -, hN₁, hN₂, hc₁, hc₂⟩ := hS.basic
  obtain ⟨u₁, hu₁, hV₁⟩ := tm_eq_plane TM hZ₁ hV₁Q hN₁ hc₁
  obtain ⟨u₂, hu₂, hV₂⟩ := tm_eq_plane TM hZ₂ hV₂Q hN₂ hc₂
  have hq := H.q4
  have hne : ∀ c : TM.F, u₂ ≠ c • u₁ := by
    intro c hcu
    have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hcu; exact hu₂ hcu
    have h12 : V₁ = V₂ := by rw [hV₁, hV₂, hcu, TensorModel.plane_smul hc0]
    have h1 : V₁ = Z := by rw [← hint, ← h12, inf_idem]
    have e : Nat.card V₁ = Nat.card Z ^ 3 := hc₁
    rw [h1] at e
    have hlt : Nat.card Z ^ 1 < Nat.card Z ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    rw [pow_one, ← e] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨ρ, hρπ, hρ1, -⟩ := exists_actionHom_H0 H TM.gm
  have hTπ : ∀ x ∈ Q, TM.M₀.π (t * x * t⁻¹) = ρ ⟨t, ht⟩ (TM.M₀.π x) :=
    fun x hx => hρπ ⟨t, ht⟩ x hx
  obtain ⟨P, Hm, hP, hH, hform⟩ := exists_matrix_form' (TM := TM) hc ht.1 _ hTπ
  have hformQ : ∀ x ∈ Q, TM.Φ (TM.M₀.π (t * x * t⁻¹)) = P * TM.Φ (TM.M₀.π x) * Hm :=
    fun x hx => by rw [hTπ x hx, hform]
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr (by rw [hP]; exact isUnit_one)
  have hHu : IsUnit Hm := (Matrix.isUnit_iff_isUnit_det Hm).mpr hH
  have heig : ∀ {u : Fin 2 → TM.F}, u ≠ 0 → conjSubgroup t (TM.plane u) = TM.plane u →
      ∃ c : TM.F, c ≠ 0 ∧ u ᵥ* Hm = c • u := by
    intro u hu hconj
    set n : Fin 2 → TM.F := Pi.single 0 1 with hn
    have hn0 : n ≠ 0 := by simp [hn]
    obtain ⟨x, hxQ, hx⟩ := TM.M₀.π_surj (TM.Φ.symm (Matrix.vecMulVec n u))
    have hxp : x ∈ TM.plane u := TensorModel.mem_plane_iff.mpr
      ⟨hxQ, by rw [hx, AddEquiv.apply_symm_apply]; exact vecMulVec_mem_planeAdd n u⟩
    have htx : t * x * t⁻¹ ∈ TM.plane u := by
      rw [← hconj, mem_conjSubgroup]
      simpa [mul_assoc] using hxp
    have h1 := (TensorModel.mem_plane_iff.mp htx).2
    rw [hformQ x hxQ, hx, AddEquiv.apply_symm_apply] at h1
    have h2 : P * Matrix.vecMulVec n u * Hm ∈ planeAdd (u ᵥ* Hm) :=
      (mul_mul_mem_planeAdd_iff (by rw [hP]; exact isUnit_one) hH).mpr
        (vecMulVec_mem_planeAdd n u)
    have hX0 : P * Matrix.vecMulVec n u * Hm ≠ 0 := by
      rw [Ne, hHu.mul_left_eq_zero, hPu.mul_right_eq_zero]
      exact Matrix.vecMulVec_ne_zero hn0 hu
    have huH : u ᵥ* Hm ≠ 0 := by
      intro h0
      apply hu
      obtain ⟨Hi, hHi⟩ := hHu.exists_right_inv
      calc u = u ᵥ* (Hm * Hi) := by rw [hHi, Matrix.vecMul_one]
        _ = 0 := by rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul]
    exact exists_smul_of_ne_zero_mem_planeAdd hu huH hX0 h1 h2
  obtain ⟨c₁, -, hc₁e⟩ := heig hu₁ (by rw [← hV₁]; exact h₁)
  obtain ⟨c₂, -, hc₂e⟩ := heig hu₂ (by rw [← hV₂]; exact h₂)
  have hsq : ∀ X, (P * P) * X * (Hm * Hm) = X := by
    intro X
    obtain ⟨x, hxQ, hx⟩ := TM.M₀.π_surj (TM.Φ.symm X)
    have hX : X = TM.Φ (TM.M₀.π x) := by rw [hx, AddEquiv.apply_symm_apply]
    have h1 := hformQ _ (conj_mem_Q H ht.1 hxQ)
    rw [hformQ x hxQ] at h1
    have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
      calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
        _ = x := by rw [ht2]; group
    rw [e] at h1
    rw [hX]
    conv_rhs => rw [h1]
    simp only [Matrix.mul_assoc]
  have hH2 : Hm * Hm = 1 :=
    eq_one_of_mul_mul_eq' (by rw [Matrix.det_mul, hP, one_mul]) hsq
  have hc1 : ∀ {u : Fin 2 → TM.F} {c : TM.F}, u ≠ 0 → u ᵥ* Hm = c • u → u ᵥ* Hm = u := by
    intro u c hu hcu
    have h1 : u ᵥ* (Hm * Hm) = (c * c) • u := by
      rw [← Matrix.vecMul_vecMul, hcu, Matrix.smul_vecMul, hcu, smul_smul]
    rw [hH2, Matrix.vecMul_one] at h1
    have hcc : c * c = 1 := by
      by_contra hne'
      apply hu
      have : ((c * c) - 1) • u = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
      exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne')
    have : c = 1 := by
      have h2 : c ^ 2 = 1 ^ 2 := by rw [one_pow, pow_two, hcc]
      exact CharTwo.sq_inj.mp h2
    rw [hcu, this, one_smul]
  have hH1 : Hm = 1 := eq_one_of_vecMul_eq hu₁ hne (hc1 hu₁ hc₁e) (hc1 hu₂ hc₂e)
  obtain ⟨s, hs⟩ := exists_phi_eq' (TM := TM) P hP
  have hsH : (s : G) ∈ H0 M Z := Lgen_le_H0 hc s.2
  have hm : (s : G)⁻¹ * t ∈ H0 M Z := (H0 M Z).mul_mem ((H0 M Z).inv_mem hsH) ht
  have hρm : ρ ⟨_, hm⟩ = 1 := by
    refine LinearEquiv.ext fun e => ?_
    obtain ⟨x, hxQ, rfl⟩ := TM.M₀.π_surj e
    rw [← hρπ ⟨_, hm⟩ x hxQ, LinearEquiv.coe_one, id]
    show TM.M₀.π ((s : G)⁻¹ * t * x * ((s : G)⁻¹ * t)⁻¹) = TM.M₀.π x
    apply TM.Φ.injective
    have hwQ : (s : G)⁻¹ * t * x * ((s : G)⁻¹ * t)⁻¹ ∈ Q :=
      conj_mem_Q H (M.mul_mem (M.inv_mem hsH.1) ht.1) hxQ
    have e1 : (s : G) * ((s : G)⁻¹ * t * x * ((s : G)⁻¹ * t)⁻¹) * (s : G)⁻¹ = t * x * t⁻¹ := by
      group
    set w := (s : G)⁻¹ * t * x * ((s : G)⁻¹ * t)⁻¹ with hw
    have h1 := TM.act s w hwQ
    rw [e1, hformQ x hxQ, hH1, Matrix.mul_one, hs] at h1
    exact (hPu.mul_left_cancel h1).symm
  have hmQ : (s : G)⁻¹ * t ∈ Q := (hρ1 ⟨_, hm⟩).mp hρm
  have e : t = (s : G) * ((s : G)⁻¹ * t) := by group
  rw [e]
  exact (Lgen M (LB M Q B)).mul_mem s.2 (Q_le_LgenLB hmQ)

theorem sit_mem_Lgen_two (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B 2 V₁ V₂) :
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → x ∈ Lgen M (LB M Q B) := by
  intro X x hs
  obtain ⟨V₁', V₂', hS', -, h31'⟩ := lin31Statement_holds G M Q Z B 2 V₁ V₂ hb hc hS le_rfl
  have SS := OddSetup.of_linSetup hc hS' h31'
  obtain ⟨-, -, -, -, -, -, -, -, hc₁, hc₂⟩ := hS'.basic
  obtain ⟨h₁, h₂⟩ := Sit.conj_V_eq SS hc₁ hc₂ hs
  obtain ⟨TM⟩ := exists_tensorModel hc hS'
  exact tm_mem_Lgen TM hc hS' ((smith_1_12 hs).1 hs.mem) hs.x_sq h₁ h₂

end Tensor

theorem lin212TwoStatement_holds : Lin212TwoStatement := by
  intro G _ _ M Q Z B V₁ V₂ hb hc hS
  have hL := sit_mem_Lgen_two hb hc hS
  obtain ⟨V₁', V₂', hS', hBV, h31'⟩ := lin31Statement_holds G M Q Z B 2 V₁ V₂ hb hc hS le_rfl
  have SS := OddSetup.of_linSetup hc hS' h31'
  intro X x hs
  have c1 := hL X x hs
  obtain ⟨c2, c3⟩ := hasDimOn_two hc hS hs c1
  have c4 := c4_two hc hS' hBV SS hL hs
  have c7 := c7_two hc hS' SS hs c1 c4
  exact ⟨c1, c2, c3, c4, c5_two hc hS' hBV SS hL hs, cqt_eq_of_class hs c4, c7,
    c8_two hb hc hS hs c1 c7⟩

theorem lin28TwoStatement_holds : Lin28TwoStatement := by
  intro G _ _ M Q Z B V₁ V₂ hb hc hS
  have hL := sit_mem_Lgen_two hb hc hS
  obtain ⟨V₁', V₂', hS', hBV, h31'⟩ := lin31Statement_holds G M Q Z B 2 V₁ V₂ hb hc hS le_rfl
  have SS := OddSetup.of_linSetup hc hS' h31'
  intro X x hs
  obtain ⟨C, hC, -, -, hCle, -⟩ := Sit.exists_root_le_two hc hS' (Or.inl hBV) SS hL hs
  exact ⟨C, hC, hCle⟩

end World

end CFSG.RankThree.GF2n.Smith81
