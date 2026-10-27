module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivKindFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivKindConj
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivKindGrp
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G] {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
  {m : ℕ} {L0 : Type} [Group L0]

private noncomputable def qTwoLMDivKindCard_diagOf {g : GL (Fin m) F0} (hg : ggIsDiagMat g) :
    Fin m → F0 := Classical.choose hg

omit [Finite F0] [CharP F0 2] in
private theorem qTwoLMDivKindCard_diagOf_spec {g : GL (Fin m) F0} (hg : ggIsDiagMat g) :
    (g : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal (qTwoLMDivKindCard_diagOf hg) :=
  Classical.choose_spec hg

omit [Finite F0] [CharP F0 2] in
private theorem qTwoLMDivKindCard_card_diagSet (hF : Nat.card F0 = 4) (hm : 1 ≤ m) :
    Nat.card {e : Fin m → F0ˣ // e ⟨0, hm⟩ = 1} = 3 ^ (m - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hcard : Nat.card F0ˣ = 3 := by
    rw [Nat.card_units, hF]
  change Nat.card {e : Fin (n + 1) → F0ˣ // e 0 = 1} = 3 ^ n
  let e : {e : Fin (n + 1) → F0ˣ // e 0 = 1} ≃ (Fin n → F0ˣ) :=
  { toFun := fun x => Fin.tail x.val
    invFun := fun f => ⟨Fin.cons 1 f, by simp⟩
    left_inv := by
      intro x
      apply Subtype.ext
      have h := Fin.cons_self_tail x.val
      rw [x.property] at h
      exact h
    right_inv := by
      intro f
      simp }
  rw [Nat.card_congr e, Nat.card_fun]
  simp [hcard]

private theorem qTwoLMDivKindCard_rho_eq_of_diag_eq {E : Type} [Group E]
    (hm : 1 ≤ m)
    (πSU : Su F0 2 1 m →* L0) (hπ_surj : Function.Surjective πSU) (ρ : E →* MulAut L0)
    (gOf : E → GL (Fin m) F0) (dOf : E → Fin m → F0)
    (hdOf : ∀ b, (gOf b : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal (dOf b))
    (hdOf_ne_zero : ∀ b i, dOf b i ≠ 0)
    (hpropOf : ∀ (b : E) (u : Su F0 2 1 m), ∃ u' : Su F0 2 1 m,
      (u' : GL (Fin m) F0) = gOf b * (u : GL (Fin m) F0) * (gOf b)⁻¹ ∧
        ρ b (πSU u) = πSU u')
    {b b' : E}
    (hd_eq : ∀ i, dOf b i / dOf b ⟨0, hm⟩ = dOf b' i / dOf b' ⟨0, hm⟩) :
    ρ b = ρ b' := by
  let c : F0 := dOf b ⟨0, hm⟩ / dOf b' ⟨0, hm⟩
  have hd_scaled : ∀ i, dOf b i = c * dOf b' i := by
    intro i
    have h1 := hd_eq i
    have h2 : dOf b ⟨0, hm⟩ = c * dOf b' ⟨0, hm⟩ := by
      dsimp [c]
      rw [div_mul_cancel₀ _ (hdOf_ne_zero b' ⟨0, hm⟩)]
    calc dOf b i = dOf b ⟨0, hm⟩ * (dOf b i / dOf b ⟨0, hm⟩) := by
          rw [mul_div_cancel₀ _ (hdOf_ne_zero b ⟨0, hm⟩)]
      _ = (c * dOf b' ⟨0, hm⟩) * (dOf b' i / dOf b' ⟨0, hm⟩) := by rw [h1, h2]
      _ = c * dOf b' i := by
          rw [mul_assoc, mul_div_cancel₀ _ (hdOf_ne_zero b' ⟨0, hm⟩)]
  have hc : c ≠ 0 := div_ne_zero (hdOf_ne_zero b ⟨0, hm⟩) (hdOf_ne_zero b' ⟨0, hm⟩)
  let cUnit : F0ˣ := Units.mk0 c hc
  let sUnit : GL (Fin m) F0 := Matrix.GeneralLinearGroup.scalar (Fin m) cUnit
  have hsUnit_val : (sUnit : Matrix (Fin m) (Fin m) F0) = Matrix.scalar (Fin m) c := by
    simp [sUnit, cUnit, Matrix.GeneralLinearGroup.coe_scalar]
  have hg_eq : gOf b = sUnit * gOf b' := by
    apply Units.ext
    rw [Units.val_mul, hsUnit_val, hdOf b, hdOf b']
    have hscalar : Matrix.scalar (Fin m) c = Matrix.diagonal (fun _ => c) := rfl
    rw [hscalar, Matrix.diagonal_mul_diagonal]
    apply Matrix.ext
    intro i j
    simp [Matrix.diagonal_apply, hd_scaled i]
  have hsUnit_center : sUnit ∈ Subgroup.center (GL (Fin m) F0) := by
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    exact ⟨c, hsUnit_val.symm⟩
  have hconj_eq : ∀ u : Su F0 2 1 m, gOf b * (u : GL (Fin m) F0) * (gOf b)⁻¹ =
      gOf b' * (u : GL (Fin m) F0) * (gOf b')⁻¹ := by
    intro u
    have hc := Subgroup.mem_center_iff.mp hsUnit_center
      (gOf b' * (u : GL (Fin m) F0) * (gOf b')⁻¹)
    rw [hg_eq]
    calc _ = sUnit * (gOf b' * (u : GL (Fin m) F0) * (gOf b')⁻¹) * sUnit⁻¹ := by group
      _ = _ := by rw [← hc, mul_inv_cancel_right]
  ext x
  obtain ⟨u, rfl⟩ := hπ_surj x
  have h1 := (hpropOf b u).choose_spec
  have h2 := (hpropOf b' u).choose_spec
  have h3 : ((hpropOf b u).choose : GL (Fin m) F0) =
      ((hpropOf b' u).choose : GL (Fin m) F0) := by
    rw [h1.1, h2.1]
    exact hconj_eq u
  rw [h1.2, h2.2, Subtype.ext h3]

theorem qTwoLMDivKind_card_range_le {E : Type} [Group E] (hF : Nat.card F0 = 4) (hm : 1 ≤ m)
    (πSU : Su F0 2 1 m →* L0) (hπ_surj : Function.Surjective πSU) (ρ : E →* MulAut L0)
    (hdiag : ∀ b : E, ∃ g : GL (Fin m) F0, ggIsDiagMat g ∧
      ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
        (u' : GL (Fin m) F0) = g * (u : GL (Fin m) F0) * g⁻¹ ∧ ρ b (πSU u) = πSU u') :
    Nat.card ρ.range ≤ 3 ^ (m - 1) := by
  classical
  let S := {e : Fin m → F0ˣ // e ⟨0, hm⟩ = 1}
  have hS_card : Nat.card S = 3 ^ (m - 1) := qTwoLMDivKindCard_card_diagSet hF hm
  let gOf (b : E) : GL (Fin m) F0 := Classical.choose (hdiag b)
  have hgOf (b : E) : ggIsDiagMat (gOf b) := (Classical.choose_spec (hdiag b)).1
  let dOf (b : E) : Fin m → F0 := qTwoLMDivKindCard_diagOf (hgOf b)
  have hdOf (b : E) : (gOf b : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal (dOf b) :=
    qTwoLMDivKindCard_diagOf_spec (hgOf b)
  have hpropOf (b : E) : ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
      (u' : GL (Fin m) F0) = gOf b * (u : GL (Fin m) F0) * (gOf b)⁻¹ ∧ ρ b (πSU u) = πSU u' :=
    (Classical.choose_spec (hdiag b)).2
  have hdOf_ne_zero (b : E) (i : Fin m) : dOf b i ≠ 0 := by
    have h_unit : IsUnit (gOf b : Matrix (Fin m) (Fin m) F0) := (gOf b).isUnit
    have h_diag : IsUnit (Matrix.diagonal (dOf b)) := by
      rw [← hdOf b]
      exact h_unit
    have h_vec_unit : IsUnit (dOf b) := by
      rw [← Matrix.isUnit_diagonal]
      exact h_diag
    exact IsUnit.ne_zero (h_vec_unit.apply i)
  let eOf (b : E) : S :=
    ⟨fun i => Units.mk0 (dOf b i / dOf b ⟨0, hm⟩)
        (div_ne_zero (hdOf_ne_zero b i) (hdOf_ne_zero b ⟨0, hm⟩)),
     by simp [div_self, hdOf_ne_zero b ⟨0, hm⟩]⟩
  have h_e_eq_implies_rho_eq : ∀ b b' : E, eOf b = eOf b' → ρ b = ρ b' := by
    intro b b' h
    have hd_eq : ∀ i, dOf b i / dOf b ⟨0, hm⟩ = dOf b' i / dOf b' ⟨0, hm⟩ := by
      intro i
      have := congrArg (fun x : S => (x.val i : F0)) h
      simpa [eOf, Units.ext_iff] using this
    exact qTwoLMDivKindCard_rho_eq_of_diag_eq hm πSU hπ_surj ρ gOf dOf hdOf hdOf_ne_zero
      hpropOf hd_eq
  let F : ρ.range → S := fun φ => eOf (Classical.choose (MonoidHom.mem_range.mp φ.2))
  have hF_inj : Function.Injective F := by
    intro φ ψ h
    have hφ : ρ (Classical.choose (MonoidHom.mem_range.mp φ.2)) = φ.1 :=
      Classical.choose_spec (MonoidHom.mem_range.mp φ.2)
    have hψ : ρ (Classical.choose (MonoidHom.mem_range.mp ψ.2)) = ψ.1 :=
      Classical.choose_spec (MonoidHom.mem_range.mp ψ.2)
    have hρ : ρ (Classical.choose (MonoidHom.mem_range.mp φ.2)) =
        ρ (Classical.choose (MonoidHom.mem_range.mp ψ.2)) :=
      h_e_eq_implies_rho_eq _ _ h
    rw [hφ, hψ] at hρ
    exact Subtype.ext hρ
  calc Nat.card ρ.range ≤ Nat.card S := Nat.card_le_card_of_injective (f := F) hF_inj
    _ = 3 ^ (m - 1) := hS_card

omit [Finite G] in
private theorem qTwoLMDivKindCard_card_ker_gamma {Bs L : Subgroup G} {x : G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : ∀ b : ↥Bs, ggGamma L hN b = 1 ↔ (b : G) ∈ Subgroup.zpowers x) (hx : x ∈ Bs)
    (hx3 : orderOf x = 3) : Nat.card (ggGamma L hN).ker = 3 := by
  have hle : Subgroup.zpowers x ≤ Bs := Subgroup.zpowers_le.mpr hx
  have e : (ggGamma L hN).ker ≃ Subgroup.zpowers x :=
    { toFun := fun b => ⟨(b.1 : G), (hker b.1).mp b.2⟩
      invFun := fun y => ⟨⟨y.1, hle y.2⟩, (hker ⟨y.1, hle y.2⟩).mpr y.2⟩
      left_inv := fun b => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_zpowers, hx3]

omit [Finite G] in
theorem qTwoLMDivKind_card_le {Bs L : Subgroup G} {x : G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hperf : commutator ↥L = ⊤)
    (hker : ∀ b : ↥Bs, ggGamma L hN b = 1 ↔ (b : G) ∈ Subgroup.zpowers x) (hx : x ∈ Bs)
    (hx3 : orderOf x = 3) (hF : Nat.card F0 = 4) (hm : 1 ≤ m) (c : ↥L →* L0)
    (hc_ker : c.ker ≤ Subgroup.center ↥L) (πSU : Su F0 2 1 m →* L0)
    (hπ_surj : Function.Surjective πSU) (ρ : ↥Bs →* MulAut L0)
    (hdiag : ∀ b : ↥Bs, ∃ g : GL (Fin m) F0, ggIsDiagMat g ∧
      ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
        (u' : GL (Fin m) F0) = g * (u : GL (Fin m) F0) * g⁻¹ ∧ ρ b (πSU u) = πSU u')
    (hρ : ∀ (b : ↥Bs) (l : ↥L),
      c ⟨(b : G) * l * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hN b.2) l).mp l.2⟩ =
        ρ b (c l)) :
    Nat.card Bs ≤ 3 ^ m := by
  let γ := ggGamma L hN
  have hγker : Nat.card γ.ker = 3 := qTwoLMDivKindCard_card_ker_gamma hN hker hx hx3
  have hρker_le : ρ.ker ≤ γ.ker := by
    intro b hb
    have hb' : ρ b = 1 := MonoidHom.mem_ker.mp hb
    show ggGamma L hN b = 1
    rw [ggGamma_eq_one_iff]
    apply qTwoLMDivKind_mem_centralizer_of_map_conj c hperf hc_ker (hN b.2)
    intro l
    have h := hρ b l
    rw [hb'] at h
    simpa using h
  have hγcard : Nat.card γ.ker * Nat.card γ.range = Nat.card Bs :=
    Subgroup.card_ker_mul_card_range γ
  have hρcard : Nat.card ρ.ker * Nat.card ρ.range = Nat.card Bs :=
    Subgroup.card_ker_mul_card_range ρ
  have hγrange_le : Nat.card γ.range ≤ Nat.card ρ.range := by
    have hk_dvd : Nat.card ρ.ker ∣ Nat.card γ.ker := Subgroup.card_dvd_of_le hρker_le
    rw [hγker] at hk_dvd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hk_dvd with hk1 | hk3
    · rw [hγker] at hγcard
      rw [hk1, one_mul] at hρcard
      omega
    · rw [hγker] at hγcard
      rw [hk3] at hρcard
      omega
  have hρrange : Nat.card ρ.range ≤ 3 ^ (m - 1) :=
    qTwoLMDivKind_card_range_le hF hm πSU hπ_surj ρ hdiag
  calc
    Nat.card Bs = Nat.card γ.ker * Nat.card γ.range := hγcard.symm
    _ = 3 * Nat.card γ.range := by rw [hγker]
    _ ≤ 3 * Nat.card ρ.range := Nat.mul_le_mul_left 3 hγrange_le
    _ ≤ 3 * 3 ^ (m - 1) := Nat.mul_le_mul_left 3 hρrange
    _ = 3 ^ m := by rw [← pow_succ', Nat.sub_add_cancel hm]

private theorem qTwoLMDivKindCard_map_diag_le {B Bs L : Subgroup G} (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hF : Nat.card F0 = 4) (c : ↥L →* L0)
    (hc_surj : Function.Surjective c) (hc_ker : c.ker ≤ Subgroup.center ↥L)
    (hc_two : IsPGroup 2 c.ker) (πSU : Su F0 2 1 m →* L0) (ρ : ↥Bs →* MulAut L0)
    (hdiag : ∀ b : ↥Bs, ∃ g : GL (Fin m) F0, ggIsDiagMat g ∧
      ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
        (u' : GL (Fin m) F0) = g * (u : GL (Fin m) F0) * g⁻¹ ∧ ρ b (πSU u) = πSU u')
    (hρ : ∀ (b : ↥Bs) (l : ↥L),
      c ⟨(b : G) * l * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hN b.2) l).mp l.2⟩ =
        ρ b (c l)) :
    Nat.card ((qTwoLMDivKind_diag F0 m).map πSU) ≤ Nat.card (Bs.subgroupOf L) := by
  have hT0_le : (qTwoLMDivKind_diag F0 m).map πSU ≤ (Bs.subgroupOf L).map c := by
    intro w hw
    obtain ⟨u, hu, hwu⟩ := Subgroup.mem_map.mp hw
    have hw3 : w ^ 3 = 1 := by
      rw [← hwu, ← map_pow, qTwoLMDivKind_pow_three_of_mem_diag hF hu, map_one]
    obtain ⟨t, ht3, hct⟩ := qTwoLMDivKind_exists_lift_cube c hc_surj hc_two hw3
    have htBs : (t : G) ∈ Bs :=
      qTwoLMDivKind_mem_of_cube hBs hN c hc_ker hc_two πSU ρ hdiag hρ ht3 hu
        (hwu.trans hct.symm)
    exact Subgroup.mem_map.mpr ⟨t, by rwa [Subgroup.mem_subgroupOf], hct⟩
  have hfin : Finite ↥((Bs.subgroupOf L).map c) :=
    Finite.of_surjective (c.subgroupMap (Bs.subgroupOf L))
      (MonoidHom.subgroupMap_surjective c (Bs.subgroupOf L))
  have h1 : Nat.card ((qTwoLMDivKind_diag F0 m).map πSU) ≤
      Nat.card ((Bs.subgroupOf L).map c) :=
    @Subgroup.card_le_of_le _ _ _ ((Bs.subgroupOf L).map c) hfin hT0_le
  have h2 : Nat.card ((Bs.subgroupOf L).map c) ≤ Nat.card (Bs.subgroupOf L) :=
    Nat.le_of_dvd (Nat.card_pos_iff.mpr ⟨⟨⟨1, Subgroup.one_mem _⟩⟩, inferInstance⟩)
      (Subgroup.card_map_dvd (H := Bs.subgroupOf L) c)
  exact h1.trans h2

private theorem qTwoLMDivKindCard_card_diag_map (hF : Nat.card F0 = 4) (hm : 4 ≤ m)
    (πSU : Su F0 2 1 m →* L0) (hπ_ker : πSU.ker ≤ Subgroup.center (Su F0 2 1 m)) :
    Nat.card ((qTwoLMDivKind_diag F0 m).map πSU) * Nat.card πSU.ker = 3 ^ (m - 1) := by
  have hker_le_diag : πSU.ker ≤ qTwoLMDivKind_diag F0 m :=
    hπ_ker.trans (qTwoLMDivKind_center_le_diag hF (by omega))
  have h := Subgroup.card_ker_mul_card_range (πSU.domRestrict (qTwoLMDivKind_diag F0 m))
  rw [MonoidHom.ker_domRestrict] at h
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le_diag).toEquiv] at h
  rw [MonoidHom.domRestrict_range, qTwoLMDivKind_card_diag hF (by omega)] at h
  rw [mul_comm] at h
  exact h

omit [Finite G] in
private theorem qTwoLMDivKindCard_subgroupOf_card (Bs L : Subgroup G) :
    Nat.card (L.subgroupOf Bs) = Nat.card (Bs.subgroupOf L) := by
  rw [← Subgroup.inf_subgroupOf_left L Bs, ← Subgroup.inf_subgroupOf_right Bs L]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]

private theorem qTwoLMDivKindCard_ker_card (hF : Nat.card F0 = 4) (hm : 4 ≤ m)
    (πSU : Su F0 2 1 m →* L0) (hπ_ker : πSU.ker ≤ Subgroup.center (Su F0 2 1 m))
    (hker_dvd : Nat.card πSU.ker ∣ 3 ^ (m - 1)) (hker_ne_bot : πSU.ker ≠ ⊥) :
    Nat.card πSU.ker = 3 := by
  have hker_card_le : Nat.card πSU.ker ≤ 3 :=
    (Subgroup.card_le_of_le hπ_ker).trans (qTwoLMDivKind_card_center_le hF (by omega))
  have hker_card_ne_one : Nat.card πSU.ker ≠ 1 := by
    intro h
    apply hker_ne_bot
    rw [Subgroup.eq_bot_iff_card]
    exact h
  obtain ⟨k, _hk_le, hk_eq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hker_dvd
  have hk_le_one : k ≤ 1 := by
    have h : 3 ^ k ≤ 3 ^ 1 := by
      calc
        3 ^ k = Nat.card πSU.ker := hk_eq.symm
        _ ≤ 3 := hker_card_le
        _ = 3 ^ 1 := by norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    apply hker_card_ne_one
    rw [hk_eq, hk0]
    norm_num
  have hk1 : k = 1 := by omega
  rw [hk_eq, hk1]
  norm_num

private theorem qTwoLMDivKindCard_ker_eq_center (hF : Nat.card F0 = 4) (hm : 4 ≤ m)
    (πSU : Su F0 2 1 m →* L0) (hπ_ker : πSU.ker ≤ Subgroup.center (Su F0 2 1 m))
    (hker_card : Nat.card πSU.ker = 3) :
    πSU.ker = Subgroup.center (Su F0 2 1 m) := by
  apply Subgroup.eq_of_le_of_card_ge hπ_ker
  rw [hker_card]
  exact qTwoLMDivKind_card_center_le hF (by omega)

omit [Finite G] in
private theorem qTwoLMDivKindCard_x_not_mem {B Bs L : Subgroup G} {x : G}
    (hBs : GGBstar 3 B Bs) (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hF : Nat.card F0 = 4) (hm : 4 ≤ m)
    (c : ↥L →* L0) (hc_surj : Function.Surjective c) (hc_two : IsPGroup 2 c.ker)
    (πSU : Su F0 2 1 m →* L0) (hπ_surj : Function.Surjective πSU)
    (hπ_ker : πSU.ker ≤ Subgroup.center (Su F0 2 1 m))
    (hker_eq_center : πSU.ker = Subgroup.center (Su F0 2 1 m)) :
    x ∉ L := by
  intro hxL
  let x' : ↥L := ⟨x, hxL⟩
  have hx'_center : x' ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    change (l : G) * x = x * (l : G)
    exact (Subgroup.mem_centralizer_iff.mp (hLx l.2) x (Set.mem_singleton x)).symm
  have hcx'_center : c x' ∈ Subgroup.center L0 := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨l, rfl⟩ := hc_surj y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx'_center l]
  obtain ⟨s, hs⟩ := hπ_surj (c x')
  have hs_center : s ∈ Subgroup.center (Su F0 2 1 m) :=
    qTwoLMDivKind_mem_center_of_map hF hm hπ_ker (hs ▸ hcx'_center)
  have hs_ker : s ∈ πSU.ker := by
    rw [hker_eq_center]
    exact hs_center
  have hcx'_one : c x' = 1 := by
    rw [← hs, MonoidHom.mem_ker.mp hs_ker]
  have hx'_ker : x' ∈ c.ker := MonoidHom.mem_ker.mpr hcx'_one
  have hx'3 : x' ^ 3 = 1 := by
    apply Subtype.ext
    change x ^ 3 = 1
    exact hBs.2.1.2 x hx
  have hcop : (orderOf x').Coprime 3 := by
    have h := hc_two.orderOf_coprime (by norm_num : Nat.Coprime 2 3) ⟨x', hx'_ker⟩
    rwa [← Subgroup.orderOf_coe (⟨x', hx'_ker⟩ : c.ker)] at h
  have hdvd : orderOf x' ∣ 3 := orderOf_dvd_of_pow_eq_one hx'3
  have hone : orderOf x' = 1 := Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdvd
  exact hx1 (congrArg Subtype.val (orderOf_eq_one_iff.mp hone))

private theorem qTwoLMDivKindCard_index_ge_three {B Bs L : Subgroup G} {x : G}
    (hBs : GGBstar 3 B Bs) (hx : x ∈ Bs) (hx_not_mem_L : x ∉ L) :
    3 ≤ (L.subgroupOf Bs).index := by
  have hLsub_ne_top : L.subgroupOf Bs ≠ ⊤ := by
    intro htop
    apply hx_not_mem_L
    have hmem : (⟨x, hx⟩ : ↥Bs) ∈ L.subgroupOf Bs := by
      rw [htop]
      exact Subgroup.mem_top _
    rwa [Subgroup.mem_subgroupOf] at hmem
  have hBs_p : IsPGroup 3 Bs := fun g => ⟨1, Subtype.ext (by simpa using hBs.2.1.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hBs_p.exists_card_eq
  have hI_gt_one : 1 < (L.subgroupOf Bs).index :=
    Subgroup.one_lt_index_of_ne_top hLsub_ne_top
  have hI_dvd : (L.subgroupOf Bs).index ∣ Nat.card Bs :=
    Subgroup.card_quotient_dvd_card _
  rw [hk] at hI_dvd
  obtain ⟨j, _hj_le, hj_eq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hI_dvd
  have hj_pos : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj
    · rw [hj_eq, hj0] at hI_gt_one
      norm_num at hI_gt_one
    · exact hj
  rw [hj_eq]
  calc
    3 = 3 ^ 1 := by norm_num
    _ ≤ 3 ^ j := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mpr hj_pos

theorem qTwoLMDivKind_le_card {B Bs L : Subgroup G} {x : G} (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hF : Nat.card F0 = 4) (hm : 4 ≤ m)
    (c : ↥L →* L0) (hc_surj : Function.Surjective c) (hc_ker : c.ker ≤ Subgroup.center ↥L)
    (hc_two : IsPGroup 2 c.ker) (πSU : Su F0 2 1 m →* L0) (hπ_surj : Function.Surjective πSU)
    (hπ_ker : πSU.ker ≤ Subgroup.center (Su F0 2 1 m)) (ρ : ↥Bs →* MulAut L0)
    (hdiag : ∀ b : ↥Bs, ∃ g : GL (Fin m) F0, ggIsDiagMat g ∧
      ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
        (u' : GL (Fin m) F0) = g * (u : GL (Fin m) F0) * g⁻¹ ∧ ρ b (πSU u) = πSU u')
    (hρ : ∀ (b : ↥Bs) (l : ↥L),
      c ⟨(b : G) * l * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hN b.2) l).mp l.2⟩ =
        ρ b (c l)) :
    3 ^ (m - 1) ≤ Nat.card Bs := by
  let T0 := (qTwoLMDivKind_diag F0 m).map πSU
  have hT0_card_le : Nat.card T0 ≤ Nat.card (Bs.subgroupOf L) :=
    qTwoLMDivKindCard_map_diag_le hBs hN hF c hc_surj hc_ker hc_two πSU ρ hdiag hρ
  have hcard_subgroupOf : Nat.card (L.subgroupOf Bs) = Nat.card (Bs.subgroupOf L) :=
    qTwoLMDivKindCard_subgroupOf_card Bs L
  have hT0_card : Nat.card T0 * Nat.card πSU.ker = 3 ^ (m - 1) :=
    qTwoLMDivKindCard_card_diag_map hF hm πSU hπ_ker
  by_cases hker_bot : πSU.ker = ⊥
  · rw [hker_bot, Subgroup.card_bot, mul_one] at hT0_card
    calc
      3 ^ (m - 1) = Nat.card T0 := hT0_card.symm
      _ ≤ Nat.card (Bs.subgroupOf L) := hT0_card_le
      _ ≤ Nat.card Bs := by
        rw [← Subgroup.inf_subgroupOf_right Bs L]
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
        exact Subgroup.card_le_of_le inf_le_left
  · have hker_card : Nat.card πSU.ker = 3 :=
      qTwoLMDivKindCard_ker_card hF hm πSU hπ_ker (Dvd.intro_left _ hT0_card) hker_bot
    have hx_not_mem_L : x ∉ L :=
      qTwoLMDivKindCard_x_not_mem hBs hx hx1 hLx hF hm c hc_surj hc_two πSU hπ_surj hπ_ker
        (qTwoLMDivKindCard_ker_eq_center hF hm πSU hπ_ker hker_card)
    have h3 : 3 ^ (m - 1) = 3 ^ (m - 2) * 3 := by
      rw [← pow_succ, show m - 2 + 1 = m - 1 by omega]
    rw [hker_card, h3] at hT0_card
    have hT0_lower : 3 ^ (m - 2) ≤ Nat.card (L.subgroupOf Bs) := by
      rw [hcard_subgroupOf, ← Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3) hT0_card]
      exact hT0_card_le
    calc
      3 ^ (m - 1) = 3 ^ (m - 2) * 3 := h3
      _ ≤ Nat.card (L.subgroupOf Bs) * (L.subgroupOf Bs).index :=
        Nat.mul_le_mul hT0_lower (qTwoLMDivKindCard_index_ge_three hBs hx hx_not_mem_L)
      _ = Nat.card Bs := Subgroup.card_mul_index (L.subgroupOf Bs)

end CFSG.StandardType.QTwo

end
