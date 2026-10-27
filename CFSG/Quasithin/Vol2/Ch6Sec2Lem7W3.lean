module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def dcomm627 (σ : Equiv.Perm (Fin 5)) : Finset (Fin 5 → ZMod 2) :=
  (Finset.univ.filter fun v : Fin 5 → ZMod 2 => ∑ i, v i = 0).image
    fun v => (fun i => v (σ⁻¹ i)) - v

theorem fc_dcomm627 : ∀ s t : Equiv.Perm (Fin 5), s * s = 1 → t * t = 1 → s * t = t * s →
    s ≠ 1 → t ≠ 1 → s ≠ t →
      ((dcomm627 s).card = 4 ∨ (dcomm627 t).card = 4 ∨ (dcomm627 (s * t)).card = 4) ∧
        dcomm627 s ≠ dcomm627 t := by
  decide +kernel

variable {Q : Type} [CommGroup Q]

theorem mem_fixV_zpowers627 {a : MulAut Q} {v : Q} :
    v ∈ fixV (Subgroup.zpowers a) ↔ a v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

@[expose] def commHom627 {U : Subgroup Q} (a : MulAut Q) (hU : ∀ u ∈ U, a u ∈ U) : ↥U →* ↥U where
  toFun u := ⟨a u * (u : Q)⁻¹, U.mul_mem (hU u u.2) (U.inv_mem u.2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem commHom627_apply {U : Subgroup Q} (a : MulAut Q) (hU : ∀ u ∈ U, a u ∈ U) (u : ↥U) :
    ((commHom627 a hU u : ↥U) : Q) = a u * (u : Q)⁻¹ := rfl

theorem false_of_d5_627 [Finite Q] {A : Subgroup (MulAut Q)} {U : Subgroup Q}
    (hA4 : Nat.card A = 4) (hAab : IsElemAbelian2 A)
    (hfix : ∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers a) = fixV A)
    (hcomm : Nat.card (commV A) ≤ 4) (hU : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U)
    (σ : ↥A →* Equiv.Perm (Fin 5)) (hσ : Function.Injective σ) (b : ↥U → Fin 5 → ZMod 2)
    (hbm : ∀ u v, b (u * v) = b u + b v)
    (hβs : ∀ v : Fin 5 → ZMod 2, ∑ i, v i = 0 → ∃ u, b u = v)
    (hβr : ∀ u, ∑ i, b u i = 0)
    (hβe : ∀ (a : ↥A) (u : ↥U) (hu : (a : MulAut Q) (u : Q) ∈ U),
      b ⟨_, hu⟩ = fun i => b u ((σ a)⁻¹ i)) :
    False := by
  classical
  have hbinv : ∀ u, b u⁻¹ = -b u := by
    intro u
    have h1 := hbm u u⁻¹
    rw [mul_inv_cancel] at h1
    have h0 : b 1 = 0 := by
      have := hbm 1 1
      rw [mul_one] at this
      simpa using this
    rw [h0] at h1
    exact (neg_eq_of_add_eq_zero_right h1.symm).symm
  set φ : ↥A → (↥U →* ↥U) := fun a => commHom627 (a : MulAut Q) (hU a a.2) with hφ
  have hker : ∀ a : ↥A, a ≠ 1 → (φ a).ker = (fixV A).subgroupOf U := by
    intro a ha
    have ha' : (a : MulAut Q) ≠ 1 := fun h => ha (Subtype.ext h)
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hfix a a.2 ha', mem_fixV_zpowers627]
    constructor
    · intro h
      have := congrArg Subtype.val h
      rw [hφ, commHom627_apply] at this
      exact mul_inv_eq_one.mp this
    · intro h
      apply Subtype.ext
      rw [hφ, commHom627_apply, h, mul_inv_cancel]
      rfl
  have hcard : ∀ a : ↥A, a ≠ 1 →
      Nat.card (φ a).range * Nat.card ((fixV A).subgroupOf U) = Nat.card U := by
    intro a ha
    rw [← hker a ha, mul_comm]
    exact Subgroup.card_ker_mul_card_range (φ a)
  have hrange : ∀ a : ↥A, (φ a).range ≤ (commV A).subgroupOf U := by
    rintro a _ ⟨u, rfl⟩
    rw [Subgroup.mem_subgroupOf, hφ, commHom627_apply]
    exact Subgroup.subset_closure ⟨a, a.2, u, rfl⟩
  have hW : Nat.card ((commV A).subgroupOf U) ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : ↥((commV A).subgroupOf U) => (⟨((x : ↥U) : Q), x.2⟩ : ↥(commV A))) ?_) hcomm
    intro x y hxy
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
  have hφβ : ∀ (a : ↥A) (u : ↥U), b (φ a u) = (fun i => b u ((σ a)⁻¹ i)) - b u := by
    intro a u
    have e1 : φ a u = ⟨(a : MulAut Q) u, hU a a.2 u u.2⟩ * u⁻¹ := rfl
    rw [e1, hbm, hbinv, hβe a u]
    exact (sub_eq_add_neg _ _).symm
  have himg : ∀ a : ↥A, (dcomm627 (σ a) : Set (Fin 5 → ZMod 2)) =
      b '' ((φ a).range : Set ↥U) := by
    intro a
    ext w
    simp only [dcomm627, Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_image, Set.mem_ofPred_eq, SetLike.mem_coe, MonoidHom.mem_range]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨u, hu⟩ := hβs v hv
      refine ⟨φ a u, ⟨u, rfl⟩, ?_⟩
      rw [hφβ, hu]
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨b u, hβr u, (hφβ a u).symm⟩
  have hle : ∀ a : ↥A, (dcomm627 (σ a)).card ≤ Nat.card (φ a).range := by
    intro a
    rw [← Set.ncard_coe_finset, himg a, ← Nat.card_coe_set_eq]
    exact (Set.ncard_image_le (Set.toFinite _)).trans_eq (Nat.card_coe_set_eq _).symm
  have : Fintype ↥A := Fintype.ofFinite _
  have hcA : Fintype.card ↥A = 4 := by rw [← Nat.card_eq_fintype_card]; exact hA4
  have : Nontrivial ↥A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha1⟩ := exists_ne (1 : ↥A)
  obtain ⟨b, hb1, hba⟩ : ∃ b : ↥A, b ≠ 1 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset ↥A) ⊆ {1, a} := fun x _ => by
      by_cases hx : x = 1
      · simp [hx]
      · simp [hcon x hx]
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (1 : ↥A) {a}
    rw [Finset.card_univ, hcA] at h1
    rw [Finset.card_singleton] at h2
    omega
  have hsq : ∀ x : ↥A, x * x = 1 := fun x => Subtype.ext (by
    have := hAab.2 x x.2
    rw [pow_two] at this
    simpa using this)
  have hcm : ∀ x y : ↥A, x * y = y * x := fun x y => Subtype.ext (hAab.1 x x.2 y y.2)
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hba
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_left (hsq a)]
  obtain ⟨h4, hne⟩ := fc_dcomm627 (σ a) (σ b) (by rw [← map_mul, hsq, map_one])
    (by rw [← map_mul, hsq, map_one]) (by rw [← map_mul, ← map_mul, hcm])
    (fun h => ha1 (hσ (h.trans (map_one σ).symm)))
    (fun h => hb1 (hσ (h.trans (map_one σ).symm))) (fun h => hba (hσ h).symm)
  rw [← map_mul] at h4
  have hk : 0 < Nat.card ((fixV A).subgroupOf U) := Nat.card_pos
  have hcab : ∀ x : ↥A, x ≠ 1 → Nat.card (φ x).range = Nat.card (φ a).range := fun x hx =>
    Nat.eq_of_mul_eq_mul_right hk ((hcard x hx).trans (hcard a ha1).symm)
  have h4' : 4 ≤ Nat.card (φ a).range := by
    rcases h4 with h | h | h
    · exact h ▸ hle a
    · exact (h ▸ hle b).trans (hcab b hb1).le
    · exact (h ▸ hle (a * b)).trans (hcab (a * b) hab1).le
  have heq : ∀ x : ↥A, x ≠ 1 → (φ x).range = (commV A).subgroupOf U := fun x hx =>
    Subgroup.eq_of_le_of_card_ge (hrange x) (hW.trans (h4'.trans (hcab x hx).ge))
  apply hne
  rw [← Finset.coe_inj, himg, himg, heq a ha1, heq b hb1]

theorem zpowers_allOnes_inf_coreMod_five627 :
    Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨k, rfl⟩, hk⟩
  rw [Subgroup.mem_bot]
  have hval : ∀ i, Multiplicative.toAdd ((G6.allOnes 5) ^ k) i = (k : ZMod 2) := by
    intro i
    simp [G6.allOnes, toAdd_zpow]
  have hk' := G6.mem_coreMod.mp hk
  simp only [hval, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hk'
  have hk0 : (k : ZMod 2) = 0 := by
    have h5 : ∀ c : ZMod 2, (5 : ℕ) • c = c := by decide
    rw [← h5 (k : ZMod 2)]
    exact hk'
  apply Multiplicative.toAdd.injective
  funext i
  rw [hval, hk0]
  rfl

theorem altDn_five_ker627 :
    (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec = ⊥ := by
  show (Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5).subgroupOf (G6.coreMod 5) = ⊥
  rw [zpowers_allOnes_inf_coreMod_five627, Subgroup.bot_subgroupOf]

theorem symDn_five_ker627 :
    (FFModel.symDn 5).ker.subgroupOf (FFModel.symDn 5).sec = ⊥ := by
  show (Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5).subgroupOf (G6.coreMod 5) = ⊥
  rw [zpowers_allOnes_inf_coreMod_five627, Subgroup.bot_subgroupOf]

theorem false_of_altD5_627 [Finite Q] {L A : Subgroup (MulAut Q)} {U Z : Subgroup Q}
    (h : AlternatingNatural L U Z 5) (hAL : A ≤ L) (hA4 : Nat.card A = 4)
    (hAab : IsElemAbelian2 A) (hfix : ∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers a) = fixV A)
    (hcomm : Nat.card (commV A) ≤ 4) : False := by
  classical
  obtain ⟨π, hπ⟩ := h
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
  obtain ⟨hsurj, -, -, hUinv, -, -, -, β₀, hβs, -, hβe⟩ := hπ
  set e := MulEquiv.ofBijective π ⟨hinj, hsurj⟩ with he
  set ι := (QuotientGroup.quotientMulEquivOfEq altDn_five_ker627).trans
    (QuotientGroup.quotientBot (G := ↥(FFModel.altDn 5).sec)) with hι
  have hιmk : ∀ m : ↥(FFModel.altDn 5).sec, ι (QuotientGroup.mk m) = m := fun m => rfl
  have hmkι : ∀ x, QuotientGroup.mk (ι x) = x := fun x => by
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hιmk]
  set b : ↥U → Fin 5 → ZMod 2 := fun u =>
    Multiplicative.toAdd (show G6.PermMod 5 from (ι (β₀ u)).1) with hb
  set σ : ↥A →* Equiv.Perm (Fin 5) :=
    (alternatingGroup (Fin 5)).subtype.comp (e.symm.toMonoidHom.comp (Subgroup.inclusion hAL))
    with hσ
  have hσi : Function.Injective σ := by
    intro x y hxy
    exact Subgroup.inclusion_injective hAL (e.symm.injective (Subtype.ext hxy))
  refine false_of_d5_627 hA4 hAab hfix hcomm (fun a ha u hu => hUinv ⟨a, hAL ha⟩ u hu) σ hσi b
    (fun u v => ?_) (fun v hv => ?_) (fun u => G6.mem_coreMod.mp (ι (β₀ u)).2)
    (fun a u hu => ?_)
  · show Multiplicative.toAdd (show G6.PermMod 5 from (ι (β₀ (u * v))).1) = _
    rw [map_mul, map_mul]
    rfl
  · obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨Multiplicative.ofAdd v, G6.mem_coreMod.mpr hv⟩)
    refine ⟨u, ?_⟩
    show Multiplicative.toAdd (show G6.PermMod 5 from (ι (β₀ u)).1) = v
    rw [hu, hιmk]
    rfl
  · set γ := e.symm ⟨a, hAL a.2⟩ with hγ
    have hπγ : π γ = ⟨a, hAL a.2⟩ := e.apply_symm_apply _
    have hu' : ((π γ : ↥L) : MulAut Q) (u : Q) ∈ U := by
      rw [hπγ]
      exact hu
    have h1 := hβe γ u (ι (β₀ u)) hu' (G6.permAct_mem_coreMod _ (ι (β₀ u)).2) (hmkι _).symm
    have h2 : (⟨(a : MulAut Q) u, hu⟩ : ↥U) = ⟨_, hu'⟩ := by
      apply Subtype.ext
      show (a : MulAut Q) u = ((π γ : ↥L) : MulAut Q) u
      rw [hπγ]
    show Multiplicative.toAdd (show G6.PermMod 5 from (ι (β₀ ⟨(a : MulAut Q) u, hu⟩)).1) = _
    rw [h2, h1, hιmk]
    rfl

theorem false_of_symD5_627 [Finite Q] {J A : Subgroup (MulAut Q)} {U Z : Subgroup Q}
    (h : SymmetricNatural J U Z 5) (hAJ : A ≤ J) (hA4 : Nat.card A = 4)
    (hAab : IsElemAbelian2 A) (hfix : ∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers a) = fixV A)
    (hcomm : Nat.card (commV A) ≤ 4) : False := by
  classical
  obtain ⟨π, hπ⟩ := h
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.symDn_faithful (by norm_num)) hπ
  obtain ⟨hsurj, -, -, hUinv, -, -, -, β₀, hβs, -, hβe⟩ := hπ
  set e := MulEquiv.ofBijective π ⟨hinj, hsurj⟩ with he
  set ι := (QuotientGroup.quotientMulEquivOfEq symDn_five_ker627).trans
    (QuotientGroup.quotientBot (G := ↥(FFModel.symDn 5).sec)) with hι
  have hιmk : ∀ m : ↥(FFModel.symDn 5).sec, ι (QuotientGroup.mk m) = m := fun m => rfl
  have hmkι : ∀ x, QuotientGroup.mk (ι x) = x := fun x => by
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hιmk]
  set b : ↥U → Fin 5 → ZMod 2 := fun u =>
    Multiplicative.toAdd (show G6.PermMod 5 from (ι (β₀ u)).1) with hb
  set σ : ↥A →* Equiv.Perm (Fin 5) := e.symm.toMonoidHom.comp (Subgroup.inclusion hAJ) with hσ
  have hσi : Function.Injective σ := fun x y hxy =>
    Subgroup.inclusion_injective hAJ (e.symm.injective hxy)
  refine false_of_d5_627 hA4 hAab hfix hcomm (fun a ha u hu => hUinv ⟨a, hAJ ha⟩ u hu) σ hσi b
    (fun u v => ?_) (fun v hv => ?_) (fun u => G6.mem_coreMod.mp (ι (β₀ u)).2)
    (fun a u hu => ?_)
  · show Multiplicative.toAdd (show G6.PermMod 5 from (ι (β₀ (u * v))).1) = _
    rw [map_mul, map_mul]
    rfl
  · obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨Multiplicative.ofAdd v, G6.mem_coreMod.mpr hv⟩)
    refine ⟨u, ?_⟩
    show Multiplicative.toAdd (show G6.PermMod 5 from (ι (β₀ u)).1) = v
    rw [hu, hιmk]
    rfl
  · set γ := e.symm ⟨a, hAJ a.2⟩ with hγ
    have hπγ : π γ = ⟨a, hAJ a.2⟩ := e.apply_symm_apply _
    have hu' : ((π γ : ↥J) : MulAut Q) (u : Q) ∈ U := by
      rw [hπγ]
      exact hu
    have h1 := hβe γ u (ι (β₀ u)) hu' (G6.permAct_mem_coreMod _ (ι (β₀ u)).2) (hmkι _).symm
    have h2 : (⟨(a : MulAut Q) u, hu⟩ : ↥U) = ⟨_, hu'⟩ := by
      apply Subtype.ext
      show (a : MulAut Q) u = ((π γ : ↥J) : MulAut Q) u
      rw [hπγ]
    show Multiplicative.toAdd (show G6.PermMod 5 from (ι (β₀ ⟨(a : MulAut Q) u, hu⟩)).1) = _
    rw [h2, h1, hιmk]
    rfl

end CFSG.Quasithin.H13
