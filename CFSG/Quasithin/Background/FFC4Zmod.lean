module

public import CFSG.Quasithin.Background.B4ModelsApi

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank Matrix

variable {V : Type*} [CommGroup V]

theorem RealizesVia.secMap {D : FFModel} (hker : D.ker = ⊥) {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    ∃ f : ↥U →* ↥D.sec, Function.Surjective f ∧ (∀ u : ↥U, f u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : D.Gam) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        ((f ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ : ↥D.sec) : D.Amb) =
          D.act γ ((f u : ↥D.sec) : D.Amb) := by
  obtain ⟨_, _, _, _, _, hsec, _, β, hβs, hβk, hβe⟩ := h
  have hqi : Function.Injective (QuotientGroup.mk' (D.ker.subgroupOf D.sec)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hker,
      Subgroup.mem_bot] at hx
    exact Subtype.ext hx
  let Q : ↥D.sec ≃* D.Mod :=
    MulEquiv.ofBijective (QuotientGroup.mk' (D.ker.subgroupOf D.sec))
      ⟨hqi, QuotientGroup.mk'_surjective _⟩
  refine ⟨Q.symm.toMonoidHom.comp β, ?_, ?_, ?_⟩
  · exact Q.symm.surjective.comp hβs
  · intro u
    rw [← hβk u]
    show Q.symm (β u) = 1 ↔ β u = 1
    exact MulEquiv.map_eq_one_iff _
  · intro γ u hu
    set m : ↥D.sec := Q.symm (β u) with hm
    have hm' : β u = QuotientGroup.mk m := by
      rw [hm]
      exact (Q.apply_symm_apply (β u)).symm
    have hact : D.act γ (m : D.Amb) ∈ D.sec := hsec γ m m.2
    have := hβe γ u m hu hact hm'
    show ((Q.symm (β ⟨_, hu⟩) : ↥D.sec) : D.Amb) = D.act γ (m : D.Amb)
    rw [this]
    have : Q.symm (QuotientGroup.mk ⟨D.act γ (m : D.Amb), hact⟩) = ⟨D.act γ (m : D.Amb), hact⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [this]


section Nat

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}

theorem natAct_one_right (γ : ↥Γ) : natAct Γ γ 1 = 1 := by
  simp [natAct]

@[expose] noncomputable def natQuot (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    Multiplicative (ι → K) →* (FFModel.nat Γ).Mod :=
  (QuotientGroup.mk' _).comp (Subgroup.topEquiv.symm.toMonoidHom)

theorem natQuot_injective : Function.Injective (natQuot Γ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 := (QuotientGroup.eq_one_iff _).1 hx
  rw [Subgroup.mem_subgroupOf] at h1
  exact h1

theorem natQuot_surjective : Function.Surjective (natQuot Γ) := by
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨m.1, rfl⟩

theorem realizesVia_nat_of {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥Γ →* ↥H}
    (hπ : Function.Surjective π) (hZU : Z ≤ U)
    (hHU : ∀ h : ↥H, ∀ u ∈ U, (h : MulAut V) u ∈ U)
    (hHZ : ∀ h : ↥H, ∀ z ∈ Z, (h : MulAut V) z ∈ Z) (f : ↥U →* Multiplicative (ι → K))
    (hfs : Function.Surjective f) (hfk : ∀ u : ↥U, f u = 1 ↔ (u : V) ∈ Z)
    (hfe : ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) u ∈ U),
      f ⟨_, hu⟩ = natAct Γ γ (f u)) :
    (FFModel.nat Γ).RealizesVia H U Z π := by
  refine ⟨hπ, hZU, bot_le, hHU, hHZ, fun _ _ _ => trivial, ?_, ?_⟩
  · intro (γ : ↥Γ) (m : Multiplicative (ι → K)) hm
    have hm' : m = 1 := Subgroup.mem_bot.1 hm
    show natAct Γ γ m ∈ (⊥ : Subgroup (Multiplicative (ι → K)))
    rw [hm', natAct_one_right]
    exact Subgroup.one_mem _
  · refine ⟨(natQuot Γ).comp f, natQuot_surjective.comp hfs, fun u => ?_, ?_⟩
    · rw [MonoidHom.comp_apply, ← hfk u]
      exact ⟨fun h => natQuot_injective (h.trans (map_one _).symm), fun h => by
        rw [h, map_one]⟩
    · intro (γ : ↥Γ) u m hu hm hum
      have hm' : (m.1 : Multiplicative (ι → K)) = f u := by
        have : natQuot Γ m.1 = natQuot Γ (f u) := hum.symm
        exact natQuot_injective this
      show natQuot Γ (f ⟨_, hu⟩) = natQuot Γ (natAct Γ γ m.1)
      calc natQuot Γ (f ⟨_, hu⟩) = natQuot Γ (natAct Γ γ (f u)) := congrArg _ (hfe γ u hu)
        _ = natQuot Γ (natAct Γ γ m.1) := by rw [hm']

theorem exists_natMap {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥Γ →* ↥H}
    (h : (FFModel.nat Γ).RealizesVia H U Z π) :
    ∃ f : ↥U →* Multiplicative (ι → K), Function.Surjective f ∧
      (∀ u : ↥U, f u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) u ∈ U),
        f ⟨_, hu⟩ = natAct Γ γ (f u) := by
  obtain ⟨f, hfs, hfk, hfe⟩ := RealizesVia.secMap (D := FFModel.nat Γ) rfl h
  refine ⟨(FFModel.nat Γ).sec.subtype.comp f, fun y => ?_, fun u => ?_, fun γ u hu => hfe γ u hu⟩
  · obtain ⟨u, hu⟩ := hfs ⟨y, trivial⟩
    exact ⟨u, congrArg Subtype.val hu⟩
  · rw [← hfk u]
    exact ⟨fun h1 => Subtype.ext h1, fun h1 => congrArg Subtype.val h1⟩

end Nat


theorem mem_statedSL_zmod {n : ℕ} (x : GL (Fin n) (ZMod 2)) : x ∈ StatedSL n (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSL_zmod_two x

@[expose] noncomputable def ringEquivZModTwo (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) : K ≃+* ZMod 2 :=
  let _ : Fintype K := Fintype.ofFinite K
  FiniteField.ringEquivOfCardEq (by rw [ZMod.card, ← Nat.card_eq_fintype_card, hK])

theorem det_map_symm {K : Type} [Field K] (e : K ≃+* ZMod 2) {n : ℕ} (g : GL (Fin n) (ZMod 2)) :
    ((Matrix.GeneralLinearGroup.map e.symm.toRingHom g : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K).det = 1 := by
  have h1 : ((Matrix.GeneralLinearGroup.map e.symm.toRingHom g : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
        e.symm.toRingHom.mapMatrix (g : Matrix (Fin n) (Fin n) (ZMod 2)) := rfl
  have h2 : (Matrix.GeneralLinearGroup.det g : (ZMod 2)ˣ) = 1 := Subsingleton.elim _ _
  have h3 : (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
    have := congrArg Units.val h2
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  rw [h1, ← RingHom.map_det, h3, map_one]

@[expose] noncomputable def slOfZMod {K : Type} [Field K] (e : K ≃+* ZMod 2) (n : ℕ) :
    ↥(StatedSL n (ZMod 2)) →* ↥(StatedSL n K) where
  toFun g := ⟨Matrix.GeneralLinearGroup.map e.symm.toRingHom (g : GL (Fin n) (ZMod 2)),
    Subgroup.subset_closure (det_map_symm e (g : GL (Fin n) (ZMod 2)))⟩
  map_one' := by ext : 1; exact map_one _
  map_mul' g h := by ext : 1; exact map_mul _ _ _

theorem slOfZMod_coe {K : Type} [Field K] (e : K ≃+* ZMod 2) {n : ℕ}
    (g : ↥(StatedSL n (ZMod 2))) :
    (((slOfZMod e n g : ↥(StatedSL n K)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).map e.symm :=
  rfl

theorem slOfZMod_surjective {K : Type} [Field K] (e : K ≃+* ZMod 2) (n : ℕ) :
    Function.Surjective (slOfZMod e n) := by
  intro g
  refine ⟨⟨Matrix.GeneralLinearGroup.map e.toRingHom (g : GL (Fin n) K),
    mem_statedSL_zmod _⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [slOfZMod_coe]
  ext i j
  simp

@[expose] def vecOfField {K : Type} [Field K] (e : K ≃+* ZMod 2) (n : ℕ) :
    Multiplicative (Fin n → K) →* Multiplicative (Fin n → ZMod 2) where
  toFun x := Multiplicative.ofAdd fun i => e (Multiplicative.toAdd x i)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    simp

theorem vecOfField_surjective {K : Type} [Field K] (e : K ≃+* ZMod 2) (n : ℕ) :
    Function.Surjective (vecOfField e n) := by
  intro y
  refine ⟨Multiplicative.ofAdd fun i => e.symm (Multiplicative.toAdd y i), ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  simp [vecOfField]

theorem vecOfField_eq_one {K : Type} [Field K] (e : K ≃+* ZMod 2) {n : ℕ}
    {x : Multiplicative (Fin n → K)} : vecOfField e n x = 1 ↔ x = 1 := by
  constructor
  · intro h
    apply Multiplicative.toAdd.injective
    funext i
    have := congrFun (congrArg Multiplicative.toAdd h) i
    simpa [vecOfField] using this
  · rintro rfl
    exact map_one _

theorem vecOfField_natAct {K : Type} [Field K] (e : K ≃+* ZMod 2) {n : ℕ}
    (γ : ↥(StatedSL n (ZMod 2))) (x : Multiplicative (Fin n → K)) :
    vecOfField e n (natAct (StatedSL n K) (slOfZMod e n γ) x) =
      natAct (StatedSL n (ZMod 2)) γ (vecOfField e n x) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [vecOfField, natAct, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, slOfZMod_coe]
  rw [← RingHom.coe_coe e, RingHom.map_mulVec]
  congr 1
  ext k l
  simp

theorem realizesVia_zmod {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥(StatedSL n K) →* ↥H}
    (h : (FFModel.nat (StatedSL n K)).RealizesVia H U Z π) :
    (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H U Z
      (π.comp (slOfZMod (ringEquivZModTwo K hK) n)) := by
  set e := ringEquivZModTwo K hK with he
  obtain ⟨f, hfs, hfk, hfe⟩ := exists_natMap h
  refine realizesVia_nat_of (h.1.comp (slOfZMod_surjective e n)) h.2.1 h.2.2.2.1 h.2.2.2.2.1
    ((vecOfField e n).comp f) ((vecOfField_surjective e n).comp hfs) (fun u => ?_)
    (fun γ u hu => ?_)
  · rw [MonoidHom.comp_apply, vecOfField_eq_one, hfk]
  · exact (congrArg (vecOfField e n) (hfe (slOfZMod e n γ) u hu)).trans
      (vecOfField_natAct e γ _)

theorem BinaryNaturalSL.exists_zmod {H : Subgroup (MulAut V)} {U Z : Subgroup V} {n : ℕ}
    (h : BinaryNaturalSL H U Z n 1) :
    ∃ π : ↥(StatedSL n (ZMod 2)) →* ↥H,
      (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H U Z π := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  exact ⟨_, realizesVia_zmod (by simpa using hK) hπ⟩

end FFC

end CFSG.Quasithin
