module

public import CFSG.Quasithin.MS93.S4Stmt
public import CFSG.Quasithin.MS93.Sec2Basic
public import CFSG.Quasithin.MS93.ML3Facts
public import CFSG.Quasithin.MS93.ML3Bridge

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix commutatorElement

section Transport

variable {G G' : Type} [Group G] [Group G'] {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
  [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {dual : Bool} {k : ℕ}

theorem isSumOfNaturalModulesVia_of_equiv {K V Z : Subgroup G} {K' V' Z' : Subgroup G'}
    {φ : ↥K →* ↥Γ} (h : IsSumOfNaturalModulesVia K V Z φ dual k) (eK : ↥K' ≃* ↥K)
    (eV : ↥V' ≃* ↥V) (hK' : K' ≤ Subgroup.normalizer (V' : Set G')) (hZ' : Z' ≤ V')
    (hZ : ∀ v : ↥V', (v : G') ∈ Z' ↔ ((eV v : ↥V) : G) ∈ Z)
    (hconj : ∀ (a : ↥K') (u v : ↥V'), (v : G') = a * u * a⁻¹ →
      ((eV v : ↥V) : G) = (eK a : G) * eV u * (eK a : G)⁻¹) :
    IsSumOfNaturalModulesVia K' V' Z' (φ.comp eK.toMonoidHom) dual k := by
  obtain ⟨-, -, β, hβs, hβk, hβeq⟩ := h
  refine ⟨hK', hZ', β.comp eV.toMonoidHom, hβs.comp eV.surjective, ?_, ?_⟩
  · ext v
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker,
      hβk, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hZ]
  · intro a u v huv i
    exact hβeq (eK a) (eV u) (eV v) (hconj a u v huv) i

theorem isSumOfNaturalModulesVia_map {K V Z : Subgroup G} {φ : ↥K →* ↥Γ}
    (h : IsSumOfNaturalModulesVia K V Z φ dual k) (e : G →* G') (he : Function.Injective e) :
    IsSumOfNaturalModulesVia (K.map e) (V.map e) (Z.map e)
      (φ.comp (K.equivMapOfInjective e he).symm.toMonoidHom) dual k := by
  have hKV := h.1
  have hZV := h.2.1
  refine isSumOfNaturalModulesVia_of_equiv h (K.equivMapOfInjective e he).symm
    (V.equivMapOfInjective e he).symm ?_ (Subgroup.map_mono hZV) ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨a * v * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hKV ha) v).mp hv, by simp⟩
    · rintro ⟨w, hw, hwx⟩
      refine ⟨a⁻¹ * w * a, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hKV (K.inv_mem ha)) w).mp hw
        simpa using this
      · rw [map_mul, map_mul, map_inv, hwx]
        group
  · rintro ⟨v, hv⟩
    obtain ⟨w, hw, rfl⟩ := hv
    have hsymm : ((V.equivMapOfInjective e he).symm ⟨e w, ⟨w, hw, rfl⟩⟩ : ↥V) = ⟨w, hw⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hsymm]
    exact ⟨fun ⟨z, hz, hzw⟩ => he hzw ▸ hz, fun hz => ⟨w, hz, rfl⟩⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, u, hu, rfl⟩ ⟨_, v, hv, rfl⟩ huv
    have hsa : ((K.equivMapOfInjective e he).symm ⟨e a, ⟨a, ha, rfl⟩⟩ : ↥K) = ⟨a, ha⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have hsu : ((V.equivMapOfInjective e he).symm ⟨e u, ⟨u, hu, rfl⟩⟩ : ↥V) = ⟨u, hu⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have hsv : ((V.equivMapOfInjective e he).symm ⟨e v, ⟨v, hv, rfl⟩⟩ : ↥V) = ⟨v, hv⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hsa, hsu, hsv]
    apply he
    simpa using huv

theorem isSumOfNaturalModulesVia_subgroupOf {K V Z M : Subgroup G} {φ : ↥K →* ↥Γ}
    (h : IsSumOfNaturalModulesVia K V Z φ dual k) (hK : K ≤ M) (hV : V ≤ M) :
    IsSumOfNaturalModulesVia (K.subgroupOf M) (V.subgroupOf M) (Z.subgroupOf M)
      (φ.comp (Subgroup.subgroupOfEquivOfLe hK).toMonoidHom) dual k := by
  have hKV := h.1
  have hZV := h.2.1
  refine isSumOfNaturalModulesVia_of_equiv h (Subgroup.subgroupOfEquivOfLe hK)
    (Subgroup.subgroupOfEquivOfLe hV) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := Subgroup.mem_normalizer_iff.mp (hKV (Subgroup.mem_subgroupOf.mp ha)) (x : G)
    simpa using this
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hZV (Subgroup.mem_subgroupOf.mp hx))
  · intro v
    rfl
  · intro a u v huv
    simpa using congrArg Subtype.val huv

end Transport

section Coord

variable {G : Type} [Group G] {K V : Subgroup G} {F : Type} [Field F]
  {φ : ↥K →* ↥(StatedSL 3 F)}

@[expose] def oneCoordEquiv : Multiplicative (Fin 1 → Fin 3 → F) ≃* Multiplicative (Fin 3 → F) :=
  AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (Fin 3 → F))

theorem toAdd_oneCoordEquiv (m : Multiplicative (Fin 1 → Fin 3 → F)) :
    Multiplicative.toAdd (oneCoordEquiv m) = Multiplicative.toAdd m 0 :=
  rfl

@[expose] noncomputable def natCoord (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) :
    ↥V ≃* Multiplicative (Fin 3 → F) :=
  (MulEquiv.ofBijective (Classical.choose h.2.2)
      ⟨by
        rw [← MonoidHom.ker_eq_bot_iff, (Classical.choose_spec h.2.2).2.1, Subgroup.bot_subgroupOf],
        (Classical.choose_spec h.2.2).1⟩).trans oneCoordEquiv

theorem natCoord_conj (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (a : ↥K) (u v : ↥V)
    (huv : (v : G) = a * u * a⁻¹) :
    Multiplicative.toAdd (natCoord h v) =
      ((φ a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Multiplicative.toAdd (natCoord h u) := by
  have := (Classical.choose_spec h.2.2).2.2 a u v huv 0
  simpa [natCoord, toAdd_oneCoordEquiv, moduleAct] using this

theorem card_eq_of_natural [Finite F] (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) :
    Nat.card ↥V = Nat.card F ^ 3 := by
  rw [Nat.card_congr (natCoord h).toEquiv]
  change Nat.card (Fin 3 → F) = _
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

theorem conj_eq_iff_of_natural (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (a : ↥K)
    (u : ↥V) :
    (a : G) * u * (a : G)⁻¹ = u ↔
      ((φ a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Multiplicative.toAdd (natCoord h u) = Multiplicative.toAdd (natCoord h u) := by
  have hmem : (a : G) * u * (a : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (h.1 a.2) u).mp u.2
  rw [← natCoord_conj h a u ⟨_, hmem⟩ rfl]
  constructor
  · intro he
    congr 2
    exact Subtype.ext he
  · intro he
    have : (⟨_, hmem⟩ : ↥V) = u :=
      (natCoord h).injective (Multiplicative.toAdd.injective he)
    exact congrArg Subtype.val this

end Coord

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem exists_natural_Uloc (h : PUHyp M T L) (hφ : IsSL3FullVia M T L φ)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    ∃ ψ : ↥(stab (puAmalgam h.le) δ) →* ↥(StatedSL 3 F), Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (stab (puAmalgam h.le) δ) (Uloc h.le L δ) ⊥ ψ false 1 := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  obtain ⟨-, hφs, -, -, hnat⟩ := hφ
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hn : ((Uq M T L).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUM).2 (le_normalizer_Uq h.le_normalizer)
  set e : ↥M →* (puAmalgam h.le).Universal :=
    (MulAut.conj g).toMonoidHom.comp (puAmalgam h.le).ofA with he
  have hei : Function.Injective e :=
    (MulAut.conj g).injective.comp (puAmalgam h.le).ofA_injective
  have h1 := isSumOfNaturalModulesVia_map
    (isSumOfNaturalModulesVia_subgroupOf hnat le_rfl hUM) e hei
  have hstab : stab (puAmalgam h.le) (g • baseA _) = (M.subgroupOf M).map e := by
    rw [stab_smul, puAmalgam.stab_baseA, imM, Subgroup.map_map]
  have hU : Uloc h.le L (g • baseA _) = ((Uq M T L).subgroupOf M).map e := by
    rw [Uloc, puTrans_smul_baseA hn, imM, Subgroup.map_map]
  have hbot : ((⊥ : Subgroup G).subgroupOf M).map e = ⊥ := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h1
  refine ⟨_, ?_, isSumOfNaturalModulesVia_of_equiv h1 (MulEquiv.subgroupCongr hstab)
    (MulEquiv.subgroupCongr hU) (stab_le_normalizer_puTrans h.le hn _) bot_le
    (fun v => Iff.rfl) (fun a u v huv => huv)⟩
  exact (hφs.comp (MulEquiv.surjective _)).comp ((MulEquiv.surjective _).comp
    (MulEquiv.surjective _))

end Vertex

section Dictionary

variable {G : Type} [Group G] {K V : Subgroup G} {F : Type} [Field F]
  {φ : ↥K →* ↥(StatedSL 3 F)}

@[expose] noncomputable def natImage (φ : ↥K →* ↥(StatedSL 3 F)) (A : Subgroup G) :
    Subgroup (SL3 F) :=
  (A.subgroupOf K).map (toSL3 φ)

theorem mem_natImage {A : Subgroup G} {g : SL3 F} :
    g ∈ natImage φ A ↔ ∃ a : ↥K, (a : G) ∈ A ∧ toSL3 φ a = g := by
  simp only [natImage, Subgroup.mem_map, Subgroup.mem_subgroupOf]

@[expose] noncomputable def natVec (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (v : ↥V) :
    Fin 3 → F :=
  Multiplicative.toAdd (natCoord h v)

theorem natVec_injective (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) :
    Function.Injective (natVec h) :=
  fun _ _ he => (natCoord h).injective (Multiplicative.toAdd.injective he)

theorem natVec_surjective (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) :
    Function.Surjective (natVec h) := fun x =>
  ⟨(natCoord h).symm (Multiplicative.ofAdd x), by simp [natVec]⟩

theorem natVec_bijective (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) :
    Function.Bijective (natVec h) :=
  ⟨natVec_injective h, natVec_surjective h⟩

theorem natVec_mul (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (v w : ↥V) :
    natVec h (v * w) = natVec h v + natVec h w := by
  simp [natVec]

theorem natVec_inv (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (v : ↥V) :
    natVec h v⁻¹ = - natVec h v := by
  simp [natVec]

theorem natVec_one (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) : natVec h 1 = 0 := by
  simp [natVec]

theorem toSL3_mat (a : ↥K) :
    ((toSL3 φ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      ((φ a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
  coe_toSL3 φ a

theorem natVec_conj (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (a : ↥K) (u v : ↥V)
    (huv : (v : G) = a * u * a⁻¹) :
    natVec h v = ((toSL3 φ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec h u := by
  rw [toSL3_mat]
  exact natCoord_conj h a u v huv

theorem natVec_commutator (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (a : ↥K) (v w : ↥V)
    (hw : (w : G) = ⁅(v : G), (a : G)⁆) :
    natVec h w = natVec h v - ((toSL3 φ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec h v := by
  have hmem : (a : G) * v * (a : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (h.1 a.2) v).mp v.2
  have hw' : w = v * (⟨_, hmem⟩ : ↥V)⁻¹ := by
    apply Subtype.ext
    rw [hw, commutatorElement_def]
    simp [mul_assoc]
  rw [hw', natVec_mul, natVec_inv, natVec_conj h a v ⟨_, hmem⟩ rfl, sub_eq_add_neg]

theorem commute_iff_natVec (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (a : ↥K) (v : ↥V) :
    (a : G) * v = v * a ↔
      ((toSL3 φ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec h v = natVec h v := by
  rw [toSL3_mat]
  unfold natVec
  rw [← conj_eq_iff_of_natural h a v]
  constructor
  · intro hc
    rw [hc, mul_inv_cancel_right]
  · intro hc
    calc (a : G) * v = (a : G) * v * (a : G)⁻¹ * a := by group
      _ = v * a := by rw [hc]

theorem card_inf_centralizer_eq (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1)
    {A : Subgroup G} (hA : A ≤ K) :
    Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) = Nat.card ↥(fixN (natImage φ A)) := by
  let e1 : ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≃
      {v : ↥V // (v : G) ∈ Subgroup.centralizer (A : Set G)} :=
    { toFun := fun x => ⟨⟨x, x.2.1⟩, x.2.2⟩
      invFun := fun x => ⟨x.1, x.1.2, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : {v : ↥V // (v : G) ∈ Subgroup.centralizer (A : Set G)} ≃
      {x : Fin 3 → F // x ∈ fixN (natImage φ A)} := by
    refine Equiv.subtypeEquiv (Equiv.ofBijective (natVec h)
      (natVec_bijective h)) fun v => ?_
    simp only [Equiv.ofBijective_apply]
    rw [Subgroup.mem_centralizer_iff, mem_fixN]
    constructor
    · intro hv g hg
      obtain ⟨a, haA, rfl⟩ := mem_natImage.mp hg
      exact (commute_iff_natVec h a v).mp (hv _ haA)
    · intro hv a haA
      have := hv _ (mem_natImage.mpr ⟨⟨a, hA haA⟩, haA, rfl⟩)
      exact (commute_iff_natVec h ⟨a, hA haA⟩ v).mpr this
  rw [Nat.card_congr (e1.trans e2)]

theorem card_commutator_eq (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1)
    {A : Subgroup G} (hA : A ≤ K) :
    Nat.card ↥⁅V, A⁆ = Nat.card ↥(commN (natImage φ A)) := by
  have hVA : ⁅V, A⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp (hA.trans h.1)
  have key : ∀ v : ↥V, (v : G) ∈ ⁅V, A⁆ ↔ natVec h v ∈ commN (natImage φ A) := by
    intro v
    constructor
    · intro hv
      have hp : ∀ y ∈ ⁅V, A⁆, ∃ hy : y ∈ V, natVec h ⟨y, hy⟩ ∈ commN (natImage φ A) := by
        intro y hy
        rw [Subgroup.commutator_def] at hy
        induction hy using Subgroup.closure_induction with
        | mem y hy =>
          obtain ⟨v, hv, a, ha, rfl⟩ := hy
          have hmem : ⁅v, a⁆ ∈ V := hVA (Subgroup.commutator_mem_commutator hv ha)
          refine ⟨hmem, ?_⟩
          rw [natVec_commutator h ⟨a, hA ha⟩ ⟨v, hv⟩ ⟨_, hmem⟩ rfl]
          have hg : toSL3 φ ⟨a, hA ha⟩ ∈ natImage φ A := mem_natImage.mpr ⟨_, ha, rfl⟩
          have := sub_mem_commN hg (natVec h ⟨v, hv⟩)
          rw [← neg_sub]
          exact Submodule.neg_mem _ this
        | one =>
          refine ⟨V.one_mem, ?_⟩
          rw [show (⟨1, V.one_mem⟩ : ↥V) = 1 from rfl, natVec_one]
          exact Submodule.zero_mem _
        | mul a b _ _ iha ihb =>
          obtain ⟨ha, ha'⟩ := iha
          obtain ⟨hb, hb'⟩ := ihb
          refine ⟨V.mul_mem ha hb, ?_⟩
          rw [show (⟨a * b, V.mul_mem ha hb⟩ : ↥V) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, natVec_mul]
          exact Submodule.add_mem _ ha' hb'
        | inv a _ iha =>
          obtain ⟨ha, ha'⟩ := iha
          refine ⟨V.inv_mem ha, ?_⟩
          rw [show (⟨a⁻¹, V.inv_mem ha⟩ : ↥V) = (⟨a, ha⟩ : ↥V)⁻¹ from rfl, natVec_inv]
          exact Submodule.neg_mem _ ha'
      obtain ⟨_, hv'⟩ := hp v hv
      exact hv'
    · intro hv
      have hcl : natVec h v ∈ (commN (natImage φ A)).toAddSubgroup := hv
      rw [commN_eq_closure] at hcl
      have hp : ∀ x ∈ AddSubgroup.closure {y | ∃ g ∈ natImage φ A, ∃ x : Fin 3 → F,
          ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x = y},
          ∀ w : ↥V, natVec h w = x → (w : G) ∈ ⁅V, A⁆ := by
        intro x hx
        induction hx using AddSubgroup.closure_induction with
        | mem y hy =>
          intro w hw
          obtain ⟨g, hg, x, rfl⟩ := hy
          obtain ⟨a, haA, rfl⟩ := mem_natImage.mp hg
          obtain ⟨u, rfl⟩ := natVec_surjective h x
          have hmem : ⁅(u : G), (a : G)⁆ ∈ V := hVA (Subgroup.commutator_mem_commutator u.2 haA)
          have hc := natVec_commutator h a u ⟨_, hmem⟩ rfl
          have hw' : w = (⟨_, hmem⟩ : ↥V)⁻¹ := by
            apply natVec_injective h
            rw [hw, natVec_inv, hc, neg_sub]
          rw [hw']
          exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator u.2 haA)
        | zero =>
          intro w hw
          have : w = 1 := natVec_injective h (by rw [hw, natVec_one])
          rw [this]
          exact Subgroup.one_mem _
        | add x y _ _ ihx ihy =>
          intro w hw
          obtain ⟨u, hu⟩ := natVec_surjective h x
          obtain ⟨u', hu'⟩ := natVec_surjective h y
          have : w = u * u' := natVec_injective h (by rw [hw, natVec_mul, hu, hu'])
          rw [this]
          exact Subgroup.mul_mem _ (ihx u hu) (ihy u' hu')
        | neg x _ ihx =>
          intro w hw
          obtain ⟨u, hu⟩ := natVec_surjective h x
          have : w = u⁻¹ := natVec_injective h (by rw [hw, natVec_inv, hu])
          rw [this]
          exact Subgroup.inv_mem _ (ihx u hu)
      exact hp _ hcl v rfl
  let e1 : ↥⁅V, A⁆ ≃ {v : ↥V // (v : G) ∈ ⁅V, A⁆} :=
    { toFun := fun x => ⟨⟨x, hVA x.2⟩, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : {v : ↥V // (v : G) ∈ ⁅V, A⁆} ≃ {x : Fin 3 → F // x ∈ commN (natImage φ A)} :=
    Equiv.subtypeEquiv (Equiv.ofBijective (natVec h) (natVec_bijective h))
      fun v => key v
  rw [Nat.card_congr (e1.trans e2)]

theorem toSL3_eq_one_iff (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (a : ↥K) :
    toSL3 φ a = 1 ↔ ∀ v ∈ V, (a : G) * v * (a : G)⁻¹ = v := by
  constructor
  · intro ha v hv
    refine (conj_eq_iff_of_natural h a ⟨v, hv⟩).mpr ?_
    rw [← toSL3_mat, ha]
    simp
  · intro ha
    refine eq_one_of_mulVec_eq_self fun x => ?_
    obtain ⟨v, rfl⟩ := natVec_surjective h x
    exact ((commute_iff_natVec h a v).mp (by
      have := ha v v.2
      calc (a : G) * v = (a : G) * v * (a : G)⁻¹ * a := by group
        _ = v * a := by rw [this])).trans rfl

theorem card_natImage_mul (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) {A : Subgroup G}
    (hA : A ≤ K) :
    Nat.card ↥(natImage φ A) * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card ↥A := by
  set f : ↥(A.subgroupOf K) →* SL3 F := (toSL3 φ).comp (A.subgroupOf K).subtype with hf
  have hrange : f.range = natImage φ A := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : Nat.card f.ker = Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : ↥(A.subgroupOf K)) : ↥K), Subgroup.mem_subgroupOf.mp x.1.2,
          Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
        invFun := fun y => ⟨⟨⟨y, hA y.2.1⟩, Subgroup.mem_subgroupOf.mpr y.2.1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · set c : G := (((x : ↥(A.subgroupOf K)) : ↥K) : G) with hc
      have h1 : c * v * c⁻¹ = v := by simpa [hc] using (toSL3_eq_one_iff h _).mp x.2 v hv
      calc v * c = c * v * c⁻¹ * c := by rw [h1]
        _ = c * v := by group
    · rw [MonoidHom.mem_ker]
      refine (toSL3_eq_one_iff h ⟨y, hA y.2.1⟩).mpr fun v hv => ?_
      have := Subgroup.mem_centralizer_iff.mp y.2.2 v hv
      rw [← this, mul_inv_cancel_right]
  have hA' : Nat.card ↥(A.subgroupOf K) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  rw [← hrange, ← hker, mul_comm, Subgroup.card_ker_mul_card_range, hA']

end Dictionary

end CFSG.Quasithin.MS93
