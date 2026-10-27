module

public import CFSG.SignalizerFunctorTheorem.NonLocal.ModuleOfV
public import CFSG.Quasithin.Background.MulAutTwo
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Background.E1Sec7
public import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.SignalizerFunctorTheorem.Quadratic
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[instance_reducible]
private noncomputable def commGroupOfComm'' {A : Type*} [Group A]
    (hc : ∀ a b : A, a * b = b * a) : CommGroup A :=
  { (inferInstance : Group A) with mul_comm := hc }

@[instance_reducible]
private noncomputable def elemTwoModule'' {A : Type*} [Group A]
    (hc : ∀ a b : A, a * b = b * a) (hp : ∀ a : A, a ^ 2 = 1) :
    letI := commGroupOfComm'' hc
    Module (ZMod 2) (Additive A) :=
  letI := commGroupOfComm'' hc
  AddCommMonoid.zmodModule fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hp (Additive.toMul x)

structure ModDataE (J E : Subgroup G) where
  W : Type
  [addCommGroup : AddCommGroup W]
  [module : Module (ZMod 2) W]
  [finite : Finite W]
  ρ : ↥J →* LGL 2 W
  ι : G → W
  ι_mul : ∀ e ∈ E, ∀ e' ∈ E, ι (e * e') = ι e + ι e'
  ι_surj : ∀ w : W, ∃ e ∈ E, ι e = w
  ι_eq_zero : ∀ e ∈ E, ι e = 0 → e = 1
  ρ_ι : ∀ j : ↥J, ∀ e ∈ E, ρ j (ι e) = ι ((j : G) * e * (j : G)⁻¹)
  le_normalizer : J ≤ normalizer (E : Set G)

attribute [instance] ModDataE.addCommGroup ModDataE.module ModDataE.finite

theorem exists_modDataE {J E : Subgroup G} (hE : IsElemAbelian 2 E)
    (hJ : J ≤ normalizer (E : Set G)) : Nonempty (ModDataE J E) := by
  classical
  let hc : ∀ a b : ↥E, a * b = b * a := fun a b => Subtype.ext (hE.comm a.2 b.2)
  let hp : ∀ a : ↥E, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hE.2 a.1 a.2)
  letI : CommGroup ↥E := commGroupOfComm'' hc
  letI : Module (ZMod 2) (Additive ↥E) := elemTwoModule'' hc hp
  let ι : G → Additive ↥E := fun g => if hg : g ∈ E then Additive.ofMul ⟨g, hg⟩ else 0
  have hι_of : ∀ (g : G) (hg : g ∈ E), ι g = Additive.ofMul (⟨g, hg⟩ : ↥E) := fun g hg =>
    dif_pos hg
  have hnorm : ∀ j : ↥J, ∀ v ∈ E, (J.subtype j : G) * v * (J.subtype j : G)⁻¹ ∈ E :=
    fun j v hv => (Subgroup.mem_normalizer_iff.mp (hJ j.2) v).1 hv
  let ρ : ↥J →* LGL 2 (Additive ↥E) :=
    (CFSG.Quasithin.MulAutTwo.linEquiv (V := ↥E)).toMonoidHom.comp
      (CFSG.SignalizerFunctorTheorem.NonLocal.conjHom J.subtype E hnorm)
  refine ⟨⟨Additive ↥E, ρ, ι, ?_, ?_, ?_, ?_, hJ⟩⟩
  · intro e he e' he'
    rw [hι_of (e * e') (E.mul_mem he he'), hι_of e he, hι_of e' he', ← ofMul_mul]
    rfl
  · intro w
    refine ⟨(Additive.toMul w : ↥E), (Additive.toMul w : ↥E).2, ?_⟩
    rw [hι_of _ (Additive.toMul w : ↥E).2, ofMul_toMul]
  · intro e he h
    have h1 : (⟨e, he⟩ : ↥E) = 1 := ofMul_eq_zero.mp (by rwa [hι_of e he] at h)
    exact congrArg Subtype.val h1
  · intro j e he
    show (CFSG.Quasithin.MulAutTwo.linEquiv
      (CFSG.SignalizerFunctorTheorem.NonLocal.conjHom J.subtype E hnorm j)) (ι e) = _
    rw [CFSG.Quasithin.MulAutTwo.linEquiv_apply, hι_of e he]
    show Additive.ofMul ((CFSG.SignalizerFunctorTheorem.NonLocal.conjHom J.subtype E hnorm j)
      ⟨e, he⟩) = _
    rw [hι_of ((j : G) * e * (j : G)⁻¹) (hnorm j e he)]
    rfl

namespace ModDataE

variable {J E : Subgroup G} (M : ModDataE J E)

theorem ι_one : M.ι 1 = 0 := by
  have h := M.ι_mul 1 E.one_mem 1 E.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem ι_inv {e : G} (he : e ∈ E) : M.ι e⁻¹ = - M.ι e := by
  have h := M.ι_mul e he e⁻¹ (E.inv_mem he)
  rw [mul_inv_cancel, M.ι_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem ι_injOn {e e' : G} (he : e ∈ E) (he' : e' ∈ E) (h : M.ι e = M.ι e') : e = e' := by
  have h1 : M.ι (e * e'⁻¹) = 0 := by
    rw [M.ι_mul e he e'⁻¹ (E.inv_mem he'), M.ι_inv he', h]
    exact add_neg_cancel _
  have h2 := M.ι_eq_zero _ (E.mul_mem he (E.inv_mem he')) h1
  exact mul_inv_eq_one.mp h2

@[expose] def img (S : Subgroup G) : Subgroup (LGL 2 M.W) :=
  (S.subgroupOf J).map M.ρ

theorem mem_img {S : Subgroup G} {r : LGL 2 M.W} :
    r ∈ M.img S ↔ ∃ j : ↥J, (j : G) ∈ S ∧ M.ρ j = r := by
  unfold img
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨h, hh, e⟩ => ⟨h, hh, e⟩, fun ⟨h, hh, e⟩ => ⟨h, hh, e⟩⟩

theorem ρ_eq_one_iff (j : ↥J) : M.ρ j = 1 ↔ (j : G) ∈ centralizer (E : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hn : (j : G) * e * (j : G)⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.1 (M.le_normalizer j.2) e).1 he
    have h1 : M.ι ((j : G) * e * (j : G)⁻¹) = M.ι e := by
      rw [← M.ρ_ι j e he, h]
      rfl
    have h2 := M.ι_injOn hn he h1
    calc e * (j : G) = ((j : G) * e * (j : G)⁻¹) * (j : G) := by rw [h2]
      _ = (j : G) * e := by group
  · intro h
    ext w
    obtain ⟨e, he, rfl⟩ := M.ι_surj w
    rw [M.ρ_ι j e he]
    have h1 : e * (j : G) = (j : G) * e := Subgroup.mem_centralizer_iff.1 h e he
    have h2 : (j : G) * e * (j : G)⁻¹ = e := by rw [← h1]; group
    rw [h2]
    rfl

theorem card_img {S : Subgroup G} (hS : S ≤ J) :
    Nat.card (M.img S) = (centralizer (E : Set G)).relIndex S := by
  have hker : M.ρ.ker = (centralizer (E : Set G)).subgroupOf J := by
    ext j
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact M.ρ_eq_one_iff j
  unfold img
  rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hS]

include M in
theorem commutator_le_E {A : Subgroup G} (hA : A ≤ J) : ⁅E, A⁆ ≤ E := by
  refine Subgroup.commutator_le.2 fun e he a ha => ?_
  have h1 : a * e⁻¹ * a⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.1 (M.le_normalizer (hA ha)) e⁻¹).1 (E.inv_mem he)
  have : ⁅e, a⁆ = e * (a * e⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
  rw [this]
  exact E.mul_mem he h1

theorem ι_commutator {j : G} (hj : j ∈ J) {e : G} (he : e ∈ E) :
    M.ι ⁅j, e⁆ = M.ρ ⟨j, hj⟩ (M.ι e) - M.ι e := by
  have hn : j * e * j⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 (M.le_normalizer hj) e).1 he
  have h1 := M.ι_mul _ hn e⁻¹ (E.inv_mem he)
  have h2 : M.ρ ⟨j, hj⟩ (M.ι e) = M.ι (j * e * j⁻¹) := M.ρ_ι ⟨j, hj⟩ e he
  rw [M.ι_inv he, ← h2] at h1
  rw [commutatorElement_def, h1, sub_eq_add_neg]

theorem mem_commSub_img_iff {A : Subgroup G} (hA : A ≤ J) {e : G} (he : e ∈ E) :
    M.ι e ∈ commSub (M.img A) ↔ e ∈ ⁅E, A⁆ := by
  have hEA : ⁅E, A⁆ ≤ E := M.commutator_le_E hA
  constructor
  · intro h
    have key : ∀ w ∈ commSub (M.img A), ∃ e' ∈ ⁅E, A⁆, M.ι e' = w := by
      intro w hw
      refine Submodule.span_induction (p := fun w _ => ∃ e' ∈ ⁅E, A⁆, M.ι e' = w) ?_ ?_ ?_ ?_ hw
      · rintro w ⟨r, hr, v, rfl⟩
        obtain ⟨j, hjA, rfl⟩ := M.mem_img.1 hr
        obtain ⟨e'', he'', rfl⟩ := M.ι_surj v
        have hmem : ⁅(j : G), e''⁆ ∈ ⁅A, E⁆ := Subgroup.commutator_mem_commutator hjA he''
        rw [Subgroup.commutator_comm] at hmem
        exact ⟨⁅(j : G), e''⁆, hmem, M.ι_commutator j.2 he''⟩
      · exact ⟨1, Subgroup.one_mem _, M.ι_one⟩
      · rintro x y _ _ ⟨e₁, h₁, rfl⟩ ⟨e₂, h₂, rfl⟩
        exact ⟨e₁ * e₂, Subgroup.mul_mem _ h₁ h₂, M.ι_mul e₁ (hEA h₁) e₂ (hEA h₂)⟩
      · rintro c x _ ⟨e₁, h₁, rfl⟩
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
        · exact ⟨1, Subgroup.one_mem _, by rw [zero_smul, M.ι_one]⟩
        · exact ⟨e₁, h₁, by rw [one_smul]⟩
    obtain ⟨e', he', h'⟩ := key _ h
    have h2 : e' = e := M.ι_injOn (hEA he') he h'
    rw [← h2]
    exact he'
  · intro h
    have key : ∀ x ∈ ⁅E, A⁆, x ∈ E ∧ M.ι x ∈ commSub (M.img A) := by
      intro x hx
      rw [Subgroup.commutator_def] at hx
      refine Subgroup.closure_induction (p := fun x _ => x ∈ E ∧ M.ι x ∈ commSub (M.img A))
        ?_ ?_ ?_ ?_ hx
      · rintro x ⟨e', he', a, ha, rfl⟩
        have hcom : ⁅a, e'⁆ ∈ ⁅A, E⁆ := Subgroup.commutator_mem_commutator ha he'
        rw [Subgroup.commutator_comm] at hcom
        have hE' : ⁅a, e'⁆ ∈ E := hEA hcom
        have hinv : ⁅e', a⁆ = (⁅a, e'⁆)⁻¹ := (commutatorElement_inv a e').symm
        have hE'' : ⁅e', a⁆ ∈ E := by
          rw [hinv]
          exact E.inv_mem hE'
        refine ⟨hE'', ?_⟩
        rw [hinv, M.ι_inv hE', M.ι_commutator (hA ha) he']
        refine Submodule.neg_mem _ (Submodule.subset_span ⟨M.ρ ⟨a, hA ha⟩, ?_, M.ι e', rfl⟩)
        exact M.mem_img.2 ⟨⟨a, hA ha⟩, ha, rfl⟩
      · exact ⟨E.one_mem, by rw [M.ι_one]; exact Submodule.zero_mem _⟩
      · rintro x y _ _ ⟨hxE, hx⟩ ⟨hyE, hy⟩
        exact ⟨E.mul_mem hxE hyE, by rw [M.ι_mul x hxE y hyE]; exact Submodule.add_mem _ hx hy⟩
      · rintro x _ ⟨hxE, hx⟩
        exact ⟨E.inv_mem hxE, by rw [M.ι_inv hxE]; exact Submodule.neg_mem _ hx⟩
    exact (key e h).2

theorem img_conj {A : Subgroup G} (hA : A ≤ J) (j : ↥J) :
    cj (M.ρ j) (M.img A) = M.img (conjSubgroup A (j : G)⁻¹) := by
  ext r
  rw [mem_cj, M.mem_img, M.mem_img]
  constructor
  · rintro ⟨a, haA, ha⟩
    refine ⟨j * a * j⁻¹, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      have e : (j : G)⁻¹ * ((j * a * j⁻¹ : ↥J) : G) * ((j : G)⁻¹)⁻¹ = (a : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact haA
    · rw [map_mul, map_mul, map_inv, ha]
      group
  · rintro ⟨x, hx, rfl⟩
    rw [mem_conjSubgroup_iff] at hx
    refine ⟨j⁻¹ * x * j, ?_, ?_⟩
    · have e : ((j⁻¹ * x * j : ↥J) : G) = (j : G)⁻¹ * (x : G) * ((j : G)⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [e]
      exact hx
    · rw [map_mul, map_mul, map_inv]

theorem img_mono {S S' : Subgroup G} (h : S ≤ S') : M.img S ≤ M.img S' := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := M.mem_img.1 hr
  exact M.mem_img.2 ⟨j, h hj, rfl⟩

theorem img_sup {S S' : Subgroup G} (hS : S ≤ J) (hS' : S' ≤ J) :
    M.img (S ⊔ S') = M.img S ⊔ M.img S' := by
  unfold img
  rw [Subgroup.subgroupOf_sup hS hS', Subgroup.map_sup]

theorem isPGroup_img {p : ℕ} {S : Subgroup G} (hS : IsPGroup p S) : IsPGroup p (M.img S) :=
  (hS.comap_subtype (K := J)).map M.ρ

theorem img_le_normalizer {A S : Subgroup G} (hA : A ≤ J) (hS : S ≤ J)
    (h : A ≤ normalizer (S : Set G)) : M.img A ≤ normalizer ((M.img S : Subgroup (LGL 2 M.W)) :
      Set (LGL 2 M.W)) := by
  intro r hr
  obtain ⟨j, hjA, rfl⟩ := M.mem_img.1 hr
  have h1 : conjSubgroup S ((j : G)⁻¹) = S := by
    rw [conjSubgroup_eq_iff_mem_normalizer]
    exact (Subgroup.inv_mem _ (h hjA))
  have h2 := M.img_conj hS j
  rw [h1] at h2
  have h4 : ∀ y, y ∈ M.img S ↔ (M.ρ j)⁻¹ * y * M.ρ j ∈ M.img S := fun y => by
    rw [← mem_cj, h2]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h5 := h4 (M.ρ j * x * (M.ρ j)⁻¹)
  have e : (M.ρ j)⁻¹ * (M.ρ j * x * (M.ρ j)⁻¹) * M.ρ j = x := by group
  rw [e] at h5
  exact h5.symm

theorem img_pCoreOf (hC : IsPGroup 2 ↥(J ⊓ centralizer (E : Set G))) :
    M.img (pCoreOf 2 J) = pCoreOf 2 (M.img J) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pCoreOf 2 J ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
  apply le_antisymm
  ·
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (M.img_mono hO) ?_
      (M.isPGroup_img (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J))
    exact M.img_le_normalizer le_rfl hO (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J)
  ·
    set R : Subgroup (LGL 2 M.W) := pCoreOf 2 (M.img J) with hR
    have hRJ : R ≤ M.img J := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hker : M.ρ.ker ≤ (J ⊓ centralizer (E : Set G)).subgroupOf J := by
      intro j hj
      rw [MonoidHom.mem_ker] at hj
      rw [Subgroup.mem_subgroupOf]
      exact ⟨j.2, (M.ρ_eq_one_iff j).1 hj⟩
    have hkerP : IsPGroup 2 ↥M.ρ.ker := (hC.comap_subtype (K := J)).to_le hker
    have hP' : IsPGroup 2 ↥(R.comap M.ρ) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (M.img J)).comap_of_ker_isPGroup M.ρ hkerP
    set P : Subgroup G := (R.comap M.ρ).map J.subtype with hP
    have hPJ : P ≤ J := Subgroup.map_subtype_le _
    have hP2 : IsPGroup 2 P := hP'.map J.subtype
    have hPn : J ≤ normalizer (P : Set G) := by
      intro j hj
      apply E1.mem_normalizer_of_conj_mem
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_map.2 ⟨⟨j, hj⟩ * x * ⟨j, hj⟩⁻¹, ?_, rfl⟩
      rw [Subgroup.mem_comap] at hx ⊢
      rw [map_mul, map_mul, map_inv]
      have hρ : M.ρ ⟨j, hj⟩ ∈ normalizer (R : Set (LGL 2 M.W)) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (M.img J)
          (M.mem_img.2 ⟨⟨j, hj⟩, hj, rfl⟩)
      exact (Subgroup.mem_normalizer_iff.1 hρ _).1 hx
    have hPle : P ≤ pCoreOf 2 J :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPJ hPn hP2
    intro r hr
    obtain ⟨j, hjJ, rfl⟩ := M.mem_img.1 (hRJ hr)
    exact M.mem_img.2 ⟨j, hPle (Subgroup.mem_map.2 ⟨j, hr, rfl⟩), rfl⟩

end ModDataE

end CFSG.LocalAnalysis.WeakClosure81

end
