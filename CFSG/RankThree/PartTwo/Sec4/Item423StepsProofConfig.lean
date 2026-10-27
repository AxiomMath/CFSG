module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofInnerBack
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec4.Item462ProofUL

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Item424Proof

structure Config423 (G : Type) [Group G] [Finite G] (A L : Subgroup G) (a : G) : Prop where
  sectionFourHyp : SectionFourHyp G
  maximal : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A
  card_eq : Nat.card A = 27
  mem_thetaComponents : L ∈ thetaComponents 3 G
  orderOf_a : orderOf a = 3
  a_mem_center : a ∈ Subgroup.center G
  sectionCentralizer_eq : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
    (Subgroup.zpowers a : Set G)

namespace Config423

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {a : G}

theorem isElemAbelian (h : Config423 G A L a) : CFSG.Assembly.IsElemAbelian 3 A :=
  h.maximal.prop

theorem pow_three (h : Config423 G A L a) : ∀ x ∈ A, x ^ 3 = 1 :=
  h.isElemAbelian.2

theorem comm (h : Config423 G A L a) : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem isPGroup (h : Config423 G A L a) : IsPGroup 3 A :=
  Sec5.isPGroup_of_isElemAbelian h.isElemAbelian

theorem a_mem (h : Config423 G A L a) : a ∈ A := by
  have ha : a ∈ (Subgroup.zpowers a : Set G) := Subgroup.mem_zpowers a
  rw [← h.sectionCentralizer_eq] at ha
  exact ha.1

theorem a_ne_one (h : Config423 G A L a) : a ≠ 1 := by
  intro h1
  have := h.orderOf_a
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem a_comm (h : Config423 G A L a) (x : G) : x * a = a * x :=
  Subgroup.mem_center_iff.mp h.a_mem_center x

theorem isQuasisimple_L (h : Config423 G A L a) :
    IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) :=
  h.mem_thetaComponents.2.2

theorem inf_thetaQuotCentralizer (h : Config423 G A L a)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    A ⊓ thetaQuotCentralizer L = Subgroup.zpowers a := by
  have hsc := h.sectionCentralizer_eq
  rw [Sec13.sectionCentralizer_eq_inf hAN] at hsc
  exact SetLike.coe_injective hsc

theorem le_normalizer (h45 : Item4_5) (h : Config423 G A L a) :
    A ≤ Subgroup.normalizer (L : Set G) :=
  h45 G h.sectionFourHyp A h.isPGroup
    (Or.inr ⟨h.isElemAbelian, 3, le_rfl, by rw [h.card_eq]; norm_num⟩) L h.mem_thetaComponents

theorem eq_one_of_mem_zpowers_a_of_mem_L (h : Config423 G A L a)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) {z : G}
    (hza : z ∈ Subgroup.zpowers a) (hzL : z ∈ L) : z = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hza
  refine eq_one_of_mem_of_commute hZ hzL (fun l _ => ?_) ?_
  · exact ((Commute.zpow_left (Commute.symm (h.a_comm l)) k : Commute (a ^ k) l)).eq
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [show a ^ (3 : ℕ) = 1 by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a, one_zpow]

theorem isPGroup_inf_subgroupOf (h : Config423 G A L a) :
    IsPGroup 3 ((A ⊓ L).subgroupOf L) := fun x =>
  ⟨1, Subtype.ext (Subtype.ext (by simpa using h.pow_three _ (Subgroup.mem_subgroupOf.mp x.2).1))⟩

theorem isElemAbelian_inf_subgroupOf (h : Config423 G A L a) :
    CFSG.Assembly.IsElemAbelian 3 ((A ⊓ L).subgroupOf L) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩
  · exact h.comm _ (Subgroup.mem_subgroupOf.mp x.2).1 _ (Subgroup.mem_subgroupOf.mp y.2).1
  · exact Subtype.ext (by simpa using h.pow_three _ (Subgroup.mem_subgroupOf.mp hy).1)

theorem isElemAbelian_imageModTheta_inf (h : Config423 G A L a) :
    CFSG.Assembly.IsElemAbelian 3 (Sec8.imageModTheta L (A ⊓ L)) :=
  isElemAbelian_map _ h.isElemAbelian_inf_subgroupOf

theorem card_imageModTheta_inf (h : Config423 G A L a) :
    Nat.card (Sec8.imageModTheta L (A ⊓ L)) = Nat.card (A ⊓ L : Subgroup G) := by
  rw [Sec8.imageModTheta, card_map_mk_of_isPGroup h.isPGroup_inf_subgroupOf]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

theorem eq_of_mk_eq (h : Config423 G A L a) {x y : L} (hx : (x : G) ∈ A) (hy : (y : G) ∈ A)
    (hxy : (x : L ⧸ aschbacherSolvableCore 3 L) = (y : L ⧸ aschbacherSolvableCore 3 L)) :
    x = y :=
  injOn_mk_of_isPGroup Nat.prime_three h.isPGroup_inf_subgroupOf
    (Subgroup.mem_subgroupOf.mpr ⟨hx, x.2⟩) (Subgroup.mem_subgroupOf.mpr ⟨hy, y.2⟩) hxy

theorem commute_of_closure (h : Config423 G A L a) {c₀ d : G}
    (hA : A = Subgroup.closure {a, c₀, d}) {f : G} (hc₀ : c₀ * f = f * c₀) (hd : d * f = f * d) :
    ∀ y ∈ A, y * f = f * y := by
  have hle : A ≤ Subgroup.centralizer ({f} : Set G) := by
    rw [hA, Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with rfl | rfl | rfl
    · exact (h.a_comm f).symm
    · exact hc₀
    · exact hd
  exact fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem maximal_imageModTheta_inf (h : Config423 G A L a) {c₀ d : G}
    (hA : A = Subgroup.closure {a, c₀, d}) (hc₀ : c₀ ∈ A ⊓ L) (hd : d ∈ A ⊓ L) :
    Maximal (fun B : Subgroup (L ⧸ aschbacherSolvableCore 3 L) =>
      CFSG.Assembly.IsElemAbelian 3 B) (Sec8.imageModTheta L (A ⊓ L)) := by
  refine ⟨h.isElemAbelian_imageModTheta_inf, fun B hB hDB => ?_⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  obtain ⟨F₃, hDF, hF₃, hF₃B⟩ := exists_pGroup_cover h.isPGroup_inf_subgroupOf
    (Sec5.isPGroup_of_isElemAbelian hB) hDB
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hF₃
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFB : ∀ f ∈ F₃, π f ∈ B := fun f hf => hF₃B ▸ Subgroup.mem_map_of_mem π hf
  have hFD : F₃ ≤ (A ⊓ L).subgroupOf L := by
    intro f hf
    have hcomm : ∀ x ∈ F₃, x * f = f * x := fun x hx =>
      hinj (F₃.mul_mem hx hf) (F₃.mul_mem hf hx) (by
        rw [map_mul, map_mul, hBc _ (hFB x hx) _ (hFB f hf)])
    have hc₀F : (⟨c₀, hc₀.2⟩ : L) ∈ F₃ := hDF (Subgroup.mem_subgroupOf.mpr hc₀)
    have hdF : (⟨d, hd.2⟩ : L) ∈ F₃ := hDF (Subgroup.mem_subgroupOf.mpr hd)
    have hf3 : (f : G) ^ 3 = 1 := by
      have h1 : f ^ 3 = 1 := hinj (F₃.pow_mem hf 3) F₃.one_mem (by
        rw [map_pow, map_one]
        exact hB.2 _ (hFB f hf))
      simpa using congrArg Subtype.val h1
    have hfA : (f : G) ∈ A := mem_of_maximal_of_commute h.maximal hf3
      (h.commute_of_closure hA (congrArg Subtype.val (hcomm _ hc₀F))
        (congrArg Subtype.val (hcomm _ hdF)))
    exact Subgroup.mem_subgroupOf.mpr ⟨hfA, f.2⟩
  rw [← hF₃B]
  exact Subgroup.map_mono hFD

theorem mem_normalizer_A (h : Config423 G A L a) {c₀ d : G}
    (hA : A = Subgroup.closure {a, c₀, d}) (hc₀ : c₀ ∈ A ⊓ L) (hd : d ∈ A ⊓ L) {w : G}
    (hw : w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G)) :
    w ∈ Subgroup.normalizer (A : Set G) := by
  have hle : A ≤ A.comap (MulAut.conj w).toMonoidHom := by
    conv_lhs => rw [hA]
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show w * y * w⁻¹ ∈ A
    rcases hy with rfl | rfl | rfl
    · rw [h.a_comm w, mul_inv_cancel_right]
      exact h.a_mem
    · exact ((Subgroup.mem_normalizer_iff.mp hw _).mp hc₀).1
    · exact ((Subgroup.mem_normalizer_iff.mp hw _).mp hd).1
  exact Subgroup.mem_normalizer_fintype fun y hy => hle hy

theorem exists_lift_of_mem_normalizer (h : Config423 G A L a)
    {xb : L ⧸ aschbacherSolvableCore 3 L}
    (hxb : xb ∈ Subgroup.normalizer
      ((Sec8.imageModTheta L (A ⊓ L) : Subgroup _) : Set (L ⧸ aschbacherSolvableCore 3 L))) :
    ∃ w : L, (w : G) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
      ∃ e ∈ Sec8.imageModTheta L (A ⊓ L),
        xb = e * QuotientGroup.mk' (aschbacherSolvableCore 3 L) w := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) xb
  obtain ⟨w, hw, e, he, hne⟩ := exists_normalizer_lift h.isPGroup_inf_subgroupOf (n := n) hxb
  refine ⟨w, Subgroup.mem_normalizer_fintype fun y hy => ?_, e, he, hne⟩
  have hyL : y ∈ L := hy.2
  have h1 := (Subgroup.mem_normalizer_iff.mp hw ⟨y, hyL⟩).mp (Subgroup.mem_subgroupOf.mpr hy)
  exact Subgroup.mem_subgroupOf.mp h1

theorem nonempty_autIn_equiv (h : Config423 G A L a) {c₀ d : G}
    (hA : A = Subgroup.closure {a, c₀, d}) (hc₀ : c₀ ∈ A ⊓ L) (hd : d ∈ A ⊓ L) :
    Nonempty (autIn L A ≃*
      autIn (⊤ : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) (Sec8.imageModTheta L (A ⊓ L))) := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  set Db := Sec8.imageModTheta L (A ⊓ L) with hDb
  set NA := Subgroup.normalizer (A : Set G) with hNA
  set M := L ⊓ NA with hM
  have hML : M ≤ L := inf_le_left
  have hMN : M ≤ NA := inf_le_right
  have hMDb : ∀ g : M, π (Subgroup.inclusion hML g) ∈ Subgroup.normalizer (Db : Set _) := by
    intro g
    have hgD := mem_normalizer_inf (hML g.2) (hMN g.2)
    have hg' : Subgroup.inclusion hML g ∈
        Subgroup.normalizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L) :=
      Subgroup.mem_normalizer_fintype fun y hy => Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hgD _).mp (Subgroup.mem_subgroupOf.mp hy))
    exact Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hg')
  let Φ' : M →* MulAut A := A.normalizerMonoidHom.comp (Subgroup.inclusion hMN)
  let ψ : M →* Subgroup.normalizer (Db : Set (L ⧸ aschbacherSolvableCore 3 L)) :=
    (π.comp (Subgroup.inclusion hML)).codRestrict _ hMDb
  let Φ : M →* MulAut Db := Db.normalizerMonoidHom.comp ψ
  have hr' : Φ'.range = autIn L A := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hr : Φ.range = autIn ⊤ Db := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      exact mem_autIn_iff.mpr ⟨_, (ψ g).2, Subgroup.mem_top _, rfl⟩
    · intro σ hσ
      obtain ⟨xb, hxN, -, rfl⟩ := mem_autIn_iff.mp hσ
      obtain ⟨w, hwD, e, he, hxe⟩ := h.exists_lift_of_mem_normalizer hxN
      have hwA : (w : G) ∈ NA := h.mem_normalizer_A hA hc₀ hd hwD
      refine ⟨⟨w, w.2, hwA⟩, ?_⟩
      have heN : e ∈ Subgroup.normalizer (Db : Set (L ⧸ aschbacherSolvableCore 3 L)) :=
        Subgroup.le_normalizer he
      have hpwN : π w ∈ Subgroup.normalizer (Db : Set (L ⧸ aschbacherSolvableCore 3 L)) :=
        hMDb ⟨w, w.2, hwA⟩
      have hsplit : (⟨xb, hxN⟩ : Subgroup.normalizer (Db : Set _)) = ⟨e, heN⟩ * ⟨π w, hpwN⟩ :=
        Subtype.ext hxe
      have he1 : Db.normalizerMonoidHom ⟨e, heN⟩ = 1 := by
        ext y
        rw [normalizerMonoidHom_apply_coe, MulAut.one_apply]
        have hc := congrArg Subtype.val
          (h.isElemAbelian_imageModTheta_inf.1.is_comm.comm ⟨e, he⟩ y)
        simp only [Subgroup.coe_mul] at hc
        rw [hc, mul_inv_cancel_right]
      show Db.normalizerMonoidHom (ψ ⟨w, w.2, hwA⟩) = Db.normalizerMonoidHom ⟨xb, hxN⟩
      rw [hsplit, map_mul, he1, one_mul]
      rfl
  have hk : Φ'.ker = Φ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have hgL : (g : G) ∈ L := hML g.2
    have hgA : (g : G) ∈ NA := hMN g.2
    constructor
    · intro h1
      ext y
      obtain ⟨_, ⟨x, hxD, rfl⟩⟩ := y
      show π (Subgroup.inclusion hML g) * π x * (π (Subgroup.inclusion hML g))⁻¹ = π x
      have hxA : (x : G) ∈ A := (Subgroup.mem_subgroupOf.mp hxD).1
      have h2 := congrArg (fun φ : MulAut A => ((φ ⟨x, hxA⟩ : A) : G)) h1
      simp only [MulAut.one_apply] at h2
      have h3 : Subgroup.inclusion hML g * x * (Subgroup.inclusion hML g)⁻¹ = x :=
        Subtype.ext h2
      rw [← map_mul, ← map_inv, ← map_mul, h3]
    · intro h1
      have hcen : ∀ x ∈ A ⊓ L, (g : G) * x * (g : G)⁻¹ = x := by
        intro x hx
        have hgx : (g : G) * x * (g : G)⁻¹ ∈ A ⊓ L :=
          (Subgroup.mem_normalizer_iff.mp (mem_normalizer_inf hgL hgA) x).mp hx
        have hxL : x ∈ L := (Subgroup.mem_inf.mp hx).2
        have hgxL : (g : G) * x * (g : G)⁻¹ ∈ L := (Subgroup.mem_inf.mp hgx).2
        have h2 := congrArg (fun φ : MulAut Db => ((φ ⟨π ⟨x, hxL⟩,
          Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)⟩ : Db) :
            L ⧸ aschbacherSolvableCore 3 L)) h1
        simp only [MulAut.one_apply] at h2
        have h3 := h.eq_of_mk_eq (x := ⟨(g : G) * x * (g : G)⁻¹, hgxL⟩) (y := ⟨x, hxL⟩)
          (Subgroup.mem_inf.mp hgx).1 (Subgroup.mem_inf.mp hx).1 (by
            change π _ = π _
            rw [← h2]
            show π _ = π (Subgroup.inclusion hML g) * π ⟨x, hxL⟩ *
              (π (Subgroup.inclusion hML g))⁻¹
            rw [← map_mul, ← map_inv, ← map_mul]
            rfl)
        exact congrArg Subtype.val h3
      have hcomm := h.commute_of_closure hA
        (f := (g : G)) (by
          have := hcen c₀ hc₀
          calc c₀ * g = ((g : G) * c₀ * (g : G)⁻¹) * g := by rw [this]
            _ = g * c₀ := by group)
        (by
          have := hcen d hd
          calc d * g = ((g : G) * d * (g : G)⁻¹) * g := by rw [this]
            _ = g * d := by group)
      ext y
      show (g : G) * y * (g : G)⁻¹ = y
      rw [← hcomm y y.2, mul_inv_cancel_right]
  obtain ⟨e⟩ := nonempty_range_mulEquiv_of_ker_eq Φ' Φ hk
  exact ⟨(MulEquiv.subgroupCongr hr'.symm).trans (e.trans (MulEquiv.subgroupCongr hr))⟩

theorem nonempty_thetaImage_equiv (h : Config423 G A L a)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) {c₀ d : G}
    (hA : A = Subgroup.closure {a, c₀, d}) (hc₀ : c₀ ∈ A ⊓ L) (hd : d ∈ A ⊓ L) :
    Nonempty (thetaImage (L ⊔ A) ≃*
      Multiplicative (ZMod 3) × (L ⧸ aschbacherSolvableCore 3 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 G with hN
  set πG := QuotientGroup.mk' N with hπG
  set Z := Subgroup.zpowers a with hZdef
  have hZn : Z.Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * a ^ k * g⁻¹ = a ^ k := by
      rw [(Commute.zpow_right (show Commute g a from h.a_comm g) k).eq, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem_zpowers a k⟩
  have hLA : L ⊔ A = L ⊔ Z := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [hA, Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact le_sup_right (α := Subgroup G) (Subgroup.mem_zpowers y)
      · exact le_sup_left (α := Subgroup G) hc₀.2
      · exact le_sup_left (α := Subgroup G) hd.2
    · exact sup_le_sup_left (Subgroup.zpowers_le.mpr h.a_mem) L
  have hθ : inSubgroup (aschbacherSolvableCore 3) L = L ⊓ N :=
    solvable_prime_complement_core_subnormal_intersection Nat.prime_three
      h.mem_thetaComponents.2.1
  have hθN : ∀ x : L, x ∈ aschbacherSolvableCore 3 L ↔ (x : G) ∈ N := by
    intro x
    constructor
    · intro hx
      have : (x : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := ⟨x, hx, rfl⟩
      rw [hθ] at this
      exact this.2
    · intro hx
      have : (x : G) ∈ L ⊓ N := ⟨x.2, hx⟩
      rw [← hθ] at this
      obtain ⟨y, hy, hyx⟩ := this
      rwa [show y = x from Subtype.ext hyx] at hy
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  let f₁ : L ⧸ aschbacherSolvableCore 3 L →* G ⧸ N :=
    QuotientGroup.lift (aschbacherSolvableCore 3 L) (πG.comp L.subtype) (fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπG, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact (hθN x).mp hx)
  let f₂ : Z →* G ⧸ N := πG.comp Z.subtype
  have hcomm : ∀ x z, Commute (f₁ x) (f₂ z) := by
    intro x z
    induction x using QuotientGroup.induction_on with
    | H l =>
      obtain ⟨_, k, rfl⟩ := z
      show πG l * πG (a ^ k) = πG (a ^ k) * πG l
      rw [← map_mul, ← map_mul,
        (Commute.zpow_right (show Commute (l : G) a from h.a_comm l) k).eq]
  let F := f₁.noncommCoprod f₂ hcomm
  have hF : ∀ (l : L) (z : Z), F ((l : L ⧸ aschbacherSolvableCore 3 L), z) = πG ((l : G) * z) := by
    intro l z
    show πG l * πG z = _
    rw [map_mul]
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, z⟩ hxz
    induction x using QuotientGroup.induction_on with
    | H l =>
      rw [hF, hπG, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxz
      have hlz : (l : G) * z = z * l := by
        obtain ⟨_, k, rfl⟩ := z
        exact (Commute.zpow_right (show Commute (l : G) a from h.a_comm l) k).eq
      set m := orderOf ((l : G) * z) with hm
      have hm3 : ¬ 3 ∣ m := fun h3 => hN3 (h3.trans (Subgroup.orderOf_dvd_natCard N hxz))
      have hpow : (l : G) ^ m * (z : G) ^ m = 1 := by
        rw [← (show Commute (l : G) z from hlz).mul_pow, hm, pow_orderOf_eq_one]
      have hzm : (z : G) ^ m = 1 := by
        have hzL : (z : G) ^ m ∈ L := by
          have e : (z : G) ^ m = ((l : G) ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hpow
          rw [e]
          exact L.inv_mem (L.pow_mem l.2 m)
        exact h.eq_one_of_mem_zpowers_a_of_mem_L hZ (Subgroup.pow_mem _ z.2 m) hzL
      have hz1 : (z : G) = 1 := by
        have h1 : orderOf (z : G) ∣ m := orderOf_dvd_of_pow_eq_one hzm
        have h2 : orderOf (z : G) ∣ 3 := by
          obtain ⟨_, k, rfl⟩ := z
          refine orderOf_dvd_of_pow_eq_one ?_
          show (a ^ k) ^ 3 = 1
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
            show a ^ (3 : ℕ) = 1 by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a, one_zpow]
        rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h3 | h3
        · exact orderOf_eq_one_iff.mp h3
        · exact absurd (h3 ▸ h1) hm3
      have hz1' : z = 1 := Subtype.ext hz1
      subst hz1'
      have hlN : (l : G) ∈ N := by simpa using hxz
      refine Prod.ext ?_ rfl
      show ((l : L ⧸ aschbacherSolvableCore 3 L) = 1)
      rw [QuotientGroup.eq_one_iff]
      exact (hθN l).mpr hlN
  have hFr : F.range = thetaImage (L ⊔ A) := by
    rw [thetaImage, hLA]
    apply le_antisymm
    · rintro _ ⟨⟨x, z⟩, rfl⟩
      induction x using QuotientGroup.induction_on with
      | H l =>
        rw [hF]
        exact Subgroup.mem_map_of_mem πG (Subgroup.mul_mem _ (le_sup_left (α := Subgroup G) l.2)
          (le_sup_right (α := Subgroup G) z.2))
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
      exact ⟨(((⟨y, hy⟩ : L) : L ⧸ aschbacherSolvableCore 3 L), ⟨z, hz⟩), hF ⟨y, hy⟩ ⟨z, hz⟩⟩
  have hZ3 : Nat.card Z = 3 := by rw [hZdef, Nat.card_zpowers, h.orderOf_a]
  have hC3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  let eZ : Z ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hZ3 hC3
  exact ⟨(MulEquiv.subgroupCongr hFr.symm).trans ((MonoidHom.ofInjective hFinj).symm.trans
    ((MulEquiv.prodCongr (MulEquiv.refl _) eZ).trans (MulEquiv.prodComm)))⟩

omit [Finite G] in
theorem card_map_mul_card_inf_ker {H K : Type*} [Group H] [Group K] [Finite H] (f : H →* K)
    (P : Subgroup H) : Nat.card (P.map f) * Nat.card (P ⊓ f.ker : Subgroup H) = Nat.card P := by
  set g := f.comp P.subtype with hg
  have h1 : g.range = P.map f := by rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have h2 : Nat.card g.ker = Nat.card (P ⊓ f.ker : Subgroup H) := by
    have e : g.ker.map P.subtype = P ⊓ f.ker := by
      rw [hg, ← MonoidHom.comap_ker, Subgroup.map_comap_eq, Subgroup.range_subtype]
    rw [← e, Subgroup.card_map_of_injective P.subtype_injective]
  have h3 := Subgroup.card_mul_index g.ker
  rw [Subgroup.index_ker, h1] at h3
  rw [← h2, mul_comm]
  exact h3

theorem of_card (h45 : Item4_5) (hS4 : SectionFourHyp G)
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (h27 : Nat.card A = 27) (haA : a ∈ A) (haZ : a ∈ Subgroup.center G) (ha1 : a ≠ 1)
    (hL : L ∈ thetaComponents 3 G) (h9 : Nat.card (autThetaQuot A L) = 9) :
    Config423 G A L a := by
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.1
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  have hAp : IsPGroup 3 A := Sec5.isPGroup_of_isElemAbelian hAe
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    h45 G hS4 A hAp (Or.inr ⟨hAe, 3, le_rfl, by rw [h27]; norm_num⟩) L hL
  have haC : a ∈ thetaQuotCentralizer L := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAN haA, fun l _ => ?_⟩
    have e : l⁻¹ * (a * l * a⁻¹) = 1 := by
      rw [show a * l = l * a from (Subgroup.mem_center_iff.mp haZ l).symm, mul_inv_cancel_right,
        inv_mul_cancel]
    rw [e]
    exact Subgroup.one_mem _
  set N := Subgroup.normalizer (L : Set G) with hN
  set ψ : N →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (thetaQuotMulAut L).comp L.normalizerMonoidHom with hψ
  have hA' : autThetaQuot A L = (A.subgroupOf N).map ψ := by
    rw [autThetaQuot, autIn, Subgroup.map_map, inf_of_le_left hAN]
  have hk := card_map_mul_card_inf_ker ψ (A.subgroupOf N)
  rw [← hA', h9, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, h27] at hk
  have hmap : (A.subgroupOf N ⊓ ψ.ker).map N.subtype = A ⊓ thetaQuotCentralizer L := by
    rw [Subgroup.map_inf_eq _ _ N.subtype N.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hAN]
    rfl
  have hcard : Nat.card (A ⊓ thetaQuotCentralizer L : Subgroup G) = 3 := by
    rw [← hmap, Subgroup.card_map_of_injective N.subtype_injective]
    omega
  have hinf : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers a :=
    (Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (show a ∈ A ⊓ thetaQuotCentralizer L from ⟨haA, haC⟩))
      (by rw [hcard, Nat.card_zpowers, ha3])).symm
  refine ⟨hS4, hmax, h27, hL, ha3, haZ, ?_⟩
  rw [Sec13.sectionCentralizer_eq_inf hAN, hinf]

theorem exists_closure_eq (h45 : Item4_5) (h : Config423 G A L a)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hinner : ∀ x ∈ A, ¬ InducesOuterTheta x L) :
    Nat.card (A ⊓ L : Subgroup G) = 9 ∧ (∀ x ∈ A, x ∈ (A ⊓ L) ⊔ Subgroup.zpowers a) ∧
      ∃ c₀ d : G, c₀ ∈ A ⊓ L ∧ d ∈ A ⊓ L ∧ A = Subgroup.closure {a, c₀, d} := by
  classical
  have hAN := h.le_normalizer h45
  have hinf := h.inf_thetaQuotCentralizer hAN
  have hCA : ∀ y ∈ A, y ∈ thetaQuotCentralizer L ↔ y ∈ Subgroup.zpowers a := by
    intro y hy
    rw [← hinf]
    exact ⟨fun hyC => ⟨hy, hyC⟩, fun hy' => hy'.2⟩
  have hZn : (Subgroup.zpowers a).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr h.a_mem_center)
  have hALa : ∀ x ∈ A, x ∈ L ⊔ Subgroup.zpowers a := fun x hx =>
    Item462Proof.mem_sup_zpowers_of_not_inducesOuterTheta h.maximal h.mem_thetaComponents hAN
      hCA hZ hx (hinner x hx)
  have haL : a ∉ L := fun haL =>
    h.a_ne_one (h.eq_one_of_mem_zpowers_a_of_mem_L hZ (Subgroup.mem_zpowers a) haL)
  have hsup : ∀ x ∈ A, x ∈ (A ⊓ L) ⊔ Subgroup.zpowers a := by
    intro x hx
    obtain ⟨l, hl, w', hw', hlw⟩ := Subgroup.mem_sup_of_normal_right.mp (hALa x hx)
    have hlA : l ∈ A := by
      have e : l = x * w'⁻¹ := by rw [← hlw]; group
      rw [e]
      exact A.mul_mem hx (A.inv_mem (Subgroup.zpowers_le.mpr h.a_mem hw'))
    rw [← hlw]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hlA, hl⟩) (Subgroup.mem_sup_right hw')
  have hAsup : (A ⊓ L) ⊔ Subgroup.zpowers a = A :=
    le_antisymm (sup_le inf_le_left (Subgroup.zpowers_le.mpr h.a_mem)) hsup
  have hAL9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
    have h1 := Item462Proof.card_sup_zpowers_of_not_mem h.a_mem_center h.orderOf_a
      (B := A ⊓ L) (fun h' => haL h'.2)
    rw [hAsup, h.card_eq] at h1
    omega
  refine ⟨hAL9, hsup, ?_⟩
  obtain ⟨c₀, hc₀, hc₀1⟩ : ∃ c₀ ∈ A ⊓ L, c₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : A ⊓ L ≤ ⊥ := fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
    have := Subgroup.card_le_of_le hle
    rw [hAL9, Subgroup.card_bot] at this
    norm_num at this
  have hc₀3 : orderOf c₀ = 3 := orderOf_eq_prime (h.pow_three c₀ hc₀.1) hc₀1
  obtain ⟨d, hd, hdc₀⟩ : ∃ d ∈ A ⊓ L, d ∉ Subgroup.zpowers c₀ := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show A ⊓ L ≤ Subgroup.zpowers c₀ from hcon)
    rw [hAL9, Nat.card_zpowers, hc₀3] at this
    norm_num at this
  have h9 := card_closure_pair_eq_nine h.isElemAbelian h.card_eq hc₀.1 hd.1 hc₀1 hdc₀
  have hcl : Subgroup.closure ({c₀, d} : Set G) ≤ A ⊓ L := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hc₀
    · exact hd
  have haC : a ∉ Subgroup.closure ({c₀, d} : Set G) := fun h' => haL (hcl h').2
  have hA := eq_closure_triple h.card_eq hc₀.1 hd.1 h.a_mem h9 haC
  refine ⟨c₀, d, hc₀, hd, ?_⟩
  rw [hA]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem autThetaQuot_eq_map_conj (h45 : Item4_5) (h : Config423 G A L a)
    (hsup : ∀ x ∈ A, x ∈ (A ⊓ L) ⊔ Subgroup.zpowers a) :
    autThetaQuot A L =
      (Sec8.imageModTheta L (A ⊓ L)).map
        (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* MulAut _) := by
  have hAN := h.le_normalizer h45
  have hinf := h.inf_thetaQuotCentralizer hAN
  have hZn : (Subgroup.zpowers a).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr h.a_mem_center)
  ext τ
  constructor
  · intro hτ
    obtain ⟨x, hxN, hxA, rfl⟩ := mem_autThetaQuot_iff.mp hτ
    obtain ⟨l, hl, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hsup x hxA)
    have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl.2
    have hwC : w ∈ thetaQuotCentralizer L := by
      have : w ∈ A ⊓ thetaQuotCentralizer L := by rw [hinf]; exact hw
      exact this.2
    have hwN : w ∈ Subgroup.normalizer (L : Set G) :=
      Sec6.thetaQuotCentralizer_le_normalizer L hwC
    have hw1 : thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) = 1 := by
      obtain ⟨n, hn, hne⟩ := hwC
      have : n = ⟨w, hwN⟩ := Subtype.ext hne
      rw [this, SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply] at hn
      exact hn
    have e : (⟨l * w, hxN⟩ : Subgroup.normalizer (L : Set G)) = ⟨l, hlN⟩ * ⟨w, hwN⟩ := rfl
    have hl1 : thetaQuotMulAut L (L.normalizerMonoidHom ⟨l, hlN⟩) =
        MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l, hl.2⟩) :=
      KFacts.thetaQuotMulAut_compAction_of_mem hl.2 hlN
    rw [e, map_mul, map_mul, hw1, mul_one, hl1]
    exact ⟨_, ⟨⟨l, hl.2⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    rw [mem_autThetaQuot_iff]
    refine ⟨l, Subgroup.le_normalizer l.2, (Subgroup.mem_subgroupOf.mp hl).1, ?_⟩
    exact KFacts.thetaQuotMulAut_compAction_of_mem l.2 _

omit [Finite G] in
theorem range_conj_le_autThetaQuot_top [Finite G] (L : Subgroup G) :
    (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* MulAut _).range ≤ autThetaQuot ⊤ L := by
  rintro _ ⟨s, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective s
  rw [mem_autThetaQuot_iff]
  refine ⟨l, Subgroup.le_normalizer l.2, Subgroup.mem_top _, ?_⟩
  exact KFacts.thetaQuotMulAut_compAction_of_mem l.2 _

end Config423

end CFSG.RankThree.PartTwo.Sec4
