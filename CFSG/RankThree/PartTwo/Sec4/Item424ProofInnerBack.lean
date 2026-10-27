module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofInnerBar
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofField

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item424Proof

theorem nonempty_range_mulEquiv_of_ker_eq {A B₁ B₂ : Type*} [Group A] [Group B₁] [Group B₂]
    (f₁ : A →* B₁) (f₂ : A →* B₂) (h : f₁.ker = f₂.ker) : Nonempty (f₁.range ≃* f₂.range) :=
  ⟨((QuotientGroup.quotientKerEquivRange f₁).symm.trans
    (QuotientGroup.quotientMulEquivOfEq h)).trans (QuotientGroup.quotientKerEquivRange f₂)⟩

end Item424Proof

open Item424Proof

namespace Config424

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {a c : G} {K : Subgroup G}

omit [Finite G] in
theorem _root_.CFSG.RankThree.PartTwo.Sec4.Item424Proof.mem_normalizer_inf [Finite G] {g : G}
    (hgL : g ∈ L) (hgA : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun y hy => ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hgA y).mp hy.1
  · exact L.mul_mem (L.mul_mem hgL hy.2) (L.inv_mem hgL)

theorem nonempty_autIn_equiv (h : Config424 G A L a c K) {c₀ d : G}
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

theorem nonempty_thetaImage_equiv (h : Config424 G A L a c K)
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

end Config424

end CFSG.RankThree.PartTwo.Sec4
