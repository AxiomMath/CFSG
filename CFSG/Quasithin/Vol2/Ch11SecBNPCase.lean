module

public import CFSG.Quasithin.Vol2.Ch11SecBNPE22Cases
public import CFSG.Quasithin.Vol2.Ch11SecBNPStar
public import CFSG.Quasithin.Background.A3Structure36ABasic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

theorem isSubnormal_of_open {G : Type} [Group G] {A B : Subgroup G}
    (hAB : CFSG.Open.IsSubnormal A B) (hB : B.IsSubnormal) : A.IsSubnormal :=
  hAB.mathlib hB

theorem nonabelian_of_perfect_surjective {A B : Type} [Group A] [Group B] [Group.IsPerfect A]
    [Nontrivial B] (f : A →* B) (hf : Function.Surjective f) : ∃ a b : B, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hker : commutator A ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      h (f a) (f b)]
    group
  rw [Group.IsPerfect.commutator_eq_top] at hker
  obtain ⟨x, y, hxy⟩ := exists_pair_ne B
  obtain ⟨a, rfl⟩ := hf x
  obtain ⟨b, rfl⟩ := hf y
  apply hxy
  rw [hker (Subgroup.mem_top a), hker (Subgroup.mem_top b)]

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_one_of_e22 (h1111 : ASInputs.AS_E_1_11) (h1114 : ASInputs.AS_E_1_14)
    {H T M K R : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 T) (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T) (hcases : E2.E22Cases H T M K) (hSQs : SQTKGroup (E2.StarQuot M H))
    (hn : E1.nParam H ≤ 1) (hRH : R ≤ H) : E1.nParam (R ⊔ oTwoUpper H) ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := R ⊔ oTwoUpper H with hYdef
  have hYH : Y ≤ H := sup_le hRH (oTwoUpper_le H)
  have hKH : K ≤ H := by rw [hHK]; exact le_sup_left
  set J' := (kerIn M H).subgroupOf H with hJ'
  set π : ↥H →* E2.StarQuot M H := QuotientGroup.mk' J' with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J'
  set Ks : Subgroup (E2.StarQuot M H) := (K.subgroupOf H).map π with hKsdef
  have hTy : TypeOne ↥Ks := typeOne_star_of_e22Cases hcases hn
  have hKs : IsSimpleGroup ↥Ks := hTy.isSimpleGroup
  have hKp : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKc
  have hKab : ∃ a b : ↥Ks, a * b ≠ b * a :=
    nonabelian_of_perfect_surjective
      ((π.subgroupMap (K.subgroupOf H)).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      ((π.subgroupMap_surjective _).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective)
  have hKsn : Ks.IsSubnormal := by
    have h1 := A4.subnormal_comap H.subtype hKc.2.2.1
    have h2 : H.comap H.subtype = ⊤ := Subgroup.subgroupOf_self H
    rw [h2] at h1
    exact (isSubnormal_of_open h1 Subgroup.IsSubnormal.top).map hπs
  set Ts : Subgroup (E2.StarQuot M H) := (T.subgroupOf H).map π with hTsdef
  have hTs : IsPGroup 2 ↥Ts := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map π
  have hKT : Ks ⊔ Ts = ⊤ := by
    have h1 : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKH hTH, ← hHK, Subgroup.subgroupOf_self]
    rw [hKsdef, hTsdef, ← Subgroup.map_sup, h1, Subgroup.map_top_of_surjective π hπs]
  set Os : Subgroup (E2.StarQuot M H) := ((oTwoUpper H).subgroupOf H).map π with hOsdef
  have hOn : Os.Normal := by
    have : ((oTwoUpper H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).mpr
        (le_normalizer_oTwoUpper H)
    exact this.map π hπs
  have hKO : Ks ≤ Os := Subgroup.map_mono fun x hx =>
    B1Red.perfect_le_oTwoUpper' hKH hKp (Subgroup.mem_subgroupOf.mp hx)
  set f : ↥Y →* E2.StarQuot M H := π.comp (Subgroup.inclusion hYH) with hf
  have hOY : Os ≤ f.range := by
    rintro _ ⟨o, ho, rfl⟩
    exact ⟨⟨o, le_sup_right (a := R) (Subgroup.mem_subgroupOf.mp ho)⟩, rfl⟩
  set P : GrpPred := fun (X : Type) [Group X] => Nonempty (X ≃* ↥Ks) with hPdef
  have hP : IsoInv P := by
    intro A B _ _ e h
    obtain ⟨e'⟩ := h
    exact ⟨e.trans e'⟩
  have hsecY' : SecAll ↥f.range P :=
    secAll_of_simple_subnormal hP hKs hKab hKsn ⟨MulEquiv.refl _⟩ hTs hKT hOn hKO hOY
  have hJs : Group.IsSolvable ↥(kerIn M H) := isSolvable_kerIn_of_e22Cases hcases
  have hker : Group.IsSolvable ↥f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    let j : ↥f.ker →* ↥(kerIn M H) :=
      { toFun := fun y => ⟨((y : ↥Y) : G), by
          have hy : π (Subgroup.inclusion hYH (y : ↥Y)) = 1 := y.2
          rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hJ',
            Subgroup.mem_subgroupOf] at hy
          exact hy⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := j) fun a b hab => ?_
    apply Subtype.ext
    apply Subtype.ext
    simpa [j] using congrArg Subtype.val hab
  have hsecY : SecAll ↥Y P :=
    secAll_of_surjective hP f.rangeRestrict f.rangeRestrict_surjective hker hsecY'
  have hE : ASInputs.E111Hyp ↥Y 1 := by
    intro H₁ K₁ _ _ hsn hsimple hnab B hB hBI
    have hsn' : H₁.IsSubnormal := isSubnormal_of_open hsn Subgroup.IsSubnormal.top
    obtain ⟨e⟩ := hsecY H₁ (K₁.subgroupOf H₁) hsn' hsimple hnab
    have hSQX : SQTKGroup (↥H₁ ⧸ K₁.subgroupOf H₁) :=
      sqtkGroup_of_mulEquiv e (sqtkGroup_subgroup hSQs Ks)
    have := nParam_sup_le_one (e114TypeOne_of_e114 h1114) hnab hSQX (TypeOne.of_mulEquiv e hTy)
      hB hBI
    simpa using this
  have := h1111 ↥Y 1 le_rfl hE
  rw [E1.nParam_subgroupOf]
  simpa using this

end CFSG.Quasithin.Vol2.Ch11.SecB
