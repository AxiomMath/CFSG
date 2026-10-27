module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeData
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeGlue
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.Quasithin.Background.SmithC27RTypeGen
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneCoord

public section

namespace CFSG.StandardType.TwDesc

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.U63TB CFSG.StandardType.Line63
  CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Solomon.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open scoped commutatorElement

section Red

variable {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
  (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
  {A : Subgroup (MulAut L')} (hAle : A ≤ presZ (twoSub ψ.ker hker))

@[expose] noncomputable def redEquiv : ↥A ≃* ↥(redSub hker hAle).range :=
  MonoidHom.ofInjective (redSub_injective hker hAle hperf)

theorem coe_redEquiv (a : ↥A) :
    (((redEquiv hker hperf hAle) a : ↥(redSub hker hAle).range) :
      MulAut (L' ⧸ twoSub ψ.ker hker)) = redSub hker hAle a :=
  rfl

include hperf in
theorem conj_mul_mem {m : L'}
    (hm : MulAut.conj (m : L' ⧸ twoSub ψ.ker hker) ∈
      Subgroup.normalizer ((redSub hker hAle).range : Set (MulAut (L' ⧸ twoSub ψ.ker hker))))
    {a : MulAut L'} (ha : a ∈ A) : MulAut.conj m * a * (MulAut.conj m)⁻¹ ∈ A := by
  classical
  have hpres : MulAut.conj m * a * (MulAut.conj m)⁻¹ ∈ presZ (twoSub ψ.ker hker) :=
    (presZ _).mul_mem ((presZ _).mul_mem (conjP _ m).2 (hAle ha)) ((presZ _).inv_mem (conjP _ m).2)
  have hred : redHom (twoSub ψ.ker hker) ⟨_, hpres⟩ =
      MulAut.conj (m : L' ⧸ twoSub ψ.ker hker) * redSub hker hAle ⟨a, ha⟩ *
        (MulAut.conj (m : L' ⧸ twoSub ψ.ker hker))⁻¹ := by
    have : (⟨MulAut.conj m * a * (MulAut.conj m)⁻¹, hpres⟩ : presZ (twoSub ψ.ker hker)) =
        conjP _ m * ⟨a, hAle ha⟩ * (conjP _ m)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, redHom_conjP]
    rfl
  have hmem : MulAut.conj (m : L' ⧸ twoSub ψ.ker hker) * redSub hker hAle ⟨a, ha⟩ *
      (MulAut.conj (m : L' ⧸ twoSub ψ.ker hker))⁻¹ ∈ (redSub hker hAle).range :=
    (Subgroup.mem_normalizer_iff.mp hm _).mp ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨b, hb⟩ := hmem
  have h1 : redHom (twoSub ψ.ker hker) ⟨b.1, hAle b.2⟩ =
      redHom (twoSub ψ.ker hker) ⟨_, hpres⟩ := by
    rw [hred, ← hb]
    rfl
  have h2 := redHom_injective _ (twoSub_le_center hker) hperf h1
  have h3 : b.1 = MulAut.conj m * a * (MulAut.conj m)⁻¹ := congrArg Subtype.val h2
  rw [← h3]
  exact b.2

include hperf in
theorem conj_mem_normalizer {m : L'}
    (hm : MulAut.conj (m : L' ⧸ twoSub ψ.ker hker) ∈
      Subgroup.normalizer ((redSub hker hAle).range : Set (MulAut (L' ⧸ twoSub ψ.ker hker)))) :
    MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  have hm' : MulAut.conj ((m⁻¹ : L') : L' ⧸ twoSub ψ.ker hker) ∈
      Subgroup.normalizer ((redSub hker hAle).range :
        Set (MulAut (L' ⧸ twoSub ψ.ker hker))) := by
    rw [QuotientGroup.mk_inv, map_inv]
    exact Subgroup.inv_mem _ hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mul_mem hker hperf hAle hm hx, fun hx => ?_⟩
  have h := conj_mul_mem hker hperf hAle hm' hx
  rw [map_inv] at h
  have e : (MulAut.conj m)⁻¹ * (MulAut.conj m * x * (MulAut.conj m)⁻¹) *
      ((MulAut.conj m)⁻¹)⁻¹ = x := by group
  rwa [e] at h

theorem conj_mem_normalizer_range {m : L'}
    (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    MulAut.conj (m : L' ⧸ twoSub ψ.ker hker) ∈
      Subgroup.normalizer ((redSub hker hAle).range :
        Set (MulAut (L' ⧸ twoSub ψ.ker hker))) := by
  have key : ∀ {m : L'}, MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∀ x ∈ (redSub hker hAle).range,
        MulAut.conj (m : L' ⧸ twoSub ψ.ker hker) * x *
          (MulAut.conj (m : L' ⧸ twoSub ψ.ker hker))⁻¹ ∈ (redSub hker hAle).range := by
    intro m hm x hx
    obtain ⟨a, rfl⟩ := hx
    have h : MulAut.conj m * a.1 * (MulAut.conj m)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hm _).mp a.2
    exact ⟨⟨_, h⟩, redSub_conj_triple hker hAle m a h⟩
  have hm' : MulAut.conj (m⁻¹) ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key hm x hx, fun hx => ?_⟩
  have h := key hm' _ hx
  rw [QuotientGroup.mk_inv, map_inv] at h
  have e : (MulAut.conj (m : L' ⧸ twoSub ψ.ker hker))⁻¹ *
      (MulAut.conj (m : L' ⧸ twoSub ψ.ker hker) * x *
        (MulAut.conj (m : L' ⧸ twoSub ψ.ker hker))⁻¹) *
      ((MulAut.conj (m : L' ⧸ twoSub ψ.ker hker))⁻¹)⁻¹ = x := by group
  rwa [e] at h

include hperf in
theorem redEquiv_ggConjAut {n : L'} (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hn' : MulAut.conj (n : L' ⧸ twoSub ψ.ker hker) ∈
      Subgroup.normalizer ((redSub hker hAle).range : Set (MulAut (L' ⧸ twoSub ψ.ker hker))))
    (a : ↥A) :
    redEquiv hker hperf hAle (ggConjAut A hn a) =
      ggConjAut (redSub hker hAle).range hn' (redEquiv hker hperf hAle a) := by
  apply Subtype.ext
  have h : MulAut.conj n * a.1 * (MulAut.conj n)⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp a.2
  exact redSub_conj_triple hker hAle n a h

end Red

section Frame

variable {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
  (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
  {A : Subgroup (MulAut L')} (hAle : A ≤ presZ (twoSub ψ.ker hker))

include hperf in
theorem frameA_of_red (hA : IsElemAbelian 3 A)
    {κ : ↥(redSub hker hAle).range →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    (hF : GGE6ThreeFrameA (redSub hker hAle).range κ) :
    GGE6ThreeFrameA A (κ.comp (redEquiv hker hperf hAle).toMonoidHom) := by
  obtain ⟨hinj, hrange, hroot, hnorm⟩ := hF
  have hrange' : (κ.comp (redEquiv hker hperf hAle).toMonoidHom).range = κ.range := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := (redEquiv hker hperf hAle).surjective b
      exact ⟨a, rfl⟩
  refine ⟨hinj.comp (redEquiv hker hperf hAle).injective, ?_, ?_, ?_⟩
  · rw [hrange']
    exact hrange
  · intro γ hγ
    obtain ⟨nb, hnb, hW, hRefl, hact⟩ := hroot γ hγ
    obtain ⟨n, hnπ, hnW⟩ := exists_lift_W hker hA hAle hW
    subst hnπ
    have hcn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
      conj_mem_normalizer hker hperf hAle hnb
    refine ⟨n, hcn, hnW, ?_, fun a => ?_⟩
    · have hφ : ggConjAut A hcn =
          MulAut.congr (redEquiv hker hperf hAle).symm
            (ggConjAut (redSub hker hAle).range hnb) := by
        refine MulEquiv.ext fun a => ?_
        change ggConjAut A hcn a = (redEquiv hker hperf hAle).symm
          (ggConjAut (redSub hker hAle).range hnb ((redEquiv hker hperf hAle) a))
        apply (redEquiv hker hperf hAle).injective
        rw [MulEquiv.apply_symm_apply, redEquiv_ggConjAut hker hperf hAle hcn hnb]
      rw [hφ]
      exact ggIsReflection_congr _ hRefl.1 hRefl.2
    · change Multiplicative.toAdd (κ (redEquiv hker hperf hAle (ggConjAut A hcn a))) = _
      rw [redEquiv_ggConjAut hker hperf hAle hcn hnb]
      exact hact _
  · intro m hm
    obtain ⟨u, hu⟩ := hnorm (m : L' ⧸ twoSub ψ.ker hker)
      (conj_mem_normalizer_range hker hAle hm)
    refine ⟨u, fun a b hab => ?_⟩
    have hbab : ((redEquiv hker hperf hAle b : ↥(redSub hker hAle).range) :
        MulAut (L' ⧸ twoSub ψ.ker hker)) =
        MulAut.conj (m : L' ⧸ twoSub ψ.ker hker) *
          ((redEquiv hker hperf hAle a : ↥(redSub hker hAle).range) :
            MulAut (L' ⧸ twoSub ψ.ker hker)) *
          (MulAut.conj (m : L' ⧸ twoSub ψ.ker hker))⁻¹ := by
      rw [coe_redEquiv, coe_redEquiv]
      have h : MulAut.conj m * a.1 * (MulAut.conj m)⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hm _).mp a.2
      have hb : b = ⟨_, h⟩ := Subtype.ext hab
      rw [hb]
      exact redSub_conj_triple hker hAle m a h
    exact hu _ _ hbab

end Frame

section Perfect

variable {G : Type} [Group G]

theorem eq_of_central_perfect {J C : Subgroup G} (hJ : commutator ↥J = ⊤)
    (hC : C ≤ Subgroup.center G) {a : MulAut G} (h : ∀ j ∈ J, j⁻¹ * a j ∈ C) :
    ∀ j ∈ J, a j = j := by
  have hcen : ∀ y ∈ C, ∀ g : G, g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hC hy) g
  letI : CommGroup C :=
    { (inferInstance : Group C) with mul_comm := fun x y => Subtype.ext (hcen y y.2 x) }
  let f : ↥J →* C :=
    { toFun := fun j => ⟨(j : G)⁻¹ * a j, h j j.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun l m => Subtype.ext (by
        show ((l * m : ↥J) : G)⁻¹ * a ((l * m : ↥J) : G) =
          (l : G)⁻¹ * a l * ((m : G)⁻¹ * a m)
        have hc := hcen _ (h l l.2) (m : G)⁻¹
        calc ((l * m : ↥J) : G)⁻¹ * a ((l * m : ↥J) : G)
            = (m : G)⁻¹ * ((l : G)⁻¹ * a l) * a m := by
              rw [Subgroup.coe_mul, map_mul]; group
          _ = ((l : G)⁻¹ * a l) * (m : G)⁻¹ * a m := by rw [hc]
          _ = (l : G)⁻¹ * a l * ((m : G)⁻¹ * a m) := by group) }
  have hf : ∀ l, f l = 1 := fun l =>
    Abelianization.commutator_subset_ker f (by rw [hJ]; exact Subgroup.mem_top l)
  intro j hj
  have h1 : (j : G)⁻¹ * a j = 1 := congrArg Subtype.val (hf ⟨j, hj⟩)
  exact (inv_mul_eq_one.mp h1).symm

theorem mem_of_perfect_of_central {J C : Subgroup G} (hJ : commutator ↥J = ⊤)
    (hC : C ≤ Subgroup.center G) {a : MulAut G} (h : ∀ x ∈ J, ∃ j ∈ J, ∃ z ∈ C, a x = j * z) :
    ∀ x ∈ J, a x ∈ J := by
  have hcen : ∀ y ∈ C, ∀ g : G, g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hC hy) g
  let K : Subgroup ↥J := (J.comap a.toMonoidHom).subgroupOf J
  have hK : (⊤ : Subgroup ↥J) ≤ K := by
    rw [← hJ, commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    show a ((⁅g₁, g₂⁆ : ↥J) : G) ∈ J
    have e : ((⁅g₁, g₂⁆ : ↥J) : G) = ⁅(g₁ : G), (g₂ : G)⁆ := rfl
    rw [e, map_commutatorElement]
    obtain ⟨j₁, hj₁, z₁, hz₁, h₁⟩ := h g₁ g₁.2
    obtain ⟨j₂, hj₂, z₂, hz₂, h₂⟩ := h g₂ g₂.2
    rw [h₁, h₂, commutatorElement_mul_mul' (Commute.symm (Subgroup.mem_center_iff.1 (hC hz₁) j₂))
      (Commute.symm (Subgroup.mem_center_iff.1 (hC hz₁) z₂))
      (Commute.symm (Subgroup.mem_center_iff.1 (hC hz₂) j₁))]
    exact J.mul_mem (J.mul_mem (J.mul_mem hj₁ hj₂) (J.inv_mem hj₁)) (J.inv_mem hj₂)
  intro x hx
  exact hK (Subgroup.mem_top (⟨x, hx⟩ : ↥J))

end Perfect

section Weyl

variable {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
  (hker : ψ.ker ≤ Subgroup.center L')
  {A : Subgroup (MulAut L')} (hAle : A ≤ presZ (twoSub ψ.ker hker))

theorem exists_lift_W_mem (hA : IsElemAbelian 3 A) {J : Subgroup L'}
    (hJA : ∀ a ∈ A, ∀ x ∈ J, a x ∈ J) {w : L' ⧸ twoSub ψ.ker hker}
    (hwJ : w ∈ J.map (QuotientGroup.mk' (twoSub ψ.ker hker)))
    (hw : ∀ a₁ ∈ (redSub hker hAle).range, (w * (a₁ w)⁻¹) ^ 3 = 1 ∧
      ∀ a₁' ∈ (redSub hker hAle).range, a₁' (w * (a₁ w)⁻¹) = w * (a₁ w)⁻¹) :
    ∃ n ∈ J, (n : L' ⧸ twoSub ψ.ker hker) = w ∧
      ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹ := by
  classical
  obtain ⟨n₀, hn₀J, rfl⟩ := hwJ
  have hZc := twoSub_le_center hker
  have hAp : ∀ a ∈ A, a ^ 3 = 1 := hA.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAp g.1 g.2)⟩
  have hZ'2 : IsPGroup 2 (J ⊓ twoSub ψ.ker hker : Subgroup L') :=
    (isPGroup_twoSub hker).to_le inf_le_right
  have hmk : ∀ x : L', (QuotientGroup.mk' (twoSub ψ.ker hker)) x = (x : L' ⧸ twoSub ψ.ker hker) :=
    fun x => rfl
  have hu : ∀ a : A, ((n₀ * (a.1 n₀)⁻¹ : L') : L' ⧸ twoSub ψ.ker hker) =
      (n₀ : L' ⧸ twoSub ψ.ker hker) *
        (redSub hker hAle a (n₀ : L' ⧸ twoSub ψ.ker hker))⁻¹ := by
    intro a
    rw [redSub_mk, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hn₀w : (QuotientGroup.mk' (twoSub ψ.ker hker)) n₀ = (n₀ : L' ⧸ twoSub ψ.ker hker) := rfl
  rw [hn₀w] at hw
  have hJ3 : ∀ a ∈ A, (n₀ * (a n₀)⁻¹) ^ 3 ∈ J ⊓ twoSub ψ.ker hker := by
    intro a ha
    refine Subgroup.mem_inf.mpr ⟨J.pow_mem (J.mul_mem hn₀J (J.inv_mem (hJA a ha n₀ hn₀J))) 3, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hu ⟨a, ha⟩]
    exact (hw (redSub hker hAle ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).1
  have hJfix : ∀ a ∈ A, ∀ a' ∈ A,
      (n₀ * (a n₀)⁻¹)⁻¹ * a' (n₀ * (a n₀)⁻¹) ∈ J ⊓ twoSub ψ.ker hker := by
    intro a ha a' ha'
    refine Subgroup.mem_inf.mpr ⟨J.mul_mem (J.inv_mem (J.mul_mem hn₀J (J.inv_mem (hJA a ha n₀ hn₀J))))
      (hJA a' ha' _ (J.mul_mem hn₀J (J.inv_mem (hJA a ha n₀ hn₀J)))), ?_⟩
    apply QuotientGroup.eq.mp
    rw [show ((a' (n₀ * (a n₀)⁻¹) : L') : L' ⧸ twoSub ψ.ker hker) =
        redSub hker hAle ⟨a', ha'⟩ ((n₀ * (a n₀)⁻¹ : L') : L' ⧸ twoSub ψ.ker hker) from
      (redSub_mk hker hAle ⟨a', ha'⟩ _).symm, hu ⟨a, ha⟩]
    exact ((hw (redSub hker hAle ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).2 _ ⟨⟨a', ha'⟩, rfl⟩).symm
  obtain ⟨z, hz, hzW⟩ := exists_lift_fixed (Z := J ⊓ twoSub ψ.ker hker) (A := A)
    (fun x hx => hZc hx.2) hZ'2 hA3 hAc
    (fun a ha z hz => ⟨hJA a ha z hz.1, hAle ha z hz.2⟩) n₀ hJ3 hJfix
  refine ⟨n₀ * z, J.mul_mem hn₀J hz.1, ?_, hzW⟩
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz.2, mul_one]
  rfl

end Weyl

section Component

theorem nonempty_quotCenter_map {K Q : Type} [Group K] [Group Q] (π : K →* Q)
    (hker : π.ker ≤ Subgroup.center K) {J : Subgroup K} (hJ : commutator ↥J = ⊤) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥(J.map π) ⧸ Subgroup.center ↥(J.map π)) := by
  set φ : ↥J →* ↥(J.map π) := π.subgroupMap J with hφdef
  have hφ : Function.Surjective φ := π.subgroupMap_surjective J
  have hφk : φ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    have h1 : π (j : K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hj)
    have hjc := Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr h1))
    exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hjc g)
  haveI : Group.IsPerfect ↥J := ⟨hJ⟩
  exact ⟨CFSG.Quasithin.SmithC27.quotCenterEquivOfSurjective φ hφ hφk⟩

theorem isComponentOf_map {K Q : Type} [Group K] [Group Q] (π : K →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K) (α : MulAut K)
    (β : MulAut Q) (hαβ : ∀ k, π (α k) = β (π k)) {J : Subgroup K}
    (hJ : IsComponentOf J (fixSubgroup α)) : IsComponentOf (J.map π) (fixSubgroup β) := by
  refine ⟨(Subgroup.map_mono hJ.1).trans (map_fixSubgroup_le π hker α β hαβ), ?_, ?_⟩
  · exact (hJ.2.1.map π).trans (IsSubnormal.step (map_fixSubgroup_le π hker α β hαβ)
      (normal_map_fixSubgroup π hker α β hαβ hπ) (IsSubnormal.refl _))
  · have hφ : Function.Surjective (π.subgroupMap J) := π.subgroupMap_surjective J
    haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
    obtain ⟨e⟩ := nonempty_quotCenter_map π hker hJ.2.2.1
    exact ⟨(Group.IsPerfect.ofSurjective hφ).commutator_eq_top,
      (MulEquiv.isSimpleGroup_congr e).mp hJ.2.2.2⟩

end Component

section Class

variable {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
  (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
  {A : Subgroup (MulAut L')} (hAle : A ≤ presZ (twoSub ψ.ker hker))

theorem invariant_of_red {J : Subgroup L'} (hJ : commutator ↥J = ⊤)
    (hX : ∀ a₁ ∈ (redSub hker hAle).range,
      ∀ x ∈ J.map (QuotientGroup.mk' (twoSub ψ.ker hker)),
        a₁ x ∈ J.map (QuotientGroup.mk' (twoSub ψ.ker hker))) :
    ∀ a ∈ A, ∀ x ∈ J, a x ∈ J := by
  intro a ha
  refine mem_of_perfect_of_central (C := twoSub ψ.ker hker) hJ (twoSub_le_center hker) ?_
  intro x hx
  have h1 : ((a x : L') : L' ⧸ twoSub ψ.ker hker) ∈
      J.map (QuotientGroup.mk' (twoSub ψ.ker hker)) := by
    have := hX (redSub hker hAle ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩ (x : L' ⧸ twoSub ψ.ker hker) ⟨x, hx, rfl⟩
    rwa [redSub_mk] at this
  obtain ⟨j, hj, hjx⟩ := h1
  refine ⟨j, hj, j⁻¹ * a x, QuotientGroup.eq.mp hjx, by group⟩

include hperf in
theorem classA_of_red (hA : IsElemAbelian 3 A)
    {κ : ↥(redSub hker hAle).range →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    {y : ↥A} {J : Subgroup L'} (hJ : commutator ↥J = ⊤)
    (hJA : ∀ a ∈ A, ∀ x ∈ J, a x ∈ J) {P P' : Prop} (hPP : P → P')
    (hcl : GGE6ThreeClassA (redSub hker hAle).range κ (redEquiv hker hperf hAle y)
      (J.map (QuotientGroup.mk' (twoSub ψ.ker hker))) P) :
    GGE6ThreeClassA A (κ.comp (redEquiv hker hperf hAle).toMonoidHom) y J P' := by
  obtain ⟨F, hF, ζ, hζ, hζo, i, hkc, hreal, hd4⟩ := hcl
  refine ⟨F, hF, ζ, hζ, hζo, i, ?_, ?_, fun h => hPP (hd4 h)⟩
  · intro a ha j hj
    have h1 := hkc (redEquiv hker hperf hAle a) ha
    refine eq_of_central_perfect hJ (twoSub_le_center hker) (a := (a : MulAut L'))
      (fun x hx => ?_) j hj
    have h2 := h1 (x : L' ⧸ twoSub ψ.ker hker) ⟨x, hx, rfl⟩
    rw [coe_redEquiv, redSub_mk] at h2
    exact QuotientGroup.eq.mp h2.symm
  · intro c hc
    obtain ⟨nb, hnb, hnbJ, hW, hact⟩ := hreal c hc
    obtain ⟨n, hnJ, hnπ, hnW⟩ := exists_lift_W_mem hker hAle hA hJA hnbJ hW
    subst hnπ
    have hcn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
      conj_mem_normalizer hker hperf hAle hnb
    refine ⟨n, hcn, hnJ, hnW, fun a => ?_⟩
    change Multiplicative.toAdd (κ (redEquiv hker hperf hAle (ggConjAut A hcn a))) = _
    rw [redEquiv_ggConjAut hker hperf hAle hcn hnb]
    exact hact _

end Class

end CFSG.StandardType.TwDesc

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwE6Three_frameClass_descent_one
    (hOdd : ∀ {K₁ : Type} [Field K₁] [Finite K₁], Nat.card K₁ = (2 ^ 1) ^ 2 →
      ∀ {L₁ : Type} [Group L₁] [Finite L₁] {ψ₁ : L₁ →* TwE6Delta.RecipeR K₁ 1}
        {A₁ : Subgroup (MulAut L₁)}, Odd (Nat.card ψ₁.ker) →
        GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K₁ 1) (TwE6Delta.RecipeI K₁ 1) L₁ ψ₁ A₁ →
        ∃ κ : ↥A₁ →* Multiplicative (Fin Tag.E6.rank → ZMod 3), GGE6ThreeFrameA A₁ κ ∧
          ∀ (y : ↥A₁) (J : Subgroup L₁), y ≠ 1 → IsComponentOf J (fixSubgroup (y : MulAut L₁)) →
            GGE6ThreeClassA A₁ κ y J (∃ m : ℕ, 1 ≤ m ∧
              GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)))
    (hNorm : ∀ {K₁ : Type} [Field K₁] [Finite K₁], Nat.card K₁ = (2 ^ 1) ^ 2 →
      ∀ {L₁ : Type} [Group L₁] [Finite L₁] {ψ₁ : L₁ →* TwE6Delta.RecipeR K₁ 1}
        {A₁ : Subgroup (MulAut L₁)}, Odd (Nat.card ψ₁.ker) →
        GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K₁ 1) (TwE6Delta.RecipeI K₁ 1) L₁ ψ₁ A₁ →
        ∀ (y : ↥A₁) (J : Subgroup L₁), y ≠ 1 →
          IsComponentOf J (fixSubgroup (y : MulAut L₁)) → ∀ a ∈ A₁, ∀ x ∈ J, a x ∈ J)
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* TwE6Delta.RecipeR K 1}
    {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K 1) (TwE6Delta.RecipeI K 1) L' ψ₀ A) :
    ∃ κ : ↥A →* Multiplicative (Fin Tag.E6.rank → ZMod 3), GGE6ThreeFrameA A κ ∧
      ∀ (y : ↥A) (J : Subgroup L'), y ≠ 1 → IsComponentOf J (fixSubgroup (y : MulAut L')) →
        GGE6ThreeClassA A κ y J (∃ m : ℕ, 1 ≤ m ∧
          GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) := by
  obtain ⟨hψ, hker, hperf, hA, hAI, h5, -, hsc⟩ := hTB
  have hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ₀.ker hker) := fun a ha =>
    U63TB.mem_presZ_of_ker hker fun z hz => U63TB.preserves_ker (hAI a ha) hz
  have h5' : 3 ^ 5 ≤ Nat.card (U63TB.redSub hker hAle).range := by
    rw [U63TB.card_range_redSub hker hAle hperf]
    exact h5
  have hTB' : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K 1) (TwE6Delta.RecipeI K 1)
      (L' ⧸ U63TB.twoSub ψ₀.ker hker) (U63TB.psi1 hker) (U63TB.redSub hker hAle).range :=
    ⟨U63TB.psi1_surjective hker hψ, U63TB.psi1_ker_central hker,
      U63TB.commutator_quot hker hperf, U63TB.isElemAbelian_range_redSub hker hAle hA,
      U63TB.redSub_hAI hker hAle hAI, h5',
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 3 ≤ 5)).trans h5',
      U63TB.selfCent_quot hker hA hAle hsc⟩
  obtain ⟨κ, hF, hC⟩ := hOdd hK (U63TB.odd_card_ker_psi1 hker) hTB'
  refine ⟨κ.comp (TwDesc.redEquiv hker hperf hAle).toMonoidHom,
    TwDesc.frameA_of_red hker hperf hAle hA hF, ?_⟩
  intro y J hy hJ
  have hyne : TwDesc.redEquiv hker hperf hAle y ≠ 1 := fun h =>
    hy ((TwDesc.redEquiv hker hperf hAle).injective (by rw [h, map_one]))
  have hπker : (QuotientGroup.mk' (U63TB.twoSub ψ₀.ker hker)).ker ≤ Subgroup.center L' := by
    rw [QuotientGroup.ker_mk']
    exact U63TB.twoSub_le_center hker
  have hJbar : IsComponentOf (J.map (QuotientGroup.mk' (U63TB.twoSub ψ₀.ker hker)))
      (fixSubgroup ((TwDesc.redEquiv hker hperf hAle y : ↥(U63TB.redSub hker hAle).range) :
        MulAut (L' ⧸ U63TB.twoSub ψ₀.ker hker))) :=
    TwDesc.isComponentOf_map (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) hπker
      (y : MulAut L') _ (fun k => (U63TB.redSub_mk hker hAle y k).symm) hJ
  have hJA := TwDesc.invariant_of_red hker hAle hJ.2.2.1
    (hNorm hK (U63TB.odd_card_ker_psi1 hker) hTB' _ _ hyne hJbar)
  obtain ⟨e⟩ := TwDesc.nonempty_quotCenter_map (QuotientGroup.mk' _) hπker hJ.2.2.1
  exact TwDesc.classA_of_red hker hperf hAle hA hJ.2.2.1 hJA
    (fun ⟨m, hm1, hm⟩ => ⟨m, hm1, largeEvenRawDatum_mono
      (fun _ _ _ _ hQ => ⟨e.trans hQ.some⟩) hm⟩) (hC _ _ hyne hJbar)

end CFSG.StandardType

end
