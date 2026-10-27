module

public import CFSG.Quasithin.Background.C35Insp
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique

variable {A : Type} [Group A] {K : Subgroup A} {G' : Type} [Group G']

@[expose] def img (φ : ↥K →* G') (X : Subgroup A) : Subgroup G' := (X.subgroupOf K).map φ

theorem mem_centerOf_iff {x : ↥K} : (x : A) ∈ centerOf K ↔ x ∈ Subgroup.center ↥K := by
  constructor
  · rintro ⟨-, hc⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hc y y.2)
  · intro h
    refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 h ⟨y, hy⟩)

variable {φ : ↥K →* G'}

theorem mem_of_img_mem (hker : φ.ker ≤ Subgroup.center ↥K) {X : Subgroup A}
    (hZX : centerOf K ≤ X) {x : ↥K} (hx : φ x ∈ img φ X) : (x : A) ∈ X := by
  obtain ⟨y, hy, hxy⟩ := hx
  have h1 : y⁻¹ * x ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have h2 : ((y⁻¹ * x : ↥K) : A) ∈ centerOf K := mem_centerOf_iff.2 (hker h1)
  have h3 := X.mul_mem (Subgroup.mem_subgroupOf.1 hy) (hZX h2)
  simpa using h3

theorem img_ne_top (hker : φ.ker ≤ Subgroup.center ↥K) {Y : Subgroup A} (hYK : Y ≤ K)
    (hZY : centerOf K ≤ Y) (hne : Y ≠ K) : img φ Y ≠ ⊤ := by
  intro htop
  apply hne
  refine le_antisymm hYK fun x hx => ?_
  have : φ ⟨x, hx⟩ ∈ img φ Y := by
    rw [htop]
    exact Subgroup.mem_top _
  exact mem_of_img_mem hker hZY this

theorem isSolvable_of_img (hker : φ.ker ≤ Subgroup.center ↥K) {Y : Subgroup A}
    (hYK : Y ≤ K) (h : Group.IsSolvable ↥(img φ Y)) : Group.IsSolvable ↥Y := by
  let ψ : ↥(Y.subgroupOf K) →* ↥(img φ Y) := φ.subgroupMap (Y.subgroupOf K)
  have hψ : Function.Surjective ψ := φ.subgroupMap_surjective _
  have hab : Group.IsSolvable ↥ψ.ker := by
    have hcomm : ∀ a b : ↥ψ.ker, a * b = b * a := by
      intro a b
      have ha : ((a : ↥(Y.subgroupOf K)) : ↥K) ∈ Subgroup.center ↥K := by
        apply hker
        have := a.2
        rw [MonoidHom.mem_ker] at this ⊢
        exact congrArg Subtype.val this
      exact Subtype.ext (Subtype.ext ((Subgroup.mem_center_iff.1 ha) _).symm)
    let _ : CommGroup ↥ψ.ker := { mul_comm := hcomm }
    infer_instance
  have h2 : Group.IsSolvable ↥(Y.subgroupOf K) :=
    Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ (by rw [Subgroup.range_subtype])
  exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hYK).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hYK).surjective

theorem isSylowTwoOf_img [Finite A] (hker : φ.ker ≤ Subgroup.center ↥K)
    (hφ : Function.Surjective φ) {S : Subgroup A} (hS : IsSylowTwoOf S K)
    (hZS : centerOf K ≤ S) : IsSylowTwoOf (img φ S) ⊤ := by
  obtain ⟨hSK, hp, hidx⟩ := hS
  have hkerS : φ.ker ≤ S.subgroupOf K := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hZS (mem_centerOf_iff.2 (hker hx)))
  refine ⟨le_top, ?_, ?_⟩
  · have hp' : IsPGroup 2 ↥(S.subgroupOf K) :=
      hp.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
    exact hp'.map φ
  · rw [index_subgroupOf_top, img, Subgroup.index_map_eq _ hφ hkerS]
    exact hidx

theorem normalizer_img_le (hker : φ.ker ≤ Subgroup.center ↥K) (hφ : Function.Surjective φ)
    {S Y : Subgroup A} (hSK : S ≤ K) (hZS : centerOf K ≤ S)
    (hY : K ⊓ Subgroup.normalizer (S : Set A) ≤ Y) :
    Subgroup.normalizer ((img φ S : Subgroup G') : Set G') ≤ img φ Y := by
  intro g hg
  obtain ⟨k, rfl⟩ := hφ g
  refine ⟨k, Subgroup.mem_subgroupOf.2 (hY ⟨k.2, ?_⟩), rfl⟩
  show (k : A) ∈ Subgroup.normalizer (S : Set A)
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    by_cases hsK : s ∈ K
    · have h1 : φ ⟨s, hsK⟩ ∈ img φ S := ⟨⟨s, hsK⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 hg (φ ⟨s, hsK⟩)).1 h1
      have h3 : φ (k * ⟨s, hsK⟩ * k⁻¹) ∈ img φ S := by
        rw [map_mul, map_mul, map_inv]
        exact h2
      exact mem_of_img_mem hker hZS h3
    · exact absurd (hSK hs) hsK
  · intro hs
    have hsK : s ∈ K := by
      have := K.mul_mem (K.mul_mem (K.inv_mem k.2) (hSK hs)) k.2
      simpa [mul_assoc] using this
    have h1 : φ (k * ⟨s, hsK⟩ * k⁻¹) ∈ img φ S :=
      ⟨k * ⟨s, hsK⟩ * k⁻¹, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    have h2 : φ ⟨s, hsK⟩ ∈ img φ S := by
      rw [map_mul, map_mul, map_inv] at h1
      have := (Subgroup.mem_normalizer_iff.1 hg (φ ⟨s, hsK⟩)).2 h1
      exact this
    exact mem_of_img_mem hker hZS h2

theorem isPGroup_center (hZ : IsPGroup 2 ↥(centerOf K)) : IsPGroup 2 ↥(Subgroup.center ↥K) := by
  let f : ↥(Subgroup.center ↥K) →* ↥(centerOf K) :=
    { toFun := fun x => ⟨((x : ↥K) : A), mem_centerOf_iff.2 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine hZ.of_injective f fun x y hxy => ?_
  have := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext this)

theorem centerOf_le_of_sylow [Finite A] (hZ : IsPGroup 2 ↥(centerOf K)) {S : Subgroup A}
    (hS : IsSylowTwoOf S K) : centerOf K ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSK, hp, hidx⟩ := hS
  have hp' : IsPGroup 2 ↥(S.subgroupOf K) := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  have hle := (isPGroup_center hZ).le_sylow_of_normal (hp'.toSylow hidx)
  intro x hx
  exact Subgroup.mem_subgroupOf.1 (hle ((mem_centerOf_iff (x := ⟨x, hx.1⟩)).1 hx))

theorem exists_overgroup [Finite A] {Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V)
    (hker : φ.ker ≤ Subgroup.center ↥K) (hφ : Function.Surjective φ) :
    ∃ T : Subgroup G', IsSylowTwoOf T ⊤ ∧ T ≤ img φ Y ∧
      Subgroup.normalizer (T : Set G') ≤ img φ Y ∧ img φ Y ≠ ⊤ ∧
        ¬ Group.IsSolvable ↥(img φ Y) := by
  obtain ⟨hYK, S, hS, hNS⟩ := hD.parabolic
  have hZS : centerOf K ≤ S := centerOf_le_of_sylow hD.center hS
  have hSY : S ≤ Y := fun s hs => hNS ⟨hS.1 hs, Subgroup.le_normalizer hs⟩
  refine ⟨img φ S, isSylowTwoOf_img hker hφ hS hZS, Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.2 (hSY (Subgroup.mem_subgroupOf.1 hx)),
    normalizer_img_le hker hφ hS.1 hZS hNS,
    img_ne_top hker hYK (hZS.trans hSY) hD.ne_top, fun hsolv => ?_⟩
  have h0 : perfectCore Y = ⊥ :=
    (isSolvable_iff_perfectCore_eq_bot Y).1 (isSolvable_of_img hker hYK hsolv)
  exact hD.ne_bot (hD.eq_perfectCore.trans h0)

end CFSG.Quasithin.C35Pf
