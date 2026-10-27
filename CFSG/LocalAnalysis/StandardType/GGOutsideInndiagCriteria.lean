module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Assembly

section Perfect

variable {G : Type*} [Group G] {J : Subgroup G}

private theorem commutator_eq_top_of_eq (hJ : ⁅J, J⁆ = J) : commutator ↥J = ⊤ := by
  apply Subgroup.map_injective J.subtype_injective
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, hJ]

private theorem eq_self_of_mem_center {H : Type*} [Group H] (hH : commutator H = ⊤)
    (α : H →* H) (h : ∀ x : H, x⁻¹ * α x ∈ Subgroup.center H) (x : H) : α x = x := by
  let c : H →* Subgroup.center H :=
    { toFun := fun x => ⟨x⁻¹ * α x, h x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => by
        apply Subtype.ext
        have hc : y⁻¹ * (x⁻¹ * α x) = x⁻¹ * α x * y⁻¹ := Subgroup.mem_center_iff.mp (h x) y⁻¹
        change (x * y)⁻¹ * α (x * y) = x⁻¹ * α x * (y⁻¹ * α y)
        rw [map_mul, mul_inv_rev]
        calc y⁻¹ * x⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
          _ = x⁻¹ * α x * y⁻¹ * α y := by rw [hc]
          _ = x⁻¹ * α x * (y⁻¹ * α y) := by group }
  have hle : commutator H ≤ c.ker := Abelianization.commutator_subset_ker c
  rw [hH] at hle
  have hx : c x = 1 := MonoidHom.mem_ker.mp (hle (Subgroup.mem_top x))
  have hx' : x⁻¹ * α x = 1 := congrArg Subtype.val hx
  exact (inv_mul_eq_one.mp hx').symm

private def restrictHom {e : MulAut G} (he : J.map e.toMonoidHom = J) : ↥J →* ↥J :=
  MonoidHom.mk' (fun l => ⟨e l, he.le (Subgroup.mem_map_of_mem e.toMonoidHom l.2)⟩)
    fun a b => Subtype.ext (map_mul e (a : G) (b : G))

private theorem exists_eq_mk {R : Type} [Group R] (θ : ↥J ⧸ Subgroup.center ↥J ≃* R) (y : R) :
    ∃ l : ↥J, θ (l : ↥J ⧸ Subgroup.center ↥J) = y := by
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (θ.symm y)
  exact ⟨l, by rw [hl, MulEquiv.apply_symm_apply]⟩

end Perfect

theorem not_forall_induces_of_threeRankTwo {G : Type*} [Group G] {J : Subgroup G}
    (hJ : ⁅J, J⁆ = J) {E : Subgroup (MulAut G)} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) {f : MulAut G} (hf : f ∈ E)
    (hEJ : ∀ e ∈ E, J.map e.toMonoidHom = J)
    (hCJ : ∀ e ∈ E, (∀ c ∈ J, e c = c) → e ∈ Subgroup.zpowers f)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (hB : ∀ B : Subgroup (MulAut R), CFSG.Open.IsElemAbelian 3 B →
      B ≤ Subgroup.closure I → Nat.card B ≤ 9)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R) :
    ¬ ∀ e ∈ E, ∃ φ ∈ Subgroup.closure I,
      LargeEvenInduces θ (fun l l' : ↥J => (l' : G) = e l) φ := by
  intro hall
  choose φ hφI hφ using hall
  have hval : ∀ (e : MulAut G) (he : e ∈ E) (l : ↥J),
      φ e he (θ (l : ↥J ⧸ Subgroup.center ↥J)) =
        θ ((restrictHom (hEJ e he) l : ↥J) : ↥J ⧸ Subgroup.center ↥J) :=
    fun e he l => hφ e he l _ rfl
  let Ψ : ↥E →* MulAut R := MonoidHom.mk' (fun e => φ e e.2) fun a b => by
    ext y
    obtain ⟨l, rfl⟩ := exists_eq_mk θ y
    rw [MulAut.mul_apply, hval _ _ l, hval _ _ l, hval _ _ (restrictHom _ l)]
    rfl
  haveI : IsMulCommutative ↥E := hE.1
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hrange : Nat.card Ψ.range ≤ 9 := by
    refine hB _ ⟨inferInstance, ?_⟩ ?_
    · rintro _ ⟨e, rfl⟩
      have he3 : e ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hE.2 _ e.2)
      rw [← map_pow, he3, map_one]
    · rintro _ ⟨e, rfl⟩
      exact hφI e e.2
  have hker : Ψ.ker ≤ Subgroup.zpowers (⟨f, hf⟩ : ↥E) := by
    intro e he1
    have h1 : φ e e.2 = 1 := MonoidHom.mem_ker.mp he1
    have hc : ∀ l : ↥J, l⁻¹ * restrictHom (hEJ e e.2) l ∈ Subgroup.center ↥J := fun l =>
      QuotientGroup.eq.1 (θ.injective (by rw [← hval e e.2 l, h1, MulAut.one_apply]))
    have hfix : ∀ c ∈ J, (e : MulAut G) c = c := fun c hc' =>
      congrArg Subtype.val (eq_self_of_mem_center (commutator_eq_top_of_eq hJ) _ hc ⟨c, hc'⟩)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hCJ e e.2 hfix)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
  have hk3 : Nat.card Ψ.ker ≤ 3 := by
    have h3 : (⟨f, hf⟩ : ↥E) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hE.2 f hf)
    calc Nat.card Ψ.ker ≤ Nat.card (Subgroup.zpowers (⟨f, hf⟩ : ↥E)) :=
          Subgroup.card_le_of_le hker
      _ = orderOf (⟨f, hf⟩ : ↥E) := Nat.card_zpowers _
      _ ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) h3
  have h81 : 3 ^ 4 ≤ 3 * 9 := by
    rw [← hcard, ← Subgroup.card_ker_mul_card_range Ψ]
    exact Nat.mul_le_mul hk3 hrange
  norm_num at h81

theorem not_induces_of_not_inner {G : Type*} [Group G] {J : Subgroup G} (hJ : ⁅J, J⁆ = J)
    {e : MulAut G} (he : J.map e.toMonoidHom = J)
    (hni : ¬ ∃ x ∈ J, ∀ l ∈ J, e l = x * l * x⁻¹)
    {R : Type} [Group R] {I : Set (MulAut R)} (hI : I ⊆ LargeEvenInnSet R)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R) :
    ¬ ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (fun l l' : ↥J => (l' : G) = e l) φ := by
  rintro ⟨φ, hφ, hind⟩
  have hcl : Subgroup.closure I ≤ (MulAut.conj : R →* MulAut R).range :=
    (Subgroup.closure_le _).2 fun y hy => hI hy
  obtain ⟨r, rfl⟩ := hcl hφ
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (θ.symm r)
  have hr : θ (x : ↥J ⧸ Subgroup.center ↥J) = r := by rw [hx, MulEquiv.apply_symm_apply]
  let α : ↥J →* ↥J := MonoidHom.mk' (fun l => x⁻¹ * restrictHom he l * x) fun a b => by
    simp only [map_mul]
    group
  have hα : ∀ l : ↥J, l⁻¹ * α l ∈ Subgroup.center ↥J := by
    intro l
    refine QuotientGroup.eq.1 (θ.injective ?_)
    have h1 := hind l (restrictHom he l) rfl
    rw [MulAut.conj_apply] at h1
    change θ (l : ↥J ⧸ Subgroup.center ↥J) = θ ((x⁻¹ * restrictHom he l * x : ↥J) : ↥J ⧸ _)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, ← h1, hr]
    group
  refine hni ⟨x, x.2, fun l hl => ?_⟩
  have h2 : (x : G)⁻¹ * e l * x = l := congrArg Subtype.val
    (eq_self_of_mem_center (commutator_eq_top_of_eq hJ) α hα ⟨l, hl⟩)
  calc e l = x * ((x : G)⁻¹ * e l * x) * (x : G)⁻¹ := by group
    _ = x * l * (x : G)⁻¹ := by rw [h2]

end CFSG.StandardType.SCFourCover
