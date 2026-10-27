module

public import CFSG.LocalAnalysis.StandardType.GGWPlusTwE6
public import CFSG.LocalAnalysis.StandardType.GGWPlusTwE6Quot
public import CFSG.LocalAnalysis.StandardType.GGWPlusE6Auto
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTwE6
public import CFSG.LocalAnalysis.StandardType.GGCoverRkTwE6Frame
public import CFSG.LocalAnalysis.StandardType.GGCoverRkTwE6Count
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private abbrev InnerAut (R : Type*) [Group R] : Subgroup (MulAut R) :=
  (MulAut.conj : R →* MulAut R).range

private def conjSub {G : Type*} [Group G] (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

private theorem conjSub_one {G : Type*} [Group G] (H : Subgroup G) :
    conjSub (1 : G) H = H := by
  ext x
  simp [conjSub, MulAut.conj_apply]

private theorem conjSub_mul {G : Type*} [Group G] (g h : G) (H : Subgroup G) :
    conjSub (g * h) H = conjSub g (conjSub h H) := by
  simp only [conjSub, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, mul_assoc]

private theorem conjSub_injective {G : Type*} [Group G] (g : G) :
    Function.Injective (conjSub g) :=
  Subgroup.map_injective (by simpa using (MulAut.conj g).injective)

private theorem conj_conj_mul {G : Type*} [Group G] (a : MulAut G) (r : G) :
    a * MulAut.conj r * a⁻¹ = MulAut.conj (a r) := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]

@[instance_reducible] private instance conjSubAction (G : Type*) [Group G] : MulAction G (Subgroup G) where
  smul := conjSub
  one_smul := conjSub_one
  mul_smul := conjSub_mul

private theorem innerAut_normal (R : Type) [Group R] : (InnerAut R).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨r, rfl⟩ := hx
  exact ⟨g r, (conj_conj_mul g r).symm⟩

private theorem isMulCommutative_map_conjSub {G H : Type*} [Group G] [Group H]
    {A : Subgroup G} (hA : IsMulCommutative A) (f : G →* H) :
    IsMulCommutative (A.map f) := by
  let g : A →* A.map f :=
    { toFun := fun a => ⟨f a.1, Subgroup.mem_map.mpr ⟨a.1, a.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp [map_mul] }
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨a, ha⟩, rfl⟩
  exact hg.isMulCommutative hA

private theorem isElemAbelian_map {G H : Type*} [Group G] [Group H] {p : ℕ}
    {A : Subgroup G} (hA : IsElemAbelian p A) (f : G →* H) :
    IsElemAbelian p (A.map f) := by
  refine ⟨isMulCommutative_map_conjSub hA.1 f, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [← map_pow, hA.2 y hy, map_one]

private theorem eq_or_eq_of_relIndex_prime {G : Type*} [Group G] {A B C : Subgroup G}
    (hAB : A ≤ B) (hBC : B ≤ C) (hp : (A.relIndex C).Prime) : B = A ∨ B = C := by
  have hmul : A.relIndex B * B.relIndex C = A.relIndex C :=
    Subgroup.relIndex_mul_relIndex A B C hAB hBC
  have h1 : A.relIndex B = 1 ∨ B.relIndex C = 1 := by
    have hprime : Nat.Prime (A.relIndex B * B.relIndex C) := hmul ▸ hp
    rcases Nat.prime_mul_iff.mp hprime with ⟨_, hb⟩ | ⟨_, ha⟩
    · exact Or.inr hb
    · exact Or.inl ha
  rcases h1 with h1 | h1
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hAB
  · right
    exact le_antisymm hBC (Subgroup.relIndex_eq_one.mp h1)

private theorem conjSub_eq_self_of_le_centralizer {G : Type*} [Group G] {x : G}
    {V A' : Subgroup G} (hx : ∀ v ∈ V, x * v = v * x) (hA' : A' ≤ V) :
    conjSub x A' = A' := by
  rw [conjSub]
  apply le_antisymm
  · rintro y ⟨a, ha, rfl⟩
    have hcomm := hx a (hA' ha)
    have hxa : x * a * x⁻¹ = a := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    show (MulAut.conj x) a ∈ A'
    rw [MulAut.conj_apply, hxa]
    exact ha
  · intro a ha
    refine ⟨a, ha, ?_⟩
    have hcomm := hx a (hA' ha)
    have hxa : x * a * x⁻¹ = a := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    show (MulAut.conj x) a = a
    rw [MulAut.conj_apply, hxa]

private theorem conj_injective_of_center_bot {G : Type} [Group G]
    (h : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [← h]
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := congrArg (fun f : MulAut G => f g) hx
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc g * x = x * g * x⁻¹ * x := by rw [h1]
    _ = x * g := by group

private theorem card_diag_range {R : Type} [Group R] {D : E6ThreeModel.FrameData R}
    (hD : D.Good) : Nat.card D.diag.range = 3 ^ 6 := by
  have h : Nat.card D.diag.range =
      Nat.card (Multiplicative (Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → ZMod 3)) := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hD.faithful,
      Subgroup.card_top]
  rw [h, Nat.card_congr Multiplicative.toAdd]
  norm_num [Nat.card_fun, ZMod.card, CFSG.Blueprint.Chevalley.Tag.rank]

private theorem classify6 {R : Type} [Group R] [Finite R] {D : E6ThreeModel.FrameData R}
    (hD : D.Good) {A : Subgroup (MulAut R)} (hAH : A ≤ D.H) (hAe : IsElemAbelian 3 A)
    (hr : Nat.card A = 3 ^ 6) :
    ∃ γ ∈ D.H, A.map (MulAut.conj γ).toMonoidHom = D.diag.range := by
  obtain ⟨γ, hγH, hγA⟩ := hD.shape A hAH hAe (by rw [hr]; norm_num)
  refine ⟨γ, hγH, ?_⟩
  set A' := A.map (MulAut.conj γ).toMonoidHom with hA'def
  have hA'V : A' ≤ D.diag.range := by
    intro x hx
    rw [hA'def, Subgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hγA a ha
  have hcardA' : Nat.card A' = 3 ^ 6 := by
    rw [hA'def, Subgroup.card_map_of_injective
      (by simpa using (MulAut.conj γ).injective)]
    exact hr
  exact Subgroup.eq_of_le_of_card_ge hA'V (by rw [hcardA', card_diag_range hD])

private theorem exists_conj_normalized_aux {R : Type} [Group R] [Finite R]
    (D : E6ThreeModel.FrameData R) (hD : D.Good)
    (hHnorm : D.H.Normal) (hInnH : InnerAut R ≤ D.H)
    (hHindex : ((InnerAut R).subgroupOf D.H).index = 3)
    {X : Subgroup (MulAut R)} (hXH : X ≤ D.H)
    (hXcent : ∀ x ∈ X, ∀ v ∈ D.diag.range, x * v = v * x)
    (hXnotInn : ¬ X ≤ InnerAut R)
    {A : Subgroup (MulAut R)} (hAH : A ≤ D.H) (hAe : IsElemAbelian 3 A)
    (hr : Nat.card A = 3 ^ 6)
    {a : MulAut R} {k : ℕ} (hk : a ^ 3 ^ k = 1)
    (hcount : ¬ 3 ∣ ((InnerAut R) ⊓
        Subgroup.normalizer (A : Set (MulAut R))).relIndex (InnerAut R)) :
    ∃ ι : R, a ∈ Subgroup.normalizer
      ((A.map (MulAut.conj (MulAut.conj ι : MulAut R)).toMonoidHom : Subgroup (MulAut R)) :
        Set (MulAut R)) := by
  haveI hInnNormal : (InnerAut R).Normal := innerAut_normal R
  haveI hHnormI : D.H.Normal := hHnorm
  have hHa : conjSub a D.H = D.H := by
    rw [conjSub]
    exact Subgroup.normal_iff_map_conj_eq.mp hHnormI a
  set B := conjSub a A with hBdef
  have hBAcard : Nat.card B = Nat.card A := by
    rw [hBdef, conjSub,
      Subgroup.card_map_of_injective (by simpa using (MulAut.conj a).injective)]
  have hBH : B ≤ D.H := by
    rw [hBdef, conjSub]
    calc A.map (MulAut.conj a).toMonoidHom
        ≤ D.H.map (MulAut.conj a).toMonoidHom := Subgroup.map_mono hAH
      _ = D.H := Subgroup.normal_iff_map_conj_eq.mp hHnormI a
  have hBe : IsElemAbelian 3 B := by
    rw [hBdef, conjSub]
    exact isElemAbelian_map hAe (MulAut.conj a).toMonoidHom
  have hBcard : Nat.card B = 3 ^ 6 := by rw [hBAcard]; exact hr
  obtain ⟨γ, hγH, hγ⟩ := classify6 hD hAH hAe hr
  obtain ⟨γ', hγ'H, hγ'⟩ := classify6 hD hBH hBe hBcard
  have hδA : conjSub a A = conjSub (γ'⁻¹ * γ) A := by
    have h1 : conjSub γ A = conjSub (γ' * a) A := by
      rw [show conjSub γ A = D.diag.range from hγ]
      rw [conjSub_mul, ← hBdef]
      exact hγ'.symm
    have h2 := congrArg (conjSub γ'⁻¹) h1
    rw [← conjSub_mul, ← conjSub_mul, show γ'⁻¹ * (γ' * a) = a by group] at h2
    exact h2.symm
  obtain ⟨x, hxX, hxNotInn⟩ : ∃ x ∈ X, x ∉ InnerAut R := by
    by_contra hcon
    apply hXnotInn
    intro y hy
    by_contra hy'
    exact hcon ⟨y, hy, hy'⟩
  have hn0N : γ⁻¹ * x * γ ∈ Subgroup.normalizer (A : Set (MulAut R)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hxcent : ∀ v ∈ D.diag.range, x * v = v * x := fun v hv => hXcent x hxX v hv
    have hfixV : conjSub x D.diag.range = D.diag.range :=
      conjSub_eq_self_of_le_centralizer hxcent le_rfl
    change conjSub (γ⁻¹ * x * γ) A = A
    rw [show γ⁻¹ * x * γ = γ⁻¹ * (x * γ) by group, conjSub_mul, conjSub_mul,
      show conjSub γ A = D.diag.range from hγ, hfixV,
      show D.diag.range = conjSub γ A from hγ.symm, ← conjSub_mul, inv_mul_cancel,
      conjSub_one]
  have hn0H : γ⁻¹ * x * γ ∈ D.H :=
    D.H.mul_mem (D.H.mul_mem (D.H.inv_mem hγH) (hXH hxX)) hγH
  have hn0NotInn : γ⁻¹ * x * γ ∉ InnerAut R := by
    rintro ⟨r₀, hr₀⟩
    apply hxNotInn
    refine ⟨γ r₀, ?_⟩
    calc MulAut.conj (γ r₀) = γ * MulAut.conj r₀ * γ⁻¹ := (conj_conj_mul γ r₀).symm
      _ = γ * (γ⁻¹ * x * γ) * γ⁻¹ := by rw [hr₀]
      _ = x := by group
  set K : Subgroup (MulAut R) :=
    InnerAut R ⊔ (Subgroup.normalizer (A : Set (MulAut R)) ⊓ D.H) with hKdef
  have hKle : K ≤ D.H := sup_le hInnH inf_le_right
  have hKne : K ≠ InnerAut R := by
    intro heq
    have hn0K : γ⁻¹ * x * γ ∈ K :=
      Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hn0N, hn0H⟩)
    rw [heq] at hn0K
    exact hn0NotInn hn0K
  have hK : K = D.H := by
    rcases eq_or_eq_of_relIndex_prime le_sup_left hKle
        (by rw [show (InnerAut R).relIndex D.H = ((InnerAut R).subgroupOf D.H).index from rfl,
                hHindex]; norm_num) with h | h
    · exact absurd h hKne
    · exact h
  have hδH : γ'⁻¹ * γ ∈ D.H := D.H.mul_mem (D.H.inv_mem hγ'H) hγH
  have hδK : γ'⁻¹ * γ ∈ K := by rw [hK]; exact hδH
  have hδKmem : γ'⁻¹ * γ ∈ (↑(InnerAut R ⊔
      (Subgroup.normalizer (A : Set (MulAut R)) ⊓ D.H)) : Set (MulAut R)) := by
    change γ'⁻¹ * γ ∈ K
    exact hδK
  rw [Subgroup.normal_mul] at hδKmem
  obtain ⟨y, hyInn, z, hzM, hyz⟩ := Set.mem_mul.mp hδKmem
  have hzN : z ∈ Subgroup.normalizer (A : Set (MulAut R)) := hzM.1
  have hzA : conjSub (z : MulAut R) A = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hzN
  have hyA : conjSub a A = conjSub (y : MulAut R) A := by
    rw [hδA, ← hyz, conjSub_mul, hzA]
  let yA : InnerAut R := ⟨y, hyInn⟩
  have hImgA : conjSub a A ∈ MulAction.orbit (InnerAut R) A := by
    rw [MulAction.mem_orbit_iff]
    exact ⟨yA, by change conjSub (yA : MulAut R) A = conjSub a A; exact hyA.symm⟩
  have hZinv : ∀ C ∈ MulAction.orbit (InnerAut R) A,
      conjSub a C ∈ MulAction.orbit (InnerAut R) A := by
    intro C hC
    rw [MulAction.mem_orbit_iff] at hC ⊢
    obtain ⟨g, hg⟩ := hC
    obtain ⟨r, hr⟩ := g.2
    obtain ⟨ι₀, hι₀⟩ := yA.2
    refine ⟨⟨MulAut.conj ((a r) * ι₀), ⟨(a r) * ι₀, rfl⟩⟩, ?_⟩
    change conjSub (MulAut.conj ((a r) * ι₀)) A = conjSub a C
    rw [← hg]
    change conjSub (MulAut.conj ((a r) * ι₀)) A =
      conjSub a (conjSub (g : MulAut R) A)
    rw [← hr, ← conjSub_mul]
    rw [show MulAut.conj ((a r) * ι₀) = MulAut.conj (a r) * MulAut.conj ι₀ from by rw [map_mul],
      conjSub_mul]
    rw [show conjSub (MulAut.conj ι₀) A = conjSub a A from by rw [hι₀]; exact hyA.symm,
      ← conjSub_mul]
    have hkey : a * MulAut.conj r = MulAut.conj (a r) * a := by
      rw [← conj_conj_mul]; group
    rw [hkey]
  have hZfin : (MulAction.orbit (InnerAut R) A).Finite := by
    change (Set.range (fun k : InnerAut R => conjSub (k : MulAut R) A)).Finite
    exact Set.finite_range _
  haveI : Fintype ↥(MulAction.orbit (InnerAut R) A) := hZfin.fintype
  have hZcard : Fintype.card ↥(MulAction.orbit (InnerAut R) A) =
      ((InnerAut R) ⊓ Subgroup.normalizer (A : Set (MulAut R))).relIndex (InnerAut R) := by
    have h1 : Fintype.card ↥(MulAction.orbit (InnerAut R) A) =
        (MulAction.orbit (InnerAut R) A).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    rw [h1, ← MulAction.index_stabilizer (G := InnerAut R) (x := A)]
    congr 1
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      exact ⟨k.2, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h⟩
    · rintro ⟨-, h⟩
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp h
  have hcardZ : ¬ 3 ∣ Fintype.card ↥(MulAction.orbit (InnerAut R) A) := by
    rw [hZcard]; exact hcount
  let f : ↥(MulAction.orbit (InnerAut R) A) → ↥(MulAction.orbit (InnerAut R) A) :=
    fun C => ⟨conjSub a C.1, hZinv C.1 C.2⟩
  have hfinj : Function.Injective f := by
    intro C1 C2 h
    apply Subtype.ext
    exact conjSub_injective a (congrArg Subtype.val h)
  let σ : Equiv.Perm ↥(MulAction.orbit (InnerAut R) A) := Equiv.ofBijective f
    ⟨hfinj, (Finite.injective_iff_surjective.mp hfinj)⟩
  have hiter : ∀ m : ℕ, ∀ C : ↥(MulAction.orbit (InnerAut R) A),
      (f^[m] C).1 = conjSub (a ^ m) C.1 := by
    intro m
    induction m with
    | zero => intro C; rw [Function.iterate_zero, pow_zero, conjSub_one]; rfl
    | succ m ih =>
        intro C
        rw [Function.iterate_succ_apply']
        change conjSub a ((f^[m] C).1) = conjSub (a ^ (m + 1)) C.1
        rw [ih, ← conjSub_mul, ← pow_succ']
  have hpow : ∀ m : ℕ, ∀ C : ↥(MulAction.orbit (InnerAut R) A), (σ ^ m) C = (f^[m]) C := by
    intro m
    induction m with
    | zero => intro C; rfl
    | succ m ih =>
        intro C
        rw [pow_succ, Equiv.Perm.mul_apply, ih]
        change f^[m] (f C) = f^[m+1] C
        rw [Function.iterate_succ_apply]
  have hσ : σ ^ 3 ^ k = 1 := by
    apply Equiv.ext
    intro C
    rw [hpow]
    apply Subtype.ext
    show (f^[3 ^ k] C).1 = C.1
    rw [hiter, hk, conjSub_one]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨C, hCfix⟩ := Equiv.Perm.exists_fixed_point_of_prime
    (α := ↥(MulAction.orbit (InnerAut R) A)) hcardZ hσ
  have hfC : conjSub a C.1 = C.1 := congrArg Subtype.val hCfix
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp C.2
  obtain ⟨r, hr⟩ := g.2
  refine ⟨r, ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hg' : conjSub (MulAut.conj r) A = C.1 := by
    rw [hr]
    change (g : MulAut R) • A = C.1
    exact hg
  change conjSub a (conjSub (MulAut.conj r) A) = conjSub (MulAut.conj r) A
  rw [hg', hfC]

end CFSG.StandardType

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem exists_conj_normalized_twE6
    {K : Type} [Field K] [Finite K] (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) {A : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hA : IsElemAbelian 3 A)
    (hI : (A : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n) (hr : Nat.card A = 3 ^ 6) {a : MulAut (TwE6Delta.RecipeR K n)} {k : ℕ} (hk : a ^ 3 ^ k = 1) :
    ∃ ι : TwE6Delta.RecipeR K n, a ∈ Subgroup.normalizer
      ((A.map (MulAut.conj (MulAut.conj ι : MulAut (TwE6Delta.RecipeR K n))).toMonoidHom : Subgroup (MulAut (TwE6Delta.RecipeR K n))) :
        Set (MulAut (TwE6Delta.RecipeR K n))) := by
  haveI : Finite (TwE6Delta.RecipeR K n) := TwE6Delta.finite_recipeR hK
  obtain ⟨D, X, hGood, hDH, hHnum, hH3R, hXH, hXcard, hXcent, hXnotInn, -⟩ :=
    exists_langFrame_recipeR (K := K) n hn hK h3
  have hAH : A ≤ D.H := by
    intro φ hφ
    have hφI : φ ∈ (D.H : Set (MulAut (TwE6Delta.RecipeR K n))) := by
      rw [hDH]; exact hI hφ
    exact hφI
  have hInnH : InnerAut (TwE6Delta.RecipeR K n) ≤ D.H := by
    intro φ hφ
    have hφI : φ ∈ (D.H : Set (MulAut (TwE6Delta.RecipeR K n))) := by
      rw [hDH]
      obtain ⟨r, rfl⟩ := hφ
      exact Subgroup.subset_closure (Set.mem_union_left _ ⟨r, rfl⟩)
    exact hφI
  have hHnorm : D.H.Normal := by
    have hN := InndiagE6.ggInndiagNormal_twE6 hn K hK
    have hggNormal :
        (ggInndiag (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)).Normal :=
      ⟨fun x hx g => hN.conj_mem g hx⟩
    have hggEq : ggInndiag (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) = D.H := by
      apply le_antisymm
      · rw [ggInndiag]
        apply sup_le hInnH
        rw [Subgroup.closure_le]
        intro x hx
        rw [hDH]
        exact hx
      · intro x hx
        rw [ggInndiag]
        have hx' : x ∈ (D.H : Set (MulAut (TwE6Delta.RecipeR K n))) := hx
        rw [hDH] at hx'
        exact Subgroup.mem_sup_right (Subgroup.subset_closure hx')
    exact hggEq ▸ hggNormal
  have hInnCard : Nat.card (InnerAut (TwE6Delta.RecipeR K n)) =
      Nat.card (TwE6Delta.RecipeR K n) := by
    have hinj : Function.Injective
        (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)) :=
      conj_injective_of_center_bot hGood.center
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hHindex : ((InnerAut (TwE6Delta.RecipeR K n)).subgroupOf D.H).index = 3 := by
    have hcardSub : Nat.card ((InnerAut (TwE6Delta.RecipeR K n)).subgroupOf D.H) =
        Nat.card (TwE6Delta.RecipeR K n) := by
      calc Nat.card ((InnerAut (TwE6Delta.RecipeR K n)).subgroupOf D.H)
          = Nat.card (((InnerAut (TwE6Delta.RecipeR K n)).subgroupOf D.H).map D.H.subtype) :=
            (Subgroup.card_subtype D.H _).symm
        _ = Nat.card (InnerAut (TwE6Delta.RecipeR K n)) := by
              rw [Subgroup.map_subgroupOf_eq_of_le hInnH]
        _ = Nat.card (TwE6Delta.RecipeR K n) := hInnCard
    have h := Subgroup.card_mul_index ((InnerAut (TwE6Delta.RecipeR K n)).subgroupOf D.H)
    rw [hcardSub, hH3R] at h
    rw [mul_comm 3 (Nat.card (TwE6Delta.RecipeR K n))] at h
    exact Nat.mul_left_cancel Nat.card_pos h
  have hcount := not_three_dvd_relIndex_automizer_twE6 (K := K) n hn hK h3 hA hI hr
  exact exists_conj_normalized_aux D hGood hHnorm hInnH hHindex hXH hXcent hXnotInn hAH hA hr hk
    hcount

end CFSG.StandardType
