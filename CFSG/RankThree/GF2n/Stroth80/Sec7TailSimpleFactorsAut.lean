module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailSimpleFactors
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.Models.PGLSimple
public import CFSG.RankThree.GF2n.Stroth80.Sec7ArtinOrders
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCorBList

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem conjSubgroup_mul_eq {Y : Type} [Group Y] (x y : Y) (A : Subgroup Y) :
    conjSubgroup (x * y) A = conjSubgroup x (conjSubgroup y A) := by
  ext z
  have e : (x * y)⁻¹ * z * (x * y) = y⁻¹ * (x⁻¹ * z * x) * y := by group
  rw [mem_conjSubgroup, mem_conjSubgroup, mem_conjSubgroup, e]

theorem normalizer_of_conjSubgroup_eq_factor {Y : Type} [Group Y] {A : Subgroup Y} {y : Y}
    (hy : conjSubgroup y A = A) : y ∈ Subgroup.normalizer (A : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : y * x * y⁻¹ ∈ conjSubgroup y A ↔ x ∈ A := by
    rw [mem_conjSubgroup, show y⁻¹ * (y * x * y⁻¹) * y = x by group]
  rw [hy] at h1
  exact h1.symm

theorem conjSubgroup_eq_factor_of_normalizer {Y : Type} [Group Y] {A : Subgroup Y} {y : Y}
    (hy : y ∈ Subgroup.normalizer (A : Set Y)) : conjSubgroup y A = A := by
  ext z
  rw [mem_conjSubgroup]
  have h1 := Subgroup.mem_normalizer_iff.mp hy (y⁻¹ * z * y)
  rw [show y * (y⁻¹ * z * y) * y⁻¹ = z by group] at h1
  exact h1

theorem normal_eq_top_of_index_le {E S : Type} [Group E] [Finite E] [Group S] [Finite S]
    [IsSimpleGroup S] (hS : Nat.factorial 9 < Nat.card S) (hE : commutator E = ⊤) (θ : E →* S)
    (hθ : Function.Surjective θ) (hker : IsPGroup 2 θ.ker) (C : Subgroup E) [C.Normal]
    (hC : C.index ≤ Nat.factorial 9) : C = ⊤ := by
  haveI : Group.IsPerfect E := Group.isPerfect_def.mpr hE
  by_cases hCθ : C ≤ θ.ker
  · exfalso
    have hφ : Function.Surjective (QuotientGroup.lift C θ hCθ) := by
      intro s
      obtain ⟨x, rfl⟩ := hθ s
      exact ⟨(x : E ⧸ C), QuotientGroup.lift_mk (N := C) hCθ x⟩
    have h1 : Nat.card S ≤ Nat.card (E ⧸ C) := Nat.card_le_card_of_surjective _ hφ
    have h2 : Nat.card (E ⧸ C) ≤ Nat.factorial 9 := hC
    exact absurd (lt_of_lt_of_le hS (le_trans h1 h2)) (lt_irrefl _)
  · obtain ⟨c0, hc0C, hc0⟩ := SetLike.not_le_iff_exists.mp hCθ
    have hne : C.map θ ≠ ⊥ := by
      intro hbot
      apply hc0
      have hmem : θ c0 ∈ C.map θ := Subgroup.mem_map_of_mem θ hc0C
      rw [hbot, Subgroup.mem_bot] at hmem
      exact MonoidHom.mem_ker.mpr hmem
    haveI : (C.map θ).Normal := Subgroup.Normal.map ‹C.Normal› θ hθ
    have htop : C.map θ = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map θ)).resolve_left hne
    have hcov : ∀ x : E, ∃ c ∈ C, θ c = θ x := by
      intro x
      have hx : θ x ∈ C.map θ := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
      exact ⟨c, hc, hcx⟩
    have h2 : IsPGroup 2 (E ⧸ C) := by
      refine isPGroup_iff_pow_pow_eq_one.mpr fun q => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨c, hc, hcx⟩ := hcov x
      have hk : x * c⁻¹ ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcx, mul_inv_cancel]
      obtain ⟨n, hn⟩ := (isPGroup_iff_pow_pow_eq_one.mp hker) ⟨x * c⁻¹, hk⟩
      refine ⟨n, ?_⟩
      have hn' : (x * c⁻¹) ^ 2 ^ n = 1 := by
        have h1 := congrArg Subtype.val hn
        simpa using h1
      have hmk : ((x * c⁻¹ * c : E) : E ⧸ C) = ((x * c⁻¹ : E) : E ⧸ C) :=
        QuotientGroup.mk_mul_of_mem (x * c⁻¹) hc
      rw [inv_mul_cancel_right] at hmk
      rw [hmk, ← QuotientGroup.mk_pow, hn', QuotientGroup.mk_one]
    have hsub : Subsingleton (E ⧸ C) :=
      not_nontrivial_iff_subsingleton.mp fun _ =>
        Group.IsPerfect.not_isNilpotent (E ⧸ C) (IsPGroup.isNilpotent h2)
    rw [eq_top_iff]
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

theorem no_small_index {E S : Type} [Group E] [Finite E] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : Nat.factorial 9 < Nat.card S) (hE : commutator E = ⊤) (θ : E →* S)
    (hθ : Function.Surjective θ) (hker : IsPGroup 2 θ.ker) (E₁ : Subgroup E)
    (hidx : E₁.index ≤ 9) : E₁ = ⊤ := by
  have hcore : E₁.normalCore = ⊤ :=
    normal_eq_top_of_index_le hS hE θ hθ hker E₁.normalCore
      (le_trans (Subgroup.index_normalCore_le_factorial_index E₁) (Nat.factorial_le hidx))
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ E₁.normalCore := by
    rw [hcore]
    exact Subgroup.mem_top x
  exact Subgroup.normalCore_le E₁ hx

theorem fix_factors {Y : Type} [Group Y] [Finite Y] {ι : Type} [Fintype ι] {Gs : Subgroup Y}
    {X : ι → Subgroup Y} (h : SimpleFactors Gs X) (E : Subgroup Y) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hS : Nat.factorial 9 < Nat.card S) (hE : commutator ↥E = ⊤)
    (θ : ↥E →* S) (hθ : Function.Surjective θ) (hker : IsPGroup 2 θ.ker)
    (hι : Fintype.card ι ≤ 9) : ∀ e ∈ E, ∀ i, conjSubgroup e (X i) = X i := by
  intro e0 he0 i
  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Subgroup ↥E,
      E₁ = (Subgroup.normalizer (X i : Set Y)).subgroupOf E := ⟨_, rfl⟩
  have hmem : ∀ a : ↥E, a ∈ E₁ ↔ (a : Y) ∈ Subgroup.normalizer (X i : Set Y) := by
    intro a
    rw [hE₁, Subgroup.mem_subgroupOf]
  have hone : ∀ B : Subgroup Y, conjSubgroup (1 : Y) B = B := by
    intro B
    ext z
    rw [mem_conjSubgroup]
    simp
  have hfix : ∀ a b : Y, conjSubgroup a (X i) = conjSubgroup b (X i) →
      conjSubgroup (a⁻¹ * b) (X i) = X i := by
    intro a b hab
    calc conjSubgroup (a⁻¹ * b) (X i) = conjSubgroup a⁻¹ (conjSubgroup b (X i)) :=
          conjSubgroup_mul_eq a⁻¹ b (X i)
      _ = conjSubgroup a⁻¹ (conjSubgroup a (X i)) := by rw [hab]
      _ = conjSubgroup (a⁻¹ * a) (X i) := (conjSubgroup_mul_eq a⁻¹ a (X i)).symm
      _ = conjSubgroup 1 (X i) := by rw [inv_mul_cancel]
      _ = X i := hone (X i)
  have hfix2 : ∀ a b : Y, conjSubgroup (a⁻¹ * b) (X i) = X i →
      conjSubgroup a (X i) = conjSubgroup b (X i) := by
    intro a b hab
    calc conjSubgroup a (X i) = conjSubgroup a (conjSubgroup (a⁻¹ * b) (X i)) := by
          rw [hab]
      _ = conjSubgroup (a * (a⁻¹ * b)) (X i) := (conjSubgroup_mul_eq a (a⁻¹ * b) (X i)).symm
      _ = conjSubgroup b (X i) := by rw [mul_inv_cancel_left]
  have hidx : E₁.index ≤ 9 := by
    choose g hg using fun a : ↥E => factor_conj_exists h (a : Y) i
    have hgE : ∀ a b : ↥E, a⁻¹ * b ∈ E₁ → g a = g b := by
      intro a b hab
      rw [hmem, Subgroup.coe_mul, Subgroup.coe_inv] at hab
      apply h.injective
      rw [← hg a, ← hg b]
      exact hfix2 _ _ (conjSubgroup_eq_factor_of_normalizer hab)
    obtain ⟨F, hF⟩ : ∃ F : ↥E ⧸ E₁ → ι, ∀ a : ↥E, F (a : ↥E ⧸ E₁) = g a :=
      ⟨Quotient.lift (s := QuotientGroup.leftRel E₁) g
        (fun a b hab => hgE a b (QuotientGroup.leftRel_apply.mp hab)), fun a => rfl⟩
    have hFinj : Function.Injective F := by
      intro q q'
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q'
      intro hab
      rw [hF, hF] at hab
      rw [QuotientGroup.eq, hmem, Subgroup.coe_mul, Subgroup.coe_inv]
      apply normalizer_of_conjSubgroup_eq_factor
      apply hfix
      rw [hg a, hg b, hab]
    have hcardι : Nat.card ι ≤ 9 := by
      rw [Nat.card_eq_fintype_card]
      exact hι
    show Nat.card (↥E ⧸ E₁) ≤ 9
    exact le_trans (Nat.card_le_card_of_injective F hFinj) hcardι
  have hfull : E₁ = ⊤ := no_small_index hS hE θ hθ hker E₁ hidx
  have he1 : (⟨e0, he0⟩ : ↥E) ∈ E₁ := by
    rw [hfull]
    exact Subgroup.mem_top _
  exact conjSubgroup_eq_factor_of_normalizer ((hmem _).mp he1)

theorem le_of_fix_inner {Y : Type} [Group Y] [Finite Y] {ι : Type} [Fintype ι] {Gs : Subgroup Y}
    {X : ι → Subgroup Y} (h : SimpleFactors Gs X) {π : ι → ↥Gs →* Y} (hπ : IsProj Gs X π)
    (hOut : ∀ i, ∀ P : Subgroup (MulAut ↥(X i)), commutator ↥P = ⊤ →
      P ≤ (MulAut.conj : ↥(X i) →* MulAut ↥(X i)).range)
    (hC : ∀ c : Y, (∀ s ∈ Gs, c * s = s * c) → c = 1) (E : Subgroup Y)
    (hE : commutator ↥E = ⊤) (hfix : ∀ e ∈ E, ∀ i, conjSubgroup e (X i) = X i) : E ≤ Gs := by
  have hcent : ∀ i (w : ↥Gs), π i w = 1 → ∀ y ∈ X i, (w : Y) * y = y * (w : Y) := by
    intro i w hw y hy
    have hyG : y ∈ Gs := h.le i hy
    have key : w * ⟨y, hyG⟩ = ⟨y, hyG⟩ * w := by
      apply hπ.inj
      intro j
      rw [map_mul, map_mul]
      by_cases hji : j = i
      · rw [hji, hw, hπ.self i ⟨y, hyG⟩ hy, one_mul, mul_one]
      · rw [hπ.other j i hji ⟨y, hyG⟩ hy, mul_one, one_mul]
    exact congrArg Subtype.val key
  have hmemE : ∀ e ∈ E, ∀ i, ∀ x ∈ X i, e * x * e⁻¹ ∈ X i := by
    intro e he i x hx
    rw [← hfix e he i, mem_conjSubgroup,
      show e⁻¹ * (e * x * e⁻¹) * e = x by group]
    exact hx
  have hmemE' : ∀ e ∈ E, ∀ i, ∀ x ∈ X i, e⁻¹ * x * e ∈ X i := by
    intro e he i x hx
    rw [← mem_conjSubgroup, hfix e he i]
    exact hx
  have hα : ∀ i, ∃ α : ↥E →* MulAut ↥(X i), ∀ (e : ↥E) (x : ↥(X i)),
      ((α e x : ↥(X i)) : Y) = (e : Y) * (x : Y) * (e : Y)⁻¹ := by
    intro i
    refine ⟨MonoidHom.mk' (fun e : ↥E => (
      { toFun := fun x => ⟨(e : Y) * (x : Y) * (e : Y)⁻¹, hmemE (e : Y) e.2 i x x.2⟩
        invFun := fun x => ⟨(e : Y)⁻¹ * (x : Y) * (e : Y), hmemE' (e : Y) e.2 i x x.2⟩
        left_inv := fun x => Subtype.ext (by group)
        right_inv := fun x => Subtype.ext (by group)
        map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) } :
          ↥(X i) ≃* ↥(X i))) ?_, fun e x => rfl⟩
    intro a b
    ext x
    show (a : Y) * (b : Y) * (x : Y) * ((a : Y) * (b : Y))⁻¹
      = (a : Y) * ((b : Y) * (x : Y) * (b : Y)⁻¹) * (a : Y)⁻¹
    group
  have hperf : ∀ i (α : ↥E →* MulAut ↥(X i)), commutator ↥(α.range) = ⊤ := by
    intro i α
    have hrt : α.rangeRestrict.range = ⊤ :=
      MonoidHom.range_eq_top.mpr (MonoidHom.rangeRestrict_surjective α)
    have h1 := map_commutator_eq ↥E α.rangeRestrict
    rw [hE, ← MonoidHom.range_eq_map, hrt] at h1
    exact h1.symm
  intro e he
  have hinner : ∀ i, ∃ g : ↥(X i), ∀ x : ↥(X i),
      e * (x : Y) * e⁻¹ = (g : Y) * (x : Y) * (g : Y)⁻¹ := by
    intro i
    obtain ⟨α, hαe⟩ := hα i
    have hmem : α ⟨e, he⟩ ∈ α.range := MonoidHom.mem_range.mpr ⟨⟨e, he⟩, rfl⟩
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hOut i α.range (hperf i α) hmem)
    refine ⟨g, fun x => ?_⟩
    have key := congrArg (fun φ : MulAut ↥(X i) => ((φ x : ↥(X i)) : Y)) hg
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at key
    rw [hαe] at key
    exact key.symm
  choose gi hgi using hinner
  obtain ⟨g, hg⟩ := hπ.surj (fun i => (gi i : Y)) (fun i => (gi i).2)
  have hg' : ∀ i, π i g = (gi i : Y) := hg
  have hcomm : ∀ s ∈ Gs, Commute ((g : Y)⁻¹ * e) s := by
    intro s hs
    rw [← h.gen] at hs
    refine Subgroup.iSup_induction X (C := fun s => Commute ((g : Y)⁻¹ * e) s) hs ?_ ?_ ?_
    · intro i x hx
      obtain ⟨gh, hgh⟩ : ∃ gh : ↥Gs, (gh : Y) = (gi i : Y) :=
        ⟨⟨(gi i : Y), h.le i (gi i).2⟩, rfl⟩
      have hπgh : π i gh = (gi i : Y) := by
        rw [hπ.self i gh (by rw [hgh]; exact (gi i).2), hgh]
      obtain ⟨u, hu⟩ : ∃ u : ↥Gs, u = g * gh⁻¹ := ⟨_, rfl⟩
      have huπ : π i u = 1 := by
        rw [hu, map_mul, map_inv, hg' i, hπgh, mul_inv_cancel]
      have huY : (u : Y) = (g : Y) * (gi i : Y)⁻¹ := by
        rw [hu, Subgroup.coe_mul, Subgroup.coe_inv, hgh]
      have hy : (gi i : Y) * x * (gi i : Y)⁻¹ ∈ X i :=
        (X i).mul_mem ((X i).mul_mem (gi i).2 hx) ((X i).inv_mem (gi i).2)
      have hcu := hcent i u huπ _ hy
      have hgu : (g : Y) = (u : Y) * (gi i : Y) := by
        rw [huY]
        group
      have hgx : (g : Y) * x * (g : Y)⁻¹ = (gi i : Y) * x * (gi i : Y)⁻¹ := by
        rw [hgu]
        calc (u : Y) * (gi i : Y) * x * ((u : Y) * (gi i : Y))⁻¹
            = (u : Y) * ((gi i : Y) * x * (gi i : Y)⁻¹) * (u : Y)⁻¹ := by group
          _ = (gi i : Y) * x * (gi i : Y)⁻¹ := by rw [hcu]; group
      have hEG : e * (x : Y) * e⁻¹ = (g : Y) * x * (g : Y)⁻¹ :=
        (hgi i ⟨x, hx⟩).trans hgx.symm
      have hex : e * x = (g : Y) * x * (g : Y)⁻¹ * e := by
        rw [← hEG]
        group
      show (g : Y)⁻¹ * e * x = x * ((g : Y)⁻¹ * e)
      rw [mul_assoc, hex]
      group
    · exact Commute.one_right _
    · intro x y hx hy
      exact Commute.mul_right hx hy
  have hc1 : (g : Y)⁻¹ * e = 1 := hC ((g : Y)⁻¹ * e) hcomm
  have hge : (g : Y) = e := inv_mul_eq_one.mp hc1
  rw [← hge]
  exact g.2

theorem solvable_pi_of_fintype {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    (hG : ∀ i, Group.IsSolvable (G i)) : Group.IsSolvable (∀ i, G i) := by
  choose n hn using fun i => (hG i).solvable
  refine ⟨⟨(Finset.univ : Finset ι).sup n, ?_⟩⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  funext i
  have h1 : x i ∈ derivedSeries (G i) ((Finset.univ : Finset ι).sup n) :=
    map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom G i) ((Finset.univ : Finset ι).sup n)
      (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have h2 : derivedSeries (G i) ((Finset.univ : Finset ι).sup n) ≤ derivedSeries (G i) (n i) :=
    derivedSeries_antitone (G i) (Finset.le_sup (f := n) (Finset.mem_univ i))
  rw [hn i] at h2
  exact Subgroup.mem_bot.mp (h2 h1)

theorem solvable_normalizer_inf {Y : Type} [Group Y] [Finite Y] {ι : Type} [Fintype ι]
    {Gs : Subgroup Y} {X : ι → Subgroup Y} (h : SimpleFactors Gs X) {π : ι → ↥Gs →* Y}
    (hπ : IsProj Gs X π) (V : Subgroup Y) (hVG : V ≤ Gs) (hV2 : ∀ v ∈ V, v * v = 1)
    (hBor : ∀ i, ∀ P : Subgroup Y, P ≤ X i → P ≠ ⊥ → IsPGroup 2 P →
      Group.IsSolvable ↥(Subgroup.normalizer ((P.subgroupOf (X i) : Subgroup ↥(X i)) :
        Set ↥(X i))))
    (hne : ∀ i, ∃ v : ↥Gs, (v : Y) ∈ V ∧ π i v ≠ 1) :
    Group.IsSolvable ↥(Subgroup.normalizer (V : Set Y) ⊓ Gs) := by
  obtain ⟨Vi, hVi⟩ : ∃ Vi : ι → Subgroup Y,
      ∀ i (y : Y), y ∈ Vi i ↔ ∃ v : ↥Gs, (v : Y) ∈ V ∧ π i v = y :=
    ⟨fun i => (V.subgroupOf Gs).map (π i), fun i y => by
      simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]⟩
  have hViX : ∀ i, ∀ y ∈ Vi i, y ∈ X i := by
    intro i y hy
    obtain ⟨v, -, rfl⟩ := (hVi i y).1 hy
    exact hπ.mem i v
  have hViNe : ∀ i, Vi i ≠ ⊥ := by
    intro i hbot
    obtain ⟨v, hvV, hv1⟩ := hne i
    have hmem : π i v ∈ Vi i := (hVi i _).2 ⟨v, hvV, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hv1 hmem
  have hViSq : ∀ i, ∀ x ∈ Vi i, x * x = 1 := by
    intro i x hx
    obtain ⟨w, hw, rfl⟩ := (hVi i _).1 hx
    have hww : w * w = 1 := Subtype.ext (hV2 _ hw)
    rw [← map_mul, hww, map_one]
  have hViP : ∀ i, IsPGroup 2 ↥(Vi i) := by
    intro i g
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext (by simpa using hViSq i _ g.2)
  obtain ⟨N, hN⟩ : ∃ N : ∀ i, Subgroup ↥(X i), ∀ i, N i = Subgroup.normalizer
      (((Vi i).subgroupOf (X i) : Subgroup ↥(X i)) : Set ↥(X i)) :=
    ⟨fun i => Subgroup.normalizer (((Vi i).subgroupOf (X i) : Subgroup ↥(X i)) : Set ↥(X i)),
      fun i => rfl⟩
  have hsolv : ∀ i, Group.IsSolvable ↥(N i) := fun i => by
    rw [hN i]
    exact hBor i (Vi i) (by intro y hy; exact hViX i y hy) (hViNe i) (hViP i)
  haveI hpi : Group.IsSolvable (∀ i, ↥(N i)) :=
    solvable_pi_of_fintype (G := fun i => ↥(N i)) hsolv
  obtain ⟨A, hA⟩ : ∃ A : Subgroup Y, A = Subgroup.normalizer (V : Set Y) ⊓ Gs := ⟨_, rfl⟩
  rw [← hA]
  have hAG : ∀ a ∈ A, a ∈ Gs := by
    intro a ha
    rw [hA, Subgroup.mem_inf] at ha
    exact ha.2
  have hAN : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V := by
    intro a ha v hv
    rw [hA, Subgroup.mem_inf] at ha
    exact (Subgroup.mem_normalizer_iff.mp ha.1 v).1 hv
  obtain ⟨ιA, hιA⟩ : ∃ ι' : ↥A →* ↥Gs, ∀ a : ↥A, ((ι' a : ↥Gs) : Y) = (a : Y) :=
    ⟨Subgroup.inclusion (show A ≤ Gs by intro y hy; exact hAG y hy), fun a => rfl⟩
  have hconjV : ∀ (a : ↥A) (i : ι), ∀ y ∈ Vi i, π i (ιA a) * y * (π i (ιA a))⁻¹ ∈ Vi i := by
    intro a i y hy
    obtain ⟨w, hw, rfl⟩ := (hVi i y).1 hy
    refine (hVi i _).2 ⟨ιA a * w * (ιA a)⁻¹, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hιA]
      exact hAN (a : Y) a.2 _ hw
    · simp only [map_mul, map_inv]
  have hcore : ∀ (a : ↥A) (i : ι) (y : Y),
      y ∈ Vi i ↔ π i (ιA a) * y * (π i (ιA a))⁻¹ ∈ Vi i := by
    intro a i y
    constructor
    · exact hconjV a i y
    · intro hy
      have h2 := hconjV a⁻¹ i _ hy
      have e : π i (ιA a⁻¹) * (π i (ιA a) * y * (π i (ιA a))⁻¹) * (π i (ιA a⁻¹))⁻¹ = y := by
        simp only [map_inv]
        group
      rw [e] at h2
      exact h2
  have hmemN : ∀ (a : ↥A) (i : ι), (⟨π i (ιA a), hπ.mem i (ιA a)⟩ : ↥(X i)) ∈ N i := by
    intro a i
    rw [hN i, Subgroup.mem_normalizer_iff]
    intro g
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hcore a i (g : Y)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥A →* (∀ i, ↥(N i)),
      ∀ a i, (((ρ a i : ↥(N i)) : ↥(X i)) : Y) = π i (ιA a) :=
    ⟨MonoidHom.mk' (fun a i => ⟨⟨π i (ιA a), hπ.mem i (ιA a)⟩, hmemN a i⟩) (by
      intro a b
      funext i
      apply Subtype.ext
      apply Subtype.ext
      simp [map_mul]), fun a i => rfl⟩
  have hρinj : Function.Injective ρ := by
    intro a b hab
    have hi : ∀ i, π i (ιA a) = π i (ιA b) := by
      intro i
      rw [← hρ, ← hρ, hab]
    have hab' : ιA a = ιA b := hπ.inj (ιA a) (ιA b) hi
    have hab'' : (a : Y) = (b : Y) := by
      have h3 := congrArg (fun z : ↥Gs => (z : Y)) hab'
      simpa only [hιA] using h3
    exact Subtype.ext hab''
  exact Group.isSolvable_of_isSolvable_injective hρinj

theorem normalTwoComplement_odd_le {X : Type} [Group X] [Finite X] (O : Subgroup X) [O.Normal]
    (hq : IsPGroup 2 (X ⧸ O)) (N : Subgroup X) (hN : Odd (Nat.card N)) : N ≤ O := by
  intro y hy
  have h1 : orderOf y ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hy
  have hodd : Odd (orderOf y) := Odd.of_dvd_nat hN h1
  have h2 : orderOf (y : X ⧸ O) ∣ orderOf y := orderOf_map_dvd (QuotientGroup.mk' O) y
  obtain ⟨k, hk⟩ := hq (y : X ⧸ O)
  have h3 : orderOf (y : X ⧸ O) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf (y : X ⧸ O)) 2 :=
    Nat.coprime_two_right.mpr (Odd.of_dvd_nat hodd h2)
  have h4 : Nat.Coprime (orderOf (y : X ⧸ O)) (2 ^ k) := Nat.Coprime.pow_right k hcop
  have h5 : orderOf (y : X ⧸ O) = 1 := Nat.Coprime.eq_one_of_dvd h4 h3
  exact (QuotientGroup.eq_one_iff y).mp (orderOf_eq_one_iff.mp h5)

theorem eq_bot_of_normalTwoComplement {Y : Type} [Group Y] [Finite Y] (Gs : Subgroup Y)
    [Gs.Normal] (hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥) (X : Subgroup ↥Gs)
    [X.Normal] (h : HasNormalTwoComplement ↥X) : X = ⊥ := by
  obtain ⟨O, hOn, hOodd, hOn', hOq⟩ := h
  obtain ⟨M, hM⟩ : ∃ M : Subgroup ↥Gs, M = O.map X.subtype := ⟨_, rfl⟩
  have hMX : M ≤ X := by
    rw [hM]
    intro m hm
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hm
    exact x.2
  have hMcard : Odd (Nat.card M) := by
    rw [hM, Subgroup.card_map_of_injective X.subtype_injective]
    exact hOodd
  have hconjX : ∀ g : ↥Gs, conjSubgroup g M ≤ X := by
    intro g y hy
    have h1 := Subgroup.Normal.conj_mem ‹X.Normal› _ (hMX (mem_conjSubgroup.mp hy)) g
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h1
  have hconj : ∀ g : ↥Gs, conjSubgroup g M ≤ M := by
    intro g y hy
    have hyX : y ∈ X := hconjX g hy
    have hcardconj : Nat.card ↥(conjSubgroup g M) = Nat.card ↥M :=
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (K := M)
        (MulAut.conj g).injective
    have hN : Odd (Nat.card ↥((conjSubgroup g M).subgroupOf X)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hconjX g)).toEquiv, hcardconj]
      exact hMcard
    have hsub := normalTwoComplement_odd_le O hOq _ hN
    have hmem : (⟨y, hyX⟩ : ↥X) ∈ O := hsub (Subgroup.mem_subgroupOf.mpr hy)
    rw [hM]
    exact Subgroup.mem_map.mpr ⟨⟨y, hyX⟩, hmem, rfl⟩
  have hMn : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g * n * g⁻¹ ∈ conjSubgroup g M := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * n * g⁻¹) * g = n by group]
      exact hn
    exact hconj g h1
  have hM0 : M = ⊥ := by
    have hpc : CFSG.pPrimeCore 2 ↥Gs = ⊥ := corB_pPrimeCore_sub_eq_bot hO Gs
    exact CFSG.pPrimeCore_eq_bot_iff.mp hpc M hMn (Nat.coprime_two_left.mpr hMcard)
  have hO0 : O = ⊥ := by
    have hmap : O.map X.subtype = ⊥ := by
      rw [← hM]
      exact hM0
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hmap
  have hXp : IsPGroup 2 ↥X := by
    intro x
    obtain ⟨k, hk⟩ := hOq (x : ↥X ⧸ O)
    refine ⟨k, ?_⟩
    have h1 : ((x ^ 2 ^ k : ↥X) : ↥X ⧸ O) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hk
    have h2 : x ^ 2 ^ k ∈ O := (QuotientGroup.eq_one_iff _).mp h1
    rw [hO0, Subgroup.mem_bot] at h2
    exact h2
  have hXle : X ≤ CFSG.pCore 2 ↥Gs :=
    le_sSup (show X ∈ {K : Subgroup ↥Gs | K.Normal ∧ IsPGroup 2 K} from ⟨inferInstance, hXp⟩)
  rw [corB_pCore_sub_eq_bot hO2 Gs, le_bot_iff] at hXle
  exact hXle

theorem tim77Cor2BetaList_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Tim77Cor2BetaList X) : Tim77Cor2BetaList Y := by
  rcases h with ⟨m, hm, hc⟩ | ⟨m, hm, hc⟩ | ⟨m, hm, hc⟩
  · exact Or.inl ⟨m, hm, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e hc⟩
  · exact Or.inr (Or.inl ⟨m, hm, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e hc⟩)
  · exact Or.inr (Or.inr ⟨m, hm, CFSG.Blueprint.LieModel.of_mulEquiv e hc⟩)

theorem beta_facts (hBorel : BorelRankOneSolvableStatement)
    {H : Type} [Group H] [Finite H] (hcov : IsCoveringOf Tim77Cor2BetaList H)
    (hZ : ∀ z : H, (∀ g : H, z * g = g * z) → z = 1) :
    ListGroup H ∧ IsSimpleGroup H ∧
      ∀ P : Subgroup H, P ≠ ⊥ → IsPGroup 2 P →
        Group.IsSolvable ↥(Subgroup.normalizer (P : Set H)) := by
  obtain ⟨-, Z, hZc, hZn, hP⟩ := hcov
  have hZbot : Z = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact hZ z fun g => (Subgroup.mem_center_iff.mp (hZc hz) g).symm
  subst hZbot
  have hH : Tim77Cor2BetaList H := tim77Cor2BetaList_of_mulEquiv QuotientGroup.quotientBot hP
  rcases hH with ⟨m, hm, hc⟩ | ⟨m, hm, hc⟩ | ⟨m, hm, hl⟩
  ·
    have hc2 := hc
    obtain ⟨hadm, K, hKf, hKfin, hK, ⟨φ⟩⟩ := hc2
    obtain ⟨-, -, -, h22, -⟩ := hadm
    have hm2 : 2 ≤ m := by
      by_contra hlt
      exact h22 (by simp [show m = 1 by omega])
    have h4 : 4 ≤ Nat.card K := by
      have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hm2
      rw [← hK] at h
      norm_num at h
      exact h
    have hsimp : IsSimpleGroup (StatedProj (StatedSL 2 K)) :=
      CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K le_rfl (Or.inr (by omega))
        (Or.inr (by omega))
    haveI := hsimp
    have hHs : IsSimpleGroup H := φ.isSimpleGroup
    exact ⟨Or.inl ⟨2, m, le_rfl, hm, hc⟩, hHs,
      fun P hP hP2 => hBorel H (Or.inl ⟨m, hm2, hc⟩) P hP hP2⟩
  ·
    have hc2 := hc
    obtain ⟨hadm, -⟩ := hc2
    obtain ⟨-, -, -, h32⟩ := hadm
    have hm2 : 2 ≤ m := by
      by_contra hlt
      exact h32 (by simp [show m = 1 by omega])
    exact ⟨Or.inr (Or.inl ⟨m, hm2, hc⟩),
      (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity H 3 2 m hc).2,
      fun P hP hP2 => hBorel H (Or.inr (Or.inl ⟨m, hm2, hc⟩)) P hP hP2⟩
  ·
    have hl2 := hl
    rcases hl2 with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    obtain ⟨-, a, ha, K, hKf, hKfin, hfa, hKc, ⟨φ⟩⟩ := h
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by
      rw [← hfa]
      exact hKc
    have hsz := (CFSG.LieType.Ree.suzuki_simple (a := a) (K := K) ha hK').2.2
    haveI := hsz
    have hHs : IsSimpleGroup H := φ.isSimpleGroup
    have hodd : Odd m := ⟨a, hfa⟩
    have h3 : 3 ≤ m := by omega
    exact ⟨Or.inr (Or.inr (Or.inl ⟨m, hodd, h3, hl⟩)), hHs,
      fun P hP hP2 => hBorel H (Or.inr (Or.inr ⟨m, hodd, h3, hl⟩)) P hP hP2⟩

theorem factorial_nine_lt_card_L4 {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    Nat.factorial 9 < Nat.card (StatedProj (StatedSL 4 K)) := by
  have h := card_statedProj_statedSL_mul_gcd (K := K) (a := 4) (by norm_num)
  have hprod : (∏ j ∈ Finset.Icc 2 4, (Nat.card K ^ j - 1)) =
      (Nat.card K ^ 2 - 1) * ((Nat.card K ^ 3 - 1) * (Nat.card K ^ 4 - 1)) := by
    rw [show Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) from by decide,
      Finset.prod_insert (show (2 : ℕ) ∉ ({3, 4} : Finset ℕ) by decide),
      Finset.prod_insert (show (3 : ℕ) ∉ ({4} : Finset ℕ) by decide), Finset.prod_singleton]
  have e6 : 4 * (4 - 1) / 2 = 6 := by norm_num
  rw [e6, hprod] at h
  have h2 : 16 ≤ Nat.card K ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hK 2
  have h3 : 64 ≤ Nat.card K ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hK 3
  have h4 : 256 ≤ Nat.card K ^ 4 := by
    calc 256 = 4 ^ 4 := by norm_num
      _ ≤ Nat.card K ^ 4 := Nat.pow_le_pow_left hK 4
  have h6 : 4096 ≤ Nat.card K ^ 6 := by
    calc 4096 = 4 ^ 6 := by norm_num
      _ ≤ Nat.card K ^ 6 := Nat.pow_le_pow_left hK 6
  have hB : 15 ≤ Nat.card K ^ 2 - 1 := by omega
  have hC : 63 ≤ Nat.card K ^ 3 - 1 := by omega
  have hD : 255 ≤ Nat.card K ^ 4 - 1 := by omega
  have hR : 4096 * (15 * (63 * 255)) ≤
      Nat.card K ^ 6 * ((Nat.card K ^ 2 - 1) * ((Nat.card K ^ 3 - 1) * (Nat.card K ^ 4 - 1))) :=
    Nat.mul_le_mul h6 (Nat.mul_le_mul hB (Nat.mul_le_mul hC hD))
  by_contra hlt
  have hle : Nat.card (StatedProj (StatedSL 4 K)) ≤ 362880 := by
    have hfac : Nat.factorial 9 = 362880 := by decide
    have hle' := not_lt.mp hlt
    omega
  have hg : Nat.gcd 4 (Nat.card K - 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
  have hmul := Nat.mul_le_mul hle hg
  rw [h] at hmul
  omega

theorem simpleFactors_exists_noncomm {A : Type} [Group A] [Nontrivial A]
    (hA : commutator A = ⊤) : ∃ a b : A, a * b ≠ b * a := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  have h1 : commutator A = ⊥ := by
    change (⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ : Subgroup A) = ⊥
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcon a b
  obtain ⟨x, hx⟩ := exists_ne (1 : A)
  have h3 : (⊤ : Subgroup A) = ⊥ := hA.symm.trans h1
  have h4 : x ∈ (⊥ : Subgroup A) := by
    rw [← h3]
    exact Subgroup.mem_top x
  exact hx (Subgroup.mem_bot.mp h4)

theorem simpleFactors_isPGroup_comap {A B : Type} [Group A] [Group B] (p : ℕ) (f : A →* B)
    (hf : Function.Injective f) {R : Subgroup B} (hR : IsPGroup p ↥R) :
    IsPGroup p ↥(R.comap f) := by
  intro g
  obtain ⟨k, hk⟩ := hR ⟨f (g : A), Subgroup.mem_comap.mp g.2⟩
  refine ⟨k, Subtype.ext (hf ?_)⟩
  have h1 : f (g : A) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  simpa [map_pow] using h1

theorem simpleFactors_solvable_normalizer_of_mulEquiv {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (R : Subgroup B)
    (h : Group.IsSolvable ↥(Subgroup.normalizer ((R.comap e.toMonoidHom : Subgroup A) : Set A))) :
    Group.IsSolvable ↥(Subgroup.normalizer (R : Set B)) := by
  have hN : Subgroup.normalizer ((R.comap e.toMonoidHom : Subgroup A) : Set A) =
      (Subgroup.normalizer (R : Set B)).comap e.toMonoidHom :=
    (Subgroup.comap_normalizer_eq_of_surjective (f := e.toMonoidHom) R e.surjective).symm
  have hmem : ∀ g : ↥(Subgroup.normalizer (R : Set B)),
      e.symm (g : B) ∈ Subgroup.normalizer ((R.comap e.toMonoidHom : Subgroup A) : Set A) := by
    intro g
    rw [hN]
    exact Subgroup.mem_comap.mpr (by simpa using g.2)
  let f : ↥(Subgroup.normalizer (R : Set B)) →*
      ↥(Subgroup.normalizer ((R.comap e.toMonoidHom : Subgroup A) : Set A)) :=
    { toFun := fun g => ⟨e.symm (g : B), hmem g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (map_mul e.symm (a : B) (b : B)) }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply e.symm.injective
    exact congrArg Subtype.val hab
  exact Group.isSolvable_of_isSolvable_injective hf

theorem simpleFactors_solvable_normalizer_map {Y : Type} [Group Y] (Gs : Subgroup Y)
    (X0 : Subgroup ↥Gs)
    (hsolv : ∀ Q : Subgroup ↥X0, Q ≠ ⊥ → IsPGroup 2 Q →
      Group.IsSolvable ↥(Subgroup.normalizer (Q : Set ↥X0)))
    (P : Subgroup Y) (hP : P ≤ X0.map Gs.subtype) (hP0 : P ≠ ⊥) (hP2 : IsPGroup 2 P) :
    Group.IsSolvable ↥(Subgroup.normalizer
      (((P.subgroupOf (X0.map Gs.subtype)) : Subgroup ↥(X0.map Gs.subtype)) :
        Set ↥(X0.map Gs.subtype))) := by
  let e : ↥X0 ≃* ↥(X0.map Gs.subtype) :=
    Subgroup.equivMapOfInjective X0 Gs.subtype Gs.subtype_injective
  have hR2 : IsPGroup 2 ↥(P.subgroupOf (X0.map Gs.subtype)) :=
    simpleFactors_isPGroup_comap 2 (X0.map Gs.subtype).subtype
      (X0.map Gs.subtype).subtype_injective hP2
  have hQ2 : IsPGroup 2 ↥((P.subgroupOf (X0.map Gs.subtype)).comap e.toMonoidHom) :=
    simpleFactors_isPGroup_comap 2 e.toMonoidHom e.injective hR2
  have hQne : (P.subgroupOf (X0.map Gs.subtype)).comap e.toMonoidHom ≠ ⊥ := by
    intro hQ
    apply hP0
    rw [eq_bot_iff]
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (hP hp)
    have hxQ : (⟨x, hx⟩ : ↥X0) ∈ (P.subgroupOf (X0.map Gs.subtype)).comap e.toMonoidHom := by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact hp
    rw [hQ, Subgroup.mem_bot] at hxQ
    have hx1 : x = 1 := congrArg Subtype.val hxQ
    rw [Subgroup.mem_bot, hx1, map_one]
  exact simpleFactors_solvable_normalizer_of_mulEquiv e (P.subgroupOf (X0.map Gs.subtype))
    (hsolv _ hQne hQ2)

theorem simpleFactors_of_beta
    (hBorel : BorelRankOneSolvableStatement) {Y : Type} [Group Y] [Finite Y]
    (Gs : Subgroup Y) [Gs.Normal] (hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥) (r : ℕ)
    (X : Fin r → Subgroup ↥Gs) (hXn : ∀ i, (X i).Normal)
    (hXc : ∀ i j, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j, x * y = y * x) (hXgen : ⨆ i, X i = ⊤)
    (hXcov : ∀ i, IsCoveringOf Tim77Cor2BetaList ↥(X i) ∨ HasNormalTwoComplement ↥(X i)) :
    ∃ (ι : Type) (_ : Fintype ι) (Xs : ι → Subgroup Y), SimpleFactors Gs Xs ∧
      (∀ i, ListGroup ↥(Xs i)) ∧
      (∀ i, ∀ P : Subgroup Y, P ≤ Xs i → P ≠ ⊥ → IsPGroup 2 P →
        Group.IsSolvable ↥(Subgroup.normalizer ((P.subgroupOf (Xs i) : Subgroup ↥(Xs i)) :
          Set ↥(Xs i)))) := by
  classical
  have hcenGs : Subgroup.center ↥Gs = ⊥ := corB_center_eq_bot hO hO2 Gs
  have hZ : ∀ i (z : ↥(X i)), (∀ g : ↥(X i), z * g = g * z) → z = 1 := by
    intro i z hz
    have hcen : ∀ j, X j ≤ Subgroup.centralizer ({(z : ↥Gs)} : Set ↥Gs) := by
      intro j
      by_cases hji : j = i
      · rw [hji]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff] at hs
        rw [hs]
        have h1 := congrArg Subtype.val (hz ⟨x, hx⟩)
        simpa using h1
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff] at hs
        rw [hs]
        exact hXc i j (Ne.symm hji) (z : ↥Gs) z.2 x hx
    have hall : ∀ g : ↥Gs, (z : ↥Gs) * g = g * (z : ↥Gs) := by
      intro g
      have hg : g ∈ ⨆ j, X j := by
        rw [hXgen]
        exact Subgroup.mem_top g
      have hC : (⨆ j, X j) ≤ Subgroup.centralizer ({(z : ↥Gs)} : Set ↥Gs) :=
        iSup_le hcen
      have h1 := hC hg
      rw [Subgroup.mem_centralizer_iff] at h1
      exact h1 (z : ↥Gs) (Set.mem_singleton _)
    have hmem : (z : ↥Gs) ∈ Subgroup.center ↥Gs := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hall g).symm
    rw [hcenGs, Subgroup.mem_bot] at hmem
    exact Subtype.ext (by simpa using hmem)
  have hcovi : ∀ i, X i ≠ ⊥ → IsCoveringOf Tim77Cor2BetaList ↥(X i) := by
    intro i hi
    rcases hXcov i with h | h
    · exact h
    · haveI := hXn i
      exact absurd (eq_bot_of_normalTwoComplement Gs hO2 hO (X i) h) hi
  have hleS : ∀ i : Fin r, (X i).map Gs.subtype ≤ Gs := by
    intro i y hy
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hy
    exact x.2
  have hgen : Gs = ⨆ i : Fin r, (X i).map Gs.subtype := by
    rw [← Subgroup.map_iSup Gs.subtype X, hXgen, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  refine ⟨{i : Fin r // X i ≠ ⊥}, inferInstance, fun i => (X i.1).map Gs.subtype,
    ⟨?_, fun i => hleS i.1, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  ·
    intro y g hg
    exact Subgroup.Normal.conj_mem ‹Gs.Normal› g hg y
  ·
    intro i g hg x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * x' * (⟨g, hg⟩ : ↥Gs)⁻¹,
      Subgroup.Normal.conj_mem (hXn i.1) x' hx' ⟨g, hg⟩, ?_⟩
    simp
  ·
    intro i j hij x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    rw [← map_mul, ← map_mul, hXc i.1 j.1 hne x' hx' y' hy']
  ·
    apply le_antisymm
    · exact iSup_le fun i => hleS i.1
    · refine le_trans (le_of_eq hgen) (iSup_le fun i => ?_)
      by_cases hi : X i = ⊥
      · rw [hi, Subgroup.map_bot]
        exact bot_le
      · exact le_iSup (fun j : {i : Fin r // X i ≠ ⊥} => (X j.1).map Gs.subtype) ⟨i, hi⟩
  ·
    intro i
    have hs := (beta_facts hBorel (hcovi i.1 i.2) (hZ i.1)).2.1
    haveI := hs
    have he := (Subgroup.equivMapOfInjective (X i.1) Gs.subtype Gs.subtype_injective).symm
    exact he.isSimpleGroup
  ·
    intro i
    have hs := (beta_facts hBorel (hcovi i.1 i.2) (hZ i.1)).2.1
    haveI := hs
    obtain ⟨hcomm, -⟩ := hcovi i.1 i.2
    obtain ⟨a, b, hab⟩ := simpleFactors_exists_noncomm hcomm
    refine ⟨Gs.subtype a.1, Subgroup.mem_map.mpr ⟨a.1, a.2, rfl⟩, Gs.subtype b.1,
      Subgroup.mem_map.mpr ⟨b.1, b.2, rfl⟩, fun h => hab (Subtype.ext (Gs.subtype_injective ?_))⟩
    simpa using h
  ·
    intro z hz hzc
    have hmem : (⟨z, hz⟩ : ↥Gs) ∈ Subgroup.center ↥Gs := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (hzc g.1 g.2).symm
    rw [hcenGs, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  ·
    intro i
    exact ListGroup.of_mulEquiv
      (Subgroup.equivMapOfInjective (X i.1) Gs.subtype Gs.subtype_injective)
      (beta_facts hBorel (hcovi i.1 i.2) (hZ i.1)).1
  ·
    intro i P hP hP0 hP2
    exact simpleFactors_solvable_normalizer_map Gs (X i.1)
      (beta_facts hBorel (hcovi i.1 i.2) (hZ i.1)).2.2 P hP hP0 hP2

end CFSG.RankThree.GF2n.Stroth80
