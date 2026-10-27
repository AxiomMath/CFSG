module

public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.H13.KGLieTwSL2
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13.KGLie
open scoped IsMulCommutative Matrix

private def lineSub (F : Type) [Field F] : Subgroup (Multiplicative (Fin 2 → F)) where
  carrier := {x | Multiplicative.toAdd x 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change Multiplicative.toAdd a 1 + Multiplicative.toAdd b 1 = 0
    rw [ha, hb, add_zero]
  inv_mem' := by
    intro a ha
    change -Multiplicative.toAdd a 1 = 0
    rw [ha, neg_zero]

private noncomputable def lineEquiv (F : Type) [Field F] : lineSub F ≃ F where
  toFun x := Multiplicative.toAdd (x : Multiplicative (Fin 2 → F)) 0
  invFun a := ⟨Multiplicative.ofAdd ![a, 0], by simp [lineSub]⟩
  left_inv x := by
    apply Subtype.ext
    show Multiplicative.ofAdd ![Multiplicative.toAdd (x : Multiplicative (Fin 2 → F)) 0, 0] =
      (x : Multiplicative (Fin 2 → F))
    conv_rhs => rw [show (x : Multiplicative (Fin 2 → F)) =
      Multiplicative.ofAdd (Multiplicative.toAdd (x : Multiplicative (Fin 2 → F))) from
      (ofAdd_toAdd (x : Multiplicative (Fin 2 → F))).symm]
    congr 1
    funext i
    fin_cases i
    · simp
    · simpa [lineSub] using x.2.symm
  right_inv a := by simp

private theorem card_lineSub {F : Type} [Field F] : Nat.card (lineSub F) = Nat.card F :=
  Nat.card_congr (lineEquiv F)

private theorem card_eq_mul_card_comap_line {F : Type} [Field F] {V : Type} [Group V]
    (β : V →* Multiplicative (Fin 2 → F)) [Finite F] [Finite V]
    (hβ : Function.Surjective β) :
    Nat.card V = Nat.card F * Nat.card ↥((lineSub F).comap β) := by
  have hcard := Subgroup.card_ker_mul_card_range β
  rw [MonoidHom.range_eq_top.mpr hβ, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_fin] at hcard
  have hkerle : β.ker ≤ (lineSub F).comap β := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap, hx]
    exact (lineSub F).one_mem
  have hker : (β.domRestrict ((lineSub F).comap β)).ker =
      β.ker.subgroupOf ((lineSub F).comap β) := by
    ext x
    rfl
  have hrange : (β.domRestrict ((lineSub F).comap β)).range = lineSub F := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      obtain ⟨v, hv⟩ := hβ y
      refine ⟨⟨v, ?_⟩, hv⟩
      rw [Subgroup.mem_comap, hv]
      exact hy
  have hpre := Subgroup.card_ker_mul_card_range (β.domRestrict ((lineSub F).comap β))
  rw [hker, hrange] at hpre
  have hsub : Nat.card (β.ker.subgroupOf ((lineSub F).comap β)) = Nat.card β.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv
  rw [hsub, card_lineSub] at hpre
  rw [← hcard, ← hpre]
  ring

private theorem isElemAbelian_ut2 {F : Type} [Field F] [CharP F 2] :
    IsElemAbelian 2 (ut2 F) := by
  rw [ut2]
  exact (isElemAbelian_utri (F := F)).map _

private theorem utriMat_mulVec {F : Type} [Field F] (c : F) (x : Fin 2 → F) :
    (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) F) *ᵥ x =
      x + Pi.single 0 (c * x 1) := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem utriMat_mulVec_pair {F : Type} [Field F] (c x y : F) :
    (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) F) *ᵥ (![x, y] : Fin 2 → F) =
      ![x + c * y, y] := by
  rw [utriMat_mulVec]
  funext i
  fin_cases i <;> simp

theorem isFFModule_autOn_of_isNaturalSection_two {G : Type} [Group G] [Finite G]
    {A V W : Subgroup G} {N : Subgroup ↥A} {F : Type} [Field F] [Fintype F]
    (hF : (2 : F) = 0) (hV : ∀ v ∈ V, v ^ 2 = 1)
    (hW : W ≤ Subgroup.centralizer (A : Set G))
    (hN : N.map A.subtype ≤ Subgroup.centralizer (V : Set G))
    (h : IsNaturalSection A V W N (StatedSL 2 F)) [IsMulCommutative ↥V] :
    IsFFModule (V := ↥V) (autOn A V) := by
  classical
  haveI : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast hF)
  obtain ⟨hAN, α, hαsurj, hαker, β, hβsurj, hβker, hβeq⟩ := h
  choose t ht using hαsurj
  let e : F → ↥(StatedSL 2 F) := fun c => specialLinearGroupEquivStatedSL 2 F (utriElt c)
  have he_mem : ∀ c, e c ∈ ut2 F := fun c => utriElt_mem_ut2 c
  have he_sq : ∀ c, e c ^ 2 = 1 := fun c => (isElemAbelian_ut2 (F := F)).2 _ (he_mem c)
  have he_comm : ∀ c d : F, e c * e d = e d * e c := fun c d =>
    (isElemAbelian_ut2 (F := F)).comm (he_mem c) (he_mem d)
  let σ : F → MulAut ↥V := fun c =>
    conjAct V ⟨(t (e c) : G), hAN (t (e c)).2⟩
  have hσ_mem : ∀ c, σ c ∈ autOn A V := fun c =>
    AutOn.conjAct_mem_autOn _ (t (e c)).2
  have hσ_sq : ∀ c, σ c ^ 2 = 1 := by
    intro c
    have hker : (t (e c)) ^ 2 ∈ N := by
      rw [← hαker, MonoidHom.mem_ker]
      rw [map_pow, ht, he_sq]
    have hcent : ((t (e c) : ↥A) : G) ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
      have hmem := hN (Subgroup.mem_map_of_mem A.subtype hker)
      simpa using hmem
    rw [show σ c = conjAct V ⟨(t (e c) : G), hAN (t (e c)).2⟩ from rfl,
      ← map_pow, AutOn.conjAct_eq_one_iff]
    simpa using hcent
  have hσ_comm : ∀ c d, σ c * σ d = σ d * σ c := by
    intro c d
    have hker : t (e c) * t (e d) * (t (e c))⁻¹ * (t (e d))⁻¹ ∈ N := by
      rw [← hαker, MonoidHom.mem_ker]
      simp only [map_mul, map_inv, ht]
      rw [he_comm c d]
      group
    have hcent : (((t (e c) * t (e d) * (t (e c))⁻¹ * (t (e d))⁻¹ : ↥A)) : G) ∈
        Subgroup.centralizer (V : Set G) :=
      hN (Subgroup.mem_map_of_mem A.subtype hker)
    have h1 : σ c * σ d * (σ c)⁻¹ * (σ d)⁻¹ = 1 := by
      have hconj : σ c * σ d * (σ c)⁻¹ * (σ d)⁻¹ =
          conjAct V (⟨(t (e c) : G), hAN (t (e c)).2⟩ *
            ⟨(t (e d) : G), hAN (t (e d)).2⟩ *
            (⟨(t (e c) : G), hAN (t (e c)).2⟩)⁻¹ *
            (⟨(t (e d) : G), hAN (t (e d)).2⟩)⁻¹) := by
        simp only [σ, map_mul, map_inv]
      rw [hconj, AutOn.conjAct_eq_one_iff]
      simpa using hcent
    exact mul_inv_eq_one.mp h1
  have hmat : ∀ c : F, (((e c : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] := by
    intro c
    rw [show e c = specialLinearGroupEquivStatedSL 2 F (utriElt c) from rfl,
      coe_utriElt_stated]
  obtain ⟨u₁, hu₁⟩ := hβsurj (Multiplicative.ofAdd (![0, 1] : Fin 2 → F))
  have hσu₁ : ∀ c, Multiplicative.toAdd (β (σ c u₁)) = (![c, 1] : Fin 2 → F) := by
    intro c
    have hcoe : ((σ c u₁ : ↥V) : G) = (t (e c) : G) * (u₁ : G) * (t (e c) : G)⁻¹ :=
      AutOn.coe_conjAct_apply V ⟨(t (e c) : G), hAN (t (e c)).2⟩ u₁
    have h := hβeq (t (e c)) u₁ (σ c u₁) hcoe
    rw [ht] at h
    rw [hu₁, hmat c, toAdd_ofAdd, utriMat_mulVec_pair] at h
    simpa using h
  have hσ_inj : Function.Injective σ := by
    intro c d hcd
    have h1 := congrArg (fun φ : MulAut ↥V => Multiplicative.toAdd (β (φ u₁))) hcd
    rw [hσu₁ c, hσu₁ d] at h1
    have := congrFun h1 0
    simpa using this
  let B : Subgroup (MulAut ↥V) := Subgroup.closure (Set.range σ)
  have hB_le : B ≤ autOn A V :=
    (Subgroup.closure_le (autOn A V)).mpr (by rintro _ ⟨c, rfl⟩; exact hσ_mem c)
  have hB_elem : IsElemAbelian 2 B :=
    IsElemAbelian.closure_of_commute
      (s := Set.range σ)
      (by rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩; exact hσ_comm c d)
      (by rintro _ ⟨c, rfl⟩; exact hσ_sq c)
  have hB_card : Nat.card F ≤ Nat.card B := by
    let f : F → B := fun c => ⟨σ c, Subgroup.subset_closure ⟨c, rfl⟩⟩
    have hfinj : Function.Injective f := fun c d h => hσ_inj (Subtype.ext_iff.mp h)
    exact Nat.card_le_card_of_injective f hfinj
  let Vt : Subgroup ↥V := (lineSub F).comap β
  have hVt_fix : Vt ≤ fixV B := by
    intro x hx
    rw [mem_fixV]
    intro φ hφ
    induction hφ using Subgroup.closure_induction with
    | mem a ha =>
        obtain ⟨c, rfl⟩ := ha
        by_cases hc : c = 0
        · subst hc
          have ht0 : t (e 0) ∈ N := by
            rw [← hαker, MonoidHom.mem_ker]
            rw [ht]
            simp [e, utriElt_zero]
          have hσ0 : σ 0 = 1 := by
            rw [show σ 0 = conjAct V ⟨(t (e 0) : G), hAN (t (e 0)).2⟩ from rfl,
              AutOn.conjAct_eq_one_iff]
            exact hN (Subgroup.mem_map_of_mem A.subtype ht0)
          rw [hσ0, MulAut.one_apply]
        ·
          have hx' : Multiplicative.toAdd (β x) 1 = 0 := by
            have h := hx
            rw [Subgroup.mem_comap] at h
            simpa [lineSub] using h
          have hxline : Multiplicative.toAdd (β x) =
              (![Multiplicative.toAdd (β x) 0, 0] : Fin 2 → F) := by
            funext i
            fin_cases i
            · simp
            · simpa using hx'
          obtain ⟨u, hu⟩ := hβsurj (Multiplicative.ofAdd
            (![0, Multiplicative.toAdd (β x) 0 / c] : Fin 2 → F))
          have hβσu : Multiplicative.toAdd (β (σ c u)) =
              (![c * (Multiplicative.toAdd (β x) 0 / c),
                Multiplicative.toAdd (β x) 0 / c] : Fin 2 → F) := by
            have hcoe : ((σ c u : ↥V) : G) = (t (e c) : G) * (u : G) * (t (e c) : G)⁻¹ :=
              AutOn.coe_conjAct_apply V ⟨(t (e c) : G), hAN (t (e c)).2⟩ u
            have h := hβeq (t (e c)) u (σ c u) hcoe
            rw [ht] at h
            rw [hu, hmat c, toAdd_ofAdd, utriMat_mulVec_pair] at h
            simpa using h
          have hdiv : c * (Multiplicative.toAdd (β x) 0 / c) =
              Multiplicative.toAdd (β x) 0 := by
            field_simp
          have hβσu' : Multiplicative.toAdd (β (σ c u)) =
              (![Multiplicative.toAdd (β x) 0, Multiplicative.toAdd (β x) 0 / c] :
                Fin 2 → F) := by
            rw [hβσu]
            ext i
            fin_cases i <;> simp [hdiv]
          have hβv : Multiplicative.toAdd (β (σ c u * u⁻¹)) =
              (![Multiplicative.toAdd (β x) 0, 0] : Fin 2 → F) := by
            rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hβσu', hu]
            ext i
            fin_cases i <;> simp [Pi.add_apply]
          let z : ↥V := (σ c u * u⁻¹)⁻¹ * x
          have hzβ : β z = 1 := by
            have hzadd : Multiplicative.toAdd (β z) = 0 := by
              show Multiplicative.toAdd (β ((σ c u * u⁻¹)⁻¹ * x)) = 0
              rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hβv, hxline]
              ext i
              fin_cases i <;> simp [Pi.add_apply]
            have := congrArg Multiplicative.ofAdd hzadd
            simpa using this
          have hzW : ((z : ↥V) : G) ∈ W := by
            have hzmem : z ∈ β.ker := MonoidHom.mem_ker.mpr hzβ
            rwa [hβker, Subgroup.mem_subgroupOf] at hzmem
          have hσz : σ c z = z := by
            apply Subtype.ext
            rw [AutOn.coe_conjAct_apply]
            have hcz := Subgroup.mem_centralizer_iff.mp (hW hzW) (t (e c) : G) (t (e c)).2
            calc (t (e c) : G) * (z : ↥V) * (t (e c) : G)⁻¹
                = ((z : ↥V) * (t (e c) : G)) * (t (e c) : G)⁻¹ := by rw [hcz]
              _ = z := by group
          have hu_inv : (u : ↥V)⁻¹ = u := by
            have h : u * u = 1 := by
              apply Subtype.ext
              rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
              exact hV _ u.2
            exact inv_eq_of_mul_eq_one_right h
          have hσu_inv : (σ c u)⁻¹ = σ c u := by
            have h : σ c u * σ c u = 1 := by
              apply Subtype.ext
              rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
              exact hV _ (σ c u).2
            exact inv_eq_of_mul_eq_one_right h
          have hσ2u : σ c (σ c u) = u := by
            have h := congrArg (fun ψ : MulAut ↥V => ψ u) (hσ_sq c)
            simpa [pow_two] using h
          have hσv : σ c (σ c u * u⁻¹) = σ c u * u⁻¹ := by
            rw [map_mul, map_inv, hσ2u, hσu_inv, hu_inv, mul_comm]
          have hxz : x = (σ c u * u⁻¹) * z := by
            show x = (σ c u * u⁻¹) * ((σ c u * u⁻¹)⁻¹ * x)
            group
          rw [hxz, map_mul, hσv, hσz]
    | one => rfl
    | mul a b ha hb iha ihb => rw [MulAut.mul_apply, ihb, iha]
    | inv a ha iha =>
        have h := congrArg (fun y => a⁻¹ y) iha
        simpa using h.symm
  have hVcard : Nat.card ↥V = Nat.card F * Nat.card Vt :=
    card_eq_mul_card_comap_line β hβsurj
  have hVtle : Nat.card Vt ≤ Nat.card (fixV B) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hVt_fix) (Subgroup.inclusion_injective _)
  have hB_ne : B ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card B = 1 := by rw [hbot, Subgroup.card_bot]
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  refine ⟨B, hB_le, hB_ne, ⟨fun a ha b hb => hB_elem.comm ha hb,
    fun a ha => hB_elem.2 a ha⟩, ?_⟩
  calc Nat.card ↥V = Nat.card F * Nat.card Vt := hVcard
    _ ≤ Nat.card B * Nat.card (fixV B) := Nat.mul_le_mul hB_card hVtle

end CFSG.Quasithin

end
