module

public import CFSG.Quasithin.Vol2.KGFact12617L52a
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.Quasithin.H13.KG12617L52

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits Module
open scoped commutatorElement

section Group

variable {G : Type*} [Group G] [Finite G]

theorem card_modEq_one {U : Subgroup G} {x : G} (hx : orderOf x = 5)
    (hxU : x ∈ Subgroup.normalizer (U : Set G)) (hcU : ∀ u ∈ U, u * x = x * u → u = 1) :
    Nat.card ↥U ≡ 1 [MOD 5] := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hG : IsPGroup 5 ↥(Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx, pow_one]
  have hzN : Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.zpowers_le).2 hxU
  let act : MulAction ↥(Subgroup.zpowers x) ↥U :=
    { smul := fun g u => ⟨(g : G) * u * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hzN g.2) u).mp u.2⟩
      one_smul := fun u => Subtype.ext (by
        show ((1 : ↥(Subgroup.zpowers x)) : G) * u * ((1 : ↥(Subgroup.zpowers x)) : G)⁻¹ = u
        simp)
      mul_smul := fun g h u => Subtype.ext (by
        show ((g * h : ↥(Subgroup.zpowers x)) : G) * u * ((g * h : ↥(Subgroup.zpowers x)) : G)⁻¹ =
          (g : G) * ((h : G) * u * (h : G)⁻¹) * (g : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  have hmod := hG.card_modEq_card_fixedPoints ↥U
  have hfix : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥U) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, fun g => Subtype.ext (by
      show ((g : G) * ((1 : ↥U) : G) * (g : G)⁻¹) = ((1 : ↥U) : G)
      simp)⟩⟩⟩
    have key : ∀ a : MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥U, a.1 = 1 := by
      rintro ⟨a, ha⟩
      have h1 := congrArg Subtype.val (ha ⟨x, Subgroup.mem_zpowers x⟩)
      change x * (a : G) * x⁻¹ = a at h1
      apply Subtype.ext
      apply hcU a a.2
      calc (a : G) * x = x * (a : G) * x⁻¹ * x := by rw [h1]
        _ = x * a := by group
    rw [key a, key b]
  rwa [hfix] at hmod

theorem mem_of_two_elt {B U : Subgroup G} (hBU : B ≤ Subgroup.normalizer (U : Set G))
    (hU2 : IsPGroup 2 ↥U) {x : G} (hxB : x ∈ B) (hcU : ∀ u ∈ U, u * x = x * u → u = 1)
    (h2 : ∀ d : G, (∃ k : ℕ, d ^ 2 ^ k = 1) → d * x = x * d → d = 1) {c : G}
    (hc2 : ∃ k : ℕ, c ^ 2 ^ k = 1) (hcN : c ∈ Subgroup.normalizer (U : Set G))
    (hcB : ∀ b ∈ B, b * c * b⁻¹ * c⁻¹ ∈ U) : c ∈ U := by
  classical
  have hxN : x ∈ Subgroup.normalizer (U : Set G) := hBU hxB
  have hu₁ : c * x * c⁻¹ * x⁻¹ ∈ U := by
    have h := hcB x⁻¹ (B.inv_mem hxB)
    have h' := (Subgroup.mem_normalizer_iff.mp hxN _).mp h
    rw [inv_inv] at h'
    have : x * (x⁻¹ * c * x * c⁻¹) * x⁻¹ = c * x * c⁻¹ * x⁻¹ := by group
    rwa [this] at h'
  have hmem : ∀ u ∈ U, u * x * u⁻¹ * x⁻¹ ∈ U := by
    intro u hu
    have h := (Subgroup.mem_normalizer_iff.mp hxN _).mp (U.inv_mem hu)
    have : u * (x * u⁻¹ * x⁻¹) = u * x * u⁻¹ * x⁻¹ := by group
    rw [← this]
    exact U.mul_mem hu h
  let f : ↥U → ↥U := fun u => ⟨u * x * (u : G)⁻¹ * x⁻¹, hmem u u.2⟩
  have hf : Function.Injective f := by
    intro u u' huu'
    have h := congrArg Subtype.val huu'
    change (u : G) * x * (u : G)⁻¹ * x⁻¹ = u' * x * (u' : G)⁻¹ * x⁻¹ at h
    have hc : ((u' : G)⁻¹ * u) * x = x * ((u' : G)⁻¹ * u) := by
      calc ((u' : G)⁻¹ * u) * x = (u' : G)⁻¹ * ((u : G) * x * (u : G)⁻¹ * x⁻¹) * x * u := by
            group
        _ = (u' : G)⁻¹ * ((u' : G) * x * (u' : G)⁻¹ * x⁻¹) * x * u := by rw [h]
        _ = x * ((u' : G)⁻¹ * u) := by group
    have h1 := hcU _ (U.mul_mem (U.inv_mem u'.2) u.2) hc
    apply Subtype.ext
    calc (u : G) = u' * ((u' : G)⁻¹ * u) := by group
      _ = u' := by rw [h1, mul_one]
  obtain ⟨u', hu'⟩ := (Finite.injective_iff_surjective.mp hf) ⟨_, hu₁⟩
  have hu'' : (u' : G) * x * (u' : G)⁻¹ * x⁻¹ = c * x * c⁻¹ * x⁻¹ := congrArg Subtype.val hu'
  have hdx : ((u' : G)⁻¹ * c) * x = x * ((u' : G)⁻¹ * c) := by
    have e1 : (u' : G) * x * (u' : G)⁻¹ = c * x * c⁻¹ := by
      have := congrArg (· * x) hu''
      simpa [mul_assoc] using this
    calc ((u' : G)⁻¹ * c) * x = (u' : G)⁻¹ * (c * x * c⁻¹) * c := by group
      _ = (u' : G)⁻¹ * ((u' : G) * x * (u' : G)⁻¹) * c := by rw [e1]
      _ = x * ((u' : G)⁻¹ * c) := by group
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers c) := by
    obtain ⟨k, hk⟩ := hc2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hzN : Subgroup.zpowers c ≤ Subgroup.normalizer (U : Set G) := (Subgroup.zpowers_le).2 hcN
  have hW2 := IsPGroup.to_sup_of_normal_left' hU2 hz2 hzN
  obtain ⟨k, hk⟩ := hW2 ⟨(u' : G)⁻¹ * c, Subgroup.mul_mem _ (Subgroup.mem_sup_left (U.inv_mem u'.2))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))⟩
  have hd := h2 ((u' : G)⁻¹ * c) ⟨k, by simpa using congrArg Subtype.val hk⟩ hdx
  have hcu : c = u' := by
    calc c = (u' : G) * ((u' : G)⁻¹ * c) := by group
      _ = u' := by rw [hd, mul_one]
  rw [hcu]
  exact u'.2

theorem card_le_of_isPGroup_normalizer {B : Subgroup G}
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)))
    (hU : ∀ c : G, (∃ k : ℕ, c ^ 2 ^ k = 1) →
      c ∈ centralizerSection ⊤ B (pCoreOf 2 B) → c ∈ pCoreOf 2 B)
    {D : Subgroup G} (hD : IsPGroup 2 ↥D) (hDN : D ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥D ≤ 32 * Nat.card ↥(pCoreOf 2 B) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, hker⟩ := hBiso
  set ρ : ↥D →* MulAut ↥(alternatingGroup (Fin 6)) :=
    (KG12617Lie.quotAct φ hφ hker).comp (Subgroup.inclusion hDN) with hρ
  have hr := KG12617Lie.card_le_of_isPGroup_mulAut
    (hD.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective)
  have hPc : Nat.card ↥D = Nat.card ↥ρ.range * Nat.card ↥ρ.ker := by
    rw [ρ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  have hk : Nat.card ↥ρ.ker ≤ Nat.card ↥(pCoreOf 2 B) := by
    refine Nat.card_le_card_of_injective (fun d => ⟨((d : ↥D) : G), ?_⟩) ?_
    · have hd := KG12617Lie.mem_centralizerSection_of_quotAct_eq_one φ hφ hker
        (M := ⊤) (n := Subgroup.inclusion hDN d) (Subgroup.mem_top _) d.2
      obtain ⟨k, hk⟩ := hD (d : ↥D)
      exact hU _ ⟨k, congrArg Subtype.val hk⟩ hd
    · intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
  calc Nat.card ↥D = Nat.card ↥ρ.range * Nat.card ↥ρ.ker := hPc
    _ ≤ 32 * Nat.card ↥(pCoreOf 2 B) := Nat.mul_le_mul hr hk

end Group

section Aut

variable {F : Type} [Field F]

local notation "SLF" => Assembly.LowTwoRank.StatedSL 5 F
local notation "ρ" => natRep (Assembly.LowTwoRank.StatedSL 5 F)

theorem ringEquiv_apply_eq [Finite F] (hF : Nat.card F = 2) (σ : F ≃+* F) (c : F) : σ c = c := by
  classical
  have := Fintype.ofFinite F
  have h01 : ∀ d : F, d = 0 ∨ d = 1 := by
    intro d
    by_contra h
    push Not at h
    have h3 : ({0, 1, d} : Finset F).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair h.2.symm]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨zero_ne_one, fun h' => h.1 h'.symm⟩
    have := Finset.card_le_univ ({0, 1, d} : Finset F)
    rw [h3, ← Nat.card_eq_fintype_card, hF] at this
    omega
  rcases h01 c with rfl | rfl
  · exact map_zero σ
  · exact map_one σ

theorem mem_statedSL [Finite F] (hF : Nat.card F = 2) (A : GL (Fin 5) F) :
    A ∈ Assembly.LowTwoRank.StatedSL 5 F := by
  classical
  refine Subgroup.subset_closure ?_
  show (A : Matrix (Fin 5) (Fin 5) F).det = 1
  have h : (A : Matrix (Fin 5) (Fin 5) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have := Fintype.ofFinite F
  by_contra h1
  have h3 : ({0, 1, (A : Matrix (Fin 5) (Fin 5) F).det} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h1)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, fun h' => h h'.symm⟩
  have := Finset.card_le_univ ({0, 1, (A : Matrix (Fin 5) (Fin 5) F).det} : Finset F)
  rw [h3, ← Nat.card_eq_fintype_card, hF] at this
  omega

theorem fixFlag_map_conj (W : Subgroup ↥SLF) (a : ↥SLF) :
    fixFlag ρ (W.map (MulAut.conj a).toMonoidHom) 1 = (fixFlag ρ W 1).map (ρ a) := by
  have hinv : ∀ y, ρ a (ρ a⁻¹ y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ y, ρ a⁻¹ (ρ a y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  ext v
  constructor
  · intro hv
    refine ⟨ρ a⁻¹ v, (mem_fixFlag_succ ρ (k := 0)).2 fun w hw => ?_, hinv v⟩
    have h := (mem_fixFlag_succ ρ (k := 0)).1 hv _ ⟨w, hw, rfl⟩
    rw [fixFlag_zero, Submodule.mem_bot, sub_eq_zero] at h ⊢
    have h' : ρ (a * w * a⁻¹) v = v := h
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply] at h'
    rw [← hinv' (ρ w (ρ a⁻¹ v)), h']
  · rintro ⟨y, hy, rfl⟩
    refine (mem_fixFlag_succ ρ (k := 0)).2 ?_
    rintro _ ⟨w, hw, rfl⟩
    have h := (mem_fixFlag_succ ρ (k := 0)).1 hy w hw
    rw [fixFlag_zero, Submodule.mem_bot, sub_eq_zero] at h ⊢
    show ρ (a * w * a⁻¹) (ρ a y) = ρ a y
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hinv', h]

theorem finrank_fixFlag_map_conj (W : Subgroup ↥SLF) (a : ↥SLF) :
    finrank F ↥(fixFlag ρ (W.map (MulAut.conj a).toMonoidHom) 1) = finrank F ↥(fixFlag ρ W 1) := by
  rw [fixFlag_map_conj]
  let e : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F) := LinearEquiv.ofLinearMap (ρ a) (ρ a⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
  exact e.finrank_map_eq (fixFlag ρ W 1)

theorem exists_inner_of_map_eq [Finite F] (hF : Nat.card F = 2) (β : MulAut ↥SLF)
    {U : Subgroup ↥SLF} (hβ : U.map β.toMonoidHom = U)
    (hne : finrank F ↥(fixFlag ρ U 1) ≠ finrank F ↥(fixFlag ρ (U.map theta.toMonoidHom) 1)) :
    ∃ a : ↥SLF, ∀ g, β g = a * g * a⁻¹ := by
  classical
  set e₀ := Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 F with he₀
  have hcoe : ∀ g : ↥SLF, (((e₀.symm g : Matrix.SpecialLinearGroup (Fin 5) F) :
      Matrix (Fin 5) (Fin 5) F)) = ((g : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
    intro g
    conv_rhs => rw [← e₀.apply_symm_apply g]
    rw [Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
  set β' : MulAut (Matrix.SpecialLinearGroup (Fin 5) F) := MulAut.congr e₀.symm β with hβ'
  have hβ'g : ∀ g : ↥SLF, ((β g : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      ((β' (e₀.symm g) : Matrix.SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
    intro g
    have h1 : β' (e₀.symm g) = e₀.symm (β g) := by
      rw [hβ']
      simp [MulAut.congr_apply]
    rw [h1, hcoe]
  have hmap : ∀ M : Matrix (Fin 5) (Fin 5) F, ∀ σ : F ≃+* F, M.map σ = M := by
    intro M σ
    ext i j
    exact ringEquiv_apply_eq hF σ _
  obtain ⟨A, σ, h | h⟩ := CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl
    (by norm_num : 3 ≤ 5) β'
  · refine ⟨⟨A, mem_statedSL hF A⟩, fun g => Subtype.ext (Units.ext ?_)⟩
    rw [hβ'g, h, hmap, hcoe]
    rfl
  · exfalso
    set a : ↥SLF := ⟨A, mem_statedSL hF A⟩ with ha
    have hform : ∀ g, β g = a * theta g * a⁻¹ := by
      intro g
      refine Subtype.ext (Units.ext ?_)
      rw [hβ'g, h, hmap, ← map_inv, hcoe]
      rfl
    have hUmap : U.map β.toMonoidHom =
        (U.map theta.toMonoidHom).map (MulAut.conj a).toMonoidHom := by
      ext g
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨theta u, ⟨u, hu, rfl⟩, (hform u).symm⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨u, hu, hform u⟩
    apply hne
    rw [← finrank_fixFlag_map_conj (U.map theta.toMonoidHom) a, ← hUmap, hβ]

end Aut

end CFSG.Quasithin.H13.KG12617L52
