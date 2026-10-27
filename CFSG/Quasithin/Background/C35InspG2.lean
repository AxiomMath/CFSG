module

public import CFSG.Quasithin.Background.C35InspG2A
public import CFSG.Quasithin.Background.C35InspBase
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2Cent
public import CFSG.Quasithin.H13.NQCatG2RadModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.QuasithinUnique.Setup.X6
open scoped commutatorElement

section G2

variable {F : Type} [Field F] [CharP F 2]

theorem bc_inj
    {w w' : Fin 2 → F} (h : gX rB (w 1) * gX rC (w 0) = gX rB (w' 1) * gX rC (w' 0)) : w = w' := by
  have h1 : gX rB (w 1 + w' 1) * gX rC (w 0 + w' 0) = 1 := by
    rw [gX_add, gX_add]
    have e : gX rB (w 1) * gX rB (w' 1) * (gX rC (w 0) * gX rC (w' 0)) =
        (gX rB (w 1) * gX rC (w 0)) * (gX rB (w' 1) * gX rC (w' 0)) := by
      rw [show gX rB (w 1) * gX rB (w' 1) * (gX rC (w 0) * gX rC (w' 0)) =
        gX rB (w 1) * (gX rB (w' 1) * gX rC (w 0)) * gX rC (w' 0) by group,
        (comm_bc (w' 1) (w 0)).eq]
      group
    rw [e, h, show gX rB (w' 1) * gX rC (w' 0) * (gX rB (w' 1) * gX rC (w' 0)) =
      gX rB (w' 1) * (gX rC (w' 0) * gX rB (w' 1)) * gX rC (w' 0) by group,
      ← (comm_bc (w' 1) (w' 0)).eq,
      show gX rB (w' 1) * (gX rB (w' 1) * gX rC (w' 0)) * gX rC (w' 0) =
        (gX rB (w' 1) * gX rB (w' 1)) * (gX rC (w' 0) * gX rC (w' 0)) by group,
      gX_self, gX_self, one_mul]
  obtain ⟨hb, hc⟩ := prod_bc_eq_one h1
  ext i
  fin_cases i
  · exact (add_eq_zero_iff_eq_neg.mp hc).trans (CharTwo.neg_eq _)
  · exact (add_eq_zero_iff_eq_neg.mp hb).trans (CharTwo.neg_eq _)

@[expose] noncomputable def coordBC
    (z : ModGL Tag.G2 F) : Fin 2 → F :=
  open Classical in
  if h : ∃ w : Fin 2 → F, z = gX rB (w 1) * gX rC (w 0) then h.choose else 0

theorem coordBC_eq
    (w : Fin 2 → F) : coordBC (gX rB (w 1) * gX rC (w 0)) = w := by
  have h : ∃ w' : Fin 2 → F, gX rB (w 1) * gX rC (w 0) = gX rB (w' 1) * gX rC (w' 0) := ⟨w, rfl⟩
  rw [coordBC, dite_eq_left h]
  exact (bc_inj h.choose_spec).symm

end G2

theorem g2_holds_base :
    ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Base K Y M₀ V →
      ∀ f : ℕ, 2 ≤ f → IsG2 2 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V := by
  intro A _ _ K Y M₀ V hD f hf2 hX
  classical
  have hX' := hX
  obtain ⟨-, F, _, _, _, hcard, ⟨e⟩⟩ := exists_mulEquiv_G2_model hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 F) := finite_modGL
  have hK4' : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hK4 : ∃ s : Finset F, s.card = 4 := Vol2Native.A312L.exists_finset_card_four hK4'
  set C := adjointGroup Tag.G2 F with hCdef
  let φ : ↥K →* ↥C := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφker : φ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := e.surjective y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
    exact ⟨k, hx⟩
  have hUC : posUnipotent Tag.G2 F ≤ C := posUnipotent_le_adjointGroup
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 F).subgroupOf C) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := F) 2).1)
  obtain ⟨g, hNY, hne, hns⟩ := hD.exists_conj_normalizer φ hφker.le hφs hU₀
  set θ := (MulAut.conj g⁻¹).toMonoidHom.comp φ with hθ
  have hθker : θ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hφker]
  set θ' : ↥K →* ModGL Tag.G2 F := C.subtype.comp θ with hθ'
  have hθ'ker : θ'.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker, hθ', MonoidHom.comp_apply, Subgroup.coe_subtype,
      OneMemClass.coe_eq_one, ← MonoidHom.mem_ker, hθker]
  have hYK : Y ≤ K := hD.parabolic.1
  have hM₀K : M₀ ≤ K := hD.eq_perfectCore ▸ (perfectCore_le Y).trans hYK
  have hZY : centerOf K ≤ Y := hD.center_le.trans (Subgroup.map_subtype_le _)
  have hmapY : img θ' Y = (img θ Y).map C.subtype := by
    rw [img, img, Subgroup.map_map]
  obtain ⟨hBN, -⟩ := borel_self_normalizers Tag.G2 F
  have hBC : borelGroup Tag.G2 F ≤ C := hBN ▸ inf_le_left
  have hB : borelGroup Tag.G2 F ≤ img θ' Y := by
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (posUnipotent Tag.G2 F : Set (ModGL Tag.G2 F)) := by
      rw [← hBN] at hb
      exact hb.2
    have hbN' : (⟨b, hBC hb⟩ : ↥C) ∈
        Subgroup.normalizer (((posUnipotent Tag.G2 F).subgroupOf C : Subgroup ↥C) : Set ↥C) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.1 hbN u).trans Iff.rfl
    rw [hmapY]
    exact ⟨⟨b, hBC hb⟩, hNY hbN', rfl⟩
  have hYC : img θ' Y ≤ C := by
    rw [hmapY]
    exact Subgroup.map_subtype_le _
  obtain ⟨hcl, -⟩ := borel_overgroup_classification Tag.G2 F
  obtain ⟨-, -, hmemP, hleP, hP0, hPuniv, -⟩ := standard_parabolic_cells Tag.G2 F
  have hYi : ∃ i : Fin Tag.G2.rank, img θ' Y = parabolicSubgroup Tag.G2 F {i} := by
    have hJ := hcl _ hB hYC
    set J := {i | weylElt Tag.G2 F i 1 ∈ img θ' Y} with hJdef
    by_cases h0 : i0 ∈ J <;> by_cases h1 : i1 ∈ J
    · exfalso
      apply hne
      have hJu : J = Set.univ := by
        ext i
        simp only [Set.mem_univ, iff_true]
        rcases fin_two_cases i with rfl | rfl
        · exact h0
        · exact h1
      rw [hJu, hPuniv] at hJ
      rw [eq_top_iff]
      intro x _
      have hx : (x : ModGL Tag.G2 F) ∈ img θ' Y := by rw [hJ]; exact x.2
      rw [hmapY] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [← Subtype.ext hyx]
      exact hy
    · refine ⟨i0, ?_⟩
      rw [hJ]
      congr 1
      ext i
      rcases fin_two_cases i with rfl | rfl
      · simpa using h0
      · simp only [Set.mem_singleton_iff]
        exact ⟨fun h => absurd h h1, fun h => absurd h (by decide)⟩
    · refine ⟨i1, ?_⟩
      rw [hJ]
      congr 1
      ext i
      rcases fin_two_cases i with rfl | rfl
      · simp only [Set.mem_singleton_iff]
        exact ⟨fun h => absurd h h0, fun h => absurd h (by decide)⟩
      · simpa using h1
    · exfalso
      apply hns
      have hJe : J = ∅ := by
        ext i
        simp only [Set.mem_empty_iff_false, iff_false]
        rcases fin_two_cases i with rfl | rfl
        · exact h0
        · exact h1
      rw [hJe, hP0] at hJ
      have hsolv : Group.IsSolvable ↥(img θ' Y) := by
        rw [hJ]
        exact G2_isSolvable_borelGroup
      rw [hmapY] at hsolv
      exact Group.isSolvable_of_isSolvable_injective
        (f := ((img θ Y).equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom)
        ((img θ Y).equivMapOfInjective C.subtype C.subtype_injective).injective
  obtain ⟨i, hi⟩ := hYi
  have hMi : img θ' M₀ = perfectCore (parabolicSubgroup Tag.G2 F {i}) := by
    rw [hD.eq_perfectCore, img_perfectCore θ' hYK, hi]
  have hQP : parabolicRadical Tag.G2 F {i} ≤ parabolicSubgroup Tag.G2 F {i} :=
    (parabolicRadical_le_posUnipotent {i}).trans (posUnipotent_le_parabolicSubgroup {i})
  have hVK : V ≤ K := hD.V_le.trans hM₀K
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hD.V_elem.2 x x.2)⟩
  have hVQ : ∀ v (hv : v ∈ V), θ' ⟨v, hVK hv⟩ ∈ parabolicRadical Tag.G2 F {i} := by
    intro v hv
    have h := img_le_pCoreOf θ' hD.V_le (le_normalizer_of_comm hD.V_comm) hV2 hVK
      ⟨⟨v, hVK hv⟩, Subgroup.mem_subgroupOf.2 hv, rfl⟩
    rw [hMi, H13.NQCat.G2Rad.pCoreOf_perfectCore_parabolic hcard hf2 i] at h
    exact h
  have hQM : parabolicRadical Tag.G2 F {i} ≤ img θ' M₀ := by
    rw [hMi, ← H13.NQCat.G2Rad.pCoreOf_perfectCore_parabolic hcard hf2 i]
    exact CFSG.LieType.BorelTits.pCoreOf_le (r := 2) _
  have hQn : img θ' M₀ ≤ Subgroup.normalizer
      (parabolicRadical Tag.G2 F {i} : Set (ModGL Tag.G2 F)) := by
    rw [hMi]
    exact (perfectCore_le _).trans (parabolicSubgroup_le_normalizer_parabolicRadical {i})
  have hVC : ∀ v (hv : v ∈ V), θ' ⟨v, hVK hv⟩ ∈
      Subgroup.centralizer (parabolicRadical Tag.G2 F {i} : Set (ModGL Tag.G2 F)) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hD.comm_of_pCore θ' hθ'ker.le hQM hQn (pGroup_radical hcard {i}) hv (hVK hv) hq
  rcases fin_two_cases i with rfl | rfl
  ·
    have := Vol2Native.A312L.sl2_isSimple hK4
    obtain ⟨ρ, hu, -, hH, hW, hrange, hρker, -, -⟩ :=
      exceptional_ordinary_rank_one_central_image Tag.G2 F i0
    have hρ : Function.Injective ρ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      obtain ⟨l, hl, hxl⟩ := hρker x hx
      have hl1 : (l : F) = 1 := by
        have h2 : ((l : F) - 1) ^ 2 = 0 := by
          linear_combination hl + (1 - (l : F)) * (CharTwo.two_eq_zero : (2 : F) = 0)
        exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
      rw [Subgroup.mem_bot]
      refine Subtype.ext ?_
      rw [hxl, hl1, one_smul]
      rfl
    obtain ⟨ρ₁, hρ₁, -, -, hMinf₁⟩ := Vol2Native.A312L.levi_data hK4 i0
    have hLM : ρ.range ≤ parabolicLevi Tag.G2 F {i0} := by
      rw [hrange]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact xUnit_mem_parabolicLevi (Set.mem_singleton i0) c
      · exact yUnit_mem_parabolicLevi (Set.mem_singleton i0) c
    have hL : ⁅ρ.range, ρ.range⁆ = ρ.range := by
      have := CFSG.LinearGroups.special_linear_dimension_two_perfect (K := F) hK4
      exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ρ)
    have hLL₁ : ρ.range ≤ ρ₁.range := (le_perfectCore_of_perfect hLM hL).trans hMinf₁
    have hcardL : Nat.card ρ₁.range ≤ Nat.card ρ.range := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv,
        ← Nat.card_congr (MonoidHom.ofInjective hρ₁).toEquiv]
    have hMinf : perfectCore (parabolicLevi Tag.G2 F {i0}) ≤ ρ.range :=
      (Subgroup.eq_of_le_of_card_ge hLL₁ hcardL) ▸ hMinf₁
    obtain ⟨lam, hlams, hlamdec⟩ := exists_levi_proj hQP
      (parabolicSubgroup_le_normalizer_parabolicRadical {i0})
      (parabolicRadical_inf_parabolicLevi {i0}) (parabolicRadical_sup_parabolicLevi {i0}) hLM hL
      hMinf
    let eL : ↥ρ.range ≃* SL2 F := (MonoidHom.ofInjective hρ).symm
    have heL : ∀ l : ↥ρ.range, ρ (eL l) = (l : ModGL Tag.G2 F) := fun l =>
      congrArg Subtype.val ((MonoidHom.ofInjective hρ).apply_symm_apply l)
    have hinj : Set.InjOn (MonoidHom.id (ModGL Tag.G2 F))
        (perfectCore (parabolicSubgroup Tag.G2 F {i0}) : Set (ModGL Tag.G2 F)) :=
      fun _ _ _ _ h => h
    have hMN : img θ' M₀ =
        (perfectCore (parabolicSubgroup Tag.G2 F {i0})).map (MonoidHom.id (ModGL Tag.G2 F)) := by
      rw [Subgroup.map_id]
      exact hMi
    set ν := liftHom hM₀K θ' (MonoidHom.id (ModGL Tag.G2 F))
      (perfectCore (parabolicSubgroup Tag.G2 F {i0})) hinj hMN with hν
    have hνs := liftHom_surjective hM₀K θ' (MonoidHom.id (ModGL Tag.G2 F))
      (perfectCore (parabolicSubgroup Tag.G2 F {i0})) hinj hMN
    have hνspec : ∀ x : ↥M₀, ((ν x : ↥(perfectCore (parabolicSubgroup Tag.G2 F {i0}))) :
        ModGL Tag.G2 F) = θ' ⟨x, hM₀K x.2⟩ := fun x =>
      liftHom_spec hM₀K θ' (MonoidHom.id (ModGL Tag.G2 F))
        (perfectCore (parabolicSubgroup Tag.G2 F {i0})) hinj hMN x
    have hν1 : ∀ x : ↥M₀, ν x = 1 ↔ (x : A) ∈ centerOf K := by
      intro x
      rw [hν, liftHom_eq_one_iff, ← MonoidHom.mem_ker, hθ'ker]
      exact mem_centerOf_iff.symm
    let α : ↥M₀ →* SL2 F := eL.toMonoidHom.comp (lam.comp ν)
    have hαs : Function.Surjective α := eL.surjective.comp (hlams.comp hνs)
    have hαρ : ∀ x : ↥M₀, ρ (α x) = ((lam (ν x) : ↥ρ.range) : ModGL Tag.G2 F) := fun x =>
      heL _
    have hαker : IsPGroup 2 α.ker := by
      rintro ⟨x, hx⟩
      have h1 : lam (ν x) = 1 := (MulEquiv.map_eq_one_iff eL).mp hx
      have hq := hlamdec (ν x)
      rw [h1, OneMemClass.coe_one, inv_one, one_mul] at hq
      obtain ⟨k, hk⟩ := pGroup_radical hcard {i0} ⟨_, hq⟩
      have hk' : ν (x ^ 2 ^ k) = 1 := by
        rw [map_pow]
        apply Subtype.ext
        have := congrArg Subtype.val hk
        simpa using this
      have hxZ : (⟨((x ^ 2 ^ k : ↥M₀) : A), hM₀K (x ^ 2 ^ k).2⟩ : ↥K) ∈ Subgroup.center ↥K :=
        mem_centerOf_iff.1 ((hν1 _).1 hk')
      obtain ⟨l, hl⟩ := isPGroup_center hD.center ⟨_, hxZ⟩
      refine ⟨k + l, Subtype.ext (Subtype.ext ?_)⟩
      have hl' := congrArg (fun z : ↥(Subgroup.center ↥K) => ((z : ↥K) : A)) hl
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hl'
      show (x : A) ^ 2 ^ (k + l) = 1
      rw [pow_add, pow_mul]
      exact hl'
    have hO : CFSG.pCore 2 ↥M₀ = α.ker :=
      Vol2Native.A312L.pCore_two_eq_ker (Vol2Native.A312L.sl2_nonabelian hK4) α hαs hαker
    let c : ↥V → (Fin 2 → F) := fun v => coordBC (θ' ⟨v, hVK v.2⟩)
    have hcoord : ∀ v : ↥V, θ' ⟨v, hVK v.2⟩ = gX rB (c v 1) * gX rC (c v 0) := by
      intro v
      obtain ⟨s, t, hst⟩ := H13.Sec53F.G2.centerQ0 (hVQ v v.2) (hVC v v.2)
      have h : θ' ⟨v, hVK v.2⟩ = gX rB ((![t, s] : Fin 2 → F) 1) *
          gX rC ((![t, s] : Fin 2 → F) 0) := by simpa using hst
      show θ' ⟨v, hVK v.2⟩ = gX rB (coordBC (θ' ⟨v, hVK v.2⟩) 1) *
        gX rC (coordBC (θ' ⟨v, hVK v.2⟩) 0)
      rw [h, coordBC_eq]
    have hone : (1 : ModGL Tag.G2 F) = gX rB ((0 : Fin 2 → F) 1) * gX rC ((0 : Fin 2 → F) 0) := by
      simp [gX_zero]
    have hcmul : ∀ u v : ↥V, c (u * v) = c u + c v := by
      intro u v
      have h1 : θ' ⟨((u * v : ↥V) : A), hVK (u * v).2⟩ =
          gX rB ((c u + c v) 1) * gX rC ((c u + c v) 0) := by
        rw [show (⟨((u * v : ↥V) : A), hVK (u * v).2⟩ : ↥K) = ⟨u, hVK u.2⟩ * ⟨v, hVK v.2⟩ from rfl,
          map_mul, hcoord u, hcoord v, Pi.add_apply, Pi.add_apply, gX_add, gX_add,
          show gX rB (c u 1) * gX rC (c u 0) * (gX rB (c v 1) * gX rC (c v 0)) =
            gX rB (c u 1) * (gX rC (c u 0) * gX rB (c v 1)) * gX rC (c v 0) by group,
          ← (comm_bc (c v 1) (c u 0)).eq]
        group
      show coordBC _ = _
      rw [h1, coordBC_eq]
    let β : ↥V →* Multiplicative (Fin 2 → F) :=
      { toFun := fun v => Multiplicative.ofAdd (c v)
        map_one' := by
          show Multiplicative.ofAdd (coordBC (θ' 1)) = 1
          rw [map_one, hone, coordBC_eq]
          rfl
        map_mul' := fun u v => by
          show Multiplicative.ofAdd (c (u * v)) =
            Multiplicative.ofAdd (c u) * Multiplicative.ofAdd (c v)
          rw [hcmul]
          rfl }
    have hMV := le_normalizer_of_comm hD.V_comm
    have hVZ : ¬ V ≤ V ⊓ centerOf K := by
      intro h
      apply hD.V_ne
      rw [← hD.V_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact Subgroup.mem_centralizer_iff.1 (h hv).2.2 m (hM₀K hm)
    have hβker : β.ker = (V ⊓ centerOf K).subgroupOf V := by
      ext v
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show Multiplicative.ofAdd (c v) = 1 ↔ _
      constructor
      · intro h0
        have hc0 : c v = 0 := h0
        have h1 : (⟨v, hVK v.2⟩ : ↥K) ∈ θ'.ker := by
          rw [MonoidHom.mem_ker, hcoord v, hc0]
          simp [gX_zero]
        rw [hθ'ker] at h1
        exact ⟨v.2, mem_centerOf_iff.2 h1⟩
      · rintro ⟨-, hvZ⟩
        have h1 : θ' ⟨v, hVK v.2⟩ = 1 := by
          rw [← MonoidHom.mem_ker, hθ'ker]
          exact mem_centerOf_iff.1 hvZ
        show Multiplicative.ofAdd (coordBC (θ' ⟨v, hVK v.2⟩)) = 1
        rw [h1, hone, coordBC_eq]
        rfl
    have hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
        Multiplicative.toAdd (β v) = ((α a : SL2 F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
          Multiplicative.toAdd (β u) := by
      intro a u v huv
      show c v = _ *ᵥ c u
      have hv : θ' ⟨v, hVK v.2⟩ = θ' ⟨a, hM₀K a.2⟩ * θ' ⟨u, hVK u.2⟩ * (θ' ⟨a, hM₀K a.2⟩)⁻¹ := by
        rw [← map_mul, ← map_inv, ← map_mul]
        congr 1
        exact Subtype.ext huv
      set q : ModGL Tag.G2 F := ((lam (ν a) : ↥ρ.range) : ModGL Tag.G2 F)⁻¹ *
        ((ν a : ↥(perfectCore (parabolicSubgroup Tag.G2 F {i0}))) : ModGL Tag.G2 F) with hqdef
      have hq : q ∈ parabolicRadical Tag.G2 F {i0} := hlamdec (ν a)
      have hqc := Subgroup.mem_centralizer_iff.1 (hVC u u.2) _ hq
      have ha : θ' ⟨a, hM₀K a.2⟩ = ρ (α a) * q := by
        rw [hqdef, hαρ, ← hνspec]
        group
      have hv' : θ' ⟨v, hVK v.2⟩ = ρ (α a) * θ' ⟨u, hVK u.2⟩ * (ρ (α a))⁻¹ := by
        rw [hv, ha]
        calc ρ (α a) * q * θ' ⟨u, hVK u.2⟩ * (ρ (α a) * q)⁻¹ =
              ρ (α a) * (q * θ' ⟨u, hVK u.2⟩) * q⁻¹ * (ρ (α a))⁻¹ := by group
          _ = _ := by
            rw [hqc]
            group
      rw [hcoord u, g2_action ρ hu hH hW (α a) (c u)] at hv'
      show coordBC (θ' ⟨v, hVK v.2⟩) = _
      rw [hv', coordBC_eq]
    have hnat := isNaturalSection_of_equiv hMV hVZ α hαs hO.symm β hβker hequiv
    have hco : IsCoatom (img θ Y) := by
      refine ⟨hne, fun M' hM' => ?_⟩
      have hM'B : img θ' Y ≤ M'.map C.subtype := by
        rw [hmapY]
        exact Subgroup.map_mono hM'.le
      have hM'C : M'.map C.subtype ≤ C := Subgroup.map_subtype_le _
      have hJ := hcl _ (hB.trans hM'B) hM'C
      set J' := {j | weylElt Tag.G2 F j 1 ∈ M'.map C.subtype} with hJ'
      have h0 : i0 ∈ J' := by
        show weylElt Tag.G2 F i0 1 ∈ M'.map C.subtype
        apply hM'B
        rw [hi]
        exact (hmemP {i0} i0).2 rfl
      by_cases h1 : i1 ∈ J'
      · have hJu : J' = Set.univ := by
          ext j
          simp only [Set.mem_univ, iff_true]
          rcases fin_two_cases j with rfl | rfl
          · exact h0
          · exact h1
        rw [hJu, hPuniv] at hJ
        rw [eq_top_iff]
        intro x _
        have hx : (x : ModGL Tag.G2 F) ∈ M'.map C.subtype := by
          rw [hJ]
          exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        rw [← Subtype.ext hyx]
        exact hy
      · exfalso
        have hJ0 : J' = {i0} := by
          ext j
          simp only [Set.mem_singleton_iff]
          rcases fin_two_cases j with rfl | rfl
          · exact ⟨fun _ => rfl, fun _ => h0⟩
          · exact ⟨fun h => absurd h h1, fun h => absurd h (by decide)⟩
        rw [hJ0, ← hi, hmapY] at hJ
        exact hM'.ne (Subgroup.map_injective C.subtype_injective hJ).symm
    exact ⟨f, Or.inr (Or.inr (Or.inl hX')),
      isMaxParabolic2_of_coatom θ hθker.le hD.parabolic hD.ne_top hZY hco,
      isPSL2_modO2 hcard hf2 α hαs hαker,
      Or.inl ⟨F, inferInstance, Fintype.ofFinite F, by rw [Fintype.card_eq_nat_card, hcard],
        hnat⟩⟩
  ·
    exfalso
    apply hD.V_ne
    have hVN : ∀ v (hv : v ∈ V), θ' ⟨v, hVK hv⟩ ∈ N1 := by
      intro v hv
      rw [← H13.NQCat.G2Rad.centerOf_parabolicRadical_one]
      exact ⟨hVQ v hv, hVC v hv⟩
    have hcomm : ⁅V, M₀⁆ ≤ centerOf K := by
      rw [Subgroup.commutator_le]
      intro v hv m hm
      have hmP : θ' ⟨m, hM₀K hm⟩ ∈ perfectCore (parabolicSubgroup Tag.G2 F {i1}) := by
        rw [← hMi]
        exact ⟨⟨m, hM₀K hm⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
      have hc := Subgroup.mem_centralizer_iff.1
        (H13.NQCat.G2Rad.perfectCore_le_centralizer hmP) _ (hVN v hv)
      have h1 : ⁅(⟨v, hVK hv⟩ : ↥K), ⟨m, hM₀K hm⟩⁆ ∈ θ'.ker := by
        rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
          hc]
        group
      rw [hθ'ker] at h1
      exact mem_centerOf_iff.2 h1
    have hVZ : V ≤ centerOf K := hD.V_comm ▸ hcomm
    rw [← hD.V_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact Subgroup.mem_centralizer_iff.1 (hVZ hv).2 m (hM₀K hm)

theorem g2_holds :
    ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
      ∀ f : ℕ, 2 ≤ f → IsG2 2 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V :=
  fun A _ _ K Y M₀ V hD => g2_holds_base A K Y M₀ V hD.toBase

end CFSG.Quasithin.C35Pf
