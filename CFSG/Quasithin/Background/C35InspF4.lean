module

public import CFSG.Quasithin.Background.C35InspF4A
public import CFSG.Quasithin.Background.C35InspBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique Matrix CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (rad_le_parabolic parabolic_le_normalizer_rad
  isPGroup_rad)
open scoped commutatorElement

theorem f4_holds_base :
    ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Base K Y M₀ V →
      ∀ f : ℕ, Odd f → 3 ≤ f → Is2F4 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V := by
  intro A _ _ K Y M₀ V hD f _ _ hX
  classical
  have hX' := hX
  obtain ⟨a, F, _, _, _, ha, hfa, hcard, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  subst hfa
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag F) := finite_modGL
  set C := F4.reeGamma F a with hCdef
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
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a F w₀ hw₀).1
  have hU₀ : IsSylowTwoOf ((F4.reeFixedPosUnipotent F a).subgroupOf C) ⊤ :=
    hPU ▸ isSylowTwoOf_top_of_sylow PU
  obtain ⟨g, hNY, hne, hns⟩ := hD.exists_conj_normalizer φ hφker.le hφs hU₀
  set θ := (MulAut.conj g⁻¹).toMonoidHom.comp φ with hθ
  have hθker : θ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hφker]
  set θ' : ↥K →* ModGL F4.tag F := C.subtype.comp θ with hθ'
  have hθ'ker : θ'.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker, hθ', MonoidHom.comp_apply, Subgroup.coe_subtype,
      OneMemClass.coe_eq_one, ← MonoidHom.mem_ker, hθker]
  have hYK : Y ≤ K := hD.parabolic.1
  have hM₀K : M₀ ≤ K := hD.eq_perfectCore ▸ (perfectCore_le Y).trans hYK
  have hZY : centerOf K ≤ Y := hD.center_le.trans (Subgroup.map_subtype_le _)
  have hmapY : img θ' Y = (img θ Y).map C.subtype := by
    rw [img, img, Subgroup.map_map]
  have hBN : C ⊓ Subgroup.normalizer (F4.reeFixedPosUnipotent F a : Set (ModGL F4.tag F)) =
      F4.reeFixedBorel F a := reeGamma_inf_normalizer_reeFixedPosUnipotent
  have hBC : F4.reeFixedBorel F a ≤ C := hBN ▸ inf_le_left
  have hB : F4.reeFixedBorel F a ≤ img θ' Y := by
    intro b hb
    have hbN : b ∈ Subgroup.normalizer
        (F4.reeFixedPosUnipotent F a : Set (ModGL F4.tag F)) := by
      rw [← hBN] at hb
      exact hb.2
    have hbN' : (⟨b, hBC hb⟩ : ↥C) ∈ Subgroup.normalizer
        (((F4.reeFixedPosUnipotent F a).subgroupOf C : Subgroup ↥C) : Set ↥C) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.1 hbN u).trans Iff.rfl
    rw [hmapY]
    exact ⟨⟨b, hBC hb⟩, hNY hbN', rfl⟩
  have hYC : img θ' Y ≤ C := by
    rw [hmapY]
    exact Subgroup.map_subtype_le _
  have hcl := ree_Borel_overgroup_classification F4 a F
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hPle : ∀ (A' : Subgroup (ModGL F4.tag F)) (i : Fin F4.fixedOrbitCount),
      F4.reeFixedBorel F a ≤ A' →
      canonicalRep (coxeterSystem F4.tag) F (F4.fixedOrbitElement i) ∈ A' →
      F4.reeLocalParabolic F a i ≤ A' := by
    intro A' i hBA hn
    rw [← reeParabolic_singleton]
    refine sup_le hBA ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨i', hi', rfl⟩
    rw [Set.mem_singleton_iff.1 hi']
    exact hn
  have hgen : ∀ A' : Subgroup (ModGL F4.tag F), F4.reeFixedBorel F a ≤ A' →
      canonicalRep (coxeterSystem F4.tag) F (F4.fixedOrbitElement ⟨0, by decide⟩) ∈ A' →
      canonicalRep (coxeterSystem F4.tag) F (F4.fixedOrbitElement ⟨1, by decide⟩) ∈ A' →
      C ≤ A' := by
    intro A' hBA h0 h1
    rw [hCdef, large_Ree_simple_pair_generation a F hcard]
    exact sup_le ((large_Ree_local_block_Sylow_action F4 a F _).1.trans (hPle A' _ hBA h0))
      ((large_Ree_local_block_Sylow_action F4 a F _).1.trans (hPle A' _ hBA h1))
  have hnP : ∀ i : Fin F4.fixedOrbitCount,
      canonicalRep (coxeterSystem F4.tag) F (F4.fixedOrbitElement i) ∈
        F4.reeLocalParabolic F a i := fun i => by
    rw [← reeParabolic_singleton]
    exact canonicalRep_mem_reeParabolic (t := F4) (K := F) (a := a) (Set.mem_singleton i)
  have htop : ∀ M' : Subgroup ↥C, C ≤ M'.map C.subtype → M' = ⊤ := by
    intro M' hCM
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := hCM x.2
    rw [← Subtype.ext hyx]
    exact hy
  have hYa : ∃ j : Fin F4.fixedOrbitCount, img θ' Y = F4.reeLocalParabolic F a j := by
    have hJ := (hcl _ hB hYC).1
    by_cases h0 : canonicalRep (coxeterSystem F4.tag) F
        (F4.fixedOrbitElement ⟨0, by decide⟩) ∈ img θ' Y <;>
      by_cases h1 : canonicalRep (coxeterSystem F4.tag) F
        (F4.fixedOrbitElement ⟨1, by decide⟩) ∈ img θ' Y
    · exfalso
      apply hne
      rw [hmapY] at h0 h1
      exact htop _ (hgen _ (hB.trans hmapY.le) h0 h1)
    · refine ⟨⟨0, by decide⟩, ?_⟩
      rw [hJ, ← reeParabolic_singleton]
      congr 1
      ext i
      rcases hcases i with rfl | rfl
      · simpa using h0
      · simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        exact ⟨fun h => absurd h h1, fun h => absurd h (by decide)⟩
    · refine ⟨⟨1, by decide⟩, ?_⟩
      rw [hJ, ← reeParabolic_singleton]
      congr 1
      ext i
      rcases hcases i with rfl | rfl
      · simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        exact ⟨fun h => absurd h h0, fun h => absurd h (by decide)⟩
      · simpa using h1
    · exfalso
      apply hns
      have hJe : {i | canonicalRep (coxeterSystem F4.tag) F (F4.fixedOrbitElement i) ∈
          img θ' Y} = ∅ := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rcases hcases i with rfl | rfl
        · exact h0
        · exact h1
      rw [hJe, reeParabolic_empty] at hJ
      have hsolv : Group.IsSolvable ↥(img θ' Y) := by
        rw [hJ]
        exact isSolvable_reeFixedBorel
      rw [hmapY] at hsolv
      exact Group.isSolvable_of_isSolvable_injective
        (f := ((img θ Y).equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom)
        ((img θ Y).equivMapOfInjective C.subtype C.subtype_injective).injective
  obtain ⟨j, hja⟩ := hYa
  have hMa : img θ' M₀ = perfectCore (F4.reeLocalParabolic F a j) := by
    rw [hD.eq_perfectCore, img_perfectCore θ' hYK, hja]
  have hVK : V ≤ K := hD.V_le.trans hM₀K
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hD.V_elem.2 x x.2)⟩
  have hVQ : ∀ v (hv : v ∈ V), θ' ⟨v, hVK hv⟩ ∈ F4.reeFixedOrbitComplementUnipotent F a j := by
    intro v hv
    have h := img_le_pCoreOf θ' hD.V_le (le_normalizer_of_comm hD.V_comm) hV2 hVK
      ⟨⟨v, hVK hv⟩, Subgroup.mem_subgroupOf.2 hv, rfl⟩
    rw [hMa, pCoreOf_perfectCore_f4 ha hcard j] at h
    exact h
  have hQM : F4.reeFixedOrbitComplementUnipotent F a j ≤ img θ' M₀ := by
    rw [hMa, ← pCoreOf_perfectCore_f4 ha hcard j]
    exact CFSG.LieType.BorelTits.pCoreOf_le (r := 2) _
  have hQn : img θ' M₀ ≤ Subgroup.normalizer
      (F4.reeFixedOrbitComplementUnipotent F a j : Set (ModGL F4.tag F)) := by
    rw [hMa]
    exact (perfectCore_le (F4.reeLocalParabolic F a j)).trans (parabolic_le_normalizer_rad j)
  have hVC : ∀ v (hv : v ∈ V), θ' ⟨v, hVK hv⟩ ∈ Subgroup.centralizer
      (F4.reeFixedOrbitComplementUnipotent F a j : Set (ModGL F4.tag F)) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hD.comm_of_pCore θ' hθ'ker.le hQM hQn (isPGroup_rad ha hcard j) hv (hVK hv) hq
  have hVZ' : ¬ V ≤ centerOf K := by
    intro h
    apply hD.V_ne
    rw [← hD.V_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact Subgroup.mem_centralizer_iff.1 (h hv).2 m (hM₀K hm)
  rcases hcases j with rfl | rfl
  ·
    have hρσ : ∀ x : F, largeReeRhoHom F a (largeReeSigma a x) = x := fun x =>
      (largeReeRhoHom_apply a (largeReeSigma a x)).trans (largeReeSigma_pow_two_pow hcard x)
    have : CharP F 2 := ‹CharP F F4.prime›
    have hf2' : 2 ≤ 2 * a + 1 := by omega
    have hE4 : ∃ s : Finset F, s.card = 4 := by
      refine exists_finset_card_four ?_
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) hf2'
    have := sl2_isSimple hE4
    obtain ⟨lam, hlams, hlamdec⟩ := levi_proj_f4 ha hcard
    have hRinj : Function.Injective (largeReeA1Hom F a) := largeReeA1Hom_injective
    let eL : ↥(largeReeA1Hom F a).range ≃* SL2 F := (MonoidHom.ofInjective hRinj).symm
    have heL : ∀ l : ↥(largeReeA1Hom F a).range, largeReeA1Hom F a (eL l) =
        (l : ModGL F4.tag F) := fun l =>
      congrArg Subtype.val ((MonoidHom.ofInjective hRinj).apply_symm_apply l)
    have hinj : Set.InjOn (MonoidHom.id (ModGL F4.tag F))
        (perfectCore (F4.reeLocalParabolic F a ⟨0, by decide⟩) : Set (ModGL F4.tag F)) :=
      fun _ _ _ _ h => h
    have hMN : img θ' M₀ = (perfectCore (F4.reeLocalParabolic F a ⟨0, by decide⟩)).map
        (MonoidHom.id (ModGL F4.tag F)) := by
      rw [Subgroup.map_id]
      exact hMa
    set ν := liftHom hM₀K θ' (MonoidHom.id (ModGL F4.tag F))
      (perfectCore (F4.reeLocalParabolic F a ⟨0, by decide⟩)) hinj hMN with hν
    have hνs := liftHom_surjective hM₀K θ' (MonoidHom.id (ModGL F4.tag F))
      (perfectCore (F4.reeLocalParabolic F a ⟨0, by decide⟩)) hinj hMN
    have hνspec : ∀ x : ↥M₀,
        ((ν x : ↥(perfectCore (F4.reeLocalParabolic F a ⟨0, by decide⟩))) : ModGL F4.tag F) =
          θ' ⟨x, hM₀K x.2⟩ := fun x =>
      liftHom_spec hM₀K θ' (MonoidHom.id (ModGL F4.tag F))
        (perfectCore (F4.reeLocalParabolic F a ⟨0, by decide⟩)) hinj hMN x
    have hν1 : ∀ x : ↥M₀, ν x = 1 ↔ (x : A) ∈ centerOf K := by
      intro x
      rw [hν, liftHom_eq_one_iff, ← MonoidHom.mem_ker, hθ'ker]
      exact mem_centerOf_iff.symm
    let α : ↥M₀ →* SL2 F := eL.toMonoidHom.comp (lam.comp ν)
    have hαs : Function.Surjective α := eL.surjective.comp (hlams.comp hνs)
    have hαρ : ∀ x : ↥M₀, largeReeA1Hom F a (α x) =
        ((lam (ν x) : ↥(largeReeA1Hom F a).range) : ModGL F4.tag F) := fun x => heL _
    have hQ2 := isPGroup_rad ha hcard ⟨0, by decide⟩
    have hαker : IsPGroup 2 α.ker := by
      rintro ⟨x, hx⟩
      have h1 : lam (ν x) = 1 := (MulEquiv.map_eq_one_iff eL).mp hx
      have hq := hlamdec (ν x)
      rw [h1, OneMemClass.coe_one, inv_one, one_mul] at hq
      obtain ⟨k, hk⟩ := hQ2 ⟨_, hq⟩
      have hk2 : ((ν x : ↥(perfectCore (F4.reeLocalParabolic F a ⟨0, by decide⟩))) :
          ModGL F4.tag F) ^ 2 ^ k = 1 :=
        (SubgroupClass.coe_pow _ _).symm.trans (congrArg Subtype.val hk)
      have hk' : ν (x ^ 2 ^ k) = 1 := by
        rw [map_pow]
        exact Subtype.ext ((SubgroupClass.coe_pow _ _).trans hk2)
      have hxZ : (⟨((x ^ 2 ^ k : ↥M₀) : A), hM₀K (x ^ 2 ^ k).2⟩ : ↥K) ∈ Subgroup.center ↥K :=
        mem_centerOf_iff.1 ((hν1 _).1 hk')
      obtain ⟨l, hl⟩ := isPGroup_center hD.center ⟨_, hxZ⟩
      refine ⟨k + l, Subtype.ext (Subtype.ext ?_)⟩
      have hl' := congrArg (fun z : ↥(Subgroup.center ↥K) => ((z : ↥K) : A)) hl
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hl'
      show (x : A) ^ 2 ^ (k + l) = 1
      rw [pow_add, pow_mul]
      exact hl'
    have hO : CFSG.pCore 2 ↥M₀ = α.ker := pCore_two_eq_ker (sl2_nonabelian hE4) α hαs hαker
    let c : ↥V → (Fin 2 → F) := fun v => coordFH a (θ' ⟨v, hVK v.2⟩)
    have hcoord : ∀ v : ↥V, θ' ⟨v, hVK v.2⟩ = sylowF a F 0 (largeReeRhoHom F a (c v 1)) *
        sylowH a F 0 (largeReeRhoHom F a (c v 0)) := by
      intro v
      obtain ⟨g', i', hgi⟩ := centerV0_f4 hcard (hVQ v v.2) (hVC v v.2)
      have h : θ' ⟨v, hVK v.2⟩ =
          sylowF a F 0 (largeReeRhoHom F a ((![largeReeSigma a i', largeReeSigma a g'] :
            Fin 2 → F) 1)) *
          sylowH a F 0 (largeReeRhoHom F a ((![largeReeSigma a i', largeReeSigma a g'] :
            Fin 2 → F) 0)) := by
        rw [hgi]
        show sylowF a F 0 g' * sylowH a F 0 i' = sylowF a F 0 (largeReeRhoHom F a
          (largeReeSigma a g')) * sylowH a F 0 (largeReeRhoHom F a (largeReeSigma a i'))
        rw [hρσ, hρσ]
      show θ' ⟨v, hVK v.2⟩ = sylowF a F 0 (largeReeRhoHom F a (coordFH a (θ' ⟨v, hVK v.2⟩) 1)) *
        sylowH a F 0 (largeReeRhoHom F a (coordFH a (θ' ⟨v, hVK v.2⟩) 0))
      rw [h, coordFH_eq hcard]
    have hone : (1 : ModGL F4.tag F) =
        sylowF a F 0 (largeReeRhoHom F a ((0 : Fin 2 → F) 1)) *
          sylowH a F 0 (largeReeRhoHom F a ((0 : Fin 2 → F) 0)) := by
      have h6 : sylowF a F 0 0 = 1 :=
        CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.fam_zero (m := a) (K := F) (n := 6)
          (by norm_num)
      have h8 : sylowH a F 0 0 = 1 :=
        CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.fam_zero (m := a) (K := F) (n := 8)
          (by norm_num)
      rw [Pi.zero_apply, Pi.zero_apply, map_zero, h6, h8, one_mul]
    have hcmul : ∀ u v : ↥V, c (u * v) = c u + c v := by
      intro u v
      have h1 : θ' ⟨((u * v : ↥V) : A), hVK (u * v).2⟩ =
          sylowF a F 0 (largeReeRhoHom F a ((c u + c v) 1)) *
            sylowH a F 0 (largeReeRhoHom F a ((c u + c v) 0)) := by
        rw [show (⟨((u * v : ↥V) : A), hVK (u * v).2⟩ : ↥K) = ⟨u, hVK u.2⟩ * ⟨v, hVK v.2⟩ from rfl,
          map_mul, hcoord u, hcoord v, Pi.add_apply, Pi.add_apply, map_add, map_add,
          f4_FH_mul ha hcard]
      show coordFH a _ = _
      rw [h1, coordFH_eq hcard]
    let β : ↥V →* Multiplicative (Fin 2 → F) :=
      { toFun := fun v => Multiplicative.ofAdd (c v)
        map_one' := by
          show Multiplicative.ofAdd (coordFH a (θ' 1)) = 1
          rw [map_one, hone, coordFH_eq hcard]
          rfl
        map_mul' := fun u v => by
          show Multiplicative.ofAdd (c (u * v)) =
            Multiplicative.ofAdd (c u) * Multiplicative.ofAdd (c v)
          rw [hcmul]
          rfl }
    have hMV := le_normalizer_of_comm hD.V_comm
    have hVZ : ¬ V ≤ V ⊓ centerOf K := fun h => hVZ' fun v hv => (h hv).2
    have hβker : β.ker = (V ⊓ centerOf K).subgroupOf V := by
      ext v
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show Multiplicative.ofAdd (c v) = 1 ↔ _
      constructor
      · intro h0
        have hc0 : c v = 0 := h0
        have h1 : (⟨v, hVK v.2⟩ : ↥K) ∈ θ'.ker := by
          rw [MonoidHom.mem_ker, hcoord v, hc0, ← hone]
        rw [hθ'ker] at h1
        exact ⟨v.2, mem_centerOf_iff.2 h1⟩
      · rintro ⟨-, hvZ⟩
        have h1 : θ' ⟨v, hVK v.2⟩ = 1 := by
          rw [← MonoidHom.mem_ker, hθ'ker]
          exact mem_centerOf_iff.1 hvZ
        show Multiplicative.ofAdd (coordFH a (θ' ⟨v, hVK v.2⟩)) = 1
        rw [h1, hone, coordFH_eq hcard]
        rfl
    have hequiv : ∀ (x : ↥M₀) (u v : ↥V), (v : A) = x * u * x⁻¹ →
        Multiplicative.toAdd (β v) =
          ((α x : SL2 F) : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β u) := by
      intro x u v huv
      show c v = _ *ᵥ c u
      have hv : θ' ⟨v, hVK v.2⟩ =
          θ' ⟨x, hM₀K x.2⟩ * θ' ⟨u, hVK u.2⟩ * (θ' ⟨x, hM₀K x.2⟩)⁻¹ := by
        rw [← map_mul, ← map_inv, ← map_mul]
        congr 1
        exact Subtype.ext huv
      set q : ModGL F4.tag F := ((lam (ν x) : ↥(largeReeA1Hom F a).range) : ModGL F4.tag F)⁻¹ *
        ((ν x : ↥(perfectCore (F4.reeLocalParabolic F a ⟨0, by decide⟩))) :
          ModGL F4.tag F) with hqdef
      have hq : q ∈ F4.reeFixedOrbitComplementUnipotent F a ⟨0, by decide⟩ := hlamdec (ν x)
      have hqc := Subgroup.mem_centralizer_iff.1 (hVC u u.2) _ hq
      have hx' : θ' ⟨x, hM₀K x.2⟩ = largeReeA1Hom F a (α x) * q := by
        rw [hqdef, hαρ, ← hνspec]
        group
      have hv' : θ' ⟨v, hVK v.2⟩ =
          largeReeA1Hom F a (α x) * θ' ⟨u, hVK u.2⟩ * (largeReeA1Hom F a (α x))⁻¹ := by
        rw [hv, hx']
        calc largeReeA1Hom F a (α x) * q * θ' ⟨u, hVK u.2⟩ * (largeReeA1Hom F a (α x) * q)⁻¹ =
              largeReeA1Hom F a (α x) * (q * θ' ⟨u, hVK u.2⟩) * q⁻¹ *
                (largeReeA1Hom F a (α x))⁻¹ := by group
          _ = _ := by
            rw [hqc]
            group
      rw [hcoord u, f4_action ha hcard (α x) (c u)] at hv'
      show coordFH a (θ' ⟨v, hVK v.2⟩) = _
      rw [hv', coordFH_eq hcard]
    have hnat := isNaturalSection_of_equiv hMV hVZ α hαs hO.symm β hβker hequiv
    have hco : IsCoatom (img θ Y) := by
      refine ⟨hne, fun M' hM' => ?_⟩
      have hM'B : img θ' Y ≤ M'.map C.subtype := by
        rw [hmapY]
        exact Subgroup.map_mono hM'.le
      have hM'C : M'.map C.subtype ≤ C := Subgroup.map_subtype_le _
      have hJ := (hcl _ (hB.trans hM'B) hM'C).1
      have h0 : canonicalRep (coxeterSystem F4.tag) F (F4.fixedOrbitElement ⟨0, by decide⟩) ∈
          M'.map C.subtype := by
        apply hM'B
        rw [hja]
        exact hnP _
      by_cases h1 : canonicalRep (coxeterSystem F4.tag) F
          (F4.fixedOrbitElement ⟨1, by decide⟩) ∈ M'.map C.subtype
      · exact htop _ (hgen _ (hB.trans hM'B) h0 h1)
      · exfalso
        have hJ1 : {i | canonicalRep (coxeterSystem F4.tag) F (F4.fixedOrbitElement i) ∈
            M'.map C.subtype} = {⟨0, by decide⟩} := by
          ext i
          simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
          rcases hcases i with rfl | rfl
          · exact ⟨fun _ => rfl, fun _ => h0⟩
          · exact ⟨fun h => absurd h h1, fun h => absurd h (by decide)⟩
        rw [hJ1, reeParabolic_singleton, ← hja, hmapY] at hJ
        exact hM'.ne (Subgroup.map_injective C.subtype_injective hJ).symm
    exact ⟨2 * a + 1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hX')))),
      isMaxParabolic2_of_coatom θ hθker.le hD.parabolic hD.ne_top hZY hco,
      isPSL2_modO2 hcard hf2' α hαs hαker,
      Or.inl ⟨F, inferInstance, Fintype.ofFinite _, by rw [Fintype.card_eq_nat_card, hcard], hnat⟩⟩
  ·
    exfalso
    apply hVZ'
    rw [← hD.V_comm, Subgroup.commutator_le]
    intro v hv m hm
    have hmP : θ' ⟨m, hM₀K hm⟩ ∈ perfectCore (F4.reeLocalParabolic F a ⟨1, by decide⟩) := by
      rw [← hMa]
      exact ⟨⟨m, hM₀K hm⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
    obtain ⟨i, hi⟩ := centerV1_f4 hcard (hVQ v hv) (hVC v hv)
    have hc := Subgroup.mem_centralizer_singleton_iff.1
      (perfectCore_P1_le_centralizer ha hcard i hmP)
    rw [← hi] at hc
    have h1 : ⁅(⟨v, hVK hv⟩ : ↥K), ⟨m, hM₀K hm⟩⁆ ∈ θ'.ker := by
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
        ← hc]
      group
    rw [hθ'ker] at h1
    exact mem_centerOf_iff.2 h1

theorem f4_holds :
    ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
      ∀ f : ℕ, Odd f → 3 ≤ f → Is2F4 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V :=
  fun A _ _ K Y M₀ V hD => f4_holds_base A K Y M₀ V hD.toBase

end CFSG.Quasithin.C35Pf
