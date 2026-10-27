module

public import CFSG.RankThree.OddKernel.UnitriangularFlag
public import CFSG.RankThree.Classical.TransvectionGeneration
public import CFSG.LocalAnalysis.SectionRank.OddCover.PrimeThree
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Centralization

public section

namespace CFSG.RankThree.OddKernel

open Module Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.RankThree.Classical
open scoped commutatorElement

variable {p : ℕ} [hp : Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

@[expose] noncomputable def flagHom {G : Subgroup (V ≃ₗ[ZMod p] V)} {b : Basis (Fin 3) (ZMod p) V}
    (hb : IsFlagBasis G b) : G →* Multiplicative (ZMod p × ZMod p) where
  toFun g := Multiplicative.ofAdd (flagA b g, flagB b g)
  map_one' := by
    simp [flagA, flagB, Basis.coord_apply]
  map_mul' g h := by
    obtain ⟨h1, h2, -⟩ := flag_mul hb g.2 h.2
    simp only [coe_mul, h1, h2]
    rfl

theorem isTransvectionWith_of_flag {G : Subgroup (V ≃ₗ[ZMod p] V)}
    {b : Basis (Fin 3) (ZMod p) V} (hb : IsFlagBasis G b) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ G)
    (ha : flagA b g = 0) (hb' : flagB b g = 0) (hc : flagC b g ≠ 0) :
    IsTransvectionWith g (b 0) (flagC b g • b.coord 2) := by
  refine ⟨b.ne_zero 0, fun h0 => hc ?_, ?_, flag_transvection hb hg ha hb'⟩
  · have := congrArg (fun f : Dual (ZMod p) V => f (b 2)) h0
    simpa [Basis.coord_apply] using this
  · simp [Basis.coord_apply]

theorem exists_transvection_of_not_isCyclic [FiniteDimensional (ZMod p) V]
    (hV : finrank (ZMod p) V = 3) (G : Subgroup (V ≃ₗ[ZMod p] V)) (hG : IsPGroup p G)
    (hnc : ¬ IsCyclic G) : ∃ t ∈ G, ∃ v f, IsTransvectionWith t v f := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod p)
  have : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V)) DFunLike.coe_injective
  obtain ⟨b, hb⟩ := exists_flag_basis hV G hG
  by_contra hnone
  push Not at hnone
  set ψ := flagHom hb with hψ
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hg' : Multiplicative.ofAdd (flagA b g, flagB b g) = 1 := hg
    have ha : flagA b g = 0 := congrArg Prod.fst hg'
    have hb' : flagB b g = 0 := congrArg Prod.snd hg'
    have hc : flagC b g = 0 := by
      by_contra hc
      exact hnone g g.2 _ _ (isTransvectionWith_of_flag hb g.2 ha hb' hc)
    exact mem_bot.2 (Subtype.ext (flag_eq_one hb g.2 ha hb' hc))
  obtain ⟨k, hk⟩ := hG.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hk2
    apply hnc
    interval_cases k
    · rw [pow_zero] at hk
      exact @isCyclic_of_subsingleton _ _ (Finite.card_le_one_iff_subsingleton.1 hk.le)
    · rw [pow_one] at hk
      exact isCyclic_of_prime_card hk
  have hcardT : Nat.card (Multiplicative (ZMod p × ZMod p)) = p ^ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod, ZMod.card, sq]
  have hle := Nat.card_le_card_of_injective ψ hinj
  rw [hk, hcardT] at hle
  have hle' : Nat.card (Multiplicative (ZMod p × ZMod p)) ≤ Nat.card G := by
    rw [hk, hcardT]
    exact Nat.pow_le_pow_right hp.out.pos hk2
  have hsurj : Function.Surjective ψ := (hinj.bijective_of_nat_card_le hle').2
  obtain ⟨g₁, hg₁⟩ := hsurj (Multiplicative.ofAdd (1, 0))
  obtain ⟨g₂, hg₂⟩ := hsurj (Multiplicative.ofAdd (0, 1))
  have ha₁ : flagA b g₁ = 1 := congrArg Prod.fst hg₁
  have hb₁ : flagB b g₁ = 0 := congrArg Prod.snd hg₁
  have ha₂ : flagA b g₂ = 0 := congrArg Prod.fst hg₂
  have hb₂ : flagB b g₂ = 1 := congrArg Prod.snd hg₂
  have hcomm : g₁ * g₂ = g₂ * g₁ := hinj (by rw [map_mul, map_mul, mul_comm])
  have h12 := (flag_mul hb g₁.2 g₂.2).2.2
  have h21 := (flag_mul hb g₂.2 g₁.2).2.2
  have hval : (g₁ : V ≃ₗ[ZMod p] V) * g₂ = g₂ * g₁ := congrArg Subtype.val hcomm
  rw [hval, ha₁, hb₂] at h12
  rw [h21, ha₂, hb₁] at h12
  have : (1 : ZMod p) = 0 := by linear_combination -h12
  exact one_ne_zero this

theorem card_le_sq_of_commute [FiniteDimensional (ZMod p) V] (hV : finrank (ZMod p) V = 3)
    (G : Subgroup (V ≃ₗ[ZMod p] V)) (hG : IsPGroup p G)
    (hcomm : ∀ g ∈ G, ∀ h ∈ G, g * h = h * g) : Nat.card G ≤ p ^ 2 := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod p)
  have : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V)) DFunLike.coe_injective
  obtain ⟨b, hb⟩ := exists_flag_basis hV G hG
  set ψ := flagHom hb with hψ
  have hrel : ∀ g h : G, flagA b g * flagB b h = flagA b h * flagB b g := by
    intro g h
    have h1 := (flag_mul hb g.2 h.2).2.2
    have h2 := (flag_mul hb h.2 g.2).2.2
    rw [hcomm g g.2 h h.2] at h1
    rw [h1] at h2
    linear_combination h2
  have hker : Nat.card ψ.ker ≤ p := by
    let χ : ψ.ker →* Multiplicative (ZMod p) :=
      { toFun := fun g => Multiplicative.ofAdd (flagC b (g : G))
        map_one' := by simp [flagC, Basis.coord_apply]
        map_mul' := fun g h => by
          have hg : flagA b (g : G) = 0 := congrArg Prod.fst g.2
          simp only [coe_mul, (flag_mul hb (g : G).2 (h : G).2).2.2, hg, zero_mul, add_zero]
          rfl }
    have hχ : Function.Injective χ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      have hc : flagC b (g : G) = 0 := hg
      have hg' := g.2
      have ha : flagA b (g : G) = 0 := congrArg Prod.fst hg'
      have hb' : flagB b (g : G) = 0 := congrArg Prod.snd hg'
      exact mem_bot.2 (Subtype.ext (Subtype.ext (flag_eq_one hb (g : G).2 ha hb' hc)))
    have := Nat.card_le_card_of_injective χ hχ
    rwa [Nat.card_eq_fintype_card (α := Multiplicative (ZMod p)), Fintype.card_multiplicative,
      ZMod.card] at this
  have hrange : Nat.card ψ.range ≤ p := by
    by_cases hbot : ψ.range = ⊥
    · rw [hbot, card_bot]
      exact hp.out.one_lt.le
    · obtain ⟨⟨_, g₀, rfl⟩, hg₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
      have hu : (flagA b g₀, flagB b g₀) ≠ 0 := by
        intro h0
        apply hg₀
        apply Subtype.ext
        change Multiplicative.ofAdd (flagA b g₀, flagB b g₀) = 1
        rw [h0]
        rfl
      let f : ZMod p → Multiplicative (ZMod p × ZMod p) :=
        fun t => Multiplicative.ofAdd (t • (flagA b g₀, flagB b g₀))
      have hsub : (ψ.range : Set (Multiplicative (ZMod p × ZMod p))) ⊆ Set.range f := by
        rintro _ ⟨g, rfl⟩
        by_cases ha₀ : flagA b g₀ = 0
        · have hb₀ : flagB b g₀ ≠ 0 := fun h => hu (by rw [ha₀, h]; rfl)
          refine ⟨flagB b g * (flagB b g₀)⁻¹, ?_⟩
          have hag : flagA b g = 0 := by
            have := hrel g₀ g
            rw [ha₀, zero_mul] at this
            exact (mul_eq_zero.1 this.symm).resolve_right hb₀
          show Multiplicative.ofAdd _ = Multiplicative.ofAdd (flagA b g, flagB b g)
          congr 1
          ext
          · simp [ha₀, hag]
          · simp [mul_assoc, inv_mul_cancel₀ hb₀]
        · refine ⟨flagA b g * (flagA b g₀)⁻¹, ?_⟩
          show Multiplicative.ofAdd _ = Multiplicative.ofAdd (flagA b g, flagB b g)
          congr 1
          ext
          · simp [mul_assoc, inv_mul_cancel₀ ha₀]
          · have := hrel g₀ g
            simp only [Prod.smul_mk, smul_eq_mul]
            calc flagA b g * (flagA b g₀)⁻¹ * flagB b g₀
                = flagA b g * flagB b g₀ * (flagA b g₀)⁻¹ := by ring
              _ = flagA b g₀ * flagB b g * (flagA b g₀)⁻¹ := by rw [this]
              _ = flagB b g := by field_simp
      calc Nat.card ψ.range = Nat.card (ψ.range : Set (Multiplicative (ZMod p × ZMod p))) := rfl
        _ ≤ Nat.card (Set.range f) := Nat.card_mono (Set.toFinite _) hsub
        _ ≤ Nat.card (ZMod p) := Finite.card_range_le f
        _ = p := Nat.card_zmod p
  have hcard : Nat.card G = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  rw [hcard, sq]
  exact Nat.mul_le_mul hrange hker

theorem isPerfect_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Group.IsPerfect S := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hc : ⁅a, b⁆ ∈ commutator S := Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · exact h

theorem mem_statedSL_iff' {n : ℕ} {L : Type} [Field L] (A : GL (Fin n) L) :
    A ∈ CFSG.Assembly.LowTwoRank.StatedSL n L ↔ (A : Matrix (Fin n) (Fin n) L).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem prime_three_dimensional_simple_module_central_cover (hp3 : 3 < p) {S : Type*} [Group S]
    [Finite S] [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a)
    (hV : finrank (ZMod p) V = 3) (ι : S →* (V ≃ₗ[ZMod p] V)) (hι : Function.Injective ι)
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ s, ∀ v ∈ X, ι s v ∈ X) → X = ⊥ ∨ X = ⊤)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S)
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) (hCp : IsPGroup p π.ker) :
    π.ker = ⊥ ∧ pRank p E ≤ 2 ∧
      ((∀ Q : Sylow p S, IsCyclic Q) ∨
        ∀ g : V ≃ₗ[ZMod p] V, g ∈ ι.range ↔ LinearMap.det g.toLinearMap = 1) := by
  classical
  have : FiniteDimensional (ZMod p) V := Module.finite_of_finrank_pos (by omega)
  have hp2 : p ≠ 2 := by omega
  have : Group.IsPerfect S := isPerfect_of_isSimpleGroup hnab
  have hSL : ∀ h ∈ ι.range, LinearMap.det h.toLinearMap = 1 := by
    rintro _ ⟨s, rfl⟩
    have hdet := perfect_hom_eq_one_of_range_comm (LinearEquiv.det.comp ι)
      (fun a _ b _ => mul_comm a b)
    have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) (DFunLike.congr_fun hdet s)
    simpa [LinearEquiv.coe_det] using this
  have hdich : (∀ Q : Sylow p S, IsCyclic Q) ∨
      ∀ g : V ≃ₗ[ZMod p] V, g ∈ ι.range ↔ LinearMap.det g.toLinearMap = 1 := by
    by_cases hcyc : ∀ Q : Sylow p S, IsCyclic Q
    · exact Or.inl hcyc
    right
    push Not at hcyc
    obtain ⟨Q, hQ⟩ := hcyc
    have hGp : IsPGroup p ((Q : Subgroup S).map ι) := Q.isPGroup'.map ι
    have hGnc : ¬ IsCyclic ((Q : Subgroup S).map ι) := fun h => hQ
      (isCyclic_of_injective ((Q : Subgroup S).equivMapOfInjective ι hι).toMonoidHom
        (MulEquiv.injective _))
    obtain ⟨t, htG, v, f, ht⟩ := exists_transvection_of_not_isCyclic hV _ hGp hGnc
    obtain ⟨q, -, rfl⟩ := mem_map.1 htG
    let T : Set (V ≃ₗ[ZMod p] V) := Set.range fun s : S => ι s * ι q * (ι s)⁻¹
    have hT : ∀ τ ∈ T, ∃ v f, IsTransvectionWith τ v f := by
      rintro _ ⟨s, rfl⟩
      exact ⟨_, _, ht.conj (ι s)⟩
    have hconjT : ∀ g : S, ∀ x ∈ closure T, ι g * x * (ι g)⁻¹ ∈ closure T := by
      intro g x hx
      induction hx using closure_induction with
      | mem x hx =>
        obtain ⟨s, rfl⟩ := hx
        refine subset_closure ⟨g * s, ?_⟩
        simp only [map_mul, mul_inv_rev]
        group
      | one => simp
      | mul x y _ _ hx hy =>
        have : ι g * (x * y) * (ι g)⁻¹ = (ι g * x * (ι g)⁻¹) * (ι g * y * (ι g)⁻¹) := by group
        rw [this]
        exact mul_mem hx hy
      | inv x _ hx =>
        have : ι g * x⁻¹ * (ι g)⁻¹ = (ι g * x * (ι g)⁻¹)⁻¹ := by group
        rw [this]
        exact inv_mem hx
    have hq1 : q ≠ 1 := by
      rintro rfl
      obtain ⟨hv0, hf0, -, happ⟩ := ht
      obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
        by_contra h
        push Not at h
        exact hf0 (LinearMap.ext h)
      have := happ x
      rw [map_one] at this
      change x = x + f x • v at this
      rw [left_eq_add, smul_eq_zero] at this
      rcases this with h | h
      · exact hx h
      · exact hv0 h
    have hTrange : closure T = ι.range := by
      apply le_antisymm
      · rw [closure_le]
        rintro _ ⟨s, rfl⟩
        exact ⟨s * q * s⁻¹, by simp⟩
      · have hNn : ((closure T).comap ι).Normal := ⟨fun n hn g => by
          rw [mem_comap] at hn ⊢
          rw [map_mul, map_mul, map_inv]
          exact hconjT g _ hn⟩
        have hqN : q ∈ (closure T).comap ι := subset_closure ⟨1, by simp⟩
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((closure T).comap ι) with hbot | htop
        · rw [hbot, mem_bot] at hqN
          exact absurd hqN hq1
        · rintro _ ⟨s, rfl⟩
          have : s ∈ (closure T).comap ι := htop ▸ mem_top s
          exact this
    exact prime_three_space_irreducible_transvection_generation hV ι.range hSL
      (fun W hW => hirr W fun s v hv => hW _ ⟨s, rfl⟩ v hv) ⟨T, hT, hTrange.symm⟩
  have hker : π.ker = ⊥ := by
    rcases hdich with hcyc | hSLeq
    · obtain ⟨Q⟩ : Nonempty (Sylow p S) := inferInstance
      obtain ⟨C'⟩ : Nonempty (Sylow p π.ker) := inferInstance
      have hC'bot := (CFSG.ShultStronglyClosedTI.small_sylow_central_cover_bound π hπ hC C' Q).1
        (hcyc Q)
      have hC'top : (C' : Subgroup π.ker) = ⊤ := (C'.3 (hCp.to_subgroup ⊤) le_top).symm
      rw [hC'top] at hC'bot
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx⟩ : π.ker) ∈ (⊤ : Subgroup π.ker) := mem_top _
      rw [hC'bot, mem_bot] at this
      exact mem_bot.2 (congrArg Subtype.val this)
    · set bV := Module.finBasisOfFinrankEq (ZMod p) V hV
      set T : (V ≃ₗ[ZMod p] V) ≃* GL (Fin 3) (ZMod p) :=
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) V).symm.trans
          (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bV).toMulEquiv) with hT
      have hTdet : ∀ g, ((T g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).det =
          LinearMap.det g.toLinearMap := by
        intro g
        change (LinearMap.toMatrix bV bV (g : V →ₗ[ZMod p] V)).det = _
        rw [LinearMap.det_toMatrix]
      have hmap : ι.range.map T.toMonoidHom = CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod p) := by
        ext A
        rw [mem_map, mem_statedSL_iff']
        constructor
        · rintro ⟨g, hg, rfl⟩
          rw [MulEquiv.coe_toMonoidHom, hTdet]
          exact hSL g hg
        · intro hA
          refine ⟨T.symm A, (hSLeq _).2 ?_, T.apply_symm_apply A⟩
          rw [← hTdet, T.apply_symm_apply]
          exact hA
      let e : S ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod p) :=
        (MonoidHom.ofInjective hι).trans
          ((ι.range.equivMapOfInjective T.toMonoidHom T.injective).trans
            (MulEquiv.subgroupCongr hmap))
      let π' : E →* CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod p) := e.toMonoidHom.comp π
      have hπ' : Function.Surjective π' := e.surjective.comp hπ
      have hker' : π'.ker = π.ker := by
        ext x
        simp only [π', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.map_eq_one_iff]
      have hodd : Odd (Nat.card π'.ker) := by
        rw [hker']
        obtain ⟨k, hk⟩ := hCp.exists_card_eq
        rw [hk]
        exact (hp.out.odd_of_ne_two hp2).pow
      have := CFSG.SectionRank.OddCover.prime_classical_three_perfect_odd_extension_trivial
        hp.out hp2 (K := ZMod p) (ε := 1) (Or.inl ⟨rfl, Nat.card_zmod p, rfl⟩) π' hπ'
        (hker' ▸ hC) hodd
      rwa [hker'] at this
  refine ⟨hker, ?_, hdich⟩
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
  rw [pRank_eq_open_pRank_top]
  refine SectionRank.pRank_le hp.out.one_lt fun A _ hA => ?_
  have hinj : Function.Injective (ι.comp π) := hι.comp hπinj
  have hAp : IsPGroup p A := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hA.2 x x.2)⟩
  have hcomm : ∀ g ∈ A.map (ι.comp π), ∀ h ∈ A.map (ι.comp π), g * h = h * g := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := hA.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩
    rw [← map_mul, ← map_mul]
    exact congrArg (ι.comp π) (congrArg Subtype.val this)
  have := card_le_sq_of_commute hV (A.map (ι.comp π)) (hAp.map _) hcomm
  rwa [Subgroup.card_map_of_injective hinj] at this

end CFSG.RankThree.OddKernel
