module

public import CFSG.LocalAnalysis.UniquenessCase.UC6O633Defs
import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic
import CFSG.Quasithin.Background.B682Ambient
import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open
open CFSG.RankThree.FFModules (fixSub)
open scoped IsMulCommutative MatrixGroups

namespace UCK.M591D

theorem sylow_inf_center_eq_bot {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (hY : commutator Y = ⊤) (P : Sylow p Y) [IsMulCommutative (P : Subgroup Y)] :
    (P : Subgroup Y) ⊓ center Y = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzP, hzZ⟩ := mem_inf.1 hz
  have key : ∀ (k : ℕ) (g₀ : Y), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup Y) → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ center Y := pow_mem hzZ k
    rw [mul_assoc, ← mem_center_iff.1 hzk g₀, inv_mul_cancel_left]
  have htr := MonoidHom.transfer_eq_pow (MonoidHom.id (P : Subgroup Y)) z key
  have h1 : (MonoidHom.id (P : Subgroup Y)).transfer z = 1 := by
    have hz' : z ∈ commutator Y := by rw [hY]; exact mem_top z
    exact Abelianization.commutator_subset_ker _ hz'
  rw [h1, MonoidHom.id_apply] at htr
  have hpow : z ^ (P : Subgroup Y).index = 1 := by
    have := congrArg Subtype.val htr
    simpa using this.symm
  obtain ⟨a, ha⟩ := P.isPGroup' ⟨z, hzP⟩
  have hza : z ^ (p ^ a) = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hcop : Nat.Coprime (p ^ a) (P : Subgroup Y).index :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 P.not_dvd_index)
  have hord : orderOf z ∣ 1 := by
    have h2 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hza) (orderOf_dvd_of_pow_eq_one hpow)
    rwa [hcop.gcd_eq_one] at h2
  exact mem_bot.2 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord))

theorem not_dvd_card_center {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    (hY : commutator Y = ⊤) (hcyc : ∀ P : Sylow p Y, IsCyclic (P : Subgroup Y)) :
    ¬ p ∣ Nat.card (center Y) := by
  intro hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center Y) p hdvd
  have hzY : orderOf (z : Y) = p := by rw [Subgroup.orderOf_coe]; exact hz
  have hzp : IsPGroup p (zpowers (z : Y)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzY, pow_one])
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  haveI := hcyc P
  have hmem : (z : Y) ∈ (P : Subgroup Y) ⊓ center Y := ⟨hP (mem_zpowers _), z.2⟩
  rw [sylow_inf_center_eq_bot hY P, mem_bot] at hmem
  rw [hmem, orderOf_one] at hzY
  exact hp.out.one_lt.ne hzY

theorem exists_minimal_invariant {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [Nontrivial V] (ρ : Representation (ZMod 2) X V) :
    ∃ W : Submodule (ZMod 2) V, W ≠ ⊥ ∧ (∀ g, W ≤ W.comap (ρ g)) ∧
      ∀ W' : Submodule (ZMod 2) V, W' ≠ ⊥ → (∀ g, W' ≤ W'.comap (ρ g)) → W' ≤ W → W' = W := by
  haveI : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun W : Submodule (ZMod 2) V => (W : Set V)) SetLike.coe_injective
  obtain ⟨W, ⟨hW0, hWinv⟩, hWmin⟩ :=
    (Set.toFinite {W : Submodule (ZMod 2) V | W ≠ ⊥ ∧ ∀ g, W ≤ W.comap (ρ g)}).exists_minimal
      ⟨⊤, top_ne_bot, fun _ => le_top⟩
  exact ⟨W, hW0, hWinv, fun W' hW'0 hW'inv hle => le_antisymm hle (hWmin ⟨hW'0, hW'inv⟩ hle)⟩

theorem isIrreducible_quotientLift {X V : Type} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) X V) (W : Submodule (ZMod 2) V) (hW0 : W ≠ ⊥)
    (hWinv : ∀ g, W ≤ W.comap (ρ g))
    (hWmin : ∀ W' : Submodule (ZMod 2) V, W' ≠ ⊥ → (∀ g, W' ≤ W'.comap (ρ g)) → W' ≤ W → W' = W) :
    Representation.IsIrreducible (QuotientGroup.lift (ρ.subrepresentation W hWinv).ker
      (ρ.subrepresentation W hWinv) le_rfl) := by
  set ρW := ρ.subrepresentation W hWinv with hρW
  set ρbar := QuotientGroup.lift ρW.ker ρW le_rfl with hρbar
  have hact : ∀ (x : X) (w : W), ((ρbar (x : X ⧸ ρW.ker) w : W) : V) = ρ x w := fun _ _ => rfl
  have hWnt : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW0
  have hbt : (⊥ : Subrepresentation ρbar) ≠ ⊤ := by
    intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have : w ∈ (⊤ : Subrepresentation ρbar).toSubmodule := Submodule.mem_top
    rw [← h] at this
    exact hw ((Submodule.mem_bot _).1 this)
  haveI : Nontrivial (Subrepresentation ρbar) := ⟨⟨⊥, ⊤, hbt⟩⟩
  refine ⟨fun ψ => ?_⟩
  set U : Submodule (ZMod 2) V := ψ.toSubmodule.map W.subtype with hU
  have hUW : U ≤ W := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hUinv : ∀ g, U ≤ U.comap (ρ g) := by
    rintro g _ ⟨w, hw, rfl⟩
    refine ⟨ρbar (g : X ⧸ ρW.ker) w, ψ.apply_mem_toSubmodule _ hw, ?_⟩
    exact hact g w
  by_cases hU0 : U = ⊥
  · left
    apply Subrepresentation.toSubmodule_injective
    change ψ.toSubmodule = ⊥
    rw [eq_bot_iff]
    intro w hw
    have : (w : V) ∈ U := ⟨w, hw, rfl⟩
    rw [hU0] at this
    exact (Submodule.mem_bot _).2 (Subtype.ext ((Submodule.mem_bot _).1 this))
  · right
    apply Subrepresentation.toSubmodule_injective
    have hUeq := hWmin U hU0 hUinv hUW
    change ψ.toSubmodule = ⊤
    rw [eq_top_iff]
    intro w _
    have hw : (w : V) ∈ U := by rw [hUeq]; exact w.2
    obtain ⟨w', hw', hww'⟩ := hw
    rwa [← Subtype.ext hww']

end UCK.M591D

open UCK.M591D in
theorem UCK.k634_of_k461 (h : UCK.K461) : UCK.K634 := by
  intro X _ _ hX hQ hr3 V _ _ _ ρ hρ D hD3 hfix p hp hp2 hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hperf : commutator X = ⊤ := hQ.1
  haveI : Nontrivial X := by
    haveI : IsSimpleGroup (X ⧸ center X) := hQ.2
    by_contra hX1
    rw [not_nontrivial_iff_subsingleton] at hX1
    obtain ⟨a, b, hab⟩ := exists_pair_ne (X ⧸ center X)
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (congrArg _ (Subsingleton.elim a' b'))
  haveI : Nontrivial V := by
    by_contra hV1
    rw [not_nontrivial_iff_subsingleton] at hV1
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    apply hx
    apply hρ
    ext v
    exact Subsingleton.elim _ _
  have hcyc3 : ∀ P : Sylow 3 X, IsCyclic (P : Subgroup X) := fun P =>
    CFSG.Quasithin.isCyclic_of_pRank_le_one (by norm_num) le_top P.isPGroup' hr3.le
  have hZ3 : ¬ 3 ∣ Nat.card (center X) := not_dvd_card_center hperf hcyc3
  obtain ⟨W, hW0, hWinv, hWmin⟩ := exists_minimal_invariant ρ
  set ρW := ρ.subrepresentation W hWinv with hρW
  set X₀ : Subgroup X := ρW.ker with hX₀
  have hX₀top : X₀ ≠ ⊤ := by
    intro htop
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    have hwfix : w ∈ fixSub ρ D := by
      intro d _
      have hd : d ∈ X₀ := by rw [htop]; exact mem_top d
      have := congrArg (fun f : Module.End (ZMod 2) W => ((f ⟨w, hw⟩ : W) : V))
        (MonoidHom.mem_ker.1 hd)
      exact this
    rw [hfix] at hwfix
    exact hwfix
  have hX₀Z : X₀ ≤ center X :=
    (CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ X₀).resolve_right hX₀top
  have hX₀3 : ¬ 3 ∣ Nat.card X₀ := fun h3 => hZ3 (h3.trans (Subgroup.card_dvd_of_le hX₀Z))
  set ρbar := QuotientGroup.lift X₀ ρW le_rfl with hρbar
  set π := QuotientGroup.mk' X₀ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective X₀
  have hact : ∀ (x : X) (w : W), ((ρbar (π x) w : W) : V) = ρ x w := fun _ _ => rfl
  have hinj : Function.Injective ρbar := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    exact (QuotientGroup.eq_one_iff k).2 (MonoidHom.mem_ker.2 hx)
  have hirr : Representation.IsIrreducible ρbar := isIrreducible_quotientLift ρ W hW0 hWinv hWmin
  set Dbar : Subgroup (X ⧸ X₀) := D.map π with hDbar
  have hD3' : Nat.card Dbar = 3 := by
    have hdvd : Nat.card Dbar ∣ 3 := hD3 ▸ Subgroup.card_map_dvd D π
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exfalso
      have hDX₀ : D ≤ X₀ := by
        intro d hd
        have : π d ∈ Dbar := mem_map_of_mem π hd
        rw [Subgroup.card_eq_one.1 h1, mem_bot] at this
        exact (QuotientGroup.eq_one_iff d).1 this
      exact hX₀3 (hD3 ▸ Subgroup.card_dvd_of_le hDX₀)
    · exact h1
  have hncl : normalClosure (Dbar : Set (X ⧸ X₀)) = ⊤ := by
    have hD : normalClosure (D : Set X) = ⊤ := by
      refine (CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ _).resolve_left ?_
      intro hle
      exact hZ3 (hD3 ▸ Subgroup.card_dvd_of_le ((subset_normalClosure).trans hle))
    rw [hDbar, coe_map, ← map_normalClosure _ π hπs, hD, map_top_of_surjective π hπs]
  have hfixbar : fixSub ρbar Dbar = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hwV : (w : V) ∈ fixSub ρ D := by
      intro d hd
      have := congrArg Subtype.val (hw (π d) (mem_map_of_mem π hd))
      rwa [hact] at this
    rw [hfix] at hwV
    exact (Submodule.mem_bot _).2 (Subtype.ext ((Submodule.mem_bot _).1 hwV))
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ X₀)) = 1 := by
    rw [CFSG.SectionRank.pRank_quotient_eq X₀ hX₀3, hr3]
  have hcomm : commutator (X ⧸ X₀) = ⊤ := by
    rw [_root_.commutator_def, ← map_top_of_surjective π hπs, ← map_commutator, ← _root_.commutator_def,
      hperf]
  obtain ⟨n, F, _, _, φ, -, hF, -⟩ :=
    h (X ⧸ X₀) (hX.quotient X₀) W ρbar hinj hirr Dbar hD3' hncl hfixbar hrank hcomm
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (by rw [Fintype.card_eq_nat_card]; exact hF)
  have hcycΓ : ∀ H : Subgroup (X ⧸ X₀), IsPGroup p H → IsCyclic H := by
    intro H hH
    haveI := CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic hp2 (H.map φ.toMonoidHom)
      (hH.map φ.toMonoidHom)
    exact isCyclic_of_surjective (H.equivMapOfInjective φ.toMonoidHom φ.injective).symm
      (MulEquiv.surjective _)
  have hcycP : ∀ P : Sylow p X, IsCyclic (P : Subgroup X) := by
    intro P
    set f := π.subgroupMap (P : Subgroup X) with hf
    haveI : IsCyclic ((P : Subgroup X).map π) := hcycΓ _ (P.isPGroup'.map π)
    have hker : f.ker ≤ center (P : Subgroup X) := by
      intro x hx
      have hxX₀ : (x : X) ∈ X₀ := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
        exact (QuotientGroup.eq_one_iff _).1 this
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_center_iff.1 (hX₀Z hxX₀) y)
    haveI : IsMulCommutative (P : Subgroup X) := f.isMulCommutative_of_isCyclic_of_ker_le_center hker
    have hPZ := sylow_inf_center_eq_bot hperf P
    have hfinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxX₀ : (x : X) ∈ X₀ := by
        have := congrArg Subtype.val hx
        exact (QuotientGroup.eq_one_iff _).1 this
      have hmem : (x : X) ∈ (P : Subgroup X) ⊓ center X := ⟨x.2, hX₀Z hxX₀⟩
      rw [hPZ, mem_bot] at hmem
      exact Subtype.ext hmem
    exact isCyclic_of_surjective (MulEquiv.ofBijective f ⟨hfinj, π.subgroupMap_surjective _⟩).symm
      (MulEquiv.surjective _)
  obtain ⟨E, -, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup X)
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  have h1 := CFSG.SectionRank.le_pRank hp.one_lt hEP hEel hEcard
  have h2 := CFSG.SectionRank.pRank_le_one_of_isCyclic hp (hcycP P)
  omega

end CFSG.LocalAnalysis.UniquenessCase
