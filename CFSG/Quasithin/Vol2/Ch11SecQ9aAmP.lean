module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmN
public import CFSG.Quasithin.Vol2.Ch11SecQ9aG2C
public import CFSG.Quasithin.Vol2.Ch11SecQ9aG2D
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverTorus
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4E
public import CFSG.Quasithin.Vol2.Ch11SecQ9aG2B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open CFSG.Open
open scoped commutatorElement

theorem commutator_pCoreOf_ne_bot_of_radical {G : Type*} [Group G] [Finite G]
    {P B R : Subgroup G} (hBP : B ≤ P) (hPB : P ≤ Subgroup.normalizer (B : Set G))
    (hRP : R ≤ P) (hPR : P ≤ Subgroup.normalizer (R : Set G)) (hR : IsPGroup 2 ↥R) {d u : G}
    (hd : d ∈ B) (hu : u ∈ R) (h : ⁅⁅d, u⁆, d⁆ ≠ 1) : ⁅pCoreOf 2 B, B⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvB : ⁅d, u⁆ ∈ B := by
    rw [commutatorElement_def, show d * u * d⁻¹ * u⁻¹ = d * (u * d⁻¹ * u⁻¹) by group]
    exact B.mul_mem hd ((Subgroup.mem_normalizer_iff.mp (hPB (hRP hu)) _).mp (B.inv_mem hd))
  have hvR : ⁅d, u⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPR (hBP hd)) u).mp hu) (R.inv_mem hu)
  have hO : B ⊓ R ≤ pCoreOf 2 B :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, hPR (hBP hx)⟩) (hR.to_le inf_le_right)
  intro h0
  have hc := Subgroup.commutator_mem_commutator (hO ⟨hvB, hvR⟩) hd
  rw [h0, Subgroup.mem_bot] at hc
  exact h hc

section G2

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover

theorem g2_commutator_ne_bot {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (i : Fin Tag.G2.rank) :
    ⁅pCoreOf 2 (perfectCore (parabolicSubgroup Tag.G2 K {i})),
      perfectCore (parabolicSubgroup Tag.G2 K {i})⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4 : ∃ s : Finset K, s.card = 4 :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four hK.ge
  obtain ⟨hRP, -, -, -, -, -, -, -, -, -, -, -, h13⟩ :=
    parabolic_root_radical_Levi_factors (τ := Tag.G2) (K := K) {i}
  obtain ⟨-, hR2, -⟩ := h13 2
  obtain ⟨t, ht⟩ := C11P9A.exists_units_ne_one hK
  have hrange : (simpleRootSL2 Tag.G2 K i).range ≤
      perfectCore (parabolicSubgroup Tag.G2 K {i}) := by
    have hSL : ⁅(⊤ : Subgroup (SL2 K)), ⊤⁆ = ⊤ := Group.isPerfect_def.mp
      (CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K) hK4)
    have hp : ⁅(simpleRootSL2 Tag.G2 K i).range, (simpleRootSL2 Tag.G2 K i).range⁆ =
        (simpleRootSL2 Tag.G2 K i).range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hSL]
    calc (simpleRootSL2 Tag.G2 K i).range = perfectCore (simpleRootSL2 Tag.G2 K i).range :=
          (perfectCore_eq_self_of_perfect hp).symm
      _ ≤ perfectCore (parabolicSubgroup Tag.G2 K {i}) :=
          perfectCore_mono (C11P9A.range_simpleRootSL2_le_parabolic i)
  have hd : torusElt Tag.G2 K i t ∈ perfectCore (parabolicSubgroup Tag.G2 K {i}) :=
    hrange ⟨HSL t, simpleRootSL2_HSL i t⟩
  set γ : Fin Tag.G2.rank → ℤ := fun _ => 1 with hγdef
  have hγ : IsRoot Tag.G2 γ := by
    have e : reflect Tag.G2 ⟨0, by decide⟩ (Pi.single ⟨1, by decide⟩ 1) = γ := by
      funext k
      fin_cases k <;> decide
    exact e ▸ IsRoot.reflect ⟨0, by decide⟩ (IsRoot.basis ⟨1, by decide⟩)
  have hγR : γ ∈ parabolicRadicalRoots Tag.G2 {i} := by
    refine ⟨⟨hγ, by decide⟩, fun h => ?_⟩
    obtain ⟨k, hk⟩ : ∃ k : Fin Tag.G2.rank, k ≠ i := by
      fin_cases i
      · exact ⟨⟨1, by decide⟩, by decide⟩
      · exact ⟨⟨0, by decide⟩, by decide⟩
    have := h.1.2 k (by simpa using hk)
    simp [hγdef] at this
  have hu : pinnedX Tag.G2 K γ 1 ∈ parabolicRadical Tag.G2 K {i} :=
    (le_iSup₂ (f := fun α (_ : α ∈ parabolicRadicalRoots Tag.G2 {i}) =>
      rootSubgroup Tag.G2 K α) γ hγR) (Subgroup.subset_closure ⟨1, rfl⟩)
  set χ : Kˣ := rootChar K γ (Pi.mulSingle i t) with hχ
  have hχ1 : (χ : K) ≠ 1 := by
    intro h1
    have hχe : χ = t ^ cartanCoord γ i := rootChar_mulSingle γ i t
    have hc : cartanCoord γ i = 1 ∨ cartanCoord γ i = -1 := by
      fin_cases i <;> decide
    apply ht
    have h1' : χ = 1 := Units.ext h1
    rcases hc with hc | hc <;> rw [hχe, hc] at h1'
    · simpa using h1'
    · simpa using h1'
  have hconj : ∀ c : K, torusElt Tag.G2 K i t * pinnedX Tag.G2 K γ c *
      (torusElt Tag.G2 K i t)⁻¹ = pinnedX Tag.G2 K γ ((χ : K) * c) := fun c => by
    rw [← torusVec_mulSingle, torusVec_conj_pinnedX hγ]
  refine commutator_pCoreOf_ne_bot_of_radical (perfectCore_le _)
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)) hRP
    (parabolicSubgroup_le_normalizer_parabolicRadical {i}) hR2 hd hu ?_
  have h1 : ⁅torusElt Tag.G2 K i t, pinnedX Tag.G2 K γ 1⁆ = pinnedX Tag.G2 K γ ((χ : K) - 1) := by
    rw [commutatorElement_def, hconj, pinnedX_neg, ← pinnedX_add, mul_one, sub_eq_add_neg]
  have hg : ∀ a b : ModGL Tag.G2 K, a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := fun a b => by
    group
  rw [h1, commutatorElement_def, hg, pinnedX_neg, hconj, ← pinnedX_add]
  intro h0
  rw [← pinnedX_zero Tag.G2 (R := K) γ] at h0
  have h2 := pinnedHom_injective Tag.G2 K γ (a₁ := Multiplicative.ofAdd _)
    (a₂ := Multiplicative.ofAdd 0) h0
  have h3 : ((χ : K) - 1) + (χ : K) * -((χ : K) - 1) = 0 := Multiplicative.ofAdd.injective h2
  have h4 : ((χ : K) - 1) * ((χ : K) - 1) = 0 := by linear_combination -h3
  rcases mul_eq_zero.mp h4 with h5 | h5 <;> exact hχ1 (sub_eq_zero.mp h5)

theorem parabRadical_g2 {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Blueprint.LieModel Q .G2 0 2 2) {S B : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hB : IsL24Sub S B) : ⁅pCoreOf 2 B, B⁆ ≠ ⊥ := by
  have hX := C11P9A.chevalleyExceptionalModel_of_lieModel hQ
  have := (CFSG.LieType.Simplicity.fam_g2_simplicity Q 2 2 hX).2
  obtain ⟨K, _, _, _, φ, hK, -, hres, -⟩ :=
    CFSG.QuasithinUnique.Setup.X6.even_rank_two_residual_G2 hX hS
  have hK' : Nat.card K = 4 := by rw [hK]; norm_num
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hpp := C11P9A.parabPair_of_residual hS hres fun j =>
    C11P9A.dInf_map_ne_bot φ.symm (factG2FourParabNonsolv_holds K hK' j)
  set π : Q →* ModGL Tag.G2 K := (adjointGroup Tag.G2 K).subtype.comp φ.toMonoidHom with hπ
  have hπi : Function.Injective π := Subtype.val_injective.comp φ.injective
  have key : ∀ j : Fin 2, ⁅pCoreOf 2 (CFSG.QuasithinUnique.Setup.X6.dInf
      (((parabolicSubgroup Tag.G2 K {CFSG.QuasithinUnique.Setup.X6.g2Index j}).subgroupOf
        (adjointGroup Tag.G2 K)).map φ.symm.toMonoidHom)),
      CFSG.QuasithinUnique.Setup.X6.dInf
      (((parabolicSubgroup Tag.G2 K {CFSG.QuasithinUnique.Setup.X6.g2Index j}).subgroupOf
        (adjointGroup Tag.G2 K)).map φ.symm.toMonoidHom)⁆ ≠ ⊥ := by
    intro j h0
    have hBe : (CFSG.QuasithinUnique.Setup.X6.dInf
        (((parabolicSubgroup Tag.G2 K {CFSG.QuasithinUnique.Setup.X6.g2Index j}).subgroupOf
          (adjointGroup Tag.G2 K)).map φ.symm.toMonoidHom)).map π =
        perfectCore (parabolicSubgroup Tag.G2 K {CFSG.QuasithinUnique.Setup.X6.g2Index j}) := by
      rw [CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore, map_perfectCore,
        Subgroup.map_map]
      have e : π.comp φ.symm.toMonoidHom = (adjointGroup Tag.G2 K).subtype := by
        ext x
        simp [hπ]
      rw [e, Subgroup.map_subgroupOf_eq_of_le (parabolicSubgroup_le_adjointGroup Tag.G2 K _)]
    have h1 := commutator_pCoreOf_map_eq_bot π
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr hπi, inf_bot_eq]) h0
    rw [hBe] at h1
    exact g2_commutator_ne_bot hK' _ h1
  rcases hpp.eq_or_eq_of_isL24Sub hB with hj | hj | hj
  · rw [hj]
    exact key 0
  · rw [hj]
    exact key 1
  · exfalso
    obtain ⟨a, ha⟩ := exists_card_eq_of_SL2 (hj ▸ hB).2.2.2
    rw [Subgroup.card_top] at ha
    have h9 : 9 ∣ Nat.card Q := by
      have hN := (factG2FourBorelNorm_holds K hK').2
      have hd := Subgroup.card_subgroup_dvd_card (Subgroup.normalizer
        (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
          Subgroup ↥(adjointGroup Tag.G2 K)) : Set ↥(adjointGroup Tag.G2 K)))
      rw [hN, ← Nat.card_congr φ.toEquiv] at hd
      exact (Dvd.intro_left _ rfl).trans hd
    rw [ha] at h9
    have hc : Nat.Coprime 9 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
    have := hc.dvd_of_dvd_mul_left h9
    omega

end G2

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
