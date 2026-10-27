module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveSylow
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcG2
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcF4
import CFSG.RankThree.PartOne.KGD.D4Weyl
import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusLocalCore
import CFSG.LieType.OutStructureOrthNorm
import CFSG.Quasithin.Vol2.F134LieG2Power

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Quasithin.KGC31

private instance instFactPrime31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩

attribute [local instance] finite_modGL

private theorem mem_normalizer_of_pow_map {C : Type*} [Group C] [Fact (Nat.Prime 31)]
    {P : Subgroup C} [Finite ↥P] {u : C} {n : ℕ} (hP : IsPGroup 31 ↥P) (hn : ¬ 31 ∣ n)
    (hu : ∀ y ∈ P, u * y ^ n * u⁻¹ ∈ P) :
    u ∈ Subgroup.normalizer (P : Set C) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  let f : C →* C := MulAut.conj u
  change P.map f = P
  have hmaple : P.map f ≤ P := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨y, hyeq⟩ := (hP.powEquiv' hn).surjective ⟨k, hk⟩
    have hyval : (y : C) ^ n = k := by
      simpa using congrArg Subtype.val hyeq
    have h := hu (y : C) y.2
    rw [hyval] at h
    simpa [f, MulAut.conj_apply] using h
  have hcard : Nat.card (P.map f) = Nat.card P :=
    Subgroup.card_map_of_injective (f := f) (show Function.Injective ⇑f from
      fun a b h => (MulAut.conj u).injective h)
  exact Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm)

theorem weylFive_native_split
    {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .D4 ∨ τ = .F4) {K : Type}
    [Field K] [Finite K] (hK : 31 ∣ Nat.card K - 1) (g : ModGL τ K)
    (hg : g ∈ adjointGroup τ K) (a : Fin τ.rank → Kˣ) (σ : K ≃+* K)
    (E : Subgroup (ModGL τ K)) (hEC : E ≤ adjointGroup τ K) (hE : ∀ x ∈ E, x ^ 31 = 1)
    (hθE : ∀ x ∈ E, (g * rootDiagUnit τ a) * Units.map (entrywiseHom σ.toRingHom) x *
      (g * rootDiagUnit τ a)⁻¹ ∈ E) :
    ∃ k : ℕ, ∀ x ∈ E, (fun y : ModGL τ K => (g * rootDiagUnit τ a) *
      Units.map (entrywiseHom σ.toRingHom) y * (g * rootDiagUnit τ a)⁻¹)^[Nat.card (WeylGroup τ)]
        x = x ^ k := by
  classical
  let C : Subgroup (ModGL τ K) := adjointGroup τ K
  let d : ModGL τ K := rootDiagUnit τ a
  let h : ModGL τ K := g * d
  let ε : ModGL τ K →* ModGL τ K := Units.map (entrywiseHom σ.toRingHom)
  let θf : ModGL τ K →* ModGL τ K := (MulAut.conj h).toMonoidHom.comp ε
  have hθf_apply : ∀ y : ModGL τ K, θf y = h * ε y * h⁻¹ := by
    intro y
    change (MulAut.conj h) (ε y) = h * ε y * h⁻¹
    rw [MulAut.conj_apply]
  have hε_inj : Function.Injective ε :=
    Units.map_injective (entrywise_injective σ.toRingHom)
  have hθf_inj : Function.Injective θf := by
    intro x y hxy
    rw [hθf_apply, hθf_apply] at hxy
    exact hε_inj (mul_left_cancel (mul_right_cancel hxy))
  have hθC_mem : ∀ y ∈ C, θf y ∈ C := by
    intro y hy
    rw [hθf_apply]
    have hσy : ε y ∈ adjointGroup τ K :=
      CFSG.RankThree.Chevalley.SteinbergBN.units_map_entrywiseHom_mem_adjointGroup
        σ.toRingHom (show y ∈ adjointGroup τ K from hy)
    have hd : d * ε y * d⁻¹ ∈ adjointGroup τ K := conj_rootDiagUnit_mem_adjointGroup a hσy
    have e : h * ε y * h⁻¹ = g * (d * ε y * d⁻¹) * g⁻¹ := by
      simp only [h]
      group
    rw [e]
    exact C.mul_mem (C.mul_mem (show g ∈ C from hg) hd) (C.inv_mem (show g ∈ C from hg))
  let θC : C →* C := (θf.comp C.subtype).codRestrict C fun y => hθC_mem y y.2
  have hθC_coe : ∀ y : C, ((θC y : C) : ModGL τ K) = θf (y : ModGL τ K) := fun _ => rfl
  have hθC_inj : Function.Injective θC := by
    intro x y hxy
    apply Subtype.ext
    apply hθf_inj
    exact congrArg (fun z : C => (z : ModGL τ K)) hxy
  let D : Subgroup C := (torusGroup τ K).subgroupOf C
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact (triangular_borel_structure.{0, 0} τ K).1 (x : ModGL τ K)
      (Subgroup.mem_subgroupOf.1 hx) (y : ModGL τ K) (Subgroup.mem_subgroupOf.1 hy)
  have hW : ¬ 31 ∣ Nat.card (WeylGroup τ) := by
    rcases hτ with rfl | rfl | rfl
    · exact CFSG.LocalAnalysis.RankFourTheoremC.crossExc_not_dvd_card_weylGroup_G2
        (p := 31) (by norm_num) (by norm_num)
    · exact CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 (p := 31)
        (by norm_num) (by norm_num)
    · exact CFSG.LocalAnalysis.RankFourTheoremC.crossExc_not_dvd_card_weylGroup_F4
        (p := 31) (by norm_num) (by norm_num)
  have hDidx : ¬ 31 ∣ D.index :=
    CFSG.LocalAnalysis.RankFourTheoremC.crossExc_not_dvd_index_torusGroup (p := 31)
      (by norm_num) hW hK
  obtain ⟨S₀⟩ : Nonempty (Sylow 31 D) := inferInstance
  let P₀sub : Subgroup C := (S₀ : Subgroup D).map D.subtype
  have hP₀sub_p : IsPGroup 31 P₀sub := (Sylow.isPGroup' S₀).map D.subtype
  have hP₀sub_idx : ¬ 31 ∣ P₀sub.index := by
    rw [Subgroup.index_map_subtype]
    intro hdvd
    rcases (Nat.Prime.dvd_mul (Fact.out : Nat.Prime 31)).1 hdvd with h1 | h2
    · exact S₀.not_dvd_index h1
    · exact hDidx h2
  let P₀ : Sylow 31 C := hP₀sub_p.toSylow hP₀sub_idx
  have hP₀coe : (P₀ : Subgroup C) = P₀sub := IsPGroup.toSylow_coe hP₀sub_p hP₀sub_idx
  have hP₀D : (P₀ : Subgroup C) ≤ D := by
    intro x hx
    rw [hP₀coe] at hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hP₀p : IsPGroup 31 ↥(P₀ : Subgroup C) := Sylow.isPGroup' P₀
  let E_C : Subgroup C := E.subgroupOf C
  have hE_C_p : IsPGroup 31 E_C := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one]
    exact Subtype.ext (by
      simpa using hE ((x : C) : ModGL τ K) (Subgroup.mem_subgroupOf.1 x.2))
  obtain ⟨P₁, hE₁⟩ := hE_C_p.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P₀ P₁
  have hc₁ : ∀ y ∈ (P₀ : Subgroup C), c * y * c⁻¹ ∈ (P₁ : Subgroup C) := by
    intro y hy
    have hmem : c * y * c⁻¹ ∈ ((c • P₀ : Sylow 31 C) : Subgroup C) := by
      rw [sylow_mem_smul_iff]
      have e : c⁻¹ * (c * y * c⁻¹) * c = y := by group
      rwa [e]
    rwa [hc] at hmem
  have hc₂ : ∀ w ∈ (P₁ : Subgroup C), c⁻¹ * w * c ∈ (P₀ : Subgroup C) := by
    intro w hw
    exact (sylow_mem_smul_iff (g := c) (x := w) (P := P₀)).1 (hc ▸ hw)
  have hθE_sub : E_C.map θC ≤ E_C := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact hθE (y : ModGL τ K) (Subgroup.mem_subgroupOf.1 hy)
  have hθE_eq : E_C.map θC = E_C := by
    refine Subgroup.eq_of_le_of_card_ge hθE_sub ?_
    rw [Subgroup.card_map_of_injective hθC_inj]
  let Q : Subgroup C := (P₁ : Subgroup C).map θC
  have hQp : IsPGroup 31 Q := (Sylow.isPGroup' P₁).map θC
  have hQcard : Nat.card Q = Nat.card (P₁ : Subgroup C) :=
    Subgroup.card_map_of_injective hθC_inj
  have hQidx : Q.index = (P₁ : Subgroup C).index := by
    have h1 := Subgroup.card_mul_index Q
    have h2 := Subgroup.card_mul_index (P₁ : Subgroup C)
    rw [hQcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (P₁ : Subgroup C))) (h1.trans h2.symm)
  have hQnotdvd : ¬ 31 ∣ Q.index := by
    rw [hQidx]
    exact P₁.not_dvd_index
  let P₂ : Sylow 31 C := hQp.toSylow hQnotdvd
  have hP₂coe : (P₂ : Subgroup C) = Q := IsPGroup.toSylow_coe hQp hQnotdvd
  have hE₂ : E_C ≤ (P₂ : Subgroup C) := by
    rw [hP₂coe]
    calc E_C = E_C.map θC := hθE_eq.symm
      _ ≤ (P₁ : Subgroup C).map θC := Subgroup.map_mono hE₁
  have hAut := sylowAutBoundAll_thirtyOne_split hτ hK
  have hP₁ab : ∀ x ∈ (P₁ : Subgroup C), ∀ y ∈ (P₁ : Subgroup C), x * y = y * x :=
    (hAut P₁).1
  have hP₂ab : ∀ x ∈ (P₂ : Subgroup C), ∀ y ∈ (P₂ : Subgroup C), x * y = y * x :=
    (hAut P₂).1
  let N : Subgroup C := Subgroup.centralizer ((E_C : Subgroup C) : Set C)
  have hP₁N : (P₁ : Subgroup C) ≤ N := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact hP₁ab e (hE₁ he) x hx
  have hP₂N : (P₂ : Subgroup C) ≤ N := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact hP₂ab e (hE₂ he) x hx
  obtain ⟨z, hzN, hz⟩ :=
    sylow_exists_smul_eq_of_le (G := C) (H := N) (P := P₂) (Q := P₁) hP₂N hP₁N
  have hzconj : ∀ w ∈ (P₂ : Subgroup C), z * w * z⁻¹ ∈ (P₁ : Subgroup C) := by
    intro w hw
    have hmem : z * w * z⁻¹ ∈ ((z • P₂ : Sylow 31 C) : Subgroup C) := by
      rw [sylow_mem_smul_iff]
      have e : z⁻¹ * (z * w * z⁻¹) * z = w := by group
      rwa [e]
    rwa [hz] at hmem
  let βC : C →* C :=
    (MulAut.conj (c⁻¹ * z)).toMonoidHom.comp (θC.comp (MulAut.conj c).toMonoidHom)
  have hβC_apply : ∀ y : C, βC y = c⁻¹ * z * θC (c * y * c⁻¹) * (c⁻¹ * z)⁻¹ := by
    intro y
    change (MulAut.conj (c⁻¹ * z)) (θC (c * y * c⁻¹)) =
      c⁻¹ * z * θC (c * y * c⁻¹) * (c⁻¹ * z)⁻¹
    rw [MulAut.conj_apply]
  have hβP₀ : ∀ y ∈ (P₀ : Subgroup C), βC y ∈ (P₀ : Subgroup C) := by
    intro y hy
    have h1 : c * y * c⁻¹ ∈ (P₁ : Subgroup C) := hc₁ y hy
    have h2 : θC (c * y * c⁻¹) ∈ (P₂ : Subgroup C) := by
      rw [hP₂coe]
      exact Subgroup.mem_map_of_mem θC h1
    have h3 : z * θC (c * y * c⁻¹) * z⁻¹ ∈ (P₁ : Subgroup C) := hzconj _ h2
    have h4 : c⁻¹ * (z * θC (c * y * c⁻¹) * z⁻¹) * c ∈ (P₀ : Subgroup C) := hc₂ _ h3
    have e : c⁻¹ * z * θC (c * y * c⁻¹) * (c⁻¹ * z)⁻¹ =
        c⁻¹ * (z * θC (c * y * c⁻¹) * z⁻¹) * c := by group
    rw [hβC_apply y, e]
    exact h4
  obtain ⟨s, hσs⟩ := CFSG.LieType.OutStructure.exists_pow_eq_of_ringAut σ
  let S : ℕ := ringChar K ^ s
  have hσS : ∀ x : K, σ x = x ^ S := hσs
  have hs31 : ¬ 31 ∣ S := by
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 31 (by
      rw [Nat.card_units]
      exact hK)
    intro hs
    have hζS : ζ ^ S = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hζ]
      exact hs
    have hσζ : σ (ζ : K) = 1 := by
      rw [hσS]
      simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hζS
    have hζ1 : ζ = 1 := by
      apply Units.ext
      exact σ.injective (by
        rw [hσζ]
        simp)
    rw [hζ1, orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  have hσy : ∀ y ∈ (P₀ : Subgroup C), ε (y : ModGL τ K) = (y : ModGL τ K) ^ S := by
    intro y hy
    have hyT : (y : ModGL τ K) ∈ torusGroup τ K :=
      Subgroup.mem_subgroupOf.1 (hP₀D hy)
    exact CFSG.Quasithin.F134.LieG2.units_map_entrywiseHom_eq_pow (σ := σ.toRingHom)
      (m := S) hσS (torusGroup_le_diagonalGroup hyT)
  let u : ModGL τ K := (c : ModGL τ K)⁻¹ * (z : ModGL τ K) * g * d *
    ε (c : ModGL τ K) * d⁻¹
  have huC : u ∈ C := by
    have hσcC : ε (c : ModGL τ K) ∈ adjointGroup τ K :=
      CFSG.RankThree.Chevalley.SteinbergBN.units_map_entrywiseHom_mem_adjointGroup
        σ.toRingHom (show (c : ModGL τ K) ∈ adjointGroup τ K from c.2)
    have hdconjC : d * ε (c : ModGL τ K) * d⁻¹ ∈ adjointGroup τ K :=
      conj_rootDiagUnit_mem_adjointGroup a hσcC
    have e : u = ((c : ModGL τ K)⁻¹ * (z : ModGL τ K) * g) *
        (d * ε (c : ModGL τ K) * d⁻¹) := by
      simp only [u]
      group
    rw [e]
    exact C.mul_mem (C.mul_mem (C.mul_mem
      (C.inv_mem (show (c : ModGL τ K) ∈ C from c.2))
      (show (z : ModGL τ K) ∈ C from z.2)) (show g ∈ C from hg)) hdconjC
  let uC : C := ⟨u, huC⟩
  have huC_coe : ((uC : C) : ModGL τ K) = u := rfl
  have hdcomm : ∀ y ∈ (P₀ : Subgroup C),
      d * (y : ModGL τ K) ^ S = (y : ModGL τ K) ^ S * d := by
    intro y hy
    exact rootDiagUnit_mul_comm_of_mem_torusGroup a
      (Subgroup.pow_mem _ (Subgroup.mem_subgroupOf.1 (hP₀D hy)) S)
  have hβeq : ∀ y ∈ (P₀ : Subgroup C),
      (βC y : ModGL τ K) = u * (y : ModGL τ K) ^ S * u⁻¹ := by
    intro y hy
    have hcoe : (βC y : ModGL τ K) =
        (c : ModGL τ K)⁻¹ * (z : ModGL τ K) *
          θf ((c : ModGL τ K) * (y : ModGL τ K) * (c : ModGL τ K)⁻¹) *
            ((c : ModGL τ K)⁻¹ * (z : ModGL τ K))⁻¹ := by
      change ((MulAut.conj (c⁻¹ * z)) (θC (c * y * c⁻¹)) : ModGL τ K) = _
      rw [MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hθC_coe]
    rw [hcoe]
    have hθlin : θf ((c : ModGL τ K) * (y : ModGL τ K) * (c : ModGL τ K)⁻¹) =
        h * (ε (c : ModGL τ K) * ε (y : ModGL τ K) * (ε (c : ModGL τ K))⁻¹) *
          h⁻¹ := by
      rw [hθf_apply]
      simp only [map_mul, map_inv]
    rw [hθlin, hσy y hy]
    have hdu : d⁻¹ * (y : ModGL τ K) ^ S * d = (y : ModGL τ K) ^ S := by
      have h1 : d * (y : ModGL τ K) ^ S * d⁻¹ = (y : ModGL τ K) ^ S := by
        rw [hdcomm y hy]
        group
      calc d⁻¹ * (y : ModGL τ K) ^ S * d
          = d⁻¹ * (d * (y : ModGL τ K) ^ S * d⁻¹) * d := by rw [h1]
        _ = (y : ModGL τ K) ^ S := by group
    have hmid : d * ε (c : ModGL τ K) * (y : ModGL τ K) ^ S *
        (ε (c : ModGL τ K))⁻¹ * d⁻¹ =
        d * ε (c : ModGL τ K) * d⁻¹ * (y : ModGL τ K) ^ S * d *
          (ε (c : ModGL τ K))⁻¹ * d⁻¹ := by
      calc d * ε (c : ModGL τ K) * (y : ModGL τ K) ^ S *
            (ε (c : ModGL τ K))⁻¹ * d⁻¹
          = d * ε (c : ModGL τ K) * (d⁻¹ * (y : ModGL τ K) ^ S * d) *
              (ε (c : ModGL τ K))⁻¹ * d⁻¹ := by rw [hdu]
        _ = d * ε (c : ModGL τ K) * d⁻¹ * (y : ModGL τ K) ^ S * d *
              (ε (c : ModGL τ K))⁻¹ * d⁻¹ := by group
    have e1 : (c : ModGL τ K)⁻¹ * (z : ModGL τ K) *
          (h * (ε (c : ModGL τ K) * (y : ModGL τ K) ^ S *
            (ε (c : ModGL τ K))⁻¹) * h⁻¹) *
            ((c : ModGL τ K)⁻¹ * (z : ModGL τ K))⁻¹
        = (c : ModGL τ K)⁻¹ * (z : ModGL τ K) *
          (g * (d * ε (c : ModGL τ K) * (y : ModGL τ K) ^ S *
            (ε (c : ModGL τ K))⁻¹ * d⁻¹) * g⁻¹) *
            ((c : ModGL τ K)⁻¹ * (z : ModGL τ K))⁻¹ := by
      simp only [h]
      group
    have e2 : (c : ModGL τ K)⁻¹ * (z : ModGL τ K) *
          (g * (d * ε (c : ModGL τ K) * (y : ModGL τ K) ^ S *
            (ε (c : ModGL τ K))⁻¹ * d⁻¹) * g⁻¹) *
            ((c : ModGL τ K)⁻¹ * (z : ModGL τ K))⁻¹
        = (c : ModGL τ K)⁻¹ * (z : ModGL τ K) *
          (g * (d * ε (c : ModGL τ K) * d⁻¹ * (y : ModGL τ K) ^ S * d *
            (ε (c : ModGL τ K))⁻¹ * d⁻¹) * g⁻¹) *
            ((c : ModGL τ K)⁻¹ * (z : ModGL τ K))⁻¹ := by
      rw [hmid]
    have e3 : (c : ModGL τ K)⁻¹ * (z : ModGL τ K) *
          (g * (d * ε (c : ModGL τ K) * d⁻¹ * (y : ModGL τ K) ^ S * d *
            (ε (c : ModGL τ K))⁻¹ * d⁻¹) * g⁻¹) *
            ((c : ModGL τ K)⁻¹ * (z : ModGL τ K))⁻¹ =
        u * (y : ModGL τ K) ^ S * u⁻¹ := by
      simp only [u]
      group
    exact e1.trans (e2.trans e3)
  have hβeqC : ∀ y ∈ (P₀ : Subgroup C), βC y = uC * y ^ S * uC⁻¹ := by
    intro y hy
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    exact hβeq y hy
  have huN : uC ∈ Subgroup.normalizer ((P₀ : Subgroup C) : Set C) :=
    mem_normalizer_of_pow_map hP₀p hs31 fun y hy => by
      have h := hβP₀ y hy
      rw [hβeqC y hy] at h
      exact h
  let m : ℕ := Nat.card (WeylGroup τ)
  have hP₀N : uC ^ m ∈ Subgroup.centralizer ((P₀ : Subgroup C) : Set C) :=
    (hAut P₀).2 uC huN
  have huNpow : ∀ j : ℕ, uC ^ j ∈
      Subgroup.normalizer ((P₀ : Subgroup C) : Set C) :=
    fun j => Subgroup.pow_mem _ huN j
  have hβpow : ∀ (j : ℕ) (y : C), y ∈ (P₀ : Subgroup C) →
      βC^[j] y = uC ^ j * y ^ (S ^ j) * (uC ^ j)⁻¹ := by
    intro j
    induction j with
    | zero =>
      intro y _
      simp
    | succ j ih =>
      intro y hy
      rw [Function.iterate_succ_apply', ih y hy]
      have hzmem : uC ^ j * y ^ (S ^ j) * (uC ^ j)⁻¹ ∈ (P₀ : Subgroup C) :=
        (Subgroup.mem_set_normalizer_iff.1 (huNpow j) _).1 (Subgroup.pow_mem _ hy _)
      rw [hβeqC _ hzmem]
      have hconj : (uC ^ j * y ^ (S ^ j) * (uC ^ j)⁻¹) ^ S =
          uC ^ j * (y ^ (S ^ j)) ^ S * (uC ^ j)⁻¹ := by
        exact conj_pow (a := uC ^ j) (b := y ^ (S ^ j)) (i := S)
      calc uC * (uC ^ j * y ^ (S ^ j) * (uC ^ j)⁻¹) ^ S * uC⁻¹
          = uC * (uC ^ j * (y ^ (S ^ j)) ^ S * (uC ^ j)⁻¹) * uC⁻¹ := by
              rw [hconj]
        _ = (uC * uC ^ j) * (y ^ (S ^ j)) ^ S * ((uC ^ j)⁻¹ * uC⁻¹) := by group
        _ = uC ^ (j + 1) * (y ^ (S ^ j)) ^ S * (uC ^ (j + 1))⁻¹ := by
              rw [pow_succ' uC j]
              group
        _ = uC ^ (j + 1) * y ^ (S ^ j * S) * (uC ^ (j + 1))⁻¹ := by rw [← pow_mul]
        _ = uC ^ (j + 1) * y ^ (S ^ (j + 1)) * (uC ^ (j + 1))⁻¹ := by rw [← pow_succ]
  have hβm : ∀ y ∈ (P₀ : Subgroup C), βC^[m] y = y ^ (S ^ m) := by
    intro y hy
    rw [hβpow m y hy]
    have hpow : y ^ (S ^ m) ∈ (P₀ : Subgroup C) := Subgroup.pow_mem _ hy _
    have hcen := Subgroup.mem_centralizer_iff.1 hP₀N _ hpow
    rw [← hcen]
    group
  let η : C →* C := (MulAut.conj z).toMonoidHom.comp θC
  have hηapply : ∀ y : C, η y = z * θC y * z⁻¹ := by
    intro y
    change (MulAut.conj z) (θC y) = z * θC y * z⁻¹
    rw [MulAut.conj_apply]
  have hη_eq : η =
      (MulAut.conj c).toMonoidHom.comp (βC.comp (MulAut.conj c⁻¹).toMonoidHom) := by
    apply MonoidHom.ext
    intro y
    rw [hηapply]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hβC_apply]
    group
  have hη_eq_apply : ∀ y : C, η y = c * βC (c⁻¹ * y * c) * c⁻¹ := by
    intro y
    have h := congrArg (fun f : C →* C => f y) hη_eq
    simpa [MonoidHom.comp_apply, MulAut.conj_apply] using h
  have hηpow : ∀ (j : ℕ) (x : C),
      η^[j] x = c * (βC^[j] (c⁻¹ * x * c)) * c⁻¹ := by
    intro j
    induction j with
    | zero =>
      intro x
      change x = c * (c⁻¹ * x * c) * c⁻¹
      group
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', ih x, hη_eq_apply, Function.iterate_succ_apply']
      rw [show c⁻¹ * (c * (βC^[j] (c⁻¹ * x * c)) * c⁻¹) * c =
          βC^[j] (c⁻¹ * x * c) by group]
  have hηθ : ∀ e ∈ (E_C : Subgroup C), η e = θC e := by
    intro e he
    rw [hηapply]
    have hθe : θC e ∈ (E_C : Subgroup C) :=
      hθE_sub (Subgroup.mem_map_of_mem θC he)
    have hcomm := Subgroup.mem_centralizer_iff.1 hzN (θC e) hθe
    rw [← hcomm]
    group
  have hθiter : ∀ (j : ℕ) (x : C), x ∈ (E_C : Subgroup C) →
      θC^[j] x ∈ (E_C : Subgroup C) := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact hθE_sub (Subgroup.mem_map_of_mem θC (ih x hx))
  have hθη : ∀ (j : ℕ) (x : C), x ∈ (E_C : Subgroup C) →
      θC^[j] x = η^[j] x := by
    intro j
    induction j with
    | zero => intro x _; simp
    | succ j ih =>
      intro x hx
      calc θC^[j + 1] x = θC (θC^[j] x) := Function.iterate_succ_apply' _ _ _
        _ = η (θC^[j] x) := (hηθ _ (hθiter j x hx)).symm
        _ = η (η^[j] x) := by rw [ih x hx]
        _ = η^[j + 1] x := (Function.iterate_succ_apply' _ _ _).symm
  have hθm : ∀ x ∈ (E_C : Subgroup C), θC^[m] x = x ^ (S ^ m) := by
    intro x hx
    rw [hθη m x hx, hηpow m x]
    have hcxP : c⁻¹ * x * c ∈ (P₀ : Subgroup C) := hc₂ x (hE₁ hx)
    rw [hβm (c⁻¹ * x * c) hcxP]
    have hconj : (c⁻¹ * x * c) ^ (S ^ m) = c⁻¹ * x ^ (S ^ m) * c := by
      simpa using conj_pow (a := c⁻¹) (b := x) (i := S ^ m)
    rw [hconj]
    group
  have hsub_iter : ∀ (j : ℕ) (y : C),
      C.subtype (θC^[j] y) = θf^[j] (C.subtype y) := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
      intro y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [show C.subtype (θC (θC^[j] y)) = θf (C.subtype (θC^[j] y)) from rfl]
      rw [ih y]
  have hθfun : (fun y : ModGL τ K => (g * rootDiagUnit τ a) *
      Units.map (entrywiseHom σ.toRingHom) y * (g * rootDiagUnit τ a)⁻¹) = θf := by
    funext y
    rw [hθf_apply]
  refine ⟨S ^ m, ?_⟩
  intro x hx
  let xC : C := ⟨x, hEC hx⟩
  have hxE : xC ∈ (E_C : Subgroup C) := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  have h1 : C.subtype (θC^[m] xC) = θf^[m] x := by
    rw [hsub_iter m xC]
    rfl
  rw [hθm xC hxE] at h1
  have h2 : C.subtype (xC ^ (S ^ m)) = x ^ (S ^ m) := by
    change ((xC ^ (S ^ m) : C) : ModGL τ K) = x ^ (S ^ m)
    rw [Subgroup.coe_pow]
  rw [h2] at h1
  rw [hθfun]
  exact h1.symm


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
