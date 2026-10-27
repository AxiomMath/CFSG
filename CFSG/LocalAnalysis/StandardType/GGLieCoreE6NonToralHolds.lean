module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneDichotomy
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTable
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneConn
public import CFSG.LocalAnalysis.StandardType.E6FieldNoneMixedFinal
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.GroupTheory.PerfectCentralQuotient
public import CFSG.LocalAnalysis.StandardType.GGLieCoreE6NonToral
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneModFiveA2
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneModFiveD4
public import CFSG.Blueprint.Catalog
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.StandardType.LieCore

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.StandardType.ExcFramesHalf

variable {τ : Tag} {K : Type} [Field K]

theorem exists_rootChar_eq_zpow {p : ℕ} (hp : p.Prime) {b : Fin τ.rank → Kˣ}
    (hb : ∀ i, b i ^ p = 1) (hb1 : b ≠ 1) :
    ∃ (ζ : Kˣ) (χ : (Fin τ.rank → ℤ) →+ ℤ), IsPrimitiveRoot ζ p ∧
      ∀ v : Fin τ.rank → ℤ, rootChar b v = ζ ^ (χ v) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i, b i ≠ 1 := by
    by_contra h
    rw [not_exists] at h
    exact hb1 (funext fun i => not_not.mp (h i))
  have hζo : orderOf (b i₀) = p := orderOf_eq_prime (hb i₀) hi₀
  have hζ : IsPrimitiveRoot (b i₀) p := hζo ▸ IsPrimitiveRoot.orderOf (b i₀)
  have hroot : ∀ j, ∃ m : ZMod p, (b i₀) ^ m.val = b j := fun j => by
    obtain ⟨n, hn, hn'⟩ := hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p (b j)).2 (hb j))
    exact ⟨n, by rw [ZMod.val_natCast_of_lt hn]; exact hn'⟩
  choose x hx using hroot
  let χ : (Fin τ.rank → ℤ) →+ ℤ :=
    { toFun := fun v => ∑ j, ((x j).val : ℤ) * v j
      map_zero' := by simp
      map_add' := fun u v => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] }
  refine ⟨b i₀, χ, hζ, fun v => ?_⟩
  have hprod : ∀ (s : Finset (Fin τ.rank)) (e : Fin τ.rank → ℤ),
      ∏ j ∈ s, (b i₀) ^ e j = (b i₀) ^ (∑ j ∈ s, e j) := by
    intro s e
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, ih]
  change (∏ j, b j ^ v j) = (b i₀) ^ (∑ j, ((x j).val : ℤ) * v j)
  rw [show (∏ j, b j ^ v j) = ∏ j, ((b i₀) ^ (x j).val) ^ v j from
    Finset.prod_congr rfl fun j _ => by rw [hx j]]
  rw [show (∏ j, ((b i₀) ^ (x j).val) ^ v j) =
      ∏ j, (b i₀) ^ (((x j).val : ℤ) * v j) from
    Finset.prod_congr rfl fun j _ => by rw [← zpow_natCast, ← zpow_mul]]
  exact hprod Finset.univ _

theorem exists_rootChar_addHom {p : ℕ} (hp : p.Prime) {b : Fin τ.rank → Kˣ}
    (hb : ∀ i, b i ^ p = 1) (hb1 : b ≠ 1) :
    ∃ μ : (Fin τ.rank → ℤ) →+ ZMod p,
      (∀ v, rootChar b v = 1 ↔ μ v = 0) ∧ μ ≠ 0 ∧
      ∀ {u : WeylGroup τ} {k : ℕ},
        (∀ v, rootChar b (u • v) = rootChar b v ^ k) → ∀ v, μ (u • v) = k * μ v := by
  classical
  obtain ⟨ζ, χ, hζ, hχ⟩ := exists_rootChar_eq_zpow (τ := τ) (K := K) hp hb hb1
  let μ : (Fin τ.rank → ℤ) →+ ZMod p :=
    { toFun := fun v => (χ v : ZMod p)
      map_zero' := by simp
      map_add' := fun u v => by rw [map_add, Int.cast_add] }
  have hμ : ∀ v, μ v = (χ v : ZMod p) := fun _ => rfl
  have hker : ∀ v, rootChar b v = 1 ↔ μ v = 0 := by
    intro v
    rw [hχ v, hζ.zpow_eq_one_iff_dvd, hμ, ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨μ, hker, ?_, ?_⟩
  · intro h0
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ 1 := by
      by_contra h
      rw [not_exists] at h
      exact hb1 (funext fun i => not_not.mp (h i))
    have h1 : μ (Pi.single i 1) = 0 := by rw [h0]; rfl
    have h2 : rootChar b (Pi.single i 1) = 1 := (hker _).2 h1
    rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_single] at h2
    exact hi h2
  · intro u k h v
    have hζeq : ζ ^ (χ (u • v)) = ζ ^ ((k : ℤ) * χ v) := by
      calc ζ ^ (χ (u • v)) = rootChar b (u • v) := (hχ (u • v)).symm
        _ = rootChar b v ^ k := h v
        _ = (ζ ^ (χ v)) ^ k := by rw [hχ v]
        _ = ζ ^ ((k : ℤ) * χ v) := by
            rw [← zpow_natCast, ← zpow_mul]
            congr 1
            ring
    have hdvd : (p : ℤ) ∣ χ (u • v) - (k : ℤ) * χ v := by
      refine (hζ.zpow_eq_one_iff_dvd _).1 ?_
      rw [zpow_sub, hζeq, mul_inv_cancel]
    have hcast : ((χ (u • v) - (k : ℤ) * χ v : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd
    rw [hμ, hμ]
    push_cast at hcast ⊢
    linear_combination hcast

private theorem pow_ten_eq_self_of_pow_three {G : Type*} [Group G] {x : G} (h : x ^ 3 = 1) :
    x ^ 10 = x := by
  rw [show 10 = 3 * 3 + 1 by norm_num, pow_add, pow_mul, h, one_pow, one_mul, pow_one]

private theorem pow_six_eq_one_of_pow_three {G : Type*} [Group G] {x : G} (h : x ^ 3 = 1) :
    x ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by norm_num, pow_mul, h, one_pow]

private theorem pow_ten_eq_one_of_pow_five {G : Type*} [Group G] {x : G} (h : x ^ 5 = 1) :
    x ^ 10 = 1 := by
  rw [show 10 = 5 * 2 by norm_num, pow_mul, h, one_pow]

private theorem pow_six_eq_self_of_pow_five {G : Type*} [Group G] {x : G} (h : x ^ 5 = 1) :
    x ^ 6 = x := by
  rw [show 6 = 5 + 1 by norm_num, pow_add, h, one_mul, pow_one]

theorem ggLieE6NonToralNoA8_of_isAlgebraic_of_weyl
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    (hA2 : ∀ a : Fin Tag.E6.rank → Lˣ, (∀ i, a i ^ 3 = 1) →
      (rootCharKernel a).ncard = 18 →
      ∀ (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) {w : WeylGroup Tag.E6},
        w ∈ rootCharStabilizerSubgroup a → (∀ v, μ (w • v) = 2 * μ v) → μ = 0)
    (hD4 : ∀ a : Fin Tag.E6.rank → Lˣ, (∀ i, a i ^ 3 = 1) →
      (rootCharKernel a).ncard = 24 →
      ∀ (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) {w u : WeylGroup Tag.E6},
        w ∈ rootCharStabilizerSubgroup a → (∀ v, μ (w • v) = 2 * μ v) →
        u ∈ rootCharStabilizerSubgroup a → u ∉ kernelReflectionGroup a →
        (∀ v, μ (u • v) = μ v) → μ = 0)
    (hD4f : ∀ a : Fin Tag.E6.rank → Lˣ, (∀ i, a i ^ 3 = 1) →
      (rootCharKernel a).ncard = 24 →
      ∃ z : Fin Tag.E6.rank → Lˣ, (∀ α ∈ rootCharKernel a, rootChar z α = 1) ∧
        rootCharStabilizerSubgroup a ⊓ rootCharStabilizerSubgroup z ≤ kernelReflectionGroup a)
    (A : Subgroup (ModGL Tag.E6 L)) (hA : A ≤ adjointGroup Tag.E6 L) (hel : IsElemAbelian 3 A)
    (hcard : Nat.card A = 3 ^ 2) (hnt : ¬ IsToralSubgroup Tag.E6 L A)
    (J : Subgroup (ModGL Tag.E6 L)) (hJ : J ≤ adjointGroup Tag.E6 L)
    (hJA : J ≤ Subgroup.centralizer (A : Set (ModGL Tag.E6 L))) (hperf : ⁅J, J⁆ = J) :
    ¬ LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 1 := by
  classical
  intro hLie
  obtain ⟨eA8⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hLie
  have hJtop : ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ = ⊤ := by
    have hmap := Subgroup.map_commutator (⊤ : Subgroup ↥J) (⊤ : Subgroup ↥J)
      (Subgroup.subtype J)
    have htop : Subgroup.map (Subgroup.subtype J) (⊤ : Subgroup ↥J) = J := by
      have h := Subgroup.subgroupOf_map_subtype (⊤ : Subgroup (ModGL Tag.E6 L)) J
      rw [top_inf_eq] at h
      simpa using h
    rw [htop, hperf] at hmap
    exact Subgroup.map_injective (Subgroup.subtype_injective J) (by rw [hmap, htop])
  obtain ⟨v₀, g₀, hv₀5, hv₀Z, hconj₀⟩ :=
    CFSG.GroupTheory.exists_pow_five_eq_one_conj_sq_of_quotient_center_alternating_eight
      (J := ↥J) hJtop eA8
  have hv₀1 : v₀ ≠ 1 := by
    intro h
    exact hv₀Z (by rw [h]; exact Subgroup.one_mem _)
  obtain ⟨x₀, hx₀A, hx₀1⟩ : ∃ x ∈ A, x ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one A with hbot | h
    · exfalso
      rw [hbot, Subgroup.card_bot] at hcard
      norm_num at hcard
    · exact h
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hel.2
  have hnt' : ¬ ∃ C ∈ adjointGroup Tag.E6 L, ∀ x ∈ A,
      C * x * C⁻¹ ∈ torusGroup Tag.E6 L := by
    rintro ⟨C, hC, hCD⟩
    exact hnt ⟨C⁻¹, inv_mem hC, fun x hx => by
      have h := hCD x hx
      simpa only [inv_inv] using h⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨C, hC, a, n, ha3, hCx, hCA, hn, hn3, hna, hstab, hnotker⟩ :=
    CFSG.StandardType.NTPlane.plane_nontoral_normal_form (p := 3) (ℓ := 2) (τ := Tag.E6)
      CFSG.HardMathSupport.Timmesfeld.CrossChar.monomialToralAt_E6_three
      (show (2 : ℕ) ≠ 3 by norm_num) halg hA hcomm hexp hcard hnt' hx₀A hx₀1
  have hda1 : rootDiagUnit Tag.E6 a ≠ 1 := by
    intro h
    apply hx₀1
    have h1 : C * x₀ * C⁻¹ = 1 := by rw [hCx, h]
    have h2 := congrArg (fun z => C⁻¹ * z * C) h1
    simpa [mul_assoc] using h2
  have ha1 : a ≠ 1 := fun h => hda1 (by rw [h, rootDiagUnit_one])
  set ρn : WeylGroup Tag.E6 := weylQuotientHom Tag.E6 L ⟨n, hn⟩ with hρdef
  have hstab' : ρn ∈ rootCharStabilizerSubgroup a := by rw [hρdef]; exact hstab
  have hnotker' : ρn ∉ kernelReflectionGroup a := by rw [hρdef]; exact hnotker
  have htable := CFSG.StandardType.NTPlane.e6_three_class_table a ha3 ha1
  obtain ⟨hcardSigma, hidx⟩ : ((rootCharKernel a).ncard = 18 ∨
      (rootCharKernel a).ncard = 24) ∧
      ((kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)).index = 3 := by
    rcases htable with hker | h
    · rw [← hker] at hstab'
      exact absurd hstab' hnotker'
    · exact h

  set A' : Subgroup (ModGL Tag.E6 L) := A.map (MulAut.conj C).toMonoidHom with hA'def
  set J₁ : Subgroup (ModGL Tag.E6 L) := J.map (MulAut.conj C).toMonoidHom with hJ₁def
  have hJ₁G : J₁ ≤ adjointGroup Tag.E6 L := by
    rintro _ ⟨j, hj, rfl⟩
    exact mul_mem (mul_mem hC (hJ hj)) (inv_mem hC)
  have hJ₁perf : ⁅J₁, J₁⁆ = J₁ := by
    rw [hJ₁def, ← Subgroup.map_commutator J J (MulAut.conj C).toMonoidHom, hperf]
  have hJ₁cent : J₁ ≤ Subgroup.centralizer (A' : Set (ModGL Tag.E6 L)) := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have h := Subgroup.mem_centralizer_iff.mp (hJA hj) y hy
    change (C * y * C⁻¹) * (C * j * C⁻¹) = (C * j * C⁻¹) * (C * y * C⁻¹)
    calc (C * y * C⁻¹) * (C * j * C⁻¹) = C * (y * j) * C⁻¹ := by group
      _ = C * (j * y) * C⁻¹ := by rw [h]
      _ = (C * j * C⁻¹) * (C * y * C⁻¹) := by group
  have hdaA' : rootDiagUnit Tag.E6 a ∈ A' := by
    rw [hCA]
    exact (le_sup_left : Subgroup.zpowers (rootDiagUnit Tag.E6 a) ≤
      Subgroup.zpowers (rootDiagUnit Tag.E6 a) ⊔ Subgroup.zpowers n)
      (Subgroup.mem_zpowers _)
  have hnA' : n ∈ A' := by
    rw [hCA]
    exact (le_sup_right : Subgroup.zpowers n ≤
      Subgroup.zpowers (rootDiagUnit Tag.E6 a) ⊔ Subgroup.zpowers n)
      (Subgroup.mem_zpowers _)
  have hJ₁_da : ∀ j ∈ J₁, j * rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a * j :=
    fun j hj => (Subgroup.mem_centralizer_iff.mp (hJ₁cent hj) _ hdaA').symm
  have hJ₁_n : ∀ j ∈ J₁, j * n = n * j := fun j hj =>
    (Subgroup.mem_centralizer_iff.mp (hJ₁cent hj) _ hnA').symm
  have hJ₁toral : J₁ ≤ toralCentralizer Tag.E6 L a := by
    intro j hj
    rw [mem_toralCentralizer]
    refine ⟨hJ₁G hj, ?_⟩
    rw [← hJ₁_da j hj]
    group
  have hJ₁span : J₁ ≤ rootSpan Tag.E6 L (rootCharKernel a) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_rootSpan_kernel
      Nat.prime_three a ha3 hJ₁toral hJ₁perf
  have hJ₁C : J₁ ≤ toralRootGroup Tag.E6 L a := le_trans hJ₁span le_sup_right
  set v : ModGL Tag.E6 L := C * (v₀ : ModGL Tag.E6 L) * C⁻¹ with hvdef
  set g : ModGL Tag.E6 L := C * (g₀ : ModGL Tag.E6 L) * C⁻¹ with hgdef
  have hvJ₁ : v ∈ J₁ := by
    refine Subgroup.mem_map.mpr ⟨(v₀ : ModGL Tag.E6 L), v₀.2, ?_⟩
    simp [hvdef, MulAut.conj_apply]
  have hgJ₁ : g ∈ J₁ := by
    refine Subgroup.mem_map.mpr ⟨(g₀ : ModGL Tag.E6 L), g₀.2, ?_⟩
    simp [hgdef, MulAut.conj_apply]
  have hv₀5' : (v₀ : ModGL Tag.E6 L) ^ 5 = 1 := by
    simpa using congrArg Subtype.val hv₀5
  have hv5 : v ^ 5 = 1 := by
    rw [hvdef]
    have hc : (C * (v₀ : ModGL Tag.E6 L) * C⁻¹) ^ 5 =
        C * (v₀ : ModGL Tag.E6 L) ^ 5 * C⁻¹ := conj_pow
    rw [hc, hv₀5', mul_one, mul_inv_cancel]
  have hv1 : v ≠ 1 := by
    intro h
    apply hv₀1
    apply Subtype.ext
    have h1 : C * (v₀ : ModGL Tag.E6 L) * C⁻¹ = 1 := by simpa [hvdef] using h
    have h2 := congrArg (fun z => C⁻¹ * z * C) h1
    simpa [mul_assoc] using h2
  have hconj_v : g * v * g⁻¹ = v ^ 2 := by
    have h := congrArg Subtype.val hconj₀
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at h
    rw [hgdef, hvdef]
    calc (C * (g₀ : ModGL Tag.E6 L) * C⁻¹) * (C * (v₀ : ModGL Tag.E6 L) * C⁻¹) *
          (C * (g₀ : ModGL Tag.E6 L) * C⁻¹)⁻¹
        = C * ((g₀ : ModGL Tag.E6 L) * (v₀ : ModGL Tag.E6 L) * (g₀ : ModGL Tag.E6 L)⁻¹) *
            C⁻¹ := by group
      _ = C * (v₀ : ModGL Tag.E6 L) ^ 2 * C⁻¹ := by rw [h]
      _ = (C * (v₀ : ModGL Tag.E6 L) * C⁻¹) ^ 2 := by rw [conj_pow]
  have hv_da : v * rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a * v := hJ₁_da v hvJ₁
  have hv_n : v * n = n * v := hJ₁_n v hvJ₁
  have hg_da : g * rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a * g := hJ₁_da g hgJ₁

  set y : ModGL Tag.E6 L := rootDiagUnit Tag.E6 a * v with hydef
  have hyG : y ∈ adjointGroup Tag.E6 L := by
    rw [hydef]
    exact (CFSG.RankThree.Classical2.torusGroup_le_adjointGroup_of_field (τ := Tag.E6)
      (K := L)) (rootDiagUnit_mem_torusGroup a) |> fun h => mul_mem h (hJ₁G hvJ₁)
  have hda3 : (rootDiagUnit Tag.E6 a) ^ 3 = 1 := by
    rw [← CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_pow',
      show a ^ 3 = 1 from funext fun i => ha3 i, rootDiagUnit_one]
  have hda15 : (rootDiagUnit Tag.E6 a) ^ 15 = 1 := by
    rw [show 15 = 3 * 5 by norm_num, pow_mul, hda3, one_pow]
  have hcomm_dv : Commute (rootDiagUnit Tag.E6 a) v := hv_da.symm
  have hv15 : v ^ 15 = 1 := by
    rw [show 15 = 5 * 3 by norm_num, pow_mul, hv5, one_pow]
  have hy15 : y ^ 15 = 1 := by
    rw [hydef, Commute.mul_pow hcomm_dv, hda15, hv15, mul_one]
  obtain ⟨h, hhG, hhy⟩ :=
    CFSG.StandardType.exists_conj_torusGroup_of_odd_order_unconditional
      (L := L) halg (by decide : Odd 15) hyG hy15
  set D : ModGL Tag.E6 L := h⁻¹ * rootDiagUnit Tag.E6 a * h with hDdef
  set V : ModGL Tag.E6 L := h⁻¹ * v * h with hVdef
  have hY : h⁻¹ * y * h = D * V := by rw [hydef, hDdef, hVdef]; group
  have hDV : D * V = V * D := by
    rw [hDdef, hVdef]
    calc h⁻¹ * rootDiagUnit Tag.E6 a * h * (h⁻¹ * v * h) =
          h⁻¹ * (rootDiagUnit Tag.E6 a * v) * h := by group
      _ = h⁻¹ * (v * rootDiagUnit Tag.E6 a) * h := by rw [hv_da]
      _ = h⁻¹ * v * h * (h⁻¹ * rootDiagUnit Tag.E6 a * h) := by group
  have hD3 : D ^ 3 = 1 := by
    rw [hDdef]
    have h' : h⁻¹ * rootDiagUnit Tag.E6 a * h =
        h⁻¹ * rootDiagUnit Tag.E6 a * (h⁻¹)⁻¹ := by rw [inv_inv]
    rw [h', conj_pow, hda3, mul_one, inv_inv, inv_mul_cancel]
  have hV5 : V ^ 5 = 1 := by
    rw [hVdef]
    have h' : h⁻¹ * v * h = h⁻¹ * v * (h⁻¹)⁻¹ := by rw [inv_inv]
    rw [h', conj_pow, hv5, mul_one, inv_inv, inv_mul_cancel]
  have hDmem : D ∈ torusGroup Tag.E6 L := by
    have hD10 : D ^ 10 = D := pow_ten_eq_self_of_pow_three hD3
    have hV10 : V ^ 10 = 1 := pow_ten_eq_one_of_pow_five hV5
    have hDeq : D = (h⁻¹ * y * h) ^ 10 := by
      rw [hY, Commute.mul_pow hDV, hD10, hV10, mul_one]
    rw [hDeq]
    exact Subgroup.pow_mem _ hhy 10
  have hVmem : V ∈ torusGroup Tag.E6 L := by
    have hD6 : D ^ 6 = 1 := pow_six_eq_one_of_pow_three hD3
    have hV6 : V ^ 6 = V := pow_six_eq_self_of_pow_five hV5
    have hVeq : V = (h⁻¹ * y * h) ^ 6 := by
      rw [hY, Commute.mul_pow hDV, hD6, hV6, one_mul]
    rw [hVeq]
    exact Subgroup.pow_mem _ hhy 6
  obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hDmem
  obtain ⟨b', hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hVmem
  have hconj_h : h * rootDiagUnit Tag.E6 a' * h⁻¹ = rootDiagUnit Tag.E6 a := by
    rw [← ha', hDdef]
    group
  obtain ⟨w₁, hw₁⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.exists_weyl_of_conj_family
      Tag.E6 L (fun _ : Fin 1 => a) (fun _ : Fin 1 => a') hhG (fun i => by
        fin_cases i
        exact hconj_h)
  have hw₁0 : rootDiagUnit Tag.E6 a =
      canonicalRep (coxeterSystem Tag.E6) L w₁ * rootDiagUnit Tag.E6 a' *
        (canonicalRep (coxeterSystem Tag.E6) L w₁)⁻¹ := hw₁ 0
  set n₁ : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L w₁ with hn₁def
  set c₀ : ModGL Tag.E6 L := h * n₁⁻¹ with hc₀def
  have hc₀G : c₀ ∈ adjointGroup Tag.E6 L :=
    mul_mem hhG (inv_mem (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) L w₁))
  have hc₀toral : c₀ ∈ toralCentralizer Tag.E6 L a := by
    rw [mem_toralCentralizer]
    refine ⟨hc₀G, ?_⟩
    have h1 : c₀⁻¹ * rootDiagUnit Tag.E6 a * c₀ = rootDiagUnit Tag.E6 a := by
      rw [hc₀def]
      calc (h * n₁⁻¹)⁻¹ * rootDiagUnit Tag.E6 a * (h * n₁⁻¹)
          = n₁ * (h⁻¹ * rootDiagUnit Tag.E6 a * h) * n₁⁻¹ := by group
        _ = n₁ * (n₁⁻¹ * rootDiagUnit Tag.E6 a * n₁) * n₁⁻¹ := by
            rw [← hDdef, ha', ← hw₁0]
            group
        _ = rootDiagUnit Tag.E6 a := by group
    have hcomm : rootDiagUnit Tag.E6 a * c₀ = c₀ * rootDiagUnit Tag.E6 a := by
      calc rootDiagUnit Tag.E6 a * c₀ = c₀ * (c₀⁻¹ * rootDiagUnit Tag.E6 a * c₀) := by group
        _ = c₀ * rootDiagUnit Tag.E6 a := by rw [h1]
    rw [hcomm, mul_inv_cancel_right]
  have hc₀v : c₀⁻¹ * v * c₀ =
      rootDiagUnit Tag.E6 (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w₁ b') := by
    calc c₀⁻¹ * v * c₀ = n₁ * (h⁻¹ * v * h) * n₁⁻¹ := by rw [hc₀def]; group
      _ = n₁ * rootDiagUnit Tag.E6 b' * n₁⁻¹ := by rw [← hb']
      _ = rootDiagUnit Tag.E6 (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w₁ b') :=
          CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit w₁ b'

  obtain ⟨i, m, hmC, hc₀eq⟩ :=
    CFSG.StandardType.NTPlane.toralCentralizer_cosets_of_index_three Tag.E6 L a hidx hstab'
      hnotker' c₀ hc₀toral
  set r : ModGL Tag.E6 L :=
    canonicalRep (coxeterSystem Tag.E6) L (ρn ^ (i : ℕ)) with hrdef
  set b : Fin Tag.E6.rank → Lˣ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct (ρn ^ (i : ℕ))
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w₁ b') with hbdef
  have hcv : m⁻¹ * v * m = rootDiagUnit Tag.E6 b := by
    have h1 : (m * r)⁻¹ * v * (m * r) = rootDiagUnit Tag.E6
        (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w₁ b') := by
      rw [← hc₀eq]
      exact hc₀v
    have h2 : m⁻¹ * v * m =
        r * rootDiagUnit Tag.E6 (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w₁ b') *
          r⁻¹ := by
      calc m⁻¹ * v * m = r * ((m * r)⁻¹ * v * (m * r)) * r⁻¹ := by group
        _ = r * rootDiagUnit Tag.E6
              (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w₁ b') * r⁻¹ := by rw [h1]
    rw [h2, hrdef]
    rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit]
  have hb5 : ∀ j, b j ^ 5 = 1 := by
    have hdb5 : (rootDiagUnit Tag.E6 b) ^ 5 = 1 := by
      rw [← hcv]
      have h := conj_pow (i := 5) (a := m⁻¹) (b := v)
      simpa only [inv_inv, hv5, mul_one, inv_mul_cancel] using h
    have hdb : rootDiagUnit Tag.E6 (b ^ 5) = 1 := by
      rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_pow']
      exact hdb5
    have hdb' : rootDiagUnit Tag.E6 (b ^ 5) = rootDiagUnit Tag.E6 1 := by
      rw [hdb, rootDiagUnit_one]
    intro j
    have := congrFun (rootDiagUnit_injective (τ := Tag.E6) (K := L) hdb') j
    simpa using this
  have hb1 : b ≠ 1 := by
    intro hb
    apply hv1
    have h1 : m⁻¹ * v * m = 1 := by rw [hcv, hb, rootDiagUnit_one]
    have h2 := congrArg (fun z => m * z * m⁻¹) h1
    simpa [mul_assoc] using h2

  obtain ⟨μ, hμker, hμne, hμrel⟩ :=
    exists_rootChar_addHom (τ := Tag.E6) (K := L) Nat.prime_five hb5 hb1
  have hm_toral : m ∈ toralCentralizer Tag.E6 L a := toralRootGroup_le a hmC
  have hmG : m ∈ adjointGroup Tag.E6 L := (mem_toralCentralizer.mp hm_toral).1
  have hm_da : rootDiagUnit Tag.E6 a * m = m * rootDiagUnit Tag.E6 a := by
    have h := (mem_toralCentralizer.mp hm_toral).2
    calc rootDiagUnit Tag.E6 a * m =
          (rootDiagUnit Tag.E6 a * m * (rootDiagUnit Tag.E6 a)⁻¹) *
            rootDiagUnit Tag.E6 a := by group
      _ = m * rootDiagUnit Tag.E6 a := by rw [h]
  set g' : ModGL Tag.E6 L := m⁻¹ * g * m with hg'def
  have hg'G : g' ∈ adjointGroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem hmG) (hJ₁G hgJ₁)) hmG
  have hm_da_inv : m⁻¹ * rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a * m⁻¹ := by
    calc m⁻¹ * rootDiagUnit Tag.E6 a =
          m⁻¹ * rootDiagUnit Tag.E6 a * m * m⁻¹ := by group
      _ = m⁻¹ * (rootDiagUnit Tag.E6 a * m) * m⁻¹ := by group
      _ = m⁻¹ * (m * rootDiagUnit Tag.E6 a) * m⁻¹ := by rw [hm_da]
      _ = rootDiagUnit Tag.E6 a * m⁻¹ := by group
  have hg'_da : g' * rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a * g' := by
    rw [hg'def]
    calc m⁻¹ * g * m * rootDiagUnit Tag.E6 a
        = m⁻¹ * g * (m * rootDiagUnit Tag.E6 a) := by group
      _ = m⁻¹ * g * (rootDiagUnit Tag.E6 a * m) := by rw [hm_da]
      _ = m⁻¹ * (g * rootDiagUnit Tag.E6 a) * m := by group
      _ = m⁻¹ * (rootDiagUnit Tag.E6 a * g) * m := by rw [hg_da]
      _ = (m⁻¹ * rootDiagUnit Tag.E6 a) * g * m := by group
      _ = (rootDiagUnit Tag.E6 a * m⁻¹) * g * m := by rw [hm_da_inv]
      _ = rootDiagUnit Tag.E6 a * (m⁻¹ * g * m) := by group
  have hg'_b : g' * rootDiagUnit Tag.E6 b * g'⁻¹ = rootDiagUnit Tag.E6 (b ^ 2) := by
    rw [hg'def]
    calc (m⁻¹ * g * m) * rootDiagUnit Tag.E6 b * (m⁻¹ * g * m)⁻¹
        = (m⁻¹ * g * m) * (m⁻¹ * v * m) * (m⁻¹ * g * m)⁻¹ := by rw [← hcv]
      _ = m⁻¹ * (g * v * g⁻¹) * m := by group
      _ = m⁻¹ * v ^ 2 * m := by rw [hconj_v]
      _ = (m⁻¹ * v * m) ^ 2 := by
        simpa only [inv_inv] using (conj_pow (i := 2) (a := m⁻¹) (b := v)).symm
      _ = (rootDiagUnit Tag.E6 b) ^ 2 := by rw [hcv]
      _ = rootDiagUnit Tag.E6 (b ^ 2) := by
          rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_pow']
  let Afam : Fin 2 → Fin Tag.E6.rank → Lˣ := ![a, b ^ 2]
  let Bfam : Fin 2 → Fin Tag.E6.rank → Lˣ := ![a, b]
  obtain ⟨w, hw⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.exists_weyl_of_conj_family
      Tag.E6 L Afam Bfam hg'G (fun i => by
        fin_cases i
        · change g' * rootDiagUnit Tag.E6 a * g'⁻¹ = rootDiagUnit Tag.E6 a
          rw [hg'_da]
          group
        · change g' * rootDiagUnit Tag.E6 b * g'⁻¹ = rootDiagUnit Tag.E6 (b ^ 2)
          exact hg'_b)
  have hwa : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w a = a := by
    have h : rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6
        (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w a) := by
      rw [← CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit
        (K := L) w a]
      simpa [Afam, Bfam] using hw 0
    exact (rootDiagUnit_injective (τ := Tag.E6) (K := L) h).symm
  have hwb : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w b = b ^ 2 := by
    have h : rootDiagUnit Tag.E6 (b ^ 2) = rootDiagUnit Tag.E6
        (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w b) := by
      rw [← CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit
        (K := L) w b]
      simpa [Afam, Bfam] using hw 1
    exact (rootDiagUnit_injective (τ := Tag.E6) (K := L) h).symm
  have hw'a : w⁻¹ ∈ rootCharStabilizerSubgroup a := by
    rw [mem_rootCharStabilizerSubgroup]
    intro v
    have h := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_weylAct w a v
    rw [hwa] at h
    exact h.symm
  have hμw : ∀ v, μ (w⁻¹ • v) = 2 * μ v := by
    have hpow : ∀ v, rootChar b (w⁻¹ • v) = rootChar b v ^ 2 := by
      intro v
      have h := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_weylAct w b v
      rw [hwb] at h
      rw [CFSG.HardMathSupport.Timmesfeld.Torality.rootChar_pow'] at h
      exact h.symm
    exact hμrel hpow

  rcases hcardSigma with h18 | h24
  · exact hμne (hA2 a ha3 h18 μ hw'a hμw)
  ·
    have hnC : n ∉ toralRootGroup Tag.E6 L a := by
      intro hnC
      obtain ⟨z, hzroot, hzint⟩ := hD4f a ha3 h24
      have hdz_cent : toralRootGroup Tag.E6 L a ≤
          Subgroup.centralizer {rootDiagUnit Tag.E6 z} := by
        refine sup_le ?_ ?_
        · intro t ht
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (rootDiagUnit_mul_comm_of_mem_torusGroup z ht).symm
        · refine CFSG.LieType.Chevalley.rootSpan_le_centralizer (a := z) ?_
          intro α hα
          exact ⟨hα.1, hzroot α hα⟩
      have hn_comm_z : n * rootDiagUnit Tag.E6 z = rootDiagUnit Tag.E6 z * n :=
        (Subgroup.mem_centralizer_iff.mp (hdz_cent hnC) _ (Set.mem_singleton _)).symm
      have hweylz : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct ρn z = z := by
        apply rootDiagUnit_injective (τ := Tag.E6) (K := L)
        have h : rootDiagUnit Tag.E6
            (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct ρn z) =
            rootDiagUnit Tag.E6 z := by
          rw [← CFSG.HardMathSupport.Timmesfeld.Tables.T1b.monomial_conj_rootDiagUnit
            (K := L) ⟨n, hn⟩ z]
          calc n * rootDiagUnit Tag.E6 z * n⁻¹ =
                rootDiagUnit Tag.E6 z * n * n⁻¹ := by rw [hn_comm_z]
            _ = rootDiagUnit Tag.E6 z := by group
        exact h
      have hρz : ρn ∈ rootCharStabilizerSubgroup z := by
        rw [mem_rootCharStabilizerSubgroup]
        intro v
        have h := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_weylAct ρn z (ρn • v)
        rw [hweylz] at h
        simpa using h
      exact hnotker' (hzint ⟨hstab', hρz⟩)
    set n' : ModGL Tag.E6 L := m⁻¹ * n * m with hn'def
    have hnG : n ∈ adjointGroup Tag.E6 L := by
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hnA'
      exact mul_mem (mul_mem hC (hA hy)) (inv_mem hC)
    have hn'_da : n' * rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a * n' := by
      rw [hn'def]
      calc m⁻¹ * n * m * rootDiagUnit Tag.E6 a
          = m⁻¹ * n * (m * rootDiagUnit Tag.E6 a) := by group
        _ = m⁻¹ * n * (rootDiagUnit Tag.E6 a * m) := by rw [hm_da]
        _ = m⁻¹ * (n * rootDiagUnit Tag.E6 a) * m := by group
        _ = m⁻¹ * (rootDiagUnit Tag.E6 a * n) * m := by rw [hna]
        _ = (m⁻¹ * rootDiagUnit Tag.E6 a) * n * m := by group
        _ = (rootDiagUnit Tag.E6 a * m⁻¹) * n * m := by rw [hm_da_inv]
        _ = rootDiagUnit Tag.E6 a * (m⁻¹ * n * m) := by group
    have hn'_db : n' * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * n' := by
      rw [← hcv, hn'def]
      calc (m⁻¹ * n * m) * (m⁻¹ * v * m) = m⁻¹ * (n * v) * m := by group
        _ = m⁻¹ * (v * n) * m := by rw [hv_n]
        _ = (m⁻¹ * v * m) * (m⁻¹ * n * m) := by group
    have hn'_dab : n' * rootDiagUnit Tag.E6 (a * b) =
        rootDiagUnit Tag.E6 (a * b) * n' := by
      rw [rootDiagUnit_mul]
      calc n' * (rootDiagUnit Tag.E6 a * rootDiagUnit Tag.E6 b)
          = (n' * rootDiagUnit Tag.E6 a) * rootDiagUnit Tag.E6 b := by group
        _ = (rootDiagUnit Tag.E6 a * n') * rootDiagUnit Tag.E6 b := by rw [hn'_da]
        _ = rootDiagUnit Tag.E6 a * (n' * rootDiagUnit Tag.E6 b) := by group
        _ = rootDiagUnit Tag.E6 a * (rootDiagUnit Tag.E6 b * n') := by rw [hn'_db]
        _ = (rootDiagUnit Tag.E6 a * rootDiagUnit Tag.E6 b) * n' := by group
    have hn'C : n' ∈ toralCentralizer Tag.E6 L (a * b) := by
      rw [mem_toralCentralizer]
      refine ⟨mul_mem (mul_mem (inv_mem hmG) hnG) hmG, ?_⟩
      rw [conj_eq_iff_mem_centralizer]
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hn'_dab.symm
    obtain ⟨w', hw', h₁, hh₁, u₁, hu₁, v₁, hv₁, hn'fac⟩ :=
      (CFSG.LieType.Chevalley.Chevalley_toral_centralizer_Bruhat_factors Tag.E6 L (a * b)).1
        n' hn'C
    have hab10 : (a * b) ^ 10 = a := by
      rw [mul_pow, show a ^ 10 = a from funext fun j =>
        pow_ten_eq_self_of_pow_three (ha3 j),
        show b ^ 10 = 1 from funext fun j => pow_ten_eq_one_of_pow_five (hb5 j), mul_one]
    have hab6 : (a * b) ^ 6 = b := by
      rw [mul_pow, show a ^ 6 = 1 from funext fun j => pow_six_eq_one_of_pow_three (ha3 j),
        show b ^ 6 = b from funext fun j => pow_six_eq_self_of_pow_five (hb5 j), one_mul]
    have hker_sub : rootCharKernel (a * b) ⊆ rootCharKernel a := by
      intro α hα
      refine ⟨hα.1, ?_⟩
      have h10 := congrArg (fun x : Lˣ => x ^ 10) hα.2
      simp only [one_pow] at h10
      rw [← CFSG.HardMathSupport.Timmesfeld.Torality.rootChar_pow' (a * b) 10 α,
        hab10] at h10
      exact h10
    have hw'a' : w' ∈ rootCharStabilizerSubgroup a := by
      rw [mem_rootCharStabilizerSubgroup]
      intro v
      have h10 := congrArg (fun x : Lˣ => x ^ 10) (hw' v)
      rw [← CFSG.HardMathSupport.Timmesfeld.Torality.rootChar_pow' (a * b) 10 (w' • v),
        ← CFSG.HardMathSupport.Timmesfeld.Torality.rootChar_pow' (a * b) 10 v,
        hab10] at h10
      exact h10
    have hwSix : ∀ v, rootChar b (w' • v) = rootChar b v := by
      intro v
      have h6 := congrArg (fun x : Lˣ => x ^ 6) (hw' v)
      rw [← CFSG.HardMathSupport.Timmesfeld.Torality.rootChar_pow' (a * b) 6 (w' • v),
        ← CFSG.HardMathSupport.Timmesfeld.Torality.rootChar_pow' (a * b) 6 v,
        hab6] at h6
      exact h6
    have hμ' : ∀ v, μ (w' • v) = μ v := by
      simpa using hμrel (u := w') (k := 1) (by simpa using hwSix)
    have hw'ker : w' ∉ kernelReflectionGroup a := by
      intro hker
      have hmem : (⟨w', hw'a'⟩ : rootCharStabilizerSubgroup a) ∈
          (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a) := by
        rw [Subgroup.mem_subgroupOf]
        exact hker
      have h1 := CFSG.LieType.Chevalley.kernelReflectionGroup_le_ker (K := L) a hmem
      rw [MonoidHom.mem_ker, CFSG.LieType.Chevalley.weylToralQuotientHom_apply] at h1
      rw [QuotientGroup.eq_one_iff] at h1
      have hrep : canonicalRep (coxeterSystem Tag.E6) L w' ∈ toralRootGroup Tag.E6 L a :=
        Subgroup.mem_subgroupOf.mp h1
      have hu₁C : u₁ ∈ toralRootGroup Tag.E6 L a :=
        (le_sup_right : CFSG.Blueprint.Chevalley.rootSpan Tag.E6 L (rootCharKernel a) ≤
          toralRootGroup Tag.E6 L a)
          (CFSG.LieType.Chevalley.rootSpan_mono (S := rootCharKernel (a * b) ∩
            {α | IsRoot Tag.E6 α ∧ 0 < height α}) (T := rootCharKernel a) (by
              intro α hα
              exact hker_sub hα.1) hu₁)
      have hv₁C : v₁ ∈ toralRootGroup Tag.E6 L a :=
        (le_sup_right : CFSG.Blueprint.Chevalley.rootSpan Tag.E6 L (rootCharKernel a) ≤
          toralRootGroup Tag.E6 L a)
          (CFSG.LieType.Chevalley.rootSpan_mono (S := rootCharKernel (a * b) ∩
            inversionSet w') (T := rootCharKernel a) (by
              intro α hα
              exact hker_sub hα.1) hv₁)
      have hn'C' : n' ∈ toralRootGroup Tag.E6 L a := by
        rw [hn'fac]
        exact mul_mem (mul_mem (mul_mem
          ((le_sup_left : CFSG.LieType.Chevalley.torusGroup Tag.E6 L ≤
            toralRootGroup Tag.E6 L a) hh₁) hu₁C) hrep) hv₁C
      have hnC' : n ∈ toralRootGroup Tag.E6 L a := by
        have hn_eq : n = m * n' * m⁻¹ := by rw [hn'def]; group
        rw [hn_eq]
        exact mul_mem (mul_mem hmC hn'C') (inv_mem hmC)
      exact hnC hnC'
    exact hμne (hD4 a ha3 h24 μ hw'a hμw hw'a' hw'ker hμ')

theorem ggLieE6NonToralNoA8_holds :
    GGLieE6NonToralNoA8 := by
  intro L _ _ _ halg A hA hel hcard hnt J hJ hJA hperf
  exact ggLieE6NonToralNoA8_of_isAlgebraic_of_weyl halg
    (fun a ha3 h18 μ _ hw hμ =>
      CFSG.StandardType.NTPlane.modFive_eq_zero_of_ncard_rootCharKernel_eq_eighteen a ha3 h18 μ
        hw hμ)
    (fun a ha3 h24 μ _ _ hw hμw hu hu' hμu =>
      CFSG.StandardType.NTPlane.modFive_eq_zero_of_ncard_rootCharKernel_eq_twentyFour a ha3 h24 μ
        hw hμw hu hu' hμu)
    (fun a ha3 h24 =>
      CFSG.StandardType.NTPlane.exists_central_of_ncard_rootCharKernel_eq_twentyFour a ha3 h24)
    A hA hel hcard hnt J hJ hJA hperf

end CFSG.StandardType.LieCore

end
