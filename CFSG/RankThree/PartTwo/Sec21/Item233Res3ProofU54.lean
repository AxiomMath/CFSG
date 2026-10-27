module

public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofInner
public import CFSG.RankThree.PartTwo.KFacts.KS222U5
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
import CFSG.RankThree.PartTwo.Sec21.Item222ProofStar
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Matrix
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.RankThree.PartOne (suQ isCentralPQuot_suQ)
open CFSG.RankThree.PartOne.KFU (dvec5 diagU diagU_mul permGL permGL_mem_SU permGL_conj_diagU
  torus6 mem_torus6_iff torus6_pow_eq_one b6 coe_b6 diagU_dvec5_mem_SU suBlock6 suBlock6_injective
  perfectResidual_centralizer_b6 card_center_range_suBlock6 exists_conj_into_d8Tor_su d8Comb_five
  IsCentralPQuot exists_toral_quot map_inSubgroup_perfectResidual card_center_mulEquiv)

variable {G : Type} [Group G]

abbrev K16 : Type := GaloisField 2 (2 * 2)

theorem card_K16 : Nat.card K16 = (2 ^ 2) ^ 2 := U4Lines.card_galoisField_two_mul 2 (by norm_num)

noncomputable abbrev σ16 : K16 ≃+* K16 := unitaryInvolution K16 2 2

abbrev SU54 : Type := ↥(SU σ16 5)

abbrev U54 : Type := StatedProj (StatedSU 5 (2 ^ 2) K16)

noncomputable abbrev qU : SU54 →* U54 := suQ 5 card_K16

theorem isCentralPQuot_qU : IsCentralPQuot 3 qU :=
  isCentralPQuot_suQ Nat.prime_three (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    card_K16

noncomputable def projSUEquivU54 : projSU 5 2 2 ≃* U54 :=
  (MulEquiv.subgroupCongr (Census.projImage_statedSU 5 2 2).symm).trans
    (Census.statedProjEquivProjImage _).symm

theorem card_mu3 : Nat.card (rootsOfUnity 3 K16) = 3 :=
  U4Lines.card_rootsOfUnity_three even_two card_K16

theorem σ16_mu3 (u : rootsOfUnity 3 K16) : σ16 ((u : K16ˣ) : K16) = (u : K16ˣ) :=
  U4Lines.unitaryInvolution_rootsOfUnity even_two u

@[expose] noncomputable def tt (a b : rootsOfUnity 3 K16) : SU54 :=
  ⟨diagU (dvec5 (a : K16ˣ) (b : K16ˣ)), diagU_dvec5_mem_SU σ16 (σ16_mu3 a) (σ16_mu3 b)⟩

theorem coe_tt (a b : rootsOfUnity 3 K16) :
    ((tt a b : SU54) : GL (Fin 5) K16) = diagU (dvec5 (a : K16ˣ) (b : K16ˣ)) := rfl

theorem tt_mem (a b : rootsOfUnity 3 K16) : tt a b ∈ torus6 σ16 3 :=
  mem_torus6_iff.mpr ⟨a, b, (mem_rootsOfUnity 3 _).mp a.2, (mem_rootsOfUnity 3 _).mp b.2, rfl⟩

theorem exists_tt {t : SU54} (ht : t ∈ torus6 σ16 3) : ∃ a b, t = tt a b := by
  obtain ⟨a, b, ha, hb, hab⟩ := mem_torus6_iff.mp ht
  exact ⟨⟨a, (mem_rootsOfUnity 3 _).mpr ha⟩, ⟨b, (mem_rootsOfUnity 3 _).mpr hb⟩,
    Subtype.ext hab⟩

theorem tt_mul (a b c d : rootsOfUnity 3 K16) : tt a b * tt c d = tt (a * c) (b * d) := by
  apply Subtype.ext
  change diagU (dvec5 (a : K16ˣ) (b : K16ˣ)) * diagU (dvec5 (c : K16ˣ) (d : K16ˣ)) = _
  rw [diagU_mul]
  change _ = diagU (dvec5 ((a * c : rootsOfUnity 3 K16) : K16ˣ)
    ((b * d : rootsOfUnity 3 K16) : K16ˣ))
  congr 1
  funext i
  fin_cases i <;> simp [dvec5, mul_comm]

theorem tt_one : tt 1 1 = 1 := by
  apply Subtype.ext
  change diagU (dvec5 ((1 : rootsOfUnity 3 K16) : K16ˣ) ((1 : rootsOfUnity 3 K16) : K16ˣ)) = 1
  have h : dvec5 ((1 : rootsOfUnity 3 K16) : K16ˣ) ((1 : rootsOfUnity 3 K16) : K16ˣ) = 1 := by
    funext i
    fin_cases i <;> simp [dvec5]
  rw [h, CFSG.RankThree.PartOne.KFU.diagU_one]

theorem tt_injective {a b c d : rootsOfUnity 3 K16} (h : tt a b = tt c d) : a = c ∧ b = d := by
  have h' := congrArg (fun x : SU54 => ((x : GL (Fin 5) K16) : Matrix (Fin 5) (Fin 5) K16) 0 0) h
  have h'' := congrArg (fun x : SU54 => ((x : GL (Fin 5) K16) : Matrix (Fin 5) (Fin 5) K16) 1 1) h
  simp only [coe_tt, CFSG.RankThree.PartOne.KFU.diagU_val, Matrix.diagonal_apply_eq,
    dvec5] at h' h''
  exact ⟨Subtype.ext (Units.ext h'), Subtype.ext (Units.ext h'')⟩

abbrev perm₁ : Equiv.Perm (Fin 5) := Equiv.swap (0 : Fin 5) 1 * Equiv.swap 3 4

@[expose] noncomputable def wU : SU54 := ⟨permGL perm₁, permGL_mem_SU _ _ U5Lines.perm₁_rev⟩

theorem wU_conj_tt (a b : rootsOfUnity 3 K16) : wU * tt a b * wU⁻¹ = tt b a := by
  apply Subtype.ext
  change permGL perm₁ * diagU (dvec5 (a : K16ˣ) (b : K16ˣ)) * (permGL perm₁)⁻¹ = _
  rw [permGL_conj_diagU]
  have hs : perm₁.symm = perm₁ := by decide
  rw [hs]
  change _ = diagU (dvec5 (b : K16ˣ) (a : K16ˣ))
  congr 1
  funext i
  fin_cases i <;> rfl

theorem wU_mul_self : wU * wU = 1 := by
  apply Subtype.ext
  change permGL perm₁ * permGL perm₁ = (1 : GL (Fin 5) K16)
  rw [← map_mul, show perm₁ * perm₁ = 1 by decide, map_one]

theorem exists_model_U54 [Finite G] {A Z : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A) (hA27 : Nat.card A = 3 ^ 3)
    (hAN : A ≤ Subgroup.normalizer (Z : Set G))
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3)
    (eZ : Z ≃* projSU 5 2 2) :
    Subgroup.center Z = ⊥ ∧ Nat.card (A ⊓ Z : Subgroup G) = 9 ∧
      ∃ ε : Z ≃* U54, (∀ t ∈ torus6 σ16 3, ((ε.symm (qU t) : Z) : G) ∈ A) ∧
        ∀ f (hf : f ∈ A ⊓ Z), ∃ t ∈ torus6 σ16 3, ε ⟨f, (Subgroup.mem_inf.mp hf).2⟩ = qU t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hA.prop
  have hZc : Subgroup.center Z = ⊥ := by
    have h := card_center_mulEquiv eZ
    rw [Sec4.Item434SmallTwoOther.U54.center_U54, Subgroup.card_bot] at h
    exact Subgroup.eq_bot_of_card_eq _ h
  have hCI : Sec4.CubeInner Z :=
    (Sec4.cubeInner_of_not_three_dvd_card_outer Sec4.outU54_holds).of_mulEquiv eZ
  have h27 : ¬ 27 ∣ Nat.card Z := by
    rw [Nat.card_congr eZ.toEquiv]
    exact not_twentySeven_dvd_card_projSU_five_four
  have hF9 := card_inf_eq_nine hA hA27 hAN hZc hCI hC3 h27
  refine ⟨hZc, hF9, ?_⟩
  set eU : Z ≃* U54 := eZ.trans projSUEquivU54
  have hε₀ : IsCentralPQuot 3 eU.toMonoidHom := by
    refine ⟨eU.surjective, ?_, ?_⟩
    · intro x hx
      rw [(MonoidHom.ker_eq_bot_iff _).mpr eU.injective] at hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact Subgroup.one_mem _
    · rw [(MonoidHom.ker_eq_bot_iff _).mpr eU.injective, Subgroup.card_bot]
      norm_num
  have hTcomm : ∀ s ∈ torus6 σ16 3, ∀ t ∈ torus6 σ16 3, s * t = t * s := by
    intro s hs t ht
    obtain ⟨a, b, rfl⟩ := exists_tt hs
    obtain ⟨c, d, rfl⟩ := exists_tt ht
    rw [tt_mul, tt_mul, mul_comm a, mul_comm b]
  have hDiag : ∀ X : Subgroup SU54, (∀ x ∈ X, x ^ 3 = 1) →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → ∃ g : SU54, ∀ x ∈ X, g * x * g⁻¹ ∈ torus6 σ16 3 :=
    fun X hexp _ => exists_conj_into_d8Tor_su (n := 5) (Or.inr rfl) d8Comb_five card_K16
      Nat.prime_three (by norm_num) (by norm_num) X hexp
  have hFexp : ∀ f ∈ A ⊓ Z, f ^ 3 = 1 := fun f hf => hAe.2 f (Subgroup.mem_inf.mp hf).1
  have hFcomm : ∀ a ∈ A ⊓ Z, ∀ b ∈ A ⊓ Z, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, (Subgroup.mem_inf.mp ha).1⟩
      ⟨b, (Subgroup.mem_inf.mp hb).1⟩)
  have hmax : ∀ F' : Subgroup G, F' ≤ Z → (∀ x ∈ F', x ^ 3 = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → A ⊓ Z ≤ F' → F' = A ⊓ Z := by
    intro F' hF'Z hF'e _ hle
    have hp : IsPGroup 3 F' := fun x => ⟨1, Subtype.ext (by simpa using hF'e x x.2)⟩
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hdvd : 3 ^ k ∣ Nat.card Z := hk ▸ Subgroup.card_dvd_of_le hF'Z
    have hk2 : k ≤ 2 := by
      by_contra h
      exact h27 ((pow_dvd_pow 3 (by omega : 3 ≤ k)).trans hdvd)
    have hle9 : Nat.card F' ≤ 9 := by
      rw [hk]
      calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 9 := by norm_num
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hF9]; exact hle9)).symm
  obtain ⟨ε, hε, hT1, hT2⟩ := exists_toral_quot qU isCentralPQuot_qU eU.toMonoidHom hε₀
    (fun t ht => torus6_pow_eq_one ht) hTcomm hDiag (inf_le_right : A ⊓ Z ≤ Z) hFexp hFcomm hmax
  have hinj : Function.Injective ε := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have := hε.central hx
    rw [hZc] at this
    exact this
  set ε' : Z ≃* U54 := MulEquiv.ofBijective ε ⟨hinj, hε.surjective⟩
  refine ⟨ε', ?_, ?_⟩
  · intro t ht
    obtain ⟨f, hf⟩ := hT1 t ht
    have h1 : ε'.symm (qU t) = Subgroup.inclusion (inf_le_right : A ⊓ Z ≤ Z) f := by
      rw [MulEquiv.symm_apply_eq]
      exact hf.symm
    rw [h1]
    exact (Subgroup.mem_inf.mp f.2).1
  · intro f hf
    obtain ⟨t, ht, h⟩ := hT2 ⟨f, hf⟩
    exact ⟨t, ht, h⟩

theorem σ16_involutive : ∀ x, σ16 (σ16 x) = x := unitaryInvolution_involutive card_K16

theorem nonempty_perfectResidual_centralizer_qU {ζ : rootsOfUnity 3 K16} (hζ : ζ ≠ 1) :
    Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({qU (tt ζ ζ)} : Set U54)) ≃*
      SpecialLinearGroup (Fin 2) K16) := by
  have hq := isCentralPQuot_qU
  have hx3 : tt ζ ζ ^ 3 = 1 := torus6_pow_eq_one (tt_mem ζ ζ)
  have h1 : (ζ : K16ˣ) ≠ 1 := fun h => hζ (Subtype.ext h)
  have h3 : (ζ : K16ˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp ζ.2
  have h2 : (ζ : K16ˣ) ^ 2 ≠ 1 := by
    intro h
    apply h1
    calc (ζ : K16ˣ) = (ζ : K16ˣ) ^ 3 * ((ζ : K16ˣ) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h, inv_one, one_mul]
  have hK4 : 4 ≤ Nat.card K16 := by rw [card_K16]; norm_num
  set H := inSubgroup perfectResidual (Subgroup.centralizer ({tt ζ ζ} : Set SU54)) with hHdef
  have hmap : inSubgroup perfectResidual (Subgroup.centralizer ({qU (tt ζ ζ)} : Set U54)) =
      H.map qU := by
    rw [hHdef, CFSG.RankThree.PartOne.KFU.map_inSubgroup_perfectResidual,
      hq.map_centralizer hx3]
  have hb6 : tt ζ ζ = b6 σ16 (ζ : K16ˣ) (σ16_mu3 ζ) := rfl
  have hH : H = (suBlock6 σ16 σ16_involutive).range := by
    rw [hHdef, hb6]
    exact perfectResidual_centralizer_b6 σ16 σ16_involutive hK4 (σ16_mu3 ζ) h1 h2
  have hc : Subgroup.center H = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [hH]
    exact card_center_range_suBlock6 σ16 σ16_involutive
  have hinj : Function.Injective (qU.subgroupMap H) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hz' : (z : SU54) ∈ qU.ker := MonoidHom.mem_ker.mpr (congrArg Subtype.val hz)
    have hzc : (z : SU54) ∈ Subgroup.center SU54 := hq.central hz'
    have hzH : z ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_center_iff.mp hzc w)
    rw [hc] at hzH
    exact hzH
  exact ⟨(MulEquiv.subgroupCongr hmap).trans
    ((MulEquiv.ofBijective _ ⟨hinj, qU.subgroupMap_surjective H⟩).symm.trans
      ((MulEquiv.subgroupCongr hH).trans
        (MonoidHom.ofInjective (suBlock6_injective σ16 σ16_involutive)).symm))⟩

theorem eq_of_dvd_twentySeven {n : ℕ} (h : n ∣ 3 ^ 3) : n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 27 := by
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h
  interval_cases k <;> simp

theorem exists_mu3_ne_one : ∃ ζ : rootsOfUnity 3 K16, ζ ≠ 1 := by
  have : Nontrivial (rootsOfUnity 3 K16) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [card_mu3]; norm_num)
  exact exists_ne 1

theorem inf_centralizer_sup_eq {Z H K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer (Z : Set G)) :
    Z ⊓ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) =
      Z ⊓ Subgroup.centralizer (H : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
  · intro g hg
    obtain ⟨hgZ, hgH⟩ := Subgroup.mem_inf.mp hg
    have hle : H ⊔ K ≤ Subgroup.centralizer ({g} : Set G) := by
      refine sup_le (fun h hh => ?_) (fun k hk => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hgH h hh)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hK hk) g hgZ).symm
    refine Subgroup.mem_inf.mpr ⟨hgZ, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem u54LongRoot : U54LongRoot := by
  intro G _ _ A Z hA hA27 hAN hC3 ⟨eZ⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hA.prop
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  obtain ⟨hZc, hF9, ε, hT1, hT2⟩ := exists_model_U54 hA hA27 hAN hC3 eZ
  have hq := isCentralPQuot_qU
  set θ : SU54 →* G := Z.subtype.comp (ε.symm.toMonoidHom.comp qU) with hθ
  have hθZ : ∀ x, θ x ∈ Z := fun x => (ε.symm (qU x)).2
  have hθA : ∀ t ∈ torus6 σ16 3, θ t ∈ A := hT1
  have hθinj : ∀ x y : SU54, x ^ 3 = 1 → y ^ 3 = 1 → θ x = θ y → x = y := by
    intro x y hx hy h
    have h' : qU x = qU y := ε.symm.injective (Subtype.ext h)
    exact hq.eq_of_map_eq hx hy h'
  have hF : ∀ f ∈ A ⊓ Z, ∃ a b, f = θ (tt a b) := by
    intro f hf
    obtain ⟨t, ht, h⟩ := hT2 f hf
    obtain ⟨a, b, rfl⟩ := exists_tt ht
    refine ⟨a, b, ?_⟩
    have h1 : ε.symm (qU (tt a b)) = ⟨f, (Subgroup.mem_inf.mp hf).2⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact h.symm
    change f = ((ε.symm (qU (tt a b)) : Z) : G)
    rw [h1]
  have htt3 : ∀ a b, tt a b ^ 3 = 1 := fun a b => torus6_pow_eq_one (tt_mem a b)
  have hAZ := inf_sup_inf_centralizer_eq hA27 hZc hF9 hC3
  have hdecomp := exists_mul_of_inf_sup_eq hAZ
  set wG := θ wU with hwG
  have hwGZ : wG ∈ Z := hθZ wU
  have hwconj : ∀ a b, wG * θ (tt a b) * wG⁻¹ = θ (tt b a) := by
    intro a b
    rw [hwG, ← map_mul, ← map_inv, ← map_mul, wU_conj_tt]
  have hwC : ∀ c ∈ A ⊓ Subgroup.centralizer (Z : Set G), wG * c * wG⁻¹ = c := by
    intro c hc
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 wG hwGZ
    rw [h1, mul_inv_cancel_right]
  have hwN : wG ∈ Subgroup.normalizer (A : Set G) := by
    apply mem_normalizer_of_forall_conj_mem
    intro x hx
    obtain ⟨f, hf, c, hc, rfl⟩ := hdecomp x hx
    obtain ⟨a, b, rfl⟩ := hF f hf
    have e : wG * (θ (tt a b) * c) * wG⁻¹ = (wG * θ (tt a b) * wG⁻¹) * (wG * c * wG⁻¹) := by
      group
    rw [e, hwconj, hwC c hc]
    exact A.mul_mem (hθA _ (tt_mem b a)) (Subgroup.mem_inf.mp hc).1
  set ρ : MulAut A := A.normalizerMonoidHom ⟨wG, hwN⟩ with hρdef
  have hρapp : ∀ x : A, ((ρ x : A) : G) = wG * x * wG⁻¹ := fun x => rfl
  have hρZ : ρ ∈ starOf A Z := ⟨⟨wG, hwN⟩, Subgroup.mem_subgroupOf.mpr hwGZ, rfl⟩
  obtain ⟨ζ, hζ⟩ := exists_mu3_ne_one
  have hw2 : wG * wG = 1 := by rw [hwG, ← map_mul, wU_mul_self, map_one]
  have hρ2 : ρ * ρ = 1 := by
    ext x
    change ((ρ (ρ x) : A) : G) = x
    rw [hρapp, hρapp]
    calc wG * (wG * (x : G) * wG⁻¹) * wG⁻¹ = (wG * wG) * x * (wG * wG)⁻¹ := by group
      _ = x := by rw [hw2]; group
  have hρ1 : ρ ≠ 1 := by
    intro h
    have hx1 : θ (tt ζ 1) ∈ A := hθA _ (tt_mem ζ 1)
    have h1 := congrArg (fun φ : MulAut A => ((φ ⟨_, hx1⟩ : A) : G)) h
    simp only [MulAut.one_apply] at h1
    rw [hρapp, hwconj] at h1
    have h2 := tt_injective (hθinj _ _ (htt3 1 ζ) (htt3 ζ 1) h1)
    exact hζ h2.1.symm
  have hρord : orderOf ρ = 2 := orderOf_eq_prime (by rw [sq, hρ2]) hρ1
  set x0 := θ (tt ζ ζ) with hx0
  have hx0A : x0 ∈ A := hθA _ (tt_mem ζ ζ)
  have hx0Z : x0 ∈ Z := hθZ _
  have hx0fix : wG * x0 * wG⁻¹ = x0 := hwconj ζ ζ
  have hx01 : x0 ≠ 1 := by
    intro h
    have h1 : tt ζ ζ = tt 1 1 := by
      rw [tt_one]
      exact hθinj _ _ (htt3 ζ ζ) (one_pow 3) (by rw [← hx0, h, map_one])
    exact hζ (tt_injective h1).1
  set C := A ⊓ Subgroup.centralizer (Z : Set G) with hCdef
  set B := fixedInG A ρ with hBdef
  have hmemB : ∀ x (hx : x ∈ A), wG * x * wG⁻¹ = x → x ∈ B := by
    intro x hx h
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_fixedSubgroupOf]
    exact Subtype.ext h
  set J := Subgroup.zpowers x0 ⊔ C with hJdef
  have hJB : J ≤ B := sup_le (Subgroup.zpowers_le.mpr (hmemB x0 hx0A hx0fix))
    fun c hc => hmemB c (Subgroup.mem_inf.mp hc).1 (hwC c hc)
  have hBA : B ≤ A := Subgroup.map_subtype_le _
  have hBne : B ≠ A := by
    intro h
    apply hρ1
    ext x
    have hx : (x : G) ∈ B := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx', MulAut.one_apply]
    exact congrArg Subtype.val ((mem_fixedSubgroupOf ρ y).mp hy)
  have hx03 : Nat.card (Subgroup.zpowers x0) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hAe.2 x0 hx0A) hx01
  have hCZ : ¬ C ≤ Subgroup.zpowers x0 := by
    intro h
    have h1 : C ≤ Z ⊓ Subgroup.centralizer (Z : Set G) :=
      le_inf (h.trans (Subgroup.zpowers_le.mpr hx0Z)) inf_le_right
    rw [inf_centralizer_self_eq_bot hZc] at h1
    have h2 := Subgroup.card_le_of_le h1
    rw [hC3, Subgroup.card_bot] at h2
    omega
  have hJ3 : 3 < Nat.card J := by
    rw [← hx03]
    exact Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hCZ (h ▸ le_sup_right))
  have hB27 : Nat.card B < 27 := by
    have := Subgroup.card_lt_of_lt (lt_of_le_of_ne hBA hBne)
    rwa [hA27] at this
  have hJdvd : Nat.card J ∣ 3 ^ 3 := hA27 ▸ Subgroup.card_dvd_of_le (hJB.trans hBA)
  have hBdvd : Nat.card B ∣ 3 ^ 3 := hA27 ▸ Subgroup.card_dvd_of_le hBA
  have hJBle := Subgroup.card_le_of_le hJB
  have hB9 : Nat.card B = 9 := by
    rcases eq_of_dvd_twentySeven hJdvd with h | h | h | h <;>
      rcases eq_of_dvd_twentySeven hBdvd with h' | h' | h' | h' <;> omega
  have hJeq : J = B := Subgroup.eq_of_le_of_card_ge hJB (by
    rw [hB9]
    rcases eq_of_dvd_twentySeven hJdvd with h | h | h | h <;> omega)
  have hfix9 : Nat.card (fixedSubgroupOf ρ) = 9 := by
    rw [← hB9, hBdef, fixedInG, Subgroup.card_map_of_injective A.subtype_injective]
  have hcomm3 : Nat.card (commOf ρ) = 3 := by
    have h := card_eq_card_fixed_mul_card_commOf hAc ρ
    rw [hA27, hfix9] at h
    omega
  refine ⟨ρ, hρZ, ⟨hρord, hcomm3⟩, ?_⟩
  have hℓ : Subgroup.zpowers x0 ≤ Z := Subgroup.zpowers_le.mpr hx0Z
  have hPR : inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer (B : Set G)) =
      inSubgroup perfectResidual
        (Z ⊓ Subgroup.centralizer ((Subgroup.zpowers x0 : Subgroup G) : Set G)) := by
    rw [← hJeq, hJdef, inf_centralizer_sup_eq (inf_le_right : C ≤ _)]
  let e : Z ≃* (⊤ : Subgroup U54) := ε.trans Subgroup.topEquiv.symm
  have e₁ := U4Lines.perfectResidualEquiv e hℓ
  have hsub : (Subgroup.zpowers x0).subgroupOf Z = Subgroup.zpowers ⟨x0, hx0Z⟩ := by
    apply Subgroup.map_injective Z.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hℓ, MonoidHom.map_zpowers]
    rfl
  have hx0e : ((e ⟨x0, hx0Z⟩ : (⊤ : Subgroup U54)) : U54) = qU (tt ζ ζ) := by
    change ε ⟨x0, hx0Z⟩ = qU (tt ζ ζ)
    have h1 : (⟨x0, hx0Z⟩ : Z) = ε.symm (qU (tt ζ ζ)) := rfl
    rw [h1, MulEquiv.apply_symm_apply]
  have hmapL : U4Lines.mapL e (Subgroup.zpowers x0) = Subgroup.zpowers (qU (tt ζ ζ)) := by
    rw [U4Lines.mapL, hsub, MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hx0e
  rw [hmapL, top_inf_eq, Item222Proof.centralizer_zpowers_eq (qU (tt ζ ζ))] at e₁
  obtain ⟨e₂⟩ := nonempty_perfectResidual_centralizer_qU hζ
  exact ⟨(MulEquiv.subgroupCongr hPR).trans (e₁.trans (e₂.trans (projSLTwoEquivSL K16).symm))⟩

end CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof

namespace CFSG.RankThree.PartTwo.Sec21

theorem u54LongRoot : U54LongRoot := Item233Res3Proof.u54LongRoot

end CFSG.RankThree.PartTwo.Sec21
