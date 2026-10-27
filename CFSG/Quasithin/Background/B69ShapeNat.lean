module

public import CFSG.Quasithin.Background.B69Shape
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace B69

section Sec

variable {V : Type*} [CommGroup V]

theorem exists_sec_equiv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Γ : Subgroup (GL ι K)) {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥Γ →* ↥H}
    (h : (FFModel.nat Γ).RealizesVia H U Z π) :
    ∃ ε : Sec U Z ≃* Multiplicative (ι → K),
      ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        ε (QuotientGroup.mk ⟨_, hu⟩) = natAct Γ γ (ε (QuotientGroup.mk u)) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hker : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  let q : ↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
      (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf (⊤ : Subgroup (Multiplicative (ι → K))) ≃*
        Multiplicative (ι → K) :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  let ε : Sec U Z ≃* Multiplicative (ι → K) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective β hβs)).trans q
  have hε : ∀ u : ↥U, ε (QuotientGroup.mk u) = q (β u) := fun u => rfl
  refine ⟨ε, fun γ u hu => ?_⟩
  have hqs : ∀ x, x = (QuotientGroup.mk ⟨q x, trivial⟩ : ↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
      (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf (⊤ : Subgroup (Multiplicative (ι → K)))) :=
    fun x => by
      induction x using QuotientGroup.induction_on with
      | H m => rfl
  have h1 : β u = QuotientGroup.mk ⟨q (β u), trivial⟩ := hqs _
  have h2 := hβe γ u ⟨q (β u), trivial⟩ hu trivial h1
  rw [hε, hε]
  exact congrArg q h2

end Sec

theorem card_fixed_le {K : Type} [Field K] [Finite K] (M : Matrix (Fin 2) (Fin 2) K) (hM : M ≠ 1) :
    Nat.card {v : Fin 2 → K // M.mulVec v = v} ≤ Nat.card K := by
  let N : Submodule K (Fin 2 → K) := LinearMap.ker (Matrix.mulVecLin (M - 1))
  have hN : ∀ v, v ∈ N ↔ M.mulVec v = v := fun v => by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have hne : N ≠ ⊤ := by
    intro htop
    apply hM
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [Matrix.one_mulVec]
    exact (hN v).1 (by rw [htop]; trivial)
  have h1 : Module.finrank K N < Module.finrank K (Fin 2 → K) := Submodule.finrank_lt hne
  rw [Module.finrank_fin_fun] at h1
  have h2 : Nat.card N = Nat.card K ^ Module.finrank K N :=
    Module.natCard_eq_pow_finrank (K := K) (V := N)
  have h3 : Nat.card {v : Fin 2 → K // M.mulVec v = v} = Nat.card N :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => (hN v).symm)
  rw [h3, h2]
  calc Nat.card K ^ Module.finrank K N ≤ Nat.card K ^ 1 :=
        Nat.pow_le_pow_right Nat.card_pos (by omega)
    _ = Nat.card K := pow_one _

section Main

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_le_of_sylow_natural {K : Type} [Field K] [Finite K] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) {L A : Subgroup (MulAut V)}
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf A L) (π : ↥(StatedSL 2 K) →* ↥L)
    (hπ : Function.Surjective π) : Nat.card A ≤ Nat.card K := by
  have hSL : Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv]
    exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K
  have hdvd : Nat.card ↥L ∣ Nat.card K * (Nat.card K ^ 2 - 1) :=
    hSL ▸ Subgroup.card_dvd_of_surjective (f := π) hπ
  have h1 := Subgroup.card_mul_index (A.subgroupOf L)
  have h2 : Nat.card (A.subgroupOf L) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsyl.1).toEquiv
  rw [h2] at h1
  have hfinL : Finite ↥L := Finite.of_surjective π hπ
  have : Finite ↥A :=
    Finite.of_injective (Subgroup.inclusion hsyl.1) (Subgroup.inclusion_injective hsyl.1)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hsyl.2.1
  have hAdvd : Nat.card A ∣ Nat.card K * (Nat.card K ^ 2 - 1) := (Dvd.intro _ h1).trans hdvd
  have h2q : 2 ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨m, hm⟩ := h2q
  have hmpos : 0 < m := by
    have := Nat.card_pos (α := K)
    omega
  have hodd : Odd (Nat.card K ^ 2 - 1) := by
    have h4 : Nat.card K ^ 2 = 4 * m ^ 2 := by rw [hm]; ring
    have : 0 < m ^ 2 := by positivity
    rw [h4]
    refine ⟨2 * m ^ 2 - 1, ?_⟩
    omega
  have hcop : Nat.Coprime (Nat.card A) (Nat.card K ^ 2 - 1) := by
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hodd)
  exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hAdvd)

theorem sec_card_le_of_natural (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) {e : ℕ} (he : 1 ≤ e)
    (hnat : BinaryNaturalSL L W (W ⊓ fixV L) 2 e)
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf A L) :
    Nat.card (autSec A W (W ⊓ fixV L)) * Nat.card (fixV (autSec A W (W ⊓ fixV L))) ≤
      Nat.card (Sec W (W ⊓ fixV L)) := by
  classical
  obtain ⟨K, hKf, hKfin, hK, π₀, hπ₀⟩ := hnat
  let π : ↥(StatedSL 2 K) →* ↥L := π₀
  have hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia L W (W ⊓ fixV L) π := hπ₀
  obtain ⟨ε, hε⟩ := exists_sec_equiv (StatedSL 2 K) hπ
  have hπs : Function.Surjective π := hπ.1
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hAW := a_stab_irr hV hA hL hLA hW
  have hAst : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hnt : commSub W A ≠ ⊥ := commSub_ne_bot_of_irr hLA hW
  have hAU : A ≤ stabSub (W ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn))
  have hAL : A ≤ L := hsyl.1
  have hAq : Nat.card A ≤ Nat.card K := card_le_of_sylow_natural he hK hsyl π hπs
  have hS2 : Nat.card (Sec W (W ⊓ fixV L)) = Nat.card K ^ 2 := by
    rw [Nat.card_congr ε.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]
  have hAut_le : Nat.card (autSec A W (W ⊓ fixV L)) ≤ Nat.card A := by
    have := card_autSec_mul hAst hAU
    exact Nat.le_of_dvd Nat.card_pos ⟨_, this.symm⟩
  obtain ⟨a₀, ha₀A, w₀, hw₀, hne⟩ : ∃ a₀ ∈ A, ∃ w ∈ W, a₀ w * w⁻¹ ∉ W ⊓ fixV L := by
    by_contra hcon
    push Not at hcon
    apply hnt
    rw [commSub_eq_bot_iff]
    intro w hw a ha
    exact sec_triv_imp_triv hL hAn hW hAW ha (fun w' hw' => (hcon a ha w' hw').2) w hw
  obtain ⟨γ₀, hγ₀⟩ := hπs ⟨a₀, hAL ha₀A⟩
  have hγ₀a : ∀ u : V, ((π γ₀ : ↥L) : MulAut V) u = a₀ u := fun u =>
    congrArg (fun g : ↥L => ((g : MulAut V) u)) hγ₀
  let M₀ : Matrix (Fin 2) (Fin 2) K := ((γ₀ : ↥(StatedSL 2 K)) : GL (Fin 2) K)
  have hnatAct : ∀ x : Multiplicative (Fin 2 → K),
      Multiplicative.toAdd (natAct (StatedSL 2 K) γ₀ x) = M₀.mulVec (Multiplicative.toAdd x) :=
    fun x => rfl
  have hM₀ne : M₀ ≠ 1 := by
    intro h1
    have hu : ((π γ₀ : ↥L) : MulAut V) (w₀ : V) ∈ W := by
      rw [hγ₀a]
      exact hAW a₀ ha₀A w₀ hw₀
    have h2 := hε γ₀ ⟨w₀, hw₀⟩ hu
    have h3 : natAct (StatedSL 2 K) γ₀ (ε (QuotientGroup.mk ⟨w₀, hw₀⟩)) =
        ε (QuotientGroup.mk ⟨w₀, hw₀⟩) := by
      apply Multiplicative.toAdd.injective
      rw [hnatAct, h1, Matrix.one_mulVec]
    rw [h3] at h2
    have h4 := ε.injective h2
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h4
    apply hne
    have h5 := (W ⊓ fixV L).inv_mem h4
    have h6 : a₀ w₀ * w₀⁻¹ = (((⟨((π γ₀ : ↥L) : MulAut V) (w₀ : V), hu⟩ : ↥W)⁻¹ *
        (⟨w₀, hw₀⟩ : ↥W) : ↥W) : V)⁻¹ := by
      rw [← hγ₀a w₀]
      simp [mul_comm]
    rw [h6]
    exact h5
  have hfix : Nat.card (fixV (autSec A W (W ⊓ fixV L))) ≤ Nat.card K := by
    refine (Nat.card_le_card_of_injective
      (fun s : ↥(fixV (autSec A W (W ⊓ fixV L))) =>
        (⟨Multiplicative.toAdd (ε (s : Sec W (W ⊓ fixV L))), ?_⟩ :
          {v : Fin 2 → K // M₀.mulVec v = v})) ?_).trans (card_fixed_le M₀ hM₀ne)
    · have hφ : B5.secHom A hAst hAU ⟨a₀, ha₀A⟩ ∈ autSec A W (W ⊓ fixV L) := by
        rw [← B5.range_secHom A hAst hAU]
        exact ⟨_, rfl⟩
      have hs := (mem_fixV.1 s.2) _ hφ
      obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (s : Sec W (W ⊓ fixV L))
      have hu' : ((π γ₀ : ↥L) : MulAut V) (u : V) ∈ W := by
        rw [hγ₀a]
        exact hAW a₀ ha₀A u u.2
      have h2 := hε γ₀ u hu'
      have h3 : (QuotientGroup.mk ⟨((π γ₀ : ↥L) : MulAut V) (u : V), hu'⟩ : Sec W (W ⊓ fixV L)) =
          QuotientGroup.mk u := by
        rw [← hu] at hs
        have h7 : (QuotientGroup.mk ⟨((π γ₀ : ↥L) : MulAut V) (u : V), hu'⟩ :
            Sec W (W ⊓ fixV L)) =
            B5.secHom A hAst hAU ⟨a₀, ha₀A⟩ (QuotientGroup.mk u) := by
          rw [B5.secHom_mk]
          congr 1
          exact Subtype.ext (hγ₀a _)
        rw [h7, hs, hu]
      rw [h3] at h2
      rw [hu] at h2
      have h4 := congrArg Multiplicative.toAdd h2
      rw [hnatAct] at h4
      exact h4.symm
    · intro s t hst
      have : ε (s : Sec W (W ⊓ fixV L)) = ε (t : Sec W (W ⊓ fixV L)) := by
        have := congrArg (fun x : {v : Fin 2 → K // M₀.mulVec v = v} => Multiplicative.ofAdd x.1) hst
        simpa using this
      exact Subtype.ext (ε.injective this)
  calc Nat.card (autSec A W (W ⊓ fixV L)) * Nat.card (fixV (autSec A W (W ⊓ fixV L)))
      ≤ Nat.card K * Nat.card K := Nat.mul_le_mul (hAut_le.trans hAq) hfix
    _ = Nat.card (Sec W (W ⊓ fixV L)) := by rw [hS2]; ring

theorem eq_sup_fixV_of_natural (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) {e : ℕ} (he : 1 ≤ e)
    (hnat : BinaryNaturalSL L W (W ⊓ fixV L) 2 e)
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf A L) : W ⊔ fixV A = ⊤ ∧ A ⊓ centSub W = ⊥ :=
  eq_sup_fixV_of_sec hV hA hL hLA hW (sec_card_le_of_natural hV hA hL hLA hW he hnat hsyl)

omit [Finite V] in
theorem card_le_two_of_swap {n : ℕ} {Ω : Type*} [Group Ω] (f : Equiv.Perm (Fin n) →* Ω)
    (i j : Fin n) : Nat.card ((Subgroup.zpowers (Equiv.swap i j)).map f) ≤ 2 := by
  rw [MonoidHom.map_zpowers, Nat.card_zpowers]
  refine orderOf_le_of_pow_eq_one (by norm_num) ?_
  rw [← map_pow, pow_two, Equiv.swap_mul_self, map_one]

theorem eq_sup_fixV_of_shape (hV : ∀ v : V, v ^ 2 = 1) {X T M A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hshape : CompShape T M A L W) :
    W ⊔ fixV A = ⊤ ∧ A ⊓ centSub W = ⊥ := by
  rcases hshape with ⟨⟨e, he, hnat⟩, hsyl, -⟩ | ⟨k, -, π, -, -, -, ⟨i, j, -, hAij⟩, -⟩
  · exact eq_sup_fixV_of_natural hV hA hL hLA hW he hnat hsyl
  · refine eq_sup_fixV_of_card_le_two hV hA hL hLA hW ?_
    rw [hAij]
    exact card_le_two_of_swap _ i j

end Main

end B69

end CFSG.Quasithin
