module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Four
public import CFSG.LocalAnalysis.WeakClosure81.FiveSixOrder
public import CFSG.Quasithin.EmptyFaithful.S153EB6K
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmallLieModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open scoped commutatorElement IsMulCommutative

variable {W : Type} [CommGroup W] [Finite W]

private theorem f4b_exp_sec {W : Type} [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1)
    (I C : Subgroup W) : ∀ a : Sec I C, a ^ 2 = 1 := by
  intro a
  induction a using QuotientGroup.induction_on with
  | H x =>
    have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using hW (x : W))
    rw [← QuotientGroup.mk_pow, hx2]
    simp

private theorem f4b_le_stabSub {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    {I : Subgroup W} (h : StableUnder K I) : K ≤ stabSub I := by
  intro g hg
  rw [mem_stabSub]
  intro u
  exact ⟨fun hu => by simpa using h g⁻¹ (K.inv_mem hg) (g u) hu,
    fun hu => h g hg u hu⟩

private theorem f4b_perfect_range {G : Type} [Group G] {A : Type} [Group A]
    (hperf : Group.IsPerfect G) (ρ : G →* A) : ⁅ρ.range, ρ.range⁆ = ρ.range := by
  have := hperf
  exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (f := ρ))

private theorem f4b_secHom_range_ne_bot {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    {I C : Subgroup W} (hKI : K ≤ stabSub I) (hKC : K ≤ stabSub C)
    (hnt : ∃ k ∈ K, ∃ u ∈ I, (k : MulAut W) u * u⁻¹ ∉ C) :
    (B5.secHom K hKI hKC).range ≠ ⊥ := by
  intro hbot
  obtain ⟨k, hk, u, hu, hku⟩ := hnt
  have h1 : B5.secHom K hKI hKC ⟨k, hk⟩ = 1 := by
    have hmem : B5.secHom K hKI hKC ⟨k, hk⟩ ∈ (B5.secHom K hKI hKC).range :=
      ⟨⟨k, hk⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have h2 : (⟨k, hk⟩ : ↥K) ∈ (B5.secHom K hKI hKC).ker := MonoidHom.mem_ker.mpr h1
  have h3 : k ∈ centSec I C := (B5.mem_ker_secHom K hKI hKC ⟨k, hk⟩).mp h2
  exact hku ((CFSG.Quasithin.mem_centSec.mp h3).2 u hu)

theorem s134b_isSimpleGroup_of_isL3 {X : Type} [Group X] (h : UC22.IsL3 X 1) :
    IsSimpleGroup X := by
  obtain ⟨e⟩ := CFSG.Blueprint.LieModel.nonempty_mulEquiv_SL_three_two h
  have : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
    CFSG.LargeExtraspecial.S45Q.isSimpleGroup_GL_zmod_two (n := 3) (by norm_num)
  exact (e.trans (MulEquiv.ofBijective _
    CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two)).isSimpleGroup

theorem s134b_perfect_of_isL3 {G : Type} [Group G] {K : Subgroup G} (h : UC22.IsL3 ↥K 1) :
    ⁅K, K⁆ = K := by
  have : IsSimpleGroup ↥K := s134b_isSimpleGroup_of_isL3 h
  have hnotcomm : ¬ IsMulCommutative ↥K := by
    intro hcomm
    have : IsMulCommutative ↥K := hcomm
    have hprime : (Nat.card ↥K).Prime := IsSimpleGroup.prime_card
    rw [card_eq_of_isL3 h] at hprime
    norm_num at hprime
  have hcommtop : commutator ↥K = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥K) with hbot | htop
    · exact absurd ((commutator_eq_bot_iff (↥K)).mp hbot) hnotcomm
    · exact htop
  exact Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hcommtop)

theorem s134b_perfect_sec_card (hW : ∀ w : W, w ^ 2 = 1) {K : Subgroup (MulAut W)}
    (hK : ⁅K, K⁆ = K) {I C : Subgroup W} (hCI : C ≤ I) (hI : StableUnder K I)
    (hC : StableUnder K C) (hnt : ∃ k ∈ K, ∃ u ∈ I, (k : MulAut W) u * u⁻¹ ∉ C)
    (hle : Nat.card (Sec I C) ≤ 8) : Nat.card (Sec I C) = 8 := by
  have _hCI : C ≤ I := hCI
  have hKI : K ≤ stabSub I := f4b_le_stabSub hI
  have hKC : K ≤ stabSub C := f4b_le_stabSub hC
  let ρ : ↥K →* MulAut (Sec I C) := B5.secHom K hKI hKC
  have hAexp : ∀ a : Sec I C, a ^ 2 = 1 := f4b_exp_sec hW I C
  have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  have hXperf : ⁅ρ.range, ρ.range⁆ = ρ.range := f4b_perfect_range hperf ρ
  have hXne : ρ.range ≠ ⊥ := by
    change (B5.secHom K hKI hKC).range ≠ ⊥
    exact f4b_secHom_range_ne_bot hKI hKC hnt
  have hrk : rk ↥(⊤ : Subgroup (Sec I C)) ≤ 3 := by
    have h := card_eq_two_pow hAexp (⊤ : Subgroup (Sec I C))
    rw [Subgroup.card_top] at h
    have h23 : 2 ^ rk ↥(⊤ : Subgroup (Sec I C)) ≤ 2 ^ 3 := by
      rw [← h]
      exact hle.trans (by norm_num)
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h23
  obtain ⟨hrk3, -⟩ := w16f_perfect_gl_three hAexp hrk ρ.range hXperf hXne
  rw [← Subgroup.card_top (G := Sec I C), card_eq_two_pow hAexp (⊤ : Subgroup (Sec I C)), hrk3]
  norm_num

theorem s134b_natural_of_card_eight (hW : ∀ w : W, w ^ 2 = 1) {K : Subgroup (MulAut W)}
    (hL3 : UC22.IsL3 ↥K 1) {I C : Subgroup W} (hCI : C ≤ I) (hI : StableUnder K I)
    (hC : StableUnder K C) (hcard : Nat.card (Sec I C) = 8)
    (hnt : ∃ k ∈ K, ∃ u ∈ I, (k : MulAut W) u * u⁻¹ ∉ C) : BinaryNaturalSL K I C 3 1 := by
  have hK : ⁅K, K⁆ = K := s134b_perfect_of_isL3 hL3
  have hKI : K ≤ stabSub I := f4b_le_stabSub hI
  have hKC : K ≤ stabSub C := f4b_le_stabSub hC
  let ρ : ↥K →* MulAut (Sec I C) := B5.secHom K hKI hKC
  have hAexp : ∀ a : Sec I C, a ^ 2 = 1 := f4b_exp_sec hW I C
  have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  have hXperf : ⁅ρ.range, ρ.range⁆ = ρ.range := f4b_perfect_range hperf ρ
  have hXne : ρ.range ≠ ⊥ := by
    change (B5.secHom K hKI hKC).range ≠ ⊥
    exact f4b_secHom_range_ne_bot hKI hKC hnt
  have hrk : rk ↥(⊤ : Subgroup (Sec I C)) ≤ 3 := by
    have h := card_eq_two_pow hAexp (⊤ : Subgroup (Sec I C))
    rw [Subgroup.card_top, hcard] at h
    have h23 : 2 ^ rk ↥(⊤ : Subgroup (Sec I C)) ≤ 2 ^ 3 := by
      rw [← h]
      norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h23
  obtain ⟨-, hXtop⟩ := w16f_perfect_gl_three hAexp hrk ρ.range hXperf hXne
  have hXaut : ρ.range = autSec K I C := B5.range_secHom K hKI hKC
  have hXtopAut : autSec K I C = ⊤ := hXaut.symm.trans hXtop
  have hcardMulAut : Nat.card (MulAut (Sec I C)) = 168 := by
    obtain ⟨e⟩ := S153E58.nonempty_mulEquiv_pi_of_sq_eq_one hAexp (d := 3)
      (by rw [hcard]; norm_num)
    calc Nat.card (MulAut (Sec I C))
        = Nat.card (MulAut (Multiplicative (Fin 3 → ZMod 2))) :=
          Nat.card_congr (MulAut.congr e).toEquiv
      _ = Nat.card (GL (Fin 3) (ZMod 2)) :=
          Nat.card_congr (S153E58.mulAutPiEquivGL 3).toEquiv
      _ = 168 := CFSG.LocalAnalysis.ComponentInitial.card_GL_three_zmod_two
  have hcardK : Nat.card ↥K = 168 := card_eq_of_isL3 hL3
  have hker : Nat.card ρ.ker = 1 := by
    have h := Subgroup.card_ker_mul_card_range ρ
    rw [hXtop, Subgroup.card_top, hcardMulAut, hcardK] at h
    omega
  have hfaith : K ⊓ centSec I C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxker : (⟨x, hx.1⟩ : ↥K) ∈ ρ.ker :=
      (B5.mem_ker_secHom K hKI hKC ⟨x, hx.1⟩).mpr hx.2
    rw [(Subgroup.card_eq_one).mp hker, Subgroup.mem_bot] at hxker
    exact congrArg Subtype.val hxker
  let e := Subgroup.topEquiv (G := Sec I C)
  let ρ' : ↥(autSec K I C) →* MulAut ↥(⊤ : Subgroup (Sec I C)) :=
    ((MulAut.congr e).symm.toMonoidHom).comp (autSec K I C).subtype
  have hρ' : ∀ (k : ↥(autSec K I C)) (u : ↥(⊤ : Subgroup (Sec I C))),
      ((ρ' k u : ↥(⊤ : Subgroup (Sec I C))) : Sec I C) =
        (k : MulAut (Sec I C)) (u : Sec I C) := by
    intro k u
    rfl
  have hinj : Function.Injective ρ' :=
    (MulEquiv.injective (MulAut.congr e).symm).comp
      (Subgroup.subtype_injective (autSec K I C))
  have hsurj : Function.Surjective ρ' := by
    intro φ
    refine ⟨⟨(MulAut.congr e) φ, ?_⟩, ?_⟩
    · rw [hXtopAut]
      exact Subgroup.mem_top _
    · show (MulAut.congr e).symm ((MulAut.congr e) φ) = φ
      rw [MulEquiv.symm_apply_apply]
  obtain ⟨π, hπ⟩ := S153EB6.realizes_of_top (W := Sec I C) (K := autSec K I C)
    (W₁ := ⊤) hAexp (fun _ _ _ _ => Subgroup.mem_top _)
    (by rw [Subgroup.card_top]; exact hcard) ρ' hρ' hinj hsurj
  refine ⟨ZMod 2, inferInstance, inferInstance, ?_, ?_⟩
  · rw [Nat.card_zmod, pow_one]
  · exact ⟨_, B5.realizesVia_of_autSec (V := W) (W := I) (U := C) (L := K)
      hCI hKI hKC hfaith hπ⟩

end CFSG.LocalAnalysis.WeakClosure81
