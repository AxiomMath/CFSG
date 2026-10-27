module

public import CFSG.Quasithin.Background.FFC11B
public import CFSG.Quasithin.Background.FFC10B

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace B69

theorem natCard_statedSL_two {K : Type} [Field K] [Finite K] :
    Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two K

theorem odd_card_sq_sub_one {K : Type} [Field K] [Finite K] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) : Odd (Nat.card K ^ 2 - 1) := by
  have h2q : 2 ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨m, hm⟩ := h2q
  have hmpos : 0 < m := by
    have := Nat.card_pos (α := K)
    omega
  have h4 : Nat.card K ^ 2 = 4 * m ^ 2 := by rw [hm]; ring
  have : 0 < m ^ 2 := by positivity
  rw [h4]
  refine ⟨2 * m ^ 2 - 1, ?_⟩
  omega

theorem card_le_of_two_subgroup_natural {K : Type} [Field K] [Finite K] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) {M : Type*} [Group M] {R Q : Subgroup M} (hQR : Q ≤ R)
    (π : ↥(StatedSL 2 K) →* ↥R) (hπ : Function.Surjective π) (hQ : ∀ x ∈ Q, x ^ 2 = 1) :
    Nat.card Q ≤ Nat.card K := by
  classical
  have hdvd : Nat.card ↥R ∣ Nat.card K * (Nat.card K ^ 2 - 1) :=
    natCard_statedSL_two (K := K) ▸ Subgroup.card_dvd_of_surjective (f := π) hπ
  have hQd : Nat.card ↥Q ∣ Nat.card ↥R := by
    have h1 := Subgroup.card_mul_index (Q.subgroupOf R)
    have h2 : Nat.card (Q.subgroupOf R) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR).toEquiv
    rw [h2] at h1
    exact Dvd.intro _ h1
  have hfinR : Finite ↥R := Finite.of_surjective π hπ
  have : Finite ↥Q :=
    Finite.of_injective (Subgroup.inclusion hQR) (Subgroup.inclusion_injective hQR)
  have hQ2 : IsPGroup 2 ↥Q := fun x => ⟨1, Subtype.ext (by simpa using hQ x x.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ2
  have hQdvd : Nat.card Q ∣ Nat.card K * (Nat.card K ^ 2 - 1) := hQd.trans hdvd
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card K ^ 2 - 1) := by
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.2 (odd_card_sq_sub_one he hK))
  exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hQdvd)

theorem not_two_dvd_index_of_natural {K : Type} [Field K] [Finite K] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) {M : Type*} [Group M] {R Q : Subgroup M} (hQR : Q ≤ R)
    (π : ↥(StatedSL 2 K) →* ↥R) (hπ : Function.Surjective π) (hQc : Nat.card Q = Nat.card K) :
    ¬ 2 ∣ (Q.subgroupOf R).index := by
  classical
  have hdvd : Nat.card ↥R ∣ Nat.card K * (Nat.card K ^ 2 - 1) :=
    natCard_statedSL_two (K := K) ▸ Subgroup.card_dvd_of_surjective (f := π) hπ
  have h1 := Subgroup.card_mul_index (Q.subgroupOf R)
  have h2 : Nat.card (Q.subgroupOf R) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR).toEquiv
  rw [h2, hQc] at h1
  have hidx : (Q.subgroupOf R).index ∣ Nat.card K ^ 2 - 1 := by
    have h3 : Nat.card K * (Q.subgroupOf R).index ∣ Nat.card K * (Nat.card K ^ 2 - 1) := h1 ▸ hdvd
    exact (Nat.mul_dvd_mul_iff_left Nat.card_pos).1 h3
  intro h2d
  exact (Nat.not_even_iff_odd.2 (odd_card_sq_sub_one he hK)) (even_iff_two_dvd.2 (h2d.trans hidx))

theorem autSec_le_of_act {V : Type} [CommGroup V] {A L : Subgroup (MulAut V)} {W U : Subgroup V}
    (hAW : A ≤ stabSub W) (hAU : A ≤ stabSub U) (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U)
    (hact : ∀ a ∈ A, ∃ l ∈ L, ∀ w ∈ W, l w = a w) : autSec A W U ≤ autSec L W U := by
  set X' : Subgroup (MulAut V) := stabSub W ⊓ stabSub U with hX'
  have hX'W : X' ≤ stabSub W := inf_le_left
  have hX'U : X' ≤ stabSub U := inf_le_right
  have hAX' : A ≤ X' := le_inf hAW hAU
  have hLX' : L ≤ X' := le_inf hLW hLU
  rw [← B5.map_secHom_eq_autSec X' hX'W hX'U hAX', ← B5.map_secHom_eq_autSec X' hX'W hX'U hLX']
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨l, hl, hlw⟩ := hact (y : MulAut V) hy
  refine ⟨⟨l, hLX' hl⟩, hl, ?_⟩
  apply MulEquiv.ext
  intro s
  induction s using QuotientGroup.induction_on with
  | H u =>
    rw [B5.secHom_mk, B5.secHom_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (hlw u u.2))

theorem sq_eq_one_of_mem_autSec {V : Type} [CommGroup V] {A : Subgroup (MulAut V)} {W U : Subgroup V}
    (hAW : A ≤ stabSub W) (hAU : A ≤ stabSub U) (hA2 : ∀ a ∈ A, a ^ 2 = 1) :
    ∀ x ∈ autSec A W U, x ^ 2 = 1 := by
  intro x hx
  rw [← B5.range_secHom A hAW hAU] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [← map_pow]
  have : y ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hA2 _ y.2)
  rw [this, map_one]

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem natural_counts (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) {e : ℕ} (he : 1 ≤ e)
    (hnat : BinaryNaturalSL L W (W ⊓ fixV L) 2 e)
    (hact : ∀ a ∈ A, ∃ l ∈ L, ∀ w ∈ W, l w = a w) :
    Nat.card (autSec A W (W ⊓ fixV L)) * Nat.card (fixV (autSec A W (W ⊓ fixV L))) ≤
        Nat.card (Sec W (W ⊓ fixV L)) ∧ 2 ^ e ≤ Nat.card (autSec A W (W ⊓ fixV L)) := by
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
  have hLinv := (mem_irrPlus_top_iff.1 hW).1
  have hLW : L ≤ stabSub W := B1.le_stabSub_of_invariant hLinv
  have hLU : L ≤ stabSub (W ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hLinv (isInv_fixV L))
  have hS2 : Nat.card (Sec W (W ⊓ fixV L)) = Nat.card K ^ 2 := by
    rw [Nat.card_congr ε.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]
  obtain ⟨f, hfs, -⟩ := exists_surj_autSec hLW hLU
  have hAut_le : Nat.card (autSec A W (W ⊓ fixV L)) ≤ Nat.card K :=
    card_le_of_two_subgroup_natural he hK (autSec_le_of_act hAst hAU hLW hLU hact)
      (f.comp π) (hfs.comp hπs) (sq_eq_one_of_mem_autSec hAst hAU hA.1.2.2.1.2)
  obtain ⟨a₀, ha₀A, w₀, hw₀, hne⟩ : ∃ a₀ ∈ A, ∃ w ∈ W, a₀ w * w⁻¹ ∉ W ⊓ fixV L := by
    by_contra hcon
    push Not at hcon
    apply hnt
    rw [commSub_eq_bot_iff]
    intro w hw a ha
    exact sec_triv_imp_triv hL hAn hW hAW ha (fun w' hw' => (hcon a ha w' hw').2) w hw
  obtain ⟨l₀, hl₀, hl₀a⟩ := hact a₀ ha₀A
  obtain ⟨γ₀, hγ₀⟩ := hπs ⟨l₀, hl₀⟩
  have hγ₀a : ∀ u ∈ W, ((π γ₀ : ↥L) : MulAut V) u = a₀ u := fun u hu => by
    have := congrArg (fun g : ↥L => ((g : MulAut V) u)) hγ₀
    exact this.trans (hl₀a u hu)
  let M₀ : Matrix (Fin 2) (Fin 2) K := ((γ₀ : ↥(StatedSL 2 K)) : GL (Fin 2) K)
  have hnatAct : ∀ x : Multiplicative (Fin 2 → K),
      Multiplicative.toAdd (natAct (StatedSL 2 K) γ₀ x) = M₀.mulVec (Multiplicative.toAdd x) :=
    fun x => rfl
  have hM₀ne : M₀ ≠ 1 := by
    intro h1
    have hu : ((π γ₀ : ↥L) : MulAut V) (w₀ : V) ∈ W := by
      rw [hγ₀a _ hw₀]
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
      rw [← hγ₀a w₀ hw₀]
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
        rw [hγ₀a _ u.2]
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
          exact Subtype.ext (hγ₀a _ u.2)
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
  have hoff := sec_card_le_of_offender hA.1 hL hAn hW hAW hnt
  have hfixpos : 0 < Nat.card (fixV (autSec A W (W ⊓ fixV L))) := Nat.card_pos
  refine ⟨?_, ?_⟩
  · calc Nat.card (autSec A W (W ⊓ fixV L)) * Nat.card (fixV (autSec A W (W ⊓ fixV L)))
        ≤ Nat.card K * Nat.card K := Nat.mul_le_mul hAut_le hfix
      _ = Nat.card (Sec W (W ⊓ fixV L)) := by rw [hS2]; ring
  · rw [← hK]
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card (autSec A W (W ⊓ fixV L)) * Nat.card (fixV (autSec A W (W ⊓ fixV L))) <
        Nat.card K * Nat.card K :=
      calc Nat.card (autSec A W (W ⊓ fixV L)) * Nat.card (fixV (autSec A W (W ⊓ fixV L)))
          < Nat.card K * Nat.card (fixV (autSec A W (W ⊓ fixV L))) :=
            Nat.mul_lt_mul_of_pos_right hlt hfixpos
        _ ≤ Nat.card K * Nat.card K := Nat.mul_le_mul_left _ hfix
    have h3 : Nat.card K ^ 2 ≤ Nat.card (autSec A W (W ⊓ fixV L)) *
        Nat.card (fixV (autSec A W (W ⊓ fixV L))) := hS2 ▸ hoff
    rw [sq] at h3
    exact absurd (lt_of_le_of_lt h3 h1) (lt_irrefl _)

end Main

end B69

end CFSG.Quasithin
