module

public import CFSG.RankThree.CentralLift.LinearScalarCover
public import CFSG.RankThree.Classical.EvenSurvivingScalarRank

public section

namespace CFSG.RankThree.CentralLift

open Matrix
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (scalars mem_scalars projectiveSL proj
  scalars_eq_center)
open CFSG.RankThree.Classical (torusExp torusExp_coord torusDiag torusDiag_add torusDiag_zero
  coe_torusDiag_apply coe_diagGL det_torusDiag pow_val_add pow_val_eq_one_iff coordEquiv
  le_localRank_of_injective five_le_of_prime)
open CFSG.RankThree.CentralLift.LinearRoots (signSL signUnit signUnit_mem signUnit_notMem
  ringChar_ne_two_of_card)

section Rank

variable {k : Type} [Field k] {p : ℕ} [hp : Fact p.Prime]

@[expose] noncomputable def torusSL (hodd : Odd p) {ζ : kˣ} (hζ : orderOf ζ = p) (m : ℕ) :
    Multiplicative (Fin m → ZMod p) →* SpecialLinearGroup (Fin (m + 3)) k where
  toFun y := ⟨(torusDiag ζ m y.toAdd : Matrix (Fin (m + 3)) (Fin (m + 3)) k),
    det_torusDiag hodd hζ y.toAdd⟩
  map_one' := Subtype.ext (by
    change ((torusDiag ζ m (0 : Fin m → ZMod p) : GL (Fin (m + 3)) k) :
      Matrix (Fin (m + 3)) (Fin (m + 3)) k) = 1
    rw [torusDiag_zero]
    rfl)
  map_mul' y y' := Subtype.ext (by
    change ((torusDiag ζ m (y.toAdd + y'.toAdd) : GL (Fin (m + 3)) k) :
      Matrix (Fin (m + 3)) (Fin (m + 3)) k) = _
    rw [torusDiag_add (hζ ▸ pow_orderOf_eq_one ζ)]
    rfl)

theorem coe_torusSL (hodd : Odd p) {ζ : kˣ} (hζ : orderOf ζ = p) {m : ℕ}
    (y : Multiplicative (Fin m → ZMod p)) :
    ((torusSL hodd hζ m y : SpecialLinearGroup (Fin (m + 3)) k) :
      Matrix (Fin (m + 3)) (Fin (m + 3)) k) =
      diagonal fun i => ((ζ ^ (torusExp m y.toAdd i).val : kˣ) : k) := by
  change ((torusDiag ζ m y.toAdd : GL (Fin (m + 3)) k) :
    Matrix (Fin (m + 3)) (Fin (m + 3)) k) = _
  rw [torusDiag, coe_diagGL]

theorem le_localRank_of_scalar_survivor (hk2 : ringChar k ≠ 2) (hp2 : p ≠ 2) {m : ℕ}
    {L : Type*} [Group L] [Finite L] (φ : SpecialLinearGroup (Fin (m + 3)) k →* L)
    (hker : φ.ker ≤ scalars (m + 3) k) {ζ : kˣ} (hζ : orderOf ζ = p)
    {z : SpecialLinearGroup (Fin (m + 3)) k} (hzD : z ∈ scalars (m + 3) k)
    (hzo : orderOf (φ z) = p) : m + 1 ≤ localRank p L := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hxp : φ z ^ p = 1 := hzo ▸ pow_orderOf_eq_one (φ z)
  have hzc : ∀ g, g * z = z * g :=
    Subgroup.mem_center_iff.1 ((scalars_eq_center (m + 3) k).le hzD)
  have hxc : ∀ g, Commute (φ g) (φ z) := fun g => by
    change φ g * φ z = φ z * φ g
    rw [← map_mul, ← map_mul, hzc g]
  set a₀ := coordEquiv m (Sum.inl 0)
  set b₀ := coordEquiv m (Sum.inl 1)
  set c₀ := coordEquiv m (Sum.inr (Sum.inr 0))
  have hab : a₀ ≠ b₀ := fun h => by
    have := (coordEquiv m).injective h
    simp at this
  have hA : ({a₀, b₀} : Finset (Fin (m + 3))).card = 2 := Finset.card_pair hab
  have hc₀ : c₀ ∉ ({a₀, b₀} : Finset (Fin (m + 3))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor <;> intro h <;> have := (coordEquiv m).injective h <;> simp at this
  have hu : φ (signSL (k := k) hA) ≠ 1 := by
    intro h
    obtain ⟨c, -, hc⟩ := mem_scalars.1 (hker (MonoidHom.mem_ker.2 h))
    have h1 := congrFun (congrFun hc a₀) a₀
    have h2 := congrFun (congrFun hc c₀) c₀
    change (diagonal fun x => ((signUnit ({a₀, b₀} : Finset (Fin (m + 3))) x : kˣ) : k)) a₀ a₀ =
      _ at h1
    change (diagonal fun x => ((signUnit ({a₀, b₀} : Finset (Fin (m + 3))) x : kˣ) : k)) c₀ c₀ =
      _ at h2
    rw [diagonal_apply_eq, signUnit_mem (by simp)] at h1
    rw [diagonal_apply_eq, signUnit_notMem hc₀] at h2
    rw [scalar_apply, diagonal_apply_eq] at h1 h2
    have h3 : (-1 : k) = 1 := by
      have := h1.trans h2.symm
      simpa using this
    exact Ring.two_ne_zero hk2 (by linear_combination -h3)
  have hu2 : φ (signSL (k := k) hA) ^ 2 = 1 := by
    rw [← map_pow]
    have : signSL (k := k) hA ^ 2 = 1 := by
      refine Subtype.ext ?_
      change (diagonal fun x => ((signUnit ({a₀, b₀} : Finset (Fin (m + 3))) x : kˣ) : k)) ^ 2 = 1
      rw [pow_two, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext x
      by_cases hx : x ∈ ({a₀, b₀} : Finset (Fin (m + 3)))
      · rw [signUnit_mem hx]
        simp
      · rw [signUnit_notMem hx]
        simp
    rw [this, map_one]
  let T := torusSL (k := k) hodd hζ m
  let Ψ₁ : Multiplicative (Fin m → ZMod p) →* L := φ.comp T
  let Ψ₂ : Multiplicative (ZMod p) →* L :=
    { toFun := fun j => φ z ^ j.toAdd.val
      map_one' := by simp
      map_mul' := fun j j' => pow_val_add hxp _ _ }
  let Ψ := Ψ₁.noncommCoprod Ψ₂ fun a j => (hxc (T a)).pow_right _
  have hΨ : ∀ g, Ψ g = φ (T g.1) * φ z ^ g.2.toAdd.val := fun g =>
    MonoidHom.noncommCoprod_apply _ _ _ g
  refine le_localRank_of_injective hp.out.one_lt (fun a b => mul_comm a b) (fun a => ?_) ?_ Ψ
    ?_ hu hu2 ?_
  · refine Prod.ext ?_ ?_
    · change Multiplicative.ofAdd (p • a.1.toAdd) = 1
      have : p • a.1.toAdd = 0 := by
        funext i
        simp [nsmul_eq_mul]
      rw [this]
      rfl
    · change Multiplicative.ofAdd (p • a.2.toAdd) = 1
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rfl
  · rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, pow_succ]
  · refine (injective_iff_map_eq_one Ψ).mpr ?_
    rintro ⟨a, j⟩ h
    rw [hΨ] at h
    have hmem : T a * z ^ j.toAdd.val ∈ scalars (m + 3) k :=
      hker (MonoidHom.mem_ker.2 (by rw [map_mul, map_pow]; exact h))
    have hTD : T a ∈ scalars (m + 3) k := by
      have h2 : z ^ j.toAdd.val ∈ scalars (m + 3) k := Subgroup.pow_mem _ hzD _
      simpa using Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ h2)
    obtain ⟨ν, -, hν⟩ := mem_scalars.1 hTD
    have hentry : ∀ i, ((ζ ^ (torusExp m a.toAdd i).val : kˣ) : k) = ν := by
      intro i
      have := congrFun (congrFun hν i) i
      rw [coe_torusSL, diagonal_apply_eq, scalar_apply, diagonal_apply_eq] at this
      exact this
    have hν1 : (ν : k) = 1 := by
      rw [← hentry c₀, torusExp_coord]
      simp
    have ha : a = 1 := by
      refine Multiplicative.toAdd.injective ?_
      funext i
      have h1 := hentry (coordEquiv m (Sum.inr (Sum.inl i)))
      rw [hν1, torusExp_coord, Sum.elim_inr, Sum.elim_inl, Units.val_eq_one] at h1
      exact (pow_val_eq_one_iff hζ _).mp h1
    subst ha
    have hj : φ z ^ j.toAdd.val = 1 := by
      rw [map_one, map_one, one_mul] at h
      exact h
    have hj0 : j.toAdd = 0 := (pow_val_eq_one_iff hzo _).mp hj
    exact Prod.ext rfl (Multiplicative.toAdd.injective hj0)
  · intro g
    rw [hΨ]
    have h1 : Commute (φ (T g.1)) (φ (signSL (k := k) hA)) := by
      have hcomm : T g.1 * signSL (k := k) hA = signSL (k := k) hA * T g.1 := by
        refine Subtype.ext ?_
        change (T g.1 : Matrix (Fin (m + 3)) (Fin (m + 3)) k) *
            (diagonal fun x => ((signUnit ({a₀, b₀} : Finset (Fin (m + 3))) x : kˣ) : k)) =
          (diagonal fun x => ((signUnit ({a₀, b₀} : Finset (Fin (m + 3))) x : kˣ) : k)) *
            (T g.1 : Matrix (Fin (m + 3)) (Fin (m + 3)) k)
        rw [coe_torusSL, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext x
        exact mul_comm _ _
      change φ (T g.1) * φ (signSL (k := k) hA) = φ (signSL (k := k) hA) * φ (T g.1)
      rw [← map_mul, ← map_mul, hcomm]
    have h2 : Commute (φ z ^ g.2.toAdd.val) (φ (signSL (k := k) hA)) :=
      ((hxc (signSL (k := k) hA)).symm).pow_left _
    exact (h1.mul_left h2).eq

end Rank

theorem odd_field_linear_small_local_rank_quasisimple_prime_center_trivial {p ℓ f n : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L)
    (hZ : IsPGroup p (Subgroup.center L)) (hloc : localRank p L ≤ 2) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hf : 1 ≤ f) (hn : 2 ≤ n)
    (hM : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL n ℓ f) :
    Subgroup.center L = ⊥ := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hM
  let e' : L ⧸ Subgroup.center L ≃* projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center n K).symm)
  let η : L →* projectiveSL n K := e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hη : Function.Surjective η := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker]
    change e' (x : L ⧸ Subgroup.center L) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have : Group.IsPerfect L := hL.1
  obtain ⟨⟨φ, hφ, -⟩, hprop⟩ :=
    odd_field_linear_perfect_central_large_prime_exact_scalar_cover_map hp hp3 hℓ hℓodd hf hK hn
      η hη hηker.le (by rw [hηker]; exact hZ)
  obtain ⟨-, hker, hmapD, -, -, -, hcard⟩ := hprop φ hφ
  by_contra hne
  have : Fact p.Prime := ⟨hp⟩
  have hpZ : p ∣ Nat.card (Subgroup.center L) := by
    obtain ⟨k₀, hk₀⟩ := hZ.exists_card_eq
    rcases k₀ with _ | k₀
    · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hk₀, pow_zero])) hne
    · rw [hk₀]
      exact dvd_pow_self p (Nat.succ_ne_zero k₀)
  have hpgcd : p ∣ Nat.gcd n (ℓ ^ f - 1) := by
    rw [← hηker] at hpZ
    exact hpZ.trans hcard
  have hpn : p ∣ n := hpgcd.trans (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ ℓ ^ f - 1 := hpgcd.trans (Nat.gcd_dvd_right _ _)
  have hn5 : 5 ≤ n := (five_le_of_prime hp hp3).trans (Nat.le_of_dvd (by omega) hpn)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ, orderOf ζ = p :=
    exists_prime_orderOf_dvd_card' p (by rwa [Nat.card_units, hK])
  obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) p hpZ
  rw [Subgroup.orderOf_mk] at hxo
  have hxD : x ∈ (scalars n K).map φ := by
    rw [hmapD, hηker]
    exact hx
  obtain ⟨z, hzD, rfl⟩ := hxD
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have := le_localRank_of_scalar_survivor (ringChar_ne_two_of_card hℓ hℓodd hK) (by omega) φ
    hker hζ hzD hxo
  omega

end CFSG.RankThree.CentralLift
