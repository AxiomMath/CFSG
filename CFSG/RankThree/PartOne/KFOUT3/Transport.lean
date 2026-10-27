module

public import CFSG.RankThree.PartOne.KF.R1Model
public import CFSG.RankThree.PartOne.KFOUT3.Torus

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem card_Tor_le [Finite K] {p : ℕ} (hp : 0 < p) : Nat.card (Tor p K) ≤ p ^ 2 := by
  have h1 : Function.Injective (fun t : Tor p K =>
      (⟨Matrix.SpecialLinearGroup.toGL (t : SL3 K), t.2⟩ : torusSU p 3 K)) := by
    intro s t hst
    apply Subtype.ext
    exact Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val hst)
  exact (Nat.card_le_card_of_injective _ h1).trans (card_torusSU_le hp 2)

theorem isCentralPQuot_mk [Finite K] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    IsCentralPQuot p (QuotientGroup.mk' (Subgroup.center (SL3 K))) := by
  refine ⟨QuotientGroup.mk'_surjective _, by rw [QuotientGroup.ker_mk'], ?_⟩
  rw [QuotientGroup.ker_mk', Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h3 : (x : SL3 K) ^ 3 = 1 := center_pow_three x.2
  have h4 : orderOf (x : SL3 K) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h5' : orderOf (x : SL3 K) = p := by rw [Subgroup.orderOf_coe, hx]
  rw [h5'] at h4
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem exists_conj_Tor [Finite K] {p : ℕ} (hp : p.Prime) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (X : Subgroup (SL3 K)) (hexp : ∀ x ∈ X, x ^ p = 1)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    ∃ g : SL3 K, ∀ x ∈ X, g * x * g⁻¹ ∈ Tor p K := by
  let eSL : SL3 K ≃* ↥(StatedSL 3 K) := specialLinearGroupEquivStatedSL 3 K
  obtain ⟨g', hg'⟩ := exists_conj_torus_statedSL hp hζ (X.map eSL.toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩
      show eSL x ^ p = 1
      rw [← map_pow, hexp x hx, map_one])
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      show eSL x * eSL y = eSL y * eSL x
      rw [← map_mul, ← map_mul, hcomm x hx y hy])
  refine ⟨eSL.symm g', fun x hx => ?_⟩
  have h1 := hg' (eSL x) ⟨x, hx, rfl⟩
  rw [Subgroup.mem_subgroupOf] at h1
  show Matrix.SpecialLinearGroup.toGL (eSL.symm g' * x * (eSL.symm g')⁻¹) ∈ torusSU p 3 K
  have h2 : ((eSL (eSL.symm g' * x * (eSL.symm g')⁻¹) : ↥(StatedSL 3 K)) : GL (Fin 3) K) =
      Matrix.SpecialLinearGroup.toGL (eSL.symm g' * x * (eSL.symm g')⁻¹) := rfl
  rw [← h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact h1

theorem card_Tbar_le [Finite K] {p : ℕ} (hp : 0 < p) : Nat.card (Tbar p K) ≤ p ^ 2 := by
  have h1 : Nat.card (Tbar p K) ≤ Nat.card (Tor p K) :=
    Nat.card_le_card_of_surjective _ ((QuotientGroup.mk' (Subgroup.center (SL3 K))).subgroupMap_surjective
      (Tor p K))
  exact h1.trans (card_Tor_le hp)

theorem exists_torus_transport [Finite K] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) {L : Type} [Group L] (ε₀ : L →* PSL3 K)
    (hε₀ : IsCentralPQuot p ε₀) (T : Subgroup L) (hTexp : ∀ t ∈ T, t ^ p = 1)
    (hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) (hTcard : p ^ 2 ≤ Nat.card T) :
    ∃ κ : PSL3 K, (∀ t ∈ T, κ * ε₀ t * κ⁻¹ ∈ Tbar p K) ∧
      ∀ s ∈ Tbar p K, ∃ t ∈ T, κ * ε₀ t * κ⁻¹ = s := by
  classical
  set q : SL3 K →* PSL3 K := QuotientGroup.mk' (Subgroup.center (SL3 K)) with hq_def
  have hq : IsCentralPQuot p q := isCentralPQuot_mk hp h5
  let S : Subgroup (PSL3 K) := T.map ε₀
  have hS_comm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hTcomm x hx y hy]
  have hS_exp : ∀ a ∈ S, a ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hTexp x hx, map_one]
  let Fh : Subgroup (SL3 K) :=
    { carrier := {x | x ^ p = 1 ∧ q x ∈ S}
      mul_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        have hc : Commute x y := hq.commute_of_map_commute hx1 (by
          show q x * q y = q y * q x
          exact hS_comm _ hx2 _ hy2)
        refine ⟨?_, ?_⟩
        · rw [hc.mul_pow, hx1, hy1, mul_one]
        · rw [map_mul]
          exact S.mul_mem hx2 hy2
      one_mem' := ⟨one_pow p, by rw [map_one]; exact S.one_mem⟩
      inv_mem' := by
        rintro x ⟨hx1, hx2⟩
        exact ⟨by rw [inv_pow, hx1, inv_one], by rw [map_inv]; exact S.inv_mem hx2⟩ }
  have hFh_comm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x := fun x hx y hy =>
    (hq.commute_of_map_commute hx.1 (by
      show q x * q y = q y * q x
      exact hS_comm _ hx.2 _ hy.2)).eq
  obtain ⟨g, hg⟩ := exists_conj_Tor hp hζ Fh (fun x hx => hx.1) hFh_comm
  let ε : L →* PSL3 K := (MulAut.conj (q g)).toMonoidHom.comp ε₀
  have hker : ε.ker = ε₀.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact MulEquiv.map_eq_one_iff (MulAut.conj (q g))
  have hε : IsCentralPQuot p ε :=
    ⟨(MulAut.conj (q g)).surjective.comp hε₀.surjective, hker ▸ hε₀.central, by
      rw [hker]; exact hε₀.coprime⟩
  have hεx : ∀ x : L, ε x = q g * ε₀ x * (q g)⁻¹ := fun x => rfl
  have hstep : ∀ t ∈ T, ε t ∈ Tbar p K := by
    intro t ht
    obtain ⟨x, hx1, hx2⟩ := hq.exists_lift (hS_exp _ ⟨t, ht, rfl⟩)
    have hxF : x ∈ Fh := ⟨hx2, by rw [hx1]; exact ⟨t, ht, rfl⟩⟩
    refine mem_Tbar_iff.2 ⟨g * x * g⁻¹, hg x hxF, ?_⟩
    rw [hεx, ← hx1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rfl
  refine ⟨q g, hstep, ?_⟩
  let φ : T → Tbar p K := fun t => ⟨ε t, hstep t t.2⟩
  have hφinj : Function.Injective φ := by
    intro s t hst
    apply Subtype.ext
    exact hε.eq_of_map_eq (hTexp _ s.2) (hTexp _ t.2) (congrArg Subtype.val hst)
  have hbij : Function.Bijective φ :=
    hφinj.bijective_of_nat_card_le ((card_Tbar_le hp.pos).trans hTcard)
  intro s hs
  obtain ⟨t, ht⟩ := hbij.2 ⟨s, hs⟩
  exact ⟨t, t.2, congrArg Subtype.val ht⟩

end CFSG.RankThree.PartOne.KFOUT3
