module

public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCoreDefs
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofBalance
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFix
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofInv
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartOne.S15K.AutLayer
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL

public section

namespace CFSG.RankThree.PartTwo.Sec14.Proof142Res

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_sup_of {A H K : Subgroup G} (hH : A ≤ Subgroup.normalizer (H : Set G))
    (hK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  intro a ha
  have e₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hH ha)
  have e₂ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK ha)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, e₁, e₂]

theorem thetaQuotMulAut_eq_one_of_commute {L : Subgroup G} {g : G}
    (hgN : g ∈ Subgroup.normalizer (L : Set G)) (hg : ∀ l ∈ L, l * g = g * l) :
    thetaQuotMulAut L (L.normalizerMonoidHom ⟨g, hgN⟩) = 1 := by
  ext v
  induction v using QuotientGroup.induction_on with
  | H l =>
    rw [thetaQuotMulAut_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe, ← hg l l.2, mul_inv_cancel_right]

theorem thetaQuotMulAut_of_mem {L : Subgroup G} {l : G} (hl : l ∈ L) :
    thetaQuotMulAut L (L.normalizerMonoidHom ⟨l, Subgroup.le_normalizer hl⟩) =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l, hl⟩) := by
  ext v
  induction v using QuotientGroup.induction_on with
  | H m =>
    rw [thetaQuotMulAut_mk, MulAut.conj_apply, QuotientGroup.mk'_apply,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1

theorem mem_thetaQuotCentralizer_iff' {L : Subgroup G} {g : G} :
    g ∈ thetaQuotCentralizer L ↔ ∃ hg : g ∈ Subgroup.normalizer (L : Set G),
      thetaQuotMulAut L (L.normalizerMonoidHom ⟨g, hg⟩) = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, h1, rfl⟩

theorem normalizer_le_normalizer_thetaQuotCentralizer (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((thetaQuotCentralizer L : Subgroup G) : Set G) := by
  have key : ∀ g' (hg' : g' ∈ Subgroup.normalizer (L : Set G)) k,
      k ∈ thetaQuotCentralizer L → g' * k * g'⁻¹ ∈ thetaQuotCentralizer L := by
    intro g' hg' k hk
    obtain ⟨hkN, hk1⟩ := mem_thetaQuotCentralizer_iff'.mp hk
    have hm : g' * k * g'⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem (mul_mem hg' hkN) (inv_mem hg')
    refine mem_thetaQuotCentralizer_iff'.mpr ⟨hm, ?_⟩
    have e : (⟨g' * k * g'⁻¹, hm⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨g', hg'⟩ * ⟨k, hkN⟩ * (⟨g', hg'⟩ : Subgroup.normalizer (L : Set G))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hk1, mul_one, mul_inv_cancel]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨key g hg k, fun hk => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hk
  simpa [mul_assoc] using this

theorem not_mem_sup_of_inducesTypeOn_three {L : Subgroup G} {c d x : G}
    (hLθ : L ∈ thetaComponentsAt 3 c) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hcN : c ∈ Subgroup.normalizer (L : Set G)) (hcd : c * d = d * c) (hdL : d ∈ L)
    (hx : InducesTypeOn L x 3) : x ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  intro hxm
  obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup hcd hxm
  have hck : c ^ (-i) ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpow_mem _ hcN (-i)
  have hσ := thetaQuotMulAut_eq_one_of_commute hck (fun l hl =>
    (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)) (-i)).eq)
  have hx' := inducesTypeOn_mul_of_eq_one hx hck hσ
  apply Sec16.Proof1613Fix.not_mem_of_inducesTypeOn_three hLθ hx'
  have hc : Commute (d ^ j) (c ^ (-i)) :=
    (Commute.zpow_zpow (show Commute c d from hcd) (-i) j).symm
  rw [mul_assoc, hc.eq, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  exact Subgroup.zpow_mem _ hdL j

end CFSG.RankThree.PartTwo.Sec14.Proof142Res

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec14.Proof142Res
open CFSG.RankThree.PartTwo.Sec13 (card_zpowers_sup_zpowers_eq_nine sup_zpowers_eq_of_card)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped commutatorElement

theorem step142PGLCore_of (hInn : KS142InndiagNormal) (hKer : Step142PGLKer) :
    Step142PGLCore := by
  intro G _ _ A c L h hPGL _ hxA' _ Q hQ B hB hcB hALB
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hA := hD.isElemAbelian
  have hAE : Late.IsE27 A := h.isE27'
  have h27 := hD.card_eq
  have hcA := hD.mem_A
  have hAN := hD.le_normalizer
  have hLc := hD.le_centralizer
  have hLθ := hD.mem_thetaComponentsAt
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hD.commute ha hb
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hAN hcA
  obtain ⟨d, hdAL, hd1, -⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three
    (Sec16.Proof1614Trans.card_inf_eq_three_of_pgl hD hPGL)
  have hdA : d ∈ A := hdAL.1
  have hdL : d ∈ L := hdAL.2
  have hd3 : d ^ 3 = 1 := hA.2 d hdA
  have hdB : d ∈ B := hALB hdAL
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  have hZL := (Sec13.facts_of_isZ3PGLThreePi hD hPGL).2.1
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot hD hZL
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL (Subgroup.zpowers_le.mpr hdL h)
  have h9 := card_zpowers_sup_zpowers_eq_nine hA h27 hcA hdA hd1 hcd
  have hB9 : Nat.card B = 9 := by
    have := hB.2
    rw [h27] at this
    omega
  have hBeq : Subgroup.closure {c, d} = B := by
    rw [closure_pair_eq]
    exact Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr hcB) (Subgroup.zpowers_le.mpr hdB)) (by rw [hB9, h9])
  have hCB : ∀ g : G, g ∈ Subgroup.centralizer (B : Set G) ↔
      g ∈ Subgroup.centralizer ({c} : Set G) ∧ g ∈ Subgroup.centralizer ({d} : Set G) := by
    intro g
    rw [← hBeq, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hg
      exact ⟨(hg c (by simp)).symm, (hg d (by simp)).symm⟩
    · rintro ⟨hgc, hgd⟩ y (rfl | rfl)
      · exact hgc.symm
      · exact hgd.symm
  have hCBc : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
    fun g hg => ((hCB g).mp hg).1
  have hCBd : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({d} : Set G) :=
    fun g hg => ((hCB g).mp hg).2
  have h3L : 3 ∣ Nat.card L :=
    (orderOf_eq_prime hd3 hd1) ▸ Subgroup.orderOf_dvd_natCard L hdL
  have hCcN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd h h3L
  obtain ⟨x, hxA, hx⟩ := hxA'
  have hxcd := not_mem_sup_of_inducesTypeOn_three hLθ hLc hcN (hcomm c hcA d hdA) hdL hx
  have hcdA : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA)
  have hAeq := sup_zpowers_eq_of_card h27 hcdA h9 hxA hxcd
  obtain ⟨hxN, π, p, f, K, _, hK, hq, ψ, y, hyH, hy3, hact⟩ := hx
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hqs := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLθ
  have hLp : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hqs.1
  have : IsSimpleGroup ((L ⧸ aschbacherSolvableCore 3 L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := hqs.2.1
  have hLnt : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))).nontrivial
  have hq2 : 2 < p ^ f := by
    by_contra h2
    have hp := hK.prime
    have hf := hK.one_le
    have h2' : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    cases π
    · have := Sec13.isSolvable_projImage_slPi_two hK h2'
      have : Group.IsSolvable (L ⧸ aschbacherSolvableCore 3 L) :=
        Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective
      exact Group.IsPerfect.not_isSolvable _ this
    · change p ^ f % 3 = 1 at hq
      omega
  have hPp : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  have hZP : Subgroup.center (projImage (slPi π 3 (p ^ f) K)) = ⊥ := by
    have := hPp
    exact center_projImage_eq_bot hK hq
  have hNorm := hInn π p f K hK hq hq2
  have hinj : Function.Injective
      (MulAut.conj : projImage (slPi π 3 (p ^ f) K) →*
        MulAut (projImage (slPi π 3 (p ^ f) K))) := by
    intro a b hab
    have h1 : b⁻¹ * a ∈ Subgroup.center (projImage (slPi π 3 (p ^ f) K)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut (projImage (slPi π 3 (p ^ f) K)) => φ g) hab
      simp only [MulAut.conj_apply] at this
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
        _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [this]
        _ = b⁻¹ * a * g := by group
    rw [hZP, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  let ρ : Subgroup.normalizer (L : Set G) →* MulAut (projImage (slPi π 3 (p ^ f) K)) :=
    (MulAut.congr ψ).toMonoidHom.comp ((thetaQuotMulAut L).comp L.normalizerMonoidHom)
  have hρ : ∀ (g : Subgroup.normalizer (L : Set G)) (s : projImage (slPi π 3 (p ^ f) K)),
      ρ g s = ψ (thetaQuotMulAut L (L.normalizerMonoidHom g) (ψ.symm s)) := fun g s => rfl
  set db : L ⧸ aschbacherSolvableCore 3 L := QuotientGroup.mk' _ (⟨d, hdL⟩ : L) with hdb
  have hd'3 : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hdb3 : db ^ 3 = 1 := by rw [hdb, ← map_pow, hd'3, map_one]
  have hdb1 : db ≠ 1 := by
    intro h1
    have h2 := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
      (Sec16.Proof1613Inv.isPGroup_zpowers_three hd'3) (Subgroup.mem_zpowers _)
      (Subgroup.one_mem _) (by rw [map_one]; exact h1)
    exact hd1 (congrArg Subtype.val h2)
  obtain ⟨sd, hsd, hsde⟩ := Subgroup.mem_map.mp (ψ db).2
  have hsdZ : sd ∉ StatedScalars (Fin 3) K := by
    intro hsZ
    apply hdb1
    apply ψ.injective
    apply Subtype.ext
    rw [← hsde, map_one, Subgroup.coe_one, mk_eq_one_iff_mem_statedScalars]
    exact hsZ
  have hsd3 : sd ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hsde, ← Subgroup.coe_pow, ← map_pow, hdb3,
      map_one, Subgroup.coe_one]
  have hfix : thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) db = db := by
    rw [hdb, QuotientGroup.mk'_apply, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe, hcomm x hxA d hdA, mul_inv_cancel_right]
  have hysd : y * sd * y⁻¹ * sd⁻¹ ∈ StatedScalars (Fin 3) K := by
    have h1 := hact db
    rw [hfix, ← hsde] at h1
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1,
      mul_inv_cancel]
  have hsd1 := type1_of_commute_mod_type3 hK hq hy3 hsd hsdZ hsd3 hysd
  have hψdb : ψ db = ⟨ProjGenLinGroup.mk sd, ⟨sd, hsd, rfl⟩⟩ := Subtype.ext hsde.symm
  have hsig := signalPoint_of_type1 hK hq hsd hsd1
  rw [← hψdb] at hsig
  obtain ⟨W, hW3, hWN, hWle⟩ := hsig
  have hρd : ρ ⟨d, hdN⟩ = MulAut.conj (ψ db) := by
    ext s
    rw [hρ, thetaQuotMulAut_of_mem hdL, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply, MulAut.conj_apply]
  have hσc := thetaQuotMulAut_eq_one_of_commute hcN (fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLc hl))
  have hρc : ρ ⟨c, hcN⟩ = 1 := by
    change MulAut.congr ψ (thetaQuotMulAut L (L.normalizerMonoidHom ⟨c, hcN⟩)) = 1
    rw [hσc, map_one]
  set S : Subgroup G := ((inndiagPi π (p ^ f) K).comap ρ).map
    (Subgroup.normalizer (L : Set G)).subtype with hS
  have hmemS : ∀ g : G, g ∈ S ↔ ∃ hg : g ∈ Subgroup.normalizer (L : Set G),
      ρ ⟨g, hg⟩ ∈ inndiagPi π (p ^ f) K := by
    intro g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g'.2, hg'⟩
    · rintro ⟨hg, hgI⟩
      exact ⟨⟨g, hg⟩, hgI, rfl⟩
  have hcS : c ∈ S := (hmemS c).mpr ⟨hcN, by rw [hρc]; exact one_mem _⟩
  have hdS : d ∈ S := (hmemS d).mpr ⟨hdN, ⟨sd, slPi_le_glPi hπ hsd, fun s => by
    rw [hρd, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hψdb]⟩⟩
  have hxS : x ∈ S := (hmemS x).mpr ⟨hxN, ⟨y, hyH, fun s => by
    rw [hρ, hact, MulEquiv.apply_symm_apply]⟩⟩
  have hAS : A ≤ S := by
    rw [← hAeq]
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr hcS) (Subgroup.zpowers_le.mpr hdS))
      (Subgroup.zpowers_le.mpr hxS)
  have hQc : Q ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_invariantPiSubgroups hcA hD.orderOf_eq hQ.prop
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.prop.2.1
  set Y := Q ⊓ Subgroup.centralizer (B : Set G) with hY
  have hY3 : ¬ 3 ∣ Nat.card Y := fun h3 => hQ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_inf_centralizer hAE.1.1 hQ.prop.2.2 hB.1
  set Z := ⁅Y, A⁆ with hZ
  have hZY : Z ≤ Y := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Y A hAY
  have hZ3 : ¬ 3 ∣ Nat.card Z := fun h3 => hY3 (h3.trans (Subgroup.card_dvd_of_le hZY))
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized A Y hAY
  have hZB : Z ≤ Subgroup.centralizer (B : Set G) := hZY.trans inf_le_right
  have hZc : Z ≤ Subgroup.centralizer ({c} : Set G) := hZB.trans hCBc
  have hZN : Z ≤ Subgroup.normalizer (L : Set G) := hZc.trans hCcN
  have hZS : Z ≤ S := by
    rw [hZ, Subgroup.commutator_le]
    intro y₀ hy₀ a ha
    have hy₀N : y₀ ∈ Subgroup.normalizer (L : Set G) := hCcN (hQc hy₀.1)
    obtain ⟨haN, haI⟩ := (hmemS a).mp (hAS ha)
    have hm : ⁅y₀, a⁆ ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem (mul_mem (mul_mem hy₀N haN) (inv_mem hy₀N)) (inv_mem haN)
    refine (hmemS _).mpr ⟨hm, ?_⟩
    have e : (⟨⁅y₀, a⁆, hm⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨y₀, hy₀N⟩ * ⟨a, haN⟩ * (⟨y₀, hy₀N⟩ : Subgroup.normalizer (L : Set G))⁻¹ *
          (⟨a, haN⟩ : Subgroup.normalizer (L : Set G))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact mul_mem (hNorm.conj_mem _ haI _) (inv_mem haI)
  have hinner : ∀ z (hz : z ∈ Z), ∃ u : projImage (slPi π 3 (p ^ f) K),
      ρ ⟨z, hZN hz⟩ = MulAut.conj u := by
    intro z hz
    obtain ⟨hzN', hzI⟩ := (hmemS z).mp (hZS hz)
    refine exists_eq_conj_of_mem_inndiagPi hK hzI ?_
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hZ3 ?_
    refine h3.trans ((orderOf_map_dvd ρ _).trans ?_)
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_dvd_natCard Z hz
  set U : Subgroup (projImage (slPi π 3 (p ^ f) K)) :=
    ((Z.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ).comap MulAut.conj with hU
  have hUC : U ≤ Subgroup.centralizer ({ψ db} : Set (projImage (slPi π 3 (p ^ f) K))) := by
    rintro u ⟨⟨z, hzN⟩, hz', hzu⟩
    have hz : z ∈ Z := hz'
    have hzd : z * d = d * z := Subgroup.mem_centralizer_singleton_iff.mp (hCBd (hZB hz))
    have hc' : ρ ⟨z, hzN⟩ * ρ ⟨d, hdN⟩ = ρ ⟨d, hdN⟩ * ρ ⟨z, hzN⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hzd
    change ρ ⟨z, hzN⟩ = MulAut.conj u at hzu
    rw [hzu, hρd, ← map_mul, ← map_mul] at hc'
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hinj hc'
  have hU3 : ¬ 3 ∣ Nat.card U := by
    intro h3
    apply hZ3
    have h1 : Nat.card (U.map MulAut.conj) = Nat.card U := Subgroup.card_map_of_injective hinj
    have h2 : U.map MulAut.conj ≤ (Z.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ :=
      Subgroup.map_comap_le _ _
    have h4 : Nat.card (Z.subgroupOf (Subgroup.normalizer (L : Set G))) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv
    rw [← h1] at h3
    exact h4 ▸ (h3.trans (Subgroup.card_dvd_of_le h2)).trans (Subgroup.card_map_dvd _ _)
  have hUW : U ≤ W := hWle U hUC hU3
  set W' := W.comap ψ.toMonoidHom with hW'
  have hW'3 : ¬ 3 ∣ Nat.card W' := by
    have e1 : W'.map ψ.toMonoidHom = W :=
      Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective W
    rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, e1]
    exact hW3
  have hfixd : ∀ v : L ⧸ aschbacherSolvableCore 3 L, v ∈ thetaFix L hdN →
      ψ v ∈ Subgroup.centralizer ({ψ db} : Set (projImage (slPi π 3 (p ^ f) K))) := by
    intro v hv
    rw [mem_thetaFix_iff, thetaQuotMulAut_of_mem hdL, MulAut.conj_apply] at hv
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    calc v * db = db * v * db⁻¹ * db := by rw [hv]
      _ = db * v := by group
  have hW'N : thetaFix L hdN ≤
      Subgroup.normalizer (W' : Set (L ⧸ aschbacherSolvableCore 3 L)) := by
    intro v hv
    have hψv := hWN (hfixd v hv)
    rw [Subgroup.mem_normalizer_iff] at hψv ⊢
    intro w
    rw [hW', Subgroup.mem_comap, Subgroup.mem_comap]
    change ψ w ∈ W ↔ ψ (v * w * v⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv]
    exact hψv (ψ w)
  set R₀ : Subgroup G := ((W'.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) ⊓
    (Subgroup.centralizer ({d} : Set G)).subgroupOf L).map L.subtype with hR₀
  have hR₀le : R₀ ≤ L ⊓ Subgroup.centralizer ({d} : Set G) := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨l.2, Subgroup.mem_subgroupOf.mp hl.2⟩
  have hR₀W : (R₀.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) ≤ W' := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨l', hl', hll'⟩ := Subgroup.mem_subgroupOf.mp hl
    have : l' = l := Subtype.ext hll'
    rw [← this]
    exact hl'.1
  have hBC : L ⊓ Subgroup.centralizer ({d} : Set G) ≤ Subgroup.centralizer (B : Set G) :=
    fun g hg => (hCB g).mpr ⟨hLc hg.1, hg.2⟩
  have hCBN : Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (hCBc.trans hCcN) (hCBd.trans Subgroup.le_normalizer)
  have hR₀O : R₀ ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
    le_pPrimeCoreOf_of_signalFix hdN hW'3 hW'N hBC hCBN hR₀le hR₀W
  set R := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hR
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)) with hO
  have hOB : O ⊓ Subgroup.centralizer (B : Set G) ≤ R := by
    refine le_pPrimeCoreOf inf_le_right
      (Late.le_normalizer_inf (hCBc.trans (le_normalizer_pPrimeCoreOf 3 _))
        Subgroup.le_normalizer) ?_
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 _)
  set K₀ := Subgroup.centralizer ({c} : Set G) ⊓ thetaQuotCentralizer L with hK₀
  set V := (Z ⊔ R ⊔ O) ⊓ (K₀ ⊔ O) with hV
  have hZR : Z ≤ Subgroup.normalizer (R : Set G) :=
    hZB.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hZRO : Z ⊔ R ≤ Subgroup.normalizer (O : Set G) :=
    (sup_le hZc ((pPrimeCoreOf_le 3 _).trans hCBc)).trans (le_normalizer_pPrimeCoreOf 3 _)
  have hR3 : ¬ 3 ∣ Nat.card R := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (coprime_card_pPrimeCoreOf 3 _)
  have hO3 : ¬ 3 ∣ Nat.card O := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (coprime_card_pPrimeCoreOf 3 _)
  have hV3 : ¬ 3 ∣ Nat.card V := by
    intro h3
    have h1 : 3 ∣ Nat.card (Z ⊔ R ⊔ O : Subgroup G) :=
      h3.trans (Subgroup.card_dvd_of_le inf_le_left)
    have h2 := h1.trans (card_sup_dvd_card_mul hZRO)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h2 with h4 | h4
    · have h5 := h4.trans (card_sup_dvd_card_mul hZR)
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h5 with h6 | h6
      · exact hZ3 h6
      · exact hR3 h6
    · exact hO3 h4
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := le_centralizer_of_isHyperplane hAE.1.1 hB
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := hD.A_le_centralizer
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := hAc.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    Late.le_normalizer_inf
      (le_normalizer_sup_of (le_normalizer_sup_of hAZ (hAB.trans (le_normalizer_pPrimeCoreOf 3 _)))
        hAO)
      (le_normalizer_sup_of (Late.le_normalizer_inf (hAc.trans Subgroup.le_normalizer)
        (hAN.trans (normalizer_le_normalizer_thetaQuotCentralizer L))) hAO)
  have hVO : V ≤ O := hKer G A c L h hPGL V inf_le_right hV3 hAV
  intro z hz
  obtain ⟨u, hzu⟩ := hinner z hz
  have huU : u ∈ U := ⟨⟨z, hZN hz⟩, Subgroup.mem_subgroupOf.mpr hz, hzu⟩
  have huC := hUC huU
  have hθ3 : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).ker := by
    rw [QuotientGroup.ker_mk']
    exact (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
  have hσ3 : (MulAut.conj (⟨d, hdL⟩ : L)) ^ 3 = 1 := by rw [← map_pow, hd'3, map_one]
  have hσβ : ∀ l : L, QuotientGroup.mk' (aschbacherSolvableCore 3 L) (MulAut.conj ⟨d, hdL⟩ l) =
      MulAut.conj db (QuotientGroup.mk' (aschbacherSolvableCore 3 L) l) := fun l => by
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have htfix : MulAut.conj db (ψ.symm u) = ψ.symm u := by
    rw [MulAut.conj_apply]
    apply ψ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp huC
    rw [← h1, mul_inv_cancel_right]
  obtain ⟨w, hwfix, hwu⟩ := CFSG.RankThree.PartOne.S15K.exists_fixed_lift Nat.prime_three
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) (QuotientGroup.mk'_surjective _) hθ3
    (MulAut.conj ⟨d, hdL⟩) hσ3 (MulAut.conj db) hσβ htfix
  have hwd : (w : G) ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := congrArg Subtype.val hwfix
    rw [MulAut.conj_apply] at h1
    change d * (w : G) * d⁻¹ = w at h1
    calc (w : G) * d = d * w * d⁻¹ * d := by rw [h1]
      _ = d * w := by group
  have hwR₀ : (w : G) ∈ R₀ := ⟨w, ⟨by
      change ψ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) w) ∈ W
      rw [hwu, MulEquiv.apply_symm_apply]
      exact hUW huU, Subgroup.mem_subgroupOf.mpr hwd⟩, rfl⟩
  have hwR : (w : G) ∈ R := hR₀O hwR₀
  have hwB : (w : G) ∈ Subgroup.centralizer (B : Set G) := hBC (hR₀le hwR₀)
  set k := (w : G)⁻¹ * z with hk
  have hwN : (w : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer w.2
  have hkN : k ∈ Subgroup.normalizer (L : Set G) := mul_mem (inv_mem hwN) (hZN hz)
  have hσw : thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) = MulAut.conj (ψ.symm u) := by
    have := thetaQuotMulAut_of_mem (L := L) w.2
    rw [this, ← hwu]
  have hσz : thetaQuotMulAut L (L.normalizerMonoidHom ⟨z, hZN hz⟩) = MulAut.conj (ψ.symm u) := by
    ext v
    apply ψ.injective
    have h1 := congrArg (fun φ : MulAut (projImage (slPi π 3 (p ^ f) K)) => φ (ψ v)) hzu
    simp only [hρ, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
    rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hkθ : k ∈ thetaQuotCentralizer L := by
    refine mem_thetaQuotCentralizer_iff'.mpr ⟨hkN, ?_⟩
    have e : (⟨k, hkN⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨w, hwN⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨z, hZN hz⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, map_inv, hσw, hσz, inv_mul_cancel]
  have hkc : k ∈ Subgroup.centralizer ({c} : Set G) :=
    mul_mem (inv_mem (hLc w.2)) (hZc hz)
  have hkV : k ∈ V := by
    refine ⟨?_, Subgroup.mem_sup_left ⟨hkc, hkθ⟩⟩
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right (inv_mem hwR)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hz))
  have hkO : k ∈ O := hVO hkV
  have hkB : k ∈ Subgroup.centralizer (B : Set G) := mul_mem (inv_mem hwB) (hZB hz)
  have hkR : k ∈ R := hOB ⟨hkO, hkB⟩
  have hzwk : z = (w : G) * k := by rw [hk, mul_inv_cancel_left]
  rw [hzwk]
  exact mul_mem hwR hkR

end CFSG.RankThree.PartTwo.Sec14
