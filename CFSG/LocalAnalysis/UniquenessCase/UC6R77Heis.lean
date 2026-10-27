module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R77E3
public import CFSG.LocalAnalysis.UniquenessCase.UC6R77Lines
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2Key
import CFSG.GroupTheory.ProjectiveElemAbelianRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6R77

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (P65N2.exists_elemSec P65N2.ElemSec.card_eq
  P65N2.ElemSec.eq_iff P65N2.ElemSec.map_one P65N2.actEquiv P65N2.card_le_of_range
  P65N2.eq_of_trivial_on_quotient_pElt P65N2.commutator_le_self
  P65N2.normalizer_le_normalizer_commutator)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank (ZA628.commutator_pow_le_frattini)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_scalar_of_card_sq {p r : ℕ} [hr : Fact r.Prime] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpr : p ≠ r) (hpr1 : p ∣ r - 1) {X P : Subgroup G} (hX : IsPGroup r X)
    (hexp : ∀ x ∈ X, x ^ r = 1) (hXcard : Nat.card X = Nat.card (⁅X, X⁆ : Subgroup G) * r ^ 2)
    (hPX : P ≤ normalizer (X : Set G)) (hPel : IsElemAbelian p P)
    (hPc : p ^ 2 * Nat.card (P ⊓ centralizer (X : Set G) : Subgroup G) ≤ Nat.card P) :
    ∃ s ∈ P, s ∉ centralizer (X : Set G) ∧
      ∃ k : ℕ, ∀ y ∈ X, (y ^ k)⁻¹ * (s * y * s⁻¹) ∈ (⁅X, X⁆ : Subgroup G) := by
  have hle : (⁅X, X⁆ : Subgroup G) ≤ X := P65N2.commutator_le_self X
  have hNX : ∀ g ∈ normalizer (X : Set G), g ∈ normalizer ((⁅X, X⁆ : Subgroup G) : Set G) :=
    fun g hg => P65N2.normalizer_le_normalizer_commutator X hg
  have hMn : ∀ x ∈ X, ∀ m ∈ (⁅X, X⁆ : Subgroup G), x * m * x⁻¹ ∈ (⁅X, X⁆ : Subgroup G) :=
    fun x hx m hm => (mem_normalizer_iff.mp (hNX x (le_normalizer hx)) m).mp hm
  obtain ⟨W, _, _, _, π, ρ, hs⟩ := P65N2.exists_elemSec (f := r) (Y := X) (M := ⁅X, X⁆)
    (G := P) hle hMn (fun x hx y hy => commutator_mem_commutator hx hy)
    (fun x hx => by rw [hexp x hx]; exact one_mem _) hPX (fun g hg => hNX g (hPX hg))
  haveI : Finite W := Module.finite_of_finite (ZMod r)
  have hW : Module.finrank (ZMod r) W = 2 := by
    have h := hs.card_eq hle
    rw [hXcard, Module.natCard_eq_pow_finrank (K := ZMod r) (V := W), Nat.card_zmod] at h
    exact (Nat.pow_right_injective hr.out.two_le (Nat.eq_of_mul_eq_mul_left Nat.card_pos h)).symm
  have hfr : (⁅X, X⁆).subgroupOf X ≤ frattini ↥X := fun x hx =>
    ZA628.commutator_pow_le_frattini (f := r) (C := X) hX
      (mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hx)))
  have hker : ∀ a : ↥P, P65N2.actEquiv ρ (inclusion le_rfl a) = 1 →
      (a : G) ∈ centralizer (X : Set G) := by
    intro a h1
    have htriv : ∀ y ∈ X, y⁻¹ * ((a : G) * y * (a : G)⁻¹) ∈ (⁅X, X⁆ : Subgroup G) := by
      intro y hy
      have h2 : ρ a (π y) = π y := LinearEquiv.congr_fun h1 (π y)
      exact (hs.eq_iff hy ((mem_normalizer_iff.mp (hPX a.2) y).mp hy)).mp
        (h2.symm.trans (hs.act a y hy))
    exact mem_centralizer_iff.mpr fun x hx => (P65N2.eq_of_trivial_on_quotient_pElt (n := 1) hp
      hpr hX hle hMn hfr (by rw [pow_one]; exact hPel.2 a a.2) (hPX a.2) (hNX a (hPX a.2)) htriv
      x hx).symm
  set R := ((P65N2.actEquiv ρ).comp (inclusion (le_refl P))).range with hR
  haveI : Finite R := Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hRcard : p ^ 2 ≤ Nat.card R := Nat.le_of_mul_le_mul_right
    (hPc.trans (P65N2.card_le_of_range (P65N2.actEquiv ρ) le_rfl hker le_rfl)) Nat.card_pos
  have hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext (hPel.comm a.2 b.2)]
  have hRp : ∀ x ∈ R, x ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, show a ^ p = 1 from Subtype.ext (by simpa using hPel.2 a a.2), map_one]
  have hsc := CFSG.GroupTheory.card_le_pow_finrank_sub_one_mul_card_scalar hp hp2
    (by rw [Nat.card_zmod]; exact hpr1) R
    (fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hRp x x.2)⟩)
    (fun x hx y hy => ⟨1, fun v => by simp [hRc x hx y hy]⟩)
    (fun x hx => ⟨1, fun v => by simp [hRp x hx]⟩)
  rw [hW, show 2 - 1 = 1 from rfl, pow_one] at hsc
  haveI : Nontrivial {x : R // ∃ a : ZMod r, ∀ v, (x : W ≃ₗ[ZMod r] W) v = a • v} :=
    Finite.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le hp.one_lt
      (Nat.le_of_mul_le_mul_left ((pow_two p).symm.le.trans (hRcard.trans hsc)) hp.pos))
  obtain ⟨⟨x, a, hxa⟩, hx1⟩ := exists_ne (⟨1, 1, fun v => by simp⟩ :
    {x : R // ∃ a : ZMod r, ∀ v, (x : W ≃ₗ[ZMod r] W) v = a • v})
  obtain ⟨s, hsx⟩ := x.2
  have hρ : ∀ v, ρ s v = a • v := fun v => by rw [← hxa v, ← hsx]; rfl
  have hact : ∀ y ∈ X, ρ s (π y) = π ((s : G) * y * (s : G)⁻¹) := fun y hy => hs.act s y hy
  refine ⟨s, s.2, fun hsC => hx1 (Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => ?_))),
    a.val, fun y hy => ?_⟩
  ·
    obtain ⟨y, hy, rfl⟩ := hs.surj v
    have hsy : (s : G) * y * (s : G)⁻¹ = y := by
      rw [← (mem_centralizer_iff.mp hsC) y hy, mul_inv_cancel_right]
    show (x : W ≃ₗ[ZMod r] W) (π y) = π y
    rw [hxa, ← hρ, hact y hy, hsy]
  ·
    have hpow : ∀ n : ℕ, π (y ^ n) = n • π y := by
      intro n
      induction n with
      | zero => rw [pow_zero, zero_nsmul, hs.map_one]
      | succ n ih => rw [pow_succ, hs.add _ (X.pow_mem hy n) _ hy, ih, succ_nsmul]
    refine (hs.eq_iff (X.pow_mem hy _) ((mem_normalizer_iff.mp (hPX s.2) y).mp hy)).mp ?_
    rw [hpow, ← hact y hy, hρ, ← Nat.cast_smul_eq_nsmul (ZMod r), ZMod.natCast_zmod_val]

theorem two_le_pRank_normalizer_zpowers {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hpr : p ≠ r) {M X : Subgroup G} (hXM : X ≤ M) (hexp : ∀ x ∈ X, x ^ r = 1)
    (hZcard : Nat.card (X ⊓ centralizer (X : Set G) : Subgroup G) = r)
    (hX'Z : (⁅X, X⁆ : Subgroup G) ≤ X ⊓ centralizer (X : Set G)) {s c : G} (hsM : s ∈ M)
    (hsX : s ∈ normalizer (X : Set G)) (hsC : s ∉ centralizer (X : Set G)) (hso : orderOf s = p)
    {k : ℕ} (hk : ∀ y ∈ X, (y ^ k)⁻¹ * (s * y * s⁻¹) ∈ (⁅X, X⁆ : Subgroup G)) (hcM : c ∈ M)
    (hcX : c ∈ centralizer (X : Set G)) (hco : orderOf c = p) (hcs : Commute c s) {w : G}
    (hwX : w ∈ X) (hwZ : w ∉ X ⊓ centralizer (X : Set G)) :
    2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (zpowers w : Set G)) := by
  set Z : Subgroup G := X ⊓ centralizer (X : Set G) with hZdef
  have hwo : orderOf w = r := orderOf_eq_prime (hexp w hwX) fun h => hwZ (h ▸ one_mem _)
  obtain ⟨hEel, hEcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute hZcard hwo hwZ
    fun z hz => ((mem_centralizer_iff.1 (mem_inf.1 hz).2) w hwX).symm
  have hsZ : s ∈ normalizer (Z : Set G) := normalizer_le_normalizer_inf_centralizer X hsX
  have hEs : Z ⊔ zpowers w ≤ (Z ⊔ zpowers w).comap (MulAut.conj s).toMonoidHom := by
    refine sup_le (fun z hz => mem_sup_left ((mem_normalizer_iff.mp hsZ z).mp hz))
      (zpowers_le.mpr ?_)
    have h2 : s * w * s⁻¹ = w ^ k * ((w ^ k)⁻¹ * (s * w * s⁻¹)) := by group
    show s * w * s⁻¹ ∈ Z ⊔ zpowers w
    rw [h2]
    exact mul_mem (mem_sup_right (pow_mem (mem_zpowers w) k)) (mem_sup_left (hX'Z (hk w hwX)))
  have hsE : s ∈ normalizer ((Z ⊔ zpowers w : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem fun x hx => hEs hx
  obtain ⟨y, hyE, hyZ, hsy⟩ :=
    exists_mem_normalizer_zpowers_of_line hpr hEel hEcard le_sup_left hZcard hsE hsZ hso
  have hwN : zpowers w ≤ normalizer (Z : Set G) :=
    zpowers_le.mpr (normalizer_le_normalizer_inf_centralizer X (le_normalizer hwX))
  have hyZw : y ∈ (Z : Set G) * (zpowers w : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left Z (zpowers w) hwN]
    exact hyE
  obtain ⟨z₁, hz₁, v, hv, rfl⟩ := hyZw
  have hvZ : v ∉ Z := fun h => hyZ (mul_mem hz₁ h)
  have hvX : v ∈ X := zpowers_le.mpr hwX hv
  have hvw : zpowers v = zpowers w := eq_of_le_of_card_ge (zpowers_le.mpr hv) (by
    rw [Nat.card_zpowers, Nat.card_zpowers, hwo,
      orderOf_eq_prime (hexp v hvX) fun h => hvZ (h ▸ one_mem _)])
  obtain ⟨g, hgX, hg⟩ := exists_conj_eq_mul_of_not_mem hZcard hX'Z hvX hvZ hz₁
  set a : G := g⁻¹ * s * g with ha
  have hgv : g⁻¹ * (z₁ * v) * g = v := by
    rw [← hg]
    group
  have haN : a ∈ normalizer (zpowers w : Set G) := by
    rw [← hvw]
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    have h1 : g * v ^ n * g⁻¹ = (z₁ * v) ^ n := by rw [← conj_zpow, hg]
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp
      ((mem_normalizer_iff.mp hsy ((z₁ * v) ^ n)).mp (zpow_mem (mem_zpowers _) n))
    have h2 := conj_zpow (a := g⁻¹) (b := z₁ * v) (i := m)
    rw [inv_inv, hgv] at h2
    refine mem_zpowers_iff.mpr ⟨m, ?_⟩
    calc v ^ m = g⁻¹ * (z₁ * v) ^ m * g := h2
      _ = g⁻¹ * (s * (z₁ * v) ^ n * s⁻¹) * g := by rw [hm]
      _ = a * v ^ n * a⁻¹ := by rw [← h1, ha]; group
  have hao : orderOf a = p := by
    have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective s
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
    rw [ha, h, hso]
  have hcg : Commute c g := (show Commute g c from mem_centralizer_iff.1 hcX g hgX).symm
  have hac : a ∉ zpowers c := by
    intro h
    have haC := mem_centralizer_iff.mp (zpowers_le.mpr hcX h)
    refine hsC (mem_centralizer_iff.mpr fun x hx => ?_)
    have h1 := haC (g⁻¹ * x * g) (X.mul_mem (X.mul_mem (X.inv_mem hgX) hx) hgX)
    rw [ha] at h1
    calc x * s = g * ((g⁻¹ * x * g) * (g⁻¹ * s * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * s * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = s * x := by group
  refine CFSG.GroupTheory.two_le_pRank_of_commute (mem_inf.2 ⟨hcM, ?_⟩)
    (mem_inf.2 ⟨M.mul_mem (M.mul_mem (M.inv_mem (hXM hgX)) hsM) (hXM hgX), haN⟩) hco hao
    ((hcg.inv_right.mul_right hcs).mul_right hcg) hac
  exact centralizer_le_normalizer_zpowers w
    (mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hcX w hwX).symm)

theorem rankThreeGamma_le_of_pRank_le_two {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hp2 : p ≠ 2) (hpr : p ≠ r) (hpr1 : p ∣ r - 1) {M X P : Subgroup G}
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    (h76 : PartOne.Section7.Conclusion76 M p) (hXM : X ≤ M) (hX : IsPGroup r X)
    (hexp : ∀ x ∈ X, x ^ r = 1) (hcl : ⁅⁅X, X⁆, X⁆ = ⊥) (hrank : CFSG.Open.pRank r X ≤ 2)
    {a b : G} (ha : a ∈ X) (hb : b ∈ X) (hab : a * b ≠ b * a) (hPM : P ≤ M)
    (hPX : P ≤ normalizer (X : Set G)) (hPel : IsElemAbelian p P)
    (hPc : p ^ 2 * Nat.card (P ⊓ centralizer (X : Set G) : Subgroup G) ≤ Nat.card P)
    (hK : P ⊓ centralizer (X : Set G) ≠ ⊥)
    (h1 : 1 < CFSG.Open.pRank p (M ⊓ normalizer (X : Set G))) :
    rankThreeGamma 1 r X ≤ M := by
  obtain ⟨hZcard, hX'Z, hXcard⟩ :=
    card_inf_centralizer_eq_of_pRank_le_two hX hexp hcl hrank ha hb hab
  set Z : Subgroup G := X ⊓ centralizer (X : Set G) with hZdef
  obtain ⟨s, hsP, hsC, k, hk⟩ :=
    exists_mem_scalar_of_card_sq hp.out hp2 hpr hpr1 hX hexp hXcard hPX hPel hPc
  obtain ⟨c, hcK, hc1⟩ := (bot_or_exists_ne_one _).resolve_left hK
  have hcP : c ∈ P := (mem_inf.1 hcK).1
  have hcX : c ∈ centralizer (X : Set G) := (mem_inf.1 hcK).2
  have hco : orderOf c = p := orderOf_eq_prime (hPel.2 c hcP) hc1
  have hso : orderOf s = p := orderOf_eq_prime (hPel.2 s hsP) fun h => hsC (h ▸ one_mem _)
  have hΓ : ∀ w ∈ X, w ∉ Z → rankThreeGamma 1 r (Z ⊔ zpowers w) ≤ M := by
    intro w hwX hwZ
    have hwo : orderOf w = r := orderOf_eq_prime (hexp w hwX) fun h => hwZ (h ▸ one_mem _)
    obtain ⟨hEel, hEcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute hZcard hwo
      hwZ fun z hz => ((mem_centralizer_iff.1 (mem_inf.1 hz).2) w hwX).symm
    have hEX : Z ⊔ zpowers w ≤ X := sup_le inf_le_left (zpowers_le.mpr hwX)
    refine h76 r hr.out _ (hEX.trans hXM) hEel hEcard (lt_of_lt_of_le zero_lt_one
      (CFSG.SectionRank.le_pRank hp.out.one_lt
        (zpowers_le.mpr (mem_inf.2 ⟨hPM hcP, centralizer_le hEX hcX⟩))
        (isElemAbelian_zpowers (hPel.2 c hcP)) (by rw [Nat.card_zpowers, hco, pow_one])))
      fun L hLE hLcard => ?_
    by_cases hLZ : L = Z
    · rw [hLZ]
      exact lt_of_lt_of_le h1 (CFSG.SectionRank.pRank_mono hp.out.one_lt
        (inf_le_inf_left _ (normalizer_le_normalizer_inf_centralizer X)))
    obtain ⟨y, hyL, hy1⟩ := (bot_or_exists_ne_one L).resolve_left fun h => by
      rw [h, card_bot] at hLcard
      exact hr.out.one_lt.ne hLcard
    have hyX : y ∈ X := hEX (hLE hyL)
    have hyL' : zpowers y = L := eq_of_le_of_card_ge (zpowers_le.mpr hyL) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (hexp y hyX) hy1, hLcard])
    have hyZ : y ∉ Z := fun h => hLZ (eq_of_le_of_card_ge (by rw [← hyL']; exact zpowers_le.mpr h)
      (by rw [hLcard, hZcard]))
    rw [← hyL']
    exact one_lt_two.trans_le (two_le_pRank_normalizer_zpowers hpr hXM hexp hZcard hX'Z
      (hPM hsP) (hPX hsP) hsC hso hk (hPM hcP) hcX hco (hPel.comm hcP hsP) hyX hyZ)
  refine rankThreeGamma_le_of_forall_normalizer_zpowers_le hM hX hcX hco fun y hyX hy1 => ?_
  by_cases hyZ : y ∈ Z
  · have haZ : a ∉ Z := fun h => hab ((mem_centralizer_iff.1 (mem_inf.1 h).2) b hb).symm
    exact (normalizer_zpowers_le_rankThreeGamma (mem_sup_left hyZ) (hexp y hyX) hy1).trans
      (hΓ a ha haZ)
  · exact (normalizer_zpowers_le_rankThreeGamma (mem_sup_right (mem_zpowers y)) (hexp y hyX)
      hy1).trans (hΓ y hyX hyZ)

end CFSG.LocalAnalysis.UniquenessCase.UC6R77
