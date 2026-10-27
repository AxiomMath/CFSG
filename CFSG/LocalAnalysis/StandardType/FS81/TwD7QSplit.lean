module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QCent
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaHost
public import CFSG.LocalAnalysis.StandardType.FS81.TransferTwD7
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7CentDecomp
public import CFSG.LocalAnalysis.StandardType.FS81.D6ReflAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup TwD7Q

variable {G : Type} [Group G]

abbrev twD7M0 (K : Subgroup G) (B : Basis3 G 8) : Subgroup G :=
  ⁅centralizer ({B.b 1} : Set G) ⊓ K, centralizer ({B.b 1} : Set G) ⊓ K⁆

variable [Finite G]

theorem exists_split_twD7Quot {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD7 B b₀) {Y : Subgroup (Q (B.b 0 * B.b 1))} {g : Q (B.b 0 * B.b 1)}
    (hMY : img (B.b 0 * B.b 1) (twD7M0 K B) ≤ Y) (hb₀Y : B.twD7Quot.b 0 ∈ Y)
    (hgN : g ∈ normalizer (B.twD7Quot.span : Set (Q (B.b 0 * B.b 1))))
    (hYle : Y ≤ img (B.b 0 * B.b 1) (twD7M0 K B) ⊔
      (img (B.b 0 * B.b 1) (twD7M0 K B)).map (MulAut.conj g).toMonoidHom)
    (hZ : centralizer (Y : Set (Q (B.b 0 * B.b 1))) ⊓ Y = ⊥)
    (horb : ∀ n ∈ normalizer (B.twD7Quot.span : Set (Q (B.b 0 * B.b 1))), ∀ e : Coords 7,
      n * B.twD7Quot.b 0 * n⁻¹ = B.twD7Quot.vec e → IsD6Root e)
    (hfus : ∀ e : Coords 7, IsD6Root e → ∃ y ∈ Y,
      y ∈ normalizer (B.twD7Quot.span : Set (Q (B.b 0 * B.b 1))) ∧
        y * B.twD7Quot.b 0 * y⁻¹ = B.twD7Quot.vec e) :
    ∃ R : Subgroup G, R ≤ centralizer ({b₀} : Set G) ∧
      (R.subgroupOf (centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R ∧
      R ≤ cen (B.b 0 * B.b 1) ∧
      Y ≤ img (B.b 0 * B.b 1) (twD7BetaHost b₀ K E B) ∧
      img (B.b 0 * B.b 1) (twD7BetaHost b₀ K E B) ≤ Y ⊔ img (B.b 0 * B.b 1) R ∧
      (∀ y ∈ Y, ∀ r ∈ img (B.b 0 * B.b 1) R, y * r = r * y) ∧
      Y ⊓ img (B.b 0 * B.b 1) R = ⊥ := by
  classical
  have hb0 : B.b 0 = b₀ := hB.2.1
  subst hb0
  obtain ⟨_hsimple, hHyp, hCanon⟩ := id hstd
  obtain ⟨hrow, -, -, -, -, -⟩ := hCanon
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨-, hKC, -, hcenter, -, -, -, -⟩ := hA
  obtain ⟨R, hRC, hRn, hR3, hCsup, hRE, hNR, -, hRX⟩ := exists_threePrime_core_twD7 hstd hB hrec
  have hrec0 : RecOutTwD7 B (B.b 0) := hrec
  have hb₁K : B.b 1 ∈ K := hB.2.2 1 (by decide)
  have hbE : ∀ i, B.b i ∈ E := fun i => hB.1 ▸ B.b_mem_span i
  have hβE : B.b 0 * B.b 1 ∈ E := E.mul_mem (hbE 0) (hbE 1)
  have hEcen : E ≤ cen (B.b 0 * B.b 1) := by
    intro y hy
    rw [← hB.1] at hy
    obtain ⟨e, rfl⟩ := B.exists_vec_eq hy
    exact B.vec_mem_cen_twD7 e
  have hb₁1 : B.b 1 ≠ 1 := by
    intro h
    have h3 := B.ord 1
    rw [h, orderOf_one] at h3
    exact absurd h3 (by decide)
  have hRK : R ≤ centralizer (K : Set G) := by
    obtain ⟨hKs, -⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hrow hcenter
    exact hRX K hKs (le_sup_of_le_left hKC) ⟨B.b 1, hb₁K, hbE 1, hb₁1⟩
  have hRcen : R ≤ cen (B.b 0 * B.b 1) := fun r hr =>
    mem_cen_iff.mpr (mem_centralizer_iff.mp (hRE hr) _ hβE).symm
  obtain ⟨hMK, hMβ₀⟩ := commutator_centralizer_le_beta_of_std_twD7 hstd B
  have hMβ : twD7M0 K B ≤ cen (B.b 0 * B.b 1) := hMβ₀
  have hEbar : B.twD7Quot.span = img (B.b 0 * B.b 1) E := by rw [B.twD7Quot_span, hB.1]
  have hNiff : ∀ x : ↥(cen (B.b 0 * B.b 1)),
      pr _ x ∈ normalizer (B.twD7Quot.span : Set (Q (B.b 0 * B.b 1))) ↔
        (x : G) ∈ normalizer (E : Set G) := fun x => by
    rw [hEbar]
    exact pr_mem_normalizer_img_iff hβE hEcen
  set P : Subgroup G := ((Y ⊔ img (B.b 0 * B.b 1) R).comap (pr _)).map (cen _).subtype with hP
  have hmemP : ∀ x : ↥(cen (B.b 0 * B.b 1)), pr _ x ∈ Y ⊔ img (B.b 0 * B.b 1) R → (x : G) ∈ P :=
    fun x hx => ⟨x, hx, rfl⟩
  have hPmem : ∀ x : ↥(cen (B.b 0 * B.b 1)), (x : G) ∈ P → pr _ x ∈ Y ⊔ img (B.b 0 * B.b 1) R := by
    rintro x ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have hRP : R ≤ P := fun r hr =>
    hmemP ⟨r, hRcen hr⟩ (mem_sup_right (pr_mem_img hr))
  have hMP : twD7M0 K B ≤ P := fun m hm =>
    hmemP ⟨m, hMβ hm⟩ (mem_sup_left (hMY (pr_mem_img hm)))
  have hb0P : B.b 0 ∈ P := by
    refine hmemP ⟨B.b 0, B.b_mem_cen_twD7 0⟩ (mem_sup_left ?_)
    rw [B.pr_b_zero_twD7Quot]
    exact hb₀Y
  have hb1P : B.b 1 ∈ P := by
    refine hmemP ⟨B.b 1, B.b_mem_cen_twD7 1⟩ (mem_sup_left ?_)
    rw [B.pr_b_one_twD7Quot]
    exact inv_mem hb₀Y
  have hCC : centralizer ({B.b 0} : Set G) ⊓ centralizer ({B.b 1} : Set G) ≤ P := by
    refine (centralizer_inf_centralizer_eq_twD7 hstd hB hrec hRK hCsup).le.trans ?_
    exact sup_le hRP (sup_le (zpowers_le.mpr hb0P) (sup_le (zpowers_le.mpr hb1P) hMP))
  have hNYR : ∀ n ∈ normalizer (B.twD7Quot.span : Set (Q (B.b 0 * B.b 1))),
      n ∈ Y ⊔ img (B.b 0 * B.b 1) R := by
    intro n hn
    have hnb : n * B.twD7Quot.b 0 * n⁻¹ ∈ B.twD7Quot.span :=
      (mem_normalizer_iff.mp hn _).mp (B.twD7Quot.b_mem_span 0)
    obtain ⟨e, he⟩ := B.twD7Quot.exists_vec_eq hnb
    obtain ⟨y, hyY, -, hy⟩ := hfus e (horb n hn e he.symm)
    obtain ⟨z, hz⟩ := pr_surjective _ (y⁻¹ * n)
    have hzc : pr _ z ∈ centralizer ({B.twD7Quot.b 0} : Set (Q (B.b 0 * B.b 1))) := by
      rw [hz, mem_centralizer_singleton_iff]
      calc y⁻¹ * n * B.twD7Quot.b 0 = y⁻¹ * (n * B.twD7Quot.b 0 * n⁻¹) * n := by group
        _ = y⁻¹ * (y * B.twD7Quot.b 0 * y⁻¹) * n := by rw [← he, ← hy]
        _ = B.twD7Quot.b 0 * (y⁻¹ * n) := by group
    have hz0 : (z : G) ∈ centralizer ({B.b 0} : Set G) :=
      (B.pr_mem_centralizer_twD7Quot_b_zero_iff hrec0 z).mp hzc
    have hz1 : (z : G) ∈ centralizer ({B.b 1} : Set G) := by
      have h0 : Commute (z : G) (B.b 0) := mem_centralizer_singleton_iff.mp hz0
      have hβ : Commute (z : G) (B.b 0 * B.b 1) := mem_cen_iff.mp z.2
      have h1 := h0.inv_right.mul_right hβ
      rw [inv_mul_cancel_left] at h1
      exact mem_centralizer_singleton_iff.mpr h1
    have hzP : (z : G) ∈ P := hCC ⟨hz0, hz1⟩
    have hyn : n = y * (y⁻¹ * n) := by group
    rw [hyn, ← hz]
    exact mul_mem (mem_sup_left hyY) (hPmem z hzP)
  have hNP : centralizer ({B.b 0 * B.b 1} : Set G) ⊓ normalizer (E : Set G) ≤ P := by
    rintro x ⟨hxc, hxN⟩
    exact hmemP ⟨x, hxc⟩ (hNYR _ ((hNiff ⟨x, hxc⟩).mpr hxN))
  have hHP : twD7BetaHost (B.b 0) K E B ≤ P := sup_le hMP hNP
  obtain ⟨x, rfl⟩ := pr_surjective _ g
  have hxN : (x : G) ∈ normalizer (E : Set G) := (hNiff x).mp hgN
  have hxH : (x : G) ∈ twD7BetaHost (B.b 0) K E B := mem_sup_right ⟨x.2, hxN⟩
  have hMH : img (B.b 0 * B.b 1) (twD7M0 K B) ≤ img (B.b 0 * B.b 1) (twD7BetaHost (B.b 0) K E B) :=
    img_mono le_sup_left
  have hgR : ∀ r ∈ img (B.b 0 * B.b 1) R, pr _ x * r * (pr _ x)⁻¹ ∈ img (B.b 0 * B.b 1) R ∧
      (pr _ x)⁻¹ * r * pr _ x ∈ img (B.b 0 * B.b 1) R := by
    intro r hr
    obtain ⟨r', hr'R, rfl⟩ := mem_img_iff.mp hr
    have hxR := hNR hxN
    constructor
    · rw [← map_inv, ← map_mul, ← map_mul]
      exact pr_mem_img ((mem_normalizer_iff.mp hxR _).mp hr'R)
    · rw [← map_inv, ← map_mul, ← map_mul]
      apply pr_mem_img
      have h := (mem_normalizer_iff.mp (inv_mem hxR) _).mp hr'R
      simpa [mul_assoc] using h
  have hMcR : img (B.b 0 * B.b 1) (twD7M0 K B) ≤
      centralizer (img (B.b 0 * B.b 1) R : Set (Q (B.b 0 * B.b 1))) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_centralizer_iff]
    intro r hr
    obtain ⟨r', hr'R, rfl⟩ := mem_img_iff.mp hr
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have h := mem_centralizer_iff.mp (hRK hr'R) (m : G) (hMK (mem_subgroupOf.mp hm))
    simpa using h.symm
  have hMgcR : (img (B.b 0 * B.b 1) (twD7M0 K B)).map (MulAut.conj (pr _ x)).toMonoidHom ≤
      centralizer (img (B.b 0 * B.b 1) R : Set (Q (B.b 0 * B.b 1))) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_centralizer_iff]
    intro r hr
    have hr' := (hgR r hr).2
    have hc := mem_centralizer_iff.mp (hMcR hm) _ hr'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc r * (pr _ x * m * (pr _ x)⁻¹)
        = pr _ x * ((pr _ x)⁻¹ * r * pr _ x * m) * (pr _ x)⁻¹ := by group
      _ = pr _ x * (m * ((pr _ x)⁻¹ * r * pr _ x)) * (pr _ x)⁻¹ := by rw [hc]
      _ = pr _ x * m * (pr _ x)⁻¹ * r := by group
  have hYcR : Y ≤ centralizer (img (B.b 0 * B.b 1) R : Set (Q (B.b 0 * B.b 1))) :=
    hYle.trans (sup_le hMcR hMgcR)
  have hcomm : ∀ y ∈ Y, ∀ r ∈ img (B.b 0 * B.b 1) R, y * r = r * y := fun y hy r hr =>
    (mem_centralizer_iff.mp (hYcR hy) r hr).symm
  refine ⟨R, hRC, hRn, hR3, hRcen, ?_, ?_, hcomm, ?_⟩
  · refine hYle.trans (sup_le hMH ?_)
    rintro _ ⟨m, hm, rfl⟩
    have hxH' : pr _ x ∈ img (B.b 0 * B.b 1) (twD7BetaHost (B.b 0) K E B) := pr_mem_img hxH
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hxH' (hMH hm)) (inv_mem hxH')
  · rintro _ ⟨h, hh, rfl⟩
    exact hPmem h (hHP (mem_subgroupOf.mp hh))
  · rw [eq_bot_iff]
    rintro z ⟨hzY, hzR⟩
    have hzC : z ∈ centralizer (Y : Set (Q (B.b 0 * B.b 1))) :=
      mem_centralizer_iff.mpr fun y hy => hcomm y hy z hzR
    exact hZ.le ⟨hzC, hzY⟩
