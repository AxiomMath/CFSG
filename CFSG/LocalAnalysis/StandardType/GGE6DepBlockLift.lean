module

public import CFSG.LocalAnalysis.StandardType.GGE6DepBlockLiftAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

private lemma commutatorElement_center_left {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (g : G) : ⁅z, g⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp hz g).symm

private lemma commutatorElement_center_right {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (g : G) : ⁅g, z⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_center_iff.mp hz g

private lemma commutatorElement_mul_center {G : Type*} [Group G] {z x w y : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) :
    ⁅z * x, w * y⁆ = ⁅x, y⁆ := by
  have hzt : ∀ t : G, z * t * z⁻¹ = t := fun t => by
    rw [← Subgroup.mem_center_iff.mp hz t, mul_assoc, mul_inv_cancel, mul_one]
  have hwt : ∀ t : G, w * t * w⁻¹ = t := fun t => by
    rw [← Subgroup.mem_center_iff.mp hw t, mul_assoc, mul_inv_cancel, mul_one]
  calc ⁅z * x, w * y⁆
      = z * ⁅x, w * y⁆ * z⁻¹ * ⁅z, w * y⁆ :=
        commutatorElement_mul_left_eq_conj_mul z x (w * y)
    _ = z * ⁅x, w * y⁆ * z⁻¹ * 1 := by
        rw [commutatorElement_center_left hz (w * y)]
    _ = ⁅x, w * y⁆ := by rw [mul_one, hzt (⁅x, w * y⁆)]
    _ = ⁅x, w⁆ * w * ⁅x, y⁆ * w⁻¹ :=
        commutatorElement_mul_right_eq_mul_conj x w y
    _ = 1 * w * ⁅x, y⁆ * w⁻¹ := by rw [commutatorElement_center_right hw x]
    _ = ⁅x, y⁆ := by rw [one_mul, hwt (⁅x, y⁆)]

private lemma mem_center_mul_inv_of_mem_comap {L' R : Type} [Group L'] [Group R]
    (ψ : L' →* R) (hker : ψ.ker ≤ Subgroup.center L')
    (F : Set (MulAut L')) (hF : ∀ f ∈ F, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (f l))
    {ER : Subgroup R} (hER : ER ≤ ggRFix ψ F) {x : L'} (hx : x ∈ ER.comap ψ)
    {f : MulAut L'} (hf : f ∈ F) : f x * x⁻¹ ∈ Subgroup.center L' := by
  obtain ⟨l, hl, hlf⟩ := hER (Subgroup.mem_comap.mp hx)
  obtain ⟨φ, hφ⟩ := hF f hf
  have hfx : ψ (f x) = ψ x := by
    calc ψ (f x) = φ (ψ x) := (hφ x).symm
      _ = φ (ψ l) := by rw [hl]
      _ = ψ (f l) := hφ l
      _ = ψ l := hlf f hf
      _ = ψ x := hl
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, hfx, mul_inv_cancel]

private lemma commutator_comap_le_ggFix {L' R : Type} [Group L'] [Group R]
    (ψ : L' →* R) (hker : ψ.ker ≤ Subgroup.center L')
    (F : Set (MulAut L')) (hF : ∀ f ∈ F, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (f l))
    {ER : Subgroup R} (hER : ER ≤ ggRFix ψ F) {f : MulAut L'} (hf : f ∈ F) :
    ⁅ER.comap ψ, ER.comap ψ⁆ ≤ ggFix f := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [mem_ggFix, map_commutatorElement f x y]
  have hzx := mem_center_mul_inv_of_mem_comap ψ hker F hF hER hx hf
  have hzy := mem_center_mul_inv_of_mem_comap ψ hker F hF hER hy hf
  have hfx : f x = (f x * x⁻¹) * x := by rw [mul_assoc, inv_mul_cancel, mul_one]
  have hfy : f y = (f y * y⁻¹) * y := by rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [hfx, hfy]
  exact commutatorElement_mul_center hzx hzy

private lemma mem_ggRFix_of_mem_C {L' R : Type} [Group L'] [Group R]
    (ψ : L' →* R) (F : Set (MulAut L')) (C : Subgroup L')
    (hC : ∀ l, l ∈ C ↔ ∀ f ∈ F, f l = l) {g : L'} (hg : g ∈ C) :
    ψ g ∈ ggRFix ψ F := by
  refine ⟨g, rfl, ?_⟩
  intro f hf
  rw [(hC g).mp hg f hf]

private lemma le_C_of_largest_perfect {L' R : Type} [Group L'] [Group R]
    (ψ : L' →* R) (hker : ψ.ker ≤ Subgroup.center L')
    (F : Set (MulAut L')) (hF : ∀ f ∈ F, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (f l))
    (C : Subgroup L') (hC : ∀ l, l ∈ C ↔ ∀ f ∈ F, f l = l)
    {ER : Subgroup R} (hER : ER ≤ ggRFix ψ F)
    {E : Subgroup L'} (hEX : E ≤ ER.comap ψ) (hEperf : ⁅E, E⁆ = E) :
    E ≤ C := by
  intro e he
  rw [hC]
  intro f hf
  have hle : E ≤ ggFix f := by
    rw [← hEperf]
    exact (Subgroup.commutator_mono hEX hEX).trans
      (commutator_comap_le_ggFix ψ hker F hF hER hf)
  exact mem_ggFix.mp (hle he)

private lemma conj_mem_comap {L' R : Type} [Group L'] [Group R]
    (ψ : L' →* R) (F : Set (MulAut L')) (C : Subgroup L')
    (hC : ∀ l, l ∈ C ↔ ∀ f ∈ F, f l = l)
    {ER : Subgroup R} (hER : ER ≤ ggRFix ψ F)
    (hERnorm : (ER.subgroupOf (ggRFix ψ F)).Normal)
    {k : L'} (hk : k ∈ C) {e : L'} (he : e ∈ ER.comap ψ) :
    k * e * k⁻¹ ∈ ER.comap ψ := by
  rw [Subgroup.mem_comap] at he ⊢
  have hkR : ψ k ∈ ggRFix ψ F := mem_ggRFix_of_mem_C ψ F C hC hk
  have hn := (Subgroup.normal_subgroupOf_iff hER).mp hERnorm (ψ e) (ψ k) he hkR
  rw [map_mul, map_mul, map_inv]
  exact hn

private lemma normal_subgroupOf_C_of_largest_perfect {L' R : Type} [Group L'] [Group R]
    (ψ : L' →* R) (F : Set (MulAut L')) (C : Subgroup L')
    (hC : ∀ l, l ∈ C ↔ ∀ f ∈ F, f l = l)
    {ER : Subgroup R} (hER : ER ≤ ggRFix ψ F)
    (hERnorm : (ER.subgroupOf (ggRFix ψ F)).Normal)
    {E : Subgroup L'} (hEC : E ≤ C) (hEX : E ≤ ER.comap ψ) (hEperf : ⁅E, E⁆ = E)
    (hmax : ∀ P : Subgroup L', P ≤ ER.comap ψ → ⁅P, P⁆ = P → P ≤ E) :
    (E.subgroupOf C).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hEC]
  intro e k he hk
  have hconj : ∀ e' ∈ E, k * e' * k⁻¹ ∈ ER.comap ψ := fun e' he' =>
    conj_mem_comap ψ F C hC hER hERnorm hk (hEX he')
  have hperfect : ⁅E.map (MulAut.conj k : L' →* L'), E.map (MulAut.conj k : L' →* L')⁆
      = E.map (MulAut.conj k : L' →* L') := by
    rw [← Subgroup.map_commutator (H₁ := E) (H₂ := E)
      (f := (MulAut.conj k : L' →* L')), hEperf]
  have hle : E.map (MulAut.conj k : L' →* L') ≤ E :=
    hmax _ (by
      rintro _ ⟨e', he', rfl⟩
      exact hconj e' he') hperfect
  exact hle (Subgroup.mem_map.mpr ⟨e, he, rfl⟩)

private lemma perfect_le_of_le_C {L' R : Type} [Group L'] [Group R]
    (ψ : L' →* R) (F : Set (MulAut L')) (C : Subgroup L')
    (hC : ∀ l, l ∈ C ↔ ∀ f ∈ F, f l = l)
    {ER : Subgroup R} (hERmax : ∀ P : Subgroup R, P ≤ ggRFix ψ F → ⁅P, P⁆ = P → P ≤ ER)
    {E : Subgroup L'} (hmax : ∀ P : Subgroup L', P ≤ ER.comap ψ → ⁅P, P⁆ = P → P ≤ E) :
    ∀ P : Subgroup L', P ≤ C → ⁅P, P⁆ = P → P ≤ E := by
  intro P hPC hPperf
  apply hmax
  · intro p hp
    rw [Subgroup.mem_comap]
    have hmaple : P.map ψ ≤ ggRFix ψ F := by
      rintro _ ⟨p', hp', rfl⟩
      exact mem_ggRFix_of_mem_C ψ F C hC (hPC hp')
    have hperf : ⁅P.map ψ, P.map ψ⁆ = P.map ψ := by
      rw [← Subgroup.map_commutator (H₁ := P) (H₂ := P) (f := ψ), hPperf]
    exact hERmax (P.map ψ) hmaple hperf (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)
  · exact hPperf

theorem ggLayerOf_lift {L' R : Type} [Group L'] [Finite L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (F : Set (MulAut L')) (hF : ∀ f ∈ F, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (f l))
    (C : Subgroup L') (hC : ∀ l, l ∈ C ↔ ∀ f ∈ F, f l = l)
    {ER : Subgroup R} (hER : GGLayerOf (ggRFix ψ F) ER) :
    ∃ E : Subgroup L', IsComponentOf E C ∧ (∀ J : Subgroup L', IsComponentOf J C → J = E) ∧
      (∀ P : Subgroup L', P ≤ C → ⁅P, P⁆ = P → P ≤ E) ∧ E.map ψ = ER := by
  obtain ⟨hERle, hERnorm, hERqs, hERmax⟩ := hER
  obtain ⟨E, hEX, hEperf, hmax⟩ := exists_largest_perfect_subgroup (ER.comap ψ)
  have hERperf : ⁅ER, ER⁆ = ER := Subgroup.isPerfect_iff.mp hERqs.1
  have hEC : E ≤ C := le_C_of_largest_perfect ψ hker F hF C hC hERle hEX hEperf
  have hmap : E.map ψ = ER := map_eq_of_largest_perfect ψ hψ hERperf hEX hmax
  have hEqs : CFSG.Assembly.IsQuasisimple ↥E :=
    isQuasisimple_of_map_eq ψ hker hEperf hmap hERqs
  have hnormal : (E.subgroupOf C).Normal :=
    normal_subgroupOf_C_of_largest_perfect ψ F C hC hERle hERnorm hEC hEX hEperf hmax
  have hmaxC : ∀ P : Subgroup L', P ≤ C → ⁅P, P⁆ = P → P ≤ E :=
    perfect_le_of_le_C ψ F C hC hERmax hmax
  have hcomp : IsComponentOf E C :=
    ⟨hEC, Assembly.IsSubnormal.step hEC hnormal (Assembly.IsSubnormal.refl C), hEqs⟩
  refine ⟨E, hcomp, ?_, hmaxC, hmap⟩
  intro J hJ
  have hJcopy := hJ
  obtain ⟨hJC, -, hJqs⟩ := hJcopy
  have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp (⟨hJqs.1⟩ : Group.IsPerfect ↥J)
  exact eq_of_isComponentOf_of_le hEC hEqs hJ (hmaxC J hJC hJperf)

theorem exists_mem_conj_eq_of_map_eq {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R)
    (hker : ψ.ker ≤ Subgroup.center L') {E : Subgroup L'} {ER : Subgroup R}
    (hmap : E.map ψ = ER) {l : L'} (hl : ψ l ∈ ER) :
    ∃ m ∈ E, MulAut.conj m = MulAut.conj l := by
  obtain ⟨m, hmE, hm⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hl)
  have hz : m⁻¹ * l ∈ Subgroup.center L' := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hm, inv_mul_cancel]
  have hza : ∀ t : L', (m⁻¹ * l) * t = t * (m⁻¹ * l) := fun t =>
    (Subgroup.mem_center_iff.mp hz t).symm
  have hzconj : MulAut.conj (m⁻¹ * l) = 1 := by
    ext a
    rw [MulAut.conj_apply]
    show (m⁻¹ * l) * a * (m⁻¹ * l)⁻¹ = a
    rw [hza a, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨m, hmE, ?_⟩
  have hl_eq : l = m * (m⁻¹ * l) := (mul_inv_cancel_left m l).symm
  rw [hl_eq, map_mul (MulAut.conj) m (m⁻¹ * l), hzconj, mul_one]

end CFSG.StandardType

end
