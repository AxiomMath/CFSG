module

import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def conjAut {N K : Subgroup G} (h : K ≤ Subgroup.normalizer (N : Set G)) :
    K →* MulAut N :=
  N.normalizerMonoidHom.comp (Subgroup.inclusion h)

theorem conjAut_apply_coe {N K : Subgroup G} (h : K ≤ Subgroup.normalizer (N : Set G))
    (k : K) (n : N) : ((conjAut h k n : N) : G) = k * n * k⁻¹ := rfl

theorem le_pRank [Finite G] {p : ℕ} (hp : p.Prime) {X E : Subgroup G} (hEX : E ≤ X)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ pRank p X :=
  CFSG.SectionRank.le_pRank hp.one_lt hEX hE hk

theorem exists_elemAbelian_sup_zpowers [Finite G] {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hE : IsElemAbelian p E) {y : G} (hy : orderOf y = p) (hcomm : ∀ e ∈ E, Commute e y)
    (hyE : y ∉ E) :
    IsElemAbelian p (E ⊔ Subgroup.zpowers y) ∧
      Nat.card ↥(E ⊔ Subgroup.zpowers y) = Nat.card E * p := by
  classical
  have hEc := hE.1
  set Y := Subgroup.zpowers y with hYdef
  have hYcard : Nat.card Y = p := by rw [hYdef, Nat.card_zpowers, hy]
  have hyp : y ^ p = 1 := hy ▸ pow_orderOf_eq_one y
  have hEY : E ⊓ Y = ⊥ := by
    have h1 : Nat.card (E ⊓ Y : Subgroup G) ∣ p := by
      rw [← hYcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 h1 with h | h
    · exact Subgroup.card_eq_one.1 h
    · exfalso
      apply hyE
      have hle : E ⊓ Y = Y := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hYcard])
      have : y ∈ E ⊓ Y := by rw [hle]; exact Subgroup.mem_zpowers y
      exact this.1
  have hcm : ∀ (e : E) (w : Y), Commute (E.subtype e) (Y.subtype w) := by
    intro e w
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 w.2
    simp only [Subgroup.coe_subtype]
    rw [← hk]
    exact (hcomm e e.2).zpow_right k
  let f : E × Y →* G := MonoidHom.noncommCoprod E.subtype Y.subtype hcm
  have hf : ∀ z : E × Y, f z = (z.1 : G) * (z.2 : G) := fun z => rfl
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨e, w⟩ hz
    rw [MonoidHom.mem_ker, hf] at hz
    have hmem : (e : G) ∈ E ⊓ Y := ⟨e.2, by
      have : (e : G) = ((w : G))⁻¹ := eq_inv_of_mul_eq_one_left hz
      rw [this]; exact Y.inv_mem w.2⟩
    rw [hEY] at hmem
    have he : (e : G) = 1 := hmem
    have hw : (w : G) = 1 := by rw [he, one_mul] at hz; exact hz
    simp only [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext he, Subtype.ext hw⟩
  have hrange : f.range = E ⊔ Y := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hcommE : ∀ z z' : E × Y, z * z' = z' * z := by
    intro z z'
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact congrArg Subtype.val (hEc.is_comm.comm z.1 z'.1)
    · have : IsMulCommutative Y := inferInstance
      exact congrArg Subtype.val (this.is_comm.comm z.2 z'.2)
  rw [← hrange]
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨z, hz⟩ := a.2
    obtain ⟨z', hz'⟩ := b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hz, ← hz', ← map_mul, ← map_mul, hcommE]
  · rintro x ⟨z, rfl⟩
    rw [← map_pow]
    have : z ^ p = 1 := by
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact hE.2 z.1 z.1.2
      · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 z.2.2
        show ((z.2 : G)) ^ p = 1
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow]
    rw [this, map_one]
  · have : Nat.card f.range = Nat.card (E × Y) :=
      (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
    rw [this, Nat.card_prod, hYcard]

theorem exists_orderOf_eq_of_isPGroup_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    {P H : Subgroup G} (hP : IsPGroup p P) (hPH : P ≤ Subgroup.normalizer (H : Set G))
    (hdvd : p ∣ Nat.card H) :
    ∃ x ∈ H, orderOf x = p ∧ x ∈ Subgroup.centralizer (P : Set G) := by
  classical
  let _ : MulDistribMulAction P H := MulDistribMulAction.compHom H (conjAut hPH)
  have h1 := hP.card_modEq_card_fixedPoints H
  have h2 : p ∣ Nat.card (MulAction.fixedPoints P H) :=
    Nat.modEq_zero_iff_dvd.1 (h1.symm.trans (Nat.modEq_zero_iff_dvd.2 hdvd))
  let F : Subgroup H := FixedPoints.subgroup P H
  have hF : Nat.card F = Nat.card (MulAction.fixedPoints P H) := rfl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := F) p (by rw [hF]; exact h2)
  refine ⟨((x : H) : G), (x : H).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h3 : (⟨g, hg⟩ : P) • (x : H) = (x : H) := x.2 ⟨g, hg⟩
    have h4 := congrArg Subtype.val h3
    change g * ((x : H) : G) * g⁻¹ = ((x : H) : G) at h4
    rw [mul_inv_eq_iff_eq_mul] at h4
    exact h4

theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem normalizer_le_normalizer_centralizer (U : Subgroup G) :
    Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff] at hg ⊢
  have key : ∀ g ∈ Subgroup.normalizer (U : Set G), ∀ c ∈ Subgroup.centralizer (U : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rw [Subgroup.mem_set_normalizer_iff] at hg
    have hu' : g⁻¹ * u * g ∈ U := by
      have := (hg (g⁻¹ * u * g)).2 (by simpa [mul_assoc] using hu)
      exact this
    have := Subgroup.mem_centralizer_iff.1 hc _ hu'
    calc u * (g * c * g⁻¹) = g * ((g⁻¹ * u * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * u * g)) * g⁻¹ := by rw [this]
      _ = (g * c * g⁻¹) * u := by group
  intro c
  constructor
  · intro hc
    exact key g (by rw [Subgroup.mem_set_normalizer_iff]; exact hg) c hc
  · intro hc
    have hginv : g⁻¹ ∈ Subgroup.normalizer (U : Set G) := by
      have : g ∈ Subgroup.normalizer (U : Set G) := by
        rw [Subgroup.mem_set_normalizer_iff]; exact hg
      exact (Subgroup.normalizer (U : Set G)).inv_mem this
    have := key g⁻¹ hginv _ hc
    simpa [mul_assoc] using this

theorem not_dvd_card_of_elemAbelian_sq_normalizes [Finite G] {X : Subgroup G}
    (hX : ∀ q : ℕ, q.Prime → q ≠ 2 → pRank q X ≤ 2) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup G} (hPX : P ≤ X) (hP : IsElemAbelian p P) (hPcard : Nat.card P = p ^ 2)
    {H : Subgroup G} (hHX : H ≤ X) (hPH : P ≤ Subgroup.normalizer (H : Set G))
    (hdisj : P ⊓ H = ⊥) : ¬ p ∣ Nat.card H := by
  intro hdvd
  obtain ⟨x, hxH, hxord, hxc⟩ := exists_orderOf_eq_of_isPGroup_normalizer (isPGroup_of_isElemAbelian hP) hPH hdvd
  have hxP : x ∉ P := by
    intro hxP
    have : x ∈ P ⊓ H := ⟨hxP, hxH⟩
    rw [hdisj, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hxord
    exact hp.out.one_lt.ne hxord
  obtain ⟨hA, hAcard⟩ := exists_elemAbelian_sup_zpowers hP hxord
    (fun e he => (Subgroup.mem_centralizer_iff.1 hxc e he)) hxP
  have hAX : P ⊔ Subgroup.zpowers x ≤ X :=
    sup_le hPX ((Subgroup.zpowers_le).2 (hHX hxH))
  have h3 : 3 ≤ pRank p X := le_pRank hp.out hAX hA (k := 3) (by rw [hAcard, hPcard]; ring)
  have h4 := hX p hp.out hp2
  omega

theorem not_dvd_card_centralizer_of_faithful [Finite G] {X : Subgroup G}
    (hX : ∀ q : ℕ, q.Prime → q ≠ 2 → pRank q X ≤ 2) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup G} (hPX : P ≤ X) (hP : IsElemAbelian p P) (hPcard : Nat.card P = p ^ 2)
    {U : Subgroup G} (_hUX : U ≤ X) (_hU : IsElemAbelian 2 U)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hfaith : P ⊓ Subgroup.centralizer (U : Set G) = ⊥) :
    ¬ p ∣ Nat.card ↥(X ⊓ Subgroup.centralizer (U : Set G)) := by
  refine not_dvd_card_of_elemAbelian_sq_normalizes hX hp2 hPX hP hPcard inf_le_left ?_ ?_
  · intro g hg
    have h1 : g ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer (hPX hg)
    have h2 := normalizer_le_normalizer_centralizer U (hPU hg)
    rw [Subgroup.mem_set_normalizer_iff] at h1 h2 ⊢
    intro c
    simp only [SetLike.mem_coe, Subgroup.mem_inf] at *
    rw [h1 c, h2 c]
  · rw [← hfaith]
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hPX h.1, h.2⟩⟩

end CFSG.Quasithin
