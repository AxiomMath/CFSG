module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.StandardType CFSG.StandardType.GGOppRadSpU CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.QuasithinUnique.B113Lie.Sp

private lemma mem_ggCenterOf_iff' {G : Type} [Group G] (Y : Subgroup G) (x : G) :
    x ∈ ggCenterOf Y ↔ x ∈ Y ∧ ∀ y ∈ Y, y * x = x * y := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, fun y hy => congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨y, hy⟩)⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (h y y.2), rfl⟩

private lemma mem_suStabFix_iff {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {g : ↥(SU (unitaryInvolution F 2 f) n)} :
    g ∈ suStabFix hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr) ↔
      g ∈ suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr) ∧
        ∀ y ∈ (suH hc n).perp (Submodule.span F {v, w}),
          natRep (SU (unitaryInvolution F 2 f) n) g y = y :=
  Iff.rfl

private lemma sub_mem_span_singleton_of_commute_eichler
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {H : Type*} [Group H] {B : ReflForm K V} {ρ : H →* Module.End K V}
    (hρ : IsIsometric B ρ) {x u : V} (hx : x ≠ 0) {d : K} {g s : H}
    (hge : ρ g x = x)
    (hs : ∀ v, ρ s v = v + B.β x v • (u + d • x) + B.β u v • x)
    (hgs : g * s = s * g) : ρ g u - u ∈ K ∙ x := by
  obtain ⟨v₀, hv₀⟩ := CFSG.QuasithinUnique.B113Lie.Sp.exists_β_eq_one (F := B) hx
  have h1 := rep_conj_apply hρ hs g v₀
  rw [eq_of_commute hgs, hs, hge, map_add, map_smul, hge, hv₀, one_smul, one_smul] at h1
  have h2 : (u + d • x) + B.β u v₀ • x = (ρ g u + d • x) + B.β (ρ g u) v₀ • x :=
    add_left_cancel (by simpa only [add_assoc] using h1)
  have h3 : u + B.β u v₀ • x = ρ g u + B.β (ρ g u) v₀ • x := by
    have h2' : (u + B.β u v₀ • x) + d • x
        = (ρ g u + B.β (ρ g u) v₀ • x) + d • x := by
      rw [show (u + d • x) + B.β u v₀ • x
            = (u + B.β u v₀ • x) + d • x by abel] at h2
      rw [show (ρ g u + d • x) + B.β (ρ g u) v₀ • x
            = (ρ g u + B.β (ρ g u) v₀ • x) + d • x by abel] at h2
      exact h2
    exact add_right_cancel h2'
  rw [Submodule.mem_span_singleton]
  refine ⟨B.β u v₀ - B.β (ρ g u) v₀, ?_⟩
  rw [sub_smul, sub_eq_sub_iff_add_eq_add, add_comm (B.β u v₀ • x) u]
  exact h3

theorem ggCenterOf_suStabRad_eq {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    ggCenterOf (suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr)) =
      suStabFix hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr) := by
  let A : Submodule F (Fin n → F) := Submodule.span F {v, w}
  let hA : (suH hc n).IsTotallyIsotropic A := suFrame_isTotallyIsotropic hfr
  let B : ReflForm F (Fin n → F) := suH hc n
  let ρ : ↥(SU (unitaryInvolution F 2 f) n) →* Module.End F (Fin n → F) :=
    natRep (SU (unitaryInvolution F 2 f) n)
  have hρ : IsIsometric B ρ :=
    isIsometric_natRep_SU (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) n
  have hρS : IsIsometric (suH hc n) ρ := hρ
  apply le_antisymm
  ·
    intro g hg
    rw [mem_ggCenterOf_iff'] at hg
    obtain ⟨hgR, hgcent⟩ := hg
    have hgR' : g ∈ rad (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) A hA := hgR
    have hgfixA : ∀ a ∈ A, ρ g a = a := (mem_rad.mp hgR').1
    rw [mem_suStabFix_iff hfr]
    obtain ⟨hvw', hwv', ⟨hvv, hww, _, _⟩, ⟨_, _, hww', _⟩⟩ := hfr
    have hvA : v ∈ A := Submodule.subset_span (by simp)
    have hwA : w ∈ A := Submodule.subset_span (by simp)
    have hv_ne : v ≠ 0 := by
      intro h0
      have h1 := hvw'
      rw [h0, (suH hc n).β_zero_left] at h1
      exact zero_ne_one h1
    have hw_ne : w ≠ 0 := by
      intro h0
      have h1 := hwv'
      rw [h0, (suH hc n).β_zero_left] at h1
      exact zero_ne_one h1
    refine ⟨hgR, ?_⟩
    intro z hz
    have hzz : unitaryInvolution F 2 f (B.β z z) = B.β z z :=
      (suForm_symm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) z z).symm
    obtain ⟨c, hct⟩ := exists_add_unitaryInvolution_eq hc hzz
    have hvz : B.β v z = 0 := (B.mem_perp.mp hz) v hvA
    have hwz : B.β w z = 0 := (B.mem_perp.mp hz) w hwA
    obtain ⟨Ev, hEv⟩ := exists_SU_eichler (unitaryInvolution F 2 f)
      (unitaryInvolution_involutive hc) hvv hvz hct
    have hEvB : ∀ y, ρ Ev y = y + B.β v y • (z + c • v) + B.β z y • v := hEv
    have hEvR : Ev ∈ suStabRad hc n A hA := by
      refine mem_rad.mpr ⟨?_, ?_⟩
      · intro a ha
        rw [hEvB a]
        have hva : B.β v a = 0 := (B.mem_perp.mp (hA ha)) v hvA
        have hza : B.β z a = 0 := B.refl a z ((B.mem_perp.mp hz) a ha)
        rw [hva, hza, zero_smul, zero_smul, add_zero, add_zero]
      · intro y hy
        rw [hEvB y]
        have hvy : B.β v y = 0 := (B.mem_perp.mp hy) v hvA
        rw [hvy, zero_smul, add_zero, add_sub_cancel_left]
        exact Submodule.smul_mem _ _ hvA
    have hgv : ρ g v = v := hgfixA v hvA
    have hδv : ρ g z - z ∈ F ∙ v :=
      sub_mem_span_singleton_of_commute_eichler hρ hv_ne hgv hEvB (hgcent Ev hEvR).symm
    obtain ⟨Ew, hEw⟩ := exists_SU_eichler (unitaryInvolution F 2 f)
      (unitaryInvolution_involutive hc) hww hwz hct
    have hEwB : ∀ y, ρ Ew y = y + B.β w y • (z + c • w) + B.β z y • w := hEw
    have hEwR : Ew ∈ suStabRad hc n A hA := by
      refine mem_rad.mpr ⟨?_, ?_⟩
      · intro a ha
        rw [hEwB a]
        have hwa : B.β w a = 0 := (B.mem_perp.mp (hA ha)) w hwA
        have hza : B.β z a = 0 := B.refl a z ((B.mem_perp.mp hz) a ha)
        rw [hwa, hza, zero_smul, zero_smul, add_zero, add_zero]
      · intro y hy
        rw [hEwB y]
        have hwy : B.β w y = 0 := (B.mem_perp.mp hy) w hwA
        rw [hwy, zero_smul, add_zero, add_sub_cancel_left]
        exact Submodule.smul_mem _ _ hwA
    have hgw : ρ g w = w := hgfixA w hwA
    have hδw : ρ g z - z ∈ F ∙ w :=
      sub_mem_span_singleton_of_commute_eichler hρ hw_ne hgw hEwB (hgcent Ew hEwR).symm
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hδv
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hδw
    have hpair_a : B.β (ρ g z - z) w' = B.σ a := by
      rw [← ha, B.smul_left, hvw', mul_one]
    have hpair_b : B.β (ρ g z - z) w' = 0 := by
      rw [← hb, B.smul_left, hww', mul_zero]
    have ha0 : a = 0 := by
      apply (map_eq_zero_iff B.σ B.σ.injective).mp
      rw [← hpair_a]
      exact hpair_b
    have hδ0 : ρ g z - z = 0 := by rw [← ha, ha0, zero_smul]
    exact sub_eq_zero.mp hδ0
  ·
    intro g hg
    rw [mem_suStabFix_iff hfr] at hg
    obtain ⟨hgR, hgFix⟩ := hg
    rw [mem_ggCenterOf_iff']
    refine ⟨hgR, ?_⟩
    intro q hq
    have hgR' : g ∈ rad (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) A hA := hgR
    have hqR' : q ∈ rad (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) A hA := hq
    have hgFixA : ∀ a ∈ A, ρ g a = a := (mem_rad.mp hgR').1
    have hqFixA : ∀ a ∈ A, ρ q a = a := (mem_rad.mp hqR').1
    set X : Module.End F (Fin n → F) := ρ g - 1 with hXdef
    set Y : Module.End F (Fin n → F) := ρ q - 1 with hYdef
    have hX_apply : ∀ v, X v = ρ g v - v := fun v => by
      rw [hXdef]
      simp only [LinearMap.sub_apply, Module.End.one_apply]
    have hY_apply : ∀ v, Y v = ρ q v - v := fun v => by
      rw [hYdef]
      simp only [LinearMap.sub_apply, Module.End.one_apply]
    have hgFixinv : ∀ z ∈ (suH hc n).perp A, ρ g⁻¹ z = z := by
      intro z hz
      have h1 := congrArg (ρ g⁻¹) (hgFix z hz)
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] at h1
      exact h1.symm
    have hX_perp : ∀ z ∈ (suH hc n).perp A, X z = 0 := fun z hz => by
      rw [hX_apply z, hgFix z hz, sub_self]
    have hY_A : ∀ a ∈ A, Y a = 0 := fun a ha => by
      rw [hY_apply a, hqFixA a ha, sub_self]
    have hY_perp : ∀ v, Y v ∈ (suH hc n).perp A := by
      intro v
      rw [(suH hc n).mem_perp]
      intro a ha
      have hqinv : q⁻¹ ∈ rad (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) A hA :=
        inv_mem hqR'
      have hqa : ρ q⁻¹ a = a := (mem_rad.mp hqinv).1 a ha
      have hiso := hρS q (ρ q⁻¹ a) v
      rw [rep_apply_inv_apply, hqa] at hiso
      rw [hY_apply v, (suH hc n).β_sub_right, hiso, sub_self]
    have hX_A : ∀ v, X v ∈ A := by
      intro v
      rw [← (suH hc n).perp_perp A]
      rw [(suH hc n).mem_perp]
      intro z hz
      have hiso := hρS g v (ρ g⁻¹ z)
      rw [rep_apply_inv_apply, hgFixinv z hz] at hiso
      exact (suH hc n).refl _ _
        (by rw [hX_apply v, (suH hc n).β_sub_left, hiso, sub_self])
    have hXY : X * Y = 0 := by
      refine LinearMap.ext fun v => ?_
      rw [Module.End.mul_apply, LinearMap.zero_apply]
      exact hX_perp (Y v) (hY_perp v)
    have hYX : Y * X = 0 := by
      refine LinearMap.ext fun v => ?_
      rw [Module.End.mul_apply, LinearMap.zero_apply]
      exact hY_A (X v) (hX_A v)
    have hρg : ρ g = 1 + X := by rw [hXdef]; abel
    have hρq : ρ q = 1 + Y := by rw [hYdef]; abel
    apply natRep_injective (SU (unitaryInvolution F 2 f) n)
    rw [map_mul, map_mul]
    calc ρ q * ρ g = (1 + Y) * (1 + X) := by rw [hρq, hρg]
      _ = 1 + X + Y := by
            rw [add_mul, one_mul, mul_add, mul_one, hYX, add_zero]
      _ = (1 + X) * (1 + Y) := by
            rw [add_mul, one_mul, mul_add, mul_one, hXY, add_zero]
            abel
      _ = ρ g * ρ q := by rw [hρg, hρq]

end CFSG.StandardType.LieKnownR2.Short
