module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneSix
import CFSG.LocalAnalysis.StandardType.ZS.MovedAction
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

public section

namespace CFSG.StandardType.ZS

namespace LemmaOneSixSetting

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U} {l : ℕ}

private theorem reflGen_closure_insert {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {g : U ≃ₗ[ZMod p] U} (hH : ReflGen p H) (hg : IsRefl p g) :
    ReflGen p (Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U)))) := by
  let X : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U)))
  change ReflGen p X
  have hHgen : H = Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ H ∧ IsRefl p t} := hH
  have hgX : g ∈ X := Subgroup.subset_closure (Set.mem_insert g _)
  have hHX : H ≤ X := fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem g hh)
  have hSH : H ≤ Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ X ∧ IsRefl p t} := by
    rw [hHgen]
    refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨htH, htr⟩
    exact Subgroup.subset_closure ⟨hHX htH, htr⟩
  change X = Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ X ∧ IsRefl p t}
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun _ hx => hx.1)
  change Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))) ≤ _
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hxH
  · exact Subgroup.subset_closure ⟨hgX, hg⟩
  · exact hSH hxH

theorem kerSection_inf_eq_bot (hS : LemmaOneSixSetting F H a l) : kerSection F ⊓ H = ⊥ := by
  have hHF : H ≤ F := by
    rw [hS.eq_closure]
    intro h hh
    exact Subgroup.subset_closure (Set.mem_insert_of_mem a hh)
  have hVFle : HardMathSupport.Kantor79.commutatorSpace H ≤
      HardMathSupport.Kantor79.commutatorSpace F := by
    rw [commutatorSpace_le_iff]
    intro h hh v
    exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hHF hh) ⟨v, rfl⟩
  have hVcle : centralizerSpace F ≤ centralizerSpace H := by
    intro v hv
    rw [mem_centralizerSpace] at hv ⊢
    intro h hh
    exact hv h (hHF hh)
  refine le_bot_iff.mp ?_
  intro t ht
  rw [Subgroup.mem_inf] at ht
  obtain ⟨htT, htH⟩ := ht
  obtain ⟨-, htV⟩ := mem_kerSection_iff.mp htT
  have hfixVH : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H, t v = v := by
    intro v hv
    have h1 : t v - v ∈ centralizerSpace F := htV v (hVFle hv)
    have h2 : t v - v ∈ centralizerSpace H := hVcle h1
    have h3 : t v - v ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      (HardMathSupport.Kantor79.commutatorSpace H).sub_mem
        (apply_mem_commutatorSpace htH hv) hv
    have h4 : t v - v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
      ⟨h3, h2⟩
    rw [hS.splitSupport.1.inf_eq_bot] at h4
    exact sub_eq_zero.mp (by simpa using h4)
  have hfixVc : ∀ v ∈ centralizerSpace H, t v = v := fun v hv =>
    (mem_centralizerSpace.mp hv) t htH
  rw [Subgroup.mem_bot]
  ext v
  change t v = v
  have hv : v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊔ centralizerSpace H := by
    rw [hS.splitSupport.1.sup_eq_top]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hv
  rw [← hxy, map_add, hfixVH x hx, hfixVc y hy]

theorem commute_of_conj_mem (hS : LemmaOneSixSetting F H a l) {t h : U ≃ₗ[ZMod p] U}
    (ht : t ∈ kerSection F) (hh : h ∈ H) (hth : t * h * t⁻¹ ∈ H) : Commute t h := by
  have hHF : H ≤ F := by
    rw [hS.eq_closure]
    intro x hx
    exact Subgroup.subset_closure (Set.mem_insert_of_mem a hx)
  have hcH : t * h * t⁻¹ * h⁻¹ ∈ H := H.mul_mem hth (H.inv_mem hh)
  have hcT : t * h * t⁻¹ * h⁻¹ ∈ kerSection F := by
    have h1 : h * t⁻¹ * h⁻¹ ∈ kerSection F :=
      conj_mem_kerSection (hHF hh) ((kerSection F).inv_mem ht)
    have h2 : t * (h * t⁻¹ * h⁻¹) ∈ kerSection F := (kerSection F).mul_mem ht h1
    simpa only [mul_assoc] using h2
  have hc : t * h * t⁻¹ * h⁻¹ = 1 := by
    have hmem : t * h * t⁻¹ * h⁻¹ ∈ kerSection F ⊓ H := ⟨hcT, hcH⟩
    rw [kerSection_inf_eq_bot hS] at hmem
    simpa using hmem
  exact commutatorElement_eq_one_iff_commute.mp hc

theorem orderOf_mul_dvd_orderOf_conj_mul (hS : LemmaOneSixSetting F H a l)
    {t x y : U ≃ₗ[ZMod p] U} (ht : t ∈ kerSection F) (hx : x ∈ H) (hy : y ∈ H) :
    orderOf (x * y) ∣ orderOf (t * x * t⁻¹ * y) := by
  have hHF : H ≤ F := by
    rw [hS.eq_closure]
    intro h hh
    exact Subgroup.subset_closure (Set.mem_insert_of_mem a hh)
  set g : U ≃ₗ[ZMod p] U := x * y with hg
  set s : U ≃ₗ[ZMod p] U := t * (x * t⁻¹ * x⁻¹) with hs
  have hsT : s ∈ kerSection F := by
    have h1 : x * t⁻¹ * x⁻¹ ∈ kerSection F :=
      conj_mem_kerSection (hHF hx) ((kerSection F).inv_mem ht)
    simpa [hs] using (kerSection F).mul_mem ht h1
  have hgF : g ∈ F := hHF (H.mul_mem hx hy)
  have hgH : g ∈ H := H.mul_mem hx hy
  have hsg : s * g = t * x * t⁻¹ * y := by
    rw [hs, hg]; group
  have key : ∀ n, ∃ sₙ ∈ kerSection F, (s * g) ^ n = sₙ * g ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, (kerSection F).one_mem, by simp⟩
    | succ n ih =>
        obtain ⟨sₙ, hsₙ, ih⟩ := ih
        refine ⟨sₙ * (g ^ n * s * (g ^ n)⁻¹), ?_, ?_⟩
        · exact (kerSection F).mul_mem hsₙ (conj_mem_kerSection (F.pow_mem hgF n) hsT)
        · calc (s * g) ^ (n + 1) = (s * g) ^ n * (s * g) := pow_succ _ _
            _ = (sₙ * g ^ n) * (s * g) := by rw [ih]
            _ = (sₙ * (g ^ n * s * (g ^ n)⁻¹)) * g ^ (n + 1) := by group
  set k : ℕ := orderOf (s * g) with hk
  obtain ⟨sₖ, hsₖ, hsk⟩ := key k
  have h1 : sₖ * g ^ k = 1 := by
    rw [← hsk, pow_orderOf_eq_one]
  have hgpow : g ^ k = sₖ⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  have hgkT : g ^ k ∈ kerSection F := by
    rw [hgpow]
    exact (kerSection F).inv_mem hsₖ
  have hgkH : g ^ k ∈ H := H.pow_mem hgH k
  have hgk1 : g ^ k = 1 := by
    have hmem : g ^ k ∈ kerSection F ⊓ H := ⟨hgkT, hgkH⟩
    rw [kerSection_inf_eq_bot hS] at hmem
    simpa using hmem
  have hk1 : orderOf g ∣ k := orderOf_dvd_of_pow_eq_one hgk1
  rw [hk] at hk1
  rwa [hg, hsg] at hk1

private def invariantSubgroup (Y : Submodule (ZMod p) U) :
    Subgroup (U ≃ₗ[ZMod p] U) where
  carrier := {x | (∀ y ∈ Y, x y ∈ Y) ∧ (∀ y ∈ Y, x⁻¹ y ∈ Y)}
  one_mem' := ⟨fun y hy => by simpa using hy, fun y hy => by simpa using hy⟩
  mul_mem' := by
    rintro x z ⟨hx1, hx2⟩ ⟨hz1, hz2⟩
    refine ⟨fun y hy => hx1 (z y) (hz1 y hy), fun y hy => ?_⟩
    have hmul : (x * z)⁻¹ y = z⁻¹ (x⁻¹ y) := by
      rw [mul_inv_rev, LinearEquiv.mul_apply]
    rw [hmul]
    exact hz2 (x⁻¹ y) (hx2 y hy)
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx2, fun y hy => by simpa using hx1 y hy⟩

private theorem invariantSubgroup_mem_of_maps [Module.Finite (ZMod p) U]
    {Y : Submodule (ZMod p) U} {g : U ≃ₗ[ZMod p] U} (hcon : ∀ y ∈ Y, g y ∈ Y) :
    g ∈ invariantSubgroup Y := by
  refine ⟨hcon, fun y hy => ?_⟩
  have hle : Y.map (g : U →ₗ[ZMod p] U) ≤ Y := by
    rintro w ⟨v, hv, rfl⟩
    exact hcon v hv
  have heq : Y.map (g : U →ₗ[ZMod p] U) = Y :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq g Y)
  have hy' : y ∈ Y.map (g : U →ₗ[ZMod p] U) := heq.symm ▸ hy
  obtain ⟨w, hw, hwg⟩ := hy'
  rw [← hwg]
  simpa using hw

private theorem exists_not_mem_of_not_mem_le_F (hS : LemmaOneSixSetting F H a l)
    {g : U ≃ₗ[ZMod p] U} (hgF : g ∈ F) :
    H ≤ F ∧ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))) ≤ F := by
  have hHF : H ≤ F := by
    rw [hS.eq_closure]
    intro h hh
    exact Subgroup.subset_closure (Set.mem_insert_of_mem a hh)
  refine ⟨hHF, ?_⟩
  refine (Subgroup.closure_le F).mpr ?_
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hxH
  · exact hgF
  · exact hHF hxH

private theorem exists_not_mem_of_not_mem_X (hS : LemmaOneSixSetting F H a l)
    {g : U ≃ₗ[ZMod p] U} (hgF : g ∈ F) (hg : IsRefl p g) (hgH : g ∉ H) :
    H < Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))) ∧
      Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))) ≤ F ∧
      ReflGen p (Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U)))) := by
  let X : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U)))
  obtain ⟨hHF, hXF⟩ := exists_not_mem_of_not_mem_le_F hS hgF
  have hHleX : H ≤ X := fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem g hh)
  have hgX : g ∈ X := Subgroup.subset_closure (Set.mem_insert g _)
  have hHX : H < X := lt_of_le_of_ne hHleX (by
    intro heq
    apply hgH
    rw [heq]
    exact hgX)
  have hXgen : ReflGen p X := reflGen_closure_insert hS.reflGen hg
  exact ⟨hHX, hXF, hXgen⟩

private theorem exists_not_mem_of_not_mem_inv [Module.Finite (ZMod p) U]
    {Y : Submodule (ZMod p) U} (hY : ∀ h ∈ H, ∀ y ∈ Y, h y ∈ Y)
    {g : U ≃ₗ[ZMod p] U} (hcon : ∀ y ∈ Y, g y ∈ Y) :
    ∀ x ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), ∀ y ∈ Y, x y ∈ Y := by
  let X : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U)))
  have hHS : H ≤ invariantSubgroup Y := fun h hh =>
    ⟨fun y hy => hY h hh y hy, fun y hy => hY h⁻¹ (H.inv_mem hh) y hy⟩
  have hgS : g ∈ invariantSubgroup Y := invariantSubgroup_mem_of_maps hcon
  have hXS : X ≤ invariantSubgroup Y := (Subgroup.closure_le _).mpr (by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hxH
    · exact hgS
    · exact hHS hxH)
  intro x hx y hy
  exact (hXS hx).1 y hy

theorem exists_not_mem_of_not_mem (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {Y : Submodule (ZMod p) U}
    (hY : ∀ h ∈ H, ∀ y ∈ Y, h y ∈ Y) (haY : ∃ y ∈ Y, a y ∉ Y) {g : U ≃ₗ[ZMod p] U}
    (hgF : g ∈ F) (hg : IsRefl p g) (hgH : g ∉ H) : ∃ y ∈ Y, g y ∉ Y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hHX, hXF, hXgen⟩ := exists_not_mem_of_not_mem_X hS hgF hg hgH
  have hYinv : ∀ x ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), ∀ y ∈ Y, x y ∈ Y :=
    exists_not_mem_of_not_mem_inv hY hcon
  have hFfix : ∀ f ∈ F, ∀ y ∈ Y, f y ∈ Y := hS.invariant_of_lt hp hHX hXF hXgen hYinv
  obtain ⟨y, hy, hay⟩ := haY
  have haF : a ∈ F := by
    rw [hS.eq_closure]
    exact Subgroup.subset_closure (Set.mem_insert a _)
  exact hay (hFfix a haF y hy)

private theorem eq_self_of_maps_movedSpace_of_isRefl_ne (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (hG : QTwoLin.TransvectionFree G) {b r : U ≃ₗ[ZMod p] U} (hbG : b ∈ G) (hrG : r ∈ G)
    (hb : IsRefl p b) (hr : IsRefl p r) (hrne : r ≠ b)
    (hle : HardMathSupport.Kantor79.movedSpace b ≤
      (HardMathSupport.Kantor79.movedSpace b).comap (r : U →ₗ[ZMod p] U)) :
    ∀ w ∈ HardMathSupport.Kantor79.movedSpace b, r w = w := by
  intro w hw
  by_contra hne
  have hu : r w - w ≠ 0 := sub_ne_zero.mpr hne
  have hu_b : r w - w ∈ HardMathSupport.Kantor79.movedSpace b :=
    (HardMathSupport.Kantor79.movedSpace b).sub_mem (hle hw) hw
  have hu_r : r w - w ∈ HardMathSupport.Kantor79.movedSpace r := ⟨w, rfl⟩
  have hspan : HardMathSupport.Kantor79.movedSpace b =
      Submodule.span (ZMod p) {r w - w} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hb.2 hu_b hu
  have hle' : HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.movedSpace r := by
    rw [hspan]
    exact Submodule.span_le.mpr (by rintro x rfl; exact hu_r)
  have heq : HardMathSupport.Kantor79.movedSpace b =
      HardMathSupport.Kantor79.movedSpace r :=
    Submodule.eq_of_le_of_finrank_eq hle' (by
      have hb2' : Module.finrank (ZMod p)
          (HardMathSupport.Kantor79.movedSpace b) = 1 := hb.2
      have hr2' : Module.finrank (ZMod p)
          (HardMathSupport.Kantor79.movedSpace r) = 1 := hr.2
      rw [hb2', hr2'])
  exact hrne (eq_of_movedSpace_eq hp hG hbG hrG hb hr heq).symm

private abbrev Dsubgroup (H : Subgroup (U ≃ₗ[ZMod p] U)) (a : U ≃ₗ[ZMod p] U) :
    Subgroup (U ≃ₗ[ZMod p] U) := H ⊔ H.map (MulAut.conj a)

private theorem conj_not_mem_centralizer_hhab (hS : LemmaOneSixSetting F H a l)
    {b : U ≃ₗ[ZMod p] U}
    (habH : a * b * a ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U))) :
    ∀ h ∈ H, (a * h * a⁻¹) * b = b * (a * h * a⁻¹) := by
  have ha2 : a * a = 1 := hS.isRefl.1
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  intro h hh
  have h1 : h * (a * b * a) = (a * b * a) * h :=
    (Subgroup.mem_centralizer_iff.mp habH) h hh
  have h2 : a * (h * (a * b * a)) = b * a * h := by
    calc a * (h * (a * b * a)) = a * ((a * b * a) * h) := by rw [h1]
      _ = (a * a) * b * a * h := by group
      _ = b * a * h := by rw [ha2, one_mul]
  have h3 : (a * h * a) * b = b * (a * h * a) := by
    have hL : (a * h * a) * b = a * (h * (a * b * a)) * a := by
      calc (a * h * a) * b = (a * h * a) * (b * (a * a)) := by rw [ha2, mul_one]
        _ = a * (h * (a * b * a)) * a := by group
    calc (a * h * a) * b = a * (h * (a * b * a)) * a := hL
      _ = (b * a * h) * a := by rw [h2]
      _ = b * (a * h * a) := by group
  rw [show a⁻¹ = a from ha_inv]
  exact h3

private theorem conj_not_mem_centralizer_D_le (hS : LemmaOneSixSetting F H a l)
    {b : U ≃ₗ[ZMod p] U}
    (hhab : ∀ h ∈ H, (a * h * a⁻¹) * b = b * (a * h * a⁻¹))
    (hbH : b ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U))) :
    Dsubgroup H a ≤ F ∧
      Dsubgroup H a ≤ Subgroup.centralizer ({b} : Set (U ≃ₗ[ZMod p] U)) := by
  have haF : a ∈ F := by
    rw [hS.eq_closure]
    exact Subgroup.subset_closure (Set.mem_insert a _)
  have hHF : H ≤ F := by
    rw [hS.eq_closure]
    intro h hh
    exact Subgroup.subset_closure (Set.mem_insert_of_mem a hh)
  have hDF : Dsubgroup H a ≤ F := by
    refine sup_le hHF ?_
    rintro x ⟨h, hh, rfl⟩
    change a * h * a⁻¹ ∈ F
    exact F.mul_mem (F.mul_mem haF (hHF hh)) (F.inv_mem haF)
  have hDcen : Dsubgroup H a ≤ Subgroup.centralizer ({b} : Set (U ≃ₗ[ZMod p] U)) := by
    refine sup_le ?_ ?_
    · intro h hh
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ((Subgroup.mem_centralizer_iff.mp hbH) h hh).symm
    · rintro x ⟨h, hh, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (hhab h hh).symm
  exact ⟨hDF, hDcen⟩

private theorem conj_not_mem_centralizer_D_lt
    (haV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace H,
      a v ∉ HardMathSupport.Kantor79.commutatorSpace H) :
    H < Dsubgroup H a := by
  refine lt_of_le_of_ne le_sup_left ?_
  intro hHeq
  have hDH : Dsubgroup H a ≤ H := le_of_eq hHeq.symm
  obtain ⟨v, hv, hav⟩ := haV
  apply hav
  have hle : HardMathSupport.Kantor79.commutatorSpace H ≤
      (HardMathSupport.Kantor79.commutatorSpace H).comap (a : U →ₗ[ZMod p] U) := by
    conv_lhs => rw [HardMathSupport.Kantor79.commutatorSpace]
    rw [Submodule.span_le]
    rintro u ⟨h, hh, w, rfl⟩
    have hconjH : MulAut.conj a h ∈ H :=
      hDH (Subgroup.mem_sup_right ⟨h, hh, rfl⟩)
    have hgen : (MulAut.conj a h) (a w) - a w ∈
        HardMathSupport.Kantor79.commutatorSpace H :=
      Submodule.subset_span ⟨MulAut.conj a h, hconjH, a w, rfl⟩
    show a (h w - w) ∈ HardMathSupport.Kantor79.commutatorSpace H
    rw [map_sub]
    have heq : a (h w) - a w = (MulAut.conj a h) (a w) - a w := by
      rw [MulAut.conj_apply]
      simp [LinearEquiv.mul_apply]
    rw [heq]
    exact hgen
  exact hle hv

private theorem conj_not_mem_centralizer_D_gen (hS : LemmaOneSixSetting F H a l) :
    ReflGen p (Dsubgroup H a) := by
  have hHgen : H = Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ H ∧ IsRefl p t} := hS.reflGen
  change Dsubgroup H a = Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ Dsubgroup H a ∧ IsRefl p t}
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun _ hx => hx.1)
  refine sup_le ?_ ?_
  · conv_lhs => rw [hHgen]
    exact Subgroup.closure_mono (fun t ht => ⟨Subgroup.mem_sup_left ht.1, ht.2⟩)
  · conv_lhs => rw [hHgen, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨r, ⟨hrH, hrr⟩, rfl⟩
    exact Subgroup.subset_closure
      ⟨Subgroup.mem_sup_right ⟨r, hrH, rfl⟩, by
        simpa [MulAut.conj_apply] using IsRefl.conj hrr a⟩

private theorem conj_not_mem_centralizer_hbF {b : U ≃ₗ[ZMod p] U}
    (hbW : ∃ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F,
      b w ∉ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) :
    b ∉ F := by
  intro hbF
  obtain ⟨w, hw, hbw⟩ := hbW
  rw [mem_centralizerSpace.mp hw.2 b hbF] at hbw
  exact hbw hw

private theorem conj_not_mem_centralizer_hfix_refl (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : QTwoLin.TransvectionFree G)
    (hFG : F ≤ G) {b : U ≃ₗ[ZMod p] U} (hbG : b ∈ G) (hb : IsRefl p b)
    (hbF : b ∉ F) (hDF : Dsubgroup H a ≤ F)
    (hDcen : Dsubgroup H a ≤ Subgroup.centralizer ({b} : Set (U ≃ₗ[ZMod p] U))) :
    ∀ r ∈ Dsubgroup H a, IsRefl p r →
      ∀ w ∈ HardMathSupport.Kantor79.movedSpace b, r w = w := by
  intro r hrD hr w hw
  have hrF : r ∈ F := hDF hrD
  have hrne : r ≠ b := fun heq => hbF (heq ▸ hrF)
  have hrG : r ∈ G := hFG hrF
  have hrb : b * r = r * b :=
    (Subgroup.mem_centralizer_iff.mp (hDcen hrD)) b (Set.mem_singleton b)
  have hle : HardMathSupport.Kantor79.movedSpace b ≤
      (HardMathSupport.Kantor79.movedSpace b).comap (r : U →ₗ[ZMod p] U) := by
    intro u hu
    obtain ⟨v, rfl⟩ := hu
    have hru : r (b v) = b (r v) := by
      have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hrb
      simpa [LinearEquiv.mul_apply] using h.symm
    show r (b v - v) ∈ HardMathSupport.Kantor79.movedSpace b
    rw [map_sub, hru]
    exact ⟨r v, rfl⟩
  exact eq_self_of_maps_movedSpace_of_isRefl_ne hp hG hbG hrG hb hr hrne hle w hw

private theorem conj_not_mem_centralizer_hDfix {b : U ≃ₗ[ZMod p] U}
    (hDgen : ReflGen p (Dsubgroup H a))
    (hfix_refl : ∀ r ∈ Dsubgroup H a, IsRefl p r →
      ∀ w ∈ HardMathSupport.Kantor79.movedSpace b, r w = w) :
    ∀ d ∈ Dsubgroup H a, ∀ w ∈ HardMathSupport.Kantor79.movedSpace b, d w = w := by
  have hclosure : Dsubgroup H a =
      Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ Dsubgroup H a ∧ IsRefl p t} := hDgen
  intro d hd
  rw [hclosure] at hd
  induction hd using Subgroup.closure_induction with
  | mem r hr => exact hfix_refl r hr.1 hr.2
  | one => intro w hw; rfl
  | mul x y hx hy ihx ihy =>
      intro w hw
      rw [LinearEquiv.mul_apply, ihy w hw, ihx w hw]
  | inv x hx ihx =>
      intro w hw
      calc x⁻¹ w = x⁻¹ (x w) := by rw [ihx w hw]
        _ = w := LinearEquiv.symm_apply_apply x w

private theorem conj_not_mem_centralizer_hVbInv (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {b : U ≃ₗ[ZMod p] U}
    (hHD : H < Dsubgroup H a) (hDF : Dsubgroup H a ≤ F)
    (hDgen : ReflGen p (Dsubgroup H a))
    (hfix_refl : ∀ r ∈ Dsubgroup H a, IsRefl p r →
      ∀ w ∈ HardMathSupport.Kantor79.movedSpace b, r w = w) :
    ∀ f ∈ F, ∀ w ∈ HardMathSupport.Kantor79.movedSpace b,
      f w ∈ HardMathSupport.Kantor79.movedSpace b := by
  have hDfix : ∀ d ∈ Dsubgroup H a,
      ∀ w ∈ HardMathSupport.Kantor79.movedSpace b, d w = w :=
    conj_not_mem_centralizer_hDfix hDgen hfix_refl
  have hDinv : ∀ d ∈ Dsubgroup H a, ∀ w ∈ HardMathSupport.Kantor79.movedSpace b,
      d w ∈ HardMathSupport.Kantor79.movedSpace b := fun d hd w hw => by
    rw [hDfix d hd w hw]
    exact hw
  exact hS.invariant_of_lt hp hHD hDF hDgen hDinv

private theorem conj_not_mem_centralizer_hVbleVcF (hS : LemmaOneSixSetting F H a l)
    {b : U ≃ₗ[ZMod p] U}
    (hfix_a : ∀ w ∈ HardMathSupport.Kantor79.movedSpace b, a w = w)
    (hfix_H : ∀ h ∈ H, ∀ w ∈ HardMathSupport.Kantor79.movedSpace b, h w = w) :
    HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace F := by
  intro w hw
  rw [mem_centralizerSpace]
  intro f hf
  have hf' : f ∈ Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))) := by
    rw [← hS.eq_closure]
    exact hf
  refine Subgroup.closure_induction (p := fun x _ => x w = w) ?_ ?_ ?_ ?_ hf'
  · rintro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hgH
    · exact hfix_a w hw
    · exact hfix_H g hgH w hw
  · rfl
  · rintro x y hx hy ihx ihy
    rw [LinearEquiv.mul_apply, ihy, ihx]
  · rintro x hx ihx
    calc x⁻¹ w = x⁻¹ (x w) := by rw [ihx]
      _ = w := LinearEquiv.symm_apply_apply x w

private theorem conj_not_mem_centralizer_hVcleVF (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hl : l + 2 = Module.finrank (ZMod p) U) :
    centralizerSpace F ≤ HardMathSupport.Kantor79.commutatorSpace F := by
  have hsup_eq : HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F =
      HardMathSupport.Kantor79.commutatorSpace F := by
    refine Eq.symm (Submodule.eq_of_le_of_finrank_eq le_sup_left ?_)
    rw [hS.finrank_sup_eq hp, hS.finrank_eq]
    omega
  rw [← hsup_eq]
  exact le_sup_right

private theorem conj_not_mem_centralizer_hVbW (hS : LemmaOneSixSetting F H a l)
    [Module.Finite (ZMod p) U]
    {b : U ≃ₗ[ZMod p] U} (hb : IsRefl p b)
    (hVbleVcF : HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace F)
    (hVcleVF : centralizerSpace F ≤ HardMathSupport.Kantor79.commutatorSpace F) :
    HardMathSupport.Kantor79.movedSpace b ≤
        HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ∧
      HardMathSupport.Kantor79.movedSpace b =
        HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F := by
  have hVb_le_W : HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F :=
    le_inf (le_trans hVbleVcF hVcleVF) hVbleVcF
  have hVbW : HardMathSupport.Kantor79.movedSpace b =
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F :=
    Submodule.eq_of_le_of_finrank_eq hVb_le_W (by
      have hb2' : Module.finrank (ZMod p)
          (HardMathSupport.Kantor79.movedSpace b) = 1 := hb.2
      rw [hb2']
      exact (hS.degenerate.1).symm)
  exact ⟨hVb_le_W, hVbW⟩

theorem conj_not_mem_centralizer (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hl : l + 2 = Module.finrank (ZMod p) U)
    (haV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace H,
      a v ∉ HardMathSupport.Kantor79.commutatorSpace H)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : QTwoLin.TransvectionFree G) (hFG : F ≤ G)
    {b : U ≃ₗ[ZMod p] U} (hbG : b ∈ G) (hb : IsRefl p b)
    (hbW : ∃ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F,
      b w ∉ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    (hbH : b ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U))) :
    a * b * a ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)) := by
  intro habH
  have ha2 : a * a = 1 := hS.isRefl.1
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haF : a ∈ F := by
    rw [hS.eq_closure]
    exact Subgroup.subset_closure (Set.mem_insert a _)
  have hhab : ∀ h ∈ H, (a * h * a⁻¹) * b = b * (a * h * a⁻¹) :=
    conj_not_mem_centralizer_hhab hS habH
  obtain ⟨hDF, hDcen⟩ := conj_not_mem_centralizer_D_le hS hhab hbH
  have hHD : H < Dsubgroup H a := conj_not_mem_centralizer_D_lt haV
  have hDgen : ReflGen p (Dsubgroup H a) := conj_not_mem_centralizer_D_gen hS
  have hbF : b ∉ F := conj_not_mem_centralizer_hbF hbW
  have hfix_refl : ∀ r ∈ Dsubgroup H a, IsRefl p r →
      ∀ w ∈ HardMathSupport.Kantor79.movedSpace b, r w = w :=
    conj_not_mem_centralizer_hfix_refl hp hG hFG hbG hb hbF hDF hDcen
  have hVbInv : ∀ f ∈ F, ∀ w ∈ HardMathSupport.Kantor79.movedSpace b,
      f w ∈ HardMathSupport.Kantor79.movedSpace b :=
    conj_not_mem_centralizer_hVbInv hS hp hHD hDF hDgen hfix_refl
  have hfix_a : ∀ w ∈ HardMathSupport.Kantor79.movedSpace b, a w = w :=
    eq_self_of_maps_movedSpace_of_isRefl_ne hp hG hbG (hFG haF) hb hS.isRefl
      (fun heq => hbF (heq ▸ haF)) (hVbInv a haF)
  have hfix_H : ∀ h ∈ H, ∀ w ∈ HardMathSupport.Kantor79.movedSpace b, h w = w := by
    intro h hh w hw
    exact conj_not_mem_centralizer_hDfix hDgen hfix_refl
      h (Subgroup.mem_sup_left hh) w hw
  have hVbleVcF : HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace F :=
    conj_not_mem_centralizer_hVbleVcF hS hfix_a hfix_H
  have hVcleVF : centralizerSpace F ≤ HardMathSupport.Kantor79.commutatorSpace F :=
    conj_not_mem_centralizer_hVcleVF hS hp hl
  obtain ⟨hVb_le_W, hVbW⟩ :=
    conj_not_mem_centralizer_hVbW hS hb hVbleVcF hVcleVF
  obtain ⟨w, hw, hbw⟩ := hbW
  refine hbw ?_
  rw [show b w = w + (b w - w) by abel]
  exact (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F).add_mem hw
    (hVbW ▸ ⟨w, rfl⟩)

end LemmaOneSixSetting

end CFSG.StandardType.ZS
