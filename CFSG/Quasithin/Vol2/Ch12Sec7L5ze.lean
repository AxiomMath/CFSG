module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.Quasithin.Lift3

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Elem

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem mem_zpowers_two {e : W} (he : e ^ 2 = 1) {x : W} (hx : x ∈ Subgroup.zpowers e) :
    x = 1 ∨ x = e := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have he2 : e ^ (2 : ℤ) = 1 := by exact_mod_cast he
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, he2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, he2, one_zpow, one_mul, zpow_one]

theorem exists_compl (hW : ∀ w : W, w ^ 2 = 1) (P : Subgroup W) :
    ∃ C : Subgroup W, C ⊓ P = ⊥ ∧ C ⊔ P = ⊤ := by
  classical
  have : Finite (Subgroup W) :=
    Finite.of_injective (SetLike.coe : Subgroup W → Set W) SetLike.coe_injective
  let _ : Fintype (Subgroup W) := Fintype.ofFinite _
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun C : Subgroup W => C ⊓ P = ⊥)
    (fun C : Subgroup W => Nat.card C) ⟨⊥, by simp⟩
  have hCP : C ⊓ P = ⊥ := (Finset.mem_filter.mp hC).2
  refine ⟨C, hCP, ?_⟩
  by_contra hne
  obtain ⟨e, heCP⟩ : ∃ e : W, e ∉ C ⊔ P := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  have heC : e ∉ C := fun h => heCP (Subgroup.mem_sup_left h)
  have hC'P : (C ⊔ Subgroup.zpowers e) ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨c, hc, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx1
    rcases mem_zpowers_two (hW e) hb with hb1 | hb1
    · rw [hb1, mul_one] at hx2 ⊢
      have : c ∈ C ⊓ P := ⟨hc, hx2⟩
      rwa [hCP] at this
    · exfalso
      rw [hb1] at hx2
      apply heCP
      have : e = c⁻¹ * (c * e) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (C.inv_mem hc)) (Subgroup.mem_sup_right hx2)
  have hlt : C < C ⊔ Subgroup.zpowers e :=
    lt_of_le_of_ne le_sup_left fun h => heC (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
  have h1 := hmax _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC'P⟩)
  have h2 := Subgroup.card_lt_of_lt hlt
  omega

theorem exists_lift (hW : ∀ w : W, w ^ 2 = 1) (P : Subgroup W) (φ : MulAut (W ⧸ P)) :
    ∃ (g : MulAut W) (hg : P.map g.toMonoidHom = P), QuotientGroup.congr P P g hg = φ := by
  classical
  obtain ⟨C, hCP, hCPt⟩ := exists_compl hW P
  set mkC : ↥C →* W ⧸ P := (QuotientGroup.mk' P).comp C.subtype with hmkC
  have hmkC_inj : Function.Injective mkC := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hcP : (c : W) ∈ P := (QuotientGroup.eq_one_iff _).mp hc
    have : (c : W) ∈ C ⊓ P := ⟨c.2, hcP⟩
    rw [hCP, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hmkC_surj : Function.Surjective mkC := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective P q
    have hw : w ∈ C ⊔ P := hCPt ▸ Subgroup.mem_top w
    obtain ⟨c, hc, p, hp, rfl⟩ := Subgroup.mem_sup.mp hw
    refine ⟨⟨c, hc⟩, ?_⟩
    show QuotientGroup.mk' P c = QuotientGroup.mk' P (c * p)
    rw [map_mul, show QuotientGroup.mk' P p = 1 from (QuotientGroup.eq_one_iff p).mpr hp, mul_one]
  set σ : ↥C ≃* W ⧸ P := MulEquiv.ofBijective mkC ⟨hmkC_inj, hmkC_surj⟩ with hσ
  set mulH : ↥C × ↥P →* W :=
    (C.subtype.comp (MonoidHom.fst _ _)) * (P.subtype.comp (MonoidHom.snd _ _)) with hmulH
  have hmulH_apply : ∀ x : ↥C × ↥P, mulH x = (x.1 : W) * x.2 := fun _ => rfl
  have hmulH_inj : Function.Injective mulH := by
    rw [injective_iff_map_eq_one]
    rintro ⟨c, p⟩ h
    rw [hmulH_apply] at h
    have hcp : (c : W) = (p : W)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hc : (c : W) ∈ C ⊓ P := ⟨c.2, hcp ▸ P.inv_mem p.2⟩
    rw [hCP, Subgroup.mem_bot] at hc
    have hp : (p : W) = 1 := by rw [hc] at hcp; exact (inv_eq_one.mp hcp.symm)
    exact Prod.ext (Subtype.ext hc) (Subtype.ext hp)
  have hmulH_surj : Function.Surjective mulH := by
    intro w
    have hw : w ∈ C ⊔ P := hCPt ▸ Subgroup.mem_top w
    obtain ⟨c, hc, p, hp, rfl⟩ := Subgroup.mem_sup.mp hw
    exact ⟨(⟨c, hc⟩, ⟨p, hp⟩), rfl⟩
  set e : ↥C × ↥P ≃* W := MulEquiv.ofBijective mulH ⟨hmulH_inj, hmulH_surj⟩ with he
  set ψ : ↥C ≃* ↥C := σ.trans (φ.trans σ.symm) with hψ
  set g : MulAut W := e.symm.trans ((MulEquiv.prodCongr ψ (MulEquiv.refl _)).trans e) with hg
  have hgcp : ∀ c : ↥C, ∀ p : ↥P, g ((c : W) * p) = (ψ c : W) * p := by
    intro c p
    have h1 : e.symm ((c : W) * p) = (c, p) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    show e ((MulEquiv.prodCongr ψ (MulEquiv.refl _)) (e.symm ((c : W) * p))) = _
    rw [h1]
    rfl
  have hgp : ∀ p ∈ P, g p = p := by
    intro p hp
    have := hgcp 1 ⟨p, hp⟩
    simp only [OneMemClass.coe_one, one_mul, map_one] at this
    exact this
  have hgP : P.map g.toMonoidHom = P := by
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      show g p ∈ P
      rw [hgp p hp]
      exact hp
    · intro hw
      exact ⟨w, hw, hgp w hw⟩
  refine ⟨g, hgP, MulEquiv.ext fun q => ?_⟩
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective P q
  have hw : w ∈ C ⊔ P := hCPt ▸ Subgroup.mem_top w
  obtain ⟨c, hc, p, hp, rfl⟩ := Subgroup.mem_sup.mp hw
  show QuotientGroup.mk' P (g (c * p)) = φ (QuotientGroup.mk' P (c * p))
  have hgcp' := hgcp ⟨c, hc⟩ ⟨p, hp⟩
  simp only at hgcp'
  rw [hgcp']
  have hp1 : QuotientGroup.mk' P p = 1 := (QuotientGroup.eq_one_iff p).mpr hp
  have e1 : QuotientGroup.mk' P ((ψ ⟨c, hc⟩ : W) * p) = mkC (ψ ⟨c, hc⟩) := by
    rw [map_mul, hp1, mul_one]
    rfl
  have e2 : QuotientGroup.mk' P (c * p) = σ ⟨c, hc⟩ := by
    rw [map_mul, hp1, mul_one]
    rfl
  rw [e1, e2]
  show σ (ψ ⟨c, hc⟩) = φ (σ ⟨c, hc⟩)
  rw [hψ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

end Elem

theorem subnormal_eq_top {Y : Type*} [Group Y] [IsSimpleGroup Y] {K : Subgroup Y}
    (hK : IsSubnormal K ⊤) (hK1 : K ≠ ⊥) : K = ⊤ := by
  by_contra hne
  obtain ⟨P, hPt, hPn, hKP⟩ := A3.subnormal_exists_normal_of_lt hK (lt_top_iff_ne_top.2 hne)
  have hPn' : P.Normal := by
    have := (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hPn
    exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.2 this)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
  · exact hK1 (le_bot_iff.1 (h ▸ hKP))
  · exact (lt_irrefl _ (h ▸ hPt))

theorem exists_cComp_map_top {A Y : Type*} [Group A] [Finite A] [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hnab : ∃ a b : Y, a * b ≠ b * a) (ρ : A →* Y)
    (hρ : Function.Surjective ρ)
    (hspan : cCompSpan (⊤ : Subgroup A) = perfectCore (⊤ : Subgroup A)) :
    ∃ L' ∈ cComp (⊤ : Subgroup A), L'.map ρ = ⊤ := by
  have hperf : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ with
      h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hc : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    · exact h
  have hrange : (⊤ : Subgroup A).map ρ = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact hρ
  have htop : (cCompSpan (⊤ : Subgroup A)).map ρ = ⊤ := by
    rw [hspan, map_perfectCore, hrange, perfectCore_eq_self_of_perfect hperf]
  by_contra hall
  push Not at hall
  have hbot : ∀ L' ∈ cComp (⊤ : Subgroup A), L'.map ρ = ⊥ := by
    intro L' hL'
    by_contra hne
    refine hall L' hL' (subnormal_eq_top ?_ hne)
    have := A3.subnormal_map ρ (subnormal_of_mem_cComp hL')
    rwa [hrange] at this
  have : (cCompSpan (⊤ : Subgroup A)).map ρ = ⊥ := by
    rw [cCompSpan, (Subgroup.gc_map_comap ρ).l_sSup]
    exact le_bot_iff.1 (iSup₂_le fun L hL => (hbot L hL).le)
  rw [htop] at this
  have h1 : ∀ y : Y, y = 1 := fun y => by
    have hy : y ∈ (⊤ : Subgroup Y) := Subgroup.mem_top y
    rw [this, Subgroup.mem_bot] at hy
    exact hy
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (by rw [h1 a, h1 b])

section Outer

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierAlternating

theorem card_outer_dvd_two {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 8)) : Nat.card (Outer Q) ∣ 2 := by
  have h1 := outer_card_dvd_two_of_equiv_outside_six (Or.inr (by norm_num)) e
  have hinj := centerQuotient_outer_injective Q
  have : Finite (MulAut (Q ⧸ Subgroup.center Q)) := MulEquiv.finite_left
  have h2 : Nat.card (Outer Q) ∣ Nat.card (Outer (Q ⧸ Subgroup.center Q)) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  exact h2.trans h1

theorem exists_conj_of_pow_three {Q : Type*} [Group Q] [Finite Q]
    (h : Nat.card (Outer Q) ∣ 2) {α : MulAut Q} (hα : α ^ 3 = 1) :
    ∃ q : Q, α = MulAut.conj q := by
  have : Finite (MulAut Q) := MulEquiv.finite_left
  set o := QuotientGroup.mk' (inner Q) α with ho
  have h3 : o ^ 3 = 1 := by rw [ho, ← map_pow, hα, map_one]
  have h2 : o ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard o).trans h)
  have ho1 : o = 1 := by
    calc o = o ^ 3 * (o ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  obtain ⟨q, hq⟩ := (QuotientGroup.eq_one_iff α).mp ho1
  exact ⟨q, hq.symm⟩

end Outer

end CFSG.Quasithin.Lift3
