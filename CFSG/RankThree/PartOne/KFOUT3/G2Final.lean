module

public import CFSG.RankThree.PartOne.KFOUT3.G2Aut
public import CFSG.RankThree.PartOne.N1322.Statements
public import CFSG.RankThree.PartOne.KF.R11Final

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N1322 CFSG.RankThree.PartOne.KFU

theorem exists_torusImage_conj_of_scalar {G : Type} [Group G] {c : G} {L E F : Subgroup G}
    (R : Sec12Three.Restr c L E F) {y h : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyE : y ∈ Subgroup.normalizer (E : Set G)) (hhL : h ∈ L)
    (hhF : h ∈ Subgroup.normalizer (F : Set G)) {n : ℤ}
    (hn : ∀ f ∈ F, y * f * y⁻¹ = h * f ^ n * h⁻¹) {t : MulAut E} (ht : t ∈ torusImage E L) :
    ∃ l ∈ torusImage E L,
      E.normalizerMonoidHom ⟨y, hyE⟩ * t * (E.normalizerMonoidHom ⟨y, hyE⟩)⁻¹ = l * t * l⁻¹ := by
  obtain ⟨x, hxL, hxE, rfl⟩ := Sec12Three.mem_torusImage_iff.mp ht
  have hxF : x ∈ Subgroup.normalizer (F : Set G) := R.inf_normalizer_le ⟨hxL, hxE⟩
  have hyF : y ∈ Subgroup.normalizer (F : Set G) := by
    have := Sec12Three.mem_normalizer_inf hyL hyE
    rwa [← R.F_eq] at this
  have hhE : h ∈ Subgroup.normalizer (E : Set G) := R.inf_normalizer_ge ⟨hhL, hhF⟩
  refine ⟨E.normalizerMonoidHom ⟨h, hhE⟩, Sec12Three.mem_torusImage_iff.mpr ⟨h, hhL, hhE, rfl⟩, ?_⟩
  have key : ∀ f ∈ F, y * x * y⁻¹ * f * (y * x * y⁻¹)⁻¹ = h * x * h⁻¹ * f * (h * x * h⁻¹)⁻¹ := by
    intro f hf
    have hf₃mem : y⁻¹ * f * y ∈ F := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (F : Set G)).inv_mem hyF) f).mp
        hf
      simpa using this
    obtain ⟨f₃, hf₃, rfl⟩ : ∃ f₃ ∈ F, f = y * f₃ * y⁻¹ := ⟨y⁻¹ * f * y, hf₃mem, by group⟩
    have hxf₃ : x * f₃ * x⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hxF f₃).mp hf₃
    have e1 : y * x * y⁻¹ * (y * f₃ * y⁻¹) * (y * x * y⁻¹)⁻¹ = y * (x * f₃ * x⁻¹) * y⁻¹ := by
      group
    rw [e1, hn _ hxf₃, conj_zpow, hn f₃ hf₃]
    group
  have hu : y * x * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL x).mp hxL
  have hv : h * x * h⁻¹ ∈ L := L.mul_mem (L.mul_mem hhL hxL) (L.inv_mem hhL)
  have hconj : ∀ u ∈ L, ∀ (f : G) (i : ℤ), u * (f * c ^ i) * u⁻¹ = (u * f * u⁻¹) * c ^ i := by
    intro u hu f i
    calc u * (f * c ^ i) * u⁻¹ = (u * f * u⁻¹) * (u * c ^ i * u⁻¹) := by group
      _ = (u * f * u⁻¹) * c ^ i := by rw [R.conj_zpow hu i]
  have e1 : E.normalizerMonoidHom ⟨y, hyE⟩ * E.normalizerMonoidHom ⟨x, hxE⟩ *
      (E.normalizerMonoidHom ⟨y, hyE⟩)⁻¹ = E.normalizerMonoidHom
        ((⟨y, hyE⟩ : Subgroup.normalizer (E : Set G)) * ⟨x, hxE⟩ * ⟨y, hyE⟩⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  have e2 : E.normalizerMonoidHom ⟨h, hhE⟩ * E.normalizerMonoidHom ⟨x, hxE⟩ *
      (E.normalizerMonoidHom ⟨h, hhE⟩)⁻¹ = E.normalizerMonoidHom
        ((⟨h, hhE⟩ : Subgroup.normalizer (E : Set G)) * ⟨x, hxE⟩ * ⟨h, hhE⟩⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [e1, e2]
  refine MulEquiv.ext fun e => Subtype.ext ?_
  show y * x * y⁻¹ * (e : G) * (y * x * y⁻¹)⁻¹ = h * x * h⁻¹ * (e : G) * (h * x * h⁻¹)⁻¹
  obtain ⟨f, hf, i, hfi⟩ := R.exists_mul_zpow e.2
  rw [hfi, hconj _ hu f i, hconj _ hv f i, key f hf]

theorem kf1322G2_holds :
    KF1322G2 := by
  intro G _ _ p A c L E h12 hF12 _ _ hEA _ hmodel t _ s _ hts y hyc hyE heq
  have hyL : y ∈ Subgroup.normalizer (L : Set G) :=
    hF12.twoB (Subgroup.mem_inf.mpr ⟨hyc, hyE⟩)
  rcases hF12.two with hG | hS
  ·
    have R := h12.restr_of_generic hG
    have hp := h12.prime
    have h5 := Sec12Three.five_le h12
    have hyF : y ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) :=
      Sec12Three.mem_normalizer_inf hyL hyE
    have hFexp : ∀ f ∈ E ⊓ L, f ^ p = 1 := fun f hf =>
      Sec12Three.pow_eq_one_of_mem_E h12 (Subgroup.mem_inf.mp hf).1
    have hFcomm : ∀ a ∈ E ⊓ L, ∀ b ∈ E ⊓ L, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (h12.E_elem.is_comm.comm ⟨a, (Subgroup.mem_inf.mp ha).1⟩
        ⟨b, (Subgroup.mem_inf.mp hb).1⟩)
    have hmax : ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
        (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → E ⊓ L ≤ F' → F' = E ⊓ L := by
      intro F' hF'L hexp hcomm hFF'
      have hc : IsMulCommutative F' := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
      have hel : IsElementaryAbelian p F' :=
        { toIsMulCommutative := hc
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun g =>
            Subtype.ext (hexp _ g.2) }
      refine Sec12Three.F_max_generic h12 hG F' hF'L hel ?_ hFF'
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have ha' := Subgroup.mem_inf.mp ha
      exact hcomm a (hFF' (Subgroup.mem_inf.mpr ⟨h12.A_le_E ha'.1, ha'.2⟩)) x hx
    obtain ⟨h, hhL, hhF, n, hn⟩ := exists_weyl_scalar hp h5 hG.center_pPrime inf_le_right hFexp
      hFcomm hmax hmodel hyL hyF
    obtain ⟨l, hl, hlt⟩ := exists_torusImage_conj_of_scalar R hyL hyE hhL hhF hn hts.1
    have heq' : E.normalizerMonoidHom ⟨y, hyE⟩ * t * (E.normalizerMonoidHom ⟨y, hyE⟩)⁻¹ = s := heq
    exact hts.2.2 l hl (hlt.symm.trans heq')
  ·
    exfalso
    have hrow := kf123Row11 G p L A E (Sec12Three.table123SU5 h12 hS)
    have hcard : Nat.card E = p ^ 4 := hrow.2.1
    rw [hEA, h12.A_card] at hcard
    have h5 := Sec12Three.five_le h12
    have h1 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

end CFSG.RankThree.PartOne.KFOUT3
