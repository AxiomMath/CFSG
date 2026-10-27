module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedAut
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedLift
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFinite

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.ComponentClassification.PerfectAutomorphisms

def wccg_conjAut {Y : Type} [Group Y] (L : Subgroup Y) (a : Y)
    (ha : a ∈ Subgroup.normalizer (L : Set Y)) : MulAut ↥L :=
  Subgroup.normalizerMonoidHom (H := L) ⟨a, ha⟩

theorem wccg_conjAut_apply_coe {Y : Type} [Group Y] (L : Subgroup Y) (a : Y)
    (ha : a ∈ Subgroup.normalizer (L : Set Y)) (x : ↥L) :
    (wccg_conjAut L a ha x : Y) = a * (x : Y) * a⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨a, ha⟩ x

theorem wccg_conjAut_mul_self {Y : Type} [Group Y] (L : Subgroup Y) (a : Y)
    (ha : a ∈ Subgroup.normalizer (L : Set Y)) (ha2 : a * a = 1) :
    wccg_conjAut L a ha * wccg_conjAut L a ha = 1 := by
  have hpair : (⟨a, ha⟩ : Subgroup.normalizer (L : Set Y)) * ⟨a, ha⟩ = 1 := by
    apply Subtype.ext
    change a * a = 1
    exact ha2
  calc wccg_conjAut L a ha * wccg_conjAut L a ha
      = Subgroup.normalizerMonoidHom (H := L) (⟨a, ha⟩ * ⟨a, ha⟩) := by
        unfold wccg_conjAut
        rw [← map_mul]
    _ = Subgroup.normalizerMonoidHom (H := L) 1 := by rw [hpair]
    _ = 1 := map_one _

theorem wccg_conjAut_mul_comm {Y : Type} [Group Y] (L : Subgroup Y) (a b : Y)
    (ha : a ∈ Subgroup.normalizer (L : Set Y)) (hb : b ∈ Subgroup.normalizer (L : Set Y))
    (hab : a * b = b * a) :
    wccg_conjAut L a ha * wccg_conjAut L b hb =
      wccg_conjAut L b hb * wccg_conjAut L a ha := by
  unfold wccg_conjAut
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hab

theorem wccg_conjAut_not_inner_of_not_mem_sup {Y : Type} [Group Y] {L : Subgroup Y}
    {β : Y} (hβN : β ∈ Subgroup.normalizer (L : Set Y))
    (hβnot : β ∉ L ⊔ Subgroup.centralizer (L : Set Y)) :
    ¬ ∃ g : ↥L, ∀ x : ↥L, wccg_conjAut L β hβN x = g * x * g⁻¹ := by
  rintro ⟨g, hg⟩
  apply hβnot
  have hgβ : (g : Y)⁻¹ * β ∈ Subgroup.centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hconj : β * y * β⁻¹ = (g : Y) * y * (g : Y)⁻¹ := by
      have h1 := congrArg (fun z : ↥L => (z : Y)) (hg ⟨y, hy⟩)
      simpa [wccg_conjAut_apply_coe] using h1
    calc y * ((g : Y)⁻¹ * β) = y * (g : Y)⁻¹ * β := by group
      _ = (g : Y)⁻¹ * ((g : Y) * y * (g : Y)⁻¹) * β := by group
      _ = (g : Y)⁻¹ * (β * y * β⁻¹) * β := by rw [← hconj]
      _ = (g : Y)⁻¹ * β * y := by group
  have hmem : (g : Y) * ((g : Y)⁻¹ * β) ∈ L ⊔ Subgroup.centralizer (L : Set Y) :=
    Subgroup.mul_mem_sup g.2 hgβ
  rwa [show (g : Y) * ((g : Y)⁻¹ * β) = β by group] at hmem

theorem wccg_onCenterQuotient_mul {G : Type} [Group G] (α β : MulAut G) :
    onCenterQuotient (α * β) = onCenterQuotient α * onCenterQuotient β :=
  map_mul (centerQuotientHom G) α β

theorem wccg_onCenterQuotient_inv {G : Type} [Group G] (α : MulAut G) :
    onCenterQuotient α⁻¹ = (onCenterQuotient α)⁻¹ :=
  map_inv (centerQuotientHom G) α

theorem wccg_conj_eq_of_forall_fixed
    {Y : Type} [Group Y] [Finite Y] {L A : Subgroup Y} {a β : Y}
    (hAe : IsElemAbelian 2 A) (hK : K1In L A)
    (hAN : A ≤ Subgroup.normalizer (L : Set Y))
    (haA : a ∈ A) (hβA : β ∈ A)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hNoTwo : OuterFixedNoNormalTwo (↥L ⧸ Subgroup.center ↥L))
    (hβnot : β ∉ L ⊔ Subgroup.centralizer (L : Set Y))
    {x : Y} (hxL : x ∈ L) (hxβ : x * β = β * x) :
    x * a * x⁻¹ = a := by
  haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
  haveI : Finite ↥L := Subtype.finite
  have hβN : β ∈ Subgroup.normalizer (L : Set Y) := hAN hβA
  have haN : a ∈ Subgroup.normalizer (L : Set Y) := hAN haA
  have hβ1 : β ≠ 1 := by
    rintro rfl
    exact hβnot (one_mem _)
  have ha2 : a * a = 1 := by simpa [pow_two] using hAe.2 a haA
  have hβ2 : β * β = 1 := by simpa [pow_two] using hAe.2 β hβA
  have hcommA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := by
    haveI : IsMulCommutative A := hAe.1
    intro u hu v hv
    exact congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : A) ⟨v, hv⟩)
  have hAcent : A ≤ Subgroup.centralizer ({β} : Set Y) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (hcommA u hu β hβA).symm
  have haCent : a ∈ Subgroup.centralizer ({β} : Set Y) := hAcent haA
  let αβ : MulAut ↥L := wccg_conjAut L β hβN
  have hαβ2 : αβ * αβ = 1 := wccg_conjAut_mul_self L β hβN hβ2
  have hαβNotInner : ¬ ∃ g : ↥L, ∀ z : ↥L, αβ z = g * z * g⁻¹ := by
    have := wccg_conjAut_not_inner_of_not_mem_sup hβN hβnot
    simpa [αβ] using this
  let C : Subgroup Y := L ⊓ Subgroup.centralizer ({β} : Set Y)
  let D : Subgroup Y := Subgroup.closure
    {γ : Y | ∃ z ∈ (C : Set Y), γ = z * a * z⁻¹}
  let E : Subgroup Y := Subgroup.closure
    {t : Y | ∃ z ∈ (C : Set Y), t = z * a * z⁻¹ * a⁻¹}
  have hD_e : IsElemAbelian 2 D := hK a haA β hβA hβ1
  have haD : a ∈ D := Subgroup.subset_closure
    ⟨1, Subgroup.mem_inf.mpr ⟨L.one_mem, (Subgroup.centralizer _).one_mem⟩, by group⟩
  have hED : E ≤ D := by
    apply (Subgroup.closure_le D).mpr
    rintro t ⟨z, hz, rfl⟩
    have hzD : z * a * z⁻¹ ∈ D := Subgroup.subset_closure ⟨z, hz, rfl⟩
    exact D.mul_mem hzD (D.inv_mem haD)
  have hE_e : IsElemAbelian 2 E := hD_e.mono hED
  have hE_P : IsPGroup 2 E := hE_e.isPGroup
  have hEL : E ≤ L := by
    apply (Subgroup.closure_le L).mpr
    rintro t ⟨z, hz, rfl⟩
    have hzL : z ∈ L := (Subgroup.mem_inf.mp hz).1
    have haxL : a * z⁻¹ * a⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp haN z⁻¹).mp (L.inv_mem hzL)
    have hzeq : z * a * z⁻¹ * a⁻¹ = z * (a * z⁻¹ * a⁻¹) := by group
    rw [hzeq]
    exact L.mul_mem hzL haxL
  have hE_cent : E ≤ Subgroup.centralizer ({β} : Set Y) := by
    apply (Subgroup.closure_le (Subgroup.centralizer ({β} : Set Y))).mpr
    rintro t ⟨z, hz, rfl⟩
    have hzC : z ∈ Subgroup.centralizer ({β} : Set Y) := (Subgroup.mem_inf.mp hz).2
    exact (Subgroup.centralizer ({β} : Set Y)).mul_mem
      ((Subgroup.centralizer ({β} : Set Y)).mul_mem
        ((Subgroup.centralizer ({β} : Set Y)).mul_mem hzC haCent)
        ((Subgroup.centralizer ({β} : Set Y)).inv_mem hzC))
      ((Subgroup.centralizer ({β} : Set Y)).inv_mem haCent)
  have hE_norm : ∀ y : Y, y ∈ L → y * β = β * y → ∀ e ∈ E, y * e * y⁻¹ ∈ E := by
    intro y hyL hyβ e he
    have hyC : y ∈ Subgroup.centralizer ({β} : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hyβ.symm
    have hyCl : y ∈ C := Subgroup.mem_inf.mpr ⟨hyL, hyC⟩
    have hgen : ∀ z : Y, z ∈ C → z * a * z⁻¹ * a⁻¹ ∈ E := fun z hz =>
      Subgroup.subset_closure ⟨z, hz, rfl⟩
    induction he using Subgroup.closure_induction with
    | mem t ht =>
        obtain ⟨z, hz, rfl⟩ := ht
        have hyz : y * z ∈ C := Subgroup.mul_mem _ hyCl hz
        have h1 := hgen (y * z) hyz
        have h2 := hgen y hyCl
        have h3 := E.mul_mem h1 (E.inv_mem h2)
        convert h3 using 1
        group
    | one => simpa using E.one_mem
    | mul u v hu hv ihu ihv =>
        have h3 := E.mul_mem ihu ihv
        convert h3 using 1
        group
    | inv u hu ihu =>
        have h3 := E.inv_mem ihu
        convert h3 using 1
        group
  let E' : Subgroup ↥L := E.subgroupOf L
  let Ē : Subgroup (↥L ⧸ Subgroup.center ↥L) :=
    E'.map (QuotientGroup.mk' (Subgroup.center ↥L))
  have hE'P : IsPGroup 2 E' := hE_P.comap_subtype
  have hĒP : IsPGroup 2 Ē := hE'P.map (QuotientGroup.mk' (Subgroup.center ↥L))
  have hĒfix : ∀ u ∈ Ē, onCenterQuotient αβ u = u := by
    intro u hu
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hu
    rw [onCenterQuotient_apply_mk]
    congr 1
    apply Subtype.ext
    show (wccg_conjAut L β hβN e : Y) = (e : Y)
    rw [wccg_conjAut_apply_coe]
    have heE : (e : Y) ∈ E := Subgroup.mem_subgroupOf.mp he
    have hcomm := Subgroup.mem_centralizer_iff.mp (hE_cent heE) β (Set.mem_singleton β)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hβbar2 : onCenterQuotient αβ * onCenterQuotient αβ = 1 := by
    rw [← wccg_onCenterQuotient_mul, hαβ2]
    exact map_one (centerQuotientHom ↥L)
  have hβbarNotInner : ¬ ∃ g : ↥L ⧸ Subgroup.center ↥L,
      ∀ z : ↥L ⧸ Subgroup.center ↥L, onCenterQuotient αβ z = g * z * g⁻¹ := by
    rintro ⟨g, hg⟩
    exact hαβNotInner (isInner_of_onCenterQuotient_inner αβ ⟨g, hg⟩)
  have hĒnorm : ∀ u : ↥L ⧸ Subgroup.center ↥L, onCenterQuotient αβ u = u →
      ∀ w ∈ Ē, u * w * u⁻¹ ∈ Ē := by
    intro u hu w hw
    obtain ⟨y, hyfix, hyeq⟩ := exists_fixed_lift_centerQuotient hodd αβ hαβ2 u hu
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hw
    subst u
    have hyconj : β * (y : Y) * β⁻¹ = (y : Y) := by
      have h1 := congrArg (fun z : ↥L => (z : Y)) hyfix
      simpa [αβ, wccg_conjAut_apply_coe] using h1
    have hyβ : (y : Y) * β = β * (y : Y) := by
      calc (y : Y) * β = (β * (y : Y) * β⁻¹) * β := by rw [hyconj]
        _ = β * (y : Y) := by group
    have hmem : ((y : Y) * (e : Y) * (y : Y)⁻¹) ∈ E :=
      hE_norm (y : Y) y.2 hyβ (e : Y) (Subgroup.mem_subgroupOf.mp he)
    have hzE : y * e * y⁻¹ ∈ E' := Subgroup.mem_subgroupOf.mpr hmem
    have hzĒ : (QuotientGroup.mk' (Subgroup.center ↥L)) (y * e * y⁻¹) ∈ Ē :=
      Subgroup.mem_map.mpr ⟨y * e * y⁻¹, hzE, rfl⟩
    have hEq : ((y : ↥L) : ↥L ⧸ Subgroup.center ↥L) *
          (QuotientGroup.mk' (Subgroup.center ↥L)) e *
          (((y : ↥L) : ↥L ⧸ Subgroup.center ↥L))⁻¹ =
        (QuotientGroup.mk' (Subgroup.center ↥L)) (y * e * y⁻¹) := rfl
    rw [hEq]
    exact hzĒ
  have hĒbot : Ē = ⊥ :=
    hNoTwo (onCenterQuotient αβ) hβbar2 hβbarNotInner Ē hĒP hĒfix hĒnorm
  have hE'Z : E' ≤ Subgroup.center ↥L := by
    have hker : E' ≤ MonoidHom.ker (QuotientGroup.mk' (Subgroup.center ↥L)) := by
      intro e he
      rw [MonoidHom.mem_ker]
      have hm : (QuotientGroup.mk' (Subgroup.center ↥L)) e ∈ Ē :=
        Subgroup.mem_map.mpr ⟨e, he, rfl⟩
      rw [hĒbot] at hm
      exact Subgroup.mem_bot.mp hm
    rwa [QuotientGroup.ker_mk'] at hker
  have hE'card : Nat.card E' = 1 := by
    rcases hE'P.card_eq_or_dvd with h1 | h2
    · exact h1
    · exact absurd (dvd_trans h2 (Subgroup.card_dvd_of_le hE'Z)) (Odd.not_two_dvd_nat hodd)
  have hE'bot : E' = ⊥ := (Subgroup.eq_bot_iff_card E').mpr hE'card
  have hEbot : E = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro e he
    have hmem : (⟨e, hEL he⟩ : ↥L) ∈ E' := Subgroup.mem_subgroupOf.mpr he
    rw [hE'bot] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  have hxC : x ∈ C := Subgroup.mem_inf.mpr ⟨hxL, by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hxβ.symm⟩
  have htE : x * a * x⁻¹ * a⁻¹ ∈ E := Subgroup.subset_closure ⟨x, hxC, rfl⟩
  rw [hEbot] at htE
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp htE)

end CFSG.LocalAnalysis.WeakClosure81

end
