module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwo
public import CFSG.GroupTheory.CardMapInfKer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

section Certified


theorem isPerfect_hatK (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    Group.IsPerfect ↥(hatK Mo V) := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  let Khat : Subgroup (LGL 2 Mo.W) := hatK Mo V
  let Lhat : Subgroup (LGL 2 Mo.W) := Mo.img (V ⊔ conjSubgroup V g)
  let C : Subgroup (LGL 2 Mo.W) := ⁅Khat, Khat⁆
  have hLK : Lhat ≤ Khat := Mo.img_mono c.L_le_conjClosure
  haveI hperfL : Group.IsPerfect ↥Lhat := isPerfect_hatL hn h1 h5 h15 hS c Mo
  have hLcomm : ⁅Lhat, Lhat⁆ = Lhat := Subgroup.isPerfect_iff.mp hperfL
  have hLC : Lhat ≤ C := by
    rw [show Lhat = ⁅Lhat, Lhat⁆ from hLcomm.symm]
    exact Subgroup.commutator_mono hLK hLK
  have hVC : Mo.img V ≤ C :=
    (Mo.img_mono (le_sup_left : V ≤ V ⊔ conjSubgroup V g)).trans hLC
  have hgen : kHatOf (hatGamma Mo V) ≤ C := by
    rw [kHatOf, Subgroup.closure_le]
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨A, hx'⟩
    rcases Set.mem_iUnion.1 hx' with ⟨hA, hxA⟩
    obtain ⟨h, hh, rfl⟩ := hA
    have himg : Mo.img (conjSubgroup V h) = cj (Mo.ρ (⟨h, hh⟩ : ↥H)⁻¹) (Mo.img V) := by
      have h := Mo.img_conj (A := V) hVH (⟨h, hh⟩ : ↥H)⁻¹
      simpa using h.symm
    have hnormK : conjSubgroup (conjClosure V H) h = conjClosure V H := by
      rw [conjSubgroup_eq_iff_mem_normalizer]
      exact le_normalizer_conjClosure V H hh
    have hcoe : (↑(⟨h, hh⟩ : ↥H)⁻¹ : G)⁻¹ = h := by simp
    have hcjK : cj (Mo.ρ (⟨h, hh⟩ : ↥H)⁻¹) Khat = Khat := by
      have h := Mo.img_conj (A := conjClosure V H) c.conjClosure_le_H (⟨h, hh⟩ : ↥H)⁻¹
      rw [show Khat = Mo.img (conjClosure V H) from rfl, h, hcoe, hnormK]
    have hcjC : cj (Mo.ρ (⟨h, hh⟩ : ↥H)⁻¹) C = C := by
      have hmap : cj (Mo.ρ (⟨h, hh⟩ : ↥H)⁻¹) (⁅Khat, Khat⁆) = ⁅Khat, Khat⁆ := by
        rw [show cj (Mo.ρ (⟨h, hh⟩ : ↥H)⁻¹) (⁅Khat, Khat⁆) =
            (⁅Khat, Khat⁆).map (MulAut.conj (Mo.ρ (⟨h, hh⟩ : ↥H)⁻¹)).toMonoidHom from rfl,
          Subgroup.map_commutator]
        rw [show Khat.map (MulAut.conj (Mo.ρ (⟨h, hh⟩ : ↥H)⁻¹)).toMonoidHom =
            cj (Mo.ρ (⟨h, hh⟩ : ↥H)⁻¹) Khat from rfl, hcjK]
      rw [show C = ⁅Khat, Khat⁆ from rfl, hmap]
    rw [himg] at hxA
    exact hcjC ▸ (cj_mono _ hVC) hxA
  have hKC : Khat ≤ C := by
    conv_lhs =>
      rw [show Khat = kHatOf (hatGamma Mo V) by
        rw [show Khat = Mo.img (conjClosure V H) from rfl, kHatOf_hatGamma_eq Mo V hVH]]
    exact hgen
  have hCK : C ≤ Khat := by
    rw [show C = ⁅Khat, Khat⁆ from rfl, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact Khat.mul_mem (Khat.mul_mem (Khat.mul_mem ha hb) (Khat.inv_mem ha))
      (Khat.inv_mem hb)
  have hCeq : C = Khat := le_antisymm hCK hKC
  exact Subgroup.isPerfect_iff.mpr (by change C = Khat; exact hCeq)

theorem ker_hatBar (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    (hatBar Mo V).ker = Subgroup.center ↥(hatK Mo V) := by
  haveI hperf : Group.IsPerfect ↥(hatK Mo V) := isPerfect_hatK hn h1 h5 h15 hS c Mo
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext k
  constructor
  · intro hk
    rw [MonoidHom.mem_ker] at hk
    have hk1 : (QuotientGroup.mk' (Subgroup.center (hatX Mo V)))
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V)) k) = 1 := hk
    have hcen : (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V)) k) ∈
        Subgroup.center (hatX Mo V) :=
      (QuotientGroup.eq_one_iff (N := Subgroup.center (hatX Mo V))
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V)) k)).1 hk1
    have hdisp : ∀ x : ↥(hatK Mo V),
        x⁻¹ * (MulAut.conj k).toMonoidHom x ∈ Subgroup.center ↥(hatK Mo V) := by
      intro x
      have hmem : ⁅x⁻¹, k⁆ ∈ CFSG.pCore 2 ↥(hatK Mo V) := by
        rw [← QuotientGroup.ker_mk' (N := CFSG.pCore 2 ↥(hatK Mo V)), MonoidHom.mem_ker]
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_center_iff.mp hcen
            (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V)) x⁻¹))
      have hmem' := pCore_hatK_le_center h1 h5 h15 hS c Mo hmem
      simpa [commutatorElement_def, MulAut.conj_apply, mul_assoc] using hmem'
    have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
      (MulAut.conj k).toMonoidHom hdisp
    rw [Subgroup.mem_center_iff]
    intro x
    have hx : (MulAut.conj k).toMonoidHom x = x := by
      have h := congrArg (fun f : ↥(hatK Mo V) →* ↥(hatK Mo V) => f x) hid
      simpa using h
    have hx' : k * x * k⁻¹ = x := by simpa [MulAut.conj_apply] using hx
    calc x * k = (k * x * k⁻¹) * k := by rw [hx']
      _ = k * x := by group
  · intro hk
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk' (Subgroup.center (hatX Mo V)))
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V)) k) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(hatK Mo V)) y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hk x]

theorem odd_card_center_hatX (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    Odd (Nat.card (Subgroup.center (hatX Mo V))) := by
  haveI hperf : Group.IsPerfect ↥(hatK Mo V) := isPerfect_hatK hn h1 h5 h15 hS c Mo
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.not_even_iff_odd]
  intro heven
  rw [even_iff_two_dvd] at heven
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 heven
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(hatK Mo V)) (z : hatX Mo V)
  have hbar1 : hatBar Mo V k = 1 := by
    change (QuotientGroup.mk' (Subgroup.center (hatX Mo V)))
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V)) k) = 1
    rw [hk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact z.2
  have hkcenter : k ∈ Subgroup.center ↥(hatK Mo V) := by
    rw [← ker_hatBar hn h1 h5 h15 hS c Mo]
    exact MonoidHom.mem_ker.mpr hbar1
  have hk2 : k ^ 2 ∈ CFSG.pCore 2 ↥(hatK Mo V) := by
    rw [← QuotientGroup.ker_mk' (N := CFSG.pCore 2 ↥(hatK Mo V)), MonoidHom.mem_ker]
    rw [map_pow, hk]
    have hz2 := pow_orderOf_eq_one z
    rw [hz] at hz2
    simpa using congrArg Subtype.val hz2
  let P : Subgroup ↥(hatK Mo V) := Subgroup.zpowers k ⊔ CFSG.pCore 2 ↥(hatK Mo V)
  have hPle : P ≤ Subgroup.center ↥(hatK Mo V) := by
    refine sup_le ?_ (pCore_hatK_le_center h1 h5 h15 hS c Mo)
    rw [Subgroup.zpowers_le]
    exact hkcenter
  have hPnorm : P.Normal := Subgroup.normal_of_le_center hPle
  have hkorder : ∃ a, orderOf k = 2 ^ a := by
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(hatK Mo V))).exists_orderOf_eq_pow
      (⟨k ^ 2, hk2⟩ : ↥(CFSG.pCore 2 ↥(hatK Mo V)))
    have hb' : orderOf (k ^ 2) = 2 ^ b := by simpa using hb
    rw [orderOf_pow] at hb'
    have hg : Nat.gcd (orderOf k) 2 = 1 ∨ Nat.gcd (orderOf k) 2 = 2 :=
      (Nat.dvd_prime Nat.prime_two).1 (Nat.gcd_dvd_right _ _)
    have hdvd : Nat.gcd (orderOf k) 2 ∣ orderOf k := Nat.gcd_dvd_left _ _
    have hmul : orderOf k = (orderOf k / Nat.gcd (orderOf k) 2) * Nat.gcd (orderOf k) 2 :=
      (Nat.div_mul_cancel hdvd).symm
    rcases hg with h1 | h2
    · exact ⟨b, by rw [hmul, hb', h1, mul_one]⟩
    · exact ⟨b + 1, by rw [hmul, hb', h2, pow_succ]⟩
  have hPp : IsPGroup 2 P := by
    have hzp : IsPGroup 2 (Subgroup.zpowers k) := by
      obtain ⟨a, ha⟩ := hkorder
      refine IsPGroup.of_card (n := a) ?_
      rw [Nat.card_zpowers, ha]
    exact IsPGroup.to_sup_of_normal_right hzp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(hatK Mo V)))
  have hPcore : P ≤ CFSG.pCore 2 ↥(hatK Mo V) := by
    rw [CFSG.pCore]
    exact le_sSup ⟨hPnorm, hPp⟩
  have hkcore : k ∈ CFSG.pCore 2 ↥(hatK Mo V) :=
    hPcore (Subgroup.mem_sup_left (Subgroup.mem_zpowers k))
  have hz1 : (z : hatX Mo V) = 1 := by
    rw [← hk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hkcore
  have hzne : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  exact hzne (Subtype.ext (by simpa using hz1))

private theorem card_hatBarSub_eq_card_img_of_le (hn : 2 ≤ E3.mQuot V (U ⊔ V₀))
    (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    {J : Subgroup G} (hJ : Mo.img J ≤ Mo.img (V ⊔ conjSubgroup V g)) :
    Nat.card ↥(hatBarSub Mo V J) = Nat.card (Mo.img J) := by
  have hJK : Mo.img J ≤ hatK Mo V := hJ.trans (Mo.img_mono c.L_le_conjClosure)
  have hker : (Mo.img J).subgroupOf (hatK Mo V) ⊓ (hatBar Mo V).ker = ⊥ := by
    rw [ker_hatBar hn h1 h5 h15 hS c Mo, eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr
      (inf_center_hatL hn h1 h5 h15 hS c Mo x (hJ hx.1) hx.2)
  rw [hatBarSub, CFSG.card_map_eq_card_of_inf_ker_eq_bot (hatBar Mo V) hker]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJK).toEquiv

theorem card_hatBarSub_V (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    Nat.card ↥(hatBarSub Mo V V) = 2 ^ E3.mQuot V (U ⊔ V₀) := by
  rw [card_hatBarSub_eq_card_img_of_le hn h1 h5 h15 hS c Mo
    (Mo.img_mono (le_sup_left : V ≤ V ⊔ conjSubgroup V g))]
  simpa [conjSubgroup_one] using
    card_img_conjSubgroup h1 h5 h15 hS c Mo (Subgroup.one_mem H)

theorem card_hatBarSub_L (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    Nat.card ↥(hatBarSub Mo V (V ⊔ conjSubgroup V g)) =
      Nat.card ↥(Mo.img (V ⊔ conjSubgroup V g)) :=
  card_hatBarSub_eq_card_img_of_le hn h1 h5 h15 hS c Mo le_rfl

theorem hatBarSub_L_ne_top (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    hatBarSub Mo V (V ⊔ conjSubgroup V g) ≠ ⊤ := by
  haveI hperf : Group.IsPerfect ↥(hatK Mo V) := isPerfect_hatK hn h1 h5 h15 hS c Mo
  let K : Subgroup G := conjClosure V H
  have hKH : K ≤ H := c.conjClosure_le_H
  let Q := ↥(hatK Mo V)
  let ρK : ↥K →* Q :=
    { toFun := fun k => ⟨Mo.ρ ⟨(k : G), hKH k.2⟩,
        Mo.mem_img.mpr ⟨⟨(k : G), hKH k.2⟩, k.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        change Mo.ρ (1 : ↥H) = 1
        exact map_one _
      map_mul' := by
        intro a b
        apply Subtype.ext
        change Mo.ρ ((⟨(a : G), hKH a.2⟩ : ↥H) * ⟨(b : G), hKH b.2⟩) =
          Mo.ρ ⟨(a : G), hKH a.2⟩ * Mo.ρ ⟨(b : G), hKH b.2⟩
        exact map_mul _ _ _ }
  let Z : Subgroup G := ((Subgroup.center Q).comap ρK).map K.subtype
  have hZK : Z ≤ K := by
    rintro z ⟨k, -, rfl⟩
    exact k.2
  have hZ : ∀ z ∈ Z, ∀ k ∈ K,
      ⁅z, k⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
    rintro z ⟨z₀, hz₀, rfl⟩ k hk
    have hz₀center : ρK z₀ ∈ Subgroup.center Q := hz₀
    have hz₀H : (z₀ : G) ∈ H := hKH z₀.2
    have hkH : k ∈ H := hKH hk
    have hz₀kK : ⁅(z₀ : G), k⁆ ∈ K := by
      rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem z₀.2 hk) (K.inv_mem z₀.2)) (K.inv_mem hk)
    have hz₀kH : ⁅(z₀ : G), k⁆ ∈ H := hKH hz₀kK
    let kK : ↥K := ⟨k, hk⟩
    have hcommQ : ⁅ρK z₀, ρK kK⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hz₀center (ρK kK)).symm
    have hmap : Mo.ρ (⟨⁅(z₀ : G), k⁆, hz₀kH⟩ : ↥H) =
        ⁅Mo.ρ (⟨(z₀ : G), hz₀H⟩ : ↥H), Mo.ρ (⟨k, hkH⟩ : ↥H)⁆ := by
      have hsub : (⟨⁅(z₀ : G), k⁆, hz₀kH⟩ : ↥H) =
          ⁅(⟨(z₀ : G), hz₀H⟩ : ↥H), (⟨k, hkH⟩ : ↥H)⁆ := Subtype.ext rfl
      rw [hsub, map_commutatorElement]
    have hρone : Mo.ρ (⟨⁅(z₀ : G), k⁆, hz₀kH⟩ : ↥H) = 1 := by
      rw [hmap]
      have hρz_eq : (hatK Mo V).subtype (ρK z₀) = Mo.ρ (⟨(z₀ : G), hz₀H⟩ : ↥H) := by
        change Mo.ρ (⟨(z₀ : G), hKH z₀.2⟩ : ↥H) = Mo.ρ ⟨(z₀ : G), hz₀H⟩
        rw [show (⟨(z₀ : G), hKH z₀.2⟩ : ↥H) = ⟨(z₀ : G), hz₀H⟩ from Subtype.ext rfl]
      have hρk_eq : (hatK Mo V).subtype (ρK kK) = Mo.ρ (⟨k, hkH⟩ : ↥H) := by
        change Mo.ρ (⟨k, hKH hk⟩ : ↥H) = Mo.ρ ⟨k, hkH⟩
        rw [show (⟨k, hKH hk⟩ : ↥H) = ⟨k, hkH⟩ from Subtype.ext rfl]
      have hval := congrArg (hatK Mo V).subtype hcommQ
      rw [map_commutatorElement, map_one, hρz_eq, hρk_eq] at hval
      exact hval
    exact ⟨hz₀kH, by
      have h := (Mo.ρ_eq_one_iff (⟨⁅(z₀ : G), k⁆, hz₀kH⟩ : ↥H)).1 hρone
      simpa using h⟩
  intro htop
  apply c.not_le_sup_of_comm h15 hS hZK hZ
  intro k hk
  have hkH : k ∈ H := hKH hk
  let kQ : Q := ⟨Mo.ρ ⟨k, hkH⟩, Mo.mem_img.mpr ⟨⟨k, hkH⟩, hk, rfl⟩⟩
  have hkQtop : hatBar Mo V kQ ∈ hatBarSub Mo V (V ⊔ conjSubgroup V g) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨x, hxL, hxπ⟩ := (mem_hatBarSub_iff (Mo := Mo) (V := V)).1 hkQtop
  have hx1 : x⁻¹ * kQ ∈ (hatBar Mo V).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxπ]
    group
  have hx1center : x⁻¹ * kQ ∈ Subgroup.center Q := by
    rw [← ker_hatBar hn h1 h5 h15 hS c Mo]
    exact hx1
  obtain ⟨l, hlL, hxl⟩ := Mo.mem_img.mp hxL
  have hLK : V ⊔ conjSubgroup V g ≤ K := c.L_le_conjClosure
  let lK : ↥K := ⟨(l : G), hLK hlL⟩
  have hl_eq : (⟨(l : G), hKH lK.2⟩ : ↥H) = l := Subtype.ext rfl
  have hxlK : ρK lK = x := by
    apply Subtype.ext
    change Mo.ρ ⟨(l : G), hKH lK.2⟩ = (x : LGL 2 Mo.W)
    rw [hl_eq]
    exact hxl
  let kK : ↥K := ⟨k, hk⟩
  have hkK : ρK kK = kQ := by
    apply Subtype.ext
    change Mo.ρ ⟨k, hKH hk⟩ = (kQ : LGL 2 Mo.W)
    rw [show (⟨k, hKH hk⟩ : ↥H) = ⟨k, hkH⟩ from Subtype.ext rfl]
  let z₀ : ↥K := lK⁻¹ * kK
  have hz₀eq : ρK z₀ = x⁻¹ * kQ := by
    dsimp only [z₀]
    rw [map_mul, map_inv, hxlK, hkK]
  have hz₀ : z₀ ∈ (Subgroup.center Q).comap ρK := by
    rw [Subgroup.mem_comap]
    show ρK z₀ ∈ Subgroup.center Q
    rw [hz₀eq]
    exact hx1center
  have hz₀Z : ((z₀ : ↥K) : G) ∈ Z := Subgroup.mem_map.mpr ⟨z₀, hz₀, rfl⟩
  have hz₀val : ((z₀ : ↥K) : G) = (l : G)⁻¹ * k := rfl
  have hl_sup : (l : G) ∈ (V ⊔ conjSubgroup V g) ⊔ Z := Subgroup.mem_sup_left hlL
  have hz_sup : (l : G)⁻¹ * k ∈ (V ⊔ conjSubgroup V g) ⊔ Z := by
    rw [← hz₀val]
    exact Subgroup.mem_sup_right hz₀Z
  have hmul := ((V ⊔ conjSubgroup V g) ⊔ Z).mul_mem hl_sup hz_sup
  rwa [mul_inv_cancel_left] at hmul

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
