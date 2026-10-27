module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneLin
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneImg
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneGen
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProdLemmas
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem inf_centralizer_conjSubgroup_inf_eq_bot (c : Cfg1620 M V₀ V U S R H g B) {h : G}
    (hh : ¬ conjSubgroup V h ≤ M) :
    (U ⊔ V₀) ⊓ centralizer (conjSubgroup V h : Set G) ⊓ V₀ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  apply hh
  intro v hv
  exact c.cex.hyp.centralizer_le hx.2 hx1 (Subgroup.mem_centralizer_singleton_iff.2
    ((Subgroup.mem_centralizer_iff.1 hx.1.2) v hv))

theorem sup_inf_centralizer_eq (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (hn : E3.mQuot V (U ⊔ V₀) = 1) {h : G}
    (hhH : h ∈ H) (hh : ¬ conjSubgroup V h ≤ M) :
    (U ⊔ V₀) ⊓ centralizer (conjSubgroup V h : Set G) ⊔ V₀ = U ⊔ V₀ := by
  set CH : Subgroup G := H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) with hCHdef
  set H₀ : Subgroup G := conjSubgroup (U ⊔ V₀) h with hH0def
  set U' : Subgroup G := (U ⊔ V₀) ⊓ centralizer (conjSubgroup V h : Set G) with hU'def
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hV0V : V₀ ≤ V := c.cex.hyp.h6.le
  have hUV : U ≤ V := c.cex.le
  have habel : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian hx hy
  have hCH : V ⊓ CH = U ⊔ V₀ := by
    rw [hCHdef]
    exact inf_centralizer_eq_sup h1 h5 h15 hS c
  have hCHh : conjSubgroup CH h = CH := by
    rw [hCHdef, E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer (H := H) hhH),
      conjSubgroup_eq_iff_mem_normalizer.2 (le_normalizer_conjClosure (U ⊔ V₀) H hhH)]
  have hVhCH : conjSubgroup V h ⊓ CH = H₀ := by
    rw [hH0def]
    have h1 := congrArg (fun A : Subgroup G => conjSubgroup A h) hCH
    rw [E3.conjSubgroup_inf, hCHh] at h1
    exact h1
  have hrel : H₀.relIndex (conjSubgroup V h) = 2 := by
    rw [hH0def, E3.relIndex_conjSubgroup,
      E3.relIndex_eq_two_pow c.cex.hyp.isPGroup (U ⊔ V₀), hn, pow_one]
  obtain ⟨v₂, hv₂Vh, hv₂not, hcase⟩ :=
    Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hrel
  have hU'eq : U' = (U ⊔ V₀) ⊓ centralizer ({v₂} : Set G) := by
    rw [hU'def]
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 hx.2) v₂ hv₂Vh).symm⟩
    · intro x hx
      refine ⟨hx.1, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro y hy
      have hxv2 : x * v₂ = v₂ * x := Subgroup.mem_centralizer_singleton_iff.1 hx.2
      have hxI : x ∈ conjClosure (U ⊔ V₀) H := le_conjClosure (U ⊔ V₀) H hx.1
      rcases hcase y hy with hy1 | hy0
      · have hyCH : y * v₂ ∈ CH := by
          have hy' : y * v₂ ∈ conjSubgroup V h ⊓ CH := by
            rw [hVhCH]; exact hy1
          exact hy'.2
        have hcx : (y * v₂) * x = x * (y * v₂) :=
          ((Subgroup.mem_centralizer_iff.1 hyCH.2) x hxI).symm
        have hv2inv : v₂⁻¹ * x = x * v₂⁻¹ := by
          have hh' := congrArg (fun t => v₂⁻¹ * t * v₂⁻¹) hxv2
          simpa [mul_assoc] using hh'
        have hyv : y = (y * v₂) * v₂⁻¹ := by group
        rw [hyv]
        calc ((y * v₂) * v₂⁻¹) * x = (y * v₂) * (v₂⁻¹ * x) := mul_assoc _ _ _
          _ = (y * v₂) * (x * v₂⁻¹) := congrArg (fun t => (y * v₂) * t) hv2inv
          _ = ((y * v₂) * x) * v₂⁻¹ := (mul_assoc _ _ _).symm
          _ = (x * (y * v₂)) * v₂⁻¹ := congrArg (fun t => t * v₂⁻¹) hcx
          _ = x * ((y * v₂) * v₂⁻¹) := mul_assoc _ _ _
      · have hyCH : y ∈ CH := by
          have hy' : y ∈ conjSubgroup V h ⊓ CH := by
            rw [hVhCH]; exact hy0
          exact hy'.2
        exact ((Subgroup.mem_centralizer_iff.1 hyCH.2) x hxI).symm
  have hcardUV : Nat.card (U ⊔ V₀ : Subgroup G) = Nat.card U * Nat.card V₀ :=
    CFSG.card_sup_eq_mul_of_commute U V₀ (fun a ha b hb => habel a (hUV ha) b (hV0V hb))
      c.cex.inf_eq_bot
  have hcardU'V : Nat.card (U' ⊔ V₀ : Subgroup G) = Nat.card U' * Nat.card V₀ := by
    rw [hU'def]
    exact CFSG.card_sup_eq_mul_of_commute _ V₀
      (fun a ha b hb => habel a (inf_le_left.trans (sup_le hUV hV0V) ha) b (hV0V hb))
      (inf_centralizer_conjSubgroup_inf_eq_bot c hh)
  have hcomm : ∀ z ∈ U ⊔ V₀, z * v₂ * z⁻¹ * v₂⁻¹ ∈ conjSubgroup V₀ h := by
    intro z hz
    have hzI : z ∈ conjClosure (U ⊔ V₀) H := le_conjClosure (U ⊔ V₀) H hz
    have hmem : ⁅v₂, z⁆ ∈ conjSubgroup V₀ h :=
      comm_conj_conjClosure_le h1 hS c hhH
        (Subgroup.commutator_mem_commutator hv₂Vh hzI)
    have h2 : z * v₂ * z⁻¹ * v₂⁻¹ = (⁅v₂, z⁆)⁻¹ := by
      rw [commutatorElement_inv]
      rfl
    rw [h2]
    exact (conjSubgroup V₀ h).inv_mem hmem
  have hcard_le : Nat.card U ≤ Nat.card U' := by
    have hcard := CFSG.OddStandard.AltStdSec.SwapPartner.card_le_card_inf_centralizer_mul
      (U ⊔ V₀) (conjSubgroup V₀ h) v₂ hcomm
    rw [← hU'eq, E3.card_conjSubgroup, hcardUV] at hcard
    haveI : Nonempty ↥V₀ := ⟨⟨1, V₀.one_mem⟩⟩
    exact Nat.le_of_mul_le_mul_right hcard Nat.card_pos
  refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left le_sup_right) ?_
  rw [hcardUV, hcardU'V]
  exact Nat.mul_le_mul_right _ hcard_le

theorem eq_sup_zpowers_of_mem_centralizer (c : Cfg1620 M V₀ V U S R H g B) {b y : G}
    (hb : b ∈ R ⊓ (F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G))) (hyH : y ∈ H) (hyM : y ∉ M)
    (hyC : y ∈ centralizer (conjSubgroup U b : Set G)) : R ⊔ Subgroup.zpowers y = H := by
  have hle : R ⊔ Subgroup.zpowers y ≤ H := sup_le c.mem.1 (Subgroup.zpowers_le.2 hyH)
  refine c.min (R ⊔ Subgroup.zpowers y) hle ⟨le_sup_left, ?_, ?_⟩
  · intro hsub
    have hbR : b ∈ R := hb.1
    have hbM : b ∈ M := cTilde_le_M M V₀ V hb.2.1
    have hbyH : b * y * b⁻¹ ∈ R ⊔ Subgroup.zpowers y :=
      (R ⊔ Subgroup.zpowers y).mul_mem
        ((R ⊔ Subgroup.zpowers y).mul_mem (Subgroup.mem_sup_left hbR)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
        ((R ⊔ Subgroup.zpowers y).inv_mem (Subgroup.mem_sup_left hbR))
    have hmem : b * y * b⁻¹ ∈
        (R ⊔ Subgroup.zpowers y) ⊓ centralizer (U : Set G) := by
      refine ⟨hbyH, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro u hu
      have hu' : b⁻¹ * u * b ∈ conjSubgroup U b := by
        rw [mem_conjSubgroup_iff]
        rw [show b * (b⁻¹ * u * b) * b⁻¹ = u by group]
        exact hu
      have hc := (Subgroup.mem_centralizer_iff.1 hyC) (b⁻¹ * u * b) hu'
      calc u * (b * y * b⁻¹) = b * ((b⁻¹ * u * b) * y) * b⁻¹ := by group
        _ = b * (y * (b⁻¹ * u * b)) * b⁻¹ := by rw [hc]
        _ = (b * y * b⁻¹) * u := by group
    have hnot : b * y * b⁻¹ ∉ M := by
      intro h
      refine hyM ?_
      have := M.mul_mem (M.mul_mem (M.inv_mem hbM) h) hbM
      rwa [show b⁻¹ * (b * y * b⁻¹) * b = y by group] at this
    exact hnot (hsub hmem)
  · intro x hx y hy
    exact c.mem.2.2 x (conjClosure_mono le_rfl hle hx) y (conjClosure_mono le_rfl hle hy)

private theorem eq_one_of_odd_of_mul_self_eq_one {X : Type*} [Group X] {z : X}
    (hz : z * z = 1) (ho : Odd (orderOf z)) : z = 1 := by
  have h2 : z ^ 2 = 1 := by rwa [pow_two]
  have hdvd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at ho
    exact absurd ho (by norm_num)

theorem img_eq_sup_zpowers (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (hn : E3.mQuot V (U ⊔ V₀) = 1)
    {t y : LGL 2 Mo.W} (ht : t ∈ Mo.img V) (ht1 : t ≠ 1) (hy : y ∈ Mo.img H) (hy1 : y ≠ 1)
    (hyo : Odd (orderOf y)) (hty : t * y * t⁻¹ = y⁻¹) :
    Mo.img R ⊔ Subgroup.zpowers y = Mo.img H := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have ht2 : t * t = 1 := by
    simpa [pow_two] using (Mo.isElemAbelian_img c.cex.hyp.h6.elemAbelian).2 t ht
  obtain ⟨x, hx, hxt⟩ := NOne.exists_mem_zpowers_conj_eq ht2 hty hyo
  obtain ⟨hH, -, hρ⟩ := Mo.mem_img.1 ((Subgroup.zpowers_le.2 hy) hx)
  have hhH : (hH : G) ∈ H := hH.2
  set t' : LGL 2 Mo.W := x⁻¹ * t * x with ht'def
  have ht'yt : t' = y * t := ht'def.trans hxt
  have hy_eq : y = t' * t := by rw [ht'yt, mul_assoc, ht2, mul_one]
  have ht'2 : t' * t' = 1 := by
    rw [ht'def, show x⁻¹ * t * x * (x⁻¹ * t * x) = x⁻¹ * (t * t) * x by group, ht2]
    group
  have ht'1 : t' ≠ 1 := by
    intro h
    apply ht1
    have hx' : x * t' * x⁻¹ = t := by rw [ht'def]; group
    rw [h, mul_one] at hx'
    have : t = 1 := by simpa using hx'.symm
    exact this
  have hVhH : conjSubgroup V (hH : G) ≤ H := by
    have h := E3.conjSubgroup_mono_left (hH : G) hVH
    rwa [conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer (H := H) hhH)] at h
  have hρinv : Mo.ρ ⟨(hH : G)⁻¹, H.inv_mem hhH⟩ = x⁻¹ := by
    have : (⟨(hH : G)⁻¹, H.inv_mem hhH⟩ : ↥H) = hH⁻¹ := rfl
    rw [this, map_inv, hρ]
  have ht'img : t' ∈ Mo.img (conjSubgroup V (hH : G)) := by
    have hconj : Mo.img (conjSubgroup V (hH : G))
        = cj (Mo.ρ ⟨(hH : G)⁻¹, H.inv_mem hhH⟩) (Mo.img V) := by
      have h := (Mo.img_conj hVH ⟨(hH : G)⁻¹, H.inv_mem hhH⟩).symm
      rwa [inv_inv] at h
    rw [show t' = x⁻¹ * t * x from ht'def, hconj, mem_cj, hρinv,
      show x⁻¹⁻¹ * (x⁻¹ * t * x) * x⁻¹ = t by group]
    exact ht
  have hnot : ¬ conjSubgroup V (hH : G) ≤ M := by
    intro hM
    have ht'inf : t' ∈ Mo.img (H ⊓ M) :=
      Mo.img_mono (le_inf hVhH hM) ht'img
    have hcomm : t' * t = t * t' :=
      img_commute_of_mem_inf h1 h5 h15 hS c Mo hn ht'inf ht
    have hyy : y * y = 1 := by
      rw [hy_eq]
      calc (t' * t) * (t' * t) = t' * (t * t') * t := by group
        _ = t' * (t' * t) * t := by rw [← hcomm]
        _ = t' * t' * (t * t) := by group
        _ = 1 := by simp [ht'2, ht2]
    exact hy1 (eq_one_of_odd_of_mul_self_eq_one hyy hyo)
  set U' : Subgroup G := (U ⊔ V₀) ⊓ centralizer (conjSubgroup V (hH : G) : Set G) with hU'def
  have hU'le : U' ≤ U ⊔ V₀ := by rw [hU'def]; exact inf_le_left
  have hU'inf : U' ⊓ V₀ = ⊥ := by
    rw [hU'def]
    exact inf_centralizer_conjSubgroup_inf_eq_bot c hnot
  have hU'sup : U' ⊔ V₀ = U ⊔ V₀ := by
    rw [hU'def]
    exact sup_inf_centralizer_eq h1 h5 h15 hS c hn hhH hnot
  obtain ⟨b, hb, hbU⟩ := exists_mem_inf_conj_eq h1 hS c hn hU'le hU'inf hU'sup
  obtain ⟨yH, -, hyρ⟩ := Mo.mem_img.1 hy
  have hyH : (yH : G) ∈ H := yH.2
  have hyVsup : y ∈ Mo.img (V ⊔ conjSubgroup V (hH : G)) := by
    have hmem : t' * t ∈ Mo.img (conjSubgroup V (hH : G)) ⊔ Mo.img V :=
      Subgroup.mul_mem_sup ht'img ht
    have hsup : Mo.img (conjSubgroup V (hH : G)) ⊔ Mo.img V
        = Mo.img (V ⊔ conjSubgroup V (hH : G)) :=
      (sup_comm (Mo.img (conjSubgroup V (hH : G))) (Mo.img V)).trans
        (Mo.img_sup hVH hVhH).symm
    rw [← hy_eq, hsup] at hmem
    exact hmem
  set CH : Subgroup G := H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) with hCHdef
  have hy_mem : (yH : G) ∈ (V ⊔ conjSubgroup V (hH : G)) ⊔ CH := by
    rw [hCHdef]
    exact (Mo.ρ_mem_img_iff (S := V ⊔ conjSubgroup V (hH : G)) (sup_le hVH hVhH) hyH).1
      (by rw [hyρ]; exact hyVsup)
  have hVU' : V ≤ centralizer (U' : Set G) := by
    intro v hv
    refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
    exact B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian
      (hU'le.trans (sup_le c.cex.le c.cex.hyp.h6.le) hu) hv
  have hVhU' : conjSubgroup V (hH : G) ≤ centralizer (U' : Set G) := by
    intro v hv
    refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
    have hu' : u ∈ centralizer (conjSubgroup V (hH : G) : Set G) := by
      rw [hU'def] at hu
      exact hu.2
    exact ((Subgroup.mem_centralizer_iff.1 hu') v hv).symm
  have hCHU' : CH ≤ centralizer (U' : Set G) := by
    rw [hCHdef]
    intro ch hch
    refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
    exact (Subgroup.mem_centralizer_iff.1 hch.2) u (le_conjClosure (U ⊔ V₀) H (hU'le hu))
  have hy_cent : (yH : G) ∈ centralizer (U' : Set G) :=
    (sup_le (sup_le hVU' hVhU') hCHU') hy_mem
  have hyM : (yH : G) ∉ M := by
    intro hM
    have hy_inf : y ∈ Mo.img (H ⊓ M) := Mo.mem_img.2 ⟨yH, ⟨hyH, hM⟩, hyρ⟩
    have hcomm : y * t = t * y := img_commute_of_mem_inf h1 h5 h15 hS c Mo hn hy_inf ht
    have hyy : y * y = 1 := by
      have h1' : y⁻¹ = y := by
        have h2' : t * y * t⁻¹ = y := by rw [← hcomm]; group
        rwa [hty] at h2'
      simpa [h1'] using mul_inv_cancel y
    exact hy1 (eq_one_of_odd_of_mul_self_eq_one hyy hyo)
  have hEq : R ⊔ Subgroup.zpowers (yH : G) = H :=
    eq_sup_zpowers_of_mem_centralizer c hb hyH hyM (by rw [hbU]; exact hy_cent)
  have hZpowH : Subgroup.zpowers (yH : G) ≤ H := Subgroup.zpowers_le.2 hyH
  have himg_zpow : Mo.img (Subgroup.zpowers (yH : G)) = Subgroup.zpowers y := by
    have hsub : (Subgroup.zpowers (yH : G)).subgroupOf H = Subgroup.zpowers yH := by
      ext j
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      exact ⟨fun ⟨k, hk⟩ => ⟨k, Subtype.ext (by simpa using hk)⟩,
        fun ⟨k, hk⟩ => ⟨k, by simpa using congrArg Subtype.val hk⟩⟩
    show ((Subgroup.zpowers (yH : G)).subgroupOf H).map Mo.ρ = Subgroup.zpowers y
    rw [hsub, MonoidHom.map_zpowers, hyρ]
  have hmap := congrArg Mo.img hEq
  rw [Mo.img_sup c.mem.1 hZpowH, himg_zpow] at hmap
  exact hmap

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
