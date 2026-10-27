module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGNsq2QuotAut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.CoprimeKernel

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]
variable {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

theorem Datum.hyperplane_img (hD : Datum p N f L Bs Z) (r : MulAut ↥Bs) :
    ggHyperplane (img N f Bs) (MulAut.congr hD.tau r) = img N f (ggHyperplane Bs r) := by
  ext q
  constructor
  · intro hq
    obtain ⟨q', hq'fix, rfl⟩ := Subgroup.mem_map.1 hq
    obtain ⟨b, rfl⟩ := hD.tau.surjective q'
    have hfix : r b = b := by
      have h1 : (MulAut.congr hD.tau r) (hD.tau b) = hD.tau b := hq'fix
      rw [congr_apply_tau] at h1
      exact hD.tau.injective h1
    refine mem_img.2 ⟨⟨(b : G), hD.BsN b.2⟩, ?_, rfl⟩
    exact Subgroup.mem_map.2 ⟨b, hfix, rfl⟩
  · intro hq
    obtain ⟨u, hu, rfl⟩ := mem_img.1 hq
    obtain ⟨b, hbfix, hbu⟩ := Subgroup.mem_map.1 hu
    have hbfix' : r b = b := hbfix
    refine Subgroup.mem_map.2 ⟨hD.tau b, ?_, ?_⟩
    · show (MulAut.congr hD.tau r) (hD.tau b) = hD.tau b
      rw [congr_apply_tau, hbfix']
    · change ((hD.tau b : ↥(img N f Bs)) : Q) = f u
      rw [hD.tau_apply]
      have hub : u = ⟨(b : G), hD.BsN b.2⟩ := Subtype.ext hbu.symm
      rw [hub]

theorem Datum.centralizer_img (hD : Datum p N f L Bs Z) {H : Subgroup G} (hH : H ≤ Bs) :
    img N f (L ⊓ Subgroup.centralizer (H : Set G)) =
      img N f L ⊓ Subgroup.centralizer ((img N f H : Subgroup Q) : Set Q) := by
  ext q
  constructor
  · intro hq
    obtain ⟨u, hu, rfl⟩ := mem_img.1 hq
    obtain ⟨huL, huC⟩ := Subgroup.mem_inf.1 hu
    refine Subgroup.mem_inf.2 ⟨mem_img.2 ⟨u, huL, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨v, hv, rfl⟩ := mem_img.1 (SetLike.mem_coe.1 hw)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 huC _ hv
  · intro hq
    obtain ⟨hqL, hqC⟩ := Subgroup.mem_inf.1 hq
    obtain ⟨u, huL, rfl⟩ := mem_img.1 hqL
    haveI := Fact.mk hD.prime
    have hcomm : ∀ v ∈ H.subgroupOf N, f v * f u = f u * f v := by
      intro v hv
      have hmem : f v ∈ img N f H := mem_img.2 ⟨v, hv, rfl⟩
      exact Subgroup.mem_centralizer_iff.1 hqC (f v) hmem
    obtain ⟨u', hu'f, hu'c⟩ :=
      exists_lift_centralizing (hD.isPGroup_sub hH) hD.not_dvd hcomm
    have hk : u'⁻¹ * u ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hu'f, inv_mul_cancel]
    have hZu : (((u'⁻¹ * u : ↥N)) : G) ∈ Z := (hD.mem_ker_iff _).1 hk
    have hu'L : ((u' : ↥N) : G) ∈ L := by
      have h1 : (u' : ↥N) = u * (u'⁻¹ * u)⁻¹ := by group
      have h2 : ((u' : ↥N) : G) = ((u : ↥N) : G) * (((u'⁻¹ * u : ↥N) : G))⁻¹ :=
        congrArg Subtype.val h1
      rw [h2]
      exact L.mul_mem huL (L.inv_mem (hD.ZL hZu))
    refine mem_img.2 ⟨u', Subgroup.mem_inf.2 ⟨hu'L, ?_⟩, hu'f⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhN : h ∈ N := hD.BsN (hH hh)
    have hc : Commute (⟨h, hhN⟩ : ↥N) u' := hu'c ⟨h, hhN⟩ hh
    exact congrArg Subtype.val hc.eq

theorem Datum.injOn_centralizer (hD : Datum p N f L Bs Z) {H : Subgroup G}
    (hfix : ∀ z ∈ Z, (∀ h ∈ H, h * z = z * h) → z = 1) :
    Function.Injective
      (fun u : ↥((L ⊓ Subgroup.centralizer (H : Set G)).subgroupOf N) => f (u : ↥N)) := by
  intro u₁ u₂ h
  have hk : (u₁ : ↥N)⁻¹ * (u₂ : ↥N) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have h' : f (u₁ : ↥N) = f (u₂ : ↥N) := h
    rw [h', inv_mul_cancel]
  have hZ : (((u₁ : ↥N)⁻¹ * (u₂ : ↥N) : ↥N) : G) ∈ Z := (hD.mem_ker_iff _).1 hk
  have h₁ : ((u₁ : ↥N) : G) ∈ L ⊓ Subgroup.centralizer (H : Set G) := u₁.2
  have h₂ : ((u₂ : ↥N) : G) ∈ L ⊓ Subgroup.centralizer (H : Set G) := u₂.2
  have hcent : ∀ h ∈ H, h * (((u₁ : ↥N)⁻¹ * (u₂ : ↥N) : ↥N) : G) =
      (((u₁ : ↥N)⁻¹ * (u₂ : ↥N) : ↥N) : G) * h := by
    intro h hh
    have e₁ := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 h₁).2 h hh
    have e₂ := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 h₂).2 h hh
    show h * (((u₁ : ↥N) : G)⁻¹ * ((u₂ : ↥N) : G)) = (((u₁ : ↥N) : G)⁻¹ * ((u₂ : ↥N) : G)) * h
    have e₁' : ((u₁ : ↥N) : G)⁻¹ * h = h * ((u₁ : ↥N) : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e₁, mul_assoc, mul_inv_cancel, mul_one]
    calc h * (((u₁ : ↥N) : G)⁻¹ * ((u₂ : ↥N) : G))
        = (h * ((u₁ : ↥N) : G)⁻¹) * ((u₂ : ↥N) : G) := by rw [mul_assoc]
      _ = (((u₁ : ↥N) : G)⁻¹ * h) * ((u₂ : ↥N) : G) := by rw [e₁']
      _ = ((u₁ : ↥N) : G)⁻¹ * (h * ((u₂ : ↥N) : G)) := by rw [mul_assoc]
      _ = ((u₁ : ↥N) : G)⁻¹ * (((u₂ : ↥N) : G) * h) := by rw [e₂]
      _ = (((u₁ : ↥N) : G)⁻¹ * ((u₂ : ↥N) : G)) * h := by rw [mul_assoc]
  have h1 : (u₁ : ↥N)⁻¹ * (u₂ : ↥N) = 1 := Subtype.ext (hfix _ hZ hcent)
  exact Subtype.ext (inv_mul_eq_one.1 h1)

theorem card_img_of_injOn {U : Subgroup G} (hUN : U ≤ N)
    (hinj : Function.Injective fun u : ↥(U.subgroupOf N) => f (u : ↥N)) :
    Nat.card ↥(img N f U) = Nat.card ↥U := by
  unfold img
  rw [card_map_eq_of_inj hinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv

theorem Datum.img_ggOTwoPrime (hD : Datum p N f L Bs Z) {C : Subgroup G} (hCN : C ≤ N)
    (hinj : Function.Injective fun u : ↥(C.subgroupOf N) => f (u : ↥N)) :
    img N f (ggOTwoPrime C) = ggOTwoPrime (img N f C) := by
  apply le_antisymm
  · let K' : Subgroup G := ((ggOTwoPrime (img N f C)).comap f).map N.subtype
    have hsub : ggOTwoPrime C ≤ K' := by
      refine (Subgroup.closure_le K').mpr ?_
      rintro y ⟨hyC, k, hk⟩
      have hyN : y ∈ N := hCN hyC
      refine Subgroup.mem_map.2 ⟨⟨y, hyN⟩, ?_, rfl⟩
      refine Subgroup.subset_closure ⟨mem_img.2 ⟨⟨y, hyN⟩, hyC, rfl⟩, k, ?_⟩
      rw [← map_pow]
      have h1 : (⟨y, hyN⟩ : ↥N) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
      rw [h1, map_one]
    intro q hq
    obtain ⟨u, hu, rfl⟩ := mem_img.1 hq
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 (hsub hu)
    have : w = u := Subtype.ext hwu
    subst this
    exact hw
  · refine (Subgroup.closure_le _).mpr ?_
    rintro q ⟨hqC, k, hk⟩
    obtain ⟨c, hcC, rfl⟩ := mem_img.1 hqC
    have hc1 : c ^ (2 ^ k) = 1 := by
      have h1 : f (c ^ (2 ^ k)) = f 1 := by rw [map_pow, map_one]; exact hk
      have h2 := @hinj ⟨c ^ (2 ^ k), by
          show (((c ^ (2 ^ k) : ↥N)) : G) ∈ C
          have := C.pow_mem hcC (2 ^ k)
          simpa using this⟩ ⟨1, C.one_mem⟩ h1
      exact congrArg Subtype.val h2
    refine mem_img.2 ⟨c, Subgroup.subset_closure ⟨hcC, k, ?_⟩, rfl⟩
    have := congrArg Subtype.val hc1
    simpa using this

theorem Datum.card_ggOTwoPrime_img (hD : Datum p N f L Bs Z) {C : Subgroup G} (hCN : C ≤ N)
    (hinj : Function.Injective fun u : ↥(C.subgroupOf N) => f (u : ↥N)) :
    Nat.card ↥(ggOTwoPrime (img N f C)) = Nat.card ↥(ggOTwoPrime C) := by
  rw [← hD.img_ggOTwoPrime hCN hinj]
  have hle : ggOTwoPrime C ≤ C := ggOTwoPrime_le C
  refine card_img_of_injOn (hle.trans hCN) (fun a b hab => ?_)
  have h := @hinj ⟨(a : ↥N), hle a.2⟩ ⟨(b : ↥N), hle b.2⟩ hab
  exact Subtype.ext (congrArg (fun u : ↥(C.subgroupOf N) => (u : ↥N)) h)

theorem Datum.card_rankOneIn (hD : Datum p N f L Bs Z) {r : MulAut ↥Bs}
    (hfix : ∀ z ∈ Z, (∀ h ∈ ggHyperplane Bs r, h * z = z * h) → z = 1) :
    Nat.card ↥(ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau r)) =
      Nat.card ↥(ggRankOneIn L Bs r) := by
  have hH : ggHyperplane Bs r ≤ Bs := Subgroup.map_subtype_le _
  unfold ggRankOneIn
  rw [hD.hyperplane_img r, ← hD.centralizer_img hH]
  exact hD.card_ggOTwoPrime_img (inf_le_left.trans hD.LN) (hD.injOn_centralizer hfix)

end NsQuot

end CFSG.StandardType

end
