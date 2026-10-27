module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.GL83PartI.I_24_3.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow

open Subgroup

variable {G : Type} [Group G]

theorem isSubnormal_barImage {L K : Subgroup G} (h : CFSG.Open.IsSubnormal K L) :
    CFSG.Open.IsSubnormal (barImage L K) ⊤ := by
  have hsub : (K.subgroupOf L).IsSubnormal := h.subgroupOf
  have htop : CFSG.Open.IsSubnormal (K.subgroupOf L) ⊤ := .of_mathlib hsub
  have hmap := htop.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hmap

theorem commutator_barImage {L K : Subgroup G} (hKL : K ≤ L) (h : ⁅K, K⁆ = K) :
    ⁅barImage L K, barImage L K⁆ = barImage L K := by
  have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr h
  have hperf' : Group.IsPerfect ↥(K.subgroupOf L) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKL).symm.surjective
  have hcomm : ⁅K.subgroupOf L, K.subgroupOf L⁆ = K.subgroupOf L :=
    Subgroup.isPerfect_iff.mp hperf'
  show ⁅(K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
      (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))⁆ =
      (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  rw [← Subgroup.map_commutator, hcomm]

theorem barImage_ne_bot [Finite G] {L K : Subgroup G} (hK : K ∈ calC L) : barImage L K ≠ ⊥ := by
  obtain ⟨hsub, hperf, hquasi⟩ := hK
  intro hbot
  have hle : K.subgroupOf L ≤ CFSG.pCore 2 ↥L := by
    have hker : K.subgroupOf L ≤ (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker :=
      (Subgroup.map_eq_bot_iff (K.subgroupOf L)).mp hbot
    simpa [QuotientGroup.ker_mk'] using hker
  have hp2 : IsPGroup 2 ↥(K.subgroupOf L) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).to_le hle
  have hpK : IsPGroup 2 ↥K := by
    have hm : IsPGroup 2 ↥((K.subgroupOf L).map L.subtype) := hp2.map L.subtype
    rwa [Subgroup.map_subgroupOf_eq_of_le hsub.le] at hm
  have hperfK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  have hntK : Nontrivial ↥K := by
    letI : Nontrivial (Bar2 K ⧸ Subgroup.center (Bar2 K)) := hquasi.2.toNontrivial
    have hntBar : Nontrivial (Bar2 K) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (Bar2 K))).nontrivial
    letI : Nontrivial (Bar2 K) := hntBar
    exact (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K)).nontrivial
  haveI : Nontrivial ↥K := hntK
  exact Group.IsPerfect.not_isNilpotent ↥K hpK.isNilpotent

theorem eq_bot_of_le_center {X : Type*} [Group X] {H : Subgroup X} (hH : H ≤ center X)
    (hperf : ⁅H, H⁆ = H) : H = ⊥ := by
  have hcomm : ⁅H, H⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hH.trans (Subgroup.center_le_centralizer (H : Set X)))
  rw [← hperf]
  exact hcomm

private theorem le_or_commutator_eq_bot_of_normal_isQuasisimple {X : Type*} [Group X]
    {K H : Subgroup X} (hK : K.Normal) (hq : CFSG.Open.IsQuasisimple ↥K)
    (hH : H.IsSubnormal) : K ≤ H ∨ ⁅K, H⁆ = ⊥ := by
  haveI : K.Normal := hK
  induction hH with
  | top => exact Or.inl le_top
  | step H M hHM hMK hHnorm ih =>
    rcases ih with hKM | hcommKM
    ·
      have hKH_le : ⁅K, H⁆ ≤ K ⊓ H := by
        refine le_inf (Subgroup.commutator_le_left K H) ?_
        rw [Subgroup.commutator_le]
        intro k hk h hh
        have hconj : k * h * k⁻¹ ∈ H :=
          (Subgroup.normal_subgroupOf_iff hHM).mp hHnorm h k hh (hKM hk)
        rw [commutatorElement_def]
        exact H.mul_mem hconj (H.inv_mem hh)
      have hinf_norm : ((K ⊓ H).subgroupOf K).Normal := by
        rw [Subgroup.normal_subgroupOf_iff inf_le_left]
        intro x k hx hk
        refine ⟨K.mul_mem (K.mul_mem hk hx.1) (K.inv_mem hk), ?_⟩
        exact (Subgroup.normal_subgroupOf_iff hHM).mp hHnorm x k hx.2 (hKM hk)
      haveI : ((K ⊓ H).subgroupOf K).Normal := hinf_norm
      rcases GL83.I243.normal_le_center_or_eq_top hq ((K ⊓ H).subgroupOf K) with hcen | htop
      ·
        right
        have hcentral : ⁅K, H⁆ ≤ Subgroup.centralizer (K : Set X) := by
          intro x hx
          have hxKH : x ∈ K ⊓ H := hKH_le hx
          have hxsub : (⟨x, hxKH.1⟩ : ↥K) ∈ (K ⊓ H).subgroupOf K := by
            rw [Subgroup.mem_subgroupOf]
            exact hxKH
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen hxsub) ⟨y, hy⟩)
        have h1 : ⁅⁅K, H⁆, K⁆ = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral
        have h2 : ⁅⁅H, K⁆, K⁆ = ⊥ := by
          rw [Subgroup.commutator_comm H K]
          exact h1
        have h3 : ⁅⁅K, K⁆, H⁆ = ⊥ :=
          Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := K) (H₃ := H) h1 h2
        have hKK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.2 hq.1)
        simpa [hKK] using h3
      ·
        left
        have hKle : K ≤ K ⊓ H := (Subgroup.subgroupOf_eq_top).mp htop
        exact hKle.trans inf_le_right
    ·
      right
      have hle : ⁅K, H⁆ ≤ ⁅K, M⁆ := Subgroup.commutator_mono le_rfl hHM
      rw [hcommKM] at hle
      exact le_bot_iff.mp hle

theorem le_center_or_eq_top_of_isSubnormal {X : Type*} [Group X]
    (hX : IsSimpleGroup X ∨ CFSG.Open.IsQuasisimple X) {H : Subgroup X}
    (hH : CFSG.Open.IsSubnormal H ⊤) : H ≤ center X ∨ H = ⊤ := by
  rcases hX with hsimple | hq
  · letI : IsSimpleGroup X := hsimple
    rcases hH.eq_bot_or_top with hbot | htop
    · exact Or.inl (hbot ▸ bot_le)
    · exact Or.inr htop
  · rcases le_or_commutator_eq_bot_of_normal_isQuasisimple (K := ⊤) (H := H)
      inferInstance ((CFSG.Open.IsQuasisimple.congr Subgroup.topEquiv).mpr hq)
      (CFSG.Open.IsSubnormal.top_iff.mp hH) with hle | hcomm
    · exact Or.inr (top_le_iff.mp hle)
    · exact Or.inl ((Subgroup.commutator_top_left_eq_bot_iff_le_center).mp hcomm)

private theorem eq_left_or_eq_top_of_le_of_centralizes {X : Type*} [Group X]
    {K L H : Subgroup X} (hsup : K ⊔ L = ⊤)
    (hcomm : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a)
    (hq : CFSG.Open.IsQuasisimple ↥K) (hKnorm : K.Normal) (hLnorm : L.Normal)
    (hLH : L ≤ H) (hKH : ⁅K, H⁆ = ⊥) (hH : CFSG.Open.IsSubnormal H ⊤)
    (hperf : ⁅H, H⁆ = H) : H = L ∨ H = ⊤ := by
  have hinf : CFSG.Open.IsSubnormal (K ⊓ H) K := by
    simpa [inf_comm] using hH.inf K
  have hsubK : CFSG.Open.IsSubnormal ((K ⊓ H).subgroupOf K) ⊤ :=
    .of_mathlib hinf.subgroupOf
  have hsup' : L ⊔ K = ⊤ := by rw [sup_comm]; exact hsup
  rcases le_center_or_eq_top_of_isSubnormal (X := ↥K) (Or.inr hq) hsubK with hcen | htop
  ·
    left
    have hHle : H ≤ L ⊔ Subgroup.center X := by
      intro h hh
      rcases (Subgroup.mem_sup_of_normal_right (s := L) (t := K)).mp
        (hsup' ▸ Subgroup.mem_top h) with ⟨l, hl, k, hk, hlk⟩
      have hkH : k ∈ H := by
        have hk_eq : k = l⁻¹ * h := by rw [← hlk]; group
        rw [hk_eq]
        exact H.mul_mem (H.inv_mem (hLH hl)) hh
      have hkKH : k ∈ K ⊓ H := ⟨hk, hkH⟩
      have hkZ : k ∈ Subgroup.center X := by
        have hksub : (⟨k, hk⟩ : ↥K) ∈ (K ⊓ H).subgroupOf K := by
          rw [Subgroup.mem_subgroupOf]
          exact hkKH
        rw [Subgroup.mem_center_iff]
        intro g
        rcases (Subgroup.mem_sup_of_normal_right (s := L) (t := K)).mp
          (hsup' ▸ Subgroup.mem_top g) with ⟨l', hl', k', hk', hlk'⟩
        have hkk' : k' * k = k * k' :=
          congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen hksub) ⟨k', hk'⟩)
        have hkl' : k * l' = l' * k := hcomm k hk l' hl'
        calc g * k = (l' * k') * k := by rw [← hlk']
          _ = l' * (k' * k) := by rw [mul_assoc]
          _ = l' * (k * k') := by rw [hkk']
          _ = (l' * k) * k' := by rw [mul_assoc]
          _ = (k * l') * k' := by rw [hkl']
          _ = k * (l' * k') := by rw [mul_assoc]
          _ = k * g := by rw [← hlk']
      refine (Subgroup.mem_sup_of_normal_left (s := L) (t := Subgroup.center X)).mpr
        ⟨l, hl, k, hkZ, ?_⟩
      exact hlk
    have hcomm_le : ⁅H, H⁆ ≤ L := by
      have hmono : ⁅H, H⁆ ≤ ⁅L ⊔ Subgroup.center X, L ⊔ Subgroup.center X⁆ :=
        Subgroup.commutator_mono hHle hHle
      refine hmono.trans ?_
      haveI : (L ⊔ Subgroup.center X).Normal := Subgroup.sup_normal L (Subgroup.center X)
      have hC₁ : ⁅Subgroup.center X, L⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (Subgroup.center_le_centralizer (L : Set X))
      have hL₁ : ⁅L, Subgroup.center X⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact hC₁
      have hCC : ⁅Subgroup.center X, Subgroup.center X⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (Subgroup.center_le_centralizer (Subgroup.center X : Set X))
      calc ⁅L ⊔ Subgroup.center X, L ⊔ Subgroup.center X⁆
          = ⁅L, L ⊔ Subgroup.center X⁆ ⊔ ⁅Subgroup.center X, L ⊔ Subgroup.center X⁆ :=
              Subgroup.commutator_sup_right L (Subgroup.center X) (L ⊔ Subgroup.center X)
        _ = (⁅L, L⁆ ⊔ ⁅L, Subgroup.center X⁆) ⊔
              (⁅Subgroup.center X, L⁆ ⊔ ⁅Subgroup.center X, Subgroup.center X⁆) := by
              rw [Subgroup.commutator_sup_left (N := L) (H := L) (K := Subgroup.center X),
                Subgroup.commutator_sup_left (N := Subgroup.center X) (H := L)
                  (K := Subgroup.center X)]
        _ = ⁅L, L⁆ := by rw [hL₁, hC₁, hCC]; simp
        _ ≤ L := Subgroup.commutator_le_self L
    exact le_antisymm (hperf ▸ hcomm_le) hLH
  ·
    right
    apply top_le_iff.mp
    rw [← hsup]
    exact sup_le (((Subgroup.subgroupOf_eq_top).mp htop).trans inf_le_right) hLH

theorem eq_or_eq_or_eq_top_of_sup {X : Type*} [Group X] {K₁ K₂ H : Subgroup X}
    (hsup : K₁ ⊔ K₂ = ⊤) (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (h₁ : CFSG.Open.IsQuasisimple ↥K₁) (h₂ : CFSG.Open.IsQuasisimple ↥K₂)
    (hH : CFSG.Open.IsSubnormal H ⊤) (hperf : ⁅H, H⁆ = H) (hne : H ≠ ⊥) :
    H = K₁ ∨ H = K₂ ∨ H = ⊤ := by
  have hK₂central : K₂ ≤ Subgroup.centralizer (K₁ : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcomm y hy x hx
  have hK₁central : K₁ ≤ Subgroup.centralizer (K₂ : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y hy).symm
  have hK₁norm : K₁.Normal := by
    have htop : Subgroup.normalizer (K₁ : Set X) = ⊤ := by
      rw [eq_top_iff, ← hsup]
      exact sup_le Subgroup.le_normalizer
        (hK₂central.trans (Subgroup.centralizer_le_normalizer (K₁ : Set X)))
    exact (Subgroup.normalizer_eq_top_iff).mp htop
  have hK₂norm : K₂.Normal := by
    have htop : Subgroup.normalizer (K₂ : Set X) = ⊤ := by
      rw [eq_top_iff, ← hsup]
      exact sup_le (hK₁central.trans (Subgroup.centralizer_le_normalizer (K₂ : Set X)))
        Subgroup.le_normalizer
    exact (Subgroup.normalizer_eq_top_iff).mp htop
  have hHsub := CFSG.Open.IsSubnormal.top_iff.mp hH
  rcases le_or_commutator_eq_bot_of_normal_isQuasisimple hK₁norm h₁ hHsub with hK₁H | hK₁c
  · rcases le_or_commutator_eq_bot_of_normal_isQuasisimple hK₂norm h₂ hHsub with hK₂H | hK₂c
    ·
      right; right
      apply top_le_iff.mp
      rw [← hsup]
      exact sup_le hK₁H hK₂H
    ·
      have hcomm' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb =>
        (hcomm b hb a ha).symm
      have hsup' : K₂ ⊔ K₁ = ⊤ := by rw [sup_comm]; exact hsup
      rcases eq_left_or_eq_top_of_le_of_centralizes (K := K₂) (L := K₁) (H := H)
        hsup' hcomm' h₂ hK₂norm hK₁norm hK₁H hK₂c hH hperf with h | h
      · left; exact h
      · right; right; exact h
  · rcases le_or_commutator_eq_bot_of_normal_isQuasisimple hK₂norm h₂ hHsub with hK₂H | hK₂c
    ·
      rcases eq_left_or_eq_top_of_le_of_centralizes (K := K₁) (L := K₂) (H := H)
        hsup hcomm h₁ hK₁norm hK₂norm hK₂H hK₁c hH hperf with h | h
      · right; left; exact h
      · right; right; exact h
    ·
      exfalso
      have hHcenter : H ≤ Subgroup.center X := by
        intro h hh
        rw [Subgroup.mem_center_iff]
        intro g
        rcases (Subgroup.mem_sup_of_normal_left (s := K₁) (t := K₂)).mp
          (hsup ▸ Subgroup.mem_top g) with ⟨a, ha, b, hb, hab⟩
        have ha' : a * h = h * a :=
          (Subgroup.mem_centralizer_iff.mp
            ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hK₁c) ha) h hh).symm
        have hb' : b * h = h * b :=
          (Subgroup.mem_centralizer_iff.mp
            ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hK₂c) hb) h hh).symm
        calc g * h = (a * b) * h := by rw [← hab]
          _ = a * (b * h) := by rw [mul_assoc]
          _ = a * (h * b) := by rw [hb']
          _ = (a * h) * b := by rw [mul_assoc]
          _ = (h * a) * b := by rw [ha']
          _ = h * (a * b) := by rw [mul_assoc]
          _ = h * g := by rw [← hab]
      exact hne (eq_bot_of_le_center hHcenter hperf)

end CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow
