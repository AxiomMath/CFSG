module

public import CFSG.Monster.GMS.ASegAmalgamZeta
public import CFSG.Monster.GMS.S365Center
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3024
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10037
public import Certificates.Certificate10038
public import Certificates.Certificate10039
public import Certificates.Certificate10040
public import Certificates.Certificate10041
public import Certificates.Certificate10042
public import Certificates.Certificate10043
public import Certificates.Certificate10044
public import Certificates.Certificate10045
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate10072
public import Certificates.Certificate10073
public import Certificates.Certificate10074
public import Certificates.Certificate10075
public import Certificates.Certificate10076
public import Certificates.Certificate8955
public import CFSG.Monster.GMS.Facts.Section4Coh

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.S4Assembly CFSG.Monster.GMS.S4Family

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section KeyId

variable {G G' : Type*} [Group G] [Group G'] {a y z : G} {a' y' z' : G'} {A Z : G → G'}

@[expose] def KeyId (a y : G) (A Z : G → G') (e : G') (w : G) : Prop :=
  ∀ k ∈ C[a] ⊓ C[y], A (w * k * w⁻¹) = (Z w * e) * A k * (Z w * e)⁻¹

theorem KeyId.mul (hZ : IsIsoOn Z C[z] C[z']) {w₁ w₂ : G} {e₁ e₂ : G'}
    (hw₁ : w₁ ∈ Xt0 a y ⊓ C[z]) (hw₂ : w₂ ∈ Xt0 a y ⊓ C[z]) (hc : e₁ * Z w₂ = Z w₂ * e₁)
    (h₁ : KeyId a y A Z e₁ w₁) (h₂ : KeyId a y A Z e₂ w₂) :
    KeyId a y A Z (e₁ * e₂) (w₁ * w₂) := by
  intro k hk
  have hk' : w₂ * k * w₂⁻¹ ∈ C[a] ⊓ C[y] := (Xt0.mem_K_iff hw₂.1 k).1 hk
  have e1 : (Z w₁ * e₁) * (Z w₂ * e₂) = Z (w₁ * w₂) * (e₁ * e₂) := by
    rw [hZ.map_mul w₁ hw₁.2 w₂ hw₂.2]
    calc (Z w₁ * e₁) * (Z w₂ * e₂) = Z w₁ * (e₁ * Z w₂) * e₂ := by group
      _ = Z w₁ * (Z w₂ * e₁) * e₂ := by rw [hc]
      _ = Z w₁ * Z w₂ * (e₁ * e₂) := by group
  rw [show w₁ * w₂ * k * (w₁ * w₂)⁻¹ = w₁ * (w₂ * k * w₂⁻¹) * w₁⁻¹ by group, h₁ _ hk',
    h₂ k hk, ← e1]
  group

theorem KeyId.inv (hZ : IsIsoOn Z C[z] C[z']) {w : G} {e : G'} (hw : w ∈ Xt0 a y ⊓ C[z])
    (hc : e * Z w = Z w * e) (h : KeyId a y A Z e w) : KeyId a y A Z e⁻¹ w⁻¹ := by
  intro k hk
  have hk' : w⁻¹ * k * w ∈ C[a] ⊓ C[y] := by
    have := (Xt0.mem_K_iff ((Xt0 a y).inv_mem hw.1) k).1 hk
    rwa [inv_inv] at this
  have h' := h _ hk'
  rw [show w * (w⁻¹ * k * w) * w⁻¹ = k by group] at h'
  have hu : Z w⁻¹ * e⁻¹ = (Z w * e)⁻¹ := by
    rw [iso_map_inv hZ hw.2, mul_inv_rev]
    exact ((Commute.inv_inv (show Commute e (Z w) from hc)).eq).symm
  rw [hu]
  simp only [inv_inv]
  calc A (w⁻¹ * k * w)
      = (Z w * e)⁻¹ * ((Z w * e) * A (w⁻¹ * k * w) * (Z w * e)⁻¹) * (Z w * e) := by group
    _ = (Z w * e)⁻¹ * A k * (Z w * e) := by rw [← h']

theorem KeyId.of_mem (P : AlphaZeta a y z a' y' z' A Z) {w : G} (hw : w ∈ C[a] ⊓ C[z]) :
    KeyId a y A Z 1 w := by
  intro k hk
  rw [iso_map_conj P.hA hw.1 hk.1, ← P.Z_eq_A w hw, mul_one]

end KeyId

section SubgroupW

variable {G G' : Type*} [Group G] [Group G']

@[expose] def asegW0 (A Z : G → G') (a y z : G) {z' : G'} (hZ : IsIsoOn Z C[z] C[z']) :
    Subgroup G where
  carrier := {w | w ∈ Xt0 a y ⊓ C[z] ∧ KeyId a y A Z 1 w}
  one_mem' := ⟨(Xt0 a y ⊓ C[z]).one_mem, fun k _ => by simp [iso_map_one hZ]⟩
  mul_mem' := fun {w₁ w₂} h₁ h₂ => ⟨(Xt0 a y ⊓ C[z]).mul_mem h₁.1 h₂.1, by
    have := KeyId.mul hZ h₁.1 h₂.1 (by rw [one_mul, mul_one]) h₁.2 h₂.2
    rwa [mul_one] at this⟩
  inv_mem' := fun {w} h => ⟨(Xt0 a y ⊓ C[z]).inv_mem h.1, by
    have := KeyId.inv hZ h.1 (by rw [one_mul, mul_one]) h.2
    rwa [inv_one] at this⟩

theorem mem_asegW0 {A Z : G → G'} {a y z : G} {z' : G'} {hZ : IsIsoOn Z C[z] C[z']} {w : G} :
    w ∈ asegW0 A Z a y z hZ ↔ w ∈ Xt0 a y ⊓ C[z] ∧ KeyId a y A Z 1 w := Iff.rfl

end SubgroupW

section Rigid

variable {G : Type*} [Group G]

@[expose] def KAutRigidAt (a y z : G) : Prop :=
  ∀ ψ : ↥(C[a] ⊓ C[y]) ≃* ↥(C[a] ⊓ C[y]),
    (∀ g : ↥(C[a] ⊓ C[y]), (g : G) ∈ C[z] → ψ g = g) →
      (∀ g : ↥(C[a] ⊓ C[y]), ψ g = g) ∨ (∀ g : ↥(C[a] ⊓ C[y]), (ψ g : G) = z * g * z⁻¹)

@[expose] def KAutRigid {G : Type} [Group G] (a z₀ : G) : Prop :=
  ∀ y z : G, ASegData a z₀ y z → KAutRigidAt a y z

theorem kAutRigidAt_of {a y z : G} (hTC : TripleCenter a) (hCA : CentInvAutInnerAt a y)
    (hy : y ∈ twoANbr a a) (h : Comm3 a y z) (hz2 : orderOf z = 2) : KAutRigidAt a y z := by
  intro ψ hψ
  have hzC : z ∈ C[a] := Subgroup.mem_centralizer_singleton_iff.2 h.za
  have hzY : z ∈ C[y] := Subgroup.mem_centralizer_singleton_iff.2 h.zy
  have haZ : a ∈ C[z] := Subgroup.mem_centralizer_singleton_iff.2 h.az
  have hyZ : y ∈ C[z] := Subgroup.mem_centralizer_singleton_iff.2 h.yz
  obtain ⟨c, hc, hconj⟩ := hCA ψ (fun g hg => hψ g (by rw [hg]; exact haZ))
    (fun g hg => hψ g (by rw [hg]; exact hyZ))
  have hcent : ∀ g ∈ C[a] ⊓ C[y] ⊓ C[z], c * g = g * c := by
    intro g hg
    have e : g = c * g * c⁻¹ := by
      have := hconj ⟨g, hg.1⟩
      rwa [hψ ⟨g, hg.1⟩ hg.2] at this
    calc c * g = c * g * c⁻¹ * c := by group
      _ = g * c := by rw [← e]
  have hczC : c ∈ C[z] :=
    Subgroup.mem_centralizer_singleton_iff.2 (hcent z ⟨⟨hzC, hzY⟩, self_mem_centralizer z⟩)
  have hmem8 := hTC a y z (IsConj.refl a) hy ⟨hzC, hzY⟩ hz2 c ⟨hc, hczC⟩ hcent
  have hK : ∀ p : G, (∀ g ∈ C[a] ⊓ C[y], g * p = p * g) → ∀ g ∈ C[a] ⊓ C[y], p * g * p⁻¹ = g :=
    fun p hp g hg => by rw [← hp g hg]; group
  have hKz : ∀ p : G, p * z = z * p → (∀ g ∈ C[a] ⊓ C[y], g * p = p * g) →
      ∀ g ∈ C[a] ⊓ C[y], (p * z) * g * (p * z)⁻¹ = z * g * z⁻¹ := by
    intro p hp hpg g hg
    have c1 : Commute p z := hp
    have c2 : Commute p g := (hpg g hg).symm
    have c3 : Commute p (z * g * z⁻¹) := (c1.mul_right c2).mul_right c1.inv_right
    rw [show p * z * g * (p * z)⁻¹ = p * (z * g * z⁻¹) * p⁻¹ by group, c3.eq]
    group
  have ha : ∀ g ∈ C[a] ⊓ C[y], g * a = a * g :=
    fun g hg => Subgroup.mem_centralizer_singleton_iff.1 hg.1
  have hy' : ∀ g ∈ C[a] ⊓ C[y], g * y = y * g :=
    fun g hg => Subgroup.mem_centralizer_singleton_iff.1 hg.2
  have hay : ∀ g ∈ C[a] ⊓ C[y], g * (a * y) = (a * y) * g := fun g hg => by
    have ga : Commute g a := ha g hg
    have gy : Commute g y := hy' g hg
    exact (ga.mul_right gy).eq
  have hcz : ∀ g : ↥(C[a] ⊓ C[y]), (ψ g : G) = c * g * c⁻¹ := fun g => hconj g
  rcases hmem8 with e | e | e | e | e | e | e | e
  · left; intro g; apply Subtype.ext; rw [hcz, e]; group
  · left; intro g; apply Subtype.ext; rw [hcz, e, hK a ha g g.2]
  · left; intro g; apply Subtype.ext; rw [hcz, e, hK y hy' g g.2]
  · right; intro g; rw [hcz, e]
  · left; intro g; apply Subtype.ext; rw [hcz, e, hK (a * y) hay g g.2]
  · right; intro g; rw [hcz, e, hKz a h.az ha g g.2]
  · right; intro g; rw [hcz, e, hKz y h.yz hy' g g.2]
  · right; intro g; rw [hcz, e, hKz (a * y) (by comm3_simp h) hay g g.2]

theorem kAutRigid_of_twoA
    {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hCA : CentInvAutInnerTwoA a) :
    KAutRigid a z₀ := by
  intro y z D
  exact kAutRigidAt_of (tripleCenter_of I hG)
    (hCA a y (IsConj.refl a) ⟨D.isConj_y, D.isConj_ay⟩) ⟨D.isConj_y, D.isConj_ay⟩ (D.comm3 hG)
    (orderOf_eq_two_of_isConj_z₀ hG D.isConj_z)

end Rigid

section Dichotomy

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {d₀ : B} {a z₀ y z : G}
  {a' y' z' : G'} {A Z : G → G'}

theorem keyId_dichotomy (hKR : KAutRigidAt a y z) (hG : GMSF1Type d₀ a z₀) (D : ASegData a z₀ y z)
    (P : AlphaZeta a y z a' y' z' A Z) {w : G} (hw : w ∈ Xt0 a y ⊓ C[z]) :
    KeyId a y A Z 1 w ∨ KeyId a y A Z z' w := by
  have h := D.comm3 hG
  have hyC : y ∈ C[a] := Subgroup.mem_centralizer_singleton_iff.2 h.ya
  have hzC : z ∈ C[a] := Subgroup.mem_centralizer_singleton_iff.2 h.za
  have haZ : a ∈ C[z] := Subgroup.mem_centralizer_singleton_iff.2 D.comm_az
  have hyZ : y ∈ C[z] := Subgroup.mem_centralizer_singleton_iff.2 D.comm_yz
  have hZw : Z w ∈ Xt0 a' y' := by
    have := (mem_Xt0_iff_of_isIsoOn P.hZ haZ hyZ hw.2).2 hw.1
    rwa [P.Z_a, P.Z_y] at this
  have hK : ∀ x, x ∈ C[a] ⊓ C[y] ↔ w * x * w⁻¹ ∈ C[a] ⊓ C[y] := Xt0.mem_K_iff hw.1
  have hK' : ∀ x, x ∈ C[a'] ⊓ C[y'] ↔ (Z w)⁻¹ * x * (Z w)⁻¹⁻¹ ∈ C[a'] ⊓ C[y'] :=
    Xt0.mem_K_iff ((Xt0 a' y').inv_mem hZw)
  have hAK : IsIsoOn A (C[a] ⊓ C[y]) (C[a'] ⊓ C[y']) := by
    have := isIsoOn_inf_centralizer P.hA hyC
    rwa [P.A_y] at this
  have h₂ : IsIsoOn (fun g => (Z w)⁻¹ * A (w * g * w⁻¹) * (Z w)⁻¹⁻¹) (C[a] ⊓ C[y])
      (C[a'] ⊓ C[y']) :=
    isIsoOn_comp (isIsoOn_comp (isIsoOn_conj_of_iff w hK) hAK) (isIsoOn_conj_of_iff (Z w)⁻¹ hK')
  have hval : ∀ c ∈ C[a] ⊓ C[y] ⊓ C[z], (Z w)⁻¹ * A (w * c * w⁻¹) * (Z w)⁻¹⁻¹ = A c := by
    intro c hc
    have hwcK : w * c * w⁻¹ ∈ C[a] ⊓ C[y] := (hK c).1 hc.1
    have hwcZ : w * c * w⁻¹ ∈ C[z] :=
      (C[z]).mul_mem ((C[z]).mul_mem hw.2 hc.2) ((C[z]).inv_mem hw.2)
    rw [← P.Z_eq_A _ ⟨hwcK.1, hwcZ⟩, iso_map_conj P.hZ hw.2 hc.2, P.Z_eq_A c ⟨hc.1.1, hc.2⟩]
    group
  let ψ : ↥(C[a] ⊓ C[y]) ≃* ↥(C[a] ⊓ C[y]) := (isoEquiv h₂).trans (isoEquiv hAK).symm
  have hψ : ∀ g : ↥(C[a] ⊓ C[y]),
      A (ψ g : G) = (Z w)⁻¹ * A (w * g * w⁻¹) * (Z w)⁻¹⁻¹ := fun g =>
    congrArg Subtype.val ((isoEquiv hAK).apply_symm_apply (isoEquiv h₂ g))
  have hfix : ∀ g : ↥(C[a] ⊓ C[y]), (g : G) ∈ C[z] → ψ g = g := by
    intro g hg
    refine Subtype.ext (hAK.injOn (ψ g).2 g.2 ?_)
    rw [hψ g, hval g ⟨g.2, hg⟩]
  rcases hKR ψ hfix with hk | hk
  · left
    intro g hg
    have e := hψ ⟨g, hg⟩
    rw [hk ⟨g, hg⟩] at e
    calc A (w * g * w⁻¹) = Z w * ((Z w)⁻¹ * A (w * g * w⁻¹) * (Z w)⁻¹⁻¹) * (Z w)⁻¹ := by group
      _ = (Z w * 1) * A g * (Z w * 1)⁻¹ := by rw [← e]; group
  · right
    intro g hg
    have e := hψ ⟨g, hg⟩
    rw [hk ⟨g, hg⟩, iso_map_conj P.hA hzC hg.1, P.A_z] at e
    calc A (w * g * w⁻¹) = Z w * ((Z w)⁻¹ * A (w * g * w⁻¹) * (Z w)⁻¹⁻¹) * (Z w)⁻¹ := by group
      _ = (Z w * z') * A g * (Z w * z')⁻¹ := by rw [← e]; group

end Dichotomy

section Main

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {d₀ : B} {a z₀ y z : G}
  {a' y' z' : G'} {A Z : G → G'}

theorem key_identity
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hKR : KAutRigidAt a y z) (D : ASegData a z₀ y z) (P : AlphaZeta a y z a' y' z' A Z) :
    ∀ w ∈ Xt0 a y ⊓ C[z], ∀ k ∈ C[a] ⊓ C[y], A (w * k * w⁻¹) = Z w * A k * (Z w)⁻¹ := by
  have EL := eightGroupLines_of I hG
  have h := D.comm3 hG
  have hne := D.a_ne_y hG
  obtain ⟨s, hs1, hs2, hs3⟩ := D.exists_s EL hG
  obtain ⟨t, ht1, ht2, ht3⟩ := D.exists_t' EL hG
  obtain ⟨r, hr1, hr2, hr3⟩ := D.exists_r₀ EL hG
  have hsW : s ∈ Xt0 a y ⊓ C[z] :=
    ⟨mem_Xt0_of_fix_or_swap h (Or.inr ⟨hs1, hs2⟩), mem_centralizer_of_conj_eq hs3⟩
  have htW : t ∈ Xt0 a y ⊓ C[z] :=
    ⟨mem_Xt0_of_transposition h ht1 ht2, mem_centralizer_of_conj_eq ht3⟩
  have hrW : r ∈ Xt0 a y ⊓ C[z] :=
    ⟨mem_Xt0_of_cycle h hr1 hr2, mem_centralizer_of_conj_eq hr3⟩
  have hKW : ∀ k ∈ C[a] ⊓ C[y] ⊓ C[z], k ∈ asegW0 A Z a y z P.hZ := fun k hk =>
    mem_asegW0.2 ⟨⟨K_le_Xt0 a y hk.1, hk.2⟩, KeyId.of_mem P ⟨hk.1.1, hk.2⟩⟩
  have htW₀ : t ∈ asegW0 A Z a y z P.hZ :=
    mem_asegW0.2 ⟨htW, KeyId.of_mem P
      ⟨mem_centralizer_of_conj_eq ht1, mem_centralizer_of_conj_eq ht3⟩⟩
  have hcz : ∀ u ∈ C[z], z'⁻¹ * Z u = Z u * z'⁻¹ := fun u hu => by
    have c1 : Commute (Z u) z' := Subgroup.mem_centralizer_singleton_iff.1 (P.hZ.map_mem u hu)
    exact c1.inv_right.eq.symm
  have hcz' : ∀ u ∈ C[z], z' * Z u = Z u * z' := fun u hu => by
    have c1 : Commute (Z u) z' := Subgroup.mem_centralizer_singleton_iff.1 (P.hZ.map_mem u hu)
    exact c1.eq.symm
  have hsW₀ : s ∈ asegW0 A Z a y z P.hZ := by
    have hm : r⁻¹ * t * r ∈ asegW0 A Z a y z P.hZ := by
      rcases keyId_dichotomy hKR hG D P hrW with hr0 | hr1'
      · exact (asegW0 A Z a y z P.hZ).mul_mem ((asegW0 A Z a y z P.hZ).mul_mem
          ((asegW0 A Z a y z P.hZ).inv_mem (mem_asegW0.2 ⟨hrW, hr0⟩)) htW₀)
          (mem_asegW0.2 ⟨hrW, hr0⟩)
      · refine mem_asegW0.2 ⟨(Xt0 a y ⊓ C[z]).mul_mem ((Xt0 a y ⊓ C[z]).mul_mem
          ((Xt0 a y ⊓ C[z]).inv_mem hrW) htW) hrW, ?_⟩
        have i1 := KeyId.inv P.hZ hrW (hcz' r hrW.2) hr1'
        have i2 := KeyId.mul P.hZ ((Xt0 a y ⊓ C[z]).inv_mem hrW) htW (hcz t htW.2) i1
          (mem_asegW0.1 htW₀).2
        have i3 := KeyId.mul P.hZ ((Xt0 a y ⊓ C[z]).mul_mem ((Xt0 a y ⊓ C[z]).inv_mem hrW) htW)
          hrW (by rw [mul_one]; exact hcz r hrW.2) i2 hr1'
        rwa [show z'⁻¹ * 1 * z' = 1 by simp] at i3
    have e1 : r⁻¹ * (a * y) * r = y := by rw [← hr2]; group
    have e2 : r⁻¹ * y * r = a := by rw [← hr1]; group
    have hmK : (r⁻¹ * t * r)⁻¹ * s ∈ C[a] ⊓ C[y] := by
      rw [inv_mul_mem_K_iff]
      constructor
      · rw [hs1]
        calc y = r⁻¹ * (a * y) * r := e1.symm
          _ = r⁻¹ * (t * y * t⁻¹) * r := by rw [ht2]
          _ = r⁻¹ * (t * (r * a * r⁻¹) * t⁻¹) * r := by rw [hr1]
          _ = (r⁻¹ * t * r) * a * (r⁻¹ * t * r)⁻¹ := by group
      · rw [hs2]
        calc a = r⁻¹ * y * r := e2.symm
          _ = r⁻¹ * (a * (a * y)) * r := by rw [show a * (a * y) = y by comm3_simp h]
          _ = r⁻¹ * ((t * a * t⁻¹) * (t * y * t⁻¹)) * r := by rw [ht1, ht2]
          _ = r⁻¹ * (t * (a * y) * t⁻¹) * r := by group
          _ = r⁻¹ * (t * (r * y * r⁻¹) * t⁻¹) * r := by rw [hr2]
          _ = (r⁻¹ * t * r) * y * (r⁻¹ * t * r)⁻¹ := by group
    have hmz : (r⁻¹ * t * r)⁻¹ * s ∈ C[z] :=
      (C[z]).mul_mem ((C[z]).inv_mem (mem_asegW0.1 hm).1.2) hsW.2
    have := (asegW0 A Z a y z P.hZ).mul_mem hm (hKW _ ⟨hmK, hmz⟩)
    rwa [mul_inv_cancel_left] at this
  have hW : ∀ w ∈ Xt0 a y ⊓ C[z], w ∈ asegW0 A Z a y z P.hZ := by
    intro w hw
    obtain ⟨m, hm, hk⟩ := exists_mem_inv_mul_mem_K h hne hs1 hs2 ht1 ht2 (asegW0 A Z a y z P.hZ)
      hsW₀ htW₀ hw.1
    have hmz : m⁻¹ * w ∈ C[z] := (C[z]).mul_mem ((C[z]).inv_mem (mem_asegW0.1 hm).1.2) hw.2
    have := (asegW0 A Z a y z P.hZ).mul_mem hm (hKW _ ⟨hk, hmz⟩)
    rwa [mul_inv_cancel_left] at this
  intro w hw k hk
  rw [(mem_asegW0.1 (hW w hw)).2 k hk, mul_one]

end Main

end CFSG.Monster.GMS
