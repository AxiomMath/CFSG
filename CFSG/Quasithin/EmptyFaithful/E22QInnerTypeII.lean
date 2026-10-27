module

public import CFSG.Quasithin.EmptyFaithful.E22QWr
import CFSG.Quasithin.EmptyFaithful.E22PL2Psl
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.EmptyFaithful.E22QLift
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E22L2 CFSG.GorensteinWalter

section Aux

variable {G : Type} [Group G]

theorem typeIIi_exists_mul {P Q : Subgroup G} (hPQ : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) {x : G}
    (hx : x ∈ P ⊔ Q) : ∃ a ∈ P, ∃ b ∈ Q, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ P, ∃ b ∈ Q, x = a * b}
      one_mem' := ⟨1, P.one_mem, 1, Q.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', P.mul_mem ha ha', b * b', Q.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hPQ a' ha' b hb]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, P.inv_mem ha, b⁻¹, Q.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact ((Commute.inv_inv (hPQ a ha b hb)).eq).symm }
  have hle : P ⊔ Q ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, Q.one_mem, by simp⟩) (fun b hb => ⟨1, P.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem typeIIi_unique {J₁ J₂ : Subgroup G} (hdisj : J₁ ⊓ J₂ = ⊥) {a a' b b' : G} (ha : a ∈ J₁)
    (ha' : a' ∈ J₁) (hb : b ∈ J₂) (hb' : b' ∈ J₂) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a ∈ J₁ ⊓ J₂ := by
    refine ⟨J₁.mul_mem (J₁.inv_mem ha') ha, ?_⟩
    have : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    rw [this]
    exact J₂.mul_mem hb' (J₂.inv_mem hb)
  rw [hdisj, Subgroup.mem_bot] at h1
  have haa : a = a' := by
    have := mul_eq_one_iff_eq_inv.mp h1
    simpa using this.symm
  subst haa
  exact ⟨rfl, mul_left_cancel h⟩

theorem typeIIi_swap {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G} (h : Wr p T M J₁ J₂ z₁) {s : G}
    (hs : s ∈ T)
    (hsn : s ∉ Subgroup.normalizer (J₁ : Set G)) : conjSub s J₁ = J₂ ∧ conjSub s J₂ = J₁ := by
  have hne : J₁ ≠ J₂ := by
    intro heq
    have h1 : z₁ ∈ J₁ ⊓ J₂ := ⟨h.z₁_mem, heq ▸ h.z₁_mem⟩
    rw [h.disj, Subgroup.mem_bot] at h1
    have := h.z₁_ord
    rw [h1, orderOf_one] at this
    omega
  have h1 : conjSub s J₁ = J₂ := by
    rcases h.perm s hs with h1 | h1
    · exact absurd (conjSub_eq_iff_mem_normalizer.mp h1) hsn
    · exact h1
  refine ⟨h1, ?_⟩
  have h2 : conjSub s J₂ = conjSub (s * s) J₁ := by rw [conjSub_mul, h1]
  rcases h.perm (s * s) (T.mul_mem hs hs) with h3 | h3
  · rw [h2, h3]
  · exact absurd ((conjSub_inj s).mp (h2.trans (h3.trans h1.symm))).symm hne

theorem typeIIi_exists_Y [Finite G] {A T J₁ J₂ : Subgroup G} {c : G}
    (hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) (hdisj : J₁ ⊓ J₂ = ⊥)
    (hc1 : conjSub c J₁ = J₂) (hc2 : conjSub c J₂ = J₁)
    (hcA : ∀ a ∈ A, a * c = c * a) (hAab : IsElemAbelian 2 A)
    (hAT : A ≤ (T ⊓ J₁) ⊔ (T ⊓ J₂)) :
    ∃ Y : Subgroup G, Y ≤ T ⊓ J₁ ∧ IsElemAbelian 2 Y ∧ Nat.card A ≤ Nat.card Y ∧
      (∀ y ∈ Y, y * (c * y * c⁻¹) ∈ A) ∧ (∀ a ∈ A, ∃ y ∈ Y, a = y * (c * y * c⁻¹)) := by
  have hcJ1 : ∀ y ∈ J₁, c * y * c⁻¹ ∈ J₂ := fun y hy => by
    rw [← hc1]; exact mem_conjSub_of_mem hy
  have hcJ2 : ∀ y ∈ J₂, c * y * c⁻¹ ∈ J₁ := fun y hy => by
    rw [← hc2]; exact mem_conjSub_of_mem hy
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have key : ∀ y z : G, y ∈ J₁ → z ∈ J₁ →
      y * (c * y * c⁻¹) * (z * (c * z * c⁻¹)) = (y * z) * ((c * y * c⁻¹) * (c * z * c⁻¹)) := by
    intro y z hy hz
    calc y * (c * y * c⁻¹) * (z * (c * z * c⁻¹))
        = y * ((c * y * c⁻¹) * z) * (c * z * c⁻¹) := by group
      _ = y * (z * (c * y * c⁻¹)) * (c * z * c⁻¹) := by
        rw [← hcomm z hz _ (hcJ1 y hy)]
      _ = (y * z) * ((c * y * c⁻¹) * (c * z * c⁻¹)) := by group
  have hdecomp : ∀ a ∈ A, ∃ y ∈ T ⊓ J₁, a = y * (c * y * c⁻¹) := by
    intro a ha
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := typeIIi_exists_mul (P := T ⊓ J₁) (Q := T ⊓ J₂)
      (fun a ha b hb => hcomm a ha.2 b hb.2) (hAT ha)
    have h1 : c * t₁ * c⁻¹ ∈ J₂ := hcJ1 t₁ ht₁.2
    have h2 : c * t₂ * c⁻¹ ∈ J₁ := hcJ2 t₂ ht₂.2
    have hc' : c * (t₁ * t₂) * c⁻¹ = t₁ * t₂ := by
      rw [← hcA _ ha]; group
    have h3 : t₁ * t₂ = (c * t₂ * c⁻¹) * (c * t₁ * c⁻¹) := by
      calc t₁ * t₂ = c * (t₁ * t₂) * c⁻¹ := hc'.symm
        _ = (c * t₁ * c⁻¹) * (c * t₂ * c⁻¹) := by group
        _ = (c * t₂ * c⁻¹) * (c * t₁ * c⁻¹) := (hcomm _ h2 _ h1).symm
    obtain ⟨-, h4⟩ := typeIIi_unique hdisj ht₁.2 h2 ht₂.2 h1 h3
    exact ⟨t₁, ht₁, by rw [← h4]⟩
  let Y : Subgroup G :=
    { carrier := {y | y ∈ T ⊓ J₁ ∧ y * (c * y * c⁻¹) ∈ A}
      one_mem' := ⟨(T ⊓ J₁).one_mem, by simp⟩
      mul_mem' := by
        rintro y z ⟨hy, hyA⟩ ⟨hz, hzA⟩
        refine ⟨(T ⊓ J₁).mul_mem hy hz, ?_⟩
        have : y * z * (c * (y * z) * c⁻¹) = y * (c * y * c⁻¹) * (z * (c * z * c⁻¹)) := by
          rw [key y z hy.2 hz.2]; group
        rw [this]
        exact A.mul_mem hyA hzA
      inv_mem' := by
        rintro y ⟨hy, hyA⟩
        refine ⟨(T ⊓ J₁).inv_mem hy, ?_⟩
        have hyw : y * (c * y * c⁻¹) = (c * y * c⁻¹) * y := hcomm y hy.2 _ (hcJ1 y hy.2)
        have : y⁻¹ * (c * y⁻¹ * c⁻¹) = (y * (c * y * c⁻¹))⁻¹ := by
          calc y⁻¹ * (c * y⁻¹ * c⁻¹) = ((c * y * c⁻¹) * y)⁻¹ := by group
            _ = (y * (c * y * c⁻¹))⁻¹ := by rw [hyw]
        rw [this]
        exact A.inv_mem hyA }
  have hY : ∀ y, y ∈ Y ↔ y ∈ T ⊓ J₁ ∧ y * (c * y * c⁻¹) ∈ A := fun y => Iff.rfl
  refine ⟨Y, fun y hy => ((hY y).mp hy).1, ⟨⟨⟨fun y z => ?_⟩⟩, fun y hy => ?_⟩, ?_,
    fun y hy => ((hY y).mp hy).2, fun a ha => ?_⟩
  · obtain ⟨hyJ, hyA⟩ := (hY y).mp y.2
    obtain ⟨hzJ, hzA⟩ := (hY z).mp z.2
    have e := hAcomm _ hyA _ hzA
    rw [key _ _ hyJ.2 hzJ.2, key _ _ hzJ.2 hyJ.2] at e
    have := typeIIi_unique hdisj (J₁.mul_mem hyJ.2 hzJ.2) (J₁.mul_mem hzJ.2 hyJ.2)
      (J₂.mul_mem (hcJ1 _ hyJ.2) (hcJ1 _ hzJ.2)) (J₂.mul_mem (hcJ1 _ hzJ.2) (hcJ1 _ hyJ.2)) e
    exact Subtype.ext this.1
  · obtain ⟨hyJ, hyA⟩ := (hY y).mp hy
    have e := hAab.2 _ hyA
    rw [pow_two, key _ _ hyJ.2 hyJ.2] at e
    have := typeIIi_unique hdisj (J₁.mul_mem hyJ.2 hyJ.2) J₁.one_mem
      (J₂.mul_mem (hcJ1 _ hyJ.2) (hcJ1 _ hyJ.2)) J₂.one_mem (e.trans (one_mul 1).symm)
    rw [pow_two]
    exact this.1
  · let f : Y → A := fun y => ⟨y * (c * y * c⁻¹), ((hY y).mp y.2).2⟩
    have hf : Function.Surjective f := by
      rintro ⟨a, ha⟩
      obtain ⟨y, hy, rfl⟩ := hdecomp a ha
      exact ⟨⟨y, (hY y).mpr ⟨hy, ha⟩⟩, rfl⟩
    exact Nat.card_le_card_of_surjective f hf
  · obtain ⟨y, hy, rfl⟩ := hdecomp a ha
    exact ⟨y, (hY y).mpr ⟨hy, ha⟩, rfl⟩

end Aux

theorem typeIIi_orderOf_normalizerMonoidHom_map {H G : Type} [Group H] [Group G] (ι : H →* G)
    (hι : Function.Injective ι) (V : Subgroup H) (x : H)
    (hx : x ∈ Subgroup.normalizer (V : Set H))
    (hx' : ι x ∈ Subgroup.normalizer ((V.map ι : Subgroup G) : Set G)) :
    orderOf ((V.map ι).normalizerMonoidHom ⟨ι x, hx'⟩) =
      orderOf (V.normalizerMonoidHom ⟨x, hx⟩) := by
  have key : (V.map ι).normalizerMonoidHom ⟨ι x, hx'⟩ =
      MulAut.congr (V.equivMapOfInjective ι hι) (V.normalizerMonoidHom ⟨x, hx⟩) := by
    ext y
    obtain ⟨v, rfl⟩ := (V.equivMapOfInjective ι hι).surjective y
    have h1 := Subgroup.normalizerMonoidHom_apply_apply_coe (V.map ι) ⟨ι x, hx'⟩
      (V.equivMapOfInjective ι hι v)
    have h2 := Subgroup.normalizerMonoidHom_apply_apply_coe V ⟨x, hx⟩ v
    have h3 : (MulAut.congr (V.equivMapOfInjective ι hι) (V.normalizerMonoidHom ⟨x, hx⟩))
        (V.equivMapOfInjective ι hι v) =
        V.equivMapOfInjective ι hι (V.normalizerMonoidHom ⟨x, hx⟩ v) := by
      simp [MulAut.congr_apply]
    rw [h3, h1]
    show ι x * ι ↑v * (ι x)⁻¹ = ι ↑(V.normalizerMonoidHom ⟨x, hx⟩ v)
    rw [h2, map_mul, map_mul, map_inv]
  rw [key, MulEquiv.orderOf_eq]

theorem typeIIi_isPGroup {H : Type*} [Group H] {A : Subgroup H} (hA : IsElemAbelian 2 A) :
    IsPGroup 2 A := CFSG.Open.IsElemAbelian.isPGroup hA

theorem typeIIi_aut3 {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hp7 : 7 ≤ p) {J Y : Subgroup G} (hJ : IsPSL 2 p 1 ↥J)
    (hYJ : Y ≤ J) (hYab : IsElemAbelian 2 Y) (hY4 : 4 ≤ Nat.card Y) :
    ∃ x ∈ J, ∃ hx : x ∈ Subgroup.normalizer (Y : Set G),
      orderOf (Y.normalizerMonoidHom ⟨x, hx⟩) = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.equiv_psl2_zmod_of_model hJ
  obtain ⟨ι, hι, hrange⟩ := e22pd1_exists_embedding e
  have hYr : Y ≤ ι.range := hrange ▸ hYJ
  obtain ⟨V, rfl⟩ := e22pd1_exists_map_eq hYr
  have hodd : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by simp⟩
  have hq8 : Nat.card (ZMod p) % 8 = 1 ∨ Nat.card (ZMod p) % 8 = 7 := by
    rwa [Nat.card_zmod]
  have hcard : 3 < Nat.card (ZMod p) := by
    rw [Nat.card_zmod]
    omega
  have hVab : IsElemAbelian 2 V := isElemAbelian_of_map_injective' hι hYab
  have hV4 : 4 ≤ Nat.card V := by rwa [Subgroup.card_map_of_injective hι] at hY4
  obtain ⟨S₀, hVS₀⟩ := (typeIIi_isPGroup hVab).exists_le_sylow
  have hS₀ : IsSylowIn 2 (S₀ : Subgroup (PSL2 (ZMod p))) ⊤ := by
    refine ⟨le_top, S₀.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S₀.not_dvd_index
  obtain ⟨S, m, hSS, hm2, ⟨eS⟩⟩ := e22pl2psl_sylow_dihedral_q hodd hq8 hS₀
  have hVS : V ≤ (S : Subgroup (PSL2 (ZMod p))) := hSS ▸ hVS₀
  obtain ⟨-, -, -, -, -, hAV⟩ := dihedral_sylow_data hm2 eS
  obtain ⟨-, hVK⟩ := hAV V hVS hVab hV4
  have hperf : Group.IsPerfect (PSL2 (ZMod p)) := psl2_isPerfect_of_card_gt_three (ZMod p) hcard
  have hsurj := perfect_dihedral_fourgroup_normalizer_surjective S hm2 eS V hVS hVK
  have := hVK
  let a : MulAut V := (kleinFourAutSymmetricThreeEquiv V).symm (finRotate 3)
  have ha : orderOf a = 3 := by
    rw [MulEquiv.orderOf_eq, (isCycle_finRotate (n := 1)).orderOf, support_finRotate]
    simp
  obtain ⟨x', hx'⟩ := hsurj a
  have hxJ : ι x'.1 ∈ J := hrange ▸ ⟨x'.1, rfl⟩
  have hxN : ι x'.1 ∈ Subgroup.normalizer ((V.map ι : Subgroup G) : Set G) :=
    e22pd1_map_normalizer_le ι hι V ⟨x'.1, x'.2, rfl⟩
  refine ⟨ι x'.1, hxJ, hxN, ?_⟩
  rw [typeIIi_orderOf_normalizerMonoidHom_map ι hι V x'.1 x'.2 hxN]
  have h1 : V.normalizerMonoidHom ⟨x'.1, x'.2⟩ = a := hx'
  rw [h1, ha]

theorem typeII_inner {G : Type} [Group G] [Finite G] {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G}
    (h : Wr p T M J₁ J₂ z₁)
    (hI : ∀ {A' : Subgroup G}, A' ≤ T → IsElemAbelian 2 A' → A' ≠ ⊥ →
      T ⊓ Subgroup.centralizer (A' : Set G) ≤ Subgroup.normalizer (J₁ : Set G) →
      ∃ K : Subgroup G, E1.IsE 1 ⊤ T A' K ∧ ¬ K ≤ M)
    {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl ⊤ Ω) {A : Subgroup G} (hAΩ : A ∈ Ω) (hAT : A ≤ T)
    (hAab : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A)
    (hc : ¬ T ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (J₁ : Set G))
    (hAX : A ≤ J₁ ⊔ J₂) :
    ∃ A' ∈ Ω, A' ≤ T ∧ ∃ K : Subgroup G, E1.IsE 1 ⊤ T A' K ∧ ¬ K ≤ M := by
  obtain ⟨c, hcTC, hcN⟩ := IsConcreteLE.not_le_iff_exists.mp hc
  have hcT : c ∈ T := (Subgroup.mem_inf.mp hcTC).1
  have hcA : ∀ a ∈ A, a * c = c * a := fun a ha =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcTC).2 a ha
  obtain ⟨hc1, hc2⟩ := typeIIi_swap h hcT hcN
  have hAX' : A ≤ (T ⊓ J₁) ⊔ (T ⊓ J₂) := fun a ha => by
    have : a ∈ T ⊓ (J₁ ⊔ J₂) := ⟨hAT ha, hAX ha⟩
    rwa [h.TX_eq] at this
  obtain ⟨Y, hYTJ, hYab, hYcard, hYA, hAY⟩ :=
    typeIIi_exists_Y h.comm h.disj hc1 hc2 hcA hAab hAX'
  have hYJ : Y ≤ J₁ := hYTJ.trans inf_le_right
  have hYT : Y ≤ T := hYTJ.trans inf_le_left
  obtain ⟨x, hxJ, hxN, hxord⟩ :=
    typeIIi_aut3 h.p_prime h.p_mod h.p_ge h.psl₁ hYJ hYab (hA4.trans hYcard)
  have hxY : ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := fun y hy => (Subgroup.mem_normalizer_iff.mp hxN y).mp hy
  have hcJ1 : ∀ y ∈ J₁, c * y * c⁻¹ ∈ J₂ := fun y hy => by
    rw [← hc1]; exact mem_conjSub_of_mem hy
  have hconj : ∀ y ∈ J₁, x * (y * (c * y * c⁻¹)) * x⁻¹ = (x * y * x⁻¹) * (c * y * c⁻¹) := by
    intro y hy
    have hxw : x * (c * y * c⁻¹) = (c * y * c⁻¹) * x := h.comm x hxJ _ (hcJ1 y hy)
    calc x * (y * (c * y * c⁻¹)) * x⁻¹
        = x * y * (x⁻¹ * (x * (c * y * c⁻¹)) * x⁻¹) := by group
      _ = x * y * (x⁻¹ * ((c * y * c⁻¹) * x) * x⁻¹) := by rw [hxw]
      _ = (x * y * x⁻¹) * (c * y * c⁻¹) := by group
  have hA'mem : ∀ y ∈ Y, (x * y * x⁻¹) * (c * y * c⁻¹) ∈ conjSub x A := by
    intro y hy
    rw [← hconj y (hYJ hy)]
    exact mem_conjSub_of_mem (hYA y hy)
  have hA'form : ∀ g ∈ conjSub x A, ∃ y ∈ Y, g = (x * y * x⁻¹) * (c * y * c⁻¹) := by
    intro g hg
    obtain ⟨y, hy, hay⟩ := hAY _ (mem_conjSub_iff.mp hg)
    refine ⟨y, hy, ?_⟩
    calc g = x * (x⁻¹ * g * x) * x⁻¹ := by group
      _ = x * (y * (c * y * c⁻¹)) * x⁻¹ := by rw [← hay]
      _ = (x * y * x⁻¹) * (c * y * c⁻¹) := hconj y (hYJ hy)
  have hA'Ω : conjSub x A ∈ Ω := hΩ.conj A hAΩ x (Subgroup.mem_top x)
  have hA'T : conjSub x A ≤ T := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := hA'form g hg
    exact T.mul_mem (hYT (hxY y hy)) (T.mul_mem (T.mul_mem hcT (hYT hy)) (T.inv_mem hcT))
  have hA'1 : conjSub x A ≠ ⊥ := by
    have hA1 : A ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hA4
      omega
    obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
    intro hbot
    have h1 : x * a * x⁻¹ ∈ conjSub x A := mem_conjSub_of_mem ha
    rw [hbot, Subgroup.mem_bot] at h1
    exact ha1 (Subtype.ext (by simpa using h1))
  have hcent : T ⊓ Subgroup.centralizer ((conjSub x A : Subgroup G) : Set G) ≤
      Subgroup.normalizer (J₁ : Set G) := by
    intro s hs
    by_contra hsn
    obtain ⟨hsT, hsC⟩ := Subgroup.mem_inf.mp hs
    obtain ⟨hs1, hs2⟩ := typeIIi_swap h hsT hsn
    have hu : ∀ y ∈ Y, (s * c) * y * (s * c)⁻¹ = x * y * x⁻¹ := by
      intro y hy
      have hyJ : y ∈ J₁ := hYJ hy
      have hφ : x * y * x⁻¹ ∈ J₁ := J₁.mul_mem (J₁.mul_mem hxJ hyJ) (J₁.inv_mem hxJ)
      have hw : c * y * c⁻¹ ∈ J₂ := hcJ1 y hyJ
      have hcomm := Subgroup.mem_centralizer_iff.mp hsC _ (hA'mem y hy)
      have h1 : s * (x * y * x⁻¹) * s⁻¹ ∈ J₂ := by
        rw [← hs1]; exact mem_conjSub_of_mem hφ
      have h2 : s * (c * y * c⁻¹) * s⁻¹ ∈ J₁ := by
        rw [← hs2]; exact mem_conjSub_of_mem hw
      have h3 : s * ((x * y * x⁻¹) * (c * y * c⁻¹)) * s⁻¹ = (x * y * x⁻¹) * (c * y * c⁻¹) := by
        rw [← hcomm]; group
      have h4 : (s * (c * y * c⁻¹) * s⁻¹) * (s * (x * y * x⁻¹) * s⁻¹) =
          (x * y * x⁻¹) * (c * y * c⁻¹) := by
        calc (s * (c * y * c⁻¹) * s⁻¹) * (s * (x * y * x⁻¹) * s⁻¹)
            = (s * (x * y * x⁻¹) * s⁻¹) * (s * (c * y * c⁻¹) * s⁻¹) := h.comm _ h2 _ h1
          _ = s * ((x * y * x⁻¹) * (c * y * c⁻¹)) * s⁻¹ := by group
          _ = (x * y * x⁻¹) * (c * y * c⁻¹) := h3
      have h5 := (typeIIi_unique h.disj h2 hφ h1 hw h4).1
      calc (s * c) * y * (s * c)⁻¹ = s * (c * y * c⁻¹) * s⁻¹ := by group
        _ = x * y * x⁻¹ := h5
    have huT : s * c ∈ T := T.mul_mem hsT hcT
    have hu' : x⁻¹ * (s * c) ∈ Subgroup.centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      calc y * (x⁻¹ * (s * c)) = x⁻¹ * (x * y * x⁻¹) * (s * c) := by group
        _ = x⁻¹ * ((s * c) * y * (s * c)⁻¹) * (s * c) := by rw [hu y hy]
        _ = (x⁻¹ * (s * c)) * y := by group
    have huN : s * c ∈ Subgroup.normalizer (Y : Set G) := by
      have : s * c = x * (x⁻¹ * (s * c)) := by group
      rw [this]
      exact Subgroup.mul_mem _ hxN (Subgroup.centralizer_le_normalizer _ hu')
    have hfeq : Y.normalizerMonoidHom ⟨s * c, huN⟩ = Y.normalizerMonoidHom ⟨x, hxN⟩ := by
      ext y
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact hu y y.2
    obtain ⟨k, hk⟩ := h.sylow.isPGroup ⟨s * c, huT⟩
    have hk' : (s * c) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : orderOf (⟨s * c, huN⟩ : Subgroup.normalizer (Y : Set G)) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext hk')
    have h3 : 3 ∣ 2 ^ k := by
      have := orderOf_map_dvd Y.normalizerMonoidHom ⟨s * c, huN⟩
      rw [hfeq, hxord] at this
      exact this.trans hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  obtain ⟨K, hK, hKM⟩ := hI hA'T (hΩ.isElemAbelian _ hA'Ω) hA'1 hcent
  exact ⟨conjSub x A, hA'Ω, hA'T, K, hK, hKM⟩

end CFSG.Quasithin.E2.E22N
