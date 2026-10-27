module

public import CFSG.CGT.Timmesfeld75.CentralQuotient

public section

namespace CFSG.RankThree.GF2n.Tim81.CentralTI

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {Y : Type*} [Group Y] {T Z : Subgroup Y} [Z.Normal]

private theorem conjSubgroup_eq_self_of_le_center (hZ : Z ≤ Subgroup.center Y) (g : Y) :
    conjSubgroup g Z = Z := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_conjSubgroup] at hx
    have hx' : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [hx']
    exact Subgroup.Normal.conj_mem inferInstance (g⁻¹ * x * g) hx g
  · intro x hx
    rw [mem_conjSubgroup]
    simpa using Subgroup.Normal.conj_mem inferInstance x hx g⁻¹

theorem sup_le_normalizer (hZ : Z ≤ Subgroup.center Y) :
    T ⊔ Z ≤ Subgroup.normalizer (T : Set Y) :=
  sup_le Subgroup.le_normalizer fun x hx => Subgroup.center_le_normalizer (T : Set Y) (hZ hx)

private theorem normalizer_sup_eq_normalizer (hZ : Z ≤ Subgroup.center Y)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y))) :
    Subgroup.normalizer ((T ⊔ Z : Subgroup Y) : Set Y) = Subgroup.normalizer (T : Set Y) := by
  refine le_antisymm ?_ ?_
  · intro n hn
    rw [mem_normalizer_iff_conjSubgroup_eq] at hn ⊢
    refine hwc.2 n ?_
    calc conjSubgroup n T ≤ conjSubgroup n (T ⊔ Z) := Subgroup.map_mono le_sup_left
      _ = T ⊔ Z := hn
      _ ≤ Subgroup.normalizer (T : Set Y) := sup_le_normalizer hZ
  · intro n hn
    rw [mem_normalizer_iff_conjSubgroup_eq] at hn ⊢
    have hn' : T.map (MulAut.conj n).toMonoidHom = T := hn
    have hZ' : Z.map (MulAut.conj n).toMonoidHom = Z := conjSubgroup_eq_self_of_le_center hZ n
    show Subgroup.map (MulAut.conj n).toMonoidHom (T ⊔ Z) = T ⊔ Z
    rw [Subgroup.map_sup T Z (MulAut.conj n).toMonoidHom, hn', hZ']

theorem inf_eq_bot_of_not_isMulCommutative (hT : Assembly.IsElemAbelian 2 T)
    (hgen : Subgroup.normalClosure (T : Set Y) = ⊤) (hTI : IsTI T)
    (hZ : Z ≤ Subgroup.center Y) (hq : ¬ IsMulCommutative (Y ⧸ Z)) : T ⊓ Z = ⊥ := by
  by_contra hne
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hzT : (z : Y) ∈ T := z.2.1
  have hzZ : (z : Y) ∈ Z := z.2.2
  have hz1' : (z : Y) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzconj : ∀ g : Y, (z : Y) ∈ conjSubgroup g T := by
    intro g
    rw [mem_conjSubgroup]
    have hzg : g⁻¹ * (z : Y) * g = (z : Y) := by
      rw [Subgroup.mem_center_iff.mp (hZ hzZ) g⁻¹]
      group
    rwa [hzg]
  have hle : ∀ g : Y, T ≤ conjSubgroup g T := by
    intro g
    have hz' : (z : Y) ∈ T ⊓ conjSubgroup g T := ⟨hzT, hzconj g⟩
    rcases hTI g with h | h
    · rw [h] at hz'
      exact absurd (Subgroup.mem_bot.mp hz') hz1'
    · have hle2 : T ⊓ conjSubgroup g T ≤ conjSubgroup g T := inf_le_right
      rwa [h] at hle2
  have hnormal : T.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have h := hle g⁻¹ hx
    rw [mem_conjSubgroup] at h
    simpa using h
  haveI : T.Normal := hnormal
  have htop : T = ⊤ := by rw [← hgen, Subgroup.normalClosure_eq_self]
  haveI : IsMulCommutative T := hT.1
  haveI : IsMulCommutative Y := IsMulCommutative.of_comm fun a b => by
    have ha : a ∈ T := by rw [htop]; exact Subgroup.mem_top a
    have hb : b ∈ T := by rw [htop]; exact Subgroup.mem_top b
    exact congrArg Subtype.val (mul_comm' ⟨a, ha⟩ ⟨b, hb⟩)
  refine hq (IsMulCommutative.of_comm fun a b => ?_)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z b
  rw [← map_mul, ← map_mul, mul_comm' x y]

theorem isPGroup_map_mk'_and_ne_bot (hT : IsPGroup 2 T) (hTZ : T ⊓ Z = ⊥) (hTne : T ≠ ⊥) :
    IsPGroup 2 (T.map (QuotientGroup.mk' Z)) ∧ T.map (QuotientGroup.mk' Z) ≠ ⊥ := by
  refine ⟨hT.map (QuotientGroup.mk' Z), ?_⟩
  rw [Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact fun hle => hTne (le_bot_iff.mp (hTZ ▸ le_inf le_rfl hle))

private theorem conjSubgroup_eq_of_mk'_mem_normalizer (hZ : Z ≤ Subgroup.center Y)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y))) {u : Y}
    (hu : QuotientGroup.mk' Z u ∈
      Subgroup.normalizer ((T.map (QuotientGroup.mk' Z)) : Set (Y ⧸ Z))) :
    conjSubgroup u T = T := by
  rw [mem_normalizer_iff_conjSubgroup_eq] at hu
  have h1 : (conjSubgroup u T).map (QuotientGroup.mk' Z) = T.map (QuotientGroup.mk' Z) := by
    rw [map_conjSubgroup, hu]
  have hle : conjSubgroup u T ≤ T ⊔ Z := by
    simpa [QuotientGroup.ker_mk'] using
      (Subgroup.map_le_map_iff (f := QuotientGroup.mk' Z) (H := conjSubgroup u T)
        (K := T)).1 (le_of_eq h1)
  exact hwc.2 u (hle.trans (sup_le_normalizer hZ))

theorem weaklyClosed_map_mk' (hZ : Z ≤ Subgroup.center Y)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y))) :
    ∀ g : Y ⧸ Z, conjSubgroup g (T.map (QuotientGroup.mk' Z)) ≤
        Subgroup.normalizer ((T.map (QuotientGroup.mk' Z)) : Set (Y ⧸ Z)) →
      conjSubgroup g (T.map (QuotientGroup.mk' Z)) = T.map (QuotientGroup.mk' Z) := by
  intro g hg
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z g
  rw [← map_conjSubgroup] at hg ⊢
  have hle : conjSubgroup y T ≤ Subgroup.normalizer (T : Set Y) := fun u hu =>
    mem_normalizer_iff_conjSubgroup_eq.2
      (conjSubgroup_eq_of_mk'_mem_normalizer hZ hwc (hg (Subgroup.mem_map_of_mem _ hu)))
  rw [hwc.2 y hle]

theorem weaklyClosed_map_mulEquiv {L : Type*} [Group L] (e : Y ≃* L) {U : Subgroup Y}
    (hwc : ∀ g : Y, conjSubgroup g U ≤ Subgroup.normalizer (U : Set Y) →
      conjSubgroup g U = U) :
    ∀ g : L, conjSubgroup g (U.map e.toMonoidHom) ≤
        Subgroup.normalizer ((U.map e.toMonoidHom) : Set L) →
      conjSubgroup g (U.map e.toMonoidHom) = U.map e.toMonoidHom := by
  intro g hg
  obtain ⟨y, rfl⟩ : ∃ y, e.toMonoidHom y = g := ⟨e.symm g, by simpa using e.apply_symm_apply g⟩
  rw [← map_conjSubgroup] at hg ⊢
  refine congrArg (Subgroup.map e.toMonoidHom) (hwc y fun u hu => ?_)
  rw [mem_normalizer_iff_conjSubgroup_eq]
  have hN := hg (Subgroup.mem_map_of_mem _ hu)
  rw [mem_normalizer_iff_conjSubgroup_eq, ← map_conjSubgroup] at hN
  exact Subgroup.map_injective e.injective hN

theorem normalize_and_fixedPointFree_of_map [Finite Y] (hZ : Z ≤ Subgroup.center Y)
    (hTZ : T ⊓ Z = ⊥)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y))) {d : Y} {dbar : Y ⧸ Z}
    (hd : QuotientGroup.mk' Z d = dbar)
    (hdN : dbar ∈ Subgroup.normalizer ((T.map (QuotientGroup.mk' Z)) : Set (Y ⧸ Z)))
    (hfpf : ∀ x ∈ T.map (QuotientGroup.mk' Z), dbar * x * dbar⁻¹ = x → x = 1) :
    d ∈ Subgroup.normalizer (T : Set Y) ∧ ∀ x ∈ T, d * x * d⁻¹ = x → x = 1 := by
  have hdN' : QuotientGroup.mk' Z d ∈
      Subgroup.normalizer ((T.map (QuotientGroup.mk' Z)) : Set (Y ⧸ Z)) := hd ▸ hdN
  rw [mem_normalizer_iff_conjSubgroup_eq] at hdN'
  have h1 : (conjSubgroup d T).map (QuotientGroup.mk' Z) = T.map (QuotientGroup.mk' Z) := by
    rw [map_conjSubgroup, hdN']
  have hTZnorm : conjSubgroup d (T ⊔ Z) = T ⊔ Z := by
    have hZ' : Z.map (MulAut.conj d).toMonoidHom = Z := conjSubgroup_eq_self_of_le_center hZ d
    have hle : conjSubgroup d (T ⊔ Z) ≤ T ⊔ Z := by
      show Subgroup.map (MulAut.conj d).toMonoidHom (T ⊔ Z) ≤ T ⊔ Z
      rw [Subgroup.map_sup T Z (MulAut.conj d).toMonoidHom, hZ']
      exact sup_le (by
        have h := (Subgroup.map_le_map_iff (f := QuotientGroup.mk' Z)
          (H := Subgroup.map (MulAut.conj d).toMonoidHom T) (K := T)).1 (le_of_eq h1)
        simpa [QuotientGroup.ker_mk'] using h) le_sup_right
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hc : Nat.card ↥(conjSubgroup d (T ⊔ Z)) = Nat.card ↥(T ⊔ Z : Subgroup Y) :=
      Subgroup.card_map_of_injective (MulAut.conj d).injective
    exact le_of_eq hc.symm
  refine ⟨?_, ?_⟩
  · rw [← normalizer_sup_eq_normalizer hZ hwc]
    exact mem_normalizer_iff_conjSubgroup_eq.2 hTZnorm
  · intro x hx hfix
    have hx1 : QuotientGroup.mk' Z x = 1 := by
      refine hfpf (QuotientGroup.mk' Z x) (Subgroup.mem_map_of_mem _ hx) ?_
      calc dbar * QuotientGroup.mk' Z x * dbar⁻¹
          = QuotientGroup.mk' Z d * QuotientGroup.mk' Z x * (QuotientGroup.mk' Z d)⁻¹ := by
            rw [hd]
        _ = QuotientGroup.mk' Z (d * x * d⁻¹) := by rw [map_mul, map_mul, map_inv]
        _ = QuotientGroup.mk' Z x := by rw [hfix]
    have hxZ : x ∈ Z := (QuotientGroup.eq_one_iff x).1 hx1
    have hbot : x ∈ (⊥ : Subgroup Y) := by
      rw [← hTZ]
      exact ⟨hx, hxZ⟩
    exact Subgroup.mem_bot.1 hbot

theorem commutator_eq_top_of_fixedPointFree [Finite T] {d : Y}
    (hdN : d ∈ Subgroup.normalizer (T : Set Y))
    (hfpf : ∀ x ∈ T, d * x * d⁻¹ = x → x = 1)
    (hgen : Subgroup.normalClosure (T : Set Y) = ⊤) : commutator Y = ⊤ := by
  have hdT : ∀ x ∈ T, d * x * d⁻¹ ∈ T := by
    intro x hx
    have hconj : conjSubgroup d T = T := mem_normalizer_iff_conjSubgroup_eq.1 hdN
    rw [← hconj]
    refine mem_conjSubgroup.2 ?_
    rw [show d⁻¹ * (d * x * d⁻¹) * d = x by group]
    exact hx
  let φ : T →* T :=
    { toFun := fun x => ⟨d * (x : Y) * d⁻¹, hdT x x.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hfpfφ : MonoidHom.FixedPointFree φ := by
    intro x hx
    apply Subtype.ext
    exact hfpf x x.2 (congrArg Subtype.val hx)
  have hTle : T ≤ commutator Y := by
    intro x hx
    obtain ⟨t, ht⟩ := MonoidHom.FixedPointFree.commutatorMap_surjective hfpfφ ⟨x, hx⟩
    have hval : x = ⁅(t : Y), d⁆ := by
      have h2 : ((MonoidHom.commutatorMap φ t : T) : Y) = x := by rw [ht]
      rw [← h2, MonoidHom.commutatorMap_apply, commutatorElement_def, Subgroup.coe_div,
        div_eq_mul_inv]
      show (t : Y) * (d * (t : Y) * d⁻¹)⁻¹ = (t : Y) * d * (t : Y)⁻¹ * d⁻¹
      group
    rw [hval]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [eq_top_iff, ← hgen]
  exact Subgroup.normalClosure_le_normal fun x hx => hTle hx

theorem center_eq_of_center_quotient_eq_bot (hZ : Z ≤ Subgroup.center Y)
    (h : Subgroup.center (Y ⧸ Z) = ⊥) : Z = Subgroup.center Y := by
  refine le_antisymm hZ ?_
  intro x hx
  have hx' : QuotientGroup.mk' Z x ∈ Subgroup.center (Y ⧸ Z) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
  rw [h, Subgroup.mem_bot] at hx'
  exact (QuotientGroup.eq_one_iff x).1 hx'

end CFSG.RankThree.GF2n.Tim81.CentralTI
