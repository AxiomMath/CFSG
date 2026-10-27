module

public import CFSG.LocalAnalysis.UniquenessCase.UCK41
import CFSG.Goldschmidt.Steps.G55Basic
import CFSG.GroupTheory.ABGLocalTools.FrobeniusFixedPoints
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.RankThree.FFModules (fixSub mem_fixSub)
open Subgroup

private theorem fixSub_eq_invariants {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) :
    fixSub ρ A = Representation.invariants (ρ.comp A.subtype) := by
  ext v
  rw [mem_fixSub, Representation.mem_invariants]
  exact ⟨fun h a => h a.1 a.2, fun h a ha => h ⟨a, ha⟩⟩

private theorem inf_centralizer_eq_bot_of_commutator_eq_top
    {G : Type*} [Group G] [Finite G] {Q D : Subgroup G}
    (hQab : IsMulCommutative ↥Q) (hDQ : D ≤ normalizer (Q : Set G)) (hQD : ⁅D, Q⁆ = Q)
    (hcop : Nat.Coprime (Nat.card D) (Nat.card Q)) :
    Q ⊓ Subgroup.centralizer (D : Set G) = ⊥ := by
  have hQD' : ⁅Q, D⁆ = Q := by rw [Subgroup.commutator_comm, hQD]
  obtain ⟨-, hdisj⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp Q D hDQ
      (fun x y => hQab.is_comm.comm x y) hcop
  rw [hQD'] at hdisj
  rw [disjoint_iff] at hdisj
  rwa [inf_eq_left.mpr inf_le_left] at hdisj

private theorem inf_fixSub_fixSub_ne_bot
    {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) H W)
    {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hr : r.Prime)
    (A D : Subgroup H) (hA : CFSG.Open.IsElemAbelian q A)
    (hHtop : A ⊔ D = ⊤) (hDA : D ≤ Subgroup.normalizer (A : Set H))
    (hCD : A ⊓ Subgroup.centralizer (D : Set H) = ⊥)
    (hD : Nat.card D = r)
    (hfixA : fixSub ρ A = ⊥)
    (B : Subgroup H) (hBA : B ≤ A) (hBD : D ≤ Subgroup.normalizer (B : Set H))
    (hBne : fixSub ρ B ≠ ⊥) :
    fixSub ρ B ⊓ fixSub ρ D ≠ ⊥ := by
  have hAB : A ≤ Subgroup.normalizer (B : Set H) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have hcomm : a * b = b * a :=
        congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hBA hb⟩)
      rwa [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    · intro hb
      have hbA : b ∈ A := by
        have h1 : a * b * a⁻¹ ∈ A := hBA hb
        have h2 : a⁻¹ * (a * b * a⁻¹) * a = b := by group
        rw [← h2]
        exact A.mul_mem (A.mul_mem (A.inv_mem ha) h1) ha
      have hcomm : a * b = b * a :=
        congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hbA⟩)
      have h1 : a * b * a⁻¹ = b := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rwa [h1] at hb
  have hN : A ⊔ D ≤ Subgroup.normalizer (B : Set H) := sup_le hAB hBD
  have hgN : ∀ g : H, g ∈ Subgroup.normalizer (B : Set H) := fun g =>
    hN (hHtop ▸ Subgroup.mem_top g)
  have hinv : ∀ g : H, ∀ v ∈ fixSub ρ B, ρ g v ∈ fixSub ρ B := by
    intro g v hv
    have hg := hgN g
    rw [mem_fixSub] at hv ⊢
    intro b hb
    have hgbg : g⁻¹ * b * g ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) b).mp hb
      simpa using this
    calc ρ b (ρ g v) = ρ (b * g) v := by rw [map_mul, Module.End.mul_apply]
      _ = ρ (g * (g⁻¹ * b * g)) v := by rw [show b * g = g * (g⁻¹ * b * g) by group]
      _ = ρ g (ρ (g⁻¹ * b * g) v) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ g v := by rw [hv (g⁻¹ * b * g) hgbg]
  let ρB : Representation (ZMod 2) H ↥(fixSub ρ B) :=
    { toFun := fun g => (ρ g).restrict (fun v hv => hinv g v hv)
      map_one' := by ext v; simp
      map_mul' := by intro g h; ext v; simp [Module.End.mul_apply] }
  have hfixK : Representation.invariants (ρB.comp A.subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have hvA : (v : W) ∈ fixSub ρ A := by
      rw [mem_fixSub]
      intro a ha
      have := (Representation.mem_invariants (ρ := ρB.comp A.subtype) v).mp hv ⟨a, ha⟩
      exact congrArg Subtype.val this
    rw [hfixA, Submodule.mem_bot] at hvA
    exact Subtype.ext (by simpa using hvA)
  have hfpf : ∀ b ∈ D, b ≠ 1 → ∀ k ∈ A, b * k = k * b → k = 1 := by
    intro b hb hb1 k hk hbk
    have hbD : Subgroup.zpowers b = D := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb) ?_
      have hdvd : orderOf b ∣ Nat.card D := by
        have := orderOf_dvd_natCard (⟨b, hb⟩ : D)
        simpa using this
      rw [hD] at hdvd
      haveI : Fact r.Prime := ⟨hr⟩
      have hord : orderOf b = r := by
        rcases hr.eq_one_or_self_of_dvd (orderOf b) hdvd with h1 | h1
        · exact absurd h1 (orderOf_eq_one_iff.not.mpr hb1)
        · exact h1
      rw [Nat.card_zpowers, hord, hD]
    have hDgen : D = Subgroup.zpowers b := hbD.symm
    have hkC : k ∈ A ⊓ Subgroup.centralizer (D : Set H) := by
      refine ⟨hk, Subgroup.mem_centralizer_iff.mpr (fun d hd => ?_)⟩
      rw [hDgen] at hd
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
      exact ((show Commute b k from hbk).zpow_left m).eq
    rw [hCD, Subgroup.mem_bot] at hkC
    exact hkC
  have hchar : ¬ ringChar (ZMod 2) ∣ Nat.card A := by
    rw [ZMod.ringChar_zmod_n]
    haveI : Fact q.Prime := ⟨hq⟩
    have hAp : IsPGroup q A := fun y => ⟨1, Subtype.ext (by simpa using hA.2 y y.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAp
    rw [hk]
    exact fun h =>
      hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have hcount := CFSG.ABGLocalTools.finrank_invariants_mul_card_of_fixedPointFree
    (F := ZMod 2) (H := H) (V := ↥(fixSub ρ B)) ρB
    (K := A) (B := D) hA.1 hDA hfpf hchar hfixK
  have hposB : 0 < Module.finrank (ZMod 2) ↥(fixSub ρ B) :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hBne)
  have hneD : Representation.invariants (ρB.comp D.subtype) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot, zero_mul] at hcount
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hneD
  refine (Submodule.ne_bot_iff (fixSub ρ B ⊓ fixSub ρ D)).mpr ⟨(v : W), ⟨v.2, ?_⟩, ?_⟩
  · show (v : W) ∈ fixSub ρ D
    rw [mem_fixSub]
    intro d hd
    have := (Representation.mem_invariants (ρ := ρB.comp D.subtype) v).mp hv ⟨d, hd⟩
    exact congrArg Subtype.val this
  · exact fun h => hv0 (Subtype.ext (by simpa using h))

private theorem map_conj_mem_hyperplaneSet
    {H : Type} [Group H] {q : ℕ} {A B : Subgroup H}
    (hB : B ∈ (CFSG.LocalAnalysis.UniquenessCase.UCK.hyperplaneSet q A : Set (Subgroup H)))
    {d : H} (hdA : d ∈ Subgroup.normalizer (A : Set H)) :
    B.map (MulAut.conj d : H →* H) ∈
      (CFSG.LocalAnalysis.UniquenessCase.UCK.hyperplaneSet q A : Set (Subgroup H)) := by
  obtain ⟨hBA, hrel⟩ := hB
  refine ⟨?_, ?_⟩
  · calc B.map (MulAut.conj d : H →* H) ≤ A.map (MulAut.conj d : H →* H) :=
        Subgroup.map_mono hBA
      _ = A := Subgroup.mem_normalizer_iff_map_conj_eq.mp hdA
  · have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj d : H →* H)) B A
      (MulAut.conj d).injective
    rwa [Subgroup.mem_normalizer_iff_map_conj_eq.mp hdA, hrel] at h

private theorem map_conj_zpow_injective
    {H : Type*} [Group H] [Finite H] {r : ℕ} (hr : r.Prime)
    {D : Subgroup H} (hD : Nat.card D = r) {d : H} (hdD : d ∈ D) (hd1 : d ≠ 1)
    {B : Subgroup H} (hBnf : B.map (MulAut.conj d).toMonoidHom ≠ B) :
    Function.Injective (fun j : ZMod r => B.map (MulAut.conj (d ^ j.val)).toMonoidHom) := by
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have hdr : d ^ r = 1 := by
    have h1 : (⟨d, hdD⟩ : D) ^ Nat.card D = 1 := pow_card_eq_one'
    have h2 : d ^ Nat.card D = 1 := by
      have hh := congrArg (fun x : D => (x : H)) h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at hh
    rwa [hD] at h2
  have hdord : orderOf d = r := by
    haveI : Fact r.Prime := ⟨hr⟩
    exact orderOf_eq_prime hdr hd1
  intro i j hij
  have hkey : B.map (MulAut.conj ((d ^ j.val)⁻¹ * d ^ i.val)).toMonoidHom = B := by
    have hcomp : ((MulAut.conj (d ^ j.val))⁻¹).toMonoidHom.comp
        (MulAut.conj (d ^ i.val)).toMonoidHom =
        (MulAut.conj ((d ^ j.val)⁻¹ * d ^ i.val)).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← map_inv]
      simp only [MulAut.conj_apply]
      group
    have h1 : ((MulAut.conj (d ^ j.val))⁻¹).toMonoidHom.comp
        (MulAut.conj (d ^ j.val)).toMonoidHom = MonoidHom.id H := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      rw [← map_inv]
      simp only [MulAut.conj_apply]
      group
    have hthis := congrArg (fun X : Subgroup H =>
      X.map (((MulAut.conj (d ^ j.val))⁻¹).toMonoidHom)) hij
    simp only [Subgroup.map_map, hcomp, h1, Subgroup.map_id] at hthis
    exact hthis
  have hgD : (d ^ j.val)⁻¹ * d ^ i.val ∈ D :=
    D.mul_mem (D.inv_mem (D.pow_mem hdD j.val)) (D.pow_mem hdD i.val)
  have hgN : (d ^ j.val)⁻¹ * d ^ i.val ∈ Subgroup.normalizer (B : Set H) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hkey
  by_cases hg1 : (d ^ j.val)⁻¹ * d ^ i.val = 1
  ·
    have hdeq : d ^ i.val = d ^ j.val := by
      have := congrArg (fun x => d ^ j.val * x) hg1
      simpa [mul_assoc] using this
    have hmod : i.val ≡ j.val [MOD orderOf d] := pow_eq_pow_iff_modEq.mp hdeq
    rw [hdord] at hmod
    have hval : i.val = j.val := by
      rw [Nat.ModEq] at hmod
      rwa [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
    exact ZMod.val_injective r hval
  ·
    have hgord : orderOf ((d ^ j.val)⁻¹ * d ^ i.val) = r := by
      haveI : Fact r.Prime := ⟨hr⟩
      have hgr : ((d ^ j.val)⁻¹ * d ^ i.val) ^ r = 1 := by
        have h1 : (⟨(d ^ j.val)⁻¹ * d ^ i.val, hgD⟩ : D) ^ Nat.card D = 1 := pow_card_eq_one'
        have h2 : ((d ^ j.val)⁻¹ * d ^ i.val) ^ Nat.card D = 1 := by
          have hh := congrArg (fun x : D => (x : H)) h1
          rwa [Subgroup.coe_pow, Subgroup.coe_one] at hh
        rwa [hD] at h2
      exact orderOf_eq_prime hgr hg1
    have hDle : D ≤ Subgroup.normalizer (B : Set H) := by
      have hgen : Subgroup.zpowers ((d ^ j.val)⁻¹ * d ^ i.val) = D := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgD) ?_
        rw [Nat.card_zpowers, hgord, hD]
      rw [← hgen]
      exact Subgroup.zpowers_le.mpr hgN
    exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hDle hdD)) hBnf

private theorem two_le_finrank_of_hyperplane_ne_bot
    {H : Type} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) H W)
    {q : ℕ} (hq : q.Prime)
    (A B : Subgroup H) (hA : CFSG.Open.IsElemAbelian q A)
    (hB : B ∈ (hyperplaneSet q A : Set (Subgroup H)))
    (hfixA : fixSub ρ A = ⊥) (hBne : fixSub ρ B ≠ ⊥) :
    2 ≤ Module.finrank (ZMod 2) ↥(fixSub ρ B) := by
  obtain ⟨hBA, hrel⟩ := hB
  have hBltA : B < A := by
    refine lt_of_le_of_ne hBA ?_
    intro h
    rw [h] at hrel
    rw [Subgroup.relIndex_self] at hrel
    exact hq.ne_one hrel.symm
  obtain ⟨-, x, hxA, hxB⟩ := SetLike.lt_iff_le_and_exists.mp hBltA
  have hsup : B ⊔ Subgroup.zpowers x = A := by
    have hidx : (B.subgroupOf A).index = q := hrel
    have hcoat : IsCoatom (B.subgroupOf A) :=
      Subgroup.isCoatom_of_index_prime (H := B.subgroupOf A) (by rw [hidx]; exact hq)
    have hlt : B.subgroupOf A < (B ⊔ Subgroup.zpowers x).subgroupOf A := by
      refine lt_of_le_of_ne (Subgroup.subgroupOf_mono _ le_sup_left) ?_
      intro heq
      have hxmem : (⟨x, hxA⟩ : A) ∈ (B ⊔ Subgroup.zpowers x).subgroupOf A :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
      rw [← heq] at hxmem
      exact hxB (Subgroup.mem_subgroupOf.mp hxmem)
    have htop := hcoat.2 _ hlt
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact le_antisymm (sup_le hBA (Subgroup.zpowers_le.mpr hxA)) htop
  have hCx : fixSub ρ B ⊓ fixSub ρ (Subgroup.zpowers x) = ⊥ := by
    rw [← CFSG.RankThree.FFModules.fixSub_sup, hsup, hfixA]
  have hxinv : ∀ v ∈ fixSub ρ B, ρ x v ∈ fixSub ρ B := by
    intro v hv
    rw [mem_fixSub] at hv ⊢
    intro b hb
    have hbx : x⁻¹ * b * x ∈ B := by
      have h1 : x * b * x⁻¹ = b := by
        have hcomm : x * b = b * x :=
          congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hxA⟩ ⟨b, hBA hb⟩)
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      have h2 : x⁻¹ * b * x = b := by
        calc x⁻¹ * b * x = x⁻¹ * (x * b * x⁻¹) * x := by rw [h1]
          _ = b := by group
      rwa [h2]
    calc ρ b (ρ x v) = ρ (b * x) v := by rw [map_mul, Module.End.mul_apply]
      _ = ρ (x * (x⁻¹ * b * x)) v := by rw [show b * x = x * (x⁻¹ * b * x) by group]
      _ = ρ x (ρ (x⁻¹ * b * x) v) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ x v := by rw [hv (x⁻¹ * b * x) hbx]
  by_contra hle
  push Not at hle
  have hle1 : Module.finrank (ZMod 2) ↥(fixSub ρ B) ≤ 1 := by omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hle1
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hBne
  have hv0 : v ≠ 0 := by
    intro hvz
    obtain ⟨c, hc⟩ := hv ⟨u, hu⟩
    rw [hvz, smul_zero] at hc
    exact hu0 (congrArg Subtype.val hc.symm)
  have hxv : ρ x v ∈ fixSub ρ B := hxinv v v.2
  obtain ⟨c, hc⟩ := hv ⟨ρ x v, hxv⟩
  have hcases : c = 0 ∨ c = 1 := by
    have hlt : c.val < 2 := ZMod.val_lt c
    have h0 : c.val = 0 ∨ c.val = 1 := by omega
    rcases h0 with h | h
    · left; exact (ZMod.val_eq_zero c).mp h
    · right; exact (ZMod.val_eq_one (by norm_num : 1 < 2) c).mp h
  rcases hcases with rfl | rfl
  ·
    have hinj : Function.Injective (ρ x) := by
      have hxq : x ^ q = 1 := hA.2 x hxA
      exact Function.LeftInverse.injective (g := ρ (x ^ (q - 1))) (fun w => by
        rw [← Module.End.mul_apply, ← map_mul, ← pow_succ, Nat.sub_add_cancel hq.one_le,
          hxq, map_one, Module.End.one_apply])
    have hzero : (ρ x) (v : W) = 0 := by
      have hcv := congrArg Subtype.val hc
      simpa using hcv.symm
    have : (v : W) = 0 := hinj (by rw [hzero, map_zero])
    exact hv0 (Subtype.ext this)
  ·
    have hcx : (ρ x) (v : W) = (v : W) := by
      have hcv := congrArg Subtype.val hc
      simpa using hcv.symm
    have hvfix : (v : W) ∈ fixSub ρ (Subgroup.zpowers x) := by
      rw [mem_fixSub]
      let S : Subgroup H :=
        { carrier := {g | ρ g (v : W) = (v : W)}
          mul_mem' := fun {g h} hg hh => by
            show ρ (g * h) (v : W) = (v : W)
            rw [map_mul, Module.End.mul_apply, hh, hg]
          one_mem' := by
            show ρ 1 (v : W) = (v : W)
            rw [map_one, Module.End.one_apply]
          inv_mem' := fun {g} hg => by
            show ρ g⁻¹ (v : W) = (v : W)
            calc ρ g⁻¹ (v : W) = ρ g⁻¹ (ρ g (v : W)) := by rw [hg]
              _ = ρ (g⁻¹ * g) (v : W) := by rw [map_mul, Module.End.mul_apply]
              _ = (v : W) := by rw [inv_mul_cancel, map_one, Module.End.one_apply] }
      intro a ha
      exact Subgroup.zpowers_le.mpr (show x ∈ S from hcx) ha
    have hmem : (v : W) ∈ fixSub ρ B ⊓ fixSub ρ (Subgroup.zpowers x) := ⟨v.2, hvfix⟩
    rw [hCx, Submodule.mem_bot] at hmem
    exact hv0 (Subtype.ext hmem)

private lemma mul_pow_zmod_val
    {H : Type*} [Group H] {r : ℕ} (hr : r.Prime) {d : H}
    (hd1 : d ≠ 1) (hdr : d ^ r = 1) (j : ZMod r) :
    d * d ^ j.val = d ^ (j + 1).val := by
  haveI : NeZero r := ⟨hr.ne_zero⟩
  haveI : Fact (1 < r) := ⟨hr.one_lt⟩
  have hdord : orderOf d = r := by
    haveI : Fact r.Prime := ⟨hr⟩
    exact orderOf_eq_prime hdr hd1
  have h1 : d * d ^ j.val = d ^ (j.val + 1) := by
    have := pow_add d 1 j.val
    rw [pow_one, add_comm] at this
    exact this.symm
  have h2 : (j + 1).val = (j.val + 1) % r := by
    have hv1 : (1 : ZMod r).val = 1 := ZMod.val_one r
    rw [ZMod.val_add, hv1]
  rw [h1, h2, ← pow_mod_orderOf d (j.val + 1), hdord]

private lemma card_nsmul_eq_self {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    {n : ℕ} (hn : Odd n) (v : M) : n • v = v := by
  obtain ⟨m, rfl⟩ := hn
  have h2 : (2 : ℕ) • v = 0 := by
    calc (2 : ℕ) • v = (2 : ZMod 2) • v := (Nat.cast_smul_eq_nsmul (R := ZMod 2) 2 v).symm
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
  have h3 : ∀ k : ℕ, (2 * k : ℕ) • v = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ, add_nsmul, ih, h2, add_zero]
  rw [add_nsmul, h3 m, one_nsmul, zero_add]

private lemma sum_rho_mul_self {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (X : Subgroup G) [Fintype X] (hXodd : Odd (Nat.card X)) :
    (∑ x : X, ρ (x : G)) * (∑ x : X, ρ (x : G)) = ∑ x : X, ρ (x : G) := by
  classical
  have h1 : (∑ x : X, ρ (x : G)) * (∑ x : X, ρ (x : G)) =
      ∑ _ : X, (∑ x : X, ρ (x : G)) := by
    calc (∑ x : X, ρ (x : G)) * (∑ x : X, ρ (x : G))
        = ∑ x : X, ρ (x : G) * (∑ y : X, ρ (y : G)) := by rw [Finset.sum_mul]
      _ = ∑ x : X, ∑ y : X, ρ (x : G) * ρ (y : G) := by
            refine Finset.sum_congr rfl (fun x _ => ?_); rw [Finset.mul_sum]
      _ = ∑ x : X, ∑ y : X, ρ ((x * y : X) : G) := by
            refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
            rw [Subgroup.coe_mul, map_mul]
      _ = ∑ _ : X, (∑ x : X, ρ (x : G)) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            exact Fintype.sum_equiv (Equiv.mulLeft x) (fun y : X => ρ ((x * y : X) : G))
              (fun z : X => ρ (z : G)) (fun y => rfl)
  rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card]
  exact card_nsmul_eq_self hXodd _

private lemma range_sum_rho {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (X : Subgroup G) [Fintype X] (hXodd : Odd (Nat.card X)) :
    LinearMap.range (∑ x : X, ρ (x : G)) = fixSub ρ X := by
  classical
  refine le_antisymm ?_ ?_
  · rintro v ⟨w, rfl⟩
    rw [mem_fixSub]
    intro y hy
    have h1 : (∑ x : X, ρ (x : G)) w = ∑ x : X, ρ (x : G) w :=
      LinearMap.sum_apply Finset.univ (fun x : X => ρ (x : G)) w
    calc ρ y ((∑ x : X, ρ (x : G)) w) = ∑ x : X, ρ (y * (x : G)) w := by
          rw [h1, map_sum]
          exact Finset.sum_congr rfl (fun x _ => by rw [map_mul, Module.End.mul_apply])
      _ = ∑ z : X, ρ (z : G) w := Fintype.sum_equiv (Equiv.mulLeft (⟨y, hy⟩ : X))
            (fun x : X => ρ (y * (x : G)) w) (fun z : X => ρ (z : G) w) (fun x => rfl)
      _ = (∑ x : X, ρ (x : G)) w := h1.symm
  · intro v hv
    refine ⟨v, ?_⟩
    calc (∑ x : X, ρ (x : G)) v = ∑ x : X, ρ (x : G) v :=
          LinearMap.sum_apply Finset.univ (fun x : X => ρ (x : G)) v
      _ = ∑ _ : X, v := Finset.sum_congr rfl (fun x _ => hv x x.2)
      _ = (Nat.card X) • v := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card]
      _ = v := card_nsmul_eq_self hXodd v

private lemma mul_sum_rho {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (X : Subgroup G) [Fintype X] {x : G} (hx : x ∈ X) :
    ρ x * (∑ y : X, ρ (y : G)) = ∑ y : X, ρ (y : G) := by
  classical
  calc ρ x * (∑ y : X, ρ (y : G)) = ∑ y : X, ρ x * ρ (y : G) := Finset.mul_sum _ _ _
    _ = ∑ y : X, ρ (((⟨x, hx⟩ : X) * y : X) : G) := by
          refine Finset.sum_congr rfl (fun y _ => ?_); rw [Subgroup.coe_mul, map_mul]
    _ = ∑ z : X, ρ (z : G) := Fintype.sum_equiv (Equiv.mulLeft (⟨x, hx⟩ : X))
          (fun y : X => ρ (((⟨x, hx⟩ : X) * y : X) : G)) (fun z : X => ρ (z : G)) (fun y => rfl)

private lemma conj_sum_rho {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (X : Subgroup G) [Fintype X] {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    ρ g * (∑ x : X, ρ (x : G)) * ρ g⁻¹ = ∑ x : X, ρ (x : G) := by
  classical
  let φ : X ≃ X :=
    { toFun := fun y => ⟨g * (y : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp y.2⟩
      invFun := fun y => ⟨g⁻¹ * (y : G) * g, by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp y.2
        simpa using this⟩
      left_inv := fun y => by ext; simp [mul_assoc]
      right_inv := fun y => by ext; simp [mul_assoc] }
  have h2 : ρ g * (∑ x : X, ρ (x : G)) * ρ g⁻¹ =
      ∑ x : X, ρ (g * (x : G) * g⁻¹) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← map_mul, ← map_mul]
  rw [h2]
  exact Fintype.sum_equiv φ (fun x : X => ρ (g * (x : G) * g⁻¹))
    (fun z : X => ρ (z : G)) (fun x => by
      show ρ (g * (x : G) * g⁻¹) = ρ ((φ x : X) : G)
      simp [φ])

private lemma isCompl_range_ker {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (f : M →ₗ[ZMod 2] M) (hf : f * f = f) :
    IsCompl (LinearMap.range f) (LinearMap.ker f) := by
  refine ⟨disjoint_iff.mpr ?_, codisjoint_iff.mpr ?_⟩
  · rw [eq_bot_iff]
    rintro v ⟨hv1, hv2⟩
    rw [Submodule.mem_bot]
    obtain ⟨u, rfl⟩ := hv1
    have h : f (f u) = 0 := hv2
    rwa [← Module.End.mul_apply, hf] at h
  · rw [eq_top_iff]
    intro v _
    have h1 : f v ∈ LinearMap.range f := ⟨v, rfl⟩
    have h2 : v - f v ∈ LinearMap.ker f := by
      show f (v - f v) = 0
      rw [map_sub, ← Module.End.mul_apply, hf, sub_self]
    have : v = f v + (v - f v) := by abel
    rw [this]
    exact Submodule.add_mem_sup h1 h2

private lemma fixSub_inf_ker_sum_rho {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (X : Subgroup G) [Fintype X] (hXodd : Odd (Nat.card X)) :
    fixSub ρ X ⊓ LinearMap.ker (∑ x : X, ρ (x : G)) = ⊥ := by
  rw [← range_sum_rho ρ X hXodd]
  exact disjoint_iff.mp (isCompl_range_ker _ (sum_rho_mul_self ρ X hXodd)).1

private lemma ker_sum_rho_invariant {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (X : Subgroup G) [Fintype X] (hXodd : Odd (Nat.card X))
    {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    (LinearMap.ker (∑ x : X, ρ (x : G))).map (ρ g) ≤
      LinearMap.ker (∑ x : X, ρ (x : G)) := by
  have hginv : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hcomm : ρ g * (∑ x : X, ρ (x : G)) = (∑ x : X, ρ (x : G)) * ρ g := by
    have h1 := conj_sum_rho ρ X hg
    calc ρ g * (∑ x : X, ρ (x : G))
        = (ρ g * (∑ x : X, ρ (x : G)) * ρ g⁻¹) * ρ g := by
            rw [mul_assoc, hginv, mul_one]
      _ = (∑ x : X, ρ (x : G)) * ρ g := by rw [h1]
  rintro w ⟨u, hu, rfl⟩
  show (∑ x : X, ρ (x : G)) (ρ g u) = 0
  calc (∑ x : X, ρ (x : G)) (ρ g u)
      = ((∑ x : X, ρ (x : G)) * ρ g) u := (Module.End.mul_apply _ _ _).symm
    _ = (ρ g * (∑ x : X, ρ (x : G))) u := by rw [hcomm]
    _ = ρ g ((∑ x : X, ρ (x : G)) u) := Module.End.mul_apply _ _ _
    _ = ρ g 0 := by rw [LinearMap.mem_ker.mp hu]
    _ = 0 := map_zero (ρ g)

private theorem false_of_module_data
    {H : Type} [Group H] [Finite H]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Nontrivial W]
    (ρ : Representation (ZMod 2) H W)
    {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hr : r.Prime)
    (A : Subgroup H) (hA : CFSG.Open.IsElemAbelian q A) (hA2 : q ^ 2 ≤ Nat.card A)
    (D : Subgroup H) (hD : Nat.card D = r) (hHtop : A ⊔ D = ⊤)
    (hDA : D ≤ Subgroup.normalizer (A : Set H))
    (hCD : A ⊓ Subgroup.centralizer (D : Set H) = ⊥)
    (hfixA : fixSub ρ A = ⊥)
    (hfaith : ∀ a ∈ A, (∀ w : W, ρ a w = w) → a = 1)
    (hfixD : Module.finrank (ZMod 2) (fixSub ρ D) ≤ 1) :
    False := by
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have hA1 : A ≠ ⊥ := by
    intro hbot
    have hc : Nat.card A = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hc] at hA2
    have : 2 ≤ q := hq.two_le
    nlinarith
  have htop := iSup_fixSub_hyperplane_eq_top ρ hq hq2 hA hA1
  have hind := iSupIndep_fixSub_hyperplane ρ hq hq2 hA hfixA
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    have hcard : 1 < Nat.card D := by rw [hD]; exact hr.one_lt
    haveI : Nontrivial D := (Finite.one_lt_card_iff_nontrivial).mp hcard
    obtain ⟨d₀, hd0⟩ := exists_ne (1 : D)
    exact ⟨(d₀ : H), d₀.2, fun h => hd0 (Subtype.ext h)⟩
  have hdr : d ^ r = 1 := by
    have h1 : (⟨d, hdD⟩ : D) ^ Nat.card D = 1 := pow_card_eq_one'
    have h2 : d ^ Nat.card D = 1 := by
      have hh := congrArg (fun x : D => (x : H)) h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at hh
    rwa [hD] at h2
  have hDgen : D = Subgroup.zpowers d := by
    have hbD : Subgroup.zpowers d = D := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdD) ?_
      rw [Nat.card_zpowers]
      have hdvd : orderOf d ∣ Nat.card D := by
        have := orderOf_dvd_natCard (⟨d, hdD⟩ : D)
        simpa using this
      rw [hD] at hdvd
      haveI : Fact r.Prime := ⟨hr⟩
      have hord : orderOf d = r := by
        rcases hr.eq_one_or_self_of_dvd (orderOf d) hdvd with h1 | h1
        · exact absurd h1 (orderOf_eq_one_iff.not.mpr hd1)
        · exact h1
      rw [hord, hD]
    exact hbD.symm
  have hΔne : ∃ B : hyperplaneSet q A, fixSub ρ (B : Subgroup H) ≠ ⊥ := by
    by_contra h
    push Not at h
    have hle : (⨆ B : hyperplaneSet q A, fixSub ρ (B : Subgroup H)) ≤ ⊥ :=
      iSup_le (fun B => le_bot_iff.mpr (h B))
    rw [htop] at hle
    exact bot_ne_top (le_antisymm hle bot_le).symm
  by_cases hcase : ∃ B : hyperplaneSet q A,
      fixSub ρ (B : Subgroup H) ≠ ⊥ ∧ B.1.map (MulAut.conj d).toMonoidHom ≠ B.1
  ·
    obtain ⟨B, hBne, hBnf⟩ := hcase
    let o : ZMod r → hyperplaneSet q A := fun j =>
      ⟨B.1.map (MulAut.conj (d ^ j.val)).toMonoidHom,
        map_conj_mem_hyperplaneSet B.2 (hDA (D.pow_mem hdD j.val))⟩
    have ho : Function.Injective o := by
      intro i j hij
      exact map_conj_zpow_injective hr hD hdD hd1 hBnf (congrArg Subtype.val hij)
    have hind_o : iSupIndep (fun j : ZMod r =>
        fixSub ρ ((o j : hyperplaneSet q A) : Subgroup H)) := hind.comp ho
    let Φ : ↥(fixSub ρ B) →ₗ[ZMod 2] W :=
      ∑ j : ZMod r, (ρ (d ^ j.val)).comp (Submodule.subtype (fixSub ρ B))
    have hΦapply : ∀ v : ↥(fixSub ρ B), Φ v = ∑ j : ZMod r, ρ (d ^ j.val) v := by
      intro v
      simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    have hΦmem : ∀ v : ↥(fixSub ρ B), Φ v ∈ fixSub ρ D := by
      intro v
      have hdΦ : ρ d (Φ v) = Φ v := by
        have h1 : ∀ j : ZMod r, ρ d (ρ (d ^ j.val) v) = ρ (d ^ (j + 1).val) v := by
          intro j
          rw [← Module.End.mul_apply, ← map_mul, mul_pow_zmod_val hr hd1 hdr j]
        calc ρ d (Φ v) = ∑ j : ZMod r, ρ d (ρ (d ^ j.val) v) := by
              rw [hΦapply v, map_sum]
          _ = ∑ j : ZMod r, ρ (d ^ (j + 1).val) v := Finset.sum_congr rfl (fun j _ => h1 j)
          _ = ∑ j : ZMod r, ρ (d ^ j.val) v :=
                Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun j => rfl)
          _ = Φ v := (hΦapply v).symm
      let S : Subgroup H :=
        { carrier := {g | ρ g (Φ v) = Φ v}
          mul_mem' := fun {g h} hg hh => by
            show ρ (g * h) (Φ v) = Φ v
            rw [map_mul, Module.End.mul_apply, hh, hg]
          one_mem' := by
            show ρ 1 (Φ v) = Φ v
            rw [map_one, Module.End.one_apply]
          inv_mem' := fun {g} hg => by
            show ρ g⁻¹ (Φ v) = Φ v
            calc ρ g⁻¹ (Φ v) = ρ g⁻¹ (ρ g (Φ v)) := by rw [hg]
              _ = ρ (g⁻¹ * g) (Φ v) := by rw [map_mul, Module.End.mul_apply]
              _ = Φ v := by rw [inv_mul_cancel, map_one, Module.End.one_apply] }
      rw [mem_fixSub]
      intro g hg
      rw [hDgen] at hg
      exact Subgroup.zpowers_le.mpr (show d ∈ S from hdΦ) hg
    have hΦinj : Function.Injective Φ := by
      intro v w hvw
      have h0 : ∑ j : ZMod r, ρ (d ^ j.val) ((v : W) - (w : W)) = 0 := by
        rw [hΦapply v, hΦapply w] at hvw
        have h' : (∑ j : ZMod r, ρ (d ^ j.val) (v : W)) -
            (∑ j : ZMod r, ρ (d ^ j.val) (w : W)) = 0 := sub_eq_zero.mpr hvw
        rw [← Finset.sum_sub_distrib] at h'
        simpa only [map_sub] using h'
      have hmem : ∀ j : ZMod r, ρ (d ^ j.val) ((v : W) - (w : W)) ∈
          fixSub ρ ((o j : hyperplaneSet q A) : Subgroup H) := by
        intro j
        rw [mem_fixSub]
        intro b hb
        obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.mp hb
        have hb0' : (ρ b0) ((v : W) - (w : W)) = (v : W) - (w : W) := by
          have h := (mem_fixSub.mp (v - w).2) b0 hb0
          simpa using h
        calc ρ (d ^ j.val * b0 * (d ^ j.val)⁻¹) (ρ (d ^ j.val) ((v : W) - (w : W)))
            = ρ ((d ^ j.val * b0 * (d ^ j.val)⁻¹) * (d ^ j.val)) ((v : W) - (w : W)) := by
              rw [← Module.End.mul_apply, ← map_mul]
          _ = ρ (d ^ j.val * b0) ((v : W) - (w : W)) := by
              congr 1
              group
          _ = ρ (d ^ j.val) (ρ b0 ((v : W) - (w : W))) := by rw [map_mul, Module.End.mul_apply]
          _ = ρ (d ^ j.val) ((v : W) - (w : W)) := by rw [hb0']
      have hsum : ∑ j ∈ (Finset.univ : Finset (ZMod r)),
          ρ (d ^ j.val) ((v : W) - (w : W)) = 0 := by
        simpa using h0
      have hall := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
        (fun j : ZMod r => fixSub ρ ((o j : hyperplaneSet q A) : Subgroup H))).mp
        hind_o Finset.univ (fun j => ρ (d ^ j.val) ((v : W) - (w : W)))
          (fun i _ => hmem i) hsum
      have h0' : ρ (d ^ (0 : ZMod r).val) ((v : W) - (w : W)) = 0 :=
        hall 0 (Finset.mem_univ 0)
      have hsub : (v : W) - (w : W) = 0 := by simpa using h0'
      exact Subtype.ext (sub_eq_zero.mp hsub)
    have hrange_le : LinearMap.range Φ ≤ fixSub ρ D := by
      rintro y ⟨v, rfl⟩
      exact hΦmem v
    have hCdim : 2 ≤ Module.finrank (ZMod 2) ↥(fixSub ρ B) :=
      two_le_finrank_of_hyperplane_ne_bot ρ hq A B.1 hA B.2 hfixA hBne
    have hfin : Module.finrank (ZMod 2) ↥(fixSub ρ B) ≤
        Module.finrank (ZMod 2) (fixSub ρ D) :=
      calc Module.finrank (ZMod 2) ↥(fixSub ρ B)
          = Module.finrank (ZMod 2) (LinearMap.range Φ) :=
            (LinearMap.finrank_range_of_inj hΦinj).symm
        _ ≤ Module.finrank (ZMod 2) (fixSub ρ D) := Submodule.finrank_mono hrange_le
    omega
  ·
    push Not at hcase
    obtain ⟨B0, hB0ne⟩ := hΔne
    by_cases htwo : ∃ B B' : hyperplaneSet q A, B ≠ B' ∧
        fixSub ρ (B : Subgroup H) ≠ ⊥ ∧ fixSub ρ (B' : Subgroup H) ≠ ⊥
    ·
      obtain ⟨B, B', hBB', hBne, hB'ne⟩ := htwo
      have hBD : D ≤ Subgroup.normalizer (B.1 : Set H) := by
        rw [hDgen]
        exact Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hcase B hBne))
      have hB'D : D ≤ Subgroup.normalizer (B'.1 : Set H) := by
        rw [hDgen]
        exact Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hcase B' hB'ne))
      have h1 := inf_fixSub_fixSub_ne_bot ρ hq hq2 hr A D hA hHtop hDA hCD hD hfixA
        B.1 B.2.1 hBD hBne
      have h2 := inf_fixSub_fixSub_ne_bot ρ hq hq2 hr A D hA hHtop hDA hCD hD hfixA
        B'.1 B'.2.1 hB'D hB'ne
      have h1pos : 0 < Module.finrank (ZMod 2) ↥(fixSub ρ B.1 ⊓ fixSub ρ D) :=
        Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr h1)
      have h2pos : 0 < Module.finrank (ZMod 2) ↥(fixSub ρ B'.1 ⊓ fixSub ρ D) :=
        Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr h2)
      have hdisj : (fixSub ρ B.1 ⊓ fixSub ρ D) ⊓ (fixSub ρ B'.1 ⊓ fixSub ρ D) = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨⟨hx1, -⟩, ⟨hx2, -⟩⟩
        exact Submodule.disjoint_def.mp (hind.pairwiseDisjoint hBB') x hx1 hx2
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq
        (fixSub ρ B.1 ⊓ fixSub ρ D) (fixSub ρ B'.1 ⊓ fixSub ρ D)
      rw [hdisj, finrank_bot, add_zero] at hsup
      have hmono : Module.finrank (ZMod 2)
          (((fixSub ρ B.1 ⊓ fixSub ρ D) ⊔ (fixSub ρ B'.1 ⊓ fixSub ρ D) :
            Submodule (ZMod 2) W)) ≤
          Module.finrank (ZMod 2) (fixSub ρ D) :=
        Submodule.finrank_mono (sup_le inf_le_right inf_le_right)
      omega
    ·
      push Not at htwo
      have hall : ∀ B : hyperplaneSet q A, fixSub ρ (B : Subgroup H) = ⊥ ∨ B = B0 := by
        intro B
        by_cases hB : fixSub ρ (B : Subgroup H) = ⊥
        · exact Or.inl hB
        · refine Or.inr (by_contra fun hBB' => hB0ne (htwo B B0 hBB' hB))
      have hsupB : (⨆ B : hyperplaneSet q A, fixSub ρ (B : Subgroup H)) ≤
          fixSub ρ (B0 : Subgroup H) := by
        refine iSup_le (fun B => ?_)
        rcases hall B with h | h
        · rw [h]; exact bot_le
        · rw [h]
      have hB0top : fixSub ρ (B0 : Subgroup H) = ⊤ := by
        rw [← htop]
        exact le_antisymm (le_iSup (fun B : hyperplaneSet q A => fixSub ρ (B : Subgroup H)) B0) hsupB
      have hB0bot : B0.1 ≤ (⊥ : Subgroup H) := by
        intro b hb
        have : ρ b = 1 := by
          refine LinearMap.ext fun w => ?_
          have hw : w ∈ fixSub ρ (B0 : Subgroup H) := by rw [hB0top]; trivial
          exact (mem_fixSub.mp hw) b hb
        exact Subgroup.mem_bot.mpr (hfaith b (B0.2.1 hb) (fun w => by rw [this, Module.End.one_apply]))
      have hB0ne' : B0.1 ≠ ⊥ := by
        intro hbot
        have hcard : Nat.card B0.1 * q = Nat.card A := by
          have hthis := Subgroup.card_mul_index (H := B0.1.subgroupOf A)
          rw [show (B0.1.subgroupOf A).index = q from B0.2.2] at hthis
          have hc : Nat.card (B0.1.subgroupOf A) = Nat.card B0.1 :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe B0.2.1).toEquiv
          rwa [hc] at hthis
        rw [hbot, Subgroup.card_bot, one_mul] at hcard
        have : q ^ 2 ≤ q := hcard ▸ hA2
        nlinarith [hq.two_le]
      exact hB0ne' (le_bot_iff.mp hB0bot)

private theorem exists_elementary_abelian_subgroup
    {G : Type} [Group G] [Finite G]
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (Q D : Subgroup G) (hQ : IsPGroup q Q) (hQab : IsMulCommutative ↥Q)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) (hQD : ⁅D, Q⁆ = Q)
    (hcop : Nat.Coprime (Nat.card D) (Nat.card Q)) (hQnc : ¬ IsCyclic ↥Q) :
    ∃ E : Subgroup G, E ≤ Q ∧ CFSG.Open.IsElemAbelian q E ∧ q ^ 2 ≤ Nat.card E ∧
      D ≤ Subgroup.normalizer (E : Set G) ∧
      E ⊓ Subgroup.centralizer (D : Set G) = ⊥ := by
  obtain ⟨E₀, hE₀Q, hE₀ea, hE₀card⟩ :=
    CFSG.Goldschmidt.G55.exists_isElemAbelian_card_sq hq hq2 hQ hQnc
  let E : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ x ^ q = 1}
      mul_mem' := by
        rintro x y ⟨hxQ, hxq⟩ ⟨hyQ, hyq⟩
        refine ⟨Q.mul_mem hxQ hyQ, ?_⟩
        have hcomm : Commute x y :=
          show x * y = y * x from
            congrArg (Subtype.val : ↥Q → G) (hQab.is_comm.comm ⟨x, hxQ⟩ ⟨y, hyQ⟩)
        rw [hcomm.mul_pow, hxq, hyq, one_mul]
      one_mem' := ⟨Q.one_mem, one_pow q⟩
      inv_mem' := by
        rintro x ⟨hxQ, hxq⟩
        exact ⟨Q.inv_mem hxQ, by rw [inv_pow, hxq, inv_one]⟩ }
  have hEQ : E ≤ Q := fun _ hx => hx.1
  have hEea : CFSG.Open.IsElemAbelian q E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hx.2⟩
    exact congrArg (Subtype.val : ↥Q → G)
      (hQab.is_comm.comm ⟨a.1, hEQ a.2⟩ ⟨b.1, hEQ b.2⟩)
  have hE₀E : E₀ ≤ E := by
    intro x hx
    exact ⟨hE₀Q hx, hE₀ea.2 x hx⟩
  have hEcard : q ^ 2 ≤ Nat.card E := by
    have hdvd : Nat.card E₀ ∣ Nat.card E := Subgroup.card_dvd_of_le hE₀E
    have := Nat.le_of_dvd Nat.card_pos hdvd
    omega
  have hDE : D ≤ Subgroup.normalizer (E : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hDQ hd) x).mp hx.1, ?_⟩
      rw [← MulAut.conj_apply, ← map_pow, hx.2, map_one]
    · intro hx
      have hxE : d⁻¹ * (d * x * d⁻¹) * d ∈ E := by
        refine ⟨?_, ?_⟩
        · have h := (Subgroup.mem_normalizer_iff.mp (hDQ (D.inv_mem hd)) (d * x * d⁻¹)).mp hx.1
          simpa only [inv_inv] using h
        · have hconj : (d⁻¹ * (d * x * d⁻¹) * d) ^ q = 1 := by
            rw [show d⁻¹ * (d * x * d⁻¹) * d = MulAut.conj d⁻¹ (d * x * d⁻¹) by
              rw [MulAut.conj_apply, inv_inv]]
            rw [← map_pow, hx.2, map_one]
          exact hconj
      rwa [show d⁻¹ * (d * x * d⁻¹) * d = x by group] at hxE
  have hCE : E ⊓ Subgroup.centralizer (D : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxQ : x ∈ Q ⊓ Subgroup.centralizer (D : Set G) := ⟨hEQ hx.1, hx.2⟩
    rw [inf_centralizer_eq_bot_of_commutator_eq_top hQab hDQ hQD hcop] at hxQ
    exact Subgroup.mem_bot.mp hxQ
  exact ⟨E, hEQ, hEea, hEcard, hDE, hCE⟩

theorem k47_two {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hq2 : q ≠ 2) (hr2 : r ≠ 2) (hqr : q ≠ r)
    (D : Subgroup G) (hD : Nat.card D = r) (hfix : Module.finrank (ZMod 2) (fixSub ρ D) ≤ 1)
    (Q : Subgroup G) (hQ : IsPGroup q Q) (hQab : IsMulCommutative ↥Q)
    (hDQ : D ≤ normalizer (Q : Set G)) (hQD : ⁅D, Q⁆ = Q) : IsCyclic ↥Q := by
  by_contra hQnc
  haveI : Fact q.Prime := ⟨hq⟩
  have hcop : Nat.Coprime (Nat.card D) (Nat.card Q) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    rw [hD, hk]
    have hrg : ¬ r ∣ q := fun h => hqr ((Nat.prime_dvd_prime_iff_eq hr hq).mp h).symm
    exact (hr.coprime_iff_not_dvd.mpr hrg).pow_right k
  obtain ⟨E, hEQ, hEea, hEcard, hDE, hCE⟩ :=
    exists_elementary_abelian_subgroup hq hq2 Q D hQ hQab hDQ hQD hcop hQnc
  haveI : Fintype ↥E := Fintype.ofFinite ↥E
  have hEp : IsPGroup q E := fun y => ⟨1, Subtype.ext (by simpa using hEea.2 y y.2)⟩
  obtain ⟨kE, hkE⟩ := IsPGroup.iff_card.mp hEp
  have hEodd : Odd (Nat.card E) := by
    rw [hkE]; exact (hq.odd_of_ne_two hq2).pow (n := kE)
  let e : Module.End (ZMod 2) V := ∑ x : E, ρ (x : G)
  have heidem : e * e = e := sum_rho_mul_self ρ E hEodd
  have hrange : LinearMap.range e = fixSub ρ E := range_sum_rho ρ E hEodd
  let W : Submodule (ZMod 2) V := LinearMap.ker e
  have hcompl : IsCompl (fixSub ρ E) W := by
    have h := isCompl_range_ker e heidem
    rwa [hrange] at h
  have hfixker : fixSub ρ E ⊓ W = ⊥ := fixSub_inf_ker_sum_rho ρ E hEodd
  let H : Subgroup G := E ⊔ D
  have hEH : E ≤ H := le_sup_left
  have hDH : D ≤ H := le_sup_right
  have hHnorm : H ≤ Subgroup.normalizer (E : Set G) := sup_le Subgroup.le_normalizer hDE
  have hWin : ∀ g ∈ H, W.map (ρ g) ≤ W :=
    fun g hg => ker_sum_rho_invariant ρ E hEodd (hHnorm hg)
  have hWin' : ∀ g ∈ H, ∀ v ∈ W, ρ g v ∈ W :=
    fun g hg v hv => hWin g hg (Submodule.mem_map.mpr ⟨v, hv, rfl⟩)
  let ρW : Representation (ZMod 2) ↥H ↥W :=
    { toFun := fun h => (ρ (h : G)).restrict (p := W) (q := W) (fun v hv => hWin' h.1 h.2 v hv)
      map_one' := by ext v; simp
      map_mul' := by intro a b; ext v; simp [map_mul, Module.End.mul_apply] }
  let A : Subgroup ↥H := E.subgroupOf H
  let D' : Subgroup ↥H := D.subgroupOf H
  have hcardA : Nat.card A = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
  have hcardD : Nat.card D' = r := by
    have h : Nat.card D' = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv
    rw [h, hD]
  have hAea : CFSG.Open.IsElemAbelian q A := by
    refine ⟨?_, ?_⟩
    · refine IsMulCommutative.of_comm (fun a b => ?_)
      have hcomm := hEea.1.is_comm.comm
        ((Subgroup.subgroupOfEquivOfLe hEH) a) ((Subgroup.subgroupOfEquivOfLe hEH) b)
      simpa using congrArg (fun x : ↥E => (Subgroup.subgroupOfEquivOfLe hEH).symm x) hcomm
    · intro x hx
      exact Subtype.ext (by simpa using hEea.2 (x : G) (Subgroup.mem_subgroupOf.mp hx))
  have hA2 : q ^ 2 ≤ Nat.card A := by rw [hcardA]; exact hEcard
  have hHtop : A ⊔ D' = ⊤ := by
    rw [show A ⊔ D' = (E ⊔ D).subgroupOf H from (Subgroup.subgroupOf_sup hEH hDH).symm]
    exact Subgroup.subgroupOf_self (H := E ⊔ D)
  have hDA' : D' ≤ Subgroup.normalizer (A : Set ↥H) := by
    intro d hd
    have hdn := Subgroup.mem_normalizer_iff.mp (hDE (Subgroup.mem_subgroupOf.mp hd))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hdn (x : G)
  have hCD' : A ⊓ Subgroup.centralizer (D' : Set ↥H) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx.1
    have hxC : (x : G) ∈ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hgD' : (⟨g, hDH hg⟩ : ↥H) ∈ D' := by
        rw [Subgroup.mem_subgroupOf]; exact hg
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx.2) (⟨g, hDH hg⟩ : ↥H) hgD'
      exact congrArg (fun y : ↥H => (y : G)) hcomm
    have hxbot : (x : G) ∈ E ⊓ Subgroup.centralizer (D : Set G) := ⟨hxE, hxC⟩
    rw [hCE, Subgroup.mem_bot] at hxbot
    exact Subtype.ext hxbot
  have hfixA : fixSub ρW A = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    have hwE : (w : V) ∈ fixSub ρ E := by
      rw [mem_fixSub]
      intro x hx
      have hxA : (⟨x, hEH hx⟩ : ↥H) ∈ A := by
        rw [Subgroup.mem_subgroupOf]; exact hx
      have h := (mem_fixSub.mp hw) (⟨x, hEH hx⟩ : ↥H) hxA
      exact congrArg Subtype.val h
    have hwbot : (w : V) ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← hfixker]
      exact ⟨hwE, w.2⟩
    rw [Submodule.mem_bot] at hwbot
    exact Subtype.ext hwbot
  have hfaith : ∀ a ∈ A, (∀ w : ↥W, ρW a w = w) → a = 1 := by
    intro a ha htriv
    have haE : (a : G) ∈ E := Subgroup.mem_subgroupOf.mp ha
    have hfix : ∀ v : V, ρ (a : G) v = v := by
      intro v
      have hv : v ∈ (fixSub ρ E : Submodule (ZMod 2) V) ⊔ W := by
        have hc := hcompl.2
        rw [codisjoint_iff] at hc
        rw [hc]; trivial
      obtain ⟨u, hu, w, hw, huv⟩ := Submodule.mem_sup.mp hv
      rw [← huv, map_add]
      congr 1
      · exact (mem_fixSub.mp hu) (a : G) haE
      · exact congrArg Subtype.val (htriv ⟨w, hw⟩)
    have heq : ρ (a : G) = 1 := LinearMap.ext hfix
    have ha1 : (a : G) = 1 := hρ (by rw [heq, map_one])
    exact Subtype.ext ha1
  have hfixD : Module.finrank (ZMod 2) (fixSub ρW D') ≤ 1 := by
    have hmaps : ∀ v : ↥(fixSub ρW D'), (v : V) ∈ fixSub ρ D := by
      intro v
      rw [mem_fixSub]
      intro d hd
      have hdD' : (⟨d, hDH hd⟩ : ↥H) ∈ D' := by
        rw [Subgroup.mem_subgroupOf]; exact hd
      have hv := (mem_fixSub.mp v.2) (⟨d, hDH hd⟩ : ↥H) hdD'
      exact congrArg Subtype.val hv
    let f : ↥(fixSub ρW D') →ₗ[ZMod 2] (fixSub ρ D) :=
      { toFun := fun v => ⟨(v : V), hmaps v⟩
        map_add' := by intro a b; ext; rfl
        map_smul' := by intro c a; ext; rfl }
    have hfinj : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : ↥(fixSub ρ D) => (x : V)) h
    exact (LinearMap.finrank_le_finrank_of_injective (f := f) hfinj).trans hfix
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hker : LinearMap.ker e = ⊥ := hbot
    have he1 : e = 1 := by
      have hinj : Function.Injective e := fun a b h => by
        have h1 : e (a - b) = 0 := by rw [map_sub, h, sub_self]
        have h2 : a - b ∈ LinearMap.ker e := LinearMap.mem_ker.mpr h1
        rw [hker, Submodule.mem_bot] at h2
        rwa [sub_eq_zero] at h2
      refine LinearMap.ext fun v => ?_
      show e v = v
      exact hinj (by rw [← Module.End.mul_apply, heidem])
    have hEbot : E = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have hxmul : ρ x * e = e := mul_sum_rho ρ E hx
      have hx1 : ρ x = 1 := by simpa [he1] using hxmul
      exact hρ (by rw [hx1, map_one])
    have hcard1 : Nat.card E = 1 := by rw [hEbot, Subgroup.card_bot]
    have hle1 := hEcard
    rw [hcard1] at hle1
    nlinarith [hq.two_le]
  haveI : Nontrivial ↥W := Submodule.nontrivial_iff_ne_bot.mpr hWne
  exact false_of_module_data ρW hq hq2 hr A hAea hA2 D' hcardD hHtop hDA' hCD' hfixA hfaith hfixD

end CFSG.LocalAnalysis.UniquenessCase.UCK
