module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec15.Sylow155CDTest
import CFSG.RankThree.PartTwo.Sec15.Sylow155NODeg
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6Cent
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.Coprime.PrimeCubeTorsionExtension
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentPQ
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155CD

open CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {Q : Type*} [Group Q]

private theorem exists_mul_of_mem_sup {J₁ J₂ : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥) {g : Q}
    (hg : g ∈ J₁ ⊔ J₂) : ∃ y ∈ J₁, ∃ v ∈ J₂, g = y * v := by
  have hle : J₂ ≤ Subgroup.normalizer (J₁ : Set Q) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm, hJ])).trans (Subgroup.centralizer_le_normalizer _)
  have h : g ∈ ((J₁ ⊔ J₂ : Subgroup Q) : Set Q) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left J₁ J₂ hle] at h
  obtain ⟨y, hy, v, hv, rfl⟩ := h
  exact ⟨y, hy, v, hv, rfl⟩

private theorem mem_inf_of_mem_sup {J₁ J₂ : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥)
    (hZ₁ : J₁ ⊓ J₂ = Sec14.Item148PtRes.centerIn J₁)
    (hZ₂ : J₁ ⊓ J₂ = Sec14.Item148PtRes.centerIn J₂) {u : Q}
    (huc : u ∈ Subgroup.centralizer ((J₁ ⊔ J₂ : Subgroup Q) : Set Q)) (huY : u ∈ J₁ ⊔ J₂) :
    u ∈ J₁ ⊓ J₂ := by
  have hcu : ∀ x ∈ J₁ ⊔ J₂, x * u = u * x := fun x hx => Subgroup.mem_centralizer_iff.mp huc x hx
  obtain ⟨y, hy, v, hv, rfl⟩ := exists_mul_of_mem_sup hJ huY
  have hyZ : y ∈ Sec14.Item148PtRes.centerIn J₁ := by
    refine Sec14.Item148PtRes.mem_centerIn_iff.mpr ⟨hy, Subgroup.mem_center_iff.mpr fun x => ?_⟩
    apply Subtype.ext
    have h1 : (x : Q) * (y * v) = (y * v) * x := hcu x (Subgroup.mem_sup_left x.2)
    have h2 : (x : Q) * v = v * x :=
      Sec14.Item148PtRes.commute_of_commutator_eq_bot hJ x.2 hv
    have h3 : (x : Q) * y * v = y * x * v := by
      calc (x : Q) * y * v = x * (y * v) := by rw [mul_assoc]
        _ = (y * v) * x := h1
        _ = y * (v * x) := by rw [mul_assoc]
        _ = y * (x * v) := by rw [h2]
        _ = y * x * v := by rw [mul_assoc]
    exact mul_right_cancel h3
  have hyJ₂ : y ∈ J₂ := by
    have : y ∈ J₁ ⊓ J₂ := by
      rw [hZ₁]
      exact hyZ
    exact this.2
  have huJ₂ : y * v ∈ J₂ := J₂.mul_mem hyJ₂ hv
  rw [hZ₂]
  refine Sec14.Item148PtRes.mem_centerIn_iff.mpr ⟨huJ₂, Subgroup.mem_center_iff.mpr fun x => ?_⟩
  apply Subtype.ext
  exact hcu x (Subgroup.mem_sup_right x.2)

private theorem mem_normalizer_map_subtype {J : Subgroup Q} {V : Subgroup ↥J} {y : ↥J}
    (hy : y ∈ Subgroup.normalizer (V : Set ↥J)) :
    (y : Q) ∈ Subgroup.normalizer ((V.map J.subtype : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff] at hy ⊢
  intro x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨y * v * y⁻¹, (hy v).mp hv, rfl⟩
  · rintro ⟨w, hw, hwx⟩
    have hxJ : x ∈ J := by
      have : x = (y : Q)⁻¹ * (w : Q) * y := by
        rw [show (w : Q) = y * x * (y : Q)⁻¹ from hwx]
        group
      rw [this]
      exact J.mul_mem (J.mul_mem (J.inv_mem y.2) w.2) y.2
    refine ⟨⟨x, hxJ⟩, (hy _).mpr ?_, rfl⟩
    have : y * (⟨x, hxJ⟩ : ↥J) * y⁻¹ = w := Subtype.ext hwx.symm
    rw [this]
    exact hw

private theorem normal_centralizer_of_normal {Y : Subgroup Q} (hY : Y.Normal) :
    (Subgroup.centralizer (Y : Set Q)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro h hh
  have h1 : g⁻¹ * h * g ∈ Y := by simpa using hY.conj_mem h hh g⁻¹
  have h2 := hn _ h1
  calc h * (g * n * g⁻¹) = g * ((g⁻¹ * h * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * h * g)) * g⁻¹ := by rw [h2]
    _ = g * n * g⁻¹ * h := by group

variable [Finite Q]

theorem mem_inf_of_mem_centralizer {J₁ J₂ : Subgroup Q}
    (hJ : ⁅J₁, J₂⁆ = ⊥) (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3)
    (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6)))
    (hR4 : ∀ E T : Subgroup Q, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 81 →
      IsPGroup 2 T → T ≠ ⊥ → E ≤ Subgroup.normalizer (T : Set Q) → False)
    {u : Q} (hu : u ∈ Subgroup.centralizer ((J₁ ⊔ J₂ : Subgroup Q) : Set Q)) (hu3 : u ^ 3 = 1) :
    u ∈ J₁ ⊓ J₂ := by
  by_contra hunot
  have hc₁ : Nat.card (Subgroup.center ↥J₁) = 3 := hT₁.1
  have hc₂ : Nat.card (Subgroup.center ↥J₂) = 3 := hT₂.1
  have hZ₁ := Sec14.Item148PtRes.inf_eq_centerIn_left hJ h3 hc₁
  have hZ₂ := Sec14.Item148PtRes.inf_eq_centerIn_right hJ h3 hc₂
  have hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := fun a ha b hb =>
    Sec14.Item148PtRes.commute_of_commutator_eq_bot hJ ha hb
  have hcu : ∀ x ∈ J₁ ⊔ J₂, x * u = u * x := fun x hx => Subgroup.mem_centralizer_iff.mp hu x hx
  obtain ⟨y₁, hy₁3, hy₁Z, V, hV2, hV1, hy₁V⟩ := exists_pow_three_le_normalizer_two hT₁
  obtain ⟨y₂, hy₂3, hy₂Z⟩ := Sylow155NO.exists_pow_three_not_mem_center hT₂
  have hy₁3' : (y₁ : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hy₁3
  have hy₂3' : (y₂ : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hy₂3
  have hy₁Z' : (y₁ : Q) ∉ J₁ ⊓ J₂ := by
    rw [hZ₁]
    intro h
    exact hy₁Z (Sec14.Item148PtRes.mem_centerIn_iff.mp h).2
  have hy₂Z' : (y₂ : Q) ∉ J₁ ⊓ J₂ := by
    rw [hZ₂]
    intro h
    exact hy₂Z (Sec14.Item148PtRes.mem_centerIn_iff.mp h).2
  have hZe : CFSG.Assembly.IsElemAbelian 3 (J₁ ⊓ J₂) := by
    refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hcomm a a.2.1 b b.2.2), fun x hx => ?_⟩
    have h := Subgroup.orderOf_dvd_natCard (J₁ ⊓ J₂) hx
    rw [h3] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hE₁J : (J₁ ⊓ J₂) ⊔ Subgroup.zpowers (y₁ : Q) ≤ J₁ :=
    sup_le inf_le_left (Subgroup.zpowers_le.mpr y₁.2)
  obtain ⟨hE₁, hE₁c⟩ := Sec5.isElemAbelian_sup_zpowers (p := 3) hZe hy₁Z' hy₁3' fun a ha =>
    (hcomm y₁ y₁.2 a ha.2).symm
  have hy₂E₁ : (y₂ : Q) ∉ (J₁ ⊓ J₂) ⊔ Subgroup.zpowers (y₁ : Q) := fun h =>
    hy₂Z' ⟨hE₁J h, y₂.2⟩
  have hE₂Y : ((J₁ ⊓ J₂) ⊔ Subgroup.zpowers (y₁ : Q)) ⊔ Subgroup.zpowers (y₂ : Q) ≤ J₁ ⊔ J₂ :=
    sup_le (hE₁J.trans le_sup_left) (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right y₂.2))
  obtain ⟨hE₂, hE₂c⟩ := Sec5.isElemAbelian_sup_zpowers (p := 3) hE₁ hy₂E₁ hy₂3' fun a ha =>
    hcomm a (hE₁J ha) y₂ y₂.2
  have huE₂ : u ∉ ((J₁ ⊓ J₂) ⊔ Subgroup.zpowers (y₁ : Q)) ⊔ Subgroup.zpowers (y₂ : Q) := fun h =>
    hunot (mem_inf_of_mem_sup hJ hZ₁ hZ₂ hu (hE₂Y h))
  obtain ⟨hE, hEc⟩ := Sec5.isElemAbelian_sup_zpowers (p := 3) hE₂ huE₂ hu3 fun a ha =>
    hcu a (hE₂Y ha)
  have hE81 : Nat.card
      ↥(((J₁ ⊓ J₂) ⊔ Subgroup.zpowers (y₁ : Q) ⊔ Subgroup.zpowers (y₂ : Q)) ⊔
        Subgroup.zpowers u : Subgroup Q) = 81 := by
    rw [hEc, hE₂c, hE₁c, h3]
  have hV'2 : IsPGroup 2 (V.map J₁.subtype) := hV2.map J₁.subtype
  have hV'1 : V.map J₁.subtype ≠ ⊥ := fun h =>
    hV1 ((Subgroup.map_eq_bot_iff_of_injective V J₁.subtype_injective).mp h)
  have hV'J : V.map J₁.subtype ≤ J₁ := Subgroup.map_subtype_le V
  have hcent : ∀ g : Q, (∀ x ∈ J₁, x * g = g * x) →
      g ∈ Subgroup.normalizer ((V.map J₁.subtype : Subgroup Q) : Set Q) := fun g hg =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun h hh => hg h (hV'J hh))
  refine hR4 _ (V.map J₁.subtype) hE hE81 hV'2 hV'1 ?_
  refine sup_le (sup_le (sup_le (fun a ha => hcent a fun x hx => hcomm x hx a ha.2)
    (Subgroup.zpowers_le.mpr (mem_normalizer_map_subtype hy₁V)))
    (Subgroup.zpowers_le.mpr (hcent y₂ fun x hx => hcomm x hx y₂ y₂.2)))
    (Subgroup.zpowers_le.mpr (hcent u fun x hx => hcu x (Subgroup.mem_sup_left hx)))

private theorem isCyclic_sylow_three {C Z : Subgroup Q} (hZ : Nat.card Z ≤ 3)
    (hCZ : ∀ x ∈ C, x ^ 3 = 1 → x ∈ Z) (P : Sylow 3 ↥C) : IsCyclic ↥P := by
  let f : ↥(P : Subgroup ↥C) →* Q := C.subtype.comp (P : Subgroup ↥C).subtype
  have hf : Function.Injective f := Subtype.coe_injective.comp Subtype.coe_injective
  have hZc : Nat.card (Z.comap f) ≤ 3 := by
    have := Subgroup.card_comap_dvd_of_injective Z f hf
    exact (Nat.le_of_dvd Nat.card_pos this).trans hZ
  have hcy := CFSG.RankThree.Coprime.isCyclic_of_forall_pow_eq_one_mem (p := 3) (by norm_num)
    P.isPGroup' ⊤ (Z.comap f) hZc fun x _ hx3 =>
      hCZ (f x) x.1.2 (by rw [← map_pow, hx3, map_one])
  exact (Subgroup.topEquiv.isCyclic).mp hcy

private theorem eq_one_of_normal_of_cyclic_sylow {C : Subgroup Q} (hCn : C.Normal)
    (hO : ∀ N : Subgroup Q, N.Normal → ¬ 3 ∣ Nat.card N → N = ⊥)
    (hcyc : ∀ P : Sylow 3 ↥C, IsCyclic ↥P)
    (hcen : ∀ x : ↥C, orderOf x = 3 → x ∈ Subgroup.center ↥C)
    {g : Q} (hg : g ∈ C) (hg3 : ¬ 3 ∣ orderOf g) : g = 1 := by
  obtain ⟨N, hNn, hNcop, hNp⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.hasNormalPComplement_of_cyclic_sylow_central (p := 3)
      hcyc hcen
  have hN3 : ¬ 3 ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hNcop
  have hmem : ∀ x : ↥C, ¬ 3 ∣ orderOf x → x ∈ N := by
    intro x hx
    have h1 : (x : ↥C ⧸ N) ^ orderOf x = 1 := by
      rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one]
    obtain ⟨k, hk⟩ := hNp (x : ↥C ⧸ N)
    have hcop : Nat.Coprime (orderOf x) (3 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hx).symm
    have h2 := pow_gcd_eq_one.mpr ⟨h1, hk⟩
    have hgcd : (orderOf x).gcd (3 ^ k) = 1 := hcop
    rw [hgcd] at h2
    exact (QuotientGroup.eq_one_iff x).mp (by simpa using h2)
  have hord : ∀ n : ↥C, n ∈ N → ¬ 3 ∣ orderOf n := fun n hn h =>
    hN3 (h.trans (Subgroup.orderOf_dvd_natCard N hn))
  have hNQ : (N.map C.subtype).Normal := by
    refine ⟨fun n hn q => ?_⟩
    obtain ⟨n₀, hn₀, rfl⟩ := hn
    have hqC : q * (n₀ : Q) * q⁻¹ ∈ C := hCn.conj_mem _ n₀.2 q
    have hq : (⟨q * (n₀ : Q) * q⁻¹, hqC⟩ : ↥C) ∈ N := by
      apply hmem
      rw [Subgroup.orderOf_mk]
      have h1 : orderOf (q * (n₀ : Q) * q⁻¹) = orderOf (n₀ : Q) :=
        orderOf_injective (MulAut.conj q).toMonoidHom (MulAut.conj q).injective (n₀ : Q)
      rw [h1, Subgroup.orderOf_coe]
      exact hord n₀ hn₀
    exact ⟨_, hq, rfl⟩
  have hN'3 : ¬ 3 ∣ Nat.card (N.map C.subtype) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hN3
  have hbot : N.map C.subtype = ⊥ := hO _ hNQ hN'3
  have hgN : (⟨g, hg⟩ : ↥C) ∈ N := by
    apply hmem
    rw [Subgroup.orderOf_mk]
    exact hg3
  have : g ∈ N.map C.subtype := ⟨⟨g, hg⟩, hgN, rfl⟩
  rw [hbot] at this
  exact Subgroup.mem_bot.mp this

theorem eq_one_of_mem_centralizer {J₁ J₂ : Subgroup Q}
    (hJ : ⁅J₁, J₂⁆ = ⊥) (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3)
    (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6)))
    (hX : (J₁ ⊔ J₂).Normal)
    (hO : ∀ N : Subgroup Q, N.Normal → ¬ 3 ∣ Nat.card N → N = ⊥)
    (hR4 : ∀ E T : Subgroup Q, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 81 →
      IsPGroup 2 T → T ≠ ⊥ → E ≤ Subgroup.normalizer (T : Set Q) → False)
    {g : Q} (hg : g ∈ Subgroup.centralizer ((J₁ ⊔ J₂ : Subgroup Q) : Set Q))
    (hg3 : ¬ 3 ∣ orderOf g) : g = 1 := by
  have hord3 : ∀ x : Q, x ∈ Subgroup.centralizer ((J₁ ⊔ J₂ : Subgroup Q) : Set Q) →
      x ^ 3 = 1 → x ∈ J₁ ⊓ J₂ := fun x hx hx3 =>
    mem_inf_of_mem_centralizer hJ h3 hT₁ hT₂ hR4 hx hx3
  refine eq_one_of_normal_of_cyclic_sylow (normal_centralizer_of_normal hX) hO ?_ ?_ hg hg3
  ·
    intro P
    exact isCyclic_sylow_three (Z := J₁ ⊓ J₂) h3.le (fun x hx hx3 => hord3 x hx hx3) P
  ·
    intro x hx
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hxZ : (x : Q) ∈ J₁ ⊓ J₂ := hord3 x x.2 (by simpa using congrArg Subtype.val hx3)
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp w.2 (x : Q) (Subgroup.mem_sup_left hxZ.1)).symm

end CFSG.RankThree.PartTwo.Sec15.Sylow155CD
