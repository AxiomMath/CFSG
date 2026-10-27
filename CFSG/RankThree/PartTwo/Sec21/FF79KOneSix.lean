module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
import CFSG.RankThree.PartTwo.Sec21.FF79KFrob
import CFSG.GroupTheory.GL52.FrobSevenThree
import CFSG.GF2Type.Smith1979.CaseIIExclL52
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G]

theorem conj_mem_of_mem_nor {H : Subgroup G} {g x : G} (hg : g ∈ Nor H) (hx : x ∈ H) :
    g * x * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

def fixMod (T₀ : Subgroup G) (E : Set G) : Subgroup G where
  carrier := {a | a ∈ Nor T₀ ∧ ∀ x ∈ E, a * x * a⁻¹ * x⁻¹ ∈ T₀}
  one_mem' := Set.mem_setOf.mpr ⟨one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, haE⟩ ⟨hb, hbE⟩
    refine ⟨mul_mem ha hb, fun x hx => ?_⟩
    have h1 : a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ ∈ T₀ := conj_mem_of_mem_nor ha (hbE x hx)
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
        a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem h1 (haE x hx)
  inv_mem' := by
    rintro a ⟨ha, haE⟩
    refine ⟨inv_mem ha, fun x hx => ?_⟩
    have h1 : a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a⁻¹⁻¹ ∈ T₀ :=
      conj_mem_of_mem_nor (inv_mem ha) (inv_mem (haE x hx))
    have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact h1

theorem mem_fixMod {T₀ : Subgroup G} {E : Set G} {a : G} :
    a ∈ fixMod T₀ E ↔ a ∈ Nor T₀ ∧ ∀ x ∈ E, a * x * a⁻¹ * x⁻¹ ∈ T₀ :=
  Iff.rfl

def omegaMod (T T₀ : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ T ⊓ Nor T₀ ∧ x ∈ fixMod T₀ (T ⊓ Nor T₀ : Subgroup G) ∧ x * x ∈ T₀}
  one_mem' := Set.mem_setOf.mpr ⟨one_mem _, one_mem _, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxN, hxF, hxx⟩ ⟨hyN, hyF, hyy⟩
    refine ⟨mul_mem hxN hyN, mul_mem hxF hyF, ?_⟩
    have h1 : x * (y * x * y⁻¹ * x⁻¹) * x⁻¹ ∈ T₀ :=
      conj_mem_of_mem_nor (Subgroup.mem_inf.mp hxN).2 ((mem_fixMod.mp hyF).2 x hxN)
    have e : x * y * (x * y) = x * (y * x * y⁻¹ * x⁻¹) * x⁻¹ * (x * x) * (y * y) := by group
    rw [e]
    exact mul_mem (mul_mem h1 hxx) hyy
  inv_mem' := by
    rintro x ⟨hxN, hxF, hxx⟩
    refine ⟨inv_mem hxN, inv_mem hxF, ?_⟩
    have e : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
    rw [e]
    exact inv_mem hxx

theorem mem_omegaMod {T T₀ : Subgroup G} {x : G} :
    x ∈ omegaMod T T₀ ↔
      x ∈ T ⊓ Nor T₀ ∧ x ∈ fixMod T₀ (T ⊓ Nor T₀ : Subgroup G) ∧ x * x ∈ T₀ :=
  Iff.rfl

theorem le_omegaMod {T T₀ : Subgroup G} (h : T₀ ≤ T) : T₀ ≤ omegaMod T T₀ := by
  intro t ht
  have htN : t ∈ Nor T₀ := Subgroup.le_normalizer ht
  refine mem_omegaMod.mpr ⟨Subgroup.mem_inf.mpr ⟨h ht, htN⟩, mem_fixMod.mpr ⟨htN, fun y hy => ?_⟩,
    mul_mem ht ht⟩
  have h1 : y * t⁻¹ * y⁻¹ ∈ T₀ := conj_mem_of_mem_nor (Subgroup.mem_inf.mp hy).2 (inv_mem ht)
  have e : t * y * t⁻¹ * y⁻¹ = t * (y * t⁻¹ * y⁻¹) := by group
  rw [e]
  exact mul_mem ht h1

theorem omegaMod_le (T T₀ : Subgroup G) : omegaMod T T₀ ≤ T := fun _ hx =>
  (Subgroup.mem_inf.mp (mem_omegaMod.mp hx).1).1

theorem omegaMod_le_nor (T T₀ : Subgroup G) : omegaMod T T₀ ≤ Nor T₀ := fun _ hx =>
  (Subgroup.mem_inf.mp (mem_omegaMod.mp hx).1).2

theorem omegaMod_comm (T T₀ : Subgroup G) :
    ∀ x ∈ omegaMod T T₀, ∀ y ∈ omegaMod T T₀, x * y * x⁻¹ * y⁻¹ ∈ T₀ := fun _ hx y hy =>
  (mem_fixMod.mp (mem_omegaMod.mp hx).2.1).2 y (mem_omegaMod.mp hy).1

theorem omegaMod_sq (T T₀ : Subgroup G) : ∀ x ∈ omegaMod T T₀, x * x ∈ T₀ := fun _ hx =>
  (mem_omegaMod.mp hx).2.2

theorem conj_mem_omegaMod {T T₀ : Subgroup G} {g x : G} (hgT : g ∈ Nor T) (hgT₀ : g ∈ Nor T₀)
    (hx : x ∈ omegaMod T T₀) : g * x * g⁻¹ ∈ omegaMod T T₀ := by
  obtain ⟨hxN, hxF, hxx⟩ := mem_omegaMod.mp hx
  have hxT := (Subgroup.mem_inf.mp hxN).1
  have hxT₀ := (Subgroup.mem_inf.mp hxN).2
  have hc : g * x * g⁻¹ ∈ Nor T₀ := mul_mem (mul_mem hgT₀ hxT₀) (inv_mem hgT₀)
  refine mem_omegaMod.mpr ⟨Subgroup.mem_inf.mpr ⟨conj_mem_of_mem_nor hgT hxT, hc⟩,
    mem_fixMod.mpr ⟨hc, fun y hy => ?_⟩, ?_⟩
  · have hyT := (Subgroup.mem_inf.mp hy).1
    have hyT₀ := (Subgroup.mem_inf.mp hy).2
    have hy' : g⁻¹ * y * g ∈ T ⊓ Nor T₀ := by
      refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem (inv_mem hgT₀) hyT₀) hgT₀⟩
      have h := conj_mem_of_mem_nor (inv_mem hgT) hyT
      rwa [inv_inv] at h
    have h1 := conj_mem_of_mem_nor hgT₀ ((mem_fixMod.mp hxF).2 _ hy')
    have e : g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ * y⁻¹ =
        g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact h1
  · have e : g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
    rw [e]
    exact conj_mem_of_mem_nor hgT₀ hxx

theorem le_nor_omegaMod {T T₀ J : Subgroup G} (hJT : J ≤ Nor T) (hJT₀ : J ≤ Nor T₀) :
    J ≤ Nor (omegaMod T T₀) := by
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun x =>
    ⟨fun hx => conj_mem_omegaMod (hJT hg) (hJT₀ hg) hx, fun hx => ?_⟩
  have h := conj_mem_omegaMod (hJT (inv_mem hg)) (hJT₀ (inv_mem hg)) hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h

theorem lt_inf_nor [Finite G] {T T₀ : Subgroup G} (hT : IsPGroup 2 T) (hlt : T₀ < T) :
    T₀ < T ⊓ Nor T₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent T := hT.isNilpotent
  have hT₀T : T₀ ≤ T := hlt.le
  have h1 : T₀.subgroupOf T < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => lt_irrefl T₀ (hlt.trans_le (Subgroup.subgroupOf_eq_top.mp h))
  have h2 := Group.normalizerCondition_of_isNilpotent (G := T) _ h1
  rw [← Subgroup.subgroupOf_normalizer_eq hT₀T] at h2
  obtain ⟨y, hy, hny⟩ := SetLike.exists_of_lt h2
  rw [Subgroup.mem_subgroupOf] at hy hny
  exact SetLike.lt_iff_le_and_exists.mpr
    ⟨le_inf hT₀T Subgroup.le_normalizer, (y : G), Subgroup.mem_inf.mpr ⟨y.2, hy⟩, hny⟩

theorem exists_mem_omegaMod [Finite G] {T T₀ : Subgroup G} (hT : IsPGroup 2 T) (hlt : T₀ < T) :
    ∃ x ∈ omegaMod T T₀, x ∉ T₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt' : T₀ < T ⊓ Nor T₀ := lt_inf_nor hT hlt
  set N : Subgroup G := T ⊓ Nor T₀ with hN
  haveI : (T₀.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hlt'.le).mpr inf_le_right
  have hQp : IsPGroup 2 (↥N ⧸ T₀.subgroupOf N) := (hT.to_le inf_le_left).to_quotient _
  obtain ⟨y₀, hy₀N, hy₀⟩ := SetLike.exists_of_lt hlt'
  haveI : Nontrivial (↥N ⧸ T₀.subgroupOf N) := by
    refine ⟨⟨QuotientGroup.mk ⟨y₀, hy₀N⟩, 1, fun h => hy₀ ?_⟩⟩
    rwa [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  have hZp : IsPGroup 2 (Subgroup.center (↥N ⧸ T₀.subgroupOf N)) := hQp.to_subgroup _
  obtain ⟨n, hn, hcard⟩ := hZp.nontrivial_iff_card.mp hQp.center_nontrivial
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (↥N ⧸ T₀.subgroupOf N)) 2
    (by rw [hcard]; exact dvd_pow_self 2 hn.ne')
  have hz2 : (z : ↥N ⧸ T₀.subgroupOf N) ^ 2 = 1 := by
    rw [← hz, ← Subgroup.orderOf_coe]
    exact pow_orderOf_eq_one _
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (z : ↥N ⧸ T₀.subgroupOf N)
  refine ⟨(y : G), mem_omegaMod.mpr ⟨y.2, mem_fixMod.mpr ⟨(Subgroup.mem_inf.mp y.2).2,
    fun w hw => ?_⟩, ?_⟩, fun hyT => ?_⟩
  · have hc : (QuotientGroup.mk (y * ⟨w, hw⟩ * y⁻¹ * (⟨w, hw⟩ : N)⁻¹) :
        ↥N ⧸ T₀.subgroupOf N) = 1 := by
      have hzc := Subgroup.mem_center_iff.mp z.2 (QuotientGroup.mk ⟨w, hw⟩)
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy]
      rw [← hzc]
      group
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hc
    simpa using hc
  · have hc : (QuotientGroup.mk (y * y) : ↥N ⧸ T₀.subgroupOf N) = 1 := by
      rw [QuotientGroup.mk_mul, hy, ← pow_two, hz2]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hc
    simpa using hc
  · have h1 : (QuotientGroup.mk y : ↥N ⧸ T₀.subgroupOf N) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hyT
    rw [hy] at h1
    have hz1 : z = 1 := Subtype.ext h1
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)

theorem mem_of_comm_mem [Finite G] {T T₀ : Subgroup G} (hT : IsPGroup 2 T) (hT₀ : T₀ ≤ T)
    {β : G} (hβ : orderOf β = 3) (hβT₀ : β ∈ Nor T₀) (hC : T ⊓ Cen β ≤ T₀) {x : G} (hx : x ∈ T)
    (hβx : β * x * β⁻¹ * x⁻¹ ∈ T₀) : x ∈ T₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsPGroup 3 (Subgroup.zpowers β) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hβ, pow_one])
  have hle : Subgroup.zpowers β ≤ fixMod T₀ {x} := by
    rw [Subgroup.zpowers_le]
    refine mem_fixMod.mpr ⟨hβT₀, fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hβx
  have hcop : ¬ 3 ∣ Nat.card T₀ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hT.to_le hT₀)
    rw [hn]
    intro h
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  let α : Subgroup.zpowers β →* MulAut G := MulAut.conj.comp (Subgroup.zpowers β).subtype
  obtain ⟨c, hc, hcfix⟩ :=
    (Semidihedral.Principal.coprime_invariant_coset_fixed 3 hA α T₀ hcop x).1 fun a y hy => by
      have ha := mem_fixMod.mp (hle a.2)
      have h1 : (a : G) * (y * x⁻¹) * (a : G)⁻¹ ∈ T₀ := conj_mem_of_mem_nor ha.1 hy
      have h2 : (a : G) * x * (a : G)⁻¹ * x⁻¹ ∈ T₀ := ha.2 x (Set.mem_singleton x)
      show (a : G) * y * (a : G)⁻¹ * x⁻¹ ∈ T₀
      have e : (a : G) * y * (a : G)⁻¹ * x⁻¹ =
          (a : G) * (y * x⁻¹) * (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹ * x⁻¹) := by group
      rw [e]
      exact mul_mem h1 h2
  have hcT : c ∈ T := by
    have e : c = c * x⁻¹ * x := by group
    rw [e]
    exact mul_mem (hT₀ hc) hx
  have hcβ : c ∈ Cen β := by
    have h' : β * c * β⁻¹ = c := hcfix ⟨β, Subgroup.mem_zpowers β⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact mul_inv_eq_iff_eq_mul.mp h'
  have hcT₀ : c ∈ T₀ := hC (Subgroup.mem_inf.mpr ⟨hcT, hcβ⟩)
  have e : x = (c * x⁻¹)⁻¹ * c := by group
  rw [e]
  exact mul_mem (inv_mem hc) hcT₀

theorem ff79_1_6_holds : FF79_1_6 := by
  intro G _ _ J T T₀ hJ hT hJT hT₀T hJT₀ β hβJ hβ hC
  classical
  by_contra hne
  have hlt : T₀ < T := lt_of_le_of_ne hT₀T hne
  obtain ⟨x₀, hx₀E, hx₀⟩ := exists_mem_omegaMod hT hlt
  have hJE : J ≤ Nor (omegaMod T T₀) := le_nor_omegaMod hJT hJT₀
  have hfix : ∀ x ∈ omegaMod T T₀, β * x * β⁻¹ * x⁻¹ ∈ T₀ → x ∈ T₀ := fun x hx hβx =>
    mem_of_comm_mem hT hT₀T hβ (hJT₀ hβJ) hC (omegaMod_le T T₀ hx) hβx
  obtain ⟨e⟩ := GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two (X := J) (n := 5) hJ
  let f : GL (Fin 5) (ZMod 2) →* G := J.subtype.comp e.symm.toMonoidHom
  have hfinj : Function.Injective f := J.subtype_injective.comp e.symm.injective
  have hfJ : ∀ g, f g ∈ J := fun g => (e.symm g).2
  have hfβ : f (e ⟨β, hβJ⟩) = β := by
    show ((e.symm (e ⟨β, hβJ⟩) : J) : G) = β
    rw [MulEquiv.symm_apply_apply]
  have hβ' : orderOf (e ⟨β, hβJ⟩) = 3 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hβ]
  obtain ⟨d', hd'1, hd'7, k, hk, hrel'⟩ := GroupTheory.GL52.exists_frob73 hβ'
  have hd1 : f d' ≠ 1 := fun h => hd'1 (hfinj (h.trans (map_one f).symm))
  have hd7 : f d' ^ 7 = 1 := by rw [← map_pow, hd'7, map_one]
  have hrel : β * f d' * β⁻¹ = f d' ^ k := by
    rw [← hfβ, ← map_inv, ← map_mul, ← map_mul, ← map_pow, hrel']
  have hβ3 : β ^ 3 = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
  have hdE : ∀ x ∈ omegaMod T T₀, f d' * x * (f d')⁻¹ * x⁻¹ ∈ T₀ :=
    frob73_mod (le_omegaMod hT₀T) (omegaMod_le_nor T T₀) (omegaMod_comm T T₀) (omegaMod_sq T T₀)
      (hJE (hfJ d')) (hJT₀ (hfJ d')) (hJE hβJ) (hJT₀ hβJ) hd7 hβ3 hk hrel hfix
  let K : Subgroup J := (fixMod T₀ (omegaMod T T₀ : Set G)).subgroupOf J
  haveI hKn : K.Normal := by
    refine ⟨fun a ha n => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨haN, haE⟩ := mem_fixMod.mp ha
    have hn : (n : G) ∈ J := n.2
    have hc : (n : G) * a * (n : G)⁻¹ ∈ Nor T₀ :=
      mul_mem (mul_mem (hJT₀ hn) haN) (inv_mem (hJT₀ hn))
    refine mem_fixMod.mpr ⟨by push_cast; exact hc, fun x hx => ?_⟩
    have hx' : (n : G)⁻¹ * x * (n : G) ∈ omegaMod T T₀ := by
      have h := conj_mem_of_mem_nor (hJE (inv_mem hn)) hx
      rwa [inv_inv] at h
    have h1 := conj_mem_of_mem_nor (hJT₀ hn) (haE _ hx')
    have e : ((n * a * n⁻¹ : J) : G) * x * ((n * a * n⁻¹ : J) : G)⁻¹ * x⁻¹ =
        (n : G) * ((a : G) * ((n : G)⁻¹ * x * (n : G)) * (a : G)⁻¹ *
          ((n : G)⁻¹ * x * (n : G))⁻¹) * (n : G)⁻¹ := by
      push_cast
      group
    rw [e]
    exact h1
  haveI := GroupTheory.GL52.isSimpleGroup_G52
  haveI : IsSimpleGroup J := e.isSimpleGroup
  have hdK : (⟨f d', hfJ d'⟩ : J) ∈ K := by
    rw [Subgroup.mem_subgroupOf]
    exact mem_fixMod.mpr ⟨hJT₀ (hfJ d'), hdE⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · rw [h, Subgroup.mem_bot] at hdK
    exact hd1 (congrArg Subtype.val hdK)
  · have hβK : (⟨β, hβJ⟩ : J) ∈ K := by
      rw [h]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at hβK
    exact hx₀ (hfix x₀ hx₀E ((mem_fixMod.mp hβK).2 x₀ hx₀E))

end CFSG.RankThree.PartTwo.Sec21.FF79
