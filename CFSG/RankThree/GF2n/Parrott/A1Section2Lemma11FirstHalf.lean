module

public import CFSG.RankThree.GF2n.Parrott.A1Section2J0Normal
public import CFSG.RankThree.GF2n.Parrott.Parrott77Prop7
public import CFSG.GroupTheory.CentralizerSylowFusion
import CFSG.RankThree.GF2n.Parrott.A1Section2CJ
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2U42
import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.GroupTheory.ExtraspecialElementaryAbelianBound

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem conj_eq_of_mem_zpowers_z {x y : G} (hx : x ∈ H z) (hy : y ∈ Subgroup.zpowers z) :
    x * y * x⁻¹ = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hc : Commute x z := Subgroup.mem_centralizer_singleton_iff.mp hx
  rw [(hc.zpow_right k).eq, mul_inv_cancel_right]

omit [Finite G] in
private theorem commutatorElement_mul_left' (x y w : G) :
    ⁅x * y, w⁆ = x * ⁅y, w⁆ * x⁻¹ * ⁅x, w⁆ := by
  simp only [commutatorElement_def]
  group

omit [Finite G] in
private theorem commutatorElement_mul_right' (k a b : G) :
    ⁅k, a * b⁆ = ⁅k, a⁆ * (a * ⁅k, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]
  group

private structure CaseIData (z : G) (σ : G) (J₀ J₁ : Subgroup G) : Prop where
  hyp : Tim79a.ParrottHypA1 z
  σ_mem : σ ∈ H z
  σ_order : orderOf σ = 3
  σ_not_mem : σ ∉ J z
  J₀_eq : J₀ = CJ z σ
  sup : J₀ ⊔ J₁ = J z
  inf : J₀ ⊓ J₁ = Subgroup.zpowers z
  comm : ∀ a ∈ J₀, ∀ b ∈ J₁, a * b = b * a
  card₀ : Nat.card J₀ = 8
  normal₀ : H z ≤ Subgroup.normalizer (J₀ : Set G)

namespace CaseIData

variable {σ : G} {J₀ J₁ : Subgroup G}

private theorem orderOf_z (d : CaseIData z σ J₀ J₁) : orderOf z = 2 := orderOf_z_A1 d.hyp

private theorem J₀_le (d : CaseIData z σ J₀ J₁) : J₀ ≤ J z := d.sup ▸ le_sup_left

private theorem J₁_le (d : CaseIData z σ J₀ J₁) : J₁ ≤ J z := d.sup ▸ le_sup_right

private theorem zpowers_le₁ (d : CaseIData z σ J₀ J₁) : Subgroup.zpowers z ≤ J₁ :=
  d.inf ▸ inf_le_right

private theorem z_mem₁ (d : CaseIData z σ J₀ J₁) : z ∈ J₁ := d.zpowers_le₁ (Subgroup.mem_zpowers z)

private theorem comm_mem_zpowers (d : CaseIData z σ J₀ J₁) {x y : G} (hx : x ∈ J z) (hy : y ∈ J z) :
    ⁅x, y⁆ ∈ Subgroup.zpowers z := by
  rw [← d.hyp.commutator]
  exact Subgroup.commutator_mem_commutator hx hy

private theorem comm_eq_z (d : CaseIData z σ J₀ J₁) {x y : G} (hx : x ∈ J z) (hy : y ∈ J z)
    (hne : x * y ≠ y * x) : ⁅x, y⁆ = z := by
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two d.orderOf_z).mp
    (d.comm_mem_zpowers hx hy) with h1 | h1
  · exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h1) hne
  · exact h1

private theorem decomp (d : CaseIData z σ J₀ J₁) {x : G} (hx : x ∈ J z) :
    ∃ a ∈ J₀, ∃ b ∈ J₁, a * b = x := by
  rw [← d.sup] at hx
  exact (CFSG.mem_sup_of_commute fun a ha b hb => d.comm a ha b hb).mp hx

private theorem mem_zpowers_of_commute (d : CaseIData z σ J₀ J₁) {x : G} (hx : x ∈ J z)
    (hc : ∀ y ∈ J z, y * x = x * y) : x ∈ Subgroup.zpowers z := by
  rw [← centerIn_J_eq_zpowers_A1 d.hyp]
  exact Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_iff.mpr hc⟩

private theorem mem_zpowers_of_commute₀₁ (d : CaseIData z σ J₀ J₁) {x : G} (hx : x ∈ J z)
    (h₀ : ∀ a ∈ J₀, a * x = x * a) (h₁ : ∀ b ∈ J₁, b * x = x * b) : x ∈ Subgroup.zpowers z := by
  refine d.mem_zpowers_of_commute hx fun y hy => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := d.decomp hy
  rw [mul_assoc, h₁ b hb, ← mul_assoc, h₀ a ha, mul_assoc]

private theorem eq_inf_centralizer (d : CaseIData z σ J₀ J₁) :
    J₁ = J z ⊓ Subgroup.centralizer (J₀ : Set G) := by
  apply le_antisymm
  · intro b hb
    exact Subgroup.mem_inf.mpr ⟨d.J₁_le hb, Subgroup.mem_centralizer_iff.mpr fun a ha =>
      d.comm a ha b hb⟩
  · intro x hx
    obtain ⟨hxJ, hxc⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := d.decomp hxJ
    have haz : a ∈ Subgroup.zpowers z := by
      refine d.mem_zpowers_of_commute₀₁ (d.J₀_le ha) (fun a' ha' => ?_) (fun b' hb' => ?_)
      · have h1 := Subgroup.mem_centralizer_iff.mp hxc a' ha'
        have h2 := d.comm a' ha' b hb
        calc a' * a = a' * (a * b) * b⁻¹ := by group
          _ = a * b * a' * b⁻¹ := by rw [h1]
          _ = a * (b * a') * b⁻¹ := by group
          _ = a * (a' * b) * b⁻¹ := by rw [h2]
          _ = a * a' := by group
      · exact (d.comm a ha b' hb').symm
    exact J₁.mul_mem (d.zpowers_le₁ haz) hb

private theorem card₁ (d : CaseIData z σ J₀ J₁) : Nat.card J₁ = 128 := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute J₀ J₁ d.comm).1
  rw [d.sup, d.inf, card_J_A1 d.hyp, Nat.card_zpowers, d.orderOf_z, d.card₀] at h
  omega

private theorem conj_mem₁ (d : CaseIData z σ J₀ J₁) {g x : G} (hg : g ∈ H z) (hx : x ∈ J₁) :
    g * x * g⁻¹ ∈ J₁ := by
  rw [d.eq_inf_centralizer] at hx ⊢
  obtain ⟨hxJ, hxc⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (J_le_normalizer_A hg) x).mp hxJ,
    Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
  have ha' : g⁻¹ * a * g ∈ J₀ := by
    have := (Subgroup.mem_normalizer_iff.mp (d.normal₀ ((H z).inv_mem hg)) a).mp ha
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hxc _ ha'
  calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * a := by group

private theorem normal₁ (d : CaseIData z σ J₀ J₁) : H z ≤ Subgroup.normalizer (J₁ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact d.conj_mem₁ hg
  · intro hx
    have := d.conj_mem₁ ((H z).inv_mem hg) hx
    simpa [mul_assoc] using this

private theorem exists_comm_eq_z₀ (d : CaseIData z σ J₀ J₁) {j : G} (hj : j ∈ J z) (hj1 : j ∉ J₁) :
    ∃ a ∈ J₀, ⁅a, j⁆ = z := by
  have hnc : ¬ ∀ a ∈ J₀, a * j = j * a := fun hc =>
    hj1 (d.eq_inf_centralizer ▸ Subgroup.mem_inf.mpr ⟨hj, Subgroup.mem_centralizer_iff.mpr hc⟩)
  push Not at hnc
  obtain ⟨a, ha, hne⟩ := hnc
  exact ⟨a, ha, d.comm_eq_z (d.J₀_le ha) hj hne⟩

private theorem exists_comm_eq_z₁ (d : CaseIData z σ J₀ J₁) {x : G} (hx : x ∈ J₁)
    (hxz : x ∉ Subgroup.zpowers z) : ∃ e ∈ J₁, ⁅e, x⁆ = z := by
  have hnc : ¬ ∀ b ∈ J₁, b * x = x * b := fun hc =>
    hxz (d.mem_zpowers_of_commute₀₁ (d.J₁_le hx) (fun a ha => d.comm a ha x hx) hc)
  push Not at hnc
  obtain ⟨b, hb, hne⟩ := hnc
  exact ⟨b, hb, d.comm_eq_z (d.J₁_le hb) (d.J₁_le hx) hne⟩

private theorem commute_of_comm_mem_zpowers (d : CaseIData z σ J₀ J₁) {s b : G} (hs : s ∈ H z)
    (hs3 : orderOf s = 3) (hb : ⁅s, b⁆ ∈ Subgroup.zpowers z) : s * b = b * s := by
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two d.orderOf_z).mp hb with h1 | h1
  · exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · exfalso
    have hz2 : z * z = 1 := by
      rw [← pow_two, ← d.orderOf_z]
      exact pow_orderOf_eq_one z
    have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp hs
    have e1 : s * b * s⁻¹ = z * b := by
      rw [← h1, commutatorElement_def]
      group
    have e2 : s * (z * b) * s⁻¹ = b := by
      calc s * (z * b) * s⁻¹ = (s * z) * b * s⁻¹ := by group
        _ = z * (s * b * s⁻¹) := by rw [hsz]; group
        _ = b := by rw [e1, ← mul_assoc, hz2, one_mul]
    have hs3' : s ^ 3 = 1 := by
      rw [← hs3]
      exact pow_orderOf_eq_one s
    have e3 : s * (s * s) * b * (s * (s * s))⁻¹ = z * b := by
      calc s * (s * s) * b * (s * (s * s))⁻¹ = s * (s * (s * b * s⁻¹) * s⁻¹) * s⁻¹ := by group
        _ = z * b := by rw [e1, e2, e1]
    rw [← pow_three, hs3', one_mul, inv_one, mul_one] at e3
    have hz1 : z = 1 := by
      calc z = z * b * b⁻¹ := by group
        _ = 1 := by rw [← e3, mul_inv_cancel]
    have hz := d.orderOf_z
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)

end CaseIData

private def centKer (z : G) (X : Subgroup G) : Subgroup ↥(H z) where
  carrier := {k | ∀ x ∈ X, ⁅(k : G), x⁆ ∈ Subgroup.zpowers z}
  one_mem' := fun x _ => by simp
  mul_mem' := by
    intro a b ha hb x hx
    change ⁅(a : G) * b, x⁆ ∈ Subgroup.zpowers z
    rw [commutatorElement_mul_left', conj_eq_of_mem_zpowers_z a.2 (hb x hx)]
    exact Subgroup.mul_mem _ (hb x hx) (ha x hx)
  inv_mem' := by
    intro a ha x hx
    change ⁅(a : G)⁻¹, x⁆ ∈ Subgroup.zpowers z
    have e : ⁅(a : G)⁻¹, x⁆ = (a : G)⁻¹ * ⁅(a : G), x⁆⁻¹ * ((a : G)⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, conj_eq_of_mem_zpowers_z ((H z).inv_mem a.2) (Subgroup.inv_mem _ (ha x hx))]
    exact Subgroup.inv_mem _ (ha x hx)

omit [Finite G] in
private theorem mem_centKer {X : Subgroup G} {k : ↥(H z)} :
    k ∈ centKer z X ↔ ∀ x ∈ X, ⁅(k : G), x⁆ ∈ Subgroup.zpowers z := Iff.rfl

omit [Finite G] in
private theorem centKer_normal {X : Subgroup G} (hX : H z ≤ Subgroup.normalizer (X : Set G)) :
    (centKer z X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_centKer] at hn ⊢
  intro x hx
  have hx' : (g : G)⁻¹ * x * g ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (hX ((H z).inv_mem g.2)) x).mp hx
    simpa using this
  have e : ⁅((g * n * g⁻¹ : ↥(H z)) : G), x⁆ =
      (g : G) * ⁅(n : G), (g : G)⁻¹ * x * g⁆ * (g : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [e, conj_eq_of_mem_zpowers_z g.2 (hn _ hx')]
  exact hn _ hx'

private theorem J_le_centKer (h : Tim79a.ParrottHypA1 z) {X : Subgroup G} (hXJ : X ≤ J z) :
    (J z).subgroupOf (H z) ≤ centKer z X := by
  intro k hk x hx
  rw [← h.commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hk) (hXJ hx)

omit [Finite G] in
private theorem eq_top_or_le_J_of_normal
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)
    (N : Subgroup ↥(H z)) [hNn : N.Normal] (hJN : (J z).subgroupOf (H z) ≤ N) :
    N = ⊤ ∨ N ≤ (J z).subgroupOf (H z) := by
  have := CFSG.HardMathSupport.Dickson.I271.isSimpleGroup_QP45
  have hmapN : (N.map (qHP D)).Normal := Subgroup.Normal.map hNn (qHP D) (qHP_surjective D)
  rcases hmapN.eq_bot_or_eq_top with hbot | htop
  · right
    rw [← ker_qHP D]
    exact (Subgroup.map_eq_bot_iff _).mp hbot
  · left
    have hker : (qHP D).ker ≤ N := by rw [ker_qHP D]; exact hJN
    rw [← Subgroup.comap_map_eq_self hker, htop, Subgroup.comap_top]

namespace CaseIData

variable {σ : G} {J₀ J₁ : Subgroup G}

private theorem comm_mem_zpowers₀
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)
    (d : CaseIData z σ J₀ J₁) {k : G} (hk : k ∈ H z) {a : G} (ha : a ∈ J₀) :
    ⁅k, a⁆ ∈ Subgroup.zpowers z := by
  have := centKer_normal d.normal₀
  have hσ : (⟨σ, d.σ_mem⟩ : ↥(H z)) ∈ centKer z J₀ := by
    intro a ha
    have hc : a ∈ CJ z σ := d.J₀_eq ▸ ha
    have : σ * a = a * σ := (Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hc).1).symm
    rw [commutatorElement_eq_one_iff_mul_comm.mpr this]
    exact Subgroup.one_mem _
  rcases eq_top_or_le_J_of_normal D (centKer z J₀) (J_le_centKer d.hyp d.J₀_le) with htop | hle
  · have hk' : (⟨k, hk⟩ : ↥(H z)) ∈ centKer z J₀ := htop ▸ Subgroup.mem_top _
    exact hk' a ha
  · exact absurd (Subgroup.mem_subgroupOf.mp (hle hσ)) d.σ_not_mem

private theorem exists_comm_not_mem_zpowers₁
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)
    (d : CaseIData z σ J₀ J₁) {k : G} (hk : k ∈ H z) (hkJ : k ∉ J z) :
    ∃ b ∈ J₁, ⁅k, b⁆ ∉ Subgroup.zpowers z := by
  have := centKer_normal d.normal₁
  rcases eq_top_or_le_J_of_normal D (centKer z J₁) (J_le_centKer d.hyp d.J₁_le) with htop | hle
  · exfalso
    have hσ : (⟨σ, d.σ_mem⟩ : ↥(H z)) ∈ centKer z J₁ := htop ▸ Subgroup.mem_top _
    have hJ₁J₀ : J₁ ≤ J₀ := by
      intro b hb
      have hc := d.commute_of_comm_mem_zpowers d.σ_mem d.σ_order (hσ b hb)
      rw [d.J₀_eq]
      exact mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hc.symm, d.J₁_le hb⟩
    have hle₂ : J₁ ≤ Subgroup.zpowers z := d.inf ▸ le_inf hJ₁J₀ le_rfl
    have hcard := Subgroup.card_le_of_le hle₂
    rw [d.card₁, Nat.card_zpowers, d.orderOf_z] at hcard
    omega
  · by_contra hall
    push Not at hall
    exact hkJ (Subgroup.mem_subgroupOf.mp (hle (show (⟨k, hk⟩ : ↥(H z)) ∈ centKer z J₁ from
      fun b hb => hall b hb)))

private theorem derived_inf_J_le
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)
    (d : CaseIData z σ J₀ J₁) : ⁅H z, ⁅H z, H z⁆⁆ ⊓ J z ≤ J₁ := by
  have hHJ₀ : ⁅H z, J₀⁆ ≤ Subgroup.zpowers z :=
    Subgroup.commutator_le.mpr fun k hk a ha => d.comm_mem_zpowers₀ D hk ha
  have hzH : ⁅Subgroup.zpowers z, H z⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.zpowers_le.mpr z_centralizes_H_A
  have h1 : ⁅⁅H z, J₀⁆, H z⁆ = ⊥ :=
    eq_bot_iff.mpr (hzH ▸ Subgroup.commutator_mono hHJ₀ le_rfl)
  have h2 : ⁅⁅J₀, H z⁆, H z⁆ = ⊥ := by
    rw [Subgroup.commutator_comm J₀ (H z)]
    exact h1
  have h3 : ⁅⁅H z, H z⁆, J₀⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have h4 : ⁅H z, H z⁆ ≤ Subgroup.centralizer (J₀ : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h3
  have h5 : ⁅H z, ⁅H z, H z⁆⁆ ≤ ⁅H z, H z⁆ :=
    Subgroup.commutator_mono le_rfl (Subgroup.commutator_le_self (H z))
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  rw [d.eq_inf_centralizer]
  exact Subgroup.mem_inf.mpr ⟨hx2, h4 (h5 hx1)⟩

end CaseIData

omit [Finite G] in
private theorem relIndex_inf_centralizer_le_ncard {K : Subgroup G} {x : G} {T : Set G}
    (hT : T.Finite) (hKT : ∀ k ∈ K, k * x * k⁻¹ ∈ T) :
    (K ⊓ Subgroup.centralizer ({x} : Set G)).relIndex K ≤ T.ncard := by
  have : Finite T := hT.to_subtype
  set C : Subgroup ↥K := (K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K with hC
  have key : ∀ a b : ↥K,
      (a : G) * x * (a : G)⁻¹ = (b : G) * x * (b : G)⁻¹ ↔ a⁻¹ * b ∈ C := by
    intro a b
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro hab
      refine ⟨K.mul_mem (K.inv_mem a.2) b.2, ?_⟩
      calc (a : G)⁻¹ * b * x = (a : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * b := by group
        _ = (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * b := by rw [hab]
        _ = x * ((a : G)⁻¹ * b) := by group
    · rintro ⟨-, hc⟩
      calc (a : G) * x * (a : G)⁻¹ = (a : G) * (x * ((a : G)⁻¹ * b)) * (b : G)⁻¹ := by group
        _ = (a : G) * ((a : G)⁻¹ * b * x) * (b : G)⁻¹ := by rw [hc]
        _ = (b : G) * x * (b : G)⁻¹ := by group
  let f : ↥K ⧸ C → T := fun q => Quotient.liftOn' q
    (fun k => (⟨(k : G) * x * (k : G)⁻¹, hKT k k.2⟩ : T))
    (fun a b hab => Subtype.ext ((key a b).mpr (QuotientGroup.leftRel_apply.mp hab)))
  have hf : Function.Injective f := by
    intro q₁ q₂ hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q₂
    exact QuotientGroup.eq.mpr ((key a b).mp (congrArg Subtype.val hq))
  calc (K ⊓ Subgroup.centralizer ({x} : Set G)).relIndex K = Nat.card (↥K ⧸ C) := rfl
    _ ≤ Nat.card T := Nat.card_le_card_of_injective f hf
    _ = T.ncard := Nat.card_coe_set_eq T

private theorem card_H_A1 (h : Tim79a.ParrottHypA1 z) :
    Nat.card (H z) = 2 ^ 15 * 405 := by
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup ((J z).subgroupOf (H z))
  rw [Nat.card_congr (QuotientDataPSp.toQP45 (quotientDataA1 h)).toEquiv,
    CFSG.HardMathSupport.Dickson.I271.card_QP45_eq,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (J_le_H (z := z))).toEquiv, card_J_A1 h] at hq
  rw [hq]
  norm_num

private theorem two_pow_nine_le_card_sylow
    (h : Tim79a.ParrottHypA1 z) {j : G} {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ Subgroup.centralizer ({j} : Set G)))
    (hidx : (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) ≤ 127) :
    2 ^ 9 ≤ Nat.card K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := H z ⊓ Subgroup.centralizer ({j} : Set G) with hCdef
  have hmul : C.relIndex (H z) * Nat.card C = 2 ^ 15 * 405 := by
    have := Subgroup.relIndex_mul_card C (H z)
    rw [inf_eq_left.mpr (inf_le_left : C ≤ H z), card_H_A1 h] at this
    exact this
  have hn0 : C.relIndex (H z) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    norm_num at hmul
  have hm0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hfac := congrArg (fun n => n.factorization 2) hmul
  rw [Nat.factorization_mul hn0 hm0] at hfac
  have h405 : (2 ^ 15 * 405 : ℕ).factorization 2 = 15 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 405)]
  rw [h405] at hfac
  simp only [Finsupp.coe_add, Pi.add_apply] at hfac
  have hn6 : (C.relIndex (H z)).factorization 2 ≤ 6 := by
    by_contra hlt
    push Not at hlt
    have h1 : 2 ^ 7 ≤ 2 ^ (C.relIndex (H z)).factorization 2 :=
      Nat.pow_le_pow_right (by norm_num) hlt
    have h2 := Nat.ordProj_le 2 hn0
    have h3 : (2 : ℕ) ^ 7 = 128 := by norm_num
    omega
  rw [hK.card_eq]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem card_inf_centralizer_le (h : Tim79a.ParrottHypA1 z) {j : G}
    (hjc : ¬ J z ≤ Subgroup.centralizer ({j} : Set G)) :
    Nat.card (J z ⊓ Subgroup.centralizer ({j} : Set G) : Subgroup G) ≤ 2 ^ 8 := by
  have hdvd : Nat.card (J z ⊓ Subgroup.centralizer ({j} : Set G) : Subgroup G) ∣ 2 ^ 9 :=
    card_J_A1 h ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk9, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk8 : k ≠ 9 := by
    rintro rfl
    apply hjc
    have heq : J z ⊓ Subgroup.centralizer ({j} : Set G) = J z :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, card_J_A1 h])
    rw [← heq]
    exact inf_le_right
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

namespace CaseIData

variable {σ : G} {J₀ J₁ : Subgroup G}

private theorem not_le_centralizer (d : CaseIData z σ J₀ J₁) {j : G} (hj : j ∈ J z)
    (hj1 : j ∉ J₁) : ¬ J z ≤ Subgroup.centralizer ({j} : Set G) := by
  intro hle
  obtain ⟨a, ha, haj⟩ := d.exists_comm_eq_z₀ hj hj1
  have hc : a * j = j * a := Subgroup.mem_centralizer_singleton_iff.mp (hle (d.J₀_le ha))
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hc] at haj
  have hz := d.orderOf_z
  rw [← haj, orderOf_one] at hz
  exact absurd hz (by norm_num)

private theorem relIndex_le
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)
    (d : CaseIData z σ J₀ J₁) {j : G} (hj : j ∈ J z) :
    (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) ≤ 127 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := d.decomp hj
  have hex : ∃ e ∈ J₁, (e ∈ Subgroup.zpowers z ↔ b ∉ Subgroup.zpowers z) := by
    by_cases hbz : b ∈ Subgroup.zpowers z
    · have hnle : ¬ (J₁ : Set G) ⊆ Subgroup.zpowers z := by
        intro hle
        have hc := Subgroup.card_le_of_le (show J₁ ≤ Subgroup.zpowers z from hle)
        rw [d.card₁, Nat.card_zpowers, d.orderOf_z] at hc
        omega
      obtain ⟨e, he, hez⟩ := Set.not_subset.mp hnle
      exact ⟨e, he, fun h => absurd h hez, fun h => absurd hbz h⟩
    · exact ⟨1, J₁.one_mem, fun _ => hbz, fun _ => Subgroup.one_mem _⟩
  obtain ⟨e, he, hebz⟩ := hex
  set T : Set G := (fun y => a * y) '' ((J₁ : Set G) \ {e}) with hT
  have hmem : ∀ k ∈ H z, k * (a * b) * k⁻¹ ∈ T := by
    intro k hk
    have hka := d.comm_mem_zpowers₀ D hk ha
    have hyJ₁ : ⁅k, a⁆ * (k * b * k⁻¹) ∈ J₁ := J₁.mul_mem (d.zpowers_le₁ hka) (d.conj_mem₁ hk hb)
    have hyz : ⁅k, a⁆ * (k * b * k⁻¹) ∈ Subgroup.zpowers z ↔ b ∈ Subgroup.zpowers z := by
      constructor
      · intro hy
        have h1 : k * b * k⁻¹ ∈ Subgroup.zpowers z := by
          have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hka) hy
          rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
        have h2 := conj_eq_of_mem_zpowers_z ((H z).inv_mem hk) h1
        rw [show k⁻¹ * (k * b * k⁻¹) * k⁻¹⁻¹ = b by group] at h2
        rw [h2]
        exact h1
      · intro hbz
        rw [conj_eq_of_mem_zpowers_z hk hbz]
        exact Subgroup.mul_mem _ hka hbz
    have hye : ⁅k, a⁆ * (k * b * k⁻¹) ≠ e := by
      intro hye
      rw [hye] at hyz
      exact iff_not_self (hyz.symm.trans hebz)
    refine ⟨⁅k, a⁆ * (k * b * k⁻¹), ⟨hyJ₁, hye⟩, ?_⟩
    have hc : a * ⁅k, a⁆ * a⁻¹ = ⁅k, a⁆ :=
      conj_eq_of_mem_zpowers_z (J_le_H (d.J₀_le ha)) hka
    calc a * (⁅k, a⁆ * (k * b * k⁻¹)) = (a * ⁅k, a⁆ * a⁻¹) * a * (k * b * k⁻¹) := by group
      _ = ⁅k, a⁆ * a * (k * b * k⁻¹) := by rw [hc]
      _ = k * (a * b) * k⁻¹ := by rw [commutatorElement_def]; group
  have hJ₁card : (J₁ : Set G).ncard = 128 := by
    rw [← Nat.card_coe_set_eq]
    exact d.card₁
  calc (H z ⊓ Subgroup.centralizer ({a * b} : Set G)).relIndex (H z) ≤ T.ncard :=
        relIndex_inf_centralizer_le_ncard (Set.toFinite T) hmem
    _ ≤ ((J₁ : Set G) \ {e}).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = 127 := by rw [Set.ncard_diff_singleton_of_mem he, hJ₁card]

private theorem exists_mem_sylow_not_mem_J
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)
    (d : CaseIData z σ J₀ J₁) {j : G} (hj : j ∈ J z) (hj1 : j ∉ J₁) {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ Subgroup.centralizer ({j} : Set G))) :
    ∃ k ∈ K, k ∉ J z := by
  by_contra hall
  push Not at hall
  have hKJ : K ≤ J z ⊓ Subgroup.centralizer ({j} : Set G) := fun k hk =>
    Subgroup.mem_inf.mpr ⟨hall k hk, (Subgroup.mem_inf.mp (hK.le hk)).2⟩
  have h1 := Subgroup.card_le_of_le hKJ
  have h9 := two_pow_nine_le_card_sylow d.hyp hK (d.relIndex_le D hj)
  have h8 := card_inf_centralizer_le d.hyp (d.not_le_centralizer hj hj1)
  have e9 : (2 : ℕ) ^ 9 = 512 := by norm_num
  have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  omega

private theorem commute_or_commute_mul (d : CaseIData z σ J₀ J₁) {a j x : G} (ha : a ∈ J₀)
    (haj : ⁅a, j⁆ = z) (hj : j ∈ J z) (hx : x ∈ J z) :
    x ∈ Subgroup.centralizer ({j} : Set G) ∨ a * x ∈ Subgroup.centralizer ({j} : Set G) := by
  by_cases hxj : x * j = j * x
  · exact Or.inl (Subgroup.mem_centralizer_singleton_iff.mpr hxj)
  · right
    have hxz := d.comm_eq_z hx hj hxj
    have hz2 : z * z = 1 := by
      rw [← pow_two, ← d.orderOf_z]
      exact pow_orderOf_eq_one z
    have hc : ⁅a * x, j⁆ = 1 := by
      rw [commutatorElement_mul_left', hxz,
        conj_eq_of_mem_zpowers_z (J_le_H (d.J₀_le ha)) (Subgroup.mem_zpowers z), haj, hz2]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hc)

private theorem z_mem_secondDerived
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)
    (d : CaseIData z σ J₀ J₁) {j : G} (hj : j ∈ J z) (hj1 : j ∉ J₁) {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ Subgroup.centralizer ({j} : Set G))) :
    z ∈ ⁅K, ⁅K, K⁆⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJp : IsPGroup 2 (J z) := IsPGroup.of_card (n := 9) (card_J_A1 d.hyp)
  have hCJK : J z ⊓ Subgroup.centralizer ({j} : Set G) ≤ K := by
    refine CFSG.GroupTheory.le_isSylowOf_of_isPGroup_of_le_normalizer hK
      (inf_le_inf_right _ J_le_H) ?_ (hJp.to_le inf_le_left)
    intro g hg
    obtain ⟨hgH, hgj⟩ := Subgroup.mem_inf.mp hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hJ := Subgroup.mem_normalizer_iff.mp (J_le_normalizer_A hgH) x
    have hC := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hgj) x
    simp only [Subgroup.mem_inf]
    exact and_congr hJ hC
  obtain ⟨k, hkK, hkJ⟩ := d.exists_mem_sylow_not_mem_J D hj hj1 hK
  obtain ⟨hkH, hkj⟩ := Subgroup.mem_inf.mp (hK.le hkK)
  obtain ⟨a, ha, haj⟩ := d.exists_comm_eq_z₀ hj hj1
  have haJ : a ∈ J z := d.J₀_le ha
  obtain ⟨b, hb, hkb⟩ := d.exists_comm_not_mem_zpowers₁ D hkH hkJ
  have hkbJ₁ : ⁅k, b⁆ ∈ J₁ := by
    rw [commutatorElement_def]
    exact J₁.mul_mem (d.conj_mem₁ hkH hb) (J₁.inv_mem hb)
  obtain ⟨c, hcC, hcJ₁, hcz⟩ : ∃ c ∈ J z ⊓ Subgroup.centralizer ({j} : Set G),
      ⁅k, c⁆ ∈ J₁ ∧ ⁅k, c⁆ ∉ Subgroup.zpowers z := by
    rcases d.commute_or_commute_mul ha haj hj (d.J₁_le hb) with hbj | habj
    · exact ⟨b, Subgroup.mem_inf.mpr ⟨d.J₁_le hb, hbj⟩, hkbJ₁, hkb⟩
    · have hka := d.comm_mem_zpowers₀ D hkH ha
      have hca : a * ⁅k, b⁆ * a⁻¹ = ⁅k, b⁆ := by
        rw [d.comm a ha _ hkbJ₁, mul_inv_cancel_right]
      refine ⟨a * b, Subgroup.mem_inf.mpr ⟨(J z).mul_mem haJ (d.J₁_le hb), habj⟩, ?_, ?_⟩
      · rw [commutatorElement_mul_right', hca]
        exact J₁.mul_mem (d.zpowers_le₁ hka) hkbJ₁
      · rw [commutatorElement_mul_right', hca]
        intro hmem
        apply hkb
        have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hka) hmem
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  obtain ⟨e₁, he₁, he₁d⟩ := d.exists_comm_eq_z₁ hcJ₁ hcz
  obtain ⟨e, heC, hed⟩ : ∃ e ∈ J z ⊓ Subgroup.centralizer ({j} : Set G), ⁅e, ⁅k, c⁆⁆ = z := by
    rcases d.commute_or_commute_mul ha haj hj (d.J₁_le he₁) with he₁j | hae₁j
    · exact ⟨e₁, Subgroup.mem_inf.mpr ⟨d.J₁_le he₁, he₁j⟩, he₁d⟩
    · refine ⟨a * e₁, Subgroup.mem_inf.mpr ⟨(J z).mul_mem haJ (d.J₁_le he₁), hae₁j⟩, ?_⟩
      have had : ⁅a, ⁅k, c⁆⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (d.comm a ha _ hcJ₁)
      rw [commutatorElement_mul_left', he₁d,
        conj_eq_of_mem_zpowers_z (J_le_H haJ) (Subgroup.mem_zpowers z), had, mul_one]
  rw [← hed]
  exact Subgroup.commutator_mem_commutator (hCJK heC)
    (Subgroup.commutator_mem_commutator hkK (hCJK hcC))

private theorem no_conj_z_eq
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)
    (d : CaseIData z σ J₀ J₁) {j : G} (hj : j ∈ J z) (hj2 : orderOf j = 2) (hj1 : j ∉ J₁) :
    ∀ g : G, g * z * g⁻¹ ≠ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := exists_isSylowOf 2 (H z ⊓ Subgroup.centralizer ({j} : Set G))
  have hZ := d.z_mem_secondDerived D hj hj1 hK
  have hder := d.derived_inf_J_le D
  have hz2 := d.orderOf_z
  have hJp : IsPGroup 2 (J z) := IsPGroup.of_card (n := 9) (card_J_A1 d.hyp)
  have hjz : j ∉ Subgroup.zpowers z := fun hjz => hj1 (d.zpowers_le₁ hjz)
  have hjzc : Commute z j := (Subgroup.mem_centralizer_singleton_iff.mp (J_le_H hj)).symm
  have hzK : z ∈ K := by
    have hzC : z ∈ J z ⊓ Subgroup.centralizer ({j} : Set G) :=
      Subgroup.mem_inf.mpr ⟨z_mem_J_A1 d.hyp,
        Subgroup.mem_centralizer_singleton_iff.mpr hjzc.eq⟩
    refine CFSG.GroupTheory.le_isSylowOf_of_isPGroup_of_le_normalizer hK
      (inf_le_inf_right _ J_le_H) ?_ (hJp.to_le inf_le_left) hzC
    intro g hg
    obtain ⟨hgH, hgj⟩ := Subgroup.mem_inf.mp hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hJ := Subgroup.mem_normalizer_iff.mp (J_le_normalizer_A hgH) x
    have hC := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hgj) x
    simp only [Subgroup.mem_inf]
    exact and_congr hJ hC
  have hKH : K ≤ H z := hK.le.trans inf_le_left
  have hCH : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (J z : Set G) =
      Subgroup.zpowers z :=
    (centralizer_J_eq_centerIn_A1 d.hyp).trans (centerIn_J_eq_zpowers_A1 d.hyp)
  have hconj : ∀ g ∈ Subgroup.normalizer (K : Set G), g * z * g⁻¹ = z := by
    intro g hg
    have hKmap : K.map (MulAut.conj g).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hγ : g * z * g⁻¹ ∈ ⁅K, ⁅K, K⁆⁆ := by
      have hmem : (MulAut.conj g) z ∈ (⁅K, ⁅K, K⁆⁆).map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hZ
      rw [Subgroup.map_commutator, Subgroup.map_commutator, hKmap] at hmem
      simpa [MulAut.conj_apply] using hmem
    have hwK : g * z * g⁻¹ ∈ K := by
      have hmem : (MulAut.conj g) z ∈ K.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hzK
      rw [hKmap] at hmem
      simpa [MulAut.conj_apply] using hmem
    have hwc : g * z * g⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : g⁻¹ * y * g ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
        simpa using this
      have hzc : (g⁻¹ * y * g) * z = z * (g⁻¹ * y * g) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hKH hy')
      calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hzc]
        _ = g * z * g⁻¹ * y := by group
    have hw2 : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
      have hzz : z * z = 1 := by
        rw [← pow_two, ← hz2]
        exact pow_orderOf_eq_one z
      calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hzz]; group
    have hsup : g * z * g⁻¹ ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers j :=
      (parrott77_omega_one_center z j (J z) hz2 rfl d.hyp.extraspecial hCH hj2 hj hjz
        (T := K) hK.le hK.isPGroup (fun S hS hS2 hKS => hK.eq_of_le hKS hS hS2)
        (g * z * g⁻¹)).mp ⟨Subgroup.mem_inf.mpr ⟨hwK, hwc⟩, hw2⟩
    have hwJ : g * z * g⁻¹ ∈ J z :=
      sup_le (Subgroup.zpowers_le.mpr (z_mem_J_A1 d.hyp)) (Subgroup.zpowers_le.mpr hj) hsup
    have hwH3 : g * z * g⁻¹ ∈ ⁅H z, ⁅H z, H z⁆⁆ :=
      Subgroup.commutator_mono hKH (Subgroup.commutator_mono hKH hKH) hγ
    have hwJ₁ : g * z * g⁻¹ ∈ J₁ := hder (Subgroup.mem_inf.mpr ⟨hwH3, hwJ⟩)
    obtain ⟨y, hy, c, hc, hyc⟩ := (CFSG.mem_sup_of_commute (A := Subgroup.zpowers z)
      (B := Subgroup.zpowers j) (fun y hy c hc => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
        exact hjzc.zpow_zpow m n)).mp hsup
    have hwz : g * z * g⁻¹ ∈ Subgroup.zpowers z := by
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hj2).mp hc with rfl | rfl
      · rw [← hyc, mul_one]
        exact hy
      · exfalso
        apply hj1
        have := J₁.mul_mem (J₁.inv_mem (d.zpowers_le₁ hy)) hwJ₁
        rwa [← hyc, ← mul_assoc, inv_mul_cancel, one_mul] at this
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp hwz with h1 | h1
    · exfalso
      have hz1 : z = 1 := by
        calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      rw [hz1, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    · exact h1
  have hN' : ∀ g ∈ Subgroup.centralizer ({j} : Set G), g ∈ Subgroup.normalizer (K : Set G) →
      IsPGroup 2 (Subgroup.zpowers g) → g ∈ Subgroup.centralizer ({z} : Set G) := by
    intro g _ hgn _
    have hgz := hconj g hgn
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hgz]
  have hdvd : 2 ∣ (Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({j} : Set G)).relIndex (Subgroup.centralizer ({z} : Set G)) :=
    CFSG.GroupTheory.dvd_relIndex_inf_centralizer_of_normal_pGroup (p := 2) (H := H z)
      (J := J z) (y := j) J_le_H J_le_normalizer_A hJp (d.not_le_centralizer hj hj1)
  have hnot : ¬ IsConj z j :=
    CFSG.GroupTheory.not_isConj_of_isSylowOf_inf_centralizer (p := 2) (z := z) (y := j)
      (K := K) hK hN' hdvd
  intro g hg
  exact hnot (isConj_iff.mpr ⟨g, hg⟩)

end CaseIData

private theorem caseIData_s1HP
    (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G))
 :
    CaseIData z ((s1HP (quotientDataA1 h) : ↥(H z)) : G)
      (CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G))
      ⁅Subgroup.zpowers ((s1HP (quotientDataA1 h) : ↥(H z)) : G), J z⁆ where
  hyp := h
  σ_mem := (s1HP (quotientDataA1 h)).2
  σ_order := by rw [Subgroup.orderOf_coe]; exact orderOf_s1HP _
  σ_not_mem := by
    intro hmem
    have h1 : qHP (quotientDataA1 h) (s1HP (quotientDataA1 h)) = 1 := by
      rw [← MonoidHom.mem_ker, ker_qHP]
      exact Subgroup.mem_subgroupOf.mpr hmem
    rw [qHP_s1HP] at h1
    exact sigma1_ne_one (by simpa using congrArg Subtype.val h1)
  J₀_eq := rfl
  sup := CJ_s1HP_sup_commutator_eq_J_A1 h
  inf := CJ_s1HP_inf_commutator_eq_A1 h
  comm := commute_CJ_s1HP_commutator_A1 h
  card₀ := card_CJ_s1HP_A1 h
  normal₀ := H_le_normalizer_CJ_s1HP_A1 h heq

theorem no_conj_z_eq_of_mem_J_not_mem_J1_A1
    (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G))
    {j : G} (hjJ : j ∈ J z) (hj2 : orderOf j = 2)
    (hj1 : j ∉ J z ⊓ Subgroup.centralizer
      (CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) : Set G)) :
    ∀ g : G, g * z * g⁻¹ ≠ j := by
  have d := caseIData_s1HP h heq
  have hj1' : j ∉ ⁅Subgroup.zpowers ((s1HP (quotientDataA1 h) : ↥(H z)) : G), J z⁆ := by
    rw [d.eq_inf_centralizer]
    exact hj1
  exact d.no_conj_z_eq (quotientDataA1 h) hjJ hj2 hj1'

end CFSG.RankThree.GF2n.Parrott
