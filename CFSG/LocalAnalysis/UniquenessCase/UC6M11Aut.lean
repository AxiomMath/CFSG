module

public import CFSG.LocalAnalysis.UniquenessCase.UC6AutL2
public import CFSG.LocalAnalysis.UniquenessCase.UC6C621M11
public import Certificates.Certificate419002

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ABGLocalTools

namespace M11K

abbrev S11 : Type := ↥NativeSporadic.M11

@[expose] def U : S11 := m11U

@[expose] def V : S11 := m11b * m11U * m11b⁻¹

@[expose] def Elist : List S11 := [1, U, U ^ 2, V, U * V, U ^ 2 * V, V ^ 2, U * V ^ 2, U ^ 2 * V ^ 2]

@[expose] def Eu : Subgroup S11 := Subgroup.closure {U, V}

theorem Elist_mul : ∀ a ∈ Elist, ∀ b ∈ Elist, a * b ∈ Elist := by decide +kernel

theorem Elist_inv : ∀ a ∈ Elist, a⁻¹ ∈ Elist := by decide +kernel

theorem Elist_pow3 : ∀ a ∈ Elist, a ^ 3 = 1 := by decide +kernel

theorem Elist_nodup : Elist.Nodup := by decide +kernel

theorem Elist_comm : ∀ a ∈ Elist, ∀ b ∈ Elist, a * b = b * a := by decide +kernel

theorem mem_Elist_of_mem_Eu {g : S11} (hg : g ∈ Eu) : g ∈ Elist := by
  unfold Eu at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · decide +kernel
    · decide +kernel
  | one => decide +kernel
  | mul a b _ _ ha hb => exact Elist_mul a ha b hb
  | inv a _ ha => exact Elist_inv a ha

theorem mem_Eu_of_mem_Elist {g : S11} (hg : g ∈ Elist) : g ∈ Eu := by
  have hU : U ∈ Eu := Subgroup.subset_closure (Set.mem_insert _ _)
  have hV : V ∈ Eu := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  simp only [Elist, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact hU
  · exact pow_mem hU 2
  · exact hV
  · exact mul_mem hU hV
  · exact mul_mem (pow_mem hU 2) hV
  · exact pow_mem hV 2
  · exact mul_mem hU (pow_mem hV 2)
  · exact mul_mem (pow_mem hU 2) (pow_mem hV 2)

theorem mem_Eu_iff {g : S11} : g ∈ Eu ↔ g ∈ Elist := ⟨mem_Elist_of_mem_Eu, mem_Eu_of_mem_Elist⟩

theorem pow3_of_mem_Eu {g : S11} (hg : g ∈ Eu) : g ^ 3 = 1 := Elist_pow3 g (mem_Elist_of_mem_Eu hg)

theorem comm_of_mem_Eu {a b : S11} (ha : a ∈ Eu) (hb : b ∈ Eu) : a * b = b * a :=
  Elist_comm a (mem_Elist_of_mem_Eu ha) b (mem_Elist_of_mem_Eu hb)

theorem U_mem : U ∈ Eu := Subgroup.subset_closure (Set.mem_insert _ _)

theorem V_mem : V ∈ Eu := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem Eu_card : Nat.card Eu = 9 := by
  have h : Nat.card Eu = Nat.card {a : S11 // a ∈ Elist} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => mem_Eu_iff)
  rw [h]
  exact card_eq_length (fun a : S11 => a ∈ Elist) id Function.injective_id Elist Elist_nodup
    (fun b => by simp) |>.trans (by decide)

theorem isElemAbelian_Eu : CFSG.Open.IsElemAbelian 3 Eu :=
  ⟨⟨⟨fun a b => Subtype.ext (comm_of_mem_Eu a.2 b.2)⟩⟩, fun a ha => pow3_of_mem_Eu ha⟩

theorem U_val : (U : Equiv.Perm (Fin 11)) = M11Sylow.pU () := rfl

theorem V_val : (V : Equiv.Perm (Fin 11)) = M11Sylow.pV () := rfl

theorem pE_eq : M11Sylow.pE () = Elist.map Subtype.val := by decide +kernel

section Finite


theorem centralizer_Eu {g : S11} (h : ∀ e ∈ Eu, g * e = e * g) : g ∈ Eu := by
  have hU : g * U = U * g := h U U_mem
  have hV : g * V = V * g := h V V_mem
  have hg : (g : Equiv.Perm (Fin 11)) ∈ m11Elements := (mem_m11Elements _).2 g.2
  have key := List.all_eq_true.1 (Certificates.certificate419002).1 _ hg
  have hUp : (g : Equiv.Perm (Fin 11)) * M11Sylow.pU () = M11Sylow.pU () * (g : Equiv.Perm (Fin 11)) := by
    have := congrArg Subtype.val hU
    rw [Subgroup.coe_mul, Subgroup.coe_mul, U_val] at this
    exact this
  have hVp : (g : Equiv.Perm (Fin 11)) * M11Sylow.pV () = M11Sylow.pV () * (g : Equiv.Perm (Fin 11)) := by
    have := congrArg Subtype.val hV
    rw [Subgroup.coe_mul, Subgroup.coe_mul, V_val] at this
    exact this
  simp only [hUp, hVp, decide_true, Bool.and_self, Bool.not_true, Bool.false_or] at key
  rw [pE_eq] at key
  obtain ⟨e, he, heg⟩ := List.mem_map.1 (List.contains_iff_mem.1 key)
  have : e = g := Subtype.ext heg
  exact mem_Eu_of_mem_Elist (this ▸ he)

theorem card_centralizer_Eu {e : S11} (he : e ∈ Eu) (he1 : e ≠ 1) :
    Nat.card (Subgroup.centralizer ({e} : Set S11)) = 18 := by
  classical
  have hel : (e : Equiv.Perm (Fin 11)) ∈ M11Sylow.pE () := by
    rw [pE_eq]
    exact List.mem_map.2 ⟨e, mem_Elist_of_mem_Eu he, rfl⟩
  have key := List.all_eq_true.1 (Certificates.certificate419002).2.1 _ hel
  have hne : (e : Equiv.Perm (Fin 11)) ≠ 1 := fun h => he1 (Subtype.ext h)
  simp only [hne, decide_false, Bool.false_or, beq_iff_eq] at key
  have hcard : Nat.card {a : S11 // a ∈ Subgroup.centralizer ({e} : Set S11)} =
      (m11Elements.filter fun g => decide (g * (e : Equiv.Perm (Fin 11)) = (e : Equiv.Perm (Fin 11)) * g)).length := by
    refine card_eq_length _ Subtype.val Subtype.val_injective _
      (m11Elements_nodup.filter _) (fun b => ?_)
    constructor
    · intro hb
      obtain ⟨hbm, hbc⟩ := List.mem_filter.1 hb
      have hbM : b ∈ NativeSporadic.M11 := (mem_m11Elements b).1 hbm
      refine ⟨⟨b, hbM⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have := of_decide_eq_true hbc
      simpa only [Subgroup.coe_mul] using this
    · rintro ⟨a, ha, rfl⟩
      refine List.mem_filter.2 ⟨(mem_m11Elements _).2 a.2, ?_⟩
      have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 ha)
      simpa only [Subgroup.coe_mul] using decide_eq_true this
  exact hcard.trans key

theorem move_pair (g : S11) (hg : orderOf g = 5 ∨ orderOf g = 11) :
    ((g : Equiv.Perm (Fin 11)) M11Sylow.p0 ≠ M11Sylow.p0 ∧
        (g : Equiv.Perm (Fin 11)) M11Sylow.p0 ≠ M11Sylow.q0) ∨
      ((g : Equiv.Perm (Fin 11)) M11Sylow.q0 ≠ M11Sylow.p0 ∧
        (g : Equiv.Perm (Fin 11)) M11Sylow.q0 ≠ M11Sylow.q0) := by
  have hmem : (g : Equiv.Perm (Fin 11)) ∈ m11Elements := (mem_m11Elements _).2 g.2
  have key := List.all_eq_true.1 (Certificates.certificate419002).2.2 _ hmem
  have hp : (orderIs (g : Equiv.Perm (Fin 11)) 5 || orderIs (g : Equiv.Perm (Fin 11)) 11) = true := by
    rcases hg with h | h
    · simp [(m11_orderOf_eq_iff g (by norm_num)).1 h]
    · simp [(m11_orderOf_eq_iff g (by norm_num)).1 h]
  simp only [hp, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne,
    ne_eq] at key
  exact key

theorem allInner (α : MulAut S11) : ∃ g : S11, α = MulAut.conj g := by
  have h : α ∈ inner S11 := by
    rw [inner_eq_top_of_card_le m11_center_eq_bot' m11_mulAut_card]; trivial
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg.symm⟩

theorem conj_inj : Function.Injective (MulAut.conj : S11 →* MulAut S11) :=
  conj_injective_of_center NativeSporadic.M11 m11_center_eq_bot'

theorem mem_Eu_of_conj_fix {g : S11} (h : ∀ e ∈ Eu, (MulAut.conj g : MulAut S11) e = e) : g ∈ Eu := by
  refine centralizer_Eu fun e he => ?_
  have h' := h e he
  rw [MulAut.conj_apply] at h'
  calc g * e = (g * e * g⁻¹) * g := by group
    _ = e * g := by rw [h']

theorem absKC_m11 : AbsKC S11 3 Eu := by
  intro α _ hfix
  obtain ⟨g, rfl⟩ := allInner α
  exact ⟨g, mem_Eu_of_conj_fix hfix, rfl⟩

theorem absKInv_m11 : AbsKInv S11 Eu := by
  intro x y hx _ hxf _ hx1 _
  exfalso
  apply hx1
  obtain ⟨g, rfl⟩ := allInner x
  have hg : g ∈ Eu := mem_Eu_of_conj_fix hxf
  have h3 : orderOf (MulAut.conj g : MulAut S11) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow3_of_mem_Eu hg, map_one])
  obtain ⟨k, hk⟩ := hx
  rw [hk] at h3
  have h1 : 2 ^ k = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)) h3
  rw [h1] at hk
  exact orderOf_eq_one_iff.1 hk

theorem mem_normalizer_of_commute {e : S11} (he : e ∈ Eu) (he1 : e ≠ 1) {g : S11} (hg : g * e = e * g)
    {e' : S11} (he' : e' ∈ Eu) : g * e' * g⁻¹ ∈ Eu := by
  classical
  set C : Subgroup S11 := Subgroup.centralizer ({e} : Set S11) with hC
  have hEC : Eu ≤ C := fun x hx => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_mem_Eu hx he
  have hCcard := card_centralizer_Eu he he1
  have hcardEC : Nat.card (Eu.subgroupOf C) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, Eu_card]
  have hidx : (Eu.subgroupOf C).index = 2 := by
    have h := Subgroup.card_mul_index (Eu.subgroupOf C)
    rw [hcardEC, hCcard] at h
    omega
  haveI : (Eu.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hidx
  have hgC : g ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact hg
  have hmem : (⟨g, hgC⟩ : C) * ⟨e', hEC he'⟩ * (⟨g, hgC⟩ : C)⁻¹ ∈ Eu.subgroupOf C :=
    Subgroup.Normal.conj_mem inferInstance _ (Subgroup.mem_subgroupOf.2 he') _
  exact Subgroup.mem_subgroupOf.1 hmem

theorem absKN_m11 (P : Prop) : AbsKN S11 3 Eu P := by
  refine absKN_generic Nat.prime_three isElemAbelian_Eu (by rw [Eu_card]; norm_num) m11_center_eq_bot' ?_ ?_ P
  · intro e he he1 α hα e' he'
    obtain ⟨g, rfl⟩ := allInner α
    have hg : g * e = e * g := by
      have h := hα
      rw [MulAut.conj_apply] at h
      calc g * e = (g * e * g⁻¹) * g := by group
        _ = e * g := by rw [h]
    exact mem_normalizer_of_commute he he1 hg he'
  · intro α hα
    obtain ⟨g, rfl⟩ := allInner α
    have hg : g ∈ Eu := mem_Eu_of_conj_fix hα
    have h3 : orderOf (MulAut.conj g : MulAut S11) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow3_of_mem_Eu hg, map_one])
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩

theorem absKN_m11_of_eq {r : ℕ} (hr : r = 3) (P : Prop) : AbsKN S11 r Eu P := by
  subst hr
  exact absKN_m11 P

end Finite

theorem card_S11 : Nat.card S11 = 7920 := card_M11

theorem factorization_S11 : (Nat.card S11).factorization 3 = 2 := by
  rw [card_S11, show (7920 : ℕ) = 3 ^ 2 * 880 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem isSylowOf_Eu : IsSylowOf 3 Eu ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isSylowOf_of_card le_top ?_
  rw [Eu_card, Subgroup.card_top, factorization_S11]
  norm_num

end M11K

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)


theorem kc633_of_m11 (h620 : m.C620) (hr3 : m.r = 3)
    (hX : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor m.Lbar .M11) : m.KC633 := by
  obtain ⟨φ0⟩ := hX
  let φ : m.Lbar ≃* M11K.S11 := φ0
  refine m.kc633_of_model h620 φ (by rw [hr3]; exact M11K.factorization_S11)
    (E₀ := M11K.Eu) (by rw [hr3]; exact M11K.isSylowOf_Eu) ?_
  rw [hr3]
  exact M11K.absKC_m11

theorem kn633_of_m11 (h620 : m.C620) (hr3 : m.r = 3)
    (hX : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor m.Lbar .M11) : m.KN633 := by
  obtain ⟨φ0⟩ := hX
  let φ : m.Lbar ≃* M11K.S11 := φ0
  refine m.kn633_of_model h620 φ (by rw [hr3]; exact M11K.factorization_S11)
    (E₀ := M11K.Eu) (by rw [hr3]; exact M11K.isSylowOf_Eu) ?_
  exact M11K.absKN_m11_of_eq hr3 _

theorem kinv633_of_m11 (h620 : m.C620) (hr3 : m.r = 3)
    (hX : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor m.Lbar .M11) : m.KInv633 := by
  obtain ⟨φ0⟩ := hX
  let φ : m.Lbar ≃* M11K.S11 := φ0
  exact m.kinv633_of_model h620 φ (by rw [hr3]; exact M11K.factorization_S11)
    (E₀ := M11K.Eu) (by rw [hr3]; exact M11K.isSylowOf_Eu) M11K.absKInv_m11

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
