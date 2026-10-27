module

public import CFSG.Quasithin.SteinbergBSA7ReversalOvergroup
public import CFSG.LocalAnalysis.SteinbergBVA7ConjugateCentralizerIndex
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAlt3
public import CFSG.Dihedral.Glauberman.DicksonMaxExist

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup CFSG CFSG.QuasithinUnique CFSG.LocalAnalysis.SteinbergBV
open CFSG.LocalAnalysis.SteinbergBV.ConstantRank
open scoped commutatorElement Pointwise

namespace ReversalPair

section Helpers

variable {G : Type*} [Group G]

theorem eq_of_mem_of_card_eq_two {E : Subgroup G} (hE : Nat.card E = 2) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨y, z, hyz, hyz'⟩ := Nat.card_eq_two_iff.1 hE
  have hmem : ∀ w : E, w = y ∨ w = z := fun w => by
    have : w ∈ ({y, z} : Set E) := hyz' ▸ Set.mem_univ w
    simpa using this
  have ha1' : (⟨a, ha⟩ : E) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hb1' : (⟨b, hb⟩ : E) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have key : (⟨a, ha⟩ : E) = ⟨b, hb⟩ := by
    rcases hmem 1 with h1 | h1 <;> rcases hmem ⟨a, ha⟩ with h2 | h2 <;>
      rcases hmem ⟨b, hb⟩ with h3 | h3
    all_goals first
      | exact h2.trans h3.symm
      | exact absurd (h2.trans h1.symm) ha1'
      | exact absurd (h3.trans h1.symm) hb1'
  exact congrArg Subtype.val key

theorem eq_of_le_of_prime_relIndex {E W U : Subgroup G} (hEW : E ≤ W) (hWU : W ≤ U)
    (hp : (E.relIndex U).Prime) (hne : ¬ W ≤ E) : W = U := by
  have hmul := relIndex_mul_relIndex E W U hEW hWU
  rcases hp.eq_one_or_self_of_dvd _ (Dvd.intro_left _ hmul) with h | h
  · exact le_antisymm hWU (relIndex_eq_one.1 h)
  · rw [h] at hmul
    exact absurd (relIndex_eq_one.1
      (Nat.eq_of_mul_eq_mul_right hp.pos (hmul.trans (one_mul _).symm))) hne

theorem conj_mem_centralizer {W : Subgroup G} {g z : G} (hg : g ∈ normalizer (W : Set G))
    (hz : z ∈ centralizer (W : Set G)) : g * z * g⁻¹ ∈ centralizer (W : Set G) := by
  rw [mem_centralizer_iff] at hz ⊢
  intro w hw
  have hw' : g⁻¹ * w * g ∈ W := by
    refine (mem_normalizer_iff.1 hg _).2 ?_
    rwa [show g * (g⁻¹ * w * g) * g⁻¹ = w by group]
  have h := hz _ hw'
  calc w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [h]
    _ = g * z * g⁻¹ * w := by group

theorem mem_normalizer_conjugate {W : Subgroup G} {g x : G}
    (h : x * g * x⁻¹ ∈ normalizer (W : Set G)) :
    g ∈ normalizer ((CFSG.conjugate W x : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro z
  rw [mem_conjugate_iff_conj, mem_conjugate_iff_conj,
    show x * (g * z * g⁻¹) * x⁻¹ = (x * g * x⁻¹) * (x * z * x⁻¹) * (x * g * x⁻¹)⁻¹ by group]
  exact (mem_normalizer_iff.1 h) _

theorem le_or_le_of_forall_mem_or {H K₁ K₂ : Subgroup G} (h : ∀ z ∈ H, z ∈ K₁ ∨ z ∈ K₂) :
    H ≤ K₁ ∨ H ≤ K₂ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨a, haH, haK⟩ := IsConcreteLE.not_le_iff_exists.1 hcon.1
  obtain ⟨b, hbH, hbK⟩ := IsConcreteLE.not_le_iff_exists.1 hcon.2
  have ha2 : a ∈ K₂ := (h a haH).resolve_left haK
  have hb1 : b ∈ K₁ := (h b hbH).resolve_right hbK
  rcases h (a * b) (mul_mem haH hbH) with hab | hab
  · exact haK (by simpa using mul_mem hab (inv_mem hb1))
  · exact hbK (by simpa using mul_mem (inv_mem ha2) hab)

end Helpers

section Block

variable {G : Type} [Group G] [Finite G]

theorem a3_data {K : Subgroup G} (hK : IsShort2 K) (h3 : Nat.card (K ⧸ CFSG.pCore 2 K) = 3) :
    Nonempty (K ≃* alternatingGroup (Fin 4)) ∧ blockQ K ≤ K ∧ Nat.card (blockQ K) = 4 ∧
      (∀ u ∈ blockQ K, u * u = 1) ∧ blockQ K ≤ centralizer (blockQ K : Set G) ∧
      Nat.card K = 12 ∧ blockQ K ⊓ centralizer (K : Set G) = ⊥ ∧
      K ≤ normalizer (blockQ K : Set G) ∧
      ∃ c ∈ K, c ∈ normalizer (blockQ K : Set G) ∧
        (∀ u ∈ blockQ K, u ≠ 1 → c * u * c⁻¹ ≠ u) ∧ K = blockQ K ⊔ zpowers c := by
  obtain ⟨hQU, -, hZ, hiso, halt⟩ := Setup.Campbell.short_order_three_is_alternating_four hK h3
  obtain ⟨-, hcard, hexp, hcomm, hK12, -, c, hcK, -, hcN, hcfix, hKgen⟩ :=
    hK.alt3_structure halt
  rw [← hQU] at hcard hexp hcomm hcN hcfix hKgen
  have hZ' : blockQ K ⊓ centralizer (K : Set G) = ⊥ := by
    rw [hQU]
    exact hZ
  refine ⟨hiso, le_sup_left.trans hKgen.ge, hcard, fun u hu => by rw [← sq]; exact hexp u hu,
    fun u hu => mem_centralizer_iff.2 fun v hv => hcomm v hv u hu, hK12, hZ',
    hKgen.le.trans (sup_le le_normalizer (zpowers_le.2 hcN)), c, hcK, hcN, hcfix, hKgen⟩

theorem block_structure {K P U Q D : Subgroup G} (hK : IsShort2 K)
    (h3 : Nat.card (K ⧸ CFSG.pCore 2 K) = 3) (hPK : P ≤ normalizer (K : Set G))
    (hU : U = blockQ K) (hUP : U ≤ P) (hQ : Q = P ⊓ centralizer (U : Set G))
    (hD : D = P ⊓ centralizer (K : Set G)) :
    Nonempty (K ≃* alternatingGroup (Fin 4)) ∧ IsKleinFour U ∧
      K ⊓ centralizer (U : Set G) = U ∧ Q ≤ K ⊔ P ∧ K ⊔ P ≤ normalizer (Q : Set G) ∧
      ⁅Q, K⁆ ≤ U ∧ U ⊔ D = Q ∧ U ⊓ D = ⊥ ∧ D ≤ centralizer (U : Set G) := by
  classical
  obtain ⟨hiso, hUK, hcard, hexp, hab, hK12, hZ, hKN, c, hcK, hcN, hcfix, hKgen⟩ := a3_data hK h3
  rw [← hU] at hUK hcard hexp hab hZ hKN hcN hcfix hKgen
  subst hQ hD
  have hPU : P ≤ normalizer (U : Set G) := by
    rw [hU]
    exact hPK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hUne : U ≠ ⊥ := fun h => by
    rw [h, card_bot] at hcard
    exact absurd hcard (by norm_num)
  have hKlein : IsKleinFour U := by
    have : Nontrivial U := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      norm_num
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).2 fun g hg => ?_⟩
    refine orderOf_eq_prime (Subtype.ext ?_) hg
    rw [Subgroup.coe_pow, sq]
    exact hexp g g.2
  have hUidx : U.relIndex K = 3 := by
    have h := relIndex_mul_card U K
    rw [inf_of_le_left hUK, hcard, hK12] at h
    omega
  have hCKU : K ⊓ centralizer (U : Set G) = U := by
    refine le_antisymm ?_ (le_inf hUK hab)
    by_contra hne
    have h := eq_of_le_of_prime_relIndex (le_inf hUK hab) inf_le_left
      (hUidx ▸ Nat.prime_three) hne
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hUne
    have hu1' : u ≠ 1 := fun h' => hu1 (Subtype.ext h')
    have hcC : c ∈ centralizer (U : Set G) := (h.ge hcK).2
    exact hcfix u hu hu1' (by rw [(mem_centralizer_iff.1 hcC u hu).symm, mul_inv_cancel_right])
  have hcommQK : ⁅P ⊓ centralizer (U : Set G), K⁆ ≤ U := by
    rw [commutator_le]
    intro q hq k hk
    obtain ⟨hqP, hqC⟩ := mem_inf.1 hq
    rw [← hCKU]
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.1 (hPK hqP) k).1 hk) (inv_mem hk)
    · rw [commutatorElement_def, show q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) by group]
      exact mul_mem hqC (conj_mem_centralizer (hKN hk) (inv_mem hqC))
  have hUQ : U ≤ P ⊓ centralizer (U : Set G) := le_inf hUP hab
  have hKQ : K ≤ normalizer ((P ⊓ centralizer (U : Set G) : Subgroup G) : Set G) := by
    refine ReversalOvergroup.le_normalizer_of_conj_mem fun k hk q hq => ?_
    have h1 : ⁅k, q⁆ ∈ U := hcommQK (by rw [commutator_comm]; exact commutator_mem_commutator hk hq)
    rw [show k * q * k⁻¹ = ⁅k, q⁆ * q by rw [commutatorElement_def]; group]
    exact mul_mem (hUQ h1) hq
  have hPQ := le_normalizer_inf_centralizer hPU
  have hDU : P ⊓ centralizer (K : Set G) ≤ centralizer (U : Set G) :=
    inf_le_right.trans (centralizer_le (SetLike.coe_subset_coe.2 hUK))
  have hQUD : P ⊓ centralizer (U : Set G) ≤ U ⊔ P ⊓ centralizer (K : Set G) := by
    intro q hq
    obtain ⟨hqP, hqC⟩ := mem_inf.1 hq
    have hcU : ∀ u ∈ U, c * u * c⁻¹ ∈ U := fun u hu => (mem_normalizer_iff.1 hcN u).1 hu
    let f : U → U := fun u => ⟨u * (c * u * c⁻¹)⁻¹, mul_mem u.2 (inv_mem (hcU u u.2))⟩
    have hfinj : Function.Injective f := by
      intro u v huv
      have h : (u : G) * (c * u * c⁻¹)⁻¹ = v * (c * v * c⁻¹)⁻¹ := congrArg Subtype.val huv
      have h' : (c * v * c⁻¹)⁻¹ * (c * u * c⁻¹) = (v : G)⁻¹ * u := by
        calc (c * v * c⁻¹)⁻¹ * (c * u * c⁻¹)
            = (v : G)⁻¹ * (v * (c * v * c⁻¹)⁻¹) * (c * u * c⁻¹) := by group
          _ = (v : G)⁻¹ * (u * (c * u * c⁻¹)⁻¹) * (c * u * c⁻¹) := by rw [h]
          _ = (v : G)⁻¹ * u := by group
      by_contra hne
      have hw : (v : G)⁻¹ * u ≠ 1 := fun h1 =>
        hne (Subtype.ext (inv_mul_eq_one.1 h1).symm)
      exact hcfix _ (mul_mem (inv_mem v.2) u.2) hw (by
        calc c * ((v : G)⁻¹ * u) * c⁻¹ = (c * v * c⁻¹)⁻¹ * (c * u * c⁻¹) := by group
          _ = (v : G)⁻¹ * u := h')
    have hw : ⁅c, q⁆ ∈ U := by
      rw [← commutatorElement_inv]
      exact inv_mem (hcommQK (commutator_mem_commutator hq hcK))
    obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.1 hfinj) ⟨⁅c, q⁆, hw⟩
    have hu' : (u : G) * (c * u * c⁻¹)⁻¹ = c * q * c⁻¹ * q⁻¹ := by
      rw [← commutatorElement_def]
      exact congrArg Subtype.val hu
    have hcomm1 : (c * u * c⁻¹) * u = u * (c * u * c⁻¹) :=
      mem_centralizer_iff.1 (hab u.2) _ (hcU u u.2)
    have hcq : c * (u * q) * c⁻¹ = u * q := by
      calc c * (u * q) * c⁻¹ = (c * u * c⁻¹) * (c * q * c⁻¹ * q⁻¹) * q := by group
        _ = (c * u * c⁻¹) * (u * (c * u * c⁻¹)⁻¹) * q := by rw [← hu']
        _ = ((c * u * c⁻¹) * u) * (c * u * c⁻¹)⁻¹ * q := by group
        _ = (u * (c * u * c⁻¹)) * (c * u * c⁻¹)⁻¹ * q := by rw [hcomm1]
        _ = u * q := by group
    have huqK : (u : G) * q ∈ centralizer (K : Set G) := by
      rw [mem_centralizer_iff]
      intro k hk
      have hle : K ≤ centralizer ({(u : G) * q} : Set G) := by
        refine hKgen.le.trans (sup_le (fun w hw => ?_) (zpowers_le.2 ?_))
        · rw [mem_centralizer_singleton_iff]
          have h1 : w * u = u * w := mem_centralizer_iff.1 (hab u.2) w hw
          have h2 : w * q = q * w := mem_centralizer_iff.1 hqC w hw
          calc w * (u * q) = (w * u) * q := by group
            _ = u * (w * q) := by rw [h1]; group
            _ = (u * q) * w := by rw [h2]; group
        · rw [mem_centralizer_singleton_iff]
          calc c * (u * q) = c * (u * q) * c⁻¹ * c := by group
            _ = u * q * c := by rw [hcq]
      exact mem_centralizer_singleton_iff.1 (hle hk)
    rw [show q = (u : G)⁻¹ * (u * q) by group]
    exact mul_mem ((le_sup_left : U ≤ U ⊔ P ⊓ centralizer (K : Set G)) (inv_mem u.2))
      ((le_sup_right : P ⊓ centralizer (K : Set G) ≤ U ⊔ P ⊓ centralizer (K : Set G))
        (mem_inf.2 ⟨mul_mem (hUP u.2) hqP, huqK⟩))
  refine ⟨hiso, hKlein, hCKU, inf_le_left.trans le_sup_right, sup_le hKQ hPQ, hcommQK,
    le_antisymm (sup_le hUQ (le_inf inf_le_left hDU)) hQUD, ?_, hDU⟩
  exact le_bot_iff.1 (hZ ▸ le_inf inf_le_left (inf_le_right.trans inf_le_right))

end Block

section Reversal

variable {G : Type} [Group G] [Finite G]

theorem reversal_pair {K P U Q D A E : Subgroup G} (hK : IsShort2 K)
    (h3 : Nat.card (K ⧸ CFSG.pCore 2 K) = 3) (hP : IsPGroup 2 P)
    (hPK : P ≤ normalizer (K : Set G)) (hU : U = blockQ K) (hUP : U ≤ P)
    (hQ : Q = P ⊓ centralizer (U : Set G)) (hD : D = P ⊓ centralizer (K : Set G)) {x : G}
    (hx : x ∈ normalizer (P : Set G)) (hA : A = CFSG.conjugate U x) (hE : E = ⁅U, A⁆)
    (hE1 : E ≠ ⊥) :
    A ≤ P ∧ P ≤ normalizer (A : Set G) ∧
      E = U ⊓ A ∧ U ⊓ A = U ⊓ centralizer (A : Set G) ∧
      U ⊓ centralizer (A : Set G) = A ⊓ centralizer (U : Set G) ∧ Nat.card E = 2 ∧
      E ≤ P ⊓ centralizer (P : Set G) ∧ CFSG.conjugate E x = E ∧
      A ⊔ Q = P ∧ U ⊔ (P ⊓ centralizer (A : Set G)) = P ∧
      U ⊔ (P ⊓ centralizer ((U ⊔ A : Subgroup G) : Set G)) = Q ∧
      P ⊓ centralizer (A : Set G) = A ⊔ (P ⊓ centralizer ((U ⊔ A : Subgroup G) : Set G)) ∧
      (Q ⊓ centralizer (A : Set G)).relIndex Q = 2 ∧ D ≤ centralizer (A : Set G) ∧
      U ⊔ A ⊔ D = P ∧ (U ⊔ A) ⊓ D = ⊥ ∧ D ≤ centralizer ((U ⊔ A : Subgroup G) : Set G) ∧
      Nonempty (↥(U ⊔ A) ≃* DihedralGroup 4) ∧
      CFSG.conjugate ((frattini D).map D.subtype) x = (frattini D).map D.subtype ∧
      Even (orderOf x) := by
  classical
  obtain ⟨-, -, -, -, hKPQ, hcommQK, hUD, hUDbot, hDU⟩ := block_structure hK h3 hPK hU hUP hQ hD
  obtain ⟨-, hUK, hcard, hexp, hab, hK12, hZ, -, c, hcK, hcN, hcfix, -⟩ := a3_data hK h3
  rw [← hU] at hUK hcard hexp hab hZ hcN hcfix
  have hPU : P ≤ normalizer (U : Set G) := by
    rw [hU]
    exact hPK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hKQ : K ≤ normalizer (Q : Set G) := le_sup_left.trans hKPQ
  have hQP : Q ≤ P := hQ ▸ inf_le_left
  have hUQ : U ≤ Q := hQ ▸ le_inf hUP hab
  have hQCU : Q ≤ centralizer (U : Set G) := hQ ▸ inf_le_right
  have hDP : D ≤ P := hD ▸ inf_le_left
  have hDQ : D ≤ Q := hUD ▸ le_sup_right
  have hUne : U ≠ ⊥ := fun h => by
    rw [h, card_bot] at hcard
    exact absurd hcard (by norm_num)
  have hUidx : U.relIndex K = 3 := by
    have h := relIndex_mul_card U K
    rw [inf_of_le_left hUK, hcard, hK12] at h
    omega
  have hxP : CFSG.conjugate P x = P := conjugate_eq_self_of_mem_normalizer hx
  have hAP : A ≤ P := by
    rw [hA]
    intro z hz
    rw [← hxP, mem_conjugate_iff_conj]
    rw [mem_conjugate_iff_conj] at hz
    exact hUP hz
  have hPA : P ≤ normalizer (A : Set G) := by
    rw [hA]
    intro p hp
    exact mem_normalizer_conjugate (hPU ((mem_normalizer_iff.1 hx p).1 hp))
  have hAcard : Nat.card A = 4 := by
    rw [hA, CFSG.conjugate, card_map_of_injective (MulAut.conj x⁻¹).injective, hcard]
  have hAexp : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    rw [hA, mem_conjugate_iff_conj] at ha
    have h : x * (a * a) * x⁻¹ = 1 := by
      rw [← hexp _ ha]
      group
    exact conj_eq_one_iff.1 h
  have hAab : A ≤ centralizer (A : Set G) := by
    rw [hA]
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    rw [SetLike.mem_coe, mem_conjugate_iff_conj] at hb
    rw [mem_conjugate_iff_conj] at ha
    have h := mem_centralizer_iff.1 (hab ha) _ hb
    calc b * a = x⁻¹ * ((x * b * x⁻¹) * (x * a * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * a * x⁻¹) * (x * b * x⁻¹)) * x := by rw [h]
      _ = a * b := by group
  have hPnC : ¬ P ≤ centralizer (U : Set G) := by
    intro h
    apply hE1
    rw [hE, commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
    exact hAP.trans h
  have hZ₀ne : U ⊓ centralizer (P : Set G) ≠ ⊥ := by
    have : Group.IsNilpotent P := hP.isNilpotent
    have hnormal : (U.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPU
    have hne : U.subgroupOf P ≠ ⊥ := by
      intro h
      apply hUne
      rw [← map_subgroupOf_eq_of_le hUP, h, Subgroup.map_bot]
    obtain ⟨⟨y, hy⟩, hy1⟩ :=
      ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    intro hbot
    have hyZ : (y : G) ∈ U ⊓ centralizer (P : Set G) := by
      refine mem_inf.2 ⟨(mem_inf.1 hy).1, ?_⟩
      rw [mem_centralizer_iff]
      intro p hp
      exact congrArg Subtype.val (mem_center_iff.mp (mem_inf.1 hy).2 ⟨p, hp⟩)
    rw [hbot, mem_bot] at hyZ
    exact hy1 (Subtype.ext (Subtype.ext hyZ))
  have hZ₀card : Nat.card (U ⊓ centralizer (P : Set G) : Subgroup G) = 2 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show Nat.card (U ⊓ centralizer (P : Set G) : Subgroup G) ∣ 2 ^ 2 by
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hcard]
        exact card_dvd_of_le inf_le_left)
    interval_cases k
    · exact absurd (eq_bot_of_card_eq _ hk') hZ₀ne
    · exact hk'
    · exfalso
      have h : U ⊓ centralizer (P : Set G) = U :=
        eq_of_le_of_card_ge inf_le_left (by rw [hk', hcard]; norm_num)
      exact hPnC (le_centralizer_iff.mp (h.ge.trans inf_le_right))
  have hZ₀idx : (U ⊓ centralizer (P : Set G)).relIndex U = 2 := by
    have h := relIndex_mul_card (U ⊓ centralizer (P : Set G)) U
    rw [inf_of_le_left (inf_le_left : U ⊓ centralizer (P : Set G) ≤ U), hZ₀card, hcard] at h
    omega
  have hcommZ : ∀ s ∈ P, ∀ u ∈ U, ⁅s, u⁆ ∈ U ⊓ centralizer (P : Set G) := by
    intro s hs u hu
    have hsu : s * u * s⁻¹ ∈ U := (mem_normalizer_iff.1 (hPU hs) u).1 hu
    have hiff : s * u * s⁻¹ ∈ U ⊓ centralizer (P : Set G) ↔ u ∈ U ⊓ centralizer (P : Set G) := by
      constructor
      · intro h
        have hc : s * (s * u * s⁻¹) = (s * u * s⁻¹) * s :=
          mem_centralizer_iff.1 (mem_inf.1 h).2 s hs
        have : s * u * s⁻¹ = u := by
          calc s * u * s⁻¹ = s⁻¹ * (s * (s * u * s⁻¹)) := by group
            _ = s⁻¹ * ((s * u * s⁻¹) * s) := by rw [hc]
            _ = u := by group
        rwa [this] at h
      · intro h
        have hc : s * u = u * s := mem_centralizer_iff.1 (mem_inf.1 h).2 s hs
        rwa [hc, mul_inv_cancel_right]
    have h2 : ((U ⊓ centralizer (P : Set G)).subgroupOf U).index = 2 := hZ₀idx
    have h := (mul_mem_iff_of_index_two h2 (a := ⟨s * u * s⁻¹, hsu⟩) (b := ⟨u, hu⟩⁻¹)).2 (by
      rw [mem_subgroupOf, mem_subgroupOf, InvMemClass.coe_inv, inv_mem_iff]
      exact hiff)
    rw [mem_subgroupOf] at h
    rw [commutatorElement_def]
    exact h
  obtain ⟨u₀, hu₀U, hu₀Z⟩ : ∃ u₀ ∈ U, u₀ ∉ U ⊓ centralizer (P : Set G) := by
    by_contra h
    push Not at h
    have := card_le_of_le (show U ≤ U ⊓ centralizer (P : Set G) from h)
    rw [hcard, hZ₀card] at this
    omega
  have hQiff : ∀ s ∈ P, s ∈ Q ↔ ⁅s, u₀⁆ = 1 := by
    intro s hs
    constructor
    · intro hsQ
      rw [commutatorElement_def, (mem_centralizer_iff.1 (hQCU hsQ) u₀ hu₀U).symm]
      group
    · intro h1
      rw [hQ]
      refine mem_inf.2 ⟨hs, ?_⟩
      have hW : U ⊓ centralizer ({s} : Set G) = U := by
        refine eq_of_le_of_prime_relIndex (le_inf inf_le_left ?_) inf_le_left
          (hZ₀idx ▸ Nat.prime_two) fun h => hu₀Z (h (mem_inf.2 ⟨hu₀U, ?_⟩))
        · intro z hz
          rw [mem_centralizer_singleton_iff]
          exact (mem_centralizer_iff.1 (mem_inf.1 hz).2 s hs).symm
        · rw [mem_centralizer_singleton_iff]
          rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
          exact h1.symm
      rw [mem_centralizer_iff]
      intro u hu
      exact (mem_centralizer_singleton_iff.1 (mem_inf.1 (hW.ge hu)).2)
  have hchimul : ∀ s ∈ P, ∀ s' ∈ P, ⁅s * s', u₀⁆ = ⁅s, u₀⁆ * ⁅s', u₀⁆ := by
    intro s hs s' hs'
    have hc' : s * ⁅s', u₀⁆ * s⁻¹ = ⁅s', u₀⁆ := by
      have := mem_centralizer_iff.1 (mem_inf.1 (hcommZ s' hs' u₀ hu₀U)).2 s hs
      rw [this, mul_inv_cancel_right]
    have hcomm' : ⁅s', u₀⁆ * ⁅s, u₀⁆ = ⁅s, u₀⁆ * ⁅s', u₀⁆ :=
      mem_centralizer_iff.1 (hab (mem_inf.1 (hcommZ s hs u₀ hu₀U)).1) _
        (mem_inf.1 (hcommZ s' hs' u₀ hu₀U)).1
    calc ⁅s * s', u₀⁆ = (s * ⁅s', u₀⁆ * s⁻¹) * ⁅s, u₀⁆ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅s, u₀⁆ * ⁅s', u₀⁆ := by rw [hc', hcomm']
  obtain ⟨s₀, hs₀P, hs₀Q⟩ : ∃ s₀ ∈ P, s₀ ∉ Q := by
    by_contra h
    push Not at h
    exact hPnC ((show P ≤ Q from h).trans hQCU)
  have hQidx : Q.relIndex P = 2 := by
    change (Q.subgroupOf P).index = 2
    rw [index_eq_two_iff]
    refine ⟨⟨s₀, hs₀P⟩, fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : G) ∈ Q
    · refine Or.inr ⟨hb, fun h => hs₀Q ?_⟩
      have := mul_mem (inv_mem hb) h
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨?_, hb⟩
      rw [hQiff _ (mul_mem b.2 hs₀P), hchimul _ b.2 _ hs₀P]
      have h1 : ⁅(b : G), u₀⁆ ≠ 1 := fun h => hb ((hQiff _ b.2).2 h)
      have h2 : ⁅s₀, u₀⁆ ≠ 1 := fun h => hs₀Q ((hQiff _ hs₀P).2 h)
      rw [eq_of_mem_of_card_eq_two hZ₀card (hcommZ _ b.2 u₀ hu₀U) (hcommZ _ hs₀P u₀ hu₀U) h1 h2]
      exact hexp _ (mem_inf.1 (hcommZ _ hs₀P u₀ hu₀U)).1
  have hconst : ∀ s ∈ P, s ∉ Q → (U ⊓ centralizer ({s} : Set G)).relIndex U = 2 := by
    intro s hs hsQ
    have hle : U ⊓ centralizer (P : Set G) ≤ U ⊓ centralizer ({s} : Set G) := by
      refine le_inf inf_le_left fun z hz => ?_
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 (mem_inf.1 hz).2 s hs).symm
    have hW : U ⊓ centralizer ({s} : Set G) = U ⊓ centralizer (P : Set G) := by
      refine le_antisymm ?_ hle
      by_contra hne
      have h := eq_of_le_of_prime_relIndex hle inf_le_left (hZ₀idx ▸ Nat.prime_two) hne
      apply hsQ
      rw [hQ]
      refine mem_inf.2 ⟨hs, mem_centralizer_iff.2 fun u hu => ?_⟩
      exact mem_centralizer_singleton_iff.1 (mem_inf.1 (h.ge hu)).2
    rw [hW, hZ₀idx]
  have hUel : IsElementaryAbelian 2 U := by
    have hcommU : IsMulCommutative U :=
      ⟨⟨fun a b => Subtype.ext (mem_centralizer_iff.1 (hab b.2) a a.2)⟩⟩
    have hexpU : Monoid.exponent U ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
      Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact hexp g g.2)
    exact { toIsMulCommutative := hcommU, exponent_dvd_p := hexpU }
  obtain ⟨hAQ, hUQx, -, hUC, hACx, hCidx, hUCA, hACU, hFrat, hcommUP⟩ :=
    constant_rank_conjugates_force_centralizer_factorization (p := 2) (n := 1) hP hx hUP hPU hUel
      hA hQ rfl le_rfl (by rw [pow_one]; exact hQidx)
      (fun s hs hsQ => by rw [pow_one]; exact hconst s hs hsQ) (hE ▸ hE1)
  have hUPZ : ⁅U, P⁆ = U ⊓ centralizer (P : Set G) := by
    have hle : ⁅U, P⁆ ≤ U ⊓ centralizer (P : Set G) := by
      rw [commutator_le]
      intro u hu s hs
      rw [← commutatorElement_inv]
      exact inv_mem (hcommZ s hs u hu)
    have hne : ⁅U, P⁆ ≠ ⊥ := by
      rw [Ne, commutator_eq_bot_iff_le_centralizer]
      exact fun h => hPnC (le_centralizer_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_two).1 (hZ₀card ▸ card_dvd_of_le hle) with h | h
    · exact absurd (eq_bot_of_card_eq _ h) hne
    · exact eq_of_le_of_card_ge hle (by rw [h, hZ₀card])
  obtain ⟨hEUA, hUAC, hxE⟩ := hcommUP hUPZ
  rw [← hE] at hEUA hxE
  have hEcard : Nat.card E = 2 := by
    have h := relIndex_mul_card (U ⊓ centralizer (A : Set G)) U
    rw [pow_one] at hUCA
    rw [inf_of_le_left (inf_le_left : U ⊓ centralizer (A : Set G) ≤ U), hUCA, hcard] at h
    rw [hEUA, hUAC]
    omega
  have hEU : E ≤ U := hEUA ▸ inf_le_left
  have hEA : E ≤ A := hEUA ▸ inf_le_right
  have hECA : E ≤ centralizer (A : Set G) := (hEUA.trans hUAC) ▸ inf_le_right
  have hAC : A ⊓ centralizer (U : Set G) = E := by
    refine (eq_of_le_of_card_ge (le_inf hEA (hEU.trans hab)) ?_).symm
    have h := relIndex_mul_card (A ⊓ centralizer (U : Set G)) A
    rw [pow_one] at hACU
    rw [inf_of_le_left (inf_le_left : A ⊓ centralizer (U : Set G) ≤ A), hACU, hAcard] at h
    rw [hEcard]
    omega
  have hEidx : E.relIndex U = 2 := by
    have h := relIndex_mul_card E U
    rw [inf_of_le_left hEU, hEcard, hcard] at h
    omega
  have hEidxA : E.relIndex A = 2 := by
    have h := relIndex_mul_card E A
    rw [inf_of_le_left hEA, hEcard, hAcard] at h
    omega
  have hEZ : E ≤ P ⊓ centralizer (P : Set G) :=
    le_inf (hEU.trans hUP) ((hE ▸ commutator_mono le_rfl hAP).trans (hUPZ ▸ inf_le_right))
  have hQx : CFSG.conjugate Q x = P ⊓ centralizer (A : Set G) := by
    rw [hQ, conjugate_inf, conjugate_centralizer, hxP, hA]
  rw [hQx] at hUQx hACx
  have hQCA : Q ⊓ centralizer (A : Set G) = P ⊓ centralizer ((U ⊔ A : Subgroup G) : Set G) := by
    rw [hQ, centralizer_sup_eq_inf, inf_assoc]
  have hQCAidx : (Q ⊓ centralizer (A : Set G)).relIndex Q = 2 := by
    have h := relIndex_mul_relIndex (Q ⊓ centralizer (A : Set G)) Q P inf_le_left hQP
    have h4 : (Q ⊓ centralizer (A : Set G)).relIndex P = 4 := by
      rw [hQCA, hCidx]
      norm_num
    rw [hQidx, h4] at h
    omega
  have hKL : K ≤ A ⊔ CFSG.conjugate A c := by
    obtain ⟨⟨e, he⟩, he1⟩ := ne_bot_iff_exists_ne_one.mp hE1
    have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
    have heU : e ∈ U := hEU he
    have he'U : c⁻¹ * e * c ∈ U := by
      have := (mem_normalizer_iff.1 (inv_mem hcN) e).1 heU
      rwa [inv_inv] at this
    have he'L : c⁻¹ * e * c ∈ A ⊔ CFSG.conjugate A c := by
      refine (le_sup_right : CFSG.conjugate A c ≤ A ⊔ CFSG.conjugate A c) ?_
      rw [mem_conjugate_iff_conj, show c * (c⁻¹ * e * c) * c⁻¹ = e by group]
      exact hEA he
    have he'E : c⁻¹ * e * c ∉ E := by
      intro h
      have h1 : c⁻¹ * e * c ≠ 1 := by
        intro h1
        apply he1'
        calc e = c * (c⁻¹ * e * c) * c⁻¹ := by group
          _ = 1 := by rw [h1]; group
      have h2 := eq_of_mem_of_card_eq_two hEcard h he h1 he1'
      apply hcfix e heU he1'
      calc c * e * c⁻¹ = c * (c⁻¹ * e * c) * c⁻¹ := by rw [h2]
        _ = e := by group
    have hUL : U ≤ A ⊔ CFSG.conjugate A c := by
      have h := eq_of_le_of_prime_relIndex (le_inf hEU (hEA.trans le_sup_left)) inf_le_left
        (hEidx ▸ Nat.prime_two) fun h => he'E (h (mem_inf.2 ⟨he'U, he'L⟩))
      exact h.ge.trans inf_le_right
    obtain ⟨a, haA, haE⟩ : ∃ a ∈ A, a ∉ E := by
      by_contra h
      push Not at h
      have := card_le_of_le (show A ≤ E from h)
      rw [hAcard, hEcard] at this
      omega
    have hCUa : U ⊓ centralizer ({a} : Set G) = E := by
      have hEle : E ≤ U ⊓ centralizer ({a} : Set G) := by
        refine le_inf hEU fun z hz => ?_
        rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.1 (hECA hz) a haA).symm
      refine le_antisymm ?_ hEle
      by_contra hne
      have h := eq_of_le_of_prime_relIndex hEle inf_le_left (hEidx ▸ Nat.prime_two) hne
      apply haE
      rw [← hAC]
      refine mem_inf.2 ⟨haA, mem_centralizer_iff.2 fun u hu => ?_⟩
      exact mem_centralizer_singleton_iff.1 (mem_inf.1 (h.ge hu)).2
    have hgL : a * (c⁻¹ * a * c) ∈ A ⊔ CFSG.conjugate A c := by
      refine mul_mem ((le_sup_left : A ≤ A ⊔ CFSG.conjugate A c) haA)
        ((le_sup_right : CFSG.conjugate A c ≤ A ⊔ CFSG.conjugate A c) ?_)
      rw [mem_conjugate_iff_conj, show c * (c⁻¹ * a * c) * c⁻¹ = a by group]
      exact haA
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hAexp a haA)
    have hgK : a * (c⁻¹ * a * c) ∈ K := by
      rw [show a * (c⁻¹ * a * c) = (a * c⁻¹ * a⁻¹) * c by rw [hainv]; group]
      exact mul_mem ((mem_normalizer_iff.1 (hPK (hAP haA)) c⁻¹).1 (inv_mem hcK)) hcK
    have hgU : a * (c⁻¹ * a * c) ∉ U := by
      intro hg
      have hca : c⁻¹ * a * c = a * (a * (c⁻¹ * a * c)) := by
        rw [← mul_assoc, hAexp a haA, one_mul]
      have hea : a * e = e * a := mem_centralizer_iff.1 (hECA he) a haA
      have heg : e * (a * (c⁻¹ * a * c)) = (a * (c⁻¹ * a * c)) * e :=
        mem_centralizer_iff.1 (hab hg) e heU
      have h1 : e * (c⁻¹ * a * c) = (c⁻¹ * a * c) * e := by
        calc e * (c⁻¹ * a * c) = e * a * (a * (c⁻¹ * a * c)) := by
              rw [mul_assoc e a, ← hca]
          _ = a * (e * (a * (c⁻¹ * a * c))) := by rw [← hea]; group
          _ = a * ((a * (c⁻¹ * a * c)) * e) := by rw [heg]
          _ = (c⁻¹ * a * c) * e := by rw [← mul_assoc a, ← hca]
      have h2 : (c * e * c⁻¹) * a = a * (c * e * c⁻¹) := by
        calc (c * e * c⁻¹) * a = c * (e * (c⁻¹ * a * c)) * c⁻¹ := by group
          _ = c * ((c⁻¹ * a * c) * e) * c⁻¹ := by rw [h1]
          _ = a * (c * e * c⁻¹) := by group
      have h3 : c * e * c⁻¹ ∈ E := by
        rw [← hCUa]
        exact mem_inf.2 ⟨(mem_normalizer_iff.1 hcN e).1 heU, mem_centralizer_singleton_iff.2 h2⟩
      have h4 : c * e * c⁻¹ ≠ 1 := fun h => he1' (conj_eq_one_iff.1 h)
      exact hcfix e heU he1' (eq_of_mem_of_card_eq_two hEcard h3 he h4 he1')
    have h := eq_of_le_of_prime_relIndex (le_inf hUK hUL) inf_le_left (hUidx ▸ Nat.prime_three)
      fun h => hgU (h (mem_inf.2 ⟨hgK, hgL⟩))
    exact h.ge.trans inf_le_right
  have hUK4 : (U ⊓ centralizer (K : Set G)).relIndex U = 2 ^ 2 := by
    rw [hZ, relIndex_bot_left, hcard]
    norm_num
  obtain ⟨-, -, hCK⟩ := two_conjugate_centralizer_index_extracts_fixed_factor
    (conjugate_eq_self_of_mem_normalizer (hKQ hcK)) hKL (le_inf hUQ (le_centralizer_iff.mp hQCU))
    (m := 2) (by norm_num) hQCAidx hUK4
  have hDA : D ≤ centralizer (A : Set G) :=
    (le_inf hDQ (hD ▸ inf_le_right : D ≤ centralizer (K : Set G))).trans hCK
  have hDUA : D ≤ centralizer ((U ⊔ A : Subgroup G) : Set G) := by
    rw [centralizer_sup_eq_inf]
    exact le_inf hDU hDA
  have hUAD : U ⊔ A ⊔ D = P := by
    refine le_antisymm (sup_le (sup_le hUP hAP) hDP) ?_
    rw [← hAQ, ← hUD]
    exact sup_le (le_sup_right.trans le_sup_left)
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  have hUAmul : ((U ⊔ A : Subgroup G) : Set G) = (U : Set G) * (A : Set G) :=
    coe_mul_of_left_le_normalizer_right U A (hUP.trans hPA)
  have hUAQ : (U ⊔ A) ⊓ Q ≤ U := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := mem_inf.1 hz
    obtain ⟨u, hu, a, ha, rfl⟩ : z ∈ (U : Set G) * (A : Set G) := hUAmul ▸ hz1
    have haC : a ∈ centralizer (U : Set G) := by
      have := mul_mem (inv_mem (hab hu)) (hQCU hz2)
      rwa [inv_mul_cancel_left] at this
    exact mul_mem hu (hEU (hAC ▸ mem_inf.2 ⟨ha, haC⟩))
  have hUADbot : (U ⊔ A) ⊓ D = ⊥ := by
    rw [eq_bot_iff, ← hUDbot]
    exact le_inf ((inf_le_inf_left _ hDQ).trans hUAQ) inf_le_right
  have hnc : ∀ u ∈ U, u ∉ E → ∀ a ∈ A, a ∉ E → u * a ≠ a * u := by
    intro u hu huE a ha haE h
    have hEle : E ≤ A ⊓ centralizer ({u} : Set G) := by
      refine le_inf hEA fun z hz => ?_
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 (hab (hEU hz)) u hu).symm
    have h' := eq_of_le_of_prime_relIndex hEle inf_le_left (hEidxA ▸ Nat.prime_two)
      fun h' => haE (h' (mem_inf.2 ⟨ha, mem_centralizer_singleton_iff.2 h.symm⟩))
    apply huE
    rw [hEUA, hUAC]
    refine mem_inf.2 ⟨hu, mem_centralizer_iff.2 fun b hb => ?_⟩
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 (h'.ge hb)).2
  have hD8 : Nonempty (↥(U ⊔ A) ≃* DihedralGroup 4) := by
    obtain ⟨u, hu, huE⟩ : ∃ u ∈ U, u ∉ E := by
      by_contra h
      push Not at h
      have := card_le_of_le (show U ≤ E from h)
      rw [hcard, hEcard] at this
      omega
    obtain ⟨a, ha, haE⟩ : ∃ a ∈ A, a ∉ E := by
      by_contra h
      push Not at h
      have := card_le_of_le (show A ≤ E from h)
      rw [hAcard, hEcard] at this
      omega
    have hua := hnc u hu huE a ha haE
    have hu2 : u * u = 1 := hexp u hu
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hAexp a ha)
    have hr2 : ¬ (u * a) ^ 2 ^ 1 = 1 := by
      intro h
      apply hua
      rw [pow_one, sq] at h
      rw [eq_inv_of_mul_eq_one_left h, mul_inv_rev, huinv, hainv]
    have hr4 : (u * a) ^ 2 ^ (1 + 1) = 1 := by
      have hr2E : (u * a) ^ 2 ∈ E := by
        rw [hE, show (u * a) ^ 2 = ⁅u, a⁆ by rw [commutatorElement_def, huinv, hainv, sq]; group]
        exact commutator_mem_commutator hu ha
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, sq]
      exact hexp _ (hEU hr2E)
    have hord : orderOf (u * a) = 4 := orderOf_eq_prime_pow hr2 hr4
    have huR : u ∉ zpowers (u * a) := by
      intro h
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
      apply hua
      have hcomm : u * (u * a) = (u * a) * u := by
        have := ((Commute.refl (u * a)).zpow_left k).eq
        rwa [hk] at this
      calc u * a = u * (u * (u * a)) := by rw [← mul_assoc u u, hu2, one_mul]
        _ = u * ((u * a) * u) := by rw [hcomm]
        _ = (u * u) * a * u := by group
        _ = a * u := by rw [hu2, one_mul]
    have hinvr : ∀ y ∈ zpowers (u * a), u * y * u⁻¹ = y⁻¹ := by
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      have h1 : u * (u * a) * u⁻¹ = (u * a)⁻¹ := by
        rw [mul_inv_rev, hainv, huinv, ← mul_assoc u u a, hu2, one_mul]
      rw [← conj_zpow, h1, inv_zpow]
    obtain ⟨e8⟩ := CFSG.Glauberman.Dickson.nonempty_sup_zpowers_mulEquiv_dihedral
      (zpowers (u * a)) inferInstance u huR hu2 hinvr
    have hcardUA : Nat.card (U ⊔ A : Subgroup G) = 8 := by
      have h1 := relIndex_sup_of_le_normalizer (hUP.trans hPA)
      have h2 : A.relIndex U = 2 := by
        rw [← inf_relIndex_right, inf_comm, ← hEUA, hEidx]
      have h3 := relIndex_mul_card A (U ⊔ A)
      rw [inf_of_le_left le_sup_right, h1, h2, hAcard] at h3
      omega
    have hsup : zpowers (u * a) ⊔ zpowers u = U ⊔ A := by
      refine eq_of_le_of_card_ge (sup_le (zpowers_le.2 (mul_mem
        ((le_sup_left : U ≤ U ⊔ A) hu) ((le_sup_right : A ≤ U ⊔ A) ha)))
        (zpowers_le.2 ((le_sup_left : U ≤ U ⊔ A) hu))) ?_
      rw [Nat.card_congr e8.toEquiv, DihedralGroup.nat_card, Nat.card_zpowers, hord, hcardUA]
    rw [Nat.card_zpowers, hord] at e8
    exact ⟨(MulEquiv.subgroupCongr hsup.symm).trans e8⟩
  have hD2 : IsPGroup 2 D := hP.to_le hDP
  have hFQD : (frattini Q).map Q.subtype = (frattini D).map D.subtype := by
    rw [frattini_map_eq_closure (hP.to_le hQP), frattini_map_eq_closure hD2]
    have hcen : U ≤ centralizer ((U ⊔ D : Subgroup G) : Set G) := by
      rw [centralizer_sup_eq_inf]
      exact le_inf hab (le_centralizer_iff.mp hDU)
    have := closure_commPowSet_sup_central (p := 2) hcen fun e he => by
      rw [sq]
      exact hexp e he
    rwa [hUD] at this
  have hFrat' : CFSG.conjugate ((frattini D).map D.subtype) x = (frattini D).map D.subtype := by
    rw [← hFQD]
    exact hFrat
  have hF₀D : (frattini D).map D.subtype ≤ D := map_subtype_le _
  have hF₀sq : ∀ d ∈ D, d * d ∈ (frattini D).map D.subtype := by
    intro d hd
    rw [frattini_map_eq_closure hD2]
    exact subset_closure (Or.inr ⟨d, hd, (sq d).symm⟩)
  have hUDmul : ((U ⊔ D : Subgroup G) : Set G) = (U : Set G) * (D : Set G) :=
    coe_mul_of_left_le_normalizer_right U D
      ((le_centralizer_iff.mp hDU).trans (centralizer_le_normalizer _))
  have hQsq : ∀ q ∈ Q, q * q ∈ (frattini D).map D.subtype := by
    intro q hq
    rw [← hUD] at hq
    obtain ⟨u, hu, d, hd, rfl⟩ : q ∈ (U : Set G) * (D : Set G) := hUDmul ▸ hq
    have hud : u * d = d * u := mem_centralizer_iff.1 (hDU hd) u hu
    have : u * d * (u * d) = (u * u) * (d * d) := by
      calc u * d * (u * d) = u * (d * u) * d := by group
        _ = u * (u * d) * d := by rw [hud]
        _ = (u * u) * (d * d) := by group
    rw [this, hexp u hu, one_mul]
    exact hF₀sq d hd
  have hPmul : (P : Set G) = ((U ⊔ A : Subgroup G) : Set G) * (D : Set G) := by
    rw [← hUAD]
    exact coe_mul_of_left_le_normalizer_right (U ⊔ A) D
      ((le_centralizer_iff.mp hDUA).trans (centralizer_le_normalizer _))
  have hkey : ∀ z ∈ P, z * z ∈ (frattini D).map D.subtype →
      z ∈ Q ∨ z ∈ P ⊓ centralizer (A : Set G) := by
    intro z hz hzz
    obtain ⟨w, hw, d, hd, rfl⟩ : z ∈ ((U ⊔ A : Subgroup G) : Set G) * (D : Set G) := hPmul ▸ hz
    have hwd : w * d = d * w := mem_centralizer_iff.1 (hDUA hd) w hw
    have hww : w * w = 1 := by
      have h1 : w * w ∈ D := by
        have : w * d * (w * d) * (d * d)⁻¹ = w * w := by
          calc w * d * (w * d) * (d * d)⁻¹ = w * (d * w) * d * (d * d)⁻¹ := by group
            _ = w * (w * d) * d * (d * d)⁻¹ := by rw [hwd]
            _ = w * w := by group
        rw [← this]
        exact mul_mem (hF₀D hzz) (inv_mem (mul_mem hd hd))
      have : w * w ∈ (U ⊔ A) ⊓ D := mem_inf.2 ⟨mul_mem hw hw, h1⟩
      rwa [hUADbot, mem_bot] at this
    obtain ⟨u, hu, a, ha, rfl⟩ : w ∈ (U : Set G) * (A : Set G) := hUAmul ▸ hw
    by_cases haE : a ∈ E
    · left
      rw [← hUD]
      exact mul_mem ((le_sup_left : U ≤ U ⊔ D) (mul_mem hu (hEU haE)))
        ((le_sup_right : D ≤ U ⊔ D) hd)
    · by_cases huE : u ∈ E
      · right
        have hAPC : A ≤ P ⊓ centralizer (A : Set G) := le_inf hAP hAab
        exact mul_mem (mul_mem (hAPC (hEA huE)) (hAPC ha)) (le_inf hDP hDA hd)
      · exfalso
        have hww' : u * a * (u * a) = 1 := hww
        have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hexp u hu)
        have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hAexp a ha)
        apply hnc u hu huE a ha haE
        rw [eq_inv_of_mul_eq_one_left hww', mul_inv_rev, huinv, hainv]
  have hcard_conj : ∀ (H : Subgroup G) (g : G), Nat.card (CFSG.conjugate H g) = Nat.card H :=
    fun H g => card_map_of_injective (MulAut.conj g⁻¹).injective
  have hQne : CFSG.conjugate Q x ≠ Q := by
    intro h
    apply hE1
    rw [hE, commutator_eq_bot_iff_le_centralizer]
    exact hUQ.trans (h.ge.trans (hQx.le.trans inf_le_right))
  have hxF : x ∈ normalizer (((frattini D).map D.subtype : Subgroup G) : Set G) :=
    mem_normalizer_of_conjugate_eq hFrat'
  have hxxQ : CFSG.conjugate Q (x * x) = Q := by
    have hxxP : x * x ∈ normalizer (P : Set G) := mul_mem hx hx
    have hxxF := mul_mem hxF hxF
    rcases le_or_le_of_forall_mem_or (H := CFSG.conjugate Q (x * x)) (K₁ := Q)
        (K₂ := P ⊓ centralizer (A : Set G)) (fun z hz => by
      rw [mem_conjugate_iff_conj] at hz
      refine hkey z ?_ ?_
      · have := (mem_normalizer_iff.1 (inv_mem hxxP) _).1 (hQP hz)
        rwa [show (x * x)⁻¹ * (x * x * z * (x * x)⁻¹) * (x * x)⁻¹⁻¹ = z by group] at this
      · have := (mem_normalizer_iff.1 (inv_mem hxxF) _).1 (hQsq _ hz)
        rwa [show (x * x)⁻¹ * (x * x * z * (x * x)⁻¹ * (x * x * z * (x * x)⁻¹)) *
          (x * x)⁻¹⁻¹ = z * z by group] at this) with h | h
    · exact eq_of_le_of_card_ge h (by rw [hcard_conj])
    · exfalso
      have h' : CFSG.conjugate Q (x * x) = CFSG.conjugate Q x :=
        eq_of_le_of_card_ge (h.trans hQx.ge) (by rw [hcard_conj, hcard_conj])
      rw [← ReversalOvergroup.conjugate_conjugate_eq] at h'
      exact hQne (map_injective (MulAut.conj x⁻¹).injective h')
  have hEven : Even (orderOf x) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (Nat.coprime_two_left.2 hodd)
    apply hQne
    have hxx : x * x ∈ normalizer (Q : Set G) := mem_normalizer_of_conjugate_eq hxxQ
    have : x ∈ normalizer (Q : Set G) := by
      rw [← hm, sq]
      exact pow_mem hxx m
    exact conjugate_eq_self_of_mem_normalizer this
  refine ⟨hAP, hPA, hEUA, hUAC, ?_, hEcard, hEZ, conjugate_eq_self_of_mem_normalizer hxE, hAQ,
    hUQx, hUC, hACx.symm, hQCAidx, hDA, hUAD, hUADbot, hDUA, hD8, hFrat', hEven⟩
  rw [← hUAC, ← hEUA, hAC]

end Reversal

end ReversalPair

open ReversalPair

variable {G : Type} [Group G] [Finite G]

theorem actual_A3_reversal_pair_identities_and_odd_commutation {K P U Q D : Subgroup G}
    (hK : IsShort2 K) (h3 : Nat.card (K ⧸ CFSG.pCore 2 K) = 3) (hP : IsPGroup 2 P)
    (hPK : P ≤ normalizer (K : Set G)) (hU : U = blockQ K) (hUP : U ≤ P)
    (hQ : Q = P ⊓ centralizer (U : Set G)) (hD : D = P ⊓ centralizer (K : Set G)) :
    (Nonempty (K ≃* alternatingGroup (Fin 4)) ∧ IsKleinFour U ∧
      K ⊓ centralizer (U : Set G) = U ∧ Q ≤ K ⊔ P ∧ K ⊔ P ≤ normalizer (Q : Set G) ∧
      ⁅Q, K⁆ ≤ U ∧ U ⊔ D = Q ∧ U ⊓ D = ⊥ ∧ D ≤ centralizer (U : Set G)) ∧
    (∀ x ∈ normalizer (P : Set G), ∀ A E : Subgroup G, A = CFSG.conjugate U x →
      E = ⁅U, A⁆ → E ≠ ⊥ →
      A ≤ P ∧ P ≤ normalizer (A : Set G) ∧
        E = U ⊓ A ∧ U ⊓ A = U ⊓ centralizer (A : Set G) ∧
        U ⊓ centralizer (A : Set G) = A ⊓ centralizer (U : Set G) ∧ Nat.card E = 2 ∧
        E ≤ P ⊓ centralizer (P : Set G) ∧ CFSG.conjugate E x = E ∧
        A ⊔ Q = P ∧ U ⊔ (P ⊓ centralizer (A : Set G)) = P ∧
        U ⊔ (P ⊓ centralizer ((U ⊔ A : Subgroup G) : Set G)) = Q ∧
        P ⊓ centralizer (A : Set G) = A ⊔ (P ⊓ centralizer ((U ⊔ A : Subgroup G) : Set G)) ∧
        (Q ⊓ centralizer (A : Set G)).relIndex Q = 2 ∧ D ≤ centralizer (A : Set G) ∧
        U ⊔ A ⊔ D = P ∧ (U ⊔ A) ⊓ D = ⊥ ∧ D ≤ centralizer ((U ⊔ A : Subgroup G) : Set G) ∧
        Nonempty (↥(U ⊔ A) ≃* DihedralGroup 4) ∧
        CFSG.conjugate ((frattini D).map D.subtype) x = (frattini D).map D.subtype ∧
        Even (orderOf x)) ∧
    ∀ y ∈ normalizer (P : Set G), Odd (orderOf y) → ⁅U, CFSG.conjugate U y⁆ = ⊥ := by
  refine ⟨block_structure hK h3 hPK hU hUP hQ hD,
    fun x hx A E hA hE hE1 => reversal_pair hK h3 hP hPK hU hUP hQ hD hx hA hE hE1,
    fun y hy hodd => ?_⟩
  by_contra h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, heven⟩ :=
    reversal_pair hK h3 hP hPK hU hUP hQ hD hy rfl rfl h
  exact Nat.not_even_iff_odd.2 hodd heven

end CFSG.Quasithin.SteinbergBS
