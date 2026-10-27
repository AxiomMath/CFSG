module

public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Xi
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1543
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1542Three
public import CFSG.Quasithin.Background.G2
import CFSG.Quasithin.Background.OrderingMax

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.L3213

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Ch1Sec3 CFSG.LieType.BorelTits
open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def vOf (T X : Subgroup G) : Subgroup G :=
  ⁅omegaOneCenterOf (pCoreOf 2 (X ⊔ T)), X⁆

theorem mem_normalizer_frattini {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer ((⁅X, X⁆ ⊔ pCoreOf 2 X : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨commutator_le_normalizer hg hg, normalizer_le_normalizer_pCoreOf 2 X hg⟩

section Finite

variable [Finite G] {T X : Subgroup G}

omit [Finite G] in
theorem sup_le_normalizer_of_isXi (hX : IsXi T X) :
    X ⊔ T ≤ Subgroup.normalizer (X : Set G) :=
  sup_le Subgroup.le_normalizer hX.2.1

theorem pCoreOf_le_pCoreOf_sup (hX : IsXi T X) : pCoreOf 2 X ≤ pCoreOf 2 (X ⊔ T) :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 X).trans le_sup_left)
    ((sup_le_normalizer_of_isXi hX).trans (normalizer_le_normalizer_pCoreOf 2 X))
    (pCoreOf_isPGroup 2 X)

omit [Finite G] in
theorem sup_le_normalizer_omegaOneCenterOf (T X : Subgroup G) :
    X ⊔ T ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (X ⊔ T)) : Set G) :=
  (le_normalizer_pCoreOf 2 (X ⊔ T)).trans (normalizer_le_normalizer_omegaOneCenterOf _)

omit [Finite G] in
theorem vOf_le_omegaOneCenterOf (T X : Subgroup G) :
    vOf T X ≤ omegaOneCenterOf (pCoreOf 2 (X ⊔ T)) :=
  commutator_le_left_of_le_normalizer (le_sup_left.trans (sup_le_normalizer_omegaOneCenterOf T X))

omit [Finite G] in
theorem vOf_le (hX : IsXi T X) : vOf T X ≤ X := by
  rw [vOf, Subgroup.commutator_comm]
  exact commutator_le_left_of_le_normalizer ((omegaOneCenterOf_le _).trans
    ((pCoreOf_le 2 _).trans (sup_le_normalizer_of_isXi hX)))

omit [Finite G] in
theorem sup_le_normalizer_vOf (hX : IsXi T X) :
    X ⊔ T ≤ Subgroup.normalizer (vOf T X : Set G) := fun _ hg =>
  A4.mem_normalizer_commutator (sup_le_normalizer_omegaOneCenterOf T X hg)
    (sup_le_normalizer_of_isXi hX hg)

omit [Finite G] in
theorem isElemAbelian_vOf (T X : Subgroup G) : IsElemAbelian 2 (vOf T X) := by
  have hU := vOf_le_omegaOneCenterOf T X
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun v hv => sq_eq_one_of_mem_omegaOneCenterOf (hU hv)⟩
  exact (mem_centralizer_of_mem_omegaOneCenterOf (hU a.2)
    (omegaOneCenterOf_le _ (hU b.2))).symm

omit [Finite G] in
theorem pCoreOf_sup_le_centralizer_vOf (T X : Subgroup G) :
    pCoreOf 2 (X ⊔ T) ≤ Subgroup.centralizer (vOf T X : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (mem_centralizer_of_mem_omegaOneCenterOf (vOf_le_omegaOneCenterOf T X hv) hr).symm

theorem pCoreOf_le_centralizer_vOf (hX : IsXi T X) :
    pCoreOf 2 X ≤ Subgroup.centralizer (vOf T X : Set G) :=
  (pCoreOf_le_pCoreOf_sup hX).trans (pCoreOf_sup_le_centralizer_vOf T X)

theorem vOf_le_pCoreOf_normalizer (hX : IsXi T X) :
    vOf T X ≤ pCoreOf 2 (Subgroup.normalizer (X : Set G)) := by
  have hV2 : IsPGroup 2 (vOf T X) :=
    (pCoreOf_isPGroup 2 (X ⊔ T)).to_le ((vOf_le_omegaOneCenterOf T X).trans (omegaOneCenterOf_le _))
  have h1 : vOf T X ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 (vOf_le hX) (le_sup_left.trans (sup_le_normalizer_vOf hX)) hV2
  exact h1.trans (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 X).trans Subgroup.le_normalizer)
    (normalizer_le_normalizer_pCoreOf 2 X) (pCoreOf_isPGroup 2 X))

theorem vOf_ne_bot {G : Type} [Group G] [Finite G] {T X M : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (hX : IsXi T X) (hM : IsUniqueM (X ⊔ T) M) :
    vOf T X ≠ ⊥ := by
  set T' : Sylow 2 G := hyp.sylow.1.toSylow hyp.sylow.2 with hT'
  have hT'c : (T' : Subgroup G) = T := IsPGroup.toSylow_coe _ _
  have hXTc : CharTwo (X ⊔ T) := charTwo_of_inH hyp.qtke.2.1 T' (hT'c ▸ ⟨le_sup_right, hX.2.2.1⟩)
  have hZ := quasithinOmegaOneCenter_le_omegaOneCenterOf T' (hT'c ▸ le_sup_right) hXTc
  rw [hT'c] at hZ
  have hZX := commutator_ne_bot_of_isUniqueM hyp hM
  intro h
  exact hZX (le_bot_iff.mp (h ▸ Subgroup.commutator_mono hZ le_rfl))

theorem inf_centralizer_vOf_le (hX : IsXi T X) (hsolv : Group.IsSolvable X) (hVne : vOf T X ≠ ⊥) :
    X ⊓ Subgroup.centralizer (vOf T X : Set G) ≤ ⁅X, X⁆ ⊔ pCoreOf 2 X := by
  obtain ⟨-, -, -, p, hp, hp2, hpow, -, hirr⟩ := id hX
  set V := vOf T X with hVdef
  set U := omegaOneCenterOf (pCoreOf 2 (X ⊔ T)) with hUdef
  set N := X ⊓ Subgroup.centralizer (V : Set G) with hNdef
  have hXTV := sup_le_normalizer_vOf hX
  have hNn : X ⊔ T ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
    A4.mem_normalizer_inf (sup_le_normalizer_of_isXi hX hg)
      (A4.mem_normalizer_centralizer (hXTV hg))
  have hQN : pCoreOf 2 X ≤ N := le_inf (pCoreOf_le 2 X) (pCoreOf_le_centralizer_vOf hX)
  have hT : T ≤ Subgroup.normalizer ((N ⊔ (⁅X, X⁆ ⊔ pCoreOf 2 X) : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨hNn (le_sup_right (a := X) ht), mem_normalizer_frattini (hX.2.1 ht)⟩
  rcases hirr _ le_sup_right (sup_le inf_le_left (sup_le (commutator_le_self X)
    (pCoreOf_le 2 X))) hT with h | h
  · exact le_sup_left.trans h.le
  exfalso
  have hle : X ≤ N ⊔ ⁅X, X⁆ := by
    calc X = N ⊔ (⁅X, X⁆ ⊔ pCoreOf 2 X) := h.symm
      _ ≤ N ⊔ ⁅X, X⁆ := sup_le le_sup_left (sup_le le_sup_right (hQN.trans le_sup_left))
  have hXN : X ≤ N := le_of_le_sup_commutator (le_sup_left.trans hNn) hsolv hle
  apply hVne
  rw [eq_bot_iff, hVdef, vOf, Subgroup.commutator_le]
  intro u hu x hx
  rw [Subgroup.mem_bot]
  set c := x * u * x⁻¹ * u⁻¹ with hc
  have hcV : c ∈ V := by
    have := Subgroup.commutator_mem_commutator hx hu
    rwa [Subgroup.commutator_comm, commutatorElement_def] at this
  have hxc : x * c * x⁻¹ = c := by
    rw [← Subgroup.mem_centralizer_iff.mp (hXN hx).2 c hcV, mul_inv_cancel_right]
  have hxu : x * u * x⁻¹ = c * u := by rw [hc]; group
  have hxpu : x ^ p * u * (x ^ p)⁻¹ = u := by
    rw [mem_centralizer_of_mem_omegaOneCenterOf hu (pCoreOf_le_pCoreOf_sup hX (hpow x hx)),
      mul_inv_cancel_right]
  have hc2 : c ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenterOf (vOf_le_omegaOneCenterOf T X hcV)
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hc1 : c = 1 := eq_one_of_conj_coprime hcop hxpu hxu hxc hc2
  rw [commutatorElement_def]
  have : x * u * x⁻¹ = u := by rw [hxu, hc1, one_mul]
  calc u * x * u⁻¹ * x⁻¹ = u * (x * u * x⁻¹)⁻¹ := by group
    _ = 1 := by rw [this, mul_inv_cancel]

end Finite

end CFSG.Quasithin.EmptyFaithfulMultiple.L3213
