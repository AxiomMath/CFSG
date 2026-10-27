module

public import CFSG.Quasithin.Vol2.Ch3Sec3D8D8E4
public import CFSG.Quasithin.Vol2.Ch3Sec3A6Cocycle
public import CFSG.Quasithin.Vol2.Ch3Sec3Close

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

@[expose] def Step3_3_31S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsAltBlockType L 6 → T ≤ Subgroup.normalizer (L : Set G) → tC L T ≠ ⊥ →
    ∀ d ∈ D, d ∉ M → ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T →
      (qL L T).relIndex (qL L T ⊔ CFSG.conjugate (vPlus L T) d) = 2 ∧
      d ∈ Subgroup.normalizer ((qL L T ⊔ CFSG.conjugate (vPlus L T) d : Subgroup G) : Set G) ∧
      CFSG.conjugate (vPlus L T) d ≤ Subgroup.centralizer (tC L T : Set G) ∧
      qL L T = vPlus L T ⊔
        (qL L T ⊓ Subgroup.centralizer (CFSG.conjugate (vPlus L T) d : Set G)) ∧
      T = T ⊓ L ⊔ qL L T ⊔ CFSG.conjugate (vPlus L T) d ∧
      Nat.card ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) = 2

@[expose] def Step3_3_31E4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsAltBlockType L 6 → T ≤ Subgroup.normalizer (L : Set G) → tC L T ≠ ⊥ →
    ∀ d ∈ D, d ∉ M → ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T →
      frattini ↥(qL L T) ≠ ⊥ → Nat.card ↥(tC L T) = 4 →
      Nonempty (↥(qL L T ⊔ CFSG.conjugate (vPlus L T) d) ≃* D8D8E4)

variable {G : Type} [Group G] [Finite G]

namespace Lem3331

theorem isMaxElemAbelian_of_relIndex_two {S Q : Subgroup G} (hQS : Q ≤ S)
    (hQ : IsElemAbelian 2 Q) (hidx : Q.relIndex S = 2)
    (hC : S ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) :
    IsMaxElemAbelian S Q ∧ ∀ A A' : Subgroup G, IsMaxElemAbelian S A → IsMaxElemAbelian S A' →
      A ≠ Q → A' ≠ Q → A = A' := by
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => by
    have := hQ.1
    exact setLike_mul_comm ha hb
  have hcoset : ∀ a ∈ S, a ∉ Q → ∀ x ∈ S, x ∉ Q → a⁻¹ * x ∈ Q := by
    intro a ha haQ x hx hxQ
    have h2 : (Q.subgroupOf S).index = 2 := hidx
    have h3 := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨a, ha⟩ : ↥S)⁻¹)
      (b := ⟨x, hx⟩)).mpr (iff_of_false (fun h => haQ (by
        have := Subgroup.mem_subgroupOf.mp h
        simpa using this)) (fun h => hxQ (Subgroup.mem_subgroupOf.mp h)))
    exact Subgroup.mem_subgroupOf.mp h3
  have hcent : ∀ a ∈ S, a ∉ Q →
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({a} : Set G)) * 2 ≤ Nat.card ↥Q := by
    intro a ha haQ
    have hne : Q ⊓ Subgroup.centralizer ({a} : Set G) ≠ Q := by
      intro heq
      apply haQ
      refine hC ⟨ha, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      have hq' : q ∈ Q ⊓ Subgroup.centralizer ({a} : Set G) := by
        rw [heq]
        exact hq
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hq').2
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (inf_le_left :
      Q ⊓ Subgroup.centralizer ({a} : Set G) ≤ Q)
    have hpos : 0 < Nat.card ↥Q := Nat.card_pos
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hne (Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hk, mul_one])))
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    rw [hk]
    exact Nat.mul_le_mul_left _ (by omega)
  have hidxA : ∀ A : Subgroup G, A ≤ S → Nat.card ↥A ≤ 2 * Nat.card ↥(Q ⊓ A) := by
    intro A hAS
    have h1 := Subgroup.relIndex_mul_card (H := Q) (K := A)
    have h2 : Q.relIndex A ≤ Q.relIndex S :=
      Subgroup.relIndex_le_of_le_right hAS (by rw [hidx]; norm_num)
    rw [hidx] at h2
    rw [← h1]
    exact Nat.mul_le_mul_right _ h2
  have hinf : ∀ A : Subgroup G, IsElemAbelian 2 A → ∀ a ∈ A,
      Q ⊓ A ≤ Q ⊓ Subgroup.centralizer ({a} : Set G) := by
    intro A hA a ha x hx
    refine ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := hA.1
    exact setLike_mul_comm hx.2 ha
  have hbound : ∀ A : Subgroup G, A ≤ S → IsElemAbelian 2 A → Nat.card ↥A ≤ Nat.card ↥Q := by
    intro A hAS hA
    by_cases hAQ : A ≤ Q
    · exact Subgroup.card_le_of_le hAQ
    · obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp hAQ
      have h1 := hidxA A hAS
      have h2 := Subgroup.card_le_of_le (hinf A hA a haA)
      have h3 := hcent a (hAS haA) haQ
      omega
  have hQmax : IsMaxElemAbelian S Q := ⟨hQS, hQ, hbound⟩
  refine ⟨hQmax, fun A A' hA hA' hAQ hA'Q => ?_⟩
  have hcard : ∀ A : Subgroup G, IsMaxElemAbelian S A → Nat.card ↥A = Nat.card ↥Q := fun A hA =>
    le_antisymm (hbound A hA.1 hA.2.1) (hA.2.2 Q hQS hQ)
  have hout : ∀ A : Subgroup G, IsMaxElemAbelian S A → A ≠ Q → ¬ A ≤ Q := fun A hA hne hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (hcard A hA).ge)
  have hmeet : ∀ A : Subgroup G, IsMaxElemAbelian S A → ∀ a ∈ A, a ∉ Q →
      Q ⊓ A = Q ⊓ Subgroup.centralizer ({a} : Set G) := by
    intro A hA a haA haQ
    have h1 := hidxA A hA.1
    have h3 := hcent a (hA.1 haA) haQ
    have h4 := hcard A hA
    refine Subgroup.eq_of_le_of_card_ge (hinf A hA.2.1 a haA) ?_
    omega
  obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp (hout A hA hAQ)
  obtain ⟨a', ha'A, ha'Q⟩ := Set.not_subset.mp (hout A' hA' hA'Q)
  have hmA := hmeet A hA a haA haQ
  have hmA' := hmeet A' hA' a' ha'A ha'Q
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hA.2.1.2 a haA
  have hq₀ := hcoset a (hA.1 haA) haQ a' (hA'.1 ha'A) ha'Q
  have hCC : ∀ x ∈ Q, x * a' = a' * x → x * a = a * x := by
    intro x hx hxa'
    have hc := hQab x hx _ hq₀
    have h1 : x * a * (a⁻¹ * a') = a * x * (a⁻¹ * a') := by
      calc x * a * (a⁻¹ * a') = x * a' := by group
        _ = a' * x := hxa'
        _ = a * ((a⁻¹ * a') * x) := by group
        _ = a * (x * (a⁻¹ * a')) := by rw [hc]
        _ = a * x * (a⁻¹ * a') := by group
    exact mul_right_cancel h1
  have hle : A' ≤ A := by
    intro x hxA'
    by_cases hxQ : x ∈ Q
    · have h1 : x ∈ Q ⊓ A' := ⟨hxQ, hxA'⟩
      rw [hmA'] at h1
      have h2 : x ∈ Q ⊓ A := by
        rw [hmA]
        refine ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        exact hCC x hxQ (Subgroup.mem_centralizer_singleton_iff.mp h1.2)
      exact h2.2
    · have hq := hcoset a (hA.1 haA) haQ x (hA'.1 hxA') hxQ
      have hx2 : x * x = 1 := by rw [← pow_two]; exact hA'.2.1.2 x hxA'
      have hq2 : (a⁻¹ * x) * (a⁻¹ * x) = 1 := by rw [← pow_two]; exact hQ.2 _ hq
      have hcomm : (a⁻¹ * x) * a = a * (a⁻¹ * x) := by
        have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
        set q := a⁻¹ * x with hqdef
        have hx' : x = a * q := by rw [hqdef]; group
        rw [hx'] at hx2
        have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq2
        have h4 : a * q * a * q = 1 := by
          rw [show a * q * a * q = a * q * (a * q) by group]
          exact hx2
        have h5 : a * q * a = q := by
          calc a * q * a = a * q * a * q * q⁻¹ := by group
            _ = q := by rw [h4, one_mul, hqi]
        calc q * a = a⁻¹ * (a * q * a) := by group
          _ = a * q := by rw [h5, hai]
      have h1 : a⁻¹ * x ∈ Q ⊓ Subgroup.centralizer ({a} : Set G) :=
        ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
      rw [← hmA] at h1
      have h2 : x = a * (a⁻¹ * x) := by group
      rw [h2]
      exact A.mul_mem haA h1.2
  exact (Subgroup.eq_of_le_of_card_ge hle ((hcard A hA).trans (hcard A' hA').symm).le).symm

omit [Finite G] in
theorem mem_normalizer_of_odd_of_unique {S Q : Subgroup G} {d : G} (hQ : IsMaxElemAbelian S Q)
    (huniq : ∀ A A' : Subgroup G, IsMaxElemAbelian S A → IsMaxElemAbelian S A' →
      A ≠ Q → A' ≠ Q → A = A')
    (hdS : d ∈ Subgroup.normalizer (S : Set G)) (hodd : Odd (orderOf d)) :
    d ∈ Subgroup.normalizer (Q : Set G) := by
  have hmax : ∀ g : G, g ∈ Subgroup.normalizer (S : Set G) →
      IsMaxElemAbelian S (Q.map (MulAut.conj g).toMonoidHom) := fun g hg => by
    have := (isMaxElemAbelian_map_mulEquiv (MulAut.conj g)).mpr hQ
    rwa [A38.map_conj_eq_iff.mpr hg] at this
  by_contra hdQ
  have hQ1 : Q.map (MulAut.conj d).toMonoidHom ≠ Q := fun h => hdQ (A38.map_conj_eq_iff.mp h)
  have hQ2 : Q.map (MulAut.conj (d ^ 2)).toMonoidHom = Q := by
    by_contra hne
    have h1 := huniq _ _ (hmax d hdS) (hmax (d ^ 2) (Subgroup.pow_mem _ hdS 2)) hQ1 hne
    apply hQ1
    have h2 := congrArg (fun X : Subgroup G => X.map (MulAut.conj d⁻¹).toMonoidHom) h1
    simp only [map_conj_map_conj] at h2
    rw [inv_mul_cancel, map_conj_one, show d⁻¹ * d ^ 2 = d by group] at h2
    exact h2.symm
  exact hdQ ((Subgroup.zpowers_le.mpr (A38.map_conj_eq_iff.mp hQ2)) (mem_zpowers_sq_of_odd hodd))

omit [Finite G] in
theorem isElemAbelian_of_sq_eq_one {E : Subgroup G} (h : ∀ x ∈ E, x ^ 2 = 1) :
    IsElemAbelian 2 E := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, h⟩
  have hinv : ∀ w : G, w ^ 2 = 1 → w⁻¹ = w := fun w hw =>
    inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hw)
  change (x : G) * y = y * x
  calc (x : G) * y = ((x : G) * y)⁻¹ := (hinv _ (h _ (E.mul_mem x.2 y.2))).symm
    _ = (y : G)⁻¹ * (x : G)⁻¹ := mul_inv_rev _ _
    _ = y * x := by rw [hinv _ (h _ y.2), hinv _ (h _ x.2)]

theorem sq_mem_of_frattini_le {Q C : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hF : (frattini ↥Q).map Q.subtype ≤ C) {x : G} (hx : x ∈ Q) : x ^ 2 ∈ C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥Q) := ⟨hQ⟩
  have h1 : (⟨x, hx⟩ : ↥Q) ^ 2 ∈ frattini ↥Q := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
    exact Subgroup.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)
  exact hF ⟨_, h1, by simp⟩

theorem exists_mem_centralizer_of_normal {T U : Subgroup G} (hT : IsPGroup 2 ↥T) (hUT : U ≤ T)
    (hUn : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    ∃ x ∈ U, x ≠ 1 ∧ x ∈ Subgroup.centralizer (T : Set G) := by
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy.1, fun h => hy1 (Subtype.ext (Subtype.ext h)),
    Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)

theorem card_le_sq_of_centralizes {C : Subgroup G} (hCe : IsElemAbelian 2 C) {u : G}
    (huN : u ∈ Subgroup.normalizer (C : Set G)) (hu2 : ∀ c ∈ C, u ^ 2 * c = c * u ^ 2) :
    Nat.card ↥C ≤ Nat.card ↥(C ⊓ Subgroup.centralizer ({u} : Set G)) ^ 2 := by
  have hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb => by
    have := hCe.1
    exact setLike_mul_comm ha hb
  have hconj : ∀ c ∈ C, u * c * u⁻¹ ∈ C := fun c hc =>
    (Subgroup.mem_normalizer_iff.mp huN c).mp hc
  have hinv : ∀ w ∈ C, w⁻¹ = w := fun w hw =>
    inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hCe.2 w hw)
  let ψ : ↥C →* ↥C :=
    { toFun := fun c => ⟨(c : G)⁻¹ * (u * c * u⁻¹), C.mul_mem (C.inv_mem c.2) (hconj c c.2)⟩
      map_one' := Subtype.ext (by
        change (1 : G)⁻¹ * (u * 1 * u⁻¹) = 1
        group)
      map_mul' := fun a b => Subtype.ext (by
        change ((a : G) * b)⁻¹ * (u * ((a : G) * b) * u⁻¹) =
          (a : G)⁻¹ * (u * a * u⁻¹) * ((b : G)⁻¹ * (u * b * u⁻¹))
        have h1 := hCab _ (C.inv_mem b.2) _ (C.mul_mem (C.inv_mem a.2) (hconj a a.2))
        calc ((a : G) * b)⁻¹ * (u * ((a : G) * b) * u⁻¹)
            = (b : G)⁻¹ * ((a : G)⁻¹ * (u * a * u⁻¹)) * (u * b * u⁻¹) := by group
          _ = (a : G)⁻¹ * (u * a * u⁻¹) * (b : G)⁻¹ * (u * b * u⁻¹) := by rw [h1]
          _ = (a : G)⁻¹ * (u * a * u⁻¹) * ((b : G)⁻¹ * (u * b * u⁻¹)) := by group) }
  set K := C ⊓ Subgroup.centralizer ({u} : Set G) with hK
  have hker : ψ.ker.map C.subtype = K := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype, hK, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      have h' : (c : G)⁻¹ * (u * c * u⁻¹) = 1 := congrArg Subtype.val hc
      have h2 : u * c * u⁻¹ = c := by
        calc u * c * u⁻¹ = c * ((c : G)⁻¹ * (u * c * u⁻¹)) := by group
          _ = c := by rw [h', mul_one]
      refine ⟨c.2, ?_⟩
      calc (c : G) * u = u * c * u⁻¹ * u := by rw [h2]
        _ = u * c := by group
    · rintro ⟨hxC, hxu⟩
      refine ⟨⟨x, hxC⟩, Subtype.ext ?_, rfl⟩
      change x⁻¹ * (u * x * u⁻¹) = 1
      rw [← hxu]
      group
  have hrange : ψ.range.map C.subtype ≤ K := by
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨(ψ c).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    change (c : G)⁻¹ * (u * c * u⁻¹) * u = u * ((c : G)⁻¹ * (u * c * u⁻¹))
    have hc'C : u * (c : G) * u⁻¹ ∈ C := hconj c c.2
    have hA : u⁻¹ * (c : G) * u = u * c * u⁻¹ := by
      have h1 : (c : G) * u ^ 2 = u ^ 2 * c := (hu2 c c.2).symm
      calc u⁻¹ * (c : G) * u = u⁻¹ * ((c : G) * u ^ 2) * u⁻¹ := by group
        _ = u⁻¹ * (u ^ 2 * c) * u⁻¹ := by rw [h1]
        _ = u * c * u⁻¹ := by group
    have hcomm' := hCab _ c.2 _ hc'C
    calc (c : G)⁻¹ * (u * c * u⁻¹) * u
        = u * (u⁻¹ * (c : G) * u)⁻¹ * (u⁻¹ * (u * c * u⁻¹) * u) := by group
      _ = u * (u * c * u⁻¹)⁻¹ * c := by rw [hA]; group
      _ = u * (u * c * u⁻¹) * c := by rw [hinv _ hc'C]
      _ = u * ((c : G) * (u * c * u⁻¹)) := by rw [mul_assoc, ← hcomm']
      _ = u * ((c : G)⁻¹ * (u * c * u⁻¹)) := by rw [hinv _ c.2]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at h1
  have h2 : Nat.card ↥ψ.ker = Nat.card ↥K := by
    rw [← hker, Subgroup.card_map_of_injective C.subtype_injective]
  have h3 : Nat.card ↥ψ.range ≤ Nat.card ↥K := by
    rw [← Subgroup.card_map_of_injective C.subtype_injective]
    exact Subgroup.card_le_of_le hrange
  rw [h1, h2, sq]
  exact Nat.mul_le_mul_right _ h3

end Lem3331

open Lem3331

variable {T M L D : Subgroup G}

namespace Hyp331

theorem relIndex_qL_le_two
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hA6 : IsAltBlockType L 6) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    (blockU L ⊔ tC L T).relIndex (qL L T) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hshort := hA6.1
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hFQ := h.frattini_qL_le_tC h38 h39 hshort hTL
  have hQQ : ∀ a ∈ qL L T, ∀ b ∈ qL L T, ⁅a, b⁆ ∈ Subgroup.centralizer (L : Set G) := by
    intro a ha b hb
    have : Fact (IsPGroup 2 ↥(qL L T)) := ⟨CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _⟩
    have hF := CFSG.frattini_eq_closure_commutator_union_powers (R := ↥(qL L T)) (p := 2)
    have h1 : ⁅(⟨a, ha⟩ : ↥(qL L T)), ⟨b, hb⟩⁆ ∈ frattini ↥(qL L T) :=
      hF ▸ Subgroup.subset_closure (Or.inl (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top _) (Subgroup.mem_top _)))
    exact (Subgroup.mem_inf.mp (hFQ ⟨_, h1, rfl⟩)).2
  have hQU : ∀ q ∈ qL L T, ∀ ℓ ∈ L, ⁅q, ℓ⁆ ∈ blockU L := fun q hq ℓ hℓ =>
    commutator_qL_le_blockU hshort hTL (Subgroup.commutator_mem_commutator hq hℓ)
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hCQ : tC L T ≤ qL L T := h.tC_le_qL h38 h39 hTL
  have hC : qL L T ⊓ Subgroup.centralizer (L : Set G) = tC L T :=
    le_antisymm (fun x hx => ⟨hQT hx.1, hx.2⟩) (fun x hx => ⟨hCQ hx, hx.2⟩)
  have h2 := A6Block.relIndex_le_two hA6 (hQT.trans hTL) hQU hQQ hOQ
  rwa [hC] at h2

theorem card_qL_le_of_tC_eq_bot
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hA6 : IsAltBlockType L 6) (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTC : tC L T = ⊥) :
    Nat.card ↥(qL L T) ≤ 2 ^ 5 := by
  have h1 := h.relIndex_qL_le_two h38 h39 hA6 hTL
  rw [hTC, sup_bot_eq] at h1
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hUQ : blockU L ≤ qL L T := (C1.blockU_le_blockQ hA6.1).trans hOQ
  have hZ : blockZ L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ tC L T := ⟨hQT (hUQ hz.1), hz.2⟩
    rw [hTC] at hz'
    exact hz'
  have hU := A6Block.card_blockU_of_blockZ_eq_bot hA6 hZ
  have h2 := Subgroup.relIndex_mul_card (H := blockU L) (K := qL L T)
  rw [inf_of_le_left hUQ, hU] at h2
  rw [← h2]
  calc (blockU L).relIndex (qL L T) * 16 ≤ 2 * 16 := Nat.mul_le_mul_right 16 h1
    _ = 2 ^ 5 := by norm_num

theorem frattini_qL_eq_bot_of_tC_ne_bot
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h27 : Stmt3_3_27)
    (hS : Step3_3_31S) (hE4 : Step3_3_31E4) (hA6 : IsAltBlockType L 6)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTC : tC L T ≠ ⊥) {d : G} (hdD : d ∈ D)
    (hdM : d ∉ M) (hdV : ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T) : frattini ↥(qL L T) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hF
  obtain ⟨-, hdS, hVdC, hQdec, hTdec, hZ2⟩ := hS G T M L D h hA6 hTL hTC d hdD hdM hdV
  obtain ⟨hTCd, hFTC, -⟩ := h27 G T M L D h d hdD hdM hdV hTC
  set Q := qL L T with hQdef
  set V := vPlus L T with hVdef
  set C := tC L T with hCdef
  set Vd := CFSG.conjugate V d with hVddef
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hCT : C ≤ T := inf_le_left
  have hCe : IsElemAbelian 2 C := isElemAbelian_of_frattini_eq_bot (hT2.to_le hCT) hFTC
  have hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb => by
    have := hCe.1
    exact setLike_mul_comm ha hb
  have hCQ : C ≤ Q := h.tC_le_qL h38 h39 hTL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : V ≤ Q := hred.1.trans inf_le_left
  have hVZ : ∀ v ∈ V, ∀ q ∈ Q, v * q = q * v := fun v hv q hq =>
    (Subgroup.mem_centralizer_iff.mp ((hred.1.trans inf_le_right) hv) q hq).symm
  have hVe := hred.2.1
  have hΦ : (frattini ↥Q).map Q.subtype ≤ C := h.frattini_qL_le_tC h38 h39 hA6.1 hTL
  have hsq : ∀ x ∈ Q, x ^ 2 ∈ C := fun x hx => sq_mem_of_frattini_le hQ2 hΦ hx
  have hCN : T ≤ Subgroup.normalizer (C : Set G) := le_normalizer_tC hTL
  have hVN : V ≤ Subgroup.normalizer (C : Set G) := (hVQ.trans hQT).trans hCN
  have hx₀ : ∃ x ∈ Q, x ^ 2 ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hF (frattini_eq_bot_of_isElemAbelian (isElemAbelian_of_sq_eq_one hall))
  have hCVe : ∀ x ∈ C ⊔ V, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨c, hc, v, hv, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hVN).mp hx
    have hcv : Commute c v := (hVZ v hv c (hCQ hc)).symm
    rw [hcv.mul_pow, hCe.2 c hc, hVe.2 v hv, one_mul]
  have hCVQ : C ⊔ V ≤ Q := sup_le hCQ hVQ
  have hlt : ¬ Q ≤ C ⊔ V := fun hle => by
    obtain ⟨x, hx, hx2⟩ := hx₀
    exact hx2 (hCVe x (hle hx))
  obtain ⟨u, ⟨huQ, huVd⟩, huCV⟩ : ∃ u ∈ Q ⊓ Subgroup.centralizer (Vd : Set G), u ∉ C ⊔ V := by
    by_contra hcon
    push Not at hcon
    apply hlt
    rw [hQdec]
    exact sup_le le_sup_right fun x hx => hcon x hx
  have hidx2 : (C ⊔ V).relIndex Q = 2 := by
    have hU := h.blockU_le_vPlus h38 h39 hA6.1 hTL
    have h1 : (blockU L ⊔ C).relIndex Q ≤ 2 := h.relIndex_qL_le_two h38 h39 hA6 hTL
    have h2 : (C ⊔ V).relIndex Q ≤ (blockU L ⊔ C).relIndex Q := by
      rw [sup_comm C V]
      exact Subgroup.relIndex_le_of_le_left (sup_le_sup_right hU C)
        Subgroup.index_ne_zero_of_finite
    have h3 : (C ⊔ V).relIndex Q ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact hlt
    have h4 : (C ⊔ V).relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hu2 : u ^ 2 ∈ C ⊔ V := by
    have h2 : ((C ⊔ V).subgroupOf Q).index = 2 := hidx2
    have h3 := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨u, huQ⟩ : ↥Q))
      (b := ⟨u, huQ⟩)).mpr Iff.rfl
    rw [pow_two]
    exact Subgroup.mem_subgroupOf.mp h3
  have hQgen : Q = Subgroup.zpowers u ⊔ (C ⊔ V) := by
    have hle : Subgroup.zpowers u ⊔ (C ⊔ V) ≤ Q := sup_le (Subgroup.zpowers_le.mpr huQ) hCVQ
    refine le_antisymm (fun x hx => ?_) hle
    by_cases hxW : x ∈ C ⊔ V
    · exact Subgroup.mem_sup_right hxW
    · have h2 : ((C ⊔ V).subgroupOf Q).index = 2 := hidx2
      have h3 := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨u, huQ⟩ : ↥Q)⁻¹)
        (b := ⟨x, hx⟩)).mpr (iff_of_false (fun h' => huCV (by
          have := Subgroup.mem_subgroupOf.mp h'
          simpa using this)) (fun h' => hxW (Subgroup.mem_subgroupOf.mp h')))
      have h4 : u⁻¹ * x ∈ C ⊔ V := Subgroup.mem_subgroupOf.mp h3
      have h5 : x = u * (u⁻¹ * x) := by group
      rw [h5]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
        (Subgroup.mem_sup_right h4)
  have huN : u ∈ Subgroup.normalizer (C : Set G) := hCN (hQT huQ)
  have hu2C : ∀ c ∈ C, u ^ 2 * c = c * u ^ 2 := by
    intro c hc
    obtain ⟨c₁, hc₁, v, hv, he⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hVN).mp hu2
    rw [he]
    have h1 : c₁ * c = c * c₁ := hCab c₁ hc₁ c hc
    have h2 : v * c = c * v := hVZ v hv c (hCQ hc)
    calc c₁ * v * c = c₁ * (v * c) := by group
      _ = c₁ * (c * v) := by rw [h2]
      _ = c * c₁ * v := by rw [← mul_assoc, h1]
      _ = c * (c₁ * v) := by group
  have hcentT : C ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer (T : Set G) := by
    intro c hc
    have hcC : c ∈ C := hc.1
    have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hcL : c ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp hcC).2
    have hle : T ≤ Subgroup.centralizer ({c} : Set G) := by
      rw [hTdec]
      refine sup_le (sup_le ?_ ?_) ?_
      · intro t ht
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hcL t ht.2)
      · rw [hQgen]
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (sup_le ?_ ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact hcu.symm
        · intro c' hc'
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hCab c' hc' c hcC
        · intro v hv
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hVZ v hv c (hCQ hcC)
      · intro w hw
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hVdC hw) c hcC).symm
    exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hle ht))
  have hCuZ : C ⊓ Subgroup.centralizer ({u} : Set G) ≤
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := by
    intro c hc
    refine ⟨Subgroup.subset_closure ⟨⟨hCT hc.1, hcentT hc⟩, hCe.2 c hc.1⟩,
      (Subgroup.mem_inf.mp hc.1).2⟩
  have hCu2 : Nat.card ↥(C ⊓ Subgroup.centralizer ({u} : Set G)) ≤ 2 := by
    rw [← hZ2]
    exact Subgroup.card_le_of_le hCuZ
  have hC4 : Nat.card ↥C ≤ 4 := by
    have h1 := card_le_sq_of_centralizes hCe huN hu2C
    have h2 : Nat.card ↥(C ⊓ Subgroup.centralizer ({u} : Set G)) ^ 2 ≤ 4 :=
      calc Nat.card ↥(C ⊓ Subgroup.centralizer ({u} : Set G)) ^ 2 ≤ 2 ^ 2 :=
            Nat.pow_le_pow_left hCu2 2
        _ = 4 := by norm_num
    exact h1.trans h2
  obtain ⟨k, hk⟩ := (hT2.to_le hCT).exists_card_eq
  have hC1 : 1 < Nat.card ↥C := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    exact hTC
  have hk12 : k = 1 ∨ k = 2 := by
    rcases k with _ | _ | _ | k
    · rw [hk] at hC1; norm_num at hC1
    · left; rfl
    · right; rfl
    · exfalso
      rw [hk] at hC4
      have h8 : 8 ≤ 2 ^ (k + 1 + 1 + 1) :=
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (k + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf (⟨d, hdD⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat h.Dodd h1
  have hfin : d ∈ Subgroup.normalizer (C : Set G) → False := by
    intro hdC
    apply hTC
    rw [← hTCd]
    refine le_antisymm (le_inf le_rfl fun c hc => ?_) inf_le_left
    show c ∈ C.map (MulAut.conj d⁻¹).toMonoidHom
    rw [A38.mem_map_conj, inv_inv]
    exact (Subgroup.mem_normalizer_iff.mp hdC c).mp hc
  rcases hk12 with rfl | rfl
  ·
    have hk2 : Nat.card ↥C = 2 := by rw [hk, pow_one]
    have hCcen : ∀ t ∈ T, ∀ c ∈ C, t * c = c * t := by
      intro t ht c hc
      by_cases hc1 : c = 1
      · rw [hc1, mul_one, one_mul]
      have h1 : t * c * t⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hCN ht) c).mp hc
      have h2 : t * c * t⁻¹ ≠ 1 := fun h' => hc1 (by
        have := congrArg (fun z => t⁻¹ * z * t) h'
        simpa [mul_assoc] using this)
      have h3 : (⟨t * c * t⁻¹, h1⟩ : ↥C) = ⟨c, hc⟩ :=
        eq_of_card_two hk2 (fun h' => h2 (congrArg Subtype.val h'))
          (fun h' => hc1 (congrArg Subtype.val h'))
      have h4 : t * c * t⁻¹ = c := congrArg Subtype.val h3
      calc t * c = t * c * t⁻¹ * t := by group
        _ = c * t := by rw [h4]
    have huQc : ∀ q ∈ Q, u * q = q * u := by
      intro q hq
      have hle : Q ≤ Subgroup.centralizer ({u} : Set G) := by
        rw [hQgen]
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (sup_le ?_ ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
        · intro c hc
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hCcen u (hQT huQ) c hc).symm
        · intro v hv
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hVZ v hv u huQ)
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hq)).symm
    have hu21 : u ^ 2 ≠ 1 := by
      intro hu1
      obtain ⟨x, hx, hx2⟩ := hx₀
      apply hx2
      rw [hQgen] at hx
      have hWN : C ⊔ V ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
        intro w hw
        rw [Subgroup.mem_normalizer_iff]
        intro z
        have hwu : w * u = u * w := (huQc w (hCVQ hw)).symm
        constructor
        · rintro ⟨n, rfl⟩
          refine ⟨n, ?_⟩
          change u ^ n = w * u ^ n * w⁻¹
          rw [(Commute.zpow_right hwu n).eq]
          group
        · rintro ⟨n, hn⟩
          have hn' : u ^ n = w * z * w⁻¹ := hn
          refine ⟨n, ?_⟩
          have hc := (Commute.zpow_right hwu n).eq
          calc u ^ n = w⁻¹ * (w * u ^ n) := by group
            _ = w⁻¹ * (u ^ n * w) := by rw [hc]
            _ = w⁻¹ * (w * z * w⁻¹ * w) := by rw [hn']
            _ = z := by group
      obtain ⟨y, ⟨n, rfl⟩, w, hw, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hWN).mp hx
      have hwu : w * u = u * w := (huQc w (hCVQ hw)).symm
      have hc : Commute (u ^ n) w := Commute.zpow_left hwu.symm n
      have hun2 : (u ^ n) ^ 2 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu1, one_zpow]
      rw [hc.mul_pow, hun2, one_mul, hCVe w hw]
    have hSu : Q ⊔ Vd ≤ Subgroup.centralizer ({u} : Set G) := by
      refine sup_le (fun q hq => Subgroup.mem_centralizer_singleton_iff.mpr (huQc q hq).symm) ?_
      intro w hw
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp huVd w hw)
    have hduQ : d * u * d⁻¹ ∈ Q := by
      have hSN : d⁻¹ ∈ Subgroup.normalizer ((Q ⊔ Vd : Subgroup G) : Set G) :=
        Subgroup.inv_mem _ hdS
      have hdu : d * u * d⁻¹ ∈ Q ⊔ Vd :=
        (Subgroup.mem_normalizer_iff.mp hdS u).mp (Subgroup.mem_sup_left huQ)
      have hC : (Q ⊔ Vd) ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
        intro x hx
        have hcv : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
          (h.centralizer_vPlus h38 h39).2.1
        show x ∈ qL L T
        rw [← hcv]
        exact ⟨(sup_le hQT (Hyp331.map_conj_le_of_le (hVQ.trans hQT)
          (Subgroup.inv_mem _ (h.DN hdD)))) hx.1,
          Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVQ) hx.2⟩
      refine hC ⟨hdu, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      have h1 : d⁻¹ * q * d ∈ Q ⊔ Vd := by
        have := (Subgroup.mem_normalizer_iff.mp hSN q).mp (Subgroup.mem_sup_left hq)
        simpa using this
      have h2 : u * (d⁻¹ * q * d) = (d⁻¹ * q * d) * u :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hSu h1)).symm
      calc q * (d * u * d⁻¹) = d * ((d⁻¹ * q * d) * u) * d⁻¹ := by group
        _ = d * (u * (d⁻¹ * q * d)) * d⁻¹ := by rw [h2]
        _ = d * u * d⁻¹ * q := by group
    have hu2C' : u ^ 2 ∈ C := hsq u huQ
    have hdu2 : d * u ^ 2 * d⁻¹ ∈ C := by
      have := hsq _ hduQ
      rwa [conj_pow] at this
    have hdu2' : d * u ^ 2 * d⁻¹ = u ^ 2 := by
      have h1 : (⟨d * u ^ 2 * d⁻¹, hdu2⟩ : ↥C) = ⟨u ^ 2, hu2C'⟩ :=
        eq_of_card_two hk2 (fun h' => hu21 (by
          have := congrArg Subtype.val h'
          have h2 : d * u ^ 2 * d⁻¹ = 1 := this
          have := congrArg (fun z => d⁻¹ * z * d) h2
          simpa [mul_assoc] using this)) (fun h' => hu21 (congrArg Subtype.val h'))
      exact congrArg Subtype.val h1
    apply hfin
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have hall : ∀ c ∈ C, c = 1 ∨ c = u ^ 2 := by
      intro c hc
      by_cases hc1 : c = 1
      · exact Or.inl hc1
      · right
        have := eq_of_card_two hk2 (x := (⟨c, hc⟩ : ↥C)) (y := ⟨u ^ 2, hu2C'⟩)
          (fun h' => hc1 (congrArg Subtype.val h')) (fun h' => hu21 (congrArg Subtype.val h'))
        exact congrArg Subtype.val this
    constructor
    · intro hc
      rcases hall c hc with rfl | rfl
      · simp
      · rw [hdu2']
        exact hu2C'
    · intro hc
      rcases hall _ hc with h1 | h1
      · have : c = 1 := by
          have := congrArg (fun z => d⁻¹ * z * d) h1
          simpa [mul_assoc] using this
        rw [this]
        exact C.one_mem
      · have : c = u ^ 2 := by
          have h2 : d * c * d⁻¹ = d * u ^ 2 * d⁻¹ := by rw [h1, hdu2']
          have := congrArg (fun z => d⁻¹ * z * d) h2
          simpa [mul_assoc] using this
        rw [this]
        exact hu2C'
  ·
    have hk4 : Nat.card ↥C = 4 := by rw [hk]; norm_num
    obtain ⟨e⟩ := hE4 G T M L D h hA6 hTL hTC d hdD hdM hdV hF hk4
    obtain ⟨x, hx, hx2⟩ := hx₀
    set S := Q ⊔ Vd with hSdef
    have hxS : x ∈ S := Subgroup.mem_sup_left hx
    set α : MulAut ↥S := S.normalizerMonoidHom ⟨d, hdS⟩ with hα
    have hαodd : Odd (orderOf α) := by
      have h1 : orderOf α ∣ orderOf (⟨d, hdS⟩ : ↥(Subgroup.normalizer (S : Set G))) :=
        orderOf_map_dvd _ _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hodd h1
    have hfix := fixes_sq_of_odd e α hαodd ⟨x, hxS⟩
    have h1 : d * x ^ 2 * d⁻¹ = x ^ 2 := congrArg Subtype.val hfix
    have hx2C : x ^ 2 ∈ C := hsq x hx
    have hmem : x ^ 2 ∈ C ⊓ CFSG.conjugate C d := by
      refine ⟨hx2C, ?_⟩
      show x ^ 2 ∈ C.map (MulAut.conj d⁻¹).toMonoidHom
      rw [A38.mem_map_conj, inv_inv, h1]
      exact hx2C
    rw [hTCd, Subgroup.mem_bot] at hmem
    exact hx2 hmem

end Hyp331

theorem stmt3_3_31_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14) (h26 : Stmt3_3_26)
    (h27 : Stmt3_3_27) (h30 : Stmt3_3_30) (hS : Step3_3_31S) (hE4 : Step3_3_31E4) :
    Stmt3_3_31 := by
  intro G _ _ T M L D h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hTC
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hA6 := h30 G T M L D h
  obtain ⟨d, hdD, hdM, hdV⟩ := h26 G T M L D h
  obtain ⟨hidx, hdS, -⟩ := hS G T M L D h hA6 hTL hTC d hdD hdM hdV
  have hF := h.frattini_qL_eq_bot_of_tC_ne_bot h38 h39 h27 hS hE4 hA6 hTL hTC hdD hdM hdV
  have hQe : IsElemAbelian 2 (qL L T) :=
    isElemAbelian_of_frattini_eq_bot (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hF
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hVdT : CFSG.conjugate (vPlus L T) d ≤ T :=
    Hyp331.map_conj_le_of_le (hVQ.trans hQT) (Subgroup.inv_mem _ hdT)
  have hST : qL L T ⊔ CFSG.conjugate (vPlus L T) d ≤ T := sup_le hQT hVdT
  have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  have hSC : (qL L T ⊔ CFSG.conjugate (vPlus L T) d) ⊓ Subgroup.centralizer (qL L T : Set G) ≤
      qL L T := fun x hx => by
    rw [← hCQ]
    exact ⟨hST hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVQ) hx.2⟩
  obtain ⟨hQmax, huniq⟩ := isMaxElemAbelian_of_relIndex_two le_sup_left hQe hidx hSC
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf (⟨d, hdD⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat h.Dodd h1
  have hdQ := mem_normalizer_of_odd_of_unique hQmax huniq hdS hodd
  exact hdM (h.toSetup331.normalizer_le h38 h39 h.toSetup331.pCoreOf_ne_bot
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) hdQ)

end CFSG.Quasithin.H13
