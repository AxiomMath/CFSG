module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cA
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cAutN

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem le_normalizer_of_relIndex_two' {H K : Subgroup D} (hHK : H ≤ K)
    (h2 : H.relIndex K = 2) : K ≤ Subgroup.normalizer (H : Set D) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).1 (Subgroup.normal_of_index_eq_two h2)

theorem mem_of_cube_of_relIndex_two {H K : Subgroup D} (h2 : H.relIndex K = 2) {x : D}
    (hx : x ∈ K) (hx3 : x * x * x = 1) : x ∈ H := by
  have hn : (H.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two h2
  have h2' : (H.subgroupOf K).index = 2 := h2
  have := Subgroup.pow_index_mem (H.subgroupOf K) (⟨x, hx⟩ : K)
  rw [h2', Subgroup.mem_subgroupOf] at this
  have hsq : x ^ 2 ∈ H := by simpa using this
  have e : x = x ^ 2 * x ^ 2 := by
    calc x = x * (x * x * x) := by rw [hx3, mul_one]
      _ = x ^ 2 * x ^ 2 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e]
  exact H.mul_mem hsq hsq

theorem pCoreOf_eq_inf_of_relIndex_two {A' : Subgroup D} [Finite D] (hle : A' ≤ A)
    (h2 : A'.relIndex A = 2) : pCoreOf 2 A' = A' ⊓ pCoreOf 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : A ≤ Subgroup.normalizer (A' : Set D) := le_normalizer_of_relIndex_two' hle h2
  apply le_antisymm
  · refine le_inf (pCoreOf_le 2 A') ?_
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 A').trans hle)
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 A')) (pCoreOf_isPGroup 2 A')
  · refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 A).to_le inf_le_right)
    exact le_normalizer_inf (fun g hg => (Subgroup.mem_normalizer_iff.mpr
      (Subgroup.mem_normalizer_iff.mp (hn (hle hg)))))
      (fun g hg => le_normalizer_pCoreOf 2 A (hle hg))

structure SubAm (A B A' B' : Subgroup D) : Prop where
  le₁ : A' ≤ A
  le₂ : B' ≤ B
  idx₁ : A'.relIndex A = 2
  idx₂ : B'.relIndex B = 2
  v₁ : Vertex A' (A' ⊓ B')
  v₂ : Vertex B' (A' ⊓ B')

section SubAmMain

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂) {A' B' : Subgroup D}
  (s : SubAm A B A' B')

include g s

theorem SubAm.inf_B_eq : A' ⊓ B = A' ⊓ B' := by
  have hTC : A' ⊓ B' ≤ A' ⊓ B := inf_le_inf_left _ s.le₂
  by_contra hne
  obtain ⟨c, hc, hcT'⟩ : ∃ c ∈ A' ⊓ B, c ∉ A' ⊓ B' := by
    by_contra hall
    push Not at hall
    exact hne (le_antisymm (fun c hc => hall c hc) hTC)
  have hA'le : A' ≤ A' ⊓ B := s.v₁.le_of_not_mem hTC inf_le_left hc hcT'
  obtain ⟨w, hwA', hw3⟩ := s.v₁.exists_order_three
  exact g.hyp.gold.vertex_left.not_mem_of_orderOf hw3 ⟨s.le₁ hwA', (hA'le hwA').2⟩

theorem SubAm.inf_A_eq : B' ⊓ A = A' ⊓ B' := by
  have hTC : A' ⊓ B' ≤ B' ⊓ A := le_inf inf_le_right (inf_le_left.trans s.le₁)
  by_contra hne
  obtain ⟨c, hc, hcT'⟩ : ∃ c ∈ B' ⊓ A, c ∉ A' ⊓ B' := by
    by_contra hall
    push Not at hall
    exact hne (le_antisymm (fun c hc => hall c hc) hTC)
  have hB'le : B' ≤ B' ⊓ A := s.v₂.le_of_not_mem hTC inf_le_left hc hcT'
  obtain ⟨w, hwB', hw3⟩ := s.v₂.exists_order_three
  exact g.hyp.gold.vertex_left.not_mem_of_orderOf hw3 ⟨(hB'le hwB').2, s.le₂ hwB'⟩

theorem SubAm.relIndex_T' : (A' ⊓ B').relIndex (A ⊓ B) = 2 := by
  have hT'T : A' ⊓ B' ≤ A ⊓ B := le_inf (inf_le_left.trans s.le₁) (inf_le_right.trans s.le₂)
  have h1 := Subgroup.relIndex_mul_relIndex (A' ⊓ B') A' A inf_le_left s.le₁
  have h2 := Subgroup.relIndex_mul_relIndex (A' ⊓ B') (A ⊓ B) A hT'T inf_le_left
  rw [s.v₁.index_eq, s.idx₁] at h1
  rw [g.hyp.gold.vertex_left.index_eq] at h2
  omega

omit [Finite D] in
theorem SubAm.x_mem : x ∈ B' := mem_of_cube_of_relIndex_two s.idx₂ g.x_mem g.x_cube

theorem SubAm.card_T' (hT : Nat.card ↥(A ⊓ B) = 128) : Nat.card ↥(A' ⊓ B') = 64 := by
  have hT'T : A' ⊓ B' ≤ A ⊓ B := le_inf (inf_le_left.trans s.le₁) (inf_le_right.trans s.le₂)
  have h1 := card_eq_relIndex_mul hT'T
  rw [s.relIndex_T' g, hT] at h1
  omega

theorem SubAm.card_pCoreOf_A' (hT : Nat.card ↥(A ⊓ B) = 128) : Nat.card ↥(pCoreOf 2 A') = 32 := by
  have h1 := card_eq_relIndex_mul s.v₁.pCoreOf_le
  rw [s.v₁.relIndex_pCoreOf_T, s.card_T' g hT] at h1
  omega

theorem SubAm.card_pCoreOf_B' (hT : Nat.card ↥(A ⊓ B) = 128) : Nat.card ↥(pCoreOf 2 B') = 32 := by
  have h1 := card_eq_relIndex_mul s.v₂.pCoreOf_le
  rw [s.v₂.relIndex_pCoreOf_T, s.card_T' g hT] at h1
  omega

theorem SubAm.V_le_A' {y : D} (hyA' : y ∈ A') (hy3 : orderOf y = 3) : V ≤ A' := by
  have hyA : y ∈ A := s.le₁ hyA'
  have hn : A ≤ Subgroup.normalizer (A' : Set D) := le_normalizer_of_relIndex_two' s.le₁ s.idx₁
  have hcomm : ∀ p q : D, p ∈ V → q ∈ V → p * q = q * p := fun p q hp hq =>
    g.U_comm (le_conjClosure V B hp) (le_conjClosure V B hq)
  let φ : ↥V →* ↥V :=
    { toFun := fun w => ⟨(w : D) * (y * (w : D) * y⁻¹)⁻¹,
        V.mul_mem w.2 (V.inv_mem (g.conj_mem_V hyA w.2))⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro w w'
        apply Subtype.ext
        have hp : (y * (w : D) * y⁻¹)⁻¹ ∈ V := V.inv_mem (g.conj_mem_V hyA w.2)
        have hq : (y * (w' : D) * y⁻¹)⁻¹ ∈ V := V.inv_mem (g.conj_mem_V hyA w'.2)
        have c1 := hcomm _ _ hq hp
        have c2 := hcomm (w' : D) _ w'.2 hp
        show (w : D) * (w' : D) * (y * ((w : D) * (w' : D)) * y⁻¹)⁻¹ =
          ((w : D) * (y * (w : D) * y⁻¹)⁻¹) * ((w' : D) * (y * (w' : D) * y⁻¹)⁻¹)
        calc (w : D) * (w' : D) * (y * ((w : D) * (w' : D)) * y⁻¹)⁻¹
            = (w : D) * (w' : D) * ((y * (w' : D) * y⁻¹)⁻¹ * (y * (w : D) * y⁻¹)⁻¹) := by group
          _ = (w : D) * ((w' : D) * ((y * (w' : D) * y⁻¹)⁻¹ * (y * (w : D) * y⁻¹)⁻¹)) := by group
          _ = (w : D) * ((w' : D) * ((y * (w : D) * y⁻¹)⁻¹ * (y * (w' : D) * y⁻¹)⁻¹)) := by
            rw [c1]
          _ = (w : D) * (((w' : D) * (y * (w : D) * y⁻¹)⁻¹) * (y * (w' : D) * y⁻¹)⁻¹) := by
            group
          _ = (w : D) * (((y * (w : D) * y⁻¹)⁻¹ * (w' : D)) * (y * (w' : D) * y⁻¹)⁻¹) := by
            rw [c2]
          _ = ((w : D) * (y * (w : D) * y⁻¹)⁻¹) * ((w' : D) * (y * (w' : D) * y⁻¹)⁻¹) := by
            group }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : (w : D) * (y * (w : D) * y⁻¹)⁻¹ = 1 := congrArg Subtype.val hw
    have h2 : y * (w : D) * y⁻¹ = w := by
      have := mul_inv_eq_one.mp h1
      exact this.symm
    by_contra hne
    exact g.conj_ne_of_ne_one hyA hy3 w.2 (fun h => hne (Subtype.ext h)) h2
  have hsurj : Function.Surjective φ := Finite.surjective_of_injective hinj
  intro v hv
  obtain ⟨w, hw⟩ := hsurj ⟨v, hv⟩
  have hv' : v = (w : D) * (y * (w : D) * y⁻¹)⁻¹ := (congrArg Subtype.val hw).symm
  have hwA : (w : D) ∈ A :=
    pCoreOf_le 2 A ((g.hyp.natural.le_center w.2).1)
  have hconj : (w : D) * y * (w : D)⁻¹ ∈ A' := (Subgroup.mem_normalizer_iff.mp (hn hwA) y).mp hyA'
  have : v = ((w : D) * y * (w : D)⁻¹) * y⁻¹ := by rw [hv']; group
  rw [this]
  exact A'.mul_mem hconj (A'.inv_mem hyA')

theorem SubAm.U_le_T' {y : D} (hyA' : y ∈ A') (hy3 : orderOf y = 3) :
    conjClosure V B ≤ A' ⊓ B' := by
  have hVA' : V ≤ A' := s.V_le_A' g hyA' hy3
  have hVA : V ≤ A := fun v hv => pCoreOf_le 2 A ((g.hyp.natural.le_center hv).1)
  have hVT : V ≤ A ⊓ B := fun v hv =>
    g.hyp.gold.pCoreOf_left_le ((g.hyp.natural.le_center hv).1)
  have hVB' : V ≤ B' := by
    have : V ≤ A' ⊓ B := le_inf hVA' (fun v hv => (hVT hv).2)
    rw [s.inf_B_eq g] at this
    exact this.trans inf_le_right
  have hnB : B ≤ Subgroup.normalizer (B' : Set D) := le_normalizer_of_relIndex_two' s.le₂ s.idx₂
  have hUB' : conjClosure V B ≤ B' := by
    refine conjClosure_le fun k hk v hv => ?_
    exact (Subgroup.mem_normalizer_iff.mp (hnB hk) v).mp (hVB' hv)
  have hUA : conjClosure V B ≤ A := fun u hu =>
    pCoreOf_le 2 A (g.hyp.conjClosure_le_pCoreOf_left hu)
  have : conjClosure V B ≤ B' ⊓ A := le_inf hUB' hUA
  rwa [s.inf_A_eq g] at this

theorem SubAm.nData (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 128) :
    NData B V x (pCoreOf 2 B') := by
  obtain ⟨y, hyA, hy3⟩ := g.hyp.gold.vertex_left.exists_order_three
  have hyA' : y ∈ A' := mem_of_cube_of_relIndex_two s.idx₁ hyA (by
    have := pow_orderOf_eq_one y
    rwa [hy3, pow_three'] at this)
  have hUT' := s.U_le_T' g hyA' hy3
  have hle : pCoreOf 2 B' ≤ pCoreOf 2 B := by
    rw [pCoreOf_eq_inf_of_relIndex_two s.le₂ s.idx₂]; exact inf_le_right
  refine ⟨hle, ?_, ?_, s.card_pCoreOf_B' g hT, ?_⟩
  · exact le_normalizer_pCoreOf 2 B' (s.x_mem g)
  · rw [pCoreOf_eq_inf_of_relIndex_two s.le₂ s.idx₂]
    exact le_inf (hUT'.trans inf_le_right)
      (g.hyp.conjClosure_le_pCoreOf_right)
  · by_contra hcon
    push Not at hcon
    have hK : pCoreOf 2 B' ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
      rw [← g.hyp.pCoreOf_inf_centralizer_eq_coreIn]
      exact fun q hq => ⟨hle hq, Subgroup.mem_centralizer_iff.mpr fun u hu => hcon q hq u hu⟩
    have h1 := Subgroup.card_le_of_le hK
    have h2 := g.hyp.card_inf_eq_eight_mul hU
    rw [s.card_pCoreOf_B' g hT] at h1
    omega

end SubAmMain

end GoldAmL3c

end F6

end CFSG.Quasithin
