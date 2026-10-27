module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Idx
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Geom
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Ker

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem pCoreOf_left_le_centralizer : pCoreOf 2 A ≤ Subgroup.centralizer (V : Set D) :=
  fun _ hx => ((inf_inf_centralizer_eq_pCoreOf h.natural).ge hx).2

omit [Finite D] in
theorem relIndex_V_conjClosure (hU : Nat.card (conjClosure V B) = 8) :
    V.relIndex (conjClosure V B) = 2 := by
  have h1 := Subgroup.relIndex_mul_card V (conjClosure V B)
  rw [inf_eq_left.mpr (le_conjClosure V B), h.natural.card_eq, hU] at h1
  omega

omit [Finite D] in
theorem mul_inv_mem_V_of_not_mem (hU : Nat.card (conjClosure V B) = 8) {x y : D}
    (hx : x ∈ conjClosure V B) (hy : y ∈ conjClosure V B) (hxV : x ∉ V) (hyV : y ∉ V) :
    x * y⁻¹ ∈ V := by
  obtain ⟨a, -, ha⟩ := Subgroup.relIndex_eq_two_iff.mp (h.relIndex_V_conjClosure hU)
  have hxa : x * a ∈ V := by
    rcases ha x hx with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hxV
  have hya : y * a ∈ V := by
    rcases ha y hy with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hyV
  have e : x * y⁻¹ = (x * a) * (y * a)⁻¹ := by group
  rw [e]
  exact V.mul_mem hxa (V.inv_mem hya)

theorem commutator_mem_V_of_pCoreOf_left (hU : Nat.card (conjClosure V B) = 8) {u q : D}
    (hu : u ∈ conjClosure V B) (hq : q ∈ pCoreOf 2 A) : u * q * u⁻¹ * q⁻¹ ∈ V := by
  by_cases huV : u ∈ V
  · have hc : u * q = q * u :=
      Subgroup.mem_centralizer_iff.mp (h.pCoreOf_left_le_centralizer hq) u huV
    have : u * q * u⁻¹ * q⁻¹ = 1 := by rw [hc]; group
    rw [this]
    exact V.one_mem
  · have hqT : q ∈ A ⊓ B := h.gold.pCoreOf_left_le hq
    have hqU : q * u * q⁻¹ ∈ conjClosure V B :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B hqT.2) u).mp hu
    have hqV : q * u * q⁻¹ ∉ V := fun hx =>
      huV ((Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 hqT.1) u).mpr hx)
    have := h.mul_inv_mem_V_of_not_mem hU hu hqU huV hqV
    have e : u * q * u⁻¹ * q⁻¹ = u * (q * u * q⁻¹)⁻¹ := by group
    rw [e]
    exact this

theorem mem_coreIn_of_comm {x : D} (hx : x ∈ pCoreOf 2 A)
    (hc : ∀ u ∈ conjClosure V B, u * x = x * u) :
    x ∈ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
  have hxB : x ∈ B := (h.gold.pCoreOf_left_le hx).2
  have hQ : x ∈ pCoreOf 2 B := by
    rw [h.pCoreOf_eq_centralizerMod]
    refine ⟨hxB, mem_normalizer_zpowers_of_mul_comm (mul_eq_of_conj_eq (h.central x hxB)),
      fun u hu => ?_⟩
    have : x * u * x⁻¹ * u⁻¹ = 1 := by
      rw [← hc u hu]; group
    rw [this]
    exact Subgroup.one_mem _
  rw [← h.pCoreOf_inf_centralizer_eq_coreIn]
  exact ⟨hQ, Subgroup.mem_centralizer_iff.mpr fun u hu => hc u hu⟩

theorem comm_of_mem_coreIn {x : D} (hx : x ∈ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) :
    ∀ u ∈ conjClosure V B, u * x = x * u := by
  rw [← h.pCoreOf_inf_centralizer_eq_coreIn] at hx
  intro u hu
  exact Subgroup.mem_centralizer_iff.mp hx.2 u hu

theorem relIndex_coreIn_pCoreOf_left_le (hU : Nat.card (conjClosure V B) = 8) :
    (coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B).relIndex (pCoreOf 2 A) ≤ 4 := by
  obtain ⟨u₀, hu₀U, hu₀V⟩ : ∃ u₀ ∈ conjClosure V B, u₀ ∉ V := by
    by_contra hcon
    push Not at hcon
    exact h.not_conjClosure_le fun u hu => hcon u hu
  have hcomm : ∀ q ∈ pCoreOf 2 A, u₀ * q * u₀⁻¹ * q⁻¹ ∈ V := fun q hq =>
    h.commutator_mem_V_of_pCoreOf_left hU hu₀U hq
  let f : ↥(pCoreOf 2 A) →* D :=
    MonoidHom.mk' (fun q => u₀ * (q : D) * u₀⁻¹ * (q : D)⁻¹) (by
      intro a b
      have hcb := hcomm (b : D) b.2
      have hcom : (u₀ * (b : D) * u₀⁻¹ * (b : D)⁻¹) * (a : D) =
          (a : D) * (u₀ * (b : D) * u₀⁻¹ * (b : D)⁻¹) :=
        Subgroup.mem_centralizer_iff.mp (h.pCoreOf_left_le_centralizer a.2) _ hcb
      simp only [Subgroup.coe_mul]
      calc u₀ * ((a : D) * (b : D)) * u₀⁻¹ * ((a : D) * (b : D))⁻¹
          = (u₀ * (a : D) * u₀⁻¹ * (a : D)⁻¹) *
            ((a : D) * (u₀ * (b : D) * u₀⁻¹ * (b : D)⁻¹) * (a : D)⁻¹) := by group
        _ = _ := by rw [← hcom]; group)
  have hker : f.ker = (coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B).subgroupOf (pCoreOf 2 A) := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hq
      have hq' : u₀ * (q : D) * u₀⁻¹ * (q : D)⁻¹ = 1 := hq
      have hc0 : u₀ * (q : D) = (q : D) * u₀ := by
        calc u₀ * (q : D) = (u₀ * (q : D) * u₀⁻¹ * (q : D)⁻¹) * ((q : D) * u₀) := by group
          _ = (q : D) * u₀ := by rw [hq', one_mul]
      refine h.mem_coreIn_of_comm q.2 fun u hu => ?_
      by_cases huV : u ∈ V
      · exact Subgroup.mem_centralizer_iff.mp (h.pCoreOf_left_le_centralizer q.2) u huV
      · have hv : u * u₀⁻¹ ∈ V := h.mul_inv_mem_V_of_not_mem hU hu hu₀U huV hu₀V
        have hvc : (u * u₀⁻¹) * (q : D) = (q : D) * (u * u₀⁻¹) :=
          Subgroup.mem_centralizer_iff.mp (h.pCoreOf_left_le_centralizer q.2) _ hv
        calc u * (q : D) = (u * u₀⁻¹) * (u₀ * (q : D)) := by group
          _ = (u * u₀⁻¹) * ((q : D) * u₀) := by rw [hc0]
          _ = ((u * u₀⁻¹) * (q : D)) * u₀ := by group
          _ = ((q : D) * (u * u₀⁻¹)) * u₀ := by rw [hvc]
          _ = (q : D) * u := by group
    · intro hq
      have hc : u₀ * (q : D) = (q : D) * u₀ := h.comm_of_mem_coreIn hq u₀ hu₀U
      show u₀ * (q : D) * u₀⁻¹ * (q : D)⁻¹ = 1
      rw [hc]
      group
  have hrange : f.range ≤ V := by
    rintro _ ⟨q, rfl⟩
    exact hcomm (q : D) q.2
  have e : (coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B).relIndex (pCoreOf 2 A) = f.ker.index := by
    rw [hker]
    rfl
  rw [e, Subgroup.index_ker f]
  calc Nat.card f.range ≤ Nat.card V := Subgroup.card_le_of_le hrange
    _ = 4 := h.natural.card_eq

theorem card_pCoreOf_left_le (hU : Nat.card (conjClosure V B) = 8) :
    Nat.card ↥(pCoreOf 2 A) ≤ 4 * Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) := by
  have h1 := Subgroup.relIndex_mul_card (coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) (pCoreOf 2 A)
  rw [inf_eq_left.mpr coreIn_right_le_pCoreOf_left] at h1
  have h2 := h.relIndex_coreIn_pCoreOf_left_le hU
  calc Nat.card ↥(pCoreOf 2 A) = _ := h1.symm
    _ ≤ 4 * _ := Nat.mul_le_mul_right _ h2

theorem card_inf_eq_two_mul_card_pCoreOf_left :
    Nat.card ↥(A ⊓ B) = 2 * Nat.card ↥(pCoreOf 2 A) := by
  have e := Subgroup.relIndex_mul_card (pCoreOf 2 A) (A ⊓ B)
  rw [inf_eq_left.mpr h.gold.pCoreOf_left_le, h.gold.relIndex_pCoreOf_T_left] at e
  exact e.symm

theorem card_coreIn_le_four_mul_inf_conjSub (hU : Nat.card (conjClosure V B) = 8) {y : D}
    (hy : y ∈ A) :
    Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) ≤
      4 * Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B ⊓
        conjSub y (coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B)) := by
  set K : Subgroup D := coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B with hK
  have hKQ : K ≤ pCoreOf 2 A := coreIn_right_le_pCoreOf_left
  have hKyQ : conjSub y K ≤ pCoreOf 2 A := by
    have := conjSub_mono y hKQ
    rwa [conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 A hy)] at this
  have h1 : K.relIndex (conjSub y K) ≤ 4 := by
    have h2 := Subgroup.relIndex_le_of_le_right (H := K) hKyQ
      (relIndex_ne_zero_of_finite K (pCoreOf 2 A))
    exact h2.trans (h.relIndex_coreIn_pCoreOf_left_le hU)
  have h3 := Subgroup.relIndex_mul_card (K ⊓ conjSub y K) (conjSub y K)
  rw [Subgroup.inf_relIndex_right, inf_eq_left.mpr (inf_le_right : K ⊓ conjSub y K ≤ conjSub y K),
    card_conjSub] at h3
  calc Nat.card ↥K = K.relIndex (conjSub y K) * Nat.card ↥(K ⊓ conjSub y K) := h3.symm
    _ ≤ 4 * Nat.card ↥(K ⊓ conjSub y K) := Nat.mul_le_mul_right _ h1

theorem critDist_eq_three_of_inf_conjSub_le {y : D} (hy : y ∈ A)
    (hN : coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B ⊓
      conjSub y (coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) ≤ V) :
    critDist (A ⊔ B) A B V = 3 := by
  have h3 := h.three_le_critDist
  by_contra hne
  have h4 : 4 ≤ critDist (A ⊔ B) A B V := by omega
  have hW := h.four_le_critDist_iff_le_coreIn.mp h4
  have hUK := h.conjClosure_le_coreIn
  have hUKy : conjClosure V B ≤ conjSub y (coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) := by
    intro u hu
    rw [mem_conjSub]
    apply hW
    have hmem : y⁻¹ * u * y⁻¹⁻¹ ∈ conjSub y⁻¹ (conjClosure V B) := mul_mem_conjSub hu
    rw [inv_inv] at hmem
    exact HypF91.conjSub_le_conjClosure (A.inv_mem hy) hmem
  exact h.not_conjClosure_le fun u hu => hN ⟨hUK hu, hUKy hu⟩

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
