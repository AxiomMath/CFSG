module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB16

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem eq_of_card_two {K : Type*} [Group K] {B : Subgroup K} (hB : Nat.card B = 2) {x y : K}
    (hx : x ∈ B) (hy : y ∈ B) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  by_contra hxy
  classical
  have hfin : Finite ↥B := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype ↥B := Fintype.ofFinite _
  have h3 : ({1, ⟨x, hx⟩, ⟨y, hy⟩} : Finset ↥B).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨1, ⟨x, hx⟩, ⟨y, hy⟩, ?_, ?_, ?_, rfl⟩
    · exact fun e => hx1 (congrArg Subtype.val e).symm
    · exact fun e => hy1 (congrArg Subtype.val e).symm
    · exact fun e => hxy (congrArg Subtype.val e)
  have := Finset.card_le_univ ({1, ⟨x, hx⟩, ⟨y, hy⟩} : Finset ↥B)
  rw [h3, Fintype.card_eq_nat_card, hB] at this
  omega

theorem no_cyc3_comm_ab : ∀ c : Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 →
    c * (swap 0 2 * swap 1 3) ≠ (swap 0 2 * swap 1 3) * c := by decide +kernel

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem isThreeCyc (hA : F53Amalgam H M S) (h : ConfR δ μ U) (fr : OrthFrame δ μ) {c : G}
    (hcU : c ∈ U) (hc3 : orderOf c = 3) :
    IsThreeCyc (fr.Ψ ⟨c, h.sig.le_stab hcU⟩) := by
  have hcX : c ∈ stab δ := h.sig.le_stab hcU
  set k : ↥(stab δ) := ⟨c, hcX⟩ with hk
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have h1 : fr.Ψ k ^ 3 = 1 := by
    rw [← map_pow]
    have : k ^ 3 = 1 := Subtype.ext (by simpa using hc3')
    rw [this, map_one]
  have h2 : fr.Ψ k ≠ 1 := fun e => by
    have hmem : c ∈ Qv δ := (fr.ker k).mp e
    obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab δ) ⟨c, hmem⟩
    have hm' : c ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h5 : orderOf c ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
    rw [hc3] at h5
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5
    omega
  set R := pCoreOf 2 U with hR
  have hRP : R ≤ Qv μ := fun x hx => (h.sig.R_le_P hx).1
  have hRF : R ≤ stab δ := (CFSG.LieType.BorelTits.pCoreOf_le 2 U).trans h.sig.le_stab
  have hcardR : Nat.card (fr.img R) = 2 := by
    rw [card_img fr hRF]
    have h3 := Subgroup.relIndex_mul_card (Qv δ) R
    rw [inf_of_le_left h.Qv_le_R] at h3
    have h4 := h.card_R_K hA
    have hpos : 0 < Nat.card (Qv δ) := Nat.card_pos
    rw [inf_of_le_left h.Qv_le_R]
    nlinarith
  obtain ⟨τ, hτ, hτ1⟩ : ∃ τ ∈ fr.img R, τ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : fr.img R = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hcardR
    omega
  have hnorm : c ∈ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 U hcU
  have hτc : fr.Ψ k * τ * (fr.Ψ k)⁻¹ ∈ fr.img R := by
    obtain ⟨x, hx, rfl⟩ := hτ
    refine ⟨k * x * k⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp only [map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.mp hnorm (x : G)).mp (Subgroup.mem_subgroupOf.mp hx)
    simpa [hk] using this
  have hτc1 : fr.Ψ k * τ * (fr.Ψ k)⁻¹ ≠ 1 := fun e => hτ1 (by
    have : τ = (fr.Ψ k)⁻¹ * (fr.Ψ k * τ * (fr.Ψ k)⁻¹) * fr.Ψ k := by group
    rw [this, e]; group)
  have hcomm : fr.Ψ k * τ * (fr.Ψ k)⁻¹ = τ := eq_of_card_two hcardR hτc hτ hτc1 hτ1
  have hcomm' : fr.Ψ k * τ = τ * fr.Ψ k := by
    rw [mul_inv_eq_iff_eq_mul] at hcomm; exact hcomm
  have hT : τ ∈ S5That := img_le_That fr hRP hτ
  rw [mem_S5That_iff, O2.mem_S5ThatF_iff_eq] at hT
  rcases hT with e | e | e | e
  · exact absurd e hτ1
  · rw [e] at hcomm'; exact ⟨h1, h2, Or.inl hcomm'⟩
  · rw [e] at hcomm'; exact ⟨h1, h2, Or.inr hcomm'⟩
  · rw [e] at hcomm'; exact absurd hcomm' (no_cyc3_comm_ab _ h1 h2)

end ConfR

namespace OrthFrame

variable {δ μ : Geo H M} (fr : OrthFrame δ μ)

theorem map_top : (⊤ : Subgroup orth.W).map fr.γ = OoOf δ := by
  ext x
  constructor
  · rintro ⟨w, -, rfl⟩; exact fr.mem w
  · intro hx
    obtain ⟨w, rfl⟩ := fr.surj x hx
    exact ⟨w, trivial, rfl⟩

theorem img_zpowers {c : G} (hc : c ∈ stab δ) :
    fr.img (Subgroup.zpowers c) = Subgroup.zpowers (fr.Ψ ⟨c, hc⟩) := by
  unfold OrthFrame.img
  have : (Subgroup.zpowers c).subgroupOf (stab δ) = Subgroup.zpowers (⟨c, hc⟩ : ↥(stab δ)) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp⟩
  rw [this, MonoidHom.map_zpowers]

theorem comm_Oo_zpowers {c : G} (hc : c ∈ stab δ) :
    ⁅OoOf δ, Subgroup.zpowers c⁆ = (planeOf (fr.Ψ ⟨c, hc⟩)).map fr.γ := by
  rw [Subgroup.commutator_comm, ← fr.map_top, fr.comm_map _ ((Subgroup.zpowers_le).mpr hc),
    fr.img_zpowers hc]
  rfl

end OrthFrame

end CFSG.Quasithin.F53
