module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cU

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem zpowers_cases (h : GoldHyp3 A B z V) {w : D} (hw : w ∈ Subgroup.zpowers z) :
    w = 1 ∨ w = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact zpow_eq_one_or_self h.natural.z_sq k

theorem zpowers_comm_B (h : GoldHyp3 A B z V) {b w : D} (hb : b ∈ B)
    (hw : w ∈ Subgroup.zpowers z) : b * w = w * b := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ((show Commute b z from mul_eq_of_conj_eq (h.central b hb)).zpow_right k).eq

theorem conj_zpowers_B (h : GoldHyp3 A B z V) {b w : D} (hb : b ∈ B)
    (hw : w ∈ Subgroup.zpowers z) : b * w * b⁻¹ = w := by
  rw [zpowers_comm_B h hb hw]; group

variable [Finite D] in
@[expose] def commHom (h : GoldHyp3 A B z V) {p : D} (hp : p ∈ conjClosure V B) :
    ↥(pCoreOf 2 B) →* ↥(Subgroup.zpowers z) where
  toFun q := ⟨p * q * p⁻¹ * (q : D)⁻¹, h.commutator_mem p hp q q.2⟩
  map_one' := by
    apply Subtype.ext
    show p * (1 : D) * p⁻¹ * (1 : D)⁻¹ = 1
    group
  map_mul' q q' := by
    apply Subtype.ext
    show p * ((q : D) * q') * p⁻¹ * ((q : D) * q')⁻¹ =
      (p * q * p⁻¹ * (q : D)⁻¹) * (p * q' * p⁻¹ * (q' : D)⁻¹)
    have hu := h.commutator_mem p hp q' q'.2
    have hq : (q : D) * (p * q' * p⁻¹ * (q' : D)⁻¹) = (p * q' * p⁻¹ * (q' : D)⁻¹) * q :=
      zpowers_comm_B h (pCoreOf_le 2 B q.2) hu
    calc p * ((q : D) * q') * p⁻¹ * ((q : D) * q')⁻¹
        = (p * q * p⁻¹ * (q : D)⁻¹) * ((q : D) * (p * q' * p⁻¹ * (q' : D)⁻¹) * (q : D)⁻¹) := by
          group
      _ = (p * q * p⁻¹ * (q : D)⁻¹) * (p * q' * p⁻¹ * (q' : D)⁻¹) := by rw [hq]; group

variable [Finite D] in
theorem commHom_apply (h : GoldHyp3 A B z V) {p : D} (hp : p ∈ conjClosure V B)
    (q : ↥(pCoreOf 2 B)) :
    ((commHom h hp q : ↥(Subgroup.zpowers z)) : D) = p * q * p⁻¹ * (q : D)⁻¹ := rfl

section Psi

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

@[expose] def psi (g : Gen3 A B z V x a a₁ a₂) :
    ↥(pCoreOf 2 B) →* ↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z) :=
  (commHom g.hyp g.a_mem_U).prod (commHom g.hyp g.a₁_mem_U)

include g

theorem Gen3.mem_U_cases (hU : Nat.card (conjClosure V B) = 8) {u : D}
    (hu : u ∈ conjClosure V B) : u ∈ V ∨ ∃ v ∈ V, u = v * a₁ := by
  by_cases huV : u ∈ V
  · exact Or.inl huV
  · right
    have h1 := g.mul_inv_mem_V_of_not_mem hU hu g.a₁_mem_U huV g.a₁_not_mem_V
    exact ⟨u * a₁⁻¹, h1, by group⟩

theorem Gen3.comm_U_of (hU : Nat.card (conjClosure V B) = 8) {q : D} (hq : q ∈ B)
    (hqa : a * q = q * a) (hqa₁ : a₁ * q = q * a₁) {u : D} (hu : u ∈ conjClosure V B) :
    u * q = q * u := by
  have hzq : z * q = q * z := (g.z_comm hq).symm
  have hV : ∀ v ∈ V, v * q = q * v := by
    intro v hv
    rcases g.mem_V_iff.mp hv with rfl | rfl | rfl | rfl
    · simp
    · exact hzq
    · exact hqa
    · calc z * a * q = z * (a * q) := by group
        _ = z * (q * a) := by rw [hqa]
        _ = (z * q) * a := by group
        _ = (q * z) * a := by rw [hzq]
        _ = q * (z * a) := by group
  rcases g.mem_U_cases hU hu with huV | ⟨v, hv, rfl⟩
  · exact hV u huV
  · calc v * a₁ * q = v * (a₁ * q) := by group
      _ = v * (q * a₁) := by rw [hqa₁]
      _ = (v * q) * a₁ := by group
      _ = (q * v) * a₁ := by rw [hV v hv]
      _ = q * (v * a₁) := by group

theorem Gen3.mem_ker_psi (hU : Nat.card (conjClosure V B) = 8) (q : ↥(pCoreOf 2 B)) :
    q ∈ (psi g).ker ↔
      (q : D) ∈ pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) := by
  have hcomm : ∀ {p : D} (hp : p ∈ conjClosure V B),
      (commHom g.hyp hp q = 1 ↔ p * (q : D) = (q : D) * p) := by
    intro p hp
    constructor
    · intro h1
      have h2 := congrArg (fun w : ↥(Subgroup.zpowers z) => (w : D)) h1
      simp only [commHom_apply, OneMemClass.coe_one] at h2
      calc p * (q : D) = (p * q * p⁻¹ * (q : D)⁻¹) * ((q : D) * p) := by group
        _ = (q : D) * p := by rw [h2, one_mul]
    · intro h1
      apply Subtype.ext
      rw [commHom_apply]
      calc p * (q : D) * p⁻¹ * (q : D)⁻¹ = ((q : D) * p) * p⁻¹ * (q : D)⁻¹ := by rw [h1]
        _ = 1 := by group
  constructor
  · intro hq
    rw [MonoidHom.mem_ker] at hq
    have h1 : commHom g.hyp g.a_mem_U q = 1 := congrArg Prod.fst hq
    have h2 : commHom g.hyp g.a₁_mem_U q = 1 := congrArg Prod.snd hq
    refine ⟨q.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact g.comm_U_of hU (pCoreOf_le 2 B q.2) ((hcomm g.a_mem_U).mp h1)
      ((hcomm g.a₁_mem_U).mp h2) hw
  · intro hq
    rw [MonoidHom.mem_ker]
    have hc : ∀ {p : D}, p ∈ conjClosure V B → p * (q : D) = (q : D) * p := fun {p} hp =>
      Subgroup.mem_centralizer_iff.mp hq.2 p hp
    exact Prod.ext ((hcomm g.a_mem_U).mpr (hc g.a_mem_U))
      ((hcomm g.a₁_mem_U).mpr (hc g.a₁_mem_U))

end Psi

end GoldAmL3c

end F6

end CFSG.Quasithin
