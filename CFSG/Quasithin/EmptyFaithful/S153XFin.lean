module

public import CFSG.Quasithin.EmptyFaithful.S153XLoc
public import CFSG.Quasithin.EmptyFaithful.ModFA5J

public section

namespace CFSG.Quasithin.X1469

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.ModF CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

def modCent (Q Z : Subgroup G) (h : Q ≤ Subgroup.normalizer (Z : Set G)) : Subgroup G where
  carrier := {q | q ∈ Q ∧ ∀ q' ∈ Q, q * q' * q⁻¹ * q'⁻¹ ∈ Z}
  one_mem' := ⟨Q.one_mem, fun q' _ => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, fun q' hq' => by
    have e : a * b * q' * (a * b)⁻¹ * q'⁻¹ =
        (a * (b * q' * b⁻¹ * q'⁻¹) * a⁻¹) * (a * q' * a⁻¹ * q'⁻¹) := by group
    rw [e]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.1 (h ha.1) _).1 (hb.2 q' hq')) (ha.2 q' hq')⟩
  inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, fun q' hq' => by
    have e : a⁻¹ * q' * a⁻¹⁻¹ * q'⁻¹ = a⁻¹ * (a * q' * a⁻¹ * q'⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (h (Q.inv_mem ha.1)) _).1 (Z.inv_mem (ha.2 q' hq'))⟩

omit [Finite G] in
theorem mem_normalizer_modCent {Q Z : Subgroup G} {h : Q ≤ Subgroup.normalizer (Z : Set G)} {g : G}
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G)) (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    g ∈ Subgroup.normalizer (modCent Q Z h : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (Q : Set G), g ∈ Subgroup.normalizer (Z : Set G) →
      ∀ f ∈ modCent Q Z h, g * f * g⁻¹ ∈ modCent Q Z h := by
    intro g hgQ hgZ f hf
    refine ⟨(Subgroup.mem_normalizer_iff.1 hgQ f).1 hf.1, fun q' hq' => ?_⟩
    have hq'' : g⁻¹ * q' * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hgQ) q').1 hq'
      simpa using this
    have e : g * f * g⁻¹ * q' * (g * f * g⁻¹)⁻¹ * q'⁻¹ =
        g * (f * (g⁻¹ * q' * g) * f⁻¹ * (g⁻¹ * q' * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 hgZ _).1 (hf.2 _ hq'')
  rw [Subgroup.mem_normalizer_iff]
  intro f
  refine ⟨key g hgQ hgZ f, fun hf => ?_⟩
  have := key g⁻¹ (inv_mem hgQ) (inv_mem hgZ) _ hf
  simpa [mul_assoc] using this

section Core

variable {I S Iz K₁ K₂ T : Subgroup G} {r z : G}

theorem fin_core (C : LocalCfg I S Iz K₁ K₂ T r z) (L : LocalFacts I S Iz r z)
    (hPhi : ∀ g ∈ Subgroup.centralizer ({z} : Set G),
      (∀ q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)),
        g * q * g⁻¹ * q⁻¹ ∈ omegaOneCenterOf (pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) →
      g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))
    (hc : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≤ pCoreOf 2 Iz)
    (he : omegaOneCenterOf (pCoreOf 2 Iz) ≤
      omegaOneCenterOf (pCoreOf 2 (Subgroup.centralizer ({z} : Set G))))
    (V : Subgroup G) (hV4 : Nat.card V = 4)
    (hV15 : V ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
      ∀ v ∈ V, ∀ q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)),
        v * q * v⁻¹ * q⁻¹ ∈ Subgroup.zpowers z)
    (hVN : ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (V : Set G)) : False := by
  set G1 : Subgroup G := Subgroup.centralizer ({z} : Set G) with hG1
  set Q1 : Subgroup G := pCoreOf 2 G1 with hQ1
  set Z1 : Subgroup G := omegaOneCenterOf Q1 with hZ1
  have hcfg := C.cfg
  have hIzG1 : Iz ≤ G1 := by rw [C.hIz]; exact inf_le_right
  have hSIz : S ≤ Iz := hcfg.S_le_Iz
  have hIzI : Iz ≤ I := hcfg.Iz_le_I
  have hRzS : rz Iz ≤ S := hcfg.R_le_S
  have hQRz : pCoreOf 2 I ≤ rz Iz := hcfg.Q_le_R
  have hSG1 : S ≤ G1 := hSIz.trans hIzG1
  have hTG1 : T ≤ G1 := fun y hy => Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff.1 hh]; exact (C.hzc y hy).symm
  have hrT : r ∈ T := C.hrT
  have hrG1 : r ∈ G1 := hTG1 hrT
  have hQ1Rz : Q1 ≤ rz Iz := hc
  have hQ1S : Q1 ≤ S := hQ1Rz.trans hRzS
  have hG1Q1 : G1 ≤ Subgroup.normalizer (Q1 : Set G) := le_normalizer_pCoreOf 2 G1
  have hG1Z1 : G1 ≤ Subgroup.normalizer (Z1 : Set G) :=
    hG1Q1.trans (A4.normalizer_le_normalizer_omegaOneCenterOf Q1)
  have hQ1N : Q1 ≤ Subgroup.normalizer (Z1 : Set G) := fun x hx => hG1Z1 (pCoreOf_le 2 G1 hx)
  have hZ1le : Z1 ≤ centerOf Q1 :=
    (Subgroup.closure_le (centerOf Q1)).mpr fun x hx => hx.1
  have hZ1Q1 : Z1 ≤ Q1 := fun x hx => (hZ1le hx).1
  have hZ1C : ∀ x ∈ Z1, ∀ q ∈ Q1, x * q * x⁻¹ * q⁻¹ = 1 := fun x hx q hq => by
    have := Subgroup.mem_centralizer_iff.1 (hZ1le hx).2 q hq
    rw [← this]
    simp [mul_assoc]
  set F : Subgroup G := modCent Q1 Z1 hQ1N with hF
  have hFQ1 : F ≤ Q1 := fun x hx => hx.1
  have hFN : G1 ≤ Subgroup.normalizer (F : Set G) := fun g hg =>
    mem_normalizer_modCent (hG1Q1 hg) (hG1Z1 hg)
  have hZ1F : Z1 ≤ F := fun x hx => ⟨hZ1Q1 hx, fun q hq => by rw [hZ1C x hx q hq]; exact Z1.one_mem⟩
  have hz0Z1 : z0 Iz ≤ Z1 := he
  have hQIN : I ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) := le_normalizer_pCoreOf 2 I
  obtain ⟨K', P, E0, hK'Iz, hPRz, hE0P, hE0N, hQK, hPle, hRPQ, hcentP, hcentU, hcenterPmod, hirrE0,
    ⟨x₀, hx₀E, hx₀Z, hx₀S⟩, ⟨e, heE, heQ⟩⟩ := L.exists_sub
  have hQKz : ∀ q ∈ pCoreOf 2 I, ∀ k ∈ K', q * k * q⁻¹ * k⁻¹ ∈ E0 := fun q hq k hk =>
    hQK (Subgroup.commutator_mem_commutator hq hk)
  have hx₀S' : x₀ ∈ S := hRzS (hPRz (hE0P hx₀E))
  have hx₀Q1 : x₀ ∈ Q1 := hPhi x₀ (hSG1 hx₀S') fun q hq => hz0Z1 (hx₀S q (hQ1S hq))
  have hx₀F : x₀ ∈ F := ⟨hx₀Q1, fun q hq => hz0Z1 (hx₀S q (hQ1S hq))⟩
  have hE0F : E0 ≤ F := by
    have hirr := hirrE0 (F ⊓ E0) inf_le_right (fun g hg => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.1 (hFN (hIzG1 hg)) y
      have h2 := Subgroup.mem_normalizer_iff.1 (hE0N hg) y
      exact ⟨fun hy => ⟨h1.1 hy.1, h2.1 hy.2⟩, fun hy => ⟨h1.2 hy.1, h2.2 hy.2⟩⟩)
    rcases hirr with h | h
    · exact absurd (h ⟨hx₀F, hx₀E⟩) hx₀Z
    · exact h.trans (sup_le inf_le_left (hz0Z1.trans hZ1F))
  have hreF : r * e * r⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.1 (hFN hrG1) e).1 (hE0F heE)
  have hFRz : F ≤ rz Iz := hFQ1.trans hQ1Rz
  have hFnotQ : ¬ F ≤ pCoreOf 2 I := fun h => heQ (h hreF)
  have hFQ : F ⊔ pCoreOf 2 I = rz Iz := by
    rcases L.irred_Rz F hFRz (fun g hg => hFN (hIzG1 hg)) with h | h
    · exact absurd h hFnotQ
    · exact h
  have hFI : F ≤ I := hFRz.trans (hRzS.trans (hSIz.trans hIzI))
  have hFNQ : F ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) := hFI.trans hQIN
  have hcomm : ⁅rz Iz, K'⁆ ≤ F := by
    rw [Subgroup.commutator_le]
    intro x hx k hk
    have hx' : x ∈ ((F : Subgroup G) : Set G) * ((pCoreOf 2 I : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right F (pCoreOf 2 I) hFNQ, hFQ]
      exact hx
    obtain ⟨f, hf, q, hq, rfl⟩ := hx'
    have hkG1 : k ∈ G1 := hIzG1 (hK'Iz hk)
    have h1 : (f * q) * k * (f * q)⁻¹ * k⁻¹ =
        (f * (q * k * q⁻¹ * k⁻¹) * f⁻¹) * (f * k * f⁻¹ * k⁻¹) := by group
    show ⁅f * q, k⁆ ∈ F
    rw [commutatorElement_def, h1]
    refine F.mul_mem ?_ ?_
    · have hqk : q * k * q⁻¹ * k⁻¹ ∈ F := hE0F (hQKz q hq k hk)
      exact (Subgroup.mem_normalizer_iff.1 (hFN (hSG1 (hRzS (hFRz hf)))) _).1 hqk
    · have hfk : k * f⁻¹ * k⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.1 (hFN hkG1) _).1 (F.inv_mem hf)
      have e : f * k * f⁻¹ * k⁻¹ = f * (k * f⁻¹ * k⁻¹) := by group
      rw [e]
      exact F.mul_mem hf hfk
  have hPF : P ≤ F := hPle.trans (sup_le hcomm hE0F)
  have hZ1z0 : Z1 ≤ z0 Iz := by
    intro x hx
    refine hcentP x (hQ1Rz (hZ1Q1 hx)) fun p hp => ?_
    exact hZ1C x hx p (hFQ1 (hPF hp))
  have hZ1eq : Z1 = z0 Iz := le_antisymm hZ1z0 hz0Z1
  have hQ1P : Q1 ≤ P := by
    intro q hq
    have hPN : P ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) :=
      (hPRz.trans (hRzS.trans (hSIz.trans hIzI))).trans hQIN
    have hq' : q ∈ ((P : Subgroup G) : Set G) * ((pCoreOf 2 I : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right P (pCoreOf 2 I) hPN]
      exact hRPQ (hQ1Rz hq)
    obtain ⟨p, hp, u, hu, rfl⟩ := hq'
    have hu1 : u ∈ Q1 := by
      have := Q1.mul_mem (Q1.inv_mem (hFQ1 (hPF hp))) hq
      simpa [mul_assoc] using this
    refine P.mul_mem hp (hcentU u hu fun p' hp' => ?_)
    have h1 : p' * u * p'⁻¹ * u⁻¹ ∈ Z1 := (hPF hp').2 u hu1
    have e : u * p' * u⁻¹ * p'⁻¹ = (p' * u * p'⁻¹ * u⁻¹)⁻¹ := by group
    rw [e, ← hZ1eq]
    exact Z1.inv_mem h1
  have hPQ1 : P = Q1 := le_antisymm (hPF.trans hFQ1) hQ1P
  have hVz0 : V ≤ z0 Iz := by
    intro v hv
    refine hcenterPmod v (hQ1P (hV15.1 hv)) fun p hp => ?_
    exact hV15.2 v hv p (hPQ1 ▸ hp)
  have hVeq : V = z0 Iz := by
    refine (Subgroup.eq_of_le_of_card_ge hVz0 ?_)
    rw [hV4, L.card_z0]
  apply hVN
  rw [hVeq, ← hZ1eq]
  exact hG1Z1

end Core

end CFSG.Quasithin.X1469
