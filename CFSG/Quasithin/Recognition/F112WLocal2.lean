module

public import CFSG.Quasithin.Recognition.F112WLocal
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Recognition.F112WSetup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace F112W

section Comm

variable {G : Type*} [Group G]

theorem commutator_conjClosure_le {H V Q Z : Subgroup G} (hVH : V ≤ H)
    (hQ : H ≤ Subgroup.normalizer (Q : Set G)) (hZ : H ≤ Subgroup.normalizer (Z : Set G))
    (h : ⁅V, Q⁆ ≤ Z) : ⁅conjClosure V H, Q⁆ ≤ Z := by
  have hCH : conjClosure V H ≤ H := conjClosure_le fun h' hh' z hz =>
    H.mul_mem (H.mul_mem hh' (hVH hz)) (H.inv_mem hh')
  rw [Subgroup.commutator_le]
  intro u hu q hq
  show u * q * u⁻¹ * q⁻¹ ∈ Z
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h', hh', v, hv, rfl⟩ := hx
    have hq' : h'⁻¹ * q * h' ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hQ (H.inv_mem hh')) q).mp hq
      simpa using this
    have h1 : v * (h'⁻¹ * q * h') * v⁻¹ * (h'⁻¹ * q * h')⁻¹ ∈ Z :=
      h (Subgroup.commutator_mem_commutator hv hq')
    have h2 := (Subgroup.mem_normalizer_iff.mp (hZ hh') _).mp h1
    have e : h' * v * h'⁻¹ * q * (h' * v * h'⁻¹)⁻¹ * q⁻¹ =
        h' * (v * (h'⁻¹ * q * h') * v⁻¹ * (h'⁻¹ * q * h')⁻¹) * h'⁻¹ := by group
    rw [e]
    exact h2
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxH : x ∈ H := hCH hx
    have e : x * y * q * (x * y)⁻¹ * q⁻¹ =
        (x * (y * q * y⁻¹ * q⁻¹) * x⁻¹) * (x * q * x⁻¹ * q⁻¹) := by group
    rw [e]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hZ hxH) _).mp ihy) ihx
  | inv x hx ih =>
    have hxH : x ∈ H := hCH hx
    have e : x⁻¹ * q * (x⁻¹)⁻¹ * q⁻¹ = x⁻¹ * (x * q * x⁻¹ * q⁻¹)⁻¹ * x := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff''.mp (hZ hxH) _).mp (Z.inv_mem ih)

variable {G₀ G₁ G₂ T V : Subgroup G} [Finite G]

theorem commutator_V_T (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hS : IsNaturalS3 G₁ V)
    (hb : critDist G₀ G₁ G₂ V = 2) : ⁅V, T⁆ = V ⊓ Subgroup.centralizer (T : Set G) := by
  have hV := hS.ne_bot
  obtain ⟨-, -, -, x, hxG₂, hWU, hWG, hT, -, hcomm, hVW, hc2, -⟩ := critDist_two_structure hyp hS hb
  have hVT : V ≤ T := (V_le_pCoreOf hyp).trans (isSylowTwoOf_pCoreOf_le hyp.sylow₁)
  have hWT : conjSub x V ≤ T := hT ▸ le_sup_right
  have hZle : V ⊓ Subgroup.centralizer (T : Set G) ≤ ⁅V, T⁆ := by
    rw [← hVW, ← hcomm]
    exact Subgroup.commutator_mono le_rfl hWT
  have hVN : V ≤ Subgroup.normalizer (T : Set G) := hVT.trans Subgroup.le_normalizer
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hyp.sylow₁.1.trans hyp.normalizes
  have hcle : ⁅V, T⁆ ≤ V := (commutator_le_inf_of_normalizes hVN hTN).trans inf_le_left
  have hlt : ⁅V, T⁆ < V := by
    refine lt_of_le_of_ne hcle fun h => ?_
    have := D14.le_of_le_commutator_sup (V := ⊥) hyp.sylow₁.2.1 hVT
      (fun t _ => by rw [Subgroup.mem_normalizer_iff]; intro y; simp [Subgroup.mem_bot])
      (by rw [sup_bot_eq, h])
    exact hV (le_bot_iff.mp this)
  have hcZ : Nat.card ↥(V ⊓ Subgroup.centralizer (T : Set G)) = 2 := card_inf_centralizer_T hyp hS
  have hlt' : Nat.card ↥⁅V, T⁆ < 4 := hS.card_eq ▸ Subgroup.card_lt_of_lt hlt
  have hd : Nat.card ↥⁅V, T⁆ ∣ 4 := hS.card_eq ▸ Subgroup.card_dvd_of_le hlt.le
  have h2 : Nat.card ↥⁅V, T⁆ = 2 := by
    have h1 : 2 ≤ Nat.card ↥⁅V, T⁆ := hcZ ▸ Subgroup.card_le_of_le hZle
    interval_cases hc : Nat.card ↥⁅V, T⁆
    · rfl
    · omega
  exact (Subgroup.eq_of_le_of_card_ge hZle (by rw [h2, hcZ])).symm

theorem commutator_V_pCoreOf (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hS : IsNaturalS3 G₁ V)
    (hb : critDist G₀ G₁ G₂ V = 2) :
    ⁅V, pCoreOf 2 G₂⁆ = V ⊓ Subgroup.centralizer (T : Set G) := by
  obtain ⟨-, hUQ, -, x, hxG₂, hWU, hWG, hT, -, hcomm, hVW, hc2, -⟩ := critDist_two_structure hyp hS hb
  have hQT : pCoreOf 2 G₂ ≤ T := isSylowTwoOf_pCoreOf_le hyp.sylow₂
  apply le_antisymm
  · rw [← commutator_V_T hyp hS hb]
    exact Subgroup.commutator_mono le_rfl hQT
  · rw [← hVW, ← hcomm]
    exact Subgroup.commutator_mono le_rfl (hWU.trans hUQ)

theorem commutator_conjClosure_pCoreOf (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hS : IsNaturalS3 G₁ V)
    (hb : critDist G₀ G₁ G₂ V = 2)
    (hZ : G₂ ≤ Subgroup.normalizer ((V ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) : Set G)) :
    ⁅conjClosure V G₂, pCoreOf 2 G₂⁆ = V ⊓ Subgroup.centralizer (T : Set G) := by
  have hVQ := le_pCoreOf_G₂_of_critDist_eq_two hyp hS.ne_bot hb
  apply le_antisymm
  · exact commutator_conjClosure_le (hVQ.trans (pCoreOf_le 2 G₂)) (le_normalizer_pCoreOf 2 G₂) hZ
      (commutator_V_pCoreOf hyp hS hb).le
  · rw [← commutator_V_pCoreOf hyp hS hb]
    exact Subgroup.commutator_mono (le_conjClosure V G₂) le_rfl

theorem commutator_conjClosure_self (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hS : IsNaturalS3 G₁ V)
    (hb : critDist G₀ G₁ G₂ V = 2)
    (hZ : G₂ ≤ Subgroup.normalizer ((V ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) : Set G)) :
    ⁅conjClosure V G₂, conjClosure V G₂⁆ = V ⊓ Subgroup.centralizer (T : Set G) := by
  obtain ⟨-, hUQ, -, x, hxG₂, hWU, hWG, hT, -, hcomm, hVW, hc2, -⟩ := critDist_two_structure hyp hS hb
  apply le_antisymm
  · rw [← commutator_conjClosure_pCoreOf hyp hS hb hZ]
    exact Subgroup.commutator_mono le_rfl hUQ
  · rw [← hVW, ← hcomm]
    exact Subgroup.commutator_mono (le_conjClosure V G₂) hWU

theorem sup_oTwoUpper_eq_of_isSylowTwoOf {H T : Subgroup G} (hT : IsSylowTwoOf T H) :
    T ⊔ oTwoUpper H = H := by
  rw [← F6.twoResidual_eq_oTwoUpper]
  exact sup_twoResidual_eq hT

theorem commutator_V_oTwoUpper_ne_bot (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) :
    ⁅V, oTwoUpper G₂⁆ ≠ ⊥ := by
  intro h
  have hOC : oTwoUpper G₂ ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact h)
  have hG₂N : G₂ ≤ Subgroup.normalizer (V : Set G) := by
    rw [← sup_oTwoUpper_eq_of_isSylowTwoOf hyp.sylow₂]
    exact sup_le ((hyp.T_le.trans inf_le_left).trans hyp.normalizes)
      (hOC.trans (Subgroup.centralizer_le_normalizer _))
  have hG₀N : G₀ ≤ Subgroup.normalizer (V : Set G) := by
    rw [hyp.gen]
    exact sup_le hyp.normalizes hG₂N
  have hVB : V ≤ G₁ ⊓ G₂ :=
    ((V_le_pCoreOf hyp).trans (isSylowTwoOf_pCoreOf_le hyp.sylow₁)).trans hyp.T_le
  have hVcore : V ≤ coreIn (G₁ ⊓ G₂) G₀ := le_coreIn (hVB.trans (inf_le_left.trans hyp.le₁)) hG₀N hVB
  rw [coreIn_eq_bot_of_amalgamHyp hyp.toAmalgamHyp] at hVcore
  exact hV (le_bot_iff.mp hVcore)

theorem commutator_conjClosure_oTwoUpper_ne_bot (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) :
    ⁅conjClosure V G₂, oTwoUpper G₂⁆ ≠ ⊥ := fun h =>
  commutator_V_oTwoUpper_ne_bot hyp hV
    (le_bot_iff.mp ((Subgroup.commutator_mono (le_conjClosure V G₂) le_rfl).trans h.le))

theorem critDist_eq_two_of_commutator_ne_bot (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hVQ : V ≤ pCoreOf 2 G₂) (hna : ⁅conjClosure V G₂, conjClosure V G₂⁆ ≠ ⊥) :
    critDist G₀ G₁ G₂ V = 2 := by
  refine critDist_eq_two_of_nonabelian hyp hV hVQ fun h => hna ?_
  rw [Vv_γ₁ hyp.le₂ hyp.normalizes] at h
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact h y hy x hx

end Comm

end F112W

end CFSG.Quasithin
