module

public import CFSG.Milestones.ASVolI.C135.NG
public import CFSG.Milestones.ASVolI.C135.P4b

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4.C135 (QC cnj coe_cnj slNat slNat_surjective dualHom coe_dualHom
  dualHom_dualHom moduleAct_true_eq le_normalizer_centerOf le_normalizer_bot fixAll msPair_facts
  card_le_mul_card_inf mul_comm_of_isElemAbelian)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem burnsideC135_two_mul_card_le {S V : Subgroup G} (hSV : S ≤ V) (hne : ¬ V ≤ S) :
    2 * Nat.card S ≤ Nat.card V := by
  have e := Subgroup.relIndex_mul_card S V
  rw [inf_eq_left.mpr hSV] at e
  have h1 : S.relIndex V ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.mp h)
  have h0 : S.relIndex V ≠ 0 := by
    intro h
    rw [h, zero_mul] at e
    exact Nat.card_pos.ne e
  rw [← e]
  exact Nat.mul_le_mul_right _ (by omega)

theorem burnsideC135_isElemAbelian_mono {A B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hAB : A ≤ B) : IsElemAbelian 2 A :=
  ⟨⟨⟨fun a b => Subtype.ext (mul_comm_of_isElemAbelian hB (hAB a.2) (hAB b.2))⟩⟩,
    fun x hx => hB.2 x (hAB hx)⟩

namespace burnsideC135_H1

variable {X R L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)} {β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F)}
  {βU : ↥(centerOf (c134Q X L)) →* Multiplicative (Fin 3 → F)}
  (H : burnsideC135_H1 X R L α β βU)
include H

theorem pCoreOf_eq : pCoreOf 2 X = c134Q X L := by
  classical
  refine le_antisymm ?_ H.Q_le
  by_contra hTQ
  obtain ⟨A, hAmax, hAT⟩ := H.exists_maxElemAbelian_not_le
  obtain ⟨hRX, hTR, -⟩ := msPair_facts H.ms
  have hAR : A ≤ R := hAmax.1
  have hAX : A ≤ X := hAR.trans hRX
  have hA : IsElemAbelian 2 A := hAmax.2.1
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    mul_comm_of_isElemAbelian hA hx hy
  have hVel := H.isElemAbelian_V
  have hVA : Nat.card ↥(pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)) ≤
      Nat.card A := hAmax.2.2 _ (inf_le_left.trans hTR) hVel
  obtain ⟨o1, o2⟩ := H.offender hAX hA hAT
  have hFc : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, H.card]
  rw [hFc] at o1 o2
  have hAB := H.card_le_range_mul hAX
  have hAU := H.card_inf_U_le hAX hA
  have hAW := H.card_inf_W_le hAX hA
  set a := Nat.card (H.q0.rep (hAX.trans H.normU) (le_normalizer_bot A)).range with ha
  set f₀ := Nat.card (fixAll (H.q0.rep (hAX.trans H.normU) (le_normalizer_bot A))) with hf₀
  set f₁ := Nat.card (fixAll (H.q1.rep (hAX.trans H.normW) (hAX.trans H.normU))) with hf₁
  set f₂ := Nat.card (fixAll (H.q2.rep (hAX.trans H.normQ) (hAX.trans H.normW))) with hf₂
  have hW₁ : Nat.card ↥(burnsideC135_Wc β 1) = 2 ^ 6 := by
    rw [burnsideC135_card_dual H.dsg H.dsg.le₁ H.dsg.dual₁_onto H.dsg.dual₁_ker, H.card]
  have hproj : ∀ S : Set (Fin 3 → F), (∀ t ∈ A ⊓ pCoreOf 2 X, H.proj t ∈ S) →
      Nat.card ↥(A ⊓ pCoreOf 2 X) ≤ Nat.card ↥(A ⊓ (pCoreOf 2 X ⊓
        Subgroup.centralizer (burnsideC135_Wc β 1 : Set G))) * Nat.card S := by
    intro S hS
    refine burnsideC135_card_le_of_hom (inf_le_inf_left _ inf_le_left)
      (fun t => H.proj (t : G)) (fun x y => H.proj_mul x.2.2 y.2.2) (fun x => ?_) S
      (fun x => hS x x.2)
    show H.proj (x : G) = 0 ↔ _
    rw [H.proj_eq_zero_iff x.2.2]
    exact ⟨fun h => ⟨x.2.1, h⟩, fun h => h.2⟩
  have hfix₂ : ∀ t ∈ A ⊓ pCoreOf 2 X,
      H.proj t ∈ {y | ∀ a', H.q2.rep (hAX.trans H.normQ) (hAX.trans H.normW) a' y = y} := by
    intro t ht a'
    rw [← H.proj_conj hAX a' ht.2]
    congr 1
    rw [hcommA _ a'.2 t ht.1]
    group
  by_cases h₁ : ∃ v ∈ A ⊓ (pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)),
      ¬ ∀ q ∈ c134Q X L, v * q * v⁻¹ * q⁻¹ ∈ centerOf (c134Q X L)
  ·
    obtain ⟨v, hv, hnt⟩ := h₁
    have hATV : A ⊓ pCoreOf 2 X ≤
        A ⊓ (pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)) := fun t ht =>
      ⟨ht.1, H.le_V_of_nontriv hv.2 hnt ht.2 (hcommA t ht.1 v hv.1)⟩
    have h1 := hVA.trans (hAB.trans (Nat.mul_le_mul_left a (Subgroup.card_le_of_le hATV)))
    have h2 := card_le_mul_card_inf inf_le_right H.W₁_le_V h1
    have h3 : Nat.card ↥(A ⊓ (pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)) ⊓
        burnsideC135_Wc β 1) ≤ Nat.card ↥(A ⊓ burnsideC135_Wc β 1) :=
      Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)
    rw [hW₁] at h2
    have h4 := h2.trans (Nat.mul_le_mul_left a (h3.trans hAW))
    have e : a * 2 * f₀ * f₁ = 2 * (a * (f₀ * f₁)) := by ring
    omega
  push Not at h₁
  have hAVS : A ⊓ (pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)) ≤
      A ⊓ (burnsideC135_Wc β 1 ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G))) :=
    fun v hv => ⟨hv.1, H.mem_sup_of_triv hv.2 (h₁ v hv)⟩
  set k := (burnsideC135_Wc β 1).relIndex
    (burnsideC135_Wc β 1 ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G))) with hk
  have hkS : k * Nat.card ↥(burnsideC135_Wc β 1) = Nat.card ↥(burnsideC135_Wc β 1 ⊔
      (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G))) := by
    have e := Subgroup.relIndex_mul_card (burnsideC135_Wc β 1)
      (burnsideC135_Wc β 1 ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)))
    rwa [inf_eq_left.mpr (le_sup_left : burnsideC135_Wc β 1 ≤ burnsideC135_Wc β 1 ⊔
      (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)))] at e
  have hAS : Nat.card ↥(A ⊓ (burnsideC135_Wc β 1 ⊔
      (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)))) ≤
      k * Nat.card ↥(A ⊓ burnsideC135_Wc β 1) := by
    have h1 := card_le_mul_card_inf (le_sup_left : burnsideC135_Wc β 1 ≤ _)
      (inf_le_right : A ⊓ (burnsideC135_Wc β 1 ⊔
        (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G))) ≤ _) hkS.ge
    exact h1.trans (Nat.mul_le_mul_left k (Subgroup.card_le_of_le
      (fun x hx => ⟨hx.2.1, hx.1⟩)))
  have hAV : Nat.card ↥(A ⊓ (pCoreOf 2 X ⊓
      Subgroup.centralizer (burnsideC135_Wc β 1 : Set G))) ≤
      k * Nat.card ↥(A ⊓ burnsideC135_Wc β 1) := (Subgroup.card_le_of_le hAVS).trans hAS
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, zero_mul] at hkS
      exact absurd hkS.symm Nat.card_pos.ne'
    · exact h
  by_cases h₂ : ∃ v₀ ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G),
      ¬ ∀ q ∈ c134Q X L, v₀ * q * v₀⁻¹ * q⁻¹ ∈ centerOf (c134Q X L)
  ·
    obtain ⟨v₀, hv₀, hnt⟩ := h₂
    have hv₀S : ¬ (pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) ≤
        burnsideC135_Wc β 1 ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G))) :=
      fun h => hnt (H.triv_of_mem_sup (h hv₀))
    have hV2 := burnsideC135_two_mul_card_le H.sup_le_V hv₀S
    rw [← hkS, hW₁] at hV2
    by_cases h₃ : ∃ w ∈ A ⊓ burnsideC135_Wc β 1, w ∉ centerOf (c134Q X L)
    ·
      obtain ⟨w, hw, hwU⟩ := h₃
      have hline : ∀ t ∈ A ⊓ pCoreOf 2 X, H.proj t ∈ {y : Fin 3 → F | ∃ c : F,
          y = c • Multiplicative.toAdd (β ⟨w, burnsideC135_Wc_le 1 hw.2⟩) 0} := by
        intro t ht
        obtain ⟨v, hv, q, hq, rfl⟩ := H.exists_V_mul ht.2
        rw [H.proj_eq hv hq rfl, burnsideC135_qc_of_mem hq]
        have hvw : w * v = v * w := Subgroup.mem_centralizer_iff.mp hv.2 w hw.2
        have htw : (v * q) * w = w * (v * q) := hcommA _ ht.1 w hw.1
        have hqw : w * q = q * w := by
          have h1 : v * (q * w) = v * (w * q) := by
            calc v * (q * w) = (v * q) * w := by group
              _ = w * (v * q) := htw
              _ = (w * v) * q := by group
              _ = v * (w * q) := by rw [hvw]; group
          exact (mul_left_cancel h1).symm
        exact (burnsideC135_commute_iff_coords H.dsg H.comm hw.2 hwU ⟨q, hq⟩).mp hqw
      have h1 := hproj _ hline
      have hl := burnsideC135_card_line (Multiplicative.toAdd (β ⟨w, burnsideC135_Wc_le 1 hw.2⟩) 0)
      rw [H.card] at hl
      have h2 : Nat.card A ≤ a * (k * (f₀ * f₁) * 2) :=
        hAB.trans (Nat.mul_le_mul_left a (h1.trans (Nat.mul_le_mul (hAV.trans
          (Nat.mul_le_mul_left k hAW)) hl)))
      have h3 : a * (k * (f₀ * f₁) * 2) = k * (a * 2 * f₀ * f₁) := by ring
      have h4 : k * (a * 2 * f₀ * f₁) < k * (2 * 2 ^ 6) := Nat.mul_lt_mul_of_pos_left o1 hk0
      have h5 : 2 * (k * 2 ^ 6) = k * (2 * 2 ^ 6) := by ring
      omega
    ·
      push Not at h₃
      have hAWU : Nat.card ↥(A ⊓ burnsideC135_Wc β 1) ≤ f₀ :=
        (Subgroup.card_le_of_le (show A ⊓ burnsideC135_Wc β 1 ≤ A ⊓ centerOf (c134Q X L) from
          fun x hx => ⟨hx.1, h₃ x hx⟩)).trans hAU
      have h1 := hproj _ hfix₂
      have hfx : Nat.card ↥{y | ∀ a', H.q2.rep (hAX.trans H.normQ) (hAX.trans H.normW) a' y = y} =
          f₂ := rfl
      rw [hfx] at h1
      have h2 : Nat.card A ≤ a * (k * f₀ * f₂) :=
        hAB.trans (Nat.mul_le_mul_left a (h1.trans (Nat.mul_le_mul_right _ (hAV.trans
          (Nat.mul_le_mul_left k hAWU)))))
      have h3 : a * (k * f₀ * f₂) = k * (a * f₀ * f₂) := by ring
      have h4 : k * (a * f₀ * f₂) < k * (2 * 2 ^ 6) := Nat.mul_lt_mul_of_pos_left o2 hk0
      have h5 : 2 * (k * 2 ^ 6) = k * (2 * 2 ^ 6) := by ring
      omega
  push Not at h₂
  have hVS : pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) ≤
      burnsideC135_Wc β 1 ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) :=
    fun v hv => H.mem_sup_of_triv hv (h₂ v hv)
  by_cases hEU : pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) ≤ centerOf (c134Q X L)
  ·
    apply hTQ
    intro t ht
    obtain ⟨v, hv, q, hq, rfl⟩ := H.exists_V_mul ht
    have hvW : v ∈ burnsideC135_Wc β 1 :=
      (sup_le le_rfl (hEU.trans H.dsg.le₁)) (hVS hv)
    exact (c134Q X L).mul_mem (burnsideC135_Wc_le 1 hvW) hq
  have hk2 : 2 ≤ k := by
    have hne : ¬ (burnsideC135_Wc β 1 ⊔
        (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) ≤ burnsideC135_Wc β 1) := by
      intro h
      apply hEU
      intro e he
      exact H.inf_WE_le ⟨h (Subgroup.mem_sup_right he), he⟩
    have h1 : k ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.mp h)
    omega
  have hVcard : Nat.card ↥(pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)) =
      k * 2 ^ 6 := by
    rw [le_antisymm hVS H.sup_le_V, ← hkS, hW₁]
  have htrivT : ∀ t ∈ pCoreOf 2 X, ∀ q ∈ c134Q X L, t * q * t⁻¹ * q⁻¹ ∈ centerOf (c134Q X L) := by
    intro t ht q' hq'
    obtain ⟨v, hv, q, hq, rfl⟩ := H.exists_V_mul ht
    have h1 := h₂ v hv q' hq'
    have h2 := H.comm q hq q' hq'
    have hvU := (Subgroup.mem_normalizer_iff.mp (H.normU (pCoreOf_le 2 X hv.1)) _).mp h2
    have e : v * q * q' * (v * q)⁻¹ * q'⁻¹ =
        (v * (q * q' * q⁻¹ * q'⁻¹) * v⁻¹) * (v * q' * v⁻¹ * q'⁻¹) := by group
    rw [e]
    exact (centerOf (c134Q X L)).mul_mem hvU h1
  have hf12 : f₁ = f₂ := by
    rw [hf₁, hf₂]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => forall_congr' fun a' => by
      rw [H.rep_eq_of_triv hAX htrivT a' v])
  have hAE := H.inf_E_le_U hAX hA hAT
  have hAEf : Nat.card ↥(A ⊓ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G))) ≤ f₀ :=
    (Subgroup.card_le_of_le (show A ⊓ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) ≤
      A ⊓ centerOf (c134Q X L) from fun x hx => ⟨hx.1, hAE hx⟩)).trans hAU
  have hUE : centerOf (c134Q X L) ≤ pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) :=
    fun u hu => ⟨H.Q_le hu.1, hu.2⟩
  have hE16 : 2 * 2 ^ 3 ≤ Nat.card ↥(pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) := by
    have h := burnsideC135_two_mul_card_le hUE hEU
    rwa [burnsideC135_card_U H.dsg, H.card] at h
  have hEf : Nat.card ↥(pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) ≤ a * f₀ := by
    set C := A ⊓ Subgroup.centralizer
      ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) : Subgroup G) : Set G) with hC
    have hATC : A ⊓ pCoreOf 2 X ≤ C := fun t ht =>
      ⟨ht.1, Subgroup.mem_centralizer_iff.mpr fun e he => (H.T_comm_E ht.2 he).symm⟩
    have hEel : IsElemAbelian 2 (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) :=
      burnsideC135_isElemAbelian_mono hVel H.E_le_V
    have hCel : IsElemAbelian 2 C := burnsideC135_isElemAbelian_mono hA inf_le_left
    have hjoin := burnsideC135_isElemAbelian_sup hEel hCel fun e he c hc =>
      Subgroup.mem_centralizer_iff.mp hc.2 e he
    have hjR : (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) ⊔ C ≤ R :=
      sup_le (inf_le_left.trans hTR) (inf_le_left.trans hAR)
    have h1 := hAmax.2.2 _ hjR hjoin
    have h2 : Nat.card ↥((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) ⊔ C) ≤
        a * Nat.card C :=
      h1.trans (hAB.trans (Nat.mul_le_mul_left a (Subgroup.card_le_of_le hATC)))
    have h3 := card_le_mul_card_inf le_sup_right le_sup_left h2
    exact h3.trans (Nat.mul_le_mul_left a ((Subgroup.card_le_of_le
      (show C ⊓ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) ≤
        A ⊓ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) from
        fun x hx => ⟨hx.1.1, hx.2⟩)).trans hAEf))
  have hAVE : Nat.card ↥(A ⊓ (pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G))) ≤
      f₀ * f₁ := by
    have hsub : A ⊓ (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) ≤
        A ⊓ (pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)) :=
      inf_le_inf_left _ H.E_le_V
    have h1 := burnsideC135_card_le_of_hom hsub (fun x => H.projE (x : G))
      (fun x y => H.projE_mul (hVS x.2.2) (hVS y.2.2))
      (fun x => by
        show H.projE (x : G) = 0 ↔ _
        rw [H.projE_eq_zero_iff (hVS x.2.2)]
        exact ⟨fun h => ⟨x.2.1, h⟩, fun h => h.2⟩)
      {y | ∀ a', H.q1.rep (hAX.trans H.normW) (hAX.trans H.normU) a' y = y}
      (fun x a' => by
        show H.q1.rep _ _ a' (H.projE (x : G)) = H.projE (x : G)
        rw [← H.projE_conj hAX a' (hVS x.2.2)]
        congr 1
        rw [hcommA _ a'.2 _ x.2.1]
        group)
    have hfx : Nat.card ↥{y | ∀ a', H.q1.rep (hAX.trans H.normW) (hAX.trans H.normU) a' y = y} =
        f₁ := rfl
    rw [hfx] at h1
    exact h1.trans (Nat.mul_le_mul_right _ hAEf)
  have hAle : Nat.card A ≤ a * (f₀ * f₁ * f₁) := by
    have h1 := hproj _ hfix₂
    have hfx : Nat.card ↥{y | ∀ a', H.q2.rep (hAX.trans H.normQ) (hAX.trans H.normW) a' y = y} =
        f₂ := rfl
    rw [hfx, ← hf12] at h1
    exact hAB.trans (Nat.mul_le_mul_left a (h1.trans (Nat.mul_le_mul_right _ hAVE)))
  have hdvd : f₁ ∣ 2 ^ 3 := by
    have h := burnsideC135_card_fixAll_dvd (H.q1.rep (hAX.trans H.normW) (hAX.trans H.normU))
      (H.q1.rep_add (hAX.trans H.normW) (hAX.trans H.normU))
    have h8 : Nat.card (Fin 3 → F) = 2 ^ 3 := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, hFc]
    rwa [h8] at h
  have hf₁pos : 0 < f₁ := by
    have h0 : ∀ x, H.q1.rep (hAX.trans H.normW) (hAX.trans H.normU) x 0 = 0 := fun x => by
      have := H.q1.rep_add (hAX.trans H.normW) (hAX.trans H.normU) x 0 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    haveI : Nonempty (fixAll (H.q1.rep (hAX.trans H.normW) (hAX.trans H.normU))) := ⟨⟨0, h0⟩⟩
    exact Nat.card_pos
  have hVA' := hVA
  rw [hVcard] at hVA'
  have hf₁lt : f₁ < 4 := by
    by_contra h
    push Not at h
    have : 2 * 2 ^ 3 * 4 ≤ a * f₀ * f₁ := by
      calc 2 * 2 ^ 3 * 4 ≤ (a * f₀) * f₁ := Nat.mul_le_mul (hE16.trans hEf) h
        _ = a * f₀ * f₁ := rfl
    have e : a * 2 * f₀ * f₁ = 2 * (a * f₀ * f₁) := by ring
    omega
  interval_cases f₁
  ·
    have e : a * 2 * f₀ * 1 = 2 * (a * f₀) := by ring
    have e2 : a * (f₀ * 1 * 1) = a * f₀ := by ring
    rw [e2] at hAle
    omega
  ·
    have e : a * 2 * f₀ * 2 = 4 * (a * f₀) := by ring
    have e2 : a * (f₀ * 2 * 2) = 4 * (a * f₀) := by ring
    rw [e2] at hAle
    omega
  ·
    norm_num at hdvd

end burnsideC135_H1

end CFSG.ASVolI

end
