module

public import CFSG.Quasithin.EmptyFaithful.E111L2IG

public section

namespace CFSG.Quasithin.E2.E22N.E111L.KMI

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_sup' [Finite G] {g : G} {H K : Subgroup G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjSub_eq
  unfold A1b.conjSub
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (conjSub_eq_of_mem_normalizer hH) (conjSub_eq_of_mem_normalizer hK)

section Diag

variable {X T A S C : Subgroup G} (h : DiagSetting X T A S C) [Fintype ↥C] [Finite G]
  {L₀ P V' : Subgroup G}
  (hd : S4Data (diagSub S C h.diagComm) T (T ⊓ Subgroup.centralizer (A : Set G)) L₀ P V')
include h hd

omit [Finite G] in
theorem le_commutator_A (hPW : P ≤ V' ⊔ ⁅P, diagInner A S C h.diagComm⁆) :
    P ≤ V' ⊔ ⁅P, A⁆ := by
  refine hPW.trans (sup_le_sup_left (Subgroup.commutator_le.mpr fun x hx w hw => ?_) _)
  obtain ⟨v, hvA, hv⟩ := exists_of_mem_diagInner h hw
  have hxD : x⁻¹ ∈ diagSub S C h.diagComm := Subgroup.inv_mem _ (S4Data.P_le_D h hd hx)
  have hc : ⁅x, w⁆ = ⁅x, v⁆ := by
    calc ⁅x, w⁆ = x * (w * x⁻¹ * w⁻¹) := by rw [commutatorElement_def]; group
      _ = x * (v * x⁻¹ * v⁻¹) := by rw [hv _ hxD]
      _ = ⁅x, v⁆ := by rw [commutatorElement_def]; group
  rw [hc]
  exact Subgroup.commutator_mem_commutator hx hvA

theorem eOneAmb_K (hCV : C ⊔ (A ⊓ Subgroup.normalizer (S : Set G)) = A)
    (hinn : ∀ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S,
      s⁻¹ * a ∈ Subgroup.centralizer (S : Set G))
    (hcent : Subgroup.centralizer (V' : Set G) ⊓ diagSub S C h.diagComm = V')
    (hV' : IsKleinFour ↥V') (hV₀ : IsKleinFour ↥(diagInner A S C h.diagComm))
    (hV₀L : diagInner A S C h.diagComm ≤ L₀)
    (hV₀V : Nat.card ↥(diagInner A S C h.diagComm ⊓ V') = 2)
    (hPW : P ≤ V' ⊔ ⁅P, diagInner A S C h.diagComm⁆) {y : G} (hyP : y ∈ P)
    (hy : ∀ w ∈ L₀, w ∉ V' → w * w = 1 → ∀ n : ℕ, ⁅y, w⁆ ^ 2 ^ n ≠ 1) :
    E1.EOneAmb (sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
      (T ⊓ Subgroup.centralizer (A : Set G))) A := by
  set R := T ⊓ Subgroup.centralizer (A : Set G) with hR
  set K := sSup (conjFam R L₀) ⊔ R with hK
  set O := pCoreOf 2 K with hO
  set P₄ := sSup (conjFam R P) with hP₄
  have hidx : O.relIndex A = 2 := relIndex_pCoreOf h hd hCV hinn hcent hV' hV₀ hV₀L hV₀V hyP hy
  have hP₄K : P₄ ≤ K := (sSup_le fun Z hZ => by
    obtain ⟨k, rfl⟩ := hZ
    exact (A1b.conjSub_mono _ hd.P_le).trans (le_sSup (conj_mem_conjFam k.2))).trans le_sup_left
  have hKN₄ : K ≤ Subgroup.normalizer (P₄ : Set G) :=
    sup_le (sSup_le_normalizer h hd.L_le (S4Data.P_le_D h hd) (fun k hk hD => (hd.inv k hk hD).1)
      hd.P_norm) (le_normalizer_conjFam R P)
  have hKNO : K ≤ Subgroup.normalizer (O : Set G) := fun k hk =>
    mem_normalizer_of_conjSub_le
      (by rintro _ ⟨n, hn, rfl⟩; exact conj_mem_pCoreOf K k hk n hn)
      (by rintro _ ⟨n, hn, rfl⟩; exact conj_mem_pCoreOf K k⁻¹ (K.inv_mem hk) n hn)
  have hOK : O ≤ K := Subgroup.map_subtype_le _
  have hMO : sSup (conjFam R V') ≤ O := M_le_pCoreOf h hd
  obtain ⟨a₀, ha₀, ha₀O⟩ : ∃ a₀ ∈ A, a₀ ∉ O := by
    by_contra hc
    push Not at hc
    have : O.relIndex A = 1 := Subgroup.relIndex_eq_one.mpr fun a ha => hc a ha
    omega
  refine ⟨3, Nat.prime_three, by norm_num, O ⊔ P₄, sup_le hOK hP₄K,
    fun k hk => mem_normalizer_sup' (hKNO hk) (hKN₄ hk), le_sup_left, ?_, ?_, ?_, ?_, hidx⟩
  ·
    intro x hx
    obtain ⟨o, ho, q, hq, rfl⟩ := exists_mul_of_mem_sup (hP₄K.trans hKNO) hx
    refine ⟨1, ?_⟩
    have hqK := hP₄K hq
    have e : (o * q) ^ 3 ^ 1 = o * (q * o * q⁻¹) * ((q * q) * o * (q * q)⁻¹) * q ^ 3 := by
      rw [pow_one, pow_three, pow_three]
      group
    rw [e]
    refine O.mul_mem (O.mul_mem (O.mul_mem ho (conj_mem_pCoreOf K q hqK o ho))
      (conj_mem_pCoreOf K _ (K.mul_mem hqK hqK) o ho)) (hMO (pow_three_mem h hd q hq))
  ·
    intro s hs
    obtain ⟨m, hm⟩ := pow_two_mem_P₄ h hd hs
    exact ⟨m, Subgroup.mem_sup_right hm⟩
  ·
    intro heq
    have hyO : y ∈ O := by
      have h1 : y ∈ O ⊔ P₄ := by
        refine Subgroup.mem_sup_right (le_sSup (conj_mem_conjFam (Subgroup.one_mem R)) ?_)
        rw [A1b.conjSub_one]
        exact hyP
      rwa [heq] at h1
    obtain ⟨w, hw, hwa⟩ := exists_conj_diagInner h hCV hinn ha₀
    have hwV : w ∉ V' := fun h1 => ha₀O (le_pCoreOf_of_centralizer h hd hcent hV' ha₀
      ((mem_centralizer_iff_of_conj h (S4Data.V_le_D h hd) hcent (diagInner_le_diag h hw)
        hwa).mpr h1))
    have hyD : y⁻¹ ∈ diagSub S C h.diagComm := Subgroup.inv_mem _ (S4Data.P_le_D h hd hyP)
    have hc : ⁅y, a₀⁆ = ⁅y, w⁆ := by
      calc ⁅y, a₀⁆ = y * (a₀ * y⁻¹ * a₀⁻¹) := by rw [commutatorElement_def]; group
        _ = y * (w * y⁻¹ * w⁻¹) := by rw [hwa _ hyD]
        _ = ⁅y, w⁆ := by rw [commutatorElement_def]; group
    have hcO : ⁅y, a₀⁆ ∈ O := by
      have e : ⁅y, a₀⁆ = y * (a₀ * y⁻¹ * a₀⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact O.mul_mem hyO (conj_mem_pCoreOf K a₀ (A_le_K h ha₀) _ (O.inv_mem hyO))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hcO⟩
    apply hy w (hV₀L hw) hwV (congrArg Subtype.val (hV₀.mul_self ⟨w, hw⟩)) n
    rw [← hc]
    simpa using congrArg Subtype.val hn
  ·
    refine sup_le le_sup_right (sSup_le fun Z hZ => ?_)
    obtain ⟨k, rfl⟩ := hZ
    have hkA : A1b.conjSub (k : G) A = A :=
      conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ k.2.2)
    have h1 := A1b.conjSub_mono (k : G) (le_commutator_A h hd hPW)
    unfold A1b.conjSub at h1 hkA
    rw [Subgroup.map_sup, Subgroup.map_commutator, hkA] at h1
    refine h1.trans (sup_le ?_ ?_)
    · exact (le_sSup (conj_mem_conjFam k.2)).trans (hMO.trans le_sup_right)
    · refine (Subgroup.commutator_mono ?_ le_rfl).trans le_sup_left
      exact (le_sSup (conj_mem_conjFam k.2)).trans le_sup_right

end Diag

end CFSG.Quasithin.E2.E22N.E111L.KMI
