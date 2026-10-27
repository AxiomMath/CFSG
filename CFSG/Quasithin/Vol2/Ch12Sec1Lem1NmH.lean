module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmD
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmG
public import CFSG.Quasithin.Vol2.KGNatG2Order

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix SL2Two

theorem lem1211NormalLin_holds : Lem1211NormalLin := by
  classical
  intro G _ _ B B₀ P k hB hk hlin hB₀ hBor hP hPN hPB₀ hPQ
  obtain ⟨F, _, _, hF, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hlin
  have : CharP F 2 := Vol2.KGNat.charP_two_of_card (n := k) (by omega)
    (by rw [Nat.card_eq_fintype_card, hF])
  obtain ⟨l, hl0, hl1⟩ : ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
    have h4 : (({0, 1} : Finset F)).card < (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, hF]
      calc (({0, 1} : Finset F)).card ≤ 2 := Finset.card_le_two
        _ < 2 ^ k := by
          calc 2 < 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card h4
    exact ⟨l, fun h => hl (by simp [h]), fun h => hl (by simp [h])⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard3 : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) ≠ 3 := by
    rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv,
      card_SL2_eq, hF]
    have hq : 4 ≤ 2 ^ k :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    generalize 2 ^ k = q at hq ⊢
    have h16 : 16 ≤ q ^ 2 := by nlinarith
    have : 4 * 15 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq (by omega)
    omega
  unfold IsBorelOfBlock at hBor
  split_ifs at hBor with h3
  · exact absurd h3 hcard3
  obtain ⟨S, hS, hSD⟩ := hBor
  have hQS : blockQ B ≤ S := hS.le_of_normalizes (C1.blockQ_le B) (C1.le_normalizer_blockQ B)
    (C1.blockQ_isPGroup B)
  set Sb := (S.subgroupOf B).map α with hSb
  have hSb2 : IsPGroup 2 Sb :=
    (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).map α
  have hSbi : ¬ 2 ∣ Sb.index := fun h => hS.2.2 (h.trans (Subgroup.index_map_dvd _ hαs))
  obtain ⟨g₀, hg₀⟩ := exists_conj_unitri2 (k := k) (by omega) hF hSb2 hSbi
  set α' : ↥B →* SpecialLinearGroup (Fin 2) F := (MulAut.conj g₀⁻¹).toMonoidHom.comp α with hα'
  have hα'a : ∀ x, α' x = g₀⁻¹ * α x * g₀ := fun x => by
    simp [hα']
  have hα's : Function.Surjective α' := fun g => by
    obtain ⟨x, hx⟩ := hαs (g₀ * g * g₀⁻¹)
    exact ⟨x, by rw [hα'a, hx]; group⟩
  have hα'1 : ∀ x, α' x = 1 → (x : G) ∈ blockQ B := fun x hx => by
    have h1 : α x = 1 := by
      rw [hα'a] at hx
      calc α x = g₀ * (g₀⁻¹ * α x * g₀) * g₀⁻¹ := by group
        _ = 1 := by rw [hx]; group
    have h2 : x ∈ α.ker := h1
    rw [hαk] at h2
    exact (C56.mem_blockQ_iff x).mpr h2
  have hD : ∀ x : ↥B, (α' x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
      (x : G) ∈ B ⊓ Subgroup.normalizer (S : Set G) := by
    intro x hx
    refine ⟨x.2, Sec121Swap.mem_normalizer_of_conj_mem fun s hs => ?_⟩
    have hsB : s ∈ B := hS.1 hs
    have h1 : α ⟨s, hsB⟩ ∈ Sb := ⟨⟨s, hsB⟩, hs, rfl⟩
    have h2 : α' ⟨s, hsB⟩ ∈ unitri2 := by rw [hα'a]; exact (hg₀ _).mp h1
    have h3 : α' (x * ⟨s, hsB⟩ * x⁻¹) ∈ unitri2 := by
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_unitri2 hx h2
    have h4 : α (x * ⟨s, hsB⟩ * x⁻¹) ∈ Sb := by
      rw [hg₀]
      rw [hα'a] at h3
      exact h3
    obtain ⟨y, hy, hyx⟩ := h4
    have hk : y⁻¹ * (x * ⟨s, hsB⟩ * x⁻¹) ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    rw [hαk] at hk
    have hkQ := hQS ((C56.mem_blockQ_iff _).mpr hk)
    have e : (x : G) * s * (x : G)⁻¹ =
        (y : G) * ((y⁻¹ * (x * ⟨s, hsB⟩ * x⁻¹) : ↥B) : G) := by
      simp
    rw [e]
    exact S.mul_mem hy hkQ
  intro p hp
  have hpB : p ∈ Subgroup.normalizer (B : Set G) := hPN hp
  have hpc : B₀ ⊔ pCoreOf 2 B ≤ Subgroup.centralizer ({p} : Set G) := by
    refine sup_le (fun b hb => ?_) (fun q hq => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hPB₀ hp)) b hb
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hPQ hp)) q hq
  have hpD : ∀ x : ↥B, (α' x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
      p * (x : G) * p⁻¹ = x := by
    intro x hx
    have h1 := hpc (hSD ▸ hD x hx)
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    rw [← h1, mul_inv_cancel_right]
  have hpBx : ∀ b : ↥B, p * (b : G) * p⁻¹ ∈ B := fun b =>
    (Subgroup.mem_normalizer_iff.mp hpB b).mp b.2
  let cp : ↥B →* ↥B :=
    { toFun := fun b => ⟨p * b * p⁻¹, hpBx b⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcp : ∀ b : ↥B, ((cp b : ↥B) : G) = p * b * p⁻¹ := fun _ => rfl
  have hψ : ∀ b : ↥B, α' (cp b) = α' b := hom_eq_of_eq_on_borel hl0 hl1 α' (α'.comp cp) hα's
    (fun x hx => by
      have hxQ := hα'1 x hx
      have h1 : cp x = x := Subtype.ext (by
        rw [hcp]
        have := (Subgroup.mem_centralizer_singleton_iff.mp
          (hpc (le_sup_right (a := B₀) hxQ)))
        rw [← this, mul_inv_cancel_right])
      show α' (cp x) = 1
      rw [h1, hx])
    (fun x hx => by
      show α' (cp x) = α' x
      have h1 : cp x = x := Subtype.ext (by rw [hcp]; exact hpD x hx)
      rw [h1])
  have hQ : ∀ b ∈ B, p * b * p⁻¹ * b⁻¹ ∈ blockQ B := by
    intro b hb
    have h1 := hψ ⟨b, hb⟩
    have h2 : α' (cp ⟨b, hb⟩ * (⟨b, hb⟩ : ↥B)⁻¹) = 1 := by
      rw [map_mul, h1, map_inv, mul_inv_cancel]
    exact hα'1 _ h2
  have hU : ∀ b ∈ B, p * b * p⁻¹ * b⁻¹ ∈ blockU B :=
    C1.commutator_mem_of_noTwoQuotient hB.1 (C1.blockQ_isPGroup B)
      (fun m hm n hn => (Subgroup.mem_normalizer_iff.mp
        (C1.le_normalizer_blockU B (C1.blockQ_le B hm)) n).mp hn)
      (fun l hl w hw => C1.commutator_mem_blockU' hl hw) hQ
  have hconjU : ∀ (b : ↥B) (w : ↥(blockU B)), (b : G) * w * (b : G)⁻¹ ∈ blockU B := fun b w =>
    (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU B b.2) w).mp w.2
  let u : ↥B → ↥(blockU B) := fun b => ⟨p * b * p⁻¹ * (b : G)⁻¹, hU b b.2⟩
  let c : ↥B → Fin 2 → F := fun b =>
    ((g₀⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
      Multiplicative.toAdd (β (u b))
  have hc : ∀ x y : ↥B, c (x * y) = c x + (α' x : Matrix (Fin 2) (Fin 2) F) *ᵥ c y := by
    intro x y
    have h1 : u (x * y) = u x * ⟨x * (u y : G) * (x : G)⁻¹, hconjU x (u y)⟩ :=
      Subtype.ext (by simp only [u, Subgroup.coe_mul, _root_.mul_inv_rev]; group)
    have h2 := hβe x (u y) ⟨x * (u y : G) * (x : G)⁻¹, hconjU x (u y)⟩ rfl
    have e : ((g₀⁻¹ * α x * g₀ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((g₀⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((g₀⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((α x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      have h3 : g₀⁻¹ * α x * g₀ * g₀⁻¹ = g₀⁻¹ * α x := by group
      exact congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h3
    simp only [c]
    rw [h1, map_mul, toAdd_mul, mulVec_add, h2, hα'a, mulVec_mulVec, mulVec_mulVec, e]
  have hB0 : ∀ x : ↥B, (α' x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 → c x = 0 := by
    intro x hx
    have h1 : u x = 1 := Subtype.ext (by
      show p * (x : G) * p⁻¹ * (x : G)⁻¹ = 1
      rw [hpD x hx, mul_inv_cancel])
    simp only [c]
    rw [h1, map_one, toAdd_one, mulVec_zero]
  have hc0 := cocycle_eq_zero hl0 hl1 α' hα's c hc hB0
  have hZ : ∀ b ∈ B, p * b * p⁻¹ * b⁻¹ ∈ blockZ B := by
    intro b hb
    have h1 := hc0 ⟨b, hb⟩
    have h2 : Multiplicative.toAdd (β (u ⟨b, hb⟩)) = 0 := by
      have := congrArg (fun v => ((g₀ : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) *ᵥ v) h1
      simp only [c, mulVec_mulVec, mulVec_zero] at this
      have h4 : ((g₀ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((g₀⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 :=
        congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
          (mul_inv_cancel g₀)
      rwa [h4, one_mulVec] at this
    have h3 : u ⟨b, hb⟩ ∈ β.ker := by
      rw [MonoidHom.mem_ker]
      exact h2
    rw [hβk] at h3
    exact h3
  have hone : ∀ b ∈ B, p * b * p⁻¹ * b⁻¹ ∈ (⊥ : Subgroup G) :=
    C1.commutator_mem_of_noTwoQuotient hB.1
      ((C1.isPGroup_blockU hB).to_le inf_le_left)
      (fun m _ n hn => by rw [Subgroup.mem_bot] at hn ⊢; rw [hn, mul_one, mul_inv_cancel])
      (fun l hl w hw => by
        rw [Subgroup.mem_bot]
        have h1 := (Subgroup.mem_centralizer_iff.mp hw.2) l hl
        rw [h1, mul_inv_cancel_right, mul_inv_cancel]) hZ
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have h1 := hone b hb
  rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

end CFSG.Quasithin.H13
