module

public import CFSG.Quasithin.EmptyFaithful.S152L27A
public import CFSG.Quasithin.Background.D1Statement

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

theorem exists_chiefStep_of_not_le_pCoreOf [Finite G]
    {X Q ZS Z V : Subgroup G} (hQ : IsPGroup 2 Q) (hZ : IsPGroup 2 Z)
    (hZSQ : ZS ≤ Q)
    (hZS_inv : ∀ g ∈ X, ∀ s ∈ ZS, g * s * g⁻¹ ∈ ZS)
    (hZS_mod : ∀ g ∈ X, ∀ s ∈ ZS, g * s * g⁻¹ * s⁻¹ ∈ Z)
    (hZc : ∀ g ∈ X, ∀ z ∈ Z, g * z * g⁻¹ = z)
    (hQX : ∀ g ∈ X, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hchar : ∀ x ∈ X, (∀ q ∈ Q, q * x = x * q) → x ∈ Q)
    (hVX : V ≤ X) (hVO : ¬ V ≤ pCoreOf 2 X) :
    ∃ L N : Subgroup G, IsChiefStep X Q L N ∧ ZS ≤ L ∧ ¬ ⁅N, V⁆ ≤ L := by
  by_contra hcon
  push Not at hcon
  let Sg : Subgroup G :=
    { carrier := {x | x ∈ X ∧ ∀ L N : Subgroup G, IsChiefStep X Q L N → ZS ≤ L →
        ∀ n ∈ N, x * n * x⁻¹ * n⁻¹ ∈ L}
      one_mem' := ⟨X.one_mem, fun L N _ _ n _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hxs⟩ ⟨hy, hys⟩
        refine ⟨X.mul_mem hx hy, fun L N hLN hZL n hn => ?_⟩
        have hc := hys L N hLN hZL n hn
        have e : x * y * n * (x * y)⁻¹ * n⁻¹ =
            (x * (y * n * y⁻¹ * n⁻¹) * x⁻¹) * (x * n * x⁻¹ * n⁻¹) := by group
        rw [e]
        exact L.mul_mem (hLN.2.1.2 x hx _ hc) (hxs L N hLN hZL n hn)
      inv_mem' := by
        rintro x ⟨hx, hxs⟩
        refine ⟨X.inv_mem hx, fun L N hLN hZL n hn => ?_⟩
        have hn' : x⁻¹ * n * x ∈ N := by
          have := hLN.1.2 x⁻¹ (X.inv_mem hx) n hn
          simpa using this
        have hc := hxs L N hLN hZL _ hn'
        have e : x⁻¹ * n * x⁻¹⁻¹ * n⁻¹ =
            (x * (x⁻¹ * n * x) * x⁻¹ * (x⁻¹ * n * x)⁻¹)⁻¹ := by group
        rw [e]
        exact L.inv_mem hc }
  have hSgX : Sg ≤ X := fun y hy => hy.1
  have hSgn : X ≤ Subgroup.normalizer (Sg : Set G) := by
    have key : ∀ g ∈ X, ∀ y ∈ Sg, g * y * g⁻¹ ∈ Sg := by
      intro g hg y
      rintro ⟨hy, hys⟩
      refine ⟨X.mul_mem (X.mul_mem hg hy) (X.inv_mem hg), fun L N hLN hZL n hn => ?_⟩
      have hn' : g⁻¹ * n * g ∈ N := by
        have := hLN.1.2 g⁻¹ (X.inv_mem hg) n hn
        simpa using this
      have hc := hys L N hLN hZL _ hn'
      have e : g * y * g⁻¹ * n * (g * y * g⁻¹)⁻¹ * n⁻¹ =
          g * (y * (g⁻¹ * n * g) * y⁻¹ * (g⁻¹ * n * g)⁻¹) * g⁻¹ := by group
      rw [e]
      exact hLN.2.1.2 g hg _ hc
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key g hg y, fun hy => ?_⟩
    have := key g⁻¹ (X.inv_mem hg) _ hy
    simpa [mul_assoc] using this
  have hodd : ∀ y ∈ Sg, Odd (orderOf y) → y = 1 := by
    intro y hy ho
    obtain ⟨hyX, hys⟩ := hy
    have hP : ∀ n : ℕ, ∀ A : Subgroup G, Nat.card A = n → (∀ g ∈ X, ∀ a ∈ A, g * a * g⁻¹ ∈ A) →
        ZS ≤ A → A ≤ Q → ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ ZS := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro A hAn hAinv hZA hAQ a ha
        by_cases hAZ : A = ZS
        · have ha' : a ∈ ZS := hAZ ▸ ha
          exact ZS.mul_mem (hZS_inv y hyX a ha') (ZS.inv_mem ha')
        ·
          have hlt : ZS < A := lt_of_le_of_ne hZA (Ne.symm hAZ)
          classical
          let 𝒮 : Set (Subgroup G) := {L | (∀ g ∈ X, ∀ a ∈ L, g * a * g⁻¹ ∈ L) ∧ ZS ≤ L ∧ L < A}
          have hne : 𝒮.Nonempty := ⟨ZS, hZS_inv, le_rfl, hlt⟩
          obtain ⟨L, hL𝒮, hLmax⟩ := Set.Finite.exists_maximalFor (fun L : Subgroup G => L)
            𝒮 (Set.toFinite _) hne
          obtain ⟨hLinv, hZL, hLA⟩ := hL𝒮
          have hLQ : L ≤ Q := hLA.le.trans hAQ
          have hstep : IsChiefStep X Q L A := by
            refine ⟨⟨hAQ, hAinv⟩, ⟨hLQ, hLinv⟩, hLA, ?_⟩
            intro K hK hLK hKA
            by_contra hKne
            push Not at hKne
            have hKlt : K < A := lt_of_le_of_ne hKA hKne.2
            have := hLmax ⟨hK.2, hZL.trans hLK, hKlt⟩ hLK
            exact hKne.1 (le_antisymm this hLK)
          have hcardL : Nat.card L < n := by
            rw [← hAn]
            exact Subgroup.card_lt_of_lt hLA
          have hIH := ih _ hcardL L rfl hLinv hZL hLQ
          exact odd_conj_mem_of_mem_pGroup ho hZL (hQ.to_le hLQ) (fun l hl => hIH l hl)
            (hys L A hstep hZL a ha)
    have hQcomm := hP _ Q rfl hQX hZSQ le_rfl
    have hZScomm : ∀ s ∈ ZS, y * s * y⁻¹ * s⁻¹ ∈ (⊥ : Subgroup G) := fun s hs =>
      odd_conj_mem_of_mem_pGroup ho (Z₀ := ⊥) (L := Z) bot_le hZ
        (fun l hl => by rw [hZc y hyX l hl]; simp) (hZS_mod y hyX s hs)
    have hQcomm' : ∀ q ∈ Q, y * q * y⁻¹ * q⁻¹ ∈ (⊥ : Subgroup G) := fun q hq =>
      odd_conj_mem_of_mem_pGroup ho (Z₀ := ⊥) (L := ZS) bot_le (hQ.to_le hZSQ) hZScomm
        (hQcomm q hq)
    have hyc : ∀ q ∈ Q, q * y = y * q := by
      intro q hq
      have := Subgroup.mem_bot.mp (hQcomm' q hq)
      calc q * y = (y * q * y⁻¹ * q⁻¹) * (q * y) := by rw [this]; simp
        _ = y * q := by group
    exact eq_one_of_odd_of_mem_pGroup hQ (hchar y hyX hyc) ho
  have hSg2 : IsPGroup 2 Sg := isPGroup_two_of_forall_odd_eq_one hodd
  have hSgO : Sg ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSgX hSgn hSg2
  refine hVO (fun v hv => hSgO ⟨hVX hv, fun L N hLN hZL n hn => ?_⟩)
  have hmem : v * n * v⁻¹ * n⁻¹ ∈ ⁅V, N⁆ :=
    Subgroup.commutator_mem_commutator hv hn
  rw [Subgroup.commutator_comm] at hmem
  exact hcon L N hLN hZL hmem

end CFSG.Quasithin
