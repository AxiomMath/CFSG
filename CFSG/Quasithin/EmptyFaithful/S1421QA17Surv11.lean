module

public import CFSG.Quasithin.EmptyFaithful.S1421QA17Setup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421QA17

section Setting

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem mcOf_eq_sup_of_s5 (h : Hyp1421 G T M) (hK1 : K1 ≤ mcOf T)
    (hQ : IsQ8D8 ↥(pCoreOf 2 (mcOf T))) (hQK : pCoreOf 2 (mcOf T) ≤ K1)
    (hS5 : Nonempty (OTwoQuot (K1 ⊔ T) ≃* Equiv.Perm (Fin 5))) :
    K1 ⊔ T = mcOf T ∧ ∃ θ : ↥(mcOf T) →* Equiv.Perm (Fin 5),
      θ.ker = (pCoreOf 2 (mcOf T)).subgroupOf (mcOf T) ∧ θ.range = ⊤ ∧
        Nat.card (mcOf T) = 3840 := by
  obtain ⟨θ, hker⟩ := exists_theta_mcOf h hQ
  have hc := card_eq_mul_card_range (pCoreOf_le 2 _) hQ hker
  have hdvd := card_range_dvd θ
  have hXM : K1 ⊔ T ≤ mcOf T := sup_le hK1 (T_le_mcOf h)
  have hQX : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 (K1 ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hQK.trans le_sup_left)
      (hXM.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hX120 : Nat.card (OTwoQuot (K1 ⊔ T)) = 120 := by
    obtain ⟨e⟩ := hS5
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hXc := card_eq_card_oTwoQuot_mul (K1 ⊔ T)
  have h32 : 32 ≤ Nat.card (pCoreOf 2 (K1 ⊔ T)) := by
    rw [← hQ.1]
    exact Subgroup.card_le_of_le hQX
  have hXge : 3840 ≤ Nat.card ↥(K1 ⊔ T) := by
    rw [hXc, hX120]
    omega
  have hXle : Nat.card ↥(K1 ⊔ T) ≤ Nat.card (mcOf T) := Subgroup.card_le_of_le hXM
  have hr : Nat.card θ.range ≤ 120 := Nat.le_of_dvd (by norm_num) hdvd
  have hMc : Nat.card (mcOf T) = 3840 := by omega
  refine ⟨Subgroup.eq_of_le_of_card_ge hXM (by omega), θ, hker, ?_, hMc⟩
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [Nat.card_perm, Nat.card_fin]
  show Nat.card θ.range = 120
  omega

omit [Finite G] in
theorem card_eq_of_perfect_normal_s5 {Mc K1 Q : Subgroup G} (θ : ↥Mc →* Equiv.Perm (Fin 5))
    (hker : θ.ker = Q.subgroupOf Mc) (hrange : θ.range = ⊤) (hQ32 : Nat.card Q = 32)
    (hK1 : K1 ≤ Mc) (hQK : Q ≤ K1) (hn : Mc ≤ Subgroup.normalizer (K1 : Set G))
    (hp : ⁅K1, K1⁆ = K1) (hns : ¬ K1 ≤ Q) : Nat.card K1 = 1920 := by
  set K' := K1.subgroupOf Mc with hK'
  have hK'p : ⁅K', K'⁆ = K' := by
    have h1 : (⁅K', K'⁆).map Mc.subtype = K1 := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hK1, hp]
    have h2 : K'.map Mc.subtype = K1 := Subgroup.map_subgroupOf_eq_of_le hK1
    exact Subgroup.map_injective Mc.subtype_injective (h1.trans h2.symm)
  have hK'n : K'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hn
  have hsurj : Function.Surjective θ := MonoidHom.range_eq_top.mp hrange
  set Nθ := K'.map θ with hNθ
  have hNθn : Nθ.Normal := hK'n.map θ hsurj
  have hNθp : ⁅Nθ, Nθ⁆ = Nθ := by rw [hNθ, ← Subgroup.map_commutator, hK'p]
  have hNθA : Nθ ≤ alternatingGroup (Fin 5) := by
    rw [← hNθp]
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    rw [Equiv.Perm.mem_alternatingGroup, commutatorElement_def]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, mul_comm, mul_left_comm]
  have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hNθnA : (Nθ.subgroupOf (alternatingGroup (Fin 5))).Normal := hNθn.subgroupOf _
  have hNθeq : Nθ = alternatingGroup (Fin 5) := by
    rcases hNθnA.eq_bot_or_eq_top with h0 | h1
    · exfalso
      apply hns
      intro k hk
      have hkM : k ∈ Mc := hK1 hk
      have hmem : θ ⟨k, hkM⟩ ∈ Nθ := Subgroup.mem_map_of_mem θ (show (⟨k, hkM⟩ : ↥Mc) ∈ K' from hk)
      have hA : θ ⟨k, hkM⟩ ∈ alternatingGroup (Fin 5) := hNθA hmem
      have h2 : (⟨θ ⟨k, hkM⟩, hA⟩ : ↥(alternatingGroup (Fin 5))) ∈
          Nθ.subgroupOf (alternatingGroup (Fin 5)) := hmem
      rw [h0, Subgroup.mem_bot] at h2
      have h3 : θ ⟨k, hkM⟩ = 1 := congrArg Subtype.val h2
      have hker' : (⟨k, hkM⟩ : ↥Mc) ∈ θ.ker := h3
      rw [hker] at hker'
      exact hker'
    · refine le_antisymm hNθA fun x hx => ?_
      have : (⟨x, hx⟩ : ↥(alternatingGroup (Fin 5))) ∈
          Nθ.subgroupOf (alternatingGroup (Fin 5)) := by
        rw [h1]
        trivial
      exact this
  have hQ'K' : Q.subgroupOf Mc ≤ K' := fun x hx => hQK hx
  have hQM : Q ≤ Mc := hQK.trans hK1
  set θK : ↥K' →* Equiv.Perm (Fin 5) := θ.comp K'.subtype with hθK
  have hrangeK : θK.range = Nθ := by
    ext y
    simp only [hθK, MonoidHom.mem_range, MonoidHom.comp_apply, Subgroup.subtype_apply, hNθ,
      Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hkerK : θK.ker = (Q.subgroupOf Mc).subgroupOf K' := by
    ext x
    simp only [hθK, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.subtype_apply,
      Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have : (x : ↥Mc) ∈ θ.ker := hx
      rw [hker] at this
      exact this
    · intro hx
      have : (x : ↥Mc) ∈ θ.ker := by rw [hker]; exact hx
      exact this
  have h1 := Subgroup.card_ker_mul_card_range θK
  rw [hkerK, hrangeK, hNθeq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ'K').toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv, hQ32, nat_card_alternatingGroup,
    Nat.card_fin] at h1
  have h2 : Nat.card ↥K' = Nat.card K1 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK1).toEquiv
  rw [← h2, ← h1]
  rfl

end Setting

end S1421QA17

end CFSG.Quasithin
