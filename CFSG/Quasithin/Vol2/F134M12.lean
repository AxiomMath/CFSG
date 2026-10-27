module

public import CFSG.Quasithin.Vol2.F134Overgroup
public import CFSG.Quasithin.Recognition.M12AmalInst
public import CFSG.Quasithin.Recognition.ModelBridges
public import Certificates.Certificate17019


public section

namespace CFSG.Quasithin.F134

open CFSG.Quasithin CFSG.Quasithin.M12Amal CFSG.Quasithin.P134 Equiv

theorem m12ATab_one : List.range 12 ∈ m12ATab :=
  Certificates.certificate17019.1

theorem m12BTab_one : List.range 12 ∈ m12BTab :=
  Certificates.certificate17019.2.1

theorem m12ATab_closed :
    ∀ l ∈ m12ATab, ∀ k ∈ [0, 1, 2, 3], compL l (genTab.getD k []) ∈ m12ATab :=
  Certificates.certificate17019.2.2.1

theorem m12BTab_closed :
    ∀ l ∈ m12BTab, ∀ k ∈ [0, 1, 2, 4], compL l (genTab.getD k []) ∈ m12BTab :=
  Certificates.certificate17019.2.2.2.1

theorem m12ATab_length : m12ATab.length = 192 :=
  Certificates.certificate17019.2.2.2.2.1

theorem m12BTab_length : m12BTab.length = 192 :=
  Certificates.certificate17019.2.2.2.2.2

@[expose] def valList (σ : Perm (Fin 12)) : List ℕ := List.ofFn fun i => (σ i : ℕ)

theorem repL_valList (σ : Perm (Fin 12)) : RepL (valList σ) σ := by
  refine ⟨List.length_ofFn, fun i => ?_⟩
  have hi : (i : ℕ) < (List.ofFn fun j : Fin 12 => (σ j : ℕ)).length := by
    rw [List.length_ofFn]
    exact i.2
  change (List.ofFn fun j : Fin 12 => (σ j : ℕ)).getD i 0 = (σ i : ℕ)
  rw [List.getD_eq_getElem _ _ hi, List.getElem_ofFn]

theorem card_closure_le_of_tab (ks : List ℕ) (hks : ∀ k ∈ ks, k < 5) (tab : List (List ℕ))
    (h1 : List.range 12 ∈ tab) (hcl : ∀ l ∈ tab, ∀ k ∈ ks, compL l (genTab.getD k []) ∈ tab) :
    Nat.card (Subgroup.closure {g : M12G | ∃ k ∈ ks, genG k = g}) ≤ tab.length := by
  set P : Set M12G := {g | ∃ l ∈ tab, ReprG l g}
  have hsub : ↑(Subgroup.closure {g : M12G | ∃ k ∈ ks, genG k = g}) ⊆ P := by
    refine closure_subset_of_right_closed ?_ ⟨_, h1, repL_one 12⟩ ?_
    · rintro s -
      exact ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩
    · rintro g ⟨l, hl, hgl⟩ s ⟨k, hk, rfl⟩
      refine ⟨_, hcl l hl k hk, reprG_mul hgl ?_⟩
      show RepL (genTab.getD k []) ((genG k : M12G) : Perm (Fin 12))
      rw [genG_coe k (hks k hk)]
      exact genTab_rep k (hks k hk)
  let f : ↥(Subgroup.closure {g : M12G | ∃ k ∈ ks, genG k = g}) → ↥tab.toFinset := fun g =>
    ⟨valList ((g : M12G) : Perm (Fin 12)), by
      obtain ⟨l, hl, hgl⟩ := hsub g.2
      rw [List.mem_toFinset, repL_unique (repL_valList _) hgl]
      exact hl⟩
  have hf : Function.Injective f := by
    intro g g' h
    have h' : valList ((g : M12G) : Perm (Fin 12)) = valList ((g' : M12G) : Perm (Fin 12)) :=
      congrArg Subtype.val h
    have := eq_of_repL (repL_valList _) (h' ▸ repL_valList ((g' : M12G) : Perm (Fin 12)))
    exact Subtype.ext (Subtype.ext this)
  calc Nat.card (Subgroup.closure {g : M12G | ∃ k ∈ ks, genG k = g})
      ≤ Nat.card ↥tab.toFinset := Nat.card_le_card_of_injective f hf
    _ = tab.toFinset.card := Nat.card_eq_card_toFinset _ |>.trans (by simp)
    _ ≤ tab.length := List.toFinset_card_le tab

theorem m12Data_A_eq :
    m12Data.A = Subgroup.closure {g : M12G | ∃ k ∈ [0, 1, 2, 3], genG k = g} := by
  show Subgroup.closure ({genG 0, genG 1, genG 2, genG 3} : Set M12G) = _
  congr 1
  ext g
  simp [eq_comm]

theorem m12Data_B_eq :
    m12Data.B = Subgroup.closure {g : M12G | ∃ k ∈ [0, 1, 2, 4], genG k = g} := by
  show Subgroup.closure ({genG 0, genG 1, genG 2, genG 4} : Set M12G) = _
  congr 1
  ext g
  simp [eq_comm]

theorem card_m12_A_le : Nat.card m12Data.A ≤ 192 := by
  rw [m12Data_A_eq, ← m12ATab_length]
  exact card_closure_le_of_tab _ (by decide) _ m12ATab_one m12ATab_closed

theorem card_m12_B_le : Nat.card m12Data.B ≤ 192 := by
  rw [m12Data_B_eq, ← m12BTab_length]
  exact card_closure_le_of_tab _ (by decide) _ m12BTab_one m12BTab_closed

theorem eleven_dvd_card_m12 : 11 ∣ Nat.card M12G := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let g : M12G := ⟨mA * mB, Subgroup.mul_mem _ mA_mem mB_mem⟩
  have h11 : g ^ 11 = 1 := Subtype.ext (by
    simp only [g, Subgroup.coe_pow, Subgroup.coe_one]
    decide +kernel)
  have h1 : g ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    simp only [g, Subgroup.coe_one] at this
    revert this
    decide +kernel
  rw [← orderOf_eq_prime h11 h1]
  exact orderOf_dvd_natCard g

theorem three_dvd_card_m12 : 3 ∣ Nat.card M12G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let g : M12G := ⟨mB, mB_mem⟩
  have h3 : g ^ 3 = 1 := Subtype.ext (by
    simp only [g, Subgroup.coe_pow, Subgroup.coe_one]
    decide +kernel)
  have h1 : g ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    simp only [g, Subgroup.coe_one] at this
    revert this
    decide +kernel
  rw [← orderOf_eq_prime h3 h1]
  exact orderOf_dvd_natCard g

@[expose] noncomputable def carrierM12Equiv :
    CFSG.Blueprint.NativeSporadic.Carrier .M12 ≃* M12G :=
  MulEquiv.subgroupCongr CFSG.Quasithin.quasithinM12_eq_native.symm

theorem noE9Config_m12 {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X → Nonempty (X ≃* M12G)) : NoE9Config F := by
  refine noE9Config_of_overgroupData m12Data isPGroup_T m12_syl.2 ?_ ?_ ?_ hF
  · rw [m12_card_T]
    have := card_m12_A_le
    omega
  · rw [m12_card_T]
    have := card_m12_B_le
    omega
  · rw [m12_card_T]
    intro h
    have := eleven_dvd_card_m12
    rw [h] at this
    norm_num at this

end CFSG.Quasithin.F134
