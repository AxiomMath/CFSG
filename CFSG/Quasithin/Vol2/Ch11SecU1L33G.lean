module

public import CFSG.Quasithin.Vol2.Ch11SecU1L33F
public import CFSG.Quasithin.Vol2.Ch11SecU1Main

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L33

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.LieType.BorelTits
  CFSG.QuasithinUnique.Vol2Native.L239.L33Insp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

namespace Model

variable (M : Model L)

omit [Finite G] in
theorem mem_comm_sup {A : Subgroup G} {a : G} (haA : a ∈ A) (haTK : M.code a ∈ tk0l)
    (haQ : M.code a ∉ q0l) : M.R0 ≤ ⁅M.R0, A⁆ ⊔ M.Q0 := by
  obtain ⟨e, -, he1, hr, hri, hai, hrri, haai, hall⟩ := comm_check _ haTK haQ
  obtain ⟨r, hrR, hrc⟩ := M.exists_mem r0l_facts hr
  obtain ⟨ri, -, hric⟩ := M.exists_mem r0l_facts hri
  obtain ⟨ai, -, haic⟩ := M.exists_mem tk0l_facts hai
  have h1 : r * ri = 1 := M.code_inj (by rw [code_mul, hrc, hric, code_one]; exact hrri)
  have h2 : a * ai = 1 := M.code_inj (by rw [code_mul, haic, code_one]; exact haai)
  have hc : r * a * ri * ai ∈ ⁅M.R0, A⁆ := by
    rw [inv_eq_of_mul_eq_one_right h1 |>.symm, inv_eq_of_mul_eq_one_right h2 |>.symm,
      ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hrR haA
  have hcc : M.code (r * a * ri * ai) = commC e := by
    simp only [code_mul, hrc, hric, haic, commC, he1]
  intro w hw
  obtain ⟨q, hq, hwq | hwq | hwq⟩ := hall _ hw
  · obtain ⟨g, hg, hgc⟩ := M.exists_mem q0l_facts hq
    have : w = g := M.code_inj (by rw [hwq, hgc])
    exact Subgroup.mem_sup_right (this ▸ hg)
  · obtain ⟨g, hg, hgc⟩ := M.exists_mem q0l_facts hq
    have : w = r * a * ri * ai * g := M.code_inj (by rw [hwq, code_mul, hcc, hgc])
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hg)
  · obtain ⟨g, hg, hgc⟩ := M.exists_mem q0l_facts hq
    have : w = r * a * ri * ai * (r * a * ri * ai) * g :=
      M.code_inj (by rw [hwq, code_mul, code_mul, hcc, hgc])
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hc)
      (Subgroup.mem_sup_left hc)) (Subgroup.mem_sup_right hg)

theorem isE_K0 (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {A : Subgroup G} (hAT : A ≤ M.T0)
    (hA : IsElemAbelian 2 A) {x y : G} (hx : x ∈ A) (hy : y ∈ A)
    (hcov : ∀ c ∈ tl, cmul c (M.code x) = cmul (M.code x) c →
      cmul c (M.code y) = cmul (M.code y) c → c ∈ k0l)
    (hnq : ¬ (M.code x ∈ q0l ∧ M.code y ∈ q0l)) : IsE 1 ⊤ M.T0 A M.K0 := by
  have hT := M.isSylow_T0
  have hτ : tauOf ⊤ M.T0 A ≤ M.T0 ⊓ M.K0 := by
    intro t ht
    have htT : t ∈ M.T0 := tauOf_le _ _ _ ht
    have htx := Subgroup.mem_centralizer_singleton_iff.mp (tauOf_le_centralizer hO2 hx ht)
    have hty := Subgroup.mem_centralizer_singleton_iff.mp (tauOf_le_centralizer hO2 hy ht)
    refine ⟨htT, hcov _ htT ?_ ?_⟩
    · rw [← code_mul, ← code_mul, htx]
    · rw [← code_mul, ← code_mul, hty]
  have hAτ : A ≤ tauOf ⊤ M.T0 A := le_sup_left.trans (le_tauOf hT hAT hA)
  have hAK : A ≤ M.K0 := fun a ha => (hτ (hAτ ha)).2
  obtain ⟨a, haA, haQ⟩ : ∃ a ∈ A, M.code a ∉ q0l := by
    by_cases h : M.code x ∈ q0l
    · exact ⟨y, hy, fun h' => hnq ⟨h, h'⟩⟩
    · exact ⟨x, hx, h⟩
  have hTK : ∀ b ∈ A, M.code b ∈ tk0l := fun b hb => tk0l_check.1 _ (hAT hb) (hAK hb)
  have hpc := M.pcore_K0
  have hamb : EOneAmb M.K0 A := by
    refine ⟨3, Nat.prime_three, by norm_num, M.R0, fun r hr => sub_check.2.1 _ hr,
      M.K0_le_normalizer_R0, ?_, fun r hr => ⟨1, ?_⟩, fun k hk => ⟨1, ?_⟩, ?_, ?_, ?_⟩
    · rw [hpc]
      exact fun q hq => (sub_check.1 _ hq).2
    · rw [hpc, pow_one]
      show M.code (r ^ 3) ∈ q0l
      rw [pow_succ, pow_two, code_mul, code_mul]
      exact power_check.2.1 _ hr
    · rw [pow_one]
      show M.code (k ^ 2) ∈ r0l
      rw [pow_two, code_mul]
      exact power_check.2.2 _ hk
    · rw [hpc]
      intro h
      obtain ⟨c, hc, hcq⟩ := sub_check.2.2
      obtain ⟨g, hg, hgc⟩ := M.exists_mem r0l_facts hc
      have hg' : g ∈ M.Q0 := h ▸ hg
      exact hcq (by rw [← hgc]; exact hg')
    · rw [hpc]
      exact M.mem_comm_sup haA (hTK a haA) haQ
    · rw [hpc]
      refine Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr ⟨a, haA, haQ, fun b hb => ?_⟩
      rcases index_check _ (hTK b hb) _ (hTK a haA) haQ with h | h
      · exact Or.inr h
      · exact Or.inl (by
          show M.code (b * a) ∈ q0l
          rw [code_mul]
          exact h)
  have hE : EOne ↥M.K0 (A.subgroupOf M.K0) := (eOne_iff_amb hAK).mpr hamb
  have hcard : Nat.card (barO2 ↥M.K0 (A.subgroupOf M.K0)) ≤ 2 ^ 1 := by
    obtain ⟨-, -, -, -, -, -, h⟩ := hE
    rw [h]
    norm_num
  refine ⟨le_top, hτ, ?_, Or.inl ⟨hE, hcard⟩⟩
  rw [M.inf_T0_K0]
  exact M.isSylow_TK0

end Model

end CFSG.Quasithin.Vol2.Ch11.SecU1.L33
