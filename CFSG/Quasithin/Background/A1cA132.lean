module

public import CFSG.Quasithin.Background.A1cA132Aux
public import CFSG.Quasithin.Background.A1cA132Struct
public import CFSG.Quasithin.Background.A1cA133Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank.Ccomm

namespace A1c

section A132

variable {r p : ℕ} [hr : Fact r.Prime] [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G]

theorem commutator_eq_bot_or_isPOnePlusTwo (hr2 : r ≠ 2) (hp2 : p ≠ 2)
    {R : Subgroup G} [R.Normal] (hRr : IsPGroup r ↥R)
    (hRΩ : Subgroup.closure {x : G | x ∈ R ∧ x ^ r = 1} = R) (hRcl : ClassLeTwo R)
    (hRrk : pRank r R ≤ 2) {P : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPΩ : Subgroup.closure {x : G | x ∈ P ∧ x ^ p = 1} = P) (hPcl : ClassLeTwo P)
    (hPrk : pRank p P = 2) (hirr : IsNormalizerIrreducible P) :
    ⁅R, P⁆ = ⊥ ∨ (p = r ∧ IsPOnePlusTwo p ↥R ∧ P ≤ R ⊔ Subgroup.centralizer (R : Set G)) := by
  have hRΩ' := closure_pow_eq_top_of_closure_eq hRΩ
  have hPΩ' := closure_pow_eq_top_of_closure_eq hPΩ
  have hRclt := classLeTwo_top_of hRcl
  have hPclt := classLeTwo_top_of hPcl
  have hRexp : ∀ x : ↥R, x ^ r = 1 := pow_eq_one_of_classLeTwo hr2 hRclt hRΩ'
  have hPexp : ∀ x : ↥P, x ^ p = 1 := pow_eq_one_of_classLeTwo hp2 hPclt hPΩ'
  have hPexp' : ∀ x ∈ P, x ^ p = 1 := fun x hx => by
    simpa using congrArg Subtype.val (hPexp ⟨x, hx⟩)
  have hRrk' : pRank r (⊤ : Subgroup ↥R) ≤ 2 := by rw [pRank_top_subtype]; exact hRrk
  have hPrk' : pRank p (⊤ : Subgroup ↥P) = 2 := by rw [pRank_top_subtype]; exact hPrk
  have hΦ : (frattini ↥P).index = p ^ 2 := index_frattini_eq_sq hp2 hPp hPΩ' hPclt hPrk'
  have hirr' : ∀ U₀ : Subgroup ↥P, frattini ↥P ≤ U₀ → IsNInv P U₀ →
      U₀ = frattini ↥P ∨ U₀ = ⊤ := fun U₀ h1 h2 => eq_frattini_or_eq_top_of_ambient hirr.2 h1 h2
  have hker : ∀ x ∈ P, (MulAut.conjNormal x : MulAut ↥R) ∈ (autQuotient (frattini ↥R)).ker :=
    fun x hx => conjNormal_mem_ker_of_irreducible hr2 hp2 hRr hRexp hRrk' hPexp' hΦ hirr' hx
  have hcomm_of_triv : (∀ x ∈ P, (MulAut.conjNormal x : MulAut ↥R) = 1) → ⁅R, P⁆ = ⊥ := by
    intro h
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact mul_comm_of_conjNormal_eq_one (h x hx) hy
  by_cases hrp : r = p
  · obtain rfl := hrp
    rcases frattini_eq_bot_or_isPOnePlusTwo hr2 hRr hRΩ' hRclt hRrk' with hΦR | hR3
    · left
      exact hcomm_of_triv fun x hx => conjNormal_eq_one_of_frattini_eq_bot hΦR (hker x hx)
    · right
      exact ⟨rfl, hR3, fun x hx => mem_sup_centralizer_of_isPOnePlusTwo hR3 (hker x hx)⟩
  · left
    exact hcomm_of_triv fun x hx =>
      conjNormal_eq_one_of_coprime hrp hRr (hPexp' x hx) (hker x hx)

theorem eq_or_eq_centerOf_of_pRank_eq_two (hr2 : r ≠ 2) (hp2 : p ≠ 2) (hrp : r = p)
    {R : Subgroup G} [R.Normal] (hR1 : R ≠ ⊥) (hRr : IsPGroup r ↥R)
    (hRΩ : Subgroup.closure {x : G | x ∈ R ∧ x ^ r = 1} = R) (hRcl : ClassLeTwo R)
    (hRrk : pRank r R ≤ 2) {P : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPΩ : Subgroup.closure {x : G | x ∈ P ∧ x ^ p = 1} = P) (hPcl : ClassLeTwo P)
    (hPrk : pRank p P = 2) (hirr : IsNormalizerIrreducible P)
    (hG : pRank p (⊤ : Subgroup G) = 2) :
    R = P ∨ (IsElemAbelianOfRank p 1 ↥R ∧ IsPOnePlusTwo p ↥P ∧ R = centerOf P) := by
  obtain rfl := hrp
  have h1 := commutator_eq_bot_or_isPOnePlusTwo hr2 hp2 hRr hRΩ hRcl hRrk hPp hPΩ hPcl hPrk hirr
  have hRΩ' := closure_pow_eq_top_of_closure_eq hRΩ
  have hPΩ' := closure_pow_eq_top_of_closure_eq hPΩ
  have hRclt := classLeTwo_top_of hRcl
  have hPclt := classLeTwo_top_of hPcl
  have hRexp : ∀ x : ↥R, x ^ r = 1 := pow_eq_one_of_classLeTwo hr2 hRclt hRΩ'
  have hPexp : ∀ x : ↥P, x ^ r = 1 := pow_eq_one_of_classLeTwo hp2 hPclt hPΩ'
  have hRexp' : ∀ x ∈ R, x ^ r = 1 := fun x hx => by
    simpa using congrArg Subtype.val (hRexp ⟨x, hx⟩)
  have hPexp' : ∀ x ∈ P, x ^ r = 1 := fun x hx => by
    simpa using congrArg Subtype.val (hPexp ⟨x, hx⟩)
  have hPrk' : pRank r (⊤ : Subgroup ↥P) = 2 := by rw [pRank_top_subtype]; exact hPrk
  have hPstruct := frattini_bot_or_isPOnePlusTwo hp2 hPp hPΩ' hPclt hPrk'
  have hfrattini_bot : frattini ↥P = ⊥ → frattiniIn P = ⊥ := fun h => by
    unfold frattiniIn
    rw [h, Subgroup.map_bot]
  rcases h1 with hcomm | ⟨-, hR3, hPRC⟩
  ·
    have hRP : R ≤ P := by
      intro x hx
      by_contra hxP
      have hx1 : x ≠ 1 := fun h => hxP (h ▸ P.one_mem)
      have hxo : orderOf x = r := orderOf_eq_prime (hRexp' x hx) hx1
      have hxc : ∀ y ∈ P, x * y = y * x := fun y hy =>
        commutatorElement_eq_one_iff_mul_comm.1
          (Subgroup.mem_bot.1 (hcomm ▸ Subgroup.commutator_mem_commutator hx hy))
      have := two_lt_pRank_of_centralizing hPrk hxo hxc hxP
      omega
    rcases inf_le_frattiniIn_or_le (M := R) hirr with hle | hPR
    · right
      have hRΦ : R ≤ frattiniIn P := fun y hy => hle y hy (hRP hy)
      rcases hPstruct with ⟨hΦbot, -⟩ | hP3
      · exfalso
        apply hR1
        rw [eq_bot_iff]
        intro y hy
        have h2 := hRΦ hy
        rw [hfrattini_bot hΦbot] at h2
        exact h2
      · have hfin : frattiniIn P = centerOf P := by
          unfold frattiniIn
          rw [frattini_eq_center_of_isPOnePlusTwo hP3, centerOf_eq_map_center]
        have hcardC : Nat.card (centerOf P) = r := card_centerOf hP3.1
        have hRC : R ≤ centerOf P := hfin ▸ hRΦ
        have hdvd : Nat.card R ∣ r := hcardC ▸ Subgroup.card_dvd_of_le hRC
        have hcardR : Nat.card R = r := by
          rcases (Nat.dvd_prime hr.out).1 hdvd with h | h
          · exact absurd (Subgroup.card_eq_one.1 h) hR1
          · exact h
        have hRcomm : ∀ a b : ↥R, a * b = b * a :=
          commutative_of_card_le_prime_sq hRr (by
            rw [hcardR]
            calc r = r ^ 1 := (pow_one r).symm
              _ ≤ r ^ 2 := Nat.pow_le_pow_right hr.out.pos (by norm_num))
        refine ⟨?_, hP3, Subgroup.eq_of_le_of_card_ge hRC (by rw [hcardR, hcardC])⟩
        exact nonempty_mulEquiv_of_elementary hRcomm hRexp (by rw [pow_one]; exact hcardR)
    · exact Or.inl (le_antisymm hRP hPR)
  ·
    have hPR : P ≤ R := by
      intro x hx
      have hx' : x ∈ ((R ⊔ Subgroup.centralizer (R : Set G) : Subgroup G) : Set G) := hPRC hx
      rw [Subgroup.normal_mul] at hx'
      obtain ⟨y, hy, z, hz, rfl⟩ := hx'
      have hzc : ∀ w ∈ R, z * w = w * z := fun w hw =>
        (Subgroup.mem_centralizer_iff.1 hz w hw).symm
      have hzp : z ^ r = 1 := by
        have hxp : (y * z) ^ r = 1 := hPexp' _ hx
        have hcm : Commute y z := Subgroup.mem_centralizer_iff.1 hz y hy
        rw [hcm.mul_pow, hRexp' y hy, one_mul] at hxp
        exact hxp
      have hzR : z ∈ R := by
        by_contra hzR
        have hz1 : z ≠ 1 := fun h => hzR (h ▸ R.one_mem)
        have hzo : orderOf z = r := orderOf_eq_prime hzp hz1
        have := two_lt_pRank_of_centralizing_element hR3 hzo hzc hzR
        omega
      exact R.mul_mem hy hzR
    rcases hPstruct with ⟨hΦbot, hPcard⟩ | hP3
    · exfalso
      have hRcard : Nat.card R = r ^ 3 := hR3.2.1
      obtain ⟨-, -, -, -, -, hT, -⟩ := nonabelian_prime_cube_central_structure hRcard
        (exists_not_commute_of_isPOnePlusTwo hR3)
      have hTcard : Nat.card (P.subgroupOf R) = r ^ 2 := by
        rw [← hPcard]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv
      have hZP : centerOf R ≤ P := by
        intro z hz
        have hzR : z ∈ R := (mem_centerOf_iff.1 hz).1
        have hzc : (⟨z, hzR⟩ : ↥R) ∈ Subgroup.center ↥R := (coe_mem_centerOf_iff ⟨z, hzR⟩).1 hz
        exact (hT _ hTcard).1 hzc
      have : (centerOf R).Normal := centerOf_normal
      have hcardZ : Nat.card (centerOf R) = r := card_centerOf hR3.1
      rcases inf_le_frattiniIn_or_le (M := centerOf R) hirr with hle | hPZ
      · have hcR : centerOf R = ⊥ := by
          rw [eq_bot_iff]
          intro y hy
          have h2 := hle y hy (hZP hy)
          rw [hfrattini_bot hΦbot] at h2
          exact h2
        rw [hcR, Subgroup.card_bot] at hcardZ
        exact hr.out.one_lt.ne hcardZ
      · have h2 := Subgroup.card_le_of_le hPZ
        rw [hcardZ, hPcard] at h2
        have hr1 := hr.out.one_lt
        nlinarith
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hPR (by rw [hP3.2.1, hR3.2.1])).symm

end A132

end A1c

end CFSG.Quasithin
