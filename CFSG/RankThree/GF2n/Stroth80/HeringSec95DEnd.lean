module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CFive

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

theorem three95_noTwo (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    (hA : Sec9AExistsStatement) (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G)
    (hc : Ctx M Q Z B) (n : ℕ) (t : G) (Z0 : Subgroup G) (cfg : HS9.Cfg95 hc n t Z0)
    (hn7 : 7 ≤ n) (h1 : HS9.One95 hc t Z0) (z : G) (hz : HS9.ZPair95 hc t Z0 z) :
    HS9.Three95 hc t z := by
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t cfg.hs
  have hzN : ∀ c ∈ Z0, z * c * z⁻¹ ∈ hc.CN t := fun c hc0 =>
    (Subgroup.mem_inf.mp (hz.toN1 c hc0)).2
  have hnot : ¬ conjSubgroup z (HS9.N1 hc t) ≤ HS9.N1 hc t := by
    intro hle
    have heq : conjSubgroup z (HS9.N1 hc t) = HS9.N1 hc t :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
    have hZ0 := h1 z hz.mem heq
    obtain ⟨c, hc0, hcn⟩ := hz.notN
    apply hcn
    have : z * c * z⁻¹ ∈ conjSubgroup z Z0 := HS9.conj_mem95 z hc0
    rwa [hZ0] at this
  refine ⟨⟨?_, HS9.relIndex_N1_conj_le h34 h91b cfg.hs hr cfg.centre hz.mem hz.normL hzN hnot⟩,
    ?_⟩
  · exact lt_of_le_of_ne le_sup_left (fun h => hnot (le_sup_right.trans h.symm.le))
  · intro x hx hxN
    exact HS9.isTypeA2_of_conj95 h34 h91b cfg.hs hr hn7 hz.mem hz.normL hx hxN

theorem five95_noTwo (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    (hA : Sec9AExistsStatement) (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G)
    (hc : Ctx M Q Z B) (n : ℕ) (t : G) (Z0 : Subgroup G) (cfg : HS9.Cfg95 hc n t Z0)
    (hn7 : 7 ≤ n) (z : G) (hz : HS9.ZPair95 hc t Z0 z) (h3 : HS9.Three95 hc t z) :
    HS9.Five95 hc t z := by
  classical
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t cfg.hs
  have hs := cfg.hs
  have ht : t ∈ LB M Q B := hs.mem
  have hzN : ∀ c ∈ Z0, z * c * z⁻¹ ∈ hc.CN t := fun c hc0 =>
    (Subgroup.mem_inf.mp (hz.toN1 c hc0)).2
  have hnot : ¬ conjSubgroup z (HS9.N1 hc t) ≤ HS9.N1 hc t := fun hle =>
    not_le_of_gt h3.1.1 (sup_le le_rfl hle)
  have hex := HS9.exists_notCN_conj95 hz.normL hnot
  have hzi : z⁻¹ ∈ M := M.inv_mem hz.mem
  have hzLi : conjSubgroup z⁻¹ (LB M Q B) = LB M Q B := by
    rw [conjSubgroup_eq_self_iff]
    exact (Subgroup.normalizer ((LB M Q B : Subgroup G) : Set G)).inv_mem
      (conjSubgroup_eq_self_iff.mp hz.normL)
  have hzNi : ∀ c ∈ Z0, z⁻¹ * c * z⁻¹⁻¹ ∈ hc.CN t := by
    intro c hc0
    refine cfg.hbad c hc0 z⁻¹ hzi ?_
    have hcL : c ∈ LB M Q B := (Subgroup.mem_inf.mp (cfg.centre.1 hc0)).1
    have := HS9.conj_mem95 z⁻¹ hcL
    rwa [hzLi] at this
  have hnoti : ¬ conjSubgroup z⁻¹ (HS9.N1 hc t) ≤ HS9.N1 hc t := by
    intro hle
    have heq : conjSubgroup z⁻¹ (HS9.N1 hc t) = HS9.N1 hc t :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
    apply hnot
    intro x hx
    have h5 : z⁻¹ * x * z ∈ conjSubgroup z⁻¹ (HS9.N1 hc t) := by
      rw [heq]
      exact mem_conjSubgroup.mp hx
    rw [mem_conjSubgroup] at h5
    have e : z⁻¹⁻¹ * (z⁻¹ * x * z) * z⁻¹ = x := by group
    rwa [e] at h5
  have hexi := HS9.exists_notCN_conj95 hzLi hnoti
  have hsing := HS9.isSingV_of_mem_inf_conj95 h34 h91b hs hr hn7 cfg.centre hz.mem hz.normL hzN
    hex
  have hsingi := HS9.isSingV_of_mem_inf_conj95 h34 h91b hs hr hn7 cfg.centre hzi hzLi hzNi hexi
  obtain ⟨x₀, hx₀z, hx₀N⟩ := hex
  have hx₀L : x₀ ∈ LB M Q B := by
    have : x₀ ∈ conjSubgroup z (LB M Q B) :=
      mem_conjSubgroup.mpr (Subgroup.mem_inf.mp (mem_conjSubgroup.mp hx₀z)).1
    rwa [hz.normL] at this
  obtain ⟨K, fK, finK, hK2, hnrm, ⟨C⟩⟩ := HS9.exists_coord95 h34 hs hr
  obtain ⟨y₀, hy₀, rfl⟩ : ∃ y₀ ∈ HS9.N1 hc t, z * y₀ * z⁻¹ = x₀ :=
    ⟨z⁻¹ * x₀ * z, mem_conjSubgroup.mp hx₀z, by group⟩
  obtain ⟨w, -, -, -, hcard, -, -⟩ := C.plane_facts hs hx₀L hx₀N
  obtain ⟨-, hY⟩ := C.cent_eq_inf h34 h91b hs hr cfg.centre hz.mem hzN
    (Subgroup.mem_inf.mp hy₀).2 hx₀L hx₀N
  refine ⟨?_, HS9.B_le_inf_conj95 h34 hs hz.mem hz.normL, hsing, ?_, ?_⟩
  · rw [← hY]
    exact hcard
  · intro u hu
    have hu' : z⁻¹ * u * z ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z⁻¹ (Vt M (LB M Q B) B Z t) :=
      ⟨mem_conjSubgroup.mp hu.2, HS9.conj_inv_mem95 z hu.1⟩
    exact HS9.isSingV_conj95 (hc := hc) hz.mem (HS9.mem_normalizer_BZ95 h34 hs hz.mem hz.normL)
      (hsingi _ hu')
  · intro x hx hxN
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ HS9.N1 hc t, z * y * z⁻¹ = x :=
      ⟨z⁻¹ * x * z, mem_conjSubgroup.mp hx, by group⟩
    have hxL : z * y * z⁻¹ ∈ LB M Q B := by
      have : z * y * z⁻¹ ∈ conjSubgroup z (LB M Q B) :=
        HS9.conj_mem95 z (Subgroup.mem_inf.mp hy).1
      rwa [hz.normL] at this
    exact (C.cent_eq_inf h34 h91b hs hr cfg.centre hz.mem hzN (Subgroup.mem_inf.mp hy).2 hxL
      hxN).2

end CFSG.RankThree.GF2n.Stroth80
