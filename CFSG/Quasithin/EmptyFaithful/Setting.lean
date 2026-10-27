module

public import CFSG.Quasithin.QTFE14Cat
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem exists_sylow_of_quasithinIsSylowTwo {T : Subgroup G} (hT : quasithinIsSylowTwo T) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  obtain ⟨hp, hodd⟩ := hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  refine ⟨S, le_antisymm ?_ hS⟩
  by_contra hne
  have hidx : (T.subgroupOf S).index ∣ T.index := by
    have := Subgroup.relIndex_dvd_index_of_le hS
    simpa [Subgroup.relIndex] using this
  have hpow : IsPGroup 2 (↥(S : Subgroup G)) := S.isPGroup'
  have hne1 : (T.subgroupOf S).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
    exact hne h1
  obtain ⟨k, hk⟩ := hpow.index (T.subgroupOf S)
  rcases k with _ | k
  · exact hne1 (by simpa using hk)
  · exact hodd (dvd_trans (by rw [hk]; exact dvd_pow_self 2 (Nat.succ_ne_zero k)) hidx)

theorem quasithinOmegaOneCenter_ne_bot {T : Subgroup G} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    quasithinOmegaOneCenter T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hne
  have hcen : Nontrivial (Subgroup.center T) := hT.center_nontrivial
  have hcard : 2 ∣ Nat.card (Subgroup.center T) := by
    rcases (hT.to_subgroup (Subgroup.center T)).card_eq_or_dvd with h1 | h2
    · exact absurd h1 (Finite.one_lt_card).ne'
    · exact h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2 hcard
  intro hbot
  have hxmem : ((x : T) : G) ∈ quasithinOmegaOneCenter T := by
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_inf.mpr ⟨(x : T).2, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_center_iff.mp x.2 ⟨y, hy⟩
      exact congrArg Subtype.val this
    · have : (x : Subgroup.center T) ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      exact congrArg (fun u : Subgroup.center T => ((u : T) : G)) this
  rw [hbot, Subgroup.mem_bot] at hxmem
  have h1 : x = 1 := by
    apply Subtype.ext; apply Subtype.ext; simpa using hxmem
  rw [h1, orderOf_one] at hx
  exact absurd hx (by decide)

end CFSG.Quasithin

namespace CFSG.Quasithin.quasithinQTFE14Cat

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
include h

theorem exists_sylow : ∃ S : Sylow 2 G, (S : Subgroup G) = T :=
  exists_sylow_of_quasithinIsSylowTwo h.sylow

theorem two_dvd_card : 2 ∣ Nat.card G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hP2, -⟩ := h.mc_max.1
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hP
  obtain ⟨k, hk⟩ := hP2 x
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨i, -, hik⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases i with _ | i
  · exact absurd (orderOf_eq_one_iff.mp (by simpa using hik)) hx1
  · have hpos : 2 ∣ orderOf x := by rw [hik]; exact dvd_pow_self 2 (Nat.succ_ne_zero i)
    have hord : orderOf (x : G) ∣ Nat.card G := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_coe] at hord
    exact dvd_trans hpos hord

theorem ne_bot : T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := h.exists_sylow
  intro hbot
  have hcard := S.card_eq_multiplicity
  rw [hS, hbot, Subgroup.card_bot] at hcard
  have hpos : 0 < (Nat.card G).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h.two_dvd_card
  have := (Nat.pow_eq_one.mp hcard.symm)
  omega

theorem omegaOneCenter_ne_bot : quasithinOmegaOneCenter T ≠ ⊥ :=
  quasithinOmegaOneCenter_ne_bot h.sylow.1 h.ne_bot

theorem inM_mc : InM T Mc := ⟨h.mc_max, h.t_le_mc⟩

theorem isUniqueM_mc :
    IsUniqueM (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) Mc :=
  ⟨⟨h.mc_max, h.centralizer_le_mc⟩, fun M hM => h.mc_unique M hM.1 hM.2⟩

theorem exists_inM_ne : ∃ M : Subgroup G, InM T M ∧ M ≠ Mc := by
  obtain ⟨M, hM, hTM, hne⟩ := h.two_maximal
  exact ⟨M, ⟨hM, hTM⟩, hne⟩

end CFSG.Quasithin.quasithinQTFE14Cat
