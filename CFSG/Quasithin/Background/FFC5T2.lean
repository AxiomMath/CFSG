module

public import CFSG.Quasithin.Background.FFC5Coh3
public import CFSG.Quasithin.Background.FFC5Idx

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section T2

variable {V : Type} [CommGroup V]

theorem natural3_facts {L : Subgroup (MulAut V)} {U : Subgroup V} (hnat : BinaryNaturalSL L U ⊥ 3 1) :
    Nonempty (↥L ≃* ↥(StatedSL 3 (ZMod 2))) ∧ Nat.card ↥U = 2 ^ 3 := by
  obtain ⟨D⟩ := exists_natQuot3 hnat
  refine ⟨⟨(MulEquiv.ofBijective D.ρ ⟨D.inj, D.surj⟩).symm.trans
    (specialLinearGroupEquivStatedSL 3 (ZMod 2))⟩, ?_⟩
  have hθi : Function.Injective D.θ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((D.θ_ker u).1 hu))
  rw [Nat.card_congr (MulEquiv.ofBijective D.θ ⟨hθi, D.θ_surj⟩).toEquiv]
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2))]
  simp [Nat.card_eq_fintype_card, ZMod.card]

namespace B510Fa

variable {G G₁ G₂ : Subgroup (MulAut V)} (h : B510Fa G G₁ G₂)

include h in
theorem case5_of [Finite V] (hnat : BinaryNaturalSL G₁ (commV G₁) ⊥ 3 1)
    (hidx : (commV G₁ ⊔ fixV G₁).index = 2) (hV₂ : fixV G₁ = commV G₂ ⊔ fixV G)
    (hlast : (Nonempty (↥G₂ ≃* ↥(StatedSL 3 (ZMod 2))) ∧ ∃ k : ℕ, k ≤ 2 ∧
        DirectSumOfCopies G₂ (commV G₂) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) k) ∨
      ∃ n, BinaryNaturalSL G₂ (commV G₂) (fixV G₂ ⊓ commV G₂) 2 n) : B56Case5 G := by
  obtain ⟨hiso, hcard⟩ := natural3_facts hnat
  refine ⟨G₁, G₂, h.sup, h.inf, h.comm, ⟨?_, ?_⟩, hiso, hcard, ?_, hlast⟩
  · rw [← h.sup, B19.commV_sup]
  · rw [eq_bot_iff]
    have hbot : fixV G₁ ⊓ commV G₁ = ⊥ := by
      obtain ⟨K, hK, hf, hc, π, hπ⟩ := hnat
      exact fixV_inf_eq_bot_of_nat (by norm_num : 2 ≤ 3) hπ
    calc commV G₁ ⊓ commV G₂ ≤ commV G₁ ⊓ fixV G₁ := inf_le_inf_left _ h.commV_le
      _ = ⊥ := by rw [inf_comm]; exact hbot
      _ ≤ ⊥ := le_rfl
  · have hcomm : commV G = commV G₁ ⊔ commV G₂ := by rw [← h.sup, B19.commV_sup]
    rw [hcomm, sup_assoc, ← hV₂]
    exact hidx

end B510Fa

end T2

section Restrict

variable {V : Type} [CommGroup V]

theorem realizesVia_restrict {D : FFModel} {H : Subgroup (MulAut V)} {U Z U' : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) (hsup : U' ⊔ Z = U)
    (hinv : ∀ g : ↥H, ∀ u ∈ U', (g : MulAut V) u ∈ U') : D.RealizesVia H U' (Z ⊓ U') π := by
  obtain ⟨hπs, hZU, hker, hHU, hHZ, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  have hU'U : U' ≤ U := hsup ▸ le_sup_left
  refine ⟨hπs, inf_le_right, hker, hinv, fun g z hz => ⟨hHZ g z hz.1, hinv g z hz.2⟩, hsec, hkerinv,
    β.comp (Subgroup.inclusion hU'U), ?_, ?_, ?_⟩
  · intro q
    obtain ⟨u, hu⟩ := hβs q
    have hmem : (u : V) ∈ U' ⊔ Z := by rw [hsup]; exact u.2
    obtain ⟨u', hu', z, hz, huz⟩ := Subgroup.mem_sup.1 hmem
    refine ⟨⟨u', hu'⟩, ?_⟩
    have h1 : u = (Subgroup.inclusion hU'U ⟨u', hu'⟩) * ⟨z, hZU hz⟩ := Subtype.ext huz.symm
    have h2 : β ⟨z, hZU hz⟩ = 1 := (hβk _).2 hz
    show β (Subgroup.inclusion hU'U ⟨u', hu'⟩) = q
    rw [← hu, h1, map_mul, h2, mul_one]
  · intro u'
    show β (Subgroup.inclusion hU'U u') = 1 ↔ (u' : V) ∈ Z ⊓ U'
    rw [hβk]
    exact ⟨fun h => ⟨h, u'.2⟩, fun h => h.1⟩
  · intro γ u' m hu hm hbu
    exact hβe γ (Subgroup.inclusion hU'U u') m (hU'U hu) hm hbu

end Restrict

end FFC

end CFSG.Quasithin
