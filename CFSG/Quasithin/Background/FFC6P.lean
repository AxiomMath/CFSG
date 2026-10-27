module

public import CFSG.Quasithin.Background.B4L3FactA
public import CFSG.Quasithin.Background.B4L3Off
public import CFSG.Quasithin.Background.FFC5T7

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace B59

section Generic

variable {V : Type} [CommGroup V]

theorem exists_complement_in (hV : ∀ v : V, v ^ 2 = 1) {C F : Subgroup V} (hCF : C ≤ F) :
    ∃ F'' : Subgroup V, F'' ≤ F ∧ F'' ⊓ C = ⊥ ∧ F'' ⊔ C = F := by
  have hF : ∀ v : ↥F, v ^ 2 = 1 := fun v => Subtype.ext (hV v)
  have : IsElementaryAbelian 2 ↥F :=
    ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hF⟩
  obtain ⟨S, hS⟩ := IsElementaryAbelian.exists_isCompl 2 ↥F (C.subgroupOf F)
  have hd : S ⊓ C.subgroupOf F = ⊥ := disjoint_iff.1 hS.symm.disjoint
  have hc : S ⊔ C.subgroupOf F = ⊤ := codisjoint_iff.1 hS.symm.codisjoint
  refine ⟨S.map F.subtype, Subgroup.map_subtype_le S, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨⟨s, hs, rfl⟩, hxC⟩
    have h1 : s ∈ S ⊓ C.subgroupOf F := ⟨hs, hxC⟩
    rw [hd, Subgroup.mem_bot] at h1
    rw [h1]
    exact Subgroup.one_mem _
  · refine le_antisymm (sup_le (Subgroup.map_subtype_le S) hCF) ?_
    intro f hf
    have h1 : (⟨f, hf⟩ : ↥F) ∈ S ⊔ C.subgroupOf F := by rw [hc]; trivial
    obtain ⟨s, hs, c, hc', hsc⟩ := Subgroup.mem_sup.1 h1
    have hfeq : f = (s : V) * (c : V) := by
      have := congrArg Subtype.val hsc
      simpa using this.symm
    rw [hfeq]
    exact Subgroup.mul_mem_sup ⟨s, hs, rfl⟩ hc'

section Indec

variable [Finite V]

theorem not_decomp_of_card {L : Subgroup (MulAut V)} {U : Subgroup V} (hcomm : commSub U L = U)
    (hirr : ∀ J : Subgroup V, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → U ⊓ fixV L ≤ J → J ≤ U →
      J = U ⊓ fixV L ∨ J = U)
    (hUc : Nat.card ↥U = 16) (hCc : Nat.card ↥(U ⊓ fixV L) = 2) :
    ¬ ∃ A' B' : Subgroup V, ⊥ < A' ∧ ⊥ < B' ∧ XMod.IsInv ↥L A' ∧ XMod.IsInv ↥L B' ∧
      A' ⊔ B' = U ∧ A' ⊓ B' = ⊥ := by
  rintro ⟨A', B', hA, hB, hAi, hBi, hsup, hinf⟩
  have hAi' : ∀ x ∈ L, ∀ w ∈ A', x w ∈ A' := fun x hx w hw => hAi ⟨x, hx⟩ w hw
  have hBi' : ∀ x ∈ L, ∀ w ∈ B', x w ∈ B' := fun x hx w hw => hBi ⟨x, hx⟩ w hw
  have key : ∀ {P Q : Subgroup V}, P ⊔ Q = U → P ≤ fixV L → (∀ x ∈ L, ∀ w ∈ Q, x w ∈ Q) →
      Q = U := by
    intro P Q hPQ hPf hQi
    apply le_antisymm (hPQ ▸ le_sup_right)
    rw [← hcomm]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, u, hu, rfl⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := Subgroup.mem_sup.1 (hPQ ▸ hu)
    have h1 : x (p * q) * (p * q)⁻¹ = x q * q⁻¹ := by
      rw [map_mul, hPf hp x hx, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
    rw [h1]
    exact Q.mul_mem (hQi x hx q hq) (Q.inv_mem hq)
  have hC : ∀ x ∈ L, ∀ w ∈ U ⊓ fixV L, x w ∈ U ⊓ fixV L := fun x hx w hw => by
    rw [hw.2 x hx]
    exact hw
  have hAU : A' ≤ U := hsup ▸ le_sup_left
  have hBU : B' ≤ U := hsup ▸ le_sup_right
  have hAC : A' ⊔ U ⊓ fixV L = U := by
    rcases hirr (A' ⊔ U ⊓ fixV L) (by
        intro x hx w hw
        obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
        rw [map_mul]
        exact Subgroup.mul_mem_sup (hAi' x hx a ha) (hC x hx c hc))
      le_sup_right (sup_le hAU inf_le_left) with h | h
    · exfalso
      have hAC' : A' ≤ U ⊓ fixV L := h ▸ le_sup_left
      have hAf : A' ≤ fixV L := fun a ha => (hAC' ha).2
      have hBeq := key hsup hAf hBi'
      have : A' = ⊥ := by
        rw [eq_bot_iff, ← hinf]
        exact le_inf le_rfl (hBeq ▸ hAU)
      exact hA.ne' this
    · exact h
  have hBC : B' ⊔ U ⊓ fixV L = U := by
    rcases hirr (B' ⊔ U ⊓ fixV L) (by
        intro x hx w hw
        obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
        rw [map_mul]
        exact Subgroup.mul_mem_sup (hBi' x hx a ha) (hC x hx c hc))
      le_sup_right (sup_le hBU inf_le_left) with h | h
    · exfalso
      have hBC' : B' ≤ U ⊓ fixV L := h ▸ le_sup_left
      have hBf : B' ≤ fixV L := fun a ha => (hBC' ha).2
      have hAeq := key (by rwa [sup_comm]) hBf hAi'
      have : B' = ⊥ := by
        rw [eq_bot_iff, ← hinf]
        exact le_inf (hAeq ▸ hBU) le_rfl
      exact hB.ne' this
    · exact h
  have h1 : 16 ≤ Nat.card ↥A' * 2 := by
    have := card_sup_le_mul A' (U ⊓ fixV L)
    rw [hAC, hUc, hCc] at this
    exact this
  have h2 : 16 ≤ Nat.card ↥B' * 2 := by
    have := card_sup_le_mul B' (U ⊓ fixV L)
    rw [hBC, hUc, hCc] at this
    exact this
  have h3 := card_sup_mul_card_inf A' B'
  rw [hsup, hinf, Subgroup.card_bot, mul_one, hUc] at h3
  nlinarith

end Indec

end Generic

section Restrict

variable {V : Type} [CommGroup V]

theorem realizesVia_comap {L : Subgroup (MulAut V)} {U : Subgroup V} (hst : L ≤ stabSub U)
    (hf : ∀ g ∈ L, (∀ v ∈ U, g v = v) → g = 1) {D : FFModel} {Z : Subgroup V} {π : D.Gam →* ↥L}
    (h : D.RealizesVia L U Z π) :
    D.RealizesVia (autSub L U) (⊤ : Subgroup ↥U) (Z.comap U.subtype)
      ((resEquiv hst hf).toMonoidHom.comp π) := by
  obtain ⟨hsurj, hZU, hkersec, hHU, hHZ, hsec, hker, β, hβs, hβk, hβe⟩ := h
  refine ⟨(resEquiv hst hf).surjective.comp hsurj, le_top, hkersec, fun _ _ _ => trivial, ?_, hsec,
    hker, ?_⟩
  · intro h' z hz
    obtain ⟨g, rfl⟩ := (resEquiv hst hf).surjective h'
    exact hHZ g z hz
  · refine ⟨β.comp (⊤ : Subgroup ↥U).subtype, hβs.comp fun u => ⟨⟨u, trivial⟩, rfl⟩,
      fun u => hβk _, ?_⟩
    intro γ u m hu hm hbu
    exact hβe γ _ m (hHU (π γ) _ (u : ↥U).2) hm hbu

theorem realizes_comap {L : Subgroup (MulAut V)} {U : Subgroup V} (hst : L ≤ stabSub U)
    (hf : ∀ g ∈ L, (∀ v ∈ U, g v = v) → g = 1) {D : FFModel} {Z : Subgroup V}
    (h : D.Realizes L U Z) : D.Realizes (autSub L U) (⊤ : Subgroup ↥U) (Z.comap U.subtype) := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨_, realizesVia_comap hst hf hπ⟩

theorem isIndecompModule_autSub {L : Subgroup (MulAut V)} {U : Subgroup V} (hst : L ≤ stabSub U)
    (h : ¬ ∃ A' B' : Subgroup V, ⊥ < A' ∧ ⊥ < B' ∧ XMod.IsInv ↥L A' ∧ XMod.IsInv ↥L B' ∧
      A' ⊔ B' = U ∧ A' ⊓ B' = ⊥) : IsIndecompModule (autSub L U) := by
  intro X' Y' hX hY hXY hsup
  by_contra hne
  rw [not_or] at hne
  apply h
  have hinv : ∀ Z' : Subgroup ↥U, (∀ g ∈ autSub L U, ∀ z ∈ Z', g z ∈ Z') →
      XMod.IsInv ↥L (Z'.map U.subtype) := by
    intro Z' hZ' g _ hz
    obtain ⟨z, hz', rfl⟩ := hz
    exact ⟨_, hZ' _ (mem_autSub.2 ⟨⟨g, hst g.2⟩, g.2, rfl⟩) z hz', rfl⟩
  refine ⟨X'.map U.subtype, Y'.map U.subtype, ?_, ?_, hinv X' hX, hinv Y' hY, ?_, ?_⟩
  · refine bot_lt_iff_ne_bot.2 fun hb => hne.1 ?_
    exact (Subgroup.map_eq_bot_iff_of_injective X' U.subtype_injective).1 hb
  · refine bot_lt_iff_ne_bot.2 fun hb => hne.2 ?_
    exact (Subgroup.map_eq_bot_iff_of_injective Y' U.subtype_injective).1 hb
  · rw [← Subgroup.map_sup, hsup, Subgroup.map_top, Subgroup.range_subtype]
  · rw [← Subgroup.map_inf _ _ _ U.subtype_injective, hXY, Subgroup.map_bot]

end Restrict

section Off

variable {W : Type} [CommGroup W] [Finite W]

theorem offHyp_card_offender {G : Subgroup (MulAut W)} (H : OffHyp G) {A : Subgroup (MulAut W)}
    (hA : IsFFStarOffender G A) : Nat.card ↥A = 4 ∧ Nat.card ↥(fixV A) = 4 := by
  obtain ⟨hAG, hAne, hAel, hAoff⟩ := hA
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAne
  have ha1' : (a : MulAut W) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haA' : (a : MulAut W) ∈ A := a.2
  have hAcard : Nat.card ↥A ≤ 4 := H.E4 A hAG hAel
  have hVle := hAoff ⊥ bot_le
  rw [B1.card_bot_mul_card_fixV, H.card_four] at hVle
  have hfx : Nat.card ↥(fixV A) ≤ 4 := H.card_fixV_le hAG hAel haA' ha1'
  have hcA : Nat.card ↥A = 4 := by
    by_contra hne
    have h3 : Nat.card ↥A ≤ 3 := by omega
    have : Nat.card ↥A * Nat.card ↥(fixV A) ≤ 3 * 4 := Nat.mul_le_mul h3 hfx
    omega
  refine ⟨hcA, ?_⟩
  rw [hcA] at hVle
  omega

end Off

end B59

end FFC

end CFSG.Quasithin
