module

public import CFSG.Quasithin.Background.F918Z8g
public import CFSG.Quasithin.Background.F918H3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeSecHom

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

section

variable {Y : Type} [CommGroup Y] {I J : Subgroup Y}

theorem sxc_stab_secPre (g : ↥(stabSub I ⊓ stabSub J)) (S : Subgroup (Sec I J)) :
    (g : MulAut Y) ∈ stabSub (d321f_secPre I J S) ↔ Bridge.secHom I J g ∈ stabSub S := by
  have hgI : (g : MulAut Y) ∈ stabSub I := g.2.1
  have key : ∀ (u : Y) (hu : u ∈ I), (g : MulAut Y) u ∈ d321f_secPre I J S ↔
      Bridge.secHom I J g (QuotientGroup.mk ⟨u, hu⟩) ∈ S := by
    intro u hu
    rw [Bridge.secHom_apply, d321f_mem_secPre]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(hgI u).2 hu, h⟩⟩
  constructor
  · intro h q
    obtain ⟨⟨u, hu⟩, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← key u hu, h u, d321f_mem_secPre]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩
  · intro h u
    by_cases hu : u ∈ I
    · rw [key u hu, h (QuotientGroup.mk ⟨u, hu⟩), d321f_mem_secPre]
      exact ⟨fun h => ⟨hu, h⟩, fun ⟨_, h⟩ => h⟩
    · have h1 : (g : MulAut Y) u ∉ I := fun h' => hu ((hgI u).1 h')
      exact ⟨fun h2 => absurd (d321f_secPre_le S h2) h1, fun h2 => absurd (d321f_secPre_le S h2) hu⟩

theorem sxc_le_stab_iff {A : Subgroup (MulAut Y)} (hAK : A ≤ stabSub I ⊓ stabSub J)
    (S : Subgroup (Sec I J)) :
    A ≤ stabSub (d321f_secPre I J S) ↔ autSec A I J ≤ stabSub S := by
  constructor
  · intro h ψ hψ
    obtain ⟨g, hg, rfl⟩ := (Bridge.mem_autSec_iff_secHom hAK).1 hψ
    exact (sxc_stab_secPre g S).1 (h hg)
  · intro h g hg
    exact (sxc_stab_secPre ⟨g, hAK hg⟩ S).2
      (h ((Bridge.mem_autSec_iff_secHom hAK).2 ⟨⟨g, hAK hg⟩, hg, rfl⟩))

theorem sxc_autSec_inf_stab {A : Subgroup (MulAut Y)} (hAK : A ≤ stabSub I ⊓ stabSub J)
    (S : Subgroup (Sec I J)) :
    autSec (A ⊓ stabSub (d321f_secPre I J S)) I J = autSec A I J ⊓ stabSub S := by
  have hA₁K : A ⊓ stabSub (d321f_secPre I J S) ≤ stabSub I ⊓ stabSub J := inf_le_left.trans hAK
  ext ψ
  constructor
  · intro hψ
    obtain ⟨g, hg, rfl⟩ := (Bridge.mem_autSec_iff_secHom hA₁K).1 hψ
    exact ⟨(Bridge.mem_autSec_iff_secHom hAK).2 ⟨g, hg.1, rfl⟩, (sxc_stab_secPre g S).1 hg.2⟩
  · rintro ⟨hψA, hψS⟩
    obtain ⟨g, hg, rfl⟩ := (Bridge.mem_autSec_iff_secHom hAK).1 hψA
    exact (Bridge.mem_autSec_iff_secHom hA₁K).2 ⟨g, ⟨hg, (sxc_stab_secPre g S).2 hψS⟩, rfl⟩

theorem sxc_centSec_le_stab {I₀ : Subgroup Y} (hJI₀ : J ≤ I₀) (hI₀I : I₀ ≤ I) :
    centSec I J ≤ stabSub I₀ := by
  intro g hg u
  by_cases hu : u ∈ I
  · have h1 : g u * u⁻¹ ∈ I₀ := hJI₀ (hg.2 u hu)
    constructor
    · intro hgu
      have := I₀.mul_mem (I₀.inv_mem h1) hgu
      have e : (g u * u⁻¹)⁻¹ * g u = u := by group
      rwa [e] at this
    · intro hu₀
      have := I₀.mul_mem h1 hu₀
      have e : g u * u⁻¹ * u = g u := by group
      rwa [e] at this
  · have h1 : g u ∉ I := fun h => hu ((hg.1 u).1 h)
    exact ⟨fun h => absurd (hI₀I h) h1, fun h => absurd (hI₀I h) hu⟩

theorem sxc_mem_stabSub [Finite Y] {t : MulAut Y} {I : Subgroup Y} (h : ∀ w ∈ I, t w ∈ I) :
    t ∈ stabSub I := by
  have hle : I.map t.toMonoidHom ≤ I := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  have hcard : Nat.card I ≤ Nat.card (I.map t.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective t.injective]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  intro u
  refine ⟨fun hu => ?_, h u⟩
  have h1 : t u ∈ I.map t.toMonoidHom := by rw [heq]; exact hu
  obtain ⟨v, hv, hvu⟩ := h1
  have h2 : v = u := t.injective hvu
  rwa [← h2]

theorem sxc_secPre_bot (hJI : J ≤ I) : d321f_secPre I J ⊥ = J := by
  ext u
  rw [d321f_mem_secPre]
  constructor
  · rintro ⟨hu, h⟩
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h
    simpa [Subgroup.mem_subgroupOf] using h
  · intro hu
    exact ⟨hJI hu, Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff _).2
      (by simpa [Subgroup.mem_subgroupOf] using hu))⟩

theorem sxc_secPre_top : d321f_secPre I J ⊤ = I := by
  ext u
  rw [d321f_mem_secPre]
  exact ⟨fun ⟨hu, _⟩ => hu, fun hu => ⟨hu, trivial⟩⟩

theorem sxc_secPre_eq_bot {S : Subgroup (Sec I J)} (h : d321f_secPre I J S = J) : S = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun s hs => ?_
  obtain ⟨⟨u, hu⟩, rfl⟩ := QuotientGroup.mk_surjective s
  have hu₀ : u ∈ d321f_secPre I J S := d321f_mem_secPre.2 ⟨hu, hs⟩
  rw [h] at hu₀
  exact (QuotientGroup.eq_one_iff _).2 (by simpa [Subgroup.mem_subgroupOf] using hu₀)

theorem sxc_secPre_eq_top {S : Subgroup (Sec I J)} (h : d321f_secPre I J S = I) : S = ⊤ := by
  refine eq_top_iff.2 fun s _ => ?_
  obtain ⟨⟨u, hu⟩, rfl⟩ := QuotientGroup.mk_surjective s
  have hu₀ : u ∈ d321f_secPre I J S := by rw [h]; exact hu
  exact (d321f_mem_secPre.1 hu₀).2

theorem sxc_lt_secPre (hJI : J ≤ I) {S : Subgroup (Sec I J)} (hS : S ≠ ⊥) :
    J < d321f_secPre I J S :=
  lt_of_le_of_ne (d321f_le_secPre hJI S) fun h => hS (sxc_secPre_eq_bot h.symm)

theorem sxc_secPre_lt {S : Subgroup (Sec I J)} (hS : S ≠ ⊤) : d321f_secPre I J S < I :=
  lt_of_le_of_ne (d321f_secPre_le S) fun h => hS (sxc_secPre_eq_top h)

def sxc_secImage (I J T : Subgroup Y) : Subgroup (Sec I J) :=
  (T.subgroupOf I).map (QuotientGroup.mk' (J.subgroupOf I))

theorem sxc_mk_mem_secImage {T : Subgroup Y} (hJT : J ≤ T) (u : ↥I) :
    (QuotientGroup.mk u : Sec I J) ∈ sxc_secImage I J T ↔ (u : Y) ∈ T := by
  constructor
  · rintro ⟨t, ht, hte⟩
    have h1 : t⁻¹ * u ∈ J.subgroupOf I := QuotientGroup.eq.1 hte
    have h2 : ((t⁻¹ * u : ↥I) : Y) ∈ J := h1
    have h3 : (u : Y) = (t : Y) * ((t⁻¹ * u : ↥I) : Y) := by simp
    rw [h3]
    exact T.mul_mem ht (hJT h2)
  · intro hu
    exact ⟨u, hu, rfl⟩

theorem sxc_secPre_secImage {T : Subgroup Y} (hJT : J ≤ T) (hTI : T ≤ I) :
    d321f_secPre I J (sxc_secImage I J T) = T := by
  ext u
  rw [d321f_mem_secPre]
  constructor
  · rintro ⟨hu, h⟩
    exact (sxc_mk_mem_secImage hJT ⟨u, hu⟩).1 h
  · intro hu
    exact ⟨hTI hu, (sxc_mk_mem_secImage hJT ⟨u, hTI hu⟩).2 hu⟩

theorem sxc_xirr_secPre {X : Subgroup (MulAut Y)} (hXI : X ≤ stabSub I) (hXJ : X ≤ stabSub J)
    {L : Subgroup (Sec I J)} (hL : XMod.IsIrr ↥(autSec X I J) L) (T : Subgroup Y) (hJT : J ≤ T)
    (hTI₀ : T ≤ d321f_secPre I J L) (hXT : ∀ x ∈ X, ∀ s ∈ T, x s ∈ T) :
    T = J ∨ T = d321f_secPre I J L := by
  have hXK : X ≤ stabSub I ⊓ stabSub J := le_inf hXI hXJ
  have hTI : T ≤ I := hTI₀.trans (d321f_secPre_le L)
  have hinv : XMod.IsInv ↥(autSec X I J) (sxc_secImage I J T) := by
    intro a q hq
    obtain ⟨g, hgX, hga⟩ := (Bridge.mem_autSec_iff_secHom hXK).1 a.2
    obtain ⟨⟨u, hu⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hu' : u ∈ T := (sxc_mk_mem_secImage hJT ⟨u, hu⟩).1 hq
    have e : a • (QuotientGroup.mk ⟨u, hu⟩ : Sec I J) =
        Bridge.secHom I J g (QuotientGroup.mk ⟨u, hu⟩) := by rw [hga]; rfl
    rw [e, Bridge.secHom_apply]
    exact (sxc_mk_mem_secImage hJT _).2 (hXT _ hgX u hu')
  have hle : sxc_secImage I J T ≤ L := by
    intro q hq
    obtain ⟨⟨u, hu⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hu' : u ∈ T := (sxc_mk_mem_secImage hJT ⟨u, hu⟩).1 hq
    exact (d321f_mem_secPre.1 (hTI₀ hu')).2
  rcases hL.2.2 _ hinv bot_le hle with h | h
  · left
    refine le_antisymm (fun u hu => ?_) hJT
    have h1 := (sxc_mk_mem_secImage hJT ⟨u, hTI hu⟩).2 hu
    rw [h, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
    simpa [Subgroup.mem_subgroupOf] using h1
  · right
    rw [← h, sxc_secPre_secImage hJT hTI]

theorem sxc_irr_Q {X A : Subgroup (MulAut Y)} {t : MulAut Y} (hJI : J ≤ I)
    (hXK : X ≤ stabSub I ⊓ stabSub J) (hAK : A ≤ stabSub I ⊓ stabSub J)
    (ht : t ∈ stabSub I ⊓ stabSub J)
    (hirrΞ : ∀ T : Subgroup Y, J ≤ T → T ≤ I → (∀ x ∈ X, ∀ s ∈ T, x s ∈ T) →
      (∀ a ∈ A, ∀ s ∈ T, a s ∈ T) → (∀ s ∈ T, t s ∈ T) → T = J ∨ T = I)
    (T' : Subgroup (Sec I J)) (hX : autSec X I J ≤ stabSub T') (hA : autSec A I J ≤ stabSub T')
    (ht' : ∀ s ∈ T', Bridge.secHom I J ⟨t, ht⟩ s ∈ T') : T' = ⊥ ∨ T' = ⊤ := by
  have key : ∀ g : ↥(stabSub I ⊓ stabSub J), Bridge.secHom I J g ∈ stabSub T' →
      ∀ s ∈ d321f_secPre I J T', (g : MulAut Y) s ∈ d321f_secPre I J T' := by
    intro g hg s hs
    obtain ⟨hsI, hs'⟩ := d321f_mem_secPre.1 hs
    exact d321f_mem_secPre.2 ⟨(g.2.1 s).2 hsI, (hg (QuotientGroup.mk ⟨s, hsI⟩)).2 hs'⟩
  rcases hirrΞ (d321f_secPre I J T') (d321f_le_secPre hJI T') (d321f_secPre_le T')
    (fun x hx => key ⟨x, hXK hx⟩
      (hX ((Bridge.mem_autSec_iff_secHom hXK).2 ⟨⟨x, hXK hx⟩, hx, rfl⟩)))
    (fun a ha => key ⟨a, hAK ha⟩
      (hA ((Bridge.mem_autSec_iff_secHom hAK).2 ⟨⟨a, hAK ha⟩, ha, rfl⟩)))
    (fun s hs => by
      obtain ⟨hsI, hs'⟩ := d321f_mem_secPre.1 hs
      exact d321f_mem_secPre.2 ⟨(ht.1 s).2 hsI, ht' _ hs'⟩) with h | h
  · exact Or.inl (sxc_secPre_eq_bot h)
  · exact Or.inr (sxc_secPre_eq_top h)

theorem sxc_notX_Q {X : Subgroup (MulAut Y)} (hXK : X ≤ stabSub I ⊓ stabSub J) (hJI : J ≤ I)
    (hnotX : ∃ T : Subgroup Y, J ≤ T ∧ T ≤ I ∧ (∀ x ∈ X, ∀ s ∈ T, x s ∈ T) ∧ T ≠ J ∧ T ≠ I) :
    ∃ T' : Subgroup (Sec I J), autSec X I J ≤ stabSub T' ∧ T' ≠ ⊥ ∧ T' ≠ ⊤ := by
  obtain ⟨T, hJT, hTI, hXT, hTJ, hTI'⟩ := hnotX
  refine ⟨sxc_secImage I J T, le_stabSub_of_forall_mem fun a ha q hq => ?_, fun h => ?_,
    fun h => ?_⟩
  · obtain ⟨g, hgX, rfl⟩ := (Bridge.mem_autSec_iff_secHom hXK).1 ha
    obtain ⟨⟨u, hu⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hu' : u ∈ T := (sxc_mk_mem_secImage hJT ⟨u, hu⟩).1 hq
    rw [Bridge.secHom_apply]
    exact (sxc_mk_mem_secImage hJT _).2 (hXT _ hgX u hu')
  · apply hTJ
    rw [← sxc_secPre_secImage hJT hTI, h]
    exact sxc_secPre_bot hJI
  · apply hTI'
    rw [← sxc_secPre_secImage hJT hTI, h]
    exact sxc_secPre_top

end

end CFSG.Quasithin
