
module

public import CFSG.Quasithin.Background.A3Structure320

public section

namespace CFSG.Quasithin

namespace A318

open CFSG.Open CFSG.SectionRank CFSG.Quasithin.A320
open scoped commutatorElement

theorem pRank_le_pRank_map_of_coprime {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    {p : ℕ} [hp : Fact p.Prime] (f : G →* G') (hf : Nat.Coprime p (Nat.card f.ker))
    (H : Subgroup G) : CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (H.map f) := by
  obtain ⟨E, hEH, hE, hcard⟩ := exists_pRank hp.out.one_lt H
  have hdisj : Disjoint E f.ker :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hcard]; exact hf.pow_left _)
  have hinj : Function.Injective (f.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : G) ∈ f.ker := hx
    exact Subtype.ext (Subgroup.disjoint_def.1 hdisj x.2 h1)
  have := hE.1
  refine le_pRank_of_injective hp.out.one_lt (A := ↥E) (fun a b => mul_comm' a b)
    (fun a => Subtype.ext (hE.2 a a.2)) hcard (f.comp E.subtype) hinj ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨x, hEH x.2, rfl⟩

theorem mem_cComp_quotient {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (hL : L ∈ cComp (⊤ : Subgroup H)) :
    L.map (QuotientGroup.mk' (CFSG.pCore 2 H)) ∈
      cComp (⊤ : Subgroup (H ⧸ CFSG.pCore 2 H)) :=
  (cComp_quotient_bijOn (CFSG.pCore 2 H) (isSolvable_pCore_two H)).mapsTo hL

theorem normal_of_pRank_gt_one {H : Type} [Group H] [Finite H] (hH : SQTKGroup H)
    (h38 : A38Part3 (H ⧸ CFSG.pCore 2 H)) {L : Subgroup H}
    (hL : L ∈ cComp (⊤ : Subgroup H)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : 1 < CFSG.Open.pRank p L) : L.Normal := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGH : SQTKHyp (H ⧸ CFSG.pCore 2 H) := SQTKHyp.of_sqtkGroup H hH
  let π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hLbar := mem_cComp_quotient hL
  have hrank' : 2 ≤ CFSG.Open.pRank p (L.map π) :=
    (pRank_le_pRank_map hp2 π hker L).trans' hrank
  have hLbarN : (L.map π).Normal := by
    rcases (h38 _ hLbar).1 with h | ⟨-, t, -, hcomm, hinter, -⟩
    · exact h
    · exfalso
      obtain ⟨E, hEL, hEel, hEcard⟩ := exists_pRank hp.one_lt (L.map π)
      have hE'el : IsElemAbelian p (E.map (MulAut.conj t).toMonoidHom) :=
        isElemAbelian_map hEel _
      have hE'card : Nat.card (E.map (MulAut.conj t).toMonoidHom) =
          p ^ CFSG.Open.pRank p (L.map π) := by
        rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, hEcard]
      have hmain := pRank_add_le (⊥ : Subgroup (H ⧸ CFSG.pCore 2 H))
        (by simpa [Nat.dvd_one] using hp.ne_one) hEel hE'el
        (fun x hx e he => by
          have : ⁅x, e⁆ ∈ ⁅L.map π, (L.map π).map (MulAut.conj t).toMonoidHom⁆ :=
            Subgroup.commutator_mem_commutator (hEL hx) (Subgroup.map_mono hEL he)
          rwa [hcomm] at this)
        (fun x hx e he hxe => by
          have hxe1 : x * e = 1 := Subgroup.mem_bot.1 hxe
          have hxL : x ∈ L.map π ⊓ (L.map π).map (MulAut.conj t).toMonoidHom := by
            refine ⟨hEL hx, ?_⟩
            have : x = e⁻¹ := eq_inv_of_mul_eq_one_left hxe1
            rw [this]
            exact Subgroup.inv_mem _ (Subgroup.map_mono hEL he)
          rw [hinter, Subgroup.mem_bot] at hxL
          rw [hxL, one_mul] at hxe1
          exact ⟨hxL, hxe1⟩)
        (a := CFSG.Open.pRank p (L.map π)) (b := CFSG.Open.pRank p (L.map π)) hEcard hE'card
      have := hGH.pRank_le ⊤ hp hp2
      omega
  have hLN₂ : (L ⊔ CFSG.pCore 2 H).Normal := by
    have := Subgroup.Normal.comap hLbarN π
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
  obtain ⟨-, hperf⟩ := cComp_commutator_perfectCore hL (le_top) (isSolvable_pCore_two H)
    Subgroup.le_normalizer_of_normal
  refine ⟨fun n hn g => ?_⟩
  have hg : g ∈ Subgroup.normalizer ((L ⊔ CFSG.pCore 2 H : Subgroup H) : Set H) :=
    Subgroup.le_normalizer_of_normal (K := ⊤) (Subgroup.mem_top g)
  have hg' := normalizer_le_normalizer_perfectCore _ hg
  rw [hperf] at hg'
  exact (Subgroup.mem_normalizer_iff.1 hg' n).1 hn

end A318

end CFSG.Quasithin
