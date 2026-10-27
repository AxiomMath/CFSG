module

public import CFSG.Quasithin.Background.GoldschmidtShultI85
public import CFSG.RankThree.PartOne.KE8F.HyperGen

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.Open CFSG.Quasithin.Shult CFSG.QuasithinUnique
open scoped commutatorElement

section Aux

variable {H : Type} [Group H]

theorem map_subtype_top_eq (K : Subgroup H) : (⊤ : Subgroup ↥K).map K.subtype = K := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commutator_eq_top_of_perfect {K : Subgroup H} (hKp : ⁅K, K⁆ = K) :
    commutator ↥K = ⊤ := by
  have h1 : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [commutator, Subgroup.map_commutator, map_subtype_top_eq]
  apply Subgroup.map_injective K.subtype_injective
  rw [h1, hKp, map_subtype_top_eq]

theorem hom_eq_one_of_perfect {K : Subgroup H} (hKp : ⁅K, K⁆ = K) {S : Type*} [Group S]
    [Group.IsSolvable S] (φ : ↥K →* S) (k : ↥K) : φ k = 1 := by
  have hder : ∀ n : ℕ, derivedSeries ↥K n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [derivedSeries_succ, ih]
      exact commutator_eq_top_of_perfect hKp
  obtain ⟨n, hn⟩ := (Group.IsSolvable.solvable (G := S))
  have hmap := map_derivedSeries_le_derivedSeries φ n
  rw [hder n, hn] at hmap
  have : φ k ∈ (⊥ : Subgroup S) := hmap ⟨k, Subgroup.mem_top k, rfl⟩
  simpa using this

theorem oddCoreIn_conj_mem [Finite H] {L : Subgroup H} [L.Normal] (g : H) {o : H}
    (ho : o ∈ oddCoreIn L) : g * o * g⁻¹ ∈ oddCoreIn L := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ho
  set σ : MulAut ↥L := MulAut.conjNormal g with hσ
  have hmem : σ x ∈ fusionOddCore ↥L := by
    have h1 : (fusionOddCore ↥L).map σ.toMonoidHom ≤ fusionOddCore ↥L := by
      apply le_sSup
      refine ⟨(fusionOddCore_normal ↥L).map _ σ.surjective, ?_⟩
      rw [Subgroup.card_map_of_injective (f := σ.toMonoidHom) (fun a b h => σ.injective h)]
      exact CFSG.ComponentClassification.OddCore.odd_card ↥L
    exact h1 ⟨x, hx, rfl⟩
  exact ⟨σ x, hmem, by simp [hσ, MulAut.conjNormal_apply]⟩

theorem odd_card_oddCoreIn' [Finite H] (L : Subgroup H) : Odd (Nat.card (oddCoreIn L)) := by
  rw [oddCoreIn, Subgroup.card_map_of_injective L.subtype_injective]
  exact CFSG.ComponentClassification.OddCore.odd_card ↥L

theorem odd_case [Finite H] {X Uh R : Subgroup H} (hX : X ≠ ⊤)
    (hUn : ∀ x ∈ X, ∀ u ∈ Uh, x * u * x⁻¹ ∈ Uh) (hU2 : ∀ a ∈ Uh, a ^ 2 = 1)
    (hNX : Subgroup.normalizer (Uh : Set H) ≤ X)
    (hR2 : ∃ a ∈ R, ∃ b ∈ R, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b)
    (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRsq : ∀ a ∈ R, a ^ 2 = 1)
    (hRC : ∀ r ∈ R, r ≠ 1 → ∀ g : H, g * r = r * g → g ∈ X)
    (hL : Subgroup.normalClosure (Uh : Set H) =
      oddCoreIn (Subgroup.normalClosure (Uh : Set H)) ⊔ Uh) : False := by
  set L : Subgroup H := Subgroup.normalClosure (Uh : Set H) with hLdef
  set O : Subgroup H := oddCoreIn L with hOdef
  have hUL : Uh ≤ L := Subgroup.le_normalClosure
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreIn' L
  have hOnorm : ∀ g : H, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g o ho => oddCoreIn_conj_mem g ho
  have hnormO : ∀ g : H, g ∈ Subgroup.normalizer (O : Set H) := fun g => by
    rw [Subgroup.mem_normalizer_iff]
    intro o
    refine ⟨fun ho => hOnorm g o ho, fun ho => ?_⟩
    have := hOnorm g⁻¹ _ ho
    simpa [mul_assoc] using this
  have hOX : O ≤ X := by
    have hel : IsElementaryAbelian 2 ↥R :=
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hRab a.1 a.2 b.1 b.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one
          (fun x => Subtype.ext (hRsq x.1 x.2)) }
    obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := hR2
    have : Nontrivial ↥R := ⟨⟨⟨a, ha⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
    have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := 2) (A := R)
      (V := O) (fun g _ => hnormO g)
      (fun h => (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 h))
    refine hgen.trans (iSup_le fun B => iSup_le fun hB => ?_)
    have hB1 : B ≠ ⊥ := by
      intro hbot
      have hc := Subgroup.card_mul_index B
      rw [hB, hbot, Subgroup.card_bot] at hc
      exact hab (eq_of_card_two (by simpa using hc.symm) ha hb ha1 hb1)
    obtain ⟨⟨r, hrB⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
    intro g hg
    have hr1' : (r : H) ≠ 1 := fun h => hr1 (Subtype.ext (Subtype.ext h))
    have hrB' : (r : H) ∈ B.map R.subtype := ⟨r, hrB, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 hg.2 (r : H) hrB'
    exact hRC r r.2 hr1' g hcomm.symm
  have hOc : ∀ o ∈ O, ∀ u ∈ Uh, o * u = u * o := by
    intro o ho u hu
    have hcU : o * u * o⁻¹ * u⁻¹ ∈ Uh := Uh.mul_mem (hUn o (hOX ho) u hu) (Uh.inv_mem hu)
    have hcO : o * u * o⁻¹ * u⁻¹ ∈ O := by
      have := O.mul_mem ho (hOnorm u o⁻¹ (O.inv_mem ho))
      simpa [mul_assoc] using this
    have h1 : o * u * o⁻¹ * u⁻¹ = 1 :=
      eq_one_of_mem_odd (Z := O) hOodd hcO ⟨1, by simpa using hU2 _ hcU⟩
    have h2 : o * u * o⁻¹ = u := mul_inv_eq_one.1 h1
    calc o * u = (o * u * o⁻¹) * o := by group
      _ = u * o := by rw [h2]
  have hUN : ∀ g : H, ∀ u ∈ Uh, g * u * g⁻¹ ∈ Uh := by
    intro g u hu
    have hv : g * u * g⁻¹ ∈ L := Subgroup.normalClosure_normal.conj_mem u (hUL hu) g
    have hvsq : (g * u * g⁻¹) ^ 2 = 1 := by
      have := hU2 u hu
      calc (g * u * g⁻¹) ^ 2 = g * (u * u) * g⁻¹ := by rw [sq]; group
        _ = 1 := by rw [← sq, this]; group
    have hUle : Uh ≤ Subgroup.normalizer (O : Set H) := fun x _ => hnormO x
    have hmem : g * u * g⁻¹ ∈ ((Uh ⊔ O : Subgroup H) : Set H) := by
      rw [sup_comm, ← hL]
      exact hv
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Uh O hUle] at hmem
    obtain ⟨u1, hu1, o1, ho1, hv1⟩ := Set.mem_mul.1 hmem
    have hc : Commute u1 o1 := (hOc o1 ho1 u1 hu1).symm
    have ho12 : o1 ^ 2 = 1 := by
      have h2 := hvsq
      rw [← hv1, hc.mul_pow, hU2 u1 hu1, one_mul] at h2
      exact h2
    have ho11 : o1 = 1 := eq_one_of_mem_odd (Z := O) hOodd ho1 ⟨1, by simpa using ho12⟩
    rw [← hv1, ho11, mul_one]
    exact hu1
  apply hX
  rw [eq_top_iff]
  intro g _
  apply hNX
  rw [Subgroup.mem_normalizer_iff]
  intro u
  exact ⟨fun hu => hUN g u hu, fun hu => by simpa [mul_assoc] using hUN g⁻¹ _ hu⟩

end Aux

end CFSG.Quasithin.H13.F431.Un
