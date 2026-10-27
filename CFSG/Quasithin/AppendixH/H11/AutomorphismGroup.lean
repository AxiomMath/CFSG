module

public import CFSG.Quasithin.Background.HModelType
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.Quasithin.H13.A5M12CentBase
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.AppendixH.H11

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModelType
  CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

section Aut

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem centralizer_eq_bot_of_std {e : V ≃* W10}
    (he : L.map (congrHom e) = (rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair).range) :
    Subgroup.centralizer (L : Set (MulAut V)) = ⊥ := by
  exact centralizer_eq_bot_of_map e (h := by rw [he]; exact centralizer_rhoC12)

@[expose] noncomputable def conjHom (hLM : IsOver L M) : ↥M →* MulAut ↥L :=
  L.normalizerMonoidHom.comp (Subgroup.inclusion hLM.2)

theorem coe_conjHom_apply (hLM : IsOver L M) (m : ↥M) (l : ↥L) :
    ((conjHom hLM m l : ↥L) : MulAut V) = (m : MulAut V) * (l : MulAut V) * (m : MulAut V)⁻¹ := by
  change ((L.normalizerMonoidHom (Subgroup.inclusion hLM.2 m) l : ↥L) : MulAut V) =
    (m : MulAut V) * (l : MulAut V) * (m : MulAut V)⁻¹
  exact Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hLM.2 m) l

theorem conjHom_injective (hLM : IsOver L M)
    (hC : Subgroup.centralizer (L : Set (MulAut V)) = ⊥) :
    Function.Injective (conjHom hLM) := by
  rw [injective_iff_map_eq_one]
  intro m hm
  have hmem : (m : MulAut V) ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : conjHom hLM m ⟨l, hl⟩ = ⟨l, hl⟩ := by rw [hm]; rfl
    have h2 : ((conjHom hLM m ⟨l, hl⟩ : ↥L) : MulAut V) =
        (m : MulAut V) * l * (m : MulAut V)⁻¹ := coe_conjHom_apply hLM m ⟨l, hl⟩
    have h3 : ((conjHom hLM m ⟨l, hl⟩ : ↥L) : MulAut V) = l := by rw [h1]
    have h4 : (m : MulAut V) * l * (m : MulAut V)⁻¹ = l := by rw [← h2, h3]
    calc l * (m : MulAut V) = ((m : MulAut V) * l * (m : MulAut V)⁻¹) * (m : MulAut V) := by
          rw [h4]
      _ = (m : MulAut V) * l := by group
  rw [hC, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem eq_or_card_eq [Finite (MulAut V)]
    (hLM : IsOver L M) (hC : Subgroup.centralizer (L : Set (MulAut V)) = ⊥)
    (θ : ↥L ≃* ↥CFSG.Blueprint.NativeSporadic.M12) :
    M = L ∨ Nat.card ↥M = 190080 := by
  have hcardL : Nat.card ↥L = 95040 := by
    rw [Nat.card_congr θ.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
  have hcardM12 : Nat.card ↥CFSG.Blueprint.NativeSporadic.M12 = 95040 :=
    CFSG.Sporadic.Mathieu.card_M12
  haveI : Finite ↥L := Subtype.finite
  haveI : Finite (MulAut ↥L) := inferInstance
  have hinj : Function.Injective (conjHom hLM) := conjHom_injective hLM hC
  have hcard_le : Nat.card ↥M ≤ Nat.card (MulAut ↥L) :=
    Nat.card_le_card_of_injective (conjHom hLM) hinj
  have hcardAut : Nat.card (MulAut ↥L) =
      Nat.card (MulAut ↥CFSG.Blueprint.NativeSporadic.M12) :=
    Nat.card_congr (MulAut.congr θ).toEquiv
  have hbound : Nat.card ↥M ≤ 190080 := by
    calc Nat.card ↥M ≤ Nat.card (MulAut ↥L) := hcard_le
      _ = Nat.card (MulAut ↥CFSG.Blueprint.NativeSporadic.M12) := hcardAut
      _ ≤ 2 * Nat.card ↥CFSG.Blueprint.NativeSporadic.M12 :=
          CFSG.Sporadic.Schreier.m12_mulAut_card
      _ = 190080 := by norm_num [hcardM12]
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hLM.1
  rw [hcardL] at hk
  haveI : Nonempty ↥M := ⟨1⟩
  have hpos : 0 < Nat.card ↥M := Nat.card_pos
  have hkpos : 1 ≤ k := by omega
  have hkub : k ≤ 2 := by omega
  interval_cases k
  · left
    have hMeqL : Nat.card ↥M = Nat.card ↥L := by omega
    exact (Subgroup.eq_of_le_of_card_ge hLM.1 (le_of_eq hMeqL)).symm
  · right
    omega

theorem even_card [Finite (MulAut V)]
    (hLM : IsOver L M) (θ : ↥L ≃* ↥CFSG.Blueprint.NativeSporadic.M12) :
    Even (Nat.card ↥M) := by
  have hcardL : Nat.card ↥L = 95040 := by
    rw [Nat.card_congr θ.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
  have hdvd : Nat.card ↥L ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hLM.1
  exact (show Even (Nat.card ↥L) by rw [hcardL]; norm_num).trans_dvd hdvd

theorem nonempty_mulEquiv_mulAut_of_ne [Finite (MulAut V)]
    (hLM : IsOver L M) (hC : Subgroup.centralizer (L : Set (MulAut V)) = ⊥)
    (θ : ↥L ≃* ↥CFSG.Blueprint.NativeSporadic.M12) (hne : M ≠ L) :
    Nonempty (↥M ≃* MulAut ↥CFSG.Blueprint.NativeSporadic.M12) := by
  have hcardM : Nat.card ↥M = 190080 := by
    rcases eq_or_card_eq hLM hC θ with h | h
    · exact absurd h hne
    · exact h
  let f : ↥M →* MulAut ↥CFSG.Blueprint.NativeSporadic.M12 :=
    (MulAut.congr θ).toMonoidHom.comp (conjHom hLM)
  have hinj : Function.Injective f := by
    intro a b hab
    exact conjHom_injective hLM hC ((MulAut.congr θ).injective hab)
  haveI : Finite (MulAut ↥CFSG.Blueprint.NativeSporadic.M12) := by
    haveI : Finite ↥CFSG.Blueprint.NativeSporadic.M12 :=
      Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num)
    infer_instance
  have hle : Nat.card (MulAut ↥CFSG.Blueprint.NativeSporadic.M12) ≤ Nat.card ↥M := by
    rw [hcardM]
    calc Nat.card (MulAut ↥CFSG.Blueprint.NativeSporadic.M12)
        ≤ 2 * Nat.card ↥CFSG.Blueprint.NativeSporadic.M12 :=
          CFSG.Sporadic.Schreier.m12_mulAut_card
      _ = 190080 := by norm_num [CFSG.Sporadic.Mathieu.card_M12]
  exact ⟨MulEquiv.ofBijective f (hinj.bijective_of_nat_card_le hle)⟩

end Aut

end CFSG.Quasithin.AppendixH.H11
