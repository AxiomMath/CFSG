module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup

theorem center_quot_eq_bot {I : Type} [Group I] (hQ : IsQuasisimple I) :
    Subgroup.center (I ⧸ Subgroup.center I) = ⊥ := by
  obtain ⟨-, hsimple, a, b, hab⟩ := hQ
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (I ⧸ Subgroup.center I)) with h | h
  · exact h
  · exfalso
    have hb : b ∈ Subgroup.center (I ⧸ Subgroup.center I) := by
      rw [h]
      exact Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem exists_invariant_two_subgroup_of_central {I S : Type*} [Group I] [Finite I] [Group S]
    (π : I →* S) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center I)
    (f : MulAut I) (fb : MulAut S) (hf : ∀ x, π (f x) = fb (π x))
    (V' : Subgroup S) (hV'1 : V' ≠ ⊥) (hV'2 : IsPGroup 2 V') (hinv : ∀ s ∈ V', fb s ∈ V') :
    ∃ T : Subgroup I, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T.map f.toMonoidHom = T := by
  haveI : Finite S := Finite.of_surjective π hπ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup I := V'.comap π
  have hfK : K.map f.toMonoidHom ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    show π (f x) ∈ V'
    rw [hf]
    exact hinv _ hx
  have hK : K.map f.toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge hfK (by rw [Subgroup.card_map_of_injective f.injective])
  let φ : K →* V' := (π.comp K.subtype).codRestrict V' fun x => x.2
  have hφsurj : Function.Surjective φ := by
    rintro ⟨s, hs⟩
    obtain ⟨x, rfl⟩ := hπ s
    exact ⟨⟨x, hs⟩, Subtype.ext rfl⟩
  have hφker : φ.ker ≤ Subgroup.center K := by
    intro x hx
    have h0 : φ x = 1 := (MonoidHom.mem_ker).1 hx
    have h1 : π (x : I) = 1 := congrArg Subtype.val h0
    have h2 : (x : I) ∈ Subgroup.center I := hker ((MonoidHom.mem_ker).2 h1)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_center_iff.mp h2) y)
  haveI : Group.IsNilpotent V' := hV'2.isNilpotent
  haveI : Group.IsNilpotent K := _root_.isNilpotent_of_ker_le_center φ hφker
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  have hV'card : 2 ∣ Nat.card V' := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hV'2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hV'1 (Subgroup.card_eq_one.1 (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  have hKcard : 2 ∣ Nat.card K := hV'card.trans (Subgroup.card_dvd_of_surjective hφsurj)
  refine ⟨(P : Subgroup K).map K.subtype, ?_, ?_, ?_⟩
  · intro h
    have hP : (P : Subgroup K) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 h
    have hc : Nat.card (P : Subgroup K) = 1 := by
      rw [hP]
      exact Subgroup.card_bot
    rw [Sylow.card_eq_multiplicity] at hc
    have hKne : Nat.card K ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card K).factorization 2 :=
      (Nat.prime_two.dvd_iff_one_le_factorization hKne).1 hKcard
    have h2 : 2 ^ 1 ≤ 2 ^ (Nat.card K).factorization 2 := Nat.pow_le_pow_right (by norm_num) h1
    omega
  · exact P.isPGroup'.map K.subtype
  · have hchar : (P : Subgroup K).Characteristic := Sylow.characteristic_of_normal P inferInstance
    let fK : K ≃* K := (f.subgroupMap K).trans (MulEquiv.subgroupCongr hK)
    have h1 : (P : Subgroup K).map fK.toMonoidHom = P :=
      Subgroup.characteristic_iff_map_eq.mp hchar fK
    have hcomm : f.toMonoidHom.comp K.subtype = K.subtype.comp fK.toMonoidHom := by
      ext x
      rfl
    calc ((P : Subgroup K).map K.subtype).map f.toMonoidHom
        = (P : Subgroup K).map (f.toMonoidHom.comp K.subtype) := by rw [Subgroup.map_map]
      _ = (P : Subgroup K).map (K.subtype.comp fK.toMonoidHom) := by rw [hcomm]
      _ = ((P : Subgroup K).map fK.toMonoidHom).map K.subtype := by rw [Subgroup.map_map]
      _ = (P : Subgroup K).map K.subtype := by rw [h1]

end CFSG.RankThree.PartTwo.Sec13.F135Last
