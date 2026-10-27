module

public import CFSG.Mathlib.GroupTheory.CoprimeInvariantSylowTwo
public import CFSG.Open.LocalVocabulary

@[expose] public section

namespace CFSG.LiftNormalizing

theorem exists_lift_normalizer {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {E T : Subgroup (H ⧸ N)} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set (H ⧸ N))) :
    ∃ E' T' : Subgroup H, CFSG.Open.IsElemAbelian 3 E' ∧ Nat.card E' = Nat.card E ∧
      T' ≠ ⊥ ∧ IsPGroup 2 T' ∧ E' ≤ Subgroup.normalizer (T' : Set H) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  let preE : Subgroup H := E.comap π
  let P : Sylow 3 preE := default
  let πE : preE →* E := (π.comp preE.subtype).codRestrict E fun x => x.2
  have hπE : Function.Surjective πE := by
    intro e
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective N (e : H ⧸ N)
    refine ⟨⟨h, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, hh]
      exact e.2
    · exact Subtype.ext hh
  let Q : Sylow 3 E := P.mapSurjective hπE
  have hE3 : IsPGroup 3 E := by
    rw [isPGroup_iff_exists_pow_pow_eq_one]
    exact ⟨1, fun x => Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hQtop : (Q : Subgroup E) = ⊤ :=
    (Q.is_maximal' (hE3.of_equiv (Subgroup.topEquiv (G := ↥E)).symm) le_top).symm
  have htopE : (P : Subgroup preE).map πE = ⊤ := by
    rw [← Sylow.coe_mapSurjective (f := πE) hπE]
    exact hQtop
  let E' : Subgroup H := (P : Subgroup preE).map preE.subtype
  have hE'3 : IsPGroup 3 E' := P.isPGroup'.map preE.subtype
  have hEq : E'.map π = E := by
    calc
      E'.map π = ((P : Subgroup preE).map preE.subtype).map π := rfl
      _ = (P : Subgroup preE).map (π.comp preE.subtype) :=
        Subgroup.map_map (K := (P : Subgroup preE)) π preE.subtype
      _ = (P : Subgroup preE).map (E.subtype.comp πE) := by
        congr 1
      _ = ((P : Subgroup preE).map πE).map E.subtype :=
        (Subgroup.map_map (K := (P : Subgroup preE)) E.subtype πE).symm
      _ = (⊤ : Subgroup E).map E.subtype := by rw [htopE]
      _ = E := by rw [Subgroup.map_top, Subgroup.range_subtype]
  have hdisj : Disjoint E' N :=
    IsPGroup.disjoint_of_coprime hE'3 (IsPGroup.card (G := ↥N))
      ((Nat.prime_three.coprime_iff_not_dvd).mpr hN)
  have hEN : E' ⊓ N = ⊥ := hdisj.eq_bot
  have hinj : Function.Injective (π.comp E'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : H) ∈ N := (QuotientGroup.eq_one_iff (x : H)).mp hx
    have hxinf : (x : H) ∈ E' ⊓ N := Subgroup.mem_inf.mpr ⟨x.2, hxN⟩
    rw [hEN, Subgroup.mem_bot] at hxinf
    exact Subtype.ext hxinf
  have hprele : E' ≤ preE := Subgroup.map_subtype_le _
  let f : E' →* E := (π.comp E'.subtype).codRestrict E fun x =>
    Subgroup.mem_comap.mp (hprele x.2)
  have hf_inj : Function.Injective f := fun _ _ hab => hinj (congrArg Subtype.val hab)
  have hf_surj : Function.Surjective f := by
    intro e
    have he : (e : H ⧸ N) ∈ E'.map π := by
      rw [hEq]
      exact e.2
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp he
    exact ⟨⟨x, hx⟩, Subtype.ext hxeq⟩
  have hcardE' : Nat.card E' = Nat.card E :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  have hE'ea : CFSG.Open.IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply hinj
      have ha : π (a : H) ∈ E := Subgroup.mem_comap.mp (hprele a.2)
      have hb : π (b : H) ∈ E := Subgroup.mem_comap.mp (hprele b.2)
      have : IsMulCommutative E := hE.1
      have hc : (⟨π (a : H), ha⟩ : E) * ⟨π (b : H), hb⟩ =
          ⟨π (b : H), hb⟩ * ⟨π (a : H), ha⟩ := mul_comm' _ _
      simpa [map_mul] using congrArg Subtype.val hc
    · let x' : E' := ⟨x, hx⟩
      have hx' : x' ^ 3 = 1 := by
        apply hinj
        have hxE : π (x : H) ∈ E := Subgroup.mem_comap.mp (hprele hx)
        simpa [x', map_pow] using hE.2 (π (x : H)) hxE
      simpa [x'] using congrArg Subtype.val hx'
  let Y : Subgroup H := T.comap π
  have hNY : N ≤ Y := by
    intro n hn
    rw [Subgroup.mem_comap]
    show π n ∈ T
    have hn1 : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [hn1]
    exact T.one_mem
  let g : Y →* T := (π.comp Y.subtype).codRestrict T fun y =>
    Subgroup.mem_comap.mp y.2
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective N (t : H ⧸ N)
    refine ⟨⟨h, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap]
      show π h ∈ T
      rw [hh]
      exact t.2
    · exact Subtype.ext hh
  have hker : g.ker = N.subgroupOf Y := by
    dsimp only [g]
    rw [MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker π Y.subtype,
      Subgroup.comap_subtype, QuotientGroup.ker_mk']
  have hcardY : Nat.card Y = Nat.card N * Nat.card T := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := g) hg
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv] at h
    exact h.symm
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    rw [hcardY]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h3N | h3T
    · exact hN h3N
    · obtain ⟨k, hk⟩ := hT2.exists_card_eq
      rw [hk] at h3T
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h3T) (by norm_num)
  have hY2 : 2 ∣ Nat.card Y := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    have hk0 : k ≠ 0 := by
      intro hzero
      have hcardT : Nat.card T = 1 := by rw [hk, hzero, pow_zero]
      exact hT (Subgroup.eq_bot_of_card_eq (H := T) hcardT)
    rw [hcardY, hk]
    exact dvd_mul_of_dvd_right (dvd_pow_self 2 hk0) _
  have hE'norm : E' ≤ Subgroup.normalizer (Y : Set H) := by
    rw [← Subgroup.comap_normalizer_eq_of_surjective (f := π) T
      (QuotientGroup.mk'_surjective N)]
    intro x hx
    exact hET (Subgroup.mem_comap.mp (hprele hx))
  obtain ⟨T', -, hT'2, hT'ne, hT'norm⟩ :=
    CFSG.CoprimeInvariantSylowTwo.exists_isPGroup_ne_bot_normalizer
      (G := H) (Y := Y) (E := E') hE'norm hE'3 hY3 hY2
  exact ⟨E', T', hE'ea, hcardE', hT'ne, hT'2, hT'norm⟩

end CFSG.LiftNormalizing

end
