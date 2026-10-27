module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25PerfInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2b

public section

namespace CFSG.Quasithin.H13.LiePerf

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.Assembly.LowTwoRank

@[expose] def BenderLevi {S : Type} [Group S] (P : Subgroup S) : Prop :=
  perfectCore P = ⊥ ∨ ∃ (B : Type) (_ : Group B) (_ : IsSimpleGroup B)
    (g : ↥(perfectCore P) →* B), Function.Surjective g ∧ Group.IsSolvable g.ker ∧
      ∃ m : ℕ, E2.IsBenderOf m B

@[expose] def HasBenderLevi (S : Type) [Group S] : Prop :=
  ∀ U : Subgroup S, IsSylowTwoOf U ⊤ →
    ∃ P : Fin 2 → Subgroup S, ResidualOvergroupsAt S U P ∧ ∀ j, BenderLevi (P j)

section Transport

variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B]

theorem benderLevi_map (f : A →* B) {P : Subgroup A}
    (hf : Set.InjOn f (perfectCore P : Set A)) (h : BenderLevi P) : BenderLevi (P.map f) := by
  rcases h with h | ⟨T, _, _, g, hg, hk, m, hm⟩
  · left
    rw [← map_perfectCore, h, Subgroup.map_bot]
  · right
    have hρ : Function.Injective (f.comp (perfectCore P).subtype) := fun x y hxy =>
      Subtype.ext (hf x.2 y.2 hxy)
    have hr : (f.comp (perfectCore P).subtype).range = perfectCore (P.map f) := by
      rw [← map_perfectCore, MonoidHom.range_comp, Subgroup.range_subtype]
    let e : ↥(perfectCore P) ≃* ↥(perfectCore (P.map f)) :=
      (MonoidHom.ofInjective hρ).trans (MulEquiv.subgroupCongr hr)
    refine ⟨T, inferInstance, inferInstance, g.comp e.symm.toMonoidHom,
      hg.comp e.symm.surjective, ?_, m, hm⟩
    let ι : ↥(g.comp e.symm.toMonoidHom).ker →* ↥g.ker :=
      (e.symm.toMonoidHom.comp (Subgroup.subtype _)).codRestrict g.ker fun x => x.2
    have hι : Function.Injective ι := fun x y hxy =>
      Subtype.ext (e.symm.injective (congrArg Subtype.val hxy))
    exact Group.isSolvable_of_isSolvable_injective hι

theorem benderLevi_map_equiv (e : A ≃* B) {P : Subgroup A} (h : BenderLevi P) :
    BenderLevi (P.map e.toMonoidHom) :=
  benderLevi_map e.toMonoidHom (fun _ _ _ _ hxy => e.injective hxy) h

end Transport

theorem isBenderOf_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 2 ≤ m) :
    E2.IsBenderOf m (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have h2m : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨hm, Or.inl ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance,
    inferInstance, hF, ⟨CFSG.QuasithinUnique.Vol2Native.A312L.sl2EquivStatedProj⟩⟩⟩
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega

theorem benderLevi_of_leviData {S : Type} [Group S] [Finite S] {P : Subgroup S}
    (h : CFSG.QuasithinUnique.Vol2Native.A312L.LeviData P) : BenderLevi P := by
  rcases h with h | ⟨K, _, _, _, n, hK, hn, g, hg, hk⟩
  · exact Or.inl h
  · have hK4 : ∃ s : Finset K, s.card = 4 := by
      refine CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four ?_
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple hK4
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Or.inr ⟨_, inferInstance, inferInstance, g, hg, by
      have := hk.isNilpotent
      infer_instance, n, isBenderOf_sl2 hK hn⟩

theorem dInf_eq_perfectCore' {S : Type} [Group S] [Finite S] (M : Subgroup S) :
    dInf M = perfectCore M :=
  le_antisymm
    (le_perfectCore_of_perfect (dInf_le M) (Subgroup.isPerfect_iff.mp (dInf_isPerfect M)))
    (le_dInf_of_perfect (Subgroup.isPerfect_iff.mpr (perfectCore_perfect M)) (perfectCore_le M))

theorem liePerf_of_residual {S : Type} [Group S] [Finite S] {U : Subgroup S}
    {P : Fin 2 → Subgroup S} (hP : ResidualOvergroupsAt S U P) (hL : ∀ j, BenderLevi (P j))
    {X : Subgroup S} (hUX : U ≤ X) (hX : X ≠ ⊤) {Y : Subgroup S} (hYX : Y ≤ X)
    (hsub : (Y.subgroupOf X).IsSubnormal) (hperf : ⁅Y, Y⁆ = Y) (hY : Y ≠ ⊥) :
    ∃ (B : Type) (_ : Group B) (f : ↥Y →* B), Function.Surjective f ∧
      ∃ m : ℕ, E2.IsBenderOf m B := by
  have hYns : ¬ Group.IsSolvable ↥Y := fun hs => by
    rw [isSolvable_iff_perfectCore_eq_bot, perfectCore_eq_self_of_perfect hperf] at hs
    exact hY hs
  have hXns : ¬ Group.IsSolvable ↥X := fun hs =>
    hYns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hYX))
  obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 X hUX hX hXns
  have hD : perfectCore X = perfectCore (P j) := by
    rw [← dInf_eq_perfectCore', ← dInf_eq_perfectCore', hd]
  have hYD : Y ≤ perfectCore (P j) := hD ▸ le_perfectCore_of_perfect hYX hperf
  rcases hL j with h0 | ⟨B, _, _, g, hg, hk, m, hm⟩
  · exact absurd (le_bot_iff.1 (h0 ▸ hYD)) hY
  · have hDX : perfectCore (P j) ≤ X := hD ▸ perfectCore_le X
    have hsubD : (Y.subgroupOf (perfectCore (P j))).IsSubnormal := by
      have h1 := hsub.comap (Subgroup.inclusion hDX)
      have e : (Y.subgroupOf X).comap (Subgroup.inclusion hDX) =
          Y.subgroupOf (perfectCore (P j)) := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      rwa [e] at h1
    rcases (hsubD.map hg).eq_bot_or_top_of_isSimpleGroup inferInstance with hbot | htop
    · exfalso
      apply hYns
      have hle : Y.subgroupOf (perfectCore (P j)) ≤ g.ker := (Subgroup.map_eq_bot_iff _).1 hbot
      let ι : ↥Y →* ↥g.ker :=
        (Subgroup.inclusion hYD).codRestrict g.ker fun y => hle (show _ ∈ Y.subgroupOf _ from y.2)
      exact Group.isSolvable_of_isSolvable_injective (f := ι) fun x y hxy =>
        Subgroup.inclusion_injective hYD (congrArg Subtype.val hxy)
    · refine ⟨B, inferInstance, g.comp (Subgroup.inclusion hYD), fun b => ?_, m, hm⟩
      have hb : b ∈ (Y.subgroupOf (perfectCore (P j))).map g := htop ▸ Subgroup.mem_top b
      obtain ⟨d, hd, rfl⟩ := hb
      exact ⟨⟨d, hd⟩, rfl⟩

theorem liePerfOvergroupFactRank2_of
    (h : ∀ (S : Type) [Group S] [Finite S],
      (∃ k : ℕ, 2 ≤ k ∧ (IsPSL 3 2 k S ∨ IsPSp4 2 k S ∨ IsG2 2 k S ∨ Is3D4 2 k S ∨ Is2F4 k S)) →
        HasBenderLevi S) : LiePerfOvergroupFactRank2 := by
  intro S _ _ _ hS P hP X hPX hX Y hYX hsub hperf hY
  obtain ⟨Q, hres, hL⟩ := h S hS P hP
  exact liePerf_of_residual hres hL hPX hX hYX hsub hperf hY

end CFSG.Quasithin.H13.LiePerf
