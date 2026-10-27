module

public import CFSG.RankThree.PartTwo.KFacts.ONanKS152Lift
public import CFSG.RankThree.PartTwo.KFacts.ONanKS152Trace
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS152

open CFSG.SectionRank.Ccomm

theorem eq_one_of_solvable_range {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (f : G →* H) (hf : Group.IsSolvable f.range) : f = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable f.range hf
  ext x
  exact congrArg Subtype.val (Subsingleton.elim (⟨f x, x, rfl⟩ : f.range) 1)

theorem eq_one_of_cover {G H : Type*} [Group G] [Group H] [Group.IsPerfect G] (f : G →* H)
    (T : Subgroup G) (hT : Group.IsSolvable T) (hG : ∀ x : G, ∃ n ∈ f.ker, ∃ t ∈ T, x = n * t) :
    f = 1 := by
  let g : T →* f.range := (f.comp T.subtype).codRestrict f.range (fun t => ⟨t, rfl⟩)
  have hg : Function.Surjective g := by
    rintro ⟨_, x, rfl⟩
    obtain ⟨n, hn, t, ht, rfl⟩ := hG x
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    change f t = f (n * t)
    rw [map_mul, MonoidHom.mem_ker.mp hn, one_mul]
  exact eq_one_of_solvable_range f (Group.isSolvable_of_surjective hg)

theorem eq_one_of_comm {G A : Type*} [Group G] [CommGroup A] [Group.IsPerfect G]
    (f : G →* A) : f = 1 :=
  eq_one_of_solvable_range f inferInstance

theorem false_of_nine_in_special {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : k ≤ 2) {E : Type*}
    [Group E] (hE : Nat.card E = 9) (hE3 : ∀ x : E, x ^ 3 = 1) (f : E →* GL (Fin k) (ZMod p))
    (hf : Function.Injective f)
    (hdet : ∀ x : E, ((f x : GL (Fin k) (ZMod p)) : Matrix (Fin k) (Fin k) (ZMod p)).det = 1) :
    False := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE]; norm_num)
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · obtain ⟨x, hx⟩ := exists_ne (1 : E)
    exact hx (hf (Subsingleton.elim (f x) (f 1)))
  · obtain ⟨x, hx⟩ := exists_ne (1 : E)
    refine hx (hf ?_)
    rw [map_one]
    apply Units.ext
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.det_fin_one] using hdet x
  · by_cases hp3 : p = 3
    · subst hp3
      have h1 : Nat.card E ∣ Nat.card (GL (Fin 2) (ZMod 3)) := Subgroup.card_dvd_of_injective f hf
      rw [card_GL_zmod, hE] at h1
      simp [Fin.prod_univ_two] at h1
    · refine KS152.false_of_nine_in_sl_two ?_ hE hE3 f hf hdet
      intro h
      have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h')

theorem action_trivial
    {p : ℕ} [hp : Fact p.Prime]
    {V : Type} [Group V] [Finite V] (hV : IsPGroup p V) (hW : Nat.card (V ⧸ frattini V) ≤ p ^ 2)
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L] (θ : Subgroup L) [θ.Normal]
    (hθs : Group.IsSolvable θ) (hθ3 : ¬ 3 ∣ Nat.card θ)
    (he : Nonempty (L ⧸ θ ≃* CFSG.Blueprint.NativeSporadic.J2)) (ρ : L →* MulAut V) :
    ρ = 1 := by
  have h3p : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hchar, hcomm, hpow⟩ := frattini_quotient_elementary hV
  have := hchar
  obtain ⟨k, hk⟩ := (hV.to_quotient (frattini V)).exists_card_eq
  have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 (hk ▸ hW)
  obtain ⟨ε⟩ := nonempty_mulEquiv_of_elementary hcomm hpow hk
  set φ : L →* GL (Fin k) (ZMod p) :=
    (elemAutEquivGL ε).toMonoidHom.comp ((autQuotient (frattini V)).comp ρ) with hφ
  have hsimple : IsSimpleGroup (L ⧸ θ) := by
    obtain ⟨e⟩ := he
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    exact MulEquiv.isSimpleGroup e
  have hdich : φ.ker ≤ θ ∨ ∀ x : L, ∃ n ∈ φ.ker, ∃ t ∈ θ, x = n * t := by
    have hN : (φ.ker.map (QuotientGroup.mk' θ)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective θ)
    rcases hsimple.eq_bot_or_eq_top_of_normal (φ.ker.map (QuotientGroup.mk' θ)) with h | h
    · left
      intro n hn
      have : QuotientGroup.mk' θ n ∈ (⊥ : Subgroup (L ⧸ θ)) := h ▸ Subgroup.mem_map_of_mem _ hn
      exact (QuotientGroup.eq_one_iff n).mp (Subgroup.mem_bot.mp this)
    · right
      intro x
      have hx : QuotientGroup.mk' θ x ∈ φ.ker.map (QuotientGroup.mk' θ) := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      exact ⟨n, hn, n⁻¹ * x, QuotientGroup.eq.mp hnx, by group⟩
  rcases hdich with hB | hA
  ·
    exfalso
    obtain ⟨E, hE9, hEθ, hE3⟩ := exists_lift_nine θ hθ3 he
    have hinj : Function.Injective (φ.comp E.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hxker : (x : L) ∈ φ.ker := hx
      have h2 : (x : L) = 1 := Subgroup.mem_bot.mp (hEθ.le_bot ⟨x.2, hB hxker⟩)
      exact Subgroup.mem_bot.mpr (Subtype.ext h2)
    have hdet1 : ∀ x : L,
        ((φ x : GL (Fin k) (ZMod p)) : Matrix (Fin k) (Fin k) (ZMod p)).det = 1 := by
      intro x
      have h := congrArg (fun f : L →* (ZMod p)ˣ => ((f x : (ZMod p)ˣ) : ZMod p))
        (eq_one_of_comm (Matrix.GeneralLinearGroup.det.comp φ))
      simpa using h
    exact false_of_nine_in_special hk2 hE9 (fun x => Subtype.ext (hE3 x x.2))
      (φ.comp E.subtype) hinj (fun x => hdet1 x)
  ·
    have hφ1 : φ = 1 := eq_one_of_cover φ θ hθs hA
    have hle : ρ.range ≤ (autQuotient (frattini V)).ker := by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker]
      have h : (elemAutEquivGL ε) ((autQuotient (frattini V)) (ρ x)) = 1 := by
        have := congrArg (fun f : L →* GL (Fin k) (ZMod p) => f x) hφ1
        simpa [hφ] using this
      exact (map_eq_one_iff _ (elemAutEquivGL ε).injective).mp h
    have hpg : IsPGroup p ρ.range := (isPGroup_ker_autQuotient_frattini hV).to_le hle
    have : Group.IsNilpotent ρ.range := hpg.isNilpotent
    exact eq_one_of_solvable_range ρ inferInstance

end CFSG.RankThree.PartTwo.KFacts.KS152
