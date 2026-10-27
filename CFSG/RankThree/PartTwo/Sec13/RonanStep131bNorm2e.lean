module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bNorm2

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

@[expose] def Norm2e (X : Type) [Group X] : Prop :=
  ∀ P : Subgroup (MulAut X), IsPGroup 3 P → (∀ σ ∈ P, σ ^ 3 = 1) → Nat.card P ≤ 9 →
    ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ σ ∈ P, V.map σ.toMonoidHom = V

theorem Norm2.toNorm2e {X : Type} [Group X] (h : Norm2 X) : Norm2e X :=
  fun P hP _ hP9 => h P hP hP9

theorem Norm2e.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : Norm2e Y) :
    Norm2e X := by
  intro P hP hexp hcard
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hP' : IsPGroup 3 (P.map (MulAut.congr e).toMonoidHom) := hP.map _
  have hcard' : Nat.card (P.map (MulAut.congr e).toMonoidHom) ≤ 9 := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hcard
  have hexp' : ∀ τ ∈ P.map (MulAut.congr e).toMonoidHom, τ ^ 3 = 1 := by
    rintro _ ⟨σ, hσ, rfl⟩
    show ((MulAut.congr e) σ) ^ 3 = 1
    rw [← map_pow, hexp σ hσ, map_one]
  obtain ⟨V', hV'ne, hV'2, hV'inv⟩ := h _ hP' hexp' hcard'
  refine ⟨V'.comap e.toMonoidHom, ?_, ?_, ?_⟩
  · intro hbot
    apply hV'ne
    rw [Subgroup.eq_bot_iff_forall] at hbot
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hx : e.symm y ∈ V'.comap e.toMonoidHom := by
      rw [Subgroup.mem_comap]
      simpa using hy
    have h1 := hbot _ hx
    have h2 := congrArg e h1
    simpa using h2
  · exact IsPGroup.comap_of_injective hV'2 e.toMonoidHom e.injective
  · intro σ hσ
    apply norm2_map_eq_of_forall_mem_iff
    intro x
    have hτ : (MulAut.congr e) σ ∈ P.map (MulAut.congr e).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hσ
    have key := norm2_mem_iff_of_map_eq (hV'inv _ hτ) (e x)
    have hcongr : (MulAut.congr e) σ (e x) = e (σ x) := by
      simp [MulAut.congr_apply]
    rw [hcongr] at key
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    exact key

theorem norm2e_of_center_quotient {Y X : Type} [Group Y] [Finite Y] [Group X]
    (hZ : IsPGroup 3 (Subgroup.center Y)) (e : Y ⧸ Subgroup.center Y ≃* X) (h : Norm2e X) :
    Norm2e Y := by
  have hW : Norm2e (Y ⧸ Subgroup.center Y) := Norm2e.of_mulEquiv e h
  intro P hP hexp hcard
  have hPbar : IsPGroup 3 (P.map (norm2_quotAutHom Y)) := hP.map _
  have hcardbar : Nat.card (P.map (norm2_quotAutHom Y)) ≤ 9 := by
    refine le_trans (Nat.card_le_card_of_surjective
      (fun x : P => (⟨norm2_quotAutHom Y x.1, Subgroup.mem_map_of_mem _ x.2⟩ :
        P.map (norm2_quotAutHom Y))) ?_) hcard
    rintro ⟨τ, hτ⟩
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hτ
    exact ⟨⟨σ, hσ⟩, rfl⟩
  have hexpbar : ∀ τ ∈ P.map (norm2_quotAutHom Y), τ ^ 3 = 1 := by
    rintro _ ⟨σ, hσ, rfl⟩
    show (norm2_quotAutHom Y σ) ^ 3 = 1
    rw [← map_pow, hexp σ hσ, map_one]
  obtain ⟨V₁, hV₁ne, hV₁2, hV₁inv⟩ := hW _ hPbar hexpbar hcardbar
  obtain ⟨Vt, hVt⟩ : ∃ Vt : Subgroup Y, ∀ x : Y, x ∈ Vt ↔ ((x : Y ⧸ Subgroup.center Y)) ∈ V₁ :=
    ⟨V₁.comap (QuotientGroup.mk' (Subgroup.center Y)), fun x => Iff.rfl⟩
  have hVt_inv : ∀ σ ∈ P, ∀ x : Y, σ x ∈ Vt ↔ x ∈ Vt := by
    intro σ hσ x
    rw [hVt, hVt, ← norm2_quotAutHom_mk σ x]
    exact norm2_mem_iff_of_map_eq (hV₁inv _ (Subgroup.mem_map_of_mem _ hσ)) _
  have hNil : Group.IsNilpotent Vt := by
    haveI : Group.IsNilpotent V₁ := hV₁2.isNilpotent
    obtain ⟨f, hf⟩ : ∃ f : Vt →* V₁, ∀ x : Vt,
        ((f x : V₁) : Y ⧸ Subgroup.center Y) = ((x : Y) : Y ⧸ Subgroup.center Y) :=
      ⟨{ toFun := fun x => ⟨((x : Y) : Y ⧸ Subgroup.center Y), (hVt _).mp x.2⟩
         map_one' := Subtype.ext (by simp)
         map_mul' := fun a b => Subtype.ext (by simp) }, fun x => rfl⟩
    refine Subgroup.isNilpotent_of_ker_le_center f ?_
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : ((x : Y) : Y ⧸ Subgroup.center Y) = 1 := by
      rw [← hf x]
      exact congrArg Subtype.val hx
    have hxZ : (x : Y) ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp hxZ (g : Y)
  haveI : Group.IsNilpotent Vt := hNil
  obtain ⟨Q, -⟩ := IsPGroup.exists_le_sylow (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup Vt))
  have hkey : ∀ q : Vt, (∃ k : ℕ, q ^ 2 ^ k = 1) → q ∈ (Q : Subgroup Vt) := by
    rintro q ⟨k, hk⟩
    have hR : IsPGroup 2 (Subgroup.zpowers q) := by
      apply IsPGroup.of_card_dvd_pow (n := k)
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk
    have hmax := Q.is_maximal' (IsPGroup.to_sup_of_normal_left Q.isPGroup' hR) le_sup_left
    have hq : q ∈ (Q : Subgroup Vt) ⊔ Subgroup.zpowers q :=
      (le_sup_right : Subgroup.zpowers q ≤ (Q : Subgroup Vt) ⊔ Subgroup.zpowers q)
        (Subgroup.mem_zpowers q)
    rw [hmax] at hq
    exact hq
  have hnt : ∃ q : Vt, q ≠ 1 ∧ ∃ k : ℕ, q ^ 2 ^ k = 1 := by
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ V₁, y ≠ 1 := by
      by_contra hcon
      apply hV₁ne
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      by_contra hy1
      exact hcon ⟨y, hy, hy1⟩
    obtain ⟨k, hk⟩ := hV₁2 ⟨y, hy⟩
    have hyk : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective y
    have hu : ((u ^ 2 ^ k : Y) : Y ⧸ Subgroup.center Y) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hyk
    have hzZ : u ^ 2 ^ k ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff _).mp hu
    obtain ⟨m, hm⟩ := hZ ⟨u ^ 2 ^ k, hzZ⟩
    have hm' : (u ^ 2 ^ k) ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hcop : Nat.Coprime (3 ^ m) (2 ^ k) := Nat.Coprime.pow m k (by norm_num)
    have hy3 : ((u : Y) : Y ⧸ Subgroup.center Y) ^ 3 ^ m ≠ 1 := by
      intro h3
      apply hy1
      have h4 := pow_gcd_eq_one.mpr ⟨h3, hyk⟩
      rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h4
      exact h4
    have hxVt : u ^ 3 ^ m ∈ Vt := by
      rw [hVt, QuotientGroup.mk_pow]
      exact V₁.pow_mem hy _
    have hpow : (u ^ 3 ^ m) ^ 2 ^ k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hm']
    refine ⟨⟨u ^ 3 ^ m, hxVt⟩, ?_, k, Subtype.ext (by simpa using hpow)⟩
    intro hq
    apply hy3
    have h' : u ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hq
    rw [← QuotientGroup.mk_pow, h', QuotientGroup.mk_one]
  obtain ⟨V, hV⟩ : ∃ V : Subgroup Y, ∀ x : Y, x ∈ V ↔ (x ∈ Vt ∧ ∃ k : ℕ, x ^ 2 ^ k = 1) := by
    refine ⟨(Q : Subgroup Vt).map Vt.subtype, fun x => ?_⟩
    constructor
    · intro hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      refine ⟨q.2, ?_⟩
      obtain ⟨k, hk⟩ := Q.isPGroup' ⟨q, hq⟩
      exact ⟨k, by simpa using congrArg (fun t : (Q : Subgroup Vt) => ((t : Vt) : Y)) hk⟩
    · rintro ⟨hxVt, k, hk⟩
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hxVt⟩, hkey ⟨x, hxVt⟩ ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩
  have hV2 : IsPGroup 2 V := by
    intro g
    obtain ⟨_, k, hk⟩ := (hV g.1).mp g.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hVne : V ≠ ⊥ := by
    obtain ⟨q, hq1, k, hk⟩ := hnt
    intro hbot
    apply hq1
    have hmem : (q : Y) ∈ V := (hV _).mpr ⟨q.2, k, by simpa using congrArg Subtype.val hk⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hVinv : ∀ σ ∈ P, V.map σ.toMonoidHom = V := by
    intro σ hσ
    apply norm2_map_eq_of_forall_mem_iff
    intro x
    have hpow : ∀ k : ℕ, σ x ^ 2 ^ k = 1 ↔ x ^ 2 ^ k = 1 := by
      intro k
      rw [← map_pow]
      constructor
      · intro hk
        exact σ.injective (hk.trans (map_one σ).symm)
      · intro hk
        rw [hk, map_one]
    rw [hV, hV]
    simp only [hpow]
    rw [hVt_inv σ hσ x]
  exact ⟨V, hVne, hV2, hVinv⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
