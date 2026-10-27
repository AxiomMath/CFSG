module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1L38SolvableA
public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofHeis

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.L38Solvable

open CFSG.Assembly.RankThreeEven (projSL)

section FixedSpaces

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_ker_restrict_sub_one_le (W : Submodule K V) (f : V →ₗ[K] V)
    (hW : ∀ w ∈ W, f w ∈ W) :
    Module.finrank K (LinearMap.ker (f.restrict hW - 1)) ≤
      Module.finrank K (LinearMap.ker (f - 1)) := by
  let g : LinearMap.ker (f.restrict hW - 1) →ₗ[K] LinearMap.ker (f - 1) :=
    { toFun := fun w => ⟨(w.1 : V), by
        have := w.2
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this ⊢
        exact congrArg Subtype.val this⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  have hg : Function.Injective g := fun a b h => by
    have h' := congrArg (fun x : LinearMap.ker (f - 1) => (x : V)) h
    exact Subtype.ext (Subtype.ext h')
  exact LinearMap.finrank_le_finrank_of_injective hg

theorem finrank_ker_mapQ_le (W : Submodule K V) (T : V →ₗ[K] V) (hT : W ≤ W.comap T) :
    Module.finrank K (LinearMap.ker (W.mapQ W T hT)) ≤ Module.finrank K (LinearMap.ker T) := by
  have h1 := (W.mapQ W T hT).finrank_range_add_finrank_ker
  have h2 := T.finrank_range_add_finrank_ker
  have h3 := W.finrank_quotient_add_finrank
  have h4 : Module.finrank K (LinearMap.range T) ≤
      Module.finrank K (LinearMap.range (W.mapQ W T hT)) + Module.finrank K W := by
    let φ : LinearMap.range T →ₗ[K] V ⧸ W := W.mkQ ∘ₗ (LinearMap.range T).subtype
    have hφ : LinearMap.range φ = LinearMap.range (W.mapQ W T hT) := by
      ext q
      constructor
      · rintro ⟨⟨_, v, rfl⟩, rfl⟩
        exact ⟨W.mkQ v, rfl⟩
      · rintro ⟨q', rfl⟩
        obtain ⟨v, rfl⟩ := W.mkQ_surjective q'
        exact ⟨⟨T v, v, rfl⟩, rfl⟩
    let g : LinearMap.ker φ →ₗ[K] W :=
      { toFun := fun y => ⟨(y.1 : V), by
          have := y.2
          rw [LinearMap.mem_ker] at this
          exact (Submodule.Quotient.mk_eq_zero W).mp this⟩
        map_add' := fun a b => rfl
        map_smul' := fun c a => rfl }
    have hg : Function.Injective g := fun a b h => by
      have h' := congrArg (fun x : W => (x : V)) h
      exact Subtype.ext (Subtype.ext h')
    have h5 := φ.finrank_range_add_finrank_ker
    have h6 := LinearMap.finrank_le_finrank_of_injective hg
    rw [hφ] at h5
    omega
  omega

theorem finrank_ker_sub_one_mapQ_le (W : Submodule K V) (f : V →ₗ[K] V) (hf : W ≤ W.comap f) :
    Module.finrank K (LinearMap.ker (W.mapQ W f hf - 1)) ≤
      Module.finrank K (LinearMap.ker (f - 1)) := by
  have hT : W ≤ W.comap (f - 1) := by
    intro w hw
    rw [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply]
    exact W.sub_mem (hf hw) hw
  have h : W.mapQ W f hf - 1 = W.mapQ W (f - 1) hT := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro v
    simp [Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub]
  rw [h]
  exact finrank_ker_mapQ_le W (f - 1) hT

end FixedSpaces

theorem index_lt_eq_top_L38 {X : Type*} [Group X] [Finite X] [Group.IsPerfect X] {N : Subgroup X}
    [N.Normal] (hN : Group.IsSolvable N) (e : X ⧸ N ≃* projSL 3 (GaloisField 2 3)) :
    ∀ J : Subgroup X, J.Normal → J.index < 262080 → J = ⊤ := by
  intro J _ hidx
  by_contra hJ
  have : IsSimpleGroup (projSL 3 (GaloisField 2 3)) := isSimpleGroup_projSL_three_eight
  have hsimple : IsSimpleGroup (X ⧸ N) := MulEquiv.isSimpleGroup e
  obtain ⟨x, hx⟩ : ∃ x, x ∉ J := by
    by_contra hall
    push Not at hall
    exact hJ (eq_top_iff.mpr fun x _ => hall x)
  have hρ : ∃ x, QuotientGroup.mk' J x ≠ 1 := ⟨x, by
    rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]; exact hx⟩
  have hJN : (QuotientGroup.mk' J).ker ≤ N :=
    LSSolvableProof.ker_le_of_perfect hN hsimple _ hρ
  rw [QuotientGroup.ker_mk'] at hJN
  have hdvd := Subgroup.index_dvd_of_le hJN
  have hpos : 0 < J.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle := Nat.le_of_dvd hpos hdvd
  have hN' : N.index = Nat.card (projSL 3 (GaloisField 2 3)) := by
    rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv]
  rw [card_projSL_three_eight] at hN'
  omega

theorem seven_le_finrank_of_irreducible_L38 {r : ℕ} [Fact r.Prime]
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y] (M : Subgroup Y) [M.Normal]
    (hM : Group.IsSolvable M) (hM3 : ¬ 3 ∣ Nat.card M) (hMne : M ≠ ⊥)
    (e : Y ⧸ M ≃* projSL 3 (GaloisField 2 3))
    (hsmall : ∀ J : Subgroup Y, J.Normal → J.index < 262080 → J = ⊤)
    {V : Type} [AddCommGroup V] [Module (ZMod r) V] [Module.Finite (ZMod r) V] [Nontrivial V]
    (ρ : Y →* (V →ₗ[ZMod r] V)) (hρ : Function.Injective ρ)
    (hirr : LSSolvableProof.IsIrreducibleRep ρ) :
    7 ≤ Module.finrank (ZMod r) V := by
  by_contra hlt
  push Not at hlt
  have hdim : Module.finrank (ZMod r) V ≤ 6 := by omega
  by_cases hMZ : M ≤ Subgroup.center Y
  ·
    set π : Y →* projSL 3 (GaloisField 2 3) := e.toMonoidHom.comp (QuotientGroup.mk' M) with hπ
    have hπs : Function.Surjective π :=
      e.surjective.comp (QuotientGroup.mk'_surjective M)
    have hker : π.ker = M := by
      ext x
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine hMne ?_
    have h := kernel_eq_bot_of_central π hπs (hker ▸ hMZ) (by rw [hker]; exact hM3)
    rwa [hker] at h
  · obtain ⟨R, hRn, hZR, hRZ, hRR, s, hs, hpow, hact⟩ :=
      LSSolvableProof.exists_noncentral_normal M hM hMZ
    have : R.Normal := hRn
    exact LSSolvableProof.false_of_noncentral_normal hρ hirr hdim hsmall R hZR hRZ hRR hs hpow
      hact

end CFSG.RankThree.PartTwo.Sec11.SimsR1.L38Solvable
