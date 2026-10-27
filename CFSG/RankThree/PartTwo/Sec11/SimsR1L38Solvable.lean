module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1L38SolvableB
public import CFSG.RankThree.PartTwo.Sec11.SimsR1Defs

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1

open CFSG.Assembly.RankThreeEven (projSL)
open L38Solvable

theorem l38SolvableFix_of_faithful (hFF : SimsR1L38FaithfulFix) : SimsR1L38SolvableFix := by
  intro r _ hr5 X _ _ hperf N _ hN hN3 hiso V _ _ _ ρ hρN
  obtain ⟨e⟩ := hiso
  have hK2 : (2 : ZMod r) ≠ 0 :=
    Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  have : IsSimpleGroup (projSL 3 (GaloisField 2 3)) := isSimpleGroup_projSL_three_eight
  have hsimple : IsSimpleGroup (X ⧸ N) := MulEquiv.isSimpleGroup e
  have hsmallX := @index_lt_eq_top_L38 X _ _ hperf N _ hN e
  suffices H : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod r) V]
      [Module.Finite (ZMod r) V] (ρ : X →* (V →ₗ[ZMod r] V)),
      Module.finrank (ZMod r) V = n → (∃ x, ρ x ≠ 1) →
        ∃ t : X, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
          3 ≤ Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1)) by
    have hρ : ∃ x, ρ x ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hρN fun x _ => hall x
    exact H _ V ρ rfl hρ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ ρ hn hρ
  have hVnt : Nontrivial V := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    obtain ⟨x, hx⟩ := hρ
    exact hx (LinearMap.ext fun v => Subsingleton.elim _ _)
  by_cases hirr : LSSolvableProof.IsIrreducibleRep ρ
  · have hKN : ρ.ker ≤ N := @LSSolvableProof.ker_le_of_perfect X _ hperf N _ hN hsimple _ _ ρ hρ
    have : Group.IsPerfect X := hperf
    by_cases hNK : N ≤ ρ.ker
    ·
      set ρ₀ : X ⧸ N →* (V →ₗ[ZMod r] V) := QuotientGroup.lift N ρ (fun x hx => hNK hx)
        with hρ₀
      set ρ' : projSL 3 (GaloisField 2 3) →* (V →ₗ[ZMod r] V) :=
        ρ₀.comp e.symm.toMonoidHom with hρ'
      have hρ'apply : ∀ x : X, ρ' (e (QuotientGroup.mk' N x)) = ρ x := fun x => by
        rw [hρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
          hρ₀, QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
      have hρ'inj : Function.Injective ρ' := by
        rw [injective_iff_map_eq_one]
        intro a ha
        obtain ⟨q, rfl⟩ := e.surjective a
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
        rw [hρ'apply] at ha
        have hx : x ∈ N := hKN ha
        have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
        rw [h1, map_one]
      obtain ⟨t', ht'2, ht'dim⟩ := hFF r hr5 V ρ' hρ'inj
      have ht'sq : t' * t' = 1 := by
        have h := pow_orderOf_eq_one t'
        rw [ht'2, sq] at h
        exact h
      have ht'1 : t' ≠ 1 := by
        intro h
        rw [h, orderOf_one] at ht'2
        omega
      obtain ⟨t, htq, k, htk⟩ := TwoStarProof.exists_two_element_lift (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) (y := e.symm t')
        (by rw [← map_mul, ht'sq, map_one])
      have hρt : ρ t = ρ' t' := by
        rw [← hρ'apply, htq, MulEquiv.apply_symm_apply]
      refine ⟨t, ?_, ⟨k, htk⟩, ?_⟩
      · rw [hρt]
        intro h1
        exact ht'1 (hρ'inj (h1.trans (map_one ρ').symm))
      · rw [hρt]
        exact ht'dim
    ·
      set ρbar : X ⧸ ρ.ker →* (V →ₗ[ZMod r] V) := QuotientGroup.lift ρ.ker ρ (fun _ hx => hx)
        with hρbar
      have hinj : Function.Injective ρbar := LSSolvableProof.liftKer_injective ρ
      set M : Subgroup (X ⧸ ρ.ker) := N.map (QuotientGroup.mk' ρ.ker) with hM
      have hMsolv : Group.IsSolvable M := by
        have : Group.IsSolvable N := hN
        refine Group.isSolvable_of_surjective
          (f := ((QuotientGroup.mk' ρ.ker).comp N.subtype).codRestrict M
            (fun x => ⟨x, x.2, rfl⟩)) ?_
        rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      have hM3 : ¬ 3 ∣ Nat.card M := fun h =>
        hN3 (h.trans (Subgroup.card_map_dvd (H := N) (QuotientGroup.mk' ρ.ker)))
      have hMne : M ≠ ⊥ := by
        intro h
        apply hNK
        intro x hx
        have : QuotientGroup.mk' ρ.ker x ∈ M := ⟨x, hx, rfl⟩
        rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
        exact this
      set e' : (X ⧸ ρ.ker) ⧸ M ≃* projSL 3 (GaloisField 2 3) :=
        (QuotientGroup.quotientQuotientEquivQuotient ρ.ker N hKN).trans e with he'
      have hsmallY : ∀ J : Subgroup (X ⧸ ρ.ker), J.Normal → J.index < 262080 → J = ⊤ := by
        intro J hJ hidx
        have h1 : (J.comap (QuotientGroup.mk' ρ.ker)).index = J.index :=
          Subgroup.index_comap_of_surjective J (QuotientGroup.mk'_surjective ρ.ker)
        have h2 := hsmallX (J.comap (QuotientGroup.mk' ρ.ker)) (hJ.comap _) (h1 ▸ hidx)
        rw [eq_top_iff]
        intro q _
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ρ.ker q
        have : x ∈ J.comap (QuotientGroup.mk' ρ.ker) := by rw [h2]; exact Subgroup.mem_top x
        exact this
      have hirr' : LSSolvableProof.IsIrreducibleRep ρbar := by
        intro W hW
        apply hirr W
        intro x v hv
        have := hW (QuotientGroup.mk' ρ.ker x) v hv
        rwa [hρbar, QuotientGroup.mk'_apply, QuotientGroup.lift_mk] at this
      have hdim : 7 ≤ Module.finrank (ZMod r) V :=
        seven_le_finrank_of_irreducible_L38 M hMsolv hM3 hMne e' hsmallY ρbar hinj hirr'
      let π : X ⧸ ρ.ker →* projSL 3 (GaloisField 2 3) :=
        e.toMonoidHom.comp
          (QuotientGroup.map ρ.ker N (MonoidHom.id X) (by rw [Subgroup.comap_id]; exact hKN))
      have hπs : Function.Surjective π := by
        refine e.surjective.comp ?_
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
        refine ⟨QuotientGroup.mk' ρ.ker x, ?_⟩
        rw [QuotientGroup.mk'_apply, QuotientGroup.map_mk, MonoidHom.id_apply,
          QuotientGroup.mk'_apply]
      obtain ⟨a, b, ha, hb, hab, ha1, hb1, hne⟩ := exists_klein_four_L38 π hπs
      have hρa : ρbar a * ρbar a = 1 := by rw [← map_mul, ha, map_one]
      have hρb : ρbar b * ρbar b = 1 := by rw [← map_mul, hb, map_one]
      have hρab : ρbar a * ρbar b = ρbar b * ρbar a := by rw [← map_mul, ← map_mul, hab]
      have hsum := LSSolvableProof.finrank_le_add_ker hK2 hρa hρb hρab
      obtain ⟨g, hg2, hg1, hgdim⟩ : ∃ g : X ⧸ ρ.ker, g * g = 1 ∧ g ≠ 1 ∧
          3 ≤ Module.finrank (ZMod r) (LinearMap.ker (ρbar g - 1)) := by
        by_cases h1 : 3 ≤ Module.finrank (ZMod r) (LinearMap.ker (ρbar a - 1))
        · exact ⟨a, ha, ha1, h1⟩
        by_cases h2 : 3 ≤ Module.finrank (ZMod r) (LinearMap.ker (ρbar b - 1))
        · exact ⟨b, hb, hb1, h2⟩
        refine ⟨a * b, ?_, ?_, ?_⟩
        · calc a * b * (a * b) = a * b * (b * a) := by rw [hab]
            _ = 1 := by rw [mul_assoc, ← mul_assoc b b a, hb, one_mul, ha]
        · intro h1'
          apply hne
          calc a = a * (a * b) := by rw [h1', mul_one]
            _ = b := by rw [← mul_assoc, ha, one_mul]
        · rw [map_mul]
          omega
      obtain ⟨t, htg, k, htk⟩ := TwoStarProof.exists_two_element_lift (QuotientGroup.mk' ρ.ker)
        (QuotientGroup.mk'_surjective ρ.ker) hg2
      have hρt : ρ t = ρbar g := by
        rw [← htg, QuotientGroup.mk'_apply, hρbar, QuotientGroup.lift_mk]
      refine ⟨t, ?_, ⟨k, htk⟩, ?_⟩
      · rw [hρt]
        intro h1
        exact hg1 (hinj (h1.trans (map_one ρbar).symm))
      · rw [hρt]
        exact hgdim
  ·
    obtain ⟨W, hW, hW0, hWt⟩ : ∃ W : Submodule (ZMod r) V, (∀ x, ∀ v ∈ W, ρ x v ∈ W) ∧
        W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra hall
      push Not at hall
      exact hirr fun W hW => by
        by_cases h0 : W = ⊥
        · exact Or.inl h0
        · exact Or.inr (hall W hW h0)
    let ρW : X →* (W →ₗ[ZMod r] W) :=
      { toFun := fun x => (ρ x).restrict (p := W) (q := W) (hW x)
        map_one' := by
          apply LinearMap.ext
          intro w
          apply Subtype.ext
          simp
        map_mul' := fun x y => by
          apply LinearMap.ext
          intro w
          apply Subtype.ext
          simp }
    let ρQ : X →* ((V ⧸ W) →ₗ[ZMod r] (V ⧸ W)) :=
      { toFun := fun x => W.mapQ W (ρ x) (fun v hv => hW x v hv)
        map_one' := by
          apply Submodule.linearMap_qext
          apply LinearMap.ext
          intro v
          simp
        map_mul' := fun x y => by
          apply Submodule.linearMap_qext
          apply LinearMap.ext
          intro v
          simp }
    have hWlt : Module.finrank (ZMod r) W < n := hn ▸ Submodule.finrank_lt hWt
    have hQlt : Module.finrank (ZMod r) (V ⧸ W) < n := by
      have h1 := W.finrank_quotient_add_finrank
      have h2 : 0 < Module.finrank (ZMod r) W := by
        rw [Module.finrank_pos_iff]
        exact Submodule.nontrivial_iff_ne_bot.mpr hW0
      omega
    by_cases hρW : ∃ x, ρW x ≠ 1
    · obtain ⟨t, ht1, htk, htd⟩ := ih _ hWlt W ρW rfl hρW
      refine ⟨t, ?_, htk, htd.trans (finrank_ker_restrict_sub_one_le W (ρ t) (hW t))⟩
      intro h
      apply ht1
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      simp [ρW, h]
    by_cases hρQ : ∃ x, ρQ x ≠ 1
    · obtain ⟨t, ht1, htk, htd⟩ := ih _ hQlt (V ⧸ W) ρQ rfl hρQ
      refine ⟨t, ?_, htk,
        htd.trans (finrank_ker_sub_one_mapQ_le W (ρ t) (fun v hv => hW t v hv))⟩
      intro h
      apply ht1
      apply Submodule.linearMap_qext
      apply LinearMap.ext
      intro v
      simp [ρQ, h]
    exfalso
    push Not at hρW hρQ
    have hfixW : ∀ x, ∀ w ∈ W, ρ x w = w := by
      intro x w hw
      have := congrArg (fun φ : W →ₗ[ZMod r] W => ((φ ⟨w, hw⟩ : W) : V)) (hρW x)
      simpa [ρW] using this
    have hfixQ : ∀ x v, ρ x v - v ∈ W := by
      intro x v
      have := congrArg (fun φ : (V ⧸ W) →ₗ[ZMod r] (V ⧸ W) => φ (Submodule.Quotient.mk v))
        (hρQ x)
      simp only [ρQ, MonoidHom.coe_mk, OneHom.coe_mk, Submodule.mapQ_apply,
        Module.End.one_apply] at this
      exact (Submodule.Quotient.eq W).mp this
    have hcomm : ∀ x y, ρ x * ρ y = ρ y * ρ x := by
      intro x y
      apply LinearMap.ext
      intro v
      rw [Module.End.mul_apply, Module.End.mul_apply]
      have ha := hfixQ x v
      have hb := hfixQ y v
      have e1 : ρ y v = v + (ρ y v - v) := by abel
      have e2 : ρ x v = v + (ρ x v - v) := by abel
      rw [e1, map_add, hfixW x _ hb, e2, map_add, hfixW y _ ha]
      abel
    have hker : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ ρ.ker := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, hcomm x y,
        mul_assoc (ρ y), ← map_mul, mul_inv_cancel, map_one, mul_one, ← map_mul,
        mul_inv_cancel, map_one]
    have htop : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top
    rw [htop] at hker
    obtain ⟨x, hx⟩ := hρ
    exact hx (hker (Subgroup.mem_top x))

end CFSG.RankThree.PartTwo.Sec11.SimsR1
