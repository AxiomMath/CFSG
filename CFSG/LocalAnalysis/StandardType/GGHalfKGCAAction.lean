module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCARes
public import CFSG.LocalAnalysis.StandardType.GGHalfKGCASimple
public import CFSG.LocalAnalysis.StandardType.GGHalfKGCASplit
public import CFSG.LocalAnalysis.StandardType.GGHalfKGCANum

public section

namespace CFSG.StandardType

theorem ggKGCAAction
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    {m : ℕ} (hm : 5 ≤ m) (hV : Module.finrank GGKGCF V = m + 2)
    (J : Subgroup (V ≃ₗ[GGKGCF] V)) (k : V ≃ₗ[GGKGCF] V)
    (hJ : Nonempty (↥J ≃* Matrix.SpecialLinearGroup (Fin m) GGKGCF))
    (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1)
    (hkJ : k ∈ Subgroup.centralizer (J : Set (V ≃ₗ[GGKGCF] V))) :
    Module.finrank GGKGCF (ggKGCAFix k) = m ∧ Module.finrank GGKGCF (ggKGCAPlane k) = 2 ∧
      (∀ a ∈ J, ∀ t ∈ ggKGCAPlane k, a t = t) ∧
      (∀ φ : ggKGCAFix k ≃ₗ[GGKGCF] ggKGCAFix k, ∃ a ∈ J, ∀ w : ggKGCAFix k,
        (a (w : V) : V) = (φ w : V)) := by
  classical
  haveI : Finite V := Module.finite_of_finite GGKGCF
  haveI : Fintype V := Fintype.ofFinite V
  have hcomm : ∀ a ∈ J, a * k = k * a := fun a ha =>
    (Subgroup.mem_centralizer_iff.mp hkJ) a ha
  have hstable : ∀ a ∈ J, (∀ w ∈ ggKGCAFix k, a w ∈ ggKGCAFix k) ∧
      (∀ t ∈ ggKGCAPlane k, a t ∈ ggKGCAPlane k) := fun a ha =>
    ggKGCASplit_stable (k := k) (g := a) (hcomm a ha)
  have hJT : ∀ a ∈ J, ∀ x ∈ ggKGCAPlane k, a x ∈ ggKGCAPlane k :=
    fun a ha x hx => (hstable a ha).2 x hx
  have hJW : ∀ a ∈ J, ∀ x ∈ ggKGCAFix k, a x ∈ ggKGCAFix k :=
    fun a ha x hx => (hstable a ha).1 x hx
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin m) GGKGCF) := ggKGCASimple (by omega)
  haveI : IsSimpleGroup ↥J := MulEquiv.isSimpleGroup hJ.some
  have hcompl : IsCompl (ggKGCAFix k) (ggKGCAPlane k) := ggKGCASplit_isCompl k hk3
  have hfr : Module.finrank GGKGCF (ggKGCAFix k) + Module.finrank GGKGCF (ggKGCAPlane k) =
      Module.finrank GGKGCF V := Submodule.finrank_add_eq_of_isCompl hcompl
  have hfr' : Module.finrank GGKGCF (ggKGCAFix k) + Module.finrank GGKGCF (ggKGCAPlane k) =
      m + 2 := by rw [hfr, hV]
  obtain ⟨r, hr⟩ := ggKGCASplit_rank (k := k) hk3
  have hTne : ggKGCAPlane k ≠ ⊥ := ggKGCASplit_plane_ne_bot (k := k) hk3 hk1
  have hT1 : 1 ≤ Module.finrank GGKGCF (ggKGCAPlane k) :=
    (Submodule.one_le_finrank_iff).mpr hTne
  have hr1 : 1 ≤ r := by omega
  have hWle : Module.finrank GGKGCF (ggKGCAFix k) ≤ m := by omega
  let ρT : ↥J →* (ggKGCAPlane k ≃ₗ[GGKGCF] ggKGCAPlane k) :=
    ggKGCARes (ggKGCAPlane k) J hJT
  let ρW : ↥J →* (ggKGCAFix k ≃ₗ[GGKGCF] ggKGCAFix k) :=
    ggKGCARes (ggKGCAFix k) J hJW
  have hρT_apply : ∀ (a : ↥J) (x : ggKGCAPlane k),
      ((ρT a x : ggKGCAPlane k) : V) = (a : V ≃ₗ[GGKGCF] V) (x : V) :=
    fun a x => ggKGCARes_apply (ggKGCAPlane k) J hJT a x
  have hρW_apply : ∀ (a : ↥J) (x : ggKGCAFix k),
      ((ρW a x : ggKGCAFix k) : V) = (a : V ≃ₗ[GGKGCF] V) (x : V) :=
    fun a x => ggKGCARes_apply (ggKGCAFix k) J hJW a x
  have hJcard : Nat.card ↥J = Nat.card (Matrix.SpecialLinearGroup (Fin m) GGKGCF) :=
    Nat.card_congr hJ.some.toEquiv
  have hkerT : ρT.ker = ⊥ ∨ ρT.ker = ⊤ := by
    haveI : ρT.ker.Normal := MonoidHom.normal_ker ρT
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal ρT.ker
  have hkerTtop : ρT.ker = ⊤ := by
    rcases hkerT with hbot | htop
    · exfalso
      have hinjT : Function.Injective ρT := (MonoidHom.ker_eq_bot_iff ρT).mp hbot
      have hcardle : Nat.card ↥J ≤
          Nat.card (Set.range fun g : {g : V ≃ₗ[GGKGCF] V // g * k = k * g} =>
            fun t : ggKGCAPlane k => (g.1 t : V)) := by
        let Ψ : ↥J → Set.range (fun g : {g : V ≃ₗ[GGKGCF] V // g * k = k * g} =>
            fun t : ggKGCAPlane k => (g.1 t : V)) :=
          fun a => ⟨fun t => ((a : V ≃ₗ[GGKGCF] V) (t : V) : V),
            ⟨⟨(a : V ≃ₗ[GGKGCF] V), hcomm a.1 a.2⟩, rfl⟩⟩
        have hΨinj : Function.Injective Ψ := by
          intro a a' h
          have hval : ∀ t : ggKGCAPlane k,
              ((a : V ≃ₗ[GGKGCF] V) (t : V) : V) =
              ((a' : V ≃ₗ[GGKGCF] V) (t : V) : V) := by
            intro t
            have h' := congrArg (fun y : Set.range
                (fun g : {g : V ≃ₗ[GGKGCF] V // g * k = k * g} =>
                  fun t : ggKGCAPlane k => (g.1 t : V)) =>
              (y.1 : ggKGCAPlane k → V) t) h
            simpa using h'
          have hρ : ρT a = ρT a' := by
            apply LinearEquiv.ext
            intro t
            apply Subtype.ext
            rw [hρT_apply, hρT_apply]
            exact hval t
          exact hinjT hρ
        exact Nat.card_le_card_of_injective Ψ hΨinj
      have hcardT : Nat.card (Set.range fun g : {g : V ≃ₗ[GGKGCF] V // g * k = k * g} =>
            fun t : ggKGCAPlane k => (g.1 t : V)) ≤ Nat.card (ggKGCAPlane k) ^ r :=
        ggKGCASplit_card_restrict_le (k := k) hk3 hr
      have hcardT2 : Nat.card (ggKGCAPlane k) = 2 ^ (2 * r) := by
        rw [Module.natCard_eq_pow_finrank (K := GGKGCF), hr, GaloisField.card 2 1 (by norm_num)]
        norm_num
      have hbound : Nat.card ↥J ≤ (2 ^ (2 * r)) ^ r := by
        have h := le_trans hcardle hcardT
        rwa [hcardT2] at h
      have hrle : 2 * r ≤ m + 2 := by
        have h := Submodule.finrank_le (ggKGCAPlane k)
        omega
      have hpow := ggKGCANum_pow_lt hm hrle
      have hbound' := hbound
      rw [hJcard] at hbound'
      exact (not_lt_of_ge hbound') hpow
    · exact htop
  have htriv : ∀ a ∈ J, ∀ t ∈ ggKGCAPlane k, a t = t := by
    intro a ha t ht
    have hmem : (⟨a, ha⟩ : ↥J) ∈ ρT.ker := by rw [hkerTtop]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hmem
    have h2 := congrArg (fun e : ggKGCAPlane k ≃ₗ[GGKGCF] ggKGCAPlane k => e ⟨t, ht⟩) hmem
    have h3 : ((ρT ⟨a, ha⟩) ⟨t, ht⟩ : V) = t := by
      have := congrArg Subtype.val h2
      simpa using this
    rw [hρT_apply] at h3
    exact h3
  haveI : Fintype (ggKGCAFix k) := Fintype.ofFinite _
  haveI : Finite (ggKGCAFix k ≃ₗ[GGKGCF] ggKGCAFix k) :=
    Finite.of_injective (fun e : ggKGCAFix k ≃ₗ[GGKGCF] ggKGCAFix k =>
        (e : ggKGCAFix k → ggKGCAFix k))
      (fun e1 e2 h => LinearEquiv.ext (congrFun h))
  have hinjW : Function.Injective ρW := by
    intro a b hab
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ ggKGCAFix k ⊔ ggKGCAPlane k := by
      rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hv
    obtain ⟨w, hw, t, ht, hwt⟩ := hv
    have haw : (a : V ≃ₗ[GGKGCF] V) w = (b : V ≃ₗ[GGKGCF] V) w := by
      have h := congrArg (fun e : ggKGCAFix k ≃ₗ[GGKGCF] ggKGCAFix k => e ⟨w, hw⟩) hab
      have h2 := congrArg Subtype.val h
      rw [hρW_apply, hρW_apply] at h2
      exact h2
    calc (a : V ≃ₗ[GGKGCF] V) v
        = (a : V ≃ₗ[GGKGCF] V) (w + t) := by rw [← hwt]
      _ = (a : V ≃ₗ[GGKGCF] V) w + (a : V ≃ₗ[GGKGCF] V) t := by rw [map_add]
      _ = (b : V ≃ₗ[GGKGCF] V) w + t := by rw [haw, htriv a.1 a.2 t ht]
      _ = (b : V ≃ₗ[GGKGCF] V) w + (b : V ≃ₗ[GGKGCF] V) t := by rw [htriv b.1 b.2 t ht]
      _ = (b : V ≃ₗ[GGKGCF] V) (w + t) := by rw [map_add]
      _ = (b : V ≃ₗ[GGKGCF] V) v := by rw [← hwt]
  have hcardW : Nat.card ↥J ≤ Nat.card (ggKGCAFix k ≃ₗ[GGKGCF] ggKGCAFix k) :=
    Nat.card_le_card_of_injective ρW hinjW
  have hnlt : ¬ Module.finrank GGKGCF (ggKGCAFix k) < m := by
    intro hb
    have hlt : Nat.card (ggKGCAFix k ≃ₗ[GGKGCF] ggKGCAFix k) <
        Nat.card (Matrix.SpecialLinearGroup (Fin m) GGKGCF) :=
      ggKGCANum_card_aut_lt (W := ggKGCAFix k) (m := m) (by omega) hb
    have hcardW' := hcardW
    rw [hJcard] at hcardW'
    exact (not_lt_of_ge hcardW') hlt
  have hdimW : Module.finrank GGKGCF (ggKGCAFix k) = m :=
    le_antisymm hWle (not_lt.mp hnlt)
  have hdimT : Module.finrank GGKGCF (ggKGCAPlane k) = 2 := by omega
  have hcardWm : Nat.card (ggKGCAFix k ≃ₗ[GGKGCF] ggKGCAFix k) =
      Nat.card (Matrix.SpecialLinearGroup (Fin m) GGKGCF) := by
    rw [ggKGCANum_card_aut, hdimW, ggKGCANum_card_SL_eq_GL m]
  refine ⟨hdimW, hdimT, htriv, ?_⟩
  intro φ
  have hsurjW : Function.Surjective ρW := by
    have hbij : Function.Bijective ρW :=
      (Nat.bijective_iff_injective_and_card ρW).mpr
        ⟨hinjW, by rw [hJcard, hcardWm]⟩
    exact hbij.2
  obtain ⟨a, ha⟩ := hsurjW φ
  refine ⟨a.1, a.2, ?_⟩
  intro w
  have h := congrArg (fun e : ggKGCAFix k ≃ₗ[GGKGCF] ggKGCAFix k => e w) ha
  have h2 := congrArg Subtype.val h
  rw [hρW_apply] at h2
  exact h2

end CFSG.StandardType

end
