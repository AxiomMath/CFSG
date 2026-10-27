module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Abstract

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def s15Normalizes (t : MulAut W) (A : Subgroup (MulAut W)) : Prop :=
  ∀ a : MulAut W, a ∈ A ↔ t * a * t⁻¹ ∈ A

@[expose] def s15TGroup (A : Subgroup (MulAut W)) (t : MulAut W) : Subgroup (MulAut W) :=
  Subgroup.closure {x | ∃ a ∈ A, x = a⁻¹ * t * a}

@[expose] def s15Semisimple (A : Subgroup (MulAut W)) : Prop :=
  ∀ S : Subgroup W, StableUnder A S →
    ∃ S' : Subgroup W, StableUnder A S' ∧ S ⊓ S' = ⊥ ∧ S ⊔ S' = ⊤

@[expose] def s15TwoCoreTrivial (A : Subgroup (MulAut W)) : Prop :=
  ∀ P : Subgroup ↥A, P.Normal → IsPGroup 2 ↥P → P = ⊥

private lemma s15_Three_commSub_sup_le (U V : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (U ⊔ V) X ≤ commSub U X ⊔ commSub V X := by
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  obtain ⟨u, hu, v, hv, hwv⟩ := Subgroup.mem_sup.1 hw
  rw [← hwv]
  have h1 : x (u * v) * (u * v)⁻¹ = (x u * u⁻¹) * (x v * v⁻¹) := by
    rw [map_mul, mul_inv_rev]
    calc x u * x v * (v⁻¹ * u⁻¹)
        = x u * x v * (u⁻¹ * v⁻¹) := by rw [mul_comm (v⁻¹) (u⁻¹)]
      _ = x u * (x v * (u⁻¹ * v⁻¹)) := by rw [mul_assoc]
      _ = x u * (u⁻¹ * (x v * v⁻¹)) := by
            rw [← mul_assoc (x v) (u⁻¹) (v⁻¹), mul_comm (x v) (u⁻¹), mul_assoc]
      _ = (x u * u⁻¹) * (x v * v⁻¹) := by rw [← mul_assoc]
  rw [h1]
  have hgen : x u * u⁻¹ ∈ commSub U X := Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩
  have hgenv : x v * v⁻¹ ∈ commSub V X := Subgroup.subset_closure ⟨x, hx, v, hv, rfl⟩
  exact (commSub U X ⊔ commSub V X).mul_mem (Subgroup.mem_sup_left hgen)
    (Subgroup.mem_sup_right hgenv)

private lemma s15_Three_commSub_top_stable {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ θ ∈ X, g * θ * g⁻¹ ∈ X) {r : W} (hr : r ∈ commSub (⊤ : Subgroup W) X) :
    g r ∈ commSub (⊤ : Subgroup W) X := by
  induction hr using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨θ, hθ, w, -, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨g * θ * g⁻¹, hg θ hθ, g w, Subgroup.mem_top _, ?_⟩
    simp [MulAut.mul_apply]
  | one => simp
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [map_inv]
    exact inv_mem hx

theorem s15_Three_transv_cases (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : InducesTransvection t ⊤) :
    ∃ c : W, c ≠ 1 ∧ t c = c ∧ (∀ u : W, t u = u ∨ t u = u * c) ∧
      commSub ⊤ (Subgroup.zpowers t) = Subgroup.zpowers c := by
  obtain ⟨-, hrt⟩ := ht
  set C : Subgroup W := commSub ⊤ (Subgroup.zpowers t) with hC
  have hcard : Nat.card C = 2 := by
    rw [card_eq_two_pow hW C, hrt]
    norm_num
  obtain ⟨c, hc1, hcu⟩ := (Nat.card_eq_two_iff' (1 : C)).1 hcard
  have hcne : (c : W) ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hc2 : (c : W) ^ 2 = 1 := hW _
  have hmemc : (c : W) ∈ C := c.2
  have hchar : ∀ x ∈ C, x = 1 ∨ x = (c : W) := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      have := hcu ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this
  have hstab : ∀ x ∈ C, t x ∈ C := by
    intro x hx
    refine s15_Three_commSub_top_stable (X := Subgroup.zpowers t) (g := t) (fun θ hθ => ?_) hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hθ
    have h : t * t ^ k * t⁻¹ = t ^ k := by group
    rw [h]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) k
  have htc : t (c : W) = (c : W) := by
    rcases hchar (t (c : W)) (hstab _ hmemc) with h | h
    · exact absurd (t.injective (h.trans (map_one t).symm)) hcne
    · exact h
  have hact : ∀ u : W, t u = u ∨ t u = u * c := by
    intro u
    have hmem : t u * u⁻¹ ∈ C := Subgroup.subset_closure
      ⟨t, Subgroup.mem_zpowers t, u, Subgroup.mem_top u, rfl⟩
    rcases hchar _ hmem with h | h
    · left
      exact mul_inv_eq_one.1 h
    · right
      have h' : t u * u⁻¹ = (c : W) := h
      calc t u = t u * u⁻¹ * u := by simp
        _ = (c : W) * u := by rw [h']
        _ = u * c := mul_comm _ _
  have hcardz : Nat.card (Subgroup.zpowers (c : W)) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc2 hcne]
  refine ⟨c, hcne, htc, hact, ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hmemc) (by
    rw [hcard, hcardz])).symm

theorem s15_Three_irr_inf_or_le {A : Subgroup (MulAut W)} {I X : Subgroup W}
    (hI : IsIrrOn A I ⊥) (hX : StableUnder A X) : I ⊓ X = ⊥ ∨ I ≤ X := by
  have hstable : StableUnder A (I ⊓ X) := fun a ha u hu =>
    ⟨hI.2.1 a ha u hu.1, hX a ha u hu.2⟩
  rcases hI.2.2.2 (I ⊓ X) hstable bot_le inf_le_left with h | h
  · exact Or.inl h
  · exact Or.inr (le_of_inf_eq h)

theorem s15_Three_exists_irr_le {A : Subgroup (MulAut W)} {X : Subgroup W}
    (hX : StableUnder A X) (h : X ≠ ⊥) : ∃ I : Subgroup W, I ≤ X ∧ IsIrrOn A I ⊥ := by
  classical
  let F : Set (Subgroup W) := {Y : Subgroup W | StableUnder A Y ∧ Y ≠ ⊥ ∧ Y ≤ X}
  have hFfin : F.Finite := Set.toFinite F
  obtain ⟨Y, hYset, hYmin⟩ := Set.exists_min_image F (fun Y => Nat.card Y) hFfin
    ⟨X, hX, h, le_rfl⟩
  obtain ⟨hYstab, hYne, hYX⟩ := hYset
  refine ⟨Y, hYX, ?_, hYstab, ?_, ?_⟩
  · exact lt_of_le_of_ne bot_le (Ne.symm hYne)
  · intro φ hφ u hu
    rw [Subgroup.mem_bot] at hu
    rw [hu, map_one]
    exact Subgroup.one_mem _
  · intro J hJstab _ hJY
    by_cases hJ : J = ⊥
    · exact Or.inl hJ
    · right
      have hJset : J ∈ F := ⟨hJstab, hJ, hJY.trans hYX⟩
      have hcard : Nat.card Y ≤ Nat.card J := hYmin J hJset
      exact Subgroup.eq_of_le_of_card_ge hJY hcard

theorem s15_Three_stableUnder_sSup {A : Subgroup (MulAut W)} {F : Set (Subgroup W)}
    (hF : ∀ X ∈ F, StableUnder A X) : StableUnder A (sSup F) := by
  intro φ hφ u hu
  rw [sSup_eq_iSup'] at hu ⊢
  refine Subgroup.iSup_induction (fun Y : F => (Y : Subgroup W))
    (C := fun z => φ z ∈ ⨆ Y : F, (Y : Subgroup W)) hu ?_ ?_ ?_
  · intro Y uY huY
    exact Subgroup.mem_iSup_of_mem Y (hF Y Y.2 φ hφ uY huY)
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro x y hx hy
    rw [map_mul]
    exact mul_mem hx hy

theorem s15_Three_stableUnder_sup {A : Subgroup (MulAut W)} {X Y : Subgroup W}
    (hX : StableUnder A X) (hY : StableUnder A Y) : StableUnder A (X ⊔ Y) := by
  intro φ hφ u hu
  rw [Subgroup.sup_eq_closure] at hu ⊢
  refine Subgroup.closure_induction
    (p := fun z _ => φ z ∈ Subgroup.closure ((X : Set W) ∪ (Y : Set W))) ?_ ?_ ?_ ?_ hu
  · rintro z (hz | hz)
    · exact Subgroup.subset_closure (Or.inl (hX φ hφ z hz))
    · exact Subgroup.subset_closure (Or.inr (hY φ hφ z hz))
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    rw [map_mul]
    exact mul_mem hx hy
  · intro x _ hx
    rw [map_inv]
    exact inv_mem hx

theorem s15_Three_sSup_irr_le {A : Subgroup (MulAut W)} (hsemi : s15Semisimple A)
    {X : Subgroup W} (hX : StableUnder A X) :
    sSup {I : Subgroup W | IsIrrOn A I ⊥ ∧ I ≤ X} = X := by
  set F : Set (Subgroup W) := {I : Subgroup W | IsIrrOn A I ⊥ ∧ I ≤ X} with hFdef
  have hFX : ∀ I ∈ F, I ≤ X := fun I hI => hI.2
  have hFstab : ∀ I ∈ F, StableUnder A I := fun I hI => hI.1.2.1
  have hYle : sSup F ≤ X := sSup_le hFX
  have hYstab : StableUnder A (sSup F) := s15_Three_stableUnder_sSup hFstab
  by_contra hne
  obtain ⟨X', hX'stab, hX'disj, hX'sup⟩ := hsemi (sSup F) hYstab
  have hZne : X ⊓ X' ≠ ⊥ := by
    intro hZ
    have h1 : X = sSup F := by
      have hmod := sup_inf_assoc_of_le (X' : Subgroup W) hYle
      rw [inf_comm] at hZ
      rw [hX'sup, top_inf_eq, hZ, sup_bot_eq] at hmod
      exact hmod
    exact hne h1.symm
  have hZstab : StableUnder A (X ⊓ X') := fun a ha u hu =>
    ⟨hX a ha u hu.1, hX'stab a ha u hu.2⟩
  obtain ⟨I, hIle, hIirr⟩ := s15_Three_exists_irr_le hZstab hZne
  have hIF : I ∈ F := ⟨hIirr, hIle.trans inf_le_left⟩
  have hIY : I ≤ sSup F := le_sSup hIF
  have hIX' : I ≤ X' := hIle.trans inf_le_right
  have hbot : I ≤ ⊥ := by
    have h1 : I ≤ X' ⊓ sSup F := le_inf hIX' hIY
    have h2 : X' ⊓ sSup F = ⊥ := by rw [inf_comm, hX'disj]
    exact h2 ▸ h1
  exact absurd (le_bot_iff.mp hbot) (ne_of_gt hIirr.1)

theorem s15_Three_comm_irr {A : Subgroup (MulAut W)} (hsemi : s15Semisimple A)
    (hcomm : commSub ⊤ A = ⊤) {I : Subgroup W} (hI : IsIrrOn A I ⊥) : commSub I A = I := by
  have hIle : commSub I A ≤ I := commSub_le_of_invariant hI.2.1
  obtain ⟨I', hI'stab, hI'disj, hI'sup⟩ := hsemi I hI.2.1
  have hsup : commSub I A ⊔ commSub I' A = ⊤ := by
    refine top_le_iff.mp ?_
    have h1 := s15_Three_commSub_sup_le I I' A
    rwa [hI'sup, hcomm] at h1
  have hle : I ≤ commSub I A ⊔ commSub I' A := hsup ▸ le_top
  have hI'le : commSub I' A ≤ I' := commSub_le_of_invariant hI'stab
  have hmod : (commSub I A ⊔ commSub I' A) ⊓ I = commSub I A ⊔ (commSub I' A ⊓ I) :=
    sup_inf_assoc_of_le (commSub I' A) hIle
  have hkey : commSub I A ⊔ (commSub I' A ⊓ I) = I := by
    rw [← hmod]
    exact inf_eq_right.2 hle
  have hbot : commSub I' A ⊓ I = ⊥ := by
    have h1 : commSub I' A ⊓ I ≤ I' ⊓ I := inf_le_inf hI'le le_rfl
    have h2 : I' ⊓ I = ⊥ := by rw [inf_comm, hI'disj]
    exact le_bot_iff.mp (h2 ▸ h1)
  rw [hbot, sup_bot_eq] at hkey
  exact hkey

theorem s15_Three_exists_irr_noncomm (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)}
    {t : MulAut W} (ht : InducesTransvection t ⊤) (hsemi : s15Semisimple A) :
    ∃ R : Subgroup W, IsIrrOn A R ⊥ ∧ commSub R (Subgroup.zpowers t) ≠ ⊥ := by
  by_contra h
  push Not at h
  have hfix : sSup {I : Subgroup W | IsIrrOn A I ⊥} ≤ fixV (Subgroup.zpowers t) := by
    refine sSup_le ?_
    intro I hI
    exact commSub_eq_bot_iff.mp (h I hI)
  have htop : sSup {I : Subgroup W | IsIrrOn A I ⊥} = ⊤ := by
    have := s15_Three_sSup_irr_le (A := A) hsemi (X := ⊤)
      (fun _ _ u hu => Subgroup.mem_top _)
    simpa using this
  have hle : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers t) := htop ▸ hfix
  have hbot : commSub ⊤ (Subgroup.zpowers t) = ⊥ :=
    commSub_eq_bot_iff.mpr hle
  have h1 : rk (commSub ⊤ (Subgroup.zpowers t)) = 1 := ht.2
  rw [hbot, rk_bot] at h1
  exact Nat.zero_ne_one h1

theorem s15_Three_stable_irr (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)}
    {t : MulAut W} (ht : InducesTransvection t ⊤) (htA : s15Normalizes t A) {S : Subgroup W}
    (hS : IsIrrOn A S ⊥) (hSc : commSub S A = S) : StableUnder (Subgroup.zpowers t) S := by
  obtain ⟨c, hc1, htc, hact, hcomm⟩ := s15_Three_transv_cases hW ht
  have hCcard : Nat.card (commSub ⊤ (Subgroup.zpowers t)) = 2 := by
    rw [hcomm, Nat.card_zpowers, orderOf_eq_prime (hW c) hc1]
  have ht2 : t * t = 1 := by
    ext u
    rcases hact u with h | h
    · simp [MulAut.mul_apply, h]
    · calc (t * t) u = t (t u) := rfl
        _ = t (u * c) := by rw [h]
        _ = t u * t c := by rw [map_mul]
        _ = (u * c) * c := by rw [h, htc]
        _ = u := by rw [mul_assoc, ← sq, hW c, mul_one]
  have htinv : t⁻¹ = t := by
    calc t⁻¹ = t⁻¹ * (t * t) := by rw [ht2, mul_one]
      _ = t := by group
  set S' : Subgroup W := S.map t.toMonoidHom with hS'def
  have hS'A : StableUnder A S' := by
    intro a ha u hu
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hu
    have ha' : t⁻¹ * a * t ∈ A := by
      refine (htA (t⁻¹ * a * t)).mpr ?_
      simpa [mul_assoc] using ha
    refine Subgroup.mem_map.2 ⟨(t⁻¹ * a * t) s, hS.2.1 _ ha' s hs, ?_⟩
    simp [MulAut.mul_apply]
  rcases s15_Three_irr_inf_or_le hS hS'A with hdisj | hle
  ·
    let φ : ↥S →* ↥(commSub ⊤ (Subgroup.zpowers t)) :=
      { toFun := fun u =>
          ⟨t (u : W) * (u : W)⁻¹,
            Subgroup.subset_closure
              ⟨t, Subgroup.mem_zpowers t, (u : W), Subgroup.mem_top _, rfl⟩⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun u v => by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
          calc t (u : W) * t (v : W) * ((v : W)⁻¹ * (u : W)⁻¹)
              = t (u : W) * t (v : W) * ((u : W)⁻¹ * (v : W)⁻¹) := by
                rw [mul_comm ((v : W)⁻¹) ((u : W)⁻¹)]
            _ = t (u : W) * (t (v : W) * ((u : W)⁻¹ * (v : W)⁻¹)) := by
                rw [mul_assoc]
            _ = t (u : W) * ((u : W)⁻¹ * (t (v : W) * (v : W)⁻¹)) := by
                rw [← mul_assoc (t (v : W)) ((u : W)⁻¹) ((v : W)⁻¹),
                  mul_comm (t (v : W)) ((u : W)⁻¹), mul_assoc]
            _ = (t (u : W) * (u : W)⁻¹) * (t (v : W) * (v : W)⁻¹) := by
                rw [← mul_assoc] }
    have hker : φ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [MonoidHom.mem_ker] at hu
      have htu : t (u : W) = (u : W) := by
        have h1 : t (u : W) * (u : W)⁻¹ = 1 := by
          have := congrArg (fun x : ↥(commSub ⊤ (Subgroup.zpowers t)) => (x : W)) hu
          simpa [φ] using this
        exact mul_inv_eq_one.1 h1
      have huS' : (u : W) ∈ S' := by
        rw [hS'def]
        exact Subgroup.mem_map.2 ⟨(u : W), u.2, htu⟩
      have hmem : (u : W) ∈ S ⊓ S' := ⟨u.2, huS'⟩
      rw [hdisj] at hmem
      exact Subtype.ext (Subgroup.mem_bot.1 hmem)
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
    have hcardS : Nat.card S ≤ 2 := by
      have := Nat.card_le_card_of_injective _ hinj
      rw [hCcard] at this
      exact this
    have hSne : S ≠ ⊥ := ne_of_gt hS.1
    have hcardS' : Nat.card S = 2 := by
      have h1 : 1 < Nat.card S := (Subgroup.one_lt_card_iff_ne_bot S).2 hSne
      omega
    obtain ⟨s, hs1, hsu⟩ := (Nat.card_eq_two_iff' (1 : S)).1 hcardS'
    have hcharS : ∀ x ∈ S, x = 1 ∨ x = (s : W) := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · right
        have := hsu ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
        exact congrArg Subtype.val this
    have hfix : S ≤ fixV A := by
      intro u hu a ha
      rcases hcharS _ hu with h | h
      · rw [h, map_one]
      · rw [h]
        rcases hcharS (a (s : W)) (hS.2.1 a ha (s : W) s.2) with h' | h'
        · have h'' : a (s : W) = a 1 := by rw [h', map_one]
          exact absurd (Subtype.ext (a.injective h'')) hs1
        · exact h'
    have hbot : commSub S A = ⊥ := commSub_eq_bot_iff.mpr hfix
    rw [hSc] at hbot
    exact absurd hbot hSne
  ·
    have hS'eq : S' = S := by
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      rw [hS'def, Subgroup.card_map_of_injective t.injective]
    have htS : ∀ u ∈ S, t u ∈ S := by
      intro u hu
      rw [← hS'eq, hS'def]
      exact Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    have ht_stab : t ∈ stabSub S := by
      rw [mem_stabSub]
      intro u
      constructor
      · intro hu
        have h1 : t (t u) ∈ S := htS (t u) hu
        rw [show t (t u) = u from by
          have := congrArg (fun f : MulAut W => f u) ht2
          simpa [MulAut.mul_apply] using this] at h1
        exact h1
      · exact htS u
    intro z hz u hu
    exact (mem_stabSub.1 ((Subgroup.zpowers_le.2 ht_stab) hz) u).2 hu

private lemma s15_Three_mem_zpowers_of_ne_bot {c : W} (hc1 : c ≠ 1) (hc2 : c ^ 2 = 1)
    {H : Subgroup W} (hH : H ≤ Subgroup.zpowers c) (hne : H ≠ ⊥) : c ∈ H := by
  have hcard : Nat.card (Subgroup.zpowers c) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc2 hc1]
  have hHcard : Nat.card H = 2 := by
    have hle : Nat.card H ≤ 2 := by
      have := Subgroup.card_le_of_le hH
      rw [hcard] at this
      exact this
    have hgt : 1 < Nat.card H := (Subgroup.one_lt_card_iff_ne_bot H).2 hne
    omega
  have heq : H = Subgroup.zpowers c := by
    refine Subgroup.eq_of_le_of_card_ge hH ?_
    rw [hcard, hHcard]
  rw [heq]
  exact Subgroup.mem_zpowers c

theorem s15_Three_split (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} {t : MulAut W}
    (ht : InducesTransvection t ⊤) (htA : s15Normalizes t A) (hsemi : s15Semisimple A)
    (hcomm : commSub ⊤ A = ⊤) :
    ∃ R S : Subgroup W, IsIrrOn A R ⊥ ∧ commSub R A = R ∧ StableUnder (Subgroup.zpowers t) R ∧
      StableUnder A S ∧ R ⊓ S = ⊥ ∧ R ⊔ S = ⊤ ∧
      S ≤ fixV (Subgroup.zpowers t) ∧ commSub R (Subgroup.zpowers t) ≠ ⊥ ∧
      ∀ I : Subgroup W, IsIrrOn A I ⊥ → I ≠ R → I ≤ S := by
  obtain ⟨c, hc1, htc, hact, hcommt⟩ := s15_Three_transv_cases hW ht
  obtain ⟨R, hR, hRt⟩ := s15_Three_exists_irr_noncomm hW ht hsemi
  have hRA : commSub R A = R := s15_Three_comm_irr hsemi hcomm hR
  have hRtstab : StableUnder (Subgroup.zpowers t) R :=
    s15_Three_stable_irr hW ht htA hR hRA
  have hcommle : commSub R (Subgroup.zpowers t) ≤ Subgroup.zpowers c := by
    rw [← hcommt]
    exact commSub_mono le_top le_rfl
  have hcR : c ∈ R :=
    commSub_le_of_invariant hRtstab
      (s15_Three_mem_zpowers_of_ne_bot (H := commSub R (Subgroup.zpowers t))
        hc1 (hW c) hcommle hRt)
  let S : Subgroup W :=
    sSup {I : Subgroup W | IsIrrOn A I ⊥ ∧ commSub I (Subgroup.zpowers t) = ⊥}
  have hSstab : StableUnder A S := by
    refine s15_Three_stableUnder_sSup ?_
    intro I hI
    exact hI.1.2.1
  have hSfix : S ≤ fixV (Subgroup.zpowers t) := by
    refine sSup_le ?_
    intro I hI
    exact commSub_eq_bot_iff.mp hI.2
  have hRS : R ⊓ S = ⊥ := by
    rcases s15_Three_irr_inf_or_le hR hSstab with h | h
    · exact h
    · exfalso
      exact hRt (commSub_eq_bot_iff.mpr (h.trans hSfix))
  have hRStop : R ⊔ S = ⊤ := by
    by_contra hne
    obtain ⟨X', hX'stab, hX'disj, hX'sup⟩ :=
      hsemi (R ⊔ S) (s15_Three_stableUnder_sup hR.2.1 hSstab)
    by_cases hX' : X' = ⊥
    · rw [hX', sup_bot_eq] at hX'sup
      exact hne hX'sup
    · obtain ⟨I, hIle, hIirr⟩ := s15_Three_exists_irr_le hX'stab hX'
      have hIA : commSub I A = I := s15_Three_comm_irr hsemi hcomm hIirr
      have hIstab : StableUnder (Subgroup.zpowers t) I :=
        s15_Three_stable_irr hW ht htA hIirr hIA
      have hItbot : commSub I (Subgroup.zpowers t) = ⊥ := by
        refine le_bot_iff.mp ?_
        have hle1 : commSub I (Subgroup.zpowers t) ≤ I :=
          commSub_le_of_invariant hIstab
        have hle2 : commSub I (Subgroup.zpowers t) ≤ Subgroup.zpowers c := by
          rw [← hcommt]
          exact commSub_mono le_top le_rfl
        have hcX : c ∈ R ⊔ S := Subgroup.mem_sup_left hcR
        have hIc : Subgroup.zpowers c ≤ R ⊔ S := Subgroup.zpowers_le.2 hcX
        have h1 : I ⊓ Subgroup.zpowers c ≤ X' ⊓ (R ⊔ S) := inf_le_inf hIle hIc
        have h2 : X' ⊓ (R ⊔ S) = ⊥ := by rw [inf_comm, hX'disj]
        exact (le_inf hle1 hle2).trans (h2 ▸ h1)
      have hIS : I ≤ S := le_sSup ⟨hIirr, hItbot⟩
      have hIbot : I ≤ ⊥ := by
        have h1 : I ≤ X' ⊓ (R ⊔ S) := le_inf hIle (hIS.trans le_sup_right)
        have h2 : X' ⊓ (R ⊔ S) = ⊥ := by rw [inf_comm, hX'disj]
        exact h2 ▸ h1
      exact absurd (le_bot_iff.mp hIbot) hIirr.1.ne'
  have hmult : ∀ I : Subgroup W, IsIrrOn A I ⊥ → I ≠ R → I ≤ S := by
    intro I hI hne
    by_contra hnot
    have hItne : commSub I (Subgroup.zpowers t) ≠ ⊥ := by
      intro hbot
      exact hnot (le_sSup ⟨hI, hbot⟩)
    have hcommleI : commSub I (Subgroup.zpowers t) ≤ Subgroup.zpowers c := by
      rw [← hcommt]
      exact commSub_mono le_top le_rfl
    have hIA : commSub I A = I := s15_Three_comm_irr hsemi hcomm hI
    have hIstab : StableUnder (Subgroup.zpowers t) I :=
      s15_Three_stable_irr hW ht htA hI hIA
    have hcI : c ∈ I :=
      commSub_le_of_invariant hIstab
        (s15_Three_mem_zpowers_of_ne_bot (H := commSub I (Subgroup.zpowers t))
          hc1 (hW c) hcommleI hItne)
    have hinf : I ⊓ R ≠ ⊥ := by
      intro h
      have hmem : c ∈ I ⊓ R := ⟨hcI, hcR⟩
      rw [h] at hmem
      exact hc1 (Subgroup.mem_bot.1 hmem)
    rcases s15_Three_irr_inf_or_le hI hR.2.1 with h | h
    · exact absurd h hinf
    · have hIR : I = R := by
        rcases hR.2.2.2 I hI.2.1 bot_le h with hzero | heq
        · exact absurd hzero hI.1.ne'
        · exact heq
      exact hne hIR
  exact ⟨R, S, hR, hRA, hRtstab, hSstab, hRS, hRStop, hSfix, hRt, hmult⟩

private lemma s15_Three_commSub_map_conj (U : Subgroup W) (Y : Subgroup (MulAut W))
    (α : MulAut W) :
    commSub (U.map α.toMonoidHom) (Y.map (MulAut.conj α).toMonoidHom) =
      (commSub U Y).map α.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    refine ⟨x₀ w₀ * w₀⁻¹, ⟨x₀, hx₀, w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x₀, hx₀, w₀, hw₀, rfl⟩ := hs
    refine ⟨MulAut.conj α x₀, ⟨x₀, hx₀, rfl⟩, α w₀, ⟨w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]

private lemma s15_Three_map_sSup_eq (α : MulAut W) (F : Set (Subgroup W)) :
    (sSup F).map α.toMonoidHom = sSup ((Subgroup.map α.toMonoidHom) '' F) := by
  rw [sSup_eq_iSup' F, Subgroup.map_iSup, sSup_eq_iSup']
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro I
    exact le_iSup_of_le ⟨I.1.map α.toMonoidHom, ⟨I.1, I.2, rfl⟩⟩ le_rfl
  · refine iSup_le ?_
    intro J
    obtain ⟨I, hI, hJ⟩ := J.2
    rw [← hJ]
    exact le_iSup_of_le ⟨I, hI⟩ le_rfl

theorem s15_Three_commSub_conj (n : MulAut W) (X : Subgroup (MulAut W)) :
    commSub ⊤ (X.map (MulAut.conj n).toMonoidHom) = (commSub ⊤ X).map n.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, -, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    refine ⟨x₀ (n⁻¹ w) * (n⁻¹ w)⁻¹, ⟨x₀, hx₀, n⁻¹ w, trivial, rfl⟩, ?_⟩
    change n (x₀ (n⁻¹ w) * (n⁻¹ w)⁻¹) = (MulAut.conj n x₀) w * w⁻¹
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.apply_inv_self, map_mul, map_inv]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x₀, hx₀, v, -, rfl⟩ := hs
    refine ⟨MulAut.conj n x₀, ⟨x₀, hx₀, rfl⟩, n v, trivial, ?_⟩
    change (MulAut.conj n x₀) (n v) * (n v)⁻¹ = n (x₀ v * v⁻¹)
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.inv_apply_self,
      map_mul, map_inv]

theorem s15_Three_secIso_trivial {A X : Subgroup (MulAut W)} (hXA : X ≤ A) {I I' : Subgroup W}
    (hI : StableUnder A I) (hiso : s15SecIso A I ⊥ I' ⊥)
    (hX' : ∀ b ∈ X, ∀ u ∈ I', b u = u) : ∀ b ∈ X, ∀ u ∈ I, b u = u := by
  obtain ⟨β, hsurj, hker, hequiv⟩ := hiso
  have hinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥I) : W) ∈ (⊥ : Subgroup W) := (hker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  intro b hb u hu
  obtain ⟨u', hu'⟩ := QuotientGroup.mk_surjective (β ⟨u, hu⟩)
  have hbu : b (u' : W) = (u' : W) := hX' b hb (u' : W) u'.2
  have hbu' : b (u' : W) ∈ I' := by rw [hbu]; exact u'.2
  have heq := hequiv b (hXA hb) ⟨u, hu⟩ u' (hI b (hXA hb) u hu) hbu' hu'.symm
  have hmk : QuotientGroup.mk ⟨b (u' : W), hbu'⟩ = β ⟨u, hu⟩ := by
    rw [show QuotientGroup.mk ⟨b (u' : W), hbu'⟩ = QuotientGroup.mk u' from
      congrArg QuotientGroup.mk (Subtype.ext hbu), hu']
  have hsub : (⟨b u, hI b (hXA hb) u hu⟩ : ↥I) = ⟨u, hu⟩ :=
    hinj (heq.trans hmk)
  exact congrArg Subtype.val hsub

private lemma s15_Three_irr_map_of_normalizes {α : MulAut W} {A : Subgroup (MulAut W)}
    (hαA : ∀ a : MulAut W, a ∈ A ↔ α * a * α⁻¹ ∈ A)
    {I : Subgroup W} (hI : IsIrrOn A I ⊥) :
    IsIrrOn A (I.map α.toMonoidHom) ⊥ := by
  have hcomp : (α⁻¹).toMonoidHom.comp α.toMonoidHom = MonoidHom.id W := by
    ext w; simp
  have hcomp2 : α.toMonoidHom.comp (α⁻¹).toMonoidHom = MonoidHom.id W := by
    ext w; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne bot_le (Ne.symm ?_)
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    obtain ⟨i, hi⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hI.1.ne'
    refine ⟨⟨α i, Subgroup.mem_map.2 ⟨i, i.2, rfl⟩⟩, ?_⟩
    intro h
    have hval : α i = 1 := congrArg Subtype.val h
    exact hi (Subtype.ext (α.injective (hval.trans (map_one α).symm)))
  · intro a ha u hu
    obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.1 hu
    have hβ : α⁻¹ * a * α ∈ A := (hαA (α⁻¹ * a * α)).mpr (by simpa [mul_assoc] using ha)
    exact Subgroup.mem_map.2 ⟨(α⁻¹ * a * α) i, hI.2.1 _ hβ i hi, by simp [MulAut.mul_apply]⟩
  · intro a ha u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro K hKstable hbotK hKI
    have hK'I : K.map (α⁻¹).toMonoidHom ≤ I := by
      have h := Subgroup.map_mono (f := (α⁻¹).toMonoidHom) hKI
      rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h
    have hK'stable : StableUnder A (K.map (α⁻¹).toMonoidHom) := by
      intro a ha k hk
      obtain ⟨k0, hk0, rfl⟩ := Subgroup.mem_map.1 hk
      have hβ : α * a * α⁻¹ ∈ A := (hαA a).mp ha
      exact Subgroup.mem_map.2
        ⟨(α * a * α⁻¹) k0, hKstable _ hβ k0 hk0, by simp [MulAut.mul_apply]⟩
    rcases hI.2.2.2 _ hK'stable bot_le hK'I with hzero | heq
    · left
      have hK' : (K.map (α⁻¹).toMonoidHom).map α.toMonoidHom = K := by
        rw [Subgroup.map_map, hcomp2, Subgroup.map_id]
      rw [← hK', hzero, Subgroup.map_bot]
    · right
      have hK' : (K.map (α⁻¹).toMonoidHom).map α.toMonoidHom = K := by
        rw [Subgroup.map_map, hcomp2, Subgroup.map_id]
      rw [← hK', heq]

section Assemble

variable {A N : Subgroup (MulAut W)} {R S : Subgroup W} {B : Subgroup (MulAut W)}
  (hNA : ∀ n ∈ N, ∀ a : MulAut W, a ∈ A ↔ n * a * n⁻¹ ∈ A) (hsemi : s15Semisimple A)
  (htrans : ∀ I I' : Subgroup W, IsIrrOn A I ⊥ → IsIrrOn A I' ⊥ →
    ∃ n ∈ N, s15SecIso A (I.map (n : MulAut W).toMonoidHom) ⊥ I' ⊥)
  (hR : IsIrrOn A R ⊥) (hS : StableUnder A S) (hRS : R ⊓ S = ⊥) (hRS' : R ⊔ S = ⊤)
  (hmult : ∀ I : Subgroup W, IsIrrOn A I ⊥ → I ≠ R → I ≤ S)
  (hBA : B ≤ A) (hBS : ∀ s ∈ S, ∀ b ∈ B, b s = s)
  (hAB : ∀ a ∈ A, ∃ b ∈ B, ∀ r ∈ R, a r = b r) (hBR : commSub ⊤ B = R)

include hNA in
theorem s15_Three_irr_map {n : MulAut W} (hn : n ∈ N) {I : Subgroup W} (hI : IsIrrOn A I ⊥) :
    IsIrrOn A (I.map (n : MulAut W).toMonoidHom) ⊥ :=
  s15_Three_irr_map_of_normalizes (fun a => hNA n hn a) hI

include hsemi hR hS hRS hmult in
theorem s15_Three_S_eq : S = sSup {I : Subgroup W | IsIrrOn A I ⊥ ∧ I ≠ R} := by
  have hset : {I : Subgroup W | IsIrrOn A I ⊥ ∧ I ≠ R} =
      {I : Subgroup W | IsIrrOn A I ⊥ ∧ I ≤ S} := by
    ext I
    constructor
    · rintro ⟨hI, hne⟩
      exact ⟨hI, hmult I hI hne⟩
    · rintro ⟨hI, hIS⟩
      refine ⟨hI, ?_⟩
      intro hIR
      have hRleS : R ≤ S := hIR ▸ hIS
      have hbot : R = ⊥ := by rw [← hRS, inf_eq_left.mpr hRleS]
      exact hR.1.ne' hbot
  rw [hset]
  exact (s15_Three_sSup_irr_le hsemi hS).symm

include hNA hsemi hR hS hRS hRS' hmult hBA hBS hAB hBR in
theorem s15_Three_conj_B {k : MulAut W} (hk : k ∈ N) (hkR : R.map k.toMonoidHom = R) :
    B.map (MulAut.conj k).toMonoidHom = B := by
  have hS_eq : S = sSup {I : Subgroup W | IsIrrOn A I ⊥ ∧ I ≠ R} :=
    s15_Three_S_eq hsemi hR hS hRS hmult
  have hmap_le : ∀ m : MulAut W, m ∈ N → R.map m.toMonoidHom = R →
      S.map m.toMonoidHom ≤ S := by
    intro m hm hmR
    rw [hS_eq, s15_Three_map_sSup_eq]
    refine sSup_le ?_
    rintro J ⟨I, hI, rfl⟩
    have hIr : IsIrrOn A (I.map m.toMonoidHom) ⊥ := s15_Three_irr_map hNA hm hI.1
    have hne : I.map m.toMonoidHom ≠ R := by
      intro h
      have hcomp : (m⁻¹).toMonoidHom.comp m.toMonoidHom = MonoidHom.id W := by
        ext w; simp
      have h1 : (I.map m.toMonoidHom).map (m⁻¹).toMonoidHom =
          R.map (m⁻¹).toMonoidHom := by rw [h]
      rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h1
      have hmRinv : R.map (m⁻¹).toMonoidHom = R := by
        have := congrArg (Subgroup.map (m⁻¹).toMonoidHom) hmR
        rw [Subgroup.map_map, hcomp, Subgroup.map_id] at this
        exact this.symm
      rw [hmRinv] at h1
      exact hI.2 h1
    exact le_sSup ⟨hIr, hne⟩
  have hkSle : S.map k.toMonoidHom ≤ S := hmap_le k hk hkR
  have hkRinv : R.map (k⁻¹).toMonoidHom = R := by
    have hcomp : (k⁻¹).toMonoidHom.comp k.toMonoidHom = MonoidHom.id W := by
      ext w; simp
    have := congrArg (Subgroup.map (k⁻¹).toMonoidHom) hkR
    rw [Subgroup.map_map, hcomp, Subgroup.map_id] at this
    exact this.symm
  have hkS : S.map k.toMonoidHom = S := by
    refine le_antisymm hkSle ?_
    have h := Subgroup.map_mono (f := k.toMonoidHom) (hmap_le k⁻¹ (N.inv_mem hk) hkRinv)
    have hcomp : k.toMonoidHom.comp (k⁻¹).toMonoidHom = MonoidHom.id W := by
      ext w; simp
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h
  have hCA : B.map (MulAut.conj k).toMonoidHom ≤ A := by
    rintro c ⟨b, hb, rfl⟩
    exact (hNA k hk b).mp (hBA hb)
  have htrivS : ∀ c ∈ B.map (MulAut.conj k).toMonoidHom, ∀ s ∈ S, c s = s := by
    intro c hc s hs
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hc
    have hks : k⁻¹ s ∈ S := by
      have hmem : s ∈ S.map k.toMonoidHom := by rw [hkS]; exact hs
      obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.1 hmem
      have hst : k⁻¹ s = t := by
        rw [← hts]
        simp
      rw [hst]
      exact ht
    calc (MulAut.conj k b) s = k (b (k⁻¹ s)) := by
          simp [MulAut.conj_apply, MulAut.mul_apply]
      _ = s := by
          rw [hBS _ hks b hb]
          simp
  have hle : B.map (MulAut.conj k).toMonoidHom ≤ B := by
    intro x hx
    have hxA : x ∈ A := hCA hx
    obtain ⟨b, hb, hbR⟩ := hAB x hxA
    have hxS : ∀ s ∈ S, x s = s := fun s hs => htrivS x hx s hs
    have heq : x = b := by
      ext w
      have hw : w ∈ R ⊔ S := by rw [hRS']; exact Subgroup.mem_top w
      obtain ⟨r, hr, s, hs, rfl⟩ := Subgroup.mem_sup.1 hw
      rw [map_mul, map_mul, hbR r hr, hBS s hs b hb, hxS s hs]
    rw [heq]
    exact hb
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]

include hNA hsemi hR hS hRS hmult hBA hBS hAB hBR in
theorem s15_Three_conj_le_S {n : MulAut W} (hn : n ∈ N) (hne : R.map n.toMonoidHom ≠ R) :
    R ≤ S.map n.toMonoidHom := by
  have hcomp : n.toMonoidHom.comp (n⁻¹).toMonoidHom = MonoidHom.id W := by
    ext w; simp
  have hIr : IsIrrOn A (R.map (n⁻¹).toMonoidHom) ⊥ :=
    s15_Three_irr_map hNA (N.inv_mem hn) hR
  have hneR : R.map (n⁻¹).toMonoidHom ≠ R := by
    intro h
    apply hne
    have := congrArg (Subgroup.map n.toMonoidHom) h
    rw [Subgroup.map_map, hcomp, Subgroup.map_id] at this
    exact this.symm
  have hle : R.map (n⁻¹).toMonoidHom ≤ S := hmult _ hIr hneR
  have hmap := Subgroup.map_mono (f := n.toMonoidHom) hle
  have hcomp2 : n.toMonoidHom.comp (n⁻¹).toMonoidHom = MonoidHom.id W := by
    ext w; simp
  rwa [Subgroup.map_map, hcomp2, Subgroup.map_id] at hmap

private lemma s15_Three_conj_trivial_on_map_S
    (hBS : ∀ s ∈ S, ∀ b ∈ B, b s = s) {n : MulAut W} :
    ∀ c ∈ B.map (MulAut.conj n).toMonoidHom, ∀ u ∈ S.map n.toMonoidHom, c u = u := by
  intro c hc u hu
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hc
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hu
  calc (MulAut.conj n b) (n s) = n (b (n⁻¹ (n s))) := by
        simp [MulAut.conj_apply, MulAut.mul_apply]
    _ = n (b s) := by simp
    _ = n s := by rw [hBS s hs b hb]

include hNA hsemi hR hS hRS hRS' hmult hBA hBS hAB hBR in
theorem s15_Three_comm_conj {n : MulAut W} (hn : n ∈ N) (hne : R.map n.toMonoidHom ≠ R) :
    ⁅B, B.map (MulAut.conj n).toMonoidHom⁆ = ⊥ := by
  have hRle : R ≤ S.map n.toMonoidHom :=
    s15_Three_conj_le_S hNA hsemi hR hS hRS hmult hBA hBS hAB hBR hn hne
  have hCA : B.map (MulAut.conj n).toMonoidHom ≤ A := by
    rintro c ⟨b, hb, rfl⟩
    exact (hNA n hn b).mp (hBA hb)
  have hCS : StableUnder (B.map (MulAut.conj n).toMonoidHom) S :=
    fun c hc s hs => hS c (hCA hc) s hs
  have hBRstab : StableUnder B R := fun b hb r hr => hR.2.1 b (hBA hb) r hr
  have hCRstab : StableUnder (B.map (MulAut.conj n).toMonoidHom) R :=
    fun c hc r hr => hR.2.1 c (hCA hc) r hr
  have hCR : ∀ c ∈ B.map (MulAut.conj n).toMonoidHom, ∀ r ∈ R, c r = r :=
    fun c hc r hr => s15_Three_conj_trivial_on_map_S hBS c hc r (hRle hr)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  ext w
  have hw : w ∈ R ⊔ S := by rw [hRS']; exact Subgroup.mem_top w
  obtain ⟨r, hr, s, hs, rfl⟩ := Subgroup.mem_sup.1 hw
  calc c (b (r * s)) = c (b r * b s) := by rw [map_mul]
    _ = c (b r) * c (b s) := by rw [map_mul]
    _ = c (b r) * c s := by rw [hBS s hs b hb]
    _ = b r * c s := by rw [hCR c hc (b r) (hBRstab b hb r hr)]
    _ = b (r * c s) := by rw [map_mul, hBS (c s) (hCS c hc s hs) b hb]
    _ = b (c r * c s) := by rw [hCR c hc r hr]
    _ = b (c (r * s)) := by rw [← map_mul]

include hNA hR hmult in
private lemma s15_Three_conj_le_map_S {m n : MulAut W} (hm : m ∈ N) (hn : n ∈ N)
    (hne : R.map m.toMonoidHom ≠ R.map n.toMonoidHom) :
    R.map m.toMonoidHom ≤ S.map n.toMonoidHom := by
  have hk : n⁻¹ * m ∈ N := N.mul_mem (N.inv_mem hn) hm
  have hIr : IsIrrOn A (R.map (n⁻¹ * m).toMonoidHom) ⊥ := s15_Three_irr_map hNA hk hR
  have hneR : R.map (n⁻¹ * m).toMonoidHom ≠ R := by
    intro h
    apply hne
    have hcomp : n.toMonoidHom.comp (n⁻¹ * m).toMonoidHom = m.toMonoidHom := by
      ext w; simp [mul_assoc]
    have := congrArg (Subgroup.map n.toMonoidHom) h
    rw [Subgroup.map_map, hcomp] at this
    exact this
  have hle : R.map (n⁻¹ * m).toMonoidHom ≤ S := hmult _ hIr hneR
  have hmap := Subgroup.map_mono (f := n.toMonoidHom) hle
  have hcomp : n.toMonoidHom.comp (n⁻¹ * m).toMonoidHom = m.toMonoidHom := by
    ext w; simp [mul_assoc]
  rwa [Subgroup.map_map, hcomp] at hmap

include hNA hsemi htrans hR hS hRS hRS' hmult hBA hBS hAB hBR in
theorem s15_Three_sSup_conj :
    sSup {Z : Subgroup W | ∃ n ∈ N, Z = R.map n.toMonoidHom} = ⊤ := by
  set T : Set (Subgroup W) := {Z | ∃ n ∈ N, Z = R.map n.toMonoidHom}
  have hTstab : StableUnder A (sSup T) := by
    refine s15_Three_stableUnder_sSup ?_
    rintro Z ⟨n, hn, rfl⟩
    exact (s15_Three_irr_map hNA hn hR).2.1
  by_contra hne
  obtain ⟨X', hX'stab, hX'disj, hX'sup⟩ := hsemi (sSup T) hTstab
  have hX'ne : X' ≠ ⊥ := by
    intro h
    apply hne
    rw [h, sup_bot_eq] at hX'sup
    exact hX'sup
  obtain ⟨I, hIle, hIirr⟩ := s15_Three_exists_irr_le hX'stab hX'ne
  obtain ⟨n, hn, hiso⟩ := htrans R I hR hIirr
  have hcomp : n.toMonoidHom.comp (n⁻¹).toMonoidHom = MonoidHom.id W := by
    ext w; simp
  have hI_ne : I ≠ R.map n.toMonoidHom := by
    intro h
    have hIsup : I ≤ sSup T := by rw [h]; exact le_sSup ⟨n, hn, rfl⟩
    have h1 : I ≤ X' ⊓ sSup T := le_inf hIle hIsup
    have h2 : X' ⊓ sSup T = ⊥ := by rw [inf_comm, hX'disj]
    exact hIirr.1.ne' (le_bot_iff.mp (h2 ▸ h1))
  have hIleS : I ≤ S.map n.toMonoidHom := by
    have hIr : IsIrrOn A (I.map (n⁻¹).toMonoidHom) ⊥ :=
      s15_Three_irr_map hNA (N.inv_mem hn) hIirr
    have hneR : I.map (n⁻¹).toMonoidHom ≠ R := by
      intro h
      apply hI_ne
      have := congrArg (Subgroup.map n.toMonoidHom) h
      rw [Subgroup.map_map, hcomp, Subgroup.map_id] at this
      exact this
    have hle := hmult _ hIr hneR
    have hmap := Subgroup.map_mono (f := n.toMonoidHom) hle
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at hmap
  have hCA : B.map (MulAut.conj n).toMonoidHom ≤ A := by
    rintro c ⟨b, hb, rfl⟩
    exact (hNA n hn b).mp (hBA hb)
  have hCtrivI : ∀ c ∈ B.map (MulAut.conj n).toMonoidHom, ∀ u ∈ I, c u = u :=
    fun c hc u hu => s15_Three_conj_trivial_on_map_S hBS c hc u (hIleS hu)
  have htrivR : ∀ c ∈ B.map (MulAut.conj n).toMonoidHom,
      ∀ u ∈ R.map n.toMonoidHom, c u = u :=
    s15_Three_secIso_trivial hCA (s15_Three_irr_map hNA hn hR).2.1 hiso hCtrivI
  have hcommRB : commSub R B = R := by
    have h1 : commSub ⊤ B ≤ commSub R B ⊔ commSub S B := by
      rw [← hRS']
      exact s15_Three_commSub_sup_le R S B
    rw [hBR] at h1
    have h2 : commSub S B = ⊥ := commSub_eq_bot_iff.mpr hBS
    rw [h2, sup_bot_eq] at h1
    exact le_antisymm
      (commSub_le_of_invariant fun b hb r hr => hR.2.1 b (hBA hb) r hr) h1
  have hcommC : commSub (R.map n.toMonoidHom) (B.map (MulAut.conj n).toMonoidHom) =
      R.map n.toMonoidHom := by
    rw [s15_Three_commSub_map_conj R B n, hcommRB]
  have hbot : commSub (R.map n.toMonoidHom) (B.map (MulAut.conj n).toMonoidHom) = ⊥ :=
    commSub_eq_bot_iff.mpr (fun u hu c hc => htrivR c hc u hu)
  rw [hcommC] at hbot
  have hRne : R.map n.toMonoidHom ≠ ⊥ := by
    intro h
    have hcomp2 : (n⁻¹).toMonoidHom.comp n.toMonoidHom = MonoidHom.id W := by
      ext w; simp
    have := congrArg (Subgroup.map (n⁻¹).toMonoidHom) h
    rw [Subgroup.map_map, hcomp2, Subgroup.map_id, Subgroup.map_bot] at this
    exact hR.1.ne' this
  exact hRne hbot

include hNA hsemi htrans hR hS hRS hRS' hmult hBA hBS hAB hBR in
theorem s15_Three_indep :
    sSupIndep {Z : Subgroup W | ∃ n ∈ N, Z = R.map n.toMonoidHom} := by
  intro Y hY
  obtain ⟨n, hn, rfl⟩ := hY
  rw [disjoint_iff]
  have hle : sSup ({Z : Subgroup W | ∃ m ∈ N, Z = R.map m.toMonoidHom} \
      {R.map n.toMonoidHom}) ≤ S.map n.toMonoidHom := by
    refine sSup_le ?_
    intro Z hZ
    obtain ⟨m, hm, rfl⟩ := hZ.1
    have hZY : R.map m.toMonoidHom ≠ R.map n.toMonoidHom := by
      intro h
      exact hZ.2 (by simpa [h])
    exact s15_Three_conj_le_map_S hNA hR hmult hm hn hZY
  have hdisj : R.map n.toMonoidHom ⊓ S.map n.toMonoidHom = ⊥ := by
    rw [← Subgroup.map_inf R S n.toMonoidHom n.injective, hRS, Subgroup.map_bot]
  have h1 : R.map n.toMonoidHom ⊓
      sSup ({Z : Subgroup W | ∃ m ∈ N, Z = R.map m.toMonoidHom} \
        {R.map n.toMonoidHom}) ≤ ⊥ :=
    (inf_le_inf le_rfl hle).trans (by rw [hdisj])
  exact le_bot_iff.mp h1

include hNA hsemi htrans hR hS hRS hRS' hmult hBA hBS hAB hBR in
theorem s15_Three_gen : (⨆ Y ∈ conjSet B N, Y) = A := by
  classical
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro Y
    refine iSup_le ?_
    rintro ⟨n, hn, rfl⟩
    rintro b ⟨b₀, hb₀, rfl⟩
    exact (hNA n hn b₀).mp (hBA hb₀)
  · intro a ha
    set T : Set (Subgroup W) := {Z | ∃ n ∈ N, Z = R.map n.toMonoidHom}
    have hTfin : T.Finite := Set.toFinite T
    let nOf : T → MulAut W := fun Z => Classical.choose Z.2
    have hnOf : ∀ Z : T, nOf Z ∈ N := fun Z => (Classical.choose_spec Z.2).1
    have hZOf : ∀ Z : T, R.map (nOf Z).toMonoidHom = Z.1 :=
      fun Z => (Classical.choose_spec Z.2).2.symm
    have hconjA : ∀ Z : T, (nOf Z)⁻¹ * a * nOf Z ∈ A := by
      intro Z
      exact (hNA (nOf Z) (hnOf Z) ((nOf Z)⁻¹ * a * nOf Z)).mpr
        (by simpa [mul_assoc] using ha)
    let bOf : T → MulAut W :=
      fun Z => Classical.choose (hAB ((nOf Z)⁻¹ * a * nOf Z) (hconjA Z))
    have hbOf : ∀ Z : T, bOf Z ∈ B :=
      fun Z => (Classical.choose_spec (hAB ((nOf Z)⁻¹ * a * nOf Z) (hconjA Z))).1
    have hbOfR : ∀ Z : T, ∀ r ∈ R,
        ((nOf Z)⁻¹ * a * nOf Z) r = bOf Z r :=
      fun Z => (Classical.choose_spec (hAB ((nOf Z)⁻¹ * a * nOf Z) (hconjA Z))).2
    let gOf : T → MulAut W := fun Z => MulAut.conj (nOf Z) (bOf Z)
    have hgOf_a : ∀ Z : T, ∀ z ∈ Z.1, gOf Z z = a z := by
      intro Z z hz
      have hz' : z ∈ R.map (nOf Z).toMonoidHom := by rwa [hZOf Z]
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hz'
      have h1 : ((nOf Z)⁻¹ * a * nOf Z) r = bOf Z r := hbOfR Z r hr
      calc gOf Z (nOf Z r) = nOf Z (bOf Z r) := by
            simp [gOf, MulAut.conj_apply, MulAut.mul_apply]
        _ = nOf Z (((nOf Z)⁻¹ * a * nOf Z) r) := by rw [h1]
        _ = a (nOf Z r) := by simp [MulAut.mul_apply]
    have hgOf_triv : ∀ Z W : T, W ≠ Z → ∀ w ∈ W.1, gOf Z w = w := by
      intro Z W hneWZ w hw
      have hneR : R.map (nOf W).toMonoidHom ≠ R.map (nOf Z).toMonoidHom := by
        intro h
        apply hneWZ
        apply Subtype.ext
        rw [← hZOf W, ← hZOf Z, h]
      have hle : R.map (nOf W).toMonoidHom ≤ S.map (nOf Z).toMonoidHom :=
        s15_Three_conj_le_map_S hNA hR hmult (hnOf W) (hnOf Z) hneR
      have hw' : w ∈ S.map (nOf Z).toMonoidHom := hle (by rwa [← hZOf W] at hw)
      exact s15_Three_conj_trivial_on_map_S hBS (gOf Z)
        (Subgroup.mem_map.2 ⟨bOf Z, hbOf Z, rfl⟩) w hw'
    have hgOf_mem : ∀ Z : T, gOf Z ∈ (⨆ Y ∈ conjSet B N, Y) := by
      intro Z
      refine Subgroup.mem_iSup_of_mem (B.map (MulAut.conj (nOf Z)).toMonoidHom) ?_
      refine Subgroup.mem_iSup_of_mem ⟨nOf Z, hnOf Z, rfl⟩ ?_
      exact Subgroup.mem_map.2 ⟨bOf Z, hbOf Z, rfl⟩
    let s : Finset (Subgroup W) := hTfin.toFinset
    have hs : ∀ Z : Subgroup W, Z ∈ s ↔ Z ∈ T := fun Z => hTfin.mem_toFinset
    have aux : ∀ F : Finset (Subgroup W), F ⊆ s →
        ∃ x ∈ (⨆ Y ∈ conjSet B N, Y),
          (∀ Z ∈ F, ∀ z ∈ Z, x z = a z) ∧
          (∀ Z ∈ s, Z ∉ F → ∀ z ∈ Z, x z = z) := by
      intro F
      induction F using Finset.induction_on with
      | empty =>
        intro _
        refine ⟨1, Subgroup.one_mem _, ?_, ?_⟩
        · intro Z hZ
          simp at hZ
        · intro Z hZ _ z hz
          rfl
      | insert Z F hZF ih =>
        intro hsub
        have hFsub : F ⊆ s := fun W hW => hsub (Finset.mem_insert_of_mem hW)
        obtain ⟨x, hxmem, hxagree, hxtriv⟩ := ih hFsub
        have hZs : Z ∈ s := hsub (Finset.mem_insert_self Z F)
        let Zt : T := ⟨Z, (hs Z).1 hZs⟩
        refine ⟨gOf Zt * x, ?_, ?_, ?_⟩
        · exact (⨆ Y ∈ conjSet B N, Y).mul_mem (hgOf_mem Zt) hxmem
        · intro W hW z hz
          rw [MulAut.mul_apply]
          rcases Finset.mem_insert.1 hW with hWZ | hWF
          · have hzZ : z ∈ Z := by rwa [← hWZ]
            rw [hxtriv Z hZs hZF z hzZ, hgOf_a Zt z hzZ]
          · have hWt : W ∈ T := (hs W).1 (hFsub hWF)
            let Wt : T := ⟨W, hWt⟩
            have hWne : Wt ≠ Zt := by
              intro h
              have hWZ : W = Z := congrArg Subtype.val h
              rw [hWZ] at hWF
              exact hZF hWF
            have hWstab : StableUnder A W := by
              have h := (s15_Three_irr_map hNA (hnOf Wt) hR).2.1
              rwa [hZOf Wt] at h
            rw [hxagree W hWF z hz]
            exact hgOf_triv Zt Wt hWne (a z) (hWstab a ha z hz)
        · intro W hWs hWnot z hz
          rw [MulAut.mul_apply]
          have hWt : W ∈ T := (hs W).1 hWs
          let Wt : T := ⟨W, hWt⟩
          have hWnotF : W ∉ F := fun h => hWnot (Finset.mem_insert_of_mem h)
          have hZW : Z ≠ W := by
            intro h
            exact hWnot (h ▸ Finset.mem_insert_self Z F)
          have hWne : Wt ≠ Zt := by
            intro h
            exact hZW (congrArg Subtype.val h).symm
          rw [hxtriv W hWs hWnotF z hz]
          exact hgOf_triv Zt Wt hWne z hz
    obtain ⟨x, hxmem, hxagree, -⟩ := aux s (fun _ h => h)
    have hxeq : x = a := by
      ext w
      have hw : w ∈ sSup T := by
        rw [s15_Three_sSup_conj hNA hsemi htrans hR hS hRS hRS' hmult hBA hBS hAB hBR]
        exact Subgroup.mem_top w
      rw [sSup_eq_iSup'] at hw
      refine Subgroup.iSup_induction (fun Z : T => (Z : Subgroup W))
        (C := fun z => x z = a z) hw ?_ ?_ ?_
      · intro Z z hz
        exact hxagree Z.1 ((hs Z.1).2 Z.2) z hz
      · simp
      · intro y z hy hz
        rw [map_mul, map_mul, hy, hz]
    exact hxeq ▸ hxmem

include hNA hsemi hR hS hRS hRS' hmult hBA hBS hAB hBR in
private lemma s15_Three_R_ne_of_B_ne {m n : MulAut W} (hm : m ∈ N) (hn : n ∈ N)
    (hne : B.map (MulAut.conj m).toMonoidHom ≠ B.map (MulAut.conj n).toMonoidHom) :
    R.map m.toMonoidHom ≠ R.map n.toMonoidHom := by
  intro hRmn
  apply hne
  have hk : n⁻¹ * m ∈ N := N.mul_mem (N.inv_mem hn) hm
  have hkR : R.map (n⁻¹ * m).toMonoidHom = R := by
    have hcomp1 : n.toMonoidHom.comp (n⁻¹ * m).toMonoidHom = m.toMonoidHom := by
      ext w; simp [mul_assoc]
    have h1 : (R.map (n⁻¹ * m).toMonoidHom).map n.toMonoidHom = R.map n.toMonoidHom := by
      rw [Subgroup.map_map, hcomp1, hRmn]
    have hcomp2 : (n⁻¹).toMonoidHom.comp n.toMonoidHom = MonoidHom.id W := by
      ext w; simp
    have h2 := congrArg (Subgroup.map (n⁻¹).toMonoidHom) h1
    rw [Subgroup.map_map] at h2
    rw [hcomp2, Subgroup.map_id] at h2
    rw [Subgroup.map_map, hcomp2, Subgroup.map_id] at h2
    exact h2
  have hBk : B.map (MulAut.conj (n⁻¹ * m)).toMonoidHom = B :=
    s15_Three_conj_B hNA hsemi hR hS hRS hRS' hmult hBA hBS hAB hBR hk hkR
  have h1 := congrArg (Subgroup.map (MulAut.conj n).toMonoidHom) hBk
  have hcomp3 : (MulAut.conj n).toMonoidHom.comp (MulAut.conj (n⁻¹ * m)).toMonoidHom =
      (MulAut.conj m).toMonoidHom := by
    ext w; simp [MulAut.conj_apply, mul_assoc]
  rw [Subgroup.map_map, hcomp3] at h1
  exact h1

end Assemble

theorem s15_Three_assemble (hW : ∀ w : W, w ^ 2 = 1) {A N : Subgroup (MulAut W)}
    (hNA : ∀ n ∈ N, ∀ a : MulAut W, a ∈ A ↔ n * a * n⁻¹ ∈ A) (hsemi : s15Semisimple A)
    (htrans : ∀ I I' : Subgroup W, IsIrrOn A I ⊥ → IsIrrOn A I' ⊥ →
      ∃ n ∈ N, s15SecIso A (I.map (n : MulAut W).toMonoidHom) ⊥ I' ⊥)
    {R S : Subgroup W} (hR : IsIrrOn A R ⊥) (hS : StableUnder A S) (hRS : R ⊓ S = ⊥)
    (hRS' : R ⊔ S = ⊤) (hmult : ∀ I : Subgroup W, IsIrrOn A I ⊥ → I ≠ R → I ≤ S)
    {B : Subgroup (MulAut W)} (hBA : B ≤ A) (hBS : ∀ s ∈ S, ∀ b ∈ B, b s = s)
    (hAB : ∀ a ∈ A, ∃ b ∈ B, ∀ r ∈ R, a r = b r) (hBR : commSub ⊤ B = R) :
    IsDirectProdOfConj A B N ∧
      sSupIndep {Z : Subgroup W | ∃ n ∈ N,
        Z = commSub ⊤ (B.map (MulAut.conj n).toMonoidHom)} ∧
      sSup {Z : Subgroup W | ∃ n ∈ N,
        Z = commSub ⊤ (B.map (MulAut.conj n).toMonoidHom)} = ⊤ := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro Y ⟨n, hn, rfl⟩
    rintro b ⟨b₀, hb₀, rfl⟩
    exact (hNA n hn b₀).mp (hBA hb₀)
  · exact s15_Three_gen hNA hsemi htrans hR hS hRS hRS' hmult hBA hBS hAB hBR
  · rintro Y ⟨m, hm, rfl⟩ Z ⟨n, hn, rfl⟩ hYZ
    have hRne : R.map m.toMonoidHom ≠ R.map n.toMonoidHom :=
      s15_Three_R_ne_of_B_ne hNA hsemi hR hS hRS hRS' hmult hBA hBS hAB hBR hm hn hYZ
    have hk : m⁻¹ * n ∈ N := N.mul_mem (N.inv_mem hm) hn
    have hkRne : R.map (m⁻¹ * n).toMonoidHom ≠ R := by
      intro h
      apply hRne
      have hcomp : m.toMonoidHom.comp (m⁻¹ * n).toMonoidHom = n.toMonoidHom := by
        ext w; simp [mul_assoc]
      have := congrArg (Subgroup.map m.toMonoidHom) h
      rw [Subgroup.map_map, hcomp] at this
      exact this.symm
    have hc := s15_Three_comm_conj hNA hsemi hR hS hRS hRS' hmult hBA hBS hAB hBR hk hkRne
    have hmap := congrArg (Subgroup.map (MulAut.conj m).toMonoidHom) hc
    rw [Subgroup.map_commutator, Subgroup.map_bot] at hmap
    have hcomp2 : (MulAut.conj m).toMonoidHom.comp (MulAut.conj (m⁻¹ * n)).toMonoidHom =
        (MulAut.conj n).toMonoidHom := by
      ext w; simp [MulAut.conj_apply, mul_assoc]
    rw [Subgroup.map_map, hcomp2] at hmap
    exact hmap
  · rintro Y ⟨n, hn, rfl⟩
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyY, hyrest⟩ := Subgroup.mem_inf.1 hy
    have hle_cent : (⨆ Z ∈ conjSet B N, ⨆ (_ : Z ≠ B.map (MulAut.conj n).toMonoidHom), Z) ≤
        centSub (R.map n.toMonoidHom) := by
      refine iSup_le ?_
      intro Z
      refine iSup_le ?_
      intro hZ
      refine iSup_le ?_
      intro hZY
      obtain ⟨m, hm, rfl⟩ := hZ
      have hRne : R.map m.toMonoidHom ≠ R.map n.toMonoidHom :=
        s15_Three_R_ne_of_B_ne hNA hsemi hR hS hRS hRS' hmult hBA hBS hAB hBR hm hn hZY
      have hRm : R.map n.toMonoidHom ≤ S.map m.toMonoidHom :=
        s15_Three_conj_le_map_S hNA hR hmult hn hm hRne.symm
      intro z hz r hr
      exact s15_Three_conj_trivial_on_map_S hBS z hz r (hRm hr)
    have hyR : ∀ r ∈ R.map n.toMonoidHom, y r = r :=
      fun r hr => mem_centSub.1 (hle_cent hyrest) r hr
    have hyS : ∀ s ∈ S.map n.toMonoidHom, y s = s :=
      s15_Three_conj_trivial_on_map_S hBS y hyY
    have hy_top : ∀ w : W, y w = w := by
      intro w
      have hw : w ∈ R.map n.toMonoidHom ⊔ S.map n.toMonoidHom := by
        rw [← Subgroup.map_sup, hRS',
          Subgroup.map_top_of_surjective n.toMonoidHom n.surjective]
        exact Subgroup.mem_top w
      obtain ⟨r, hr, s, hs, rfl⟩ := Subgroup.mem_sup.1 hw
      rw [map_mul, hyR r hr, hyS s hs]
    exact Subgroup.mem_bot.mpr (MulEquiv.ext hy_top)
  · have hset : {Z : Subgroup W | ∃ n ∈ N,
        Z = commSub ⊤ (B.map (MulAut.conj n).toMonoidHom)} =
        {Z : Subgroup W | ∃ n ∈ N, Z = R.map n.toMonoidHom} := by
      ext Z
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, by rw [s15_Three_commSub_conj n B, hBR]⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, by rw [s15_Three_commSub_conj n B, hBR]⟩
    rw [hset]
    exact s15_Three_indep hNA hsemi htrans hR hS hRS hRS' hmult hBA hBS hAB hBR
  · have hset : {Z : Subgroup W | ∃ n ∈ N,
        Z = commSub ⊤ (B.map (MulAut.conj n).toMonoidHom)} =
        {Z : Subgroup W | ∃ n ∈ N, Z = R.map n.toMonoidHom} := by
      ext Z
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, by rw [s15_Three_commSub_conj n B, hBR]⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, by rw [s15_Three_commSub_conj n B, hBR]⟩
    rw [hset]
    exact s15_Three_sSup_conj hNA hsemi htrans hR hS hRS hRS' hmult hBA hBS hAB hBR

end Abstract

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
