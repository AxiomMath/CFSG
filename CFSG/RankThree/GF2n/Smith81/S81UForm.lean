module

public import CFSG.RankThree.GF2n.Smith81.S81URoot
public import CFSG.RankThree.GF2n.Smith81.S81UModelDef

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

private theorem h52_even_odd_decide : ∀ x y z : Fin 6, x ≠ y → x ≠ z → y ≠ z →
    ({x, y, z} : Finset (Fin 6)) ≠ ({0, 2, 4} : Finset (Fin 6)) →
    ∃ a b : Fin 6, a.val % 2 = 0 ∧ b.val % 2 = 1 ∧ b ∈ ({x, y, z} : Finset (Fin 6)) ∧
      a ∉ ({x, y, z} : Finset (Fin 6)) := by
  decide

theorem exists_even_odd_pair (I : Set.powersetCard (Fin 6) 3) (hI : I ≠ S024) :
    ∃ a b : Fin 6, a.val % 2 = 0 ∧ b.val % 2 = 1 ∧ b ∈ I.val ∧ a ∉ I.val := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hIxyz⟩ := Finset.card_eq_three.mp I.prop
  have hne : ({x, y, z} : Finset (Fin 6)) ≠ ({0, 2, 4} : Finset (Fin 6)) := fun h =>
    hI (Subtype.ext (hIxyz.trans h))
  rw [hIxyz]
  exact h52_even_odd_decide x y z hxy hxz hyz hne

private theorem h52_partner_val_even (a : Fin 6) (ha : a.val % 2 = 0) :
    (partner a).val = a.val + 1 := by
  simp [partner, ha]

private theorem h52_conj_fix (S X : GL (Fin 6) F) (ξ : Cube F)
    (h : rho F (S * X * S⁻¹) ξ = ξ) : rho F X (rho F S⁻¹ ξ) = rho F S⁻¹ ξ := by
  rw [rho_mul_apply, rho_mul_apply] at h
  have h2 : rho F S⁻¹ (rho F S (rho F X (rho F S⁻¹ ξ))) = rho F S⁻¹ ξ := by rw [h]
  rwa [← rho_mul_apply, inv_mul_cancel, rho_one, Module.End.one_apply] at h2

private theorem h52_transvGL_congr {i k i' k' : Fin 6} (hik : i ≠ k) (hik' : i' ≠ k')
    (h1 : i = i') (h2 : k = k') (c : F) : transvGL F i k hik c = transvGL F i' k' hik' c := by
  subst h1 h2
  rfl

private theorem h52_long_fix (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (ξ : Cube F)
    (h : ∀ g : SUid σ 6, g ∈ e3uU0Sub σ → rho F (g : GL (Fin 6) F) ξ = ξ)
    {i k : Fin 6} (hik : i ≠ k) (j : Fin 3) (hi : i.val = 2 * j.val)
    (hk : k.val = 2 * j.val + 1) :
    rho F (transvGL F i k hik 1) (rho F ((frameGL σ ω hω : GL (Fin 6) F))⁻¹ ξ) =
      rho F ((frameGL σ ω hω : GL (Fin 6) F))⁻¹ ξ := by
  obtain ⟨g, hg, hgeq⟩ := exists_longRoot hσ hω j
  have hfix := h g hg
  rw [hgeq] at hfix
  have hne : (⟨2 * j.val, by omega⟩ : Fin 6) ≠ ⟨2 * j.val + 1, by omega⟩ := by
    intro e
    have := congrArg Fin.val e
    simp at this
  have hT := h52_transvGL_congr (i' := ⟨2 * j.val, by omega⟩) (k' := ⟨2 * j.val + 1, by omega⟩)
    hik hne (Fin.ext hi) (Fin.ext hk) (1 : F)
  rw [hT]
  exact h52_conj_fix _ _ _ hfix

private theorem h52_short_fix (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (ξ : Cube F)
    (h : ∀ g : SUid σ 6, g ∈ e3uU0Sub σ → rho F (g : GL (Fin 6) F) ξ = ξ)
    {a b : Fin 6} (ha : a.val % 2 = 0) (hb : b.val % 2 = 1) (hab : a ≠ b)
    (hbp : b ≠ partner a) (c : F) :
    rho F (transvGL F a b hab c * transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c))
      (rho F ((frameGL σ ω hω : GL (Fin 6) F))⁻¹ ξ) =
      rho F ((frameGL σ ω hω : GL (Fin 6) F))⁻¹ ξ := by
  obtain ⟨g, hg, hgeq⟩ := frameConj_short_mem_U0 hσ hω ha hb hab hbp c
  have hfix := h g hg
  rw [hgeq] at hfix
  exact h52_conj_fix _ _ _ hfix

private theorem h52_eq_smul (ξ : Cube F) (I : Set.powersetCard (Fin 6) 3)
    (h : ∀ J : Set.powersetCard (Fin 6) 3, J ≠ I → coord F ξ J = 0) :
    ξ = coord F ξ I • cubeBasis F I := by
  apply (cubeBasis F).repr.injective
  refine Finsupp.ext fun J => ?_
  show coord F ξ J = coord F (coord F ξ I • cubeBasis F I) J
  rw [coord_smul, coord_cubeBasis]
  by_cases hJ : I = J
  · subst hJ
    simp
  · rw [if_neg hJ, mul_zero]
    exact h J (fun h' => hJ h'.symm)

private theorem h52_claimA (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (ξ : Cube F)
    (h : ∀ g : SUid σ 6, g ∈ e3uU0Sub σ → rho F (g : GL (Fin 6) F) ξ = ξ)
    {a b : Fin 6} (ha : a.val % 2 = 0) (hb : b.val % 2 = 1) (hab : a ≠ b) :
    Nop F a b hab (rho F ((frameGL σ ω hω : GL (Fin 6) F))⁻¹ ξ) = 0 := by
  obtain ⟨η, hη⟩ : ∃ η : Cube F, rho F ((frameGL σ ω hω : GL (Fin 6) F))⁻¹ ξ = η := ⟨_, rfl⟩
  rw [hη]
  by_cases hbp : b = partner a
  · have hL := h52_long_fix hσ hω ξ h hab ⟨a.val / 2, by have := a.isLt; omega⟩
      (by show a.val = 2 * (a.val / 2); omega)
      (by show b.val = 2 * (a.val / 2) + 1; rw [hbp, h52_partner_val_even a ha]; omega)
    rw [hη] at hL
    unfold Nop
    rw [LinearMap.sub_apply, Module.End.one_apply, hL, sub_self]
  · have key : ∀ c : F,
        c • Nop F a b hab η + σ c • Nop F (partner b) (partner a) (partner_ne_partner hab) η +
          (c * σ c) • Nop F a b hab
            (Nop F (partner b) (partner a) (partner_ne_partner hab) η) = 0 := by
      intro c
      have hS := h52_short_fix hσ hω ξ h ha hb hab hbp c
      rw [hη] at hS
      have h2 := rho_shortRoot_sub (σ := σ) hab c η
      rw [hS, sub_self] at h2
      exact h2.symm
    have hmem := three_vectors hσ (⊥ : Submodule F (Cube F))
      (x := Nop F a b hab η) (y := Nop F (partner b) (partner a) (partner_ne_partner hab) η)
      (z := Nop F a b hab (Nop F (partner b) (partner a) (partner_ne_partner hab) η))
      (fun c => (Submodule.mem_bot (R := F)).mpr (key c))
    exact (Submodule.mem_bot (R := F)).mp hmem.1

theorem fixU0_eq_smul_pt0 (hσ : IsUnitaryInvolution σ) {ξ : Cube F}
    (h : ∀ g : SUid σ 6, g ∈ e3uU0Sub σ → rho F (g : GL (Fin 6) F) ξ = ξ) :
    ∃ c : F, ξ = c • pt0 F := by
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one σ)
  have hB : ∀ J : Set.powersetCard (Fin 6) 3, J ≠ S024 →
      coord F (rho F ((frameGL σ ω hω : GL (Fin 6) F))⁻¹ ξ) J = 0 := by
    intro J hJ
    obtain ⟨a, b, ha, hb, hbJ, haJ⟩ := exists_even_odd_pair J hJ
    have hab : a ≠ b := fun e => by rw [e] at ha; omega
    exact coord_eq_zero_of_Nop_eq_zero hab (h52_claimA hσ hω ξ h ha hb hab) hbJ haJ
  obtain ⟨c, hc⟩ : ∃ c : F, rho F ((frameGL σ ω hω : GL (Fin 6) F))⁻¹ ξ = c • p0 F :=
    ⟨coord F (rho F ((frameGL σ ω hω : GL (Fin 6) F))⁻¹ ξ) S024, h52_eq_smul _ S024 hB⟩
  refine ⟨c, ?_⟩
  have h1 : rho F (frameGL σ ω hω : GL (Fin 6) F)
      (rho F ((frameGL σ ω hω : GL (Fin 6) F))⁻¹ ξ) = ξ := by
    rw [← rho_mul_apply, mul_inv_cancel, rho_one, Module.End.one_apply]
  rw [← h1, hc, map_smul, rho_frameGL_p0]

theorem reach_all (P : Set.powersetCard (Fin 6) 3 → Prop) (h0 : P S024)
    (hstep : ∀ (I : Set.powersetCard (Fin 6) 3) (a b : Fin 6) (hab : a ≠ b)
      (h : b ∈ I.val ∧ a ∉ I.val), P I → P (replSet I a b h.1 h.2)) :
    ∀ I, P I := by
  have hcard : ∀ J : Set.powersetCard (Fin 6) 3, J.val.card = 3 := fun J => J.prop
  have key : ∀ n : ℕ, ∀ I : Set.powersetCard (Fin 6) 3, (I.val \ S024.val).card = n → P I := by
    intro n
    induction n with
    | zero =>
      intro I hI
      have hsub : I.val ⊆ S024.val := by
        intro x hx
        by_contra hx'
        have hmem : x ∈ I.val \ S024.val := Finset.mem_sdiff.mpr ⟨hx, hx'⟩
        have := Finset.card_pos.mpr ⟨x, hmem⟩
        omega
      have heq : I.val = S024.val :=
        Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [hcard I, hcard S024]))
      have hIS : I = S024 := Subtype.ext heq
      rw [hIS]
      exact h0
    | succ n ih =>
      intro I hI
      obtain ⟨b, hb⟩ : (I.val \ S024.val).Nonempty := Finset.card_pos.mp (by omega)
      have hbI : b ∈ I.val := (Finset.mem_sdiff.mp hb).1
      have hbS : b ∉ S024.val := (Finset.mem_sdiff.mp hb).2
      obtain ⟨a, haS, haI⟩ : ∃ a, a ∈ S024.val ∧ a ∉ I.val := by
        by_contra hcon
        have hsub : S024.val ⊆ I.val := by
          intro x hx
          by_contra hx'
          exact hcon ⟨x, hx, hx'⟩
        have heq : S024.val = I.val :=
          Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [hcard I, hcard S024]))
        exact hbS (by rw [heq]; exact hbI)
      have hab : a ≠ b := by
        rintro rfl
        exact hbS haS
      have haJ : a ∈ (replSet I a b hbI haI).val := by
        show a ∈ insert a (I.val.erase b)
        exact Finset.mem_insert_self a _
      have hbJ : b ∉ (replSet I a b hbI haI).val := by
        show b ∉ insert a (I.val.erase b)
        rw [Finset.mem_insert, not_or]
        exact ⟨Ne.symm hab, fun h => (Finset.mem_erase.mp h).1 rfl⟩
      have hJcard : ((replSet I a b hbI haI).val \ S024.val).card = n := by
        have hset : (replSet I a b hbI haI).val \ S024.val = (I.val \ S024.val).erase b := by
          ext x
          rw [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_sdiff]
          show (x ∈ insert a (I.val.erase b) ∧ x ∉ S024.val) ↔
            (x ≠ b ∧ x ∈ I.val ∧ x ∉ S024.val)
          constructor
          · rintro ⟨hx, hxS⟩
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact absurd haS hxS
            · exact ⟨(Finset.mem_erase.mp hx').1, (Finset.mem_erase.mp hx').2, hxS⟩
          · rintro ⟨hxb, hxI, hxS⟩
            exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxb, hxI⟩), hxS⟩
        have h1 := Finset.card_erase_of_mem hb
        rw [hset]
        omega
      have hPJ : P (replSet I a b hbI haI) := ih _ hJcard
      have hI' : I = replSet (replSet I a b hbI haI) b a haJ hbJ :=
        (replSet_eq_iff hbI haI haJ hbJ).mp rfl
      rw [hI']
      exact hstep _ b a hab.symm ⟨haJ, hbJ⟩ hPJ
  intro I
  exact key _ I rfl

private theorem h53_rho_conj (g t : GL (Fin 6) F) (v : Cube F) :
    rho F (g * t * g⁻¹) (rho F g v) = rho F (g * t) v := by
  rw [← rho_mul_apply, inv_mul_cancel_right]

private theorem h53_rho_sub (g t : GL (Fin 6) F) (v : Cube F) :
    rho F g (rho F t v - v) = rho F (g * t * g⁻¹) (rho F g v) - rho F g v := by
  rw [map_sub, h53_rho_conj, ← rho_mul_apply]

private theorem h53_Nop_apply {a b : Fin 6} (hab : a ≠ b) (v : Cube F) :
    Nop F a b hab v = rho F (transvGL F a b hab 1) v - v := by
  simp only [Nop, LinearMap.sub_apply, Module.End.one_apply]

private theorem h53_nop_comap (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1)
    (Q : Submodule F (Cube F))
    (hQ : ∀ g : SUid σ 6, ∀ w ∈ Q, rho F (g : GL (Fin 6) F) w ∈ Q)
    {a b : Fin 6} (hab : a ≠ b) (v : Cube F)
    (hv : v ∈ Q.comap (rho F (frameGL σ ω hω))) :
    Nop F a b hab v ∈ Q.comap (rho F (frameGL σ ω hω)) := by
  rw [Submodule.mem_comap] at hv
  by_cases hb : b = partner a
  · subst hb
    have hmem := frameConj_long_mem hσ hω a (c := 1) (map_one σ)
    rw [Submodule.mem_comap, h53_Nop_apply, h53_rho_sub]
    exact Q.sub_mem (hQ ⟨_, hmem⟩ _ hv) hv
  · have hcomb : ∀ c : F,
        c • Nop F a b hab v + σ c • Nop F (partner b) (partner a) (partner_ne_partner hab) v +
          (c * σ c) • Nop F a b hab (Nop F (partner b) (partner a) (partner_ne_partner hab) v) ∈
          Q.comap (rho F (frameGL σ ω hω)) := by
      intro c
      rw [Submodule.mem_comap, ← rho_shortRoot_sub hab c v, h53_rho_sub]
      exact Q.sub_mem (hQ ⟨_, frameConj_short_mem hσ hω hab hb c⟩ _ hv) hv
    exact (three_vectors hσ _ hcomb).1

theorem orbit_span_top (hσ : IsUnitaryInvolution σ) :
    Submodule.span F (Set.range fun g : SUid σ 6 => rho F (g : GL (Fin 6) F) (pt0 F)) = ⊤ := by
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one σ)
  obtain ⟨Q, hQdef⟩ : ∃ Q : Submodule F (Cube F),
      Q = Submodule.span F (Set.range fun g : SUid σ 6 => rho F (g : GL (Fin 6) F) (pt0 F)) :=
    ⟨_, rfl⟩
  rw [← hQdef]
  have hstab : ∀ g : SUid σ 6, ∀ w ∈ Q, rho F (g : GL (Fin 6) F) w ∈ Q := by
    intro g w hw
    rw [hQdef] at hw ⊢
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      show rho F (g : GL (Fin 6) F) (rho F (h : GL (Fin 6) F) (pt0 F)) ∈ _
      rw [← rho_mul_apply]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  have hpt0 : pt0 F ∈ Q := by
    rw [hQdef]
    have hmem : rho F ((1 : SUid σ 6) : GL (Fin 6) F) (pt0 F) ∈
        Submodule.span F (Set.range fun g : SUid σ 6 => rho F (g : GL (Fin 6) F) (pt0 F)) :=
      Submodule.subset_span ⟨1, rfl⟩
    rwa [Subgroup.coe_one, rho_one, Module.End.one_apply] at hmem
  have hp0 : rho F (frameGL σ ω hω) (cubeBasis F S024) = pt0 F := rho_frameGL_p0 ω hω
  have hcb : cubeBasis F S024 ∈ Q.comap (rho F (frameGL σ ω hω)) := by
    rw [Submodule.mem_comap, hp0]
    exact hpt0
  have hall : ∀ I : Set.powersetCard (Fin 6) 3,
      cubeBasis F I ∈ Q.comap (rho F (frameGL σ ω hω)) := by
    intro I
    refine reach_all (fun J => cubeBasis F J ∈ Q.comap (rho F (frameGL σ ω hω))) hcb ?_ I
    intro J a b hab h hJ
    have hN := Nop_cubeBasis (F := F) hab J
    rw [dif_pos h] at hN
    show cubeBasis F (replSet J a b h.1 h.2) ∈ Q.comap (rho F (frameGL σ ω hω))
    rw [← hN]
    exact h53_nop_comap hσ hω Q hstab hab (cubeBasis F J) hJ
  have hle : Submodule.span F (Set.range (cubeBasis F)) ≤ Q.comap (rho F (frameGL σ ω hω)) := by
    rw [Submodule.span_le]
    rintro _ ⟨I, rfl⟩
    exact hall I
  rw [(cubeBasis F).span_eq] at hle
  rw [eq_top_iff]
  intro η _
  have h1 : rho F (frameGL σ ω hω) (rho F (frameGL σ ω hω)⁻¹ η) ∈ Q :=
    hle (show rho F (frameGL σ ω hω)⁻¹ η ∈ (⊤ : Submodule F (Cube F)) from Submodule.mem_top)
  rwa [← rho_mul_apply, mul_inv_cancel, rho_one, Module.End.one_apply] at h1

@[expose] noncomputable def pt0W (σ : F ≃+* F) : Wform σ :=
  ⟨pt0 F, mem_Wform_iff.mpr (mem_Wsub_iff.mpr theta_pt0)⟩

theorem orbit_span_Fq (hσ : IsUnitaryInvolution σ) :
    Submodule.span (Fσ σ) (Set.range fun g : SUid σ 6 => Wact σ g (pt0W σ)) = ⊤ := by
  have hspan := orbit_span_top hσ
  have hmem1 : ∀ (g : SUid σ 6) (c : F),
      ∃ s ∈ Submodule.span (Fσ σ) (Set.range fun g : SUid σ 6 => Wact σ g (pt0W σ)),
        (s : Cube F) = c • rho F (g : GL (Fin 6) F) (pt0 F) +
          theta σ (c • rho F (g : GL (Fin 6) F) (pt0 F)) := by
    intro g c
    have hθ : theta σ (rho F (g : GL (Fin 6) F) (pt0 F)) = rho F (g : GL (Fin 6) F) (pt0 F) :=
      mem_Wsub_iff.mp (mem_Wform_iff.mp (Wact σ g (pt0W σ)).2)
    refine ⟨(⟨c + σ c, mem_Fσ_iff.mpr (hσ.trace_fixed c)⟩ : Fσ σ) • Wact σ g (pt0W σ),
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩), ?_⟩
    rw [theta_smul, hθ]
    show (c + σ c) • rho F (g : GL (Fin 6) F) (pt0 F) =
      c • rho F (g : GL (Fin 6) F) (pt0 F) + σ c • rho F (g : GL (Fin 6) F) (pt0 F)
    rw [add_smul]
  have hQ : ∀ x : Cube F,
      x ∈ Submodule.span F (Set.range fun g : SUid σ 6 => rho F (g : GL (Fin 6) F) (pt0 F)) →
        ∀ c : F, ∃ s ∈ Submodule.span (Fσ σ) (Set.range fun g : SUid σ 6 => Wact σ g (pt0W σ)),
          (s : Cube F) = c • x + theta σ (c • x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hmem1 g
    | zero =>
      intro c
      exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      intro c
      obtain ⟨s₁, hs₁, e₁⟩ := hx c
      obtain ⟨s₂, hs₂, e₂⟩ := hy c
      refine ⟨s₁ + s₂, Submodule.add_mem _ hs₁ hs₂, ?_⟩
      rw [Submodule.coe_add, e₁, e₂, smul_add, map_add]
      abel
    | smul a x _ hx =>
      intro c
      obtain ⟨s, hs, e⟩ := hx (c * a)
      refine ⟨s, hs, ?_⟩
      rw [smul_smul]
      exact e
  rw [eq_top_iff]
  intro w _
  obtain ⟨τ, hτ⟩ := hσ.trace_surj 1 (map_one σ)
  have hw : (w : Cube F) ∈
      Submodule.span F (Set.range fun g : SUid σ 6 => rho F (g : GL (Fin 6) F) (pt0 F)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨s, hs, e⟩ := hQ (w : Cube F) hw τ
  have hθw : theta σ (w : Cube F) = (w : Cube F) := mem_Wsub_iff.mp (mem_Wform_iff.mp w.2)
  have hsw : s = w := by
    apply Subtype.ext
    rw [e, theta_smul, hθw, ← add_smul, hτ, one_smul]
  rw [← hsw]
  exact hs

private theorem h54_bmat_symm (a b : Idx) : bmat (K := F) a b = bmat (K := F) b a := by
  by_cases hb : b = cmpl a
  · subst hb
    have h := bmat_cmpl_eq (K := F) a (cmpl a)
    rwa [cmpl_cmpl] at h
  · have h1 : bmat (K := F) a b = 0 := bmat_eq_zero hb
    have h2 : bmat (K := F) b a = 0 := by
      apply bmat_eq_zero
      intro hab
      apply hb
      rw [hab, cmpl_cmpl]
    rw [h1, h2]

private theorem h54_beta_symm (ξ η : Cube F) : beta F ξ η = beta F η ξ := by
  rw [beta_expand, beta_expand, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [h54_bmat_symm a b]
  ring

private noncomputable def h54_fval (hσ : IsUnitaryInvolution σ) (u v : Wform σ) : Fσ σ :=
  ⟨beta F (u : Cube F) (v : Cube F),
    mem_Fσ_iff.mpr (beta_mem_fixed hσ.invol (mem_Wform_iff.mp u.2) (mem_Wform_iff.mp v.2))⟩

private theorem h54_riesz {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (b : V →ₗ[L] V →ₗ[L] L)
    (hb : ∀ w : V, (∀ u : V, b u w = 0) → w = 0) (B' : V →ₗ[L] V →ₗ[L] L) :
    ∃ T : V →ₗ[L] V, ∀ u v : V, B' u v = b u (T v) := by
  have hinj : Function.Injective b.flip := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply hb
    intro u
    have h := LinearMap.congr_fun hw u
    rw [LinearMap.flip_apply, LinearMap.zero_apply] at h
    exact h
  have hdim : Module.finrank L V = Module.finrank L (Module.Dual L V) :=
    Subspace.dual_finrank_eq.symm
  have hsurj : Function.Surjective b.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let Φ : V ≃ₗ[L] Module.Dual L V := LinearEquiv.ofBijective b.flip ⟨hinj, hsurj⟩
  refine ⟨Φ.symm.toLinearMap ∘ₗ B'.flip, fun u v => ?_⟩
  have h1 : b.flip (Φ.symm (B'.flip v)) = B'.flip v := Φ.apply_symm_apply _
  have h2 := LinearMap.congr_fun h1 u
  rw [LinearMap.flip_apply, LinearMap.flip_apply] at h2
  exact h2.symm

private noncomputable def h54_BW (hσ : IsUnitaryInvolution σ) :
    Wform σ →ₗ[Fσ σ] Wform σ →ₗ[Fσ σ] Fσ σ :=
  LinearMap.mk₂ (Fσ σ) (h54_fval hσ)
    (fun m₁ m₂ n => Subtype.ext (by simp [h54_fval]))
    (fun c m n => Subtype.ext (by simp [h54_fval] <;> rfl))
    (fun m n₁ n₂ => Subtype.ext (by simp [h54_fval]))
    (fun c m n => Subtype.ext (by simp [h54_fval] <;> rfl))

theorem exists_commuting_T [Finite F] (hσ : IsUnitaryInvolution σ)
    (B' : Wform σ →ₗ[Fσ σ] Wform σ →ₗ[Fσ σ] Fσ σ)
    (hinv : ∀ (g : SUid σ 6) (u v : Wform σ), B' (Wact σ g u) (Wact σ g v) = B' u v) :
    ∃ T : Wform σ →ₗ[Fσ σ] Wform σ,
      (∀ u v : Wform σ, ((B' u v : Fσ σ) : F) = beta F (u : Cube F) ((T v : Wform σ) : Cube F)) ∧
      ∀ (g : SUid σ 6) (v : Wform σ), T (Wact σ g v) = Wact σ g (T v) := by
  haveI : FiniteDimensional F (Cube F) := Module.Finite.of_basis (cubeBasis F)
  haveI : Finite (Cube F) := Module.finite_of_finite F
  haveI : Finite (Wform σ) := Subtype.finite
  obtain ⟨BW, hBW⟩ : ∃ BW : Wform σ →ₗ[Fσ σ] Wform σ →ₗ[Fσ σ] Fσ σ,
      ∀ u v : Wform σ, ((BW u v : Fσ σ) : F) = beta F (u : Cube F) (v : Cube F) :=
    ⟨h54_BW hσ, fun _ _ => rfl⟩
  have hnd : ∀ w : Wform σ, (∀ u : Wform σ, BW u w = 0) → w = 0 := by
    intro w hw
    have hw0 : (w : Cube F) = 0 := by
      refine beta_nondeg_Wsub hσ (mem_Wform_iff.mp w.2) fun w' hw' => ?_
      have h1 := hBW ⟨w', mem_Wform_iff.mpr hw'⟩ w
      have h2 : ((BW ⟨w', mem_Wform_iff.mpr hw'⟩ w : Fσ σ) : F) = 0 := by
        rw [hw ⟨w', mem_Wform_iff.mpr hw'⟩]
        rfl
      rw [h2] at h1
      exact (h54_beta_symm (w : Cube F) w').trans h1.symm
    exact Submodule.coe_eq_zero.mp hw0
  have hinj : Function.Injective BW.flip := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply hnd
    intro u
    have h := LinearMap.congr_fun hw u
    rw [LinearMap.flip_apply, LinearMap.zero_apply] at h
    exact h
  obtain ⟨T, hT⟩ := h54_riesz (L := Fσ σ) (V := Wform σ) BW hnd B'
  have hTB : ∀ x, BW.flip (T x) = B'.flip x := fun x => LinearMap.ext fun u => by
    rw [LinearMap.flip_apply, LinearMap.flip_apply]
    exact (hT u x).symm
  have hy : ∀ x v : Wform σ, BW x (T v) = B' x v := fun x v => (hT x v).symm
  have hinvBW : ∀ (g : SUid σ 6) (x y : Wform σ), BW (Wact σ g x) (Wact σ g y) = BW x y := by
    intro g x y
    apply Subtype.ext
    rw [hBW, hBW, Wact_apply, Wact_apply, beta_rho, (mem_SUid.mp g.2).1, one_mul]
  refine ⟨T, fun u v => ?_, fun g v => ?_⟩
  · rw [← hy u v, hBW]
  · apply hinj
    rw [hTB]
    apply LinearMap.ext
    intro u
    obtain ⟨u', rfl⟩ : ∃ u', u = Wact σ g u' :=
      ⟨(Wact σ g).symm u, ((Wact σ g).apply_symm_apply u).symm⟩
    rw [LinearMap.flip_apply, LinearMap.flip_apply, hinv g u' v, hinvBW g u' (T v), hy u' v]

theorem schur_W [Finite F] (hσ : IsUnitaryInvolution σ) (T : Wform σ →ₗ[Fσ σ] Wform σ)
    (hcomm : ∀ (g : SUid σ 6) (v : Wform σ), T (Wact σ g v) = Wact σ g (T v)) :
    ∃ c : Fσ σ, ∀ v : Wform σ, T v = c • v := by
  have hfixp : ∀ g : SUid σ 6, g ∈ e3uU0Sub σ → Wact σ g (pt0W σ) = pt0W σ := by
    intro g hg
    have hg' : ∀ i : Fin 3, ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec i) =
        e3uT0Vec i := hg
    apply Subtype.ext
    rw [Wact_apply]
    show rho F (g : GL (Fin 6) F) (pt0 F) = pt0 F
    rw [pt0_eq_ιMulti_T0, rho_ιMulti]
    congr 1
    funext i
    exact hg' i
  have hfixt : ∀ g : SUid σ 6, g ∈ e3uU0Sub σ →
      rho F (g : GL (Fin 6) F) ((T (pt0W σ) : Wform σ) : Cube F) =
        ((T (pt0W σ) : Wform σ) : Cube F) := by
    intro g hg
    have h1 : Wact σ g (T (pt0W σ)) = T (pt0W σ) := by
      rw [← hcomm g (pt0W σ), hfixp g hg]
    have h2 := Wact_apply g (T (pt0W σ))
    rw [h1] at h2
    exact h2.symm
  obtain ⟨c, hc⟩ := fixU0_eq_smul_pt0 hσ hfixt
  have hpW : pt0 F ∈ Wsub σ := mem_Wform_iff.mp (pt0W σ).2
  have hcF : σ c = c :=
    smul_mem_Fq_of_mem_Wsub hσ.invol (mem_Wform_iff.mp (T (pt0W σ)).2) hpW pt0_ne_zero hc
  have hTp : T (pt0W σ) = (⟨c, mem_Fσ_iff.mpr hcF⟩ : Fσ σ) • pt0W σ := by
    apply Subtype.ext
    exact hc
  have hall : T = (⟨c, mem_Fσ_iff.mpr hcF⟩ : Fσ σ) • LinearMap.id := by
    apply LinearMap.ext_on_range (orbit_span_Fq hσ)
    intro g
    show T (Wact σ g (pt0W σ)) = (⟨c, mem_Fσ_iff.mpr hcF⟩ : Fσ σ) • Wact σ g (pt0W σ)
    rw [hcomm g (pt0W σ), hTp, map_smul]
  exact ⟨⟨c, mem_Fσ_iff.mpr hcF⟩, fun v => LinearMap.congr_fun hall v⟩

end CFSG.RankThree.GF2n.Smith81.U6Cube

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

theorem u6InvariantFormStatement_holds : U6InvariantFormStatement := by
  intro F _ _ _ f hF B' hinv
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) :=
    isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨T, hT, hcomm⟩ := exists_commuting_T hσ B' hinv
  obtain ⟨c, hc⟩ := schur_W hσ T hcomm
  refine ⟨(c : F), fun u v => ?_⟩
  rw [hT u v, hc v]
  show beta F (u : Cube F) ((c : F) • (v : Cube F)) = (c : F) * beta F (u : Cube F) (v : Cube F)
  rw [map_smul, smul_eq_mul]

end CFSG.RankThree.GF2n.Smith81

