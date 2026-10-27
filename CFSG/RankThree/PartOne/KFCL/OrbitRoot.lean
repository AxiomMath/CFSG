module

public import CFSG.RankThree.PartOne.KFCL.Core

public section

namespace CFSG.RankThree.PartOne.KFCL

variable {Γ : Type} [Group Γ]

@[expose] def blockOrbit (W : Subgroup Γ) (Std : Set (Subgroup Γ)) : Set (Subgroup Γ) :=
  {B | ∃ w ∈ W, ∃ S ∈ Std, B = S.map (MulAut.conj w).toMonoidHom}

theorem conj_mul_toMonoidHom (w w' : Γ) :
    (MulAut.conj (w * w')).toMonoidHom = (MulAut.conj w).toMonoidHom.comp (MulAut.conj w').toMonoidHom := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem conj_mem_blockOrbit {W : Subgroup Γ} {Std : Set (Subgroup Γ)} {B : Subgroup Γ}
    (hB : B ∈ blockOrbit W Std) {w : Γ} (hw : w ∈ W) :
    B.map (MulAut.conj w).toMonoidHom ∈ blockOrbit W Std := by
  obtain ⟨w', hw', S, hS, rfl⟩ := hB
  refine ⟨w * w', W.mul_mem hw hw', S, hS, ?_⟩
  rw [Subgroup.map_map, conj_mul_toMonoidHom]

theorem mem_map_conj_iff' {H : Subgroup Γ} {w x : Γ} :
    x ∈ H.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * x * w ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem map_conj_inf_centralizer {T : Subgroup Γ} {w : Γ} (hw : w ∈ Subgroup.normalizer (T : Set Γ))
    (B : Subgroup Γ) :
    (T ⊓ Subgroup.centralizer (B : Set Γ)).map (MulAut.conj w).toMonoidHom =
      T ⊓ Subgroup.centralizer ((B.map (MulAut.conj w).toMonoidHom : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff] at hw
  ext x
  rw [mem_map_conj_iff', Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  have hT : w⁻¹ * x * w ∈ T ↔ x ∈ T := by
    have h2 := hw (w⁻¹ * x * w)
    rw [show w * (w⁻¹ * x * w) * w⁻¹ = x by group] at h2
    exact h2
  refine and_congr hT ?_
  constructor
  · intro h b hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    have h1 := h b' hb'
    show w * b' * w⁻¹ * x = x * (w * b' * w⁻¹)
    calc w * b' * w⁻¹ * x = w * (b' * (w⁻¹ * x * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * x * w) * b') * w⁻¹ := by rw [h1]
      _ = x * (w * b' * w⁻¹) := by group
  · intro h b hb
    have h1 := h (w * b * w⁻¹) (Subgroup.mem_map.2 ⟨b, hb, rfl⟩)
    calc b * (w⁻¹ * x * w) = w⁻¹ * ((w * b * w⁻¹) * x) * w := by group
      _ = w⁻¹ * (x * (w * b * w⁻¹)) * w := by rw [h1]
      _ = (w⁻¹ * x * w) * b := by group

theorem block_simple_map {S : Subgroup Γ}
    (hS : ∀ N : Subgroup Γ, N ≤ S → (N.subgroupOf S).Normal → N = ⊥ ∨ N = S) (w : Γ) :
    ∀ N : Subgroup Γ, N ≤ S.map (MulAut.conj w).toMonoidHom →
      (N.subgroupOf (S.map (MulAut.conj w).toMonoidHom)).Normal →
      N = ⊥ ∨ N = S.map (MulAut.conj w).toMonoidHom := by
  intro N hN hnorm
  set φ : Γ ≃* Γ := MulAut.conj w with hφ
  set N' : Subgroup Γ := N.map φ.symm.toMonoidHom with hN'
  have hmapN : N'.map φ.toMonoidHom = N := by
    rw [hN', Subgroup.map_map]
    have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id Γ := by ext x; simp
    rw [this, Subgroup.map_id]
  have hN'S : N' ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 (hN hy)
    have : φ.symm y = b := by rw [← hby]; simp
    simpa [this] using hb
  have hnorm' : (N'.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hN'S]
    intro n g hn hg
    have hn' : φ n ∈ N := by rw [← hmapN]; exact Subgroup.mem_map_of_mem _ hn
    have hg' : φ g ∈ S.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ hg
    have := (Subgroup.normal_subgroupOf_iff hN).1 hnorm (φ n) (φ g) hn' hg'
    have h2 : φ (g * n * g⁻¹) ∈ N := by simpa using this
    rw [← hmapN] at h2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h2
    exact φ.injective hyx ▸ hy
  rcases hS N' hN'S hnorm' with h0 | h0
  · left
    rw [← hmapN, h0, Subgroup.map_bot]
  · right
    rw [← hmapN, h0]

@[expose] noncomputable def orbitRoot (p : ℕ) (T W : Subgroup Γ) (hW : W ≤ Subgroup.normalizer (T : Set Γ))
    (Std : Set (Subgroup Γ))
    (hsimple : ∀ S ∈ Std, ∀ N : Subgroup Γ, N ≤ S → (N.subgroupOf S).Normal → N = ⊥ ∨ N = S)
    (hne : ∀ B ∈ blockOrbit W Std, ¬ T ≤ Subgroup.centralizer (B : Set Γ))
    (hinj : ∀ B ∈ blockOrbit W Std, ∀ B' ∈ blockOrbit W Std,
      T ⊓ Subgroup.centralizer (B : Set Γ) = T ⊓ Subgroup.centralizer (B' : Set Γ) → B = B')
    (hder : ∀ S : Subgroup Γ, S ≤ T →
      (S.relIndex T = p ∨ ∃ e : Γ, e ∈ T ∧ e ≠ 1 ∧ S = Subgroup.zpowers e) →
      ⁅Subgroup.centralizer (S : Set Γ), Subgroup.centralizer (S : Set Γ)⁆ ≤
        ⨆ B : {B : ↥(blockOrbit W Std) // S ≤ T ⊓ Subgroup.centralizer (B.1 : Set Γ)}, B.1.1) :
    RootData p T where
  ι := ↥(blockOrbit W Std)
  block B := B.1
  hyp B := T ⊓ Subgroup.centralizer (B.1 : Set Γ)
  W := W
  W_le := hW
  hyp_le _ := inf_le_left
  hyp_ne B h := hne B.1 B.2 (by rw [← h]; exact inf_le_right)
  hyp_inj B B' h := Subtype.ext (hinj B.1 B.2 B'.1 B'.2 h)
  block_le B := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 ht).2 x hx).symm
  block_simple B N hN hnorm := by
    obtain ⟨w, -, S, hS, hB⟩ := B.2
    have hB' : B.1 = S.map (MulAut.conj w).toMonoidHom := hB
    rw [hB'] at hN hnorm ⊢
    exact block_simple_map (hsimple S hS) w N hN hnorm
  derived_le := hder
  weyl w hw B := by
    refine ⟨⟨B.1.map (MulAut.conj w).toMonoidHom, conj_mem_blockOrbit B.2 hw⟩, rfl, ?_⟩
    exact map_conj_inf_centralizer (hW hw) B.1

theorem orbitRoot_genBlocks (p : ℕ) (T W : Subgroup Γ) (hW : W ≤ Subgroup.normalizer (T : Set Γ))
    (Std : Set (Subgroup Γ))
    (hsimple : ∀ S ∈ Std, ∀ N : Subgroup Γ, N ≤ S → (N.subgroupOf S).Normal → N = ⊥ ∨ N = S)
    (hne : ∀ B ∈ blockOrbit W Std, ¬ T ≤ Subgroup.centralizer (B : Set Γ))
    (hinj : ∀ B ∈ blockOrbit W Std, ∀ B' ∈ blockOrbit W Std,
      T ⊓ Subgroup.centralizer (B : Set Γ) = T ⊓ Subgroup.centralizer (B' : Set Γ) → B = B')
    (hder : ∀ S : Subgroup Γ, S ≤ T →
      (S.relIndex T = p ∨ ∃ e : Γ, e ∈ T ∧ e ≠ 1 ∧ S = Subgroup.zpowers e) →
      ⁅Subgroup.centralizer (S : Set Γ), Subgroup.centralizer (S : Set Γ)⁆ ≤
        ⨆ B : {B : ↥(blockOrbit W Std) // S ≤ T ⊓ Subgroup.centralizer (B.1 : Set Γ)}, B.1.1)
    (hgen : ∀ Std' : Set (Subgroup Γ), Std' ⊆ Std → Std' ≠ Std →
      ∃ P : Subgroup Γ, P ≠ ⊤ ∧ ∀ B ∈ blockOrbit W Std', B ≤ P) :
    (orbitRoot p T W hW Std hsimple hne hinj hder).GenBlocks := by
  classical
  intro J hJ hgenJ
  set Std' : Set (Subgroup Γ) := {S | S ∈ Std ∧ ∃ i ∈ J, i.1 ∈ blockOrbit W {S}} with hStd'
  have hsub : Std' ⊆ Std := fun S hS => hS.1
  have hJorb : ∀ i ∈ J, i.1 ∈ blockOrbit W Std' := by
    intro i hi
    obtain ⟨w, hw, S, hS, hiS⟩ := i.2
    refine ⟨w, hw, S, ⟨hS, i, hi, ⟨w, hw, S, rfl, hiS⟩⟩, hiS⟩
  have hStd'eq : Std' = Std := by
    by_contra hne'
    obtain ⟨P, hP, hPB⟩ := hgen Std' hsub hne'
    apply hP
    rw [eq_top_iff, ← hgenJ]
    exact iSup₂_le fun i hi => hPB _ (hJorb i hi)
  rw [Set.eq_univ_iff_forall]
  intro B
  obtain ⟨w, hw, S, hS, hB⟩ := B.2
  have hSStd' : S ∈ Std' := by rw [hStd'eq]; exact hS
  obtain ⟨-, i, hiJ, w', hw', S', hS', hiS'⟩ := hSStd'
  have hS'S : S' = S := by simpa using hS'
  subst hS'S
  have hstable := hJ (w * w'⁻¹) (W.mul_mem hw (W.inv_mem hw')) i hiJ
  obtain ⟨j, hjJ, hjb, -⟩ := hstable
  have hji : j = B := by
    apply Subtype.ext
    have h1 : (i.1).map (MulAut.conj (w * w'⁻¹)).toMonoidHom = j.1 := hjb
    rw [← h1, hiS', hB, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [← hji]
  exact hjJ

theorem not_le_centralizer_of_std {T W : Subgroup Γ} (hW : W ≤ Subgroup.normalizer (T : Set Γ))
    {Std : Set (Subgroup Γ)} (hne : ∀ S ∈ Std, ¬ T ≤ Subgroup.centralizer (S : Set Γ)) :
    ∀ B ∈ blockOrbit W Std, ¬ T ≤ Subgroup.centralizer (B : Set Γ) := by
  rintro B ⟨w, hw, S, hS, rfl⟩ hle
  apply hne S hS
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hwn := hW hw
  rw [Subgroup.mem_normalizer_iff] at hwn
  have hT : w * t * w⁻¹ ∈ T := (hwn t).1 ht
  have h2 := Subgroup.mem_centralizer_iff.1 (hle hT) (w * s * w⁻¹)
    (Subgroup.mem_map.2 ⟨s, hs, by simp [MulAut.conj_apply]⟩)
  have h3 : w * (s * t) * w⁻¹ = w * (t * s) * w⁻¹ := by
    calc w * (s * t) * w⁻¹ = (w * s * w⁻¹) * (w * t * w⁻¹) := by group
      _ = (w * t * w⁻¹) * (w * s * w⁻¹) := h2
      _ = w * (t * s) * w⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h3)

theorem hinj_of_std {T W : Subgroup Γ} (hW : W ≤ Subgroup.normalizer (T : Set Γ))
    {Std : Set (Subgroup Γ)}
    (hred : ∀ S ∈ Std, ∀ B' ∈ blockOrbit W Std,
      T ⊓ Subgroup.centralizer (S : Set Γ) = T ⊓ Subgroup.centralizer (B' : Set Γ) → B' = S) :
    ∀ B ∈ blockOrbit W Std, ∀ B' ∈ blockOrbit W Std,
      T ⊓ Subgroup.centralizer (B : Set Γ) = T ⊓ Subgroup.centralizer (B' : Set Γ) → B = B' := by
  rintro B ⟨w, hw, S, hS, rfl⟩ B' ⟨w', hw', S', hS', rfl⟩ h
  set u : Γ := w⁻¹ * w' with hu
  have huW : u ∈ W := W.mul_mem (W.inv_mem hw) hw'
  set B'' : Subgroup Γ := S'.map (MulAut.conj u).toMonoidHom with hB''
  have hB''orb : B'' ∈ blockOrbit W Std := ⟨u, huW, S', hS', rfl⟩
  have hwinv := hW (W.inv_mem hw)
  have h1 := congrArg (Subgroup.map (MulAut.conj w⁻¹).toMonoidHom) h
  rw [map_conj_inf_centralizer hwinv, map_conj_inf_centralizer hwinv] at h1
  have e1 : (S.map (MulAut.conj w).toMonoidHom).map (MulAut.conj w⁻¹).toMonoidHom = S := by
    rw [Subgroup.map_map]
    have : (MulAut.conj w⁻¹).toMonoidHom.comp (MulAut.conj w).toMonoidHom = MonoidHom.id Γ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [this, Subgroup.map_id]
  have e2 : (S'.map (MulAut.conj w').toMonoidHom).map (MulAut.conj w⁻¹).toMonoidHom = B'' := by
    rw [Subgroup.map_map, hB'', hu, conj_mul_toMonoidHom]
  rw [e1, e2] at h1
  have hB''S := hred S hS B'' hB''orb h1
  have e3 : B''.map (MulAut.conj w).toMonoidHom = S'.map (MulAut.conj w').toMonoidHom := by
    rw [hB'', Subgroup.map_map, ← conj_mul_toMonoidHom, hu, mul_inv_cancel_left]
  rw [← e3, hB''S]

end CFSG.RankThree.PartOne.KFCL
