module

public import CFSG.RankThree.GF2n.Smith81.OrthE1LemmaCNonsplit

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.Open Module

namespace LCData

variable {K : Type} [Field K] [CharP K 2] {S : QSpace K} {V : Submodule K S.E}
  {Xg : Subgroup (S.E ≃ₗ[K] S.E)}

theorem pf_comm (D : LCData S V Xg) (v w : V) : D.pf v w = D.pf w v := by
  have h := D.pf_alt (v + w)
  simp only [map_add, LinearMap.add_apply, D.pf_alt, zero_add, add_zero] at h
  exact (CharTwo.add_eq_zero.mp h).symm

structure Split (D : LCData S V Xg) where
  V' : Submodule K S.E
  hc : IsCompl V V'
  hinv : ∀ g ∈ Xg, ∀ v ∈ V', g v ∈ V'

variable {D : LCData S V Xg}

namespace Split

variable (Sp : D.Split)

@[expose] noncomputable def βV' : Sp.V' →ₗ[K] V := D.β0 ∘ₗ Sp.V'.subtype

theorem βV'_injective : Function.Injective Sp.βV' := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h1 : (v : S.E) ∈ V := (D.β0_eq_zero_iff _).1 hv
  exact Subtype.ext ((Submodule.disjoint_def.1 Sp.hc.disjoint) v h1 v.2)

theorem finrank_V' : Module.finrank K Sp.V' = 4 := by
  have h := Submodule.finrank_add_eq_of_isCompl Sp.hc
  rw [D.dimV, D.dimE] at h
  omega

@[expose] noncomputable def eV : Sp.V' ≃ₗ[K] V :=
  LinearEquiv.ofBijective Sp.βV' ⟨Sp.βV'_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Sp.finrank_V', D.dimV])).mp Sp.βV'_injective⟩

@[expose] noncomputable def τ : V →ₗ[K] S.E := Sp.V'.subtype ∘ₗ Sp.eV.symm.toLinearMap

theorem β0_τ (w : V) : D.β0 (Sp.τ w) = w := by
  have h : Sp.eV (Sp.eV.symm w) = w := Sp.eV.apply_symm_apply w
  exact h

theorem τ_mem (w : V) : Sp.τ w ∈ Sp.V' := (Sp.eV.symm w).2

theorem τ_act (g : ↥Xg) (w : V) : Sp.τ (D.act g w) = (g : S.E ≃ₗ[K] S.E) (Sp.τ w) := by
  have h1 : Sp.τ (D.act g w) ∈ Sp.V' := Sp.τ_mem _
  have h2 : (g : S.E ≃ₗ[K] S.E) (Sp.τ w) ∈ Sp.V' := Sp.hinv g g.2 _ (Sp.τ_mem w)
  have h3 : Sp.βV' ⟨_, h1⟩ = Sp.βV' ⟨_, h2⟩ := by
    change D.β0 (Sp.τ (D.act g w)) = D.β0 ((g : S.E ≃ₗ[K] S.E) (Sp.τ w))
    rw [Sp.β0_τ, D.β0_act, Sp.β0_τ]
  exact congrArg Subtype.val (Sp.βV'_injective h3)

theorem B_τ (w w' : V) : S.B (Sp.τ w) w' = D.pf w w' := by
  rw [← D.pf_β0, Sp.β0_τ]

@[expose] noncomputable def Θ : (V × V) ≃ₗ[K] S.E :=
  (LinearEquiv.prodCongr (LinearEquiv.refl K V) Sp.eV.symm).trans
    (Submodule.prodEquivOfIsCompl V Sp.V' Sp.hc)

theorem Θ_apply (v w : V) : Sp.Θ (v, w) = (v : S.E) + Sp.τ w := rfl

theorem act_Θ (g : ↥Xg) (v w : V) :
    (g : S.E ≃ₗ[K] S.E) (Sp.Θ (v, w)) = Sp.Θ (D.act g v, D.act g w) := by
  rw [Θ_apply, Θ_apply, map_add, D.act_coe, τ_act]

theorem β0_Θ (v w : V) : D.β0 (Sp.Θ (v, w)) = w := by
  rw [Θ_apply, map_add, (D.β0_eq_zero_iff _).2 v.2, zero_add, Sp.β0_τ]

theorem β_Θ (v w : V) : D.β (Sp.Θ (v, w)) = (w : S.E) := by
  rw [β_apply, Sp.β0_Θ]

theorem blocks (φ : S.E →ₗ[K] S.E)
    (hcomm : ∀ (x : ↥Xg) e, φ ((x : S.E ≃ₗ[K] S.E) e) = (x : S.E ≃ₗ[K] S.E) (φ e)) :
    ∃ a b c d : K, ∀ v w : V, φ (Sp.Θ (v, w)) = Sp.Θ (a • v + b • w, c • v + d • w) := by
  let φΘ : V × V →ₗ[K] V × V := Sp.Θ.symm.toLinearMap ∘ₗ φ ∘ₗ Sp.Θ.toLinearMap
  have hΘ : ∀ (x : ↥Xg) (p : V × V), φΘ (D.act x p.1, D.act x p.2) =
      (D.act x (φΘ p).1, D.act x (φΘ p).2) := by
    intro x p
    have h1 : φ (Sp.Θ (D.act x p.1, D.act x p.2)) = Sp.Θ (D.act x (φΘ p).1, D.act x (φΘ p).2) := by
      rw [← Sp.act_Θ, hcomm, ← Sp.act_Θ]
      simp [φΘ]
    simpa [φΘ] using congrArg Sp.Θ.symm h1
  have blk : ∀ (π : V × V →ₗ[K] V) (ι : V →ₗ[K] V × V),
      (∀ (x : ↥Xg) (v : V), ι (D.act x v) = (D.act x (ι v).1, D.act x (ι v).2)) →
      (∀ (x : ↥Xg) (p : V × V), π (D.act x p.1, D.act x p.2) = D.act x (π p)) →
      ∃ c : K, ∀ v, π (φΘ (ι v)) = c • v := by
    intro π ι hι hπ
    obtain ⟨c, hc⟩ := D.schur (π ∘ₗ φΘ ∘ₗ ι) (by
      intro x v
      simp only [LinearMap.comp_apply]
      rw [hι x v, hΘ x (ι v), hπ x])
    exact ⟨c, hc⟩
  obtain ⟨a, ha⟩ := blk (LinearMap.fst K V V) (LinearMap.inl K V V) (by simp) (fun _ _ => rfl)
  obtain ⟨b, hb⟩ := blk (LinearMap.fst K V V) (LinearMap.inr K V V) (by simp) (fun _ _ => rfl)
  obtain ⟨c, hc⟩ := blk (LinearMap.snd K V V) (LinearMap.inl K V V) (by simp) (fun _ _ => rfl)
  obtain ⟨d, hd⟩ := blk (LinearMap.snd K V V) (LinearMap.inr K V V) (by simp) (fun _ _ => rfl)
  refine ⟨a, b, c, d, fun v w => ?_⟩
  have h1 : φ (Sp.Θ (v, w)) = Sp.Θ (φΘ (v, w)) := by simp [φΘ]
  have h2 : φΘ (v, w) = (a • v + b • w, c • v + d • w) := by
    have hp : (v, w) = (v, 0) + (0, w) := by simp
    rw [hp, map_add]
    refine Prod.ext ?_ ?_
    · have e1 := ha v
      have e2 := hb w
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
        LinearMap.fst_apply] at e1 e2
      simp [e1, e2]
    · have e1 := hc v
      have e2 := hd w
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
        LinearMap.snd_apply] at e1 e2
      simp [e1, e2]
  rw [h1, h2]

@[expose] noncomputable def ν (w : V) : K := S.Qf (Sp.τ w)

theorem Qf_Θ (v w : V) : S.Qf (Sp.Θ (v, w)) = Sp.ν w + D.pf w v := by
  rw [Θ_apply, S.Qf_add, D.ts _ v.2, ν, S.B_comm (v : S.E) (Sp.τ w), Sp.B_τ, zero_add]

theorem ν_smul (c : K) (w : V) : Sp.ν (c • w) = c ^ 2 * Sp.ν w := by
  simp only [ν, map_smul]
  exact S.Qf_smul c _

theorem ν_add (w w' : V) :
    Sp.ν (w + w') = Sp.ν w + Sp.ν w' + S.B (Sp.τ w) (Sp.τ w') := by
  simp only [ν, map_add]
  exact S.Qf_add _ _

theorem ν_zero : Sp.ν 0 = 0 := by
  have := Sp.ν_smul 0 0
  simpa using this

theorem Qf_block (a b c d : K) (v w : V) :
    S.Qf (Sp.Θ (a • v + b • w, c • v + d • w)) =
      c ^ 2 * Sp.ν v + d ^ 2 * Sp.ν w + c * d * S.B (Sp.τ v) (Sp.τ w) +
        (c * b + d * a) * D.pf v w := by
  rw [Qf_Θ, ν_add, ν_smul, ν_smul]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, D.pf_alt, smul_eq_mul,
    D.pf_comm w v]
  ring

theorem iso_identity {g : S.E ≃ₗ[K] S.E} (hgO : g ∈ S.O) {a b c d : K}
    (hg : ∀ v w : V, g (Sp.Θ (v, w)) = Sp.Θ (a • v + b • w, c • v + d • w)) (v w : V) :
    c ^ 2 * Sp.ν v + d ^ 2 * Sp.ν w + c * d * S.B (Sp.τ v) (Sp.τ w) +
      (c * b + d * a) * D.pf v w = Sp.ν w + D.pf v w := by
  have h : S.Qf (g (Sp.Θ (v, w))) = S.Qf (Sp.Θ (v, w)) := hgO _
  rw [hg, Qf_block, Qf_Θ, D.pf_comm w v] at h
  simpa using h

end Split

theorem exists_pf_ne_zero : ∃ v w : V, D.pf v w ≠ 0 := by
  obtain ⟨v, hv, hne⟩ := D.exists_ne_zero
  by_contra h
  push Not at h
  exact hne (congrArg Subtype.val (D.pf_nondeg ⟨v, hv⟩ (h ⟨v, hv⟩)))

namespace Split

variable (Sp : D.Split)

theorem det_of_nu_zero (hν : ∀ w, Sp.ν w = 0) {g : S.E ≃ₗ[K] S.E} (hgO : g ∈ S.O)
    {a b c d : K}
    (hg : ∀ v w : V, g (Sp.Θ (v, w)) = Sp.Θ (a • v + b • w, c • v + d • w)) :
    c * b + d * a = 1 := by
  have hk : ∀ v w, S.B (Sp.τ v) (Sp.τ w) = 0 := by
    intro v w
    have := Sp.ν_add v w
    rw [hν, hν, hν] at this
    simpa using this.symm
  obtain ⟨v₀, w₀, hne⟩ := D.exists_pf_ne_zero
  have h := Sp.iso_identity hgO hg v₀ w₀
  rw [hν, hν, hk] at h
  have h2 : (c * b + d * a - 1) * D.pf v₀ w₀ = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hne)

theorem entries_of_nu_ne_zero {w₀ : V} (hw₀ : Sp.ν w₀ ≠ 0) {g : S.E ≃ₗ[K] S.E}
    (hgO : g ∈ S.O) {a b c d : K}
    (hg : ∀ v w : V, g (Sp.Θ (v, w)) = Sp.Θ (a • v + b • w, c • v + d • w)) :
    c = 0 ∧ d = 1 ∧ a = 1 := by
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc : c = 0 := by
    have h := Sp.iso_identity hgO hg w₀ 0
    simp only [Sp.ν_zero, map_zero, LinearMap.zero_apply, mul_zero, add_zero, zero_add] at h
    have h3 : c ^ 2 * Sp.ν w₀ = 0 := by simpa using h
    exact pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp h3).resolve_right hw₀)
  have hd : d = 1 := by
    have h := Sp.iso_identity hgO hg 0 w₀
    simp only [Sp.ν_zero, map_zero, LinearMap.zero_apply, mul_zero, add_zero, zero_add] at h
    have h3 : (d + 1) ^ 2 * Sp.ν w₀ = 0 := by linear_combination h + (d * Sp.ν w₀ + Sp.ν w₀) * h2'
    have h4 := pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp h3).resolve_right hw₀)
    exact (CharTwo.add_eq_zero.mp h4)
  refine ⟨hc, hd, ?_⟩
  obtain ⟨v₀, w₁, hne⟩ := D.exists_pf_ne_zero
  have h := Sp.iso_identity hgO hg v₀ w₁
  rw [hc, hd] at h
  have h3 : (a - 1) * D.pf v₀ w₁ = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hne)

theorem cent_of_nu_ne_zero {w₀ : V} (hw₀ : Sp.ν w₀ ≠ 0) {g : S.E ≃ₗ[K] S.E}
    (hgO : g ∈ S.O) {a b c d : K}
    (hg : ∀ v w : V, g (Sp.Θ (v, w)) = Sp.Θ (a • v + b • w, c • v + d • w)) :
    ∃ b : K, ∀ e, g e = e + b • D.β e := by
  obtain ⟨hc, hd, ha⟩ := Sp.entries_of_nu_ne_zero hw₀ hgO hg
  refine ⟨b, fun e => ?_⟩
  obtain ⟨⟨v, w⟩, rfl⟩ := Sp.Θ.surjective e
  rw [hg v w, hc, hd, ha, β_Θ]
  simp only [Θ_apply, zero_smul, zero_add, one_smul, Submodule.coe_add, Submodule.coe_smul]
  abel

@[expose] noncomputable def blockMap (W : Type) [AddCommGroup W] [Module K W]
    (M : Matrix (Fin 2) (Fin 2) K) : Module.End K (W × W) :=
  LinearMap.prod (M 0 0 • LinearMap.fst K W W + M 0 1 • LinearMap.snd K W W)
    (M 1 0 • LinearMap.fst K W W + M 1 1 • LinearMap.snd K W W)

theorem blockMap_apply {W : Type} [AddCommGroup W] [Module K W] (M : Matrix (Fin 2) (Fin 2) K)
    (v w : W) : blockMap W M (v, w) = (M 0 0 • v + M 0 1 • w, M 1 0 • v + M 1 1 • w) := rfl

theorem blockMap_mul (W : Type) [AddCommGroup W] [Module K W] (M N : Matrix (Fin 2) (Fin 2) K) :
    blockMap W (M * N) = blockMap W M * blockMap W N := by
  refine LinearMap.ext fun p => ?_
  obtain ⟨v, w⟩ := p
  rw [Module.End.mul_apply, blockMap_apply, blockMap_apply, blockMap_apply]
  refine Prod.ext ?_ ?_
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, smul_add, smul_smul, add_smul]
    abel
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, smul_add, smul_smul, add_smul]
    abel

theorem blockMap_one (W : Type) [AddCommGroup W] [Module K W] :
    blockMap W (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  refine LinearMap.ext fun p => ?_
  obtain ⟨v, w⟩ := p
  simp [blockMap_apply]

@[expose] noncomputable def φMhom : Matrix (Fin 2) (Fin 2) K →* Module.End K S.E where
  toFun M := Sp.Θ.toLinearMap ∘ₗ blockMap V M ∘ₗ Sp.Θ.symm.toLinearMap
  map_one' := by
    rw [blockMap_one V]
    ext e
    simp
  map_mul' M N := by
    rw [blockMap_mul V]
    ext e
    simp [Module.End.mul_apply]

theorem φMhom_Θ (M : Matrix (Fin 2) (Fin 2) K) (v w : V) :
    Sp.φMhom M (Sp.Θ (v, w)) = Sp.Θ (M 0 0 • v + M 0 1 • w, M 1 0 • v + M 1 1 • w) := by
  change Sp.Θ (blockMap V M (Sp.Θ.symm (Sp.Θ (v, w)))) = _
  rw [LinearEquiv.symm_apply_apply, blockMap_apply]

theorem φMhom_comm (M : Matrix (Fin 2) (Fin 2) K) (x : ↥Xg) (e : S.E) :
    (x : S.E ≃ₗ[K] S.E) (Sp.φMhom M e) = Sp.φMhom M ((x : S.E ≃ₗ[K] S.E) e) := by
  obtain ⟨⟨v, w⟩, rfl⟩ := Sp.Θ.surjective e
  rw [Sp.act_Θ, φMhom_Θ, φMhom_Θ, Sp.act_Θ]
  simp only [map_add, map_smul]

theorem φMhom_isometry (hν : ∀ w, Sp.ν w = 0) (M : Matrix (Fin 2) (Fin 2) K)
    (hdet : M.det = 1) (e : S.E) : S.Qf (Sp.φMhom M e) = S.Qf e := by
  have hk : ∀ v w, S.B (Sp.τ v) (Sp.τ w) = 0 := by
    intro v w
    have := Sp.ν_add v w
    rw [hν, hν, hν] at this
    simpa using this.symm
  obtain ⟨⟨v, w⟩, rfl⟩ := Sp.Θ.surjective e
  rw [φMhom_Θ, Qf_block, Qf_Θ]
  simp only [hν, hk, D.pf_comm w v]
  rw [Matrix.det_fin_two, CharTwo.sub_eq_add] at hdet
  have : M 1 0 * M 0 1 + M 1 1 * M 0 0 = 1 := by linear_combination hdet
  rw [this]
  ring

theorem iso_of_nu_zero (hν : ∀ w, Sp.ν w = 0) :
    Nonempty (↥(StatedSL 2 K) ≃* ↥(S.Cent (Xg : Set (S.E ≃ₗ[K] S.E)))) := by
  let Φ0 : GL (Fin 2) K →* (S.E ≃ₗ[K] S.E) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K S.E).toMonoidHom.comp
      (Units.map Sp.φMhom)
  have hΦ0 : ∀ (A : GL (Fin 2) K) (e : S.E), Φ0 A e = Sp.φMhom (A : Matrix (Fin 2) (Fin 2) K) e :=
    fun _ _ => rfl
  have hmem : ∀ A : ↥(StatedSL 2 K), Φ0 A ∈ S.Cent (Xg : Set (S.E ≃ₗ[K] S.E)) := by
    intro A
    rw [S.mem_Cent_iff]
    refine ⟨fun e => ?_, fun x hx e => ?_⟩
    · rw [hΦ0]
      exact Sp.φMhom_isometry hν _ (CFSG.Open.StatedAPI.det_of_mem_statedSL A.2) e
    · rw [hΦ0, hΦ0]
      exact Sp.φMhom_comm _ ⟨x, hx⟩ e
  let Φ : ↥(StatedSL 2 K) →* ↥(S.Cent (Xg : Set (S.E ≃ₗ[K] S.E))) :=
    ((Φ0.comp (StatedSL 2 K).subtype).codRestrict _ hmem)
  refine ⟨MulEquiv.ofBijective Φ ⟨?_, ?_⟩⟩
  · intro A B hAB
    have h : ∀ e, Sp.φMhom (A.1 : Matrix (Fin 2) (Fin 2) K) e =
        Sp.φMhom (B.1 : Matrix (Fin 2) (Fin 2) K) e := fun e =>
      congrArg (fun g : ↥(S.Cent (Xg : Set (S.E ≃ₗ[K] S.E))) => (g : S.E ≃ₗ[K] S.E) e) hAB
    obtain ⟨v₀, hv₀, hne⟩ := D.exists_ne_zero
    have hu0 : (⟨v₀, hv₀⟩ : V) ≠ 0 := fun h0 => hne (congrArg Subtype.val h0)
    have h1 := h (Sp.Θ (⟨v₀, hv₀⟩, 0))
    have h2 := h (Sp.Θ (0, ⟨v₀, hv₀⟩))
    rw [φMhom_Θ, φMhom_Θ] at h1 h2
    replace h1 := Sp.Θ.injective h1
    replace h2 := Sp.Θ.injective h2
    simp only [smul_zero, add_zero, zero_add, Prod.mk.injEq] at h1 h2
    have e00 := smul_left_injective K hu0 h1.1
    have e10 := smul_left_injective K hu0 h1.2
    have e01 := smul_left_injective K hu0 h2.1
    have e11 := smul_left_injective K hu0 h2.2
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> assumption
  · rintro ⟨g, hg⟩
    obtain ⟨hgO, hgc⟩ := (S.mem_Cent_iff _ g).1 hg
    obtain ⟨a, b, c, d, hblk⟩ :=
      Sp.blocks (g : S.E →ₗ[K] S.E) (fun x e => (hgc x x.2 e).symm)
    have hdet1 := Sp.det_of_nu_zero hν hgO (fun v w => hblk v w)
    let M : Matrix (Fin 2) (Fin 2) K := !![a, b; c, d]
    have hdet : M.det = 1 := by
      rw [Matrix.det_fin_two, CharTwo.sub_eq_add]
      simp only [M, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val_zero]
      linear_combination hdet1
    let A : GL (Fin 2) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero)
    have hAM : (A : Matrix (Fin 2) (Fin 2) K) = M := rfl
    have hA : A ∈ StatedSL 2 K := CFSG.Open.StatedAPI.mem_statedSL_of_det (by rw [hAM]; exact hdet)
    refine ⟨⟨A, hA⟩, ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro e
    obtain ⟨⟨v, w⟩, rfl⟩ := Sp.Θ.surjective e
    change Φ0 A (Sp.Θ (v, w)) = g (Sp.Θ (v, w))
    rw [hΦ0, hAM, φMhom_Θ]
    have := hblk v w
    simpa [M] using this.symm

theorem split_dichotomy (Sp : D.Split) :
    ((∃ w, Sp.ν w ≠ 0) ∧ ∀ g ∈ S.Cent (Xg : Set (S.E ≃ₗ[K] S.E)), ∃ c : K,
        ∀ e, g e = e + c • D.β e) ∨
      ((∀ w, Sp.ν w = 0) ∧
        Nonempty (↥(StatedSL 2 K) ≃* ↥(S.Cent (Xg : Set (S.E ≃ₗ[K] S.E))))) := by
  by_cases hν : ∀ w, Sp.ν w = 0
  · exact Or.inr ⟨hν, Sp.iso_of_nu_zero hν⟩
  · left
    push Not at hν
    refine ⟨hν, fun g hg => ?_⟩
    obtain ⟨w₀, hw₀⟩ := hν
    obtain ⟨hgO, hgc⟩ := (S.mem_Cent_iff _ g).1 hg
    obtain ⟨a, b, c, d, hblk⟩ :=
      Sp.blocks (g : S.E →ₗ[K] S.E) (fun x e => (hgc x x.2 e).symm)
    exact Sp.cent_of_nu_ne_zero hw₀ hgO (fun v w => hblk v w)

theorem split_cent (Sp : D.Split) :
    (∀ g ∈ S.Cent (Xg : Set (S.E ≃ₗ[K] S.E)), ∃ c : K, ∀ e, g e = e + c • D.β e) ∨
      Nonempty (↥(StatedSL 2 K) ≃* ↥(S.Cent (Xg : Set (S.E ≃ₗ[K] S.E)))) :=
  (Sp.split_dichotomy).imp And.right And.right

end Split

@[expose] noncomputable def unip (D : LCData S V Xg) (c : K) : S.E ≃ₗ[K] S.E :=
  LinearEquiv.ofLinear (LinearMap.id + c • D.β) (LinearMap.id + c • D.β)
    (by
      ext e
      have h2 : ∀ x : S.E, x + x = 0 := fun x => by rw [← two_smul K x, CharTwo.two_eq_zero,
        zero_smul]
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
        LinearMap.smul_apply, map_add, map_smul, D.β_β, smul_zero, add_zero, LinearMap.id_coe,
        id_eq]
      rw [add_assoc, h2, add_zero])
    (by
      ext e
      have h2 : ∀ x : S.E, x + x = 0 := fun x => by rw [← two_smul K x, CharTwo.two_eq_zero,
        zero_smul]
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
        LinearMap.smul_apply, map_add, map_smul, D.β_β, smul_zero, add_zero, LinearMap.id_coe,
        id_eq]
      rw [add_assoc, h2, add_zero])

theorem unip_apply (D : LCData S V Xg) (c : K) (e : S.E) : D.unip c e = e + c • D.β e := rfl

theorem unip_mem (D : LCData S V Xg) (c : K) : D.unip c ∈ S.Cent (Xg : Set (S.E ≃ₗ[K] S.E)) := by
  rw [S.mem_Cent_iff]
  refine ⟨fun e => ?_, fun x hx e => ?_⟩
  · rw [unip_apply]
    exact D.Qf_add_smul_β c e
  · rw [unip_apply, unip_apply, map_add, map_smul, ← D.β_act ⟨x, hx⟩ e]

theorem conclusion (D : LCData S V Xg) : LemmaCConclusion S V Xg := by
  unfold LemmaCConclusion
  refine ⟨D.β, D.betaProps, fun x hx e => (D.β_act ⟨x, hx⟩ e).symm,
    fun c => ⟨D.unip c, D.unip_mem c, fun e => rfl⟩, ?_⟩
  by_cases hns : HasInvComplement S V Xg
  · obtain ⟨V', hc, hinv⟩ := hns
    exact (Split.mk V' hc hinv : D.Split).split_cent
  · exact Or.inl fun g hg => D.nonsplit_cent hns hg

end LCData

end CFSG.RankThree.GF2n.Smith81.Smith23E1
