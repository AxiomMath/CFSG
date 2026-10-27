module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3aSmul
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Orbit

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.RootSystem

private theorem levTwoS3a_lam_eq {τ : Tag} {p : ℕ} [NeZero p] {c : Fin τ.rank → ZMod p}
    {m : Fin τ.rank → ℤ} (hm : ∀ i, c i = (m i : ZMod p)) (β : Fin τ.rank → ℤ) :
    lam c β = ((β ⬝ᵥ m : ℤ) : ZMod p) := by
  rw [lam]
  rw [show (∑ j, (β j : ZMod p) * c j) =
      ∑ j, (β j : ZMod p) * (m j : ZMod p) from
    Finset.sum_congr rfl fun j _ => by rw [hm j]]
  rw [dotProduct]
  push_cast
  ring

private theorem levTwoS3a_lam_normal {τ : Tag} {p : ℕ} [NeZero p] {c : Fin τ.rank → ZMod p}
    {lam₀ : Fin τ.rank → ℤ} (hm : ∀ i, c i = (lam₀ i : ZMod p))
    (μ : Fin τ.rank → ℤ) (w : WeylGroup τ)
    (hw : ∀ β, (p : ℤ) ∣ (w • β) ⬝ᵥ μ - β ⬝ᵥ lam₀) (β : Fin τ.rank → ℤ) :
    lam (fun i => (μ i : ZMod p)) (weylAction (isFiniteType_cartan τ) w β) = lam c β := by
  rw [levTwoS3a_lam_eq (c := fun i => (μ i : ZMod p)) (m := μ) (fun i => rfl)
      (weylAction (isFiniteType_cartan τ) w β),
    levTwoS3a_lam_eq hm β]
  obtain ⟨m, hm'⟩ := hw β
  have h : (w • β) ⬝ᵥ μ = β ⬝ᵥ lam₀ + p * m := by linarith
  change (((w • β) ⬝ᵥ μ : ℤ) : ZMod p) = ((β ⬝ᵥ lam₀ : ℤ) : ZMod p)
  rw [h]
  push_cast
  rw [show (p : ZMod p) = 0 from ZMod.natCast_self p]
  ring

theorem levTwoS3a_engine
    {τ : Tag} (K : KacData τ) (hK : K.Facts)
    (htrans : ∀ α β : Fin τ.rank → ℤ, IsRoot τ α → IsRoot τ β → iform α α = iform β β →
      ∃ w : WeylGroup τ, w • α = β)
    (hrk : ∀ (k : ℕ) (p : ℕ), p.Prime → p ≠ 2 → 3 ≤ k → τ.rank ≤ k + 2 →
      (τ.rank ≤ k + 1 ∨ (p : ℤ) ∣ (τ.cartan).det) → ExcRankOK τ k)
    (hexc : ExcFinite τ K) :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (c : Fin τ.rank → ZMod p) (Φ : Set (Fin τ.rank → ℤ)),
      LevTwoData (isFiniteType_cartan τ) p c Φ → TCRoot (isFiniteType_cartan τ) Φ := by
  intro p hp hp2 c Φ hd
  obtain ⟨κ, hκpos, hform⟩ := levTwoS3a_form_eq τ
  have hκ : κ ≠ 0 := ne_of_gt hκpos
  have hp0 : 0 < p := hp.pos
  have : NeZero p := ⟨hp0.ne'⟩
  let lamZ : Fin τ.rank → ℤ := fun i => ((c i).val : ℤ)
  have hm : ∀ i, c i = (lamZ i : ZMod p) := by
    intro i
    change c i = (((c i).val : ℤ) : ZMod p)
    rw [Int.cast_natCast]
    exact ((ZMod.natCast_val (R := ZMod p) (c i)).trans (ZMod.cast_id p (c i))).symm
  obtain ⟨w, μ, hw, hμ⟩ := K.exists_normal p hp0 lamZ
  let c' : Fin τ.rank → ZMod p := fun i => (μ i : ZMod p)
  have hc : ∀ β, lam c' (weylAction (isFiniteType_cartan τ) w β) = lam c β :=
    fun β => levTwoS3a_lam_normal hm μ w hw β
  have hd₁ : LevTwoData (isFiniteType_cartan τ) p c'
      (weylAction (isFiniteType_cartan τ) w '' Φ) :=
    levTwoS3a_levTwoData_smul hd w hc
  classical
  obtain ⟨s₀, hs₀, -, h3₀, -, -⟩ := hd.rank
  obtain ⟨α₀, hα₀s⟩ := Finset.card_pos.1 (by omega : 0 < s₀.card)
  have hα₀ : α₀ ∈ Φ := hs₀ hα₀s
  let l : ℤ := iform α₀ α₀
  let D : Finset (Option (Fin τ.rank)) := Finset.univ.filter fun x => K.IsZ p μ x
  have hD : D ≠ Finset.univ := by
    intro hDuniv
    by_cases hnone : none ∈ D
    · have hθμ : K.θ ⬝ᵥ μ = p := by
        have h := (Finset.mem_filter.1 hnone).2
        simpa [KacData.IsZ] using h
      obtain ⟨j, hj⟩ : ∃ j, μ j ≠ 0 := by
        by_contra h
        push Not at h
        have h0 : K.θ ⬝ᵥ μ = 0 := by
          rw [dotProduct]
          exact Finset.sum_eq_zero fun j _ => by rw [h j, mul_zero]
        omega
      have hsome : some j ∉ D := by
        simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [KacData.IsZ] using hj
      exact hsome (hDuniv ▸ Finset.mem_univ (some j))
    · exact hnone (hDuniv ▸ Finset.mem_univ none)
  have hΦ₁ : weylAction (isFiniteType_cartan τ) w '' Φ = partOf K (D : Set _) l := by
    ext γ
    constructor
    · rintro ⟨α, hα, rfl⟩
      have hroot : IsRoot τ (weylAction (isFiniteType_cartan τ) w α) :=
        IsRoot.smul ((levTwoS3a_isRt_iff).1 (hd.isRt α hα)) w
      have hzero : lam c' (weylAction (isFiniteType_cartan τ) w α) = 0 :=
        hd₁.fix _ ⟨α, hα, rfl⟩
      have hdvd : (p : ℤ) ∣ (weylAction (isFiniteType_cartan τ) w α) ⬝ᵥ μ := by
        have h0 : (((weylAction (isFiniteType_cartan τ) w α) ⬝ᵥ μ : ℤ) : ZMod p) = 0 := by
          rw [← levTwoS3a_lam_eq (c := c') (m := μ) (fun i => rfl) _]
          exact hzero
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h0
      obtain ⟨n, hn, hγn⟩ := K.exists_combo_of_dvd hK hp0 hμ hroot hdvd
      refine ⟨⟨hroot, n, ?_, hγn⟩, ?_⟩
      · intro x hx
        exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ x, hn x hx⟩)
      · change iform (w • α) (w • α) = l
        rw [iform_smul]
        exact (levTwoS3a_form_norm_eq_iff hκ hform).1 (hd.oneLen α hα α₀ hα₀)
    · intro hγ
      obtain ⟨hγroots, hγnorm⟩ := hγ
      obtain ⟨hγroot, n, hn, hγn⟩ := hγroots
      have hdvd : (p : ℤ) ∣ γ ⬝ᵥ μ := by
        have hcombo : (p : ℤ) ∣ K.combo n ⬝ᵥ μ := K.combo_dvd fun x hx =>
          (Finset.mem_filter.1 (Finset.mem_coe.1 (hn x hx))).2
        rcases hγn with e | e
        · rw [e]; exact hcombo
        · rw [e, neg_dotProduct]; exact dvd_neg.2 hcombo
      have hzero : lam c' γ = 0 := by
        rw [levTwoS3a_lam_eq (c := c') (m := μ) (fun i => rfl) γ]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd
      have hα₀'root : IsRoot τ (weylAction (isFiniteType_cartan τ) w α₀) :=
        IsRoot.smul ((levTwoS3a_isRt_iff).1 (hd.isRt α₀ hα₀)) w
      have hnorm₀ : iform (weylAction (isFiniteType_cartan τ) w α₀)
          (weylAction (isFiniteType_cartan τ) w α₀) = iform γ γ := by
        change iform (w • α₀) (w • α₀) = iform γ γ
        rw [iform_smul]
        exact hγnorm.symm
      obtain ⟨v, hv⟩ := htrans _ γ hα₀'root hγroot hnorm₀
      exact hd₁.sat γ ((levTwoS3a_isRt_iff).2 hγroot) hzero ⟨_, ⟨α₀, hα₀, rfl⟩, v, hv⟩
  have hirr : ∀ α ∈ partOf K (D : Set _) l, ∀ β ∈ partOf K (D : Set _) l,
      Relation.ReflTransGen (fun a b => b ∈ partOf K (D : Set _) l ∧ iform a b ≠ 0) α β := by
    intro α hα β hβ
    have h := hd₁.irred α (hΦ₁ ▸ hα) β (hΦ₁ ▸ hβ)
    simpa only [hΦ₁, levTwoS3a_form_ne_zero_iff hκ hform] using h
  have hrank : ∃ s : Finset (Fin τ.rank → ℤ),
      (s : Set (Fin τ.rank → ℤ)) ⊆ partOf K (D : Set _) l ∧
      LinearIndependent ℚ (fun v : s => (fun i => ((v : Fin τ.rank → ℤ) i : ℚ))) ∧
      ExcRankOK τ s.card := by
    obtain ⟨s, hs, hind, h3, hcard, hdet⟩ := hd₁.rank
    refine ⟨s, ?_, ?_, hrk s.card p hp hp2 h3 (by simpa using hcard) (by simpa using hdet)⟩
    · rw [← hΦ₁]; exact hs
    · have hfun : (fun v : s => toRat (v : Fin τ.rank → ℤ)) =
          (fun v : s => fun i => ((v : Fin τ.rank → ℤ) i : ℚ)) := by
        funext v i
        rw [toRat_apply]
      rwa [hfun] at hind
  have htc : TCRoot (isFiniteType_cartan τ) (partOf K (D : Set _) l) :=
    hexc D l hD hirr hrank
  have hback : TCRoot (isFiniteType_cartan τ) Φ := by
    have h := tcRoot_smul (isFiniteType_cartan τ) hd₁.isRt w⁻¹ (hΦ₁ ▸ htc)
    have himg : weylAction (isFiniteType_cartan τ) w⁻¹ ''
        (weylAction (isFiniteType_cartan τ) w '' Φ) = Φ := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨weylAction (isFiniteType_cartan τ) w x, ⟨x, hx, rfl⟩,
          weylAction_inv_apply_apply (isFiniteType_cartan τ) w x⟩
    rwa [himg] at h
  exact hback

theorem levTwoS3a_trans_E8 :
    ∀ α β : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 α → IsRoot Tag.E8 β →
      iform α α = iform β β → ∃ w : WeylGroup Tag.E8, w • α = β := by
  intro α β hα hβ _
  exact CFSG.StandardType.GGFinModel.G5.ggG5_orbit_simplyLaced (Or.inr (Or.inr rfl)) hα hβ

theorem levTwoS3a_trans_E7 :
    ∀ α β : Fin Tag.E7.rank → ℤ, IsRoot Tag.E7 α → IsRoot Tag.E7 β →
      iform α α = iform β β → ∃ w : WeylGroup Tag.E7, w • α = β := by
  intro α β hα hβ _
  exact CFSG.StandardType.GGFinModel.G5.ggG5_orbit_simplyLaced (Or.inr (Or.inl rfl)) hα hβ

theorem levTwoS3a_trans_E6 :
    ∀ α β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → IsRoot Tag.E6 β →
      iform α α = iform β β → ∃ w : WeylGroup Tag.E6, w • α = β := by
  intro α β hα hβ _
  exact CFSG.StandardType.GGFinModel.G5.ggG5_orbit_simplyLaced (Or.inl rfl) hα hβ

theorem levTwoS3a_trans_F4 :
    ∀ α β : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 α → IsRoot Tag.F4 β →
      iform α α = iform β β → ∃ w : WeylGroup Tag.F4, w • α = β := by
  intro α β hα hβ hlen
  exact CFSG.StandardType.GGFinModel.G5.ggG5_orbit_F4 hα hβ hlen

theorem levTwoS3a_det_E8 (p : ℕ) (hp : p.Prime) (_hp2 : p ≠ 2) :
    ¬ (p : ℤ) ∣ (Tag.cartan Tag.E8).det := by
  rw [det_cartan_E8]
  intro h
  have h1 : p ∣ 1 := by exact_mod_cast h
  exact hp.not_dvd_one h1

theorem levTwoS3a_det_E7 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ (p : ℤ) ∣ (Tag.cartan Tag.E7).det := by
  rw [det_cartan_E7]
  intro h
  have h1 : p ∣ 2 := by exact_mod_cast h
  exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) h1) hp.two_le)

theorem levTwoS3a_det_F4 (p : ℕ) (hp : p.Prime) (_hp2 : p ≠ 2) :
    ¬ (p : ℤ) ∣ (Tag.cartan Tag.F4).det := by
  rw [det_cartan_F4]
  intro h
  have h1 : p ∣ 1 := by exact_mod_cast h
  exact hp.not_dvd_one h1

theorem levTwoS3a_rk_E6 (k : ℕ) (p : ℕ) (_hp : p.Prime) (_hp2 : p ≠ 2) (h3 : 3 ≤ k)
    (hcard : Tag.E6.rank ≤ k + 2) (_hdet : Tag.E6.rank ≤ k + 1 ∨ (p : ℤ) ∣ (Tag.cartan Tag.E6).det) :
    ExcRankOK Tag.E6 k :=
  ⟨h3, hcard, Or.inr rfl⟩

theorem levTwoS3a_rk_E8 (k : ℕ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ k)
    (hcard : Tag.E8.rank ≤ k + 2) (hdet : Tag.E8.rank ≤ k + 1 ∨ (p : ℤ) ∣ (Tag.cartan Tag.E8).det) :
    ExcRankOK Tag.E8 k :=
  ⟨h3, hcard, hdet.elim Or.inl fun h => absurd h (levTwoS3a_det_E8 p hp hp2)⟩

theorem levTwoS3a_rk_E7 (k : ℕ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ k)
    (hcard : Tag.E7.rank ≤ k + 2) (hdet : Tag.E7.rank ≤ k + 1 ∨ (p : ℤ) ∣ (Tag.cartan Tag.E7).det) :
    ExcRankOK Tag.E7 k :=
  ⟨h3, hcard, hdet.elim Or.inl fun h => absurd h (levTwoS3a_det_E7 p hp hp2)⟩

theorem levTwoS3a_rk_F4 (k : ℕ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ k)
    (hcard : Tag.F4.rank ≤ k + 2) (hdet : Tag.F4.rank ≤ k + 1 ∨ (p : ℤ) ∣ (Tag.cartan Tag.F4).det) :
    ExcRankOK Tag.F4 k :=
  ⟨h3, hcard, hdet.elim Or.inl fun h => absurd h (levTwoS3a_det_F4 p hp hp2)⟩

theorem levTwoS3a_engine_E8
    (h : ExcFinite Tag.E8 kacE8) :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (c : Fin Tag.E8.rank → ZMod p) (Φ : Set (Fin Tag.E8.rank → ℤ)),
      LevTwoData (isFiniteType_cartan Tag.E8) p c Φ →
        TCRoot (isFiniteType_cartan Tag.E8) Φ :=
  levTwoS3a_engine kacE8 facts_E8 levTwoS3a_trans_E8 levTwoS3a_rk_E8 h

theorem levTwoS3a_engine_E7
    (h : ExcFinite Tag.E7 kacE7) :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (c : Fin Tag.E7.rank → ZMod p) (Φ : Set (Fin Tag.E7.rank → ℤ)),
      LevTwoData (isFiniteType_cartan Tag.E7) p c Φ →
        TCRoot (isFiniteType_cartan Tag.E7) Φ :=
  levTwoS3a_engine kacE7 facts_E7 levTwoS3a_trans_E7 levTwoS3a_rk_E7 h

theorem levTwoS3a_engine_E6
    (h : ExcFinite Tag.E6 kacE6) :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (c : Fin Tag.E6.rank → ZMod p) (Φ : Set (Fin Tag.E6.rank → ℤ)),
      LevTwoData (isFiniteType_cartan Tag.E6) p c Φ →
        TCRoot (isFiniteType_cartan Tag.E6) Φ :=
  levTwoS3a_engine kacE6 facts_E6 levTwoS3a_trans_E6 levTwoS3a_rk_E6 h

theorem levTwoS3a_engine_F4
    (h : ExcFinite Tag.F4 kacF4) :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (c : Fin Tag.F4.rank → ZMod p) (Φ : Set (Fin Tag.F4.rank → ℤ)),
      LevTwoData (isFiniteType_cartan Tag.F4) p c Φ →
        TCRoot (isFiniteType_cartan Tag.F4) Φ :=
  levTwoS3a_engine kacF4 facts_F4 levTwoS3a_trans_F4 levTwoS3a_rk_F4 h

end CFSG.StandardType.LevTwo
