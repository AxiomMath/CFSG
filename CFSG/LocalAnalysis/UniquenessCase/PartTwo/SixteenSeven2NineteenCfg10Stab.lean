module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Frame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {X Fs : Subgroup (MulAut W)} {I₁ I₂ : Subgroup W}

private theorem s16c167_cfg10_map_mul_map (Y : Subgroup W) (g h : MulAut W) :
    (Y.map g.toMonoidHom).map h.toMonoidHom = Y.map (h * g).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem s16c167_cfg10_mem_stabSub_of_map_eq {Y : Subgroup W} {g : MulAut W}
    (h : Y.map g.toMonoidHom = Y) : g ∈ stabSub Y := by
  rw [mem_stabSub]
  intro u
  constructor
  · intro hgu
    have hmem : g u ∈ Y.map g.toMonoidHom := by rw [h]; exact hgu
    rw [Subgroup.mem_map] at hmem
    obtain ⟨v, hv, hvu⟩ := hmem
    exact g.injective hvu ▸ hv
  · intro hu
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hu

private theorem s16c167_cfg10_map_one (Y : Subgroup W) :
    Y.map (1 : MulAut W).toMonoidHom = Y := by
  ext x
  simp [Subgroup.mem_map]

theorem s16c167_cfg10_stab (F : Cfg10Mod X Fs I₁ I₂) {f : MulAut W} (hf : f ∈ Fs) :
    f ∈ stabSub I₁ ∧ f ∈ stabSub I₂ := by
  have hfX : f ∈ X := F.le hf
  have hpow : f * f * f = 1 := s16c167_cfg10_F_pow F.el f hf
  have hI₁ : I₁ ∈ conjSubs X I₁ := ⟨1, X.one_mem, (Subgroup.map_id I₁).symm⟩
  have hI₂ : I₂ ∈ conjSubs X I₁ := by rw [F.orb]; simp
  have h1 : I₁.map f.toMonoidHom ∈ conjSubs X I₁ := s16c167_cfg4_map_mem hfX hI₁
  have h2 : I₂.map f.toMonoidHom ∈ conjSubs X I₁ := s16c167_cfg4_map_mem hfX hI₂
  rw [F.orb] at h1 h2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  have hI1 : I₁.map f.toMonoidHom = I₁ := by
    rcases h1 with h1 | h1
    · exact h1
    exfalso
    have htriple : I₁.map (f * f * f).toMonoidHom = I₂ := by
      have e : I₁.map (f * f * f).toMonoidHom =
          ((I₁.map f.toMonoidHom).map f.toMonoidHom).map f.toMonoidHom := by
        rw [s16c167_cfg10_map_mul_map (I₁.map f.toMonoidHom) f f,
          s16c167_cfg10_map_mul_map I₁ f (f * f)]
      rw [e, h1]
      rcases h2 with h2 | h2
      · rw [h2, h1]
      · rw [h2, h2]
    rw [hpow] at htriple
    exact F.ne ((s16c167_cfg10_map_one I₁).symm.trans htriple)
  have hI2 : I₂.map f.toMonoidHom = I₂ := by
    rcases h2 with h2 | h2
    · exfalso
      have htriple : I₂.map (f * f * f).toMonoidHom = I₁ := by
        calc I₂.map (f * f * f).toMonoidHom
            = ((I₂.map f.toMonoidHom).map f.toMonoidHom).map f.toMonoidHom := by
              rw [s16c167_cfg10_map_mul_map (I₂.map f.toMonoidHom) f f,
                s16c167_cfg10_map_mul_map I₂ f (f * f)]
          _ = (I₁.map f.toMonoidHom).map f.toMonoidHom := by rw [h2]
          _ = I₁.map f.toMonoidHom := by
                exact congrArg (fun K : Subgroup W => K.map f.toMonoidHom) hI1
          _ = I₁ := hI1
      rw [hpow] at htriple
      exact F.ne (((s16c167_cfg10_map_one I₂).symm.trans htriple).symm)
    · exact h2
  exact ⟨s16c167_cfg10_mem_stabSub_of_map_eq hI1,
    s16c167_cfg10_mem_stabSub_of_map_eq hI2⟩

theorem s16c167_cfg10_ker_inf (F : Cfg10Mod X Fs I₁ I₂) :
    (Fs ⊓ centSub I₁) ⊓ (Fs ⊓ centSub I₂) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro f hf
  have hle : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers f) := by
    rw [← F.sup]
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · rw [mem_fixV_zpowers_iff_apply]
      exact (mem_centSub.mp hf.1.2) u hu
    · rw [mem_fixV_zpowers_iff_apply]
      exact (mem_centSub.mp hf.2.2) u hu
  ext w
  exact mem_fixV_zpowers_iff_apply.mp (hle trivial)

theorem s16c167_cfg10_ker_card_eq (F : Cfg10Mod X Fs I₁ I₂) :
    Nat.card ↥(Fs ⊓ centSub I₂) = Nat.card ↥(Fs ⊓ centSub I₁) := by
  have hI₂ : I₂ ∈ conjSubs X I₁ := by rw [F.orb]; simp
  obtain ⟨φ, hφX, hφ⟩ := hI₂
  have hφmap : I₁.map φ.toMonoidHom = I₂ := hφ.symm
  have hmain : Fs ⊓ centSub I₂ = (Fs ⊓ centSub I₁).map (MulAut.conj φ).toMonoidHom := by
    ext f
    constructor
    · intro hf
      refine Subgroup.mem_map.mpr ⟨φ⁻¹ * f * φ, ⟨?_, ?_⟩, ?_⟩
      · exact F.norm φ⁻¹ (X.inv_mem hφX) f hf.1
      · refine (mem_centSub (U := I₁)).mpr ?_
        intro w hw
        have hφw : φ w ∈ I₂ := by
          rw [← hφmap]
          exact Subgroup.mem_map_of_mem φ.toMonoidHom hw
        have hfix : f (φ w) = φ w := (mem_centSub.mp hf.2) (φ w) hφw
        calc (φ⁻¹ * f * φ) w = φ⁻¹ (f (φ w)) := by simp [MulAut.mul_apply]
          _ = φ⁻¹ (φ w) := by rw [hfix]
          _ = w := by simp
      · show (MulAut.conj φ) (φ⁻¹ * f * φ) = f
        rw [MulAut.conj_apply]
        group
    · rintro ⟨q, hq, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [MulAut.conj_apply] using F.norm φ hφX q hq.1
      · refine (mem_centSub (U := I₂)).mpr ?_
        intro w' hw'
        have hw'I : w' ∈ I₁.map φ.toMonoidHom := by rwa [hφmap]
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hw'I
        calc (MulAut.conj φ) q (φ w)
            = (φ * q * φ⁻¹) (φ w) := by rw [MulAut.conj_apply]
          _ = φ (q (φ⁻¹ (φ w))) := by simp [MulAut.mul_apply]
          _ = φ (q w) := by simp
          _ = φ w := by rw [(mem_centSub.mp hq.2) w hw]
  rw [hmain]
  exact Subgroup.card_map_of_injective (MulAut.conj φ).injective

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
