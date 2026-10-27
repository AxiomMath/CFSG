module

public import CFSG.LocalAnalysis.StandardType.GGTBJMaxRankRow
public import CFSG.LocalAnalysis.StandardType.GGMaxRankJModel
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LangModel
public import CFSG.LocalAnalysis.StandardType.GGTBJE8InnerModel
public import CFSG.LocalAnalysis.StandardType.GGTBJE8ComponentTransport
import CFSG.LieType.Chevalley.GraphFixedF4Canonical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.GGFinModel

theorem ggE8LangWitness_of_inner
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs X J : Subgroup G} {n : ℕ} (hΛ : LargeEvenInLambda2 ⟨.E8, 0, n⟩)
    (hinn : GGInnerDiagOn Bs X) (hlab : GGHasLabel ⟨.E8, 0, n⟩ (↥X ⧸ Subgroup.center ↥X))
    (hreg : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) {g : G} (hg : g ∈ Bs) (hgp : g ^ p = 1)
    (hgX : ∃ l ∈ X, g * l * g⁻¹ ≠ l)
    (hJ : CFSG.Assembly.IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G))) :
    GGE8LangWitness n p J := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hf : 1 ≤ n := hΛ.1
  have ht : GGExcFive .E8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨M⟩ := GGFinModel.ggDatumModel_nonempty ht hf hp hp2 hreg
  obtain ⟨e, c, hcp, hgN, he⟩ :=
    ggE8_inner_model (p := p) hRig hΛ hinn hlab hg hgp 0
  obtain ⟨b, hb, α, hα⟩ :=
    GGFinModel.ggE8_conj_bfull (f := n) (p := p) hf hp hp2 hreg M 0 c hcp
  obtain ⟨B⟩ := M.langData (n := 0) hf hp hp2 hreg
  have hZ : Subgroup.center (GGKb .E8 0 n) = ⊥ := B.center_bot
  have hconj_inj :
      Function.Injective (MulAut.conj : GGKb .E8 0 n → MulAut (GGKb .E8 0 n)) :=
    CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot hZ
  let BsM : Subgroup (GGAutU .E8 0 n) := (M.torusData (n := 0) hf hp hp2 hreg).ggBfull
  let C : Subgroup G := X ⊓ Subgroup.centralizer ({g} : Set G)
  let C' : Subgroup (GGAutU .E8 0 n) :=
    (ggPsiU .E8 0 n).range ⊓ Subgroup.centralizer ({b} : Set (GGAutU .E8 0 n))
  have hCX : C ≤ X := inf_le_left
  let Φ : ↥X →* GGAutU .E8 0 n :=
    (MulAut.conj : GGKb .E8 0 n →* GGAutU .E8 0 n).comp
      (α.toMonoidHom.comp e.toMonoidHom)
  have hmem : ∀ y : ↥C, Φ (Subgroup.inclusion hCX y) ∈ C' := by
    intro y
    have hy : y.1 ∈ X ⊓ Subgroup.centralizer ({g} : Set G) := y.2
    have hyX : y.1 ∈ X := (Subgroup.mem_inf.mp hy).1
    have hyC : y.1 ∈ Subgroup.centralizer ({g} : Set G) := (Subgroup.mem_inf.mp hy).2
    have hinc : Subgroup.inclusion hCX y = ⟨y.1, hyX⟩ := Subtype.ext rfl
    have hgfix : g * y.1 * g⁻¹ = y.1 := by
      have h := (Subgroup.mem_centralizer_iff.mp hyC) g (by simp)
      calc g * y.1 * g⁻¹ = (y.1 * g) * g⁻¹ := by rw [h]
        _ = y.1 := by group
    have hmemX : g * y.1 * g⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hgN y.1).mp hyX
    have hce : c * e ⟨y.1, hyX⟩ * c⁻¹ = e ⟨y.1, hyX⟩ := by
      have h := he ⟨y.1, hyX⟩ ⟨g * y.1 * g⁻¹, hmemX⟩ rfl
      rw [← h, show (⟨g * y.1 * g⁻¹, hmemX⟩ : ↥X) = ⟨y.1, hyX⟩ from Subtype.ext hgfix]
    have hfix : b (α (e ⟨y.1, hyX⟩)) = α (e ⟨y.1, hyX⟩) := by
      have h := hα (e ⟨y.1, hyX⟩)
      rw [hce] at h
      exact h.symm
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center (ggU .E8 0 n).K)
        (α (e (Subgroup.inclusion hCX y)))
      refine ⟨x, ?_⟩
      show MulAut.conj (QuotientGroup.mk' (Subgroup.center (ggU .E8 0 n).K) x) =
        MulAut.conj (α (e (Subgroup.inclusion hCX y)))
      rw [hx]
    · refine (Subgroup.mem_centralizer_iff.mpr ?_)
      intro z hz
      have hzg : z = b := by simpa using hz
      rw [hzg, hinc]
      change b * MulAut.conj (α (e ⟨y.1, hyX⟩)) =
        MulAut.conj (α (e ⟨y.1, hyX⟩)) * b
      ext w
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix]
  let F : ↥C →* ↥C' := (Φ.comp (Subgroup.inclusion hCX)).codRestrict C' hmem
  have hF_apply : ∀ y : ↥C, (F y).1 =
      MulAut.conj (α (e (Subgroup.inclusion hCX y))) := fun _ => rfl
  have hF_inj : Function.Injective F := by
    intro y z hyz
    have h1 : MulAut.conj (α (e (Subgroup.inclusion hCX y))) =
        MulAut.conj (α (e (Subgroup.inclusion hCX z))) := by
      have h := congrArg (fun w : ↥C' => (w : GGAutU .E8 0 n)) hyz
      rwa [hF_apply y, hF_apply z] at h
    have h2 := hconj_inj h1
    have h3 := α.injective h2
    have h4 := e.injective h3
    exact Subtype.ext (congrArg (fun w : ↥X => (w : G)) h4)
  have hF_surj : Function.Surjective F := by
    intro z
    have hz : z.1 ∈ (ggPsiU .E8 0 n).range ⊓
        Subgroup.centralizer ({b} : Set (GGAutU .E8 0 n)) := z.2
    have hzr : z.1 ∈ (ggPsiU .E8 0 n).range := (Subgroup.mem_inf.mp hz).1
    have hzc : z.1 ∈ Subgroup.centralizer ({b} : Set (GGAutU .E8 0 n)) :=
      (Subgroup.mem_inf.mp hz).2
    obtain ⟨x, hx⟩ := hzr
    let k : GGKb .E8 0 n := QuotientGroup.mk' (Subgroup.center (ggU .E8 0 n).K) x
    have hx' : MulAut.conj k = z.1 := by
      change MulAut.conj (QuotientGroup.mk' (Subgroup.center (ggU .E8 0 n).K) x) = z.1
      rw [← hx]
      rfl
    have hbz : b * z.1 = z.1 * b := (Subgroup.mem_centralizer_iff.mp hzc) b (by simp)
    have hcomm : b * MulAut.conj k = MulAut.conj k * b := by rw [hx']; exact hbz
    have hbk : b k = k := by
      apply hconj_inj
      have h1 : b * MulAut.conj k * b⁻¹ = MulAut.conj k := by
        rw [hcomm, mul_inv_cancel_right]
      rwa [CFSG.LieType.Chevalley.mulAut_mul_conj_mul_inv b k] at h1
    let yX : ↥X := e.symm (α.symm k)
    have he_yX : e yX = α.symm k := by
      change e (e.symm (α.symm k)) = α.symm k
      exact e.apply_symm_apply (α.symm k)
    have hc_w : c * α.symm k * c⁻¹ = α.symm k := by
      apply α.injective
      rw [hα (α.symm k), α.apply_symm_apply k]
      exact hbk
    have hcyX : yX.1 ∈ Subgroup.centralizer ({g} : Set G) := by
      refine (Subgroup.mem_centralizer_iff.mpr ?_)
      intro u hu
      have hug : u = g := by simpa using hu
      rw [hug]
      have hmemX : g * yX.1 * g⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp hgN yX.1).mp yX.2
      have he_conj : e ⟨g * yX.1 * g⁻¹, hmemX⟩ = c * e yX * c⁻¹ :=
        he yX ⟨g * yX.1 * g⁻¹, hmemX⟩ rfl
      have heq : e ⟨g * yX.1 * g⁻¹, hmemX⟩ = e yX := by
        rw [he_conj, he_yX, hc_w]
      have hval : g * yX.1 * g⁻¹ = yX.1 := by
        have h := e.injective heq
        simpa using congrArg (fun w : ↥X => (w : G)) h
      calc g * yX.1 = (g * yX.1 * g⁻¹) * g := by group
        _ = yX.1 * g := by rw [hval]
    let y : ↥C := ⟨yX.1, Subgroup.mem_inf.mpr ⟨yX.2, hcyX⟩⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change MulAut.conj (α (e (Subgroup.inclusion hCX y))) = z.1
    rw [show Subgroup.inclusion hCX y = yX from Subtype.ext rfl]
    rw [he_yX, α.apply_symm_apply k]
    exact hx'
  have hbij : Function.Bijective F := ⟨hF_inj, hF_surj⟩
  let φ : ↥C ≃* ↥C' := MulEquiv.ofBijective F hbij
  have hbne : (⟨b, hb⟩ : BsM) ≠ 1 := by
    intro hb1
    have hb1' : b = 1 := by
      simpa using congrArg (fun w : BsM => (w : GGAutU .E8 0 n)) hb1
    obtain ⟨l, hlX, hln⟩ := hgX
    have hc_center : c ∈ Subgroup.center (GGKb .E8 0 n) := by
      refine (Subgroup.mem_center_iff.mpr ?_)
      intro x
      have hx : c * x * c⁻¹ = x := by
        apply α.injective
        rw [hα x, hb1']
        rfl
      have hcx : c * x = x * c := by
        calc c * x = (c * x * c⁻¹) * c := by group
          _ = x * c := by rw [hx]
      exact hcx.symm
    have hc1 : c = 1 := by
      have hcb : c ∈ (⊥ : Subgroup (GGKb .E8 0 n)) := hZ ▸ hc_center
      exact Subgroup.mem_bot.mp hcb
    have hmemX : g * l * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hgN l).mp hlX
    have h := he ⟨l, hlX⟩ ⟨g * l * g⁻¹, hmemX⟩ rfl
    rw [hc1] at h
    simp only [one_mul, inv_one, mul_one] at h
    have hval : g * l * g⁻¹ = l := by
      have h2 := e.injective h
      simpa using congrArg (fun w : ↥X => (w : G)) h2
    exact hln hval
  obtain ⟨Jm, hJm, ⟨θ⟩⟩ := ggE8_component_transport φ hJ
  exact ⟨GGL, inferInstance, inferInstance, 0, BsM, gram .E8 n, piB .E8 p n,
    (M.torusData (n := 0) hf hp hp2 hreg).ggCoord, B, ⟨b, hb⟩, Jm, hbne, hJm, ⟨θ⟩⟩

end CFSG.StandardType
