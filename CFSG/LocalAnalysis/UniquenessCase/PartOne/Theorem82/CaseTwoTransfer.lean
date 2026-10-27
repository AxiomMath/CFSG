module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoNormalizerA
import CFSG.GroupTheory.TransferCoset
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CComponents
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

namespace CaseTwoTransitive

variable {G : Type} [Group G] [Finite G] {c : Ctx812E G}
  (t : CaseTwoTransitive c)

theorem hpermM : ∀ m ∈ t.d.M, ∀ i : Fin 3,
    ∃ j, (t.d.Lf i).map (MulAut.conj m).toMonoidHom = t.d.Lf j := by
  intro m hm i
  exact t.hperm m (t.hdM ▸ hm) i

@[expose] def InducesAlternating : Prop :=
  ∀ m : ↥t.d.M, Equiv.Perm.sign (t.d.permHom t.hinj t.hpermM m) = 1

theorem P_le_normalizer_S : t.P ≤ Subgroup.normalizer (t.d.S : Set G) := by
  intro x hx
  rw [t.hdS]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx, c.le_normalizer_L (t.hP.le hx)⟩

theorem y_mem_normalizer_S : t.y ∈ Subgroup.normalizer (t.d.S : Set G) :=
  t.P_le_normalizer_S t.hyP

theorem conj_ne_inv_of_inducesAlternating (hIIa : t.InducesAlternating)
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 (t.P ⊓ Subgroup.centralizer ({t.y} : Set G))
      (Subgroup.centralizer ({t.y} : Set G)))
    (hNT : Subgroup.normalizer ((t.P ⊓ Subgroup.centralizer ({t.y} : Set G) : Subgroup G) : Set G)
      ≤ c.S.M) (g : G) :
    g * t.y * g⁻¹ ≠ t.y⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hconj
  set C : Subgroup G := Subgroup.centralizer ({t.y} : Set G) with hCdef
  set T : Subgroup G := t.P ⊓ C with hTdef
  have hgy_inv : g⁻¹ * t.y * g = t.y⁻¹ := by
    have h : g⁻¹ * t.y⁻¹ * g = t.y := by
      have h1 := congrArg (fun z => g⁻¹ * z * g) hconj
      simpa [mul_assoc] using h1.symm
    calc g⁻¹ * t.y * g = (g⁻¹ * t.y⁻¹ * g)⁻¹ := by group
      _ = t.y⁻¹ := by rw [h]
  have hCmap : C.map (MulAut.conj g).toMonoidHom = C := by
    rw [hCdef, CFSG.QuasiDihedralFusion.map_conj_centralizer_singleton g t.y, hconj]
    ext x
    simp only [Subgroup.mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff
  have hTg_sylow : CFSG.ABGLocalTools.IsSylowOf 3
      (T.map (MulAut.conj g).toMonoidHom) C := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at ⊢
    obtain ⟨hle, hP3, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
    have hker : (MulAut.conj g).toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj g).injective
    refine ⟨?_, hP3.map _, ?_⟩
    · calc T.map (MulAut.conj g).toMonoidHom ≤ C.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hle
        _ = C := hCmap
    · rw [← hCmap, Subgroup.relIndex_map_map, hker, sup_bot_eq, sup_bot_eq]
      exact hdvd
  obtain ⟨x, hxC, hxconj⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_exists_conj hTg_sylow hT
  rw [hCdef] at hxC
  have hT_eq : (T.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x).toMonoidHom = T := by
    ext z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hxconj (x * w * x⁻¹)).mpr (by simpa [MulAut.conj_apply, mul_assoc] using hw)
    · intro hz
      exact ⟨x⁻¹ * z * x, (hxconj z).mp hz, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hnorm : x * g ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change T.map (MulAut.conj (x * g)).toMonoidHom = T
    have hcomp : (MulAut.conj (x * g)).toMonoidHom =
        ((MulAut.conj x).toMonoidHom).comp ((MulAut.conj g).toMonoidHom) := by
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hcomp, ← Subgroup.map_map]
    exact hT_eq
  have hxgM : x * g ∈ c.S.M := hNT hnorm
  have hxy : x * t.y = t.y * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hxg_conj : (x * g) * t.y * (x * g)⁻¹ = t.y⁻¹ := by
    have hxyinv : x * t.y⁻¹ = t.y⁻¹ * x :=
      (Commute.inv_right_iff (a := x) (b := t.y)).mpr hxy
    calc (x * g) * t.y * (x * g)⁻¹ = x * (g * t.y * g⁻¹) * x⁻¹ := by group
      _ = x * t.y⁻¹ * x⁻¹ := by rw [hconj]
      _ = t.y⁻¹ := by rw [hxyinv]; group
  have hyM : t.y ∈ t.d.M := by
    rw [t.hdM]
    exact t.hP.le t.hyP
  have hxgM' : x * g ∈ t.d.M := by
    rw [t.hdM]
    exact hxgM
  let m : ↥t.d.M := ⟨x * g, hxgM'⟩
  set σ : Equiv.Perm (Fin 3) := t.d.permHom t.hinj t.hpermM ⟨t.y, hyM⟩ with hσdef
  have hmconj : m * ⟨t.y, hyM⟩ * m⁻¹ = ⟨t.y⁻¹, t.d.M.inv_mem hyM⟩ := by
    apply Subtype.ext
    simpa [m] using hxg_conj
  have hperm_conj : t.d.permHom t.hinj t.hpermM m * σ *
      (t.d.permHom t.hinj t.hpermM m)⁻¹ = σ⁻¹ := by
    calc t.d.permHom t.hinj t.hpermM m * σ * (t.d.permHom t.hinj t.hpermM m)⁻¹
        = t.d.permHom t.hinj t.hpermM (m * ⟨t.y, hyM⟩ * m⁻¹) := by
          rw [map_mul, map_mul, map_inv, hσdef]
      _ = t.d.permHom t.hinj t.hpermM ⟨t.y⁻¹, t.d.M.inv_mem hyM⟩ := by rw [hmconj]
      _ = σ⁻¹ := by
          have hyinv_eq : (⟨t.y⁻¹, t.d.M.inv_mem hyM⟩ : ↥t.d.M) =
              (⟨t.y, hyM⟩ : ↥t.d.M)⁻¹ := Subtype.ext (by simp)
          rw [hyinv_eq, map_inv, hσdef]
  have hσ0 : σ 0 = 1 := by
    have h := t.d.map_conj_Lf_eq t.hinj t.hpermM ⟨t.y, hyM⟩ 0
    rw [← hσdef] at h
    rw [t.hyL 0] at h
    simpa using (t.hinj h).symm
  have hσ3 : σ ^ 3 = 1 := by
    have he3 : (⟨t.y, hyM⟩ : ↥t.d.M) ^ 3 = 1 := Subtype.ext (by simpa using t.hy3)
    rw [hσdef, ← map_pow, he3, map_one]
  have hσne : σ ≠ 1 := by
    intro h1
    rw [h1] at hσ0
    exact (by decide : (0 : Fin 3) ≠ 1) (by simpa using hσ0)
  have hσsign : Equiv.Perm.sign σ = 1 := by
    have hsign3 : Equiv.Perm.sign σ ^ 3 = 1 := by
      rw [← map_pow, hσ3, map_one]
    exact (by decide : ∀ u : ℤˣ, u ^ 3 = 1 → u = 1) (Equiv.Perm.sign σ) hsign3
  have hcomm : t.d.permHom t.hinj t.hpermM m * σ =
      σ * t.d.permHom t.hinj t.hpermM m :=
    (by decide : ∀ a b : Equiv.Perm (Fin 3), Equiv.Perm.sign a = 1 → Equiv.Perm.sign b = 1 →
      a * b = b * a) _ _ (hIIa m) hσsign
  have hσeq : σ = σ⁻¹ := by
    calc σ = (t.d.permHom t.hinj t.hpermM m * σ) *
          (t.d.permHom t.hinj t.hpermM m)⁻¹ := by rw [hcomm]; group
      _ = σ⁻¹ := hperm_conj
  have hσsq : σ * σ = 1 := by
    have h := congrArg (fun τ => σ * τ) hσeq
    simpa using h
  have hσ1 : σ = 1 := by
    have h : σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
    rw [hσ3, pow_two, hσsq] at h
    simpa using h
  exact hσne hσ1

theorem false_of_forall_conj_y {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hF1 : ∀ g : G, g * t.y * g⁻¹ ∉ t.d.AA) (hF2 : ∀ g : G, g * t.y * g⁻¹ ≠ t.y⁻¹) : False := by
  classical
  haveI : IsSimpleGroup G := c.standing.simple
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPtop : CFSG.ABGLocalTools.IsSylowOf 3 t.P ⊤ := t.isSylowOf_top (p := p) hp hN
  have hPidx : ¬ 3 ∣ t.P.index := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hPtop).2.2
    rwa [Subgroup.relIndex_top_right] at h
  have hSleP : t.d.S ≤ t.P := by
    rw [t.hdS]
    exact inf_le_left
  have hcardP : Nat.card t.P = 3 * Nat.card t.d.S := by
    have h := CFSG.GroupTheory.WreathThree.card_sup_zpowers t.isWreathThree t.hy3
    rw [t.base_eq, t.hPy] at h
    exact h
  have hrel : t.d.S.relIndex t.P = 3 := by
    have hmul := Subgroup.relIndex_mul_card t.d.S t.P
    rw [inf_of_le_left hSleP, hcardP] at hmul
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) hmul
  have hSn : (t.d.S.subgroupOf t.P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSleP).mpr t.P_le_normalizer_S
  have hyS : t.y ∉ t.d.S := by
    rw [t.hdS]
    exact fun h => t.y_not_mem_L h.2
  have hfus : ∀ g : G, g * t.y * g⁻¹ ∈ t.P →
      t.y⁻¹ * (g * t.y * g⁻¹) ∈ t.d.S := by
    intro g hg
    have hx3 : (g * t.y * g⁻¹) ^ 3 = 1 := by
      rw [show (g * t.y * g⁻¹) ^ 3 = MulAut.conj g (t.y ^ 3) from by rw [map_pow]; rfl,
        t.hy3, map_one]
    rcases t.mem_AA_or_exists_conj_eq hg hx3 with hA | ⟨s, hs, hconj | hconj⟩
    · exact absurd hA (hF1 g)
    ·
      have hw : g * t.y * g⁻¹ = s⁻¹ * t.y * s := by
        have h := congrArg (fun z => s⁻¹ * z * s) hconj
        simpa [mul_assoc] using h
      have h1 : t.y⁻¹ * s⁻¹ * t.y ∈ t.d.S := by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ t.y_mem_normalizer_S)
          s⁻¹).mp (t.d.S.inv_mem hs)
        simpa using h
      rw [hw]
      have h2 := t.d.S.mul_mem h1 hs
      simpa [mul_assoc] using h2
    ·
      exact absurd (by
        have h : (s * g) * t.y * (s * g)⁻¹ = t.y⁻¹ := by
          calc (s * g) * t.y * (s * g)⁻¹ = s * (g * t.y * g⁻¹) * s⁻¹ := by group
            _ = t.y⁻¹ := hconj
        exact h) (hF2 (s * g))
  exact CFSG.GroupTheory.false_of_isSimpleGroup_of_conj_mem_coset (p := 3)
    c.standing.nonab hPidx hSn hrel t.hyP hyS t.hy3 hfus

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
