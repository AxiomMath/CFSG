module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchKap
public import CFSG.LocalAnalysis.StandardType.PhanEMatchBlock
public import CFSG.LocalAnalysis.StandardType.PhanEResSeam

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt.SLClosed
  CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.ClassicalInvolution.Phan.PhanE.Res

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) {w₀ : W} (F : FrobData D n H w₀)
  {M : ChevModel2 D n H Fld} {θ : Fld →+* Fld} (PC : M.PhiCompat F θ) {m : ℕ}

theorem pathRoot_up {r : ℕ} (e : Fin m → Fin r) (k : Fin m) :
    pathRoot e k.castSucc k.succ = Pi.single (e k) 1 := by
  unfold pathRoot
  rw [if_pos k.castSucc_lt_succ]
  refine (Fintype.sum_eq_single k ?_).trans ?_
  · intro b hb
    rw [if_neg (by
      rintro ⟨h1, h2⟩
      simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
      exact hb (Fin.ext (by omega)))]
  · rw [if_pos (show k.castSucc.val ≤ k.val ∧ k.val < k.succ.val from
      ⟨le_rfl, by simp [Fin.val_succ]⟩)]

theorem pathRoot_down {r : ℕ} (e : Fin m → Fin r) (k : Fin m) :
    pathRoot e k.succ k.castSucc = -Pi.single (e k) 1 := by
  unfold pathRoot
  rw [if_neg (not_lt.mpr k.castSucc_lt_succ.le)]
  congr 1
  refine (Fintype.sum_eq_single k ?_).trans ?_
  · intro b hb
    rw [if_neg (by
      rintro ⟨h1, h2⟩
      simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
      exact hb (Fin.ext (by omega)))]
  · rw [if_pos (show k.castSucc.val ≤ k.val ∧ k.val < k.succ.val from
      ⟨le_rfl, by simp [Fin.val_succ]⟩)]

theorem kapMat_tv_coll [CharP Fld 2] (ρ : Equiv.Perm (Fin (m + 1))) (hρ : ∀ i, ρ (ρ i) = i)
    (p q : Fin (m + 1)) (c : Fld) :
    kapMat θ false (permSL ρ) (tv Fld p q c) = tv Fld (ρ p) (ρ q) (θ c) := by
  unfold kapMat
  rw [if_neg (by decide : ¬((false : Bool) = true))]
  simp only [MonoidHom.comp_apply, MulAut.conj_apply]
  exact permSL_conj_map_tv θ ρ hρ p q c

theorem kapMat_tv_pol [CharP Fld 2] (ρ : Equiv.Perm (Fin (m + 1))) (hρ : ∀ i, ρ (ρ i) = i)
    (p q : Fin (m + 1)) (c : Fld) :
    kapMat θ true (permSL ρ) (tv Fld p q c) = tv Fld (ρ q) (ρ p) (θ c) := by
  unfold kapMat
  rw [if_pos (rfl : (true : Bool) = true)]
  simp only [MonoidHom.comp_apply, MulAut.conj_apply]
  exact permSL_conj_sigma_tv θ ρ hρ p q c

include PC in
theorem hP_of_perm [CharP Fld 2] (L : SLPath M m) {v : W} {π : Fin D.rank → Fin D.rank}
    {d : List ℕ} (ρ : Equiv.Perm (Fin (m + 1))) (hρ : ∀ i, ρ (ρ i) = i) (pol : Bool)
    (hπ : ∀ k ∈ cutTypes m d,
      weylAction D.isFiniteType v (Pi.single (F.op (L.e k)) 1) = Pi.single (π (L.e k)) 1)
    (hperm : ∀ k ∈ cutTypes m d, ∃ k' : Fin m, π (L.e k) = L.e k' ∧
      (if pol = true then ρ k.succ = k'.castSucc ∧ ρ k.castSucc = k'.succ
      else ρ k.castSucc = k'.castSucc ∧ ρ k.succ = k'.succ)) :
    (∀ k ∈ cutTypes m d, ∀ c : Fld,
      nrep hct v * F.φ (L.ε (tv Fld k.castSucc k.succ c)) * (nrep hct v)⁻¹ =
        L.ε (kapMat θ pol (permSL ρ) (tv Fld k.castSucc k.succ c))) ∧
    (∀ k ∈ cutTypes m d, ∀ c : Fld,
      nrep hct v * F.φ (L.ε (tv Fld k.succ k.castSucc c)) * (nrep hct v)⁻¹ =
        L.ε (kapMat θ pol (permSL ρ) (tv Fld k.succ k.castSucc c))) := by
  refine ⟨fun k hk c => ?_, fun k hk c => ?_⟩
  · have hne : k.castSucc ≠ k.succ := k.castSucc_lt_succ.ne
    rw [L.tv_eq k.castSucc k.succ hne c, pathRoot_up L.e k,
      kappa_single hct F M PC (hπ k hk) c]
    obtain ⟨k', hk', hρ'⟩ := hperm k hk
    cases pol
    · rw [if_neg (by decide : ¬((false : Bool) = true))] at hρ'
      rw [kapMat_tv_coll ρ hρ, hρ'.1, hρ'.2,
        L.tv_eq k'.castSucc k'.succ k'.castSucc_lt_succ.ne (θ c),
        pathRoot_up L.e k', hk']
    · rw [if_pos (rfl : (true : Bool) = true)] at hρ'
      rw [kapMat_tv_pol ρ hρ, hρ'.1, hρ'.2,
        L.tv_eq k'.castSucc k'.succ k'.castSucc_lt_succ.ne (θ c),
        pathRoot_up L.e k', hk']
  · have hne : k.castSucc ≠ k.succ := k.castSucc_lt_succ.ne
    rw [L.tv_eq k.succ k.castSucc hne.symm c, pathRoot_down L.e k,
      kappa_neg_single hct F M PC (hπ k hk) c]
    obtain ⟨k', hk', hρ'⟩ := hperm k hk
    cases pol
    · rw [if_neg (by decide : ¬((false : Bool) = true))] at hρ'
      rw [kapMat_tv_coll ρ hρ, hρ'.1, hρ'.2,
        L.tv_eq k'.succ k'.castSucc k'.castSucc_lt_succ.ne.symm (θ c),
        pathRoot_down L.e k', hk']
    · rw [if_pos (rfl : (true : Bool) = true)] at hρ'
      rw [kapMat_tv_pol ρ hρ, hρ'.1, hρ'.2,
        L.tv_eq k'.succ k'.castSucc k'.castSucc_lt_succ.ne.symm (θ c),
        pathRoot_down L.e k', hk']

include PC in
theorem seam_hyps_of_match [CharP Fld 2] {c : PhanCode} (hc : c.IsFlagCode)
    (L : SLPath M c.rank) {v : W} {I : Set (Fin D.rank)} {π : Fin D.rank → Fin D.rank}
    (hcore : ∀ k : Fin c.rank, L.e k ∈ I ↔ c.coreN k = true)
    (hperm : ∀ k : Fin c.rank, L.e k ∈ I →
      ∃ k' : Fin c.rank, k'.val = c.permN k ∧ L.e k' = π (L.e k))
    (hπ : ∀ i ∈ I, weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1) :
    IsCut (c.rank + 1) c.cut ∧ (∀ k, L.e k ∈ I ↔ k ∈ cutTypes c.rank c.cut) ∧
      (∀ k ∈ cutTypes c.rank c.cut, ∀ x : Fld,
        nrep hct v * F.φ (L.ε (tv Fld k.castSucc k.succ x)) * (nrep hct v)⁻¹ =
          L.ε (kapMat θ c.polB (permSL c.blockPerm) (tv Fld k.castSucc k.succ x))) ∧
      (∀ k ∈ cutTypes c.rank c.cut, ∀ x : Fld,
        nrep hct v * F.φ (L.ε (tv Fld k.succ k.castSucc x)) * (nrep hct v)⁻¹ =
          L.ε (kapMat θ c.polB (permSL c.blockPerm) (tv Fld k.succ k.castSucc x))) := by
  have hI : ∀ k : Fin c.rank, L.e k ∈ I ↔ k ∈ cutTypes c.rank c.cut := fun k =>
    (hcore k).trans (PhanCode.coreN_iff_cutTypes hc k)
  have hπ' : ∀ k ∈ cutTypes c.rank c.cut,
      weylAction D.isFiniteType v (Pi.single (F.op (L.e k)) 1) = Pi.single (π (L.e k)) 1 :=
    fun k hk => hπ (L.e k) ((hI k).mpr hk)
  have hperm' : ∀ k ∈ cutTypes c.rank c.cut, ∃ k' : Fin c.rank, π (L.e k) = L.e k' ∧
      (if c.polB = true then c.blockPerm k.succ = k'.castSucc ∧ c.blockPerm k.castSucc = k'.succ
      else c.blockPerm k.castSucc = k'.castSucc ∧ c.blockPerm k.succ = k'.succ) := by
    intro k hk
    have hkI : L.e k ∈ I := (hI k).mpr hk
    have hcorek : c.coreN k = true := (hcore k).mp hkI
    obtain ⟨k', hk'1, hk'2⟩ := hperm k hkI
    obtain ⟨k'', hk''1, hk''2⟩ := PhanCode.blockPerm_spec hc k hcorek
    have hkk : k'' = k' := Fin.ext (by rw [hk''1, hk'1])
    exact ⟨k', hk'2.symm, by rwa [hkk] at hk''2⟩
  obtain ⟨hPu, hPl⟩ :=
    hP_of_perm hct F PC L c.blockPerm (PhanCode.blockPerm_invol c) c.polB hπ' hperm'
  exact ⟨PhanCode.isCut_cut hc, hI, hPu, hPl⟩

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
