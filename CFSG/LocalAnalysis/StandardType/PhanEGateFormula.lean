module

public import CFSG.LocalAnalysis.StandardType.PhanEGatePsi

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Gate

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W} {w₀ : W} {t : C → C} {J I : Set ι} {a x₁ c x : C}

private theorem p9uGO_length_dist_comm (hB : IsWeylDistanceBuilding cs δ) (u v : C) :
    cs.length (δ u v) = cs.length (δ v u) := by
  rw [dist_inv hB, cs.length_inv]

private theorem p9uGO_length_dist_resProj (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hI : flipCore cs δ t J a = residue cs δ I x₁)
    {x₀ y₀ : C}
    (hpair : IsClosestPair cs δ J (flipType cs w₀ J) a (t a) x₀ y₀)
    {v : C} (hv : v ∈ residue cs δ I x₁) {c₀ : C} (hc₀ : c₀ ∈ residue cs δ J a) :
    cs.length (δ c₀ (resProj cs δ (flipType cs w₀ J) (t a) v)) =
      cs.length (δ x₀ y₀) + cs.length (δ c₀ v) := by
  have hvcore : v ∈ flipCore cs δ t J a := by rw [hI]; exact hv
  have hvproj : v ∈ projSet cs δ J a (residue cs δ (flipType cs w₀ J) (t a)) := by
    have h : v ∈ projSet cs δ J a (t '' residue cs δ J a) := hvcore
    rwa [image_residue_flip hw ht J a] at h
  obtain ⟨_, hgfv⟩ := resProj_projSet hB hvproj
  have hproj : IsProjection cs δ (residue cs δ J a)
      (resProj cs δ (flipType cs w₀ J) (t a) v) v := by
    have h := isProjection_resProj hB J a (resProj cs δ (flipType cs w₀ J) (t a) v)
    rwa [hgfv] at h
  obtain ⟨_, hlen⟩ := IsProjection.gate hB hproj hc₀
  have hconst : δ v (resProj cs δ (flipType cs w₀ J) (t a) v) = δ x₀ y₀ :=
    dist_resProj_eq hB hpair hvproj
  calc cs.length (δ c₀ (resProj cs δ (flipType cs w₀ J) (t a) v))
      = cs.length (δ (resProj cs δ (flipType cs w₀ J) (t a) v) c₀) :=
        p9uGO_length_dist_comm hB c₀ _
    _ = cs.length (δ (resProj cs δ (flipType cs w₀ J) (t a) v) v) + cs.length (δ v c₀) := hlen
    _ = cs.length (δ v (resProj cs δ (flipType cs w₀ J) (t a) v)) + cs.length (δ c₀ v) := by
        rw [p9uGO_length_dist_comm hB _ v, p9uGO_length_dist_comm hB v c₀]
    _ = cs.length (δ x₀ y₀) + cs.length (δ c₀ v) := by rw [hconst]

theorem resProj_flip_eq_of_isProjection (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hI : flipCore cs δ t J a = residue cs δ I x₁)
    (hc : c ∈ residue cs δ J a) (hx : IsProjection cs δ (residue cs δ I x₁) c x) :
    resProj cs δ (flipType cs w₀ J) (t a) c =
      resProj cs δ (flipType cs w₀ J) (t a) x := by
  classical
  obtain ⟨x₀, y₀, hpair⟩ := exists_isClosestPair cs δ J (flipType cs w₀ J) a (t a)
  let f : C → C := fun y => resProj cs δ (flipType cs w₀ J) (t a) y
  let g : C → C := fun y => resProj cs δ J a y
  have hfc_proj : f c ∈ projSet cs δ (flipType cs w₀ J) (t a) (residue cs δ J a) :=
    ⟨c, hc, rfl⟩
  obtain ⟨hv₀_mem, hfv₀⟩ := resProj_projSet hB hfc_proj
  have hv₀_core : g (f c) ∈ flipCore cs δ t J a := by
    show g (f c) ∈ projSet cs δ J a (t '' residue cs δ J a)
    rw [image_residue_flip hw ht J a]
    exact hv₀_mem
  have hv₀_I : g (f c) ∈ residue cs δ I x₁ := by rwa [hI] at hv₀_core
  have hfg : f (g (f c)) = f c := hfv₀
  have hle : ∀ v ∈ residue cs δ I x₁, cs.length (δ c (g (f c))) ≤ cs.length (δ c v) := by
    intro v hv
    have hvcore : v ∈ flipCore cs δ t J a := by rw [hI]; exact hv
    have hvproj : v ∈ projSet cs δ J a (residue cs δ (flipType cs w₀ J) (t a)) := by
      have h : v ∈ projSet cs δ J a (t '' residue cs δ J a) := hvcore
      rwa [image_residue_flip hw ht J a] at h
    have hd₀ := p9uGO_length_dist_resProj hB hw ht hI hpair hv₀_I hc
    have hd := p9uGO_length_dist_resProj hB hw ht hI hpair hv hc
    have hfvQ : f v ∈ residue cs δ (flipType cs w₀ J) (t a) := resProj_mem hB _ _ _
    have hproj := isProjection_resProj hB (flipType cs w₀ J) (t a) c
    have hineq : cs.length (δ c (f c)) ≤ cs.length (δ c (f v)) := by
      by_cases h : f v = f c
      · rw [h]
      · exact (hproj.2 (f v) hfvQ h).le
    have h1 : cs.length (δ x₀ y₀) + cs.length (δ c (g (f c))) ≤
        cs.length (δ x₀ y₀) + cs.length (δ c v) := by
      calc cs.length (δ x₀ y₀) + cs.length (δ c (g (f c)))
          = cs.length (δ c (f (g (f c)))) := hd₀.symm
        _ = cs.length (δ c (f c)) := by rw [hfg]
        _ ≤ cs.length (δ c (f v)) := hineq
        _ = cs.length (δ x₀ y₀) + cs.length (δ c v) := hd
    omega
  have hv₀_eq : g (f c) = x := by
    by_contra hne
    have hlt := hx.2 (g (f c)) hv₀_I hne
    have hge := hle x hx.1
    omega
  have hfx : f c = f x := by
    calc f c = f (g (f c)) := hfv₀.symm
      _ = f x := by rw [hv₀_eq]
  show resProj cs δ (flipType cs w₀ J) (t a) c =
    resProj cs δ (flipType cs w₀ J) (t a) x
  exact hfx

theorem resProj_t_eq_flipPsi (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hI : flipCore cs δ t J a = residue cs δ I x₁)
    (hc : c ∈ residue cs δ J a) (hx : IsProjection cs δ (residue cs δ I x₁) c x) :
    resProj cs δ J a (t c) = flipPsi cs δ t J a x := by
  have hfx := resProj_flip_eq_of_isProjection hB hw ht hI hc hx
  have htc := t_resProj_of_image hB hw ht (image_residue_flip_flip hw ht J a) c
  have htx := t_resProj_of_image hB hw ht (image_residue_flip_flip hw ht J a) x
  rw [hfx] at htc
  show resProj cs δ J a (t c) = resProj cs δ J a (t x)
  rw [← htc, htx]

theorem length_dist_flip (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hI : flipCore cs δ t J a = residue cs δ I x₁)
    (hc : c ∈ residue cs δ J a) (hx : IsProjection cs δ (residue cs δ I x₁) c x) :
    cs.length (δ c (t c)) = cs.length (δ (flipPsi cs δ t J a x) (t x)) +
      2 * cs.length (δ c x) + cs.length (δ x (flipPsi cs δ t J a x)) := by
  have hxcore : x ∈ flipCore cs δ t J a := by rw [hI]; exact hx.1
  have hψI : flipPsi cs δ t J a x ∈ residue cs δ I x₁ := by
    rw [← hI]
    exact flipPsi_mem hB hw ht hxcore
  have hproj_tc : IsProjection cs δ (residue cs δ J a) (t c) (flipPsi cs δ t J a x) := by
    have h2 := resProj_t_eq_flipPsi hB hw ht hI hc hx
    have h := isProjection_resProj hB J a (t c)
    rwa [h2] at h
  obtain ⟨_, hb⟩ := IsProjection.gate hB hproj_tc hc
  obtain ⟨_, hc'⟩ := IsProjection.gate hB hx hψI
  have htcQ : t c ∈ residue cs δ (flipType cs w₀ J) (t a) := by
    have h : t c ∈ t '' residue cs δ J a := ⟨c, hc, rfl⟩
    rwa [image_residue_flip hw ht J a] at h
  have hproj_ψ : IsProjection cs δ (residue cs δ (flipType cs w₀ J) (t a))
      (flipPsi cs δ t J a x) (t x) := by
    have h2 := resProj_flipPsi hB hw ht hxcore
    have h := isProjection_resProj hB (flipType cs w₀ J) (t a) (flipPsi cs δ t J a x)
    rwa [h2] at h
  obtain ⟨_, hd'⟩ := IsProjection.gate hB hproj_ψ htcQ
  have he : cs.length (δ (t x) (t c)) = cs.length (δ c x) := by
    rw [ht.dist, CoxeterSystem.length_w0_conj cs w₀ hw, p9uGO_length_dist_comm hB x c]
  calc cs.length (δ c (t c))
      = cs.length (δ (t c) c) := p9uGO_length_dist_comm hB c (t c)
    _ = cs.length (δ (t c) (flipPsi cs δ t J a x)) +
          cs.length (δ (flipPsi cs δ t J a x) c) := hb
    _ = cs.length (δ (flipPsi cs δ t J a x) (t c)) +
          cs.length (δ c (flipPsi cs δ t J a x)) := by
        rw [p9uGO_length_dist_comm hB (t c) (flipPsi cs δ t J a x),
          p9uGO_length_dist_comm hB (flipPsi cs δ t J a x) c]
    _ = (cs.length (δ (flipPsi cs δ t J a x) (t x)) + cs.length (δ (t x) (t c))) +
          (cs.length (δ c x) + cs.length (δ x (flipPsi cs δ t J a x))) := by
        rw [hd', hc']
    _ = cs.length (δ (flipPsi cs δ t J a x) (t x)) + 2 * cs.length (δ c x) +
          cs.length (δ x (flipPsi cs δ t J a x)) := by
        rw [he]; ring

end CFSG.ClassicalInvolution.Phan.PhanE.Gate

end
