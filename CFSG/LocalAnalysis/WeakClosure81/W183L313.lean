module

public import CFSG.LocalAnalysis.WeakClosure81.W183L31End
public import CFSG.LocalAnalysis.WeakClosure81.W183L313Dich
public import CFSG.LocalAnalysis.WeakClosure81.W183L313Img

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

private theorem w183l313_preimage_of_normalizer (x : Ctx188 D V₀ V H i 3)
    (M : ModDataE H (eOmegaZ H D.T)) (hV1 : Gam183 V H (eOmegaZ H D.T) i 1)
    {S : Subgroup (LGL 2 M.W)} (hcen : M.img V = sylowCenter S) {n : LGL 2 M.W}
    (hn : n ∈ M.img H) (hnS : n ∈ Subgroup.normalizer (S : Set (LGL 2 M.W))) :
    ∃ y : G, ∃ hy : y ∈ H, y ∈ D.M ∧ M.ρ ⟨y, hy⟩ = n := by
  have hnZ : n ∈ Subgroup.normalizer
      ((M.img V : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := by
    rw [hcen]
    exact w183l313_normalizes_center hnS
  exact x.w183l313_exists_preimage M hV1 hn hnZ

section Certified


theorem w183l313_dich (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    {L : Subgroup G} (hLH : L ≤ H) (hLn : H ≤ Subgroup.normalizer (L : Set G))
    (hcent : ∀ y ∈ M.img H, (∀ l ∈ M.img L, y * l = l * y) → y = 1)
    (hshape : IsU3 ↥(M.img L) 2) (hV1 : Gam183 V H (eOmegaZ H D.T) i 1)
    (hPM : D.M ≤ Subgroup.normalizer ((FourteenTwo.PSub D.M V₀ V : Subgroup G) : Set G))
    {S : Subgroup (LGL 2 M.W)} (hS : IsSylowIn 2 S (M.img L)) (hcen : M.img V = sylowCenter S) :
    S ≤ M.img (H ⊓ Subgroup.centralizer (V : Set G)) ∨
      ∀ f ∈ M.img (H ⊓ FourteenTwo.PSub D.M V₀ V), f * f = 1 → f ∈ M.img L := by
  have hVH : V ≤ H := x.hyp.V_le_T.trans x.hyp.hyp171.2.1
  have hYQ : ∀ y ∈ M.img H, ∀ q ∈ M.img L, y * q * y⁻¹ ∈ M.img L :=
    w183l31_img_normal M hLH hLn
  have hQY : M.img L ≤ M.img H := M.img_mono hLH
  have hPY : M.img (H ⊓ FourteenTwo.PSub D.M V₀ V) ≤ M.img H := M.img_mono inf_le_left
  have hPS : M.img (H ⊓ FourteenTwo.PSub D.M V₀ V) ≤
      Subgroup.normalizer (S : Set (LGL 2 M.W)) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := M.mem_img.1 hk
    have hjH : (j : G) ∈ H := j.2
    have hjP : (j : G) ∈ FourteenTwo.PSub D.M V₀ V := (Subgroup.mem_inf.1 hj).2
    have hjM : (j : G) ∈ D.M := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hjP).2).1
    have hkY : M.ρ j ∈ M.img H := M.mem_img.2 ⟨j, hjH, rfl⟩
    have hkZ : M.ρ j ∈ Subgroup.normalizer (sylowCenter S) := by
      have hv1 : vInH V H 1 = V := by
        unfold vInH
        rw [conjSubgroup_one, inf_eq_left.2 hVH]
      have h := x.hyp.img_normalizer_of_mem_conj M hjH (g := 1) (by rwa [conjSubgroup_one])
      rwa [hv1, hcen] at h
    have hkQ : M.ρ j ∈ Subgroup.normalizer
        ((M.img L : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro q
      exact ⟨fun hq => hYQ (M.ρ j) hkY q hq, fun hq => by
        have h := hYQ (M.ρ j)⁻¹ ((M.img H).inv_mem hkY) (M.ρ j * q * (M.ρ j)⁻¹) hq
        convert h using 1
        group⟩
    exact w183l313_normalizes_sylow hshape hS hkQ hkZ
  have hPN : ∀ n ∈ M.img H ⊓ Subgroup.normalizer (S : Set (LGL 2 M.W)),
      ∀ p ∈ M.img (H ⊓ FourteenTwo.PSub D.M V₀ V),
      n * p * n⁻¹ ∈ M.img (H ⊓ FourteenTwo.PSub D.M V₀ V) := by
    intro n hn p hp
    obtain ⟨y, hy, hyM, rfl⟩ := w183l313_preimage_of_normalizer x M hV1 hcen hn.1 hn.2
    obtain ⟨z, hz, rfl⟩ := M.mem_img.1 hp
    have hconj : y * (z : G) * y⁻¹ ∈ H ⊓ FourteenTwo.PSub D.M V₀ V :=
      ⟨H.mul_mem (H.mul_mem hy z.2) (H.inv_mem hy),
        (Subgroup.mem_normalizer_iff.mp (hPM hyM) (z : G)).mp (Subgroup.mem_inf.1 hz).2⟩
    refine M.mem_img.2 ⟨⟨y, hy⟩ * z * ⟨y, hy⟩⁻¹, ?_, ?_⟩
    · simpa using hconj
    · simp only [map_mul, map_inv]
  have hLN : ∀ n ∈ M.img H ⊓ Subgroup.normalizer (S : Set (LGL 2 M.W)),
      ∀ l ∈ M.img (H ⊓ Subgroup.centralizer (V : Set G)),
      n * l * n⁻¹ ∈ M.img (H ⊓ Subgroup.centralizer (V : Set G)) := by
    intro n hn l hl
    obtain ⟨y, hy, hyM, rfl⟩ := w183l313_preimage_of_normalizer x M hV1 hcen hn.1 hn.2
    obtain ⟨z, hz, rfl⟩ := M.mem_img.1 hl
    have hyNormV : y ∈ Subgroup.normalizer (V : Set G) := by
      rw [x.hyp.setting.normalizer_eq]
      exact hyM
    have hconj : y * (z : G) * y⁻¹ ∈ H ⊓ Subgroup.centralizer (V : Set G) := by
      refine ⟨H.mul_mem (H.mul_mem hy z.2) (H.inv_mem hy), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      have hyinv : y⁻¹ * v * y ∈ V := by
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyNormV) v).mp hv
      have hcomm :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.1 hz).2) (y⁻¹ * v * y) hyinv
      calc v * (y * (z : G) * y⁻¹) = y * ((y⁻¹ * v * y) * z) * y⁻¹ := by group
        _ = y * (z * (y⁻¹ * v * y)) * y⁻¹ := by rw [hcomm]
        _ = (y * (z : G) * y⁻¹) * v := by group
    refine M.mem_img.2 ⟨⟨y, hy⟩ * z * ⟨y, hy⟩⁻¹, ?_, ?_⟩
    · simpa using hconj
    · simp only [map_mul, map_inv]
  have hZL : sylowCenter S ≤ M.img (H ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [← hcen]
    exact M.img_mono (le_inf hVH
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr x.hyp.setting.isElemAbelian.1))
  have hLZ : ∀ l ∈ M.img (H ⊓ Subgroup.centralizer (V : Set G)),
      ∀ z ∈ sylowCenter S, l * z = z * l := by
    intro l hl z hz
    obtain ⟨c, hc, rfl⟩ := M.mem_img.1 hl
    have hz' : z ∈ M.img V := by rwa [hcen]
    obtain ⟨v, hv, rfl⟩ := M.mem_img.1 hz'
    have hcomm := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.1 hc).2) (v : G) hv
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm.symm
  have hodd : ∀ k ∈ M.img (H ⊓ FourteenTwo.PSub D.M V₀ V), Odd (orderOf k) →
      k ∈ M.img (H ⊓ Subgroup.centralizer (V : Set G)) :=
    fun k hk hkodd => x.w183l313_odd_mem M hk hkodd
  exact w183l313_dichotomy hshape hS hQY hYQ hcent hPY hPS hPN hLN hZL hLZ hodd

end Certified

theorem w183l313_caseI (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hV1 : Gam183 V H (eOmegaZ H D.T) i 1) {p : G} (hpH : p ∈ H) (hyp : Hyp64 2 D.M V₀ V p)
    {B : Subgroup G} (hBH : B ≤ H) (hBP : B ≤ FourteenTwo.PSub D.M V₀ V)
    (hBV : M.img B ≤ M.img V) : ⁅NOf D.M V p, B⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro d hd b hb
  have hbH : b ∈ H := hBH hb
  have hbV : M.ρ ⟨b, hbH⟩ ∈ M.img V :=
    hBV (M.mem_img.2 ⟨⟨b, hbH⟩, hb, rfl⟩)
  obtain ⟨j, hjV, hjρ⟩ := M.mem_img.1 hbV
  have hjH : (j : G) ∈ H := j.2
  let r : G := (j : G)⁻¹ * b
  have hrH : r ∈ H := H.mul_mem (H.inv_mem hjH) hbH
  have hrρ : M.ρ ⟨r, hrH⟩ = 1 := by
    have h1 : (⟨r, hrH⟩ : ↥H) = (⟨(j : G), hjH⟩ : ↥H)⁻¹ * ⟨b, hbH⟩ := by
      apply Subtype.ext
      simp [r]
    rw [h1, map_mul, map_inv, hjρ]
    simp
  have hrCent : r ∈ Subgroup.centralizer (eOmegaZ H D.T : Set G) :=
    (M.ρ_eq_one_iff ⟨r, hrH⟩).mp hrρ
  have hrM : r ∈ D.M := x.hyp.centralizer_eOmegaZ_le_M hrCent
  have hrMp : r ∈ conjSubgroup D.M p :=
    x.w183l31_centralizer_le_conj (w183l31_gam183_conj hV1 hpH) hrCent
  have hbCT : b ∈ F11.CTilde D.M V₀ V := (Subgroup.mem_inf.1 (hBP hb)).1
  have hbr : b = (j : G) * r := by simp [r]
  exact Subgroup.mem_bot.mpr
    (w183l313_comm_of_mem_V_mul hyp hbCT hjV hrM hrMp hbr d hd)

section Certified


theorem w183l313_caseII (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    {L : Subgroup G} (hLH : L ≤ H) (hLn : H ≤ Subgroup.normalizer (L : Set G))
    (hshape : IsU3 ↥(M.img L) 2) (hV1 : Gam183 V H (eOmegaZ H D.T) i 1)
    {S : Subgroup (LGL 2 M.W)} (hS : IsSylowIn 2 S (M.img L)) (hcen : M.img V = sylowCenter S)
    (hSL : S ≤ M.img (H ⊓ Subgroup.centralizer (V : Set G))) {p : G} (hpL : p ∈ L)
    (hpM : p ∉ D.M) : D.T ≤ Subgroup.normalizer ((NOf D.M V p : Subgroup G) : Set G) := by
  have hTH : D.T ≤ H := x.hyp.hyp171.2.1
  have hVH : V ≤ H := x.hyp.V_le_T.trans hTH
  have hpH : p ∈ H := hLH hpL
  have hVM : V ≤ D.M := x.hyp.setting.pair.le_M
  have hstepA : ∀ y (hy : y ∈ H), M.ρ ⟨y, hy⟩ ∈
      Subgroup.normalizer (S : Set (LGL 2 M.W)) → y ∈ D.M := by
    intro y hy hyS
    have hv1 : vInH V H 1 = V := by
      unfold vInH
      rw [conjSubgroup_one, inf_eq_left.2 hVH]
    have hZ : M.ρ ⟨y, hy⟩ ∈ Subgroup.normalizer (sylowCenter S) :=
      w183l313_normalizes_center hyS
    have hZ' : M.ρ ⟨y, hy⟩ ∈
        Subgroup.normalizer ((M.img V : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := by
      rwa [hcen]
    have hmem : y ∈ conjSubgroup D.M 1 :=
      x.mem_conj_M_of_img_normalizer M hV1 hy (by rwa [hv1])
    rwa [conjSubgroup_one] at hmem
  obtain ⟨D₀, hBor⟩ := w183l313_borel_exists hshape hS
  have hstepC : ∀ q ∈ L, q ∉ D.M → NOf D.M V p = NOf D.M V q := by
    intro q hqL hqM
    have hqH : q ∈ H := hLH hqL
    set aq : LGL 2 M.W := M.ρ ⟨q, hqH⟩ with haq
    set ap : LGL 2 M.W := M.ρ ⟨p, hpH⟩ with hap
    have haqL : aq ∈ M.img L := M.mem_img.2 ⟨⟨q, hqH⟩, hqL, rfl⟩
    have hapL : ap ∈ M.img L := M.mem_img.2 ⟨⟨p, hpH⟩, hpL, rfl⟩
    have hSqSyl : IsSylowIn 2 (conjSubgroup S aq) (M.img L) := by
      have hnorm : aq⁻¹ ∈ Subgroup.normalizer
          ((M.img L : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) :=
        Subgroup.le_normalizer ((M.img L).inv_mem haqL)
      have hmap := (E1.isSylowIn_map_of_injective (p := 2)
        (f := (MulAut.conj aq⁻¹).toMonoidHom) (MulAut.conj aq⁻¹).injective).mpr hS
      have hLmap : (M.img L).map (MulAut.conj aq⁻¹).toMonoidHom = M.img L :=
        cj_eq_of_mem_normalizer hnorm
      rw [hLmap] at hmap
      exact hmap
    have hSpSyl : IsSylowIn 2 (conjSubgroup S ap) (M.img L) := by
      have hnorm : ap⁻¹ ∈ Subgroup.normalizer
          ((M.img L : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) :=
        Subgroup.le_normalizer ((M.img L).inv_mem hapL)
      have hmap := (E1.isSylowIn_map_of_injective (p := 2)
        (f := (MulAut.conj ap⁻¹).toMonoidHom) (MulAut.conj ap⁻¹).injective).mpr hS
      have hLmap : (M.img L).map (MulAut.conj ap⁻¹).toMonoidHom = M.img L :=
        cj_eq_of_mem_normalizer hnorm
      rw [hLmap] at hmap
      exact hmap
    have hSqNe : conjSubgroup S aq ≠ S := by
      intro heq
      have hmem : aq ∈ Subgroup.normalizer (S : Set (LGL 2 M.W)) :=
        conjSubgroup_eq_iff_mem_normalizer.mp heq
      exact hqM (hstepA q hqH (by rwa [haq] at hmem))
    have hSpNe : conjSubgroup S ap ≠ S := by
      intro heq
      have hmem : ap ∈ Subgroup.normalizer (S : Set (LGL 2 M.W)) :=
        conjSubgroup_eq_iff_mem_normalizer.mp heq
      exact hpM (hstepA p hpH (by rwa [hap] at hmem))
    obtain ⟨s, hsS, hsconj⟩ := hBor.trans (conjSubgroup S aq) (conjSubgroup S ap)
      hSqSyl hSpSyl hSqNe hSpNe
    have hconjSq : conjSubgroup S (aq * s) = conjSubgroup S ap := by
      rwa [conjSubgroup_conjSubgroup] at hsconj
    have hnNorm : aq * s * ap⁻¹ ∈ Subgroup.normalizer (S : Set (LGL 2 M.W)) := by
      rw [← conjSubgroup_eq_iff_mem_normalizer]
      calc conjSubgroup S (aq * s * ap⁻¹)
          = conjSubgroup (conjSubgroup S (aq * s)) ap⁻¹ :=
            (conjSubgroup_conjSubgroup S (aq * s) ap⁻¹).symm
        _ = conjSubgroup (conjSubgroup S ap) ap⁻¹ := by rw [hconjSq]
        _ = S := E3.conjSubgroup_conj_inv S ap
    have hnH : aq * s * ap⁻¹ ∈ M.img H :=
      (M.img H).mul_mem ((M.img H).mul_mem (M.img_mono hLH haqL)
        (M.img_mono hLH (hS.le hsS))) ((M.img H).inv_mem (M.img_mono hLH hapL))
    obtain ⟨y, hy, hyM, hyρ⟩ := w183l313_preimage_of_normalizer x M hV1 hcen hnH hnNorm
    obtain ⟨c', hc', hsc'⟩ := M.mem_img.1 (hSL hsS)
    have hc'C : (c' : G) ∈ Subgroup.centralizer (V : Set G) := (Subgroup.mem_inf.1 hc').2
    have hρeq : M.ρ ((⟨y, hy⟩ : ↥H)⁻¹ * (⟨q, hqH⟩ * c' * ⟨p, hpH⟩⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      rw [hyρ, hsc', haq, hap]
      group
    have hker : y⁻¹ * (q * (c' : G) * p⁻¹) ∈
        Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
      have h := (M.ρ_eq_one_iff ((⟨y, hy⟩ : ↥H)⁻¹ *
        (⟨q, hqH⟩ * c' * ⟨p, hpH⟩⁻¹))).mp hρeq
      simpa using h
    have hqcp : q * (c' : G) * p⁻¹ ∈ D.M := by
      have hcentM : y⁻¹ * (q * (c' : G) * p⁻¹) ∈ D.M :=
        x.hyp.centralizer_eOmegaZ_le_M hker
      have heq : q * (c' : G) * p⁻¹ = y * (y⁻¹ * (q * (c' : G) * p⁻¹)) := by group
      rw [heq]
      exact D.M.mul_mem hyM hcentM
    exact w183l313_NOf_eq_of_mul x.hyp.setting.normalizer_eq hc'C hqcp
  intro t ht
  have htH : t ∈ H := hTH ht
  have htM : t ∈ D.M := D.sylowM.le ht
  let q : G := t⁻¹ * p * t
  have hqL : q ∈ L := by
    have h := (Subgroup.mem_normalizer_iff.mp (hLn (H.inv_mem htH)) p).mp hpL
    simpa [q] using h
  have hqM : q ∉ D.M := by
    intro hq
    have hpq : p = t * q * t⁻¹ := by simp [q]; group
    rw [hpq] at hpM
    exact hpM (D.M.mul_mem (D.M.mul_mem htM hq) (D.M.inv_mem htM))
  have htV : conjSubgroup V t = V := by
    rw [conjSubgroup_eq_iff_mem_normalizer, x.hyp.setting.normalizer_eq]
    exact htM
  have hpt : p * t = t * q := by simp [q]; group
  have hconj : conjSubgroup (NOf D.M V p) t = NOf D.M V q := by
    rw [NOf_eq D.M V p hVM, NOf_eq D.M V q hVM, E3.conjSubgroup_inf, htV,
      conjSubgroup_conjSubgroup, hpt, ← conjSubgroup_conjSubgroup, htV]
  exact conjSubgroup_eq_iff_mem_normalizer.mp (by rw [hconj, ← hstepC q hqL hqM])

end Certified

end Ctx188

section Certified


theorem false_of_U34_member {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}
    (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T)) {L : Subgroup G}
    (hLH : L ≤ H) (hLn : H ≤ Subgroup.normalizer (L : Set G)) (hLT : L ⊔ D.T = H)
    (hcent : ∀ y ∈ M.img H, (∀ l ∈ M.img L, y * l = l * y) → y = 1)
    (hshape : IsU3 ↥(M.img L) 2) {g : G} (hg : Gam183 V H (eOmegaZ H D.T) i g)
    (hgT : vInH V H g ≤ D.T)
    (hcen : ∃ S : Subgroup (LGL 2 M.W), IsSylowIn 2 S (M.img L) ∧
      M.img (vInH V H g) = (Subgroup.center ↥S).map S.subtype) : False := by
  obtain ⟨S, hS, hcenS⟩ := hcen
  have hcen' : M.img (vInH V H g) = sylowCenter S := by
    rw [hcenS, w183l313_center_map_eq]
  obtain ⟨hgM, hSeq⟩ := x.w183l313_step0 M hLH hLn hshape hg hgT hS hcen'
  obtain ⟨hvV, hV1⟩ := x.w183l31_member_eq_V hg hgM
  rw [hvV] at hcen'
  obtain ⟨p, hpL, hpM⟩ := x.w183l313_exists_h hLT
  have hpH : p ∈ H := hLH hpL
  obtain ⟨hcard, hK, hK'⟩ := x.w183l313_two_points M hLH hshape hV1 hS hcen' hpL hpM
  have hyp := x.w183l31_hyp64 M hV1 hpH hcard hK hK'
  obtain ⟨-, hU⟩ := x.w183l31_U_eq M hV1 hpH hcard hK
  have hm : 2 < mBar D.M V₀ V hyp.elemAbelian := by
    have := x.bound
    omega
  have hN := w183l31_N_ne_bot hyp hm hU
  have hVh : ¬ V ≤ conjSubgroup D.M p := hyp.inCalOStar.1.2.1
  obtain ⟨B, hBle, hBea, hBne⟩ := w183l31_exists_conj x.hyp.setting x.hyp.ne_bot hyp hVh hN
  have hTH : D.T ≤ H := x.hyp.hyp171.2.1
  have hBT : B ≤ D.T := hBle.trans inf_le_left
  have hBP : B ≤ FourteenTwo.PSub D.M V₀ V := hBle.trans inf_le_right
  have hPM := (w183l31_conjV₀_le_P hyp).2
  rcases x.w183l313_dich M hLH hLn hcent hshape hV1 hPM hS hcen' with hSL | hinv
  · exact w183l31_false_of_normalizes x.hyp.setting x.hyp.ne_bot hyp hVh hN
      (x.w183l313_caseII M hLH hLn hshape hV1 hS hcen' hSL hpL hpM)
  · obtain ⟨D₀, hBor⟩ := w183l313_borel_exists hshape hS
    refine hBne (x.w183l313_caseI M hV1 hpH hyp (hBT.trans hTH) hBP ?_)
    intro r hr
    obtain ⟨j, hjB, rfl⟩ := M.mem_img.1 hr
    have hjH : (j : G) ∈ H := j.2
    have hjP : (j : G) ∈ H ⊓ FourteenTwo.PSub D.M V₀ V := ⟨hjH, hBP hjB⟩
    have hrP : M.ρ j ∈ M.img (H ⊓ FourteenTwo.PSub D.M V₀ V) := M.mem_img.2 ⟨j, hjP, rfl⟩
    have hr2 : M.ρ j * M.ρ j = 1 := by
      have h2 : (j : G) ^ 2 = 1 := hBea.2 _ hjB
      rw [← map_mul]
      have : j * j = 1 := Subtype.ext (by simpa [pow_two] using h2)
      rw [this, map_one]
    have hrL : M.ρ j ∈ M.img L := hinv _ hrP hr2
    have hrT : M.ρ j ∈ M.img D.T := M.mem_img.2 ⟨j, hBT hjB, rfl⟩
    have hrS : M.ρ j ∈ S := by
      rw [hSeq]
      exact ⟨hrT, hrL⟩
    rw [hcen']
    exact hBor.omega_le _ hrS hr2

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
