module

public import CFSG.LocalAnalysis.StandardType.FF81.CentACore
public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelEmbed
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelLevi
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelUnip
import CFSG.Walter.PSL2Facts.Odd
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.FF81.CentA

open RootFusionLin

variable {G : Type} [Group G]

@[expose] def liftSub {m : ℕ} {Y : Subgroup G} (φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2))
    (K : Subgroup (GL (BlkIdx 1 m) (ZMod 2))) : Subgroup G :=
  (K.map φ.symm.toMonoidHom).map Y.subtype

@[expose] noncomputable def bStarG {m : ℕ} {Y : Subgroup G}
    (φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)) : G :=
  ((φ.symm (bStar m) : ↥Y) : G)

@[expose] noncomputable def lStar {k : ℕ} {Y : Subgroup G}
    (φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)) : Subgroup G :=
  liftSub φ (embGL k).range

@[expose] noncomputable def uStar {k : ℕ} {Y : Subgroup G}
    (φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)) : Subgroup G :=
  liftSub φ ((uSub 1 k).map (embGL k))

section lift

variable {m : ℕ} {Y : Subgroup G} {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)}

theorem mem_liftSub {K : Subgroup (GL (BlkIdx 1 m) (ZMod 2))} {x : G} :
    x ∈ liftSub φ K ↔ ∃ hx : x ∈ Y, φ ⟨x, hx⟩ ∈ K := by
  rw [liftSub, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨hyx ▸ y.2, ?_⟩
    have hφy : φ y = z := by
      rw [← hzy]
      exact MulEquiv.apply_symm_apply φ z
    have hxy : (⟨x, hyx ▸ y.2⟩ : ↥Y) = y := Subtype.ext hyx.symm
    rw [hxy, hφy]
    exact hz
  · rintro ⟨hx, hφx⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_map.mpr ⟨φ ⟨x, hx⟩, hφx, ?_⟩, rfl⟩
    exact MulEquiv.symm_apply_apply φ ⟨x, hx⟩

theorem liftSub_le (K : Subgroup (GL (BlkIdx 1 m) (ZMod 2))) : liftSub φ K ≤ Y := by
  rw [liftSub]
  exact Subgroup.map_subtype_le _

theorem liftSub_mono {K K' : Subgroup (GL (BlkIdx 1 m) (ZMod 2))} (h : K ≤ K') :
    liftSub φ K ≤ liftSub φ K' := by
  rw [liftSub, liftSub]
  exact Subgroup.map_mono (Subgroup.map_mono h)

theorem liftSub_top : liftSub φ ⊤ = Y := by
  rw [liftSub, Subgroup.map_top_of_surjective φ.symm.toMonoidHom φ.symm.surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem liftSub_sup (K K' : Subgroup (GL (BlkIdx 1 m) (ZMod 2))) :
    liftSub φ (K ⊔ K') = liftSub φ K ⊔ liftSub φ K' := by
  simp only [liftSub, Subgroup.map_sup]

private theorem caFrame_mem_centralizer_map_conj {a c : G} {K : Subgroup G} :
    c ∈ Subgroup.centralizer ((K.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) ↔
      a⁻¹ * c * a ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h l hl
    have h1 := h ((MulAut.conj a) l) (Subgroup.mem_map_of_mem _ hl)
    rw [MulAut.conj_apply] at h1
    calc l * (a⁻¹ * c * a) = a⁻¹ * ((a * l * a⁻¹) * c) * a := by group
      _ = a⁻¹ * (c * (a * l * a⁻¹)) * a := by rw [h1]
      _ = (a⁻¹ * c * a) * l := by group
  · intro h x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    show (MulAut.conj a) l * c = c * (MulAut.conj a) l
    calc (MulAut.conj a) l * c = a * (l * (a⁻¹ * c * a)) * a⁻¹ := by
          rw [MulAut.conj_apply]; group
      _ = a * ((a⁻¹ * c * a) * l) * a⁻¹ := by rw [h l hl]
      _ = c * (MulAut.conj a) l := by rw [MulAut.conj_apply]; group

private theorem caFrame_mem_normalizer_map_conj {a c : G} {K : Subgroup G} :
    c ∈ Subgroup.normalizer ((K.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) ↔
      a⁻¹ * c * a ∈ Subgroup.normalizer (K : Set G) := by
  rw [← Subgroup.map_equiv_normalizer_eq K (MulAut.conj a), Subgroup.mem_map_equiv,
    MulAut.conj_symm_apply]

private theorem caFrame_map_conj_self {Y R : Subgroup G} {y : G}
    (hR : R ≤ Subgroup.centralizer (Y : Set G)) (hy : y ∈ Y) :
    R.map (MulAut.conj y).toMonoidHom = R := by
  have hfix : ∀ r ∈ R, (MulAut.conj y).toMonoidHom r = r := by
    intro r hr
    show (MulAut.conj y) r = r
    have hcomm : y * r = r * y := (Subgroup.mem_centralizer_iff.mp (hR hr)) y hy
    rw [MulAut.conj_apply, hcomm]
    group
  apply le_antisymm
  · rintro x ⟨r, hr, rfl⟩
    rw [hfix r hr]
    exact hr
  · intro r hr
    exact Subgroup.mem_map.mpr ⟨r, hr, hfix r hr⟩

theorem liftSub_map_conj (K : Subgroup (GL (BlkIdx 1 m) (ZMod 2)))
    (A : GL (BlkIdx 1 m) (ZMod 2)) :
    liftSub φ (K.map (MulAut.conj A).toMonoidHom) =
      (liftSub φ K).map (MulAut.conj (((φ.symm A : ↥Y) : G))).toMonoidHom := by
  have hconj : ∀ k : GL (BlkIdx 1 m) (ZMod 2),
      ((φ.symm (A * k * A⁻¹) : ↥Y) : G) =
        ((φ.symm A : ↥Y) : G) * ((φ.symm k : ↥Y) : G) * ((φ.symm A : ↥Y) : G)⁻¹ := by
    intro k
    have h1 : φ.symm (A * k * A⁻¹) = φ.symm A * φ.symm k * (φ.symm A)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    simp only [h1, Subgroup.coe_mul, Subgroup.coe_inv]
  ext x
  constructor
  · intro hx
    rw [liftSub, Subgroup.mem_map] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    obtain ⟨g, hg, hgz⟩ := Subgroup.mem_map.mp hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
    have hgz' : φ.symm ((MulAut.conj A).toMonoidHom k) = z := hgz
    have hkA : A * k * A⁻¹ = (MulAut.conj A).toMonoidHom k := by
      show A * k * A⁻¹ = (MulAut.conj A) k
      rw [MulAut.conj_apply]
    rw [liftSub, Subgroup.mem_map]
    refine ⟨((φ.symm k : ↥Y) : G), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem Y.subtype
        (Subgroup.mem_map_of_mem φ.symm.toMonoidHom hk)
    · show (MulAut.conj ((φ.symm A : ↥Y) : G)) ((φ.symm k : ↥Y) : G) = x
      rw [MulAut.conj_apply, ← hconj k]
      show ((φ.symm (A * k * A⁻¹) : ↥Y) : G) = x
      rw [hkA, hgz']
      exact hzx
  · intro hx
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨hwY, hwk⟩ := mem_liftSub.mp hw
    rw [liftSub]
    refine Subgroup.mem_map.mpr ⟨φ.symm ((MulAut.conj A).toMonoidHom (φ ⟨w, hwY⟩)), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem φ.symm.toMonoidHom
        (Subgroup.mem_map_of_mem (MulAut.conj A).toMonoidHom hwk)
    · have hwx' : ((φ.symm A : ↥Y) : G) * w * ((φ.symm A : ↥Y) : G)⁻¹ = x := by
        rw [← MulAut.conj_apply]
        exact hwx
      show ((φ.symm ((MulAut.conj A).toMonoidHom (φ ⟨w, hwY⟩)) : ↥Y) : G) = x
      rw [show (MulAut.conj A).toMonoidHom (φ ⟨w, hwY⟩) = A * φ ⟨w, hwY⟩ * A⁻¹ from
            MulAut.conj_apply A (φ ⟨w, hwY⟩),
          hconj (φ ⟨w, hwY⟩), MulEquiv.symm_apply_apply φ ⟨w, hwY⟩]
      simpa using hwx'

theorem eq_one_of_forall_commute_of_mem (φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)) {y : G}
    (hy : y ∈ Y) (hc : ∀ g ∈ Y, y * g = g * y) : y = 1 := by
  have h1 : φ ⟨y, hy⟩ = 1 := by
    apply eq_one_of_forall_commute
    intro x
    obtain ⟨z, rfl⟩ := φ.surjective x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc (z : G) z.2)
  have h2 : (⟨y, hy⟩ : ↥Y) = 1 := φ.injective (by rw [h1, map_one])
  simpa using congrArg Subtype.val h2

end lift

section setting

variable [Finite G] {m : ℕ} {Y L R : Subgroup G} {b t : G}
  {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)}

theorem liftSub_leviB (hS : CentASetting m Y L R b t φ) : liftSub φ (leviB m) = L := by
  ext x
  rw [mem_liftSub]
  constructor
  · rintro ⟨hx, hφx⟩
    exact (hS.φ_L ⟨x, hx⟩).mpr hφx
  · intro hx
    exact ⟨hS.L_le hx, (hS.φ_L ⟨x, hS.L_le hx⟩).mp hx⟩

theorem mem_liftSub_cent (hS : CentASetting m Y L R b t φ) {x : G} :
    x ∈ liftSub φ (Cent 1 m) ↔ x ∈ Y ∧ x * t = t * x := by
  rw [mem_liftSub]
  constructor
  · rintro ⟨hx, hφx⟩
    have hcomm : φ ⟨x, hx⟩ * jGL 1 m = jGL 1 m * φ ⟨x, hx⟩ :=
      (Subgroup.mem_centralizer_singleton_iff).mp hφx
    refine ⟨hx, ?_⟩
    have h2 : (⟨x, hx⟩ : ↥Y) * ⟨t, hS.t_mem⟩ = ⟨t, hS.t_mem⟩ * ⟨x, hx⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, hS.φ_t]
      exact hcomm
    simpa using congrArg Subtype.val h2
  · rintro ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    change φ ⟨x, hx⟩ ∈
      Subgroup.centralizer ({jGL 1 m} : Set (GL (BlkIdx 1 m) (ZMod 2)))
    rw [Subgroup.mem_centralizer_singleton_iff, ← hS.φ_t, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxt

theorem bStarG_mem (hS : CentASetting m Y L R b t φ) :
    bStarG φ ∈ L ∧ bStarG φ ∈ liftSub φ (Cent 1 m) := by
  have hY : bStarG φ ∈ Y := by
    rw [bStarG]
    exact (φ.symm (bStar m)).2
  have hφb : φ ⟨bStarG φ, hY⟩ = bStar m := by
    show φ (φ.symm (bStar m)) = bStar m
    exact MulEquiv.apply_symm_apply φ (bStar m)
  constructor
  · rw [← liftSub_leviB hS, mem_liftSub]
    exact ⟨hY, by rw [hφb]; exact bStar_mem_leviB m⟩
  · rw [mem_liftSub]
    exact ⟨hY, by rw [hφb]; exact leviB_le_cent m (bStar_mem_leviB m)⟩

theorem orderOf_bStarG (hS : CentASetting m Y L R b t φ) : orderOf (bStarG φ) = 3 := by
  rw [bStarG, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact orderOf_bStar (by rcases hS.m_cases with h | h <;> omega)

theorem exists_sl3_bStarG (hS : CentASetting m Y L R b t φ) :
    ∃ P : Subgroup G, P ≤ L ∧ bStarG φ ∈ P ∧
      Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hm : 3 ≤ m := by rcases hS.m_cases with h | h <;> omega
  obtain ⟨P₀, hP₀L, hP₀b, ⟨e₀⟩⟩ := exists_sl3_bStar (m := m) hm
  have hY : bStarG φ ∈ Y := by
    rw [bStarG]
    exact (φ.symm (bStar m)).2
  have hφb : φ ⟨bStarG φ, hY⟩ = bStar m := by
    show φ (φ.symm (bStar m)) = bStar m
    exact MulEquiv.apply_symm_apply φ (bStar m)
  refine ⟨liftSub φ P₀, ?_, ?_, ?_⟩
  · rw [← liftSub_leviB hS]
    exact liftSub_mono hP₀L
  · rw [mem_liftSub]
    exact ⟨hY, by rw [hφb]; exact hP₀b⟩
  · have e1 : ↥P₀ ≃* ↥(P₀.map φ.symm.toMonoidHom) :=
      Subgroup.equivMapOfInjective P₀ φ.symm.toMonoidHom φ.symm.injective
    have e2 : ↥(P₀.map φ.symm.toMonoidHom) ≃* ↥(liftSub φ P₀) :=
      Subgroup.equivMapOfInjective (P₀.map φ.symm.toMonoidHom) Y.subtype Y.subtype_injective
    exact ⟨(e1.trans e2).symm.trans e₀⟩

end setting

section frame

variable [Finite G] {k : ℕ} {Y L R : Subgroup G} {b t : G}
  {φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)}

theorem bStarG_eq_conj (hS : CentASetting (k + 2) Y L R b t φ) :
    bStarG φ = ((φ.symm (piStd k) : ↥Y) : G) * b * ((φ.symm (piStd k) : ↥Y) : G)⁻¹ := by
  have hb : φ.symm (betaStd (k + 2)) = ⟨b, hS.b_mem⟩ :=
    (MulEquiv.symm_apply_eq φ).mpr hS.φ_b.symm
  have h := congrArg (fun z : GL (BlkIdx 1 (k + 2)) (ZMod 2) => φ.symm z)
    (piStd_conj_betaStd k)
  simp only [map_mul, map_inv, hb] at h
  have h' := congrArg (fun y : ↥Y => (y : G)) h
  show ((φ.symm (bStar (k + 2)) : ↥Y) : G) = _
  simpa using h'.symm

theorem lStar_eq_map (hS : CentASetting (k + 2) Y L R b t φ) :
    lStar φ = L.map (MulAut.conj ((φ.symm (piStd k) : ↥Y) : G)).toMonoidHom := by
  rw [lStar, ← map_leviB_piStd k, liftSub_map_conj, liftSub_leviB hS]

theorem t_mem_lStar (hS : CentASetting (k + 2) Y L R b t φ) : t ∈ lStar φ := by
  rw [lStar, mem_liftSub]
  refine ⟨hS.t_mem, ?_⟩
  have ht : φ ⟨t, hS.t_mem⟩ = embGL k (jGL 1 k) := by rw [hS.φ_t, embGL_jGL]
  rw [ht]
  exact MonoidHom.mem_range.mpr ⟨jGL 1 k, rfl⟩

theorem lStar_le_centralizer (hS : CentASetting (k + 2) Y L R b t φ) :
    lStar φ ≤ Subgroup.centralizer ({bStarG φ} : Set G) := by
  intro x hx
  rw [lStar, mem_liftSub] at hx
  obtain ⟨hxY, hxr⟩ := hx
  have hcomm : φ ⟨x, hxY⟩ * bStar (k + 2) = bStar (k + 2) * φ ⟨x, hxY⟩ := by
    have hmem : φ ⟨x, hxY⟩ ∈
        Subgroup.centralizer ({bStar (k + 2)} : Set (GL (BlkIdx 1 (k + 2)) (ZMod 2))) := by
      rw [centralizer_bStar k]
      exact Subgroup.mem_sup_left hxr
    exact (Subgroup.mem_centralizer_singleton_iff (g := bStar (k + 2))).mp hmem
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain rfl : h = bStarG φ := by simpa using hh
  have hbY : bStarG φ ∈ Y := liftSub_le _ (bStarG_mem hS).2
  have hbφ : φ ⟨bStarG φ, hbY⟩ = bStar (k + 2) := by
    show φ (φ.symm (bStar (k + 2))) = bStar (k + 2)
    exact MulEquiv.apply_symm_apply φ (bStar (k + 2))
  have h2 : (⟨bStarG φ, hbY⟩ : ↥Y) * ⟨x, hxY⟩ = ⟨x, hxY⟩ * ⟨bStarG φ, hbY⟩ := by
    apply φ.injective
    rw [map_mul, map_mul, hbφ]
    exact hcomm.symm
  simpa using congrArg Subtype.val h2

theorem centralizer_bStarG_le_normalizer (hS : CentASetting (k + 2) Y L R b t φ) :
    Subgroup.centralizer ({bStarG φ} : Set G) ≤ Subgroup.normalizer (lStar φ : Set G) := by
  intro c hc
  set y : G := ((φ.symm (piStd k) : ↥Y) : G) with hydef
  have hyY : y ∈ Y := by
    rw [hydef]
    exact (φ.symm (piStd k)).2
  have hbstar : bStarG φ = y * b * y⁻¹ := by rw [bStarG_eq_conj hS, hydef]
  have hlstar : lStar φ = L.map (MulAut.conj y).toMonoidHom := by rw [lStar_eq_map hS, hydef]
  have hc' : y⁻¹ * c * y ∈ Subgroup.centralizer ({b} : Set G) := by
    have h1 : c ∈ Subgroup.centralizer ({y * b * y⁻¹} : Set G) := by rwa [← hbstar]
    rwa [CFSG.Walter.centralizer_conj_eq_map y b, Subgroup.mem_map_equiv,
      MulAut.conj_symm_apply] at h1
  rw [hlstar]
  exact (caFrame_mem_normalizer_map_conj (a := y) (K := L) (c := c)).mpr (hS.nor hc')

theorem centralizer_bStarG_inf_le (hS : CentASetting (k + 2) Y L R b t φ) :
    Subgroup.centralizer ({bStarG φ} : Set G) ⊓ Subgroup.centralizer (lStar φ : Set G) ≤
      R ⊔ Subgroup.zpowers (bStarG φ) := by
  intro c hc
  obtain ⟨hc1, hc2⟩ := Subgroup.mem_inf.mp hc
  set y : G := ((φ.symm (piStd k) : ↥Y) : G) with hydef
  have hyY : y ∈ Y := by
    rw [hydef]
    exact (φ.symm (piStd k)).2
  have hbstar : bStarG φ = y * b * y⁻¹ := by rw [bStarG_eq_conj hS, hydef]
  have hlstar : lStar φ = L.map (MulAut.conj y).toMonoidHom := by rw [lStar_eq_map hS, hydef]
  have hc' : y⁻¹ * c * y ∈ Subgroup.centralizer ({b} : Set G) := by
    have h1 : c ∈ Subgroup.centralizer ({y * b * y⁻¹} : Set G) := by rwa [← hbstar]
    rwa [CFSG.Walter.centralizer_conj_eq_map y b, Subgroup.mem_map_equiv,
      MulAut.conj_symm_apply] at h1
  have hc'L : y⁻¹ * c * y ∈ Subgroup.centralizer (L : Set G) :=
    (caFrame_mem_centralizer_map_conj (a := y) (K := L) (c := c)).mp (by rwa [← hlstar])
  have hrad : y⁻¹ * c * y ∈ R ⊔ Subgroup.zpowers b :=
    hS.rad (Subgroup.mem_inf.mpr ⟨hc', hc'L⟩)
  have hcy : (MulAut.conj y).toMonoidHom (y⁻¹ * c * y) = c := by
    show (MulAut.conj y) (y⁻¹ * c * y) = c
    rw [MulAut.conj_apply]
    group
  have hconjb : (MulAut.conj y).toMonoidHom b = bStarG φ := by
    show (MulAut.conj y) b = bStarG φ
    rw [MulAut.conj_apply, ← hbstar]
  have hmem : c ∈ (R ⊔ Subgroup.zpowers b).map (MulAut.conj y).toMonoidHom := by
    rw [← hcy]
    exact Subgroup.mem_map_of_mem _ hrad
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, hconjb,
    caFrame_map_conj_self hS.rad_le hyY] at hmem
  exact hmem

end frame

end CFSG.StandardType.FF81.CentA

end
