module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyShape
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoSpSu
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoOmTwo
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinPlus
public import CFSG.LieType.CurtisTits.Reduction

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem irgTN_map_conj_conj {G : Type*} [Group G] (S : Subgroup G) (a w : G) :
    (S.map (MulAut.conj w).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      S.map (MulAut.conj (a * w)).toMonoidHom := by
  have h : (MulAut.conj a).toMonoidHom.comp (MulAut.conj w).toMonoidHom =
      (MulAut.conj (a * w)).toMonoidHom := by
    ext z
    show a * (w * z * w⁻¹) * a⁻¹ = a * w * z * (a * w)⁻¹
    group
  rw [Subgroup.map_map, h]

private theorem irgTN_map_conj_map {G H : Type*} [Group G] [Group H] (S : Subgroup G) (u : G)
    (e : G ≃* H) :
    (S.map (MulAut.conj u).toMonoidHom).map e.toMonoidHom =
      (S.map e.toMonoidHom).map (MulAut.conj (e u)).toMonoidHom := by
  have h : e.toMonoidHom.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (e u)).toMonoidHom.comp e.toMonoidHom := by
    ext z
    show e (u * z * u⁻¹) = e u * e z * (e u)⁻¹
    simp only [map_mul, map_inv]
  rw [Subgroup.map_map, Subgroup.map_map, h]

private theorem irgTN_ggRootSub_transport {U V X : Type*} [Group U] [Group V] [Group X]
    (D : UniversalRootDatum U) (D' : UniversalRootDatum V) (e : U ≃* V) (φ : U →* X)
    {β : Fin D.rank → ℤ} {γ : Fin D'.rank → ℤ} {w : V}
    (h1 : (D.rootGroup β).map e.toMonoidHom = (D'.rootGroup γ).map (MulAut.conj w).toMonoidHom)
    (u : U) :
    ggRootSub D φ β u = ggRootSub D' (φ.comp e.symm.toMonoidHom) γ (e u * w) := by
  have hcomp : (φ.comp e.symm.toMonoidHom).comp e.toMonoidHom = φ := by
    ext x
    simp
  have e1 : (D'.rootGroup γ).map (MulAut.conj (e u * w)).toMonoidHom =
      ((D.rootGroup β).map (MulAut.conj u).toMonoidHom).map e.toMonoidHom := by
    rw [← irgTN_map_conj_conj, ← h1, irgTN_map_conj_map]
  unfold ggRootSub
  rw [e1, Subgroup.map_map ((D.rootGroup β).map (MulAut.conj u).toMonoidHom)
    (φ.comp e.symm.toMonoidHom) e.toMonoidHom, hcomp]

private theorem irgTN_of_iso
    {X : Type} [Group X] {J R Rm : Subgroup X}
    {t' : StatedLieTag} {m g : ℕ} {t : StatedLieTag} {n g₂ : ℕ}
    (e : (ggU t' m g).K ≃* (ggU t n g₂).K) (he : IRGIsoCompat e)
    (hnorm : RCKNormalizedModel t n g₂) (hnot : ¬(((t = .PSp ∧ n = 2) ∨ t = .F4)))
    (φ : (ggU t' m g).K →* X) (hr : φ.range = J) (hk : φ.ker ≤ Subgroup.center (ggU t' m g).K)
    {β : Fin (ggU t' m g).D.rank → ℤ} (hβ : β ∈ (ggU t' m g).D.roots)
    (hlong : GGLongRoot (ggU t' m g).D β) {u : (ggU t' m g).K}
    (hR : R = ggRootSub (ggU t' m g).D φ β u) (hRm : Rm = ggRootSub (ggU t' m g).D φ (-β) u) :
    ∃ (t'' : StatedLieTag) (m'' g'' : ℕ) (φ'' : (ggU t'' m'' g'').K →* X)
      (γ : Fin (ggU t'' m'' g'').D.rank → ℤ) (u'' : (ggU t'' m'' g'').K),
      RCKNormalizedModel t'' m'' g'' ∧ φ''.range = J ∧
      φ''.ker ≤ Subgroup.center (ggU t'' m'' g'').K ∧
      γ ∈ (ggU t'' m'' g'').D.roots ∧ GGLongRoot (ggU t'' m'' g'').D γ ∧
      R = ggRootSub (ggU t'' m'' g'').D φ'' γ u'' ∧
      Rm = ggRootSub (ggU t'' m'' g'').D φ'' (-γ) u'' := by
  obtain ⟨γ, ⟨hγroot, hγlong⟩, w, h1, h2⟩ := he β hβ hlong
  have hγl : GGLongRoot (ggU t n g₂).D γ := by
    rcases hγlong with h | ⟨h, -⟩
    · exact h
    · exact absurd h hnot
  have hrange : (φ.comp e.symm.toMonoidHom).range = φ.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨e z, by simp⟩
  refine ⟨t, n, g₂, φ.comp e.symm.toMonoidHom, γ, e u * w, hnorm, hrange.trans hr, ?_, hγroot,
    hγl, ?_, ?_⟩
  · intro y hy
    have hy' : φ (e.symm y) = 1 := MonoidHom.mem_ker.mp hy
    have hx : e.symm y ∈ Subgroup.center (ggU t' m g).K := hk (MonoidHom.mem_ker.mpr hy')
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro z
    have h3 := congrArg e (hx (e.symm z))
    simpa using h3
  · exact hR.trans (irgTN_ggRootSub_transport (ggU t' m g).D (ggU t n g₂).D e φ h1 u)
  · exact hRm.trans (irgTN_ggRootSub_transport (ggU t' m g).D (ggU t n g₂).D e φ h2 u)

private theorem irgTN_pow_ne {g : ℕ} (hg : 2 ≤ g) (c : ℕ) (hc : c < 4) : 2 ^ g ≠ c := by
  have h4 : 4 ≤ 2 ^ g := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  omega

private theorem irgTN_norm_PSL_two {g : ℕ} (hg : 2 ≤ g) : RCKNormalizedModel .PSL 2 g := by
  refine ⟨Or.inl rfl, Nat.prime_two, by omega, le_refl 2, ?_, ?_⟩
  · intro h
    exact irgTN_pow_ne hg 2 (by norm_num) (congrArg Prod.snd h)
  · intro h
    exact irgTN_pow_ne hg 3 (by norm_num) (congrArg Prod.snd h)

private theorem irgTN_norm_PSL_four {g : ℕ} (hg : 1 ≤ g) : RCKNormalizedModel .PSL 4 g := by
  refine ⟨Or.inl rfl, Nat.prime_two, hg, by norm_num, ?_, ?_⟩
  · intro h
    exact absurd (congrArg Prod.fst h) (by norm_num)
  · intro h
    exact absurd (congrArg Prod.fst h) (by norm_num)

private theorem irgTN_norm_PSU_four {g : ℕ} (hg : 1 ≤ g) : RCKNormalizedModel .PSU 4 g := by
  refine ⟨Or.inr (Or.inl rfl), Nat.prime_two, hg, by norm_num, ?_⟩
  intro h
  exact absurd (congrArg Prod.fst h) (by norm_num)

theorem irg_normalize_hyp
    {X : Type} [Group X] {J R Rm : Subgroup X} (hqs : CFSG.Assembly.IsQuasisimple ↥J)
    (h : ∃ (t' : StatedLieTag) (m g : ℕ) (β : Fin (ggU t' m g).D.rank → ℤ), GGPosTag t' ∧ 1 ≤ g ∧
      GGLongRoot (ggU t' m g).D β ∧ GGRootPairVia (ggU t' m g) J R Rm β) :
    ∃ (t'' : StatedLieTag) (m'' g'' : ℕ) (φ'' : (ggU t'' m'' g'').K →* X)
      (γ : Fin (ggU t'' m'' g'').D.rank → ℤ) (u'' : (ggU t'' m'' g'').K),
      RCKRP.RCKNormalizedModel t'' m'' g'' ∧ φ''.range = J ∧
      φ''.ker ≤ Subgroup.center (ggU t'' m'' g'').K ∧
      γ ∈ (ggU t'' m'' g'').D.roots ∧ GGLongRoot (ggU t'' m'' g'').D γ ∧
      R = ggRootSub (ggU t'' m'' g'').D φ'' γ u'' ∧
      Rm = ggRootSub (ggU t'' m'' g'').D φ'' (-γ) u'' := by
  obtain ⟨t', m, g, β, ht', hg, hlong, hpair⟩ := h
  obtain ⟨φ, hr, hk, u, hR, hRm⟩ := hpair
  have hβ : β ∈ (ggU t' m g).D.roots := by
    obtain ⟨w, γ₀, hγ₀, -, hγ⟩ := hlong
    rw [hγ]
    exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w
  rcases irg_hyp_shape hqs ht' hg ⟨β, hlong⟩ φ hr hk with hadm | hexc | ⟨rfl, rfl, hg2⟩ |
      ⟨rfl, rfl, hg2⟩ | ⟨rfl, hm⟩ | ⟨rfl, rfl⟩
  · exact ⟨t', m, g, φ, β, u, ⟨ht', hadm⟩, hr, hk, hβ, hlong, hR, hRm⟩
  · rcases hexc with rfl | rfl | rfl | rfl | rfl
    · exact ⟨.F4, 0, g, φ, β, u, ⟨ht', Nat.prime_two, hg, rfl⟩, hr, hk, hβ, hlong, hR, hRm⟩
    · exact ⟨.E6, 0, g, φ, β, u, ⟨ht', Nat.prime_two, hg, rfl⟩, hr, hk, hβ, hlong, hR, hRm⟩
    · exact ⟨.E7, 0, g, φ, β, u, ⟨ht', Nat.prime_two, hg, rfl⟩, hr, hk, hβ, hlong, hR, hRm⟩
    · exact ⟨.E8, 0, g, φ, β, u, ⟨ht', Nat.prime_two, hg, rfl⟩, hr, hk, hβ, hlong, hR, hRm⟩
    · exact ⟨.twistedE6, 0, g, φ, β, u, ⟨ht', Nat.prime_two, hg, rfl⟩, hr, hk, hβ, hlong, hR,
        hRm⟩
  · obtain ⟨e, he⟩ := irgIsoCompat_sp_one hg2
    exact irgTN_of_iso e he (irgTN_norm_PSL_two hg2) (by simp) φ hr hk hβ hlong hR hRm
  · obtain ⟨e, he⟩ := irgIsoCompat_su_two hg2
    exact irgTN_of_iso e he (irgTN_norm_PSL_two hg2) (by simp) φ hr hk hβ hlong hR hRm
  · rcases hm with rfl | rfl
    · obtain ⟨e, he⟩ := irgIsoCompat_omegaMinus_two hg
      exact irgTN_of_iso e he (irgTN_norm_PSL_two (by omega)) (by simp) φ hr hk hβ hlong hR hRm
    · obtain ⟨e, he⟩ := irgIsoCompat_omegaMinus_three hg
      exact irgTN_of_iso e he (irgTN_norm_PSU_four hg) (by simp) φ hr hk hβ hlong hR hRm
  · obtain ⟨e, he⟩ := irgIsoCompat_omegaPlus_three hg
    exact irgTN_of_iso e he (irgTN_norm_PSL_four hg) (by simp) φ hr hk hβ hlong hR hRm

end CFSG.StandardType.RCKRP
