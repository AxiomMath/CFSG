module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TorusLift
public import CFSG.LocalAnalysis.StandardType.GGTwE6TorusDescent
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityProof

public section

namespace CFSG.StandardType.TwE6Tori

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem l10mincl_e6RootParams_map {K k : Type} [Field K] [Field k] (ι : K →+* k)
    (u : Fin Tag.E6.rank → Kˣ) :
    e6RootParams (fun l => Units.map ι.toMonoidHom (u l)) =
      fun j => Units.map ι.toMonoidHom (e6RootParams u j) := by
  funext j
  simp only [e6RootParams, map_prod, map_zpow]

private theorem l10mincl_baseChangeGL_twistHom
    (t : TwistTag) {k L : Type} [Field k] [Field L]
    (ι : k →+* L) (θ : k →+* k) (θ' : L →+* L) (h : θ'.comp ι = ι.comp θ)
    (g : ModGL t.tag k) :
    baseChangeGL ι (twistHom t k θ g) = twistHom t L θ' (baseChangeGL ι g) :=
  (twistHom_baseChangeGL (t := t) (ι := ι) (σk := θ) (σ := θ') h.symm g).symm

private theorem l10mincl_twistHom_lang_descent
    (t : TwistTag) {k L : Type} [Field k] [Field L]
    (ι : k →+* L) (θ : k →+* k) (θ' : L →+* L) (h : θ'.comp ι = ι.comp θ)
    {g₃ n₃ : ModGL t.tag k} {g0 n0 : ModGL t.tag L}
    (hg : baseChangeGL ι g₃ = g0) (hn : baseChangeGL ι n₃ = n0)
    (hLang : twistHom t L θ' g0 = g0 * n0) : twistHom t k θ g₃ = g₃ * n₃ := by
  apply baseChangeGL_injective ι
  rw [l10mincl_baseChangeGL_twistHom t ι θ θ' h, hg, map_mul, hg, hn]
  exact hLang

theorem twE6_torus_gamma_le_image
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2)
    (halg : ∀ c : L, ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c)
    (D : LangDatum TwistTag.E6.tag L) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr)
    (ω : List (Fin Tag.E6.rank))
    (hn : D.n = canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω)) :
    D.torus ⊓ D.Γ ≤ twE6Image Fr ω := by
  intro s hs
  obtain ⟨hsT, hsΓ⟩ := Subgroup.mem_inf.1 hs
  obtain ⟨K, hKfield, hKalg, σ, hKcard, hσ, hAC⟩ := exists_gf4_algClosure halg
  letI : Field K := hKfield
  letI : Algebra K L := hKalg
  haveI : IsAlgClosure K L := hAC
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  haveI : Fintype K := Fintype.ofFinite K
  have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK4]; norm_num)
  have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ c]; norm_num
  have hFr' : ∀ c, Fr c = c ^ (2 ^ 1) := fun c => by rw [hFr]; norm_num
  have hΓeq := Γ_eq_map_twistedE6RootGroup (ℓ := 2) (f := 1) Nat.prime_two le_rfl hKcard hσ
    hFr' D hΦ
  have hsΓ' : s ∈ ((twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K L))).map
      (MulAut.conj D.g0⁻¹).toMonoidHom := by
    rw [← hΓeq]
    exact hsΓ
  obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.1 hsΓ'
  obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 hy
  let g0' : ModGL Tag.E6 L := D.g0
  let t' : ModGL Tag.E6 K := t
  let y' : ModGL Tag.E6 L := y
  let s' : ModGL Tag.E6 L := s
  have ht' : t' ∈ twistedE6RootGroup K σ := ht
  have hty' : baseChangeGL (algebraMap K L) t' = y' := hty
  have hys' : (MulAut.conj g0'⁻¹).toMonoidHom y' = s' := hys
  have hs_eq : s' = g0'⁻¹ * baseChangeGL (algebraMap K L) t' * g0' := by
    rw [← hys', ← hty']
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hsH : s ∈ torusGroup Tag.E6 L := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hsT).1
  obtain ⟨a, hs_root⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hsH
  obtain ⟨u₀, hu₀⟩ := exists_e6RootParams_eq a
  obtain ⟨k, hkfin, ι, g₃, u₃, hι, hg₃mem, hg₃, hu₃⟩ :=
    twE6_descent_packet (K := K) (g₀ := D.g0) D.g0_mem u₀
  haveI : Finite k := hkfin
  haveI : CharP k 2 := Subfield.charP k 2
  have hg₃' : baseChangeGL k.subtype g₃ = g0' := hg₃
  have hcomp : Fr.comp k.subtype = k.subtype.comp (iterateFrobenius k 2 1) := by
    ext c
    simp only [RingHom.comp_apply]
    rw [hFr, iterateFrobenius_def, map_pow]
    norm_num
  have hLangL : twistHom TwistTag.E6 L Fr D.g0 = D.g0 * D.n := by
    simpa [hΦ] using D.lang
  have hnc : baseChangeGL k.subtype
      (canonicalRep (coxeterSystem Tag.E6) k ((coxeterSystem Tag.E6).wordProd ω)) = D.n := by
    rw [baseChangeGL_canonicalRep, hn]
  have hLangk : twistHom TwistTag.E6 k (iterateFrobenius k 2 1) g₃ =
      g₃ * canonicalRep (coxeterSystem Tag.E6) k ((coxeterSystem Tag.E6).wordProd ω) :=
    l10mincl_twistHom_lang_descent TwistTag.E6 k.subtype (iterateFrobenius k 2 1) Fr hcomp
      hg₃ hnc hLangL
  obtain ⟨sl, hsl, hπ⟩ := twE6_fixed_lift (K := K) hK4 σ hσ2 ι ω hg₃mem hLangk ht'
  have hbase : (fun i => Units.map k.subtype.toMonoidHom (e6RootParams u₃ i)) = a := by
    rw [← l10mincl_e6RootParams_map (ι := k.subtype) u₃, hu₃, hu₀]
  have hπ' : ((e6Isogeny k sl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 (e6RootParams u₃) := by
    apply baseChangeGL_injective (f := k.subtype)
    rw [hπ, baseChangeGL_rootDiagUnit]
    simp only [map_mul, map_inv]
    rw [baseChangeGL_baseChangeGL, hι, hg₃', ← hs_eq, hbase]
    exact hs_root
  obtain ⟨u, hu_fix, hu_params⟩ := twE6_fixed_lift_torus ω hsl u₃ hπ'
  refine Subgroup.mem_map.2 ⟨fun j => Units.map k.subtype.toMonoidHom (u j), ?_, ?_⟩
  · rw [twE6Pfix]
    change twE6Fp Fr ω (fun j => Units.map k.subtype.toMonoidHom (u j)) =
      (fun j => Units.map k.subtype.toMonoidHom (u j))
    have hmap := twE6Fp_map (ι := k.subtype) (θ := iterateFrobenius k 2 1) (Fr := Fr) hcomp ω u
    rw [hmap, hu_fix]
  · change rootDiagUnit Tag.E6
        (e6RootParams (fun j => Units.map k.subtype.toMonoidHom (u j))) = s
    rw [l10mincl_e6RootParams_map (ι := k.subtype) u, hu_params, hbase, ← hs_root]

end CFSG.StandardType.TwE6Tori

end
