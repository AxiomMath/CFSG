module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Levi2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix

variable {K : Type} [Field K] [CharP K 2]

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

@[expose] noncomputable def psiG {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H) (g : ↥(cayleyGroup K)) :
    ↥(cayleyGroup K) →* MulAut W :=
  H.subtype.comp ((rhoG hc0 hc1 π).comp (MulAut.conj g).toMonoidHom)

theorem psiG_apply {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) (g γ : ↥(cayleyGroup K)) :
    psiG hc0 hc1 π g γ = ((rhoG hc0 hc1 π (g * γ * g⁻¹) : ↥H) : MulAut W) := rfl

theorem psiG_injective (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (g : ↥(cayleyGroup K)) : Function.Injective (psiG hc0 hc1 π g) :=
  H.subtype_injective.comp ((rhoG_bijective hf hc0 hc1).1.comp (MulAut.conj g).injective)

theorem map_stabQ_eq (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (g : ↥(cayleyGroup K)) (S : Submodule K (Ix3 → K)) :
    (stabQ S).map (psiG hc0 hc1 π g) =
      H ⊓ Ch11.SecA.stabW (hf.pre (gmapG g S).toAddSubgroup) := by
  ext x
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [psiG_apply]
    refine Subgroup.mem_inf.mpr ⟨(rhoG hc0 hc1 π _).2, ?_⟩
    rw [IsCoord.rhoG_mem_stabW_iff hf hc0 hc1 (hf.le_pre _), hf.img_pre]
    intro y
    change y ∈ gmapG g S ↔ _ ∈ gmapG g S
    rw [mem_gmapG, mem_gmapG, conj_g2Act]
    exact (mem_stabQ.mp hγ) _
  · rintro ⟨hxH, hxS⟩
    obtain ⟨δ, hδ⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨x, hxH⟩
    have hδx : ((rhoG hc0 hc1 π δ : ↥H) : MulAut W) = x := congrArg Subtype.val hδ
    have hδS : ((rhoG hc0 hc1 π δ : ↥H) : MulAut W) ∈
        Ch11.SecA.stabW (hf.pre (gmapG g S).toAddSubgroup) := by
      rw [hδx]
      exact hxS
    rw [IsCoord.rhoG_mem_stabW_iff hf hc0 hc1 (hf.le_pre _), hf.img_pre] at hδS
    refine ⟨g⁻¹ * δ * g, mem_stabQ.mpr fun w => ?_, ?_⟩
    · have h1 := hδS (g2Act g w)
      change g2Act g w ∈ gmapG g S ↔ g2Act δ (g2Act g w) ∈ gmapG g S at h1
      rw [mem_gmapG, mem_gmapG, g2Act_inv_apply] at h1
      rw [h1, g2Act_mul_apply, g2Act_mul_apply]
    · rw [psiG_apply, show g * (g⁻¹ * δ * g) * g⁻¹ = δ by group, hδx]

end Real

theorem factLeviG2_holds : Ch11.SecA.FactLeviG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP i U hi hU
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have h4 := four_le_card hn hK
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four h4
  have := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple (K := K) hK4
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  rw [← hK] at hU
  obtain ⟨S, hS, hc, rfl⟩ := exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg hU
  rw [eq_stdF_of_card hS hc]
  have hA : perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapG g (stdF K i)).toAddSubgroup)) =
      (perfectCore (stabQ (stdF K i))).map (psiG hc0 hc1 π g) :=
    (congrArg perfectCore (map_stabQ_eq hf hc0 hc1 g _)).symm.trans
      (perfectCore_map _ (psiG_injective hf hc0 hc1 g) _)
  let e := (MulEquiv.subgroupCongr hA).trans
    ((perfectCore (stabQ (stdF K i))).equivMapOfInjective _ (psiG_injective hf hc0 hc1 g)).symm
  have hna := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_nonabelian hK4
  rcases hi with rfl | rfl
  · let e1 := e.trans (MulEquiv.subgroupCongr (perfectCore_stabQ_one h4))
    exact ⟨(QuotientGroup.congr _ _ e1 (CFSG.pCore_map_iso 2 e1)).trans
      (CFSG.QuasithinUnique.Vol2Native.A312L.modO2EquivOfHom hna levi1 levi1_surjective
        isPGroup_ker_levi1)⟩
  · exact ⟨(QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)).trans
      (CFSG.QuasithinUnique.Vol2Native.A312L.modO2EquivOfHom hna levi2 (levi2_surjective h4)
        isPGroup_ker_levi2)⟩

theorem factSylowLeviG2_holds : Ch11.SecA.FactSylowLeviG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have h4 := four_le_card hn hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  rw [← hK] at hU
  obtain ⟨S, hS, hc, rfl⟩ := exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg hU
  rw [eq_stdF_of_card hS hc, ← map_stabQ_eq hf hc0 hc1 g,
    perfectCore_map _ (psiG_injective hf hc0 hc1 g)]
  intro x hx
  obtain ⟨u, hu, rfl⟩ := (hg x).mp hx
  exact ⟨u, U0_le_perfectCore_stabQ_one h4 hu, rfl⟩

end CFSG.Quasithin.Vol2.Ch11.G2Q8
