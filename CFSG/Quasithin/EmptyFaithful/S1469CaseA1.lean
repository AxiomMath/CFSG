module

public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.S1469CaseA0
public import CFSG.Quasithin.EmptyFaithful.S1469Sev

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.QuasithinUnique.Ch1

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.blocks_of_ctx (i1 : Input1469C126) (i2 : Input1469Lin2) {H : Subgroup G} {u : G}
    {I : Subgroup G} (c : Ctx1469 T M H u I) (hchar : CharTwo I) :
    ∃ (r : ℕ) (K : Fin r → Subgroup G), IsBlockProduct I (T ⊓ I) r K ∧
      (∀ i, ¬ K i ≤ I ⊓ mcOf T) ∧ ∀ i, IsAltType (K i) 3 ∨ IsAltType (K i) 5 := by
  have S := c.setting
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.hyp1281.omegaOneCenter_ne_bot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hSQ : IsSQTKTC I := S.isSQTKTC_of_pCoreOf_ne_bot c.hI.1.1.1.2
  obtain ⟨r, K, hK, hnotle⟩ := i1 G I (T ⊓ I) (I ⊓ mcOf T) hSQ hchar c.minPar c.cgs_le
  have hIG : ¬ I ≤ mcOf T := c.hI.1.1.2.1
  have hlin : ¬ ∃ i, ∃ n : ℕ, 1 < n ∧ IsLin2Type (K i) n := by
    intro h
    have hzT : z ∈ T := S146T.Z_le hzZ
    have huQ : u ∈ pCoreOf 2 (mcOf T) := S.conjClosure_le_pCoreOf_mcOf c.hH c.hu.mem
    have hQ1T : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_mcOf_le
    have hzu : z ∈ tU T u := (S146T.mem_tU_iff).mpr ⟨hzT,
      commutatorElement_eq_one_iff_mul_comm.mpr (S146T.comm_Z_T (hQ1T huQ) hzZ).symm⟩
    have hzI : z ∈ I := c.hI.1.1.1.1 hzu
    have hzS : z ∈ quasithinOmegaOneCenter (T ⊓ I) :=
      (mem_quasithinOmegaOneCenter_iff).mpr ⟨⟨hzT, hzI⟩,
        Subgroup.mem_centralizer_iff.mpr fun g hg => S146T.comm_Z_T hg.1 hzZ, S146T.Z_sq hzZ⟩
    have hcen := S.mcOf_eq_centralizer hzZ hz1'
    have h2 := i2 G I (T ⊓ I) (I ⊓ mcOf T) z r K hSQ hchar c.minPar hK hzS hz1'
      (by rw [hcen]) hnotle h
    have hzG : z ∈ mcOf T := Subgroup.mem_centralizer_iff.mpr fun y hy =>
      S146T.comm_Z_T (S146T.Z_le hy) hzZ
    have hzc : z ∈ centerOf (I ⊓ mcOf T) :=
      ⟨⟨hzI, hzG⟩, Subgroup.mem_centralizer_iff.mpr fun g hg =>
        (Subgroup.mem_centralizer_iff.mp hg.2 z hzZ).symm⟩
    have hzcI := h2 hzc
    apply hIG
    rw [hcen]
    intro g hg
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    exact (Subgroup.mem_centralizer_iff.mp hzcI.2 g hg).symm
  refine ⟨r, K, hK, hnotle, fun i => ?_⟩
  rcases (hK.2.2.1 i).2 with ⟨n, hn, hl⟩ | h | h
  · exact absurd ⟨i, n, hn, hl⟩ hlin
  · exact Or.inl h
  · exact Or.inr h

theorem Setting146.two_a5_of_ctx (i3 : Input1469C61) (h1 : Stage1463One) (h2 : Stage1463Two)
    (h4 : Stage1463Four) {H : Subgroup G} {u : G} {I : Subgroup G} (c : Ctx1469 T M H u I)
    (hchar : CharTwo I) {r : ℕ} {K : Fin r → Subgroup G} (hK : IsBlockProduct I (T ⊓ I) r K)
    (hnot : ∀ i, ¬ K i ≤ I ⊓ mcOf T) (hty : ∀ i, IsAltType (K i) 3 ∨ IsAltType (K i) 5) :
    r = 2 ∧ ∀ i, IsAltType (K i) 5 := by
  by_contra hno
  have S := c.setting
  have hSQ : IsSQTKTC I := S.isSQTKTC_of_pCoreOf_ne_bot c.hI.1.1.1.2
  obtain ⟨ρ, hρT, hρA, hρN, hρ2⟩ :=
    exists_sq_mem_normalizer_of_lt S.hyp.sylow.1 (S.tI_lt c.hI.1.1)
  have hidx := (h1 G T M S H c.hH u c.hu).2.1
  have hN0 := h2 G T M S H c.hH u c.hu
  have hNu := (h4 G T M S H c.hH u c.hu).1
  have hb : ∀ X : Subgroup G, X ≤ T ⊓ I → X ≠ ⊥ → I ≤ Subgroup.normalizer (X : Set G) →
      (T ⊓ I ⊔ Subgroup.zpowers ρ) ⊓ Subgroup.normalizer (X : Set G) ≤ T ⊓ I := by
    intro X hXS hX1 hXI g hg
    obtain ⟨_, hTX, _⟩ := S.obs_a c.hu hidx hN0 hNu c.hI.1 hXS hX1 hXI
    have hgT : g ∈ T := (sup_le inf_le_left (Subgroup.zpowers_le.mpr hρT)) hg.1
    have : g ∈ T ⊓ Subgroup.normalizer (X : Set G) := ⟨hgT, hg.2⟩
    rw [hTX] at this
    exact this
  have := i3 G I (T ⊓ I) (I ⊓ mcOf T) r K ρ hSQ hchar c.minPar hK hnot hty hno hρN hρA hρ2 hb
  exact absurd this (not_le.mpr c.hTI)

theorem Setting146.ctxA5_of_ctx (i1 : Input1469C126) (i2 : Input1469Lin2) (i3 : Input1469C61)
    (h1 : Stage1463One) (h2 : Stage1463Two) (h4 : Stage1463Four) {H : Subgroup G} {u : G}
    {I : Subgroup G} (c : Ctx1469 T M H u I) (hchar : CharTwo I) :
    ∃ (K₁ K₂ : Subgroup G) (ρ : G), Ctx1469A5 T M H u I K₁ K₂ ρ := by
  have S := c.setting
  obtain ⟨r, K, hK, hnot, hty⟩ := Setting146.blocks_of_ctx i1 i2 c hchar
  obtain ⟨hr, h5⟩ := Setting146.two_a5_of_ctx i3 h1 h2 h4 c hchar hK hnot hty
  subst hr
  have hKeq : K = ![K 0, K 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hKeq] at hK
  obtain ⟨ρ, hρT, hρA, hρN, hρ2⟩ :=
    exists_sq_mem_normalizer_of_lt S.hyp.sylow.1 (S.tI_lt c.hI.1.1)
  have hidx := (h1 G T M S H c.hH u c.hu).2.1
  have hN0 := h2 G T M S H c.hH u c.hu
  have hNu := (h4 G T M S H c.hH u c.hu).1
  exact ⟨K 0, K 1, ρ, c, hchar, hK, ⟨h5 0, h5 1⟩, hnot 0, ⟨hρT, hρN, hρA, hρ2⟩,
    fun X hXS hX1 hXI => S.obs_a c.hu hidx hN0 hNu c.hI.1 hXS hX1 hXI⟩


end CFSG.Quasithin
