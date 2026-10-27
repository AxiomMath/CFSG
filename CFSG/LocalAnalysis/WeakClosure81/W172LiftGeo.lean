module

public import CFSG.LocalAnalysis.WeakClosure81.W172D3
public import CFSG.LocalAnalysis.WeakClosure81.W172Lemma229
public import CFSG.LocalAnalysis.WeakClosure81.W172LiftRank
public import CFSG.LocalAnalysis.WeakClosure81.W172Two5

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

theorem w172_rho_one_of_mem_pCore (c : MinCex172 D V₀ V H) (M : ModDataE H (eOmegaZ H D.T))
    {q : ↥H} (hq : q ∈ CFSG.pCore 2 ↥H) : M.ρ q = 1 := by
  have h1 : (q : G) ∈ pCoreOf 2 H := Subgroup.mem_map_of_mem H.subtype hq
  rw [← c.inf_centralizer_eOmegaZ_eq] at h1
  exact (M.ρ_eq_one_iff q).2 h1.2

theorem w172_mem_pCore_of_rho_eq_one (c : MinCex172 D V₀ V H) (M : ModDataE H (eOmegaZ H D.T))
    {t : ↥H} (ht : (t : G) ∈ D.T) (h1 : M.ρ t = 1) : t ∈ CFSG.pCore 2 ↥H := by
  have h2 : (t : G) ∈ pCoreOf 2 H := by
    rw [← c.inf_centralizer_eOmegaZ_eq]
    exact ⟨ht, (M.ρ_eq_one_iff t).1 h1⟩
  exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective H)).mp h2

theorem w172_rho_eq_iff_mk_eq (c : MinCex172 D V₀ V H) (M : ModDataE H (eOmegaZ H D.T))
    {x y : ↥H} (hx : (x : G) ∈ D.T) (hy : (y : G) ∈ D.T) :
    M.ρ x = M.ρ y ↔
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) x = QuotientGroup.mk' (CFSG.pCore 2 ↥H) y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  constructor
  · intro h
    refine c.w172_mem_pCore_of_rho_eq_one M (D.T.mul_mem (D.T.inv_mem hx) hy) ?_
    rw [map_mul, map_inv, h, inv_mul_cancel]
  · intro h
    have h1 := c.w172_rho_one_of_mem_pCore M h
    rw [map_mul, map_inv] at h1
    exact inv_mul_eq_one.mp h1

theorem w172_relIndex_le_two (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) 1 g) (hgT : vInH V H g ≤ D.T) :
    (conjSubgroup D.M g).relIndex D.T ≤ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ (Hyp183.normalizer_eOmegaZ H D.T)
  have hT : IsPGroup 2 D.T := (isSylowOf_two_iff_isSylowIn.mp D.sylowM).isPGroup
  have hTH : D.T ≤ H := c.hyp.hyp171.2.1
  have hm := w172_two5 h162 c hg
  have hiS : 1 ≤ (c.ctx188 h162).iStar := (c.ctx188 h162).iStar_pos
  obtain ⟨e, he, hge⟩ := (c.ctx188 h162).w172_exists_mem_D M ⟨hg, hm.trans hiS⟩ hm
  have hI := (c.ctx188 h162).w172_invSys M
  have hsq : e * e = 1 := hI.sq e he
  have he1 : e ≠ 1 := hI.ne_one e he
  obtain ⟨a', haA, hρa⟩ : ∃ a' : ↥H, (a' : G) ∈ vInH V H g ∧ M.ρ a' = e :=
    M.mem_img.1 (hge ▸ Subgroup.mem_zpowers e)
  have haT : (a' : G) ∈ D.T := hgT haA
  have heT : e ∈ M.img D.T := M.mem_img.2 ⟨a', haT, hρa⟩
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  let ρbar : (↥H ⧸ CFSG.pCore 2 ↥H) →* LGL 2 M.W :=
    QuotientGroup.lift (CFSG.pCore 2 ↥H) M.ρ
      (fun q hq => (MonoidHom.mem_ker).2 (c.w172_rho_one_of_mem_pCore M hq))
  have hρbar : ∀ x : ↥H, ρbar (π x) = M.ρ x := fun x => rfl
  have hfib : ∀ x y : ↥H, (x : G) ∈ D.T → (y : G) ∈ D.T → (M.ρ x = M.ρ y ↔ π x = π y) :=
    fun x y hx hy => c.w172_rho_eq_iff_mk_eq M hx hy
  have hconj : ∀ t : ↥H, π t * π a' * (π t)⁻¹ = π (t * a' * t⁻¹) := fun t => by
    rw [map_mul, map_mul, map_inv]
  have hconjT : ∀ t : ↥H, (t : G) ∈ D.T → ((t * a' * t⁻¹ : ↥H) : G) ∈ D.T := by
    intro t ht
    have := D.T.mul_mem (D.T.mul_mem ht haT) (D.T.inv_mem ht)
    simpa using this
  have hconjD : ∀ t : ↥H, (t : G) ∈ D.T →
      M.ρ (t * a' * t⁻¹) ∈ (c.ctx188 h162).w172D M ∧
        e * M.ρ (t * a' * t⁻¹) = M.ρ (t * a' * t⁻¹) * e := by
    intro t ht
    have hρ : M.ρ (t * a' * t⁻¹) = M.ρ t * e * (M.ρ t)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hρa]
    have hrt : M.ρ t ∈ M.img H := M.mem_img.2 ⟨t, t.2, rfl⟩
    have hD' : M.ρ (t * a' * t⁻¹) ∈ (c.ctx188 h162).w172D M := by
      rw [hρ]
      exact hI.conj_mem e he _ hrt
    have hT' : M.ρ (t * a' * t⁻¹) ∈ M.img D.T :=
      M.mem_img.2 ⟨t * a' * t⁻¹, hconjT t ht, rfl⟩
    exact ⟨hD', (c.ctx188 h162).w172_comm_of_mem_img M hT he hD' heT hT'⟩
  have hd₀ : π a' * π a' = 1 := by
    rw [← map_mul, ← map_one π]
    refine (hfib (a' * a') 1 ?_ ?_).1 ?_
    · simpa using D.T.mul_mem haT haT
    · simpa using D.T.one_mem
    · rw [map_mul, map_one, hρa]
      exact hsq
  have hd₀1 : π a' ≠ 1 := by
    intro h
    apply he1
    rw [← hρa]
    have h1 := (hfib a' 1 haT (by simpa using D.T.one_mem)).2 (by rw [map_one]; exact h)
    rwa [map_one] at h1
  have hcomm : ∀ s ∈ (D.T.subgroupOf H).map π,
      π a' * (s * π a' * s⁻¹) = (s * π a' * s⁻¹) * π a' := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
    have ht' : (t : G) ∈ D.T := ht
    rw [hconj t, ← map_mul, ← map_mul]
    refine (hfib _ _ ?_ ?_).1 ?_
    · simpa using D.T.mul_mem haT (by simpa using hconjT t ht')
    · simpa using D.T.mul_mem (by simpa using hconjT t ht') haT
    · have h2 := (hconjD t ht').2
      rw [← hρa, ← map_mul, ← map_mul] at h2
      exact h2
  have hno : ∀ s ∈ (D.T.subgroupOf H).map π, s * π a' * s⁻¹ ≠ π a' →
      ∀ u : ↥H ⧸ CFSG.pCore 2 ↥H, Odd (orderOf u) → π a' * u * (π a')⁻¹ = u⁻¹ →
        (s * π a' * s⁻¹) * u * (s * π a' * s⁻¹)⁻¹ = u⁻¹ → u = 1 := by
    intro s hs hne u hodd hu1 hu2
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
    have ht' : (t : G) ∈ D.T := ht
    obtain ⟨x, rfl⟩ : ∃ x : ↥H, π x = u := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) u
    rw [hconj t] at hne hu2
    have hdvd : orderOf (M.ρ x) ∣ orderOf (π x) := by
      have := orderOf_map_dvd ρbar (π x)
      rwa [hρbar] at this
    have hoddρ : Odd (orderOf (M.ρ x)) := Odd.of_dvd_nat hodd hdvd
    have hxL : M.ρ x ∈ M.img H := M.mem_img.2 ⟨x, x.2, rfl⟩
    have hex : e * M.ρ x * e⁻¹ = (M.ρ x)⁻¹ := by
      have := congrArg ρbar hu1
      simp only [map_mul, map_inv, hρbar] at this
      rwa [hρa] at this
    have hfx : M.ρ (t * a' * t⁻¹) * M.ρ x * (M.ρ (t * a' * t⁻¹))⁻¹ = (M.ρ x)⁻¹ := by
      have := congrArg ρbar hu2
      simpa only [map_mul, map_inv, hρbar] using this
    have hne' : e ≠ M.ρ (t * a' * t⁻¹) := by
      intro h
      exact hne (((hfib a' (t * a' * t⁻¹) haT (hconjT t ht')).1 (hρa.trans h)).symm)
    have hone : M.ρ x = 1 :=
      w172_eq_one_of_inverted hI he (hconjD t ht').1 hne' (hconjD t ht').2 hxL hoddρ hex hfx
    have hxC : (x : G) ∈ Subgroup.centralizer (eOmegaZ H D.T : Set G) :=
      (M.ρ_eq_one_iff x).1 hone
    have hcm : ((⁅x, a'⁆ : ↥H) : G) ∈ pCoreOf 2 H :=
      c.w172_comm_centralizer_le_pCoreOf h162 hg ⟨x.2, hxC⟩ haA
    have hcm' : ⁅x, a'⁆ ∈ CFSG.pCore 2 ↥H :=
      (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective H)).mp hcm
    have h1 : ⁅π x, π a'⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 hcm'
    have hc : π x * π a' = π a' * π x := commutatorElement_eq_one_iff_mul_comm.1 h1
    have hc' : π a' * π x * (π a')⁻¹ = π x := by
      rw [← hc, mul_inv_cancel_right]
    have hinv : π x * π x = 1 := by
      rw [hc'] at hu1
      exact mul_eq_one_iff_eq_inv.2 hu1
    have hdvd2 : orderOf (π x) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hinv)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h | h
    · exact orderOf_eq_one_iff.1 h
    · rw [h] at hodd
      have := Nat.odd_iff.mp hodd
      omega
  haveI : Group.IsSolvable ↥H := c.solv
  have hQp : IsPGroup 2 ↥(CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup
  have hO2 : CFSG.pCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  obtain ⟨p, hp, hp2, ⟨B₁, hB₁ea, hB₁card⟩, ⟨B₂, hB₂ea, hB₂c, hB₂card⟩⟩ :=
    w172_lift_rank hQp inferInstance hO2 hd₀ hd₀1 hcomm hno
  have hKfwd : ∀ b : ↥H,
      π b ∈ Subgroup.centralizer ({π a'} : Set (↥H ⧸ CFSG.pCore 2 ↥H)) →
        M.ρ b * e = e * M.ρ b := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff] at hb
    have := congrArg ρbar hb
    simp only [map_mul, hρbar] at this
    rwa [hρa] at this
  have hTK : ∀ x : ↥H, (x : G) ∈ D.T → ((x : G) ∈ conjSubgroup D.M g ↔
      π x ∈ Subgroup.centralizer ({π a'} : Set (↥H ⧸ CFSG.pCore 2 ↥H))) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (x : G) ∈ conjSubgroup D.M g ↔ M.ρ x * e = e * M.ρ x :=
      w172_mem_conj_iff_comm h162 c hg hm M hge hsq he1 x.2
    have hxa : ((x * a' : ↥H) : G) ∈ D.T := D.T.mul_mem hx haT
    have hax : ((a' * x : ↥H) : G) ∈ D.T := D.T.mul_mem haT hx
    rw [h1, ← hρa, ← map_mul M.ρ x a', ← map_mul M.ρ a' x, ← map_mul π x a', ← map_mul π a' x]
    exact hfib _ _ hxa hax
  have hr : (Subgroup.centralizer ({π a'} : Set (↥H ⧸ CFSG.pCore 2 ↥H))).relIndex
      ((D.T.subgroupOf H).map π) = (conjSubgroup D.M g).relIndex D.T := by
    have h2 : (Subgroup.centralizer ({π a'} : Set (↥H ⧸ CFSG.pCore 2 ↥H))).comap π ⊓
        D.T.subgroupOf H = (conjSubgroup D.M g).subgroupOf H ⊓ D.T.subgroupOf H := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(hTK x h2).2 h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(hTK x h2).1 h1, h2⟩
    calc (Subgroup.centralizer ({π a'} : Set (↥H ⧸ CFSG.pCore 2 ↥H))).relIndex
          ((D.T.subgroupOf H).map π)
        = ((Subgroup.centralizer ({π a'} : Set (↥H ⧸ CFSG.pCore 2 ↥H))).comap π).relIndex
            (D.T.subgroupOf H) := (Subgroup.relIndex_comap _ π _).symm
      _ = ((Subgroup.centralizer ({π a'} : Set (↥H ⧸ CFSG.pCore 2 ↥H))).comap π ⊓
            D.T.subgroupOf H).relIndex (D.T.subgroupOf H) := (Subgroup.inf_relIndex_right _ _).symm
      _ = ((conjSubgroup D.M g).subgroupOf H ⊓ D.T.subgroupOf H).relIndex
            (D.T.subgroupOf H) := by rw [h2]
      _ = ((conjSubgroup D.M g).subgroupOf H).relIndex (D.T.subgroupOf H) :=
          Subgroup.inf_relIndex_right _ _
      _ = (conjSubgroup D.M g).relIndex D.T := Subgroup.relIndex_subgroupOf hTH
  rw [hr] at hB₁card hB₂card
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (conjSubgroup D.M g).relIndex D.T = 2 ^ n :=
    hT.index ((conjSubgroup D.M g).subgroupOf D.T)
  by_contra hgt
  have hgt3 : 3 ≤ (conjSubgroup D.M g).relIndex D.T := by omega
  have hr4 : 4 ≤ (conjSubgroup D.M g).relIndex D.T := by
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have h2 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hB₁le : B₁.map H.subtype ≤ H := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hrank1 : (conjSubgroup D.M g).relIndex D.T ≤ CFSG.Open.pRank p H :=
    CFSG.SectionRank.le_pRank hp.one_lt hB₁le (hB₁ea.map H.subtype)
      (by rw [Subgroup.card_map_of_injective H.subtype_injective]; exact hB₁card)
  have h3 : 3 < CFSG.pRank p ↥H := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    omega
  have h4 := c.hyp.hyp171.2.2 p hp hp2 h3 g
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h4
  have hB₂le : B₂.map H.subtype ≤ H ⊓ conjSubgroup D.M g := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨b.2, ?_⟩
    exact (w172_mem_conj_iff_comm h162 c hg hm M hge hsq he1 b.2).2 (hKfwd b (hB₂c b hb))
  have hrank2 : (conjSubgroup D.M g).relIndex D.T - 1 ≤
      CFSG.Open.pRank p (H ⊓ conjSubgroup D.M g) :=
    CFSG.SectionRank.le_pRank hp.one_lt hB₂le (hB₂ea.map H.subtype)
      (by rw [Subgroup.card_map_of_injective H.subtype_injective]; exact hB₂card)
  omega

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end
