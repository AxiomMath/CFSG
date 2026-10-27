module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutLieMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieMain
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Milestones.ASVolI.F431.J2
public import CFSG.Milestones.ASVolI.F431.JOdd

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Generic

variable {K : Type*} [Group K]

theorem burnsideF4m_inf_normal_ne_bot [Finite K] {T I : Subgroup K} (hT : IsSylowTwoOf T ⊤)
    (hI : I.Normal) {j : K} (hj : j ∈ I) (hj1 : j ≠ 1) {k : ℕ} (hk : orderOf j = 2 ^ k) :
    T ⊓ I ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers j) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨c, -, hc⟩ := F7.isSylowTwoOf_exists_conj_le hT le_top hp
  have hjT : c⁻¹ * j * c ∈ T := mem_conjSub.mp (hc (Subgroup.mem_zpowers j))
  have hjI : c⁻¹ * j * c ∈ I := by
    have := hI.conj_mem j hj c⁻¹
    simpa using this
  intro hbot
  have hmem : c⁻¹ * j * c ∈ T ⊓ I := ⟨hjT, hjI⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  apply hj1
  calc j = c * (c⁻¹ * j * c) * c⁻¹ := by group
    _ = 1 := by rw [hmem]; group

theorem burnsideF4m_center_mem_of_center_T [Finite K] {T I N : Subgroup K} {z : K}
    (hT : IsSylowTwoOf T ⊤) (hI : I.Normal) (hTI : T ⊓ I ≠ ⊥)
    (hcen : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ N, m * z * m⁻¹ = w)
    {w : K} (hw : w ∈ T) (hwc : ∀ y ∈ T, y * w = w * y) : w ∈ I := by
  by_cases hw1 : w = 1
  · rw [hw1]; exact I.one_mem
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥T := hT.2.1.isNilpotent
  haveI hHn : (I.subgroupOf T).Normal := Subgroup.normal_subgroupOf
  have hHne : I.subgroupOf T ≠ ⊥ := by
    intro h
    apply hTI
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxI⟩
    have hmem : (⟨x, hxT⟩ : ↥T) ∈ I.subgroupOf T := hxI
    rw [h, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hmem
  obtain ⟨w₁, hw₁1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hHne)
  obtain ⟨hw₀I, hw₀Z⟩ := w₁.2
  set w₀ : ↥T := (w₁ : ↥T) with hw₀def
  have hw₀I' : ((w₀ : ↥T) : K) ∈ I := hw₀I
  have hw₀c : ∀ y ∈ T, y * (w₀ : K) = (w₀ : K) * y := by
    intro y hy
    have := Subgroup.mem_center_iff.mp hw₀Z ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hw₀ne : ((w₀ : ↥T) : K) ≠ 1 := by
    intro h
    exact hw₁1 (Subtype.ext (Subtype.ext h))
  obtain ⟨m₀, -, hm₀⟩ := hcen _ w₀.2 hw₀c hw₀ne
  obtain ⟨m, -, hm⟩ := hcen w hw hwc hw1
  have hconj : w = (m * m₀⁻¹) * (w₀ : K) * (m * m₀⁻¹)⁻¹ := by
    rw [← hm₀, ← hm]
    group
  rw [hconj]
  exact hI.conj_mem _ hw₀I' _

theorem burnsideF4m_eq_of_sylow_le {G : Type*} [Group G] [Finite G] {S H P : Subgroup G}
    (hS : IsSylowTwoOf S H) (hP : IsPGroup 2 P) (hSP : S ≤ P) (hPH : P ≤ H) : P = S := by
  obtain ⟨x, -, hx⟩ := F7.isSylowTwoOf_exists_conj_le hS hPH hP
  have h1 : Nat.card P ≤ Nat.card S := by
    have := Subgroup.card_le_of_le hx
    have e : Nat.card ↥(conjSub x S) = Nat.card ↥S :=
      Subgroup.card_map_of_injective (MulAut.conj x).injective
    rwa [e] at this
  exact (Subgroup.eq_of_le_of_card_ge hSP h1).symm

theorem burnsideF4m_ctr_le_of_transport {E : Type} [Group E] [Finite E] (θ : E ≃* K)
    {Gp M₁ M₂ : Subgroup E} (hGp : Gp.Normal) {T : Subgroup K} (hT : IsSylowTwoOf T ⊤)
    (hTM : T.comap θ.toMonoidHom ≤ M₁ ⊓ M₂)
    (hZ : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ∈ Gp.map θ.toMonoidHom)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T' : Subgroup E := T.comap θ.toMonoidHom with hT'
  have hT'map : T'.map θ.toMonoidHom = T := Subgroup.map_comap_eq_self_of_surjective θ.surjective T
  have hT'p : IsPGroup 2 T' := by
    have h := hT.2.1.comap_of_injective (θ.toMonoidHom) θ.injective
    exact h
  have hT'syl : IsSylowTwoOf T' ⊤ := by
    refine ⟨le_top, hT'p, ?_⟩
    have h1 : (T'.subgroupOf ⊤).index = T'.index := Subgroup.relIndex_top_right T'
    have h2 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    have h3 : T'.index = T.index := by
      rw [hT']
      exact Subgroup.index_comap_of_surjective T θ.surjective
    rw [h1, h3, ← h2]
    exact hT.2.2
  have hT'12 : IsSylowTwoOf T' (M₁ ⊓ M₂) := F7.isSylowTwoOf_mono_right hT'syl hTM le_top
  obtain ⟨c, hc, hle⟩ := F7.isSylowTwoOf_exists_conj_le hT'12 hTb.1 hTb.2.1
  have hcp : IsPGroup 2 (conjSub c T') := F7.isPGroup_conjSub hT'p
  have hcle : conjSub c T' ≤ M₁ ⊓ M₂ := by
    intro y hy
    rw [mem_conjSub] at hy
    have := (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem hc (hTM hy)) ((M₁ ⊓ M₂).inv_mem hc)
    simpa [mul_assoc] using this
  have heq : conjSub c T' = Tb := burnsideF4m_eq_of_sylow_le hTb hcp hle hcle
  have hxT : x ∈ conjSub c T' := heq ▸ hx.1
  have hx' : c⁻¹ * x * c ∈ T' := mem_conjSub.mp hxT
  have hx'c : ∀ y ∈ T', y * (c⁻¹ * x * c) = (c⁻¹ * x * c) * y := by
    intro y hy
    have hcy : c * y * c⁻¹ ∈ Tb := by
      rw [← heq, mem_conjSub]
      simpa [mul_assoc] using hy
    have h1 := (Subgroup.mem_centralizer_iff.mp hx.2) _ hcy
    calc y * (c⁻¹ * x * c) = c⁻¹ * ((c * y * c⁻¹) * x) * c := by group
      _ = c⁻¹ * (x * (c * y * c⁻¹)) * c := by rw [h1]
      _ = (c⁻¹ * x * c) * y := by group
  have himg : θ (c⁻¹ * x * c) ∈ Gp.map θ.toMonoidHom := by
    refine hZ _ hx' fun y hy => ?_
    obtain ⟨y', rfl⟩ := θ.surjective y
    have hy' : y' ∈ T' := hy
    rw [← map_mul, ← map_mul, hx'c y' hy']
  obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp himg
  have hgx : g = c⁻¹ * x * c := θ.injective hge
  have hgx' : x = c * g * c⁻¹ := by rw [hgx]; group
  rw [hgx']
  exact hGp.conj_mem g hg c

end Generic

section Bridge

set_option linter.unusedSectionVars false


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_mem_of_odd [Gp.Normal] [Finite E] (hodd : Odd Gp.index) {Tb H : Subgroup E}
    (hTb : IsSylowTwoOf Tb H) {x : E} (hx : x ∈ Tb) : x ∈ Gp := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hTb.2.1 ⟨x, hx⟩
  refine burnsideF4d_two_elt_mem hodd (k := k) ?_
  rw [Subgroup.orderOf_mk] at hk
  rw [← hk]
  exact pow_orderOf_eq_one x

theorem burnsideF4m_not_odd [Finite E] (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {TD : Subgroup ↥Gp}
    (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) (hodd : ¬ Odd Gp.index) :
    ¬ Odd (Nat.card ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K / Nat.card ↥Gp) := by
  haveI := hyp.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  have hK : Nat.card ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K = Nat.card E := by
    have : (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K = (burnsideF4d_rho Gp).range :=
      burnsideF4d_K_eq hyp.toHypF_4_4g hyam
    rw [this, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  rw [hK]
  have := Subgroup.card_mul_index Gp
  have hpos : 0 < Nat.card ↥Gp := Nat.card_pos
  rw [show Nat.card E / Nat.card ↥Gp = Gp.index by
    rw [← this, Nat.mul_div_cancel_left _ hpos]]
  exact hodd

theorem burnsideF4m_ctr_le_of_lieExt [Finite E] (hyp : HypF_4_4 κ 2 f Gp M₁ M₂)
    {TD : Subgroup ↥Gp} (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp))
    {T N : Subgroup ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K}
    {z : ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K}
    (hT : IsSylowTwoOf T ⊤) (hT1 : T ≤ (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).Mb1)
    (hT2 : T ≤ (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).Mb2)
    (hcen : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ N, m * z * m⁻¹ = w)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  haveI := hyp.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  have hK : (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K = (burnsideF4d_rho Gp).range :=
    burnsideF4d_K_eq hyp.toHypF_4_4g hyam
  let θ : E ≃* ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hK.symm)
  have hθ : ∀ e : E, ((θ e : ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K) : MulAut ↥Gp) =
      burnsideF4d_rho Gp e := fun e => rfl
  have hN1 : (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).N1 = M₁.map (burnsideF4d_rho Gp) :=
    burnsideF4d_N1_eq hyp.toHypF_4_4g hyam
  have hN2 : (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).N2 = M₂.map (burnsideF4d_rho Gp) :=
    burnsideF4d_N2_eq hyp.toHypF_4_4g hyam
  haveI : Finite ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K := Finite.of_equiv E θ.toEquiv
  have hTM : T.comap θ.toMonoidHom ≤ M₁ ⊓ M₂ := by
    intro e he
    have h1 : θ e ∈ (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).Mb1 := hT1 he
    have h2 : θ e ∈ (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).Mb2 := hT2 he
    rw [Subgroup.mem_subgroupOf, hθ, hN1] at h1
    rw [Subgroup.mem_subgroupOf, hθ, hN2] at h2
    obtain ⟨e1, he1, he1e⟩ := h1
    obtain ⟨e2, he2, he2e⟩ := h2
    exact ⟨hinj he1e ▸ he1, hinj he2e ▸ he2⟩
  have hInorm : (Gp.map θ.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ θ.surjective
  obtain ⟨j, hjG, hj1, k, hk⟩ := burnsideF4jb_exists_two_elt
    (burnsideF4jb_parabolics ChF.nativeChartCompatibility hyp)
  have hTI : T ⊓ Gp.map θ.toMonoidHom ≠ ⊥ :=
    burnsideF4m_inf_normal_ne_bot hT hInorm (Subgroup.mem_map_of_mem θ.toMonoidHom hjG)
      (fun h => hj1 (θ.injective (h.trans (map_one θ).symm)))
      ((orderOf_injective θ.toMonoidHom θ.injective j).trans hk)
  exact burnsideF4m_ctr_le_of_transport θ inferInstance hT hTM
    (fun w hw hwc => burnsideF4m_center_mem_of_center_T hT hInorm hTI hcen hw hwc) hTb hx

theorem burnsideF4m_ctr_le_G2 (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  by_cases hodd : Odd Gp.index
  · exact burnsideF4m_mem_of_odd hodd hTb hx.1
  obtain ⟨K, fK, finK, hcard, marking, h1, h2⟩ := burnsideF4g_chart_G2 hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  haveI : CharP K 2 := burnsideF4f_charP_of_card (by omega) hcard
  have hK3 : 3 ≤ Nat.card K := by
    rw [hcard]
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamG2 hK3 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_G2 hf hyp.model
  obtain ⟨T, S, g, z, I, hO | hO⟩ := G2.f431TwoOutLieProp_g2 f ↥Gp hmodel
    (burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).toLieAmalgamExt (burnsideF4m_not_odd hyp hTD hodd)
  · exact burnsideF4m_ctr_le_of_lieExt hyp hTD hO.sylow hO.T_le hO.T_le' hO.center_T hTb hx
  · exact burnsideF4m_ctr_le_of_lieExt hyp hTD hO.sylow hO.T_le' hO.T_le hO.center_T hTb hx

theorem burnsideF4m_ctr_le_D4tw (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  by_cases hodd : Odd Gp.index
  · exact burnsideF4m_mem_of_odd hodd hTb hx.1
  obtain ⟨K, fK, finK, sigma, hscope, marking, h1, h2⟩ := burnsideF4g_chart_D4tw hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamD4 sigma hscope marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_D4tw hyp.model
  have hf1 : 1 ≤ f := hyp.model.2.1
  obtain ⟨T, S, g, z, I, hO | hO⟩ := D4q.f431TwoOutLieProp_d4q f hf1 ↥Gp hmodel
    (burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).toLieAmalgamExt (burnsideF4m_not_odd hyp hTD hodd)
  · exact burnsideF4m_ctr_le_of_lieExt hyp hTD hO.sylow hO.T_le hO.T_le' hO.center_T hTb hx
  · exact burnsideF4m_ctr_le_of_lieExt hyp hTD hO.sylow hO.T_le' hO.T_le hO.center_T hTb hx

theorem burnsideF4m_ctr_le_U4 (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) (hf : 2 ≤ f)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  by_cases hodd : Odd Gp.index
  · exact burnsideF4m_mem_of_odd hodd hTb hx.1
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U4) hyp.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamU4 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_U4 hyp.model
  obtain ⟨T, S, g, z, t, V, hO | hO⟩ := Un.f431UnOutLieProp_four f hf ↥Gp hmodel
    (burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).toLieAmalgamExt (burnsideF4m_not_odd hyp hTD hodd)
  · exact burnsideF4m_ctr_le_of_lieExt hyp hTD hO.sylow hO.T_le hO.T_le' hO.center_T hTb hx
  · exact burnsideF4m_ctr_le_of_lieExt hyp hTD hO.sylow hO.T_le' hO.T_le hO.center_T hTb hx

theorem burnsideF4m_ctr_le_U5 (hyp : HypF_4_4 .U5 2 2 Gp M₁ M₂)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  by_cases hodd : Odd Gp.index
  · exact burnsideF4m_mem_of_odd hodd hTb hx.1
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U5) hyp.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamU5 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_U5 hyp.model
  obtain ⟨T, S, g, z, t, V, hO | hO⟩ := Un.f431UnOutLieProp_five ↥Gp hmodel
    (burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).toLieAmalgamExt (burnsideF4m_not_odd hyp hTD hodd)
  · exact burnsideF4m_ctr_le_of_lieExt hyp hTD hO.sylow hO.T_le hO.T_le' hO.center_T hTb hx
  · exact burnsideF4m_ctr_le_of_lieExt hyp hTD hO.sylow hO.T_le' hO.T_le hO.center_T hTb hx

end Bridge

end CFSG.ASVolI

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section F433

set_option linter.unusedSectionVars false


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_ZT_inv_mem_Z1 (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hL3 : κ ≠ .L3)
    (hSp : κ ≠ .Sp4) (hG2d : κ ≠ .G2d) {z : E} (hz : z ∈ ctr (oPPrime 2 (Gp ⊓ M₁)))
    (hz1 : z ≠ 1) {T : Subgroup E} (hT : IsSylowTwoOf T (M₁ ⊓ M₂))
    (hZG : ∀ x ∈ ctr T, x * x = 1 → x ∈ Gp) {x : E} (hx : x ∈ ctr T) (hx1 : x ≠ 1)
    (hx2 : x * x = 1) : x ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) := by
  have hSle := burnsideF4j_S_le_sylow hyp hT
  have hxS : x ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
    rw [← burnsideF4j_sylow_inf_Gp hyp hT]
    exact ⟨hx.1, hZG x hx hx2⟩
  exact burnsideF4j_ZS_inv_mem_Z1 hyp hL3 hSp hG2d hz hz1
    (show x ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) from
      ⟨hxS, Subgroup.mem_centralizer_iff.2 fun s hs =>
        (Subgroup.mem_centralizer_iff.1 hx.2) s (hSle hs)⟩) hx1 hx2

theorem burnsideF4m_F_4_33_main {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hL3 : κ ≠ .L3) (hSp : κ ≠ .Sp4)
    (hZG : ∀ Tb : Subgroup E, IsSylowTwoOf Tb (M₁ ⊓ M₂) → ∀ x ∈ ctr Tb, x * x = 1 → x ∈ Gp)
    {T : Subgroup M} (hT : ChF.IsSylowOf 2 T (MiOne β ε ⊓ MiTwo β ε)) : ChF.IsSylowOf 2 T ⊤ := by
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  set b := burnsideF4d_bOne β ε with hbdef
  have hb : Function.Injective b := burnsideF4j_bOne_injective hyp
  have hinter : MiOne β ε ⊓ MiTwo β ε = subImg b (M₁ ⊓ M₂) :=
    burnsideF4d_inter_eq β hyp.faithful ε hyp.inj
  have hT' : IsSylowTwoOf T (subImg b (M₁ ⊓ M₂)) := hinter ▸ hT
  obtain ⟨Tb, hTbY, hTbN, hTbeq⟩ := burnsideF4j_exists_preimage b hb hT'.1
  have hTbsyl : IsSylowTwoOf Tb (M₁ ⊓ M₂) :=
    (burnsideF4j_isSylow_subImg_iff b hb hTbN inf_le_left).1 (hTbeq ▸ hT')
  have hTb1 : IsSylowTwoOf Tb M₁ := burnsideF4j_sylow_M1 hyp.amalgam hTbsyl
  have hT1 : IsSylowTwoOf T (MiOne β ε) := by
    rw [← hTbeq, burnsideF4d_MiOne_eq]
    exact (burnsideF4j_isSylow_subImg_iff b hb hTbN le_rfl).2 hTb1
  have hZ := burnsideF4j_Z1_eq hyp
  have hz := hyp.z_mem.1 hL3
  have hz' := hz
  rw [hZ] at hz'
  obtain ⟨zb, hzbN, hzb, hzbe⟩ := mem_subImg.mp hz'
  have hzb1 : zb ≠ 1 := by
    rintro rfl
    exact hyp.z_inv.1 (by rw [← hzbe]; exact map_one b)
  have hTne : T ≠ ⊥ := by
    intro hbot
    have hzM : z ∈ MiOne β ε := hyp.hb (Subgroup.mem_centralizer_singleton_iff.2 rfl)
    have h2 : orderOf (⟨z, hzM⟩ : ↥(MiOne β ε)) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [pow_two]; exact hyp.z_inv.2) hyp.z_inv.1
    have hdvd : 2 ∣ Nat.card ↥(MiOne β ε) := h2 ▸ orderOf_dvd_natCard _
    apply hT1.2.2
    rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
    exact hdvd
  have hZT : ∀ w ∈ burnsideF4j_omegaCtr T, w ≠ 1 →
      Subgroup.centralizer ({w} : Set M) ≤ MiOne β ε := by
    intro w hw hw1
    obtain ⟨hwT, hw2⟩ := burnsideF4j_mem_omegaCtr.1 hw
    rw [← hTbeq, burnsideF4j_ctr_subImg b hb hTbN] at hwT
    obtain ⟨wb, hwbN, hwb, rfl⟩ := mem_subImg.mp hwT
    have hwb1 : wb ≠ 1 := by
      rintro rfl
      exact hw1 (map_one b)
    have hwb2 : wb * wb = 1 := by
      have : (⟨wb, hwbN⟩ : ↥M₁) * ⟨wb, hwbN⟩ = 1 := hb (by rw [map_mul, hw2, map_one])
      exact congrArg Subtype.val this
    have hwZ : wb ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) :=
      burnsideF4m_ZT_inv_mem_Z1 hyp.amalgam hL3 hSp hyp.not_G2d hzb hzb1 hTbsyl
        (hZG Tb hTbsyl) hwb hwb1 hwb2
    have hwZ1 : b ⟨wb, hwbN⟩ ∈ ctr (oPPrime 2 (GiOne Gp β ε)) := by
      rw [hZ]; exact mem_subImg_of_mem b hwbN hwZ
    exact burnsideF4j_centralizer_Z1_le hyp hL3 hwZ1 hw1
  have hmax := CFSG.Quasithin.H13.F431.L3.maximal_two_of_char (H := ⊤) hT1
    (fun x hx => (burnsideF4j_mem_omegaCtr.1 hx).1.1)
    (burnsideF4j_exists_omegaCtr hT.2.1 hTne)
    (fun n _ hn x hx => by
      obtain ⟨hxT, hx2⟩ := burnsideF4j_mem_omegaCtr.1 hx
      refine burnsideF4j_mem_omegaCtr.2 ⟨burnsideF4j_conj_mem_ctr hn hxT, ?_⟩
      calc n * x * n⁻¹ * (n * x * n⁻¹) = n * (x * x) * n⁻¹ := by group
        _ = 1 := by rw [hx2]; group)
    (fun w hw hw1 y _ hy => hZT w hw hw1 (Subgroup.mem_centralizer_singleton_iff.2 hy))
  exact CFSG.Quasithin.H13.F431.L3.isSylowTwoOf_of_max le_top hT.2.1 hmax

@[expose] def burnsideF4m_CtrInputRest : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 κ 2 f Gp M₁ M₂ →
    ((κ = .G2 ∧ f = 1) ∨ (κ = .U4 ∧ f = 1) ∨ (κ = .U5 ∧ f ≠ 2) ∨ (κ = .F4tw ∧ f = 1)) →
    ∀ T : Subgroup E, IsSylowTwoOf T (M₁ ⊓ M₂) → ∀ x ∈ ctr T, x * x = 1 → x ∈ Gp

theorem burnsideF4m_F_4_33_of (hin : burnsideF4m_CtrInputRest) : F_4_33 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp T hT
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  have hodd_of : Odd Gp.index → ChF.IsSylowOf 2 T ⊤ := fun hodd =>
    burnsideF4j_F_4_33_odd hyp hodd hT
  have hf1 : 1 ≤ f := by
    have hm := hyp.amalgam.model
    cases κ <;> first
      | exact hm.2.1
      | (obtain ⟨-, hfo, -⟩ := hm; exact hfo.pos)
      | (obtain ⟨-, hf, -⟩ := hm; omega)
  cases κ
  · exact burnsideF4d_Z6_F_4_33_L3 hyp hT
  · exact burnsideF4j_F_4_33_Sp4 hyp hT
  · refine burnsideF4m_F_4_33_main hyp (by decide) (by decide) (fun Tb hTb x hx hx2 => ?_) hT
    by_cases hf2 : 2 ≤ f
    · exact burnsideF4m_ctr_le_G2 hyp.amalgam hf2 hTb hx
    · exact hin _ f E Gp M₁ M₂ hyp.amalgam (Or.inl ⟨rfl, by omega⟩) Tb hTb x hx hx2
  · exact burnsideF4m_F_4_33_main hyp (by decide) (by decide)
      (fun Tb hTb x hx _ => burnsideF4m_ctr_le_D4tw hyp.amalgam hTb hx) hT
  · by_cases hf3 : 3 ≤ f
    · exact hodd_of (burnsideF4j_odd_index_F4tw hyp.amalgam hf3)
    · have hf1' : f = 1 := by
        obtain ⟨-, -, h1 | h3⟩ := hyp.amalgam.model
        · exact h1.1
        · exact absurd h3.1 hf3
      exact burnsideF4m_F_4_33_main hyp (by decide) (by decide)
        (fun Tb hTb x hx hx2 => hin _ f E Gp M₁ M₂ hyp.amalgam
          (Or.inr (Or.inr (Or.inr ⟨rfl, hf1'⟩))) Tb hTb x hx hx2) hT
  · refine burnsideF4m_F_4_33_main hyp (by decide) (by decide) (fun Tb hTb x hx hx2 => ?_) hT
    by_cases hf2 : 2 ≤ f
    · exact burnsideF4m_ctr_le_U4 hyp.amalgam hf2 hTb hx
    · exact hin _ f E Gp M₁ M₂ hyp.amalgam (Or.inr (Or.inl ⟨rfl, by omega⟩)) Tb hTb x hx hx2
  · refine burnsideF4m_F_4_33_main hyp (by decide) (by decide) (fun Tb hTb x hx hx2 => ?_) hT
    by_cases hf2 : f = 2
    · subst hf2
      exact burnsideF4m_ctr_le_U5 hyp.amalgam hTb hx
    · exact hin _ f E Gp M₁ M₂ hyp.amalgam (Or.inr (Or.inr (Or.inl ⟨rfl, hf2⟩))) Tb hTb x hx hx2
  · exact absurd rfl hyp.not_G2d
  · exact hodd_of (burnsideF4j_odd_index_Tits hyp.amalgam)

end F433

end CFSG.ASVolI
