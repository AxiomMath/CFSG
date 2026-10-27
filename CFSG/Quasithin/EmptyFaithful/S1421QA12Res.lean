module

public import CFSG.Quasithin.EmptyFaithful.S1421QA12Aut
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Borel
public import CFSG.Quasithin.EmptyFaithful.SBc16GAct
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223BlkEpi
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.EmptyFaithful.S1421Q9F

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace QA12

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem cComp_mcOf_of_inputs
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h128Four : Lemma128Four)
    (hL34 : Q9.L34Maximal) (st : Setting1427 T M H K1) (hK : oTwoUpper H ∈ cComp H)
    (hs3 : ShapeL3Sp4 T K1 (oTwoUpper H)) :
    oTwoUpper H ∈ cComp (mcOf T) ∧ mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have hmax := Q9.isMaximalLocal_oTwoUpper h128Four hL34 st hK hs3
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKT : oTwoUpper H ⊔ T = H := S1421.sup_oTwoUpper_eq st
  have hTN := T_le_normalizer_K st
  have hBl : oTwoUpper H ∈ lFamily T := by
    show oTwoUpper H ∈ cComp (oTwoUpper H ⊔ T)
    rw [hKT]
    exact hK
  obtain ⟨Kc, hKc, hKKc⟩ := Q9.exists_cComp_mcOf h37 h39 st hBl (hKH.trans (Q9.H_le_mcOf st))
  have hKcK : Kc = oTwoUpper H := hmax.2 Kc (Q9.isLocal_of_cComp_mcOf st hKc) hKKc
  have hnorm := lemma_1_2_4_normal st.hyp.qtke st.hyp.simple st.hyp.nonabelian h37 h38
    (Q9.pCoreOf_mcOf_ne_bot st) (Q9.isSylowTwoOf_mcOf st) hBl hKKc hKc hTN
  rw [hKcK] at hnorm
  exact ⟨hKcK ▸ hKc, (Subgroup.normal_subgroupOf_iff_le_normalizer
    (hKH.trans (Q9.H_le_mcOf st))).mp hnorm⟩

theorem noTwoQuotient_of_perfect {B : Subgroup G} (hperf : ⁅B, B⁆ = B) :
    ∀ (N : Subgroup ↥B) [N.Normal], IsPGroup 2 (↥B ⧸ N) → N = ⊤ := by
  intro N _ hN
  by_contra hNtop
  have : Nontrivial (↥B ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
  have hP : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hperf
  have : Group.IsPerfect (↥B ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective _)
  have : Group.IsNilpotent (↥B ⧸ N) := hN.isNilpotent
  exact Group.IsPerfect.not_isSolvable (↥B ⧸ N) inferInstance

omit [Finite G] in
@[expose] noncomputable def rhoOf (K N : Subgroup G) (hKN : N ≤ Subgroup.normalizer (K : Set G)) :
    ↥N →* MulAut (OTwoQuot K) :=
  (SBc16.actHom K).comp (Subgroup.inclusion hKN)

omit [Finite G] in
theorem rhoOf_eq_one_iff (K N : Subgroup G) (hKN : N ≤ Subgroup.normalizer (K : Set G))
    (g : ↥N) : rhoOf K N hKN g = 1 ↔
      ∀ k ∈ K, (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
  SBc16.actHom_eq_one_iff K (hKN g.2)

omit [Finite G] in
theorem rhoOf_of_mem (K N : Subgroup G) (hKN : N ≤ Subgroup.normalizer (K : Set G))
    (hKN' : K ≤ N) {k : G} (hk : k ∈ K) :
    rhoOf K N hKN ⟨k, hKN' hk⟩ = MulAut.conj (QuotientGroup.mk ⟨k, hk⟩ : OTwoQuot K) := by
  apply MulEquiv.ext
  intro v
  induction v using QuotientGroup.induction_on with | H x => ?_
  obtain ⟨x, hx⟩ := x
  show SBc16.actHom K ⟨k, hKN (hKN' hk)⟩ (QuotientGroup.mk ⟨x, hx⟩) = _
  rw [SBc16.actHom_mk]
  rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

omit [Finite G] in
theorem inv_mul_mul_mem_pCoreOf {K Mc : Subgroup G}
    (hWN : Mc ≤ Subgroup.normalizer (pCoreOf 2 K : Set G)) {a b : G} (ha : a ∈ Mc)
    (hb : b ∈ Mc) (h : a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 K) : (a * b)⁻¹ * (b * a) ∈ pCoreOf 2 K := by
  have h1 : (a * b * a⁻¹ * b⁻¹)⁻¹ ∈ pCoreOf 2 K := (pCoreOf 2 K).inv_mem h
  have h2 := (Subgroup.mem_normalizer_iff.mp
    (hWN (Mc.mul_mem (Mc.inv_mem hb) (Mc.inv_mem ha))) _).mp h1
  have e : (b⁻¹ * a⁻¹) * (a * b * a⁻¹ * b⁻¹)⁻¹ * (b⁻¹ * a⁻¹)⁻¹ = (a * b)⁻¹ * (b * a) := by group
  rw [← e]
  exact h2

theorem eq_one_of_pow_three_of_rho_eq_one {K Mc : Subgroup G}
    (hpsl : IsPSL 3 2 2 (OTwoQuot K)) (hKMc : K ≤ Mc)
    (hKN : Mc ≤ Subgroup.normalizer (K : Set G)) (hMc3 : CFSG.Open.pRank 3 Mc ≤ 2)
    {x : ↥Mc} (hx : rhoOf K Mc hKN x = 1) (hx3 : x ^ 3 = 1) : x = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWN : Mc ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := fun g hg =>
    normalizer_le_normalizer_pCoreOf 2 K (hKN hg)
  set N : Subgroup ↥Mc := (pCoreOf 2 K).subgroupOf Mc with hN
  have hNn : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hWN
  have hN2 : IsPGroup 2 N := IsPGroup.comap_subtype (pCoreOf_isPGroup 2 K)
  have hN3 : ¬ 3 ∣ Nat.card N := by
    obtain ⟨n, hn⟩ := hN2.exists_card_eq
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (↥Mc ⧸ N)) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_quotient_eq N hN3, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hMc3
  have hle : CFSG.Open.pCore 2 ↥K ≤ N.comap (Subgroup.inclusion hKMc) := by
    intro w hw
    rw [Subgroup.mem_comap, hN, Subgroup.mem_subgroupOf]
    exact (SBc16.mem_pCore_iff_coe K w).mp hw
  let ι : OTwoQuot K →* ↥Mc ⧸ N := QuotientGroup.map _ N (Subgroup.inclusion hKMc) hle
  have hι : ∀ k : ↥K, ι (QuotientGroup.mk k) = QuotientGroup.mk (Subgroup.inclusion hKMc k) :=
    fun k => rfl
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro v hv
    induction v using QuotientGroup.induction_on with | H k => ?_
    rw [hι] at hv
    have h1 : Subgroup.inclusion hKMc k ∈ N := (QuotientGroup.eq_one_iff _).mp hv
    have h2 : (k : G) ∈ pCoreOf 2 K := Subgroup.mem_subgroupOf.mp h1
    exact (QuotientGroup.eq_one_iff k).mpr ((SBc16.mem_pCore_iff_coe K k).mpr h2)
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup (OTwoQuot K))
  have hr2 := two_le_pRank_psl34 hpsl
  have hL : 2 ≤ CFSG.Open.pRank 3 (E.map ι) := by
    have h1 : CFSG.Open.IsElemAbelian 3 (E.map ι) := CFSG.SectionRank.isElemAbelian_map hE ι
    have h2 : Nat.card (E.map ι) = 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot K)) := by
      rw [Subgroup.card_map_of_injective hιinj]
      exact hEcard
    exact hr2.trans (CFSG.SectionRank.le_pRank (by norm_num) le_rfl h1 h2)
  have hc : ∀ l ∈ E.map ι, (QuotientGroup.mk x : ↥Mc ⧸ N) * l = l * QuotientGroup.mk x := by
    intro l hl
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hl
    induction e using QuotientGroup.induction_on with | H k => ?_
    rw [hι, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hxk := (rhoOf_eq_one_iff K Mc hKN x).mp hx (k : G) k.2
    exact inv_mul_mul_mem_pCoreOf hWN x.2 (hKMc k.2) hxk
  have hcx : (QuotientGroup.mk x : ↥Mc ⧸ N) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hx3]
    rfl
  have hmem := A318.le_of_centralizes_of_pow_eq_one (p := 3) hL hrank hc hcx
  obtain ⟨e, -, he⟩ := Subgroup.mem_map.mp hmem
  induction e using QuotientGroup.induction_on with | H k => ?_
  rw [hι] at he
  have h1 : (Subgroup.inclusion hKMc k)⁻¹ * x ∈ N := QuotientGroup.eq.mp he
  have h2 : (k : G)⁻¹ * (x : G) ∈ pCoreOf 2 K := Subgroup.mem_subgroupOf.mp h1
  have hxK : (x : G) ∈ K := by
    have : (k : G) * ((k : G)⁻¹ * (x : G)) ∈ K := K.mul_mem k.2 (pCoreOf_le 2 K h2)
    simpa using this
  have hx' : rhoOf K Mc hKN ⟨(x : G), hKMc hxK⟩ = 1 := hx
  rw [rhoOf_of_mem K Mc hKN hKMc hxK] at hx'
  have hz : (QuotientGroup.mk ⟨(x : G), hxK⟩ : OTwoQuot K) ∈ Subgroup.center (OTwoQuot K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h3 := congrArg (fun a : MulAut (OTwoQuot K) => a y) hx'
    simp only [MulAut.conj_apply, MulAut.one_apply] at h3
    calc y * QuotientGroup.mk ⟨(x : G), hxK⟩
        = (QuotientGroup.mk ⟨(x : G), hxK⟩ * y * (QuotientGroup.mk ⟨(x : G), hxK⟩)⁻¹) *
          QuotientGroup.mk ⟨(x : G), hxK⟩ := by rw [h3]
      _ = QuotientGroup.mk ⟨(x : G), hxK⟩ * y := by group
  rw [H13.A5.center_eq_bot_of_isPSL34 hpsl, Subgroup.mem_bot] at hz
  have hxW : (x : G) ∈ pCoreOf 2 K := (mk_eq_one_iff_mem_pCoreOf ⟨(x : G), hxK⟩).mp hz
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 K) ⟨(x : G), hxW⟩
  have hxm : (x : G) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hx3' : (x : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
  have hord : orderOf (x : G) = 1 :=
    Nat.eq_one_of_dvd_coprimes (a := 2 ^ m) (b := 3) (Nat.Coprime.pow_left m (by norm_num))
      (orderOf_dvd_of_pow_eq_one hxm) (orderOf_dvd_of_pow_eq_one hx3')
  exact Subtype.ext (orderOf_eq_one_iff.mp hord)

omit [Finite G] in
theorem pow_card_ker_eq_one {Γ Δ : Type} [Group Γ] [Group Δ] [Finite Γ] (ρ : Γ →* Δ) {c : Γ}
    (hc : ρ c = 1) : c ^ Nat.card ρ.ker = 1 := by
  have h3 : (⟨c, MonoidHom.mem_ker.mpr hc⟩ : ↥ρ.ker) ^ Nat.card ρ.ker = 1 := pow_card_eq_one'
  exact congrArg Subtype.val h3

theorem not_three_dvd_card_ker {K Mc : Subgroup G} (hpsl : IsPSL 3 2 2 (OTwoQuot K))
    (hKMc : K ≤ Mc) (hKN : Mc ≤ Subgroup.normalizer (K : Set G))
    (hMc3 : CFSG.Open.pRank 3 Mc ≤ 2) : ¬ 3 ∣ Nat.card (rhoOf K Mc hKN).ker := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(rhoOf K Mc hKN).ker) 3 h3
  have hc3 : (c : ↥Mc) ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one c
    rw [hc] at h1
    exact congrArg Subtype.val h1
  have h1 : (c : ↥Mc) = 1 :=
    eq_one_of_pow_three_of_rho_eq_one hpsl hKMc hKN hMc3 (MonoidHom.mem_ker.mp c.2) hc3
  have h2 : c = 1 := Subtype.ext h1
  rw [h2, orderOf_one] at hc
  omega

theorem mem_of_mem_perfectCore_of_orderOf_eq_pow_three {K Mc : Subgroup G}
    (hpsl : IsPSL 3 2 2 (OTwoQuot K)) (hKMc : K ≤ Mc)
    (hKN : Mc ≤ Subgroup.normalizer (K : Set G)) (hMc3 : CFSG.Open.pRank 3 Mc ≤ 2) {x : G}
    (hx : x ∈ perfectCore Mc) {a : ℕ} (hxa : orderOf x = 3 ^ a) : x ∈ K := by
  have hxMc : x ∈ Mc := perfectCore_le Mc hx
  set R₁ : Subgroup ↥Mc := (perfectCore Mc).subgroupOf Mc with hR₁
  have hR₁perf : ⁅R₁, R₁⁆ = R₁ := by
    apply Subgroup.map_injective Mc.subtype_injective
    rw [Subgroup.map_commutator, hR₁, Subgroup.map_subgroupOf_eq_of_le (perfectCore_le Mc)]
    exact perfectCore_perfect Mc
  have hPperf : ⁅R₁.map (rhoOf K Mc hKN), R₁.map (rhoOf K Mc hKN)⁆ = R₁.map (rhoOf K Mc hKN) := by
    rw [← Subgroup.map_commutator, hR₁perf]
  have hinn := perfect_subgroup_le_inn hpsl hPperf
  obtain ⟨z, hz⟩ := hinn (Subgroup.mem_map_of_mem (rhoOf K Mc hKN)
    (show (⟨x, hxMc⟩ : ↥Mc) ∈ R₁ from Subgroup.mem_subgroupOf.mpr hx))
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective z
  have hρk := rhoOf_of_mem K Mc hKN hKMc hk
  have hc : rhoOf K Mc hKN ((⟨k, hKMc hk⟩ : ↥Mc)⁻¹ * ⟨x, hxMc⟩) = 1 := by
    rw [map_mul, map_inv, hρk]
    have hz' : (MulAut.conj (QuotientGroup.mk ⟨k, hk⟩ : OTwoQuot K)) =
        rhoOf K Mc hKN ⟨x, hxMc⟩ := hz
    rw [hz', inv_mul_cancel]
  have hNK : (K.subgroupOf Mc).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKMc).mpr hKN
  have hker3 := not_three_dvd_card_ker hpsl hKMc hKN hMc3
  have hκ : (QuotientGroup.mk (⟨k, hKMc hk⟩ : ↥Mc) : ↥Mc ⧸ K.subgroupOf Mc) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hk)
  have hmk : (QuotientGroup.mk (⟨x, hxMc⟩ : ↥Mc) : ↥Mc ⧸ K.subgroupOf Mc) =
      QuotientGroup.mk ((⟨k, hKMc hk⟩ : ↥Mc)⁻¹ * ⟨x, hxMc⟩) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hκ, inv_one, one_mul]
  have h1 : (QuotientGroup.mk (⟨x, hxMc⟩ : ↥Mc) : ↥Mc ⧸ K.subgroupOf Mc) ^ 3 ^ a = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hxMc⟩ : ↥Mc) ^ 3 ^ a = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one x
      rw [hxa] at this
      simpa using this
    rw [this]
    rfl
  have h2 : (QuotientGroup.mk (⟨x, hxMc⟩ : ↥Mc) : ↥Mc ⧸ K.subgroupOf Mc) ^
      Nat.card (rhoOf K Mc hKN).ker = 1 := by
    rw [hmk, ← QuotientGroup.mk_pow]
    have h4 : ((⟨k, hKMc hk⟩ : ↥Mc)⁻¹ * ⟨x, hxMc⟩) ^ Nat.card (rhoOf K Mc hKN).ker = 1 :=
      pow_card_ker_eq_one _ hc
    rw [h4]
    rfl
  have hcop : Nat.Coprime (3 ^ a) (Nat.card (rhoOf K Mc hKN).ker) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker3)
  have hord : orderOf (QuotientGroup.mk (⟨x, hxMc⟩ : ↥Mc) : ↥Mc ⧸ K.subgroupOf Mc) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  have h5 := (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hord)
  exact Subgroup.mem_subgroupOf.mp h5

theorem eq_residual_of_psl34 {K Mc : Subgroup G} (hpsl : IsPSL 3 2 2 (OTwoQuot K))
    (hKc : K ∈ cComp Mc) (hKN : Mc ≤ Subgroup.normalizer (K : Set G))
    (hMc3 : CFSG.Open.pRank 3 Mc ≤ 2) : K = oPrimeResidualOf 3 (perfectCore Mc) := by
  have hKMc : K ≤ Mc := le_of_mem_cComp hKc
  have hKperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  have hKR : K ≤ perfectCore Mc := le_perfectCore_of_perfect hKMc hKperf
  have : IsSimpleGroup (OTwoQuot K) := H13.A5.isSimpleGroup_of_isPSL34 hpsl
  have h3 : 3 ∣ Nat.card (OTwoQuot K) := by
    rw [H13.A5.card_of_isPSL34 hpsl]
    norm_num
  have hKres : K = oPrimeResidualOf 3 K :=
    S15223.eq_oPrimeResidualOf_of_epi_simple (noTwoQuotient_of_perfect hKperf)
      (α := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']) h3
  refine le_antisymm ?_ ?_
  · calc K = oPrimeResidualOf 3 K := hKres
      _ ≤ oPrimeResidualOf 3 (perfectCore Mc) :=
        Subgroup.closure_mono fun x hx => ⟨hKR hx.1, hx.2⟩
  · refine (Subgroup.closure_le K).mpr ?_
    rintro x ⟨hx, a, hxa⟩
    exact mem_of_mem_perfectCore_of_orderOf_eq_pow_three hpsl hKMc hKN hMc3 hx hxa

end QA12

end CFSG.Quasithin
