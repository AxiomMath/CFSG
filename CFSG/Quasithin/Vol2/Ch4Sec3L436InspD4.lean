module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspL3
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspD4Aut
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspNat
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspDefs

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4 CFSG.Quasithin.H13.NQCat L3M
  CFSG.QuasithinUnique.Setup.X7a
open CFSG.Quasithin (perfectCore map_perfectCore le_perfectCore_of_perfect centerOf)

theorem D4A.centerOf_le_centerOf_Q0
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {R : Subgroup (ModGL TwistTag.D4.tag K)}
    (hRQ : R ≤ Q0 σ)
    (hRN : perfectCore (P0 σ) ≤ Subgroup.normalizer (R : Set (ModGL TwistTag.D4.tag K))) :
    centerOf R ≤ centerOf (Q0 σ) := by
  have : CharP K 2 := CFSG.Quasithin.B42D4.charP_two_of_card hf hK
  have hσ3 := CFSG.Quasithin.B42D4.sigma_cube hK σ hσ
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2) 3
  obtain ⟨-, hPN, -, -⟩ := library_facts σ fa0 singleton_ne_univ_fa0
  have hZQ : centerOf (Q0 σ) ≤ Q0 σ := inf_le_left
  have hRZ : centerOf R ≤ Q0 σ := inf_le_left.trans hRQ
  have hWN : perfectCore (P0 σ) ≤
      Subgroup.normalizer ((centerOf R ⊔ centerOf (Q0 σ) : Subgroup (ModGL TwistTag.D4.tag K)) :
        Set (ModGL TwistTag.D4.tag K)) := by
    intro g hg
    have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (G2Rad.mem_normalizer_centerOf (hRN hg))
    have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (G2Rad.mem_normalizer_centerOf (hPN (CFSG.Quasithin.perfectCore_le _ hg)))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, h1, h2]
  rcases D4Irred.eq_or_eq_of_le_normalizer σ hσ3 hK4
      (CFSG.Quasithin.B42D4.exists_sigma_ne hf hK σ hσ)
      (CFSG.Quasithin.B42D4.exists_spanning hf hK σ hσ) le_sup_right (sup_le hRZ hZQ) hWN with
    h | h
  · exact h ▸ le_sup_left
  · exfalso
    have hA : centerOf R ⊔ centerOf (Q0 σ) ≤
        Subgroup.centralizer (centerOf R : Set (ModGL TwistTag.D4.tag K)) := by
      refine sup_le (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
        (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
      · exact (Subgroup.mem_centralizer_iff.1 hy.2 x hx.1).symm
      · exact Subgroup.mem_centralizer_iff.1 hx.2 y (hRZ hy)
    have hB : centerOf R ⊔ centerOf (Q0 σ) ≤
        Subgroup.centralizer (centerOf (Q0 σ) : Set (ModGL TwistTag.D4.tag K)) := by
      refine sup_le (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
        (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
      · exact (Subgroup.mem_centralizer_iff.1 hy.2 x (hRZ hx)).symm
      · exact (Subgroup.mem_centralizer_iff.1 hy.2 x hx.1).symm
    have hC : centerOf R ⊔ centerOf (Q0 σ) ≤ Subgroup.centralizer
        ((centerOf R ⊔ centerOf (Q0 σ) : Subgroup (ModGL TwistTag.D4.tag K)) :
          Set (ModGL TwistTag.D4.tag K)) :=
      sup_le (Subgroup.le_centralizer_iff.1 hA) (Subgroup.le_centralizer_iff.1 hB)
    obtain ⟨x, hx, y, hy, hxy⟩ := nonabelian_a0 σ hσ3
    rw [← h] at hx hy
    exact hxy (Subgroup.mem_centralizer_iff.1 (hC hy) x hx)

theorem insp436D4_holds :
    Insp436D4 := by
  intro G _ _ K P V R₀ n hn hKq hD4 hP hPSL hnat hV hR₀2 hR₀N hR₀P hNP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₀ : Subgroup ↥K := P.comap K.subtype with hP₀
  have hPK : P ≤ K := hP.1.1
  have hP₀K : P₀.map K.subtype = P := by
    rw [hP₀, Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])]
  have hP₀max : IsMaxParabolic2 (⊤ : Subgroup ↥K) P₀ :=
    L436.isMaxParabolic2_comap K.subtype K.subtype_injective K.range_subtype.symm hP
  obtain ⟨S₁, hS₁, hNS₁, hPcov⟩ :=
    CFSG.Quasithin.Lie2Parabolic.exists_sylow_of_isMaxParabolic2 hP₀max
  obtain ⟨hn1, L, _, _, σ, hL, hσ, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model hD4
  have : CharP L 2 := CFSG.Quasithin.B42D4.charP_two_of_card hn1 hL
  have hσ3 := CFSG.Quasithin.B42D4.sigma_cube hL σ hσ
  have : Finite (ModGL TwistTag.D4.tag L) := finite_modGL
  have hL4 : 4 ≤ Nat.card L := by
    rw [hL]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2) 3
  set C := graphFixedRootGroup TwistTag.D4 L σ.toRingHom with hC
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 L 2 σ w₀ hw₀).1
  have hres := CFSG.QuasithinUnique.Setup.X6.triality_residualOvergroupsAt (K := L) σ
  set q : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hT := isSylowTwoOf_map_top hS₁ (f := e.toMonoidHom.comp q) (e.surjective.comp hqs)
  have hidx : ¬ 2 ∣ (S₁.map (e.toMonoidHom.comp q)).index := by
    have := hT.2.2
    rwa [← Subgroup.relIndex_top_right]
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C (hT.2.1.toSylow hidx) PU
  set θ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥C := e.trans (MulAut.conj c) with hθ
  set Φ : ↥K →* ↥C := θ.toMonoidHom.comp q with hΦ
  have hΦs : Function.Surjective Φ := θ.surjective.comp hqs
  have hΦker : ∀ x, Φ x = 1 → x ∈ Subgroup.center ↥K := by
    intro x hx
    have h1 : q x = 1 := θ.injective (by rw [map_one]; exact hx)
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hker : Φ.ker ≤ P₀ := fun x hx =>
    ((Subgroup.center_le_normalizer _).trans hNS₁) (hΦker x hx)
  have hSU : S₁.map Φ = (graphFixedPosUnipotent TwistTag.D4 L σ.toRingHom).subgroupOf C := by
    have h1 : ((c • hT.2.1.toSylow hidx : Sylow 2 ↥C) : Subgroup ↥C) =
        (graphFixedPosUnipotent TwistTag.D4 L σ.toRingHom).subgroupOf C := by
      rw [hc]
      exact hPU
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    rw [← h1]
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨e (q y), Subgroup.mem_map_of_mem _ hy, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hcov : P₀.map Φ ⋖ ⊤ := by
    rw [← Subgroup.map_top_of_surjective Φ hΦs]
    exact covBy_map_of_ker_le hΦs hker hPcov
  have hUM : (graphFixedPosUnipotent TwistTag.D4 L σ.toRingHom).subgroupOf C ≤ P₀.map Φ :=
    hSU ▸ Subgroup.map_mono (Subgroup.le_normalizer.trans hNS₁)
  obtain ⟨j, hj⟩ := (hres.2.2.1 _ hUM).mp hcov
  have hPcore : (perfectCore P₀).map K.subtype = perfectCore P := by rw [map_perfectCore, hP₀K]
  have hmemP₀ : ∀ a : ↥K, (a : G) ∈ perfectCore P → a ∈ perfectCore P₀ := by
    intro a ha
    rw [← hPcore] at ha
    obtain ⟨b, hb, hba⟩ := ha
    rwa [Subtype.ext hba] at hb
  have hP₀le : ∀ a ∈ perfectCore P₀, (a : G) ∈ perfectCore P := fun a ha =>
    hPcore ▸ Subgroup.mem_map_of_mem _ ha
  have hcoreJ : ((perfectCore P₀).map Φ).map C.subtype =
      perfectCore (graphFixedParabolic TwistTag.D4 L σ.toRingHom
        {CFSG.QuasithinUnique.Setup.X6.d4Index j}) := by
    rw [map_perfectCore Φ P₀, hj, CFSG.QuasithinUnique.Vol2Native.A312L.perfectCore_map_subgroupOf
      (graphFixedParabolic_le _ _ _ _)]
  have hcases : ∀ a : Fin TwistTag.D4.foldedTag.rank, a = fa0 ∨ a = fa1 := by decide
  rcases hcases (CFSG.QuasithinUnique.Setup.X6.d4Index j) with hj0 | hj1
  ·
    exfalso
    have hcore0 : ((perfectCore P₀).map Φ).map C.subtype = perfectCore (P0 σ) := by
      rw [hj0] at hcoreJ
      exact hcoreJ
    obtain ⟨F, _, _, hF, hnat'⟩ := hnat
    set Ψ : ↥K →* ModGL TwistTag.D4.tag L := C.subtype.comp Φ with hΨ
    have hP0 : (perfectCore P₀).map Ψ = perfectCore (P0 σ) := by
      rw [hΨ, ← Subgroup.map_map]
      exact hcore0
    set O : Subgroup ↥K := (CFSG.Open.pCoreOf 2 (perfectCore P)).comap K.subtype with hO
    set Vk : Subgroup ↥K := V.comap K.subtype with hVk
    have hOle : CFSG.Open.pCoreOf 2 (perfectCore P) ≤ perfectCore P :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hOP : O ≤ perfectCore P₀ := fun a ha => hmemP₀ a (hOle ha)
    have hON : perfectCore P₀ ≤ Subgroup.normalizer (O : Set ↥K) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [hO, Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hP₀le a ha)) x
    have hO2 : IsPGroup 2 ↥O :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (perfectCore P)).comap_of_injective K.subtype
        K.subtype_injective
    have hRN : perfectCore (P0 σ) ≤ Subgroup.normalizer
        ((O.map Ψ : Subgroup (ModGL TwistTag.D4.tag L)) : Set (ModGL TwistTag.D4.tag L)) := by
      rw [← hP0]
      exact (Subgroup.map_mono hON).trans (Subgroup.le_normalizer_map Ψ)
    have hpc : CFSG.Open.pCoreOf 2 (perfectCore (P0 σ)) ≤ Q0 σ := by
      by_cases h0 : CFSG.Open.pCoreOf 2 (perfectCore (P0 σ)) = ⊥
      · rw [h0]
        exact bot_le
      · exact (D4Irred.pCoreOf_eq_of_parabolicFacts (parabolicFacts_a0 σ hσ3 hL4) h0).le
    have hRQ : O.map Ψ ≤ Q0 σ := by
      refine le_trans ?_ hpc
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ hRN (hO2.map Ψ)
      rw [← hP0]
      exact Subgroup.map_mono hOP
    have hZ0 := D4A.centerOf_le_centerOf_Q0 hn1 hL σ hσ hRQ hRN
    have hW : Vk.map Ψ ≤ centerOf (O.map Ψ) := by
      rintro _ ⟨v, hv, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem _ (hV hv).1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨o, ho, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      have h1 := Subgroup.mem_centralizer_iff.mp (hV hv).2 _ ho
      exact Subtype.ext (by simpa using h1)
    have hcent := D4Irred.perfectCore_le_centralizer σ hσ3
    have hVK : V ≤ K := fun v hv => hPK ((CFSG.Quasithin.perfectCore_le P) (hOle (hV hv).1))
    have hAK : perfectCore P ≤ K := (CFSG.Quasithin.perfectCore_le P).trans hPK
    refine G2A.false_of_natural_comm_inf hnat' (Z := (Subgroup.center ↥K).map K.subtype) ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      show (z : G) ∈ K ⊓ Subgroup.centralizer (K : Set G)
      refine Subgroup.mem_inf.mpr ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
    · intro a ha v hv
      set a' : ↥K := ⟨a, hAK ha⟩
      set v' : ↥K := ⟨v, hVK hv⟩
      have ha' : Ψ a' ∈ perfectCore (P0 σ) := by
        rw [← hP0]
        exact Subgroup.mem_map_of_mem _ (hmemP₀ a' ha)
      have hv' : Ψ v' ∈ centerOf (Q0 σ) :=
        hZ0 (hW (Subgroup.mem_map_of_mem _ (show v' ∈ Vk from hv)))
      have hcomm : Ψ v' * Ψ a' = Ψ a' * Ψ v' :=
        Subgroup.mem_centralizer_iff.mp (hcent ha') _ hv'
      have h1 : Ψ (a' * v' * a'⁻¹ * v'⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [← hcomm]
        group
      have h2 : Φ (a' * v' * a'⁻¹ * v'⁻¹) = 1 := Subtype.ext h1
      exact ⟨_, hΦker _ h2, rfl⟩
  ·
    have hcore1 : ((perfectCore P₀).map Φ).map C.subtype = perfectCore (P1 σ) := by
      rw [hj1] at hcoreJ
      exact hcoreJ
    intro r hr
    set ψ : MulAut ↥K := conjOn K (hR₀N hr) with hψ
    have hψx : ∀ x : ↥K, ((ψ x : ↥K) : G) = r * x * r⁻¹ := fun x => coe_conjOn K (hR₀N hr) x
    have hfix : ∀ x ∈ perfectCore P₀, ψ x = x := by
      intro x hx
      apply Subtype.ext
      rw [hψx, ← Subgroup.mem_centralizer_iff.mp (hR₀P hr) _ (hP₀le x hx), mul_inv_cancel_right]
    set φ' : MulAut ↥C := θ.symm.trans ((autCenter ψ).trans θ) with hφ'
    have hφ'Φ : ∀ y : ↥K, φ' (Φ y) = Φ (ψ y) := by
      intro y
      simp only [hφ', hΦ, MulEquiv.trans_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply]
      rw [hq, QuotientGroup.mk'_apply, autCenter_mk]
      rfl
    have hfix' : ∀ x : ↥C,
        (x : ModGL TwistTag.D4.tag L) ∈ perfectCore (P1 σ) → φ' x = x := by
      intro x hx
      rw [← hcore1] at hx
      obtain ⟨x', hx', hx'x⟩ := hx
      have hxx : x' = x := Subtype.ext hx'x
      subst hxx
      obtain ⟨y, hy, rfl⟩ := hx'
      rw [hφ'Φ, hfix y hy]
    obtain ⟨m₀, hm₀⟩ := hR₀2 ⟨r, hr⟩
    have hrm : r ^ 2 ^ m₀ = 1 := congrArg Subtype.val hm₀
    have hψpow : ∀ (m : ℕ) (y : ↥K), (((ψ ^ m) y : ↥K) : G) = r ^ m * y * (r ^ m)⁻¹ := by
      intro m y
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ' ψ m, MulAut.mul_apply, hψx, ih]
        group
    have hφ'pow : ∀ (m : ℕ) (y : ↥K), (φ' ^ m) (Φ y) = Φ ((ψ ^ m) y) := by
      intro m y
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [pow_succ' φ' m, pow_succ' ψ m, MulAut.mul_apply, MulAut.mul_apply, ih, hφ'Φ]
    have hφ'2 : φ' ^ 2 ^ m₀ = 1 := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨y, rfl⟩ := hΦs x
      rw [hφ'pow, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [hψpow, hrm, one_mul, inv_one, mul_one]
    have hφ'1 := D4A.aut_eq_one_of_fixes σ hσ3 hn hL hσ φ' hφ'2 hfix'
    have hψ1 : autCenter ψ = 1 := by
      ext y
      have h := congrArg (fun β : MulAut ↥C => β (θ y)) hφ'1
      simp only [hφ', MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h
      rw [MulAut.one_apply]
      exact θ.injective h
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h := congrArg Subtype.val (eq_of_autCenter_eq_one hKq.1 ψ hψ1 ⟨k, hk⟩)
    rw [hψx] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm

end CFSG.Quasithin.H13.Ch4
