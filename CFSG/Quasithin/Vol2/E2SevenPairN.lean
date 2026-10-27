module

public import CFSG.Quasithin.Vol2.E2SevenPairB
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

variable {G : Type} [Group G] [Finite G]

theorem exists_fusionBenderBorel_of_psl_or_sz {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 2 ≤ n) (h : IsPSL 2 2 n X ∨ IsSz n X) : ∃ k, fusionBenderBorel X (2 ^ n) k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with h | h
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    let e' := e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 2 n (by omega) hF)
    have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
      Finite.of_equiv X e'.toEquiv
    exact ⟨1, (bender_psl2_borel_full n hn).map_mulEquiv e'.symm⟩
  · obtain ⟨-, a, ha, F, _, _, rfl, hcard, ⟨e⟩⟩ := h
    let e' : X ≃* ↥(Sz a) := e.trans ((MulEquiv.subgroupCongr
      (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
    have : Finite ↥(Sz a) := Finite.of_equiv X e'.toEquiv
    exact ⟨2, (bender_suzuki_borel_full a ha).map_mulEquiv e'.symm⟩

omit [Finite G] in
theorem card_inf_centralizer_of_fusionBenderBorel {K S : Subgroup G} {q k : ℕ}
    (hB : fusionBenderBorel ↥K q k) (hS : IsSylowTwoOf S K) :
    Nat.card ↥(S ⊓ Subgroup.centralizer (S : Set G)) = q ∧
      ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set G), z ^ 2 = 1 := by
  set Q := toSylow2 hS
  have hQ : (Q : Subgroup ↥K) = S.subgroupOf K := toSylow2_coe hS
  obtain ⟨-, -, hsq, hcard, -⟩ := hB Q
  have hmemQ : ∀ w : ↥K, w ∈ (Q : Subgroup ↥K) → (w : G) ∈ S := fun w hw => by
    rw [hQ] at hw
    exact Subgroup.mem_subgroupOf.mp hw
  have hmemQ' : ∀ w : ↥K, (w : G) ∈ S → w ∈ (Q : Subgroup ↥K) := fun w hw => by
    rw [hQ]
    exact Subgroup.mem_subgroupOf.mpr hw
  have hfwd : ∀ y : ↥(Subgroup.center ↥(Q : Subgroup ↥K)),
      (((y : ↥(Q : Subgroup ↥K)) : ↥K) : G) ∈ S ⊓ Subgroup.centralizer (S : Set G) := by
    intro y
    have hyQ := hmemQ _ (y : ↥(Q : Subgroup ↥K)).2
    refine ⟨hyQ, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hwQ : (⟨w, hS.1 hw⟩ : ↥K) ∈ (Q : Subgroup ↥K) := hmemQ' _ hw
    have := Subgroup.mem_center_iff.mp y.2 ⟨⟨w, hS.1 hw⟩, hwQ⟩
    exact congrArg (fun z : ↥(Q : Subgroup ↥K) => ((z : ↥K) : G)) this
  have hbwd : ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set G),
      ∃ y : ↥(Subgroup.center ↥(Q : Subgroup ↥K)), (((y : ↥(Q : Subgroup ↥K)) : ↥K) : G) = z := by
    rintro z ⟨hzS, hzC⟩
    have hzQ : (⟨z, hS.1 hzS⟩ : ↥K) ∈ (Q : Subgroup ↥K) := hmemQ' _ hzS
    refine ⟨⟨⟨⟨z, hS.1 hzS⟩, hzQ⟩, Subgroup.mem_center_iff.mpr fun w => ?_⟩, rfl⟩
    have hwS : ((w : ↥K) : G) ∈ S := hmemQ _ w.2
    apply Subtype.ext
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hzC) _ hwS
  constructor
  · rw [← hcard]
    refine (Nat.card_congr (Equiv.ofBijective (fun y => (⟨_, hfwd y⟩ :
      ↥(S ⊓ Subgroup.centralizer (S : Set G)))) ⟨fun a b hab => ?_, fun z => ?_⟩)).symm
    · refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
      have := congrArg Subtype.val hab
      simpa using this
    · obtain ⟨y, hy⟩ := hbwd z z.2
      exact ⟨y, Subtype.ext hy⟩
  · intro z hz
    obtain ⟨y, rfl⟩ := hbwd z hz
    have := congrArg (fun w : ↥(Q : Subgroup ↥K) => ((w : ↥K) : G)) (hsq y y.2)
    simpa using this

theorem sylow_eq_of_center_le {X : Type} [Group X] [Finite X] {q k : ℕ} (hq : Even q)
    (hB : fusionBenderBorel X q k) (P Q : Sylow 2 X)
    (hZ : ∀ z ∈ (Q : Subgroup X), (∀ y ∈ (Q : Subgroup X), y * z = z * y) →
      z ∈ (P : Subgroup X)) : P = Q := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X Q P
  by_cases hg : g ∈ Subgroup.normalizer ((Q : Subgroup X) : Set X)
  · exact Sylow.smul_eq_iff_mem_normalizer.mpr hg
  exfalso
  set N := Subgroup.normalizer ((Q : Subgroup X) : Set X) with hN
  obtain ⟨hSE, -, -, hcard, -⟩ := hB Q
  have hg' : g⁻¹ ∉ N := fun h => hg (by simpa using N.inv_mem h)
  have hodd := hSE.2.2 g⁻¹ hg'
  rw [inv_inv] at hodd
  set Z := (Subgroup.center ↥(Q : Subgroup X)).map (Q : Subgroup X).subtype with hZdef
  have hZcard : Nat.card Z = q := by
    rw [hZdef, Subgroup.card_map_of_injective (Q : Subgroup X).subtype_injective, hcard]
  have hZQ : Z ≤ (Q : Subgroup X) := by
    rw [hZdef]
    exact Subgroup.map_subtype_le _
  have hZP : Z ≤ ((g • Q : Sylow 2 X) : Subgroup X) := by
    rintro _ ⟨y, hy, rfl⟩
    refine hZ _ y.2 fun w hw => ?_
    have := Subgroup.mem_center_iff.mp hy ⟨w, hw⟩
    exact congrArg Subtype.val this
  have hgQ : ((g • Q : Sylow 2 X) : Subgroup X) =
      (Q : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hNg : N.map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer (((g • Q : Sylow 2 X) : Subgroup X) : Set X) := by
    rw [hgQ, hN, Subgroup.map_equiv_normalizer_eq]
  have hZN : Z ≤ N ⊓ N.map (MulAut.conj g).toMonoidHom := by
    refine le_inf (hZQ.trans Subgroup.le_normalizer) ?_
    rw [hNg]
    exact hZP.trans Subgroup.le_normalizer
  have hdvd := Subgroup.card_dvd_of_le hZN
  rw [hZcard] at hdvd
  exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat hdvd)) hq

theorem eq_of_inf_centralizer_le {K S S' : Subgroup G} {q k : ℕ} (hq : Even q)
    (hB : fusionBenderBorel ↥K q k) (hS : IsSylowTwoOf S K) (hS' : IsSylowTwoOf S' K)
    (hZ : S' ⊓ Subgroup.centralizer (S' : Set G) ≤ S) : S = S' := by
  have h := sylow_eq_of_center_le hq hB (toSylow2 hS) (toSylow2 hS') fun z hz hzc => by
    rw [toSylow2_coe] at hz ⊢
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    refine hZ ⟨hz, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have := hzc ⟨w, hS'.1 hw⟩ (by rw [toSylow2_coe, Subgroup.mem_subgroupOf]; exact hw)
    exact congrArg Subtype.val this
  have h2 := congrArg (fun P : Sylow 2 ↥K => (P : Subgroup ↥K)) h
  simp only [toSylow2_coe] at h2
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hS.1, inf_of_le_left hS'.1] at h2
  exact h2

omit [Finite G] in
theorem isSylowTwoOf_cjSub {S K : Subgroup G} (hS : IsSylowTwoOf S K) (g : G) :
    IsSylowTwoOf (cjSub g S) (cjSub g K) := by
  refine ⟨cjSub_mono hS.1, hS.2.1.map _, ?_⟩
  have e1 : ((cjSub g S).subgroupOf (cjSub g K)).index = (cjSub g S).relIndex (cjSub g K) := rfl
  rw [e1]
  unfold cjSub
  rw [Subgroup.relIndex_map_map, (MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj g).injective,
    sup_bot_eq, sup_bot_eq]
  exact hS.2.2

omit [Finite G] in
theorem cjSub_inf_centralizer (g : G) (S : Subgroup G) :
    cjSub g (S ⊓ Subgroup.centralizer (S : Set G)) =
      cjSub g S ⊓ Subgroup.centralizer (cjSub g S : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, mem_cjSub, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  refine and_congr_right fun _ => ⟨fun hC y hy => ?_, fun hC y hy => ?_⟩
  · have h1 := hC _ hy
    have h2 : g⁻¹ * (y * x) * g = g⁻¹ * (x * y) * g := by
      calc g⁻¹ * (y * x) * g = g⁻¹ * y * g * (g⁻¹ * x * g) := by group
        _ = g⁻¹ * x * g * (g⁻¹ * y * g) := h1
        _ = g⁻¹ * (x * y) * g := by group
    have h3 := congrArg (fun w => g * w * g⁻¹) h2
    simpa [mul_assoc] using h3
  · have h1 := hC (g * y * g⁻¹) (by simpa [mul_assoc] using hy)
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * x * g * y := by group

theorem card_map_of_forall_eq_one {Q R : Type*} [Group Q] [Group R] (f : Q →* R)
    (B : Subgroup Q) (h : ∀ x ∈ B, f x = 1 → x = 1) : Nat.card ↥(B.map f) = Nat.card ↥B := by
  refine (Nat.card_congr (Equiv.ofBijective (fun b : ↥B =>
    (⟨f b, Subgroup.mem_map_of_mem f b.2⟩ : ↥(B.map f))) ⟨?_, ?_⟩)).symm
  · intro a b hab
    have h1 : f ((a : Q)⁻¹ * b) = 1 := by
      have := congrArg Subtype.val hab
      simp only at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    have h2 := h _ (B.mul_mem (B.inv_mem a.2) b.2) h1
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  · rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem pCore_le_solvableRadical (X : Type) [Group X] [Finite X] :
    CFSG.Open.pCore 2 X ≤ CFSG.solvableRadical X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := X)).isNilpotent
  exact A3.le_solvableRadical inferInstance inferInstance

omit [Finite G] in
theorem le_normalizer_map_subtype {K' : Subgroup G} (N : Subgroup ↥K') [N.Normal] :
    K' ≤ Subgroup.normalizer ((N.map K'.subtype : Subgroup G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨y, hy⟩ * w * ⟨y, hy⟩⁻¹, Subgroup.Normal.conj_mem inferInstance w hw ⟨y, hy⟩, rfl⟩
  · rintro ⟨w, hw, hwz⟩
    have hz : z ∈ K' := by
      have := K'.mul_mem (K'.mul_mem (K'.inv_mem hy) w.2) hy
      rw [show (w : G) = y * z * y⁻¹ from hwz] at this
      simpa [mul_assoc] using this
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    have := Subgroup.Normal.conj_mem inferInstance w hw ⟨y, hy⟩⁻¹
    have e : (⟨y, hy⟩⁻¹ * w * (⟨y, hy⟩⁻¹)⁻¹ : ↥K') = ⟨z, hz⟩ := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [show (w : G) = y * z * y⁻¹ from hwz]
      group)
    rwa [e] at this

theorem eq_one_of_mem_solvableRadical {K' L : Subgroup G} (hLK : L ≤ K') (hs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) {x : ↥K'} (hxL : (x : G) ∈ L)
    (hx : x ∈ CFSG.solvableRadical ↥K') : x = 1 := by
  set R := (CFSG.solvableRadical ↥K').map K'.subtype ⊓ L with hR
  have hsolv1 : Group.IsSolvable ↥((CFSG.solvableRadical ↥K').map K'.subtype) := by
    have : Group.IsSolvable ↥(CFSG.solvableRadical ↥K') := A3.solvableRadical_isSolvable
    exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective _ _
      K'.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hRsolv : Group.IsSolvable ↥R :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (inf_le_left : R ≤ _))
      (Subgroup.inclusion_injective _)
  have hRn : (R.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    exact fun y hy => mem_normalizer_inf_of_mem
      (le_normalizer_map_subtype (CFSG.solvableRadical ↥K') (hLK hy)) (Subgroup.le_normalizer hy)
  rcases hs.eq_bot_or_eq_top_of_normal (R.subgroupOf L) with h0 | h0
  · rw [Subgroup.subgroupOf_eq_bot] at h0
    have hxR : (x : G) ∈ R := ⟨⟨x, hx, rfl⟩, hxL⟩
    have := (Subgroup.disjoint_def.mp h0) hxR hxL
    exact Subtype.ext this
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at h0
    have : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion h0) (Subgroup.inclusion_injective _)
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a b)

theorem card_barO2_barRad_eq {K' L A : Subgroup G} (hLK : L ≤ K') (hs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hAL : A ≤ L) :
    Nat.card ↥(E1.barO2 ↥K' (A.subgroupOf K')) = Nat.card A ∧
      Nat.card ↥(E1.barRad ↥K' (A.subgroupOf K')) = Nat.card A := by
  have hcardA : Nat.card ↥(A.subgroupOf K') = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAL.trans hLK)).toEquiv
  have key : ∀ x ∈ A.subgroupOf K', x ∈ CFSG.solvableRadical ↥K' → x = 1 := fun x hx hxR =>
    eq_one_of_mem_solvableRadical hLK hs hnab (hAL (Subgroup.mem_subgroupOf.mp hx)) hxR
  constructor
  · unfold E1.barO2
    rw [card_map_of_forall_eq_one _ _ fun x hx h1 => key x hx
      (pCore_le_solvableRadical _ ((QuotientGroup.eq_one_iff x).mp h1)), hcardA]
  · unfold E1.barRad
    rw [card_map_of_forall_eq_one _ _ fun x hx h1 => key x hx
      ((QuotientGroup.eq_one_iff x).mp h1), hcardA]

theorem not_eOne_eTwo_of_le_pCoreOf {K' A T : Subgroup G} (hA : A ≤ pCoreOf 2 K') :
    ¬ E1.EOne ↥K' (A.subgroupOf K') ∧
      ¬ E1.ETwo ↥K' ((T ⊓ K').subgroupOf K') (A.subgroupOf K') := by
  have hle : A.subgroupOf K' ≤ CFSG.Open.pCore 2 ↥K' := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hA (Subgroup.mem_subgroupOf.mp hx)
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hO2 : E1.barO2 ↥K' (A.subgroupOf K') = ⊥ := by
    unfold E1.barO2
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hle
  have hRad : E1.barRad ↥K' (A.subgroupOf K') = ⊥ := by
    unfold E1.barRad
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hle.trans (pCore_le_solvableRadical _)
  constructor
  · rintro ⟨p, -, -, -, -, -, hcard⟩
    rw [hO2, Subgroup.card_bot] at hcard
    omega
  · rintro ⟨-, -, -, L, hL, -, hL'⟩
    rw [hRad] at hL'
    rcases hL' with h1 | ⟨h1, -⟩
    · rw [Subgroup.commutator_bot_right] at h1
      have := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
      exact ((Subgroup.nontrivial_iff_ne_bot L).mp this) h1
    · exact h1 bot_le

omit [Finite G] in
theorem mem_normalizer_sup_of_mem {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite G] in
theorem le_of_le_sup_of_simple {L₁ L₂ D P : Subgroup G} (hc : ⁅L₁, L₂⁆ = ⊥)
    (hDN : D ≤ Subgroup.normalizer (L₂ : Set G)) (hs : IsSimpleGroup ↥L₁) (hP : P ≤ D ⊓ L₁)
    (hP1 : P ≠ ⊥) (hπ : L₁ ≤ D ⊔ L₂) : L₁ ≤ D := by
  have hnorm : ((D ⊓ L₁).subgroupOf L₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro y hy
    obtain ⟨d, hd, b, hb, hdb⟩ := exists_mul_of_mem_sup_of_le_normalizer hDN (hπ hy)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ w ∈ L₁, y * w * y⁻¹ = d * w * d⁻¹ := fun w hw => by
      have hbw : w * b = b * w := commute_of_commutator_eq_bot hc hw hb
      rw [hdb]
      calc d * b * w * (d * b)⁻¹ = d * (b * w) * b⁻¹ * d⁻¹ := by group
        _ = d * (w * b) * b⁻¹ * d⁻¹ := by rw [hbw]
        _ = d * w * d⁻¹ := by group
    constructor
    · rintro ⟨hxD, hxL⟩
      refine ⟨?_, L₁.mul_mem (L₁.mul_mem hy hxL) (L₁.inv_mem hy)⟩
      rw [key x hxL]
      exact D.mul_mem (D.mul_mem hd hxD) (D.inv_mem hd)
    · rintro ⟨hxD, hxL⟩
      have hxL' : x ∈ L₁ := by
        have := L₁.mul_mem (L₁.mul_mem (L₁.inv_mem hy) hxL) hy
        simpa [mul_assoc] using this
      refine ⟨?_, hxL'⟩
      rw [key x hxL'] at hxD
      have := D.mul_mem (D.mul_mem (D.inv_mem hd) hxD) hd
      simpa [mul_assoc] using this
  rcases hs.eq_bot_or_eq_top_of_normal ((D ⊓ L₁).subgroupOf L₁) with h0 | h0
  · exfalso
    apply hP1
    rw [Subgroup.subgroupOf_eq_bot] at h0
    exact eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr
      ((Subgroup.disjoint_def.mp h0) (hP hx) (hP hx).2)
  · rw [Subgroup.subgroupOf_eq_top] at h0
    exact h0.trans inf_le_left

theorem proj_le_of_isPGroup {L₁ L₂ R P : Subgroup G} (hc : ⁅L₁, L₂⁆ = ⊥)
    (hinf : L₁ ⊓ L₂ = ⊥) (hRN : R ≤ Subgroup.normalizer (L₂ : Set G)) (hR2 : IsPGroup 2 R)
    (hP : IsSylowTwoOf P L₁) (hPR : P ≤ L₁ ⊓ (R ⊔ L₂)) : L₁ ⊓ (R ⊔ L₂) ≤ P := by
  have h2 : IsPGroup 2 ↥(L₁ ⊓ (R ⊔ L₂)) := by
    intro a
    obtain ⟨r, hr, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_normalizer hRN a.2.2
    obtain ⟨m, hm⟩ := hR2 ⟨r, hr⟩
    have hrm : r ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine ⟨m, Subtype.ext ?_⟩
    have hcomm : (a : G) * b⁻¹ = b⁻¹ * a :=
      commute_of_commutator_eq_bot hc a.2.1 (L₂.inv_mem hb)
    have hr' : r = (a : G) * b⁻¹ := by rw [hab]; group
    have h1 : ((a : G) * b⁻¹) ^ 2 ^ m = 1 := by rw [← hr']; exact hrm
    rw [Commute.mul_pow hcomm] at h1
    have h3 : (a : G) ^ 2 ^ m = ((b⁻¹) ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h4 : (a : G) ^ 2 ^ m ∈ L₁ ⊓ L₂ :=
      ⟨L₁.pow_mem a.2.1 _, by rw [h3]; exact L₂.inv_mem (L₂.pow_mem (L₂.inv_mem hb) _)⟩
    rw [hinf, Subgroup.mem_bot] at h4
    simpa using h4
  exact (A4.isSylowTwoOf_iff_maximal.mp hP).2.2 _ inf_le_left h2 hPR

theorem not_isE_of_pair (hKG3 : KGBenderMax) {H T A K' L₁ L₂ : Subgroup G} {i n : ℕ}
    (hi : i < n) (hn2 : 2 ≤ n) (hB₁ : IsPSL 2 2 n ↥L₁ ∨ IsSz n ↥L₁)
    (hB₂ : IsPSL 2 2 n ↥L₂ ∨ IsSz n ↥L₂) (hO2 : pCoreOf 2 H = ⊥) (hc : ⁅L₁, L₂⁆ = ⊥)
    (hinf : L₁ ⊓ L₂ = ⊥) (hHN : H ≤ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup G) : Set G))
    (horb₁ : ∀ x ∈ H, cjSub x L₁ = L₁ ∨ cjSub x L₁ = L₂)
    (hS₁ : IsSylowTwoOf (T ⊓ L₁) L₁) (hS₂ : IsSylowTwoOf (T ⊓ L₂) L₂) (hP₂1 : T ⊓ L₂ ≠ ⊥)
    (hA : A = T ⊓ L₁ ⊓ Subgroup.centralizer ((T ⊓ L₁ : Subgroup G) : Set G))
    (hAcard : Nat.card A = 2 ^ n) (hE : E1.IsE i H T A K') : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hK'H, hτ, -, hEE⟩ := hE
  have hs₁ := isSimpleGroup_of_psl_or_sz hB₁
  have hnab₁ := nonabelian_of_psl_or_sz (by omega) hB₁
  have hs₂ := isSimpleGroup_of_psl_or_sz hB₂
  have hc' : ⁅L₂, L₁⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hc
  have hinf' : L₂ ⊓ L₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hAP : A ≤ T ⊓ L₁ := by rw [hA]; exact inf_le_left
  have hAL : A ≤ L₁ := hAP.trans inf_le_right
  have h4n : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hA1 : A ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hAcard
    omega
  have hP₁1 : T ⊓ L₁ ≠ ⊥ := fun h0 => hA1 (le_bot_iff.mp (h0 ▸ hAP))
  have hτmem : ∀ x ∈ T, (∀ a ∈ A, x * a = a * x) → x ∈ K' := by
    intro x hxT hxa
    refine (hτ (E1.mem_tauOf.mpr ⟨hxT, ?_, fun a ha => ?_⟩)).2
    · rw [hO2, Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      trivial
    · rw [hO2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hxa a ha
  have hP₁K' : T ⊓ L₁ ≤ K' := fun x hx => hτmem x hx.1 fun a ha => by
    have haC : a ∈ Subgroup.centralizer ((T ⊓ L₁ : Subgroup G) : Set G) := by
      rw [hA] at ha
      exact ha.2
    exact Subgroup.mem_centralizer_iff.mp haC x hx
  have hP₂K' : T ⊓ L₂ ≤ K' := fun x hx => hτmem x hx.1 fun a ha =>
    (commute_of_commutator_eq_bot hc (hAL ha) hx.2).symm
  set D := K' ⊓ (L₁ ⊔ L₂) with hD
  have hDN₁ : D ≤ Subgroup.normalizer (L₁ : Set G) :=
    inf_le_right.trans (sup_le Subgroup.le_normalizer (le_normalizer_of_commutator_eq_bot hc'))
  have hDN₂ : D ≤ Subgroup.normalizer (L₂ : Set G) :=
    inf_le_right.trans (sup_le (le_normalizer_of_commutator_eq_bot hc) Subgroup.le_normalizer)
  have hK'D : K' ≤ Subgroup.normalizer (D : Set G) := fun x hx =>
    mem_normalizer_inf_of_mem (Subgroup.le_normalizer hx) (hHN (hK'H hx))
  have hP₁D : T ⊓ L₁ ≤ D ⊓ L₁ := fun x hx =>
    ⟨⟨hP₁K' hx, Subgroup.mem_sup_left hx.2⟩, hx.2⟩
  have hP₂D : T ⊓ L₂ ≤ D ⊓ L₂ := fun x hx =>
    ⟨⟨hP₂K' hx, Subgroup.mem_sup_right hx.2⟩, hx.2⟩
  have hbig : ¬ L₁ ≤ K' := by
    intro hL₁K'
    obtain ⟨h1, h2⟩ := card_barO2_barRad_eq hL₁K' hs₁ hnab₁ hAL
    have hlt : 2 ^ i < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hi
    rcases hEE with ⟨-, h3⟩ | ⟨-, h3⟩
    · rw [h1, hAcard] at h3
      omega
    · rw [h2, hAcard] at h3
      omega
  have hsmall : ¬ A ≤ pCoreOf 2 K' := by
    intro hle
    obtain ⟨hO, hT⟩ := not_eOne_eTwo_of_le_pCoreOf (T := T) hle
    rcases hEE with ⟨h3, -⟩ | ⟨h3, -⟩
    · exact hO h3
    · exact hT h3
  rcases hKG3 G L₁ (T ⊓ L₁) (L₁ ⊓ (D ⊔ L₂)) n hn2 hB₁ hS₁
      (fun x hx => ⟨hx.2, Subgroup.mem_sup_left (hP₁D hx).1⟩) inf_le_left with hπ₁ | hπ₁
  swap
  · exact hbig ((le_of_le_sup_of_simple hc hDN₂ hs₁ hP₁D hP₁1
      (by rw [← hπ₁]; exact inf_le_right)).trans inf_le_left)
  apply hsmall
  rcases hKG3 G L₂ (T ⊓ L₂) (L₂ ⊓ (D ⊔ L₁)) n hn2 hB₂ hS₂
      (fun x hx => ⟨hx.2, Subgroup.mem_sup_left (hP₂D hx).1⟩) inf_le_left with hπ₂ | hπ₂
  ·
    set Q := T ⊓ L₁ ⊔ T ⊓ L₂ with hQ
    have hQ2 : IsPGroup 2 Q := IsPGroup.to_sup_of_normal_right' hS₁.2.1 hS₂.2.1 fun x hx =>
      mem_normalizer_of_forall_commute fun y hy => commute_of_commutator_eq_bot hc hx.2 hy.2
    have hQD : Q ≤ D := sup_le (fun x hx => (hP₁D hx).1) (fun x hx => (hP₂D hx).1)
    have hQK' : Q ≤ K' := hQD.trans inf_le_left
    have hDQ : D ≤ Subgroup.normalizer (Q : Set G) := by
      intro d hd
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        exists_mul_of_mem_sup_of_le_normalizer (le_normalizer_of_commutator_eq_bot hc) hd.2
      have haπ : a ∈ L₁ ⊓ (D ⊔ L₂) := ⟨ha, by
        have := (D ⊔ L₂).mul_mem (Subgroup.mem_sup_left hd)
          (Subgroup.mem_sup_right (L₂.inv_mem hb))
        simpa using this⟩
      have hbπ : b ∈ L₂ ⊓ (D ⊔ L₁) := ⟨hb, by
        have := (D ⊔ L₁).mul_mem (Subgroup.mem_sup_right (L₁.inv_mem ha))
          (Subgroup.mem_sup_left hd)
        simpa using this⟩
      refine Subgroup.mul_mem _ (mem_normalizer_sup_of_mem (hπ₁ haπ) ?_)
        (mem_normalizer_sup_of_mem ?_ (hπ₂ hbπ))
      · exact mem_normalizer_of_forall_commute fun y hy => commute_of_commutator_eq_bot hc ha hy.2
      · exact mem_normalizer_of_forall_commute fun y hy =>
          (commute_of_commutator_eq_bot hc hy.2 hb).symm
    have hmax : ∀ R : Subgroup G, Q ≤ R → R ≤ D → IsPGroup 2 R → R ≤ Q := by
      intro R hQR hRD hR2
      have h₁ := proj_le_of_isPGroup hc hinf (hRD.trans hDN₂) hR2 hS₁
        (fun x hx => ⟨hx.2, Subgroup.mem_sup_left (hQR (Subgroup.mem_sup_left hx))⟩)
      have h₂ := proj_le_of_isPGroup hc' hinf' (hRD.trans hDN₁) hR2 hS₂
        (fun x hx => ⟨hx.2, Subgroup.mem_sup_left (hQR (Subgroup.mem_sup_right hx))⟩)
      intro r hr
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        exists_mul_of_mem_sup_of_le_normalizer (le_normalizer_of_commutator_eq_bot hc) (hRD hr).2
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (h₁ ⟨ha, ?_⟩))
        (Subgroup.mem_sup_right (h₂ ⟨hb, ?_⟩))
      · have := (R ⊔ L₂).mul_mem (Subgroup.mem_sup_left hr)
          (Subgroup.mem_sup_right (L₂.inv_mem hb))
        simpa using this
      · have := (R ⊔ L₁).mul_mem (Subgroup.mem_sup_right (L₁.inv_mem ha))
          (Subgroup.mem_sup_left hr)
        simpa using this
    have hK'Q : K' ≤ Subgroup.normalizer (Q : Set G) := by
      intro x hx
      have hxD : cjSub x D = D := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK'D hx)
      have hcj : cjSub x Q ≤ D := by
        rw [← hxD]
        exact cjSub_mono hQD
      have h2 : IsPGroup 2 ↥(cjSub x Q ⊔ Q) :=
        IsPGroup.to_sup_of_normal_right' (hQ2.map _) hQ2 (hcj.trans hDQ)
      have hxQ : cjSub x Q ≤ Q := le_sup_left.trans (hmax _ le_sup_right (sup_le hcj hQD) h2)
      apply mem_normalizer_of_cjSub_eq
      exact Subgroup.eq_of_le_of_card_ge hxQ (by rw [card_cjSub])
    exact hAP.trans (le_sup_left.trans
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQK' hK'Q hQ2))
  ·
    have hL₂D : L₂ ≤ D := le_of_le_sup_of_simple hc' hDN₁ hs₂ hP₂D hP₂1
      (by rw [← hπ₂]; exact inf_le_right)
    have hK'N₁ : K' ≤ Subgroup.normalizer (L₁ : Set G) := by
      intro x hx
      rcases horb₁ x (hK'H hx) with h1 | h1
      · exact mem_normalizer_of_cjSub_eq h1
      · exfalso
        apply hbig
        have h2 : cjSub x⁻¹ L₂ = L₁ := by
          rw [← h1, cjSub_cjSub, inv_mul_cancel, cjSub_one]
        rw [← h2, ← cjSub_self_of_mem (K'.inv_mem hx)]
        exact cjSub_mono (hL₂D.trans inf_le_left)
    have hK'P : K' ≤ Subgroup.normalizer ((T ⊓ L₁ : Subgroup G) : Set G) := by
      intro x hx
      have hxL : cjSub x L₁ = L₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK'N₁ hx)
      have hxK' : cjSub x K' = K' := cjSub_self_of_mem hx
      have hcj : cjSub x (T ⊓ L₁) ≤ L₁ ⊓ (D ⊔ L₂) := by
        intro y hy
        have hyL : y ∈ L₁ := by
          have := cjSub_mono (inf_le_right : T ⊓ L₁ ≤ L₁) hy
          rwa [hxL] at this
        have hyK' : y ∈ K' := by
          have := cjSub_mono hP₁K' hy
          rwa [hxK'] at this
        exact ⟨hyL, Subgroup.mem_sup_left ⟨hyK', Subgroup.mem_sup_left hyL⟩⟩
      have h2 : IsPGroup 2 ↥(cjSub x (T ⊓ L₁) ⊔ T ⊓ L₁) :=
        IsPGroup.to_sup_of_normal_right' (hS₁.2.1.map _) hS₁.2.1 (hcj.trans hπ₁)
      have hxP : cjSub x (T ⊓ L₁) ≤ T ⊓ L₁ := le_sup_left.trans
        ((A4.isSylowTwoOf_iff_maximal.mp hS₁).2.2 _
          (sup_le (hcj.trans inf_le_left) inf_le_right) h2 le_sup_right)
      apply mem_normalizer_of_cjSub_eq
      exact Subgroup.eq_of_le_of_card_ge hxP (by rw [card_cjSub])
    exact hAP.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hP₁K' hK'P hS₁.2.1)

variable {H T M V : Subgroup G}

theorem nParam_eq_of_pairCase (hKG3 : KGBenderMax) (h : Hyp28 H T M V) (hJ : kerIn M H = ⊥)
    {K : Subgroup G} {t : G} (hP : PairCase H T K t) {n : ℕ} (hn2 : 2 ≤ n)
    (hK : IsPSL 2 2 n ↥K ∨ IsSz n ↥K) (hle : E1.nParam H ≤ n) : E1.nParam H = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : pCoreOf 2 H = ⊥ := le_bot_iff.mp (hJ ▸ h.minParabolic.pCoreOf_le_kerIn)
  have hTH : T ≤ H := h.minParabolic.isSylow.1
  have htH : t ∈ H := hTH hP.mem
  have hL : IsPSL 2 2 n ↥(cjSub t K) ∨ IsSz n ↥(cjSub t K) :=
    hK.imp (isPSL_of_mulEquiv (cjSubEquiv t K).symm) (isSz_of_mulEquiv' (cjSubEquiv t K).symm)
  obtain ⟨kK, hBK⟩ := exists_fusionBenderBorel_of_psl_or_sz hn2 hK
  obtain ⟨kL, hBL⟩ := exists_fusionBenderBorel_of_psl_or_sz hn2 hL
  have hev : Even (2 ^ n) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have h4n : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hS₁ : IsSylowTwoOf (T ⊓ K) K :=
    E2P.isSylowTwoOf_inf_of_subnormal h.minParabolic.isSylow (subnormal_of_mem_cComp hP.comp)
  have hS₂ : IsSylowTwoOf (T ⊓ cjSub t K) (cjSub t K) :=
    E2P.isSylowTwoOf_inf_of_subnormal h.minParabolic.isSylow (subnormal_of_mem_cComp hP.comp')
  obtain ⟨hZ₁card, hZ₁2⟩ := card_inf_centralizer_of_fusionBenderBorel hBK hS₁
  obtain ⟨hZ₂card, -⟩ := card_inf_centralizer_of_fusionBenderBorel hBL hS₂
  have hP₁1 : T ⊓ K ≠ ⊥ := by
    intro h0
    rw [h0, bot_inf_eq, Subgroup.card_bot] at hZ₁card
    omega
  have hP₂1 : T ⊓ cjSub t K ≠ ⊥ := by
    intro h0
    rw [h0, bot_inf_eq, Subgroup.card_bot] at hZ₂card
    omega
  set Z₁ := T ⊓ K ⊓ Subgroup.centralizer ((T ⊓ K : Subgroup G) : Set G) with hZ₁
  have hZ₁e : IsElemAbelian 2 Z₁ :=
    ⟨Subgroup.le_centralizer_iff_isMulCommutative.mp fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun b hb => Subgroup.mem_centralizer_iff.mp ha.2 b hb.1,
      hZ₁2⟩
  set Ω : Set (Subgroup G) := {A | ∃ g ∈ H, A = cjSub g Z₁} with hΩ
  have hΩinv : E1.IsInvColl H Ω := by
    refine ⟨?_, ?_, ?_⟩
    · rintro A ⟨g, hg, rfl⟩
      rw [← cjSub_self_of_mem hg]
      exact cjSub_mono ((inf_le_left.trans inf_le_right).trans (le_of_mem_cComp hP.comp))
    · rintro A ⟨g, hg, rfl⟩
      exact isElemAbelian_cjSub hZ₁e
    · rintro A ⟨g, hg, rfl⟩ x hx
      refine ⟨x * g, H.mul_mem hx hg, ?_⟩
      show cjSub x (cjSub g Z₁) = cjSub (x * g) Z₁
      rw [cjSub_cjSub]
  have horbL : ∀ x ∈ H, cjSub x (cjSub t K) = cjSub t K ∨ cjSub x (cjSub t K) = K :=
    fun x hx => by
      rw [cjSub_cjSub]
      exact (hP.orbit (x * t) (H.mul_mem hx htH)).symm
  have hcL : ⁅cjSub t K, K⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hP.comm
  have hinfL : cjSub t K ⊓ K = ⊥ := by rw [inf_comm]; exact hP.inf
  have hHNL : H ≤ Subgroup.normalizer ((cjSub t K ⊔ K : Subgroup G) : Set G) := by
    rw [sup_comm]; exact hP.norm
  have hmain : ∀ i : ℕ, i < n → ∀ A ∈ Ω, A ≤ T → ∀ K' : Subgroup G, E1.IsE i H T A K' →
      False := by
    rintro i hin A ⟨g, hg, rfl⟩ hAT K' hE
    have hcardA : Nat.card ↥(cjSub g Z₁) = 2 ^ n := by rw [card_cjSub, hZ₁card]
    have hZg := cjSub_inf_centralizer g (T ⊓ K)
    have hSg := isSylowTwoOf_cjSub hS₁ g
    have hZ₁K : Z₁ ≤ K := inf_le_left.trans inf_le_right
    rcases hP.orbit g hg with hgK | hgL
    · rw [hgK] at hSg
      have hle1 : cjSub g Z₁ ≤ T ⊓ K :=
        le_inf hAT (by rw [← hgK]; exact cjSub_mono hZ₁K)
      have hSeq := eq_of_inf_centralizer_le hev hBK hS₁ hSg (by rw [← hZg]; exact hle1)
      exact not_isE_of_pair hKG3 hin hn2 hK hL hO2 hP.comm hP.inf hP.norm hP.orbit hS₁ hS₂ hP₂1
        (by rw [hZg, ← hSeq]) hcardA hE
    · rw [hgL] at hSg
      have hle1 : cjSub g Z₁ ≤ T ⊓ cjSub t K :=
        le_inf hAT (by rw [← hgL]; exact cjSub_mono hZ₁K)
      have hSeq := eq_of_inf_centralizer_le hev hBL hS₂ hSg (by rw [← hZg]; exact hle1)
      exact not_isE_of_pair hKG3 hin hn2 hL hK hO2 hcL hinfL hHNL horbL hS₂ hS₁ hP₁1
        (by rw [hZg, ← hSeq]) hcardA hE
  have key : ∀ i : ℕ, 0 < i → i < n → ¬ E1.InE i H := by
    intro i _ hin hInE
    have h1 := hInE T h.minParabolic.isSylow Ω hΩinv
    have hE0 : E1.eGen i H T Ω = ⊥ := le_bot_iff.mp (iSup₂_le fun A hA => iSup_le fun hAT =>
      iSup₂_le fun K' hK' => (hmain i hin A hA hAT K' hK').elim)
    rw [hE0, bot_sup_eq] at h1
    have hW : E1.weakClosure T Ω ≤ T := iSup₂_le fun A _ => iSup_le fun hAT => hAT
    have hHW : H ≤ Subgroup.normalizer (E1.weakClosure T Ω : Set G) :=
      calc H = H ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G) := h1.symm
        _ ≤ _ := inf_le_right
    have hWO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hW.trans hTH) hHW
      (h.minParabolic.isSylow.2.1.to_le hW)
    rw [hO2] at hWO
    have hZΩ : Z₁ ∈ Ω := ⟨1, H.one_mem, (cjSub_one Z₁).symm⟩
    have hZW : Z₁ ≤ E1.weakClosure T Ω :=
      le_iSup₂_of_le (f := fun A (_ : A ∈ Ω) => ⨆ (_ : A ≤ T), A) Z₁ hZΩ
        (le_iSup_of_le (inf_le_left.trans inf_le_left) le_rfl)
    have h0 : Z₁ = ⊥ := le_bot_iff.mp (hZW.trans hWO)
    rw [h0, Subgroup.card_bot] at hZ₁card
    omega
  by_contra hne
  have hlt : E1.nParam H < n := lt_of_le_of_ne hle hne
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  rw [← hm] at hlt
  have hmn : m < n := by exact_mod_cast hlt
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · have hodd := E1.odd_of_nParam_le_zero (H := H) (by rw [← hm, hm0]; rfl)
    have hdvd : 2 ∣ Nat.card H := by
      have h1 : 2 ∣ Nat.card Z₁ := by rw [hZ₁card]; exact dvd_pow_self 2 (by omega)
      exact h1.trans (Subgroup.card_dvd_of_le
        ((inf_le_left.trans inf_le_right).trans (le_of_mem_cComp hP.comp)))
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  · exact key m hm0 hmn ((E1.nParam_le_iff hm0).mp (le_of_eq hm.symm))

end E2

end CFSG.Quasithin
