module

public import CFSG.Monster.B.Recog.GenericGoldschmidtSection
public import CFSG.Monster.B.Recog.GenericGoldschmidtArithOmega
public import CFSG.Open.BenderStronglyEmbedded
public import CFSG.Walter.J1Props.Elt

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Open CFSG.ComponentClassification CFSG.Monster.B.Recog
open CFSG.Monster.B.Recog.GoldschmidtApp CFSG.Monster.B.Recog.GoldschmidtSection
open CFSG.SignalizerFunctorTheorem.McBride Matrix
open scoped MatrixGroups

namespace GoldVariant

theorem goldschmidtOddCore_eq_bot_of_mulEquiv {H Y : Type*} [Group H] [Group Y] (φ : H ≃* Y)
    (h : goldschmidtOddCore H = ⊥) : goldschmidtOddCore Y = ⊥ := by
  rw [eq_bot_iff]
  refine sSup_le fun N hN => ?_
  obtain ⟨hNn, hodd⟩ := hN
  have hle : N.map φ.symm.toMonoidHom ≤ goldschmidtOddCore H := by
    refine le_sSup ⟨hNn.map _ φ.symm.surjective, ?_⟩
    rw [Subgroup.card_map_of_injective (f := φ.symm.toMonoidHom) φ.symm.injective]
    exact hodd
  rw [h, le_bot_iff] at hle
  intro y hy
  have hmem : φ.symm.toMonoidHom y ∈ N.map φ.symm.toMonoidHom := Subgroup.mem_map_of_mem _ hy
  rw [hle, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  simpa using congrArg φ hmem

theorem eq_bot_of_normal_of_comm {Y : Type*} [Group Y] [Finite Y]
    (h2 : CFSG.Open.pCore 2 Y = ⊥) (hodd : goldschmidtOddCore Y = ⊥)
    (A : Subgroup Y) [A.Normal] (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 A) := inferInstance
  have hPn : (P : Subgroup A).Normal := ⟨fun n hn g => by
    have e : g * n * g⁻¹ = n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hA _ g.2 _ n.2, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact hn⟩
  have : (P : Subgroup A).Characteristic := Sylow.characteristic_of_normal P hPn
  have hPY : ((P : Subgroup A).map A.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hle : (P : Subgroup A).map A.subtype ≤ CFSG.Open.pCore 2 Y :=
    le_sSup ⟨hPY, P.isPGroup'.map _⟩
  rw [h2, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ A.subtype_injective] at hle
  have hodd' : Odd (Nat.card A) := by
    refine Nat.odd_iff.2 ?_
    by_contra hne
    have h2A : 2 ∣ Nat.card A := by omega
    have h2P := P.dvd_card_of_dvd_card h2A
    rw [hle, Subgroup.card_bot] at h2P
    exact absurd h2P (by norm_num)
  have hA' : A ≤ goldschmidtOddCore Y := le_sSup ⟨inferInstance, hodd'⟩
  rwa [hodd, le_bot_iff] at hA'

theorem center_component_eq_bot {Y : Type*} [Group Y] [Finite Y]
    (h2 : CFSG.Open.pCore 2 Y = ⊥) (hodd : goldschmidtOddCore Y = ⊥)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) : Subgroup.center K = ⊥ := by
  have hEn : (goldschmidtLayer Y).Normal := Layer.normal Y
  have hZn : (goldschmidtLayer Y ⊓
      Subgroup.centralizer ((goldschmidtLayer Y : Subgroup Y) : Set Y)).Normal :=
    ⟨fun x hx g => ⟨hEn.conj_mem x hx.1 g,
      conj_mem_centralizer ((Subgroup.normalizer_eq_top (goldschmidtLayer Y)).symm ▸
        Subgroup.mem_top g) hx.2⟩⟩
  have hZ := eq_bot_of_normal_of_comm h2 hodd (goldschmidtLayer Y ⊓
      Subgroup.centralizer ((goldschmidtLayer Y : Subgroup Y) : Set Y)) fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 hb.2 a ha.1
  rw [eq_bot_iff]
  intro z hz
  have hzE : (z : Y) ∈ goldschmidtLayer Y := Layer.component_le hK z.2
  have hEz : goldschmidtLayer Y ≤ Subgroup.centralizer ({(z : Y)} : Set Y) := by
    refine sSup_le fun K₂ hK₂ => ?_
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hne : K₂ = K
    · subst hne
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨k, hk⟩)
    · have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (LocalComponents.commute_of_ne K₂ K hK₂ hK hne) hk
      exact (Subgroup.mem_centralizer_iff.1 hc z z.2).symm
  have hzC : (z : Y) ∈ Subgroup.centralizer ((goldschmidtLayer Y : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.1 (hEz he)
  have hmem : (z : Y) ∈ goldschmidtLayer Y ⊓
      Subgroup.centralizer ((goldschmidtLayer Y : Subgroup Y) : Set Y) := ⟨hzE, hzC⟩
  rw [hZ, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact Subtype.ext hmem

theorem exists_conj_le_sylow {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 2 P) (S : Sylow 2 G) : ∃ g : G, ∀ x ∈ P, g * x * g⁻¹ ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R S
  refine ⟨g, fun x hx => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hR hx

theorem sylow_psl2_even {K : Type*} [Group K] [Finite K] {f : ℕ} (hf : 2 ≤ f)
    (e : K ≃* PSL(2, GaloisField 2 f)) (Q : Sylow 2 K) :
    Nat.card (Q : Subgroup K) = 2 ^ f ∧ ∀ x ∈ (Q : Subgroup K), x * x = 1 := by
  have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv K e.toEquiv
  have hB := (CFSG.Open.Open.bender_psl2_borel f hf).map_mulEquiv e.symm
  obtain ⟨-, -, hZ2, hZcard, hQcard⟩ := hB Q
  rw [pow_one] at hQcard
  have htop : Subgroup.center (Q : Subgroup K) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (hZcard.trans hQcard.symm)
  refine ⟨hQcard, fun x hx => ?_⟩
  have h := hZ2 ⟨x, hx⟩ (htop ▸ Subgroup.mem_top _)
  have h' : (⟨x, hx⟩ : (Q : Subgroup K)) * ⟨x, hx⟩ = 1 := by
    rw [← pow_two]
    exact h
  exact congrArg Subtype.val h'

end GoldVariant

open GoldVariant

theorem normal_of_goldschmidt_conclusion_of_psl2 {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) {V : Subgroup X} (hVS : V ≤ S)
    (hGold :
      let M : Subgroup X := Subgroup.normalClosure (V : Set X)
      let π := QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore M)
      let T := ((S : Subgroup X).subgroupOf M).map π ⊓
        CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M)
      CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
          CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M) = ⊤ ∧
      (V.subgroupOf M).map π =
        CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
          Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
      ∀ K : Subgroup (M ⧸ CFSG.Open.goldschmidtOddCore M), CFSG.Open.IsComponentOf K ⊤ →
        CFSG.Open.goldschmidtSimpleType (K ⧸ Subgroup.center K))
    (hclosed : ∀ a ∈ V, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ V)
    (hO : CFSG.oddCore X = ⊥)
    (hC2 : IsPGroup 2 (Subgroup.centralizer (V : Set X)))
    (hQB1' : ∀ U : Subgroup X, U ≤ V →
      Subgroup.normalizer (V : Set X) ≤ Subgroup.normalizer (U : Set X) → U = ⊥ ∨ U = V)
    {O : Type*} [Group O] (ρ : ↥(Subgroup.normalizer (V : Set X)) →* O)
    (hρ : Function.Surjective ρ)
    (hker : ∀ g : ↥(Subgroup.normalizer (V : Set X)),
      ρ g = 1 ↔ (g : X) ∈ Subgroup.centralizer (V : Set X))
    (Ω : Subgroup O) (hΩ : IsSimpleGroup Ω) (hΩnab : ¬ IsMulCommutative Ω)
    (hΩmin : ∀ R : Subgroup O, R.Normal → R ≠ ⊥ → Ω ≤ R)
    (hAr : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.goldschmidtSimpleType L →
      Nat.card Ω ∣ Nat.card L → Nat.card L ∣ Nat.card X →
        ∃ f : ℕ, 2 ≤ f ∧ Nat.card V < 2 ^ f ∧ Nonempty (L ≃* PSL(2, GaloisField 2 f))) :
    V.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases eq_or_ne V ⊥ with hV1 | hV1
  · rw [hV1]
    infer_instance
  obtain ⟨-, hGb, hGc⟩ := hGold
  have hOM : goldschmidtOddCore (Subgroup.normalClosure (V : Set X)) = ⊥ := by
    have h := OddCore.normal_intersection X (Subgroup.normalClosure (V : Set X))
    have h' : componentClassificationOddCore X = ⊥ := hO
    rw [h', inf_bot_eq] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 h
  set M : Subgroup X := Subgroup.normalClosure (V : Set X) with hM
  have hVM : V ≤ M := Subgroup.le_normalClosure
  have hπ : Function.Injective (QuotientGroup.mk' (goldschmidtOddCore M)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hOM]
  obtain ⟨φ, hφ⟩ : ∃ φ : M ≃* M ⧸ goldschmidtOddCore M,
      ∀ m, φ m = QuotientGroup.mk' (goldschmidtOddCore M) m :=
    ⟨MulEquiv.ofBijective _ ⟨hπ, QuotientGroup.mk'_surjective _⟩, fun _ => rfl⟩
  obtain ⟨ι, hιdef⟩ : ∃ ι : M ⧸ goldschmidtOddCore M →* X,
      ι = M.subtype.comp φ.symm.toMonoidHom := ⟨_, rfl⟩
  have hι : Function.Injective ι := by
    rw [hιdef]
    exact M.subtype_injective.comp φ.symm.injective
  have hιπ : ∀ m : M, ι (QuotientGroup.mk' (goldschmidtOddCore M) m) = m := by
    intro m
    rw [hιdef, ← hφ]
    simp
  have hnormal : ∀ A : Subgroup (M ⧸ goldschmidtOddCore M), A.Characteristic →
      (A.map ι).Normal := by
    intro A hA
    rw [hιdef]
    exact normal_map_of_characteristic φ hA
  have hnorm : ∀ (A : Subgroup X) [A.Normal] (n : X), n ∈ Subgroup.normalizer (A : Set X) :=
    fun A _ n => (Subgroup.normalizer_eq_top A).symm ▸ Subgroup.mem_top n
  have hVeq : ((V.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M))).map ι = V := by
    have hcomp : ι.comp (QuotientGroup.mk' (goldschmidtOddCore M)) = M.subtype := by
      ext m
      exact hιπ m
    rw [Subgroup.map_map, hcomp, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVM]
  have hLX : ∀ K : Subgroup (M ⧸ goldschmidtOddCore M),
      Nat.card (K ⧸ Subgroup.center K) ∣ Nat.card X := by
    intro K
    refine (Subgroup.index_dvd_card (Subgroup.center K)).trans
      ((Subgroup.card_subgroup_dvd_card K).trans ?_)
    rw [← Nat.card_congr φ.toEquiv]
    exact Subgroup.card_subgroup_dvd_card M
  set E := goldschmidtLayer (M ⧸ goldschmidtOddCore M) with hE
  have hEX : (E.map ι).Normal := hnormal E (Layer.characteristic _)
  by_cases hO2 : CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) = ⊥
  swap
  · have hle : (CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M)).map ι ≤ V := by
      rw [← hVeq, hGb]
      exact Subgroup.map_mono le_sup_left
    have hP := hnormal _ (openPCore_characteristic _)
    rcases hQB1' _ hle (fun n _ => hnorm _ n) with h | h
    · exact absurd ((Subgroup.map_eq_bot_iff_of_injective _ hι).1 h) hO2
    · rw [← h]
      exact hP
  have hVE : V ≤ E.map ι := by
    rw [← hVeq, hGb, hO2, bot_sup_eq]
    exact Subgroup.map_mono ((Subgroup.closure_le _).2 fun t ht => ht.1.2)
  have hinv : ∀ y : X, y ∈ (S : Subgroup X) → y ∈ E.map ι → y * y = 1 → y ∈ V := by
    intro y hyS hyE hy2
    obtain ⟨e, he, rfl⟩ := hyE
    have hyM : ι e ∈ M := by
      rw [hιdef]
      exact (φ.symm e).2
    have hπe : QuotientGroup.mk' (goldschmidtOddCore M) ⟨ι e, hyM⟩ = e :=
      hι (by rw [hιπ])
    have he2 : e ^ 2 = 1 := by
      apply hι
      rw [map_pow, pow_two, hy2, map_one]
    have hmemV : e ∈ (V.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M)) := by
      rw [hGb, hO2, bot_sup_eq]
      exact Subgroup.subset_closure ⟨⟨⟨⟨ι e, hyM⟩, hyS, hπe⟩, he⟩, he2⟩
    rw [← hVeq]
    exact Subgroup.mem_map_of_mem ι hmemV
  have hRn : ((E.map ι).subgroupOf (Subgroup.normalizer (V : Set X))).Normal := inferInstance
  by_cases hR : ((E.map ι).subgroupOf (Subgroup.normalizer (V : Set X))).map ρ = ⊥
  ·
    have hRC : Subgroup.normalizer (V : Set X) ⊓ E.map ι ≤ Subgroup.centralizer (V : Set X) := by
      intro x hx
      have h1 := Subgroup.mem_map_of_mem ρ
        (show (⟨x, hx.1⟩ : Subgroup.normalizer (V : Set X)) ∈
          (E.map ι).subgroupOf (Subgroup.normalizer (V : Set X)) from hx.2)
      rw [hR, Subgroup.mem_bot] at h1
      exact (hker _).1 h1
    have hSN : (S : Subgroup X) ≤ Subgroup.normalizer (V : Set X) := fun s hs =>
      Subgroup.mem_normalizer_fintype fun v hv => by
        have h := hclosed v hv s⁻¹ (by
          rw [inv_inv]
          exact S.mul_mem (S.mul_mem hs (hVS hv)) (S.inv_mem hs))
        rwa [inv_inv] at h
    have hReq : Subgroup.normalizer (V : Set X) ⊓ E.map ι = (S : Subgroup X) ⊓ E.map ι :=
      eq_inf_of_isPGroup S (hC2.to_le hRC) inf_le_right (inf_le_inf_right _ hSN)
    obtain ⟨P, hP⟩ : ∃ P : Sylow 2 (E.map ι),
        (P : Subgroup (E.map ι)) = ((S : Subgroup X) ⊓ E.map ι).subgroupOf (E.map ι) := by
      obtain ⟨P, hP⟩ := ((S.isPGroup'.to_le (inf_le_left :
        (S : Subgroup X) ⊓ E.map ι ≤ S)).comap_of_injective _
          (E.map ι).subtype_injective).exists_le_sylow
      refine ⟨P, ?_⟩
      have h := eq_inf_of_isPGroup S (R := (P : Subgroup (E.map ι)).map (E.map ι).subtype)
        (P.isPGroup'.map _) (Subgroup.map_subtype_le _)
        (fun x hx => ⟨⟨x, hx.2⟩, hP hx, rfl⟩)
      rw [← h, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
        (E.map ι).subtype_injective]
    have hPC : ∀ p ∈ (P : Subgroup (E.map ι)), (p : X) ∈ Subgroup.centralizer (V : Set X) := by
      intro p hp
      rw [hP, Subgroup.mem_subgroupOf, ← hReq] at hp
      exact hRC hp
    have hV2 : IsPGroup 2 V := S.isPGroup'.to_le hVS
    have h2V : 2 ∣ Nat.card V := by
      rcases hV2.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.1 h) hV1
      · exact h
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2V
    have hvE : (v : X) ∈ E.map ι := hVE v.2
    have hvP : (⟨v, hvE⟩ : E.map ι) ∈ (P : Subgroup (E.map ι)) := by
      rw [hP, Subgroup.mem_subgroupOf]
      exact ⟨hVS v.2, hvE⟩
    have hvZ : (⟨⟨v, hvE⟩, hvP⟩ : (P : Subgroup (E.map ι))) ∈
        Subgroup.center (P : Subgroup (E.map ι)) := by
      rw [Subgroup.mem_center_iff]
      intro p
      refine Subtype.ext (Subtype.ext ?_)
      simp only [Subgroup.coe_mul]
      exact (Subgroup.mem_centralizer_iff.1 (hPC p p.2) v v.2).symm
    have hv2 : orderOf (⟨⟨v, hvE⟩, hvP⟩ : (P : Subgroup (E.map ι))) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hv]
    have hwc : ∀ g : E.map ι, g⁻¹ * (⟨v, hvE⟩ : E.map ι) * g ∈ (P : Subgroup (E.map ι)) →
        g⁻¹ * (⟨v, hvE⟩ : E.map ι) * g = ⟨v, hvE⟩ := by
      intro g hg
      have hgS : (g : X)⁻¹ * v * g ∈ (S : Subgroup X) := by
        rw [hP, Subgroup.mem_subgroupOf] at hg
        exact hg.1
      have hgV := hclosed v v.2 g hgS
      have hcent : ∀ y : E.map ι, (y : X) ∈ V → y ∈ Subgroup.centralizer
          ((P : Subgroup (E.map ι)) : Set (E.map ι)) := by
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro p hp
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hPC p hp) y hy).symm)
      obtain ⟨n, hn, hgn⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer P ⟨v, hvE⟩ g
        (hcent _ v.2) (hcent _ hgV)
      have hnN : (n : X) ∈ Subgroup.normalizer (V : Set X) := Subgroup.mem_normalizer_fintype
        fun w hw => by
          have hwP : (⟨w, hVE hw⟩ : E.map ι) ∈ (P : Subgroup (E.map ι)) := by
            rw [hP, Subgroup.mem_subgroupOf]
            exact ⟨hVS hw, hVE hw⟩
          have h := (Subgroup.mem_normalizer_iff.1 hn _).1 hwP
          rw [hP, Subgroup.mem_subgroupOf] at h
          have h' := hclosed w hw (n : X)⁻¹ (by rw [inv_inv]; exact h.1)
          rwa [inv_inv] at h'
      have hnC := hRC ⟨hnN, n.2⟩
      rw [hgn]
      refine Subtype.ext ?_
      show (n : X)⁻¹ * v * n = v
      have hvn := Subgroup.mem_centralizer_iff.1 hnC v v.2
      rw [mul_assoc, hvn, ← mul_assoc, inv_mul_cancel, one_mul]
    have hGl := CFSG.Adapters.glauberman_zStar P ⟨⟨v, hvE⟩, hvP⟩ hvZ hv2 hwc
    have hOE : CFSG.oddCore (E.map ι) = ⊥ := by
      have h := OddCore.normal_intersection X (E.map ι)
      have h' : componentClassificationOddCore X = ⊥ := hO
      rw [h', inf_bot_eq] at h
      exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 h
    have hvC : (v : X) ∈ Subgroup.centralizer ((E.map ι : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨c, hc, k, hk, hck⟩ := hGl.1 ⟨x, hx⟩
      rw [hOE, Subgroup.mem_bot] at hk
      rw [hk, mul_one] at hck
      have h := Subgroup.mem_centralizer_singleton_iff.1 hc
      rw [← hck] at h
      have h2 := congrArg Subtype.val h
      simp only [Subgroup.coe_mul] at h2
      exact h2
    rcases hQB1' (V ⊓ Subgroup.centralizer ((E.map ι : Subgroup X) : Set X)) inf_le_left
        (fun n hn => mem_normalizer_inf hn
          (hnorm (Subgroup.centralizer ((E.map ι : Subgroup X) : Set X)) n)) with h | h
    · have hmem : (v : X) ∈ V ⊓ Subgroup.centralizer ((E.map ι : Subgroup X) : Set X) :=
        ⟨v.2, hvC⟩
      rw [h, Subgroup.mem_bot] at hmem
      have hv1 : v = 1 := Subtype.ext hmem
      rw [hv1, orderOf_one] at hv
      exact absurd hv (by norm_num)
    · have hle : V ≤ Subgroup.centralizer ((E.map ι : Subgroup X) : Set X) := h ▸ inf_le_right
      have hE2 : IsPGroup 2 (E.map ι) := hC2.to_le (Subgroup.le_centralizer_iff.1 hle)
      have hEbot : E = ⊥ := eq_bot_of_map_isPGroup (Layer.perfect _) hι hE2
      exfalso
      apply hV1
      rw [eq_bot_iff]
      refine hVE.trans ?_
      rw [hEbot, Subgroup.map_bot]
  ·
    have hΩR := hΩmin _ (hRn.map ρ hρ) hR
    have := hΩ
    set HY : Subgroup (M ⧸ goldschmidtOddCore M) :=
      ((((E.map ι).subgroupOf (Subgroup.normalizer (V : Set X))) ⊓ Ω.comap ρ).map
        (Subgroup.normalizer (V : Set X)).subtype).comap ι with hHY
    have hHYE : HY ≤ E := by
      intro y hy
      obtain ⟨n, ⟨⟨e, he, hen⟩, -⟩, hny⟩ := hy
      rw [hny] at hen
      rw [← hι hen]
      exact he
    have hmemN : ∀ y : HY, ι y ∈ Subgroup.normalizer (V : Set X) := by
      intro y
      obtain ⟨n, -, hny⟩ := y.2
      rw [← hny]
      exact n.2
    let f₁ : HY →* Subgroup.normalizer (V : Set X) :=
      (ι.comp HY.subtype).codRestrict _ hmemN
    have hf₁ : ∀ y : HY, ρ (f₁ y) ∈ Ω := by
      intro y
      obtain ⟨n, ⟨-, hnΩ⟩, hny⟩ := y.2
      have e1 : f₁ y = n := Subtype.ext hny.symm
      rw [e1]
      exact hnΩ
    let f : HY →* Ω := (ρ.comp f₁).codRestrict Ω hf₁
    have hf : Function.Surjective f := by
      intro ω
      obtain ⟨n, hnR, hnω⟩ := hΩR ω.2
      obtain ⟨e, he, hen⟩ := hnR
      have hnΩ : n ∈ Ω.comap ρ := by
        rw [Subgroup.mem_comap, hnω]
        exact ω.2
      have hy : e ∈ HY := ⟨n, ⟨⟨e, he, hen⟩, hnΩ⟩, hen.symm⟩
      refine ⟨⟨e, hy⟩, Subtype.ext ?_⟩
      show ρ (f₁ ⟨e, hy⟩) = ω
      have e1 : f₁ ⟨e, hy⟩ = n := Subtype.ext hen
      rw [e1, hnω]
    obtain ⟨K, hK, hdvd⟩ := exists_component_dvd_of_simple_quotient hΩnab hHYE f hf
    obtain ⟨q, hq2, hqV, ⟨e⟩⟩ := hAr _ (hGc K hK) hdvd (hLX K)
    have hZK : Subgroup.center K = ⊥ := center_component_eq_bot hO2
      (goldschmidtOddCore_eq_bot_of_mulEquiv φ hOM) hK
    let eK : K ≃* PSL(2, GaloisField 2 q) :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZK.symm)).trans e
    obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
    obtain ⟨hQcard, hQ2⟩ := sylow_psl2_even hq2 eK Q
    set Q' : Subgroup X := ((Q : Subgroup K).map K.subtype).map ι with hQ'
    have hQ'2 : IsPGroup 2 Q' := (Q.isPGroup'.map _).map _
    obtain ⟨g, hg⟩ := exists_conj_le_sylow hQ'2 S
    have hQ'V : Q'.map (MulAut.conj g).toMonoidHom ≤ V := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨_, ⟨k, hk, rfl⟩, rfl⟩ := hy
      have hkE : ι (k : M ⧸ goldschmidtOddCore M) ∈ E.map ι :=
        Subgroup.mem_map_of_mem ι (Layer.component_le hK k.2)
      have hk2 : (k : M ⧸ goldschmidtOddCore M) * k = 1 := by
        rw [← Subgroup.coe_mul, hQ2 k hk, Subgroup.coe_one]
      have hι2 : ι k * ι k = 1 := by
        rw [← map_mul, hk2, map_one]
      have hS' : g * ι k * g⁻¹ ∈ (S : Subgroup X) := hg _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      have hE' : g * ι k * g⁻¹ ∈ E.map ι := hEX.conj_mem _ hkE g
      have h2' : g * ι k * g⁻¹ * (g * ι k * g⁻¹) = 1 := by
        rw [show g * ι k * g⁻¹ * (g * ι k * g⁻¹) = g * (ι k * ι k) * g⁻¹ by group, hι2,
          mul_one, mul_inv_cancel]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
      exact hinv _ hS' hE' h2'
    have hcardQ' : Nat.card (Q'.map (MulAut.conj g).toMonoidHom) = 2 ^ q := by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective, hQ', Subgroup.card_map_of_injective hι,
        Subgroup.card_map_of_injective K.subtype_injective, hQcard]
    exact absurd (Subgroup.card_le_of_le hQ'V) (by rw [hcardQ']; exact not_le.2 hqV)

namespace GoldVariant

theorem card_psl42_le :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) ≤ 20160 := by
  have h1 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ≤
      Nat.card (GL (Fin 4) (ZMod 2)) :=
    Nat.card_le_card_of_injective _ Matrix.SpecialLinearGroup.toGL_injective
  have h3 : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
    rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
    norm_num
  omega

theorem exists_injective_mulAut_psl {V : Type*} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v * v = 1) (hV : Nat.card V = 16) :
    ∃ κ : MulAut V →* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2),
      Function.Injective κ := by
  classical
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    exact hV2 (Additive.toMul x)
  have : Fintype (Additive V) := Fintype.ofFinite _
  have hrank : Module.finrank (ZMod 2) (Additive V) = 4 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
    have h16 : Nat.card (Additive V) = 16 := hV
    rw [h16, show (16 : ℕ) = 2 ^ 4 by norm_num] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let b : Module.Basis (Fin 4) (ZMod 2) (Additive V) := Module.finBasisOfFinrankEq _ _ hrank
  let f : MulAut V →* Module.End (ZMod 2) (Additive V) :=
    { toFun := fun σ => (MulEquiv.toAdditive σ).toAddMonoidHom.toZModLinearMap 2
      map_one' := by ext x; rfl
      map_mul' := fun σ τ => by ext x; rfl }
  let β : MulAut V →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive V) :=
    (Units.map f).comp (toUnits : MulAut V ≃* (MulAut V)ˣ).toMonoidHom
  have hβ : Function.Injective β := by
    intro σ τ h
    have h' := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) (Additive V) =>
      (u : Module.End (ZMod 2) (Additive V))) h
    ext x
    exact LinearMap.congr_fun h' (Additive.ofMul x)
  let γ := (Matrix.GeneralLinearGroup.toLin' b).symm
  have hdet : ∀ A : GL (Fin 4) (ZMod 2), (A : Matrix (Fin 4) (Fin 4) (ZMod 2)).det = 1 := by
    intro A
    have h2 : ∀ x : ZMod 2, IsUnit x → x = 1 := by decide
    exact h2 _ (by simpa using (Matrix.isUnit_det_of_invertible
      (A : Matrix (Fin 4) (Fin 4) (ZMod 2))))
  let δ : GL (Fin 4) (ZMod 2) →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    { toFun := fun A => ⟨A, hdet A⟩
      map_one' := rfl
      map_mul' := fun A B => rfl }
  have hδ : Function.Injective δ := fun A B h => Units.ext (congrArg Subtype.val h)
  let ε := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
  have hε : Function.Injective ε := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    have h1 : ∀ x : ZMod 2, x ^ 4 = 1 → x = 1 := by decide
    rw [Fintype.card_fin] at hr
    rw [h1 r hr] at hrA
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by rw [← hrA]; simp)
  exact ⟨ε.comp (δ.comp (γ.toMonoidHom.comp β)),
    hε.comp (hδ.comp (γ.injective.comp hβ))⟩

theorem mulAut_isSimpleGroup {V : Type*} [Group V] [Finite V]
    (hcomm : ∀ a b : V, a * b = b * a) (hV2 : ∀ v : V, v * v = 1) (hV : Nat.card V = 16)
    (h20160 : 20160 ≤ Nat.card (MulAut V)) :
    IsSimpleGroup (MulAut V) ∧ Nat.card (MulAut V) = 20160 := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 4 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  obtain ⟨κ, hκ⟩ : ∃ κ : MulAut V →* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2),
      Function.Injective κ := by
    let _ : CommGroup V := { (inferInstance : Group V) with mul_comm := hcomm }
    exact exists_injective_mulAut_psl hV2 hV
  have hle := (Nat.card_le_card_of_injective κ hκ).trans card_psl42_le
  have hbij := hκ.bijective_of_nat_card_le (card_psl42_le.trans h20160)
  exact ⟨(MulEquiv.ofBijective κ hbij).isSimpleGroup, le_antisymm hle h20160⟩

theorem not_isMulCommutative_of_card {G : Type*} [Group G] [IsSimpleGroup G]
    (hG : Nat.card G = 20160) : ¬ IsMulCommutative G := by
  intro h
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := h.is_comm.comm }
  have := IsSimpleGroup.prime_card (α := G)
  rw [hG] at this
  exact absurd this (by norm_num)

theorem psl2_of_goldschmidtSimpleType {L : Type} [Group L] [Finite L]
    (hL : goldschmidtSimpleType L) (hdvd : 2 ^ 6 * 3 * 5 * 7 ∣ Nat.card L)
    (h17 : (Nat.card L).factorization 2 ≤ 17) :
    ∃ f : ℕ, 6 ≤ f ∧ Nonempty (L ≃* PSL(2, GaloisField 2 f)) := by
  have h6 : 6 ≤ (Nat.card L).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos (α := L)).ne').1
      ((by norm_num : 2 ^ 6 ∣ 2 ^ 6 * 3 * 5 * 7).trans hdvd)
  have h105 : 3 * 5 * 7 ∣ Nat.card L :=
    (by norm_num : 3 * 5 * 7 ∣ 2 ^ 6 * 3 * 5 * 7).trans hdvd
  rcases hL with ⟨f, hf, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpo, hf, -, hq, ⟨e⟩⟩ |
    ⟨m, -, hm⟩ | ⟨⟨e⟩⟩
  ·
    have hcard : Nat.card L = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
      (Nat.card_congr e.toEquiv).trans (NearSolvable.card_psl2_even (by omega))
    have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
      rw [← pow_mul]
      exact GoldschmidtArith.odd_two_pow_sub_one (by omega)
    rw [hcard, GoldschmidtArith.factorization_two_pow_mul_odd f hodd] at h6
    exact ⟨f, h6, ⟨e⟩⟩
  · exact absurd ((by norm_num : 3 ∣ 3 * 5 * 7).trans h105)
      (GoldschmidtArithOmega.sz_not_three_dvd e)
  ·
    exfalso
    have h := NearSolvable.card_psu3_mul_gcd (p := f) (by omega)
    rw [← Nat.card_congr e.toEquiv] at h
    have hg : Odd (Nat.gcd 3 (2 ^ f + 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
    have hodd : Odd (((2 ^ f) ^ 2 - 1) * (2 ^ (f * 3) + 1)) := by
      rw [← pow_mul]
      exact (GoldschmidtArith.odd_two_pow_sub_one (by omega)).mul
        (GoldschmidtArith.odd_two_pow_add_one (by omega))
    have hfac : (Nat.card L * Nat.gcd 3 (2 ^ f + 1)).factorization 2 =
        ((2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1))).factorization 2 := by
      rw [h]
    rw [Nat.factorization_mul Nat.card_pos.ne' hg.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hg.not_two_dvd_nat, add_zero, ← pow_mul,
      GoldschmidtArith.factorization_two_pow_mul_odd _ hodd] at hfac
    rw [hfac] at h17
    have hdvd' : 3 * 5 * 7 ∣ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
      rw [← h]
      exact h105.trans (Dvd.intro _ rfl)
    have hf5 : f ≤ 5 := by omega
    interval_cases f <;> norm_num at hdvd'
  · have h2 := GoldschmidtArithOmega.psl2_odd_factorization hpo hf hq e
    omega
  · have h2 := GoldschmidtArithOmega.ree_factorization hm
    omega
  ·
    have hcard : Nat.card L = 175560 := by
      rw [Nat.card_congr e.toEquiv, show goldschmidtJ1 = walterJ1 from rfl,
        CFSG.Walter.J1Props.card_walterJ1]
    rw [hcard] at hdvd
    norm_num at hdvd

end GoldVariant

theorem normal_of_goldschmidt_conclusion_of_E16 {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) {V : Subgroup X} (hVS : V ≤ S)
    (hGold :
      let M : Subgroup X := Subgroup.normalClosure (V : Set X)
      let π := QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore M)
      let T := ((S : Subgroup X).subgroupOf M).map π ⊓
        CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M)
      CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
          CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M) = ⊤ ∧
      (V.subgroupOf M).map π =
        CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
          Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
      ∀ K : Subgroup (M ⧸ CFSG.Open.goldschmidtOddCore M), CFSG.Open.IsComponentOf K ⊤ →
        CFSG.Open.goldschmidtSimpleType (K ⧸ Subgroup.center K))
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ v ∈ V, v * v = 1)
    (hV16 : Nat.card V = 16)
    (hclosed : ∀ a ∈ V, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ V)
    (hO : CFSG.oddCore X = ⊥)
    (hC2 : IsPGroup 2 (Subgroup.centralizer (V : Set X)))
    (htrans : ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (V : Set X), n * v * n⁻¹ = w)
    (hN : 20160 * Nat.card (Subgroup.centralizer (V : Set X)) ≤
      Nat.card (Subgroup.normalizer (V : Set X)))
    (hX : (Nat.card X).factorization 2 ≤ 17) :
    V.Normal := by
  classical
  let ρ := V.normalizerMonoidHom
  have hker : ∀ g : ↥(Subgroup.normalizer (V : Set X)),
      ρ g = 1 ↔ (g : X) ∈ Subgroup.centralizer (V : Set X) := by
    intro g
    constructor
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 := congrArg (fun σ : MulAut V => ((σ ⟨v, hv⟩ : V) : X)) h
      simp only [ρ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h1
      calc v * g = (g * v * (g : X)⁻¹) * g := by rw [h1]
        _ = g * v := by group
    · intro h
      ext v
      simp only [ρ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
      rw [Subgroup.mem_centralizer_iff] at h
      rw [← h v v.2, mul_assoc, mul_inv_cancel, mul_one]
  have hkerρ : ρ.ker =
      (Subgroup.centralizer (V : Set X)).subgroupOf (Subgroup.normalizer (V : Set X)) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker g
  have hrange : 20160 ≤ Nat.card ρ.range := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hkerρ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer (V : Set X))).toEquiv] at h1
    rw [h1] at hN
    exact Nat.le_of_mul_le_mul_right hN Nat.card_pos
  have : Finite (MulAut V) :=
    Finite.of_injective (fun σ : MulAut V => (σ : V → V)) DFunLike.coe_injective
  have hle : 20160 ≤ Nat.card (MulAut V) := hrange.trans (Subgroup.card_le_card_group ρ.range)
  obtain ⟨hsimp, hcard⟩ := GoldVariant.mulAut_isSimpleGroup
    (fun a b => Subtype.ext (hVab a a.2 b b.2)) (fun v => Subtype.ext (hV2 v v.2)) hV16 hle
  have hρ : Function.Surjective ρ := by
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _
      (le_antisymm (Subgroup.card_le_card_group ρ.range) (hcard ▸ hrange))
  have hΩ : IsSimpleGroup (⊤ : Subgroup (MulAut V)) := Subgroup.topEquiv.isSimpleGroup
  have hΩnab : ¬ IsMulCommutative (⊤ : Subgroup (MulAut V)) :=
    GoldVariant.not_isMulCommutative_of_card (by rw [Subgroup.card_top, hcard])
  have hΩmin : ∀ R : Subgroup (MulAut V), R.Normal → R ≠ ⊥ → (⊤ : Subgroup (MulAut V)) ≤ R :=
    fun R _ hne => ((IsSimpleGroup.eq_bot_or_eq_top_of_normal R).resolve_left hne).ge
  have hQB1' : ∀ U : Subgroup X, U ≤ V →
      Subgroup.normalizer (V : Set X) ≤ Subgroup.normalizer (U : Set X) → U = ⊥ ∨ U = V := by
    intro U hUV hNU
    rcases eq_or_ne U ⊥ with h | h
    · exact Or.inl h
    right
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
    refine le_antisymm hUV fun w hw => ?_
    by_cases hw1 : w = 1
    · rw [hw1]
      exact U.one_mem
    have hu1' : (u : X) ≠ 1 := fun e => hu1 (Subtype.ext e)
    obtain ⟨n, hn, hnw⟩ := htrans u (hUV u.2) w hw hu1' hw1
    rw [← hnw]
    exact (Subgroup.mem_normalizer_iff.1 (hNU hn) u).1 u.2
  have hAr : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.goldschmidtSimpleType L →
      Nat.card (⊤ : Subgroup (MulAut V)) ∣ Nat.card L → Nat.card L ∣ Nat.card X →
        ∃ f : ℕ, 2 ≤ f ∧ Nat.card V < 2 ^ f ∧ Nonempty (L ≃* PSL(2, GaloisField 2 f)) := by
    intro L _ _ hL hΩL hLX
    rw [Subgroup.card_top, hcard] at hΩL
    have h17 : (Nat.card L).factorization 2 ≤ 17 :=
      ((Nat.factorization_le_iff_dvd (Nat.card_pos (α := L)).ne'
        (Nat.card_pos (α := X)).ne').2 hLX 2).trans hX
    obtain ⟨f, hf, he⟩ := GoldVariant.psl2_of_goldschmidtSimpleType hL
      ((by norm_num : 2 ^ 6 * 3 * 5 * 7 ∣ 20160).trans hΩL) h17
    refine ⟨f, by omega, ?_, he⟩
    rw [hV16]
    calc 16 < 2 ^ 6 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact normal_of_goldschmidt_conclusion_of_psl2 S hVS hGold hclosed hO hC2 hQB1' ρ hρ hker ⊤
    hΩ hΩnab hΩmin hAr

end CFSG.RankThree.Co2
