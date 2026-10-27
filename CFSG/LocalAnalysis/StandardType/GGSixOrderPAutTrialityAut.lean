module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KG
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofOut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RankXTriality
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalGraphPlus
public import CFSG.Monster.B.TwoA.Sp8.A8

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.StandardType.Triality

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

namespace OrdPTri

section Transport

variable {Γ G : Type} [Group Γ] [Group G] {G₀ : Subgroup G} {ι : Γ →* G}

@[expose] noncomputable def embEquiv (hinj : Function.Injective ι) (hrange : ι.range = G₀) :
    Γ ≃* G₀ :=
  (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)

theorem coe_embEquiv (hinj : Function.Injective ι) (hrange : ι.range = G₀) (x : Γ) :
    ((embEquiv hinj hrange x : G₀) : G) = ι x := by
  simp [embEquiv, MonoidHom.ofInjective_apply]

theorem coe_embEquiv_symm (hinj : Function.Injective ι) (hrange : ι.range = G₀) (z : G₀) :
    ι ((embEquiv hinj hrange).symm z) = z := by
  rw [← coe_embEquiv hinj hrange, MulEquiv.apply_symm_apply]

@[expose] noncomputable def autHom (hinj : Function.Injective ι) (hrange : ι.range = G₀) :
    Subgroup.normalizer (G₀ : Set G) →* MulAut Γ :=
  (MulAut.congr (embEquiv hinj hrange).symm).toMonoidHom.comp G₀.normalizerMonoidHom

theorem autHom_apply (hinj : Function.Injective ι) (hrange : ι.range = G₀)
    (m : Subgroup.normalizer (G₀ : Set G)) (x : Γ) :
    ι (autHom hinj hrange m x) = (m : G) * ι x * (m : G)⁻¹ := by
  change ι ((embEquiv hinj hrange).symm (G₀.normalizerMonoidHom m
    ((embEquiv hinj hrange).symm.symm x))) = _
  rw [coe_embEquiv_symm, MulEquiv.symm_symm]
  change ((SMul.smul m (embEquiv hinj hrange x) : G₀) : G) = _
  rw [Subgroup.smul_coe, coe_embEquiv]
  rfl

theorem autHom_injective (hinj : Function.Injective ι) (hrange : ι.range = G₀)
    (hC : Subgroup.centralizer (G₀ : Set G) = ⊥) : Function.Injective (autHom hinj hrange) := by
  rw [injective_iff_map_eq_one]
  intro m hm
  have hcen : (m : G) ∈ Subgroup.centralizer (G₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' : g ∈ ι.range := by rw [hrange]; exact hg
    obtain ⟨x, rfl⟩ := hg'
    have h := autHom_apply hinj hrange m x
    rw [hm, MulAut.one_apply] at h
    calc ι x * (m : G) = ((m : G) * ι x * (m : G)⁻¹) * m := by rw [← h]
      _ = (m : G) * ι x := by group
  rw [hC, Subgroup.mem_bot] at hcen
  exact Subtype.ext hcen

theorem mem_of_autHom_mem_inner (hinj : Function.Injective ι) (hrange : ι.range = G₀)
    (hC : Subgroup.centralizer (G₀ : Set G) = ⊥) {m : Subgroup.normalizer (G₀ : Set G)}
    (h : autHom hinj hrange m ∈ Inn Γ) : (m : G) ∈ G₀ := by
  have h1 := L613KG.mem_range_of_mulAut_mem_inner (by rw [hrange]; exact hC)
    (autHom_apply hinj hrange m) h
  rwa [hrange] at h1

theorem autHom_mem_inner_of_mem (hinj : Function.Injective ι) (hrange : ι.range = G₀)
    {m : Subgroup.normalizer (G₀ : Set G)} (h : (m : G) ∈ G₀) :
    autHom hinj hrange m ∈ Inn Γ :=
  L613KG.mulAut_mem_inner_of_mem_range hinj (autHom_apply hinj hrange m) (by rw [hrange]; exact h)

theorem autHom_apply_eq_iff (hinj : Function.Injective ι) (hrange : ι.range = G₀)
    (m : Subgroup.normalizer (G₀ : Set G)) (x : Γ) :
    autHom hinj hrange m x = x ↔ (m : G) * ι x = ι x * m :=
  L613KG.mulAut_apply_eq_iff hinj (autHom_apply hinj hrange m) x

theorem map_ggFix (hinj : Function.Injective ι) (hrange : ι.range = G₀)
    (m : Subgroup.normalizer (G₀ : Set G)) :
    (ggFix (autHom hinj hrange m)).map ι = G₀ ⊓ Subgroup.centralizer {(m : G)} := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨by rw [← hrange]; exact ⟨x, rfl⟩, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((autHom_apply_eq_iff hinj hrange m x).mp hx).symm
  · rintro ⟨hg, hgc⟩
    have hg' : g ∈ ι.range := by rw [hrange]; exact hg
    obtain ⟨x, rfl⟩ := hg'
    exact ⟨x, (autHom_apply_eq_iff hinj hrange m x).mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hgc).symm, rfl⟩

end Transport

section Layer

variable {G : Type} [Group G]

theorem exists_orderOf_eq_of_embeds {G₀ : Subgroup G}
    (hperf : ∀ X : Subgroup G, X ≤ Subgroup.normalizer (G₀ : Set G) → ⁅X, X⁆ = X → X ≤ G₀)
    {y b : G} (hemb : GGCentralizerEmbeds (Subgroup.normalizer (G₀ : Set G)) y b) {x : G}
    (hx : x ∈ LargeEvenLayer (G₀ ⊓ Subgroup.centralizer {y})) :
    ∃ w ∈ G₀ ⊓ Subgroup.centralizer {b}, orderOf w = orderOf x := by
  obtain ⟨θ, hθinj, hθM, -⟩ := hemb
  set Y := LargeEvenLayer (G₀ ⊓ Subgroup.centralizer {y}) with hYdef
  have hYle : Y ≤ G₀ ⊓ Subgroup.centralizer {y} := LayerCC.largeEvenLayer_le _
  have hYM : Y ≤ Subgroup.normalizer (G₀ : Set G) ⊓ Subgroup.centralizer {y} :=
    hYle.trans (inf_le_inf_right _ Subgroup.le_normalizer)
  set θ' : ↥Y →* G := θ.comp (Subgroup.inclusion hYM) with hθ'
  have hθ'inj : Function.Injective θ' := hθinj.comp (Subgroup.inclusion_injective hYM)
  have hYp : ⁅Y, Y⁆ = Y := LayerCC.commutator_largeEvenLayer _
  have htop : ⁅(⊤ : Subgroup ↥Y), (⊤ : Subgroup ↥Y)⁆ = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hYp]
  have hRp : ⁅θ'.range, θ'.range⁆ = θ'.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  have hRM : θ'.range ≤ Subgroup.normalizer (G₀ : Set G) := by
    rintro _ ⟨c, rfl⟩
    exact (hθM _).1
  have hRG₀ := hperf _ hRM hRp
  refine ⟨θ' ⟨x, hx⟩, ⟨hRG₀ ⟨_, rfl⟩, (hθM _).2⟩, ?_⟩
  rw [orderOf_injective θ' hθ'inj, Subgroup.orderOf_mk]

variable {Γ : Type} [Group Γ] {ι : Γ →* G}

theorem map_mem_layer (hinj : Function.Injective ι) {H : Subgroup Γ} {H' : Subgroup G}
    (hmap : H.map ι = H') {x : Γ} (hx : x ∈ LargeEvenLayer H) : ι x ∈ LargeEvenLayer H' := by
  rw [← hmap, largeEvenLayer_map_of_injective ι hinj]
  exact ⟨x, hx, rfl⟩

theorem lieModel_layer_of_map (hinj : Function.Injective ι) {H : Subgroup Γ} {H' : Subgroup G}
    (hmap : H.map ι = H') {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel (↥(LargeEvenLayer H) ⧸ Subgroup.center ↥(LargeEvenLayer H)) t n p f) :
    LieModel (↥(LargeEvenLayer H') ⧸ Subgroup.center ↥(LargeEvenLayer H')) t n p f := by
  have hL : LargeEvenLayer H' = (LargeEvenLayer H).map ι := by
    rw [← hmap, largeEvenLayer_map_of_injective ι hinj]
  have e : ↥(LargeEvenLayer H) ≃* ↥(LargeEvenLayer H') :=
    ((LargeEvenLayer H).equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hL.symm)
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (L613KG.centerQuotEquiv e) h

end Layer

section Nonsplit

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem false_of_nonsplit (hTL : GGD4NonsplitTwoLocalInput)
    (hOI : GGD4NonsplitOuterInvolutionInput) (h3 : ¬ 3 ∣ Nat.card K - 1)
    {E : Subgroup (MulAut (Om8 K))} (hE : IsElemAbelian 3 E) (h81 : 81 ≤ Nat.card E)
    (hEF : ∀ e ∈ E, e ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range → e ∈ Inn (Om8 K))
    {T : Subgroup (MulAut (Om8 K))} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hET : E ≤ Subgroup.normalizer (T : Set (MulAut (Om8 K)))) : False := by
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEI : E ≤ Inn (Om8 K) := by
    intro α hαE
    by_contra hαI
    have hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range := fun h => hαI (hEF α hαE h)
    have hα3 : α ^ 3 = 1 := hE.2 α hαE
    have h1 : Nat.card E ≤ 3 * Nat.card ↥(E ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)) :=
      NbrGraphD4.card_le_three_mul hαE fun a ha =>
        NbrGraphD4.exists_mul_pow_mem_sup (hE.2 a ha) hα3 hα
    have h2 : Nat.card ↥(E ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)) ≤
        Nat.card ↥(E ⊓ Inn (Om8 K)) :=
      Subgroup.card_le_of_le fun a ha => ⟨ha.1, hEF a ha.1 ha.2⟩
    have h9 := NbrGraphD4.card_inf_inner_le_nine hE hαE hα
    omega
  set E' := E.comap (MulAut.conj : Om8 K →* MulAut (Om8 K)) with hE'def
  have hE'el : IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun u v => Subtype.ext (NbrGraphD4.conj_injective ?_)⟩⟩,
      fun γ hγ => NbrGraphD4.conj_injective ?_⟩
    · change MulAut.conj ((u : Om8 K) * v) = MulAut.conj ((v : Om8 K) * u)
      rw [map_mul, map_mul]
      exact hcomm _ u.2 _ v.2
    · rw [map_pow, map_one]
      exact hE.2 _ hγ
  have hE'card : Nat.card E' = Nat.card E := by
    have hmap : E'.map (MulAut.conj : Om8 K →* MulAut (Om8 K)) = E := by
      ext a
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        exact hγ
      · intro ha
        obtain ⟨γ, rfl⟩ := hEI ha
        exact ⟨γ, ha, rfl⟩
    rw [← hmap, Subgroup.card_map_of_injective NbrGraphD4.conj_injective]
  set T' := T.comap (MulAut.conj : Om8 K →* MulAut (Om8 K)) with hT'def
  have hT'2 : IsPGroup 2 T' := hT.comap_of_injective _ NbrGraphD4.conj_injective
  have hE'T' : E' ≤ Subgroup.normalizer (T' : Set (Om8 K)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro t
    change MulAut.conj t ∈ T ↔ MulAut.conj (g * t * g⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp (hET hg) (MulAut.conj t)
  have hT'bot : T' = ⊥ := hTL K h3 E' hE'el (hE'card ▸ h81) T' hT'2 hE'T'
  have hTI : ∀ c ∈ T, c ∈ Inn (Om8 K) → c = 1 := by
    rintro c hcT ⟨γ, rfl⟩
    have hγ : γ ∈ T' := hcT
    rw [hT'bot, Subgroup.mem_bot] at hγ
    rw [hγ, map_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (Om8 K)) :=
    Finite.of_injective (fun e : MulAut (Om8 K) => (e : Om8 K → Om8 K)) DFunLike.coe_injective
  have h2T : 2 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := hT.exists_card_eq
    rcases n with _ | n
    · exact absurd (Subgroup.eq_bot_of_card_eq T (by rw [hn, pow_zero])) hT1
    · rw [hn, pow_succ]
      exact Dvd.intro_left _ rfl
  obtain ⟨t, ht2⟩ := exists_prime_orderOf_dvd_card' 2 h2T
  have ht1 : (t : MulAut (Om8 K)) ≠ 1 := by
    intro h
    have h' : t = 1 := Subtype.ext h
    rw [h', orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have htI : (t : MulAut (Om8 K)) ∉ Inn (Om8 K) := fun h => ht1 (hTI t t.2 h)
  have ht2' : t ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [ht2])
  have htsq : (t : MulAut (Om8 K)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ht2', Subgroup.coe_one]
  have hEt : ∀ e ∈ E, e * t = t * e := by
    intro e he
    have hmemT : e * t * e⁻¹ * (t : MulAut (Om8 K))⁻¹ ∈ T :=
      T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hET he) t).mp t.2) (T.inv_mem t.2)
    have hmemI : e * t * e⁻¹ * (t : MulAut (Om8 K))⁻¹ ∈ Inn (Om8 K) := by
      have h1 : (t : MulAut (Om8 K)) * e⁻¹ * (t : MulAut (Om8 K))⁻¹ ∈ Inn (Om8 K) :=
        (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal (Om8 K)).conj_mem _
          (inv_mem (hEI he)) _
      have h2 := mul_mem (hEI he) h1
      rwa [show e * (t * e⁻¹ * (t : MulAut (Om8 K))⁻¹) =
        e * t * e⁻¹ * (t : MulAut (Om8 K))⁻¹ by group] at h2
    have h1 := hTI _ hmemT hmemI
    calc e * t = (e * t * e⁻¹ * (t : MulAut (Om8 K))⁻¹) * (t * e) := by group
      _ = t * e := by rw [h1, one_mul]
  obtain ⟨g, hgE', hg⟩ :=
    hOI K h3 E' hE'el (hE'card ▸ h81) (t : MulAut (Om8 K)) htsq htI
  apply hg
  apply NbrGraphD4.conj_injective
  have h1 := hEt _ hgE'
  rw [D4Rank.mulAut_mul_conj] at h1
  exact mul_right_cancel h1.symm

end Nonsplit

section Psi

variable {G : Type} [Group G]

theorem ggPsiDiagField_of_mem_sup {f : ℕ} {ψ : (ggU .POmegaPlus 4 f).K →* G}
    {ι : Om8 (GaloisField 2 f) →* G} (hιψ : ∀ u : Sp8 (GaloisField 2 f), ι (model8 u) = ψ u)
    {y : G} {β : MulAut (Om8 (GaloisField 2 f))} (hβ : ∀ x, ι (β x) = y * ι x * y⁻¹)
    (hmem : β ∈ Inn (Om8 (GaloisField 2 f)) ⊔ (AutOm.fieldAutP 4).range) :
    GGPsiDiagField (ggU .POmegaPlus 4 f).D ψ y := by
  obtain ⟨_, ⟨h, rfl⟩, _, ⟨τ, rfl⟩, hβe⟩ := Subgroup.mem_sup_of_normal_left.1 hmem
  set h' := AutOm.fieldAutP 4 τ⁻¹ h⁻¹ with hh'
  have hinv : β⁻¹ = MulAut.conj h' * AutOm.fieldAutP 4 τ⁻¹ := by
    rw [← hβe, mul_inv_rev, ← map_inv (AutOm.fieldAutP 4) τ, ← map_inv MulAut.conj h,
    D4Rank.mulAut_mul_conj]
  have hβinv : ∀ x, y⁻¹ * ι x * y = ι (β⁻¹ x) := fun x => by
    have h1 := hβ (β⁻¹ x)
    rw [MulAut.apply_inv_self] at h1
    rw [h1]
    group
  obtain ⟨g, hg⟩ := OrdPGraphOmega.modelDiagField_plus three_le_four h' τ⁻¹
  refine ⟨ι g, ?_, fun γ hγ z hz => ?_⟩
  · obtain ⟨u, rfl⟩ := AutOm.spinModelPlus_surjective three_le_four g
    exact ⟨u, (hιψ u).symm⟩
  · obtain ⟨z', hz', e⟩ := hg γ hγ z hz
    refine ⟨z', hz', ?_⟩
    have e' := congrArg ι e
    rw [← hinv, map_mul, map_mul, map_inv, ← hβinv] at e'
    rw [← hιψ z, ← hιψ z']
    change _ = ι (AutOm.spinModelPlus three_le_four z')
    rw [← e']
    group

theorem mem_of_ggPsiInnerDiag [Finite G] {f : ℕ} {G₀ : Subgroup G}
    {ψ : (ggU .POmegaPlus 4 f).K →* G}
    (hpres : GGPresentsG0 G₀ (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ)
    (hC : Subgroup.centralizer (G₀ : Set G) = ⊥) {c : G}
    (hc : c ∈ Subgroup.normalizer (G₀ : Set G))
    (hd : GGPsiInnerDiag (ggU .POmegaPlus 4 f).D ψ c) : c ∈ G₀ := by
  obtain ⟨g, hg, hcg⟩ := ggPsiDiagInner_POmegaPlus G 4 f ψ G₀ hpres c hc hd
  rw [hC, Subgroup.mem_bot] at hcg
  rw [eq_inv_of_mul_eq_one_left hcg]
  exact G₀.inv_mem hg

end Psi

end OrdPTri

end CFSG.StandardType
