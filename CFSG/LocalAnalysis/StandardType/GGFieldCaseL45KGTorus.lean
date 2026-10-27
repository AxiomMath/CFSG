module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGLabel
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneRankXAbs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.kg_package
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hraw : GGRawInnFieldInput) (hisoI : GGRawInndiagIsoInput) (hsub : GGNbrSubcomponentInput)
    (hgr : GGNbrGraphInput) (hD4 : GGL45D4BstarProperInput) (hnone : GGL44iiiTriD4NoneInput)
    (hStdL : GGTriD4StdSubInput) (hE6 : GGTwE6LocalRankInput) (hT : GGStdSubNotTorsionInput)
    (hK : GGL45KnownForms) (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) :
    ∃ (R : Type) (_ : Group R) (I : Set (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R),
      (∀ r : R, MulAut.conj r ∈ I) ∧
      (∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
        (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I)) ∧
      GGL45TorusPackage p I θ (K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)
        (ggL45KgE K _ hcfg.kg_B1N) := by
  have hp := hcfg.prime
  have hp2 := hcfg.odd
  have hcent := hcfg.cent_le_of_iOne hsub hI1
  obtain ⟨hB₁U₁, hxU₁, -⟩ := ggL4546_basic hraw hisoI hcfg
  obtain ⟨lab, hmk, R, _, I, F, θ, hs, hna, hRIF, ⟨hP'lab, hfix⟩, ⟨hgrθ, hnoneθ⟩, hB₁I,
      ⟨f, hf, u, hu, hord, hxind⟩, hiff⟩ :=
    ggL45_exists_marking_labQ
      (P' := fun lab R _ I F =>
        (GGL45KGLabel p lab → GGL45TorusKGRaw p lab R I F) ∧ GGL45FieldFixKGRaw p lab R I F)
      (fun lab hl => largeEvenLabelAll_and
        (by
          by_cases hKG : GGL45KGLabel p lab
          · exact ggL45_labelAll_mono (hK.1 p hp hp2 lab hl hKG) fun _ _ _ _ h _ => h
          · exact ggL45_labelAll_mono (largeEvenLabelAll_true lab) fun _ _ _ _ _ h => absurd h hKG)
        (hK.2 p hp hp2 lab hl))
      (hcfg.kg_markingAll hgr hnone) hraw hisoI hcfg
  obtain ⟨-, hinv, hinn, -⟩ := hRIF hs hna
  have hKperf : commutator K = ⊤ := hmk.1
  have hψ : ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧ LargeEvenInduces θ
      (fun k k' => k' = K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩ k) (u * f * u⁻¹) :=
    ⟨f, hf, u, hu, hord, (induces_inv_iff K θ hcfg.kg_xN _).mp hxind⟩
  have hxI : ggLAut K θ ⟨x, hcfg.kg_xN⟩ ∉ I := fun h =>
    hxU₁ ((hiff x (hcfg.bs_le hcfg.x_mem) hcfg.kg_xN).mpr h)
  have htor : ¬ GGL45TorsionTag lab := hcfg.kg_not_torsion hsub hT θ hKperf hfix hψ
  have hD : ¬ (lab.tag = .triD4 ∧ p = 3) := fun h =>
    hnoneθ h hgrθ (fun b hb => (ggL45_exists_induces_iff hinv _).mp (hB₁I b hb))
      ⟨x, hcfg.x_mem, hxI⟩
  have hKG : GGL45KGLabel p lab := by
    refine ⟨Or.inl fun h => htor (Or.inl h), ?_⟩
    by_cases h3 : p = 3
    · exact Or.inl ⟨fun h => htor (Or.inr (Or.inl h)), fun h => htor (Or.inr (Or.inr (Or.inl h))),
        fun h => htor (Or.inr (Or.inr (Or.inr h))), fun h => hD ⟨h, h3⟩⟩
    · exact Or.inr h3
  refine ⟨R, inferInstance, I, θ, hinn, hiff, hP'lab hKG (↥K) θ hKperf
    (fun hA2 hp3 => hcfg.kg_A2_center hsub hStdL hE6 θ hKperf hfix hψ hA2 hp3) _ _
    hcfg.kg_psi_pow hψ hcfg.kg_E_elemAbelian
    (hcfg.kg_sq_le_card_E hcent) ?_ (hcfg.kg_E_inducesIn θ hB₁I) hcfg.kg_E_comm
    (hcfg.kg_sat θ hinn hB₁U₁ hxU₁ hiff) (hcfg.kg_rk θ hinn hxI hcent) hcfg.kg_pi⟩
  intro ht hr hp3
  subst hp3
  exact hcfg.kg_card_E_d4 hcent (hcfg.pow_five_le_card_bstar
    (hD4 G 3 B Bs x L D J X B₂ d y K U U₁ hcfg rfl (largeEvenMarking_mono
      (fun lab' _ _ _ _ _ heq => by subst heq; exact ⟨ht, hr⟩) hmk)))

theorem ggL45IsPElt_coe {S : Subgroup G} (h : S) : GGL45IsPElt p h ↔ GGL45IsPElt p (h : G) := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem GGL45Config.kg_inP
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I)) {b : G} (hb : b ∈ U₁) :
    GGL45InP p θ I (ggL45KgE K _ hcfg.kg_B1N)
      (K.normalizerMonoidHom ⟨b, hcfg.le_normalizer (hcfg.part_le hb)⟩) := by
  have hbU := hcfg.part_le hb
  refine ⟨?_, fun e he => ?_, (ggL45_inducesIn_rhoK_iff K θ I _).mpr ((hiff b hbU _).mp hb)⟩
  · obtain ⟨k, hk⟩ := hcfg.isPGroup ⟨b, hbU⟩
    refine ⟨k, ?_⟩
    have : (⟨b, hcfg.le_normalizer hbU⟩ : Subgroup.normalizer (K : Set G)) ^ p ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [← map_pow, this, map_one]
  · obtain ⟨c, hc, hcN, rfl⟩ := mem_ggL45KgE.mp he
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hcfg.le_centralizer hbU) c hc).symm

theorem GGL45Config.kg_S_mem
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I))
    (hmul : ∀ h t : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
      GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) t →
      GGL45IsPElt p (h * t))
    {a : K} (ha : GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a) : (a : G) ∈ U₁ := by
  set E := ggL45KgE K _ hcfg.kg_B1N
  have hfix : ∀ h : K, (∀ e ∈ E, e h = h) ↔
      ∀ c ∈ Bs ⊓ Subgroup.centralizer (X : Set G), c * h = (h : G) * c := by
    intro h
    constructor
    · intro hh c hc
      exact (ggL45_rhoK_fix_iff (hcfg.kg_B1N hc) h).mp (hh _ (mem_ggL45KgE.mpr ⟨c, hc, _, rfl⟩))
    · intro hh e he
      obtain ⟨c, hc, hcN, rfl⟩ := mem_ggL45KgE.mp he
      exact (ggL45_rhoK_fix_iff hcN h).mpr (hh c hc)
  let Sg : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ K, GGL45InS p E ⟨g, hg⟩}
      mul_mem' := by
        rintro g₁ g₂ ⟨hg₁, h₁⟩ ⟨hg₂, h₂⟩
        refine ⟨K.mul_mem hg₁ hg₂, hmul _ _ h₁ h₂, fun e he => ?_⟩
        show e (⟨g₁, hg₁⟩ * ⟨g₂, hg₂⟩) = ⟨g₁, hg₁⟩ * ⟨g₂, hg₂⟩
        rw [map_mul, h₁.2 e he, h₂.2 e he]
      one_mem' := ⟨K.one_mem, ⟨0, by simp⟩, fun e _ => map_one e⟩
      inv_mem' := by
        rintro g ⟨hg, ⟨k, hk⟩, hfx⟩
        refine ⟨K.inv_mem hg, ⟨k, ?_⟩, fun e he => ?_⟩
        · show (⟨g, hg⟩⁻¹ : K) ^ p ^ k = 1
          rw [inv_pow, hk, inv_one]
        · show e (⟨g, hg⟩⁻¹ : K) = ⟨g, hg⟩⁻¹
          rw [map_inv, hfx e he] }
  have hSgp : IsPGroup p Sg := by
    rintro ⟨g, hg, ⟨k, hk⟩, -⟩
    refine ⟨k, Subtype.ext ?_⟩
    simpa using congrArg Subtype.val hk
  have hconj : ∀ u ∈ U, ∀ g ∈ Sg, u * g * u⁻¹ ∈ Sg := by
    rintro u hu g ⟨hg, hpe, hfx⟩
    have hugK : u * g * u⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hcfg.le_normalizer hu) g).mp hg
    refine ⟨hugK, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := (ggL45IsPElt_coe (p := p) (⟨g, hg⟩ : K)).mp hpe
      refine (ggL45IsPElt_coe (p := p) (⟨_, hugK⟩ : K)).mpr ⟨k, ?_⟩
      show (u * g * u⁻¹) ^ p ^ k = 1
      rw [conj_pow, hk]
      group
    · refine (hfix _).mpr fun c hc => ?_
      have hcu : c * u = u * c :=
        Subgroup.mem_centralizer_iff.mp (hcfg.le_centralizer hu) c hc
      have hcg : c * g = g * c := (hfix _).mp hfx c hc
      show c * (u * g * u⁻¹) = u * g * u⁻¹ * c
      have hcu' : c * u⁻¹ = u⁻¹ * c := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, hcu, ← mul_assoc, inv_mul_cancel, one_mul]
      calc c * (u * g * u⁻¹) = u * (c * g) * u⁻¹ := by
            rw [← mul_assoc, ← mul_assoc, hcu, mul_assoc u c g]
        _ = u * g * (c * u⁻¹) := by rw [hcg]; group
        _ = u * g * u⁻¹ * c := by rw [hcu']; group
  have hUN : U ≤ Subgroup.normalizer (Sg : Set G) := fun u hu =>
    Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => hconj u hu g hg, fun hg => by
      have := hconj u⁻¹ (U.inv_mem hu) _ hg
      simpa [mul_assoc] using this⟩
  have hQp : IsPGroup p (U ⊔ Sg : Subgroup G) :=
    hcfg.isPGroup.to_sup_of_normal_right' hSgp hUN
  have hQC : (U ⊔ Sg : Subgroup G) ≤ Subgroup.centralizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
    refine sup_le hcfg.le_centralizer fun g hg => ?_
    obtain ⟨hgK, -, hfx⟩ := hg
    exact Subgroup.mem_centralizer_iff.mpr fun c hc => (hfix _).mp hfx c hc
  have hQ := hcfg.2.2.2.2.2.2.1.2.2.1 _ hQC hQp le_sup_left
  have haU : (a : G) ∈ U := hQ ▸ (le_sup_right : Sg ≤ U ⊔ Sg) ⟨a.2, ha⟩
  exact (hiff a haU (Subgroup.le_normalizer a.2)).mpr (by rw [ggLAut_mk_self K θ a]; exact hinn _)

theorem coe_comm_psi {x : G} (hxN : x ∈ Subgroup.normalizer (K : Set G)) (a : K) :
    ((a * ((K.normalizerMonoidHom ⟨x⁻¹, inv_mem hxN⟩)⁻¹ a)⁻¹ : K) : G) =
      (a : G) * x * (a : G)⁻¹ * x⁻¹ := by
  have : (K.normalizerMonoidHom ⟨x⁻¹, inv_mem hxN⟩)⁻¹ = K.normalizerMonoidHom ⟨x, hxN⟩ := by
    rw [← map_inv]
    congr 1
    exact Subtype.ext (by simp)
  rw [this, Subgroup.coe_mul, Subgroup.coe_inv, ggL45_rhoK_coe]
  group

theorem GGL45Config.kg_rankXAbs
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I))
    (hpk : GGL45TorusPackage p I θ (K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)
      (ggL45KgE K _ hcfg.kg_B1N)) :
    ∃ a₁ ∈ U₁, ∃ a₂ ∈ U₁, (∀ b ∈ U₁, a₁ * b = b * a₁) ∧ (∀ b ∈ U₁, a₂ * b = b * a₂) ∧
      (a₁ * x * a₁⁻¹ * x⁻¹) ^ p = 1 ∧ (a₂ * x * a₂⁻¹ * x⁻¹) ^ p = 1 ∧
      a₁ * x * a₁⁻¹ * x⁻¹ ∉ U ⊓ Subgroup.centralizer (K : Set G) ∧
      ∀ i j : ℕ, (a₁ * x * a₁⁻¹ * x⁻¹) ^ i * (a₂ * x * a₂⁻¹ * x⁻¹) ^ j = 1 → p ∣ i ∧ p ∣ j := by
  obtain ⟨s, -, k, -, -, -, hP2m, -, -, hP2f, ⟨a₁, a₂, ha₁, ha₂, hb₁p, hb₂p, hb₁c, hind⟩, -⟩ :=
    hpk
  have hmul : ∀ h t : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
      GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) t →
      GGL45IsPElt p (h * t) := fun h t hh ht => (hP2m h t hh ht).2
  have hcent : ∀ a : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a →
      ∀ b ∈ U₁, (a : G) * b = b * a := by
    intro a ha b hb
    have := hP2f _ (hcfg.kg_inP θ hiff hb) a ha
    exact ((ggL45_rhoK_fix_iff _ a).mp this).symm
  have hc := coe_comm_psi (K := K) hcfg.kg_xN
  refine ⟨a₁, hcfg.kg_S_mem θ hinn hiff hmul ha₁, a₂, hcfg.kg_S_mem θ hinn hiff hmul ha₂,
    hcent a₁ ha₁, hcent a₂ ha₂, ?_, ?_, fun h => hb₁c ?_, fun i j hij => hind i j ?_⟩
  · rw [← hc a₁, ← Subgroup.coe_pow, hb₁p, Subgroup.coe_one]
  · rw [← hc a₂, ← Subgroup.coe_pow, hb₂p, Subgroup.coe_one]
  · refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    have := Subgroup.mem_centralizer_iff.mp h.2 g g.2
    rw [← hc a₁] at this
    exact this
  · refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hc a₁, hc a₂, hij,
      Subgroup.coe_one]

theorem GGL45Config.kg_torus
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I))
    (hpk : GGL45TorusPackage p I θ (K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)
      (ggL45KgE K _ hcfg.kg_B1N)) :
    ∃ s : ℕ, 2 ≤ s ∧
      (∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G)) ∧
      (∀ u ∈ U₁, u ^ p ^ s ∈ U ⊓ Subgroup.centralizer (K : Set G)) ∧
      (∃ u ∈ U₁, u ^ p ^ (s - 1) ∉ U ⊓ Subgroup.centralizer (K : Set G)) ∧
      ∃ x' : G, Subgroup.zpowers x' = Subgroup.zpowers x ∧
        ∀ u ∈ U₁, (u ^ (1 + p ^ (s - 1)))⁻¹ * (x'⁻¹ * u * x') ∈
          U ⊓ Subgroup.centralizer (K : Set G) := by
  obtain ⟨a₁, ha₁, -, -, -, -, -, -, ha₁x, -⟩ := hcfg.kg_rankXAbs θ hinn hiff hpk
  obtain ⟨s, -, k, -, hP1c, hP1p, -⟩ := hpk
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have hUK := hcfg.le_normalizer
  have hU₁U := hcfg.part_le
  refine hcfg.torus_of_pow (fun a ha b hb => ?_) ⟨1 + p ^ (s - 1) * k, fun u hu => ?_⟩ ha₁ ha₁x
  · have hw : a * b * a⁻¹ * b⁻¹ ∈ U :=
      U.mul_mem (U.mul_mem (U.mul_mem (hU₁U ha) (hU₁U hb)) (U.inv_mem (hU₁U ha)))
        (U.inv_mem (hU₁U hb))
    refine ⟨hw, (ggL45_rhoK_eq_one_iff K ⟨_, hUK hw⟩).mp ?_⟩
    have e : (⟨a * b * a⁻¹ * b⁻¹, hUK hw⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨a, hUK (hU₁U ha)⟩ * ⟨b, hUK (hU₁U hb)⟩ * (⟨a, hUK (hU₁U ha)⟩)⁻¹ *
          (⟨b, hUK (hU₁U hb)⟩)⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv,
      hP1c _ _ (hcfg.kg_inP θ hiff ha) (hcfg.kg_inP θ hiff hb)]
    group
  · have hxu : x⁻¹ * u * x ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hxU) (hU₁U hu)) hxU
    have hw : (u ^ (1 + p ^ (s - 1) * k))⁻¹ * (x⁻¹ * u * x) ∈ U :=
      U.mul_mem (U.inv_mem (U.pow_mem (hU₁U hu) _)) hxu
    refine ⟨hw, (ggL45_rhoK_eq_one_iff K ⟨_, hUK hw⟩).mp ?_⟩
    have e : (⟨(u ^ (1 + p ^ (s - 1) * k))⁻¹ * (x⁻¹ * u * x), hUK hw⟩ :
        Subgroup.normalizer (K : Set G)) =
        (⟨u, hUK (hU₁U hu)⟩ ^ (1 + p ^ (s - 1) * k))⁻¹ *
          (⟨x⁻¹, inv_mem hcfg.kg_xN⟩ * ⟨u, hUK (hU₁U hu)⟩ *
            (⟨x⁻¹, inv_mem hcfg.kg_xN⟩ : Subgroup.normalizer (K : Set G))⁻¹) :=
      Subtype.ext (by simp)
    rw [e, map_mul, map_inv, map_pow, map_mul, map_mul, map_inv,
      hP1p _ (hcfg.kg_inP θ hiff hu), inv_mul_cancel]

end Config

theorem ggL45RankXAbsIOneInput_of_known (hraw : GGRawInnFieldInput)
    (hisoI : GGRawInndiagIsoInput) (hsub : GGNbrSubcomponentInput) (hgr : GGNbrGraphInput)
    (hD4 : GGL45D4BstarProperInput) (hnone : GGL44iiiTriD4NoneInput)
    (hStdL : GGTriD4StdSubInput) (hE6 : GGTwE6LocalRankInput) (hT : GGStdSubNotTorsionInput)
    (hK : GGL45KnownForms) : GGL45RankXAbsIOneInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg hI1
  obtain ⟨R, _, I, θ, hinn, hiff, hpk⟩ :=
    hcfg.kg_package hraw hisoI hsub hgr hD4 hnone hStdL hE6 hT hK hI1
  exact hcfg.kg_rankXAbs θ hinn hiff hpk

theorem ggL45TorusIOneInput_of_known (hraw : GGRawInnFieldInput)
    (hisoI : GGRawInndiagIsoInput) (hsub : GGNbrSubcomponentInput) (hgr : GGNbrGraphInput)
    (hD4 : GGL45D4BstarProperInput) (hnone : GGL44iiiTriD4NoneInput)
    (hStdL : GGTriD4StdSubInput) (hE6 : GGTwE6LocalRankInput) (hT : GGStdSubNotTorsionInput)
    (hK : GGL45KnownForms) : GGL45TorusIOneInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg hI1
  obtain ⟨R, _, I, θ, hinn, hiff, hpk⟩ :=
    hcfg.kg_package hraw hisoI hsub hgr hD4 hnone hStdL hE6 hT hK hI1
  exact hcfg.kg_torus θ hinn hiff hpk

end CFSG.StandardType
