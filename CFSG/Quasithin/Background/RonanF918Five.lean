module

public import CFSG.Quasithin.Background.F918Z5ATensor
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.RonanF918Four
public import CFSG.Quasithin.Background.RonanF918Nat

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped Pointwise commutatorElement

@[expose] def IsF918FiveListU (Ks : Type) [Group Ks] : Prop :=
  (∃ n : ℕ, LieModel Ks .PSL 2 2 n) ∨ (∃ n : ℕ, LieModel Ks .twistedB2 0 2 n) ∨
    Nonempty (Ks ≃* alternatingGroup (Fin 5)) ∨ LieModel Ks .PSL 3 2 1

theorem isF918FiveListU_of_fiveShape {X : Type} [Group X] (h : FiveShape X) : IsF918FiveListU X := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | h | h
  · exact Or.inl ⟨n, lieModel_of_isPSL h⟩
  · exact Or.inr (Or.inl ⟨n, lieModel_of_isSz h⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (lieModel_of_isPSL h)))

theorem charP_two_of_card_pow_two {F : Type} [Field F] [Finite F] {n : ℕ}
    (h : Nat.card F = 2 ^ n) : CharP F 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem isPSL_two_equiv_statedSL {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (X ≃* ↥(StatedSL 2 F)) := by
  obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := h
  haveI : CharP F 2 := charP_two_of_card_pow_two hcard
  refine ⟨F, hF, hFin, hcard, ⟨e.trans ?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot).trans QuotientGroup.quotientBot

theorem units_eq_one_of_card_two {F : Type} [Field F] (hF : Nat.card F = 2) (c : Fˣ) : c = 1 := by
  have h1 : Nat.card Fˣ = 1 := by
    rw [Nat.card_units, hF]
  obtain ⟨hu⟩ := Nat.card_eq_one_iff_unique.mp h1
  exact hu.elim c 1

theorem statedScalars_subgroupOf_statedSL_eq_bot_of_card_two {F : Type} [Field F]
    (hF : Nat.card F = 2) (n : ℕ) :
    (StatedScalars (Fin n) F).subgroupOf (StatedSL n F) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, units_eq_one_of_card_two hF c, map_one]
  rfl

theorem isPSL_three_equiv_statedSL_zmod_two {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Nonempty (X ≃* ↥(StatedSL 3 (ZMod 2))) := by
  obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := h
  rw [pow_one] at hcard
  have e2 : F ≃+* ZMod 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact (ZMod.ringEquivOfPrime F Nat.prime_two (by rw [← Nat.card_eq_fintype_card, hcard])).symm
  refine ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq
    (statedScalars_subgroupOf_statedSL_eq_bot_of_card_two hcard 3)).trans
      (QuotientGroup.quotientBot.trans (statedSLMapEquiv 3 e2)))⟩

section Tilde

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem modelOnU_tilde_of_realizes (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G)) {D : FFModel}
    (hD : D.Realizes (autSub (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)) ⊤ ⊥) :
    ModelOnU D (tildeOf V₁ (conjClosure K T)) (tildeOf V₁ I) := by
  have hel : IsElemAbelian 2 (tildeOf V₁ I) := h.isElemAbelian_tilde_of_le hIU
  have hle : tildeOf V₁ I ≤ tildeOf V₁ (conjClosure I H) := secImg_mono (le_conjClosure I H)
  have hYA : tildeOf V₁ (conjClosure K T) ≤
      Subgroup.normalizer ((tildeOf V₁ I : Subgroup (GtOf V₁)) : Set (GtOf V₁)) :=
    secImg_le_normalizer_secImg hKI
  have hYB : tildeOf V₁ (conjClosure K T) ≤
      Subgroup.normalizer ((tildeOf V₁ (conjClosure I H) : Subgroup (GtOf V₁)) : Set (GtOf V₁)) :=
    secImg_le_normalizer_secImg (h.K₀_le_H.trans (le_normalizer_conjClosure I H))
  refine ⟨hYA, hel, ?_⟩
  obtain ⟨π, hπ⟩ := hD
  letI : CommGroup ↥(tildeOf V₁ I) := commGroupOfElemAbelian hel
  let V₀ : Subgroup ↥(tildeOf V₁ (conjClosure I H)) := subM V₁ (conjClosure I H) I
  let e : ↥V₀ ≃* ↥(tildeOf V₁ I) := Subgroup.subgroupOfEquivOfLe hle
  have hcoe : ∀ u : ↥V₀, ((e u : ↥(tildeOf V₁ I)) : GtOf V₁) =
      (((u : ↥(tildeOf V₁ (conjClosure I H))) : ↥(tildeOf V₁ (conjClosure I H))) : GtOf V₁) :=
    fun u => rfl
  have hstab : ∀ (n : GtOf V₁) (hnY : n ∈ tildeOf V₁ (conjClosure K T)),
      conjAct (tildeOf V₁ (conjClosure I H)) ⟨n, hYB hnY⟩ ∈ stabSub V₀ := by
    intro n hnY u
    show ((conjAct (tildeOf V₁ (conjClosure I H)) ⟨n, hYB hnY⟩ u : ↥(tildeOf V₁ (conjClosure I H))) :
        GtOf V₁) ∈ tildeOf V₁ I ↔ (u : GtOf V₁) ∈ tildeOf V₁ I
    rw [AutOn.coe_conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hYA hnY) (u : GtOf V₁)).symm
  have key : ∀ (n : GtOf V₁) (hnY : n ∈ tildeOf V₁ (conjClosure K T))
      (hg : conjAct (tildeOf V₁ (conjClosure I H)) ⟨n, hYB hnY⟩ ∈ stabSub V₀),
      MulAut.congr e (resHom V₀ ⟨conjAct (tildeOf V₁ (conjClosure I H)) ⟨n, hYB hnY⟩, hg⟩) =
        conjAct (tildeOf V₁ I) ⟨n, hYA hnY⟩ := by
    intro n hnY hg
    refine MulEquiv.ext fun a => Subtype.ext ?_
    show ((e (resHom V₀ ⟨_, hg⟩ (e.symm a)) : ↥(tildeOf V₁ I)) : GtOf V₁) =
      ((conjAct (tildeOf V₁ I) ⟨n, hYA hnY⟩ a : ↥(tildeOf V₁ I)) : GtOf V₁)
    rw [AutOn.coe_conjAct_apply, hcoe, resHom_apply]
    show (((conjAct (tildeOf V₁ (conjClosure I H)) ⟨n, hYB hnY⟩
      ((e.symm a : ↥V₀) : ↥(tildeOf V₁ (conjClosure I H))) : ↥(tildeOf V₁ (conjClosure I H))) :
        GtOf V₁)) = _
    rw [AutOn.coe_conjAct_apply]
    have h1 := hcoe (e.symm a)
    rw [e.apply_symm_apply] at h1
    rw [← h1]
  have hτmem : ∀ x : ↥(autSub (autIH V₁ I H (conjClosure K T)) V₀),
      (MulAut.congr e) (x : MulAut ↥V₀) ∈
        autOn (tildeOf V₁ (conjClosure K T)) (tildeOf V₁ I) := by
    rintro ⟨φ, hφ⟩
    obtain ⟨⟨g, hgst⟩, hgMp, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨⟨n, hn⟩, hnY, rfl⟩ := AutOn.mem_autOn_iff.mp hgMp
    exact AutOn.mem_autOn_iff.mpr ⟨⟨n, hYA hnY⟩, hnY, (key n hnY hgst).symm⟩
  let τ : ↥(autSub (autIH V₁ I H (conjClosure K T)) V₀) →*
      ↥(autOn (tildeOf V₁ (conjClosure K T)) (tildeOf V₁ I)) :=
    ((MulAut.congr e).toMonoidHom.comp (autSub (autIH V₁ I H (conjClosure K T)) V₀).subtype).codRestrict
      _ hτmem
  have hτs : Function.Surjective τ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨⟨n, hnA⟩, hnY, rfl⟩ := AutOn.mem_autOn_iff.mp hψ
    have hgst := hstab n hnY
    have hmem : conjAct (tildeOf V₁ (conjClosure I H)) ⟨n, hYB hnY⟩ ∈
        autIH V₁ I H (conjClosure K T) := AutOn.mem_autOn_iff.mpr ⟨⟨n, hYB hnY⟩, hnY, rfl⟩
    refine ⟨⟨resHom V₀ ⟨conjAct (tildeOf V₁ (conjClosure I H)) ⟨n, hYB hnY⟩, hgst⟩,
      mem_autSub.mpr ⟨⟨_, hgst⟩, hmem, rfl⟩⟩, Subtype.ext (key n hnY hgst)⟩
  let ρ : ↥(⊤ : Subgroup ↥V₀) →* ↥(tildeOf V₁ I) :=
    e.toMonoidHom.comp (Subgroup.topEquiv (G := ↥V₀)).toMonoidHom
  have hρs : Function.Surjective ρ := e.surjective.comp (Subgroup.topEquiv (G := ↥V₀)).surjective
  have hρk : ∀ u : ↥(⊤ : Subgroup ↥V₀), ρ u = 1 ↔ (u : ↥V₀) ∈ (⊥ : Subgroup ↥V₀) := by
    intro u
    rw [Subgroup.mem_bot]
    show e (u : ↥V₀) = 1 ↔ (u : ↥V₀) = 1
    exact map_eq_one_iff e e.injective
  refine ⟨τ.comp π, realizesVia_transport (H' := autOn (tildeOf V₁ (conjClosure K T)) (tildeOf V₁ I))
    hπ ρ hρs hρk τ hτs ?_⟩
  intro x u hu
  show e ((x : MulAut ↥V₀) (e.symm (e (u : ↥V₀)))) = e ((x : MulAut ↥V₀) (u : ↥V₀))
  rw [e.symm_apply_apply]

end Tilde

section Cases

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem autIH_equiv [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (hK : conjClosure K T ≠ K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) :
    Nonempty (↥(autIH V₁ Vp H K) ≃* ↥(autIH V₁ I H K)) := by
  have hFU := factElem h (le_conjClosure Vp H)
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  obtain ⟨hA38K, -⟩ := five_group_data h hH hA37 hA38 hK
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA38K
  have hneL : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map h hKH]
    exact map_K_ne_bot h hIU hnt
  have hneU : autIH V₁ Vp H K ≠ ⊥ := by
    intro hbot
    apply hneL
    rw [eq_bot_iff]
    rintro y hy
    obtain ⟨x, hx⟩ := toAutI_surjective h I ⟨y, hy⟩
    have hx1 : toAutI h Vp x = 1 := by
      have : ((toAutI h Vp x : ↥(autIH V₁ Vp H K)) :
          MulAut ↥(tildeOf V₁ (conjClosure Vp H))) ∈
          (⊥ : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) := by
        rw [← hbot]
        exact (toAutI h Vp x).2
      exact Subtype.ext (Subgroup.mem_bot.mp this)
    have h2 : x ∈ (toAutI h I).ker := toAutI_ker_le h hIU (show x ∈ (toAutI h Vp).ker from hx1)
    rw [MonoidHom.mem_ker] at h2
    rw [Subgroup.mem_bot]
    have h3 := congrArg Subtype.val hx
    rw [h2] at h3
    exact h3.symm
  obtain ⟨eL⟩ := nonempty_mulEquiv_quotient_autI h hIU hS hneL
  obtain ⟨eU⟩ := nonempty_mulEquiv_quotient_autI h (le_conjClosure Vp H) hS hneU
  exact ⟨eU.symm.trans eL⟩

variable [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem autIH_inf_centSub_eq_bot_of_top {J : Subgroup G}
    (htop : subM V₁ (conjClosure I H) J = ⊤) :
    autIH V₁ I H K ⊓ centSub (subM V₁ (conjClosure I H) J) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨-, hg⟩
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun w => ?_
  exact hg w (by rw [htop]; exact Subgroup.mem_top w)

theorem H_le_normalizer_of_autIH_le_stabSub (h : HypF918 T V L V₁ Vp H K) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H)
    (hM : autIH V₁ I H H ≤ stabSub (subM V₁ (conjClosure I H) I)) :
    H ≤ Subgroup.normalizer (I : Set G) := by
  intro x hx
  have hxM : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨x, hx⟩ ∈ autIH V₁ I H H := by
    rw [autIH_eq_map h le_rfl]
    exact ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  exact (actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
    (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) ⟨x, hx⟩).mp (hM hxM)

theorem five_one_of_modFive (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) (hK : conjClosure K T ≠ K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G))
    (htop : subM V₁ (conjClosure I H) I = ⊤)
    (hM : autIH V₁ I H H ≤ stabSub (subM V₁ (conjClosure I H) I))
    (hL : ∃ n, IsPSL 2 2 n ↥(autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ∧
      Omega4PlusModule (autSub (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)) n) :
    H ≤ Subgroup.normalizer (I : Set G) ∧
      ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        Nonempty (↥(autIH V₁ Vp H K) ≃* ↥(StatedSL 2 F)) ∧
        ModelOnU (FFModel.tensorNat 2 F) (tildeOf V₁ (conjClosure K T)) (tildeOf V₁ I) := by
  obtain ⟨n, hPSL, F, hF, hFin, hcard, hreal⟩ := hL
  refine ⟨H_le_normalizer_of_autIH_le_stabSub h hV₁I hIU hM, n, F, hF, hFin, hcard, ?_,
    modelOnU_tilde_of_realizes h hIU hKI hreal⟩
  obtain ⟨F', hF', hFin', hcard', ⟨eF⟩⟩ := isPSL_two_equiv_statedSL hPSL
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hLV : autIH V₁ I H K ≤ stabSub (subM V₁ (conjClosure I H) I) :=
    (CFSG.Quasithin.AutOn.autOn_mono (V := tildeOf V₁ (conjClosure I H))
      (secImg_mono (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) hKH)).trans hM
  obtain ⟨eA⟩ := autIH_equiv h hH hA37 hA38 hK hIU hnt
  letI := Fintype.ofFinite F'
  letI := Fintype.ofFinite F
  have hcardF : Fintype.card F' = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard', hcard]
  have φ : F' ≃+* F := FiniteField.ringEquivOfCardEq hcardF
  exact ⟨eA.trans ((autSubEquivOfFaithful hLV (autIH_inf_centSub_eq_bot_of_top htop)).trans
    (eF.trans (statedSLMapEquiv 2 φ)))⟩

theorem five_two_of_modFive (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) (hK : conjClosure K T ≠ K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G))
    (htop : subM V₁ (conjClosure I H) I = ⊤)
    (hM : autIH V₁ I H H ≤ stabSub (subM V₁ (conjClosure I H) I))
    (hL : IsPSL 3 2 1 ↥(autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)))
    (hT : TensorNatL32 (autSub (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I))) :
    H ≤ Subgroup.normalizer (I : Set G) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
        Nonempty (↥(autIH V₁ Vp H K) ≃* ↥(StatedSL 3 F)) ∧
        ModelOnU (FFModel.tensorNat 3 F) (tildeOf V₁ (conjClosure K T)) (tildeOf V₁ I) := by
  refine ⟨H_le_normalizer_of_autIH_le_stabSub h hV₁I hIU hM, ZMod 2, inferInstance, inferInstance,
    Nat.card_zmod 2, ?_, modelOnU_tilde_of_realizes h hIU hKI hT⟩
  obtain ⟨eF⟩ := isPSL_three_equiv_statedSL_zmod_two hL
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hLV : autIH V₁ I H K ≤ stabSub (subM V₁ (conjClosure I H) I) :=
    (CFSG.Quasithin.AutOn.autOn_mono (V := tildeOf V₁ (conjClosure I H))
      (secImg_mono (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) hKH)).trans hM
  obtain ⟨eA⟩ := autIH_equiv h hH hA37 hA38 hK hIU hnt
  exact ⟨eA.trans ((autSubEquivOfFaithful hLV (autIH_inf_centSub_eq_bot_of_top htop)).trans eF)⟩

end Cases

section Alternatives

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

@[expose] def ModFiveOne {W : Type} [CommGroup W] [Finite W] (M Mp L : Subgroup (MulAut W))
    (V : Subgroup W) : Prop :=
  V = ⊤ ∧ M ≤ stabSub V ∧ ∃ n, IsPSL 2 2 n ↥(autSub L V) ∧ Omega4PlusModule (autSub Mp V) n

@[expose] def ModFiveTwo {W : Type} [CommGroup W] [Finite W] (M Mp L : Subgroup (MulAut W))
    (V : Subgroup W) : Prop :=
  V = ⊤ ∧ M ≤ stabSub V ∧ IsPSL 3 2 1 ↥(autSub L V) ∧ TensorNatL32 (autSub Mp V)

@[expose] noncomputable def F918FiveIii (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) {t : G} (ht : t ∈ T) : Prop :=
  haveI := factElem h hIU
  ModFiveIii (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
      (subM V₁ (conjClosure I H) I)
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩) ∨
    ModFiveIii (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T)
      (conjAutSub (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩)
        (autIH V₁ I H K))
      (subM V₁ (conjClosure I H) I)
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩)⁻¹

@[expose] noncomputable def F918FiveIiiS (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) {t : G} (ht : t ∈ T) : Prop :=
  haveI := factElem h hIU
  F918FiveIii h hIU ht ∧
    (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I) ≠ ⊤ ∨
      ModFiveIiiAB (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
        (subM V₁ (conjClosure I H) I)
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩) ∨
      ModFiveIiiAB (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T)
        (conjAutSub (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩)
          (autIH V₁ I H K))
        (subM V₁ (conjClosure I H) I)
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩)⁻¹)

omit [Finite G] in
theorem exists_mem_T_not_normalizer (h : HypF918 T V L V₁ Vp H K) (hK : conjClosure K T ≠ K) :
    ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
  by_contra hcon
  push Not at hcon
  apply hK
  apply le_antisymm
  · refine conjClosure_le fun t ht z hz => ?_
    exact (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
  · exact le_conjClosure K T

theorem mod5_core_strong {W : Type} [CommGroup W] [Finite W] (h36 : D36) (h37 : D37) (h321 : D321)
    (hI5 : Insp5a) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {A : Subgroup (MulAut W)}
    {t : MulAut W} (hD : D31 M Mp T L V) (hirr : V ∈ IrrPlusOn Mp (orbSup T V) T) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hL38 : A38Types ↥L) (hA : QOff Mp T A (orbSup T V)) :
    ModFive M Mp T L V t ∧ (orbSup T V ≠ ⊤ ∨ ModFiveTop M Mp T L V t) := by
  by_cases htop : orbSup T V = ⊤
  · have := mod5_of_top h36 h37 hI5 hD hirr htT htL hMp hL38 hA htop
    exact ⟨this.toModFive, Or.inr this⟩
  · exact ⟨mod5_core h36 h37 h321 hI5 hD hirr htT htL hMp hL38 hA, Or.inl htop⟩

theorem five_alternatives (hD36 : D36) (hD37 : D37) (hD321 : D321)
    (hI5 : Insp5a) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h : HypF918 T V L V₁ Vp H K)
    (hH : SQTKGroup ↥H) (hK : conjClosure K T ≠ K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hirr : IsIrrPlusTildeT h hIU) :
    IsF918FiveListU ↥(autIH V₁ Vp H K) ∧
      ((H ≤ Subgroup.normalizer (I : Set G) ∧
          ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
            Nonempty (↥(autIH V₁ Vp H K) ≃* ↥(StatedSL 2 F)) ∧
            ModelOnU (FFModel.tensorNat 2 F) (tildeOf V₁ (conjClosure K T)) (tildeOf V₁ I)) ∨
        (H ≤ Subgroup.normalizer (I : Set G) ∧
          ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
            Nonempty (↥(autIH V₁ Vp H K) ≃* ↥(StatedSL 3 F)) ∧
            ModelOnU (FFModel.tensorNat 3 F) (tildeOf V₁ (conjClosure K T)) (tildeOf V₁ I)) ∨
        ∀ t (ht : t ∈ T), t ∉ Subgroup.normalizer (K : Set G) → F918FiveIiiS h hIU ht) := by
  have hF := factElem h hIU
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  have hD := d31_of_hyp h hH hIU hV₁I hirr'
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp h hIU hV₁I hKI hnt
  obtain ⟨hL38, hshape, hdata⟩ := five_prelim h hH hK hIU hnt hA37 hA38
  have key : ∀ t (ht : t ∈ T), t ∉ Subgroup.normalizer (K : Set G) →
      ModFive (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T)
        (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩) ∧
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I) ≠ ⊤ ∨
        ModFiveTop (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T)
          (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)
          (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩)) := by
    intro t ht htK
    obtain ⟨ht'T, ht'L, hMp, -⟩ := hdata t ht htK
    exact mod5_core_strong hD36 hD37 hD321 hI5 hD hirr' ht'T ht'L hMp hL38 hA
  obtain ⟨t₀, ht₀, ht₀K⟩ := exists_mem_T_not_normalizer h hK
  refine ⟨isF918FiveListU_of_fiveShape (hshape (key t₀ ht₀ ht₀K).1.fiveShape), ?_⟩
  by_cases hA1 : ModFiveOne (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H K)
      (subM V₁ (conjClosure I H) I)
  · exact Or.inl (five_one_of_modFive h hH hA37 hA38 hK hV₁I hIU hnt hKI hA1.1 hA1.2.1 hA1.2.2)
  by_cases hA2 : ModFiveTwo (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H K)
      (subM V₁ (conjClosure I H) I)
  · exact Or.inr (Or.inl (five_two_of_modFive h hH hA37 hA38 hK hV₁I hIU hnt hKI hA2.1 hA2.2.1
      hA2.2.2.1 hA2.2.2.2))
  refine Or.inr (Or.inr fun t ht htK => ?_)
  obtain ⟨hf, hflag⟩ := key t ht htK
  refine ⟨?_, ?_⟩
  · rcases hf with h1 | h2 | h3 | h4
    · exact absurd h1 hA1
    · exact absurd h2 hA2
    · exact Or.inl h3
    · exact Or.inr h4
  · rcases hflag with hne | h1 | h2 | h3 | h4
    · exact Or.inl hne
    · exact absurd h1 hA1
    · exact absurd h2 hA2
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h4)

end Alternatives

end CFSG.Quasithin.RonanF918
