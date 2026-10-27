module

public import CFSG.Quasithin.EmptyFaithful.S1421STDefs
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabNine
public import CFSG.Quasithin.EmptyFaithful.SBc16GAct
public import CFSG.Quasithin.EmptyFaithful.S1421QA13aL34

public section

namespace CFSG.Quasithin.QA13a

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open CFSG.Quasithin.Hyp1281Two (wOfU wOfU_le_uOfL22)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def rhoH (H : Subgroup G) :
    ↥H →* MulAut (OTwoQuot (oTwoUpper H)) :=
  (SBc16.actHom (oTwoUpper H)).comp (Subgroup.inclusion (le_normalizer_oTwoUpper H))

omit [Finite G] in
theorem rhoH_eq_one_iff (H : Subgroup G) (h : ↥H) :
    rhoH H h = 1 ↔ ∀ k ∈ oTwoUpper H, (h : G) * k * (h : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 (oTwoUpper H) :=
  SBc16.actHom_eq_one_iff (oTwoUpper H) (le_normalizer_oTwoUpper H h.2)

omit [Finite G] in
theorem rhoH_of_mem (H : Subgroup G) {k : G} (hk : k ∈ oTwoUpper H) :
    rhoH H ⟨k, oTwoUpper_le H hk⟩ =
      MulAut.conj (QuotientGroup.mk ⟨k, hk⟩ : OTwoQuot (oTwoUpper H)) := by
  apply MulEquiv.ext
  intro v
  induction v using QuotientGroup.induction_on with | H x => ?_
  obtain ⟨x, hx⟩ := x
  show SBc16.actHom (oTwoUpper H) ⟨k, le_normalizer_oTwoUpper H (oTwoUpper_le H hk)⟩
    (QuotientGroup.mk ⟨x, hx⟩) = _
  rw [SBc16.actHom_mk]
  rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

theorem inf_le_pCoreOf_oTwoUpper (H : Subgroup G) :
    oTwoUpper H ⊓ pCoreOf 2 H ≤ pCoreOf 2 (oTwoUpper H) := by
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
  intro k hk
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hk, le_normalizer_pCoreOf 2 H (oTwoUpper_le H hk)⟩

theorem rhoH_pCore (H : Subgroup G) {q : G} (hq : q ∈ pCoreOf 2 H) :
    rhoH H ⟨q, pCoreOf_le 2 H hq⟩ = 1 := by
  rw [rhoH_eq_one_iff]
  intro k hk
  have hkH : k ∈ H := oTwoUpper_le H hk
  have hqH : q ∈ H := pCoreOf_le 2 H hq
  apply inf_le_pCoreOf_oTwoUpper H
  refine ⟨?_, ?_⟩
  · have h1 : q * k * q⁻¹ ∈ oTwoUpper H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H hqH) k).mp hk
    exact (oTwoUpper H).mul_mem h1 ((oTwoUpper H).inv_mem hk)
  · have h1 : k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hkH) q⁻¹).mp
        ((pCoreOf 2 H).inv_mem hq)
    have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem hq h1

theorem mem_pCoreOf_of_rhoH_eq_one (H : Subgroup G)
    (hZ : ∀ z : OTwoQuot (oTwoUpper H), (∀ x, x * z = z * x) → z = 1) (h : ↥H)
    (hρ : rhoH H h = 1) : (h : G) ∈ pCoreOf 2 H := by
  have hker : IsPGroup 2 (rhoH H).ker := by
    intro c
    obtain ⟨a, ha⟩ := exists_pow_mem_oTwoUpper H c.1.2
    set d : G := ((c.1 : ↥H) : G) ^ 2 ^ a with hd
    have hdK : d ∈ oTwoUpper H := ha
    have hρd : rhoH H ⟨d, oTwoUpper_le H hdK⟩ = 1 := by
      have e : (⟨d, oTwoUpper_le H hdK⟩ : ↥H) = (c.1 : ↥H) ^ 2 ^ a := Subtype.ext rfl
      rw [e, map_pow, MonoidHom.mem_ker.mp c.2, one_pow]
    rw [rhoH_of_mem H hdK] at hρd
    have hcen : (QuotientGroup.mk ⟨d, hdK⟩ : OTwoQuot (oTwoUpper H)) = 1 := by
      apply hZ
      intro x
      have h1 := congrArg (fun φ : MulAut (OTwoQuot (oTwoUpper H)) => φ x) hρd
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc x * QuotientGroup.mk ⟨d, hdK⟩
          = (QuotientGroup.mk ⟨d, hdK⟩ * x * (QuotientGroup.mk ⟨d, hdK⟩)⁻¹) *
              QuotientGroup.mk ⟨d, hdK⟩ := by rw [h1]
        _ = QuotientGroup.mk ⟨d, hdK⟩ * x := by group
    have hdQ : d ∈ pCoreOf 2 (oTwoUpper H) :=
      (mk_eq_one_iff_mem_pCoreOf (⟨d, hdK⟩ : ↥(oTwoUpper H))).mp hcen
    obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 (oTwoUpper H)) ⟨_, hdQ⟩
    refine ⟨a + b, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hb' : d ^ 2 ^ b = 1 := congrArg Subtype.val hb
    simpa [hd, pow_add, pow_mul] using hb'
  have hN : (rhoH H).ker.Normal := MonoidHom.normal_ker _
  have hle : (rhoH H).ker ≤ CFSG.Open.pCore 2 ↥H := le_pCore 2 hN hker
  exact ⟨h, hle (MonoidHom.mem_ker.mpr hρ), rfl⟩

theorem rhoH_comm_of_comm_mem (H : Subgroup G) {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (hc : a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 H) :
    rhoH H ⟨a, ha⟩ * rhoH H ⟨b, hb⟩ = rhoH H ⟨b, hb⟩ * rhoH H ⟨a, ha⟩ := by
  have h1 := rhoH_pCore H hc
  have e : (⟨a * b * a⁻¹ * b⁻¹, pCoreOf_le 2 H hc⟩ : ↥H) =
      ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ := Subtype.ext rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem rhoH_sq_of_mem (H : Subgroup G) {a : G} (ha : a ∈ H) (hs : a * a ∈ pCoreOf 2 H) :
    rhoH H ⟨a, ha⟩ * rhoH H ⟨a, ha⟩ = 1 := by
  rw [← map_mul]
  exact rhoH_pCore H (q := a * a) hs

theorem card_image_ge (H T : Subgroup G) (hT : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H))
    (hcard : Nat.card (OTwoQuot (oTwoUpper H)) = 20160) :
    64 ≤ Nat.card ↥(imageOTwoQuot (oTwoUpper H) (T ⊓ oTwoUpper H)) := by
  set P : Subgroup (OTwoQuot (oTwoUpper H)) := imageOTwoQuot (oTwoUpper H) (T ⊓ oTwoUpper H)
    with hP
  have hidx : ¬ 2 ∣ P.index := by
    intro h2
    apply hT.2.2
    refine h2.trans ?_
    exact Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
  have hmul : Nat.card P * P.index = 64 * 315 := by
    rw [Subgroup.card_mul_index, hcard]
  have hodd : Odd P.index := Nat.odd_iff.mpr (by omega)
  have hcop : Nat.Coprime 64 P.index := by
    have : Nat.Coprime (2 ^ 6) P.index := Nat.Coprime.pow_left 6 (Nat.coprime_two_left.mpr hodd)
    simpa using this
  have hdvd : 64 ∣ Nat.card P := hcop.dvd_of_dvd_mul_right ⟨315, hmul⟩
  exact Nat.le_of_dvd Nat.card_pos hdvd

variable {T M H K1 : Subgroup G}

theorem exists_B (st : Setting1427 T M H K1) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) :
    ∃ (B : Subgroup G) (Xs : Set G), pCoreOf 2 (yOfL22 T M) ≤ B ∧ B ≤ T ∧
      T ≤ Subgroup.normalizer (B : Set G) ∧
      (∀ b ∈ B, ∃ q ∈ pCoreOf 2 H, ∃ x ∈ Xs, b = q * x) ∧ (∀ x ∈ Xs, x ∈ B) ∧
      (∀ x ∈ Xs, ∀ x' ∈ Xs, x * x' * x⁻¹ * x'⁻¹ ∈ pCoreOf 2 H) ∧
      (∀ x ∈ Xs, x * x ∈ pCoreOf 2 H) := by
  have hTH : T ≤ H := st.hStar.1.1
  have hHMc : H ≤ mcOf T := (st.hyp.isUniqueM_centralizer st.hStar.1 st.hStar.2.1).1.2
  have h := lemma_14_2_4 st.hyp st.facts
  obtain ⟨g, hg⟩ := h.exists_goodElt_L
  have hgM : g ∈ M := h.le hg.mem
  have hUQ : uOfL22 T M ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (h.uOfL22_le_T.trans hTH)
      (hHMc.trans h.g1_le_normalizer_uOfL22) (h.sylow.1.to_le h.uOfL22_le_T)
  have hVQ : VZ T M ≤ pCoreOf 2 H := (Hyp1281Two.VZ_le_uOfL22 T M).trans hUQ
  have hWQ : wOfU T M ≤ pCoreOf 2 H := (wOfU_le_uOfL22 T M).trans hUQ
  have hconjV : ∀ z ∈ quasithinOmegaOneCenter T, g⁻¹ * z * g ∈ VZ T M := fun z hz => by
    have := mem_conjClosure (Z := quasithinOmegaOneCenter T) (H := M) (M.inv_mem hgM) hz
    rw [inv_inv] at this
    exact this
  refine ⟨pCoreOf 2 (yOfL22 T M ⊔ uOfL22 T M), (rconj (wOfU T M) g : Set G), ?_,
    h.pCoreOf_sup_uOfL22_le_T hU hg, ?_, ?_, fun x hx => h.rconj_wOfU_le_pCoreOf hU hg hx, ?_, ?_⟩
  · rw [st.facts.y_oTwo, h.pCoreOf_sup_uOfL22_eq hU hg]
    exact inf_le_inf_right _ le_sup_left
  · exact (le_sup_right.trans h.LT_le_normalizer_sup_uOfL22).trans
      (normalizer_le_normalizer_pCoreOf 2 _)
  · intro b hb
    have hset := (h.pCoreOf_sup_uOfL22_eq_wOfU_sup hU hg).2
    have hb' : b ∈ (wOfU T M : Set G) * (rconj (wOfU T M) g : Set G) := by
      rw [← hset]
      exact hb
    obtain ⟨w, hw, x, hx, hwx⟩ := hb'
    exact ⟨w, hWQ hw, x, hx, hwx.symm⟩
  · intro x hx x' hx'
    have hw : g * x * g⁻¹ ∈ wOfU T M := mem_rconj.mp hx
    have hw' : g * x' * g⁻¹ ∈ wOfU T M := mem_rconj.mp hx'
    have hc := h.commutator_mem_omegaOneCenter (wOfU_le_uOfL22 T M hw) (wOfU_le_uOfL22 T M hw')
    have e : x * x' * x⁻¹ * x'⁻¹ = g⁻¹ * ((g * x * g⁻¹) * (g * x' * g⁻¹) * (g * x * g⁻¹)⁻¹ *
        (g * x' * g⁻¹)⁻¹) * g := by group
    rw [e]
    exact hVQ (hconjV _ hc)
  · intro x hx
    have hw : g * x * g⁻¹ ∈ wOfU T M := mem_rconj.mp hx
    have hc := h.sq_mem_omegaOneCenter (wOfU_le_uOfL22 T M hw)
    rw [pow_two] at hc
    have e : x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
    rw [e]
    exact hVQ (hconjV _ hc)

theorem core_of_B (st : Setting1427 T M H K1)
    (cfg : S1421.L34Cfg T M H K1) {B : Subgroup G} {Xs : Set G} (hBT : B ≤ T)
    (hTB : T ≤ Subgroup.normalizer (B : Set G))
    (hdec : ∀ b ∈ B, ∃ q ∈ pCoreOf 2 H, ∃ x ∈ Xs, b = q * x) (hXB : ∀ x ∈ Xs, x ∈ B)
    (hcomm : ∀ x ∈ Xs, ∀ x' ∈ Xs, x * x' * x⁻¹ * x'⁻¹ ∈ pCoreOf 2 H)
    (hsq : ∀ x ∈ Xs, x * x ∈ pCoreOf 2 H) : B ≤ S1421.sOf T K1 := by
  have hTH : T ≤ H := st.hStar.1.1
  have hK : IsPSL 3 2 2 (OTwoQuot (oTwoUpper H)) := cfg.psl
  have hZ : ∀ z : OTwoQuot (oTwoUpper H), (∀ x, x * z = z * x) → z = 1 :=
    fun z hz => eq_one_of_central_psl34 hK hz
  have hSyl : IsSylowTwoOf T H := isSylowTwoOf_of_isSylowTwo st.hyp.sylow hTH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hSyl
  have hSylK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hSyl (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hρx : ∀ b : ↥H, (b : G) ∈ B → ∃ x : ↥H, (x : G) ∈ Xs ∧ rhoH H b = rhoH H x := by
    intro b hb
    obtain ⟨q, hq, x, hx, hbqx⟩ := hdec b hb
    refine ⟨⟨x, hTH (hBT (hXB x hx))⟩, hx, ?_⟩
    have e : b = ⟨q, pCoreOf_le 2 H hq⟩ * ⟨x, hTH (hBT (hXB x hx))⟩ := Subtype.ext hbqx
    rw [e, map_mul, rhoH_pCore H hq, one_mul]
  have hT2 : IsPGroup 2 ↥(T.subgroupOf H) :=
    st.hyp.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hmain := core_psl34 hK (T' := (T.subgroupOf H).map (rhoH H))
    (N' := (B.subgroupOf H).map (rhoH H)) (hT2.map (rhoH H))
    (Subgroup.map_mono fun b hb => Subgroup.mem_subgroupOf.mpr
      (hBT (Subgroup.mem_subgroupOf.mp hb)))
    (by
      rintro _ ⟨t, ht, rfl⟩ _ ⟨a, ha, rfl⟩
      refine ⟨t * a * t⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp (hTB (Subgroup.mem_subgroupOf.mp ht)) (a : G)).mp
          (Subgroup.mem_subgroupOf.mp ha)))
    (by
      rintro _ ⟨b₁, hb₁, rfl⟩ _ ⟨b₂, hb₂, rfl⟩
      obtain ⟨x₁, hx₁, h₁⟩ := hρx b₁ (Subgroup.mem_subgroupOf.mp hb₁)
      obtain ⟨x₂, hx₂, h₂⟩ := hρx b₂ (Subgroup.mem_subgroupOf.mp hb₂)
      rw [h₁, h₂]
      exact rhoH_comm_of_comm_mem H x₁.2 x₂.2 (hcomm _ hx₁ _ hx₂))
    (by
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨x, hx, h₁⟩ := hρx b (Subgroup.mem_subgroupOf.mp hb)
      rw [h₁]
      exact rhoH_sq_of_mem H x.2 (hsq _ hx))
    (P := imageOTwoQuot (oTwoUpper H) (T ⊓ oTwoUpper H))
    (card_image_ge H T hSylK (card_psl34 hK))
    (by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨⟨y.1, oTwoUpper_le H y.2⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_subgroupOf.mp hy).1, rhoH_of_mem H y.2⟩)
  intro b hb
  have hbT : b ∈ T := hBT hb
  have hbH : b ∈ H := hTH hbT
  obtain ⟨kb, hkb⟩ := hmain (rhoH H ⟨b, hbH⟩) ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  obtain ⟨⟨k, hkK⟩, rfl⟩ := QuotientGroup.mk_surjective kb
  have hkH : k ∈ H := oTwoUpper_le H hkK
  have hρ1 : rhoH H ⟨b * k⁻¹, H.mul_mem hbH (H.inv_mem hkH)⟩ = 1 := by
    have e : (⟨b * k⁻¹, H.mul_mem hbH (H.inv_mem hkH)⟩ : ↥H) = ⟨b, hbH⟩ * ⟨k, hkH⟩⁻¹ :=
      Subtype.ext rfl
    rw [e, map_mul, map_inv, hkb, rhoH_of_mem H hkK, mul_inv_cancel]
  have hq : b * k⁻¹ ∈ pCoreOf 2 H := mem_pCoreOf_of_rhoH_eq_one H hZ _ hρ1
  have hkT : k ∈ T := by
    have : (b * k⁻¹)⁻¹ * b ∈ T := T.mul_mem (T.inv_mem (hQT hq)) hbT
    simpa [mul_assoc] using this
  have hN : b ∈ Subgroup.normalizer (K1 : Set G) := by
    have hq' : b * k⁻¹ ∈ Subgroup.normalizer (K1 : Set G) := st.notation_.pCore_le hq
    have hk' : k ∈ Subgroup.normalizer (K1 : Set G) := st.notation_.inf_le ⟨hkT, hkK⟩
    have := (Subgroup.normalizer (K1 : Set G)).mul_mem hq' hk'
    simpa [mul_assoc] using this
  exact ⟨hbT, hN⟩

theorem l34NonabelianO2Y : L34NonabelianO2Y := by
  intro G _ _ T M H K1 st cfg hU
  obtain ⟨B, Xs, hYB, hBT, hTB, hdec, hXB, hcomm, hsq⟩ := exists_B st hU
  exact hYB.trans (core_of_B st cfg hBT hTB hdec hXB hcomm hsq)

end CFSG.Quasithin.QA13a
