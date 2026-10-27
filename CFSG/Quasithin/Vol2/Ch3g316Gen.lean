module

public import CFSG.Quasithin.Vol2.Ch3nCore
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Vol2.Ch3g316Ker

public section

namespace CFSG.Quasithin.Ch3g316

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def ClC (H T D : Subgroup G) : Prop :=
  ∀ t ∈ T ⊓ twoResidual H, (∃ j ∈ thompsonJ T, ∃ c ∈ pCoreOf 2 H, j = t * c) →
    ∀ y ∈ twoResidual H ⊓ Subgroup.normalizer ((T ⊓ twoResidual H : Subgroup G) : Set G),
      t⁻¹ * (y * t * y⁻¹) ∈ D

@[expose] def ClD (H T D : Subgroup G) : Prop :=
  ∀ s ∈ thompsonJ T, ∀ t ∈ T ⊓ twoResidual H, ⁅s, t⁆ ∈ D

variable {H T M₂ R : Subgroup G}

omit [Finite G] in
theorem conjSub_genBy_le (hmp : MinParabolic H T M₂) {K : Subgroup G}
    (hTK : T ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) {t : G} (ht : t ∈ T) :
    B6.conjSub t (Ch3n.genBy T K R M₂) ≤ Ch3n.genBy T K R M₂ := by
  rw [Ch3n.genBy, OrderIso.map_iSup]
  refine iSup_le fun y => ?_
  rw [OrderIso.map_iSup]
  refine iSup_le fun hy => ?_
  rw [OrderIso.map_inf, ← B6.conjSub_mul, B6.conjSub_eq_self (Subgroup.le_normalizer ht)]
  exact le_iSup₂_of_le (f := fun y (_ : y ∈ M₂ ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) :
    Set G)) => B6.conjSub y R ⊓ T) (t * y)
    ⟨M₂.mul_mem (hmp.le ht) hy.1, Subgroup.mul_mem _ (hTK ht) hy.2⟩ le_rfl

theorem exists_good_subgroup (hmp : MinParabolic H T M₂)
    (hXM : H ⊓ Subgroup.normalizer ((T ⊓ twoResidual H : Subgroup G) : Set G) ≤ M₂)
    (hRT : R ≤ T) (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hJR : thompsonJ T ≤ R)
    (hKQ : ⁅twoResidual H, pCoreOf 2 H⁆ ≤ R ⊓ pCoreOf 2 H)
    (hQn : H ≤ Subgroup.normalizer ((R ⊓ pCoreOf 2 H : Subgroup G) : Set G)) :
    ∃ D : Subgroup G, D ≤ T ⊓ twoResidual H ∧ D ≤ Ch3n.genBy T (twoResidual H) R M₂ ∧
      H ⊓ Subgroup.normalizer ((T ⊓ twoResidual H : Subgroup G) : Set G) ≤
        Subgroup.normalizer (D : Set G) ∧
      ClC H T D ∧ ClD H T D ∧ R ⊓ twoResidual H ≤ D := by
  classical
  set K := twoResidual H with hKdef
  set P := T ⊓ K with hPdef
  set Γ := Ch3n.genBy T K R M₂ with hΓdef
  set B := K ⊓ Subgroup.normalizer (P : Set G) with hBdef
  have hTH : T ≤ H := hmp.isSylow.1
  have hKH : K ≤ H := twoResidual_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_twoResidual H
  have hTP : T ≤ Subgroup.normalizer (P : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hHK (hTH ht)⟩
  have hPT : P ≤ T := inf_le_left
  have hPK : P ≤ K := inf_le_right
  have hΓgen : ∀ y ∈ B, B6.conjSub y R ⊓ T ≤ Γ := fun y hy =>
    le_iSup₂_of_le (f := fun y (_ : y ∈ M₂ ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) =>
      B6.conjSub y R ⊓ T) y ⟨hXM ⟨hKH hy.1, hy.2⟩, hy.2⟩ le_rfl
  have hRΓ : R ≤ Γ := fun x hx => hΓgen 1 B.one_mem
    ⟨by simpa [B6.mem_conjSub] using hx, hRT hx⟩
  have hΓT : T ≤ Subgroup.normalizer (Γ : Set G) := fun t ht =>
    B6.mem_normalizer_of_conjSub_le (conjSub_genBy_le hmp (K := K) hTP ht)
      (conjSub_genBy_le hmp (K := K) hTP (T.inv_mem ht))
  let D : Subgroup G := P ⊓ ⨅ y ∈ B, B6.conjSub y⁻¹ Γ
  have hmemD : ∀ x, x ∈ D ↔ x ∈ P ∧ ∀ y ∈ B, y * x * y⁻¹ ∈ Γ := by
    intro x
    simp only [D, Subgroup.mem_inf, Subgroup.mem_iInf, B6.mem_conjSub, inv_inv]
  have hDP : D ≤ P := inf_le_left
  have hDΓ : D ≤ Γ := fun x hx => by
    simpa using ((hmemD x).1 hx).2 1 B.one_mem
  have hBD : B ≤ Subgroup.normalizer (D : Set G) := by
    intro z hz
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxP, hxΓ⟩ := (hmemD x).1 hx
      refine (hmemD _).2 ⟨(Subgroup.mem_normalizer_iff.mp hz.2 x).mp hxP, fun y hy => ?_⟩
      have := hxΓ (y * z) (B.mul_mem hy hz)
      simpa [mul_assoc] using this
    · obtain ⟨hxP, hxΓ⟩ := (hmemD x).1 hx
      have hz' : z⁻¹ ∈ B := B.inv_mem hz
      refine (hmemD _).2 ⟨?_, fun y hy => ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hz'.2 x).mp hxP
        simpa using this
      · have := hxΓ (y * z⁻¹) (B.mul_mem hy hz')
        simpa [mul_assoc] using this
  have hTD : T ≤ Subgroup.normalizer (D : Set G) := by
    intro t ht
    have key : ∀ t ∈ T, ∀ x ∈ D, t * x * t⁻¹ ∈ D := by
      intro t ht x hx
      obtain ⟨hxP, hxΓ⟩ := (hmemD x).1 hx
      refine (hmemD _).2 ⟨(Subgroup.mem_normalizer_iff.mp (hTP ht) x).mp hxP, fun y hy => ?_⟩
      have hy' : t⁻¹ * y * t ∈ B := by
        refine ⟨?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (hHK (hTH (T.inv_mem ht))) y).mp hy.1
          simpa [mul_assoc] using this
        · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTP (T.inv_mem ht)) hy.2) (hTP ht)
      have h1 := hxΓ _ hy'
      have h2 := (Subgroup.mem_normalizer_iff.mp (hΓT ht) _).mp h1
      have e : t * (t⁻¹ * y * t * x * (t⁻¹ * y * t)⁻¹) * t⁻¹ = y * (t * x * t⁻¹) * y⁻¹ := by group
      rwa [e] at h2
    exact B6.mem_normalizer_of_forall_mem (fun x hx => key t ht x hx)
      (fun x hx => by simpa using key t⁻¹ (T.inv_mem ht) x hx)
  have hRD : R ⊓ P ≤ D := by
    intro x hx
    refine (hmemD x).2 ⟨hx.2, fun y hy => ?_⟩
    have hmem : y * x * y⁻¹ ∈ B6.conjSub y R ⊓ T := Subgroup.mem_inf.mpr
      ⟨B6.mem_conjSub.mpr (by simpa [mul_assoc] using hx.1),
        hPT ((Subgroup.mem_normalizer_iff.mp hy.2 x).mp hx.2)⟩
    exact hΓgen y hy hmem
  refine ⟨D, hDP, hDΓ, ?_, ?_, ?_, ?_⟩
  ·
    intro h hh
    have hHKT : H = K ⊔ T := by rw [sup_comm]; exact (sup_twoResidual_eq hmp.isSylow).symm
    have hh' : h ∈ ((K ⊔ T : Subgroup G) : Set G) := by rw [← hHKT]; exact hh.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hTH.trans hHK)] at hh'
    obtain ⟨k, hk, t, ht, rfl⟩ := hh'
    have hkB : k ∈ B := by
      refine ⟨hk, ?_⟩
      have := Subgroup.mul_mem _ hh.2 (Subgroup.inv_mem _ (hTP ht))
      simpa [mul_assoc] using this
    exact Subgroup.mul_mem _ (hBD hkB) (hTD ht)
  ·
    intro t ht ⟨j, hj, c, hc, hjc⟩ y hy
    have htP : t ∈ P := ht
    have hcH : c ∈ H := pCoreOf_le 2 H hc
    have hcT : c ∈ T := B6.pCoreOf_two_le_of_isSylowTwoOf hmp.isSylow hc
    have hjR : j ∈ R := hJR hj
    have hQΓ : R ⊓ pCoreOf 2 H ≤ Γ := inf_le_left.trans hRΓ
    have hQT : R ⊓ pCoreOf 2 H ≤ T := inf_le_left.trans hRT
    have hQH : ∀ h ∈ H, ∀ q ∈ R ⊓ pCoreOf 2 H, h * q * h⁻¹ ∈ R ⊓ pCoreOf 2 H :=
      fun h hh q hq => (Subgroup.mem_normalizer_iff.mp (hQn hh) q).mp hq
    have hKc : ∀ w ∈ K, ∀ c' ∈ pCoreOf 2 H, ⁅w, c'⁆ ∈ R ⊓ pCoreOf 2 H := fun w hw c' hc' =>
      hKQ (Subgroup.commutator_mem_commutator hw hc')
    have hwP : ∀ w ∈ B, w * t * w⁻¹ ∈ P := fun w hw =>
      (Subgroup.mem_normalizer_iff.mp hw.2 t).mp htP
    have hg : ∀ w ∈ B, w * j * w⁻¹ ∈ Γ := by
      intro w hw
      have hq : ⁅w, c⁆ ∈ R ⊓ pCoreOf 2 H := hKc w hw.1 c hc
      have e : w * j * w⁻¹ = (w * t * w⁻¹) * ⁅w, c⁆ * c := by
        rw [hjc]; simp only [commutatorElement_def]; group
      have hmem : w * j * w⁻¹ ∈ B6.conjSub w R ⊓ T := by
        refine Subgroup.mem_inf.mpr ⟨B6.mem_conjSub.mpr (by simpa [mul_assoc] using hjR), ?_⟩
        rw [e]
        exact T.mul_mem (T.mul_mem (hPT (hwP w hw)) (hQT hq)) hcT
      exact hΓgen w hw hmem
    have hkey : ∀ w ∈ B, ∀ w' ∈ B, (w * t * w⁻¹)⁻¹ * (w' * t * w'⁻¹) ∈ Γ := by
      intro w hw w' hw'
      have hmP : (w * t * w⁻¹)⁻¹ * (w' * t * w'⁻¹) ∈ P :=
        P.mul_mem (P.inv_mem (hwP w hw)) (hwP w' hw')
      have hq : ⁅w, c⁆ ∈ R ⊓ pCoreOf 2 H := hKc w hw.1 c hc
      have hq' : ⁅w', c⁆ ∈ R ⊓ pCoreOf 2 H := hKc w' hw'.1 c hc
      have hq'' : ⁅((w * t * w⁻¹)⁻¹ * (w' * t * w'⁻¹))⁻¹, c⁻¹⁆ ∈ R ⊓ pCoreOf 2 H :=
        hKc _ (K.inv_mem (hPK hmP)) c⁻¹ ((pCoreOf 2 H).inv_mem hc)
      have hq1 : c⁻¹ * ⁅w, c⁆⁻¹ * c ∈ R ⊓ pCoreOf 2 H := by
        simpa using hQH c⁻¹ (H.inv_mem hcH) _ ((R ⊓ pCoreOf 2 H).inv_mem hq)
      have hq2 : c⁻¹ * ⁅w', c⁆ * c ∈ R ⊓ pCoreOf 2 H := by
        simpa using hQH c⁻¹ (H.inv_mem hcH) _ hq'
      have hE := Γ.mul_mem (Γ.inv_mem (hg w hw)) (hg w' hw')
      have e : (w * t * w⁻¹)⁻¹ * (w' * t * w'⁻¹) =
          (c⁻¹ * ⁅w, c⁆⁻¹ * c)⁻¹ * ((w * j * w⁻¹)⁻¹ * (w' * j * w'⁻¹)) * (c⁻¹ * ⁅w', c⁆ * c)⁻¹ *
            ⁅((w * t * w⁻¹)⁻¹ * (w' * t * w'⁻¹))⁻¹, c⁻¹⁆⁻¹ := by
        rw [hjc]; simp only [commutatorElement_def]; group
      rw [e]
      exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (hQΓ hq1)) hE)
        (Γ.inv_mem (hQΓ hq2))) (Γ.inv_mem (hQΓ hq''))
    refine (hmemD _).2 ⟨?_, fun z hz => ?_⟩
    · exact P.mul_mem (P.inv_mem htP) ((Subgroup.mem_normalizer_iff.mp hy.2 t).mp htP)
    · have h1 := hkey z hz (z * y) (B.mul_mem hz hy)
      have e : z * (t⁻¹ * (y * t * y⁻¹)) * z⁻¹ =
          (z * t * z⁻¹)⁻¹ * ((z * y) * t * (z * y)⁻¹) := by group
      rw [e]
      exact h1
  ·
    intro s hs t ht
    refine hRD ⟨?_, ?_⟩
    · have h1 : t * s⁻¹ * t⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hTR ht.1) _).mp
        (R.inv_mem (hJR hs))
      have e : ⁅s, t⁆ = s * (t * s⁻¹ * t⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact R.mul_mem (hJR hs) h1
    · refine ⟨?_, ?_⟩
      · have hsT : s ∈ T := (B6.thompsonJ_le T) hs
        simp only [commutatorElement_def]
        exact T.mul_mem (T.mul_mem (T.mul_mem hsT ht.1) (T.inv_mem hsT)) (T.inv_mem ht.1)
      · have hsH : s ∈ H := hTH ((B6.thompsonJ_le T) hs)
        have h1 : s * t * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hHK hsH) t).mp ht.2
        have e : ⁅s, t⁆ = (s * t * s⁻¹) * t⁻¹ := by simp only [commutatorElement_def]
        rw [e]
        exact K.mul_mem h1 (K.inv_mem ht.2)
  · intro x hx
    exact hRD ⟨hx.1, hRT hx.1, hx.2⟩

theorem not_inf_le_pCoreOf_of_not_solvable (hmp : MinParabolic H T M₂)
    (hns : ¬ Group.IsSolvable ↥H) : ¬ T ⊓ twoResidual H ≤ pCoreOf 2 H := by
  intro hP
  set K := twoResidual H with hKdef
  have hKH : K ≤ H := twoResidual_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_twoResidual H
  have hPsyl : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hmp.isSylow hKH hHK
  have hPN : T ⊓ K ≤ pCoreOf 2 K := by
    have h1 : pCoreOf 2 H ⊓ K ≤ pCoreOf 2 K := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_right (fun k hk => ?_) ?_
      · exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨le_normalizer_pCoreOf 2 H (hKH hk), hHK (hKH hk)⟩
      · exact (pCoreOf_isPGroup 2 H).to_le inf_le_left
    exact fun x hx => h1 ⟨hP hx, hx.2⟩
  have hNK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hodd : Odd (Nat.card (↥K ⧸ (pCoreOf 2 K).subgroupOf K)) := by
    have h1 : (pCoreOf 2 K).relIndex K ∣ (T ⊓ K).relIndex K :=
      Subgroup.relIndex_dvd_of_le_left K hPN
    have h2 : ¬ 2 ∣ (pCoreOf 2 K).relIndex K := fun h => hPsyl.2.2 (h.trans h1)
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have hNn : ((pCoreOf 2 K).subgroupOf K).Normal := normal_pCoreOf_subgroupOf K
  have hp : IsPGroup 2 ↥((pCoreOf 2 K).subgroupOf K) :=
    (pCoreOf_isPGroup 2 K).of_equiv (Subgroup.subgroupOfEquivOfLe hNK).symm
  have : Group.IsNilpotent ↥((pCoreOf 2 K).subgroupOf K) := hp.isNilpotent
  have hq : Group.IsSolvable (↥K ⧸ (pCoreOf 2 K).subgroupOf K) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hKs : Group.IsSolvable ↥K :=
    Group.isSolvable_of_ker_le_range ((pCoreOf 2 K).subgroupOf K).subtype
      (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  apply hns
  apply B6.isSolvable_of_twoResidual
  rw [B6.twoResidual_top_eq_subgroupOf]
  exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective

theorem gen316_of_gen (hmp : MinParabolic H T M₂) (hns : ¬ Group.IsSolvable ↥H)
    (hRT : R ≤ T) (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hJR : thompsonJ T ≤ R)
    (hKQ : ⁅twoResidual H, pCoreOf 2 H⁆ ≤ R ⊓ pCoreOf 2 H)
    (hQn : H ≤ Subgroup.normalizer ((R ⊓ pCoreOf 2 H : Subgroup G) : Set G))
    (hgen : ∀ D : Subgroup G, D ≤ T ⊓ twoResidual H →
      H ⊓ Subgroup.normalizer ((T ⊓ twoResidual H : Subgroup G) : Set G) ≤
        Subgroup.normalizer (D : Set G) → ClC H T D → ClD H T D →
      T ⊓ twoResidual H ≤ D ⊔ pCoreOf 2 (twoResidual H)) :
    T ⊓ twoResidual H ≤ Ch3n.genBy T (twoResidual H) R M₂ := by
  classical
  set K := twoResidual H with hKdef
  set P := T ⊓ K with hPdef
  have hTH : T ≤ H := hmp.isSylow.1
  have hKH : K ≤ H := twoResidual_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_twoResidual H
  have hTP : T ≤ Subgroup.normalizer (P : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hHK (hTH ht)⟩
  have hPsyl : IsSylowTwoOf P K := B6.isSylowTwoOf_inf_normal hmp.isSylow hKH hHK
  have hXM : H ⊓ Subgroup.normalizer (P : Set G) ≤ M₂ := by
    refine hmp.le_of_lt (le_inf hTH hTP) (lt_of_le_of_ne inf_le_left fun hX => ?_)
    have hHP : H ≤ Subgroup.normalizer (P : Set G) := by rw [← hX]; exact inf_le_right
    have hPO : P ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hTH) hHP
      (hmp.isSylow.2.1.to_le inf_le_left)
    exact not_inf_le_pCoreOf_of_not_solvable hmp hns hPO
  obtain ⟨D, hDP, hDΓ, hDN, hC, hD, hRD⟩ := exists_good_subgroup hmp hXM hRT hTR hJR hKQ hQn
  have hPD := hgen D hDP hDN hC hD
  have hO₂K : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hcomm : ⁅pCoreOf 2 K, K⁆ ≤ (R ⊓ pCoreOf 2 H) ⊓ K := by
    refine le_inf ?_ ?_
    · refine (Subgroup.commutator_mono hO₂K le_rfl).trans ?_
      rw [Subgroup.commutator_comm]
      exact hKQ
    · refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      have ha' : a ∈ K := (pCoreOf_le 2 K) ha
      rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem ha' hb) (K.inv_mem ha')) (K.inv_mem hb)
  have hN₀K : K ≤ Subgroup.normalizer (((R ⊓ pCoreOf 2 H) ⊓ K : Subgroup G) : Set G) :=
    fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hQn (hKH hk), Subgroup.le_normalizer hk⟩
  have hN₀D : (R ⊓ pCoreOf 2 H) ⊓ K ≤ D := fun x hx => hRD ⟨hx.1.1, hx.2⟩
  have hPle : P ≤ D := sylow_le_of_central_quotient hPsyl (twoResidual_twoResidual H) hDP
    (fun x hx => hDN ⟨hTH hx.1, Subgroup.le_normalizer hx⟩) hN₀K hN₀D
    (B6.pCoreOf_two_le_of_isSylowTwoOf hPsyl) hcomm hPD
  exact hPle.trans hDΓ

end CFSG.Quasithin.Ch3g316
