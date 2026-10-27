module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Moving

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem ggL45_inf_conj_eq_one_of_cent (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hC : Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.zpowers d) {r : G}
    (hr : r ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    (hrd : r ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    ∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G),
      r * v * r⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G) → v = 1 := by
  have : Fact p.Prime := ⟨hcfg.prime⟩
  obtain ⟨hB₁U₁, hxU₁, hVU₁⟩ := ggL4546_basic hraw hiso hcfg
  set V : Subgroup G := U ⊓ Subgroup.centralizer (K : Set G) with hV
  set W : Subgroup G := V ⊓ V.comap (MulAut.conj r).toMonoidHom with hW
  have hmemW : ∀ g : G, g ∈ W ↔ g ∈ V ∧ r * g * r⁻¹ ∈ V := fun g => by
    simp [hW, MulAut.conj_apply]
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  intro v hv hrv
  by_contra hv1
  have hWp : IsPGroup p W := hcfg.isPGroup.to_le (inf_le_left.trans inf_le_left)
  have hpW : p ∣ Nat.card W := by
    rcases hWp.card_eq_or_dvd with h | h
    · exfalso
      rw [Subgroup.card_eq_one] at h
      have hvW : v ∈ W := (hmemW v).mpr ⟨hv, hrv⟩
      rw [h] at hvW
      exact hv1 hvW
    · exact h
  have hxW : Subgroup.zpowers x ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.zpowers_le]
    apply mem_normalizer_of_forall_conj_mem
    intro w hw
    obtain ⟨hwV, hrwV⟩ := (hmemW w).mp hw
    refine (hmemW _).mpr ⟨?_, ?_⟩
    · have h1 := hcfg.conj_mem_V (U.inv_mem hxU) hwV
      rw [inv_inv] at h1
      exact h1
    · have hrx : r * x⁻¹ * r⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp hr.1 _).mp (U.inv_mem hxU)
      have := hcfg.conj_mem_V hrx hrwV
      have e : r * (x⁻¹ * w * x) * r⁻¹ =
          r * x⁻¹ * r⁻¹ * (r * w * r⁻¹) * (r * x⁻¹ * r⁻¹)⁻¹ := by group
      rw [e]
      exact this
  have hxp : ∀ g ∈ Subgroup.zpowers x, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (W : Set G) := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, ?_⟩
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcfg.x_pow,
      one_zpow]
    exact one_mem _
  obtain ⟨w, hwW, hw1, hwx⟩ := exists_ne_one_mem_centralizer hpW hxW hxp
  have hwU : w ∈ U := ((hmemW w).mp hwW).1.1
  obtain ⟨n, hn⟩ := hcfg.isPGroup ⟨w, hwU⟩
  have hwn : w ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨m, he1, hep⟩ := exists_pow_pow_ne_one ⟨n, hwn⟩ hw1
  set e := w ^ p ^ m with he
  have heW : e ∈ W := W.pow_mem hwW _
  obtain ⟨heV, hreV⟩ := (hmemW e).mp heW
  have hwx' : w * x = x * w :=
    ((Subgroup.mem_centralizer_iff.mp hwx) x (Subgroup.mem_zpowers x)).symm
  have hex : e * x = x * e := (Commute.pow_left hwx' _).eq
  have heBs : e ∈ Bs := hcfg.mem_of_commute heV.1 hex hep
  have heB₁ := hcfg.inf_part_le hB₁U₁ hxU₁ ⟨heBs, hVU₁ heV⟩
  have hed : e ∈ Subgroup.zpowers d := hC ⟨heB₁, heV.2⟩
  have hreB₁ : r * e * r⁻¹ ∈ Bs ⊓ Subgroup.centralizer (X : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hr.2 e).mp heB₁
  have hred : r * e * r⁻¹ ∈ Subgroup.zpowers d := hC ⟨hreB₁, hreV.2⟩
  exact hrd (mem_normalizer_zpowers_of_conj_mem hcfg.d_pow hed he1 hred)

theorem ggL45_omega_conj_V_of_comm_of_cent (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hC : Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.zpowers d)
    (hcomm : ∀ z ∈ U₁, z ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) →
      x * z * x⁻¹ * z⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G)) {r : G}
    (hr : r ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    (hrd : r ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G)) {z : G}
    (hzV : r⁻¹ * z * r ∈ U ⊓ Subgroup.centralizer (K : Set G)) (hzU₁ : z ∈ U₁)
    (hzp : z ^ p = 1) : z ∈ Subgroup.zpowers (r * d * r⁻¹) := by
  obtain ⟨hB₁U₁, hxU₁, -⟩ := ggL4546_basic hraw hiso hcfg
  have hii := ggL45_inf_conj_eq_one_of_cent hraw hiso hcfg hC hr hrd
  have hzU : z ∈ U := hcfg.part_le hzU₁
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have hV1 : (1 : G) ∈ U ⊓ Subgroup.centralizer (K : Set G) := one_mem _
  have ht := hcomm z hzU₁ (hzp ▸ hV1)
  have hrx : r⁻¹ * x * r ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hr.1) x).mp hxU
    rwa [inv_inv] at this
  have ht' : r⁻¹ * (x * z * x⁻¹ * z⁻¹) * r ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
    have h1 := hcfg.conj_mem_V hrx hzV
    have e : r⁻¹ * (x * z * x⁻¹ * z⁻¹) * r =
        (r⁻¹ * x * r) * (r⁻¹ * z * r) * (r⁻¹ * x * r)⁻¹ * (r⁻¹ * z * r)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hzV)
  have h1 := hii _ ht' (by simpa [mul_assoc] using ht)
  have hxz : z * x = x * z := by
    have : x * z * x⁻¹ * z⁻¹ = 1 := by
      have := congrArg (fun g => r * g * r⁻¹) h1
      simpa [mul_assoc] using this
    have h2 := congrArg (· * (z * x)) this
    simp only [one_mul] at h2
    rw [← h2]
    group
  have hzBs := hcfg.mem_of_commute hzU hxz hzp
  have hzB₁ := hcfg.inf_part_le hB₁U₁ hxU₁ ⟨hzBs, hzU₁⟩
  have hrz : r⁻¹ * z * r ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hr.2) z).mp hzB₁
    rwa [inv_inv] at this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hC ⟨hrz, hzV.2⟩)
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [conj_zpow, hk]
  group

theorem ggL45_comm_mem_zpowers_of_comm_of_cent (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hC : Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.zpowers d)
    (hcomm : ∀ z ∈ U₁, z ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) →
      x * z * x⁻¹ * z⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G)) {n : G}
    (hn : n ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    (hnd : n ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    {v : G} (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) {a : G} (ha : a ∈ U₁)
    (hap : (a * (n * v * n⁻¹) * a⁻¹ * (n * v * n⁻¹)⁻¹) ^ p ∈
      U ⊓ Subgroup.centralizer (K : Set G)) :
    a * (n * v * n⁻¹) * a⁻¹ * (n * v * n⁻¹)⁻¹ ∈ Subgroup.zpowers (n * d * n⁻¹) := by
  have hwU : n * v * n⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hn.1 v).mp hv.1
  have hii := ggL45_inf_conj_eq_one_of_cent hraw hiso hcfg hC hn hnd
  set w := n * v * n⁻¹ with hwdef
  have hcU₁ : a * w * a⁻¹ * w⁻¹ ∈ U₁ := by
    have := U₁.mul_mem ha (hcfg.conj_mem_part hwU (U₁.inv_mem ha))
    simpa [mul_assoc] using this
  have hnaU : n⁻¹ * a * n ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn.1) a).mp (hcfg.part_le ha)
    rwa [inv_inv] at this
  have hcV : n⁻¹ * (a * w * a⁻¹ * w⁻¹) * n ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
    have e : n⁻¹ * (a * w * a⁻¹ * w⁻¹) * n =
        (n⁻¹ * a * n) * v * (n⁻¹ * a * n)⁻¹ * v⁻¹ := by
      rw [hwdef]
      group
    rw [e]
    exact Subgroup.mul_mem _ (hcfg.conj_mem_V hnaU hv) (Subgroup.inv_mem _ hv)
  have hc1 : (a * w * a⁻¹ * w⁻¹) ^ p = 1 := by
    have hpV : n⁻¹ * (a * w * a⁻¹ * w⁻¹) ^ p * n ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
      have e := (conj_pow (a := n⁻¹) (b := a * w * a⁻¹ * w⁻¹) (i := p)).symm
      rw [inv_inv] at e
      rw [e]
      exact Subgroup.pow_mem _ hcV p
    have h1 := hii _ hpV (by
      rw [show n * (n⁻¹ * (a * w * a⁻¹ * w⁻¹) ^ p * n) * n⁻¹ = (a * w * a⁻¹ * w⁻¹) ^ p by
        group]
      exact hap)
    have := congrArg (fun g => n * g * n⁻¹) h1
    simpa [mul_assoc] using this
  exact ggL45_omega_conj_V_of_comm_of_cent hraw hiso hcfg hC hcomm hn hnd hcV hcU₁ hc1

theorem ggL45_omega_V_of_conj_of_cent (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hC : Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.zpowers d)
    (hcomm : ∀ z ∈ U₁, z ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) →
      x * z * x⁻¹ * z⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G))
    (hconj : ∀ n ∈ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      ∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G), n * v * n⁻¹ ∈ U₁) {v : G}
    (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) (hvp : v ^ p = 1) :
    v ∈ Subgroup.zpowers d := by
  obtain ⟨r, hr, hrd⟩ := ggL45_exists_moving hcfg.1 hcfg.2.1 hcfg.2.2.1 hcfg.2.2.2.2.2.1
    hcfg.2.2.2.2.2.2.1
  have hr' : r⁻¹ ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) :=
    inv_mem hr
  have hrd' : r⁻¹ ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) := fun h =>
    hrd (by simpa using inv_mem h)
  have hzU₁ : r⁻¹ * v * r ∈ U₁ := by
    have := hconj _ hr' v hv
    rwa [inv_inv] at this
  have hzV : (r⁻¹)⁻¹ * (r⁻¹ * v * r) * r⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
    simpa [mul_assoc] using hv
  have hzp : (r⁻¹ * v * r) ^ p = 1 := by
    have e := conj_pow (a := r⁻¹) (b := v) (i := p)
    rw [inv_inv] at e
    rw [e, hvp]
    group
  have h := ggL45_omega_conj_V_of_comm_of_cent hraw hiso hcfg hC hcomm hr' hrd' hzV hzU₁ hzp
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [conj_zpow, inv_inv] at hk
  have := congrArg (fun g => r * g * r⁻¹) hk
  simpa [mul_assoc] using this

end Moving

@[expose] def GGL45MovingIOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCase p B Bs x L D J X → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
      GGTableBModule p Bs x L B₂ → GGL43 Bs x X → GGL44i p Bs x X → GGL44ii Bs x X B₂ →
      GGL44iii p B Bs x D J X d y K → GGL45Setup p Bs X U → GGInnerDiagPart U K U₁ →
      Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
        Subgroup.normalizer (U₁ : Set G) →
      ∀ r ∈ Subgroup.normalizer (U : Set G) ⊓
          Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
        r ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
          r ∈ Subgroup.normalizer (U₁ : Set G)

@[expose] def GGL45IOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U : Subgroup G),
    GGFieldCase p B Bs x L D J X → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
      GGTableBModule p Bs x L B₂ → GGL43 Bs x X → GGL44i p Bs x X → GGL44ii Bs x X B₂ →
      GGL44iii p B Bs x D J X d y K → GGL45Setup p Bs X U →
      U ≤ Subgroup.normalizer (K : Set G) →
      ∃ U₁ : Subgroup G, GGInnerDiagPart U K U₁ ∧
        Subgroup.normalizer (U : Set G) ⊓
            Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ≤
          Subgroup.normalizer (U₁ : Set G)

theorem ggL45IOneInput_of_moving (hN : GGInndiagNormalInput) (hsub : GGRawInnSubgroupInput)
    (hmov : GGL45MovingIOneInput) : GGL45IOneInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U hFC hI1 hTBM hL43 hL44 hL44ii hK hsetup hUK
  have hM1 := largeEvenMarking_and_labelAll_simple (S := fun _ => True) (P' := GGRawInnSubgroup)
    (fun lab hl _ => hsub lab hl) (fun _ _ _ _ _ _ _ => trivial) hK.2.2.2.2
  have hM2 := largeEvenMarking_and_labelAll_simple (S := fun _ => True)
    (P' := fun R _ I _ => GGInndiagNormal R I) (fun lab hl _ => hN lab hl)
    (fun _ _ _ _ _ _ _ => trivial) hM1
  obtain ⟨U₁, hU₁⟩ := ggL45_marking_exists_of (X := ↥K)
    (P' := fun U₁ _ _ _ I _ θ => U₁ ≤ U ∧
      (∀ u ∈ U, u ∈ U₁ ↔
        ∃ φ ∈ I, LargeEvenInduces θ (fun k k' => (k' : G) = u⁻¹ * k * u) φ) ∧
      Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
        Subgroup.normalizer (U₁ : Set G))
    (fun _ _ _ I _ θ h => by
      obtain ⟨⟨-, hmul, hinv, hinn⟩, hNn⟩ := h
      exact ⟨ggInnerDiagPartOf K θ I U, inf_le_left,
        fun u hu => mem_ggInnerDiagPartOf_iff hmul hinv hinn hUK hu,
        normalizer_inf_le_normalizer_ggInnerDiagPartOf hNn U⟩) hM2
  obtain ⟨-, lab, -, hraw'⟩ := id hU₁
  obtain ⟨R, _, I, F, -, -, θ, hle, -, hon⟩ := largeEvenRawDatum_exists hraw'
  have hpart : GGInnerDiagPart U K U₁ :=
    ⟨hUK, hle, largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2.1) hU₁⟩
  refine ⟨U₁, hpart, fun r hr => ?_⟩
  by_cases hrd : r ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)
  · exact hon ⟨hr.1, ggL45_normalizer_le_of_canonical hFC hK ⟨hr.2, hrd⟩⟩
  · exact hmov G p B Bs x L D J X B₂ d y K U U₁ hFC hI1 hTBM hL43 hL44 hL44ii hK hsetup hpart hon
      r hr hrd

end CFSG.StandardType

end
