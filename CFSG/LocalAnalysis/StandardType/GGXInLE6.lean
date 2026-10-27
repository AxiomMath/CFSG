module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKGFrameE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModule
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.StandardType.GGXInL

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.E6ThreeModel CFSG.StandardType.TableBExc.E6Three

private lemma lup8e_nbar_le_normalizer {R : Type} [Group R] (D : FrameData R) (hD : D.Good) :
    Subgroup.closure (↑D.Tor ∪ Set.range D.nb) ≤ Subgroup.normalizer (D.V0 : Set R) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro z (hz | ⟨i, rfl⟩)
  · refine (Subgroup.centralizer_le_normalizer (D.V0 : Set R)) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hD.torus.1 z hz y (D.V0_le_Tor hy)).symm
  · change D.nb i ∈ Subgroup.normalizer (D.V0 : Set R)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨_, v, hv, hyv⟩ := (FrameData.mem_V0 D).1 hy
      rw [FrameData.mem_V0]
      refine ⟨hD.weyl.2.1 i y (D.V0_le_Tor hy), ?_⟩
      refine ⟨adRefl .E6 3 i v, adRefl_mem_hypE6 hv i, ?_⟩
      rw [map_mul, map_mul, map_inv, hyv]
      exact hD.weyl.2.2.1 i v
    · intro hy
      have hni : (D.nb i)⁻¹ = D.nb i := inv_eq_of_mul_eq_one_right (hD.weyl.1 i)
      have hx : D.nb i * (D.nb i * y * (D.nb i)⁻¹) * (D.nb i)⁻¹ = y := by
        calc D.nb i * (D.nb i * y * (D.nb i)⁻¹) * (D.nb i)⁻¹
            = (D.nb i * D.nb i) * y * ((D.nb i)⁻¹ * (D.nb i)⁻¹) := by group
          _ = y := by rw [hD.weyl.1 i, one_mul, hni, hD.weyl.1 i, mul_one]
      obtain ⟨_, v, hv, hyv⟩ := (FrameData.mem_V0 D).1 hy
      rw [FrameData.mem_V0]
      refine ⟨?_, ?_⟩
      · rw [← hx]
        exact hD.weyl.2.1 i _ (D.V0_le_Tor hy)
      · refine ⟨adRefl .E6 3 i v, adRefl_mem_hypE6 hv i, ?_⟩
        rw [← hx, map_mul, map_mul, map_inv, hyv]
        exact hD.weyl.2.2.1 i v

private theorem lup8e_conj_injective {G : Type} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G → MulAut G) := by
  intro a b hab
  have h : ∀ g : G, a * g * a⁻¹ = b * g * b⁻¹ := fun g =>
    congrArg (fun f : MulAut G => f g) hab
  have hcenter : b⁻¹ * a ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := h g
    have h2 : (b⁻¹ * a) * g * (a⁻¹ * b) = g := by
      calc (b⁻¹ * a) * g * (a⁻¹ * b) = b⁻¹ * (a * g * a⁻¹) * b := by group
        _ = b⁻¹ * (b * g * b⁻¹) * b := by rw [hg]
        _ = g := by group
    have h3 : (b⁻¹ * a) * g * (b⁻¹ * a)⁻¹ = g := by
      rwa [mul_inv_rev, inv_inv]
    have hcomm : (b⁻¹ * a) * g = g * (b⁻¹ * a) := mul_inv_eq_iff_eq_mul.mp h3
    exact hcomm.symm
  have hbot : b⁻¹ * a ∈ (⊥ : Subgroup G) := by simpa [hZ] using hcenter
  have h1 : b⁻¹ * a = 1 := Subgroup.mem_bot.mp hbot
  exact (inv_mul_eq_one.mp h1).symm

private theorem lup8e_ad_injective {R : Type} [Group R] (D : FrameData R) (hD : D.Good) :
    Function.Injective D.ad :=
  fun x y h => Multiplicative.ofAdd.injective (hD.faithful h)

private noncomputable def lup8e_eVec {R : Type} [Group R] (D : FrameData R)
    (hD : D.Good) (r : D.V0) : (Fin Tag.E6.rank → ZMod 3) :=
  Classical.choose r.2.2

private theorem lup8e_eVec_mem {R : Type} [Group R] (D : FrameData R)
    (hD : D.Good) (r : D.V0) : lup8e_eVec D hD r ∈ NoOffRest.hypE6 :=
  (Classical.choose_spec r.2.2).1

private theorem lup8e_eVec_conj {R : Type} [Group R] (D : FrameData R)
    (hD : D.Good) (r : D.V0) :
    MulAut.conj (r : R) = D.ad (lup8e_eVec D hD r) :=
  (Classical.choose_spec r.2.2).2

private theorem lup8e_eVec_inj {R : Type} [Group R] (D : FrameData R)
    (hD : D.Good) : Function.Injective (lup8e_eVec D hD) := by
  intro r r' h
  have hconj : Function.Injective (MulAut.conj : R → MulAut R) :=
    lup8e_conj_injective hD.center
  apply Subtype.ext
  apply hconj
  calc MulAut.conj (r : R) = D.ad (lup8e_eVec D hD r) := lup8e_eVec_conj D hD r
    _ = D.ad (lup8e_eVec D hD r') := by rw [h]
    _ = MulAut.conj (r' : R) := (lup8e_eVec_conj D hD r').symm

private theorem lup8e_eVec_bijective {R : Type} [Group R] (D : FrameData R)
    (hD : D.Good) :
    Function.Bijective (fun r : D.V0 => (⟨lup8e_eVec D hD r, lup8e_eVec_mem D hD r⟩ :
      NoOffRest.hypE6)) := by
  constructor
  · intro r r' h
    exact lup8e_eVec_inj D hD (Subtype.ext_iff.mp h)
  · intro v
    obtain ⟨r, hrT, -, hconj⟩ := hD.inner v v.2
    refine ⟨⟨r, ⟨hrT, v, v.2, hconj⟩⟩, ?_⟩
    apply Subtype.ext
    apply lup8e_ad_injective D hD
    exact (lup8e_eVec_conj D hD ⟨r, ⟨hrT, v, v.2, hconj⟩⟩).symm.trans hconj

private noncomputable def lup8e_equiv {R : Type} [Group R] (D : FrameData R)
    (hD : D.Good) : D.V0 ≃ NoOffRest.hypE6 :=
  Equiv.ofBijective _ (lup8e_eVec_bijective D hD)

private noncomputable def lup8e_act {R : Type} [Group R] (D : FrameData R)
    (hD : D.Good) :
    Subgroup.closure (↑D.Tor ∪ Set.range D.nb) →* Equiv.Perm D.V0 :=
  (MulAut.toPerm D.V0).comp
    ((Subgroup.normalizerMonoidHom D.V0).comp
      (Subgroup.inclusion (lup8e_nbar_le_normalizer D hD)))

private theorem lup8e_norm_hyp {R : Type} [Group R] (D : FrameData R) (hD : D.Good)
    (r : R) (hr : r ∈ Subgroup.closure (↑D.Tor ∪ Set.range D.nb)) :
    ∀ x ∈ NoOffRest.hypE6, ∃ y ∈ NoOffRest.hypE6,
      MulAut.conj r * D.ad x * (MulAut.conj r)⁻¹ = D.ad y := by
  have htor : ∀ t ∈ D.Tor, ∀ x ∈ NoOffRest.hypE6, ∃ y ∈ NoOffRest.hypE6,
      MulAut.conj t * D.ad x * (MulAut.conj t)⁻¹ = D.ad y := by
    intro t ht x hx
    refine ⟨x, hx, ?_⟩
    have hcomm : MulAut.conj t * D.ad x = D.ad x * MulAut.conj t := by
      ext z
      simp only [MulAut.mul_apply, MulAut.conj_apply]
      rw [map_mul, map_mul, map_inv, hD.torus.2.2 x t ht]
    calc MulAut.conj t * D.ad x * (MulAut.conj t)⁻¹
        = (D.ad x * MulAut.conj t) * (MulAut.conj t)⁻¹ := by rw [hcomm]
      _ = D.ad x := by group
  have hnb : ∀ i, ∀ x ∈ NoOffRest.hypE6, ∃ y ∈ NoOffRest.hypE6,
      MulAut.conj (D.nb i) * D.ad x * (MulAut.conj (D.nb i))⁻¹ = D.ad y :=
    fun i x hx => ⟨adRefl .E6 3 i x, adRefl_mem_hypE6 hx i, hD.weyl.2.2.1 i x⟩
  induction hr using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with hxT | ⟨i, rfl⟩
    · exact htor x hxT
    · exact hnb i
  | inv_mem x hx =>
    rcases hx with hxT | ⟨i, rfl⟩
    · exact htor x⁻¹ (D.Tor.inv_mem hxT)
    · have hinv : (D.nb i)⁻¹ = D.nb i := inv_eq_of_mul_eq_one_right (hD.weyl.1 i)
      rw [hinv]
      exact hnb i
  | one => exact fun y hy => ⟨y, hy, by simp⟩
  | mul a b _ _ ha hb =>
    intro y hy
    obtain ⟨z, hz, hz'⟩ := hb y hy
    obtain ⟨w, hw, hw'⟩ := ha z hz
    refine ⟨w, hw, ?_⟩
    calc MulAut.conj (a * b) * D.ad y * (MulAut.conj (a * b))⁻¹
        = MulAut.conj a * (MulAut.conj b * D.ad y * (MulAut.conj b)⁻¹) * (MulAut.conj a)⁻¹ := by
          simp only [map_mul]
          group
      _ = MulAut.conj a * D.ad z * (MulAut.conj a)⁻¹ := by rw [hz']
      _ = D.ad w := hw'

private theorem lup8e_adAct_eq_of_eq_on_hypE6
    {u v : WeylGroup .E6}
    (h : ∀ x ∈ NoOffRest.hypE6, adAct .E6 3 u x = adAct .E6 3 v x) : u = v := by
  have huv : u * v⁻¹ = 1 := by
    apply eq_one_of_adAct_eq_on_hypE6
    intro x hx
    rw [adAct_mul]
    have hx' : adAct .E6 3 v⁻¹ x ∈ NoOffRest.hypE6 := NoOffRest.adAct_mem_hypE6 v⁻¹ hx
    rw [h _ hx']
    rw [← adAct_mul, mul_inv_cancel, adAct_one]
  exact mul_inv_eq_one.mp huv

private noncomputable abbrev lup8e_phiFun
    {R : Type} [Group R] (D : FrameData R) (hD : D.Good)
    (r : Subgroup.closure (↑D.Tor ∪ Set.range D.nb)) : WeylGroup .E6 :=
  Classical.choose (hD.norm (r : R) NoOffRest.hypE6 (Or.inr rfl)
    (lup8e_norm_hyp D hD (r : R) r.2))

private noncomputable def lup8e_phi
    {R : Type} [Group R] (D : FrameData R) (hD : D.Good) :
    Subgroup.closure (↑D.Tor ∪ Set.range D.nb) →* WeylGroup .E6 where
  toFun := lup8e_phiFun D hD
  map_one' := by
    apply lup8e_adAct_eq_of_eq_on_hypE6
    intro x hx
    apply lup8e_ad_injective D hD
    have h := Classical.choose_spec (hD.norm (1 : R) NoOffRest.hypE6 (Or.inr rfl)
      (lup8e_norm_hyp D hD (1 : R) (Subgroup.one_mem _))) x hx
    rw [← h, adAct_one]
    simp
  map_mul' a b := by
    apply lup8e_adAct_eq_of_eq_on_hypE6
    intro x hx
    apply lup8e_ad_injective D hD
    have ha := Classical.choose_spec (hD.norm (a : R) NoOffRest.hypE6 (Or.inr rfl)
      (lup8e_norm_hyp D hD (a : R) a.2)) x hx
    have hb := Classical.choose_spec (hD.norm (b : R) NoOffRest.hypE6 (Or.inr rfl)
      (lup8e_norm_hyp D hD (b : R) b.2)) x hx
    have hab := Classical.choose_spec
      (hD.norm ((a * b : Subgroup.closure (↑D.Tor ∪ Set.range D.nb)) : R)
        NoOffRest.hypE6 (Or.inr rfl)
        (lup8e_norm_hyp D hD ((a * b : Subgroup.closure (↑D.Tor ∪ Set.range D.nb)) : R)
          (a * b).2)) x hx
    have ha' := Classical.choose_spec (hD.norm (a : R) NoOffRest.hypE6 (Or.inr rfl)
      (lup8e_norm_hyp D hD (a : R) a.2)) (adAct .E6 3 (lup8e_phiFun D hD b) x)
      (NoOffRest.adAct_mem_hypE6 (lup8e_phiFun D hD b) hx)
    rw [← hab]
    calc MulAut.conj (((a * b : Subgroup.closure (↑D.Tor ∪ Set.range D.nb)) : R)) * D.ad x *
          (MulAut.conj (((a * b : Subgroup.closure (↑D.Tor ∪ Set.range D.nb)) : R)))⁻¹
        = MulAut.conj (a : R) * (MulAut.conj (b : R) * D.ad x * (MulAut.conj (b : R))⁻¹) *
          (MulAut.conj (a : R))⁻¹ := by
          rw [Subgroup.coe_mul, map_mul]
          group
      _ = MulAut.conj (a : R) * D.ad (adAct .E6 3 (lup8e_phiFun D hD b) x) *
          (MulAut.conj (a : R))⁻¹ := by rw [hb]
      _ = D.ad (adAct .E6 3 (lup8e_phiFun D hD a) (adAct .E6 3 (lup8e_phiFun D hD b) x)) := by
        rw [ha']
      _ = D.ad (adAct .E6 3 (lup8e_phiFun D hD a * lup8e_phiFun D hD b) x) := by rw [← adAct_mul]

private theorem lup8e_phi_range
    {R : Type} [Group R] (D : FrameData R) (hD : D.Good) :
    (lup8e_phi D hD).range = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro w
  refine weyl_induction (P := fun w => w ∈ (lup8e_phi D hD).range) ?_ ?_ w
  · exact ⟨1, by rw [map_one]⟩
  · intro i w hw
    obtain ⟨n, hn⟩ := hw
    let ni : Subgroup.closure (↑D.Tor ∪ Set.range D.nb) :=
      ⟨D.nb i, Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)⟩
    refine ⟨ni * n, ?_⟩
    rw [map_mul, hn]
    congr 1
    apply lup8e_adAct_eq_of_eq_on_hypE6
    intro x hx
    apply lup8e_ad_injective D hD
    have h := Classical.choose_spec (hD.norm (D.nb i) NoOffRest.hypE6 (Or.inr rfl)
      (lup8e_norm_hyp D hD (D.nb i) ni.2)) x hx
    change D.ad (adAct .E6 3 (lup8e_phiFun D hD ni) x) =
      D.ad (adAct .E6 3 (simple .E6 i) x)
    rw [← h, hD.weyl.2.2.1 i x, adAct_simple]

private theorem lup8e_phi_ker
    {R : Type} [Group R] (D : FrameData R) (hD : D.Good) :
    (lup8e_phi D hD).ker =
      D.Tor.subgroupOf (Subgroup.closure (↑D.Tor ∪ Set.range D.nb)) := by
  apply le_antisymm
  · intro r hr
    rw [MonoidHom.mem_ker] at hr
    rw [Subgroup.mem_subgroupOf, ← hD.cent (r : R)]
    intro v hv
    have h : MulAut.conj (r : R) * D.ad v * (MulAut.conj (r : R))⁻¹ =
        D.ad (adAct .E6 3 (lup8e_phiFun D hD r) v) :=
      Classical.choose_spec (hD.norm (r : R) NoOffRest.hypE6 (Or.inr rfl)
        (lup8e_norm_hyp D hD (r : R) r.2)) v hv
    have hr' : lup8e_phiFun D hD r = 1 := hr
    rw [hr', adAct_one] at h
    have hcomm : MulAut.conj (r : R) * D.ad v = D.ad v * MulAut.conj (r : R) := by
      calc MulAut.conj (r : R) * D.ad v
          = MulAut.conj (r : R) * D.ad v * (MulAut.conj (r : R))⁻¹ * MulAut.conj (r : R) := by
            group
        _ = D.ad v * MulAut.conj (r : R) := by rw [h]
    have h2 : MulAut.conj ((D.ad v) (r : R)) = MulAut.conj (r : R) := by
      have h3 : MulAut.conj ((D.ad v) (r : R)) = (D.ad v) * MulAut.conj (r : R) * (D.ad v)⁻¹ := by
        ext z
        simp only [MulAut.mul_apply, MulAut.conj_apply]
        rw [map_mul, map_mul, map_inv]
        simp
      rw [h3, ← hcomm]
      group
    exact lup8e_conj_injective hD.center h2
  · intro r hr
    rw [Subgroup.mem_subgroupOf] at hr
    rw [MonoidHom.mem_ker]
    apply eq_one_of_adAct_eq_on_hypE6
    intro v hv
    have h := Classical.choose_spec (hD.norm (r : R) NoOffRest.hypE6 (Or.inr rfl)
      (lup8e_norm_hyp D hD (r : R) r.2)) v hv
    have h1 : (D.ad v) (r : R) = (r : R) := hD.torus.2.2 v (r : R) hr
    have hcomm : MulAut.conj (r : R) * D.ad v = D.ad v * MulAut.conj (r : R) := by
      have h2 : MulAut.conj ((D.ad v) (r : R)) = (D.ad v) * MulAut.conj (r : R) * (D.ad v)⁻¹ := by
        ext z
        simp only [MulAut.mul_apply, MulAut.conj_apply]
        rw [map_mul, map_mul, map_inv]
        simp
      rw [h1] at h2
      calc MulAut.conj (r : R) * D.ad v
          = ((D.ad v) * MulAut.conj (r : R) * (D.ad v)⁻¹) * D.ad v := by
            conv_lhs => rw [h2]
        _ = D.ad v * MulAut.conj (r : R) := by group
    have h3 : D.ad (adAct .E6 3 (lup8e_phiFun D hD r) v) = D.ad v := by
      rw [← h]
      calc MulAut.conj (r : R) * D.ad v * (MulAut.conj (r : R))⁻¹
          = (D.ad v * MulAut.conj (r : R)) * (MulAut.conj (r : R))⁻¹ := by rw [hcomm]
        _ = D.ad v := by group
    exact lup8e_ad_injective D hD h3
private theorem lup8e_tor_le_V0
    {R : Type} [Group R] [Finite R] (D : FrameData R)
    (hD : D.Good) (hTexp : ∀ t ∈ D.Tor, t ^ 3 = 1) (h3R : ¬ 3 ^ 10 ∣ Nat.card R) :
    D.Tor ≤ D.V0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Nbar : Subgroup R := Subgroup.closure (↑D.Tor ∪ Set.range D.nb)
  have hTor_pgroup : IsPGroup 3 D.Tor := fun t => ⟨1, by
    apply Subtype.ext
    simpa using hTexp (t : R) t.2⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).mp hTor_pgroup
  have hTor_le_Nbar : D.Tor ≤ Nbar := fun t ht => Subgroup.subset_closure (Or.inl ht)
  have hcard : Nat.card Nbar = Nat.card D.Tor * 51840 := by
    have h := Subgroup.card_ker_mul_card_range (lup8e_phi D hD)
    rw [lup8e_phi_ker D hD, lup8e_phi_range D hD, Subgroup.card_top] at h
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTor_le_Nbar).toEquiv,
      CFSG.RankThree.E6.card_weylGroup_E6] at h
    exact h.symm
  have hNbar_dvd : Nat.card Nbar ∣ Nat.card R := Subgroup.card_subgroup_dvd_card _
  have hdiv : Nat.card D.Tor * 51840 ∣ Nat.card R := hcard ▸ hNbar_dvd
  have hnot6 : ¬ 3 ^ 6 ∣ Nat.card D.Tor := by
    intro h6
    have h10 : 3 ^ 10 ∣ Nat.card D.Tor * 51840 := by
      have h4 : 3 ^ 4 ∣ 51840 := by norm_num
      calc 3 ^ 10 = 3 ^ 6 * 3 ^ 4 := by ring
        _ ∣ Nat.card D.Tor * 51840 := Nat.mul_dvd_mul h6 h4
    exact h3R (h10.trans hdiv)
  have hk6 : ¬ 3 ^ 6 ∣ 3 ^ k := by
    intro h
    exact hnot6 (hk.symm ▸ h)
  have hk5 : k ≤ 5 := by
    by_contra h
    have h6k : 6 ≤ k := by omega
    exact hk6 (pow_dvd_pow 3 h6k)
  have hcardTor : Nat.card D.Tor ≤ 3 ^ 5 := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk5
  have hcardV0 : Nat.card D.V0 = 3 ^ 5 := by
    have h := Nat.card_congr (lup8e_equiv D hD)
    rwa [NoOffRest.card_hypE6] at h
  have hcard_le : Nat.card D.Tor ≤ Nat.card D.V0 := by rw [hcardV0]; exact hcardTor
  exact (Subgroup.eq_of_le_of_card_ge D.V0_le_Tor hcard_le).ge

private theorem lup8e_coxeterMatrix_E6 :
    CoxeterMatrix.E₆ = CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E6) := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E6 = CartanMatrix.E 6 := cartanE_eq 6
  exact (coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E6)
    (M := CoxeterMatrix.E₆) (isFiniteType_cartan .E6) (hc.symm ▸ ggIntCartan_E₆)).symm

theorem e6_transfer_frame
    {R : Type} [Group R] [Finite R] {L' : Type} [Group L'] [Finite L']
    (D : FrameData R) (hAL : GGAbelianLift) (hD : D.Good) (hTexp : ∀ t ∈ D.Tor, t ^ 3 = 1)
    (h3R : ¬ 3 ^ 10 ∣ Nat.card R)
    (hperf : commutator L' = ⊤) {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hcard : Nat.card ψ.ker = 3)
    {ρ : MulAut L' →* MulAut R} (hρ : ∀ a l, ρ a (ψ l) = ψ (a l)) (hρinj : Function.Injective ρ)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) (hsc : GGTorusSelfCent 3 A)
    (hal : ∀ a ∈ A, ρ a ∈ D.diag.range) :
    ∃ (T N : Subgroup L') (hn : (T.subgroupOf N).Normal), T ≤ N ∧ ψ.ker ≤ T ∧
      (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) ∧ (∀ t ∈ T, t ^ 3 = 1) ∧
      (∀ a ∈ A, ∀ t ∈ T, a t = t) ∧ (∀ n ∈ N, ∀ a ∈ A, n * (a n)⁻¹ ∈ T) ∧
      (haveI := hn; Nonempty (CoxeterSystem CoxeterMatrix.E₆ (N ⧸ T.subgroupOf N))) ∧
      ¬ 3 ∣ N.index := by
  have hodd : Odd (Nat.card ψ.ker) := by rw [hcard]; decide
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g.1 g.2)⟩
  choose w hw hw2 using fun i => exists_weyl_lift_odd D hD.weyl hψ hker hodd i
  obtain ⟨hTab, hTfix, hcube⟩ :=
    abelianLift_apply D hAL hD hψ hker (Or.inr hcard) hρ hAp hal hw
  have hTV : D.Tor ≤ D.V0 := lup8e_tor_le_V0 D hD hTexp h3R
  let T : Subgroup L' := D.Tor.comap ψ
  let N : Subgroup L' := Subgroup.closure (↑T ∪ Set.range w)
  have hTN : T ≤ N := fun t ht => Subgroup.subset_closure (Or.inl ht)
  have hkerT : ψ.ker ≤ T := fun z hz => by
    rw [Subgroup.mem_comap, (MonoidHom.mem_ker).1 hz]; exact D.Tor.one_mem
  have hTex : ∀ t ∈ T, t ^ 3 = 1 := fun t ht => hcube t (hTV ht)
  have hFix : ∀ a ∈ A, ∀ t ∈ T, a t = t := hTfix
  have hmem_nb : ∀ i, w i ∈ Subgroup.normalizer (T : Set L') := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      change ψ ((w i) * h * (w i)⁻¹) ∈ D.Tor
      rw [map_mul, map_mul, map_inv, hw i]
      exact hD.weyl.2.1 i (ψ h) (by rwa [Subgroup.mem_comap] at hh)
    · intro hh
      change ψ ((w i) * h * (w i)⁻¹) ∈ D.Tor at hh
      change ψ h ∈ D.Tor
      rw [map_mul, map_mul, map_inv, hw i] at hh
      have h1 := hD.weyl.2.1 i ((D.nb i) * ψ h * (D.nb i)⁻¹) hh
      have hinv : (D.nb i)⁻¹ = D.nb i := inv_eq_of_mul_eq_one_right (hD.weyl.1 i)
      have heq : D.nb i * ((D.nb i) * ψ h * (D.nb i)⁻¹) * (D.nb i)⁻¹ = ψ h := by
        rw [hinv]
        calc D.nb i * ((D.nb i) * ψ h * D.nb i) * D.nb i
            = (D.nb i * ((D.nb i) * ψ h)) * D.nb i * D.nb i := by rw [← mul_assoc]
          _ = ((D.nb i * D.nb i) * ψ h) * D.nb i * D.nb i := by rw [← mul_assoc]
          _ = ψ h * D.nb i * D.nb i := by rw [hD.weyl.1 i, one_mul]
          _ = ψ h * (D.nb i * D.nb i) := by rw [mul_assoc]
          _ = ψ h := by rw [hD.weyl.1 i, mul_one]
      rw [heq] at h1
      exact h1
  have hNnormT : N ≤ Subgroup.normalizer (T : Set L') := by
    rw [show N = Subgroup.closure (↑T ∪ Set.range w) from rfl]
    refine (Subgroup.closure_le _).2 ?_
    rintro z (hz | ⟨i, rfl⟩)
    · exact Subgroup.le_normalizer hz
    · exact hmem_nb i
  haveI hn : (T.subgroupOf N).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNnormT
  have hCob : ∀ n ∈ N, ∀ a ∈ A, n * (a n)⁻¹ ∈ T := by
    intro n hn
    refine Subgroup.closure_induction (p := fun x _ => ∀ a ∈ A, x * (a x)⁻¹ ∈ T) ?_ ?_ ?_ ?_ hn
    · rintro x (hxT | ⟨i, rfl⟩) a ha
      · rw [hFix a ha x hxT, mul_inv_cancel]
        exact T.one_mem
      · exact (coboundary_clause D hAL hD hψ hker (Or.inr hcard) hρ hAp hal hw i a ha).1
    · intro a ha
      simpa using T.one_mem
    · intro x y hx hy ihx ihy a ha
      have hxN : x ∈ Subgroup.normalizer (T : Set L') := hNnormT hx
      have ht_y : y * (a y)⁻¹ ∈ T := ihy a ha
      have ht_x : x * (a x)⁻¹ ∈ T := ihx a ha
      have hconj : x * (y * (a y)⁻¹) * x⁻¹ ∈ T :=
        ((Subgroup.mem_normalizer_iff).1 hxN (y * (a y)⁻¹)).1 ht_y
      have hprod : x * (y * (a y)⁻¹) * x⁻¹ * (x * (a x)⁻¹) ∈ T := T.mul_mem hconj ht_x
      have heq : x * (y * (a y)⁻¹) * x⁻¹ * (x * (a x)⁻¹) = x * y * (a (x * y))⁻¹ := by
        rw [map_mul, mul_inv_rev]
        group
      rwa [heq] at hprod
    · intro x hx ihx a ha
      have hxN : x ∈ Subgroup.normalizer (T : Set L') := hNnormT hx
      have hxinvN : x⁻¹ ∈ Subgroup.normalizer (T : Set L') := Subgroup.inv_mem _ hxN
      have ht : x * (a x)⁻¹ ∈ T := ihx a ha
      have htinv : (x * (a x)⁻¹)⁻¹ ∈ T := Subgroup.inv_mem _ ht
      have hconj : x⁻¹ * (x * (a x)⁻¹)⁻¹ * x ∈ T :=
        ((Subgroup.mem_normalizer_iff'').1 hxN ((x * (a x)⁻¹)⁻¹)).1 htinv
      have heq : x⁻¹ * (x * (a x)⁻¹)⁻¹ * x = x⁻¹ * (a (x⁻¹))⁻¹ := by
        rw [map_inv]
        group
      rwa [heq] at hconj
  let Nbar : Subgroup R := Subgroup.closure (↑D.Tor ∪ Set.range D.nb)
  have hψN_mem : ∀ (x : L'), x ∈ Subgroup.closure (↑T ∪ Set.range w) → ψ x ∈ Nbar := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hyT | ⟨i, rfl⟩
      · exact Subgroup.subset_closure (Or.inl (Subgroup.mem_comap.mp hyT))
      · rw [hw i]
        exact Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
    | one => simpa using Nbar.one_mem
    | mul a b _ _ ha hb => rw [map_mul]; exact Nbar.mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact Nbar.inv_mem ha
  let ψN : N →* Nbar :=
    { toFun := fun n => ⟨ψ (n : L'), hψN_mem (n : L') n.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [map_mul] }
  have hψN_surj : Function.Surjective ψN := by
    rintro ⟨x, hx⟩
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hyT | ⟨i, rfl⟩
      · obtain ⟨l, hl⟩ := hψ y
        have hlT : l ∈ T := by rw [Subgroup.mem_comap]; rw [hl]; exact hyT
        exact ⟨⟨l, hTN hlT⟩, Subtype.ext hl⟩
      · exact ⟨⟨w i, Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)⟩, Subtype.ext (hw i)⟩
    | one => exact ⟨1, by ext; simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨na, hna⟩ := ha
      obtain ⟨nb, hnb⟩ := hb
      exact ⟨na * nb, by rw [map_mul, hna, hnb]; rfl⟩
    | inv a _ ha =>
      obtain ⟨na, hna⟩ := ha
      refine ⟨na⁻¹, ?_⟩
      rw [map_inv, hna]
      rfl
  let Φ : N →* WeylGroup .E6 := (lup8e_phi D hD).comp ψN
  have hΦker : Φ.ker = T.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    constructor
    · intro h
      have hmem : ψN n ∈ (lup8e_phi D hD).ker := h
      rw [lup8e_phi_ker D hD] at hmem
      rw [Subgroup.mem_subgroupOf] at hmem
      exact hmem
    · intro h
      rw [← MonoidHom.mem_ker, lup8e_phi_ker D hD, Subgroup.mem_subgroupOf]
      exact h
  have hΦrange : Φ.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro w
    obtain ⟨nbar, hnbar⟩ := (MonoidHom.range_eq_top.mp (lup8e_phi_range D hD)) w
    obtain ⟨n, hn⟩ := hψN_surj nbar
    exact ⟨n, by rw [MonoidHom.comp_apply, hn, hnbar]⟩
  refine ⟨T, N, hn, hTN, hkerT, hTab, hTex, hFix, hCob, ?_, ?_⟩
  ·
    let e : (N ⧸ T.subgroupOf N) ≃* WeylGroup .E6 :=
      QuotientGroup.liftEquiv (T.subgroupOf N) (MonoidHom.range_eq_top.mp hΦrange) hΦker.symm
    exact ⟨lup8e_coxeterMatrix_E6.symm ▸ (coxeterSystem .E6).map e.symm⟩
  ·
    have hTorEqV0 : D.Tor = D.V0 := le_antisymm hTV D.V0_le_Tor
    have hcardTor : Nat.card D.Tor = 3 ^ 5 := by
      rw [hTorEqV0]
      have h := Nat.card_congr (lup8e_equiv D hD)
      rwa [NoOffRest.card_hypE6] at h
    let ψT : T →* D.Tor :=
      { toFun := fun t => ⟨ψ (t : L'), t.2⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp [map_mul] }
    have hψT_surj : Function.Surjective ψT := by
      intro t
      obtain ⟨l, hl⟩ := hψ (t : R)
      have hlT : l ∈ T := by rw [Subgroup.mem_comap]; rw [hl]; exact t.2
      exact ⟨⟨l, hlT⟩, Subtype.ext hl⟩
    have hψT_ker : ψT.ker = ψ.ker.subgroupOf T := by
      ext t
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    have hcardT : Nat.card T = 3 ^ 6 := by
      have h := Subgroup.card_ker_mul_card_range ψT
      rw [hψT_ker, MonoidHom.range_eq_top.mpr hψT_surj, Subgroup.card_top] at h
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerT).toEquiv, hcard, hcardTor] at h
      rw [← h]
      norm_num
    let f : (N ⧸ T.subgroupOf N) →* WeylGroup .E6 :=
      QuotientGroup.lift (T.subgroupOf N) Φ (by rw [hΦker])
    have hfrange : f.range = ⊤ := by
      rw [MonoidHom.range_eq_top]
      intro w
      obtain ⟨n, hn⟩ := (MonoidHom.range_eq_top.mp hΦrange) w
      exact ⟨QuotientGroup.mk n, by
        change f (QuotientGroup.mk n) = w
        rw [show f (QuotientGroup.mk n) = Φ n from rfl]
        exact hn⟩
    have hNTdvd : 51840 ∣ Nat.card (N ⧸ T.subgroupOf N) := by
      have h := Subgroup.card_ker_mul_card_range f
      rw [hfrange, Subgroup.card_top, CFSG.RankThree.E6.card_weylGroup_E6] at h
      exact ⟨Nat.card f.ker, by rw [h.symm, Nat.mul_comm]⟩
    have hNcard : Nat.card N = Nat.card T * Nat.card (N ⧸ T.subgroupOf N) := by
      have h := Subgroup.card_mul_index (T.subgroupOf N)
      rw [Subgroup.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv] at h
      exact h.symm
    have h3N : 3 ^ 10 ∣ Nat.card N := by
      rw [hNcard, hcardT]
      have h1 : 3 ^ 10 ∣ 3 ^ 6 * 51840 := by norm_num
      exact h1.trans (Nat.mul_dvd_mul_left (3 ^ 6) hNTdvd)
    have hLcard : Nat.card L' = Nat.card R * Nat.card ψ.ker := by
      have h := Subgroup.card_ker_mul_card_range ψ
      rw [MonoidHom.range_eq_top.mpr hψ, Subgroup.card_top] at h
      exact h.symm.trans (Nat.mul_comm _ _)
    have hnot11 : ¬ 3 ^ 11 ∣ Nat.card L' := by
      intro h11
      rw [hLcard, hcard, show 3 ^ 11 = 3 ^ 10 * 3 from by norm_num] at h11
      apply h3R
      obtain ⟨k, hk⟩ := h11
      refine ⟨k, ?_⟩
      apply Nat.mul_right_cancel (by norm_num : 0 < (3:ℕ))
      rw [hk]
      ring
    intro h3idx
    apply hnot11
    have h := Subgroup.index_mul_card N
    have h3 : 3 * Nat.card N ∣ Nat.card L' := by
      rw [← h]
      exact Nat.mul_dvd_mul_right h3idx _
    exact (show 3 ^ 11 ∣ 3 * Nat.card N from by
      rw [show 3 ^ 11 = 3 * 3 ^ 10 from by norm_num]
      exact Nat.mul_dvd_mul_left 3 h3N).trans h3

end CFSG.StandardType.GGXInL

end
