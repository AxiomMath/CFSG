module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveSetup
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsThree
public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

@[expose] def omegaUnder (V H E : Subgroup G) {X : Type} [Group X] (φ : ↥(kSub V H E) →* X)
    (Wb : Subgroup X) : Subgroup G :=
  ⨆ (U : Subgroup G) (_ : U ∈ omegaSet V H E ∧ barSub (kSub V H E) φ U ≤ Wb), U

theorem le_omegaUnder {X : Type} [Group X] {φ : ↥(kSub V H E) →* X} {Wb : Subgroup X}
    {U : Subgroup G} (hU : U ∈ omegaSet V H E) (hUW : barSub (kSub V H E) φ U ≤ Wb) :
    U ≤ omegaUnder V H E φ Wb := by
  exact le_iSup₂_of_le U ⟨hU, hUW⟩ le_rfl

theorem omegaUnder_le_kSub {X : Type} [Group X] (φ : ↥(kSub V H E) →* X) (Wb : Subgroup X) :
    omegaUnder V H E φ Wb ≤ kSub V H E := by
  exact iSup₂_le fun U hU => le_kSub hU.1

theorem mem_normalizer_omegaUnder (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} {Wb : Subgroup X} {g : ↥(kSub V H E)}
    (hg : φ g ∈ Subgroup.normalizer (Wb : Set X)) :
    (g : G) ∈ Subgroup.normalizer (omegaUnder V H E φ Wb : Set G) := by
  have hK : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hmem_fam : ∀ (g' : ↥(kSub V H E)), φ g' ∈ Subgroup.normalizer (Wb : Set X) →
      ∀ (U : Subgroup G) (hU : U ∈ omegaSet V H E),
      barSub (kSub V H E) φ U ≤ Wb →
      conjSubgroup U ((g' : G)⁻¹) ∈ omegaSet V H E ∧
        barSub (kSub V H E) φ (conjSubgroup U ((g' : G)⁻¹)) ≤ Wb := by
    intro g' hg' U hU hUW
    refine ⟨conjSubgroup_mem_omegaSet h.le h.normal hU
      (hK ((kSub V H E).inv_mem g'.2)), ?_⟩
    have hbar : barSub (kSub V H E) φ (conjSubgroup U ((g' : G)⁻¹)) =
        conjSubgroup (barSub (kSub V H E) φ U) ((φ g')⁻¹) := by
      have hh := barSub_conjSubgroup (K := kSub V H E) φ U (g'⁻¹)
      simpa using hh
    rw [hbar]
    have hgN : (φ g')⁻¹ ∈ Subgroup.normalizer (Wb : Set X) :=
      (Subgroup.normalizer (Wb : Set X)).inv_mem hg'
    calc conjSubgroup (barSub (kSub V H E) φ U) ((φ g')⁻¹)
        ≤ conjSubgroup Wb ((φ g')⁻¹) := Subgroup.map_mono hUW
      _ = Wb := conjSubgroup_eq_iff_mem_normalizer.mpr hgN
  have hact : ∀ (g' : ↥(kSub V H E)), φ g' ∈ Subgroup.normalizer (Wb : Set X) →
      ∀ x ∈ omegaUnder V H E φ Wb, (g' : G) * x * (g' : G)⁻¹ ∈ omegaUnder V H E φ Wb := by
    intro g' hg' x hx
    have hle : omegaUnder V H E φ Wb ≤
        (omegaUnder V H E φ Wb).comap ((MulAut.conj (g' : G)).toMonoidHom) := by
      unfold omegaUnder
      refine iSup₂_le fun U hU => ?_
      intro u hu
      have hf := hmem_fam g' hg' U hU.1 hU.2
      refine le_omegaUnder hf.1 hf.2 ?_
      rw [mem_conjSubgroup_iff]
      have h2 : (↑g')⁻¹ * (MulEquiv.toMonoidHom (MulAut.conj (↑g'))) u *
          (↑g')⁻¹⁻¹ = u := by
        rw [show (MulEquiv.toMonoidHom (MulAut.conj (↑g'))) u =
            (↑g') * u * (↑g')⁻¹ from rfl, inv_inv]
        group
      rwa [h2]
    have h := hle hx
    rw [Subgroup.mem_comap] at h
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hact g hg x hx
  · intro hx
    have hgi : φ (g⁻¹) ∈ Subgroup.normalizer (Wb : Set X) := by
      rw [map_inv]
      exact (Subgroup.normalizer (Wb : Set X)).inv_mem hg
    have h := hact (g⁻¹) hgi (g * x * g⁻¹) hx
    have hx' : (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) = x := by group
    rw [Subgroup.coe_inv, inv_inv, hx'] at h
    exact h

theorem omegaUnder_le_sup_pCoreOf {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) {Wb : Subgroup X} {Y : Subgroup G}
    (hY : Y ≤ kSub V H E) (hWY : Wb ≤ barSub (kSub V H E) φ Y) :
    omegaUnder V H E φ Wb ≤ Y ⊔ pCoreOf 2 (kSub V H E) := by
  unfold omegaUnder
  refine iSup₂_le fun U hU => ?_
  intro u hu
  have huK : u ∈ kSub V H E := (le_kSub hU.1) hu
  have hbarU : φ ⟨u, huK⟩ ∈ barSub (kSub V H E) φ U := mem_barSub.mpr ⟨⟨u, huK⟩, hu, rfl⟩
  have hbarY : φ ⟨u, huK⟩ ∈ barSub (kSub V H E) φ Y := hWY (hU.2 hbarU)
  obtain ⟨y, hyY, hyφ⟩ := mem_barSub.mp hbarY
  have hker : u * (y : G)⁻¹ ∈ pCoreOf 2 (kSub V H E) := by
    refine (hφ.ker_iff ⟨u * (y : G)⁻¹,
      (kSub V H E).mul_mem huK ((kSub V H E).inv_mem y.2)⟩).mp ?_
    have h1 : (⟨u * (y : G)⁻¹, (kSub V H E).mul_mem huK
        ((kSub V H E).inv_mem y.2)⟩ : ↥(kSub V H E)) = ⟨u, huK⟩ * y⁻¹ :=
      Subtype.ext rfl
    rw [h1, map_mul, map_inv, hyφ]
    simp
  rw [show u = (u * (y : G)⁻¹) * (y : G) by group]
  exact (Y ⊔ pCoreOf 2 (kSub V H E)).mul_mem (Subgroup.mem_sup_right hker)
    (Subgroup.mem_sup_left hyY)

theorem isPGroup_barPre {K : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}
    (hφ : IsBarMap K (pCoreOf 2 K) φ) {Tb : Subgroup X} (hT : IsPGroup 2 Tb) :
    IsPGroup 2 ↥(barPre K φ Tb) := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hT
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K)
  have hcard : Nat.card ↥(barPre K φ Tb) = 2 ^ (a + b) := by
    have hr := Subgroup.relIndex_mul_card
      (H := pCoreOf 2 K) (K := barPre K φ Tb)
    rw [relIndex_barPre (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hφ Tb] at hr
    rw [inf_eq_left.mpr
      (le_barPre (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hφ Tb)] at hr
    rw [hb, ha] at hr
    rw [← hr, pow_add]
  exact IsPGroup.of_card hcard


private theorem seven_twelve_root_mem_normalizer_inf {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA y, hB y]

private theorem seven_twelve_root_mem_sup_of_mem_barSub {K : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ) {V : Subgroup G} {y : G}
    (hyK : y ∈ K) (hy : φ ⟨y, hyK⟩ ∈ barSub K φ V) : y ∈ V ⊔ pCoreOf 2 K := by
  obtain ⟨v, hvV, hvφ⟩ := mem_barSub.mp hy
  have hker : y * (v : G)⁻¹ ∈ pCoreOf 2 K := by
    refine (hφ.ker_iff ⟨y * (v : G)⁻¹, K.mul_mem hyK (K.inv_mem v.2)⟩).mp ?_
    have h1 : (⟨y * (v : G)⁻¹, K.mul_mem hyK (K.inv_mem v.2)⟩ : ↥K) =
        ⟨y, hyK⟩ * v⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_inv, hvφ]
    simp
  rw [show y = (y * (v : G)⁻¹) * (v : G) by group]
  exact (V ⊔ pCoreOf 2 K).mul_mem (Subgroup.mem_sup_right hker)
    (Subgroup.mem_sup_left hvV)

theorem commutator_omegaUnder_le_centralizer (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    {Wb : Subgroup X} (hW2 : IsPGroup 2 Wb) (hVW : barSub (kSub V H E) φ V ≤ Wb) :
    ⁅iSubFix V H E, omegaUnder V H E φ Wb⁆ ≤ Subgroup.centralizer (V : Set G) := by
  have hKNF : kSub V H E ≤ Subgroup.normalizer (iSubFix V H E : Set G) :=
    kSub_le_normalizer_iSubFix h
  have hUcent : ∀ U : Subgroup G, U ∈ omegaSet V H E →
      barSub (kSub V H E) φ U ≤ Wb → U ≤ Subgroup.centralizer (V : Set G) := by
    intro U hU hUW
    obtain ⟨k, hk, rfl⟩ := h.transitive U hU
    have hbarc : barSub (kSub V H E) φ (conjSubgroup V k) ≤ Wb := hUW
    rw [barSub_conjSubgroup (K := kSub V H E) φ V ⟨k, hk⟩] at hbarc
    have hsup : barSub (kSub V H E) φ V ⊔
        conjSubgroup (barSub (kSub V H E) φ V) (φ ⟨k, hk⟩) ≤ Wb := sup_le hVW hbarc
    have hp : IsPGroup 2 ↥(barSub (kSub V H E) φ V ⊔
        conjSubgroup (barSub (kSub V H E) φ V) (φ ⟨k, hk⟩)) := hW2.to_le hsup
    have hcomm : ⁅V, conjSubgroup V k⁆ = ⊥ :=
      (isPGroup_barSub_sup_conj_iff h hφ ⟨k, hk⟩).mp hp
    rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  let s : Set G := {x | ∃ U : Subgroup G,
    U ∈ omegaSet V H E ∧ barSub (kSub V H E) φ U ≤ Wb ∧ x ∈ U}
  have hclosure : Subgroup.closure s = omegaUnder V H E φ Wb := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro u ⟨U, hU, hUW, huU⟩
      exact le_omegaUnder hU hUW huU
    · unfold omegaUnder
      refine iSup₂_le fun U hU => ?_
      intro u hu
      exact Subgroup.subset_closure ⟨U, hU.1, hU.2, hu⟩
  have hS : s ⊆ Subgroup.normalizer
      ((iSubFix V H E ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    rintro u ⟨U, hU, hUW, huU⟩
    have h1 : u ∈ Subgroup.normalizer (iSubFix V H E : Set G) :=
      hKNF ((le_kSub hU) huU)
    have h2 : u ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
      (Subgroup.le_normalizer (H := Subgroup.centralizer (V : Set G)))
        (hUcent U hU hUW huU)
    exact seven_twelve_root_mem_normalizer_inf h1 h2
  have hAcomm : ∀ a ∈ iSubFix V H E, ∀ u ∈ s,
      ⁅a, u⁆ ∈ iSubFix V H E ⊓ Subgroup.centralizer (V : Set G) := by
    intro a ha u hu
    obtain ⟨U, hU, hUW, huU⟩ := hu
    have hUN : U ≤ Subgroup.normalizer (iSubFix V H E : Set G) :=
      (le_kSub hU).trans hKNF
    have hmem := Subgroup.commutator_le.mp
      (commutator_le_inf_of_mem_omegaSet h.toHyp73 hU iSubFix_le_iSub hUN) a ha u huU
    exact ⟨hmem.1, hUcent U hU hUW hmem.2⟩
  have hmain := commutator_closure_le_of_forall (A := iSubFix V H E)
    (S := iSubFix V H E ⊓ Subgroup.centralizer (V : Set G)) (s := s) hS hAcomm
  rw [hclosure] at hmain
  exact hmain.trans inf_le_right

theorem commutator_omegaUnder_eq (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    {V₂ V₃ : Subgroup G} (hc : SevenSevenCfg V H E V V₂ V₃)
    (hA : SevenSevenModule V H E V V₂ V₃ ⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆)
    {Wb : Subgroup X} (hW2 : IsPGroup 2 Wb) (hVW : barSub (kSub V H E) φ V ≤ Wb)
    (hV₂W : barSub (kSub V H E) φ V₂ ≤ Wb) (hWX : Wb ≤ barSub (kSub V H E) φ (V ⊔ V₂ ⊔ V₃)) :
    ⁅iSubFix V H E, omegaUnder V H E φ Wb⁆ =
      ⁅⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆, V⁆ ⊔ ⁅⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆, V₂⁆ := by
  have hX₀K : V ⊔ V₂ ⊔ V₃ ≤ kSub V H E :=
    sup_le (sup_le (le_kSub h.mem) (le_kSub hc.mem₂)) (le_kSub hc.mem₃)
  have hX₀NF : V ⊔ V₂ ⊔ V₃ ≤ Subgroup.normalizer (iSubFix V H E : Set G) :=
    hX₀K.trans (kSub_le_normalizer_iSubFix h)
  have hAF : ⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆ ≤ iSubFix V H E :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hX₀NF
  apply le_antisymm
  · have h1 : omegaUnder V H E φ Wb ≤ V ⊔ V₂ ⊔ V₃ ⊔ pCoreOf 2 (kSub V H E) :=
      omegaUnder_le_sup_pCoreOf hφ hX₀K hWX
    have h2 : ⁅iSubFix V H E, omegaUnder V H E φ Wb⁆ ≤
        ⁅iSubFix V H E, (V ⊔ V₂ ⊔ V₃) ⊔ pCoreOf 2 (kSub V H E)⁆ :=
      Subgroup.commutator_mono_right h1
    rw [commutator_iSubFix_sup_pCoreOf h hX₀K] at h2
    have h3 := commutator_omegaUnder_le_centralizer h hφ hW2 hVW
    have h4 : ⁅iSubFix V H E, omegaUnder V H E φ Wb⁆ ≤
        ⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆ ⊓ Subgroup.centralizer (V : Set G) :=
      le_inf h2 h3
    rw [(inf_centralizer_eq_sup_commutator h.toHyp73 hc hA).1] at h4
    exact h4
  · apply sup_le
    · exact (Subgroup.commutator_mono_left hAF).trans
        (Subgroup.commutator_mono_right (le_omegaUnder h.mem hVW))
    · exact (Subgroup.commutator_mono_left hAF).trans
        (Subgroup.commutator_mono_right (le_omegaUnder hc.mem₂ hV₂W))

theorem commutator_iSubFix_eq_commutator (h : Hyp711 V H E) {V₂ V₃ : Subgroup G}
    (hc : SevenSevenCfg V H E V V₂ V₃)
    (hA : SevenSevenModule V H E V V₂ V₃ ⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆) :
    ⁅iSubFix V H E, V⁆ = ⁅⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆, V⁆ := by
  have hX₀K : V ⊔ V₂ ⊔ V₃ ≤ kSub V H E :=
    sup_le (sup_le (le_kSub h.mem) (le_kSub hc.mem₂)) (le_kSub hc.mem₃)
  have hX₀NF : V ⊔ V₂ ⊔ V₃ ≤ Subgroup.normalizer (iSubFix V H E : Set G) :=
    hX₀K.trans (kSub_le_normalizer_iSubFix h)
  have hAF : ⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆ ≤ iSubFix V H E :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hX₀NF
  apply le_antisymm
  · have h1 : ⁅iSubFix V H E, V⁆ ≤ ⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆ :=
      Subgroup.commutator_mono_right (le_sup_left.trans le_sup_left)
    have h2 : ⁅iSubFix V H E, V⁆ ≤ V :=
      (commutator_le_inf_of_mem_omegaSet h.toHyp73 h.mem iSubFix_le_iSub
        ((le_kSub h.mem).trans (kSub_le_normalizer_iSubFix h))).trans inf_le_right
    have h3 : ⁅iSubFix V H E, V⁆ ≤
        ⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆ ⊓ V := le_inf h1 h2
    rw [← (commutator_eq_inf h.toHyp73 hc hA).1] at h3
    exact h3
  · exact Subgroup.commutator_mono_left hAF

theorem barPre_le_normalizer_commutator_iSubFix (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    {Tb : Subgroup X} (hTV : Tb ≤ Subgroup.normalizer (barSub (kSub V H E) φ V : Set X)) :
    barPre (kSub V H E) φ Tb ≤
      Subgroup.normalizer ((⁅iSubFix V H E, V⁆ : Subgroup G) : Set G) := by
  have hKNF : kSub V H E ≤ Subgroup.normalizer (iSubFix V H E : Set G) :=
    kSub_le_normalizer_iSubFix h
  have hclaim : ∀ (u : G) (huK : u ∈ kSub V H E), φ ⟨u, huK⟩ ∈ Tb →
      conjSubgroup (⁅iSubFix V H E, V⁆) u ≤ ⁅iSubFix V H E, V⁆ := by
    intro u huK huTb
    have hFu : conjSubgroup (iSubFix V H E) u = iSubFix V H E :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (hKNF huK)
    have hCONJ : conjSubgroup (⁅iSubFix V H E, V⁆) u =
        ⁅conjSubgroup (iSubFix V H E) u, conjSubgroup V u⁆ := by
      simp only [CFSG.Quasithin.conjSubgroup]
      rw [Subgroup.map_commutator]
    have hbarVU : barSub (kSub V H E) φ (conjSubgroup V u) = barSub (kSub V H E) φ V := by
      rw [barSub_conjSubgroup (K := kSub V H E) φ V ⟨u, huK⟩]
      exact conjSubgroup_eq_iff_mem_normalizer.mpr (hTV huTb)
    have hconjK : conjSubgroup V u ≤ kSub V H E := by
      intro z hz
      rw [mem_conjSubgroup_iff] at hz
      rw [show z = u⁻¹ * (u * z * u⁻¹) * u by group]
      exact (kSub V H E).mul_mem
        ((kSub V H E).mul_mem ((kSub V H E).inv_mem huK) ((le_kSub h.mem) hz)) huK
    have hVu : conjSubgroup V u ≤ V ⊔ pCoreOf 2 (kSub V H E) := by
      intro y hy
      have hyK : y ∈ kSub V H E := hconjK hy
      have hybar : φ ⟨y, hyK⟩ ∈ barSub (kSub V H E) φ V := by
        have hy' : φ ⟨y, hyK⟩ ∈ barSub (kSub V H E) φ (conjSubgroup V u) :=
          mem_barSub.mpr ⟨⟨y, hyK⟩, hy, rfl⟩
        rwa [hbarVU] at hy'
      exact seven_twelve_root_mem_sup_of_mem_barSub hφ hyK hybar
    rw [hCONJ, hFu]
    calc ⁅iSubFix V H E, conjSubgroup V u⁆
        ≤ ⁅iSubFix V H E, V ⊔ pCoreOf 2 (kSub V H E)⁆ :=
          Subgroup.commutator_mono_right hVu
      _ = ⁅iSubFix V H E, V⁆ := commutator_iSubFix_sup_pCoreOf h (le_kSub h.mem)
  intro t ht
  rw [mem_barPre] at ht
  obtain ⟨htK, htTb⟩ := ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hTbinv : φ (⟨t, htK⟩⁻¹) ∈ Tb := by
      rw [map_inv]
      exact Tb.inv_mem htTb
    have hmem : t * x * t⁻¹ ∈ conjSubgroup (⁅iSubFix V H E, V⁆) t⁻¹ := by
      rw [mem_conjSubgroup_iff]
      convert hx using 1
      group
    exact hclaim t⁻¹ ((kSub V H E).inv_mem htK) hTbinv hmem
  · intro hx
    exact hclaim t htK htTb (mem_conjSubgroup_iff.mpr hx)

theorem exists_ne_one_mem_commutator_centralizer_barPre (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    {V₂ V₃ : Subgroup G} (hc : SevenSevenCfg V H E V V₂ V₃)
    (hA : SevenSevenModule V H E V V₂ V₃ ⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆) {Tb : Subgroup X}
    (hT2 : IsPGroup 2 Tb) (hTV : Tb ≤ Subgroup.normalizer (barSub (kSub V H E) φ V : Set X)) :
    ∃ a ∈ ⁅⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆, V⁆, a ≠ 1 ∧
      a ∈ Subgroup.centralizer (barPre (kSub V H E) φ Tb : Set G) := by
  let A₁ : Subgroup G := ⁅⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆, V⁆
  let T : Subgroup G := barPre (kSub V H E) φ Tb
  have hA₁eq : A₁ = ⁅iSubFix V H E, V⁆ := (commutator_iSubFix_eq_commutator h hc hA).symm
  have hA₁_le_A : A₁ ≤ ⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((le_sup_left.trans le_sup_left).trans hA.normalizes)
  have hA₁_le_iSub : A₁ ≤ iSub V H E := hA₁_le_A.trans hA.le_iSub
  have hI : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le
  have hA₁p : IsPGroup 2 ↥A₁ :=
    (isPGroup_two_of_isElemAbelian hI).to_le hA₁_le_iSub
  have hA₁ab : ∀ a ∈ A₁, ∀ b ∈ A₁, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hI.1.is_comm.comm
      ⟨a, hA₁_le_iSub ha⟩ ⟨b, hA₁_le_iSub hb⟩)
  have hA₁_ne : A₁ ≠ ⊥ := by
    intro hbot
    have hcard := card_eq_card_commutator_pow h.toHyp73 hc hA
    have hbot' : ⁅⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆, V⁆ = ⊥ := hbot
    rw [hbot', Subgroup.card_bot] at hcard
    simp only [one_pow] at hcard
    exact hA.ne_bot (Subgroup.eq_bot_of_card_eq _ hcard)
  have hTp : IsPGroup 2 ↥T := isPGroup_barPre hφ hT2
  have hTA₁ : T ≤ Subgroup.normalizer (A₁ : Set G) := by
    have h := barPre_le_normalizer_commutator_iSubFix h hφ hTV
    rwa [← hA₁eq] at h
  have hTbot : T ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp
  have hlt : (⊥ : Subgroup G) < A₁ := lt_of_le_of_ne bot_le hA₁_ne.symm
  obtain ⟨a, haA₁, haB, hcomm⟩ :=
    exists_mem_sdiff_forall_commutator_mem (P := T) (A := A₁) (B := ⊥)
      hTp hA₁p hA₁ab hTA₁ hTbot hlt
  refine ⟨a, haA₁, fun h1 => haB (Subgroup.mem_bot.mpr h1), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact (commutatorElement_eq_one_iff_mul_comm.mp
    (Subgroup.mem_bot.mp (hcomm t ht))).symm

end CFSG.LocalAnalysis.WeakClosure81
