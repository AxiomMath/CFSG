module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveRoot
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveCfg
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveFix
public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

structure SevenTwelveConfig {X : Type} [Group X] (S : Subgroup X) (g₂ g₃ y : X)
    (W T : Subgroup X) : Prop where
  ne : conjSubgroup S g₂ ≠ S
  comm₁₃ : ⁅S, conjSubgroup S g₃⁆ ≠ ⊥
  comm₂₃ : ⁅conjSubgroup S g₂, conjSubgroup S g₃⁆ ≠ ⊥
  perfect : ⁅S ⊔ conjSubgroup S g₂ ⊔ conjSubgroup S g₃,
      S ⊔ conjSubgroup S g₂ ⊔ conjSubgroup S g₃⁆ = S ⊔ conjSubgroup S g₂ ⊔ conjSubgroup S g₃
  w_two : IsPGroup 2 W
  le_w : S ≤ W
  le_w₂ : conjSubgroup S g₂ ≤ W
  w_le : W ≤ S ⊔ conjSubgroup S g₂ ⊔ conjSubgroup S g₃
  t_two : IsPGroup 2 T
  t_le : T ≤ Subgroup.normalizer (S : Set X)
  gen : S ⊔ conjSubgroup S g₂ ⊔ conjSubgroup S g₃ ⊔ T = ⊤
  y_mem : y ∈ S ⊔ conjSubgroup S g₂ ⊔ conjSubgroup S g₃
  y_t : y ∈ Subgroup.normalizer (T : Set X)
  y_w : y ∈ Subgroup.normalizer (W : Set X)
  y_s : y ∉ Subgroup.normalizer (S : Set X)

@[expose] def SpURootConfiguration : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (m n : ℕ) (t : X), 1 < n → CFSG.pCore 2 X = ⊥ →
    t * t = 1 → Subgroup.normalClosure ((Subgroup.zpowers t : Subgroup X) : Set X) = ⊤ →
    (IsSymplecticTransvection X m n t ∨ IsUnitaryTransvection X m n t) →
    ∃ (g₂ g₃ y : X) (W T : Subgroup X), SevenTwelveConfig (Subgroup.zpowers t) g₂ g₃ y W T

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

private theorem seven_twelve_mem_normalizer_inf {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA y, hB y]

private theorem seven_twelve_normalizer_le_normalizer_centralizer (V₀ : Subgroup G) :
    Subgroup.normalizer (V₀ : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (V₀ : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro v hv
    have hw : g⁻¹ * v * g ∈ V₀ :=
      (hg (g⁻¹ * v * g)).mpr (by rwa [show g * (g⁻¹ * v * g) * g⁻¹ = v by group])
    have hx' := hx (g⁻¹ * v * g) hw
    calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [hx']
      _ = g * x * g⁻¹ * v := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro v hv
    have hw : g * v * g⁻¹ ∈ V₀ := (hg v).mp hv
    have hx' := hx (g * v * g⁻¹) hw
    calc v * x = g⁻¹ * ((g * v * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * v * g⁻¹)) * g := by rw [hx']
      _ = x * v := by group


theorem seven_twelve_core (h : Hyp711 V H E) {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hV2 : Nat.card (barSub (kSub V H E) φ V) = 2) {k₂ k₃ : ↥(kSub V H E)} {yb : X}
    {Wb Tb : Subgroup X}
    (hcfg : SevenTwelveConfig (barSub (kSub V H E) φ V) (φ k₂) (φ k₃) yb Wb Tb) :
    iSub V H E ⊓ Subgroup.centralizer (kSub V H E : Set G) ≠ ⊥ := by
  let X₀ : Subgroup G := V ⊔ conjSubgroup V (k₂ : G) ⊔ conjSubgroup V (k₃ : G)
  let A : Subgroup G := ⁅iSubFix V H E, X₀⁆
  let A₁ : Subgroup G := ⁅A, V⁆
  let A₂ : Subgroup G := ⁅A, conjSubgroup V (k₂ : G)⁆
  let C : Subgroup G := A ⊓ Subgroup.centralizer (X₀ : Set G)
  let T : Subgroup G := barPre (kSub V H E) φ Tb
  let P : Subgroup G := (A₁ ⊔ C) ⊓ Subgroup.centralizer (T : Set G)
  have hVK : V ≤ kSub V H E := le_kSub h.mem
  have hk₂H : (k₂ : G) ∈ H := kSub_le_of_forall_le h.omega_le k₂.2
  have hk₃H : (k₃ : G) ∈ H := kSub_le_of_forall_le h.omega_le k₃.2
  have hmem₂ : conjSubgroup V (k₂ : G) ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem hk₂H
  have hmem₃ : conjSubgroup V (k₃ : G) ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem hk₃H
  have hV₂K : conjSubgroup V (k₂ : G) ≤ kSub V H E := le_kSub hmem₂
  have hV₃K : conjSubgroup V (k₃ : G) ≤ kSub V H E := le_kSub hmem₃
  have hX₀K : X₀ ≤ kSub V H E := sup_le (sup_le hVK hV₂K) hV₃K
  have hbar : barSub (kSub V H E) φ X₀ =
      barSub (kSub V H E) φ V ⊔ conjSubgroup (barSub (kSub V H E) φ V) (φ k₂)
        ⊔ conjSubgroup (barSub (kSub V H E) φ V) (φ k₃) := by
    dsimp only [X₀]
    rw [barSub_sup (K := kSub V H E) (A := V ⊔ conjSubgroup V (k₂ : G))
        (B := conjSubgroup V (k₃ : G)) (sup_le hVK hV₂K) hV₃K φ,
      barSub_sup (K := kSub V H E) (A := V) (B := conjSubgroup V (k₂ : G)) hVK hV₂K φ,
      barSub_conjSubgroup (K := kSub V H E) φ V k₂,
      barSub_conjSubgroup (K := kSub V H E) φ V k₃]
  by_cases hA0 : A = ⊥
  · have hle : ⁅iSubFix V H E, V⁆ ≤ A :=
      Subgroup.commutator_mono_right (H := iSubFix V H E) (K₁ := V) (K₂ := X₀)
        (le_sup_left.trans le_sup_left)
    have hFV : ⁅iSubFix V H E, V⁆ = ⊥ := by
      rw [hA0] at hle
      exact le_antisymm hle bot_le
    have hFcent : iSubFix V H E ≤ Subgroup.centralizer (kSub V H E : Set G) :=
      le_centralizer_kSub_of_commutator_eq_bot h (kSub_le_normalizer_iSubFix h) hFV
    exact ne_bot_of_le_ne_bot (iSubFix_ne_bot h hφ hV2) (le_inf iSubFix_le_iSub hFcent)
  · have hc : SevenSevenCfg V H E V (conjSubgroup V (k₂ : G)) (conjSubgroup V (k₃ : G)) :=
      sevenSevenCfg_of_barSub h hφ hV2 k₂ k₃
        (hcfg.w_two.to_le (sup_le hcfg.le_w hcfg.le_w₂)) hcfg.ne hcfg.comm₁₃ hcfg.comm₂₃
    have hA : SevenSevenModule V H E V (conjSubgroup V (k₂ : G)) (conjSubgroup V (k₃ : G)) A :=
      sevenSevenModule_commutator_iSubFix h hφ hc.mem₂ hc.mem₃
        (by rw [hbar]; exact hcfg.perfect) hA0
    obtain ⟨-, -, -, -, h1C, -⟩ :=
      inf_centralizer_properties h.toHyp73 hc hA (B := C) rfl
    have hW : ⁅iSubFix V H E, omegaUnder V H E φ Wb⁆ = A₁ ⊔ A₂ :=
      commutator_omegaUnder_eq h hφ hc hA hcfg.w_two hcfg.le_w
        (by rw [barSub_conjSubgroup (K := kSub V H E) φ V k₂]; exact hcfg.le_w₂)
        (by rw [hbar]; exact hcfg.w_le)
    have hA₁_eq : A₁ = A ⊓ V := (commutator_eq_inf h.toHyp73 hc hA).1
    have hA₁V : A₁ ≤ V := hA₁_eq.le.trans inf_le_right
    have hA₁C_I : A₁ ⊔ C ≤ iSub V H E :=
      sup_le (hA₁_eq.le.trans (inf_le_left.trans hA.le_iSub)) (inf_le_left.trans hA.le_iSub)
    have hI : IsElemAbelian 2 (iSub V H E) :=
      seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le
    have hM : ∀ a ∈ A₁ ⊔ C, ∀ b ∈ A₁ ⊔ C, a * b = b * a := by
      intro a ha b hb
      exact congrArg Subtype.val (hI.1.is_comm.comm ⟨a, hA₁C_I ha⟩ ⟨b, hA₁C_I hb⟩)
    obtain ⟨a, haA₁, ha1, haT⟩ :=
      exists_ne_one_mem_commutator_centralizer_barPre h hφ hc hA hcfg.t_two hcfg.t_le
    have haA₁V : a ∈ V := hA₁V haA₁
    have hyb : yb ∈ barSub (kSub V H E) φ X₀ := by
      rw [hbar]
      exact hcfg.y_mem
    obtain ⟨y', hy'X₀, hy'φ⟩ := mem_barSub.mp hyb
    have hyF : (y' : G) ∈ Subgroup.normalizer (iSubFix V H E : Set G) :=
      kSub_le_normalizer_iSubFix h y'.2
    have hyW₀ : (y' : G) ∈ Subgroup.normalizer (omegaUnder V H E φ Wb : Set G) :=
      mem_normalizer_omegaUnder h (by rw [hy'φ]; exact hcfg.y_w)
    have hEq : A₁ ⊔ C = ⁅iSubFix V H E, omegaUnder V H E φ Wb⁆ := h1C.trans hW.symm
    have hyM : (y' : G) ∈ Subgroup.normalizer ((A₁ ⊔ C : Subgroup G) : Set G) := by
      have hcomm := le_normalizer_commutator_of_le_of_le
        (P := Subgroup.zpowers (y' : G)) (A := iSubFix V H E)
        (B := omegaUnder V H E φ Wb)
        (Subgroup.zpowers_le.mpr hyF) (Subgroup.zpowers_le.mpr hyW₀)
      have hmem : (y' : G) ∈ Subgroup.normalizer
          ((⁅iSubFix V H E, omegaUnder V H E φ Wb⁆ : Subgroup G) : Set G) :=
        hcomm (Subgroup.mem_zpowers (y' : G))
      rw [← hEq] at hmem
      exact hmem
    have hbarZp : barSub (kSub V H E) φ (Subgroup.zpowers (y' : G)) ≤
        Subgroup.normalizer (Tb : Set X) := by
      intro z hz
      obtain ⟨k, hk, hkφ⟩ := mem_barSub.mp hz
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hk
      rw [← hkφ]
      have hk_eq : k = y' ^ i := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow, hi]
      rw [hk_eq, map_zpow, hy'φ]
      exact Subgroup.zpow_mem (K := Subgroup.normalizer (Tb : Set X)) hcfg.y_t i
    have hyT : (y' : G) ∈ Subgroup.normalizer (T : Set G) :=
      le_normalizer_barPre hφ (Subgroup.zpowers_le.mpr y'.2) hbarZp
        (Subgroup.mem_zpowers (y' : G))
    have hyC : C ≤ Subgroup.centralizer ({(y' : G)} : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2 (y' : G) hy'X₀
    have hneV : conjSubgroup V ((y' : G)⁻¹) ≠ V := by
      intro heq
      have hNg : (y' : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
        conjSubgroup_eq_iff_mem_normalizer.mp heq
      have hNy : (y' : G) ∈ Subgroup.normalizer (V : Set G) := by
        simpa using (Subgroup.normalizer (V : Set G)).inv_mem hNg
      have hbarZpV : barSub (kSub V H E) φ (Subgroup.zpowers (y' : G)) ≤
          Subgroup.normalizer (barSub (kSub V H E) φ V : Set X) :=
        barSub_le_normalizer_barSub φ (Subgroup.zpowers_le.mpr hNy)
      have hyb' : yb ∈ barSub (kSub V H E) φ (Subgroup.zpowers (y' : G)) := by
        rw [← hy'φ]
        exact mem_barSub.mpr ⟨y', Subgroup.mem_zpowers (y' : G), rfl⟩
      exact hcfg.y_s (hbarZpV hyb')
    have hVy : V ⊓ conjSubgroup V ((y' : G)⁻¹) = ⊥ :=
      inf_conjSubgroup_eq_bot_of_isTI h.ti hneV
    have hyCen : (y' : G) ∈ Subgroup.normalizer
        (Subgroup.centralizer (T : Set G) : Set G) :=
      seven_twelve_normalizer_le_normalizer_centralizer T hyT
    have hyP : (y' : G) ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
      seven_twelve_mem_normalizer_inf (A := A₁ ⊔ C)
        (B := Subgroup.centralizer (T : Set G)) hyM hyCen
    have hPV : P ⊓ V ≠ ⊥ := by
      refine Subgroup.ne_bot_iff_exists_ne_one.mpr
        ⟨⟨a, ⟨⟨Subgroup.mem_sup_left haA₁, haT⟩, haA₁V⟩⟩,
          fun h => ha1 (congrArg Subtype.val h)⟩
    have hPC : P ⊓ C ≠ ⊥ :=
      inf_ne_bot_of_inf_ne_bot_of_inf_conjSubgroup_eq_bot hVy hA₁V hM hyM hyC
        inf_le_left hyP hPV
    have hJT : pCoreOf 2 (kSub V H E) ≤ T :=
      le_barPre (CFSG.LieType.BorelTits.pCoreOf_le 2 (kSub V H E)) hφ Tb
    have hbarTop : barSub (kSub V H E) φ (X₀ ⊔ T) = ⊤ := by
      rw [barSub_sup (K := kSub V H E) (A := X₀) (B := T) hX₀K
          (barPre_le (kSub V H E) φ Tb) φ, hbar, barSub_barPre hφ Tb]
      exact hcfg.gen
    have hK_eq : kSub V H E = pCoreOf 2 (kSub V H E) ⊔ (X₀ ⊔ T) :=
      (barSub_eq_top_iff (sup_le hX₀K (barPre_le (kSub V H E) φ Tb))
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (kSub V H E)) hφ).mp hbarTop
    have hKT : kSub V H E ≤ X₀ ⊔ T := by
      rw [hK_eq]
      exact sup_le (hJT.trans le_sup_right) le_rfl
    have hPC_le_cent : P ⊓ C ≤ Subgroup.centralizer (kSub V H E : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      refine hKT.trans (sup_le ?_ ?_)
      · exact Subgroup.le_centralizer_iff.mp (inf_le_right.trans inf_le_right)
      · exact Subgroup.le_centralizer_iff.mp (inf_le_left.trans inf_le_right)
    have hPC_le_I : P ⊓ C ≤ iSub V H E :=
      inf_le_right.trans (inf_le_left.trans hA.le_iSub)
    exact ne_bot_of_le_ne_bot hPC (le_inf hPC_le_I hPC_le_cent)

theorem seven_twelve (hConf : SpURootConfiguration) (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) {m n : ℕ}
    (hn : 1 < n)
    (hX : IsSpGp (X ⧸ Subgroup.center X) m n ∨ IsPSUGp (X ⧸ Subgroup.center X) m n)
    (hV2 : Nat.card (barSub (kSub V H E) φ V) = 2)
    (hroot : ∀ k : ↥(kSub V H E), (k : G) ∈ V → (k : G) ∉ pCoreOf 2 (kSub V H E) →
      IsSymplecticTransvection X m n (φ k) ∨ IsUnitaryTransvection X m n (φ k)) :
    iSub V H E ⊓ Subgroup.centralizer (kSub V H E : Set G) ≠ ⊥ := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  obtain ⟨v, hvV, hvJ⟩ := Set.not_subset.mp (not_le_pCoreOf_kSub h)
  have hvK : v ∈ kSub V H E := le_kSub h.mem hvV
  let t : X := φ ⟨v, hvK⟩
  have htt : t * t = 1 := by
    have hvv : v * v = 1 := elemAbelian_mul_self h.elemAbelian hvV
    have hsub : (⟨v, hvK⟩ : ↥(kSub V H E)) * ⟨v, hvK⟩ = 1 :=
      Subtype.ext (by simpa using hvv)
    calc t * t = φ (⟨v, hvK⟩ * ⟨v, hvK⟩) := by rw [map_mul]
      _ = φ 1 := by rw [hsub]
      _ = 1 := map_one φ
  have ht1 : t ≠ 1 := by
    intro h1
    exact hvJ ((hφ.ker_iff ⟨v, hvK⟩).mp h1)
  have hVt : barSub (kSub V H E) φ V = Subgroup.zpowers t :=
    (Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (mem_barSub.mpr ⟨⟨v, hvK⟩, hvV, rfl⟩))
      (by
        rw [hV2, Nat.card_zpowers,
          orderOf_eq_prime (p := 2) (by simpa [pow_two] using htt) ht1])).symm
  have hO2 : CFSG.pCore 2 X = ⊥ := pCore_eq_bot_of_isBarMap hφ
  have hnc : Subgroup.normalClosure ((Subgroup.zpowers t : Subgroup X) : Set X) = ⊤ := by
    rw [← hVt]
    exact normalClosure_barSub_eq_top h hφ
  obtain ⟨g₂, g₃, yb, Wb, Tb, hc⟩ :=
    hConf X m n t hn hO2 htt hnc (hroot ⟨v, hvK⟩ hvV hvJ)
  rw [← hVt] at hc
  obtain ⟨k₂, rfl⟩ := hφ.surjective g₂
  obtain ⟨k₃, rfl⟩ := hφ.surjective g₃
  exact seven_twelve_core h hφ hV2 hc

end CFSG.LocalAnalysis.WeakClosure81
