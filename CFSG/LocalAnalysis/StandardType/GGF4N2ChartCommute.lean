module

public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartBlock
public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartComponent
public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartSupport
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartType
import CFSG.LocalAnalysis.StandardType.GGF4N2FourSpaceSlice
import CFSG.LocalAnalysis.StandardType.GGF4N2LineAlignment

public section

namespace CFSG.StandardType.N2Chart

open CFSG.Assembly (LargeEvenPLayer)
open Matrix Polynomial CFSG.RankThree.CALinearPrimary

variable {G : Type} [Group G] [Finite G]

theorem card_SL3_four : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F4) = 60480 := by
  let : Fintype F4 := Fintype.ofFinite _
  have hcard : Fintype.card F4 = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  rw [Matrix.card_SL_field, hcard]
  decide

theorem isQuasisimple_SL3_four : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) F4) :=
  CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F4 le_rfl

omit [Finite G] in
theorem commutator_eq_self_of_mulEquiv_SL3 {H : Subgroup G}
    (e : H ≃* Matrix.SpecialLinearGroup (Fin 3) F4) : ⁅H, H⁆ = H := by
  have hq : CFSG.IsQuasisimple H :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm isQuasisimple_SL3_four
  have h1 : commutator H = ⊤ := hq.1.commutator_eq_top
  have h2 := Subgroup.map_commutator (⊤ : Subgroup H) ⊤ H.subtype
  rw [← commutator_def, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact h2.symm

theorem mem_zpowers_symm {x y : G} (hx : orderOf x = 5) (hy : orderOf y = 5)
    (h : x ∈ Subgroup.zpowers y) : y ∈ Subgroup.zpowers x := by
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y :=
    (Subgroup.zpowers_le (G := G) (H := Subgroup.zpowers y)).mpr h
  have heq : Subgroup.zpowers x = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hy])
  rw [heq]
  exact Subgroup.mem_zpowers y

omit [Finite G] in
theorem mem_zpowers_of_pow_mem {x y : G} (hy : y ^ 5 = 1) {k : ℕ} (hk : k = 1 ∨ k = 2)
    (h : y ^ k ∈ Subgroup.zpowers x) : y ∈ Subgroup.zpowers x := by
  rcases hk with rfl | rfl
  · simpa using h
  · have h3 : (y ^ 2) ^ 3 = y := by
      rw [← pow_mul, show 2 * 3 = 5 + 1 from rfl, pow_succ, hy, one_mul]
    rw [← h3]
    exact Subgroup.pow_mem _ h 3

theorem ggN2_actualChart_commute_core
    (ψ : SL6 →* G) (hψ : ψ.ker ≤ Subgroup.center SL6)
    {X : Subgroup G} (hX : X ≤ ψ.range) {u₁ u₂ : G} (hu₁ : u₁ ∈ X) (hu₂ : u₂ ∈ X)
    (ho₁ : orderOf u₁ = 5) (ho₂ : orderOf u₂ = 5) (hc : Commute u₁ u₂)
    (hD : u₂ ∉ Subgroup.zpowers u₁)
    (hH₁ : Nonempty (LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₁} : Set G)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) F4))
    (hH₂ : Nonempty (LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₂} : Set G)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) F4))
    (h₂₁ : u₂ ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₁} : Set G)))
    (h₁₂ : u₁ ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₂} : Set G))) :
    (∀ a ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₁} : Set G)),
      ∀ b ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₂} : Set G)), Commute a b) ∨
    ∃ s₁ s₂ : SL6, s₁ ^ 5 = 1 ∧ ψ s₁ = u₁ ∧ s₂ ^ 5 = 1 ∧ ψ s₂ = u₂ ∧
      Module.finrank F4 (suppSp s₁) = 2 ∧ Disjoint (suppSp s₁) (fixSp s₁) ∧
      Module.finrank F4 (suppSp s₂) = 2 ∧ Disjoint (suppSp s₂) (fixSp s₂) ∧
      ∀ {ω : F4}, ω ^ 2 + ω + 1 = 0 → ∀ {r k : ℕ},
        (∀ v ∈ suppSp s₁, aeval (endo (s₁ ^ r)) (quadOm ω) v = 0) →
        (∀ v ∈ suppSp s₂, aeval (endo (s₂ ^ k)) (quadOm ω) v = 0) →
        ∃ K : Subgroup G, CFSG.Open.IsComponentOf K
            (LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({ψ (s₁ ^ r * s₂ ^ k)} : Set G))) ∧
          Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
  let hAlign : GGN2LineAlignmentInput := ggN2LineAlignmentInput_holds
  let hLines : GGN2SliceLinesInput := ggN2SliceLinesInput_holds
  have h5₁ : u₁ ^ 5 = 1 := by rw [← ho₁]; exact pow_orderOf_eq_one u₁
  have h5₂ : u₂ ^ 5 = 1 := by rw [← ho₂]; exact pow_orderOf_eq_one u₂
  obtain ⟨s₁, hs₁, rfl⟩ := exists_lift_five hψ (hX hu₁) h5₁
  obtain ⟨s₂, hs₂, rfl⟩ := exists_lift_five hψ (hX hu₂) h5₂
  have hos₁ : orderOf s₁ = 5 := orderOf_eq_five_of_lift hs₁ ho₁
  have hos₂ : orderOf s₂ = 5 := orderOf_eq_five_of_lift hs₂ ho₂
  have hcs : Commute s₁ s₂ := commute_of_map_commute_five hψ hs₂ hc
  have hDs : s₂ ∉ Subgroup.zpowers s₁ := by
    rintro ⟨k, hk⟩
    exact hD ⟨k, by rw [← hk, map_zpow]⟩
  set H₁ := LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({ψ s₁} : Set G)) with hH₁def
  set H₂ := LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({ψ s₂} : Set G)) with hH₂def
  obtain ⟨e₁⟩ := hH₁
  obtain ⟨e₂⟩ := hH₂
  have hlayer : ∀ Y : Subgroup G, LargeEvenPLayer 5 Y ≤ Y := by
    intro Y
    rw [CFSG.Assembly.LargeEven.largeEvenPLayer_eq_glaPLayer]
    exact sSup_le fun L hL => hL.1
  have hnorm : ∀ Y : Subgroup G, ∀ g ∈ Y, ∀ h ∈ LargeEvenPLayer 5 Y,
      g * h * g⁻¹ ∈ LargeEvenPLayer 5 Y := fun Y g hg h hh =>
    CFSG.StandardType.largeEvenPLayer_map_conj_le hg ⟨h, hh, rfl⟩
  have hH₁le : H₁ ≤ X ⊓ Subgroup.centralizer ({ψ s₁} : Set G) := hlayer _
  have hH₂le : H₂ ≤ X ⊓ Subgroup.centralizer ({ψ s₂} : Set G) := hlayer _
  have hperf₁ : ⁅H₁, H₁⁆ = H₁ := commutator_eq_self_of_mulEquiv_SL3 e₁
  have hperf₂ : ⁅H₂, H₂⁆ = H₂ := commutator_eq_self_of_mulEquiv_SL3 e₂
  have h7 : ∀ {s : SL6} {H : Subgroup G}, s ^ 5 = 1 →
      H ≤ X ⊓ Subgroup.centralizer ({ψ s} : Set G) →
      Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin 3) F4) →
      7 ∣ Nat.card (Subgroup.centralizer ({s} : Set SL6)) := by
    intro s H hs hH ⟨e⟩
    have hcard : Nat.card H = 60480 := by rw [Nat.card_congr e.toEquiv, card_SL3_four]
    have h1 : Nat.card H ∣ Nat.card ↥(X ⊓ Subgroup.centralizer ({ψ s} : Set G)) :=
      Subgroup.card_dvd_of_le hH
    rw [← map_comap_inf_centralizer hψ hX hs] at h1
    have h2 := Subgroup.card_map_dvd (X.comap ψ ⊓ Subgroup.centralizer ({s} : Set SL6)) ψ
    have h3 : Nat.card ↥(X.comap ψ ⊓ Subgroup.centralizer ({s} : Set SL6)) ∣
        Nat.card (Subgroup.centralizer ({s} : Set SL6)) := Subgroup.card_dvd_of_le inf_le_right
    exact (show 7 ∣ Nat.card H by rw [hcard]; norm_num).trans (h1.trans (h2.trans h3))
  have hinv : ∀ {s t : SL6} {H : Subgroup G}, s ^ 5 = 1 → t ^ 5 = 1 → orderOf (ψ t) = 5 →
      H ≤ X ⊓ Subgroup.centralizer ({ψ s} : Set G) → (e : H ≃* Matrix.SpecialLinearGroup (Fin 3) F4) →
      ψ t ∈ H → ∃ g ∈ Subgroup.centralizer ({s} : Set SL6), g * t * g⁻¹ = t⁻¹ := by
    intro s t H hs ht hot hH e htH
    obtain ⟨g, hg⟩ := ggN2SL3InvConjInput_holds (e ⟨ψ t, htH⟩)
      (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hot])
    have hh : e.symm g * ⟨ψ t, htH⟩ * (e.symm g)⁻¹ = (⟨ψ t, htH⟩ : H)⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, hg]
    have hh' : ((e.symm g : H) : G) * ψ t * ((e.symm g : H) : G)⁻¹ = (ψ t)⁻¹ := by
      have := congrArg Subtype.val hh
      simpa using this
    obtain ⟨g', hg', hg's⟩ := exists_inverter_lift hψ hX hs ht (hH (e.symm g).2) hh'
    exact ⟨g', hg'.2, hg's⟩
  obtain ⟨hdim₁, hdim₂, hc₁, hc₂, hle₁₂, hle₂₁⟩ := ggN2SupportTwoInput_holds s₁ s₂ hos₁ hos₂ hcs hDs
    (h7 hs₁ hH₁le ⟨e₁⟩) (h7 hs₂ hH₂le ⟨e₂⟩) (hinv hs₁ hs₂ ho₂ hH₁le e₁ h₂₁)
    (hinv hs₂ hs₁ ho₁ hH₂le e₂ h₁₂)
  have hST : SuppTwo s₁ s₂ := ⟨hs₁, hs₂, hdim₁, hdim₂, hc₁, hc₂, hle₁₂, hle₂₁, hcs⟩
  obtain ⟨hmap₁, hinj₁, hfix₁, hT₁le⟩ := slice_lift hψ hX hs₁ hdim₁ hc₁.disjoint hH₁le hperf₁
  obtain ⟨hmap₂, hinj₂, hfix₂, hT₂le⟩ := slice_lift hψ hX hs₂ hdim₂ hc₂.disjoint hH₂le hperf₂
  set T₁ := ⁅H₁.comap ψ, H₁.comap ψ⁆ with hT₁def
  set T₂ := ⁅H₂.comap ψ, H₂.comap ψ⁆ with hT₂def
  obtain ⟨eT₁⟩ := slice_lift_mulEquiv hmap₁ hinj₁ rfl
  obtain ⟨eT₂⟩ := slice_lift_mulEquiv hmap₂ hinj₂ rfl
  have hs₂T₁ : s₂ ∈ T₁ := lift_mem_slice_lift hψ hmap₁ hinj₁ hs₂ h₂₁
  have hs₁T₂ : s₁ ∈ T₂ := lift_mem_slice_lift hψ hmap₂ hinj₂ hs₁ h₁₂
  obtain ⟨b, b', hb, hb', hbb', hb1, hb'1, hT₁eq⟩ := hLines s₁ s₂ T₁ hs₁ hs₂ hdim₁ hdim₂ hc₁ hc₂
    hle₁₂ hle₂₁ ⟨eT₁.trans e₁⟩ (fun g hg => (hT₁le hg).2) hfix₁ hs₂T₁
  obtain ⟨a, a', ha, ha', haa', ha1, ha'1, hT₂eq⟩ := hLines s₂ s₁ T₂ hs₂ hs₁ hdim₂ hdim₁ hc₂ hc₁
    hle₂₁ hle₁₂ ⟨eT₂.trans e₂⟩ (fun g hg => (hT₂le hg).2) hfix₂ hs₁T₂
  rw [inf_comm] at ha ha'
  have hW : a ⊔ a' = fixSp s₁ ⊓ fixSp s₂ := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le ha ha')
    have h' := Submodule.finrank_sup_add_finrank_inf_eq a a'
    rw [haa'.eq_bot, finrank_bot, ha1, ha'1] at h'
    rw [hST.finrank_fix]
    omega
  have hnormT : ∀ z ∈ stabSub (suppSp s₂ ⊔ a') (suppSp s₁ ⊔ a),
      (∀ h ∈ stabSub (suppSp s₂ ⊔ a') (suppSp s₁ ⊔ a), Commute z h) →
      ∀ g ∈ stabSub (suppSp s₁ ⊔ b') (suppSp s₂ ⊔ b),
        z * g * z⁻¹ ∈ stabSub (suppSp s₁ ⊔ b') (suppSp s₂ ⊔ b) := by
    intro z hz hzc g hg
    rw [← hT₂eq] at hz hzc
    rw [← hT₁eq] at hg ⊢
    have hz1 : z ∈ X.comap ψ ⊓ Subgroup.centralizer ({s₁} : Set SL6) :=
      ⟨(hT₂le hz).1, Subgroup.mem_centralizer_singleton_iff.mpr (hzc s₁ hs₁T₂).eq⟩
    exact slice_lift_normal hψ hs₁ (hnorm _) hz1 hg
  rcases hAlign (suppSp s₁) (suppSp s₂) a a' b b' hdim₁ hdim₂ ha1 ha'1 hb1 hb'1
      (by rw [sup_assoc (suppSp s₁ ⊔ suppSp s₂), hW, hST.sup_eq_top])
      (hW ▸ hb) (hW ▸ hb') hbb' hnormT with hcomm | ⟨rfl, rfl, hgen⟩
  ·
    left
    intro x hx y hy
    rw [← hmap₁] at hx
    rw [← hmap₂] at hy
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨h, hh, rfl⟩ := hy
    rw [hT₁eq] at hg
    rw [hT₂eq] at hh
    exact (hcomm g hg h hh).map ψ
  ·
    right
    refine ⟨s₁, s₂, hs₁, rfl, hs₂, rfl, hdim₁, hc₁.disjoint, hdim₂, hc₂.disjoint, ?_⟩
    intro ω hω r k hqr hqk
    set N := sl2Block (s₁ ^ r * s₂ ^ k) (quadOm ω) with hNdef
    have hNstab : N ≤ stabSub b' (suppSp s₁ ⊔ suppSp s₂ ⊔ b) := by
      have hpres : ∀ g ∈ N, ∀ v ∈ suppSp s₁ ⊔ suppSp s₂ ⊔ b,
          (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ suppSp s₁ ⊔ suppSp s₂ ⊔ b := by
        intro g hg v hv
        obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
        rw [Matrix.mulVec_add, hST.sl2Block_fix hg (hb hy)]
        exact Submodule.add_mem_sup (hST.sl2Block_mem_sup hω hqr hqk hg hx) hy
      intro g hg
      exact ⟨fun v hv => hST.sl2Block_fix hg (hb' hv), hpres g hg,
        hpres g⁻¹ (N.inv_mem hg)⟩
    have hNX : N ≤ X.comap ψ ⊓ Subgroup.centralizer ({s₁ ^ r * s₂ ^ k} : Set SL6) := by
      intro g hg
      refine ⟨?_, comap_linearSpecialBlock_le_centralizer _ hg⟩
      have hle : stabSub (suppSp s₁ ⊔ b') (suppSp s₂ ⊔ b) ⊔
          stabSub (suppSp s₂ ⊔ b') (suppSp s₁ ⊔ b) ≤ X.comap ψ := by
        rw [← hT₁eq, ← hT₂eq]
        exact sup_le (fun x hx => (hT₁le hx).1) (fun x hx => (hT₂le hx).1)
      exact hle (hgen (hNstab hg))
    have hNn : ∀ g ∈ X.comap ψ ⊓ Subgroup.centralizer ({s₁ ^ r * s₂ ^ k} : Set SL6),
        ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
      conj_mem_comap_linearSpecialBlock hg.2 hn
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (p := fixSp s₁ ⊓ fixSp s₂) (by
        intro h0
        have := hST.finrank_fix
        rw [h0, finrank_bot] at this
        norm_num at this)
    have hinj : ∀ n ∈ N, ψ n = 1 → n = 1 := fun n hn h1 =>
      eq_one_of_mem_center_of_mulVec_eq (hψ h1) hw0 (hST.sl2Block_fix hn hw)
    obtain ⟨eN⟩ := hST.sl2Block_mulEquiv hω hqr hqk
    obtain ⟨hcomp, hiso⟩ := isComponentOf_pLayer_of_normal_lift hψ hX hST.pow_mul_pow_five hNX
      hNn hinj (hST.sl2Block_isQuasisimple hω hqr hqk) eN
    exact ⟨N.map ψ, hcomp, hiso⟩

theorem ggN2_actualChart_commute_of_inputs
    (ψ : SL6 →* G) (hψ : ψ.ker ≤ Subgroup.center SL6)
    {X : Subgroup G} (hX : X ≤ ψ.range) {u₁ u₂ : G} (hu₁ : u₁ ∈ X) (hu₂ : u₂ ∈ X)
    (ho₁ : orderOf u₁ = 5) (ho₂ : orderOf u₂ = 5) (hc : Commute u₁ u₂)
    (hD : u₂ ∉ Subgroup.zpowers u₁)
    (hH₁ : Nonempty (LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₁} : Set G)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) F4))
    (hH₂ : Nonempty (LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₂} : Set G)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) F4))
    (h₂₁ : u₂ ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₁} : Set G)))
    (h₁₂ : u₁ ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₂} : Set G))) :
    (∀ a ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₁} : Set G)),
      ∀ b ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₂} : Set G)), Commute a b) ∨
    ∃ u ∈ Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂, u ∉ Subgroup.zpowers u₁ ∧
      u ∉ Subgroup.zpowers u₂ ∧ ∃ K : Subgroup G,
        CFSG.Open.IsComponentOf K (LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u} : Set G))) ∧
        Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
  have h5₁ : u₁ ^ 5 = 1 := by rw [← ho₁]; exact pow_orderOf_eq_one u₁
  have h5₂ : u₂ ^ 5 = 1 := by rw [← ho₂]; exact pow_orderOf_eq_one u₂
  rcases ggN2_actualChart_commute_core ψ hψ hX hu₁ hu₂ ho₁ ho₂ hc hD hH₁ hH₂ h₂₁ h₁₂ with
    h | ⟨s₁, s₂, hs₁, rfl, hs₂, rfl, hdim₁, hd₁, hdim₂, hd₂, hb⟩
  · exact Or.inl h
  · right
    obtain ⟨ω, hω⟩ := exists_omega
    obtain ⟨r, hr, hqr⟩ := exists_quadOm_pow hs₁ hdim₁ hd₁ hω
    obtain ⟨k, hk, hqk⟩ := exists_quadOm_pow hs₂ hdim₂ hd₂ hω
    obtain ⟨K, hcomp, hiso⟩ := hb hω hqr hqk
    have hu : ψ (s₁ ^ r * s₂ ^ k) = ψ s₁ ^ r * ψ s₂ ^ k := by rw [map_mul, map_pow, map_pow]
    refine ⟨ψ (s₁ ^ r * s₂ ^ k), ?_, ?_, ?_, K, hcomp, hiso⟩
    · rw [hu]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) r))
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k))
    · intro h
      rw [hu] at h
      apply hD
      apply mem_zpowers_of_pow_mem h5₂ hk
      have h' := Subgroup.mul_mem _ (Subgroup.inv_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers (ψ s₁)) r)) h
      rwa [inv_mul_cancel_left] at h'
    · intro h
      rw [hu] at h
      apply hD
      apply mem_zpowers_symm ho₁ ho₂
      apply mem_zpowers_of_pow_mem h5₁ hr
      have h' := Subgroup.mul_mem _ h (Subgroup.inv_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers (ψ s₂)) k))
      rwa [mul_inv_cancel_right] at h'


theorem ggN2_actualChart_commute_of_matching
    (ψ : SL6 →* G) (hψ : ψ.ker ≤ Subgroup.center SL6)
    {X : Subgroup G} (hX : X ≤ ψ.range) {u₁ u₂ : G} (hu₁ : u₁ ∈ X) (hu₂ : u₂ ∈ X)
    (ho₁ : orderOf u₁ = 5) (ho₂ : orderOf u₂ = 5) (hc : Commute u₁ u₂)
    (hD : u₂ ∉ Subgroup.zpowers u₁)
    (hH₁ : Nonempty (LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₁} : Set G)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) F4))
    (hH₂ : Nonempty (LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₂} : Set G)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) F4))
    (h₂₁ : u₂ ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₁} : Set G)))
    (h₁₂ : u₁ ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₂} : Set G)))
    (htype : ∀ (c : F4) (s₁ s₂ : SL6), ψ s₁ = u₁ → s₁ ^ 5 = 1 → ψ s₂ = u₂ → s₂ ^ 5 = 1 →
      (quadMat c (s₁ : Matrix (Fin 6) (Fin 6) F4) = 0 ↔
        quadMat c (s₂ : Matrix (Fin 6) (Fin 6) F4) = 0)) :
    (∀ a ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₁} : Set G)),
      ∀ b ∈ LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₂} : Set G)), Commute a b) ∨
    ∃ K : Subgroup G, CFSG.Open.IsComponentOf K
        (LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({u₁ * u₂} : Set G))) ∧
      Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
  rcases ggN2_actualChart_commute_core ψ hψ hX hu₁ hu₂ ho₁ ho₂ hc hD hH₁ hH₂ h₂₁ h₁₂ with
    h | ⟨s₁, s₂, hs₁, rfl, hs₂, rfl, hdim₁, hd₁, -, -, hb⟩
  · exact Or.inl h
  · right
    have key : ∀ {c : F4}, c ^ 2 + c + 1 = 0 →
        (∀ v ∈ suppSp s₁, aeval (endo s₁) (quadOm c) v = 0) →
        ∃ K : Subgroup G, CFSG.Open.IsComponentOf K
            (LargeEvenPLayer 5 (X ⊓ Subgroup.centralizer ({ψ s₁ * ψ s₂} : Set G))) ∧
          Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
      intro c hcc h1
      have h2 : ∀ v ∈ suppSp s₂, aeval (endo s₂) (quadOm c) v = 0 :=
        (quadOm_kills_iff s₂ c).mpr
          ((htype c s₁ s₂ rfl hs₁ rfl hs₂).mp ((quadOm_kills_iff s₁ c).mp h1))
      have h1' : ∀ v ∈ suppSp s₁, aeval (endo (s₁ ^ 1)) (quadOm c) v = 0 := by
        rw [pow_one]
        exact h1
      have h2' : ∀ v ∈ suppSp s₂, aeval (endo (s₂ ^ 1)) (quadOm c) v = 0 := by
        rw [pow_one]
        exact h2
      obtain ⟨K, hcomp, hiso⟩ := hb hcc h1' h2'
      rw [pow_one, pow_one, map_mul] at hcomp
      exact ⟨K, hcomp, hiso⟩
    obtain ⟨ω, hω⟩ := exists_omega
    have hω2 : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by linear_combination (ω ^ 2 - ω + 1) * hω
    rcases quadOm_dichotomy hs₁ hdim₁ hd₁ hω with h1 | h1
    · exact key hω h1
    · exact key hω2 h1

end CFSG.StandardType.N2Chart

end
