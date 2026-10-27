module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerLastChoice
public import CFSG.LocalAnalysis.StandardType.GGExcKGToralFrame
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralSmallOfFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeCount
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley

@[expose] def GGLayerExcThreeOddIndexAtTwoTwE6 :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (ψ : (ggU .twistedE6 n 1).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU .twistedE6 n 1).D .twistedE6 n 1 ψ →
    Subgroup.centralizer (G₀ : Set G) = ⊥ →
    ∀ y : G, y ≠ 1 → y ^ 3 = 1 → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU .twistedE6 n 1).D ψ y →
      ∀ C : Subgroup G, IsComponentOf C (G₀ ⊓ Subgroup.centralizer {y}) →
        GGStepTwoExcThreeType C →
          Subgroup.center C = ⊥ ∧ ∀ r ∈ G₀ ⊓ Subgroup.centralizer {y}, r ^ 2 = 1 → r ∈ C

namespace StepTwoToralSmall

theorem exists_toralFrame_E6_coord_eq
    {G : Type} [Group G] {p : ℕ} [NeZero p] {f : ℕ} {Bs G₀ : Subgroup G}
    {S : Matrix (Fin (ggU .E6 6 f).D.rank) (Fin (ggU .E6 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU .E6 6 f).D.rank)} (F : GGStdForm p Bs G₀ (ggU .E6 6 f).D S π f)
    (hS : IsRootGram (ggU .E6 6 f).D S) (hW : FrameW F) (hA : FrameA F) (hAU : FrameAU F) :
    ∃ fr : ToralFrame Tag.E6 p G₀ Bs π, fr.coord = F.coord := by
  obtain ⟨k, hk, rfl⟩ := isRootGram_E6 6 f S hS
  have hroots : (ggU .E6 6 f).D.roots = {α | IsRoot Tag.E6 α} :=
    Set.ext fun α => (mem_roots_E6 6 f α).trans mem_rootFinset
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨
    { coord := F.coord
      coord_inj := F.coord_inj
      coord_fixed := F.coord_fixed
      coord_surj := fun g hg hfix => F.coord_surj g (exists_int_of_mem_t0Sub hg) hfix
      weyl := fun u hu => ?_
      orbit := fun b hb L hL => ?_
      orbitU := fun U hU hne K hK => ?_ }, rfl⟩
  · obtain ⟨m, hm, h⟩ := hW u hu
    exact ⟨m, hm, fun b b' hb' => funext fun i => h b b' hb' i⟩
  · obtain ⟨O, hO, h1, h2⟩ := hA b hb L hL
    rw [hroots] at hO
    exact ⟨O, (isCompOrbit_smul_iff hkpos.ne' _ _ _ _).1 hO, h1, fun b' hb' =>
      h2 b' ((Set.ext_iff.1 (latEigenCoroot_smul hkpos p _ π O) _).2 hb')⟩
  · obtain ⟨O, hO, h1⟩ := hAU U hU hne K hK
    rw [hroots] at hO
    exact ⟨O, (isCompOrbit_smul_iff hkpos.ne' _ _ _ _).1 hO, h1⟩

end StepTwoToralSmall

theorem ggTwE6Three_exists_weyl_move {G : Type} [Group G] {p : ℕ} [NeZero p]
    {G₀ Bs : Subgroup G} (fr : StepTwoToralSmall.ToralFrame TwistTag.E6.tag p G₀ Bs 1) (b : Bs)
    {α₀ α₁ : Fin TwistTag.E6.tag.rank → ℤ} (h₀ : IsRoot TwistTag.E6.tag α₀)
    (h₁ : IsRoot TwistTag.E6.tag α₁)
    (hb : latChar p (Multiplicative.toAdd (fr.coord b)) α₀ = 0) :
    ∃ m ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G), ∃ b' : Bs, (b' : G) = m * b * m⁻¹ ∧
      latChar p (Multiplicative.toAdd (fr.coord b')) α₁ = 0 := by
  classical
  obtain ⟨w₀, hw₀⟩ := TwE6NormThree.exists_smul_single_zero h₀
  obtain ⟨w₁, hw₁⟩ := TwE6NormThree.exists_smul_single_zero h₁
  have hu : (w₁ * w₀⁻¹) • α₀ = α₁ := by
    rw [← hw₀, ← hw₁, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
  have hcomm : StepTwoToralCert.CommutesPi (1 : Equiv.Perm (Fin TwistTag.E6.tag.rank))
      (w₁ * w₀⁻¹) := fun _ => rfl
  obtain ⟨m, hm, hmb⟩ := fr.weyl (w₁ * w₀⁻¹) hcomm
  have hmem : m * (b : G) * m⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hm.2 b).mp b.2
  refine ⟨m, hm, ⟨m * (b : G) * m⁻¹, hmem⟩, rfl, ?_⟩
  have h1 := hmb b ⟨m * (b : G) * m⁻¹, hmem⟩ rfl
  rw [h1]
  have h2 := StepTwoToralCert.latChar_weyl_smul (p := p) (w₁ * w₀⁻¹)⁻¹
    (Multiplicative.toAdd (fr.coord b)) α₁
  rw [inv_inv] at h2
  rw [← h2, ← hu, inv_smul_smul]
  exact hb

theorem ggTwE6Three_exists_involution
    (hF : GGExcKGToralFrame) (hreg : GGExcRegimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n : ℕ} {ψ : (ggU .twistedE6 n 1).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .twistedE6 n 1).D .twistedE6 n 1 ψ)
    (hs1 : GGSixStepOne p B Bs x L D J) (hp : p = 3) {b : G} (hb : b ∈ Bs) (hb1 : b ≠ 1)
    {L₁ : Subgroup G}
    (hL₁ : IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer ({b} : Set G))) :
    ∃ m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (Bs : Set G),
      ∃ g ∈ ggG0 p B x L D J ⊓ Subgroup.centralizer ({b} : Set G), orderOf g = 2 ∧
        g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) := by
  classical
  have ht' : GGExcFive .twistedE6 := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hpp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  have hks : GGKnownSetting .twistedE6 n 1 ψ := ggKnownSetting_of_ctx hctx hs1
  have hcard : p ^ 4 ≤ Nat.card Bs := hctx.pow_four_le_card_bstar
  have hBsN : Bs ≤ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hctx.range_eq]; exact hctx.bstar_le_normalizer
  have hinn : ∀ b ∈ (Bs : Subgroup G), GGPsiInnerDiag (ggU .twistedE6 n 1).D ψ b :=
    hctx.2.2.2.2.2.2.1.2
  have hsyl : ∃ P : Sylow p (Subgroup.normalizer (ψ.range : Set G)),
      Bs ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
        (Subgroup.normalizer (ψ.range : Set G)).subtype ∧
      ∀ E : Subgroup G, E ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
        (Subgroup.normalizer (ψ.range : Set G)).subtype →
        IsElemAbelian p E → Nat.card E = Nat.card Bs → E = Bs := by
    have hnorm : Subgroup.normalizer (ψ.range : Set G) =
        Subgroup.normalizer (ggG0 p B x L D J : Set G) := by rw [hctx.range_eq]
    exact hnorm.symm ▸ hs1.2.2.2.1
  obtain ⟨S, π, F, ⟨hSr, hπ, hπ1, -, hπtw, hF3, -⟩, hW, hA, hAU⟩ :=
    hF .twistedE6 n 1 ht' G ψ hks p hpp hp2
      (hreg G p B Bs x L D J .twistedE6 n 1 ψ ht' hctx hs1) Bs
      hctx.bstar.2.1 hcard hBsN hinn hsyl
  have hπ' : π = 1 := (hπtw rfl).2 (by rw [hp]; decide)
  subst hπ'
  obtain ⟨fr, hfr⟩ := StepTwoToralSmall.exists_toralFrame_E6_coord_eq F hSr hW hA hAU
  have hrange : ψ.range = ggG0 p B x L D J := hctx.range_eq
  have hDBs : D ≤ Bs := hctx.d_le_bstar
  have hDcard := hctx.card_d
  have hJ := hctx.j_isComponentOf_inf
  have hDne : D ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot, hp] at hDcard
    norm_num at hDcard
  have hL₁' : IsComponentOf L₁
      (ψ.range ⊓ Subgroup.centralizer ({((⟨b, hb⟩ : Bs) : G)} : Set G)) := by
    rw [hrange]; exact hL₁
  have hb1' : (⟨b, hb⟩ : Bs) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hJ' : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [hrange]; exact hJ
  obtain ⟨O₀, ⟨α₀, hα₀, -⟩, -, -⟩ := fr.orbit ⟨b, hb⟩ hb1' L₁ hL₁'
  obtain ⟨O₁, ⟨α₁, hα₁, -⟩, -⟩ := fr.orbitU D hDBs hDne J hJ'
  have hroots : (ggU (absTag .twistedE6) 6 1).D.roots = {α | IsRoot Tag.E6 α} :=
    Set.ext fun α => (mem_roots_E6 6 1 α).trans mem_rootFinset
  have hα₀r : IsRoot TwistTag.E6.tag α₀ := hα₀.1
  have hα₁r : IsRoot TwistTag.E6.tag α₁ := hα₁.1
  have hα₀z : latChar p (Multiplicative.toAdd (fr.coord ⟨b, hb⟩)) α₀ = 0 := hα₀.2
  obtain ⟨m, hm, b', hb'eq, hb'α⟩ :=
    ggTwE6Three_exists_weyl_move (G₀ := ψ.range) fr ⟨b, hb⟩ hα₀r hα₁r hα₀z
  have hα₁roots : α₁ ∈ (ggU (absTag .twistedE6) 6 1).D.roots := by
    rw [hroots]; exact hα₁.1
  obtain ⟨γ, u, hγ, hcent, r, hr, hr2⟩ := hF3 α₁ hα₁roots rfl
  have hrψ : r ∈ ψ.range := by
    obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp hr
    exact ⟨y, hy⟩
  have hb'α' : latChar p (Multiplicative.toAdd (F.coord b')) α₁ = 0 := by
    rw [← hfr]; exact hb'α
  have hrb' : r * (b' : G) = (b' : G) * r :=
    Subgroup.mem_centralizer_iff.mp (hcent b' hb'α') r hr
  have hrD : ∀ d ∈ D, r * d = d * r := by
    intro d hd
    have hdBs : d ∈ Bs := hDBs hd
    have hz : latChar p (Multiplicative.toAdd (F.coord ⟨d, hdBs⟩)) α₁ = 0 := by
      rw [← hfr]; exact hα₁.2 ⟨d, hdBs⟩ hd
    exact Subgroup.mem_centralizer_iff.mp (hcent ⟨d, hdBs⟩ hz) r hr
  rw [← hrange]
  have hmψ : m ∈ ψ.range := hm.1
  refine ⟨m, hm, m⁻¹ * r * m, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · exact ψ.range.mul_mem (ψ.range.mul_mem (ψ.range.inv_mem hmψ) hrψ) hmψ
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h1 : m * h = (b' : G) * m := by rw [hb'eq]; group
    calc h * (m⁻¹ * r * m) = m⁻¹ * (m * h) * (m⁻¹ * m) * (m⁻¹ * (r * m)) := by group
      _ = m⁻¹ * ((b' : G) * m) * (m⁻¹ * (r * m)) := by rw [h1]; group
      _ = m⁻¹ * ((b' : G) * r) * m := by group
      _ = m⁻¹ * (r * (b' : G)) * m := by rw [hrb']
      _ = m⁻¹ * r * m * h := by
        have : (b' : G) * m = m * h := h1.symm
        calc m⁻¹ * (r * (b' : G)) * m = m⁻¹ * r * ((b' : G) * m) := by group
          _ = m⁻¹ * r * (m * h) := by rw [this]
          _ = m⁻¹ * r * m * h := by group
  · have := MulEquiv.orderOf_eq (MulAut.conj m⁻¹) r
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this]; exact hr2
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hh
    have hrd := hrD d hd
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc m⁻¹ * d * m * (m⁻¹ * r * m) = m⁻¹ * (d * r) * m := by group
      _ = m⁻¹ * (r * d) * m := by rw [hrd]
      _ = m⁻¹ * r * m * (m⁻¹ * d * m) := by group

theorem ggStepTwoChoiceThreeTwoTag_twistedE6_of_frame_of_layer
    (hF : GGExcKGToralFrame) (hreg : GGExcRegimeInput)
    (hX : GGLayerExcThreeOddIndexAtTwoTwE6) : GGStepTwoChoiceThreeTwoTag .twistedE6 := by
  intro G _ _ p B Bs x L D J n ψ hctx hs1 _ b L₁ hpair hp hexc
  obtain ⟨hb, hb1, hL₁, -⟩ := hpair
  obtain ⟨m, hm, g, hg, hord, hgD⟩ :=
    ggTwE6Three_exists_involution hF hreg hctx hs1 hp hb hb1 hL₁
  subst hp
  obtain ⟨hZ, hinv⟩ := hX G n ψ _ hctx.presents hs1.1 b hb1 (hctx.2.1.2.1.2 b hb)
    (hctx.2.2.2.2.2.2.1.1 hb) (hctx.2.2.2.2.2.2.1.2 b hb) L₁ hL₁ hexc
  have hg2 : g ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  have hgL₁ : g ∈ L₁ := hinv g hg hg2
  refine ⟨m, hm, g, hgL₁, ?_, hgD, ?_⟩
  · by_contra hcon
    push Not at hcon
    have hmem : (⟨g, hgL₁⟩ : L₁) ∈ Subgroup.center L₁ := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (hcon z z.2).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    have hg1 : g = 1 := congrArg Subtype.val hmem
    rw [hg1, orderOf_one] at hord
    omega
  · rw [hord]
    decide

end CFSG.StandardType
