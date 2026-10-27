module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosHolds
public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJoin
public import CFSG.LocalAnalysis.StandardType.GGPumpupCentral
public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
public import CFSG.LocalAnalysis.StandardType.GGCoxReflConv
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompPCore
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSmallImage
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSmallBasic
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneRestSeven
public import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1CitedDefs

public section

namespace CFSG.StandardType.SecFiveL1Odd

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.LieType.RootSystem CFSG.LieType.Universal
open scoped commutatorElement

section Lemma21

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}

theorem le_bstar (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) : D ≤ Bs :=
  hcfg.1.1.2.2.1.1.trans hcfg.1.1.2.1.1

theorem bstar_le_centralizer (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    Bs ≤ Subgroup.centralizer (D : Set G) := by
  have hab : IsMulCommutative Bs := hcfg.1.1.2.1.2.1.1
  intro b hb d hd
  have := hab.is_comm.comm ⟨d, le_bstar hcfg hd⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem centralizer_le_normalizer_L (ha₀ : GGLNoncyclicInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hI : GGThmIHyp p B x L := hcfg.1.1.1
  have hxD : x ∈ D := hcfg.1.1.2.2.1.2.2.2.1
  intro g hg
  refine mem_normalizer_of_sstar hI.2.2.2.2.2.2.1 (ha₀ G p B x L hI) ?_
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact hg h hxD

theorem centralizer_le_normalizer_J (ha₀ : GGLNoncyclicInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  have hDJ : LargeEvenStdSubPre p B x L D J := hcfg.1.1.2.2.1
  rw [hDJ.2.2.2.2.1]
  exact le_normalizer_of_map_conj_le fun g hg =>
    map_conj_largeEvenLayer_le (mem_normalizer_inf_centralizer
      (centralizer_le_normalizer_L ha₀ hcfg hg) hg)

theorem centralizer_le_normalizer_nbr (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hpJ : p ∣ Nat.card J) {y : G} {K : Subgroup G}
    (hK : GGNbr p B x D J y K) :
    Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro c hc
  have hyD : y ∈ D := by
    rw [hK.2.1]
    exact Subgroup.subset_closure (by simp)
  have hcy : c ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    have h1 : c ∈ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hcm : Commute c y := (Subgroup.mem_centralizer_iff.mp hc y hyD).symm
      exact (hcm.symm.zpow_left n).eq
    exact Subgroup.centralizer_le_normalizer (s := ((Subgroup.zpowers y : Subgroup G) : Set G)) h1
  exact normalizer_inf_le_of_ggNbr hL hcfg.1.1.1 hcfg.1.1.2.2 hpJ hK
    ⟨hcy, centralizer_le_normalizer_J ha₀ hcfg hc⟩

theorem J_le (hL : GGLBalanceInput) (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hpJ : p ∣ Nat.card J) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) : J ≤ X := by
  rcases hX with rfl | hX
  · exact (hcfg.1.1.2.2.1.2.2.2.2.2.1.1).trans inf_le_left
  · obtain ⟨y, hy⟩ := hcfg.2.2.2.1.2 X hX
    exact le_of_ggNbr hL hcfg.1.1.1 hcfg.1.1.2.2 hpJ hy

end Lemma21

section Lemma22

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}

theorem p_dvd_card_J (ha₀ : GGLNoncyclicInput) (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {r : MulAut ↥Bs}
    (hr : r ∈ ggAutomizer J Bs) (hrefl : GGIsReflection p r) : p ∣ Nat.card J := by
  have hp : p.Prime := hcfg.1.1.1.2.2.2.2.2.1.1
  have hel : ∀ b ∈ Bs, b ^ p = 1 := hcfg.1.1.2.1.2.1.2
  have hmove : ∃ b : ↥Bs, r b ≠ b := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hall : Nat.card {b : ↥Bs // r b = b} = Nat.card ↥Bs :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hcon)
    have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
    have := hrefl.2
    rw [hall] at this
    have h1 : p = 1 := by
      have := Nat.eq_of_mul_eq_mul_left hpos (this.trans (mul_one _).symm)
      exact this
    exact hp.one_lt.ne' h1
  obtain ⟨b, hb⟩ := hmove
  obtain ⟨j, hjJ, hjN, hrj⟩ := mem_ggAutomizer_iff.mp hr
  have hbN : (b : G) ∈ Subgroup.normalizer (J : Set G) :=
    centralizer_le_normalizer_J ha₀ hcfg (bstar_le_centralizer hcfg b.2)
  set z : G := j * (b : G) * j⁻¹ * (b : G)⁻¹ with hz
  have hzJ : z ∈ J := by
    have h1 : (b : G) * j⁻¹ * (b : G)⁻¹ ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp hbN j⁻¹).mp (J.inv_mem hjJ)
      exact this
    have h2 : z = j * ((b : G) * j⁻¹ * (b : G)⁻¹) := by simp [hz, mul_assoc]
    rw [h2]; exact J.mul_mem hjJ h1
  have hzB : z ∈ Bs := by
    have h1 : j * (b : G) * j⁻¹ ∈ Bs := by
      have := (Subgroup.mem_normalizer_iff.mp hjN (b : G)).mp b.2
      exact this
    exact Bs.mul_mem h1 (Bs.inv_mem b.2)
  have hz1 : z ≠ 1 := by
    intro h
    apply hb
    apply Subtype.ext
    rw [hrj]
    have : j * (b : G) * j⁻¹ = (b : G) := by
      have := congrArg (· * (b : G)) h
      simpa [hz] using this
    exact this
  have hzp : z ^ p = 1 := hel z hzB
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf z = p := (orderOf_eq_prime hzp hz1)
  have := Subgroup.orderOf_dvd_natCard J hzJ
  rwa [hord] at this

theorem le_ggHyperplane_of_mem_automizer_J (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer J Bs) : D ≤ ggHyperplane Bs r := by
  have hJC : J ≤ Subgroup.centralizer (D : Set G) :=
    (hcfg.1.1.2.2.1.2.2.2.2.2.1.1).trans inf_le_right
  obtain ⟨g, hg, -, hr⟩ := mem_ggAutomizer_iff.mp hr
  intro d hd
  refine Subgroup.mem_map.mpr ⟨⟨d, le_bstar hcfg hd⟩, ?_, rfl⟩
  show (r : ↥Bs →* ↥Bs) _ = MonoidHom.id ↥Bs _
  apply Subtype.ext
  have := Subgroup.mem_centralizer_iff.mp (hJC hg) d hd
  show ((r ⟨d, le_bstar hcfg hd⟩ : ↥Bs) : G) = d
  rw [hr]
  show g * d * g⁻¹ = d
  rw [← this]
  simp

theorem exists_conj_le_ggHyperplane
    (ha₀ : GGLNoncyclicInput) (hKGp : GGSecFiveKGPosInput) (hJR : GGSecFiveJReflInput)
    (hL : GGLBalanceInput) (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) (hXs : GGSplitLie p X) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e) :
    ∃ g ∈ X, g ∈ Subgroup.normalizer (Bs : Set G) ∧
      D ≤ (ggHyperplane Bs r).map (MulAut.conj g).toMonoidHom := by
  classical
  obtain ⟨t, n, f, ψ, hadm, -, -, -, ht, -, hTB⟩ :=
    hKGp G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX hXs
  obtain ⟨ε, hεr, -, -⟩ := hTB
  obtain ⟨hW, h3⟩ := ggTag_weylMatrix ht hadm
  have hpres' : GGCoxeterPres p (ggAutomizer X Bs)
      (coxeterMatrix (ggU t n f).D.isFiniteType) ε := ⟨hW, hεr⟩
  have hr : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
  have hr' := ggCoxRefl_of_cfg hcfg (ggAutomizer_le_top X Bs) hpres' h3 hrA hr
  obtain ⟨r₁, hr₁J, hrefl₁⟩ := hJR G p B Bs x L D J 𝒦 hcfg hsplit
  have hpJ : p ∣ Nat.card J := p_dvd_card_J ha₀ hcfg hr₁J hrefl₁
  have hr₁A : r₁ ∈ ggAutomizer X Bs := ggTBJ_automizer_le hL hcfg hpJ hX hr₁J
  have hr₁' := ggCoxRefl_of_cfg hcfg (ggAutomizer_le_top X Bs) hpres' h3 hr₁A hrefl₁
  obtain ⟨a, haA, hra⟩ := ggCoxRefl_conj_of_connected ε
    (ggSimplyLacedConnected_of_weyl hW h3) hr₁' hr'
  obtain ⟨g₀, hg₀X, hg₀N, hg₀a⟩ := mem_ggAutomizer_iff.mp haA
  have hmap : (ggHyperplane Bs r₁).map (MulAut.conj g₀).toMonoidHom = ggHyperplane Bs r := by
    rw [ggHyperplane_map_conj hg₀a, hra]
  refine ⟨g₀⁻¹, X.inv_mem hg₀X, Subgroup.inv_mem _ hg₀N, ?_⟩
  intro d hd
  have hdH : d ∈ ggHyperplane Bs r₁ := le_ggHyperplane_of_mem_automizer_J hcfg hr₁J hd
  have hmem : g₀ * d * g₀⁻¹ ∈ ggHyperplane Bs r := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨d, hdH, rfl⟩
  exact Subgroup.mem_map.mpr ⟨g₀ * d * g₀⁻¹, hmem, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem card_centralizer_inf_map_conj {X H : Subgroup G} {g : G} (hg : g ∈ X) :
    Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓
        Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) =
      Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (H : Set G)) := by
  have hX : X.map (MulAut.conj g).toMonoidHom = X := map_conj_eq_of_mem hg
  have h1 : Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (H : Set G)).map
        (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, ggMap_conj_centralizer,
      ggMap_conj_centralizer, hX]
  rw [h1]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

end Lemma22

section TheoremO

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}

theorem commutator_eq_bot_of_isComponentOf_of_two {H K R : Subgroup G}
    (hK : CFSG.Assembly.IsComponentOf K H) (hRH : R ≤ H) (hR : IsPGroup 2 R)
    (hKR : K ≤ Subgroup.normalizer (R : Set G)) : ⁅K, R⁆ = ⊥ := by
  have hKH : K ≤ H := hK.1
  have hsub : CFSG.Assembly.IsSubnormal K (K ⊔ R) := by
    have hopen :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open K H).1 hK.2.1
    have h1 := hopen.inf_of_le (sup_le hKH hRH)
    rw [inf_eq_left.mpr le_sup_left] at h1
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open _ _).2 h1
  have hnorm : (R.subgroupOf (K ⊔ R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hKR Subgroup.le_normalizer)
  have hRs : CFSG.Assembly.IsSubnormal R (K ⊔ R) :=
    CFSG.Assembly.IsSubnormal.step le_sup_right hnorm (CFSG.Assembly.IsSubnormal.refl _)
  rcases isComponentOf_le_or_commutator_eq_bot (⟨le_sup_left, hsub, hK.2.2⟩ :
    CFSG.Assembly.IsComponentOf K (K ⊔ R)) hRs with h | h
  · exfalso
    have hK2 : IsPGroup 2 ↥K := hR.to_le h
    haveI : Group.IsNilpotent ↥K := hK2.isNilpotent
    have hqs := hK.2.2
    haveI : Nontrivial (↥K ⧸ Subgroup.center ↥K) := hqs.2.toNontrivial
    haveI : Nontrivial ↥K := (QuotientGroup.mk_surjective (s := Subgroup.center ↥K)).nontrivial
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K)).ne hqs.1
  · exact h

theorem commutator_eq_bot_of_perfect {J R : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (h : ⁅⁅R, J⁆, J⁆ = ⊥) : ⁅J, R⁆ = ⊥ := by
  have h2 : ⁅⁅J, R⁆, J⁆ = ⊥ := by rw [Subgroup.commutator_comm J R]; exact h
  have := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := J) (H₂ := J) (H₃ := R) h2 h
  rwa [hJ] at this

theorem commutator_self_of_isComponentOf {H K : Subgroup G} (hK : CFSG.Assembly.IsComponentOf K H) :
    ⁅K, K⁆ = K := by
  rw [← Subgroup.map_subtype_commutator, hK.2.2.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem le_centralizer_of_commute {X T : Subgroup G} (hX : ⁅X, X⁆ = X)
    (h : ∀ t ∈ T, ∀ g ∈ X, ∀ k ∈ X, Commute (t * g * t⁻¹ * g⁻¹) k) :
    T ≤ Subgroup.centralizer (X : Set G) := by
  have hTX : ⁅T, X⁆ ≤ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.commutator_le]
    intro t ht g hg
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact ((h t ht g hg k hk).eq).symm
  have h3 : ⁅⁅T, X⁆, X⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro c hc g hg
    have hcg := Subgroup.mem_centralizer_iff.mp (hTX hc) g hg
    rw [Subgroup.mem_bot, commutatorElement_def, ← hcg]
    group
  have hXT := commutator_eq_bot_of_perfect hX h3
  rw [Subgroup.commutator_comm] at hXT
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXT

theorem eq_of_commute_of_dihedral {ι : Type} {M : CoxeterMatrix ι} (a b : ι)
    (hab : ∀ i, i = a ∨ i = b) (h3 : a ≠ b → M.M a b = 3) (x y : M.Group)
    (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hc : x * y = y * x) :
    x = y := by
  have hinj : Function.Injective M.simple := by
    rw [← CoxeterMatrix.toCoxeterSystem_simple]
    exact CoxeterSystem.simple_injective _
  have hss : ∀ i, M.simple i * M.simple i = 1 := fun i => by
    simpa [CoxeterMatrix.toCoxeterSystem_simple] using
      (CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem i)
  set sa := M.simple a with hsa
  set sb := M.simple b with hsb
  have haa : ∀ z : M.Group, sa * (sa * z) = z := fun z => by rw [← mul_assoc, hss, one_mul]
  have hbb : ∀ z : M.Group, sb * (sb * z) = z := fun z => by rw [← mul_assoc, hss, one_mul]
  have hbr : sa * (sb * sa) = sb * (sa * sb) := by
    by_cases h : a = b
    · subst h; rfl
    · simpa [mul_assoc] using ggSimplyLaced_braid (h3 h)
  have hall : ∀ g : M.Group, g = 1 ∨ g = sa ∨ g = sb ∨ g = sa * sb ∨ g = sb * sa ∨
      g = sa * (sb * sa) := by
    intro g
    refine M.toCoxeterSystem.simple_induction_left (p := fun g => g = 1 ∨ g = sa ∨ g = sb ∨
      g = sa * sb ∨ g = sb * sa ∨ g = sa * (sb * sa)) g (Or.inl rfl) ?_
    intro w i hw
    rw [CoxeterMatrix.toCoxeterSystem_simple]
    rcases hab i with hi | hi
    · have hsi : M.simple i = sa := by rw [hi]
      rw [hsi]
      rcases hw with hw | hw | hw | hw | hw | hw <;> rw [hw]
      · exact Or.inr (Or.inl (mul_one _))
      · exact Or.inl (hss a)
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inl (haa _)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (haa _)))))
    · have hsi : M.simple i = sb := by rw [hi]
      rw [hsi]
      rcases hw with hw | hw | hw | hw | hw | hw <;> rw [hw]
      · exact Or.inr (Or.inr (Or.inl (mul_one _)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inl (hss b)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbr.symm))))
      · exact Or.inr (Or.inl (hbb _))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hbr, hbb]))))
  by_cases hab' : a = b
  · have hbs : sb = sa := by rw [hsb, hsa, hab']
    have key : ∀ g : M.Group, g ≠ 1 → g = sa := by
      intro g hg
      rcases hall g with h | h | h | h | h | h
      · exact absurd h hg
      · exact h
      · rw [h, hbs]
      · exfalso; apply hg; rw [h, hbs]; exact hss a
      · exfalso; apply hg; rw [h, hbs]; exact hss a
      · rw [h, hbs]; exact haa sa
    rw [key x hx1, key y hy1]
  · have hne : sa ≠ sb := fun h => hab' (hinj h)
    have hnc : sa * sb ≠ sb * sa := by
      intro h
      apply hne
      have e1 : sa * (sb * sa) = sb := by rw [← mul_assoc, h, mul_assoc, hss, mul_one]
      have e2 : sb * (sa * sb) = sa := by rw [← mul_assoc, ← h, mul_assoc, hss, mul_one]
      exact e2.symm.trans (hbr.symm.trans e1)
    have key : ∀ g : M.Group, g * g = 1 → g ≠ 1 → g = sa ∨ g = sb ∨ g = sa * (sb * sa) := by
      intro g hgg hg
      rcases hall g with h | h | h | h | h | h
      · exact absurd h hg
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exfalso
        apply hne
        rw [h] at hgg
        have : sb * sa = 1 := by
          calc sb * sa = sa * (sa * (sb * sa)) := (haa _).symm
            _ = sa * (sb * (sa * sb)) := by rw [hbr]
            _ = sa * sb * (sa * sb) := by rw [mul_assoc]
            _ = 1 := hgg
        calc sa = sb * (sb * sa) := (hbb sa).symm
          _ = sb := by rw [this, mul_one]
      · exfalso
        apply hne
        rw [h] at hgg
        have : sa * sb = 1 := by
          calc sa * sb = sb * (sb * (sa * sb)) := (hbb _).symm
            _ = sb * (sa * (sb * sa)) := by rw [hbr]
            _ = sb * sa * (sb * sa) := by rw [mul_assoc]
            _ = 1 := hgg
        calc sa = sa * 1 := (mul_one _).symm
          _ = sa * (sa * sb) := by rw [this]
          _ = sb := haa _
      · exact Or.inr (Or.inr h)
    have e1 : sa * (sa * (sb * sa)) = sb * sa := haa _
    have e2 : sa * (sb * sa) * sa = sa * sb := by rw [mul_assoc, mul_assoc, hss, mul_one]
    have e3 : sb * (sa * (sb * sa)) = sa * sb := by rw [hbr, hbb]
    have e4 : sa * (sb * sa) * sb = sb * sa := by rw [hbr, mul_assoc, mul_assoc, hss, mul_one]
    rcases key x hx hx1 with hx' | hx' | hx' <;> rcases key y hy hy1 with hy' | hy' | hy' <;>
      rw [hx', hy'] at hc ⊢
    · exact absurd hc hnc
    · exfalso; rw [e1, e2] at hc; exact hnc hc.symm
    · exact absurd hc.symm hnc
    · exfalso; rw [e3, e4] at hc; exact hnc hc
    · exfalso; rw [e2, e1] at hc; exact hnc hc
    · exfalso; rw [e4, e3] at hc; exact hnc hc.symm

theorem weyl_ad_or_e_or_small {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) :
    GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M ∨
      ∃ (n : ℕ) (e : Fin n ≃ ι), 1 ≤ n ∧ n ≤ 2 ∧ M = (CoxeterMatrix.A n).reindex e := by
  rcases hM with ⟨n, e, hn, hcase⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
  · rcases hcase with hA | hB | hD
    · by_cases hn3 : 3 ≤ n
      · exact Or.inl (Or.inl ⟨n, e, hn3, hA⟩)
      · exact Or.inr (Or.inr ⟨n, e, hn, by omega, hA⟩)
    · obtain ⟨hn2, hB⟩ := hB
      exfalso
      have hne : e ⟨n - 1, by omega⟩ ≠ e ⟨n - 2, by omega⟩ := by
        intro hh
        have hv := congrArg Fin.val (e.injective hh)
        simp only [Fin.val_mk] at hv
        omega
      have hle := h3 (e ⟨n - 1, by omega⟩) (e ⟨n - 2, by omega⟩) hne
      rw [hB] at hle
      have hlab : ((CoxeterMatrix.B n).reindex e).M (e ⟨n - 1, by omega⟩)
          (e ⟨n - 2, by omega⟩) = 4 := by
        rw [CoxeterMatrix.reindex_apply]
        simp only [Equiv.symm_apply_apply]
        have hneFin : (⟨n - 1, by omega⟩ : Fin n) ≠ ⟨n - 2, by omega⟩ := by
          intro hh
          have hv := congrArg Fin.val hh
          simp only [Fin.val_mk] at hv
          omega
        simp [CoxeterMatrix.B, Matrix.of_apply, hneFin]
      rw [hlab] at hle
      omega
    · exact Or.inl (Or.inr ⟨n, e, hD.1, hD.2⟩)
  · exact Or.inr (Or.inl (Or.inl ⟨e, hE6⟩))
  · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨e, hE7⟩)))
  · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨e, hE8⟩)))
  · exfalso
    have hne : e 1 ≠ e 2 := by
      intro hh
      have hv := congrArg Fin.val (e.injective hh)
      norm_num at hv
    have hle := h3 (e 1) (e 2) hne
    rw [hF4] at hle
    have hlab : ((CoxeterMatrix.F₄).reindex e).M (e 1) (e 2) = 4 := by
      rw [CoxeterMatrix.reindex_apply]
      simp only [Equiv.symm_apply_apply]
      simp [CoxeterMatrix.F₄, Matrix.of_apply, Matrix.cons_val']
    rw [hlab] at hle
    omega
  · exfalso
    have hne : e 0 ≠ e 1 := by
      intro hh
      have hv := congrArg Fin.val (e.injective hh)
      norm_num at hv
    have hle := h3 (e 0) (e 1) hne
    rw [hG2] at hle
    have hlab : ((CoxeterMatrix.G₂).reindex e).M (e 0) (e 1) = 6 := by
      rw [CoxeterMatrix.reindex_apply]
      simp only [Equiv.symm_apply_apply]
      simp [CoxeterMatrix.G₂, Matrix.of_apply, Matrix.cons_val']
    rw [hlab] at hle
    omega

theorem exists_nonadj_pair {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M)
    (hcard : 3 ≤ Nat.card ι) : ∃ u b : ι, u ≠ b ∧ M.M u b = 2 := by
  rcases hM with ⟨n, e, hn, hX⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hF⟩ | ⟨e, hG⟩
  · rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    refine ⟨e ⟨0, by omega⟩, e ⟨2, by omega⟩, e.injective.ne (by simp [Fin.ext_iff]), ?_⟩
    rcases hX with hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩
    · rw [hA, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact coxeterMatrixA_eq_two n _ _ (by simp)
    · rw [hB, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
      simp only [CoxeterMatrix.B, Matrix.of_apply, if_neg hne]
      split_ifs <;> first | rfl | (exfalso; simp_all; try omega)
    · rw [hD, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      refine ggCoxeterMatrixD_eq_two hn4 _ _ (by simp [Fin.ext_iff]) ?_ ?_ <;>
        simp only [CFSG.Timmesfeld.edgeD, Fin.val_mk] <;> omega
  · refine ⟨e 0, e 1, e.injective.ne (by decide), ?_⟩
    rw [hE, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  · refine ⟨e 0, e 1, e.injective.ne (by decide), ?_⟩
    rw [hE, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  · refine ⟨e 0, e 1, e.injective.ne (by decide), ?_⟩
    rw [hE, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  · refine ⟨e 0, e 2, e.injective.ne (by decide), ?_⟩
    rw [hF, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  · rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    omega

theorem isWeylMatrixAD_or_E
    (hKGp : GGSecFiveKGPosInput) (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) :
    GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M := by
  classical
  rcases weyl_ad_or_e_or_small hpres.1 hle3 with hAD | hE | ⟨n, e', hn1, hn2, hM⟩
  · exact Or.inl hAD
  · exact Or.inr hE
  · exfalso
    obtain ⟨t, n', f, ψ, hadm, hrank, -, -, ht, -, hTB⟩ :=
      hKGp G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 L (Or.inl rfl) hsplit
    obtain ⟨ε, -, -, -⟩ := hTB
    obtain ⟨hW, -⟩ := ggTag_weylMatrix ht hadm
    have h3 : 3 ≤ (ggU t n' f).D.rank := by
      rw [show (ggU t n' f).D.rank = bnRank t n' from
        lieUniversal_rank_eq_bnRank t n' 2 f Nat.prime_two hadm hrank]
      exact hrank
    obtain ⟨u, b, hub, hlab⟩ := exists_nonadj_pair hW
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact h3)
    set M' := coxeterMatrix (ggU t n' f).D.isFiniteType with hM'
    have hle : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
      ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
    let φ : M'.Group →* M.Group :=
      (e.symm : ↥(ggAutomizerJoin L Bs 𝒦) ≃* M.Group).toMonoidHom.comp
        ((Subgroup.inclusion hle).comp ε.toMonoidHom)
    have hφ : Function.Injective φ := by
      intro g g' h
      exact ε.injective (Subgroup.inclusion_injective hle (e.symm.injective h))
    have hsi : Function.Injective M'.simple := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.simple_injective _
    have hss : ∀ i, M'.simple i * M'.simple i = 1 := fun i => by
      simpa [CoxeterMatrix.toCoxeterSystem_simple] using
        (CoxeterSystem.simple_mul_simple_self M'.toCoxeterSystem i)
    have hs1 : ∀ i, M'.simple i ≠ 1 := fun i => by
      simpa [CoxeterMatrix.toCoxeterSystem_simple] using
        (CoxeterSystem.simple_ne_one M'.toCoxeterSystem i)
    have hne : φ (M'.simple u) ≠ φ (M'.simple b) := fun h => hub (hsi (hφ h))
    have hcomm : φ (M'.simple u) * φ (M'.simple b) = φ (M'.simple b) * φ (M'.simple u) := by
      rw [← map_mul, ← map_mul, ggSimplyLaced_simple_comm hlab]
    refine hne (eq_of_commute_of_dihedral (M := M) (e' ⟨0, by omega⟩) (e' ⟨n - 1, by omega⟩) ?_ ?_
      _ _ ?_ ?_ ?_ ?_ hcomm)
    · intro i
      obtain ⟨k, rfl⟩ := e'.surjective i
      by_cases hk : k.val = 0
      · exact Or.inl (congrArg e' (Fin.ext hk))
      · exact Or.inr (congrArg e' (Fin.ext (by simp only [Fin.val_mk]; omega)))
    · intro hab
      have hn2' : n = 2 := by
        by_contra hne2
        apply hab
        exact congrArg e' (Fin.ext (by simp only [Fin.val_mk]; omega))
      subst hn2'
      rw [hM, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact coxeterMatrixA_eq_three 2 _ _ (by simp)
    · rw [← map_mul, hss, map_one]
    · rw [← map_mul, hss, map_one]
    · intro h
      exact hs1 u (hφ (h.trans (map_one φ).symm))
    · intro h
      exact hs1 b (hφ (h.trans (map_one φ).symm))

theorem le_centralizer_ggG0
    (ha₀ : GGLNoncyclicInput) (hKGp : GGSecFiveKGPosInput)
    (hKC : GGSecFiveKGCentInput) (hSplit : GGSecFiveSplitNbrInput)
    (hJoin : GGSecFiveJoinRegionInput) (hL : GGLBalanceInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hpJ : p ∣ Nat.card J) {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hT : T ≤ Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (J : Set G)) :
    T ≤ Subgroup.centralizer (ggG0 p B x L D J : Set G) := by
  have hI : GGThmIHyp p B x L := hcfg.1.1.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.1.1.2.2
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
  have key : ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X → ⁅X, X⁆ = X →
      Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (X : Set G) →
        T ≤ Subgroup.centralizer (X : Set G) := by
    intro X hX hXs hXp hXN
    refine le_centralizer_of_commute hXp fun t ht => ?_
    have h2 : ∃ k : ℕ, t ^ (2 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    exact hKC G p B Bs x L D J 𝒦 hcfg hsplit X hX hXs t h2 (hXN (hT ht).1) (hT ht).1 (hT ht).2
  have hLT : T ≤ Subgroup.centralizer (L : Set G) :=
    key L (Or.inl rfl) hsplit (commutator_self_of_isComponentOf hS.2.2.2.1)
      (centralizer_le_normalizer_L ha₀ hcfg)
  have hKT : ∀ K ∈ 𝒦, T ≤ Subgroup.centralizer (K : Set G) := by
    intro K hK
    obtain ⟨y, hy⟩ := hcfg.2.2.2.1.2 K hK
    exact key K (Or.inr hK) (hSplit G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 K hK)
      (commutator_self_of_isComponentOf
        (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hy)).1)
      (centralizer_le_normalizer_nbr ha₀ hL hcfg hpJ hy)
  rw [hJoin G p B Bs x L D J 𝒦 hcfg hsplit
    ⟨ι, M, e, hpres, isWeylMatrixAD_or_E hKGp hcfg hsplit hpres hle3⟩, Subgroup.le_centralizer_iff]
  exact sup_le (Subgroup.le_centralizer_iff.mp hLT)
    (iSup₂_le fun K hK => Subgroup.le_centralizer_iff.mp (hKT K hK))

theorem not_isPGroup_two_of_isQuasisimple {K : Subgroup G} (hK : CFSG.Assembly.IsQuasisimple K)
    (h : IsPGroup 2 ↥K) : False := by
  haveI : Group.IsNilpotent ↥K := h.isNilpotent
  haveI : Nontrivial (↥K ⧸ Subgroup.center ↥K) := hK.2.toNontrivial
  haveI : Nontrivial ↥K := (QuotientGroup.mk_surjective (s := Subgroup.center ↥K)).nontrivial
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K)).ne hK.1

theorem exists_commutator_ne_bot (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hT : T ≤ Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (J : Set G)) :
    ∃ d ∈ D, d ≠ 1 ∧
      ⁅J, pCoreOf 2 (Subgroup.normalizer (T : Set G)) ⊓
        Subgroup.centralizer ({d} : Set G)⁆ ≠ ⊥ := by
  have hI : GGThmIHyp p B x L := hcfg.1.1.1
  have hDJ : LargeEvenStdSubPre p B x L D J := hcfg.1.1.2.2.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hI.2.2.2.2.2.1.2.1
  have hct : IsCharTwoType G := hI.2.2.2.1
  have hJq : CFSG.Assembly.IsQuasisimple J := hDJ.2.2.2.2.2.1.2.2
  set N : Subgroup G := Subgroup.normalizer (T : Set G) with hN
  set Q : Subgroup G := pCoreOf 2 N with hQ
  have hQ2 : IsPGroup 2 ↥Q := ggIsPGroup_pCoreOf 2 N
  have hTN : IsTwoLocal N := ⟨T, hT1, hT2, rfl⟩
  have hCN : Subgroup.centralizer (T : Set G) ≤ N := Subgroup.centralizer_le_normalizer _
  have hJC : J ≤ Subgroup.centralizer (T : Set G) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp (hT ht).2 j hj).symm
  have hDC : D ≤ Subgroup.centralizer (T : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp (hT ht).1 d hd).symm
  have hA : ⁅J, Q⁆ ≠ ⊥ := by
    intro h
    have hJle : J ≤ Q := by
      have h1 : J ≤ Subgroup.centralizer (Q : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      intro j hj
      exact hct N hTN ⟨hCN (hJC hj), h1 hj⟩
    exact not_isPGroup_two_of_isQuasisimple hJq (hQ2.to_le hJle)
  by_contra hcon
  push Not at hcon
  apply hA
  have hle : Q ≤ Subgroup.centralizer (J : Set G) := by
    refine ggLe_of_plane_centralizers hp (E := D) hDJ.2.1 hDJ.2.2.1 ?_
      (ggNot_dvd_card_of_isPGroup_two hp hp2 hQ2) ?_
    · intro d hd
      exact ggMem_normalizer_pCoreOf (hCN (hDC hd))
    · intro d hd hd1
      have := hcon d hd hd1
      rw [Subgroup.commutator_comm] at this
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp this
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle

theorem commutator_eq_bot_of_component {T K : Subgroup G} {d : G}
    (hT2 : IsPGroup 2 T) (hK : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({d} : Set G)))
    (hJK : J ≤ K) (hKT : K ≤ Subgroup.centralizer (T : Set G)) :
    ⁅J, pCoreOf 2 (Subgroup.normalizer (T : Set G)) ⊓ Subgroup.centralizer ({d} : Set G)⁆ = ⊥ := by
  have hR2 : IsPGroup 2 ↥(pCoreOf 2 (Subgroup.normalizer (T : Set G)) ⊓
      Subgroup.centralizer ({d} : Set G)) :=
    (ggIsPGroup_pCoreOf 2 (Subgroup.normalizer (T : Set G))).to_le inf_le_left
  have hKN : K ≤ Subgroup.normalizer
      ((pCoreOf 2 (Subgroup.normalizer (T : Set G)) ⊓ Subgroup.centralizer ({d} : Set G) :
        Subgroup G) : Set G) := by
    intro k hk
    have hkT : k ∈ Subgroup.normalizer (T : Set G) :=
      Subgroup.centralizer_le_normalizer (s := (T : Set G)) (hKT hk)
    have h1 : k ∈ Subgroup.normalizer (pCoreOf 2 (Subgroup.normalizer (T : Set G)) : Set G) :=
      ggMem_normalizer_pCoreOf hkT
    have h2 : k ∈ Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G) :=
      Subgroup.le_normalizer (hK.1 hk)
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro h
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    rw [h1 h, h2 h]
  have := commutator_eq_bot_of_isComponentOf_of_two hK inf_le_right hR2 hKN
  exact le_bot_iff.mp (this ▸ Subgroup.commutator_mono hJK le_rfl)

theorem comm_le_pPrimeCoreOf_of_cover {p : ℕ} [Fact p.Prime] {Y X J V : Subgroup G}
    (hX : LargeEvenPComponent p Y X) (hJX : J ≤ X) (hcov : X = J ⊔ LargeEvenPPrimeCoreOf p X)
    (hVY : V ≤ Y) (hJV : J ≤ Subgroup.normalizer (V : Set G)) (hV : IsPGroup 2 V) :
    ⁅J, V⁆ ≤ LargeEvenPPrimeCoreOf p Y := by
  set π := QuotientGroup.mk' (LargeEvenPPrimeCore p ↥Y) with hπ
  have hXY : X ≤ Y := hX.1
  have hJY : J ≤ Y := hJX.trans hXY
  set E := LargeEvenPPrimeCoreOf p X with hE
  have hEX : E ≤ X := Subgroup.map_subtype_le _
  have hEY : E ≤ LargeEvenPPrimeCoreOf p Y := ggPPrimeCoreOf_le_of_isSubnormal hX.2.1
  have hEbot := ggMap_eq_bot_of_le_pPrimeCoreOf p hEY
  have hsplit : X.subgroupOf Y = J.subgroupOf Y ⊔ E.subgroupOf Y := by
    rw [← Subgroup.subgroupOf_sup hJY (hEX.trans hXY)]
    congr 1
  have heq : (J.subgroupOf Y).map π = (X.subgroupOf Y).map π := by
    refine le_antisymm (Subgroup.map_mono (Subgroup.subgroupOf_mono Y hJX)) ?_
    rw [hsplit, Subgroup.map_sup, hEbot, sup_bot_eq]
  have hJcomp : CFSG.Assembly.IsComponentOf ((J.subgroupOf Y).map π) ⊤ := heq ▸ hX.2.2.1
  have hVq : IsPGroup 2 ↥((V.subgroupOf Y).map π) :=
    (hV.of_equiv (Subgroup.subgroupOfEquivOfLe hVY).symm).map π
  have hc := ggCommutator_eq_bot_of_isComponentOf hJcomp le_top (ggMap_le_normalizer_map p hJV)
    hVq
  rw [← Subgroup.map_commutator, ← ggSubgroupOf_commutator hJY hVY] at hc
  exact ggLe_pPrimeCoreOf_of_map_eq_bot p (Subgroup.commutator_le.mpr fun a ha b hb =>
    commutatorElement_mem_of_mem (hJY ha) (hVY hb)) hc

theorem commutator_eq_bot_of_cover (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hpJ : p ∣ Nat.card J) {d : G}
    (hD : D = Subgroup.closure {x, d})
    (hcov : ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J =
      J ⊔ LargeEvenPPrimeCoreOf p (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J))
    {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hT : T ≤ Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (J : Set G)) :
    ⁅J, pCoreOf 2 (Subgroup.normalizer (T : Set G)) ⊓ Subgroup.centralizer ({d} : Set G)⁆ = ⊥ := by
  have hI : GGThmIHyp p B x L := hcfg.1.1.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.1.1.2.2
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hXpc, hJX, -, -⟩ := pumpup_of_stdSub (ggPumpupInput_of_lBalance hL) hI hDJ hpJ hD
  obtain ⟨-, -, hd1, -⟩ := facts_of_closure_pair hI hDJ hD
  have hdD : d ∈ D := hD ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  set Y : Subgroup G := Subgroup.centralizer ({d} : Set G) with hY
  set N : Subgroup G := Subgroup.normalizer (T : Set G) with hN
  set Q : Subgroup G := pCoreOf 2 N with hQ
  set R : Subgroup G := Q ⊓ Y with hR
  have hQ2 : IsPGroup 2 ↥Q := ggIsPGroup_pCoreOf 2 N
  have hR2 : IsPGroup 2 ↥R := hQ2.to_le inf_le_left
  have hCN : Subgroup.centralizer (T : Set G) ≤ N := Subgroup.centralizer_le_normalizer _
  have hJC : J ≤ Subgroup.centralizer (T : Set G) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp (hT ht).2 j hj).symm
  have hXY : ggLayerClosure p Y J ≤ Y := hXpc.1
  have hJY : J ≤ Y := hJX.trans hXY
  have hJR : J ≤ Subgroup.normalizer (R : Set G) := by
    intro j hj
    have h1 : j ∈ Subgroup.normalizer (Q : Set G) := ggMem_normalizer_pCoreOf (hCN (hJC hj))
    have h2 : j ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer (hJY hj)
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro h
    simp only [SetLike.mem_coe, hR, Subgroup.mem_inf]
    rw [h1 h, h2 h]
  have hO : ⁅J, R⁆ ≤ LargeEvenPPrimeCoreOf p Y :=
    comm_le_pPrimeCoreOf_of_cover hXpc hJX hcov inf_le_right hJR hR2
  have hRJ : ⁅R, J⁆ ≤ R := by
    refine Subgroup.commutator_le.mpr fun r hr j hj => ?_
    have h1 : j * r * j⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hJR hj) r).mp hr
    have h2 : ⁅r, j⁆ = r * (j * r * j⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [h2]
    exact R.mul_mem hr (R.inv_mem h1)
  have hRO : ⁅R, J⁆ ≤ LargeEvenPPrimeCoreOf p Y := by
    rw [Subgroup.commutator_comm]; exact hO
  set S : Subgroup G := ⁅⁅R, J⁆, J⁆ with hS
  have hSR : S ≤ R := (Subgroup.commutator_mono hRJ le_rfl).trans hRJ
  have hSO : S ≤ ⁅J, LargeEvenPPrimeCoreOf p Y⁆ := by
    rw [Subgroup.commutator_comm J]
    exact Subgroup.commutator_mono hRO le_rfl
  have hodd : Odd (Nat.card (⁅J, LargeEvenPPrimeCoreOf p Y⁆ : Subgroup G)) :=
    (hI.2.2.2.2.2.2.2.2.2.2 D J hDJ).2 d hdD hd1
  have hSodd : Odd (Nat.card S) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hSO)
  have hS2 : IsPGroup 2 ↥S := hR2.to_le hSR
  have hSbot : S = ⊥ := by
    obtain ⟨n, hn⟩ := hS2.exists_card_eq
    rw [hn] at hSodd
    have hn0 : n = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.mpr hSodd) (by
        rw [Nat.even_pow]; exact ⟨even_two, hne⟩)
    rw [hn0, pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq S hn
  exact commutator_eq_bot_of_perfect (commutator_self_eq_of_isQuasisimple hDJ.1.2.2.2.2.2.1.2.2)
    hSbot

theorem false_of_le_centralizer_ggG0 (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hpJ : p ∣ Nat.card J) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hT : T ≤ Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (J : Set G))
    (hT0 : T ≤ Subgroup.centralizer (ggG0 p B x L D J : Set G)) : False := by
  have hI : GGThmIHyp p B x L := hcfg.1.1.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.1.1.2.2
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hPU : GGPumpupInput := ggPumpupInput_of_lBalance hL
  have hG0T : ggG0 p B x L D J ≤ Subgroup.centralizer (T : Set G) :=
    Subgroup.le_centralizer_iff.mp hT0
  obtain ⟨d, hdD, hd1, hne⟩ := exists_commutator_ne_bot hcfg hT2 hT1 hT
  apply hne
  by_cases hdx : d ∈ Subgroup.zpowers x
  ·
    have hx1 : x ≠ 1 := hS.2.2.1
    have hxp : x ^ p = 1 := hS.1.1.2 x hS.2.1
    have hox : orderOf x = p := orderOf_eq_prime hxp hx1
    have hod : orderOf d = p := by
      have hdvd : orderOf d ∣ p := hox ▸ orderOf_dvd_of_mem_zpowers hdx
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hd1
      · exact h
    have hzeq : Subgroup.zpowers d = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdx)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hod, hox])
    have hCd : Subgroup.centralizer ({d} : Set G) = Subgroup.centralizer ({x} : Set G) := by
      rw [← Subgroup.centralizer_closure ({d} : Set G),
        ← Subgroup.centralizer_closure ({x} : Set G),
        ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, hzeq]
    have hLc : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({d} : Set G)) :=
      hCd ▸ hS.2.2.2.1
    exact commutator_eq_bot_of_component hT2 hLc (J_le hL hcfg hpJ (Or.inl rfl))
      ((le_sup_left : L ≤ ggG0 p B x L D J).trans hG0T)
  · have hD := eq_closure_pair_of_mem hI hDJ hdD hdx
    rcases ggNbr_or_eq_sup_of_stdSub hPU hI hDJ hpJ hD with hN | hcov
    ·
      have hKc := (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hN)).1
      exact commutator_eq_bot_of_component hT2 hKc (le_of_ggNbr hL hI hDJ hpJ hN)
        ((le_ggG0_of_ggNbr hN).trans hG0T)
    ·
      exact commutator_eq_bot_of_cover ha₀ hL hcfg hpJ hD hcov hT2 hT

theorem odd_card_centralizer_D_inf_J
    (ha₀ : GGLNoncyclicInput) (hKGp : GGSecFiveKGPosInput)
    (hKC : GGSecFiveKGCentInput) (hSplit : GGSecFiveSplitNbrInput)
    (hJoin : GGSecFiveJoinRegionInput) (hL : GGLBalanceInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hpJ : p ∣ Nat.card J) :
    Odd (Nat.card ↥(Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (J : Set G))) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (J : Set G)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  set T : Subgroup G := Subgroup.zpowers (t : G) with hTdef
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
  have hT1 : T ≠ ⊥ := by
    intro h
    have h1 : (t : G) = 1 := Subgroup.zpowers_eq_bot.mp h
    rw [h1, orderOf_one] at ht'
    exact absurd ht' (by norm_num)
  have hT : T ≤ Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (J : Set G) :=
    (Subgroup.zpowers_le).mpr t.2
  exact false_of_le_centralizer_ggG0 ha₀ hL hcfg hpJ hT2 hT1 hT
    (le_centralizer_ggG0 ha₀ hKGp hKC hSplit hJoin hL hcfg hsplit hpres hle3 hpJ hT2 hT)

end TheoremO

section Assembly

theorem ggSecFiveL1OddInput_of_pieces
    (ha₀ : GGLNoncyclicInput) (hKGp : GGSecFiveKGPosInput) (hKC : GGSecFiveKGCentInput)
    (hJR : GGSecFiveJReflInput) (hSplit : GGSecFiveSplitNbrInput)
    (hJoin : GGSecFiveJoinRegionInput) (hL : GGLBalanceInput) : GGSecFiveL1OddInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX hXs r hrA hrC
  obtain ⟨r₁, hr₁, hr₁refl⟩ := hJR G p B Bs x L D J 𝒦 hcfg hsplit
  have hpJ : p ∣ Nat.card J := p_dvd_card_J ha₀ hcfg hr₁ hr₁refl
  obtain ⟨g, hgX, -, hDle⟩ :=
    exists_conj_le_ggHyperplane ha₀ hKGp hJR hL hcfg hsplit hpres hle3 hX hXs hrA hrC
  rw [← card_centralizer_inf_map_conj (H := ggHyperplane Bs r) hgX]
  have hodd := odd_card_centralizer_D_inf_J ha₀ hKGp hKC hSplit hJoin hL hcfg hsplit hpres hle3 hpJ
  have hle : Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer (((ggHyperplane Bs r).map (MulAut.conj g).toMonoidHom : Subgroup G) :
        Set G) ≤ Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (J : Set G) :=
    le_inf (inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hDle)))
      (inf_le_left.trans (Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr (J_le hL hcfg hpJ hX))))
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)

end Assembly

end CFSG.StandardType.SecFiveL1Odd
