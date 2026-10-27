module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTorus.Restrict
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTorus.BorelCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.OrderOfX

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.TwoConj

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private instance finiteMulAut_Tor4 {W : Type} [Group W] [Finite W] : Finite (MulAut W) :=
  Finite.of_injective (fun (g : MulAut W) => (fun w : W => g w))
    (fun _ _ hgh => MulEquiv.ext (congrFun hgh))

private lemma isL2_of_hnat_Tor4 {W : Type} [CommGroup W] {X : Subgroup (MulAut W)} {n : ℕ}
    (hn : 2 < n)
    (hnat : (IsL2 ↥X n ∧ BinaryNaturalSL X (commV X) ⊥ 2 n) ∨
      (Even n ∧ IsOmegaMinus ↥X 4 (n / 2) ∧ NatOmegaMinus X (commV X) ⊥ 4 (n / 2))) :
    IsL2 ↥X n := by
  rcases hnat with ⟨hL2, -⟩ | ⟨hEven, hOM, -⟩
  · exact hL2
  · have hk : 1 ≤ n / 2 := by omega
    have h2 : 2 * (n / 2) = n := by
      rw [mul_comm]
      exact Nat.div_mul_cancel hEven.two_dvd
    rw [← h2]
    exact S18.isL2_of_isOmegaMinus_four hk hOM

private lemma commutator_top_subtype_Tor4 {G : Type} [Group G] (X : Subgroup G)
    (hperf : ⁅X, X⁆ = X) : (_root_.commutator ↥X) = ⊤ := by
  have h1 : (_root_.commutator ↥X).map X.subtype = (⊤ : Subgroup ↥X).map X.subtype := by
    rw [Subgroup.map_subtype_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact hperf
  have h2 := congrArg (Subgroup.comap X.subtype) h1
  rwa [Subgroup.comap_map_eq_self_of_injective X.subtype_injective,
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective] at h2

private lemma isPerfect_map_of_isPerfect_Tor4 {G H : Type} [Group G] [Group H]
    (φ : G →* H) (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = (⊤ : Subgroup G)) :
    ⁅(⊤ : Subgroup G).map φ, (⊤ : Subgroup G).map φ⁆ = (⊤ : Subgroup G).map φ := by
  rw [← Subgroup.map_commutator (f := φ)]
  rw [hperf]

private lemma mem_map_iff_Tor4 {G H : Type} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) (S : Subgroup G) {y : G} :
    φ y ∈ S.map φ ↔ y ∈ S := by
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨z, hz, hzy⟩ => by rwa [hφ hzy] at hz, fun hy => ⟨y, hy, rfl⟩⟩

private lemma range_subtype_comp_Tor4 {A M : Type} [Group A] [Group M] {B : Subgroup M}
    (f : A ≃* ↥B) : (B.subtype.comp f.toMonoidHom).range = B := by
  ext h
  constructor
  · rintro ⟨x, rfl⟩
    exact (f x).2
  · intro hh
    exact ⟨f.symm ⟨h, hh⟩, by simp⟩

private lemma map_subgroupOf_ne_bot_Tor4 {G : Type} [Group G] {X S : Subgroup G}
    (hSX : S ≤ X) (hSne : S ≠ ⊥) : S.subgroupOf X ≠ ⊥ := by
  intro h
  apply hSne
  have hmap := congrArg (Subgroup.map X.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hSX, Subgroup.map_bot] at hmap

private lemma map_ne_bot_Tor4 {G H : Type} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) {S : Subgroup G} (hSne : S ≠ ⊥) : S.map φ ≠ ⊥ := by
  intro hbot
  apply hSne
  rw [Subgroup.eq_bot_iff_forall]
  intro s hs
  have hmem : φ s ∈ S.map φ := ⟨s, hs, rfl⟩
  rw [hbot] at hmem
  exact hφ (by rw [Subgroup.mem_bot.mp hmem, map_one])

private lemma isSylowIn_map_Tor4 {W : Type} [CommGroup W] [Finite W]
    {X S : Subgroup (MulAut W)} {H : Subgroup (MulAut ↥(commV X))}
    (hS : IsSylowIn 2 S X) (f : ↥X ≃* ↥H) (φ : ↥X →* MulAut ↥(commV X))
    (hφ : Function.Injective φ) (hφrange : φ.range = H) :
    IsSylowIn 2 ((S.subgroupOf X).map φ) H := by
  have hle : (S.subgroupOf X).map φ ≤ H := by
    rintro _ ⟨y, -, rfl⟩
    rw [← hφrange]
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  have hcardS : Nat.card ((S.subgroupOf X).map φ) = Nat.card S := by
    rw [Subgroup.card_map_of_injective hφ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.le).toEquiv
  have hcardH : Nat.card H = Nat.card X := (Nat.card_congr f.toEquiv).symm
  refine isSylowIn_of_card_eq hle ?_
  rw [hcardS, hcardH]
  exact hS.card_eq

private lemma sylow_ne_bot_Tor4 {W : Type} [CommGroup W] [Finite W]
    {X S : Subgroup (MulAut W)} {n : ℕ} (hS : IsSylowIn 2 S X)
    (hcard : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1)) (hn : 2 < n) : S ≠ ⊥ := by
  intro hbot
  apply hS.not_dvd_relIndex
  rw [hbot, Subgroup.relIndex_bot_left, hcard]
  exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _

private lemma fixV_map_eq_bot_Tor4 {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    {H : Subgroup (MulAut ↥(commV X))} (f : ↥X ≃* ↥H)
    (hf : ∀ (x : ↥X) (u : ↥(commV X)),
      (((f x : ↥H) : MulAut ↥(commV X)) u : W) = (x : MulAut W) (u : W))
    (hfix : commV X ⊓ fixV X = ⊥) : fixV H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  apply Subtype.ext
  have hufix : (u : W) ∈ fixV X := by
    rw [mem_fixV]
    intro x hx
    have hxH : ((f ⟨x, hx⟩ : ↥H) : MulAut ↥(commV X)) ∈ H := (f ⟨x, hx⟩).2
    have h1 : ((f ⟨x, hx⟩ : ↥H) : MulAut ↥(commV X)) u = u :=
      (mem_fixV.mp hu) (f ⟨x, hx⟩) hxH
    have h2 := hf ⟨x, hx⟩ u
    have h3 : (((f ⟨x, hx⟩ : ↥H) : MulAut ↥(commV X)) u : W) = (u : W) :=
      congrArg Subtype.val h1
    rw [h2] at h3
    exact h3
  have hmem : (u : W) ∈ commV X ⊓ fixV X := ⟨u.2, hufix⟩
  rw [hfix] at hmem
  exact Subgroup.mem_bot.mp hmem

private lemma mem_fixV_map_Tor4 {W : Type} [CommGroup W] {X S : Subgroup (MulAut W)}
    {H : Subgroup (MulAut ↥(commV X))} (f : ↥X ≃* ↥H)
    (hf : ∀ (x : ↥X) (u : ↥(commV X)),
      (((f x : ↥H) : MulAut ↥(commV X)) u : W) = (x : MulAut W) (u : W))
    {v : W} (hvX : v ∈ commV X) (hvS : v ∈ fixV S) :
    (⟨v, hvX⟩ : ↥(commV X)) ∈
      fixV ((S.subgroupOf X).map (H.subtype.comp f.toMonoidHom)) := by
  rw [mem_fixV]
  intro b hb
  rw [Subgroup.mem_map] at hb
  obtain ⟨y, hy, rfl⟩ := hb
  apply Subtype.ext
  have h1 := hf y ⟨v, hvX⟩
  have h2 : (((H.subtype.comp f.toMonoidHom) y) ⟨v, hvX⟩ : W) = (y : MulAut W) v := by
    simpa using h1
  rw [h2]
  exact (mem_fixV.mp hvS) (y : MulAut W) (Subgroup.mem_subgroupOf.mp hy)

private lemma mem_normalizer_subgroupOf_map_Tor4 {W U : Type} [CommGroup W] [CommGroup U]
    {X S : Subgroup (MulAut W)} (hSX : S ≤ X) (φ : ↥X →* MulAut U)
    (hφ : Function.Injective φ) (x : ↥X)
    (hg : φ x ∈ normalizer ((S.subgroupOf X).map φ)) :
    (x : MulAut W) ∈ normalizer (S : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff] at ⊢
  intro s
  constructor
  · intro hs
    have hsX : s ∈ X := hSX hs
    have h1 : φ x * φ ⟨s, hsX⟩ * (φ x)⁻¹ ∈ (S.subgroupOf X).map φ :=
      (Subgroup.mem_normalizer_iff.mp hg (φ ⟨s, hsX⟩)).mp
        (Subgroup.mem_map.mpr ⟨⟨s, hsX⟩, hs, rfl⟩)
    have h2 : φ (x * ⟨s, hsX⟩ * x⁻¹) ∈ (S.subgroupOf X).map φ := by
      simpa only [map_mul, map_inv] using h1
    exact (mem_map_iff_Tor4 φ hφ (S.subgroupOf X)).mp h2
  · intro hs
    have hsX : s ∈ X := by
      have h1 : (x : MulAut W) * s * (x : MulAut W)⁻¹ ∈ X := hSX hs
      have h2 : (x : MulAut W)⁻¹ * ((x : MulAut W) * s * (x : MulAut W)⁻¹) *
          (x : MulAut W) = s := by group
      rw [← h2]
      exact X.mul_mem (X.mul_mem (X.inv_mem x.2) h1) x.2
    have h1 : φ (x * ⟨s, hsX⟩ * x⁻¹) ∈ (S.subgroupOf X).map φ :=
      (mem_map_iff_Tor4 φ hφ (S.subgroupOf X)).mpr hs
    have h2 : φ x * φ ⟨s, hsX⟩ * (φ x)⁻¹ ∈ (S.subgroupOf X).map φ := by
      simpa only [map_mul, map_inv] using h1
    have hginv : (φ x)⁻¹ ∈ normalizer ((S.subgroupOf X).map φ) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hh := Subgroup.mem_normalizer_iff.mp hg ((φ x)⁻¹ * h * φ x)
      rw [show φ x * ((φ x)⁻¹ * h * φ x) * (φ x)⁻¹ = h from by group] at hh
      simpa using hh.symm
    have h3 : (φ x)⁻¹ * (φ x * φ ⟨s, hsX⟩ * (φ x)⁻¹) * ((φ x)⁻¹)⁻¹ ∈
        (S.subgroupOf X).map φ :=
      ((Subgroup.mem_normalizer_iff.mp hginv) _).mp h2
    have h4 : (φ x)⁻¹ * (φ x * φ ⟨s, hsX⟩ * (φ x)⁻¹) * ((φ x)⁻¹)⁻¹ = φ ⟨s, hsX⟩ := by
      group
    rw [h4] at h3
    exact Subgroup.mem_subgroupOf.mp ((mem_map_iff_Tor4 φ hφ (S.subgroupOf X)).mp h3)

private lemma exists_apply_ne_of_map_exists_Tor4 {W : Type} [CommGroup W]
    {X S : Subgroup (MulAut W)} {H : Subgroup (MulAut ↥(commV X))} (f : ↥X ≃* ↥H)
    (hf : ∀ (x : ↥X) (u : ↥(commV X)),
      (((f x : ↥H) : MulAut ↥(commV X)) u : W) = (x : MulAut W) (u : W))
    (hSX : S ≤ X) {b' : MulAut ↥(commV X)} (hb'H : b' ∈ H)
    (hg : b' ∈ normalizer ((S.subgroupOf X).map (H.subtype.comp f.toMonoidHom)))
    {v : W} (hvX : v ∈ commV X) (hmove : b' ⟨v, hvX⟩ ≠ ⟨v, hvX⟩) :
    ∃ b ∈ X ⊓ normalizer (S : Set (MulAut W)), b v ≠ v := by
  let x : ↥X := f.symm ⟨b', hb'H⟩
  have hφx : (H.subtype.comp f.toMonoidHom) x = b' := by simp [x]
  have hφinj : Function.Injective (H.subtype.comp f.toMonoidHom) :=
    fun a b h => f.injective (Subtype.ext h)
  have hxnorm : (x : MulAut W) ∈ normalizer (S : Set (MulAut W)) :=
    mem_normalizer_subgroupOf_map_Tor4 hSX (H.subtype.comp f.toMonoidHom) hφinj x
      (by rw [hφx]; exact hg)
  refine ⟨(x : MulAut W), ⟨x.2, hxnorm⟩, ?_⟩
  intro hxv
  have hb'v' : b' ⟨v, hvX⟩ = ⟨v, hvX⟩ := by
    apply Subtype.ext
    rw [← hφx]
    have h2 := hf x ⟨v, hvX⟩
    rw [hxv] at h2
    simpa using h2
  exact hmove hb'v'

theorem exists_mem_inf_normalizer_apply_ne_of_commV (hBI : KNatBorelIrr) (hTa : KTab23a)
    {W : Type} [CommGroup W] [Finite W] {X S : Subgroup (MulAut W)} (hperf : ⁅X, X⁆ = X)
    (hS : IsSylowIn 2 S X) (hfix : commV X ⊓ fixV X = ⊥) {n : ℕ} (hn : 2 < n)
    (hnat : (IsL2 ↥X n ∧ BinaryNaturalSL X (commV X) ⊥ 2 n) ∨
      (Even n ∧ IsOmegaMinus ↥X 4 (n / 2) ∧ NatOmegaMinus X (commV X) ⊥ 4 (n / 2)))
    {v : W} (hvX : v ∈ commV X) (hvS : v ∈ fixV S) (hv1 : v ≠ 1) (hv2 : v ^ 2 = 1) :
    ∃ b ∈ X ⊓ normalizer (S : Set (MulAut W)), b v ≠ v := by
  have hL2 : IsL2 ↥X n := isL2_of_hnat_Tor4 hn hnat
  have hcard := UC22.KOrdNat.isL2_two_le_and_card hL2
  have hsimpX : IsSimpleGroup ↥X :=
    UC22.uc22p22r_lieModel_isSimple_classical (Or.inl rfl) hL2
  have hSne : S ≠ ⊥ := sylow_ne_bot_Tor4 hS hcard.2 hn
  obtain ⟨H, k, f, hk, hnatH, hf⟩ := exists_mulEquiv_isNaturalClassicalModule hn hnat
  let φ : ↥X →* MulAut ↥(commV X) := H.subtype.comp f.toMonoidHom
  have hφinj : Function.Injective φ := fun a b h => f.injective (Subtype.ext h)
  have hφrange : φ.range = H := range_subtype_comp_Tor4 f
  have hperf_top : (_root_.commutator ↥X) = ⊤ := commutator_top_subtype_Tor4 X hperf
  have hperfH : ⁅H, H⁆ = H := by
    have hH : H = (⊤ : Subgroup ↥X).map φ := by rw [Subgroup.map_top, hφrange]
    rw [hH]
    exact isPerfect_map_of_isPerfect_Tor4 φ hperf_top
  have hsimpH : IsSimpleGroup ↥H := f.symm.isSimpleGroup
  have hfixH : fixV H = ⊥ := fixV_map_eq_bot_Tor4 f hf hfix
  set S' : Subgroup (MulAut ↥(commV X)) := (S.subgroupOf X).map φ with hS'def
  have hS' : IsSylowIn 2 S' H := by
    rw [hS'def]
    exact isSylowIn_map_Tor4 hS f φ hφinj hφrange
  have hS'ne : S' ≠ ⊥ := by
    rw [hS'def]
    exact map_ne_bot_Tor4 φ hφinj (map_subgroupOf_ne_bot_Tor4 hS.le hSne)
  let v' : ↥(commV X) := ⟨v, hvX⟩
  have hv' : v' ∈ fixV S' := by
    rw [hS'def]
    exact mem_fixV_map_Tor4 f hf hvX hvS
  have hv'1 : v' ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  have hv'2 : v' ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hv2
  obtain ⟨b', hb', hmove⟩ :=
    exists_mem_normalizer_apply_ne hBI hTa hnatH hperfH hsimpH hS' hS'ne hfixH hk hv' hv'1 hv'2
  exact exists_apply_ne_of_map_exists_Tor4 f hf hS.le hb'.1 hb'.2 hvX hmove

end CFSG.LocalAnalysis.UniquenessCase.UC22.TwoConj
