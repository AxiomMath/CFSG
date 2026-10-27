module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6Pat
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaForkCox
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveDkForkLeaves
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRoots
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsPairs
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitWeylEquiv
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupRoots
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpRoute
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem ggDk_commute_of_sameSupp {k : ℕ} (hk : 2 ≤ k) {t t' u : ggWeylD k}
    (hS : GGDSameSupp k t t') (hu : ∃ δ, GGDReflRoot k u δ) (hcomm : u * t' = t' * u) :
    u * t = t * u := by
  by_cases hne : u = t'
  · rw [hne]
    exact (hS.commute hk).symm
  obtain ⟨a, b, s, hab, hs, ht, ht'⟩ := hS
  obtain ⟨δ, hδ⟩ := hu
  have hda : δ a = s * δ b := by
    have h := ggDDot_eq_zero_of_commute hk hδ ht' hcomm hne
    rw [sub_eq_add_neg, ← Pi.single_neg, ggDDot_comm, ggDDot_single_add_single, one_mul,
      neg_mul] at h
    linarith
  have hdot : ggDDot (Pi.single a 1 + Pi.single b s) δ = 2 * δ a := by
    rw [ggDDot_single_add_single, one_mul]
    linarith
  by_cases hz : δ a = 0
  · refine hδ.commute_of_dot_eq_zero hk ht ?_
    rw [ggDDot_comm, hdot, hz]
    norm_num
  have hdb : δ b ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hda
    exact hz hda
  have heq : δ = Pi.single a (δ a) + Pi.single b (δ b) :=
    ggDRootSet_eq_single_add_single (hδ.mem (by omega)) hab hz hdb
  have hb' : δ b = s * δ a := by
    have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
    calc δ b = s * (s * δ b) := by rw [← mul_assoc, hss, one_mul]
      _ = s * δ a := by rw [hda]
  rcases ggDRootSet_sign (hδ.mem (by omega)) hz with h1 | h1
  · have hb1 : δ b = s := by rw [hb', h1]; ring
    have hpm : δ = Pi.single a 1 + Pi.single b s := by rw [heq, h1, hb1]
    rw [hδ.unique hk ht (Or.inl hpm.symm)]
  · have hb1 : δ b = -s := by rw [hb', h1]; ring
    have hpm : δ = -(Pi.single a 1 + Pi.single b s) := by
      rw [heq, h1, hb1, Pi.single_neg, Pi.single_neg]
      abel
    rw [hδ.unique hk ht (Or.inr (by rw [hpm, neg_neg]))]

theorem ggCoxE6Pat_absurd_typeD {ι : Type} {M : CoxeterMatrix ι} (hD : GGIsWeylMatrixD M)
    {t₀ t₁ t₂ t₃ u₁ u₂ : M.Group}
    (h₀ : ∃ (w : M.Group) (i : ι), t₀ = w * M.simple i * w⁻¹)
    (h₁ : ∃ (w : M.Group) (i : ι), t₁ = w * M.simple i * w⁻¹)
    (h₂ : ∃ (w : M.Group) (i : ι), t₂ = w * M.simple i * w⁻¹)
    (h₃ : ∃ (w : M.Group) (i : ι), t₃ = w * M.simple i * w⁻¹)
    (hu₁ : ∃ (w : M.Group) (i : ι), u₁ = w * M.simple i * w⁻¹)
    (hu₂ : ∃ (w : M.Group) (i : ι), u₂ = w * M.simple i * w⁻¹)
    (h12 : t₁ * t₂ = t₂ * t₁) (h13 : t₁ * t₃ = t₃ * t₁) (h23 : t₂ * t₃ = t₃ * t₂)
    (hn12 : t₁ ≠ t₂) (hn13 : t₁ ≠ t₃) (hn23 : t₂ ≠ t₃)
    (hn01 : t₀ * t₁ ≠ t₁ * t₀) (hn02 : t₀ * t₂ ≠ t₂ * t₀) (hn03 : t₀ * t₃ ≠ t₃ * t₀)
    (hu11 : u₁ * t₁ ≠ t₁ * u₁) (hu12 : u₁ * t₂ = t₂ * u₁) (hu13 : u₁ * t₃ = t₃ * u₁)
    (hu22 : u₂ * t₂ ≠ t₂ * u₂) (hu23 : u₂ * t₃ = t₃ * u₂) : False := by
  obtain ⟨k, σ, hk, hM⟩ := hD
  obtain ⟨φ, hφ⟩ := ggDk_weylEquiv hM
  have hroot : ∀ t : M.Group, (∃ (w : M.Group) (i : ι), t = w * M.simple i * w⁻¹) →
      ∃ γ, GGDReflRoot k (φ t) γ := by
    rintro t ⟨w, i, rfl⟩
    exact exists_ggDReflRoot_of_conj φ hφ w i
  have hmul : ∀ {a b : M.Group}, a * b = b * a → φ a * φ b = φ b * φ a := by
    intro a b h
    rw [← map_mul, ← map_mul, h]
  have hne : ∀ {a b : M.Group}, a ≠ b → φ a ≠ φ b := fun h hh => h (φ.injective hh)
  have hncomm : ∀ {a b : M.Group}, a * b ≠ b * a → φ a * φ b ≠ φ b * φ a := by
    intro a b h hh
    apply h
    apply φ.injective
    rw [map_mul, map_mul]
    exact hh
  have hk2 : 2 ≤ k := by omega
  obtain ⟨hS, -⟩ := ggDk_fork_leaves hk (hroot t₀ h₀) (hroot t₁ h₁) (hroot t₂ h₂) (hroot t₃ h₃)
    (hmul h12) (hmul h13) (hmul h23) (hne hn12) (hne hn13) (hne hn23)
    (hncomm hn01) (hncomm hn02) (hncomm hn03)
  rcases hS with h | h | h
  · exact hncomm hu11 (ggDk_commute_of_sameSupp hk2 h (hroot u₁ hu₁) (hmul hu12))
  · exact hncomm hu11 (ggDk_commute_of_sameSupp hk2 h (hroot u₁ hu₁) (hmul hu13))
  · exact hncomm hu22 (ggDk_commute_of_sameSupp hk2 h (hroot u₂ hu₂) (hmul hu23))

theorem ggX_e6Pat_coxeter {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G}
    (hle : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {c₀ c₁ c₂ c₃ d₁ d₂ : MulAut ↥Bs} (hc₀ : c₀ ∈ ggAutomizer X Bs) (hc₁ : c₁ ∈ ggAutomizer X Bs)
    (hc₂ : c₂ ∈ ggAutomizer X Bs) (hc₃ : c₃ ∈ ggAutomizer X Bs) (hd₁ : d₁ ∈ ggAutomizer X Bs)
    (hd₂ : d₂ ∈ ggAutomizer X Bs) (hr₀ : GGIsReflection p c₀)
    (hr₁ : GGIsReflection p c₁) (hr₂ : GGIsReflection p c₂) (hr₃ : GGIsReflection p c₃)
    (hs₁ : GGIsReflection p d₁) (hs₂ : GGIsReflection p d₂)
    (h01 : 3 ∣ orderOf (c₀ * c₁)) (h02 : 3 ∣ orderOf (c₀ * c₂)) (h03 : 3 ∣ orderOf (c₀ * c₃))
    (h12 : 2 ∣ orderOf (c₁ * c₂)) (h13 : 2 ∣ orderOf (c₁ * c₃)) (h23 : 2 ∣ orderOf (c₂ * c₃))
    (hb11 : 3 ∣ orderOf (d₁ * c₁)) (hb12 : 2 ∣ orderOf (d₁ * c₂)) (hb13 : 2 ∣ orderOf (d₁ * c₃))
    (hb22 : 3 ∣ orderOf (d₂ * c₂)) (hb23 : 2 ∣ orderOf (d₂ * c₃)) :
    ∃ t₀ t₁ t₂ t₃ u₁ u₂ : M.Group,
      (∃ (w : M.Group) (i : ι), t₀ = w * M.simple i * w⁻¹) ∧
      (∃ (w : M.Group) (i : ι), t₁ = w * M.simple i * w⁻¹) ∧
      (∃ (w : M.Group) (i : ι), t₂ = w * M.simple i * w⁻¹) ∧
      (∃ (w : M.Group) (i : ι), t₃ = w * M.simple i * w⁻¹) ∧
      (∃ (w : M.Group) (i : ι), u₁ = w * M.simple i * w⁻¹) ∧
      (∃ (w : M.Group) (i : ι), u₂ = w * M.simple i * w⁻¹) ∧
      t₁ * t₂ = t₂ * t₁ ∧ t₁ * t₃ = t₃ * t₁ ∧ t₂ * t₃ = t₃ * t₂ ∧
      t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃ ∧
      t₀ * t₁ ≠ t₁ * t₀ ∧ t₀ * t₂ ≠ t₂ * t₀ ∧ t₀ * t₃ ≠ t₃ * t₀ ∧
      u₁ * t₁ ≠ t₁ * u₁ ∧ u₁ * t₂ = t₂ * u₁ ∧ u₁ * t₃ = t₃ * u₁ ∧
      u₂ * t₂ ≠ t₂ * u₂ ∧ u₂ * t₃ = t₃ * u₂ := by
  have hC : ∀ {c : MulAut ↥Bs}, c ∈ ggAutomizer X Bs → GGIsReflection p c →
      c ∈ ggCoxRefl M e := fun hc hr =>
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hle hc) hr
  have hsq : ∀ {c : MulAut ↥Bs}, GGIsReflection p c → c * c = 1 := fun hr => by
    simpa [sq] using hr.1
  have hord : ∀ {c c' : MulAut ↥Bs}, c ∈ ggCoxRefl M e → c' ∈ ggCoxRefl M e →
      (c * c') ^ 2 = 1 ∨ (c * c') ^ 3 = 1 := fun hc hc' =>
    ggCoxRefl_mul_orderOf_le_three hpres.1 hle3 hc hc'
  have hC₀ := hC hc₀ hr₀
  have hC₁ := hC hc₁ hr₁
  have hC₂ := hC hc₂ hr₂
  have hC₃ := hC hc₃ hr₃
  have hD₁ := hC hd₁ hs₁
  have hD₂ := hC hd₂ hs₂
  obtain ⟨w₀, i₀, hw₀⟩ := id hC₀
  obtain ⟨w₁, i₁, hw₁⟩ := id hC₁
  obtain ⟨w₂, i₂, hw₂⟩ := id hC₂
  obtain ⟨w₃, i₃, hw₃⟩ := id hC₃
  obtain ⟨v₁, j₁, hv₁⟩ := id hD₁
  obtain ⟨v₂, j₂, hv₂⟩ := id hD₂
  obtain ⟨h12c, hn12⟩ := commute_ne_of_two_dvd_orderOf_coxRefl hw₁ hw₂ (hsq hr₁) (hsq hr₂)
    (hord hC₁ hC₂) h12
  obtain ⟨h13c, hn13⟩ := commute_ne_of_two_dvd_orderOf_coxRefl hw₁ hw₃ (hsq hr₁) (hsq hr₃)
    (hord hC₁ hC₃) h13
  obtain ⟨h23c, hn23⟩ := commute_ne_of_two_dvd_orderOf_coxRefl hw₂ hw₃ (hsq hr₂) (hsq hr₃)
    (hord hC₂ hC₃) h23
  obtain ⟨hb12c, -⟩ := commute_ne_of_two_dvd_orderOf_coxRefl hv₁ hw₂ (hsq hs₁) (hsq hr₂)
    (hord hD₁ hC₂) hb12
  obtain ⟨hb13c, -⟩ := commute_ne_of_two_dvd_orderOf_coxRefl hv₁ hw₃ (hsq hs₁) (hsq hr₃)
    (hord hD₁ hC₃) hb13
  obtain ⟨hb23c, -⟩ := commute_ne_of_two_dvd_orderOf_coxRefl hv₂ hw₃ (hsq hs₂) (hsq hr₃)
    (hord hD₂ hC₃) hb23
  exact ⟨w₀ * M.simple i₀ * w₀⁻¹, w₁ * M.simple i₁ * w₁⁻¹, w₂ * M.simple i₂ * w₂⁻¹,
    w₃ * M.simple i₃ * w₃⁻¹, v₁ * M.simple j₁ * v₁⁻¹, v₂ * M.simple j₂ * v₂⁻¹,
    ⟨w₀, i₀, rfl⟩, ⟨w₁, i₁, rfl⟩, ⟨w₂, i₂, rfl⟩, ⟨w₃, i₃, rfl⟩, ⟨v₁, j₁, rfl⟩, ⟨v₂, j₂, rfl⟩,
    h12c, h13c, h23c, hn12, hn13, hn23,
    not_commute_of_three_dvd_orderOf_coxRefl hw₀ hw₁ (hsq hr₀) (hsq hr₁) h01,
    not_commute_of_three_dvd_orderOf_coxRefl hw₀ hw₂ (hsq hr₀) (hsq hr₂) h02,
    not_commute_of_three_dvd_orderOf_coxRefl hw₀ hw₃ (hsq hr₀) (hsq hr₃) h03,
    not_commute_of_three_dvd_orderOf_coxRefl hv₁ hw₁ (hsq hs₁) (hsq hr₁) hb11,
    hb12c, hb13c,
    not_commute_of_three_dvd_orderOf_coxRefl hv₂ hw₂ (hsq hs₂) (hsq hr₂) hb22,
    hb23c⟩

theorem ggX_noReflE6Pat_typeD {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hD : GGIsWeylMatrixD M)
    {X : Subgroup G} (hle : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    GGNoReflE6Pat p Bs X := by
  rintro ⟨c₀, hc₀, c₁, hc₁, c₂, hc₂, c₃, hc₃, d₁, hd₁, d₂, hd₂, hr₀, hr₁, hr₂, hr₃, hs₁, hs₂,
    h01, h02, h03, h12, h13, h23, hb11, hb12, hb13, hb22, hb23⟩
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixAD.le_three (Or.inr hD)
  obtain ⟨t₀, t₁, t₂, t₃, u₁, u₂, h₀, h₁, h₂, h₃, hu₁, hu₂, hc12, hc13, hc23, hn12, hn13, hn23,
    hn01, hn02, hn03, hu11, hu12, hu13, hu22, hu23⟩ :=
    ggX_e6Pat_coxeter hcfg hpres hle3 hle hc₀ hc₁ hc₂ hc₃ hd₁ hd₂ hr₀ hr₁ hr₂ hr₃ hs₁ hs₂
      h01 h02 h03 h12 h13 h23 hb11 hb12 hb13 hb22 hb23
  exact ggCoxE6Pat_absurd_typeD hD h₀ h₁ h₂ h₃ hu₁ hu₂ hc12 hc13 hc23 hn12 hn13 hn23
    hn01 hn02 hn03 hu11 hu12 hu13 hu22 hu23

end CFSG.StandardType

end
