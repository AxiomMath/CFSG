module

public import CFSG.LocalAnalysis.StandardType.FS81.ConstructYE7
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10Cover
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.SeitzReduction.E8PilotAutD
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR4Basic
import CFSG.GroupTheory.InnerCentralizerProjection
import CFSG.GroupTheory.ConjTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
import CFSG.LocalAnalysis.StandardType.GGResQTwoTits
import CFSG.LocalAnalysis.StandardType.FS81.SplitEAux
import CFSG.LocalAnalysis.StandardType.FS81.SplitE
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralCoreReduction
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ClassicalGroups.Alternating.TransvectionGenerationTwo

public section
namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Assembly CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
open CFSG.Open

private theorem isRow_E7_data {G : Type} [Group G] {K : Subgroup G} (hK : IsRow Row.E7 K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ∃ _θ : ↥K ⧸ Subgroup.center ↥K ≃* TableBExc.RecipeGroup .E7 F,
        commutator ↥K = ⊤ := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hK
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  obtain ⟨hn1, hdisj⟩ := hP
  have htag : lab.tag = .E7 := by
    rcases hdisj with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h
  have hrank : lab.rank = 0 := by
    rcases hdisj with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h
  obtain ⟨tag, rank, n⟩ := lab
  simp only at htag hrank hn1
  subst htag
  subst hrank
  subst hn1
  simp only at hraw
  obtain ⟨F', fieldF', finiteF', hcardF', hQ'⟩ := hraw
  obtain ⟨-, -, θ', -⟩ := hQ'
  exact ⟨F', fieldF', finiteF', by simpa using hcardF', θ', hperf⟩

private theorem relIndex_inf_centralizer_inf_normalizer_le_two {G : Type} [Group G]
    [Finite G] {M A : Subgroup G} (hA3 : Nat.card A = 3) :
    (M ⊓ Subgroup.centralizer (A : Set G)).relIndex
      (M ⊓ Subgroup.normalizer (A : Set G)) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := M ⊓ Subgroup.centralizer (A : Set G)
  let N : Subgroup G := M ⊓ Subgroup.normalizer (A : Set G)
  change C.relIndex N ≤ 2
  have hNM : N ≤ M := inf_le_left
  let ρ : ↥N →* MulAut ↥A := (Subgroup.normalizerMonoidHom A).comp
    (Subgroup.inclusion (inf_le_right : N ≤ Subgroup.normalizer (A : Set G)))
  have hker : ρ.ker = C.subgroupOf N := by
    rw [show ρ = (Subgroup.normalizerMonoidHom A).comp
        (Subgroup.inclusion (inf_le_right : N ≤ Subgroup.normalizer (A : Set G))) from rfl,
      ← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker,
      Subgroup.comap_inclusion_subgroupOf]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, C]
    simp [hNM x.2]
  have hrel : C.relIndex N = Nat.card ρ.range := by
    rw [← Subgroup.index_ker ρ, hker]
    rfl
  have hAut : Nat.card (MulAut ↥A) = 2 := by
    have : IsCyclic ↥A := isCyclic_of_prime_card hA3
    rw [IsCyclic.card_mulAut, hA3, Nat.totient_prime Nat.prime_three]
  have hdvd : Nat.card ρ.range ∣ Nat.card (MulAut ↥A) :=
    Subgroup.card_subgroup_dvd_card ρ.range
  rw [hAut] at hdvd
  rw [hrel]
  exact Nat.le_of_dvd (by norm_num) hdvd

private theorem le_normalizer_inf_of_normalizer_le {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal) :
    Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G) ≤
      Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G) := by
  have hC_le_normK : Subgroup.centralizer ({b₀} : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hKC]
    exact hKn
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp hm.1 x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp (hC_le_normK hm.2) x).mp hx.2⟩
  · intro hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp hm.1 x).mpr hx.1,
      (Subgroup.mem_normalizer_iff.mp (hC_le_normK hm.2) x).mpr hx.2⟩

private theorem centralizer_inf_eq_of_normalizer_le {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G}
    (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E) :
    (Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G)) ⊓
        Subgroup.centralizer (E : Set G) =
      (Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G)) ⊓
        Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) := by
  have hC_zpow : Subgroup.centralizer (Subgroup.zpowers b₀ : Set G) =
      Subgroup.centralizer ({b₀} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1, Subgroup.centralizer_le (inf_le_left : E ⊓ K ≤ E) hx.2⟩
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have hx_b : x ∈ Subgroup.centralizer (Subgroup.zpowers b₀ : Set G) := by
      rw [hC_zpow]
      exact hx.1.2
    have hxE1 : x ∈ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) := hx.2
    have hxsup : Subgroup.zpowers x ≤
        Subgroup.centralizer ((Subgroup.zpowers b₀ ⊔ (E ⊓ K) : Subgroup G) : Set G) :=
      CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
        (Subgroup.zpowers_le.mpr hx_b) (Subgroup.zpowers_le.mpr hxE1)
    rw [hsup] at hxsup
    exact Subgroup.mem_centralizer_iff.mp (hxsup (Subgroup.mem_zpowers x))

private theorem card_inf_normalizer_mul_relIndex {G : Type} [Group G] [Finite G]
    {b₀ : G} {E : Subgroup G} :
    Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G)) *
      (Subgroup.normalizer (E : Set G) ⊓
        Subgroup.centralizer ({b₀} : Set G)).relIndex (Subgroup.normalizer (E : Set G)) =
      Nat.card ↥(Subgroup.normalizer (E : Set G)) := by
  have hM_le_N : Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G) ≤
      Subgroup.normalizer (E : Set G) := inf_le_left
  have h := Subgroup.card_mul_index
    (H := (Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G)).subgroupOf
      (Subgroup.normalizer (E : Set G)))
  rwa [show Nat.card ↥((Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({b₀} : Set G)).subgroupOf (Subgroup.normalizer (E : Set G))) =
      Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G)) from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_N).toEquiv] at h

private theorem mem_zpowers_of_orderOf_eq_three_of_mem_inf_centralizer
    {G : Type} [Group G] [Finite G] {b₀ : G} {K : Subgroup G}
    (hb₀ : orderOf b₀ = 3)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hA2 : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    {x : G} (hxD : x ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G)) (hx3 : x ^ 3 = 1) :
    x ∈ Subgroup.zpowers b₀ := by
  let H : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers b₀
  have hb₀CK : b₀ ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hKC hk) b₀ (by simp)).symm
  have hH_le_CK : H ≤ Subgroup.centralizer (K : Set G) := by
    apply sup_le
    · exact Subgroup.zpowers_le.mpr hxD.2
    · exact Subgroup.zpowers_le.mpr hb₀CK
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers b₀, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hxb : Commute x b₀ :=
      (Subgroup.mem_centralizer_iff.mp hxD.1 b₀ (by simp)).symm
    exact ((hxb.zpow_left i).zpow_right j).eq
  have hH_ea : IsElemAbelian 3 H :=
    IsElemAbelian.sup_of_commute (isElemAbelian_zpowers hx3)
      (isElemAbelian_zpowers (by rw [← hb₀]; exact pow_orderOf_eq_one b₀)) hcomm
  have hH_p : IsPGroup 3 H := hH_ea.isPGroup
  have : IsCyclic ↥H := hA2 H hH_le_CK hH_p
  have hbH : orderOf (⟨b₀, Subgroup.mem_sup_right (Subgroup.mem_zpowers b₀)⟩ : ↥H) = 3 := by
    rw [← Subgroup.orderOf_coe, hb₀]
  have hxH3 : (⟨x, Subgroup.mem_sup_left (Subgroup.mem_zpowers x)⟩ : ↥H) ^ 3 = 1 :=
    Subtype.ext (by simpa using hx3)
  have hmem := CFSG.StandardType.FrameRoute.fs81Sp_order3_unique
    (H := ↥H)
    (d := ⟨x, Subgroup.mem_sup_left (Subgroup.mem_zpowers x)⟩)
    (b₀ := ⟨b₀, Subgroup.mem_sup_right (Subgroup.mem_zpowers b₀)⟩) hbH hxH3
  rw [Subgroup.mem_zpowers_iff] at hmem ⊢
  obtain ⟨i, hi⟩ := hmem
  exact ⟨i, by simpa using congrArg Subtype.val hi⟩

private theorem sylow_three_cyclic_of_le_centralizer {G : Type} [Group G] [Finite G]
    {K D : Subgroup G}
    (hA2 : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hD_le_CK : D ≤ Subgroup.centralizer (K : Set G)) (P : Sylow 3 ↥D) :
    IsCyclic ↥(P : Subgroup ↥D) := by
  let PD : Subgroup ↥D := (P : Subgroup ↥D)
  have hPD_p : IsPGroup 3 ↥(PD.map D.subtype) := P.isPGroup'.map D.subtype
  have hPD_le_CK : PD.map D.subtype ≤ Subgroup.centralizer (K : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hD_le_CK x.2
  have hcyc_img : IsCyclic ↥(PD.map D.subtype) := hA2 _ hPD_le_CK hPD_p
  let f : ↥PD →* ↥(PD.map D.subtype) :=
    { toFun := fun x => (⟨x.1, Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩ : ↥(PD.map D.subtype))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf_inj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : ↥(PD.map D.subtype) => (z : G)) hxy))
  have : IsCyclic ↥(PD.map D.subtype) := hcyc_img
  exact isCyclic_of_injective f hf_inj

private theorem exists_generator_order_of_nine_dvd {G : Type} [Group G] [Finite G]
    {D : Subgroup G} (P : Sylow 3 ↥D) (hcyc : IsCyclic ↥(P : Subgroup ↥D))
    (h9 : 9 ∣ Nat.card ↥D) :
    ∃ (k : ℕ) (dP : ↥(P : Subgroup ↥D)), 2 ≤ k ∧ orderOf dP = 3 ^ k := by
  let PD : Subgroup ↥D := (P : Subgroup ↥D)
  have : IsCyclic ↥PD := hcyc
  obtain ⟨dP, hdPgen⟩ := IsCyclic.exists_generator (α := ↥PD)
  have hdPord : orderOf dP = Nat.card ↥PD := by
    rw [← Nat.card_zpowers (dP),
      show Subgroup.zpowers dP = ⊤ from top_unique (fun x _ => hdPgen x), Subgroup.card_top]
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have h9PD : 3 ^ 2 ∣ Nat.card ↥PD := by
    have hDcard : Nat.card ↥D = Nat.card ↥PD * PD.index := PD.card_mul_index.symm
    have h3 : ¬ 3 ∣ PD.index := P.not_dvd_index
    have hcop : Nat.Coprime (3 ^ 2) PD.index :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).pow_left 2
    have hdvd : 3 ^ 2 ∣ Nat.card ↥PD * PD.index := by
      rw [← hDcard]
      exact h9
    exact hcop.dvd_of_dvd_mul_right hdvd
  have hk2 : 2 ≤ k := by
    have hle : 3 ^ 2 ≤ 3 ^ k := by
      rw [← hk]
      exact Nat.le_of_dvd (by rw [hk]; exact pow_pos (by norm_num) k) h9PD
    by_contra hklt
    have hk1 : k ≤ 1 := by omega
    interval_cases k <;> norm_num at hle
  exact ⟨k, dP, hk2, hdPord.trans hk⟩

private theorem exists_decomposition_of_conj_sylow_generator {G : Type} [Group G] [Finite G]
    {K E D : Subgroup G} (hE1max : IsMaxElemAb3 K (E ⊓ K))
    (hD_le_CE : D ≤ Subgroup.centralizer (E : Set G))
    (hCE_le : Subgroup.centralizer (E : Set G) ≤ (E ⊓ K : Subgroup G) ⊔ D)
    {dP : ↥D} :
    ∀ n ∈ Subgroup.normalizer (E : Set G),
      ∃ e ∈ (E ⊓ K : Subgroup G), ∃ d' ∈ D,
        n * (dP : G) * n⁻¹ = e * d' ∧ e ^ 3 = 1 ∧ Commute e d' := by
  have hcomm_E1_D : ∀ a ∈ (E ⊓ K : Subgroup G), ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (hD_le_CE hb) a ha.1
  intro n hnN
  have hdP_D : (dP : G) ∈ D := dP.2
  have hconj_CE : n * (dP : G) * n⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hne : n⁻¹ * e * n ∈ E := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnN) e).mp he
    have hdE : (n⁻¹ * e * n) * (dP : G) = (dP : G) * (n⁻¹ * e * n) :=
      Subgroup.mem_centralizer_iff.mp (hD_le_CE hdP_D) (n⁻¹ * e * n) hne
    calc e * (n * (dP : G) * n⁻¹) = n * ((n⁻¹ * e * n) * (dP : G)) * n⁻¹ := by group
      _ = n * ((dP : G) * (n⁻¹ * e * n)) * n⁻¹ := by rw [hdE]
      _ = (n * (dP : G) * n⁻¹) * e := by group
  obtain ⟨e, heE1, d', hd'D, hed'⟩ :=
    fs81Sp_mem_sup_of_commute hcomm_E1_D (hCE_le hconj_CE)
  exact ⟨e, heE1, d', hd'D, hed', hE1max.2.1.2 e heE1,
    Subgroup.mem_centralizer_iff.mp (hD_le_CE hd'D) e heE1.1⟩

private theorem exists_normal_complement_of_central_order_prime
    {D : Type*} [Group D] [Finite D] {p : ℕ} [Fact p.Prime] {z : D}
    (hz : orderOf z = p) (hzc : ∀ d : D, Commute z d)
    (hindex : ¬ p ∣ (Subgroup.zpowers z).index) :
    ∃ Q : Subgroup D, Q.Normal ∧ Subgroup.zpowers z ⊓ Q = ⊥ ∧
      Subgroup.zpowers z ⊔ Q = ⊤ ∧
      (∀ x : D, ∃ i : ℤ, ∃ q ∈ Q, x = z ^ i * q) ∧
      Nat.Coprime p (Nat.card Q) ∧
      ∀ Q' : Subgroup D, Nat.Coprime p (Nat.card Q') → Q' ≤ Q := by
  classical
  let N : Subgroup D := Subgroup.zpowers z
  have hNnormal : N.Normal := by
    refine Subgroup.Normal.mk ?_
    intro a ha b
    rw [Subgroup.mem_zpowers_iff] at ha ⊢
    obtain ⟨i, rfl⟩ := ha
    refine ⟨i, ?_⟩
    rw [((hzc b).symm.zpow_right i).eq]
    group
  have : N.Normal := hNnormal
  have hNcard : Nat.card N = p := by
    dsimp only [N]
    rw [Nat.card_zpowers, hz]
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hNcard]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hindex
  obtain ⟨Q, hcomp⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hQnormal : Q.Normal :=
    CFSG.RankThreeCoreUniqueness.Helpers.complement_normal_of_central_kernel N Q
      (by
        intro x hx
        rw [Subgroup.mem_center_iff]
        intro d
        rw [Subgroup.mem_zpowers_iff] at hx
        obtain ⟨i, rfl⟩ := hx
        exact ((hzc d).symm.zpow_right i).eq) hcomp.symm
  have : Q.Normal := hQnormal
  have hQindex : Q.index = Nat.card N := by
    have h1 := hcomp.card_mul_card
    have h2 := Q.card_mul_index
    rw [mul_comm] at h1
    exact Nat.mul_left_cancel (Nat.card_pos (α := Q)) (h2.trans h1.symm)
  have hQcard : Nat.card Q = N.index := by
    have h1 := hcomp.card_mul_card
    have h2 := N.card_mul_index
    exact Nat.mul_left_cancel (Nat.card_pos (α := N)) (h1.trans h2.symm)
  have hQcop : Nat.Coprime p (Nat.card Q) := by
    rw [hQcard]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hindex
  have hdecomp : ∀ x : D, ∃ i : ℤ, ∃ q ∈ Q, x = z ^ i * q := by
    intro x
    have hx : x ∈ N ⊔ Q := by rw [hcomp.sup_eq_top]; exact Subgroup.mem_top x
    obtain ⟨a, ha, q, hq, haq⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := N) (t := Q) (x := x)).mp hx
    rw [Subgroup.mem_zpowers_iff] at ha
    obtain ⟨i, rfl⟩ := ha
    exact ⟨i, q, hq, haq.symm⟩
  refine ⟨Q, hQnormal, hcomp.disjoint.eq_bot, hcomp.sup_eq_top, hdecomp, hQcop, ?_⟩
  intro Q' hQ'cop
  have hcardQ : Nat.card (D ⧸ Q) = p := by
    rw [← Subgroup.index_eq_card, hQindex, hNcard]
  have hmapdvd : Nat.card (Q'.map (QuotientGroup.mk' Q)) ∣ Nat.card Q' :=
    Subgroup.card_map_dvd Q' (QuotientGroup.mk' Q)
  have hmapdvd' : Nat.card (Q'.map (QuotientGroup.mk' Q)) ∣ p := by
    rw [← hcardQ]
    exact Subgroup.card_subgroup_dvd_card _
  have hcopimg : Nat.Coprime (Nat.card (Q'.map (QuotientGroup.mk' Q))) p :=
    (Nat.Coprime.of_dvd_right hmapdvd hQ'cop).symm
  have hone : Nat.card (Q'.map (QuotientGroup.mk' Q)) = 1 :=
    Nat.Coprime.eq_one_of_dvd hcopimg hmapdvd'
  have hbot : Q'.map (QuotientGroup.mk' Q) = ⊥ := Subgroup.card_eq_one.mp hone
  have hle : Q' ≤ (QuotientGroup.mk' Q).ker := (Subgroup.map_eq_bot_iff Q').mp hbot
  rwa [QuotientGroup.ker_mk'] at hle

private theorem automizer_card_eq_of_normalizer_le {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E) :
    Nat.card (ggAutomizer (Subgroup.normalizer (E : Set G) ⊓
        Subgroup.centralizer ({b₀} : Set G)) E) =
      Nat.card (ggAutomizer (Subgroup.normalizer (E : Set G) ⊓
        Subgroup.centralizer ({b₀} : Set G)) ((E ⊓ K : Subgroup G))) := by
  have hb₀E : b₀ ∈ E := by
    rw [← hsup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀)
  have hCGE_le_M : Subgroup.centralizer (E : Set G) ≤
      Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G) := by
    refine le_inf (Subgroup.centralizer_le_normalizer (E : Set G)) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using Subgroup.mem_centralizer_iff.mp hx b₀ hb₀E
  have hM_le_N : Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G) ≤
      Subgroup.normalizer (E : Set G) := inf_le_left
  have hM_le_NE1 := le_normalizer_inf_of_normalizer_le (E := E) hKC hKn
  have hMcard : Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({b₀} : Set G)) =
      Nat.card ↥((Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G)) ⊓
        Subgroup.centralizer (E : Set G)) *
        Nat.card (ggAutomizer (Subgroup.normalizer (E : Set G) ⊓
          Subgroup.centralizer ({b₀} : Set G)) E) := by
    have h := card_inf_normalizer_eq_card_centralizer_mul_card_automizer
      (H := Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G)) (A := E)
    rwa [inf_eq_left.mpr hM_le_N] at h
  have hMcard_E1 : Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({b₀} : Set G)) =
      Nat.card ↥((Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G)) ⊓
        Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G)) *
        Nat.card (ggAutomizer (Subgroup.normalizer (E : Set G) ⊓
          Subgroup.centralizer ({b₀} : Set G)) ((E ⊓ K : Subgroup G))) := by
    have h := card_inf_normalizer_eq_card_centralizer_mul_card_automizer
      (H := Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G))
      (A := (E ⊓ K : Subgroup G))
    rwa [inf_eq_left.mpr hM_le_NE1] at h
  have hCM_E_eq := centralizer_inf_eq_of_normalizer_le hsup
  have hCGE_eq : (Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G)) ⊓
      Subgroup.centralizer (E : Set G) = Subgroup.centralizer (E : Set G) :=
    inf_eq_right.mpr hCGE_le_M
  rw [hCGE_eq] at hMcard
  have hcardCM : Nat.card ↥((Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({b₀} : Set G)) ⊓
      Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G)) =
      Nat.card ↥(Subgroup.centralizer (E : Set G)) := by
    rw [← hCM_E_eq, hCGE_eq]
  have hMcard_E1' : Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({b₀} : Set G)) =
      Nat.card ↥(Subgroup.centralizer (E : Set G)) *
        Nat.card (ggAutomizer (Subgroup.normalizer (E : Set G) ⊓
          Subgroup.centralizer ({b₀} : Set G)) ((E ⊓ K : Subgroup G))) := by
    rw [hMcard_E1, hcardCM]
  exact Nat.mul_left_cancel
    (Nat.card_pos (α := ↥(Subgroup.centralizer (E : Set G))))
    (hMcard.symm.trans hMcard_E1')

private theorem relIndex_inf_normalizer_le_two {G : Type} [Group G] [Finite G]
    {b₀ : G} {E : Subgroup G} (hb₀ : orderOf b₀ = 3)
    (hNle : Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :
    (Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G)).relIndex
      (Subgroup.normalizer (E : Set G)) ≤ 2 := by
  have hC_zpow : Subgroup.centralizer (Subgroup.zpowers b₀ : Set G) =
      Subgroup.centralizer ({b₀} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have h := relIndex_inf_centralizer_inf_normalizer_le_two (M := Subgroup.normalizer (E : Set G))
    (A := Subgroup.zpowers b₀) (by rw [Nat.card_zpowers, hb₀])
  rw [hC_zpow, inf_eq_left.mpr hNle] at h
  exact h

private theorem exists_zpow_order_three_of_generator {G : Type} [Group G] [Finite G]
    {b₀ : G} {K D : Subgroup G}
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hD_le_C : D ≤ Subgroup.centralizer ({b₀} : Set G))
    (hD_le_CK : D ≤ Subgroup.centralizer (K : Set G))
    (hA2 : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    {k : ℕ} {dP : ↥D} (hk2 : 2 ≤ k) (hdPord : orderOf dP = 3 ^ k) :
    ∃ zP : ↥D, orderOf zP = 3 ∧ (zP : G) ∈ Subgroup.zpowers b₀ ∧
      Subgroup.zpowers (zP : G) = Subgroup.zpowers b₀ ∧
      (zP : G) = (dP : G) ^ (3 ^ (k - 1)) := by
  have hk2' : 2 ≤ k := hk2
  let zP : ↥D := dP ^ (3 ^ (k - 1))
  have hz3 : zP ^ 3 = 1 := by
    change (dP ^ (3 ^ (k - 1))) ^ 3 = 1
    rw [← pow_mul, show 3 ^ (k - 1) * 3 = 3 ^ k by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]]
    rw [← hdPord]
    exact pow_orderOf_eq_one dP
  have hz1 : zP ≠ 1 := by
    intro h
    have hdvd : orderOf dP ∣ 3 ^ (k - 1) := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact h
    rw [hdPord] at hdvd
    have hlt : 3 ^ (k - 1) < 3 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hle := Nat.le_of_dvd (pow_pos (by norm_num) (k - 1)) hdvd
    omega
  have hzord : orderOf zP = 3 := orderOf_eq_prime hz3 hz1
  have hzG_ord : orderOf (zP : G) = 3 := by
    rw [show (zP : G) = ((zP : D) : G) from rfl, Subgroup.orderOf_coe (zP : D)]
    exact hzord
  have hzG3 : (zP : G) ^ 3 = 1 := by
    rw [← hzG_ord]
    exact pow_orderOf_eq_one _
  have hzG_D : (zP : G) ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G) :=
    ⟨hD_le_C zP.2, hD_le_CK zP.2⟩
  have hzG_zp : (zP : G) ∈ Subgroup.zpowers b₀ :=
    mem_zpowers_of_orderOf_eq_three_of_mem_inf_centralizer hb₀ hKC hA2 hzG_D hzG3
  have hzp_eq : Subgroup.zpowers (zP : G) = Subgroup.zpowers b₀ := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzG_zp)
    rw [Nat.card_zpowers, Nat.card_zpowers, hzG_ord, hb₀]
  have hzPval : (zP : G) = (dP : G) ^ (3 ^ (k - 1)) := by
    have hzPdef : (zP : ↥D) = dP ^ (3 ^ (k - 1)) := rfl
    calc (zP : G) = ((zP : ↥D) : G) := rfl
      _ = ((dP ^ (3 ^ (k - 1)) : ↥D) : G) := by rw [hzPdef]
      _ = (dP : G) ^ (3 ^ (k - 1)) := by simp
  exact ⟨zP, hzord, hzG_zp, hzp_eq, hzPval⟩

private theorem normalizer_mem_zpowers_of_decomposition {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E D : Subgroup G}
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hD_le_C : D ≤ Subgroup.centralizer ({b₀} : Set G))
    (hD_le_CK : D ≤ Subgroup.centralizer (K : Set G))
    (hA2 : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    {k : ℕ} {dP zP : ↥D} (hk2 : 2 ≤ k)
    (hzord : orderOf (zP : G) = 3)
    (hzp_eq : Subgroup.zpowers (zP : G) = Subgroup.zpowers b₀)
    (hzPval : (zP : G) = (dP : G) ^ (3 ^ (k - 1)))
    (hdecomp : ∀ n ∈ Subgroup.normalizer (E : Set G),
      ∃ e ∈ (E ⊓ K : Subgroup G), ∃ d' ∈ D,
        n * (dP : G) * n⁻¹ = e * d' ∧ e ^ 3 = 1 ∧ Commute e d') :
    ∀ n ∈ Subgroup.normalizer (E : Set G), n * b₀ * n⁻¹ ∈ Subgroup.zpowers b₀ := by
  have hk2' : 2 ≤ k := hk2
  intro n hnN
  obtain ⟨e, heE1, d', hd'D, hed', he3, hedge⟩ := hdecomp n hnN
  have hpow : (n * (dP : G) * n⁻¹) ^ (3 ^ (k - 1)) = d' ^ (3 ^ (k - 1)) := by
    rw [hed', hedge.mul_pow]
    have hmul : 3 ∣ 3 ^ (k - 1) := by
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k - 1 ≠ 0)
      exact ⟨3 ^ j, by rw [hj, pow_succ]; ring⟩
    obtain ⟨t, ht⟩ := hmul
    rw [ht, pow_mul, he3, one_pow, one_mul]
  have hconjz : n * (zP : G) * n⁻¹ = (n * (dP : G) * n⁻¹) ^ (3 ^ (k - 1)) := by
    rw [hzPval, ← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  have horder_conj : orderOf (n * (zP : G) * n⁻¹) = 3 := by
    rw [← hzord]
    exact orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective _
  have hd'pow_order : orderOf (d' ^ (3 ^ (k - 1))) = 3 := by
    calc orderOf (d' ^ (3 ^ (k - 1))) =
          orderOf ((n * (dP : G) * n⁻¹) ^ (3 ^ (k - 1))) := by rw [hpow]
      _ = orderOf (n * (zP : G) * n⁻¹) := by rw [← hconjz]
      _ = 3 := horder_conj
  have hd'pow3 : (d' ^ (3 ^ (k - 1))) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (d' ^ (3 ^ (k - 1)))
    rwa [hd'pow_order] at h
  have hd'powD : d' ^ (3 ^ (k - 1)) ∈ D := D.pow_mem hd'D _
  have hd'pow_zp : d' ^ (3 ^ (k - 1)) ∈ Subgroup.zpowers b₀ :=
    mem_zpowers_of_orderOf_eq_three_of_mem_inf_centralizer hb₀ hKC hA2
      ⟨hD_le_C hd'powD, hD_le_CK hd'powD⟩ hd'pow3
  have hnz_z : n * (zP : G) * n⁻¹ ∈ Subgroup.zpowers (zP : G) := by
    rw [hzp_eq, hconjz, hpow]
    exact hd'pow_zp
  have hn_norm_z : n ∈ Subgroup.normalizer (Subgroup.zpowers (zP : G) : Set G) :=
    (CFSG.GroupTheory.mem_normalizer_zpowers_iff).mpr hnz_z
  have hn_norm_b : n ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    rwa [hzp_eq] at hn_norm_z
  exact (CFSG.GroupTheory.mem_normalizer_zpowers_iff.mp hn_norm_b)

private theorem exists_complement_data_of_order_three
    {G : Type} [Group G] [Finite G] {b₀ : G} {K : Subgroup G}
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hnot9 : ¬ 9 ∣ Nat.card ↥(Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G))) :
    ∃ Q : Subgroup G, Q ≤ Subgroup.centralizer ({b₀} : Set G) ⊓
        Subgroup.centralizer (K : Set G) ∧
      Nat.Coprime 3 (Nat.card Q) ∧
      (∀ x ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G),
        ∃ i : ℤ, ∃ q ∈ Q, x = b₀ ^ i * q) ∧
      (∀ Q' : Subgroup G, Q' ≤ Subgroup.centralizer ({b₀} : Set G) ⊓
        Subgroup.centralizer (K : Set G) → Nat.Coprime 3 (Nat.card Q') → Q' ≤ Q) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({b₀} : Set G) with hCdef
  set D : Subgroup G := C ⊓ Subgroup.centralizer (K : Set G) with hDdef
  have hb₀C : b₀ ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
  have hb₀CK : b₀ ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hKC hk) b₀ (by simp)).symm
  have hb₀D : b₀ ∈ D := ⟨hb₀C, hb₀CK⟩
  let z : D := ⟨b₀, hb₀D⟩
  have hz : orderOf z = 3 := by
    rw [← Subgroup.orderOf_coe z, hb₀]
  have hzc : ∀ d : D, Commute z d := by
    intro d
    have hcomm : d * z = z * d := by
      have h1 := Subgroup.mem_centralizer_iff.mp d.2.1 b₀ (by simp)
      apply Subtype.ext
      simpa [z] using h1.symm
    exact hcomm.symm
  have hindex : ¬ 3 ∣ (Subgroup.zpowers z).index := by
    have hcard : Nat.card ↥D = 3 * (Subgroup.zpowers z).index := by
      rw [← (Subgroup.zpowers z).card_mul_index, Nat.card_zpowers, hz]
    intro h3
    apply hnot9
    obtain ⟨t, ht⟩ := h3
    exact ⟨t, by rw [hcard, ht]; ring⟩
  obtain ⟨Qd, hQdnormal, hQddisjoint, hQdsup, hQddecomp, hQdcop, hQdcont⟩ :=
    exists_normal_complement_of_central_order_prime (D := D) (z := z) hz hzc hindex
  let Q : Subgroup G := Qd.map D.subtype
  have hQ_le_D : Q ≤ D := Subgroup.map_subtype_le Qd
  have hQcard : Nat.card ↥Q = Nat.card ↥Qd :=
    Subgroup.card_map_of_injective D.subtype_injective
  have hQcop : Nat.Coprime 3 (Nat.card Q) := by
    rw [hQcard]
    exact hQdcop
  have hQdecomp : ∀ x ∈ D, ∃ i : ℤ, ∃ q ∈ Q, x = b₀ ^ i * q := by
    intro x hx
    obtain ⟨i, qd, hqd, hxeq⟩ := hQddecomp ⟨x, hx⟩
    refine ⟨i, (qd : G), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨qd, hqd, rfl⟩
    · have h := congrArg (fun y : D => (y : G)) hxeq
      simpa [z] using h
  have hQcont : ∀ Q' : Subgroup G, Q' ≤ D → Nat.Coprime 3 (Nat.card Q') → Q' ≤ Q := by
    intro Q' hQ' hcop
    have hsub : Q'.subgroupOf D ≤ Qd := by
      apply hQdcont (Q'.subgroupOf D)
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ').toEquiv]
        exact hcop
    intro x hx
    let y : D := ⟨x, hQ' hx⟩
    have hy : y ∈ Qd := hsub hx
    exact (Subgroup.mem_map (K := Qd) (y := x) (f := D.subtype)).mpr ⟨y, hy, rfl⟩
  exact ⟨Q, hQ_le_D, hQcop, hQdecomp, hQcont⟩

private theorem coprime_three_pow_five_relIndex {G : Type} [Group G] [Finite G]
    {b₀ : G} {E : Subgroup G} (hb₀ : orderOf b₀ = 3)
    (hNle : Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :
    Nat.Coprime (3 ^ 5) ((Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({b₀} : Set G)).relIndex (Subgroup.normalizer (E : Set G))) := by
  have hMrel := relIndex_inf_normalizer_le_two (E := E) hb₀ hNle
  have hrelpos : 0 < (Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({b₀} : Set G)).relIndex (Subgroup.normalizer (E : Set G)) := by
    change 0 < ((Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({b₀} : Set G)).subgroupOf (Subgroup.normalizer (E : Set G))).index
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
      (H := (Subgroup.normalizer (E : Set G) ⊓
        Subgroup.centralizer ({b₀} : Set G)).subgroupOf (Subgroup.normalizer (E : Set G))))
  have hrel_cases : (Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({b₀} : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 1 ∨
      (Subgroup.normalizer (E : Set G) ⊓
        Subgroup.centralizer ({b₀} : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 2 := by
    omega
  rcases hrel_cases with h | h <;> rw [h] <;> norm_num

private theorem not_nine_dvd_card_inf_centralizer {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G}
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hA2 : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hC_le_KD : Subgroup.centralizer ({b₀} : Set G) ≤
      K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)))
    (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E)
    (hE1max : IsMaxElemAb3 K (E ⊓ K))
    (hE1SC : Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) ⊓ K = E ⊓ K)
    (hExists : ∃ n ∈ Subgroup.normalizer (E : Set G), n * b₀ * n⁻¹ ∉ Subgroup.zpowers b₀) :
    ¬ 9 ∣ Nat.card ↥(Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G)) := by
  classical
  intro h9
  set C : Subgroup G := Subgroup.centralizer ({b₀} : Set G) with hCdef
  set D : Subgroup G := C ⊓ Subgroup.centralizer (K : Set G) with hDdef
  set E₁ : Subgroup G := E ⊓ K with hE1def
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD_Czp : D ≤ Subgroup.centralizer (Subgroup.zpowers b₀ : Set G) := by
    rw [hDdef, hCdef, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact inf_le_left
  have hD_CE1 : D ≤ Subgroup.centralizer (E₁ : Set G) :=
    (inf_le_right : D ≤ Subgroup.centralizer (K : Set G)).trans
      (Subgroup.centralizer_le (inf_le_right : E₁ ≤ K))
  have hD_le_CE : D ≤ Subgroup.centralizer (E : Set G) := by
    have h := CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
      (K := D) (A := Subgroup.zpowers b₀) (B := E₁) hD_Czp hD_CE1
    rwa [hsup] at h
  have hC_le_normK : C ≤ Subgroup.normalizer (K : Set G) := by
    rw [hCdef, ← Subgroup.normal_subgroupOf_iff_le_normalizer hKC]
    exact hKn
  have hCE_le : Subgroup.centralizer (E : Set G) ≤ E₁ ⊔ D := by
    intro c hc
    have hcC : c ∈ C := by
      rw [hCdef, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      have hbE : b₀ ∈ E := by
        rw [← hsup]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀)
      simpa [hy] using Subgroup.mem_centralizer_iff.mp hc b₀ hbE
    obtain ⟨k, hk, d, hd, hkd⟩ :=
      fs81Sp_mem_sup_of_commute fs81Sp_comm (hC_le_KD hcC)
    have hc_CE1 : c ∈ Subgroup.centralizer (E₁ : Set G) :=
      Subgroup.centralizer_le (inf_le_left : E₁ ≤ E) hc
    have hd_CE1 : d ∈ Subgroup.centralizer (E₁ : Set G) :=
      Subgroup.centralizer_le (inf_le_right : E₁ ≤ K) hd.2
    have hk_CE1 : k ∈ Subgroup.centralizer (E₁ : Set G) := by
      have hkeq : k = c * d⁻¹ := by rw [hkd]; group
      rw [hkeq]
      exact Subgroup.mul_mem _ hc_CE1 (Subgroup.inv_mem _ hd_CE1)
    have hkE1 : k ∈ E₁ := by
      have hmem : k ∈ Subgroup.centralizer (E₁ : Set G) ⊓ K := ⟨hk_CE1, hk⟩
      rwa [hE1SC] at hmem
    rw [hkd]
    exact Subgroup.mul_mem_sup hkE1 hd
  have hcomm_E1_D : ∀ a ∈ E₁, ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp hb.2 a ha.2
  let P : Sylow 3 ↥D := Classical.choice Sylow.nonempty
  have hcyc : IsCyclic ↥(P : Subgroup ↥D) :=
    sylow_three_cyclic_of_le_centralizer hA2 (by rw [hDdef]; exact inf_le_right) P
  obtain ⟨k, dP, hk2, hdPord⟩ := exists_generator_order_of_nine_dvd P hcyc (by simpa [D] using h9)
  let dPD : ↥D := dP.1
  have hdPord' : orderOf dPD = 3 ^ k := by simpa [dPD] using hdPord
  obtain ⟨zPD, hzord, hzG_zp, hzp_eq, hzPval⟩ :=
    exists_zpow_order_three_of_generator hb₀ hKC (by rw [hDdef]; exact inf_le_left)
      (by rw [hDdef]; exact inf_le_right) hA2 hk2 hdPord'
  have hdecomp := exists_decomposition_of_conj_sylow_generator (E := E) (D := D)
    hE1max hD_le_CE hCE_le (dP := dPD)
  have hzordG : orderOf (zPD : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hzord
  have h_all := normalizer_mem_zpowers_of_decomposition (b₀ := b₀) hb₀ hKC
    (by rw [hDdef]; exact inf_le_left) (by rw [hDdef]; exact inf_le_right) hA2
    hk2 hzordG hzp_eq hzPval hdecomp
  obtain ⟨n, hnN, hnnot⟩ := hExists
  exact hnnot (h_all n hnN)

private theorem exists_complement_of_order_three_in_centralizer
    {G : Type} [Group G] [Finite G] {b₀ : G} {K : Subgroup G}
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hnot9 : ¬ 9 ∣ Nat.card ↥(Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G))) :
    ∃ Q : Subgroup G, Q ≤ Subgroup.centralizer ({b₀} : Set G) ⊓
        Subgroup.centralizer (K : Set G) ∧
      (Q.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal ∧
      Nat.Coprime 3 (Nat.card Q) ∧
      (∀ x ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G),
        ∃ i : ℤ, ∃ q ∈ Q, x = b₀ ^ i * q) ∧
      (∀ Q' : Subgroup G, Q' ≤ Subgroup.centralizer ({b₀} : Set G) ⊓
        Subgroup.centralizer (K : Set G) → Nat.Coprime 3 (Nat.card Q') → Q' ≤ Q) := by
  classical
  obtain ⟨Q, hQ_le_D, hQcop, hQdecomp, hQcont⟩ :=
    exists_complement_data_of_order_three hb₀ hKC hnot9
  set C : Subgroup G := Subgroup.centralizer ({b₀} : Set G) with hCdef
  set D : Subgroup G := C ⊓ Subgroup.centralizer (K : Set G) with hDdef
  have hD_normal_C : (D.subgroupOf C).Normal := by
    have : (K.subgroupOf C).Normal := hKn
    have hDc_eq : D.subgroupOf C = Subgroup.centralizer (K.subgroupOf C : Set C) := by
      ext x
      constructor
      · intro hx
        have hx' : (x : G) ∈ D := hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hx'.2 (y : G) hy
      · intro hx
        have hxD : (x : G) ∈ D := by
          refine ⟨x.2, ?_⟩
          change (x : G) ∈ Subgroup.centralizer (K : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hyC : y ∈ C := hKC hy
          exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx ⟨y, hyC⟩ hy)
        exact hxD
    rw [hDc_eq]
    exact Subgroup.normal_centralizer (H := K.subgroupOf C)
  have hC_le_normD : C ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : D ≤ C)).mp hD_normal_C
  have hQ_normal : (Q.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hQ_le_D.trans inf_le_left)]
    intro c hc
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcardmap : Nat.card ↥(Q.map (MulAut.conj c).toMonoidHom) = Nat.card ↥Q :=
      (Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj c) Q).toEquiv).symm
    have hle : Q.map (MulAut.conj c).toMonoidHom ≤ Q := by
      apply hQcont
      · rintro _ ⟨q, hq, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hC_le_normD hc) (q : G)).mp (hQ_le_D hq)
      · rw [hcardmap]
        exact hQcop
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardmap.symm)
  exact ⟨Q, hQ_le_D, hQ_normal, hQcop, hQdecomp, hQcont⟩

private theorem three_pow_five_dvd_automizer_of_normalizer_le {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G}
    (hb₀ : orderOf b₀ = 3)
    (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E)
    (hAut : Nat.card (ggAutomizer ⊤ E) = 696729600)
    (hNle : Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :
    3 ^ 5 ∣ Nat.card (ggAutomizer (Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({b₀} : Set G)) E) := by
  have hb₀E : b₀ ∈ E := by
    rw [← hsup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀)
  have hCGE_le_M : Subgroup.centralizer (E : Set G) ≤
      Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G) := by
    refine le_inf (Subgroup.centralizer_le_normalizer (E : Set G)) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using Subgroup.mem_centralizer_iff.mp hx b₀ hb₀E
  have hM_le_N : Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G) ≤
      Subgroup.normalizer (E : Set G) := inf_le_left
  have hNcard : Nat.card ↥(Subgroup.normalizer (E : Set G)) =
      Nat.card ↥(Subgroup.centralizer (E : Set G)) *
        Nat.card (ggAutomizer ⊤ E) := by
    have h := card_inf_normalizer_eq_card_centralizer_mul_card_automizer (H := ⊤) (A := E)
    simpa [inf_comm] using h
  have hMcard : Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({b₀} : Set G)) =
      Nat.card ↥(Subgroup.centralizer (E : Set G)) *
        Nat.card (ggAutomizer (Subgroup.normalizer (E : Set G) ⊓
          Subgroup.centralizer ({b₀} : Set G)) E) := by
    have h := card_inf_normalizer_eq_card_centralizer_mul_card_automizer
      (H := Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G)) (A := E)
    rw [inf_eq_left.mpr hM_le_N, inf_eq_right.mpr hCGE_le_M] at h
    exact h
  have hC_zpow : Subgroup.centralizer (Subgroup.zpowers b₀ : Set G) =
      Subgroup.centralizer ({b₀} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcop := coprime_three_pow_five_relIndex (E := E) hb₀ hNle
  have hmain : Nat.card (ggAutomizer (Subgroup.normalizer (E : Set G) ⊓
        Subgroup.centralizer ({b₀} : Set G)) E) *
        (Subgroup.normalizer (E : Set G) ⊓
          Subgroup.centralizer ({b₀} : Set G)).relIndex (Subgroup.normalizer (E : Set G)) =
      Nat.card (ggAutomizer ⊤ E) := by
    have h1 := card_inf_normalizer_mul_relIndex (b₀ := b₀) (E := E)
    rw [hMcard, hNcard, mul_assoc] at h1
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥(Subgroup.centralizer (E : Set G)))) h1
  rw [hAut] at hmain
  exact hcop.dvd_of_dvd_mul_right (by rw [hmain]; norm_num)

theorem not_three_pow_twelve_dvd_card_of_isRow_E7 {G : Type} [Group G] [Finite G]
    {K : Subgroup G} (hK : IsRow Row.E7 K) : ¬ 3 ^ 12 ∣ Nat.card K := by
  obtain ⟨F, hF, hFfin, hFcard, θ, hperf⟩ := isRow_E7_data hK
  let := hF
  have := hFfin
  obtain ⟨-, eK, -, -⟩ := P10a_cover_E7 (F := F) (K := ↥K) hFcard hperf θ
  rw [Nat.card_congr eK.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7,
    CFSG.Open.ordE7, hFcard]
  norm_num

theorem le_sup_centralizer_of_isRow_E7 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsRow Row.E7 K) {R : Subgroup G} (hR : R ≤ Subgroup.normalizer (K : Set G)) :
    R ≤ K ⊔ Subgroup.centralizer (K : Set G) := by
  obtain ⟨F, hF, hFfin, hFcard, θ, hperf⟩ := isRow_E7_data hK
  let := hF
  have := hFfin
  obtain ⟨-, eK, -, -⟩ := P10a_cover_E7 (F := F) (K := ↥K) hFcard hperf θ
  refine CFSG.le_sup_centralizer_of_forall_mem_range_conj hR (fun r hr => ?_)
  refine (CFSG.SeitzReduction.F4Pilot.conj_mem_range_conj_iff eK
    (K.normalizerMonoidHom ⟨r, hR hr⟩)).1 ?_
  obtain ⟨g, hg⟩ := CFSG.SeitzReduction.E8Pilot.exists_eq_conj_of_forall_eq_zero_or_eq_one
    (Or.inl rfl)
    (fun c => CFSG.ClassicalGroups.Alternating.eq_zero_or_eq_one_of_card_eq_two hFcard c)
    ((eK.symm.trans (K.normalizerMonoidHom ⟨r, hR hr⟩)).trans eK)
  exact ⟨g, hg.symm⟩

private theorem automizer_inf_le_automizer_of_le_sup_inf {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hRow : IsRow Row.E7 K) :
    ggAutomizer (Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({b₀} : Set G))
        ((E ⊓ K : Subgroup G)) ≤
      ggAutomizer K ((E ⊓ K : Subgroup G)) := by
  have hC_le_normK : Subgroup.centralizer ({b₀} : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hKC]
    exact hKn
  have hC_le_KD : Subgroup.centralizer ({b₀} : Set G) ≤
      K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)) := by
    intro c hc
    have hc' : c ∈ K ⊔ Subgroup.centralizer (K : Set G) :=
      le_sup_centralizer_of_isRow_E7 hRow hC_le_normK hc
    obtain ⟨k, hk, d, hd, hkd⟩ := fs81Sp_mem_sup_of_commute
      (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha) hc'
    have hdC : d ∈ Subgroup.centralizer ({b₀} : Set G) := by
      have hdeq : d = k⁻¹ * c := by rw [hkd]; group
      rw [hdeq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKC hk)) hc
    rw [hkd]
    exact Subgroup.mul_mem_sup hk ⟨hdC, hd⟩
  intro φ hφ
  obtain ⟨m, hmM, hmN, hφm⟩ := mem_ggAutomizer_iff.mp hφ
  obtain ⟨k, hk, d, hd, hmd⟩ :=
    fs81Sp_mem_sup_of_commute fs81Sp_comm (hC_le_KD hmM.2)
  have hdCK : d ∈ Subgroup.centralizer (K : Set G) := hd.2
  have hd_CE1 : d ∈ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (inf_le_right : E ⊓ K ≤ K) hdCK
  have hd_NE1 : d ∈ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer ((E ⊓ K : Subgroup G) : Set G) hd_CE1
  have hk_NE1 : k ∈ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G) := by
    have hk_eq : k = m * d⁻¹ := by rw [hmd]; group
    rw [hk_eq]
    exact Subgroup.mul_mem _ hmN (Subgroup.inv_mem _ hd_NE1)
  refine mem_ggAutomizer_iff.mpr ⟨k, hk, hk_NE1, fun b => ?_⟩
  have hdb : d * (b : G) = (b : G) * d :=
    (Subgroup.mem_centralizer_iff.mp hdCK (b : G) b.2.2).symm
  rw [hφm b]
  calc m * (b : G) * m⁻¹ = k * d * (b : G) * (d⁻¹ * k⁻¹) := by rw [hmd]; group
    _ = k * (d * (b : G) * d⁻¹) * k⁻¹ := by group
    _ = k * ((b : G) * d * d⁻¹) * k⁻¹ := by rw [hdb]
    _ = k * (b : G) * k⁻¹ := by group

private theorem exists_normalizer_not_normalizes_zpowers {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G}
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hRow : IsRow Row.E7 K)
    (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E)
    (hE1max : IsMaxElemAb3 K (E ⊓ K))
    (hE1card : Nat.card ↥(E ⊓ K) = 3 ^ 7)
    (hAut : Nat.card (ggAutomizer ⊤ E) = 696729600) :
    ∃ n ∈ Subgroup.normalizer (E : Set G), n * b₀ * n⁻¹ ∉ Subgroup.zpowers b₀ := by
  classical
  by_contra hnot
  have hNle : Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    intro n hn
    rw [CFSG.GroupTheory.mem_normalizer_zpowers_iff]
    by_contra hn'
    exact hnot ⟨n, hn, hn'⟩
  have hAM_dvd := three_pow_five_dvd_automizer_of_normalizer_le hb₀ hsup hAut hNle
  have hAM_E_eq := automizer_card_eq_of_normalizer_le hKC hKn hsup
  have hAM_le := automizer_inf_le_automizer_of_le_sup_inf (E := E) hKC hKn hRow
  have hE1_le_KC : (E ⊓ K : Subgroup G) ≤
      K ⊓ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) := by
    intro x hx
    refine ⟨hx.2, ?_⟩
    change x ∈ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (IsElemAbelian.comm hE1max.2.1 hx hy).symm
  have hKcard : Nat.card ↥(K ⊓ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G)) =
      Nat.card ↥(K ⊓ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G)) *
        Nat.card (ggAutomizer K ((E ⊓ K : Subgroup G))) :=
    card_inf_normalizer_eq_card_centralizer_mul_card_automizer (H := K) (A := (E ⊓ K : Subgroup G))
  have hdvd1 : 3 ^ 7 ∣ Nat.card ↥(K ⊓ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G)) := by
    rw [← hE1card]
    exact Subgroup.card_dvd_of_le hE1_le_KC
  have hAM_E1_dvd : 3 ^ 5 ∣ Nat.card (ggAutomizer (Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({b₀} : Set G)) ((E ⊓ K : Subgroup G))) := by
    rw [← hAM_E_eq]
    exact hAM_dvd
  have hAK_dvd : 3 ^ 5 ∣ Nat.card (ggAutomizer K ((E ⊓ K : Subgroup G))) :=
    hAM_E1_dvd.trans (Subgroup.card_dvd_of_le hAM_le)
  have h12 : 3 ^ 12 ∣ Nat.card ↥(K ⊓ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G)) := by
    rw [hKcard]
    have := Nat.mul_dvd_mul hdvd1 hAK_dvd
    simpa [← pow_add] using this
  exact not_three_pow_twelve_dvd_card_of_isRow_E7 hRow
    (h12.trans (Subgroup.card_dvd_of_le inf_le_left))

theorem e7CapAt_holds : E7CapAt := by
  intro G _ _ b₀ K E hstd B hB hrec Y hKY hb₀Y hZY hCore
  obtain ⟨hGsimple, hHyp, hCanon⟩ := hstd
  obtain ⟨hA, hEmax, hb₀E, hEcard, hm7, hAutBig⟩ := hHyp
  obtain ⟨hb₀ord, hKC, hKn, hKz, hKmark, hA2, hA3, hA4⟩ := hA
  obtain ⟨hRow, hdisj, hsup, hE1max, hE1card, hE1SC⟩ := hCanon
  have hAut : Nat.card (ggAutomizer ⊤ E) = 696729600 := by
    rw [← hB.1]
    exact hrec.1
  have hExists := exists_normalizer_not_normalizes_zpowers hb₀ord hKC hKn hRow hsup
    hE1max hE1card hAut
  have hC_le_KD : Subgroup.centralizer ({b₀} : Set G) ≤
      K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)) := by
    intro c hc
    have hc' : c ∈ K ⊔ Subgroup.centralizer (K : Set G) := by
      have hC_le_normK : Subgroup.centralizer ({b₀} : Set G) ≤
          Subgroup.normalizer (K : Set G) := by
        rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hKC]
        exact hKn
      exact le_sup_centralizer_of_isRow_E7 hRow hC_le_normK hc
    obtain ⟨k, hk, d, hd, hkd⟩ := fs81Sp_mem_sup_of_commute
      (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha) hc'
    have hdC : d ∈ Subgroup.centralizer ({b₀} : Set G) := by
      have hdeq : d = k⁻¹ * c := by rw [hkd]; group
      rw [hdeq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKC hk)) hc
    rw [hkd]
    exact Subgroup.mul_mem_sup hk ⟨hdC, hd⟩
  have hnot9 : ¬ 9 ∣ Nat.card ↥(Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G)) :=
    not_nine_dvd_card_inf_centralizer hb₀ord hKC hKn hA2 hC_le_KD hsup
      hE1max hE1SC hExists
  obtain ⟨Q, hQ_le_D, hQ_normal, hQcop, hQdecomp, hQcont⟩ :=
    exists_complement_of_order_three_in_centralizer hb₀ord hKC hKn hnot9
  have hb₀C : b₀ ∈ Subgroup.centralizer ({b₀} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
  apply le_antisymm
  · intro y hy
    have hyC : y ∈ Subgroup.centralizer ({b₀} : Set G) := hy.1
    have hyY : y ∈ Y := hy.2
    obtain ⟨k, hk, d, hd, hyd⟩ := fs81Sp_mem_sup_of_commute fs81Sp_comm (hC_le_KD hyC)
    obtain ⟨i, q, hqQ, hdq⟩ := hQdecomp d hd
    have hqC : q ∈ Subgroup.centralizer ({b₀} : Set G) := (hQ_le_D hqQ).1
    have hqY : q ∈ Y := by
      have hqeq : q = b₀ ^ (-i) * k⁻¹ * y := by rw [hyd, hdq]; group
      rw [hqeq]
      refine Y.mul_mem (Y.mul_mem ?_ (Y.inv_mem (hKY hk))) hyY
      exact Subgroup.zpowers_le.mpr hb₀Y (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b₀) (-i))
    have hQnot3 : ¬ 3 ∣ Nat.card ↥Q :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hQcop
    have hQcore : Q ≤ Subgroup.centralizer (Y : Set G) :=
      hCore Q (hQ_le_D.trans inf_le_left) hQ_normal hQnot3
    have hqCY : q ∈ Subgroup.centralizer (Y : Set G) := hQcore hqQ
    have hqbot : q ∈ (⊥ : Subgroup G) := by
      rw [← hZY]
      exact ⟨hqCY, hqY⟩
    have hq1 : q = 1 := Subgroup.mem_bot.mp hqbot
    have hy_eq : y = k * b₀ ^ i := by rw [hyd, hdq, hq1, mul_one]
    have hy_sup : y ∈ K ⊔ Subgroup.zpowers b₀ := by
      rw [hy_eq]
      exact Subgroup.mul_mem_sup hk (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b₀) i)
    rwa [sup_comm] at hy_sup
  · refine sup_le (le_inf (Subgroup.zpowers_le.mpr hb₀C) (Subgroup.zpowers_le.mpr hb₀Y))
      (le_inf hKC hKY)

end CFSG.StandardType.FrameRoute.FS81
