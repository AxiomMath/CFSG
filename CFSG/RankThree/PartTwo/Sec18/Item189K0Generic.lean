module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.RankThree.PartTwo.Late

private theorem mem_normalizer_of_commute_generic {Q : Type} [Group Q] {S : Subgroup Q} {g : Q}
    (h : ∀ s ∈ S, s * g = g * s) : g ∈ Subgroup.normalizer (S : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    have h1 : g * s * g⁻¹ = s := by
      rw [← h s hs, mul_inv_cancel_right]
    rw [h1]
    exact hs
  · intro hs
    have hz : g * s * g⁻¹ * g = g * (g * s * g⁻¹) := h (g * s * g⁻¹) hs
    have hz' : g * s = g * (g * s * g⁻¹) := by
      rw [inv_mul_cancel_right] at hz
      exact hz
    have hs' : s = g * s * g⁻¹ := by
      have e1 : g⁻¹ * (g * s) = s := inv_mul_cancel_left g s
      have e2 : g⁻¹ * (g * s) = g⁻¹ * (g * (g * s * g⁻¹)) :=
        congrArg (fun t => g⁻¹ * t) hz'
      have e3 : g⁻¹ * (g * (g * s * g⁻¹)) = g * s * g⁻¹ := inv_mul_cancel_left g _
      exact e1.symm.trans (e2.trans e3)
    rw [hs']
    exact hs

theorem isElemAbelian_zpowers_sup {Q : Type} [Group Q] [Finite Q] {P : Subgroup Q} {e : Q}
    (hP : CFSG.Open.IsElemAbelian 3 P) (he3 : e ^ 3 = 1) (hce : ∀ x ∈ P, x * e = e * x)
    (heP : e ∉ P) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers e ⊔ P) ∧
      Nat.card (Subgroup.zpowers e ⊔ P : Subgroup Q) = 3 * Nat.card P := by
  have he1 : e ≠ 1 := by
    rintro rfl
    exact heP P.one_mem
  have hord : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hcardE : Nat.card (Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, hord]
  have hE : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers e) :=
    CFSG.Open.isElemAbelian_zpowers he3
  have hcomm : ∀ a ∈ Subgroup.zpowers e, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (show Commute e b from (hce b hb).symm) k).eq
  have hsup : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers e ⊔ P) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE hP hcomm
  have hnormal : P ≤ Subgroup.normalizer (Subgroup.zpowers e : Set Q) := by
    intro x hx
    apply mem_normalizer_of_commute_generic
    intro s hs
    exact hcomm s hs x hx
  have hdisj : Disjoint (Subgroup.zpowers e) P := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxP
    by_contra hx1
    have hx3 : x ^ 3 = 1 := hE.2 x hxE
    have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers e := Subgroup.zpowers_le.mpr hxE
    have h1 : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, hox]
    have heq : Subgroup.zpowers x = Subgroup.zpowers e :=
      Subgroup.eq_of_le_of_card_ge hle (by omega)
    apply heP
    have hePx : e ∈ Subgroup.zpowers x := by
      rw [heq]
      exact Subgroup.mem_zpowers e
    exact (Subgroup.zpowers_le.mpr hxP) hePx
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Subgroup.zpowers e) P hnormal hdisj
  exact ⟨hsup, by rw [hcard, hcardE]⟩

theorem isElemAbelian_sup_of_commute {Q : Type} [Group Q] [Finite Q] {P R : Subgroup Q}
    (hP : CFSG.Open.IsElemAbelian 3 P) (hR : CFSG.Open.IsElemAbelian 3 R)
    (hPR : ∀ x ∈ P, ∀ y ∈ R, x * y = y * x) (hdisj : P ⊓ R = ⊥) :
    CFSG.Open.IsElemAbelian 3 (P ⊔ R) ∧
      Nat.card (P ⊔ R : Subgroup Q) = Nat.card P * Nat.card R := by
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute hP hR hPR, ?_⟩
  have hnormal : R ≤ Subgroup.normalizer (P : Set Q) := by
    intro y hy
    apply mem_normalizer_of_commute_generic
    intro s hs
    exact hPR s hs y hy
  exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P R hnormal
    (disjoint_iff.mpr hdisj)

theorem le_normalizer_normalClosureIn_self {G : Type} [Group G] (M : Subgroup G) (c : G) :
    M ≤ Subgroup.normalizer (normalClosureIn M c : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ normalClosureIn M c, m * x * m⁻¹ ∈ normalClosureIn M c := by
    intro m hm x hx
    unfold normalClosureIn at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨n, hn, rfl⟩ := ha
      exact Subgroup.subset_closure ⟨m * n, mul_mem hm hn, by group⟩
    | one => simp
    | mul a b _ _ iha ihb =>
      have e : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
      rw [e]
      exact mul_mem iha ihb
    | inv a _ iha =>
      have e : m * a⁻¹ * m⁻¹ = (m * a * m⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem iha
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key m hm h hh
  · intro hh
    have h2 := key m⁻¹ (inv_mem hm) _ hh
    have e : m⁻¹ * (m * h * m⁻¹) * m⁻¹⁻¹ = h := by group
    rw [e] at h2
    exact h2

theorem card_le_of_isElemAbelian {Q : Type} [Group Q] [Finite Q] {r : ℕ}
    (hQ : CFSG.Open.pRank 3 (⊤ : Subgroup Q) ≤ r) {E : Subgroup Q}
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ r := by
  obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
  have hkr : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hE hk
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) (hkr.trans hQ)

theorem pRank_eq_one_of {Q : Type} [Group Q] [Finite Q] {K : Subgroup Q}
    (h3 : 3 ∣ Nat.card K)
    (h : ∀ E : Subgroup Q, E ≤ K → CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 3) :
    CFSG.Open.pRank 3 K = 1 := by
  apply le_antisymm
  · apply CFSG.SectionRank.pRank_le (p := 3) (by norm_num) (k := 1)
    intro E hEK hE
    rw [pow_one]
    exact h E hEK hE
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3
    have hq : orderOf (x : Q) = 3 := (Subgroup.orderOf_coe x).trans hx
    have hxQ : (x : Q) ^ 3 = 1 := by
      have h' := pow_orderOf_eq_one (x : Q)
      rwa [hq] at h'
    have hEK : Subgroup.zpowers (x : Q) ≤ K := Subgroup.zpowers_le.mpr x.2
    have hEa : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers (x : Q)) :=
      CFSG.Open.isElemAbelian_zpowers hxQ
    have hk : Nat.card (Subgroup.zpowers (x : Q)) = 3 ^ 1 := by
      rw [pow_one, Nat.card_zpowers, hq]
    exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hEK hEa hk

theorem exists_isSylowOf_ge {G : Type} [Group G] [Finite G] {D M : Subgroup G}
    (hD : IsPGroup 3 D) (hDM : D ≤ M) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P M ∧ D ≤ P := by
  have hDM' : IsPGroup 3 (D.subgroupOf M) := hD.comap_subtype
  obtain ⟨Q, hQ⟩ := hDM'.exists_le_sylow
  refine ⟨(Q : Subgroup M).map M.subtype, ⟨Q, rfl⟩, ?_⟩
  intro d hd
  have hdM : (⟨d, hDM hd⟩ : M) ∈ D.subgroupOf M := hd
  have hQd : (⟨d, hDM hd⟩ : M) ∈ (Q : Subgroup M) := hQ hdM
  exact Subgroup.mem_map.mpr ⟨⟨d, hDM hd⟩, hQd, rfl⟩

theorem exists_mem_inf_center_of_normal {G : Type} [Group G] [Finite G] {P N : Subgroup G}
    (hP : IsPGroup 3 P) (hNP : N ≤ P) (hN : (N.subgroupOf P).Normal) (hN1 : N ≠ ⊥) :
    ∃ t ∈ N, t ≠ 1 ∧ t ^ 3 = 1 ∧ ∀ x ∈ P, x * t = t * x := by
  haveI : Fact (IsPGroup 3 P) := ⟨hP⟩
  haveI : (N.subgroupOf P).Normal := hN
  haveI : Nontrivial (N.subgroupOf P) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro h
    apply hN1
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hNP] at h
    exact h
  obtain ⟨x, hx1, hxc⟩ := CFSG.exists_nontrivial_center_mem_normal (N.subgroupOf P) (p := 3)
  obtain ⟨y, hyN, hy1, hyc⟩ : ∃ y ∈ N, y ≠ 1 ∧ ∀ g ∈ P, g * y = y * g := by
    refine ⟨x.1.1, x.2, ?_, ?_⟩
    · intro h
      apply hx1
      exact Subtype.ext (Subtype.ext h)
    · intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨g, hg⟩)
  have hyP : y ∈ P := hNP hyN
  have h3 : 3 ∣ orderOf y := by
    obtain ⟨k, hk⟩ := hP ⟨y, hyP⟩
    have hk' : y ^ 3 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨i, _, hoi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk')
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply hy1
      rw [← orderOf_eq_one_iff]
      simpa using hoi
    rw [hoi]
    exact dvd_pow_self 3 hi0
  have ho : orderOf (y ^ (orderOf y / 3)) = 3 :=
    orderOf_pow_orderOf_div (orderOf_pos y).ne' h3
  refine ⟨y ^ (orderOf y / 3), pow_mem hyN _, ?_, ?_, ?_⟩
  · intro ht
    rw [ht, orderOf_one] at ho
    norm_num at ho
  · have h := pow_orderOf_eq_one (y ^ (orderOf y / 3))
    rwa [ho] at h
  · intro g hg
    exact (Commute.pow_right (show Commute g y from hyc g hg) _).eq

theorem inf_ne_bot_of_sylow {G : Type} [Group G] [Finite G] {M K P : Subgroup G}
    (hKM : K ≤ M) (hKn : M ≤ Subgroup.normalizer (K : Set G))
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P M) (h3 : 3 ∣ Nat.card K) : P ⊓ K ≠ ⊥ := by
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ K) K := hP.inf_of_le_normalizer hKM hKn
  have hcard : Nat.card (P ⊓ K : Subgroup G) = 3 ^ (Nat.card K).factorization 3 :=
    hS.card_eq
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hpos : 0 < (Nat.card K).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three hKpos.ne' h3
  intro hbot
  rw [hbot, Subgroup.card_bot] at hcard
  have h1 : 3 ^ 1 ≤ 3 ^ (Nat.card K).factorization 3 :=
    Nat.pow_le_pow_right (by norm_num) hpos
  rw [← hcard] at h1
  norm_num at h1

theorem eq_of_isPerfect_of_le_sup {G : Type} [Group G] [Finite G] {P N R : Subgroup G}
    (hP : Group.IsPerfect P) (hNP : N ≤ P) (hRP : R ≤ P) (hN : (N.subgroupOf P).Normal)
    (hR : Group.IsSolvable R) (hPNR : P ≤ N ⊔ R) : P = N := by
  haveI := hP
  haveI := hN
  haveI := hR
  have hPN : P ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mp hN
  have hRN : R ≤ Subgroup.normalizer (N : Set G) := hRP.trans hPN
  let f : R →* (P ⧸ N.subgroupOf P) :=
    (QuotientGroup.mk' (N.subgroupOf P)).comp (Subgroup.inclusion hRP)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨p₀, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf P) x
    have hmem : (p₀ : G) ∈ (↑(N ⊔ R) : Set G) := hPNR p₀.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N R hRN, Set.mem_mul] at hmem
    obtain ⟨n, hn, r, hr, hnr⟩ := hmem
    refine ⟨⟨r, hr⟩, ?_⟩
    have hp : p₀ = (⟨n, hNP hn⟩ : P) * ⟨r, hRP hr⟩ := Subtype.ext hnr.symm
    have hn1 : (QuotientGroup.mk' (N.subgroupOf P)) (⟨n, hNP hn⟩ : P) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hn
    show (QuotientGroup.mk' (N.subgroupOf P)) (⟨r, hRP hr⟩ : P) =
      (QuotientGroup.mk' (N.subgroupOf P)) p₀
    rw [hp, map_mul, hn1, one_mul]
  have hsolv : Group.IsSolvable (P ⧸ N.subgroupOf P) := Group.isSolvable_of_surjective hf
  have hsub : Subsingleton (P ⧸ N.subgroupOf P) := by
    by_contra hnt
    haveI : Nontrivial (P ⧸ N.subgroupOf P) := not_subsingleton_iff_nontrivial.mp hnt
    exact (Group.IsPerfect.not_isSolvable (P ⧸ N.subgroupOf P)) hsolv
  have htop : N.subgroupOf P = ⊤ := QuotientGroup.subgroup_eq_top_of_subsingleton _ hsub
  exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hNP

theorem commute_of_forall_commutator_mem_centralizer {Q : Type} [Group Q] {K : Subgroup Q}
    (hK : Group.IsPerfect K) {b : Q} (hbn : b ∈ Subgroup.normalizer (K : Set Q))
    (h : ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ Subgroup.centralizer (K : Set Q)) :
    ∀ k ∈ K, b * k = k * b := by
  have hφK : ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ K := by
    intro k hk
    have hbk : b * k * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hbn k).mp hk
    exact mul_mem hbk (inv_mem hk)
  have hmul : ∀ k₁ k₂ : K,
      b * ((k₁ * k₂ : K) : Q) * b⁻¹ * ((k₁ * k₂ : K) : Q)⁻¹ =
        (b * (k₁ : Q) * b⁻¹ * (k₁ : Q)⁻¹) * (b * (k₂ : Q) * b⁻¹ * (k₂ : Q)⁻¹) := by
    intro k₁ k₂
    have hc : ∀ x ∈ K, x * (b * (k₂ : Q) * b⁻¹ * (k₂ : Q)⁻¹) =
        (b * (k₂ : Q) * b⁻¹ * (k₂ : Q)⁻¹) * x :=
      fun x hx => Subgroup.mem_centralizer_iff.mp (h k₂ k₂.2) x hx
    set c : Q := b * (k₂ : Q) * b⁻¹ * (k₂ : Q)⁻¹ with hc_def
    have key : b * (k₂ : Q) * b⁻¹ = c * (k₂ : Q) := by
      rw [hc_def, inv_mul_cancel_right]
    have hk1 : c * (k₁ : Q)⁻¹ = (k₁ : Q)⁻¹ * c := by
      have e : (k₁ : Q) * c = c * (k₁ : Q) := hc (k₁ : Q) k₁.2
      calc c * (k₁ : Q)⁻¹ = (k₁ : Q)⁻¹ * ((k₁ : Q) * c) * (k₁ : Q)⁻¹ := by group
        _ = (k₁ : Q)⁻¹ * (c * (k₁ : Q)) * (k₁ : Q)⁻¹ := by rw [e]
        _ = (k₁ : Q)⁻¹ * c := by group
    calc b * ((k₁ * k₂ : K) : Q) * b⁻¹ * ((k₁ * k₂ : K) : Q)⁻¹
        = (b * (k₁ : Q) * b⁻¹) * (b * (k₂ : Q) * b⁻¹) * (k₂ : Q)⁻¹ * (k₁ : Q)⁻¹ := by
          simp only [Subgroup.coe_mul, mul_inv_rev]
          group
      _ = (b * (k₁ : Q) * b⁻¹) * (c * (k₂ : Q)) * (k₂ : Q)⁻¹ * (k₁ : Q)⁻¹ := by rw [key]
      _ = (b * (k₁ : Q) * b⁻¹) * (c * (k₁ : Q)⁻¹) := by group
      _ = (b * (k₁ : Q) * b⁻¹) * ((k₁ : Q)⁻¹ * c) := by rw [hk1]
      _ = (b * (k₁ : Q) * b⁻¹ * (k₁ : Q)⁻¹) * c := by group
  let φ : K →* K := MonoidHom.mk' (fun k => ⟨b * (k : Q) * b⁻¹ * (k : Q)⁻¹, hφK k k.2⟩)
    (fun k₁ k₂ => Subtype.ext (hmul k₁ k₂))
  have hker : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ φ.ker := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    have hcen : ∀ x ∈ K, x * (b * (g₁ : Q) * b⁻¹ * (g₁ : Q)⁻¹) =
        (b * (g₁ : Q) * b⁻¹ * (g₁ : Q)⁻¹) * x :=
      fun x hx => Subgroup.mem_centralizer_iff.mp (h g₁ g₁.2) x hx
    show (b * (g₁ : Q) * b⁻¹ * (g₁ : Q)⁻¹) * (b * (g₂ : Q) * b⁻¹ * (g₂ : Q)⁻¹) =
      (b * (g₂ : Q) * b⁻¹ * (g₂ : Q)⁻¹) * (b * (g₁ : Q) * b⁻¹ * (g₁ : Q)⁻¹)
    exact (hcen _ (φ g₂).2).symm
  have h1 : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := hK.commutator_eq_top
  have htop : (⊤ : Subgroup K) ≤ φ.ker := h1.symm.le.trans hker
  intro k hk
  have hk' : φ ⟨k, hk⟩ = 1 := MonoidHom.mem_ker.mp (htop (Subgroup.mem_top _))
  have hk'' : b * k * b⁻¹ * k⁻¹ = 1 := congrArg Subtype.val hk'
  have h2 : b * k * b⁻¹ = k := mul_inv_eq_one.mp hk''
  calc b * k = b * k * b⁻¹ * b := by group
    _ = k * b := by rw [h2]

end CFSG.RankThree.PartTwo.Sec18
