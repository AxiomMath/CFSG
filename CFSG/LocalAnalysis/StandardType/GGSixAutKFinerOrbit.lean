module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerFive
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

@[expose] def GGAltFiveCentreInput : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Assembly.IsQuasisimple L →
    Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) →
      ¬ 5 ∣ Nat.card (Subgroup.center L)

section Elements

theorem ggAKF_lt_five_pow {m : ℕ} (hm : 5 ≤ m) : 125 * m < 5 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h5 : 125 ≤ 5 ^ k :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 3 ≤ k by omega))
    rw [pow_succ]
    omega

theorem ggAKF_exists_orderFive_noncentral (hS : GGAltFiveCentreInput) {L : Type} [Group L]
    [Finite L] (hL : CFSG.Assembly.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) :
    ∃ z : L, orderOf z = 5 ∧ z ∉ Subgroup.center L := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hZ := hS L hL ⟨e⟩
  have h60 : 5 ∣ Nat.card (alternatingGroup (Fin 5)) := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 5 h60
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (e.symm a)
  have hlo : orderOf (l : L ⧸ Subgroup.center L) = 5 := by
    rw [hl, MulEquiv.orderOf_eq, ha]
  obtain ⟨k, r, hr, hlr⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos l).ne' 5 (by norm_num)
  have hcop : Nat.Coprime 5 r := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hr
  have hrne : r ≠ 0 := fun h => hr (h ▸ dvd_zero 5)
  set l' := l ^ r with hl'
  have hl'o : orderOf l' = 5 ^ k := by
    rw [hl', orderOf_pow_of_dvd hrne ⟨5 ^ k, by rw [hlr, mul_comm]⟩, hlr,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hrne)]
  have himg : orderOf (l' : L ⧸ Subgroup.center L) = 5 := by
    rw [hl', QuotientGroup.mk_pow, Nat.Coprime.orderOf_pow (by rw [hlo]; exact hcop), hlo]
  have hnz : l' ∉ Subgroup.center L := by
    intro h
    rw [← QuotientGroup.eq_one_iff] at h
    rw [h, orderOf_one] at himg
    norm_num at himg
  have hpow : l' ^ 5 ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← himg, pow_orderOf_eq_one]
  have hk1 : k = 1 := by
    by_contra hk1
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hl'o
      exact hnz (hl'o ▸ Subgroup.one_mem _)
    have hk2 : 2 ≤ k := by omega
    have ho : orderOf (l' ^ 5) = 5 ^ (k - 1) := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hl'o]; exact dvd_pow_self 5 hk0), hl'o]
      rw [show k = (k - 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      simp
    have hdvd : orderOf (⟨l' ^ 5, hpow⟩ : Subgroup.center L) ∣ Nat.card (Subgroup.center L) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, ho] at hdvd
    exact hZ ((dvd_pow_self 5 (by omega : k - 1 ≠ 0)).trans hdvd)
  exact ⟨l', by rw [hl'o, hk1, pow_one], hnz⟩

end Elements

section Orbit

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggAKF_le_normalizer_of_alt_five (hS : GGAltFiveCentreInput) {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {b : G} {L₁ : Subgroup G}
    (hBsel : IsElemAbelian 5 Bs) (hBsM : Bs ≤ ggM 5 B x L D J)
    (s1 : GGSixStepOne 5 B Bs x L D J) (hpair : GGStepTwoPair 5 B Bs x L D J b L₁)
    (e : ↥L₁ ⧸ Subgroup.center ↥L₁ ≃* alternatingGroup (Fin 5)) :
    Bs ≤ Subgroup.normalizer (L₁ : Set G) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_contra hnot
  obtain ⟨y, hyBs, hyN⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hL₁X : IsComponentOf L₁ (ggG0 5 B x L D J ⊓ Subgroup.centralizer {b}) := hpair.2.2.1
  have hq : CFSG.Assembly.IsQuasisimple ↥L₁ := hL₁X.2.2
  have hBs1 : Bs ≠ ⊥ := fun h => hpair.2.1 (by
    have h0 := hpair.1
    rw [h] at h0
    exact Subgroup.mem_bot.mp h0)
  have hBsNX : ∀ g ∈ Bs, g ∈ Subgroup.normalizer
      ((ggG0 5 B x L D J ⊓ Subgroup.centralizer {b} : Subgroup G) : Set G) := by
    intro g hg
    have hgb : g ∈ Subgroup.centralizer {b} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hBsel.1
      exact congrArg Subtype.val (mul_comm' (⟨g, hg⟩ : Bs) ⟨b, hpair.1⟩)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨hh0, hhC⟩ := Subgroup.mem_inf.mp hh
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hBsM hg) h).mp hh0,
        (Subgroup.centralizer {b}).mul_mem ((Subgroup.centralizer {b}).mul_mem hgb hhC)
          ((Subgroup.centralizer {b}).inv_mem hgb)⟩
    · intro hh
      obtain ⟨hh0, hhC⟩ := Subgroup.mem_inf.mp hh
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hBsM hg) h).mpr hh0, ?_⟩
      have h1 := (Subgroup.centralizer {b}).mul_mem ((Subgroup.centralizer {b}).mul_mem
        ((Subgroup.centralizer {b}).inv_mem hgb) hhC) hgb
      simpa [mul_assoc] using h1
  have hcomp : ∀ g ∈ Bs,
      IsComponentOf (conjSub g L₁) (ggG0 5 B x L D J ⊓ Subgroup.centralizer {b}) := by
    intro g hg
    have h := isComponentOf_map_conj hL₁X g
    rwa [show (ggG0 5 B x L D J ⊓ Subgroup.centralizer {b}).map (MulAut.conj g).toMonoidHom =
      ggG0 5 B x L D J ⊓ Subgroup.centralizer {b} from
        conjSub_eq_of_mem_normalizer (hBsNX g hg)] at h
  have hfeq : ∀ g ∈ Bs, ∀ g' ∈ Bs, conjSub g L₁ = conjSub g' L₁ →
      g⁻¹ * g' ∈ Subgroup.normalizer (L₁ : Set G) := by
    intro g _ g' _ h
    refine mem_normalizer_of_conjSub_le (le_of_eq ?_) (le_of_eq ?_)
    · rw [conjSub_mul, ← h, conjSub_inv_conjSub]
    · rw [mul_inv_rev, inv_inv, conjSub_mul, h, conjSub_inv_conjSub]
  let f : ↥Bs → Subgroup G := fun g => conjSub (g : G) L₁
  have : Finite (Set.range f) := (Set.finite_range f).to_subtype
  let _ : Fintype (Set.range f) := Fintype.ofFinite _
  have : Nonempty ↥Bs := ⟨1⟩
  let rep : Subgroup G → G := fun K => ((Function.invFun f K : ↥Bs) : G)
  have hrepB : ∀ g : ↥Bs, rep (f g) ∈ Bs := fun g => (Function.invFun f (f g)).2
  have hrepf : ∀ g : ↥Bs, conjSub (rep (f g)) L₁ = f g := fun g =>
    Function.invFun_eq (⟨g, rfl⟩ : ∃ g' : ↥Bs, f g' = f g)
  have hK : ∀ K : Set.range f, rep K ∈ Bs ∧ conjSub (rep K) L₁ = K := by
    rintro ⟨_, g, rfl⟩
    exact ⟨hrepB g, hrepf g⟩
  have hcount : Nat.card Bs ≤
      Nat.card (Bs ⊓ Subgroup.normalizer (L₁ : Set G) : Subgroup G) * Nat.card (Set.range f) := by
    let ι : ↥Bs → ↥(Bs ⊓ Subgroup.normalizer (L₁ : Set G)) × Set.range f := fun g =>
      (⟨(rep (f g))⁻¹ * g, Subgroup.mem_inf.mpr ⟨Bs.mul_mem (Bs.inv_mem (hrepB g)) g.2,
        hfeq _ (hrepB g) _ g.2 (hrepf g)⟩⟩, ⟨f g, g, rfl⟩)
    have hι : Function.Injective ι := by
      intro g₁ g₂ h
      have h2 : conjSub (g₁ : G) L₁ = conjSub (g₂ : G) L₁ :=
        congrArg (fun q : ↥(Bs ⊓ Subgroup.normalizer (L₁ : Set G)) × Set.range f =>
          (q.2 : Subgroup G)) h
      have h1 : (rep (conjSub (g₁ : G) L₁))⁻¹ * (g₁ : G) =
          (rep (conjSub (g₂ : G) L₁))⁻¹ * (g₂ : G) :=
        congrArg (fun q : ↥(Bs ⊓ Subgroup.normalizer (L₁ : Set G)) × Set.range f =>
          ((q.1 : ↥(Bs ⊓ Subgroup.normalizer (L₁ : Set G))) : G)) h
      rw [h2] at h1
      exact Subtype.ext (mul_left_cancel h1)
    calc Nat.card Bs ≤ Nat.card (↥(Bs ⊓ Subgroup.normalizer (L₁ : Set G)) × Set.range f) :=
          Nat.card_le_card_of_injective ι hι
      _ = _ := Nat.card_prod _ _
  have hy1 : y ≠ 1 := fun h => hyN (h ▸ Subgroup.one_mem _)
  have hyo : orderOf y = 5 := orderOf_eq_prime (hBsel.2 y hyBs) hy1
  have hpowmem : ∀ d : ℕ, 0 < d → d < 5 → y ^ d ∈ Subgroup.normalizer (L₁ : Set G) → False := by
    intro d hd0 hd5 hd
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := y) (n := d)
      (by rw [hyo]; exact (Nat.coprime_of_lt_prime hd0.ne' hd5 (by norm_num)).symm)
    exact hyN (hm ▸ Subgroup.pow_mem _ hd m)
  have hO5 : 5 ≤ Nat.card (Set.range f) := by
    let τ : Fin 5 → Set.range f := fun i => ⟨f ⟨y ^ (i : ℕ), Bs.pow_mem hyBs _⟩, _, rfl⟩
    have hτ : Function.Injective τ := by
      intro i j hij
      have h : conjSub (y ^ (i : ℕ)) L₁ = conjSub (y ^ (j : ℕ)) L₁ := congrArg Subtype.val hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hle : (i : ℕ) ≤ j := le_of_lt hlt
        have hmem := hfeq _ (Bs.pow_mem hyBs i) _ (Bs.pow_mem hyBs j) h
        rw [show (y ^ (i : ℕ))⁻¹ * y ^ (j : ℕ) = y ^ ((j : ℕ) - i) by
          rw [inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hle]] at hmem
        exact hpowmem _ (by omega) (by omega) hmem
      · have hle : (j : ℕ) ≤ i := le_of_lt hlt
        have hmem := hfeq _ (Bs.pow_mem hyBs j) _ (Bs.pow_mem hyBs i) h.symm
        rw [show (y ^ (j : ℕ))⁻¹ * y ^ (i : ℕ) = y ^ ((i : ℕ) - j) by
          rw [inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hle]] at hmem
        exact hpowmem _ (by omega) (by omega) hmem
    have h5 := Nat.card_le_card_of_injective τ hτ
    rwa [Nat.card_fin] at h5
  have hN : Nat.card (Bs ⊓ Subgroup.normalizer (L₁ : Set G) : Subgroup G) ≤ 125 := by
    have hNp : IsPGroup 5 (Bs ⊓ Subgroup.normalizer (L₁ : Set G) : Subgroup G) := fun g =>
      ⟨1, Subtype.ext (by simpa using hBsel.2 g (Subgroup.mem_inf.mp g.2).1)⟩
    have h1 := ggAKF_card_le_five_mul hNp inf_le_right hq.1 e
    have h3 : (Bs ⊓ Subgroup.normalizer (L₁ : Set G)) ⊓ Subgroup.centralizer (L₁ : Set G) ≤
        Bs ⊓ Subgroup.centralizer (L₁ : Set G) := inf_le_inf_right _ inf_le_left
    have h4 : Nat.card ((Bs ⊓ Subgroup.normalizer (L₁ : Set G)) ⊓
        Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ 25 :=
      ((Subgroup.card_le_of_le h3).trans hpair.2.2.2).trans (by norm_num)
    omega
  obtain ⟨z, hz5, hzZ⟩ := ggAKF_exists_orderFive_noncentral hS hq e
  obtain ⟨l₀, hl₀⟩ := not_forall.mp (fun h => hzZ (Subgroup.mem_center_iff.mpr h))
  let zK : Set.range f → G := fun K => rep K * (z : G) * (rep K)⁻¹
  have hF1 : ∀ K : Set.range f, zK K ∈ (K : Subgroup G) := fun K => by
    have hmem : zK K ∈ conjSub (rep K) L₁ := ⟨(z : G), z.2, by simp [zK, MulAut.conj_apply]⟩
    exact (hK K).2.le hmem
  have hF2 : ∀ K : Set.range f, orderOf (zK K) = 5 := fun K => by
    have h := MulEquiv.orderOf_eq (MulAut.conj (rep K)) (z : G)
    rw [MulAut.conj_apply, Subgroup.orderOf_coe, hz5] at h
    exact h
  have hF3 : ∀ K : Set.range f, ∃ k ∈ (K : Subgroup G), k * zK K ≠ zK K * k := fun K => by
    refine ⟨rep K * (l₀ : G) * (rep K)⁻¹, ?_, fun h => hl₀ ?_⟩
    · have hmem : rep K * (l₀ : G) * (rep K)⁻¹ ∈ conjSub (rep K) L₁ :=
        ⟨(l₀ : G), l₀.2, by simp [MulAut.conj_apply]⟩
      exact (hK K).2.le hmem
    · apply Subtype.ext
      have h' : rep K * ((l₀ : G) * z) * (rep K)⁻¹ = rep K * ((z : G) * l₀) * (rep K)⁻¹ := by
        simp only [zK] at h
        calc rep K * ((l₀ : G) * z) * (rep K)⁻¹
            = rep K * (l₀ : G) * (rep K)⁻¹ * (rep K * (z : G) * (rep K)⁻¹) := by group
          _ = rep K * (z : G) * (rep K)⁻¹ * (rep K * (l₀ : G) * (rep K)⁻¹) := h
          _ = rep K * ((z : G) * l₀) * (rep K)⁻¹ := by group
      have h'' := mul_left_cancel (mul_right_cancel h')
      simpa using h''
  have hF4 : ∀ K : Set.range f,
      IsComponentOf (K : Subgroup G) (ggG0 5 B x L D J ⊓ Subgroup.centralizer {b}) := fun K =>
    (hK K).2 ▸ hcomp _ (hK K).1
  have hF5 : ∀ K K' : Set.range f, K ≠ K' → ⁅(K : Subgroup G), (K' : Subgroup G)⁆ = ⊥ := by
    intro K K' hne
    rcases isComponentOf_eq_or_commute (hF4 K) (hF4 K') with h | h
    · exact absurd (Subtype.ext h) hne
    · exact h
  let H : Set.range f → Subgroup G := fun K => Subgroup.zpowers (zK K)
  have hHK : ∀ K, H K ≤ (K : Subgroup G) := fun K => Subgroup.zpowers_le.mpr (hF1 K)
  have hcomm : Pairwise fun K K' : Set.range f => ∀ a c : G, a ∈ H K → c ∈ H K' →
      Commute a c := by
    intro K K' hne a c ha hc
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hF5 K K' hne)
    exact (Subgroup.mem_centralizer_iff.mp (hle (hHK K ha)) c (hHK K' hc)).symm
  have hind : iSupIndep H := by
    intro K
    rw [Subgroup.disjoint_def]
    intro w hw hw'
    have hle : (⨆ (j : Set.range f) (_ : j ≠ K), H j) ≤
        Subgroup.centralizer ((K : Subgroup G) : Set G) := by
      refine iSup₂_le fun j hj => ?_
      exact (hHK j).trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hF5 j K hj))
    have hwC := hle hw'
    by_contra hw1
    have hwo : orderOf w = 5 := by
      have hd := orderOf_dvd_of_mem_zpowers hw
      rw [hF2 K] at hd
      rcases (Nat.dvd_prime (by norm_num)).mp hd with h1 | h5
      · exact absurd (orderOf_eq_one_iff.mp h1) hw1
      · exact h5
    have hzw : zK K ∈ Subgroup.zpowers w := by
      have heq := Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hwo, hF2 K])
      rw [heq]
      exact Subgroup.mem_zpowers _
    have hzC : zK K ∈ Subgroup.centralizer ((K : Subgroup G) : Set G) :=
      (Subgroup.zpowers_le.mpr hwC) hzw
    obtain ⟨k, hk, hne⟩ := hF3 K
    exact hne (Subgroup.mem_centralizer_iff.mp hzC k hk)
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have hcardE : Nat.card (Subgroup.noncommPiCoprod hcomm).range =
      5 ^ Nat.card (Set.range f) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]
    simp only [H, Nat.card_zpowers, hF2]
    rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have hEM : (Subgroup.noncommPiCoprod hcomm).range ≤ ggM 5 B x L D J := by
    rw [Subgroup.noncommPiCoprod_range]
    exact iSup_le fun K => (hHK K).trans ((hF4 K).1.trans (inf_le_left.trans
      Subgroup.le_normalizer))
  have hEel : IsElemAbelian 5 (Subgroup.noncommPiCoprod hcomm).range := by
    have hpi : ∀ u v : (∀ K : Set.range f, ↥(H K)), u * v = v * u := fun u v => by
      funext K
      apply Subtype.ext
      obtain ⟨k₁, hk₁⟩ := Subgroup.mem_zpowers_iff.mp (u K).2
      obtain ⟨k₂, hk₂⟩ := Subgroup.mem_zpowers_iff.mp (v K).2
      show ((u K : G)) * (v K : G) = (v K : G) * (u K : G)
      rw [← hk₁, ← hk₂, ← zpow_add, ← zpow_add, add_comm]
    refine ⟨⟨⟨fun a c => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨u, hu⟩ := a.2
      obtain ⟨v, hv⟩ := c.2
      apply Subtype.ext
      show (a : G) * c = c * a
      rw [← hu, ← hv, ← map_mul, ← map_mul, hpi]
    · obtain ⟨u, rfl⟩ := ha
      have hu5 : u ^ 5 = 1 := by
        funext K
        apply Subtype.ext
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (u K).2
        show ((u K : G)) ^ 5 = 1
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hF2 K,
          pow_orderOf_eq_one, one_zpow]
      rw [← map_pow, hu5, map_one]
  have hle := ggAKF_card_le_card_bstar (by norm_num) hBsel hBs1 s1 hEel hEM
  rw [hcardE] at hle
  have hfin := hle.trans (hcount.trans (Nat.mul_le_mul_right _ hN))
  exact absurd hfin (not_le.mpr (ggAKF_lt_five_pow hO5))

end Orbit

section Input

theorem ggStepTwoBstarNormFiveInput_of_schur (hS : GGAltFiveCentreInput) :
    GGStepTwoBstarNormFiveInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 b L₁ hpair hp5 he
  subst hp5
  obtain ⟨e⟩ := he
  exact ggAKF_le_normalizer_of_alt_five hS hctx.bstar.2.1 hctx.bstar_le_normalizer s1 hpair e

theorem ggStepTwoAutKFiveInput_of_schur (hS : GGAltFiveCentreInput) (hF : GGSixFieldFiveInput)
    (hD : GGLayerNotDFourTwoInput) : GGStepTwoAutKFiveInput :=
  ggStepTwoAutKFiveInput_of_finer (ggStepTwoBstarNormFiveInput_of_schur hS) hF hD

end Input

end CFSG.StandardType
