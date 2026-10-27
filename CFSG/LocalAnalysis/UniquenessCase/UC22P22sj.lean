module

public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.Quasithin.Background.C118NoOuterAlg
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sc
import CFSG.RankThree.PartOne.KFCL.L4Block
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement Pointwise

namespace P22sj

theorem comm_mul_central {Q : Type*} [Group Q] {a b c d : Q} (hc : c ∈ center Q) (hd : d ∈ center Q) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hc' := mem_center_iff.1 hc
  have hd' := mem_center_iff.1 hd
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
      = a * (c * (b * d)) * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹) := by group
    _ = a * ((b * d) * c) * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹) := by rw [hc' (b * d)]
    _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [hd' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem le_center_of_quasisimple {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) {N : Subgroup Q}
    (hN : N.Normal) (hne : N ≠ ⊤) : N ≤ center Q := by
  obtain ⟨hcomm, hsimp⟩ := hQ
  haveI := hsimp
  haveI hmap : (N.map (QuotientGroup.mk' (center Q))).Normal := hN.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center Q))) with hbot | htop
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  · exfalso
    apply hne
    have hdec : ∀ x : Q, ∃ n ∈ N, n⁻¹ * x ∈ center Q := by
      intro x
      have hx : QuotientGroup.mk' (center Q) x ∈ N.map (QuotientGroup.mk' (center Q)) := by
        rw [htop]
        trivial
      obtain ⟨n, hn, hnx⟩ := hx
      refine ⟨n, hn, ?_⟩
      rw [← QuotientGroup.ker_mk' (center Q), MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel]
    rw [eq_top_iff, ← hcomm, _root_.commutator_def, commutator_le]
    intro x _ y _
    obtain ⟨n, hn, hnx⟩ := hdec x
    obtain ⟨m, hm, hmy⟩ := hdec y
    have hx : x = n * (n⁻¹ * x) := by group
    have hy : y = m * (m⁻¹ * y) := by group
    rw [hx, hy, comm_mul_central hnx hmy, commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn hm) (N.inv_mem hn)) (N.inv_mem hm)

theorem not_isPGroup_sl2 {F : Type} [Field F] [Fintype F] {e : ℕ} (hF : Fintype.card F = 2 ^ e) (he : 2 ≤ e) :
    ¬ IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← CFSG.Open.StatedAPI.card_statedSL 2 F, CFSG.Open.StatedAPI.card_statedSL_two]
  rw [hm, Nat.card_eq_fintype_card, hF] at hcard
  have hdvd : (2 ^ e) ^ 2 - 1 ∣ 2 ^ m := Dvd.intro_left _ hcard.symm
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have h4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ e = 2 * r := ⟨2 ^ (e - 1), by rw [← pow_succ']; congr 1; omega⟩
  have hsq : (2 ^ e) ^ 2 = 4 * (r * r) := by rw [hr]; ring
  have hr2 : 2 ≤ r := by omega
  have hrr : 4 ≤ r * r := by nlinarith
  generalize r * r = t at hsq hrr
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · rw [hj0, pow_zero, hsq] at hj
    omega
  · have h2j : 2 ^ j = 2 * 2 ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
    rw [h2j, hsq] at hj
    generalize 2 ^ (j - 1) = w at hj
    omega

variable {G : Type} [Group G]

@[expose] noncomputable def act {H W₁ : Subgroup G} (h : H ≤ normalizer (W₁ : Set G)) : ↥H →* MulAut ↥W₁ :=
  W₁.normalizerMonoidHom.comp (Subgroup.inclusion h)

theorem act_coe {H W₁ : Subgroup G} (h : H ≤ normalizer (W₁ : Set G)) (g : ↥H) (u : ↥W₁) :
    ((act h g u : ↥W₁) : G) = (g : G) * u * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

end P22sj

open P22sj

theorem uc22p22sj_inClassG {G : Type} [Group G] [Finite G] {S L W₁ W₀ : Subgroup G}
    {F : Type} [Field F] [Fintype F] {e : ℕ} (hF : Fintype.card F = 2 ^ e) (he : 2 ≤ e)
    (hS : IsPGroup 2 S) (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hsyl : ¬ 2 ∣ S.relIndex (L ⊔ S))
    (hchar : (L ⊔ S) ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 (L ⊔ S) : Set G) ≤
      CFSG.Open.pCoreOf 2 (L ⊔ S))
    (hLp : ⁅L, L⁆ = L) (hLq : CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hSW₁ : S ≤ Subgroup.normalizer (W₁ : Set G)) (hSW₀ : S ≤ Subgroup.normalizer (W₀ : Set G))
    (hLW₁ : L ≤ Subgroup.normalizer (W₁ : Set G))
    (α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (β : ↥W₁ →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβker : β.ker = W₀.subgroupOf W₁)
    (hβα : ∀ (l : ↥L) (u v : ↥W₁), (v : G) = l * u * l⁻¹ →
      Multiplicative.toAdd (β v) = (α l : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hinn : ∀ b ∈ S, ∃ l ∈ L, ∀ u v : ↥W₁, (v : G) = (l⁻¹ * b) * u * (l⁻¹ * b)⁻¹ → β v = β u) :
    CFSG.RankThree.PartOne.InClassG ↥S ↥(L ⊔ S) (Subgroup.inclusion le_sup_right) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchp : CharP F 2 := charP_of_card_eq_prime_pow hF
  have h4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  haveI hsimpleSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup h4
  set H : Subgroup G := L ⊔ S with hHdef
  have hLH : L ≤ H := le_sup_left
  have hSH : S ≤ H := le_sup_right
  have hHL : H ≤ normalizer (L : Set G) := sup_le le_normalizer hSL
  have hHW₁ : H ≤ normalizer (W₁ : Set G) := sup_le hLW₁ hSW₁
  have hLW01 : L ≤ normalizer ((W₀ ⊓ W₁ : Subgroup G) : Set G) := by
    rw [le_normalizer_iff]
    intro l hl w hw
    have hw1 : l * w * l⁻¹ ∈ W₁ := (mem_normalizer_iff.mp (hLW₁ hl) w).mp hw.2
    have h1 : (⟨w, hw.2⟩ : ↥W₁) ∈ β.ker := by rw [hβker, mem_subgroupOf]; exact hw.1
    have h2 : Multiplicative.toAdd (β ⟨_, hw1⟩) = 0 := by
      rw [hβα ⟨l, hl⟩ ⟨w, hw.2⟩ ⟨_, hw1⟩ rfl, MonoidHom.mem_ker.mp h1]
      simp
    have h3 : (⟨_, hw1⟩ : ↥W₁) ∈ β.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective (h2.trans rfl)
    rw [hβker, mem_subgroupOf] at h3
    exact ⟨h3, hw1⟩
  have hSW01 : S ≤ normalizer ((W₀ ⊓ W₁ : Subgroup G) : Set G) := by
    rw [le_normalizer_iff]
    intro s hs w hw
    exact ⟨(mem_normalizer_iff.mp (hSW₀ hs) w).mp hw.1, (mem_normalizer_iff.mp (hSW₁ hs) w).mp hw.2⟩
  have hHW01 : H ≤ normalizer ((W₀ ⊓ W₁ : Subgroup G) : Set G) := sup_le hLW01 hSW01
  have hcongr : ∀ (g : ↥H) (u v : ↥W₁), β u = β v → β (act hHW₁ g u) = β (act hHW₁ g v) := by
    intro g u v huv
    have h1 : u⁻¹ * v ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
    rw [hβker, mem_subgroupOf] at h1
    have h2 : (act hHW₁ g u)⁻¹ * (act hHW₁ g v) ∈ β.ker := by
      rw [hβker, mem_subgroupOf]
      have h3 := (mem_normalizer_iff.mp (hHW01 g.2) ((u⁻¹ * v : ↥W₁) : G)).mp ⟨h1, (u⁻¹ * v).2⟩
      have e : (act hHW₁ g u)⁻¹ * (act hHW₁ g v) = act hHW₁ g (u⁻¹ * v) := by
        simp [map_mul, map_inv]
      rw [e, act_coe hHW₁ g (u⁻¹ * v)]
      exact h3.1
    rw [MonoidHom.mem_ker, map_mul, map_inv] at h2
    exact inv_mul_eq_one.mp h2
  obtain ⟨ρ, hadd, hact⟩ := exists_perm_action (act hHW₁) β hβ hcongr
  have hρL : ∀ l : ↥L, ρ ⟨(l : G), hLH l.2⟩ = slPerm F (α l) := by
    intro l
    refine Equiv.ext fun x => ?_
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd x)
    have hux : Multiplicative.toAdd (β u) = x := by rw [hu]; rfl
    rw [← hux, hact, slPerm_apply, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
    exact hβα l u _ (act_coe hHW₁ _ u)
  have hρS : ∀ s : ↥H, (s : G) ∈ S → ∃ l : ↥L, ρ s = slPerm F (α l) := by
    intro s hs
    obtain ⟨l, hl, hls⟩ := hinn (s : G) hs
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [← hρL]
    have h1 : ρ ((⟨l, hLH hl⟩ : ↥H)⁻¹ * s) = 1 := by
      refine Equiv.ext fun x => ?_
      obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd x)
      have hux : Multiplicative.toAdd (β u) = x := by rw [hu]; rfl
      rw [← hux, hact, Equiv.Perm.one_apply]
      congr 1
      refine hls u _ ?_
      rw [act_coe]
      simp
    have h2 : s = (⟨l, hLH hl⟩ : ↥H) * ((⟨l, hLH hl⟩ : ↥H)⁻¹ * s) := by group
    rw [h2, map_mul, h1, mul_one]
  have hslinj : Function.Injective (slPerm F) := by
    rw [injective_iff_map_eq_one]
    intro A hA
    exact eq_one_of_forall_smul_vec fun w => by
      have := congrArg (fun g : Equiv.Perm (Fin 2 → F) => g w) hA
      simpa [slPerm_apply] using this
  set L' : Subgroup ↥H := L.subgroupOf H with hL'def
  set S' : Subgroup ↥H := S.subgroupOf H with hS'def
  have htop : L' ⊔ S' = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLH, Subgroup.map_subgroupOf_eq_of_le hSH,
      Subgroup.map_top, Subgroup.range_subtype]
  have hrange : ∀ h : ↥H, ρ h ∈ (slPerm F).range := by
    let P : Subgroup ↥H := (slPerm F).range.comap ρ
    have hLP : L' ≤ P := fun h hh => ⟨α ⟨(h : G), hh⟩, (hρL ⟨(h : G), hh⟩).symm⟩
    have hSP : S' ≤ P := fun h hh => by
      obtain ⟨l, hl⟩ := hρS h hh
      exact ⟨α l, hl.symm⟩
    intro h
    have : h ∈ P := (sup_le hLP hSP) (htop ▸ Subgroup.mem_top h)
    exact this
  let eSL : Matrix.SpecialLinearGroup (Fin 2) F ≃* (slPerm F).range := MonoidHom.ofInjective hslinj
  let φ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) F :=
    eSL.symm.toMonoidHom.comp (ρ.codRestrict (slPerm F).range hrange)
  have hφρ : ∀ h : ↥H, slPerm F (φ h) = ρ h := by
    intro h
    have h1 : eSL (φ h) = ρ.codRestrict (slPerm F).range hrange h := by
      show eSL (eSL.symm _) = _
      rw [MulEquiv.apply_symm_apply]
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hφL : ∀ l : ↥L, φ ⟨(l : G), hLH l.2⟩ = α l := fun l =>
    hslinj ((hφρ _).trans (hρL l))
  have hφs : Function.Surjective φ := by
    intro A
    obtain ⟨l, rfl⟩ := hα A
    exact ⟨_, hφL l⟩
  haveI hL'n : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHL
  have hS'2 : IsPGroup 2 S' := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  have hquot : IsPGroup 2 (↥H ⧸ L') := by
    have hmap : S'.map (QuotientGroup.mk' L') = ⊤ := by
      have h1 := congrArg (Subgroup.map (QuotientGroup.mk' L')) htop
      rw [Subgroup.map_sup, Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective L')] at h1
      have h2 : L'.map (QuotientGroup.mk' L') = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      rw [h2, bot_sup_eq] at h1
      exact h1
    have h3 : IsPGroup 2 (S'.map (QuotientGroup.mk' L')) := hS'2.map _
    rw [hmap] at h3
    exact h3.of_equiv Subgroup.topEquiv
  have hpow : ∀ h : ↥H, ∃ k : ℕ, h ^ (2 ^ k) ∈ L' := by
    intro h
    obtain ⟨k, hk⟩ := hquot (QuotientGroup.mk' L' h)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.ker_mk' L', MonoidHom.mem_ker, map_pow]
    exact hk
  set Q' : Subgroup ↥H := (CFSG.pCore 2 ↥L).map (Subgroup.inclusion hLH) with hQ'def
  have hQ'2 : IsPGroup 2 Q' := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map _
  have hQ'mem : ∀ x : ↥H, (x : G) ∈ CFSG.Open.pCoreOf 2 L → x ∈ Q' := by
    rintro x ⟨q, hq, hqx⟩
    exact ⟨q, hq, Subtype.ext hqx⟩
  haveI hQ'n : Q'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hn
    have hgN := UC6S846.normalizer_le_normalizer_pCoreOf L (hHL g.2)
    have h1 : (g : G) * ((q : ↥L) : G) * (g : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
      (mem_normalizer_iff.mp hgN _).mp ⟨q, hq, rfl⟩
    exact hQ'mem _ h1
  have hQ'H : Q' ≤ CFSG.pCore 2 ↥H := CFSG.LieType.BorelTits.le_pCore 2 hQ'n hQ'2
  have hQα : CFSG.pCore 2 ↥L ≤ α.ker := by
    haveI hn : ((CFSG.pCore 2 ↥L).map α).Normal := Subgroup.Normal.map inferInstance α hα
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥L).map α) with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).1 hb
    · exfalso
      have hp : IsPGroup 2 ((CFSG.pCore 2 ↥L).map α) := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map α
      rw [ht] at hp
      exact not_isPGroup_sl2 hF he (hp.of_equiv Subgroup.topEquiv)
  have hcent : ∀ z : ↥L, α z = 1 →
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) z ∈ center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro z hz
    have hNn : (α.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    have hNne : α.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≠ ⊤ := by
      intro hN
      have h1 := congrArg (Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) hN
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hQα, Subgroup.comap_top] at h1
      obtain ⟨A, hA⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin 2) F)
      obtain ⟨l, rfl⟩ := hα A
      exact hA (MonoidHom.mem_ker.1 (h1 ▸ Subgroup.mem_top l))
    exact le_center_of_quasisimple hLq hNn hNne ⟨z, MonoidHom.mem_ker.2 hz, rfl⟩
  have hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = (⊤ : Subgroup ↥L) := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hLp]
  have hcommQ : ∀ k ∈ φ.ker, ∀ l ∈ L', k * l * k⁻¹ * l⁻¹ ∈ Q' := by
    intro k hk lH hlH
    have hcL : ∀ l : ↥L, ((k * ⟨(l : G), hLH l.2⟩ * k⁻¹ * (⟨(l : G), hLH l.2⟩ : ↥H)⁻¹ : ↥H) : G) ∈ L := by
      intro l
      have h1 : k * ⟨(l : G), hLH l.2⟩ * k⁻¹ ∈ L' := hL'n.conj_mem _ l.2 k
      exact L'.mul_mem h1 (L'.inv_mem l.2)
    let c : ↥L → ↥L := fun l => ⟨_, hcL l⟩
    have hcα : ∀ l, α (c l) = 1 := by
      intro l
      rw [← hφL (c l)]
      have e1 : (⟨((c l : ↥L) : G), hLH (c l).2⟩ : ↥H) =
          k * ⟨(l : G), hLH l.2⟩ * k⁻¹ * (⟨(l : G), hLH l.2⟩ : ↥H)⁻¹ := Subtype.ext rfl
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, MonoidHom.mem_ker.1 hk]
      group
    set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπdef
    have hcmul : ∀ l₁ l₂ : ↥L, c (l₁ * l₂) = c l₁ * (l₁ * c l₂ * l₁⁻¹) := by
      intro l₁ l₂
      apply Subtype.ext
      show (k : G) * ((l₁ : G) * l₂) * (k : G)⁻¹ * ((l₁ : G) * l₂)⁻¹ =
        ((k : G) * l₁ * (k : G)⁻¹ * (l₁ : G)⁻¹) * ((l₁ : G) * ((k : G) * l₂ * (k : G)⁻¹ * (l₂ : G)⁻¹) *
          (l₁ : G)⁻¹)
      group
    let f : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) :=
      { toFun := fun l => π (c l)
        map_one' := by
          show π (c 1) = 1
          have : c 1 = 1 := Subtype.ext (by
            show (k : G) * ((1 : ↥L) : G) * (k : G)⁻¹ * ((1 : ↥L) : G)⁻¹ = ((1 : ↥L) : G)
            simp)
          rw [this, map_one]
        map_mul' := fun l₁ l₂ => by
          show π (c (l₁ * l₂)) = π (c l₁) * π (c l₂)
          have hz := mem_center_iff.1 (hcent (c l₂) (hcα l₂))
          rw [hcmul, map_mul, map_mul, map_mul, map_inv, hz (π l₁)]
          group }
    have hfker : f.ker = ⊤ := by
      rw [eq_top_iff, ← hperf, commutator_le]
      intro x _ y _
      have hz := mem_center_iff.1 (hcent (c x) (hcα x))
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
      show π (c x) * π (c y) * (π (c x))⁻¹ * (π (c y))⁻¹ = 1
      rw [← hz (π (c y))]
      group
    have h1 : f ⟨(lH : G), hlH⟩ = 1 := MonoidHom.mem_ker.1 (hfker ▸ Subgroup.mem_top _)
    have h2 : c ⟨(lH : G), hlH⟩ ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L)]
      exact h1
    refine hQ'mem _ ⟨_, h2, ?_⟩
    rfl
  refine ⟨Subgroup.inclusion_injective hSH, ?_, ?_, ?_⟩
  · refine ⟨le_top, ?_, ?_⟩
    · rw [Subgroup.inclusion_range]
      exact hS'2
    · rw [Subgroup.inclusion_range, Subgroup.relIndex_top_right]
      exact hsyl
  · refine (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥H 2).1 ?_
    intro x hx
    have hxG : (x : G) ∈ H ⊓ centralizer (CFSG.Open.pCoreOf 2 H : Set G) := by
      refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.1 hx) y hy)
    obtain ⟨y, hy, hyx⟩ := hchar hxG
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · have hL2 : IsL2Ev (↥H ⧸ φ.ker) e :=
      ⟨F, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hF],
        ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφs).trans
          (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 2 F).symm⟩⟩
    obtain ⟨eq⟩ := P22s.exists_mulEquiv_projSL hL2 (by omega)
    refine ⟨e, by omega, φ.ker, inferInstance, ⟨eq⟩, ?_⟩
    intro Y hY hYK hQY
    have hYφ : Y.map φ = ⊤ := by
      have h1 := congrArg (Subgroup.map φ) hYK
      rw [Subgroup.map_sup, Subgroup.map_top, MonoidHom.range_eq_top.mpr hφs] at h1
      have h2 : φ.ker.map φ = ⊥ := by rw [Subgroup.map_eq_bot_iff]
      rw [h2, sup_bot_eq] at h1
      exact h1
    have hYLφ : (Y ⊓ L').map φ = ⊤ := by
      haveI hn : ((Y ⊓ L').map φ).Normal := ⟨fun n hn g => by
        obtain ⟨x, hx, rfl⟩ := hn
        have hg : g ∈ Y.map φ := hYφ ▸ Subgroup.mem_top g
        obtain ⟨y, hy, rfl⟩ := hg
        refine ⟨y * x * y⁻¹, ⟨Y.mul_mem (Y.mul_mem hy hx.1) (Y.inv_mem hy), hL'n.conj_mem x hx.2 y⟩, ?_⟩
        simp [map_mul, map_inv]⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Y ⊓ L').map φ) with hb | ht
      · exfalso
        apply not_isPGroup_sl2 hF he
        intro A
        have hA : A ∈ Y.map φ := hYφ ▸ Subgroup.mem_top A
        obtain ⟨y, hy, rfl⟩ := hA
        obtain ⟨k, hk⟩ := hpow y
        refine ⟨k, ?_⟩
        have h1 : y ^ (2 ^ k) ∈ Y ⊓ L' := ⟨Y.pow_mem hy _, hk⟩
        have h2 : φ (y ^ (2 ^ k)) ∈ (Y ⊓ L').map φ := ⟨_, h1, rfl⟩
        rw [hb, Subgroup.mem_bot, map_pow] at h2
        exact h2
      · exact ht
    have hdecomp : ∀ l : ↥L, ∃ a : ↥L, (⟨(a : G), hLH a.2⟩ : ↥H) ∈ Y ∧ α (a⁻¹ * l) = 1 := by
      intro l
      have hl : φ ⟨(l : G), hLH l.2⟩ ∈ (Y ⊓ L').map φ := hYLφ ▸ Subgroup.mem_top _
      obtain ⟨y, ⟨hyY, hyL⟩, hyl⟩ := hl
      refine ⟨⟨(y : G), hyL⟩, hyY, ?_⟩
      rw [map_mul, map_inv, ← hφL, ← hφL]
      show (φ y)⁻¹ * φ ⟨(l : G), hLH l.2⟩ = 1
      rw [hyl, inv_mul_cancel]
    have hLYG : L ≤ Y.map H.subtype := by
      rw [← hLp, commutator_le]
      intro g₁ hg₁ g₂ hg₂
      obtain ⟨a₁, ha₁Y, ha₁⟩ := hdecomp ⟨g₁, hg₁⟩
      obtain ⟨a₂, ha₂Y, ha₂⟩ := hdecomp ⟨g₂, hg₂⟩
      have hz₁ := hcent _ ha₁
      have hz₂ := hcent _ ha₂
      have hπ : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⁅(⟨g₁, hg₁⟩ : ↥L), ⟨g₂, hg₂⟩⁆ =
          QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⁅a₁, a₂⁆ := by
        obtain ⟨b₁, hb₁⟩ : ∃ b₁ : ↥L, b₁ = a₁⁻¹ * ⟨g₁, hg₁⟩ := ⟨_, rfl⟩
        obtain ⟨b₂, hb₂⟩ : ∃ b₂ : ↥L, b₂ = a₂⁻¹ * ⟨g₂, hg₂⟩ := ⟨_, rfl⟩
        have e1 : (⟨g₁, hg₁⟩ : ↥L) = a₁ * b₁ := by rw [hb₁]; group
        have e2 : (⟨g₂, hg₂⟩ : ↥L) = a₂ * b₂ := by rw [hb₂]; group
        rw [← hb₁] at hz₁
        rw [← hb₂] at hz₂
        rw [e1, e2, map_commutatorElement, map_mul, map_mul, comm_mul_central hz₁ hz₂,
          map_commutatorElement]
      have hq : ⁅a₁, a₂⁆⁻¹ * ⁅(⟨g₁, hg₁⟩ : ↥L), ⟨g₂, hg₂⟩⁆ ∈ CFSG.pCore 2 ↥L := by
        rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L), MonoidHom.mem_ker, map_mul, map_inv, hπ,
          inv_mul_cancel]
      have hqY : Subgroup.inclusion hLH (⁅a₁, a₂⁆⁻¹ * ⁅(⟨g₁, hg₁⟩ : ↥L), ⟨g₂, hg₂⟩⁆) ∈ Y :=
        hQY (hQ'H ⟨_, hq, rfl⟩)
      have haY : Subgroup.inclusion hLH ⁅a₁, a₂⁆ ∈ Y := by
        rw [map_commutatorElement, commutatorElement_def]
        exact Y.mul_mem (Y.mul_mem (Y.mul_mem ha₁Y ha₂Y) (Y.inv_mem ha₁Y)) (Y.inv_mem ha₂Y)
      refine ⟨_, Y.mul_mem haY hqY, ?_⟩
      rw [← map_mul, mul_inv_cancel_left]
      rfl
    have hLY : L' ≤ Y := by
      intro h hh
      obtain ⟨y, hy, hyh⟩ := hLYG hh
      have : y = h := Subtype.ext hyh
      rwa [← this]
    have hSK : S' ⊓ φ.ker ≤ CFSG.pCore 2 ↥H := by
      have hX2 : IsPGroup 2 ↥((S' ⊓ φ.ker) ⊔ Q') := (hS'2.to_inf_left).to_sup_of_normal_right hQ'2
      have hXn : ((S' ⊓ φ.ker) ⊔ Q').Normal := by
        rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
        refine sup_le ?_ ?_
        · rw [le_normalizer_iff]
          intro l hl x hx
          rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx
          obtain ⟨a, ha, q, hq, rfl⟩ := hx
          have h1 : l * a * l⁻¹ = a * (a⁻¹ * l * a⁻¹⁻¹ * l⁻¹) := by group
          have h2 : a⁻¹ * l * a⁻¹⁻¹ * l⁻¹ ∈ Q' := hcommQ a⁻¹ (φ.ker.inv_mem ha.2) l hl
          have h3 : l * (a * q) * l⁻¹ = (a * (a⁻¹ * l * a⁻¹⁻¹ * l⁻¹)) * (l * q * l⁻¹) := by
            rw [← h1]; group
          rw [h3]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_sup_left ha) (mem_sup_right h2))
            (mem_sup_right (hQ'n.conj_mem q hq l))
        · rw [le_normalizer_iff]
          intro s hs x hx
          rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx
          obtain ⟨a, ha, q, hq, rfl⟩ := hx
          have h3 : s * (a * q) * s⁻¹ = (s * a * s⁻¹) * (s * q * s⁻¹) := by group
          rw [h3]
          refine Subgroup.mul_mem _ (mem_sup_left ⟨?_, ?_⟩) (mem_sup_right (hQ'n.conj_mem q hq s))
          · exact S'.mul_mem (S'.mul_mem hs ha.1) (S'.inv_mem hs)
          · exact (inferInstance : φ.ker.Normal).conj_mem a ha.2 s
      exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCore 2 hXn hX2)
    have hKY : φ.ker ≤ Y := by
      have h1 : Y.relIndex φ.ker ∣ L'.relIndex φ.ker := Subgroup.relIndex_dvd_of_le_left φ.ker hLY
      have h2 : L'.relIndex φ.ker ∣ L'.index := Subgroup.relIndex_dvd_index_of_normal L' φ.ker
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hquot
      have h3 : L'.index = 2 ^ m := hm
      have h4 : Y.relIndex φ.ker ∣ (S' ⊓ φ.ker).relIndex φ.ker :=
        Subgroup.relIndex_dvd_of_le_left φ.ker (hSK.trans hQY)
      have hsylK : ¬ 2 ∣ (S' ⊓ φ.ker).relIndex φ.ker := by
        have hS'syl : CFSG.ABGLocalTools.IsSylowOf 2 S' ⊤ :=
          CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_top, hS'2, by rw [Subgroup.relIndex_top_right]; exact hsyl⟩
        have h5 := hS'syl.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top φ.ker])
        exact (CFSG.ABGLocalTools.isSylowOf_iff.1 h5).2.2
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (h1.trans (h3 ▸ h2))
      rcases j with _ | j
      · rw [pow_zero] at hj
        exact Subgroup.relIndex_eq_one.1 hj
      · exfalso
        apply hsylK
        rw [hj] at h4
        exact (dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h4
    exact hY.ne (by rw [← hYK, sup_eq_left.2 hKY])

end CFSG.LocalAnalysis.UniquenessCase.UC22
