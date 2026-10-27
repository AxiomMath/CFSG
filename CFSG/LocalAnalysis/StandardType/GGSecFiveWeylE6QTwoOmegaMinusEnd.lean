module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaMinusCard
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitaryAux
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOutOrth
import CFSG.GroupTheory.MulAutTrivialOnSubgroup
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGF4QTwoHypA
import CFSG.GroupTheory.OddAbelianInvolutionDecomp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open FrameRoute

variable {G : Type} [Group G] [Finite G]

private lemma mulAut_apply_eq_self_of_mem_three_subgroup
    {Bs : Subgroup G} {x : G} {S : Subgroup (MulAut ↥Bs)}
    (hBs : IsElemAbelian 3 Bs) (hxB : x ∈ Bs) (horderx : orderOf x = 3)
    (hS3 : IsPGroup 3 ↥S) (hStop : S ≤ ggAutomizer ⊤ Bs)
    (h : ∀ g : G, g * x * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) →
      g * x * g⁻¹ ∈ Subgroup.zpowers x) :
    ∀ φ ∈ S, φ ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBsCent : Bs ≤ Subgroup.centralizer ({x} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact IsElemAbelian.comm hBs hb hxB
  have hodd : Odd (Nat.card ↥S) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS3
    rw [hn]
    exact (by decide : Odd 3).pow
  have horderC : orderOf (⟨x, hxB⟩ : ↥Bs) = 3 :=
    (orderOf_injective Bs.subtype Bs.subtype_injective ⟨x, hxB⟩).symm.trans horderx
  have hCcard : Nat.card ↥(Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs)) = 3 := by
    rw [Nat.card_zpowers]
    exact horderC
  have hpres : ∀ φ ∈ S, Subgroup.map (φ : ↥Bs →* ↥Bs) (Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs)) =
      Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs) := by
    intro φ hφ
    have hφtop : φ ∈ ggAutomizer ⊤ Bs := hStop hφ
    obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp hφtop
    have hyC : g * x * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [← hg ⟨x, hxB⟩]
      exact hBsCent (φ ⟨x, hxB⟩).2
    have hzp : g * x * g⁻¹ ∈ Subgroup.zpowers x := h g hyC
    have hmem : φ ⟨x, hxB⟩ ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzp
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨k, Subtype.ext (by
        rw [Subgroup.coe_zpow]
        exact hk.trans (hg ⟨x, hxB⟩).symm)⟩
    rw [MonoidHom.map_zpowers]
    apply Subgroup.eq_of_le_of_card_ge
    · rwa [Subgroup.zpowers_le]
    · rw [Nat.card_zpowers, Nat.card_zpowers]
      exact le_of_eq (MulEquiv.orderOf_eq φ ⟨x, hxB⟩).symm
  intro φ hφ
  exact CFSG.MulAut.act_trivial_of_preserves_card_three hodd hCcard hpres φ hφ
    ⟨x, hxB⟩ (Subgroup.mem_zpowers _)

private lemma exists_three_pow_order_of_inducing
    {H : Subgroup G} {g : G} {φ : MulAut ↥H}
    (hg : g ∈ Subgroup.normalizer (H : Set G))
    (hφ : ∀ b : ↥H, ((φ b : ↥H) : G) = g * b * g⁻¹)
    (hφ3 : ∃ k, orderOf φ = 3 ^ k) :
    ∃ (r s b : ℕ), ¬ 3 ∣ r ∧ orderOf ((g ^ r) ^ s) = 3 ^ b ∧
      ∀ c : ↥H, ((φ c : ↥H) : G) = ((g ^ r) ^ s) * c * ((g ^ r) ^ s)⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ψ : MulAut ↥H := Subgroup.normalizerMonoidHom (H := H) ⟨g, hg⟩
  have hψ : ψ = φ := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (hφ b).symm
  obtain ⟨k, hk⟩ := hφ3
  obtain ⟨a, r, hr, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  have hrpos : 0 < r := Nat.pos_of_ne_zero fun h0 => hr (h0 ▸ dvd_zero 3)
  have hcop : Nat.Coprime r (orderOf φ) := by
    rw [hk]
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hr)).pow_right k
  have hmem : φ ∈ Subgroup.zpowers (φ ^ r) := by
    rwa [mem_zpowers_pow_iff]
  rw [mem_zpowers_iff_mem_range_orderOf] at hmem
  obtain ⟨s, -, hs⟩ := Finset.mem_image.mp hmem
  have hordpow : orderOf (g ^ r) = 3 ^ a := by
    rw [orderOf_pow, hord, Nat.gcd_eq_right (Nat.dvd_mul_left r (3 ^ a)),
      Nat.mul_div_cancel _ hrpos]
  have hdvd : orderOf ((g ^ r) ^ s) ∣ 3 ^ a := by
    rw [← hordpow]
    exact orderOf_dvd_of_mem_zpowers (Subgroup.npow_mem_zpowers (g ^ r) s)
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  refine ⟨r, s, b, hr, hb, ?_⟩
  intro c
  let ψ' : MulAut ↥H := Subgroup.normalizerMonoidHom (H := H) (⟨g, hg⟩ ^ (r * s))
  have hψ' : ψ' = φ := by
    calc ψ' = (Subgroup.normalizerMonoidHom (H := H) ⟨g, hg⟩) ^ (r * s) := map_pow _ _ _
      _ = ψ ^ (r * s) := rfl
      _ = φ ^ (r * s) := by rw [hψ]
      _ = (φ ^ r) ^ s := by rw [pow_mul]
      _ = φ := hs
  have hco := congrArg (fun f : MulAut ↥H => ((f c : ↥H) : G)) hψ'
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hco
  simpa [Subgroup.coe_pow, pow_mul] using hco.symm

private lemma le_ggAutomizer_of_three_subgroup
    {Bs L : Subgroup G} {x : G} {S : Subgroup (MulAut ↥Bs)}
    (hBs : IsElemAbelian 3 Bs) (hxB : x ∈ Bs) (horderx : orderOf x = 3)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hLN : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal)
    (hInner : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AutThreePowInner ↥L)
    (hsup : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L))
    (hS3 : IsPGroup 3 ↥S) (hStop : S ≤ ggAutomizer ⊤ Bs)
    (h : ∀ g : G, g * x * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) →
      g * x * g⁻¹ ∈ Subgroup.zpowers x) :
    S ≤ ggAutomizer L Bs := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfix := mulAut_apply_eq_self_of_mem_three_subgroup hBs hxB horderx hS3 hStop h
  have hCN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLx).mp hLN
  intro φ hφS
  obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp (hStop hφS)
  have hgx : g * x * g⁻¹ = x := by
    have h2 := hg ⟨x, hxB⟩
    rw [hfix φ hφS] at h2
    simpa using h2.symm
  have hgC : g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [hgx]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hS3 ⟨φ, hφS⟩
  have hk' : orderOf φ = 3 ^ k :=
    (orderOf_injective S.subtype S.subtype_injective ⟨φ, hφS⟩).trans hk
  obtain ⟨r, s, b, hr, hg'order, hg'ind⟩ := exists_three_pow_order_of_inducing hgN hg ⟨k, hk'⟩
  set g' : G := (g ^ r) ^ s with hg'def
  have hg'N : g' ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [hg'def]
    exact (Subgroup.normalizer (Bs : Set G)).pow_mem
      ((Subgroup.normalizer (Bs : Set G)).pow_mem hgN r) s
  have hg'C : g' ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [hg'def]
    exact (Subgroup.centralizer ({x} : Set G)).pow_mem
      ((Subgroup.centralizer ({x} : Set G)).pow_mem hgC r) s
  have hg'x : g' * x * g'⁻¹ = x := by
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg'C
    calc g' * x * g'⁻¹ = x * g' * g'⁻¹ := by rw [hcomm]
      _ = x := by group
  have hg'NL : g' ∈ Subgroup.normalizer (L : Set G) := hCN hg'C
  let ψ : MulAut ↥L := Subgroup.normalizerMonoidHom (H := L) ⟨g', hg'NL⟩
  have hψorder : ψ ^ (3 ^ b) = 1 := by
    have horder : orderOf (⟨g', hg'NL⟩ : ↥(Subgroup.normalizer (L : Set G))) = 3 ^ b :=
      (orderOf_injective (Subgroup.normalizer (L : Set G)).subtype
        (Subgroup.normalizer (L : Set G)).subtype_injective ⟨g', hg'NL⟩).symm.trans hg'order
    have h1 : (⟨g', hg'NL⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ (3 ^ b) = 1 := by
      rw [← horder]
      exact pow_orderOf_eq_one _
    rw [← map_pow, h1, map_one]
  have hiter : ∀ l : ↥L, ψ^[3 ^ b] l = l := by
    intro l
    rw [← CFSG.BenderSuzuki.External.hkt_mulAut_pow_apply_iterate ψ (3 ^ b) l, hψorder]
    rfl
  obtain ⟨a, ha⟩ := hInner ψ b hiter
  have hax : (a : G) * x * (a : G)⁻¹ = x := by
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hLx a.2)
    calc (a : G) * x * (a : G)⁻¹ = x * (a : G) * (a : G)⁻¹ := by rw [hcomm]
      _ = x := by group
  have hkey : ∀ c : ↥Bs, g' * (c : G) * g'⁻¹ = (a : G) * (c : G) * (a : G)⁻¹ := by
    intro c
    have hc : (c : G) ∈ Subgroup.zpowers x ⊔ (Bs ⊓ L) := by
      rw [← hsup]; exact c.2
    rw [Subgroup.sup_eq_closure] at hc
    let f₁ : G →* G := (MulAut.conj g').toMonoidHom
    let f₂ : G →* G := (MulAut.conj (a : G)).toMonoidHom
    have hfg : f₁ (c : G) = f₂ (c : G) := by
      refine Subgroup.closure_induction (p := fun y _ => f₁ y = f₂ y) ?_ ?_ ?_ ?_ hc
      · intro y hy
        rcases hy with hyp | hyq
        · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyp
          have h1 : f₁ x = x := by
            change g' * x * g'⁻¹ = x
            exact hg'x
          have h2 : f₂ x = x := by
            change (a : G) * x * (a : G)⁻¹ = x
            exact hax
          rw [map_zpow, map_zpow, h1, h2]
        · have h1 : g' * y * g'⁻¹ = ((ψ ⟨y, hyq.2⟩ : ↥L) : G) :=
            (Subgroup.normalizerMonoidHom_apply_apply_coe (H := L) ⟨g', hg'NL⟩
              ⟨y, hyq.2⟩).symm
          have h2 := congrArg (fun t : ↥L => (t : G)) (ha ⟨y, hyq.2⟩)
          change g' * y * g'⁻¹ = (a : G) * y * (a : G)⁻¹
          rw [h1]
          simpa using h2
      · simp [f₁, f₂]
      · intro y z hy hz hyz hzw
        rw [map_mul, map_mul, hyz, hzw]
      · intro y hy hyz
        rw [map_inv, map_inv, hyz]
    have hf₁ : f₁ (c : G) = g' * (c : G) * g'⁻¹ := rfl
    have hf₂ : f₂ (c : G) = (a : G) * (c : G) * (a : G)⁻¹ := rfl
    rw [hf₁, hf₂] at hfg
    exact hfg
  have hg'ind' : ∀ c : ↥Bs, ((φ c : ↥Bs) : G) = g' * (c : G) * g'⁻¹ := by
    intro c
    rw [hg'def]
    exact hg'ind c
  have haConj : ∀ c ∈ Bs, (a : G) * c * (a : G)⁻¹ ∈ Bs := by
    intro c hc
    rw [← hkey ⟨c, hc⟩]
    exact (Subgroup.mem_set_normalizer_iff.mp hg'N c).mp hc
  have haN : (a : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro y ⟨c, hc, rfl⟩
      simpa using haConj c hc
    · rw [Subgroup.card_map_of_injective (MulAut.conj (a : G)).injective]
  exact mem_ggAutomizer_iff.mpr ⟨(a : G), a.2, haN, fun c => (hg'ind' c).trans (hkey c)⟩

private lemma three_pow_seven_dvd_card_of_three_subgroup
    {Bs L : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hcardBL : Nat.card ↥(Bs ⊓ L) = 3 ^ 5)
    {S : Subgroup (MulAut ↥Bs)} (hSle : S ≤ ggAutomizer L Bs)
    (hS4 : 3 ^ 4 ∣ Nat.card ↥S) :
    3 ^ 7 ∣ Nat.card ↥L := by
  classical
  have hBsCent : Bs ≤ Subgroup.centralizer (Bs : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact IsElemAbelian.comm hBs hy hb
  have hBLN : Bs ⊓ L ≤ Subgroup.normalizer (Bs : Set G) :=
    (inf_le_left.trans hBsCent).trans (Subgroup.centralizer_le_normalizer (Bs : Set G))
  let N : Subgroup G := L ⊓ Subgroup.normalizer (Bs : Set G)
  have hBLN' : Bs ⊓ L ≤ N := fun b hb => ⟨hb.2, hBLN hb⟩
  let f : ↥N →* MulAut ↥Bs :=
    (Subgroup.normalizerMonoidHom (H := Bs)).comp (Subgroup.inclusion inf_le_right)
  have hrange : S ≤ f.range := by
    intro φ hφ
    obtain ⟨c, hcL, hcN, hcφ⟩ := mem_ggAutomizer_iff.mp (hSle hφ)
    refine ⟨⟨c, ⟨hcL, hcN⟩⟩, ?_⟩
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    have h1 : ((f ⟨c, ⟨hcL, hcN⟩⟩ b : ↥Bs) : G) = c * (b : G) * c⁻¹ := by
      simp [f, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [h1]
    exact (hcφ b).symm
  have hker : (Bs ⊓ L).subgroupOf N ≤ f.ker := by
    intro b hb
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    have hb' : (b : G) ∈ Bs := (Subgroup.mem_subgroupOf.mp hb).1
    have h1 : ((f b c : ↥Bs) : G) = (b : G) * (c : G) * (b : G)⁻¹ := by
      simp [f, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [h1]
    have hcomm := IsElemAbelian.comm hBs hb' c.2
    calc (b : G) * (c : G) * (b : G)⁻¹ = (c : G) * (b : G) * (b : G)⁻¹ := by rw [hcomm]
      _ = (c : G) := by group
  have hSdvd : Nat.card ↥S ∣ Nat.card ↥f.range := Subgroup.card_dvd_of_le hrange
  have hkerdvd : Nat.card ↥((Bs ⊓ L).subgroupOf N) ∣ Nat.card ↥f.ker :=
    Subgroup.card_dvd_of_le hker
  have hcardBLN : Nat.card ↥((Bs ⊓ L).subgroupOf N) = 3 ^ 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBLN').toEquiv, hcardBL]
  have hker5 : 3 ^ 5 ∣ Nat.card ↥f.ker := hcardBLN ▸ hkerdvd
  have hS4' : 3 ^ 4 ∣ Nat.card ↥f.range := hS4.trans hSdvd
  have h9 : 3 ^ 9 ∣ Nat.card ↥f.ker * Nat.card ↥f.range := by
    have h := mul_dvd_mul hker5 hS4'
    rwa [← pow_add] at h
  have h7 : 3 ^ 7 ∣ Nat.card ↥N := by
    rw [← Subgroup.card_ker_mul_card_range f]
    exact (pow_dvd_pow 3 (by norm_num : 7 ≤ 9)).trans h9
  exact h7.trans (Subgroup.card_dvd_of_le inf_le_left)

theorem GGSecFiveE6QTwoCfg.exists_le_ggAutomizer_top_card_eq
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg p B Bs x L D J) :
    ∃ A ≤ ggAutomizer ⊤ Bs, Nat.card A = 51840 := by
  obtain ⟨𝒦, -, -, ι, M, e, -, ⟨e', rfl⟩, -⟩ := hC
  refine ⟨ggAutomizerJoin L Bs 𝒦,
    sup_le (ggAutomizer_mono Bs le_top) (iSup₂_le fun K _ => ggAutomizer_mono Bs le_top), ?_⟩
  rw [← Nat.card_congr e.toEquiv, card_coxeterGroup_reindex, card_coxeterE6_group]

theorem lt_card_ggAutomizer_top_of_exists_card_eq
    {Bs : Subgroup G}
    (hA : ∃ A ≤ ggAutomizer (⊤ : Subgroup G) Bs, Nat.card A = 51840) :
    2 ^ 6 * Nat.factorial 6 < Nat.card (ggAutomizer ⊤ Bs) := by
  obtain ⟨A, hAle, hcard⟩ := hA
  calc 2 ^ 6 * Nat.factorial 6 < Nat.card A := by rw [hcard]; norm_num [Nat.factorial]
    _ ≤ Nat.card (ggAutomizer ⊤ Bs) := Subgroup.card_le_of_le hAle

theorem GGSecFiveRestHyp.exists_conj_not_mem_zpowers_of_twD5
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hA : ∃ A ≤ ggAutomizer (⊤ : Subgroup G) Bs, Nat.card A = 51840)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1)) :
    ∃ g : G, g * x * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) ∧
      g * x * g⁻¹ ∉ Subgroup.zpowers x := by
  by_contra h
  push Not at h
  obtain ⟨A₀, hA₀le, hA₀card⟩ := hA
  have hS : LargeEvenSStar 3 B x L := hR.1.1.2.2.2.2.2.2.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hR.1.tableB_facts
  have horderx : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hxB) hS.2.2.1
  obtain ⟨-, -, hmodel⟩ := E6QTwo.omegaMinusFive_of_marking hlab
  obtain ⟨-, hsup⟩ := GGSecFiveRestHyp.bstar_eq_sup_of_twD5 hR hlab
  have hcardBL := GGSecFiveRestHyp.card_bstar_inf_of_twD5 hR hlab
  have hLN := GGSecFiveRestHyp.normal_of_twD5 hR hlab
  have hInner : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AutThreePowInner ↥L :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.autThreePowInner_pomegaMinus_two
      (n := 5) (by norm_num) hmodel
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S₀, hS₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime (p := 3) (n := 4) (by rw [hA₀card]; norm_num)
  let S : Subgroup (MulAut ↥Bs) := S₀.map A₀.subtype
  have hScard : Nat.card ↥S = 3 ^ 4 := by
    rw [Subgroup.card_subtype A₀ S₀, hS₀card]
  have hSleA₀ : S ≤ A₀ := Subgroup.map_subtype_le S₀
  have hStop : S ≤ ggAutomizer ⊤ Bs := hSleA₀.trans hA₀le
  have hS3 : IsPGroup 3 ↥S := by
    rw [IsPGroup.iff_card]
    exact ⟨4, hScard⟩
  have hS4 : 3 ^ 4 ∣ Nat.card ↥S := by rw [hScard]
  have hc : S ≤ ggAutomizer L Bs :=
    le_ggAutomizer_of_three_subgroup hBs hxB horderx hLx hLN hInner hsup hS3 hStop h
  have h3L : 3 ^ 7 ∣ Nat.card ↥L :=
    three_pow_seven_dvd_card_of_three_subgroup hBs hcardBL hc hS4
  have hcardL : Nat.card ↥L = ordTwistedD 5 (2 ^ 1) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.2.2.2 rfl
  have hnot : ¬ 3 ^ 7 ∣ Nat.card ↥L := by
    rw [hcardL]
    decide
  exact hnot h3L

theorem GGSecFiveRestHyp.omegaMinusEnd_false'
    (hFSE : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → KProper InCatalog X →
      ∀ (b₀ : X) (K E : Subgroup X), orderOf b₀ = 3 →
        K ≤ Subgroup.centralizer ({b₀} : Set X) →
        (K.subgroupOf (Subgroup.centralizer ({b₀} : Set X))).Normal → Subgroup.center K = ⊥ →
        LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1) →
        (∀ S : Subgroup X, S ≤ Subgroup.centralizer (K : Set X) → IsPGroup 3 S → IsCyclic S) →
        twoLocalPrimeRank 3 (Subgroup.centralizer ({b₀} : Set X)) = twoLocalPrimeRank 3 X →
        (∃ g : X, g * b₀ * g⁻¹ ∈ Subgroup.centralizer ({b₀} : Set X) ∧
          g * b₀ * g⁻¹ ∉ Subgroup.zpowers b₀) →
        IsMaxElemAb3 (Subgroup.centralizer ({b₀} : Set X)) E → b₀ ∈ E → Nat.card E = 3 ^ 6 →
        2 ^ 6 * Nat.factorial 6 < Nat.card (ggAutomizer ⊤ E) → ¬ IsCharTwoType X)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hA : ∃ A ≤ ggAutomizer (⊤ : Subgroup G) Bs, Nat.card A = 51840)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1)) :
    False := by
  have hcfg : GGConfig 3 B Bs x L D J := hR.1
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have hord : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hxB) hS.2.2.1
  exact hFSE G hcfg.1.1 hcfg.1.2.2.1 x L Bs hord hLx (GGSecFiveRestHyp.normal_of_twD5 hR hlab)
    (E6QTwo.omegaMinusFive_of_marking hlab).2.1 hlab (fun S hSL hSp => hS.2.2.2.2 S hSL hSp)
    (twoLocalPrimeRank_centralizer_eq_of_config hcfg)
    (GGSecFiveRestHyp.exists_conj_not_mem_zpowers_of_twD5 hR hA hlab)
    (GGSecFiveRestHyp.isMaxElemAb3_centralizer hR) hxB
    (GGSecFiveRestHyp.card_bstar_of_twD5 hR hlab)
    (lt_card_ggAutomizer_top_of_exists_card_eq hA) hcfg.1.2.2.2.1

theorem GGSecFiveE6QTwoCfg.omegaMinusEnd_false'
    (hFSE : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → KProper InCatalog X →
      ∀ (b₀ : X) (K E : Subgroup X), orderOf b₀ = 3 →
        K ≤ Subgroup.centralizer ({b₀} : Set X) →
        (K.subgroupOf (Subgroup.centralizer ({b₀} : Set X))).Normal → Subgroup.center K = ⊥ →
        LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1) →
        (∀ S : Subgroup X, S ≤ Subgroup.centralizer (K : Set X) → IsPGroup 3 S → IsCyclic S) →
        twoLocalPrimeRank 3 (Subgroup.centralizer ({b₀} : Set X)) = twoLocalPrimeRank 3 X →
        (∃ g : X, g * b₀ * g⁻¹ ∈ Subgroup.centralizer ({b₀} : Set X) ∧
          g * b₀ * g⁻¹ ∉ Subgroup.zpowers b₀) →
        IsMaxElemAb3 (Subgroup.centralizer ({b₀} : Set X)) E → b₀ ∈ E → Nat.card E = 3 ^ 6 →
        2 ^ 6 * Nat.factorial 6 < Nat.card (ggAutomizer ⊤ E) → ¬ IsCharTwoType X)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1)) :
    False := by
  obtain ⟨𝒦, hRoute, -⟩ := id hC
  exact GGSecFiveRestHyp.omegaMinusEnd_false' hFSE hRoute.1
    hC.exists_le_ggAutomizer_top_card_eq hlab

end CFSG.StandardType

end
