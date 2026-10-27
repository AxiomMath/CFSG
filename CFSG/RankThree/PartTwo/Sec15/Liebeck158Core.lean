module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck158NineE
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec15.Liebeck158Split
import CFSG.RankThree.PartTwo.Sec15.Liebeck158Model
import CFSG.RankThree.PartTwo.Sec15.Liebeck158Cartan
import CFSG.RankThree.PartTwo.Sec15.Item158CartanProofPair
import CFSG.RankThree.PartTwo.Sec15.Item158CartanProof
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck158

open CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

private theorem exists_eq_mul_pow_mul_pow {F L : Subgroup G} {c x : G}
    (hFeq : F = Subgroup.zpowers c ⊔ (F ⊓ L)) (hc3 : c ^ 3 = 1) (hx3 : x ^ 3 = 1)
    (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hxFN : ∀ t ∈ F, x * t * x⁻¹ ∈ F) {a : G}
    (ha : a ∈ F ⊔ Subgroup.zpowers x) :
    ∃ b ∈ F ⊓ L, ∃ i j : ℕ, a = b * (c ^ i * x ^ j) := by
  have hcF : c ∈ F := by rw [hFeq]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  obtain ⟨t, htF, j, -, rfl⟩ := Sec13.exists_mul_pow_of_mem_sup hx3 hxFN ha
  have htF' : t ∈ (F ⊓ L) ⊔ Subgroup.zpowers c := by rw [sup_comm, ← hFeq]; exact htF
  obtain ⟨b, hb, i, -, rfl⟩ := Sec13.exists_mul_pow_of_mem_sup hc3
    (fun s hs => by rw [hFc c hcF s hs.1, mul_inv_cancel_right]; exact hs) htF'
  exact ⟨b, hb, i, j, mul_assoc _ _ _⟩

private theorem pow_three_mul_pow_mul {B : Subgroup G} {c y b : G}
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBe : ∀ a ∈ B, a ^ 3 = 1) (hB9 : Nat.card B = 9)
    (hc3 : c ^ 3 = 1) (hcB : ∀ a ∈ B, a * c = c * a) (hcy : y * c = c * y) (hy3 : y ^ 3 = 1)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) (hb : b ∈ B) (i : ℕ) :
    (b * (c ^ i * y)) ^ 3 = 1 := by
  have hcb : Commute (c ^ i) b := Commute.pow_left (Commute.symm (hcB b hb)) i
  have hcy' : Commute (c ^ i) y := Commute.pow_left (Commute.symm hcy) i
  have h1 : b * (c ^ i * y) = c ^ i * (b * y) := by
    rw [← mul_assoc, ← hcb.eq, mul_assoc]
  have hcj : (c ^ i) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hc3, one_pow]
  have hds : (b * y) ^ 3 = b * (y * b * y⁻¹) * (y * (y * b * y⁻¹) * y⁻¹) * y ^ 3 := by
    rw [pow_three, pow_three]; group
  rw [h1, (hcb.mul_right hcy').mul_pow, hcj, one_mul, hds,
    Sec16.Proof1617.mul_conj_mul_conj_eq_one hBc hBe hB9 hyB hy3 hb, one_mul, hy3]

private theorem commutator_mem_of_mul {L : Subgroup G} {b b' w w' : G} (hb : b ∈ L) (hb' : b' ∈ L)
    (hw : w ∈ Subgroup.normalizer (L : Set G)) (hw' : w' ∈ Subgroup.normalizer (L : Set G))
    (hww' : w * w' = w' * w) : b * w * (b' * w') * (b * w)⁻¹ * (b' * w')⁻¹ ∈ L := by
  have h1 : b * w * (b' * w') * (b * w)⁻¹ * (b' * w')⁻¹ =
      b * (w * b' * w⁻¹) * (w * w' * w⁻¹ * w'⁻¹) * (w' * b⁻¹ * w'⁻¹) * b'⁻¹ := by group
  have h2 : w * w' * w⁻¹ * w'⁻¹ = 1 := by rw [hww']; group
  rw [h1, h2, mul_one]
  exact L.mul_mem (L.mul_mem (L.mul_mem hb ((Subgroup.mem_normalizer_iff.mp hw b').mp hb'))
    ((Subgroup.mem_normalizer_iff.mp hw' b⁻¹).mp (L.inv_mem hb))) (L.inv_mem hb')

section Core


theorem exists_typeC_of_split (h41 : Sec4.Item4_1LargePrime) {A L F Y P : Subgroup G} {c : G}
    (hR : Sec15R G A c L) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) (hY : Y ∈ scriptY2 A)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)))
    (h3L : 3 ∣ Nat.card L) (hFP : F ≤ P) (hF : CFSG.Assembly.IsElemAbelian 3 F)
    (hF27 : Nat.card F = 27) (hF9 : Nat.card (F ⊓ L : Subgroup G) = 9)
    (hFeq : F = Subgroup.zpowers c ⊔ (F ⊓ L))
    (hsecF : ∀ a ∈ F, a ∈ Sec4.thetaQuotCentralizer L → a ∈ Subgroup.zpowers c)
    (hΩ : F ≠ omegaOneThree P) :
    ∃ E : Subgroup G, E ≤ P ∧ E ≤ Subgroup.normalizer (L : Set G) ∧ c ∈ E ∧
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
        (Subgroup.zpowers c : Set G) ∧
      Sec4.IsTypeCOn E L ∧ F ≤ Subgroup.normalizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := hR.toSec13Data
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hD.mem_A
  have hc1 : c ≠ 1 := hR.ne_one
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  have hFE : partTwoF G = partTwoE G :=
    (hR.toTheoremFourHyp.partTwoF_eq_partTwoE hR.partTwoS_eq).1
  obtain ⟨hP3, hPH, hPL, hPU⟩ := Proof158Cartan.facts_of_sylow hR h3L hP
  have hU2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hcF : c ∈ F := by rw [hFeq]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hcL : c ∉ L := by
    intro hcL
    have hle : F ≤ F ⊓ L := hFeq.le.trans (sup_le
      (Subgroup.zpowers_le.mpr (show c ∈ F ⊓ L from ⟨hcF, hcL⟩)) le_rfl)
    have := Subgroup.card_le_of_le hle
    omega
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hFF : F ∈ partTwoF G := hFE ▸ (⟨hF, hF27, _, hY.2, hU2, hFP.trans hPU⟩ : F ∈ partTwoE G)
  obtain ⟨x, hxP, hxN, hxF, hx3⟩ := Proof158Cartan.exists_of_ne_omegaOneThree hFP hF hP3 hΩ
  have hx1 : x ≠ 1 := fun h1 => hxF (h1 ▸ F.one_mem)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxc : x * c = c * x := by
    have hmem : x * c * x⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp (hPH hxP) c).mp (Subgroup.mem_zpowers c)
    exact Sec12.commute_of_conj_mem_zpowers hco hmem (k := 1) (by rw [pow_one]; exact hx3)
  have hxFN : ∀ t ∈ F, x * t * x⁻¹ ∈ F := fun t ht =>
    (Subgroup.mem_normalizer_iff.mp hxN t).mp ht
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := hPL hxP
  have hxB : x ∈ Subgroup.normalizer ((F ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp hxN y
    have h2 := Subgroup.mem_normalizer_iff.mp hxL y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
  set P' := F ⊔ Subgroup.zpowers x with hP'def
  have hP'P : P' ≤ P := sup_le hFP (Subgroup.zpowers_le.mpr hxP)
  have hP'3 : IsPGroup 3 P' := hP3.to_le hP'P
  have hP'N : P' ≤ Subgroup.normalizer (L : Set G) := hP'P.trans hPL
  have hFP' : F ≤ P' := le_sup_left
  have hxP' : x ∈ P' := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hcP' : c ∈ P' := hFP' hcF
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hP'N hcP'
  have hP'c : P' ≤ Subgroup.centralizer ({c} : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hFc a ha c hcF))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxc))
  have hP'81 : Nat.card P' = 81 := by
    have hXN : Subgroup.zpowers x ≤ Subgroup.normalizer (F : Set G) :=
      Subgroup.zpowers_le.mpr hxN
    have h1 := Sec6.card_sup_mul_card_inf hXN
    rw [Sec13.zpowers_inf_eq_bot hx3 hxF, Subgroup.card_bot, mul_one, Nat.card_zpowers, hxo,
      hF27, sup_comm] at h1
    rw [hP'def]
    omega
  have hexp : ∀ a ∈ P', a ^ 3 = 1 := by
    intro a ha
    obtain ⟨b, hb, i, j, rfl⟩ := exists_eq_mul_pow_mul_pow hFeq hc3 hx3 hFc hxFN ha
    have hxj : x ^ j * c = c * x ^ j := (Commute.pow_left (hxc : Commute x c) j).eq
    exact pow_three_mul_pow_mul (B := F ⊓ L) (fun a ha b hb => hFc a ha.1 b hb.1)
      (fun a ha => hF.2 a ha.1) hF9 hc3 (fun a ha => hFc a ha.1 c hcF) hxj
      (by rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow]) (Subgroup.pow_mem _ hxB j) hb i
  have hmodL : ∀ a ∈ P', ∀ b ∈ P', a * b * a⁻¹ * b⁻¹ ∈ L := by
    intro a ha b hb
    obtain ⟨b₁, hb₁, i, j, rfl⟩ := exists_eq_mul_pow_mul_pow hFeq hc3 hx3 hFc hxFN ha
    obtain ⟨b₂, hb₂, i', j', rfl⟩ := exists_eq_mul_pow_mul_pow hFeq hc3 hx3 hFc hxFN hb
    have hcx : Commute c x := hxc.symm
    have hww' : Commute (c ^ i * x ^ j) (c ^ i' * x ^ j') :=
      ((Commute.pow_pow_self c i i').mul_right (hcx.pow_pow i j')).mul_left
        ((hcx.symm.pow_pow j i').mul_right (Commute.pow_pow_self x j j'))
    exact commutator_mem_of_mul hb₁.2 hb₂.2
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hcN i) (Subgroup.pow_mem _ hxL j))
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hcN i') (Subgroup.pow_mem _ hxL j')) hww'.eq
  have hmax : ∀ E : Subgroup G, E ≤ P' → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E := by
    intro E hEP' hE hE27
    have hEE : E ∈ partTwoE G := ⟨hE, hE27, _, hY.2, hU2, hEP'.trans (hP'P.trans hPU)⟩
    exact (hFE ▸ hEE : E ∈ partTwoF G).2.1
  have hker : ∀ a ∈ P', a ∈ thetaQuotCentralizer L → a ∈ Subgroup.zpowers c := by
    intro a ha haC
    obtain ⟨-, haθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp haC
    have haB : ∀ b ∈ F ⊓ L, a * b = b * a := by
      intro b hb
      have h1 := haθ b hb.2
      have hbP' : b ∈ P' := hFP' hb.1
      have h2 : b⁻¹ * (a * b * a⁻¹) ∈ P' :=
        P'.mul_mem (P'.inv_mem hbP') (P'.mul_mem (P'.mul_mem ha hbP') (P'.inv_mem ha))
      have h3 := Proof158Cartan.eq_one_of_mem_theta_of_isPGroup hP'3 h2 h1
      calc a * b = b * (b⁻¹ * (a * b * a⁻¹)) * a := by group
        _ = b * a := by rw [h3, mul_one]
    have hac : a * c = c * a := Subgroup.mem_centralizer_singleton_iff.mp (hP'c ha)
    have haF : F ≤ Subgroup.centralizer ({a} : Set G) :=
      hFeq.le.trans (sup_le
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hac.symm))
        (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (haB b hb).symm))
    exact hsecF a (mem_of_mem_partTwoF hFF (hexp a ha) haF) haC
  have hnc : ∃ a ∈ P', ∃ b ∈ P', a * b * a⁻¹ * b⁻¹ ∉ Subgroup.zpowers c := by
    by_contra hcon
    push Not at hcon
    have hxB' : ∀ b ∈ F ⊓ L, b * x = x * b := by
      intro b hb
      have h1 := hcon x hxP' b (hFP' hb.1)
      have h2 : x * b * x⁻¹ * b⁻¹ ∈ L :=
        L.mul_mem ((Subgroup.mem_normalizer_iff.mp hxL b).mp hb.2) (L.inv_mem hb.2)
      have h3 : x * b * x⁻¹ * b⁻¹ ∈ Subgroup.zpowers c ⊓ L := ⟨h1, h2⟩
      rw [Sec13.zpowers_inf_eq_bot hc3 hcL, Subgroup.mem_bot] at h3
      calc b * x = (x * b * x⁻¹ * b⁻¹)⁻¹ * (x * b) := by group
        _ = x * b := by rw [h3, inv_one, one_mul]
    have hFx : F ≤ Subgroup.centralizer ({x} : Set G) :=
      hFeq.le.trans (sup_le
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxc.symm))
        (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hxB' b hb)))
    exact hxF (mem_of_mem_partTwoF hFF hx3 hFx)
  obtain ⟨π, p', f, K, _, hK, hq, e', hq2', hA'⟩ := exists_model_inndiag h41 hR
    ⟨p, e, inferInstance, he, hL3⟩ hP'def hF hF27 hFeq hF9 hx3 hxN hxF hP'N hP'c hmax
  obtain ⟨E, hEP', hcE, hE, hE27, hsec, hTC, hNE⟩ := exists_cartan_of_card_nine hcL hc3 hLc hP'N
    hP'3 hcP' hmodL (fun a ha => by rw [hexp a ha]; exact L.one_mem) hker hP'81
    (fun a ha => by rw [hexp a ha]; exact Subgroup.one_mem _) hnc hK hq hq2' e' hA'
  exact ⟨E, hEP'.trans hP'P, (hEP'.trans hP'P).trans hPL, hcE, hE, hE27, hsec, hTC,
    le_sup_left.trans hNE⟩

end Core

section Assembly


theorem step158NineE_of (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h148 : Item148R) (h41 : Sec4.Item4_1LargePrime) : Step158NineE := by
  intro G _ _ A c L hR p e _ he hL3 _ Y hY hmeet P hAP hP hΩ
  obtain ⟨F, hFP, hF, hF27, hFeq, hF9, hsecF, hFΩ⟩ :=
    exists_split_pair h131 h134 h48 h148 hR he hL3 hY hmeet hAP hP hΩ
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (hF9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨E, hEP, hEN, hcE, hE, hE27, hsec, hTC, -⟩ :=
    exists_typeC_of_split h41 hR he hL3 hY.2 hP h3L hFP hF hF27 hF9 hFeq hsecF hFΩ
  exact ⟨E, hEP, hEN, hE, hE27, hcE, hsec, hTC⟩

theorem step158CartanNineR_of_items (h138 : Item138N) (h131 : Item131) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h148 : Item148R) (h41 : Sec4.Item4_1LargePrime) :
    Step158CartanNineR :=
  step158CartanNineR_of_nineE h138 (step158NineE_of h131 h134 h48 h148 h41)

theorem step158CartanP_of_items (h138 : Item138N) (h131 : Item131) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h148 : Item148R) (h41 : Sec4.Item4_1LargePrime) : Step158CartanP :=
  step158CartanP_of h131 h134 h48 h148 (step158CartanNineR_of_items h138 h131 h134 h48 h148 h41)

theorem item158Y0R_of_items (h138 : Item138N) (h131 : Item131) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h148 : Item148R) (h41 : Sec4.Item4_1LargePrime) : Item158Y0R :=
  item158Y0R_of_cartanP h131 h138 h134 h48 h148
    (step158CartanP_of_items h138 h131 h134 h48 h148 h41)

end Assembly

end CFSG.RankThree.PartTwo.Sec15.Liebeck158
