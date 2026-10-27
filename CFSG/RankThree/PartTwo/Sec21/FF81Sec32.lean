module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32A
import CFSG.RankThree.PartTwo.Sec21.FF81KFacts
import CFSG.RankThree.PartTwo.Sec21.FF81J
import CFSG.RankThree.PartTwo.Sec21.FF81S0
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81Fusion
import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.GroupTheory.ElemAbelianClosure

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Open (IsElemAbelian)

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem eq_or_eq_inv_of_mem_zpowers {x : G} (hb : orderOf b = 3) (hx : x ∈ Subgroup.zpowers b)
    (hx1 : x ≠ 1) : x = b ∨ x = b⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hb] at hx1 ⊢
  have : (k % ((3 : ℕ) : ℤ)) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases this with h0 | h0 | h0 <;> rw [h0] at hx1 ⊢
  · exact absurd (zpow_zero b) hx1
  · left; exact zpow_one b
  · right
    have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hb3])

theorem mem_nor_of_gen {S : Set G} {n : G} (h : ∀ x ∈ S, n * x * n⁻¹ ∈ Subgroup.closure S) :
    n ∈ Nor (Subgroup.closure S) :=
  Subgroup.mem_normalizer_fintype fun _ hw => conj_mem_of_closure h hw

theorem conj_eq_inv_of_closure {S : Set G} {i : G}
    (hc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x)
    (hS : ∀ x ∈ S, i * x * i⁻¹ = x⁻¹) {x : G} (hx : x ∈ Subgroup.closure S) :
    i * x * i⁻¹ = x⁻¹ := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hS y hy
  | one => simp
  | mul y z hy hz ihy ihz =>
    rw [show i * (y * z) * i⁻¹ = (i * y * i⁻¹) * (i * z * i⁻¹) by group, ihy, ihz,
      hc y hy z hz, mul_inv_rev]
  | inv y hy ihy => rw [show i * y⁻¹ * i⁻¹ = (i * y * i⁻¹)⁻¹ by group, ihy]

theorem closure_four_eq (b b₁ b₂ b₃ : G) :
    Subgroup.closure ({b, b₁, b₂, b₃} : Set G) =
      Subgroup.zpowers b ⊔ Subgroup.closure ({b₁, b₂, b₃} : Set G) := by
  rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure]

section B

variable {b₁ b₂ b₃ : G}

theorem FF81Hyp.isElemAb_B (h : FF81Hyp b L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hB₁L : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ L) :
    IsElemAb 3 4 (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) := by
  set B₁ := Subgroup.closure ({b₁, b₂, b₃} : Set G)
  rw [closure_four_eq]
  have hB₁ab : IsElemAbelian 3 B₁ :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hE.1
  have hab : IsElemAbelian 3 (Subgroup.zpowers b ⊔ B₁) :=
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers h.b_cube) hB₁ab
      (fun x hx y hy => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact (comm_zpow_of_mem_cen (h.hLC (hB₁L hy)) k).symm)
  refine ⟨CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hab, ?_⟩
  have hinf : B₁ ⊓ Subgroup.zpowers b = ⊥ := eq_bot_iff.mpr fun x hx => by
    rw [← h.zpowers_inf_L]; exact ⟨hx.2, hB₁L hx.1⟩
  have hcard := card_sup_mul_card_inf B₁ (Subgroup.zpowers b)
    ((hB₁L.trans h.hLC).trans cen_le_nor_zpowers)
  rw [hinf, Subgroup.card_bot, mul_one, hE.2, h.card_zpowers, sup_comm] at hcard
  rw [hcard]; norm_num

theorem FF81Hyp.odd_cenS (h : FF81Hyp b L) (hTF : KF_Sp6TorusFree)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    {B : Subgroup G} (hB : IsElemAb 3 4 B) (hbB : b ∈ B) (hBC : B ≤ Cen b) :
    Odd (Nat.card (CenS B)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CenS B)) 2 (even_iff_two_dvd.mp hodd)
  have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have htC : (t : G) ∈ Cen b :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp t.2 b hbB).symm
  refine h.no_e81_local hTF hrk hBC (comm_of_isElemAb hB)
    (fun x hx => pow_three_eq_one_of_isElemAb hB hx) (by rw [hB.2]; norm_num)
    (T := Subgroup.zpowers (t : G)) (Subgroup.zpowers_le.mpr htC)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one]))
    (fun h0 => by
      rw [Subgroup.zpowers_eq_bot] at h0
      rw [h0, orderOf_one] at ht2; norm_num at ht2)
    (fun x hx => Subgroup.centralizer_le_normalizer _ (cen_le_cenS_zpowers_of_cen
      (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp t.2 x hx))))

theorem le_of_selfcen {B B₁ : Subgroup G} (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hB₁B : B₁ ≤ B) (hself : L ⊓ CenS B₁ = B₁) {x : G} (hx : x ∈ B) (hxL : x ∈ L) : x ∈ B₁ := by
  rw [← hself]
  exact ⟨hxL, Subgroup.mem_centralizer_iff.mpr fun y hy => hB y (hB₁B hy) x hx⟩

theorem mem_of_cenS_decomp {B B₁ : Subgroup G} (hB₁B : B₁ ≤ B) (hB₁L : B₁ ≤ L)
    (hself : L ⊓ CenS B₁ = B₁) {x l : G} (hx : x ∈ CenS B) (hl : l ∈ L)
    (hd : l⁻¹ * x ∈ CenS L) : l ∈ B₁ := by
  rw [← hself]
  refine ⟨hl, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have h1 : y * x = x * y := Subgroup.mem_centralizer_iff.mp hx y (hB₁B hy)
  have h2 : y * (l⁻¹ * x) = (l⁻¹ * x) * y := Subgroup.mem_centralizer_iff.mp hd y (hB₁L hy)
  calc y * l = y * (x * (l⁻¹ * x)⁻¹) := by group
    _ = x * y * (l⁻¹ * x)⁻¹ := by rw [← mul_assoc, h1]
    _ = x * (l⁻¹ * x)⁻¹ * ((l⁻¹ * x) * y * (l⁻¹ * x)⁻¹) := by group
    _ = x * (l⁻¹ * x)⁻¹ * (y * (l⁻¹ * x) * (l⁻¹ * x)⁻¹) := by rw [h2]
    _ = l * y := by group

end B

theorem FF81Hyp.opp_comm (h : FF81Hyp b L) {o l : G}
    (ho : o ∈ Opp 3 (Cen b)) (hl : l ∈ L) : o * l = l * o := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hON := CFSG.pPrimeCore_normal (p := 3) (G := ↥(Cen b))
  have hOco : Nat.Coprime 3 (Nat.card (Opp 3 (Cen b))) := by
    rw [Opp, CFSG.inSubgroup, Subgroup.card_map_of_injective (Cen b).subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hOL : Opp 3 (Cen b) ⊓ L = ⊥ := by
    haveI : IsSimpleGroup L :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp L 3 2 1 h.model
    haveI : ((Opp 3 (Cen b) ⊓ L).subgroupOf L).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨inSubgroup_conj_mem hON (h.hLC g.2) hn.1,
        L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)⟩⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Opp 3 (Cen b) ⊓ L).subgroupOf L) with h0 | h0
    · refine eq_bot_iff.mpr fun x hx => ?_
      have : (⟨x, hx.2⟩ : L) ∈ (Opp 3 (Cen b) ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
      rw [h0, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      have hLO : L ≤ Opp 3 (Cen b) := fun x hx => by
        have : (⟨x, hx⟩ : L) ∈ (Opp 3 (Cen b) ⊓ L).subgroupOf L := by
          rw [h0]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).1
      have h1 := Subgroup.card_dvd_of_le hLO
      rw [h.card_L] at h1
      exact absurd (hOco.coprime_dvd_right h1) (by norm_num)
  have hoC : o ∈ Cen b := Subgroup.map_subtype_le _ ho
  have h1 : o * l * o⁻¹ * l⁻¹ ∈ Opp 3 (Cen b) ⊓ L := by
    refine ⟨?_, ?_⟩
    · rw [show o * l * o⁻¹ * l⁻¹ = o * (l * o⁻¹ * l⁻¹) by group]
      exact Subgroup.mul_mem _ ho (inSubgroup_conj_mem hON (h.hLC hl) (Subgroup.inv_mem _ ho))
    · exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (h.hLN hoC) l).mp hl) (L.inv_mem hl)
  rw [hOL, Subgroup.mem_bot] at h1
  calc o * l = o * l * o⁻¹ * l⁻¹ * (l * o) := by group
    _ = l * o := by rw [h1, one_mul]

theorem FF81Hyp.closure_involutions (h : FF81Hyp b L) :
    Subgroup.closure {x | x ∈ L ∧ x * x = 1} = L := by
  haveI : IsSimpleGroup L :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp L 3 2 1 h.model
  set K := Subgroup.closure {x | x ∈ L ∧ x * x = 1}
  have hKL : K ≤ L := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hS : ∀ g ∈ L, ∀ x ∈ {x | x ∈ L ∧ x * x = 1}, g * x * g⁻¹ ∈ K := by
    rintro g hg x ⟨hxL, hx2⟩
    apply Subgroup.subset_closure
    refine ⟨L.mul_mem (L.mul_mem hg hxL) (L.inv_mem hg), ?_⟩
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hx2]; group
  have hn : (K.subgroupOf L).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_of_closure (hS g g.2) hn⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 (by rw [h.card_L]; norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf L) with h0 | h0
  · exfalso
    have htK : t ∈ K.subgroupOf L := Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure
      ⟨t.2, by
        have := pow_orderOf_eq_one t
        rw [ht, sq] at this
        exact congrArg Subtype.val this⟩)
    rw [h0, Subgroup.mem_bot] at htK
    rw [htK, orderOf_one] at ht
    norm_num at ht
  · refine le_antisymm hKL fun x hx => ?_
    have : (⟨x, hx⟩ : L) ∈ K.subgroupOf L := by rw [h0]; exact Subgroup.mem_top _
    exact this

theorem FF81Hyp.mem_nor_L (h : FF81Hyp b L) (hDodd : Odd (Nat.card ↥(Cen b ⊓ CenS L))) {g : G}
    (hg : g * b * g⁻¹ = b ∨ g * b * g⁻¹ = b⁻¹) : g ∈ Nor L := by
  have key : ∀ x ∈ {x | x ∈ L ∧ x * x = 1}, g * x * g⁻¹ ∈ L := by
    rintro x ⟨hxL, hx2⟩
    set y := g * x * g⁻¹ with hy
    have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp (h.hLC hxL)
    have hyb' : y * (g * b * g⁻¹) = (g * b * g⁻¹) * y := conj_commute hxb
    have hyC : y ∈ Cen b := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hg with hg | hg
      · rwa [hg] at hyb'
      · rw [hg] at hyb'
        calc y * b = b * (b⁻¹ * y) * b := by group
          _ = b * (y * b⁻¹) * b := by rw [hyb']
          _ = b * y := by group
    have hy2 : y * y = 1 := by
      rw [hy, show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hx2]; group
    obtain ⟨l, hlL, hd⟩ := h.exists_decomp hyC
    set d := l⁻¹ * y with hddef
    have hld : Commute l d := Subgroup.mem_centralizer_iff.mp hd.2 l hlL
    have hyd : y = l * d := by rw [hddef]; group
    have h2 : l ^ 2 * d ^ 2 = 1 := by rw [← hld.mul_pow, ← hyd, sq, hy2]
    have hl2 : l ^ 2 = 1 := by
      have hmem : l ^ 2 ∈ L ⊓ CenS L := ⟨L.pow_mem hlL 2, by
        rw [eq_inv_of_mul_eq_one_left h2]; exact (CenS L).inv_mem ((CenS L).pow_mem hd.2 2)⟩
      rw [h.inf_cenS_self, Subgroup.mem_bot] at hmem
      exact hmem
    have hd2 : d ^ 2 = 1 := by rwa [hl2, one_mul] at h2
    have hd1 : d = 1 := by
      have hd1' := eq_one_of_pow_two_of_odd (k := 1) (c := (⟨d, hd⟩ : ↥(Cen b ⊓ CenS L)))
        (Subtype.ext (by simpa using hd2)) (orderOf_dvd_natCard _) hDodd
      exact congrArg Subtype.val hd1'
    rw [hyd, hd1, mul_one]; exact hlL
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  rw [← h.closure_involutions] at hx ⊢
  exact conj_mem_of_closure (fun z hz => by rw [h.closure_involutions]; exact key z hz) hx

theorem FF81Hyp.cube_of_mem_zpowers (h : FF81Hyp b L) {x : G} (hx : x ∈ Subgroup.zpowers b) :
    x ^ 3 = 1 := by
  have := pow_card_eq_one' (G := ↥(Subgroup.zpowers b)) (x := ⟨x, hx⟩)
  rw [h.card_zpowers] at this
  simpa using congrArg Subtype.val this

theorem FF81Hyp.eq_sup_of_e81 (h : FF81Hyp b L)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    {E : Subgroup G} (hEC : E ≤ Cen b) (hE : IsElemAb 3 4 E) :
    E = (E ⊓ L) ⊔ Subgroup.zpowers b := by
  have hE81 : Nat.card E = 81 := by rw [hE.2]; norm_num
  obtain ⟨hbE, hEL⟩ := (h.card_elem_le hrk hEC (comm_of_isElemAb hE)
    (fun x hx => pow_three_eq_one_of_isElemAb hE hx)).2 hE81
  have hle : (E ⊓ L) ⊔ Subgroup.zpowers b ≤ E := sup_le inf_le_left (Subgroup.zpowers_le.mpr hbE)
  have hinf : (E ⊓ L) ⊓ Subgroup.zpowers b = ⊥ := eq_bot_iff.mpr fun x hx => by
    rw [← h.zpowers_inf_L]; exact ⟨hx.2, hx.1.2⟩
  have hcard := card_sup_mul_card_inf (E ⊓ L) (Subgroup.zpowers b)
    ((inf_le_left.trans hEC).trans cen_le_nor_zpowers)
  rw [hinf, Subgroup.card_bot, mul_one, hEL, h.card_zpowers] at hcard
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem FF81Hyp.e81_unique (h : FF81Hyp b L)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    (huniq : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q → ∀ E₁ E₂ : Subgroup G, E₁ ≤ Q → E₂ ≤ Q →
      IsElemAb 3 3 E₁ → IsElemAb 3 3 E₂ → E₁ = E₂)
    {Q : Subgroup G} (hQC : Q ≤ Cen b) (hQ : IsPGroup 3 Q) {E₁ E₂ : Subgroup G} (h1 : E₁ ≤ Q)
    (h2 : E₂ ≤ Q) (e1 : IsElemAb 3 4 E₁) (e2 : IsElemAb 3 4 E₂) : E₁ = E₂ := by
  have key : ∀ E, E ≤ Q → IsElemAb 3 4 E → IsElemAb 3 3 (E ⊓ L) := fun E hEQ hE => by
    have hE81 : Nat.card E = 81 := by rw [hE.2]; norm_num
    obtain ⟨-, hEL⟩ := (h.card_elem_le hrk (hEQ.trans hQC) (comm_of_isElemAb hE)
      (fun x hx => pow_three_eq_one_of_isElemAb hE hx)).2 hE81
    exact ⟨CFSG.IsElementaryAbelian.of_forall (fun x hx y hy => comm_of_isElemAb hE x hx.1 y hy.1)
      (fun x hx => pow_three_eq_one_of_isElemAb hE hx.1), by rw [hEL]; norm_num⟩
  have heq := huniq (Q ⊓ L) inf_le_right (hQ.to_le inf_le_left) (E₁ ⊓ L) (E₂ ⊓ L)
    (inf_le_inf_right L h1) (inf_le_inf_right L h2) (key E₁ h1 e1) (key E₂ h2 e2)
  rw [h.eq_sup_of_e81 hrk (h1.trans hQC) e1, h.eq_sup_of_e81 hrk (h2.trans hQC) e2, heq]

theorem FF81Hyp.fusion (h : FF81Hyp b L)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    (huniq : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q → ∀ E₁ E₂ : Subgroup G, E₁ ≤ Q → E₂ ≤ Q →
      IsElemAb 3 3 E₁ → IsElemAb 3 3 E₂ → E₁ = E₂)
    {B : Subgroup G} (hBC : B ≤ Cen b) (hB : IsElemAb 3 4 B) {g : G}
    (hg : g * b * g⁻¹ ∈ B) : ∃ n ∈ Nor B, n * b * n⁻¹ = g * b * g⁻¹ := by
  have hcomm := comm_of_isElemAb hB
  have hA : conjBy g⁻¹ B ≤ Cen b := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxβ : x * (g * b * g⁻¹) = (g * b * g⁻¹) * x := hcomm x hx _ hg
    have := conj_commute (a := g⁻¹) hxβ
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b by group] at this
  obtain ⟨c, hc, hcA⟩ := exists_conjBy_eq_of_unique (Y := Cen b) (H := Cen b)
    (fun Q hQ E₁ E₂ h1 h2 e1 e2 => h.e81_unique hrk huniq hQ.1 hQ.2.1 h1 h2 e1 e2) le_rfl hA hBC
    (isElemAb_conjBy hB g⁻¹) hB
  refine ⟨g * c⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjBy (g * c⁻¹) B = B
    conv_lhs => rw [← hcA]
    rw [← conjBy_mul, ← conjBy_mul, show g * c⁻¹ * c * g⁻¹ = 1 by group, conjBy_one]
  · have hcb : c * b = b * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc g * c⁻¹ * b * (g * c⁻¹)⁻¹ = g * (c⁻¹ * (b * c)) * g⁻¹ := by group
      _ = g * (c⁻¹ * (c * b)) * g⁻¹ := by rw [hcb]
      _ = g * b * g⁻¹ := by group

theorem FF81Hyp.exists_move (h : FF81Hyp b L)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    (huniq : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q → ∀ E₁ E₂ : Subgroup G, E₁ ≤ Q → E₂ ≤ Q →
      IsElemAb 3 3 E₁ → IsElemAb 3 3 E₂ → E₁ = E₂)
    {B B₁ : Subgroup G} (hBC : B ≤ Cen b) (hB : IsElemAb 3 4 B) (hbB : b ∈ B) (hB₁B : B₁ ≤ B)
    (hconj : ∀ x ∈ L, orderOf x = 3 → ∃ m ∈ L, m * x * m⁻¹ ∈ B₁) :
    ∃ n ∈ Nor B, n * b * n⁻¹ ∉ Subgroup.zpowers b := by
  obtain ⟨g, hle, hne⟩ := h.nwc
  change conjBy g⁻¹ (Subgroup.zpowers b) ≤ Cen b at hle
  change conjBy g⁻¹ (Subgroup.zpowers b) ≠ Subgroup.zpowers b at hne
  have hβcard : Nat.card (Subgroup.zpowers (g⁻¹ * b * g⁻¹⁻¹)) = 3 := by
    rw [← conjBy_zpowers, card_conjBy, h.card_zpowers]
  rw [conjBy_zpowers] at hle hne
  have hβ3 : (g⁻¹ * b * g⁻¹⁻¹) ^ 3 = 1 := by rw [conj_pow, h.b_cube]; group
  set β := g⁻¹ * b * g⁻¹⁻¹ with hβ
  have hβC : β ∈ Cen b := hle (Subgroup.mem_zpowers β)
  have hβnot : β ∉ Subgroup.zpowers b := fun hm => hne (Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hm) (le_of_eq (by rw [hβcard, h.card_zpowers])))
  obtain ⟨l, hlL, hl3, k, hβlk⟩ := h.cube_decomp hβC hβ3
  have hl1 : l ≠ 1 := fun h1 => hβnot (by
    rw [hβlk, h1, one_mul]; exact Subgroup.zpow_mem_zpowers b k)
  obtain ⟨m, hmL, hmB⟩ := hconj l hlL (orderOf_eq_prime hl3 hl1)
  have hmb : ∀ j : ℤ, m * b ^ j * m⁻¹ = b ^ j := fun j => by
    rw [comm_zpow_of_mem_cen (h.hLC hmL) j]; group
  have hβ' : m * β * m⁻¹ ∈ B := by
    rw [hβlk, show m * (l * b ^ k) * m⁻¹ = (m * l * m⁻¹) * (m * b ^ k * m⁻¹) by group, hmb]
    exact B.mul_mem (hB₁B hmB) (B.zpow_mem hbB k)
  have hβ'' : m * β * m⁻¹ = (m * g⁻¹) * b * (m * g⁻¹)⁻¹ := by rw [hβ]; group
  obtain ⟨n, hn, hnb⟩ := h.fusion hrk huniq hBC hB (g := m * g⁻¹) (by rw [← hβ'']; exact hβ')
  refine ⟨n, hn, fun hmem => hβnot ?_⟩
  rw [hnb, ← hβ''] at hmem
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hcm := comm_zpow_of_mem_cen (h.hLC hmL) j
  have : β = b ^ j := by
    calc β = m⁻¹ * (m * β * m⁻¹) * m := by group
      _ = m⁻¹ * b ^ j * m := by rw [← hj]
      _ = m⁻¹ * (m * b ^ j) := by rw [mul_assoc, ← hcm]
      _ = b ^ j := by group
  rw [this]; exact Subgroup.zpow_mem_zpowers b j

theorem FF81Hyp.cube_eq_one (h : FF81Hyp b L)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    (huniq : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q → ∀ E₁ E₂ : Subgroup G, E₁ ≤ Q → E₂ ≤ Q →
      IsElemAb 3 3 E₁ → IsElemAb 3 3 E₂ → E₁ = E₂)
    {B₁ : Subgroup G} (hB₁L : B₁ ≤ L) (hself : L ⊓ CenS B₁ = B₁) (hB₁3 : ∀ x ∈ B₁, x ^ 3 = 1)
    {B : Subgroup G} (hBeq : B = Subgroup.zpowers b ⊔ B₁) (hB : IsElemAb 3 4 B)
    (hconj : ∀ x ∈ L, orderOf x = 3 → ∃ m ∈ L, m * x * m⁻¹ ∈ B₁)
    {y : G} (hyC : y ∈ Cen b) (hyL : y ∈ CenS L) (hy : y ^ 3 ∈ Subgroup.zpowers b) :
    y ^ 3 = 1 := by
  by_contra hy1
  have hbB : b ∈ B := hBeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hB₁B : B₁ ≤ B := hBeq ▸ le_sup_right
  have hBC : B ≤ Cen b :=
    hBeq ▸ sup_le (Subgroup.zpowers_le.mpr (b_mem_cen b)) (hB₁L.trans h.hLC)
  obtain ⟨n, hn, hnb⟩ := h.exists_move hrk huniq hBC hB hbB hB₁B hconj
  apply hnb
  have hyB : y ∈ CenS B := by
    have hle : B ≤ Cen y := hBeq ▸ sup_le (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm))
      (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hyL z (hB₁L hz)))
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hz : n * y * n⁻¹ ∈ CenS B :=
    (Subgroup.mem_normalizer_iff.mp (nor_le_normalizer_cenS B hn) y).mp hyB
  have hzC : n * y * n⁻¹ ∈ Cen b := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB) hz
  obtain ⟨l, hlL, hd⟩ := h.exists_decomp hzC
  have hlB₁ := mem_of_cenS_decomp hB₁B hB₁L hself hz hlL hd.2
  have hld : Commute l (l⁻¹ * (n * y * n⁻¹)) := Subgroup.mem_centralizer_iff.mp hd.2 l hlL
  have hz3 : (n * y * n⁻¹) ^ 3 = (l⁻¹ * (n * y * n⁻¹)) ^ 3 := by
    conv_lhs => rw [show n * y * n⁻¹ = l * (l⁻¹ * (n * y * n⁻¹)) by group]
    rw [hld.mul_pow, hB₁3 l hlB₁, one_mul]
  have hzy : (n * y * n⁻¹) ^ 3 = n * y ^ 3 * n⁻¹ := conj_pow
  have hy9 : (y ^ 3) ^ 3 = 1 := h.cube_of_mem_zpowers hy
  have hd3 : (l⁻¹ * (n * y * n⁻¹)) ^ 3 ∈ Subgroup.zpowers b :=
    h.mem_zpowers_of_cube ((Cen b).pow_mem hd.1 3) ((CenS L).pow_mem hd.2 3)
      (by rw [← hz3, hzy, conj_pow, hy9]; group)
  have hyb : Subgroup.zpowers (y ^ 3) = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy)
      (by rw [h.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hy9 hy1])
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
    (show b ∈ Subgroup.zpowers (y ^ 3) by rw [hyb]; exact Subgroup.mem_zpowers b)
  have : n * b * n⁻¹ = ((l⁻¹ * (n * y * n⁻¹)) ^ 3) ^ i := by
    calc n * b * n⁻¹ = n * (y ^ 3) ^ i * n⁻¹ := by rw [hi]
      _ = (n * y ^ 3 * n⁻¹) ^ i := by rw [conj_zpow]
      _ = _ := by rw [← hzy, hz3]
  rw [this]
  exact Subgroup.zpow_mem _ hd3 i

theorem FF81Hyp.mem_zpowers_of_pow (h : FF81Hyp b L)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    (huniq : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q → ∀ E₁ E₂ : Subgroup G, E₁ ≤ Q → E₂ ≤ Q →
      IsElemAb 3 3 E₁ → IsElemAb 3 3 E₂ → E₁ = E₂)
    {B₁ : Subgroup G} (hB₁L : B₁ ≤ L) (hself : L ⊓ CenS B₁ = B₁) (hB₁3 : ∀ x ∈ B₁, x ^ 3 = 1)
    {B : Subgroup G} (hBeq : B = Subgroup.zpowers b ⊔ B₁) (hB : IsElemAb 3 4 B)
    (hconj : ∀ x ∈ L, orderOf x = 3 → ∃ m ∈ L, m * x * m⁻¹ ∈ B₁) (m : ℕ) :
    ∀ {z : G}, z ∈ Cen b → z ∈ CenS L → z ^ (3 ^ m) = 1 → z ∈ Subgroup.zpowers b := by
  induction m with
  | zero =>
    intro z _ _ hz
    rw [pow_zero, pow_one] at hz
    rw [hz]; exact Subgroup.one_mem _
  | succ m ih =>
    intro z hzC hzL hz
    have h3 : z ^ 3 ∈ Subgroup.zpowers b := ih ((Cen b).pow_mem hzC 3) ((CenS L).pow_mem hzL 3)
      (by rw [← pow_mul, ← pow_succ']; exact hz)
    exact h.mem_zpowers_of_cube hzC hzL
      (h.cube_eq_one hrk huniq hB₁L hself hB₁3 hBeq hB hconj hzC hzL h3)

theorem FF81Hyp.mem_of_cenS (h : FF81Hyp b L)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    (huniq : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q → ∀ E₁ E₂ : Subgroup G, E₁ ≤ Q → E₂ ≤ Q →
      IsElemAb 3 3 E₁ → IsElemAb 3 3 E₂ → E₁ = E₂)
    {B₁ : Subgroup G} (hB₁L : B₁ ≤ L) (hself : L ⊓ CenS B₁ = B₁) (hB₁3 : ∀ x ∈ B₁, x ^ 3 = 1)
    {B : Subgroup G} (hBeq : B = Subgroup.zpowers b ⊔ B₁) (hB : IsElemAb 3 4 B)
    (hconj : ∀ x ∈ L, orderOf x = 3 → ∃ m ∈ L, m * x * m⁻¹ ∈ B₁)
    {x : G} (hx : x ∈ CenS B) (hxp : IsPGroup 3 (Subgroup.zpowers x)) : x ∈ B := by
  have hbB : b ∈ B := hBeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hB₁B : B₁ ≤ B := hBeq ▸ le_sup_right
  have hxC : x ∈ Cen b := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB) hx
  obtain ⟨l, hlL, hd⟩ := h.exists_decomp hxC
  have hlB₁ := mem_of_cenS_decomp hB₁B hB₁L hself hx hlL hd.2
  obtain ⟨k, hk⟩ := hxp ⟨x, Subgroup.mem_zpowers x⟩
  have hk' : x ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hlx : Commute l x := Subgroup.mem_centralizer_iff.mp hx l (hB₁B hlB₁)
  have hl' : l ^ (3 ^ (k + 1)) = 1 := by rw [pow_succ', pow_mul, hB₁3 l hlB₁, one_pow]
  have hx' : x ^ (3 ^ (k + 1)) = 1 := by rw [pow_succ, pow_mul, hk', one_pow]
  have hdp : (l⁻¹ * x) ^ (3 ^ (k + 1)) = 1 := by
    rw [hlx.inv_left.mul_pow, inv_pow, hl', hx', inv_one, one_mul]
  have hdb := h.mem_zpowers_of_pow hrk huniq hB₁L hself hB₁3 hBeq hB hconj (k + 1) hd.1 hd.2 hdp
  rw [show x = l * (l⁻¹ * x) by group]
  exact B.mul_mem (hB₁B hlB₁) (hBeq ▸ Subgroup.mem_sup_left hdb)

theorem FF81Hyp.conj_b (h : FF81Hyp b L) {n : G} (hn : n ∈ L) : n * b * n⁻¹ = b := by
  rw [Subgroup.mem_centralizer_singleton_iff.mp (h.hLC hn)]; group

theorem FF81Hyp.stab (h : FF81Hyp b L) (hDodd : Odd (Nat.card ↥(Cen b ⊓ CenS L)))
    {b₁ b₂ b₃ : G} (hB₁L : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ L)
    (hself : L ⊓ CenS (Subgroup.closure ({b₁, b₂, b₃} : Set G)) =
      Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hmon : ∀ n ∈ L, n ∈ Nor (Subgroup.closure ({b₁, b₂, b₃} : Set G)) →
      ∀ x ∈ ({b₁, b₂, b₃} : Set G), n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    {B : Subgroup G} (hB : IsElemAb 3 4 B) (hB₁B : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ B)
    {n : G} (hn : n ∈ Nor B) (hnb : conjBy n (Subgroup.zpowers b) = Subgroup.zpowers b) :
    n * b * n⁻¹ ∈ ({b, b⁻¹} : Set G) ∧ ∀ x ∈ ({b₁, b₂, b₃} : Set G),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G) := by
  have hmem : n * b * n⁻¹ ∈ Subgroup.zpowers b := by
    rw [← hnb, conjBy_zpowers]; exact Subgroup.mem_zpowers _
  have hne : n * b * n⁻¹ ≠ 1 := fun h1 => h.b_ne_one (by
    rw [show b = n⁻¹ * (n * b * n⁻¹) * n by group, h1]; group)
  have hcase := eq_or_eq_inv_of_mem_zpowers h.ord hmem hne
  refine ⟨?_, fun x hx => ?_⟩
  · rcases hcase with h1 | h1 <;> rw [h1]
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  have hnL := h.mem_nor_L hDodd hcase
  obtain ⟨l, hlL, hl⟩ := kf_sp62Out G L h.model n hnL
  have hlN : l ∈ Nor (Subgroup.closure ({b₁, b₂, b₃} : Set G)) :=
    Subgroup.mem_normalizer_fintype fun y hy => by
      rw [← hl y (hB₁L hy)]
      exact le_of_selfcen (comm_of_isElemAb hB) hB₁B hself
        ((Subgroup.mem_normalizer_iff.mp hn y).mp (hB₁B hy))
        ((Subgroup.mem_normalizer_iff.mp hnL y).mp (hB₁L hy))
  rw [hl x (hB₁L (Subgroup.subset_closure hx))]
  exact hmon l hlL hlN x hx

theorem ff81_3_2 (hTF : KF_Sp6TorusFree) (hT : KF_Sp6Torus) : FF81_3_2 := by
  intro _ hP1 G _ _ b L h
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, hE, hself, hmon, ⟨n₁, hn₁L, n₁1, n₁2, n₁3⟩,
    ⟨n₂, hn₂L, n₂1, n₂2, n₂3⟩, ⟨n₃, hn₃L, n₃1, n₃2, n₃3⟩, hmonoL, ⟨i, hiL, hi1, hi2, hi3⟩,
    hconj, hrk, huniq, s, hsL, hs2, hs1, hs3⟩ := hT G L h.model
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup G, B = Subgroup.closure {b, b₁, b₂, b₃} := ⟨_, rfl⟩
  set B₁ := Subgroup.closure ({b₁, b₂, b₃} : Set G) with hB₁
  have hB₁L : B₁ ≤ L := (Subgroup.closure_le _).mpr (by
    rintro x (rfl | rfl | rfl); exacts [hb₁, hb₂, hb₃])
  have hBeq : B = Subgroup.zpowers b ⊔ B₁ := hBdef.trans (closure_four_eq b b₁ b₂ b₃)
  have hB4 : IsElemAb 3 4 B := hBdef ▸ h.isElemAb_B hE hB₁L
  have hbB : b ∈ B := hBeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hB₁B : B₁ ≤ B := hBeq ▸ le_sup_right
  have hBC : B ≤ Cen b :=
    hBeq ▸ sup_le (Subgroup.zpowers_le.mpr (b_mem_cen b)) (hB₁L.trans h.hLC)
  have hB₁3 : ∀ x ∈ B₁, x ^ 3 = 1 := fun x hx => pow_three_eq_one_of_isElemAb hE hx
  have hgen : ∀ y ∈ ({b, b₁, b₂, b₃} : Set G), y ∈ B := fun y hy =>
    hBdef ▸ Subgroup.subset_closure hy
  obtain ⟨⟨h1c, h2c, h3c⟩, ⟨h12, h13, h23⟩⟩ := triple_facts hE
  have h9 : Nat.card (Subgroup.closure ({b₁, b₃} : Set G)) = 9 :=
    card_pair_of_card_triple h2c h1c h3c h13 h12.symm h23
      (by rw [(isElemAb_perm hE).1.2]; norm_num)
  have hrank3 : localRank 3 G = 3 :=
    h.rank.trans (h.localRank_cen hTF hrk hb₁ hb₃ h13 h1c h3c h9 hsL hs2 hs1 hs3)
  have hcenOdd := h.odd_cenS hTF hrk hB4 hbB hBC
  have hDB : Cen b ⊓ CenS L ≤ CenS B := fun y hy => by
    have hle : B ≤ Cen y := hBeq ▸ sup_le (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hy.1).symm))
      (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hy.2 z (hB₁L hz)))
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hDodd : Odd (Nat.card ↥(Cen b ⊓ CenS L)) :=
    Odd.of_dvd_nat hcenOdd (Subgroup.card_dvd_of_le hDB)
  have hOD : Opp 3 (Cen b) ≤ Cen b ⊓ CenS L := fun o ho =>
    ⟨Subgroup.map_subtype_le _ ho, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (h.opp_comm ho hl).symm⟩
  obtain ⟨g₀, hg₀⟩ := hP1 G b L h hrank3
  have hord : orderOf (g₀ * b * g₀⁻¹) = 3 := by
    rw [show g₀ * b * g₀⁻¹ = MulAut.conj g₀ b from rfl, MulEquiv.orderOf_eq, h.ord]
  obtain ⟨m, hmL, hmx⟩ := hconj _ hg₀ hord
  have hx : (m * g₀) * b * (m * g₀)⁻¹ ∈ B₁ := by
    rw [show (m * g₀) * b * (m * g₀)⁻¹ = m * (g₀ * b * g₀⁻¹) * m⁻¹ by group]; exact hmx
  obtain ⟨nm, hnm, hnmb⟩ := h.fusion hrk huniq hBC hB4 (hB₁B hx)
  have hiinv : ∀ x ∈ B₁, i * x * i⁻¹ = x⁻¹ := fun x hx =>
    conj_eq_inv_of_closure (comm_of_isElemAb hE)
      (by rintro y (rfl | rfl | rfl); exacts [hi1, hi2, hi3]) hx
  set k := m * g₀ with hk
  set g := k⁻¹ * i * k with hg
  have hgb : g * b * g⁻¹ = b⁻¹ := by
    calc g * b * g⁻¹ = k⁻¹ * (i * (k * b * k⁻¹) * i⁻¹) * k := by rw [hg]; group
      _ = k⁻¹ * (k * b * k⁻¹)⁻¹ * k := by rw [hiinv _ hx]
      _ = b⁻¹ := by group
  obtain ⟨l, hlL, hl⟩ := kf_sp62Out G L h.model g (h.mem_nor_L hDodd (Or.inr hgb))
  have ht : ∀ x ∈ L, (l⁻¹ * g) * x * (l⁻¹ * g)⁻¹ = x := fun x hx => by
    calc (l⁻¹ * g) * x * (l⁻¹ * g)⁻¹ = l⁻¹ * (g * x * g⁻¹) * l := by group
      _ = l⁻¹ * (l * x * l⁻¹) * l := by rw [hl x hx]
      _ = x := by group
  have htb : (l⁻¹ * g) * b * (l⁻¹ * g)⁻¹ = b⁻¹ := by
    calc (l⁻¹ * g) * b * (l⁻¹ * g)⁻¹ = l⁻¹ * (g * b * g⁻¹) * l := by group
      _ = (l⁻¹ * b * l⁻¹⁻¹)⁻¹ := by rw [hgb]; group
      _ = b⁻¹ := by rw [h.conj_b (L.inv_mem hlL)]
  have hLnor : ∀ n ∈ L, (∀ y ∈ ({b₁, b₂, b₃} : Set G), n * y * n⁻¹ ∈ B) → n ∈ Nor B := by
    intro n hn hy
    rw [hBdef]
    refine mem_nor_of_gen fun y hy' => ?_
    rw [← hBdef]
    rcases hy' with rfl | hy'
    · rw [h.conj_b hn]; exact hbB
    · exact hy y hy'
  have hm4 : HasH0 B b b₁ b₂ b₃ := by
    refine ⟨hB4, hBdef, ⟨l⁻¹ * g, ?_, htb, ht _ hb₁, ht _ hb₂, ht _ hb₃⟩,
      ⟨n₁, hLnor n₁ hn₁L ?_, h.conj_b hn₁L, n₁1, n₁2, n₁3⟩,
      ⟨n₂, hLnor n₂ hn₂L ?_, h.conj_b hn₂L, n₂1, n₂2, n₂3⟩,
      ⟨n₃, hLnor n₃ hn₃L ?_, h.conj_b hn₃L, n₃1, n₃2, n₃3⟩⟩
    · rw [hBdef]
      refine mem_nor_of_gen fun y hy' => ?_
      rw [← hBdef]
      rcases hy' with rfl | rfl | rfl | rfl
      · rw [htb]; exact B.inv_mem hbB
      · rw [ht _ hb₁]; exact hgen _ (by simp)
      · rw [ht _ hb₂]; exact hgen _ (by simp)
      · rw [ht _ hb₃]; exact hgen _ (by simp)
    · rintro y (rfl | rfl | rfl)
      · rw [n₁1]; exact B.inv_mem (hgen _ (by simp))
      · rw [n₁2]; exact hgen _ (by simp)
      · rw [n₁3]; exact hgen _ (by simp)
    · rintro y (rfl | rfl | rfl)
      · rw [n₂1]; exact hgen _ (by simp)
      · rw [n₂2]; exact hgen _ (by simp)
      · rw [n₂3]; exact hgen _ (by simp)
    · rintro y (rfl | rfl | rfl)
      · rw [n₃1]; exact hgen _ (by simp)
      · rw [n₃2]; exact hgen _ (by simp)
      · rw [n₃3]; exact hgen _ (by simp)
  refine ⟨B, b₁, b₂, b₃,
    { hyp := h
      hb₁ := hb₁
      hb₂ := hb₂
      hb₃ := hb₃
      elem := hE
      selfcen := hself
      mono := hm4
      monoL := hmonoL
      fus := ?_
      stab := fun n hn hnb => h.stab hDodd hB₁L hself hmon hB4 hB₁B hn hnb
      cenSyl := fun x hx hxp => h.mem_of_cenS hrk huniq hB₁L hself hB₁3 hBeq hB4 hconj hx hxp
      o3odd := Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hOD)
      rank3 := hrank3
      cenOdd := hcenOdd
      meet := ⟨nm, hnm, by rw [hnmb]; exact hx⟩ }⟩
  rintro D ⟨hDB', g', rfl⟩
  have hg' : g' * b * g'⁻¹ ∈ B := hDB' (by rw [conjBy_zpowers]; exact Subgroup.mem_zpowers _)
  obtain ⟨n, hn, hnb⟩ := h.fusion hrk huniq hBC hB4 hg'
  exact ⟨n, hn, by rw [conjBy_zpowers, conjBy_zpowers, hnb]⟩

end CFSG.RankThree.PartTwo.Sec21.FF81
