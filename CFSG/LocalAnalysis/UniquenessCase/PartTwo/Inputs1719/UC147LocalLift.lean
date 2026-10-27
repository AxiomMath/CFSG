module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC147Frame
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantQuotientFixedPoints
import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC147Route

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_sup_of_conj_commutator_mem {V₀ Ri : Subgroup G} {a : G}
    (hV₀ : a ∈ Subgroup.normalizer (V₀ : Set G))
    (hRi : ∀ y ∈ Ri, a * y * a⁻¹ * y⁻¹ ∈ V₀) :
    a ∈ Subgroup.normalizer ((V₀ ⊔ Ri : Subgroup G) : Set G) := by
  let f : G →* G := (MulAut.conj a).toMonoidHom
  have hle : (V₀ ⊔ Ri).map f ≤ V₀ ⊔ Ri := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro - ⟨z, hz, rfl⟩
      have hzf : f z = a * z * a⁻¹ := by
        rw [show f z = (MulAut.conj a) z from rfl, MulAut.conj_apply]
      rw [hzf]
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hV₀ z).mp hz)
    · rintro - ⟨y, hy, rfl⟩
      have hyf : f y = a * y * a⁻¹ := by
        rw [show f y = (MulAut.conj a) y from rfl, MulAut.conj_apply]
      rw [hyf]
      have hc : a * y * a⁻¹ * y⁻¹ ∈ V₀ := hRi y hy
      have heq : a * y * a⁻¹ = (a * y * a⁻¹ * y⁻¹) * y := by group
      rw [heq]
      exact (V₀ ⊔ Ri).mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hy)
  have heq : (V₀ ⊔ Ri).map f = V₀ ⊔ Ri :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj a).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

omit [Finite G] in
theorem map_conj_le_normalizer_and_card {B R V V₀ M : Subgroup G} {x : G}
    (hBM : B ≤ M) (hRM : R ≤ M) (hx : x ∈ R) (hcardB : Nat.card B = 3)
    (hBV : B ≤ Subgroup.normalizer (V : Set G)) (hRV : R ≤ Subgroup.normalizer (V : Set G))
    (hBV₀ : B ≤ Subgroup.normalizer (V₀ : Set G)) (hRV₀ : R ≤ Subgroup.normalizer (V₀ : Set G)) :
    B.map (MulAut.conj x).toMonoidHom ≤ M ∧
      B.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (V : Set G) ∧
      B.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (V₀ : Set G) ∧
      Nat.card (B.map (MulAut.conj x).toMonoidHom) = 3 := by
  have hxm : x ∈ M := hRM hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro - ⟨b, hb, rfl⟩
    show (MulAut.conj x) b ∈ M
    rw [MulAut.conj_apply]
    exact M.mul_mem (M.mul_mem hxm (hBM hb)) (M.inv_mem hxm)
  · rintro - ⟨b, hb, rfl⟩
    show (MulAut.conj x) b ∈ Subgroup.normalizer (V : Set G)
    rw [MulAut.conj_apply]
    exact (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).mul_mem (hRV hx) (hBV hb))
      ((Subgroup.normalizer (V : Set G)).inv_mem (hRV hx))
  · rintro - ⟨b, hb, rfl⟩
    show (MulAut.conj x) b ∈ Subgroup.normalizer (V₀ : Set G)
    rw [MulAut.conj_apply]
    exact (Subgroup.normalizer (V₀ : Set G)).mul_mem
      ((Subgroup.normalizer (V₀ : Set G)).mul_mem (hRV₀ hx) (hBV₀ hb))
      ((Subgroup.normalizer (V₀ : Set G)).inv_mem (hRV₀ hx))
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact hcardB

theorem exists_centralizing_preimage {B' V V₀ : Subgroup G} {v : G}
    (hB'p : IsPGroup 3 B') (hB'V : B' ≤ Subgroup.normalizer (V : Set G))
    (hB'V₀ : B' ≤ Subgroup.normalizer (V₀ : Set G)) (hle : V₀ ≤ V)
    (hVV₀ : V ≤ Subgroup.normalizer (V₀ : Set G)) (hcop : Nat.Coprime 3 (Nat.card V))
    (hv : v ∈ V) (hcomm : ∀ b ∈ B', b * v * b⁻¹ * v⁻¹ ∈ V₀) :
    ∃ v' ∈ V, (v' : G)⁻¹ * v ∈ V₀ ∧ ∀ b ∈ B', b * v' = v' * b := by
  classical
  let N₀ : Subgroup V := V₀.subgroupOf V
  have hN₀ : N₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hVV₀
  let : N₀.Normal := hN₀
  have hcardN₀ : Nat.card N₀ = Nat.card V₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hcopN₀ : Nat.Coprime 3 (Nat.card N₀) := by
    rw [hcardN₀]
    exact hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
  let action : B' →* MulAut V := ambientSubgroupActionHom B' V hB'V
  have hinv : ∀ a : B', ∀ m ∈ N₀, action a m ∈ N₀ := by
    intro a m hm
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    rw [ambientSubgroupActionHom_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hB'V₀ a.2) (m : G)).mp hm
  let vV : V := ⟨v, hv⟩
  let e : V ⧸ N₀ := QuotientGroup.mk' N₀ vV
  have hfixed : ∀ a : B', invariantQuotientActionHom action N₀ hinv a e = e := by
    intro a
    have hw : ((action a vV : V) : G) * v⁻¹ ∈ V₀ := by
      rw [ambientSubgroupActionHom_apply_coe]
      exact hcomm a a.2
    have hmem : (QuotientGroup.mk' N₀) (action a vV) = (QuotientGroup.mk' N₀) vV := by
      change (action a vV : V ⧸ N₀) = (vV : V ⧸ N₀)
      rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
      simpa [div_eq_mul_inv] using hw
    show invariantQuotientActionHom action N₀ hinv a e = e
    rw [show e = (QuotientGroup.mk' N₀) vV from rfl, invariantQuotientActionHom_mk]
    exact hmem
  obtain ⟨v', hv'mk, hv'fix⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.coprime_normal_quotient_fixed_lift 3
      Nat.prime_three hB'p action N₀ hinv hcopN₀ e hfixed
  refine ⟨(v' : G), v'.2, ?_, ?_⟩
  · have h1 : (QuotientGroup.mk' N₀) ((v')⁻¹ * vV) = 1 := by
      rw [map_mul, map_inv, hv'mk]
      exact inv_mul_cancel _
    have h2 : (v')⁻¹ * vV ∈ N₀ := (QuotientGroup.eq_one_iff ((v')⁻¹ * vV)).mp h1
    rwa [Subgroup.mem_subgroupOf] at h2
  · intro b hb
    have h : ((ambientSubgroupActionHom B' V hB'V) ⟨b, hb⟩ v' : G) = (v' : G) :=
      congrArg (fun z : V => (z : G)) (hv'fix ⟨b, hb⟩)
    rw [ambientSubgroupActionHom_apply_coe] at h
    calc b * (v' : G) = (b * (v' : G) * b⁻¹) * b := by group
      _ = (v' : G) * b := by rw [h]

structure Sec147 (D : Data G) (B R V V₀ : Subgroup G) : Prop where
  hBV : B ≤ normalizer (V : Set G)
  hRV : R ≤ normalizer (V : Set G)
  hV : Nat.Coprime 3 (Nat.card V)
  hle : V₀ ≤ V
  hVV₀ : V ≤ normalizer (V₀ : Set G)
  hBV₀ : B ≤ normalizer (V₀ : Set G)
  hRV₀ : R ≤ normalizer (V₀ : Set G)
  hV₀M : V₀ ≤ D.M

namespace Ctx147

variable {D : Data G} {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ} {A X B R : Subgroup G}

theorem mem_M_of_conj_commutator_mem (c : Ctx147 D L n r p A X B R)
    (hsp3 : IsStronglyPEmbedded 3 D.M) {V V₀ : Subgroup G} (s : Sec147 D B R V V₀) {x : G}
    (hx : x ∈ R) {v : G} (hv : v ∈ V)
    (hvB : ∀ b ∈ B, (x * b * x⁻¹) * v * (x * b * x⁻¹)⁻¹ * v⁻¹ ∈ V₀) : v ∈ D.M := by
  classical
  let B' : Subgroup G := B.map (MulAut.conj x).toMonoidHom
  obtain ⟨hB'M, hB'V, hB'V₀, hcardB'⟩ :=
    map_conj_le_normalizer_and_card c.hB c.R_le hx c.card_B s.hBV s.hRV s.hBV₀ s.hRV₀
  have hB'p : IsPGroup 3 B' := IsPGroup.of_card (n := 1) (by rw [hcardB']; norm_num)
  have hB'ne : B' ≠ ⊥ := by
    intro h
    have h1 : Nat.card B' = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hcardB'] at h1
    omega
  have hcomm : ∀ b ∈ B', b * v * b⁻¹ * v⁻¹ ∈ V₀ := by
    intro b hb
    obtain ⟨b₀, hb₀, hb₀b⟩ := Subgroup.mem_map.mp hb
    have hbval : b = x * b₀ * x⁻¹ := by
      rw [← hb₀b]
      exact MulAut.conj_apply x b₀
    rw [hbval]
    exact hvB b₀ hb₀
  obtain ⟨v', _, hv'₀, hv'comm⟩ :=
    exists_centralizing_preimage hB'p hB'V hB'V₀ s.hle s.hVV₀ s.hV hv hcomm
  have hv'cent : v' ∈ Subgroup.centralizer (B' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hv'comm b hb
  have hv'N : v' ∈ Subgroup.normalizer (B' : Set G) :=
    Subgroup.centralizer_le_normalizer (B' : Set G) hv'cent
  have hv'M : v' ∈ D.M := hsp3.normalizer_le hB'ne hB'p hB'M hv'N
  have hvdef : v = v' * (v'⁻¹ * v) := by group
  rw [hvdef]
  exact D.M.mul_mem hv'M (s.hV₀M hv'₀)

theorem mem_M_of_commutator_mem_inf (c : Ctx147 D L n r p A X B R)
    (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M) {V V₀ : Subgroup G} (s : Sec147 D B R V V₀) (i : Fin 2)
    {v : G} (hv : v ∈ V) (hvR : ∀ y ∈ R ⊓ L i, y * v * y⁻¹ * v⁻¹ ∈ V₀) : v ∈ D.M := by
  classical
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let Ri : Subgroup G := R ⊓ L i
  let U : Subgroup G := Subgroup.zpowers v ⊔ V₀
  let K : Subgroup G := V₀ ⊔ Ri
  have hRiR : Ri ≤ R := inf_le_left
  have hRiM : Ri ≤ D.M := hRiR.trans c.R_le
  have hRicard : Nat.card Ri = 7 := (c.frame.2.2.1 i).1
  have hvU : v ∈ U := Subgroup.mem_sup_left (Subgroup.mem_zpowers v)
  have hUN₀ : U ≤ Subgroup.normalizer (V₀ : Set G) := by
    refine sup_le ?_ Subgroup.le_normalizer
    exact Subgroup.zpowers_le.mpr (s.hVV₀ hv)
  have hRiN₀ : Ri ≤ Subgroup.normalizer (V₀ : Set G) := hRiR.trans s.hRV₀
  have hvK : v ∈ Subgroup.normalizer (K : Set G) := by
    refine mem_normalizer_sup_of_conj_commutator_mem (s.hVV₀ hv) ?_
    intro y hy
    have h := V₀.inv_mem (hvR y hy)
    simpa [mul_assoc] using h
  have hV₀K : V₀ ≤ Subgroup.normalizer (K : Set G) := by
    intro a ha
    refine mem_normalizer_sup_of_conj_commutator_mem (Subgroup.le_normalizer ha) ?_
    intro y hy
    have hya : y * a * y⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.mp (s.hRV₀ (hRiR hy)) a).mp ha
    have hcomm : a * y * a⁻¹ * y⁻¹ = (y * a * y⁻¹ * a⁻¹)⁻¹ := by group
    rw [hcomm]
    exact V₀.inv_mem (V₀.mul_mem hya (V₀.inv_mem ha))
  have hRiK : Ri ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf hRiN₀ (Subgroup.le_normalizer : Ri ≤ Subgroup.normalizer (Ri : Set G))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup V₀ Ri)
  have hUK : U ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hvK) hV₀K
  have hHK : (U ⊔ Ri) ≤ Subgroup.normalizer (K : Set G) := sup_le hUK hRiK
  have hKH : K ≤ U ⊔ Ri := by
    refine sup_le ?_ le_sup_right
    exact (le_sup_right : V₀ ≤ U).trans le_sup_left
  have hRiKle : Ri ≤ K := le_sup_right
  have hcardRi' : Nat.card (Ri.subgroupOf K) = 7 := by
    change Nat.card (Ri.subgroupOf (V₀ ⊔ Ri)) = 7
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : Ri ≤ V₀ ⊔ Ri)).toEquiv,
      hRicard]
  have hRiP' : IsPGroup 7 (Ri.subgroupOf K) :=
    IsPGroup.of_card (n := 1) (by rw [hcardRi']; norm_num)
  obtain ⟨Q, hRQ⟩ := hRiP'.exists_le_sylow
  let Y₀ : Subgroup G := (Q : Subgroup K).map K.subtype
  have hY₀P : IsPGroup 7 Y₀ := Q.isPGroup'.map K.subtype
  have hRiY₀ : Ri ≤ Y₀ := by
    intro y hy
    have hyK : (⟨y, hRiKle hy⟩ : ↥K) ∈ Ri.subgroupOf K := hy
    exact Subgroup.mem_map.mpr ⟨⟨y, hRiKle hy⟩, hRQ hyK, rfl⟩
  have hY₀Sylow : CFSG.ABGLocalTools.IsSylowOf 7 Y₀ K := ⟨Q, rfl⟩
  have hFr : U ⊔ Ri ≤ K ⊔ Subgroup.normalizer (Y₀ : Set G) :=
    (uc22p22t_frattini_sup hKH hHK hY₀Sylow).trans
      (sup_le le_sup_left (le_trans inf_le_right le_sup_right))
  have hvN : v ∈ K ⊔ Subgroup.normalizer (Y₀ : Set G) := hFr (Subgroup.mem_sup_left hvU)
  refine (show K ⊔ Subgroup.normalizer (Y₀ : Set G) ≤ D.M from sup_le ?_ ?_) hvN
  · exact sup_le s.hV₀M hRiM
  · exact (le_and_normalizer_le_of_isPGroup D.maxLocal (hRi i) hRiY₀ hY₀P).2

end Ctx147

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
