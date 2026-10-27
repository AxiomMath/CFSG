module

public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutCover
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)

variable {G : Type} [Group G] [Finite G]

theorem card_eq_three_mul_of_le_of_ne {B Bs : Subgroup G} (hle : B ≤ Bs)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs ≤ 3 * Nat.card B) (hne : B ≠ Bs) :
    Nat.card Bs = 3 * Nat.card B := by
  have hp : IsPGroup 3 Bs := fun g => ⟨1, Subtype.ext (by simpa using hBs.2 g g.2)⟩
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  have hdvd : Nat.card B ∣ Nat.card Bs := Subgroup.card_dvd_of_le hle
  rw [ha] at hdvd
  obtain ⟨b, -, hb'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hlt : Nat.card B < Nat.card Bs := by
    by_contra hge
    exact hne (Subgroup.eq_of_le_of_card_ge hle (not_lt.mp hge))
  rw [ha, hb'] at hlt hcard
  rw [ha, hb']
  have h1 : b < a := by
    by_contra h
    have := Nat.pow_le_pow_right (by norm_num : 0 < 3) (not_lt.mp h)
    omega
  have h2 : a ≤ b + 1 := by
    by_contra h
    have h3 := Nat.pow_le_pow_right (by norm_num : 0 < 3) (not_le.mp h)
    have h4 : 0 < 3 ^ b := pow_pos (by norm_num) b
    rw [pow_succ, pow_succ] at h3
    omega
  have : a = b + 1 := by omega
  subst this
  rw [pow_succ]
  ring

private noncomputable def bstarConjAction {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) : Bs →* MulAut L :=
  (Subgroup.normalizerMonoidHom (H := L)).comp (Subgroup.inclusion hNL)

private theorem bstarConjAction_apply {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) (b : Bs) (l : L) :
    ((bstarConjAction hNL b) l : G) = (b : G) * l * (b : G)⁻¹ := by
  have hb : (b : G) ∈ Subgroup.normalizer (L : Set G) := hNL b.2
  have hmem : (b : G) * (l : G) * (b : G)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hb (l : G)).mp l.2
  change (((Subgroup.normalizerMonoidHom (H := L))
    (Subgroup.inclusion hNL b)) l : G) = _
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

theorem bstar_eq_sup_of_inner {Bs L : Subgroup G} {x : G} (hBs : IsElemAbelian 3 Bs)
    (hxB : x ∈ Bs) (hx1 : x ≠ 1) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hZ : Nat.Coprime (Nat.card (Subgroup.center ↥L)) 3)
    (hinner : ∀ b ∈ Bs, ∃ a : ↥L, ∀ y ∈ L, b⁻¹ * y * b = (a : G)⁻¹ * y * (a : G))
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
      IsCyclic S) :
    x ∉ L ∧ Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L) := by
  have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hx1 hLx hcyc
  have hinner' : ∀ b ∈ Bs, ∃ a ∈ L, ∀ y ∈ L, b * y * b⁻¹ = a * y * a⁻¹ := by
    intro b hb
    obtain ⟨a, ha⟩ := hinner b⁻¹ (Bs.inv_mem hb)
    refine ⟨(a : G)⁻¹, L.inv_mem a.2, fun y hy => ?_⟩
    simpa using ha y hy
  have hZ3 : ∀ z ∈ L, (∀ y ∈ L, z * y = y * z) → z ^ 3 = 1 → z = 1 := by
    intro z hzL hzc hz3
    let zc : Subgroup.center ↥L := ⟨⟨z, hzL⟩, Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (hzc y y.2).symm⟩
    have hzc3 : zc ^ 3 = 1 := by
      apply Subtype.ext; apply Subtype.ext; simpa [zc] using hz3
    have hd : orderOf zc ∣ Nat.gcd (Nat.card (Subgroup.center ↥L)) 3 :=
      Nat.dvd_gcd (orderOf_dvd_natCard zc) (orderOf_dvd_of_pow_eq_one hzc3)
    rw [hZ, Nat.dvd_one, orderOf_eq_one_iff] at hd
    simpa [zc] using congrArg (fun w : Subgroup.center ↥L => ((w : ↥L) : G)) hd
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBs.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hxL : x ∉ L := fun hxL => hx1 (hZ3 x hxL
    (fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hLx hy)).symm) (hBs.2 x hxB))
  refine ⟨hxL, le_antisymm (fun b hb => ?_) (sup_le (Subgroup.zpowers_le.mpr hxB) inf_le_left)⟩
  have hnorm : ∀ s ∈ Bs, ∀ y ∈ L, s * y * s⁻¹ ∈ L := by
    intro s hs y hy
    obtain ⟨a, haL, ha⟩ := hinner' s hs
    rw [ha y hy]
    exact L.mul_mem (L.mul_mem haL hy) (L.inv_mem haL)
  obtain ⟨a, haL, hab⟩ := hinner' b hb
  have hconj : ∀ k : ℕ, ∀ y ∈ L, b ^ k * y * (b ^ k)⁻¹ = a ^ k * y * (a ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro y _; simp
    | succ k ih =>
      intro y hy
      have hy' : a * y * a⁻¹ ∈ L := L.mul_mem (L.mul_mem haL hy) (L.inv_mem haL)
      calc b ^ (k + 1) * y * (b ^ (k + 1))⁻¹ = b ^ k * (b * y * b⁻¹) * (b ^ k)⁻¹ := by group
        _ = b ^ k * (a * y * a⁻¹) * (b ^ k)⁻¹ := by rw [hab y hy]
        _ = a ^ k * (a * y * a⁻¹) * (a ^ k)⁻¹ := ih _ hy'
        _ = a ^ (k + 1) * y * (a ^ (k + 1))⁻¹ := by group
  have ha3c : ∀ y ∈ L, a ^ 3 * y = y * a ^ 3 := by
    intro y hy
    have h := hconj 3 y hy
    rw [hBs.2 b hb] at h
    have h' : y = a ^ 3 * y * (a ^ 3)⁻¹ := by simpa using h
    calc a ^ 3 * y = (a ^ 3 * y * (a ^ 3)⁻¹) * a ^ 3 := by group
      _ = y * a ^ 3 := by rw [← h']
  set n := Nat.card (Subgroup.center ↥L)
  have hzn : (a ^ 3) ^ n = 1 := by
    let zc : Subgroup.center ↥L := ⟨⟨a ^ 3, L.pow_mem haL 3⟩, Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (ha3c y y.2).symm⟩
    have h := congrArg (fun w : Subgroup.center ↥L => ((w : ↥L) : G))
      (pow_card_eq_one' (G := Subgroup.center ↥L) (x := zc))
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h
    exact h
  have hn3 : n * n % 3 = 1 := by
    have h3 : ¬ 3 ∣ n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hZ.symm
    have h : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rw [Nat.mul_mod]
    rcases h with h | h <;> rw [h]
  set q := n * n / 3
  have hnq : n * n = 3 * q + 1 := by have := Nat.div_add_mod (n * n) 3; omega
  set a' := a ^ (n * n) with ha'
  have ha'L : a' ∈ L := L.pow_mem haL _
  have ha'eq : a' = (a ^ 3) ^ q * a := by rw [ha', hnq, pow_succ, pow_mul]
  have ha'3 : a' ^ 3 = 1 := by
    rw [ha', ← pow_mul, show n * n * 3 = 3 * n * n by ring, pow_mul, pow_mul, hzn, one_pow]
  have hqc : ∀ y ∈ L, (a ^ 3) ^ q * y = y * (a ^ 3) ^ q := by
    intro y hy
    induction q with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, ha3c y hy, ← mul_assoc, ih, mul_assoc]
  have hba' : ∀ y ∈ L, b * y * b⁻¹ = a' * y * a'⁻¹ := by
    intro y hy
    have hy' : a * y * a⁻¹ ∈ L := L.mul_mem (L.mul_mem haL hy) (L.inv_mem haL)
    rw [hab y hy, ha'eq]
    calc a * y * a⁻¹ = (a ^ 3) ^ q * (a * y * a⁻¹) * ((a ^ 3) ^ q)⁻¹ := by
          rw [hqc _ hy']; group
      _ = (a ^ 3) ^ q * a * y * ((a ^ 3) ^ q * a)⁻¹ := by group
  have ha'C : a' ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    set c := s * a' * s⁻¹ with hc
    have hcL : c ∈ L := hnorm s hs a' ha'L
    have hcy : ∀ y ∈ L, c * y * c⁻¹ = a' * y * a'⁻¹ := by
      intro y hy
      have hy' : s⁻¹ * y * s ∈ L := by
        simpa using hnorm s⁻¹ (Bs.inv_mem hs) y hy
      have hsb : s * b = b * s := hcomm s hs b hb
      calc c * y * c⁻¹ = s * (a' * (s⁻¹ * y * s) * a'⁻¹) * s⁻¹ := by rw [hc]; group
        _ = s * (b * (s⁻¹ * y * s) * b⁻¹) * s⁻¹ := by rw [hba' _ hy']
        _ = (s * b) * s⁻¹ * y * s * (s * b)⁻¹ := by group
        _ = (b * s) * s⁻¹ * y * s * (b * s)⁻¹ := by rw [hsb]
        _ = b * y * b⁻¹ := by group
        _ = a' * y * a'⁻¹ := hba' y hy
    have hzL : a'⁻¹ * c ∈ L := L.mul_mem (L.inv_mem ha'L) hcL
    have hzc : ∀ y ∈ L, a'⁻¹ * c * y = y * (a'⁻¹ * c) := by
      intro y hy
      have h := hcy y hy
      calc a'⁻¹ * c * y = a'⁻¹ * (c * y * c⁻¹) * c := by group
        _ = a'⁻¹ * (a' * y * a'⁻¹) * c := by rw [h]
        _ = y * (a'⁻¹ * c) := by group
    have hc3 : c ^ 3 = 1 := by
      rw [hc, conj_pow, ha'3]; group
    have hz3 : (a'⁻¹ * c) ^ 3 = 1 := by
      have hca : c * a'⁻¹ = a'⁻¹ * c := by
        have := hzc a'⁻¹ (L.inv_mem ha'L)
        calc c * a'⁻¹ = a' * (a'⁻¹ * c * a'⁻¹) := by group
          _ = a' * (a'⁻¹ * (a'⁻¹ * c)) := by rw [this]
          _ = a'⁻¹ * c := by group
      have hcomm' : Commute a'⁻¹ c := hca.symm
      rw [hcomm'.mul_pow, inv_pow, ha'3, hc3]; group
    have hz1 := hZ3 _ hzL hzc hz3
    have hceq : c = a' := by
      calc c = a' * (a'⁻¹ * c) := by group
        _ = a' := by rw [hz1, mul_one]
    calc s * a' = c * s := by rw [hc]; group
      _ = a' * s := by rw [hceq]
  have ha'B : a' ∈ Bs := hstar a' ha'C ha'3
  have hrest : b * a'⁻¹ ∈ Subgroup.zpowers x := by
    rw [← hBL]
    refine Subgroup.mem_inf.mpr ⟨Bs.mul_mem hb (Bs.inv_mem ha'B), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : a'⁻¹ * y * a' ∈ L := L.mul_mem (L.mul_mem (L.inv_mem ha'L) hy) ha'L
    have h := hba' _ hy'
    calc y * (b * a'⁻¹) = (a' * (a'⁻¹ * y * a') * a'⁻¹) * (b * a'⁻¹) := by group
      _ = (b * (a'⁻¹ * y * a') * b⁻¹) * (b * a'⁻¹) := by rw [h]
      _ = b * a'⁻¹ * y := by group
  have hb' : b = (b * a'⁻¹) * a' := by group
  rw [hb']
  exact (Subgroup.zpowers x ⊔ (Bs ⊓ L)).mul_mem (Subgroup.mem_sup_left hrest)
    (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨ha'B, ha'L⟩))

theorem bstar_eq_sup_of_elemAbelian {Bs L : Subgroup G} {x : G} (hBs : IsElemAbelian 3 Bs)
    (hxB : x ∈ Bs) (hx1 : x ≠ 1) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hN : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal)
    (hZ : Subgroup.center ↥L = ⊥) (hAut : AutThreePowInner ↥L)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
      IsCyclic S) :
    x ∉ L ∧ Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L) := by
  have hBsCx : Bs ≤ Subgroup.centralizer ({x} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hBs.1.is_comm.comm ⟨b, hb⟩ ⟨x, hxB⟩)
  have hNle : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLx).mp hN
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) := hBsCx.trans hNle
  refine bstar_eq_sup_of_inner hBs hxB hx1 hLx
    (by rw [hZ, Subgroup.card_bot]; exact Nat.coprime_one_left 3) (fun b hb => ?_) hstar hcyc
  let ψ := bstarConjAction hNL ⟨b, hb⟩
  have hψ3 : ψ ^ 3 = 1 := by
    rw [← map_pow]
    have hb3 : (⟨b, hb⟩ : ↥Bs) ^ 3 = 1 := by
      ext
      exact hBs.2 b hb
    rw [hb3]
    simp
  obtain ⟨a, ha⟩ := hAut ψ 1 (by
    intro y
    rw [pow_one]
    have hiter : ψ^[3] y = (ψ ^ 3) y := rfl
    rw [hiter, hψ3]
    simp)
  refine ⟨a, fun y hy => ?_⟩
  have hw : b⁻¹ * y * b ∈ L := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hNL hb)) y).mp hy
  have h1 : b * (b⁻¹ * y * b) * b⁻¹ = (a : G) * (b⁻¹ * y * b) * (a : G)⁻¹ := by
    have h := bstarConjAction_apply hNL ⟨b, hb⟩ ⟨b⁻¹ * y * b, hw⟩
    rw [show bstarConjAction hNL ⟨b, hb⟩ = ψ from rfl, ha] at h
    simpa using h.symm
  calc b⁻¹ * y * b = (a : G)⁻¹ * (b * (b⁻¹ * y * b) * b⁻¹) * (a : G) := by rw [h1]; group
    _ = (a : G)⁻¹ * y * (a : G) := by group

theorem card_sup_zpowers_le_three_mul_card_inf {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian 3 Bs) (hxB : x ∈ Bs) (hx1 : x ≠ 1)
    (h : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L)) :
    Nat.card Bs ≤ 3 * Nat.card ↥(Bs ⊓ L) := by
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Bs ⊓ L, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hBs.1.is_comm.comm ⟨a, Subgroup.zpowers_le.mpr hxB ha⟩ ⟨b, hb.1⟩)
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers x) (Bs ⊓ L) hcomm).1
  have hcardx : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hBs.2 x hxB) hx1]
  rw [hcardx] at hc
  calc Nat.card Bs = Nat.card ↥(Subgroup.zpowers x ⊔ (Bs ⊓ L)) :=
        congrArg (fun S : Subgroup G => Nat.card ↥S) h
    _ ≤ Nat.card ↥(Subgroup.zpowers x ⊔ (Bs ⊓ L)) *
          Nat.card ↥(Subgroup.zpowers x ⊓ (Bs ⊓ L)) :=
        Nat.le_mul_of_pos_right _ Nat.card_pos
    _ = 3 * Nat.card ↥(Bs ⊓ L) := hc

theorem ne_bstar_of_stdType_twoGroup {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hT : ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hN : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal)
    (hsup : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L))
    (hK : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ Subgroup.normalizer (L : Set G) →
      Bs ⊓ L ≤ Subgroup.normalizer (T : Set G) →
        T ≤ Subgroup.centralizer ((Bs ⊓ L : Subgroup G) : Set G)) :
    B ≠ Bs := by
  intro hBBs
  obtain ⟨T, hTx, hT2, hBT, hTB⟩ := hT
  have hleN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLx).mp hN
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hTx.trans hleN
  have hBsNT : Bs ≤ Subgroup.normalizer (T : Set G) := hBBs ▸ hBT
  have hET : Bs ⊓ L ≤ Subgroup.normalizer (T : Set G) := inf_le_left.trans hBsNT
  have hTCL : T ≤ Subgroup.centralizer ((Bs ⊓ L : Subgroup G) : Set G) := hK T hT2 hTN hET
  have hTCx : T ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hTx
  have hcent : T ≤ Subgroup.centralizer
      ((Subgroup.zpowers x ⊔ (Bs ⊓ L) : Subgroup G) : Set G) := by
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with hy | hy
    · exact Subgroup.mem_centralizer_iff.mp (hTCx ht) y hy
    · exact Subgroup.mem_centralizer_iff.mp (hTCL ht) y hy
  have hB_eq : B = Subgroup.zpowers x ⊔ (Bs ⊓ L) := hBBs.trans hsup
  exact hTB (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (by
    rw [hB_eq]
    exact hcent))

theorem le_centralizer_of_twoSubgroups_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E L T : Subgroup G} (hE : IsPGroup p E) (hEL : E ≤ L) (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hET : E ≤ Subgroup.normalizer (T : Set G))
    (hcen : ∀ U : Subgroup G, U ≤ L → IsPGroup 2 U → E ≤ Subgroup.normalizer (U : Set G) →
      U ≤ Subgroup.centralizer (L : Set G)) :
    T ≤ Subgroup.centralizer (E : Set G) := by
  have hU : T ⊓ L ≤ Subgroup.centralizer (L : Set G) := by
    refine hcen _ inf_le_right (hT.to_le inf_le_left) ?_
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hT' := Subgroup.mem_normalizer_iff.mp (hET he) g
    have hL' := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hEL he)) g
    exact ⟨fun hg => ⟨hT'.mp hg.1, hL'.mp hg.2⟩, fun hg => ⟨hT'.mpr hg.1, hL'.mpr hg.2⟩⟩
  have hTE : ⁅T, E⁆ ≤ T ⊓ L := by
    rw [Subgroup.commutator_le]
    intro t ht e he
    refine ⟨?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp (hET he) t⁻¹).mp (T.inv_mem ht)
      simpa [commutatorElement_def, mul_assoc] using T.mul_mem ht h
    · have h := (Subgroup.mem_normalizer_iff.mp (hTL ht) e).mp (hEL he)
      simpa [commutatorElement_def, mul_assoc] using L.mul_mem h (L.inv_mem (hEL he))
  have hbot : ⁅⁅T, E⁆, E⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (hTE.trans hU).trans (Subgroup.centralizer_le hEL)
  have hndvd : ¬ p ∣ Nat.card T := by
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp
      (Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp E T
    hE hndvd hET
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← hidem, hbot]

end CFSG.StandardType.FrameRoute

end
