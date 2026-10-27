module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xBR866
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65G2WeakClosureData
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.Chevalley

private theorem k1471n1_not_isCyclic_of_four {Y : Type} [Group Y] [Finite Y] {H : Subgroup Y}
    {a b c d : Y} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hd : d ∈ H)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ¬ IsCyclic ↥H := by
  classical
  intro hcyc
  have : Fintype ↥H := Fintype.ofFinite ↥H
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥H) (n := 3) (by norm_num)
  have hcard : ({⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩} : Finset ↥H).card = 4 := by
    simp [Finset.card_insert_of_notMem, hab, hac, had, hbc, hbd, hcd]
  have h4 : ({⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩} : Finset ↥H).card ≤ 3 :=
    le_trans (Finset.card_le_card (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [Subtype.ext_iff, *])) hle
  omega

private theorem k1471n1_noncyclic_outside {Y : Type} [Group Y] [Finite Y] {S₀ T : Subgroup Y}
    (hT : T ≤ S₀) (hout : ∀ s ∈ S₀, s ∉ T → s ^ 3 = 1) {z : Y}
    (hz : ∀ s ∈ S₀, s * z = z * s) (hzT : z ∈ T) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    {q : Y} (hq : q ∈ S₀) (hqT : q ∉ T) :
    ¬ IsCyclic ↥(S₀ ⊓ Subgroup.centralizer ({q} : Set Y)) := by
  have hzH : z ∈ S₀ ⊓ Subgroup.centralizer ({q} : Set Y) :=
    ⟨hT hzT, Subgroup.mem_centralizer_singleton_iff.2 (hz q hq).symm⟩
  have hqH : q ∈ S₀ ⊓ Subgroup.centralizer ({q} : Set Y) :=
    ⟨hq, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hz2T : z ^ 2 ∈ T := pow_mem hzT 2
  have hz2 : z ^ 2 ≠ 1 := fun h => hz1 (by
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, h]; simp)
  have hzz2 : z ≠ z ^ 2 := fun h => hz1 (mul_left_cancel (a := z) (by
    calc z * z = z ^ 2 := (sq z).symm
      _ = z := h.symm
      _ = z * 1 := (mul_one z).symm))
  exact k1471n1_not_isCyclic_of_four (one_mem _) hzH (pow_mem hzH 2) hqH (one_pow 3) hz3
    (by rw [← pow_mul, mul_comm, pow_mul, hz3, one_pow]) (hout q hq hqT) hz1.symm hz2.symm
    (fun h => hqT (h ▸ T.one_mem)) hzz2 (fun h => hqT (h ▸ hzT)) (fun h => hqT (h ▸ hz2T))

private theorem k1471n1_noncyclic_of_mem {Y : Type} [Group Y] [Finite Y] {S₀ T : Subgroup Y}
    (hT : T ≤ S₀) (hTab : IsMulCommutative ↥T) (hTnc : ¬ IsCyclic ↥T)
    (hout : ∀ s ∈ S₀, s ∉ T → s ^ 3 = 1) {z : Y}
    (hz : ∀ s ∈ S₀, s * z = z * s) (hzT : z ∈ T) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    {q : Y} (hq : q ∈ S₀) : ¬ IsCyclic ↥(S₀ ⊓ Subgroup.centralizer ({q} : Set Y)) := by
  by_cases hqT : q ∈ T
  · intro hcyc
    have hle : T ≤ S₀ ⊓ Subgroup.centralizer ({q} : Set Y) := fun x hx =>
      ⟨hT hx, Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥T) ⟨q, hqT⟩))⟩
    exact hTnc (Subgroup.isCyclic_of_le hle)
  · exact k1471n1_noncyclic_outside hT hout hz hzT hz1 hz3 hq hqT

private theorem k1471n1_mem_smul {Y : Type} [Group Y] [Finite Y] (S : Sylow 3 Y) (g x : Y) :
    x ∈ (g • S : Sylow 3 Y) ↔ ∃ y ∈ (S : Subgroup Y), g * y * g⁻¹ = x := by
  rw [← SetLike.mem_coe, Sylow.coe_smul, Set.mem_smul_set]
  simp only [MulAut.smul_def, MulAut.conj_apply]
  exact Iff.rfl

private theorem k1471n1_conj_comm {Y : Type} [Group Y] (g q y : Y) :
    g * y * g⁻¹ * (g * q * g⁻¹) = g * q * g⁻¹ * (g * y * g⁻¹) ↔ y * q = q * y := by
  have h1 : g * y * g⁻¹ * (g * q * g⁻¹) = g * (y * q) * g⁻¹ := by group
  have h2 : g * q * g⁻¹ * (g * y * g⁻¹) = g * (q * y) * g⁻¹ := by group
  rw [h1, h2]
  constructor
  · intro h
    simpa using h
  · intro h
    rw [h]

private theorem k1471n1_map_conj {Y : Type} [Group Y] [Finite Y] (S : Sylow 3 Y) (g q : Y) :
    ((S : Subgroup Y) ⊓ Subgroup.centralizer ({q} : Set Y)).map (MulAut.conj g).toMonoidHom =
      ((g • S : Sylow 3 Y) : Subgroup Y) ⊓ Subgroup.centralizer ({g * q * g⁻¹} : Set Y) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyS, hyc⟩, rfl⟩
    refine ⟨(k1471n1_mem_smul S g _).2 ⟨y, hyS, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact (k1471n1_conj_comm g q y).2 (Subgroup.mem_centralizer_singleton_iff.1 hyc)
  · rintro ⟨hxS, hxc⟩
    obtain ⟨y, hyS, rfl⟩ := (k1471n1_mem_smul S g x).1 hxS
    exact ⟨y, ⟨hyS, Subgroup.mem_centralizer_singleton_iff.2
      ((k1471n1_conj_comm g q y).1 (Subgroup.mem_centralizer_singleton_iff.1 hxc))⟩, rfl⟩

theorem sylowNoncyclicCentralizers_of_model
    {Y : Type} [Group Y] [Finite Y] (S₀ : Sylow 3 Y) (T : Subgroup Y) (hT : T ≤ (S₀ : Subgroup Y))
    (hTab : IsMulCommutative ↥T) (hTnc : ¬ IsCyclic ↥T)
    (hout : ∀ s ∈ (S₀ : Subgroup Y), s ∉ T → s ^ 3 = 1) {z : Y}
    (hz : ∀ s ∈ (S₀ : Subgroup Y), s * z = z * s) (hzT : z ∈ T) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    SylowNoncyclicCentralizers Y := by
  intro S q hq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S S₀
  subst hg
  have hq' : g * q * g⁻¹ ∈ ((g • S : Sylow 3 Y) : Subgroup Y) :=
    (k1471n1_mem_smul S g _).2 ⟨q, hq, rfl⟩
  intro hcyc
  refine k1471n1_noncyclic_of_mem hT hTab hTnc hout hz hzT hz1 hz3 hq' ?_
  rw [← k1471n1_map_conj]
  exact isCyclic_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap _)
    (MonoidHom.subgroupMap_surjective _ _)

private theorem k1471n2_map_eq {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (S : Subgroup Y)
    (q : Y) :
    (S ⊓ Subgroup.centralizer ({q} : Set Y)).map e.toMonoidHom =
      S.map e.toMonoidHom ⊓ Subgroup.centralizer ({e q} : Set Y') := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyS, hyc⟩, rfl⟩
    refine ⟨⟨y, hyS, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.1 hyc
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h]
  · rintro ⟨⟨y, hyS, rfl⟩, hxc⟩
    refine ⟨y, ⟨hyS, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.1 hxc
    apply e.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using h

theorem sylowNoncyclicCentralizers_of_mulEquiv
    {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y'] (e : Y ≃* Y')
    (h : SylowNoncyclicCentralizers Y') : SylowNoncyclicCentralizers Y := by
  intro S q hq hcyc
  have hs : Function.Surjective e.toMonoidHom := e.surjective
  refine h (Sylow.mapSurjective hs S) (e q) ⟨q, hq, rfl⟩ ?_
  rw [Sylow.coe_mapSurjective, ← k1471n2_map_eq]
  exact isCyclic_of_surjective (e.toMonoidHom.subgroupMap _) (MonoidHom.subgroupMap_surjective _ _)

private theorem k1471n3_not_isCyclic_of_four {M : Type} [Group M] {H : Subgroup M} [Finite ↥H]
    {a b c d : M} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hd : d ∈ H)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ¬ IsCyclic ↥H := by
  classical
  intro hcyc
  have : Fintype ↥H := Fintype.ofFinite ↥H
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥H) (n := 3) (by norm_num)
  have hcard : ({⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩} : Finset ↥H).card = 4 := by
    simp [Finset.card_insert_of_notMem, hab, hac, had, hbc, hbd, hcd]
  have h4 : ({⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩} : Finset ↥H).card ≤ 3 :=
    le_trans (Finset.card_le_card (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [Subtype.ext_iff, *])) hle
  omega

open CFSG.AGLEmbedding.KFactProofs.G2Q in
private theorem k1471n3_mem_of_tor {M : Type} [Group M] {T0 Tor : Subgroup M} {y : M}
    (h : Ext3 T0 y) (hle : T0 ≤ Tor) (hy : y ∉ Tor) {x : M} (hx : x ∈ extSub h)
    (hxT : x ∈ Tor) : x ∈ T0 := by
  obtain ⟨t, ht, k, hk, rfl⟩ := (mem_extSub_iff_lt h).1 hx
  have hy3 : y = (y ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h.pow_three, one_mul, pow_one]
  interval_cases k
  · simpa using ht
  · exact absurd (by simpa using Tor.mul_mem (Tor.inv_mem (hle ht)) hxT) hy
  · have h2 : y ^ 2 ∈ Tor := by simpa using Tor.mul_mem (Tor.inv_mem (hle ht)) hxT
    exact absurd (hy3 ▸ pow_mem h2 2) hy

open CFSG.AGLEmbedding.KFactProofs.G2Q in
private theorem k1471n3_mem_ext {A M : Type} [Group A] [Group M] {φ : A →* M} {g : M}
    {T0 : Subgroup M} {y : M} (h : Ext3 T0 y) {Q0 : Subgroup A}
    (hmap : Q0.map φ = (extSub h).map (MulAut.conj g).toMonoidHom) (z0 : ↥Q0) {w : M}
    (hz : φ z0 = g * w * g⁻¹) : w ∈ extSub h := by
  have hmem : φ (z0 : A) ∈ Q0.map φ := ⟨z0, z0.2, rfl⟩
  rw [hmap] at hmem
  obtain ⟨x, hx, hxe⟩ := hmem
  have h2 : g * x * g⁻¹ = g * w * g⁻¹ := by simpa [MulAut.conj_apply] using hxe.trans hz
  have h3 : x = w := by simpa using h2
  exact h3 ▸ hx

open CFSG.AGLEmbedding.KFactProofs.G2Q in
private theorem k1471n3_cube_of_mem {M : Type} [Group M] {T0 : Subgroup M} {y : M}
    (h : Ext3 T0 y) (hcube : ∀ t ∈ T0, (t * y) ^ 3 = 1) {x : M} (hx : x ∈ extSub h)
    (hxT : x ∉ T0) : x ^ 3 = 1 := by
  obtain ⟨t, ht, k, hk, rfl⟩ := (mem_extSub_iff_lt h).1 hx
  interval_cases k
  · exact absurd (by simpa using ht) hxT
  · simpa using hcube t ht
  · have hy2 : (y ^ 2)⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact h.pow_three)
    have hinv : (t * y ^ 2)⁻¹ = (y * t⁻¹ * y⁻¹) * y := by
      rw [mul_inv_rev, hy2]; group
    have h1 := hcube _ (h.normal _ (T0.inv_mem ht))
    rw [← hinv, inv_pow, inv_eq_one] at h1
    exact h1

private theorem k1471n3_comm {A M : Type} [Group A] [Group M] {φ : A →* M}
    (hφ : Function.Injective φ) {g : M} {T0 : Subgroup M}
    (hcomm : ∀ a ∈ T0, ∀ b ∈ T0, a * b = b * a) {Q0 T : Subgroup A}
    (hT : ∀ a, a ∈ T ↔ a ∈ Q0 ∧ ∃ t ∈ T0, g * t * g⁻¹ = φ a) : IsMulCommutative ↥T := by
  refine IsMulCommutative.of_comm ?_
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨-, t, ht, hta⟩ := (hT a).1 ha
  obtain ⟨-, t', ht', htb⟩ := (hT b).1 hb
  refine Subtype.ext (hφ ?_)
  simp only [Subgroup.coe_mul, map_mul]
  rw [← hta, ← htb]
  calc g * t * g⁻¹ * (g * t' * g⁻¹) = g * (t * t') * g⁻¹ := by group
    _ = g * (t' * t) * g⁻¹ := by rw [hcomm t ht t' ht']
    _ = g * t' * g⁻¹ * (g * t * g⁻¹) := by group

open CFSG.AGLEmbedding.KFactProofs.G2Q in
private theorem k1471n3_cube_outside {A M : Type} [Group A] [Group M] {φ : A →* M}
    (hφ : Function.Injective φ) {g : M} {T0 : Subgroup M} {y : M} (h : Ext3 T0 y)
    (hcube : ∀ t ∈ T0, (t * y) ^ 3 = 1) {Q0 T : Subgroup A}
    (hmap : Q0.map φ = (extSub h).map (MulAut.conj g).toMonoidHom)
    (hT : ∀ a, a ∈ T ↔ a ∈ Q0 ∧ ∃ t ∈ T0, g * t * g⁻¹ = φ a)
    {s : A} (hs : s ∈ Q0) (hsT : s ∉ T) : s ^ 3 = 1 := by
  have hmem : φ s ∈ Q0.map φ := ⟨s, hs, rfl⟩
  rw [hmap] at hmem
  obtain ⟨x, hx, hxe⟩ := hmem
  have hxe' : g * x * g⁻¹ = φ s := by simpa [MulAut.conj_apply] using hxe
  have hxT : x ∉ T0 := fun hxT0 => hsT ((hT s).2 ⟨hs, x, hxT0, hxe'⟩)
  refine hφ ?_
  rw [map_pow, ← hxe', map_one, conj_pow, k1471n3_cube_of_mem h hcube hx hxT]
  simp

private theorem k1471n3_central {A : Type} [Group A] {Q0 : Subgroup A} {z0 : ↥Q0}
    (hcenter : Subgroup.center ↥Q0 = Subgroup.zpowers z0) {s : A} (hs : s ∈ Q0) :
    s * (z0 : A) = (z0 : A) * s := by
  have hz : z0 ∈ Subgroup.center ↥Q0 := hcenter ▸ Subgroup.mem_zpowers z0
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨s, hs⟩)

open CFSG.AGLEmbedding.KFactProofs.G2Q in
private theorem k1471n3_noncyclic {A M : Type} [Group A] [Finite A] [Group M] {φ : A →* M}
    {g : M} {T0 : Subgroup M} {y : M} (h : Ext3 T0 y) {Q0 T : Subgroup A}
    (hmap : Q0.map φ = (extSub h).map (MulAut.conj g).toMonoidHom)
    (hT : ∀ a, a ∈ T ↔ a ∈ Q0 ∧ ∃ t ∈ T0, g * t * g⁻¹ = φ a)
    (hfour : ∃ a ∈ T0, ∃ b ∈ T0, ∃ c ∈ T0, ∃ d ∈ T0, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ c ^ 3 = 1 ∧
      d ^ 3 = 1 ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) :
    ¬ IsCyclic ↥T := by
  intro hcyc
  have hsurj := MonoidHom.subgroupMap_surjective φ T
  have hTmap : ∀ x ∈ T0, g * x * g⁻¹ ∈ T.map φ := by
    intro x hx
    obtain ⟨a, haQ, hax⟩ : g * x * g⁻¹ ∈ Q0.map φ := by
      rw [hmap]
      exact ⟨x, le_extSub h hx, by simp [MulAut.conj_apply]⟩
    exact ⟨a, (hT a).2 ⟨haQ, x, hx, hax.symm⟩, hax⟩
  have : IsCyclic ↥(T.map φ) := isCyclic_of_surjective (φ.subgroupMap T) hsurj
  have : Finite ↥(T.map φ) := Finite.of_surjective (φ.subgroupMap T) hsurj
  obtain ⟨a, ha, b, hb, c, hc, d, hd, ha3, hb3, hc3, hd3, hab, hac, had, hbc, hbd, hcd⟩ := hfour
  exact k1471n3_not_isCyclic_of_four (hTmap a ha) (hTmap b hb) (hTmap c hc) (hTmap d hd)
    (by rw [conj_pow, ha3]; simp) (by rw [conj_pow, hb3]; simp) (by rw [conj_pow, hc3]; simp)
    (by rw [conj_pow, hd3]; simp) (fun e => hab (by simpa using e))
    (fun e => hac (by simpa using e)) (fun e => had (by simpa using e))
    (fun e => hbc (by simpa using e)) (fun e => hbd (by simpa using e))
    (fun e => hcd (by simpa using e)) inferInstance

open CFSG.AGLEmbedding.KFactProofs.G2Q in
private theorem k1471n3_model {A M : Type} [Group A] [Finite A] [Group M] {φ : A →* M}
    (hφ : Function.Injective φ) {g : M} {T0 : Subgroup M} {y : M} (h : Ext3 T0 y)
    (hcomm : ∀ a ∈ T0, ∀ b ∈ T0, a * b = b * a) (hcube : ∀ t ∈ T0, (t * y) ^ 3 = 1)
    (hfour : ∃ a ∈ T0, ∃ b ∈ T0, ∃ c ∈ T0, ∃ d ∈ T0, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ c ^ 3 = 1 ∧
      d ^ 3 = 1 ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    {Q0 : Subgroup A} (hmap : Q0.map φ = (extSub h).map (MulAut.conj g).toMonoidHom)
    (P : Sylow 3 A) (hP : (P : Subgroup A) = Q0) (z0 : ↥Q0)
    (hcenter : Subgroup.center ↥Q0 = Subgroup.zpowers z0) (hz3 : orderOf (z0 : A) = 3)
    {w : M} (hz : φ z0 = g * w * g⁻¹) (hw : w ∈ T0) :
    ∃ (S₀ : Sylow 3 A) (T : Subgroup A) (z : A), T ≤ (S₀ : Subgroup A) ∧ IsMulCommutative ↥T ∧
      ¬ IsCyclic ↥T ∧ (∀ s ∈ (S₀ : Subgroup A), s ∉ T → s ^ 3 = 1) ∧
      (∀ s ∈ (S₀ : Subgroup A), s * z = z * s) ∧ z ∈ T ∧ z ≠ 1 ∧ z ^ 3 = 1 := by
  have hT : ∀ a, a ∈ Q0 ⊓ (T0.map (MulAut.conj g).toMonoidHom).comap φ ↔
      a ∈ Q0 ∧ ∃ t ∈ T0, g * t * g⁻¹ = φ a := by
    intro a
    simp [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map, MulAut.conj_apply]
  refine ⟨P, Q0 ⊓ (T0.map (MulAut.conj g).toMonoidHom).comap φ, (z0 : A), ?_,
    k1471n3_comm hφ hcomm hT, k1471n3_noncyclic h hmap hT hfour, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hP]
    exact inf_le_left
  · intro s hs hsT
    rw [hP] at hs
    exact k1471n3_cube_outside hφ h hcube hmap hT hs hsT
  · intro s hs
    rw [hP] at hs
    exact k1471n3_central hcenter hs
  · exact (hT _).2 ⟨z0.2, w, hw, hz.symm⟩
  · intro h1
    rw [h1, orderOf_one] at hz3
    exact absurd hz3 (by norm_num)
  · have h1 := pow_orderOf_eq_one (z0 : A)
    rwa [hz3] at h1

private theorem k1471n3_pow_two_ne_one {G : Type} [Group G] {ω : G} (h1 : ω ≠ 1)
    (h3 : ω ^ 3 = 1) : ω ^ 2 ≠ 1 := fun h => h1 (by
  calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h]; simp)

private theorem k1471n3_ne_pow_two {G : Type} [Group G] {ω : G} (h1 : ω ≠ 1) : ω ≠ ω ^ 2 :=
  fun h => h1 (mul_left_cancel (a := ω) (by
    calc ω * ω = ω ^ 2 := (sq ω).symm
      _ = ω := h.symm
      _ = ω * 1 := (mul_one ω).symm))

open CFSG.AGLEmbedding.KFactProofs.G2Q in
private theorem k1471n3_tzPart_comm
    {L : Type} [Field L] (m : ℕ) :
    ∀ a ∈ (tzPart m : Subgroup (ModGL .G2 L)), ∀ b ∈ (tzPart m : Subgroup (ModGL .G2 L)),
      a * b = b * a := by
  rintro _ ⟨s, t, -, -, rfl⟩ _ ⟨s', t', -, -, rfl⟩
  rw [tz_mul, tz_mul, mul_comm s s', mul_comm t t']

open CFSG.AGLEmbedding.KFactProofs.G2Q in
private theorem k1471n3_tzPart_cube
    {L : Type} [Field L] (m : ℕ) :
    ∀ t ∈ (tzPart m : Subgroup (ModGL .G2 L)), (t * yq) ^ 3 = 1 := by
  rintro _ ⟨s, u, -, -, rfl⟩
  exact pow_three_tz_mul_yq s u

open CFSG.AGLEmbedding.KFactProofs.G2Q in
private theorem k1471n3_pow_eq_one
    {L : Type} [Field L] {m : ℕ} {ω : Lˣ}
    (h : (tz 1 ω⁻¹ : ModGL .G2 L) ∈ (tzPart m : Subgroup (ModGL .G2 L))) : ω ^ m = 1 := by
  obtain ⟨s, t, -, ht, he⟩ := h
  have h1 : ω⁻¹ ^ m = 1 := by
    rw [(tz_injective he).2]
    exact ht
  rwa [inv_pow, inv_eq_one] at h1

open CFSG.AGLEmbedding.KFactProofs.G2Q in
private theorem k1471n3_four
    {L : Type} [Field L] {m : ℕ} {ω : Lˣ} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) (hωm : ω ^ m = 1) :
    ∃ a ∈ (tzPart m : Subgroup (ModGL .G2 L)), ∃ b ∈ (tzPart m : Subgroup (ModGL .G2 L)),
      ∃ c ∈ (tzPart m : Subgroup (ModGL .G2 L)), ∃ d ∈ (tzPart m : Subgroup (ModGL .G2 L)),
      a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ c ^ 3 = 1 ∧ d ^ 3 = 1 ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
        c ≠ d := by
  have hω2 := k1471n3_pow_two_ne_one hω1 hω3
  have hωω2 := k1471n3_ne_pow_two hω1
  have hcube : ∀ s t : Lˣ, s ^ 3 = 1 → t ^ 3 = 1 → (tz s t : ModGL .G2 L) ^ 3 = 1 := by
    intro s t hs ht
    rw [tz_pow, hs, ht, tz_one_one]
  have hω23 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hω2m : (ω ^ 2) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hωm, one_pow]
  exact ⟨tz 1 1, ⟨1, 1, one_pow m, one_pow m, rfl⟩, tz ω 1, ⟨ω, 1, hωm, one_pow m, rfl⟩,
    tz (ω ^ 2) 1, ⟨ω ^ 2, 1, hω2m, one_pow m, rfl⟩, tz 1 ω, ⟨1, ω, one_pow m, hωm, rfl⟩,
    hcube _ _ (one_pow 3) (one_pow 3), hcube _ _ hω3 (one_pow 3), hcube _ _ hω23 (one_pow 3),
    hcube _ _ (one_pow 3) hω3, fun e => hω1 (tz_injective e).1.symm,
    fun e => hω2 (tz_injective e).1.symm, fun e => hω1 (tz_injective e).2.symm,
    fun e => hωω2 (tz_injective e).1, fun e => hω1 (tz_injective e).1,
    fun e => hω2 (tz_injective e).1⟩

theorem g2_exists_sylow_noncyclic_model
    {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) (hq3 : 3 ≤ Nat.card K) :
    ∃ (S₀ : Sylow 3 (adjointGroup .G2 K)) (T : Subgroup (adjointGroup .G2 K))
      (z : adjointGroup .G2 K),
      T ≤ (S₀ : Subgroup (adjointGroup .G2 K)) ∧ IsMulCommutative ↥T ∧ ¬ IsCyclic ↥T ∧
      (∀ s ∈ (S₀ : Subgroup (adjointGroup .G2 K)), s ∉ T → s ^ 3 = 1) ∧
      (∀ s ∈ (S₀ : Subgroup (adjointGroup .G2 K)), s * z = z * s) ∧ z ∈ T ∧ z ≠ 1 ∧
      z ^ 3 = 1 := by
  open CFSG.AGLEmbedding.KFactProofs.G2Q in
  have : Finite (adjointGroup .G2 K) := CFSG.LieType.Chevalley.generated_group_finite .G2 K
  obtain ⟨Q0, z0, ⟨P, hP⟩, hcenter, hz3, L, _, φ, g, ω, m, hω1, hφ, -, hω3, hmap, hz⟩ :=
    g2_exists_sylow_weakClosure_data h3 hq3
  have hext := ext3_tzPart (L := L) (m := m) hω1
  have hwT0 : (tz 1 ω⁻¹ : ModGL .G2 L) ∈ (tzPart m : Subgroup (ModGL .G2 L)) :=
    k1471n3_mem_of_tor hext (tzPart_le_torusGroup m) (yq_not_mem_torusGroup hω1)
      (k1471n3_mem_ext hext hmap z0 hz) (tz_mem_torusGroup 1 ω⁻¹)
  have hωm : ω ^ m = 1 := k1471n3_pow_eq_one hwT0
  exact k1471n3_model hφ hext (k1471n3_tzPart_comm m) (k1471n3_tzPart_cube m)
    (k1471n3_four hω1 hω3 hωm) hmap P hP z0 hcenter hz3 hz hwT0

theorem sylowNoncyclicOfG2_holds :
    SylowNoncyclicOfG2 := by
  classical
  intro Y _ _ p f hp hp3 hp2 hY
  have hc : CFSG.Blueprint.ChevalleyExceptionalModel Y .G2 p f :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hY (by decide)
  obtain ⟨⟨hrp, -, -, hrf3⟩, hm⟩ := hc
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eY⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (τ := .G2) hm
  have : Finite (adjointGroup .G2 K) := CFSG.LieType.Chevalley.generated_group_finite .G2 K
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hKcard]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq3 : 3 ≤ Nat.card K := by
    rw [hKcard]
    exact hrf3
  obtain ⟨S₀, T, z, hT, hTab, hTnc, hout, hz, hzT, hz1, hz3⟩ :=
    g2_exists_sylow_noncyclic_model h3 hq3
  exact sylowNoncyclicCentralizers_of_mulEquiv eY
    (sylowNoncyclicCentralizers_of_model S₀ T hT hTab hTnc hout hz hzT hz1 hz3)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
