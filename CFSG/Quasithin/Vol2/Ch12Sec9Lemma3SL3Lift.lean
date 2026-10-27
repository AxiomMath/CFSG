module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LinearAlgebra.SteinbergBQPerfectCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3Structure313SL2
public import CFSG.Quasithin.EmptyFaithful.S146B0

public section

namespace CFSG.Quasithin.H13.L1293S

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Perfect

variable {G : Type*} [Group G]

theorem commutatorElement_mul_central_left {a b z : G} (hz : ∀ g, z * g = g * z) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hz]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_central_right {a b z : G} (hz : ∀ g, z * g = g * z) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [hz]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commute_of_perfect {P : Subgroup G} (hP : ⁅P, P⁆ = P) {y : G}
    (h1 : ∀ x ∈ P, ∀ x' ∈ P, ⁅y, x⁆ * x' = x' * ⁅y, x⁆)
    (h2 : ∀ x ∈ P, ∀ x' ∈ P, ⁅y, x⁆ * ⁅y, x'⁆ = ⁅y, x'⁆ * ⁅y, x⁆) :
    ∀ x ∈ P, y * x = x * y := by
  let φ : ↥P →* G :=
    { toFun := fun x => ⁅y, (x : G)⁆
      map_one' := by simp
      map_mul' := fun a b => by
        obtain ⟨a', ha'⟩ := a
        obtain ⟨b', hb'⟩ := b
        show ⁅y, a' * b'⁆ = ⁅y, a'⁆ * ⁅y, b'⁆
        have hb := h1 b' hb' a'⁻¹ (P.inv_mem ha')
        rw [commutatorElement_def] at hb
        rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
        calc y * (a' * b') * y⁻¹ * (a' * b')⁻¹
            = y * a' * y⁻¹ * ((y * b' * y⁻¹ * b'⁻¹) * a'⁻¹) := by group
          _ = y * a' * y⁻¹ * (a'⁻¹ * (y * b' * y⁻¹ * b'⁻¹)) := by rw [hb]
          _ = y * a' * y⁻¹ * a'⁻¹ * (y * b' * y⁻¹ * b'⁻¹) := by group }
  intro x hx
  have := CFSG.LinearAlgebra.SteinbergBQ.eq_one_of_commute_of_perfect hP φ
    (fun a b => h2 a a.2 b b.2) ⟨x, hx⟩
  exact commutatorElement_eq_one_iff_mul_comm.1 this

theorem commute_of_perfect_central {P Z : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hZ : ∀ z ∈ Z, ∀ g : G, z * g = g * z) {y : G} (hy : ∀ x ∈ P, ⁅y, x⁆ ∈ Z) :
    ∀ x ∈ P, y * x = x * y :=
  commute_of_perfect hP (fun x hx x' _ => hZ _ (hy x hx) x')
    (fun x hx _ _ => hZ _ (hy x hx) _)

end Perfect

section Lift

variable {H : Type*} [Group H] {Z₀ : Subgroup H} [Z₀.Normal]

theorem exists_lift (hZc : ∀ z ∈ Z₀, ∀ h : H, z * h = h * z) (hZ3 : ∀ z ∈ Z₀, z ^ 3 = 1)
    {B' : Subgroup (H ⧸ Z₀)} (hperf : ⁅B', B'⁆ = B') {w : H ⧸ Z₀} (hwB : w ∈ B') (hw1 : w ≠ 1)
    (hww : w * w = 1) (hwc : ∀ x ∈ B', x * w = w * x) :
    ∃ B₀ : Subgroup H, ⁅B₀, B₀⁆ = B₀ ∧
      (∃ z ∈ B₀, z ≠ 1 ∧ z * z = 1 ∧ ∀ x ∈ B₀, x * z = z * x) ∧
      Nat.card ↥(Subgroup.centralizer (B' : Set (H ⧸ Z₀))) ∣
        Nat.card ↥(Subgroup.centralizer (B₀ : Set H)) := by
  have hsurj : Function.Surjective (QuotientGroup.mk' Z₀) := QuotientGroup.mk'_surjective Z₀
  set Hh := B'.comap (QuotientGroup.mk' Z₀) with hHh
  set B₀ := ⁅Hh, Hh⁆ with hB₀
  have hmap : B₀.map (QuotientGroup.mk' Z₀) = B' := by
    rw [hB₀, Subgroup.map_commutator, hHh, Subgroup.map_comap_eq_self_of_surjective hsurj, hperf]
  have hB₀Hh : B₀ ≤ Hh := Subgroup.commutator_le.2 fun a ha b hb =>
    Hh.mul_mem (Hh.mul_mem (Hh.mul_mem ha hb) (Hh.inv_mem ha)) (Hh.inv_mem hb)
  have hdec : ∀ h ∈ Hh, ∃ b ∈ B₀, b⁻¹ * h ∈ Z₀ := by
    intro h hh
    have : (QuotientGroup.mk' Z₀) h ∈ B₀.map (QuotientGroup.mk' Z₀) := hmap ▸ hh
    obtain ⟨b, hb, hbh⟩ := this
    exact ⟨b, hb, QuotientGroup.eq.1 hbh⟩
  have hcent : ∀ {u : H}, u ∈ Z₀ → ∀ g : H, u * g = g * u := fun hu g => hZc _ hu g
  have hB₀perf : ⁅B₀, B₀⁆ = B₀ := by
    refine le_antisymm (Subgroup.commutator_mono hB₀Hh hB₀Hh) ?_
    rw [hB₀, Subgroup.commutator_le]
    intro h₁ hh₁ h₂ hh₂
    obtain ⟨b₁, hb₁, hz₁⟩ := hdec h₁ hh₁
    obtain ⟨b₂, hb₂, hz₂⟩ := hdec h₂ hh₂
    have e₁ : h₁ = b₁ * (b₁⁻¹ * h₁) := by group
    have e₂ : h₂ = b₂ * (b₂⁻¹ * h₂) := by group
    rw [e₁, e₂, commutatorElement_mul_central_left (hcent hz₁),
      commutatorElement_mul_central_right (hcent hz₂)]
    exact Subgroup.commutator_mem_commutator hb₁ hb₂
  have hcomm : ∀ c : H, (∀ x ∈ B', x * (QuotientGroup.mk' Z₀) c = (QuotientGroup.mk' Z₀) c * x) →
      ∀ x ∈ B₀, c * x = x * c := by
    intro c hc
    refine commute_of_perfect_central hB₀perf hZc fun x hx => ?_
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (hc ((QuotientGroup.mk' Z₀) x)
      (hmap ▸ Subgroup.mem_map_of_mem (QuotientGroup.mk' Z₀) hx)).symm
  refine ⟨B₀, hB₀perf, ?_, ?_⟩
  ·
    obtain ⟨u, huB, huw⟩ : ∃ u ∈ B₀, (QuotientGroup.mk' Z₀) u = w := by
      have : w ∈ B₀.map (QuotientGroup.mk' Z₀) := hmap ▸ hwB
      obtain ⟨u, hu, rfl⟩ := this
      exact ⟨u, hu, rfl⟩
    have hu2 : u ^ 2 ∈ Z₀ := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, huw, pow_two, hww]
    have hu6 : u ^ 6 = 1 := by
      have := hZ3 _ hu2
      rwa [← pow_mul] at this
    have hπz : (QuotientGroup.mk' Z₀) (u ^ 3) = w := by
      rw [map_pow, huw, pow_succ, pow_two, hww, one_mul]
    refine ⟨u ^ 3, B₀.pow_mem huB 3, fun h => hw1 ?_, ?_, fun x hx => ?_⟩
    · rw [← hπz, h, map_one]
    · rw [← pow_add]
      exact hu6
    · refine (hcomm (u ^ 3) (fun y hy => ?_) x hx).symm
      rw [hπz]
      exact hwc y hy
  · have hle : (Subgroup.centralizer (B' : Set (H ⧸ Z₀))).comap (QuotientGroup.mk' Z₀) ≤
        Subgroup.centralizer (B₀ : Set H) := by
      intro c hc
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hc
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hcomm c hc x hx).symm
    have h1 := Subgroup.card_map_dvd
      ((Subgroup.centralizer (B' : Set (H ⧸ Z₀))).comap (QuotientGroup.mk' Z₀))
      (QuotientGroup.mk' Z₀)
    rw [Subgroup.map_comap_eq_self_of_surjective hsurj] at h1
    exact h1.trans (Subgroup.card_dvd_of_le hle)

end Lift

section Count

variable {X : Type} [Group X]

theorem commutator_eq_self {B : Subgroup X} (h : commutator ↥B = ⊤) : ⁅B, B⁆ = B := by
  have e : (⊤ : Subgroup ↥B).map B.subtype = B := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [commutator_def] at h
  conv_rhs => rw [← e]
  rw [← h, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem sl2_seven_data [Finite X] {B : Subgroup X} (hB : IsSL2 7 ↥B) :
    ⁅B, B⁆ = B ∧ Nat.card B = 336 ∧
      (∃ z ∈ B, z ≠ 1 ∧ z * z = 1 ∧ ∀ x ∈ B, x * z = z * x) ∧
      ∀ y ∈ pCoreOf 2 B, y ∈ B ∧ ∀ x ∈ B, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : Nat.Prime 7 := by norm_num
  have hq := A313.IsSL2.isQuasisimple hp (by norm_num) hB
  have hcomm : commutator ↥B = ⊤ := hq.1.commutator_eq_top
  have hcard : Nat.card B = 336 := by rw [A313.IsSL2.card_eq hp hB]; norm_num
  have hZ := A313.IsSL2.card_center hp (by norm_num) hB
  refine ⟨commutator_eq_self hcomm, hcard, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥B) 2 (by rw [hZ])
    have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; norm_num at ht
    refine ⟨((t : ↥B) : X), (t : ↥B).2, fun h => ht1 ?_, ?_, fun x hx => ?_⟩
    · exact Subtype.ext (Subtype.ext h)
    · have := pow_orderOf_eq_one t
      rw [ht, pow_two] at this
      exact congrArg (fun s : Subgroup.center ↥B => ((s : ↥B) : X)) this
    · have := Subgroup.mem_center_iff.1 t.2 ⟨x, hx⟩
      exact congrArg Subtype.val this
  · intro y hy
    have hyB : y ∈ B := LieType.BorelTits.pCoreOf_le 2 B hy
    refine ⟨hyB, fun x hx => ?_⟩
    have hn : ((pCoreOf 2 B).subgroupOf B).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (LieType.BorelTits.pCoreOf_le 2 B)).2
        (LieType.BorelTits.le_normalizer_pCoreOf 2 B)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hn with h | h
    · exfalso
      have hBP : B ≤ pCoreOf 2 B := fun x hx => by
        have : (⟨x, hx⟩ : B) ∈ (pCoreOf 2 B).subgroupOf B := by rw [h]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.1 this
      obtain ⟨k, hk⟩ := (LieType.BorelTits.pCoreOf_isPGroup 2 B).exists_card_eq
      have hle := Subgroup.card_dvd_of_le hBP
      rw [hcard, hk] at hle
      have h3 : 3 ∣ 2 ^ k := (by norm_num : 3 ∣ 336).trans hle
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    · have hyZ : (⟨y, hyB⟩ : B) ∈ Subgroup.center ↥B := h (Subgroup.mem_subgroupOf.2 hy)
      have := Subgroup.mem_center_iff.1 hyZ ⟨x, hx⟩
      exact congrArg Subtype.val this

theorem card_sylow_dvd [Finite X] {B K S : Subgroup X} (hBK : B ≤ K) (hB : IsSL2 7 ↥B)
    (hS : QuasithinUnique.IsSylowTwoOf S K) (hall : ∀ s ∈ S, ¬ KbarInducesOuter B s) :
    Nat.card S ∣ 168 * Nat.card ↥(K ⊓ Subgroup.centralizer (B : Set X)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hperf, hcard, ⟨z, hzB, hz1, hzz, hzc⟩, hO2⟩ := sl2_seven_data hB
  obtain ⟨hSK, -, -⟩ := hS
  set C := K ⊓ Subgroup.centralizer (B : Set X) with hC
  have hdec : ∀ s ∈ S, ∃ b ∈ B, s * b⁻¹ ∈ C := by
    intro s hs
    have h := hall s hs
    simp only [KbarInducesOuter, not_forall, not_exists, not_and, not_not] at h
    obtain ⟨b, hb, hall'⟩ := h
    refine ⟨b, hb, K.mul_mem (hSK hs) (K.inv_mem (hBK hb)), ?_⟩
    show s * b⁻¹ ∈ Subgroup.centralizer (B : Set X)
    have hnorm : ∀ x ∈ B, ⁅s * b⁻¹, x⁆ ∈ B := fun x hx => (hO2 _ (hall' x hx)).1
    have key := commute_of_perfect hperf (y := s * b⁻¹)
      (fun x hx x' hx' => ((hO2 _ (hall' x hx)).2 x' hx').symm)
      (fun x hx x' hx' => ((hO2 _ (hall' x hx)).2 _ (hnorm x' hx')).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (key x hx).symm
  have hzC : z ∈ C := ⟨hBK hzB, Subgroup.mem_centralizer_iff.2 fun x hx => hzc x hx⟩
  let f : ↥C × ↥B →* X := MonoidHom.noncommCoprod C.subtype B.subtype
    (fun c b => (Subgroup.mem_centralizer_iff.1 c.2.2 b b.2).symm)
  have hf : ∀ c b, f (c, b) = (c : X) * b := fun c b => rfl
  have hSf : S ≤ f.range := by
    intro s hs
    obtain ⟨b, hb, hsb⟩ := hdec s hs
    exact ⟨(⟨s * b⁻¹, hsb⟩, ⟨b, hb⟩), by rw [hf]; group⟩
  set t : ↥f.ker := ⟨(⟨z, hzC⟩, ⟨z, hzB⟩), by rw [MonoidHom.mem_ker, hf]; exact hzz⟩ with ht
  have ht2 : orderOf t = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      apply Prod.ext <;> apply Subtype.ext <;> simp [ht, pow_two, hzz]
    · intro h
      apply hz1
      have := congrArg (fun u : ↥f.ker => (((u : ↥C × ↥B).1 : ↥C) : X)) h
      simpa [ht] using this
  have h2ker : 2 ∣ Nat.card f.ker := ht2 ▸ orderOf_dvd_natCard t
  have hprod : Nat.card f.range * Nat.card f.ker = Nat.card C * 336 := by
    rw [← Subgroup.index_ker, mul_comm f.ker.index, Subgroup.card_mul_index, Nat.card_prod, hcard]
  have h1 := Nat.mul_dvd_mul (Subgroup.card_dvd_of_le hSf) h2ker
  rw [hprod, show Nat.card ↥C * 336 = 168 * Nat.card ↥C * 2 by ring] at h1
  exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1

theorem two_pow_dvd_card {S K : Subgroup X} (hS : QuasithinUnique.IsSylowTwoOf S K) {j : ℕ}
    (h : 2 ^ j ∣ Nat.card K) : 2 ^ j ∣ Nat.card S := by
  obtain ⟨hSK, -, hidx⟩ := hS
  have h1 := (S.subgroupOf K).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv] at h1
  rw [← h1] at h
  exact (Nat.Coprime.pow_left j
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hidx)).dvd_of_dvd_mul_right h

theorem card_centralizer_eq {M : Type*} [Group M] {B K : Subgroup X} (hBK : B ≤ K)
    (e : ↥K ≃* M) :
    Nat.card ↥(K ⊓ Subgroup.centralizer (B : Set X)) =
      Nat.card ↥(Subgroup.centralizer
        (((B.subgroupOf K).map e.toMonoidHom : Subgroup M) : Set M)) := by
  set C := K ⊓ Subgroup.centralizer (B : Set X) with hC
  have hCK : C ≤ K := inf_le_left
  have hmap : (C.subgroupOf K).map e.toMonoidHom = Subgroup.centralizer
      (((B.subgroupOf K).map e.toMonoidHom : Subgroup M) : Set M) := by
    ext m
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have hkc : (k : X) ∈ Subgroup.centralizer (B : Set X) := (Subgroup.mem_subgroupOf.1 hk).2
      rw [Subgroup.mem_centralizer_iff] at hkc
      have hbk : b * k = k * b := Subtype.ext (hkc b (Subgroup.mem_subgroupOf.1 hb))
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hbk]
    · intro hm
      refine ⟨e.symm m, Subgroup.mem_subgroupOf.2 ⟨(e.symm m).2, ?_⟩, by simp⟩
      show ((e.symm m : ↥K) : X) ∈ Subgroup.centralizer (B : Set X)
      rw [Subgroup.mem_centralizer_iff] at hm ⊢
      intro x hx
      have h := hm (e ⟨x, hBK hx⟩) ⟨⟨x, hBK hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      have h' := congrArg e.symm h
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h'
      exact congrArg Subtype.val h'
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv,
    ← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap]

end Count

end CFSG.Quasithin.H13.L1293S
