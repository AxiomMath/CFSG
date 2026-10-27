module

public import CFSG.RankThree.PartOne.S12.Sec15Frattini
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeSylow
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.RankThree.PartOne

open StrongP

namespace Sec1514Five

variable {G : Type} [Group G]

theorem exists_of_mem_conjSub {g x : G} {Y : Subgroup G} (h : x ∈ conjSub g Y) :
    ∃ z ∈ Y, x = g * z * g⁻¹ := ⟨g⁻¹ * x * g, mem_conjSub_iff.1 h, by group⟩

theorem mem_conjSub_of_mem {g z : G} {Y : Subgroup G} (h : z ∈ Y) : g * z * g⁻¹ ∈ conjSub g Y := by
  rw [mem_conjSub_iff]
  have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
  rwa [e]

theorem conjSub_mul (g h : G) (Y : Subgroup G) : conjSub (g * h) Y = conjSub g (conjSub h Y) := by
  ext x
  rw [mem_conjSub_iff, mem_conjSub_iff, mem_conjSub_iff]
  have e : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
  rw [e]

theorem conjSub_eq_of_centralizes {g : G} {Y : Subgroup G} (hg : ∀ y ∈ Y, y * g = g * y) :
    conjSub g Y = Y := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro h
    have h1 : (g⁻¹ * x * g) * g = g * (g⁻¹ * x * g) := hg _ h
    have e : x = g⁻¹ * x * g := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = (g⁻¹ * x * g) * g * g⁻¹ := by rw [h1]
        _ = g⁻¹ * x * g := by group
    rw [e]
    exact h
  · intro h
    have h1 : x * g = g * x := hg x h
    have e : g⁻¹ * x * g = x := by
      calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
        _ = g⁻¹ * (g * x) := by rw [h1]
        _ = x := by group
    rw [e]
    exact h

section Fin

variable [Finite G]

theorem mem_normalizer_of_forall {M : Subgroup G} {g : G} (h : ∀ x ∈ M, g * x * g⁻¹ ∈ M) :
    g ∈ Subgroup.normalizer (M : Set G) := by
  have hle : conjSub g M ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : conjSub g M = M := Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h1 : g * x * g⁻¹ ∈ conjSub g M := by rw [heq]; exact hx
  rw [mem_conjSub_iff] at h1
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rwa [e] at h1

theorem exists_conj_normalized {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K S B : Subgroup G}
    (hKodd : ¬ 2 ∣ Nat.card K) (hKp : ¬ p ∣ Nat.card K) (hS : IsPGroup 2 S) (hB : IsPGroup p B)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hBM : B ≤ Subgroup.normalizer ((K ⊔ S : Subgroup G) : Set G)) :
    ∃ k ∈ K, B ≤ Subgroup.normalizer ((conjSub k S : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := K ⊔ S with hM
  have hKM : K ≤ M := le_sup_left
  have hSM : S ≤ M := le_sup_right
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hSK
  set K' : Subgroup ↥M := K.subgroupOf M with hK'
  set S' : Subgroup ↥M := S.subgroupOf M with hS'
  have hK'n : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hMK
  have hK'card : Nat.card K' = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have hS'2 : IsPGroup 2 S' := hS.comap_subtype
  have hK'odd : ¬ 2 ∣ Nat.card K' := by rw [hK'card]; exact hKodd
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 2 S' (K' ⊔ S') :=
    Sec15Frattini.isSylowOf_sup_of_coprime hS'2 hK'odd
  have htop : K' ⊔ S' = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_sup, hK', hS', Subgroup.map_subgroupOf_eq_of_le hKM,
      Subgroup.map_subgroupOf_eq_of_le hSM, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [htop] at hsyl
  have hMp : ¬ p ∣ Nat.card ↥M := by
    have h1 := Subgroup.card_mul_index K'
    have h2 : K'.index = K'.relIndex S' := by
      rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_left]
    have h3 : K'.relIndex S' ∣ Nat.card S' := Subgroup.relIndex_dvd_card _ _
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hS'2
    intro hdvd
    rw [← h1] at hdvd
    rcases (Nat.Prime.dvd_mul Fact.out).1 hdvd with h | h
    · exact hKp (by rwa [hK'card] at h)
    · have h5 : K'.index ∣ Nat.card S' := by rw [h2]; exact h3
      have h4 : p ∣ 2 ^ n := by rw [← hn]; exact h.trans h5
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
        (Nat.Prime.dvd_of_dvd_pow Fact.out h4))
  let : MulDistribMulAction ↥B ↥M := Subgroup.conjMulDistribMulActionOfLeNormalizer B M hBM
  obtain ⟨Q, hQ⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.coprime_pgroup_exists_invariant_sylow
    (G := ↥M) (A := ↥B) p 2 hB hMp
  have hQ' : CFSG.ABGLocalTools.IsSylowOf 2 (Q : Subgroup ↥M) ⊤ := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_top, Q.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Q.not_dvd_index
  obtain ⟨g, -, hg⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hsyl hQ'
  have hgmem : g ∈ K' ⊔ S' := by rw [htop]; exact Subgroup.mem_top g
  obtain ⟨y, hyK', z, hzS', rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hgmem
  have hy : ∀ x : ↥M, x ∈ (Q : Subgroup ↥M) ↔ y⁻¹ * x * y ∈ S' := by
    intro x
    rw [hg x]
    have h1 : (y * z)⁻¹ * x * (y * z) = z⁻¹ * (y⁻¹ * x * y) * z := by group
    rw [h1]
    constructor
    · intro h
      have := S'.mul_mem (S'.mul_mem hzS' h) (S'.inv_mem hzS')
      have e : z * (z⁻¹ * (y⁻¹ * x * y) * z) * z⁻¹ = y⁻¹ * x * y := by group
      rwa [e] at this
    · intro h
      exact S'.mul_mem (S'.mul_mem (S'.inv_mem hzS') h) hzS'
  have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.1 hyK'
  refine ⟨(y : G), hyK, ?_⟩
  have hfwd : ∀ b ∈ B, ∀ x : G, x ∈ conjSub (y : G) S → b * x * b⁻¹ ∈ conjSub (y : G) S := by
    intro b hb x hx
    have hxS : (y : G)⁻¹ * x * (y : G) ∈ S := mem_conjSub_iff.1 hx
    have hxM : x ∈ M := by
      have e : x = (y : G) * ((y : G)⁻¹ * x * (y : G)) * (y : G)⁻¹ := by group
      rw [e]
      exact M.mul_mem (M.mul_mem y.2 (hSM hxS)) (M.inv_mem y.2)
    set m : ↥M := ⟨x, hxM⟩ with hm
    have hmQ : m ∈ (Q : Subgroup ↥M) := by
      rw [hy m]
      exact hxS
    have hbmQ := hQ ⟨b, hb⟩ m hmQ
    have hbm : (((⟨b, hb⟩ : ↥B) • m : ↥M) : G) = b * x * b⁻¹ := rfl
    have h1 := (hy _).1 hbmQ
    have h2 : (y : G)⁻¹ * (b * x * b⁻¹) * (y : G) ∈ S := by
      have h3 : (((y⁻¹ * ((⟨b, hb⟩ : ↥B) • m) * y : ↥M)) : G) =
          (y : G)⁻¹ * (b * x * b⁻¹) * (y : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hbm]
      rw [← h3]
      exact h1
    rw [mem_conjSub_iff]
    exact h2
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hfwd b hb x hx, fun hx => ?_⟩
  have h1 := hfwd b⁻¹ (B.inv_mem hb) _ hx
  have e : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem exists_pair_lift {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {N K Z S A B : Subgroup G}
    (hKN : K ≤ N) (hNK : N ≤ Subgroup.normalizer (K : Set G))
    (hKodd : ¬ 2 ∣ Nat.card K) (hKp : ¬ p ∣ Nat.card K)
    (hZ : IsPGroup 2 Z) (hS : IsPGroup 2 S) (hA : IsPGroup p A) (hBA : B ≤ A)
    (hZN : Z ≤ N) (hSN : S ≤ N) (hAN : A ≤ N)
    (hZS : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z)
    (hAZ : ∀ a ∈ A, ∀ z ∈ Z, a * z * a⁻¹ * z⁻¹ ∈ K)
    (hBS : ∀ b ∈ B, ∀ s ∈ S, ∃ s' ∈ S, b * s * b⁻¹ * s'⁻¹ ∈ K) :
    ∃ k ∈ K, A ≤ Subgroup.centralizer ((conjSub k Z : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer ((conjSub k S : Subgroup G) : Set G) := by
  classical
  have hconjK : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K :=
    fun n hn k hk => (Subgroup.mem_normalizer_iff.1 (hNK hn) k).1 hk
  have hZnorm : Z ≤ Subgroup.normalizer (K : Set G) := hZN.trans hNK
  have hAM : A ≤ Subgroup.normalizer ((K ⊔ Z : Subgroup G) : Set G) := by
    intro a ha
    apply mem_normalizer_of_forall
    intro x hx
    have hx' : x ∈ ((K ⊔ Z : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K Z hZnorm] at hx'
    obtain ⟨k, hk, z, hz, rfl⟩ := hx'
    have e : a * (k * z) * a⁻¹ = (a * k * a⁻¹) * ((a * z * a⁻¹ * z⁻¹) * z) := by group
    rw [e]
    exact (K ⊔ Z).mul_mem (Subgroup.mem_sup_left (hconjK a (hAN ha) k hk))
      ((K ⊔ Z).mul_mem (Subgroup.mem_sup_left (hAZ a ha z hz)) (Subgroup.mem_sup_right hz))
  obtain ⟨κ₁, hκ₁K, hκ₁⟩ := exists_conj_normalized hp2 hKodd hKp hZ hA hZnorm hAM
  have hκ₁N : κ₁ ∈ N := hKN hκ₁K
  set Z₁ : Subgroup G := conjSub κ₁ Z with hZ₁
  set S₁ : Subgroup G := conjSub κ₁ S with hS₁
  have hZ₁2 : IsPGroup 2 Z₁ := hZ.map _
  have hS₁2 : IsPGroup 2 S₁ := hS.map _
  have hdisj : Disjoint Z₁ K := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZ₁2
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hKodd)
  have hAC : ∀ a ∈ A, ∀ y ∈ Z₁, y * a = a * y := by
    intro a ha y hy
    obtain ⟨z, hz, hyz⟩ := exists_of_mem_conjSub hy
    have hzN : z ∈ N := hZN hz
    have hk' : z⁻¹ * κ₁ * z * κ₁⁻¹ ∈ K := by
      have h1 : z⁻¹ * κ₁ * z ∈ K := by
        have := hconjK z⁻¹ (N.inv_mem hzN) κ₁ hκ₁K
        rwa [inv_inv] at this
      exact K.mul_mem h1 (K.inv_mem hκ₁K)
    set k' := z⁻¹ * κ₁ * z * κ₁⁻¹ with hk'def
    have hyk : y = z * k' := by rw [hyz, hk'def]; group
    have hayZ : a * y * a⁻¹ ∈ Z₁ := (Subgroup.mem_normalizer_iff.1 (hκ₁ ha) y).1 hy
    have hcZ : a * y * a⁻¹ * y⁻¹ ∈ Z₁ := Z₁.mul_mem hayZ (Z₁.inv_mem hy)
    have hcK : a * y * a⁻¹ * y⁻¹ ∈ K := by
      have e : a * y * a⁻¹ * y⁻¹ =
          (a * z * a⁻¹ * z⁻¹) * (z * (a * k' * a⁻¹ * k'⁻¹) * z⁻¹) := by rw [hyk]; group
      rw [e]
      refine K.mul_mem (hAZ a ha z hz) (hconjK z hzN _ ?_)
      exact K.mul_mem (hconjK a (hAN ha) k' hk') (K.inv_mem hk')
    have hc1 : a * y * a⁻¹ * y⁻¹ = 1 := Subgroup.disjoint_def.1 hdisj hcZ hcK
    have h2 : a * y * a⁻¹ = y := mul_inv_eq_one.1 hc1
    calc y * a = (a * y * a⁻¹) * a := by rw [h2]
      _ = a * y := by group
  have hZ₁S₁ : ∀ y ∈ Z₁, ∀ s ∈ S₁, y * s = s * y := by
    intro y hy s hs
    obtain ⟨z, hz, rfl⟩ := exists_of_mem_conjSub hy
    obtain ⟨s₀, hs₀, rfl⟩ := exists_of_mem_conjSub hs
    have := hZS z hz s₀ hs₀
    calc κ₁ * z * κ₁⁻¹ * (κ₁ * s₀ * κ₁⁻¹) = κ₁ * (z * s₀) * κ₁⁻¹ := by group
      _ = κ₁ * (s₀ * z) * κ₁⁻¹ := by rw [this]
      _ = κ₁ * s₀ * κ₁⁻¹ * (κ₁ * z * κ₁⁻¹) := by group
  set K₁ : Subgroup G := K ⊓ Subgroup.centralizer (Z₁ : Set G) with hK₁
  have hK₁K : K₁ ≤ K := inf_le_left
  have hK₁odd : ¬ 2 ∣ Nat.card K₁ := fun h => hKodd (h.trans (Subgroup.card_dvd_of_le hK₁K))
  have hK₁p : ¬ p ∣ Nat.card K₁ := fun h => hKp (h.trans (Subgroup.card_dvd_of_le hK₁K))
  have hS₁N : S₁ ≤ N := by
    intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := exists_of_mem_conjSub hs
    exact N.mul_mem (N.mul_mem hκ₁N (hSN hs₀)) (N.inv_mem hκ₁N)
  have hS₁C : ∀ s ∈ S₁, ∀ y ∈ Z₁, y * s = s * y := fun s hs y hy => hZ₁S₁ y hy s hs
  have hS₁K₁ : S₁ ≤ Subgroup.normalizer (K₁ : Set G) := by
    intro s hs
    apply mem_normalizer_of_forall
    intro x hx
    refine ⟨hconjK s (hS₁N hs) x (hK₁K hx), Subgroup.mem_centralizer_iff.2 ?_⟩
    intro y hy
    have hxy : y * x = x * y := Subgroup.mem_centralizer_iff.1 hx.2 y hy
    have hys : y * s = s * y := hS₁C s hs y hy
    have hys' : y * s⁻¹ = s⁻¹ * y := by
      calc y * s⁻¹ = s⁻¹ * (s * y) * s⁻¹ := by group
        _ = s⁻¹ * (y * s) * s⁻¹ := by rw [hys]
        _ = s⁻¹ * y := by group
    calc y * (s * x * s⁻¹) = (y * s) * x * s⁻¹ := by group
      _ = s * (y * x) * s⁻¹ := by rw [hys]; group
      _ = s * (x * y) * s⁻¹ := by rw [hxy]
      _ = s * x * (y * s⁻¹) := by group
      _ = s * x * (s⁻¹ * y) := by rw [hys']
      _ = (s * x * s⁻¹) * y := by group
  have hB : IsPGroup p B := hA.to_le hBA
  have hBC : ∀ b ∈ B, ∀ y ∈ Z₁, y * b = b * y := fun b hb y hy => hAC b (hBA hb) y hy
  have hBM₁ : B ≤ Subgroup.normalizer ((K₁ ⊔ S₁ : Subgroup G) : Set G) := by
    intro b hb
    have hbN : b ∈ N := hAN (hBA hb)
    have hs : ∀ s ∈ S₁, b * s * b⁻¹ ∈ K₁ ⊔ S₁ := by
      intro s hs
      obtain ⟨s₀, hs₀, rfl⟩ := exists_of_mem_conjSub hs
      obtain ⟨s₀', hs₀', hd⟩ := hBS b hb s₀ hs₀
      set s' : G := κ₁ * s₀' * κ₁⁻¹ with hs'
      have hs'mem : s' ∈ S₁ := mem_conjSub_of_mem hs₀'
      have hs₀N : s₀ ∈ N := hSN hs₀
      have hs₀'N : s₀' ∈ N := hSN hs₀'
      have hk₁ : κ₁ * (s₀ * κ₁⁻¹ * s₀⁻¹) ∈ K :=
        K.mul_mem hκ₁K (hconjK s₀ hs₀N κ₁⁻¹ (K.inv_mem hκ₁K))
      have hk₁' : κ₁ * (s₀' * κ₁⁻¹ * s₀'⁻¹) ∈ K :=
        K.mul_mem hκ₁K (hconjK s₀' hs₀'N κ₁⁻¹ (K.inv_mem hκ₁K))
      have hmodK : b * (κ₁ * s₀ * κ₁⁻¹) * b⁻¹ * s'⁻¹ ∈ K := by
        have e : b * (κ₁ * s₀ * κ₁⁻¹) * b⁻¹ * s'⁻¹ =
            (b * (κ₁ * (s₀ * κ₁⁻¹ * s₀⁻¹)) * b⁻¹) * (b * s₀ * b⁻¹ * s₀'⁻¹) *
              (κ₁ * (s₀' * κ₁⁻¹ * s₀'⁻¹))⁻¹ := by rw [hs']; group
        rw [e]
        exact K.mul_mem (K.mul_mem (hconjK b hbN _ hk₁) hd) (K.inv_mem hk₁')
      have hmodC : b * (κ₁ * s₀ * κ₁⁻¹) * b⁻¹ * s'⁻¹ ∈ Subgroup.centralizer (Z₁ : Set G) := by
        have hsC : κ₁ * s₀ * κ₁⁻¹ ∈ Subgroup.centralizer (Z₁ : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact hS₁C _ (mem_conjSub_of_mem hs₀) y hy
        have hs'C : s' ∈ Subgroup.centralizer (Z₁ : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact hS₁C _ hs'mem y hy
        have hbC' : b ∈ Subgroup.centralizer (Z₁ : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact hBC b hb y hy
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hbC' hsC)
          (Subgroup.inv_mem _ hbC')) (Subgroup.inv_mem _ hs'C)
      have hmem : b * (κ₁ * s₀ * κ₁⁻¹) * b⁻¹ * s'⁻¹ ∈ K₁ := ⟨hmodK, hmodC⟩
      have e : b * (κ₁ * s₀ * κ₁⁻¹) * b⁻¹ =
          (b * (κ₁ * s₀ * κ₁⁻¹) * b⁻¹ * s'⁻¹) * s' := by group
      rw [e]
      exact (K₁ ⊔ S₁).mul_mem (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right hs'mem)
    apply mem_normalizer_of_forall
    intro x hx
    have hx' : x ∈ ((K₁ ⊔ S₁ : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K₁ S₁ hS₁K₁] at hx'
    obtain ⟨k, hk, s, hs', rfl⟩ := hx'
    have hkc : b * k * b⁻¹ ∈ K₁ := by
      refine ⟨hconjK b hbN k (hK₁K hk), Subgroup.mem_centralizer_iff.2 ?_⟩
      intro y hy
      have h1 : y * k = k * y := Subgroup.mem_centralizer_iff.1 hk.2 y hy
      have h2 : y * b = b * y := hBC b hb y hy
      have h3 : y * b⁻¹ = b⁻¹ * y := by
        calc y * b⁻¹ = b⁻¹ * (b * y) * b⁻¹ := by group
          _ = b⁻¹ * (y * b) * b⁻¹ := by rw [h2]
          _ = b⁻¹ * y := by group
      calc y * (b * k * b⁻¹) = (y * b) * k * b⁻¹ := by group
        _ = b * (y * k) * b⁻¹ := by rw [h2]; group
        _ = b * (k * y) * b⁻¹ := by rw [h1]
        _ = b * k * (y * b⁻¹) := by group
        _ = b * k * (b⁻¹ * y) := by rw [h3]
        _ = (b * k * b⁻¹) * y := by group
    have e : b * (k * s) * b⁻¹ = (b * k * b⁻¹) * (b * s * b⁻¹) := by group
    rw [e]
    exact (K₁ ⊔ S₁).mul_mem (Subgroup.mem_sup_left hkc) (hs s hs')
  obtain ⟨κ₂, hκ₂K₁, hκ₂⟩ := exists_conj_normalized hp2 hK₁odd hK₁p hS₁2 hB hS₁K₁ hBM₁
  have hκ₂C : ∀ y ∈ Z₁, y * κ₂ = κ₂ * y := fun y hy =>
    Subgroup.mem_centralizer_iff.1 hκ₂K₁.2 y hy
  have hZk : conjSub (κ₂ * κ₁) Z = Z₁ := by
    rw [conjSub_mul]
    exact conjSub_eq_of_centralizes hκ₂C
  have hSk : conjSub (κ₂ * κ₁) S = conjSub κ₂ S₁ := conjSub_mul κ₂ κ₁ S
  refine ⟨κ₂ * κ₁, K.mul_mem (hK₁K hκ₂K₁) hκ₁K, ?_, ?_⟩
  · rw [hZk]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hAC a ha y hy
  · rw [hSk]
    exact hκ₂

end Fin

end Sec1514Five

end CFSG.RankThree.PartOne
