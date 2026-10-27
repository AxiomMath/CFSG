module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin.SzVB.KerAux

open scoped Pointwise

theorem mem_normalizer_of_mk_mem_center {H : Type*} [Group H] {N T : Subgroup H} [N.Normal]
    (hNT : N ≤ T) {k : H} (hk : (k : H ⧸ N) ∈ Subgroup.center (H ⧸ N)) :
    k ∈ Subgroup.normalizer (T : Set H) := by
  have key : ∀ {k : H}, (k : H ⧸ N) ∈ Subgroup.center (H ⧸ N) → ∀ t ∈ T, k * t * k⁻¹ ∈ T := by
    intro k hk t ht
    have hc := Subgroup.mem_center_iff.mp hk (t : H ⧸ N)
    have h1 : ((k * t * k⁻¹ : H) : H ⧸ N) = (t : H ⧸ N) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hc,
        mul_inv_cancel_right]
    have h2 : (k * t * k⁻¹)⁻¹ * t ∈ N := QuotientGroup.eq.mp h1
    have h3 : k * t * k⁻¹ = t * ((k * t * k⁻¹)⁻¹ * t)⁻¹ := by group
    rw [h3]
    exact T.mul_mem ht (T.inv_mem (hNT h2))
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨fun ht => key hk t ht, fun ht => ?_⟩
  have hk' : ((k⁻¹ : H) : H ⧸ N) ∈ Subgroup.center (H ⧸ N) := by
    rw [QuotientGroup.mk_inv]
    exact Subgroup.inv_mem _ hk
  have h4 := key hk' _ ht
  have h5 : k⁻¹ * (k * t * k⁻¹) * k⁻¹⁻¹ = t := by group
  rw [h5] at h4
  exact h4

theorem le_ker_of_simple {H Q : Type*} [Group H] [Group Q] [IsSimpleGroup Q] (θ : H →* Q)
    (hθ : Function.Surjective θ) {R B : Subgroup H} [R.Normal] (hRB : R ≤ B)
    (hker : θ.ker ≤ B) (hB : B ≠ ⊤) : R ≤ θ.ker := by
  have : (R.map θ).Normal := (inferInstance : R.Normal).map θ hθ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.map θ) with h | h
  · exact (Subgroup.map_eq_bot_iff R).mp h
  · exfalso
    apply hB
    rw [eq_top_iff]
    intro g _
    have hg : θ g ∈ R.map θ := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨r, hr, hrg⟩ := hg
    have hmem : r⁻¹ * g ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrg, inv_mul_cancel]
    have := B.mul_mem (hRB hr) (hker hmem)
    simpa using this

theorem comm_mem_of_perfect {H Q : Type*} [Group H] [Group Q] [Group.IsPerfect H]
    [IsSimpleGroup Q] {N T R : Subgroup H} [N.Normal] [R.Normal] (hNT : N ≤ T)
    (ψ : H ⧸ N →* Q) (hψ : Function.Surjective ψ) (hψc : ψ.ker ≤ Subgroup.center (H ⧸ N))
    (hT : Subgroup.normalizer (T : Set H) ≠ ⊤) (hRT : R ≤ Subgroup.normalizer (T : Set H))
    (φ : H →* H) (hφ : ∀ x, φ x * x⁻¹ ∈ R) (x : H) : φ x * x⁻¹ ∈ N := by
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  have hθs : Function.Surjective (ψ.comp π) := hψ.comp (QuotientGroup.mk'_surjective N)
  have hker : (ψ.comp π).ker ≤ Subgroup.normalizer (T : Set H) := fun k hk =>
    mem_normalizer_of_mk_mem_center hNT
      (hψc (show π k ∈ ψ.ker from MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hk)))
  have hR : R ≤ (ψ.comp π).ker := le_ker_of_simple (ψ.comp π) hθs hRT hker hT
  have hR' : ∀ y : H, π (φ y * y⁻¹) ∈ ψ.ker := fun y =>
    MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (hR (hφ y)))
  have hc : ∀ y : H, π (φ y) * (π y)⁻¹ ∈ Subgroup.center (H ⧸ N) := fun y => by
    have := hψc (hR' y)
    rwa [map_mul, map_inv] at this
  let δ : H →* H ⧸ N := MonoidHom.mk' (fun y => π (φ y) * (π y)⁻¹) (fun a b => by
    have h1 := Subgroup.mem_center_iff.mp (hc b) (π a)⁻¹
    calc π (φ (a * b)) * (π (a * b))⁻¹
        = π (φ a) * (π (φ b) * (π b)⁻¹ * (π a)⁻¹) := by
          simp only [map_mul, mul_inv_rev]; group
      _ = π (φ a) * ((π a)⁻¹ * (π (φ b) * (π b)⁻¹)) := by rw [← h1]
      _ = (π (φ a) * (π a)⁻¹) * (π (φ b) * (π b)⁻¹) := by group)
  have hδc : ∀ y : H, δ y ∈ Subgroup.center (H ⧸ N) := hc
  have hδ : ∀ y : H, δ y = 1 := by
    have hle : commutator H ≤ δ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact Commute.commutator_eq (Subgroup.mem_center_iff.mp (hδc a) (δ b)).symm
    exact fun y => hle Group.IsPerfect.mem_commutator
  have h1 : π (φ x * x⁻¹) = 1 := by
    rw [map_mul, map_inv]
    exact hδ x
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem mem_of_mul_self_mem_of_odd {G : Type*} [Group G] {B T : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (T : Set G)) (hodd : ¬ 2 ∣ (T.subgroupOf B).index) {k : G}
    (hk : k ∈ B) (hk2 : k * k ∈ T) : k ∈ T := by
  have : (T.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hBN
  let k' : ↥B := ⟨k, hk⟩
  have hsq : (QuotientGroup.mk k' : ↥B ⧸ T.subgroupOf B) ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hk2
  have h1 := orderOf_dvd_of_pow_eq_one hsq
  have h2 : orderOf (QuotientGroup.mk k' : ↥B ⧸ T.subgroupOf B) ∣ (T.subgroupOf B).index :=
    orderOf_dvd_natCard _
  have hcop : Nat.Coprime 2 (T.subgroupOf B).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
  have h4 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h5 := orderOf_eq_one_iff.mp h4
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff k').mp h5)

theorem mem_of_mul_self_mem {G : Type*} [Group G] {K T : Subgroup G} (hTK : T ≤ K)
    (hodd : ¬ 2 ∣ (T.subgroupOf K).index) {k : G} (hk : k ∈ K)
    (hkN : k ∈ Subgroup.normalizer (T : Set G)) (hk2 : k * k ∈ T) : k ∈ T := by
  have hTB : T ≤ K ⊓ Subgroup.normalizer (T : Set G) := le_inf hTK Subgroup.le_normalizer
  have h3 : T.relIndex (K ⊓ Subgroup.normalizer (T : Set G)) ∣ T.relIndex K :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex T _ K hTB inf_le_left)
  exact mem_of_mul_self_mem_of_odd (B := K ⊓ Subgroup.normalizer (T : Set G)) inf_le_right
    (fun h => hodd (h.trans h3)) ⟨hk, hkN⟩ hk2

theorem mem_of_sq_eq_one {G : Type*} [Group G] {K S O Y : Subgroup G}
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hodd : ¬ 2 ∣ ((S ⊓ K).subgroupOf K).index) (hOT : O ≤ S ⊓ K) (hYP : Y ≤ K ⊔ S)
    (hcomm : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ O)
    {y : G} (hy : y ∈ Y) (hy2 : y * y = 1) : y ∈ S := by
  have hmem : y ∈ (K : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left K S hSK]
    exact hYP hy
  obtain ⟨k, hk, s, hs, hks⟩ := hmem
  subst hks
  have hyT : ∀ z ∈ Y, ∀ t ∈ S ⊓ K, z * t * z⁻¹ ∈ S ⊓ K := by
    intro z hz t ht
    have h1 := hcomm z hz t ht.2
    have h2 : z * t * z⁻¹ = (z * t * z⁻¹ * t⁻¹) * t := by group
    rw [h2]
    exact (S ⊓ K).mul_mem (hOT h1) ht
  have hyN : k * s ∈ Subgroup.normalizer ((S ⊓ K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨fun ht => hyT _ hy t ht, fun ht => ?_⟩
    have h4 := hyT _ (Y.inv_mem hy) _ ht
    have h5 : (k * s)⁻¹ * ((k * s) * t * (k * s)⁻¹) * (k * s)⁻¹⁻¹ = t := by group
    rw [h5] at h4
    exact h4
  have hsN : s ∈ Subgroup.normalizer ((S ⊓ K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have hsS := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hs) t
    have hsK := Subgroup.mem_normalizer_iff.mp (hSK hs) t
    show t ∈ S ⊓ K ↔ s * t * s⁻¹ ∈ S ⊓ K
    exact and_congr hsS hsK
  have hkN : k ∈ Subgroup.normalizer ((S ⊓ K : Subgroup G) : Set G) := by
    have e : k = (k * s) * s⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hyN (Subgroup.inv_mem _ hsN)
  have hk2 : k * k ∈ S ⊓ K := by
    have h1 : k * s * k * s = 1 := by simpa [mul_assoc] using hy2
    have h2 : k * s * k = s⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 := hcomm _ hy k hk
    have h4 : k * s * k * (k * s)⁻¹ * k⁻¹ = s⁻¹ * s⁻¹ * (k⁻¹ * k⁻¹) := by
      calc k * s * k * (k * s)⁻¹ * k⁻¹ = (k * s * k) * s⁻¹ * k⁻¹ * k⁻¹ := by group
        _ = s⁻¹ * s⁻¹ * (k⁻¹ * k⁻¹) := by rw [h2]; group
    rw [h4] at h3
    have h5 : k⁻¹ * k⁻¹ = (s * s) * (s⁻¹ * s⁻¹ * (k⁻¹ * k⁻¹)) := by group
    have h6 : k⁻¹ * k⁻¹ ∈ S := by
      rw [h5]
      exact S.mul_mem (S.mul_mem hs hs) (hOT h3).1
    have h7 : k * k ∈ S := by
      have := S.inv_mem h6
      rw [mul_inv_rev, inv_inv] at this
      exact this
    exact ⟨h7, K.mul_mem hk hk⟩
  have hkT : k ∈ S ⊓ K := mem_of_mul_self_mem inf_le_right hodd hk hkN hk2
  exact S.mul_mem hkT.1 hs

theorem conj_mem_map_subtype {G : Type*} [Group G] {P : Subgroup G} (Y : Subgroup ↥P) [Y.Normal]
    {p y : G} (hp : p ∈ P) (hy : y ∈ Y.map P.subtype) : p * y * p⁻¹ ∈ Y.map P.subtype := by
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨⟨p, hp⟩ * y' * ⟨p, hp⟩⁻¹, Subgroup.Normal.conj_mem inferInstance y' hy' _, rfl⟩

end CFSG.Quasithin.SzVB.KerAux
