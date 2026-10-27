module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Two
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Dih
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Cases

public section

namespace CFSG.Quasithin.Gap6R2.L3

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G]

theorem comm_mem_of_cyclic_lift {K0 Q J : Subgroup G}
    (hWQ : K0 ⊔ Q ≤ Subgroup.normalizer (Q : Set G))
    (hJW : J ≤ K0 ⊔ Q) (hJc : ∀ j ∈ J, ∀ y ∈ K0 ⊔ Q, j * y * j⁻¹ * y⁻¹ ∈ Q)
    {c a b : G} {i l : ℤ} (haK : a ∈ K0) (hbK : b ∈ K0)
    (ha : (c ^ i)⁻¹ * a ∈ J) (hb : (c ^ l)⁻¹ * b ∈ J) :
    a * b * a⁻¹ * b⁻¹ ∈ Q := by
  classical
  have hn : (Q.subgroupOf (K0 ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hWQ
  set π : ↥(K0 ⊔ Q) →* ↥(K0 ⊔ Q) ⧸ Q.subgroupOf (K0 ⊔ Q) := QuotientGroup.mk' _ with hπ
  have haW : a ∈ K0 ⊔ Q := Subgroup.mem_sup_left haK
  have hbW : b ∈ K0 ⊔ Q := Subgroup.mem_sup_left hbK
  have hj₁W : (c ^ i)⁻¹ * a ∈ K0 ⊔ Q := hJW ha
  have hj₂W : (c ^ l)⁻¹ * b ∈ K0 ⊔ Q := hJW hb
  have huW : c ^ i ∈ K0 ⊔ Q := by
    have := (K0 ⊔ Q).mul_mem haW ((K0 ⊔ Q).inv_mem hj₁W)
    simpa [mul_assoc] using this
  have hwW : c ^ l ∈ K0 ⊔ Q := by
    have := (K0 ⊔ Q).mul_mem hbW ((K0 ⊔ Q).inv_mem hj₂W)
    simpa [mul_assoc] using this
  set A : ↥(K0 ⊔ Q) := ⟨a, haW⟩
  set B : ↥(K0 ⊔ Q) := ⟨b, hbW⟩
  set U : ↥(K0 ⊔ Q) := ⟨c ^ i, huW⟩
  set V : ↥(K0 ⊔ Q) := ⟨c ^ l, hwW⟩
  set J₁ : ↥(K0 ⊔ Q) := ⟨(c ^ i)⁻¹ * a, hj₁W⟩
  set J₂ : ↥(K0 ⊔ Q) := ⟨(c ^ l)⁻¹ * b, hj₂W⟩
  have hAe : A = U * J₁ := Subtype.ext (by simp [A, U, J₁])
  have hBe : B = V * J₂ := Subtype.ext (by simp [B, V, J₂])
  have hUV : U * V = V * U :=
    Subtype.ext (by simpa [U, V] using (Commute.zpow_zpow_self c i l).eq)
  have hcen : ∀ (j : G) (hj : j ∈ J) (hjW : j ∈ K0 ⊔ Q) (Y : ↥(K0 ⊔ Q)),
      π ⟨j, hjW⟩ * π Y = π Y * π ⟨j, hjW⟩ := by
    intro j hj hjW Y
    have h1 := hJc j hj Y Y.2
    have h2 : (⟨j, hjW⟩ * Y * ⟨j, hjW⟩⁻¹ * Y⁻¹ : ↥(K0 ⊔ Q)) ∈ Q.subgroupOf (K0 ⊔ Q) := by
      rw [Subgroup.mem_subgroupOf]
      simpa using h1
    have h3 : π (⟨j, hjW⟩ * Y * ⟨j, hjW⟩⁻¹ * Y⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    exact commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def]; exact h3)
  have hc1 := hcen _ ha hj₁W
  have hc2 := hcen _ hb hj₂W
  have hcomm : Commute (π A) (π B) := by
    rw [hAe, hBe, map_mul, map_mul]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
    · show π U * π V = π V * π U
      rw [← map_mul, ← map_mul, hUV]
    · exact (hc2 U).symm
    · exact hc1 V
    · exact hc1 J₂
  have h1 : π (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have := hcomm.eq
    rw [this]
    group
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  exact Subgroup.mem_subgroupOf.mp h2


theorem oddComm_of_case_two_cyclic [Finite G] {K T N K0 : Subgroup G}
    (hmin : MinParabolic K T N) (hKK0 : K = K0 ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K0 : Set G))
    (hker : ∀ x : G, x ∈ kerIn N K ↔ x ∈ K0 ⊔ pCoreOf 2 K ∧
      ∀ y ∈ K0 ⊔ pCoreOf 2 K, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 K)
    (hcyc : ∃ c : G, ∀ a ∈ N ⊓ K0, Odd (orderOf a) → ∃ i : ℤ, (c ^ i)⁻¹ * a ∈ kerIn N K) :
    ∀ a ∈ N, Odd (orderOf a) → ∀ b ∈ N, Odd (orderOf b) →
      a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowTwoOf T K := hmin.isSylow
  have hNK : N ≤ K := hmin.maximal.1.le
  have hTN : T ≤ N := hmin.le
  have hQT : pCoreOf 2 K ≤ T := CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hsyl
  have hQN : pCoreOf 2 K ≤ pCoreOf 2 N :=
    le_pCoreOf_of_le_normalizer 2 (hQT.trans hTN)
      (fun x hx => le_normalizer_pCoreOf 2 K (hNK hx)) (pCoreOf_isPGroup 2 K)
  have hK0K : K0 ≤ K := hKK0 ▸ le_sup_left
  have hWQ : K0 ⊔ pCoreOf 2 K ≤ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
    sup_le (fun x hx => le_normalizer_pCoreOf 2 K (hK0K hx)) Subgroup.le_normalizer
  obtain ⟨c, hc⟩ := hcyc
  intro a ha hoa b hb hob
  have haK0 : a ∈ K0 := odd_mem_of_sup hsyl.2.1 hTK (hKK0 ▸ hNK ha) hoa
  have hbK0 : b ∈ K0 := odd_mem_of_sup hsyl.2.1 hTK (hKK0 ▸ hNK hb) hob
  obtain ⟨i, hi⟩ := hc a ⟨ha, haK0⟩ hoa
  obtain ⟨l, hl⟩ := hc b ⟨hb, hbK0⟩ hob
  exact hQN (comm_mem_of_cyclic_lift hWQ (fun j hj => ((hker j).mp hj).1)
    (fun j hj y hy => ((hker j).mp hj).2 y hy) haK0 hbK0 hi hl)


theorem exists_cyclic_lift_of_two_c [Finite G] {K T N K0 : Subgroup G}
    (hmin : MinParabolic K T N) (hK0 : K0 ∈ cComp K) (hKK0 : K = K0 ⊔ T) {p e : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (he : e = 1 ∨ e = 2)
    (hmod : p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) (hpsl : IsPSL 2 p e ↥(E2.star N K K0))
    (hMKs : E2.star N K (N ⊓ K0) = E2.star N K K0 ⊓ Subgroup.centralizer
      ((E2.star N K (T ⊓ K0) ⊓ Subgroup.centralizer
        ((E2.star N K (T ⊓ K0) : Subgroup (E2.StarQuot N K)) : Set (E2.StarQuot N K)) :
        Subgroup (E2.StarQuot N K)) : Set (E2.StarQuot N K))) :
    ∃ c : G, ∀ a ∈ N ⊓ K0, Odd (orderOf a) → ∃ i : ℤ, (c ^ i)⁻¹ * a ∈ kerIn N K := by
  have : Fact p.Prime := ⟨hp⟩
  have hK0K : K0 ≤ K := le_of_mem_cComp hK0
  have hTN : T ≤ N := hmin.le
  have hNK : N ≤ K := hmin.maximal.1.le
  have hJN : kerIn N K ≤ N := fun x hx => by simpa using hx 1 K.one_mem
  have hT2 : IsPGroup 2 T := hmin.isSylow.2.1
  set π : ↥K →* E2.StarQuot N K := QuotientGroup.mk' ((kerIn N K).subgroupOf K) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Ks := E2.star N K K0 with hKs
  set ZTK : Subgroup (E2.StarQuot N K) := E2.star N K (T ⊓ K0) ⊓ Subgroup.centralizer
    ((E2.star N K (T ⊓ K0) : Subgroup (E2.StarQuot N K)) : Set (E2.StarQuot N K)) with hZTK
  have hZ : ZTK ≠ ⊥ := by
    intro hZbot
    have hC : Subgroup.centralizer (ZTK : Set (E2.StarQuot N K)) = ⊤ := by
      rw [hZbot]
      exact Subgroup.centralizer_eq_top_iff_subset.mpr (by simp)
    have hMKs' : E2.star N K (N ⊓ K0) = Ks := by rw [hMKs, hC, inf_top_eq]
    have hK0N : K0 ≤ N := by
      intro k hk
      have hkK : k ∈ K := hK0K hk
      have hmem : π ⟨k, hkK⟩ ∈ Ks := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
      rw [← hMKs'] at hmem
      obtain ⟨y, hy, hyk⟩ := hmem
      have h1 : y⁻¹ * ⟨k, hkK⟩ ∈ (kerIn N K).subgroupOf K := QuotientGroup.eq.mp hyk
      have h2 : ((y : K) : G)⁻¹ * k ∈ kerIn N K := by simpa using Subgroup.mem_subgroupOf.mp h1
      have hyN : ((y : K) : G) ∈ N := (Subgroup.mem_subgroupOf.mp hy).1
      have : k = ((y : K) : G) * (((y : K) : G)⁻¹ * k) := by group
      rw [this]
      exact N.mul_mem hyN (hJN h2)
    have : K ≤ N := by rw [hKK0]; exact sup_le hK0N hTN
    exact absurd (lt_of_lt_of_le hmin.maximal.1 this) (lt_irrefl _)
  have hTKs2 : IsPGroup 2 (E2.star N K (T ⊓ K0)) :=
    ((hT2.to_le inf_le_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans (hTN.trans hNK))).symm).map π
  have hZ2 : IsPGroup 2 ZTK := hTKs2.to_le inf_le_left
  obtain ⟨g, hgZ, hg2⟩ : ∃ g ∈ ZTK, orderOf g = 2 := by
    obtain ⟨n, hn⟩ := hZ2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hZ (Subgroup.eq_bot_of_card_eq _ hn)
    have h2 : 2 ∣ Nat.card ZTK := by rw [hn]; exact dvd_pow_self 2 hn0
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  have hgKs : g ∈ Ks := by
    have h1 : E2.star N K (T ⊓ K0) ≤ Ks :=
      Subgroup.map_mono fun y hy => Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy).2
    exact h1 (hgZ.1)
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hf : 0 < e := by omega
  have h7 : 7 ≤ p ^ e := by
    have h5 : 4 ≤ p ^ e := le_trans (by omega : 4 ≤ p) (Nat.le_self_pow (by omega : e ≠ 0) p)
    omega
  obtain ⟨cX, hcX⟩ := exists_zpowers_of_odd_centralizer hodd hf h7 hpsl
    (g := (⟨g, hgKs⟩ : ↥Ks)) (by rw [Subgroup.orderOf_mk]; exact hg2)
  obtain ⟨c, hc⟩ := hπsurj (cX : E2.StarQuot N K)
  refine ⟨(c : G), fun a ha hoa => ?_⟩
  have haK : a ∈ K := hNK ha.1
  have hx : π ⟨a, haK⟩ ∈ E2.star N K (N ⊓ K0) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
  rw [hMKs] at hx
  obtain ⟨hxKs, hxC⟩ := hx
  have hxcen : (⟨π ⟨a, haK⟩, hxKs⟩ : ↥Ks) ∈ Subgroup.centralizer ({(⟨g, hgKs⟩ : ↥Ks)} :
      Set ↥Ks) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_iff.mp hxC g hgZ
    exact Subtype.ext this.symm
  have hxodd : Odd (orderOf (⟨π ⟨a, haK⟩, hxKs⟩ : ↥Ks)) := by
    rw [← Subgroup.orderOf_coe]
    refine Odd.of_dvd_nat (n := orderOf (⟨a, haK⟩ : ↥K)) ?_ (orderOf_map_dvd π _)
    rw [Subgroup.orderOf_mk]
    exact hoa
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hcX _ hxcen hxodd)
  refine ⟨i, ?_⟩
  have hpi : π (c ^ i) = π ⟨a, haK⟩ := by
    rw [map_zpow, hc]
    exact congrArg Subtype.val hi
  have h1 : (c ^ i)⁻¹ * ⟨a, haK⟩ ∈ (kerIn N K).subgroupOf K := QuotientGroup.eq.mp hpi
  simpa using Subgroup.mem_subgroupOf.mp h1


theorem oddComm_of_two_c [Finite G] {K T N K0 : Subgroup G} (hmin : MinParabolic K T N)
    (hK0 : K0 ∈ cComp K) (hKK0 : K = K0 ⊔ T) (h : E22Case2c K T N K0) :
    ∀ a ∈ N, Odd (orderOf a) → ∀ b ∈ N, Odd (orderOf b) →
      a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 N := by
  unfold E22Case2c at h
  dsimp only at h
  obtain ⟨hTK, hker, p, e, hp, hp3, he, hmod, hpsl, hMKs, -⟩ := h
  exact oddComm_of_case_two_cyclic hmin hKK0 hTK hker
    (exists_cyclic_lift_of_two_c hmin hK0 hKK0 hp hp3 he hmod hpsl hMKs)

end CFSG.Quasithin.Gap6R2.L3
