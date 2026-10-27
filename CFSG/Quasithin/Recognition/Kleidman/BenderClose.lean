module

public import CFSG.Quasithin.Recognition.J2RecGlobal
public import CFSG.Open.BenderStronglyEmbedded

public section

namespace CFSG.Quasithin.Kleidman

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem fusionStronglyEmbedded_of_isStronglyEmbedded {G : Type*} [Group G] [Finite G]
    {M : Subgroup G} (hM : CFSG.BenderSuzuki.IsStronglyEmbedded M) : fusionStronglyEmbedded M := by
  obtain ⟨hne, ⟨x, hxM, hx⟩, hodd⟩ := hM
  refine ⟨hne, ?_, fun g hg => ?_⟩
  · have hx2 : orderOf (⟨x, hxM⟩ : M) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hx.2 hx.1
    exact even_iff_two_dvd.mpr (hx2 ▸ orderOf_dvd_natCard _)
  · rw [Nat.odd_iff]
    by_contra h2
    have h2' : 2 ∣ Nat.card ↥(M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom) := by omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2'
    have hyM : (y : G) ∈ M := (Subgroup.mem_inf.mp y.2).1
    have hyc : (y : G) ∈ CFSG.BenderSuzuki.PFchapter1section1.rightConjugate M g :=
      (Subgroup.mem_inf.mp y.2).2
    apply hodd hg hyM hyc
    refine ⟨fun h1 => ?_, ?_⟩
    · have : y = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hy
      exact absurd hy (by norm_num)
    · have := pow_orderOf_eq_one y
      rw [hy] at this
      exact congrArg Subtype.val this

theorem quaternion_eq_a_of_sq_eq_one {n : ℕ} [NeZero n] {w : QuaternionGroup n} (hw : w * w = 1)
    (hw1 : w ≠ 1) : w = QuaternionGroup.a (n : ZMod (2 * n)) := by
  cases w with
  | a i =>
    rw [QuaternionGroup.a_mul_a, QuaternionGroup.one_def] at hw
    have hii : i + i = 0 := QuaternionGroup.a.inj hw
    have hi0 : i ≠ 0 := fun h0 => hw1 (by rw [h0, QuaternionGroup.one_def])
    have hpos : 0 < 2 * n := Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero (NeZero.ne n))
    have : NeZero (2 * n) := ⟨hpos.ne'⟩
    have hval := congrArg ZMod.val hii
    rw [ZMod.val_add, ZMod.val_zero] at hval
    have hlt : i.val < 2 * n := ZMod.val_lt i
    have hv0 : i.val ≠ 0 := fun h0 => hi0 ((ZMod.val_eq_zero i).mp h0)
    have hvn : i.val = n := by
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hval
      rcases k with _ | _ | k
      · omega
      · omega
      · nlinarith
    congr 1
    apply ZMod.val_injective
    rw [hvn, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  | xa i =>
    exfalso
    rw [QuaternionGroup.xa_mul_xa, add_sub_cancel_right, QuaternionGroup.one_def] at hw
    have hn : ((n : ℕ) : ZMod (2 * n)) = 0 := QuaternionGroup.a.inj hw
    have hpos : 0 < 2 * n := Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero (NeZero.ne n))
    have : NeZero (2 * n) := ⟨hpos.ne'⟩
    have := congrArg ZMod.val hn
    rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at this
    exact NeZero.ne n this

theorem not_cyclic_or_quaternion {P : Type*} [Group P] [Finite P] {a b : P} (ha2 : a * a = 1)
    (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    ¬ (IsCyclic P ∨ ∃ r : ℕ, 3 ≤ r ∧ Nonempty (P ≃* QuaternionGroup (2 ^ (r - 2)))) := by
  classical
  rintro (hcyc | ⟨r, hr, ⟨e⟩⟩)
  · have : Fintype P := Fintype.ofFinite P
    have hle := IsCyclic.card_pow_eq_one_le (α := P) (n := 2) (by norm_num)
    have hsub : ({1, a, b} : Finset P) ⊆ Finset.univ.filter (fun x : P => x ^ 2 = 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pow_two]
      rcases hx with rfl | rfl | rfl
      · exact mul_one 1
      · exact ha2
      · exact hb2
    have h3 : ({1, a, b} : Finset P).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha1.symm, hb1.symm⟩
    have := Finset.card_le_card hsub
    omega
  · have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
    have hea : e a * e a = 1 := by rw [← map_mul, ha2, map_one]
    have heb : e b * e b = 1 := by rw [← map_mul, hb2, map_one]
    have hea1 : e a ≠ 1 := fun h1 => ha1 (e.injective (h1.trans (map_one e).symm))
    have heb1 : e b ≠ 1 := fun h1 => hb1 (e.injective (h1.trans (map_one e).symm))
    exact hab (e.injective ((quaternion_eq_a_of_sq_eq_one hea hea1).trans
      (quaternion_eq_a_of_sq_eq_one heb heb1).symm))

namespace IsTypeH2

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_sylow_card_center_eq_two (h : IsTypeH2 G z) :
    ∃ S : Sylow 2 G, Nat.card (Subgroup.center (S : Subgroup G)) = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer ({z} : Set G) with hH
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥H))
  set S0 : Subgroup G := (P : Subgroup ↥H).map H.subtype with hS0
  have hS0H : S0 ≤ H := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hsub : S0.subgroupOf H = P := by
    rw [hS0]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hSyl : IsSylowTwoOf S0 H := by
    refine ⟨hS0H, ?_, ?_⟩
    · exact P.2.map H.subtype
    · rw [hsub]
      exact P.not_dvd_index
  have hSylG := h.isSylowTwoOf_top hSyl
  have hidx : ¬ 2 ∣ S0.index := by
    have := hSylG.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
  refine ⟨hSylG.2.1.toSylow hidx, ?_⟩
  rw [IsPGroup.toSylow_coe]
  have hzS0 : z ∈ S0 := CFSG.Quasithin.IsTypeH2.pCoreOf_le_sylow hSyl h.z_mem_pCoreOf
  have hzc : (⟨z, hzS0⟩ : ↥S0) ∈ Subgroup.center ↥S0 := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    have hs : (s : G) ∈ H := hS0H s.2
    rw [hH, Subgroup.mem_centralizer_singleton_iff] at hs
    exact hs
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨⟨z, hzS0⟩, hzc⟩, ?_, ?_⟩
  · intro h1
    apply h.ne_one
    have := congrArg (fun c : ↥(Subgroup.center ↥S0) => ((c : ↥S0) : G)) h1
    exact this.symm
  · ext c
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    have hcS : ((c : ↥S0) : G) ∈ S0 := (c : ↥S0).2
    have hcomm : ∀ s ∈ S0, ((c : ↥S0) : G) * s = s * ((c : ↥S0) : G) := by
      intro s hs
      have := (Subgroup.mem_center_iff.mp c.2) ⟨s, hs⟩
      exact (congrArg Subtype.val this).symm
    rcases h.eq_one_or_eq_of_mem_center_sylow hSyl hcS hcomm with h1 | h1
    · left
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    · right
      apply Subtype.ext
      apply Subtype.ext
      exact h1

theorem eq_top_of_conj_z [IsSimpleGroup G] (h : IsTypeH2 G z)
    {M : Subgroup G} (hHM : Subgroup.centralizer ({z} : Set G) ≤ M)
    (hconj : ∀ y ∈ M, y * y = 1 → y ≠ 1 → ∃ k ∈ M, k * z * k⁻¹ = y) : M = ⊤ := by
  classical
  by_contra hne
  set H := Subgroup.centralizer ({z} : Set G) with hH
  have hz2 : z * z = 1 := by rw [← pow_two]; exact h.sq
  have hzM : z ∈ M := hHM (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hzinv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution z := ⟨h.ne_one, h.sq⟩
  have hcent : ∀ y ∈ M, CFSG.BenderSuzuki.PFAppendixIII.IsInvolution y →
      Subgroup.centralizer ({y} : Set G) ≤ M := by
    intro y hyM hy c hc
    obtain ⟨k, hkM, hk⟩ := hconj y hyM (by rw [← pow_two]; exact hy.2) hy.1
    have hc' : k⁻¹ * c * k ∈ H := by
      rw [hH, Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      calc k⁻¹ * c * k * z = k⁻¹ * (c * (k * z * k⁻¹)) * k := by group
        _ = k⁻¹ * (c * y) * k := by rw [hk]
        _ = k⁻¹ * (y * c) * k := by rw [hc]
        _ = k⁻¹ * ((k * z * k⁻¹) * c) * k := by rw [hk]
        _ = z * (k⁻¹ * c * k) := by group
    have e : c = k * (k⁻¹ * c * k) * k⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hkM (hHM hc')) (M.inv_mem hkM)
  have hfus : ∀ x ∈ M, ∀ y ∈ M, CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x → IsConj x y →
      ∃ k ∈ M, k * x * k⁻¹ = y := by
    intro x hxM y hyM hx hxy
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    have hx2 : x * x = 1 := by rw [← pow_two]; exact hx.2
    have hy2 : y * y = 1 := by
      rw [← hg]
      calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    have hy1 : y ≠ 1 := by
      rw [← hg]
      intro h1
      apply hx.1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨k₁, hk₁M, hk₁⟩ := hconj x hxM hx2 hx.1
    obtain ⟨k₂, hk₂M, hk₂⟩ := hconj y hyM hy2 hy1
    refine ⟨k₂ * k₁⁻¹, M.mul_mem hk₂M (M.inv_mem hk₁M), ?_⟩
    rw [← hk₁, ← hk₂]
    group
  have hSE := CFSG.Quasithin.isStronglyEmbedded_of_centralizer_le hne hzM hzinv hcent hfus
  have hF := fusionStronglyEmbedded_of_isStronglyEmbedded hSE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG2 : Even (Nat.card G) := by
    have hzo : orderOf z = 2 := orderOf_eq_prime h.sq h.ne_one
    exact even_iff_two_dvd.mpr (hzo ▸ orderOf_dvd_natCard z)
  rcases CFSG.Open.Open.bender_strongly_embedded G M hF with hcyc |
      ⟨M', N', hM', hN', hMN', -, hodd, hidx, hB⟩
  ·
    obtain ⟨g, hgQ, hgz⟩ := h.notWeaklyClosed
    obtain ⟨S, hQS⟩ := (pCoreOf_isPGroup 2 H).exists_le_sylow
    have hzS : z ∈ (S : Subgroup G) := hQS h.z_mem_pCoreOf
    have htS : g * z * g⁻¹ ∈ (S : Subgroup G) := hQS hgQ
    refine not_cyclic_or_quaternion (P := ↥(S : Subgroup G)) (a := ⟨z, hzS⟩)
      (b := ⟨g * z * g⁻¹, htS⟩) (Subtype.ext hz2) (Subtype.ext ?_) ?_ ?_ ?_ (hcyc S)
    · show g * z * g⁻¹ * (g * z * g⁻¹) = 1
      calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    · exact fun h1 => h.ne_one (congrArg Subtype.val h1)
    · intro h1
      apply h.ne_one
      have h1' : g * z * g⁻¹ = 1 := congrArg Subtype.val h1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1']; group
    · exact fun h1 => hgz (congrArg Subtype.val h1).symm
  ·
    have hM'bot : M' = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M' with h1 | h1
      · exact h1
      · exfalso
        rw [h1, Subgroup.card_top] at hodd
        exact (Nat.not_even_iff_odd.mpr hodd) hG2
    have hN'top : N' = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N' with h1 | h1
      · exfalso
        rw [h1, Subgroup.index_bot] at hidx
        exact (Nat.not_even_iff_odd.mpr hidx) hG2
      · exact h1
    subst hM'bot hN'top
    have e₀ : (↥(⊤ : Subgroup G) ⧸ (⊥ : Subgroup G).subgroupOf ⊤) ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
        (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
    obtain ⟨S, hS⟩ := IsTypeH2.exists_sylow_card_center_eq_two h
    have key : ∀ {B : Type} [Group B] (φ : G ≃* B) {q k : ℕ}, fusionBenderBorel B q k →
        4 ≤ q → False := by
      intro B _ φ q k hBB hq
      set Q := S.mapSurjective (f := φ.toMonoidHom) φ.surjective
      obtain ⟨-, -, -, hcard, -⟩ := hBB Q
      set ψ := Subgroup.equivMapOfInjective (S : Subgroup G) φ.toMonoidHom φ.injective
      have hmap := Subgroup.map_center_eq ψ
      have h2 : Nat.card (Subgroup.center ↥(Q : Subgroup B)) =
          Nat.card (Subgroup.center ↥((S : Subgroup G).map φ.toMonoidHom)) := rfl
      rw [h2, ← hmap, Subgroup.card_map_of_injective ψ.injective, hS] at hcard
      omega
    rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact key (e₀.symm.trans e) (CFSG.Open.Open.bender_psl2_borel f hf)
        (by calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)
    · exact key (e₀.symm.trans e) (CFSG.Open.Open.bender_psu3_borel f hf)
        (by calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)
    · exact key (e₀.symm.trans e) (CFSG.Open.Open.bender_suzuki_borel a ha)
        (by calc 4 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))

end IsTypeH2

end CFSG.Quasithin.Kleidman
