module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Lift

public section

namespace CFSG.Quasithin.ModG

open CFSG.QuasithinUnique.Vol2Native.L239

theorem exists_aut_of_ker {K M : Type*} [Group K] [Group M] (ψ : K →* M) (hψ : Function.Surjective ψ)
    (φ : MulAut K) (hφ : ψ.ker.map φ.toMonoidHom = ψ.ker) :
    ∃ α : MulAut M, ∀ k : K, α (ψ k) = ψ (φ k) := by
  let e : K ⧸ ψ.ker ≃* M := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  let f : (K ⧸ ψ.ker) ≃* (K ⧸ ψ.ker) := QuotientGroup.congr ψ.ker ψ.ker φ hφ
  refine ⟨e.symm.trans (f.trans e), fun k => ?_⟩
  have h1 : e.symm (ψ k) = (k : K ⧸ ψ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show e (f (e.symm (ψ k))) = ψ (φ k)
  rw [h1]
  rfl

theorem exists_conj_fixing {M : Type*} [Group M] [Finite M] {S Z : Subgroup M} (hS2 : IsPGroup 2 ↥S)
    (hSi : ¬ 2 ∣ S.index) (hSZ : S ≤ Z) (α : MulAut M) (hα : Z.map α.toMonoidHom = Z) :
    ∃ z ∈ Z, S.map (MulAut.conj z * α).toMonoidHom = S := by
  classical
  have hSαZ : S.map α.toMonoidHom ≤ Z := by
    rw [← hα]
    exact Subgroup.map_mono hSZ
  set S₁ : Subgroup ↥Z := S.subgroupOf Z with hS₁
  set S₂ : Subgroup ↥Z := (S.map α.toMonoidHom).subgroupOf Z with hS₂
  have hS₂p : IsPGroup 2 ↥(S.map α.toMonoidHom) := hS2.map α.toMonoidHom
  have hS₁p : IsPGroup 2 ↥S₁ := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSZ).symm
  have hS₂p' : IsPGroup 2 ↥S₂ := hS₂p.of_equiv (Subgroup.subgroupOfEquivOfLe hSαZ).symm
  have hidx : ¬ 2 ∣ (S.map α.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective α.bijective]
    exact hSi
  have hS₁i : ¬ 2 ∣ S₁.index := by
    intro h
    apply hSi
    have := Subgroup.relIndex_mul_index hSZ
    rw [← this]
    exact Dvd.dvd.mul_right h _
  have hS₂i : ¬ 2 ∣ S₂.index := by
    intro h
    apply hidx
    have := Subgroup.relIndex_mul_index hSαZ
    rw [← this]
    exact Dvd.dvd.mul_right h _
  obtain ⟨g, hg⟩ := exists_conj_of_sylow_two hS₂p' hS₂i hS₁p hS₁i
  refine ⟨(g : M), g.2, ?_⟩
  have hmap : S.map (MulAut.conj (g : M) * α).toMonoidHom =
      (S.map α.toMonoidHom).map (MulAut.conj (g : M)).toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [hmap]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hy
    have h2 : (⟨α s, hSαZ ⟨s, hs, rfl⟩⟩ : ↥Z) ∈ S₂ := ⟨s, hs, rfl⟩
    have h3 : (MulAut.conj g) ⟨α s, hSαZ ⟨s, hs, rfl⟩⟩ ∈ S₁ := by
      rw [← hg]
      exact ⟨_, h2, rfl⟩
    exact h3
  · intro hx
    have h2 : (⟨x, hSZ hx⟩ : ↥Z) ∈ S₁ := hx
    rw [← hg] at h2
    obtain ⟨y, hy, hyx⟩ := h2
    refine ⟨(y : M), hy, ?_⟩
    have := congrArg Subtype.val hyx
    exact this

theorem mem_zpowers_pow_of_coprime' {G : Type*} [Group G] {x : G} {n : ℕ}
    (h : Nat.Coprime n (orderOf x)) : x ∈ Subgroup.zpowers (x ^ n) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  refine ⟨a, ?_⟩
  have hxo : x ^ (orderOf x : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  have h1 : x ^ (a * n + b * (orderOf x : ℤ)) = x := by rw [hab, zpow_one]
  have h2 : x ^ (a * n + b * (orderOf x : ℤ)) = x ^ (a * n) := by
    rw [zpow_add, mul_comm b, zpow_mul x _ b, hxo, one_zpow, mul_one]
  calc (x ^ n) ^ a = x ^ (a * n) := by rw [← zpow_natCast, ← zpow_mul, mul_comm]
    _ = x := h2.symm.trans h1

theorem exists_odd_lift {K M : Type*} [Group K] [Group M] (ψ : K →* M)
    (hker : ∀ k ∈ ψ.ker, ∃ b : ℕ, k ^ 2 ^ b = 1) (W : Subgroup K) {d : M} (hd : d ∈ W.map ψ)
    (hodd : Odd (orderOf d)) : ∃ x ∈ W, Odd (orderOf x) ∧ ψ x = d := by
  obtain ⟨k, hkW, rfl⟩ := hd
  set m := orderOf (ψ k) with hm
  have hkm : k ^ m ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hm, pow_orderOf_eq_one]
  obtain ⟨b, hb⟩ := hker _ hkm
  set x₀ := k ^ 2 ^ b with hx₀
  have hx₀m : x₀ ^ m = 1 := by
    rw [hx₀, ← pow_mul, mul_comm, pow_mul, hb]
  have hcop : Nat.Coprime (2 ^ b) (orderOf (ψ k)) :=
    Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hodd)
  obtain ⟨e, he⟩ := mem_zpowers_pow_of_coprime' hcop
  refine ⟨x₀ ^ e, ?_, ?_, ?_⟩
  · exact zpow_mem (pow_mem hkW _) e
  · have h1 : (x₀ ^ e) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx₀m, one_zpow]
    exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one h1)
  · rw [map_zpow, hx₀, map_pow]
    exact he

end CFSG.Quasithin.ModG
