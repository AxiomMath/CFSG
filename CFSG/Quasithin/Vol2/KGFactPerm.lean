module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem9
public import CFSG.Quasithin.Vol2.KGFactOut
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic
open scoped Pointwise

namespace KGPerm

section Permute

variable {G : Type*} [Group G]

theorem coe_sup_eq_mul {H K : Subgroup G} (h : (H : Set G) * K = K * H) :
    ((H ⊔ K : Subgroup G) : Set G) = H * K := by
  let T : Subgroup G :=
    { carrier := (H : Set G) * K
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        have hbc : b * c ∈ (K : Set G) * H := ⟨b, hb, c, hc, rfl⟩
        rw [← h] at hbc
        obtain ⟨c', hc', b', hb', hcb⟩ := hbc
        have hcb : c' * b' = b * c := hcb
        refine ⟨a * c', H.mul_mem ha hc', b' * d, K.mul_mem hb' hd, ?_⟩
        calc a * c' * (b' * d) = a * (c' * b') * d := by group
          _ = a * (b * c) * d := by rw [hcb]
          _ = a * b * (c * d) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have hba : b⁻¹ * a⁻¹ ∈ (K : Set G) * H := ⟨b⁻¹, K.inv_mem hb, a⁻¹, H.inv_mem ha, rfl⟩
        rw [← h] at hba
        show (a * b)⁻¹ ∈ (H : Set G) * K
        rw [_root_.mul_inv_rev]
        exact hba }
  have hT : H ⊔ K = T := le_antisymm
    (sup_le (fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩)
      (fun x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩))
    (fun x ⟨a, ha, b, hb, hab⟩ => hab ▸ Subgroup.mul_mem_sup ha hb)
  rw [hT]
  rfl

theorem card_sup_eq_mul {H K : Subgroup G} (h : (H : Set G) * K = K * H) (hHK : H ⊓ K = ⊥) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  rw [← Nat.card_prod]
  have hc := congrArg (fun s : Set G => Nat.card s) (coe_sup_eq_mul h)
  change Nat.card (H ⊔ K : Subgroup G) = Nat.card ((H : Set G) * K : Set G) at hc
  rw [hc]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun q : H × K =>
    (⟨(q.1 : G) * q.2, Set.mul_mem_mul q.1.2 q.2.2⟩ : ((H : Set G) * K : Set G))) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    have h' : a * b = a' * b' := congrArg Subtype.val hab
    have hm : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h']
        _ = b' * b⁻¹ := by group
    have hmem : a'⁻¹ * a ∈ H ⊓ K :=
      ⟨H.mul_mem (H.inv_mem ha') ha, hm ▸ K.mul_mem hb' (K.inv_mem hb)⟩
    rw [hHK, Subgroup.mem_bot] at hmem
    obtain rfl : a' = a := inv_mul_eq_one.mp hmem
    obtain rfl : b = b' := mul_left_cancel h'
    rfl
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩⟩
    exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩

theorem map_permute {G' : Type*} [Group G'] (f : G →* G') {H K : Subgroup G}
    (h : (H : Set G) * K = K * H) :
    ((H.map f : Subgroup G') : Set G') * (K.map f : Subgroup G') =
      (K.map f : Subgroup G') * (H.map f : Subgroup G') := by
  rw [Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, h, Set.image_mul]

theorem subgroupOf_permute {H K N : Subgroup G} (hHN : H ≤ N) (h : (H : Set G) * K = K * H) :
    ((H.subgroupOf N : Subgroup N) : Set N) * ((K ⊓ N).subgroupOf N : Subgroup N) =
      ((K ⊓ N).subgroupOf N : Subgroup N) * (H.subgroupOf N : Subgroup N) := by
  ext y
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha hb
    have hab : (a : G) * b ∈ (K : Set G) * H := by
      rw [← h]
      exact Set.mul_mem_mul ha (Subgroup.mem_inf.1 hb).1
    obtain ⟨k, hk, x, hx, hkx⟩ := hab
    have hkN : k ∈ N := by
      have e : k = a * b * x⁻¹ := by rw [← hkx]; group
      rw [e]
      exact N.mul_mem (N.mul_mem a.2 b.2) (N.inv_mem (hHN hx))
    refine ⟨⟨k, hkN⟩, ?_, ⟨x, hHN hx⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact ⟨hk, hkN⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact hx
    · apply Subtype.ext
      simpa using hkx
  · rintro ⟨b, hb, a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha hb
    have hba : (b : G) * a ∈ (H : Set G) * K := by
      rw [h]
      exact Set.mul_mem_mul (Subgroup.mem_inf.1 hb).1 ha
    obtain ⟨x, hx, k, hk, hxk⟩ := hba
    have hkN : k ∈ N := by
      have e : k = x⁻¹ * (b * a) := by rw [← hxk]; group
      rw [e]
      exact N.mul_mem (N.inv_mem (hHN hx)) (N.mul_mem b.2 a.2)
    refine ⟨⟨x, hHN hx⟩, ?_, ⟨k, hkN⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact hx
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact ⟨hk, hkN⟩
    · apply Subtype.ext
      simpa using hxk

end Permute

theorem eq_bot_of_permute_unitriangular {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) {X : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))} (hX : IsPGroup p X)
    (hXU : (X : Set (SpecialLinearGroup (Fin n) (ZMod 2))) * (unitriangular n (ZMod 2) :
      Set (SpecialLinearGroup (Fin n) (ZMod 2))) =
      (unitriangular n (ZMod 2) : Set (SpecialLinearGroup (Fin n) (ZMod 2))) * X) :
    X = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 hn
  have hU2 : IsPGroup 2 (unitriangular n (ZMod 2)) := by
    rw [← hT₀]
    exact T₀.isPGroup'
  have hdisj : X ⊓ unitriangular n (ZMod 2) = ⊥ :=
    disjoint_iff.1 (IsPGroup.disjoint_of_ne p 2 hp2 X _ hX hU2)
  have hUY : unitriangular n (ZMod 2) ≤ X ⊔ unitriangular n (ZMod 2) := le_sup_right
  have hidx : (unitriangular n (ZMod 2)).relIndex (X ⊔ unitriangular n (ZMod 2)) =
      Nat.card X := by
    have h1 := Subgroup.card_mul_index ((unitriangular n (ZMod 2)).subgroupOf
      (X ⊔ unitriangular n (ZMod 2)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).toEquiv, card_sup_eq_mul hXU hdisj,
      mul_comm (Nat.card X)] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hY := (borel_overgroups (X ⊔ unitriangular n (ZMod 2))
    (by rw [upperTriangular_eq_unitriangular]; exact hUY)).1
  by_cases h : ∃ (j : ℕ) (hj : 1 ≤ j) (hjn : j < n),
      reflection n (ZMod 2) j hj hjn ∈ X ⊔ unitriangular n (ZMod 2)
  · exfalso
    obtain ⟨j, hj, hjn, hr⟩ := h
    have hM : flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) ≤
        X ⊔ unitriangular n (ZMod 2) := by
      rw [parabolic_eq_closure hj hjn, Subgroup.closure_le]
      rintro g (hg | hg)
      · exact hUY hg
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact hr
    have h3 : 3 ∣ (unitriangular n (ZMod 2)).relIndex (X ⊔ unitriangular n (ZMod 2)) := by
      have e := Subgroup.relIndex_mul_relIndex _ _ _ (unitriangular_le_flagStabilizer _) hM
      rw [relIndex_parabolic hj hjn] at e
      exact Dvd.intro _ e
    rw [hidx] at h3
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hX
    rw [hk] at h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  · have hcuts : Set.Icc 1 (n - 1) ⊆ borelOvergroupCuts (X ⊔ unitriangular n (ZMod 2)) := by
      intro i hi
      obtain ⟨hi1, hin⟩ := hi
      exact ⟨hi1, by omega, fun hr => h ⟨i, hi1, by omega, hr⟩⟩
    have hYU : X ⊔ unitriangular n (ZMod 2) ≤ unitriangular n (ZMod 2) :=
      calc X ⊔ unitriangular n (ZMod 2)
          = flagStabilizer n (ZMod 2) (borelOvergroupCuts (X ⊔ unitriangular n (ZMod 2))) := hY
        _ ≤ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1)) := flagStabilizer_anti hcuts
        _ = unitriangular n (ZMod 2) := flagStabilizer_Icc
    rw [eq_bot_iff, ← hdisj]
    exact le_inf le_rfl (le_sup_left.trans hYU)

theorem eq_bot_of_permute_sylow {A : Type*} [Group A] [Finite A] {I : Subgroup A} [I.Normal]
    (hsq : ∀ a : A, a * a ∈ I) {n : ℕ} (hn : 1 ≤ n)
    (e : ↥I ≃* SpecialLinearGroup (Fin n) (ZMod 2)) (S : Sylow 2 A) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {X : Subgroup A} (hX : IsPGroup p X)
    (hXS : (X : Set A) * (S : Subgroup A) = ((S : Subgroup A) : Set A) * X) : X = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXI : X ≤ I := by
    intro x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).1 hX ⟨x, hx⟩
    have hk' : orderOf x = p ^ k := (Subgroup.orderOf_coe (⟨x, hx⟩ : X)).trans hk
    have hodd : Odd (orderOf x) := by
      rw [hk']
      exact (hp.eq_two_or_odd'.resolve_left hp2).pow
    obtain ⟨m, hm⟩ := hodd
    have ex : x = (x * x) ^ (m + 1) := by
      rw [← sq, ← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [ex]
    exact I.pow_mem (hsq x) _
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal S (N := I)
  have hperm₁ : ((X.subgroupOf I : Subgroup I) : Set I) * (P : Subgroup I) =
      ((P : Subgroup I) : Set I) * (X.subgroupOf I : Subgroup I) := by
    rw [hP]
    exact subgroupOf_permute hXI hXS
  let P₂ : Sylow 2 (SpecialLinearGroup (Fin n) (ZMod 2)) :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hperm₂ : (((X.subgroupOf I).map e.toMonoidHom : Subgroup _) :
      Set (SpecialLinearGroup (Fin n) (ZMod 2))) *
      ((P₂ : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) :
        Set (SpecialLinearGroup (Fin n) (ZMod 2))) =
      ((P₂ : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) :
        Set (SpecialLinearGroup (Fin n) (ZMod 2))) *
        ((X.subgroupOf I).map e.toMonoidHom : Subgroup _) :=
    map_permute e.toMonoidHom hperm₁
  obtain ⟨T₀, hT₀⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 hn
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin n) (ZMod 2)) P₂ T₀
  have hgP : (T₀ : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) =
      (P₂ : Subgroup _).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hperm₃ : ((((X.subgroupOf I).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom :
      Subgroup _) : Set (SpecialLinearGroup (Fin n) (ZMod 2))) *
      (unitriangular n (ZMod 2) : Set (SpecialLinearGroup (Fin n) (ZMod 2))) =
      (unitriangular n (ZMod 2) : Set (SpecialLinearGroup (Fin n) (ZMod 2))) *
        (((X.subgroupOf I).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom : Subgroup _) := by
    rw [← hT₀, hgP]
    exact map_permute _ hperm₂
  have hX₃ : IsPGroup p (((X.subgroupOf I).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom) :=
    (hX.comap_subtype.map _).map _
  have h3 := eq_bot_of_permute_unitriangular hn hp hp2 hp3 hX₃ hperm₃
  have h4 : (X.subgroupOf I).map e.toMonoidHom = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).1 h3
  have h5 : X.subgroupOf I = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).1 h4
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hXI hx⟩ : I) ∈ X.subgroupOf I := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  rw [h5, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hx'

theorem eq_one_of_mem_center {n : ℕ} (hn : 1 ≤ n) {z : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) (ZMod 2))) : z = 1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin] at hz
  obtain ⟨r, hr, hrz⟩ := hz
  have hr1 : r = 1 := by
    rcases (by decide : ∀ r : ZMod 2, r = 0 ∨ r = 1) r with rfl | rfl
    · rw [zero_pow (by omega)] at hr
      exact absurd hr zero_ne_one
    · rfl
  apply Subtype.ext
  rw [← hrz, hr1]
  simp

end KGPerm

open KGPerm in
theorem lem1219Perm_holds : Lem1219Perm := by
  intro G _ _ T L V V₁ V₂ n hyp hTM p X hp hp3 hX hXM hXT
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn3 : 3 ≤ n := by rcases hyp.rank with h | h <;> omega
  obtain ⟨ι⟩ := hyp.iso
  obtain ⟨φ⟩ := hyp.aut
  obtain ⟨hVn, -, -⟩ := hyp.reduced
  have hconjV : ∀ g ∈ Subgroup.normalizer (L : Set G), ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    intro g hg v hv
    have := hVn.conj_mem ⟨v, hyp.le hv⟩ (by rw [Subgroup.mem_subgroupOf]; exact hv) ⟨g, hg⟩
    rwa [Subgroup.mem_subgroupOf] at this
  have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconjV g hg h hh, fun hh => ?_⟩
    have := hconjV g⁻¹ (Subgroup.inv_mem _ hg) _ hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this
  let ρ₀ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(autOn (Subgroup.normalizer (L : Set G)) V) :=
    ((conjAct V).comp (Subgroup.inclusion hMV)).codRestrict _ fun g =>
      ⟨Subgroup.inclusion hMV g, by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact g.2, rfl⟩
  have hρ₀ : Function.Surjective ρ₀ := by
    rintro ⟨_, y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
    exact ⟨⟨y, hy⟩, rfl⟩
  let ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (↥L ⧸ CFSG.pCore 2 ↥L) :=
    φ.toMonoidHom.comp ρ₀
  have hρ : Function.Surjective ρ := φ.surjective.comp hρ₀
  have hker : ∀ g : ↥(Subgroup.normalizer (L : Set G)), ρ g = 1 →
      (g : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg
    have h1 : ρ₀ g = 1 := φ.injective (by rw [map_one]; exact hg)
    have h2 : Subgroup.inclusion le_rfl (Subgroup.inclusion hMV g) ∈
        V.normalizerMonoidHom.ker := congrArg Subtype.val h1
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
    exact h2
  obtain ⟨hT2, hTodd⟩ := hyp.sylow
  have hTM2 : IsPGroup 2 (T.subgroupOf (Subgroup.normalizer (L : Set G))) := hT2.comap_subtype
  have hTModd : ¬ 2 ∣ (T.subgroupOf (Subgroup.normalizer (L : Set G))).index := fun h2 =>
    hTodd (h2.trans (Subgroup.relIndex_dvd_index_of_le hTM))
  let SA : Sylow 2 (MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) := (hTM2.toSylow hTModd).mapSurjective hρ
  have hpermM : ((X.subgroupOf (Subgroup.normalizer (L : Set G)) : Subgroup _) :
      Set ↥(Subgroup.normalizer (L : Set G))) *
      (T.subgroupOf (Subgroup.normalizer (L : Set G)) : Subgroup _) =
      (T.subgroupOf (Subgroup.normalizer (L : Set G)) : Subgroup _) *
        (X.subgroupOf (Subgroup.normalizer (L : Set G)) : Subgroup _) := by
    have := subgroupOf_permute hXM hXT
    rwa [inf_of_le_left hTM] at this
  have hpermA : (((X.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ : Subgroup _) :
      Set (MulAut (↥L ⧸ CFSG.pCore 2 ↥L))) *
      ((SA : Subgroup (MulAut (↥L ⧸ CFSG.pCore 2 ↥L))) : Set (MulAut (↥L ⧸ CFSG.pCore 2 ↥L))) =
      ((SA : Subgroup (MulAut (↥L ⧸ CFSG.pCore 2 ↥L))) : Set (MulAut (↥L ⧸ CFSG.pCore 2 ↥L))) *
        ((X.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ : Subgroup _) :=
    map_permute ρ hpermM
  have hinj : Function.Injective
      (MulAut.conj : (↥L ⧸ CFSG.pCore 2 ↥L) →* MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : ι z ∈ Subgroup.center (SpecialLinearGroup (Fin n) (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := ι.surjective w
      have hw := congrArg (fun f : MulAut (↥L ⧸ CFSG.pCore 2 ↥L) => f w') hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at hw
      rw [← map_mul, ← map_mul]
      congr 1
      calc w' * z = (z * w' * z⁻¹) * z := by rw [hw]
        _ = z * w' := by group
    exact ι.injective ((eq_one_of_mem_center (by omega) hzc).trans (map_one ι).symm)
  let eI : ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner (↥L ⧸ CFSG.pCore 2 ↥L)) ≃*
      SpecialLinearGroup (Fin n) (ZMod 2) :=
    (MonoidHom.ofInjective hinj).symm.trans ι
  have hsq : ∀ a : MulAut (↥L ⧸ CFSG.pCore 2 ↥L),
      a * a ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro a
    obtain ⟨k, hk⟩ := KGOut.sq_inner_sl_two hn3 ι a
    exact ⟨k, hk.symm⟩
  have : Finite (MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    Finite.of_injective (fun f : MulAut (↥L ⧸ CFSG.pCore 2 ↥L) => (f : _ → _))
      DFunLike.coe_injective
  have hXA : (X.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ = ⊥ :=
    eq_bot_of_permute_sylow hsq (by omega) eI SA hp (by omega) (by omega)
      (hX.comap_subtype.map ρ) hpermA
  intro x hx
  have h1 : ρ ⟨x, hXM hx⟩ ∈ (X.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ :=
    ⟨⟨x, hXM hx⟩, hx, rfl⟩
  rw [hXA, Subgroup.mem_bot] at h1
  exact hker _ h1

end CFSG.Quasithin.H13
