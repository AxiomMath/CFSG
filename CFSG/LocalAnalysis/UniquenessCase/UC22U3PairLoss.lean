module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847O3Pair
import CFSG.LocalAnalysis.UniquenessCase.UC22U3Pair
import CFSG.LocalAnalysis.UniquenessCase.UC22U3Aut
import CFSG.LocalAnalysis.UniquenessCase.UC22U3Loss0
import CFSG.LocalAnalysis.UniquenessCase.UCKPRank1
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace U3Aut

variable {k : ℕ} {E : Type} [Field E]

theorem exists_commute_invPair_fixed (hU : UnitaryFieldData 2 k E) (hk : 2 ≤ k) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {β : MulAut (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))}
    (hβ : β ^ p = 1)
    (hβi : β ∉ (MulAut.conj : _ →* MulAut (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))).range)
    (hpk : p ∣ 2 ^ k + 1) {J : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))}
    (hJ : ∀ x ∈ J, x ^ p = 1) (hJc : p ^ 2 ≤ Nat.card J) (hβJ : ∀ x ∈ J, β x = x) :
    ∃ t ∈ J, t ≠ 1 ∧ ∃ c s : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E), orderOf c = 3 ∧
      s * c * s⁻¹ = c⁻¹ ∧ c * t = t * c ∧ s * t = t * s ∧ β c = c ∧ β s = s := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨m, hm⟩, E₀, _, h₀, j, hj, hfix⟩ := exists_fixed_eq_range hU hk hp hp5 hβ hβi
  have hkm : k / p = m := by rw [hm, Nat.mul_div_cancel_left m hp.pos]
  have hpm : p ∣ 2 ^ m + 1 := by
    rw [← ZMod.natCast_eq_zero_iff] at hpk ⊢
    push_cast at hpk ⊢
    rwa [hm, mul_comm p m, pow_mul, ZMod.pow_card] at hpk
  have hm2 : 2 ≤ m := by
    rcases (by omega : m = 0 ∨ m = 1 ∨ 2 ≤ m) with rfl | rfl | h
    · omega
    · exact absurd (Nat.le_of_dvd (by norm_num) hpm) (by norm_num; omega)
    · exact h
  have hJr : J ≤ j.range := fun x hx => (hfix x).1 (hβJ x hx)
  have hJ₀c : Nat.card (J.comap j) = Nat.card J := by
    rw [← Subgroup.card_map_of_injective hj, Subgroup.map_comap_eq_self hJr]
  have hJ₀p : ∀ x ∈ J.comap j, x ^ p = 1 := fun x hx =>
    hj (by rw [map_pow, hJ _ hx, map_one])
  obtain ⟨t, ht, ht1, c, s, hc, hsc, hct, hst⟩ := exists_commute_invPair h₀
    (by rw [hkm]; exact hm2) hp hp5 (by rw [hkm]; exact hpm) hJ₀p (hJ₀c.symm ▸ hJc)
  refine ⟨j t, ht, fun h => ht1 (hj (h.trans (map_one j).symm)), j c, j s, ?_, ?_, ?_, ?_,
    (hfix (j c)).2 ⟨c, rfl⟩, (hfix (j s)).2 ⟨s, rfl⟩⟩
  · rw [orderOf_injective j hj, hc]
  · simpa only [map_mul, map_inv] using congrArg j hsc
  · rw [← map_mul, hct, map_mul]
  · rw [← map_mul, hst, map_mul]

end U3Aut

private theorem isCyclic_of_card_lt_sq {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : ∀ x : G, x ^ p = 1) (hc : Nat.card G < p ^ 2) : IsCyclic G := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (fun x => ⟨1, by rw [pow_one]; exact hG x⟩ : IsPGroup p G)
  have hk1 : k ≤ 1 := by
    by_contra h
    rw [hk] at hc
    exact absurd hc (not_lt.2 (Nat.pow_le_pow_right hp.pos (by omega)))
  exact isCyclic_of_card_dvd_prime (p := p)
    (by rw [hk]; exact (pow_dvd_pow p hk1).trans (pow_one p).dvd)

private theorem mem_of_pow_mem {G : Type} [Group G] {p : ℕ} (hp : p.Prime) {z : G}
    (hz : z ^ p = 1) {K : Subgroup G} {m : ℕ} (hm : z ^ m ∈ K) (hm1 : z ^ m ≠ 1) : z ∈ K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzo : orderOf z = p := orderOf_eq_prime hz fun h => hm1 (by rw [h, one_pow])
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := z) (n := m) (by
    rw [hzo, Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact fun hd => hm1 (orderOf_dvd_iff_pow_eq_one.1 (by rw [hzo]; exact hd)))
  rw [← hk]
  exact K.pow_mem hm k

private theorem exists_index_le_of_card_le {X P : Type} [Group X] [Finite X] [Group P]
    (φ : P →* MulAut X) {p : ℕ} (ω : R847O3.ThreeInvPair X)
    (hc : Nat.card φ.range ≤ p * Nat.card (MulAction.stabilizer φ.range ω)) :
    ∃ x g : X, orderOf x = 3 ∧ g * x * g⁻¹ = x⁻¹ ∧
      ∃ Q : Subgroup P, Q.index ≤ p ∧ ∀ u ∈ Q, φ u x = x ∧ φ u g = g := by
  refine ⟨ω.1.1, ω.1.2, ω.2.1, ω.2.2, (MulAction.stabilizer φ.range ω).comap φ.rangeRestrict,
    ?_, fun u hu => ?_⟩
  · rw [Subgroup.index_comap_of_surjective _ φ.rangeRestrict_surjective]
    have h1 := Subgroup.card_mul_index (MulAction.stabilizer φ.range ω)
    exact Nat.le_of_mul_le_mul_left (by rw [h1, mul_comm]; exact hc) Nat.card_pos
  · have h := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_comap.1 hu)
    rw [Subgroup.smul_def, MonoidHom.coe_rangeRestrict] at h
    exact ⟨congrArg (fun w : R847O3.ThreeInvPair X => w.1.1) h,
      congrArg (fun w : R847O3.ThreeInvPair X => w.1.2) h⟩

theorem lossPairAt_of_isU3 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsU3 X n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : R847O3.LossPairAt X p := by
  intro P _ _ hexp hPab φ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hSU, hZ⟩ := U3Loss.isSU3_of_isU3 hX
  obtain ⟨hn2, K, _, h, ⟨θ⟩⟩ := U3Loss.exists_equiv_primeFormP hX
  set Inn := (MulAut.conj : X →* MulAut X).range with hInn
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    P22y.conj_injective_of_center_eq_bot hZ
  have hrp : ∀ x ∈ φ.range, x ^ p = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, hexp, map_one]
  have hRc : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, hPab, map_mul]
  have hquot : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x ∉ Inn → ∃ k : ℕ, x ^ k * y ∈ Inn :=
    fun x hx y hy hxi => U3Loss.exists_pow_mul_mem_inner_u3 hX hp (by omega) (hrp x hx)
      (hrp y hy) (hRc x hx y hy) hxi
  have hβ : ∀ z ∈ φ.range, z ∉ Inn → MulAut.congr θ z ^ p = 1 ∧ MulAut.congr θ z ∉
      (MulAut.conj : _ →* MulAut (primeFormP h (1 : Matrix (Fin 3) (Fin 3) K))).range :=
    fun z hz hzi => ⟨by rw [← map_pow, hrp z hz, map_one],
      fun hi => hzi ((HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ z).1 hi)⟩
  have hback : ∀ (z : MulAut X) (c : primeFormP h (1 : Matrix (Fin 3) (Fin 3) K)),
      MulAut.congr θ z c = c → z (θ.symm c) = θ.symm c := fun z c hc => by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply] at hc
    exact θ.injective (by rw [hc, MulEquiv.apply_symm_apply])
  have hpair : ∀ c s : primeFormP h (1 : Matrix (Fin 3) (Fin 3) K), orderOf c = 3 →
      s * c * s⁻¹ = c⁻¹ →
        orderOf (θ.symm c) = 3 ∧ θ.symm s * θ.symm c * (θ.symm s)⁻¹ = (θ.symm c)⁻¹ :=
    fun c s hc hsc => ⟨by rw [MulEquiv.orderOf_eq, hc], by
      simpa only [map_mul, map_inv] using congrArg θ.symm hsc⟩
  have hω : ∀ c s : primeFormP h (1 : Matrix (Fin 3) (Fin 3) K), orderOf c = 3 →
      s * c * s⁻¹ = c⁻¹ → ∃ ω : R847O3.ThreeInvPair X, ∀ y : MulAut X,
        y (θ.symm c) = θ.symm c → y (θ.symm s) = θ.symm s → y • ω = ω :=
    fun c s hc hsc => ⟨⟨(θ.symm c, θ.symm s), hpair c s hc hsc⟩,
      fun y h1 h2 => Subtype.ext (Prod.ext h1 h2)⟩
  have h3 : ∃ x g : X, orderOf x = 3 ∧ g * x * g⁻¹ = x⁻¹ := by
    obtain ⟨c, s, hc, hsc, -⟩ :=
      U3Aut.exists_invPair_commute_line h (d := 1) (by rw [map_one, map_one])
    exact ⟨_, _, hpair c s hc hsc⟩
  have hfix : ∀ z ∈ φ.range, z ∉ Inn → ∃ x g : X, orderOf x = 3 ∧ g * x * g⁻¹ = x⁻¹ ∧
      z x = x ∧ z g = g := fun z hz hzi => by
    obtain ⟨-, E₀, _, h₀, j, hj, hfx⟩ :=
      U3Aut.exists_fixed_eq_range h hn2 hp hp5 (hβ z hz hzi).1 (hβ z hz hzi).2
    obtain ⟨c, s, hc, hsc, -⟩ :=
      U3Aut.exists_invPair_commute_line h₀ (d := 1) (by rw [map_one, map_one])
    obtain ⟨hc', hsc'⟩ := hpair (j c) (j s) (by rw [orderOf_injective j hj, hc])
      (by simpa only [map_mul, map_inv] using congrArg j hsc)
    exact ⟨_, _, hc', hsc', hback z _ ((hfx (j c)).2 ⟨c, rfl⟩),
      hback z _ ((hfx (j s)).2 ⟨s, rfl⟩)⟩
  by_cases hcyc : IsCyclic ↥(φ.range ⊓ Inn)
  · exact R847O3.exists_invPair_index_le_of hp hexp hPab φ h3 hcyc hquot hfix
  set I := φ.range ⊓ Inn with hI
  have hIp : ∀ x : I, x ^ p = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hrp x (Subgroup.mem_inf.1 x.2).1, Subgroup.coe_one])
  have hcardI2 : p ^ 2 ≤ Nat.card I :=
    not_lt.1 fun hlt => hcyc (isCyclic_of_card_lt_sq hp hIp hlt)
  have hpk : p ∣ 2 ^ n + 1 := by
    by_contra hpk
    refine hcyc (isCyclic_of_card_lt_sq hp hIp ((UCK.u3RankOne X n hSU p hp (by omega) hpk I
      inf_le_right ⟨⟨⟨fun a b => Subtype.ext (hRc a (Subgroup.mem_inf.1 a.2).1 b
        (Subgroup.mem_inf.1 b.2).1)⟩⟩, fun x hx => hrp x (Subgroup.mem_inf.1 hx).1⟩).trans_lt ?_))
    nlinarith
  set B := I.comap (MulAut.conj : X →* MulAut X) with hB
  have hBI : B.map (MulAut.conj : X →* MulAut X) = I := Subgroup.map_comap_eq_self inf_le_right
  set J := B.map θ.toMonoidHom with hJdef
  have hJc : Nat.card J = Nat.card I := by
    rw [hJdef, Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective, ← hBI,
      Subgroup.card_map_of_injective hinj]
  have hJp : ∀ x ∈ J, x ^ p = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : MulAut.conj (b ^ p) = 1 := by
      rw [map_pow]
      exact hrp _ (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hb)).1
    rw [← map_pow, hinj (h1.trans (map_one _).symm), map_one]
  have hJ2 : p ^ 2 ≤ Nat.card J := by rw [hJc]; exact hcardI2
  have hI2 : Nat.card I ≤ p ^ 2 := by
    rw [← hJc]; exact U3Aut.card_le_of_pow_eq_one h hn2 hp hp5 hpk hJp
  have hpull : ∀ t ∈ J, t ≠ 1 → ∃ w ∈ φ.range, w ∈ Inn ∧ w ≠ 1 ∧
      ∀ c : primeFormP h (1 : Matrix (Fin 3) (Fin 3) K), c * t = t * c →
        w (θ.symm c) = θ.symm c := by
    rintro _ ⟨b, hb, rfl⟩ ht1
    have hbI := Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hb)
    refine ⟨MulAut.conj b, hbI.1, hbI.2, fun h1 => ht1 ?_, fun c hct => ?_⟩
    · rw [hinj (h1.trans (map_one _).symm), map_one]
    · have h2 := congrArg θ.symm hct
      rw [map_mul, map_mul, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h2
      rw [MulAut.conj_apply, ← h2, mul_inv_cancel_right]
  by_cases hall : φ.range ≤ Inn
  ·
    obtain ⟨t, ht, ht1, c, s, hc, hsc, hct, hst⟩ :=
      U3Aut.exists_commute_invPair h hn2 hp hp5 hpk hJp hJ2
    obtain ⟨w, hwR, -, hw1, hwc⟩ := hpull t ht ht1
    obtain ⟨ω, hωf⟩ := hω c s hc hsc
    refine exists_index_le_of_card_le φ ω ?_
    have hwω : (⟨w, hwR⟩ : φ.range) • ω = ω := hωf w (hwc c hct) (hwc s hst)
    have hwo : orderOf (⟨⟨w, hwR⟩, hwω⟩ : MulAction.stabilizer φ.range ω) = p :=
      orderOf_eq_prime (Subtype.ext (Subtype.ext (hrp w hwR)))
        fun h1 => hw1 (congrArg Subtype.val (congrArg Subtype.val h1))
    have hpS : p ≤ Nat.card (MulAction.stabilizer φ.range ω) :=
      Nat.le_of_dvd Nat.card_pos (by rw [← hwo]; exact orderOf_dvd_natCard _)
    have hR : Nat.card φ.range = Nat.card I := by rw [hI, inf_eq_left.2 hall]
    rw [hR, le_antisymm hI2 hcardI2, sq]
    exact Nat.mul_le_mul le_rfl hpS
  obtain ⟨z, hzR, hzi⟩ := SetLike.not_le_iff_exists.1 hall
  obtain ⟨hβp, hβi⟩ := hβ z hzR hzi
  have hzB : ∀ b ∈ B, z b = b := fun b hb => hinj (by
    have hconj : MulAut.conj (z b) = z * MulAut.conj b * z⁻¹ := by
      ext g
      simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    rw [hconj, hRc z hzR _ (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hb)).1,
      mul_inv_cancel_right])
  have hβJ : ∀ x ∈ J, MulAut.congr θ z x = x := by
    rintro _ ⟨b, hb, rfl⟩
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, hzB b hb]
  obtain ⟨t, ht, ht1, c, s, hc, hsc, hct, hst, hβc, hβs⟩ :=
    U3Aut.exists_commute_invPair_fixed h hn2 hp hp5 hβp hβi hpk hJp hJ2 hβJ
  obtain ⟨w, hwR, hwi, hw1, hwc⟩ := hpull t ht ht1
  obtain ⟨ω, hωf⟩ := hω c s hc hsc
  have hzω : (⟨z, hzR⟩ : φ.range) • ω = ω := hωf z (hback z c hβc) (hback z s hβs)
  have hwω : (⟨w, hwR⟩ : φ.range) • ω = ω := hωf w (hwc c hct) (hwc s hst)
  refine exists_index_le_of_card_le φ ω ?_
  have hzp := hrp z hzR
  have hz1 : z ≠ 1 := fun h1 => hzi (h1 ▸ Inn.one_mem)
  have hmod : ∀ m, z ^ (m % p) = z ^ m := fun m => by
    conv_rhs => rw [← Nat.mod_add_div m p, pow_add, pow_mul, hzp, one_pow, mul_one]
  have hsurj : Function.Surjective (fun ai : Fin p × I => (⟨z ^ (ai.1 : ℕ) * ai.2,
      φ.range.mul_mem (φ.range.pow_mem hzR _) (Subgroup.mem_inf.1 ai.2.2).1⟩ : φ.range)) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := hquot z hzR y hy hzi
    refine ⟨(⟨(p - 1) * k % p, Nat.mod_lt _ hp.pos⟩, ⟨z ^ k * y, Subgroup.mem_inf.2
      ⟨φ.range.mul_mem (φ.range.pow_mem hzR k) hy, hk⟩⟩), Subtype.ext ?_⟩
    change z ^ ((p - 1) * k % p) * (z ^ k * y) = y
    rw [hmod, ← mul_assoc, ← pow_add, show (p - 1) * k + k = p * k by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hp.one_lt.le], pow_mul, hzp,
      one_pow, one_mul]
  have hRle : Nat.card φ.range ≤ p * Nat.card I := by
    have := Nat.card_le_card_of_surjective _ hsurj
    rwa [Nat.card_prod, Nat.card_fin] at this
  have hSle : p ^ 2 ≤ Nat.card (MulAction.stabilizer φ.range ω) := by
    by_contra hlt
    have hHp : ∀ x : MulAction.stabilizer φ.range ω, x ^ p = 1 := fun x =>
      Subtype.ext (Subtype.ext (hrp _ x.1.2))
    haveI := isCyclic_of_card_lt_sq hp hHp (not_le.1 hlt)
    obtain ⟨k, hk⟩ := P22y.exists_pow_eq_of_isCyclic hp
      (a := (⟨⟨z, hzR⟩, hzω⟩ : MulAction.stabilizer φ.range ω)) (b := ⟨⟨w, hwR⟩, hwω⟩)
      (hHp _) (fun h1 => hz1 (congrArg Subtype.val (congrArg Subtype.val h1))) (hHp _)
    have hzk : z ^ k = w := congrArg Subtype.val (congrArg Subtype.val hk)
    exact hzi (mem_of_pow_mem hp hzp (by rw [hzk]; exact hwi) (by rw [hzk]; exact hw1))
  calc Nat.card φ.range ≤ p * p ^ 2 := hRle.trans (Nat.mul_le_mul le_rfl hI2)
    _ ≤ p * Nat.card (MulAction.stabilizer φ.range ω) := Nat.mul_le_mul le_rfl hSle

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
