module

public import CFSG.RankThree.PartTwo.Sec13.Item131bProofHeis
import CFSG.RankThree.PartTwo.KFacts.KS12ClassOut
import CFSG.RankThree.PartTwo.KFacts.KS12ClassExp
import CFSG.RankThree.PartTwo.Sec21.Item222KLeProof
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec12.Item125Basic
import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec13.Item131Transport
public import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha
public import CFSG.RankThree.PartTwo.Sec13.Item131bProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item131bProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section General

variable {H : Type} [Group H]

theorem le_normalizer_sup {T X Y : Subgroup H} (hX : T ≤ Subgroup.normalizer (X : Set H))
    (hY : T ≤ Subgroup.normalizer (Y : Set H)) :
    T ≤ Subgroup.normalizer ((X ⊔ Y : Subgroup H) : Set H) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at *
  rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hX ht),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hY ht)]

theorem mem_of_mk_mem_of_theta_le_normalizer [Finite H] {X : Subgroup H}
    (hX : aschbacherSolvableCore 3 H ≤ Subgroup.normalizer (X : Set H)) {x : H} {k : ℕ}
    (hx : x ^ 3 ^ k = 1)
    (hmem : QuotientGroup.mk' (aschbacherSolvableCore 3 H) x ∈
      X.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) : x ∈ X := by
  obtain ⟨l, hl, hlx⟩ := hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hlx
  have htN := hX hlx
  have hxe : x = l * (l⁻¹ * x) := by rw [mul_inv_cancel_left]
  have hpow : ∀ n : ℕ, ∃ ln ∈ X, (l * (l⁻¹ * x)) ^ n = ln * (l⁻¹ * x) ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, X.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨ln, hln, hn⟩ := ih
      refine ⟨ln * ((l⁻¹ * x) ^ n * l * ((l⁻¹ * x) ^ n)⁻¹), X.mul_mem hln ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ htN n) l).mp hl
      · rw [pow_succ, hn]
        group
  obtain ⟨ln, hln, hn⟩ := hpow (3 ^ k)
  rw [← hxe, hx] at hn
  have htk : (l⁻¹ * x) ^ 3 ^ k ∈ X := by
    have : (l⁻¹ * x) ^ 3 ^ k = ln⁻¹ := eq_inv_of_mul_eq_one_right hn.symm
    rw [this]
    exact X.inv_mem hln
  have hcop : (3 ^ k).Coprime (orderOf (l⁻¹ * x)) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    apply (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).2.2.1
    exact h3.trans (Subgroup.orderOf_dvd_natCard _ hlx)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have htL : l⁻¹ * x ∈ X := hm ▸ X.pow_mem htk m
  exact hxe ▸ X.mul_mem hl htL

end General

section Bar

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem lBar_commute_of_ne {K L : Subgroup G} (hK : K ∈ thetaComponentsAt 3 c)
    (hL : L ∈ thetaComponentsAt 3 c) (hne : K ≠ L) {x y} (hx : x ∈ Sec12.lBar c K)
    (hy : y ∈ Sec12.lBar c L) : x * y = y * x := by
  obtain ⟨k, hk, rfl⟩ := hx
  obtain ⟨l, hl, rfl⟩ := hy
  have hθ : inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :=
    inSubgroup_theta_le_of_isSubnormal (centralizer_le_normalizer_zpowers c)
      (centralizer_normal_in_normalizer_zpowers c).isSubnormal
  obtain ⟨t, ht, hte⟩ := hθ (Sec10.commutator_mem_theta_of_ne hK hL hne
    (Subgroup.mem_subgroupOf.mp hk) (Subgroup.mem_subgroupOf.mp hl))
  have htk : t = k * l * k⁻¹ * l⁻¹ := Subtype.ext (by simpa using hte)
  have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))) (k * l * k⁻¹ * l⁻¹) = 1 := by
    rw [← htk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ht
  simp only [map_mul, map_inv] at h1
  have h2 := congrArg (fun z => z * (QuotientGroup.mk' _ l * QuotientGroup.mk' _ k)) h1
  simp only [one_mul] at h2
  rw [← h2]
  group

theorem coe_mem_lBar_of_heis
    (hD : Sec13Data G A c L)
    (hty : HeisType (L ⧸ aschbacherSolvableCore 3 L)) {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 c) (hKL : K ≠ L)
    (hK6 : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))
    (hcK : c ∈ K) (hAK : A ≤ Subgroup.normalizer (K : Set G)) {u : lBarA c L A}
    (hu3 : u ^ 3 = 1)
    (huΛ : ∀ v ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * v = v * u) :
    ((u : lBarA c L A) : HBar c) ∈ Sec12.lBar c K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := hD.mem_thetaComponentsAt
  have hKN := le_normalizer_zpowers_of_mem hK
  have hLK : K ≤ Subgroup.normalizer (L : Set G) := fun k hk =>
    Sec21.mem_normalizer_of_mem_thetaComponentsAt hK hL hk
  have hLAK : L ⊔ A ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (fun l hl => Sec21.mem_normalizer_of_mem_thetaComponentsAt hL hK hl) hAK
  have hūN : ((u : lBarA c L A) : HBar c) ∈
      Subgroup.normalizer ((Sec12.lBar c K : Subgroup (HBar c)) : Set (HBar c)) := by
    obtain ⟨z, hz, hzu⟩ := u.2
    rw [← hzu]
    exact mk_mem_normalizer_lBar (hLAK (Subgroup.mem_subgroupOf.mp hz))
  set σ := (Sec12.lBar c K).normalizerMonoidHom ⟨_, hūN⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have h1 : (⟨_, hūN⟩ : Subgroup.normalizer ((Sec12.lBar c K : Subgroup (HBar c)) :
        Set (HBar c))) ^ 3 = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hu3)
    rw [h1, map_one]
  obtain ⟨η, -⟩ := exists_lBarEquiv hK
  have hq : IsQuasisimple (Sec12.lBar c K) :=
    LocalCores.isQuasisimple_of_mulEquiv η (Sec6.isQuasisimple_of_mem_thetaComponentsAt hK)
  have htc : Sec4.IsTripleCover (Sec12.lBar c K) (alternatingGroup (Fin 6)) :=
    isTripleCover_of_mulEquiv η hK6
  obtain ⟨κ, hκ⟩ := KFacts.ks12OutInner _ hq (Or.inl htc) σ ⟨1, by rw [pow_one]; exact hσ3⟩
  have hconj : ∀ y : Sec12.lBar c K,
      ((u : lBarA c L A) : HBar c) * (y : HBar c) * ((u : lBarA c L A) : HBar c)⁻¹ =
        (κ : HBar c) * y * (κ : HBar c)⁻¹ := by
    intro y
    have h := congrArg (fun f : MulAut (Sec12.lBar c K) => ((f y : Sec12.lBar c K) : HBar c)) hκ
    simp only [hσ, Sec4.normalizerMonoidHom_apply_coe, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  have hZ3 : ∀ z ∈ Subgroup.center (Sec12.lBar c K), z ^ 3 = 1 := by
    intro z hz
    have hdvd := Subgroup.orderOf_dvd_natCard _ hz
    rw [htc.1] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hκ3 : κ ^ 3 = 1 := by
    have h1 : MulAut.conj (κ ^ 3) = 1 := by rw [map_pow, ← hκ, hσ3]
    have hZ : κ ^ 3 ∈ Subgroup.center (Sec12.lBar c K) := Subgroup.mem_center_iff.mpr fun y => by
      have h2 := congrArg (fun f : MulAut (Sec12.lBar c K) => f y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * κ ^ 3 = κ ^ 3 * y * (κ ^ 3)⁻¹ * κ ^ 3 := by rw [h2]
        _ = κ ^ 3 * y := by group
    have h9 := hZ3 _ hZ
    have h9' : κ ^ 9 = 1 := by rw [show 9 = 3 * 3 from rfl, pow_mul]; exact h9
    exact KFacts.pow_three_eq_one_of_isTripleCover (Or.inl htc) κ ⟨2, by norm_num; exact h9'⟩
  set d : HBar c := (κ : HBar c)⁻¹ * ((u : lBarA c L A) : HBar c) with hd
  have hdK : ∀ y ∈ Sec12.lBar c K, d * y = y * d := by
    intro y hy
    have h := hconj ⟨y, hy⟩
    calc d * y = (κ : HBar c)⁻¹ *
          (((u : lBarA c L A) : HBar c) * y * ((u : lBarA c L A) : HBar c)⁻¹) *
          ((u : lBarA c L A) : HBar c) := by rw [hd]; group
      _ = (κ : HBar c)⁻¹ * ((κ : HBar c) * y * (κ : HBar c)⁻¹) *
          ((u : lBarA c L A) : HBar c) := by rw [h]
      _ = y * d := by rw [hd]; group
  have hdΛ : ∀ y ∈ Sec12.lBar c L, d * y = y * d := by
    intro y hy
    have h1 : ((u : lBarA c L A) : HBar c) * y = y * ((u : lBarA c L A) : HBar c) :=
      congrArg Subtype.val (huΛ ⟨y, lBar_le_lBarA hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
    have h2 : (κ : HBar c) * y = y * (κ : HBar c) := lBar_commute_of_ne hK hL hKL κ.2 hy
    have h2' : (κ : HBar c)⁻¹ * y = y * (κ : HBar c)⁻¹ := by
      calc (κ : HBar c)⁻¹ * y = (κ : HBar c)⁻¹ * (y * (κ : HBar c)) * (κ : HBar c)⁻¹ := by group
        _ = (κ : HBar c)⁻¹ * ((κ : HBar c) * y) * (κ : HBar c)⁻¹ := by rw [h2]
        _ = y * (κ : HBar c)⁻¹ := by group
    calc d * y = (κ : HBar c)⁻¹ * (((u : lBarA c L A) : HBar c) * y) := by rw [hd]; group
      _ = (κ : HBar c)⁻¹ * y * ((u : lBarA c L A) : HBar c) := by rw [h1]; group
      _ = y * d := by rw [h2', hd]; group
  have hdκ : d * (κ : HBar c) = (κ : HBar c) * d := hdK _ κ.2
  have hd3 : d ^ 3 = 1 := by
    have hu' : ((u : lBarA c L A) : HBar c) = (κ : HBar c) * d := by rw [hd]; group
    have hcomm : Commute (κ : HBar c) d := hdκ.symm
    have h1 : ((u : lBarA c L A) : HBar c) ^ 3 = 1 := by
      have := congrArg Subtype.val hu3
      simpa using this
    rw [hu', hcomm.mul_pow] at h1
    have hκ3' : (κ : HBar c) ^ 3 = 1 := by
      have := congrArg Subtype.val hκ3
      simpa using this
    rwa [hκ3', one_mul] at h1
  by_cases hdmem : d ∈ Sec12.lBar c K
  · have hu' : ((u : lBarA c L A) : HBar c) = (κ : HBar c) * d := by rw [hd]; group
    rw [hu']
    exact mul_mem κ.2 hdmem
  exfalso
  obtain ⟨-, ⟨e6⟩⟩ := id htc
  have h360 : Nat.card (Sec12.lBar c K ⧸ Subgroup.center (Sec12.lBar c K)) = 360 := by
    rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  obtain ⟨ξ, hξ⟩ := exists_prime_orderOf_dvd_card' 3
    (G := Sec12.lBar c K ⧸ Subgroup.center (Sec12.lBar c K)) (by rw [h360]; norm_num)
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective ξ
  have hx₀Z : x₀ ∉ Subgroup.center (Sec12.lBar c K) := by
    intro h
    rw [(QuotientGroup.eq_one_iff x₀).mpr h, orderOf_one] at hξ
    norm_num at hξ
  have hx₀3 : x₀ ^ 3 = 1 := by
    have h0 : ((x₀ : Sec12.lBar c K) : Sec12.lBar c K ⧸ Subgroup.center _) ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [hξ])
    have h1 : ((x₀ ^ 3 : Sec12.lBar c K) : Sec12.lBar c K ⧸ Subgroup.center _) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact h0
    have h9 := hZ3 _ ((QuotientGroup.eq_one_iff _).mp h1)
    have h9' : x₀ ^ 9 = 1 := by rw [show 9 = 3 * 3 from rfl, pow_mul]; exact h9
    exact KFacts.pow_three_eq_one_of_isTripleCover (Or.inl htc) x₀ ⟨2, by norm_num; exact h9'⟩
  have hcN : c ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hKN hcK
  set cb : Sec12.lBar c K := ⟨QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
        (⟨c, hcN⟩ : Subgroup.normalizer (Subgroup.zpowers c : Set G)),
    ⟨⟨c, hcN⟩, Subgroup.mem_subgroupOf.mpr hcK, rfl⟩⟩ with hcb
  have hcbZ : cb ∈ Subgroup.center (Sec12.lBar c K) := by
    refine Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_
    obtain ⟨k, hk, hky⟩ := y.2
    change (y : HBar c) * QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
        (⟨c, hcN⟩ : Subgroup.normalizer (Subgroup.zpowers c : Set G)) =
      QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
        (⟨c, hcN⟩ : Subgroup.normalizer (Subgroup.zpowers c : Set G)) * y
    rw [← hky, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (Sec6.le_centralizer_of_mem_thetaComponentsAt hK (Subgroup.mem_subgroupOf.mp hk))
  have hcb1 : (cb : HBar c) ≠ 1 := fun h => mkC_ne_one hD (Subtype.ext h)
  have hcb3 : (cb : HBar c) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (mkC (L := L) hD.mem_A)
    rw [orderOf_mkC hD] at h
    exact congrArg Subtype.val h
  set X : HBar c := (x₀ : HBar c) with hX
  set C : HBar c := (cb : HBar c) with hC
  have hX3 : X ^ 3 = 1 := by simpa using congrArg Subtype.val hx₀3
  have hXK : X ∈ Sec12.lBar c K := x₀.2
  have hCK : C ∈ Sec12.lBar c K := cb.2
  have hXC : Commute X C := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcbZ x₀)
  have hX1 : X ≠ 1 := fun h => hx₀Z (by
    have : x₀ = 1 := Subtype.ext h
    rw [this]
    exact Subgroup.one_mem _)
  have hXo : orderOf X = 3 := orderOf_eq_prime hX3 hX1
  have hCo : orderOf C = 3 := orderOf_eq_prime hcb3 hcb1
  have hCX : C ∉ Subgroup.zpowers X := by
    intro hmem
    have heq : Subgroup.zpowers C = Subgroup.zpowers X :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hXo, hCo])
    have hXmem : X ∈ Subgroup.zpowers C := heq ▸ Subgroup.mem_zpowers X
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hXmem
    apply hx₀Z
    have : x₀ = cb ^ j := Subtype.ext (by simpa [hX, hC] using hj.symm)
    rw [this]
    exact zpow_mem hcbZ j
  set E₂ := Subgroup.zpowers X ⊔ Subgroup.zpowers C with hE₂
  have hE₂K : E₂ ≤ Sec12.lBar c K :=
    sup_le (Subgroup.zpowers_le.mpr hXK) (Subgroup.zpowers_le.mpr hCK)
  have hE₂e : CFSG.Assembly.IsElemAbelian 3 E₂ :=
    Sec15.isElemAbelian_sup_zpowers (isElemAbelian_zpowers hX3) hcb3 fun e he => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
      exact (hXC.zpow_left k).eq
  have hE₂9 : Nat.card E₂ = 9 := by
    have hN : Subgroup.zpowers C ≤ Subgroup.normalizer (Subgroup.zpowers X : Set (HBar c)) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [((hXC.zpow_left k).symm).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers X k
    have h := Sec6.card_sup_mul_card_inf hN
    have hbot : Subgroup.zpowers C ⊓ Subgroup.zpowers X = ⊥ := by
      rw [inf_comm]
      exact Sec12.inf_zpowers_eq_bot_of_not_mem hCo hCX
    rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hCo, hXo,
      sup_comm] at h
    exact h
  have hdE₂ : d ∉ E₂ := fun h => hdmem (hE₂K h)
  have hd1 : d ≠ 1 := fun h => hdmem (h ▸ Subgroup.one_mem _)
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  set E₃ := E₂ ⊔ Subgroup.zpowers d with hE₃
  have hE₃e : CFSG.Assembly.IsElemAbelian 3 E₃ :=
    Sec15.isElemAbelian_sup_zpowers hE₂e hd3 fun e he => (hdK e (hE₂K he)).symm
  have hE₃27 : Nat.card E₃ = 27 := by
    have hN : Subgroup.zpowers d ≤ Subgroup.normalizer (E₂ : Set (HBar c)) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      rw [hdK y (hE₂K hy), mul_inv_cancel_right]
      exact hy
    have h := Sec6.card_sup_mul_card_inf hN
    have hbot : Subgroup.zpowers d ⊓ E₂ = ⊥ := by
      rw [inf_comm]
      exact Sec12.inf_zpowers_eq_bot_of_not_mem hdo hdE₂
    rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, hdo, hE₂9, sup_comm] at h
    exact h
  have hE₃Λ : E₃ ≤ Subgroup.centralizer ((Sec12.lBar c L : Subgroup (HBar c)) : Set (HBar c)) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le] <;>
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    · exact (lBar_commute_of_ne hK hL hKL hXK hy).symm
    · exact (lBar_commute_of_ne hK hL hKL hCK hy).symm
    · exact (hdΛ y hy).symm
  have hKM : Sec12.lBar c K ≤ ((L ⊔ A ⊔ K).subgroupOf
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ le_sup_right)
  have huM : ((u : lBarA c L A) : HBar c) ∈ ((L ⊔ A ⊔ K).subgroupOf
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) := by
    obtain ⟨z, hz, hzu⟩ := u.2
    exact ⟨z, Subgroup.subgroupOf_mono _ le_sup_left hz, hzu⟩
  have hE₃M : E₃ ≤ ((L ⊔ A ⊔ K).subgroupOf
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) :=
    sup_le (hE₂K.trans hKM) (Subgroup.zpowers_le.mpr (mul_mem (inv_mem (hKM κ.2)) huM))
  obtain ⟨S, hSM, hSe, hScard, hSmap⟩ := exists_elemAbelian_map_eq hE₃e hE₃M
  have hEe : CFSG.Assembly.IsElemAbelian 3
      (S.map (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype) :=
    isElemAbelian_map hSe _
  have hE27 : Nat.card (S.map (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype) = 27 := by
    rw [Subgroup.card_map_of_injective Subtype.coe_injective, hScard, hE₃27]
  have hLAKN : L ⊔ A ⊔ K ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hD.le_normalizer) hLK
  have hEC : S.map (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype ≤
      Sec4.thetaQuotCentralizer L := by
    rintro _ ⟨s, hs, rfl⟩
    refine mem_thetaQuotCentralizer_of_mk_commute hL (g := s)
      (hLAKN (Subgroup.mem_subgroupOf.mp (hSM hs))) fun l hl => ?_
    have hsE : QuotientGroup.mk' _ s ∈ E₃ := hSmap ▸ Subgroup.mem_map_of_mem _ hs
    exact ((Subgroup.mem_centralizer_iff.mp (hE₃Λ hsE)) _
      ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩).symm
  exact no_E27_le hD hty hEe hE27 hEC

end Bar

end CFSG.RankThree.PartTwo.Sec13.Item131bProof

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Item131bProof

theorem step131bHeisK
    (h45 : Sec4.Item4_5) : Step131bHeisK := by
  intro G _ _ A c L hD hH hty K hK hKL hK6 hcK
  have hL := hD.mem_thetaComponentsAt
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hD.toTheoremFourHyp hD.isElemAbelian
      hD.mem_A hD.ne_one K hK
  obtain ⟨U, hU, hUΛ, hUV, -⟩ := isHeisCentral_facts hD hH
  have hUK : ∀ u ∈ U, ((u : lBarA c L A) : HBar c) ∈ Sec12.lBar c K := by
    intro u hu
    have hu3 : u ^ 3 = 1 := by
      have h1 := Monoid.pow_exponent_eq_one (⟨u, hu⟩ : U)
      rw [hU.2.2] at h1
      simpa using congrArg Subtype.val h1
    exact coe_mem_lBar_of_heis hD hty hK hKL hK6 hcK hAK hu3 (hUΛ u hu)
  intro a ha
  set a' : Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    ⟨a, hD.A_le_normalizer_zpowers ha⟩ with ha'
  have hmem : QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))) a' ∈
      (K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
        L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) := by
    have h1 : aBarHom hD ⟨a, ha⟩ ∈ U ⊔ (Sec12.lBar c L).subgroupOf (lBarA c L A) := by
      rw [hUV]
      exact Subgroup.mem_top _
    have h2 := Subgroup.mem_map_of_mem (lBarA c L A).subtype h1
    rw [Subgroup.coe_subtype, aBarHom_apply, Subgroup.map_sup] at h2
    rw [Subgroup.map_sup]
    refine (sup_le ?_ ?_ : _ ≤ Sec12.lBar c K ⊔ Sec12.lBar c L) h2
    · rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.mem_sup_left (hUK u hu)
    · rintro _ ⟨v, hv, rfl⟩
      exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hv)
  have hθN := le_normalizer_sup (theta_le_normalizer_lBar hK) (theta_le_normalizer_lBar hL)
  have ha3 : a' ^ 3 ^ 1 = 1 := Subtype.ext (by simpa using hD.isElemAbelian.2 a ha)
  have h := mem_of_mk_mem_of_theta_le_normalizer hθN ha3 hmem
  have h' : (a : G) ∈ (K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map
        (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype := ⟨a', h, rfl⟩
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (le_normalizer_zpowers_of_mem hK),
    inf_eq_left.mpr (le_normalizer_zpowers_of_mem hL)] at h'
  rwa [sup_comm] at h'

end CFSG.RankThree.PartTwo.Sec13
