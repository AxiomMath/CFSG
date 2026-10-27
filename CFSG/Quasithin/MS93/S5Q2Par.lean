module

public import CFSG.Quasithin.MS93.S5BXZ
public import CFSG.Quasithin.MS93.MSPSix

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace MSP

variable {K : Type} [Field K]

theorem xPoint_not_le_commutator (hK : Nat.card K = 2) {p : Submodule K (V4 K)}
    (hp : IsPoint p) : ¬ xPoint p ≤ commutator (Sp4 K) := by
  intro hle
  obtain ⟨v, hv, rfl⟩ := exists_eq_span_of_isPoint hp
  exact transv_not_mem_commutator_of_card_two hK hv 1 one_ne_zero (hle (transv_mem_xPoint v 1))

theorem qPoint_not_le_commutator (hK : Nat.card K = 2) {p : Submodule K (V4 K)}
    (hp : IsPoint p) : ¬ qPoint p ≤ commutator (Sp4 K) :=
  fun hle => xPoint_not_le_commutator hK hp ((xPoint_le_qPoint hp).trans hle)

theorem qLine_not_le_commutator (hK : Nat.card K = 2) {l : Submodule K (V4 K)}
    (hl : IsLine l) : ¬ qLine l ≤ commutator (Sp4 K) := by
  intro hle
  have h2 : Module.finrank K l = 2 := hl.1
  obtain ⟨v, hvl, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := l) (by
    rintro rfl
    simp at h2)
  have hpl : (K ∙ v) ≤ l := (Submodule.span_singleton_le_iff_mem v l).2 hvl
  exact xPoint_not_le_commutator hK (isPoint_span hv)
    ((xPoint_le_qLine hl hpl).trans hle)

theorem card_qLine_inf_commutator (hK : Nat.card K = 2) {l : Submodule K (V4 K)}
    (hl : IsLine l) : Nat.card ↥(qLine l ⊓ commutator (Sp4 K)) = 4 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨c⟩ := nonempty_ringEquiv_of_card_two hK
  have hidx := index_commutator c
  have hrel : (commutator (Sp4 K)).relIndex (qLine l) = 2 := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal (commutator (Sp4 K)) (qLine l)
    rw [hidx] at hdvd
    have hne : (commutator (Sp4 K)).relIndex (qLine l) ≠ 1 := fun h1 =>
      qLine_not_le_commutator hK hl (Subgroup.relIndex_eq_one.1 h1)
    have hpos := (Nat.dvd_prime Nat.prime_two).1 hdvd
    omega
  have hcard := Subgroup.card_mul_index ((commutator (Sp4 K)).subgroupOf (qLine l))
  rw [← Subgroup.relIndex, hrel, card_qLine hl, hK] at hcard
  have e : Nat.card ↥((commutator (Sp4 K)).subgroupOf (qLine l)) =
      Nat.card ↥(qLine l ⊓ commutator (Sp4 K)) := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  omega

theorem eq_qLine_inf_commutator (hK : Nat.card K = 2) {l : Submodule K (V4 K)} (hl : IsLine l)
    {E : Subgroup (Sp4 K)} (hEl : E ≤ qLine l) (hEc : E ≤ commutator (Sp4 K))
    (hE : 4 ≤ Nat.card E) : E = qLine l ⊓ commutator (Sp4 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  refine Subgroup.eq_of_le_of_card_ge (le_inf hEl hEc) ?_
  rw [card_qLine_inf_commutator hK hl]
  exact hE

end MSP

namespace S5Q2

section Xq

variable {G : Type} [Group G] {M : Subgroup G}

theorem mul_comm_of_mem_Xq {x y : G} (hx : x ∈ Xq M) (hy : y ∈ Xq M) : x * y = y * x :=
  Subgroup.mem_centralizer_iff.1 ((PU.omegaOneCenterOf_le_centerOf _ hy).2) x
    (Xq_le_pCoreOf M hx)

theorem sq_eq_one_of_mem_Xq {x : G} (hx : x ∈ Xq M) : x ^ 2 = 1 := by
  have hx' : x ∈ Subgroup.closure {y | y ∈ centerOf (pCoreOf 2 M) ∧ y ^ 2 = 1} := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy => exact hy.2
  | one => simp
  | mul y z hy hz ihy ihz =>
    have hyz : y * z = z * y := mul_comm_of_mem_Xq hy hz
    rw [Commute.mul_pow hyz 2, ihy, ihz, one_mul]
  | inv y _ ih => rw [inv_pow, ih, inv_one]

end Xq

section Even

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Finite G] in
theorem mem_of_pow_mem_of_coprime {S : Subgroup G} {x : G} {r s : ℕ} (hrs : Nat.Coprime r s)
    (hr : x ^ r ∈ S) (hs : x ^ s ∈ S) : x ∈ S := by
  have h := Nat.gcd_eq_gcd_ab r s
  rw [hrs.gcd_eq_one, Nat.cast_one] at h
  have e : x = (x ^ r) ^ (Nat.gcdA r s) * (x ^ s) ^ (Nat.gcdB r s) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [e]
  exact S.mul_mem (S.zpow_mem hr _) (S.zpow_mem hs _)

theorem commute_of_map_eq_one (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {m : ↥M}
    (hm : a m = 1) {x : G} (hx : x ∈ Zq M L) : (m : G) * x = x * m := by
  set S := Subgroup.centralizer ({x} : Set G)
  suffices hmS : (m : G) ∈ S from Subgroup.mem_centralizer_singleton_iff.1 hmS
  obtain ⟨e, r, hr, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (m : G)).ne'
  have hcop : Nat.Coprime r (2 ^ e) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hr)
  refine mem_of_pow_mem_of_coprime hcop ?_ ?_
  ·
    have h2 : ((m ^ r : ↥M) : G) ∈ pCoreOf 2 M := by
      refine S5B.mem_pCoreOf_of_ker h hd (by rw [map_pow, hm, one_pow]) ⟨e, ?_⟩
      rw [Subgroup.coe_pow, ← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
    rw [Subgroup.coe_pow] at h2
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 ((PU.omegaOneCenterOf_le_centerOf _ hx.1).2) _ h2))
  ·
    have hodd : ((m : G) ^ 2 ^ e) ^ r = 1 := by rw [← pow_mul, ← hn, pow_orderOf_eq_one]
    obtain ⟨f, hf⟩ := h.exists_pow_mem_L (M.pow_mem m.2 (2 ^ e))
    have hcop' : Nat.Coprime (2 ^ f) r := Nat.Coprime.pow_left f (Nat.coprime_two_left.2 hr)
    have hL : (m : G) ^ 2 ^ e ∈ L :=
      mem_of_pow_mem_of_coprime hcop' hf (by rw [hodd]; exact L.one_mem)
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 hx.2 _ hL))

theorem commute_of_map_mem (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {m : ↥M}
    (hm : a m ∈ (L.subgroupOf M).map a) {x : G} (hx : x ∈ Zq M L) : (m : G) * x = x * m := by
  obtain ⟨l, hl, hla⟩ := hm
  have hk : a (l⁻¹ * m) = 1 := by rw [map_mul, map_inv, hla, inv_mul_cancel]
  have h1 := commute_of_map_eq_one h hd hk hx
  have h2 : (l : G) * x = x * l :=
    (Subgroup.mem_centralizer_iff.1 hx.2 _ (Subgroup.mem_subgroupOf.1 hl))
  have e : (m : G) = l * ((l⁻¹ * m : ↥M) : G) := by simp
  rw [e, mul_assoc, h1, ← mul_assoc, h2, mul_assoc]

end Even

section Two

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem map_L_eq_commutator (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a) :
    (L.subgroupOf M).map a = commutator (MSP.Sp4 F) := by
  have hF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hd.2.1, pow_one]
  obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hF
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  set A := (L.subgroupOf M).map a with hAdef
  have hAn : A.Normal := hLn.map a hd.2.2.1
  have hperf : ⁅L.subgroupOf M, L.subgroupOf M⁆ = L.subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h.L_le, h.perfect]
  have hAle : A ≤ commutator (MSP.Sp4 F) := by
    rw [hAdef, ← hperf, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hA : A ≠ ⊥ := by
    intro hbot
    apply S5B.not_le_kerG h hd
    intro l hl
    refine ⟨⟨l, h.L_le hl⟩, ?_, rfl⟩
    show _ ∈ a.ker
    have : a ⟨l, h.L_le hl⟩ ∈ A := ⟨⟨l, h.L_le hl⟩, hl, rfl⟩
    rw [hbot] at this
    exact this
  set θ := B5FinSp.theta c
  set N := A.comap θ.toMonoidHom with hNdef
  have hNn : N.Normal := hAn.comap _
  have hNle : N ≤ alternatingGroup (Fin 6) := by
    intro σ hσ
    have h1 : θ σ ∈ commutator (MSP.Sp4 F) := hAle hσ
    rw [MSP.mem_commutator_iff_sign c, MulEquiv.symm_apply_apply] at h1
    exact Equiv.Perm.mem_alternatingGroup.2 h1
  have hsimp : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hN' : (N.subgroupOf (alternatingGroup (Fin 6))).Normal := Subgroup.Normal.subgroupOf hNn _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 6))) with
    hbot | htop
  · exfalso
    apply hA
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨σ, rfl⟩ := θ.surjective g
    have hσN : σ ∈ N := hg
    have hσA : σ ∈ alternatingGroup (Fin 6) := hNle hσN
    have h1 : (⟨σ, hσA⟩ : alternatingGroup (Fin 6)) ∈ N.subgroupOf (alternatingGroup (Fin 6)) :=
      hσN
    rw [hbot] at h1
    have h2 : σ = 1 := congrArg Subtype.val ((Subgroup.mem_bot).1 h1)
    rw [h2, map_one]
    exact one_mem _
  · refine le_antisymm hAle fun g hg => ?_
    obtain ⟨σ, rfl⟩ := θ.surjective g
    rw [MSP.mem_commutator_iff_sign c, MulEquiv.symm_apply_apply] at hg
    have hσA : σ ∈ alternatingGroup (Fin 6) := Equiv.Perm.mem_alternatingGroup.2 hg
    have h1 : (⟨σ, hσA⟩ : alternatingGroup (Fin 6)) ∈ N.subgroupOf (alternatingGroup (Fin 6)) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact h1

theorem commute_of_mem_commutator (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a) {m : ↥M}
    (hm : a m ∈ commutator (MSP.Sp4 F)) {x : G} (hx : x ∈ Zq M L) : (m : G) * x = x * m :=
  commute_of_map_mem h hd (by rw [map_L_eq_commutator h hd]; exact hm) hx

omit [Finite G] in
theorem mul_mem_commutator_of_not_mem (hd : S5.IsSp4Data M T L 1 F a) {g₁ g₂ : MSP.Sp4 F}
    (h₁ : g₁ ∉ commutator (MSP.Sp4 F)) (h₂ : g₂ ∉ commutator (MSP.Sp4 F)) :
    g₁ * g₂ ∈ commutator (MSP.Sp4 F) := by
  have hF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hd.2.1, pow_one]
  obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hF
  rw [Subgroup.mul_mem_iff_of_index_two (MSP.index_commutator c)]
  exact iff_of_false h₁ h₂

theorem conj_eq_of_not_mem (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a) {m₁ m₂ : ↥M}
    (h₁ : a m₁ ∉ commutator (MSP.Sp4 F)) (h₂ : a m₂ ∉ commutator (MSP.Sp4 F)) {x : G}
    (hx : x ∈ Zq M L) : (m₁ : G) * x * (m₁ : G)⁻¹ = (m₂ : G) * x * (m₂ : G)⁻¹ := by
  have h12 : a (m₁⁻¹ * m₂) ∈ commutator (MSP.Sp4 F) := by
    rw [map_mul, map_inv]
    exact mul_mem_commutator_of_not_mem hd (fun h' => h₁ (by simpa using h')) h₂
  have hc := commute_of_mem_commutator h hd h12 hx
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc
  have hc' : ((m₁ : G)⁻¹ * m₂) * x * ((m₁ : G)⁻¹ * m₂)⁻¹ = x := by
    rw [hc, mul_inv_cancel_right]
  calc (m₁ : G) * x * (m₁ : G)⁻¹
      = m₁ * (((m₁ : G)⁻¹ * m₂) * x * ((m₁ : G)⁻¹ * m₂)⁻¹) * (m₁ : G)⁻¹ := by rw [hc']
    _ = (m₂ : G) * x * (m₂ : G)⁻¹ := by group

theorem inf_centralizer_eq_of_not_mem (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {J : Subgroup G} (hJM : J ≤ M) {j : G} (hj : j ∈ J)
    (hjo : a ⟨j, hJM hj⟩ ∉ commutator (MSP.Sp4 F)) :
    Zq M L ⊓ Subgroup.centralizer (J : Set G) = Zq M L ⊓ Subgroup.centralizer (M : Set G) := by
  apply le_antisymm
  · rintro x ⟨hx, hxJ⟩
    refine ⟨hx, Subgroup.mem_centralizer_iff.2 fun m hm => ?_⟩
    by_cases hmc : a ⟨m, hm⟩ ∈ commutator (MSP.Sp4 F)
    · exact commute_of_mem_commutator h hd hmc hx
    · have hjx : j * x = x * j := Subgroup.mem_centralizer_iff.1 hxJ j hj
      have e := conj_eq_of_not_mem h hd hmc hjo hx
      have hjx' : j * x * j⁻¹ = x := by rw [hjx, mul_inv_cancel_right]
      simp only at e
      rw [hjx'] at e
      calc m * x = m * x * m⁻¹ * m := by group
        _ = x * m := by rw [e]
  · exact inf_le_inf_left _ (Subgroup.centralizer_le hJM)

theorem le_centralizer_of_mem_commutator (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {J : Subgroup G} (hJM : J ≤ M) (hJ : ∀ j (hj : j ∈ J), a ⟨j, hJM hj⟩ ∈ commutator (MSP.Sp4 F)) :
    Zq M L ≤ Subgroup.centralizer (J : Set G) := fun _ hx =>
  Subgroup.mem_centralizer_iff.2 fun j hj => commute_of_mem_commutator h hd (hJ j hj) hx

end Two

end S5Q2

end CFSG.Quasithin.MS93
