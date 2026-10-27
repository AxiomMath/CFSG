module

public import CFSG.Quasithin.H13.A5Sit15b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth

namespace A5.Orth

theorem eq_top_of_idc_mem {Y : Subgroup (Multiplicative V4)}
    (h : ∀ i, Multiplicative.ofAdd (idc i) ∈ Y) : Y = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have hs : ∀ (a : ZMod 2) (i : Fin 4), Multiplicative.ofAdd (a • idc i) ∈ Y := by
    intro a i
    rcases (by decide : ∀ r : ZMod 2, r = 0 ∨ r = 1) a with rfl | rfl
    · rw [zero_smul, ofAdd_zero]
      exact Y.one_mem
    · rw [one_smul]
      exact h i
  have hw : w = Multiplicative.ofAdd (Multiplicative.toAdd w 0 • idc 0) *
      Multiplicative.ofAdd (Multiplicative.toAdd w 1 • idc 1) *
      Multiplicative.ofAdd (Multiplicative.toAdd w 2 • idc 2) *
      Multiplicative.ofAdd (Multiplicative.toAdd w 3 • idc 3) := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd]
    exact eq_sum_idc _
  rw [hw]
  exact Y.mul_mem (Y.mul_mem (Y.mul_mem (hs _ _) (hs _ _)) (hs _ _)) (hs _ _)

end A5.Orth

namespace A5SitPf15

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  {S : A5Sit G T V V₁ V₃ L₁ H} {SY : A5SitY S L₁} (P : A5SitPf15 S SY)
include P

@[expose] noncomputable def gen (i : Fin 4) : ↥(conjClosure V₃ H) :=
  Function.surjInv P.C.θ_surj (Multiplicative.ofAdd (idc i))

theorem θ_gen (i : Fin 4) : P.C.θ (P.gen i) = Multiplicative.ofAdd (idc i) :=
  Function.surjInv_eq P.C.θ_surj _

theorem comm_of_comm_gen {x : G} (hz : P.C.z * x = x * P.C.z)
    (hg : ∀ i, ((P.gen i : ↥(conjClosure V₃ H)) : G) * x = x * (P.gen i : G)) :
    ∀ u ∈ conjClosure V₃ H, u * x = x * u := by
  set X : Subgroup ↥(conjClosure V₃ H) :=
    (Subgroup.centralizer ({x} : Set G)).subgroupOf (conjClosure V₃ H) with hXdef
  have hmemX : ∀ u : ↥(conjClosure V₃ H), u ∈ X ↔ (u : G) * x = x * u := fun u => by
    rw [hXdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  have htop : X.map P.C.θ = ⊤ :=
    eq_top_of_idc_mem fun i => ⟨P.gen i, (hmemX _).2 (hg i), P.θ_gen i⟩
  intro u hu
  have hmem : P.C.θ ⟨u, hu⟩ ∈ X.map P.C.θ := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨u', hu'X, hθ⟩ := hmem
  have hk : P.C.θ (⟨u, hu⟩ * u'⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hθ]
    exact mul_inv_cancel _
  have hkx : ((⟨u, hu⟩ * u'⁻¹ : ↥(conjClosure V₃ H)) : G) * x =
      x * ((⟨u, hu⟩ * u'⁻¹ : ↥(conjClosure V₃ H)) : G) := by
    rcases (P.C.ker_iff _).1 hk with h | h <;> rw [h]
    · simp
    · exact hz
  have hu' := (hmemX u').1 hu'X
  have e : u = ((⟨u, hu⟩ * u'⁻¹ : ↥(conjClosure V₃ H)) : G) * u' := by simp
  rw [e, mul_assoc, hu', ← mul_assoc, hkx, mul_assoc]

theorem comm_gen_mem {q : G} (hq : q ∈ pCoreOf 2 H) (i : Fin 4) :
    q * (P.gen i : G) * q⁻¹ * (P.gen i : G)⁻¹ ∈ V₁ :=
  (S.mem_Q_iff (pCoreOf_le 2 H hq)).1 hq _ (P.gen i).2

@[expose] noncomputable def eps : ↥(pCoreOf 2 H) →* (Fin 4 → ↥V₁) where
  toFun q i := ⟨(q : G) * (P.gen i : G) * (q : G)⁻¹ * (P.gen i : G)⁻¹, P.comm_gen_mem q.2 i⟩
  map_one' := by
    funext i
    apply Subtype.ext
    simp
  map_mul' q q' := by
    funext i
    apply Subtype.ext
    show (q * q' : G) * (P.gen i : G) * (q * q' : G)⁻¹ * (P.gen i : G)⁻¹ =
      ((q : G) * (P.gen i : G) * (q : G)⁻¹ * (P.gen i : G)⁻¹) *
        ((q' : G) * (P.gen i : G) * (q' : G)⁻¹ * (P.gen i : G)⁻¹)
    set a := (q' : G) * (P.gen i : G) * (q' : G)⁻¹ * (P.gen i : G)⁻¹ with ha
    set b := (q : G) * (P.gen i : G) * (q : G)⁻¹ * (P.gen i : G)⁻¹ with hb
    have haV : a ∈ V₁ := P.comm_gen_mem q'.2 i
    have hbH : b ∈ H := S.V_le_H (S.V1_le_V (P.comm_gen_mem q.2 i))
    have hqa : (q : G) * a = a * q :=
      (Subgroup.mem_centralizer_iff.mp (S.hF.H_le_centralizer (pCoreOf_le 2 H q.2)) a haV).symm
    have hba : b * a = a * b :=
      (Subgroup.mem_centralizer_iff.mp (S.hF.H_le_centralizer hbH) a haV).symm
    have e1 : (q * q' : G) * (P.gen i : G) * (q * q' : G)⁻¹ * (P.gen i : G)⁻¹ =
        (q : G) * a * (P.gen i : G) * (q : G)⁻¹ * (P.gen i : G)⁻¹ := by
      rw [ha]
      group
    rw [e1, hqa, hba]
    rw [hb]
    group

@[expose] noncomputable def Z1 (_ : A5SitPf15 S SY) : Subgroup G :=
  pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure V₃ H : Set G)

theorem ker_eps_le : P.eps.ker ≤ P.Z1.subgroupOf (pCoreOf 2 H) := by
  intro q hq
  rw [Subgroup.mem_subgroupOf]
  refine ⟨q.2, Subgroup.mem_centralizer_iff.2 ?_⟩
  have hgi : ∀ i, ((P.gen i : ↥(conjClosure V₃ H)) : G) * q = q * (P.gen i : G) := by
    intro i
    have h1 := congrArg Subtype.val (congrFun ((MonoidHom.mem_ker).1 hq) i)
    have h2 : (q : G) * (P.gen i : G) * (q : G)⁻¹ * (P.gen i : G)⁻¹ = 1 := h1
    have h3 : (q : G) * (P.gen i : G) = (P.gen i : G) * q := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
      exact h2
    exact h3.symm
  have hz : P.C.z * q = q * P.C.z := (P.comm_z (pCoreOf_le 2 H q.2)).symm
  exact P.comm_of_comm_gen hz hgi

theorem index_Z1_le : P.Z1.relIndex (pCoreOf 2 H) ≤ 16 := by
  have h1 : P.Z1.relIndex (pCoreOf 2 H) ∣ P.eps.ker.index :=
    Subgroup.index_dvd_of_le P.ker_eps_le
  have h2 : P.eps.ker.index ≤ 16 := by
    rw [Subgroup.index_ker]
    calc Nat.card P.eps.range ≤ Nat.card (Fin 4 → ↥V₁) := Subgroup.card_le_card_group _
      _ = 16 := by rw [Nat.card_fun, S.card_V1, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) h1).trans h2

theorem U_inf_Z1 : conjClosure V₃ H ⊓ P.Z1 = V₁ := by
  apply le_antisymm
  · rintro x ⟨hx, -, hxc⟩
    exact P.mem_V1_of_central hx fun u hu => (Subgroup.mem_centralizer_iff.mp hxc u hu).symm
  · intro x hx
    have hxU : x ∈ conjClosure V₃ H := le_conjClosure _ _ (S.V1_le_V3 hx)
    refine ⟨hxU, S.U_le_Q hxU, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp
      (S.hF.H_le_centralizer (S.U_le_Q.trans (pCoreOf_le 2 H) hu)) x hx).symm

theorem Z1_le_Q : P.Z1 ≤ pCoreOf 2 H := inf_le_left

variable (hQ : Nat.card (pCoreOf 2 H) = 64)
include hQ

theorem card_Z1 : Nat.card P.Z1 = 4 := by
  have hU : Nat.card (conjClosure V₃ H) = 32 := P.card_U
  have hUQ : (conjClosure V₃ H).relIndex (pCoreOf 2 H) = 2 := by
    have h := Subgroup.relIndex_mul_card (conjClosure V₃ H) (pCoreOf 2 H)
    rw [inf_eq_left.2 S.U_le_Q, hU, hQ] at h
    omega
  have hVQ : V₁.relIndex (pCoreOf 2 H) = 32 := by
    have h := Subgroup.relIndex_mul_card V₁ (pCoreOf 2 H)
    rw [inf_eq_left.2 (S.V1_le_V3.trans ((le_conjClosure V₃ H).trans S.U_le_Q)), S.card_V1,
      hQ] at h
    omega
  have hle := Subgroup.relIndex_inf_le (H := conjClosure V₃ H) (K := P.Z1) (L := pCoreOf 2 H)
  rw [P.U_inf_Z1, hVQ, hUQ] at hle
  have hZ := P.index_Z1_le
  have h16 : P.Z1.relIndex (pCoreOf 2 H) = 16 := by omega
  have h := Subgroup.relIndex_mul_card P.Z1 (pCoreOf 2 H)
  rw [inf_eq_left.2 P.Z1_le_Q, h16, hQ] at h
  omega

theorem U_sup_Z1 : conjClosure V₃ H ⊔ P.Z1 = pCoreOf 2 H := by
  have hU : Nat.card (conjClosure V₃ H) = 32 := P.card_U
  have hle : conjClosure V₃ H ⊔ P.Z1 ≤ pCoreOf 2 H := sup_le S.U_le_Q P.Z1_le_Q
  have hUQ : (conjClosure V₃ H).relIndex (pCoreOf 2 H) = 2 := by
    have h := Subgroup.relIndex_mul_card (conjClosure V₃ H) (pCoreOf 2 H)
    rw [inf_eq_left.2 S.U_le_Q, hU, hQ] at h
    omega
  have h := Subgroup.relIndex_mul_relIndex (conjClosure V₃ H) (conjClosure V₃ H ⊔ P.Z1)
    (pCoreOf 2 H) le_sup_left hle
  rw [hUQ] at h
  refine le_antisymm hle (Subgroup.relIndex_eq_one.1 ?_)
  rcases (Nat.dvd_prime Nat.prime_two).1 (Dvd.intro_left _ h) with h1 | h1
  · exact h1
  · exfalso
    rw [h1] at h
    have h2 : (conjClosure V₃ H).relIndex (conjClosure V₃ H ⊔ P.Z1) = 1 := by omega
    have hZU : P.Z1 ≤ conjClosure V₃ H := le_sup_right.trans (Subgroup.relIndex_eq_one.1 h2)
    have hZV : P.Z1 = V₁ :=
      calc P.Z1 = conjClosure V₃ H ⊓ P.Z1 := (inf_eq_right.2 hZU).symm
        _ = V₁ := P.U_inf_Z1
    have := P.card_Z1 hQ
    rw [hZV, S.card_V1] at this
    omega

theorem decomp {q : G} (hq : q ∈ pCoreOf 2 H) :
    ∃ u ∈ conjClosure V₃ H, ∃ j ∈ P.Z1, q = u * j := by
  have hN : P.Z1 ≤ Subgroup.normalizer (conjClosure V₃ H : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (conjClosure V₃ H) P.Z1 hN
  have hq' : q ∈ ((conjClosure V₃ H ⊔ P.Z1 : Subgroup G) : Set G) := by
    rw [P.U_sup_Z1 hQ]
    exact hq
  rw [hmul] at hq'
  obtain ⟨u, hu, j, hj, rfl⟩ := hq'
  exact ⟨u, hu, j, hj, rfl⟩

theorem Z1_comm {j j' : G} (hj : j ∈ P.Z1) (hj' : j' ∈ P.Z1) : j * j' = j' * j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : Nat.card P.Z1 = 2 ^ 2 := by rw [P.card_Z1 hQ]; norm_num
  have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq h4).is_comm.comm ⟨j, hj⟩ ⟨j', hj'⟩
  exact congrArg Subtype.val this

theorem Z1_comm_Q {j q : G} (hj : j ∈ P.Z1) (hq : q ∈ pCoreOf 2 H) : j * q = q * j := by
  obtain ⟨u, hu, j', hj', rfl⟩ := P.decomp hQ hq
  have hju : u * j = j * u := Subgroup.mem_centralizer_iff.mp hj.2 u hu
  calc j * (u * j') = (j * u) * j' := by group
    _ = (u * j) * j' := by rw [hju]
    _ = u * (j * j') := by group
    _ = u * (j' * j) := by rw [P.Z1_comm hQ hj hj']
    _ = u * j' * j := by group

theorem Z1_eq_center : P.Z1 = pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
  apply le_antisymm
  · intro j hj
    exact ⟨hj.1, Subgroup.mem_centralizer_iff.2 fun q hq => (P.Z1_comm_Q hQ hj hq).symm⟩
  · rintro x ⟨hx, hxc⟩
    exact ⟨hx, Subgroup.mem_centralizer_iff.2 fun u hu =>
      Subgroup.mem_centralizer_iff.mp hxc u (S.U_le_Q hu)⟩

@[expose] noncomputable def thetaQf (q : ↥(pCoreOf 2 H)) : Multiplicative V4 :=
  P.C.θ ⟨Classical.choose (P.decomp hQ q.2), (Classical.choose_spec (P.decomp hQ q.2)).1⟩

theorem thetaQf_eq {q u j : G} (hq : q ∈ pCoreOf 2 H) (hu : u ∈ conjClosure V₃ H)
    (hj : j ∈ P.Z1) (h : q = u * j) : P.thetaQf hQ ⟨q, hq⟩ = P.C.θ ⟨u, hu⟩ := by
  obtain ⟨hu', j', hj', h'⟩ := Classical.choose_spec (P.decomp hQ hq)
  set u' := Classical.choose (P.decomp hQ hq)
  show P.C.θ ⟨u', hu'⟩ = P.C.θ ⟨u, hu⟩
  have hm : u'⁻¹ * u ∈ V₁ := by
    rw [← P.U_inf_Z1]
    refine ⟨(conjClosure V₃ H).mul_mem ((conjClosure V₃ H).inv_mem hu') hu, ?_⟩
    have e : u'⁻¹ * u = j' * j⁻¹ := by
      rw [h] at h'
      calc u'⁻¹ * u = u'⁻¹ * (u * j) * j⁻¹ := by group
        _ = u'⁻¹ * (u' * j') * j⁻¹ := by rw [h']
        _ = j' * j⁻¹ := by group
    rw [e]
    exact P.Z1.mul_mem hj' (P.Z1.inv_mem hj)
  have hk : P.C.θ ((⟨u', hu'⟩ : ↥(conjClosure V₃ H))⁻¹ * ⟨u, hu⟩) = 1 :=
    (P.C.ker_iff _).2 ((P.Cz _).1 hm)
  rw [map_mul, map_inv] at hk
  exact inv_mul_eq_one.1 hk

@[expose] noncomputable def thetaQ : ↥(pCoreOf 2 H) →* Multiplicative V4 where
  toFun := P.thetaQf hQ
  map_one' := by
    rw [show (1 : ↥(pCoreOf 2 H)) = ⟨1, (pCoreOf 2 H).one_mem⟩ from rfl,
      P.thetaQf_eq hQ _ (conjClosure V₃ H).one_mem P.Z1.one_mem (mul_one 1).symm]
    exact map_one _
  map_mul' q q' := by
    obtain ⟨u, hu, j, hj, hq⟩ := P.decomp hQ q.2
    obtain ⟨u', hu', j', hj', hq'⟩ := P.decomp hQ q'.2
    have e : ((q * q' : ↥(pCoreOf 2 H)) : G) = (u * u') * (j * j') := by
      rw [Subgroup.coe_mul, hq, hq']
      have hju : j * u' = u' * j := (Subgroup.mem_centralizer_iff.mp hj.2 u' hu').symm
      calc u * j * (u' * j') = u * (j * u') * j' := by group
        _ = u * (u' * j) * j' := by rw [hju]
        _ = u * u' * (j * j') := by group
    have h1 : P.thetaQf hQ (q * q') = P.C.θ ⟨u * u', (conjClosure V₃ H).mul_mem hu hu'⟩ :=
      P.thetaQf_eq hQ (q * q').2 _ (P.Z1.mul_mem hj hj') e
    have h2 : P.thetaQf hQ q = P.C.θ ⟨u, hu⟩ := P.thetaQf_eq hQ q.2 hu hj hq
    have h3 : P.thetaQf hQ q' = P.C.θ ⟨u', hu'⟩ := P.thetaQf_eq hQ q'.2 hu' hj' hq'
    rw [h1, h2, h3, ← map_mul]
    rfl

theorem thetaQ_U (u : ↥(conjClosure V₃ H)) :
    P.thetaQ hQ ⟨u, S.U_le_Q u.2⟩ = P.C.θ u :=
  P.thetaQf_eq hQ _ u.2 P.Z1.one_mem (mul_one _).symm

theorem thetaQ_eq {q u j : G} (hq : q ∈ pCoreOf 2 H) (hu : u ∈ conjClosure V₃ H)
    (hj : j ∈ P.Z1) (h : q = u * j) : P.thetaQ hQ ⟨q, hq⟩ = P.C.θ ⟨u, hu⟩ :=
  P.thetaQf_eq hQ hq hu hj h

theorem thetaQ_surj : Function.Surjective (P.thetaQ hQ) := by
  intro w
  obtain ⟨u, rfl⟩ := P.C.θ_surj w
  exact ⟨_, P.thetaQ_U hQ u⟩

theorem thetaQ_eq_one_iff (q : ↥(pCoreOf 2 H)) : P.thetaQ hQ q = 1 ↔ (q : G) ∈ P.Z1 := by
  obtain ⟨u, hu, j, hj, hq⟩ := P.decomp hQ q.2
  have h1 : P.thetaQ hQ q = P.C.θ ⟨u, hu⟩ := P.thetaQ_eq hQ q.2 hu hj hq
  rw [h1, P.C.ker_iff]
  constructor
  · intro h
    have huV : u ∈ V₁ := (P.Cz u).2 h
    rw [← P.U_inf_Z1] at huV
    rw [hq]
    exact P.Z1.mul_mem huV.2 hj
  · intro h
    have huZ : u ∈ P.Z1 := by
      have e : u = q * j⁻¹ := by rw [hq]; group
      rw [e]
      exact P.Z1.mul_mem h (P.Z1.inv_mem hj)
    have : u ∈ V₁ := by
      rw [← P.U_inf_Z1]
      exact ⟨hu, huZ⟩
    exact (P.Cz u).1 this

end A5SitPf15

end CFSG.Quasithin.H13
