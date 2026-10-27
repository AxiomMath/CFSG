module

public import CFSG.Milestones.ASVolI.A3
public import CFSG.Quasithin.Background.A3Structure315
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OBorelMain
public import CFSG.Quasithin.Vol2.F134LieU3
public import CFSG.Quasithin.Background.A3Structure315Facts
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveDefs

public section

namespace CFSG.ASVolI

open CFSG.Open

theorem burnsideA315x_normal {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) : L.Normal := by
  haveI := h.sqtk.finite
  have hn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  rwa [h.fitting] at hn

theorem burnsideA315x_centralizer_eq_bot {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) : Subgroup.centralizer (L : Set G) = ⊥ := by
  haveI := h.sqtk.finite
  have hle := CFSG.centralizer_generalizedFitting_le G
  rw [h.fitting] at hle
  haveI := h.simple
  obtain ⟨a, b, hab⟩ := h.nonabelian
  rw [eq_bot_iff]
  intro x hx
  have hxL : x ∈ L := hle hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with hc | hc
  · have hmem : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := Subgroup.mem_centralizer_iff.1 hx (g : G) g.2
      exact Subtype.ext this
    rw [hc, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hmem)
  · exfalso
    have hb : b ∈ Subgroup.center ↥L := hc ▸ Subgroup.mem_top b
    exact hab ((Subgroup.mem_center_iff.1 hb a))


theorem burnsideA315x_odd_mem {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B)
    (hOut : ∀ α : MulAut ↥L, Odd (orderOf α) → ∃ l : ↥L, α = MulAut.conj l)
    {g : G} (hg : Odd (orderOf g)) : g ∈ L := by
  haveI := burnsideA315x_normal h
  have hodd : Odd (orderOf (MulAut.conjNormal (H := L) g)) :=
    Odd.of_dvd_nat hg (orderOf_map_dvd _ g)
  obtain ⟨l, hl⟩ := hOut _ hodd
  have hc : (l : G)⁻¹ * g ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨x, hx⟩ : ↥L) : G)) hl
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at h1
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h1
    calc x * ((l : G)⁻¹ * g) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * g := by group
      _ = (l : G)⁻¹ * (g * x * g⁻¹) * g := by rw [← h1]
      _ = (l : G)⁻¹ * g * x := by group
  rw [burnsideA315x_centralizer_eq_bot h, Subgroup.mem_bot] at hc
  have : g = (l : G) := by
    have := congrArg (fun y => (l : G) * y) hc
    simpa using this
  rw [this]
  exact l.2

theorem burnsideA315x_le_of_out {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B)
    (hOut : ∀ α : MulAut ↥L, Odd (orderOf α) → ∃ l : ↥L, α = MulAut.conj l) : B ≤ L := by
  intro b hb
  refine burnsideA315x_odd_mem h hOut ?_
  have h1 : orderOf (⟨b, hb⟩ : ↥B) ∣ Nat.card ↥B := orderOf_dvd_natCard _
  have h2 : orderOf (⟨b, hb⟩ : ↥B) = orderOf b := Subgroup.orderOf_mk b hb
  rw [h2] at h1
  exact Odd.of_dvd_nat h.odd h1


open scoped Pointwise in
theorem burnsideA315x_relIndex_sup {G : Type} [Group G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)) ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)).injective, ?_⟩
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hy' : y ∈ (A : Set G) * (B : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left A B hB) ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa using hb

theorem burnsideA315x_sylow_inf {G : Type} [Group G] {L T : Subgroup G} [L.Normal]
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L := by
  refine ⟨inf_le_right, hT.2.1.to_le inf_le_left, ?_⟩
  have h1 : T.relIndex (L ⊔ T) = T.relIndex L :=
    burnsideA315x_relIndex_sup (A := L) (B := T)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have h2 : T.relIndex (L ⊔ T) ∣ T.relIndex ⊤ :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex T (L ⊔ T) ⊤ le_sup_right le_top)
  have h3 : (T ⊓ L).relIndex L = T.relIndex L := Subgroup.inf_relIndex_right T L
  intro h2L
  apply hT.2.2
  change 2 ∣ T.relIndex ⊤
  change 2 ∣ (T ⊓ L).relIndex L at h2L
  rw [h3, ← h1] at h2L
  exact h2L.trans h2


open scoped Pointwise in
theorem burnsideA315x_coe_sup {G : Type*} [Group G] {H K : Subgroup G}
    (h : (H : Set G) * K = K * H) : ((H ⊔ K : Subgroup G) : Set G) = H * K := by
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

open scoped Pointwise in
theorem burnsideA315x_card_sup {G : Type*} [Group G] {H K : Subgroup G}
    (h : (H : Set G) * K = K * H) (hHK : H ⊓ K = ⊥) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  rw [← Nat.card_prod]
  have hc := congrArg (fun s : Set G => Nat.card s) (burnsideA315x_coe_sup h)
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

open scoped Pointwise in
theorem burnsideA315x_map_permute {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {H K : Subgroup G} (h : (H : Set G) * K = K * H) :
    ((H.map f : Subgroup G') : Set G') * (K.map f : Subgroup G') =
      (K.map f : Subgroup G') * (H.map f : Subgroup G') := by
  rw [Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, h, Set.image_mul]

open scoped Pointwise in
theorem burnsideA315x_subgroupOf_permute {G : Type*} [Group G] {H K N : Subgroup G}
    (hHN : H ≤ N) (h : (H : Set G) * K = K * H) :
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
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha hb
    have hab : (a : G) * b ∈ (H : Set G) * K := by
      rw [h]
      exact Set.mul_mem_mul (Subgroup.mem_inf.1 ha).1 hb
    obtain ⟨x, hx, k, hk, hxk⟩ := hab
    have hkN : k ∈ N := by
      have e : k = x⁻¹ * (a * b) := by rw [← hxk]; group
      rw [e]
      exact N.mul_mem (N.inv_mem (hHN hx)) (N.mul_mem a.2 b.2)
    refine ⟨⟨x, hHN hx⟩, ?_, ⟨k, hkN⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact hx
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact ⟨hk, hkN⟩
    · apply Subtype.ext
      simpa using hxk


open scoped Pointwise in
structure burnsideA315x_Config (X : Type) [Group X] (S B : Subgroup X) : Prop where
  sylow : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤
  odd : Odd (Nat.card ↥B)
  not3 : ¬ IsPGroup 3 ↥B
  cases : IsMulCommutative ↥B ∨ ∃ r : ℕ, r.Prime ∧ IsPGroup r ↥B
  perm : (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X)

open scoped Pointwise in
theorem burnsideA315x_config_of_le {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) (hBL : B ≤ L) :
    burnsideA315x_Config ↥L ((T ⊓ L).subgroupOf L) (B.subgroupOf L) := by
  haveI := burnsideA315x_normal h
  have hsyl := burnsideA315x_sylow_inf (L := L) h.sylow
  have eB : ↥(B.subgroupOf L) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBL
  refine ⟨⟨le_top, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  · have h1 : (((T ⊓ L).subgroupOf L).subgroupOf (⊤ : Subgroup ↥L)).index =
        ((T ⊓ L).subgroupOf L).index := by
      change ((T ⊓ L).subgroupOf L).relIndex ⊤ = _
      exact Subgroup.relIndex_top_right _
    rw [h1]
    exact hsyl.2.2
  · rw [Nat.card_congr eB.toEquiv]
    exact h.odd
  · intro hp
    exact h.residual (CFSG.Quasithin.A315.pResidualOf_eq_bot_of_isPGroup (hp.of_equiv eB))
  · rcases h.cases with hab | ⟨r, hr, hBr, -⟩
    · left
      refine ⟨⟨fun a b => ?_⟩⟩
      apply eB.injective
      rw [map_mul, map_mul]
      exact hab.is_comm.comm _ _
    · right
      exact ⟨r, hr, hBr.of_equiv eB.symm⟩
  · exact burnsideA315x_subgroupOf_permute (K := T) hBL h.perm

open scoped Pointwise in
theorem burnsideA315x_config_of_hyp {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B)
    (hOut : ∀ α : MulAut ↥L, Odd (orderOf α) → ∃ l : ↥L, α = MulAut.conj l) :
    B ≤ L ∧ burnsideA315x_Config ↥L ((T ⊓ L).subgroupOf L) (B.subgroupOf L) := by
  haveI := burnsideA315x_normal h
  have hBL : B ≤ L := burnsideA315x_le_of_out h hOut
  exact ⟨hBL, burnsideA315x_config_of_le h hBL⟩

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L.PermLat Equiv in
theorem burnsideA315x_alt_cert_sizes {n : ℕ} (c : LatCert (Perm (Fin n)))
    (hc : c.check RN.enc = true)
    (hM : Subgroup.closure {g | g ∈ c.mGens} = alternatingGroup (Fin n))
    (hDA : Subgroup.closure {g | g ∈ c.tGens} ≤ alternatingGroup (Fin n))
    (hDs : IsSylowTwoOf ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
      (alternatingGroup (Fin n))) ⊤)
    {S H : Subgroup ↥(alternatingGroup (Fin n))} (hS : IsSylowTwoOf S ⊤) (hSH : S ≤ H) :
    Nat.card H ∈ c.sizes := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hS
  obtain ⟨h3, h4⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hDs
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin n)) (h1.toSylow h2)
    (h3.toSylow h4)
  have hDH : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf (alternatingGroup (Fin n)) ≤
      H.map (MulAut.conj g).toMonoidHom := by
    intro x hx
    have hx' : x ∈ ((g • h1.toSylow h2 : Sylow 2 (alternatingGroup (Fin n))) :
        Subgroup (alternatingGroup (Fin n))) := by
      rw [hg]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    exact ⟨y, hSH hy, rfl⟩
  have hHc : Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hTY : Subgroup.closure {g | g ∈ c.tGens} ≤
      (H.map (MulAut.conj g).toMonoidHom).map (alternatingGroup (Fin n)).subtype := by
    intro t ht
    exact ⟨⟨t, hDA ht⟩, hDH (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hYM : (H.map (MulAut.conj g).toMonoidHom).map (alternatingGroup (Fin n)).subtype ≤
      Subgroup.closure {g | g ∈ c.mGens} := by
    rw [hM]
    exact Subgroup.map_subtype_le _
  obtain ⟨L, hL, hYL⟩ := c.overgroups (rawIsEnc n) hc _ hTY hYM
  have hmem := c.card_member (rawIsEnc n) (c.closedOK_of_check hc) (c.sizesOK_of_check hc) L hL
  rw [← hYL, Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective,
    hHc] at hmem
  exact hmem


open CFSG.QuasithinUnique in
theorem burnsideA315x_alt5_orders
    {S H : Subgroup ↥(alternatingGroup (Fin 5))} (hS : IsSylowTwoOf S ⊤) (hSH : S ≤ H) :
    Nat.card H = 4 ∨ Nat.card H = 12 ∨ Nat.card H = 60 := by
  have h := burnsideA315x_alt_cert_sizes CFSG.QuasithinUnique.Bridge.Over.CertA5.cert
    CFSG.QuasithinUnique.Bridge.Over.CertA5.cert_check
    CFSG.QuasithinUnique.Bridge.Over.CertA5.closure_mGens
    CFSG.QuasithinUnique.Bridge.Over.CertA5.D_le
    CFSG.QuasithinUnique.Bridge.Over.CertA5.isSylow_D hS hSH
  have h2 : CFSG.QuasithinUnique.Bridge.Over.CertA5.cert.sizes = [4, 12, 60] := by decide
  rw [h2] at h
  simpa using h

open CFSG.QuasithinUnique in
theorem burnsideA315x_alt6_orders
    {S H : Subgroup ↥(alternatingGroup (Fin 6))} (hS : IsSylowTwoOf S ⊤) (hSH : S ≤ H) :
    Nat.card H = 8 ∨ Nat.card H = 24 ∨ Nat.card H = 360 := by
  have h := burnsideA315x_alt_cert_sizes CFSG.QuasithinUnique.L246C127.Even6.cert
    CFSG.QuasithinUnique.L246C127.Even6.cert_check
    CFSG.QuasithinUnique.L246C127.Even6.closure_mGens
    CFSG.QuasithinUnique.L246C127.Even6.D_le
    CFSG.QuasithinUnique.L246C127.Even6.isSylow_D hS hSH
  have h2 : CFSG.QuasithinUnique.L246C127.Even6.cert.sizes = [8, 24, 24, 360] := by decide
  rw [h2] at h
  simpa using h

open CFSG.QuasithinUnique in
theorem burnsideA315x_alt8_orders
    {S H : Subgroup ↥(alternatingGroup (Fin 8))} (hS : IsSylowTwoOf S ⊤) (hSH : S ≤ H) :
    Nat.card H = 64 ∨ Nat.card H = 192 ∨ Nat.card H = 576 ∨ Nat.card H = 1344 ∨
      Nat.card H = 20160 := by
  have h := burnsideA315x_alt_cert_sizes CFSG.QuasithinUnique.L246C127.Even8.cert
    CFSG.QuasithinUnique.L246C127.Even8.cert_check
    CFSG.QuasithinUnique.L246C127.Even8.closure_mGens
    CFSG.QuasithinUnique.L246C127.Even8.D_le
    CFSG.QuasithinUnique.L246C127.Even8.isSylow_D hS hSH
  have h2 : CFSG.QuasithinUnique.L246C127.Even8.cert.sizes =
      [64, 192, 192, 192, 576, 1344, 1344, 20160] := by decide
  rw [h2] at h
  simpa using h

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L in
theorem burnsideA315x_alt7_orders
    {S H : Subgroup ↥(alternatingGroup (Fin 7))} (hS : IsSylowTwoOf S ⊤) (hSH : S ≤ H) :
    Nat.card H = 8 ∨ Nat.card H = 24 ∨ Nat.card H = 72 ∨ Nat.card H = 120 ∨
      Nat.card H = 168 ∨ Nat.card H = 360 ∨ Nat.card H = 2520 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hS
  obtain ⟨h3, h4⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index Seven.isSylowTwoOf_T7
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (h1.toSylow h2)
    (h3.toSylow h4)
  have hTM : Seven.T7 ≤ H.map (MulAut.conj g).toMonoidHom := by
    intro x hx
    have hx' : x ∈ ((g • h1.toSylow h2 : Sylow 2 (alternatingGroup (Fin 7))) :
        Subgroup (alternatingGroup (Fin 7))) := by
      rw [hg]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    exact ⟨y, hSH hy, rfl⟩
  have hM : Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨i, hi, hiZ⟩ := Seven.overgroup_Z hTM
  have h5 := Seven.card_Z hi
  rw [← hiZ, Seven.card_map_subtype, hM] at h5
  interval_cases i <;> simp at h5 <;> omega


theorem burnsideA315x_prime_dvd_lcm {r : ℕ} (hr : r.Prime) (M : Multiset ℕ) (h : r ∣ M.lcm) :
    ∃ c ∈ M, r ∣ c := by
  induction M using Multiset.induction_on with
  | empty =>
    rw [Multiset.lcm_zero] at h
    exact absurd (Nat.le_of_dvd one_pos h) (by have := hr.two_le; omega)
  | cons a s ih =>
    rw [Multiset.lcm_cons, lcm_eq_nat_lcm] at h
    rcases (Nat.Prime.dvd_lcm hr).1 h with h | h
    · exact ⟨a, Multiset.mem_cons_self a s, h⟩
    · obtain ⟨c, hc, hrc⟩ := ih h
      exact ⟨c, Multiset.mem_cons_of_mem hc, hrc⟩

theorem burnsideA315x_perm_two_primes {n r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (h1 : n < r + s) (h2 : n < r * s) (σ : Equiv.Perm (Fin n)) (hσr : r ∣ orderOf σ)
    (hσs : s ∣ orderOf σ) : False := by
  classical
  rw [← Equiv.Perm.lcm_cycleType] at hσr hσs
  obtain ⟨c, hc, hrc⟩ := burnsideA315x_prime_dvd_lcm hr _ hσr
  obtain ⟨c', hc', hsc'⟩ := burnsideA315x_prime_dvd_lcm hs _ hσs
  have hsum : σ.cycleType.sum ≤ n := by simpa using Equiv.Perm.sum_cycleType_le σ
  have hle : ∀ x ∈ σ.cycleType, x ≤ σ.cycleType.sum :=
    Multiset.single_le_sum (fun _ _ => Nat.zero_le _)
  by_cases hcc : c = c'
  · subst hcc
    have hdvd : r * s ∣ c :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hr hs).2 hrs) hrc hsc'
    have hpos : 0 < c := by have := Equiv.Perm.two_le_of_mem_cycleType hc; omega
    have := Nat.le_of_dvd hpos hdvd
    have := hle c hc
    omega
  · have hc'e : c' ∈ σ.cycleType.erase c := (Multiset.mem_erase_of_ne (Ne.symm hcc)).2 hc'
    have e1 : σ.cycleType.sum = c + (σ.cycleType.erase c).sum := by
      conv_lhs => rw [← Multiset.cons_erase hc]
      rw [Multiset.sum_cons]
    have e2 : c' ≤ (σ.cycleType.erase c).sum :=
      Multiset.single_le_sum (fun _ _ => Nat.zero_le _) c' hc'e
    have hcr : r ≤ c := Nat.le_of_dvd (by have := Equiv.Perm.two_le_of_mem_cycleType hc; omega) hrc
    have hcs : s ≤ c' :=
      Nat.le_of_dvd (by have := Equiv.Perm.two_le_of_mem_cycleType hc'; omega) hsc'
    omega


theorem burnsideA315x_alt_odd_inner {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    {α : MulAut (alternatingGroup (Fin n))} (hα : Odd (orderOf α)) :
    ∃ l : alternatingGroup (Fin n), α = MulAut.conj l := by
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    hn α
  have hpow : ∀ k : ℕ, ∀ g : alternatingGroup (Fin n),
      (((α ^ k) g : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = σ ^ k * g * (σ ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ', MulAut.mul_apply, hσ, ih, pow_succ']
      group
  obtain ⟨j, hj⟩ := hα
  have hm : α ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one α
  have h6 : α ^ (2 * j + 2) = α := by rw [pow_succ, pow_succ, ← pow_succ, hm, one_mul]
  have hsign : Equiv.Perm.sign (σ ^ (2 * j + 2)) = 1 := by
    rw [map_pow, show 2 * j + 2 = 2 * (j + 1) by ring, pow_mul, Int.units_sq, one_pow]
  refine ⟨⟨σ ^ (2 * j + 2), Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, MulEquiv.ext fun g => ?_⟩
  apply Subtype.ext
  calc ((α g : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
      = (((α ^ (2 * j + 2)) g : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by rw [h6]
    _ = σ ^ (2 * j + 2) * g * (σ ^ (2 * j + 2))⁻¹ := hpow _ g
    _ = _ := rfl


open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Unc25K1.A6Model in
theorem burnsideA315x_alt6_odd_inner {α : MulAut (alternatingGroup (Fin 6))}
    (hα : Odd (orderOf α)) : ∃ l : alternatingGroup (Fin 6), α = MulAut.conj l := by
  obtain ⟨-, ψ, -, -⟩ := exists_pslEquiv
  set φ : alternatingGroup (Fin 6) ≃* ↥A6Models.psl29 := ψ.symm with hφ
  set b : ↥A6Models.autA6 := thetaEquiv φ α with hb
  have hbodd : Odd (orderOf b) := by
    rw [hb, MulEquiv.orderOf_eq]
    exact hα
  have hmem : (b : P10) ∈ A6Models.psl29 := by
    let N : Subgroup ↥A6Models.autA6 := A6Models.psl29.subgroupOf A6Models.autA6
    haveI hN : N.Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using psl29_normal (g : P10) g.2 (n : P10) hn⟩
    have hcardN : Nat.card N = 360 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe psl29_le_autA6).toEquiv, card_psl29]
    have hQ : Nat.card (↥A6Models.autA6 ⧸ N) = 4 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [card_autA6, hcardN] at this
      omega
    have h1 : orderOf (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N) ∣ orderOf b :=
      orderOf_map_dvd (QuotientGroup.mk' N) b
    have h2 : orderOf (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N) ∣ 4 := by
      rw [← hQ]
      exact orderOf_dvd_natCard _
    have h3 : orderOf (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N) = 1 := by
      have hodd := Odd.of_dvd_nat hbodd h1
      have hle := Nat.le_of_dvd (by norm_num) h2
      have hpos := orderOf_pos (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N)
      have hdiv : ∀ m, m ∣ 4 → m = 1 ∨ m = 2 ∨ m = 4 := by
        intro m hm
        have := Nat.le_of_dvd (by norm_num) hm
        interval_cases m <;> simp_all
      rcases hdiv _ h2 with h | h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
      · rw [h] at hodd; exact absurd hodd (by decide)
    rw [orderOf_eq_one_iff] at h3
    have := (QuotientGroup.eq_one_iff b).1 h3
    exact Subgroup.mem_subgroupOf.1 this
  refine ⟨ψ ⟨(b : P10), hmem⟩, MulEquiv.ext fun k => ?_⟩
  apply φ.injective
  apply Subtype.ext
  have hspec := thetaEquiv_spec φ α k
  rw [← hb] at hspec
  rw [hspec, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have : φ (ψ ⟨(b : P10), hmem⟩) = ⟨(b : P10), hmem⟩ := by simp [hφ]
  rw [this]
  rfl


theorem burnsideA315x_out_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ β : MulAut Y, Odd (orderOf β) → ∃ l : Y, β = MulAut.conj l) :
    ∀ α : MulAut X, Odd (orderOf α) → ∃ l : X, α = MulAut.conj l := by
  intro α hα
  have hodd : Odd (orderOf (MulAut.congr e α)) := by rwa [MulEquiv.orderOf_eq]
  obtain ⟨l', hl'⟩ := h _ hodd
  refine ⟨e.symm l', MulEquiv.ext fun x => ?_⟩
  apply e.injective
  have h1 : (MulAut.congr e α) (e x) = (MulAut.conj l') (e x) := by rw [hl']
  have h2 : (MulAut.congr e α) (e x) = e (α x) := by
    show e (α (e.symm (e x))) = e (α x)
    rw [e.symm_apply_apply]
  have h3 : (MulAut.conj l') (e x) = e ((MulAut.conj (e.symm l')) x) := by
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, e.apply_symm_apply]
  rw [h2, h3] at h1
  exact h1

theorem burnsideA315x_out_alt {X : Type} [Group X] {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    (e : X ≃* alternatingGroup (Fin n)) :
    ∀ α : MulAut X, Odd (orderOf α) → ∃ l : X, α = MulAut.conj l := by
  refine burnsideA315x_out_of_mulEquiv e fun β hβ => ?_
  by_cases h6 : n = 6
  · subst h6
    exact burnsideA315x_alt6_odd_inner hβ
  · exact burnsideA315x_alt_odd_inner (by omega) hβ


open scoped Pointwise in
theorem burnsideA315x_Config.sup_card {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) :
    S ≤ B ⊔ S ∧ Nat.card ↥(B ⊔ S) = Nat.card ↥B * Nat.card ↥S := by
  obtain ⟨k, hk⟩ := hc.sylow.2.1.exists_card_eq
  have hdB : Nat.card ↥(B ⊓ S) ∣ Nat.card ↥B := Subgroup.card_dvd_of_le inf_le_left
  have hdS : Nat.card ↥(B ⊓ S) ∣ 2 ^ k := hk ▸ Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime (Nat.card ↥B) (2 ^ k) :=
    (Nat.coprime_two_left.2 hc.odd).symm.pow_right k
  have h1 : Nat.card ↥(B ⊓ S) ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hdB hdS
  have hbot : B ⊓ S = ⊥ := Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h1)
  exact ⟨le_sup_right, burnsideA315x_card_sup hc.perm hbot⟩

theorem burnsideA315x_Config.false_of_pow_three {X : Type} [Group X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) [Finite X] {k : ℕ} (h : Nat.card ↥B = 3 ^ k) : False :=
  hc.not3 (IsPGroup.of_card h)

theorem burnsideA315x_Config.exists_order_mul {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hrB : r ∣ Nat.card ↥B) (hsB : s ∣ Nat.card ↥B) : ∃ z : X, z ∈ B ∧ orderOf z = r * s := by
  rcases hc.cases with hab | ⟨q, hq, hBq⟩
  · haveI : Fact r.Prime := ⟨hr⟩
    haveI : Fact s.Prime := ⟨hs⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) r hrB
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) s hsB
    have hcomm : Commute x y := hab.is_comm.comm x y
    have hcop : Nat.Coprime (orderOf x) (orderOf y) := by
      rw [hx, hy]
      exact (Nat.coprime_primes hr hs).2 hrs
    refine ⟨((x * y : ↥B) : X), (x * y : ↥B).2, ?_⟩
    rw [Subgroup.orderOf_coe, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hx, hy]
  · exfalso
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨k, hk⟩ := hBq.exists_card_eq
    rw [hk] at hrB hsB
    have h1 := (Nat.prime_dvd_prime_iff_eq hr hq).1 (hr.dvd_of_dvd_pow hrB)
    have h2 := (Nat.prime_dvd_prime_iff_eq hs hq).1 (hs.dvd_of_dvd_pow hsB)
    exact hrs (h1.trans h2.symm)

theorem burnsideA315x_alt_two {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {n : ℕ} (e : X ≃* alternatingGroup (Fin n)) {r s : ℕ}
    (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) (h1 : n < r + s) (h2 : n < r * s)
    (hrB : r ∣ Nat.card ↥B) (hsB : s ∣ Nat.card ↥B) : False := by
  obtain ⟨z, -, hz⟩ := hc.exists_order_mul hr hs hrs hrB hsB
  refine burnsideA315x_perm_two_primes hr hs hrs h1 h2
    ((e z : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ?_ ?_
  · have : orderOf ((e z : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = r * s := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hz]
    rw [this]
    exact Dvd.intro _ rfl
  · have : orderOf ((e z : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = r * s := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hz]
    rw [this]
    exact Dvd.intro_left _ rfl


theorem burnsideA315x_alt_orders_B {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {n k m : ℕ} (e : X ≃* alternatingGroup (Fin n))
    (hcard : Nat.card (alternatingGroup (Fin n)) = 2 ^ k * m) (hm : ¬ 2 ∣ m) (P : ℕ → Prop)
    (hP : ∀ S' H : Subgroup ↥(alternatingGroup (Fin n)), CFSG.QuasithinUnique.IsSylowTwoOf S' ⊤ →
      S' ≤ H → P (Nat.card H)) : P (Nat.card ↥B * 2 ^ k) := by
  have hS' := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_map_mulEquiv e hc.sylow
  obtain ⟨hle, hcardsup⟩ := hc.sup_card
  have hSk : Nat.card ↥(S.map e.toMonoidHom) = 2 ^ k :=
    CFSG.Quasithin.H13.FiveNorm.card_eq_of_isSylowTwoOf_top hS' hcard hm
  have hSk' : Nat.card ↥S = 2 ^ k := by
    rw [← hSk, Subgroup.card_map_of_injective e.injective]
  have := hP _ _ hS' (Subgroup.map_mono hle : S.map e.toMonoidHom ≤ (B ⊔ S).map e.toMonoidHom)
  rwa [Subgroup.card_map_of_injective e.injective, hcardsup, hSk'] at this

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L in
theorem burnsideA315x_alt_false
    {X : Type} [Group X] {S B : Subgroup X} (hc : burnsideA315x_Config X S B) {n : ℕ}
    (hn5 : 5 ≤ n) (hn8 : n ≤ 8) (e : X ≃* alternatingGroup (Fin n)) : False := by
  haveI : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have h3 : ∀ (k : ℕ), Nat.card ↥B = 3 ^ k → False := fun k h => hc.false_of_pow_three h
  have two : ∀ r s : ℕ, r.Prime → s.Prime → r ≠ s → n < r + s → n < r * s →
      r ∣ Nat.card ↥B → s ∣ Nat.card ↥B → False :=
    fun r s hr hs hrs h1 h2 hrB hsB => burnsideA315x_alt_two hc e hr hs hrs h1 h2 hrB hsB
  have p3 : Nat.Prime 3 := Nat.prime_three
  have p5 : Nat.Prime 5 := by norm_num
  have p7 : Nat.Prime 7 := by norm_num
  interval_cases n
  · have h := burnsideA315x_alt_orders_B hc e (k := 2) (m := 15)
      (by rw [CFSG.QuasithinUnique.Bridge.Over.CertA5.card_alt]; norm_num) (by decide)
      (fun N => N = 4 ∨ N = 12 ∨ N = 60)
      (fun S' H hS' hle => burnsideA315x_alt5_orders hS' hle)
    have hB : Nat.card ↥B = 1 ∨ Nat.card ↥B = 3 ∨ Nat.card ↥B = 15 := by omega
    rcases hB with hB | hB | hB
    · exact h3 0 (by rw [hB]; rfl)
    · exact h3 1 (by rw [hB]; rfl)
    · exact two 3 5 p3 p5 (by norm_num) (by norm_num) (by norm_num) (by rw [hB]; norm_num)
        (by rw [hB]; norm_num)
  · have h := burnsideA315x_alt_orders_B hc e (k := 3) (m := 45)
      (by rw [CFSG.QuasithinUnique.L246C127.Even6.card_alt]; norm_num) (by decide)
      (fun N => N = 8 ∨ N = 24 ∨ N = 360)
      (fun S' H hS' hle => burnsideA315x_alt6_orders hS' hle)
    have hB : Nat.card ↥B = 1 ∨ Nat.card ↥B = 3 ∨ Nat.card ↥B = 45 := by omega
    rcases hB with hB | hB | hB
    · exact h3 0 (by rw [hB]; rfl)
    · exact h3 1 (by rw [hB]; rfl)
    · exact two 3 5 p3 p5 (by norm_num) (by norm_num) (by norm_num) (by rw [hB]; norm_num)
        (by rw [hB]; norm_num)
  · have h := burnsideA315x_alt_orders_B hc e (k := 3) (m := 315)
      (by rw [Seven.card_A7s]; norm_num) (by decide)
      (fun N => N = 8 ∨ N = 24 ∨ N = 72 ∨ N = 120 ∨ N = 168 ∨ N = 360 ∨ N = 2520)
      (fun S' H hS' hle => burnsideA315x_alt7_orders hS' hle)
    have hB : Nat.card ↥B = 1 ∨ Nat.card ↥B = 3 ∨ Nat.card ↥B = 9 ∨ Nat.card ↥B = 15 ∨
        Nat.card ↥B = 21 ∨ Nat.card ↥B = 45 ∨ Nat.card ↥B = 315 := by omega
    rcases hB with hB | hB | hB | hB | hB | hB | hB
    · exact h3 0 (by rw [hB]; rfl)
    · exact h3 1 (by rw [hB]; rfl)
    · exact h3 2 (by rw [hB]; rfl)
    · exact two 3 5 p3 p5 (by norm_num) (by norm_num) (by norm_num) (by rw [hB]; norm_num)
        (by rw [hB]; norm_num)
    · exact two 3 7 p3 p7 (by norm_num) (by norm_num) (by norm_num) (by rw [hB]; norm_num)
        (by rw [hB]; norm_num)
    · exact two 3 5 p3 p5 (by norm_num) (by norm_num) (by norm_num) (by rw [hB]; norm_num)
        (by rw [hB]; norm_num)
    · exact two 3 5 p3 p5 (by norm_num) (by norm_num) (by norm_num) (by rw [hB]; norm_num)
        (by rw [hB]; norm_num)
  · have h := burnsideA315x_alt_orders_B hc e (k := 6) (m := 315)
      (by rw [CFSG.QuasithinUnique.L246C127.Even8.card_alt]; norm_num) (by decide)
      (fun N => N = 64 ∨ N = 192 ∨ N = 576 ∨ N = 1344 ∨ N = 20160)
      (fun S' H hS' hle => burnsideA315x_alt8_orders hS' hle)
    have hB : Nat.card ↥B = 1 ∨ Nat.card ↥B = 3 ∨ Nat.card ↥B = 9 ∨ Nat.card ↥B = 21 ∨
        Nat.card ↥B = 315 := by omega
    rcases hB with hB | hB | hB | hB | hB
    · exact h3 0 (by rw [hB]; rfl)
    · exact h3 1 (by rw [hB]; rfl)
    · exact h3 2 (by rw [hB]; rfl)
    · exact two 3 7 p3 p7 (by norm_num) (by norm_num) (by norm_num) (by rw [hB]; norm_num)
        (by rw [hB]; norm_num)
    · exact two 5 7 p5 p7 (by norm_num) (by norm_num) (by norm_num) (by rw [hB]; norm_num)
        (by rw [hB]; norm_num)


theorem burnsideA315x_altFact :
    CFSG.Quasithin.A315AltFact := by
  intro G _ L T B h n hn5 hn8 he
  obtain ⟨e⟩ := he
  obtain ⟨-, hc⟩ := burnsideA315x_config_of_hyp h (burnsideA315x_out_alt hn5 hn8 e)
  exact burnsideA315x_alt_false hc hn5 hn8 e


theorem burnsideA315x_psl2_odd_inner {K : Type} [Field K] [Finite K] {p k : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ k) (hk : k = 1 ∨ k = 2) :
    ∀ α : MulAut (CFSG.GorensteinWalter.PSL2 K), Odd (orderOf α) →
      ∃ x : CFSG.GorensteinWalter.PSL2 K, α = MulAut.conj x := by
  intro α hα
  set γ := (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearEquivAut K).symm α
    with hγ
  have hγm : γ ^ orderOf α = 1 := by rw [hγ, ← map_pow, pow_orderOf_eq_one, map_one]
  have hψ : (SemidirectProduct.rightHom γ) ^ orderOf α = 1 := by rw [← map_pow, hγm, map_one]
  have hcard : Nat.card (RingAut K) = k :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1
  have hcop : Nat.Coprime (orderOf α) k := by
    rcases hk with rfl | rfl
    · exact Nat.coprime_one_right _
    · exact Nat.coprime_two_right.2 hα
  have hord : orderOf (SemidirectProduct.rightHom γ) = 1 := by
    have h1 : orderOf (SemidirectProduct.rightHom γ) ∣ orderOf α := orderOf_dvd_of_pow_eq_one hψ
    have h2 : orderOf (SemidirectProduct.rightHom γ) ∣ k := hcard ▸ orderOf_dvd_natCard _
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hψ1 : SemidirectProduct.rightHom γ = 1 := orderOf_eq_one_iff.mp hord
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.mem_range_pglAction_of_rightHom_eq_one hψ1
  have hg' : g ^ orderOf α = 1 := by
    apply CFSG.RankThree.PartTwo.KFacts.pglAction_injective
    rw [map_pow, hg, pow_orderOf_eq_one, map_one]
  obtain ⟨x, hx⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_odd hα hg'
  refine ⟨x, ?_⟩
  rw [← hg, ← hx]
  exact CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL K x


theorem burnsideA315x_sylow_facts {F : Type} [Field F] [Finite F] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = p ^ e)
    {S : Subgroup (CFSG.GorensteinWalter.PSL2 F)} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    (∃ m : ℕ, 1 ≤ m ∧ Nat.card ↥S = 2 ^ (m + 1)) ∧ ¬ IsCyclic ↥S := by
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, e, hp, hp.odd_of_ne_two hp2, he, hF⟩
  have hD := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd
  obtain ⟨h1, h2⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hS
  obtain ⟨m, hm, ⟨eS⟩⟩ := hD (h1.toSylow h2)
  have eS' : ↥S ≃* DihedralGroup (2 ^ m) := eS
  refine ⟨⟨m, hm, ?_⟩, fun hc => ?_⟩
  · rw [Nat.card_congr eS'.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  · have : IsCyclic (DihedralGroup (2 ^ m)) := isCyclic_of_surjective eS'.toMonoidHom eS'.surjective
    refine DihedralGroup.not_isCyclic (n := 2 ^ m) ?_ this
    intro h
    have : 2 ^ m = 2 ^ 0 := by rw [h]; rfl
    have := Nat.pow_right_injective (le_refl 2) this
    omega


theorem burnsideA315x_cyclic_of_le {X : Type} [Group X] {S H : Subgroup X} (hSH : S ≤ H)
    (hH : IsCyclic ↥H) : IsCyclic ↥S :=
  isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hSH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hSH).surjective

theorem burnsideA315x_alt_no_order {Y : Type} [Group Y] {n : ℕ} (e : Y ≃* alternatingGroup (Fin n))
    {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) (h1 : n < r + s) (h2 : n < r * s)
    (y : Y) (hy : orderOf y = r * s) : False := by
  have : orderOf ((e y : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = r * s := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
  refine burnsideA315x_perm_two_primes hr hs hrs h1 h2
    ((e y : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ?_ ?_
  · rw [this]; exact Dvd.intro _ rfl
  · rw [this]; exact Dvd.intro_left _ rfl

theorem burnsideA315x_case_cyclic {X : Type} [Group X] {S B : Subgroup X}
    (hS : ¬ IsCyclic ↥S) (hH : IsCyclic ↥(B ⊔ S)) : False :=
  hS (burnsideA315x_cyclic_of_le le_sup_right hH)

theorem burnsideA315x_case_small {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {k : ℕ} (hk : 2 ≤ k) (hSk : Nat.card ↥S = 2 ^ k)
    (hH : Nat.card ↥(B ⊔ S) = 12 ∨ Nat.card ↥(B ⊔ S) = 24) : False := by
  obtain ⟨-, hcard⟩ := hc.sup_card
  rw [hSk] at hcard
  have hb := hc.odd
  have hk4 : k ≤ 4 := by
    by_contra h
    have h1 : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 0 < Nat.card ↥B := Nat.card_pos
    rcases hH with h | h <;> rw [h] at hcard <;> nlinarith
  have h3 : Nat.card ↥B = 3 := by
    obtain ⟨j, hj⟩ := hb
    interval_cases k <;> rcases hH with h | h <;> rw [h] at hcard <;> omega
  exact hc.false_of_pow_three (k := 1) (by rw [h3]; rfl)

theorem burnsideA315x_case_A5 {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {k : ℕ} (hk : 2 ≤ k) (hSk : Nat.card ↥S = 2 ^ k)
    (e : ↥(B ⊔ S) ≃* alternatingGroup (Fin 5)) (hH : Nat.card ↥(B ⊔ S) = 60) : False := by
  obtain ⟨-, hcard⟩ := hc.sup_card
  rw [hSk, hH] at hcard
  have hb := hc.odd
  have hk4 : k ≤ 5 := by
    by_contra h
    have h1 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 0 < Nat.card ↥B := Nat.card_pos
    nlinarith
  have h3 : Nat.card ↥B = 15 := by
    obtain ⟨j, hj⟩ := hb
    interval_cases k <;> omega
  obtain ⟨z, hzB, hz⟩ := hc.exists_order_mul (r := 3) (s := 5) Nat.prime_three (by norm_num)
    (by norm_num) (by rw [h3]; norm_num) (by rw [h3]; norm_num)
  exact burnsideA315x_alt_no_order e (r := 3) (s := 5) Nat.prime_three (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (⟨z, (le_sup_left : B ≤ B ⊔ S) hzB⟩ : ↥(B ⊔ S))
    (by rw [Subgroup.orderOf_mk, hz])


theorem burnsideA315x_case_ext {X : Type} [Group X] [Finite X] {S H : Subgroup X} (hSH : S ≤ H)
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} (hSk : Nat.card ↥S = 2 ^ k)
    (hS : ¬ IsCyclic ↥S) (P : Subgroup ↥H) [P.Normal] (hP : Nat.card ↥P = p ^ m)
    (hQ : IsCyclic (↥H ⧸ P)) : False := by
  let f : ↥(S.subgroupOf H) →* ↥H ⧸ P := (QuotientGroup.mk' P).comp (S.subgroupOf H).subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxP : ((x : ↥H)) ∈ P := (QuotientGroup.eq_one_iff _).1 hx
    have h1 : orderOf (x : ↥H) ∣ p ^ m := by
      rw [← hP]
      have := orderOf_dvd_natCard (⟨(x : ↥H), hxP⟩ : ↥P)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf (x : ↥H) ∣ 2 ^ k := by
      rw [← hSk, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv]
      have := orderOf_dvd_natCard x
      rwa [← Subgroup.orderOf_coe] at this
    have hcop : Nat.Coprime (p ^ m) (2 ^ k) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have h3 : orderOf (x : ↥H) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    have h4 : (x : ↥H) = 1 := orderOf_eq_one_iff.1 h3
    exact Subtype.ext h4
  have hc : IsCyclic ↥(S.subgroupOf H) := isCyclic_of_injective f hinj
  exact hS (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hSH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hSH).surjective)


theorem burnsideA315x_rot_cyclic {X : Type} [Group X] {H : Subgroup X} {z : ℕ} [NeZero z]
    (e : ↥H ≃* DihedralGroup z) (T : Subgroup X) (hTH : T ≤ H)
    (h : ∀ t : X, ∀ ht : t ∈ T, ∃ i : ZMod z, e ⟨t, hTH ht⟩ = DihedralGroup.r i) :
    IsCyclic ↥T := by
  let f : ↥T →* DihedralGroup z := e.toMonoidHom.comp (Subgroup.inclusion hTH)
  have hf : Function.Injective f := by
    intro a b hab
    exact Subgroup.inclusion_injective hTH (e.injective hab)
  have hrange : f.range ≤ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := h t.1 t.2
    have : f t = DihedralGroup.r i := hi
    rw [this]
    refine ⟨(i.val : ℤ), ?_⟩
    show DihedralGroup.r 1 ^ ((i.val : ℕ) : ℤ) = DihedralGroup.r i
    rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
  haveI : IsCyclic ↥(Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)) := inferInstance
  have h1 : IsCyclic ↥f.range := burnsideA315x_cyclic_of_le hrange inferInstance
  exact isCyclic_of_surjective (MonoidHom.ofInjective hf).symm.toMonoidHom
    (MonoidHom.ofInjective hf).symm.surjective

theorem burnsideA315x_case_dihedral {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {k : ℕ} (hk : 2 ≤ k) (hSk : Nat.card ↥S = 2 ^ k)
    (hSnc : ¬ IsCyclic ↥S) {z : ℕ} (e : ↥(B ⊔ S) ≃* DihedralGroup z) :
    IsCyclic ↥B ∧ Nat.card ↥B ∣ z ∧ 2 ∣ z ∧ ∃ s ∈ S, ∀ x ∈ B, s * x * s⁻¹ = x⁻¹ := by
  obtain ⟨hle, hcard⟩ := hc.sup_card
  have hHz : Nat.card ↥(B ⊔ S) = 2 * z := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, mul_zero] at hHz
    exact (Nat.card_pos (α := ↥(B ⊔ S))).ne' hHz
  haveI : NeZero z := ⟨hz0⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  have hz : z = Nat.card ↥B * 2 ^ (k' + 1) := by
    have h1 : 2 * z = 2 * (Nat.card ↥B * 2 ^ (k' + 1)) := by
      rw [← hHz, hcard, hSk]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have hrot : ∀ y : ↥(B ⊔ S), Odd (orderOf y) → ∃ i : ZMod z, e y = DihedralGroup.r i := by
    intro y hy
    rcases hey : e y with i | i
    · exact ⟨i, rfl⟩
    · exfalso
      have h2 : orderOf (e y) = orderOf y := MulEquiv.orderOf_eq e y
      rw [hey, DihedralGroup.orderOf_sr] at h2
      rw [← h2] at hy
      exact absurd hy (by decide)
  have hBrot : ∀ t : X, ∀ ht : t ∈ B, ∃ i : ZMod z,
      e ⟨t, (le_sup_left : B ≤ B ⊔ S) ht⟩ = DihedralGroup.r i := by
    intro t ht
    refine hrot _ ?_
    have h1 : orderOf (⟨t, ht⟩ : ↥B) ∣ Nat.card ↥B := orderOf_dvd_natCard _
    have h2 : orderOf (⟨t, (le_sup_left : B ≤ B ⊔ S) ht⟩ : ↥(B ⊔ S)) = orderOf (⟨t, ht⟩ : ↥B) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    rw [h2]
    exact Odd.of_dvd_nat hc.odd h1
  refine ⟨burnsideA315x_rot_cyclic e B le_sup_left hBrot, ⟨2 ^ (k' + 1), hz⟩, ?_, ?_⟩
  · rw [hz]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
  · have hrefl : ∃ s : X, ∃ hs : s ∈ S, ∃ j : ZMod z, e ⟨s, hle hs⟩ = DihedralGroup.sr j := by
      by_contra hno
      push Not at hno
      apply hSnc
      refine burnsideA315x_rot_cyclic e S hle ?_
      intro t ht
      rcases hey : e ⟨t, hle ht⟩ with i | i
      · exact ⟨i, rfl⟩
      · exact absurd hey (hno t ht i)
    obtain ⟨s, hs, j, hsj⟩ := hrefl
    refine ⟨s, hs, fun b hb => ?_⟩
    obtain ⟨i, hi⟩ := hBrot b hb
    have key : (⟨s, hle hs⟩ : ↥(B ⊔ S)) * ⟨b, (le_sup_left : B ≤ B ⊔ S) hb⟩ * ⟨s, hle hs⟩⁻¹ =
        ⟨b, (le_sup_left : B ≤ B ⊔ S) hb⟩⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv, hsj, hi, DihedralGroup.inv_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
      congr 1
      ring
    have := congrArg Subtype.val key
    simpa using this


theorem burnsideA315x_pow_two_pair {a i l : ℕ} (ha : 3 ≤ a) (h1 : a - 1 = 2 ^ i)
    (h2 : a + 1 = 2 ^ l) : a = 3 := by
  have key : ∀ n : ℕ, 2 ^ n = 1 ∨ 2 ^ n = 2 ∨ 4 ∣ 2 ^ n := by
    intro n
    rcases n with _ | _ | n
    · left; rfl
    · right; left; rfl
    · right; right
      exact ⟨2 ^ n, by ring⟩
  rcases key i with hi | hi | hi <;> rcases key l with hl | hl | hl <;> omega

theorem burnsideA315x_dvd_two_pow {N j k c p : ℕ} (hp : p.Prime) (hNp : ¬ p ∣ N)
    (h : N ∣ p ^ j * (2 ^ k * c)) : N ∣ 2 ^ k * c :=
  Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd hp).2 hNp).symm) h


theorem burnsideA315x_case_subfield {X Y : Type} [Group X] [Finite X] [Group Y]
    {S B : Subgroup X} (hc : burnsideA315x_Config X S B) {k : ℕ} (hSk : Nat.card ↥S = 2 ^ k)
    (e : ↥(B ⊔ S) ≃* Y) {p m c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hc12 : c = 1 ∨ c = 2) (hY : Nat.card Y * c = p ^ m * ((p ^ m) ^ 2 - 1))
    (hnc : ∀ u x : Y, orderOf u = p → (orderOf x).Prime → orderOf x ≠ p → Odd (orderOf x) →
      ¬ Commute u x) : False := by
  obtain ⟨hle, hcard⟩ := hc.sup_card
  have hHY : Nat.card ↥(B ⊔ S) = Nat.card Y := Nat.card_congr e.toEquiv
  rw [hSk] at hcard
  have hBY : Nat.card Y = Nat.card ↥B * 2 ^ k := by rw [← hHY, hcard]
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpm : 3 ≤ p ^ m := le_trans hp3 (Nat.le_self_pow (by omega) p)
  have hpY : p ∣ Nat.card Y * c := by
    rw [hY]
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
  have hpY' : p ∣ Nat.card Y := by
    rcases hc12 with rfl | rfl
    · simpa using hpY
    · rcases (Nat.Prime.dvd_mul hp).1 hpY with h | h
      · exact h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
  have hpB : p ∣ Nat.card ↥B := by
    rw [hBY] at hpY'
    rcases (Nat.Prime.dvd_mul hp).1 hpY' with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) p hpB
  let ι : ↥B →* Y := e.toMonoidHom.comp (Subgroup.inclusion le_sup_left)
  have hι : Function.Injective ι := fun a b hab =>
    Subgroup.inclusion_injective le_sup_left (e.injective hab)
  have hall : ∀ {r : ℕ}, r.Prime → r ∣ Nat.card ↥B → r = p := by
    intro r hr hrB
    by_contra hrp
    rcases hc.cases with hab | ⟨q, hq, hBq⟩
    · haveI : Fact r.Prime := ⟨hr⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) r hrB
      have hcomm : Commute u x := hab.is_comm.comm u x
      refine hnc (ι u) (ι x) ?_ ?_ ?_ ?_ (hcomm.map ι)
      · rw [orderOf_injective ι hι u, hu]
      · rw [orderOf_injective ι hι x, hx]; exact hr
      · rw [orderOf_injective ι hι x, hx]; exact hrp
      · rw [orderOf_injective ι hι x, hx]; exact Odd.of_dvd_nat hc.odd hrB
    · haveI : Fact q.Prime := ⟨hq⟩
      obtain ⟨j, hj⟩ := hBq.exists_card_eq
      rw [hj] at hpB hrB
      have h1 := (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hpB)
      have h2 := (Nat.prime_dvd_prime_iff_eq hr hq).1 (hr.dvd_of_dvd_pow hrB)
      exact hrp (h2.trans h1.symm)
  obtain ⟨j, hBp⟩ : ∃ j : ℕ, Nat.card ↥B = p ^ j :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun hd hdB => hall hd hdB)⟩
  set N' := (p ^ m) ^ 2 - 1 with hN'
  have hNp : ¬ p ∣ N' := by
    intro h
    have h1 : (p ^ m) ^ 2 = N' + 1 := by
      have : 1 ≤ (p ^ m) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    have h2 : p ∣ (p ^ m) ^ 2 := Dvd.dvd.pow (dvd_pow_self p (by omega)) (by norm_num)
    rw [h1] at h2
    have := (Nat.dvd_add_right h).1 h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hdiv : N' ∣ p ^ j * (2 ^ k * c) := by
    have : N' ∣ p ^ m * N' := Dvd.intro_left _ rfl
    rw [← hY, hBY, mul_assoc, hBp] at this
    exact this
  have hdiv2 := burnsideA315x_dvd_two_pow hp hNp hdiv
  have hdiv3 : N' ∣ 2 ^ (k + 1) := by
    refine hdiv2.trans ?_
    rcases hc12 with rfl | rfl
    · exact ⟨2, by ring⟩
    · exact ⟨1, by ring⟩
  have hfac : N' = (p ^ m - 1) * (p ^ m + 1) := by
    rw [hN']
    have := Nat.sq_sub_sq (p ^ m) 1
    rw [one_pow] at this
    rw [this, mul_comm]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    ((Dvd.intro _ hfac.symm : (p ^ m - 1) ∣ N').trans hdiv3)
  obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    ((Dvd.intro_left _ hfac.symm : (p ^ m + 1) ∣ N').trans hdiv3)
  have h3 : p ^ m = 3 := burnsideA315x_pow_two_pair hpm hi hl
  have hp3' : p = 3 := by
    have : p ∣ 3 := h3 ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this
  rw [hp3'] at hBp
  exact hc.false_of_pow_three hBp


theorem burnsideA315x_psl2_no_commute {p m : ℕ} [Fact p.Prime] (hm : 1 ≤ m)
    (u x : CFSG.GorensteinWalter.PSL2 (GaloisField p m)) (hu : orderOf u = p)
    (hx : (orderOf x).Prime) (hxp : orderOf x ≠ p) : ¬ Commute u x := by
  intro hcomm
  haveI : Fact (orderOf x).Prime := ⟨hx⟩
  exact CFSG.GorensteinWalter.psl2_no_commuting_distinct_prime_order (F := GaloisField p m)
    (r := p) (f := m) (p := orderOf x) (GaloisField.card p m (by omega)) hxp hu rfl hcomm

theorem burnsideA315x_case_psl {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {k : ℕ} (hSk : Nat.card ↥S = 2 ^ k) {p m : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (e : ↥(B ⊔ S) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m)) : False := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hK : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m (by omega)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p m)) :=
    ⟨p, m, Fact.out, hpodd, hm, hK⟩
  have hcard := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p m) hodd
  rw [hK] at hcard
  have heven : 2 ∣ p ^ m * ((p ^ m) ^ 2 - 1) := by
    have h1 : Odd ((p ^ m) ^ 2) := (hpodd.pow).pow
    have h2 : Even ((p ^ m) ^ 2 - 1) := Nat.Odd.sub_odd h1 odd_one
    exact Dvd.dvd.mul_left (even_iff_two_dvd.1 h2) _
  refine burnsideA315x_case_subfield hc hSk e (c := 2) (Fact.out : p.Prime) hp2 hm (Or.inr rfl)
    ?_ ?_
  · show Nat.card (CFSG.GorensteinWalter.PSL2 (GaloisField p m)) * 2 = _
    rw [hcard]
    exact Nat.div_mul_cancel heven
  · intro u x hu hx hxp _
    exact burnsideA315x_psl2_no_commute hm u x hu hx hxp

theorem burnsideA315x_case_pgl {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {k : ℕ} (hSk : Nat.card ↥S = 2 ^ k) {p m : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (e : ↥(B ⊔ S) ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) : False := by
  have hK : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m (by omega)
  have hcard := CFSG.GorensteinWalter.pgl2_card_formula (GaloisField p m)
  rw [hK] at hcard
  refine burnsideA315x_case_subfield hc hSk e (c := 1) (Fact.out : p.Prime) hp2 hm (Or.inl rfl)
    ?_ ?_
  · show Nat.card (CFSG.GorensteinWalter.PGL2 (GaloisField p m)) * 1 = _
    rw [hcard, mul_one]
  · intro u x hu hx hxp hxodd
    intro hcomm
    have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    obtain ⟨a, ha⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_odd
      (g := u) (n := orderOf u) (by rw [hu]; exact hpodd) (pow_orderOf_eq_one u)
    obtain ⟨b, hb⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_odd
      (g := x) (n := orderOf x) hxodd (pow_orderOf_eq_one x)
    have hinj := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2)
      (R := GaloisField p m)
    have hab : Commute a b := by
      apply hinj
      rw [map_mul, map_mul, ha, hb]
      exact hcomm
    have hoa : orderOf a = orderOf u := by
      rw [← ha]
      exact (orderOf_injective _ hinj a).symm
    have hob : orderOf b = orderOf x := by
      rw [← hb]
      exact (orderOf_injective _ hinj b).symm
    refine burnsideA315x_psl2_no_commute hm a b (hoa.trans hu) ?_ ?_ hab
    · rw [hob]; exact hx
    · rw [hob]; exact hxp


open scoped Pointwise in
theorem burnsideA315x_Config.map {X Y : Type} [Group X] [Group Y] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) (e : X ≃* Y) :
    burnsideA315x_Config Y (S.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  have eB : ↥B ≃* ↥(B.map e.toMonoidHom) := B.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_map_mulEquiv e hc.sylow, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr eB.toEquiv]
    exact hc.odd
  · intro hp
    exact hc.not3 (hp.of_equiv eB.symm)
  · rcases hc.cases with hab | ⟨r, hr, hBr⟩
    · left
      refine ⟨⟨fun a b => ?_⟩⟩
      apply eB.symm.injective
      rw [map_mul, map_mul]
      exact hab.is_comm.comm _ _
    · right
      exact ⟨r, hr, hBr.of_equiv eB⟩
  · exact burnsideA315x_map_permute e.toMonoidHom hc.perm

theorem burnsideA315x_l2_core {p e : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he1 : 1 ≤ e)
    {S B : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e))}
    (hc : burnsideA315x_Config _ S B) :
    IsCyclic ↥B ∧ (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε ((p ^ e : ℕ) : ℤ) ∧
      ((Nat.card ↥B : ℕ) : ℤ) ∣ ((p ^ e : ℕ) : ℤ) - ε) ∧
      ∃ s ∈ S, ∀ x ∈ B, s * x * s⁻¹ = x⁻¹ := by
  have hq : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  obtain ⟨⟨m, hm, hSc⟩, hSnc⟩ :=
    burnsideA315x_sylow_facts (F := GaloisField p e) (Fact.out) hp2 he1 hq hc.sylow
  have hk : 2 ≤ m + 1 := by omega
  obtain ⟨hle, hcard⟩ := hc.sup_card
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hSH : 2 ∣ Nat.card ↥(B ⊔ S) := by
    have h1 : Nat.card ↥S ∣ Nat.card ↥(B ⊔ S) := Subgroup.card_dvd_of_le hle
    rw [hSc] at h1
    exact (dvd_pow_self 2 (by omega)).trans h1
  rcases CFSG.Quasithin.F6.dicksonPSL2_holds p e he1 (B ⊔ S) with
    ⟨-, m', -, hcard'⟩ | ⟨hcyc, -⟩ | ⟨z, hz, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩ |
      ⟨m', t, P, hP, -, hPc, hQc, -, -, -⟩ | ⟨m', hm', ⟨e'⟩⟩ | ⟨m', hm', ⟨e'⟩⟩
  · exfalso
    rw [hcard'] at hSH
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).1
      (Nat.prime_two.dvd_of_dvd_pow hSH)).symm
  · exact (burnsideA315x_case_cyclic hSnc hcyc).elim
  ·
    obtain ⟨hBcyc, hBdvd, h2z, s, hs, hinv⟩ :=
      burnsideA315x_case_dihedral hc hk hSc hSnc e'
    refine ⟨hBcyc, ?_, s, hs, hinv⟩
    have hqodd : Odd (p ^ e) := hpodd.pow
    obtain ⟨t, ht⟩ := hqodd
    have hg : Nat.gcd 2 (p ^ e - 1) = 2 := by
      rw [ht, Nat.add_sub_cancel]
      exact Nat.gcd_eq_left (Dvd.intro t rfl)
    rw [hg] at hz
    obtain ⟨z', hz'⟩ := h2z
    rcases hz with ⟨c, hc'⟩ | ⟨c, hc'⟩
    ·
      refine ⟨-1, Or.inr rfl, ?_, ?_⟩
      · have h4 : (p ^ e + 1) = 4 * (z' * c) := by
          have : (p ^ e + 1) = 2 * ((p ^ e + 1) / 2) := by omega
          rw [this, hc', hz']
          ring
        rw [Int.ModEq]
        omega
      · have hdvd : Nat.card ↥B ∣ p ^ e + 1 := by
          refine hBdvd.trans ⟨2 * c, ?_⟩
          have : (p ^ e + 1) = 2 * ((p ^ e + 1) / 2) := by omega
          rw [this, hc']
          ring
        have := Int.natCast_dvd_natCast.2 hdvd
        push_cast at this ⊢
        simpa using this
    · refine ⟨1, Or.inl rfl, ?_, ?_⟩
      · have h4 : (p ^ e - 1) = 4 * (z' * c) := by
          have : (p ^ e - 1) = 2 * ((p ^ e - 1) / 2) := by omega
          rw [this, hc', hz']
          ring
        rw [Int.ModEq]
        omega
      · have hdvd : Nat.card ↥B ∣ p ^ e - 1 := by
          refine hBdvd.trans ⟨2 * c, ?_⟩
          have : (p ^ e - 1) = 2 * ((p ^ e - 1) / 2) := by omega
          rw [this, hc']
          ring
        have h1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
        have := Int.natCast_dvd_natCast.2 hdvd
        push_cast [Nat.cast_sub h1] at this ⊢
        exact this
  · exfalso
    refine burnsideA315x_case_small hc hk hSc (Or.inl ?_)
    rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  · exfalso
    refine burnsideA315x_case_small hc hk hSc (Or.inr ?_)
    rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  · exfalso
    refine burnsideA315x_case_A5 hc hk hSc e' ?_
    rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  · exfalso
    haveI := hP
    exact burnsideA315x_case_ext le_sup_right (Fact.out : p.Prime) hp2 hSc hSnc P hPc hQc
  · exfalso
    have hm0 : 1 ≤ m' := Nat.pos_of_dvd_of_pos hm' (by omega)
    exact burnsideA315x_case_psl hc hSc hp2 hm0 e'
  · exfalso
    have hm0 : 1 ≤ m' := by
      have := Nat.pos_of_dvd_of_pos hm' (by omega)
      omega
    exact burnsideA315x_case_pgl hc hSc hp2 hm0 e'


theorem burnsideA315x_l2Fact : CFSG.Quasithin.A315L2Fact := by
  intro G _ L T B h p e hp hp2 he1 he2 hL
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := id hL
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (GaloisField p e) := Fintype.ofFinite _
  have hq : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hcardK : Fintype.card K = Fintype.card (GaloisField p e) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hq]
  let eL : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e) :=
    eK.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 2)
        (FiniteField.ringEquivOfCardEq hcardK)))
  have hOut := burnsideA315x_out_of_mulEquiv eL
    (burnsideA315x_psl2_odd_inner hp hq (by omega))
  obtain ⟨hBL, hc⟩ := burnsideA315x_config_of_hyp h hOut
  have hc' := hc.map eL
  obtain ⟨hcyc, ⟨ε, hε1, hε2, hε3⟩, s, hs, hinv⟩ := burnsideA315x_l2_core hp2 he1 hc'
  have eB : ↥B ≃* ↥((B.subgroupOf L).map eL.toMonoidHom) :=
    (Subgroup.subgroupOfEquivOfLe hBL).symm.trans
      ((B.subgroupOf L).equivMapOfInjective eL.toMonoidHom eL.injective)
  have hcardB : Nat.card ↥((B.subgroupOf L).map eL.toMonoidHom) = Nat.card ↥B :=
    (Nat.card_congr eB.toEquiv).symm
  refine ⟨p, e, hp, hp2, he1, he2, hL, hBL, ?_, ⟨ε, hε1, hε2, ?_⟩, ?_⟩
  · haveI := hcyc
    exact isCyclic_of_surjective eB.symm.toMonoidHom eB.symm.surjective
  · rw [← hcardB]
    exact hε3
  · obtain ⟨s₀, hs₀, rfl⟩ := hs
    refine ⟨(s₀ : G), (Subgroup.mem_subgroupOf.1 hs₀), fun x hx => ?_⟩
    have hxm : eL ⟨x, hBL hx⟩ ∈ (B.subgroupOf L).map eL.toMonoidHom :=
      ⟨⟨x, hBL hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    have h1 := hinv _ hxm
    have h2 : s₀ * ⟨x, hBL hx⟩ * s₀⁻¹ = (⟨x, hBL hx⟩ : ↥L)⁻¹ := by
      apply eL.injective
      rw [map_mul, map_mul, map_inv, map_inv]
      exact h1
    have := congrArg Subtype.val h2
    simpa using this


@[expose] def burnsideA315x_LieConcrete : Prop :=
  ∀ (G : Type) [Group G] (L T B : Subgroup G), CFSG.Quasithin.A315Hyp L T B →
    CFSG.Quasithin.A315LieClass ↥L →
      ChA.A315Case5Concrete L T B ∨ CFSG.Quasithin.A315Case6 L T B ∨
        CFSG.Quasithin.A315Case7 L T B

theorem burnsideA315x_assembly (hlist : CFSG.Quasithin.A23SQTKListFact)
    (hal : CFSG.Quasithin.A315AltFact) (hl2 : CFSG.Quasithin.A315L2Fact)
    (hl3 : CFSG.Quasithin.A315L3Fact) (hl3r : CFSG.Quasithin.A315L3RFact)
    (hlie : burnsideA315x_LieConcrete) (hsp : CFSG.Quasithin.A315SporadicFact) : A_3_15 := by
  intro G _ L T B h
  have hL := CFSG.Quasithin.A315.a23List_of_hyp hlist h
  have hl3' : ∀ (δ : Bool) (p : ℕ), p.Prime → p ≠ 2 → CFSG.Quasithin.IsPSLEps3 δ p 1 ↥L →
      CFSG.Quasithin.A315Case2 L T B ∨ CFSG.Quasithin.A315Case3 L T B := by
    intro δ p hp hp2 hLδ
    by_cases hab : IsMulCommutative ↥B
    · exact hl3 G L T B h hab δ p hp hp2 hLδ
    · exfalso
      rcases h.cases with h' | ⟨r, hr, hBr, hBL⟩
      · exact hab h'
      · exact hl3r G L T B h hab δ p hp hp2 hLδ r hr
          (CFSG.Quasithin.A315.three_lt_of_residual h.odd h.residual hr hBr) hBr hBL
  have hlie' : CFSG.Quasithin.A315LieClass ↥L →
      CFSG.Quasithin.A315Case1 L T B ∨ CFSG.Quasithin.A315Case2 L T B ∨
      CFSG.Quasithin.A315Case3 L T B ∨ CFSG.Quasithin.A315Case4 L T B ∨
      ChA.A315Case5Concrete L T B ∨ CFSG.Quasithin.A315Case6 L T B ∨
      CFSG.Quasithin.A315Case7 L T B := fun hc => by
    rcases hlie G L T B h hc with c | c | c
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c)))))
  rcases hL with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨p, hp, hp2, hm⟩ | hchar2 | ⟨n, hn, hm⟩ | ⟨s, hs, hsL⟩
  · exact absurd ⟨e⟩ (hal G L T B h n h5 h8)
  · rcases hm with ⟨f, hf, hm⟩ | hm | hm
    · exact Or.inl (hl2 G L T B h p f hp hp2 (by omega) (by omega) hm)
    · rcases hl3' true p hp hp2 hm with c | c
      · exact Or.inr (Or.inl c)
      · exact Or.inr (Or.inr (Or.inl c))
    · rcases hl3' false p hp hp2 hm with c | c
      · exact Or.inr (Or.inl c)
      · exact Or.inr (Or.inr (Or.inl c))
  · exact hlie' (Or.inl hchar2)
  · exact hlie' (Or.inr ⟨n, hn, hm⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hsp G L T B h ⟨s, hs, hsL⟩))))


theorem burnsideA315x_algebra_torus (F : Type) [Field F] (A : Type) [CommRing A] [Algebra F A]
    [Module.Finite F A] (hA : Module.finrank F A = 3) :
    ∃ T : Subgroup (GL (Fin 3) F), IsMulCommutative ↥T ∧ Nat.card ↥T = Nat.card Aˣ := by
  let b := Module.finBasisOfFinrankEq F A hA
  let φ : A →* Matrix (Fin 3) (Fin 3) F := (Algebra.leftMulMatrix b).toRingHom.toMonoidHom
  let ψ : Aˣ →* GL (Fin 3) F := Units.map φ
  have hφ : Function.Injective φ := Algebra.leftMulMatrix_injective b
  have hψ : Function.Injective ψ := Units.map_injective hφ
  refine ⟨ψ.range, ⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨u, hu⟩ := x.2
    obtain ⟨v, hv⟩ := y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
  · exact (Nat.card_range_of_injective hψ)


theorem burnsideA315x_gl3_tori (F : Type) [Field F] [Finite F] :
    (∃ T : Subgroup (GL (Fin 3) F), IsMulCommutative ↥T ∧ Nat.card ↥T = (Nat.card F - 1) ^ 3) ∧
    (∃ T : Subgroup (GL (Fin 3) F), IsMulCommutative ↥T ∧
      Nat.card ↥T = (Nat.card F ^ 2 - 1) * (Nat.card F - 1)) ∧
    (∃ T : Subgroup (GL (Fin 3) F), IsMulCommutative ↥T ∧ Nat.card ↥T = Nat.card F ^ 3 - 1) := by
  obtain ⟨p, hp⟩ := CharP.exists F
  haveI : CharP F p := hp
  haveI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨T, hT, hc⟩ := burnsideA315x_algebra_torus F (Fin 3 → F) (by simp)
    refine ⟨T, hT, ?_⟩
    rw [hc, Nat.card_congr (MulEquiv.piUnits (M := fun _ : Fin 3 => F)).toEquiv, Nat.card_pi,
      Nat.card_units]
    simp
  · obtain ⟨T, hT, hc⟩ := burnsideA315x_algebra_torus F (FiniteField.Extension F p 2 × F)
      (by rw [Module.finrank_prod, FiniteField.finrank_extension]; simp)
    refine ⟨T, hT, ?_⟩
    rw [hc, Nat.card_congr (MulEquiv.prodUnits (M := FiniteField.Extension F p 2) (N := F)).toEquiv,
      Nat.card_prod, Nat.card_units, Nat.card_units, FiniteField.natCard_extension]
  · obtain ⟨T, hT, hc⟩ := burnsideA315x_algebra_torus F (FiniteField.Extension F p 3)
      (FiniteField.finrank_extension F p 3)
    refine ⟨T, hT, ?_⟩
    rw [hc, Nat.card_units, FiniteField.natCard_extension]


theorem burnsideA315x_gl3_card (F : Type) [Field F] [Finite F] :
    Nat.card (GL (Fin 3) F) = Nat.card F ^ 3 *
      ((Nat.card F - 1) * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_GL_eq 3]
  have : ∏ j ∈ Finset.Icc 1 3, (Nat.card F ^ j - 1) =
      (Nat.card F - 1) * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) := by
    simp [Finset.prod_Icc_succ_top]
  rw [this]

theorem burnsideA315x_gl3_card_eq {q : ℕ} (hq : 2 ≤ q) :
    q ^ 3 * ((q - 1) * (q ^ 2 - 1) * (q ^ 3 - 1)) =
      (q - 1) ^ 3 * (q ^ 3 * ((q + 1) * (q ^ 2 + q + 1))) := by
  obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
  have h2 : (a + 1) ^ 2 - 1 = a * (a + 2) := by
    have : (a + 1) ^ 2 = a * (a + 2) + 1 := by ring
    omega
  have h3 : (a + 1) ^ 3 - 1 = a * (a ^ 2 + 3 * a + 3) := by
    have : (a + 1) ^ 3 = a * (a ^ 2 + 3 * a + 3) + 1 := by ring
    omega
  rw [h2, h3, Nat.add_sub_cancel]
  ring

theorem burnsideA315x_gl3_card_eq' {q : ℕ} (hq : 2 ≤ q) :
    q ^ 3 * ((q - 1) * (q ^ 2 - 1) * (q ^ 3 - 1)) =
      ((q ^ 2 - 1) * (q - 1)) * (q ^ 3 * ((q - 1) * (q ^ 2 + q + 1))) := by
  rw [burnsideA315x_gl3_card_eq hq]
  obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
  have h2 : (a + 1) ^ 2 - 1 = a * (a + 2) := by
    have : (a + 1) ^ 2 = a * (a + 2) + 1 := by ring
    omega
  rw [h2, Nat.add_sub_cancel]
  ring

theorem burnsideA315x_gl3_card_eq'' {q : ℕ} (hq : 2 ≤ q) :
    q ^ 3 * ((q - 1) * (q ^ 2 - 1) * (q ^ 3 - 1)) =
      (q ^ 3 - 1) * (q ^ 3 * ((q - 1) ^ 2 * (q + 1))) := by
  rw [burnsideA315x_gl3_card_eq hq]
  obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
  have h3 : (a + 1) ^ 3 - 1 = a * (a ^ 2 + 3 * a + 3) := by
    have : (a + 1) ^ 3 = a * (a ^ 2 + 3 * a + 3) + 1 := by ring
    omega
  rw [h3, Nat.add_sub_cancel]
  ring


theorem burnsideA315x_factorization_mul_of_not_dvd {X M r : ℕ} (hX : X ≠ 0) (hM : M ≠ 0)
    (hr : ¬ r ∣ M) : (X * M).factorization r = X.factorization r := by
  rw [Nat.factorization_mul hX hM, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hr,
    add_zero]

theorem burnsideA315x_sq_sub_one {q : ℕ} (hq : 1 ≤ q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
  have : (a + 1) ^ 2 = a * (a + 1 + 1) + 1 := by ring
  rw [Nat.add_sub_cancel]
  omega

theorem burnsideA315x_cube_sub_one {q : ℕ} (hq : 1 ≤ q) :
    q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
  have : (a + 1) ^ 3 = a * ((a + 1) ^ 2 + (a + 1) + 1) + 1 := by ring
  rw [Nat.add_sub_cancel]
  omega

theorem burnsideA315x_coprime_one {q r : ℕ} (hq : 2 ≤ q) (hr5 : 5 ≤ r) (h1 : r ∣ q - 1) :
    ¬ r ∣ q + 1 ∧ ¬ r ∣ q ^ 2 + q + 1 := by
  refine ⟨fun h2 => ?_, fun h2 => ?_⟩
  · have : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub h2 h1
    have h3 : (q + 1) - (q - 1) = 2 := by omega
    rw [h3] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · have h3 : q ^ 2 + q + 1 = (q - 1) * (q + 2) + 3 := by
      obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      ring
    have : r ∣ 3 := (Nat.dvd_add_right (h1.mul_right _)).1 (h3 ▸ h2)
    have := Nat.le_of_dvd (by norm_num) this
    omega

theorem burnsideA315x_coprime_succ {q r : ℕ} (hr : r.Prime) (h1 : r ∣ q + 1) :
    ¬ r ∣ q ^ 2 + q + 1 := by
  intro h2
  have h3 : q ^ 2 + q + 1 = q * (q + 1) + 1 := by ring
  have : r ∣ 1 := (Nat.dvd_add_right (h1.mul_left _)).1 (h3 ▸ h2)
  exact hr.one_lt.ne' (Nat.dvd_one.1 this)

theorem burnsideA315x_gl3_key (F : Type) [Field F] [Finite F] {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrq : ¬ r ∣ Nat.card F) :
    ∃ A : Subgroup (GL (Fin 3) F), IsMulCommutative ↥A ∧
      r ^ (Nat.card (GL (Fin 3) F)).factorization r ∣ Nat.card ↥A := by
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨T1, hT1, hc1⟩ := (burnsideA315x_gl3_tori F).1
  obtain ⟨T2, hT2, hc2⟩ := (burnsideA315x_gl3_tori F).2.1
  obtain ⟨T3, hT3, hc3⟩ := (burnsideA315x_gl3_tori F).2.2
  have hGL := burnsideA315x_gl3_card F
  generalize Nat.card F = q at *
  have hqr3 : ¬ r ∣ q ^ 3 := fun h => hrq (hr.dvd_of_dvd_pow h)
  have hq0 : q - 1 ≠ 0 := by omega
  have hq1 : q ^ 2 - 1 ≠ 0 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hq3 : q ^ 3 - 1 ≠ 0 := by
    have : 1 < q ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  by_cases h1 : r ∣ q - 1
  · refine ⟨T1, hT1, ?_⟩
    obtain ⟨c1, c2⟩ := burnsideA315x_coprime_one hq2 hr5 h1
    have hM : ¬ r ∣ q ^ 3 * ((q + 1) * (q ^ 2 + q + 1)) := by
      intro h
      rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · exact hqr3 h
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · exact c1 h
        · exact c2 h
    have hfac : (q ^ 3 * ((q - 1) * (q ^ 2 - 1) * (q ^ 3 - 1))).factorization r =
        ((q - 1) ^ 3).factorization r := by
      rw [burnsideA315x_gl3_card_eq hq2]
      exact burnsideA315x_factorization_mul_of_not_dvd (pow_ne_zero 3 hq0)
        (by positivity) hM
    rw [hGL, hfac, hc1]
    exact Nat.ordProj_dvd _ _
  by_cases h2 : r ∣ q + 1
  · refine ⟨T2, hT2, ?_⟩
    have hM : ¬ r ∣ q ^ 3 * ((q - 1) * (q ^ 2 + q + 1)) := by
      intro h
      rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · exact hqr3 h
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · exact h1 h
        · exact burnsideA315x_coprime_succ hr h2 h
    have hfac : (q ^ 3 * ((q - 1) * (q ^ 2 - 1) * (q ^ 3 - 1))).factorization r =
        ((q ^ 2 - 1) * (q - 1)).factorization r := by
      rw [burnsideA315x_gl3_card_eq' hq2]
      exact burnsideA315x_factorization_mul_of_not_dvd (mul_ne_zero hq1 hq0)
        (by positivity) hM
    rw [hGL, hfac, hc2]
    exact Nat.ordProj_dvd _ _
  by_cases h3 : r ∣ q ^ 2 + q + 1
  · refine ⟨T3, hT3, ?_⟩
    have hM : ¬ r ∣ q ^ 3 * ((q - 1) ^ 2 * (q + 1)) := by
      intro h
      rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · exact hqr3 h
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · exact h1 (hr.dvd_of_dvd_pow h)
        · exact h2 h
    have hfac : (q ^ 3 * ((q - 1) * (q ^ 2 - 1) * (q ^ 3 - 1))).factorization r =
        (q ^ 3 - 1).factorization r := by
      rw [burnsideA315x_gl3_card_eq'' hq2]
      exact burnsideA315x_factorization_mul_of_not_dvd hq3 (by positivity) hM
    rw [hGL, hfac, hc3]
    exact Nat.ordProj_dvd _ _
  · refine ⟨⊥, ⟨⟨fun a b => by simp [Subsingleton.elim a b]⟩⟩, ?_⟩
    have hz : (q ^ 3 * ((q - 1) * (q ^ 2 - 1) * (q ^ 3 - 1))).factorization r = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro h
      rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · exact hqr3 h
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
          · exact h1 h
          · rw [burnsideA315x_sq_sub_one (by omega)] at h
            rcases (Nat.Prime.dvd_mul hr).1 h with h | h
            · exact h1 h
            · exact h2 h
        · rw [burnsideA315x_cube_sub_one (by omega)] at h
          rcases (Nat.Prime.dvd_mul hr).1 h with h | h
          · exact h1 h
          · exact h3 h
    rw [hGL, hz]
    simp


theorem burnsideA315x_gl3_rsub_abelian (F : Type) [Field F] [Finite F] {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrq : ¬ r ∣ Nat.card F) (R : Subgroup (GL (Fin 3) F))
    (hR : IsPGroup r ↥R) : IsMulCommutative ↥R := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨A, hA, hdvd⟩ := burnsideA315x_gl3_key F hr hr5 hrq
  obtain ⟨PA⟩ : Nonempty (Sylow r ↥A) := inferInstance
  have hPAcard : Nat.card ↥(PA : Subgroup ↥A) = r ^ (Nat.card ↥A).factorization r :=
    Sylow.card_eq_multiplicity PA
  have hk1 : (Nat.card (GL (Fin 3) F)).factorization r ≤ (Nat.card ↥A).factorization r := by
    have := (hr.pow_dvd_iff_dvd_ordProj (Nat.card_pos (α := ↥A)).ne').1 hdvd
    exact (Nat.pow_dvd_pow_iff_le_right hr.one_lt).1 this
  have hk2 : (Nat.card ↥A).factorization r ≤ (Nat.card (GL (Fin 3) F)).factorization r := by
    have h := Subgroup.card_subgroup_dvd_card A
    exact (Nat.factorization_le_iff_dvd (Nat.card_pos (α := ↥A)).ne'
      (Nat.card_pos (α := GL (Fin 3) F)).ne').2 h r
  have hk : (Nat.card ↥A).factorization r = (Nat.card (GL (Fin 3) F)).factorization r :=
    le_antisymm hk2 hk1
  let P : Subgroup (GL (Fin 3) F) := (PA : Subgroup ↥A).map A.subtype
  have hPcard : Nat.card ↥P = r ^ (Nat.card (GL (Fin 3) F)).factorization r := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hPAcard, hk]
  let PG : Sylow r (GL (Fin 3) F) := Sylow.ofCard P hPcard
  obtain ⟨P', hRP'⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 3) F) PG P'
  have hPA : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hA.is_comm.comm a b
    exact congrArg A.subtype this
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx : (x : GL (Fin 3) F) ∈ ((g • PG : Sylow r (GL (Fin 3) F)) : Subgroup (GL (Fin 3) F)) := by
    rw [hg]
    exact hRP' x.2
  have hy : (y : GL (Fin 3) F) ∈ ((g • PG : Sylow r (GL (Fin 3) F)) : Subgroup (GL (Fin 3) F)) := by
    rw [hg]
    exact hRP' y.2
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx hy
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby, ← smul_mul', ← smul_mul']
  congr 1
  exact hPA a ha b hb


theorem burnsideA315x_quot_abelian {G Q : Type} [Group G] [Group Q] [Finite G] {r : ℕ}
    [Fact r.Prime] (π : G →* Q) (hπ : Function.Surjective π)
    (hab : ∀ R : Subgroup G, IsPGroup r ↥R → IsMulCommutative ↥R) (R : Subgroup Q)
    (hR : IsPGroup r ↥R) : IsMulCommutative ↥R := by
  haveI : Finite Q := Finite.of_surjective _ hπ
  obtain ⟨P', hRP'⟩ := hR.exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hπ r P'
  have hPS : (P' : Subgroup Q) = (S : Subgroup G).map π := by
    rw [← hS, Sylow.coe_mapSurjective]
  have hSab := hab (S : Subgroup G) S.isPGroup'
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx : (x : Q) ∈ (S : Subgroup G).map π := hPS ▸ hRP' x.2
  have hy : (y : Q) ∈ (S : Subgroup G).map π := hPS ▸ hRP' y.2
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby, ← map_mul, ← map_mul]
  congr 1
  exact congrArg Subtype.val (hSab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem burnsideA315x_proj_rsub_abelian {F : Type} [Field F] [Finite F] {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrq : ¬ r ∣ Nat.card F) (H : Subgroup (GL (Fin 3) F))
    (R : Subgroup (StatedProj H)) (hR : IsPGroup r ↥R) : IsMulCommutative ↥R := by
  haveI : Fact r.Prime := ⟨hr⟩
  refine burnsideA315x_quot_abelian (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf H))
    (QuotientGroup.mk'_surjective _) (fun R' hR' => ?_) R hR
  have h1 : IsPGroup r ↥(R'.map H.subtype) := hR'.map _
  have h2 := burnsideA315x_gl3_rsub_abelian F hr hr5 hrq _ h1
  refine ⟨⟨fun x y => ?_⟩⟩
  have := h2.is_comm.comm ⟨H.subtype x.1, ⟨x.1, x.2, rfl⟩⟩ ⟨H.subtype y.1, ⟨y.1, y.2, rfl⟩⟩
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ↥(R'.map H.subtype) => ((z : GL (Fin 3) F))) this

theorem burnsideA315x_zpowers_isPGroup {X : Type} [Group X] {g : X} {k : ℕ}
    (h : g ^ (2 ^ k) = 1) : IsPGroup 2 ↥(Subgroup.zpowers g) := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])

theorem burnsideA315x_dihedral_witness {X : Type} [Group X] {α γ : X} (h1 : α ^ 2 = 1)
    (h2 : γ ^ 4 = 1) (h3 : α * γ * α⁻¹ = γ⁻¹) (h4 : γ ^ 2 ≠ 1) :
    ∃ D : Subgroup X, IsPGroup 2 ↥D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x := by
  have hα : IsPGroup 2 ↥(Subgroup.zpowers α) :=
    burnsideA315x_zpowers_isPGroup (k := 1) (by simpa using h1)
  have hγ : IsPGroup 2 ↥(Subgroup.zpowers γ) :=
    burnsideA315x_zpowers_isPGroup (k := 2) (by simpa using h2)
  have hαinv : α⁻¹ = α := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, h1]
  have hconj : ∀ n : ℤ, α * γ ^ n * α⁻¹ = γ ^ (-n) := fun n => by
    rw [← conj_zpow, h3, inv_zpow', zpow_neg]
  have hN : Subgroup.zpowers α ≤ Subgroup.normalizer (Subgroup.zpowers γ : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨-n, (hconj n).symm⟩
    · rintro ⟨m, hm⟩
      refine ⟨-m, ?_⟩
      have hy : y = α * γ ^ m * α⁻¹ := by
        have e1 : α⁻¹ * γ ^ m * α = y := by
          rw [hm]
          group
        rw [← e1, hαinv]
      rw [hy, hconj]
  refine ⟨Subgroup.zpowers α ⊔ Subgroup.zpowers γ, hα.to_sup_of_normal_right' hγ hN, α,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers α), γ,
    Subgroup.mem_sup_right (Subgroup.mem_zpowers γ), fun h => h4 ?_⟩
  have h5 : α * γ * α⁻¹ = γ := by rw [h, mul_assoc, mul_inv_cancel, mul_one]
  rw [h3] at h5
  have h6 : γ * γ = 1 := by
    calc γ * γ = γ * γ⁻¹ := by rw [h5]
      _ = 1 := mul_inv_cancel γ
  rwa [← pow_two] at h6

@[expose] def burnsideA315x_gA (K : Type) [Field K] : GL (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], !![0, 1, 0; 1, 0, 0; 0, 0, -1],
    by simp [Matrix.mul_fin_three, Matrix.one_fin_three],
    by simp [Matrix.mul_fin_three, Matrix.one_fin_three]⟩

@[expose] def burnsideA315x_gC (K : Type) [Field K] : GL (Fin 3) K :=
  ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; -1, 0, 0; 0, 0, 1],
    by simp [Matrix.mul_fin_three, Matrix.one_fin_three],
    by simp [Matrix.mul_fin_three, Matrix.one_fin_three]⟩

theorem burnsideA315x_gA_sq (K : Type) [Field K] : burnsideA315x_gA K ^ 2 = 1 := by
  apply Units.ext
  simp [pow_two, burnsideA315x_gA, Matrix.mul_fin_three, Matrix.one_fin_three]

theorem burnsideA315x_gC_pow_four (K : Type) [Field K] : burnsideA315x_gC K ^ 4 = 1 := by
  apply Units.ext
  simp [pow_succ, burnsideA315x_gC, Matrix.mul_fin_three, Matrix.one_fin_three]

theorem burnsideA315x_gA_gC (K : Type) [Field K] :
    burnsideA315x_gA K * burnsideA315x_gC K * (burnsideA315x_gA K)⁻¹ = (burnsideA315x_gC K)⁻¹ := by
  apply Units.ext
  simp [burnsideA315x_gA, burnsideA315x_gC, Matrix.mul_fin_three]

theorem burnsideA315x_gC_sq_not_scalar (K : Type) [Field K] (hK : (2 : K) ≠ 0) :
    burnsideA315x_gC K ^ 2 ∉ StatedScalars (Fin 3) K := by
  rintro ⟨u, hu⟩
  have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hu
  simp only [Matrix.GeneralLinearGroup.coe_scalar] at h
  have h0 := congrFun (congrFun h 0) 0
  have h2 := congrFun (congrFun h 2) 2
  simp [pow_two, burnsideA315x_gC, Matrix.mul_fin_three, Matrix.scalar_apply,
    -Units.val_eq_one] at h0 h2
  have h0' : (u : K) = -1 := by simpa using congrArg Units.val h0
  apply hK
  linear_combination h0' - h2

theorem burnsideA315x_proj_witness {K : Type} [Field K] (hK : (2 : K) ≠ 0)
    (H : Subgroup (GL (Fin 3) K)) (hA : burnsideA315x_gA K ∈ H) (hC : burnsideA315x_gC K ∈ H) :
    ∃ D : Subgroup (StatedProj H), IsPGroup 2 ↥D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x := by
  let q : H →* StatedProj H := QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf H)
  let a : H := ⟨burnsideA315x_gA K, hA⟩
  let c : H := ⟨burnsideA315x_gC K, hC⟩
  refine burnsideA315x_dihedral_witness (α := q a) (γ := q c) ?_ ?_ ?_ ?_
  · rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (by simpa [a] using burnsideA315x_gA_sq K)
    rw [this, map_one]
  · rw [← map_pow]
    have : c ^ 4 = 1 := Subtype.ext (by simpa [c] using burnsideA315x_gC_pow_four K)
    rw [this, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul]
    have : a * c * a⁻¹ = c⁻¹ := Subtype.ext (by simpa [a, c] using burnsideA315x_gA_gC K)
    rw [this, map_inv]
  · rw [← map_pow]
    intro h
    have h' : c ^ 2 ∈ (StatedScalars (Fin 3) K).subgroupOf H := (QuotientGroup.eq_one_iff _).1 h
    exact burnsideA315x_gC_sq_not_scalar K hK (by simpa [c] using Subgroup.mem_subgroupOf.1 h')

theorem burnsideA315x_twoGroup_comm {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (hab : IsMulCommutative ↥S) (D : Subgroup X)
    (hD : IsPGroup 2 ↥D) : IsMulCommutative ↥D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hS
  let PS : Sylow 2 X := h1.toSylow h2
  obtain ⟨P', hDP'⟩ := hD.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X PS P'
  have hPS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx : (x : X) ∈ ((g • PS : Sylow 2 X) : Subgroup X) := by
    rw [hg]
    exact hDP' x.2
  have hy : (y : X) ∈ ((g • PS : Sylow 2 X) : Subgroup X) := by
    rw [hg]
    exact hDP' y.2
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx hy
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby, ← smul_mul', ← smul_mul']
  congr 1
  exact hPS a ha b hb

theorem burnsideA315x_false_of_comm_sylow {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (hab : IsMulCommutative ↥S)
    (hw : ∃ D : Subgroup X, IsPGroup 2 ↥D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x) : False := by
  obtain ⟨D, hD, x, hx, y, hy, hxy⟩ := hw
  exact hxy (congrArg Subtype.val
    ((burnsideA315x_twoGroup_comm hS hab D hD).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))

theorem burnsideA315x_comm_of_card_dvd_sq {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (h : Nat.card G ∣ p ^ 2) : IsMulCommutative G := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow hp).1 h
  interval_cases i
  · haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.1 (by simpa using hcard)).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos hp.pos 1).ne')
    haveI : IsCyclic G := isCyclic_of_prime_card (by simpa using hcard)
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard

theorem burnsideA315x_eq_of_nonabelian {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B Q : Subgroup G} (hBQ : B ≤ Q) (hQ : Nat.card ↥Q = p ^ 3) (hB : IsPGroup p ↥B)
    (hnab : ¬ IsMulCommutative ↥B) : B = Q := by
  by_contra hne
  have hdvd : Nat.card ↥B ∣ p ^ 3 := hQ ▸ Subgroup.card_dvd_of_le hBQ
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  by_cases hi3 : i = 3
  · apply hne
    exact Subgroup.eq_of_le_of_card_ge hBQ (by rw [hQ, hcard, hi3])
  · apply hnab
    refine burnsideA315x_comm_of_card_dvd_sq hp ?_
    rw [hcard]
    exact pow_dvd_pow p (by omega)

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
@[expose] def burnsideA315x_diagHom (n : ℕ) (K : Type) [Field K] :
    ↥(upperTriangular n K) →* (Fin n → K) where
  toFun A := fun i => (A.1 : Matrix (Fin n) (Fin n) K) i i
  map_one' := by
    funext i
    simp
  map_mul' A B := by
    funext i
    have hA : (A.1 : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
      mem_upperTriangular_iff_isUpperTriangular.1 A.2
    have hB : (B.1 : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
      mem_upperTriangular_iff_isUpperTriangular.1 B.2
    simp [mul_apply_self_of_isUpperTriangular hA hB]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideA315x_commutator_mem_unitriangular {n : ℕ} {K : Type} [Field K]
    {x y : Matrix.SpecialLinearGroup (Fin n) K} (hx : x ∈ upperTriangular n K)
    (hy : y ∈ upperTriangular n K) : x * y * x⁻¹ * y⁻¹ ∈ unitriangular n K := by
  refine ⟨(upperTriangular n K).mul_mem ((upperTriangular n K).mul_mem
    ((upperTriangular n K).mul_mem hx hy) ((upperTriangular n K).inv_mem hx))
    ((upperTriangular n K).inv_mem hy), fun i => ?_⟩
  let X : ↥(upperTriangular n K) := ⟨x, hx⟩
  let Y : ↥(upperTriangular n K) := ⟨y, hy⟩
  let d := burnsideA315x_diagHom n K
  have h1 : d X * d X⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h2 : d Y * d Y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h3 : d (X * Y * X⁻¹ * Y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul]
    calc d X * d Y * d X⁻¹ * d Y⁻¹ = (d X * d X⁻¹) * (d Y * d Y⁻¹) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  have := congrFun h3 i
  simpa [d, burnsideA315x_diagHom, X, Y] using this

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideA315x_upper_two_comm {K : Type} [Field K] [Finite K] {p : ℕ} [CharP K p]
    (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) {D : Subgroup (projectiveSL n K)}
    (hD : IsPGroup 2 ↥D) (hDle : ∀ x ∈ D, ∃ y ∈ upperTriangular n K, proj n K y = x) :
    IsMulCommutative ↥D := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) p (n := n) hn
  have hdisj : Disjoint D (projUnitriangular n K) := by
    rw [← hP]
    exact IsPGroup.disjoint_of_coprime hD P.isPGroup'
      ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨x, hx, hxa⟩ := hDle a a.2
  obtain ⟨y, hy, hyb⟩ := hDle b b.2
  have hc : (a : projectiveSL n K) * b * (a : projectiveSL n K)⁻¹ * (b : projectiveSL n K)⁻¹ ∈
      projUnitriangular n K := by
    refine ⟨x * y * x⁻¹ * y⁻¹, burnsideA315x_commutator_mem_unitriangular hx hy, ?_⟩
    simp [hxa, hyb]
  have hcD : (a : projectiveSL n K) * b * (a : projectiveSL n K)⁻¹ *
      (b : projectiveSL n K)⁻¹ ∈ D :=
    D.mul_mem (D.mul_mem (D.mul_mem a.2 b.2) (D.inv_mem a.2)) (D.inv_mem b.2)
  have h1 := Subgroup.disjoint_def.1 hdisj hcD hc
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)

open scoped Pointwise in
theorem burnsideA315x_Config.sup_solvable {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) (hBnil : Group.IsNilpotent ↥B) :
    Group.IsSolvable ↥(B ⊔ S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, -⟩ := hc.sup_card
  have hBle : B ≤ B ⊔ S := le_sup_left
  have eA : ↥(B.subgroupOf (B ⊔ S)) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBle
  have eC : ↥(S.subgroupOf (B ⊔ S)) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hle
  haveI := hBnil
  refine CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product (B.subgroupOf (B ⊔ S))
    (S.subgroupOf (B ⊔ S)) (Group.nilpotent_of_mulEquiv eA.symm)
    ((hc.sylow.2.1.of_equiv eC.symm).isNilpotent) ?_ ?_
  · rw [Nat.card_congr eA.toEquiv, Nat.card_congr eC.toEquiv]
    obtain ⟨k, hk⟩ := hc.sylow.2.1.exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_left.2 hc.odd).symm.pow_right k
  · intro g
    have hg : (g : X) ∈ ((B ⊔ S : Subgroup X) : Set X) := g.2
    rw [burnsideA315x_coe_sup hc.perm] at hg
    obtain ⟨b, hb, s, hs, hbs⟩ := hg
    exact ⟨⟨b, hBle hb⟩, hb, ⟨s, hle hs⟩, hs, Subtype.ext hbs.symm⟩

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideA315x_l3_core {K : Type} [Field K] [Finite K] {p : ℕ} [CharP K p]
    (hK : Nat.card K = p) (hp : p.Prime) (hp5 : 5 ≤ p)
    {S B : Subgroup (projectiveSL 3 K)} (hc : burnsideA315x_Config _ S B)
    (hB : IsPGroup p ↥B) (hnab : ¬ IsMulCommutative ↥B) : IsMulCommutative ↥S := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) p (n := 3) (by norm_num)
  obtain ⟨P', hBP'⟩ := hB.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 K) P P'
  have h1 : Nat.card ↥(P' : Subgroup (projectiveSL 3 K)) =
      Nat.card ↥(P : Subgroup (projectiveSL 3 K)) := by
    rw [Sylow.card_eq_multiplicity P', Sylow.card_eq_multiplicity P]
  have h2 : Nat.card ↥(P : Subgroup (projectiveSL 3 K)) = p ^ 3 := by
    rw [hP, card_projUnitriangular, hK]
  have hBeq : B = (P' : Subgroup (projectiveSL 3 K)) :=
    burnsideA315x_eq_of_nonabelian hp hBP' (h1.trans h2) hB hnab
  have hsolv : Group.IsSolvable ↥(B ⊔ S) := hc.sup_solvable hB.isNilpotent
  let φ : projectiveSL 3 K ≃* projectiveSL 3 K := MulAut.conj g⁻¹
  let H' : Subgroup (projectiveSL 3 K) := (B ⊔ S).map φ.toMonoidHom
  have hH'solv : Group.IsSolvable ↥H' := by
    have e := (B ⊔ S).equivMapOfInjective φ.toMonoidHom φ.injective
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hUH' : projUnitriangular 3 K ≤ H' := by
    intro u hu
    rw [← hP] at hu
    have hb : (MulAut.conj g) u ∈ B := by
      rw [hBeq, ← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul u (MulAut.conj g) _ hu
    refine ⟨(MulAut.conj g) u, (le_sup_left : B ≤ B ⊔ S) hb, ?_⟩
    simp only [φ, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    group
  have hK4 : 4 ≤ Nat.card K := by omega
  have hH'le : ∀ x ∈ H', ∃ y ∈ upperTriangular 3 K, proj 3 K y = x := by
    intro x hx
    obtain ⟨y, rfl⟩ := proj_surjective 3 K x
    exact ⟨y, CFSG.Quasithin.H13.NQCore.L3Odd.le_upperTriangular_of_isSolvable hK4 hUH'
      hH'solv hx, rfl⟩
  have hD : IsPGroup 2 ↥(S.map φ.toMonoidHom) := hc.sylow.2.1.map _
  have hDcomm := burnsideA315x_upper_two_comm hp hp2 (n := 3) (by norm_num) hD
    (fun x hx => hH'le x (Subgroup.map_mono le_sup_right hx))
  have eS := S.equivMapOfInjective φ.toMonoidHom φ.injective
  refine ⟨⟨fun a b => eS.injective ?_⟩⟩
  rw [map_mul, map_mul]
  exact hDcomm.is_comm.comm _ _

theorem burnsideA315x_not_dvd_cube {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    ¬ p ^ 3 + 1 ∣ p ^ 3 * 2 ^ k := by
  intro hdvd
  have hcop : (p ^ 3 + 1).Coprime (p ^ 3) :=
    Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  have h1 : p ^ 3 + 1 ∣ 2 ^ k := hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hfac : (q + 1) ^ 3 + 1 = (q + 2) * (q * (q + 1) + 1) := by ring
  have hm : (q * (q + 1) + 1) ∣ 2 ^ i := Dvd.intro_left (q + 2) (hfac.symm.trans hi)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hm
  have hodd : Odd (q * (q + 1) + 1) := (Nat.even_mul_succ_self q).add_one
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · rw [hj0, pow_zero] at hj
    have : q * (q + 1) = 0 := by omega
    have hq : q = 0 := by
      rcases Nat.mul_eq_zero.1 this with h | h
      · exact h
      · omega
    omega
  · have : Even (q * (q + 1) + 1) := by
      rw [hj]
      exact (Nat.even_pow.2 ⟨even_two, hjpos.ne'⟩)
    exact (Nat.not_even_iff_odd.2 hodd) this

open CFSG.Quasithin.F134.LieU3 CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in
theorem burnsideA315x_u3_core {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hX : StatedClassicalModel X .PSU 3 p 1) {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) (hB : IsPGroup p ↥B) (hnab : ¬ IsMulCommutative ↥B) :
    IsCyclic ↥S := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hBT⟩ := hB.exists_le_sylow
  obtain ⟨K, _, h, Φ, hΦ, hrange, hcomap⟩ := exists_perm_comap_rkOneUStar_eq hX T
  have hcardT : Nat.card ↥(T : Subgroup X) = p ^ 3 := by
    rw [← hcomap, ← Subgroup.card_map_of_injective hΦ, Subgroup.map_comap_eq, hrange,
      inf_eq_right.2 (rkOneUStar_le_rkOneG h), card_rkOneUStar h, pow_one]
  have hBeq : B = (T : Subgroup X) := burnsideA315x_eq_of_nonabelian hp hBT hcardT hB hnab
  have hUH : rkOneUStar h ≤ (B ⊔ S).map Φ := by
    intro x hx
    have hx' : x ∈ Φ.range := by
      rw [hrange]
      exact rkOneUStar_le_rkOneG h hx
    obtain ⟨y, rfl⟩ := hx'
    have hy : y ∈ (rkOneUStar h).comap Φ := hx
    rw [hcomap, ← hBeq] at hy
    exact ⟨y, (le_sup_left : B ≤ B ⊔ S) hy, rfl⟩
  obtain ⟨-, hcardsup⟩ := hc.sup_card
  obtain ⟨k, hk⟩ := hc.sylow.2.1.exists_card_eq
  have hcardH : Nat.card ↥((B ⊔ S).map Φ) = p ^ 3 * 2 ^ k := by
    rw [Subgroup.card_map_of_injective hΦ, hcardsup, hk, hBeq, hcardT]
  have hfix := le_stabilizer_infL_of_not_dvd h hUH (by
    rw [hcardH, pow_one]
    exact burnsideA315x_not_dvd_cube hp hp2 k)
  have hQinf : S.map Φ ≤ rkOneGInf h := fun x hx =>
    ⟨hrange ▸ Subgroup.map_le_range Φ _ hx, hfix (Subgroup.map_mono le_sup_right hx)⟩
  have hcyc := isCyclic_of_le_rkOneGInf h hQinf (by
    rw [Subgroup.card_map_of_injective hΦ, hk]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)))
  exact isCyclic_of_surjective (S.equivMapOfInjective Φ hΦ).symm.toMonoidHom
    (S.equivMapOfInjective Φ hΦ).symm.surjective

theorem burnsideA315x_gA_mem_SL (K : Type) [Field K] : burnsideA315x_gA K ∈ StatedSL 3 K := by
  apply Subgroup.subset_closure
  simp [burnsideA315x_gA, Matrix.det_fin_three]

theorem burnsideA315x_gC_mem_SL (K : Type) [Field K] : burnsideA315x_gC K ∈ StatedSL 3 K := by
  apply Subgroup.subset_closure
  simp [burnsideA315x_gC, Matrix.det_fin_three]

theorem burnsideA315x_gA_mem_SU (K : Type) [Field K] {q : ℕ} (hq : Odd q) :
    burnsideA315x_gA K ∈ StatedSU 3 q K := by
  unfold StatedSU
  apply Subgroup.subset_closure
  have h0 : (0 : K) ^ q = 0 := zero_pow hq.pos.ne'
  have hm1 : (-1 : K) ^ q = -1 := hq.neg_one_pow
  refine ⟨by simp [burnsideA315x_gA, Matrix.det_fin_three], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideA315x_gA, Matrix.mul_apply, Fin.sum_univ_succ, h0, hm1]

theorem burnsideA315x_gC_mem_SU (K : Type) [Field K] {q : ℕ} (hq : Odd q) :
    burnsideA315x_gC K ∈ StatedSU 3 q K := by
  unfold StatedSU
  apply Subgroup.subset_closure
  have h0 : (0 : K) ^ q = 0 := zero_pow hq.pos.ne'
  have hm1 : (-1 : K) ^ q = -1 := hq.neg_one_pow
  refine ⟨by simp [burnsideA315x_gC, Matrix.det_fin_three], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideA315x_gC, Matrix.mul_apply, Fin.sum_univ_succ, h0, hm1]

theorem burnsideA315x_comm_of_cyclic {G : Type} [Group G] [IsCyclic G] : IsMulCommutative G := by
  obtain ⟨g, hg⟩ := exists_zpow_surjective G
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨m, rfl⟩ := hg a
  obtain ⟨n, rfl⟩ := hg b
  exact (Commute.zpow_zpow_self g m n).eq

theorem burnsideA315x_not_dvd_pow {r p : ℕ} (hr : r.Prime) (hp : p.Prime) (hne : r ≠ p) (k : ℕ) :
    ¬ r ∣ p ^ k := fun h =>
  hne ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h))

theorem burnsideA315x_witness_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hw : ∃ D : Subgroup X, IsPGroup 2 ↥D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x) :
    ∃ D : Subgroup Y, IsPGroup 2 ↥D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x := by
  obtain ⟨D, hD, x, hx, y, hy, hxy⟩ := hw
  refine ⟨D.map e.toMonoidHom, hD.of_equiv (D.equivMapOfInjective e.toMonoidHom e.injective),
    e x, ⟨x, hx, rfl⟩, e y, ⟨y, hy, rfl⟩, fun h => hxy (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

theorem burnsideA315x_l3r_core {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) (δ : Bool) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : CFSG.Quasithin.IsPSLEps3 δ p 1 X) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hBr : IsPGroup r ↥B) (hnab : ¬ IsMulCommutative ↥B) : False := by
  have hr5 : 5 ≤ r := by
    by_contra hlt
    have : r = 4 := by omega
    subst this
    exact absurd hr (by norm_num)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  cases δ
  ·
    have hX' : StatedClassicalModel X .PSU 3 p 1 := hX
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX'
    rcases eq_or_ne r p with rfl | hrp
    · have hcyc := burnsideA315x_u3_core hr hp2 hX (hc := hc) hBr hnab
      haveI := hcyc
      have hScomm : IsMulCommutative ↥S := burnsideA315x_comm_of_cyclic
      haveI : CharP K r :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hr
          (k := 2) (by norm_num) (by rw [hK]; ring)
      have h2 : (2 : K) ≠ 0 := by
        intro h0
        have := (CharP.cast_eq_zero_iff K r 2).1 (by exact_mod_cast h0)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
      have hw := burnsideA315x_proj_witness h2 (StatedSU 3 (r ^ 1) K)
        (burnsideA315x_gA_mem_SU K (hpodd.pow)) (burnsideA315x_gC_mem_SU K (hpodd.pow))
      exact burnsideA315x_false_of_comm_sylow hc.sylow hScomm
        (burnsideA315x_witness_of_equiv e.symm hw)
    · have hrK : ¬ r ∣ Nat.card K := by
        rw [hK, pow_one]
        exact burnsideA315x_not_dvd_pow hr hp hrp _
      have eB := B.equivMapOfInjective e.toMonoidHom e.injective
      have hRab := burnsideA315x_proj_rsub_abelian hr hr5 hrK _ _ (hBr.of_equiv eB)
      exact hnab ⟨⟨fun a b => eB.injective (by
        rw [map_mul, map_mul]
        exact hRab.is_comm.comm _ _)⟩⟩
  ·
    have hX' : StatedClassicalModel X .PSL 3 p 1 := hX
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX'
    rcases eq_or_ne r p with rfl | hrp
    · have hK' : Nat.card K = r := by simpa using hK
      haveI : CharP K r :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hr
          (k := 1) le_rfl (by simpa using hK)
      let e' : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
        e.trans (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 3 K)
      have hc' := hc.map e'
      have eB := B.equivMapOfInjective e'.toMonoidHom e'.injective
      have hScomm' := burnsideA315x_l3_core hK' hr hr5 hc' (hBr.of_equiv eB) (fun hab =>
        hnab ⟨⟨fun a b => eB.injective (by
          rw [map_mul, map_mul]
          exact hab.is_comm.comm _ _)⟩⟩)
      have eS := S.equivMapOfInjective e'.toMonoidHom e'.injective
      have hScomm : IsMulCommutative ↥S := ⟨⟨fun a b => eS.injective (by
        rw [map_mul, map_mul]
        exact hScomm'.is_comm.comm _ _)⟩⟩
      have h2 : (2 : K) ≠ 0 := by
        intro h0
        have := (CharP.cast_eq_zero_iff K r 2).1 (by exact_mod_cast h0)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
      have hw := burnsideA315x_proj_witness h2 (StatedSL 3 K) (burnsideA315x_gA_mem_SL K)
        (burnsideA315x_gC_mem_SL K)
      exact burnsideA315x_false_of_comm_sylow hc.sylow hScomm
        (burnsideA315x_witness_of_equiv e.symm hw)
    · have hrK : ¬ r ∣ Nat.card K := by
        rw [hK]
        exact burnsideA315x_not_dvd_pow hr hp hrp _
      have eB := B.equivMapOfInjective e.toMonoidHom e.injective
      have hRab := burnsideA315x_proj_rsub_abelian hr hr5 hrK _ _ (hBr.of_equiv eB)
      exact hnab ⟨⟨fun a b => eB.injective (by
        rw [map_mul, map_mul]
        exact hRab.is_comm.comm _ _)⟩⟩

theorem burnsideA315x_l3rFact : CFSG.Quasithin.A315L3RFact := by
  intro G _ L T B h hnab δ p hp hp2 hL r hr hr3 hBr hBL
  haveI : Finite G := h.sqtk.finite
  have hc := burnsideA315x_config_of_le h hBL
  have eB : ↥(B.subgroupOf L) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBL
  refine burnsideA315x_l3r_core hc δ hp hp2 hL hr hr3 (hBr.of_equiv eB.symm) (fun hab => hnab ?_)
  exact ⟨⟨fun a b => eB.symm.injective (by
    rw [map_mul, map_mul]
    exact hab.is_comm.comm _ _)⟩⟩

end CFSG.ASVolI
