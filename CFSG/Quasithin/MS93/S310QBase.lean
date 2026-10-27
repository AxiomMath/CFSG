module

public import CFSG.Quasithin.MS93.S310MI

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S310Q

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem puTrans_perfect (h : PUHyp M T L) {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) :
    ⁅puTrans h.le L ρ, puTrans h.le L ρ⁆ = puTrans h.le L ρ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hρ
  rw [puTrans_smul h.le hLn, ← Subgroup.map_commutator, S5B.puTrans_L_baseA h,
    ← imM_commutator h.le h.L_le h.L_le, h.perfect]

theorem commutator_le_of_two_elt (h : PUHyp M T L) {ρ : Vtx (puAmalgam h.le)}
    (hρ : IsMVtx _ ρ) {W Z : Subgroup (puAmalgam h.le).Universal}
    (hW : W ≤ stab _ ρ) (hZ : Z ≤ stab _ ρ)
    (hWn : puTrans h.le L ρ ≤ Subgroup.normalizer (W : Set (puAmalgam h.le).Universal))
    (hZn : puTrans h.le L ρ ≤ Subgroup.normalizer (Z : Set (puAmalgam h.le).Universal))
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ ρ) (hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1)
    (hyQ : y ∉ Qv _ ρ) (hyZ : y ∈ Subgroup.normalizer (Z : Set (puAmalgam h.le).Universal))
    (hyW : ∀ w ∈ W, y * w * y⁻¹ * w⁻¹ ∈ Z) :
    ⁅W, puTrans h.le L ρ⁆ ≤ Z := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hρ
  have hLt : puTrans h.le L (g • baseA (puAmalgam h.le)) =
      (puTrans h.le L (baseA _)).map (MulAut.conj g).toMonoidHom := puTrans_smul h.le hLn g _
  set W₀ := W.map (MulAut.conj g⁻¹).toMonoidHom with hW₀
  set Z₀ := Z.map (MulAut.conj g⁻¹).toMonoidHom with hZ₀
  have hmem : ∀ {K : Subgroup (puAmalgam h.le).Universal} {x : (puAmalgam h.le).Universal},
      x ∈ K.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ K := fun {K x} => by
    rw [mem_map_conj, inv_inv]
  have hW' : W₀ ≤ stab _ (baseA (puAmalgam h.le)) := by
    intro x hx
    rw [hmem] at hx
    have := hW hx
    rw [mem_stab_smul] at this
    simpa [mul_assoc] using this
  have hZ' : Z₀ ≤ stab _ (baseA (puAmalgam h.le)) := by
    intro x hx
    rw [hmem] at hx
    have := hZ hx
    rw [mem_stab_smul] at this
    simpa [mul_assoc] using this
  have hWn' : puTrans h.le L (baseA _) ≤
      Subgroup.normalizer (W₀ : Set (puAmalgam h.le).Universal) := by
    rw [hW₀, le_normalizer_map_conj_iff, inv_inv, ← hLt]
    exact hWn
  have hZn' : puTrans h.le L (baseA _) ≤
      Subgroup.normalizer (Z₀ : Set (puAmalgam h.le).Universal) := by
    rw [hZ₀, le_normalizer_map_conj_iff, inv_inv, ← hLt]
    exact hZn
  have hy' : g⁻¹ * y * g ∈ stab _ (baseA (puAmalgam h.le)) := (mem_stab_smul _).1 hy
  have hy2' : ∃ e : ℕ, (g⁻¹ * y * g) ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := hy2
    refine ⟨e, ?_⟩
    have : (g⁻¹ * y * g) ^ 2 ^ e = g⁻¹ * y ^ 2 ^ e * g := by
      rw [show g⁻¹ * y * g = (MulAut.conj g⁻¹) y by simp [mul_assoc], ← map_pow]
      simp [mul_assoc]
    rw [this, he]
    group
  have hyQ' : g⁻¹ * y * g ∉ Qv _ (baseA (puAmalgam h.le)) := by
    intro hq
    apply hyQ
    rw [qv_smul, mem_map_conj]
    exact hq
  have hyZ' : g⁻¹ * y * g ∈ Subgroup.normalizer (Z₀ : Set (puAmalgam h.le).Universal) := by
    rw [hZ₀, normalizer_map_conj, hmem]
    simpa [mul_assoc] using hyZ
  have hyW' : ∀ w ∈ W₀, (g⁻¹ * y * g) * w * (g⁻¹ * y * g)⁻¹ * w⁻¹ ∈ Z₀ := by
    intro w hw
    rw [hmem] at hw ⊢
    have e : g * ((g⁻¹ * y * g) * w * (g⁻¹ * y * g)⁻¹ * w⁻¹) * g⁻¹ =
        y * (g * w * g⁻¹) * y⁻¹ * (g * w * g⁻¹)⁻¹ := by group
    rw [e]
    exact hyW _ hw
  have key := S310.commutator_le_of_two_elt_baseA h hW' hZ' hWn' hZn' hy' hy2' hyQ' hyZ' hyW'
  have hmap := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) key
  rw [Subgroup.map_commutator, hW₀, hZ₀, map_conj_map_conj_inv, map_conj_map_conj_inv,
    ← hLt] at hmap
  exact hmap

theorem conj_eq_of_mem_centralizer (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a) {ρ : Vtx (puAmalgam h.le)}
    (hρ : IsMVtx _ ρ) {m u : (puAmalgam h.le).Universal} (hm : m ∈ stab _ ρ)
    (hu : u ∈ S5.uSub h.le L ρ)
    (hc : m * u * m⁻¹ * u⁻¹ ∈
      Subgroup.centralizer (puTrans h.le L ρ : Set (puAmalgam h.le).Universal)) :
    m * u * m⁻¹ = u := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hρ
  have hm' : g⁻¹ * m * g ∈ imM h.le M := by
    rw [← puAmalgam.stab_baseA]
    exact (mem_stab_smul _).1 hm
  obtain ⟨m₀, -, hm₀⟩ := hm'
  have hu' : g⁻¹ * u * g ∈ imM h.le (Uq M T L) := by
    rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, mem_map_conj] at hu
    exact hu
  obtain ⟨u₀, hu₀, hu₀e⟩ := hu'
  have hmu : m = g * (puAmalgam h.le).ofA m₀ * g⁻¹ := by rw [hm₀]; group
  have huu : u = g * (puAmalgam h.le).ofA u₀ * g⁻¹ := by rw [hu₀e]; group
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    le_normalizer_commutator (le_normalizer_Z0q M T) h.le_normalizer
  have hc₀U : ((m₀ * u₀ * m₀⁻¹ * u₀⁻¹ : ↥M) : G) ∈ Uq M T L := by
    have hu₀' : (u₀ : G) ∈ Uq M T L := Subgroup.mem_subgroupOf.1 hu₀
    have h1 : (m₀ : G) * u₀ * (m₀ : G)⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hUn m₀.2) _).1 hu₀'
    simpa using mul_mem h1 (inv_mem hu₀')
  have hcC : (puAmalgam h.le).ofA (m₀ * u₀ * m₀⁻¹ * u₀⁻¹) ∈
      Subgroup.centralizer (imM h.le L : Set (puAmalgam h.le).Universal) := by
    rw [puTrans_smul h.le hLn, S5B.puTrans_L_baseA h, PU.centralizer_map_mulEquiv,
      mem_map_conj] at hc
    have e : g⁻¹ * (m * u * m⁻¹ * u⁻¹) * g =
        (puAmalgam h.le).ofA (m₀ * u₀ * m₀⁻¹ * u₀⁻¹) := by
      rw [hmu, huu]
      simp only [map_mul, map_inv]
      group
    rw [e] at hc
    exact hc
  have hmem : (puAmalgam h.le).ofA (m₀ * u₀ * m₀⁻¹ * u₀⁻¹) ∈
      imM h.le (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [imM_inf_centralizer h.le _ h.L_le]
    exact ⟨⟨_, Subgroup.mem_subgroupOf.2 hc₀U, rfl⟩, hcC⟩
  obtain ⟨c₁, hc₁, hc₁e⟩ := hmem
  have hc₁eq : c₁ = m₀ * u₀ * m₀⁻¹ * u₀⁻¹ := (puAmalgam h.le).ofA_injective hc₁e
  have hcL : (m₀ : G) * u₀ * (m₀ : G)⁻¹ * (u₀ : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    have := (Subgroup.mem_subgroupOf.1 hc₁).2
    rw [hc₁eq] at this
    simpa using this
  have key := (sp4Lift_holds G M T L h k F _ _ a hd).2.2 m₀ m₀.2 u₀
    (Subgroup.mem_subgroupOf.1 hu₀) hcL
  have key' : m₀ * u₀ * m₀⁻¹ = u₀ := Subtype.ext (by simpa using key)
  rw [hmu, huu]
  have e : g * (puAmalgam h.le).ofA m₀ * g⁻¹ * (g * (puAmalgam h.le).ofA u₀ * g⁻¹) *
      (g * (puAmalgam h.le).ofA m₀ * g⁻¹)⁻¹ =
      g * (puAmalgam h.le).ofA (m₀ * u₀ * m₀⁻¹) * g⁻¹ := by
    simp only [map_mul, map_inv]
    group
  rw [e, key']

theorem relIndex_pCoreOf_le_M (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a) {E : Subgroup G}
    (hEM : E ≤ M) (hE2 : IsPGroup 2 E)
    (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) ≤ 2 ^ k) :
    (pCoreOf 2 M).relIndex E ≤ 2 ^ k := by
  have : CharP F 2 := S5B.charP_two_of_card hd.2.1
  by_cases hEO : E ≤ pCoreOf 2 M
  · rw [Subgroup.relIndex_eq_one.2 hEO]
    exact Nat.one_le_two_pow
  obtain ⟨p, hp, hfix⟩ := (S5B.relIndex_centralizer_M h hd hEM hE2 hEO).2 hrel
  have h3 : Module.finrank F (MSP.fixSp ((E.subgroupOf M).map a)) = 3 := by
    have h1 := MSP.finrank_perp p
    have h2 : Module.finrank F p = 1 := hp
    rw [hfix]
    omega
  obtain ⟨p', hp', -, hĒ⟩ := MSP.exists_point_of_finrank_fixSp_three h3
  have hker : a.ker ⊓ E.subgroupOf M = (pCoreOf 2 M).subgroupOf M ⊓ E.subgroupOf M := by
    ext z
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    refine ⟨fun hz => ⟨?_, hz.2⟩, fun hz => ⟨S310.map_eq_one_of_mem_pCoreOf hd.2.2.1 hz.1, hz.2⟩⟩
    obtain ⟨n, hn⟩ := hE2 ⟨z, hz.2⟩
    exact S5B.mem_pCoreOf_of_ker h hd hz.1 ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hcard : Nat.card ↥((E.subgroupOf M).map a) = (pCoreOf 2 M).relIndex E := by
    rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_right, hker,
      Subgroup.inf_relIndex_right, Subgroup.relIndex_subgroupOf hEM]
  rw [← hcard]
  calc Nat.card ↥((E.subgroupOf M).map a) ≤ Nat.card ↥(MSP.xPoint p') :=
        Subgroup.card_le_of_le hĒ
    _ = 2 ^ k := by rw [MSP.card_xPoint hp', Nat.card_eq_fintype_card, hd.2.1]

theorem relIndex_qv_le (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a) {ρ : Vtx (puAmalgam h.le)}
    (hρ : IsMVtx _ ρ) {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ stab _ ρ)
    (hE2 : IsPGroup 2 E)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L ρ) ≤ 2 ^ k) :
    (Qv _ ρ).relIndex E ≤ 2 ^ k := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hρ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  have hE₀2 : IsPGroup 2 E₀ := by
    have e1 : ↥E₀ ≃* ↥(imM h.le E₀) := by
      refine (Subgroup.subgroupOfEquivOfLe hE₀M).symm.trans ?_
      exact Subgroup.equivMapOfInjective _ _ (puAmalgam h.le).ofA_injective
    have e2 : ↥(imM h.le E₀) ≃* ↥((imM h.le E₀).map (MulAut.conj g).toMonoidHom) :=
      Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective
    exact hE2.of_equiv (e1.trans e2).symm
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  rw [qv_smul, S5B.qv_baseA_eq h,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S5B.relIndex_imM h.le hE₀M]
  exact relIndex_pCoreOf_le_M h hd hE₀M hE₀2 hrel

theorem card_commutator_ge (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a) {ρ : Vtx (puAmalgam h.le)}
    (hρ : IsMVtx _ ρ) {W : Subgroup (puAmalgam h.le).Universal} (hW : W ≤ stab _ ρ)
    (hUW : S5.uSub h.le L ρ ≤ W) {z : (puAmalgam h.le).Universal} (hzW : z ∈ W)
    (hz2 : IsPGroup 2 (Subgroup.zpowers z)) (hzQ : z ∉ Qv _ ρ)
    (hcard : Nat.card ↥⁅W, W⁆ ≤ 2 ^ k) :
    2 ^ k ≤ Nat.card ↥⁅W, W⁆ ∧
      ∀ c ∈ ⁅W, W⁆, c ∈ Subgroup.centralizer (puTrans h.le L ρ : Set (puAmalgam h.le).Universal) →
        c = 1 := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hz : z ∈ stab _ ρ := hW hzW
  have hUZ : S5.uSub h.le L ρ ≤ ZM _ ρ :=
    Subgroup.le_normalizer_iff_commutator_le_left.1
      ((puTrans_le_stab h.le L ρ).trans (stab_le_normalizer_zm _ ρ))
  have hZab := (isElemAbelian_zm _ hyp hb0 hρ).1
  have hUn : stab _ ρ ≤ Subgroup.normalizer (S5.uSub h.le L ρ : Set (puAmalgam h.le).Universal) :=
    le_normalizer_commutator (stab_le_normalizer_zm _ ρ) (stab_le_normalizer_puTrans h.le hLn ρ)
  have hcommU : ∀ u ∈ S5.uSub h.le L ρ, ∀ v ∈ S5.uSub h.le L ρ, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hZab.is_comm.comm ⟨u, hUZ hu⟩ ⟨v, hUZ hv⟩)
  have hzu : ∀ u ∈ S5.uSub h.le L ρ, z * u * z⁻¹ ∈ S5.uSub h.le L ρ := fun u hu =>
    (Subgroup.mem_normalizer_iff.1 (hUn hz) u).1 hu
  let φ : ↥(S5.uSub h.le L ρ) →* (puAmalgam h.le).Universal :=
    { toFun := fun u => z * u * z⁻¹ * (u : (puAmalgam h.le).Universal)⁻¹
      map_one' := by simp
      map_mul' := fun u v => by
        have hc := hcommU _ (mul_mem (hzu _ v.2) (inv_mem v.2)) _ (inv_mem u.2)
        simp only [Subgroup.coe_mul]
        calc z * (↑u * ↑v) * z⁻¹ * (↑u * ↑v)⁻¹ =
            z * ↑u * z⁻¹ * ((z * ↑v * z⁻¹ * (↑v)⁻¹) * (↑u)⁻¹) := by group
          _ = z * ↑u * z⁻¹ * ((↑u)⁻¹ * (z * ↑v * z⁻¹ * (↑v)⁻¹)) := by rw [hc]
          _ = z * ↑u * z⁻¹ * (↑u)⁻¹ * (z * ↑v * z⁻¹ * (↑v)⁻¹) := by group }
  have hker : φ.ker = (Subgroup.centralizer (Subgroup.zpowers z :
      Set (puAmalgam h.le).Universal)).subgroupOf (S5.uSub h.le L ρ) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure, Subgroup.mem_centralizer_singleton_iff]
    change z * u * z⁻¹ * (u : (puAmalgam h.le).Universal)⁻¹ = 1 ↔ _
    constructor
    · intro h1
      have : z * u * z⁻¹ = u := by
        have := congrArg (· * (u : (puAmalgam h.le).Universal)) h1
        simpa using this
      calc (u : (puAmalgam h.le).Universal) * z = z * u * z⁻¹ * z := by rw [this]
        _ = z * u := by group
    · intro h1
      rw [← h1]
      group
  have hrel : 2 ^ k ≤ Nat.card ↥φ.range := by
    have h1 := S5B.le_relIndex_centralizer h hd hρ
      ((Subgroup.zpowers_le (G := (puAmalgam h.le).Universal)).2 hz) hz2
      (fun hle => hzQ (hle (Subgroup.mem_zpowers z)))
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker] at h1
    exact h1
  have hfin : Finite ↥⁅W, W⁆ := by
    have := S310.finite_stab_of_isMVtx h hρ
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      ((commutator_le_of_le hW hW)))
  have hrange : φ.range ≤ ⁅W, W⁆ := by
    rintro _ ⟨u, rfl⟩
    change z * u * z⁻¹ * (u : (puAmalgam h.le).Universal)⁻¹ ∈ ⁅W, W⁆
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hzW (hUW u.2)
  have heq : φ.range = ⁅W, W⁆ :=
    Subgroup.eq_of_le_of_card_ge hrange (hcard.trans hrel)
  refine ⟨heq ▸ hrel, fun c hc hcL => ?_⟩
  rw [← heq] at hc
  obtain ⟨u, rfl⟩ := hc
  have key := conj_eq_of_mem_centralizer h hd hρ hz u.2 hcL
  change z * u * z⁻¹ * (u : (puAmalgam h.le).Universal)⁻¹ = 1
  rw [key, mul_inv_cancel]

theorem commutator_qv_eq_voSub (h : PUHyp M T L)
    (h0 : ⁅Qv _ (baseA (puAmalgam h.le)), puTrans h.le L (baseA _)⁆ =
      S5.voSub h.le L (baseA _))
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) :
    ⁅Qv _ ρ, puTrans h.le L ρ⁆ = S5.voSub h.le L ρ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hρ
  rw [qv_smul, puTrans_smul h.le hLn, S5B.voSub_smul h.le hLn, ← Subgroup.map_commutator, h0]

theorem commutator_voSub_le_dSub (h : PUHyp M T L)
    (h0 : ⁅S5.voSub h.le L (baseA (puAmalgam h.le)), S5.voSub h.le L (baseA _)⁆ ≤
      S5.dSub h.le L (baseA _))
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) :
    ⁅S5.voSub h.le L ρ, S5.voSub h.le L ρ⁆ ≤ S5.dSub h.le L ρ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hρ
  rw [S5B.voSub_smul h.le hLn, S5B.dSub_smul h.le hLn, ← Subgroup.map_commutator]
  exact Subgroup.map_mono h0

theorem voSub_le_sup_of_not_le (h : PUHyp M T L)
    (h0 : ∀ X : Subgroup (puAmalgam h.le).Universal, X ≤ S5.voSub h.le L (baseA _) →
      stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (X : Set _) →
      ¬ X ≤ S5.bSub h.le L (baseA _) →
      S5.voSub h.le L (baseA _) ≤ X ⊔ (S5.voSub h.le L (baseA _) ⊓ S5.bSub h.le L (baseA _)))
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) {X : Subgroup (puAmalgam h.le).Universal}
    (hX : X ≤ S5.voSub h.le L ρ) (hXn : stab _ ρ ≤ Subgroup.normalizer (X : Set _))
    (hXB : ¬ X ≤ S5.bSub h.le L ρ) :
    S5.voSub h.le L ρ ≤ X ⊔ (S5.voSub h.le L ρ ⊓ S5.bSub h.le L ρ) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hρ
  rw [S5B.voSub_smul h.le hLn] at hX ⊢
  rw [S5B.bSub_smul h.le hLn] at hXB ⊢
  rw [stab_smul] at hXn
  have hX₀ : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ S5.voSub h.le L (baseA _) := by
    rw [map_conj_le_iff, inv_inv]
    exact hX
  have hX₀n : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (X.map (MulAut.conj g⁻¹).toMonoidHom : Set _) := by
    rw [le_normalizer_map_conj_iff, inv_inv]
    exact hXn
  have hX₀B : ¬ X.map (MulAut.conj g⁻¹).toMonoidHom ≤ S5.bSub h.le L (baseA _) := by
    intro hle
    apply hXB
    rw [map_conj_le_iff, inv_inv] at hle
    exact hle
  have key := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (h0 _ hX₀ hX₀n hX₀B)
  rw [Subgroup.map_sup, map_conj_map_conj_inv,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective] at key
  exact key

end S310Q

end CFSG.Quasithin.MS93
