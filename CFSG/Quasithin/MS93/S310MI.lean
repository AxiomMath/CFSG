module

public import CFSG.Quasithin.MS93.S310MQ
public import CFSG.Quasithin.MS93.S5B58A

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

@[expose] def S310mQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → IsSp4Full M T L → critDist (puAmalgam h.le) = 4 →
    ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
          (a : ↥(stab (puAmalgam h.le) (baseA _)) →* ↥(StatedSp 2 F)),
        Fintype.card F = 2 ^ k → Function.Surjective a →
        IsSumOfNaturalModulesVia (stab _ (baseA _))
          (S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)))
          (S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)) ⊓ S5.bSub h.le L (baseA _))
          a false 1 →
        ⁅⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆,
            ⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆⁆ ≤
          S5.dSub h.le L (baseA _) →
        (S5.bSub h.le L (baseA _)).relIndex (ZM _ (geo _ (baseA _) α' 2)) ≤ 2 ^ k →
        (S5.bSub h.le L (geo _ (baseA _) α' 2)).relIndex (ZM _ α') ≤ 2 ^ k →
        (∃ g ∈ stab _ (geo _ (baseA _) α' 2), g • baseA (puAmalgam h.le) = α') →
        S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)) ≤ Qv _ (geo _ (baseA _) α' 2)

namespace S310

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section TV

theorem exists_mem_mul_pCoreOf_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E₀ Z₀ : Subgroup G} (hEM : E₀ ≤ M) (hE2 : IsPGroup 2 E₀) (hZE : Z₀ ≤ E₀)
    (hZO : ¬ Z₀ ≤ pCoreOf 2 M)
    (hrel : (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) ≤ 2 ^ k)
    (hZ : 2 ^ k ≤ (pCoreOf 2 M).relIndex Z₀) {x : ↥M} (hx : (x : G) ∈ E₀) :
    ∃ z : ↥M, (z : G) ∈ Z₀ ∧ ((z⁻¹ * x : ↥M) : G) ∈ pCoreOf 2 M := by
  have : CharP F 2 := S5B.charP_two_of_card hd.2.1
  have hEO : ¬ E₀ ≤ pCoreOf 2 M := fun hle => hZO (hZE.trans hle)
  obtain ⟨p, hp, hfix⟩ := (S5B.relIndex_centralizer_M h hd hEM hE2 hEO).2 hrel
  have h3 : Module.finrank F (MSP.fixSp ((E₀.subgroupOf M).map a)) = 3 := by
    have h1 := MSP.finrank_perp p
    have h2 : Module.finrank F p = 1 := hp
    rw [hfix]
    omega
  obtain ⟨p', hp', -, hĒ⟩ := MSP.exists_point_of_finrank_fixSp_three h3
  have hZĒ : (Z₀.subgroupOf M).map a ≤ (E₀.subgroupOf M).map a :=
    Subgroup.map_mono fun z hz => Subgroup.mem_subgroupOf.2 (hZE (Subgroup.mem_subgroupOf.1 hz))
  have hZM : Z₀ ≤ M := hZE.trans hEM
  have hker : a.ker ⊓ Z₀.subgroupOf M = (pCoreOf 2 M).subgroupOf M ⊓ Z₀.subgroupOf M := by
    ext z
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    refine ⟨fun hz => ⟨?_, hz.2⟩, fun hz => ⟨map_eq_one_of_mem_pCoreOf hd.2.2.1 hz.1, hz.2⟩⟩
    obtain ⟨n, hn⟩ := hE2 ⟨z, hZE hz.2⟩
    exact S5B.mem_pCoreOf_of_ker h hd hz.1 ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hcardZ : Nat.card ↥((Z₀.subgroupOf M).map a) = (pCoreOf 2 M).relIndex Z₀ := by
    rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_right, hker,
      Subgroup.inf_relIndex_right, Subgroup.relIndex_subgroupOf hZM]
  have hZX : (Z₀.subgroupOf M).map a = MSP.xPoint p' := by
    refine Subgroup.eq_of_le_of_card_ge (hZĒ.trans hĒ) ?_
    rw [MSP.card_xPoint hp', hcardZ, Nat.card_eq_fintype_card, hd.2.1]
    exact hZ
  have hax : a x ∈ (Z₀.subgroupOf M).map a := by
    rw [hZX]
    exact hĒ ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  obtain ⟨z, hz, hza⟩ := hax
  refine ⟨z, Subgroup.mem_subgroupOf.1 hz, ?_⟩
  refine S5B.mem_pCoreOf_of_ker h hd (by rw [map_mul, map_inv, hza, inv_mul_cancel]) ?_
  obtain ⟨n, hn⟩ := hE2 ⟨_, E₀.mul_mem (E₀.inv_mem (hZE (Subgroup.mem_subgroupOf.1 hz))) hx⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem exists_mem_mul_qv (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) {E Z : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ ρ) (hE2 : IsPGroup 2 E) (hZE : Z ≤ E) (hZQ : ¬ Z ≤ Qv _ ρ)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L ρ) ≤ 2 ^ k)
    (hZ : 2 ^ k ≤ (Qv _ ρ).relIndex Z) {x : (puAmalgam h.le).Universal} (hx : x ∈ E) :
    ∃ z ∈ Z, z⁻¹ * x ∈ Qv _ ρ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hρ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  obtain ⟨Z₀, hZ₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g (hZE.trans hE)
  obtain ⟨-, hZ₀O⟩ := S5B.isPGroup_not_le_of_smul h g hZ₀M (hE2.to_le hZE) hZQ
  obtain ⟨hE₀2, -⟩ := S5B.isPGroup_not_le_of_smul h g hE₀M hE2 fun hle => hZQ (hZE.trans hle)
  have hZE₀ : Z₀ ≤ E₀ := by
    rw [map_conj_le_map_conj_iff] at hZE
    exact (imM_le_imM_iff h.le hZ₀M).1 hZE
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  rw [qv_smul, S5B.qv_baseA_eq h,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S5B.relIndex_imM h.le hZ₀M] at hZ
  obtain ⟨_, ⟨e₀, he₀, rfl⟩, rfl⟩ := hx
  obtain ⟨z, hz, hze⟩ :=
    exists_mem_mul_pCoreOf_M h hd hE₀M hE₀2 hZE₀ hZ₀O hrel hZ (Subgroup.mem_subgroupOf.1 he₀)
  refine ⟨(MulAut.conj g).toMonoidHom ((puAmalgam h.le).ofA z),
    ⟨_, ⟨z, Subgroup.mem_subgroupOf.2 hz, rfl⟩, rfl⟩, ?_⟩
  rw [qv_smul, S5B.qv_baseA_eq h]
  refine ⟨(puAmalgam h.le).ofA (z⁻¹ * e₀), ⟨z⁻¹ * e₀, Subgroup.mem_subgroupOf.2 hze, rfl⟩, ?_⟩
  rw [map_mul, map_inv, map_mul, map_inv]

end TV

section Config

theorem exists_puTrans_mul_of_isMVtx (h : PUHyp M T L) {γ μ : Vtx (puAmalgam h.le)}
    (hγ : IsMVtx _ γ) (hγμ : (puAmalgam h.le).treeGraph.Adj γ μ)
    {g : (puAmalgam h.le).Universal} (hg : g ∈ stab _ γ) :
    ∃ l ∈ puTrans h.le L γ, ∃ t ∈ Qv _ μ, g = l * t := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g₀, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hγ
  have h1 : (puAmalgam h.le).treeGraph.Adj (baseA _) (g₀⁻¹ • μ) := by
    have := (adj_smul _ g₀⁻¹ _ _).2 hγμ
    rwa [inv_smul_smul] at this
  obtain ⟨l, hl, t, ht, he⟩ := S5B.exists_puTrans_mul h h1 ((mem_stab_smul _).1 hg)
  refine ⟨g₀ * l * g₀⁻¹, ?_, g₀ * t * g₀⁻¹, ?_, ?_⟩
  · rw [puTrans_smul h.le hLn]
    exact ⟨l, hl, rfl⟩
  · rw [show μ = g₀ • (g₀⁻¹ • μ) by rw [smul_inv_smul], qv_smul]
    exact ⟨t, ht, rfl⟩
  · calc g = g₀ * (g₀⁻¹ * g * g₀) * g₀⁻¹ := by group
      _ = g₀ * (l * t) * g₀⁻¹ := by rw [he]
      _ = g₀ * l * g₀⁻¹ * (g₀ * t * g₀⁻¹) := by group

theorem finite_stab_of_isMVtx (h : PUHyp M T L) {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    Finite ↥(stab _ α) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hα
  rw [stab_smul, puAmalgam.stab_baseA]
  have := S5B.finite_imM h.le M
  exact Finite.of_equiv _ (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv

theorem commutator_mem_zm (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hb : critDist (puAmalgam h.le) = 4) {α γ μ α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ α α') (hγ : IsMVtx _ γ) (hαγ : (puAmalgam h.le).treeGraph.dist α γ = 2)
    (hγμ : (puAmalgam h.le).treeGraph.Adj γ μ) (hμα' : (puAmalgam h.le).treeGraph.Adj μ α')
    (hA2 : (S5.bSub h.le L γ).relIndex (ZM _ α') ≤ 2 ^ k)
    (hA3 : ∃ g ∈ stab _ γ, g • α = α') {x : (puAmalgam h.le).Universal}
    (hx : x ∈ Qv _ α ⊓ Qv _ γ) {w : (puAmalgam h.le).Universal} (hw : w ∈ ZM _ α') :
    ⁅x, w⁆ ∈ ZM _ α := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα : IsMVtx _ α := hc.1
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hμ : ¬ IsMVtx _ μ := (isMVtx_iff_of_adj _ hγμ).1 hγ
  have hαμ : (puAmalgam h.le).treeGraph.dist α μ ≤ 3 := by
    have := dist_triangle _ α γ μ
    rw [hαγ, dist_eq_one_of_adj _ hγμ] at this
    exact this
  have hc' : IsCritical _ α' α := ms22_iii _ hyp hb0 h.centHyp hc
  have hZ'α : ZM _ α' ≤ stab _ α := zm_le_stab_of_isCritical _ hyp hb0 hc
  have hZα : ZM _ α ≤ stab _ α := (zm_le_qv_self _ hα hb0).trans (qv_le_stab _ _)
  have := finite_stab_of_isMVtx h hα
  have : Finite ↥(ZM (puAmalgam h.le) α') :=
    Finite.of_injective _ (Subgroup.inclusion_injective hZ'α)
  have : Finite ↥(ZM (puAmalgam h.le) α) := Finite.of_injective _ (Subgroup.inclusion_injective hZα)
  obtain ⟨g, hg, hgα⟩ := hA3
  obtain ⟨t, ht, s, hs, hts⟩ := exists_puTrans_mul_of_isMVtx h hγ hγμ (inv_mem hg)
  have htα' : t • α' = α := by
    have hsα' : s • α' = α' := (mem_stab _).1 (qv_le_stab_of_adj _ hμα' hs)
    have : g⁻¹ • α' = α := by rw [← hgα, inv_smul_smul]
    rw [← this, hts, mul_smul, hsα']
  have hEC : S5.bSub h.le L γ ⊓ ZM _ α' ≤
      Subgroup.centralizer ((Qv _ α ⊓ Qv _ γ : Subgroup _) : Set (puAmalgam h.le).Universal) := by
    rintro u ⟨huB, huZ⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨hyα, hyγ⟩
    have hcγ : ⁅u, t⁆ ∈ ZM _ γ := S5B.commutator_mem_zm_of_mem_bSub h (by omega) hγ huB ht
    have hzα : t * u * t⁻¹ ∈ ZM _ α := by
      rw [← htα', zm_smul]
      exact ⟨u, huZ, rfl⟩
    have h1 : y * ⁅u, t⁆ = ⁅u, t⁆ * y :=
      (Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hγ hcγ) y hyγ)
    have h2 : y * (t * u * t⁻¹) = (t * u * t⁻¹) * y :=
      (Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα hzα) y hyα)
    have e : u = ⁅u, t⁆ * (t * u * t⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e, ← mul_assoc, h1, mul_assoc ⁅u, t⁆ y, h2]
    exact (mul_assoc _ _ _).symm
  have hrel : (Subgroup.centralizer ((Qv _ α ⊓ Qv _ γ : Subgroup _) :
      Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L α') ≤ 2 ^ k := by
    calc (Subgroup.centralizer ((Qv _ α ⊓ Qv _ γ : Subgroup _) :
          Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L α')
        ≤ (Subgroup.centralizer ((Qv _ α ⊓ Qv _ γ : Subgroup _) :
          Set (puAmalgam h.le).Universal)).relIndex (ZM _ α') :=
          Subgroup.relIndex_le_of_le_right (S5B.uSub_le_zm h.le α')
            Subgroup.FiniteIndex.index_ne_zero
      _ ≤ (S5.bSub h.le L γ ⊓ ZM _ α').relIndex (ZM _ α') :=
          Subgroup.relIndex_le_of_le_left hEC Subgroup.FiniteIndex.index_ne_zero
      _ = (S5.bSub h.le L γ).relIndex (ZM _ α') := Subgroup.inf_relIndex_right _ _
      _ ≤ 2 ^ k := hA2
  have hZμ : ZM _ α' ≤ Qv _ μ :=
    zm_le_qv_of_dist_lt _ hα' (by rw [SimpleGraph.dist_comm, dist_eq_one_of_adj _ hμα', hb]; omega)
  have hZ'2 : IsPGroup 2 (ZM _ α') := (isPGroup_qv _ hyp hμ).to_le hZμ
  have hlow : 2 ^ k ≤ (Qv _ α').relIndex (ZM _ α) := by
    have h1 := S5B.le_relIndex_centralizer h hd hα hZ'α hZ'2 hc'.2.2
    have h2 : (Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal)).relIndex
          (S5.uSub h.le L α) ≤
        (Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal)).relIndex (ZM _ α) :=
      Subgroup.relIndex_le_of_le_right (S5B.uSub_le_zm h.le α) Subgroup.FiniteIndex.index_ne_zero
    have h3 : Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal) ⊓ ZM _ α =
        Qv _ α' ⊓ ZM _ α := by
      ext z
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hzc, hz⟩
        have hzμ : z ∈ Qv _ μ := zm_le_qv_of_dist_lt _ hα (by rw [hb]; omega) hz
        rw [← h.centHyp α' μ hα' hμα'.symm]
        exact ⟨⟨hzμ, hzc⟩, hz⟩
      · rintro ⟨hzQ, hz⟩
        refine ⟨Subgroup.mem_centralizer_iff.2 fun w hw => ?_, hz⟩
        exact ((Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα' hw)) z hzQ).symm
    rw [← Subgroup.inf_relIndex_right, ← h3, Subgroup.inf_relIndex_right]
    exact h1.trans h2
  have hEμ : Qv _ α ⊓ Qv _ γ ≤ Qv _ μ := inf_le_right.trans (qv_le_qv _ hyp hγ hγμ)
  have hEα' : Qv _ α ⊓ Qv _ γ ≤ stab _ α' := hEμ.trans (qv_le_stab_of_adj _ hμα')
  have hZE : ZM _ α ≤ Qv _ α ⊓ Qv _ γ := le_inf (zm_le_qv_self _ hα hb0)
    (zm_le_qv_of_dist_lt _ hα (by rw [hαγ, hb]; omega))
  obtain ⟨z, hz, hzx⟩ := exists_mem_mul_qv h hd hα' hEα' ((isPGroup_qv _ hyp hμ).to_le hEμ) hZE
    hc.2.2 hrel hlow hx
  have hq : (z⁻¹ * x) * w = w * (z⁻¹ * x) :=
    (Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα' hw)) _ hzx
  have e : ⁅x, w⁆ = z * (w * z⁻¹ * w⁻¹) := by
    have hx' : x = z * (z⁻¹ * x) := by group
    rw [hx', commutatorElement_def]
    calc z * (z⁻¹ * x) * w * (z * (z⁻¹ * x))⁻¹ * w⁻¹
        = z * ((z⁻¹ * x) * w) * (z⁻¹ * x)⁻¹ * z⁻¹ * w⁻¹ := by group
      _ = z * (w * (z⁻¹ * x)) * (z⁻¹ * x)⁻¹ * z⁻¹ * w⁻¹ := by rw [hq]
      _ = z * (w * z⁻¹ * w⁻¹) := by group
  rw [e]
  refine mul_mem hz ?_
  exact (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_zm _ _ (hZ'α hw)) _).1 (inv_mem hz)

theorem zm_le_bSub (h : PUHyp M T L) {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    ZM _ α ≤ S5.bSub h.le L α := by
  intro z hz
  refine Subgroup.subset_closure ⟨?_, fun y hy => ?_⟩
  · exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist α ρ ≤ 2}) => Zv (puAmalgam h.le) ρ) α (by simp)
      (zv_of_isMVtx _ hα).ge hz
  · have hyz : y * z⁻¹ * y⁻¹ ∈ ZM _ α :=
      (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_zm _ _ (puTrans_le_stab h.le L α hy))
        _).1 (inv_mem hz)
    have e : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hz hyz

theorem nclStab_le_qv (h : PUHyp M T L) {α γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hd : (puAmalgam h.le).treeGraph.dist α γ = 2) (hb : 2 < critDist (puAmalgam h.le)) :
    S5.nclStab _ α (ZM _ γ) ≤ Qv _ α := by
  refine iSup_le fun g => ?_
  rw [← zm_smul]
  have hgα : (g : (puAmalgam h.le).Universal) • α = α := (mem_stab _).1 g.2
  refine zm_le_qv_of_dist_lt _ ((isMVtx_smul _ _ _).2 hγ) ?_
  calc (puAmalgam h.le).treeGraph.dist ((g : (puAmalgam h.le).Universal) • γ) α =
      (puAmalgam h.le).treeGraph.dist ((g : (puAmalgam h.le).Universal) • γ)
        ((g : (puAmalgam h.le).Universal) • α) := by rw [hgα]
    _ = (puAmalgam h.le).treeGraph.dist γ α := dist_smul _ _ _ _
    _ < critDist (puAmalgam h.le) := by rw [SimpleGraph.dist_comm, hd]; exact hb

end Config

end S310

theorem s310mCore_of (hq : S310mQ) : S310mCore := by
  intro G _ _ M T L h hmin hfull hb α' hc k F _ _ a hF ha hnat hV₀ hA1 hA2 hA3
  have hVQ := hq G M T L h hmin hfull hb α' hc k F _ _ a hF ha hnat hV₀ hA1 hA2 hA3
  obtain ⟨k₀, F₀, _, _, a₀, hd⟩ := S5.isSp4Full_iff.1 hfull
  have hk : k = k₀ := S310.k_eq_of_nat h hd hF ha hnat
  subst hk
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb
  have hγ : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 2) := isMVtx_geo_two _ hyp hb0 hc
  have hαγ : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 2) =
      2 := dist_geo _ (by omega)
  have hγμ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) α' 2)
      (geo _ (baseA (puAmalgam h.le)) α' 3) := adj_geo _ (by omega)
  have hμα' : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) α' 3) α' := by
    have := adj_geo (puAmalgam h.le) (u := baseA _) (w := α') (i := 3) (by omega)
    rwa [show (3 + 1 : ℕ) = (puAmalgam h.le).treeGraph.dist (baseA _) α' by omega,
      geo_dist] at this
  have hVα := S310.nclStab_le_qv h hγ hαγ (by omega)
  refine le_trans ?_ (S310.zm_le_bSub h (isMVtx_baseA _))
  rw [Subgroup.commutator_le]
  intro x hx w hw
  exact S310.commutator_mem_zm h hd hb hc hγ hαγ hγμ hμα' hA2 hA3 ⟨hVα hx, hVQ hx⟩ hw

end CFSG.Quasithin.MS93
