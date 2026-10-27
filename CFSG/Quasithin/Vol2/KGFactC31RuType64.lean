module

public import CFSG.Quasithin.Vol2.KGFactC31RuM64
public import CFSG.Quasithin.Vol2.KGFactC31RuHyp
public import CFSG.Quasithin.Vol2.KGFactC31RuConcl
public import CFSG.Quasithin.Vol2.KGFactC31Ident
public import CFSG.Quasithin.Vol2.KGFactC31RuRefK

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Sporadic.RuSchreier
  CFSG.Quasithin.KGC31

variable {A : Type} [Group A]

section Facts


theorem ncard_u64_diff : ((u64 : Set (Equiv.Perm (Fin 4060))) \ {1}).ncard = 63 := by
  rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _), ← Nat.card_coe_set_eq]
  change Nat.card u64 - 1 = 63
  rw [card_refSub hv64]
  norm_num

theorem card_normalizer64_le :
    Nat.card ↥(ruP ⊓ Subgroup.normalizer (u64 : Set (Equiv.Perm (Fin 4060)))) ≤ 774144 := by
  set H := ruP ⊓ Subgroup.normalizer (u64 : Set (Equiv.Perm (Fin 4060))) with hH
  have h := card_le_of_conj_mem H ruZ (T := (u64 : Set (Equiv.Perm (Fin 4060))) \ {1})
    (Set.toFinite _) fun g hg => ⟨(Subgroup.mem_normalizer_iff.mp hg.2 ruZ).mp ruZ_mem_u64,
      fun h1 => ruZ_ne_one (by
        have : ruZ = g⁻¹ * (g * ruZ * g⁻¹) * g := by group
        rw [this, Set.mem_singleton_iff.mp h1]
        group)⟩
  have hC : H ⊓ Subgroup.centralizer {ruZ} = ruC ⊓
      Subgroup.normalizer (u64 : Set (Equiv.Perm (Fin 4060))) := by
    rw [ruC_eq_centralizer, hH]
    ext g
    simp only [Subgroup.mem_inf]
    tauto
  rw [ncard_u64_diff, hC] at h
  calc Nat.card H ≤ 63 * 12288 := h.trans (Nat.mul_le_mul_left _ card_ruC_normalizer64_le)
    _ = 774144 := by norm_num


theorem perf_N64 : ∀ K : Subgroup (Equiv.Perm (Fin 4060)),
    K ≤ ruP ⊓ Subgroup.normalizer (u64 : Set (Equiv.Perm (Fin 4060))) → ⁅K, K⁆ = K → K ≤ M64 :=
  perf_of_card (le_inf M64_le_ruP M64_le_normalizer)
    (by rw [card_M64]; exact card_normalizer64_le.trans (by norm_num))

theorem simple_M64 :
    IsSimpleGroup (↥M64 ⧸ u64.subgroupOf M64) :=
  SBc11.isSimpleGroup_of_list (Or.inr (Or.inr isPSU_M64))

theorem eq_of_M64_normal {W : Subgroup (Equiv.Perm (Fin 4060))} (hW : W ≤ u64)
    (hN : M64 ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 4060)))) (hne : W ≠ ⊥) :
    W = u64 := by
  obtain ⟨⟨w, hw⟩, hw1⟩ := W.ne_bot_iff_exists_ne_one.mp hne
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  refine le_antisymm hW fun u hu => ?_
  by_cases hu1 : u = 1
  · rw [hu1]
    exact W.one_mem
  obtain ⟨m₁, hm₁, hm₁e⟩ := exists_conj_t64 (hW hw) hw1'
  obtain ⟨m₂, hm₂, hm₂e⟩ := exists_conj_t64 hu hu1
  have e1 : u = (m₂ * m₁⁻¹) * w * (m₂ * m₁⁻¹)⁻¹ := by rw [← hm₂e, ← hm₁e]; group
  rw [e1]
  exact (Subgroup.mem_normalizer_iff.mp (hN (M64.mul_mem hm₂ (M64.inv_mem hm₁))) w).mp hw

end Facts

theorem mem_normalizer_sup {G : Type*} [Group G] {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

section Config

variable [Finite A]

theorem config_64 {M₀ R M V : Subgroup A} (h : RuHyp M₀ R M V) (e : G₀ ≃* A)
    {U : Subgroup (Equiv.Perm (Fin 4060))} (hU : U ≤ ruP) (hUV : img e U ≤ V)
    (hCU : ruP ⊓ Subgroup.centralizer (U : Set (Equiv.Perm (Fin 4060))) ≤ u64) :
    V = img e u64 ∧ pCoreOf 2 M₀ = img e u64 ∧ M₀ = img e M64 ∧ R = img e u64 ∧
      Subgroup.centralizer (V : Set A) = img e u64 := by
  obtain ⟨hVO, hOR, hRC, hNRM⟩ := h.facts
  set V' := pb e V with hV'
  set M₀' := pb e M₀ with hM₀'
  have hVP : V' ≤ ruP := pb_le e V
  have hUV' : U ≤ V' := (le_iff_img_le e hU).mp hUV
  have hVab : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a := by
    intro a ha b hb
    obtain ⟨haP, haV⟩ := (mem_pb e).mp ha
    obtain ⟨hbP, hbV⟩ := (mem_pb e).mp hb
    have := h.V_comm _ haV _ hbV
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (e.injective this)
  have h64ab : ∀ a ∈ u64, ∀ b ∈ u64, a * b = b * a := fun a ha b hb =>
    eSub_comm hv64 a b (by rwa [← refSub_eq]) (by rwa [← refSub_eq])
  have hV64 : V' ≤ u64 := fun v hv => hCU ⟨hVP hv,
    Subgroup.mem_centralizer_iff.mpr fun u hu => hVab u (hUV' hu) v hv⟩
  have hC : ruP ⊓ Subgroup.centralizer (V' : Set (Equiv.Perm (Fin 4060))) = u64 := by
    refine le_antisymm (fun c hc => hCU ⟨hc.1, Subgroup.centralizer_le hUV' hc.2⟩) ?_
    refine le_inf (refSub_le_ruP _) fun x hx => Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    exact h64ab v (hV64 hv) x hx
  have hCA : Subgroup.centralizer (V : Set A) = img e u64 := by
    conv_lhs => rw [← img_pb e V]
    rw [centralizer_img e hVP, hC]
  have hK2 : IsPGroup 2 ↥(img e u64) := by
    rw [img]
    refine IsPGroup.map ?_ _
    refine IsPGroup.of_card (n := 6) ?_
    rw [card_subgroupOf_of_le (refSub_le_ruP _), card_refSub hv64]
  have hR : R = img e u64 := by
    rw [h.R_eq (by rw [hCA]; exact hK2), hCA]
  have hM₀N : M₀' ≤ ruP ⊓ Subgroup.normalizer (u64 : Set (Equiv.Perm (Fin 4060))) := by
    rw [← img_le_iff_le_pb, ← normalizer_img e (refSub_le_ruP _), ← hR]
    exact h.M₀R
  have hM₀perf : ⁅M₀', M₀'⁆ = M₀' := pb_perfect e h.per
  have hM₀64 : M₀' ≤ M64 := perf_N64 M₀' hM₀N hM₀perf
  have hM64N : M64 ≤ Subgroup.normalizer (M₀' : Set (Equiv.Perm (Fin 4060))) := by
    have h1 : img e M64 ≤ Subgroup.normalizer (M₀ : Set A) := by
      refine le_trans ?_ hNRM
      rw [hR, normalizer_img e (refSub_le_ruP _), img_le_img_iff e M64_le_ruP]
      exact le_inf M64_le_ruP M64_le_normalizer
    rw [le_iff_img_le e M64_le_ruP, pb_normalizer] at h1
    exact h1.trans inf_le_right
  have hVne : V' ≠ ⊥ := pb_ne_bot e h.Vne
  have hVM₀ : V' ≤ M₀' := pb_mono e h.VM₀
  have hsup : M₀' ⊔ u64 = M64 := by
    have := simple_M64
    rcases forall_eq_of_simple this (M₀' ⊔ u64) le_sup_right (sup_le hM₀64 u64_le_M64)
      (fun m hm => mem_normalizer_sup (hM64N hm) (M64_le_normalizer hm)) with hs | hs
    · exfalso
      have hle : M₀' ≤ u64 := hs ▸ le_sup_left
      have hb : M₀' = ⊥ := by
        rw [← hM₀perf, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => h64ab y (hle hy) x (hle hx)
      exact hVne (le_bot_iff.mp (hb ▸ hVM₀))
    · exact hs
  have hinf : M₀' ⊓ u64 = u64 := by
    refine eq_of_M64_normal inf_le_right ?_ ?_
    · rw [← hsup]
      refine sup_le (fun m hm => mem_normalizer_inf (Subgroup.le_normalizer hm)
        (M64_le_normalizer (hM₀64 hm))) fun u hu => mem_normalizer_inf (hM64N (u64_le_M64 hu))
          (Subgroup.le_normalizer hu)
    · intro hb
      apply hVne
      exact le_bot_iff.mp (hb ▸ le_inf hVM₀ hV64)
  have hM₀eq : M₀' = M64 := by
    rw [← hsup]
    exact (sup_eq_left.mpr (hinf ▸ inf_le_left)).symm
  have hVeq : V' = u64 := by
    refine eq_of_M64_normal hV64 ?_ hVne
    rw [← hM₀eq]
    exact pb_le_normalizer e h.M₀V
  have hVA : V = img e u64 := (pb_eq_iff e (refSub_le_ruP _)).mpr hVeq
  refine ⟨hVA, le_antisymm (hOR.trans hR.le) (hVA ▸ hVO), (pb_eq_iff e M64_le_ruP).mpr hM₀eq, hR,
    hCA⟩

instance u64_normal_M64' : ((u64.subgroupOf ruP).subgroupOf (M64.subgroupOf ruP)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx ⊢
  have hg : (((g : G₀) : Equiv.Perm (Fin 4060))) ∈ M64 := g.2
  simpa using (Subgroup.mem_normalizer_iff.mp (M64_le_normalizer hg) _).mp hx

@[expose] noncomputable def quot64Equiv :
    (↥(M64.subgroupOf ruP) ⧸ ((u64.subgroupOf ruP).subgroupOf (M64.subgroupOf ruP))) ≃*
      (↥M64 ⧸ u64.subgroupOf M64) :=
  QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe M64_le_ruP) (by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hy
      exact hy
    · intro hx
      refine ⟨⟨⟨(x : Equiv.Perm (Fin 4060)), M64_le_ruP x.2⟩, x.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hx)

theorem concl_64 {S M₀ R M V : Subgroup A} (hSs : IsSporadic .Ru ↥S)
    (hcS : Subgroup.center ↥S = ⊥) (hM₀S : M₀ ≤ S) (h : RuHyp M₀ R M V) (e : G₀ ≃* A)
    {U : Subgroup (Equiv.Perm (Fin 4060))} (hU : U ≤ ruP) (hUV : img e U ≤ V)
    (hCU : ruP ⊓ Subgroup.centralizer (U : Set (Equiv.Perm (Fin 4060))) ≤ u64) :
    Concl S M₀ R M V := by
  obtain ⟨hV, hO, hM, -, hCA⟩ := config_64 h e hU hUV hCU
  have hvP : ∀ i, v64 i ∈ ruP := fun i => vOf_mem _ _ i
  have hv := liftV_basis hvP hv64
  have hE : eSub hv = u64.subgroupOf ruP := eSub_liftV hvP hv64
  have hUM : eSub hv ≤ M64.subgroupOf ruP := by
    rw [hE]
    exact fun x hx => u64_le_M64 hx
  have hn : ((eSub hv).subgroupOf (M64.subgroupOf ruP)).Normal := by
    rw [hE]
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx ⊢
    have hg : (((g : G₀) : Equiv.Perm (Fin 4060))) ∈ M64 := g.2
    simpa using (Subgroup.mem_normalizer_iff.mp (M64_le_normalizer hg) _).mp hx
  have hq : (eSub hv).subgroupOf (M64.subgroupOf ruP) =
      (u64.subgroupOf ruP).subgroupOf (M64.subgroupOf ruP) := by rw [hE]
  let e1 : (↥(M64.subgroupOf ruP) ⧸ (eSub hv).subgroupOf (M64.subgroupOf ruP)) ≃*
      (↥(M64.subgroupOf ruP) ⧸ (u64.subgroupOf ruP).subgroupOf (M64.subgroupOf ruP)) :=
    QuotientGroup.quotientMulEquivOfEq hq
  have hpsu : IsPSU 3 3 1 (↥(M64.subgroupOf ruP) ⧸ (eSub hv).subgroupOf (M64.subgroupOf ruP)) :=
    C31Spor.isPSU_of_mulEquiv (e1.trans quot64Equiv).symm isPSU_M64
  have ht : t64 ∈ ruP := wG_mem _
  have htrans : ∀ u ∈ eSub hv, u ≠ 1 → ∃ m ∈ M64.subgroupOf ruP, m * ⟨t64, ht⟩ * m⁻¹ = u := by
    intro u hu hu1
    rw [hE, Subgroup.mem_subgroupOf] at hu
    obtain ⟨m, hm, hme⟩ := exists_conj_t64 hu (fun h1 => hu1 (Subtype.ext h1))
    exact ⟨⟨m, M64_le_ruP hm⟩, hm, Subtype.ext (by simpa using hme)⟩
  have hVe : V = (eSub hv).map e.toMonoidHom := by rw [eSub_liftV_map e hvP hv64]; exact hV
  exact concl_G2 hSs hcS hM₀S h.per h.MN h.comm e.toMonoidHom e.injective hv hUM hpsu htrans
    hVe (by rw [← hVe]; exact hO.trans hV.symm) hM (by rw [hCA, ← hV]; exact inf_le_right)

end Config

end CFSG.Quasithin.KGC31.Ru

end
