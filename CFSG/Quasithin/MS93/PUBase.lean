module

public import CFSG.Quasithin.MS93.PUAmalgam
public import CFSG.Quasithin.MS93.PUTrans

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Open

universe u

variable {G : Type u} [Group G]

namespace PU

theorem map_subtype_subgroupOf {M : Subgroup G} (K : Subgroup ↥M) :
    (K.map M.subtype).subgroupOf M = K :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective K

theorem omegaOneCenterOf_le (L : Subgroup G) : omegaOneCenterOf L ≤ L := by
  rw [omegaOneCenterOf, omegaOneOf, Subgroup.closure_le]
  exact fun x hx => hx.1.1

theorem omegaOneCenterOf_normal {H : Type*} [Group H] (L : Subgroup H) [hL : L.Normal] :
    (omegaOneCenterOf L).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hLg : L.map (MulAut.conj g).toMonoidHom = L := by
    ext y
    rw [mem_map_conj]
    constructor
    · intro hy
      convert hL.conj_mem _ hy g using 1
      group
    · intro hy
      convert hL.conj_mem _ hy g⁻¹ using 1
      group
  have h : (MulAut.conj g).toMonoidHom x ∈
      (omegaOneCenterOf L).map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rw [← omegaOneCenterOf_map (MulAut.conj g).injective, hLg] at h
  exact h

theorem omegaOneCenterOf_subgroupOf {M K : Subgroup G} (hK : K ≤ M) :
    (omegaOneCenterOf K).subgroupOf M = omegaOneCenterOf (K.subgroupOf M) := by
  conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hK]
  rw [omegaOneCenterOf_map M.subtype_injective, map_subtype_subgroupOf]

theorem inf_centralizer_subgroupOf {M : Subgroup G} (L : Subgroup ↥M) :
    (M ⊓ Subgroup.centralizer (L.map M.subtype : Set G)).subgroupOf M =
      Subgroup.centralizer (L : Set ↥M) := by
  have h := range_inf_centralizer_map M.subtype_injective L
  rw [Subgroup.range_subtype] at h
  rw [h, map_subtype_subgroupOf]

end PU

@[expose] def normalCoreIn (M T : Subgroup G) : Subgroup G :=
  ((T.subgroupOf M).normalCore).map M.subtype

@[expose] def normalClosureIn (M K : Subgroup G) : Subgroup G :=
  (Subgroup.normalClosure (K.subgroupOf M : Set ↥M)).map M.subtype

@[expose] def charClosureIn (T K : Subgroup G) : Subgroup G :=
  (⨆ φ : MulAut ↥T, (K.subgroupOf T).map φ.toMonoidHom).map T.subtype

section Closures

variable (M T K : Subgroup G)

theorem normalCoreIn_subgroupOf :
    (normalCoreIn M T).subgroupOf M = (T.subgroupOf M).normalCore :=
  PU.map_subtype_subgroupOf _

theorem normalCoreIn_normal : ((normalCoreIn M T).subgroupOf M).Normal := by
  rw [normalCoreIn_subgroupOf]
  infer_instance

theorem normalClosureIn_le : normalClosureIn M K ≤ M := Subgroup.map_subtype_le _

theorem normalClosureIn_subgroupOf :
    (normalClosureIn M K).subgroupOf M = Subgroup.normalClosure (K.subgroupOf M : Set ↥M) :=
  PU.map_subtype_subgroupOf _

theorem normalClosureIn_normal : ((normalClosureIn M K).subgroupOf M).Normal := by
  rw [normalClosureIn_subgroupOf]
  infer_instance

variable {M K} in
theorem le_normalClosureIn (hK : K ≤ M) : K ≤ normalClosureIn M K := by
  conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hK]
  exact Subgroup.map_mono Subgroup.subset_normalClosure

variable {M K} in
theorem normalClosureIn_le_of {N : Subgroup G} (hNM : N ≤ M) (hN : (N.subgroupOf M).Normal)
    (hKN : K ⊓ M ≤ N) : normalClosureIn M K ≤ N := by
  rw [← Subgroup.map_subgroupOf_eq_of_le hNM]
  exact Subgroup.map_mono (Subgroup.normalClosure_le_normal fun x hx => hKN ⟨hx, x.2⟩)

theorem charClosureIn_le : charClosureIn T K ≤ T := Subgroup.map_subtype_le _

theorem charClosureIn_subgroupOf :
    (charClosureIn T K).subgroupOf T = ⨆ φ : MulAut ↥T, (K.subgroupOf T).map φ.toMonoidHom :=
  PU.map_subtype_subgroupOf _

variable {T K} in
theorem le_charClosureIn (hK : K ≤ T) : K ≤ charClosureIn T K := by
  conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hK]
  refine Subgroup.map_mono (le_iSup_of_le 1 ?_)
  intro x hx
  exact ⟨x, hx, rfl⟩

theorem charClosureIn_characteristic : ((charClosureIn T K).subgroupOf T).Characteristic := by
  rw [charClosureIn_subgroupOf, Subgroup.characteristic_iff_map_le]
  intro ψ
  rw [Subgroup.map_iSup]
  refine iSup_le fun φ => le_iSup_of_le (ψ * φ) ?_
  rw [Subgroup.map_map]
  exact le_of_eq rfl

theorem omegaOneCenterOf_normalCoreIn_normal :
    ((omegaOneCenterOf (normalCoreIn M T)).subgroupOf M).Normal := by
  rw [normalCoreIn, PU.omegaOneCenterOf_map M.subtype_injective, PU.map_subtype_subgroupOf]
  exact PU.omegaOneCenterOf_normal _

end Closures

variable {T M : Subgroup G} (hTM : T ≤ M)

@[expose] def imM (K : Subgroup G) : Subgroup (puAmalgam hTM).Universal :=
  (K.subgroupOf M).map (puAmalgam hTM).ofA

@[expose] def puAmalgam.ofT : ↥T →* (puAmalgam hTM).Universal :=
  (puAmalgam hTM).ofB.comp SemidirectProduct.inl

theorem puAmalgam.ofA_inclusion (t : ↥T) :
    (puAmalgam hTM).ofA (Subgroup.inclusion hTM t) = puAmalgam.ofT hTM t :=
  ((puAmalgam hTM).ofA_toA t).trans ((puAmalgam hTM).ofB_toB t).symm

theorem imM_map_subtype (K : Subgroup ↥M) :
    imM hTM (K.map M.subtype) = K.map (puAmalgam hTM).ofA := by
  rw [imM, PU.map_subtype_subgroupOf]

theorem imM_mono {K K' : Subgroup G} (h : K ≤ K') : imM hTM K ≤ imM hTM K' :=
  Subgroup.map_mono fun _ hx => h hx

theorem imM_le_imM_iff {K K' : Subgroup G} (hK : K ≤ M) :
    imM hTM K ≤ imM hTM K' ↔ K ≤ K' := by
  refine ⟨fun h k hk => ?_, imM_mono hTM⟩
  obtain ⟨m, hm, he⟩ := h ⟨⟨k, hK hk⟩, hk, rfl⟩
  have : m = ⟨k, hK hk⟩ := (puAmalgam hTM).ofA_injective he
  subst this
  exact hm

theorem imM_inf (K K' : Subgroup G) : imM hTM (K ⊓ K') = imM hTM K ⊓ imM hTM K' := by
  rw [imM, imM, imM, ← Subgroup.map_inf _ _ _ (puAmalgam hTM).ofA_injective]
  rfl

theorem imM_eq_bot_iff {K : Subgroup G} (hK : K ≤ M) : imM hTM K = ⊥ ↔ K = ⊥ := by
  rw [imM, Subgroup.map_eq_bot_iff_of_injective _ (puAmalgam hTM).ofA_injective]
  constructor
  · intro h
    rw [← Subgroup.map_subgroupOf_eq_of_le hK, h, Subgroup.map_bot]
  · intro h
    rw [h]
    simp

theorem imM_of_le {K : Subgroup G} (hK : K ≤ T) :
    imM hTM K = (K.subgroupOf T).map (puAmalgam.ofT hTM) := by
  have h : K.subgroupOf M = (K.subgroupOf T).map (Subgroup.inclusion hTM) := by
    rw [PU.map_inclusion_eq_subgroupOf, Subgroup.map_subgroupOf_eq_of_le hK]
  rw [imM, h, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext (puAmalgam.ofA_inclusion hTM)

theorem imM_T :
    imM hTM T = (SemidirectProduct.inl : ↥T →* Hol ↥T).range.map (puAmalgam hTM).ofB := by
  rw [imM_of_le hTM le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, puAmalgam.ofT,
    MonoidHom.range_comp]

namespace puAmalgam

theorem stab_baseA : stab (puAmalgam hTM) (baseA _) = imM hTM M := by
  rw [stab, stabilizer_baseA, imM, Subgroup.subgroupOf_self, MonoidHom.range_eq_map]

theorem stab_baseB : stab (puAmalgam hTM) (baseB _) = (puAmalgam hTM).ofB.range :=
  stabilizer_baseB _

theorem stab_baseA_inf_stab_baseB :
    stab (puAmalgam hTM) (baseA _) ⊓ stab (puAmalgam hTM) (baseB _) = imM hTM T := by
  rw [stab, stab, stabilizer_baseA, stabilizer_baseB, GoldAmalgam.ofA_range_inf_ofB_range, imM]
  have h : Monoid.PushoutI.base (puAmalgam hTM).diagram =
      (puAmalgam hTM).ofA.comp (puAmalgam hTM).toA := by
    ext c
    exact ((puAmalgam hTM).ofA_toA c).symm
  rw [h, MonoidHom.range_comp]
  exact congrArg _ (puAmalgam_edgeA hTM)

theorem qv_baseB : Qv (puAmalgam hTM) (baseB _) = imM hTM T := by
  apply le_antisymm
  · rw [← stab_baseA_inf_stab_baseB]
    exact le_inf (PU.qv_le_stab_of_adj _ (adj_baseA_baseB _).symm) (PU.qv_le_stab _ _)
  · rw [imM_T]
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    rw [PU.mem_qv_iff]
    refine ⟨(PU.mem_stab_iff _).1 (by rw [stab_baseB]; exact ⟨_, rfl⟩), fun ρ hρ => ?_⟩
    obtain ⟨b, rfl⟩ := (adj_baseB_iff _ ρ).1 hρ
    rw [ofB_smul_inl, inl_ofB_eq_iff, puAmalgam_edgeB]
    have ht : (SemidirectProduct.inl t : Hol ↥T) ∈
        (SemidirectProduct.inl : ↥T →* Hol ↥T).range := ⟨t, rfl⟩
    have h := (Hol.range_inl_normal (K := ↥T)).conj_mem _ (inv_mem ht) b⁻¹
    convert h using 1
    group

theorem qv_baseA : Qv (puAmalgam hTM) (baseA _) = imM hTM (normalCoreIn M T) := by
  rw [normalCoreIn, imM_map_subtype]
  apply le_antisymm
  · intro g hg
    have hgA : g ∈ stab _ (baseA _) := PU.qv_le_stab _ _ hg
    rw [stab, stabilizer_baseA] at hgA
    obtain ⟨m, rfl⟩ := hgA
    refine ⟨m, fun b => ?_, rfl⟩
    have h := ((PU.mem_qv_iff _).1 hg).2 _ ((adj_baseA_iff _ _).2 ⟨b⁻¹, rfl⟩)
    rw [ofA_smul_inr, inr_ofA_eq_iff, puAmalgam_edgeA] at h
    have h2 : (b * m * b⁻¹)⁻¹ ∈ T.subgroupOf M := by
      convert h using 1
      group
    exact (Subgroup.inv_mem_iff _).1 h2
  · rintro _ ⟨c, hc, rfl⟩
    rw [PU.mem_qv_iff]
    refine ⟨(PU.mem_stab_iff _).1 (by rw [stab, stabilizer_baseA]; exact ⟨c, rfl⟩),
      fun ρ hρ => ?_⟩
    obtain ⟨a, rfl⟩ := (adj_baseA_iff _ ρ).1 hρ
    rw [ofA_smul_inr, inr_ofA_eq_iff, puAmalgam_edgeA]
    have h := (inv_mem hc) a⁻¹
    convert h using 1
    group

theorem zh_baseB : ZH (puAmalgam hTM) (baseB _) = imM hTM (omegaOneCenterOf T) := by
  rw [ZH, qv_baseB, imM, imM, PU.omegaOneCenterOf_subgroupOf hTM,
    PU.omegaOneCenterOf_map (puAmalgam hTM).ofA_injective]

theorem zm_baseA :
    ZM (puAmalgam hTM) (baseA _) = imM hTM (normalClosureIn M (omegaOneCenterOf T)) := by
  set X := puAmalgam hTM
  set Z : Subgroup ↥M := (omegaOneCenterOf T).subgroupOf M
  have hZH : ZH X (baseB X) = Z.map X.ofA := zh_baseB hTM
  rw [normalClosureIn, imM_map_subtype]
  apply le_antisymm
  · refine iSup₂_le fun ρ hρ => ?_
    obtain ⟨a, rfl⟩ := (adj_baseA_iff X ρ).1 hρ
    have hρ' : (Sum.inr ((X.ofA a : X.Universal) : X.Universal ⧸ X.ofB.range) : Vtx X) =
        X.ofA a • baseB X := (smul_baseB X _).symm
    rw [hρ', PU.zh_smul, hZH]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨a * z * a⁻¹, (inferInstance : (Subgroup.normalClosure (Z : Set ↥M)).Normal).conj_mem
      _ (Subgroup.subset_normalClosure hz) a, ?_⟩
    simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rfl
  · let W : Subgroup ↥M := (ZM X (baseA X)).comap X.ofA
    have hW : W.Normal := by
      refine ⟨fun w hw a => ?_⟩
      have hnorm := PU.stab_le_normalizer_of_smul X (PU.zm_smul X) (baseA X)
        (show X.ofA a ∈ stab X (baseA X) by rw [stab, stabilizer_baseA]; exact ⟨a, rfl⟩)
      show X.ofA (a * w * a⁻¹) ∈ ZM X (baseA X)
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hnorm _).1 hw
    have hZW : (Z : Set ↥M) ⊆ W := by
      intro z hz
      show X.ofA z ∈ ZM X (baseA X)
      have h1 : ZH X (baseB X) ≤ ZM X (baseA X) :=
        le_iSup₂ (f := fun ρ (_ : ρ ∈ X.treeGraph.neighborSet (baseA X)) => ZH X ρ) (baseB X)
          (adj_baseA_baseB X)
      exact h1 (hZH ▸ ⟨z, hz, rfl⟩)
    exact Subgroup.map_le_iff_le_comap.2 (Subgroup.normalClosure_le_normal hZW)

theorem xm_baseA :
    XM (puAmalgam hTM) (baseA _) = imM hTM (omegaOneCenterOf (normalCoreIn M T)) := by
  rw [XM, qv_baseA, normalCoreIn, imM_map_subtype, PU.omegaOneCenterOf_map M.subtype_injective,
    imM_map_subtype, PU.omegaOneCenterOf_map (puAmalgam hTM).ofA_injective]

theorem adj_baseB_iff_mulAut (w : Vtx (puAmalgam hTM)) :
    (puAmalgam hTM).treeGraph.Adj (baseB _) w ↔
      ∃ φ : MulAut ↥T, w = (puAmalgam hTM).ofB (SemidirectProduct.inr φ) • baseA _ := by
  rw [adj_baseB_iff]
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨b.right, ?_⟩
    rw [smul_baseA]
    show (Sum.inl (((puAmalgam hTM).ofB b : (puAmalgam hTM).Universal) :
        (puAmalgam hTM).Universal ⧸ (puAmalgam hTM).ofA.range) : Vtx (puAmalgam hTM)) =
      Sum.inl (((puAmalgam hTM).ofB (SemidirectProduct.inr b.right) :
        (puAmalgam hTM).Universal) : (puAmalgam hTM).Universal ⧸ (puAmalgam hTM).ofA.range)
    rw [inl_ofB_eq_iff, puAmalgam_edgeB, SemidirectProduct.range_inl_eq_ker_rightHom,
      MonoidHom.mem_ker]
    simp
  · rintro ⟨φ, rfl⟩
    exact ⟨SemidirectProduct.inr φ, smul_baseA _ _⟩

theorem zm_ofB_inr_smul_baseA (hZ : normalClosureIn M (omegaOneCenterOf T) ≤ T)
    (φ : MulAut ↥T) :
    ZM (puAmalgam hTM) ((puAmalgam hTM).ofB (SemidirectProduct.inr φ) • baseA _) =
      (((normalClosureIn M (omegaOneCenterOf T)).subgroupOf T).map φ.toMonoidHom).map
        (puAmalgam.ofT hTM) := by
  rw [PU.zm_smul, zm_baseA, imM_of_le hTM hZ, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext t
  simp only [MonoidHom.coe_comp, Function.comp_apply, puAmalgam.ofT, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, ← map_inv, ← map_mul]
  rw [← SemidirectProduct.inl_aut]
  rfl

theorem qv_smul_baseB (g : (puAmalgam hTM).Universal) :
    Qv (puAmalgam hTM) (g • baseB _) = (imM hTM T).map (MulAut.conj g).toMonoidHom := by
  rw [PU.qv_smul, qv_baseB]

end puAmalgam

include hTM in
theorem normalCoreIn_eq_pCoreOf [Finite G] (hT : IsPGroup 2 T) (hO : pCoreOf 2 M ≤ T) :
    normalCoreIn M T = pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold normalCoreIn pCoreOf
  congr 1
  apply le_antisymm
  · have hT' : IsPGroup 2 (T.subgroupOf M) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
    exact CFSG.LieType.BorelTits.le_pCore 2 (Subgroup.normalCore_normal _)
      (hT'.to_le (Subgroup.normalCore_le _))
  · have : (CFSG.Open.pCore 2 ↥M).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    rw [Subgroup.normal_le_normalCore]
    intro x hx
    exact hO ⟨x, hx, rfl⟩

theorem puAmalgam.qv_baseA_eq_pCoreOf [Finite G] (hT : IsPGroup 2 T) (hO : pCoreOf 2 M ≤ T) :
    Qv (puAmalgam hTM) (baseA _) = imM hTM (pCoreOf 2 M) := by
  rw [puAmalgam.qv_baseA, normalCoreIn_eq_pCoreOf hTM hT hO]

@[expose] noncomputable def puTrans (N : Subgroup G) (α : Vtx (puAmalgam hTM)) :
    Subgroup (puAmalgam hTM).Universal :=
  transN (puAmalgam hTM) (N.subgroupOf M) α

variable {hTM} in
theorem puTrans_smul_baseA {N : Subgroup G} (hN : (N.subgroupOf M).Normal)
    (g : (puAmalgam hTM).Universal) :
    puTrans hTM N (g • baseA _) = (imM hTM N).map (MulAut.conj g).toMonoidHom :=
  transN_smul_baseA _ _ g

theorem puTrans_baseA {N : Subgroup G} (hN : (N.subgroupOf M).Normal) :
    puTrans hTM N (baseA _) = imM hTM N :=
  transN_baseA _ _

theorem puTrans_smul {N : Subgroup G} (hN : (N.subgroupOf M).Normal)
    (h : (puAmalgam hTM).Universal) (α : Vtx (puAmalgam hTM)) :
    puTrans hTM N (h • α) = (puTrans hTM N α).map (MulAut.conj h).toMonoidHom :=
  transN_smul _ _ h α

theorem puTrans_le_stab (N : Subgroup G) (α : Vtx (puAmalgam hTM)) :
    puTrans hTM N α ≤ stab _ α :=
  transN_le_stab _ _ α

theorem stab_le_normalizer_puTrans {N : Subgroup G} (hN : (N.subgroupOf M).Normal)
    (α : Vtx (puAmalgam hTM)) :
    stab _ α ≤ Subgroup.normalizer (puTrans hTM N α : Set (puAmalgam hTM).Universal) :=
  stab_le_normalizer_transN _ _ α

theorem puTrans_normal {N : Subgroup G} (hN : (N.subgroupOf M).Normal) (α : Vtx (puAmalgam hTM)) :
    ((puTrans hTM N α).subgroupOf (stab _ α)).Normal :=
  transN_normal _ _ α

theorem puTrans_self {α : Vtx (puAmalgam hTM)} (hα : IsMVtx _ α) :
    puTrans hTM M α = stab _ α := by
  rw [puTrans, Subgroup.subgroupOf_self]
  exact transN_top _ hα

theorem puTrans_mono {N N' : Subgroup G} (h : N ≤ N') (α : Vtx (puAmalgam hTM)) :
    puTrans hTM N α ≤ puTrans hTM N' α :=
  transN_mono (puAmalgam hTM) (N := N.subgroupOf M) (N' := N'.subgroupOf M)
    (fun _ hx => h hx) α

theorem puTrans_inf (N N' : Subgroup G) (α : Vtx (puAmalgam hTM)) :
    puTrans hTM (N ⊓ N') α = puTrans hTM N α ⊓ puTrans hTM N' α :=
  transN_inf (puAmalgam hTM) (N.subgroupOf M) (N'.subgroupOf M) α

theorem qv_eq_puTrans {α : Vtx (puAmalgam hTM)} (hα : IsMVtx _ α) :
    Qv _ α = puTrans hTM (normalCoreIn M T) α := by
  obtain ⟨g, rfl⟩ := (PU.isMVtx_iff _).1 hα
  rw [PU.qv_smul, puAmalgam.qv_baseA, puTrans_smul_baseA (normalCoreIn_normal M T)]

theorem zm_eq_puTrans {α : Vtx (puAmalgam hTM)} (hα : IsMVtx _ α) :
    ZM _ α = puTrans hTM (normalClosureIn M (omegaOneCenterOf T)) α := by
  obtain ⟨g, rfl⟩ := (PU.isMVtx_iff _).1 hα
  rw [PU.zm_smul, puAmalgam.zm_baseA, puTrans_smul_baseA (normalClosureIn_normal M _)]

theorem xm_eq_puTrans {α : Vtx (puAmalgam hTM)} (hα : IsMVtx _ α) :
    XM _ α = puTrans hTM (omegaOneCenterOf (normalCoreIn M T)) α := by
  obtain ⟨g, rfl⟩ := (PU.isMVtx_iff _).1 hα
  rw [PU.xm_smul, puAmalgam.xm_baseA,
    puTrans_smul_baseA (omegaOneCenterOf_normalCoreIn_normal M T)]

end CFSG.Quasithin.MS93
