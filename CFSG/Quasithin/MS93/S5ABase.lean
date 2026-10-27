module

public import CFSG.Quasithin.MS93.S5Stmt
public import CFSG.Quasithin.MS93.Sec2Basic

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S5

section RConj

variable {Γ : Type*} [Group Γ]

theorem mem_rconj {g x : Γ} {K : Subgroup Γ} : x ∈ rconj g K ↔ g * x * g⁻¹ ∈ K := by
  rw [rconj, mem_map_conj, inv_inv]

theorem rconj_mul (g h : Γ) (K : Subgroup Γ) : rconj (g * h) K = rconj h (rconj g K) := by
  rw [rconj, rconj, rconj, map_conj_map_conj, mul_inv_rev]

theorem rconj_one (K : Subgroup Γ) : rconj (1 : Γ) K = K := by
  rw [rconj, inv_one, map_conj_one]

theorem rconj_rconj_inv (g : Γ) (K : Subgroup Γ) : rconj g (rconj g⁻¹ K) = K := by
  rw [← rconj_mul, inv_mul_cancel, rconj_one]

theorem rconj_le_rconj_iff {g : Γ} {H K : Subgroup Γ} : rconj g H ≤ rconj g K ↔ H ≤ K :=
  map_conj_le_map_conj_iff _

theorem rconj_sup (g : Γ) (H K : Subgroup Γ) : rconj g (H ⊔ K) = rconj g H ⊔ rconj g K :=
  Subgroup.map_sup _ _ _

theorem rconj_eq_self_of_mem {g : Γ} {K : Subgroup Γ} (hg : g ∈ K) : rconj g K = K := by
  ext x
  rw [mem_rconj]
  constructor
  · intro hx
    have := K.mul_mem (K.mul_mem (inv_mem hg) hx) hg
    simpa [mul_assoc] using this
  · intro hx
    exact K.mul_mem (K.mul_mem hg hx) (inv_mem hg)

end RConj

section Equivariance

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem centralizer_conj_singleton (g t : X.Universal) :
    Subgroup.centralizer ({g * t * g⁻¹} : Set X.Universal) =
      (Subgroup.centralizer ({t} : Set X.Universal)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_map_conj, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx]
      _ = t * (g⁻¹ * x * g) := by group
  · intro hx
    calc x * (g * t * g⁻¹) = g * ((g⁻¹ * x * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by rw [hx]
      _ = g * t * g⁻¹ * x := by group

theorem isHatTriple_smul (g : X.Universal) (α α' : Vtx X) (t₁ t₂ t₃ : X.Universal) :
    IsHatTriple X (g • α) (g • α') (g * t₁ * g⁻¹) (g * t₂ * g⁻¹) (g * t₃ * g⁻¹) ↔
      IsHatTriple X α α' t₁ t₂ t₃ := by
  have hmem : ∀ (K : Subgroup X.Universal) (t : X.Universal),
      g * t * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom ↔ t ∈ K := fun K t => by
    rw [mem_map_conj]
    simp [mul_assoc]
  have hcl : ∀ s : Set X.Universal, Subgroup.closure ((fun t => g * t * g⁻¹) '' s) =
      (Subgroup.closure s).map (MulAut.conj g).toMonoidHom := fun s => by
    rw [MonoidHom.map_closure]
    rfl
  have hinj : ∀ H K : Subgroup X.Universal,
      H.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj g).toMonoidHom ↔ H = K :=
    fun H K => (Subgroup.map_injective (MulAut.conj g).injective).eq_iff
  have hri : ∀ (t : X.Universal) (K : Subgroup X.Universal),
      (Subgroup.centralizer ({g * t * g⁻¹} : Set X.Universal)).relIndex
          (K.map (MulAut.conj g).toMonoidHom) =
        (Subgroup.centralizer ({t} : Set X.Universal)).relIndex K := fun t K => by
    rw [centralizer_conj_singleton, Subgroup.relIndex_map_map_of_injective _ _
      (MulAut.conj g).injective]
  have hgeo : geo X (g • α') (g • α) 1 = g • geo X α' α 1 := geo_smul X g α' α 1
  have himg2 : (fun t => g * t * g⁻¹) '' ({t₁, t₂} : Set X.Universal) =
      {g * t₁ * g⁻¹, g * t₂ * g⁻¹} := by
    simp [Set.image_insert_eq, Set.image_singleton]
  have himg3 : (fun t => g * t * g⁻¹) '' ({t₁, t₂, t₃} : Set X.Universal) =
      {g * t₁ * g⁻¹, g * t₂ * g⁻¹, g * t₃ * g⁻¹} := by
    simp [Set.image_insert_eq, Set.image_singleton]
  have hR : critR X (g • α) (g • α') = (critR X α α').map (MulAut.conj g).toMonoidHom := by
    rw [critR, critR, zm_smul, zm_smul, Subgroup.map_commutator]
  rw [IsHatTriple, IsHatTriple, hgeo, qv_smul, zm_smul, zm_smul, qv_smul, ← himg2, ← himg3,
    hcl, hcl, hR, PU.centralizer_map_mulEquiv, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_sup, hinj, hinj,
    hmem, hmem, hmem, hri, hri, hri]
  have h12 : g * t₁ * g⁻¹ * (g * t₂ * g⁻¹)⁻¹ = g * (t₁ * t₂⁻¹) * g⁻¹ := by group
  rw [h12, hmem]

end Equivariance

section PUEquivariance

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M) {L : Subgroup G}
  (hL : (L.subgroupOf M).Normal)

include hL

theorem uSub_smul (g : (puAmalgam hTM).Universal) (δ : Vtx (puAmalgam hTM)) :
    uSub hTM L (g • δ) = (uSub hTM L δ).map (MulAut.conj g).toMonoidHom := by
  rw [uSub, uSub, zm_smul, puTrans_smul hTM hL, Subgroup.map_commutator]

omit hL in
theorem card_map_conj (g : (puAmalgam hTM).Universal) (E : Subgroup (puAmalgam hTM).Universal) :
    Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isOffCand_smul (q : ℕ) (g : (puAmalgam hTM).Universal) (γ ε : Vtx (puAmalgam hTM))
    (E : Subgroup (puAmalgam hTM).Universal) :
    IsOffCand hTM L q (g • γ) (g • ε) (E.map (MulAut.conj g).toMonoidHom) ↔
      IsOffCand hTM L q γ ε E := by
  rw [IsOffCand, IsOffCand, qv_smul, qv_smul, uSub_smul hTM hL, PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    map_conj_le_map_conj_iff]

theorem map_mem_offSet_smul (q : ℕ) (g : (puAmalgam hTM).Universal) (γ ε : Vtx (puAmalgam hTM))
    (E : Subgroup (puAmalgam hTM).Universal) :
    E.map (MulAut.conj g).toMonoidHom ∈ offSet hTM L q (g • γ) (g • ε) ↔
      E ∈ offSet hTM L q γ ε := by
  simp only [offSet, Set.mem_ofPred_eq]
  rw [isOffCand_smul hTM hL, card_map_conj]
  refine and_congr_right fun _ => ⟨fun h E' hE' => ?_, fun h E' hE' => ?_⟩
  · have := h (E'.map (MulAut.conj g).toMonoidHom) ((isOffCand_smul hTM hL q g γ ε E').2 hE')
    rwa [card_map_conj] at this
  · have hE'' : E' = (E'.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
      (map_conj_map_conj_inv E' g).symm
    rw [hE'', isOffCand_smul hTM hL] at hE'
    have := h _ hE'
    simpa only [card_map_conj] using this

theorem jOff_smul (q : ℕ) (g : (puAmalgam hTM).Universal) (γ ε : Vtx (puAmalgam hTM)) :
    jOff hTM L q (g • γ) (g • ε) = (jOff hTM L q γ ε).map (MulAut.conj g).toMonoidHom := by
  rw [jOff, jOff, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun E hE => ?_
    have hE' : E.map (MulAut.conj g⁻¹).toMonoidHom ∈ offSet hTM L q γ ε := by
      rw [← map_mem_offSet_smul hTM hL, map_conj_map_conj_inv]
      exact hE
    refine le_iSup_of_le (E.map (MulAut.conj g⁻¹).toMonoidHom) ?_
    rw [Subgroup.map_iSup]
    exact le_iSup_of_le hE' (le_of_eq (map_conj_map_conj_inv E g).symm)
  · refine iSup_le fun E => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hE => le_iSup₂_of_le _ ((map_mem_offSet_smul hTM hL q g γ ε E).2 hE) le_rfl

end PUEquivariance

section Base

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)

theorem imM_le_iff {K : Subgroup G} (hK : K ≤ M) {J : Subgroup (puAmalgam hTM).Universal} :
    imM hTM K ≤ J ↔ K ≤ (J.comap (puAmalgam hTM).ofA).map M.subtype := by
  constructor
  · intro hJ x hx
    exact ⟨⟨x, hK hx⟩, hJ ⟨⟨x, hK hx⟩, hx, rfl⟩, rfl⟩
  · rintro hJ _ ⟨m, hm, rfl⟩
    obtain ⟨m', hm', he⟩ := hJ hm
    have : m' = m := Subtype.ext he
    subst this
    exact hm'

theorem exists_eq_imM {K : Subgroup G} {E : Subgroup (puAmalgam hTM).Universal}
    (hE : E ≤ imM hTM K) : ∃ E₀ : Subgroup G, E₀ ≤ K ∧ E₀ ≤ M ∧ E = imM hTM E₀ := by
  refine ⟨(E.comap (puAmalgam hTM).ofA).map M.subtype, ?_, Subgroup.map_subtype_le _, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨m', hm', he⟩ := hE hm
    have : m' = m := (puAmalgam hTM).ofA_injective he
    subst this
    exact hm'
  · apply le_antisymm
    · intro x hx
      obtain ⟨m, -, rfl⟩ := hE hx
      exact ⟨m, ⟨m, hx, rfl⟩, rfl⟩
    · rw [imM_le_iff hTM (Subgroup.map_subtype_le _)]

theorem card_imM {E : Subgroup G} (hE : E ≤ M) : Nat.card (imM hTM E) = Nat.card E := by
  rw [imM, Subgroup.card_map_of_injective (puAmalgam hTM).ofA_injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv

theorem relIndex_imM {K E : Subgroup G} (hE : E ≤ M) :
    (imM hTM K).relIndex (imM hTM E) = K.relIndex E := by
  rw [imM, imM, Subgroup.relIndex_map_map_of_injective _ _ (puAmalgam hTM).ofA_injective,
    Subgroup.relIndex_subgroupOf hE]

theorem relIndex_centralizer_imM {U E : Subgroup G} (hU : U ≤ M) (hE : E ≤ M) :
    (Subgroup.centralizer (imM hTM E : Set (puAmalgam hTM).Universal)).relIndex (imM hTM U) =
      (Subgroup.centralizer (E : Set G)).relIndex U := by
  rw [← Subgroup.inf_relIndex_right, inf_comm, ← imM_inf_centralizer hTM U hE,
    relIndex_imM hTM hU, inf_comm, Subgroup.inf_relIndex_right]

variable {L : Subgroup G}

theorem puTrans_L_baseA [Finite G] (h : PUHyp M T L) :
    puTrans h.le L (baseA (puAmalgam h.le)) = imM h.le L :=
  puTrans_baseA h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer)

theorem qv_baseA_eq [Finite G] (h : PUHyp M T L) :
    Qv (puAmalgam h.le) (baseA _) = imM h.le (pCoreOf 2 M) :=
  puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le

theorem uSub_baseA [Finite G] (h : PUHyp M T L) :
    uSub h.le L (baseA (puAmalgam h.le)) = imM h.le (Uq M T L) := by
  rw [uSub, puAmalgam.zm_baseA, puTrans_L_baseA h, Uq,
    imM_commutator h.le (Z0q_le M T) h.L_le]

theorem dSub_baseA [Finite G] (h : PUHyp M T L) :
    dSub h.le L (baseA (puAmalgam h.le)) = imM h.le (Dq M L) := by
  rw [dSub, qv_baseA_eq h, puTrans_L_baseA h, Dq, imM_inf_centralizer h.le _ h.L_le]

theorem xm_baseA_eq [Finite G] (h : PUHyp M T L) :
    XM (puAmalgam h.le) (baseA _) = imM h.le (Xq M) := by
  rw [puAmalgam.xm_baseA, h.normalCoreIn_eq]

theorem stabCenter_baseA :
    stabCenter (puAmalgam hTM) (baseA _) = imM hTM (M ⊓ Subgroup.centralizer (M : Set G)) := by
  have hst := puAmalgam.stab_baseA hTM
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyA : (y : (puAmalgam hTM).Universal) ∈ imM hTM M := hst ▸ y.2
    obtain ⟨m, -, hm⟩ := hyA
    refine ⟨m, ⟨m.2, Subgroup.mem_centralizer_iff.2 fun n hn => ?_⟩, hm⟩
    have hn' : (puAmalgam hTM).ofA ⟨n, hn⟩ ∈ stab (puAmalgam hTM) (baseA _) := by
      rw [hst]
      exact ⟨⟨n, hn⟩, by simp, rfl⟩
    have hc := Subgroup.mem_center_iff.1 hy ⟨_, hn'⟩
    have hc' : (puAmalgam hTM).ofA ⟨n, hn⟩ * (puAmalgam hTM).ofA m =
        (puAmalgam hTM).ofA m * (puAmalgam hTM).ofA ⟨n, hn⟩ := by
      rw [hm]
      exact congrArg Subtype.val hc
    rw [← map_mul, ← map_mul] at hc'
    exact congrArg Subtype.val ((puAmalgam hTM).ofA_injective hc')
  · rintro ⟨m, ⟨-, hmC⟩, rfl⟩
    have hmA : (puAmalgam hTM).ofA m ∈ stab (puAmalgam hTM) (baseA _) := by
      rw [hst]
      exact ⟨m, by simp, rfl⟩
    refine ⟨⟨_, hmA⟩, Subgroup.mem_center_iff.2 fun y => ?_, rfl⟩
    have hyA : (y : (puAmalgam hTM).Universal) ∈ imM hTM M := hst ▸ y.2
    obtain ⟨n, -, hn⟩ := hyA
    apply Subtype.ext
    show (y : (puAmalgam hTM).Universal) * (puAmalgam hTM).ofA m =
      (puAmalgam hTM).ofA m * (y : (puAmalgam hTM).Universal)
    rw [← hn, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hmC n n.2)

@[expose] def IsOffCandM (M T L : Subgroup G) (q : ℕ) (E : Subgroup G) : Prop :=
  E ≤ T ∧ (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) ≤ (pCoreOf 2 M).relIndex E ∧
    (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) ≤ q ^ 2

@[expose] def offSetM (M T L : Subgroup G) (q : ℕ) : Set (Subgroup G) :=
  {E | IsOffCandM M T L q E ∧ ∀ E' : Subgroup G, IsOffCandM M T L q E' → Nat.card E' ≤ Nat.card E}

@[expose] def jOffM (M T L : Subgroup G) (q : ℕ) : Subgroup G := ⨆ E ∈ offSetM M T L q, E

variable [Finite G]

theorem isOffCand_imM (h : PUHyp M T L) (q : ℕ) {E : Subgroup G} (hE : E ≤ T) :
    IsOffCand h.le L q (baseA _) (baseB _) (imM h.le E) ↔ IsOffCandM M T L q E := by
  have hEM : E ≤ M := hE.trans h.le
  rw [IsOffCand, IsOffCandM, uSub_baseA h, qv_baseA_eq h, puAmalgam.qv_baseB,
    relIndex_centralizer_imM h.le (Uq_le h.L_le) hEM, relIndex_imM h.le hEM,
    imM_le_imM_iff h.le hEM]

theorem IsOffCand.exists_imM (h : PUHyp M T L) {q : ℕ} {E : Subgroup (puAmalgam h.le).Universal}
    (hE : IsOffCand h.le L q (baseA _) (baseB _) E) :
    ∃ E₀ : Subgroup G, E₀ ≤ T ∧ E = imM h.le E₀ ∧ IsOffCandM M T L q E₀ := by
  have hle : E ≤ imM h.le T := puAmalgam.qv_baseB h.le ▸ hE.1
  obtain ⟨E₀, hE₀T, -, rfl⟩ := exists_eq_imM h.le hle
  exact ⟨E₀, hE₀T, rfl, (isOffCand_imM h q hE₀T).1 hE⟩

theorem mem_offSet_imM (h : PUHyp M T L) (q : ℕ) {E : Subgroup G} (hE : E ≤ T) :
    imM h.le E ∈ offSet h.le L q (baseA _) (baseB _) ↔ E ∈ offSetM M T L q := by
  simp only [offSet, offSetM, Set.mem_ofPred_eq]
  rw [isOffCand_imM h q hE, card_imM h.le (hE.trans h.le)]
  refine and_congr_right fun _ => ⟨fun H E' hE' => ?_, fun H E' hE' => ?_⟩
  · have := H (imM h.le E') ((isOffCand_imM h q hE'.1).2 hE')
    rwa [card_imM h.le (hE'.1.trans h.le)] at this
  · obtain ⟨E₀, hE₀T, rfl, hE₀⟩ := hE'.exists_imM h
    rw [card_imM h.le (hE₀T.trans h.le)]
    exact H E₀ hE₀

omit [Finite G] in
theorem offSetM_le (q : ℕ) {E : Subgroup G} (hE : E ∈ offSetM M T L q) : E ≤ T := hE.1.1

theorem mem_offSet_baseA (h : PUHyp M T L) (q : ℕ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ∈ offSet h.le L q (baseA _) (baseB _)) :
    ∃ E₀ ∈ offSetM M T L q, E = imM h.le E₀ := by
  obtain ⟨E₀, hE₀T, rfl, -⟩ := hE.1.exists_imM h
  exact ⟨E₀, (mem_offSet_imM h q hE₀T).1 hE, rfl⟩

theorem jOff_baseA (h : PUHyp M T L) (q : ℕ) :
    jOff h.le L q (baseA _) (baseB _) = imM h.le (jOffM M T L q) := by
  have hJM : jOffM M T L q ≤ M := iSup₂_le fun E hE => (offSetM_le q hE).trans h.le
  apply le_antisymm
  · refine iSup₂_le fun E hE => ?_
    obtain ⟨E₀, hE₀, rfl⟩ := mem_offSet_baseA h q hE
    exact imM_mono h.le (le_iSup₂_of_le E₀ hE₀ le_rfl)
  · rw [imM_le_iff h.le hJM]
    refine iSup₂_le fun E₀ hE₀ => ?_
    have hE₀M : E₀ ≤ M := (offSetM_le q hE₀).trans h.le
    rw [← imM_le_iff h.le hE₀M]
    exact le_iSup₂_of_le (imM h.le E₀) ((mem_offSet_imM h q (offSetM_le q hE₀)).2 hE₀) le_rfl

theorem offSet_baseA (h : PUHyp M T L) (q : ℕ) :
    offSet h.le L q (baseA _) (baseB _) = imM h.le '' offSetM M T L q := by
  ext E
  constructor
  · intro hE
    obtain ⟨E₀, hE₀, rfl⟩ := mem_offSet_baseA h q hE
    exact ⟨E₀, hE₀, rfl⟩
  · rintro ⟨E₀, hE₀, rfl⟩
    exact (mem_offSet_imM h q (offSetM_le q hE₀)).2 hE₀

end Base

end S5

end CFSG.Quasithin.MS93
