module

public import CFSG.Quasithin.EmptyFaithful.S14610Q2
public import CFSG.Quasithin.EmptyFaithful.ModBA7Perm
public import CFSG.Quasithin.EmptyFaithful.ModBR4Core
public import CFSG.Quasithin.EmptyFaithful.ModBR4Syl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open scoped commutatorElement IsMulCommutative Pointwise

namespace ModB

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isShort_of_alt {T M : Subgroup G} {I I₂ K : Subgroup G} (hK : Concl14610List T M I I₂ K)
    (hA : IsAlt 6 (OTwoQuot K) ∨ IsAlt 7 (OTwoQuot K)) : IsShort2 K := by
  rcases hK.shape with ⟨hL32, -⟩ | ⟨hb, -⟩
  · exfalso
    have h2 : Nat.card (OTwoQuot K) = 168 := card_eq_168_of_isPSL_three_two hL32
    rcases hA with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have h1 : Nat.card (OTwoQuot K) = 360 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
        simp [Nat.factorial]
      omega
    · have h1 : Nat.card (OTwoQuot K) = 2520 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
        simp [Nat.factorial]
      omega
  · exact hb.1

theorem card_smul_subgroup {W : Type*} [CommGroup W] (σ : MulAut W) (X : Subgroup W) :
    Nat.card ↥(σ • X) = Nat.card ↥X := by
  rw [Subgroup.pointwise_smul_def]
  exact Subgroup.card_map_of_injective σ.injective

theorem relIndex_dvd_three_of_sylow {X I₂ I : Subgroup G} (hX : IsSylowTwoOf X I) (hXI₂ : X ≤ I₂)
    (hI₂I : I₂ ≤ I) (hs3 : Nonempty (OTwoQuot I₂ ≃* Equiv.Perm (Fin 3))) : X.relIndex I₂ ∣ 3 := by
  obtain ⟨e⟩ := hs3
  have h1 : X.relIndex I₂ * I₂.relIndex I = X.relIndex I := Subgroup.relIndex_mul_relIndex X I₂ I hXI₂ hI₂I
  have hdvdI : X.relIndex I₂ ∣ X.relIndex I := ⟨I₂.relIndex I, h1.symm⟩
  have hodd : ¬ 2 ∣ X.relIndex I₂ := fun h => hX.2.2 (h.trans hdvdI)
  have hq : Nat.card (OTwoQuot I₂) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hpc : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥I₂) :=
    CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥I₂) 2
  obtain ⟨b, hb⟩ := hpc.exists_card_eq
  have hI₂card : Nat.card ↥I₂ = 6 * 2 ^ b := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥I₂)
    rw [hb] at this
    have hq' : Nat.card (↥I₂ ⧸ CFSG.Open.pCore 2 ↥I₂) = 6 := hq
    rw [hq'] at this
    exact this
  obtain ⟨a, ha⟩ := hX.2.1.exists_card_eq
  have h2 : X.relIndex I₂ * Nat.card ↥X = Nat.card ↥I₂ := by
    have := Subgroup.relIndex_mul_card (H := X) (K := I₂)
    rwa [inf_of_le_left hXI₂] at this
  rw [ha, hI₂card] at h2
  have h3 : X.relIndex I₂ ∣ 2 ^ (b + 1) * 3 := by
    refine ⟨2 ^ a, ?_⟩
    calc 2 ^ (b + 1) * 3 = 6 * 2 ^ b := by ring
      _ = X.relIndex I₂ * 2 ^ a := h2.symm
  have hcop : Nat.Coprime (X.relIndex I₂) (2 ^ (b + 1)) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm
  exact hcop.dvd_of_dvd_mul_left h3

theorem rank4U_of_sylow {T M H : Subgroup G} {u : G} {I I₂ K : Subgroup G}
    (c : Facts14610 T M H u I I₂) (hK : Concl14610List T M I I₂ K) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hA : IsAlt 6 (OTwoQuot K) ∨ IsAlt 7 (OTwoQuot K)) (hW : Nat.card (wOf1469 K) = 2 ^ 4) :
    Nat.card (conjClosure (VZ T M) I₂) ≤ 2 ^ 3 := by
  classical
  have S : Setting146 G T M := c.setting
  have hshort : IsShort2 K := isShort_of_alt hK hA
  have hWeq : wOf1469 K = blockU K := wOf1469_eq_blockU_of_short hshort
  rw [hWeq] at hW
  have hVW : VZ T M ≤ blockU K := hWeq ▸ hK.v_le_w
  have hI₂I : I₂ ≤ I := c.gen ▸ le_sup_right
  have hTI₂ : T ⊓ I ≤ I₂ := c.le_I₂
  have hUQ : blockU K ≤ blockQ K ⊓ Subgroup.centralizer (blockQ K : Set G) := hshort.2.2.1.1
  have hUQ' : blockU K ≤ blockQ K := hUQ.trans inf_le_left
  have hcomm' : ∀ a ∈ blockU K, ∀ b ∈ blockU K, a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.mp (hUQ ha).2) b (hUQ' hb)).symm
  have : IsMulCommutative ↥(blockU K) := ⟨⟨fun a b => Subtype.ext (hcomm' a a.2 b b.2)⟩⟩
  have hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (blockU K : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      ((Subgroup.mem_centralizer_iff.mp (hUQ hx).2) q hq).symm
  have hKW : K ≤ Subgroup.normalizer (blockU K : Set G) := C1.le_normalizer_blockU K
  have hIW : I ≤ Subgroup.normalizer (blockU K : Set G) := fun g hg =>
    C1.mem_normalizer_blockU (hK.normal hg)
  have hsq : ∀ w : ↥(blockU K), w ^ 2 = 1 := fun w => Subtype.ext (hshort.2.2.1.2 w w.2)
  have hne : ¬ K ≤ Subgroup.centralizer (blockU K : Set G) := by
    intro h
    have hbot : ⁅blockU K, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)
    rw [C1.commutator_blockU hshort] at hbot
    rw [hbot] at hW
    simp at hW
  have hiso : Nonempty (↥(autOn K (blockU K)) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥(autOn K (blockU K)) ≃* alternatingGroup (Fin 7)) := by
    rcases hA with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · left
      have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact H13.nonempty_autOn_mulEquiv_of_simple hKW hO2 hne
        ((QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).trans e)
    · right
      have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      exact H13.nonempty_autOn_mulEquiv_of_simple hKW hO2 hne
        ((QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).trans e)
  let β : ↥I →* MulAut ↥(blockU K) := A4.actionOn (blockU K) I hIW
  have hβ : ∀ (g : ↥I) (w : ↥(blockU K)), ((β g w : ↥(blockU K)) : G) = (g : G) * w * (g : G)⁻¹ :=
    fun g w => rfl
  let K'' : Subgroup ↥I := K.subgroupOf I
  let T'' : Subgroup ↥I := (T ⊓ I).subgroupOf I
  let I₂'' : Subgroup ↥I := I₂.subgroupOf I
  have hK''N : K''.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hK.le).2 hK.normal
  have hKT : K'' ⊔ T'' = ⊤ := by
    have h1 : K ⊔ (T ⊓ I) = I := hK.eq_sup.symm
    rw [← Subgroup.subgroupOf_sup hK.le inf_le_right, h1, Subgroup.subgroupOf_self]
  have hKb : autOn K (blockU K) = K''.map β := by
    ext a
    rw [A4.mem_autOn_iff hKW, Subgroup.mem_map]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨(k : G), hK.le k.2⟩, k.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), hy⟩, rfl⟩
  have hiso' : Nonempty (↥(K''.map β) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥(K''.map β) ≃* alternatingGroup (Fin 7)) := by
    rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl ⟨(MulEquiv.subgroupCongr hKb.symm).trans e⟩
    · exact Or.inr ⟨(MulEquiv.subgroupCongr hKb.symm).trans e⟩
  have hcardKb : ∃ o, Odd o ∧ Nat.card ↥(K''.map β) = 8 * o := by
    rcases hiso' with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · refine ⟨45, ⟨22, by norm_num⟩, ?_⟩
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    · refine ⟨315, ⟨157, by norm_num⟩, ?_⟩
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
  have hT2 : IsPGroup 2 ↥T'' :=
    hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm
  have hTi : ¬ 2 ∣ T''.index := hsyl.2.2
  obtain ⟨o, ho, hKo⟩ := hcardKb
  have h8 := card_inf_map_ge β K'' T'' hKT hT2 hTi ho hKo
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    have hne' : quasithinOmegaOneCenter T ≠ ⊥ := by
      intro hbot
      have := S.card_Z
      rw [hbot, Subgroup.card_bot] at this
      omega
    obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
    exact ⟨z, z.2, fun h => hz (Subtype.ext h)⟩
  have hzV : z ∈ VZ T M := le_conjClosure _ _ hzZ
  have hH : H ≤ mcOf T := S.le_mcOf c.hH
  have hzc : ∀ g ∈ I₂, g * z * g⁻¹ = z := by
    intro g hg
    have hg' : g ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := hH (c.I₂_le hg)
    have h1 := (Subgroup.mem_centralizer_iff.mp hg') z hzZ
    calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
      _ = (z * g) * g⁻¹ := by rw [h1]
      _ = z := by group
  let z' : ↥(blockU K) := ⟨z, hVW hzV⟩
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  let V' : Subgroup ↥(blockU K) := (VZ T M).subgroupOf (blockU K)
  have hV'4 : Nat.card ↥V' = 4 := by
    have : Nat.card ↥V' = Nat.card ↥(VZ T M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW).toEquiv
    rw [this]
    exact S.hyp.rank_two
  have hz'V : z' ∈ V' := hzV
  have hTM : T ≤ M := S.hyp1281.inM.2
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hTfix : ∀ g : ↥I, (g : G) ∈ T → β g • V' = V' := by
    intro g hg
    have hmem : ∀ (g : ↥I), (g : G) ∈ T → ∀ v : ↥(blockU K), v ∈ V' → β g v ∈ V' := by
      intro g hg v hv
      have hv' : (v : G) ∈ VZ T M := hv
      show ((β g v : ↥(blockU K)) : G) ∈ VZ T M
      rw [hβ]
      exact (Subgroup.mem_normalizer_iff.mp (hMV (hTM hg)) (v : G)).mp hv'
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hmem g hg v hv
    · intro hx
      refine ⟨β g⁻¹ x, hmem g⁻¹ (inv_mem hg) x hx, ?_⟩
      show (β g) ((β g⁻¹) x) = x
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
  have hβz : ∀ g : ↥I, (g : G) ∈ I₂ → β g z' = z' := by
    intro g hg
    apply Subtype.ext
    rw [hβ]
    exact hzc g hg
  let act : MulAction ↥I₂'' (Subgroup ↥(blockU K)) := MulAction.compHom _ (β.comp I₂''.subtype)
  have hact : ∀ (g : ↥I₂'') (X : Subgroup ↥(blockU K)), g • X = β (g : ↥I) • X := fun g X => rfl
  let 𝒪 : Set (Subgroup ↥(blockU K)) := MulAction.orbit ↥I₂'' V'
  have hmemO : ∀ X, X ∈ 𝒪 ↔ ∃ g : ↥I₂'', β (g : ↥I) • V' = X := fun X => Iff.rfl
  have hstab : T''.subgroupOf I₂'' ≤ MulAction.stabilizer ↥I₂'' V' := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    have hgT : ((g : ↥I) : G) ∈ T ⊓ I := hg
    show β (g : ↥I) • V' = V'
    exact hTfix _ hgT.1
  have hidx : (T''.subgroupOf I₂'').index ∣ 3 := by
    have h1 : (T''.subgroupOf I₂'').index = (T ⊓ I).relIndex I₂ :=
      Subgroup.relIndex_subgroupOf (H := T ⊓ I) (K := I₂) (L := I) hI₂I
    rw [h1]
    exact relIndex_dvd_three_of_sylow hsyl hTI₂ hI₂I c.s3
  have h𝒪 : 𝒪.ncard ≤ 3 := by
    have h1 : (MulAction.stabilizer ↥I₂'' V').index = Nat.card (MulAction.orbit ↥I₂'' V') :=
      MulAction.index_stabilizer ↥I₂'' V'
    have h2 : (MulAction.stabilizer ↥I₂'' V').index ∣ 3 :=
      (Subgroup.index_dvd_of_le hstab).trans hidx
    have h3 : Nat.card ↥𝒪 = 𝒪.ncard := Nat.card_coe_set_eq 𝒪
    have h4 : Nat.card (MulAction.orbit ↥I₂'' V') ≤ 3 := h1 ▸ Nat.le_of_dvd (by norm_num) h2
    rw [← h3]
    exact h4
  have hzX : ∀ X ∈ 𝒪, z' ∈ X := by
    intro X hX
    obtain ⟨g, rfl⟩ := (hmemO X).1 hX
    have h1 := Subgroup.smul_mem_pointwise_smul z' (β (g : ↥I)) V' hz'V
    have h2 : β (g : ↥I) z' = z' := hβz _ g.2
    have h3 : (β (g : ↥I)) • z' = z' := by rw [MulAut.smul_def]; exact h2
    rw [h3] at h1
    exact h1
  have hX4 : ∀ X ∈ 𝒪, Nat.card ↥X = 4 := by
    intro X hX
    obtain ⟨g, rfl⟩ := (hmemO X).1 hX
    rw [card_smul_subgroup]
    exact hV'4
  have hT''I₂ : ∀ t : ↥I, t ∈ T'' → ((t : ↥I) : G) ∈ I₂ := fun t ht => hTI₂ ht
  have hOS : ∀ s ∈ K''.map β ⊓ T''.map β, ∀ X ∈ 𝒪, s • X ∈ 𝒪 := by
    intro s hs X hX
    obtain ⟨g, rfl⟩ := (hmemO X).1 hX
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs.2
    refine (hmemO _).2 ⟨⟨t, hT''I₂ t ht⟩ * g, ?_⟩
    have e : (((⟨t, hT''I₂ t ht⟩ * g : ↥I₂'') : ↥I)) = t * (g : ↥I) := rfl
    show β (((⟨t, hT''I₂ t ht⟩ * g : ↥I₂'') : ↥I)) • V' = β t • β (g : ↥I) • V'
    rw [e, map_mul, mul_smul]
  have hSz : ∀ s ∈ K''.map β ⊓ T''.map β, s z' = z' := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs.2
    exact hβz t (hT''I₂ t ht)
  have h7 : 7 ≤ Nat.card ↥(K''.map β ⊓ T''.map β) := by omega
  have hcore := rank4_core hsq hW (K''.map β) (K''.map β ⊓ T''.map β) inf_le_left hiso' h7 hz'1 hSz
    𝒪 h𝒪 hzX hX4 hOS
  have hle : conjClosure (VZ T M) I₂ ≤ (⨆ X ∈ 𝒪, X).map (blockU K).subtype := by
    refine conjClosure_le fun g hg v hv => ?_
    have hgI : g ∈ I := hI₂I hg
    have hv' : v ∈ blockU K := hVW hv
    let g' : ↥I₂'' := ⟨⟨g, hgI⟩, hg⟩
    let v' : ↥(blockU K) := ⟨v, hv'⟩
    have hv'V : v' ∈ V' := hv
    have hX : β ⟨g, hgI⟩ • V' ∈ 𝒪 := (hmemO _).2 ⟨g', rfl⟩
    have h1 := Subgroup.smul_mem_pointwise_smul v' (β ⟨g, hgI⟩) V' hv'V
    have h2 : (β ⟨g, hgI⟩ • v' : ↥(blockU K)) ∈ ⨆ X ∈ 𝒪, X :=
      (le_iSup₂ (f := fun X (_ : X ∈ 𝒪) => X) (β ⟨g, hgI⟩ • V') hX) h1
    refine Subgroup.mem_map.mpr ⟨β ⟨g, hgI⟩ • v', h2, ?_⟩
    show ((β ⟨g, hgI⟩ v' : ↥(blockU K)) : G) = g * v * g⁻¹
    rfl
  calc Nat.card ↥(conjClosure (VZ T M) I₂)
      ≤ Nat.card ↥((⨆ X ∈ 𝒪, X).map (blockU K).subtype) := Subgroup.card_le_of_le hle
    _ = Nat.card ↥(⨆ X ∈ 𝒪, X) := Subgroup.card_map_of_injective (blockU K).subtype_injective
    _ ≤ 2 ^ 3 := by simpa using hcore

end ModB

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.facts14610_rank4_of_sylow {H : Subgroup G} {u : G} {I I₂ K : Subgroup G}
    (c : Facts14610 T M H u I I₂) (hK : Concl14610List T M I I₂ K) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hA : IsAlt 6 (OTwoQuot K) ∨ IsAlt 7 (OTwoQuot K)) (hW : Nat.card (wOf1469 K) = 2 ^ 4) :
    Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3 :=
  le_antisymm (ModB.rank4U_of_sylow c hK hsyl hA hW)
    (Setting146.eight_le_card_conjClosure_I₂ c.toHyp14610)

end CFSG.Quasithin
