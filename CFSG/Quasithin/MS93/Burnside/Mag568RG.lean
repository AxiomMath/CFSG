module

public import CFSG.Quasithin.MS93.Burnside.Mag568Coord
public import CFSG.Quasithin.MS93.S310MI
public import CFSG.Quasithin.MS93.Burnside.SL3GNorm

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S34F
open scoped commutatorElement Matrix

section Index

theorem burnsideMag568_relIndex_dvd_index_of_normal {Γ : Type*} [Group Γ] [Finite Γ]
    (H N : Subgroup Γ) [N.Normal] : H.relIndex N ∣ H.index := by
  have key : H.relIndex (H ⊔ N) = H.relIndex N := by
    have h1 := Subgroup.relIndex_mul_card H N
    have h2 := Subgroup.relIndex_mul_card N (H ⊔ N)
    have h3 := Subgroup.relIndex_sup_right H N
    have h4 := Subgroup.relIndex_mul_card N H
    have h5 := Subgroup.relIndex_mul_card H (H ⊔ N)
    rw [inf_of_le_left le_sup_right] at h2
    rw [inf_of_le_left le_sup_left] at h5
    rw [inf_comm] at h4
    have hH : 0 < Nat.card ↥H := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hH
    calc H.relIndex (H ⊔ N) * Nat.card ↥H = Nat.card ↥(H ⊔ N) := h5
      _ = N.relIndex H * Nat.card ↥N := by rw [← h2, h3]
      _ = H.relIndex N * (N.relIndex H * Nat.card ↥(H ⊓ N)) := by rw [← h1]; ring
      _ = H.relIndex N * Nat.card ↥H := by rw [h4]
  rw [← key]
  exact Subgroup.relIndex_dvd_index_of_le le_sup_left

theorem burnsideMag568_relIndex_dvd_relIndex {Γ : Type*} [Group Γ] {H N K : Subgroup Γ}
    [Finite ↥K] (hNK : N ≤ K) (hN : (N.subgroupOf K).Normal) :
    H.relIndex N ∣ H.relIndex K := by
  rw [← Subgroup.relIndex_subgroupOf hNK]
  exact burnsideMag568_relIndex_dvd_index_of_normal (H.subgroupOf K) (N.subgroupOf K)

end Index

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideMag568_rg_of_bad (h : PUHyp M T L) (hb : 4 < critDist (puAmalgam h.le))
    (hU : IsSL3U M T L) (hbad : mag568_Bad h) :
    ∃ E : Subgroup (puAmalgam h.le).Universal, E ≤ S34F.flat h (baseA _) ∧
      Qv (puAmalgam h.le) (baseB _) ≤ Subgroup.normalizer (E : Set (puAmalgam h.le).Universal) ∧
      Uloc h.le L (baseA (puAmalgam h.le)) ⊓
          Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≠ ⊥ ∧
      Nat.card ↥(Uloc h.le L (baseA (puAmalgam h.le)) ⊓
          Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) ^ 3 =
        Nat.card ↥(Uloc h.le L (baseA (puAmalgam h.le))) ∧
      mag568_RG h (Uloc h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) := by
  have h20 := h.hyp20
  have hC := h.centHyp
  have hb0 := h.critDist_pos
  have hα₀ := PU.isMVtx_baseA (puAmalgam h.le)
  have hα₀β := adj_baseA_baseB (puAmalgam h.le)
  obtain ⟨n, F, _, _, φ, hcardF, hφs, hnat⟩ := exists_natural_flat h hU
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcardF]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_flat_at h hφs hnat hα₀
  set U := Uloc h.le L (baseA (puAmalgam h.le)) with hUdef
  have hβs : Qv (puAmalgam h.le) (baseB _) ≤ stab _ (baseA _) := qv_le_stab_of_adj _ hα₀β.symm
  have hβU : Qv (puAmalgam h.le) (baseB _) ≤ Subgroup.normalizer (U : Set _) :=
    hβs.trans (S4A.stab_le_normalizer_uloc h _)
  have hβf : Qv (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer (S34F.flat h (baseA _) : Set _) :=
    hβs.trans (stab_le_normalizer_puTrans h.le (flat_subgroupOf_normal h) _)
  have hne_of_card : ∀ Z : Subgroup (puAmalgam h.le).Universal,
      Nat.card ↥Z ^ 3 = Nat.card ↥U → Z ≠ ⊥ := by
    intro Z hZ hbot
    rw [hbot, Subgroup.card_bot, one_pow, card_eq_of_natural hψ] at hZ
    have : 2 ^ 3 ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  have hroot : ∀ μ, IsCritical (puAmalgam h.le) (baseA _) μ →
      ZM (puAmalgam h.le) μ ≤ S34F.flat h (baseA _) ∧
      Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) μ))) = 2 ∧
      Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) μ))) = 1 := by
    intro μ hcμ
    obtain ⟨hf2, hw1, -⟩ := burnsideMag568_rootGroup h hU (by omega) hcardF hφs hnat hcμ
      (hbad μ (hcμ.isMVtx_right _ h20)) hψ
    exact ⟨zm_le_flat h hU (ms22_iii _ h20 hb0 hC hcμ), hf2, hw1⟩
  obtain ⟨μ₀, hcμ₀, hgeoμ₀⟩ := burnsideSL3G_exists_isCritical_geo h hα₀ hα₀β
  have hZμ₀β : ZM (puAmalgam h.le) μ₀ ≤ Qv _ (baseB _) := hgeoμ₀ ▸ zm_le_qv_geo_one _ h20 hb0 hcμ₀
  obtain ⟨hZμ₀f, hf₀, hw₀⟩ := hroot μ₀ hcμ₀
  by_cases hall : ∀ μ, IsCritical (puAmalgam h.le) (baseA _) μ →
      ZM (puAmalgam h.le) μ ≤ Qv _ (baseB _) →
      ⁅U, ZM (puAmalgam h.le) μ⁆ = ⁅U, ZM (puAmalgam h.le) μ₀⁆
  ·
    set R := ⁅U, ZM (puAmalgam h.le) μ₀⁆ with hRdef
    have hRU : R ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp (hZμ₀f.trans hψ.1)
    have hRT : Qv (puAmalgam h.le) (baseB _) ≤ Subgroup.normalizer (R : Set _) := by
      refine le_normalizer_of_map_conj_le fun t ht => ?_
      have htα : t • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).mp (hβs ht)
      have hct : IsCritical (puAmalgam h.le) (baseA _) (t • μ₀) := by
        have := (isCritical_smul _ t (baseA _) μ₀).mpr hcμ₀
        rwa [htα] at this
      have hZt : ZM (puAmalgam h.le) (t • μ₀) ≤ Qv _ (baseB _) := by
        rw [zm_smul, ← map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer ht)]
        exact Subgroup.map_mono hZμ₀β
      have := hall _ hct hZt
      rw [hRdef, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hβU ht), ← zm_smul, this]
    set E := S34F.flat h (baseA _) ⊓ Subgroup.centralizer (R : Set (puAmalgam h.le).Universal)
      with hEdef
    have hZR : U ⊓ Subgroup.centralizer (E : Set _) = R := by
      refine le_antisymm ?_ (le_inf hRU (Subgroup.le_centralizer_iff.mp inf_le_right))
      intro v hv
      by_contra hvR
      set v' : ↥U := ⟨v, hv.1⟩
      have hvc : natVec hψ v' ∉ commN (natImage ψ (ZM (puAmalgam h.le) μ₀)) := fun hc =>
        hvR ((burnsideMag568_mem_commutator_iff hψ hZμ₀f v').mpr hc)
      obtain ⟨⟨c, hc⟩, hc0, hspan⟩ := finrank_eq_one_iff'.mp hw₀
      have hc0' : c ≠ 0 := fun h0 => hc0 (Subtype.ext h0)
      have hy : ∀ a : F, natVec hψ v' ≠ a • c := by
        intro a ha
        apply hvc
        rw [ha]
        exact Submodule.smul_mem _ a hc
      obtain ⟨g, hgc, hgy⟩ := burnsideMag568_exists_fix_move hc0' hy
      obtain ⟨k, rfl⟩ := toSL3_surjective hψs g
      have hkE : (k : (puAmalgam h.le).Universal) ∈ E := by
        refine Subgroup.mem_inf.mpr ⟨k.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        set r' : ↥U := ⟨r, hRU hr⟩
        have hr' := (burnsideMag568_mem_commutator_iff hψ hZμ₀f r').mp hr
        obtain ⟨a, ha⟩ := hspan ⟨_, hr'⟩
        have ha' : natVec hψ r' = a • c := (congrArg Subtype.val ha).symm
        have hfix : ((toSL3 ψ k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ r' =
            natVec hψ r' := by
          rw [ha', Matrix.mulVec_smul, hgc]
        exact ((commute_iff_natVec hψ k r').mpr hfix).symm
      apply hgy
      have := Subgroup.mem_centralizer_iff.mp hv.2 _ hkE
      exact (commute_iff_natVec hψ k v').mp this
    have hcardR : Nat.card ↥R = Nat.card F := by
      rw [hRdef, card_commutator_eq hψ hZμ₀f, Module.natCard_eq_pow_finrank (K := F), hw₀,
        pow_one]
    have hcube : Nat.card ↥(U ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) ^ 3 =
        Nat.card ↥U := by
      rw [hZR, hcardR, card_eq_of_natural hψ]
    refine ⟨E, inf_le_left, burnsideSL3G_le_normalizer_inf_centralizer hβf hRT,
      hne_of_card _ hcube, hcube, μ₀, hcμ₀, hZμ₀β, Or.inl hZR.symm⟩
  ·
    push Not at hall
    obtain ⟨μ₁, hcμ₁, hZμ₁β, hne₁⟩ := hall
    obtain ⟨hZμ₁f, hf₁, hw₁⟩ := hroot μ₁ hcμ₁
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set K := stab (puAmalgam h.le) (baseA _) with hKdef
    have : Finite ↥K := S310.finite_stab_of_isMVtx h hα₀
    have hTP : IsPGroup 2 ↥((Qv (puAmalgam h.le) (baseB _)).subgroupOf K) :=
      (isPGroup_qv _ h20 (not_isMVtx_baseB _)).of_equiv
        (Subgroup.subgroupOfEquivOfLe hβs).symm
    obtain ⟨P', hP'⟩ := hTP.exists_le_sylow
    set P := (P' : Subgroup ↥K).map K.subtype with hPdef
    have hPK : P ≤ K := Subgroup.map_subtype_le _
    have hTPle : Qv (puAmalgam h.le) (baseB _) ≤ P := fun t ht =>
      ⟨⟨t, hβs ht⟩, hP' (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
    have hP2 : IsPGroup 2 ↥P := P'.isPGroup'.map K.subtype
    have hPsub : P.subgroupOf K = (P' : Subgroup ↥K) := by
      rw [Subgroup.subgroupOf, hPdef]
      exact Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective _
    have hPodd : ¬ 2 ∣ P.relIndex K := by
      rw [Subgroup.relIndex, hPsub]
      exact P'.not_dvd_index
    have hfK : S34F.flat h (baseA _) ≤ K := puTrans_le_stab h.le _ _
    have hfn := puTrans_normal h.le (flat_subgroupOf_normal h) (baseA (puAmalgam h.le))
    have hPf : ¬ 2 ∣ P.relIndex (S34F.flat h (baseA _)) := fun hd =>
      hPodd (hd.trans (burnsideMag568_relIndex_dvd_relIndex hfK hfn))
    set E := P ⊓ S34F.flat h (baseA _) with hEdef
    have hEf : E ≤ S34F.flat h (baseA _) := inf_le_right
    have hET : Qv (puAmalgam h.le) (baseB _) ≤ Subgroup.normalizer (E : Set _) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hTPle ht), hβf ht⟩
    have hE2 : IsPGroup 2 ↥(natImage ψ E) := by
      have hP : IsPGroup 2 ↥E := hP2.to_le inf_le_left
      exact (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hEf).symm).map _
    have hEi : ¬ 2 ∣ (natImage ψ E).index := by
      intro hd
      apply hPf
      have h1 : (natImage ψ E).index ∣ (E.subgroupOf (S34F.flat h (baseA _))).index :=
        Subgroup.index_map_dvd _ (toSL3_surjective hψs)
      have h2 : (E.subgroupOf (S34F.flat h (baseA _))).index =
          P.relIndex (S34F.flat h (baseA _)) := by
        rw [← Subgroup.relIndex, hEdef, Subgroup.inf_relIndex_right]
      exact hd.trans (h2 ▸ h1)
    obtain ⟨x, hx⟩ := burnsideMag568_exists_eq_map_sStar hFn hE2 hEi
    set Z := U ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) with hZdef
    have hfE : Module.finrank F (fixN (natImage ψ E)) = 1 := by
      rw [hx]
      exact burnsideMag568_finrank_fixN_map x
    have hcube : Nat.card ↥Z ^ 3 = Nat.card ↥U := burnsideMag568_card_cube_of_finrank hψ hEf hfE
    have hZμE : ∀ μ, ZM (puAmalgam h.le) μ ≤ Qv _ (baseB _) →
        ZM (puAmalgam h.le) μ ≤ S34F.flat h (baseA _) →
        natImage ψ (ZM (puAmalgam h.le) μ) ≤
          (sStar : Subgroup (SL3 F)).map (MulAut.conj x).toMonoidHom := by
      intro μ hμβ hμf
      rw [← hx]
      exact Subgroup.map_mono fun y hy => ⟨hTPle (hμβ hy), hμf hy⟩
    have hflag : ∀ μ, IsCritical (puAmalgam h.le) (baseA _) μ →
        ZM (puAmalgam h.le) μ ≤ Qv _ (baseB _) →
        commN (natImage ψ (ZM (puAmalgam h.le) μ)) = fixN (natImage ψ E) ∨
          fixN (natImage ψ (ZM (puAmalgam h.le) μ)) = commN (natImage ψ E) := by
      intro μ hcμ hμβ
      obtain ⟨hμf, hf, hw⟩ := hroot μ hcμ
      have hcne : commN (natImage ψ (ZM (puAmalgam h.le) μ)) ≠ ⊥ := fun h0 => by
        rw [h0, finrank_bot] at hw
        exact absurd hw (by norm_num)
      rw [hx]
      exact burnsideMag568_flag (hZμE μ hμβ hμf) hf hcne
    have hcen_eq : ∀ μ, ZM (puAmalgam h.le) μ ≤ S34F.flat h (baseA _) →
        commN (natImage ψ (ZM (puAmalgam h.le) μ)) = fixN (natImage ψ E) →
        ⁅U, ZM (puAmalgam h.le) μ⁆ = Z := by
      intro μ hμf he
      have hUμ : ⁅U, ZM (puAmalgam h.le) μ⁆ ≤ U :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp (hμf.trans hψ.1)
      apply le_antisymm
      · intro v hv
        refine ⟨hUμ hv, (burnsideMag568_mem_centralizer_iff hψ hEf ⟨v, hUμ hv⟩).mpr ?_⟩
        rw [← he]
        exact (burnsideMag568_mem_commutator_iff hψ hμf ⟨v, hUμ hv⟩).mp hv
      · intro v hv
        refine (burnsideMag568_mem_commutator_iff hψ hμf ⟨v, hv.1⟩).mpr ?_
        rw [he]
        exact (burnsideMag568_mem_centralizer_iff hψ hEf ⟨v, hv.1⟩).mp hv.2
    have hfix_iff : ∀ μ, ZM (puAmalgam h.le) μ ≤ S34F.flat h (baseA _) →
        fixN (natImage ψ (ZM (puAmalgam h.le) μ)) = commN (natImage ψ E) →
        ∀ v : ↥U, (v : (puAmalgam h.le).Universal) ∈
          Subgroup.centralizer (ZM (puAmalgam h.le) μ : Set _) ↔
            natVec hψ v ∈ commN (natImage ψ E) := by
      intro μ hμf he v
      rw [burnsideMag568_mem_centralizer_iff hψ hμf v, he]
    refine ⟨E, hEf, hET, hne_of_card _ hcube, hcube, ?_⟩
    rcases hflag μ₀ hcμ₀ hZμ₀β with h₀ | h₀
    · exact ⟨μ₀, hcμ₀, hZμ₀β, Or.inl (hcen_eq μ₀ hZμ₀f h₀)⟩
    rcases hflag μ₁ hcμ₁ hZμ₁β with h₁ | h₁
    · exact ⟨μ₁, hcμ₁, hZμ₁β, Or.inl (hcen_eq μ₁ hZμ₁f h₁)⟩
    refine ⟨μ₀, hcμ₀, hZμ₀β, Or.inr ⟨μ₁, hcμ₁, hZμ₁β, ?_, ?_, Ne.symm hne₁⟩⟩
    · ext v
      constructor
      · rintro ⟨hvU, hvC⟩
        refine ⟨hvU, (hfix_iff μ₁ hZμ₁f h₁ ⟨v, hvU⟩).mpr ?_⟩
        exact (hfix_iff μ₀ hZμ₀f h₀ ⟨v, hvU⟩).mp hvC
      · rintro ⟨hvU, hvC⟩
        refine ⟨hvU, (hfix_iff μ₀ hZμ₀f h₀ ⟨v, hvU⟩).mpr ?_⟩
        exact (hfix_iff μ₁ hZμ₁f h₁ ⟨v, hvU⟩).mp hvC
    · intro v hv
      refine ⟨hv.1, (hfix_iff μ₀ hZμ₀f h₀ ⟨v, hv.1⟩).mpr ?_⟩
      have h1 := (burnsideMag568_mem_centralizer_iff hψ hEf ⟨v, hv.1⟩).mp hv.2
      rw [hx] at h1 ⊢
      exact burnsideMag568_fixN_le_commN_map x h1

end CFSG.Quasithin.MS93.S4L
